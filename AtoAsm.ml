(*transforme les arbres A en code asm dans le format de x86_64.mli*)

open Atree
open X86_64
open Ast
open Char

let process_str s =
  let sr = ref "" in
  let i = ref 0 in
  while !i<String.length s do
   (if s.[!i]='\\'
    then (incr i;sr:=!sr^String.make 1 
    (match s.[!i] with 'n' -> '\n' | 't' -> '\t' | a -> a))
    else sr:=!sr^String.make 1 s.[!i]);
    incr i;
  done;!sr;;

let countlabel = ref 0;;
let freshlabel () =  countlabel:=!countlabel+1;".L"^(string_of_int !countlabel);;

let asmprintfunctions=
  label "funprint_string" ++ pushq !%rbp ++ movq !%rsp !%rbp ++
  movq (ind ~ofs:(2*8) rbp) !%rsi ++ xorq !%rax !%rax ++
  movq (ilab "message_str") !%rdi ++testq !%rsi !%rsi ++
  jz ".LPS" ++ call "printf" ++ leave ++ ret ++
  label ".LPS" ++ movq (ilab "message_null") !%rsi ++
  call "printf" ++ leave ++ ret ++
  label "funprint_int" ++pushq !%rbp ++ movq !%rsp !%rbp ++
  movq (ind ~ofs:(2*8) rbp) !%rsi ++ movq (ilab "message_int") !%rdi ++
  xorq !%rax !%rax ++ call "printf" ++ leave ++ ret;;
    
let myadditionaldata = label "message_str" ++ string "%s" ++
                       label "message_int" ++ string "%d" ++
                       label "message_null" ++ string "null";;

let rec asmexpr = function
  | AEconst cst ->
     (match cst with
      | ACnull -> xorq !%rax !%rax
      | ACthis -> movq (ind ~ofs:(2*8) rbp) !%rax
      | ACinline i -> movq (imm i) !%rax
      | ACstring s -> movq (ilab s) !%rax)
  | AEacces acc ->
     (match acc with
      | AAccvar var ->
         (match var with
          | AVglobal s -> movq (lab ("var"^s)) !%rax
          | AVlocal n -> movq (ind ~ofs:(n*8) rbp) !%rax
          | AVclos n -> movq (ind ~ofs:(2*8) rbp) !%rdi ++
                        movq (ind ~ofs:(n*8) rdi) !%rax
          | AVarg n -> movq (ind ~ofs:(n*8) rbp) !%rax)
      | AAccdot (exp,n) -> asmexpr exp ++ movq (ind ~ofs:(n*8) rax) !%rax
      | AAccdotmaybe (exp,n)->let l1=freshlabel () in let l2=freshlabel () in
         asmexpr exp ++ testq !%rax !%rax ++ jnz l1 ++ xorq !%rax !%rax ++
         jmp l2 ++ label l1 ++ movq (ind ~ofs:(n*8) rax) !%rax ++ label l2)
  | AEassign (acc,exp) -> asmexpr exp ++
     (match acc with
      | AAccvar var ->
         (match var with
          | AVglobal s -> movq !%rax (lab ("var"^s))
          | AVlocal n -> movq !%rax (ind ~ofs:(n*8) rbp)
          | AVclos n -> movq (ind ~ofs:(2*8) rbp) !%rdi ++
                        movq !%rax (ind ~ofs:(n*8) rdi)
          | AVarg n -> movq !%rax (ind ~ofs:(n*8) rbp))
      | AAccdot (exp,n) -> pushq !%rax ++ asmexpr exp ++
                             popq rdi ++ movq !%rdi (ind ~ofs:(n*8) rax)
      | AAccdotmaybe (exp,n) -> let l1=freshlabel () in
         pushq !%rax ++ asmexpr exp ++ popq rdi ++ 
         testq !%rax !%rax ++ jz l1 ++
         movq !%rdi (ind ~ofs:(n*8) rax) ++ label l1)
  | AEevalfonction (nom,lst) ->
     List.fold_left (fun code exp -> code++asmexpr exp++pushq !%rax) nop lst ++
     call ("fun"^nom) ++ if lst=[] then nop
     else addq (imm (List.length lst*8)) !%rsp
  | AEevallambda (varexp,lst) ->
     List.fold_left (fun code exp -> code++asmexpr exp++pushq !%rax) nop lst ++
     asmexpr varexp ++ pushq !%rax ++
     call_star (ind rax)  ++ addq (imm (List.length lst*8+8)) !%rsp  
  | AEevalconstructeur (size,nom,lst) ->
     List.fold_left (fun code exp -> code++asmexpr exp++pushq !%rax) nop lst ++
     movq (imm (size*8)) !%rdi ++ call "malloc" ++ pushq !%rax ++
     call ("classe"^nom) ++ popq rax ++ addq (imm (List.length lst*8)) !%rsp
  | AEunop (op,exp) -> asmexpr exp ++
     (match op with Unot -> xorq (imm 1) !%rax | Uminus -> negq !%rax)
  | AEbinop (op,exp1,exp2) ->
    (match op with
     | Bor -> let l1 = freshlabel () in asmexpr exp1 ++ testq !%rax !%rax ++
        jnz l1 ++ asmexpr exp2 ++ label l1                              
     | Band -> let l1 = freshlabel () in asmexpr exp1 ++ testq !%rax !%rax ++
        jz l1 ++ asmexpr exp2 ++ label l1
     | _ -> (asmexpr exp2 ++ pushq !%rax ++
     asmexpr exp1 ++ popq rdi ++
     (match op with
      | Breq | Beq -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
                      cmpq !%rdi !%rsi ++ sete !%al
      | Brneq | Bneq -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
                        cmpq !%rdi !%rsi ++ setne !%al
      | Blt -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
               cmpq !%rsi !%rdi ++ setg !%al
      | Ble -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
               cmpq !%rsi !%rdi ++ setge !%al
      | Bgt -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
               cmpq !%rsi !%rdi ++ setl !%al
      | Bge -> movq !%rax !%rsi ++ xorq !%rax !%rax ++
               cmpq !%rsi !%rdi ++ setle !%al
      | Bplus -> addq !%rdi !%rax | Bminus -> subq !%rdi !%rax
      | Btimes -> imulq !%rdi !%rax
      | Bdiv -> cqto ++ idivq !%rdi
      | Bmod -> cqto ++ idivq !%rdi ++ movq !%rdx !%rax | _-> nop)))
  | AEif (cond,ifexp,elseexp) ->
     let labelelse = freshlabel () in let labelend = freshlabel ()
     in asmexpr cond ++ testq !%rax !%rax ++ jz labelelse ++
        asmexpr ifexp ++ jmp labelend ++ label labelelse ++ 
        asmexpr elseexp ++ label labelend
  | AEwhile (cond,exp) ->
     let labelstart = freshlabel () in let labelcond = freshlabel ()
     in jmp labelcond ++ label labelstart ++ asmexpr exp ++
        label labelcond ++ asmexpr cond ++ testq !%rax !%rax ++
        jnz labelstart 
  | AEreturn exp -> asmexpr exp ++ leave ++ ret
  | AEclos (nom,lst) -> movq (imm ((List.length lst + 1)* 8)) !%rdi ++
     call "malloc" ++ movq (ilab nom) !%rdi ++ movq !%rdi (ind rax) ++
     movq !%rax !%rsi++(*rsi n'est pas utilise pour acceder a une var*)
     fst (List.fold_left (fun (code,i) var -> (code ++
      asmexpr (AEacces (AAccvar var))++movq !%rax (ind ~ofs:(i*8) rsi),i+1))
      (nop,1) lst) ++ movq !%rsi !%rax
  | AEvar (n,exp) -> asmexpr exp ++ pushq !%rax
  | AEbloc (lst,pilesize) ->
     List.fold_left (fun code exp-> code++asmexpr exp) nop lst ++
     if (pilesize=0) then nop else addq (imm (pilesize*8)) !%rsp;;

let asmfonction prefix (f:Atree.afonction) =
  label (prefix^f.nom) ++ pushq !%rbp ++ movq !%rsp !%rbp ++
  asmexpr f.corps ++ leave ++ ret;;

let asmconstructeur (c:Atree.aconstructeur) =
  label ("classe"^c.nom) ++ pushq !%rbp ++ movq !%rsp !%rbp ++
  fst (List.fold_left (fun (code,i) exp -> (code++asmexpr exp++
       movq (ind ~ofs:(2*8) rbp) !%rdi++movq !%rax (ind ~ofs:(i*8) rdi),i+1))
       (nop,0) c.declVar) ++ leave ++ ret;;

let asmfichier (f:Atree.afichier) =
  {text =
     globl "main" ++ label "main" ++ movq !%rsp !%rbp ++
     (List.fold_left (fun code (nom,exp) ->
            code ++ asmexpr exp ++ movq !%rax (lab ("var"^nom)))
          nop  f.vars)++
     call "funmain" ++
     xorq !%rax !%rax ++ ret ++
     asmprintfunctions ++
     List.fold_left (fun code lam -> code++asmfonction "" lam) nop f.lambdas ++
     List.fold_left (fun code fn -> code++asmfonction "fun" fn) nop f.fonctions++
     List.fold_left (fun code cl -> code++asmconstructeur cl)
       nop f.constructeurs;
   data =
     myadditionaldata ++
     List.fold_left (fun code (lbl,s) ->
         code++label lbl++string (process_str s)) nop f.constants ++
     List.fold_left (fun code (nom,_) ->
         code++label ("var"^nom)++dquad [0]) nop f.vars
    };;
