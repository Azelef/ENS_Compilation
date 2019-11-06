
open Ast

let printast =
  let rec printfichier f =
    List.fold_right (fun d s  -> printdecl d^"\n"^s) f ""
  and printconstant c = match c.dc with
    | Cnull -> "null"
    | Cthis -> "this"
    | Cbool true -> "true"
    | Cbool false -> "false"
    | Cstring s -> "\""^s^"\""
    | Cint n -> string_of_int n
  and printunop = function
    | Unot -> "!"
    | Uminus -> "-"
  and printbinop = function
    | Bor -> "||"
    | Band -> "&&"
    | Breq -> "==="
    | Brneq -> "!=="
    | Beq -> "=="
    | Bneq -> "!="
    | Blt -> "<"
    | Ble -> "<="
    | Bgt -> ">"
    | Bge -> ">="
    | Bplus -> "+"
    | Bminus -> "-"
    | Btimes -> "*"
    | Bdiv -> "/"
    | Bmod -> "%"
  and printtyp t = match t.dt with
    | TypClasse (id,[]) -> id.di
    | TypClasse (id,t1::lst) -> id.di^" <"^
                               (List.fold_left (fun s t ->s^","^(printtyp t))
                               (printtyp t1) lst)^">"
    | TypMaybe t -> (printtyp t)^"?"
    | TypFonction ([],t) -> "() -> "^(printtyp t)
    | TypFonction (t1::lst,t) -> "("^(List.fold_left (fun s t ->s^","^
                                                                  (printtyp t))
                               (printtyp t1) lst)^") -> "^(printtyp t)
  and printparam p isc =
    let prefix = if isc then if p.dp.mut then "var " else "val " else ""
    in prefix^p.dp.nom.di^" : "^(printtyp p.dp.typ)
  and printexpr e indent = match e.de with
    | Econst c -> printconstant c
    | Eacces a -> printacces a
    | Eassign (a,e) -> (printacces a)^" = "^(printexpr e (indent^"   "))
    | Eeval (fn,[]) -> fn.di^"()"
    | Eeval (fn,p1::lst) -> fn.di^"("^
                            (List.fold_left (fun s p ->s^","^(printexpr p ""))
                            (printexpr p1 "") lst)^")"
    | Eunop (u,e) -> "("^(printunop u)^(printexpr e indent)^")"
    | Ebinop (b,e1,e2) -> "("^(printexpr e1 indent)^(printbinop b)^
                            (printexpr e2 indent)^")"
    | Eif (c,eif,eelse) -> "if ("^(printexpr c "")^") {\n"^indent^"   "^
                           (printexpr eif (indent^"   "))^"\n"^indent^"}\n"^indent^"else {\n"^indent^"   "^
                           (printexpr eelse (indent^"   "))^"\n"^indent^"}"
    | Ewhile (c,e) -> "while ("^(printexpr c "")^") {\n"^indent^"   "^
                           (printexpr e (indent^"   "))^"\n"^indent^"}"
    | Ereturn e -> "return "^(printexpr e (indent^"       "))
    | Efun ([],None,e) -> "fun ()\n"^indent^(printexpr e indent)
    | Efun (p1::lst,None,e) -> "fun ("^
                                 (List.fold_left (fun s p ->s^","^
                                             (printparam p false))
                              (printparam p1 false) lst)^")\n"^indent^
                              (printexpr e indent)  
    | Efun ([],Some t,e) -> "fun ():"^(printtyp t)^"\n"^indent^
                              (printexpr e indent)
    | Efun (p1::lst,Some t,e) -> "fun ("^
                                 (List.fold_left (fun s p ->s^","^
                                            (printparam p false))
                                  (printparam p1 false) lst)^"):"^(printtyp t)^
                                     "\n"^indent^
                              (printexpr e indent)
    | Evar v -> printvar v indent
    | Ebloc [] -> "{}"
    | Ebloc (e1::lst) -> "{\n"^indent^"   "^
                         (List.fold_left
                            (fun s e -> s^";\n"^indent^"   "^
                                          (printexpr e (indent^"   ")))
                            (printexpr e1 (indent^"   ")) lst)^
                           ";\n"^indent^"}\n"^indent
  and printacces a = match a.da with
    | Accident id -> id.di
    | Accdot (e,id) -> "("^(printexpr e "")^")."^id.di
    | Accmaybedot (e,id) -> "("^(printexpr e "")^")?."^id.di
  and printvar v indent = let prefix = if v.mut then "var " else "val " in
    match v.typ with
    | None -> prefix^v.nom.di^" = "^(printexpr v.decl (indent^"   "))
    | Some t -> prefix^v.nom.di^" : "^(printtyp t)^" = "
                ^(printexpr v.decl (indent^"   "))
  and printclasse (c:Ast.classe) =
    let typp = if c.types=[] then ""
               else " <"^(List.fold_left
                            (fun s t -> s^", "^t.di)
                            ((List.hd c.types).di) (List.tl c.types))^"> "
    and vars = if c.declVar=[] then " {} "
               else "{\n"^"   "^
                       (List.fold_left
                        (fun s v -> s^";\n"^"   "^
                                    (printvar v "   "))
                        (printvar (List.hd c.declVar) "   ")
                        (List.tl c.declVar))^
                       ";\n}\n"
    and params = "("^(List.fold_left (fun s p ->s^","^(printparam p true))
                    (printparam (List.hd c.params) true) (List.tl c.params))^")"
    in "data class "^c.nom.di^typp^params^vars
  and printfonction f =
    let typp = if f.types=[] then ""
               else " <"^(List.fold_left
                            (fun s t -> s^", "^t.di)
                            ((List.hd f.types).di) (List.tl f.types))^"> "
    and params = if f.params = [] then " "
                 else "("^(List.fold_left (fun s p ->s^","^(printparam p false))
                             (printparam (List.hd f.params) false)
                             (List.tl f.params))^")"
    and ftype =  match f.typ with
      | None -> " "
      | Some t -> " : "^(printtyp t)^" "
    in "fun "^typp^f.nom.di^params^ftype^(printexpr f.corps "")
  and printdecl = function
    | DeclVar v -> printvar v ""
    | DeclClasse c -> printclasse c
    | DeclFonction f -> printfonction f
  in printfichier
