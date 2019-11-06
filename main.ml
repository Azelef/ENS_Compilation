
(* Fichier principal du compilateur mini-kotlin *)

open Format
open Lexing
open Lexer
open Parser
open Astprinter
open Ast
open Typer
open Typetree
open Atree
open TtoA
open X86_64
open AtoAsm

(* Option de compilation, pour s'arrêter à l'issue du parser ou du typer*)
let parse_only = ref false
let type_only = ref false

(* Noms du fichier source*)
let ifile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche avec --help *)
let options =
  [("--parse-only", Arg.Set parse_only,
   "  Pour ne faire uniquement que la phase d'analyse syntaxique");
   ("--type-only", Arg.Set type_only,
   "  Pour s'arreter apres le typage")]

let usage = "usage: pkotlinc [option] file.kt"

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
  (* Parsing de la ligne de commande *)
  Arg.parse options (set_file ifile) usage;

  (* On vérifie que le nom du fichier source a bien été indiqué *)
  if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?"; exit 1 end;

  (* Ce fichier doit avoir l'extension .logo *)
  if not (Filename.check_suffix !ifile ".kt") then begin
    eprintf "Le fichier d'entrée doit avoir l'extension .kt\n@?";
    Arg.usage options usage;
    exit 1
  end;

  (* Ouverture du fichier source en lecture *)
  let f = open_in !ifile in

  (* Création d'un tampon d'analyse lexicale *)
  let buf = Lexing.from_channel f in
  
  try
    let p = Parser.fichier Lexer.token buf in
    close_in f;
    (*print_string(Astprinter.printast(p));*)
    (* On s'arrête ici si on ne veut faire que le parsing *)
    if !parse_only then exit 0;
    let myttree = Typer.tfichier p in
    if !type_only then exit 0;
    let myatree = TtoA.ttoafichier myttree in
    let prog = AtoAsm.asmfichier myatree in
    let ofile = Filename.chop_suffix !ifile ".kt" ^ ".s" in
    let f = open_out ofile in
    let fmt = formatter_of_out_channel f in
    X86_64.print_program fmt prog;
    (* on "flush" le buffer afin de s'assurer que tout y a été écrit
       avant de le fermer *)
    fprintf fmt "@?";
    close_out f;
    exit 0;

  with
    | Lexer.Lexing_error c ->
       (* Erreur lexicale*)
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur lexicale: %s@." c;
	exit 1
    | Parser.Error ->
       (*Erreur syntaxique*)
       localisation (Lexing.lexeme_start_p buf);
       eprintf "Erreur syntaxique@.";
	exit 1
    | Typer.Error ((l1,l2),s)->
       (*Erreur de typage*)
       localisation l1;
       eprintf "Erreur de typage : %s@." s;
       exit 1
	| Typer.NoMain s->
	   eprintf "Erreur de typage : %s@." s;
       exit 1
    | TtoA.TtoAerror s ->
       (*Bug dans la partie arrière*)
       eprintf "Erreur lors de la compilation en assembleur: %s@." s;
       exit 2
    | e -> print_string (Printexc.to_string e); exit 2
