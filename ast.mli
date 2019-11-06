
(* Arbres de syntaxe abstraite de Petit-Kotlin *)
type loc=Lexing.position*Lexing.position;;

type ident = {di: string;
              li: loc};;

type constant ={dc: lconstant;
                lc: loc}
and lconstant=
  | Cnull
  | Cthis (*pour les classes*)
  | Cbool of bool
  | Cstring of string
  | Cint of int;; (*WIP: ajouter la gestion des arrays*)

type unop=
  | Unot | Uminus;;

type binop =
  | Bor | Band                     (* && || *)
  | Breq | Brneq | Beq |Bneq       (* === !== == != *)
  | Blt | Ble | Bgt | Bge          (* < <= > >= *)
  | Bplus | Bminus | Btimes | Bdiv | Bmod;; (* + - * / % *)

type typ ={dt: ltyp;
           lt: loc}
and ltyp=
  | TypClasse of ident*(typ list)
  | TypMaybe of typ
  | TypFonction of (typ list)*typ;;

type param ={dp: lparam;
             lp: loc}
and lparam=
  { nom: ident;
    typ: typ;
    mut: bool};;

type expr ={de: lexpr;
            le: loc}
and lexpr=
  | Econst of constant
  | Eacces of acces
  | Eassign of acces * expr
  | Eeval of ident * (expr list)
  | Eunop of unop * expr (* pour - et ! *)
  | Ebinop of binop * expr * expr
  | Eif of expr * expr * expr
  | Ewhile of expr * expr
  | Ereturn of expr (*on met éventuellement un Econst Cnull ici*)
  | Efun of (param list) * (typ option) * expr
  | Evar of var
  | Ebloc of expr list

and acces ={da: lacces;
            la: loc }
and lacces=
  | Accident of ident
  | Accdot of expr * ident
  | Accmaybedot of expr * ident
  
and var = 
  { nom: ident;
    typ: typ option;
    decl: expr;
    mut: bool;
    lv: loc};;

type classe =
  { nom: ident;
    types: ident list; (*noms des types parmetres dans la classe*)
    params: param list; (*doit etre non vide, parametres du constructeur*)
    declVar: var list;
    lcl: loc };;

type fonction =
  { nom: ident;
    types: ident list; (*noms des types parmetres dans la fonction*)
    params: param list;
    typ: typ option;
    corps: expr;
    lf:loc };;

type decl =
  | DeclVar of var
  | DeclClasse of classe
  | DeclFonction of fonction;;

type fichier = decl list;;
