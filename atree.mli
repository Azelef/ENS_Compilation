
(* Arbres apres pretraitement *)

open Ast
open Typetree

type aconstant =
  | ACnull
  | ACthis
  | ACinline of int (*bool et int*)
  | ACstring of string;; (*numero de la constante*)

type avar = 
  | AVglobal of string (*sur le segment*)
  | AVlocal of int (*sur la pile*)
  | AVclos of int (*dans la fermeture*)
  | AVarg of int;; (*dans les arguments, registre ou pile selon <=6*)

type aacces = 
  | AAccvar of avar
  | AAccdot of aexpr * int
  | AAccdotmaybe of aexpr * int (*si la variable contient 0, on renvoit 0*)

and aexpr =
  | AEconst of aconstant
  | AEacces of aacces
  | AEassign of aacces * aexpr
  | AEevalfonction of string * (aexpr list)
  | AEevallambda of aexpr * (aexpr list) (*expr de l'acces a la variable*)
  | AEevalconstructeur of int * string * (aexpr list)(*taille du bloc a allouer*)
  | AEunop of unop * aexpr (* pour - et ! *)
  | AEbinop of binop * aexpr * aexpr
  | AEif of aexpr * aexpr * aexpr
  | AEwhile of aexpr * aexpr
  | AEreturn of aexpr (*il y a éventuellement un bloc vide ici*)
  | AEclos of string*(avar list)
  | AEvar of int*aexpr
  | AEbloc of (aexpr list)*int;; (*nombre de variables locales sur la pile*)

type aconstructeur =
  { nom: string;  
    declVar: aexpr list};; (*declarations des variables dans l'ordre*)

type afonction =
  { nom: string;
    corps: aexpr};;

type afichier =
  { vars: (string*aexpr) list; (*variables globales*)
    constructeurs: aconstructeur list; (*classes*)
    fonctions: afonction list;
    lambdas: afonction list;
    constants: (string*string) list};;
    
