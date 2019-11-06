
(* Arbres de type de Petit-Kotlin *)

open Ast

type tident = string

type tconstant =
  | TCnull
  | TCthis (*pour les classes*)
  | TCbool of bool
  | TCstring of string
  | TCint of int;;

(*type de type renvoyé par le typeur *)
type ttyp =
  | TyClasse of string*(ttyp list)*(ttyp list)*((string*ttyp*bool) list)
  (*nom,types parametres,parametres du constructeur,champs*)
  | TyMaybe of ttyp
  | TyFonction of (ttyp list)*ttyp
  | TyPoly of string*string (*fonction/constructeur,nom*)
  | TyInt
  | TyBool
  | TyString
  | TyNull
  | TyUnit
  | TyFonctionGlobale of int
  | TyClasseGlobale of int;; (*deux types pour la production de code*)


type texpr =
  | TEconst of tconstant
  | TEacces of tacces
  | TEassign of tacces * texpr
  | TEeval of tident * (texpr list)
  | TEunop of unop * texpr (* pour - et ! *)
  | TEbinop of binop * texpr * texpr
  | TEif of texpr * texpr * texpr
  | TEwhile of texpr * texpr
  | TEreturn of texpr (*il y a éventuellement un bloc vide ici*)
  | TEfun of ((tident*ttyp) list) * texpr (*type des paramètres*)
  | TEvar of tvar
  | TEbloc of texpr list

and tacces =
  | TAccident of tident * ttyp (*type de la variable*)
  | TAccdot of texpr * ttyp * tident (*type (classe) du texpr à sa droite*)
  | TAccmaybedot of texpr * ttyp * tident (*de même*)
  
and tvar = 
  { nom: tident;
    typ: ttyp; (*PIERRE: type de la variable*)
    decl: texpr};;

type tclasse =
  { nom: tident;
    params: (tident*ttyp) list; (*paramètres du constructeur et leurs types*)
    declVar: tvar list};;

type tfonction =
  { nom: tident;
    params: (tident*ttyp) list; (*type des paramètres de la fonction*)
    corps: texpr;
    };;

type tdecl =
  | TDeclVar of tvar
  | TDeclClasse of tclasse
  | TDeclFonction of tfonction;;

type tfichier = tdecl list;;
