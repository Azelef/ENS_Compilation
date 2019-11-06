
(*reduction des arbres de types en Atree*)
(*gestion des variables, du polymorphisme, des fonctions de première classe*)
(*et des classes*)

open Typetree
open Atree

(*evironnement de variables, pour le parcours*)
(*les fonctions sont considéréés comme des variables globales*)
(*les constructeurs de classe également*)
(*mais seules les 'vraies' variables globales seront stockee dans afichier.vars*)
(*contient des éléments de type avar*ttyp*)
module ENV = Map.Make(String);;
(*contient les numéros des variables des classes*)
module CLASSEENV = Map.Make(String);;
(*type pour stocker les classes utilisees, sous forme de (string,classenv) t*)

exception TtoAerror of string;; 
(*pour ajouter un element en tete d'une ref de liste*)
let app lstref e = lstref:=e::!lstref;;
(*Des fonctions pour acceder aux elements d'un tuple a 3 elements*)
let fst4 t= match t with
	|(a,_,_,_)->a;;
(*prefixe pour les doublons*)
let prefix = function 0 -> "" | k -> string_of_int k;;

(*variables globales*)
let classeshtbl = Hashtbl.create 59;;
let lambdas = ref [];;
let constants = ref [];;

(*compteurs associes*)
let countlambda = ref 0;;
let freshlambda () =
  countlambda:=!countlambda+1;"lambda"^(string_of_int !countlambda);;

let countconst = ref 0;;
let freshconst () =
  countconst:=!countconst+1;"const"^(string_of_int !countconst);;

let int_of_bool = function true -> 1 | false -> 0;;

let baseenv = ENV.add "print_string" (AVglobal "print_string",
                                      TyFonctionGlobale 0) (
                  ENV.add "print_int" (AVglobal "print_int",
                                       TyFonctionGlobale 0)
                    ENV.empty);;

let ttoaconstant = function
  | TCnull -> ACinline 0
  | TCthis -> ACthis
  | TCbool b -> ACinline (int_of_bool b)
  | TCstring s -> let lbl = freshconst () in (app constants (lbl,s);ACstring lbl)
  | TCint i -> ACinline i;;

(*pile est negatif et contient la prochaine adresse libre sur la pile*)
let rec createlambda lst varenv pile free corps =
  (*on ne garde que les variables globales*)
  let env1 = ENV.filter (function _ ->
                           (function | (AVglobal _,_)-> true
                                     | _->false))
               varenv in
  (*on ajoute les parametres de la fonction a l'envers*)
  let env2 = fst (List.fold_right (fun (id,ty) (envi,i) ->
                      (ENV.add id ((AVarg i),ty) envi,i+1))
                    lst (env1,3)) in (*apres ad retrour et enviro*)
  let nomlambda = freshlambda () in
  let (aexp,varenv2,_,freel) = ttoaexpr env2 (-1) ENV.empty corps in
  let enviro = List.sort (fun e1 e2 -> match (e1,e2) with
                                    |((_,(AVclos a,_)),(_,(AVclos b,_))) -> a-b
                                    | _ -> raise (TtoAerror "free isnt"))
                 (ENV.bindings freel)
  in app lambdas { nom= nomlambda; corps= aexp};
     let (vlst,free1) =
       List.fold_left (fun (vlst,free) (nom,(_,ty)) ->
           (match ENV.find_opt nom varenv with
            | Some (e,_) -> (e::vlst,free)
            | None -> (match ENV.find_opt nom free with
                       | Some (e,_) -> (e::vlst,free)
                       | None -> (*la variable est libre dans le contexte pere*)
                          ((AVclos (ENV.cardinal free+1))::vlst,
                           ENV.add nom (AVclos (ENV.cardinal free+1),ty) free))))
         ([],free) enviro
     in (AEclos (nomlambda,List.rev vlst),varenv,pile,free1)
  

and ttoaacces varenv pile free = function
  | TAccident (nom,ty) -> (match ENV.find_opt nom varenv with
              | Some (e,_) -> (AAccvar e,free)
              | None -> (match ENV.find_opt nom free with
                         | Some (e,_) -> (AAccvar e,free)
                         | None -> AAccvar (AVclos (ENV.cardinal free+1)),
                                   ENV.add nom (AVclos (ENV.cardinal free+1),ty)
                                     free))
  | TAccdot (texp,ty,nom) ->
     let (aexp,_,_,free1) =
       ttoaexpr varenv pile free texp in
     let nomclasse = (match ty with TyClasse (s,_,_,_) -> s
                                  | _-> raise (TtoAerror "classe inexistente"))
     in (AAccdot (aexp,CLASSEENV.find nom (Hashtbl.find classeshtbl nomclasse)),
         free1)
  | TAccmaybedot (texp,ty,nom) ->
     let (aexp,_,_,free1) =
       ttoaexpr varenv pile free texp in
     let nomclasse = (match ty with TyMaybe (TyClasse (s,_,_,_))
                                   |TyClasse (s,_,_,_)  -> s
                                  | _-> raise (TtoAerror "classe inexistente"))
     in (AAccdotmaybe (aexp, CLASSEENV.find nom
                              (Hashtbl.find classeshtbl nomclasse)),free1)

and ttoaexpr varenv pile free = function
  | TEconst tconst -> (AEconst (ttoaconstant tconst),varenv,pile,free)
  | TEacces tacc -> let (aacc,free1) =
                      (ttoaacces varenv pile free tacc)
                    in (AEacces aacc,varenv,pile,free1)
  | TEassign (tacc,texp) -> let (aacc,free1) =
                           (*on laisse de la place pour l'adresse de retour*)
                             ttoaacces varenv (pile-1) free tacc in
                           let (aexp,_,_,free2) =
                             ttoaexpr varenv pile free1 texp in
                           (AEassign (aacc,aexp),varenv,pile,free2)
  (*on distigue selon que l'on evalue une fonction globale,
    un constructeur, ou une lambda*)
  | TEeval (nom,texplst) -> let (alst,free1,numarg) =
                              List.fold_left
                                (fun (alst,free,i) texp ->
                                  let (aexp,_,_,free1) = 
                                    ttoaexpr varenv (pile-i) free texp
                                  in (aexp::alst,free1,i+1))
                                ([],free,0) texplst
                            in (match ENV.find_opt nom varenv with
                                | Some (AVglobal _,TyFonctionGlobale n) ->
                                  (AEevalfonction ((prefix n)^nom,List.rev alst),
                                    varenv,pile,free1)
                                | Some (AVglobal _,TyClasseGlobale n) ->
                                  (AEevalconstructeur (CLASSEENV.cardinal
                                    (Hashtbl.find classeshtbl nom),
                                    (prefix n)^nom,List.rev alst),
                                   varenv,pile,free1)
                                (*on renvoit a ttoaacces*)  
                                | _ -> let (acc,free2) = ttoaacces varenv
                                        (pile-List.length texplst) free1
                                        (TAccident (nom,TyFonction ([],TyNull)))
                                       in (*le type n'importe pas*)
                                       (AEevallambda (AEacces acc,List.rev alst),
                                        varenv,pile,free2)
                                )
  | TEunop (op,texp) -> let (aexp,_,_,free1) =
                          ttoaexpr varenv pile free texp
                        in (AEunop (op,aexp),varenv,pile,free1)
  | TEbinop (op,texp1,texp2) -> let ofs = (match op with
                                Ast.Band | Ast.Bor -> 0 | _ -> -1) in
                                let (aexp2,_,_,free1) =
                                  ttoaexpr varenv pile free texp2 in
                                let (aexp1,_,_,free2) =
                                (*on laisse un emplacement sur la pile*)
                                  ttoaexpr varenv (pile+ofs) free1 texp1
                                in (AEbinop (op,aexp1,aexp2),
                                    varenv,pile,free2)
  | TEif (cond,ifexp,elseexp) -> let (aexpc,_,_,free1) =
                                   ttoaexpr varenv pile free cond in
                                 let (aexpi,_,_,free2) =
                                   ttoaexpr varenv pile free1 ifexp in
                                 let (aexpe,_,_,free3) =
                                   ttoaexpr varenv pile free2 elseexp
                                 in (AEif (aexpc,aexpi,aexpe),
                                     varenv,pile,free3)
  | TEwhile (cond, loop) -> let (aexpc,_,_,free1) =
                              ttoaexpr varenv pile free cond in
                            let (aexpl,_,_,free2) =
                              ttoaexpr varenv pile free1 loop
                            in (AEwhile (aexpc,aexpl),
                                varenv,pile,free2)
  | TEreturn texp -> let (aexpc,_,_,free1) =
                       ttoaexpr varenv pile free texp
                     in (AEreturn aexpc,varenv,pile,free1)
  | TEfun (lst,corps) -> createlambda lst varenv pile free corps
  (*on empile si une nouvelle variable locale est cree*)
  | TEvar var -> let (aexp,_,_,free1) =
                   ttoaexpr varenv pile free var.decl
                 in (AEvar (pile,aexp),
                     ENV.add var.nom ((AVlocal pile),var.typ) varenv,
                     pile-1,free1)
  | TEbloc lst -> let (alst,envi1,pile1,free1) =
                    List.fold_left
                      (fun (lst,envi,pile,free) texpr ->
                        let (aexp,envi1,pile1,free1) =
                          ttoaexpr envi pile free texpr
                        in (aexp::lst,envi1,pile1,free1))
                      ([],varenv,pile,free) lst
                  in (AEbloc (List.rev alst,pile-pile1),
                      varenv,pile,free1);;

let ttoavarglob varenv (var:Typetree.tvar) =
  (var.nom,(fst4 (ttoaexpr varenv (-1) ENV.empty var.decl))),
  (ENV.add var.nom ((AVglobal var.nom),var.typ) varenv);;

let ttoafonction varenv (f:Typetree.tfonction) =
  (*pour gerer les doublons*)
  let n = match ENV.find_opt f.nom varenv with
    | Some (_,TyFonctionGlobale k) -> k+1 | _ -> 0 in
  (*on ajoute les arguments a l'envers*)
  let varenv1 = ENV.add f.nom ((AVglobal f.nom),TyFonctionGlobale n) varenv
  in let newenv = fst (List.fold_right (fun (id,ty) (envi,i) ->
                           (ENV.add id ((AVarg i),ty) envi,i+1))
                         f.params (varenv1,2)) (*apres adresse retour*)
  in ({nom=(prefix n)^f.nom;
       corps=fst4 (ttoaexpr newenv (-1) ENV.empty f.corps)},varenv1);;
      (*le type de la fonction n'importe pas ici*)

let ttoaclasse varenv (c:Typetree.tclasse) =
  (*pour gerer les doublons*)
  let n = match ENV.find_opt c.nom varenv with
    | Some (_,TyClasseGlobale k) -> k+1 | _ -> 0 in
  (*on ajoute les arguments du constructeur a l'envers*)
  let newenv = fst (List.fold_right (fun (id,ty) (envi,i) ->
                        (ENV.add id ((AVarg i),ty) envi,i+1))
                      c.params (varenv,3))
                      (*3 = apres l'adresse retour et le bloc objet*)
  and (cenv1,i) = List.fold_left (fun (envi,i) (id,_) ->
                      (CLASSEENV.add id i envi,i+1))
                    (CLASSEENV.empty,0) c.params
  in let (cenv2,_) = List.fold_left (fun (envi,i) (var:Typetree.tvar) ->
                         (CLASSEENV.add var.nom i envi,i+1))
                       (cenv1,i) c.declVar
  in Hashtbl.add classeshtbl c.nom cenv2;
     ({nom=(prefix n)^c.nom;
       declVar = List.map (fun (id,_)->
                     AEacces (AAccvar (fst (ENV.find id newenv))))
                 c.params@List.map (fun var->
                     fst4 (ttoaexpr newenv (-1) ENV.empty var.decl)) c.declVar},
     (ENV.add c.nom ((AVglobal c.nom),TyClasseGlobale n)) varenv);;
     (*le type de la classe n'importe pas*)

let ttoafichier f =
  let vars = ref [] and classes = ref [] and fonctions = ref [] in
  let rec aux varenv = function
    | [] -> ()
    | t::q -> aux
      (match t with
      | TDeclVar var -> let (v,e) = (ttoavarglob varenv var) in app vars v;e
      | TDeclClasse classe -> let (c,e) = (ttoaclasse varenv classe)
                              in app classes c;e
      | TDeclFonction fonction -> let (f,e) = (ttoafonction varenv fonction)
                                  in app fonctions f;e )
      q
  in aux baseenv f; {vars=List.rev !vars; constructeurs=List.rev !classes;
                     fonctions=List.rev !fonctions;lambdas= !lambdas;
                     constants= !constants};;
                     (*lambdas est une variable globale*)
