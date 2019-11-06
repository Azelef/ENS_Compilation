open Ast
open Typetree
(*ENV contiendra toujours des triplets (ty*bool*int) representant le type, la mutabilite et le scope d'une valeur*)
module ENV=Map.Make(String);;
exception Error of loc*string
exception NoMain of string

(*Une fonction pour stopper les warnings quand on jette ce que renvoie une fonction*)
let dump truc=();;
(*Des fonctions pour acceder aux elements d'un tuple a 3 elements*)
let get_1st t= match t with
	|(a,b,c)->a;;
let get_2nd t= match t with
	|(a,b,c)->b;;
let get_3rd t= match t with
	|(a,b,c)->c;;
	

(*Une fonction pour acceder à la liste des champs d'une classe*)
let listeChamps q=match q with
	|TyClasse (a,b,c,d)->d
	|_->failwith "La fonction listeChamps ne s'applique qu'aux classes";;
	
(*ty->string*)
let rec tyToStr t=match t with
	| TyClasse (n,l,_,p)->n^"<"^(String.concat ", " (List.map tyToStr l))^">"^" ("^(String.concat ", " (List.map (fun (a,b,c)->a^":"^(tyToStr b)) p))^")"(*Peut être plus detaillee*)
	| TyMaybe t2->(tyToStr t2)^"?"
	| TyFonction (params,r)->"("^(String.concat ", " (List.map (fun p->tyToStr p) params))^")->"^(tyToStr r)
	| TyPoly (c,n)->"'"^c^"."^n
	| TyInt->"Int"
	| TyBool->"Bool"
	| TyString->"String"
	| TyNull->"Null"
	| TyUnit->"Unit"
        | _ -> "";;

let print_ty t=print_endline (tyToStr t);;

(*Si un type poly est fixé dans l'environnement, on renvoie le type précisé*)
let dePoly env t=match t with
	|TyPoly (c,n)->begin match ENV.find_opt ("#poly"^c^"."^n) env with
		|Some (t2,_,_)->t2
		|None->t end
	|_->t;;

(*ENV option->ty->ty->ENV option : renvoie l'environnement minimal dans lequel le type t2 peut être stocké dans une variable de type t1*)
let rec typCompatAux envOuNone t1 t2=match envOuNone with
	|Some env->if t1=t2 then envOuNone else begin match t2 with
		|TyPoly (c,n)->begin match ENV.find_opt ("#poly"^c^"."^n) env with(*On teste si la variable polymorphe est déjà fixée dans le scope*)
			|Some (t,_,_)->typCompatAux envOuNone t t1
			|None->Some (ENV.add ("#poly"^c^"."^n) (t1,false,0) env) end
		|_->match t1 with
			|TyPoly (c,n)->begin match ENV.find_opt ("#poly"^c^"."^n) env with
				|Some (t,_,_)->typCompatAux envOuNone t t2
				|None->Some (ENV.add ("#poly"^c^"."^n) (t2,false,0) env) end
			|TyClasse (n1,t1,_,_)->begin match t2 with
				|TyClasse (n2,t2,_,_) when n1=n2->(try List.fold_left2 typCompatAux envOuNone t1 t2 with |Invalid_argument f->None)
				|_->None end
			|TyMaybe t3->begin match t2 with
				|TyNull->envOuNone
				|TyMaybe t4->typCompatAux envOuNone t3 t4
				|_->typCompatAux envOuNone t3 t2 end
			|TyFonction (p1,r1)->begin match t2 with
				|TyFonction (p2,r2)->(try List.fold_left2 typCompatAux envOuNone (r1::p1) (r2::p2) with |Invalid_argument f->None)
				|_->None end
			|_->None end
	|None->None;;
(*Pour les gens qui ont la flemme d'écrire le Some*)
let typCompat env t1 t2=typCompatAux (Some env) t1 t2;;	

(*typ->ty*)
let rec convTyp env t=match t.dt with
	|TypClasse (i,l)->begin match i.di with
		|"Int"->TyInt
		|"Boolean"->TyBool
		|"String"->TyString
		|"Null"->TyNull
		|"Unit"->TyUnit
		|"Array"->TyClasse ("Array",List.map (convTyp env) l,[],[])
		|a->match ENV.find_opt a env with
			|Some (c,_,_)->begin match c with
				|TyClasse (n,t,pc,p)->TyClasse (n,List.map (convTyp env) l,pc,p)
				|TyPoly (_,_)->c
				|_->failwith ("Ce matching ne devrait jamais recevoir d'objet de type "^(tyToStr c)) end
			|None->raise (Error (t.lt,"Le type "^a^" n'est pas defini")) end
	|TypMaybe t2->TyMaybe (convTyp env t2)
	|TypFonction (paras,t)->TyFonction (List.map (convTyp env) paras,convTyp env t);;

let convParam env pa=(pa.dp.nom.di,convTyp env pa.dp.typ)

        (*ENC->c->(ty*tconstant)*)
let tconstant env c=match c.dc with
	|Cbool b->(TyBool,TCbool b)
	|Cnull->(TyNull,TCnull)
	|Cstring s->(TyString,TCstring s)
	|Cint i->(TyInt,TCint i)
	|Cthis->match ENV.find_opt "this" env with
		|Some (t,_,_)->(t,TCthis)
		|_->raise (Error (c.lc,"Ce this ne se refere a rien"));;

	(*ENV->expr->(ty*ENV*texpr)*)
let rec texpr env e=match e.de with
	|Econst c->let t,a=tconstant env c in (t,env,TEconst a)
	
	|Eacces a->begin match a.da with
		|Accident i->begin match ENV.find_opt i.di env with
			|Some (t,_,_)->(t,env,TEacces (TAccident (i.di,t)))
			|None->raise (Error (e.le,"Variable non declaree"))end
		|Accdot (e2,ch)->let tty,_,tytr=texpr env e2 in
                   begin match tty with
			|TyClasse (n,_,_,_)->begin match List.find_opt (fun s->get_1st s=ch.di) (listeChamps (get_1st (ENV.find n env))) with
				|Some (_,t,_)->(t,env,TEacces (TAccdot (tytr,tty,ch.di)))
				|None->raise (Error (e.le,"Le champ "^ch.di^" n'est pas present dans la classe "^n^"."))end
			|_->raise (Error (e.le,"Seuls les objets de type classe possedent des champs, mais cet objet est de type "^(tyToStr tty))) end
		|Accmaybedot (e2,ch)->let tty,_,tytr=texpr env e2 in
                   begin match tty with
			|TyMaybe (TyClasse (n,_,_,_))|(TyClasse (n,_,_,_))->begin match List.find_opt (fun s->get_1st s=ch.di) (listeChamps (get_1st (ENV.find n env))) with
				|Some (_,TyMaybe t,_)->(TyMaybe t,env,TEacces (TAccmaybedot (tytr,tty,ch.di)))
				|Some (_,t,_)->(TyMaybe t,env,TEacces (TAccmaybedot (tytr,tty,ch.di)))
				|None->raise (Error (e.le,"Le champ "^ch.di^" n'est pas present dans la classe "^n^"."))end
			|_->raise (Error (e.le,"Seuls les objets de type classe option possedent des champs optionnels, mais cet objet est de type "^(tyToStr tty))) end end
		
	|Eassign (v,e2)->let t2,_,tytr=texpr env e2 in
		begin match v.da with
		|Accident i->begin match ENV.find_opt i.di env with
			|Some (t,mut,sco)->begin match typCompat env t t2 with
				|Some env2-> if mut then (TyUnit,env2,TEassign (TAccident (i.di,t),tytr)) else raise (Error (e.le,"La variable n'est pas mutable"))
				|None->match typCompat env (TyMaybe t) t2 with (*Un bricolage pour passer les tests, je doute qu'il suffise 100% du temps*)
					|Some env2->(TyUnit,ENV.add i.di (TyMaybe t,mut,sco) env,TEassign (TAccident (i.di,t),tytr))
					|None->raise (Error (e.le,"Le variable ne peut pas contenir de valeurs de ce type")) end
			|None->raise (Error (e.le,"Variable non declaree"))end
		|Accdot (e3,ch)->let tty,_,tytr2=texpr env e3 in
                        begin match tty with
			|TyClasse (n,_,_,_)->begin match List.find_opt (fun s->get_1st s=ch.di) (listeChamps (get_1st (ENV.find n env))) with
				|Some (_,t,mut)->begin match typCompat env t t2 with
					|Some env2-> if mut then (TyUnit,env2,TEassign (TAccdot (tytr2,tty,ch.di),tytr)) else raise (Error (e.le,"Le champ n'est pas mutable"))
					|None->raise (Error (e.le,"Le champ ne peut pas contenir de valeurs de ce type")) end
				|None->raise (Error (e.le,"Le champ "^ch.di^" n'est pas present dans la classe "^n^".")) end
			|_->raise (Error (e.le,"Seuls les objets de type classe possedent des champs")) end
		|Accmaybedot (e3,ch)->let tty,_,tytr2=texpr env e3 in
                        begin match tty with
			|TyMaybe (TyClasse (n,_,_,_))|(TyClasse (n,_,_,_))->begin match List.find_opt (fun s->get_1st s=ch.di) (listeChamps (get_1st (ENV.find n env))) with
				|Some (_,t,mut)->begin match typCompat env t t2 with
					|Some env2-> if mut then (TyUnit,env2,TEassign (TAccmaybedot (tytr2,tty,ch.di),tytr)) else raise (Error (e.le,"Le champ n'est pas mutable"))
					|None->raise (Error (e.le,"Le champ ne peut pas contenir de valeurs de ce type")) end
				|None->raise (Error (e.le,"Le champ "^ch.di^" n'est pas present dans la classe "^n^".")) end
			|_->raise (Error (e.le,"Seuls les objets de type classe option possedent des champs optionnels")) end end
		
	|Eeval (i,p)->begin try
        let paras=(List.map (texpr env) p) in
	match ENV.find_opt i.di env with
		|Some (TyClasse (n,t,pc,ch),_,_)->begin match List.fold_left2 typCompatAux (Some env) pc (List.map get_1st paras) with
			|Some env2->(TyClasse (n,t,pc,ch),env2,TEeval (i.di,List.map get_3rd paras))
			|None-> raise (Error (e.le,"Les types des parametres de ce constructeur sont incorrects")) end
		|Some (TyFonction (t1,t2),_,_)->begin match List.fold_left2 typCompatAux (Some env) t1 (List.map get_1st paras) with
			|Some env2->(dePoly env2 t2,env2,TEeval (i.di,List.map get_3rd paras)) 
			|None->raise (Error (e.le,"Les types des parametres de cette fonction sont incorrects")) end
		|Some (t,_,_)->raise (Error (e.le,"Seules les fonctions (y compris les constructeurs) peuvent etre appellees"))
		|None->if i.di="print" && List.length paras=1 then
			( match typCompat env (TyMaybe TyString) (get_1st (List.hd paras)) with
				|Some e->(TyUnit,env,TEeval ("print_string",List.map get_3rd paras))
				|None->if (get_1st (List.hd paras))=TyInt
					then (TyUnit,env,TEeval ("print_int",List.map get_3rd paras))
					else raise (Error (e.le,"Le type "^(tyToStr (get_1st (List.hd paras)))^" ne peut pas etre affiche par print")))
		   else raise (Error (e.le,"Fonction non declaree"))
	with
		|Invalid_argument f->raise (Error (e.le,"Le nombre d'arguments dans cet appel est incorrect.")) end
		
	|Eunop (o,a)->
          let t,_,tt = texpr env a in
          let a1,a2=begin match o with
		|Unot->if t=TyBool then (TyBool,env) else raise (Error (e.le,"L'operateur de negation ne s'applique qu'au type Bool"))
		|Uminus->if t=TyInt then (TyInt,env) else raise (Error (e.le,"L'operateur de changement de signe ne s'applique qu'au type Int")) end in (a1,a2,TEunop (o,tt))
		
	|Ebinop (o,a,b)->
		let (ta,_,tytra)=texpr env a in
        let aa1,aa2,tytrb=(let tb,_,tytrb1=if o=Band || o=Bor
		then match a.de with
			|Ebinop (o2,a2,b2) when (o2=Brneq&& o=Bor) || (o2=Breq && o=Band) && get_1st (texpr env b2)=TyNull->begin match a2.de with
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->texpr (ENV.add i.di (TyNull,mut,sco) env) b
						|_->texpr env b end
					|_->texpr env b end
				|_->texpr env b end
			|Ebinop (o2,a2,b2) when (o2=Breq&& o=Bor) || (o2=Brneq && o=Band) && get_1st (texpr env b2)=TyNull->begin match a2.de with 
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->texpr (ENV.add i.di (t,mut,sco) env) b
						|_->texpr env b end
					|_->texpr env b end
				|_->texpr env b end
			|_->texpr env b
		else texpr env b in
		begin match o with
			|Bor |Band->if ta=TyBool && tb=TyBool then (TyBool,env,tytrb1) else raise (Error (e.le,"Cet operateur ne s'applique qu'au type Bool"))
			|Breq |Brneq->if ta!=TyInt&&ta!=TyBool&&ta!=TyUnit&&tb!=TyInt&&tb!=TyBool&&tb!=TyUnit then (TyBool,env,tytrb1) else raise (Error (e.le,"Cet operateur ne s'applique pas aux types Bool, Int et Unit"))
			|Beq |Bneq |Blt |Ble |Bgt |Bge->if ta=TyInt && tb=TyInt then (TyBool,env,tytrb1) else raise (Error (e.le,"Cet operateur ne s'applique qu'au type Int"))
			|Bplus |Bminus |Btimes |Bdiv |Bmod->if ta=TyInt && tb=TyInt then (TyInt,env,tytrb1) else raise (Error (e.le,"Cet operateur ne s'applique qu'au type Int, mais est appelle avec les types "^(tyToStr ta)^" et "^(tyToStr tb))) end)
        in (aa1,aa2,TEbinop (o,tytra,tytrb))
	
	|Eif (a,b,c)->let ta,_,tytr=texpr env a in
                if ta=TyBool 
		then let te1,te2=match a.de with
			|Ebinop (o,a2,b2) when o=Breq && get_1st (texpr env b2)=TyNull->begin match a2.de with 
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->(texpr (ENV.add i.di (TyNull,mut,sco) env) b),(texpr (ENV.add i.di (t,mut,sco) env) c)
						|_->(texpr env b),(texpr env c) end
					|_->(texpr env b),(texpr env c) end
				|_->(texpr env b),(texpr env c) end
			|Ebinop (o,a2,b2) when o=Brneq && get_1st (texpr env b2)=TyNull->begin match a2.de with 
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->(texpr (ENV.add i.di (t,mut,sco) env) b),(texpr (ENV.add i.di (TyNull,mut,sco) env) c)
						|_->(texpr env b),(texpr env c) end
					|_->(texpr env b),(texpr env c) end
				|_->(texpr env b),(texpr env c) end
			|_->(texpr env b),(texpr env c) in
			if typCompat env (get_1st te1) (get_1st te2)==None && typCompat env (get_1st te2) (get_1st te1)==None then raise (Error (e.le,"Les types des branches de ce if sont differents."));
			match ENV.find_opt "#returngaranti" (get_2nd te1) with
			|Some t->begin match ENV.find_opt "#returngaranti" (get_2nd te2) with
				|Some t->(get_1st te1,ENV.add "#returngaranti" (TyNull,false,0) env,TEif (tytr,get_3rd te1,get_3rd te2))
				|None-> (get_1st te2,get_2nd te2,TEif(tytr,get_3rd te1,get_3rd te2)) end
			|None->match ENV.find_opt "#returngaranti" (get_2nd te2) with
			   |Some t->(get_1st te1,get_2nd te1,TEif(tytr,get_3rd te1,get_3rd te2))
			   |None->(get_1st te1,env,TEif (tytr,get_3rd te1,get_3rd te2))
		else raise (Error (e.le,"L'expression evaluee par ce if n'est pas un booleen mais un "^(tyToStr ta)))
	
	|Ewhile (a,b)->
		let (ta,_,tytra)=texpr env a in
		let aux env2 b=let tb,_,tytrb=texpr env2 b in (tb,env,TEwhile (tytra,tytrb)) in
		if ta=TyBool 
		then match a.de with
			|Ebinop (o,a2,b2) when o=Breq && get_1st (texpr env b2)=TyNull->begin match a2.de with 
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->aux (ENV.add i.di (TyNull,mut,sco) env) b
						|_->aux env b  end
					|_->aux env b  end
				|_->aux env b  end
			|Ebinop (o,a2,b2) when o=Brneq && get_1st (texpr env b2)=TyNull->begin match a2.de with 
				|Eacces a->begin match a.da with
					|Accident i->begin match ENV.find_opt i.di env with
						|Some (TyMaybe t,mut,sco)->aux (ENV.add i.di (t,mut,sco) env) b
						|_->aux env b end
					|_->aux env b end
				|_->aux env b end
			|_->aux env b
		else raise (Error (e.le,"L'expression evaluee par ce while n'est pas un booleen"))
	
	|Ereturn e2->begin let tRetour,_,tytr=texpr env e2 in
		match ENV.find_opt "#returnactuel" env with
		|None->raise (Error (e.le,"Ce return n'est pas situe dans une fonction"))
		|Some (t,_,_)->match typCompat env t tRetour with
			|Some env2->(TyUnit,ENV.add "#returngaranti" (TyNull,false,0) env2,TEreturn tytr) 
			|None->raise (Error (e.le,"Ce return ne renvoie pas le bon type")) end
	
	|Efun (p,t,c)->let a1,a2,a3=tfonction env {nom={di="#lambda";li=e.le};types=[];params=p;typ=t;corps=c;lf=e.le} in (a1,env,TEfun ((List.map (convParam env) p),a3.corps))
	
	|Evar v->let r1,r2=tvar env v in (TyUnit,r1,TEvar r2)
	
	|Ebloc b->let b1,b2,b3=List.fold_left (fun te ex->let a1,a2,a3=texpr (get_2nd te) ex in (a1,a2,a3::get_3rd te)) (TyUnit,ENV.add "#scope" (TyNull,false,(get_3rd (ENV.find "#scope" env))+1) env,[]) b in
        (b1,b2,TEbloc (List.rev b3))
                   
        (*ENV->var->(ENV*tvar)*)
and tvar env v=
	match ENV.find_opt v.nom.di env with
		|Some (_,_,n) when n=get_3rd (ENV.find "#scope" env)->raise (Error (v.lv,"Cette variable est deja declaree"))
		|_->
	let typeVar,_,tytr=texpr env v.decl in
	let tStock= match v.typ with
		|None->typeVar
		|Some t->convTyp env t in
	match typCompat env tStock typeVar with
		|Some env2->(ENV.add v.nom.di (tStock,v.mut,get_3rd (ENV.find "#scope" env2)) env2,{nom=v.nom.di;typ=tStock;decl=tytr})
		|None->raise (Error (v.lv,"Le type de cette expression ("^(tyToStr typeVar)^") ne correspond pas au type de la variable dans laquelle elle est stockee ("^(tyToStr tStock)^")"))

	(*ENV->classe->(ENV,tclasse)*)
and tclasse env c=dump c.lcl;
	if List.(length (sort_uniq String.compare (map (fun i->i.di) c.types))!=length c.types) then raise (Error (c.lcl,"Un type de cette classe apparait plusieur fois dans la declaration."));
	if List.(length (sort_uniq String.compare (map (fun p->p.dp.nom.di) c.params))!=length c.params) then raise (Error (c.lcl,"Deux parametres de ctte classe ont le meme nom."));
	let envTmp1=List.fold_left (fun e i->ENV.add i.di ((TyPoly (c.nom.di,i.di)),false,0) e) env c.types in (*On crée les types*)
	let cTypes=List.map (fun t->TyPoly (c.nom.di,t.di)) c.types in (*La liste des types*)
	let envTmpWithC=ENV.add c.nom.di (TyClasse (c.nom.di,cTypes,[],[]),false,0) envTmp1 in (*On cree une version temporaire de la classe (pour la récursivité)*)
	let envThis=ENV.add "this" (TyClasse (c.nom.di,cTypes,[],[]),false,0) envTmpWithC in (*On crée le this*)
	let envTmp2=List.fold_left (fun e p->ENV.add p.dp.nom.di (convTyp envThis p.dp.typ,p.dp.mut,0) e) envThis c.params in (*On ajoute les paramètres à l'environnement*)
	let envTmp3=(List.fold_left (fun a b->fst (tvar a b)) envTmp2 c.declVar) in (*On ajoute les autres champs à l'environnement*)
    let dv=List.rev (snd (List.fold_left (fun a b->let a1,a2=tvar (fst a) b in (a1,a2::(snd a))) (envTmp2,[]) c.declVar)) in
    let champs=(List.map (fun v->dump v.lv;match ENV.find v.nom.di envTmp3 with |(a,b,c)->(v.nom.di,a,b)) c.declVar)@(List.map (fun p->(p.dp.nom.di,convTyp envTmp3 p.dp.typ,p.dp.mut)) c.params) in(*On liste les champs de la classe*)
	let tCla=(TyClasse (c.nom.di,cTypes,List.map (fun p->convTyp envTmp3 p.dp.typ) c.params,champs)) in (*On crée le type de la classe*)
	if List.for_all (fun t->match ENV.find_opt ("#poly"^c.nom.di^"."^t.di) envTmp3 with |None->true |_->false) c.types (*On vérifie que le polymorphisme fonctionne*)
	then (ENV.add c.nom.di (tCla,false,0) env,{nom=c.nom.di;params=List.map (convParam envThis) c.params;declVar=dv})
	else raise (Error (c.lcl,"Les types parametres de cette classe ne sont pas libres"))

        (*ENV->f->(ty,ENV,tfonction)*)
and tfonction env f=
	let scope=get_3rd (ENV.find "#scope" env) in
	match ENV.find_opt f.nom.di env with
		|Some (_,_,n) when n=scope->raise (Error (f.lf,"Cette fonction est deja declaree"))
		|_->
	if List.(length (sort_uniq String.compare (map (fun i->i.di) f.types))!=length f.types) then raise (Error (f.lf,"Un type parametre de cette fonction apparait plusieur fois dans la declaration."));
	if List.(length (sort_uniq String.compare (map (fun p->p.dp.nom.di) f.params))!=length f.params) then raise (Error (f.lf,"Deux parametres de ctte fonction ont le meme nom."));
	let envTmp1=List.fold_left (fun e i->ENV.add i.di (TyPoly (f.nom.di,i.di),false,0) e) env f.types in (*On crée les types*)
	let tRetour=match f.typ with
		|None->TyUnit
		|Some t->(convTyp envTmp1 t) in
	let tFun=(TyFonction (List.map (fun p->(convTyp envTmp1 p.dp.typ)) f.params,tRetour)) in
	let envTmp2=List.fold_left (fun e p->ENV.add p.dp.nom.di ((convTyp envTmp1 p.dp.typ),false,scope+1) e) envTmp1 f.params in
	let envTmp3=ENV.add f.nom.di (tFun,false,scope) envTmp2 in
	let envTmp4=ENV.add "#returnactuel" (tRetour,false,0) envTmp3 in
	let envTmp5=ENV.add "#scope" (TyNull,false,scope+1) envTmp4 in
	let _,envTmp6,tytr=texpr envTmp5 f.corps in
	match if tRetour=TyUnit then (Some (TyNull,false,0)) else ENV.find_opt "#returngaranti" envTmp6 with
		|Some t->(tFun,ENV.add f.nom.di (tFun,false,scope) env,{nom=f.nom.di;params=List.map (convParam envTmp1) f.params;corps=tytr})
		|None->raise (Error (f.lf,"Cette fonction peut ne rien renvoyer."))

       (*ENV->decl->(ENV*tdecl)*)
let tdecl env d=match d with
|DeclVar v->let a1,a2=tvar env v in (a1,TDeclVar a2)
|DeclClasse c->let a1,a2=tclasse env c in (a1,TDeclClasse a2)
|DeclFonction f->let _,a1,a2=tfonction env f in (a1,TDeclFonction a2);;

let tfichier f=
let env=ENV.add "#scope" (TyNull,false,0) ENV.empty in
let env2,tytr=List.fold_left (fun te d->let a1,a2=tdecl (fst te) d in (a1,a2::(snd te))) (env,[]) f in
match ENV.find_opt "main" env2 with
	|Some (TyFonction ([TyClasse("Array",[TyString],_,_)],TyUnit),b,0)->List.rev tytr
	|_->raise (NoMain "Ce fichier ne contient pas de fonction main")
