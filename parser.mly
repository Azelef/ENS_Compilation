
/* Analyseur syntaxique pour Petit Kotlin */

%{
  open Ast

%}

/* Déclaration des tokens */

%token EOF

/* Mots clefs */
%token CLASS IF VAL DATA NULL VAR ELSE RETURN WHILE
%token FALSE THIS FUN TRUE

/* Identifiants */
%token <string> IDENT

/* Constantes */
%token <int> CINT
%token <string> CSTRING

/* Operateurs et autres caractères*/
%token PLUS MINUS TIMES  DIV  MOD  AND  OR  NOT  EQUAL
%token CRG CMPLE CRD CMPGE BEQ  BNEQ  REQ RNEQ LP  RP
%token LAC  RAC  DOT COMMA  COLON  MAYBEDOT  MAYBE  MPSTO COMDOT


/* À COMPLÉTER */

/* Priorités et associativités des tokens */

%nonassoc funtyp
%nonassoc THEN
%nonassoc ELSE
%nonassoc IF
%nonassoc WHILE RETURN
%right EQUAL
%left OR
%left AND
%left BEQ BNEQ REQ RNEQ
%left CRD CRG CMPGE CMPLE
%left PLUS MINUS
%left TIMES DIV MOD
%right NOT /*la précédence de Uminus est définie dans unop:*/
%left DOT MAYBEDOT
%right MPSTO
%nonassoc MAYBE

/* Point d'entrée de la grammaire */
%start fichier

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> fichier

%%

/* Règles de grammaire */

fichier:
    | d = decl* ; EOF  { d }
;
decl:
    | v = var ;  COMDOT { DeclVar v }
    | c = classe { DeclClasse c }
    | f = fonction { DeclFonction f }
;
typedec:
    | COLON ; t = typ { Some t }
    | { None }
;
typesparam:
    | CRG ; ts = separated_nonempty_list(COMMA,ident) ; CRD { ts }
    | { [] }
;

var:
    | VAR ; s = ident; t = typedec; EQUAL; e = expr { {nom=s;
                                                       typ = t;
    	      					       decl = e;
						       mut = true;
						       lv = $loc} }
    | VAL ; s = ident; t = typedec; EQUAL; e = expr { {nom=s;
                                                       typ = t;
						       decl = e;
						       mut = false;
						       lv = $loc} }
;

constant:
    | NULL { { dc = Cnull; lc = $loc} }
    | THIS { { dc = Cthis; lc = $loc} }
    | FALSE { { dc = Cbool false; lc = $loc} }
    | TRUE { { dc = Cbool true; lc = $loc} }
    | i = CINT { { dc = Cint i; lc = $loc} }
    | s = CSTRING { { dc = Cstring s; lc = $loc} }
;

fonction:
    | FUN ; ts=typesparam ; s=ident; LP ;ps=separated_list(COMMA,param) ; RP ;
      t=typedec; e = bloc
      { {nom = s;
         typ = t;
         types = ts;
         params = ps;
         corps = e;
         lf = $loc} }
;
varlist:
    | v = var { [v] }
    | vl = varlist ; COMDOT ; v = var { v::vl }
;
classe:
    | DATA; CLASS; s=ident; ts=typesparam;
      LP ; ps=separated_nonempty_list(COMMA,paramc) ; RP ;
      LAC ; vs=varlist ; COMDOT? ; RAC
      { {nom = s;
         types = ts;
         params = ps;
         declVar = (List.rev vs);
         lcl = $loc} }
    | DATA; CLASS; s=ident; ts=typesparam;
      LP ; ps=separated_nonempty_list(COMMA,paramc) ; RP;
      { {nom = s;
         types = ts;
         params = ps;
         declVar = [];
         lcl = $loc} }
    | DATA; CLASS; s=ident; ts=typesparam;
      LP ; ps=separated_nonempty_list(COMMA,paramc) ; RP; LAC ; RAC
      { {nom = s;
         types = ts;
         params = ps;
         declVar = [];
         lcl = $loc} }
;

param:
    | s=ident ; COLON ;  t=typ { { dp = {nom = s; typ = t; mut = true};
                          lp = $loc } }
;

paramc:
    | VAR ; s=ident ; COLON ; t=typ { { dp = {nom = s; typ = t; mut = true};
                                lp = $loc } }
    | VAL ; s=ident ; COLON ; t=typ { { dp = {nom = s; typ = t; mut = false};
                                lp = $loc } }
;

typ:
    | s=ident { { dt = TypClasse (s,[]);
                  lt = $loc } }
    | s=ident ; CRG ; ts=separated_nonempty_list(COMMA,typ) ; CRD
      { { dt = TypClasse (s,ts);
          lt = $loc } }
    | LP ; t = typ ; RP { t }
    | LP ; te = typ ; RP ; MPSTO ; t = typ %prec funtyp
      { { dt = TypFonction ([te],t);
          lt = $loc } }
    | LP ; RP ; MPSTO ; t = typ
      { { dt = TypFonction ([],t);
          lt = $loc } }
    | LP ; t1 = typ ; COMMA ;  ts=separated_nonempty_list(COMMA,typ) ; RP ;
      MPSTO ; t=typ
      { { dt = TypFonction (t1::ts,t);
          lt = $loc } }
    | t=typ; MAYBE { { dt = TypMaybe t;
                       lt = $loc } }
;

acces:
    | s = ident { { da = Accident s;
                    la = $loc } }
    | e = expr ; DOT ; s = ident { { da = Accdot (e,s);
                                     la = $loc } }
    | e = expr ; MAYBEDOT ; s = ident { { da = Accmaybedot (e,s);
                                          la = $loc } }
;

ifblocexpr:
    | e = expr %prec IF { e }
    | b = bloc  { b }
;

whileblocexpr:
    | e = expr %prec WHILE { e }
    | b = bloc { b }
;

inbloc:
    | v = var { { de = Evar v;
                  le = $loc} }
    | e = expr { e }
;
inbloclist:
    | i = inbloc { [i] }
    | l = inbloclist ; COMDOT ; i=inbloc { i::l }

bloc:
    | LAC ; RAC { { de = Ebloc [];
                    le = $loc } }
    | LAC ; ibs = inbloclist ; COMDOT? ; RAC
      { { de = Ebloc (List.rev ibs);
          le = $loc} }
    
;

expr:
    | c = constant { { de = Econst c;
                       le = $loc} }
    | LP ; e = expr ; RP { e }
    | a = acces { { de = Eacces a;
                    le = $loc} }
    | a = acces; EQUAL ; e = expr { { de = Eassign (a,e);
                                      le = $loc} }
    | s = ident ; LP ; ps = separated_list(COMMA,expr) ; RP
      { { de = Eeval (s,ps);
          le = $loc} }
    | IF ; LP ; e = expr ; RP ; be1 = ifblocexpr; %prec THEN
      { { de = Eif (e,be1,{de = Ebloc []; le = $loc});
          le = $loc } }
    | IF ; LP ; e = expr ; RP ; be1 = ifblocexpr; ELSE ; be2 = ifblocexpr;
      { { de = Eif (e,be1,be2);
          le = $loc } }
    | WHILE ; LP ; e = expr ; RP ; be = whileblocexpr
      { { de = Ewhile (e,be);
          le = $loc } }
    | RETURN { { de = Ereturn { de = Ebloc [];
                                le = $loc };
                 le = $loc } }
    | RETURN ; e = expr { { de = Ereturn e;
                            le = $loc } }
    | FUN ; LP ; ps = separated_list(COMMA,param) ; RP ; t = typedec ; b = bloc
      { { de = Efun (ps,t,b);
          le = $loc } }
    | NOT ; e = expr { { de = Eunop (Unot,e);
                         le = $loc;} }
    | MINUS ; e = expr %prec NOT  { { de = Eunop (Uminus,e);
                                      le = $loc;} }
    | e1 = expr ; b = binop ; e2 = expr  { { de = Ebinop (b,e1,e2);
                                             le = $loc;} }
;

%inline binop:
    | PLUS  { Bplus }
    | MINUS { Bminus }
    | TIMES { Btimes }
    | DIV   { Bdiv }
    | MOD   { Bmod }
    | AND   { Band }
    | OR    { Bor }
    | CRG   { Blt }
    | CMPLE { Ble }
    | CRD   { Bgt }
    | CMPGE { Bge }
    | BEQ   { Beq }
    | BNEQ  { Bneq }
    | REQ   { Breq }
    | RNEQ  { Brneq }
;
ident:
| s = IDENT { { di = s ; li = $loc } }