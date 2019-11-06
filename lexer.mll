
(* Analyseur lexical pour Petit Kotlin *)

{
  open Lexing
  open Parser

  (* exception à lever pour signaler une erreur lexicale *)
  exception Lexing_error of string

  let keyword_or_ident =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["class", CLASS; "if", IF; "val", VAL;
       "data", DATA; "null", NULL; "var", VAR;
       "else", ELSE; "return", RETURN; "while", WHILE;
       "false", FALSE; "this", THIS;
       "fun", FUN; "true", TRUE
       ];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s;;
  
  let string_buffer = Buffer.create 1024;;
}

let chiffre = ['0'-'9']
let alpha = ['a'-'z'] | ['A'-'Z'] | '_'

let bit = '0' | '1'
let hexa = ['0'-'9'] | ['a'-'f'] | ['A'-'F']

let ident = alpha (alpha | chiffre)*

let entier = chiffre | chiffre (chiffre | '_')* chiffre
             | ("0x"|"0X") (hexa | hexa (hexa | '_')* hexa )
             | ("0b"|"0B") (bit | bit (bit | '_')* bit )
                                                      
rule token = parse
  | [' ' '\t']+                 { token lexbuf }
  | ("\n" | "//" [^'\n']* '\n') { new_line lexbuf; token lexbuf }
  | ident as id                { keyword_or_ident id }
  | entier as s            { try let i = int_of_string s in
                                   if i>=2147483648 then raise (Lexing_error "")
                                   else CINT i
                               with _ ->
                               raise (Lexing_error ("constant too large: "^s))}
  | "/*"    { comment lexbuf ; token lexbuf }  
  | '\"'    { CSTRING (string lexbuf) }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '*'     { TIMES }
  | "/"     { DIV }
  | '%'     { MOD }
  | "&&"    { AND }
  | "||"    { OR }
  | "!"     { NOT }
  | '='     { EQUAL }
  | "<"     { CRG }
  | "<="    { CMPLE }
  | ">"     { CRD }
  | ">="    { CMPGE }
  | "=="    { BEQ }
  | "!="    { BNEQ }
  | "==="   { REQ }
  | "!=="   { RNEQ }
  | '('     { LP }
  | ')'     { RP }
  | '{'     { LAC }
  | '}'     { RAC }
  | '.'     { DOT }
  | ','     { COMMA }
  | ':'     { COLON }
  | ';'     { COMDOT }
  | "?."    { MAYBEDOT }
  | '?'     { MAYBE }
  | "->"    { MPSTO }
  | eof     { EOF }
  | _       { raise (Lexing_error "invalid character") }
and comment = parse
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | eof  { raise (Lexing_error "commentaire non terminé") }
  | "\n" { new_line lexbuf; comment lexbuf }
  | _    { comment lexbuf }
and string = parse
  | (((['\032'-'\126']#['\\' '\"'])|"\\\\"|"\\\""|"\\n"|"\\t")* as s)'\"'
               { s }
  | _ as c    { raise (Lexing_error ("Invalid character in string: "
                                     ^(Char.escaped c) ) ) }
  | eof       { raise (Lexing_error "unterminated string") }
{

}
