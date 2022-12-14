{

open Lexing
open Error
open Parser
open RawLambda

}

(* -------------------------------------------------------------------------- *)

(* Regular expressions. *)

let newline =
  ('\010' | '\013' | "\013\010")

let whitespace =
  [ ' ' '\t' ]

let lowercase =
  ['a'-'z' '\223'-'\246' '\248'-'\255' '_']

let uppercase =
  ['A'-'Z' '\192'-'\214' '\216'-'\222']

let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']

let digit =
  ['0'-'9']

let regular_car = ['\032' - '\126'] # ['"' '\\']

(* -------------------------------------------------------------------------- *)

(* The lexer. *)

rule entry = parse
| "fun"
    { FUN }
| "in"
    { IN }
| "let"
    { LET }
| "match"
    { MATCH }
| "with"
    { WITH }
| "rec"
    { REC }
| "type"
    { TYPE }
| "forall"
    { FORALL }
| "end"
    { END }
| '"'
    { let str = string (place lexbuf) lexbuf in STRING str }
| "->"
    { ARROW }
| "=>"
    { DARROW }
| "_"
    { UNDERSCORE }
| "="
    { EQ }
| ","
    { COMMA }
| ":"
    { COLON }
| "|"
    { PIPE }
| "("
    { LPAREN }
| ")"
    { RPAREN }
| "+"
    { ADDOP OpAdd }
| "-"
    { ADDOP OpSub }
| "*"
    { STAR }
| "/"
    { DIV }
| "<"
    { CMPOP CmpLt }
| "<="
    { CMPOP CmpLe }
| ">"
    { CMPOP CmpGt }
| ">="
    { CMPOP CmpGe }
| "="
    { CMPOP CmpEq }
| (lowercase identchar *) as x
    { IDENT x }
| (uppercase identchar *) as x
    { CONS x }
| digit+ as i
    { try
        INTLITERAL (int_of_string i)
      with Failure _ ->
        error (place lexbuf) "invalid integer literal." }
| "(*"
    { ocamlcomment (place lexbuf) lexbuf; entry lexbuf }
| newline
    { new_line lexbuf; entry lexbuf }
| whitespace+
    { entry lexbuf }
| eof
    { EOF }
| _ as c
    { error (place lexbuf) "unexpected character: '%c'." c }

(* ------------------------------------------------------------------------ *)

  (* Skip OCaml-style comments. Comments can be nested. This sub-lexer is
   parameterized with the place of the opening comment, so if an unterminated
   comment is detected, we can show where it was opened. *)

and ocamlcomment p = parse
| "*)"
    { () }
| "(*"
    { ocamlcomment (place lexbuf) lexbuf; ocamlcomment p lexbuf }
| newline
    { new_line lexbuf; ocamlcomment p lexbuf }
| eof
    { error p "unterminated comment." }
| _
    { ocamlcomment p lexbuf }

and string p = parse
  | '\\' 'n' 
    { "\\n" ^ (string p lexbuf) }
  | '\\' '\\' 
    { "\\" ^ (string p lexbuf) }
  | '\\' 't' 
    { "\\t" ^ (string p lexbuf) }
  | '\\' '"'
    { "\\\"" ^ (string p lexbuf) }
  | '"' 
    { "" }
  | regular_car* as c 
    { c ^ (string p lexbuf) }
  | _ 
    { error p "Ill-formed string." }
    