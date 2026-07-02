{
  open Parser
  open Lexing

  exception Error of string
}


let digit = ['0'-'9']
let hex_digit = ['0'-'9' 'a'-'f']
let int_ = digit+
let dec_float = '-'? (digit* '.' digit+ | digit+ '.')
let hex_float = '-'? '0' ('x'|'X') ('0'|'1') '.' hex_digit+ ('p'|'P') ('+'|'-') digit+
let float_ = dec_float | hex_float
let next_line =   '\r' | '\n' | "\r\n"
let true_ = "true" | "True" | "TRUE"
let false_ = "false" | "False" | "FALSE"
let null_ = "()" | "null" | "None"
let alphanum = ['a'-'z' 'A'-'Z' '0'-'9']
let string_ = alphanum* 

rule token = parse
  | [' ' '\t']   { token lexbuf }(* ignore whitespaces and tabs *)
  | next_line+   { new_line lexbuf; token lexbuf }
  | "(*"         { comment lexbuf }
  | null_        { NullToken }
  | '('          { LeftParenthesisToken }
  | ')'          { RightParenthesisToken }
  | '['          { LeftBracketToken }
  | ']'          { RightBracketToken }
  | ','          { ComaToken }
  | 'N'          { NodeToken }
  | 'L'          { LeafToken }
  | 'V'          { VectorToken }
  | 'T'          { TreeToken }
  | 'F'          { FeatureListToken }
  | "bool"       { BoolFeatureToken }
  | "float"      { FloatFeatureToken }
  | true_        { TrueToken }
  | false_       { FalseToken }
  | int_ as inum    { IntToken (int_of_string inum) }
  | float_ as inum  { FloatToken (float_of_string inum) }
  | '"' (string_ as s) '"'   { StringToken (s) }
  (* | id as text   { IdentToken text } *)
  | eof       { EOF } 
  | _ { raise (Error ("Unexpected char: "^(Lexing.lexeme lexbuf)^" at "^(string_of_int (Lexing.lexeme_start
      lexbuf))^"-"^(string_of_int (Lexing.lexeme_end lexbuf)))) }

and comment = parse
  | "*)"      { token lexbuf }
  | _         { comment lexbuf }


