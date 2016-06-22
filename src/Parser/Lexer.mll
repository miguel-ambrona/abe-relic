{
  open Parser
  exception Error1 of string

  let unterminated_comment () =
    raise (Error1 "unterminated comment")
  let unterminated_string () =
    raise (Error1 "unterminated string")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let base64 = ['A'-'Z' 'a'-'z' '0'-'9' '+' '/' '=' '_']
let chars = ['a'-'z' 'A'-'Z' '0'-'9']

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | ","     { COMMA }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "["     { LBRACK }
  | "]"     { RBRACK }
  | "="     { EQ }
  | "and"   { AND }
  | "or"    { OR }

  | "scheme"          { SCHEME }
  | "predicate"       { PREDICATE }
  | "boolean_formula" { BOOL_FORM }
  | "attributes"      { ATTRIBUTES }
  | "repetitions"     { REPETITIONS }
  | "and-gates"       { AND_GATES }
  | "policy"          { POLICY }

  | "k0"  { K0 }
  | "k1"  { K1 }

  | "c0"  { C0 }
  | "c1"  { C1 }
  | "c*"  { CT }
  | "___BEGIN_ABE_CIPHERTEXT___"   { BEGIN_CT }
  | "___END_ABE_CIPHERTEXT___"     { END_CT }

  | "A"   { A_MATRIX }
  | "WA"  { WA_MATRIX }
  | "B"   { B_MATRIX }
  | "WB"  { WB_MATRIX }
  | "mu"  { MU_MSK }
  | "msk" { MSK }

  | '-'?['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | base64* as s { NAME(s)}


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
