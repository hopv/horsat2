type token =
  | NAME of (string)
  | NONTERM of (string)
  | INT of (int)
  | CASE
  | COMMA
  | DP
  | ARROW
  | PERIOD
  | LPAR
  | RPAR
  | BEGING
  | ENDG
  | BEGINA
  | ENDA
  | ML of (string)
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.prerules * Syntax.transitions
