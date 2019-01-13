{
open Parser
exception LexError of string
let line_no = ref 1
let end_of_previousline = ref 0
}

let space = [' ' '\t' '\r']
let newline = ['\n']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule token = parse
| space+
    { token lexbuf }
| newline
    { end_of_previousline := (Lexing.lexeme_end lexbuf);
      line_no := !line_no+1;
      token lexbuf}
| "/*"
    { comment lexbuf;
      token lexbuf }
| "_case" {CASE}
| "_fun" {FUN}
| "_dcons" {DP}
| digit digit* 
   {let s = Lexing.lexeme lexbuf in
     INT(int_of_string s)}
| lower (digit|lower|upper|'_')*
    { let s = Lexing.lexeme lexbuf in
         NAME(s)}
| upper (digit|lower|upper|'_')*
    { let s = Lexing.lexeme lexbuf in
        NONTERM(s)}
| "%BEGING"
    {BEGING}
| "%ENDG"
    {ENDG}
| "%BEGINA"
    {BEGINA}
| "%ENDA"
    {ENDA}
| "%BEGINATA"
    {BEGINATA}
| "%ENDATA"
    {ENDATA}
| "%BEGINR"
    {BEGINR}
| "%ENDR"
    {ENDR}
| ","
    {COMMA}
| "->"
    {ARROW}
| "="
    {ARROW}
| "("
    {LPAR}
| ")"
    {RPAR}
| "<"
    {LBRA}
| ">"
    {RBRA}
| "/\\"
    {AND}
| "\\/"
    {OR}
| "."
    {PERIOD}
| "%BEGINML" [^ '%']* "%ENDML"
     {let s = Lexing.lexeme lexbuf in
      let s' = String.sub s 8 (String.length s - 14) in
        ML(s')}
| eof
    { EOF }
| _
    { Format.eprintf "unknown token %s in line %d, column %d-%d @."
	(Lexing.lexeme lexbuf)
        (!line_no)
	((Lexing.lexeme_start lexbuf)- (!end_of_previousline))
	((Lexing.lexeme_end lexbuf)-(!end_of_previousline));
      failwith "lex error" }
and comment = parse
| "*/"
    { () }
| "/*"
    { comment lexbuf;
      comment lexbuf }
| eof
    {  print_string "Lex error: unterminated comment\n";
       failwith "unterminated comment" }
| _
    { comment lexbuf }
