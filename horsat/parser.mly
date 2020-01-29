%{
open Syntax
%}

%token <string> NAME
%token <string> NONTERM
%token <int> INT
%token CASE
%token COMMA
%token DP
%token ARROW
%token PERIOD
%token LPAR
%token RPAR
%token BEGING
%token ENDG
%token BEGINA
%token ENDA
%token <string> ML
%token EOF

%start main
%type <Syntax.prerules * Syntax.transitions> main
%type <Syntax.prerules> rules
%type <Syntax.prerule> rule
%type <string list> names
%type <Syntax.preterm> term
%type <Syntax.preterm> pterm
%type <Syntax.preterm list> pterms
%type <Syntax.transitions> transitions
%type <Syntax.transition> transition
%%

main:
  gram automaton EOF
  { ($1, $2)  }
;
gram:
  BEGING rules ENDG
  {$2}
;
rules:
   rule 
   {[$1]}
 | rule rules
   {$1::$2}
;
rule:
  NONTERM names ARROW term PERIOD
  {($1, $2, $4)}
|
  NONTERM  ARROW term PERIOD
  {($1, [], $3)}
;
pterm:
  NONTERM
  {PTapp(NT($1), [])}
| NAME 
  {PTapp(Name($1),[])}
| LPAR term RPAR
  {$2}
| LPAR term COMMA term RPAR
  {PTapp(PAIR, [$2; $4])}
| INT
  {PTapp(FD($1), [])}
;
term:
  pterms
  {match $1 with
     [] -> assert false
   | [x] -> x
   | x::terms ->
      match x with
        PTapp(h,l) -> PTapp(h, l@terms)}
| CASE INT pterm pterms
  {PTapp(CASE($2), $3::$4)}
| DP pterm pterms
  {PTapp(DPAIR, $2::$3)}
;
pterms:
  pterm
  {[$1]}
| pterm pterms
  {$1::$2}
;
names:
  NAME
  {[$1]}
| NAME names
  {$1::$2}
;

automaton:
  BEGINA transitions ENDA
  {$2}
;
transitions:
  transition
  {[$1]}
| transition transitions
  {$1::$2}

transition:
  NAME NAME ARROW  PERIOD
 {(($1, $2), [])}
| NAME NAME ARROW names  PERIOD
 {(($1, $2), $4)}
;