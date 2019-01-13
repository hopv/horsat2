type state = string;;
type index = int;;
type formula = Bool  of bool 
             | Var   of index * state
             | Or    of formula * formula 
             | And   of formula * formula;;

type t = { alpha : (string * int) list; 
           st    : state list; 
           delta : ((state * string) * formula) list;
           init  : state };;

val from_automaton : Automaton.automaton -> t;;
val from_transitions : (state * int) list * Syntax.ata_trans list -> t;;
val print : t -> unit;;
val negate : t -> t;;
val prime_implicants : formula -> (int * string) list list;;
val cata : (bool -> 'a) -> 
          (index * state -> 'a) -> 
          ('a -> 'a -> 'a) -> (* or *) 
          ('a -> 'a -> 'a) -> (* and *)
          formula -> 
          'a;;

