(****** Interface definition of OBDD library *******)
type var = int
type bdd
val bdd_true: bdd  
val bdd_false: bdd 
val bdd_var: var -> bdd  (*** (bdd_var x) <--> x is true ***)
val bdd_nvar: var -> bdd (*** (bdd_var x) <--> x is false ***)
val bdd_eq: var -> var -> bdd (*** (bdd_eq x y) <-->  x iff y ***)
val neg: bdd -> bdd           (*** negation ***)
val bdd_or: bdd -> bdd -> bdd 
val bdd_and: bdd -> bdd -> bdd
val bdd_orl: bdd list -> bdd  (*** take a list of OBDDs and returns disjunction of them ***)
val bdd_andl: bdd list -> bdd (*** take a list of OBDDs and returns conjunction of them ***)
val imp: bdd -> bdd -> bdd  (*** implication ***)
val iff: bdd -> bdd -> bdd  (*** if and only if ***)
val exists: var -> bdd -> bdd  (*** (exists x P) ***)
val exists_vl: var list -> bdd -> bdd (*** (exists [x1,...,xn] P) ***)
val forall: var -> bdd -> bdd   (*** (forall x P) ***)
val forall_vl: var list -> bdd -> bdd  (*** forall [x1,...,xn] P ***)
val rename: (var->var) -> bdd -> bdd  
  (*** rename variables: the renaming function must be monotonic ***)
val relprod: (var->bool) -> bdd -> bdd -> bdd  (*** relational product ***)
  (*** (relprod [x1,...,xn] r1 r2) <---> exists x1,...,xn.(r1/\r2 ***)
val apply: int -> bdd -> bdd -> bdd   
  (*** apply n-ary function (as a 2n-ary relation)  ***)
  (*** (apply n f p)(x1,...,xn) <->
   ***    exists x1',...,xn'.(p(x1',...,xn') && f(x1',x1,...,xn',xn)
   ***)
val normalize: bdd -> bdd (*** normalize BDD ***)
val equiv: bdd -> bdd -> bool (*** Check equivalence of two OBDDs ***)
val cata: (var->'a->'a ->'a) -> (bool->'a) -> bdd -> 'a  (*** catamorphism on the OBDD structure ***)
val fixp: (bdd->bdd) -> bdd -> bdd 
     (*** t = fixp f x <--> f^n(x)=t and f(t)=t for some n ***)
val reset: unit -> unit
     (*** reset cache  ***)


(*** The following functions are for debugging ***)
type varnp = POS of var | NEG of var  (*** constructors to show BDD ***)
val to_dnf: bdd -> (varnp list) list (*** convert OBDD to disjunctive normal form ***)
val list_of_nodes: bdd -> bdd list   (*** Returns the list of sub-nodes of OBDD ***)
val size: bdd -> int                 (*** Returns the size of OBDD ***)


(* add by Taku Terao *) 
(* returns a minimal saturation if the OBDD is satisfiable 
 * otherwise return None  
 * *)
val sat_min : bdd -> (var list) option
val print_as_dot : bdd -> (var -> unit) -> unit
