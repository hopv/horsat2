module type OrderedType =
  sig
    type t
    val compare : t -> t -> int
    val hash : t -> int
  end;;

module type S =
  sig
    type var
    type bdd
    type zdd
    type varnp = POS of var | NEG of var
    val node_id : bdd -> int
    val bdd_true : bdd
    val bdd_false : bdd
    val bdd_var  : var -> bdd
    val bdd_nvar : var -> bdd
    val bdd_vars : bdd -> var list
    val neg      : bdd -> bdd 
    val bdd_and  : bdd -> bdd -> bdd 
    val imp      : bdd -> bdd -> bdd
    val bdd_or   : bdd -> bdd -> bdd
    val bdd_orl  : bdd list -> bdd 
    val bdd_andl : bdd list -> bdd
    val exists   : var -> bdd -> bdd
    val exists_vl: var list -> bdd -> bdd 
    val forall   : var -> bdd -> bdd 
    val forall_vl: var list -> bdd -> bdd 
    val imp_and_exists : bdd -> var -> bdd -> bdd
    val restrict_sorted : bdd -> varnp list -> bdd
    val size     : bdd -> int
    val equiv    : bdd -> bdd -> bool
    val cata     : (var -> 'a -> 'a -> 'a) -> (bool -> 'a) -> bdd -> 'a
    val sat_min  : bdd -> (var list) option
    val sat_min_while : (var -> bool) -> bdd -> (var list * var list * bdd) option
    val prime_implicants : bdd -> zdd
    val zdd_elim : zdd -> (var -> bool) -> zdd
    val zdd_enum : zdd -> var list list
    val print_as_dot : bdd -> (var -> unit) -> unit
    val run_gc   : bdd list -> unit
  end;;

module Make : functor (Elt : OrderedType) -> S with type var = Elt.t
