open Utilities

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

let convert_fml v delta =
  try
    let cls = List.assoc v delta in
    let l = List.length cls in
    let f acc q i = match acc with
      | Bool true -> Var (i,q)
      | _ -> And (acc,(Var (i,q)))
    in
    List.fold_left2 f (Bool true) cls (Utilities.fromto 1 (l+1))
  with Not_found -> Bool false;;

open Syntax;;
let convert_fml2 v delta =
  try
    let fml = List.assoc v delta in
(*    let open Syntax in *)
    let rec go = function
      | FConst "true" -> Bool true
      | FConst _ -> Bool false
      | FVar (i,q) -> Var (i,q)
      | FAnd (f1,f2) -> And (go f1,go f2)
      | FOr (f1,f2) -> Or (go f1, go f2)
    in go fml
  with Not_found -> Bool false;;

let convert alpha st delta =
  List.concat (List.map (fun q -> List.map (fun (a,_) -> 
    ((q,a),convert_fml (q,a) delta)) alpha) st);;

let convert2 alpha st delta =
  List.concat (List.map (fun q -> List.map (fun (a,_) ->
    ((q,a),convert_fml2 (q,a) delta)) alpha) st);;

let from_automaton m =
  let module A = Automaton in
  let st = m.A.st @ List.concat (List.map snd m.A.delta) in
  let st = Utilities.delete_duplication_unsorted st in
  let alpha = A.getalpha m in
  let delta = convert alpha m.A.st m.A.delta in
  { alpha = alpha; st = st; delta = delta; init = m.A.init};;

let negate_state q = q;; (* "~"^q;; *)
let rec negate_formula = function
  | Bool b -> Bool (not b)
  | Var (i,q) -> Var (i,negate_state q)
  | Or (f1,f2) -> And (negate_formula f1,negate_formula f2)
  | And (f1,f2) -> Or (negate_formula f1,negate_formula f2);;

let negate m =
  let st = List.map negate_state m.st in
  let delta = List.map (fun ((q,a),fml) -> 
      ((negate_state q,a),negate_formula fml)) m.delta in
  let init = negate_state m.init in
  { alpha = m.alpha; st = st; delta = delta; init = init};;

let rec string_of_formula = function
  | Bool b -> if b then "true" else "false"
  | Var (i,q) -> "(" ^ string_of_int i ^ "," ^ q ^ ")"
  | Or (f1,f2)  -> "(Or "^ string_of_formula f1 ^" "^ string_of_formula f2 ^")"
  | And (f1,f2)  -> "(And "^ string_of_formula f1 ^" "^ string_of_formula f2 ^")"

let print_formula fml = print_string (string_of_formula fml);;

let print m =
  print_string "alpha:\n";
  List.iter (fun (a,_) -> print_string (a ^ ";")) m.alpha;
  print_string "\n";
  print_string "states:\n";
  print_string "{";
  List.iter (fun q -> print_string (q ^ ";")) m.st;
  print_string "}\n";
  print_string "delta:\n";
  List.iter (fun ((q,a),fml) -> 
    print_string ("(" ^ q ^ "," ^ a ^ ") = ");
    print_formula fml;
    print_newline ()) m.delta;
  print_string ("init: " ^ m.init ^"\n");;
  
let cata b_f v_f or_f and_f fml =
  let rec go = function
    | Bool b -> b_f b
    | Var (i,q)  -> v_f (i,q)
    | Or (f1,f2) -> or_f (go f1) (go f2)
    | And (f1,f2) -> and_f (go f1) (go f2)
  in go fml;;

let states_in_preformula fml = 
(*  let open Syntax in  *)
  let rec go = function
    | FConst _ -> []
    | FVar (i,q) -> [q]
    | FAnd (f1,f2) | FOr (f1,f2) ->
        merge_and_unify compare (go f1) (go f2)
  in go fml;;

module Obdd = Pobdd.Make (struct
    type t = int * state
    let compare = compare
    let hash = Hashtbl.hash end)

let prime_implicants fml =
  let tau = cata (fun b -> if b then Obdd.bdd_true else Obdd.bdd_false)
                 Obdd.bdd_var
                 Obdd.bdd_or
                 Obdd.bdd_and
                 fml in
  let rec go tau = 
    match Obdd.sat_min tau with
    | None -> []
    | Some l -> 
(*        let open Obdd in *)
        let tau = Obdd.bdd_and tau (Obdd.neg (Obdd.bdd_andl (List.map Obdd.bdd_var l))) in
        l :: go tau in
  go tau;;

  

let states_in_tr ((q, a), fml) =
  merge_and_unify compare [q] (states_in_preformula fml);;

let states_in_transitions transitions =
  merge_and_unify_list compare (List.map states_in_tr transitions);;

let from_transitions (ranks,transitions) =
  let alpha = ranks in
  let init = fst (fst (List.hd transitions)) in
  let st = states_in_transitions transitions in
  let delta = convert2 alpha st transitions in
  { alpha = alpha; st = st; delta = delta; init = init };;

