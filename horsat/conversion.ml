(** BEGIN: conversion from parsing results **)
open Grammar;;
open Utilities;;
open Automaton;;

let rec pterm2term ss pterm =
(** distinguish between variables and terminal symbols **)
  match pterm with
    Syntax.PTapp(h, pterms) ->
     let h' = 
       match h with
         Syntax.Name(s) -> if List.mem s ss then Var(s) else T(s)
       | Syntax.NT(s) -> NT(s)
       | Syntax.CASE(n) -> assert false
       | Syntax.FD(n) -> assert false
       | Syntax.PAIR -> assert false
       | Syntax.DPAIR -> assert false
     in
     let terms = List.map (pterm2term ss) pterms in
        mk_app h' terms
and mk_app h terms =
  match terms with
   [] -> h
 | t::terms' -> mk_app (App(h,t)) terms'

let rec add_var term f =
  match term with
    NT _ -> term
  | T _ -> term
  | Var v -> Var (v^"@"^f)
  | App(t1,t2) -> App(add_var t1 f, add_var t2 f)

let prerule2rule (f, ss, pterm) =
  let term = pterm2term ss pterm in
  let ss' = List.map (fun v->(v^"@"^f)) ss in
  let term' = add_var term f in
  (f, (ss', term'))
let prerules2rules prerules =
     List.map prerule2rule prerules

let rec terminals_in_term term =
  match term with
    NT(_) -> []
  | T a -> [a]
  | Var _ -> []
  | App(t1,t2) ->
     merge_and_unify compare (terminals_in_term t1)  (terminals_in_term t2) 
  
let terminals_in_rule (f, (vars, term)) =
  terminals_in_term term
let rec terminals_in_rules rules =
 match rules with
   [] -> []
  |r::rules' ->
    merge_and_unify compare (terminals_in_rule r) (terminals_in_rules rules')

(*** sanity check is left for future work ***)
let prerules2gram prerules =
  let rules = prerules2rules prerules in
  let nt = List.map (fun (f,_) -> (f, O)) rules in  
  (* for the moment, ignore the kind *)
  let s = fst (List.hd rules) in
  let terminals = List.map (fun a -> (a, O)) (terminals_in_rules rules) in
    {nt=nt; t=terminals; r=rules; s=s}

let states_in_tr ((q, a), qs) =
  let qs' = delete_duplication (List.sort compare qs) in
    merge_and_unify compare [q] qs'
let rec states_in_transitions transitions =
 match transitions with
   [] -> []
 | tr::transitions' ->
     merge_and_unify compare (states_in_tr tr) (states_in_transitions transitions')
let convert (prerules, transitions) =
  let g = prerules2gram prerules in
  let q0 = fst (fst (List.hd transitions)) in
  let states = states_in_transitions transitions in
  let m = {alpha=g.t; st=states; delta=transitions; init=q0} in
     (g, m)
(** END: conversion from parsing results **)
