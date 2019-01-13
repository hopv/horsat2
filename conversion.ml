(** BEGIN: conversion from parsing results **)
open Grammar;;
open Utilities;;
open Automaton;;

let nttab = ref (Array.make 0 ("", O))
let ntid = ref 0
let new_nt() =
  let x= !ntid in
   (ntid := x+1; x)

let ntauxid = ref 0
let new_ntaux() =
  let x= !ntauxid in
   (ntauxid := x+1; x)

let tab_ntname2id = Hashtbl.create 1000

let register_nt ntname =
  if Hashtbl.mem tab_ntname2id ntname then raise (DuplicatedNonterminal ntname)
  else 
    let nt = new_nt() in 
     (Hashtbl.add tab_ntname2id ntname nt;
      (!nttab).(nt) <- (ntname,O) (* for the moment, ignore the kind *)
      )
let lookup_ntid ntname =
  try Hashtbl.find tab_ntname2id ntname
  with Not_found -> raise (UndefinedNonterminal ntname)

let aux_rules = ref []
let register_new_rule f arity body =
   aux_rules := (f,arity,body)::!aux_rules

let rec depth_of_term term =
  match term with
    T(_) -> 0
  |NT(_) -> 0
  | Var(_) -> 0
  | App(t1,t2) -> max (depth_of_term t1) (depth_of_term t2+1)



let rec pterm2term vmap pterm =
(** distinguish between variables and terminal symbols **)
  match pterm with
    Syntax.PTapp(h, pterms) ->
     let h' = 
       match h with
         Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
       | Syntax.NT(s) -> NT(lookup_ntid s)
       | Syntax.FUN(_,_) -> assert false
       | Syntax.CASE(n) -> assert false
       | Syntax.FD(n) -> assert false
       | Syntax.PAIR -> assert false
       | Syntax.DPAIR -> assert false
     in
     let terms = List.map (pterm2term vmap) pterms in
     let terms' = if !(Flags.normalize) then
                     List.map normalize_term terms
                  else terms
     in
        mk_app h' terms'

and normalize_term term =
  match term with
     App(_,_) ->
        if depth_of_term term > !(Flags.normalization_depth) then
           let vars = vars_in_term term in
           let arity = List.length vars in
           let nt = new_ntaux() in
           let subst = List.combine vars 
                          (List.map (fun i->Var(nt,i)) (fromto 0 arity)) in
           let term' = Grammar.subst_term subst term in
             (register_new_rule nt arity term';
              mk_app (NT(nt)) (List.map (fun i-> Var i) vars))
        else term
  | _ -> term

let dummy_vname = "dummy_var" 

let prerule2rule rules vinfo (f, (_, ss, pterm)) =
  let ss' = indexlist ss in
  let arity = List.length ss in
  let vmap = List.map (fun (i,v) -> (v, (f,i))) ss' in
  let _ = vinfo.(f) <- Array.make arity dummy_vname in
  let _ = List.iter (fun (i,v) -> (vinfo.(f).(i) <- v)) ss' in
  let term = pterm2term vmap pterm in
     rules.(f) <- (arity, term)

let prerules2rules rules vinfo prerules =
  let prerules_indexed = indexlist prerules in
     List.iter (prerule2rule rules vinfo) prerules_indexed



let dummy_term = NT(0)
let dummy_ntname = "DummyNT"

let add_auxiliary_rules nttab rules =
  let num_of_nts = !ntauxid in
  let nttab' = Array.make num_of_nts ("",O) in
  let rules' = Array.make num_of_nts (0,dummy_term) in
   for i=0 to Array.length rules -1 do
      nttab'.(i) <- nttab.(i);
      rules'.(i) <- rules.(i)
   done;
   List.iter (fun (f,arity,body) ->
      rules'.(f) <- (arity, body);
      nttab'.(f) <- ("$NT"^(string_of_int f), O)
      ) 
      !aux_rules;
   (nttab', rules')

let rec elim_fun_from_preterm vl preterm newrules =
  let Syntax.PTapp(h, pterms) = preterm in
  let (pterms',newrules') = elim_fun_from_preterms vl pterms newrules in
  let (Syntax.PTapp(h',pterms''), newrules'') =
         elim_fun_from_head vl h newrules' in
     (Syntax.PTapp(h', pterms''@pterms'), newrules'')
and elim_fun_from_preterms vl preterms newrules =
  match preterms with
    [] -> ([], newrules)
  | pterm::pterms ->
      let (pterms',newrules') = elim_fun_from_preterms vl pterms newrules in
      let (pterm', newrules'') = elim_fun_from_preterm vl pterm newrules' in
         (pterm'::pterms', newrules'')
and elim_fun_from_head vl h newrules =
  match h with
    Syntax.Name(s) -> (Syntax.PTapp(Syntax.Name(s),[]), newrules)
  | Syntax.NT(s) -> (Syntax.PTapp(Syntax.NT(s),[]), newrules)
  | Syntax.FUN(vl1,pterm) ->
       let vl' = vl@vl1 in (* what if names in vl and vl1 clashe? *)
       let (pterm',newrules') = elim_fun_from_preterm vl' pterm newrules in
       let f = Syntax.new_ntname() in
       let pterms1 = List.map (fun v -> Syntax.PTapp(Syntax.Name(v), [])) vl in
         (Syntax.PTapp(Syntax.NT(f), pterms1), (f, vl', pterm')::newrules')
  | Syntax.CASE(n) -> assert false
  | Syntax.FD(n) -> assert false
  | Syntax.PAIR -> assert false
  | Syntax.DPAIR -> assert false


let elim_fun_from_prerule prerule newrules =
  let (f, vl, preterm) = prerule in
  let (preterm', newrules')= elim_fun_from_preterm vl preterm newrules in
    ((f,vl,preterm'), newrules')

let elim_fun_from_prerules prerules =
 let (prerules', newrules) =
  ( List.fold_left
   (fun (prerules',newrules) prerule ->
      let (prerule',newrules')=
          elim_fun_from_prerule prerule newrules
      in (prerule'::prerules', newrules'))
   ([], [])
   prerules)
 in List.rev_append prerules' newrules

let prerules2gram prerules =
  let prerules = elim_fun_from_prerules prerules in
  let ntnames = List.map (fun (x,_,_)->x) prerules in
  let num_of_nts = List.length ntnames in
  let _ = (ntauxid := num_of_nts) in
  let _ = nttab := Array.make num_of_nts (dummy_ntname,O) in
  let _ = List.iter register_nt ntnames in
  let rules = Array.make num_of_nts (0,dummy_term) in
  let vinfo = Array.make  num_of_nts [| |] in
  let _ = prerules2rules rules vinfo prerules in
  let (nt', rules') = 
               if !(Flags.normalize) then
                   add_auxiliary_rules !nttab rules
               else (!nttab, rules)
  in
  let s = 0 in
  let terminals = List.map (fun a -> (a, -1)) (terminals_in_rules rules) in
  let g = {nt= nt'; t=terminals; vinfo = vinfo; r=rules'; s=s} in
    Grammar.gram := g; g

let states_in_tr ((q, a), qs) =
  let qs' = delete_duplication (List.sort compare qs) in
    merge_and_unify compare [q] qs'
let rec states_in_transitions transitions =
 match transitions with
   [] -> []
 | tr::transitions' ->
     merge_and_unify compare (states_in_tr tr) (states_in_transitions transitions')

let get_rank_from_tr ((q,a),qs) =
  (a, List.length qs)
let rec insert_rank (a,k) alpha =
  match alpha with
    [] -> [(a,k)]
  | (a',k')::alpha' ->
       let x = compare a a' in
         if x<0 then (a,k)::alpha
         else if x=0 then if k=k' then alpha else raise (InconsistentArity a)
         else (a',k')::(insert_rank (a,k) alpha')

let rec get_rank_from_transitions trs =
  match trs with
   [] -> []
  | tr::trs' ->
     insert_rank (get_rank_from_tr tr) (get_rank_from_transitions trs')

let rec merge_rank alpha1 alpha2 =
  match (alpha1,alpha2) with
   ([], _) -> alpha2
 | (_, []) -> alpha1
 | ((a1,k1)::alpha1', (a2,k2)::alpha2') ->
    let x = compare a1 a2 in
     if x<0 then (a1,k1)::(merge_rank alpha1' alpha2)
     else if x>0 then (a2,k2)::(merge_rank alpha1 alpha2')
     else (a1, max k1 k2)::(merge_rank alpha1' alpha2')

let convert (prerules, transitions) =
  let g = prerules2gram prerules in
  let q0 = fst (fst (List.hd transitions)) in
  let states = states_in_transitions transitions in
  let alpha1 = get_rank_from_transitions transitions in
  let alpha1' = merge_rank alpha1 g.t in
  let m = {alpha=alpha1'; st=states; delta=transitions; init=q0} in
     (g, m)

open AlternatingAutomaton;;
let convert_ata (prerules, ranks, transitions ) =
(*  let open AlternatingAutomaton in *)
  let g = prerules2gram prerules in
  let m = from_transitions (ranks,transitions) in
  (g, m);;
(** END: conversion from parsing results **)
