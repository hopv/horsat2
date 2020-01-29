open Flags;;
open Utilities;;
open Syntax;;
open Grammar;;
open Automaton;;
open Stype;;
open Typing;;

type tstate = ity * Stype.st
type delta = (tstate * tr) list
and tr = TrNT of nameNT | TrT of nameT
       | TrApp of tstate * tstate list
let emptyTE = []
let cestring = ref ""
let output_cestring s = cestring := (!cestring)^s
let cteref = ref []
let lookup_cte c =
  List.assoc c !cteref

(** convert a transition q->q1...qn(=qs) to a negated type **)
let rec tr2ty_sub q qs =
  match qs with
    [] -> (ItyQ("~"^q), [])
  | q1::qs' ->
    let (top,ty) = tr2ty_sub q qs' in
    let ty'= List.map (fun ity -> ItyFun([],ity)) ty in
     if q1="top" then
      (ItyFun([],top), ty')
     else
      (ItyFun([],top), (ItyFun([ItyQ("~"^q1)],top))::ty')
and tr2ty q qs =
  let (_,ty) = tr2ty_sub q qs in 
    ty

let extend_cte a ty cte =
  try 
    let (ty1, cte') = list_assoc2 a cte in
      (a, merge_and_unify compare ty ty1)::cte'
  with
    Not_found -> (a,ty)::cte

let arity_of a m =
  let l = List.filter (fun ((_,a'),qs)->a=a') m.delta in
   match l with
     [] -> 
     ( try let sty = Stype.lookup_sort (T(a)) in
          arity_of_sty sty 
      with
      Not_found -> 0 (* temporalily set 0 *)
     )
  | ((_,_),qs)::_ -> List.length qs

let rec add_topty n ity =
  if n=0 then ity
  else add_topty (n-1) (ItyFun([],ity))    

let automaton2cte' m =
  let delta = m.delta in
  let cte0 = List.map (fun (a,_) -> (a, [])) m.alpha in
  let cte0' = cte0
(*
             List.fold_left
              (fun cte q -> ("#or", [ItyFun([ItyQ q],ItyFun([],ItyQ q));
                                     ItyFun([],ItyFun([ItyQ q],ItyQ q))])::cte)
              (("#stop",[])::cte0) m.st
*)
  in
  let cte1 = List.fold_left 
     (fun cte -> fun ((q, a), qs) ->
        let ty = tr2ty q qs in
          extend_cte a ty cte) 
     cte0' delta
  in
    cte1

let automaton2cte_pure m =
  let delta = m.delta in
  let cte0 = List.map (fun (a,_) -> (a, [])) m.alpha in
  let cte0' = cte0
(*             List.fold_left
              (fun cte q -> ("#or", [ItyFun([ItyQ q],ItyFun([],ItyQ q));
                                     ItyFun([],ItyFun([ItyQ q],ItyQ q))])::cte)
              (("#stop",[])::cte0) m.st
*)
  in
  let cte1 = List.fold_left
    (fun cte ((q,a),qs) ->
         extend_cte a 
          [(List.fold_right 
          (fun q1 aty ->  if q1="top" then (ItyFun([],aty)) else ItyFun([ItyQ q1], aty))
          qs (ItyQ q))] cte)
    cte0' delta
  in     
    cte1

let automaton2cte_special m =
  let delta' = List.map (fun ((q,a),qs) -> ((("~"^q),a), List.map (fun q1->"~"^q1) qs)) m.delta in
  let m' = {alpha=m.alpha;st=m.st;delta=delta';init=m.init} in
    automaton2cte_pure m'

let automaton2cte m =
  let delta = m.delta in
  let cte0 = List.map (fun (a,_) -> (a, [])) m.alpha in
 if !negate_automaton then
 if !compute_all then automaton2cte_special m else
  let cte1 = List.fold_left 
     (fun cte -> fun ((q, a), qs) ->
        let ty = tr2ty q qs in
          extend_cte a ty cte) 
     cte0 delta
  in
  let qs = m.st in
  let terminals = List.map fst m.alpha in
  let cte2 =
    List.fold_left
     (fun cte a ->
        let qs1 = (* the set of q s.t. delta(q,a) is undefined *)
                  List.filter 
                  (fun q-> not(List.exists (fun ((q',a'),_)->q=q'&&a=a') delta))
                  qs
        in extend_cte a (List.map (fun q->add_topty (arity_of a m) (ItyQ("~"^q))) qs1) cte)
     cte1 terminals
  in cte2
 else automaton2cte_pure m
(**
  let cte1 = List.fold_left
    (fun cte ((q,a),qs) ->
         extend_cte a 
         (merge_and_unify compare
           [List.fold_right 
         (fun q1 aty ->  ItyFun([ItyQ q1], aty)) qs (ItyQ q)]
          [List.fold_right 
          (fun q1 aty ->  ItyFun([], aty)) qs (ItyQ q)]) cte)
    cte0 delta
  in     
    cte1
**)


let delta = Hashtbl.create 10000
let add_delta (st:tstate) tr =
  try
    let trs = Hashtbl.find delta st in
(**
    let trs' = merge_and_unify compare [tr] trs in
      Hashtbl.replace delta st trs'
**)
    if List.mem tr trs then () 
    else Hashtbl.replace delta st (tr::trs)
  with Not_found ->
    Hashtbl.add delta st [tr]

let print_tstate (ity,sty) = 
   print_string "[";
   print_ity ity; print_string "::";
   Stype.print_sty sty;
   print_string "]"

let print_tstates states =
  print_ty(List.map fst states)
let print_tr tr =
  match tr with
    TrNT(nt) -> print_string ("--> "^nt)
  | TrT(t)  -> print_string ("-->"^t)
  | TrApp(state,states) ->
     ( print_string ("--> ");
      print_tstate state;
      print_string " @ ";
      print_tstates states)

let print_delta() =
  Hashtbl.iter 
  (fun st trs ->
     print_string "[";
     print_tstate st;
     print_string "] -->\n ";
     List.iter 
     (fun tr -> print_tr tr;print_string "\n") trs
  )
  delta

let print_te te =
  List.iter
  (fun (a, ty) ->
    print_string ("  "^a^" : ");
    print_ty ty;
    print_string "\n")
  te

let print_tenv tenv = 
  List.iter
  (fun (a, state) ->
    print_string (a^" : ");
    print_tstate state;
    print_string ", ")
  tenv
  

let get_states () =
 List.fold_left
  (fun qs (state,_) ->
    match state with
      (ItyQ q,_) -> merge_and_unify compare [q] qs
    | _ -> qs)
  [] (hash2list delta)

let get_states_nt nt =
  Flow.lookup_stmap nt

let nte_candidates = Hashtbl.create 1000
let nte_valid = Hashtbl.create 1000
let inittetab = Hashtbl.create 100

let rec add_init_te f te =
  try
   let te0 = Hashtbl.find inittetab f in
   let te1 = merge_and_unify compare te0 te in
     Hashtbl.replace inittetab f te1
  with Not_found ->
   Hashtbl.add inittetab f te

let lookup_init_te f =
  try
    Hashtbl.find inittetab f
  with
   Not_found -> []

let global_nt = "#global"

let rec add_delta_funty (ity,sty) =
  match (ity,sty) with
    (ItyQ _,STbase) -> ()
  | (ItyFun(ty1,ity2), STfun(sty1,sty2)) ->
       (add_delta (ity2,sty2) (TrApp((ity,sty), List.map (fun x->(x,sty1)) ty1));
        add_delta_funty (ity2,sty2))
  | _ -> assert false

let rec init_delta_ity a ity =
  let sty = Stype.aty2sty' ity in
  add_delta (ity,sty) (TrT(a));
  add_delta_funty (ity,sty)
    

let rec init_delta_ty a ty =
  match ty with
    [] -> ()
  | ity::ty' ->
     (init_delta_ity a ity;
      init_delta_ty a ty')

let rec init_delta const_typing =
  match const_typing with
    [] -> ()
  | (a,ty)::const_typing' ->
      ( init_delta_ty a ty;
        init_delta const_typing')

let gram = ref empty_grammar

let initialize g cte =
 ( print_string "Constant typing:\n";
  print_te cte;
  gram := g;
  init_delta cte;
  cteref := cte)


let tracetab = Hashtbl.create 1000

let register_backchain te f ity =
 
  let (vars,body) = try List.assoc f (!gram).r with Not_found -> assert false in
  let (vte,rty) = Typing.mk_vte vars ity in
  let eterm = try Typing.find_derivation vte te !cteref body rty 
              with Not_found -> 
                  (print_string ("failed to find a derivation for "^f^":");
                   print_ity ity; assert false)
  in
    Hashtbl.add tracetab (f,ity) (vte,eterm)

let rec sty2topity sty q =
  match sty with
    Stype.STbase -> ItyQ(q)
  | Stype.STfun(_,sty') -> ItyFun([], sty2topity sty' q)
  | _ -> assert false

let type_found = ref false

let add_tehash te f ity =
  try
    let ty = Hashtbl.find te f in
    if List.mem ity ty then ()
    else
(**
    let ty' = merge_and_unify compare [ity] ty in
**)
    let _ = if !ce && !negate_automaton then register_backchain te f ity in
    let ty' = ity::ty in
      (type_found := true; Hashtbl.replace te f ty')
  with Not_found -> assert false

let lookup_nte f =
  Hashtbl.find nte_candidates f

let initialize_nttype dmap g m =
  let _ = List.iter (fun (f,_)->Hashtbl.add nte_candidates f []) g.nt in
  if !negate_automaton then ()
  else
(*  let _ = Grammar.register_recfun dmap g in *)
   Hashtbl.iter
   (fun f1 sc ->
      let f = Grammar.unfoldedname2 f1 in
      let sty = lookup_sort (NT(f)) in
      let qs = Flow.lookup_stmap f in
      let ty = List.fold_left
        (fun ty' q->
          let ity = sty2topity sty q in
             merge_and_unify compare ty' [ity]
        ) [] qs
      in
(*      let te = [(f, ty)] in
        List.iter (fun g -> (add_init_te g te; add_init_te global_nt te)) sc
*)
        List.iter (fun ity-> add_tehash nte_candidates f ity) ty
(*
         add_delta (ity,sty) (TrNT(f));
         add_delta_funty (ity,sty)))
*)
    )
    recfuntab 

let is_trnt tr =
  match tr with
    TrNT _ -> true
  | _ -> false
let get_trnt state =
  try
    let trs = Hashtbl.find delta state in
      List.filter is_trnt trs
  with Not_found -> []

let is_trt tr =
  match tr with
    TrT _ -> true
  | _ -> false
let get_trt state =
  try
    let trs = Hashtbl.find delta state in
      List.filter is_trt trs
  with Not_found -> []

let get_trapp state =
  try
    let trs = Hashtbl.find delta state in
    List.fold_left
     (fun l tr ->
        match tr with
          TrApp(ity1,ty2) ->
             (ity1,ty2)::l
        | _ -> l)
    [] trs

  with Not_found -> []

exception Foo of tstate * tstate;;

let netab = Hashtbl.create 10000;;
let check_ne_hash state1 state2 =
  try
     Hashtbl.find netab (state1,state2)
  with Not_found -> false

let register_ne state1 state2 =
  Hashtbl.add netab (state1,state2) true

let rec check_nonemptiness state1 state2 =
(**  let _ = (count := !count-1;
           if !count=0 then raise (Foo(state1,state2)))
  in
  let _ = if !debugging then 
         (print_string "checking nonemptiness of";
         print_tstate state1;
         print_string " and ";
         print_tstate state2;
         print_string "\n";flush stdout) in
**)
   if check_ne_hash state1 state2 then true
   else
   let b = check_nonemptiness_sub state1 state2 [] in
(**
   let _ = if !debugging then if b then (print_string "true\n";flush stdout)
           else (print_string "false\n";flush stdout) in
**)
    if b then (register_ne state1 state2; true)
    else false

and check_nonemptiness_sub state1 state2 checked =
  let c = compare state1 state2 in
  if c=0 then true
  else 
  let (state1,state2)= 
      if c>0 then (state2,state1) else (state1,state2) 
  in
  if check_ne_hash state1 state2 then true
  else if List.mem (state1,state2) checked then
     false
  else if List.length checked>3 then true (* avoid deep check for efficiency *)
  else
    let checked' = (state1,state2)::checked in
    (* check the existence of a common atomic transition first *)
    let trts1 = get_trt state1 in
    let trts2 = get_trt state2 in
    let trts3 = get_trnt state1 in
    let trts4 = get_trnt state2 in
     if List.exists (fun x -> List.mem x trts2) trts1
       || List.exists (fun x -> List.mem x trts4) trts3
     then true
     else (* check the exisitence of a common app transition *)
      let trapps1 = get_trapp state1 in
      let trapps2 = get_trapp state2 in
       List.exists 
        (fun ((ity1,sty1),states11) ->
            List.exists 
             (fun ((ity2,sty2),states22) ->
                (sty1=sty2 &&
                 check_nonemptiness_sub (ity1,sty1) (ity2,sty2) checked'
                 && 
                 check_nonemptiness_states states11 states22 checked'))
             trapps2
        )
        trapps1
      
and check_nonemptiness_states states1 states2 checked =
  List.for_all
   (fun state1 ->
     List.for_all (fun state2 -> check_nonemptiness_sub state1 state2 checked)
     states2)
   states1

(**** non-emptiness check seems to be too expensive;
 **** so, we will only check emptiness of intersection of two states
let rec check_emptiness states =
  match states with
    [] -> false
  | [_] -> false
  | _ -> check_emptiness_sub states []
and check_emptiness_sub states checked =
  if List.exists (supset_state states) checked then
     true
  else
     let trtlist = List.map (List.map get_tr) states in
     let trt = List.hd trtlist in
     let trtlist' = List.tl trtlist in
     if List.exists (fun x -> List.forall (List.mem x) trtlist') trt
     then false
     else
      let trapplist = List.map (List.map get_trapp) states in
      let trapp = List.hd trapplist in
      let trapplist' = List.tl trapplist' in
        List.exists
        (fun ((ity,sty),states) ->
          let trapplist'' = 
              List.map ...
***)

let union_tenv tenv1 tenv2 =
  let tenv2' = List.filter 
               (fun (x,(aty2,_)) ->
                 List.for_all
                 (fun (y,(aty1,_)) ->
                   not(x=y && Typing.subtype aty1 aty2)) tenv1)
                 tenv2
  in
  let tenv1' = List.filter 
               (fun (x,(aty1,_)) ->
                 List.for_all
                 (fun (y,(aty2,_)) ->
                   not(x=y && Typing.subtype aty2 aty1)) tenv2')
                 tenv1
  in
    merge_and_unify compare tenv1' tenv2'

let union_tenvs tenvs1 tenvs2 =
  merge_and_unify compare tenvs1 tenvs2
(*
  List.rev_append tenvs1 tenvs2
*)


let is_nonempty_tenv tenv1 tenv2 =
(**
  (if !debugging then
     (print_string "checking non-emptiness of intersection between \n";
     print_tenv tenv1;
     print_string "\n and\n";
     print_tenv tenv2; flush stdout));
**)
  List.for_all (fun (x,tstate1) ->
    List.for_all (fun (y,tstate2) ->
      not(x=y) || check_nonemptiness tstate1 tstate2)
    tenv2)
  tenv1

let subtenv tenv1 tenv2 =
  List.for_all (fun (x,(ity1,sty1)) ->
    List.exists (fun (y,(ity2,sty2)) ->
       x=y && sty1=sty2 && Typing.subtype ity2 ity1
    ) tenv2) tenv1

let rec product_tenvs tenvs1 tenvs2 =
  match tenvs2 with
    [] -> []
  | tenv::tenvs2' ->
    let tenvs1' = 
       if !emptiness_check then
          List.filter (is_nonempty_tenv tenv) tenvs1 
       else tenvs1 in
    let tenvs1' = List.map (union_tenv tenv) tenvs1' in
    let tenvs1'' = delete_duplication_unsorted tenvs1' in
    let tenvs3 = product_tenvs tenvs1 tenvs2' in
    let tenvs4 = 
       if !negate_automaton then
                 List.filter 
                 (fun tenv1 -> not(List.exists (fun tenv3-> subtenv tenv3 tenv1) tenvs3))
                 tenvs1''
       else tenvs1''
    in
    let tenvs5 = 
       if !negate_automaton then
                List.filter
                 (fun tenv3 -> not(List.exists (fun tenv4-> subtenv tenv4 tenv3) tenvs4))
                 tenvs3
       else tenvs3
    in
      union_tenvs tenvs4 tenvs5

let rec product_tenvslist tenvslist =
  match tenvslist with
    [] -> []
  | [tenvs] -> tenvs
  | tenvs1::tenvs2::tenvslist' ->
      product_tenvslist
       ((product_tenvs tenvs1 tenvs2)::tenvslist')

let matchtab = Hashtbl.create 10000
let lookup_matchtab term aty =
  Hashtbl.find matchtab (term,aty)

let register_matchtab term aty tenvs =
  Hashtbl.replace matchtab (term,aty) tenvs
(* let reset_matchtab () = Hashtbl.clear matchtab
*)
let reset_saturation () = Hashtbl.clear matchtab; type_found := false

exception Unmatched

let rec mk_ity_new vars env ity =
  match vars with
    [] -> ity
  | v::vars' ->
     let ty = try
                 fst(List.assoc v env)
              with Not_found -> []
     in
        ItyFun(ty,mk_ity_new vars' env ity)


let union_ty ty1 ty2 =
  let ty1' = 
     List.filter
             (fun aty1 -> 
               not(List.exists (fun aty2 -> Typing.subtype aty2 aty1) ty2))
             ty1 
  in
  let ty2' = 
     List.filter
             (fun aty2 -> 
               not(List.exists (fun aty1 -> Typing.subtype aty1 aty2) ty1'))
             ty2
  in
   merge_and_unify compare ty1' ty2'
      
exception Conflict

let rec union_tenv_new tenv1 tenv2 =
  match (tenv1,tenv2) with
    ([], _) -> tenv2
  | (_,[]) -> tenv1
  | ((x1,(ty1,hs1))::tenv1', (x2,(ty2,hs2))::tenv2') ->
     (* we assume that x1<x2 implies (x1,ty1)<(x2,ty2) *)
      let c = compare x1 x2 in
        if c<0 then (x1,(ty1,hs1))::(union_tenv_new tenv1' tenv2)
        else if c>0 then (x2,(ty2,hs2))::(union_tenv_new tenv1 tenv2')
        else
          let hs = List.filter (fun h-> List.mem h hs2) hs1 in
           if hs=[] then raise Conflict
           else
           let ty = union_ty ty1 ty2 in
             (x1,(ty,hs))::(union_tenv_new tenv1' tenv2')

let rec product_tenvs_new tenvs1 tenvs2 =
  match tenvs2 with
    [] -> []
  | tenv::tenvs2' ->
(*
    let tenvs1' = 
        if !emptiness_check then
          List.filter (is_nonempty_tenv tenv) tenvs1 
       else 
       tenvs1 in
*)
    let tenvs1' = List.fold_left
                  (fun tenvs tenv1 ->
                    try
                      (union_tenv_new tenv tenv1)::tenvs
                    with Conflict -> tenvs)
                   []
                   tenvs1 
    in
    let tenvs1'' = delete_duplication_unsorted tenvs1' in
    let tenvs3 = product_tenvs_new tenvs1 tenvs2' in
    let tenvs4 = 
(* I am not sure whether this optimization is correct.
        if !negate_automaton then
                 List.filter 
                 (fun tenv1 -> 
                  not(List.exists (fun tenv3-> subtenv_new tenv3 tenv1) tenvs3))
                 tenvs1''
       else 
*)
       tenvs1''
    in
    let tenvs5 = 
(* I am not sure whether this optimization is correct.
       if !negate_automaton then
                List.filter
                 (fun tenv3 -> 
                  not(List.exists (fun tenv4-> subtenv_new tenv4 tenv3) tenvs4))
                 tenvs3
       else
*)
       tenvs3
    in
      union_tenvs tenvs4 tenvs5

let mk_htenvs x htys =
  let tys = List.map (fun (_,ty)->ty) htys in
  let ty1 = merge_and_unify_list compare tys in
    List.map 
    (fun aty ->
       let htys' = List.filter (fun (h,ty1)-> List.mem aty ty1) htys in
       let heads = List.map fst htys' in
         ([(x, ([aty], heads))], aty)
     )
    ty1

let local_nte = ref []
let lookup_localnte f = try List.assoc f !local_nte with Not_found -> []

let local_headtab = ref []

let rec match_term_aty term aty =
 let envs1 =
   match term with
    App(_,_) ->
      ( try
         lookup_matchtab term aty
       with
       Not_found ->
         let envs1 = match_term_aty_sub term aty in
           (register_matchtab term aty envs1; envs1)
       )
  | _ -> match_term_aty_sub term aty
 in
   if envs1 = [] then raise Unmatched else envs1
and match_term_aty_sub term aty =
    let (h, ts) = Grammar.decompose_term term in
    let arity = List.length ts in
    let env_aty_list = match_head h arity aty in
      List.fold_left
       (fun envs (env, aty1) ->
        try
         union_tenvs envs (product_tenvs_new [env] (match_args ts aty1))
        with Unmatched -> envs
        )
      []
      env_aty_list

and match_args terms aty =
  match terms with
     [] -> [[]]
   | t::terms' ->
      match aty with
        ItyFun(ty1,aty2) ->
          let envs1 = match_term_ty t ty1 in
          let envs2 = match_args terms' aty2 in
            product_tenvs_new envs1 envs2
      | _ -> assert false
and match_term_ty term ty =
  match ty with
   [] -> [emptyTE]
  | aty::ty' ->
     let envs1 = match_term_aty term aty in
     let envs2 = match_term_ty term ty' in
        product_tenvs_new envs1 envs2
and match_head h arity aty =
  match h with
    (T(_)|NT(_)) -> 
      let ty = match_head_ty h arity aty in
       List.map (fun aty1 -> ([], aty1)) ty
  | Var(x) ->            
      let heads = if !Flags.flow then
                      Flow.lookup_headtab x 
                  else
                     try [List.assoc x !local_headtab]
                     with Not_found -> assert false
      in
(*
      let _ = 
       (print_string ("match_head "^x^":"); Reduce.print_heads heads; print_string "\n") in
*)
      let htys = List.map 
                (fun (h,k) -> 
                  let ty = match_head_ty' h (arity+k) aty in
                   (h,
                    delete_duplication_unsorted 
                    (List.map 
                     (fun aty1 -> 
                      let aty2 = Typing.get_rty k aty1 in
                     aty2
                     ) ty))
                )
                heads
      in
        mk_htenvs x htys 
  | _ -> assert false
and match_head_ty h arity aty =
  match h with
     T(a) ->
      let ty = lookup_cte a in
       List.filter 
         (fun aty1 -> aty=Typing.get_rty arity aty1)
         ty
   | NT(f) ->      
(*
      if String.sub f 0 1="$" then
        match_head_ty (T(String.sub f 1 (String.length f - 1))) arity aty
      else
*)
      let ty1 = lookup_nte f in
      let ty2 = lookup_localnte f in
      let ty = ty2@ty1 in
      let ty3 = List.filter 
         (fun aty1 -> aty=Typing.get_rty arity aty1)
         ty
      in ty3 (* delete_duplication_unsorted ty3 *)
   | _ -> assert false

and match_head_ty' h arity aty =
  match h with
     T(a) ->
      let ty = lookup_cte a in
       List.filter 
         (fun aty1 -> aty=Typing.get_rty arity aty1)
         ty
   | NT(f) ->      
      let ty1 = lookup_nte f in
      let ty2 = try List.assoc f (lookup_init_te global_nt) with Not_found -> [] in
      let ty = ty2@ty1 in
      let ty3 = List.filter 
         (fun aty1 -> aty=Typing.get_rty arity aty1)
         ty
      in ty3 (* delete_duplication_unsorted ty3 *)
   | _ -> assert false

let match_term_new term aty =
  try match_term_aty term aty
  with Unmatched ->
    []

let bpropagate_st rule q =
 try
  let (nt,(vars,term)) = rule in
  let _ = debug ("[back-propagation for the rule of "^nt^"\n") in
(**
  let _ = if !debugging then
          (print_string "Current types:\n";
           print_te (hash2list nte_candidates)) in
**)
(*  let envs = match_term term ((ItyQ(q)),STbase) in *)
(*
  let _ = (print_string "matching "; print_term term; print_string (":"^q^"\n"))
  in
*)
  let envs = match_term_new term (ItyQ(q)) in
  let _ = debug ("envs computed\n") in
  let _ = debug ("# of envs: "^(string_of_int(List.length envs))^"\n") in
  let _ =
   List.iter (fun env ->
    let ity = mk_ity_new vars env (ItyQ(q)) in
(*    let sty = Stype.lookup_sort (NT(nt)) in *)
(*    add_delta (ity, sty) (TrNT(nt)); *)
    add_tehash nte_candidates nt ity;
(*    add_delta_funty (ity,sty); *)
    debug ("*")
    ) envs
  in 
   debug ("back-propagation done\n")
 with Unmatched -> ()

let bpropagate dmap dmap2 rule =
  let (nt,_)=rule in
  let _ = (local_nte := lookup_init_te nt) in
  let qs = get_states_nt nt in
  let _ = type_found := false in
  let _ = List.iter (bpropagate_st rule) qs in
    if !type_found then
     (let nts1 = List.assoc nt dmap in
      let nts2 = List.assoc nt dmap2 in
        merge_and_unify compare nts1 nts2)
    else []

let merge_todo todo1 todo2 =
   todo2@(List.filter (fun f-> not(List.mem f todo2)) todo1) 

let report_yes() =
  (print_string "The property is satisfied.\n";
   if !Flags.outputfile="" then ()
                  else let fp = open_out !Flags.outputfile in
                     (output_string fp ("SATISFIED\n") ; close_out fp))

let report_no() =
  if !Flags.flow then
   (print_string "The property is NOT satisfied.\n";
    if !Flags.outputfile="" then ()
                  else let fp = open_out !Flags.outputfile in
                     (output_string fp ("VIOLATED\n") ; close_out fp))
  else (print_string "Given up\n")

(* repeat saturations; the variable "todo" keeps the non-terminals for which
   types should be recomputed *)
let rec saturate_sub todo rules dmap dmap2 s q0 =
  match todo with
    [] -> ()
  | f::todo' ->
(*      let _ = (print_string ("checking "^f); report_time()) in *)
      let d = List.assoc f rules in
      let todo1 = bpropagate dmap dmap2  (f,d) in
       if not(!Flags.compute_all) && f=s && List.mem (ItyQ("~"^q0)) (lookup_nte s) then ()
       else
         let todo_new = merge_todo todo1 todo' in
         let _ = reset_saturation() in      
           saturate_sub todo_new rules dmap dmap2 s q0

let saturate g dmap dmap2 q0 =
 let rules = g.r in
 let todo = List.map (fun (f,_)->f) rules in
  saturate_sub todo rules dmap dmap2 g.s q0

let period = ref 10

let copy_nte_candidates nte_candidates =
  let nte = Hashtbl.create 1000 in
  let _ =  Hashtbl.iter 
   (fun f ty1 ->
      let header1 = String.sub f 0 1 in
      if not(header1="#") && not(Hashtbl.mem nte f) then
        let ty =
(* The following code (that is commented out) collects type information for
 * symbols prefixed by "#". Although in principle it may provide useful type information,
 * according to experiments, it does not seem so useful in practice. Therefore,
 * it is disabled for the moment. 
           try
             let ty2 = Hashtbl.find nte_candidates ("#"^f) in
               ty1@(List.filter (fun aty->not(List.mem aty ty1)) ty2)
           with Not_found -> 
*)
           ty1
        in Hashtbl.add nte f ty
      else ()
(**
    if String.sub f 1 1="#" then ()
      else if not(Hashtbl.mem nte f) then
        let ty =
           try
             let f0 = (String.sub f 1 (String.length f - 1)) in
             let ty2 = Hashtbl.find nte_candidates f0 in
               ty1@(List.filter (fun aty->not(List.mem aty ty1)) ty2)
           with Not_found -> ty1
        in Hashtbl.add nte f ty
**)
   ) nte_candidates
  in nte

let rec gfp_saturate_sub todo g cte dmap dmap2 q0 count dmap0 g0 =
  match todo with
    [] ->  
     if check_gfp g0 cte dmap0 q0 then ()
     else report_no()
  | f::todo' ->
(*      let _ = (print_string ("checking "^f^":"); report_time()) in *)
      let d = List.assoc f g.r in
      let todo1 = bpropagate dmap dmap2 (f,d) in
      let todo_new = merge_todo todo1 todo' in
      let count' = if !type_found then
                    (reset_saturation();
                     count-1) else count in
(*      let _ = (print_string ("checking "^f^" done:"); report_time()) in *)
      if count' = 0 then 
        if check_gfp g0 cte dmap0 q0 then ()
        else
          (gfp_saturate_sub todo_new g cte dmap dmap2 q0 !period dmap0 g0 )
      else 
         (gfp_saturate_sub todo_new g cte dmap dmap2 q0 count' dmap0 g0)
and check_gfp g cte dmap q0 =
(*    let _ = (print_string "computing gfp:"; report_time()) in  *)
    let nte_candidates' = copy_nte_candidates nte_candidates in
(*    let _ = (print_string "computing gfp 1:"; report_time()) in  *)
    let _ = Typing.filter_valid_types nte_candidates' nte_valid in
(*    let _ = (print_string "computing gfp 2:"; report_time()) in  *)
    let nte1 = 
       hash2list(Typing.compute_te nte_candidates' cte nte_valid dmap g) in
(*    let _ = (print_string "computing gfp 3:"; report_time()) in  *)
    let _ = Typing.add_te nte_valid nte1 in
(*    let _ = (print_string "computing gfp done:"; report_time()) in  *)
        if List.mem (ItyQ(q0)) (Hashtbl.find nte_valid g.s) then
         let _ = print_string "Inferred Types:\n" in
         let _ = Typing.print_te (hash2list nte_valid) in
          (report_yes(); true)
        else false
        
let gfp_saturate g cte dmap dmap2 q0 dmap0 g0 =
  let _ = List.iter (fun (f,_)->Hashtbl.add nte_valid f []) g0.nt in
  let todo = List.map (fun (f,_)->f) g.r in
(*  let _ = (period := 1+(List.length todo)/2) in *)
    gfp_saturate_sub todo g cte dmap dmap2 q0 !period dmap0 g0

let bpropagate2 dmap rule heads =
  let (nt,(vars,_))=rule in
  let _ = (local_nte := lookup_init_te nt) in
  let _ = (local_headtab := List.combine vars heads) in
  let qs = get_states_nt nt in
  let _ = type_found := false in
  let _ = List.iter (bpropagate_st rule) qs in
    if !type_found then
     (let nts1 = List.assoc nt dmap in
      let todo1 = Reduce.get_nts_heads nts1 in
      let todo2 = Reduce.lookup_inv_headtab nt in
        merge_and_unify compare todo1 todo2)
    else []

let rec gfp_saturate2_sub todo g cte dmap q0 count =
  match todo with
    [] ->  
     if check_gfp g cte dmap q0 then ()
     else report_no()
  | (f,heads)::todo' ->
      let _ = (print_string ("checking "^f^" "); 
               Reduce.print_heads heads; print_string ": ";
               report_time()) in
      let d = List.assoc f g.r in
      let todo1 = bpropagate2 dmap (f,d) heads in
      let todo_new = merge_todo todo1 todo' in
      let count' = if !type_found then
                    count-1 else (print_string "type not found\n";count) in
      let _ = (print_string ("checking "^f^" done:"); report_time()) in
      let _ = reset_saturation() in
      if count' = 0 then 
        if check_gfp g cte dmap q0 then ()
        else
          (gfp_saturate2_sub todo_new g cte dmap q0 !period)
      else 
         (gfp_saturate2_sub todo_new g cte dmap q0 count')

let gfp_saturate2 g cte dmap q0 =
  let _ = List.iter (fun (f,_)->Hashtbl.add nte_valid f []) g.nt in
  let todo = Reduce.get_allheads() in
(*  let _ = (period := 1+(List.length todo)/2) in *)
    gfp_saturate2_sub todo g cte dmap q0 !period


let vid = ref 0;;
let new_vname v = let x = !vid in (vid := !vid+1; v^"#"^(string_of_int x))
let rec rename_vte vte =
  match vte with
    [] -> ([], [])
  | (v,ty)::vte' ->
      let (vte'',vmap) = rename_vte vte' in
      let v' = new_vname v in
        ((v',ty)::vte''), ((v,v')::vmap)
  
let rec rename_eterm eterm vmap =
  match eterm with
    ENT _ -> eterm
  | ET _ -> eterm
  | EVar(v,ity) -> (try EVar(List.assoc v vmap, ity) with Not_found -> eterm)
  | EApp(t1,t2) -> EApp(rename_eterm t1 vmap, List.map (fun t->rename_eterm t vmap) t2)
  | ECoerce(ity1,ity2,t) ->
       ECoerce(ity1,ity2,rename_eterm t vmap)

let rename_vte_eterm vte eterm =
  let (vte',vmap) = rename_vte vte in
     (vte', rename_eterm eterm vmap)

let rec mk_env vte termss =
  match (vte, termss) with
    ([], []) -> []
  | ((v,ty)::vte', ts::termss') ->
       let x = List.combine ty ts in
        (List.map (fun (ity,t)->((v,ity),t)) x)@(mk_env vte' termss')
  | _ -> assert false
let rec non_topaty aty =
  match aty with
    ItyQ(_) -> 1
  | ItyFun(ty,aty') ->
     if ty=[] then 1+(non_topaty(aty'))
     else 1
let rec evaluate_eterm eterm env =
  let (h,termss) = decompose_eterm eterm in
  match h with
    ENT(f,ity) -> 
      let (vte,body) = Hashtbl.find tracetab (f,ity) in
      let (vte',body') = rename_vte_eterm vte body in
      let env' = mk_env vte' termss in
         evaluate_eterm body' (env'@env)
 | ET(a,aty) -> 
    ( let k = non_topaty(aty) in
       if k=0 || k>List.length termss then 
             output_cestring ("("^a^ ",0)") 
       else
        let _ = output_cestring ("("^a^","^(string_of_int k)^")") in
        let ts = List.nth termss (k-1) in
        try    evaluate_eterm (List.hd ts) env
        with Failure("hd") -> (print_eterm eterm; assert false))
 | EVar(v,aty) ->
      let eterm1 = List.assoc (v,aty) env in
        evaluate_eterm (compose_eterm eterm1 termss) env
 | ECoerce(aty1,aty2,t) ->
      (match (aty1,aty2) with
         (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
       | (ItyFun(ty11,aty11), ItyFun(ty21,aty21)) ->
           (match termss with
             [] -> assert false
           | ts::termss' ->
               let tyterms = List.combine ty21 ts in
               let ts' = List.map (fun aty ->
                   let (aty',t') = List.find (fun (aty',_)->Typing.subtype aty' aty) tyterms in
                     if aty=aty' then t' else ECoerce(aty',aty,t')) ty11
               in 
               let t1 = if aty11=aty21 then EApp(t,ts') else
                        ECoerce(aty11,aty21,EApp(t,ts'))
               in evaluate_eterm (compose_eterm t1 termss') env)
       | _ -> assert false )
  | _ -> assert false

let rec print_tracetab typings finished =
  match typings with
    [] -> ()
  | (f,ity)::typings' ->
     if List.mem (f,ity) finished then print_tracetab typings' finished
     else
     let (vte,eterm) = Hashtbl.find tracetab (f,ity) in
     let (vars,_) = List.assoc f (!gram).r in
     let (vte,_) = Typing.mk_vte vars ity in
     let _ = Typing.print_erule f ity vte eterm in
     let typings2 = Typing.typings_in_eterm eterm in
        print_tracetab (merge_and_unify compare typings' typings2) ((f,ity)::finished)

let size_of_nte() =
  Hashtbl.fold (fun nt ty k -> k+List.length ty) nte_candidates 0

let fp = ref stdout

let report_ce nt_s aty =
  (print_string "The property is NOT satisfied.\n";
   print_string ("The size of typing:"^(string_of_int (size_of_nte()))^"\n");
   if !Flags.outputfile="" then ()
   else (fp := open_out !Flags.outputfile ;
   output_string !fp ("VIOLATED\n"));
   (if !Flags.ce then
      (cestring := "";
       register_backchain nte_candidates nt_s aty;
       print_tracetab [(nt_s,aty)] [];
       print_string "An error trace is:\n";
      evaluate_eterm (ENT(nt_s,aty)) [];
      output_cestring "\n";
      print_string (!cestring);
     if not(!Flags.outputfile="") then output_string !fp !cestring)
   else ());
   if not(!Flags.outputfile="") then close_out !fp)


let report nt_s q0 =
  let _ = print_string "saturated typing\n" in
  let _ = Typing.print_te (hash2list nte_candidates) in
  try
    let _ = match_term_aty (NT(nt_s)) (ItyQ("~"^q0)) in
           report_ce nt_s (ItyQ("~"^q0))
  with Unmatched ->      
       report_yes()

let var_dependency v =
  let heads = Flow.lookup_headtab v in
   List.fold_left
   (fun nts (h,_) ->
     match h with NT(f) -> merge_and_unify compare [f] nts
                | _ -> nts)
    [] heads 

let vars_dependency vars =
  List.fold_left 
  (fun nts v ->
    merge_and_unify compare nts (var_dependency v))
  [] vars

let var_dmap g =
 let dmap_inv =
    List.map
    (fun (f,(vars,_)) ->
       (f, vars_dependency vars))
    g.r
 in
  List.map (fun (f,_) -> 
    (f, List.map fst(List.filter (fun (g,nts) -> List.mem f nts) dmap_inv)))
  g.r



