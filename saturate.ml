open Flags;;
open Utilities;;
open Syntax;;
open Grammar;;
open Automaton;;
open Stype;;
open Type;;

type tstate = ity * Stype.st
type delta = (tstate * tr) list
and tr = TrNT of nameNT | TrT of nameT
       | TrApp of tstate * tstate list

let flag_updated_nt = ref false
let flag_updated_termid = ref false
let flag_overwritten = ref false


let merge_ty ty1 ty2 =
  merge_and_unify compare_ity ty1 ty2

let add_ity ity ty =
  if List.exists (fun ity1 -> subtype ity1 ity) ty
  then ty
  else
  merge_ty [ity] (List.filter (fun ity1 -> not(subtype ity ity1)) ty)

let compare_tys tys1 tys2 =
  compare (List.map (List.map id_of_ity) tys1) (List.map (List.map id_of_ity) tys2)

let merge_tyss tyss1 tyss2 =
  merge_and_unify compare_tys tyss1 tyss2
  
let rec eq_ty ty1 ty2 =
  match (ty1,ty2) with
   ([],[]) -> true
 | (ity1::ty1',ity2::ty2') ->
    (id_of_ity ity1 = id_of_ity ity2)
        && eq_ty ty1' ty2'
 | _ -> false
let rec eq_tys tys1 tys2 =
  match (tys1,tys2) with
   ([],[]) -> true
 | (ty1::tys1',ty2::tys2') ->
     eq_ty ty1 ty2 && eq_tys tys1' tys2'
 | _ -> false
let add_tyss tys tyss =
  if List.exists (fun tys1 -> eq_tys tys tys1) tyss then
    tyss
  else tys::tyss

let rec eq_tyarray_mask j mask tys1 tys2 =
  List.for_all (fun i ->eq_ty tys1.(i-j) tys2.(i-j)) mask


let emptyTE = []

let nteref = ref [||]


let rec register_linearity ity a i =
  match ity with
   ItyQ _ -> ()
| ItyFun(_,ty,ity1) ->
     (if List.length ty>1 then a.(i) <- false (* non-linear *));
     register_linearity ity1 a (i+1)

let mk_linearity_tab() =
  Hashtbl.iter (fun c tyarray ->
    let arity = Grammar.arity_of_t c in
    let a = Array.make arity true in
    Array.iter (fun ty ->
      List.iter (fun ity ->
      register_linearity ity a 0) ty) tyarray;
    Hashtbl.add Ai.tab_linearity c a
  )
  cte

(** convert a transition q->q1...qn(=qs) to a negated type **)
let rec tr2ty_sub q qs =
  match qs with
    [] -> (ItyQ(Ai.state2id q), [])
  | q1::qs' ->
    let (top,ty) = tr2ty_sub q qs' in
    let ty'= List.map (fun ity -> mkItyFun([],ity)) ty in
     if q1="top" then
      (mkItyFun([],top), ty')
     else
      (mkItyFun([],top), (mkItyFun([ItyQ(Ai.state2id q1)],top))::ty')
and tr2ty q qs =
  let (_,ty) = tr2ty_sub q qs in 
    ty

let arity_of a m =
  List.assoc a m.alpha

let rec add_topty n ity =
  if n=0 then ity
  else add_topty (n-1) (mkItyFun([],ity))    

let build_ity q n vs =
  let rec go = function
    | 0 -> ItyQ (Ai.state2id q)
    | k -> 
        let vs = List.filter (fun (i,_) -> n - k + 1 = i) vs in
        let vs = List.map (fun (_,q) -> ItyQ (Ai.state2id q)) vs in
        let t1 = go (k-1) in
        mkItyFun (List.sort compare_ity vs,t1) in
  go n;;

let init_cte terminals st =
  let n = List.length st in
  List.iter (fun (a,_) -> 
    Hashtbl.add cte a (Array.make n [])) terminals


let register_cte_ity a ity =
 let tyarray = lookup_cte a in
 let x = codom_of_ity ity in
 let ty = tyarray.(x) in
   tyarray.(x) <- merge_and_unify compare [ity] ty

let register_cte_ty (a, ty) =
  List.iter (register_cte_ity a) ty

let ata2cte m =
(*  let open AlternatingAutomaton in *)
  init_cte m.AlternatingAutomaton.alpha m.AlternatingAutomaton.st;
  List.iter (fun (a,i) ->
    let l = List.concat (List.map (fun q ->
      let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
      let pis = AlternatingAutomaton.prime_implicants fml in
      List.map (build_ity q i) pis) m.AlternatingAutomaton.st) in
    register_cte_ty (a,l)) m.AlternatingAutomaton.alpha

let automaton2cte m =
  let delta = m.delta in
  init_cte m.alpha m.st;
  let _ = List.iter
     (fun ((q, a), qs) ->
        let ty = tr2ty q qs in
          register_cte_ty (a, ty))
     delta
  in
  let qs = m.st in
  let terminals = List.map fst m.alpha in
    List.iter
     (fun a ->
        let qs1 = (* the set of q s.t. delta(q,a) is undefined *)
                  List.filter 
                  (fun q-> not(List.exists (fun ((q',a'),_)->q=q'&&a=a') delta))
                  qs
        in register_cte_ty (a, List.map (fun q->add_topty (arity_of a m) (ItyQ(Ai.state2id q))) qs1))
     terminals

let rec print_ity ity =
  match ity with
   ItyQ x -> print_string ("~"^(Ai.id2state x))
 | ItyFun(_,ty,ity) ->
     print_string "(";
     print_ty ty;
     print_string "->";
     print_ity ity;
     print_string ")"
and print_ty ty =
  match ty with
    [] -> print_string "top"
  | [ity] -> print_ity ity
  | ity::ty' ->
      print_ity ity;
      print_string "^";
      print_ty ty'

let print_tys tys =
   Array.iter (fun ty-> print_ty ty; print_string " * ") tys

let print_itylist ty =
  List.iter (fun ity ->
      print_ity ity; print_string "\n") ty

let print_nte() =
  print_string "types for nt:\n===========\n";
  for nt=0 to (Array.length (!nteref))-1 do
    print_string ((Grammar.name_of_nt nt)^":\n");
    for q=0 to (Array.length (!nteref).(nt))-1 do
      print_itylist (!nteref).(nt).(q)
    done
  done


let print_cte() =
  print_string "Constant types:\n=============\n";
  Hashtbl.iter
  (fun a tyarray ->
    print_string (a^":\n");
    Array.iter (fun ty -> List.iter (fun ity->print_ity ity;print_string "\n") ty) tyarray)
  cte

(* terms_id -> list of types of terms *)
type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil
type tyseqref = tyseq ref
let terms_te: (tyseqref array ref) = ref (Array.make 0 (ref TySeqNil))
let terms_tyss = ref (Array.make 0 (None))
let rec tys2tyseq_singleton tys =
  match tys with
   [] -> TySeqNil
 | ty::tys' ->
     TySeq([(ty, ref (tys2tyseq_singleton tys'))])

let rec tyseq_mem tys tyseqref =
  match tys with
    [] -> true
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
            try
              let tyseqref1 = Utilities.assoc_eq eq_ty ty tyseqlist in
                 tyseq_mem tys' tyseqref1
            with Not_found -> false
      )

let rec tyseq_subsumed tys tyseqref =
  match tys with
    [] -> true
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
              List.exists (fun (ty1,tyseqref1) ->
                 subtype_ty ty1 ty
                && tyseq_subsumed tys' tyseqref1
              ) tyseqlist
      )

let rec tyseq_add_wo_subtyping tys tyseqref =
  match tys with
    [] -> 
      (match !tyseqref with
          TySeqNil -> false
        | _ -> assert false)
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
            try
              let tyseqref1 = Utilities.assoc_eq eq_ty ty tyseqlist in
                    tyseq_add_wo_subtyping tys' tyseqref1 
            with Not_found -> 
              (tyseqref := TySeq((ty, ref (tys2tyseq_singleton tys'))::tyseqlist); true)
      )

exception TySeqEmptied

let rec tyseq_rem_subtyping_aux tys tyseqref =
  match tys with
    [] -> raise TySeqEmptied
  | ty::tys' ->
      (match !tyseqref with
          TySeqNil -> assert false
        | TySeq(tyseqlist) ->
            let (tyseqlist_subsumed,tyseqlist_not_subsumed) = 
              List.partition (fun (ty1,_) ->  subtype_ty ty ty1) tyseqlist
            in
            let removed = ref false in
            let updated = ref false in
            let tyseqlist1 =
               List.fold_left 
               (fun tyseqlist1' (ty1,tyseqref1) ->
                  try
                    updated := tyseq_rem_subtyping_aux tys' tyseqref1;
                    (ty1,tyseqref1)::tyseqlist1'
                  with TySeqEmptied ->
                    (removed := true; tyseqlist1')
                )
                [] tyseqlist_subsumed
            in if !removed
               then if tyseqlist1=[] && tyseqlist_not_subsumed=[] then raise TySeqEmptied
                    else (tyseqref := TySeq(List.rev_append tyseqlist1 tyseqlist_not_subsumed); true)
               else !updated
         )
let tyseq_rem_subtyping tys tyseqref =
  try tyseq_rem_subtyping_aux tys tyseqref
  with TySeqEmptied -> (tyseqref := TySeq []; true)

let rec tyseq_add_with_subtyping tys tyseqref =
(*  print_string "adding:"; print_tys tys;print_string "\n";*)
  let overwritten = tyseq_rem_subtyping tys tyseqref in
  let _ = tyseq_add_wo_subtyping tys tyseqref in
    overwritten

let merged_vte_updated = ref false

let rec tyseq_merge_tys tys tyseqref =
  match tys with
    [] -> 
      (match !tyseqref with
          TySeqNil -> ()
        | _ -> assert false)
  | ty::tys' ->
      (match !tyseqref with
         TySeqNil -> assert false (* size of the type sequence does not match *)
       | TySeq(tyseqlist) ->
            match tyseqlist with
              [] -> 
                  merged_vte_updated := true;
                  tyseqref := TySeq((ty, ref (tys2tyseq_singleton tys'))::tyseqlist)
            | (ty1,tyseqref')::tyseqlist' ->
                assert(tyseqlist'=[]);
                tyseq_merge_tys tys' tyseqref';
                let ty2 = merge_and_unify compare_ity ty ty1 in
                if List.length ty1=List.length ty2 then ()
                else (merged_vte_updated:= true;
                      tyseqref := TySeq([(ty2, tyseqref')]))
      )

(*
let rec tyseq2tyss tyseq len =
  match tyseq with
    TySeqNil -> [[]]
  | TySeq(tyseqlist) ->
      List.fold_left
       (fun tyss (ty,tyseqref) ->
          let tyss1 = tyseq2tyss (!tyseqref) in
           List.fold_left (fun tyss2 tys1 ->
              (ty::tys1)::tyss2) tyss tyss1)
       [] tyseqlist
*)
let rec tyseq2tyss tyseq len =
  match tyseq with
    TySeqNil -> [Array.make len []]
  | TySeq(tyseqlist) ->
      List.fold_left
       (fun tyss (ty,tyseqref) ->
          let tyss1 = tyseq2tyss (!tyseqref) (len+1) in
	  let _ = List.iter (fun tys -> tys.(len) <- ty) tyss1 in
           List.rev_append tyss1 tyss)
       [] tyseqlist

let lookup_terms_te id =
  match (!terms_tyss).(id) with
    Some(tyss) -> tyss
  | None ->
      let tyss = tyseq2tyss(!((!terms_te).(id))) 0 in
              (!terms_tyss).(id) <- Some(tyss); tyss


let print_terms_te() =
  print_string "Types_of_terms:\n=========\n";
  for id=0 to (Array.length !terms_te)-1 do
   if (!Ai.termid_isarg).(id) then
    let terms = Ai.id2terms id in
    List.iter (fun t-> print_term t; print_string ", ") terms;
    print_string "\n";
    let tyss = lookup_terms_te id in
    List.iter (fun tys -> print_tys tys;
      print_string "\n") tyss
  else ()
 done


let rec subtype_tys tys1 tys2 =
  match (tys1,tys2) with
   ([], []) -> true
 | (ty1::tys1', ty2::tys2') ->
      subtype_ty ty1 ty2
     && subtype_tys tys1' tys2'
 | _ -> assert false

let worklist_var_ty = ref ([], Array.make 1 [])
let worklist_var_ty_wo_overwrite = ref ([], Array.make 1 [])
let updated_nt_ty = ref ([], Array.make 1 [])
let init_worklist_var_ty maxid =
  worklist_var_ty := ([], Array.make maxid []);
  worklist_var_ty_wo_overwrite := ([], Array.make maxid [])
let worklist_var = ref (Setqueue.make 1)
let worklist_var_overwritten = ref (Setqueue.make 1)
let worklist_nt = ref (Setqueue.make 1)
let updated_nts = ref (Setqueue.make 1)

let enqueue_var_ty termid tys =
  let _ = (!terms_tyss).(termid) <- None in (* invalidate the previous type table for id *)
  let (ids, a) = !worklist_var_ty in
  let x = a.(termid) in
    a.(termid) <- tys::x;
    if x=[] then worklist_var_ty := (termid::ids, a)
    else ()

let enqueue_var_ty_wo_overwrite termid tys =
  let _ = (!terms_tyss).(termid) <- None in (* invalidate the previous type table for id *)
  let (ids, a) = !worklist_var_ty_wo_overwrite in
  let x = a.(termid) in
    a.(termid) <- tys::x;
    if x=[] then worklist_var_ty_wo_overwrite := (termid::ids, a)
    else ()

let enqueue_nt_ty f ity =
  let (nts,a) = !updated_nt_ty in
  let x = a.(f) in
    a.(f) <- ity::x;
    if x=[] then updated_nt_ty := (f::nts, a)
    else ()


exception WorklistVarTyEmpty

let rec dequeue_var_ty_gen worklist =
  let (ids, a) = !worklist in
   match ids with
     [] -> raise WorklistVarTyEmpty 
   | id::ids' ->
       match a.(id) with
          [] -> (worklist := (ids',a);
	         dequeue_var_ty_gen worklist)
	| tys::tyss ->
	    a.(id) <- tyss;
	    (if tyss=[] then worklist := (ids',a));
	    (id, tys)

let rec dequeue_var_ty() =
  dequeue_var_ty_gen worklist_var_ty

let rec dequeue_var_ty_wo_overwrite() =
  dequeue_var_ty_gen worklist_var_ty_wo_overwrite

let dequeue_nt_ty() = 
  let (nts, a) = !updated_nt_ty in
   match nts with
     [] -> raise WorklistVarTyEmpty
   | f::nts' ->
       let ty = a.(f) in
         (updated_nt_ty := (nts',a); a.(f) <- []; (f,ty))

let register_terms_te id ty overwrite_flag =
(*  assert (not(ty=[]));*)
 if !Flags.merge_vte then
   let tyseqref = (!terms_te).(id) in
   (merged_vte_updated := false;
     tyseq_merge_tys ty tyseqref;
     if !merged_vte_updated then
       (Utilities.debug ("type of id "^(string_of_int id)^" has been updated\n");
       let tys = List.hd (tyseq2tyss !tyseqref 0) in
       enqueue_var_ty id tys)
     else ())
 else
  let tyseqref = (!terms_te).(id) in
  if overwrite_flag && !Flags.overwrite then
    if tyseq_mem ty tyseqref then ()
    else if tyseq_subsumed ty tyseqref
    then (flag_overwritten := true;
          Setqueue.enqueue !worklist_var_overwritten id)
    else 
     (let overwritten = tyseq_add_with_subtyping ty tyseqref in
         flag_updated_termid := true;
(*         let _ = Utilities.debug ("updated type of id "^(string_of_int id)^"\n") in*)
         let ty' = Array.of_list ty in
         enqueue_var_ty id ty';
         if overwritten then 
           (flag_overwritten := true ; Setqueue.enqueue !worklist_var_overwritten id)
         else ()
       )
  else
  let changed = tyseq_add_wo_subtyping ty tyseqref in
  if changed then 
    (let ty' = Array.of_list ty in
     enqueue_var_ty_wo_overwrite id ty';
     flag_updated_termid := true)
  else ()

let rec mk_prod_venvs (i,j,tys) venvs acc =
  match tys with 
    [] -> acc
  | ty::tys' ->
      let acc' =
        List.fold_left
        (fun venvs1 venv1 ->
           ((i,j,ty)::venv1)::venvs1 ) acc venvs
      in mk_prod_venvs (i,j,tys') venvs acc'

(* env is a list of elements of the form (i,j,id), 
   which means that variables i to j are bound to ti to tj,
   where id is the identifier of [ti;...;tj] *)
let rec mk_venvs env =
  match env with
    [] -> [[]]
  | [(i,j,id)] -> let tys = lookup_terms_te(id) in 
       List.map (fun ty -> [(i,j,ty)]) tys
  | (i,j,id)::env' ->
     let tys = lookup_terms_te(id) in
     if tys=[] then []
     else 
      let venvs = mk_venvs env' in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
       mk_prod_venvs (i,j,tys) venvs []

let rec mk_venvs_incremental env (id,tys) = 
  match env with
    [] -> [[]]
  | (i,j,id1)::env' ->
     if id1=id then
      let venvs = mk_venvs env' in
        List.map (fun venv-> (i,j,tys)::venv) venvs
     else
       let tyss = lookup_terms_te(id1) in
       if tyss=[] then []
       else 
        let venvs = mk_venvs_incremental env' (id,tys) in
        if venvs=[] then []
        else
        (* this may blow up the number of type environments *)
         mk_prod_venvs (i,j,tyss) venvs []


let rec mask_ty i mask tys =
  List.iter (fun j ->
     tys.(j-i) <- []) mask
(*
  match (mask,tys) with
    ([],_) -> tys
  | (j::mask',ty::tys') ->
      if i=j then ty::(mask_ty (i+1) mask' tys')
      else []::(mask_ty (i+1) mask tys')
  | _ -> assert false
*)

let rec mask_tys i mask tys r =
   match tys with
     [] -> r
   | ty::tys' ->
       if List.exists (eq_tyarray_mask i mask ty) r then
           mask_tys i mask tys' r
       else
           mask_tys i mask tys' (ty::r)

let rec mk_venvs_mask env =
  match env with
    [] -> [[]]
  | [(i,j,mask,id)] -> 
       let tys = lookup_terms_te(id) in 
       let tys' = if List.length mask=j+1-i then tys
                  else mask_tys i mask tys []
       in  List.map (fun ty -> [(i,j,ty)]) tys'
  | (i,j,mask,id)::env' ->
     let tys = lookup_terms_te(id) in
     if tys=[] then []
     else 
      let venvs = mk_venvs_mask env' in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
       let tys' = if List.length mask=j+1-i then tys
                  else mask_tys i mask tys []
       in  mk_prod_venvs (i,j,tys') venvs []


let rec mk_venvs_mask_incremental env (id,tys) =
  match env with
    [] -> [[]]
  | (i,j,mask,id1)::env' ->
     let tyss = if id=id1 then  [tys] else lookup_terms_te(id1) in
     if tyss=[] then []
     else 
      let venvs = if id=id1 then mk_venvs_mask env' 
                  else mk_venvs_mask_incremental env' (id,tys) in
      if venvs=[] then []
      else
      (* this may blow up the number of type environments *)
       let tyss' = if j-i+1=List.length mask then tyss
                  else mask_tys i mask tyss []
       in  mk_prod_venvs (i,j,tyss') venvs []

let rec range_types ty1 ty2 =
  List.fold_left
  (fun ty ity1 ->
     match ity1 with
       ItyFun(_,ty3,ity)->
         if (* not(List.exists (fun ity0 -> subtype ity0 ity) ty)
  	     && *)
            List.for_all 
            (fun ity3-> List.exists (fun ity2-> subtype ity2 ity3) ty2)
            ty3
         then add_ity ity ty
         else ty
     | _ -> assert false
  ) [] ty1 
 
exception Untypable

let rec size_of_vte vte =
  match vte with
   [] -> 0
 | (_,ty)::vte' -> List.length ty + size_of_vte vte'


let rec pick_smallest_vte ity_vte_list =
  match ity_vte_list with 
      [] -> raise Untypable
   | (_,vte)::ity_vte_list' -> 
      let n = size_of_vte vte in
        pick_smallest_vte_aux ity_vte_list' n vte
and pick_smallest_vte_aux ity_vte_list n vte =
  match ity_vte_list with 
      [] -> vte
   | (_,vte')::ity_vte_list' -> 
      let n' = size_of_vte vte in
        if n'<n then 
          pick_smallest_vte_aux ity_vte_list' n' vte'
        else 
          pick_smallest_vte_aux ity_vte_list' n vte

let pick_vte ity ity_vte_list =
  try
     snd(List.find (fun (ity',vte)-> subtype ity' ity) ity_vte_list )
  with Not_found -> raise Untypable
(*
  let ity_vte_list' = List.filter (fun (ity',vte)-> subtype ity' ity) ity_vte_list in
    pick_smallest_vte ity_vte_list'
*)

let rec merge_vtes vtes =
  match vtes with
    [] -> []
 | vte::vtes' ->
     merge_two_vtes vte (merge_vtes vtes')
and merge_two_vtes vte1 vte2 =
  match (vte1,vte2) with
    ([], _) -> vte2
  | (_,[]) -> vte1
  | ((v1,ty1)::vte1', (v2,ty2)::vte2') ->
     let n = compare v1 v2 in
      if n<0 then (v1,ty1)::(merge_two_vtes vte1' vte2)
      else if n>0 then (v2,ty2)::(merge_two_vtes vte1 vte2')
      else (v1,merge_ty ty1 ty2)::(merge_two_vtes vte1' vte2')

let rec insert_ty_with_vte (ity,vte) ty =
  match ty with
    [] -> [(ity,vte)]
 | (ity1,vte1)::ty' ->
      let c= compare_ity ity ity1 in
      if c<0 then (ity,vte)::ty
      else if c>0 then (ity1,vte1)::(insert_ty_with_vte (ity,vte) ty')
      else if size_of_vte vte < size_of_vte vte1 
           then (ity,vte)::ty'
           else ty

let rec range_types_with_vte ty1 ty2 =
  List.fold_left
  (fun ty (ity1,vte1) ->
    match ity1 with 
       ItyFun(_,ty3,ity)->
        ( try
            let vtes = List.map (fun ity3 -> pick_vte ity3 ty2) ty3 in
            let vte' = merge_vtes (vte1::vtes) in
              insert_ty_with_vte (ity,vte') ty
          with Untypable -> ty)
     | _ -> assert false
  ) [] ty1 

let ty_of_nt f =
  Array.fold_left (@) []  (!nteref).(f)


let ty_of_nt_q f q =
  (!nteref).(f).(q)

let ty_of_nt_qs f qs =
  let tyarray = (!nteref).(f) in
  List.fold_left (fun ty q -> List.rev_append tyarray.(q) ty) [] qs

let ty_of_t_qs a qs = 
  let tyarray = lookup_cte a in
  List.fold_left (fun ty q -> List.rev_append tyarray.(q) ty) [] qs

let proj_tys f i tys = tys.(i)

let rec ty_of_var venv (f,i) =
  match venv with 
    [] -> assert false
  | (j1,j2,tys)::venv' ->
    if j1<=i && i<=j2 then
       proj_tys f (i-j1) tys 
    else ty_of_var venv' (f,i)

let rec ty_of_term venv term =
  match term with
   NT(f) -> ty_of_nt f
 | T(a) -> ty_of_t a
 | Var(v) -> ty_of_var venv v 
 | App(t1,t2) ->
    let ty1 = ty_of_term venv t1 in
    let ty2 = ty_of_term venv t2 in
      range_types ty1 ty2

let rec ty_of_term_with_vte venv term =
  match term with
   NT(f) -> List.map (fun ity -> (ity,[])) (ty_of_nt f)
 | T(a) -> List.map (fun ity -> ity,[]) (ty_of_t a)
 | Var(v) -> let ty = ty_of_var venv v in
              List.map (fun ity->(ity,[(v,[ity])])) ty
 | App(t1,t2) ->
    let ty1 = ty_of_term_with_vte venv t1 in
    let ty2 = ty_of_term_with_vte venv t2 in
      range_types_with_vte ty1 ty2

let rec ty_of_term_with_vte_qs venv term qs =
  match term with
   NT(f) -> let ty = ty_of_nt_qs f qs in
               List.map (fun ity -> (ity,[])) ty
 | T(a) -> let ty=ty_of_t_qs a qs in
               List.map (fun ity -> (ity,[])) ty
 | Var(v) -> let ty = ty_of_var venv v in
            let ty' = List.filter (fun ity->List.mem (codom_of_ity ity) qs) ty in
              List.map (fun ity->(ity,[(v,[ity])])) ty'
 | App(t1,t2) ->
    let ty1 = ty_of_term_with_vte_qs venv t1 qs in
    let ty2 = ty_of_term_with_vte venv t2 in
      range_types_with_vte ty1 ty2

let rec split_ity arity ity =
  if arity=0 then ([],ity)
  else match ity with
    ItyFun(_,ty,ity1)->
      let (tys,ity') = split_ity (arity-1) ity1 in
         (ty::tys, ity')
  | _ -> assert false
let rec get_range ity arity =
  if arity=0 then ity
  else 
    match ity with
      ItyFun(_,_,ity1) -> get_range ity1 (arity-1)
    | _ -> assert false

let rec ty_of_head h venv = 
  match h with
   NT(f) -> (ty_of_nt f)
 | T(a) -> (ty_of_t a)
 | Var(v) -> ty_of_var venv v
 | _ -> assert false


let rec ty_of_head_q h venv q = 
  match h with
   NT(f) -> List.map (fun ity -> (ity,[])) (ty_of_nt_q f q)
 | T(a) -> List.map (fun ity -> ity,[]) (ty_of_t_q a q)
 | Var(v) -> let ty = ty_of_var venv v in
              List.map (fun ity->(ity,[(v,[ity])])) ty
 | _ -> assert false

let rec ty_of_head_q2 h venv q = 
  match h with
   NT(f) -> (ty_of_nt_q f q)
 | T(a) -> (ty_of_t_q a q)
 | Var(v) -> ty_of_var venv v 
 | _ -> assert false

let rec get_argtys arity ity =
  if arity=0 then []
  else 
    match ity with
      ItyFun(_,ty,ity1) -> ty::(get_argtys (arity-1) ity1)
    | _ -> assert false



let match_head_ity h venv arity ity =
  match ity with
    ItyQ(q) -> 
      (match h with
          Var(v) ->
            if !num_of_states=1 then
              let ty = (ty_of_var venv v) in
                List.map (fun ity1 -> get_argtys arity ity1) ty
            else 
            let ty = List.filter (fun ity1->codom_of_ity ity1=q) (ty_of_var venv v) in
              List.map (fun ity1 -> get_argtys arity ity1) ty
        | _ ->
             let ty = ty_of_head_q2 h venv q in
              List.map (fun ity1 -> get_argtys arity ity1) ty
       )
  | _ ->
   let q = codom_of_ity ity in
    let ty = List.filter (fun ity1 -> 
              subtype (get_range ity1 arity) ity) (ty_of_head_q2 h venv q) in
       List.map (fun ity -> get_argtys arity ity) ty

let match_head_types h venv arity ity =
  match ity with
    ItyQ(q) -> 
      (match h with
          Var(v) -> 
            let ty = (ty_of_var venv v) in
            let ty' = if !num_of_states=1 then
                         ty
                      else List.filter (fun ity1->codom_of_ity ity1=q) ty 
            in
              List.map (fun ity1 -> (get_argtys arity ity1, [(v,[ity1])])) ty'
        | _ ->
             let ty = ty_of_head_q2 h venv q in
              List.map (fun ity1 -> (get_argtys arity ity1, [])) ty
       )
  | _ ->
    let ty = List.filter (fun (ity1,_) -> 
            subtype (get_range ity1 arity) ity) (ty_of_head_q h venv (codom_of_ity ity)) in
      List.map (fun (ity,vte) -> (get_argtys arity ity, vte)) ty

let rec check_args tys_ity_list terms venv ty =
   match tys_ity_list with
     [] -> ty
   | (tys,ity)::tys_ity_list' ->
       if check_args_aux tys terms venv
       then
(if !Flags.merge_vte then
	  let ty' = List.filter (fun ity1->not(eq_ity ity ity1)) ty in
	  let tys_ity_list'' =
	     List.filter (fun (_,ity1)->not(eq_ity ity ity1)) tys_ity_list'
	  in
	     check_args tys_ity_list'' terms venv (ity::ty')
else
	  let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in
	  let tys_ity_list'' =
	     List.filter (fun (_,ity1)->not(subtype ity ity1)) tys_ity_list'
	  in
	     check_args tys_ity_list'' terms venv (ity::ty')
)
       else
	     check_args tys_ity_list' terms venv ty
and check_args_aux tys terms venv =
  match (tys,terms) with
    ([], []) -> true
  | (ty::tys', t::terms') ->
       List.for_all (fun ity-> check_term t ity venv) ty
       && check_args_aux tys' terms' venv
  | _ -> assert false

and check_term term ity venv =
  match term with
    App(_,_) -> 
     let (h,terms) = Grammar.decompose_term term in
     let tyss = match_head_ity h venv (List.length terms) ity in
       List.exists (fun tys->check_args_aux tys terms venv) tyss
  | Var(v) -> List.exists (fun ity1 -> subtype ity1 ity) (ty_of_var venv v)
  | T(a) -> let q = codom_of_ity ity in
       List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
  | NT(f) -> let q = codom_of_ity ity in
       List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)

(* alternative implementation of ty_of_term *)
let ty_of_term2 venv term =
  let (h,terms) = Grammar.decompose_term term in
  let ty = ty_of_head h venv in
  let arity = List.length terms in
  let tys_ity_list = List.map (split_ity arity) ty in
     check_args tys_ity_list terms venv []
(* returns ty list *)
let ty_of_terms venv terms =
  if !(Flags.ty_of_term) then
   List.map (fun term ->
        List.sort compare_ity (ty_of_term venv term)) terms
  else
   List.map (fun term ->
     match term with
       Var(v) -> ty_of_var venv v
      | T(a) -> List.sort compare_ity (ty_of_t a)
      | NT(f) -> List.sort compare_ity (ty_of_nt f)
      | App(_,_) ->  List.sort compare_ity (ty_of_term2 venv term)) terms

(*
module X = struct type t = Grammar.term * Grammar.ity;;
                  let equal (t1,ity1) (t2,ity2) = t1==t2 && (id_of_ity ity1)=(id_of_ity ity2);; 
                  let hash = Hashtbl.hash end;;
module TabCheckTy = Hashtbl.Make(X)
let tab_checkty = TabCheckTy.create 10000
let reset_ty_hash() = TabCheckTy.clear tab_checkty
*)
let reset_ty_hash() = ()
let rec check_ty_of_term venv term ity =
(*
  try
     TabCheckTy.find tab_checkty (term,ity)
  with
    Not_found ->
*) 
 match term with
    App(_,_) ->
     let (h,terms) = Grammar.decompose_term term in
     let tyss = match_head_types h venv (List.length terms) ity in
     let vte = check_argtypes venv terms tyss in vte
(*        (TabCheckTy.replace tab_checkty (term,ity) vte; vte)
*)
  | Var(v) ->
    ( try
       let ity1 = List.find (fun ity1 -> subtype ity1 ity) (ty_of_var venv v) in
          [(v, [ity1])]
     with Not_found -> raise Untypable)
  | T(a) ->
      let q = codom_of_ity ity in
       if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
       then []
       else raise Untypable
  | NT(f) ->
      let q = codom_of_ity ity in
       if  List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)
       then []
       else raise Untypable

and check_argtypes venv terms tyss =
  match tyss with
    [] -> raise Untypable
  | (tys,vte0)::tyss' ->
     ( try
        merge_two_vtes vte0 (check_argtypes_aux venv terms tys)
       with Untypable -> 
         check_argtypes venv terms tyss')
and check_argtypes_aux venv terms tys =
  match (terms,tys) with
    ([], []) -> []
  | (t::terms',ty::tys') ->
      let vtes = List.map (fun ity -> check_ty_of_term venv t ity) ty in
      let vte = check_argtypes_aux venv terms' tys' in
         merge_vtes (vte::vtes)
  | _ -> assert false 


(* incremental version of check_ty_of_term *)
let rec check_ty_of_term_inc venv term ity f tyf =
     let (h,terms) = Grammar.decompose_term term in
     let arity = List.length terms in
     let tyss = 
         if h=NT(f) then
            let ty1 = List.filter (fun ity1 -> subtype (get_range ity1 arity) ity) tyf in
              if ty1=[] then raise Untypable
              else List.map (fun ity -> (get_argtys arity ity, [])) ty1
         else match_head_types h venv arity ity 
     in
     let vte = check_argtypes_inc venv terms tyss f tyf in vte
and check_argtypes_inc venv terms tyss f tyf =
  match tyss with
    [] -> raise Untypable
  | (tys,vte0)::tyss' ->
     ( try
        merge_two_vtes vte0 (check_argtypes_inc_aux venv terms tys f tyf)
       with Untypable -> 
         check_argtypes_inc venv terms tyss' f tyf)
and check_argtypes_inc_aux venv terms tys f tyf =
  match (terms,tys) with
    ([], []) -> []
  | (t::terms',ty::tys') ->
      let vtes = List.map (fun ity -> check_ty_of_term_inc venv t ity f tyf) ty in
      let vte = check_argtypes_inc_aux venv terms' tys' f tyf in
         merge_vtes (vte::vtes)
  | _ -> assert false 



let update_ty_of_id_aux id venvs overwrite_flag = 
  let terms = Ai.id2terms id in
   List.iter
   (fun venv -> 
     let ty = ty_of_terms venv terms in
     register_terms_te id ty overwrite_flag)
   venvs

(* update the set of types for each term list [t1;...;tk] *)
let update_ty_of_id id env overwrite_flag =
(*  (if !Flags.debugging then
   (print_string ("updating the type for "^(string_of_int id)^"\n");
    Ai.print_binding env));
*)
  let venvs = mk_venvs_mask env in 
  update_ty_of_id_aux id venvs overwrite_flag

let rec mk_funty venv ity = 
  match venv with
    [] -> ity
  | (i,j,ty)::venv' ->
      (* here, we assume that venv=[(i1,j1);...;(ik,jk)] where 
         i_{x+1} = j_x+1
       *)
      let ity' = mk_funty venv' ity in
        mk_funty_aux ty ity'
and mk_funty_aux tys ity =
  match tys with
    [] -> ity
  | ty::tys' -> mkItyFun(ty,mk_funty_aux tys' ity)

let rec mk_funty_with_vte vte ity arity = 
  mk_funty_with_vte_aux vte ity 0 arity
and mk_funty_with_vte_aux vte ity i arity =
  if i>=arity then ity
  else
    match vte with
       [] -> mkItyFun([], mk_funty_with_vte_aux vte (ity) (i+1) arity)
     | ((_,j),ty)::vte' ->
          if i=j then mkItyFun(ty, mk_funty_with_vte_aux vte' ity (i+1) arity)
          else mkItyFun([], mk_funty_with_vte_aux vte (ity) (i+1) arity)

exception REFUTED

let register_nte nt ity =
  let tyarray = (!nteref).(nt) in
  let q = codom_of_ity ity in
  let ty = tyarray.(q) in
   if List.exists (fun ity1 -> subtype ity1 ity) ty then ()
   else 
      (Cegen.register_nte_for_cegen nt ity q;
       flag_updated_nt := true;
       let _ = Utilities.debug ("updated type of nt "^(name_of_nt nt)^"\n") in 
       Setqueue.enqueue !updated_nts nt;
       enqueue_nt_ty nt ity;
       let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in
       let ty'' = ity::ty' in
(* no need to sort the type of nt *)
(*       let ty'' = merge_ty ty' [ity] in *)
         (!nteref).(nt).(q) <- ty'';
           if nt=0 && id_of_ity ity=0 then raise REFUTED else ())


let update_incremental_ty_of_id termid (id,tys) overwrite_flag = 
  let envs = Ai.lookup_dep_id_envs termid in
   List.iter (fun env -> 
      if List.exists (fun (_,_,_,id1)->id=id1) env then 
        let venvs = mk_venvs_mask_incremental env (id,tys) in
        update_ty_of_id_aux termid venvs overwrite_flag
      else ()
   ) envs

let update_ty_of_nt_aux nt venvs qs =
  let (_,term)=Grammar.lookup_rule nt in
  List.iter 
  (fun venv ->
if not(!(Flags.compute_alltypes)) then
(*     reset_ty_hash();*)
     List.iter (fun q ->
(*  this check actually often slows down
      let ity = mk_funty venv (ItyQ(q)) in
      if List.exists (fun ity'->subtype ity' ity) (!nteref).(nt).(q) then ()
      else
*)
        try
         let vte = check_ty_of_term venv term (ItyQ(q)) in
           register_nte nt (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt nt))
        with Untypable -> ()) qs
else
     let qs' = qs in
(* List.filter
              (fun q ->
                 let ity = mk_funty venv (ItyQ(q)) in
                 not(List.exists (fun ity' ->subtype ity' ity) (!nteref).(nt).(q))) qs in
*)
     let ty = ty_of_term_with_vte_qs venv term qs' in
     let ty' = List.filter (fun (ity,_)-> List.mem (id_of_ity ity) qs') ty in
     List.iter (fun (ity,vte)-> register_nte nt (mk_funty_with_vte vte ity (Grammar.arity_of_nt nt))) ty'
)
  venvs

let prod_vte vtes1 vtes2 =
  match (vtes1,vtes2) with
     (_,[]) -> []
   | ([],_)-> []
   | (_,[[]]) -> vtes1
   | ([[]], _) -> vtes2
   | _ ->
     List.fold_left
     (fun vtes vte1 ->
        let vtes2' = List.rev_map (fun vte2->merge_two_vtes vte1 vte2) vtes2 in
(*        let vtes2' = List.rev_append vtes2' [] in *)
	   List.rev_append vtes2' vtes)
     [] vtes1

let rec tcheck_w_venv venv term ity =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | NT(f)->	
      let q = codom_of_ity ity in
      let ty = (ty_of_nt_q f q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
       List.fold_left
       (fun vtes (tys,vte1) ->
         let vtes1=tcheck_terms_w_venv venv terms tys in
         let vtes1'= List.rev_map (fun vte0->merge_two_vtes vte0 vte1) vtes1 in
         List.rev_append vtes1' vtes) [] tyss
and tcheck_terms_w_venv venv terms tys =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_w_venv venv t ty in
      let vtes2=tcheck_terms_w_venv venv terms' tys' in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_w_venv venv t ty =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_w_venv venv t ity in
      let vtes2 = tcheck_term_ty_w_venv venv t ty' in
         prod_vte vtes1 vtes2


let update_ty_of_nt_with_merged_vte nt venvs qs =
  Utilities.debug ("updating the type of nt "^(name_of_nt nt)^"\n");
  let (_,term)=Grammar.lookup_rule nt in
  List.iter 
  (fun venv ->
     List.iter (fun q ->
       let vtes = tcheck_w_venv venv term (ItyQ(q)) in
       List.iter (fun vte-> register_nte nt (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt nt)))
         vtes
       ) qs
)
  venvs


let update_ty_of_nt nt binding qs =
 if !Flags.merge_vte then
  let venvs = mk_venvs binding in update_ty_of_nt_with_merged_vte nt venvs qs
 else
  let venvs = mk_venvs binding in update_ty_of_nt_aux nt venvs qs

let update_incremental_ty_of_nt (f,env,qs) (id,tys) = 
  if List.length (List.filter (fun (_,_,id')->id=id') env) =1
  then
    let venvs = mk_venvs_incremental env (id,tys) in
    if !Flags.merge_vte then
      update_ty_of_nt_with_merged_vte f venvs qs
    else
     update_ty_of_nt_aux f venvs qs
  else
    update_ty_of_nt f env qs


(* given a new type f:ity, update the type of g *)

let update_ty_of_nt_inc_for_nt_sub_venv g term venv qs f ty =
  List.iter (fun q ->
   try 
     let vte = check_ty_of_term_inc venv term (ItyQ(q)) f ty in
          register_nte g (mk_funty_with_vte vte (ItyQ(q)) (Grammar.arity_of_nt g))
   with Untypable -> ()) 
  qs

     
let rec tcheck_wo_venv term ity =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | NT(f)->	
      let q = codom_of_ity ity in
      let ty = (ty_of_nt_q f q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let tyss = match_head_ity h [] (List.length terms) ity in
       List.fold_left
       (fun vtes tys ->
         (tcheck_terms_wo_venv terms tys)@vtes) [] tyss
and tcheck_terms_wo_venv terms tys =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_wo_venv t ty in
      let vtes2=tcheck_terms_wo_venv terms' tys' in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_wo_venv t ty =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_wo_venv t ity in
      let vtes2 = tcheck_term_ty_wo_venv t ty' in
         prod_vte vtes1 vtes2

let rec tcheck_wo_venv_inc term ity g ty_g =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | NT(f)->	
      let ty = if f=g then ty_g else 
               let q = codom_of_ity ity in ty_of_nt_q f q 
      in
        if List.exists (fun ity1->subtype ity1 ity) ty then
	    [[]]
	else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let arity = List.length terms in
      let tyss =
        if h=NT(g) then
          let ty = List.filter (fun ity1 -> 
              subtype (get_range ity1 arity) ity) ty_g in
          List.map (fun ity -> get_argtys arity ity) ty
        else match_head_ity h [] arity ity
      in
       List.fold_left
       (fun vtes tys ->
         (tcheck_terms_wo_venv_inc terms tys g ty_g)@vtes) [] tyss
and tcheck_terms_wo_venv_inc terms tys g ty_g =
  match (terms,tys) with
    ([], []) -> [[]]
  | (t::terms', ty::tys') ->
      let vtes1=tcheck_term_ty_wo_venv_inc t ty g ty_g in
      let vtes2=tcheck_terms_wo_venv_inc terms' tys' g ty_g in
        prod_vte vtes1 vtes2
  | _ -> assert false
and tcheck_term_ty_wo_venv_inc t ty g ty_g =
  match ty with
    [] -> [[]]
  | ity::ty' ->
      let vtes1 = tcheck_wo_venv_inc t ity g ty_g in
      let vtes2 = tcheck_term_ty_wo_venv_inc t ty' g ty_g in
         prod_vte vtes1 vtes2
	 
let update_ty_of_nt_wo_venv f =
  let (_,term)=Grammar.lookup_rule f in
  let qs = (!Ai.array_st_of_nt).(f) in
    List.iter
     (fun q ->
       let ity=ItyQ(q) in
       let vtes = tcheck_wo_venv term ity in
       List.iter (fun vte ->
         register_nte f
	  (mk_funty_with_vte vte ity (Grammar.arity_of_nt f)))
       vtes) qs
       
let update_ty_of_nt_inc_wo_venv f g ty = 
  let _ = Utilities.debug
          ("updating the type of "^(name_of_nt f)^" incrementally\n") in
  let (_,term)=Grammar.lookup_rule f in
  let qs = (!Ai.array_st_of_nt).(f) in
  let _ = 
    List.iter
     (fun q ->
       let ity=ItyQ(q) in
       let vtes = tcheck_wo_venv_inc term ity g ty in
       List.iter (fun vte ->
         register_nte f
	  (mk_funty_with_vte vte ity (Grammar.arity_of_nt f)))
       vtes) qs
  in Utilities.debug ("done!\n")


let update_ty_of_nt_inc_for_nt_sub g term binding qs f ty =
  let venvs = mk_venvs binding in
    List.iter (fun venv -> 
     update_ty_of_nt_inc_for_nt_sub_venv g term venv qs f ty) venvs

let has_noheadvar f =
  (!Ai.array_headvars).(f)=[] && !Flags.eager

let update_ty_of_nt_incremental_for_nt g f ty =
  if has_noheadvar g then
     update_ty_of_nt_inc_wo_venv g f ty
  else
  let (_,term)=Grammar.lookup_rule g in
  let bindings = Ai.lookup_bindings_for_nt g in
    List.iter (fun (binding,qsref) ->
       update_ty_of_nt_inc_for_nt_sub
          g term binding !qsref f ty) bindings

let worklist_nt_binding = ref ([], Array.make 1 [])
let init_worklist_nt_binding maxnt =
  worklist_nt_binding := ([], Array.make maxnt []);
  updated_nt_ty := ([], Array.make maxnt [])
  
let enqueue_worklist_nt_binding (f,binding,qs) =
  let (nts, a) = !worklist_nt_binding in
  let x = a.(f) in
  if List.mem (binding,qs) x then ()
  else
    a.(f) <- (binding,qs)::x;
    if x=[] then worklist_nt_binding := (f::nts, a)
    else ()

exception WorklistBindingEmpty

let rec dequeue_worklist_nt_binding () =
  let (nts, a) = !worklist_nt_binding in
   match nts with
     [] -> raise WorklistBindingEmpty
   | f::nts' ->
       match a.(f) with
          [] -> (worklist_nt_binding := (nts',a);
	         dequeue_worklist_nt_binding ())
	| (binding,qs)::l ->
	    a.(f) <- l;
	    (if l=[] then worklist_nt_binding := (nts',a));
	    (f,binding,qs)

let remove_worklist_nt_binding nts =
  let (_, a) = !worklist_nt_binding in
   List.iter (fun f -> a.(f) <- []) nts

let print_worklist_nt_binding () =
  let (nts,a) = !worklist_nt_binding in
  List.iter (fun f->
    if not(a.(f)=[]) then print_string ((string_of_int f)^",")) nts;
  print_string "\n"
  
let add_worklist_nt_binding f =
  let (nts, a) = !worklist_nt_binding in
    a.(f) <-  List.map (fun (binding,qsref) -> (binding,!qsref))
              (Ai.lookup_bindings_for_nt f);
    worklist_nt_binding := (f::nts, a)
    
let rec mk_worklist_nt_binding updated_terms =
(*  print_string "calling mk_worklist\n";*)
  try
     let id = Setqueue.dequeue updated_terms in
     let bindings = Ai.lookup_dep_termid_nt id in
        List.iter enqueue_worklist_nt_binding bindings;
        mk_worklist_nt_binding updated_terms
  with Setqueue.Empty -> ()


(*
let rec mk_worklist_var updated_nts = 
  match updated_nts with
    [] -> []
  | f::updated_nts' ->
      merge_and_unify compare (Ai.lookup_dep_nt_termid f) (mk_worklist_var updated_nts')
*)

let max_termid() = !(Ai.terms_idref)
(*
let max_nt() = Array.length !(Ai.binding_array_nt) 
*)

let mk_worklist_var updated_nts =
  let queue = Setqueue.make (max_termid()) in
  List.iter
  (fun f -> List.iter (Setqueue.enqueue queue) (Ai.lookup_dep_nt_termid f))
    updated_nts;
  queue

let add_int n ns =
 if List.mem n ns then ns else n::ns

let addto_worklist_var_from_queue updated_nts =
  Setqueue.iter
  (fun f ->
    List.iter (Setqueue.enqueue !worklist_var) (Ai.lookup_dep_nt_termid f))
    updated_nts

let report_yes() =
  (print_string "The property is satisfied.\n";
   (if !Flags.certificate then (print_cte();print_nte()));
   if !Flags.outputfile="" then ()
                  else let fp = open_out !Flags.outputfile in
                     (output_string fp ("SATISFIED\n") ; close_out fp))

let rec saturate () =
  (* initialize the set of types for variables and non-terminals to empty *)
  let maxid = max_termid() in
  let maxnt = max_nt() in
   Cegen.init_nte();
   terms_te := Array.make maxid (ref TySeqNil);
   terms_tyss := Array.make maxid (Some []);
   for id=0 to maxid-1 do
     if (!Ai.termid_isarg).(id) then
       (!terms_te).(id) <- ref (TySeq [])
   done;
   check_point();
   nteref := Array.make maxnt [| |];
   for i=0 to maxnt-1 do
     (!nteref).(i) <- Array.make (!num_of_states) [] 
   done;
   check_point();
   init_worklist_nt_binding maxnt;
   init_worklist_var_ty maxid;
   check_point();
   let _ = (worklist_var := Setqueue.make maxid) in
   check_point();
   let _ = for id=0 to maxid-1 do 
           if (!Ai.termid_isarg).(id) then
              Setqueue.enqueue !worklist_var id
           done in
   check_point();
   let _ = (worklist_var_overwritten := Setqueue.make maxid) in
   let _ = (worklist_nt :=
      (* We can further restrict non-terminals to those that are reachable
         from the initial state;
	 however, if f is unreachable, the state set for f is empty, so
	 it does not do much harm to add f here
       *)
      Setqueue.make_fromlist maxnt
      (List.filter (fun f-> arity_of_nt f=0 || has_noheadvar f)
                   (Utilities.fromto 0 maxnt))) in
   let _ = (updated_nts := Setqueue.make maxnt) in
   check_point();
   (try
     saturate_vartypes()
    with REFUTED -> ());
   check_point();
   if !Flags.debugging then print_nte() else ();
   if !Flags.debugging then print_terms_te() else ();
   if (!nteref).(0).(0)=[] then report_yes()
   else 
     (print_string "The property is NOT satisfied.\n";
      Cegen.report_ce())

and saturate_vartypes() : unit =
(*  print_string "saturate_var\n";*)
  let proceed = ref false in
  (
   try
    let (id,tys) = dequeue_var_ty() in
(*   match dequeue_var_ty() with
    Some(id,tys) -> 
*)
    let _ = if !Flags.debugging then Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally\n") in
    let ids = Ai.lookup_dep_id id in
      List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) true) ids;
      let bindings = Ai.lookup_dep_termid_nt id in
      List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings
(*  | None -> *)
   with WorklistVarTyEmpty -> 
   try
    let (f,ty) = dequeue_nt_ty() in
    let _ = if !Flags.debugging then 
            Utilities.debug ("propagating type of nt "^(name_of_nt f)^" incrementally\n") 
    in
    let nts = Ai.lookup_dep_nt_nt_lin f in
    List.iter (fun g -> update_ty_of_nt_incremental_for_nt g f ty) nts
   with WorklistVarTyEmpty ->
   try
    let f = Setqueue.dequeue !updated_nts in
    let ids = Ai.lookup_dep_nt_termid f in
     List.iter (Setqueue.enqueue !worklist_var) ids;
     let nts = Ai.lookup_dep_nt_nt f in
        remove_worklist_nt_binding nts;
        List.iter (Setqueue.enqueue !worklist_nt) nts
   with Setqueue.Empty ->
  try
    let (f,binding,qs)=dequeue_worklist_nt_binding() in
     let _ = Utilities.debug ("processing nt "^(Grammar.name_of_nt f)^"\n") in
     flag_updated_nt := false;
     update_ty_of_nt f binding qs;
  with WorklistBindingEmpty ->
  try
     let f = Setqueue.dequeue !worklist_nt in
      if has_noheadvar f then
        update_ty_of_nt_wo_venv f
      else
        add_worklist_nt_binding f
  with Setqueue.Empty ->
  try
    let id = Setqueue.dequeue !worklist_var 
  in
  let _ = Utilities.debug ("processing terms "^(string_of_int id)^"\n") in
    let envs = Ai.lookup_dep_id_envs id in
      List.iter (fun env-> update_ty_of_id id env true) envs
  with Setqueue.Empty -> proceed := true
   );
   if !proceed then saturate_vartypes_wo_overwrite() 
   else saturate_vartypes()

and saturate_vartypes_wo_overwrite() : unit =
  let proceed = ref false in
 ( try
    let id = Setqueue.dequeue !worklist_var_overwritten in
    let _ = Utilities.debug ("processing terms "^(string_of_int id)^" without overwriting\n") in
    let envs = Ai.lookup_dep_id_envs id in
      List.iter (fun env-> update_ty_of_id id env false) envs 
  with Setqueue.Empty ->
  try
    let (id,tys) = dequeue_var_ty_wo_overwrite() in
(*   match dequeue_var_ty_wo_overwrite() with
   Some(id,tys) -> 
*)
    let _ = if !Flags.debugging then
             Utilities.debug ("propagating type of id "^(string_of_int id)^" incrementally wo overwrite\n") in
    let ids = Ai.lookup_dep_id id in
      List.iter (fun id1 -> update_incremental_ty_of_id id1 (id,tys) false) ids;
      let bindings = Ai.lookup_dep_termid_nt id in
      List.iter (fun binding -> update_incremental_ty_of_nt binding (id,tys)) bindings;
      saturate_vartypes_wo_overwrite()
  with WorklistVarTyEmpty -> proceed := true
(*
  | None -> proceed := true
*)
  );
  if !proceed 
  then if Setqueue.is_empty !updated_nts then ()
       else saturate_vartypes()
  else
    saturate_vartypes_wo_overwrite()
