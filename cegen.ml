open Grammar;;
open Utilities;;
type tree = Node of string * tree list | Bottom

type eterm = ET of nameT * ity | ENT of nameNT * ity * int
           | EVar of nameV * ity | EApp of eterm * eterm list
           | ECoerce of ity * ity * eterm
exception Found of eterm 


let nteallref: (ity*int) list array array ref = ref [||]

let ty_of_ntall_q f q =
  (!nteallref).(f).(q)

let nty_id_ref = ref 0
let new_nty_id() =
  let x = !nty_id_ref in
   (nty_id_ref := !nty_id_ref+1; x)

let init_nte() =
  let maxnt = max_nt() in
  let maxq = !Type.num_of_states in
   (nteallref := Array.make maxnt [||];
    for f=0 to maxnt-1 do
     (!nteallref).(f) <- Array.make maxq []
    done)

let register_nte_for_cegen f ity q =
 let x = new_nty_id() in
  (!nteallref).(f).(q) <-
     (ity,x)::(!nteallref).(f).(q)

let rev_nte() =
  let maxnt = max_nt() in
  for f=0 to maxnt-1 do
   for q=0 to !Type.num_of_states-1 do
    (!nteallref).(f).(q) <- List.rev_append (!nteallref).(f).(q) []
   done
  done
  

let rec compose_eterm term termss =
  match termss with
    [] -> term
  | terms::termss' -> compose_eterm (EApp(term,terms)) termss'

let rec decompose_eterm term =
  match term with
   (ET _ | ENT _| EVar _ | ECoerce _) -> (term, [])
 | EApp(term',terms) -> 
    let (h,termss) =  decompose_eterm term' in
       (h, termss@[terms])

let tracetab = Hashtbl.create 1000

let rec mk_vte vars at =
    match at with
      ItyQ(q) -> 
        if vars=[] then 
           ([], ItyQ(q))
        else assert false 
    | ItyFun(_, ty, aty1) ->
       (  match vars with
            [] -> ([], at)
        | v::vars' -> 
             let (ve1, rt1) = mk_vte vars' aty1 in
               ((v, ty)::ve1, rt1)
       )

let mk_ehead h aty =
  match h with
    NT(f) -> assert false
  | T(a) -> ET(a,aty)
  | Var(x) -> EVar(x,aty)
  | _ -> assert false

let rec rangesubtype aty1 aty2 k =
  if k=0 then Type.subtype aty1 aty2
  else
   match aty1 with
     ItyQ(_) -> false
  | ItyFun(_,_,aty1') -> rangesubtype aty1' aty2 (k-1)

let lookup_headty vte h aty =
  match h with
    T(a) ->
      let q = Type.codom_of_ity aty in
        Type.ty_of_t_q a q 
  | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
  | _ -> assert false

let mk_vars f arity =
  let indices = fromto 0 arity in
   List.map (fun i -> (f,i)) indices

let rec find_derivation ntyid vte term aty =
  let (h,terms) = Grammar.decompose_term term in
  let k = List.length terms in
  let head_typings = find_headtype ntyid vte h aty k in
   try
     List.iter (fun (eh,aty0) ->
      try
       let (eterms,rty) = find_derivation_terms ntyid vte terms aty0 in
       let eterm1 = compose_eterm eh eterms in
       let eterm2 =
         if rty=aty then eterm1
         else ECoerce(rty,aty,eterm1)
       in raise (Found eterm2)
      with Not_found -> ()
     ) head_typings; raise Not_found
   with Found eterm -> eterm
and find_derivation_terms ntyid vte terms aty =
  match terms with
   [] -> ([], aty)
 | term::terms' ->
    match aty with
      ItyQ(_) -> raise Not_found
    | ItyFun(_,ty1,aty2) ->
       let eterms= find_derivation_ty ntyid vte term ty1 in
       let (etermss,rty) = find_derivation_terms ntyid vte terms' aty2 in
         (eterms::etermss, rty)
and find_derivation_ty ntyid vte term ty =
  List.map (find_derivation ntyid vte term) ty
and find_headtype ntyid vte h aty k =
  match h with
    NT(f) ->
     let ty = ty_of_ntall_q f (Type.codom_of_ity aty) in
     let ty' = List.filter 
             (fun (aty1,ntyid') ->
	        ntyid'<ntyid && rangesubtype aty1 aty k) ty in
         List.map (fun (aty1,i) -> (ENT(f,aty1,i), aty1)) ty'
   | _ ->
    let ty = lookup_headty vte h aty in
    let ty' = List.filter 
             (fun aty1 -> rangesubtype aty1 aty k) ty in
     List.map (fun aty1 -> (mk_ehead h aty1, aty1)) ty'

let register_backchain f ity ntyid =
  let (arity,body) = lookup_rule f in
  let vars = mk_vars f arity in
  let (vte,rty) = mk_vte vars ity in
  let eterm = try find_derivation ntyid vte body rty
              with Not_found -> 
                  (print_string ("failed to find a derivation for "^(name_of_nt f)^":");
                   Type.print_ity ity; assert false)
  in
  Hashtbl.add tracetab (f,ity) (vte,eterm)

let rec print_eterm eterm =
  match eterm with
    ENT(f,aty,_) -> print_string ((name_of_nt f)^"[");Type.print_ity aty;print_string "]"
  | ET(a,aty) -> print_string (a^"[");Type.print_ity aty;print_string "]"
  | EVar(v,aty) -> print_string ((name_of_var v)^"[");Type.print_ity aty;print_string "]"
  | EApp(t,ts) ->
     ( print_eterm t; print_string " ";
      List.iter
      (fun t1 -> print_eterm_sub t1; print_string " ") ts)
  | ECoerce(aty1,aty2,t) ->
    ( print_string "C[";Type.print_ity aty1;print_string "=>";Type.print_ity aty2;print_string "]";
     print_eterm t)
and print_eterm_sub eterm =
  match eterm with
    EApp(_,_) -> print_string "(";print_eterm eterm; print_string ")"
  | ECoerce(_,_,_)-> print_string "(";print_eterm eterm; print_string ")"
  | _ -> print_eterm eterm

let print_evars vte =
  List.iter
  (fun (v,ty) ->
    List.iter (fun aty ->
      print_string ((name_of_var v)^"[");Type.print_ity aty;print_string "] ") ty)
  vte


let print_erule f aty vte eterm =
  print_string ((name_of_nt f)^"[");
  Type.print_ity aty;
  print_string "]";
  print_evars vte;
  print_string "-> ";
  print_eterm eterm;
  print_string "\n"

let rec typings_in_eterm eterm =
  match eterm with
    ENT(f,aty,_) -> [(f,aty)]
  | ET(a,aty) -> []
  | EVar(v,aty) -> []
  | EApp(t,ts) -> 
        let typing1 = typings_in_eterm t in
        let typing2 = typings_in_eterms ts in
          merge_and_unify compare typing1 typing2
  | ECoerce(aty1,aty2,t) -> typings_in_eterm t
and typings_in_eterms eterms =
  List.fold_left 
  (fun typings eterm -> merge_and_unify compare typings (typings_in_eterm eterm))
  [] eterms


let rec print_tracetab g typings finished =
  match typings with
    [] -> ()
  | (f,ity)::typings' ->
     if List.mem (f,ity) finished then print_tracetab g typings' finished
     else
     let (vte,eterm) = Hashtbl.find tracetab (f,ity) in
     let (arity,_) = g.r.(f) in
     let (vte,_) = mk_vte (mk_vars f arity) ity in
     let _ = print_erule f ity vte eterm in
     let typings2 = typings_in_eterm eterm in
        print_tracetab g (merge_and_unify compare typings' typings2) ((f,ity)::finished)

let rec non_topaty aty =
  match aty with
    ItyQ(_) -> 1
  | ItyFun(_,ty,aty') ->
     if ty=[] then 1+(non_topaty(aty'))
     else 1

let vid = ref 0;;
let new_vname v = 
  let x = !vid in 
       (vid := !vid+1; (-1,x))
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

let rec mk_env vte termss =
  match (vte, termss) with
    ([], []) -> []
  | ((v,ty)::vte', ts::termss') ->
       let x = List.combine ty ts in
        (List.map (fun (ity,t)->((v,ity),t)) x)@(mk_env vte' termss')
  | _ -> assert false

let rename_vte_eterm vte eterm =
  let (vte',vmap) = rename_vte vte in
     (vte', rename_eterm eterm vmap)

let rec merge_tree t1 t2 =
  match (t1,t2) with
    (Bottom,_) -> t2
  | (_, Bottom) -> t1
  | (Node(a1,ts1),Node(a2,ts2)) ->
       if a1=a2 then
          Node(a1, merge_trees ts1 ts2)
       else assert false
and merge_trees ts1 ts2 =
  List.map (fun (t1,t2)->merge_tree t1 t2) (List.combine ts1 ts2)

let rec evaluate_eterm eterm env =
  let (h,termss) = decompose_eterm eterm in
  match h with
    ENT(f,ity,ntyid) -> 
    (try 
      let (vte,body) = 
           try Hashtbl.find tracetab (f,ity) with Not_found ->
	    (register_backchain f ity ntyid;
	     Hashtbl.find tracetab (f,ity)) in
      let (vte',body') = rename_vte_eterm vte body in
      let env' = mk_env vte' termss in
         evaluate_eterm body' (env'@env)
    with Not_found -> assert false)
 | ET(a,aty) -> 
   ( try
     let trees = List.map (fun ts -> evaluate_eterms ts env) termss in
        Node(a, trees)
    with Not_found -> assert false)
 | EVar(v,aty) ->
   (try
      let eterm1 = List.assoc (v,aty) env in
        evaluate_eterm (compose_eterm eterm1 termss) env
    with Not_found -> assert false)
 | ECoerce(aty1,aty2,t) ->
   ( try
      (match (aty1,aty2) with
         (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
       | (ItyFun(_,ty11,aty11), ItyFun(_,ty21,aty21)) ->
           (match termss with
             [] -> assert false
           | ts::termss' ->
               let tyterms = List.combine ty21 ts in
               let ts' = List.map (fun aty ->
                   let (aty',t') = List.find (fun (aty',_)->Type.subtype aty' aty) tyterms in
                     if aty=aty' then t' else ECoerce(aty',aty,t')) ty11
               in 
               let t1 = if aty11=aty21 then EApp(t,ts') else
                        ECoerce(aty11,aty21,EApp(t,ts'))
               in evaluate_eterm (compose_eterm t1 termss') env)
       | _ -> assert false )
    with Not_found -> assert false)
  | _ -> assert false
and evaluate_eterms ts env =
  match ts with
    [] -> Bottom
  | t::ts' -> 
     let t1 = evaluate_eterm t env in
     let t2 = evaluate_eterms ts' env in
       merge_tree t1 t2

let find_ce aty =
  let nt_s = 0 in
  let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in
  let _ = register_backchain nt_s aty ntyid in
(*  let _ = print_string "backchain constructed\n"; flush stdout in *)
(*  let _ = print_tracetab g [(nt_s,aty)] [] in *)
  let _ = flush stdout in
  let t =  evaluate_eterm (ENT(nt_s,aty,ntyid)) [] in
(*  let _ = print_string "tree constructed\n"; flush stdout in *)
    t

let rec string_of_tree t =
  match t with
   Node(a,tl) ->
      if tl=[] then a
      else "("^a^(string_of_trees tl)^")"
  | Bottom -> "_"

and string_of_trees tl =
  match tl with
   [] -> ""
  | t::tl' -> " "^(string_of_tree t)^(string_of_trees tl')

let rec find_nonbot tl i =
  match tl with
    [] -> (0, Bottom)
  | t::tl' ->
     match t with
        Bottom -> find_nonbot tl' (i+1)
      | Node(_,_) -> (i, t)

let rec string_of_path t =
  match t with
    Node(a,tl) ->
      let (i,t') = find_nonbot tl 1 in
        if i=0 then ("("^a^",0)")
        else ("("^a^","^(string_of_int i)^")"^(string_of_path t'))
  | _ -> assert false

let fp = ref stdout
let report_ce () =
  rev_nte();
  (if !Flags.outputfile="" then ()
   else (fp := open_out !Flags.outputfile;
         output_string !fp ("VIOLATED\n")));
  (if !Flags.ce then
       let t = find_ce (ItyQ(0)) in
       let ce = 
          if !Flags.dautomaton then
              string_of_path t
          else string_of_tree t in
       (print_string "A counterexample is:\n";
        print_string (ce^"\n");
        if not(!Flags.outputfile="") then output_string !fp (ce^"\n"))
   else ());
   if !Flags.outputfile="" then () else close_out !fp
  
