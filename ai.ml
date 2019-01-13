open Grammar;;
open Automaton;;
open Utilities;;

type states = int list
type termid = int
type head = Hnt of nameNT | Hvar of nameV | Ht of nameT
(*
type aterm = term  * (term list) list
*)
type aterm = head  * termid list
   (* aterm = (t, [[t11; ...; t1k];...;[tj1; ...;tjk]]) represents
       t t11 ... t1k  ... tj1 ... tjk, where
       t,tij are subterms of the lefthand side of a rule of the grammar 
       [ti1;...;tik] share the same environment
    *)
type node = aterm * states
let normalized_body = ref [||]
let lookup_body f = (!normalized_body).(f)

let tab_state_id = Hashtbl.create 100
let tab_id_state = Hashtbl.create 100

let state_idref = ref 0
let new_state_id() =
  let x = !state_idref in
   (state_idref := x+1; x)

let register_state q =
  try 
    let _ = Hashtbl.find tab_state_id q in ()
  with Not_found ->
   ( let x=new_state_id() in
      Hashtbl.add tab_state_id q x;
      Hashtbl.add tab_id_state x q)

let id2state id =
  try Hashtbl.find tab_id_state id 
  with Not_found -> assert false

let state2id q = 
  try
  Hashtbl.find tab_state_id q
  with Not_found -> 
  (  print_string ("state "^q^" has not been registered\n");
    assert false)

(* necessary tables:
- trtab:
   information about transitions of the form
    (q,a) -->  [|Q1,...,Qk|]
  this is extracted from transition rules of the automaton.
  If the automaton is deterministic,
  the table should keep the map
    (q,a) --> ({q1},...,{qk})
  for each transition rule delta(q,a)=q1...qk.
  If the automaton is alternating,
  the table should keep the map
    (q,a) --> (Q1,...,Qk)
  where Qi is the set of states q occurring in the form of (i,q)
  in delta(q,a)

- map from aterm to node

- binding information, which maps 
   each variable x to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
   each non-terminal to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
   (the former can be obtained from the latter and the table below)
   Should the binding also contain information about which terms share the environment
   (so, [[~t11];...;[~tik]] instead of (t11,...,t1k))
   
- map from each subterm to the non-terminal of the rule containing the subterm?
- map from each variable to a pair consisting of non-terminal and index?
  (to make it easy to find binding)
*)

let trtab : (int*nameT, int list array) Hashtbl.t = Hashtbl.create 1000

let mk_trtab m =
  register_state m.init;
  List.iter register_state m.st;
  let tr = m.delta in
  Hashtbl.clear trtab;
  List.iter (fun ((q,a),qs) ->
   let arity = List.length qs in
   let x = Array.make arity [] in
   let indices = fromto 0 arity in
     List.iter 
     (fun (i,q') -> x.(i) <- [state2id q']) 
     (List.combine indices qs);
     Hashtbl.add trtab (state2id q,a) x
   ) tr

let rec merge_statevecs qsvecs =
  match qsvecs with
    [] -> assert false
  | [qsvec] -> qsvec
  | qsvec1::qsvecs' ->
     let merged = Array.copy qsvec1 in
       List.iter (fun qsvec2 -> let _=merge_statevec merged qsvec2 in ()) qsvecs';
       merged    
and merge_statevec qsvec1 qsvec2 =
   let len = Array.length qsvec1 in
    for i=0 to len-1 do
       qsvec1.(i) <- Utilities.merge_and_unify compare (qsvec1.(i)) (qsvec2.(i))
    done; 
    qsvec1

let rec get_qs form arity =
  match form with
    AlternatingAutomaton.Bool _ -> Array.make arity []
  | AlternatingAutomaton.Var (i,q) ->
     let x = Array.make arity [] in
       (x.(i-1) <- [state2id q]; x) (* index is shifted *)
  | AlternatingAutomaton.Or(f1, f2) ->
     merge_statevec (get_qs f1 arity) (get_qs f2 arity)
  | AlternatingAutomaton.And(f1, f2) ->
    merge_statevec (get_qs f1 arity) (get_qs f2 arity)
      

let mk_trtab_for_ata m =
  register_state m.AlternatingAutomaton.init;
  List.iter register_state m.AlternatingAutomaton.st;
  Hashtbl.clear trtab;
  List.iter (fun ((q,a), form) ->
    let arity = List.assoc a m.AlternatingAutomaton.alpha in
    let qs' = get_qs form arity in
      Hashtbl.add trtab (state2id q,a) qs')
   m.AlternatingAutomaton.delta

(*
let tab_id_terms = Hashtbl.create 100000
*)
let tab_id_terms = ref [||]
let termid_isarg = ref [||]


let lookup_id_terms id =
 (!tab_id_terms).(id)

let decompose_aterm (aterm: aterm) =
  let (h, termids) = aterm in
  let aterms =
    match termids with
      [] -> []
    | [id] -> let (aterms,_,_)=lookup_id_terms id in aterms
    | _ -> 
      List.rev_append
      (List.fold_left
       (fun aterms id ->
          let (aterms',_,_)=lookup_id_terms id in
    	    List.rev_append aterms' aterms) [] termids) []
  in (h, aterms)	    

let expand_state q a = 
   try Hashtbl.find trtab (q,a) 
   with Not_found -> Array.make (Grammar.arity_of_t a) []

let expand_states qs a =
  merge_statevecs (List.map (fun q -> expand_state q a) qs) 

(* return a binding of the form:
    [ [t11;...;t1m]; ... [tk1;...;tkm]]
   each block [t11;...;t1m] shares the same environment
 *)
let mk_binding _ termss = termss

let binding_array_nt = ref [||]
let binding_array_var = ref [||]
let array_headvars = ref [||]
let array_st_of_nt = ref [||]

let print_states qs =
  List.iter (fun q -> print_string ((id2state q)^",")) qs

let print_binding_and_qs (binding,qsref) =
   List.iter (fun (i,j,id1) ->
       print_string ("("^(string_of_int i)^","^(string_of_int j)^","^(string_of_int id1)^"), "))
   binding; 
   print_string "::";
   print_states !qsref;
   print_string "\n"

let print_binding binding =
   List.iter (fun (i,j,id1) ->
       print_string ("("^(string_of_int i)^","^(string_of_int j)^","^(string_of_int id1)^"), "))
   binding; 
   print_string "\n"

let print_binding_array() =
  print_string "bindings (nt --> bindings list )\n";
  for f=0 to Array.length !binding_array_nt - 1 do
    print_string ((Grammar.name_of_nt f)^":\n");
    List.iter print_binding_and_qs (!binding_array_nt).(f)
  done
let terms_idref = ref 0
let new_terms_id() =
  let x = !terms_idref in
    (terms_idref := x+1; x)

let tab_terms_id = Hashtbl.create 100000
(*
let lookup_aterms aterms =
  try
    Hashtbl.find tab_terms_id aterms
  with Not_found ->
    let id = new_terms_id() in
     (Hashtbl.add tab_terms_id aterms id;  id)
*)
(* tables that associate a list of terms [t1;...;tk] with its identifier *)

let id2aterms id =
  let (aterms,_,_)=(!tab_id_terms).(id) in aterms
let id2terms id =
  let (_,terms,_)=(!tab_id_terms).(id) in terms
let id2vars id =
  let (_,_,vars)=(!tab_id_terms).(id) in vars


let print_tab_id_terms() =
  print_string "Id --> Terms\n";
  for id=0 to !terms_idref-1 do
   if (!termid_isarg).(id) then 
    let terms = id2terms id in
    if terms=[] then ()
    else
    (
     print_int id;
     print_string ":";
     List.iter (fun t -> print_term t; print_string ", ") terms;
     print_string "\n")
   else ()
  done
  
let arity_of_term id =
 let (aterms,_,_) = lookup_id_terms id in
   List.length aterms

let rec add_index rho i =
  match rho with
    [] -> []
  | termsid::rho' ->
      let n = List.length (id2terms termsid) in
(*       if n<9 then *)
        let j = i+n in
          (i,j-1,termsid)::(add_index rho' j)
(* identifier of [t1;...;tk] to a set of non-terminals
   whose variables may be bound to [t1;...;tk]
 *)
let tab_termid_nt = ref [| |] (*Hashtbl.create 10000 *)
let register_dep_termid_nt id nt termss qs =
  (!tab_termid_nt).(id) <-
      let x = (!tab_termid_nt).(id) in
(*      if List.mem (nt,termss,qs) x then x
      else
*)      (nt,termss,qs)::x
(*       merge_and_unify compare [(nt,termss,qs)] (!tab_termid_nt).(id)
*)

let lookup_dep_termid_nt id =
  (!tab_termid_nt).(id) 

let insert_nt_binding f rho qs bindings = 
  let rho' = add_index rho 0 in
    (rho', ref qs)::bindings


(* var -> nodes that have var as the head *)
let tab_variableheadnode = ref [||] (* Hashtbl.create 10000 *)

let register_VariableHeadNode v (noderef: node ref) =
  let (nt,i) = v in
  let a = (!tab_variableheadnode).(nt) in
    a.(i) <- noderef::a.(i)
(*
  try 
    let x = Hashtbl.find tab_variableheadnode v in
      x := noderef::!x
  with Not_found ->
    Hashtbl.add tab_variableheadnode v (ref [noderef]) 
*)

let lookup_VariableHeadNode (nt,i) =
   (!tab_variableheadnode).(nt).(i)
(*
  try
     !(Hashtbl.find tab_variableheadnode v)
  with Not_found -> []
*)
let insert_var_binding term terms =
  if List.mem term terms then (terms,false)
  else (term::terms,true)
(*  merge_and_unify compare [term] terms
*)
let print_aterm (term,termss) =
  print_term term;
  List.iter (fun terms -> 
    print_string "[";
    List.iter (fun t ->
       print_string "(";
       print_term t;
       print_string ") ") terms;
    print_string "]";
   ) termss
     

let print_states qs =
  List.iter (fun q -> print_string ((id2state q)^" ")) qs

let print_node (aterm,qs) =
  print_aterm aterm;
  print_string ":";
  print_states qs

(*
let nodequeue = ref ([], [])
let clear_nodequeue() = (nodequeue := ([], []))
let enqueue_node node =
(*   print_string "Enqueued:"; print_node node; print_string "\n";*)
   Utilities.enqueue node nodequeue

let dequeue_node () =
   Utilities.dequeue nodequeue

let enqueue_nodes nodes =
   List.iter enqueue_node nodes
*)
let nodequeue = ref []
let clear_nodequeue() = (nodequeue := [])
let enqueue_node node =
(*   print_string "Enqueued:"; print_node node; print_string "\n";*)
   nodequeue := node::!nodequeue

let dequeue_node () =
   match !nodequeue with
     [] -> None
   | x::q -> (nodequeue := q; Some(x))

let enqueue_nodes nodes =
   List.iter enqueue_node nodes

let expand_varheadnode term (node: node ref) =
  let (aterm,qs) = !node in
  let (h,termss) = (*decompose_aterm*) aterm in
    match h with
      Hvar(x) ->
        let (h',terms)=term in
	   enqueue_node ((h', terms@termss),qs) 
    | _ -> assert false

let expand_varheadnodes f i term =
  let nodes = lookup_VariableHeadNode (f,i) in
   List.iter (expand_varheadnode term) nodes

let register_binding_singlevar f i term =
  let tab = (!binding_array_var).(f) in
  let (binds,changed) = insert_var_binding term tab.(i) in
   if changed then
      (tab.(i) <- binds;
       expand_varheadnodes f i term)
   else
      ()

let lookup_binding_var (f,i) = 
   (!binding_array_var).(f).(i)

let rec register_var_bindings f rho i =
  match rho with
    [] -> ()
  | termsid::rho' ->
      let aterms = id2aterms termsid in
      let aterms' = indexlist aterms in
        List.iter 
         (fun (j,aterm)-> register_binding_singlevar f (i+j) aterm)
        aterms';
        register_var_bindings f rho' (i+List.length aterms)

let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
    qref := merge_and_unify compare qs !qref

let register_binding f rho qs =
  List.iter (fun id -> (!termid_isarg).(id) <- true) rho;  
  (!binding_array_nt).(f) <- (insert_nt_binding f rho qs (!binding_array_nt).(f));
  register_var_bindings f rho 0
let lookup_bindings_for_nt f =
  (!binding_array_nt).(f)

let merge_states qs1 qs2 = merge_and_unify compare qs1 qs2
let diff_states qs1 qss2 = List.filter (fun q -> not(List.mem q qss2)) qs1

(* aterm -> ref (aterm, qs) *)

module HType = struct type t=aterm;; let equal i j = i=j;; let hash = Hashtbl.hash_param 100 100 end
module ATermHashtbl = Hashtbl.Make(HType)
let nodetab = ATermHashtbl.create 100000


let register_newnode (aterm, qs) = 
  if ATermHashtbl.mem nodetab aterm then assert false;
(*  print_string "Registered:"; print_node (aterm,qs); print_string "\n";*)
  let node = ref (aterm,qs) in
    ATermHashtbl.add nodetab aterm node;
    node

let lookup_nodetab aterm = 
  try
    Some(ATermHashtbl.find nodetab aterm)
  with Not_found -> None


let expand_terminal a termss qs = 
   let aterms = termss in
   let qss = expand_states qs a in  
        (* qss = [Q1;...;Qk] where Qi is the set of the possible states for the i-th child *)
   let aterms' = Utilities.indexlist aterms in
     List.iter (fun (i,aterm) ->
                  if qss.(i)=[] then () else enqueue_node (aterm, qss.(i))) aterms'


let states_of_node node =
  let (_,qs) = !node in qs

let update_states_of_node node qs =
  let (aterm,_)= !node in node := (aterm,qs)


let rec size_of_appterm t =
 match t with
   App(t1,t2) ->
     ( match t1 with
          App(_,_) -> size_of_appterm t1 + size_of_appterm t2
        | _ -> 1+size_of_appterm t2)
 | _ -> 0
 
let size_of_rules r =
  Array.fold_left (fun s (_,t) -> s+ size_of_appterm t) 0 r

let term2head h =
   match h with
    Var(x) -> Hvar(x)
  | NT(f) -> Hnt(f)
  | T(a) -> Ht(a)
  | _ -> assert false
  
let vars_in_aterm (h,ids) =
  let vs1 = match h with Hvar(x)->[x] | _ -> [] in
    List.fold_left
            (fun vs id ->
	      merge_and_unify compare vs
	         (id2vars id)) vs1 ids 

let vars_in_aterms aterms =
 List.fold_left
 (fun vars aterm ->
    merge_and_unify compare vars (vars_in_aterm aterm))
  [] aterms

let rec convert_term t =
  let (h,terms)=Grammar.decompose_term t in
   if terms=[] then (term2head h, [])
   else
     let aterms = List.map convert_term terms in
     let vars = vars_in_aterms aterms in
     let id =
       try
         Hashtbl.find tab_terms_id aterms
       with Not_found ->
       ( let id = new_terms_id() in
        Hashtbl.add tab_terms_id aterms id; 
        (!tab_id_terms).(id) <- (aterms,terms,vars);
         id)
     in
       (term2head h, [id])

let dummy_aterm = (Hnt(-1), [])

let init_tab_id_terms g =
 let size = size_of_rules g.r in
  tab_id_terms := Array.make size ([],[],[]);
  termid_isarg := Array.make size false;
  normalized_body := Array.make (Array.length g.r) (-1,dummy_aterm);
  for f=0 to Array.length g.r - 1 do
    let (arity,body)=Grammar.lookup_rule f in
    let u = convert_term body in
     (!normalized_body).(f) <- (arity,u)
  done     

let init_expansion q0 =
 ATermHashtbl.clear nodetab;
(* Hashtbl.clear tab_variableheadnode; *)
 clear_nodequeue ();
 let g = !(Grammar.gram) in
 let num_of_nts = Array.length g.nt in
  init_tab_id_terms g;
  binding_array_nt := Array.make num_of_nts [];
  binding_array_var := Array.make num_of_nts [||];
  for i=0 to num_of_nts-1 do
   (!binding_array_var).(i) <- Array.make (arity_of_nt i) []
  done;
  tab_variableheadnode := Array.make num_of_nts [||];
  for i=0 to num_of_nts-1 do
   (!tab_variableheadnode).(i) <- Array.make (arity_of_nt i) []
  done;
 enqueue_node ((Hnt(0), []), [q0])

let childnodes (h,termss) = 
(* we need to compute child nodes explicitly, 
  since aterms in the queue have not been registered yet.
  To avoid duplicated work, we may wish to register nodes immediately *)
  match h with
     Hnt(f) ->
          let (_,body) = lookup_body f in [body]
   | Hvar(v) ->
         let terms = lookup_binding_var v in
           List.map (fun (h,terms) -> (h,terms@termss)) terms;
   | _ -> assert false

let process_node (aterm,qs) = 
     let (h, termss) = decompose_aterm aterm in
     match lookup_nodetab aterm with
       Some(node) -> (* aterm has been processed before *)
        begin
         let qs' = states_of_node node in
         let qs'' = diff_states qs qs' in
         if qs''=[] then (* states qs have been processed before *)
           ()
         else begin
           update_states_of_node node (merge_states qs' qs'');
           match h with
              Ht(a) -> expand_terminal a termss qs''
            | Hnt(f) -> (* re-process children with new states *)
              let (_,rho) = aterm in
              add_binding_st f rho qs'';
              let aterms = childnodes aterm in
                List.iter
                 (fun aterm1 -> enqueue_node (aterm1,qs'')) aterms
            | Hvar _ -> (* re-process children with new states *)
              let aterms = childnodes aterm in
                List.iter
                 (fun aterm1 -> enqueue_node (aterm1,qs'')) aterms
          end
        end
    | None -> (* aterm has not been processed *)
       let node = register_newnode (aterm,qs) in
       match h with
         Ht(a) -> expand_terminal a termss qs
       | Hvar(x) ->
          let (_,termids)=aterm in
          let terms = lookup_binding_var x in
           (List.iter (fun (h,terms) -> enqueue_node ((h,terms@termids),qs)) terms;
            register_VariableHeadNode x node)
       | Hnt(f) -> 
          let (arity,body) = lookup_body f in
          let (_,rho) = aterm in
            (register_binding f rho qs;
             enqueue_node (body, qs))

let num = ref 0

let rec expand() =
    match dequeue_node() with
    None -> (print_string ("size of ACG: "^(string_of_int (ATermHashtbl.length nodetab))^"\n")
           (*  print_string ("# of expansion: "^(string_of_int (!num))^"\n") *))     (* no more node to expand *)
  | Some(aterm,qs) ->
      (* num := !num+1;*) process_node(aterm,qs); expand()


(* linearity information on terminal symbols *)
let tab_linearity: (string, bool array) Hashtbl.t = Hashtbl.create 100

(* identifier of [t1;...;tk] --> identifiers of [s1;...;sl] 
   that depend on the value of [t1;...;tk];
   in other words, if id is mapped to [id1;...;idk] and
   the type of id has been updated, the types of id1,...,idk should
   be recomputed 
let tab_penv_binding = Hashtbl.create 10000
*)
let tab_penv_binding = ref [| |]

(* identifier of [t1;...;tk] ---> a list of [(i,j,id1);...]
  [(i1,j1,id1);...;(ik,j1,idk)] being an element of the list
  means that the i_x-th to j_x-th free variables in [t1;...;tk]
  may be bound to the terms represented by id_x 
let tab_binding_env: (termid, (int*int*termid) list list) Hashtbl.t = Hashtbl.create 10000
*)

let tab_binding_env = ref [| |]

let register_dep_penv_binding id1 id2 =
 let ids = (!tab_penv_binding).(id1) in
(*   if List.mem id2 ids then ()
   else
 *)
    (!tab_penv_binding).(id1) <-id2::ids
(*
  try
   let idsref = Hashtbl.find tab_penv_binding id1 in
    (idsref := merge_and_unify compare [id2] !idsref)
  with Not_found ->
    Hashtbl.add tab_penv_binding id1 (ref [id2])
*)
let lookup_dep_id id =
  (!tab_penv_binding).(id)
(*
  try
   let idsref = Hashtbl.find tab_penv_binding id in
     !idsref
  with Not_found -> []
*)
let register_dep_binding_env id bindings =
  (!tab_binding_env).(id) <- bindings
(*
  Hashtbl.add tab_binding_env id bindings
*)

let print_mask mask =
 print_string "[";
 List.iter(fun i-> print_string((string_of_int i)^",")) mask;
 print_string "]"
 
let print_binding_with_mask binding =
   List.iter (fun (i,j,mask,id1) ->
       print_string ("("^(string_of_int i)^ "," ^(string_of_int j) ^ ",");
       print_mask mask;
       print_string(", "^(string_of_int id1)^"), "))
   binding; 
   print_string "\n"

let print_tab_binding_env() =
  print_string "dependency info. (id --> [(i,j,id1);...])\n";
  for id=0 to Array.length !tab_binding_env - 1 do
    if (!termid_isarg).(id) then
     (print_int id; print_string ":\n";
      List.iter print_binding_with_mask (!tab_binding_env).(id))
  done

let register_dep_env_binding env (id:termid) =
  List.iter (fun (_,_,_,id1)-> register_dep_penv_binding id1 id) env

let lookup_dep_id_envs id =
  (!tab_binding_env).(id)
(*
  try
    Hashtbl.find tab_binding_env id
  with Not_found -> []
*)

let rec split_vars vars j =
  match vars with
     [] -> ([], [])
   | v::vars' ->
      if v>j then ([], vars)
      else
        let (vars1,vars2)=split_vars vars' j in
	   (v::vars1,vars2)
	   
let rec mk_binding_with_mask vars binding: (int * int * int list * int) list =
  match binding with
    [] -> []
  | (i, j, id)::binding' ->
      let (vars1,vars2) = split_vars vars j in
        if vars1=[] then
	   mk_binding_with_mask vars2 binding'
        else
(*          let vars1c = List.filter (fun i->not(List.mem i vars1)) (fromto i (j+1)) in *)
          (i, j, vars1, id)::(mk_binding_with_mask vars2 binding')

let rec filter_binding vars binding =
  match binding with
    [] -> []
  | (i,j,id)::binding' ->
      match vars with
         [] -> []
       | v::vars' ->
           if v<i then filter_binding vars' binding
	   else if v<=j then
	      (i,j,id)::(filter_binding vars' binding')
	   else filter_binding vars binding'

let ids_in_bindings bindings =
  let ids =
    List.fold_left (fun ids binding ->
       List.rev_append (List.map (fun (_,_,id)->id) binding) ids
    ) [] bindings
  in
    delete_duplication_unsorted ids
    
let mk_binding_depgraph_for_terms id vars =
  if vars = [] then
     register_dep_binding_env id [[]]
  else
   let f = fst(List.hd vars) in
   let vars' = List.map snd vars in
   let bindings = (!binding_array_nt).(f) in
   let bindings' =
      delete_duplication_unsorted
      (List.rev_map (fun (binding,_)->filter_binding vars' binding) bindings)
(*
     List.fold_left
       (fun bindings1 (binding,_) ->
         let b = filter_binding vars' binding in
   	   if List.mem b bindings1 then bindings1
	   else b::bindings1)
       [] bindings
*)       
   in
   let bindings_with_mask =
      List.rev_map (mk_binding_with_mask vars') bindings'
   in
   let ids = ids_in_bindings bindings' in
(*   
   let bindings_with_mask =
    List.fold_left
      (fun bindmasks (binding,_) ->
        let b = mk_binding_with_mask vars' binding in
	if List.mem b bindmasks then bindmasks
	else b::bindmasks)
      [] bindings
   in
*)   
     register_dep_binding_env id bindings_with_mask;
     List.iter (fun id1 -> register_dep_penv_binding id1 id) ids
(*
     List.iter (fun env-> register_dep_env_binding env id)  bindings_with_mask
*)
let mk_binding_depgraph_for_termss f (termss,qsref) =
(*  List.iter mk_binding_depgraph_for_terms termss;*)
  let qs = !qsref in
  List.iter (fun (_,_,id) -> register_dep_termid_nt id f termss qs) termss

let mk_binding_depgraph_for_nt f termsss =
  if (!array_headvars).(f)=[] && !Flags.eager then
    List.iter (fun (_,qsref)->
         (!array_st_of_nt).(f) <-
	      merge_and_unify compare (!array_st_of_nt).(f) !qsref)
    termsss	      
       (* if no variable occurs in the head position,
          we do not use binding information to compute the type of f *)
  else
    List.iter (mk_binding_depgraph_for_termss f) termsss

let array_dep_nt_termid = ref [| |]
let array_dep_nt_nt = ref [| |]
let array_dep_nt_nt_lin = ref [| |]

let print_dep_nt_nt_lin() =
 for i=0 to Array.length (!array_dep_nt_nt_lin)-1 do
   let nts = (!array_dep_nt_nt_lin).(i) in
   if nts=[] then ()
   else
     (print_string ((name_of_nt i)^" linearly occurs in ");
      List.iter (fun j-> print_string ((name_of_nt j)^",")) nts;
      print_string "\n")
 done

let init_array_dep_nt_termid() =
  let n = Array.length (!binding_array_nt) in
     array_dep_nt_termid := Array.make n []

let init_array_dep_nt_nt() =
  let n = Array.length (!binding_array_nt) in
     array_dep_nt_nt := Array.make n [];
     array_dep_nt_nt_lin := Array.make n []

(* nt occurs in the term id *)
let register_dep_nt_termid nt id =
  let ids = (!array_dep_nt_termid).(nt) in
  (* this function can never be called with the same (nt,id) pair *)
  let ids' = id::ids (*merge_and_unify compare [id] ids*) in
   (!array_dep_nt_termid).(nt) <- ids'

let register_dep_nt_nt nt1 nt2 =
  let nts = (!array_dep_nt_nt).(nt1) in
  let nts' = merge_and_unify compare [nt2] nts in
   (!array_dep_nt_nt).(nt1) <- nts'

let register_dep_nt_nt_lin nt1 nt2 =
  let nts = (!array_dep_nt_nt_lin).(nt1) in
  let nts' = merge_and_unify compare [nt2] nts in
   (!array_dep_nt_nt_lin).(nt1) <- nts'

      

let lookup_dep_nt_termid nt =
  (!array_dep_nt_termid).(nt)
let lookup_dep_nt_nt nt =
  (!array_dep_nt_nt).(nt)
let lookup_dep_nt_nt_lin nt =
  (!array_dep_nt_nt_lin).(nt)

let rec nt_in_terms terms =
  match terms with
   [] -> []
 | t::terms' -> merge_and_unify compare (Grammar.nt_in_term t) (nt_in_terms terms')

let merge_nts_lin (nts1,nts2) (nts3,nts4) =
 let (nts11,nts12) =
    List.partition (fun f->List.mem f nts3 || List.mem f nts4) nts1 in
 let (nts31,nts32) =
    List.partition (fun f->List.mem f nts1 || List.mem f nts2) nts3 in
   (merge_and_unify compare nts12 nts32,
    merge_and_unify compare nts11
      (merge_and_unify compare nts31 
      (merge_and_unify compare nts2 nts4)))

let rec nt_in_term_with_linearity term =
   match term with
     Var(_) -> ([], [])
   | T(_) ->  ([], [])
   | NT(f) -> ([f], [])
   | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
       (match h with
          NT(f) -> let nts = nt_in_terms terms in
	            if List.mem f nts then ([],nts)
		    else ([f],nts)
	| Var(_) -> ([], nt_in_terms terms)
	| T(a) ->
	    let linearity_info = Hashtbl.find tab_linearity a in
	      nt_in_terms_with_linearity terms linearity_info 0 ([],[])
	| _ -> assert false)
	
and nt_in_terms_with_linearity terms linearity_info i (nts1,nts2) =
 match terms with
   [] -> (nts1,nts2) 
 | t::terms' ->
     let (nts1',nts2') =
        if linearity_info.(i) then
          nt_in_term_with_linearity t
	else ([], Grammar.nt_in_term t)
     in
     let (nts1'',nts2'') = merge_nts_lin (nts1',nts2') (nts1,nts2) in
       nt_in_terms_with_linearity terms' linearity_info (i+1) (nts1'',nts2'')


let mk_binding_depgraph() =
  tab_termid_nt := Array.make !terms_idref [];
  tab_binding_env := Array.make !terms_idref [];
  tab_penv_binding := Array.make !terms_idref [];
  let n = Array.length (!binding_array_nt) in
  array_headvars := Array.make n [];
  array_st_of_nt := Array.make n [];
  for f=0 to n-1 do
      (!array_headvars).(f) <- (let (_,t)=Grammar.lookup_rule f in
                               headvars_in_term t);
      mk_binding_depgraph_for_nt f (!binding_array_nt).(f)
  done;
  (* make dependency nt --> id (which means "id depends on nt") *)
  check_point();
  init_array_dep_nt_termid();
  for id'=0 to !terms_idref - 1 do
   let id = !terms_idref - 1 -id' in
   if (!termid_isarg).(id) then
    let (_,terms,vars) = (!tab_id_terms).(id) in
      let nts = nt_in_terms terms in
        List.iter (fun nt -> register_dep_nt_termid nt id) nts
   else ()
  done;
  for id=0 to !terms_idref - 1 do
   if (!termid_isarg).(id) then
    let (_,terms,vars) = (!tab_id_terms).(id) in
	mk_binding_depgraph_for_terms id vars
   else ()
  done;
  check_point();
  (* make dependency nt1 --> nt2 (which means "nt2 depends on nt1") *)
  init_array_dep_nt_nt();
  let g = !(Grammar.gram) in
  let n = Array.length g.nt in
    for i=0 to n-1 do
      let (_,t) = Grammar.lookup_rule i in
      let (nts1,nts2) = nt_in_term_with_linearity t in
        List.iter (fun nt-> register_dep_nt_nt nt i) nts2;
        (if !Flags.incremental then
            List.iter (fun nt-> register_dep_nt_nt_lin nt i) nts1
         else 
            List.iter (fun nt-> register_dep_nt_nt nt i) nts1)
    done;
  if !Flags.debugging then
   (print_binding_array();
    print_tab_id_terms();
    print_tab_binding_env();
    print_dep_nt_nt_lin())
  else ()
  

