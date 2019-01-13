(**** Copyright 2004 (see README and COPYING for details in the top directory) ***)
(********************************************************)
(********  A Library for boolean decison diagram ********)
(******** 14/07/2004, Written by Naoki Kobayashi ********)
(********************************************************)

exception Impossible;;

type var = int;;
type bdd = Node of var * bdd * bdd * int | Leaf of bool;;

let node_id t =
  match t with
    Leaf(true)-> 0
  | Leaf(false) -> 1
  | Node(v,t1,t2,x) -> x;;

let current_id = ref 2;;
let get_id() = (let x = !current_id in (current_id := x+1; x));;

module NodeHashType =
  struct
    type t = var * bdd * bdd
    let equal (v,t1,t2) (v',t1',t2') = (v==v')&&(t1==t1')&&(t2==t2')
    let hash (v,t1,t2) = (v lsl 10)+((node_id t1) lsl 5)+(node_id t2) 
(****    let hash (v,t1,t2) = Hashtbl.hash(v,(node_id t1),(node_id t2)) ***)
  end;;
module NodeHash = Hashtbl.Make(NodeHashType);;

let node_hashtbl = NodeHash.create 8192;;
let lookup_node_cache (x,t1,t2) = NodeHash.find node_hashtbl (x,t1,t2);;
let insert_in_node_cache (x,t1,t2) t = NodeHash.add node_hashtbl (x,t1,t2) t;;
let make_node (x,t1,t2) =
  try
    NodeHash.find node_hashtbl (x,t1,t2)
  with Not_found ->
    let t = Node(x,t1,t2,get_id()) in
      (NodeHash.add node_hashtbl (x,t1,t2) t;
       t);;
let reset_node_cache() = NodeHash.clear node_hashtbl;;

module Op1HashType =
  struct
    type t = bdd
    let equal t1 t2 = t1==t2
    let hash = node_id
  end;;
module Op1Hash = Hashtbl.Make(Op1HashType);;


let bdd_true = Leaf(true);;
let bdd_false = Leaf(false);;

let bdd_var (x:var) = 
   make_node(x, bdd_true, bdd_false);;

let bdd_nvar (x:var) = 
   make_node(x, bdd_false, bdd_true);;

(****************************************)
(********  Negation *********************)
(****************************************)
let neg_hashtbl = Op1Hash.create 256;;
let lookup_neg_cache = Op1Hash.find neg_hashtbl;;
let insert_in_neg_cache = Op1Hash.add neg_hashtbl;;
let reset_neg_cache() = Op1Hash.clear neg_hashtbl;;

let rec neg (t: bdd) =
  match t with
    Leaf b -> if b then bdd_false else bdd_true
  | Node(v, t1, t2,_) -> 
       try lookup_neg_cache t
       with Not_found -> (
         let t1' = neg t1 in
         let t2' = neg t2 in
           let t' = make_node (v,t1',t2') in
             (insert_in_neg_cache t t'; t'));;

(****************************************)
(************  Copy *********************)
(******* Copy obdd to cached space ******)
(****************************************)
let empty_cache = [];;
let insert_in_cache x v cache = (x,v)::cache;;
let lookup_cache = List.assq;;
(***
let copy_hashtbl = Op1Hash.create 256;;
let lookup_copy_cache = Op1Hash.find copy_hashtbl;;
let insert_in_copy_cache = Op1Hash.add copy_hashtbl;;
let reset_copy_cache() = Op1Hash.clear copy_hashtbl;;
let rec copy (t: bdd) =
  match t with
    Leaf b -> t
  | Node(v, t1, t2,_) -> 
       try lookup_copy_cache t
       with Not_found -> (
         let t1' = copy t1 in
         let t2' = copy t2 in
           let t' = make_node (v,t1',t2') in
              (insert_in_copy_cache t t'; t'))
***)
let rec copy_aux (t: bdd) cache =
  match t with
    Leaf b -> (t, cache)
  | Node(v, t1, t2,_) -> 
       try (lookup_cache t cache, cache)
       with Not_found -> (
         let (t1', cache1) = copy_aux t1 cache in
         let (t2', cache2) = copy_aux t2 cache1 in
         let t' = make_node (v,t1',t2') in
              (t', insert_in_cache t t' cache2)
      );;

let copy t = let (t',_) = copy_aux t empty_cache in t';;

(*********************************************)
(***** Normalization function (Obsolete?) ****)
(*********************************************)
let norm_hashtbl = Op1Hash.create 1024;;
let lookup_norm_cache = Op1Hash.find norm_hashtbl;;
let insert_in_norm_cache = Op1Hash.add norm_hashtbl;;
let reset_norm_cache() = Op1Hash.clear norm_hashtbl;;

let rec normalize t : bdd =
 match t with
    Leaf(b) -> (if b then bdd_true else bdd_false)
  | Node(v,t1, t2,_) ->
     try 
        lookup_norm_cache t
     with
       Not_found -> 
          let t1' = normalize t1 in
          let t2' = normalize t2 in
            if t1'==t2' then 
               (insert_in_norm_cache t t1'; t1')
            else
              let t' = make_node(v,t1',t2') in
                 (insert_in_norm_cache t t'; t');;

(************************************)
(***** Binary Operations on OBDD ****)
(************************************)

module Op2HashType =
  struct
    type t = bdd * bdd
    let equal (t1,t2) (t1',t2') = (t1==t1')&&(t2==t2')
    let hash (t1,t2) = ((node_id t1) lsl 5)+(node_id t2)
  end;;
module Op2Hash = Hashtbl.Make(Op2HashType);;

let and_hashtbl = Op2Hash.create 1024;;
let lookup_and_cache = Op2Hash.find and_hashtbl;;
let insert_in_and_cache = Op2Hash.add and_hashtbl;;
let reset_and_cache() = Op2Hash.clear and_hashtbl;;

let rec bdd_and (t1:bdd) (t2:bdd):bdd =
  match (t1,t2) with
      (Leaf b, _) ->
         if b then t2 else bdd_false
    | (_, Leaf b) -> 
         if b then t1 else bdd_false
    | (Node(v1,x11,x12,_),Node(v2,x21,x22,_)) ->
        try
          lookup_and_cache (t1, t2)
        with Not_found -> 
          let (z,x11,x12,x21,x22) =
                  if v1=v2 then (v1,x11,x12,x21,x22)
                  else if v1<v2 then (v1,x11,x12,t2,t2)
                  else (v2, t1, t1, x21,x22) in
          let t1' = bdd_and x11 x21 in
          let t2' = bdd_and x12 x22 in
          let t = if t1'==t2' then t1'
                  else make_node(z,t1',t2') in
            (insert_in_and_cache (t1,t2) t; t);;

let or_hashtbl = Op2Hash.create 1024;;
let lookup_or_cache = Op2Hash.find or_hashtbl;;
let insert_in_or_cache = Op2Hash.add or_hashtbl;;
let reset_or_cache() = Op2Hash.clear or_hashtbl;;

let rec bdd_or (t1:bdd) (t2:bdd):bdd =
  match (t1,t2) with
      (Leaf b, _) ->
         if b then bdd_true else t2
    | (_, Leaf b) -> 
         if b then bdd_true else t1
    | (Node(v1,x11,x12,_),Node(v2,x21,x22,_)) ->
        try
          lookup_or_cache (t1, t2)
        with Not_found -> 
          let (z,x11,x12,x21,x22) =
                  if v1=v2 then (v1,x11,x12,x21,x22)
                  else if v1<v2 then (v1,x11,x12,t2,t2)
                  else (v2, t1, t1, x21,x22) in
          let t1' = bdd_or x11 x21 in
          let t2' = bdd_or x12 x22 in
          let t = if t1'==t2' then t1'
                  else make_node(z,t1',t2') in
            (insert_in_or_cache (t1,t2) t; t);;

let imp t1 t2 = bdd_or (neg t1) t2;;

let iff_hashtbl = Op2Hash.create 1024;;
let lookup_iff_cache = Op2Hash.find iff_hashtbl;;
let insert_in_iff_cache = Op2Hash.add iff_hashtbl;;
let reset_iff_cache() = Op2Hash.clear iff_hashtbl;;

let rec iff (t1:bdd) (t2:bdd):bdd =
  match (t1,t2) with
      (Leaf b1, Leaf b2) ->
         if (b1&&b2)||((not b1)&&(not b2)) then bdd_true else bdd_false
    | _ ->
        try
          lookup_iff_cache (t1, t2)
        with Not_found -> 
          let (z,x11,x12,x21,x22) =
                match (t1, t2) with 
                   (Leaf _, Node(v2, x21,x22,_)) ->(v2, t1, t1, x21, x22)
                 | (Node(v1,x11,x12,_),Leaf _) -> (v1, x11, x12, t2, t2)
                 | (Node(v1,x11,x12,_),Node(v2,x21,x22,_)) ->
                     if v1=v2 then (v1,x11,x12,x21,x22)
                     else if v1<v2 then (v1,x11,x12,t2,t2)
                     else (v2, t1, t1, x21,x22) 
                 | _ -> raise Impossible
          in
          let t1' = iff x11 x21 in
          let t2' = iff x12 x22 in
          let t = if t1'==t2' then t1'
                  else make_node(z,t1',t2') in
            (insert_in_iff_cache (t1,t2) t; t);;

let bdd_orl tl = List.fold_right bdd_or tl bdd_false;;
let bdd_andl tl = List.fold_right bdd_and tl bdd_true;;

let bdd_eq (x:var) (y:var) =
   bdd_or (bdd_and (bdd_var x) (bdd_var y)) (bdd_and (bdd_nvar x) (bdd_nvar y));;

(************************************************)
(***** Existential/Universal Quantification *****)
(************************************************)
module ExistsHashType =
  struct
    type t = var list * bdd
    let equal (vl,t) (vl',t') = (vl==vl')&&(t==t')
(***    let hash (vl,t) = ((Hashtbl.hash vl) lsl 16)+(node_id t) ***)
    let hash (vl,t) = (node_id t)
  end;;
module ExistsHash = Hashtbl.Make(ExistsHashType);;
let exists_hashtbl = ExistsHash.create 1024;;
let lookup_exists_cache = ExistsHash.find exists_hashtbl;;
let insert_in_exists_cache = ExistsHash.add exists_hashtbl;;
let reset_exists_cache() = ExistsHash.clear exists_hashtbl;;

let rec exists_vl (vl:var list) x: bdd =
  if vl=[] then x
  else 
    match x with
      Leaf b -> x
    | Node(v, x1, x2,_) ->
       try lookup_exists_cache (vl, x)
       with Not_found -> (
          let x1' = exists_vl vl x1 in
          let x2' = exists_vl vl x2 in
          let x' = if x1'==x2' then x1'
                   else if List.mem v vl then bdd_or x1' x2' 
                   else make_node(v,x1',x2') in
             (insert_in_exists_cache (vl,x) x'; x')
       );;

let forall_hashtbl = ExistsHash.create 1024;;
let lookup_forall_cache = ExistsHash.find forall_hashtbl;;
let insert_in_forall_cache = ExistsHash.add forall_hashtbl;;
let reset_forall_cache() = ExistsHash.clear forall_hashtbl;;
let rec forall_vl (vl:var list) x: bdd =
  if vl=[] then x
  else 
    match x with
      Leaf b -> x
    | Node(v, x1, x2,_) ->
       try lookup_forall_cache (vl, x)
       with Not_found -> (
          let x1' = forall_vl vl x1 in
          let x2' = forall_vl vl x2 in
          let x' = if x1'==x2' then x1'
                   else if List.mem v vl then bdd_and x1' x2' 
                   else make_node(v,x1',x2') in
             (insert_in_forall_cache (vl,x) x'; x')
       );;

let exists v t = exists_vl [v] t;;
let forall v t = forall_vl [v] t;;

(*****************************)
(***** Variable Renaming *****)
(*****************************)

(*** The hash table for renaming function does not keep the variable renaming function, so that
 *** the table must be reset before a new renaming function is applied ***)
(***
let ren_hashtbl = Op1Hash.create 64;;
let lookup_ren_cache = Op1Hash.find ren_hashtbl;;
let insert_in_ren_cache = Op1Hash.add ren_hashtbl;;
let reset_ren_cache() = Op1Hash.clear ren_hashtbl;;

let rec rename_aux f (x: bdd) =
  match x with
    Leaf b -> x
  | Node(v, x1, x2,_) -> 
       try lookup_ren_cache x
       with Not_found -> (
         let x1' = rename_aux f x1 in
         let x2' = rename_aux f x2 in
         let x' =  make_node(f v, x1', x2') in
            (insert_in_ren_cache x x'; x')
       );;
let rec rename (f:var->var) (x:bdd) =
  let x' = rename_aux f x in ( reset_ren_cache(); x');;
***)

let rec rename_aux (f:var->var) (t: bdd) cache =
  match t with
    Leaf b -> (t, cache)
  | Node(v, t1, t2,_) -> 
       try (lookup_cache t cache, cache)
       with Not_found -> (
         let (t1', cache1) = rename_aux f t1 cache in
         let (t2', cache2) = rename_aux f t2 cache1 in
         let t' = make_node (f v,t1',t2') in
              (t', insert_in_cache t t' cache2)
      );;

let rename f t = let (t',_) = rename_aux f t empty_cache in t';;

(***************************************)
(*****    Relational Product       *****)
(***************************************)
module ProdHashType =
  struct
    type t = (var->bool) * bdd * bdd
    let equal (vl,t1,t2) (vl',t1',t2') = (vl==vl')&&(t1==t1')&&(t2==t2')
    let hash (vl,t1,t2) = ((node_id t1) lsl 8)+(node_id t2)
(***    let hash (vl,t1,t2) = Hashtbl.hash (vl, (node_id t1),(node_id t2)) ***)
  end;;
module ProdHash = Hashtbl.Make(ProdHashType);;
let prod_hashtbl = ProdHash.create 4096;;
let lookup_prod_cache = ProdHash.find prod_hashtbl;;
let insert_in_prod_cache = ProdHash.add prod_hashtbl;;
let reset_prod_cache() = ProdHash.clear prod_hashtbl;;

let rec relprod_aux (l:var->bool) r1 r2: bdd =
  match (r1,r2) with
   (Leaf(b1), Leaf(b2)) -> if b1&&b2 then bdd_true else bdd_false
 | _ ->
    try
       lookup_prod_cache (l,r1,r2)
    with Not_found -> (
      let (z, r11, r12, r21, r22) =
         match (r1,r2) with
            (Leaf(_), Node(v2,r21,r22,_)) -> (v2, r1, r1, r21, r22)
          | (Node(v1,r11,r12,_), Leaf _) -> (v1, r11, r12, r2, r2)
          | (Node(v1,r11,r12,_), Node(v2,r21,r22,_)) -> 
              if v1=v2 then (v1, r11, r12, r21, r22)
              else if v1<v2 then (v1, r11, r12, r2, r2)
              else (v2, r1, r1, r21, r22) 
          | _ -> raise Impossible
      in
      let r01 = relprod_aux l r11 r21 in
      let r02 = relprod_aux l r12 r22 in
      let r0 = if r01==r02 then r01
               else if l z then bdd_or r01 r02
               else make_node(z, r01, r02) in
          (insert_in_prod_cache (l,r1,r2) r0; r0)
     );;

(*** It may be better to reset the cache for the relational product ***)
let relprod l r1 r2 = relprod_aux l r1 r2;;
       
let rec fromto m n=
  if m>=n then [] 
  else m::(fromto (m+1) n);;

let iseven n = (n mod 2=0)
let apply (n:int) (f:bdd) (t:bdd) = 
   let t' = rename (function v -> 2*v) t in
(*   let vl = List.map (function v->2*v) (fromto 0 n) in *)
     rename(function v -> v/2) (relprod iseven f t');;

(*************************************************************)
(********* Equality Test for Two OBDDs (Obsolete?) ***********)
(*************************************************************)

(* Function equiv: bdd -> bdd -> bool judges the equivlence of two OBDDs.
 * To avoid the exponential cost, equiv_aux uses a cache 
 *)
exception Not_eq;;
let empty_eq_cache = [];;
let insert_in_eq_cache x1 x2 cache = (x1,x2)::cache;;
let lookup_eq_cache x1 x2 = 
   List.exists (function (x1',x2') -> x1==x1' && x2==x2');;
let rec equiv_aux x1 x2 cache =
  if lookup_eq_cache x1 x2 cache then cache
  else
    match (x1, x2) with
     (Leaf b1, Leaf b2) -> 
         if b1=b2 then
            insert_in_eq_cache x1 x2 cache
         else raise Not_eq
   | (Node(v1,x11,x12,_), Node(v2, x21, x22,_)) ->
        if v1=v2 then
           insert_in_eq_cache x1 x2 (equiv_aux x12 x22 (equiv_aux x11 x21 cache))
        else raise Not_eq
   | _ -> raise Not_eq;;
let equiv x1 x2 = 
   try let _ = equiv_aux x1 x2 empty_eq_cache in true with Not_eq -> false ;;

(**********************************************)
(********* Catamorphism on OBDD ***************)
(**********************************************)

(*** It should behave as follows:
 * let rec cata f_node f_leaf (t:bdd) =
 * match t with
 *   Leaf(b) -> f_leaf(b)
 *   | Node(v,t1,t2) ->
 *       let r1 = cata f_node f_leaf t1 in
 *       let r2 = cata f_node f_leaf t2 in
 *         f_node n r1 r2;;
***)

(*** The following is an actual implementation, using cache ***)

let cata f_node f_leaf (x:bdd) =
  let rec cata_aux (x:bdd) cache = 
     match x with
       Leaf(b) -> (f_leaf(b), cache)
     | Node(v,x1,x2,_) -> 
        try ((lookup_cache x cache), cache)
        with Not_found -> (
           let (r1, cache1) = cata_aux x1 cache in
           let (r2, cache2) = cata_aux x2 cache in
           let r = f_node v r1 r2 in
              (r, insert_in_cache x r cache2)
        ) in
  let (r, _) = cata_aux x empty_cache in
      r;;
      
(**********************************************)
(********* Fixed-point Computation ************)
(**********************************************)
(* fixp f t repeatedly applies f to t until OBDD t becomes stable *)
(* In order for the computation to terminate,
 * f must not reset the node cache and must be monotonic 
 * and the range of f must be finite *)
let rec fixp_aux (f:bdd->bdd) (t:bdd) n=
   let t' = (f t) in
     if t==t' then t else fixp_aux f t' (n+1);;
let fixp f t = fixp_aux f t 0;;
(***
let rec fixp (f:bdd->bdd) (t:bdd) =
   let t' = (f t) in
     if t==t' then t else fixp f t';;
***)
(*****************************************************)
(********* Interface for Resetting Cache *************)
(*****************************************************)
let reset() =
  (
   reset_node_cache();
   reset_neg_cache();
   reset_and_cache();
   reset_or_cache();
   reset_iff_cache();
   reset_exists_cache();
   reset_forall_cache();
   reset_prod_cache());;



(*****************************************************)
(******* Some Utility Functions for Debugging ********)
(*****************************************************)
type varnp = POS of var | NEG of var;;

let rec to_dnf t =
  match t with
     Leaf(true) -> [[]]
   | Leaf(false) -> []
   | Node(v, t1, t2,_) ->
       let dnf1 = to_dnf t1 in
       let dnf2 = to_dnf t2 in
          (List.map (function l -> POS(v)::l) dnf1)@(List.map (function l -> NEG(v)::l) dnf2);;


(*
let rec list_of_nodes_aux t l memo = 
  match t with
   Leaf _ -> l
 | Node(v,t1,t2,i) ->
    if S.mem i !memo then l else begin
      memo := S.add i !memo;
      (list_of_nodes_aux t2 (list_of_nodes_aux t1 (t::l)))
    end;;
 let list_of_nodes  list_of_nodes_aux t [] (ref S.empty);;
*)
let list_of_nodes t = 
  let module S = Set.Make(struct type t = int let compare = compare end) in
  let memo = ref S.empty in
  let rec sub t l = 
    match t with
     Leaf _ -> l
   | Node(v,t1,t2,i) ->
      if S.mem i !memo then l else begin
        memo := S.add i !memo;
        (sub t2 (sub t1 (t::l)))
      end 
  in sub t []

let size t= List.length (list_of_nodes t);;

(*** a function to make a bdd that is very large as a tree, but small as a dag ***)
let eq n = bdd_andl [bdd_eq (6*n) (6*n+1);bdd_eq (6*n+2) (6*n+3);bdd_eq (6*n+4) (6*n+5)];;
let eqs l = bdd_andl (List.map eq l);;


(* 
 * add by Taku Terao
 * 03/12/2013
 *)
let sat_min t =
  let rec go acc = function
    | Leaf(true) ->  Some(acc)
    | Leaf(false) -> None
    | Node(v,t1,t2,_) -> 
        match go acc t2 with
          | None -> go (v::acc) t1
          | res -> res
  in go [] t;;

let print_as_dot t label =
  let module S = Set.Make(struct type t = int let compare = compare end) in
  let rec go memo t = 
    let n = node_id t in
    if S.mem n memo then 
      memo
    else match t with
      | Leaf(true) -> 
          print_int n;
          print_string " [label=\"1\"];\n";
          S.add n memo
      | Leaf(false) -> 
          print_int n;
          print_string " [label=\"0\"];\n";
          S.add n memo
      | Node(v,t1,t2,_) ->
          let n1 = node_id t1 in
          let n2 = node_id t2 in
          print_int n;
          print_string " [label=\"";
          label v;
          print_string "\"];\n";
          print_int n;
          print_string " -> ";
          print_int n1;
          print_string "[label=\"1\"];\n";
          print_int n;
          print_string " -> ";
          print_int n2;
          print_string "[label=\"0\"];\n";
          go (go (S.add n memo) t1) t2
  in
  print_string "digraph {\n"; 
  let _ = go S.empty t in
  print_string "}\n";;
