(* Polymorphic Ordered Binary Decision Diagram *)

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

module Make : functor (Elt : OrderedType) -> S with type var = Elt.t = 
  functor (Elt : OrderedType) ->
struct
  type var = Elt.t;;
  type id = int
  type varnp = POS of var | NEG of var

  type bdd = Node of var * bdd * bdd * id * var list | Leaf of bool;;
  type bdd_key = var * id * id;;
  type zdd = bdd

  let node_id = function
    | Leaf(true) -> 0
    | Leaf(false) -> 1
    | Node(_,_,_,x,_) -> x;;

  let bdd_vars = function
    | Leaf _ -> []
    | Node(_,_,_,_,l) -> l;;

  let id_seed = ref 2;;
  let gen_id () = 
    let i = !id_seed in
    incr id_seed;
    i;;

  let bdd_true  = Leaf true;;
  let bdd_false = Leaf false;;

  let compare_key (v1,i1,j1) (v2,i2,j2) = 
    if compare (i1:int) i2 <> 0 then compare i1 i2
    else if compare (j1:int) j2 <> 0 then compare j1 j2
    else Elt.compare v1 v2;;
       
  module HashType = 
    struct
      type t = bdd_key
      let equal (v1,i1,j1) (v2,i2,j2) = 
        i1 = i2 && j1 = j2 && Elt.compare v1 v2 = 0
      let hash (v,i,j) = let x = Elt.hash v in (x lsl 10)+(i lsl 5)+j
    end;;
  
  let rec merge_vars l1 l2 = if l1 == l2 then l1 else
    match (l1,l2) with
    | ([],l2) -> l2
    | (l1,[]) -> l1
    | (a::l1,b::l2) ->
        let d = Elt.compare a b  in
        if d < 0 then a::merge_vars l1 (b::l2)
        else if d > 0 then b:: merge_vars (a::l1) l2
        else a :: merge_vars l1 l2;;

  module NodeHash = Hashtbl.Make(HashType)
  let node_hashtbl = NodeHash.create 1000;;
  let make_node (v,t1,t2) =
    let i1 = node_id t1 in
    let i2 = node_id t2 in
    let key = (v,i1,i2) in
    assert (i1 <> i2);
    try
      NodeHash.find node_hashtbl key
    with Not_found -> begin
      let i = gen_id () in
      let l1 = bdd_vars t1 in
      let l2 = bdd_vars t2 in
      let l = merge_vars l1 l2 in
      let t = Node (v,t1,t2,i,v::l) in
      NodeHash.add node_hashtbl key t;
      t
    end;;
  
  let make_node_zdd (v,t1,t2) =
    let i1 = node_id t1 in
    let i2 = node_id t2 in
    let key = (v,i1,i2) in
    if i1 = 1 then t2 else 
    try
      NodeHash.find node_hashtbl key
    with Not_found -> begin
      let i = gen_id () in
      let l1 = bdd_vars t1 in
      let l2 = bdd_vars t2 in
      let l = merge_vars l1 l2 in
      let t = Node (v,t1,t2,i,v::l) in
      NodeHash.add node_hashtbl key t;
      t
    end;;
  
  let bdd_var v = make_node (v, bdd_true, bdd_false);;
  let bdd_nvar v = make_node (v, bdd_false, bdd_true);;


  module Op1Map = Map.Make(struct 
    type t = int 
    let compare v1 v2 = 
      compare (v1:int) v2 
  end);;
  
  let neg t1 = 
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf b -> Leaf (not b)
      | Node (v, t1, t2, id,_) ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t1' = go t1 in
            let t2' = go t2 in
            let t = make_node (v,t1',t2') in
            memo := Op1Map.add id t !memo;
            t
          end
    in go t1;;

  module Op2Map = Map.Make(struct 
    type t = int * int 
    let compare (x1,y1) (x2,y2) = 
      let d = compare (x1:int) x2 in
      if d = 0 then compare (y1:int) y2 else d 
  end);;
  
  let bdd_and t1 t2 =
    let memo = ref Op2Map.empty in
    let rec go t1 t2 = match (t1,t2) with
      | (Leaf b,t2) -> if b then t2 else bdd_false
      | (t1,Leaf b) -> if b then t1 else bdd_false
      | (Node (v1,x1,y1,i1,_), Node (v2,x2,y2,i2,_)) ->
          if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo
          else begin
            let (z,x1,x2,y1,y2) = match (Elt.compare v1 v2) with
              | 0 -> (v1,x1,x2,y1,y2)
              | x when x < 0 -> (v1,x1,t2,y1,t2)
              | _ -> (v2,t1,x2,t1,y2)
            in 
            let t1' = go x1 x2 in
            let t2' = go y1 y2 in
            let t = 
              if node_id t1' = node_id t2' then t1'
              else make_node (z,t1',t2') in
            memo := Op2Map.add (i1,i2) t !memo;
            t
          end
    in go t1 t2;;

  let bdd_or t1 t2 =
    let memo = ref Op2Map.empty in
    let rec go t1 t2 = match (t1,t2) with
      | (Leaf b,t2) -> if b then bdd_true else t2
      | (t1,Leaf b) -> if b then bdd_true else t1
      | (Node (v1,x1,y1,i1,_), Node (v2,x2,y2,i2,_)) ->
          if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo
          else begin
            let (z,x1,x2,y1,y2) = match (Elt.compare v1 v2) with
              | 0 -> (v1,x1,x2,y1,y2)
              | x when x < 0 -> (v1,x1,t2,y1,t2)
              | _ -> (v2,t1,x2,t1,y2)
            in 
            let t1' = go x1 x2 in
            let t2' = go y1 y2 in
            let t = 
              if node_id t1' = node_id t2' then t1'
              else make_node (z,t1',t2') in
            memo := Op2Map.add (i1,i2) t !memo;
            t
          end
    in go t1 t2;;

  let imp t1 t2 = bdd_or (neg t1) t2;;
  let bdd_andl tl = List.fold_left bdd_and bdd_true tl;;
  let bdd_orl tl = List.fold_left bdd_or bdd_false tl;;
  let drop_while p l =
    let rec go = function
      | x::xs when p x -> go xs
      | xs -> xs
    in go l;;
  
  let exists_vl vl t =
    let vl = List.sort Elt.compare vl in
    let memo = ref Op1Map.empty in
    let rec go vl = function
      | Leaf b -> Leaf b
      | Node (v, t1, t2, id, _) as t ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t = match (drop_while (fun x -> Elt.compare x v < 0) vl) with
              | [] -> t
              | x::vl when Elt.compare x v = 0 -> 
                let t1' = go vl t1 in
                let t2' = go vl t2 in
                bdd_or t1' t2'
              | vl -> 
                let t1' = go vl t1 in
                let t2' = go vl t2 in
                if node_id t1' = node_id t2' then t1'
                else make_node (v,t1',t2')
            in
            memo := Op1Map.add id t !memo;
            t
          end
    in go vl t;;

  let forall_vl vl t =
    let vl = List.sort Elt.compare vl in
    let memo = ref Op1Map.empty in
    let rec go vl = function
      | Leaf b -> Leaf b
      | Node (v, t1, t2, id, _) as t ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t = match (drop_while (fun x -> Elt.compare x v < 0) vl) with
              | [] -> t
              | x::vl when Elt.compare x v = 0 -> 
                  let t1' = go vl t1 in
                  let t2' = go vl t2 in
                  bdd_and t1' t2'
              | vl -> 
                  let t1' = go vl t1 in
                  let t2' = go vl t2 in
                  if node_id t1' = node_id t2' then t1'
                  else make_node (v,t1',t2')
            in
            memo := Op1Map.add id t !memo;
            t
          end
    in go vl t;;

  let exists v t = exists_vl [v] t;;
  let forall v t = forall_vl [v] t;;
  
  let imp_and_exists tau x tau1 =
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf b -> Leaf b
      | Node (v, t1, t2, id, _) as t ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t =
              let d = Elt.compare v x in
              if d > 0 then t 
              else if d < 0 then
                let t1' = go t1 in
                let t2' = go t2 in
                if node_id t1' = node_id t2' then t1'
                else make_node (v,t1',t2')
              else
                bdd_or (bdd_and t1 tau1) t2
            in
            memo := Op1Map.add id t !memo;
            t
          end
    in go tau;;

  module Op1Set = Set.Make(struct 
    type t = int 
    let compare x y = compare (x:int) y 
  end);;

  let size t = 
    let memo = ref Op1Set.empty in
    let rec go = function
      | Leaf _ -> ()
      | Node(_,t1,t2,id,_) -> 
          if Op1Set.mem id !memo then ()
          else begin
            memo := Op1Set.add id !memo;
            go t1;
            go t2
          end
    in
    go t;
    Op1Set.cardinal !memo;;

  let zdd_size = size;;

  let sorted vl =
    let rec go = function
      [] -> true
      | [_] -> true
      | x::y::l when Elt.compare x y < 0 -> go (y::l)
      |_ -> false
    in go vl;;


  let restrict_sorted t vl =
    let memo = ref Op1Map.empty in
    assert (sorted (List.map (function POS v | NEG v -> v) vl));
    let rec go vl = function
      | Leaf b -> Leaf b
      | Node (v, t1, t2, id, _) as t ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t = match (drop_while (function | POS x | NEG x -> Elt.compare x v < 0) vl) with
              | [] -> t
              | (POS x)::vl when Elt.compare x v = 0 -> go vl t1
              | (NEG x)::vl when Elt.compare x v = 0 -> go vl t2
              | vl ->
                  let t1' = go vl t1 in
                  let t2' = go vl t2 in
                  if node_id t1' = node_id t2' then t1'
                  else make_node (v,t1',t2')
            in
            memo := Op1Map.add id t !memo;
            t
          end
    in go vl t;;

  let equiv t1 t2 = node_id t1 = node_id t2;;

  let cata f g t =
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf b -> g b
      | Node (v,t1,t2,id,_) ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let x1 = go t1 in
            let x2 = go t2 in
            let x = f v x1 x2 in
            memo := Op1Map.add id x !memo;
            x
          end
    in go t;;


            
  let sat_min t =
    let rec go acc = function
      | Leaf(true) ->  Some(acc)
      | Leaf(false) -> None
      | Node(v,t1,t2,_,_) -> 
          match go acc t2 with
            | None -> go (v::acc) t1
            | res -> res
    in go [] t;;

  let sat_min_while p t =
    let rec go tvs fvs = function
      | Leaf(false) -> None
      | Node(v,t1,t2,_,_) when p v ->
          begin match go tvs (v::fvs) t2 with
            | None -> go (v::tvs) fvs t1
            | res  -> res
          end
      | t -> Some (tvs,fvs,t)
    in go [] [] t;;


  let print_as_dot t label =
    let module S = Op1Set in
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
        | Node(v,t1,t2,_,_) ->
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

  let register_bdd bdd =
    let rec go = function
      | Leaf _ -> ()
      | Node (v,t1,t2,i,_) as t ->
          let i1 = node_id t1 in
          let i2 = node_id t2 in
          let key = (v,i1,i2) in
          if NodeHash.mem node_hashtbl key then ()
          else begin
            go t1;
            go t2;
            NodeHash.add node_hashtbl key t
          end
    in go bdd;;

  let run_gc bdds = 
    NodeHash.clear node_hashtbl;
    List.iter register_bdd bdds;;

  let rec zdd_diff t1 t2 = 
    let memo = ref Op2Map.empty in
    let rec go t1 t2 = match (t1,t2) with
      | (Leaf false,_) -> Leaf false
      | (t1,Leaf false) -> t1
      | (t1,t2) when node_id t1 = node_id t2 -> Leaf false
      | (Leaf true,_) -> Leaf true
      | (Node (v1,x1,y1,i1,_),Leaf true) -> 
          let i2 = node_id t2 in
          if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo else
            let t = make_node_zdd (v1,x1,go y1 t2) in begin
              memo := Op2Map.add (i1,i2) t !memo;
              t
            end
      | (Node (v1,x1,y1,i1,_), Node (v2,x2,y2,i2,_)) -> 
          if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo
          else begin
            let t = match (Elt.compare v1 v2) with
              | 0 -> 
                  let t1 = go x1 x2 in
                  let t2 = go y1 y2 in
                  make_node_zdd (v1,t1,t2)
              | x when x < 0 -> 
                  let t1 = x1 in
                  let t2 = go y1 t2 in
                  make_node_zdd (v1,t1,t2)
              | _ -> go t1 y2
            in
            memo := Op2Map.add (i1,i2) t !memo;
            t
          end
    in go t1 t2;;
    
  let prime_implicants bdd = 
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf b -> Leaf b
      | Node (v,t1,t2,id,_) ->
          if Op1Map.mem id !memo then Op1Map.find id !memo
          else begin
            let t1 = go t1 in
            let t2 = go t2 in
            let t1 = zdd_diff t1 t2 in
            let t  = make_node_zdd (v,t1,t2) in
            memo := Op1Map.add id t !memo;
            t
          end
    in go bdd;;

  let zdd_union t1 t2 =
    let memo = ref Op2Map.empty in
    let rec go t1 t2 = 
      let i1 = node_id t1 in
      let i2 = node_id t2 in
      if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo else
        begin
          let t = match (t1,t2) with
            | (Leaf false,_) -> t2
            | (_,Leaf false) -> t1
            | (t1,t2) when i1 = i2 -> t1
            | (Leaf true,Leaf true) -> t1
            | (Leaf true,Node (v,x,y,_,_))
            | (Node (v,x,y,_,_),Leaf true) -> 
                let t1 = x in
                let t2 = go (Leaf true) y in
                make_node_zdd (v,t1,t2)
            | (Node (v1,x1,y1,_,_),Node (v2,x2,y2,_,_)) ->
                begin match Elt.compare v1 v2 with
                  | 0 ->
                      let t1 = go x1 x2 in
                      let t2 = go y1 y2 in
                      make_node_zdd (v1,t1,t2)
                  | x when x < 0 ->
                      let t1 = x1 in
                      let t2 = go y1 t2 in
                      make_node_zdd (v1,t1,t2)
                  | _ ->
                      let t1 = x2 in
                      let t2 = go t1 y2 in
                      make_node_zdd (v2,t1,t2)
                end
          in
          memo := Op2Map.add (i1,i2) t !memo;
          t
        end
    in go t1 t2;;


  let zdd_elim t f =
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf b -> Leaf b
      | Node (v,t1,t2,id,_) ->
          if Op1Map.mem id !memo then Op1Map.find id !memo 
          else begin
            let t = if f v then 
              let t1 = go t1 in
              let t2 = go t2 in
              zdd_union t1 t2 
            else 
              let t1 = go t1 in
              let t2 = go t2 in
              make_node_zdd (v,t1,t2) in
            memo := Op1Map.add id t !memo;
            t
          end
    in go t;;
            

  let zdd_enum t = 
    let memo = ref Op1Map.empty in
    let rec go = function
      | Leaf true -> [[]]
      | Leaf false -> []
      | Node (v,t1,t2,id,_) ->
          if Op1Map.mem id !memo then Op1Map.find id !memo 
          else begin
            let l1 = go t1 in
            let l2 = go t2 in
            let l = List.map (fun vs -> v::vs) l1 @ l2 in
            memo := Op1Map.add id l !memo;
            l
          end
    in go t;;


end;;
