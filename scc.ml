(**** Copyright 2004 (see README and COPYING for details in the top directory) ***)
exception Impossible
exception Fatal of string

type node = int;;
type graph = (node* (int ref * int ref * node list ref)) list;;

let get_node (g:graph) x = List.assoc x g;;
let get_nexts g x = 
   let (_,_,r) = (get_node g x) in !r
let get_dfsnum (g:graph) x =
   let (r,_,_) = (get_node g x) in
      !r;;
let get_low (g:graph) x =
   let (_,r,_) = (get_node g x) in
      !r;;
let set_dfsnum (g:graph) x n =
   let (r,_,_) = (get_node g x) in
      r := n;;
let set_low (g:graph) x n =
   let (_,r,_) = (get_node g x) in
      r:= n;;

type edges = (node * node) list;;

let dfsnum = ref 0;;
let init_dfsnum() = (dfsnum := 0);;
let inc_dfsnum() = (dfsnum := !dfsnum+1);;
let visited = ref [];;
let add_visited v = (visited := v::!visited);;

let rec split_list_at x l =
  match l with
    [] -> raise Impossible
  | y::l' -> 
        if x=y then ([x],l') 
        else 
          let (l1,l2)=split_list_at x l' in
             (y::l1, l2);;

let take_from_visited(x) =
   let (l1,l2) = split_list_at x !visited in
   let _ = visited := l2 in
     l1;;
let rec init_graph (e:edges) =
  match e with
    [] -> []
  | (x,y)::e' ->
      let g' =
        let g = init_graph e' in
          try 
            let (_,_,nextr) = List.assoc x g in
               if List.mem y !nextr then g
               else (nextr := y::!nextr; g)
          with
           Not_found -> (x, (ref 0, ref 0, ref [y]))::g in
      try (let _ = List.assoc y g' in g') with
         Not_found -> (y, (ref 0, ref 0, ref []))::g';;

let delete_nodes (g:graph) nodes =
  let g' = List.filter (function (n,_)-> not(List.mem n nodes)) g in
    List.map (function (n,(r1,r2,nexts)) ->
         let l = List.filter (function v->not(List.mem v nodes)) !nexts in
            (n, (r1, r2, ref l))) g';;

let rec visit((g:graph),x,scc) =
(*** let _ = (print_string "visiting ";print_int x;print_newline()) in***)
  let _ = add_visited(x) in
  let _ = set_dfsnum g x !dfsnum in
  let _ = set_low g x !dfsnum in
  let _ = inc_dfsnum() in
  let nexts = get_nexts g x in
  let (g',scc') = 
              visit_next(g, x, nexts,scc) in
    if get_dfsnum g' x = get_low g' x
    then 
      let newscc = take_from_visited(x) in
      let newg = delete_nodes g' newscc in
        (newg, newscc::scc')
    else
      (g',scc')
and visit_next(g, x, nexts,scc) =
  match nexts with 
   [] -> (g, scc)
 | y::yl ->
     if List.mem_assoc y g then
         if List.mem y !visited then
           (set_low g x (min (get_low g x) (get_dfsnum g y));
            visit_next(g, x, yl, scc))
         else
          let (g', scc') = visit(g, y, scc) in
            (set_low g x (min (get_low g x) (get_low g y));
             visit_next(g', x, yl, scc'))
     else visit_next(g,x,yl,scc);;

let choose_vertex g =
  match g with
    [] -> None
  | (n,_)::_ -> Some(n);;

let rec dfs(g, scc) =
  match choose_vertex(g) with
    Some(x) ->
        let (newg, scc') = visit(g,x,scc) in
           dfs(newg,scc')
  | None -> 
        scc;;

let compute_scc e =
  (visited := [];
   init_dfsnum();
   let g = init_graph(e) in
      dfs(g, []));;

exception Cycle;;

let rec find_cycle((g:graph),visited,x) =
  let nexts = try get_nexts g x with Not_found -> [] in
  let g' = find_cycle_next(g, x, x::visited, nexts) in
    delete_nodes g' [x]
and find_cycle_next(g, x, visited, nexts) =
  match nexts with 
   [] -> g
 | y::yl ->
     if List.mem y visited then
         raise Cycle
     else
        let g' = find_cycle(g, visited, y) in
           find_cycle_next(g', x, visited, yl);;

let rec dfs_cycle(g) =
  match choose_vertex(g) with
    Some(x) ->
        let newg = find_cycle(g,[],x) in
           dfs_cycle(newg)
  | None -> 
        ();;

let check_acyclicity e =
  (init_dfsnum();
   let g = init_graph(e) in
      dfs_cycle(g));;

type cache = Empty | Locked | Computed of node list
type rgraph = (node* (node list ref * cache ref)) list;;

let rec mk_rgraph (e:edges) = 
  match e with
    [] -> []
  | (x,y)::e' ->
      let g' =
        let g = mk_rgraph e' in
          try 
            let (nextr,_) = List.assoc x g in
               if List.mem y !nextr then g
               else (nextr := y::!nextr; g)
          with
           Not_found -> (x, (ref [y], ref Empty))::g in
      try (let _ = List.assoc y g' in g') with
         Not_found -> (y, (ref [], ref Empty))::g';;

let rec compute_rset g n =
  let (nextr, cacher) = List.assoc n g in
    match !cacher with
      Computed(rset) -> Utilities.merge_and_unify compare [n] rset
    | Locked -> raise (Fatal "compute_rset: graph is cyclic")
    | Empty ->
        (cacher := Locked;
         let nll = (List.map (compute_rset g) !nextr) in
         let x = List.fold_left (Utilities.merge_and_unify compare) [] nll in
           (cacher := Computed x; Utilities.merge_and_unify compare [n] x))

         
