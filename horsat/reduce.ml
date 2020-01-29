open Grammar;;
open Utilities;;

exception Empty
let queue =
  (ref [], ref [])
let enqueue item =
  let (r1,r2) = queue in
   (r2 := item::(!r2))

let dequeue() =
  let (r1,r2) = queue in
    match !r1 with
      [] -> let  l = List.rev_append !r2 [] in
              (match l with [] -> raise Empty
                       | x::l' -> (r1 := l'; r2 := []; x))
    | x::l' -> (r1 := l'; x)

let headtab = Hashtbl.create 1000
let invheadtab = Hashtbl.create 1000

let register_invheadtab nt (f,heads) =
  try
    let l = Hashtbl.find invheadtab nt in
      Hashtbl.replace invheadtab nt (merge_and_unify compare [(f,heads)] l)
   with Not_found -> 
     Hashtbl.add invheadtab nt [(f,heads)]

let lookup_inv_headtab nt =
  try
    Hashtbl.find invheadtab nt
  with Not_found -> []

let register_args f heads =
 let _ = 
   try
    let l = Hashtbl.find headtab f in
      Hashtbl.replace headtab f (merge_and_unify compare [heads] l)
   with Not_found -> 
     Hashtbl.add headtab f [heads]
 in
 let nts = 
    List.fold_left (fun nts' h ->
      match h with (NT(f),_) -> merge_and_unify compare [f] nts'
       | _ -> nts') [] heads
 in
   List.iter (fun nt -> register_invheadtab nt (f,heads)) nts


     

let get_allheads() =
  let r = ref [] in
  let _ = Hashtbl.iter
    (fun f headss ->
       r :=
       List.rev_append (List.map (fun heads -> (f,heads)) headss) !r)
    headtab
  in !r

let get_nts_heads nts =
  let nts' = List.sort (fun x y -> -(compare x y)) nts in
  List.fold_left
  (fun todo f ->
    try 
      let headss = Hashtbl.find headtab f in
        (List.map (fun heads -> (f,heads)) headss)@todo
    with Not_found -> todo)
  [] nts'

let get_head term =
  let (h,terms) = decompose_term term in (h,List.length terms)

let redonestep g =
  let term = dequeue() in
  let (h, terms) = decompose_term term in
    match h with
      T(_) -> 
        List.iter enqueue terms
    | NT(f) ->
        let heads = List.map get_head terms in
        let _ = register_args f heads in
        let (vars,body) = get_def f g in
        let subst = List.combine vars terms in
          enqueue (subst_term subst body)
    | _ -> assert false

let print_heads heads =
  List.iter 
  (fun (h,k) -> (print_term h; print_string ("::"^(string_of_int k)^" ")))
  heads

let print_headtab() =
  Hashtbl.iter 
  (fun f headss -> 
    (print_string (f^":\n");
     List.iter 
      (fun heads -> 
        (print_string "  ";print_heads heads; print_string "\n"))
      headss))
  headtab

let print_invheadtab() =
 (print_string "inverse head table:\n==================\n";
  Hashtbl.iter 
  (fun f headss -> 
    (print_string (f^":\n");
     List.iter 
      (fun (nt,heads) -> 
        (print_string ("  "^nt^"  ");print_heads heads; print_string "\n"))
      headss))
  invheadtab)

let rec reduce g count =
  if count = 0 then ()
  else
    try 
      (redonestep g; reduce g (count-1))
    with Empty -> ()

