open Utilities

exception Fatal of string

type nameNT = string (** names of non-terminal symbols **)
type nameT = string  (** names of terminal symbols **)
type nameV = string
type term = NT of nameNT | T of nameT | Var of nameV | App of term * term
type kind = O | Kfun of kind * kind
type state = string
type ity = ItyQ of state | ItyFun of ty * ity
and ty = ity list

type nonterminals = (nameNT * kind) list
type terminals = (nameT * kind) list

type rule = nameNT * (nameV list * term)
type rules = rule list

type gram = {nt: nonterminals; t: terminals; r: rules; s: nameNT}
let empty_grammar = {nt=[];t=[];r=[];s="S"}

exception UndefinedNonterminal of nameNT
let get_def (f: nameNT) (g:gram) = 
   try
     List.assoc f (g.r)
   with Not_found -> raise (UndefinedNonterminal f)

let rec decompose_term t =
  match t with
   (NT(_)|T(_)|Var(_)) -> (t, [])
 | App(t1,t2) ->
     let (h,ts)=decompose_term t1 in (h,ts@[t2])

let head term =
  let (h,_) = decompose_term term in h

let rec compose_term h terms =
  match terms with
    [] -> h
  | t::terms' -> compose_term (App(h,t)) terms'

let rec occur_nt_in_term nt term =
  match term with
    NT(f) -> nt=f
  | T(_) -> false
  | Var(_) -> false
  | App(t1,t2) -> (occur_nt_in_term nt t1) ||(occur_nt_in_term nt t2)

let rec mk_depend g =
  let sorted_rules = List.sort (fun (f1,_) -> fun (f2, _) -> compare f1 f2) g.r in
  let nts = List.map fst g.nt in
    List.map (fun nt-> (nt, List.map fst 
                       (List.filter 
                         (fun (f,(_,body)) -> occur_nt_in_term nt body)
                         sorted_rules)))
              nts

let rec print_term term =
  match term with
    NT(f) -> print_string f
  | T(a) -> print_string a
  | Var(x) -> print_string x
  | App(t1,t2) -> (print_string "(";print_term t1;print_string " ";
                  print_term t2;print_string ")")

let rec subst_term s term =
  match term with
    (T(_)|NT(_)) -> term
  | Var(x) ->
     ( try 
        List.assoc x s
      with Not_found -> term)
  | App(t1,t2) -> App(subst_term s t1, subst_term s t2)

let rec subst_nt_in_term s term =
  match term with
    (Var(_)|T(_)) -> term
  | NT(x) ->
     ( try 
        List.assoc x s
      with Not_found -> term)
  | App(t1,t2) -> App(subst_nt_in_term s t1, subst_nt_in_term s t2)

let print_gram g =
  List.iter (fun (nt,(vars,body)) ->
     (print_string (nt^" ");
      List.iter (fun v-> print_string (v^" ")) vars;
      print_string "-> ";
      print_term body;
      print_string "\n"))
  g.r

(* normalize grammars so that each terminal a occurs only in the form
   A x1 ... xk -> a x1 ... xk
 *)
let tname2ntname a = "$"^a
let rec arity2kind k =
  if k=0 then O else Kfun(O,arity2kind(k-1))
let rec normalize_term term alpha =
  match term with
    T(a) -> (try 
              let _ = List.assoc a alpha in NT(tname2ntname a)
             with Not_found -> term
             )
  | App(t1,t2) -> App(normalize_term t1 alpha, normalize_term t2 alpha)
  | _ -> term

let mk_Tvars k nt =
  List.map (fun i-> "x"^(string_of_int i)^"@"^nt)
           (fromto 1 (k+1))
let normalize g alpha =
  let rules1 = List.map 
               (fun (a,k) ->
                 let nt = tname2ntname(a) in
                 let vars = mk_Tvars k nt in 
                 let body = compose_term (T(a)) (List.map (fun v->Var(v)) vars) in
                   (nt, (vars,body)))
               alpha
  in
  let nonterminals1 = 
      List.map (fun (a,k) -> (tname2ntname(a), arity2kind(k))) alpha
  in                      
  let rules0 = List.map (fun (nt,(vars,body)) ->
                          (nt,(vars, normalize_term body alpha))) g.r
  in
    {nt=(g.nt)@nonterminals1;
     t = g.t;
     r = rules1@rules0;
     s = g.s}
   
let rec size_of_term t =
  match t with
    (NT _ | T _ | Var _) -> 1
  | App(t1,t2) -> (size_of_term t1)+(size_of_term t2)

let rec size_of_rule (_,(_,t)) = size_of_term t
      
let rec size_of g =
   List.fold_left (fun n -> fun r -> n+(size_of_rule r)) 0 g.r


(* find and register recursive functions *)
(* (f, [g1,...,gk]) in dmap means that f occurs in g1,...,gk *)

let recfuntab = Hashtbl.create 1000
let scclist = ref []

let reset_recfuntab() =
  Hashtbl.clear recfuntab; scclist := []

let is_recfun f = 
   if !Flags.allfun then true
   else Hashtbl.mem recfuntab f
let find_dep x dmap =
  try
    List.assoc x dmap
  with Not_found ->
     raise (UndefinedNonterminal x)

let find_sc f scc =
  let scc' = List.filter (fun x-> List.mem f x) scc in
    match scc' with
       [] -> assert false
    |  sc::_ -> sc

let register_recfun dmap g =
   let nt = List.map fst g.nt in
   let graph = List.flatten 
               (List.map (fun (f,l) -> List.map (fun g->(g,f)) l) dmap)
   in
   let scc = Scc.compute_scc graph in
   let singletons = List.map List.hd
                    (List.filter list_singleton scc) in
   let rec1 = (* find self-recursive non-terminals *)
               List.filter 
               (fun x -> List.mem x (find_dep x dmap)) singletons 
   in
   let cycles1 = List.map (fun x -> [x]) rec1 in
   let cycles2 = List.filter (fun sc -> List.length sc >1) scc in
   let _ = (scclist := cycles1@cycles2) in
   let rec2 = List.filter (fun x -> not(List.mem x singletons)) nt in
   let rec2' = List.filter
             (fun f -> List.length (find_dep f dmap)>1)
              rec2
   in
     (
      List.iter (fun f -> Hashtbl.add recfuntab f (find_sc f scc)) rec1;
      List.iter (fun f -> Hashtbl.add recfuntab f (find_sc f scc)) rec2';
      if !Flags.debugging then
        (print_string "Recursive functions\n";
         let l = hash2list recfuntab in
          List.iter (fun (f,_)-> print_string (f^" ")) l;
          print_string "\n")
      )

let unfoldedname f = "#"^f
let unfoldedname2 f = "##"^f

let unfold_rule rule scc =
  let (f,(vars,body)) = rule in
  let f1 = unfoldedname f in
  let subst1 = List.map (fun f -> (f,NT(unfoldedname f))) scc in
  let body1 = subst_nt_in_term subst1 body in
  let vars1 = List.map unfoldedname vars in
    if is_recfun f then
      let body0 = App(App(NT(tname2ntname "#or"), body),body1) in
      let body2 = T("#stop") in
        [(f,(vars,body0)); (f1,(vars1,body2))]
    else
      let vs1 = List.map (fun x->(x,Var(unfoldedname x))) vars in
      let body1' = subst_term vs1 body1 in
       [(f,(vars,body)); (f1,(vars1,body1'))]

let unfold_rule2 rule scc =
  let (f,(vars,body)) = rule in
  let f1 = unfoldedname f in
  let f2 = unfoldedname2 f in 
  let subst1 = List.map (fun f -> (f,NT(unfoldedname f))) scc in
  let subst2 = List.map (fun f -> (f,NT(unfoldedname2 f))) scc in 
  let body1 = subst_nt_in_term subst1 body in
  let body2 = subst_nt_in_term subst2 body in
  let vars1 = List.map unfoldedname vars in
  let vars2 = List.map unfoldedname2 vars in
    if is_recfun f then
      let body0 = App(App(NT(tname2ntname "#or"), body),body1) in
      let vs1 = List.map (fun x->(x,Var(unfoldedname x))) vars in
      let body2' = subst_term vs1 body2 in
      let body3 = T("#stop") in
        [(f,(vars,body0)); (f1,(vars1,body2')); (f2,(vars2,body3))]
    else
      let vs1 = List.map (fun x->(x,Var(unfoldedname x))) vars in
      let vs2 = List.map (fun x->(x,Var(unfoldedname2 x))) vars in
      let body1' = subst_term vs1 body1 in
      let body2' = subst_term vs2 body2 in
       [(f,(vars,body)); (f1,(vars1,body1'));(f2,(vars2,body2'))]
(*
  let subst1 = List.map (fun f -> (f,NT(unfoldedname f))) scc in
  let body1 = subst_nt_in_term subst1 body in
  let vars1 = List.map unfoldedname vars in
  let vs1 = List.map (fun x->(x,Var(unfoldedname x))) vars in
  let vs2 = List.map (fun x->(x,Var(unfoldedname2 x))) vars in
  let body2' = subst_term vs1 body2 in
  let body2'' = subst_term vs2 body2 in
    [(f,(vars,body1)); (f1,(vars1,body2')); (f2, (vars2,body2''))]
*)

let unfold_rules g scc =
  List.fold_left
  (fun rules f -> 
     (unfold_rule2 (f,get_def f g) scc)@rules)
  [] scc

let unfold g =
(*
  let sccs = !scclist in
*)
  let sccs = [List.filter (fun f -> not(String.sub f 0 1="$"))
              (List.map fst g.nt)] in
  let nts = List.fold_left
            (fun nts scc ->
              (List.map (fun f-> (unfoldedname f, O)) scc)@
               (List.map (fun f-> (unfoldedname2 f, O)) scc)@ nts)
              (* kind is dummy *)
            g.nt sccs
  in
  let rules = List.fold_left
              (fun rules scc ->
               let rules1 = 
                List.filter (fun (f,_) -> not(List.mem f scc)) rules in
               (unfold_rules g scc)@rules1)
              g.r sccs
  in
    {nt=nts; t=g.t; r=rules; s=g.s}

let rec print_ity ity =
  match ity with
   ItyQ q -> print_string q
 | ItyFun(ty,ity) ->
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

