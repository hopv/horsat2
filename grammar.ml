open Utilities

exception Fatal of string

type nameNT = int (** names of non-terminal symbols; they are just integers **)
type nameT = string  (** names of terminal symbols **)
type nameV = nameNT * int (* pair of the non-terminal and the variable index *)
type term = NT of nameNT | T of nameT | Var of nameV | App of term * term
type kind = O | Kfun of kind * kind
type state_id = int
type ity_id = int
type ity = ItyQ of state_id | ItyFun of ity_id * ty * ity
and ty = ity list

type nonterminals = (string * kind) array 
  (* store the original name of each non-terminal and its kind *)
type varinfo = string array array (* store the original name of each variable *)
type terminals = (nameT * int) list  (* -1 if the arity is unknown *)

type rule = (int * term)  (* int: the number of formal parameters *)
type rules = rule array 

type gram = {nt: nonterminals; t: terminals; vinfo: varinfo; r: rules; s: nameNT}
let empty_grammar = {nt=[||];t=[];vinfo=[||]; r=[||];s=0}

let gram = ref empty_grammar;; (* stored here once the grammar has been read  *)

exception UndefinedNonterminal of string
exception DuplicatedNonterminal of string
exception InconsistentArity of nameT


let get_def (f: nameNT) (g:gram) = 
  g.r.(f) 

let lookup_rule (f: nameNT) =
  get_def f (!gram)

let max_nt() = Array.length (!gram.r)

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

let rec mk_app h terms =
  match terms with
   [] -> h
 | t::terms' -> mk_app (App(h,t)) terms'

let rec occur_nt_in_term nt term =
  match term with
    NT(f) -> nt=f
  | T(_) -> false
  | Var(_) -> false
  | App(t1,t2) -> (occur_nt_in_term nt t1) ||(occur_nt_in_term nt t2)

let rec vars_in_term term = 
  match term with
    NT _ -> []
  | T _ -> []
  | Var(v) -> [v]
  | App(t1,t2) ->
     merge_and_unify compare (vars_in_term t1)  (vars_in_term t2) 

let rec vars_in_terms terms =
  match terms with
    [] -> []
  | t::terms' -> merge_and_unify compare (vars_in_term t) (vars_in_terms terms')

let rec headvars_in_term term =
  match term with
    NT _ -> []
  | T _ -> []
  | Var(_) -> []
  | App(Var(x),t2) -> merge_and_unify compare [x] (headvars_in_term t2)
  | App(t1,t2) -> merge_and_unify compare (headvars_in_term t1)
                                          (headvars_in_term t2)
      
let rec nt_in_term term = 
  match term with
    NT(x) -> [x]
  | T _ -> []
  | Var _ -> []
  | App(t1,t2) ->
     merge_and_unify compare (nt_in_term t1)  (nt_in_term t2) 

let nt_in_rule (f, (vars, term)) =
  nt_in_term term

let rec nt_in_rules rules =
 match rules with
   [] -> []
  |r::rules' ->
    merge_and_unify compare (nt_in_rule r) (nt_in_rules rules')

let rec terminals_in_term term =
  match term with
    NT(_) -> []
  | T a -> [a]
  | Var _ -> []
  | App(t1,t2) ->
     merge_and_unify compare (terminals_in_term t1)  (terminals_in_term t2) 
  
let rec terminals_in_rules rules =
  Array.fold_left 
  (fun terminals (_,body) ->
          merge_and_unify compare (terminals_in_term body) terminals)
  [] rules

let rec mk_depend g =
  let n = Array.length g.nt in
  let deptab = Array.make n [] in
   for i=0 to n-1 do
      deptab.(i) <- (let (vars,body) = get_def i g in nt_in_term body)
   done;
   deptab

let update_arity alpha =
  let g = !gram in
   gram := {nt = g.nt; t = alpha; vinfo=g.vinfo; r=g.r; s=g.s}

let arity_of_t a = List.assoc a (!gram).t

let arity_of_nt f =
  let (arity,_) = (!gram).r.(f) in arity

let name_of_nt f =
  let (s,_) = (!gram).nt.(f) in s

let name_of_var x =
  let (f,i) = x in
     if f<0 || f>=Array.length (!gram).vinfo (* variable added by normalization *)
     then ("v"^(string_of_int i))
     else if i>= Array.length (!gram).vinfo.(f) then
         ("v"^(string_of_int i))
     else
       (!gram).vinfo.(f).(i)

let rec print_term term =
  match term with
    NT(f) -> print_string (name_of_nt f)
  | T(a) -> print_string a
  | Var(x) -> print_string (name_of_var x)
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
  let n = Array.length g.r in
  for i=0 to n-1 do 
    let (arity,body) =  g.r.(i) in
       (print_string ((name_of_nt i)^" ");
        for j=0 to arity-1 do
        print_string ((name_of_var (i,j))^" ")
        done;
        print_string "-> ";
        print_term body;
        print_string "\n")
  done

let rec arity2kind k =
  if k=0 then O else Kfun(O,arity2kind(k-1))
   
let rec size_of_term t =
  match t with
    (NT _ | T _ | Var _) -> 1
  | App(t1,t2) -> (size_of_term t1)+(size_of_term t2)

let rec size_of_rule r = 
  let (_,t) =  r in size_of_term t
      
let rec size_of g =
   Array.fold_left (fun n -> fun r -> n+(size_of_rule r)) 0 g.r

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
     assert false (* raise (UndefinedNonterminal (name_of_nt x)) *)

let find_sc f scc =
  let scc' = List.filter (fun x-> List.mem f x) scc in
    match scc' with
       [] -> assert false
    |  sc::_ -> sc

let register_recfun dmap g =
   let nt = fromto 0 (Array.length g.nt -1) in
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
          List.iter (fun (f,_)-> print_string ((name_of_nt f)^" ")) l;
          print_string "\n")
      )


let rec arity_of_kind = function
  | O -> 0
  | Kfun (k1,k2) -> 1 + arity_of_kind k2

