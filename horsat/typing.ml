open Utilities;;
open Grammar;;
open Automaton;;

type te = (nameNT * ty) list  (*** type environment for non-terminals ***)
type vte = (nameNT * ty) list  (*** type environment for variables ***)
type cte = (nameT * ty) list (*** type environment for constants ***)

let mode_gfp = ref true
let transduce = ref false
let empty_te = []
let outputml = ref false

let init_te nt =
  Utilities.list2hash (List.map (fun (x,_) -> (x, [])) nt)

let rec string_of_ty ty =
  match ty with
    [] -> "Top"
  | [aty] -> 
         (match aty with
           ItyQ(q) -> q
         | _ -> ("("^(string_of_aty aty)^")")
         )
  | aty::ty' -> 
      ((string_of_ty [aty])^"/\\"^(string_of_ty ty'))
and string_of_aty_parens aty =
  match aty with
     ItyQ(q) -> string_of_aty aty
   | _ -> ("("^(string_of_aty aty)^")")
and string_of_aty aty =
  match aty with
    ItyQ(q) -> q
  | ItyFun(ty, aty) ->
       (string_of_ty ty)^" -> "^(string_of_aty aty)

let rec name_of_aty aty = 
  match aty with
    ItyQ(q) -> q
  | ItyFun(ty, aty) ->
       (string_of_ty ty)^"_"^(string_of_aty aty)

let rec print_ty ty =
  match ty with
    [] -> print_string "Top"
  | [aty] -> 
         (match aty with
           ItyQ(q) -> print_string q
         | _ -> (print_string "("; print_aty aty; print_string ")")
         )
  | aty::ty' -> 
      match aty with
       | _ -> (print_ty [aty]; print_string "/\\"; print_ty ty' )
and print_aty_parens aty =
  match aty with
     ItyQ(q) -> print_aty aty
   | _ -> (print_string "("; print_aty aty; print_string ")")
and print_aty aty =
  match aty with
    ItyQ(q) -> print_string q
  | ItyFun(ty, aty) ->
       (print_ty ty; print_string " -> "; print_aty aty)

let rec output_ty fp ty =
  match ty with
    [] -> output_string fp "Top"
  | [aty] -> 
         (match aty with
           ItyQ(q) -> output_string fp q
         | _ -> (output_string fp "("; output_aty fp aty; output_string fp ")")
         )
  | aty::ty' -> 
      match aty with
       | _ -> (output_ty fp [aty]; output_string fp "/\\"; output_ty fp ty' )
and output_aty_parens fp aty =
  match aty with
     ItyQ(q) -> output_aty fp aty
   | _ -> (output_string fp "("; output_aty fp aty; output_string fp ")")
and output_aty fp aty =
  match aty with
    ItyQ(q) -> output_string fp q
  | ItyFun(ty, aty) ->
       (output_ty fp ty; output_string fp " -> "; output_aty fp aty)

let print_tbinding (f, ty) =
  (print_string (f^" : \n  ");
   List.iter (fun aty -> (print_aty aty; print_string "\n  ")) ty;
   print_string "\n")
  
let print_te te =
  List.iter print_tbinding te

let lookup_te f te =
  try Hashtbl.find te f with Not_found -> raise (Grammar.UndefinedNonterminal f)
let update_te f ty te =
  (Hashtbl.replace te f ty; te)

let size_of_te te =
  List.fold_left 
   (fun n -> fun (_,ty) -> (n+List.length(ty)))
   0
   te

let rec tsize_of_te te =
  List.fold_left 
   (fun n -> fun (_,ty) -> (n+size_of_ty(ty)))
   0
   te
and size_of_ty ty =
  List.fold_left 
   (fun n -> fun aty -> (n+size_of_aty(aty)))
   0
   ty
and size_of_aty aty =
  match aty with
    ItyQ _ -> 1
  | ItyFun(ty1,aty2) -> size_of_ty(ty1) + size_of_aty(aty2)

let size_of_judgment te aty =
  (tsize_of_te te) + (size_of_aty aty)

let singletontype_of_value n = ItyQ(string_of_int n)
let value_of_singletontype aty = 
  match aty with
     ItyQ(q) -> int_of_string q
   | _ -> raise (Fatal "value_of_singletontype")

let rec subtype aty1 aty2 =
  match (aty1,aty2) with
    (ItyQ(q1), ItyQ(q2)) -> q1=q2
  | (ItyFun(ty1,aty11), ItyFun(ty2, aty21)) ->
      (subtype aty11 aty21) 
      && (List.for_all (fun aty12 -> List.exists (fun aty22 -> subtype aty22 aty12) ty2) ty1)
  | _ -> false

let rec filter_suptype ty result =
 match ty with
   [] -> result
 | aty::ty' ->
     if (List.exists (fun aty2 -> subtype aty2 aty) result)
        ||
        (List.exists (fun aty2 -> subtype aty2 aty) ty')
     then filter_suptype ty' result
     else filter_suptype ty' (aty::result)

let rec subtype_normalize_aty aty =
  match aty with
    ItyFun(ty1,aty2) ->
       let aty2' = subtype_normalize_aty aty2 in
       let ty1' = List.map subtype_normalize_aty ty1 in
       let ty1'' = filter_suptype ty1' [] in
       let ty1''' = List.sort compare ty1'' in
         ItyFun(ty1''', aty2')
  | _ -> aty

let add_te te telist =
  let _ =
    List.iter
      (fun (f, atys) ->
        let atys1 = lookup_te f te in
        let atys1' = List.filter (fun aty1 -> not(List.exists
                           (fun aty -> subtype aty aty1) atys)) atys1 in
        let atys1'' = merge_and_unify compare atys atys1' in 
        let _ = update_te f atys1'' te in
         ())
    telist
  in
    te

let filter_valid_types te nte =
  Hashtbl.iter
   (fun f atys -> 
     let atys1 = lookup_te f nte in
      Hashtbl.replace te f
       (List.filter (fun aty -> not(List.exists 
                           (fun aty1 -> subtype aty1 aty) atys1)) atys))
    te

let rec get_rty n aty =
  if n=0 then aty
  else
    match aty with
      ItyFun(_,aty') -> get_rty (n-1) aty'
    | _ -> assert false

let rec eqrty n rty aty =
  if n=0 then subtype aty rty
  else 
    match aty with
      ItyFun(_,aty') -> eqrty (n-1) rty aty'
    | _ -> false

let ret_of_funty aty =
  match aty with
    ItyFun(_,aty')->aty'
  | _ -> assert false

let type_of_head head n rty te nte vte cte =
  match head with
    NT(f) -> 
          ( try
             let ty1 = List.filter (eqrty n rty) (lookup_te f nte) in
             let ty2 = List.filter (eqrty n rty) (lookup_te f te) in
               List.rev_append ty1 ty2
           with Not_found -> assert false)
  | T(a) -> 
         (try List.filter (eqrty n rty) (List.assoc a cte) 
         with Not_found -> assert false)
  | Var(v) -> 
        ( try List.filter (eqrty n rty) (List.assoc v vte) 
         with Not_found -> (print_string (v^" not found in: \n");
                            print_te vte; assert false))
  | App(t1,t2) -> assert false

let typetab = Hashtbl.create 1000
(**
let register_typetab term rty vte b =
  Hashtbl.add typetab (term,rty,vte) b
let lookup_typetab term rty vte = (* raise Not_found *)
  Hashtbl.find typetab (term,rty,vte) 
**)
let register_typetab term rty b =
  Hashtbl.add typetab (term,rty) b
let lookup_typetab term rty = (* raise Not_found *)
  Hashtbl.find typetab (term,rty) 

let reset_typetab() = Hashtbl.clear typetab

let rec has_type term rty te nte vte cte =
  let (h,terms) = decompose_term term in
  if terms = [] then has_type_sub h terms rty te nte vte cte 
  else
   try 
     lookup_typetab term rty 
   with
    Not_found ->
      let b = has_type_sub h terms rty te nte vte cte in
        (register_typetab term rty b; b)

and has_type_sub h terms rty te nte vte cte = 
  let ty = type_of_head h (List.length terms) rty te nte vte cte in
    List.exists (fun aty -> check_args terms aty te nte vte cte) ty

and check_args terms aty te nte vte cte =
  match terms with
    [] -> true
  | t::terms' ->
     match aty with
       ItyFun(ty1,aty2) ->
         (List.for_all (fun aty1->has_type t aty1 te nte vte cte) ty1)
         && check_args terms' aty2 te nte vte cte
     | _ -> false

let merge_ty ty1 ty2 = merge_and_unify compare ty1 ty2
let rec merge_te te1 te2 = 
  match (te1,te2) with
    ([], _) -> te2
  | (_, []) -> te1
  | ((x,ty1)::te1', (y,ty2)::te2') ->
      let c = compare x y in
      if c=0 then (x,merge_ty ty1 ty2)::(merge_te te1' te2')
      else if c<0 then (x,ty1)::(merge_te te1' te2)
      else (y,ty2)::(merge_te te1 te2')

let rec mk_vte vars at =
    match at with
      ItyQ(q) -> 
        if vars=[] then 
           ([], ItyQ(q))
        else assert false 
    | ItyFun(ty, aty1) ->
       (  match vars with
            [] -> ([], at)
        | v::vars' -> 
             let (ve1, rt1) = mk_vte vars' aty1 in
               ((v, ty)::ve1, rt1)
       )

(*** checks whether the body of f has type at ***)
let rec check_aty (f: nameNT) at te nte cte g =
  let _ = reset_typetab() in
  let (vars, body) = get_def f g in
  let (vte, rang_ty) =  mk_vte vars at in
  try
    has_type body rang_ty te nte vte cte 
  with Not_found -> assert false

let rec gfp te cte nte unchecked dmap g =
  match unchecked with
    [] -> ()
  | f::unchecked' ->
     let fty = 
      try
        lookup_te f te 
        with Not_found -> assert false
     in
     let fty' = List.filter (fun aty -> check_aty f aty te nte cte g) fty in
       if List.length fty=List.length fty' then
         gfp te cte nte unchecked' dmap g
       else
         let to_be_checked = List.assoc f dmap in
         let te' = update_te f fty' te in
           gfp te' cte nte (merge_and_unify compare unchecked' to_be_checked) dmap g

let rec lfp new_te te cte nte unchecked dmap g =
  match unchecked with
    [] -> ()
  | f::unchecked' ->
     let fty = lookup_te f te in
     let (fty',fty3) = list_filter2 (fun aty -> check_aty f aty new_te nte cte g) fty in
       if fty'=[] then
         lfp new_te te cte nte unchecked' dmap g
       else
         let to_be_checked = List.assoc f dmap in
         let fty1 = lookup_te f new_te in
         let fty2 = merge_and_unify compare fty1 fty' in
         let te' = update_te f fty3 te in
         let new_te' = update_te f fty2 new_te in
           lfp new_te' te' cte nte (merge_and_unify compare unchecked' to_be_checked) dmap g

let compute_te te cte nte dmap g =
  let unchecked = List.map fst (g.nt) in
    if !mode_gfp then
      (gfp te cte nte unchecked dmap g; te)
    else
      let new_te = init_te (g.nt ) in
        (lfp new_te te cte nte unchecked dmap g; new_te)

type eterm = ET of nameT * ity | ENT of nameNT * ity | EVar of nameNT * ity | EApp of eterm * eterm list
           | ECoerce of ity * ity * eterm
exception Found of eterm 

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

let print_evars vte =
  List.iter
  (fun (v,ty) ->
    List.iter (fun aty ->
      print_string (v^"[");print_ity aty;print_string "] ") ty)
  vte

let rec typings_in_eterm eterm =
  match eterm with
    ENT(f,aty) -> [(f,aty)]
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

let rec print_eterm eterm =
  match eterm with
    ENT(f,aty) -> print_string (f^"[");print_ity aty;print_string "]"
  | ET(a,aty) -> print_string (a^"[");print_ity aty;print_string "]"
  | EVar(v,aty) -> print_string (v^"[");print_ity aty;print_string "]"
  | EApp(t,ts) ->
     ( print_eterm t; print_string " ";
      List.iter
      (fun t1 -> print_eterm_sub t1; print_string " ") ts)
  | ECoerce(aty1,aty2,t) ->
    ( print_string "C[";print_ity aty1;print_string "=>";print_ity aty2;print_string "]";
     print_eterm t)
and print_eterm_sub eterm =
  match eterm with
    EApp(_,_) -> print_string "(";print_eterm eterm; print_string ")"
  | ECoerce(_,_,_)-> print_string "(";print_eterm eterm; print_string ")"
  | _ -> print_eterm eterm

let print_erule f aty vte eterm =
  print_string (f^"[");
  print_ity aty;
  print_string "]";
  print_evars vte;
  print_string "-> ";
  print_eterm eterm;
  print_string "\n"

let mk_ehead h aty =
  match h with
    NT(f) -> ENT(f,aty)
  | T(a) -> ET(a,aty)
  | Var(x) -> EVar(x,aty)
  | _ -> assert false

let rec rangesubtype aty1 aty2 k =
  if k=0 then subtype aty1 aty2
  else
   match aty1 with
     ItyQ(_) -> false
  | ItyFun(_,aty1') -> rangesubtype aty1' aty2 (k-1)

let lookup_headty vte te cte h =
  match h with
    NT(f) -> (try Hashtbl.find te f with Not_found -> assert false)
  | T(a) -> (try List.assoc a cte with Not_found -> assert false)
  | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
  | _ -> assert false

let rec find_derivation vte te cte term aty =
  let (h,terms) = Grammar.decompose_term term in
  let k = List.length terms in
  let head_typings = find_headtype vte te cte h aty k in
   try
     List.iter (fun (eh,aty0) ->
      try
       let (eterms,rty) = find_derivation_terms vte te cte terms aty0 in
       let eterm1 = compose_eterm eh eterms in
       let eterm2 =
         if rty=aty then eterm1
         else ECoerce(rty,aty,eterm1)
       in raise (Found eterm2)
      with Not_found -> ()
     ) head_typings; raise Not_found
   with Found eterm -> eterm
and find_derivation_terms vte te cte terms aty =
  match terms with
   [] -> ([], aty)
 | term::terms' ->
    match aty with
      ItyQ(_) -> raise Not_found
    | ItyFun(ty1,aty2) ->
       let eterms= find_derivation_ty vte te cte term ty1 in
       let (etermss,rty) = find_derivation_terms vte te cte terms' aty2 in
         (eterms::etermss, rty)
and find_derivation_ty vte te cte term ty =
  List.map (find_derivation vte te cte term) ty
and find_headtype vte te cte h aty k =
  let ty = lookup_headty vte te cte h in
  let ty' = List.filter 
            (fun aty1 -> rangesubtype aty1 aty k) ty in
   List.map (fun aty1 -> (mk_ehead h aty1, aty1)) ty'

let rec decompose_ity ity =
  match ity with
    ItyQ(_) -> ([], ity)
 | ItyFun(ty1,ity2) -> 
     let (tys,rty) = decompose_ity ity2 in
       (ty1::tys, rty)
