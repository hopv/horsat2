(** check the sorts of non-terminals, print them and the order of the recursion scheme **)
(** Note: the implementation below is naive and slow **)

open Flags;;
open Utilities;;
open Grammar;;
open Automaton;;

type tvar = int
type st = STvar of (st option) ref | STbase | STfun of st * st 
let dummy_type = STbase

let new_tvid() = ref None

let new_tvar() = STvar(new_tvid())

let rec deref_st st =
  match st with
    STvar(tref) -> 
      ( match !tref with
         None -> st
       | Some(st') -> let st1 = deref_st st' in (tref:= Some(st1); st1))
  | _ -> st

let rec kind_of_sty st =
  match deref_st st with
    | STvar _ | STbase -> O
    | STfun (t1,t2) -> Kfun (kind_of_sty t1,kind_of_sty t2);;

let rec arity2sty n =
  if n<0 then assert false
  else if n=0 then STbase
  else STfun(STbase, arity2sty (n-1))

let rec sty2arity sty =
  let sty' = deref_st sty in
  match sty' with
    STvar _ -> 0
  | STbase -> 0
  | STfun(_,sty1) -> (sty2arity sty1) + 1
exception IllSorted of string
exception UnifFailure of st * st

let is_stfun sty =
  let sty' = deref_st sty in
  match sty' with
    STfun _ -> true
  | _ -> false


let subst_id = []

let rec app_subst sub st =
  match st with
     STvar v -> (try List.assoc v sub with Not_found -> st)
   | STfun(st1,st2) -> STfun(app_subst sub st1, app_subst sub st2)
   | _ -> st

let rec inst_var st =
  let st' = deref_st st in
  match st' with
     STvar vref ->  STbase
   | STfun(st1,st2) -> STfun(inst_var st1, inst_var st2)
   | _ -> st'

let comp_subst sub1 sub2 =
  let sub1' = List.map (fun (x,st) -> (x, app_subst sub2 st)) sub1 in
  let dom1 = List.map fst sub1 in
  let sub2' = List.filter (fun (x,st) -> not(List.mem x dom1)) sub2 in
    sub1'@sub2'

let rec occur v sty =
  match sty with
    STvar(v1) -> v==v1
  | STfun(sty1,sty2) -> (occur v sty1)||(occur v sty2)
  | _ -> false

let rec unify_sty sty1 sty2 =
  let sty1' = deref_st sty1 in
  let sty2' = deref_st sty2 in
   match (sty1',sty2') with
    (STvar v1, STvar v2) ->
        if v1==v2 then ()
        else v1 := Some(sty2')
  | (STvar v1, _) ->
       if occur v1 sty2'
       then raise (UnifFailure (sty1',sty2'))
       else (v1 := Some(sty2'))
  | (_, STvar v2) -> 
       if occur v2 sty1'
       then raise (UnifFailure (sty1',sty2'))
       else (v2 := Some(sty1'))
  | (STfun(st11,st12), STfun(st21,st22)) ->
      unify_sty st11 st21; unify_sty st12 st22
  | (STbase, STbase) -> ()
  | _ -> raise (UnifFailure (sty1,sty2))
  
let rec unify_all c =
  match c with
     [] -> []
  | (sty1,sty2)::c1 ->
      unify_sty sty1 sty2;
      unify_all c1

let rec stys2sty stys =
  match stys with
    [] -> new_tvar()
  | [sty] -> sty
  | sty::stys' ->
      let sty1 = stys2sty stys' in
      let _= unify_sty sty sty1 in
         sty

let rec print_sty sty =
  match sty with
    STvar(tv) -> print_string ("'a")
  | STbase -> print_string "o"
  | STfun(sty1,sty2) ->
       let flag1 = is_stfun sty1 in
         (if flag1 then print_string "(" else ();
          print_sty sty1;
          if flag1 then print_string ")" else ();
          print_string " -> ";
          print_sty sty2)
         
let print_sortbinding (f, sty) =
  (print_string (" "^f^" : ");
   print_sty sty;
   print_string "\n")

let print_nste nste =
  let _ = print_string "\nSorts of non-terminals:\n" in
  let _ = print_string "======================\n" in
  let _ = for i=0 to (Array.length nste - 1) do
             print_sortbinding ((name_of_nt i), nste.(i))
          done
  in
  let _ = print_string "\n" in
    ()

let print_cste cste =
  let _ = print_string "\nSorts of terminals:\n" in
  let _ = print_string "======================\n" in
  let _ = List.map print_sortbinding cste in
  let _ = print_string "\n" in
    ()

let lookup_stype_nt f nste = nste.(f)
let lookup_stype_t a cste = List.assoc a cste
let lookup_stype_var v vste = let (_,i) = v in vste.(i)

let rec tcheck_term t vte cte nte =
  match t with
    NT(f) -> (lookup_stype_nt f nte, [])
  | T(a) -> (lookup_stype_t a cte, [])
  | Var(v) -> (lookup_stype_var v vte, [])
  | App(t1,t2) ->
       let (sty1, c1) = tcheck_term t1 vte cte nte in
       let (sty2, c2) = tcheck_term t2 vte cte nte in
       let sty3 = new_tvar() in
       let sty4 = STfun(sty2,sty3) in
          (sty3, (sty1,sty4)::(c2@c1))

let rec mk_functy stys sty =
  match stys with
    [] -> sty
  | sty1::stys' ->
       STfun(sty1, mk_functy stys' sty)

let tcheck_rule f (arity, body) cste nste =
  let vste = Array.make arity dummy_type in
  let _ = for i=0 to arity-1 do
               vste.(i) <- new_tvar()
          done
  in
  let (sty,c1) = tcheck_term body vste cste nste in
  let fty1 = mk_functy (Array.to_list vste) sty (* STbase*) in
  let fty2 = lookup_stype_nt f nste in
(*    (sty,STbase):: *) (* add this if we wish to enforce the righthand side has ground type *)
       (fty1,fty2)::c1

let tcheck_rules rules cste nste =
  let cstr = ref [] in
   for i=0 to Array.length rules - 1 do 
     (cstr := (tcheck_rule i rules.(i) cste nste)@ !cstr)
   done;
   !cstr

let rec order_of_sty sty =
  match sty with
    STfun(sty1,sty2) -> max ((order_of_sty sty1)+1) (order_of_sty sty2)
  | _ -> 0

let order_of_nste nste =
  let nste' = indexlist (Array.to_list nste) in
  let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
  let x = list_max (fun (nt1,ord1) ->fun (nt2,ord2) -> compare ord1 ord2) ordmap in
    x

let print_order (f,ord) =
  let _ = print_string ("\nOrder of recursion scheme: "^(string_of_int ord)^"\n") in
  let _ = print_string ("Non-terminal of highest order: "^(name_of_nt f)^"\n") in
    ()

let rec mk_vste i vste arity sty =
  if i>=arity then ()
  else 
    (match sty with
       STfun(sty1,sty') -> 
          vste.(i) <- sty1; mk_vste (i+1) vste arity sty'
     | _ -> assert false (* arity and sty contradict *)
   )

(*
let sorttab = Hashtbl.create 1000
let register_sort_htab term sty =
  try
    Hashtbl.find sorttab term
  with Not_found ->
    (Hashtbl.add sorttab term sty; sty)
let lookup_sort term =
  try
    Hashtbl.find sorttab term
  with Not_found -> 
   (print_term term; assert false)

let rec register_sort_term term cste nste vste =
  match term with
    NT(f) -> let sty = lookup_stype_nt f nste in
              register_sort_htab term sty
  | T(a) -> let sty = lookup_stype_t a cste in
              register_sort_htab term sty
  | Var(v) -> let sty = lookup_stype_var v vste in
              register_sort_htab term sty
  | App(t1,t2) ->
       let sty1 = register_sort_term t1 cste nste vste in
       let sty2 = register_sort_term t2 cste nste vste in
        match sty1 with
            STfun(sty3,sty4) ->
              if sty3=sty2 then 
                register_sort_htab term sty4
              else assert false
          | _ -> assert false

let register_sort_rule nt (arity,term) cste nste =
  let sty = nste.(nt) in
  let _ = register_sort_htab (NT(nt)) sty in
  let vste = Array.make arity dummy_type in
    begin
      mk_vste 0 vste arity sty;
      for i=0 to arity -1 do
        let _ = register_sort_htab (Var(nt,i)) vste.(i) in ()
      done;
      register_sort_term term cste nste vste
    end

let register_sort g cste nste =
  for i=0 to Array.length g.r - 1 do
    let _ = register_sort_rule i g.r.(i) cste nste in ()
  done
*)
let alpha2cste alpha =
  List.map (fun (a,k) ->
    if k<0 then (a, new_tvar()) else (a, arity2sty k)) alpha

let update_arity_of_nt g nste =
  for f=0 to Array.length g.r - 1 do
    let sty = nste.(f) in
    let arity = sty2arity sty in
    let (arity',body) = g.r.(f) in
      if arity>arity' then (* add dummy argument *)
         let vars = List.map (fun i->Var(f,i)) (fromto arity' arity) in
         let body' = Grammar.mk_app body vars in
            g.r.(f) <- (arity,body')
      else ()
  done

let tcheck g alpha =
  let cste = alpha2cste alpha in
  let num_of_nts = Array.length g.nt in
  let nste = Array.make num_of_nts dummy_type in
  let _ = for i=0 to num_of_nts-1 do
             nste.(i) <- new_tvar()
          done 
  in
  let _ = if !debugging then print_cste cste in
  let _ = if !debugging then print_nste nste in
  let rules = g.r in
  let c = tcheck_rules rules cste nste in
  let _ =  try
                unify_all c 
             with UnifFailure _ ->
                    raise (IllSorted "Rules are not well-sorted\n")
  in
  let _ = for i=0 to num_of_nts-1 do
              nste.(i) <- inst_var (nste.(i))
          done
  in
  let cste' = List.map (fun (a,sty) -> (a, inst_var sty)) cste in
  let (f,ord) = order_of_nste nste in
  begin
   ( if !Flags.debugging then 
     (print_nste nste;
     print_cste cste';
     print_order (f, ord)));
(*     register_sort g cste' nste;*)
     flush stdout;
     update_arity_of_nt g nste;
     List.map (fun (a,sty) -> (a, sty2arity sty)) cste'
   end
