open Utilities;;
open Grammar;;
open Automaton;;
open Flags;;

let parseFile filename =
  let in_strm = 
    try
      open_in filename 
    with
	Sys_error _ -> (print_string ("Cannot open file: "^filename^"\n");exit(-1)) in
  let _ = print_string ("analyzing "^filename^"...\n") in
  let _ = flush stdout in
  let lexbuf = Lexing.from_channel in_strm in
  let result =
    try
      Parser.main Lexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) in
  let _ = 
    try
      close_in in_strm
    with
	Sys_error _ -> (print_string ("Cannot close file: "^filename^"\n");exit(-1)) 
  in
    result

let parseStdIn() =
  let _ = print_string ("reading standard input ...\n") in
  let in_strm = stdin in
  let lexbuf = Lexing.from_channel in_strm in
  let result =
    try
      Parser.main Lexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) 
  in
    result

let factor = ref 1
let te_updated = ref false

(* main verification routine *)
let verify g0 m0 =
  (* in horsat mode, completement the automaton *)
  let m = if !negate_automaton then m0
          else
           let m' = Automaton.add_or m0 in
              m'
  in
  let alphabet = Automaton.getalpha m in
  (* normalize the grammar *)
  let g0 = Grammar.normalize g0 alphabet in
  let dmap0 = Grammar.mk_depend g0 in
  let _ = if !debugging then
           (print_string "normalized grammar:\n"; print_gram g0) in
  let g = if !negate_automaton then g0
          else (* gfp mode *)
           let _ = Grammar.register_recfun dmap0 g0 in
           let g' = Grammar.unfold g0 in
              g'
  in         
  let _ = if !debugging then
          (print_string "unfolded grammar:\n"; print_gram g) in
  let _ = (print_string "Doing forward analysis ...\n"; flush stdout) in
  let _ = 
     if !Flags.flow then ()
     else (Reduce.enqueue (NT(g.s));
           Reduce.reduce g !Flags.redstep;
           print_string "Reduction done\n"; flush stdout;
           Reduce.print_headtab();
           Reduce.print_invheadtab())
  in
  (* flow analysis *)
  let fcs = Flow.genC g in
  let _ = if !debugging then Flow.print_fcs fcs else () in
  let flow = Flow.solve_fcs fcs g in
  let _ = (print_string "...done\n"; flush stdout) in
  let _ = if !debugging then Flow.print_heads g in
(*  let _ = exit 0 in *)

  (* constant typing *)
  let cte = Type.automaton2cte' m in 
  let _ = Stype.tcheck g cte in 
   (* recompute the type of terminals
    * In the lfp mode, types for negated automaton are obtained
    *)
  let cte1 = Type.automaton2cte m in
  let _ = Type.initialize g cte1 in
  let ntstmap = Flow.mk_ntstmap flow g m in
  let ntstmap' = if !negate_automaton then 
                   Flow.negate_ntstmap ntstmap 
                 else ntstmap
  in
  let _ = if !debugging then Flow.print_stmap ntstmap' in
  let dmap = Grammar.mk_depend g in
  let _ = Type.initialize_nttype dmap g m in
  let dmap2 = Type.var_dmap g in
  (* run saturation *)
   if !negate_automaton then
    let _ = Type.saturate g dmap dmap2 m.init in
      Type.report g.s m.init
   else 
(**     let cte0 = Type.automaton2cte_pure m in **)
     if !Flags.flow then
      Type.gfp_saturate g cte1 dmap dmap2 m.init dmap0 g0
     else
      Type.gfp_saturate2 g cte1 dmap m.init

let rec report_input g m =
  let _ = print_string ("The number of rewrite rules: "^(string_of_int (List.length g.r))^"\n") in
  let _ = print_string ("The size of recursion scheme: "^(string_of_int (Grammar.size_of g))^"\n") in
  let _ = print_string ("The number of states: "^(string_of_int (Automaton.size_st m))^"\n") in
    ()

let verifyParseResult (prerules,tr) = 
  let (g, m) = Conversion.convert (prerules,tr) in
  let _ = report_input g m in
    verify g m 

let string_of_parseresult (prerules, tr) =
  (Syntax.string_of_prerules prerules)^"\n"^(Syntax.string_of_transitions tr)

let suicide() =
  let pid = Unix.getpid() in
    Unix.kill pid Sys.sigabrt 

exception LogFile

let web = ref false 

let rec create_file n =
  if n=0 then
     (print_string "Cannot open a log file\n"; raise LogFile)
  else
     try
      let n = Random.int(15) in
      let prefix = if !web then "/home/koba/horsmc/log/log" else "log" in
      let filename = prefix^(string_of_int n)^".hrs" in
      let fp = open_out_gen [Open_wronly;Open_creat;Open_excl;Open_trunc] 0o666 filename in
         (filename, fp)
     with
       _ -> create_file (n-1)
        
let write_log parseresult =
  let s = string_of_parseresult parseresult in
  let _ = Random.init(int_of_float(Unix.time())) in
  let (filename, fp) = create_file 3 in
  let _ = output_string fp s in
    (close_out fp; filename)

let rec loop() = loop()

let report_usage () =
    (print_string "Usage: \n";
     print_string "horsat <option>* <filename> \n\n";
     print_string " -d\n";
     print_string "  debug mode\n";
    )

let rec read_options index =
  match Sys.argv.(index) with
   "-d" -> (debugging := true; read_options (index+1))
  | "-o" -> (outputfile := Sys.argv.(index+1); read_options (index+2))
  | "-all" -> (compute_all := true; read_options (index+1))
  | "-p" -> (Type.period := int_of_string(Sys.argv.(index+1));
             read_options(index+2))
  | "-r" -> (Flags.redstep := int_of_string(Sys.argv.(index+1));
             Flags.flow := false;
             read_options(index+2))
  | "-ne" -> (emptiness_check := false; read_options (index+1))
  | "-noce" -> (Flags.ce := false; read_options (index+1))
  | "-gfp" -> (negate_automaton := false; read_options (index+1))
  | _ -> index


let main () =
  let _ = print_string "HorSat 1.02: Saturation-based model checker for higher-order recursion schemes\n" in
  let start_t = Sys.time() in
  (* read command-line options *)
  let (index,flag) = 
      try
        (read_options 1, true)
      with
        Invalid_argument _ -> (0,false)
      | _ -> 
         (print_string "Invalid options\n\n";
          report_usage();
          exit (-1))
  in
  (* parsing *)
  let parseresult =
    try
      if flag then
         parseFile(Sys.argv.(index))
      else
         parseStdIn()
    with
	Lexer.LexError s -> (print_string ("lex error: "^s^"\n"); exit (-1))
  in
 let _ = if !web then Unix.alarm 3 else 0 in
  let logfile = write_log parseresult in
    ((* Sys.set_signal Sys.sigalrm (Sys.Signal_handle(fun sigid -> write_log (string_of_parseresult parseresult))); *)
      (* loop();*)  (** for testing logging **)
     (* verify *)
     verifyParseResult parseresult;
     let end_t = Sys.time() in
       (print_string ("Elapsed Time: "^(string_of_float (end_t -. start_t))^"sec\n");
        flush stdout;
        Unix.unlink logfile)
    );;

if !Sys.interactive then
  ()
else
  main();;




