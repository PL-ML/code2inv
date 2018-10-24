(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
open Graph
open Cil
open Global
open Vocab

let print_cfg : Global.t -> Global.t
  = fun global ->
    `Assoc
      [ ("callgraph", CallGraph.to_json global.callgraph);
        ("cfgs", InterCfg.to_json global.icfg)]
    |> Yojson.Safe.pretty_to_channel stdout; exit 0



let finish t0 _ =
  my_prerr_endline "Finished properly.";
  Profiler.report stdout;
  my_prerr_endline (string_of_float (Sys.time () -. t0))

let wrap : ('a -> 'b) -> 'a -> 'a
  = fun f x ->
    let _ = f x in
    x

let main () =
  let t0 = Sys.time () in
  let _ = Profiler.start_logger () in

  let usageMsg = "Usage: main.native [options] source-files" in

  Printexc.record_backtrace true;


  (* process arguments *)
  Arg.parse Options.opts Frontend.args usageMsg;
  List.iter (fun f -> prerr_string (f ^ " ")) !Frontend.files;
  prerr_endline "";

  Cil.initCIL ();

  try
    StepManager.stepf true "Front-end" Frontend.parse ()
    |> Frontend.makeCFGinfo
    |> StepManager.stepf true "Translation to graphs" Global.init
    |> StepManager.stepf true "Pre-analysis" PreAnalysis.perform
    |> StepManager.stepf true "SSA analysis" ItvAnalysis.ssa_analysis
    |> StepManager.opt true "Simply unknown" ExtractSSAGraph.simplify_unknown
    |> StepManager.opt true "Eliminate skips" ExtractSSAGraph.remove_unnecessary_skip
    |> StepManager.opt !Options.simpl_control "Simplify control dependency" ExtractSSAGraph.simplify_control_dependency
    |> StepManager.opt !Options.print_ssa "Print ssa graph" (wrap ExtractSSAGraph.print_graph)

    |> fun ssa_graph -> if !Options.print_boogie then 
      ignore (
        ssa_graph
        |> StepManager.stepf true "prepare for boogie" ExtractSSAGraph.prepare_for_boogie
        |> StepManager.stepf true "init boogie" Boogie.init
        |> StepManager.opt !Options.print_boogie "print boogie" (wrap Boogie.print_boogie)
      );
    ssa_graph
    |> fun ssa_graph -> if !Options.print_token then 
      ignore (
        ssa_graph
        |> StepManager.stepf true "prepare for boogie (token)" ExtractSSAGraph.prepare_for_token
        |> StepManager.stepf true "init boogie (token)" Boogie.init
        |> StepManager.opt !Options.print_token "print token" (wrap Token.print_token)
      );
    ssa_graph
    |> fun ssa_graph -> if !Options.print_c then 
      ignore (
        ssa_graph
        |> StepManager.stepf true "prepare for boogie (c)" ExtractSSAGraph.prepare_for_c
        |> StepManager.stepf true "init boogie (c)" Boogie.init
        |> StepManager.opt !Options.print_c "print C" (wrap C.print_c)
      );
    ssa_graph
    |> fun ssa_graph -> if !Options.print_sygus then 
      ignore (
        ssa_graph 
        |> StepManager.stepf true "prepare for sygus" ExtractSSAGraph.prepare_for_sygus
        |> StepManager.stepf true "init boogie (sygus)" Boogie.init
        |> StepManager.opt !Options.print_sygus "print sygus" (wrap Sygus.print_sygus)
      );
    ssa_graph
    |> fun ssa_graph -> if !Options.print_inv then 
      ignore (
        ssa_graph 
        |> StepManager.stepf true "prepare for sygus (inv)" ExtractSSAGraph.prepare_for_sygus
        |> StepManager.stepf true "init boogie (inv)" Boogie.init
        |> StepManager.opt !Options.print_inv "print sygus inv track" (wrap Sygus.print_inv_track)
      );
    ssa_graph
    |> fun ssa_graph -> if !Options.print_smt2 then 
      ignore (
        ssa_graph 
        |> StepManager.stepf true "prepare for sygus (smt2)" ExtractSSAGraph.prepare_for_sygus
        |> StepManager.stepf true "init boogie (smt2)" Boogie.init
        |> StepManager.opt !Options.print_smt2 "print smt2" (wrap Smt2.print_smt2)
      );
    ssa_graph
    |> finish t0
  with exc ->
    prerr_endline (Printexc.to_string exc);
    prerr_endline (Printexc.get_backtrace())

let _ = main ()

let test_sygus () = 
  let s = "(and (== i_33 i))" in 
  let s = " (and
    (=>
      (and (= y y_30 ) )
      (not (and (not (>= y_30 1 ) ) ) )
    ))
" in 
  let x = Sygus.SExp.from_string s  in
  let x = Sygus.SExp.sanitize_for_sygus s in 
  prerr_endline (Sygus.SExp.to_string 0 x) 

(* let _ = test_sygus () *)
