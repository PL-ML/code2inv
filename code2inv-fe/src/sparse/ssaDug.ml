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
open Vocab
open Yojson.Safe
open Global
open IntraCfg
open InterCfg
open BasicDom

module type S =
sig
  module Access : Access.S
  module DUGraph : Dug.S
  module PowLoc : PowDom.CPO
  type node = BasicDom.Node.t
  type loc
  val make              : ?skip_nodes : BasicDom.Node.t BatSet.t -> Global.t * Access.t * PowLoc.t -> DUGraph.t
  val to_json_intra     : DUGraph.t -> Access.t -> Yojson.Safe.json
  val to_json_inter     : DUGraph.t -> Access.t -> Yojson.Safe.json

  val construct_ssa     : Global.t * Access.t * PowLoc.t -> ExtractSSAGraph.t
end

module Make (DUGraph : Dug.S) (Access: Access.S
                               with type Loc.t = DUGraph.Loc.t and type PowLoc.t = DUGraph.PowLoc.t) =
struct
  module DUGraph = DUGraph
  type node = BasicDom.Node.t
  module Loc = DUGraph.Loc
  module PowLoc = DUGraph.PowLoc
  module LocMap = BatMap.Make(Loc)
  module NodeMap = BatMap.Make(Node)
  module IntraNodeMap = BatMap.Make(IntraCfg.Node)
  module IntraNodeSet = IntraCfg.NodeSet
  type loc = Loc.t

  (** Def-use graph construction *)
  module Access = Access
  type phi_points = PowLoc.t NodeMap.t
  type access_map = PowLoc.t IntraNodeMap.t
  type access_map_inv = IntraNodeSet.t LocMap.t

  let get_ordinary_defs : Access.t -> node -> PowLoc.t
    =fun access node -> 
      let info = (Access.find_node node access) in
      (* let _ = prerr_endline ("get_ordinary_defs: info: "  ^ (Access.Info.to_string info)) in *)
      Access.Info.defof info

  let get_ordinary_uses : Access.t -> node -> PowLoc.t
    =fun access node -> Access.Info.useof (Access.find_node node access)

  let use_table = Hashtbl.create 10000
  let def_table = Hashtbl.create 10000
  let def_wo_local_table = Hashtbl.create 10000
  let access_table = Hashtbl.create 10000
  let access_wo_local_table = Hashtbl.create 10000

  let uses_of_function : Global.t -> Access.t -> pid -> PowLoc.t -> PowLoc.t
    =fun global access pid locset ->
      try
        Hashtbl.find use_table pid
      with _ ->
        let locset =
          if Global.is_rec pid global && not !Options.unsound_recursion then
            let uses = Access.Info.useof (Access.find_proc_reach pid access) in
            PowLoc.inter locset uses
          else
            let uses = Access.Info.useof (Access.find_proc_reach_wo_local pid access) in
            PowLoc.inter locset uses
        in
        Hashtbl.add use_table pid locset;
        locset

  let defs_of_function : Global.t -> Access.t -> pid -> PowLoc.t -> PowLoc.t
    =fun global access pid locset ->
      try
        Hashtbl.find def_table pid
      with _ ->
        let locset =
          if Global.is_rec pid global && not !Options.unsound_recursion then
            let defs = Access.Info.defof (Access.find_proc_reach pid access) in
            PowLoc.inter locset defs
          else
            let defs = Access.Info.defof (Access.find_proc_reach_wo_local pid access) in
            PowLoc.inter locset defs
        in
        Hashtbl.add def_table pid locset;
        locset

  let access_of_function : Global.t -> Access.t -> pid -> PowLoc.t -> PowLoc.t
    =fun global access pid locset ->
      try
        Hashtbl.find access_table pid
      with _ ->
        let locset =
          if Global.is_rec pid global && not !Options.unsound_recursion then
            let access_proc_reach = Access.find_proc_reach pid access in
            let defs = Access.Info.defof access_proc_reach in
            let uses = Access.Info.useof access_proc_reach in
            let access = PowLoc.union defs uses in
            PowLoc.inter locset access
          else
            let acc = Access.find_proc_reach_wo_local pid access in
            let defs = Access.Info.defof acc in
            let uses = Access.Info.useof acc in
            let access = PowLoc.union defs uses in
            PowLoc.inter locset access
        in
        Hashtbl.add access_table pid locset;
        locset

  (* locations considered as being used in the given node *)
  let lhsof : Global.t * Access.t -> node -> PowLoc.t -> PowLoc.t
    =fun (global,access) node locset ->
      let (pid,cfgnode) = Node.get_pid node, Node.get_cfgnode node in

      (* ordinary defs  *)
      let ordinary_defs = get_ordinary_defs access node in
      (* let _ = prerr_endline ("ordinary_defs: " ^ (PowLoc.to_string ordinary_defs)) in *)

      (* entry defines use(f) *)
      let defs_at_entry =
        if IntraCfg.is_entry cfgnode
        then uses_of_function global access pid locset
        else PowLoc.empty in

      (* return nodes define defs(callees) *)
      let defs_at_return =
        if InterCfg.is_returnnode node global.icfg then
          ProcSet.fold (fun callee ->
              PowLoc.union (defs_of_function global access callee locset)
            ) (InterCfg.get_callees (InterCfg.callof node global.icfg) global.icfg) PowLoc.empty
        else PowLoc.empty
      in
      (* union three possible cases *)
      PowLoc.union ordinary_defs (PowLoc.union defs_at_entry defs_at_return)

  (* locations considered as being defined in the given node *)
  let rec rhsof : Global.t * Access.t -> node -> PowLoc.t -> PowLoc.t
    =fun (global,access) node locset ->
      let (pid,cfgnode) = Node.get_pid node, Node.get_cfgnode node in
      let ordinary_uses = get_ordinary_uses access node in
      (* exit uses defs(f) *)
      let uses_at_exit =
        if IntraCfg.is_exit cfgnode
        then defs_of_function global access pid locset
        else PowLoc.empty in
      (* return node inside recursive functions uses local variables of pid *)
      let uses_at_rec_return =
        if InterCfg.is_returnnode node global.icfg && Global.is_rec pid global then
          Access.find_proc_local pid access
        else PowLoc.empty in
      (* return node uses not-localized variables of call node *)
      let uses_at_return =
        if InterCfg.is_returnnode node global.icfg then
          let call_node = InterCfg.callof node global.icfg in
          let callees = InterCfg.get_callees call_node global.icfg in
          let defs_of_callees =
            let add_defs callee =
              PowLoc.union (defs_of_function global access callee locset) in
            ProcSet.fold add_defs callees PowLoc.empty in
          let add_not_defined callee =
            let defs = defs_of_function global access callee locset in
            PowLoc.union (PowLoc.diff defs_of_callees defs) in
          ProcSet.fold add_not_defined callees PowLoc.empty
        else PowLoc.empty in
      (* call nodes uses uses(callees) *)
      let uses_at_call =
        if InterCfg.is_callnode node global.icfg then
          ProcSet.fold (fun callee ->
              PowLoc.union (uses_of_function global access callee locset)
            ) (InterCfg.get_callees node global.icfg) PowLoc.empty
        else PowLoc.empty
      in
      list_fold PowLoc.union
        [ ordinary_uses; uses_at_exit; uses_at_call; uses_at_rec_return;
          uses_at_return ] PowLoc.empty

  let prepare_defs_uses : Global.t * Access.t * PowLoc.t -> IntraCfg.t -> access_map * access_map
    =fun (global,access,locset) cfg ->
      let collect f =
        List.fold_left (fun m node ->
            let v = (f (global,access) (Node.make (IntraCfg.get_pid cfg) node) locset) in
            (* let cmd = IntraCfg.find_cmd node cfg in
               let _ = prerr_endline ("\nin collect, k:" ^ ( IntraCfg.Node.to_string node )) in
               let _ = prerr_endline ("in collect, cmd: " ^ (IntraCfg.Cmd.to_string cmd)) in
               let _ = prerr_endline ("in collect, v: " ^ (PowLoc.to_string v)) in *)

            IntraNodeMap.add node v m
          ) IntraNodeMap.empty (IntraCfg.nodesof cfg) in
      (* let _ = prerr_endline "\nwill collect lhs\n" in *)
      let lhs_res = collect lhsof in 
      (* let _ = prerr_endline "\nwill collect rhs\n" in *)
      let rhs_res = collect rhsof in 
      (lhs_res, rhs_res)

  let prepare_defnodes : Global.t * Access.t -> IntraCfg.t -> access_map -> access_map_inv
    =fun (global,access) cfg defs_of ->
      (* let _ = prerr_endline "prepare_defnodes:\n" in
         let _ = IntraNodeMap.iter 
          (fun k v ->  
             let cmd = IntraCfg.find_cmd k cfg in
             prerr_endline ("k:" ^ ( IntraCfg.Node.to_string k ));
             prerr_endline ("cmd: " ^ (IntraCfg.Cmd.to_string cmd));
             prerr_endline ("v:" ^ (PowLoc.to_string v))
          ) defs_of  in *)
      try
        list_fold (fun node ->
            PowLoc.fold (fun addr map ->
                let set = try LocMap.find addr map with _ -> IntraNodeSet.empty in
                LocMap.add addr (IntraNodeSet.add node set) map
              ) (IntraNodeMap.find node defs_of))
          (IntraCfg.nodesof cfg)
          LocMap.empty
      with _ -> failwith "Dug.prepare_defnodes"

  let get_phi_points cfg access (defs_of,uses_of,defnodes_of) : phi_points =
    let pid = IntraCfg.get_pid cfg in

    let variables = LocMap.fold (fun k _ -> PowLoc.add k) defnodes_of PowLoc.empty in

    (*XUJIE_DBG let _ = prerr_endline ("get_phi_points: variables " ^ (string_of_int (PowLoc.cardinal variables)) ^ "\n")  in *)
    (* let _ = PowLoc.iter (fun x -> prerr_endline (DUGraph.Loc.to_string x) ) variables in *)

    let map_set_add k v map =
      try NodeMap.add k (PowLoc.add v (NodeMap.find k map)) map
      with _ -> NodeMap.add k (PowLoc.singleton v) map
    in

    let rec iterate_node w var itercount hasalready work joinpoints =
      (**
         // inner while loop of Fig. 11

         while(w is not empty) {
         take x from w
         for each Y in DF(X) {
          if hasAlready(Y) < IterCount then
            place phi( V...)  at Y
            hasAlready(Y) = IterCount  // mark Y as visited (place phi)
          if work(Y) < IterCount then
            work(Y) = IterCount // mark Y as visited (enter w)
          w = w U {Y}
         }
         }
       **)

      match w with
      | node::rest ->
        let (rest,hasalready,work,joinpoints) =
          IntraNodeSet.fold (fun y (rest,hasalready,work,joinpoints) ->
              if IntraNodeMap.find y hasalready < itercount then

                let joinpoints = map_set_add (Node.make pid y) var joinpoints  in

                let hasalready = IntraNodeMap.add y itercount hasalready in
                let (work,rest) =
                  if IntraNodeMap.find y work < itercount then
                    (IntraNodeMap.add y itercount work, y::rest)
                  else (work,rest)
                in
                (rest,hasalready,work,joinpoints)
              else (rest,hasalready,work,joinpoints)
            ) (IntraCfg.dom_fronts node cfg) (rest,hasalready,work,joinpoints)
        in
        iterate_node rest var itercount hasalready work joinpoints
      | [] -> (hasalready,work,joinpoints)
    in

    let rec iterate_variable vars itercount hasalready work joinpoints =
      (** 
         // outer for loop of Fig. 11
         for each V {
         IterCount = IterCount + 1
         for each X in A(V) {
          Work(X) = IterCount // mark X as visited (enter w)
          W = W U {X}
         }
         // inner while loop
         }
       **)       
      match vars with
      | v::rest ->
        let itercount = itercount + 1 in
        let (w,work) = IntraNodeSet.fold (fun node (w,work) ->
            (node::w, IntraNodeMap.add node itercount work)
          ) (LocMap.find v defnodes_of) ([],work)
        in
        let (hasalready, work, joinpoints) = iterate_node w v itercount hasalready work joinpoints in
        iterate_variable rest itercount hasalready work joinpoints
      | [] -> joinpoints
    in

    let init_vars = (PowLoc.elements variables) in
    let init_hasalready = list_fold (fun x -> IntraNodeMap.add x 0) (IntraCfg.nodesof cfg) IntraNodeMap.empty in
    let init_work = list_fold (fun x -> IntraNodeMap.add x 0) (IntraCfg.nodesof cfg) IntraNodeMap.empty in
    let init_itercount = 0 in
    iterate_variable init_vars init_itercount init_hasalready init_work NodeMap.empty


  let cfg2ssa : Global.t * Access.t * PowLoc.t -> IntraCfg.t -> ExtractSSAGraph.t
    = fun (global,access,locset) cfg ->
      let ssa_graph = ExtractSSAGraph.from_intra_cfg cfg in

      let (node2defs,node2uses) = prepare_defs_uses (global,access,locset) cfg in 
      let loc2defnodes = prepare_defnodes (global,access) cfg node2defs in

      let pid = IntraCfg.get_pid cfg in
      let phi_points = get_phi_points cfg access (node2defs,node2uses,loc2defnodes) in


      (* XUJIE_DBG let _ = prerr_string ("after get_phi_points: " ^ ( string_of_int (NodeMap.cardinal phi_points) ) ^ "\n")  in *)
      (* let _ = NodeMap.iter (fun k v ->
          prerr_string (PowLoc.to_string v)
        ) phi_points
      in *)

      let phi_vars_of cfgnode = try NodeMap.find (Node.make pid cfgnode) phi_points with _ -> PowLoc.empty in

      (** insert phi nodes **)

      let ssa_graph =
        IntraCfg.fold_node (fun node ng ->
            let vars = phi_vars_of node in
            (* create a Phi node for each var *)
            PowLoc.fold (fun v ng ->
                let v_str = DUGraph.Loc.to_string v in
                ExtractSSAGraph.new_phi_before ng v_str node
              ) vars ng
          ) cfg ssa_graph
      in

      let entry_node = IntraCfg.entryof () in
      let rec find_def_in_dom_tree g node v_str =
        if node = entry_node then
          entry_node
        else
          let go_to_parent node =
            let parent = ExtractSSAGraph.parent_of_dom_tree node g in
            match parent with
            | Some p -> find_def_in_dom_tree g p v_str
            | _ -> raise (Failure "1: unexpected match during ssa construction")
          in
          begin
            match (ExtractSSAGraph.get_help_cmd g node) with
            | None ->
              let defs = IntraNodeMap.find node node2defs in
              let exists = DUGraph.PowLoc.exists (fun x -> (DUGraph.Loc.to_string x) = v_str) defs in
              if exists then node
              else go_to_parent node
            | Some (v_str2, _) ->
              if v_str = v_str2 then node
              else go_to_parent node
          end
      in

      (** figure out dependencies for phi nodes **)

      let ssa_graph_nodes = ExtractSSAGraph.nodesof ssa_graph in
      let ssa_graph = ExtractSSAGraph.compute_dom ssa_graph in
      let find_deps g node preds  v_str =
        (* potential bug : sequential phi nodes could ruin idom relation *)
        (* Essentially, there should be a single phi node (for several variables)  *)
        (* Thus, this function can only be used for non-phi nodes  *)
        (* OR, if it were called for phi-node, the graph should be IntraCfg rather than ssa_graph *)

        List.fold_left (fun st pre ->
            BatSet.add (find_def_in_dom_tree g pre v_str)  st
          ) BatSet.empty preds
      in
      let ssa_graph = List.fold_left (fun g node ->
          match (ExtractSSAGraph.get_help_cmd g node) with
          | None -> g
          | Some (v_str, [before_nd]) ->
            let preds = IntraCfg.pred before_nd cfg in
            let deps = find_deps g node preds v_str in
            ExtractSSAGraph.update_help_map g node (v_str, BatSet.elements deps)
          | _ -> raise (Failure "2: unexpected match during ssa construction")

        ) ssa_graph ssa_graph_nodes
      in


      (** check each use only have one def over all possible predecessors **)
      let _ = List.iter (fun node ->
          match (ExtractSSAGraph.get_help_cmd ssa_graph node) with
          | None ->
            let uses = IntraNodeMap.find node node2uses in
            DUGraph.PowLoc.iter (fun loc ->
                let preds = ExtractSSAGraph.pred node ssa_graph in

                let v_str = DUGraph.Loc.to_string loc in
                let deps = find_deps ssa_graph node preds v_str in
                assert ( (BatSet.cardinal deps) = 1 )
              ) uses
          | _ -> ()
        ) ssa_graph_nodes
      in

      (** collect vars (later passed to boogie/sygus) **)
      let vars = IntraCfg.fold_node (fun node st ->
          let (defs, uses) = IntraCfg.get_defs_uses node cfg in
          BatSet.union (BatSet.union defs uses) st
        ) cfg BatSet.empty
      in

      (* let _ = prerr_endline ("#vars: " ^  (string_of_int (BatSet.cardinal vars))) in *)

      (** collect consts (later passed to sygus) **)
      let consts = IntraCfg.fold_node (fun node st ->
          let cs = IntraCfg.get_consts node cfg in
          BatSet.union cs st
        ) cfg BatSet.empty
      in
      
      (* let _ = prerr_endline ("#consts: " ^  (string_of_int (BatSet.cardinal consts))) in *)

      (** assign cmd for each node **)
      let ssa_graph = List.fold_left (fun g node ->
          match (ExtractSSAGraph.get_help_cmd g node) with
          | None ->
            (* non-phi node *)

            (* my_prerr_endline ("assign non phi node: " ^ (string_of_int (IntraCfg.Node.id node) )); *)

            let cmd = IntraCfg.find_cmd node cfg in

            let (defs, uses) = IntraCfg.get_defs_uses node cfg in

            (* let print_log prefix st =
              my_prerr_endline ( prefix ^ ": [");
              BatSet.iter (fun v_str -> my_prerr_endline v_str) st;
              my_prerr_endline "]";
            in 

            print_log "defs" defs;
            print_log "uses" uses; *)


            assert( BatSet.cardinal defs < 2 );

            let def_dict = BatSet.fold (fun v_str mp ->
                let sub = IntraCfg.Node.id node in
                BatMap.add v_str sub mp
              ) defs  BatMap.empty
            in

            let use_dict = BatSet.fold (fun v_str mp ->
                let preds = ExtractSSAGraph.pred node ssa_graph in
                let deps = find_deps ssa_graph node preds v_str in
                (* we have checked deps can only has one element *)
                let sub = IntraCfg.Node.id (BatSet.any deps)  in
                BatMap.add v_str sub mp
              ) uses  BatMap.empty
            in

            let new_cmd = ExtractSSAGraph.MyCmd.from_intra_cmd cmd (def_dict, use_dict) in

            ExtractSSAGraph.add_cmd node new_cmd g


          | Some (v_str, deps) ->
            (* phi node *)
            (* my_prerr_endline ("assign phi node: " ^ (string_of_int (IntraCfg.Node.id node) )); *)
            (* my_prerr_endline ("phi node args: " ^ (string_of_int (List.length deps) )); *)

            let ls = List.fold_right (fun d res ->
                (v_str, IntraCfg.Node.id d) :: res) deps []
            in
            let cur_id = IntraCfg.Node.id node in
            let phi_cmd = ExtractSSAGraph.MyCmd.Phi ( (v_str,cur_id) :: ls) in

            ExtractSSAGraph.add_cmd node phi_cmd g                           

        ) ssa_graph ssa_graph_nodes
      in
      let ssa_graph = ExtractSSAGraph.record_vars_for_boogie ssa_graph vars in
      let ssa_graph = ExtractSSAGraph.record_consts_for_sygus ssa_graph consts in
      
      ssa_graph

  let construct_ssa : Global.t * Access.t * PowLoc.t -> ExtractSSAGraph.t
    =fun (global,access,locset) ->
      (* XUJIE_DBG let _ = prerr_endline ("construct_ssa, locset: " ^  ( PowLoc.to_string locset))  in *)
      let main_cfg = InterCfg.cfgof global.icfg "main" in
      (* let access = Access.restrict_access access locset in *)
      (* prerr_endline "construct_ssa..."; *)
      cfg2ssa (global,access,locset) main_cfg



  let cfg2dug : Global.t * Access.t * PowLoc.t -> IntraCfg.t -> DUGraph.t -> DUGraph.t
    =fun (global,access,locset) cfg dug ->
      Profiler.start_event "DugGen.cfg2dug init";
      let pid = IntraCfg.get_pid cfg in
      Profiler.finish_event "DugGen.cfg2dug init";

      Profiler.start_event "DugGen.cfg2dug prepare_du";
      let (node2defs,node2uses) = prepare_defs_uses (global,access,locset) cfg in
      Profiler.finish_event "DugGen.cfg2dug prepare_du";

      Profiler.start_event "DugGen.cfg2dug prepare_def";
      let loc2defnodes = prepare_defnodes (global,access) cfg node2defs in
      Profiler.finish_event "DugGen.cfg2dug prepare_def";

      Profiler.start_event "DugGen.cfg2dug get_phi";
      let phi_points = get_phi_points cfg access (node2defs,node2uses,loc2defnodes) in
      Profiler.finish_event "DugGen.cfg2dug get_phi";

      let defs_of node = IntraNodeMap.find node node2defs in
      let uses_of node = IntraNodeMap.find node node2uses in
      let phi_vars_of cfgnode = try NodeMap.find (Node.make pid cfgnode) phi_points with _ -> PowLoc.empty in
      let draw_from_lastdef loc2lastdef loc here dug =
        try
          let src = Node.make pid (LocMap.find loc loc2lastdef) in
          let dst = Node.make pid here in
          if PowLoc.mem loc locset then DUGraph.add_absloc src loc dst dug
          else dug
        with _ -> dug
      in
      let rec search loc2lastdef node dug =
        let uses = uses_of node in
        let non_phi_uses = PowLoc.diff uses (phi_vars_of node) in
        (* 1: draw non-phi uses from their last definition points
         *    do not draw for phi-vars since their the last defpoints are the
         *    current node *)
        Profiler.start_event "DugGen.cfg2dug draw_from_lastdef";
        let dug =
          PowLoc.fold (fun loc ->
              draw_from_lastdef loc2lastdef loc node
            ) non_phi_uses dug in
        Profiler.finish_event "DugGen.cfg2dug draw_from_lastdef";

        (* 2: update the last definitions:
         * (1) phi-variables are defined here
         * (2) lhs are defined here *)
        Profiler.start_event "DugGen.cfg2dug loc2lastdef";
        let loc2lastdef =
          PowLoc.fold (fun loc ->
              LocMap.add loc node
            ) (PowLoc.union (defs_of node) (phi_vars_of node)) loc2lastdef in
        Profiler.finish_event "DugGen.cfg2dug loc2lastdef";

        (* 3: draw phi-vars of successors from their last definitions *)
        Profiler.start_event "DugGen.cfg2dug draw phi";
        let dug =
          list_fold (fun succ ->
              PowLoc.fold (fun phi_var ->
                  draw_from_lastdef loc2lastdef phi_var succ
                ) (phi_vars_of succ)
            ) (IntraCfg.succ node cfg) dug in
        Profiler.finish_event "DugGen.cfg2dug draw phi";

        (* 4: process children of dominator trees *)
        IntraNodeSet.fold (search loc2lastdef) (IntraCfg.children_of_dom_tree node cfg) dug
      in
      search LocMap.empty IntraCfg.Node.entry dug

  let draw_intraedges : Global.t * Access.t * PowLoc.t -> DUGraph.t -> DUGraph.t
    =fun (global,access,locset) dug ->
      Profiler.start_event "DugGen.draw_intraedges";
      let n_pids = List.length (InterCfg.pidsof global.icfg) in
      my_prerr_endline "draw intra-procedural edges";
      let r =snd (
          InterCfg.fold_cfgs (fun pid cfg (k,dug) ->
              prerr_progressbar k n_pids;
              (k+1,cfg2dug (global,access,locset) cfg dug)
            ) global.icfg (1,dug)) in
      Profiler.finish_event "DugGen.draw_intraedges";
      r

  let draw_interedges : Global.t * Access.t * PowLoc.t -> DUGraph.t -> DUGraph.t
    =fun (global,access,locset) dug ->
      let calls = InterCfg.callnodesof global.icfg in
      let n_calls = List.length calls in
      my_prerr_endline "draw inter-procedural edges";
      list_fold (fun call (k,dug) ->
          prerr_progressbar k n_calls;
          let return = InterCfg.returnof call global.icfg in
          (k+1, ProcSet.fold (fun callee dug ->
               let entry = InterCfg.entryof global.icfg callee in
               let exit  = InterCfg.exitof  global.icfg callee in
               let locs_on_call = uses_of_function global access callee locset in
               let locs_on_return = defs_of_function global access callee locset in
               dug
               |> DUGraph.add_abslocs call locs_on_call entry
               |> DUGraph.add_abslocs exit locs_on_return return
             ) (InterCfg.get_callees call global.icfg) dug)
        ) calls (1,dug)
      |> snd

  let draw_singledefs : Global.t * Access.t * PowLoc.t -> InterCfg.Node.t list -> DUGraph.t -> DUGraph.t
    =fun (global,access,locset) nodes dug ->
      let nodes = PowNode.of_list nodes in
      let single_defs = PowLoc.inter locset (Access.find_single_defs access) in
      PowLoc.fold (fun x dug ->
          let def_points = Access.find_def_nodes x access in
          let _ = assert (PowNode.cardinal def_points = 1) in
          let def_point = PowNode.choose def_points in
          let use_points = Access.find_use_nodes x access in
          PowNode.fold (fun use_point ->
              if PowNode.mem def_point nodes && PowNode.mem use_point nodes
              then DUGraph.add_absloc def_point x use_point
              else id
            ) use_points dug
        ) single_defs dug

  let make ?(skip_nodes = BatSet.empty) : Global.t * Access.t * PowLoc.t -> DUGraph.t
    =fun (global,access,locset) ->
      let nodes = InterCfg.nodesof global.icfg in
      let access = Access.restrict_access access locset in
      DUGraph.create ~size:(List.length nodes) ()
      |> draw_intraedges (global,access,locset)
  (*    |> draw_interedges (global,access,locset) *)

  let to_json_intra : DUGraph.t -> Access.t -> json
    = fun g access ->
      let nodes = `List (DUGraph.fold_node (fun v nodes ->
          (`String (Node.to_string v))::nodes) g [])
      in
      let edges = `List (DUGraph.fold_edges (fun src dst edges ->
          let spid = InterCfg.Node.get_pid src in
          let dpid = InterCfg.Node.get_pid dst in
          if spid = dpid then
            let addrset = DUGraph.get_abslocs src dst g in
            let access_proc = Access.find_proc spid access in
            let localset = PowLoc.filter (fun x ->
                Access.Info.mem x access_proc) addrset in
            if PowLoc.is_empty localset then edges
            else
              (`List [`String (Node.to_string src); `String (Node.to_string dst);
                      `String (PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) localset "")])
              ::edges
          else edges
        ) g [])
      in
      `Assoc [("nodes", nodes); ("edges", edges)]

  let to_json_inter : DUGraph.t -> Access.t -> json
    = fun g access ->
      let nodes = `List (DUGraph.fold_node (fun v nodes ->
          (`String (Node.to_string v))::nodes) g [])
      in
      let edges = `List (DUGraph.fold_edges (fun src dst edges ->
          let spid = InterCfg.Node.get_pid src in
          let dpid = InterCfg.Node.get_pid dst in
          if not (spid = dpid) then
            let addrset = DUGraph.get_abslocs src dst g in
            let access_proc = Access.find_proc spid access in
            let localset = PowLoc.filter (fun x ->
                Access.Info.mem x access_proc) addrset in
            if PowLoc.is_empty localset then edges
            else
              (`List [`String (Node.to_string src); `String (Node.to_string dst);
                      `String (PowLoc.fold (fun addr s -> (Loc.to_string addr)^","^s) localset "")])
              ::edges
          else edges
        ) g [])
      in
      `Assoc [("nodes", nodes); ("edges", edges)]
end
