(** Implementation  **)

open IntraCfg (* access IntraCfg.Cmd *)
open Vocab (* contains *)


type json = Yojson.Safe.json

       
let unk_conds = ref []

module MyCmd = struct
  type t =
  | If of Cil.exp * Cil.block * Cil.block * Cil.location
  | Loop of Cil.location
  | Assgn of Cil.lval * Cil.exp * Cil.location
  | Assert of Cil.exp * Cil.location
  | Assume of Cil.exp * Cil.location
  | UNK0
  | UNK1 of Cil.lval
  | Skip
  | Phi
  | NOOP of string
  | Err


  let resolve_call : Cil.lval option -> Cil.exp -> Cil.exp list -> Cil.location -> t
    = fun tmp fexp params loc ->
    let fn_name = CilHelper.s_exp fexp in
    if contains fn_name "unknown" then
      match tmp with
      | Some lval -> UNK1 lval
      | None -> UNK0                
    else if contains fn_name "assert" && List.length params == 1 then
      Assert (List.hd params, loc)
    else if contains fn_name "assume" && List.length params == 1 then
      (*this is needed, as sparrow fail to catch some assume call*)
      Assume (List.hd params, loc)
    else Err


  let fromIntraCfgCmd : Cmd.t -> t
    = fun c ->
    match c with
    | Cmd.Cset (lv, exp, loc) -> Assgn (lv, exp, loc)
    | Cmd.Cif (exp, b1, b2, loc) -> If (exp, b1, b2, loc)
    | Cmd.CLoop loc -> Loop loc
    | Cmd.Ccall (tmp, fexp, params, loc) -> resolve_call tmp fexp params loc
    | Cmd.Cskip -> Skip
    | Cmd.Cassume (exp,loc) -> Assume (exp,loc)  (*sparrow fail to catch some assume call*)
    | Cmd.Creturn (_, loc) -> NOOP "return"
    | _ -> Err
            
  let to_string : t -> string = fun c ->
    match c with
    | If (e,b1,b2,loc) -> "If: " ^
                            begin
                              match e with
                              | Cil.Lval lvl ->
                                 if List.mem lvl !unk_conds then
                                   "UNK"
                                 else
                                   CilHelper.s_exp e
                              | _ -> CilHelper.s_exp e
                            end
    | Loop loc -> "Loop"
    | Assgn (lv, e, loc) -> "assign(" ^ CilHelper.s_lv lv ^ "," ^ CilHelper.s_exp e ^ ")"
    | Assert (e, loc) -> "Assert: " ^ CilHelper.s_exp e
    | Assume (e, loc) -> "Assume: " ^ CilHelper.s_exp e
    | Skip -> "SKIP"
    | UNK0 -> "UNK_COND"
    | UNK1 lv -> "UNK_COND(" ^ CilHelper.s_lv lv ^ ")"
    | Err -> "ERROR"
    | NOOP s -> s
    | Phi -> "Phi"
    (* | _ -> "undefined_to_string" *)

  let rec exp_to_json : Cil.exp -> json
    = fun exp ->
    match exp with
    | Cil.Const c -> `Assoc [("Const", `String (CilHelper.s_const c)); ]
    | Cil.Lval l -> lval_to_json l
    | Cil.UnOp (u, e, typ) -> `Assoc [("OP", `String (CilHelper.s_uop u) );
                                      ("arg1", exp_to_json e);]
                               
    | Cil.BinOp (b, e1, e2, typ) -> `Assoc [("OP", `String (CilHelper.s_bop b) );
                                            ("arg1", exp_to_json e1);
                                            ("arg2", exp_to_json e2);]       
    | _ -> `String "ERROR_json"
            
  and lval_to_json : Cil.lval -> json
    = fun lvl ->
    if List.mem lvl !unk_conds then
      `String "UNK_VAL"
    else
      begin
        let (lh,offset) = lvl in
        match offset with
        | Cil.NoOffset -> s_lhost lh
        | _ -> `String "ERROR_offset"
      end
        
  and s_lhost : Cil.lhost -> json  = function 
    | Cil.Var vi -> `Assoc [("Var", `String vi.vname)]
    | Cil.Mem e -> `Assoc [("OP", `String "pt"); ("arg1", exp_to_json e)]
                
  let cmd_to_json : t -> json =
    fun c ->
    match c with
    | If (e,b1,b2,loc) -> `Assoc [ ("cmd", `String "if"); ("rval", exp_to_json e) ]
    | Assgn (lv, e, loc) -> `Assoc [("cmd", `String "assign");
                                    ("lval", lval_to_json lv);
                                    ("rval", exp_to_json e) ]
                             
    | Assume (e, loc) ->  `Assoc [("cmd", `String "Assume");
                                  ("rval", exp_to_json e) ]
                           
    | Assert (e, loc) ->  `Assoc [("cmd", `String "Assert");
                                  ("rval", exp_to_json e) ]
    | UNK1 lv -> `Assoc[ ("cmd", `String "UNK_COND");
                         ("lval", lval_to_json lv);]

    | NOOP s -> `Assoc [("cmd", `String s)]
    | Loop loc -> `Assoc[("cmd", `String "Loop")]
    | Skip -> `Assoc[("cmd", `String "SKIP")]
    | Phi -> `Assoc[("cmd", `String "Phi")]
    | UNK0 -> `String "ERROR_UNK_COND"
    | Err -> `String "ERROR"
                          
    (* | _ -> `String "" *)
end

module Node = IntraCfg.Node                 
module InterNode = InterCfg.Node
(* module IntraNode = IntraCfg.Node *)
module G = Graph.Persistent.Digraph.ConcreteBidirectional(Node)

type inter_node = InterNode.t
(* type intra_node = IntraNode.t *)
type node = Node.t
type cmd  = MyCmd.t

type t = {
    graph       : G.t;
    cmd_map     : (node, cmd) BatMap.t;
    du_map      : (node * node, string) BatMap.t;
    (*    node_map    : (intra_node, node) BatMap.t; *)
  }
                    

           
let simplify_unknown : t -> t =
  fun g -> 
  let unk_nodes = BatMap.foldi (fun k v res ->
                       match v with
                       | MyCmd.UNK1 lvl -> unk_conds := (lvl :: !unk_conds);  k :: res
                       | _ -> res
                     ) g.cmd_map []
  in
  List.fold_left (fun g' n ->
                    let preds = G.pred g'.graph n in
                    assert (List.length preds = 1);
                    let pre = List.hd preds in
                    
                    let ss = G.succ g'.graph n in
                    assert (List.length ss = 1);
                    let s0 = List.hd ss in
                    let c_s0 = BatMap.find s0 g'.cmd_map in
                    assert (c_s0 = MyCmd.Skip);

                    let ss = G.succ g'.graph s0 in
                    assert (List.length ss = 1);
                    let s1 = List.hd ss in                    
                    let c_s1 = BatMap.find s1 g'.cmd_map in
                    let is_if = match c_s1 with MyCmd.If _ -> true | _ -> false in
                    assert(is_if);

                    let ss = G.succ g'.graph s1 in
                    let b0 = List.nth ss 0 in
                    let b1 = List.nth ss 1 in

                    let graph = G.add_edge g'.graph pre s1 in
                    let graph = List.fold_left (fun tg n ->
                                    G.add_edge tg s1 n
                                  ) graph (G.succ graph b0)
                    in
                    let graph = List.fold_left (fun tg n ->
                                    G.add_edge tg s1 n
                                  ) graph (G.succ graph b1)
                    in
                      
                    let graph = G.remove_vertex graph n in
                    let graph = G.remove_vertex graph s0 in
                    let graph = G.remove_vertex graph b0 in
                    let graph = G.remove_vertex graph b1 in

                    let cmd_map = BatMap.remove n g'.cmd_map in
                    let cmd_map = BatMap.remove s0 cmd_map in
                    let cmd_map = BatMap.remove b0 cmd_map in
                    let cmd_map = BatMap.remove b1 cmd_map in

                    let du_map = BatMap.filter (fun k v ->
                                     let (src,dst) = k in
                                     not (src = n || src = s0 || src = b0 || src = b1 ||
                                             dst = n || dst = s0 || dst = b0 || dst = b1)
                                   ) g'.du_map
                    in
                    
                    
                    {graph = graph; cmd_map = cmd_map; du_map = du_map }
                  ) g unk_nodes


(* remove skip that has 
- single pred and 
- single succ and 
- is not invovled in data-flow (i.e. not a potential phi) 
*)
                 
let remove_unnecessary_skip : t -> t
  = fun g ->
  let useless_skips = BatMap.foldi (fun k v res ->
                          match v with
                          | MyCmd.NOOP _ (* return *)
                            | MyCmd.Skip ->
                             begin
                               let preds = G.pred g.graph k in
                               let succs = G.succ g.graph k in
                               let du_map = BatMap.filter (fun (src,dst) v ->
                                                src = k || dst = k
                                              ) g.du_map
                               in
                               if List.length preds = 1 && List.length succs = 1 && du_map = BatMap.empty then
                                   k :: res
                               else
                                 res
                             end
                          | _ -> res
                        ) g.cmd_map []
  in
    List.fold_left (fun g' n -> g' ) g useless_skips

            
let label_phi_node : t -> t =
  fun g ->
  let loop_nodes = BatMap.foldi (fun k v res ->
                       match v with
                       | MyCmd.Loop _ -> k :: res
                       | _ -> res
                     ) g.cmd_map []
  in
  List.fold_left (fun g' n ->
                    let ns = G.succ g'.graph n in
                    let n' = List.hd ns in
                    let c = BatMap.find n' g'.cmd_map in
                    assert (c = MyCmd.Skip);
                    assert (List.length ns = 1);
                    {g' with cmd_map = BatMap.add n' MyCmd.Phi g'.cmd_map }
                  ) g loop_nodes


let reform_graph global dug =
  (global, dug)

let empty : t  = { graph = G.empty; cmd_map = BatMap.empty; du_map = BatMap.empty }
    
let from_intra_cfg : IntraCfg.t -> t
  = fun g ->
  empty
  (* copy IntraCfg.graph to current graph *)
  |> IntraCfg.fold_edges (fun src dst ng -> {ng with graph = (G.add_edge ng.graph src dst)}) g
  |> IntraCfg.fold_node (fun v ng ->
         let cmd = IntraCfg.find_cmd v g in
         let new_cmd = MyCmd.fromIntraCfgCmd cmd in
         { ng with cmd_map = BatMap.add v new_cmd ng.cmd_map }
       ) g

let incorporate_dug : (inter_node * inter_node * string) list -> t -> t
  = fun dug_edges ng ->
  ng |> list_fold (fun (src,dst,s) ng ->
            let src_node = InterNode.get_cfgnode src in
            let dst_node = InterNode.get_cfgnode dst in
            assert (G.mem_vertex ng.graph src_node );
            assert (G.mem_vertex ng.graph dst_node );
            { ng with du_map = BatMap.add (src_node, dst_node) s  ng.du_map }
          ) dug_edges

let find_cmd : node -> t ->  cmd
  = fun n g -> BatMap.find n g.cmd_map


              
let to_json : t -> json
  = fun g ->
  let nodes = `Assoc (G.fold_vertex (fun v nodes ->
                          (Node.to_string v, MyCmd.cmd_to_json (find_cmd v g))::nodes
                        ) g.graph [])
  in
  let collect_edges graph =  `List (G.fold_edges (fun v1 v2 edges ->
                         (`List [`String (Node.to_string v1);
                                 `String (Node.to_string v2)
                         ])::edges) graph [])
  in
  let control_edges = collect_edges g.graph in
  let dataflow_edges = `List (BatMap.foldi (fun k v res ->
                                  let s,d = k in
                                  (`List [`String (Node.to_string s);
                                          `String (Node.to_string d);
                                          `String v
                                  ]) :: res
                                ) g.du_map [])  in
  `Assoc [("nodes", nodes);
          ("control-flow", control_edges);
          ("data-flow", dataflow_edges);
    ]


               
let print_graph : InterCfg.t -> (inter_node list) * (inter_node * inter_node * string) list -> unit
  = fun g (dug_nodes, dug_edges) ->
  prerr_endline("Ready to go!!");

  let main_cfg = InterCfg.cfgof g "main" in
  let main_dug_edges = List.filter (fun (src, dst, s) ->
                           InterNode.get_pid src = "main" && InterNode.get_pid dst = "main"
                         ) dug_edges  in

  main_cfg
  |> from_intra_cfg
  |> incorporate_dug main_dug_edges
  |> label_phi_node
  |> simplify_unknown
  |> to_json
  |> Yojson.Safe.pretty_to_channel stdout;
  ()
