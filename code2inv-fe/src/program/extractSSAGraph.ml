(** Implementation  **)

open IntraCfg (* access IntraCfg.Cmd *)
open Vocab (* contains *)


type json = Yojson.Safe.json


let unk_conds = ref []


module MyCmd = struct
  type t = cmd

  and cmd =
    | If of exp * block * block * location
    | Loop of location
    | Assgn of lval * exp * location
    | Assert of exp * location
    | Assume of exp * location
    | Phi of lval list
    | UNK1 of lval
    (* | UNK0 *)
    | Skip
    | TBranch
    | FBranch 
    | Err


  and exp =
    | Const  of constant
    | Lval   of lval
    | UnOp   of unop * exp * typ
    | BinOp  of binop * exp * exp * typ

  (* and lval = lhost * offset * subscript *)
  and lval = string * subscript
  and subscript = int

  and block = Cil.block
  and location = Cil.location
  and lhost = Cil.lhost
  and offset = Cil.offset
  and constant = Cil.constant
  and unop = Cil.unop
  and binop = Cil.binop
  and typ = Cil.typ

  type subscript_map = (string, int) BatMap.t

  let rec from_cil_exp : Cil.exp -> subscript_map -> exp
    = fun exp sub_map ->
      begin
        match exp with
        | Cil.Const c -> Const c
        | Cil.Lval l -> Lval (from_cil_lval l sub_map)
        | Cil.UnOp (u, e, typ) -> UnOp (u, from_cil_exp e sub_map, typ)
        | Cil.BinOp (b, e1, e2, typ) ->
          BinOp (b,
                 from_cil_exp e1 sub_map,
                 from_cil_exp e2 sub_map,
                 typ)
        | _ -> raise (Failure ("from_cil_exp: unhandled cil exp" ^ (CilHelper.s_exp exp)))

      end

  and from_cil_lval : Cil.lval -> subscript_map -> lval
    = fun lvl sub_map ->
      let (lh,offset) = lvl in
      begin
        match lh with
        | Cil.Var vi ->
          let v_str = vi.vname in
          (* my_prerr_endline ("try to find vi.vname: " ^ v_str); *)
          let sub = BatMap.find v_str sub_map in
          (v_str, sub)
        | _ -> raise (Failure ("from_cil_lval: unhandled cil lval:" ^ (CilHelper.s_lv lvl)))
      end

  let resolve_call : Cil.lval option -> Cil.exp -> Cil.exp list -> Cil.location
    -> (subscript_map * subscript_map) -> t
    = fun tmp fexp params loc (def_map, use_map) ->
      begin
        let fn_name = CilHelper.s_exp fexp in
        if contains fn_name "unknown" then
          begin
            (* my_prerr_endline "process unknown call ..."; *)

            match tmp with
            | Some lval -> UNK1 (from_cil_lval lval def_map)
            | None -> (* UNK0 *) raise (Failure ("resolve_call: useless unknown function: " ^ fn_name))
          end
        else if contains fn_name "assert" && List.length params == 1 then
          begin
            (* prerr_endline "process assert call ..."; *)
            let ae = from_cil_exp (List.hd params) use_map in
            Assert (ae, loc)
          end
        else if contains fn_name "assume" && List.length params == 1 then
          begin
            (* prerr_endline "process assume call ..."; *)
            (*this is needed, as sparrow fail to catch some assume call*)
            let ae = from_cil_exp (List.hd params) use_map in
            Assume (ae, loc)
          end
        else
          raise (Failure ("unhandled function call in resolve_call " ^ fn_name))
      end

  let from_intra_cmd : Cmd.t -> (subscript_map * subscript_map) -> t
    = fun c (def_map, use_map) ->
      match c with
      | Cmd.Cset (lv, exp, loc) -> Assgn (from_cil_lval lv def_map,
                                          from_cil_exp exp use_map,
                                          loc)

      | Cmd.Cif (exp, b1, b2, loc) -> If (from_cil_exp exp use_map, b1, b2, loc)
      | Cmd.CLoop loc -> Loop loc
      | Cmd.Ccall (tmp, fexp, params, loc) -> resolve_call tmp fexp params loc (def_map,use_map)
      | Cmd.Cskip -> Skip
      | Cmd.Cassume (Cil.UnOp (Cil.LNot, _, _), _) -> FBranch
      | Cmd.Cassume (exp,loc) -> TBranch
      | Cmd.Creturn (_, loc) -> Skip 
      | _ -> raise (Failure ("from_intra_cmd failed to match cmd: " ^ (Cmd.to_string c)))


  let rec exp_to_json : exp -> json
    = fun exp ->
      match exp with
      | Const c -> `Assoc [("Const", `String (CilHelper.s_const c)); ]
      | Lval lv -> lval_to_json lv
      | UnOp (u, e, typ) -> `Assoc [("OP", `String (CilHelper.s_uop u) );
                                    ("arg1", exp_to_json e);]

      | BinOp (b, e1, e2, typ) -> `Assoc [("OP", `String (CilHelper.s_bop b) );
                                          ("arg1", exp_to_json e1);
                                          ("arg2", exp_to_json e2);]       
  and lval_to_json : lval -> json
    = fun lv ->
      let (s,i) = lv in
      begin
        if List.mem s !unk_conds then
          `Assoc [("UNK", `String "UNK_VAL");]
        else
          `Assoc [("Var", `String (Printf.sprintf "%s_%d" s i)); ]
      end

  and phi_to_json : lval list -> json
    = fun args ->
      let rec append i =
        if i < List.length args then
          let res = append (i+1) in
          let arg = List.nth args i in
          let arg_str = ("arg" ^ (string_of_int i), lval_to_json arg) in
          arg_str :: res
        else []
      in
      let assoc_ls = append 0 in
      `Assoc ( ("OP", `String "phi_merge") :: assoc_ls)



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

      | Loop loc -> `Assoc[("cmd", `String "Loop")]
      | Phi ls -> `Assoc[("cmd", `String "Phi");
                         ("lval", lval_to_json (List.hd ls));
                         ("rval", phi_to_json (List.tl ls));]
      | Skip -> `Assoc[("cmd", `String "SKIP")]
      | TBranch -> `Assoc [ ("cmd", `String "TrueBranch") ]
      | FBranch -> `Assoc [ ("cmd", `String "FalseBranch") ]                  
      (* | UNK0 -> `String "ERROR_UNK_COND" *)
      | Err -> `String "ERROR"

  let rec exp_to_boogie : exp -> string
    = fun exp ->
      match exp with
      | Const c ->  CilHelper.s_const c
      | Lval lv -> lval_to_boogie lv
      | UnOp (u, e, typ) ->
        Printf.sprintf "%s(%s)" (CilHelper.s_uop u) (exp_to_boogie e)
      | BinOp (b, e1, e2, typ) ->
        Printf.sprintf "((%s) %s (%s))" (exp_to_boogie e1) (CilHelper.s_bop b) (exp_to_boogie e2)

  and lval_to_boogie : lval -> string
    = fun lv ->
      let (s,i) = lv in
      begin
        if List.mem s !unk_conds then "*"
        else s
      end


  let cmd_to_boogie : t -> string * string =
    fun c ->
      match c with
      | If (Lval lv, _, _, loc) -> ("if", lval_to_boogie lv)
      | If (exp, _,_,_) -> ("if", exp_to_boogie exp)
      | Assgn (lv, e, _) ->
        ("assgn", Printf.sprintf "%s := %s" (lval_to_boogie lv) (exp_to_boogie e))
      | Assume (e, _) -> ("assume", exp_to_boogie e)
      | Assert (e, _) -> ("assert", exp_to_boogie e)
      | Loop loc -> ("loop", "")
      | Phi ls -> ("phi", "")
      | TBranch -> ("tb", "")
      | FBranch -> ("fb", "")
      | Skip -> ("skip", "")
      | _ -> raise (Failure "cmd_to_boogie: unexpected case")

  let cmd_to_c : t -> string * string =
    fun c ->
      match c with
      | If (Lval lv, _, _, loc) -> ("if", lval_to_boogie lv)
      | If (exp, _,_,_) -> ("if", exp_to_boogie exp)
      | Assgn (lv, e, _) ->
        ("assgn", Printf.sprintf "%s = %s" (lval_to_boogie lv) (exp_to_boogie e))
      | Assume (e, _) -> ("assume", exp_to_boogie e)
      | Assert (e, _) -> ("assert", exp_to_boogie e)
      | Loop loc -> ("loop", "")
      | Phi ls -> ("phi", "")
      | TBranch -> ("tb", "")
      | FBranch -> ("fb", "")
      | Skip -> ("skip", "")
      | _ -> raise (Failure "cmd_to_c: unexpected case")

  let rec exp_to_json_linear : exp -> json list
    = fun exp ->
      match exp with
      | Const c -> [ `Assoc [("Const", `String (CilHelper.s_const c)); ] ]
      | Lval lv -> [lval_to_json_linear lv]
      | UnOp (u, e, typ) -> 
        (* `Assoc [("OP", `String (CilHelper.s_uop u) );
                                    ("arg1", exp_to_json_linear e);] *)
        [ (`String (CilHelper.s_uop u))] @ (exp_to_json_linear e)

      | BinOp (b, e1, e2, typ) -> 
      (* `Assoc [("OP", `String (CilHelper.s_bop b) );
                                          ("arg1", exp_to_json_linear e1);
                                          ("arg2", exp_to_json_linear e2);]        *)
        (exp_to_json_linear e1) @ [ (`String (CilHelper.s_bop b))] @ (exp_to_json_linear e2)
        
  and lval_to_json_linear : lval -> json
    = fun lv ->
      let (s,i) = lv in
      begin
        if List.mem s !unk_conds then
          `Assoc [("UNK", `String "UNK_VAL");]
        else
          `Assoc [("Var", `String (Printf.sprintf "%s_%d" s i)); ]
      end


  let cmd_to_token : t -> string * string =
    fun c -> 
    let (typ_str, _) = cmd_to_c c in 
    let json_str =  match c with
      | If (e,b1,b2,loc) -> 
          (* `Assoc [ ("cmd", `String "if"); ("rval", exp_to_json e) ] *)
          `List (exp_to_json_linear e)
      | Assgn (lv, e, loc) -> 
          (* `Assoc [("cmd", `String "assign");
                                      ("lval", lval_to_json lv);
                                      ("rval", exp_to_json e) ] *)
         `List (  [ lval_to_json lv ] @ [ (`String "assign") ] @ (exp_to_json_linear e) @ [(`String ";")] )

      | Assume (e, loc) ->  
      (* `Assoc [("cmd", `String "Assume");
                                    ("rval", exp_to_json e) ] *)

        `List ( [(`String "Assume")] @ (exp_to_json_linear e) @ [(`String ";")]  )

      | Assert (e, loc) ->  
      (* `Assoc [("cmd", `String "Assert");
                                    ("rval", exp_to_json e) ] *)
        `List ( [(`String "Assert")] @ (exp_to_json_linear e) @ [(`String ";")]  )

      | UNK1 lv -> 
      (* `Assoc[ ("cmd", `String "UNK_COND");
                           ("lval", lval_to_json lv);] *)
        `List ([ lval_to_json_linear lv ])

      | Loop loc -> 
      (* `Assoc[("cmd", `String "Loop")] *)
      `List []
      | Phi ls -> 
      (* `Assoc[("cmd", `String "Phi");
                         ("lval", lval_to_json (List.hd ls));
                         ("rval", phi_to_json (List.tl ls));] *)
      `List []

      | Skip -> 
      (* `Assoc[("cmd", `String "SKIP")] *)
      `List []
      | TBranch -> 
      (* `Assoc [ ("cmd", `String "TrueBranch") ] *)
      `List []
      | FBranch -> 
      (* `Assoc [ ("cmd", `String "FalseBranch") ]                   *)
      `List []

      (* | UNK0 -> `String "ERROR_UNK_COND" *)
      | Err -> `String "ERROR"
    in 
    (* let json_str = Yojson.Safe.to_string (cmd_to_json c) in  *)
    (typ_str, Yojson.Safe.to_string json_str)

  let rec exp_to_sygus : exp -> string
    = fun exp ->
      match exp with
      | Const c ->  CilHelper.s_const c
      | Lval lv -> lval_to_sygus lv
      | BinOp (b, e1, e2, typ) ->
        Printf.sprintf "(%s %s  %s)" (CilHelper.s_bop b) (exp_to_sygus e1) (exp_to_sygus e2)
      | UnOp (u, e, typ) -> raise (Failure ("unhandled UnOp: " ^ (CilHelper.s_uop u)))

  and lval_to_sygus : lval -> string
    = fun lv ->
      let (s,i) = lv in
      begin
        if List.mem s !unk_conds then "*"
        else (Printf.sprintf "%s_%d" s i)
      end

  let cmd_to_sygus : t -> string * string =
    fun c ->
      match c with
      | If (Lval lv, _, _, loc) -> ("if", lval_to_sygus lv)
      | If (exp, _,_,_) -> ("if", exp_to_sygus exp)
      | Assgn (lv, e, _) ->
        prerr_endline "hanlde assignment" ;
        ("assgn", Printf.sprintf "(= %s %s)" (lval_to_sygus lv) (exp_to_sygus e))
      | Assume (e, _) -> ("assume", exp_to_sygus e)
      | Assert (e, _) -> ("assert", exp_to_sygus e)
      | Loop loc -> ("loop", "")
      | Phi ls -> 
        let phi_def = List.fold_right (fun lv res -> (lval_to_sygus lv) ^ " " ^ res) ls "" in 
        ("phi",  "(phi " ^ phi_def ^ ")")
      | TBranch -> ("tb", "")
      | FBranch -> ("fb", "")
      | Skip -> ("skip", "")
      | _ -> raise (Failure "cmd_to_boogie: unexpected case")


end

(* module Node = IntraCfg.Node                 
 * module InterNode = InterCfg.Node *)
(* module IntraNode = IntraCfg.Node *)
module G = Graph.Persistent.Digraph.ConcreteBidirectional(Node)

module NodeSet = BatSet.Make(Node)

(* type inter_node = InterNode.t *)
(* type intra_node = IntraNode.t *)
type node = Node.t
type cmd  = MyCmd.t

module GDom = struct
  module V = Node
  type t = G.t
  let empty = G.empty
  let fromG g = g
  let pred = G.pred
  let succ = G.succ
  let fold_vertex = G.fold_vertex
  let iter_vertex = G.iter_vertex
  let iter_succ = G.iter_succ
  let nb_vertex = G.nb_vertex
  let add_edge g a b = ()
  let create : ?size:int -> unit -> t = fun ?size:int () -> empty
end

module Dom = Graph.Dominator.Make_graph (GDom)


type t = {
  consts        : string BatSet.t;
  vars        : string BatSet.t;
  graph       : G.t;
  cmd_map     : (node, cmd) BatMap.t;
  help_map    : (node, (string * node list) option) BatMap.t;
  dom_fronts  : dom_fronts;
  dom_tree    : dom_tree;
}
and dom_fronts = (Node.t, NodeSet.t) BatMap.t
and dom_tree = G.t

let empty : t = {
  consts       = BatSet.empty;
  vars       = BatSet.empty;
  graph      = G.empty;
  cmd_map    = BatMap.empty;
  help_map   = BatMap.empty;
  dom_fronts = BatMap.empty;
  dom_tree   = G.empty;
}

(* let entryof _ = IntraCfg.entryof IntraCfg.empty
 * let exitof _ = IntraCfg.exitof IntraCfg.empty *)

let prepare_for_token : t -> (string BatSet.t) * (string BatSet.t) * ((Boogie.Node.t * Boogie.Node.t) list)
  = fun g ->
    let edges = 
      G.fold_edges (fun v1 v2 ls ->
          let i1 = IntraCfg.Node.id v1 in
          let i2 = IntraCfg.Node.id v2 in
          let c1 = BatMap.find v1 g.cmd_map in
          let c2 = BatMap.find v2 g.cmd_map in
          let (a,b) = MyCmd.cmd_to_token c1 in
          let (c,d) = MyCmd.cmd_to_token c2 in
          (Boogie.Node.Node (i1,a,b), Boogie.Node.Node (i2,c,d)) :: ls
        ) g.graph []
    in
    (g.vars, g.consts, edges)


let prepare_for_c : t -> (string BatSet.t) * (string BatSet.t) * ((Boogie.Node.t * Boogie.Node.t) list)
  = fun g ->
    let edges = 
      G.fold_edges (fun v1 v2 ls ->
          let i1 = IntraCfg.Node.id v1 in
          let i2 = IntraCfg.Node.id v2 in
          let c1 = BatMap.find v1 g.cmd_map in
          let c2 = BatMap.find v2 g.cmd_map in
          let (a,b) = MyCmd.cmd_to_c c1 in
          let (c,d) = MyCmd.cmd_to_c c2 in
          (Boogie.Node.Node (i1,a,b), Boogie.Node.Node (i2,c,d)) :: ls
        ) g.graph []
    in
    (g.vars, g.consts, edges)


let prepare_for_boogie : t -> (string BatSet.t) * (string BatSet.t) * ((Boogie.Node.t * Boogie.Node.t) list)
  = fun g ->
    let edges = 
      G.fold_edges (fun v1 v2 ls ->
          let i1 = IntraCfg.Node.id v1 in
          let i2 = IntraCfg.Node.id v2 in
          let c1 = BatMap.find v1 g.cmd_map in
          let c2 = BatMap.find v2 g.cmd_map in
          let (a,b) = MyCmd.cmd_to_boogie c1 in
          let (c,d) = MyCmd.cmd_to_boogie c2 in
          (Boogie.Node.Node (i1,a,b), Boogie.Node.Node (i2,c,d)) :: ls
        ) g.graph []
    in
    (g.vars, g.consts, edges)

let record_vars_for_boogie : t -> string BatSet.t -> t
  = fun g vars ->
    {g with vars = vars}


let prepare_for_sygus : t -> (string BatSet.t) * (string BatSet.t) * ((Boogie.Node.t * Boogie.Node.t) list)
  = fun g ->
    let edges = 
      G.fold_edges (fun v1 v2 ls ->
          let i1 = IntraCfg.Node.id v1 in
          let i2 = IntraCfg.Node.id v2 in
          let c1 = BatMap.find v1 g.cmd_map in
          let c2 = BatMap.find v2 g.cmd_map in
          let (a,b) = MyCmd.cmd_to_sygus c1 in
          let (c,d) = MyCmd.cmd_to_sygus c2 in
          (Boogie.Node.Node (i1,a,b), Boogie.Node.Node (i2,c,d)) :: ls
        ) g.graph []
    in
    (g.vars, g.consts, edges)

let record_consts_for_sygus : t -> string BatSet.t -> t
  = fun g consts ->
    {g with consts = consts}

(* TODO: optimize G.pred *)
let pred : node -> t -> node list
  = fun n g -> G.pred g.graph n

let succ : node -> t -> node list
  = fun n g -> G.succ g.graph n

let add_cmd : node -> cmd -> t -> t
  = fun n c g ->
    { g with cmd_map = BatMap.add n c g.cmd_map}

let nodesof : t -> node list
  = fun g -> G.fold_vertex List.cons g.graph []

let dom_fronts node g = BatMap.find node g.dom_fronts

let children_of_dom_tree node g =
  NodeSet.remove node (NodeSet.of_list (G.succ g.dom_tree node))

let parent_of_dom_tree node g =
  match G.pred g.dom_tree node with
  | [] -> None
  | [p] -> Some p
  | _ -> raise (Failure "IntraCfg.parent_of_dom_tree: fatal")

let compute_dom : t -> t
  =fun g ->
    let dom_functions = Dom.compute_all (GDom.fromG g.graph) Node.entry in
    let dom_tree =
      List.fold_left (fun dom_tree node ->
          List.fold_left (fun dom_tree child ->
              G.add_edge dom_tree node child
            ) dom_tree (dom_functions.Dom.dom_tree node)
        ) G.empty (nodesof g)
    in
    let dom_fronts =
      List.fold_left (fun dom_fronts node ->
          BatMap.add node (NodeSet.of_list (dom_functions.Dom.dom_frontier node)) dom_fronts
        ) BatMap.empty (nodesof g)
    in
    {g with dom_tree = dom_tree;
            dom_fronts = dom_fronts}

let get_help_cmd : t -> node -> (string * node list) option
  = fun g nd ->
    BatMap.find nd g.help_map

let update_help_map : t -> node -> (string * node list) -> t
  = fun g nd (v_str, ls) ->
    { g with help_map = BatMap.add nd (Some (v_str,ls)) g.help_map }

let new_phi_before : t -> string -> node -> t
  = fun g var nd ->
    ignore( assert(G.mem_vertex g.graph nd) );
    let new_nd = Node.make() in
    let preds = G.pred g.graph nd in
    let graph = G.add_edge g.graph new_nd nd in
    let graph = List.fold_left (fun graph x ->
        let graph = G.remove_edge graph x nd in
        let graph = G.add_edge graph x new_nd in
        graph
      ) graph preds
    in
    { g with graph = graph;
             help_map = BatMap.add new_nd (Some (var, [nd])) g.help_map }


let find_cmd : node -> t ->  cmd
  = fun n g -> BatMap.find n g.cmd_map

let from_intra_cfg : IntraCfg.t -> t
  = fun cfg ->
    empty
    |> IntraCfg.fold_edges (fun src dst ng -> {ng with graph = (G.add_edge ng.graph src dst)}) cfg
    |> IntraCfg.fold_node (fun node ng -> {ng with help_map = (BatMap.add node None ng.help_map)}) cfg

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

    `Assoc [("nodes", nodes);
            ("control-flow", control_edges);
           ]


let remove_unnecessary_skip : t -> t
  = fun g ->
    let useless_skips =
      BatMap.foldi (
        fun k v res ->
          match v with
          | MyCmd.Skip -> 
            begin
              let preds = G.pred g.graph k in
              let succs = G.succ g.graph k in
              if List.length preds = 1 && List.length succs = 1 then
                k :: res
              else
                res
            end
          | _ -> res
      ) g.cmd_map []
    in
    let ng = List.fold_left (fun g' n ->
        (* remove skip *)
        let preds = G.pred g'.graph n in
        assert (List.length preds = 1);
        let pre = List.hd preds in

        let ss = G.succ g'.graph n in
        assert (List.length ss = 1);
        let s1 = List.hd ss in

        let cmd_map = BatMap.remove n g'.cmd_map in
        let graph = G.remove_vertex g'.graph n in

        let graph = G.add_edge graph pre s1 in 
        {g' with graph=graph; cmd_map = cmd_map; }
      ) g useless_skips
    in
    ng


let is_unknown_phi : node -> t -> bool
  = fun nd g ->
    let cmd = BatMap.find nd g.cmd_map in
    match cmd with
    | MyCmd.Phi (hd::tl) ->
      let (v_str,_) = hd in
      List.mem v_str !unk_conds
    | _ -> false



let remove_unknown_phi : t -> t
  = fun g ->
    let unk_phi = G.fold_vertex (fun v ls ->
        if is_unknown_phi v g then
          v :: ls
        else
          ls
      ) g.graph []
    in
    let ng = List.fold_left (fun g' n ->
        (* remove phi of unknown tmps *)
        let ss = G.succ g'.graph n in
        assert (List.length ss = 1);
        let s1 = List.hd ss in

        let cmd_map = BatMap.remove n g'.cmd_map in
        let graph = G.remove_vertex g'.graph n in

        let preds = G.pred g'.graph n in

        let graph =List.fold_left (fun graph pre -> 
            G.add_edge graph pre s1
          ) graph preds
        in

        {g' with graph=graph; cmd_map = cmd_map; }
      ) g unk_phi
    in
    ng

let simplify_unknown : t -> t
  = fun g ->
    let unk_nodes = BatMap.foldi (fun k v res ->
        match v with
        | MyCmd.UNK1 lvl ->
          let (unk_name,_) = lvl in
          unk_conds := (unk_name :: !unk_conds);
          k :: res
        | _ -> res
      ) g.cmd_map []
    in
    let ng = List.fold_left (fun g' n ->
        (* remove unknown call *)
        let preds = G.pred g'.graph n in
        assert (List.length preds = 1);
        let pre = List.hd preds in

        let ss = G.succ g'.graph n in
        assert (List.length ss = 1);
        let s1 = List.hd ss in                    
        let c_s1 = BatMap.find s1 g'.cmd_map in
        let is_if = match c_s1 with MyCmd.If _ -> true | _ -> false in
        assert(is_if);


        let cmd_map = BatMap.remove n g'.cmd_map in
        let graph = G.remove_vertex g'.graph n in
        let graph = G.add_edge graph pre s1 in

        {g' with graph = graph; cmd_map = cmd_map}

      ) g unk_nodes
    in
    (* further remove unknown phi nodes *)
    remove_unknown_phi ng



let rec compute_indent_level : t -> int -> node  -> (node * int) list  
  = fun g indent v ->
    (* prerr_endline (Printf.sprintf "compute_indent_level: %s"  (Node.to_string v) ) ; *)

    let rec hanlde_phis src =
      let cmd = BatMap.find src g.cmd_map in 
      match cmd with 
      | MyCmd.Phi _ -> 
        let ss = G.succ g.graph src in
        let len = List.length ss in
        assert (len = 1);
        let (after_phi, res) = hanlde_phis (List.hd ss) in 
        let res = (src, (indent + 1)) ::  res in 

        (after_phi, res)

      | _ -> (src, [])
    in

    let handle_if nd =
      (* prerr_endline (Printf.sprintf "handle_if: %s"  (Node.to_string nd) ) ; *)
      let cmd = BatMap.find nd g.cmd_map in 
      match cmd with 
      | MyCmd.If (e,b1,b2, loc) -> 
        let ss = G.succ g.graph nd in
        (* Let's assume we always have both branches *)
        assert( List.length ss = 2);
        let b0 = List.nth ss 0 in
        let b1 = List.nth ss 1 in

        (* we don't care the actual order, e.g. tb/fb or fb/tb *)
        (* (b0,b1) *)

        (* loop cmd does care about the order *)
        let cmd = BatMap.find b0 g.cmd_map in 
        begin 
          match cmd with 
          | MyCmd.TBranch -> (b0,b1) 
          | MyCmd.FBranch -> (b1,b0)
          | _ -> raise (Failure "impossible branch in handle_if")
        end 
      | _ -> raise (Failure "unexpected cmd in handle_if")
    in

    let check_dom_then_dive src indent =
      (* prerr_endline (Printf.sprintf "check_dom_then_dive: src = %s"  (Node.to_string src) ) ; *)
      let ss = G.succ g.graph src in
      if ss = [] then [] (* reach exit *)
      else
        begin
          let len = List.length ss in
          assert (len = 1);
          let suc = List.hd ss in
          (* prerr_endline (Printf.sprintf "check_dom_then_dive: suc = %s"  (Node.to_string suc) ) ; *)
          let ds = G.pred g.dom_tree suc in
          let dom = List.hd ds in
          (* prerr_endline (Printf.sprintf "check_dom_then_dive: dom = %s"  (Node.to_string dom) ) ; *)
          if src = dom then
            (* dominates the successor, good to dive in *)
            compute_indent_level g indent suc
          else
            (* the successor should be visied earlier, stop *)
            []
        end
    in

    let cmd = BatMap.find v g.cmd_map in 
    match cmd with 
    | MyCmd.If (e, b1, b2, loc) -> 
      let (nb1, nb2) = handle_if v in  
      let if_block = (v,indent) :: (compute_indent_level g (indent + 1) nb1) in 
      let if_block = if_block @ (compute_indent_level g (indent + 1) nb2 ) in 

      (* check things after if(){}{} xxx  *)
      let dom_succ = G.succ g.dom_tree v in
      let ns = List.filter (fun x -> x != nb1 && x != nb2) dom_succ in
      assert(List.length ns <= 1);
      if List.length ns = 1 then
        let if_after = compute_indent_level g  indent (List.hd ns) in
        if_block @ if_after
      else
        if_block
    | MyCmd.Loop _ -> 
      let ss = G.succ g.graph v in
      assert (List.length ss = 1);
      let (nd,res) = hanlde_phis (List.hd ss) in

      let res = (v, indent) :: res in 
      let res = (nd, (indent+1))  :: res in 

      (* then what follows must be if *)
      let (tb,fb) = handle_if nd in
      let res = res @ (compute_indent_level g (indent+2)  tb) in 
      let res = res @ (compute_indent_level g (indent+2)  fb) in 
      res 
    | MyCmd.Phi _  
    | MyCmd.Skip 
    | MyCmd.Assume (_,_) 
    | MyCmd.Assert (_,_) 
    | MyCmd.Assgn (_,_,_)
      -> (v,indent) :: (check_dom_then_dive v indent)
    | MyCmd.TBranch 
    | MyCmd.FBranch 
      -> (v,indent) :: (check_dom_then_dive v (indent+1) )
    | _ -> raise (Failure "unexpected case in compute_indent_level ")


let simplify_control_dependency : t -> t 
  = fun g ->

    let g = compute_dom g in 

    (* first compute identation level *)
    let indent_levels = compute_indent_level g 0 Node.entry in 
    let mp = List.fold_right (fun (nd, ind) res -> 
        (* prerr_endline (Printf.sprintf "node: %s  indent: %d" (Node.to_string nd)  ind ) ; *)
        BatMap.add nd ind res 
      ) indent_levels BatMap.empty 
    in 

    let mp = BatMap.add Node.entry (-1) mp in 

    prerr_endline ("compute indent levels is done");

    (* Next, let each node in dom-tree be the direct child of 
       the idom which is exactly one level less
    *)
    let rec go_up v t_ind = 
      (* prerr_endline (Printf.sprintf "go_up: %s"  (Node.to_string v) ) ; *)
      let indent = BatMap.find v mp in 
      assert (indent <= t_ind && indent >= t_ind - 1);
      if indent = t_ind - 1 then v 
      else begin 
        let ds = G.pred g.dom_tree v in
        let dom = List.hd ds in
        go_up dom t_ind 
      end  
    in 

    let simpl_cfg = G.fold_vertex (fun v ng -> 
        (* prerr_endline (Printf.sprintf "simp_cfg: %s"  (Node.to_string v) ); *)

        let ind = BatMap.find v mp in 
        if v = Node.entry || v = Node.exit then ng 
        else 
          G.add_edge ng (go_up v ind) v 
      ) g.graph G.empty
    in 

    {g with graph = simpl_cfg}


let print_graph : t -> unit
  = fun ssa_graph ->
    ssa_graph
    (* |> simplify_unknown
     * |> remove_unnecessary_skip *)
    (* TODO: remove defined but not used phi nodes *)
    |> to_json
    |> Yojson.Safe.pretty_to_channel stdout;
    ()

