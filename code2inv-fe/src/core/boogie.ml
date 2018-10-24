

let var_list_str = ref ""

module Node = struct
  type t = Node of int * string * string
  let equal n1 n2 =
    let Node (i1,a1,b1) = n1 in
    let Node (i2,a2,b2) = n2 in
    (i1 = i2 && a1 = a2 && b1 = b2)

  let hash = Hashtbl.hash
  let compare n1 n2 =
    begin
      let Node(i1,a1,b1) = n1 in
      let Node(i2,a2,b2) = n2 in
      if i1 < i2 then -1
      else if i1 = i2 && a1 < a2 then -1
      else  if i1=i2 && a1 = a2 && b1 < b2 then -1
      else  if i1=i2 && a1 = a2 && b1 = b2 then 0
      else 1
    end

  let show : t -> unit
    = fun nd ->
      let Node (i,ty, cmd) = nd in
      prerr_endline ("i=" ^ (string_of_int i) ^ "; ty=" ^ ty ^"; cmd=" ^ cmd )
        

end

module G = Graph.Persistent.Digraph.ConcreteBidirectional(Node)


type node = Node.t
              
type t = {
  consts       : string BatSet.t;
  vars       : string BatSet.t;
  graph     : G.t;
  dom_tree  : dom_tree
}
and dom_tree = G.t

let empty = {
  consts = BatSet.empty;
  vars = BatSet.empty;
  graph = G.empty;
  dom_tree = G.empty;
}

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
module Dom = Graph.Dominator.Make_graph(GDom)

let find_entry : t -> node
  = fun g ->
    let graph = g.graph in
    let candidates = G.fold_vertex (fun node ls ->
        (* prerr_endline "";
         * Node.show node; *)
        let preds = G.pred graph node in
        (* prerr_endline "its preds: [";
         * List.iter Node.show preds;
         * prerr_endline "]"; *)
          
        if List.length preds = 0 then
          node :: ls
        else ls
      ) graph []
    in
    List.iter Node.show  candidates;
    assert ( List.length candidates = 1);
    List.hd candidates

let compute_dom : t -> t
  =fun g ->
    let entry_node = find_entry g in
    let dom_functions = Dom.compute_all (GDom.fromG g.graph) entry_node in
    let dom_tree =
      G.fold_vertex (fun node dom_tree ->
          List.fold_left (fun dom_tree child ->
              G.add_edge dom_tree node child
            ) dom_tree (dom_functions.Dom.dom_tree node)
        ) g.graph  G.empty
    in
    { g with dom_tree = dom_tree }

(* let to_boogie : ExtractSSAGraph.t -> t
 * = fun g -> empty *)

let init : (string BatSet.t) * (string BatSet.t) * ((Node.t * Node.t) list) -> t
  = fun (vars, consts, ls) ->
    let graph = List.fold_left (fun g (n1,n2) ->
        G.add_edge g n1 n2
      ) G.empty ls
    in
    { empty with graph = graph; vars = vars; consts = consts }
    |> compute_dom


let rec to_string_helper : int -> t -> Node.t -> string
  = fun indent g v ->
    let rec get_indent i =
      if i < indent then "  " ^ (get_indent (i+1))
      else ""
    in
    let ws = get_indent 0 in
        
    let rec ignore_phis src =
      let Node.Node (_, ty, cmd) = src in
      if ty = "phi" then
          let ss = G.succ g.graph src in
          let len = List.length ss in
          assert (len = 1);
          ignore_phis (List.hd ss)
      else src
    in
      
    let simplify_if nd =
      prerr_endline "simplify_if:";
      Node.show nd;
      let Node.Node (_,ty, cmd) = nd in
      assert (ty = "if" || ty = "loop");
      let ss = G.succ g.graph nd in
      (* Let's assume we always have both branches *)
      assert( List.length ss = 2);
      let b0 = List.nth ss 0 in
      let b1 = List.nth ss 1 in
      let no_swap = match b0 with Node.Node (_,"tb",_) -> true | _ -> false in
      if no_swap then (cmd, b0, b1)
      else (cmd, b1, b0)
    in

    let check_dom_then_dive src =
      prerr_endline "check_dom_then_dive:";
      Node.show src;
      
      let ss = G.succ g.graph src in
      if ss = [] then "" (* reach exit *)
      else
        begin
          let len = List.length ss in
          assert (len = 1);
          let suc = List.hd ss in
          let ds = G.pred g.dom_tree suc in
          let dom = List.hd ds in
          if src = dom then
            (* dominates the successor, good to dive in *)
            to_string_helper indent g suc
          else
            (* the successor should be visied earlier, stop *)
            ""
        end
    in
    Node.show v;
    
    (* let (nd, str) = go_straight v "" in *)
    let (nd,str) = (v, "") in
    let Node.Node (_,ty,cmd) = nd in
    match ty with
    | "if" ->
      prerr_endline ("now in if: " ^ cmd );
      let res =  str ^ ws ^ "if(" ^ cmd ^ ") {\n" in
      let (cmd, tb, fb) = simplify_if nd in
      let t_str = to_string_helper (indent+1) g tb in
      prerr_endline ("in if, got t_sr: " ^ t_str);
      let f_str = to_string_helper (indent+1) g fb in
      prerr_endline ("in if, got f_sr: " ^ f_str);

      let if_block = res ^ t_str ^ ws ^ "}\n" ^ ws ^ "else{\n" ^ f_str ^ ws ^ "}\n" in
      (* check things after if(){}{} xxx  *)
      let dom_succ = G.succ g.dom_tree nd in
      let ns = List.filter (fun x -> x != tb && x != fb) dom_succ in
      assert(List.length ns <= 1);
      if List.length ns = 1 then
        let if_after = to_string_helper (indent) g (List.hd ns) in
        if_block ^ if_after
      else
        if_block
        
    | "loop" ->
      prerr_endline ("now in loop: " ^ cmd );
      let ss = G.succ g.graph nd in
      assert (List.length ss = 1);
      
      let nd = ignore_phis (List.hd ss) in
      (* then what follows must be if *)
      let (cmd, tb, fb) = simplify_if nd in
      let res = str ^ ws ^ "while(" ^ cmd ^ ")\n" in
      let t_str = to_string_helper (indent+1) g tb in
      prerr_endline ("in loop, got t_sr: " ^ t_str);
      let f_str = to_string_helper (indent) g fb in
      prerr_endline ("in loop, got f_sr: " ^ f_str);

      let res_inv =  res ^ ws ^ "invariant H(" ^ !var_list_str ^ ");\n" ^ ws ^ "{\n" in
      
      res_inv ^ t_str ^ ws ^ "}\n" ^ ws  ^ f_str ^ "\n"

    | "phi"-> str ^ ws ^ "//phi \n" ^ (check_dom_then_dive nd)
    | "tb" -> str ^ ws ^ "//tb \n"  ^ (check_dom_then_dive nd)
    | "fb" -> str ^ ws ^ "//fb \n"  ^ (check_dom_then_dive nd)
    | "skip" -> str ^ ws ^ "//skip \n"  ^ (check_dom_then_dive nd) 
    | "assume" -> str ^ ws ^ "assume " ^ cmd ^ ";\n"  ^ (check_dom_then_dive nd) 
    | "assert" -> str ^ ws ^ "assert " ^ cmd ^ ";\n"  ^ (check_dom_then_dive nd) 
    | "assgn" -> str ^ ws ^ cmd ^ ";\n"  ^ (check_dom_then_dive nd) 

    | _ -> raise (Failure "to_string_helper: unexpected return from go_straight")



let to_string : t -> string
  = fun g ->
    let f_inv = "function {:existential true} H(" in 
    prerr_endline "step-1";
    let vs = BatSet.to_list g.vars in
    prerr_endline "step-2";
    let rec append_var i ty s =
      if i >= List.length vs then s
      else
        begin
          let s = if i > 0 then  s ^ "," ^ (List.nth vs i) ^ ty
            else s ^ (List.nth vs i) ^ ty
          in
          append_var (i+1) ty s
        end
    in

    var_list_str := (append_var 0 "" "");
    let f_inv = (append_var 0 ":int" f_inv) ^ ") returns (bool) {\ninvariant_place_holder\n}\n\n" in
    let p = f_inv ^ "procedure main()\n{\n  var " ^ !var_list_str ^ ": int;\n" in
    
    prerr_endline ("p: " ^ p);
    prerr_endline "step-3";

    let entry = find_entry g in

    prerr_endline "step-4";

    let body = to_string_helper 1 g entry in

    p ^ body ^ "\n}\n"


let print_boogie : t -> unit
  = fun g ->
    g
    |> to_string
    |> Printf.fprintf stdout "%s"
