
(**

Interface of extracting graphs for Deep Learning tasks
 
**)


module MyCmd : sig
  type t = cmd
             
  and cmd =
    | If of exp * block * block * location
    | Loop of location
    | Assgn of lval * exp * location
    | Assert of exp * location
    | Assume of exp * location
    | Phi of lval list
    | UNK1 of lval
    (* | UNK0  *)
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

  val from_intra_cmd : IntraCfg.Cmd.t -> (subscript_map * subscript_map) -> t

  (* val fromIntraCfgCmd : IntraCfg.Cmd.t -> t
   * val to_string : t -> string
   * val cmd_to_json : t -> Yojson.Safe.json *)

end

(** type for extractGraph **)
type t
and node = IntraCfg.Node.t
and cmd = MyCmd.t

module NodeSet : BatSet.S with type elt = IntraCfg.Node.t

val empty : t


val nodesof : t -> node list

(* val entryof : t -> node
 * val exitof : t -> node *)

(** {2 Predecessors and Successors } *)

val pred : node -> t -> node list
val succ : node -> t -> node list


(** {2 Graph Manipulation } *)

val add_cmd : node -> cmd -> t -> t
(*
val add_new_node : node -> cmd -> node -> t -> t
val add_node_with_cmd : node -> cmd -> t -> t
val add_edge : node -> node -> t -> t
val remove_node : node -> t -> t

 *)

val prepare_for_token : t -> (string BatSet.t) * (string BatSet.t) * ( (Boogie.Node.t * Boogie.Node.t) list )
val prepare_for_c : t -> (string BatSet.t) * (string BatSet.t) * ( (Boogie.Node.t * Boogie.Node.t) list )

val prepare_for_boogie : t -> (string BatSet.t) * (string BatSet.t) * ( (Boogie.Node.t * Boogie.Node.t) list )
val prepare_for_sygus : t -> (string BatSet.t) * (string BatSet.t) * ( (Boogie.Node.t * Boogie.Node.t) list )
val record_vars_for_boogie : t -> string BatSet.t -> t
val record_consts_for_sygus : t -> string BatSet.t -> t

val get_help_cmd : t -> node -> (string * node list) option
val update_help_map : t -> node -> (string * node list) -> t
val new_phi_before : t -> string -> node -> t
                        
(** {2 Dominators } *)

val compute_dom : t -> t

(** [dom_fronts n g] returns dominance frontiers of node [n] in graph [g] *)
val dom_fronts : node -> t -> NodeSet.t
val children_of_dom_tree : node -> t -> NodeSet.t
val parent_of_dom_tree : node -> t -> node option

              
val from_intra_cfg : IntraCfg.t -> t
                                     
val print_graph : t -> unit

val simplify_unknown : t -> t
val remove_unknown_phi : t -> t
val remove_unnecessary_skip : t -> t
val simplify_control_dependency : t -> t
