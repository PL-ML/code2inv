
(**

Interface of extracting graphs for Deep Learning tasks
 
**)


module MyCmd : sig
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


  val fromIntraCfgCmd : IntraCfg.Cmd.t -> t
  val to_string : t -> string
  val cmd_to_json : t -> Yojson.Safe.json

end

(** type for extractGraph **)
type t

(** convert to json format **)
val to_json : t -> Yojson.Safe.json

type inter_node = BasicDom.Node.t


val print_graph : InterCfg.t -> (inter_node list) * (inter_node * inter_node * string) list -> unit
                                                                               
                     
