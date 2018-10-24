open Boogie

type json = Yojson.Safe.json

let ops = ["+"; "-"]
let inside_loop = ref false 



let decode_to_json : string -> json list 
= fun s ->
  let js = Yojson.Safe.from_string s in 
  match js with 
  | `List ls -> ls 
  | `String x -> [js]
  | _ -> raise (Failure "decode_to_json: unexpected ")


let rec to_json_helper : int -> t -> Node.t -> json list
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
      (* prerr_endline "simplify_if:"; *)
      (* Node.show nd; *)
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
      (* prerr_endline "check_dom_then_dive:"; *)
      (* Node.show src; *)

      let ss = G.succ g.graph src in
      if ss = [] then [] (* reach exit *)
      else
        begin
          let len = List.length ss in
          assert (len = 1);
          let suc = List.hd ss in
          let ds = G.pred g.dom_tree suc in
          let dom = List.hd ds in
          if src = dom then
            (* dominates the successor, good to dive in *)
            to_json_helper indent g suc
          else
            (* the successor should be visied earlier, stop *)
            []
        end
    in
    (* Node.show v; *)

    (* let (nd, str) = go_straight v "" in *)
    let (nd,str) = (v, "") in
    let Node.Node (_,ty,cmd) = nd in
    match ty with
    | "if" ->
      prerr_endline ("now in if: " ^ cmd );
      let cmd = if cmd = "*" then "unknown()" else cmd in 

      (* let res =  str ^ ws ^ "if(" ^ cmd ^ ") {\n" in *)
      let tk_res =  [ (`String "if"); (`String "("); ]  @ (decode_to_json cmd) @ [(`String ")"); (`String "{")] in 

      let (cmd, tb, fb) = simplify_if nd in
      let t_str = to_json_helper (indent+1) g tb in
      (* prerr_endline ("in if, got t_sr: " ^ t_str); *)
      let f_str = to_json_helper (indent+1) g fb in
      (* prerr_endline ("in if, got f_sr: " ^ f_str); *)

      (* let if_block = res ^ t_str ^ ws ^ "}\n" ^ ws ^ "else{\n" ^ f_str ^ ws ^ "}\n" in *)

      let tk_if_block = tk_res @ t_str @ [ (`String "}"); (`String "else"); (`String "{") ] @ f_str @ [ (`String "}") ] in 

      (* check things after if(){}{} xxx  *)
      let dom_succ = G.succ g.dom_tree nd in
      let ns = List.filter (fun x -> x != tb && x != fb) dom_succ in
      assert(List.length ns <= 1);
      if List.length ns = 1 then
        let if_after = to_json_helper (indent) g (List.hd ns) in
        tk_if_block @ if_after
      else
        tk_if_block

    | "loop" ->
      inside_loop :=  true; 
      (* prerr_endline ("now in loop: " ^ cmd ); *)
      let ss = G.succ g.graph nd in
      assert (List.length ss = 1);

      let nd = ignore_phis (List.hd ss) in
      (* then what follows must be if *)
      let (cmd, tb, fb) = simplify_if nd in
      
      let cmd = if cmd = "*" then "unknown()" else cmd in 

      (* let res = str ^ ws ^ "while(" ^ cmd ^ ")\n" in *)
      let tk_res = [ (`String "while"); (`String "(") ] @ (decode_to_json cmd) @ [ (`String ")")] in 

      let t_str = to_json_helper (indent+1) g tb in
      (* prerr_endline ("in loop, got t_sr: " ^ t_str); *)
      let f_str = to_json_helper (indent) g fb in
      (* prerr_endline ("in loop, got f_sr: " ^ f_str); *)

      (* let res_inv = res ^ ws ^ "{\n" in  
      res_inv ^ t_str ^ ws ^ "}\n" ^ ws  ^ f_str ^ "\n" *)

      tk_res @ [(`String "{")] @ t_str @ [(`String "}")] @ f_str

    | "phi"-> 
        (* str ^ ws ^ "//phi \n" ^ (check_dom_then_dive nd) *)
        check_dom_then_dive nd
    | "tb" -> 
        (* str ^ ws ^ "//tb \n"  ^ (check_dom_then_dive nd) *)
        check_dom_then_dive nd
    | "fb" -> 
        (* str ^ ws ^ "//fb \n"  ^ (check_dom_then_dive nd) *)
        check_dom_then_dive nd
    | "skip" -> 
        (* str ^ ws ^ "//skip \n"  ^ (check_dom_then_dive nd)  *)
        check_dom_then_dive nd
    | "assume" -> 
        (* str ^ ws ^ "assume " ^ cmd ^ ";\n"  ^ (check_dom_then_dive nd)  *)
        (decode_to_json cmd) @ check_dom_then_dive nd

    | "assert" -> 
        (* str ^ ws ^ "assert " ^ cmd ^ ";\n"  ^ (check_dom_then_dive nd)  *)
        (decode_to_json cmd) @ check_dom_then_dive nd

    | "assgn" -> 
      begin 
        (* let junk_statement = if !inside_loop && (Random.int 3) = 1 then gen_random_statement () else "" in  *)
        (* let junk_statement = if !inside_loop then gen_random_statement () else "" in  *)
        (* str ^ ws ^ cmd ^ ";\n"  
        ^ (check_dom_then_dive nd)  *)

        (decode_to_json cmd) @ check_dom_then_dive nd
      end 

    | _ -> raise (Failure "to_json_helper: unexpected return from go_straight")


let to_json : t -> json
  = fun g ->

    let vs = BatSet.to_list g.vars in

    (* let var_decl = `List (
        List.map (fun x -> `String x) vs 
    )  in  *)


    let entry = find_entry g in
    let body = to_json_helper 1 g entry in

    `List body

    (* let p = "int main()\n{\n" in 
    let p = p ^ var_decl ^ "\n" in 
    let p = p ^ body ^ "\n" in 
    let p = p ^ "}\n" in 
    p *)

    (* `Assoc [("var_decl", var_decl);
            ("body", body);
           ] *)



let print_token : t -> unit
  = fun g ->
    g
    |> to_json
    |> Yojson.Safe.pretty_to_channel stdout;
    ()
