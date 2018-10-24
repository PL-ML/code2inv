
open Boogie
open Sygus


let split_mark = ref "SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop"

let to_string : t -> string
  = fun g ->
    let res = "(set-logic LIA)\n\n" in
    var_list := BatSet.to_list g.vars;

    (* declare vars for inv-track *)
    let var_decls = List.fold_right (fun v res ->
        let res = res ^ "(declare-const " ^ v ^ " Int)\n" in 
        let res = res ^ "(declare-const " ^ v ^ "! Int)\n" in 
        res
      ) !var_list "" 
    in
    prerr_endline ( "declare var is done" );

    (* declare auxiliary vars, which are necessary for more than one update in trans-f *)
    let aux_vars = collect_aux_vars g in 
    let aux_var_decls = List.fold_right (fun v res -> 
        res ^ "(declare-const " ^ v ^ " Int)\n"
      ) aux_vars "" 
    in 
    prerr_endline ( "declare aux var is done" );

    (* declare args for pre-f/trans-f/post-f *)
    let f_args = (get_decl_vars !var_list 0 " Int") in
    let f_args_update = (get_decl_vars !var_list 0 "! Int") in
    let f_aux = (get_decl_vars !aux_var_list 0 " Int") in

    prerr_endline ( "declare args is done" );


    (* inv-f *)
    let synth_fun_decl = "(define-fun inv-f(" ^ f_args ^ ") Bool\n" in
    let synth_fun_decl = synth_fun_decl ^ !split_mark ^ "\n" in 
    let synth_fun_decl = synth_fun_decl ^ ")\n" in 
    prerr_endline "inv-f is done";

    (* pre-f *)
    let (loop, pre_f) = process_pre_f  (f_args ^ f_aux)  g in 
    prerr_endline "pre-f is done";

    (* trans-f *)
    let (loop_exit, trans_f) = process_trans_f  ( f_args ^ f_args_update ^ f_aux) loop g in 
    prerr_endline "trans-f is done";

    (* post-f *)
    let post_f = process_post_f (f_args ^ f_aux)  loop_exit g in 
    prerr_endline "post-f is done";

    (* loop invariant constraints *)
    let (pre_cond, ind_cond, post_cond) = encode_loop_inv() in 
    let inv_cs = wrap_conds  (!split_mark ^ "\n(assert (not\n")  [pre_cond; ind_cond; post_cond] "))\n"   in 

    (* combine all components *)
    let res = res ^ var_decls ^ "\n" in 
    let res = res ^ aux_var_decls ^ "\n" in 
    let res = res ^ synth_fun_decl ^ "\n" in 
    let res = res ^ pre_f ^ "\n"  in 
    let res = res ^ trans_f ^ "\n" in 
    let res = res ^ post_f ^ "\n" in 
    let res = res ^ inv_cs ^ "\n" in
    res  


let print_smt2 : t -> unit
  = fun g ->
    g
    |> to_string
    |> Printf.fprintf stdout "%s"
