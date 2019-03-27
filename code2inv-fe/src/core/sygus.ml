
open Boogie


let var_list = ref []
let aux_var_list = ref []

let rec ws k = 
  if k <= 0 then ""
  else "  " ^ (ws (k-1))


let my_merge mp1 mp2 =
  BatMap.merge (fun k l1 l2 -> 
      match l1,l2 with 
      | Some s1, None -> Some s1 
      | None, Some s2 -> Some s2 
      | Some s1, Some s2 -> Some (s1 @ s2)
      | _ -> raise (Failure "my_merge: unexpected merge scenario");
    ) mp1 mp2


let split_var : string -> string * int 
  = fun var_sub -> 
    let len = String.length var_sub in 
    let mid = try String.rindex var_sub '_' 
      with _ -> raise (Failure (Printf.sprintf "split_var: cannot find _ in %s" var_sub)) 
    in 
    let var = String.sub var_sub 0 mid in 
    let sub = String.sub var_sub (mid + 1) (len - mid - 1) in 
    (* prerr_endline ("var: " ^ var ^ ", sub: S" ^ sub ^ "E");  *)
    (var, int_of_string sub)


let is_empty_char : char -> bool 
  = fun c -> c = ' ' || c = '\t' || c = '\n'


let first_non_empty : string -> int -> int * char 
  = fun s start ->
    let len = String.length s in 
    let rec go i = 
      if i < len then
        let c = String.get s i in 
        if is_empty_char c  then go (i+1) 
        else (i,c)  
      else (-1,' ')
    in 
    go start

let read_until_empty : string -> int -> string * int 
  = fun s start ->
    let len = String.length s in 
    if start >= len then raise (Failure (Printf.sprintf "read_until_empty: i=%d is too large, len=%d" start len) );
    let rec go i = 
      if i < len then 
        let c = String.get s i in 
        if is_empty_char c then ( String.sub s start (i-start), i)
        else go (i+1)
      else
        (String.sub s start (i-start), i)
    in 
    go start


let match_the_bracket: string -> int -> int 
  = fun s start ->
    (* prerr_endline (Printf.sprintf "match: s=%s start=%d" s start); *)
    let len = String.length s in 
    let rec go i ct= 
      if i < len then 
        let c = String.get s i in 
        match c with 
        | '(' -> go (i+1) (ct+1) 
        | ')' -> 
          if ct = 1 then i
          else begin 
            assert (ct > 1); 
            go (i+1) (ct - 1) 
          end
        | _ -> go (i+1) ct
      else raise (Failure (Printf.sprintf "failed to find a match, s=%s start=%d" s start));
    in 

    go start 0 


module SExp = struct 

  type t = App of op_name * t list
         | Var of string 
         | Const of int 
  and op_name = string

  let empty = App ("", [])

  let rec from_string : string -> t 
    = fun s -> 
      (* prerr_endline (Printf.sprintf "from_string: s=[%s]" s ); *)
      let (i0, c0) = first_non_empty s 0 in 
      if i0 < 0 then empty 
      else begin 
        match c0 with 
        | '(' -> 
          begin 
            let (op, i1) = read_until_empty s (i0+1) in 
            match op with 
            | "!=" | "==" | "=>" | "phi" | "and" | "or" | "not" | "+" | "-" | "*" | "=" | ">" | "<" | ">=" | "<=" -> 
              begin
                (* get rid of right parenthesis *)
                let len = match_the_bracket s i0 in 
                let (i2, _) = first_non_empty s (len+1) in 
                if i2 != -1 then raise (Failure "there are redundant things after (App ...) ");
                let s = String.sub s i1 (len - i1) in 
                let rec parse_args start = 
                  let (i2, c1) = first_non_empty s start in 
                  if i2 < 0 then []
                  else begin 
                    let right = 
                      if c1 = '(' then (match_the_bracket s i2) + 1
                      else 
                        let (_, i3) = read_until_empty s i2 in 
                        i3 
                    in 
                    (* prerr_endline (Printf.sprintf "s=[%s] i2=%d right=%d" s i2 right); *)
                    let sub_s = String.sub s i2 (right - i2) in 
                    let x = from_string sub_s in 
                    let res = parse_args (right + 1) in 
                    x :: res 
                  end 
                in 
                let args = parse_args 0 in 
                App (op, args)
              end 
            | _ -> raise (Failure ("unhandled operation: " ^ op))
          end 
        | '0'| '1'| '2'| '3'| '4'| '5'| '6'| '7'| '8'| '9' -> 
          begin
            let (op, i1) = read_until_empty s i0 in 
            let v = try int_of_string op with _ -> raise (Failure ("invalid const in Sygus.from_string: " ^ op) ) 
            in 
            let (i2, _) = first_non_empty s (i1 + 1) in 
            if i2 != -1 then raise (Failure "Const cannot be applied to any other things");
            Const v 
          end  
        | '-' -> begin 
            let (op, i1) = read_until_empty s i0 in 

            let is_int = try ignore(int_of_string op); true with _ -> false in 
            if is_int then begin 
              let v = try int_of_string op with _ -> raise (Failure ("invalid const in Sygus.from_string: " ^ op) ) 
              in 
              let (i2, _) = first_non_empty s (i1 + 1) in 
              if i2 != -1 then raise (Failure "Const cannot be applied to any other things");
              Const v 
            end 
            else 
              App ("-", [ Var op])
          end 
        | _ -> 
          begin 
            let (op, i1) = read_until_empty s i0 in 
            let (i2, _) = first_non_empty s (i1 + 1) in 
            if i2 != -1 then raise (Failure "Var cannot be applied to any other things");
            Var op
          end 
      end

  let rec to_string_verbose : int -> t -> string 
    = fun k e ->
      match e with 
      | App (op, args) -> 
        let res = (ws k) ^ "(Op:" ^ op ^ "\n" in 
        let res_args = List.fold_right (fun a r -> (to_string_verbose (k+1) a) ^ "\n" ^ r) args "" in 
        let res = res ^ res_args ^ (ws k) ^ ")\n" in 
        res 
      | Var v ->  (ws k) ^ "Var:" ^ v 
      | Const c -> (ws k) ^  (Printf.sprintf "Const:%d" c)

  let rec get_size : t -> int 
    = fun e -> 
      match e with 
      | App (op, args) -> 1 + List.fold_right (fun x r -> (get_size x) + r) args 0
      | _ -> 1

  let rec to_string : int -> t -> string 
    = fun k e ->
      match e with 
      | App (op, args) -> 
        let sz = get_size e in 
        if sz > 6 || op = "and" || op = "or" || op = "=>" then
          (* if sz > 10 then *)
          begin 
            let res = (ws k) ^ "("^ op ^ "\n"  in 
            let new_args = List.map (to_string (k+1)) args in 
            let res_args = String.concat "\n" new_args in 
            (* let res_args = List.fold_right (fun a r -> (to_string (k+1) a) ^ "\n" ^ r) args "" in  *)
            let res = res ^ res_args ^ "\n" in 
            let res = res ^ (ws k) ^ ")"  in 
            res 
          end 
        else begin 
          let new_args = List.map (to_string 0) args in 
          let res_args = String.concat " " new_args in 
          (* let res_args = List.fold_right (fun a r -> (to_string 0 a) ^ " " ^ r) args "" in  *)
          (ws k) ^ "("^ op ^ " " ^ res_args ^ ")"
        end
      | Var v ->   v 
      | Const c -> (Printf.sprintf "%d" c)

  let parse_and_extract_var : string -> (string, int list) BatMap.t
    = fun s ->
      let e = from_string s in 
      let rec visit x = 
        match x with 
        | App (op, args) ->  
          List.fold_right (fun arg r ->  
              my_merge (visit arg) r
            ) args BatMap.empty 
        | Var v -> 
          let (name, sub) = split_var v in 
          BatMap.add name [sub]  BatMap.empty 
        | Const c -> BatMap.empty 
      in 
      visit e

  let rec extract_ordered_var : t -> string list 
    = fun e -> 
      match e with 
      | App (_, args) -> List.fold_right (fun x ls -> (extract_ordered_var x) @ ls) args []
      | Var v -> [v]
      | _ -> []

  let get_def_use_var : string -> (string, int list) BatMap.t * (string, int list) BatMap.t
    = fun s -> 
      let e = from_string s in 
      let def = ref BatMap.empty in 
      let use = ref BatMap.empty in 
      let rec visit x = 
        match x with 
        | App (op, args) ->  
          begin 
            match op with 
            | "=" | "phi" -> 
              let h = List.hd args in 
              let t = List.tl args in 
              def := my_merge !def (visit h); 
              use := my_merge !use (List.fold_right (fun arg r ->  
                  my_merge (visit arg) r
                ) t BatMap.empty);
              BatMap.empty
            | _ ->
              let res = 
                List.fold_right (fun arg r ->  
                    my_merge (visit arg) r
                  ) args BatMap.empty 
              in
              use := my_merge !use res;
              res  
          end 
        | Var v -> 
          let (name, sub) = split_var v in 
          BatMap.add name [sub]  BatMap.empty 
        | Const c -> BatMap.empty 
      in 
      let _ = visit e in 
      (!def, !use)

  let rec rewrite_unsuported_op : t -> t 
    = fun e ->
      match e with 
      | App ("==", args) -> App ("=", List.map rewrite_unsuported_op args)
      | App ("!=", args) -> App ("not", [ App ("=", List.map rewrite_unsuported_op args) ])
      | App (op, args) ->  App (op, List.map rewrite_unsuported_op args)
      | _ -> e

  let rec re_t x = 
    match x with 
    | App (op, args) ->  
      begin 
        match op with 
        | "and" | "or" -> re_and_or x 
        | _ -> App (op, List.map (fun y -> re_t y) args)
      end 
    | Var v -> x
    | Const c -> x 
  and re_and_or x = 
    match x with 
    | App (op, args) when (op = "and" || op = "or") -> 
      assert (List.length args >= 1);
      let h = re_t(List.hd args) in 
      if (List.length args = 1) then h
      else begin 
        let rest = re_and_or (App (op, List.tl args)) in 
        App (op, [h; rest])
      end 
    | _ -> raise (Failure (Printf.sprintf "re_and get unexpected input: %s" (to_string 0 x)))

  let rec skip_single_and_or : t -> t
    = fun e -> 
      match e with 
      | App (op, args) ->  
        let new_args = List.map (fun x -> skip_single_and_or x) args in 
        if (op = "and" || op = "or") && (List.length new_args = 1) then 
          List.hd new_args 
        else
          App (op, new_args)
      | _ -> e       


  let sanitize_for_sygus : string -> t 
    = fun s -> 
      s 
      |> from_string
      |> skip_single_and_or
      |> rewrite_unsuported_op
      (* |> re_t *)

end


let def_startInt : string -> string
  = fun var_consts ->
    (* define startInt *)
    let startInt = (ws 2) ^ "(StartInt Int\n" in
    let startInt = startInt ^ (ws 3) ^ "(" ^ var_consts ^ "\n" in
    let startInt = startInt ^ (ws 4) ^ "(+ StartInt StartInt)\n" in
    let startInt = startInt ^ (ws 4) ^ "(- StartInt StartInt)\n" in
    let startInt = startInt ^ (ws 4) ^ "(* StartInt StartInt)\n" in
    let startInt = startInt ^ (ws 3) ^ ")\n" in
    let startInt = startInt ^ (ws 2) ^ ")\n" in
    startInt

let def_startBool : unit -> string
  = fun () ->
    (* define start / startBool *)
    let startBool = (ws 2) ^ "(Start Bool\n" in
    let startBool = startBool ^ (ws 3) ^ "(\n" in
    let startBool = startBool ^ (ws 4) ^ "(not Start)\n" in
    let startBool = startBool ^ (ws 4) ^ "(and Start Start)\n" in
    let startBool = startBool ^ (ws 4) ^ "(or Start Start)\n" in
    let startBool = startBool ^ (ws 4) ^ "(< StartInt StartInt)\n" in
    let startBool = startBool ^ (ws 4) ^ "(<= StartInt StartInt)\n" in
    let startBool = startBool ^ (ws 4) ^ "(= StartInt StartInt)\n" in
    (* let startBool = startBool ^ (ws 4) ^ "(!= StartInt StartInt)\n" in *)
    let startBool = startBool ^ (ws 4) ^ "(> StartInt StartInt)\n" in
    let startBool = startBool ^ (ws 4) ^ "(>= StartInt StartInt)\n" in
    let startBool = startBool ^ (ws 3) ^ ")\n" in
    let startBool = startBool ^ (ws 2) ^ ")\n" in
    startBool


let collect_aux_vars : t -> string list
  = fun g ->
    let all_vars = 
      G.fold_vertex (fun nd ls -> 
          let Node.Node (_,ty,cmd) = nd in
          match ty with 
          | "loop" | "skip" | "tb" | "fb" -> ls 
          | "if" when cmd = "*" -> ls 
          |  _ -> 
            (* prerr_endline ("1collect_aux_vars, cmd: " ^ cmd ^ "  "); *)
            let var_mp = SExp.parse_and_extract_var cmd in 
            let var_mp = BatMap.mapi (fun k vs ->
                List.map (fun x ->  Printf.sprintf "%s_%d" k x) vs
              ) var_mp 
            in 
            BatMap.fold (fun vs ls -> vs @ ls) var_mp ls
        ) g.graph []
    in 
    let res = List.sort_uniq compare all_vars in 
    aux_var_list := res; 
    res 

let rec handle_pre : t -> node -> (string list) * node
  = fun g nd ->
    let check_and_dive src = 
      let ss = G.succ g.graph src in
      assert(List.length ss = 1);
      handle_pre g (List.hd ss)
    in 
    let Node.Node (_,ty,cmd) = nd in
    match ty with
    | "loop" ->  ([], nd)
    | "skip" -> check_and_dive nd
    | "assgn"
    | "assume" ->  let (conds, loop) = check_and_dive nd in
      (cmd ::conds, loop)
    | _ -> raise (Failure ("unhandled ty in precondition: " ^ ty))


(* find the point where loop exits *)
let rec find_loop_exit_point g first_phi src = 
  (* prerr_endline "src: " ;
     Node.show src; *)
  let ss = G.succ g.graph src in
  let ex = 
    List.fold_right (
      fun cur res -> 
        let Node.Node (index,ty,cmd) = cur in
        if index = !Options.exit_id then (true, cur) :: res 
        else if cur = first_phi then (false, cur) :: res
        else (find_loop_exit_point g first_phi cur) @ res
    ) ss []
  in 
  let all_true = List.for_all (fun pr -> let s,_ = pr in s) ex in
  if all_true then 
    begin 
      (* ignore( prerr_endline "all_true:"; Node.show src );  *)
      [ (true, src) ] 
    end
  else begin 
    let true_ex = 
      List.fold_right (fun pr res -> let s,x = pr in 
                        if s then BatSet.add x res 
                        else res
                      ) ex BatSet.empty
    in
    let false_ex = 
      List.fold_right (fun pr res -> let s,x = pr in 
                        if not s then BatSet.add x res 
                        else res
                      ) ex BatSet.empty
    in
    if BatSet.cardinal true_ex = 0 then 
      begin 
        assert (BatSet.cardinal false_ex = 1); 
        [(false, BatSet.any false_ex)] 
      end
    else if BatSet.cardinal true_ex = 1 then 
      begin 
        (* ignore( prerr_endline "some true: "; Node.show src );  *)
        [ (false, BatSet.any true_ex)] 
      end
    else raise (Failure "unexpected cardinal")
  end

let extract_first_var : string -> string * int
  = fun s ->
    (* prerr_endline ("s: " ^ s) ;  *)
    let rec find_kth_space start k = 
      let index = String.index_from s start ' ' in 
      if k = 0 then index
      else (find_kth_space (index+1) (k-1))
    in 
    let left = find_kth_space 0 0 in 
    let right = find_kth_space 0 1 in 
    let len = right - left - 1 in 
    let var_sub = String.sub s (left + 1) len in

    split_var var_sub


(* constraints for an execution path *)
let gen_constraints_for_exec_path : node list -> string 
  = fun exec_path ->
    let len = List.length exec_path in 
    let cond = (ws 2) ^ "(and\n" in 
    let used_vars = ref BatMap.empty in 
    let rec exec i env = 
      (* let _ = prerr_endline ( Printf.sprintf "i=%d len=%d" i len ) in  *)
      if i < len then 
        let Node.Node (index, typ, cmd) = (List.nth exec_path i) in 

        (* save used vars *)
        let _ = 
          match typ with 
          | "phi" -> ()
          | "if" when cmd = "*" -> ()
          | _ ->
            let mp = SExp.parse_and_extract_var cmd in 
            used_vars := my_merge !used_vars mp; 
        in 

        let update_env_and_dive () = 
          let (key, sub) = extract_first_var cmd in 
          (* prerr_endline (Printf.sprintf "key=%s sub=%d" key sub); *)
          let defs = BatMap.find_default [] key env in  
          let var_sub = Printf.sprintf "%s_%d" key sub in 
          let env =
            (* let _ = prerr_endline (Printf.sprintf "defs len=%d" (List.length defs) ) in  *)
            if defs = [] then BatMap.add key [var_sub] env 
            else  
              (* let _ = prerr_endline ("hd:" ^ (List.hd defs) ) in  *)
              BatMap.add key (var_sub :: defs) env 
              (* BatMap.update key key (var_sub :: defs) env  *)
          in  
          let res = exec (i + 1) env in 
          (var_sub, key, defs,  res) 
        in 
        let handle_branch () = 
          assert (i>0);
          let Node.Node (pre_ind, pre_typ, pre_cmd) = (List.nth exec_path (i-1)) in 
          assert (pre_typ = "if");
          let res = exec (i+1) env in 
          (pre_cmd, res)
        in 

        match typ with 
        | "phi" -> 
          (* prerr_endline "process phi ... "; *)
          let (var_sub, key, defs,  res) = update_env_and_dive () in 
          if List.length defs = 0 then 
            let init_var = Printf.sprintf "(= %s %s)" var_sub key in
            (ws 3) ^ init_var ^ "\n" ^ res 
          else 
            begin 
              let last_def = List.hd defs in 
              let redef_var = Printf.sprintf "(= %s %s)" var_sub last_def in 
              (ws 3) ^ redef_var ^ "\n" ^ res
            end 

        | "assgn" ->
          (* prerr_endline "process assgn ... "; *)
          let (_, _,_, res) = update_env_and_dive () in 
          (ws 3) ^ cmd ^ "\n" ^ res 

        | "tb" ->
          (* prerr_endline "process tb ... "; *)
          let (pre_cmd, res) = handle_branch () in 
          if pre_cmd = "*" then res 
          else 
            (ws 3) ^ pre_cmd ^ "\n" ^ res

        | "fb" -> 
          (* prerr_endline "process fb ... "; *)
          let (pre_cmd, res) = handle_branch () in 
          if pre_cmd = "*" then res 
          else begin 
            let neg = "(not " ^ pre_cmd ^ ")" in 
            (ws 3) ^ neg ^ "\n" ^ res 
          end 
        | "if" 
        | "skip" ->
          (* prerr_endline "process if/skip ... "; *)
          exec (i+1) env 
        | _ -> raise (Failure ("unhandled ty in exec path: " ^ typ))

      else 
        begin 
          (* bind the last def to  var! *)
          let defs = BatMap.mapi (fun k ls -> 
              let last_def = List.hd ls in 
              Printf.sprintf "(= %s %s!)" last_def k 
            ) env 
          in 
          let res = BatMap.fold (fun v r -> (ws 3) ^ v ^ "\n" ^ r) defs "\n" in 

          (* not in def, but in use *)
          let mp = BatMap.mapi (fun k ls -> 
              let uniq_ls = List.sort_uniq compare ls in 
              List.map (fun v -> Printf.sprintf "%s_%d" k v) uniq_ls 
            ) !used_vars 
          in 

          (* check vars that keep no change *)      
          let used_only = BatMap.filter (fun k ls -> 
              let vs = BatMap.find_default [] k env in 
              if vs = [] then begin 
                assert (List.length ls = 1);
                true 
              end 
              else begin 
                List.iter (fun x ->
                    assert (List.exists (fun y -> x = y) vs) ; 
                  ) ls;
                false 
              end 
            ) mp 
          in 

          let res = BatMap.foldi (fun k ls r -> 
              let v = List.hd ls in 
              let b1 = Printf.sprintf "(= %s %s)" k v in 
              let b2 = Printf.sprintf "(= %s! %s)" k v in 
              let r = r  ^ (ws 3) ^ b1 ^ "\n" in 
              let r = r  ^ (ws 3) ^ b2 ^ "\n" in
              r 
            ) used_only res 
          in 

          (* check vars that are not used at all *)
          let vars = BatMap.foldi (fun k v r -> k :: r ) !used_vars [] in 
          let not_used = List.filter (fun x -> 
              not (List.exists (fun y -> x = y) vars)
            ) !var_list 
          in 
          let res = List.fold_right (fun x r -> 
              let b = Printf.sprintf "(= %s %s!)" x x in 
              r  ^ (ws 3) ^ b ^ "\n"
            ) not_used res 
          in

          res
        end 
    in 

    let res = exec 0 BatMap.empty in 

    let cond = cond ^ res ^ (ws 2) ^ ")\n" in 
    cond 


let handle_loop : t -> node -> string * node 
  = fun g loop ->
    let get_next_single nd = 
      let ss = G.succ g.graph nd in 
      assert (List.length ss = 1);
      List.hd ss 
    in
    let first_phi = get_next_single loop in 
    let _, loop_exit = List.hd (find_loop_exit_point g first_phi first_phi) in
    (* prerr_endline "loop_exit: "; *)
    let _ = Node.show loop_exit in


    (* enumerate all possible paths (each path correspond a different variable assginment situation) *)
    let rec exec_paths src = 
      let ss = G.succ g.graph src in
      let paths = List.fold_right (
          fun cur res ->
            (* assume a singe loop, otherwise exec_paths will not terminate*)
            if (cur = first_phi || cur = loop_exit) then ([] :: res)
            else (exec_paths cur) @ res
        ) ss []
      in 
      (* add src to the head *)
      List.fold_right (fun ls res -> 
          (src::ls) :: res
        ) paths []
    in 

    let paths = exec_paths (get_next_single first_phi) in 
    let paths = List.map (fun ls -> first_phi :: ls) paths in 
    let path_conds = List.map gen_constraints_for_exec_path paths in 

    let res = List.fold_right (fun pcond r -> pcond ^ r) path_conds "\n" in 
    let trans_body = (ws 1) ^ "(or \n" ^ res ^  (ws 1) ^ ")\n" in 

    (trans_body, loop_exit)


let gen_constraints_for_assert_path : node list -> string
  = fun assert_path -> 
    let len = List.length assert_path in 
    let use_var = ref BatMap.empty in 
    let def_var = ref BatMap.empty in 
    let assertion = ref "" in 
    let binding = ref "" in 
    let rec examine i = 
      if i < len then 
        let Node.Node (index, typ, cmd) = (List.nth assert_path i) in 
        (* prerr_endline (Printf.sprintf "len=%d i=%d typ=%s cmd=%s" len i typ cmd); *)

        (* save used vars *)
        let _ = 
          match typ with 
          | "if" when cmd = "*" -> ()
          | _ -> 
            (* the only thing that might be wrong is that: assignment vs equality *)
            let (d, u) = SExp.get_def_use_var cmd in 
            def_var := my_merge !def_var d; 
            use_var := my_merge !use_var u;
        in 

        let handle_branch () = 
          assert (i>0);
          let Node.Node (pre_ind, pre_typ, pre_cmd) = (List.nth assert_path (i-1)) in 
          assert (pre_typ = "if");
          let res = examine (i+1) in 
          (pre_cmd, res) 
        in
        match typ with 
        | "assume"
        | "assgn" ->  (ws 5) ^ cmd ^ "\n" ^ (examine (i+1)) 
        | "tb" -> 
          let (pre_cmd, res) = handle_branch () in 
          if pre_cmd = "*" then res 
          else 
            (ws 5) ^ pre_cmd ^ "\n" ^ res 

        | "fb" -> 
          let (pre_cmd, res) = handle_branch () in 
          if pre_cmd = "*" then res 
          else begin 
            let neg = "(not " ^ pre_cmd ^ ")" in 
            (ws 5) ^ neg ^ "\n" ^ res 
          end 

        | "if" -> examine (i+1)

        | "assert" -> 
          assertion := cmd;
          (examine len)

        | _  -> raise (Failure ("unhandled ty in examine: " ^ typ))
      else begin 
        (* bind the first use (before any define/kill) to  var *)

        let us = BatMap.mapi (fun k ls -> 
            let uniq_ls = List.sort_uniq compare ls in 
            List.map (fun x -> Printf.sprintf "%s_%d" k x) uniq_ls 
          ) !use_var 
        in 
        let ds = BatMap.mapi (fun k ls -> 
            let uniq_ls = List.sort_uniq compare ls in 
            List.map (fun x -> Printf.sprintf "%s_%d" k x) uniq_ls 
          ) !def_var 
        in 
        let bs = BatMap.mapi (fun k ls -> 
            let kill = BatMap.find_default [] k ds in 
            let ss = List.filter (fun x -> not (List.mem x kill) ) ls in 
            if ss = [] then []
            else begin assert (List.length ss = 1); ss end
          ) us 
        in 
        (* prerr_endline (Printf.sprintf "going to add bindings, #us=%d  #ds=%d  #bs = %d " (BatMap.cardinal us) (BatMap.cardinal ds) (BatMap.cardinal bs) ); *)
        let res = BatMap.foldi (fun k ls r -> 
            if ls = [] then begin 
              prerr_endline (Printf.sprintf "this is rare case where variable [%s] is redefined after loop" k);
              r
            end
            else  begin
              let b = Printf.sprintf "(= %s %s)" k (List.hd ls) in 
              r ^  (ws 3) ^ b ^ "\n"
            end
          ) bs "" 
        in 
        binding := res; ""
      end 
    in 
    let before_assert = examine 0 in 

    (* binding implies  (before_assert  implies assertion) *)
    let helper_1 () = 
      let res = (ws 2) ^ "(and\n" in 
      let res = res ^ (ws 2) ^ "(=>\n" in 

      let res = res ^ (ws 3) ^ "(and\n" in 
      let res = res ^ !binding  in 
      let res = res ^ (ws 3) ^ ")\n"  in 

      let res = res ^ (ws 3) ^ "(not\n" in 
      let res = res ^ (ws 4) ^ "(and\n" in 
      let res = res ^ before_assert ^ "\n" in 
      let res = res ^ (ws 5) ^ "(not " ^ !assertion ^ ")\n" in 
      let res = res ^ (ws 4) ^ ")\n" in 
      let res = res ^ (ws 3) ^ ")\n" in 
      let res = res ^ (ws 2) ^ ")\n" in 
      let res = res ^ (ws 2) ^ ")\n" in 
      res 
    in 
    let helper_2 () = 
      let res = (ws 2) ^ "(and\n" in 
      let res = res ^ (ws 2) ^ "(or\n" in 

      let res = res ^ (ws 3) ^ "(not (and\n" in 
      let res = res ^ !binding  in 
      let res = res ^ (ws 3) ^ "))\n"  in 

      let res = res ^ (ws 3) ^ "(not\n" in 
      let res = res ^ (ws 4) ^ "(and\n" in 
      let res = res ^ before_assert ^ "\n" in 
      let res = res ^ (ws 5) ^ "(not " ^ !assertion ^ ")\n" in 
      let res = res ^ (ws 4) ^ ")\n" in 

      let res = res ^ (ws 3) ^ ")\n" in 
      let res = res ^ (ws 2) ^ ")\n" in 
      let res = res ^ (ws 2) ^ ")\n" in 
      res 
    in 
    helper_2 ()

let handle_post : t -> node -> string
  = fun g loop_exit -> 
    let preds = G.pred g.graph loop_exit in 
    assert (List.length preds = 1);
    let if_b = List.hd preds in 

    let rec paths_to_assert src = 
      let Node.Node (index,ty,cmd) = src in
      if ty = "assert" then  [ [src] ]
      else if  index = !Options.exit_id then []
      else begin 
        let ss = G.succ g.graph src in
        let paths = List.fold_right (
            fun cur res -> (paths_to_assert cur) @ res 
          ) ss [] 
        in 
        (* add src to the head *)
        List.fold_right (fun ls res -> 
            (src::ls) :: res
          ) paths []
      end
    in 
    let paths = paths_to_assert loop_exit in 
    (* add if_b  *)
    let paths = List.map (fun p -> if_b :: p) paths in 
    let path_conds = List.map gen_constraints_for_assert_path paths in 

    let res = List.fold_right (fun pcond r -> pcond ^ r) path_conds "\n" in 
    let assert_body = (ws 1) ^ "(and\n" ^ res ^  (ws 1) ^ ")\n" in 
    assert_body

let rec get_decl_vars vs i suffix =
  if i >= List.length vs then ""
  else
    begin
      let decl = "(" ^ (List.nth vs i) ^ suffix ^ ")"
      in
      decl ^ (get_decl_vars vs (i+1) suffix)
    end


let define_inv_f : string -> t -> string 
  = fun args g -> 
    (* inv-f *)
    let var_consts = List.fold_right (fun x res -> x ^ " " ^ res) !var_list  "" in
    let var_consts = BatSet.fold (fun x res -> res ^ " " ^ x) g.consts  var_consts in

    (* Note that we don't need aux vars for inv-f *)
    let synth_fun_decl = "(synth-fun inv-f(" ^ args ^ ") Bool\n" in
    let synth_fun_decl = synth_fun_decl ^ (ws 1) ^ "(\n" in 
    let synth_fun_decl = synth_fun_decl ^ (def_startInt var_consts) in 
    let synth_fun_decl = synth_fun_decl ^ (def_startBool ())  in
    let synth_fun_decl = synth_fun_decl ^ (ws 1) ^ ")\n" in 
    let synth_fun_decl = synth_fun_decl ^ ")\n" in 
    synth_fun_decl


let process_pre_f : string -> t -> node * string 
  = fun args g -> 
    let entry = find_entry g in
    let (pres, loop) = handle_pre g entry  in

    (* collect last def for each variables *)
    let bindings = List.fold_right (fun z res -> 
        let e = SExp.from_string z in 
        let ordered_vars = SExp.extract_ordered_var e in 
        List.fold_left (fun res2 y -> 
            let (key,sub) = split_var y in
            let def = BatMap.find_default "" key res2 in 
            if def = "" then 
              begin 
                (* if not defined in the future, otherwise ignore current def*)
                BatMap.add key (Printf.sprintf "%s_%d" key sub) res2
              end 
            else res2 
          ) res ordered_vars 
      ) pres BatMap.empty 
    in
    (* BatMap.iter (fun k v -> prerr_endline (Printf.sprintf "key: %s" k)  ) bindings; *)
    let bindings = BatMap.mapi (fun k v -> Printf.sprintf "(= %s %s)" k  v) bindings in 
    let pres = BatMap.fold (fun v ls -> v :: ls) bindings pres in  
    let pre_cond = List.fold_right (fun cond res -> (ws 2) ^ cond ^ "\n" ^ res) pres "" in
    let pre_f = "(define-fun pre-f (" ^ args ^ ") Bool\n" in
    let pre_body = "(and\n" ^ pre_cond ^ (ws 1) ^ ")\n" in 
    let pre_body = SExp.to_string 1 (SExp.sanitize_for_sygus pre_body) in 
    let pre_f = pre_f ^ pre_body ^"\n)\n" in
    (loop, pre_f)


let process_trans_f : string -> node -> t -> node * string 
  = fun args loop g -> 
    let trans_f = "(define-fun trans-f (" ^ args ^ ") Bool\n" in 
    let (trans_body, loop_exit) =  handle_loop g loop in 
    let trans_body = SExp.to_string 1 (SExp.sanitize_for_sygus trans_body) in 
    let trans_f = trans_f ^ trans_body ^ "\n)\n" in 
    (loop_exit, trans_f)


let process_post_f : string -> node -> t -> string
  = fun args loop_exit g ->
    let post_f = "(define-fun post-f (" ^ args ^ ") Bool\n" in
    let post_body = handle_post g loop_exit in 
    let post_body = SExp.to_string 1 (SExp.sanitize_for_sygus post_body) in 
    let post_f = post_f ^ post_body ^ "\n" in 
    let post_f = post_f ^ ")\n" in 
    post_f


let wrap_conds : string ->  string list -> string -> string 
  = fun before conds after ->
    String.concat "\n"  (List.map (fun x -> before ^ x ^ after ) conds)

let encode_loop_inv : unit -> string * string * string 
  = fun () -> 
    let get_var_list vs  suffix = List.fold_right (fun v r -> v ^suffix ^ r) vs "" in

    (* pre-f => inv-f *)
    let pre_cond = (ws 1) ^ "(=>\n" in 
    let pre_cond = pre_cond ^ (ws 2) ^ "(pre-f " ^ (get_var_list !var_list " ") ^ (get_var_list !aux_var_list " ") ^ ")\n" in 
    let pre_cond = pre_cond ^ (ws 2) ^ "(inv-f " ^ (get_var_list !var_list " ") ^ ")\n" in 
    let pre_cond = pre_cond ^ (ws 1) ^ ")\n" in 

    (* inv-f & tran-f => inv-f *)
    let ind_cond = (ws 1) ^ "(=>\n" in 
    let ind_cond = ind_cond ^ (ws 2) ^ "(and\n" in 
    let ind_cond = ind_cond ^ (ws 3) ^ "(inv-f " ^ (get_var_list !var_list " ") ^ ")\n" in 
    let ind_cond = ind_cond ^ (ws 3) ^ "(trans-f " 
                   ^ (get_var_list !var_list " ") 
                   ^ (get_var_list !var_list "! ") 
                   ^ (get_var_list !aux_var_list " ")
                   ^ ")\n" in 
    let ind_cond = ind_cond ^ (ws 2) ^ ")\n" in 
    let ind_cond = ind_cond ^ (ws 2) ^ "(inv-f " ^ (get_var_list !var_list "! ") ^ ")\n" in 
    let ind_cond = ind_cond ^ (ws 1) ^ ")\n" in 

    (* inv-f => post-f *)
    let post_cond = (ws 1) ^ "(=>\n" in 
    let post_cond = post_cond ^ (ws 2) ^ "(inv-f " ^ (get_var_list !var_list " ") ^ ")\n" in 
    let post_cond = post_cond ^ (ws 2) ^ "(post-f " ^ (get_var_list !var_list " ") ^ (get_var_list !aux_var_list " ") ^ ")\n" in 
    let post_cond = post_cond ^ (ws 1) ^ ")\n" in 

    (pre_cond, ind_cond, post_cond)

let add_junk : unit -> unit 
  = fun () -> 
    (* introduce junk vars *)
    let rec dump_junk i = 
      if i >= !Options.junk then [] 
      else (Printf.sprintf "junk_%d" i) :: (dump_junk (i+1) )
    in 
    let junk_var = dump_junk 0 in 
    var_list := !var_list @ junk_var


let to_string : t -> string
  = fun g ->
    let res = "(set-logic LIA)\n\n" in
    var_list := BatSet.to_list g.vars;

    if !Options.junk > 0 then add_junk(); 

    (* declare vars for inv-track *)
    let var_decls = List.fold_right (fun v res ->
        let res = res ^ "(declare-var " ^ v ^ " Int)\n" in 
        let res = res ^ "(declare-var " ^ v ^ "! Int)\n" in 
        res
      ) !var_list "" 
    in

    (* declare auxiliary vars, which are necessary for more than one update in trans-f *)
    let aux_vars = collect_aux_vars g in 
    let aux_var_decls = List.fold_right (fun v res -> 
        res ^ "(declare-var " ^ v ^ " Int)\n"
      ) aux_vars "" 
    in 

    (* declare args for pre-f/trans-f/post-f *)
    let f_args = (get_decl_vars !var_list 0 " Int") in
    let f_args_update = (get_decl_vars !var_list 0 "! Int") in
    let f_aux = (get_decl_vars !aux_var_list 0 " Int") in

    (* inv-f *)
    let synth_fun_decl = define_inv_f f_args g in 
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
    let inv_cs = wrap_conds "(constraint\n" [pre_cond; ind_cond; post_cond] ")\n"   in 

    (* combine all components *)
    let res = res ^ var_decls ^ "\n" in 
    let res = res ^ aux_var_decls ^ "\n" in 
    let res = res ^ synth_fun_decl ^ "\n" in 
    let res = res ^ pre_f ^ "\n"  in 
    let res = res ^ trans_f ^ "\n" in 
    let res = res ^ post_f ^ "\n" in 
    let res = res ^ inv_cs ^ "\n" in
    let res = res ^ "(check-synth)" in 
    res  


let print_sygus : t -> unit
  = fun g ->
    g
    |> to_string
    |> Printf.fprintf stdout "%s"


let to_inv_track : t -> string 
  = fun g ->
    let res = "(set-logic LIA)\n\n" in
    var_list := BatSet.to_list g.vars;

    (* if !Options.junk > 0 then add_junk();  *)

    (* declare auxiliary vars, which are necessary for more than one update in trans-f *)
    let aux_vars = collect_aux_vars g in 

    (* we have to create inv_vars, 
       and cannot simply add aux_vars to var_list, 
       because var_list is used globally *)
    let inv_vars = !var_list @ aux_vars in 

    (* declare vars for inv-track *)
    let var_decls = List.fold_right (fun v res ->
        res ^ "(declare-primed-var " ^ v ^ " Int)\n"
      ) inv_vars "" 
    in

    (* declare args for pre-f/trans-f/post-f *)
    let f_args = (get_decl_vars inv_vars 0 " Int") in
    let f_args_update = (get_decl_vars inv_vars 0 "! Int") in
    let f_aux = "" in

    (* inv-f *)
    let synth_fun_decl = Printf.sprintf "(synth-inv inv-f (%s))\n" f_args in 
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
    let inv_cs = "(inv-constraint inv-f pre-f trans-f post-f)" in 

    (* combine all components *)
    let res = res ^ var_decls ^ "\n" in 
    (* let res = res ^ aux_var_decls ^ "\n" in  *)
    let res = res ^ synth_fun_decl ^ "\n" in 
    let res = res ^ pre_f ^ "\n"  in 
    let res = res ^ trans_f ^ "\n" in 
    let res = res ^ post_f ^ "\n" in 
    let res = res ^ inv_cs ^ "\n" in
    let res = res ^ "(check-synth)" in 
    res  


let print_inv_track : t -> unit 
  = fun g ->
    g
    |> to_inv_track
    |> Printf.fprintf stdout "%s"
