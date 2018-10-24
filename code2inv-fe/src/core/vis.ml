open Printf

module Json = Yojson.Safe

let ast = ref false
let opts = [
    ("-a", (Arg.Set ast), "show ast");
  ]

let usage = ""

let file = ref ""

let counter = ref 0
                  
               
let args f =
  if Sys.file_exists f then
    file := f
  else
    raise (Arg.Bad (f^": No such file"))

let rec dump_ast : out_channel -> string -> string -> (string * string) list -> Json.json -> (string * string) list
  = fun chan pred prefix edges ast ->
  let handle_str x =
        let ac = "a" ^ (string_of_int !counter) in
        ignore (counter := !counter + 1);
        let _ = output_string chan (sprintf "%s[label=\"%s:%s\" ];\n" ac prefix x) in

        (ac, (pred,ac) :: edges)
  in
  
  match ast with
  | `Assoc [("UNK",`String unk);] ->
     let (pred,edges) = handle_str unk in
     edges

  | `Assoc [("Var",`String var);] ->
     let (pred,edges) = handle_str var in
     edges

  | `Assoc [("Const",`String cons);] ->
     let (pred,edges) = handle_str cons in
     edges

  | `Assoc (("OP",`String op) :: tl) ->
     let (pred,edges) = handle_str op in
     let edges = List.fold_left (fun ls (str,arg) ->
                     dump_ast chan pred str ls arg
                   ) edges tl
     in
     edges

  | _ -> prerr_endline ("ERROR_ast:" ^ (Yojson.Safe.to_string ast));
         fprintf chan "ERROR_ast\n";
         []
                           
let dump_nodes : out_channel -> (string * Json.json) list -> unit
  = fun chan l ->

  let edges = ref [] in
  let _ = (* print nodes *)
    List.iter (fun (node, cmd) ->
        let cc = "c" ^ (string_of_int !counter) in
        ignore (counter := !counter + 1);
        
        let str = (node^"[label=\""^node ^"\"," ^ " shape=oval];\n") in
        output_string chan str;

        let handle_c cname =
          let str =
            match cname with
            | "Assume" -> 
               sprintf "%s[label=\"%s\",style=filled,fillcolor=green ];\n" cc cname
            | "Assert" ->  sprintf "%s[label=\"%s\",style=filled, fillcolor=yellow ];\n" cc cname
            | _ ->  sprintf "%s[label=\"%s\" ]\n" cc cname
          in
          output_string chan str;
          ignore( edges := (node,cc) :: !edges );
        in
        let handle_x prefix xval =
          if !ast then
            let ls = dump_ast chan cc prefix [] xval in
            ignore( edges := List.append ls !edges );
          else ()
        in
        match cmd with
        | `Assoc [("cmd", `String cname);] -> (* Skip *)
           handle_c cname;           
        | `Assoc [("cmd", `String cname); ("lval", lval)] -> (* UNK *)
           handle_c cname;
           handle_x "lval" lval; 
        | `Assoc [("cmd", `String cname); ("rval", rval)] ->
           handle_c cname;
           handle_x "rval" rval; 
        | `Assoc [("cmd", `String cname); ("lval",lval); ("rval", rval)] ->
           handle_c cname;
           handle_x "lval" lval;
           handle_x "rval" rval;
        | _ -> prerr_endline (Yojson.Safe.to_string cmd); fprintf chan "ERROR_cmd\n"

      ) l;
  in
  (* print edges *)
  List.iter (fun (src, dst) -> fprintf chan "%s -> %s[dir=none,style=dotted];\n" src dst) !edges
  (* fprintf chan "}\n" *)

let dump_edges : out_channel -> Json.json list -> unit
= fun chan l ->
  List.iter (fun edge ->
      match edge with
        `List [`String v1; `String v2] ->
          fprintf chan "%s -> %s;\n" v1 v2
      | _ -> raise (Failure "error")
    ) l


let dump :  Json.json -> unit
  = fun cfg -> 
  let dot = "tmp.dot" in
  let chan = open_out dot in
  fprintf chan "digraph G {\n";
  (* fprintf chan "{\n"; *)
  fprintf chan "node [shape=box]\n";
  (match cfg with
     `Assoc [(_, `Assoc nodes); (_, `List edges)] ->
      dump_nodes chan nodes;
      dump_edges chan edges;
   | _ -> raise (Failure "error"));
  fprintf chan "}\n";
  close_out chan;
  let _ = Unix.create_process "dot" [|"dot"; "-Tsvg"; "-o"^ !file ^".svg"; dot|] Unix.stdin Unix.stdout Unix.stderr in
  let _ = Unix.wait () in
  ()
               


let main () =
  Arg.parse opts args usage;
  Json.from_file !file
  |> dump

let _ = main ()
