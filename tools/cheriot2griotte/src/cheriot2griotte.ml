(* cheriot2griotte: from the CHERIoT compiler's assembly of a compartment
   to Griotte assembly.

     cheriot2griotte classify <file.s> [--dump <file.dump>]
     cheriot2griotte exports <file.s>...      (untrusted compartments)
     cheriot2griotte census <file.s>...
     cheriot2griotte rocq <file.s> --name <ident> --label-prefix <cs>
       [--source <path>] [--input-sha256 <hex>] [--labels <map>]
       [--description <text>]
     cheriot2griotte reverse-check <file.s> --name <ident> --label-prefix <cs>
       [--labels <map>] [other options of rocq, ignored]

   Pipeline:
     .s --Cheriot_parser--> lines --Classify--> Classify.t
        --Lower--> Griotte asm AST, by blocks --Rocq_print--> .v

   [rocq] prints the Rocq file on stdout: definitions named <ident>_...,
   generated labels .L<cs>_<function>_..., the header naming --source
   (default: the input path) and --input-sha256 (computed by the dune rule
   with sha256sum; no hash in the header without it). --labels is the
   optional label override map (Lower.read_overrides).

   [reverse-check] lowers the file as [rocq] does, then maps the Griotte
   code back to CHERIoT instructions and compares them with the .s
   (Reverse); it prints what it checked and every mismatch.

   Exit status: 0 on success, 1 on a .s/.dump or reverse-map mismatch, 2 on an input
   error (reported as file:line). *)

let usage () =
  prerr_endline
    "usage: cheriot2griotte classify <file.s> [--dump <file.dump>]\n\
    \       cheriot2griotte exports <file.s>...\n\
    \       cheriot2griotte census <file.s>...\n\
    \       cheriot2griotte rocq <file.s> --name <ident> --label-prefix <cs> [--source <path>]\n\
    \                            [--input-sha256 <hex>] [--labels <map>] [--description <text>]\n\
    \       cheriot2griotte reverse-check <file.s> <options of rocq>";
  exit 2

let run () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "classify"; file ] -> Summary.print (Classify.classify_file file); 0
  | [ "classify"; file; "--dump"; dump ] ->
      let t = Classify.classify_file file in
      Summary.print t;
      let r = Crosscheck.check t dump in
      Summary.print_crosscheck dump r;
      if Crosscheck.ok r then 0 else 1
  | "exports" :: (_ :: _ as files) ->
      List.iter
        (fun f ->
          Printf.printf "file: %s\n" f;
          Summary.print_exports (Classify.exports_only f))
        files;
      0
  | "census" :: (_ :: _ as files) ->
      let ts = List.map Classify.classify_file files in
      Printf.printf "files: %d\n" (List.length files);
      Summary.print_census (List.concat_map Summary.all_instrs ts);
      0
  | ("rocq" | "reverse-check") as cmd :: file :: opts ->
      let rec parse acc = function
        | [] -> acc
        | k :: v :: rest when String.length k > 2 && String.sub k 0 2 = "--" -> parse ((k, v) :: acc) rest
        | _ -> usage ()
      in
      let opts = parse [] opts in
      let get k = List.assoc_opt k opts in
      let req k = match get k with Some v -> v | None -> usage () in
      let name = req "--name" and prefix = req "--label-prefix" in
      let overrides = match get "--labels" with Some f -> Lower.read_overrides f | None -> [] in
      let t = Classify.classify_file file in
      let l = Lower.lower ~overrides ~prefix t in
      if cmd = "reverse-check" then (
        Printf.printf "file: %s\n" (Option.value ~default:file (get "--source"));
        let r = Reverse.check l in
        Reverse.print r;
        if r.errors = [] then 0 else 1)
      else
        let description =
          match get "--description" with
          | Some d -> d
          | None -> Printf.sprintf "The compiled code of %s, translated to Griotte." file
        in
        print_string
          (Rocq_print.print ~name ~source:(Option.value ~default:file (get "--source")) ~sha256:(get "--input-sha256")
             ~description l);
        0
  | _ -> usage ()

let () =
  match run () with
  | code -> exit code
  | exception Diag.Error (loc, msg) ->
      Printf.eprintf "%s: error: %s\n" (Diag.string_of_loc loc) msg;
      exit 2
  | exception Sys_error msg ->
      Printf.eprintf "error: %s\n" msg;
      exit 2
