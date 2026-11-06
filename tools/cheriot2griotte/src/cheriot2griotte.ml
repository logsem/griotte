(* cheriot2griotte: from the CHERIoT compiler's assembly of a compartment
   to Griotte assembly.

   Step 1 (this file): reading and classification only.
     cheriot2griotte classify <file.s> [--dump <file.dump>]
     cheriot2griotte exports <file.s>...      (untrusted compartments)
     cheriot2griotte census <file.s>...

   Pipeline, with the later stages to come:
     .s --Cheriot_parser--> lines --Classify--> Classify.t
        --(step 2: lowering)--> Griotte asm AST --(Rocq printer)--> .v

   Exit status: 0 on success, 1 on a .s/.dump mismatch, 2 on an input
   error (reported as file:line). *)

let usage () =
  prerr_endline
    "usage: cheriot2griotte classify <file.s> [--dump <file.dump>]\n\
    \       cheriot2griotte exports <file.s>...\n\
    \       cheriot2griotte census <file.s>...";
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
