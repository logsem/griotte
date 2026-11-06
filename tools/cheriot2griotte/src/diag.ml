(* Source locations and fatal errors.

   Every error the tool reports names the input file and line: the tool
   never skips what it does not understand. *)

type loc = { file : string; line : int }

exception Error of loc * string

let error loc fmt = Printf.ksprintf (fun msg -> raise (Error (loc, msg))) fmt

let no_loc file = { file; line = 0 }

let string_of_loc { file; line } =
  if line = 0 then file else Printf.sprintf "%s:%d" file line
