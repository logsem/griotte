(* The human-readable summary printed by [classify] and [census]. The
   output is stable (sorted or in file order) for the golden tests. *)

open Cheriot_ast
open Classify

let pf = Printf.printf

(* .word values are 32-bit; print them as signed (R5 of the review:
   [.word 4294967295] is [-1], like Griotte's [WInt]). *)
let signed32 n =
  let n = n land 0xffffffff in
  if n >= 0x80000000 then n - 0x100000000 else n

let string_of_data = function
  | Word (Num n) -> string_of_int (signed32 n)
  | Word e -> string_of_expr e
  | Half e -> "half " ^ string_of_expr e
  | Byte e -> "byte " ^ string_of_expr e
  | Zero n -> Printf.sprintf "zero %d" n

let name_with_mangled s =
  let d = Demangle.demangle s in
  if d = s then s else Printf.sprintf "%s (%s)" d s

(* Mnemonic census: (mnemonic, count), by count then name. *)
let census instrs =
  let tbl = Hashtbl.create 32 in
  List.iter
    (fun i -> Hashtbl.replace tbl i.mnemonic (1 + Option.value ~default:0 (Hashtbl.find_opt tbl i.mnemonic)))
    instrs;
  List.sort
    (fun (m1, c1) (m2, c2) -> if c1 <> c2 then compare c2 c1 else compare m1 m2)
    (Hashtbl.fold (fun m c acc -> (m, c) :: acc) tbl [])

let reloc_counts instrs =
  let count r =
    List.length
      (List.concat_map
         (fun i ->
           List.filter
             (function Imm (Reloc (r', _)) | Mem (Reloc (r', _), _) -> r' = r | _ -> false)
             i.operands)
         instrs)
  in
  (count Hi, count Lo_i, count Size)

let print_census instrs =
  let hi, lo, size = reloc_counts instrs in
  let c = census instrs in
  pf "census: %d instructions, %d distinct mnemonics\n" (List.length instrs) (List.length c);
  List.iter (fun (m, n) -> pf "  %-16s %d\n" m n) c;
  pf "relocations: hi %d, lo_i %d, size %d\n" hi lo size

let all_instrs t = List.concat_map func_instrs t.funcs

let string_of_import_kind = function
  | Switcher -> "switcher"
  | Library_call f -> "library call " ^ Demangle.demangle f
  | Cross_call (c, f) -> Printf.sprintf "cross-compartment call %s.%s" c (Demangle.demangle f)
  | Shared_object (n, p) -> Printf.sprintf "shared object %s, permissions %s" n p

let print_export e =
  pf "  %s: nargs %d, posture %s, min-stack byte %d, flags 0x%02x (%s)\n"
    (name_with_mangled e.efunc) e.enargs (string_of_posture e.eposture) e.emin_stack e.eflags e.esym

let print_exports exports =
  pf "exports (%d):\n" (List.length exports);
  List.iter print_export exports

let print t =
  pf "file: %s\n" t.file;
  (match t.ukind with
   | Compartment c -> pf "kind: compartment %s\n" c
   | Library -> pf "kind: library\n");
  print_exports t.exports;
  pf "imports (%d):\n" (List.length t.imports);
  List.iter
    (fun i ->
      pf "  %s: %s, %d use(s)\n" i.isym (string_of_import_kind i.ikind) (import_uses t i.isym))
    t.imports;
  pf "globals (%d):\n" (List.length t.globals);
  List.iter
    (fun g ->
      pf "  %s: %s, %d bytes, init [%s]\n" (name_with_mangled g.gname)
        (if g.gbss then ".bss" else ".data")
        g.gsize
        (String.concat "; " (List.map string_of_data g.ginit)))
    t.globals;
  pf "sealed objects (%d):\n" (List.length t.sealed_objects);
  List.iter
    (fun o ->
      pf "  %s: sealing type %s, %d bytes, data [%s]\n" o.oname o.otype o.osize
        (String.concat "; " (List.map string_of_data (List.tl o.odata))))
    t.sealed_objects;
  pf "functions (%d):\n" (List.length t.funcs);
  List.iter
    (fun f ->
      let ps = List.assoc f.fname t.pairs in
      let fetches = List.length (List.filter (fun p -> match p.pkind with Fetch_import _ -> true | _ -> false) ps) in
      let globals = List.length ps - fetches in
      pf "  %s: %d instructions, %d import fetches, %d global addresses\n" (name_with_mangled f.fname)
        (List.length (func_instrs f)) fetches globals)
    t.funcs;
  print_census (all_instrs t)

let print_crosscheck dump (r : Crosscheck.result) =
  pf "cross-check with %s: %s\n" dump (if Crosscheck.ok r then "OK" else "MISMATCH");
  List.iter (fun (f, n) -> pf "  %s: %d instructions, same mnemonics and registers\n" f n) r.matched;
  List.iter (fun m -> pf "  MISMATCH %s\n" m) r.mismatches;
  List.iter (fun (s, n) -> pf "  MISMATCH dump-only code %s (%d instructions)\n" s n) r.dump_only;
  List.iter (fun f -> pf "  MISMATCH %s absent from the dump\n" f) r.absent
