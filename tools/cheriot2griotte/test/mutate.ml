(* Mutation tests of the reverse map (Reverse): lower a real input, check
   that the reverse map accepts it, then change one element of the
   lowered Griotte code (the AST, not the lowering) and check that the
   reverse map rejects the result.

     mutate.exe <cmdc main.s> <temporal_isolation K.s> <griotte_assert.s>

   Prints each mutation and the mismatches found; exits 1 if a mutation
   goes unnoticed or an unmutated file is rejected. *)

module G = Griotte_asm

(* Replace the [nth] output for which [f] gives [Some outs'] by [outs']. *)
let mutate ?(nth = 1) (f : Lower.out -> Lower.out list option) (l : Lower.t) =
  let k = ref 0 in
  let outs os =
    List.concat_map
      (fun o ->
        match f o with
        | Some os' ->
            incr k;
            if !k = nth then os' else [ o ]
        | None -> [ o ])
      os
  in
  let l' =
    { l with
      Lower.funcs =
        List.map
          (fun (fo : Lower.func_out) ->
            { fo with
              Lower.fo_blocks =
                List.map
                  (fun (b : Lower.block) ->
                    { b with Lower.items = List.map (fun (lw : Lower.lowered) -> { lw with Lower.outs = outs lw.outs }) b.items })
                  fo.fo_blocks })
          l.funcs }
  in
  if !k < nth then failwith "mutation without an occurrence";
  l'

let failures = ref 0

let run name l =
  let r = Reverse.check l in
  Printf.printf "%s: %s\n" name (if r.errors = [] then "accepted" else "rejected");
  List.iter (fun e -> Printf.printf "  mismatch: %s\n" e) r.errors;
  r.errors = []

let expect_ok name l = if not (run name l) then incr failures

let expect_caught name l =
  if run name l then (
    print_endline "  NOT CAUGHT";
    incr failures)

let lower ~prefix file = Lower.lower ~prefix (Classify.classify_file file)

let () =
  let cmdc_file, ti_file, assert_file =
    match Sys.argv with [| _; a; b; c |] -> (a, b, c) | _ -> failwith "usage: mutate.exe <cmdc main.s> <ti K.s> <assert.s>"
  in
  let cmdc = lower ~prefix:"cmdc" cmdc_file and ti = lower ~prefix:"ti" ti_file in
  let asrt = lower ~prefix:"assert" assert_file in
  expect_ok "cmdc, unmutated" cmdc;
  expect_ok "temporal_isolation, unmutated" ti;
  expect_ok "assert, unmutated" asrt;
  print_endline "\n(1) wrong frame word: the spill of ra to word 1 instead of word 2";
  expect_caught "cmdc"
    (mutate (function Lower.C (G.Instr (G.Store (2, G.R 1, G.Z 2))) -> Some [ Lower.C (G.Instr (G.Store (2, G.R 1, G.Z 1))) ] | _ -> None) cmdc);
  print_endline "\n(2) wrong global word: lea of c (word 1) to word 0, the global b";
  expect_caught "cmdc"
    (mutate (function Lower.C (G.Instr (G.Lea (d, 3, G.E (G.Z 1)))) -> Some [ Lower.C (G.Instr (G.Lea (d, 3, G.E (G.Z 0)))) ] | _ -> None) cmdc);
  print_endline "\n(3) wrong import: the call to B.f fetches C.g";
  expect_caught "cmdc"
    (mutate (function Lower.M (G.Fetch (".Limport_B_f", r)) -> Some [ Lower.M (G.Fetch (".Limport_C_g", r)) ] | _ -> None) cmdc);
  print_endline "\n(4) wrong permission constant: the restrict keeps the locality Global";
  expect_caught "temporal_isolation"
    (mutate
       (function
         | Lower.C (G.Instr (G.Restrict (d, s, G.E (G.Perm p)))) ->
             let g = Cheriot_perms.(if p.g = Global then Local else Global) in
             Some [ Lower.C (G.Instr (G.Restrict (d, s, G.E (G.Perm { p with g })))) ]
         | _ -> None)
       ti);
  print_endline "\n(5) live scratch register: the second setbounds_asm clobbers cs0, which holds b";
  expect_caught "cmdc"
    (mutate ~nth:2
       (function Lower.M (G.Setbounds (d, s, w, t1, _)) -> Some [ Lower.M (G.Setbounds (d, s, w, t1, 8)) ] | _ -> None)
       cmdc);
  print_endline "\n(6) integer load without geta (D11): the first clw becomes a capability load";
  expect_caught "cmdc"
    (mutate (function Lower.C (G.Instr (G.GetA (d, s))) when d = s -> Some [] | _ -> None) cmdc);
  print_endline "\n(7) wrong branch target: the beq of the assert library jumps to the function's entry";
  let entry = (List.hd asrt.Lower.funcs).Lower.fo_entry in
  expect_caught "assert"
    (mutate (function Lower.C (G.Instr (G.Jeq (_, x, y))) -> Some [ Lower.C (G.Instr (G.Jeq (G.E (G.Lbl entry), x, y))) ] | _ -> None) asrt);
  print_endline "\n(8) t0 as a scratch register: the first setbounds_asm clobbers ct0, which a later call may read (D34)";
  expect_caught "cmdc"
    (mutate (function Lower.M (G.Setbounds (d, s, w, _, t2)) -> Some [ Lower.M (G.Setbounds (d, s, w, 5, t2)) ] | _ -> None) cmdc);
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
