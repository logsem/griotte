(* A minimal Itanium demangler for the names the examples use: a plain
   function or variable name [_Z<len><name><params>] ([_Z3runv] -> [run],
   [_Z7awkwardPU10chericcallFvvE] -> [awkward]) and an internal-linkage one
   [_ZL<len><name>...] ([_ZL6locked] -> [locked]). The parameter types are
   dropped: the examples do not overload. Any other name is returned
   unchanged, so the tool never depends on an external demangler. *)

let demangle s =
  let n = String.length s in
  if n < 3 || String.sub s 0 2 <> "_Z" then s
  else
    let i = if s.[2] = 'L' then 3 else 2 in
    let rec digits j = if j < n && s.[j] >= '0' && s.[j] <= '9' then digits (j + 1) else j in
    let j = digits i in
    if j = i then s
    else
      let len = int_of_string (String.sub s i (j - i)) in
      if len <= 0 || j + len > n then s else String.sub s j len

(* The key of a demangled objdump symbol, to match it with [demangle]:
   [run()] -> [run], [griotte_assert(int, int)] -> [griotte_assert]. *)
let objdump_key s =
  match String.index_opt s '(' with Some i -> String.sub s 0 i | None -> s
