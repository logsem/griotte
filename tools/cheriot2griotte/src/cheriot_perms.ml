(* Permissions: CHERIoT's permission bits and Griotte's (Perm, Locality)
   pairs (theories/opsem/permissions.v), for the lowering of
   [ct.candperm] with a constant mask to [restrict ... (encodePermPair
   (P, g))].

   CHERIoT bits (the ISA's [CGetPerm]/[CAndPerm] layout, cheri.h's
   CHERIPermission):
     0 GL global          1 LG load global      2 SD store
     3 LM load mutable    4 SL store local      5 LD load
     6 MC load/store cap  7 SR system regs      8 EX execute
     9 US unseal         10 SE seal            11 U0 user 0

   The Griotte pair (BPerm rx w dl dro, g) has the CHERIoT image:
     GL <-> g = Global
     LD <-> rx in {R, X, XSR}      EX <-> rx in {X, XSR}
     SR <-> rx = XSR
     SD <-> w in {W, WL}           SL <-> w = WL
     LG <-> dl = LG                LM <-> dro = LM
     MC <-> LD or SD (Griotte has no separate capability-access
            permission: a readable or writable capability loads and
            stores capabilities)
     US, SE, U0: none (sealing permissions are on [WSealRange] only).
   A CHERIoT set has a Griotte counterpart when it is the image of a
   pair (then of exactly one) and is representable in CHERIoT's
   compressed encoding (the ISA's formats; GL is free in all of them):
     cap read-write  LD MC SD + any of SL LM LG
     cap read-only   LD MC + any of LM LG
     cap write-only  SD MC
     data only       any of LD SD (no MC)
     executable      EX LD MC + any of SR LM LG
     sealing         any of US SE U0
   [CAndPerm] of a non-representable set gives a smaller set; the
   lowering only accepts representable results, so the AND is exact. *)

type rx = Orx | R | X | XSR
type w = Ow | W | WL
type dl = LG | DL
type dro = LM | DRO
type loc = Global | Local
type pair = { rx : rx; w : w; dl : dl; dro : dro; g : loc }

let gl = 0 and lg = 1 and sd = 2 and lm = 3 and sl = 4 and ld = 5
let mc = 6 and sr = 7 and ex = 8 and us = 9 and se = 10 and u0 = 11

let bit_names =
  [| "GL"; "LG"; "SD"; "LM"; "SL"; "LD"; "MC"; "SR"; "EX"; "US"; "SE"; "U0" |]

let has s b = s land (1 lsl b) <> 0
let of_list l = List.fold_left (fun acc b -> acc lor (1 lsl b)) 0 l
let all = 0xfff

let string_of_bits s =
  let l = List.filter (has s) (List.init 12 Fun.id) in
  if l = [] then "{}" else "{" ^ String.concat " " (List.map (fun b -> bit_names.(b)) l) ^ "}"

let to_bits p =
  let rd = p.rx <> Orx and wr = p.w <> Ow in
  of_list
    (List.concat
       [ (if p.g = Global then [ gl ] else []);
         (if rd then [ ld ] else []);
         (if p.rx = X || p.rx = XSR then [ ex ] else []);
         (if p.rx = XSR then [ sr ] else []);
         (if wr then [ sd ] else []);
         (if p.w = WL then [ sl ] else []);
         (if p.dl = LG then [ lg ] else []);
         (if p.dro = LM then [ lm ] else []);
         (if rd || wr then [ mc ] else []) ])

(* CHERIoT's compressed formats: is the set representable exactly? *)
let representable s =
  let s = s land lnot (1 lsl gl) in
  let only allowed = s land lnot (of_list allowed) = 0 in
  let req l = List.for_all (has s) l in
  (req [ ld; mc; sd ] && only [ ld; mc; sd; sl; lm; lg ])
  || (req [ ld; mc ] && only [ ld; mc; lm; lg ])
  || s = of_list [ sd; mc ]
  || only [ ld; sd ]
  || (req [ ex; ld; mc ] && only [ ex; ld; mc; sr; lm; lg ])
  || only [ us; se; u0 ]

(* The Griotte pair whose image is exactly [s], if any. *)
let of_bits s =
  let rx = if has s sr then XSR else if has s ex then X else if has s ld then R else Orx in
  let w = if has s sl then WL else if has s sd then W else Ow in
  let p =
    { rx; w; dl = (if has s lg then LG else DL); dro = (if has s lm then LM else DRO);
      g = (if has s gl then Global else Local) }
  in
  if to_bits p = s land all then Some p else None

let rx_flows a b =
  match (a, b) with
  | Orx, _ -> true
  | R, (R | X | XSR) -> true
  | X, (X | XSR) -> true
  | XSR, XSR -> true
  | _ -> false

let w_flows a b = match (a, b) with Ow, _ -> true | W, (W | WL) -> true | WL, WL -> true | _ -> false
let dl_flows a b = match (a, b) with DL, _ -> true | LG, LG -> true | _ -> false
let dro_flows a b = match (a, b) with DRO, _ -> true | LM, LM -> true | _ -> false
let loc_flows a b = match (a, b) with Local, _ -> true | Global, Global -> true | _ -> false

(* PermFlowsTo and LocalityFlowsTo (permissions.v): Restrict keeps the
   tag only then. *)
let flows a b = rx_flows a.rx b.rx && w_flows a.w b.w && dl_flows a.dl b.dl && dro_flows a.dro b.dro && loc_flows a.g b.g

(* The CHERIoT [CAndPerm] of a capability of Griotte permissions [src]
   with [mask], as a Griotte pair; [Error] says why it has none. *)
let and_perm src mask =
  let s = to_bits src in
  if not (representable s) then Error (Printf.sprintf "the source permissions %s are not representable in CHERIoT" (string_of_bits s))
  else
    let r = s land mask land all in
    if not (representable r) then
      Error (Printf.sprintf "%s & %#x = %s is not representable in CHERIoT (candperm would drop more)" (string_of_bits s) (mask land all) (string_of_bits r))
    else
      match of_bits r with
      | None -> Error (Printf.sprintf "%s has no exact Griotte counterpart" (string_of_bits r))
      | Some p ->
          if not (flows p src) then Error "the Griotte restriction does not flow to the source (Restrict would clear the tag)"
          else Ok p

(* {1 Printing, in the notations of permissions.v} *)

let base p =
  match (p.rx, p.w) with
  | Orx, Ow -> None
  | Orx, W -> Some "WO" | Orx, WL -> Some "WLO"
  | R, Ow -> Some "RO" | R, W -> Some "RW" | R, WL -> Some "RWL"
  | X, Ow -> Some "RX" | X, W -> Some "RWX" | X, WL -> Some "RWLX"
  | XSR, Ow -> Some "XSR" | XSR, W -> Some "XSRW" | XSR, WL -> Some "XSRWL"

let suffix p =
  match (p.dl, p.dro) with LG, LM -> "" | DL, LM -> "_DL" | LG, DRO -> "_DRO" | DL, DRO -> "_DL_DRO"

let string_of_dl = function LG -> "LG" | DL -> "DL"
let string_of_dro = function LM -> "LM" | DRO -> "DRO"
let string_of_loc = function Global -> "Global" | Local -> "Local"

(* The Perm, as a notation of permissions.v. *)
let perm_notation p =
  match base p with
  | None -> Printf.sprintf "O %s %s" (string_of_dl p.dl) (string_of_dro p.dro)
  | Some b ->
      let sfx = suffix p in
      (* XSR_, XSRW_, XSRWL_ end with an underscore without a suffix. *)
      if sfx = "" && (p.rx = XSR) then b ^ "_" else b ^ sfx

(* A Rocq identifier suffix for the pair: rw_dl_local, ro_dro_global. *)
let ident p =
  let n = match base p with None -> "o_" ^ String.lowercase_ascii (string_of_dl p.dl ^ "_" ^ string_of_dro p.dro) | Some _ -> String.lowercase_ascii (perm_notation p) in
  let n = if n <> "" && n.[String.length n - 1] = '_' then String.sub n 0 (String.length n - 1) else n in
  n ^ "_" ^ String.lowercase_ascii (string_of_loc p.g)

let string_of_pair p = Printf.sprintf "(%s, %s)" (perm_notation p) (string_of_loc p.g)

(* The permissions of [cgp], hence of any capability derived from it by
   the tool's patterns (auicgp pair, csetbounds): (RW, Global), as
   Griotte's firmware builds it (firmware_ok.v), and CHERIoT's loader
   (globals from the RWGlobal root: GL LD MC SD LM LG, no SL). *)
let cgp_perms = { rx = R; w = W; dl = LG; dro = LM; g = Global }
