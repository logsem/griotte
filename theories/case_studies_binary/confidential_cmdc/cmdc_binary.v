From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fetch switcher.

(** * Confidentiality variant of the CMDC example

    The trusted compartment [main] owns two cells [b] and [c], and two
    secrets [secret_b] and [secret_c] in its private data. It calls the
    untrusted entry point [B.f] with a capability to [b], and then the
    untrusted entry point [C.g] with a capability to [c]:

    [c <- secret_c ; b <- 0 ; call B.f(b)]
    [c <- 0 ; b <- secret_b ; call C.g(c)]
    [halt]

    Each cell only holds a secret while the other compartment runs: [c] is
    secret to [B], and [b] is secret to [C].

    Both runs execute the same code; they only differ in the secrets. The
    code consists of eight blocks; the first four end with the call to
    [B.f]. *)

Section CMDC_Main.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )
     cgp := (RW, Global, b_data, e_data, b_data )

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSealed ot_switcher B.f
     b_main + 2 : WSealed ot_switcher C.g

     b_data + 0 : b
     b_data + 1 : c
     b_data + 2 : secret_b
     b_data + 3 : secret_c
   *)
  Definition cmdc_conf_main_code : list Word :=
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* set c <- secret_c *)
      Lea cgp 3%Z;
      Load ct0 cgp;
      Lea cgp (-2)%Z;
      Store cgp ct0;

      (* set b <- 0 *)
      Lea cgp (-1)%Z;
      Store cgp 0%Z;

      (* call B.f b *)
      Mov ca0 cgp;
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> b *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 1 ct1 ct0 cs0 (* ct1 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp
    ]
    ++
    encodeInstrsW [
      (* set c <- 0 *)
      Lea cgp 1%Z;
      Store cgp 0%Z;
      Mov ca0 cgp;

      (* set b <- secret_b *)
      Lea cgp 1%Z;
      Load ct0 cgp;
      Lea cgp (-2)%Z;
      Store cgp ct0;

      (* call C.g c *)
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> c *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 2 ct1 ct0 cs0 (* ct1 -> {C.g}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp;
      Halt
      (* #"main_e" *)
    ].

  (** The code before the return from [B.f]: the first four blocks of
      [cmdc_conf_main_code]. *)
  Definition cmdc_conf_pre_B_code : list Word :=
    encodeInstrsW [
      Lea cgp 3%Z;
      Load ct0 cgp;
      Lea cgp (-2)%Z;
      Store cgp ct0;
      Lea cgp (-1)%Z;
      Store cgp 0%Z;
      Mov ca0 cgp;
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1
    ]
    ++ fetch_instrs 0 ctp ct0 ct1
    ++ fetch_instrs 1 ct1 ct0 cs0
    ++
    encodeInstrsW [
      Jalr cra ctp
    ].

  Definition cmdc_conf_main_data (secret_b secret_c : Z) : list Word :=
    [WInt 0; WInt 0; WInt secret_b; WInt secret_c].

  Definition cmdc_conf_main_imports `{!switcherLayout} (B_f C_g : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g
    ].

  Definition cmdc_conf_B_f_args : nat := 1.
  Definition cmdc_conf_C_g_args : nat := 1.

End CMDC_Main.
