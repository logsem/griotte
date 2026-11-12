From griotte Require Import machine_parameters assembler.
From griotte Require Import fetch.

Class assertLayout : Type :=
  mkAssertLayout {
      b_assert : Addr ;
      e_assert : Addr ;
      a_flag : Addr ;
    }.

Section Assert_Code.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (* Maintains a flag storing whether an assert has failed.

     A library, laid out as CHERIoT lays one out: its import table, then its
     code. Word 0 of the import table is the switcher slot, which the loader
     always writes; word 1 is the import of the flag, a read-write
     capability to the shared object [assert_flag], which the code fetches
     PC-relatively. The entry is at offset [assert_entry_offset]. The import
     words are data symbols: they are not assembled. *)

  (* Asserts (ct0 == ct1). Jumps back to cra.
     Clobbers cra, ct0, ct1.
   *)
  Definition assert_subroutine_asm : list asm_code :=
    [
      #@".Limport_switcher"; (* the switcher slot *)
      #@".Limport_assert_flag"; (* cap: (RW, flag, flag + 1, flag) *)
      #"assert_entry";
      sub ct0 ct0 ct1;
      jnez ("assert_fail")%asm ct0;
      #"assert_success";
      mov ct0 0;
      mov ct1 0;
      ret; (* return *)
      #"assert_fail"
    ] ++
    fetch_asm ".Limport_assert_flag" ct1 ++
    [
      store ct1 1;
      mov ct0 0;
      mov ct1 0;
      ret
    ].

  (** The offset of the entry from the base of the library: after the
      switcher slot and the flag import. *)
  Definition assert_entry_offset : nat := 2.
  Lemma assert_entry_offset_label :
    label_offset assert_subroutine_asm "assert_entry" = assert_entry_offset.
  Proof. reflexivity. Qed.

  Definition assert_subroutine : list instr :=
    Eval compute in assemble assert_subroutine_asm.
  Lemma assert_subroutine_assembles : asm_ok (assemble_check assert_subroutine_asm).
  Proof. asm_check. Qed.
  Definition assert_subroutine_instrs : list Word :=
    encodeInstrsW assert_subroutine.

  (* assert macro:
   - fetch the assert entry point, the import named by the data symbol [sym]
   - execute the assert subroutine, saving [cra] in [rscratch]

   - rdst and rscratch are both clobbered
   *)
  Definition assert_asm (sym : string) (rdst rscratch : RegName) : list asm_code :=
    fetch_asm sym rdst ++
    [
      mov rscratch cra;
      jalr cra rdst;
      mov cra rscratch;
      mov rscratch 0;
      mov rdst 0
    ].
End Assert_Code.

Section Assert_Assembled.
  Context `{MP: MachineParameters}.

  (** The assembled macro, where [off] is the resolved offset of the import
      from the address of the first instruction. *)
  Definition assembled_assert (off : Z) (rdst rscratch : RegName) : list instr :=
    fetch off rdst ++
    [ Mov rscratch (inr cra);
      Jalr cra rdst;
      Mov cra (inr rscratch);
      Mov rscratch (inl 0%Z);
      Mov rdst (inl 0%Z) ].
  Definition assert_instrs (off : Z) (rdst rscratch : RegName) : list Word :=
    encodeInstrsW (assembled_assert off rdst rscratch).
End Assert_Assembled.

(** The sentry of the entry point of the assert routine, which the assert
    macro fetches and jumps to: the base of the library plus
    [assert_entry_offset]. The address is written [b_assert ^+ 2], the form
    to which [addr_off b assert_entry_offset] reduces in the import words
    of a firmware ([fw_word_of], [firmware_ok]), so that the two agree
    syntactically. *)
Definition assert_entry `{assertLayout} : Word :=
  Sentry Inherit RX Global b_assert e_assert (b_assert ^+ 2)%a.
