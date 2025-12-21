From cap_machine Require Import machine_parameters assembler.

Section Fetch.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (* Expects r1 := e_stk ; r2 := a_stk *)
  (** Fetch the value at the address (pc_b + n).
     - rdst contains the fetched value.
     - rscratch1 and rscratch2 are both clobbered.
   **)
  Definition fetch_asm (n : Z) (rdst rscratch1 rscratch2 : RegName) : list asm_code :=
    [
      mov rdst PC;
      getb rscratch1 rdst;
      geta rscratch2 rdst;
      sub rscratch1 rscratch1 rscratch2;
      lea rdst rscratch1;
      lea rdst n;
      load rdst rdst;
      mov rscratch1 0;
      mov rscratch2 0
    ].

  Definition fetch (n : Z) (rdst rscratch1 rscratch2 : RegName) :=
    Eval compute in assemble (fetch_asm n rdst rscratch1 rscratch2).
  Definition fetch_instrs (n : Z) (rdst rscratch1 rscratch2 : RegName) : list Word :=
    encodeInstrsW (fetch n rdst rscratch1 rscratch2).
End Fetch.
