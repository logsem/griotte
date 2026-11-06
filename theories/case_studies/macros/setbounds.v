From griotte Require Import machine_parameters assembler.

Section Setbounds.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.

  (** CHERIoT's [ct.csetbounds rdst, rsrc, len]: [rdst] gets [rsrc] with
      the bounds [a, a + len), [a] the address of [rsrc] (the tag is
      cleared when they are not within the bounds of [rsrc]).
      [deviation] Griotte has no [CSetBounds]: the macro computes the
      bounds in the scratch registers [t1] and [t2], which it clobbers
      (the translator chooses them dead), and [Subseg] sets them, exactly
      (CHERIoT may round the bounds of large lengths). The
      length [len] is in words. [rdst] may be [rsrc]; [t1] and [t2] are
      distinct from [rsrc] and from each other, and [t1] may be [rdst]
      when [rdst] is not [rsrc]. *)
  Definition setbounds_asm (rdst rsrc : RegName) (len : Z) (t1 t2 : RegName) : list asm_code :=
    [
      geta t1 rsrc;
      add t2 t1 len;
      subseg rdst rsrc t1 t2
    ].

  (** The assembled macro. *)
  Definition setbounds (rdst rsrc : RegName) (len : Z) (t1 t2 : RegName) : list instr :=
    [ machine_instructions.GetA t1 rsrc;
      machine_instructions.Add t2 (inr t1) (inl len);
      machine_instructions.Subseg rdst rsrc (inr t1) (inr t2) ].
  Definition setbounds_instrs (rdst rsrc : RegName) (len : Z) (t1 t2 : RegName) : list Word :=
    encodeInstrsW (setbounds rdst rsrc len t1 t2).
End Setbounds.
