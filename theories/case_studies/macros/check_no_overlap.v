From cap_machine Require Import machine_parameters assembler.

Section Check_No_Overlap.
  Import Asm_Griotte.
  Local Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  Definition check_no_overlap_asm_pre (rsrc1 rsrc2 r1 r2 : RegName) : list asm_code :=
      [
        getb r1 rsrc1; (* r1 := b1 *)
        getb r2 rsrc2; (* r2 := b2 *)
        lt r1 r1 r2;   (* r2 := (if b1 < b2 then 1 else 0) *)
        jnz "b1_<_b2" r1;
        #"b2_<=_b1";
        (* we need b1 <= (e2-1) *)
        getb r1 rsrc1; (* r1 := b1 *)
        gete r2 rsrc2; (* r2 := e2 *)
        sub r2 r2 1;   (* r2 := e2-1 *)
        lt r1 r2 r1;   (* r1 := (if (e2-1) < b1 then 1 else 0) *)
        jnz "b1_<=_e2'" r1;
        #"e2'_<_b1";
        fail;
        #"b1_<=_e2'";
        jmp "end";

        #"b1_<_b2";
        (* we need b2 <= (e1-1) *)
        getb r2 rsrc2; (* r2 := b2 *)
        gete r1 rsrc1; (* r1 := e1 *)
        sub r1 r1 1;   (* r1 := e1-1 *)
        lt r1 r1 r2;   (* r1 := (if (e1-1) < b2 then 1 else 0) *)
        jnz "b2_<=_e1'" r1;
        #"e1'_<_b2";
        fail;
        #"b2_<=_e1'";
        jmp "end";
        #"end";
        mov r1 0;
        mov r2 0
        ].

  Definition check_no_overlap_asm_env :=
    Eval vm_compute in (compute_asm_code_env (check_no_overlap_asm_pre PC PC PC PC)).2.
  Definition check_no_overlap_asm ( rsrc1 rsrc2 r1 r2 : RegName) :=
    Eval compute in resolve_labels_macros (check_no_overlap_asm_pre rsrc1 rsrc2 r1 r2) check_no_overlap_asm_env.
  Definition check_no_overlap (rsrc1 rsrc2 r1 r2 : RegName) : list instr :=
    Eval compute in assemble (check_no_overlap_asm rsrc1 rsrc2 r1 r2).
  Definition check_no_overlap_instrs (rsrc1 rsrc2 r1 r2 : RegName) : list Word :=
    encodeInstrsW (check_no_overlap rsrc1 rsrc2 r1 r2).

End Check_No_Overlap.
