From griotte Require Import machine_parameters assembler.

Section Fetch.
  Import Asm_Griotte.
  #[local] Coercion Z.of_nat : nat >-> Z.
  Context `{MP: MachineParameters}.

  (** Fetch the word named by the data symbol [sym] (an import entry,
      declared with [#@] before the code of the enclosing program) with a
      PC-relative load into [rdst]. The symbol resolves in the enclosing
      program: the macro is inlined in its code, not assembled separately. *)
  Definition fetch_asm (sym : string) (rdst : RegName) : list asm_code :=
    [
      auipcc rdst sym;
      load rdst rdst
    ].

  (** The assembled macro, where [off] is the resolved offset of the symbol
      from the address of the [auipcc]. *)
  Definition fetch (off : Z) (rdst : RegName) : list instr :=
    [machine_instructions.Auipcc rdst off; machine_instructions.CLoad rdst rdst 0].
  Definition fetch_instrs (off : Z) (rdst : RegName) : list Word :=
    encodeInstrsW (fetch off rdst).
End Fetch.
