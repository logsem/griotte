From Stdlib Require Import ZArith.

#[local] Open Scope Z_scope.

(** The layout of the trusted stack, with CHERIoT's names (with
    [CONFIG_MSHWM]), counted in words: each field takes one word, including
    the 32-bit fields that CHERIoT packs in pairs. mtdc holds a capability
    to the base of the trusted stack, which starts with the register save
    area: [mepcc], the registers x1 to x15 (register xi at word i),
    [hazardPointers] (a store-only capability to the two hazard slots of
    the thread), [mstatus], [mcause], [mshwm] and [mshwmb]. It is
    followed by the header ([frameoffset], the offset from the base of the
    next free frame, and [threadID]) and by the frames. A frame holds the
    stack pointer of the caller, the export table of the callee and the
    number of error handlers invoked. The first frame, [frames[0]], is the
    entry frame of the thread, which the return path never pops. *)
Definition TrustedStack_offset_mepcc : Z := 0.
Definition TrustedStack_offset_cra : Z := 1.
Definition TrustedStack_offset_csp : Z := 2.
Definition TrustedStack_offset_cgp : Z := 3.
Definition TrustedStack_offset_ctp : Z := 4.
Definition TrustedStack_offset_ct0 : Z := 5.
Definition TrustedStack_offset_ct1 : Z := 6.
Definition TrustedStack_offset_ct2 : Z := 7.
Definition TrustedStack_offset_cs0 : Z := 8.
Definition TrustedStack_offset_cs1 : Z := 9.
Definition TrustedStack_offset_ca0 : Z := 10.
Definition TrustedStack_offset_ca1 : Z := 11.
Definition TrustedStack_offset_ca2 : Z := 12.
Definition TrustedStack_offset_ca3 : Z := 13.
Definition TrustedStack_offset_ca4 : Z := 14.
Definition TrustedStack_offset_ca5 : Z := 15.
Definition TrustedStack_offset_hazardPointers : Z := 16.
Definition TrustedStack_offset_mstatus : Z := 17.
Definition TrustedStack_offset_mcause : Z := 18.
Definition TrustedStack_offset_mshwm : Z := 19.
Definition TrustedStack_offset_mshwmb : Z := 20.
Definition TSTACK_REGFRAME_SZ : Z := 21.
Definition TSTACK_HEADER_SZ : Z := 2.
Definition TrustedStack_offset_frameoffset : Z := TSTACK_REGFRAME_SZ.
Definition TrustedStack_offset_threadID : Z := TSTACK_REGFRAME_SZ + 1.
Definition TrustedStack_offset_frames : Z := TSTACK_REGFRAME_SZ + TSTACK_HEADER_SZ.
Definition TrustedStackFrame_offset_csp : Z := 0.
Definition TrustedStackFrame_offset_calleeExportTable : Z := 1.
Definition TrustedStackFrame_offset_errorHandlerCount : Z := 2.
Definition TrustedStackFrame_size : Z := 3.
