From griotte Require Import machine_parameters resources switcher.

(** The user-thread number of a thread. The context-switch thread has no
    trusted stack: it gets thread 0's layout, which it never uses. *)
Definition thread_index (th : Thread) : nat :=
  match th with UserThread i => i | CtxSwitch => 0 end.

(** The layout of the section's thread: [b_trusted_stack] in a thread section
    is that thread's. *)
#[global] Instance tlayout_of {swlayout : switcherLayout} (th : Thread) : threadLayout :=
  swl_thread (thread_index th).
#[global] Instance tlayout_wf_of `{MP : MachineParameters}
  {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  (th : Thread) : threadLayoutWf (tlayout := tlayout_of th) := swl_thread_wf _.
#[global] Arguments tlayout_of : simpl never.
#[global] Arguments tlayout_wf_of : simpl never.
