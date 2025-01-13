# Griotte - Fork from Monotone Cerise

This directory contains the Coq mechanization accompanying the submission "Le
Temps des Cerises: Efficient Temporal Stack Safety on Capability Machines using
Directed Capabilities".

# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.12.0 and Iris 3.3.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --deps-only --repositories=default,coq-released=https://coq.inria.fr/opam/released .
   eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.10.0:

```
    # Add the coq-released repo (skip if you already have it)
    opam repo add coq-released https://coq.inria.fr/opam/released
    # Install Coq 8.12.0 (skip if already installed)
    opam install coq.8.12.0
    opam update
    opam install coq-iris.3.3.0
```

### Troubleshooting

For Option 1, if the invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y --deps-only .` (this will continue from where it
failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

We recommend that you have **32Gb of RAM+swap**. Please be aware that the
development takes around 2 to 3 hours to compile. In particular, the files
`theories/examples/awkward_example_u.v` and `theories/examples/stack_object.v` 
can each take up to 30 minutes to compile.

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem (and `make fundamental-binary` to build up until the binary
FTLR, or `make full-abstraction` to build up until the full abstraction
theorem). Each usually takes up 20 minutes.

## Checking for admits

The command `make check-admitted` will grep for `'admit\|Admitted\|ADMITTED'` in
the Coq files.

# Documentation

After building the development, documentation generated using Coqdoc can be
created using `make html`. 

Then, browse the `html/toc.html` file.

Note that we have included a copy of the generated html files as a supplemental material. 

# Organization

First is a lookup table for the definitions in the paper.

| *paper*                                                 | *file* or *folder*                | *name*                                                        |
|---------------------------------------------------------|-----------------------------------|---------------------------------------------------------------|
| Machine words, machine state and instructions (Fig 2)   | machine\_base.v                   |                                                               |
| Permission hierarchy (Fig 4)                            | machine\_base.v                   | `PermFlowsTo`                                                 |
| Operational semantics: instruction semantics (Fig 5)    | cap\_lang.v                       | `exec`                                                        |
| Standard State Transition System (Fig 6)                | region\_invariants.v              | `region_type`/`std_rel_{pub}{priv}{pub_plus}`                 |
| Logical relation (Fig 7)                                | logrel.v                          | `interp`/`interp_expression`/`interp_registers`               |
| Theorem 4.1  (FTLR)                                     | fundamental.v                     | `fundamental_from_interp`                                     |
| Assembly of Listing 7 (Fig 8)                           | downwards\_lse{\_preamble}.v      | `lse_instrs`/`downwards_lse_preamble_instrs`                  |
| Theorem 4.2                                             | downwards\_lse\_adequacy.v        | `downwards_lse_adequacy`                                      |
| Assembly of Listing 9 (Fig 9)                           | stack\_object{\_preamble}.v       | `stack_object_passing_instrs`/`stack_object_preamble_instrs`  |
| Theorem 4.3                                             | stack\_object\_adequacy.v         | `obj_adequacy`                                                |
| Theorem 6.1                                             | full\_abstraction.v               | `compile_fully_abstract`                                      |
| Definition 6.2 (forward simulation)                     | simulation.v                      | `forward_simulation`                                          |
| Lemma 6.3                                               | simulation.v                      | `fsim_terminates`                                             |

Next we describe the file organization of the implementation. 

The organization of the `theories/` folder is as follows.

## Operational semantics

- `addr_reg.v`: Defines registers and the set of (finite) memory addresses.

- `machine_base.v`: Contains the syntax (permissions, capability, instructions,
  ...) of the capability machine.

- `machine_parameters.v`: Defines a number of "settings" for the machine, that
  parameterize the whole development (e.g. the specific encoding scheme for
  instructions, etc.).

- `cap_lang.v`: Defines the operational semantics of the machine, and the
  embedding of the capability machine language into Iris.

## Program logic (Unary)

- `region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `rules/rules_base.v`: Contains some of the core resource algebras for the program
  logic, namely the definition for points to predicates with permissions.

- `rules/rules.v`: Imports all the Hoare triple rules for each instruction. These
  rules are separated into separate files (located in the `rules/` folder).

## Logical relation (Unary)

- `multiple_updates.v`: Auxiliary definitions to reason about multiple updates
  to a world.

- `region_invariants_transitions.v`: Lemmas about standard transitions

- `region_invariants.v`: Definitions for standard resources, and the shared
  resources map *sharedResources*. Contains some lemmas for "opening" and
  "closing" the map, akin to opening and closing invariants.

- `region_invariants_revocation.v`: Lemmas for revoking standard resources
  (setting *Temporary* invariants to a *Revoked* state).

- `region_invariants_static.v`: Lemmas for manipulating frozen standard
  resources.

- `region_invariants_batch_uninitialized.v`: Lemmas for manipulating uninitialized 
  standard resources.

- `region_invariants_allocation.v`: Lemmas for allocating a range of standard
  resources.

- `sts.v`: The definition of *stsCollection*, and associated lemmas. In particular:
  priv/pub/temporal future world relations (all these definitions are 
  parametrized by the standard states and three relations over them transitions. 
  These are instantiated in `region_invariants.v`)

- `logrel.v`: The definition of the unary logical relation.

- `monotone.v`: Proof of the monotonicity of the value relation with regards to
  public future worlds, and private future worlds for non local words.

- `fundamental.v`: Contains *Theorem 4.1: fundamental theorem of logical
  relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.

## Proof sketch of the FTLR (Appendix A)

The correspondance between the lemmas and the Coq statements is as follows.

| *paper*                                                 | *file* or *folder*                | *name*                                                        |
|---------------------------------------------------------|-----------------------------------|---------------------------------------------------------------|
| Lemma A.1 (address relative monotonicity)               | monotone.v                        | `interp_monotone_a`                                           |
| Lemma A.2 (address relative weakening)                  | sts.v                             | `related_sts_a_weak_world`                                    |
| Lemma A.3 (private monotonicity)                        | monotone.v                        | `interp_monotone_nm`                                          |
| Theorem 4.1 (FTLR)                                      | fundamental.v                     | `fundamental_from_interp`                                     |

## Binary Model (Appendix C)

The binary model is fully contained in the `binary_model` folder.

The binary model uses the same program logic as in the unary model, and a similar 
family of rules for the specification part of the refinement.
These rules are all in the `binary_model/rules_binary` folder. In particular, 
the `binary_model/rules_binary/rules_binary_base.v` file contains the resource 
algebra used for the specification part of the refinement.

- `region_invariants{_XX}_binary.v`: Binary version of the *sharedResources*.

- `logrel_binary.v`: Binary logical relation (Fig. 11).

- `fundamental_binary.v`: Binary fundamental theorem of logical relations (Theorem C.1).
  Each case is proved in a separate file located in `binary_model/ftlr_binary/`.

## Case studies: Integrity

In the `examples` folder:

- `macros/*` : Specifications for some useful macros

- `macros/scall_u.v`: Specification of a safe calling convention for
  a URWLX Directed stack. The specification is split up into two parts:
  the prologue is the specification for the code before the jump, the epilogue
  is the specification for the activation record.

- `macros/malloc.v`: A simple malloc implementation, its specification, and
  a proof that it is valid.

- `downwards_lse{_preamble}{_adequacy}.v`: The assembly definition and proof of 
  *Listing 7*. The `preamble` file creates the closure, and the `adequacy` file
  applies the adequacy of Iris weakest preconditions to prove the final theorem,
  *Theorem 4.2*.

- `stack_object{_preamble}{_adequacy}.v`: The assembly definition and proof of 
  *Listing 9*. The `preamble` file creates the closure, and the `adequacy` file
  applies the adequacy of Iris weakest preconditions to prove the final theorem,
  *Theorem 4.3*.

- `awkward_example{_u}{_preamble}{_adequacy}.v`: The assembly definition and proof of 
  *Listing 5*. The `preamble` file creates the closure, and the `adequacy` file
  applies the adequacy of Iris weakest preconditions to prove the final theorem.

## Case studies: Confidentiality

In the `binary_model/examples_binary` folder:

- `macros_binary` : Exports all macro specifications for the "spec" side of the
  binary logical relation

- `confidentiality{_adequacy}{_adequacy_theorem}.v`: The assembly definition and 
  proof of contextual equivalence of *Listing 8*. The adequacy files contain
  the contextual equivalence statements and proofs. They apply the linking definitions
  from `linking.v` (see below).

## Linking

- `linking.v`: Defines the general theory of components, well-formed components,
  linking and contexts as presented in Appendix B.

## Overlay semantics

In the `overlay` folder:

- `lang.v`: Defines the overlay semantics. Note that we use a more restrictive
  definition of *safe* words as explained in Appendix D due to some Coq
  engineering issues.

- `call.v`: Defines the implementation on the base machine of the call instruction.

## Full abstraction theorem

- `simulation.v`: Defines the general theory of forward simulations and prove
  additional corollaries.
  
- `overlay_cap_lang_sim.v`: Proves the forward simulation between the overlay
  semantics and the base capability machine. In particular, `sim` is the
  simulation relation, and `overlay_to_cap_lang_fsim` is the proof of the
  forward simulation.
  
- `full_abstraction.v`: Defines fully abstract compilation, and Theorem
  `compile_fully_abstract` proves the full abstraction result of Theorem 6.1 in
  the paper.

# Differences with the paper

Some definitions have different names from the paper.  

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper*   | *name in mechanization*   |
|-------------------|---------------------------|
| Executable        | Instr Executable          |
| Halted            | Instr Halted              |
| Failed            | Instr Failed              |

For technical reasons (so that Iris considers a single instruction as an atomic step), 
the execution mode is interweaved with the "Instr Next" mode, which reduces to a value.
The Seq _ context can then return and continue to the next instruction. The full expression 
for an executing program is Seq (Instr Executable).

In the model:

| *name in paper*     | *name in mechanization* |
|---------------------|-------------------------|
| Frozen              | Monostatic              |
| stsCollection       | full_sts_world          |
| sharedResources     | region                  |
| Temporary           | Monotemporary           |
| temporal transition | std_rel_pub_plus        |

In `scall_u.v` : the scall macro is slightly unfolded, as it does not include the part of 
the calling convention which stores local state on the stack. That part is inlined into the 
examples.
