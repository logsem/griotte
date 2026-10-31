# Griotte - Verified Compartmentalisation via Capabilities

This directory contains the Rocq mechanisation accompanying the submission "Griotte: Verified Compartmentalisation via Capabilities".
It provides a model of a capability machine based on [CHERIoT](https://cheriot.org/),
a minimal implementation of the CHERIoT's RTOS switcher's,
and principle to reason about interactions between known and unknown compartments
through the switcher.

It also provides a binary (relational) logical relation, used to prove
confidentiality properties: two runs of the same known code, which differ only in
some secret data, cannot be distinguished by unknown compartments, in the sense that
one run halts if and only if the other one does.

# Building the proofs

## With Docker

Build the Docker image.
``` sh
$ docker build -t griotte:griotte .
```

Run the loaded image in a container.

``` sh
$ docker run -it --hostname griotte --rm griotte:griotte
```

It will open a container with a shell, at `/home/rocq/griotte`, under the `rocq` user.
The directory contains the source of the artifact and all the dependencies to build it.

``` sh
rocq@griotte:~/griotte$ make
```

## Without Docker

### Installing the dependencies

Clone this repository
```
git clone --recursive git@github.com:logsem/griotte.git
```

If you forgot `--recursive`
```
git submodule update --init
```

### With Nix.

For only building the proofs:
```
nix build
```

For interactive proving in Emacs, we recommend to install `direnv`,
create a file `.envrc` as follow:
```
#!/usr/bin/env bash

use flake . --impure
```
and to allow `direnv` in the directory `direnv allow`.
It sets up the environment to contain Rocq and all the dependencies.


### With opam.
You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Rocq 9.1.1 and Iris 4.5.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --deps-only --repositories=default,rocq-released=https://rocq-prover.org/opam/released . 4.14.0
   eval $(opam env)
```

- **Option 2 (manual installation)**:

```
    opam switch create griotte-test 4.14.0
    # Add the rocq-released repo (skip if you already have it)
    opam repo add rocq-released https://rocq-prover.org/opam/released
    opam update
    # Install dependencies (skip if already installed)
    opam install dune.3.21.0
    opam install rocq-core.9.1.1 rocq-stdlib.9.0.0 rocq-stdpp.1.13.0 rocq-stdpp-bitvector.1.13.0 rocq-iris.4.5.0 rocq-equations.1.3.1+9.1
```

### Troubleshooting

For Option 1, if the invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y --deps-only .` (this will continue from where it
failed).

## Building

```
dune build --display short -jN  # replace N with the number of CPU cores of your machine
```

We recommend that you have **16Gb of RAM+swap**. Please be aware that the
development takes around 1 to 2 hours to compile. 

## Checking for admits

The command `make check-admitted` will grep for `'admit\|Admitted\|ADMITTED'` in
the Rocq files.

# Organisation

The organisation of the `theories/` folder is as follows.

The submodule `machine_utils/` (a fork of
[logsem/machine_utils](https://github.com/logsem/machine_utils), branch
`griotte`) provides the bounded integers (`finz`) used for addresses and
otypes, and the base tactics `solve_finz` and `solve_pure`.

## Operational semantics `opsem/`

- `registers.v`: Defines registers and system registers.
- `addresses.v`: Defines memory addresses.
- `otypes.v`: Defines otypes.
- `finz_notations.v`: Notations for offsets of addresses and otypes.
- `permissions.v`: Permissions, localities and sealing permissions.
- `machine_word.v`: Machine words: integers, capabilities, sealing ranges,
  sentries and sealed words.
- `memory.v`, `register_file.v`: The memory and the register files.
- `shadow_table.v`: The shadow table of the heap (allocation status of each
  heap address).
- `machine_instructions.v`: The instructions of the machine.

- `machine_base.v`: Exports the syntax (permissions, capability, instructions,
  ...) of the capability machine, defined in the files above.

- `machine_parameters.v`: Defines a number of "settings" for the machine, that
  parameterize the whole development (e.g. the specific encoding scheme for
  instructions, the heap, shadow and revoker regions, etc.).

- `machine_parameters_instance.v`: Defines a concrete instance of the typeclass `MachineParameters`.

- `trap_fault.v`: What a fault reports to the trap entry: its cause code and
  its value (`mcause` and `mtval`), in cheriot-sail's terms.

- `griotte_opsem.v`: The machine configuration and the step of each
  instruction. `griotte_opsem_prop.v`: Lemmas about it.

- `machine_run.v`: The operational semantics as an interpreter, running the
  machine until it halts or stops after a fault.

- `assembler.v`: An assembler with labels and symbols, used to write the code
  of the switcher, the allocators and the case studies.

## Program logic `program_logic/`

- `griotte_lang.v`: Defines the embedding of the capability machine language
  into Iris.

- `region_keys.v`: The keys of the regions of the world: a non-heap
  address, or a heap address with its allocation identifier.

- `logical_words.v`: Logical words: a machine word with the identifier of the
  allocation it belongs to (ghost only).

- `alloc_registry.v`: The allocation registry: the range and lifecycle status
  (live, painting, quarantined, dead) of every allocation.

- `erasure.v`: The erasure invariant relating the logical registers and memory
  to the physical machine state.

- `resources.v`: The ghost state of the machine (PC, system registers) and the
  points-to notations.

- `state_interp_def.v`, `state_interp.v`: The state interpretation, its
  opening and closing, and its initialisation.

- `si_modality.v`: The state-interpretation update modality `|~{E}~> P`.

- `crit_link.v`: The part of the state interpretation of a thread that depends
  on the interrupt status and on `mtdc`.

- `resource_maps.v`: Register, system-register and memory maps of points-to.

- `instr_operands.v`: The registers an instruction uses and the increment of
  the logical PC.

- `memory_region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `allocator_resources.v`: The initial heap memory and shadow table of the
  case studies.

- `rules.v`: Imports all the Hoare triple rules for each instruction. These
  rules are separated into separate files (located in the `rules/` folder).
  The `rules/` folder also contains:
  - `rules_base.v`: Contains some of the core resource algebras for the program
    logic, namely the definition for points to predicates with permissions.
    It also contains the Hoare triple rules for the fail cases.
  - `rules_registry.v`: Ghost steps on the allocation registry and the
    address claims.
  - `rules_deref_quar.v`: Dereferencing a capability of a quarantined object
    faults.
  - `rules_trap_entry.v`, `rules_trap_cause.v`: Trap entry, and the exact
    cause and value of a fault.
  - `rules_vcsr.v`: The volatile control and status registers (`MEPCC`,
    `mcause`, `mtval`, `mret`).

## Proofmode `proofmode/`

- `solve_addr.v`, `solve_addr_extra.v`, `solve_pure.v` define tactics for
  reasoning about address arithmetic, and (extensible) pure goals related
  to the machine.

- `classes.v`, `class_instances.v`: Helper classes and instances for
  `solve_pure`, complementing those of `machine_utils`.

- `contiguous.v`: Contiguous address regions.

- `disjoint_regions_tactics.v`: Tactics to prove the disjointness of address
  regions in concrete layouts.

- `tactics_helpers.v`: Helper lemmas and tactics for proofs of known code.

- `code_blocks.v`: Splitting a code into blocks, and the offsets of the blocks
  and of their instructions (`focus_block`).

- `proofmode.v`, `proofmode_instr_rules.v` and `proofmode_instr_support.v`
  define tactics (`iInstr`) for automatically finding the right WP rule
  to apply while proving the specification of known code.

## Model of the Kripke worlds `model/`

*The internal model is not supposed to be used by the user of Griotte.*

- `sts.v`:
  The pure definitions of the worlds (*stsCollection*) and the private and
  public future world relations (parameterised by the standard states and
  two relations over them; instantiated in `world_std_sts.v`).

- `sts_ghost.v`:
  The ghost state of the worlds (*sts_full_world* in the implementation).

- `world_std_sts.v`:
  Definitions of the standard world and the standard states, and lemmas
  about standard transitions.

- `sts_multiple_updates.v`:
  Auxiliary definitions to reason about multiple updates to a world.

- `world_std_revocation.v`:
  Definitions and lemmas to revoke (and restore) the world
  (setting *Temporary* regions to a *Revoked* state).

- `compartment_names.v`: Compartment names and the threads of a compartment.

- `heap_region.v`: The keys of heap objects and their tombstones.

- `seal_store.v`: The resources for sealing predicates.

- `rmap.v`: A generic owned region map over Iris `ghost_map`.

- `region_maps.v`:
  The two region maps of a compartment: the map of Permanent regions,
  whose predicates mention no world, and the local map of a thread, read
  off its local world. Also defines the safety resources of a key
  (`PermRes`, `TmpRes`).

- `region_maps_free.v`: Lemmas for freeing heap objects in the region maps.

- `world_interp.v`:
  The world interpretation (*sharedResources* in the paper): both maps
  of a compartment, possibly with some keys open.

- `world_interp_revocation.v`:
  Lemmas for revoking regions in the world interpretation.

- `world_interp_allocation.v`:
  Lemmas for allocating regions in the world interpretation.

## Interface of Kripke World for the user `model/`

- `world_ghost_theory.v`:
  Ghost theory of world interpretation: opening and closing the world,
  revocation, allocation. Clean interface with the model to ease the
  proofs for the user.

## Logical relation and FTLR `logrel/`

- `logrel.v`: The definition of the unary logical relation; it exports
  its five parts:
  - `logrel_conditions.v`: the conditions on the safety predicates of the
    regions;
  - `logrel_cont.v`: the continuations of the logical relation;
  - `interp.v`: the value relation (`interp`), as a fixpoint;
  - `interp_caps.v`: lemmas about valid capabilities;
  - `interp_world_free.v`: words valid in every world and at every thread.

- `monotone.v`: Proof of the monotonicity of the value relation with regards to
  public future worlds, and private future worlds for non local words.

- `interp_weakening.v`: Validity of capabilities with weaker permissions or
  bounds.

- `region_open.v`: Opening and closing the region of the PC.

- `world_interp_cells.v`: Accessing the cells of the world through a valid
  capability.

- `wp_rules_interp.v`:
  Collection of WP rules relying on safe-to-share arguments.

- `seal_registry.v`: The sealing predicate of a trusted sealer, whose sealed
  objects are each valid in one compartment, through a registry.

- `stack/`:
  - `stack_world_resources.v`: Definition of resources to have a clean
    interface with manipulation of the world, for the stack region.
  - `world_interp_stack.v`: World manipulation in presence of
    safe-to-share stacks.

- `fundamental.v`: Contains *Fundamental Theorem of Logical
  Relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.
  The `ftlr/` folder also contains `ftlr_base.v`, the shape of the cases,
  and `ftlr_step.v`, one step of the theorem from a safe PC.


## Switcher `switcher/`

- `switcher_base.v`: Exports the switcher's code and layout, its invariant and
  the functional specifications of its call and return routines.
  `switcher_base_interp.v` adds the specifications in the logical relation, and
  `switcher_base_ktk.v` the known-to-known specifications.

- `code/`: The code of the switcher and of its macros, with the macros'
  specifications.
  - `switcher.v`: Code and memory layout of the Griotte switcher.
  - `trusted_stack_layout.v`, `export_table_layout.v`: The layouts of the
    trusted stack and of an export table, with CHERIoT's names.
  - `clear_registers{,_spec}.v`, `clear_stack{,_spec}.v`,
    `clear_hazard_slots{,_spec}.v`, `copy_context{,_spec}.v`:
    Code and specifications of the macros clearing the registers, the stack
    and the hazard slots, and copying a register context.
  - `trusted_spill_registers_spec.v`: Spill and reload of the registers to the
    register save area of the trusted stack.
  - `switcher_load_spec.v`, `switcher_macros_spec.v`: Specifications of
    restoring a saved register, and of the macros for the switcher's clients.
  - `switcher_tactics.v`: Tactics on the code of the switcher.

- `common/`: Definitions shared by the proofs of the switcher.
  - `call_stack.v`: Definitions of the logical call-stack resources.
  - `switcher_preamble.v`: Definition of the switcher's invariant.
  - `switcher_sealing.v`: The sealing predicate for the export table's otype.
  - `switcher_namespace.v`: The namespace of the trusted-stack invariant.
  - `switcher_registers.v`: Splitting a register file into a list of registers
    and the rest.
  - `switcher_error_state.v`: Pure definitions about a fault that the switcher
    handles (the error handler's entry, its `ErrorState`).
  - `switcher_{call,return,exception}_states.v`: The interfaces shared by the
    block lemmas of the call routine, the return routine and the exception path.

- `call/`, `callback/`, `exception/`, `failure/`: Block lemmas of the switcher's
  code, one file per region of the code, named after its entry label: the call
  routine, the return routine, the exception path (from the exception entry to
  an error handler), and the failure exits (forced unwind, thread exit,
  exhausted trusted stack, stack too small). `call/call_path.v`,
  `callback/callback_path.v` and `exception/exception_path.v` compose the blocks
  into paths.

- `world/`: Logical steps that do not execute code.
  - `switcher_helpers.v`, `switcher_helpers_cframe.v`: Helpers lemmas to prove
    the switcher specifications.
  - `switcher_call_world.v`: Logical steps of the call routine.
  - `switcher_error_handler.v`: The obligations of a fault that the switcher
    handles: the force-unwind continuation and the invocation of an error
    handler.
  - `switcher_trap_safety.v`: The trap safety of the switcher (safety of its
    exception entry).

- `specs/`: Specifications of the switcher.
  - `interp_switcher_{call,return}.v` (and `interp_switcher_call_gen.v`): Proof
    that the switcher's sentries are safe to execute.
  - `switcher_spec_{call,return}.v` (and the `_gen` files): Specification and
    proofs of the switcher's sentries for known code, invoking unknown code.
  - `switcher_spec_KtK{,_call,_return}.v`: Specifications for calls between
    known compartments.
  - `switcher_exception.v`: Safety of the exception entry of the switcher.
  - `switcher_spec_install.v`: Installation of the context returned by an error
    handler.
  - `switcher_unwind.v`: The returns of the switcher to the caller outside the
    return routine.

## Allocators `allocators/`

A compartment providing a bump allocator with range quarantine: `malloc`
returns a fresh object, and `free` quarantines it and stores to the revoker,
which untags every stale capability to it. Memory is never reused.

- `common/`: The code shared by the allocators (`allocator_common_code.v`),
  their shared resources (`allocator_common_preamble.v`), the specifications of
  the shared macros, header chain and code segments, and the world lemmas used
  by the proofs of `malloc` and `free`.

- `ownership/`: The allocator whose entries take a sealed allocator
  capability, identifying the owner of the objects.
  - `allocator.v`: Code of the allocator compartment.
  - `allocator_owners.v`, `allocator_otype.v`: The ghost state of the owners,
    and the sealing predicate of the allocator capabilities.
  - `allocator_preamble.v`, `allocator_resource_spec.v`: The resources of the
    allocator service, and its initialisation.
  - `allocator_{malloc,free}_spec.v`: Specifications of `malloc` and `free`
    for known code, composed from the files `allocator_*_spec_states.v`,
    `allocator_*_spec_world.v` and `allocator_*_spec_*_blocks_<n>.v`.
  - `allocator_{malloc,free}_safe.v`: Proof that the entries of the allocator
    are safe to execute.
  - `allocator_switcher_spec.v`: Specifications of calls to `malloc` and `free`
    through the switcher.
  - `allocator_adequacy.v`: Layout of the allocator, for the end-to-end theorems.

The allocator without ownership (`no_ownership/`) is currently excluded from
the build.

## Firmware `firmware/`

- `firmware.v`: The abstract description of a firmware: its compartments,
  threads, exports and imports.
- `image.v`: Firmware images: the memory layout of a firmware.
- `firmware_ok.v`: The condition on an image and an initial machine state for a
  firmware.
- `firmware_obligations.v`: The obligations of a firmware, over the resources
  prepared from its initial state.
- `firmware_adequacy.v`: The generic adequacy theorem of firmware images.
- `initial_state.v`: Tactics computing the initial-state predicate of a case
  study.
- `link.v`: A linker laying out a firmware into an image, for concrete
  instances.
- `image_state.v`: The initial state built from an image, and decision
  procedures for the conditions on concrete images.
- `print.v`: Printers for the initial-state predicates and the memory maps of
  concrete images.

## Case studies `case_studies`

- `switcher_adequacy.v`: Proof of validity of the adversaries exported
cross-compartment sealed entry points.

- `adequacy_helpers.v`, `adequacy_common.v`: Helper lemmas for adequacy
  theorems.

- `case_study_spec_helpers.v`: Helpers for the case-study specifications.

- `compartment_layout.v`: Definition of regular compartment's memory layout,
  switcher's memory layout, and assert library memory layout.

- `macros/`: Code and specifications for some useful macros:
  - `assert{,_spec}.v`: The assert library.
  - `fetch{,_spec}.v`: Fetching an import entry.
  - `check_no_overlap{,_spec}.v`: Checks that two capabilities do not overlap.
  - `checkints.v`: Checks that the words of the range of a capability are
    integers.
  - `checkra.v`: Checks the return sentry in `cra`.
  - `is_word_type.v`: Tests the type of a word.
  - `lea_to_base.v`: Moves the cursor of a capability to its base.

- `world_interp_allocation_compartments.v`: Allocating the regions of an
  adversary compartment in the world.

For each examples `<name>`:
- `name.v`: contains the code, the initial data, the import table and export table of the known
compartment.
- `name_firmware.v`: contains the firmware of the example, its image and its
  initial-state predicate.
- `name_spec{_*}.v` contains the specifications of the example.
- `name_spec{_*}_closure.v` contains the specifications of the example,
  when an entry point for known code is involved.
- The proofs of the specifications are split along the blocks of the code:
  `name_spec_states.v` gives the shared definitions (blocks, labels),
  `name_spec_<segment>_blocks_<n>.v` the specifications of groups of blocks,
  and `name_spec_world{_*}.v` the logical steps between them.
- `name_adequacy.v` contains the end-to-end theorem of the example.
- `name_concrete.v` contains a concrete implementation of the adequacy with a concrete
instance of the machine and a concrete adversary.

The case studies are:
- `cmdc/`: Canonically Mutually Distrustful Compartmentalisation example.

- `counter/`: Counter compartment incrementing an internal counter (currently
  excluded from the build).

- `dle/`: Example using the deep locality (DL) permission.

- `droe/`: Example using the deep immutability (DRO) permission.

- `error_handling/`: Example of a trusted compartment with a stackful error
  handler, which recovers from the faults of its entry point.

- `hts_ownership/`: Heap temporal safety: once an object shared with an
  adversary is freed through the allocator, the adversary can no longer
  access it.

- `lse_downward/`: Example showing that the switcher protects against dangling pointers.

- `vae/`: Very Awkward Example. Shows that the switcher's defines a Well Bracketed
  calling convention. The `vae_untrusted_entry_*` files are a variant whose
  thread starts in the adversary.

- `stack_object/`: Example showing that the switcher can support stack objects,
  but requires additional checks.

## Utilities `utils/`

- `stdpp_extra.v`, `iris_extra.v`, `machine_utils_extra.v`: Additional lemmas
  for stdpp, Iris and `machine_utils`.
- `bitblast.v`: A copy of stdpp's experimental bit-blasting tactic.
- `map_simpl.v`, `register_tactics.v`, `mkregion_helpers.v`: Tactics to
  simplify and extract register maps and memory regions.
- `named_props/`: A copy of `iris-named-props` (named conjuncts `"H" ∷ P` and
  `iNamed`); `named_props_extra.v` adds the intro pattern `@`.

## Binary model

The binary model relates two runs of the machine: the *implementation* run,
described by the usual resources (`↦ᵣ`, `↦ₛᵣ`, `↦ₐ`), and the *specification* run,
described by a ghost copy of the machine state (`↣ᵣ`, `↣ₛᵣ`, `↣ₐ`, and `⤇ e` for its
current expression). Both runs execute the same code; the logical relation relates
pairs of words, and is diagonal except for sealed words, whose payloads may differ.
Each directory mirrors its unary counterpart, and files carry a `_binary` suffix.

### Specification side `program_logic_binary/`

- `spec_instance_binary.v`: Ghost state of the specification run, its points-to
  predicates, the invariant `spec_ctx` tying it to an actual execution, and the
  generic lemmas to step the specification run.

- `memory_region_binary.v`: Specification counterparts of the region points-to
  and `codefrag`.

- `rules_binary/`: Rules stepping the specification run, one file per instruction,
  and the determinism lemma of each instruction.

### Proofmode `proofmode_binary/`

- `proofmode_binary.v` and `proofmode_instr_rules_binary.v` define the tactics
  `iInstr_spec`/`iGo_spec`, to step the specification run, and
  `iInstr_lockstep`/`iGo_lockstep`, to step both runs at once.

- `register_tactics_binary.v`: Specification counterparts of the register-map tactics.

### Model of the Kripke worlds `model_binary/`

Copies of the files of `model/` whose definitions involve words, where the shared
resources hold a pair of words: one in the implementation memory and one in the
specification memory. The other files of `model/` are reused unchanged.

### Logical relation and FTLR `logrel_binary/`

- `call_stack_binary.v`: Call stack of the specification run. The logical relation
  relates the two call stacks frame by frame.

- `seal_store_binary.v`: Sealing predicates over pairs of words.

- `logrel_binary.v`: The definition of the binary logical relation.

- `monotone_binary.v`, `stack_world_resources_binary.v`, `wp_rules_interp_binary.v`:
  Binary counterparts of the corresponding unary files.

- `ftlr_binary/fundamental_binary.v`: Contains the binary *Fundamental Theorem of
  Logical Relations*. Each case (one for each instruction) is proved in a separate
  file of `ftlr_binary/`.

### Switcher `switcher_binary/`

- `switcher_preamble_binary.v`: The switcher's invariant, holding the switcher's
  state of both runs.

- `clear_registers_spec_binary.v`, `clear_stack_spec_binary.v`,
  `switcher_macros_spec_binary.v`: Specifications of the macros used by the switcher.

- `interp_switcher_{call,return}_binary.v` (and the `interp_switcher_call_*` files):
  Proof that the switcher's sentries are in the binary logical relation.

- `switcher_spec_{call,return}_binary.v` (and the `switcher_spec_call_*` files):
  Specification and proofs of the switcher's sentries for known code,
  invoking unknown code.

- `switcher_adequacy_binary.v`: Proof of validity of the adversaries exported
  cross-compartment sealed entry points.

### Case studies `case_studies_binary/`

- `adequacy_helpers_binary.v`: Helper lemmas for the end-to-end theorems, in
  particular `binary_adequacy`, which turns a proof in the binary logical relation
  into "if the first run halts, then the second run halts".

- `fetch_spec_binary.v`, `switcher_spec_call_diag_binary.v`: Specifications of
  macros used by the examples.

Each example follows the structure of the unary case studies (`name_binary.v`,
`name_spec{_*}_binary.v`, `name_adequacy_binary.v`, `name_concrete_binary.v`).
Its end-to-end theorem states that, for two initial memories that differ only in
the secret, the first run halts if and only if the second run halts.

The case studies are:
- `confidential_stack/`: A known compartment keeps a secret in its stack frame,
  and leaves a stale copy of it above its stack pointer, before calling an
  unknown compartment.

- `confidential_stack_callee/`: An unknown compartment calls a known compartment,
  which stores a secret in its stack frame before returning.

- `confidential_cmdc/`: Confidentiality variant of the CMDC example: each of two
  unknown compartments never learns the secret of the other one.

- `confidential_write_only/`: A known compartment shares with an unknown
  compartment a write-only capability to a secret.

## KVS example `case_studies/multiuser_kvs`
This case study is the multiuser KVS.
- `kvs.v`: contains the KVS compartment: code, initial data, import and export tables.
- `kvs_preamble.v`: contains the layers of resources necessary to prove the KVS layered specifications.
- `kvs_spec_*.v`: contain the (known) specifications for the KVS functions.
- `kvs_spec_*_safe.v`: contain the proof that the KVS entry points are safe to execute (invoked by an adversary).
- `kvs_main.v` contains the client of the KVS: code, initial data, import and export tables.
- `kvs_main_spec.v`: contains the specification and proof of correctness of the client. Its blocks are specified in `kvs_main_spec_blocks.v`.
- `kvs_adequacy.v`: contains the end-to-end theorem of the KVS case study.
- `kvs_firmware.v`, `kvs_concrete.v`: contain the firmware of the case study and its concrete instance.

## Assumptions `theories/assumptions.v`

The file `assumptions.v` prints the assumptions of the FTLR,
and then of each end-to-end theorems of the case studies,
for the unary and the binary models.

Uncomment the file to check the assumptions. 
Be aware that it can be long to execute (10-15 minutes).

The only axiom our theorems depend on is functional,
which is well-known to be compatible with Rocq's internal theory.
```
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Moreover, our theorem make the following assumptions:
- The typeclass `MachineParameters` from `theories/opsem/machine_parameters.v`,
  which defines well-formed encode/decode functions for instructions and permissions.
- The typeclass `memory_layout` from the respective `*_adequacy.v*` files,
  which defines the memory layout in the initial state of the machine.

# Differences with the paper

Some definitions have different names from the paper.

*name in paper => name in mechanisation*

In the operational semantics:

| *name in paper* | *name in mechanisation* |
|-----------------|-------------------------|
| Running         | Instr Executable        |
| Halted          | Instr Halted            |
| Failed          | Instr Faulted           |

For technical reasons (so that Iris considers a single instruction as an atomic step), 
the execution mode is interweaved with the "Instr Next" mode, which reduces to a value.
The Seq _ context can then return and continue to the next instruction. The full expression 
for an executing program is Seq (Instr Executable).

In the model:

| *name in paper*    | *name in mechanisation* |
|--------------------|-------------------------|
| stsCollection      | sts_full_world          |
| sharedResources    | world_interp_open       |
| stsRes             | world_interp            |
| public transition  | std_rel_pub             |
| private transition | std_rel_priv            |

# For CPP27
For CPP27, we highlight more specifically:
- The directory `theories/case_studies/multiuser_kvs` containing the KVS example.
- The file `theories/logrel/seal_registry.v` containing the registries of trusted sealers,
  which hold the non-persistent resources of their sealed objects.
- The file `theories/model/world_ghost_theory.v` containing
  the interface used by the user to interact with Kripke worlds,
  and `theories/model/seal_store.v` with the lemmas specific to sealing.
