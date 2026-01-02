# Griotte - Formal Verification of Compartmentalisation for CHERIoT

This directory contains the Rocq mechanization accompanying the submission "Griotte".
It provides a model of a capability machine based on [CHERIoT](https://cheriot.org/),
a minimal implementation of the CHERIoT's RTOS switcher's,
and principle to reason about interactions between known and unknown compartments
through the switcher.

# Building the proofs

## Installing the dependencies

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

The development is known to compile with Rocq 9.0.0 and Iris 4.4.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --deps-only --repositories=default,rocq-released=https://rocq-prover.org/opam/released .
   eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.10.0:

```
    opam switch create griotte-test 5.4.0
    # Add the rocq-released repo (skip if you already have it)
    opam repo add rocq-released https://rocq-prover.org/opam/released
    opam update
    # Install Rocq 9.9.0 (skip if already installed)
    opam install dune.3.20.2
    opam install rocq-prover.9.0.0 coq-stdpp.1.12.0 coq-stdpp-bitvector.1.12.0 coq-iris.4.4.0
    opam install rocq-equations
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

We recommend that you have **32Gb of RAM+swap**. Please be aware that the
development takes around 1 to 2 hours to compile. 

## Checking for admits

The command `make check-admitted` will grep for `'admit\|Admitted\|ADMITTED'` in
the Rocq files.

# Organisation

The organisation of the `theories/` folder is as follows.

## Operational semantics `opsem/`

- `addr_reg.v`: Defines registers and the set of (finite) memory addresses.

- `machine_base.v`: Contains the syntax (permissions, capability, instructions,
  ...) of the capability machine.

- `machine_parameters.v`: Defines a number of "settings" for the machine, that
  parameterize the whole development (e.g. the specific encoding scheme for
  instructions, etc.).

- `cap_lang.v`: Defines the operational semantics of the machine, and the
  embedding of the capability machine language into Iris.

## Program logic `program_logic/`

- `rules_base.v`: Contains some of the core resource algebras for the program
  logic, namely the definition for points to predicates with permissions.
  It also contains the Hoare triple rules for the fail cases.

- `rules.v`: Imports all the Hoare triple rules for each instruction. These
  rules are separated into separate files (located in the `rules/` folder).

## Proofmode `proofmode/`

- `solve_addr.v`, `solve_addr_extra.v`, `solve_pure.v` define tactics for
  reasoning about address arithmetic, and (extensible) pure goals related
  to the machine.
  
- `memory_region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `proofmode.v` and `proofmode_instr_rules.v` define tactics for 
  automatically finding the right WP rule to apply while proving 
  the specification of known code.
  

## Model of the Kripke worlds `model/`

- `region_invariants_definitions.v`: 
  Definitions of the standard world and the standard invariant states.
  Also contains lemmas about standard transitions

- `region_invariants.v`: Definitions for standard resources, and the shared
  resources map *sharedResources*. Contains some lemmas for "opening" and
  "closing" the map, akin to opening and closing invariants.

- `multiple_updates.v`: Auxiliary definitions to reason about multiple updates
  to a world.

- `region_invariants_revocation.v`: Lemmas for revoking standard resources
  (setting *Temporary* invariants to a *Revoked* state).

- `region_invariants_allocation.v`: Lemmas for allocating a range of standard
  resources.

- `sts.v`: The definition of *stsCollection*, and associated lemmas. In particular:
  priv/pub/temporal future world relations (all these definitions are 
  parameterised by the standard states and three relations over them transitions. 
  These are instantiated in `region_invariants_definitions.v`)
  
## Logical relation and FTLR `logrel/`

- `call_stack`: Definitions of the logical call-stack resources.

- `seal_store.v`: Definitions of the resources for sealing predicates.

- `logrel.v`: The definition of the unary logical relation.

- `logrel_extra.v`: A collections of lemmas related to world manipulation
  in presence of safe-to-share.

- `monotone.v`: Proof of the monotonicity of the value relation with regards to
  public future worlds, and private future worlds for non local words.

- `fundamental.v`: Contains *Fundamental Theorem of Logical
  Relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.

## Switcher `switcher/`

- `switcher.v`: Code of the Griotte switcher.

- `clear_registers{,_spec}.v` and `clear_stack{_spec}.v`: 
  Code and specifications of registers and stack clearing, 
  used by the switcher.
  
- `switcher_preamble.v`: Definition of the switcher's invariant and 
  sealing predicate for the export table's otype.
  
- `interp_switcher_{call,return}.v`: Proof that the switcher's 
  sentries are safe to execute

- `switcher_spec_{call,return}.v`: Specification and proofs
  of the switcher's sentries for known code, invoking unknown code.

## Case studies `case_studies`

- `switcher_adequacy.v`: Proof of validity of the adversaries exported 
cross-compartment sealed entry points.

- `compartment_layout.v`: Definition of regular compartment's memory layout,
  switcher's memory layout, and assert library memory layout.

- `macros/*` : Specifications for some useful macros

For each examples `<name>`: 
- `name.v`: contains the code, the initial data, the import table and export table of the known
compartment.
- `name_spec{_*}.v` contains the specifications of the example.
- `name_adequacy.v` contains the end-to-end theorem of the example.

The case studies are:
- `cmdc/`: Canonically Mutually Distrustful Compartmentalisation example.

- `counter/`: Counter compartment incrementing an internal counter.

- `dle/`: Example using the deep locality (DL) permission.

- `droe/`: Example using the deep immutability (DRO) permission.

- `lse_downward/`: Example showing that the switcher protects against dangling pointers.

- `vae/`: Very Awkward Example. Shows that the switcher's defines a Well Bracketed 
  calling convention.

- `stack_object/`: Example showing that the switcher can support stack objects,
  but requires additional checks.

# Differences with the paper

Some definitions have different names from the paper.

*name in paper => name in mechanisation*

In the operational semantics:

| *name in paper*   | *name in mechanisation*   |
|-------------------|---------------------------|
| Executable        | Instr Executable          |
| Halted            | Instr Halted              |
| Failed            | Instr Failed              |

For technical reasons (so that Iris considers a single instruction as an atomic step), 
the execution mode is interweaved with the "Instr Next" mode, which reduces to a value.
The Seq _ context can then return and continue to the next instruction. The full expression 
for an executing program is Seq (Instr Executable).

In the model:

| *name in paper*     | *name in mechanisation* |
|---------------------|-------------------------|
| stsCollection       | full_sts_world          |
| sharedResources     | region                  |
| temporal transition | std_rel_pub        |
