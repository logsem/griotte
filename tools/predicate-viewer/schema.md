# Predicate viewer: JSON schema (version 1)

`theories/firmware/print_json.v` writes one file per case study,
`_build/default/prints/rules/<cs>_initial_state_predicate.json` (Dune rules
in `prints/`, not promoted), from the same annotated predicate
`<cs>_initial_state_ok_annot` as the `.txt` print. The viewer in this
directory reads these files.

The rule: **Rocq keeps the predicate's structure and does not interpret it.**
It writes the tree of the predicate (sections, conjuncts, existentials,
equations, lists, unions), with the words it recognises in a structured form
and everything else as text. The viewer works out the regions, capabilities
and arrows. Text is always the term printed with `FwPrintNotations`, as in the
`.txt`, but on one line (no layout, no padding).

## Top level

```json
{
  "schema": 1,
  "case_study": "vae",
  "predicate": "vae_initial_state_ok",
  "params": [{"names": ["flag"], "type": "Addr"}, {"names": ["σ"], "type": "ExecConf"}],
  "body": [Stmt],
  "code": {"<name>": Code}
}
```

- `params`: the predicate's parameters, grouped as in the `.txt` header.
- `body`: the predicate's top-level statements in order. Sections are
  statements (`section`), so the order is that of the print.
- `code`: see below.

## Statements (`Stmt`)

Every statement may carry `"comment": string`, taken from its `note`.
They follow `walk` in `print.v`:

| `k` | Fields | Source |
|---|---|---|
| `section` | `title`, `body: [Stmt]` | `section t q` |
| `exists` | `binders: [{names, type}]`, `body: [Stmt]` | consecutive `∃`, grouped as in `ex_line` |
| `eq` | `lhs: string`, `rhs: Rhs`, optional `lhs_kind` | `l = r` |
| `disjoint` | `ranges: [{b: Addr, e: Addr, comment?}]` | `ranges_disjoint l` |
| `regs_except` | `bank`, `except: [string]`, `all: [string]`, `value: Word`, `some`, `text` | `∀ r : RegName, r ∉ {[…]} → reg σ !! r = Some w` |
| `prop` | `text` | anything else |

`regs_except`: `bank` is `gpr` (or `sreg` for the same shape on `sreg σ`),
`except` the registers of the set, `all` every register of the bank in order
(`all_registers` for `gpr`), `value` the word, `some: true` for `Some w`, and
`text` the statement as text. The viewer lists every register of `all` not in
`except` with `value`.

`∧` is flattened into consecutive statements. The existential offsets that
the `.txt` renames and hoists (`rename_offsets`) are left as ordinary
`exists` in place.

`lhs_kind` names the left-hand sides the viewer needs to recognise, when the
printer matches them:

- `{"kind": "field", "field": "cmpt_imports", "of": "main"}`: a record
  projection applied to a variable (`cmpt_*`, `b_*`/`e_*`, `flag_assert`, …).
- `{"kind": "reg", "bank": "gpr", "name": "cgp"}`: `reg σ !! r`;
  `"bank": "sreg"` for `sreg σ !! r`; `{"kind": "reg", "bank": "pc"}` for
  `pcc σ`.
- `{"kind": "mem"}`: `mem σ`; `{"kind": "shadow"}`: `shadowtbl σ`.
- `{"kind": "incr", "base": Addr, "off": string}`: the layout equations
  `A + L = Some B`, with `off` the text of `L` (for example
  `length (cmpt_imports main)`); their rhs is an `addr`.

### Right-hand sides (`Rhs`)

- `{"r": "word", "word": Word}`: a word, or `Some w` with `"some": true`.
- `{"r": "addr", "addr": Addr}`: an address, or `Some a` with `"some": true`
  (the rhs of `incr` equations).
- `{"r": "list", "items": [Word]}`: a literal list (`cons`), each item with
  its optional `comment`.
- `{"r": "union", "parts": [MemPart]}`: a union (the memory).
- `{"r": "term", "text": string}`: anything else.

### Memory parts (`MemPart`)

```json
{"region": true, "base": Addr, "content": [Piece], "comment": "main, PCC range"}
{"region": false, "text": "initial_heap_memory", "comment": "heap, zeroed"}
```

`region: true` for `mem_region b ws`. `content` is the word list split on
`++` and `::`:

- `{"words": [Word]}`: a literal list, or the words consed in front
  (`w1 :: w2 :: rest` gives `{"words": [w1, w2]}` then the pieces of `rest`).
- `{"term": string}`: any other list term, for example `cmpt_code main`,
  `switcher_instrs` or `replicate 100 (WInt 0)`. If it is a constant with an
  entry in `code`, the entry has the same name. An application of a
  constant may also carry `"head": name` and `"args": [Word]`, each argument
  a structured word when it is one and `{"w": "term", …}` otherwise (so the
  capabilities passed to `initial_trusted_stack_content` get arrows).
  When unfolding the head constant and reducing (delta of the head, beta,
  not a full computation) gives a literal list or a concatenation (`++`,
  `::`), the piece also carries `"unfolded": [Piece]`, split like `content`.
  Example: `switcher_data_words (ot_switcher sw)` gives one `words` piece
  with its 5 words, the unsealing key among them;
  `initial_trusted_stack_content …` gives `replicate` pieces and `words`
  pieces with the capabilities at their slots. In an unfolded piece,
  `replicate n w` gets `"count": k` when `n` computes to a closed numeral
  `k` (its text, e.g. `Z.to_nat TrustedStack_offset_hazardPointers`, stays in
  `args`). A `replicate` piece at the top of `content` is not unfolded: the
  viewer reads it from `head`/`args`.

## Words (`Word`)

```json
{"w": "int", "text": "0"}
{"w": "cap", "p": "RX", "g": "Global", "b": Addr, "e": Addr, "a": Addr}
{"w": "sentry", "kind": "FwdDisable", "p": "XSRW_", "g": "Local", "b": Addr, "e": Addr, "a": Addr}
{"w": "sealrange", "perm": "SU", "g": "Global", "b": Addr, "e": Addr, "a": Addr}
{"w": "sealed", "ot": Addr, "inner": Word}
{"w": "entry", "mie": "InterruptEnabled", "args": "1", "stack": "4", "off": "12"}
{"w": "term", "text": "cmpt_exp_tbl_handler main"}
```

- `int`: `WInt z`; `text` is `z` printed (a numeral or a term such as
  `ExportTable_no_handler`). When `z` is a closed term that is not a numeral, `value` is its
  computed numeral (`stats_handler_pcc_off` gives `10`,
  `ExportTable_no_handler` gives `65535`); likewise `args_value`, `stack_value` and `off_value` on `entry`
  words. Handler words (the export table's 3rd and 4th) are PCC offsets from
  the compartment's PCC base, like entry offsets; 65535 means no handler. `entry` is `WInt (encode_entry_point …)`.
- Only tagged capabilities are structured (`SCap true …`, `WSentry k true …`,
  `SSealRange true …`); anything else is `term`.
- `sealrange.perm`: `SU`, `S`, `U` or `O`, as in `FwPrintNotations`. Its
  bounds are otypes, given as `Addr` too.

### Addresses (`Addr`)

```json
{"text": "cmpt_b_pcc main ^+ 3", "base": "cmpt_b_pcc main", "off": "3"}
{"text": "a_switcher_call sw ^+ label \"exception_entry_asm\"", "base": "a_switcher_call sw", "label": "exception_entry_asm"}
{"text": "(e_stack t0 ^- StackEntry_reserved_space)%f", "base": "e_stack t0", "off": "-StackEntry_reserved_space"}
{"text": "b_switcher sw"}
```

`text` is always present. `base` and `off` (or `label`, for the switcher
labels of `label_eq`) are present when the address is
`finz.incr_default base off` or a subtraction. Otherwise the address has no
offset and `base` is left out (the viewer uses `text`).

## Code (`code`)

The constants found in a `{"term": …}` memory piece, or under `length c` in a
layout equation (for example `switcher_call_instrs`), whose body computes to a
closed list of words, under their name:

```json
"switcher_instrs": {
  "words": [Word],
  "instrs": ["Mov ct2 csp", "..."],
  "labels": {"0": ".Lswitch_csp_check", "17": "..."}
}
```

- `words`: the list, one per address.
- `instrs` (optional): when every word decodes to an instruction that
  re-encodes to the same word, the decoded instructions (opsem syntax), one
  per entry; same length as `words`.
- `labels` (optional): index (from the constant's first word) → assembler
  label, named as in the asm (leading `.` kept), when the assembler block is
  at hand cheaply (for example the switcher's `switcher_asm`).

- `asm` (optional): the assembler source the constant comes from, when
  found (see below), as a flat list of lines in source order:

  ```json
  "asm_source": "vae_main_asm",
  "asm": [
    {"label": ".Lvae_awkward_check", "depth": 0},
    {"instr": "lea ct0 .Lvae_awkward_check", "index": 9, "depth": 0},
    {"symbol": "flag", "index": 10, "depth": 0},
    {"block": 1}
  ]
  ```

  `index` is the word the line assembles to (from the constant's first word;
  labels and block markers take no word). `instr` is the asm instruction
  printed in asm syntax, with its label expressions (`Asm_lbl`, `Asm_plus`,
  `Asm_minus`) as written in the source, not resolved to offsets. `depth`
  is the nesting of `ASM_Local` blocks (labels are local to their block).
  `{"block": n}` starts the `n`-th block of a `list (list asm_code)`.
  The asm is found without touching the firmware files: by name
  (`<p>_code` or `<p>_instrs` beside `<p>_asm`) or an explicit table in
  `print_json.v`, and kept only when assembling it gives `words`.

Constants that depend on a variable (`cmpt_code main` is `vae_main_code` by
an `eq` statement, not a constant) are resolved by the viewer, which follows
the `eq` statements of `field` kind to a `term` naming a constant in `code`.
