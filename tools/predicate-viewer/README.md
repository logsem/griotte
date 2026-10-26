# Predicate viewer

One self-contained HTML page showing case studies' initial-state predicates:
the register file, then memory regions as a linear address tape with code
constants listed inline (one row per word: offset and instruction, or the asm
listing with its labels when the print has it), the capabilities in registers
and memory with an arrow to the word at their cursor and a bracket over their
bounds, export entries and error handlers with an arrow to their PCC
offset, and each region's constraints. Filters highlight capabilities by
kind, locality, sealing otype or permission; incoming arrows on hovering a
region are a setting, off by default.

    dune build prints/rules
    python3 -I tools/predicate-viewer/viewer.py OUT.html \
      _build/default/prints/rules/*_initial_state_predicate.json

Inputs are the JSON prints written by `theories/firmware/print_json.v`
(format: `schema.md` here), left in the build directory. Standard library
only.

- `model.py`: builds the viewer's model (regions, cells, capabilities,
  registers, constraints, code) from one JSON print;
  `python3 -I model.py FILE.json` prints a summary.
- `viewer.py`: embeds the models into `viewer_template.html` (each code
  constant once for all case studies) and writes the page.
- `viewer_template.html`: the page (vanilla JS, no external scripts). It
  draws only the selected case study; code rows past the first 40 of a
  constant are rendered when they come near the viewport, and arrows are
  drawn only for the hovered item and the selected band.
