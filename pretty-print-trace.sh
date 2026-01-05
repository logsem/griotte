#!/usr/bin/env bash
#
# pretty-print-trace.sh
#
# Usage: ./pretty-print-trace.sh <trace‑json-file>
#
# The script extracts every `coqc` record, keeps only the generated
# *.vo files, sorts them by duration (longest first) and prints a table
# like:
#
#   Time        | File Name
#   ------------+----------------------------------------
#   0m58.65s    | theories/logrel/ftlr/Jalr.vo
#   12m03.27s   | some/very/long/path/file.vo
#   …
#   0m02.19s    | Total
#
# The first column is padded to a constant width (12 characters) so the
# vertical bar stays aligned even when the minutes part grows to two or
# three digits.
#
# Requires: jq, awk
# -------------------------------------------------------------------------

set -euo pipefail

# ---------- helpers ----------
usage() {
    cat <<EOF >&2
Usage: $0 <trace‑json-file>

Pretty‑print a table of the .vo files produced by each coqc command,
showing the time each command took (format 0m00.41s) and a total line.

Requires: jq, awk
EOF
    exit 1
}

# ---------- argument check ----------
if [[ $# -ne 1 ]]; then
    usage
fi

TRACE_FILE="$1"

if [[ ! -f "$TRACE_FILE" ]]; then
    echo "Error: file not found – $TRACE_FILE" >&2
    exit 1
fi

# ---------- main pipeline ----------
jq -r '
  .[]                                   # each element of the top‑level array
  | select(.name == "coqc")             # keep only coqc commands
  | .dur as $dur_us                     # duration in micro‑seconds

  # walk over the files produced by this invocation
  | (.args.target_files // [])[]         # empty list if the key is missing
  | select(endswith(".vo"))             # keep only *.vo files

  # strip the leading “_build/default/”
  | sub("^_build/default/"; "") as $file

  # µs → seconds (floating point)
  | ($dur_us / 1000000) as $sec

  # output:  <seconds><TAB><file>
  | "\($sec)\t\($file)"
' "$TRACE_FILE" |
# sort by numeric duration, descending (largest first)
sort -nr -k1,1 |
awk -F'\t' '
BEGIN{
    # Header (first column width = 12 chars, second = 40 chars)
    col1_width = 12
    col2_width = 40
    printf "%-*s | %-*s\n", col1_width, "Time", col2_width, "File Name"
    printf "%s-+-%s\n", \
           gensub(/./, "-", "g", sprintf("%*s", col1_width, "")), \
           gensub(/./, "-", "g", sprintf("%*s", col2_width, ""))
}
{
    sec  = $1 + 0               # duration in seconds (numeric)
    file = $2

    total += sec                # accumulate total time (seconds)

    # split seconds into whole minutes + remaining seconds (2 decimals)
    min = int(sec/60)
    rem = sec - min*60

    # build the time string once
    time_str = sprintf("%dm%05.2fs", min, rem)

    # print each line, left‑justified in the fixed‑width column
    printf "%-*s | %s\n", col1_width, time_str, file
}
END{
    # ----- total line (same format, labelled “Total”) -----
    tot_min = int(total/60)
    tot_sec = total - tot_min*60
    total_str = sprintf("%dm%05.2fs", tot_min, tot_sec)
    printf "%-*s | %s\n", col1_width, total_str, "Total"
}'
