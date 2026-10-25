#!/bin/sh
# The Dune rules of the initial-state prints (included by rules/dune): for
# each argument theories/case_studies/<dir>/<cs>_firmware.v, which defines
# <cs>_initial_state_ok_annot, a driver <cs>_print.v instantiated from
# driver.v.in, and a rule that compiles it and promotes its output into
# theories/case_studies/<dir>/<cs>_initial_state_predicate.txt. The
# directories excluded from the build are skipped.
for f in "$@"; do
  dir=$(basename "$(dirname "$f")")
  cs=$(basename "$f" _firmware.v)
  case "$dir" in counter|hts_no_ownership|*_binary) continue ;; esac
  cat <<EOF
(rule
 (with-stdout-to
  ${cs}_print.v
  (run sed -e s/@DIR@/${dir}/g -e s/@CS@/${cs}/g %{dep:../driver.v.in})))

(rule
 (targets ${cs}_initial_state_predicate.txt ${cs}_print.vo)
 (deps
  ${cs}_print.v
  %{project_root}/theories/firmware/print.vo
  %{project_root}/theories/case_studies/${dir}/${cs}_firmware.vo)
 (mode
  (promote
   (into ../../theories/case_studies/${dir})
   (only ${cs}_initial_state_predicate.txt)))
 (action
  (with-stdout-to
   ${cs}_initial_state_predicate.txt
   (pipe-stdout
    (run rocq compile -q -noglob
     -Q %{project_root}/theories griotte
     -Q %{project_root}/machine_utils/theories machine_utils
     ${cs}_print.v)
    (run grep -vxF -e "- : unit = ()")))))

EOF
done
