#!/bin/bash
# Elaborate one file standalone with the project's exact lean options (the
# same flags lakefile.lean sets for the build), reporting the compiler's
# output verbatim.  For a Challenge file the expected outcome is rc=0 with
# exactly one `declaration uses 'sorry'` warning (the intentional target);
# for every other file, rc=0 with empty output.
#
# Usage (from the repository root or from Audit/):
#   bash Audit/check_standalone.sh Audit/GeneratorRenormalization/Challenge.lean
set -u
cd "$(dirname "$0")/.."
SRC="$1"
OUTPUT=$(lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true \
  -Dlinter.deprecated=true "$SRC" 2>&1)
RC=$?
printf '%s\n' "$OUTPUT"
echo "rc=$RC output-bytes=$(printf '%s' "$OUTPUT" | wc -c) file=$SRC"
exit $RC
