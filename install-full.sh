#!/usr/bin/env sh
# wizardry, with everything its default plugins can use. Re-run it to update.
#
#   curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install-full.sh | sh
#
# It is install.sh with WIZARDRY_FULL=1: wizardry and rtk as always, and on top of them
#   Bend       which the bend plugin runs                        (~/.bend)
#   jacobian   exact mathematics, for the defintire plugin       (WIZARDRY_HOME/tools)
#   hillclimb  long searches over programs, for defintire too    (WIZARDRY_HOME/tools)
# and uv, which installs the last two with a Python of their own. About 700 MB more than the
# plain install. Everything install.sh reads from the environment is read here too.

set -eu

# The whole script is in a function so a download cut off midway runs nothing.
main() {
  command -v curl >/dev/null 2>&1 || { printf 'wizardry: curl is required\n' >&2; exit 1; }
  FROM="${WIZARDRY_INSTALLER:-https://raw.githubusercontent.com/Pomidium/wizardry-releases/${WIZARDRY_REF:-main}/install.sh}"
  case "$FROM" in
    http://*|https://*) curl -fsSL "$FROM" | WIZARDRY_FULL=1 sh ;;
    *) WIZARDRY_FULL=1 sh "$FROM" ;;
  esac
}

main "$@"
