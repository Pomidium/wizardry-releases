#!/usr/bin/env sh
# wizardry installer. Re-run it to update.
#
#   curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install.sh | sh
#
# Environment:
#   WIZARDRY_HOME      where wizardry lives           (default: ~/.wizardry)
#   WIZARDRY_BIN_DIR   where the command is linked   (default: ~/.local/bin)
#   WIZARDRY_REPO      git URL or path to clone      (default: https://github.com/Pomidium/wizardry-releases.git)
#   WIZARDRY_REF       branch or tag to install      (default: main)
#   WIZARDRY_SKIP_RTK  set to 1 to leave rtk alone   (default: install rtk if it is missing)

set -eu

HOME_DIR="${WIZARDRY_HOME:-$HOME/.wizardry}"
BIN_DIR="${WIZARDRY_BIN_DIR:-$HOME/.local/bin}"
REPO="${WIZARDRY_REPO:-https://github.com/Pomidium/wizardry-releases.git}"
REF="${WIZARDRY_REF:-main}"
APP_DIR="$HOME_DIR/app"

say() { printf 'wizardry: %s\n' "$1"; }
die() { printf 'wizardry: %s\n' "$1" >&2; exit 1; }

# The whole script is in a function so a download cut off midway runs nothing.
main() {
  command -v git >/dev/null 2>&1 || die "git is required"
  command -v node >/dev/null 2>&1 || die "Node.js 22.19 or newer is required (https://nodejs.org)"
  command -v npm >/dev/null 2>&1 || die "npm is required (it ships with Node.js)"
  node -e 'const [a, b] = process.versions.node.split(".").map(Number); process.exit(a > 22 || (a === 22 && b >= 19) ? 0 : 1)' \
    || die "Node.js 22.19 or newer is required; found $(node -v)"

  # wizardry was called izardry: an install under the old name is carried over, with a link left
  # at the old path so open sessions and saved plugin paths keep working.
  if [ -z "${WIZARDRY_HOME:-}" ] && [ ! -e "$HOME_DIR" ] && [ -d "$HOME/.izardry" ] && [ ! -L "$HOME/.izardry" ]; then
    say "moving ~/.izardry to ~/.wizardry"
    mv "$HOME/.izardry" "$HOME_DIR"
    ln -s .wizardry "$HOME/.izardry"
  fi
  mkdir -p "$HOME_DIR"
  if [ -d "$APP_DIR/.git" ]; then
    say "updating $APP_DIR"
    git -C "$APP_DIR" fetch --quiet --depth 1 origin "$REF"
    git -C "$APP_DIR" checkout --quiet --detach FETCH_HEAD
  elif [ -e "$APP_DIR" ]; then
    die "$APP_DIR exists and is not a wizardry checkout; move it away and run again"
  else
    say "downloading into $APP_DIR"
    git clone --quiet --depth 1 --branch "$REF" "$REPO" "$APP_DIR" \
      || die "could not clone $REPO"
  fi

  # Automatic updates follow the ref that was installed.
  git -C "$APP_DIR" config wizardry.ref "$REF"

  say "installing dependencies and building"
  (cd "$APP_DIR" && npm install --ignore-scripts --no-audit --no-fund --loglevel=error && npm run --silent build)

  mkdir -p "$BIN_DIR"
  ln -sf "$APP_DIR/dist/bin.js" "$BIN_DIR/wizardry"

  if [ "${WIZARDRY_SKIP_RTK:-}" != "1" ] && ! command -v rtk >/dev/null 2>&1 && [ ! -x "$HOME/.local/bin/rtk" ]; then
    say "installing rtk (condensed command output; set WIZARDRY_SKIP_RTK=1 to skip)"
    if command -v brew >/dev/null 2>&1; then
      brew install rtk || say "could not install rtk; wizardry works without it"
    else
      curl -fsSL https://raw.githubusercontent.com/rtk-ai/rtk/refs/heads/master/install.sh | sh \
        || say "could not install rtk; wizardry works without it"
    fi
  fi

  say "installed $("$BIN_DIR/wizardry" --version 2>/dev/null || echo wizardry) at $BIN_DIR/wizardry"
  case ":$PATH:" in
    *":$BIN_DIR:"*) ;;
    *) say "$BIN_DIR is not on your PATH. Add this to your shell profile: export PATH=\"$BIN_DIR:\$PATH\"" ;;
  esac
  say "log in with \`wizardry auth login\` if you have not used Pi on this machine, then run \`wizardry\`"
}

main "$@"
