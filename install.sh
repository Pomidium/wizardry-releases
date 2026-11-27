#!/usr/bin/env sh
# wizardry installer. Re-run it to update.
#
#   curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install.sh | sh
#
# With everything the default plugins can use (Bend, jacobian, hillclimb; about 700 MB more):
#
#   curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install-full.sh | sh
#
# Environment:
#   WIZARDRY_HOME      where wizardry lives           (default: ~/.wizardry)
#   WIZARDRY_BIN_DIR   where the command is linked   (default: ~/.local/bin)
#   WIZARDRY_REPO      git URL or path to clone      (default: https://github.com/Pomidium/wizardry-releases.git)
#   WIZARDRY_REF       branch or tag to install      (default: main)
#   WIZARDRY_SKIP_RTK  set to 1 to leave rtk alone   (default: install rtk if it is missing)
#   WIZARDRY_WITH_TOOLS set to 1 to also install jacobian and hillclimb for the defintire plugin,
#                      inside WIZARDRY_HOME (about 650 MB with the Python they need; default: no)
#   WIZARDRY_WITH_BEND set to 1 to also install Bend, which the bend plugin runs (default: no)
#   WIZARDRY_FULL      set to 1 for both of those: what install-full.sh does

set -eu

HOME_DIR="${WIZARDRY_HOME:-$HOME/.wizardry}"
BIN_DIR="${WIZARDRY_BIN_DIR:-$HOME/.local/bin}"
REPO="${WIZARDRY_REPO:-https://github.com/Pomidium/wizardry-releases.git}"
REF="${WIZARDRY_REF:-main}"
APP_DIR="$HOME_DIR/app"
PATH_AT_START="$PATH"

say() { printf 'wizardry: %s\n' "$1"; }
die() { printf 'wizardry: %s\n' "$1" >&2; exit 1; }

# The whole script is in a function so a download cut off midway runs nothing.
main() {
  command -v git >/dev/null 2>&1 || die "git is required"
  # A machine with no Node.js gets one, inside wizardry's own directory. One that has an old
  # Node.js is told: putting a newer one in front of it could break what else uses it.
  command -v node >/dev/null 2>&1 || PATH="$HOME_DIR/node/bin:$PATH"
  command -v node >/dev/null 2>&1 || get_node
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
  # The Node.js wizardry brought is found the way wizardry is: by a link beside it.
  if [ -x "$HOME_DIR/node/bin/node" ]; then
    for each in node npm npx; do
      [ -e "$BIN_DIR/$each" ] && [ ! -L "$BIN_DIR/$each" ] || ln -sf "$HOME_DIR/node/bin/$each" "$BIN_DIR/$each"
    done
  fi

  if [ "${WIZARDRY_SKIP_RTK:-}" != "1" ] && ! command -v rtk >/dev/null 2>&1 && [ ! -x "$HOME/.local/bin/rtk" ]; then
    say "installing rtk (condensed command output; set WIZARDRY_SKIP_RTK=1 to skip)"
    if command -v brew >/dev/null 2>&1; then
      brew install rtk || say "could not install rtk; wizardry works without it"
    else
      curl -fsSL https://raw.githubusercontent.com/rtk-ai/rtk/refs/heads/master/install.sh | sh \
        || say "could not install rtk; wizardry works without it"
    fi
  fi

  # jacobian (exact mathematics) and hillclimb (long searches), which the defintire plugin uses
  # when they are there. They are large, so only when asked, and kept inside wizardry's directory.
  if [ "${WIZARDRY_WITH_BEND:-}" = "1" ] || [ "${WIZARDRY_FULL:-}" = "1" ]; then
    if command -v bend >/dev/null 2>&1 || [ -x "${BEND_HOME:-$HOME/.bend}/bin/bend" ]; then
      say "Bend is already installed"
    else
      say "installing Bend into ${BEND_HOME:-$HOME/.bend}"
      curl -fsSL https://bend-lang.com/install.sh | sh >/dev/null 2>&1 || say "could not install Bend; wizardry works without it"
    fi
  fi

  if [ "${WIZARDRY_WITH_TOOLS:-}" = "1" ] || [ "${WIZARDRY_FULL:-}" = "1" ]; then
    say "installing jacobian and hillclimb into $HOME_DIR/tools (about 650 MB)"
    command -v uv >/dev/null 2>&1 || [ -x "$HOME/.local/bin/uv" ] || curl -LsSf https://astral.sh/uv/install.sh | sh \
      || say "could not install uv; wizardry works without these tools"
    UV=$(command -v uv 2>/dev/null || echo "$HOME/.local/bin/uv")
    for tool in jacobian hillclimb; do
      UV_TOOL_DIR="$HOME_DIR/tools" UV_TOOL_BIN_DIR="$HOME_DIR/bin" UV_PYTHON_INSTALL_DIR="$HOME_DIR/tools/python" \
        "$UV" tool install --quiet --python 3.12 "$tool" || say "could not install $tool; wizardry works without it"
    done
  fi

  say "installed $("$BIN_DIR/wizardry" --version 2>/dev/null || echo wizardry) at $BIN_DIR/wizardry"
  NEW=""
  case ":$PATH_AT_START:" in
    *":$BIN_DIR:"*) ;;
    *) on_path && NEW="Open a new terminal window first. " ;;
  esac
  say "${NEW}Type \`wizardry auth login\` once to sign in, then \`wizardry\` and say what you want."
}

# Node.js, from nodejs.org, checked against its published checksum, into wizardry's directory.
get_node() {
  command -v curl >/dev/null 2>&1 || die "Node.js 22.19 or newer is required (https://nodejs.org), and there is no curl to fetch it with"
  case "$(uname -s)" in Darwin) OS=darwin ;; Linux) OS=linux ;; *) die "Node.js 22.19 or newer is required (https://nodejs.org)" ;; esac
  case "$(uname -m)" in arm64|aarch64) ARCH=arm64 ;; x86_64|amd64) ARCH=x64 ;; *) die "Node.js 22.19 or newer is required (https://nodejs.org)" ;; esac
  FROM="${WIZARDRY_NODE_DIST:-https://nodejs.org/dist/latest-v22.x}"
  TMP=$(mktemp -d)
  say "no Node.js here: fetching one into $HOME_DIR/node"
  curl -fsSL "$FROM/SHASUMS256.txt" -o "$TMP/sums" || die "could not reach nodejs.org; install Node.js 22.19 or newer (https://nodejs.org) and run this again"
  LINE=$(grep " node-v.*-$OS-$ARCH\.tar\.gz\$" "$TMP/sums" | head -n 1)
  FILE=${LINE##* }
  [ -n "$FILE" ] || die "nodejs.org has no Node.js for $OS-$ARCH; install Node.js 22.19 or newer and run this again"
  curl -fsSL "$FROM/$FILE" -o "$TMP/$FILE" || die "could not download $FILE"
  if command -v shasum >/dev/null 2>&1; then SUM=$(shasum -a 256 "$TMP/$FILE"); else SUM=$(sha256sum "$TMP/$FILE"); fi
  [ "${SUM%% *}" = "${LINE%% *}" ] || die "$FILE does not match its checksum; nothing was installed"
  rm -rf "$HOME_DIR/node" && mkdir -p "$HOME_DIR/node"
  tar -xzf "$TMP/$FILE" -C "$HOME_DIR/node" --strip-components 1 || die "could not unpack $FILE"
  rm -rf "$TMP"
  PATH="$HOME_DIR/node/bin:$PATH"
}

# Put BIN_DIR on the PATH of new terminals: one line in the shell's profile, once.
# False (and it says what to add) when asked not to, or when the shell is not one it knows.
on_path() {
  LINE="export PATH=\"$BIN_DIR:\$PATH\""
  case "${SHELL##*/}" in
    zsh) PROFILE="$HOME/.zprofile" ;;
    bash) if [ -f "$HOME/.bash_profile" ]; then PROFILE="$HOME/.bash_profile"; else PROFILE="$HOME/.profile"; fi ;;
    *) PROFILE="" ;;
  esac
  if [ "${WIZARDRY_NO_PROFILE:-}" = "1" ] || [ -z "$PROFILE" ]; then
    say "$BIN_DIR is not on your PATH. Add this to your shell profile: $LINE"
    return 1
  fi
  grep -qsF "$LINE" "$PROFILE" || printf '\n# Added by wizardry, so that the command is found.\n%s\n' "$LINE" >> "$PROFILE"
  say "added $BIN_DIR to your PATH in $PROFILE"
}

main "$@"
