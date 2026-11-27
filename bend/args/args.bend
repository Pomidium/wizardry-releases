# The command line: how it splits between wizardry and Pi, and what is said of it. Part of
# wizardry's decisions (../core.bend); compiled to core/args.mjs. LAWS.bend and PROOF.bend here
# say what must hold.

import Base
import ../core.bend as C

# The command line
# ----------------

# What the first argument asks for.
type Command is Data:
  Help{}
  Version{}
  PiOnly{}
  Auth{}
  Update{}
  Export{}
  Delete{}
  Run{}

def command_pick(help: Bool, version: Bool, pi: Bool, auth: Bool, update: Bool, export: Bool, delete: Bool) -> Command:
  match help version pi auth update export delete:
    case True{} _ _ _ _ _ _:
      Help{}
    case False{} True{} _ _ _ _ _:
      Version{}
    case False{} False{} True{} _ _ _ _:
      PiOnly{}
    case False{} False{} False{} True{} _ _ _:
      Auth{}
    case False{} False{} False{} False{} True{} _ _:
      Update{}
    case False{} False{} False{} False{} False{} True{} _:
      Export{}
    case False{} False{} False{} False{} False{} False{} True{}:
      Delete{}
    case False{} False{} False{} False{} False{} False{} False{}:
      Run{}

def command_of(+first: String) -> Command:
  command_pick(C.has(["--help", "-h"], first), C.has(["--version", "-v"], first),
    C.has(["install", "remove", "uninstall", "list", "config", "mcp"], first),
    String.eq(first, "auth"), String.eq(first, "update"), String.eq(first, "export"), String.eq(first, "delete"))

# wizardry's own options, taken out of the arguments; the rest are Pi's.
type Args is Data:
  Args{extra: List<&2, String>, rest: List<&2, String>}

def extras_pick(value: Bool, dashes: Bool, gate: Bool, h: String, next: List<&2, String>) -> List<&2, String>:
  match value dashes gate:
    case True{} _ _:
      h <> next
    case False{} True{} _:
      Nil{}
    case False{} False{} True{}:
      "gate" <> next
    case False{} False{} False{}:
      next

# The plugins asked for with --gate and --plugin. `value` is set while reading --plugin's value.
def extras(argv: List<&2, String>, +value: Bool) -> List<&2, String>:
  match argv:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      extras_pick(value, String.eq(h, "--"), String.eq(h, "--gate"), h,
        extras(t, Bool.and(Bool.not(value), String.eq(h, "--plugin"))))

def passes_pick(
  value: Bool, dashes: Bool, gate: Bool, plugin: Bool, h: String, t: List<&2, String>, next: List<&2, String>
) -> List<&2, String>:
  match value dashes gate plugin:
    case True{} _ _ _:
      next
    case False{} True{} _ _:
      h <> t
    case False{} False{} True{} _:
      next
    case False{} False{} False{} True{}:
      next
    case False{} False{} False{} False{}:
      h <> next

# The arguments left for Pi. Everything from `--` on passes unchanged.
def passes(argv: List<&2, String>, +value: Bool) -> List<&2, String>:
  match argv:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      passes_pick(value, String.eq(h, "--"), String.eq(h, "--gate"), String.eq(h, "--plugin"), h, t,
        passes(t, Bool.and(Bool.not(value), String.eq(h, "--plugin"))))

def complete_pick(value: Bool, dashes: Bool, empty: Bool, next: Bool) -> Bool:
  match value dashes:
    case True{} _:
      Bool.and(Bool.not(empty), next)
    case False{} True{}:
      True{}
    case False{} False{}:
      next

# Whether every --plugin has a value.
def complete(argv: List<&2, String>, +value: Bool) -> Bool:
  match argv:
    case Nil{}:
      Bool.not(value)
    case Con{+h, t}:
      complete_pick(value, String.eq(h, "--"), String.is_empty(h),
        complete(t, Bool.and(Bool.not(value), String.eq(h, "--plugin"))))

# None when a --plugin has no name or path after it.
def split_args(+argv: List<&2, String>) -> Maybe<&2, Args>:
  extra rest = extras(argv, False{}) passes(argv, False{})
  Bool.pick(Maybe<&2, Args>, complete(argv, False{}), Some{Args{extra, rest}}, None{})

# The arguments that put wizardry's colors on, unless the user asked for a theme of their own.
def theme_args(rest: List<&2, String>, themes: String, pair: String) -> List<&2, String>:
  List.append(&2, String, ["--theme", themes], C.unless(C.has(rest, "--use-theme"), ["--use-theme", pair]))

# What switches off everything Pi would add to the agent by itself.
def pi_bare() -> List<&2, String>:
  ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files"]

# What keeps Pi from reading what lies around it: themes it would discover, MCP servers, and the
# settings and add-ons of whatever project it is started in.
def pi_apart() -> List<&2, String>:
  ["--no-themes", "--no-mcp", "--no-approve"]

# The arguments Pi starts with. Pi contributes the loop, the models and the terminal; everything
# it would add to the agent by itself stays out, and so does whatever a project or another setup
# holds for it. A session directory and a theme the user chose win.
def pi_args(+rest: List<&2, String>, sessions: String, themes: String, pair: String) -> List<&2, String>:
  List.concat(&2, String, [
    pi_bare(),
    pi_apart(),
    C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]),
    theme_args(rest, themes, pair),
    rest])

# The command line, said
# ----------------------

def help() -> String:
  String.join([
    "wizardry - Pi on Cordis. Every plugin is a tool call; the agent chooses which to make.",
    "",
    "Usage:",
    "  wizardry [options] [messages...]     Start a session (interactive unless -p)",
    "  wizardry plugins                     List loaded plugins and the actions they provide",
    "  wizardry update [on|off]             Update now, or turn automatic updates on or off",
    "  wizardry auth <command>              Log in or out (wizardry keeps its own logins, apart from Pi's)",
    "  wizardry export [folder]             Copy every conversation and memory to a folder you keep",
    "  wizardry delete <what> [--yes]       Delete conversations, memories, old (Pi's own setup) or all",
    "",
    "Options:",
    "  --plugin <name|path>   Load a plugin for this run (repeatable)",
    "  --gate                 Load the \"gate\" plugin: ask before bash, write, edit and plugin changes",
    "  --version, -v          Show the version",
    "  --help, -h             Show this help",
    "",
    "Every other option goes to Pi unchanged: --model, --thinking, -p/--print, -c/--continue,",
    "-r/--resume, --mode json|rpc, --no-session, and so on (see `pi --help`).",
    "",
    "Plugins load from ~/.wizardry/plugins/, ./.wizardry/plugins/, and ~/.wizardry/plugins.json.",
    "wizardry updates itself in the background whenever it can; /update off in a session stops that.",
    "Nothing asks for approval unless you pass --gate.",
    "",
    "wizardry is kept apart: its logins, settings, conversations and memories are all in ~/.wizardry,",
    "and nothing of Pi's own setup (~/.pi) or of a project's .pi folder is read. `wizardry delete`",
    "says what it would remove and removes nothing until you add --yes; it exports first.",
    ""], "\n")

def pi_only_text(+first: String, argv: List<&2, String>) -> String:
  String.concat(["\"", first, "\" is a Pi command and wizardry does not use Pi's extensions or packages. Run `pi ",
    String.join(argv, " "), "` instead.\n"])

# Whether the arguments ask for the list of plugins.
def lists_plugins(rest: List<&2, String>) -> Bool:
  match rest:
    case Nil{}:
      False{}
    case Con{h, t}:
      String.eq(h, "plugins")

def listing_actions(actions: List<&2, String>) -> String:
  match actions:
    case Nil{}:
      ""
    case Con{h, t}:
      String.concat(["  ", String.join(h <> t, ", "), "\n"])

# A plugin as `wizardry plugins` lists it.
def listing(name: String, state: String, source: String, actions: List<&2, String>) -> String:
  String.concat([name, " [", state, "] ", source, "\n", listing_actions(actions)])

def switch_said(on: Bool) -> String:
  String.concat(["Automatic updates are ", Bool.pick(String, on, "on", "off"), "."])

def at_file(file: String) -> String:
  SCon{'@', file}

def at_files(files: List<&2, String>) -> List<&2, String>:
  match files:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      at_file(h) <> at_files(t)

# What was already said to a session that restarts: its messages, and its files as `@file`.
def said_of(messages: List<&2, String>, files: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, messages, at_files(files))
