# wizardry's decisions, in Bend.
#
# Everything here is pure: lists and strings in, lists and strings out. The host (src/*.ts) asks
# these defs what to do and then does it with Pi, Cordis and the file system, which Bend cannot
# reach. `npm run core` compiles this file to core/core.mjs; src/core.ts is the only importer.
#
# LAWS.bend states what must hold of these defs and PROOF.bend proves it: `bend PROOF.bend`.

import Base

# Names in lists
# --------------

# Whether `x` is one of `xs`.
def has(xs: List<&2, String>, +x: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, x), has(t, x))

def keep_if(keep: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case False{}:
      rest
    case True{}:
      h <> rest

# `xs` without the names in `bad`.
def without(xs: List<&2, String>, +bad: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      keep_if(Bool.not(has(bad, h)), h, without(t, bad))

# The names of `xs` that are also in `good`.
def only(xs: List<&2, String>, +good: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      keep_if(has(good, h), h, only(t, good))

# Whether any of `xs` is in `bad`.
def overlaps(xs: List<&2, String>, +bad: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(has(bad, h), overlaps(t, bad))

# `xs` with `x` at the end, unless it is there already.
def add(+xs: List<&2, String>, +x: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, has(xs, x), xs, List.append(&2, String, xs, [x]))

def add_all(ys: List<&2, String>, +xs: List<&2, String>) -> List<&2, String>:
  match ys:
    case Nil{}:
      xs
    case Con{+h, t}:
      add_all(t, add(xs, h))

# Whether every one of `need` is in `xs`.
def covers(+xs: List<&2, String>, need: List<&2, String>) -> Bool:
  match need:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(has(xs, h), covers(xs, t))

# Which plugins load at boot
# --------------------------

# A plugin file found in a directory: the name it goes by, and where it is.
type Entry is Data:
  Entry{name: String, path: String}

def names(es: List<&2, Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Entry{name, path}, t}:
      name <> names(t)

def keep_entry(keep: Bool, e: Entry, rest: List<&2, Entry>) -> List<&2, Entry>:
  match keep:
    case False{}:
      rest
    case True{}:
      e <> rest

# `es` without the entries named in `bad`.
def without_named(es: List<&2, Entry>, +bad: List<&2, String>) -> List<&2, Entry>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Entry{+name, path}, t}:
      keep_entry(Bool.not(has(bad, name)), Entry{name, path}, without_named(t, bad))

# A shipped default steps aside for a file of the same name in a plugin directory.
def shipped_kept(shipped: List<&2, Entry>, found: List<&2, Entry>) -> List<&2, Entry>:
  without_named(shipped, names(found))

# What boot loads from the plugin folders, in order: the shipped defaults nobody replaced, then
# what the plugin directories hold, less everything the user switched off.
def plan(shipped: List<&2, Entry>, +found: List<&2, Entry>, +disabled: List<&2, String>) -> List<&2, Entry>:
  without_named(List.append(&2, Entry, shipped_kept(shipped, found), found), disabled)

# The builtin plugins boot starts: the defaults, less the ones the user switched off.
def builtins_at_boot(defaults: List<&2, String>, +disabled: List<&2, String>) -> List<&2, String>:
  without(defaults, disabled)

# The names that are switched off once `name` is unloaded for good.
def switched_off(+disabled: List<&2, String>, +name: String) -> List<&2, String>:
  add(disabled, name)

# The names that are switched off once `name` is loaded for good.
def switched_on(disabled: List<&2, String>, name: String) -> List<&2, String>:
  without(disabled, [name])

# Whether a plugin loaded for good is written down to load at every start. A builtin default
# starts anyway unless it is switched off, so only its being switched on is recorded.
def remembered(builtin: Bool, default: Bool) -> Bool:
  Bool.not(Bool.and(builtin, default))

# What a session runs on. Unloading either would take the agent's own runtime away mid-call.
def core_plugins() -> List<&2, String>:
  ["pi", "cordis"]

def is_core(name: String) -> Bool:
  has(core_plugins(), name)

# What a process taking over from another unloads to match it: what it has loaded that the other
# had not, except what it runs on.
def restore_unloads(loaded: List<&2, String>, +wanted: List<&2, String>) -> List<&2, String>:
  without(without(loaded, wanted), core_plugins())

def ends_with_any(+s: String, exts: List<&2, String>) -> Bool:
  match exts:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.ends_with(s, h), ends_with_any(s, t))

def hidden_char(c: Char) -> Bool:
  +c = c
  Bool.or(Char.is_eq(c, '.'), Char.is_eq(c, '_'))

# Files whose names start with `.` or `_` are never plugins.
def hidden(name: String) -> Bool:
  match name:
    case SNil{}:
      True{}
    case SCon{h, t}:
      hidden_char(h)

# Whether a directory entry is a plugin: a module file, or a folder with an entry file.
def usable(+name: String, folder: Bool, entry: Bool) -> Bool:
  Bool.and(Bool.not(hidden(name)), Bool.pick(Bool, folder, entry, ends_with_any(name, [".ts", ".mts", ".js", ".mjs"])))

def stem_pick(dot: Bool, cut: String, more: String) -> String:
  match dot:
    case False{}:
      more
    case True{}:
      cut

# `rev` is the name backwards: the extension ends at the first dot met.
def stem_go(+whole: String, rev: String) -> String:
  match rev:
    case SNil{}:
      whole
    case SCon{h, +t}:
      stem_pick(Char.is_eq(h, '.'), Bool.pick(String, String.is_empty(t), whole, String.reverse(t)), stem_go(whole, t))

# A file name without its extension: "bend.js" is "bend". A leading dot is not an extension.
def stem(+name: String) -> String:
  stem_go(name, String.reverse(name))

# The name a plugin goes by: the first candidate that is a real name.
def pick_name(candidates: List<&2, String>) -> String:
  match candidates:
    case Nil{}:
      ""
    case Con{+h, t}:
      Bool.pick(String, has(["", "apply", "default"], h), pick_name(t), h)

# The command line
# ----------------

# What the first argument asks for.
type Command is Data:
  Help{}
  Version{}
  PiOnly{}
  Auth{}
  Update{}
  Run{}

def command_pick(help: Bool, version: Bool, pi: Bool, auth: Bool, update: Bool) -> Command:
  match help version pi auth update:
    case True{} _ _ _ _:
      Help{}
    case False{} True{} _ _ _:
      Version{}
    case False{} False{} True{} _ _:
      PiOnly{}
    case False{} False{} False{} True{} _:
      Auth{}
    case False{} False{} False{} False{} True{}:
      Update{}
    case False{} False{} False{} False{} False{}:
      Run{}

def command_of(+first: String) -> Command:
  command_pick(has(["--help", "-h"], first), has(["--version", "-v"], first),
    has(["install", "remove", "uninstall", "list", "config", "mcp"], first),
    String.eq(first, "auth"), String.eq(first, "update"))

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

def unless(skip: Bool, xs: List<&2, String>) -> List<&2, String>:
  match skip:
    case False{}:
      xs
    case True{}:
      Nil{}

# The arguments that put wizardry's colors on, unless the user asked for a theme of their own.
def theme_args(rest: List<&2, String>, themes: String, pair: String) -> List<&2, String>:
  List.append(&2, String, ["--theme", themes], unless(has(rest, "--use-theme"), ["--use-theme", pair]))

# The arguments Pi starts with. Pi contributes the loop, the models and the terminal; everything
# it would add to the agent by itself stays out. A session directory and a theme the user chose win.
def pi_args(+rest: List<&2, String>, sessions: String, themes: String, pair: String) -> List<&2, String>:
  List.concat(&2, String, [
    ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files"],
    unless(Bool.or(has(rest, "--session-dir"), has(rest, "--no-session")), ["--session-dir", sessions]),
    theme_args(rest, themes, pair),
    rest])

# Restarting onto new code
# ------------------------

def remove_one(xs: List<&2, String>, +x: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Bool.pick(List<&2, String>, String.eq(h, x), t, h <> remove_one(t, x))

# The arguments, read from the end, less the messages already sent (`said`) and any `--`.
def unsaid(rev: List<&2, String>, +said: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match rev:
    case Nil{}:
      acc
    case Con{+h, t}:
      unsaid(t,
        Bool.pick(List<&2, String>, has(said, h), remove_one(said, h), said),
        Bool.pick(List<&2, String>, Bool.or(has(said, h), String.eq(h, "--")), acc, h <> acc))

def resumes(+arg: String) -> Bool:
  has(["-c", "--continue", "-r", "--resume"], arg)

def chooses(+arg: String) -> Bool:
  has(["--session", "--fork", "--session-id"], arg)

# The arguments without a choice of session: -c and -r go, --session and its value go.
# `skip` is set while reading the value of --session, --fork or --session-id.
def strip(xs: List<&2, String>, +skip: Bool) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      keep_if(Bool.not(Bool.or(skip, Bool.or(resumes(h), chooses(h)))), h,
        strip(t, Bool.and(Bool.not(skip), chooses(h))))

# Whether any argument continues or resumes a session.
def any_resumes(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(resumes(h), any_resumes(t))

# Whether any argument names a session to open.
def any_chooses(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(chooses(h), any_chooses(t))

def session_args(session: Maybe<&2, String>) -> List<&2, String>:
  match session:
    case None{}:
      Nil{}
    case Some{file}:
      ["--session", file]

# The Pi arguments for a process taking over from this one: the same options, without the opening
# messages (they were sent once already) or a choice of session, and with `session` to open instead.
def restart_args(rest: List<&2, String>, said: List<&2, String>, session: Maybe<&2, String>) -> List<&2, String>:
  List.append(&2, String, strip(unsaid(List.reverse(&2, String, rest), said, Nil{}), False{}), session_args(session))

# What the user sees
# ------------------

# The logo: a wizard's cap. Plain ASCII, every row the same width.
def hat() -> List<&2, String>:
  [ "         /\\         ",
    "        /  \\        ",
    "       / *  \\       ",
    "      /    . \\      ",
    "     /  *     \\     ",
    " ___/__________\\___ ",
    "(__________________)"]

# A spark on or around the cap: where it sits, and what it shows on each of the eight frames.
type Spark is Data:
  Spark{row: Nat, col: Nat, frames: String}

# The first frame of every spark is what the plain cap has there.
def sparks() -> List<&2, Spark>:
  [ Spark{2n, 9n, "*+*.  .*"},
    Spark{3n, 11n, ". .*+*. "},
    Spark{4n, 8n, "*.  .*+*"},
    Spark{0n, 13n, "  .*.   "},
    Spark{1n, 5n, "     .*."},
    Spark{2n, 16n, " .+.    "}]

# `s` with `c` in place of its character at `col`. A text that short is left as it is.
def put(s: String, col: Nat, c: Char) -> String:
  match s col:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SCon{c, t}
    case SCon{h, t} 1n+p:
      SCon{h, put(t, p, c)}

def put_row(rows: List<&2, String>, row: Nat, col: Nat, c: Char) -> List<&2, String>:
  match rows row:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      put(h, col, c) <> t
    case Con{h, t} 1n+p:
      h <> put_row(t, p, col, c)

def glyph(found: Maybe<&2, Char>) -> Char:
  match found:
    case None{}:
      ' '
    case Some{c}:
      c

# `rows` with every spark showing what it shows on frame `at`.
def twinkle(sparks: List<&2, Spark>, rows: List<&2, String>, +at: Nat) -> List<&2, String>:
  match sparks:
    case Nil{}:
      rows
    case Con{Spark{row, col, frames}, t}:
      twinkle(t, put_row(rows, row, col, glyph(String.get(frames, at))), at)

# The cap's rows on one frame of its twinkle; the frames come round every eight.
def hat_frame(frame: Nat) -> List<&2, String>:
  twinkle(sparks(), hat(), Nat.mod(frame, 8n))

# The small cap that stands where Pi's spinner did while the agent works: a spark drifting off
# its tip, one frame per row.
def small_hat() -> List<&2, String>:
  [ "_/\\_   ",
    "_/\\_.  ",
    "_/\\_*  ",
    "_/\\_ + ",
    "_/\\_ * ",
    "_/\\_  ."]

# How wide each row is.
def widths(rows: List<&2, String>) -> List<&2, Nat>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.length(h) <> widths(t)

# The theme colors the caps are drawn in: blues and greys, in both themes.
def inks() -> List<&2, String>:
  ["accent", "mdLink", "dim", "text"]

def ink_pick(plus: Bool, star: Bool, dot: Bool) -> String:
  match plus star dot:
    case True{} _ _:
      "text"
    case False{} True{} _:
      "mdLink"
    case False{} False{} True{}:
      "dim"
    case False{} False{} False{}:
      "accent"

def ink_of(+c: Char) -> String:
  ink_pick(Char.is_eq(c, '+'), Char.is_eq(c, '*'), Char.is_eq(c, '.'))

# The theme color a piece of a cap is drawn in, by its first character: the cap in the accent
# blue, a spark pale blue at its brightest and grey as it fades.
def ink(part: String) -> String:
  match part:
    case SNil{}:
      "accent"
    case SCon{h, t}:
      ink_of(h)

def is_sep(+c: Char, loose: Bool) -> Bool:
  Bool.or(Char.is_space(c), Bool.and(loose, Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '-'))))

def squash_put(sep: Bool, pending: Bool, c: Char, acc: String) -> String:
  match sep pending:
    case True{} _:
      acc
    case False{} True{}:
      SCon{c, SCon{' ', acc}}
    case False{} False{}:
      SCon{c, acc}

# Runs of separators become one space, and none is left at either end. `started` is set once a
# character was kept, `pending` while a space is owed to the next one. `acc` is the answer so far,
# backwards: every text loop here is a tail call, so a long text costs no stack.
def squash_go(s: String, +loose: Bool, +started: Bool, pending: Bool, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, t}:
      squash_go(t, loose, Bool.or(started, Bool.not(is_sep(c, loose))), Bool.and(started, is_sep(c, loose)),
        squash_put(is_sep(c, loose), pending, c, acc))

def squash(s: String, loose: Bool) -> String:
  squash_go(s, loose, False{}, False{}, SNil{})

# A name as words: "plugin_load" is "plugin load".
def words(text: String) -> String:
  squash(text, True{})

# Whether a title already starts with the plugin's name.
def mine(+title: String, +owner: String) -> Bool:
  Bool.or(String.eq(title, owner), String.starts_with(title, String.append(owner, " ")))

def title_pick(titled: Bool, native: Bool, mine: Bool, title: String, name: String, +said: String, owner: String) -> String:
  match titled native mine:
    case True{} _ _:
      title
    case False{} True{} _:
      name
    case False{} False{} True{}:
      said
    case False{} False{} False{}:
      String.append(owner, SCon{' ', said})

# What the user sees a call named as: the plugin, then what it did. `plugin_load` from `cordis`
# reads "cordis plugin load". Pi's own tools keep their names, and an action's title overrides all.
def action_title(+title: String, native: Bool, +name: String, +owner: String) -> String:
  title_pick(Bool.not(String.is_empty(title)), native, mine(words(name), words(owner)), title, name, words(name), words(owner))

# Whether `s` has at most `n` characters.
def fits(s: String, n: Nat) -> Bool:
  match s n:
    case SNil{} _:
      True{}
    case SCon{h, t} 0n:
      False{}
    case SCon{h, t} 1n+p:
      fits(t, p)

def clip_at(+s: String, n: Nat) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      String.append(String.take(s, p), "…")

# `s` cut to `n` characters, the last one an ellipsis when something was cut.
def clip(+s: String, +n: Nat) -> String:
  Bool.pick(String, fits(s, n), s, clip_at(s, n))

# One argument value on the title line: on one line, and cut short.
def brief(text: String) -> String:
  +line = squash(text, False{})
  Bool.pick(String, String.is_empty(line), "\"\"", clip(line, 72n))

def expand_put(cr: Bool, tab: Bool, nl: Bool, c: Char, pad: String, acc: String) -> String:
  match cr tab nl:
    case True{} _ _:
      acc
    case False{} True{} _:
      SCon{' ', SCon{' ', SCon{' ', acc}}}
    case False{} False{} True{}:
      String.append(String.reverse(pad), SCon{'\n', acc})
    case False{} False{} False{}:
      SCon{c, acc}

def expand_go(s: String, +pad: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, t}:
      expand_go(t, pad, expand_put(Char.is_eq(c, '\r'), Char.is_eq(c, '\t'), Char.is_eq(c, '\n'), c, pad, acc))

# Text as the terminal shows it: no carriage returns, tabs as three spaces, `pad` after each newline.
def expand(s: String, pad: String) -> String:
  expand_go(s, pad, SNil{})

def line_cur(nl: Bool, c: Char, cur: String) -> String:
  match nl:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, cur}

def line_done(nl: Bool, cur: String, done: List<&2, String>) -> List<&2, String>:
  match nl:
    case True{}:
      String.reverse(cur) <> done
    case False{}:
      done

# `cur` is the line being read and `done` the lines before it, both backwards.
def lines_go(s: String, +cur: String, done: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      List.reverse(&2, String, String.reverse(cur) <> done)
    case SCon{+c, t}:
      lines_go(t, line_cur(Char.is_eq(c, '\n'), c, cur), line_done(Char.is_eq(c, '\n'), cur, done))

# The lines of a text, however many there are.
def lines(s: String) -> List<&2, String>:
  lines_go(s, SNil{}, Nil{})

# The first `limit` of `xs`.
def first(xs: List<&2, String>, limit: Nat) -> List<&2, String>:
  match xs limit:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Nil{}
    case Con{h, t} 1n+p:
      h <> first(t, p)

# How many `xs` there are, on top of `acc`.
def count(xs: List<&2, String>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      count(t, 1n+acc)

# How many of `xs` are past the first `limit`.
def beyond(xs: List<&2, String>, limit: Nat) -> Nat:
  match xs limit:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      count(t, 1n)
    case Con{h, t} 1n+p:
      beyond(t, p)

# The part of a result the user is shown, and how many lines are one keypress away.
type View is Data:
  View{shown: List<&2, String>, more: Nat}

def view_of(expanded: Bool, +lines: List<&2, String>, +limit: Nat) -> View:
  match expanded:
    case True{}:
      View{lines, 0n}
    case False{}:
      shown more = first(lines, limit) beyond(lines, limit)
      View{shown, more}

# What a call came back with: its lines, the first ten unless expanded.
def result_view(output: String, expanded: Bool) -> View:
  view_of(expanded, lines(String.trim_end(expand(output, ""))), 10n)

# The agent's own tools
# ---------------------

# `focus` cannot be put away: it is the way back.
def droppable(drop: List<&2, String>) -> List<&2, String>:
  without(drop, ["focus"])

# The actions in front of the agent after it drops some and takes some up.
def focus_active(active: List<&2, String>, drop: List<&2, String>, take: List<&2, String>) -> List<&2, String>:
  add_all(take, without(active, droppable(drop)))

# Whether rtk leaves a command alone: asked to, nothing to run, or already an rtk command.
def after_rtk(rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Char.is_space(h)

def rtk_skips(raw: Bool, command: String) -> Bool:
  +line = String.trim_start(command)
  Bool.or(raw, Bool.or(String.is_empty(line), Bool.and(String.starts_with(line, "rtk"), after_rtk(String.drop(line, 3n)))))

# What the updater said
# ---------------------

def last_said(lines: List<&2, String>, +best: String) -> String:
  match lines:
    case Nil{}:
      best
    case Con{+h, t}:
      last_said(t, Bool.pick(String, String.is_empty(h), best, h))

def unprefixed(+line: String) -> String:
  Bool.pick(String, String.starts_with(line, "wizardry: "), String.drop(line, 10n), line)

# The last thing an update run printed, without its "wizardry: " prefix.
def update_line(said: String) -> String:
  unprefixed(last_said(String.lines(said), "wizardry: the update did not say what happened"))

def updated(line: String) -> Bool:
  String.starts_with(line, "updated to")

# What `wizardry update` and `/update` were asked for: nothing after them is "update now".
type Asked is Data:
  Now{}
  On{}
  Off{}
  Unclear{}

def asked_pick(empty: Bool, on: Bool, off: Bool) -> Asked:
  match empty on off:
    case True{} _ _:
      Now{}
    case False{} True{} _:
      On{}
    case False{} False{} True{}:
      Off{}
    case False{} False{} False{}:
      Unclear{}

def update_asked(+word: String) -> Asked:
  asked_pick(String.is_empty(word), String.eq(word, "on"), String.eq(word, "off"))

# What the switch for automatic updates does to the `update` plugin, which is the switch itself.
type Act is Data:
  Loads{}
  Unloads{}
  Stays{}

def switch_act(on: Bool, loaded: Bool) -> Act:
  match on loaded:
    case True{} False{}:
      Loads{}
    case False{} True{}:
      Unloads{}
    case True{} True{}:
      Stays{}
    case False{} False{}:
      Stays{}

# Words about plugins
# -------------------

def listed(actions: List<&2, String>) -> String:
  match actions:
    case Nil{}:
      "(none)"
    case Con{h, t}:
      String.join(h <> t, ", ")

# A plugin in the header: its name, and its state when that is not "active".
def label(+name: String, +state: String) -> String:
  Bool.pick(String, String.eq(state, "active"), name, String.concat([name, " (", state, ")"]))

# A plugin as `cordis_inspect` lists it.
def inspect_line(name: String, state: String, source: String, actions: List<&2, String>) -> String:
  String.concat([name, " [", state, "] ", source, "\n  actions: ", listed(actions)])

# What the agent is told after loading or reloading a plugin.
def loaded_text(+verb: String, +name: String, +state: String, actions: List<&2, String>) -> String:
  Bool.pick(String, String.eq(state, "pending"),
    String.concat([verb, " \"", name, "\" [pending]: it injects a service nothing provides yet, and starts when one does."]),
    String.concat([verb, " \"", name, "\" [", state, "]. Actions: ", listed(actions)]))

# The description the agent is shown: the action's own, then a note from every layer around it.
def described(description: String, notes: List<&2, String>) -> String:
  String.join(description <> without(notes, [""]), "\n\n")

# The standing prompt
# -------------------

# The whole standing prompt. Everything else the agent knows comes from its tool list.
def base_prompt(cwd: String, date: String) -> String:
  String.join([
    "You are wizardry, an agent working in a terminal on the user's machine.",
    "",
    "The user states outcomes. How you reach them is yours to decide.",
    "Everything you can do is a tool call. Tools are actions open to you, not procedures you owe anyone: take the ones that serve the outcome and leave the rest. Each comes from a plugin, and you can inspect, load, write and unload plugins while you work. No action waits for approval.",
    "",
    String.append("Working directory: ", cwd),
    String.append("Date: ", date)], "\n")

# The standing prompt with what the agent wrote for itself with `become`, when it has.
def system_prompt(+base: String, +identity: String) -> String:
  Bool.pick(String, String.is_empty(identity), base, String.concat([base, "\n\nWhat you have chosen to be:\n", identity]))

# Whether `x` is one of `xs`, for the host to ask.
def among(xs: List<&2, String>, x: String) -> Bool:
  has(xs, x)

# Where wizardry keeps its things
# -------------------------------

def first_said(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_empty(a), b, a)

def home_pick(chosen: Bool, +said: String, moved: Bool, home: String, old: String) -> String:
  match chosen moved:
    case True{} _:
      said
    case False{} True{}:
      old
    case False{} False{}:
      home

# wizardry's directory: the one the user named (under the new name, then the old), and otherwise
# ~/.wizardry, unless only the old ~/.izardry is there.
def home_of(+chosen: String, +old_chosen: String, home: String, old: String, has_home: Bool, has_old: Bool) -> String:
  home_pick(Bool.not(String.is_empty(first_said(chosen, old_chosen))), first_said(chosen, old_chosen),
    Bool.and(Bool.not(has_home), has_old), home, old)

# Whether an old ~/.izardry is moved to ~/.wizardry: only when the user named no directory, the
# new one is not there yet, and the old one is a real directory and not the link left behind.
def adopts_home(named: Bool, has_home: Bool, has_old: Bool, old_is_link: Bool) -> Bool:
  Bool.and(Bool.not(named), Bool.and(Bool.not(has_home), Bool.and(has_old, Bool.not(old_is_link))))

# Whether a `wizardry` command is made beside an `izardry` one.
def adopts_command(invoked: String, is_link: Bool, has_command: Bool) -> Bool:
  Bool.and(String.eq(invoked, "izardry"), Bool.and(is_link, Bool.not(has_command)))

def moved_list(home: Bool, command: Bool) -> List<&2, String>:
  List.append(&2, String,
    unless(Bool.not(home), ["your plugins and sessions are now in ~/.wizardry"]),
    unless(Bool.not(command), ["the command is now `wizardry`"]))

def adopted_say(moved: List<&2, String>) -> Maybe<&2, String>:
  match moved:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{String.concat(["izardry is now wizardry: ", String.join(h <> t, ", and "), "."])}

# What the user is told after an install under the old name was carried over, if anything moved.
def adopted(home: Bool, command: Bool) -> Maybe<&2, String>:
  adopted_say(moved_list(home, command))

# The two plugin directories, once when they are the same one.
def plugin_dirs(+home: String, cwd: String) -> List<&2, String>:
  add([home], cwd)

# What `~/x` names under the home directory, if the source starts that way.
def under_home(+source: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(source, "~/"), Some{String.drop(source, 2n)}, None{})

# Whether a source names a builtin: said outright, or a builtin's name with no file of that name.
def is_builtin_source(prefixed: Bool, builtin: Bool, exists: Bool) -> Bool:
  Bool.and(builtin, Bool.or(prefixed, Bool.not(exists)))

def nth(xs: List<&2, String>, n: Nat, +otherwise: String) -> String:
  match xs n:
    case Nil{} _:
      otherwise
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      nth(t, p, otherwise)

# A plugin's state, as Cordis numbers it.
def state_name(n: Nat) -> String:
  nth(["pending", "loading", "active", "failed", "disposed", "unloading"], n, "unknown")

# What is said when something cannot be done
# ------------------------------------------

def already_loaded(name: String) -> String:
  String.concat(["plugin \"", name, "\" is already loaded; reload or unload it first"])

def not_loaded(name: String) -> String:
  String.concat(["no plugin named \"", name, "\" is loaded"])

def runs_on_it(name: String, verb: String) -> String:
  String.concat(["\"", name, "\" is what this session runs on and cannot be ", verb, " from inside it"])

def no_builtin(name: String, builtins: List<&2, String>) -> String:
  String.concat(["no builtin plugin named \"", name, "\"; builtins: ", String.join(builtins, ", ")])

def no_plugin_at(path: String) -> String:
  String.append("no plugin at ", path)

def no_entry(path: String) -> String:
  String.append(path, " has no index.ts, index.js or package.json \"main\"")

def load_failed(source: String, why: String) -> String:
  String.concat([source, ": ", why])

def needs_execute(name: String) -> String:
  String.concat(["action \"", name, "\" needs an execute function"])

def already_registered(name: String, owner: String) -> String:
  String.concat(["action \"", name, "\" is already registered by plugin \"", owner, "\""])

def no_action(name: String) -> String:
  String.concat(["no action named \"", name, "\""])

def action_gone(name: String) -> String:
  String.concat(["action \"", name, "\" is gone: its plugin was unloaded"])

def command_gone(name: String) -> String:
  String.concat(["/", name, " is gone: its plugin was unloaded"])

def no_such_actions(names: List<&2, String>) -> String:
  String.append("no such action: ", String.join(names, ", "))

def unloaded_text(name: String) -> String:
  String.concat(["Unloaded \"", name, "\"."])

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
    "  wizardry auth <command>              Pi's credential commands (wizardry shares Pi's logins)",
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

# The session
# -----------

# Whether a session starts again on new code now. Only an interactive one does, and only while
# the agent is idle: a restart never interrupts work.
def restarts_now(wanted: Bool, attached: Bool, tui: Bool, idle: Bool) -> Bool:
  Bool.and(wanted, Bool.and(attached, Bool.and(tui, idle)))

# Whether a tool declared again stays put away: the agent had dropped it with `focus`.
def stays_away(bound: Bool, known: Bool, active: Bool) -> Bool:
  Bool.and(bound, Bool.and(known, Bool.not(active)))

# The standing instructions a session carries: the last ones the agent wrote on this branch.
def last_of(xs: List<&2, String>, last: String) -> String:
  match xs:
    case Nil{}:
      last
    case Con{h, t}:
      last_of(t, h)

# An empty one counts: writing nothing is how the agent clears them.
def last_identity(written: List<&2, String>) -> String:
  last_of(written, "")

# What `become` keeps of what it was given.
def tidy(identity: String) -> String:
  String.trim(identity)

def become_said(identity: String) -> String:
  Bool.pick(String, String.is_empty(identity), "Cleared.", "Set. It applies from the next turn.")

def keep_starting(+word: String, +prefix: String, rest: List<&2, String>) -> List<&2, String>:
  keep_if(String.starts_with(word, prefix), word, rest)

def completions_go(words: List<&2, String>, +prefix: String) -> List<&2, String>:
  match words:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      keep_starting(h, prefix, completions_go(t, prefix))

# The words offered after a slash command: those that start with what was typed.
def completions(words: List<&2, String>, typed: String) -> List<&2, String>:
  completions_go(words, String.trim(typed))

# The day of an ISO time.
def day(iso: String) -> String:
  String.take(iso, 10n)

def focus_said(active: List<&2, String>, away: List<&2, String>) -> String:
  String.concat(["In front of you: ", String.join(active, ", "), "\nPut away: ", listed(away)])

# The thinking levels the agent may set.
def think_levels() -> List<&2, String>:
  ["off", "minimal", "low", "medium", "high", "xhigh", "max"]

def think_describe() -> String:
  String.concat(["Set how much reasoning you spend per step from here on: ", String.join(think_levels(), ", "), "."])

def think_said(level: String) -> String:
  String.append("Thinking level: ", level)

# What the updater leads to
# -------------------------

# Whether a checkout is the installer's own or one someone works in.
def kind_of(managed: Bool) -> String:
  Bool.pick(String, managed, "install", "clone")

# What a session says once it is back on new code.
def carried_on(what: Maybe<&2, String>) -> String:
  String.concat(["wizardry ", Maybe.default(&2, String, what, "updated"), "; this session carried on"])

def update_said(line: String) -> String:
  String.append("wizardry: ", line)

def not_a_checkout(app: String) -> String:
  String.append(app, " is not a git checkout, so there is nothing to update from.")

# rtk and gate
# ------------

def rtk_pick(ok: Bool, +out: String, +command: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.and(ok, Bool.and(Bool.not(String.is_empty(out)), Bool.not(String.eq(out, command)))),
    Some{out}, None{})

# The command rtk would run in place of `command`, if it has one: `rtk rewrite` ended with 0 or 3
# and printed something other than the command itself.
def rtk_takes(+code: Nat, out: String, command: String) -> Maybe<&2, String>:
  rtk_pick(Bool.or(Nat.is_eq(code, 0n), Nat.is_eq(code, 3n)), String.trim(out), command)

def in_dir(+dir: String, +file: String) -> String:
  Bool.pick(String, String.ends_with(dir, "/"), String.append(dir, file), String.concat([dir, "/", file]))

def in_dirs(dirs: List<&2, String>) -> List<&2, String>:
  match dirs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      keep_if(Bool.not(String.is_empty(h)), in_dir(h, "rtk"), in_dirs(t))

# Where rtk is looked for: where the user said, or else on PATH and then where it usually installs.
def rtk_places(configured: Maybe<&2, String>, dirs: List<&2, String>, +home: String) -> List<&2, String>:
  match configured:
    case Some{file}:
      [file]
    case None{}:
      List.append(&2, String, in_dirs(dirs),
        ["/opt/homebrew/bin/rtk", "/usr/local/bin/rtk", in_dir(home, ".cargo/bin/rtk"), in_dir(home, ".local/bin/rtk")])

def rtk_missing(configured: Maybe<&2, String>) -> String:
  match configured:
    case Some{file}:
      String.concat(["no rtk executable at ", file, "; bash output stays unfiltered"])
    case None{}:
      "rtk is not installed (brew install rtk, or see https://github.com/rtk-ai/rtk); bash output stays unfiltered"

# The actions gate asks about unless told otherwise.
def gated() -> List<&2, String>:
  ["bash", "write", "edit", "plugin_load", "plugin_unload", "plugin_reload"]

def gate_summary(params: String) -> String:
  String.take(params, 1500n)

def gate_asks(title: String) -> String:
  String.concat(["Allow ", title, "?"])

def gate_no_one(name: String) -> String:
  String.concat(["\"", name, "\" needs the user's approval and there is no one to ask in this mode"])

def gate_declined(name: String) -> String:
  String.concat(["the user declined \"", name, "\""])

# The header
# ----------

# A line of `count` items, when there is one, before the lines after it.
def emit(count: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match count:
    case 0n:
      rest
    case 1n+p:
      Con{1n+p, rest}

# `count` items make the line being filled, `used` columns wide. The next item joins it when
# there is one and the item fits after a separator; otherwise the line ends and the item starts
# the next.
def pack_go(widths: List<&2, Nat>, +count: Nat, +used: Nat, +sep: Nat, +width: Nat) -> List<&2, Nat>:
  match widths:
    case Nil{}:
      emit(count, Nil{})
    case Con{+w, t}:
      +fits = Bool.and(Nat.is_gt(count, 0n), Nat.is_le(Nat.add(used, Nat.add(sep, w)), width))
      emit(Bool.pick(Nat, fits, 0n, count),
        pack_go(t, Bool.pick(Nat, fits, 1n+count, 1n), Bool.pick(Nat, fits, Nat.add(used, Nat.add(sep, w)), w), sep, width))

# Items of these widths on as few lines as `width` allows, none broken in two: how many go on
# each line, in order.
def pack(widths: List<&2, Nat>, sep: Nat, width: Nat) -> List<&2, Nat>:
  pack_go(widths, 0n, 0n, sep, width)

# Where the header's text goes: beside the cap when at least 36 columns are left there, and
# under it otherwise. `room` is how wide the text may be.
type Layout is Data:
  Beside{room: Nat}
  Under{room: Nat}

def layout_pick(beside: Bool, room: Nat, under: Nat) -> Layout:
  match beside:
    case True{}:
      Beside{room}
    case False{}:
      Under{under}

# One column of margin, the cap, three of gap, then the text.
def layout(+width: Nat, hat_width: Nat) -> Layout:
  +room = Nat.sub(width, Nat.add(4n, hat_width))
  layout_pick(Nat.is_ge(room, 36n), room, Nat.max(1n, Nat.sub(width, 1n)))

# `xs`, made `n` long with `fill` at the end; a longer list is left as it is.
def pad_end(n: Nat, xs: List<&2, String>, +fill: String) -> List<&2, String>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      fill <> pad_end(p, Nil{}, fill)
    case 1n+p Con{h, t}:
      h <> pad_end(p, t, fill)

def blanks(n: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      "" <> blanks(p)

def beside_row(+left: String, +line: String) -> String:
  Bool.pick(String, String.is_empty(line), left, String.concat([left, "   ", line]))

def beside_zip(lefts: List<&2, String>, lines: List<&2, String>) -> List<&2, String>:
  match lefts lines:
    case Nil{} _:
      Nil{}
    case Con{h, t} Nil{}:
      h <> beside_zip(t, Nil{})
    case Con{h, t} Con{l, lt}:
      beside_row(h, l) <> beside_zip(t, lt)

def margined(rows: List<&2, String>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      SCon{' ', h} <> margined(t)

# The header with its text beside the cap: the text sits against the brim, and when there is more
# of it than cap it starts at the tip and runs on below.
def header_beside(+hat: List<&2, String>, +lines: List<&2, String>, hat_width: Nat) -> List<&2, String>:
  +tall = Nat.max(List.length(&2, String, hat), List.length(&2, String, lines))
  margined(beside_zip(pad_end(tall, hat, String.repeat(" ", hat_width)),
    pad_end(tall, List.append(&2, String, blanks(Nat.sub(List.length(&2, String, hat), List.length(&2, String, lines))), lines), "")))

# The header with its text under the cap.
def header_under(hat: List<&2, String>, lines: List<&2, String>) -> List<&2, String>:
  margined(List.append(&2, String, hat, "" <> lines))

# The cap moves only while redrawing it is cheap: on a screen of its own, or while nothing has
# scrolled away above it.
def cap_moves(viewport: Bool, at_top: Bool) -> Bool:
  Bool.or(viewport, at_top)

def next_frame(frame: Nat) -> Nat:
  Nat.mod(1n+frame, 8n)

def blank_lines(shown: List<&2, String>) -> Bool:
  match shown:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.and(String.is_empty(h), List.is_empty(&2, String, t))

# Whether a result has nothing to show: one empty line and none hidden.
def blank_view(shown: List<&2, String>, more: Nat) -> Bool:
  Bool.and(blank_lines(shown), Nat.is_eq(more, 0n))

def more_hint(more: Nat) -> String:
  String.concat(["... (", Nat.show(more), " more lines,"])

# A plugin that is loaded: what the header and the listings say of it.
type Loaded is Data:
  Loaded{name: String, state: String, source: String}

def labels(plugins: List<&2, Loaded>) -> List<&2, String>:
  match plugins:
    case Nil{}:
      Nil{}
    case Con{Loaded{name, state, source}, t}:
      label(name, state) <> labels(t)

def widest(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(String.length(h), widest(t))

def pad_right(+s: String, n: Nat) -> String:
  String.append(s, String.repeat(" ", Nat.sub(n, String.length(s))))

def wide_rows(plugins: List<&2, Loaded>, +wide: Nat) -> List<&2, String>:
  match plugins:
    case Nil{}:
      Nil{}
    case Con{Loaded{name, state, source}, t}:
      String.concat(["  ", pad_right(label(name, state), wide), "  ", source]) <> wide_rows(t, wide)

# The plugins, one to a row with where each comes from, the names in a column.
def plugin_rows(+plugins: List<&2, Loaded>) -> List<&2, String>:
  wide_rows(plugins, widest(labels(plugins)))

# The plugins on one line, to be wrapped to the width.
def plugin_line(plugins: List<&2, Loaded>) -> String:
  String.join(labels(plugins), ", ")

def indented(rows: List<&2, String>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.append("  ", h) <> indented(t)

# What the agent is told about its runtime
# ----------------------------------------

# How a plugin is written: the short manual `cordis_inspect` ends with.
def shape() -> String:
  String.join([
    "A plugin is a .ts or .js file. The smallest one needs no imports:",
    "  export const name = \"weather\"",
    "  export const actions = [{",
    "    name: \"weather\", description: \"Current weather for a city.\",",
    "    parameters: { type: \"object\", properties: { city: { type: \"string\" } }, required: [\"city\"] },",
    "    async execute({ city }, env) { return \"text for the agent\" },   // env: { cwd, signal, update(text), pi (ExtensionContext) }",
    "  }]",
    "For lifecycle or services, export `apply(ctx, config)` (or a default function/class) and use the Cordis context:",
    "ctx.actions.register(action), ctx.on(event, listener), ctx.provide(name, value), `export const inject = [...]`.",
    "ctx.effect(setup) runs setup IMMEDIATELY and keeps its return value as the cleanup on unload; passing the cleanup itself undoes the setup at once.",
    "Events: action/registered, action/changed, action/unregistered, action/before (return a string to refuse the call), action/after, task/end,",
    "pi/ready (Pi's ExtensionAPI is live), pi/session-start (api, piCtx; per-session choices go here: api.setModel, api.setThinkingLevel).",
    "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.",
    "Everything a plugin registers is removed when it is unloaded.",
    "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.",
    "Before editing wizardry itself, call cordis_map: the map of the framework you run on."], "\n")

# What `cordis_inspect` answers: every loaded plugin, the builtins that are not, and the manual.
def inspect_text(lines: List<&2, String>, idle: List<&2, String>) -> String:
  String.join(List.concat(&2, String, [
    ["Loaded plugins:"], lines,
    ["", String.append("Builtin plugins not loaded: ", listed(idle)), "", shape()]]), "\n")

def no_map(app: String) -> String:
  String.concat(["No AGENTS.md in ", app, ". This wizardry predates it; the repo has it: https://github.com/Pomidium/wizardry"])
