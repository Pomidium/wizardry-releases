# wizardry's decisions, in Bend.
#
# Everything here is pure: lists and strings in, lists and strings out. The host (src/*.ts) asks
# these defs what to do and then does it with Pi, Cordis and the file system, which Bend cannot
# reach. Three parts are files of their own, each with its laws and proofs beside it: look/ (how
# calls, results and the header read), args/ (the command line) and keep/ (export and delete).
# `npm run core` compiles each to core/<name>.mjs; src/core.ts is the only importer.
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

def unless(skip: Bool, xs: List<&2, String>) -> List<&2, String>:
  match skip:
    case False{}:
      xs
    case True{}:
      Nil{}

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

# Text
# ----

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
    "The user states outcomes, often loosely, and may never have used a terminal. Act on the likeliest reading and say in a sentence what you took it to mean; ask first only when a wrong guess could not be undone: what stands in the way and can be put back as it was (a lock, a setting) is moved, put back, and said. What only the user knows, leave as a marked blank. What you make for them opens with a double-click (a page, a document) unless they ask for a program. Answer in plain words: what now exists and how to use it.",
    "Everything you can do is a tool call. Tools are actions open to you, not procedures you owe anyone: take the ones that serve the outcome and leave the rest. No action waits for approval.",
    "When nothing you have does what is needed, make it (a script, an install, or a plugin: `cordis_inspect` says how and brings the actions that load one), and remove it afterwards unless it will be needed again. When an approach has failed twice, change the approach, not the wording.",
    "Independent work runs at the same time: calls in one step, parts given to agents of their own. Work that does not split is not split.",
    "Done means checked: run what you made, and say what you could not check. Add nothing the outcome does not need.",
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

# The session
# -----------

# Whether a session starts again on new code now. Only an interactive one does, and only while
# the agent is idle: a restart never interrupts work.
def restarts_now(wanted: Bool, attached: Bool, tui: Bool, idle: Bool) -> Bool:
  Bool.and(wanted, Bool.and(attached, Bool.and(tui, idle)))

# Actions that wait
# -----------------
#
# An action may name another it waits behind (`after`): it is not in front of the agent until
# that one has been called. A skill's first action says what the skill is; the ones that do the
# work, with their long schemas, cost nothing in the sessions that never use the skill.
type Waits is Data:
  Waits{name: String, behind: String}

# Whether an action waiting behind `behind` is still put away: the one it waits behind is there
# to be called, and has not been. One that waits behind nothing, or behind an action nobody
# registered, is in front: nothing may be out of the agent's reach.
def waits(+behind: String, names: List<&2, String>, called: List<&2, String>) -> Bool:
  Bool.and(has(names, behind), Bool.not(has(called, behind)))

# The actions put away, of those registered, given which have been called this session.
def waiting(ws: List<&2, Waits>, +names: List<&2, String>, +called: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{Waits{name, behind}, t}:
      keep_if(waits(behind, names, called), name, waiting(t, names, called))

# Walls
# -----
#
# A call that fails, made again unchanged, fails again. How many times in a row a call has
# failed is counted, and from the second time on the agent is told, with the failure, to change
# the approach. Nothing is said before that, and nothing is refused: a call may be waiting for
# something that will come.
def fails_after(failed: Bool, before: Nat) -> Nat:
  match failed:
    case True{}:
      1n+before
    case False{}:
      0n

def walled(+fails: Nat, +said: String) -> String:
  Bool.pick(String, Nat.is_ge(fails, 2n),
    String.concat([said, "\n\nThis same call has now failed ", Nat.show(fails), " times. Do not make it again unchanged: change the approach (another route, another tool, or make what is missing)."]),
    said)

# What Pi's file tools say of themselves, each thing once: their parameters say the rest.
# A tool not named here keeps Pi's words.
def fs_describe(+name: String, pi: String) -> String:
  Bool.pick(String, String.eq(name, "edit"), "Edit a single file by exact text replacement.",
    Bool.pick(String, String.eq(name, "read"), "Read a file: text, or an image (jpg, png, gif, webp, bmp). Text is cut at 2000 lines or 50KB: continue with offset.", pi))

# Whether a tool is in front of the agent once it has been declared (again). One Pi has not
# seen, or one that comes back after its plugin was unloaded, is in front unless it waits. One
# Pi knows stays as it was: the agent may have put it away with `focus`, or taken it up.
def in_front(bound: Bool, known: Bool, active: Bool, returned: Bool, waits: Bool) -> Bool:
  match bound:
    case False{}:
      True{}
    case True{}:
      Bool.pick(Bool, Bool.or(Bool.not(known), returned), Bool.not(waits), active)

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
    "export (dir, wrote): `wizardry export` asks for a copy of what you keep; write <home>/<name>/ into <dir>/<name>/ and call wrote(one line).",
    "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.",
    "Everything a plugin registers is removed when it is unloaded.",
    "An action with `after: \"other\"` stays out of the agent's tool list until `other` has been called: give a skill one short action that explains it, and put the ones with long schemas after it.",
    "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.",
    "Before editing wizardry itself, call cordis_map: the map of the framework you run on."], "\n")

# What `cordis_inspect` answers: every loaded plugin, the builtins that are not, and the manual.
def inspect_text(lines: List<&2, String>, idle: List<&2, String>) -> String:
  String.join(List.concat(&2, String, [
    ["Loaded plugins:"], lines,
    ["", String.append("Builtin plugins not loaded: ", listed(idle)), "", shape()]]), "\n")

def no_map(app: String) -> String:
  String.concat(["No AGENTS.md in ", app, ". This wizardry predates it; the repo has it: https://github.com/Pomidium/wizardry"])

# Kept apart from Pi's own setup
# ------------------------------

# Where Pi keeps its logins, settings and model lists when wizardry runs it: a folder inside
# wizardry's own directory. ~/.pi is never read, so nothing installed there reaches a session.
def own_pi(home: String) -> String:
  String.append(home, "/pi")

# Where the Pi installed on this machine keeps the same things: where PI_CODING_AGENT_DIR pointed
# when wizardry started, else ~/.pi/agent. To wizardry that is the old setup.
def old_pi(+named: String, userhome: String) -> String:
  Bool.pick(String, String.is_empty(named), String.append(userhome, "/.pi/agent"), named)

# A variable of the environment and what it is set to.
type Var is Data:
  Var{name: String, value: String}

# What Pi finds in the environment when wizardry runs it, whatever was there before: its
# directory is wizardry's, it does not look for a newer Pi (wizardry ships the one it runs), and
# it does not report this install as one of Pi's.
def pi_env(home: String) -> List<&2, Var>:
  [Var{"PI_CODING_AGENT_DIR", own_pi(home)}, Var{"PI_SKIP_VERSION_CHECK", "1"}, Var{"PI_TELEMETRY", "0"}]

# What is taken out of it: where another setup keeps its sessions and its copy of Pi.
def pi_env_cleared() -> List<&2, String>:
  ["PI_CODING_AGENT_SESSION_DIR", "PI_PACKAGE_DIR"]

def var_names(vars: List<&2, Var>) -> List<&2, String>:
  match vars:
    case Nil{}:
      Nil{}
    case Con{Var{name, value}, t}:
      name <> var_names(t)

# Every variable wizardry changes for Pi. A command the agent runs sees each as it was before.
def pi_env_touched() -> List<&2, String>:
  List.append(&2, String, var_names(pi_env("")), pi_env_cleared())

# The files brought over from Pi's own directory, once: the logins and the models added by hand.
def brought_files() -> List<&2, String>:
  ["auth.json", "models.json"]

# The settings brought over with them: which model is talked to and how it is reached.
def brought_settings() -> List<&2, String>:
  ["defaultProvider", "defaultModel", "defaultThinkingLevel", "modelThinkingLevels", "enabledModels",
    "httpProxy", "shellPath", "shellCommandPrefix"]

# What Pi's settings can hold that adds to a session or moves it elsewhere. None of it comes over.
def pi_addons() -> List<&2, String>:
  ["packages", "extensions", "skills", "prompts", "themes", "enableSkillCommands", "sessionDir",
    "defaultProjectTrust", "selfUpdateCommand"]

# Of the settings Pi's own setup holds, the ones that are brought over.
def settings_brought(keys: List<&2, String>) -> List<&2, String>:
  only(keys, brought_settings())

# Whether logins are brought over: only into a directory that is not there yet, from one that
# is, and never from a directory onto itself.
def brings(has_own: Bool, has_old: Bool, old: String, own: String) -> Bool:
  Bool.and(Bool.not(has_own), Bool.and(has_old, Bool.not(String.eq(old, own))))

def brought_list(files: List<&2, String>) -> String:
  match files:
    case Nil{}:
      "There was nothing to bring over from "
    case Con{h, t}:
      String.concat(["Brought over ", String.join(h <> t, ", "), " from "])

# What the user is told the first time wizardry starts apart from Pi's own setup.
def brought_said(files: List<&2, String>, own: String, +old: String) -> String:
  String.concat(["logins and settings are now its own, in ", own, ". ", brought_list(files), old,
    ", which is no longer read: `wizardry delete old` removes it, and `wizardry auth login` signs in here."])

def counted(+n: Nat, one: String, many: String) -> String:
  String.concat([Nat.show(n), " ", Bool.pick(String, Nat.is_eq(n, 1n), one, many)])

def bulleted(lines: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.append("- ", h) <> bulleted(t)

# /default: this session's setup, made the one new sessions start with
# --------------------------------------------------------------------

def setting(name: String, +value: String) -> List<&2, Var>:
  Bool.pick(List<&2, Var>, String.is_empty(value), Nil{}, [Var{name, value}])

# What is written to Pi's settings, in wizardry's own directory: the model and thinking level of
# this session. What the session does not have is left as it was.
def default_settings(provider: String, model: String, thinking: String) -> List<&2, Var>:
  List.concat(&2, Var, [setting("defaultProvider", provider), setting("defaultModel", model), setting("defaultThinkingLevel", thinking)])

# Of everything that would load at a start, what is switched off for good when the plugins loaded
# now are made the default: whatever is not loaded now.
def kept_off(would_load: List<&2, String>, loaded: List<&2, String>) -> List<&2, String>:
  without(would_load, loaded)

def or_unset(+value: String) -> String:
  Bool.pick(String, String.is_empty(value), "as it was", value)

# What /default says it did.
def default_said(model: String, thinking: String, plugins: List<&2, String>) -> String:
  String.concat(["New sessions now start as this one. Model: ", or_unset(model), ". Thinking: ", or_unset(thinking),
    ". Plugins: ", String.join(plugins, ", "), "."])

# The one way into the agent's head
# ---------------------------------

# A plugin's only route to the agent is its actions, with these exceptions, made by the owner:
# the plugins named here may put a little text of their own in the standing prompt.
def minds() -> List<&2, String>:
  ["defintire"]

# How much a plugin may say there, in characters.
def little() -> Nat:
  240n

# What a plugin's text comes to: nothing unless the plugin is one of those named, and never more
# than a little.
def thought_of(owner: String, text: String) -> String:
  Bool.pick(String, has(minds(), owner), clip(String.trim(text), Nat.mul(5n, little())), "")

# The base prompt with a plugin's thought after it.
def minded(+base: String, +thought: String) -> String:
  Bool.pick(String, String.is_empty(thought), base, String.concat([base, "\n\n", thought]))
