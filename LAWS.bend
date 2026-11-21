# What must hold of wizardry's decisions (bend/core.bend), whatever the input.
#
# Each law is a claim; PROOF.bend proves it. `bend PROOF.bend` prints ALL PROOFS CHECK only when
# every one of them holds, and `bend PROOF.bend --verdict` checks them again with the kernel that
# is itself proven in Lean. Change a law here when the rule itself changes, never to get a proof
# through.
#
# A law speaks of a decision, not of the world: that a plugin switched off is not in the list to
# load is proven here; that the list is then loaded, by Cordis, from files, is what the tests see.

import Base
import ./bend/core.bend as C

# A plugin the user switched off is never loaded at boot, shipped or not.
law disabled_never_load:
  for shipped: List<&2, C.Entry>
  for +found: List<&2, C.Entry>
  for +disabled: List<&2, String>
  {C.overlaps(C.names(C.plan(shipped, found, disabled)), disabled) == False{} : Bool}

# A plugin file in a plugin directory replaces the shipped default of the same name: the shipped
# one is not loaded beside it.
law home_replaces_shipped:
  for shipped: List<&2, C.Entry>
  for +found: List<&2, C.Entry>
  {C.overlaps(C.names(C.shipped_kept(shipped, found)), C.names(found)) == False{} : Bool}

# `focus` is never put away, whatever the agent asks to drop: it is the way back.
law focus_stays:
  for drop: List<&2, String>
  {C.overlaps(C.droppable(drop), ["focus"]) == False{} : Bool}

# Everything from `--` on is Pi's, unread: no option after it is taken for wizardry's.
law dashes_pass:
  for +rest: List<&2, String>
  {C.split_args("--" <> rest) == Some{C.Args{Nil{}, "--" <> rest}} : Maybe<&2, C.Args>}

# A session that restarts onto new code never carries -c, --continue, -r or --resume along: the
# session to open is named outright.
law restart_forgets_resume:
  for xs: List<&2, String>
  for +skip: Bool
  {C.any_resumes(C.strip(xs, skip)) == False{} : Bool}

# A clipped value fits the room it was clipped to.
law clip_fits:
  for +s: String
  for +p: Nat
  {C.fits(C.clip(s, 1n+p), 1n+p) == True{} : Bool}

# A collapsed result accounts for every line: the ones shown plus the ones counted as hidden.
law view_counts_all:
  for +lines: List<&2, String>
  for +limit: Nat
  {Nat.add(List.length(&2, String, C.first(lines, limit)), C.beyond(lines, limit)) == List.length(&2, String, lines) : Nat}

# Plugins: a default comes switched on, and is easy to change or remove
# ---------------------------------------------------------------------

# With nothing in the plugin directories and nothing switched off, every shipped default loads,
# in order.
law defaults_all_load:
  for +shipped: List<&2, C.Entry>
  {C.plan(shipped, Nil{}, Nil{}) == shipped : List<&2, C.Entry>}

# A plugin file in a plugin directory loads unless it is switched off.
law found_plugins_load:
  for +shipped: List<&2, C.Entry>
  for +found: List<&2, C.Entry>
  for +disabled: List<&2, String>
  for +name: String
  for there: {C.has(C.names(found), name) == True{} : Bool}
  for +on: {C.has(disabled, name) == False{} : Bool}
  {C.has(C.names(C.plan(shipped, found, disabled)), name) == True{} : Bool}

# A shipped default loads unless it is switched off: itself, or the file that replaced it.
law shipped_defaults_load:
  for +shipped: List<&2, C.Entry>
  for +found: List<&2, C.Entry>
  for +disabled: List<&2, String>
  for +name: String
  for there: {C.has(C.names(shipped), name) == True{} : Bool}
  for +on: {C.has(disabled, name) == False{} : Bool}
  {C.has(C.names(C.plan(shipped, found, disabled)), name) == True{} : Bool}

# Switched off for good, a builtin plugin does not start at boot. Automatic updates are the
# `update` plugin, so this is `wizardry update off` staying off.
law off_stays_off:
  for defaults: List<&2, String>
  for +disabled: List<&2, String>
  for +name: String
  {C.has(C.builtins_at_boot(defaults, C.switched_off(disabled, name)), name) == False{} : Bool}

# Switched off for good, a plugin file does not load at boot either, shipped or not.
law off_files_stay_off:
  for +shipped: List<&2, C.Entry>
  for +found: List<&2, C.Entry>
  for +disabled: List<&2, String>
  for +name: String
  {C.has(C.names(C.plan(shipped, found, C.switched_off(disabled, name))), name) == False{} : Bool}

# Switched back on, a builtin default starts at boot again.
law on_comes_back:
  for defaults: List<&2, String>
  for +disabled: List<&2, String>
  for +name: String
  for default: {C.has(defaults, name) == True{} : Bool}
  {C.has(C.builtins_at_boot(defaults, C.switched_on(disabled, name)), name) == True{} : Bool}

# Switching one plugin off or on leaves every other plugin as it was.
law off_touches_one:
  for +disabled: List<&2, String>
  for +name: String
  for +other: String
  for differs: {String.eq(name, other) == False{} : Bool}
  {C.has(C.switched_off(disabled, name), other) == C.has(disabled, other) : Bool}

law on_touches_one:
  for disabled: List<&2, String>
  for +name: String
  for +other: String
  for +differs: {String.eq(name, other) == False{} : Bool}
  {C.has(C.switched_on(disabled, name), other) == C.has(disabled, other) : Bool}

# What an act of the switch leaves the `update` plugin as, when loading and unloading do what
# they say (which test/wizardry.test.mjs checks on a real boot).
def loaded_after(act: C.Act, loaded: Bool) -> Bool:
  match act:
    case C.Loads{}:
      True{}
    case C.Unloads{}:
      False{}
    case C.Stays{}:
      loaded

# The switch for automatic updates ends where it was set, wherever it started.
law switch_settles:
  for on: Bool
  for loaded: Bool
  {loaded_after(C.switch_act(on, loaded), loaded) == on : Bool}

# `update` alone updates now, and `on` and `off` are the switch.
law update_words:
  ({C.update_asked("") == C.Now{} : C.Asked} & {C.update_asked("on") == C.On{} : C.Asked}) & {C.update_asked("off") == C.Off{} : C.Asked}

# A session taking over from one that restarted never unloads what it runs on.
law restore_keeps_core:
  for loaded: List<&2, String>
  for +wanted: List<&2, String>
  {C.overlaps(C.restore_unloads(loaded, wanted), C.core_plugins()) == False{} : Bool}

# A file whose name starts with `.` or `_` is never loaded as a plugin.
law hidden_files_skip:
  for rest: String
  for folder: Bool
  for entry: Bool
  {C.usable(SCon{'.', rest}, folder, entry) == False{} : Bool} & {C.usable(SCon{'_', rest}, folder, entry) == False{} : Bool}

# Every loaded plugin is listed under its own name, whatever state it is in.
law plugin_is_named:
  for +name: String
  for +state: String
  {String.starts_with(C.label(name, state), name) == True{} : Bool}

# Calls: named after the plugin, readable on one line
# ---------------------------------------------------

# A title an action sets for itself is shown as it is.
law title_wins:
  for c: Char
  for rest: String
  for native: Bool
  for +name: String
  for +owner: String
  {C.action_title(SCon{c, rest}, native, name, owner) == SCon{c, rest} : String}

# Pi's own tools keep their names: read, write, edit, bash.
law native_keeps_name:
  for +name: String
  for +owner: String
  {C.action_title("", True{}, name, owner) == name : String}

# Every other call is shown under the name of the plugin it comes from.
law named_by_plugin:
  for +name: String
  for +owner: String
  {C.mine(C.action_title("", False{}, name, owner), C.words(owner)) == True{} : Bool}

# `subagent_create` from `subagent` reads "subagent create", `plugin_load` from `cordis`
# "cordis plugin load".
law title_examples:
  {C.action_title("", False{}, "subagent_create", "subagent") == "subagent create" : String} & {C.action_title("", False{}, "plugin_load", "cordis") == "cordis plugin load" : String}

# An argument on the title line never runs past 72 characters.
law brief_fits:
  for text: String
  {C.fits(C.brief(text), 72n) == True{} : Bool}

# An expanded result is shown whole.
law expanded_shows_all:
  for +lines: List<&2, String>
  for +limit: Nat
  {C.view_of(True{}, lines, limit) == C.View{lines, 0n} : C.View}

# When no line is counted as hidden, none is: the result is shown whole.
law nothing_hidden_unsaid:
  for lines: List<&2, String>
  for limit: Nat
  for none: {C.beyond(lines, limit) == 0n : Nat}
  {C.first(lines, limit) == lines : List<&2, String>}

# The command line: Pi gets what is Pi's, and adds nothing to the agent by itself
# ------------------------------------------------------------------------------

# Arguments with no --plugin and no --gate among them all go to Pi, unchanged.
law plain_args_pass:
  for +argv: List<&2, String>
  for +plugin: {C.has(argv, "--plugin") == False{} : Bool}
  for +gate: {C.has(argv, "--gate") == False{} : Bool}
  {C.split_args(argv) == Some{C.Args{Nil{}, argv}} : Maybe<&2, C.Args>}

# Pi always starts with its own tools, extensions, skills, prompt templates and context files
# off: what the agent can do comes only from plugins.
law pi_adds_nothing:
  for +rest: List<&2, String>
  for sessions: String
  for themes: String
  for pair: String
  {C.covers(C.pi_args(rest, sessions, themes, pair),
    ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files"]) == True{} : Bool}

# Everything the user passed for Pi reaches it, in order, after what wizardry puts in front.
law user_args_reach_pi:
  for +rest: List<&2, String>
  for +sessions: String
  for +themes: String
  for +pair: String
  exs before: List<&2, String>
  {C.pi_args(rest, sessions, themes, pair) == List.append(&2, String, before, rest) : List<&2, String>}

# A theme the user asked for is not overridden by wizardry's.
law own_theme_wins:
  for rest: List<&2, String>
  for themes: String
  for pair: String
  for asked: {C.has(rest, "--use-theme") == True{} : Bool}
  {C.theme_args(rest, themes, pair) == ["--theme", themes] : List<&2, String>}

# A session that restarts onto new code carries no --session, --fork or --session-id along
# either: the one session it opens is the one it was in.
law restart_names_one_session:
  for xs: List<&2, String>
  for +skip: Bool
  {C.any_chooses(C.strip(xs, skip)) == False{} : Bool}

# The agent's own tools
# ---------------------

# Whatever is dropped and taken, `focus` is still in front of the agent afterwards.
law focus_survives:
  for +active: List<&2, String>
  for +drop: List<&2, String>
  for take: List<&2, String>
  for there: {C.has(active, "focus") == True{} : Bool}
  {C.has(C.focus_active(active, drop, take), "focus") == True{} : Bool}

# An action the agent takes up is in front of it afterwards.
law taken_is_active:
  for active: List<&2, String>
  for drop: List<&2, String>
  for take: List<&2, String>
  for +name: String
  for asked: {C.has(take, name) == True{} : Bool}
  {C.has(C.focus_active(active, drop, take), name) == True{} : Bool}

# An action the agent puts away, and does not take up again, is gone.
law dropped_is_gone:
  for active: List<&2, String>
  for +drop: List<&2, String>
  {C.overlaps(C.focus_active(active, drop, Nil{}), C.droppable(drop)) == False{} : Bool}

# `raw: true` runs a command exactly as written.
law raw_runs_as_written:
  for command: String
  {C.rtk_skips(True{}, command) == True{} : Bool}

# With nothing written by `become`, the standing prompt is the base prompt and nothing else.
law prompt_is_only_base:
  for +base: String
  {C.system_prompt(base, "") == base : String}

# Whatever the agent writes for itself comes after the base prompt and never replaces it.
law prompt_keeps_base:
  for +base: String
  for +identity: String
  {String.starts_with(C.system_prompt(base, identity), base) == True{} : Bool}

# The caps: they twinkle in place, in blues and greys
# ---------------------------------------------------

# Every frame of the cap has the plain cap's shape, so nothing beside or below it moves.
law cap_keeps_its_shape:
  for frame: Nat
  {C.widths(C.hat_frame(frame)) == C.widths(C.hat()) : List<&2, Nat>}

# Still, the cap is the plain logo.
law cap_starts_plain:
  {C.hat_frame(0n) == C.hat() : List<&2, String>}

# Every frame of the small cap is seven wide, so the message beside it stays put.
law small_cap_stays_put:
  {C.widths(C.small_hat()) == [7n, 7n, 7n, 7n, 7n, 7n] : List<&2, Nat>}

# Every piece of a cap is drawn in one of four theme colors. That those four are blues and greys
# in both themes is a test (test/wizardry.test.mjs): no proof reaches the theme files.
law caps_are_blue_and_grey:
  for part: String
  {C.has(C.inks(), C.ink(part)) == True{} : Bool}

# The session, the header and the rest of what moved from TypeScript
# ------------------------------------------------------------------

# A session never starts again on new code while the agent is working, and only an interactive
# one ever does.
law restart_waits:
  for wanted: Bool
  for attached: Bool
  for tui: Bool
  for idle: Bool
  {C.restarts_now(wanted, attached, tui, False{}) == False{} : Bool} & {C.restarts_now(wanted, attached, False{}, idle) == False{} : Bool}

# How many there are on all the lines together.
def total(counts: List<&2, Nat>) -> Nat:
  match counts:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(h, total(t))

# Packing the header's hints onto lines places every one of them, whatever the width.
law pack_places_all:
  for widths: List<&2, Nat>
  for +sep: Nat
  for +width: Nat
  {total(C.pack(widths, sep, width)) == List.length(&2, Nat, widths) : Nat}

# rtk changes a command only when `rtk rewrite` ended with 0 or 3.
law rtk_needs_a_rewrite:
  for +code: Nat
  for out: String
  for command: String
  for zero: {Nat.is_eq(code, 0n) == False{} : Bool}
  for three: {Nat.is_eq(code, 3n) == False{} : Bool}
  {C.rtk_takes(code, out, command) == None{} : Maybe<&2, String>}

# A directory the user named is the one wizardry uses.
law named_home_wins:
  for c: Char
  for rest: String
  for +old_chosen: String
  for home: String
  for old: String
  for has_home: Bool
  for has_old: Bool
  {C.home_of(SCon{c, rest}, old_chosen, home, old, has_home, has_old) == SCon{c, rest} : String}

# An old install is never moved over a ~/.wizardry that is already there, nor when the user
# named a directory.
law adopting_overwrites_nothing:
  for named: Bool
  for has_home: Bool
  for has_old: Bool
  for link: Bool
  {C.adopts_home(named, True{}, has_old, link) == False{} : Bool} & {C.adopts_home(True{}, has_home, has_old, link) == False{} : Bool}

# The cap stays still once it has scrolled away on the main screen.
law cap_rests_off_screen:
  {C.cap_moves(False{}, False{}) == False{} : Bool}

# Kept apart: wizardry's logins, settings, conversations and memories are its own
# -------------------------------------------------------------------------------

# Pi's directory, when wizardry runs it, is inside wizardry's own, wherever that is.
law pi_dir_is_wizardrys:
  for +home: String
  {String.starts_with(C.own_pi(home), home) == True{} : Bool}

# What a variable is set to among `vars`.
def set_to(vars: List<&2, C.Var>, +name: String) -> Maybe<&2, String>:
  match vars:
    case Nil{}:
      None{}
    case Con{C.Var{n, v}, t}:
      Bool.pick(Maybe<&2, String>, String.eq(n, name), Some{v}, set_to(t, name))

# Pi is pointed at that directory, whatever the environment wizardry was started in said.
law pi_is_pointed_home:
  for home: String
  {set_to(C.pi_env(home), "PI_CODING_AGENT_DIR") == Some{C.own_pi(home)} : Maybe<&2, String>}

# Pi always starts with theme discovery, MCP servers and project-local files off: nothing lying
# around a project, and nothing another setup installed, is read.
law pi_reads_nothing_around:
  for +rest: List<&2, String>
  for sessions: String
  for themes: String
  for pair: String
  {C.covers(C.pi_args(rest, sessions, themes, pair), ["--no-themes", "--no-mcp", "--no-approve"]) == True{} : Bool}

# Nothing that adds to a session comes over from Pi's own settings: no packages, extensions,
# skills, prompt templates or themes, and no place to keep sessions other than wizardry's.
law addons_stay_behind:
  {C.settings_brought(C.pi_addons()) == Nil{} : List<&2, String>}

# Whatever Pi's own settings hold, nothing but the settings wizardry names is brought over.
law only_named_settings_come:
  for keys: List<&2, String>
  {C.covers(C.brought_settings(), C.settings_brought(keys)) == True{} : Bool}

# Logins are never brought over onto a directory that is already there, nor from a directory
# onto itself.
law logins_overwrite_nothing:
  for has_own: Bool
  for has_old: Bool
  for old: String
  for own: String
  for +dir: String
  {C.brings(True{}, has_old, old, own) == False{} : Bool} & {C.brings(has_own, has_old, dir, dir) == False{} : Bool}

# Export and delete: easy to ask for, and nothing is lost by asking
# -----------------------------------------------------------------

# `export` and `delete` are wizardry's own commands.
law words_of_keeping:
  {C.command_of("export") == C.Export{} : C.Command} & {C.command_of("delete") == C.Delete{} : C.Command}

# Every conversation an export copies is written inside the export's folder.
law export_stays_in_its_folder:
  for +dir: String
  for origin: String
  for rel: String
  {String.starts_with(C.conversation_to(dir, origin, rel), dir) == True{} : Bool}

# Without --yes, nothing is deleted.
law delete_asks_first:
  for paths: List<&2, String>
  for exported: C.Exported
  {C.goes(paths, False{}, exported) == Nil{} : List<&2, String>}

# When the export that comes first did not finish, nothing is deleted.
law delete_waits_for_export:
  for paths: List<&2, String>
  for yes: Bool
  {C.goes(paths, yes, C.Failed{}) == Nil{} : List<&2, String>}

# The export is never among what is deleted: no deleted path is its folder or holds it.
law delete_keeps_the_export:
  for what: C.What
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {C.takes(C.doomed(what, home, old, userhome, to), to) == False{} : Bool}

# Whatever wizardry's directory was set to, deleting never takes the user's home directory, nor
# anything that holds it.
law delete_spares_your_home:
  for +what: C.What
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {C.takes(C.doomed(what, home, old, userhome, to), userhome) == False{} : Bool}

# Whether any of `paths` is `root` or inside it.
def any_inside(paths: List<&2, String>, +root: String) -> Bool:
  match paths:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(C.inside(h, root), any_inside(t, root))

# Deleting the old setup leaves wizardry whole: nothing deleted is wizardry's directory, holds
# it, or is inside it.
law old_spares_wizardry:
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {C.takes(C.doomed(C.Old{}, home, old, userhome, to), home) == False{} : Bool} & {any_inside(C.doomed(C.Old{}, home, old, userhome, to), home) == False{} : Bool}

# /default
# --------

# Making what is loaded now the default switches off nothing that is loaded now.
law default_keeps_what_is_loaded:
  for would_load: List<&2, String>
  for +loaded: List<&2, String>
  {C.overlaps(C.kept_off(would_load, loaded), loaded) == False{} : Bool}

# A session with no model or thinking level to speak of changes neither default.
law default_writes_only_what_is_set:
  {C.default_settings("", "", "") == Nil{} : List<&2, C.Var>}

# The one way into the agent's head
# ---------------------------------

# A plugin the owner did not name puts nothing in the standing prompt, whatever it says.
law only_named_plugins_think:
  for +owner: String
  for text: String
  for unnamed: {C.has(C.minds(), owner) == False{} : Bool}
  {C.thought_of(owner, text) == "" : String}

# defintire is the one named.
law defintire_is_the_exception:
  {C.minds() == ["defintire"] : List<&2, String>}

# A plugin with nothing to say changes nothing, and what one does say comes after the base
# prompt and never replaces it.
law a_thought_keeps_the_base:
  for +base: String
  for +thought: String
  {C.minded(base, "") == base : String} & {String.starts_with(C.minded(base, thought), base) == True{} : Bool}
