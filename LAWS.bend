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

# An argument on the title line never runs past 72 characters.
law brief_fits:
  for text: String
  {C.fits(C.brief(text), 72n) == True{} : Bool}

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

# A session never starts again on new code while the agent is working, and only an interactive
# one ever does.
law restart_waits:
  for wanted: Bool
  for attached: Bool
  for tui: Bool
  for idle: Bool
  {C.restarts_now(wanted, attached, tui, False{}) == False{} : Bool} & {C.restarts_now(wanted, attached, False{}, idle) == False{} : Bool}

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

# Nothing is out of the agent's reach: an action that waits behind one nobody registered (a
# plugin that is not loaded, a name misspelled, no name at all) is not put away.
law never_out_of_reach:
  for +behind: String
  for names: List<&2, String>
  for called: List<&2, String>
  for gone: {C.has(names, behind) == False{} : Bool}
  {C.waits(behind, names, called) == False{} : Bool}

# Calling an action brings what waited behind it in front, whatever else is registered.
law calling_opens:
  for +behind: String
  for names: List<&2, String>
  for called: List<&2, String>
  for was: {C.has(called, behind) == True{} : Bool}
  {C.waits(behind, names, called) == False{} : Bool}

# A plugin loaded again has its actions in front of the agent, as `plugin_load` says: whether
# Pi knew the tool, and wherever it stood before, one that comes back and does not wait is there.
law loaded_again_is_in_front:
  for bound: Bool
  for known: Bool
  for active: Bool
  {C.in_front(bound, known, active, True{}, False{}) == True{} : Bool}

# A failure is told as it is the first time: only one made again unchanged, and failing again,
# comes with a word to change the approach. And a call that succeeds starts the count again.
law a_first_failure_says_nothing:
  for +said: String
  ({C.walled(0n, said) == said : String} & {C.walled(1n, said) == said : String}) & {C.walled(C.fails_after(False{}, 7n), said) == said : String}
