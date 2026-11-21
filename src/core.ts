import bend from '../core/core.mjs'

/**
 * wizardry's decisions, which are written in Bend (bend/core.bend) and proven against LAWS.bend.
 *
 * This file is only the crossing: it turns arrays and optional values into the lists and
 * constructors Bend takes, calls the def, and turns the answer back. No decision is made here.
 * core/core.mjs is the compiled Bend, committed so that an install without Bend still builds;
 * `npm run core` regenerates it and `npm test` fails when it is stale.
 */

type List<T> = { $: 'Nil' } | { $: 'Con'; head: T; tail: List<T> }
type Maybe<T> = { $: 'None' } | { $: 'Some'; value: T }

function list<T>(items: readonly T[]): List<T> {
  let out: List<T> = { $: 'Nil' }
  for (let i = items.length - 1; i >= 0; i--) out = { $: 'Con', head: items[i], tail: out }
  return out
}

function array<T>(items: List<T>): T[] {
  const out: T[] = []
  for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head)
  return out
}

const maybe = <T>(value: T | undefined): Maybe<T> => (value === undefined ? { $: 'None' } : { $: 'Some', value })

/** A plugin file found in a directory. */
export interface Entry {
  name: string
  path: string
}

const entries = (items: readonly Entry[]) => list(items.map(({ name, path }) => ({ $: 'Entry', name, path })))

export type Command = 'Help' | 'Version' | 'PiOnly' | 'Auth' | 'Update' | 'Export' | 'Delete' | 'Run'
/** What `wizardry update` and `/update` were asked for. */
export type Asked = 'Now' | 'On' | 'Off' | 'Unclear'
/** What the switch for automatic updates does to the `update` plugin. */
export type Act = 'Loads' | 'Unloads' | 'Stays'

const some = <T>(value: Maybe<T>): T | undefined => (value.$ === 'Some' ? value.value : undefined)

/** A loaded plugin, as the header and the listings speak of it. */
export interface Loaded {
  name: string
  state: string
  source: string
}

const rows_ = (items: readonly Row[]) => list(items.map(({ path, bytes }) => ({ $: 'Row', path, bytes })))

const loaded = (items: readonly Loaded[]) => list(items.map(({ name, state, source }) => ({ $: 'Loaded', name, state, source })))

/** A variable of the environment and what it is set to. */
export interface Var {
  name: string
  value: string
}

/** A setup that keeps conversations, and where it keeps them. */
export interface Origin {
  name: string
  dir: string
}

/** How many conversations an export took from one setup. */
export interface Tally {
  name: string
  from: string
  count: number
}

/** A command that is a link, and what it points to. */
export interface Link {
  path: string
  target: string
}

/** A path that would be deleted, and how much is in it. */
export interface Row {
  path: string
  bytes: number
}

/** What `wizardry delete` was asked. */
export interface Removal {
  what: string
  yes: boolean
  waived: boolean
  to: string
  clear: boolean
}

/** How the export that comes before a deletion ended. */
export type Exported = 'Kept' | 'Failed' | 'Waived'

/** Where the header's text goes, and how wide it may be. */
export type Layout = { where: 'Beside' | 'Under'; room: number }

export const core = {
  /** Whether `x` is one of `xs`. */
  among: (xs: readonly string[], x: string): boolean => bend.among(list(xs), x),

  /** wizardry's directory: the one the user named, else ~/.wizardry, unless only the old one is there. */
  homeOf: (chosen: string, oldChosen: string, home: string, old: string, hasHome: boolean, hasOld: boolean): string =>
    bend.home_of(chosen, oldChosen, home, old, hasHome, hasOld),
  /** Whether an old ~/.izardry is moved to ~/.wizardry. */
  adoptsHome: (named: boolean, hasHome: boolean, hasOld: boolean, oldIsLink: boolean): boolean => bend.adopts_home(named, hasHome, hasOld, oldIsLink),
  /** Whether a `wizardry` command is made beside an `izardry` one. */
  adoptsCommand: (invoked: string, isLink: boolean, hasCommand: boolean): boolean => bend.adopts_command(invoked, isLink, hasCommand),
  /** What the user is told after an old install was carried over, if anything moved. */
  adopted: (home: boolean, command: boolean): string | undefined => some<string>(bend.adopted(home, command)),
  /** The two plugin directories, once when they are the same one. */
  pluginDirs: (home: string, cwd: string): string[] => array(bend.plugin_dirs(home, cwd)),
  /** What `~/x` names under the home directory, if the source starts that way. */
  underHome: (source: string): string | undefined => some<string>(bend.under_home(source)),
  /** Whether a source names a builtin. */
  isBuiltinSource: (prefixed: boolean, builtin: boolean, exists: boolean): boolean => bend.is_builtin_source(prefixed, builtin, exists),
  /** A plugin's state, as Cordis numbers it. */
  stateName: (state: number): string => bend.state_name(state),

  /** What is said when something cannot be done. */
  said: {
    alreadyLoaded: (name: string): string => bend.already_loaded(name),
    notLoaded: (name: string): string => bend.not_loaded(name),
    runsOnIt: (name: string, verb: string): string => bend.runs_on_it(name, verb),
    noBuiltin: (name: string, builtins: readonly string[]): string => bend.no_builtin(name, list(builtins)),
    noPluginAt: (path: string): string => bend.no_plugin_at(path),
    noEntry: (path: string): string => bend.no_entry(path),
    loadFailed: (source: string, why: string): string => bend.load_failed(source, why),
    needsExecute: (name: string): string => bend.needs_execute(name),
    alreadyRegistered: (name: string, owner: string): string => bend.already_registered(name, owner),
    noAction: (name: string): string => bend.no_action(name),
    actionGone: (name: string): string => bend.action_gone(name),
    commandGone: (name: string): string => bend.command_gone(name),
    noSuchActions: (names: readonly string[]): string => bend.no_such_actions(list(names)),
    unloaded: (name: string): string => bend.unloaded_text(name),
    noMap: (app: string): string => bend.no_map(app),
    notACheckout: (app: string): string => bend.not_a_checkout(app),
    rtkMissing: (configured: string | undefined): string => bend.rtk_missing(maybe(configured)),
    gateAsks: (title: string): string => bend.gate_asks(title),
    gateNoOne: (name: string): string => bend.gate_no_one(name),
    gateDeclined: (name: string): string => bend.gate_declined(name),
  },

  /** The usage text. */
  help: (): string => bend.help(),
  /** What is said of a Pi command wizardry does not take. */
  piOnlyText: (first: string, argv: readonly string[]): string => bend.pi_only_text(first, list(argv)),
  /** Whether the arguments ask for the list of plugins. */
  listsPlugins: (rest: readonly string[]): boolean => bend.lists_plugins(list(rest)),
  /** A plugin as `wizardry plugins` lists it. */
  listing: (name: string, state: string, source: string, actions: readonly string[]): string => bend.listing(name, state, source, list(actions)),
  /** What the switch for automatic updates says it is now. */
  switchSaid: (on: boolean): string => bend.switch_said(on),
  /** What was already said to a session that restarts: its messages, and its files as `@file`. */
  saidOf: (messages: readonly string[], files: readonly string[]): string[] => array(bend.said_of(list(messages), list(files))),

  /** Whether a session starts again on new code now. */
  restartsNow: (wanted: boolean, attached: boolean, tui: boolean, idle: boolean): boolean => bend.restarts_now(wanted, attached, tui, idle),
  /** Whether a tool declared again stays put away. */
  staysAway: (bound: boolean, known: boolean, active: boolean): boolean => bend.stays_away(bound, known, active),
  /** The standing instructions a session carries: the last the agent wrote on this branch. */
  lastIdentity: (written: readonly string[]): string => bend.last_identity(list(written)),
  /** What `become` keeps of what it was given. */
  tidy: (identity: string): string => bend.tidy(identity),
  becomeSaid: (identity: string): string => bend.become_said(identity),
  /** The words offered after a slash command: those that start with what was typed. */
  completions: (words: readonly string[], typed: string): string[] => array(bend.completions(list(words), typed)),
  /** The day of an ISO time. */
  day: (iso: string): string => bend.day(iso),
  focusSaid: (active: readonly string[], away: readonly string[]): string => bend.focus_said(list(active), list(away)),
  /** The thinking levels the agent may set. */
  thinkLevels: (): string[] => array(bend.think_levels()),
  thinkDescribe: (): string => bend.think_describe(),
  thinkSaid: (level: string): string => bend.think_said(level),

  /** Whether a checkout is the installer's own or one someone works in. */
  kindOf: (managed: boolean): 'install' | 'clone' => bend.kind_of(managed),
  /** What a session says once it is back on new code. */
  carriedOn: (what?: string): string => bend.carried_on(maybe(what)),
  updateSaid: (line: string): string => bend.update_said(line),

  /** The command rtk would run in place of `command`, if `rtk rewrite` gave one. */
  rtkTakes: (code: number, out: string, command: string): string | undefined => some<string>(bend.rtk_takes(code, out, command)),
  /** Where rtk is looked for. */
  rtkPlaces: (configured: string | undefined, dirs: readonly string[], home: string): string[] => array(bend.rtk_places(maybe(configured), list(dirs), home)),
  /** The actions gate asks about unless told otherwise. */
  gated: (): string[] => array(bend.gated()),
  gateSummary: (params: string): string => bend.gate_summary(params),

  /** Items of these widths on as few lines as `width` allows: how many go on each line. */
  pack: (widths: readonly number[], sep: number, width: number): number[] => array(bend.pack(list(widths), sep, Math.max(0, width))),
  /** Where the header's text goes at this width. */
  layout(width: number, hatWidth: number): Layout {
    const at: { $: 'Beside' | 'Under'; room: number } = bend.layout(Math.max(0, width), hatWidth)
    return { where: at.$, room: at.room }
  },
  /** The header's rows with its text beside the cap. */
  headerBeside: (hat: readonly string[], lines: readonly string[], hatWidth: number): string[] => array(bend.header_beside(list(hat), list(lines), hatWidth)),
  /** The header's rows with its text under the cap. */
  headerUnder: (hat: readonly string[], lines: readonly string[]): string[] => array(bend.header_under(list(hat), list(lines))),
  /** Whether the cap moves on this tick. */
  capMoves: (viewport: boolean, atTop: boolean): boolean => bend.cap_moves(viewport, atTop),
  nextFrame: (frame: number): number => bend.next_frame(frame),
  /** Whether a result has nothing to show. */
  blankView: (shown: readonly string[], more: number): boolean => bend.blank_view(list(shown), more),
  moreHint: (more: number): string => bend.more_hint(more),
  /** The plugins, one to a row with where each comes from. */
  pluginRows: (plugins: readonly Loaded[]): string[] => array(bend.plugin_rows(loaded(plugins))),
  /** The plugins on one line, to be wrapped to the width. */
  pluginLine: (plugins: readonly Loaded[]): string => bend.plugin_line(loaded(plugins)),
  indented: (rows: readonly string[]): string[] => array(bend.indented(list(rows))),
  /** What `cordis_inspect` answers. */
  inspectText: (lines: readonly string[], idle: readonly string[]): string => bend.inspect_text(list(lines), list(idle)),

  /** `xs` without the names in `bad`. */
  without: (xs: readonly string[], bad: readonly string[]): string[] => array(bend.without(list(xs), list(bad))),
  /** The names of `xs` that are also in `good`. */
  only: (xs: readonly string[], good: readonly string[]): string[] => array(bend.only(list(xs), list(good))),

  /** What boot loads from the plugin folders, in order. */
  plan: (shipped: readonly Entry[], found: readonly Entry[], disabled: readonly string[]): Entry[] =>
    array<Entry>(bend.plan(entries(shipped), entries(found), list(disabled))).map(({ name, path }) => ({ name, path })),
  /** The builtin plugins boot starts: the defaults, less the ones switched off. */
  builtinsAtBoot: (defaults: readonly string[], disabled: readonly string[]): string[] =>
    array(bend.builtins_at_boot(list(defaults), list(disabled))),
  /** The names that are switched off once `name` is unloaded for good. */
  switchedOff: (disabled: readonly string[], name: string): string[] => array(bend.switched_off(list(disabled), name)),
  /** The names that are switched off once `name` is loaded for good. */
  switchedOn: (disabled: readonly string[], name: string): string[] => array(bend.switched_on(list(disabled), name)),
  /** Whether a plugin loaded for good is written down to load at every start. */
  remembered: (builtin: boolean, isDefault: boolean): boolean => bend.remembered(builtin, isDefault),
  /** Whether a plugin is what the session runs on, and so cannot be unloaded from inside it. */
  isCore: (name: string): boolean => bend.is_core(name),
  /** What a process taking over from another unloads to match it. */
  restoreUnloads: (loaded: readonly string[], wanted: readonly string[]): string[] =>
    array(bend.restore_unloads(list(loaded), list(wanted))),
  /** Whether a directory entry is a plugin: a module file, or a folder with an entry file. */
  usable: (name: string, folder: boolean, entry: boolean): boolean => bend.usable(name, folder, entry),
  /** A file name without its extension. */
  stem: (name: string): string => bend.stem(name),
  /** The first candidate that can name a plugin; anything that is not a string is passed over. */
  pickName: (candidates: readonly unknown[]): string => bend.pick_name(list(candidates.map((value) => (typeof value === 'string' ? value : '')))),

  /** What the first command-line argument asks for. */
  commandOf: (first: string | undefined): Command => bend.command_of(first ?? '').$,
  /** wizardry's own options apart from Pi's; undefined when a --plugin has no value. */
  splitArgs(argv: readonly string[]): { extra: string[]; rest: string[] } | undefined {
    const split: Maybe<{ extra: List<string>; rest: List<string> }> = bend.split_args(list(argv))
    return split.$ === 'Some' ? { extra: array(split.value.extra), rest: array(split.value.rest) } : undefined
  },
  /** Pi arguments that put wizardry's colors on, unless the user asked for a theme of their own. */
  themeArgs: (rest: readonly string[], themes: string, pair: string): string[] => array(bend.theme_args(list(rest), themes, pair)),
  /** The arguments Pi starts with. */
  piArgs: (rest: readonly string[], sessions: string, themes: string, pair: string): string[] =>
    array(bend.pi_args(list(rest), sessions, themes, pair)),
  /** The Pi arguments for a process taking over from this one. `said` are the messages already sent. */
  restartArgs: (rest: readonly string[], said: readonly string[], session?: string): string[] =>
    array(bend.restart_args(list(rest), list(said), maybe(session))),

  /** A name as words: "plugin_load" is "plugin load". */
  words: (text: string): string => bend.words(text),
  /** Whether a title already starts with the plugin's name. */
  mine: (title: string, owner: string): boolean => bend.mine(title, owner),
  /** What the user sees a call named as. */
  actionTitle: (title: string | undefined, native: boolean, name: string, owner: string): string =>
    bend.action_title(title ?? '', native, name, owner),
  /** One argument value on the title line: on one line, and cut short. */
  brief: (text: string): string => bend.brief(text),
  /** Text as the terminal shows it, with `pad` after each newline. */
  expand: (text: string, pad: string): string => bend.expand(text, pad),
  /** The lines of a result the user is shown, and how many more there are. */
  resultView(output: string, expanded: boolean): { shown: string[]; more: number } {
    const view: { shown: List<string>; more: number } = bend.result_view(output, expanded)
    return { shown: array(view.shown), more: view.more }
  },

  /** The actions in front of the agent after it drops some and takes some up. */
  focusActive: (active: readonly string[], drop: readonly string[], take: readonly string[]): string[] =>
    array(bend.focus_active(list(active), list(drop), list(take))),
  /** Whether rtk leaves a command alone. */
  rtkSkips: (raw: boolean, command: string): boolean => bend.rtk_skips(raw, command),

  /** What `wizardry update <word>` and `/update <word>` ask for; no word is "update now". */
  updateAsked: (word: string | undefined): Asked => bend.update_asked(word ?? '').$,
  /** What the switch for automatic updates does to the `update` plugin, given whether it is loaded. */
  switchAct: (on: boolean, loaded: boolean): Act => bend.switch_act(on, loaded).$,
  /** The last thing an update run printed, without its "wizardry: " prefix. */
  updateLine: (said: string): string => bend.update_line(said),
  updated: (line: string): boolean => bend.updated(line),

  /** The logo: a wizard's cap, row by row. */
  hat: (): string[] => array(bend.hat()),
  /** The cap's rows on one frame of its twinkle. */
  hatFrame: (frame: number): string[] => array(bend.hat_frame(frame)),
  /** The frames of the small cap that stands where Pi's spinner did. */
  smallHat: (): string[] => array(bend.small_hat()),
  /** The theme color a piece of a cap is drawn in, by its first character. */
  ink: (part: string): string => bend.ink(part),

  /** A plugin in the header. */
  label: (name: string, state: string): string => bend.label(name, state),
  /** A plugin as `cordis_inspect` lists it. */
  inspectLine: (name: string, state: string, source: string, actions: readonly string[]): string =>
    bend.inspect_line(name, state, source, list(actions)),
  /** What the agent is told after loading or reloading a plugin. */
  loadedText: (verb: string, name: string, state: string, actions: readonly string[]): string =>
    bend.loaded_text(verb, name, state, list(actions)),
  /** The description the agent is shown: the action's own, then a note from every layer around it. */
  described: (description: string, notes: readonly string[]): string => bend.described(description, list(notes)),

  /** The whole standing prompt. */
  basePrompt: (cwd: string, date: string): string => bend.base_prompt(cwd, date),
  /** The standing prompt with what the agent wrote for itself. */
  systemPrompt: (base: string, identity: string): string => bend.system_prompt(base, identity),

  /** Where Pi keeps its logins and settings when wizardry runs it: inside wizardry's own directory. */
  ownPi: (home: string): string => bend.own_pi(home),
  /** Where the Pi installed on this machine keeps its own, given what PI_CODING_AGENT_DIR said. */
  oldPi: (named: string, userhome: string): string => bend.old_pi(named, userhome),
  /** What wizardry sets in the environment for Pi. */
  piEnv: (home: string): Var[] => array<Var>(bend.pi_env(home)).map(({ name, value }) => ({ name, value })),
  /** What it takes out of it. */
  piEnvCleared: (): string[] => array(bend.pi_env_cleared()),
  /** Every variable it changes; a command the agent runs sees each as it was. */
  piEnvTouched: (): string[] => array(bend.pi_env_touched()),
  /** The files brought over from Pi's own directory, once. */
  broughtFiles: (): string[] => array(bend.brought_files()),
  /** Of the settings Pi's own setup holds, the ones brought over. */
  settingsBrought: (keys: readonly string[]): string[] => array(bend.settings_brought(list(keys))),
  /** Whether logins are brought over now. */
  brings: (hasOwn: boolean, hasOld: boolean, old: string, own: string): boolean => bend.brings(hasOwn, hasOld, old, own),
  broughtSaid: (files: readonly string[], own: string, old: string): string => bend.brought_said(list(files), own, old),

  /** Where conversations are kept. */
  sessionsDir: (home: string): string => bend.sessions_dir(home),
  /** Where an export goes: where the user said, else a folder named for the day. */
  exportDir: (chosen: string, userhome: string, day: string, again: number): string => bend.export_dir(chosen, userhome, day, again),
  /** The setups whose conversations an export copies. */
  origins: (home: string, old: string): Origin[] => array<Origin>(bend.origins(home, old)).map(({ name, dir }) => ({ name, dir })),
  /** Whether an export may be written to `dir`. */
  exportFits: (dir: string, home: string, old: string): boolean => bend.export_fits(dir, home, old),
  isConversation: (name: string): boolean => bend.is_conversation(name),
  /** Where a conversation goes in an export. */
  conversationTo: (dir: string, origin: string, rel: string): string => bend.conversation_to(dir, origin, rel),
  /** The file beside a conversation that holds it as text to read. */
  readable: (path: string): string => bend.readable(path),
  transcriptHead: (file: string, cwd: string, started: string): string => bend.transcript_head(file, cwd, started),
  /** One piece of a conversation as text to read; empty for what is not written down. */
  piece: (kind: string, name: string, at: string, text: string): string => bend.piece(kind, name, at, text),
  /** The folders of wizardry's directory that are copied as they are when no plugin exported them. */
  leftOver: (folders: readonly string[], written: readonly string[]): string[] => array(bend.left_over(list(folders), list(written))),
  leftOverLine: (name: string): string => bend.left_over_line(name),
  /** What an export holds, line by line. */
  exportLines: (tallies: readonly Tally[], wrote: readonly string[]): string[] =>
    array(bend.export_lines(list(tallies.map(({ name, from, count }) => ({ $: 'Tally', name, from, count }))), list(wrote))),
  exportReadme: (day: string, lines: readonly string[]): string => bend.export_readme(day, list(lines)),
  exportSaid: (dir: string, lines: readonly string[]): string => bend.export_said(dir, list(lines)),
  exportInside: (dir: string): string => bend.export_inside(dir),
  exportTaken: (dir: string): string => bend.export_taken(dir),
  exportBroke: (why: string): string => bend.export_broke(why),
  exportUsage: (): string => bend.export_usage(),
  /** `wizardry export [folder]`: the folder asked for (empty for none); undefined when unclear. */
  exportAsked: (argv: readonly string[]): string | undefined => some<string>(bend.export_asked(list(argv))),

  /** What `wizardry delete` was asked. */
  deleteAsked(argv: readonly string[]): Removal {
    const { what, yes, waived, to, clear }: Removal = bend.delete_asked(list(argv))
    return { what, yes, waived, to, clear }
  },
  /** What `wizardry delete <what>` removes; nothing when it may not. */
  doomed: (what: string, home: string, old: string, userhome: string, to: string): string[] =>
    array(bend.doomed(bend.what_of(what), home, old, userhome, to)),
  /** Why it removes nothing, or empty when it would remove something. */
  whyNot: (what: string, home: string, old: string, userhome: string, to: string): string =>
    bend.why_not(bend.what_of(what), home, old, userhome, to),
  /** Of what would be removed, what is, given --yes and how the export ended. */
  goes: (paths: readonly string[], yes: boolean, exported: Exported): string[] => array(bend.goes(list(paths), yes, { $: exported })),
  /** The folders left empty by a deletion, removed only if they are. */
  emptied: (what: string, doomed: readonly string[], userhome: string): string[] =>
    array(bend.emptied(bend.what_of(what), list(doomed), userhome)),
  /** The links that would point at nothing once `doomed` is deleted. */
  dangling: (links: readonly Link[], doomed: readonly string[]): string[] =>
    array(bend.dangling(list(links.map(({ path, target }) => ({ $: 'Link', path, target }))), list(doomed))),
  /** Where commands that are links are looked for. */
  linkDirs: (invoked: string, named: string, userhome: string): string[] => array(bend.link_dirs(invoked, named, userhome)),
  oldHomeLink: (userhome: string): string => bend.old_home_link(userhome),
  deleteUsage: (): string => bend.delete_usage(),
  deletePreview: (word: string, rows: readonly Row[], links: readonly string[], to: string, waived: boolean): string =>
    bend.delete_preview(word, rows_(rows), list(links), to, waived),
  deletedSaid: (rows: readonly Row[], links: readonly string[], to: string, waived: boolean): string =>
    bend.deleted_said(rows_(rows), list(links), to, waived),
  nothingThere: (what: string): string => bend.nothing_there(bend.what_of(what)),
  exportFirstFailed: (why: string): string => bend.export_first_failed(why),

  /** What /default writes to Pi's settings: this session's model and thinking level. */
  defaultSettings: (provider: string, model: string, thinking: string): Var[] =>
    array<Var>(bend.default_settings(provider, model, thinking)).map(({ name, value }) => ({ name, value })),
  /** Of what would load at a start, what is switched off when the plugins loaded now become the default. */
  keptOff: (wouldLoad: readonly string[], loaded: readonly string[]): string[] => array(bend.kept_off(list(wouldLoad), list(loaded))),
  defaultSaid: (model: string, thinking: string, plugins: readonly string[]): string => bend.default_said(model, thinking, list(plugins)),

  /** What a plugin's text in the standing prompt comes to: nothing unless the owner named the plugin. */
  thoughtOf: (owner: string, text: string): string => bend.thought_of(owner, text),
  /** The base prompt with a plugin's thought after it. */
  minded: (base: string, thought: string): string => bend.minded(base, thought),
}
