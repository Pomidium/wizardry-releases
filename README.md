# wizardry

A CLI agent: **Pi on Cordis**. Cordis is the bottom layer, Pi is a plugin loaded onto it, and
everything the agent can do is a tool call it chooses to make.

## Install

```
curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install.sh | sh
```

Or with everything the default plugins can use, which is about 700 MB more:

```
curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install-full.sh | sh
```

That is the same installer with `WIZARDRY_FULL=1`: it adds [Bend](https://bend-lang.com) for the
`bend` plugin (in `~/.bend`), and [jacobian](https://github.com/morluto/jacobian) and
[hillclimb](https://github.com/rebase-energy/hillclimb) for `defintire`, both inside
`~/.wizardry/tools` with a Python of their own (installed by [uv](https://docs.astral.sh/uv/),
which it adds to `~/.local/bin` if missing). Run it over a plain install to add them later.

This repo is private; anyone can still install. Every push to `main` is copied (the tree, not its
history) to the public [Pomidium/wizardry-releases](https://github.com/Pomidium/wizardry-releases)
by `.github/workflows/mirror.yml`, and the installer and the updater fetch from there. The
workflow pushes with a deploy key held in this repo's `RELEASES_DEPLOY_KEY` secret.

It needs git and Node 22.19 or newer. It clones into `~/.wizardry/app`, builds, links `wizardry` into
`~/.local/bin`, and installs [rtk](https://github.com/rtk-ai/rtk) if it is missing
(`WIZARDRY_SKIP_RTK=1` to skip). Run it again to update. `WIZARDRY_HOME`, `WIZARDRY_BIN_DIR`,
`WIZARDRY_REPO` and `WIZARDRY_REF` change where things go and what is installed.

## Updates

wizardry keeps itself current whenever it can. On every start, every time the agent finishes a task,
and every fifteen minutes while a session sits open, it checks the repo in the background and builds
a new version there. An open session then moves onto it as soon as the agent is idle: it starts
again in place with the same conversation, loaded plugins and half-typed prompt, and says what it
updated to (`wizardry: updated to 9493566 (...)`). A version that fails to build is rolled back and
not tried again; `~/.wizardry/update.log` has the last run.

In a session:

```
/update        check and update now
/update off    stop automatic updates
/update on     bring them back
```

The same three exist outside one as `wizardry update`, `wizardry update off` and `wizardry update on`,
and `WIZARDRY_NO_UPDATE=1` skips updates for one run. The switch is the `update` plugin, so the
agent can also turn it off with `plugin_unload update` and `persist: true`.

The copy the installer made (`~/.wizardry/app`) follows the ref it was installed from. A clone you
work in and run through `npm link` is updated too, with your work carried along: commits you have
not pushed are rebased onto the new version, and uncommitted changes are set aside and put back on
top. If any of it does not apply cleanly the clone is returned to exactly how it was, and it is not
touched during a merge or rebase or within two minutes of an edit. `/update` says why when it
holds back.

## Use

```
wizardry                      # interactive session
wizardry -p "outcome"         # run once and print
wizardry plugins              # what is loaded, and the actions each plugin provides
wizardry update [on|off]      # update now, or switch automatic updates
wizardry export [folder]      # copy every conversation and memory to a folder you keep
wizardry delete <what>        # say what would be deleted; add --yes to export, then delete
wizardry --gate               # opt out of YOLO: ask before bash, write, edit, plugin changes
wizardry --plugin ./x.ts      # load a plugin for this run
```

Every other option goes to Pi unchanged (`--model`, `--thinking`, `-c`, `-r`, `--mode json`, ...).
`wizardry auth login` signs in: it is Pi's `auth` command, run on wizardry's own logins.

In a session, `/default` makes its setup the one new sessions start with: its model and thinking
level, and the plugins loaded now (one loaded for this session loads from then on, one unloaded
stays off). `/default-agent` does the same for the agents it deploys (see `division` below).

wizardry starts with its own header, an ASCII wizard's cap, and its own blue themes: `wizardry` on a
dark terminal and `wizardry-light` on a light one (`themes/`, logo and header in `src/look.ts`).
`--use-theme <name>` picks another theme for a run, for example `--use-theme system`.

## Kept apart

wizardry is one directory, `~/.wizardry` (`WIZARDRY_HOME` moves all of it), and nothing outside it
is read or written:

| In `~/.wizardry` | What |
|---|---|
| `app/` | the program, as the installer cloned it |
| `pi/` | logins, settings and model lists of the Pi that wizardry runs |
| `sessions/` | every conversation |
| `memory/` | everything remembered |
| `plugins/`, `plugins.json` | your plugins, and which are switched on or off |
| `tools/`, `bin/` | programs installed for plugins when you ask for them (jacobian, hillclimb); not exported, since they can be installed again |

**Apart from Pi's own setup.** wizardry ships the Pi it runs and points it at `~/.wizardry/pi`,
whatever `PI_CODING_AGENT_DIR` says. A Pi installed on the same machine (`~/.pi/agent`) is another
program with another setup: its extensions, packages, skills, prompt templates, themes, MCP
servers and settings never reach a wizardry session, and neither does a project's `.pi` folder.
Pi's own update notice is off too, since updating that Pi does not change the one wizardry runs.
The first time, the logins (`auth.json`, `models.json`) and the settings that say which model is
talked to and how it is reached are copied over, once, and wizardry says so; nothing else comes
along and Pi's directory is only read. From then on the two sign in separately: a login made
in one is not made in the other, and where a provider replaces a login each time it is renewed, the
copy the other holds stops working and that one signs in again. A command the agent runs sees the
environment wizardry was started in, so `pi` run from a session is still your Pi.

**Export.** `wizardry export` copies every conversation and memory into
`~/wizardry-export-<day>` (or the folder you name, which must be new or empty: nothing is
overwritten). Conversations come from wizardry and from Pi's own setup, each twice: the `.jsonl`
exactly as it was kept, which `wizardry --session <file>` carries on, and a `.md` beside it to
read. Memories come as the store itself (`memory.db`), as data and as text. A plugin that keeps
data exports its own folder when the `export` event reaches it; a folder nobody exported is
copied as it is. Logins are not exported.

**Delete.** `wizardry delete <what>` says what would go and how big it is, and deletes nothing.
With `--yes` it exports first (`--to <folder>` says where, `--no-export` skips it) and deletes
only once the export is kept:

| `<what>` | Removes |
|---|---|
| `conversations` | `~/.wizardry/sessions` |
| `memories` | `~/.wizardry/memory` |
| `old` | Pi's own setup: `~/.pi/agent` with its logins, settings, conversations, extensions and the `pi` program, the `pi` command that points into it, and `~/.pi` if that leaves it empty. wizardry keeps working: it has its own logins |
| `all` | all of `~/.wizardry`, and the `wizardry` command when it points into it |

It is proven that nothing is deleted without `--yes` or after an export that failed, that what is
deleted never includes your home directory or the export, and that deleting the old setup never
touches wizardry.

## The idea

- **Cordis is the lowest level.** `boot()` creates a Cordis root context. The action registry, the
  plugin loader, the file and shell tools, and Pi itself are all plugins on it.
- **Every plugin is a tool call.** A plugin's only route to the agent is `ctx.actions.register(...)`.
  Plugins add nothing to the system prompt and get no hooks into the agent's turn (with one
  exception, `defintire`, which keeps a few lines there: see below), so the
  agent is not steered by them. It sees a list of actions and picks.
- **An action is something the agent does, not something it is.** Actions that change the agent
  (`become`, `focus`, `think`) exist, and are never applied for it.
- **You state the outcome.** The system prompt is seven lines (`basePrompt` in `src/pi.ts`): who it
  is, that tools are options, the working directory and the date. Pi's own tools, extensions,
  skills, prompt templates, themes, MCP servers and `AGENTS.md` loading are switched off, and it
  reads nothing from `~/.pi` or a project's `.pi` (see Kept apart).
- **YOLO by default.** Nothing asks for approval. `gate` is a plugin like any other.

## Builtin plugins

| Plugin | Actions |
|---|---|
| `pi` | none. Hosts Pi and declares every registered action to the model as a tool |
| `fs` | `read`, `write`, `edit`, `grep`, `find`, `ls` (Pi's implementations) |
| `shell` | `bash` |
| `cordis` | `cordis_inspect`, `plugin_load`, `plugin_unload`, `plugin_reload` |
| `self` | `become` (rewrite its own standing instructions), `focus` (choose which actions are in view), `think` (reasoning level) |
| `rtk` | none. Wraps `bash` so commands [rtk](https://github.com/rtk-ai/rtk) knows run through it and return condensed output |
| `update` | none. Keeps wizardry current in the background when a task finishes (see Updates) |
| `gate` | none, not loaded by default. Asks the user before selected actions run |

`rtk` is the one plugin that changes another plugin's action, and it does so in the open: the
`bash` description says its output is condensed, and `bash` gains a `raw` parameter the agent sets
to get a command run exactly as written. All rewrite rules are rtk's own (`rtk rewrite`). If rtk is
not installed the plugin fails to load with a one-line notice and `bash` is unchanged;
`plugin_unload rtk` with `persist: true` turns it off for good.

The agent can write a plugin file, `plugin_load` it, and use the new action in the same session.

## Writing a plugin

The smallest plugin needs no imports:

```js
export const name = 'dice'
export const actions = [{
  name: 'dice',
  description: 'Roll an N-sided die.',
  parameters: { type: 'object', properties: { sides: { type: 'number' } }, required: ['sides'] },
  execute: ({ sides }, env) => `d${sides}: ${1 + Math.floor(Math.random() * sides)}`,
}]
```

For lifecycle and services, export `apply(ctx, config)` (or a default function or class) and use the
Cordis context. `actions` is always injected.

```ts
import type { Context } from 'wizardry'

export const name = 'audit'
export function apply(ctx: Context) {
  ctx.on('action/after', (action, params, outcome) => { /* log it */ })
  ctx.actions.register({ name: 'audit_tail', description: '...', execute: () => '...' })
}
```

Everything a plugin registers is owned by its Cordis fiber and removed when the plugin is unloaded.
One Cordis rule bites: `ctx.effect(setup)` runs `setup` immediately and keeps its *return value* as
the cleanup on unload, so pass a function that does the setup and returns the disposer — passing the
disposer itself undoes the setup at once.

In the terminal a call is named after its plugin, then the action: `plugin_load` from `cordis` reads
**cordis plugin load**, `subagent_create` from a `subagent` plugin reads **subagent create**, with its
arguments as `key: value` beside it and the first lines of the result below (ctrl+o shows both in
full). Pi's own tools keep their names (`read`, `write`, `edit`, `$` for bash). To name a call after
a workflow instead, give the action a `title`, for example `title: 'code review'`. The title is only
what the user sees; the agent always calls the action by `name`.

A plugin that injects `pi` can also give the user a slash command with
`ctx.pi.command('name', { description, words, run(args, piCtx) })`. Commands are the user's: the
agent does not see them.

Events: `action/registered`, `action/unregistered`, `action/before` (return a string to refuse the
call), `action/changed`, `action/after`, `task/end` (the agent finished and is waiting for the
user), `pi/ready` (Pi's extension API is live), `pi/session-start` (a session began, a resumed
one counts) and `export` (`(dir, wrote)`: the user asked for a copy of everything; a plugin that
keeps data in `~/.wizardry/<name>/` writes it to `<dir>/<name>/` and calls `wrote` with one line
saying what is there). `ctx.actions.wrap(name, { note, properties, around })` puts a layer around another
plugin's action, as `rtk` does. Services: `ctx.actions`, `ctx.plugins`, `ctx.pi`. They come through
a tracing proxy: calling their methods is all you should do with them — don't patch, subclass or
store them.

Per-session choices a plugin makes for the user belong on `pi/session-start`. A plugin that sets
wizardry's default model, leaving Pi's own settings alone:

```js
export const name = 'default-model'
export const inject = ['pi']
export function apply(ctx) {
  ctx.on('pi/session-start', async (api, piCtx) => {
    const model = piCtx.modelRegistry.find('radius', 'claude-fable-5-2')
    if (model) await api.setModel(model)
    api.setThinkingLevel('medium')
  })
}
```

Plugins load from `~/.wizardry/plugins/`, `./.wizardry/plugins/`, and the list in
`~/.wizardry/plugins.json`, which `plugin_load` / `plugin_unload` write when called with
`persist: true`.

A few default plugins ship in [`defaults/`](defaults) and are on for everyone:

- `bend`, the [Bend 2](https://bend-lang.com) skill: its rules for working in Bend are in the `bend`
  action's description, and calling it returns the language guide (install Bend with
  `curl -fsSL https://bend-lang.com/install.sh | sh`). It also makes Bend the agent's default
  language: it writes in Bend whatever Bend can express, and keeps another language for calls
  into libraries outside Bend, for a codebase already in one, or when you ask for one.
- `memory`, what the agent remembers. A small model turns the session into short timestamped
  observations as it goes; when the context is compacted they take the place of the messages they
  were made from, and the oldest are folded into topics kept per project. Everything is in one
  SQLite file, `~/.wizardry/memory/memory.db`, and the agent recalls it with `mem_search`,
  `mem_timeline` and `mem_get_observations`. `/memory` shows what it holds, `/memory off` stops it
  for a session, and `<private>...</private>` in a message is never remembered. Settings go in
  `~/.wizardry/memory/config.json` (for example `{"model": "radius/claude-haiku-5-5"}`). It joins
  [pi-observational-memory](https://github.com/amosblomqvist/pi-observational-memory) and
  [claude-mem](https://github.com/thedotmack/claude-mem), with its decisions written and proven in
  Bend.

- `division`, a way for the agent to deploy agents: it cuts a task into parts, as many as the
  task has, and hands each to its own agent; all work at the same time in the same directory,
  and a part may cut again. Each part owns its own files, and what crosses between parts is said
  beforehand, best as Bend laws that one part proves and the others count on before the proof
  exists; a part with no law is held by the check alone, and a part with no file only reads and
  reports. It is a way of working, not a set of limits: how many parts, how large, and whether to
  cut at all are the agent's to judge. A cut is refused only when it would let agents undo each
  other. It is proven ([`defaults/division/LAWS.bend`](defaults/division/LAWS.bend)) that no path
  ever has two agents that may write it, that a part never owns more than the agent that cut,
  that every law has one prover, that cutting ends, and that nothing else is asked of a cut.
  `/default-agent` makes this session's model and thinking level what those agents run on
  (`/default-agent provider/id` names a model, `/default-agent same` follows each session again);
  `/division` shows the choice and sets either alone. Other settings go in
  `~/.wizardry/division.json` (`depth`, `timeoutMinutes`, `agent`); every cut is logged in
  `~/.wizardry/division/runs.jsonl`, with how long each part took.

- `defintire`, which turns anything, mathematical or not, into an explicit definition and then into
  something that can be improved. `defintire_define` keeps a definition: the question it answers,
  its objects and their types, what is left undefined, its axioms in notation (those that are
  choices rather than findings are marked stipulated), examples and non-examples, and the same
  in Bend where Bend can say it. Criteria tie numbers to it, each one **exact** (a command
  computes the quantity), **proxy** (a command computes a stand-in) or **judged** (a model reads
  the candidate against a rubric), and may be a **gate**, standing for an axiom: the score is
  never higher than where the candidate stands on a gate. `defintire_measure` scores a candidate out of 100 by those
  criteria and nothing else, and says whether the score is verified (every criterion exact),
  estimated or partial. `defintire_rank` compares candidates two at a time and keeps an Elo
  rating for each, for what has no absolute number worth trusting. `defintire_climb` sends
  agents (on your `/default-agent` model) to improve a file: every attempt is measured, only one
  that scores strictly higher is kept, and the file changes only for something better. It is
  proven ([`defaults/defintire/LAWS.bend`](defaults/defintire/LAWS.bend)) that a score resting on
  a proxy or a judgment is never called verified, that no reading scores past the best, that a
  comparison only moves points between the two compared, and that a climb never goes downhill.
  It draws on [hillclimb](https://github.com/rebase-energy/hillclimb) (a verifier scores, the
  best is kept), [Creative-Intelligence](https://github.com/DeepMathLLM/Creative-Intelligence)
  (a concept is formed from the problem it answers, by counterexample and verification) and
  [jacobian](https://github.com/morluto/jacobian) (exact, typed mathematical operations), and
  includes no code of any; when hillclimb or jacobian is installed, the method says how to hand
  a long search to the one and exact quantities to the other. They are about 650 MB together with
  the Python they need, so they are not in the plain install: the full install (see Install) adds
  them, inside `~/.wizardry/tools`, and the method gives the same command for later. Definitions are kept in
  `~/.wizardry/defintire/`, so export and delete take them along. It is the one plugin let into
  the agent's head: while loaded it keeps a few lines in the standing prompt (at most 1200
  characters), a habit of saying what a thing is before working on it and the definitions kept.
  wizardry admits it by name, and it is proven that no other plugin can add anything there;
  `plugin_unload defintire` takes the lines out.

Switch a default off with `plugin_unload` and `persist: true`; change one by putting a file or
folder of the same name in `~/.wizardry/plugins/`.
 Sessions are stored in `~/.wizardry/sessions/`. Set `WIZARDRY_HOME` to move all of it.

## The Bend core

In this repo, anything that can be written in Bend is written in Bend. wizardry's own decisions,
computations and texts are in [Bend](https://bend-lang.com) in [`bend/core.bend`](bend/core.bend):
which plugins load at start and what switching one off or on writes down, how the command line is
split between wizardry and Pi, what a restart carries over, how calls and results are shown, what
`focus` leaves in front of the agent, what `update` was asked for, where Pi is pointed and what
comes over from its own setup, where an export goes and how a conversation reads in it, what
`delete` may remove and when, and the wizard's cap, frame by frame. The host around them stays TypeScript, because Pi, Cordis and plugins are JavaScript.

[`LAWS.bend`](LAWS.bend) states what must hold of those decisions for every input, and
[`PROOF.bend`](PROOF.bend) proves each law. Among them:

- **Plugins.** A plugin switched off is never loaded, stays off at every start, and comes back when
  switched on; switching one touches no other. A file in a plugin directory replaces the shipped
  default of its name, and everything not switched off does load. What the session runs on is
  never unloaded.
- **Calls.** Every call is shown under the name of its plugin (`subagent_create` reads
  "subagent create"), Pi's own tools keep theirs, and a title an action sets wins. An argument on
  the title line never passes 72 characters, and a collapsed result accounts for every line.
- **The command line.** Arguments that are not wizardry's reach Pi unchanged and in order; Pi always
  starts with its own tools, extensions, skills, templates and context files off; a theme you ask
  for is not overridden; a restart never resumes or opens a different session.
- **Kept apart.** Pi's directory is inside wizardry's and Pi is pointed at it whatever the
  environment says; Pi starts with theme discovery, MCP servers and project-local files off; of
  Pi's own settings nothing but the ones named comes over, and never packages, extensions, skills,
  prompt templates or themes; logins are never brought over onto a directory that is there.
- **Export and delete.** A conversation is exported inside the export's folder. Nothing is deleted
  without `--yes`, nor after an export that did not finish; what is deleted never includes your
  home directory or the export; and deleting the old setup removes nothing that is wizardry's
  directory, holds it, or is inside it.
- **The agent's tools.** `focus` can never be put away, what is taken up is there afterwards, and
  what is put away is gone. The standing prompt is the base prompt, and what the agent writes for
  itself only ever comes after it.
- **The caps.** Every frame is the same size as the plain cap, so nothing on screen moves when it
  twinkles, and every piece is drawn in one of four theme colors.

`bend PROOF.bend` checks the proofs; `bend PROOF.bend --verdict` checks them again with a small
kernel that has its own proof in Lean (it needs Lean 4.34: `elan toolchain install
leanprover/lean4:v4.34.0`). A proof says a decision is right for every input. It does not reach
Pi, Cordis, the file system or the updater's shell script: those are covered by the tests, which
boot a real Cordis root and pin what wizardry counts on each library to do.

The compiled core is committed, so building wizardry does not need Bend. Changing a `.bend` file does:
`npm run core` checks the proofs and recompiles it.

## Develop

```
npm install --ignore-scripts
npm test          # builds, then runs test/*.test.mjs
npm run core      # after editing a .bend file (needs bend)
npm link          # puts `wizardry` on PATH
```

Requires Node 22.19 or newer. [AGENTS.md](AGENTS.md) maps the framework for agents working on it:
which copy of the repo runs, what each file owns, and the Cordis rules that bite.
