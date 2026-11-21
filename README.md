# wizardry

A CLI agent: **Pi on Cordis**. Cordis is the bottom layer, Pi is a plugin loaded onto it, and
everything the agent can do is a tool call it chooses to make.

## Install

```
curl -fsSL https://raw.githubusercontent.com/Pomidium/wizardry-releases/main/install.sh | sh
```

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
wizardry --gate               # opt out of YOLO: ask before bash, write, edit, plugin changes
wizardry --plugin ./x.ts      # load a plugin for this run
```

Every other option goes to Pi unchanged (`--model`, `--thinking`, `-c`, `-r`, `--mode json`, ...).
wizardry uses Pi's logins and models; `wizardry auth login` is Pi's `auth` command.

wizardry starts with its own header, an ASCII wizard's cap, and its own blue themes: `wizardry` on a
dark terminal and `wizardry-light` on a light one (`themes/`, logo and header in `src/look.ts`).
`--use-theme <name>` picks another theme for a run, for example `--use-theme system`.

## The idea

- **Cordis is the lowest level.** `boot()` creates a Cordis root context. The action registry, the
  plugin loader, the file and shell tools, and Pi itself are all plugins on it.
- **Every plugin is a tool call.** A plugin's only route to the agent is `ctx.actions.register(...)`.
  Plugins add nothing to the system prompt and get no hooks into the agent's turn, so the
  agent is not steered by them. It sees a list of actions and picks.
- **An action is something the agent does, not something it is.** Actions that change the agent
  (`become`, `focus`, `think`) exist, and are never applied for it.
- **You state the outcome.** The system prompt is seven lines (`basePrompt` in `src/pi.ts`): who it
  is, that tools are options, the working directory and the date. Pi's own tools, extensions,
  skills, prompt templates and `AGENTS.md` loading are switched off.
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
user), `pi/ready` (Pi's extension API is live) and `pi/session-start` (a session began, a resumed
one counts). `ctx.actions.wrap(name, { note, properties, around })` puts a layer around another
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

- `division`, for large tasks only: the agent cuts the task in two, writes Bend laws at the cut,
  and hands each half to its own agent; both work at the same time in the same directory, and a
  half that is still large cuts itself again. Each half owns its own files and may count on the
  other's laws before they are proven. `bend PROOF.bend` then says whether the pieces fit. A cut
  whose halves are under 15 minutes of work is refused, since an agent costs more to start than
  that saves. It is proven ([`defaults/division/LAWS.bend`](defaults/division/LAWS.bend)) that two
  halves can never write the same file, that a half never owns more than the agent that cut, and
  that every law has one prover. `/division model` and `/division thinking` choose what those
  agents run on (a list to pick from, or name it: `/division model provider/id`,
  `/division thinking low`; `same` follows the session again). Other settings go in
  `~/.wizardry/division.json` (`chunkMinutes`, `depth`, `timeoutMinutes`, `agent`); every cut is logged in
  `~/.wizardry/division/runs.jsonl`, with how long each half took.

Switch a default off with `plugin_unload` and `persist: true`; change one by putting a file or
folder of the same name in `~/.wizardry/plugins/`.
 Sessions are stored in `~/.wizardry/sessions/`. Set `WIZARDRY_HOME` to move all of it.

## The Bend core

In this repo, anything that can be written in Bend is written in Bend. wizardry's own decisions,
computations and texts are in [Bend](https://bend-lang.com) in [`bend/core.bend`](bend/core.bend):
which plugins load at start and what switching one off or on writes down, how the command line is
split between wizardry and Pi, what a restart carries over, how calls and results are shown, what
`focus` leaves in front of the agent, what `update` was asked for, and the wizard's cap, frame by
frame. The host around them stays TypeScript, because Pi, Cordis and plugins are JavaScript.

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
