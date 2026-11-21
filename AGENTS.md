# AGENTS.md

A map of wizardry for agents working on it. Read this before touching the code; it exists because
every fact in it was once learned the expensive way.

Note: wizardry runs Pi with `--no-context-files`, so sessions never see this file on their own —
inside a session, retrieve it with the `cordis_map` action, which reads the AGENTS.md shipped next
to the running install. The short manual for writing plugins in-session is the `shape` text in
`bend/core.bend`, shown by `cordis_inspect`. When the plugin API changes, update all three.

## What this is

**Pi on Cordis.** `boot()` builds a Cordis root context; the action registry, the plugin loader,
the fs/shell tools and Pi itself are plugins on it. A plugin's only route to the agent is
`ctx.actions.register(...)`: plugins add nothing to the system prompt and get no hooks into the
agent's turn. Actions that change the agent (`become`, `focus`, `think`) exist but are never
applied for it. Nothing asks for approval; `gate` is an optional plugin.

## Which copy runs

The same repo exists in up to three places, and confusing them wastes real time:

- **Your working clone** (this one). You edit, test and commit here.
- **The install on PATH.** `install.sh` clones into `~/.wizardry/app` and links `~/.local/bin`, but a
  clone run through `npm link` (or a global npm install) takes precedence. `which wizardry` and
  `readlink` on it tell you which copy a session actually runs; that copy is a git clone and is
  rebuilt in place by the updater.
- **`~/.wizardry` (`$WIZARDRY_HOME`)** is data, not code: `plugins/`, `plugins.json`, `sessions/`,
  `update.log` — plus the installer's `app/` clone.

**Pushing to `origin/main` is deploying.** The `update` plugin checks on every start, on every
`task/end`, and periodically while open; it rebuilds the installed copy and an open session
restarts itself onto the new code as soon as the agent is idle (`restartWhenIdle` in `src/pi.ts`,
the re-exec in `src/bin.ts`). Working clones are updated too, with unpushed commits rebased on top
and uncommitted changes carried along. `wizardry update off` stops all of it.

## The old name

wizardry was called izardry until November 2026. `adoptOldName` in `src/boot.ts` carries an old
install over on its first start (`~/.izardry` becomes `~/.wizardry` with a link left behind, and a
`wizardry` command appears beside `izardry`), and `IZARDRY_HOME`, `IZARDRY_NO_UPDATE`,
`IZARDRY_HANDOFF` and the `izardry.ref` git setting are still read. Nothing else should say
izardry; a working clone may still sit in a directory of that name.

## Source map

Read in this order:

| File | Owns |
|---|---|
| `bend/core.bend` | Everything wizardry decides, computes or says, in Bend: which plugins load and what switching one off or on writes down, how the command line splits, what a restart carries over and when it happens, how calls and results read, the header's layout and the cap's frames and colors, what `focus` leaves active, what `update` and rtk lead to, where wizardry's directory is, and every message and help text |
| `LAWS.bend`, `PROOF.bend` | What must hold of those decisions for every input, and the proofs |
| `core/core.mjs` | The compiled Bend, committed. Never edit it; `npm run core` writes it |
| `src/core.ts` | The only importer of the compiled Bend: arrays in, arrays out, no decisions |
| `src/*.ts` below | The host: calls into Pi, Cordis and Node, acting on what Bend answered. Nothing here decides or computes |
| `src/boot.ts` | Building the Cordis root: `Actions`, `Plugins`, the builtin set, plugin directories |
| `src/actions.ts` | The `Action` type, `ActionEnv` (`{ cwd, signal, update, pi }`), the registry, action wraps, and the `action/*` events |
| `src/pi.ts` | The `Pi` service: hosts Pi as an extension, declares actions as tools, slash commands, restart handoff, the `pi/*` and `task/end` events |
| `src/plugins.ts` | Loading/unloading plugin files (jiti), plugin shapes (`normalise`), persistence in `plugins.json` |
| `src/bin.ts` | CLI: arg split between wizardry and Pi, session dir, restart-on-exit |
| `src/look.ts` | Header, themes, how calls and results render |
| `defaults/*.js` | The shipped default plugins; `bend.js` is the example of a skill as an action |
| `defaults/division/` | The division default: `division.bend` (who may write what, whether a cut is made, what each agent is told, whether the halves fit), its `LAWS.bend` and `PROOF.bend`, the compiled `core.mjs`, and `index.js`, which starts the agents |
| `defaults/memory/` | The memory plugin, copied in whole from its own repository (see below). Never edit it here |
| `src/plugins/*.ts` | The builtins; `rtk.ts` is the example of wrapping another plugin's action, `update.ts` of `task/end` and slash commands |

Types for embedding are exported from `src/index.ts`.

## The Bend core

**Bend is the default here: anything in this repo that can be written in Bend is written in Bend**
(https://bend-lang.com, `bend guide`). That is the owner's standing rule, not a preference. Before
adding a line of TypeScript or JavaScript, ask whether Bend can express it, and if it can, it goes
in `bend/core.bend` (or a default's own `.bend` file) with a one-line crossing in `src/core.ts`.

What Bend can express, and so holds: every decision; every computation on text, lists and numbers
(parsing, formatting, layout, filtering, choosing); every text wizardry composes for the user or
the agent, the help and the error messages included; and the laws and proofs about all of it.

What stays TypeScript or JavaScript, and why, so that nobody has to work it out again:

- **Calls into Pi, Cordis, pi-tui, jiti and Node**, and the objects those take (tool schemas,
  action descriptions handed to `register`, event listeners, timers, child processes, files).
  Bend cannot call JavaScript, and only Bend's pure defs can be called from it.
- **Reading JavaScript values Bend has no type for**: `typeof`, optional fields, JSON of unknown
  shape, a function's source, an `Error`. The host turns them into text, numbers and lists; Bend
  takes it from there.
- **A guard on asking a library something** (`piCtx?.isIdle()` only when it could matter). What
  is done with the answer is Bend's.
- **`defaults/bend.js`**: one file a user copies and edits, whose whole work is finding a binary
  and running it.
- **`defaults/memory/`**: built in its own repository, where its decisions are already Bend.
- **The updater's shell script (`SCRIPT` in `src/plugins/update.ts`) and `install.sh`**: they are
  git, npm and the file system from end to end, and they are how every install repairs itself, so
  they stay in the one language every machine runs without a build.
- **The tests**: `node:test` drives them, and they check Bend against what it replaced.

If you find TypeScript that decides or computes and is not on this list, it is a leftover: move it.

- **A new decision goes in `bend/core.bend`**, with a one-line crossing in `src/core.ts`. If a
  rule must hold for every input, state it in `LAWS.bend` and prove it in `PROOF.bend`.
- **`npm run core`** runs `bend PROOF.bend` and recompiles `core/core.mjs`. Run it after every edit
  to a `.bend` file and commit the result: `npm run build` does not need Bend, so installs without
  it keep updating. `npm test` fails when `core/core.mjs` is stale or a proof is open.
- **Run `bend PROOF.bend` before committing.** It must print ALL PROOFS CHECK. A law is changed
  only when the rule changes, never to get a proof through. `bend PROOF.bend --verdict` rechecks
  with the kernel proven in Lean (`~/.elan/bin` on PATH; `npm test` runs it when Lean is there).
- **How the proofs are written.** `%e : P` needs the goal to be `P` with `e`'s right side at `_`,
  and leaves `P` with its left side there: to put a hypothesis `x == v` to use, rewrite with
  `Equal.sym` of it. To split on a computed Bool, pass it to a `_step` helper with `{==}` as the
  proof that it is what it is. `same` and `alike` in PROOF.bend say a name equals itself and that
  names which compare equal are the same name; every law about one name among others rests on them.
  A law's `for` needs `+` when its proof uses the value twice.
- **Loops over text are tail calls with an accumulator.** The JavaScript target turns a tail call
  into a loop and anything else into real recursion, which overflows the stack near ten thousand
  characters. Lists of names (plugins, actions, arguments) are short and recurse plainly.
- `test/core.test.mjs` runs each def against the TypeScript it replaced on generated inputs.
  `test/libraries.test.mjs` pins what wizardry counts on Cordis, Pi, pi-tui and jiti to do, since no
  proof reaches them: when one fails after an upgrade, the library changed.

## Intrinsic and default plugins

Two classes, and which one a plugin belongs to decides where it lives:

- **Intrinsic**: part of the wizardry system. The builtins in `src/plugins/*.ts`, shipped and
  updated with this repo.
- **Default**: not intrinsic. A choice that comes switched on and can be changed or removed without
  touching wizardry. Defaults live in two places:
  - `defaults/` in this repo: shipped to every install (the `bend` skill, `memory`, `division`). Loaded at boot by
    `Plugins.boot`; a file of the same name in a plugin directory is loaded instead, and
    `plugin_unload <name>` with `persist: true` switches one off.
  - `$WIZARDRY_HOME/plugins/`: this machine only (a default model). Edit the
    file to change it, delete it to remove it. `$WIZARDRY_HOME/plugins/README.md` lists them.

  wizardry must work the same without any default, and nothing in `src/` may depend on one. If what
  a default relies on is missing (a binary, a worker), it stays out of the way.

When asked to add something "as a default", it goes in `defaults/` if every install should get it
and in `$WIZARDRY_HOME/plugins/` if it is for this machine. Never into `src/`.

### The division default

`defaults/division/` cuts a large task in two and runs each half as its own headless wizardry, in
the same directory, at the same time. Unlike memory it is built here: edit `division.bend`, run
`npm run core`, commit `core.mjs` with it. Its proofs import wizardry's own (`../../PROOF.bend`),
so a lemma renamed there is renamed here too.

- A half learns its place from `WIZARDRY_DIVISION` (root, depth, name, owned files, laws, check).
  In a half, an `action/before` listener refuses `write` and `edit` outside the owned files. `bash`
  is not fenced: the ownership is a rule the agent is told and the write tools enforce, not a sandbox.
- A half unloads `memory`: what it is told is not something the user said.
- `division_split` blocks until both halves exit, then runs the check. Halves are started with
  `-p --no-session`, on the model and thinking level the user chose with `/division` (kept in
  `$WIZARDRY_HOME/division.json`), and otherwise on the calling session's.
- The trial in `test/division.test.mjs` uses a fake agent (`config.agent`); a real one needs a model.

### The memory default

`defaults/memory/` is built in its own repository, https://github.com/Pomidium/wizardry-memory
(private): `memory.bend` holds its decisions, `LAWS.bend` and `PROOF.bend` what is proven of them,
`plugin/` what ships. To change it, change it there, run `npm run core && npm test`, then
`npm run ship -- <this checkout>`, which replaces `defaults/memory/` with `plugin/` (`index.js`,
`store.js`, and the compiled Bend, `core.mjs`). Commit both repositories.

- Its store is `$WIZARDRY_HOME/memory/memory.db` (SQLite through `node:sqlite`, no worker), and its
  settings `$WIZARDRY_HOME/memory/config.json`: a shipped default cannot be given a config through
  `plugins.json`, because the persisted entry is skipped once the default has loaded the same file.
- It is the one plugin that reaches the agent other than through an action: it answers Pi's
  `session_before_compact` with a summary made of its observations (`api.on(...)` on the API that
  `pi/ready` and `pi/session-start` hand out, undone on unload). That was a decision, not a
  precedent: a plugin still adds nothing to the system prompt.
- It writes `memory:start`, `memory:observed` and `memory:switch` custom entries to the session,
  which is how what was observed follows a branch through `/tree`.
- Never point `--session` at the file of a session that is open: a second process appends to it.
  When a test needs a real session, copy the file first.

## Cordis rules that bite

These are the failure modes that cost an agent an hour; all are now covered by tests or events:

- **`ctx.effect(setup)` runs `setup` immediately** and keeps its *return value* as the disposer for
  unload. Passing `() => cleanup` runs the cleanup at once and undoes your setup — the single most
  expensive mistake made here. `Actions.register` shows the right shape.
- **Services come through a tracing proxy.** Reading a method from `ctx.pi` gives a bound copy;
  property writes can land on an ephemeral shadow; identity comparisons lie. Call methods and read
  properties — never patch, subclass, store or compare services. If you think you need to
  monkey-patch a service, what you actually need is an event: add it (see how `pi/ready` and
  `pi/session-start` are declared and emitted in `src/pi.ts`).
- **Events** are typed in `declare module '@deepseek-ai/cordis' { interface Events }` blocks
  (`src/actions.ts`, `src/pi.ts`). Emit on `ctx.root`, listen with `ctx.on` from any plugin context.
- **`inject` is declarative.** A plugin whose injected service nothing provides sits `[pending]`
  rather than failing; it starts when the service appears. `self` injecting `pi` is the example.
- **The plugin's fiber owns everything it registers.** Unload removes actions, commands, listeners
  and effect disposers. Leaks across unload are a bug.

## The Pi surface

- `ctx.pi.api` is Pi's `ExtensionAPI` once `pi/ready` has fired: `setModel`, `setThinkingLevel`,
  `getActiveTools`/`setActiveTools`, `registerCommand`, `on(...)`, `appendEntry`.
- In an action, `env.pi` is the session's `ExtensionContext`: `modelRegistry`, `ui`, `cwd`, `mode`,
  `sessionManager`, `isIdle()`.
- Both are typed in `node_modules/@earendil-works/pi-coding-agent/dist/core/extensions/types.d.ts`.
  Read the types before assuming a method or event exists; Pi's own docs are not load-bearing here.
- wizardry switches off Pi's builtin tools, extensions, skills, prompt templates and context files
  (`src/bin.ts`); what the agent can do comes only from Cordis plugins.

## Developing and debugging

```
npm test                          # builds dist/, then runs test/*.test.mjs
npm run core                      # after editing a .bend file: check the proofs, recompile core/core.mjs
node dist/bin.js -p "hi"          # run from source
WIZARDRY_HOME=$(mktemp -d) node dist/bin.js   # isolated from your real plugins and sessions
```

- The tests boot a real Cordis root *without* Pi (a model is the only thing they can't have) and
  drive it through `actions.invoke`; `Pi.attach` is tested with a fake `ExtensionAPI`. New plugin
  behavior should get a test in that style.
- Smoke-test a real session headlessly: `wizardry -p "Reply with exactly: ok"`, then read the newest
  `~/.wizardry/sessions/*.jsonl` — `model_change` and `thinking_level_change` entries tell you what
  the session actually ran on.
- A plugin that fails to load is reported on stderr (`wizardry: plugin failed to load: ...`) and
  nothing it registered is left behind. From inside a plugin, log to a file; remember the restart
  path re-execs the process, so log pids if a process count is in doubt.
- `dist/` and `node_modules/` are gitignored. Never edit `dist/`; `npm run build` regenerates it.

## Commit style

Short, imperative, lowercase subjects that state the user-visible behavior
("Say what a session restarted onto"). One behavior per commit; the updater quotes these messages
to the user.

**Push every finished change.** Once a change is tested and committed, push it to `origin/main`
without asking: the owner wants every update deployed as it is done, not left in the clone.
