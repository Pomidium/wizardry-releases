import { spawn, spawnSync } from 'node:child_process'
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, realpathSync, rmSync, statSync } from 'node:fs'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import type { Context } from '@deepseek-ai/cordis'
import { core } from '../core.js'

export interface UpdateConfig {
  /** The checkout to keep current. Default: the one this wizardry runs from. */
  app?: string
  /** Time between checks while a session sits open. Default fifteen minutes. */
  intervalMs?: number
}

/** Where the running wizardry lives: the directory holding package.json and dist/. */
export const APP_DIR = fileURLToPath(new URL('../..', import.meta.url))

/** Whether `app` is the checkout install.sh made in `home`, rather than a clone someone works in. */
export function managed(app: string, home: string) {
  try {
    return existsSync(join(app, '.git')) && realpathSync(app) === realpathSync(join(home, 'app'))
  } catch {
    return false
  }
}

/**
 * The update itself: fetch, and if there is something new, move to it, install and build. A build
 * that fails is rolled back to the commit it started from.
 *
 *   sh -c SCRIPT sh <app> <home> foreground|background install|clone
 *
 * An `install` is the installer's checkout: it follows the installed ref, as install.sh does.
 *
 * A `clone` is one someone works in, so their work comes along: commits that are not pushed are
 * rebased onto the new version and uncommitted changes are set aside and put back on top. If any
 * of it does not apply cleanly, the clone is returned to exactly the state it was in. It is not
 * touched while a merge or rebase is under way, or within two minutes of an edit to a changed file.
 *
 * A successful run records the new commit in <app>/.git/wizardry-built, which running sessions watch
 * for: they start again on the new code, in the same session, as soon as the agent is idle.
 * In the background a run also leaves one line in <home>/update-notice for the next start to show.
 */
export const SCRIPT = String.raw`
set -eu
APP=$1; HOME_DIR=$2; MODE=$3; KIND=$4
LOCK="$HOME_DIR/update.lock"
say() { printf 'wizardry: %s\n' "$1"; }
tell() { say "$1"; if [ "$MODE" = background ]; then printf '%s\n' "$1" > "$HOME_DIR/update-notice"; fi; }
# Work in progress is not news: only someone who asked hears why nothing happened.
skip() { if [ "$MODE" = foreground ]; then say "$1"; fi; exit 0; }
# Said once: the same commit is not tried again in the background.
giveup() { printf '%s\n' "$NEW" > "$HOME_DIR/update-failed"; tell "$1"; exit "$2"; }

# One updater at a time. A lock left by one that was killed goes after half an hour.
find "$LOCK" -maxdepth 0 -mmin +30 -exec rmdir {} \; 2>/dev/null || true
mkdir "$LOCK" 2>/dev/null || skip "another update is running"
trap 'rmdir "$LOCK" 2>/dev/null || true' EXIT

cd "$APP"
export GIT_TERMINAL_PROMPT=0
OLD=$(git rev-parse HEAD)
if [ "$KIND" = install ]; then
  git fetch --quiet --depth 1 origin "$(git config wizardry.ref || git config izardry.ref || echo main)"
  NEW=$(git rev-parse FETCH_HEAD)
else
  git symbolic-ref -q HEAD >/dev/null || skip "not updated: $APP is not on a branch"
  git rev-parse -q --verify '@{u}' >/dev/null 2>&1 || skip "not updated: the branch in $APP has no upstream"
  for busy in MERGE_HEAD CHERRY_PICK_HEAD REVERT_HEAD BISECT_LOG rebase-merge rebase-apply; do
    if [ -e "$(git rev-parse --git-dir)/$busy" ]; then skip "not updated: a merge or rebase is under way in $APP"; fi
  done
  git fetch --quiet
  NEW=$(git rev-parse '@{u}')
fi
SHORT=$(git rev-parse --short "$NEW")
if [ "$OLD" = "$NEW" ] || { [ "$KIND" = clone ] && git merge-base --is-ancestor "$NEW" "$OLD"; }; then say "up to date ($SHORT)"; exit 0; fi
if [ "$MODE" = background ] && [ "$(cat "$HOME_DIR/update-failed" 2>/dev/null || true)" = "$NEW" ]; then exit 0; fi

# npm may rewrite package-lock.json; any other edit to a tracked file is someone's work.
changed() { git status --porcelain --untracked-files=no | grep -v ' package-lock\.json$' || true; }
if [ -n "$(changed)" ]; then
  if [ "$KIND" = install ]; then giveup "not updated to $SHORT: $APP has local changes" 0; fi
  RECENT=$(git diff --name-only HEAD | while IFS= read -r file; do if [ -e "$file" ]; then find "$file" -mmin -2; fi; done)
  if [ -n "$RECENT" ]; then skip "not updated to $SHORT: files in $APP were edited in the last two minutes"; fi
fi

SHELVED=
shelve() { if [ -n "$(git status --porcelain --untracked-files=no)" ]; then git stash push --quiet; SHELVED=1; fi; }
unshelve() { if [ -n "$SHELVED" ]; then git stash pop --quiet --index >/dev/null 2>&1; SHELVED=; fi; }
# Back to the commit this run started from, with whatever was uncommitted on top again.
restore() { git rebase --abort >/dev/null 2>&1 || true; git reset --quiet --hard "$OLD"; unshelve; }
build() { npm install --ignore-scripts --no-audit --no-fund --loglevel=error && npm run --silent build; }

if [ "$KIND" = install ]; then
  git checkout --quiet --force --detach "$NEW"
else
  shelve
  if ! git rebase --quiet "$NEW" >/dev/null 2>&1; then
    restore
    giveup "not updated to $SHORT: your commits in $APP do not apply on top of it" 0
  fi
  if [ -n "$SHELVED" ] && ! git stash pop --quiet --index >/dev/null 2>&1; then
    restore
    giveup "not updated to $SHORT: your uncommitted changes in $APP do not apply on top of it" 0
  fi
  SHELVED=
fi

if build; then
  rm -f "$HOME_DIR/update-failed"
  printf '%s\n' "$NEW" > "$(git rev-parse --git-dir)/wizardry-built"
  tell "updated to $SHORT ($(git log -1 --format=%s "$NEW"))"
else
  if [ "$KIND" = install ]; then git checkout --quiet --force --detach "$OLD"; else shelve; restore; fi
  build || true
  giveup "update to $SHORT failed to build; still on $(git rev-parse --short "$OLD")" 1
fi
`

const kind = (app: string, home: string) => core.kindOf(managed(app, home))

/** Check for an update now and wait for it, printing what happened. Returns the exit code. */
export function updateNow(app: string, home: string) {
  mkdirSync(home, { recursive: true })
  return spawnSync('sh', ['-c', SCRIPT, 'sh', app, home, 'foreground', kind(app, home)], { stdio: 'inherit' }).status ?? 1
}

/** Check for an update now without blocking, and resolve with what the run said. */
export function updateQuietly(app: string, home: string) {
  mkdirSync(home, { recursive: true })
  return new Promise<{ code: number; said: string }>((resolve) => {
    const child = spawn('sh', ['-c', SCRIPT, 'sh', app, home, 'foreground', kind(app, home)], { stdio: ['ignore', 'pipe', 'pipe'] })
    let said = ''
    child.stdout.on('data', (chunk) => { said += chunk })
    child.stderr.on('data', (chunk) => { said += chunk })
    child.on('error', (error) => resolve({ code: 1, said: String(error.message) }))
    child.on('exit', (code) => resolve({ code: code ?? 1, said: said.trim() }))
  })
}

/**
 * `/update`: check and update now. `/update on` and `/update off`: the switch for automatic
 * updates, which is the `update` plugin being loaded or not. Registered by `cordis`, which is
 * always there, so that the switch still exists while updates are off.
 */
export function updateCommand(ctx: Context) {
  ctx.root.get('pi')?.command('update', {
    description: 'Update wizardry now; "/update off" and "/update on" switch automatic updates',
    words: ['on', 'off'],
    async run(args, piCtx) {
      const plugins = ctx.root.get('plugins')!
      // What the word after /update asks for is decided in Bend, as is what the switch then does.
      const asked = core.updateAsked(args)
      if (asked === 'Unclear') return piCtx.ui.notify('Usage: /update, /update on, /update off', 'warning')
      if (asked !== 'Now') {
        const act = core.switchAct(asked === 'On', plugins.list().some((plugin) => plugin.name === 'update'))
        if (act === 'Unloads') await plugins.unload('update', { persist: true })
        if (act === 'Loads') await plugins.load('update', undefined, { persist: true })
        return piCtx.ui.notify(core.switchSaid(asked === 'On'), 'info')
      }
      if (!existsSync(join(APP_DIR, '.git'))) return piCtx.ui.notify(core.said.notACheckout(APP_DIR), 'warning')
      piCtx.ui.notify('Checking for an update...', 'info')
      const { code, said } = await updateQuietly(APP_DIR, plugins.home)
      const line = core.updateLine(said)
      if (code === 0 && core.updated(line)) ctx.root.get('pi')?.restartWhenIdle(core.carriedOn(line))
      else piCtx.ui.notify(core.updateSaid(line), code === 0 ? 'info' : 'error')
    },
  })
}

/** Start a check that outlives this process. Its output goes to <home>/update.log. */
export function updateInBackground(app: string, home: string) {
  mkdirSync(home, { recursive: true })
  const log = openSync(join(home, 'update.log'), 'w')
  try {
    const child = spawn('sh', ['-c', SCRIPT, 'sh', app, home, 'background', kind(app, home)], { detached: true, stdio: ['ignore', log, log] })
    child.unref()
    return child
  } finally {
    closeSync(log)
  }
}

/**
 * Keeps wizardry current. On every start, every time the agent finishes a task, and every fifteen
 * minutes in between, it checks the repo in the background and builds a new version there. An open
 * session then starts again on the new code as soon as the agent is idle, with the same
 * conversation, plugins and half-typed prompt. It gives the agent no actions.
 *
 * Turn it off with `wizardry update off`, `plugin_unload update` with `persist: true`, or
 * WIZARDRY_NO_UPDATE=1 for one run.
 */
export const update = {
  name: 'update',
  inject: ['plugins'],
  apply(ctx: Context, config: UpdateConfig = {}) {
    const home = ctx.plugins.home
    const app = config?.app ?? APP_DIR
    if (!existsSync(join(app, '.git'))) return

    /** The line the last background run left, read once. */
    const notice = () => {
      const file = join(home, 'update-notice')
      if (!existsSync(file)) return undefined
      const text = readFileSync(file, 'utf8').trim()
      rmSync(file, { force: true })
      return text
    }
    const news = notice()
    if (news) process.stderr.write(`${core.updateSaid(news)}\n`)

    if (process.env.WIZARDRY_NO_UPDATE === '1' || process.env.IZARDRY_NO_UPDATE === '1') return
    // A version built since this session started, by this check or by another session's: move onto it.
    const started = Date.now()
    const built = join(app, '.git', 'wizardry-built')
    const ready = () => {
      try {
        if (statSync(built).mtimeMs > started) ctx.root.get('pi')?.restartWhenIdle(core.carriedOn(notice()))
      } catch {}
    }
    const check = () => {
      try {
        updateInBackground(app, home).on('exit', ready)
      } catch {}
    }
    check()
    ctx.on('task/end', check)
    const timer = setInterval(check, config?.intervalMs ?? 15 * 60 * 1000)
    timer.unref()
    ctx.effect(() => () => clearInterval(timer))
  },
}
