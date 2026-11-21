import { existsSync, lstatSync, readlinkSync, renameSync, symlinkSync } from 'node:fs'
import { homedir } from 'node:os'
import { basename, dirname, join } from 'node:path'
import { Context } from '@deepseek-ai/cordis'
import { parseArgs } from '@earendil-works/pi-coding-agent'
import { Actions } from './actions.js'
import { core } from './core.js'
import { Pi } from './pi.js'
import { Plugins } from './plugins.js'
import { cordis } from './plugins/cordis.js'
import { fs } from './plugins/fs.js'
import { gate } from './plugins/gate.js'
import { rtk } from './plugins/rtk.js'
import { self } from './plugins/self.js'
import { shell } from './plugins/shell.js'
import { update } from './plugins/update.js'

export interface BootOptions {
  /** wizardry's directory. Default: $WIZARDRY_HOME or ~/.wizardry. */
  home?: string
  cwd?: string
  /** Builtin plugins loaded at start. Default: pi, fs, shell, cordis, self, rtk, update. */
  defaults?: string[]
  /** Extra plugin sources (builtin names or paths) to load for this run. */
  extra?: string[]
  /** The folder of shipped default plugins. Default: `defaults/` in the wizardry package. */
  shipped?: string
}

export const DEFAULTS = ['pi', 'fs', 'shell', 'cordis', 'self', 'rtk', 'update']

/** wizardry was called izardry: its directory, variables and command still answer to the old name. */
const OLD = { home: '.izardry', variable: 'IZARDRY_HOME', command: 'izardry' }

export function wizardryHome() {
  const home = join(homedir(), '.wizardry')
  const old = join(homedir(), OLD.home)
  // Which directory it is is decided in Bend, where it is proven that one the user named wins.
  return core.homeOf(process.env.WIZARDRY_HOME ?? '', process.env[OLD.variable] ?? '', home, old, existsSync(home), existsSync(old))
}

/** Whether a path is a symbolic link; a path that is not there is not one. */
function isLink(path: string) {
  try {
    return lstatSync(path).isSymbolicLink()
  } catch {
    return false
  }
}

/**
 * Bring an izardry install over to the new name, once: ~/.izardry becomes ~/.wizardry, with a link
 * left at the old path so open sessions, saved plugin paths and the old command keep working, and a
 * `wizardry` command appears beside an `izardry` one. Returns what to tell the user, if anything moved.
 */
export function adoptOldName(invoked = process.argv[1]) {
  // Whether anything moves is decided in Bend, where it is proven that nothing is moved over a
  // ~/.wizardry that is already there, or when the user named a directory.
  let movedHome = false
  let madeCommand = false
  try {
    const home = join(homedir(), '.wizardry')
    const old = join(homedir(), OLD.home)
    if (core.adoptsHome(!!process.env.WIZARDRY_HOME || !!process.env[OLD.variable], existsSync(home), existsSync(old), isLink(old))) {
      renameSync(old, home)
      symlinkSync('.wizardry', old)
      movedHome = true
    }
  } catch {}
  try {
    const command = join(dirname(invoked), 'wizardry')
    if (core.adoptsCommand(basename(invoked), isLink(invoked), existsSync(command))) {
      symlinkSync(readlinkSync(invoked), command)
      madeCommand = true
    }
  } catch {}
  return core.adopted(movedHome, madeCommand)
}

/** Build the Cordis root, then load every plugin, Pi included, onto it. */
export async function boot(options: BootOptions = {}) {
  const home = options.home ?? wizardryHome()
  const cwd = options.cwd ?? process.cwd()
  const root = new Context()
  await root.plugin(Actions)
  await root.plugin(Plugins, { home, shipped: options.shipped, builtins: { pi: Pi, fs, shell, cordis, self, rtk, update, gate } })
  const plugins = root.get('plugins')!
  const failures = await plugins.boot(options.defaults ?? DEFAULTS, cwd)
  for (const source of options.extra ?? []) {
    try {
      await plugins.load(source, undefined, { cwd })
    } catch (error: any) {
      failures.push(core.said.loadFailed(source, String(error?.message ?? error)))
    }
  }
  return { root, plugins, failures, home }
}

/**
 * The Pi arguments for a process taking over from this one: the same options, without the opening
 * messages (they were sent once already) or a choice of session, and with `session` to open instead.
 */
export function restartArgs(rest: string[], session?: string) {
  const parsed = parseArgs(rest)
  // Pi says which arguments were messages; which of the rest carry over is decided in Bend.
  return core.restartArgs(rest, core.saidOf(parsed.messages, parsed.fileArgs), session && existsSync(session) ? session : undefined)
}
