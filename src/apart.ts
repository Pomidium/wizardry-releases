import { chmodSync, copyFileSync, existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { homedir } from 'node:os'
import { join } from 'node:path'
import { core } from './core.js'

/**
 * wizardry kept apart from Pi's own setup.
 *
 * Pi keeps its logins, settings, extensions and packages in one directory (~/.pi/agent, or where
 * PI_CODING_AGENT_DIR says). wizardry runs the Pi it ships against a directory of its own inside
 * its home, so nothing installed for Pi reaches a wizardry session and nothing wizardry does
 * lands in Pi's. What that directory is, what is brought into it the first time and what Pi finds
 * in the environment are decided in Bend (bend/core.bend, "Kept apart"); this file acts on it.
 */

/** What the variables wizardry changes for Pi held when it started. */
const before = new Map<string, string | undefined>()

/** Where the Pi installed on this machine keeps its own: to wizardry, the old setup. */
export function oldPi() {
  const named = before.has('PI_CODING_AGENT_DIR') ? before.get('PI_CODING_AGENT_DIR') : process.env.PI_CODING_AGENT_DIR
  return core.oldPi(named ?? '', homedir())
}

/**
 * Point Pi at wizardry's own directory for the rest of this process. The first time, the logins
 * and the few settings Bend names are brought over from Pi's own directory, which is only read.
 * Returns what to tell the user, if anything was set up.
 */
export function keepApart(home: string) {
  const old = oldPi()
  const own = core.ownPi(home)
  const said = core.brings(existsSync(own), existsSync(old), old, own) ? bring(old, own) : undefined
  for (const name of core.piEnvTouched()) if (!before.has(name)) before.set(name, process.env[name])
  for (const name of core.piEnvCleared()) delete process.env[name]
  for (const { name, value } of core.piEnv(home)) process.env[name] = value
  return said
}

function bring(old: string, own: string) {
  mkdirSync(own, { recursive: true, mode: 0o700 })
  const brought: string[] = []
  for (const file of core.broughtFiles()) {
    if (!existsSync(join(old, file))) continue
    copyFileSync(join(old, file), join(own, file))
    chmodSync(join(own, file), 0o600)
    brought.push(file)
  }
  try {
    const settings = JSON.parse(readFileSync(join(old, 'settings.json'), 'utf8'))
    // Which settings come over is decided in Bend, where it is proven that no add-on does.
    const keys = core.settingsBrought(Object.keys(settings))
    if (keys.length) {
      writeFileSync(join(own, 'settings.json'), `${JSON.stringify(Object.fromEntries(keys.map((key) => [key, settings[key]])), null, 2)}\n`)
      brought.push('settings.json')
    }
  } catch {}
  return core.broughtSaid(brought, own, old)
}

/** The environment a command the agent runs sees: what wizardry changed for Pi is as it was. */
export function outside(env: NodeJS.ProcessEnv) {
  const out = { ...env }
  for (const [name, value] of before) {
    if (value === undefined) delete out[name]
    else out[name] = value
  }
  return out
}
