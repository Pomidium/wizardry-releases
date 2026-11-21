#!/usr/bin/env node
import { spawnSync } from 'node:child_process'
import { mkdirSync } from 'node:fs'
import { keepApart } from './apart.js'
import { adoptOldName, boot, wizardryHome, restartArgs } from './boot.js'
import { core } from './core.js'
import { deleteCommand, exportCommand } from './keep.js'
import { THEME_DIR, THEME_PAIR, VERSION } from './look.js'
import type { Handoff } from './pi.js'
import { APP_DIR, updateNow } from './plugins/update.js'

async function run() {
  const renamed = adoptOldName()
  if (renamed) process.stderr.write(`wizardry: ${renamed}\n`)
  const argv = process.argv.slice(2)
  const first = argv[0]

  // What the arguments mean is decided in Bend (bend/core.bend); this file acts on the answer.
  const command = core.commandOf(first)
  if (command === 'Help') {
    process.stdout.write(core.help())
    return
  }
  if (command === 'Version') {
    process.stdout.write(`wizardry ${VERSION}\n`)
    return
  }
  if (command === 'PiOnly') {
    process.stderr.write(core.piOnlyText(first ?? '', argv))
    process.exitCode = 2
    return
  }
  if (command === 'Update') return update(argv[1])

  // From here on Pi is involved: it is pointed at wizardry's own directory, never at ~/.pi.
  const apart = keepApart(wizardryHome())
  if (apart) process.stderr.write(`${core.updateSaid(apart)}\n`)
  if (command === 'Auth') {
    const { main } = await import('@earendil-works/pi-coding-agent')
    await main(argv)
    return
  }
  if (command === 'Export') {
    process.exitCode = await exportCommand(argv.slice(1))
    return
  }
  if (command === 'Delete') {
    process.exitCode = await deleteCommand(argv.slice(1))
    return
  }

  const split = core.splitArgs(argv)
  if (!split) throw new Error('--plugin needs a name or path')
  const { extra, rest } = split

  const listing = core.listsPlugins(rest)
  const { root, plugins, failures, home } = await boot({ extra })
  // Taking over from a session that restarted itself onto new code: load what it had loaded.
  const resumed = takeHandoff()
  if (resumed) failures.push(...await plugins.restore(resumed.plugins, process.cwd()))
  for (const failure of failures) process.stderr.write(`${core.updateSaid(`plugin failed to load: ${failure}`)}\n`)

  if (listing) {
    for (const plugin of plugins.list()) process.stdout.write(core.listing(plugin.name, plugin.state, plugin.source, plugin.actions))
    await root.fiber.dispose()
    return
  }

  const pi = root.get('pi')
  if (!pi) throw new Error('the "pi" plugin is not loaded, so there is no agent to run')
  const sessions = core.sessionsDir(home)
  mkdirSync(sessions, { recursive: true })
  // Pi contributes the loop, the models and the terminal. Everything it would add to the
  // agent on its own (tools, extensions, skills, templates, context files) stays out, and so
  // does what lies around it (a project's .pi folder, themes, MCP servers): what the agent can
  // do comes from Cordis plugins, as tool calls.
  const piArgs = core.piArgs(rest, sessions, THEME_DIR, THEME_PAIR)
  pi.resumed = resumed
  // Pi leaves through process.exit. If it left to restart, this process becomes the next one.
  process.once('exit', () => {
    if (pi.handoff) restart(restartArgs(rest, pi.handoff.session), pi.handoff)
  })
  await pi.run(piArgs)
}

const HANDOFF = 'WIZARDRY_HANDOFF'
/** What a session started under the old name hands over with. */
const OLD_HANDOFF = 'IZARDRY_HANDOFF'

function takeHandoff(): Handoff | undefined {
  const text = process.env[HANDOFF] ?? process.env[OLD_HANDOFF]
  delete process.env[HANDOFF]
  delete process.env[OLD_HANDOFF]
  try {
    return text ? JSON.parse(text) : undefined
  } catch {
    return undefined
  }
}

/** Replace this process with a fresh wizardry, or where that is not possible run one and wait for it. */
function restart(args: string[], handoff: Handoff) {
  const command = [process.execPath, ...process.execArgv, process.argv[1], ...args]
  const env = { ...process.env, [HANDOFF]: JSON.stringify(handoff) } as Record<string, string>
  try {
    ;(process as any).execve?.(command[0], command, env)
  } catch {}
  process.exitCode = spawnSync(command[0], command.slice(1), { stdio: 'inherit', env }).status ?? 1
}

/** `wizardry update`: update now. `wizardry update on|off`: the switch for automatic updates. */
async function update(choice?: string) {
  const home = wizardryHome()
  // What the word after `update` asks for is decided in Bend, as is what the switch then does.
  const asked = core.updateAsked(choice)
  if (asked === 'Now') {
    process.exitCode = updateNow(APP_DIR, home)
    return
  }
  if (asked === 'Unclear') throw new Error('usage: wizardry update [on|off]')
  // The switch is the `update` plugin being loaded or not, remembered in plugins.json.
  process.env.WIZARDRY_NO_UPDATE = '1'
  const { root, plugins } = await boot({ home })
  const act = core.switchAct(asked === 'On', plugins.list().some((plugin) => plugin.name === 'update'))
  if (act === 'Unloads') await plugins.unload('update', { persist: true })
  if (act === 'Loads') await plugins.load('update', undefined, { persist: true })
  await root.fiber.dispose()
  process.stdout.write(`${core.switchSaid(asked === 'On')}\n`)
}

run().catch((error) => {
  process.stderr.write(`wizardry: ${error?.message ?? error}\n`)
  process.exitCode = 1
})
