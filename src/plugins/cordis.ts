import { mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import type { Context } from '@deepseek-ai/cordis'
import { core } from '../core.js'
import { APP_DIR, updateCommand } from './update.js'

function describe(verb: string, plugin: { name: string; state: string; actions: string[] }) {
  return core.loadedText(verb, plugin.name, plugin.state, plugin.actions)
}

/**
 * `/default`: make this session's setup the one new sessions start with. Its model and thinking
 * level go into the settings of the Pi wizardry runs (in wizardry's own directory, which Pi
 * rewrites only for the settings it changes itself), and the plugins loaded now become the ones
 * that load at every start. The user's, not the agent's.
 */
export function defaultCommand(ctx: Context) {
  ctx.root.get('pi')?.command('default', {
    description: 'Make this session\'s model, thinking level and plugins what new sessions start with',
    run(_args, piCtx) {
      const plugins = ctx.root.get('plugins')!
      const model = piCtx.model
      let thinking = ''
      try {
        thinking = String(ctx.root.get('pi')?.api?.getThinkingLevel?.() ?? '')
      } catch {}
      const dir = core.ownPi(plugins.home)
      const file = join(dir, 'settings.json')
      let settings: Record<string, unknown> = {}
      try {
        settings = JSON.parse(readFileSync(file, 'utf8'))
      } catch {}
      // Which settings are written is decided in Bend: only what this session has.
      for (const { name, value } of core.defaultSettings(model?.provider ?? '', model?.id ?? '', thinking)) settings[name] = value
      mkdirSync(dir, { recursive: true, mode: 0o700 })
      writeFileSync(file, `${JSON.stringify(settings, null, 2)}\n`)
      piCtx.ui.notify(core.defaultSaid(model ? `${model.provider}/${model.id}` : '', thinking, plugins.keep()), 'info')
    },
  })
}

/** The agent's view of, and hands on, the Cordis runtime it runs on. */
export const cordis = {
  name: 'cordis',
  inject: ['plugins'],
  apply(ctx: Context) {
    updateCommand(ctx)
    defaultCommand(ctx)

    ctx.actions.register({
      name: 'cordis_inspect',
      description: 'Look at the runtime you are running on: loaded plugins with their state and the actions each provides, builtin plugins that are not loaded, and how a plugin file is written.',
      parameters: { type: 'object', properties: {} },
      execute() {
        const plugins = ctx.plugins.list()
        const lines = plugins.map((plugin) => core.inspectLine(plugin.name, plugin.state, plugin.source, plugin.actions))
        const idle = core.without(ctx.plugins.builtins(), plugins.map((plugin) => plugin.name))
        return core.inspectText(lines, idle)
      },
    })

    ctx.actions.register({
      name: 'cordis_map',
      description:
        'Read the map of the wizardry framework you are running on: which checkout is live, what each source file owns, the Cordis rules that bite, the Pi surface, and how to debug and test. Read it before editing wizardry\'s own code or writing a non-trivial plugin.',
      parameters: { type: 'object', properties: {} },
      execute() {
        try {
          return readFileSync(join(APP_DIR, 'AGENTS.md'), 'utf8')
        } catch {
          return core.said.noMap(APP_DIR)
        }
      },
    })

    ctx.actions.register({
      name: 'plugin_load',
      description: 'Load a plugin into the running session: a builtin name, or a path to a plugin file or directory (one you wrote counts). Its actions become available to you on the next step.',
      parameters: {
        type: 'object',
        properties: {
          source: { type: 'string', description: 'Builtin plugin name, or file/directory path.' },
          config: { type: 'object', description: 'Config passed to the plugin.' },
          persist: { type: 'boolean', description: 'Also load it in future sessions. Default false.' },
        },
        required: ['source'],
      },
      async execute({ source, config, persist }, env) {
        const plugin = await ctx.plugins.load(source, config, { persist, cwd: env.cwd })
        return describe('Loaded', plugin)
      },
    })

    ctx.actions.register({
      name: 'plugin_unload',
      description: 'Unload a plugin from the running session. Everything it registered, its actions included, goes with it.',
      parameters: {
        type: 'object',
        properties: {
          name: { type: 'string' },
          persist: { type: 'boolean', description: 'Also keep it unloaded in future sessions. Default false.' },
        },
        required: ['name'],
      },
      async execute({ name, persist }) {
        await ctx.plugins.unload(name, { persist })
        return core.said.unloaded(name)
      },
    })

    ctx.actions.register({
      name: 'plugin_reload',
      description: 'Unload a plugin and load it again from its source, picking up edits to its file.',
      parameters: { type: 'object', properties: { name: { type: 'string' } }, required: ['name'] },
      async execute({ name }) {
        const plugin = await ctx.plugins.reload(name)
        return describe('Reloaded', plugin)
      },
    })
  },
}
