import { existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs'
import { homedir } from 'node:os'
import { basename, extname, isAbsolute, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { Context, Inject, Service, type Fiber } from '@deepseek-ai/cordis'
import { createJiti } from 'jiti'
import type { Action } from './actions.js'
import { core } from './core.js'

declare module '@deepseek-ai/cordis' {
  interface Context {
    plugins: Plugins
  }
}

export interface PluginRecord {
  name: string
  /** `builtin:<name>` or an absolute path. */
  source: string
  config: unknown
  fiber: Fiber
}

export interface PluginsConfig {
  /** wizardry's own directory, normally ~/.wizardry. */
  home: string
  builtins: Record<string, unknown>
  /** The folder of default plugins shipped with wizardry. Default: `defaults/` next to `dist/`. */
  shipped?: string
}

interface Saved {
  load: { source: string; config?: unknown }[]
  disabled: string[]
}

const MODULE_FILES = ['.ts', '.mts', '.js', '.mjs']

const here = fileURLToPath(new URL('.', import.meta.url))

/** Loads, unloads and remembers plugins. Every plugin runs on the root context. */
export class Plugins extends Service {
  private records = new Map<string, PluginRecord>()
  private jiti = createJiti(import.meta.url, {
    moduleCache: false,
    fsCache: false,
    alias: {
      wizardry: join(here, 'index.js'),
      cordis: fileURLToPath(import.meta.resolve('@deepseek-ai/cordis')),
    },
  })

  constructor(ctx: Context, private config: PluginsConfig) {
    super(ctx, 'plugins')
  }

  list() {
    return [...this.records.values()].map((record) => ({
      name: record.name,
      source: record.source,
      state: core.stateName(record.fiber.state),
      actions: this.ctx.root.get('actions')!.list().filter((action) => action.owner === record.name).map((action) => action.name),
    }))
  }

  builtins() {
    return Object.keys(this.config.builtins)
  }

  /** What is loaded and from where, enough to bring another process to the same set with `restore`. */
  snapshot() {
    return [...this.records.values()].map(({ name, source, config }) => ({ name, source, config }))
  }

  /** Make the loaded set match a snapshot: unload what it lacks, load what it has. Returns failures. */
  async restore(snapshot: { name: string; source: string; config?: unknown }[], cwd: string) {
    const failures: string[] = []
    // Which go is decided in Bend, where it is proven that what the session runs on stays.
    for (const name of core.restoreUnloads([...this.records.keys()], snapshot.map((entry) => entry.name))) await this.unload(name)
    for (const entry of snapshot) {
      if (this.records.has(entry.name)) continue
      try {
        await this.load(entry.source, entry.config, { cwd })
      } catch (error: any) {
        failures.push(core.said.loadFailed(entry.source, String(error?.message ?? error)))
      }
    }
    return failures
  }

  /** wizardry's own directory, normally ~/.wizardry. */
  get home() {
    return this.config.home
  }

  /** Load a plugin from a builtin name or a file/directory path. */
  async load(source: string, config?: unknown, options: { persist?: boolean; cwd?: string } = {}) {
    const resolved = this.resolve(source, options.cwd ?? process.cwd())
    const module = resolved.startsWith('builtin:')
      ? this.config.builtins[resolved.slice('builtin:'.length)]
      : await this.jiti.import(resolved)
    const builtin = resolved.startsWith('builtin:') ? resolved.slice('builtin:'.length) : undefined
    const plugin = normalise(module, builtin ?? core.stem(basename(resolved)), builtin)
    if (this.records.has(plugin.name)) throw new Error(core.said.alreadyLoaded(plugin.name))

    const fiber = this.ctx.root.plugin(plugin, config)
    const record: PluginRecord = { name: plugin.name, source: resolved, config, fiber }
    this.records.set(plugin.name, record)
    try {
      await fiber.await()
    } catch (error) {
      this.records.delete(plugin.name)
      await fiber.dispose().catch(() => {})
      throw error
    }
    if (options.persist) {
      // What is written down is decided in Bend, where it is proven that a plugin switched off
      // stays off at the next boot, one switched back on comes back, and no other is touched.
      this.save((saved) => {
        saved.disabled = core.switchedOn(saved.disabled, plugin.name)
        if (core.remembered(resolved.startsWith('builtin:'), this.isDefault(plugin.name))) {
          saved.load = saved.load.filter((entry) => entry.source !== resolved)
          saved.load.push({ source: resolved, config })
        }
      })
    }
    return this.list().find((entry) => entry.name === plugin.name)!
  }

  async unload(name: string, options: { persist?: boolean } = {}) {
    const record = this.records.get(name)
    if (!record) throw new Error(core.said.notLoaded(name))
    if (core.isCore(name)) throw new Error(core.said.runsOnIt(name, 'unloaded'))
    this.records.delete(name)
    await record.fiber.dispose()
    if (options.persist) {
      this.save((saved) => {
        saved.load = saved.load.filter((entry) => entry.source !== record.source)
        saved.disabled = core.switchedOff(saved.disabled, name)
      })
    }
  }

  /** Unload and load again from source, picking up edits to the file. */
  async reload(name: string) {
    const record = this.records.get(name)
    if (!record) throw new Error(core.said.notLoaded(name))
    if (core.isCore(name)) throw new Error(core.said.runsOnIt(name, 'reloaded'))
    await this.unload(name)
    return this.load(record.source, record.config)
  }

  /** Bring up the defaults, the plugin directories, and whatever was persisted. */
  async boot(defaults: string[], cwd: string) {
    this.defaults = defaults
    const saved = this.saved()
    const failures: string[] = []
    const attempt = async (source: string, config?: unknown) => {
      try {
        await this.load(source, config, { cwd })
      } catch (error: any) {
        failures.push(core.said.loadFailed(source, String(error?.message ?? error)))
      }
    }
    for (const name of core.builtinsAtBoot(defaults, saved.disabled)) await attempt(`builtin:${name}`)
    // Both directories are the same one when wizardry runs from its own home's parent (e.g. ~).
    const dirs = core.pluginDirs(join(this.config.home, 'plugins'), join(cwd, '.wizardry', 'plugins'))
    const found = dirs.flatMap((dir) => pluginFiles(dir))
    const shipped = pluginFiles(this.config.shipped ?? join(here, '..', 'defaults'))
    // Which of them load is decided in Bend, where it is proven (LAWS.bend) that a shipped default
    // steps aside for a file of the same name in a plugin directory, which is how a user changes
    // one without touching wizardry, and that nothing switched off is loaded.
    for (const entry of core.plan(shipped, found, saved.disabled)) await attempt(entry.path)
    for (const entry of saved.load) {
      if (!core.among([...this.records.values()].map((record) => record.source), entry.source)) await attempt(entry.source, entry.config)
    }
    return failures
  }

  private defaults: string[] = []

  private isDefault(name: string) {
    return this.defaults.includes(name)
  }

  private resolve(source: string, cwd: string) {
    const bare = source.startsWith('builtin:') ? source.slice('builtin:'.length) : source
    if (core.isBuiltinSource(source.startsWith('builtin:'), bare in this.config.builtins, existsSync(resolve(cwd, source)))) {
      return `builtin:${bare}`
    }
    if (source.startsWith('builtin:')) throw new Error(core.said.noBuiltin(bare, this.builtins()))
    const inHome = core.underHome(source)
    const expanded = inHome === undefined ? source : join(homedir(), inHome)
    const path = isAbsolute(expanded) ? expanded : resolve(cwd, expanded)
    if (!existsSync(path)) throw new Error(core.said.noPluginAt(path))
    if (statSync(path).isDirectory()) {
      const file = entryFile(path)
      if (!file) throw new Error(core.said.noEntry(path))
      return file
    }
    return path
  }

  private get file() {
    return join(this.config.home, 'plugins.json')
  }

  private saved(): Saved {
    try {
      const data = JSON.parse(readFileSync(this.file, 'utf8'))
      // Names only: what is switched off is decided in Bend, which takes text.
      const disabled = Array.isArray(data.disabled) ? data.disabled.filter((name: unknown) => typeof name === 'string') : []
      return { load: Array.isArray(data.load) ? data.load : [], disabled }
    } catch {
      return { load: [], disabled: [] }
    }
  }

  private save(change: (saved: Saved) => void) {
    const saved = this.saved()
    change(saved)
    mkdirSync(this.config.home, { recursive: true })
    writeFileSync(this.file, `${JSON.stringify(saved, null, 2)}\n`)
  }
}

/** The loadable plugins in a directory, by file name without extension. */
function pluginFiles(dir: string) {
  if (!existsSync(dir)) return []
  return readdirSync(dir).sort().flatMap((entry) => {
    const path = join(dir, entry)
    const folder = statSync(path).isDirectory()
    return core.usable(entry, folder, folder && !!entryFile(path)) ? [{ name: core.stem(entry), path }] : []
  })
}

function entryFile(dir: string) {
  try {
    const main = JSON.parse(readFileSync(join(dir, 'package.json'), 'utf8')).main
    if (typeof main === 'string' && existsSync(join(dir, main))) return join(dir, main)
  } catch {}
  for (const ext of MODULE_FILES) {
    if (existsSync(join(dir, `index${ext}`))) return join(dir, `index${ext}`)
  }
  return undefined
}

/**
 * Accept the shapes a plugin module can take and return one Cordis object plugin.
 *
 * A module is a function `(ctx, config)`, a class, an object with `apply`, or a bare
 * `actions` array; the first three may sit on the default export or be the module itself.
 * `actions` is always injected, so a plugin can call `ctx.actions.register` without declaring it.
 */
export function normalise(module: any, fallbackName: string, forcedName?: string) {
  const exported = module?.default ?? module
  const body = typeof exported === 'function' || typeof exported?.apply === 'function'
    ? exported
    : typeof module?.apply === 'function' ? module : undefined
  const declared: Action[] | undefined = exported?.actions ?? module?.actions
  if (!body && !Array.isArray(declared)) {
    throw new TypeError('a plugin exports a function (ctx, config), a class, an object with apply(), or an `actions` array')
  }

  const pick = (key: string) => exported?.[key] ?? module?.[key]
  const ownName = typeof body === 'function' ? body.name : undefined
  const exportedName = typeof exported === 'function' ? undefined : exported?.name
  const name = core.pickName([forcedName, exportedName, module?.name, ownName, fallbackName])
  const isClass = typeof body === 'function' && /^class[\s{]/.test(Function.prototype.toString.call(body))

  return {
    name,
    inject: { actions: null, ...Inject.resolve(pick('inject')) },
    Config: pick('Config'),
    apply(ctx: Context, config: unknown) {
      for (const action of declared ?? []) ctx.actions.register(action)
      if (!body) return
      if (isClass) return new body(ctx, config)?.[Service.init]?.()
      return typeof body === 'function' ? body(ctx, config) : body.apply(ctx, config)
    },
  }
}
