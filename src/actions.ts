import { Context, Service } from '@deepseek-ai/cordis'
import type { ExtensionContext, ToolDefinition } from '@earendil-works/pi-coding-agent'
import { core } from './core.js'

/** What an action hands back: plain text, or text plus structured details. */
export type ActionResult = string | { text: string; details?: unknown }

/** What an action is told about the call it is serving. */
export interface ActionEnv {
  cwd: string
  signal?: AbortSignal
  /** Stream partial output while the action runs. */
  update?: (text: string) => void
  /** The Pi extension context of the calling session, when Pi made the call. */
  pi?: ExtensionContext
}

/**
 * An action: one thing the agent may choose to do.
 *
 * `parameters` is a JSON Schema object (TypeBox schemas are JSON Schema).
 * `native` carries a ready-made Pi tool definition instead of `parameters`/`execute`.
 */
export interface Action<P = any> {
  name: string
  description: string
  /**
   * What the user sees a call to this action named as. Default: the plugin's name, then the
   * action's, as words ("subagent create"). The agent always calls it by `name`.
   */
  title?: string
  /**
   * The name of an action this one waits behind: it is not in the agent's tool list until that
   * one has been called in the session. For a skill's working actions, behind the one that
   * explains it. Waiting behind an action nobody registered is not waiting.
   */
  after?: string
  parameters?: Record<string, unknown>
  execute?: (params: P, env: ActionEnv) => ActionResult | Promise<ActionResult>
  native?: ToolDefinition<any, any>
}

/**
 * A layer one plugin puts around another plugin's action. It can add parameters and a note to
 * the description, and run code around the call. It lasts as long as the plugin that added it.
 */
export interface ActionWrap {
  /** Appended to the action's description, so the agent can see what the layer does. */
  note?: string
  /** Extra JSON Schema properties the layer accepts on the action's parameters. */
  properties?: Record<string, unknown>
  /** Run around the call. Pass (possibly changed) params to `next`; the layer's own properties must be removed. */
  around?: (params: any, env: ActionEnv, next: (params: any) => Promise<any>) => Promise<any>
}

export interface RegisteredAction extends Action {
  /** Name of the plugin whose fiber owns the action. */
  owner: string
}

declare module '@deepseek-ai/cordis' {
  interface Context {
    actions: Actions
  }
  interface Events {
    /** An action became available. */
    'action/registered'(action: RegisteredAction): void
    /** An action's description or parameters changed because a wrap was added or removed. */
    'action/changed'(action: RegisteredAction): void
    /** An action went away, normally because its plugin was unloaded. */
    'action/unregistered'(action: RegisteredAction): void
    /** Serial. Return a string to refuse the call; the string is the reason given to the agent. */
    'action/before'(action: RegisteredAction, params: unknown, env: ActionEnv): string | void | Promise<string | void>
    /** An action finished or threw. */
    'action/after'(action: RegisteredAction, params: unknown, outcome: { result?: unknown; error?: unknown }): void
  }
}

/** The registry of actions. Registration is owned by the calling plugin's fiber. */
export class Actions extends Service {
  private store = new Map<string, RegisteredAction>()
  private wraps = new Map<string, ActionWrap[]>()

  constructor(ctx: Context) {
    super(ctx, 'actions')
  }

  /** Register an action for as long as the calling plugin stays loaded. */
  register(action: Action) {
    const ctx = this.ctx
    const name = action.name ?? action.native?.name
    if (!name) throw new TypeError('an action needs a name')
    if (!action.native && typeof action.execute !== 'function') {
      throw new TypeError(core.said.needsExecute(name))
    }
    if (this.store.has(name)) {
      throw new Error(core.said.alreadyRegistered(name, this.store.get(name)!.owner))
    }
    const entry: RegisteredAction = {
      ...action,
      name,
      description: action.description ?? action.native?.description ?? '',
      owner: ctx.fiber.name,
    }
    return ctx.effect(() => {
      this.store.set(name, entry)
      ctx.root.emit('action/registered', entry)
      return () => {
        if (this.store.get(name) !== entry) return
        this.store.delete(name)
        ctx.root.emit('action/unregistered', entry)
      }
    }, `actions.register("${name}")`)
  }

  /** Put a layer around the named action for as long as the calling plugin stays loaded. */
  wrap(name: string, wrap: ActionWrap) {
    const ctx = this.ctx
    const changed = () => {
      const action = this.store.get(name)
      if (action) ctx.root.emit('action/changed', action)
    }
    return ctx.effect(() => {
      this.wraps.set(name, [...(this.wraps.get(name) ?? []), wrap])
      changed()
      return () => {
        this.wraps.set(name, (this.wraps.get(name) ?? []).filter((entry) => entry !== wrap))
        changed()
      }
    }, `actions.wrap("${name}")`)
  }

  /** The description and parameter schema the agent is shown, with every wrap applied. */
  describe(action: RegisteredAction) {
    const wraps = this.wraps.get(action.name) ?? []
    const base: any = action.native?.parameters ?? action.parameters ?? { type: 'object', properties: {} }
    const extra = Object.assign({}, ...wraps.map((wrap) => wrap.properties ?? {}))
    const notes = wraps.map((wrap) => wrap.note ?? '')
    return {
      description: core.described(action.description, notes),
      parameters: Object.keys(extra).length ? { ...base, properties: { ...base.properties, ...extra } } : base,
    }
  }

  get(name: string) {
    return this.store.get(name)
  }

  list() {
    return [...this.store.values()]
  }

  /** Run an action outside a Pi tool call, for example from another plugin. */
  async invoke(name: string, params: unknown, env: ActionEnv = { cwd: process.cwd() }): Promise<ActionResult> {
    const action = this.store.get(name)
    if (!action) throw new Error(core.said.noAction(name))
    return this.run(action, params, env, async (params) => {
      if (action.execute) return action.execute(params, env)
      const result = await action.native!.execute('invoke', params, env.signal, undefined, env.pi as any)
      const text = result.content.map((part: any) => (part.type === 'text' ? part.text : `[${part.type}]`)).join('\n')
      return { text, details: result.details }
    })
  }

  /** Run one execution through the before/after events and the action's wraps. */
  async run<T>(action: RegisteredAction, params: unknown, env: ActionEnv, body: (params: any) => Promise<T> | T): Promise<T> {
    const refusal = await this.ctx.root.serial('action/before', action, params, env)
    if (typeof refusal === 'string') throw new Error(refusal)
    const layers = (this.wraps.get(action.name) ?? []).filter((wrap) => wrap.around)
    const call = layers.reduce<(params: any) => Promise<T>>(
      (next, wrap) => (params) => wrap.around!(params, env, next),
      async (params) => body(params),
    )
    try {
      const result = await call(params)
      this.ctx.root.emit('action/after', action, params, { result })
      return result
    } catch (error) {
      this.ctx.root.emit('action/after', action, params, { error })
      throw error
    }
  }
}
