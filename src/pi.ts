import { Context, Service } from '@deepseek-ai/cordis'
import { main, type ExtensionAPI, type ExtensionContext, type ToolDefinition } from '@earendil-works/pi-coding-agent'
import type { ActionEnv, ActionResult, RegisteredAction } from './actions.js'
import { Text } from '@earendil-works/pi-tui'
import { core } from './core.js'
import { actionTitle, callText, Header, resultText, workingIndicator } from './look.js'

declare module '@deepseek-ai/cordis' {
  interface Context {
    pi: Pi
  }
  interface Events {
    /** The agent finished what it was asked and is waiting for the user. Nothing a listener does reaches the agent. */
    'task/end'(): void
    /** Pi's extension API is live, with wizardry's tools and commands registered. No session has started yet. */
    'pi/ready'(api: ExtensionAPI): void
    /**
     * A session started (a resumed one counts), after wizardry's own setup for it is done. The place
     * for per-session choices a plugin makes: `api.setModel(...)`, `api.setThinkingLevel(...)`.
     */
    'pi/session-start'(api: ExtensionAPI, piCtx: ExtensionContext): void
  }
}

const IDENTITY_ENTRY = 'wizardry:identity'

/** A slash command the user can type. It is the user's, not the agent's: nothing it does is an action. */
export interface Command {
  description: string
  /** Offered after the command name, for example ["on", "off"]. */
  words?: string[]
  run: (args: string, piCtx: ExtensionContext) => void | Promise<void>
}

/** What a session hands to the process that takes over from it, so the user finds it as they left it. */
export interface Handoff {
  /** The session file, when there is one to open again. */
  session?: string
  plugins: { name: string; source: string; config?: unknown }[]
  /** The actions the agent has in front of it (see `focus`). */
  active: string[]
  /** Whatever the user had typed and not sent. */
  editor: string
  /** Why the session started again, to tell the user once it is back. */
  note?: string
}

/** The whole standing prompt. Everything else the agent knows comes from its tool list. */
export function basePrompt(cwd: string) {
  return core.basePrompt(cwd, core.day(new Date().toISOString()))
}

/** Pi, hosted as a Cordis service. It declares every registered action to the model as a tool. */
export class Pi extends Service {
  static inject = ['actions']

  /** The live Pi extension API, once Pi has loaded. */
  api?: ExtensionAPI
  /** Standing instructions the agent wrote for itself with `become`. Empty until it chooses to. */
  identity = ''
  private bound = false
  /** Set when this process is about to be replaced; bin.ts starts the next one from it on exit. */
  handoff?: Handoff
  /** Set in a process that took over from another; applied when its session starts. */
  resumed?: Handoff
  private live?: ExtensionContext
  private commands = new Map<string, Command>()
  private restartWanted = false
  private restartNote?: string

  constructor(ctx: Context) {
    super(ctx, 'pi')
    ctx.on('action/registered', (action) => this.expose(action))
    ctx.on('action/changed', (action) => this.expose(action))
    ctx.on('action/unregistered', (action) => this.retract(action))
  }

  private get actions() {
    return this.ctx.root.get('actions')!
  }

  systemPrompt(cwd: string) {
    return core.systemPrompt(basePrompt(cwd), this.identity)
  }

  /** Record the agent's self-authored instructions; they apply from the next turn. */
  become(identity: string) {
    this.identity = core.tidy(identity)
    this.api?.appendEntry(IDENTITY_ENTRY, { identity: this.identity })
  }

  /** Offer the user `/name` for as long as the calling plugin stays loaded. */
  command(name: string, command: Command) {
    return this.ctx.effect(() => {
      this.commands.set(name, command)
      this.declare(name)
      return () => {
        if (this.commands.get(name) === command) this.commands.delete(name)
      }
    }, `pi.command("${name}")`)
  }

  /** Pi keeps a command once it has it, so the one declared looks up whoever provides it now. */
  private declare(name: string) {
    const command = this.commands.get(name)
    if (!this.api || !command) return
    this.api.registerCommand(name, {
      description: command.description,
      getArgumentCompletions: (prefix) => {
        const words = core.completions(this.commands.get(name)?.words ?? [], prefix)
        return words.length ? words.map((word) => ({ value: word, label: word })) : null
      },
      handler: async (args, piCtx) => {
        const current = this.commands.get(name)
        if (!current) return piCtx.ui.notify(core.said.commandGone(name), 'warning')
        await current.run(args.trim(), piCtx)
      },
    })
  }

  /**
   * Start again on the code now on disk, in the same session, once the agent is idle. Only an
   * interactive session does: anything else ends by itself and the next start is already new.
   */
  restartWhenIdle(note?: string) {
    this.restartWanted = true
    this.restartNote = note ?? this.restartNote
    this.tryRestart()
  }

  private tryRestart() {
    const piCtx = this.live
    // Whether it starts again now is decided in Bend, where it is proven that it never does
    // while the agent is working (LAWS.bend, restart_waits).
    // Pi is only asked whether the agent is idle when the answer could matter.
    const tui = piCtx?.mode === 'tui'
    const idle = this.restartWanted && tui && !!piCtx?.isIdle()
    if (!this.api || !piCtx || !core.restartsNow(this.restartWanted, true, tui, idle)) return
    this.restartWanted = false
    this.handoff = {
      session: piCtx.sessionManager.getSessionFile(),
      plugins: this.ctx.root.get('plugins')?.snapshot() ?? [],
      active: this.api.getActiveTools(),
      editor: piCtx.ui.getEditorText(),
      note: this.restartNote,
    }
    piCtx.shutdown()
  }

  /** Start Pi with the given arguments. Resolves when Pi exits. */
  async run(argv: string[]) {
    await main(argv, { 
      // Hidden from Pi's [Extensions] list: the header lists the Cordis plugins instead.
      extensionFactories: [{ name: 'wizardry', hidden: true, factory: (pi) => this.attach(pi) }],
     })
  }

  private attach(pi: ExtensionAPI) {
    this.api = pi
    this.bound = false
    for (const action of this.actions.list()) pi.registerTool(this.toTool(action))
    for (const name of this.commands.keys()) this.declare(name)
    this.ctx.root.emit('pi/ready', pi)

    pi.on('session_start', (_event, piCtx) => {
      this.bound = true
      const written = (piCtx.sessionManager.getBranch() as any[])
        .filter((entry) => entry.type === 'custom' && entry.customType === IDENTITY_ENTRY)
        .map((entry) => String(entry.data?.identity ?? ''))
      this.identity = core.lastIdentity(written)
      if (piCtx.mode === 'tui') {
        piCtx.ui.setHeader((tui, theme) => new Header(theme, () => this.ctx.root.get('plugins')?.list() ?? [], tui))
        // The small cap takes the place of Pi's spinner while the agent works.
        piCtx.ui.setWorkingIndicator(workingIndicator(piCtx.ui.theme))
      }
      this.live = piCtx
      const resumed = this.resumed
      this.resumed = undefined
      if (resumed) {
        pi.setActiveTools(core.only(resumed.active, pi.getAllTools().map((tool) => tool.name)))
        if (resumed.editor && piCtx.mode === 'tui') piCtx.ui.setEditorText(resumed.editor)
        if (resumed.note) piCtx.ui.notify(resumed.note, 'info')
      }
      this.ctx.root.emit('pi/session-start', pi, piCtx)
    })
    pi.on('agent_end', () => {
      this.ctx.root.emit('task/end')
      // The agent is not idle until this handler has returned.
      setTimeout(() => this.tryRestart(), 200).unref()
    })
    pi.on('before_agent_start', (_event, piCtx) => ({ systemPrompt: this.systemPrompt(piCtx.cwd) }))
  }

  private expose(action: RegisteredAction) {
    if (!this.api) return
    // Re-declaring a tool the agent has put away with `focus` must not bring it back.
    const away = core.staysAway(this.bound, core.among(this.api.getAllTools().map((tool) => tool.name), action.name),
      core.among(this.api.getActiveTools(), action.name))
    this.api.registerTool(this.toTool(action))
    if (away) this.api.setActiveTools(core.without(this.api.getActiveTools(), [action.name]))
  }

  private retract(action: RegisteredAction) {
    if (!this.api || !this.bound) return
    this.api.setActiveTools(core.without(this.api.getActiveTools(), [action.name]))
  }

  private toTool(action: RegisteredAction): ToolDefinition<any, any> {
    const { name } = action
    const actions = this.actions
    const live = () => {
      const current = actions.get(name)
      if (!current) throw new Error(core.said.actionGone(name))
      return current
    }
    const envOf = (signal: AbortSignal | undefined, onUpdate: any, piCtx: ExtensionContext): ActionEnv => ({
      cwd: piCtx?.cwd ?? process.cwd(),
      signal,
      pi: piCtx,
      update: (text) => onUpdate?.({ content: [{ type: 'text', text }], details: undefined }),
    })

    const shown = actions.describe(action)

    if (action.native) {
      return {
        ...action.native,
        description: shown.description,
        parameters: shown.parameters,
        execute: (id, params, signal, onUpdate, piCtx) => {
          const current = live()
          return actions.run(current, params, envOf(signal, onUpdate, piCtx), (params) =>
            current.native!.execute(id, params, signal, onUpdate, piCtx))
        },
      }
    }

    return {
      name,
      label: actionTitle(action),
      description: shown.description,
      parameters: shown.parameters,
      // How the call reads to the user. Pi's own tools (the `native` branch above) bring their own.
      renderCall: (args, theme, context) => {
        const text = context.lastComponent instanceof Text ? context.lastComponent : new Text('', 0, 0)
        text.setText(callText(action, args, theme, context.expanded))
        return text
      },
      renderResult: (result, { expanded }, theme, context) => {
        const text = context.lastComponent instanceof Text ? context.lastComponent : new Text('', 0, 0)
        const output = result.content.map((part: any) => (part.type === 'text' ? part.text : `[${part.type}]`)).join('\n')
        text.setText(resultText(output, theme, expanded))
        return text
      },
      execute: async (_id, params, signal, onUpdate, piCtx) => {
        const current = live()
        const env = envOf(signal, onUpdate, piCtx)
        const result: ActionResult = await actions.run(current, params, env, (params) => current.execute!(params, env))
        if (typeof result === 'string') return { content: [{ type: 'text', text: result }], details: undefined }
        return { content: [{ type: 'text', text: result?.text ?? '' }], details: result?.details }
      },
    }
  }
}
