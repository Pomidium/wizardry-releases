import type { Context } from '@deepseek-ai/cordis'
import { core } from '../core.js'

const LEVELS = core.thinkLevels()

/** Actions that change the agent itself. None of them is ever applied for it. */
export const self = {
  name: 'self',
  inject: ['pi'],
  apply(ctx: Context) {
    ctx.actions.register({
      name: 'become',
      description: 'Rewrite your own standing instructions. The text replaces whatever you set before and is in your system prompt from the next turn of this session on; an empty string clears it.',
      parameters: {
        type: 'object',
        properties: { identity: { type: 'string', description: 'The instructions you choose to carry.' } },
        required: ['identity'],
      },
      execute({ identity }) {
        ctx.pi.become(String(identity ?? ''))
        return core.becomeSaid(ctx.pi.identity)
      },
    })

    ctx.actions.register({
      name: 'focus',
      description: 'Choose which actions are in front of you. Dropped actions leave your tool list until you take them up again; nothing is unloaded.',
      parameters: {
        type: 'object',
        properties: {
          drop: { type: 'array', items: { type: 'string' }, description: 'Action names to put away.' },
          take: { type: 'array', items: { type: 'string' }, description: 'Action names to bring back.' },
        },
      },
      execute({ drop = [], take = [] }: { drop?: string[]; take?: string[] }) {
        const api = ctx.pi.api
        if (!api) throw new Error('Pi is not running')
        const known = ctx.actions.list().map((action) => action.name)
        const unknown = core.without([...drop, ...take], known)
        if (unknown.length) throw new Error(core.said.noSuchActions(unknown))
        // What ends up in front of the agent is decided in Bend, where it is proven that `focus`
        // itself is never put away (LAWS.bend).
        const active = core.focusActive(api.getActiveTools(), drop, take)
        api.setActiveTools(active)
        const away = core.without(known, active)
        return core.focusSaid(active, away)
      },
    })

    ctx.actions.register({
      name: 'think',
      description: core.thinkDescribe(),
      parameters: { type: 'object', properties: { level: { type: 'string', enum: LEVELS } }, required: ['level'] },
      execute({ level }) {
        const api = ctx.pi.api
        if (!api) throw new Error('Pi is not running')
        api.setThinkingLevel(level)
        return core.thinkSaid(level)
      },
    })
  },
}
