import type { Context } from '@deepseek-ai/cordis'
import { core } from '../core.js'
import { actionTitle } from '../look.js'

export interface GateConfig {
  /** Actions that need a yes from the user. */
  actions?: string[]
}

/**
 * The opposite of the default: ask the user before selected actions run.
 * Not loaded unless asked for (`wizardry --gate`, or `plugin_load gate`).
 */
export const gate = {
  name: 'gate',
  apply(ctx: Context, config: GateConfig = {}) {
    const gated = config?.actions ?? core.gated()
    ctx.on('action/before', async (action, params, env) => {
      if (!core.among(gated, action.name)) return
      if (!env.pi?.hasUI) return core.said.gateNoOne(action.name)
      const summary = core.gateSummary(JSON.stringify(params, null, 2) ?? '')
      const allowed = await env.pi.ui.confirm(core.said.gateAsks(actionTitle(action)), summary)
      if (!allowed) return core.said.gateDeclined(action.name)
    })
  },
}
