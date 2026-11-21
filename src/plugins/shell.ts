import type { Context } from '@deepseek-ai/cordis'
import { createBashToolDefinition } from '@earendil-works/pi-coding-agent'

/** Pi's bash tool as an action. */
export const shell = {
  name: 'shell',
  apply(ctx: Context) {
    const native = createBashToolDefinition(process.cwd())
    ctx.actions.register({ name: native.name, description: native.description, native })
  },
}
