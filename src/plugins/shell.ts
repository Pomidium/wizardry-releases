import type { Context } from '@deepseek-ai/cordis'
import { createBashToolDefinition } from '@earendil-works/pi-coding-agent'
import { outside } from '../apart.js'

/**
 * Pi's bash tool as an action. A command sees the environment wizardry was started in: what
 * wizardry sets for the Pi it runs (its own directory, among others) is not passed on, so a
 * `pi` started from a command is the user's Pi with the user's setup.
 */
export const shell = {
  name: 'shell',
  apply(ctx: Context) {
    const native = createBashToolDefinition(process.cwd(), { spawnHook: (context) => ({ ...context, env: outside(context.env) }) })
    ctx.actions.register({ name: native.name, description: native.description, native })
  },
}
