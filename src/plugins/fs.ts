import type { Context } from '@deepseek-ai/cordis'
import {
  createEditToolDefinition, createFindToolDefinition, createGrepToolDefinition,
  createLsToolDefinition, createReadToolDefinition, createWriteToolDefinition,
} from '@earendil-works/pi-coding-agent'

/** Pi's file tools, each one an action. */
export const fs = {
  name: 'fs',
  apply(ctx: Context) {
    const cwd = process.cwd()
    for (const create of [
      createReadToolDefinition, createWriteToolDefinition, createEditToolDefinition,
      createGrepToolDefinition, createFindToolDefinition, createLsToolDefinition,
    ]) {
      const native = create(cwd)
      ctx.actions.register({ name: native.name, description: native.description, native })
    }
  },
}
