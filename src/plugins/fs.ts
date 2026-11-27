import type { Context } from '@deepseek-ai/cordis'
import { createEditToolDefinition, createReadToolDefinition, createWriteToolDefinition } from '@earendil-works/pi-coding-agent'
import { core } from '../core.js'

/** Pi's file tools, each one an action. Searching and listing are `bash`'s: one way to do a thing. */
export const fs = {
  name: 'fs',
  apply(ctx: Context) {
    const cwd = process.cwd()
    for (const create of [createReadToolDefinition, createWriteToolDefinition, createEditToolDefinition]) {
      const native = create(cwd)
      ctx.actions.register({ name: native.name, description: core.fsDescribe(native.name, native.description), native })
    }
  },
}
