import { execFile } from 'node:child_process'
import { accessSync, constants } from 'node:fs'
import { homedir } from 'node:os'
import { delimiter } from 'node:path'
import type { Context } from '@deepseek-ai/cordis'
import { core } from '../core.js'

export interface RtkConfig {
  /** Path to the rtk executable. Default: found on PATH or in the usual install directories. */
  binary?: string
  /** How long `rtk rewrite` may take before the command runs unchanged. Default 2000. */
  timeoutMs?: number
}

export function findRtk(configured?: string) {
  // Where it is looked for is decided in Bend: where the user said, or PATH and then the usual places.
  return core.rtkPlaces(configured || undefined, (process.env.PATH ?? '').split(delimiter), homedir()).find((file) => {
    try {
      accessSync(file, constants.X_OK)
      return true
    } catch {
      return false
    }
  })
}

/**
 * The command rtk would run in place of `command`, or undefined to run it as written.
 *
 * `rtk rewrite` exits 0 or 3 with the rewrite on stdout (3 leaves approval to the host, and
 * wizardry does not ask), 1 when it has no equivalent, and 2 when one of its deny rules matched;
 * refusing a command is not a rewriter's call here, so that runs unchanged too. Never rejects.
 */
export function rtkRewrite(binary: string, command: string, timeoutMs = 2000, signal?: AbortSignal) {
  return new Promise<string | undefined>((resolve) => {
    try {
      execFile(binary, ['rewrite', command], { encoding: 'utf8', timeout: timeoutMs, signal }, (error, stdout) => {
        // Whether the rewrite is taken is decided in Bend, where it is proven that it never is
        // unless rtk ended with 0 or 3. An exit that is not a status (a timeout, a signal) is 1.
        const code = error ? (error as any).code : 0
        resolve(core.rtkTakes(Number.isInteger(code) && code >= 0 ? code : 1, String(stdout ?? ''), command))
      })
    } catch {
      resolve(undefined)
    }
  })
}

/**
 * rtk (https://github.com/rtk-ai/rtk): condensed output for common dev commands.
 *
 * It puts a layer around `bash` and delegates every rewrite rule to `rtk rewrite`. The layer is
 * declared on the bash action itself, with a per-call `raw` switch, so the agent knows its output
 * is condensed and decides call by call whether it wants that.
 */
export const rtk = {
  name: 'rtk',
  apply(ctx: Context, config: RtkConfig = {}) {
    const binary = findRtk(config?.binary)
    if (!binary) {
      throw new Error(core.said.rtkMissing(config?.binary || undefined))
    }
    ctx.actions.wrap('bash', {
      note: 'Commands rtk knows (git, ls, grep, test runners, linters, package managers and more) run through rtk, which condenses their output to save context. Set `raw: true` on a call to run the command exactly as written and get its full output.',
      properties: { raw: { type: 'boolean', description: 'Skip rtk for this call and return unfiltered output.' } },
      async around({ raw, ...params }, env, next) {
        const command = params.command
        if (typeof command !== 'string' || core.rtkSkips(!!raw, command)) return next(params)
        const rewritten = await rtkRewrite(binary, command, config?.timeoutMs, env.signal)
        return next(rewritten ? { ...params, command: rewritten } : params)
      },
    })
  },
}
