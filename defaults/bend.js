// bend: the Bend 2 skill (https://bend-lang.com), as the `bend` action.
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. It ships in wizardry's
// `defaults/` folder and is switched on for everyone. Switch it off with `plugin_unload bend`
// (persist: true); change it by copying this file to ~/.wizardry/plugins/bend.js and editing the
// copy, which is loaded instead of this one.
//
// wizardry switches Pi's skills off, so a skill reaches the agent the only way anything does here:
// as an action. The rules below sit in the action's description, so they are in front of the agent
// in every session; calling the action returns them again with the output of `bend guide`.
//
// It also makes Bend the default: the description tells the agent to write in Bend whatever Bend can
// express, and to keep other languages for what Bend cannot reach or a codebase or user that wants one.
//
// This file stays JavaScript because it is one file a user copies and edits, and all it does is
// find a binary and run it, which are calls outside Bend.
//
// Bend itself is not bundled. When the binary is missing the action says how to install it.
//
// Config (optional): { bin: "/path/to/bend" }

import { execFile } from 'node:child_process'
import { existsSync } from 'node:fs'
import { homedir } from 'node:os'
import { delimiter, join } from 'node:path'

export const name = 'bend'

export const INSTALL = 'curl -fsSL https://bend-lang.com/install.sh | sh'

export const RULES = [
  'When using Bend:',
  '- run `bend guide` to learn it',
  '- use `LAWS.bend` to keep important rules',
  '- run `bend PROOF.bend` before committing',
  '- parallelize the code whenever possible',
].join('\n')

/**
 * Bend is the language wizardry writes in unless there is a reason not to. Like the rules, this
 * reaches the agent the only way anything does here: in the action's description, in every session.
 */
export const DEFAULT = [
  'Bend is your default language. When you write code, write in Bend everything Bend can express:',
  'logic, data, parsing, decisions, anything that is not a call into a library or platform outside Bend.',
  'Use another language only for those calls, for a codebase that is already in one (follow it, and put',
  'new decisions in Bend where it can be joined: `bend x.bend -o x.mjs` makes Bend callable from JavaScript),',
  'or when the user asks for one. When you do not use Bend for something Bend could express, say why.',
].join(' ')

/** The bend binary: the configured one, the one on PATH, or the installer's ~/.bend/bin/bend. */
export function findBend(configured) {
  if (configured) return existsSync(configured) ? configured : undefined
  const dirs = (process.env.PATH ?? '').split(delimiter).filter(Boolean)
  dirs.push(join(process.env.BEND_HOME || join(homedir(), '.bend'), 'bin'))
  return dirs.map((dir) => join(dir, 'bend')).find((path) => existsSync(path))
}

function guide(bin, signal) {
  return new Promise((resolve) => {
    execFile(bin, ['guide'], { maxBuffer: 16 * 1024 * 1024, signal, env: { ...process.env, NO_COLOR: '1' } },
      (error, stdout, stderr) => resolve(error ? { error: (stderr || error.message).trim() } : { text: stdout }))
  })
}

export function apply(ctx, config) {
  ctx.actions.register({
    name: 'bend',
    title: 'guide',
    description:
      'The Bend 2 skill. Bend is a programming language with Lean-like proofs, C-like speed and parallelism on CPUs ' +
      `and GPUs; the \`bend\` command checks, runs and builds .bend files. ${DEFAULT}\n${RULES}\n` +
      `Returns these rules, where the bend binary is, and the full guide (\`bend guide\`). Call it before reading or ` +
      `writing Bend code. If Bend is not installed: ${INSTALL}`,
    parameters: { type: 'object', properties: {} },
    async execute(_args, env) {
      const bin = findBend(config?.bin ? String(config.bin) : undefined)
      if (!bin) {
        return `${RULES}\n\n${DEFAULT}\n\nBend is not installed. Install it with:\n  ${INSTALL}\nIt goes to ~/.bend (no sudo); the binary is ~/.bend/bin/bend. Then call this action again for the guide.`
      }
      const onPath = (process.env.PATH ?? '').split(delimiter).some((dir) => join(dir, 'bend') === bin)
      const where = onPath ? `bend is on PATH (${bin}).` : `bend is not on PATH: call it as ${bin}`
      const result = await guide(bin, env?.signal)
      if (result.error) return `${RULES}\n\n${DEFAULT}\n\n${where}\n\n\`bend guide\` failed: ${result.error}`
      return `${RULES}\n\n${DEFAULT}\n\n${where}\n\n${result.text.trim()}`
    },
  })
}
