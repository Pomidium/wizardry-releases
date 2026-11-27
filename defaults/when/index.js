// when: if-then rules for the agent. "Whenever you make a UI, make it blue."
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. Switch it off with
// `plugin_unload when` (persist: true).
//
// The idea: a preference should cost nothing until the moment it matters. So a rule is not kept in
// the standing prompt and there is no action for it in the tool list. It sits in a file,
// ~/.wizardry/when/rules.json, with cues for the states the agent can be in:
//
//   asked     the user's message                       -> said beside the message
//   thinking  the agent's own reasoning and replies    -> said with the next result it reads
//   doing     an action's name and arguments           -> the call is held once, and said instead
//   seen      an action's result                       -> said under the result
//
// The meaning of "making a UI" is worked out once, by the agent, when it writes the rule: it
// turns the condition into cues (words, paths, commands). From then on matching is string work
// done here, on every step, without a model and without a token. A rule that fires says its
// `then` (and the output of its shell command `run`, if it has one) once per session, in the
// conversation, so the prompt cache is never touched.
//
// How rules are written is itself a rule (`teach` in when.bend): the agent learns the file and the
// format only when the user sounds like they are stating a preference.
//
// Every decision is made in Bend (when.bend, compiled to core.mjs) and what must hold is proven
// (LAWS.bend, PROOF.bend): no rules, no cue or an empty cue fire nothing, a rule fires once, and
// when nothing fires not a word is said. This file only listens to Pi, reads the rules and runs `run`.
//
// By the owner's decision this plugin reaches the agent other than through an action, as memory
// does at compaction. It still adds nothing to the system prompt.

import { execFile } from 'node:child_process'
import { readFileSync, statSync } from 'node:fs'
import { join } from 'node:path'
import bend from './core.mjs'

export const name = 'when'
export const inject = ['plugins']

const STATES = ['asked', 'thinking', 'doing', 'seen']
/** The session entry that says a rule fired, so that a resumed session or a branch knows. */
const FIRED = 'when:fired'
/** How much of a text is read for cues. */
const READ = 50000

// ---- the crossing to Bend: arrays in, answers out, no decisions -------------------------------

const list = (items) => items.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const array = (items) => { const out = []; for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head); return out }
const strings = (value) => (Array.isArray(value) ? value : [value]).filter((item) => typeof item === 'string')

export const core = {
  /** Whether a cue hits a text. */
  hits: (cue, text) => bend.cue_hits(cue, bend.words(text, false)),
  /** The names of the rules that fire on `text` in `state`, less the ones in `fired`. */
  due: (rules, state, fired, text) =>
    array(bend.due(list(rules.map((rule) => ({ $: 'Rule', name: rule.name, cues: list(strings(rule.when?.[state] ?? [])) }))), list(fired), text)),
  doing: (tool, args) => bend.doing(tool, list(args)),
  note: (name, then, out) => bend.note(name, then, out),
  told: (notes) => bend.told(list(notes)),
  held: (notes) => bend.held(list(notes)),
  alsoHeld: () => bend.also_held(),
  teach: (file) => ({ name: bend.teach_name(), when: { asked: array(bend.teach_cues()) }, then: bend.teach(file) }),
  listed: (file, rules, problem) => bend.listed(file, list(rules.map((rule) => bend.listed_one(rule.name, rule.then))), problem),
}

const text = (content) => (typeof content === 'string' ? content
  : Array.isArray(content) ? content.map((part) => part?.text ?? part?.thinking ?? '').join('\n') : '')

/** What a rule's command printed. A command that fails or runs long says what it managed to. */
const sh = (command, cwd) => new Promise((resolve) => {
  execFile('/bin/sh', ['-c', command], { cwd, encoding: 'utf8', timeout: 10000, maxBuffer: 1 << 20 }, (error, stdout, stderr) =>
    resolve(`${stdout ?? ''}${error ? `${stderr ?? ''}` : ''}`.slice(0, READ)))
})

export function apply(ctx, config) {
  const file = config?.file ?? join(ctx.plugins.home, 'when', 'rules.json')
  // An agent deployed on a part of a task is not being told preferences: it is not taught.
  const taught = process.env.WIZARDRY_DIVISION ? [] : [core.teach(file)]

  let read = { stamp: '', rules: [], problem: '' }
  /** The rules on disk now. The file is read again only when it changed. */
  const rules = () => {
    let stamp = ''
    try { const stat = statSync(file); stamp = `${stat.mtimeMs}:${stat.size}` } catch {}
    if (stamp === read.stamp) return read
    read = { stamp, rules: [], problem: '' }
    if (stamp) {
      try {
        read.rules = JSON.parse(readFileSync(file, 'utf8')).filter((rule) => typeof rule?.name === 'string' && typeof rule?.then === 'string')
      } catch (error) { read.problem = String(error?.message ?? error) }
    }
    return read
  }

  let fired = []
  let waiting = []
  let step = 0
  let heldStep = -1
  let api

  /** What the rules firing on `said` in `state` say, in order. Empty nearly always. */
  const fire = async (state, said, cwd) => {
    const all = [...taught, ...rules().rules]
    const names = core.due(all, state, fired, String(said ?? '').slice(0, READ))
    const notes = []
    for (const name of names) {
      const rule = all.find((rule) => rule.name === name)
      fired.push(name)
      try { api?.appendEntry(FIRED, { name }) } catch {}
      notes.push(core.note(name, rule.then, typeof rule.run === 'string' && rule.run.trim() ? await sh(rule.run, cwd) : ''))
    }
    return notes
  }

  const handlers = {
    session_start(_event, piCtx) {
      // What fired on this branch stays fired; a compaction forgets it, since what was said is gone.
      fired = []
      waiting = []
      for (const entry of piCtx.sessionManager.getBranch()) {
        if (entry.type === 'compaction') fired = []
        if (entry.type === 'custom' && entry.customType === FIRED && typeof entry.data?.name === 'string') fired.push(entry.data.name)
      }
    },
    session_compact() { fired = [] },
    async before_agent_start(event, piCtx) {
      const notes = [...waiting.splice(0), ...await fire('asked', event.prompt, piCtx.cwd)]
      if (notes.length) return { message: { customType: 'when', content: core.told(notes), display: true } }
    },
    async message_end(event, piCtx) {
      if (event.message?.role !== 'assistant') return
      step++
      waiting.push(...await fire('thinking', text(event.message.content), piCtx.cwd))
    },
    async tool_call(event, piCtx) {
      const notes = await fire('doing', core.doing(event.toolName, Object.values(event.input ?? {}).flatMap(strings)), piCtx.cwd)
      if (notes.length) {
        heldStep = step
        return { block: true, reason: core.held([...waiting.splice(0), ...notes]) }
      }
      if (heldStep === step) return { block: true, reason: core.alsoHeld() }
    },
    async tool_result(event, piCtx) {
      const notes = [...waiting.splice(0), ...await fire('seen', text(event.content), piCtx.cwd)]
      if (notes.length) return { content: [...event.content, { type: 'text', text: core.told(notes) }] }
    },
  }

  let unhook
  const hook = (next, replace) => {
    if (!next || (unhook && !replace)) return
    try { unhook?.() } catch {}
    api = next
    const offs = Object.entries(handlers).map(([event, handler]) => next.on(event, handler))
    unhook = () => { for (const off of offs) if (typeof off === 'function') off() }
  }
  ctx.on('pi/ready', (next) => hook(next, true))
  ctx.on('pi/session-start', (next) => hook(next, false))
  try { hook(ctx.root.get('pi')?.api, false) } catch {}
  ctx.effect(() => () => { try { unhook?.() } catch {} }, 'when.hooks')

  // The user's view of the rules. The agent has none: it reads the file when it needs to.
  try {
    ctx.root.get('pi')?.command('when', {
      description: 'Show the if-then rules the agent works under',
      run(_args, piCtx) {
        const now = rules()
        piCtx.ui.notify(core.listed(file, now.rules, now.problem), now.problem ? 'warning' : 'info')
      },
    })
  } catch {}
}
