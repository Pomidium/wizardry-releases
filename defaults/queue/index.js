// queue: tasks that wait their turn. "After this, fix the tests, then write the changelog."
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. Switch it off with
// `plugin_unload queue` (persist: true).
//
// The idea: when the agent is completely done with a task, the first task waiting is handed to
// it as the next message, at once, and so on until nothing waits. Tasks get on the list two ways:
// the user types `/queue <task>`, or says it and the agent calls the `queue` action.
//
// "Completely done" is Pi's `agent_settled`: the run is over and no retry, compaction or message
// the user typed meanwhile is still to come. A task the user stopped (Escape) or one that ended
// in an error was not done, so the queue is held with what waits in it until `/queue go`; so is a
// queue found in a session that is opened again.
//
// The queue belongs to the conversation: it is kept as `queue:state` entries in the session, so
// it survives a restart, comes back with a resumed session, follows a branch, and is exported
// with the conversation. Nothing is kept anywhere else.
//
// Every decision is made in Bend (queue.bend, compiled to core.mjs) and what must hold is proven
// (LAWS.bend, PROOF.bend): nothing starts while the agent works, while the queue is held or when
// it is empty; a stopped or failed task never runs on into the next; first in, first out. This
// file only listens to Pi, keeps the list and hands the next task over.

import bend from './core.mjs'

export const name = 'queue'

/** The session entry that holds the queue as it stands. The last one on the branch counts. */
const STATE = 'queue:state'

// ---- the crossing to Bend: arrays in, answers out, no decisions -------------------------------

const list = (items) => items.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const array = (items) => { const out = []; for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head); return out }
const strings = (value) => (Array.isArray(value) ? value : [value]).filter((item) => typeof item === 'string')

export const core = {
  add: (items, tasks) => array(bend.add(list(items), list(tasks))),
  drop: (items, n) => array(bend.drop(list(items), n)),
  next: (items) => bend.next(list(items)),
  rest: (items) => array(bend.rest(list(items))),
  starts: (busy, paused, items) => bend.starts(busy, paused, list(items)),
  pauses: (paused, aborted, failed, items) => bend.pauses(paused, aborted, failed, list(items)),
  /** `/queue ...` as { $: 'Show' | 'Clear' | 'Pause' | 'Go' } | { $: 'Drop', n } | { $: 'Add', task }. */
  command: (args) => bend.command(args),
  listed: (items, paused) => bend.listed(list(items), paused),
  told: (items, paused) => bend.told(list(items), paused),
  starting: (task, left) => bend.starting(task, list(left)),
  held: (aborted, failed, items) => bend.held(aborted, failed, list(items)),
  said: { paused: () => bend.paused_now(), cleared: () => bend.cleared(), busyGo: () => bend.busy_go() },
  about: { action: () => bend.about(), add: () => bend.about_add(), drop: () => bend.about_drop(), clear: () => bend.about_clear() },
}

export function apply(ctx) {
  // An agent deployed on a part of a task has one task, and ends with it.
  if (process.env.WIZARDRY_DIVISION) return

  let items = []
  let paused = false
  /** Whether the last thing the agent said ended in an error. */
  let failed = false
  let api
  let live

  const save = () => { try { api?.appendEntry(STATE, { items, paused }) } catch {} }
  const notify = (piCtx, text, kind = 'info') => { try { piCtx?.ui?.notify(text, kind) } catch {} }
  const idle = (piCtx) => { try { return !!piCtx?.isIdle() } catch { return false } }

  /** Hand over the task whose turn it is, if it starts now. Whether it does is Bend's answer. */
  const run = (piCtx, busy) => {
    if (!api || !core.starts(busy, paused, items)) return false
    const task = core.next(items)
    items = core.rest(items)
    save()
    notify(piCtx, core.starting(task, items))
    try { api.sendUserMessage(task) } catch (error) {
      // Not handed over, so not lost: it goes back to the front and the queue is held.
      items = [task, ...items]
      paused = true
      save()
      notify(piCtx, String(error?.message ?? error), 'warning')
      return false
    }
    return true
  }

  /** The queue as the conversation left it. One with tasks in it is held until the user says go. */
  const restore = (piCtx) => {
    live = piCtx
    items = []
    paused = false
    failed = false
    let found = false
    try {
      for (const entry of piCtx.sessionManager.getBranch()) {
        if (entry.type !== 'custom' || entry.customType !== STATE) continue
        items = strings(entry.data?.items ?? [])
        paused = entry.data?.paused === true
        found = true
      }
    } catch {}
    if (!found) return
    const was = paused
    paused = core.pauses(paused, true, false, items)
    if (paused && !was) save()
    if (paused && items.length) notify(piCtx, core.held(false, false, items))
  }

  const handlers = {
    session_start(_event, piCtx) { restore(piCtx) },
    session_tree(_event, piCtx) { restore(piCtx) },
    message_end(event) {
      if (event.message?.role === 'assistant') failed = event.message.stopReason === 'error'
    },
    agent_settled(event, piCtx) {
      live = piCtx
      const aborted = event?.aborted === true
      const was = paused
      paused = core.pauses(paused, aborted, failed, items)
      if (paused && !was) {
        save()
        notify(piCtx, core.held(aborted, failed, items), 'warning')
      }
      failed = false
      // Pi runs a message sent from here as soon as this handler has returned.
      run(piCtx, false)
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
  ctx.effect(() => () => { try { unhook?.() } catch {} }, 'queue.hooks')

  // The agent's way onto the list: what the user says in passing ("after this, do X").
  ctx.actions.register({
    name: 'queue',
    description: core.about.action(),
    parameters: {
      type: 'object',
      properties: {
        add: { type: 'array', items: { type: 'string' }, description: core.about.add() },
        drop: { type: 'integer', minimum: 1, description: core.about.drop() },
        clear: { type: 'boolean', description: core.about.clear() },
      },
    },
    execute({ add, drop, clear } = {}) {
      const before = JSON.stringify(items)
      if (clear === true) items = []
      if (Number.isInteger(drop) && drop > 0) items = core.drop(items, drop)
      if (add !== undefined) items = core.add(items, strings(add))
      if (JSON.stringify(items) !== before) save()
      return core.told(items, paused)
    },
  })

  // The user's way: `/queue <task>` adds one, and a few words steer it.
  try {
    ctx.root.get('pi')?.command('queue', {
      description: 'Queue a task for when the agent is done, or show, hold and empty the queue',
      words: ['go', 'pause', 'clear', 'drop'],
      run(args, piCtx) {
        live = piCtx
        const command = core.command(args)
        if (command.$ === 'Show') return notify(piCtx, core.listed(items, paused))
        if (command.$ === 'Clear') {
          items = []
          paused = false
          save()
          return notify(piCtx, core.said.cleared())
        }
        if (command.$ === 'Pause') {
          paused = true
          save()
          return notify(piCtx, core.said.paused())
        }
        if (command.$ === 'Drop') {
          items = core.drop(items, Number(command.n))
          save()
          return notify(piCtx, core.listed(items, paused))
        }
        const going = command.$ === 'Go'
        if (going) paused = false
        else items = core.add(items, [command.task])
        save()
        // With the agent on nothing, the next task starts here and now.
        if (run(piCtx, !idle(piCtx))) return
        notify(piCtx, going && items.length ? core.said.busyGo() : core.listed(items, paused))
      },
    })
  } catch {}
}
