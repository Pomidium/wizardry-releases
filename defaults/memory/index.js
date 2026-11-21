// memory: what the agent remembers, within a session and across them.
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. It ships in wizardry's
// `defaults/` folder and is switched on for everyone. Switch it off with `plugin_unload memory`
// (persist: true); change it by copying this folder to ~/.wizardry/plugins/memory and editing the
// copy, which is loaded instead of this one.
//
// It is two designs in one plugin:
//
//   pi-observational-memory (https://github.com/amosblomqvist/pi-observational-memory, MIT):
//     observers turn the transcript, chunk by chunk, into short timestamped observations; when
//     the context is compacted, those observations take the place of the messages they were made
//     from, as they are; a consolidator folds the oldest into durable topics and a journey.
//   claude-mem (https://github.com/thedotmack/claude-mem, Apache-2.0):
//     everything observed is kept in one store across sessions and projects, and the agent
//     recalls it in three steps: mem_search -> mem_timeline -> mem_get_observations.
//
// There is no worker, no port and no second login. The store is a SQLite file wizardry owns
// (~/.wizardry/memory/memory.db), and the observer is a small model reached through the session's
// own model registry, so it runs on whatever the session is signed in to.
//
// Every decision is made in Bend (../memory.bend in the source repository, compiled to core.mjs
// here) and the ones that must hold for every input are proven (LAWS.bend, PROOF.bend). This file
// only does what Bend cannot: it reads the session, calls the model, and writes to the store.
//
// One deliberate exception to "a plugin reaches the agent only through actions": when Pi compacts
// the context, this plugin supplies the summary. Nothing else is added to the prompt.
//
// If what it relies on is missing (SQLite in this Node, a model with credentials), it stays out of
// the way: nothing is observed, Pi compacts by itself, and the recall actions say why.
//
// Settings (all optional), in ~/.wizardry/memory/config.json or passed by whoever loads the plugin:
//   { dir, model: "provider/id", capture: false, compaction: false, import: false,
//     chunkTokens, flushTokens, poolTargetTokens, consolidateAtPoolTokens, journeyTokens,
//     topicTokens, concurrency, timeoutMs, quitWaitMs }

import { readFileSync } from 'node:fs'
import { homedir } from 'node:os'
import { join } from 'node:path'
import bend from './core.mjs'
import { minute, openStore } from './store.js'

export const name = 'memory'

export const DEFAULTS = {
  /** Transcript tokens in one observed chunk. */
  chunkTokens: 8000,
  /** When the agent stops, a leftover this big is observed without waiting for a full chunk. */
  flushTokens: 1500,
  /** The pool of observations drains back to this after a consolidation. */
  poolTargetTokens: 10000,
  /** A project's pool past this is consolidated into topics. */
  consolidateAtPoolTokens: 15000,
  /** About how long the journey may get. */
  journeyTokens: 1000,
  /** How much of the existing topics the consolidator is shown in full. */
  topicTokens: 6000,
  /** Observers running at once. */
  concurrency: 3,
  timeoutMs: 120_000,
  /** How long quitting an interactive session waits for an observer that is still running. */
  quitWaitMs: 5000,
  capture: true,
  compaction: true,
  import: true,
}

/** Session entries this plugin writes. They are on the branch, so `/tree` takes them along. */
const START = 'memory:start'
const OBSERVED = 'memory:observed'
const SWITCH = 'memory:switch'

/** Entries handed to Bend at once: its list loops recurse, and this keeps them shallow. */
const MAX_ITEMS = 1500
const MAX_BATCH = 400
/** A tool result is shown to the observer with its middle taken out past this. */
const HEAD = 3000
const TAIL = 1000
/** At compaction, a gap of unobserved transcript bigger than this many chunks is left to Pi. */
const MAX_GAP_CHUNKS = 6

const list = (items) => items.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const array = (items) => {
  const out = []
  for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head)
  return out
}
const size = (text) => bend.tokens(text.length)
const sum = (rows) => rows.reduce((total, row) => total + Number(row.tokens), 0)

function textOf(content) {
  if (typeof content === 'string') return content
  if (!Array.isArray(content)) return ''
  return content.filter((part) => part?.type === 'text' && typeof part.text === 'string').map((part) => part.text).join('\n')
}

/** How many characters an entry puts in the context: its text, thinking and calls; an image counts as 4800. */
function charsOf(content) {
  if (typeof content === 'string') return content.length
  if (!Array.isArray(content)) return 0
  let chars = 0
  for (const part of content) {
    if (part?.type === 'text') chars += String(part.text ?? '').length
    else if (part?.type === 'thinking') chars += String(part.thinking ?? '').length
    else if (part?.type === 'toolCall') chars += String(part.name ?? '').length + brief(part.arguments, Infinity).length
    else if (part?.type === 'image') chars += 4800
  }
  return chars
}

/** The same answer as Bend's alone; the check only spares it the walk through a text with no tag. */
const strip = (text) => (text.includes('<private>') ? bend.strip_private(text) : text)

function middle(text) {
  const out = bend.elided(text.length, HEAD, TAIL)
  return out > 0 ? `${text.slice(0, HEAD)}\n[... ${out} characters left out ...]\n${text.slice(-TAIL)}` : text
}

function brief(value, room = 300) {
  let text
  try { text = JSON.stringify(value) } catch { text = '' }
  return room === Infinity ? text ?? '' : bend.clip(text ?? '', room)
}

/** An entry as the observer sees it and as Bend sizes it; undefined for entries that are not conversation. */
function source(entry) {
  const at = minute(entry.timestamp ?? Date.now())
  const make = (kind, who, text) => {
    const shown = bend.entry_text(who, at, text)
    // `tokens` is the entry as the observer reads it; `weight` is the entry as it weighs on the context.
    const weight = bend.tokens(charsOf(entry.message?.content ?? entry.content ?? entry.summary))
    return { id: entry.id, kind, at, text: shown, tokens: size(shown), weight, raw: text }
  }
  if (entry.type === 'custom_message') return make({ $: 'Other' }, 'Note', strip(textOf(entry.content)))
  if (entry.type === 'branch_summary') return make({ $: 'Other' }, 'Summary of another branch', String(entry.summary ?? ''))
  if (entry.type !== 'message' || !entry.message) return undefined
  const message = entry.message
  if (message.role === 'user') return make({ $: 'User' }, 'User', strip(textOf(message.content)))
  if (message.role === 'assistant') {
    const calls = Array.isArray(message.content) ? message.content.filter((part) => part?.type === 'toolCall') : []
    const said = [strip(textOf(message.content)), ...calls.map((call) => `-> ${call.name}(${brief(call.arguments)})`)].filter(Boolean)
    return make({ $: 'Reply', calls: calls.length > 0 }, 'Assistant', said.join('\n'))
  }
  if (message.role === 'toolResult') {
    const text = bend.skips(String(message.toolName ?? '')) ? '(a recall from memory, not repeated here)' : middle(strip(textOf(message.content)))
    return make({ $: 'Result' }, `Result of ${message.toolName ?? 'a call'}`, text)
  }
  if (message.role === 'bashExecution') return make({ $: 'Other' }, 'User ran', middle(strip(`$ ${message.command ?? ''}\n${message.output ?? ''}`)))
  return undefined
}

export function apply(ctx, config = {}) {
  let home
  try { home = ctx.root.get('plugins')?.home } catch {}
  const dir = config?.dir ?? join(home || process.env.WIZARDRY_HOME || join(homedir(), '.wizardry'), 'memory')
  // Settings for this machine sit beside the store, in config.json; what the loader passes wins.
  let saved = {}
  try {
    if (dir !== ':memory:') saved = JSON.parse(readFileSync(join(dir, 'config.json'), 'utf8'))
  } catch {}
  const cfg = { ...DEFAULTS, ...(saved && typeof saved === 'object' ? saved : {}), ...(config ?? {}) }
  let live = true
  let api
  let piCtx
  let unhook
  let lastError = ''
  const sessions = new Map()

  // ---- the store ---------------------------------------------------------------------------

  let store
  let unavailable = ''
  const ready = openStore(dir === ':memory:' ? ':memory:' : join(dir, 'memory.db')).then(async (opened) => {
    if (!live) return opened.close()
    store = opened
    if (cfg.import !== false) {
      const old = cfg.claudeMem ?? join(process.env.CLAUDE_MEM_DATA_DIR || join(homedir(), '.claude-mem'), 'claude-mem.db')
      await store.importClaudeMem(old, size).catch(() => {})
    }
  }).catch((error) => {
    unavailable = `Memory is unavailable: the store did not open (${error?.message ?? error}). It needs Node 22.13 or newer.`
  })

  // ---- the session -------------------------------------------------------------------------

  function current() {
    try {
      const id = piCtx?.sessionManager.getSessionId()
      const cwd = piCtx?.cwd
      if (!id || !cwd) return undefined
      let state = sessions.get(id)
      if (!state) {
        state = { id, flying: new Set(), jobs: new Set(), seen: new Map(), failures: 0, cost: 0, runs: 0, warned: false }
        sessions.set(id, state)
      }
      return { state, piCtx, cwd, project: bend.project(cwd) }
    } catch {
      return undefined
    }
  }

  const branchOf = (context) => {
    try {
      const entries = context.sessionManager.getBranch()
      return Array.isArray(entries) ? entries : []
    } catch {
      return []
    }
  }

  /**
   * The branch as memory reads it: the conversation in order (`sources`), which of it is observed
   * already (`covered`, by position in `sources`), where observing starts, and what was observed.
   */
  function read(state, branch) {
    const sources = []
    const at = new Map()
    const ledger = []
    let on = true
    let start
    let compaction
    const where = new Map()
    branch.forEach((entry, i) => where.set(entry.id, i))
    for (const entry of branch) {
      if (entry.type === 'custom') {
        if (entry.customType === OBSERVED && entry.data) ledger.push(entry.data)
        else if (entry.customType === START && start === undefined) start = entry.data?.from
        else if (entry.customType === SWITCH) on = entry.data?.on !== false
        continue
      }
      if (entry.type === 'compaction') { compaction = entry; continue }
      let seen = state.seen.get(entry.id)
      if (seen === undefined) {
        seen = source(entry) ?? null
        state.seen.set(entry.id, seen)
      }
      if (!seen) continue
      seen.i = where.get(entry.id)
      at.set(entry.id, sources.length)
      sources.push(seen)
    }
    const covered = new Array(sources.length).fill(false)
    const mark = (from, upTo) => {
      const a = at.get(from)
      const b = at.get(upTo)
      if (a === undefined || b === undefined) return undefined
      for (let k = a; k <= b; k++) covered[k] = true
      return b
    }
    const ends = []
    for (const record of ledger) {
      const end = mark(record.from, record.upTo)
      if (end !== undefined) ends.push({ end, ids: Array.isArray(record.ids) ? record.ids : [] })
    }
    for (const flight of state.flying) mark(flight.from, flight.upTo)
    // Where observing would start if it has not yet: after what Pi has summarized already, or at the beginning.
    const kept = compaction ? where.get(compaction.firstKeptEntryId) ?? 0 : 0
    const opening = (sources.find((entry) => entry.i >= kept) ?? sources[0])?.id
    return { sources, at, covered, ends, on, start, opening, compaction, first: start === undefined ? undefined : at.get(start) }
  }

  /** The first unbroken run of conversation not yet observed, from where observing starts. */
  function pending(view, before = Infinity) {
    const run = []
    for (let k = view.first ?? 0; k < view.sources.length && k < before && run.length < MAX_ITEMS; k++) {
      if (view.covered[k]) {
        if (run.length) break
        continue
      }
      run.push(view.sources[k])
    }
    return run
  }

  // ---- the model ---------------------------------------------------------------------------

  function modelFor(context) {
    if (cfg.complete) return { provider: 'test', id: 'test' }
    try {
      const registry = context.modelRegistry
      const session = context.model
      const ok = (model) => (model && registry.hasConfiguredAuth(model) ? model : undefined)
      if (typeof cfg.model === 'string' && cfg.model.includes('/')) {
        const cut = cfg.model.indexOf('/')
        const asked = ok(registry.find(cfg.model.slice(0, cut), cfg.model.slice(cut + 1)))
        if (asked) return asked
      }
      if (!session) return undefined
      const ids = registry.getAvailable().filter((model) => model.provider === session.provider).map((model) => model.id)
      const id = bend.pick_model(list(ids), session.id, typeof cfg.model === 'string' ? cfg.model : '')
      return ok(registry.find(session.provider, id)) ?? ok(session)
    } catch {
      return undefined
    }
  }

  async function ask(context, model, system, user) {
    if (cfg.complete) return cfg.complete({ system, user })
    const message = await context.modelRegistry.complete(model, {
      systemPrompt: system,
      messages: [{ role: 'user', content: [{ type: 'text', text: user }], timestamp: Date.now() }],
    }, { signal: AbortSignal.timeout(cfg.timeoutMs) })
    if (message.stopReason === 'error' || message.stopReason === 'aborted') {
      throw new Error(message.errorMessage || `the model stopped: ${message.stopReason}`)
    }
    return { text: textOf(message.content), cost: Number(message.usage?.cost?.total ?? 0) }
  }

  /** At most `cfg.concurrency` model calls at once. */
  let running = 0
  const waiting = []
  function limited(work) {
    return new Promise((resolve, reject) => {
      const start = () => {
        running++
        Promise.resolve().then(work).then(resolve, reject).finally(() => {
          running--
          waiting.shift()?.()
        })
      }
      if (running < Math.max(1, cfg.concurrency)) start()
      else waiting.push(start)
    })
  }

  // ---- observing ---------------------------------------------------------------------------

  const append = (state, context, type, data) => {
    // A session the user has left is not written to: what was observed is in the store all the same.
    try {
      if (!api || context.sessionManager.getSessionId() !== state.id) return false
      api.appendEntry(type, data)
      return true
    } catch {
      return false
    }
  }

  async function observe(at, model, run) {
    const { state, piCtx: context, project } = at
    const answer = await ask(context, model, bend.observer_system(), bend.observer_ask(run.map((entry) => entry.text).join('\n\n')))
    if (!live) return
    const found = array(bend.parse(answer.text, run[run.length - 1].at))
    const ids = store.addAll(found.map((o) => ({
      kind: 'observation', project, session: state.id, time: o.time, type: o.kind, text: o.text, tokens: size(o.text),
    })))
    state.cost += answer.cost ?? 0
    state.runs++
    append(state, context, OBSERVED, {
      v: 1, from: run[0].id, upTo: run[run.length - 1].id, ids, model: `${model.provider}/${model.id}`, cost: answer.cost ?? 0,
    })
  }

  function launch(at, model, run) {
    const { state } = at
    const flight = { from: run[0].id, upTo: run[run.length - 1].id }
    state.flying.add(flight)
    const job = limited(() => (live ? observe(at, model, run) : undefined))
      .then(() => {
        state.failures = 0
        return true
      }, (error) => {
        state.failures++
        lastError = `observing failed: ${error?.message ?? error}`
        if (bend.paused(state.failures) && !state.warned) {
          state.warned = true
          try {
            if (at.piCtx.mode === 'tui') at.piCtx.ui.notify(`memory has stopped observing this session: ${error?.message ?? error}`, 'warning')
          } catch {}
        }
        return false
      })
      .finally(() => {
        state.flying.delete(flight)
        state.jobs.delete(job)
      })
    state.jobs.add(job)
    return job
  }

  /** Cut what is pending into runs: the chunks Bend closes, then, when asked, the leftover. */
  function runsOf(run, leftover) {
    const runs = []
    let taken = 0
    for (const n of array(bend.chunks(list(run.map((entry) => ({ $: 'Item', tokens: entry.tokens, kind: entry.kind }))), cfg.chunkTokens))) {
      runs.push(run.slice(taken, taken + n))
      taken += n
    }
    const rest = run.slice(taken)
    if (leftover === 'all' && rest.length) runs.push(rest)
    if (leftover === 'tail' && rest.length) {
      const n = bend.tail(list(rest.map((entry) => ({ $: 'Item', tokens: entry.tokens, kind: entry.kind }))), cfg.flushTokens)
      if (n > 0) runs.push(rest.slice(0, n))
    }
    return runs
  }

  function remember(at, view) {
    for (const entry of view.sources) {
      if (entry.kind.$ !== 'User' || entry.kept || !entry.raw.trim()) continue
      entry.kept = true
      try {
        store.add({ kind: 'prompt', project: at.project, session: at.state.id, time: entry.at, text: entry.raw, tokens: size(entry.raw) })
      } catch {}
    }
  }

  let ticking = false
  let again
  /** Observe what is ready. `stopped` is set when the agent has finished and the leftover goes too. */
  async function tick(stopped) {
    if (!cfg.capture || !live) return
    if (ticking) {
      again = again || stopped
      return
    }
    ticking = true
    try {
      await ready
      const at = current()
      if (!at || !store || !api) return
      const branch = branchOf(at.piCtx)
      let view = read(at.state, branch)
      if (!view.on) return
      remember(at, view)
      if (bend.paused(at.state.failures)) return
      const model = modelFor(at.piCtx)
      if (!model) return
      if (view.start === undefined) {
        const from = view.opening
        if (from === undefined || !append(at.state, at.piCtx, START, { v: 1, from })) return
        view = { ...view, start: from, first: view.at.get(from) }
      }
      if (view.first === undefined) return
      for (const run of runsOf(pending(view), stopped ? 'tail' : 'none')) {
        void launch(at, model, run).then((ok) => (ok ? consolidate(at, model) : undefined))
      }
    } catch (error) {
      lastError = String(error?.message ?? error)
    } finally {
      ticking = false
      if (again !== undefined) {
        const next = again
        again = undefined
        void tick(next)
      }
    }
  }

  // ---- consolidating -----------------------------------------------------------------------

  const retryAt = new Map()
  /** Fold a project's oldest observations into its topics and journey, when its pool has outgrown its room. */
  async function consolidate(at, model) {
    const { project } = at
    if (!live || !store || (retryAt.get(project) ?? 0) > Date.now()) return false
    const pool = store.pool(project)
    if (!bend.over(sum(pool), cfg.consolidateAtPoolTokens)) return false
    const going = bend.promoted(list(pool.map((row) => Number(row.tokens))), cfg.poolTargetTokens)
    if (!going) return false
    const key = `folding:${project}`
    if (!store.claim(key)) return false
    try {
      const batch = pool.slice(pool.length - going).reverse().slice(0, MAX_BATCH)
      const topics = store.topics(project)
      const shown = new Set()
      let room = cfg.topicTokens
      for (const topic of topics) {
        if (Number(topic.tokens) > room) continue
        room -= Number(topic.tokens)
        shown.add(topic.type)
      }
      const answer = await ask(at.piCtx, model, bend.consolidator_system(), bend.consolidator_ask(
        minute(Date.now()), cfg.journeyTokens, store.journey(project)?.text ?? '',
        topics.map((topic) => bend.map_line(topic.type, topic.title, topic.summary)).join('\n'),
        topics.filter((topic) => shown.has(topic.type)).map((topic) => bend.topic_text(topic.type, topic.title, topic.summary, topic.text)).join('\n\n'),
        batch.map((row) => bend.obs_line({ $: 'Obs', time: row.time, kind: row.type, text: row.text })).join('\n')))
      at.state.cost += answer.cost ?? 0
      let wrote = 0
      for (const section of array(bend.sections(answer.text))) {
        const kind = bend.section_kind(section.head)
        if (kind === 'topic') {
          const doc = bend.doc(section)
          if (!doc.slug || !doc.body) continue
          const old = topics.find((topic) => topic.type === doc.slug)
          const body = bend.merged(!old || shown.has(doc.slug), old?.text ?? '', doc.body)
          store.putTopic(project, { slug: doc.slug, title: doc.title, summary: doc.summary || old?.summary || '', body, tokens: size(body) })
          wrote++
        } else if (kind === 'journey') {
          const text = bend.journey_of(section)
          if (!text) continue
          store.putJourney(project, text, size(text))
          wrote++
        }
      }
      // An answer with nothing in it folds nothing: the observations stay in the pool for the next try.
      if (!wrote) throw new Error('the consolidator wrote no topic and no journey')
      store.fold(batch.map((row) => Number(row.id)))
      retryAt.delete(project)
      return true
    } catch (error) {
      lastError = `consolidating failed: ${error?.message ?? error}`
      retryAt.set(project, Date.now() + 10 * 60_000)
      return false
    } finally {
      store.release(key)
    }
  }

  // ---- compaction --------------------------------------------------------------------------

  /** What Pi puts in place of the messages it compacts away: the observations made from them. */
  async function compact(event, context) {
    if (!cfg.compaction || !live) return undefined
    try {
      piCtx = context
      await ready
      const at = current()
      if (!at || !store) return undefined
      const { state } = at
      await Promise.all([...state.jobs])
      let view = read(state, branchOf(context))
      if (!view.on || view.first === undefined) return undefined
      const proposed = view.at.get(event.preparation.firstKeptEntryId)
      if (proposed === undefined) return undefined

      // Whatever Pi is about to compact away and nobody has observed yet is observed now.
      const gaps = []
      for (let k = view.first; k < proposed; k++) {
        if (view.covered[k]) continue
        const last = gaps[gaps.length - 1]
        if (last && last.end === k - 1) { last.run.push(view.sources[k]); last.end = k } else gaps.push({ run: [view.sources[k]], end: k })
      }
      if (gaps.length) {
        const model = modelFor(context)
        const tokens = gaps.reduce((total, gap) => total + sum(gap.run), 0)
        if (!model || tokens > cfg.chunkTokens * MAX_GAP_CHUNKS) return undefined
        const done = await Promise.all(gaps.flatMap((gap) => runsOf(gap.run.slice(0, MAX_ITEMS), 'all')).map((run) => launch(at, model, run)))
        if (done.includes(false)) return undefined
        view = read(state, branchOf(context))
      }

      // Cut where an observed chunk ends, so that nothing is both summarized and kept word for word.
      const cuts = []
      let unbroken = view.first
      while (unbroken < view.sources.length && view.covered[unbroken]) unbroken++
      for (const { end } of view.ends) {
        const next = view.sources[end + 1]
        if (end >= unbroken || !next || (next.kind.$ !== 'User' && next.kind.$ !== 'Reply')) continue
        if (cuts.some((cut) => cut.end === end)) continue
        cuts.push({ end, id: next.id, tail: view.sources.slice(end + 1).reduce((total, entry) => total + entry.weight, 0) })
      }
      const chosen = bend.nearest(list(cuts.map((cut) => cut.tail)), event.preparation.settings?.keepRecentTokens ?? 20000)
      if (chosen.$ !== 'Some') return undefined
      const cut = cuts[chosen.value]

      const ids = view.ends.filter(({ end }) => end <= cut.end).flatMap(({ ids }) => ids)
      const rows = store.byIds([...new Set(ids)]).filter((row) => !row.folded).sort((a, b) => a.epoch - b.epoch || a.id - b.id)
      // A summary Pi wrote before memory was on is the only record of what it covers: it is carried along.
      const earlier = view.compaction?.details?.memory ? view.compaction.details.earlier ?? '' : view.compaction?.summary ?? ''
      const summary = bend.block(
        store.journey(at.project)?.text ?? '',
        list(store.topics(at.project).map((topic) => ({ $: 'Topic', id: Number(topic.id), title: topic.title, summary: topic.summary }))),
        list(rows.map((row) => ({ $: 'Obs', time: row.time, kind: row.type, text: row.text }))),
        earlier)
      if (!summary) return undefined
      return {
        compaction: {
          summary,
          firstKeptEntryId: cut.id,
          tokensBefore: event.preparation.tokensBefore,
          details: { memory: true, observations: rows.length, earlier },
        },
      }
    } catch (error) {
      lastError = `compaction: ${error?.message ?? error}`
      return undefined
    }
  }

  // ---- recall: the agent's side ------------------------------------------------------------

  const line = (row) => bend.index_line(Number(row.id), row.kind === 'observation' ? row.type || row.kind : row.kind, row.time, row.project,
    row.kind === 'topic' ? `${row.title}: ${row.summary}` : row.title ? `${row.title}: ${row.text}` : row.text, Number(row.tokens))

  const recall = (action, run) => ctx.actions.register({
    ...action,
    async execute(params, env) {
      await ready
      if (!store) return unavailable || 'Memory is unavailable.'
      try {
        if (env?.pi) piCtx = env.pi
        return run(params ?? {}, bend.project(env?.cwd ?? process.cwd()))
      } catch (error) {
        return `Memory request failed: ${error?.message ?? error}`
      }
    },
  })

  const scope = (asked, mine) => (asked === 'all' ? undefined : asked || mine)

  recall({
    name: 'mem_search',
    title: 'memory search',
    description: 'Search memory: what was said, done, decided, fixed and learned in this and past sessions on this machine, and the topics ' +
      'kept for each project. Returns a compact index of ids. Step 1 of 3: look around a hit with mem_timeline, then read only the ids ' +
      'worth reading with mem_get_observations. With no query it returns what memory holds for the project: its journey, its topics and ' +
      'the latest observations.',
    parameters: {
      type: 'object',
      properties: {
        query: { type: 'string', description: 'Words to look for. Any of them may match; the best matches come first.' },
        project: { type: 'string', description: 'A project (normally a directory name), or "all". Default: the current one.' },
        kind: { type: 'string', enum: ['observation', 'prompt', 'topic', 'journey'], description: 'Only this kind of memory.' },
        limit: { type: 'integer', minimum: 1, maximum: 50, description: 'Default 10.' },
      },
    },
  }, (params, mine) => {
    const project = scope(params.project, mine)
    const query = String(params.query ?? '').trim()
    const limit = Math.min(50, Math.max(1, Number(params.limit) || 10))
    const match = bend.fts(query)
    if (!match) {
      const parts = []
      const journey = project && !params.kind ? store.journey(project) : undefined
      if (journey) parts.push(`Journey of ${project} (#${journey.id}):\n${journey.text}`)
      const topics = project && !params.kind ? store.topics(project) : []
      if (topics.length) parts.push(`Topics:\n${topics.map(line).join('\n')}`)
      const recent = store.search({ project, kind: params.kind ?? 'observation', limit })
      if (recent.length) parts.push(`Latest:\n${recent.map(line).join('\n')}`)
      return parts.length ? parts.join('\n\n') : bend.nothing('', project ?? 'all')
    }
    const rows = store.search({ match, project, kind: params.kind, limit })
    return rows.length ? rows.map(line).join('\n') : bend.nothing(query, project ?? 'all')
  })

  recall({
    name: 'mem_timeline',
    title: 'memory timeline',
    description: 'What happened around a memory: the observations and prompts of its project just before and after an id (anchor), or ' +
      'around the best match for a query. Supply exactly one of anchor or query.',
    parameters: {
      type: 'object',
      properties: {
        anchor: { type: ['integer', 'string'], description: 'An id from mem_search.' },
        query: { type: 'string' },
        project: { type: 'string' },
        depth_before: { type: 'integer', minimum: 0, maximum: 50 },
        depth_after: { type: 'integer', minimum: 0, maximum: 50 },
      },
    },
  }, (params, mine) => {
    let id = Number(String(params.anchor ?? '').replace(/^#/, ''))
    if (!params.anchor) {
      const match = bend.fts(String(params.query ?? ''))
      if (!match) return 'Supply an anchor (an id from mem_search) or a query.'
      id = Number(store.search({ match, project: scope(params.project, mine), limit: 1 })[0]?.id)
    }
    const depth = (value) => Math.min(50, Math.max(0, Number.isFinite(Number(value)) && value !== undefined ? Number(value) : 5))
    const found = Number.isFinite(id) ? store.around(id, depth(params.depth_before), depth(params.depth_after)) : undefined
    if (!found) return params.anchor ? `No memory has the id ${params.anchor}.` : bend.nothing(String(params.query), scope(params.project, mine) ?? 'all')
    return found.rows.map((row) => `${Number(row.id) === id ? '>' : ' '} ${line(row)}`).join('\n')
  })

  recall({
    name: 'mem_get_observations',
    title: 'memory read',
    description: 'The full text of the memories with these ids, found by mem_search or mem_timeline. A topic id returns the whole topic.',
    parameters: {
      type: 'object',
      properties: { ids: { type: 'array', items: { type: 'integer', minimum: 1 }, minItems: 1, maxItems: 100 } },
      required: ['ids'],
    },
  }, (params) => {
    const ids = (Array.isArray(params.ids) ? params.ids : []).map(Number).filter(Number.isFinite)
    const rows = store.byIds(ids)
    if (!rows.length) return 'No memory has any of those ids.'
    return rows.map((row) => bend.detail(Number(row.id), row.kind === 'observation' ? row.type || row.kind : row.kind, row.time, row.project,
      row.session || '-', row.kind === 'topic' ? `${row.title}: ${row.summary}` : row.title, row.text)).join('\n\n')
  })

  // ---- the user's side ---------------------------------------------------------------------

  async function status() {
    await ready
    if (!store) return unavailable
    const at = current()
    if (!at) return `memory: ${store.file}`
    const view = read(at.state, branchOf(at.piCtx))
    const counts = store.counts(at.project)
    const model = modelFor(at.piCtx)
    const waitingFor = pending(view)
    return [
      `memory is ${view.on && cfg.capture ? 'on' : 'off'} for this session; project "${at.project}"`,
      `store: ${store.file}`,
      `kept for this project: ${counts.observation ?? 0} observations, ${counts.topic ?? 0} topics, ${counts.prompt ?? 0} prompts; pool ${sum(store.pool(at.project))} of ${cfg.consolidateAtPoolTokens} tokens`,
      `observer: ${model ? `${model.provider}/${model.id}` : 'no model with credentials, so nothing is observed'}`,
      `this session: ${at.state.runs} chunks observed, ${at.state.flying.size} in flight, ${sum(waitingFor)} tokens waiting, $${at.state.cost.toFixed(4)} spent`,
      ...(lastError ? [`last error: ${lastError}`] : []),
    ].join('\n')
  }

  try {
    ctx.root.get('pi')?.command('memory', {
      description: 'What memory holds and is doing; "/memory off" and "/memory on" switch it for this session',
      words: ['on', 'off'],
      async run(args, context) {
        if (!live) return
        piCtx = context
        if (args === 'on' || args === 'off') {
          const at = current()
          if (at) {
            append(at.state, context, SWITCH, { on: args === 'on' })
            if (args === 'on') { at.state.failures = 0; at.state.warned = false }
          }
          return context.ui.notify(`Memory is ${args} for this session.`, 'info')
        }
        context.ui.notify(await status(), 'info')
      },
    })
  } catch {}

  // ---- wiring ------------------------------------------------------------------------------

  /**
   * Pi waits for this before a session ends, so an observer that has just been started gets to
   * finish and record what it saw. Not for long in a terminal, where the user is waiting to leave;
   * what is cut off is observed when the session is opened again.
   */
  async function leave(_event, context) {
    const jobs = [...sessions.values()].flatMap((state) => [...state.jobs])
    if (!jobs.length) return
    let timer
    const wait = context?.mode === 'tui' ? cfg.quitWaitMs : cfg.timeoutMs
    await Promise.race([Promise.all(jobs), new Promise((resolve) => { timer = setTimeout(resolve, wait) })])
    clearTimeout(timer)
  }

  function hook(next, replace) {
    if (!next || (unhook && !replace)) return
    try { unhook?.() } catch {}
    api = next
    const offs = [next.on('session_before_compact', compact), next.on('session_shutdown', leave)]
    unhook = () => { for (const off of offs) if (typeof off === 'function') off() }
  }

  ctx.on('pi/ready', (next) => hook(next, true))
  ctx.on('pi/session-start', (next, context) => {
    hook(next, false)
    piCtx = context
    void tick(false)
  })
  // Also how a plugin loaded mid-session learns which session it is in.
  ctx.on('action/before', (_action, _params, env) => { if (env?.pi) piCtx = env.pi })
  ctx.on('action/after', () => { void tick(false) })
  ctx.on('task/end', () => { void tick(true) })
  try { hook(ctx.root.get('pi')?.api, false) } catch {}

  ctx.effect(() => () => {
    live = false
    try { unhook?.() } catch {}
    void ready.then(() => store?.close())
  })

  // For tests: the same things the events do, awaitable.
  if (cfg.expose) {
    Object.assign(cfg.expose, {
      tick, compact, status, consolidate,
      settle: async () => {
        await ready
        for (let quiet = 0; quiet < 2;) {
          const jobs = [...sessions.values()].flatMap((state) => [...state.jobs])
          if (jobs.length || ticking) quiet = 0
          else quiet++
          await Promise.all(jobs)
          await new Promise((resolve) => setTimeout(resolve, 5))
        }
      },
      store: () => store,
    })
  }
}

/** The parts a test drives directly. */
export const internals = { source, list, array }
