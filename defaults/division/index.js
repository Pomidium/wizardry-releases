// division: a large task cut in two, each half done by its own agent at the same time.
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. It ships in wizardry's
// `defaults/` folder and is switched on for everyone. Switch it off with `plugin_unload division`
// (persist: true); change it by copying this folder to ~/.wizardry/plugins/division and editing the
// copy, which is loaded instead of this one.
//
// The idea: what lets two agents work on one codebase at once, without waiting for each other and
// without undoing each other, is the laws at the place where their work meets. The agent with the
// task writes those laws in Bend (https://bend-lang.com), hands each half the files it owns and the
// laws it must prove, and both halves start together. Each can count on the other's laws before
// their proofs exist, because a law says what will be true. A half that finds divisible work cuts itself
// again. When the halves are back, one check (`bend PROOF.bend`) says whether the pieces fit.
//
// The user chooses what the halves run on with /division: `/division model` and `/division thinking`
// open a list, `/division model <provider/id>` and `/division thinking <level>` set it outright, and
// `same` goes back to following the session. The choice is kept in ~/.wizardry/division.json.
//
// It is for large tasks only. Nothing is ever applied for the agent: it chooses to call `division`,
// and `division_split` refuses a cut whose halves are under a chunk of work, since an agent costs
// more to start than that saves.
//
// Every decision is made in Bend (division.bend, compiled to core.mjs) and the ones that must hold
// for every cut are proven (LAWS.bend, PROOF.bend): two halves can never write the same file, a
// half never owns more than the agent that cut, every law has one prover, and small tasks are not
// cut. This file only does what Bend cannot: it starts the agents, stops a write to a file an agent
// was not handed, and runs the check.
//
// Config (optional, in ~/.wizardry/division.json):
//   { "chunkMinutes": 15,     a half under this is not worth an agent
//     "depth": 3,             how many times a task may be cut in two on the way down
//     "timeoutMinutes": 60,   how long one agent may take before it is stopped
//     "model": "",            the model the halves run on, as provider/id; empty: the session's
//     "thinking": "",         their thinking level; empty: the session's
//     "agent": ["cmd", ...] } what to run for a half, the prompt as its last argument
//                             (default: this wizardry, headless)

import { spawn } from 'node:child_process'
import { appendFileSync, existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs'
import { isAbsolute, join, relative, resolve } from 'node:path'
import bend from './core.mjs'

export const name = 'division'
export const inject = ['plugins']

/** What a half is told about its place in the tree, handed down in this variable. */
const PLACE = 'WIZARDRY_DIVISION'

export const DEFAULTS = { chunkMinutes: 15, depth: 3, timeoutMinutes: 60, model: '', thinking: '' }

// ---- the crossing to Bend: arrays in, answers out, no decisions -------------------------------

const list = (items) => items.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const array = (items) => { const out = []; for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head); return out }
const some = (value) => (value.$ === 'Some' ? value.value : undefined)
const owns = (entries) => (entries ? { $: 'Only', entries: list(entries) } : { $: 'All' })
const piece = ({ name, owns, laws, minutes }) => ({ $: 'Piece', name, owns: list(owns), laws: list(laws), minutes })
const ended = (result) => ({ $: 'Ended', code: Number.isInteger(result.code) && result.code >= 0 ? result.code : 1, stopped: result.failed ?? '' })
const standing = (place) => (place ? { $: 'Half', depth: place.depth, name: place.name, owns: list(place.owns), laws: list(place.laws), check: place.check } : { $: 'Whole' })

export const core = {
  /** Whether an agent that owns `entries` (undefined: everything) may write `path`. */
  may: (entries, path) => bend.may(owns(entries), path),
  /** Whether a cut is made: "Divide", or the reason it is not. */
  judge(depth, limit, chunk, parent, first, second) {
    const verdict = bend.judge(depth, limit, chunk, owns(parent), piece(first), piece(second))
    return verdict.$ === 'Divide' ? 'Divide' : verdict.why.$
  },
  /** Why a cut is not made, in words. */
  why: (reason, cfg) => bend.why({ $: reason }, cfg.chunkMinutes, cfg.depth),
  refused: (why) => bend.refused(why),
  /** The names of the laws a Bend file declares. */
  lawsIn: (text) => array(bend.laws_in(text)),
  /** The laws named that no file declares. */
  missing: (named, declared) => array(bend.missing(list(named), list(declared))),
  lawsMissing: (names) => bend.laws_missing(list(names)),
  /** A path as the laws take it, from where it is relative to the task; undefined outside it. */
  entryOf: (rel, absolute, folder) => some(bend.entry_of(rel, absolute, folder)),
  /** What a half runs on: the user's choice, and otherwise what the session is on. */
  runsOn: (choice, session) => bend.runs_on(choice ?? '', session ?? ''),
  /** The choice that is kept: "same" is none. */
  kept: (value) => bend.kept(value),
  /** The thinking levels a half can be given, and "same". */
  levels: () => array(bend.levels()),
  /** What /division was asked for, by its first word: "Show", "Model", "Thinking" or "Unclear". */
  wants: (word) => bend.wants(word).$,
  showing: (model, sessionModel, thinking, sessionThinking) => bend.showing(model ?? '', sessionModel ?? '', thinking ?? '', sessionThinking ?? ''),
  /** The options a half is started with. */
  halfArgs: (model, sessionModel, thinking, sessionThinking) => array(bend.half_args(model ?? '', sessionModel ?? '', thinking ?? '', sessionThinking ?? '')),
  /** A half's state while the other still works, and how it ended once it has. */
  state: (result) => bend.state(ended(result)),
  halfReport: (half, result) => bend.half_report(half.name, list(half.owns), list(half.laws), ended(result), Math.max(0, Math.round(result.ms)), result.out, result.err),
  /** Whether the halves fit, by how the check ended and what it printed. */
  fits: (result, said) => bend.fits(ended(result), said),
  joined: (ms, reports, check, fit, result, said) => bend.joined(Math.max(0, Math.round(ms)), list(reports), check, fit, result.failed ?? '', said),
  stoppedEarly: () => bend.stopped_early(),
  notYours: (path, name, entries) => bend.not_yours(path, name, list(entries)),
  method: (cfg, place) => bend.method(cfg.chunkMinutes, cfg.depth, standing(place)),
  brief: (half, other, whole, check, cfg) =>
    bend.brief(half.name, half.task, list(half.owns), list(half.laws), other.name, other.task, list(other.laws), whole ?? '', check, cfg.chunkMinutes),
  describeDivision: (cfg) => bend.describe_division(cfg.chunkMinutes),
  describeSplit: (cfg) => bend.describe_split(cfg.chunkMinutes),
}

// ---- files: what only Node can say ------------------------------------------------------------

/** A path as Bend takes it: relative to the root, "/" between names, a folder ending in "/". Undefined when outside the root. */
export function entry(root, path, folder) {
  const absolute = isAbsolute(path) ? path : resolve(root, path)
  const rel = relative(root, absolute)
  const isFolder = folder ?? (/[\\/]$/.test(path) || (existsSync(absolute) && statSync(absolute).isDirectory()))
  // Whether it is inside, and how it is written, is decided in Bend.
  return core.entryOf(rel, isAbsolute(rel), isFolder)
}

/** How many folders are read looking for laws before giving up: a task started in a home directory is not searched whole. */
const FOLDERS = 3000

/**
 * The names of the laws declared in the .bend files under `root`. `partial` is set on the answer
 * when there were too many folders to read them all, so that a law not found is not called missing.
 */
export function declaredLaws(root) {
  const laws = new Set()
  let folders = 0
  const walk = (dir, depth) => {
    if (depth > 8 || laws.partial) return
    if (++folders > FOLDERS) return void (laws.partial = true)
    for (const item of readdirSync(dir, { withFileTypes: true })) {
      if (item.name.startsWith('.') || item.name === 'node_modules' || item.name === 'Library') continue
      const path = join(dir, item.name)
      if (item.isDirectory()) {
        try { walk(path, depth + 1) } catch {}
      } else if (item.name.endsWith('.bend')) {
        // Which lines declare a law is decided in Bend.
        try { for (const law of core.lawsIn(readFileSync(path, 'utf8'))) laws.add(law) } catch {}
      }
    }
  }
  try { walk(root, 0) } catch {}
  return laws
}

export const method = (cfg, place) => core.method(cfg, place)
export const brief = (half, other, whole, check, cfg) => core.brief(half, other, whole, check, cfg)
/** The options a half is started with, so that it runs on the user's choice, or else on what the session is on. */
export const halfArgs = (cfg, sessionModel, sessionThinking) => core.halfArgs(cfg.model, sessionModel, cfg.thinking, sessionThinking)

// ---- running ---------------------------------------------------------------------------------

/** Run a command and resolve with how it ended and what it printed. Never rejects. */
function run(command, args, { cwd, env, timeoutMs, signal, shell }) {
  return new Promise((done) => {
    const started = Date.now()
    let out = ''
    let err = ''
    let ended = false
    const finish = (how) => {
      if (ended) return
      ended = true
      clearTimeout(timer)
      signal?.removeEventListener('abort', stop)
      done({ ...how, out: out.trim(), err: err.trim(), ms: Date.now() - started })
    }
    let child
    try {
      child = spawn(command, args, { cwd, env, shell, stdio: ['ignore', 'pipe', 'pipe'] })
    } catch (error) {
      return finish({ code: 1, failed: String(error?.message ?? error) })
    }
    let why
    const stop = () => { why ??= 'stopped'; child.kill('SIGTERM') }
    const timer = setTimeout(() => { why = 'timed out'; child.kill('SIGTERM') }, timeoutMs)
    timer.unref?.()
    signal?.addEventListener('abort', stop, { once: true })
    child.stdout.on('data', (chunk) => { out += chunk })
    child.stderr.on('data', (chunk) => { err += chunk })
    child.on('error', (error) => finish({ code: 1, failed: String(error.message) }))
    child.on('close', (code) => finish({ code: code ?? 1, failed: why }))
  })
}

export function apply(ctx, config) {
  const home = ctx.plugins.home
  let saved = {}
  try { saved = JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')) } catch {}
  const cfg = { ...DEFAULTS, ...saved, ...(config ?? {}) }

  /** Where this agent stands: undefined for the one with the whole task. */
  let place
  try { place = process.env[PLACE] ? JSON.parse(process.env[PLACE]) : undefined } catch {}

  if (place) {
    // A half writes only what it was handed. Which paths those are is decided in Bend, where it is
    // proven that no path is both halves' to write; here the write that is not is refused.
    ctx.on('action/before', (action, params) => {
      if (action.name !== 'write' && action.name !== 'edit') return
      const path = params?.path
      if (typeof path !== 'string') return
      // Pi's file tools take a relative path from where the process stands, so that is where it is read from.
      const rel = entry(place.root, isAbsolute(path) ? path : resolve(process.cwd(), path), false)
      if (rel !== undefined && core.may(place.owns, rel)) return
      return core.notYours(path, place.name, place.owns)
    })
    // A half is not the user's session: what it is told is not something the user said, so it is
    // kept out of memory. The agent that cut the task remembers the whole.
    ctx.on('pi/ready', () => {
      try {
        if (ctx.plugins.list().some((plugin) => plugin.name === 'memory')) ctx.plugins.unload('memory').catch(() => {})
      } catch {}
    })
  }

  /** Keep a choice for this session and the ones after it, beside whatever else the file holds. */
  const keep = (key, value) => {
    cfg[key] = value
    let file = {}
    try { file = JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')) } catch {}
    mkdirSync(home, { recursive: true })
    writeFileSync(join(home, 'division.json'), `${JSON.stringify({ ...file, [key]: value }, null, 2)}\n`)
  }
  const sessionModel = (piCtx) => (piCtx?.model ? `${piCtx.model.provider}/${piCtx.model.id}` : '')
  const sessionThinking = () => {
    try { return String(ctx.root.get('pi')?.api?.getThinkingLevel?.() ?? '') } catch { return '' }
  }
  const showing = (piCtx) => core.showing(cfg.model, sessionModel(piCtx), cfg.thinking, sessionThinking())

  // The user's, not the agent's: which model its halves run on is not the agent's to choose.
  try {
    ctx.root.get('pi')?.command('division', {
      description: 'What the agents division starts run on; "/division model" and "/division thinking" choose',
      words: ['model', 'thinking'],
      async run(args, piCtx) {
        const [word = '', ...more] = args.split(/\s+/).filter(Boolean)
        let value = more.join(' ')
        // What was asked for is decided in Bend, as is what a choice comes to (division.bend).
        const asked = core.wants(word)
        if (asked === 'Show') return piCtx.ui.notify(showing(piCtx), 'info')
        if (asked === 'Unclear') return piCtx.ui.notify('Usage: /division, /division model [provider/id|same], /division thinking [level|same]', 'warning')
        if (asked === 'Model') {
          const known = piCtx.modelRegistry.getAvailable().map((model) => `${model.provider}/${model.id}`)
          if (!value) value = (await piCtx.ui.select('The model division\'s agents run on', ['same (as this session)', ...known]))?.split(' ')[0] ?? ''
          if (!value) return
          if (value !== 'same' && !known.includes(value)) {
            const close = known.filter((each) => each.includes(value))
            if (close.length !== 1) return piCtx.ui.notify(`No model "${value}" is signed in${close.length ? `; did you mean ${close.slice(0, 5).join(', ')}?` : '. /division model lists them.'}`, 'warning')
            value = close[0]
          }
          keep('model', core.kept(value))
        } else {
          const levels = core.levels()
          if (!value) value = (await piCtx.ui.select('The thinking level division\'s agents run on', ['same (as this session)', ...levels.slice(1)]))?.split(' ')[0] ?? ''
          if (!value) return
          if (!levels.includes(value)) return piCtx.ui.notify(`No thinking level "${value}". Choose from: ${levels.join(', ')}`, 'warning')
          keep('thinking', core.kept(value))
        }
        piCtx.ui.notify(showing(piCtx), 'info')
      },
    })
  } catch {}

  const log = (root, record) => {
    try {
      const dir = join(home, 'division')
      mkdirSync(dir, { recursive: true })
      appendFileSync(join(dir, 'runs.jsonl'), `${JSON.stringify({ at: new Date().toISOString(), root, ...record })}\n`)
    } catch {}
  }

  ctx.actions.register({
    name: 'division',
    title: 'division method',
    description: core.describeDivision(cfg),
    parameters: { type: 'object', properties: {} },
    execute: () => method(cfg, place),
  })

  const half = {
    type: 'object',
    properties: {
      name: { type: 'string', description: 'A short name for this half.' },
      task: { type: 'string', description: 'What this half is to do, in full: its agent starts from nothing and sees only this, the other half\'s task and the files.' },
      owns: { type: 'array', items: { type: 'string' }, description: 'The files and folders (ending in "/") only this half may write.' },
      laws: { type: 'array', items: { type: 'string' }, description: 'The names of the laws this half must prove, already declared in a .bend file.' },
      minutes: { type: 'number', description: 'How many minutes of work you take this half to be for one agent.' },
    },
    required: ['name', 'task', 'owns', 'laws', 'minutes'],
  }

  ctx.actions.register({
    name: 'division_split',
    title: 'division split',
    description: core.describeSplit(cfg),
    parameters: {
      type: 'object',
      properties: {
        first: half,
        second: half,
        whole: { type: 'string', description: 'The task being cut, in a few sentences, so each half knows what it is part of.' },
        check: { type: 'string', description: 'The command that says whether the halves fit. Default: bend PROOF.bend' },
      },
      required: ['first', 'second'],
    },
    async execute({ first, second, whole, check }, env) {
      const root = place?.root ?? env.cwd
      const depth = place?.depth ?? 0
      const refuse = (why) => core.refused(why)

      const halves = []
      for (const given of [first, second]) {
        const entries = (given?.owns ?? []).map((path) => entry(root, String(path)))
        if (entries.includes(undefined)) return refuse(`"${given.owns[entries.indexOf(undefined)]}" is outside ${root}`)
        halves.push({
          name: String(given?.name ?? '').trim(),
          task: String(given?.task ?? '').trim(),
          owns: entries,
          laws: (given?.laws ?? []).map((law) => String(law).trim()).filter(Boolean),
          minutes: Math.max(0, Math.floor(Number(given?.minutes) || 0)),
        })
      }
      const [a, b] = halves
      if (!a.name || !b.name || !a.task || !b.task) return refuse('each half needs a name and a task')

      // Whether the cut is made is decided in Bend (division.bend), and proven (LAWS.bend).
      const verdict = core.judge(depth, cfg.depth, cfg.chunkMinutes, place?.owns, a, b)
      if (verdict !== 'Divide') return refuse(core.why(verdict, cfg))

      const declared = declaredLaws(root)
      const missing = declared.partial ? [] : core.missing([...a.laws, ...b.laws], [...declared])
      if (missing.length) return refuse(core.lawsMissing(missing))

      const command = String(check ?? '').trim() || 'bend PROOF.bend'
      if (!check && !existsSync(join(root, 'PROOF.bend'))) return refuse('there is no PROOF.bend here to check the halves with; make the gate first, or pass `check`')

      // Each half runs on what the user chose with /division, and otherwise on what this agent is on:
      // which of the two is decided in Bend, where it is proven that a choice always wins.
      const chosen = halfArgs(cfg, sessionModel(env.pi), sessionThinking())
      const agent = Array.isArray(cfg.agent) && cfg.agent.length
        ? cfg.agent.map(String)
        : [process.execPath, ...process.execArgv, process.argv[1], '-p', '--no-session', ...chosen]

      const state = {}
      const tell = () => env.update?.(halves.map((each) => `${each.name}: ${state[each.name] ?? 'working'}`).join('\n'))
      const start = (each, other) => {
        const next = { root, depth: depth + 1, name: each.name, owns: each.owns, laws: each.laws, check: command }
        return run(agent[0], [...agent.slice(1), brief(each, other, whole && String(whole), command, cfg)], {
          cwd: root,
          env: { ...process.env, [PLACE]: JSON.stringify(next), WIZARDRY_NO_UPDATE: '1' },
          timeoutMs: cfg.timeoutMinutes * 60_000,
          signal: env.signal,
        }).then((result) => {
          state[each.name] = core.state(result)
          tell()
          return result
        })
      }
      tell()
      log(root, { event: 'cut', depth, runsOn: chosen, halves: halves.map(({ name, owns, laws, minutes }) => ({ name, owns, laws, minutes })) })
      const started = Date.now()
      const results = await Promise.all([start(a, b), start(b, a)])
      if (env.signal?.aborted) return core.stoppedEarly()

      const checked = await run(command, [], { cwd: root, env: process.env, timeoutMs: 10 * 60_000, signal: env.signal, shell: true })
      const said = `${checked.out}\n${checked.err}`.trim()
      // Whether the halves fit, and what is said of each, is decided in Bend (division.bend).
      const fits = core.fits(checked, said)
      log(root, { event: 'joined', depth, fits, ms: Date.now() - started, halves: halves.map((each, i) => ({ name: each.name, code: results[i].code, failed: results[i].failed, ms: results[i].ms })) })
      return core.joined(Date.now() - started, halves.map((each, i) => core.halfReport(each, results[i])), command, fits, checked, said)
    },
  })
}
