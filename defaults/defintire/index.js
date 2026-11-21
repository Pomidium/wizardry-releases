// defintire: say what a thing is, in mathematical form, so that it can be measured and then improved.
//
// A DEFAULT plugin, not an intrinsic one: wizardry runs the same without it. It ships in wizardry's
// `defaults/` folder and is switched on for everyone. Switch it off with `plugin_unload defintire`
// (persist: true); change it by copying this folder to ~/.wizardry/plugins/defintire and editing
// the copy, which is loaded instead of this one.
//
// The idea: anything, mathematical or not, can be given an explicit definition: the objects it
// speaks of, the axioms that hold of them, what falls under it and what does not. Criteria tie
// numbers to that definition, so that a candidate is scored by how well it does what the
// definition says, and nothing else. What is scored can be compared, rated and climbed.
//
// It draws on three projects, and includes no code of any:
//   hillclimb (https://github.com/rebase-energy/hillclimb, MIT): a problem is a verifier that
//     scores a candidate, agents make attempts, and the best is kept. `defintire_climb` is that
//     loop, with the definition's criteria as the verifier. When hillclimb is installed, the
//     method says how to hand it a long search.
//   Creative-Intelligence (https://github.com/DeepMathLLM/Creative-Intelligence, MIT): a concept
//     is formed from the problem it answers, by construction, counterexample and verification.
//     The method asks for the question answered, for near misses, and for an attempt to break
//     the definition before it is kept.
//   jacobian (https://github.com/morluto/jacobian, MIT): typed mathematical operations whose
//     results are exact where they claim to be. When it is installed, the method says how a
//     criterion's command calls it.
// hillclimb and jacobian are programs of some size (about 650 MB together, with the Python they
// need), so they are installed only when asked for: by the installer with WIZARDRY_WITH_TOOLS=1,
// or by the command the method gives. They go into wizardry's own directory (tools/, bin/).
// Its own: the definition as a record with stipulated axioms marked, the three kinds of
// criterion and the rule that only an all-exact score is called verified, ratings from pairwise
// comparison for what has no trustworthy absolute number, and the laws about all of it.
//
// Every decision is made in Bend (defintire.bend, compiled to core.mjs) and the ones that must
// hold for every input are proven (LAWS.bend, PROOF.bend): a score resting on a proxy or a
// judgment is never called verified, no reading scores past the best, a comparison only moves
// points between the two compared, and a climb never goes downhill. This file only does what
// Bend cannot: it keeps the files, runs the commands, asks the judge and starts the agents.
//
// One exception to "a plugin reaches the agent only through actions", made by the owner: while it
// is loaded, defintire puts a few lines in the standing prompt, a habit of saying what a thing is
// before working on it, and the definitions kept. `plugin_unload defintire` takes them out.
//
// Definitions are kept in ~/.wizardry/defintire/<name>/ (definition.json, definition.md,
// scores.jsonl, ratings.json, climbs/), so `wizardry export` and `wizardry delete` take them along.
//
// Config (optional, passed by whoever loads the plugin):
//   { "timeoutMinutes": 30,     how long one climbing agent may take
//     "commandSeconds": 300,    how long one criterion's command may take
//     "agent": ["cmd", ...] }   what to run for an attempt, the prompt as its last argument
//                               (default: this wizardry, headless)

import { spawn } from 'node:child_process'
import { accessSync, appendFileSync, constants, copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs'
import { basename, delimiter, join, relative, resolve } from 'node:path'
import bend from './core.mjs'

export const name = 'defintire'
export const inject = ['plugins']

export const DEFAULTS = { timeoutMinutes: 30, commandSeconds: 300 }

// ---- the crossing to Bend: arrays in, answers out, no decisions -------------------------------

const list = (items) => items.reduceRight((tail, head) => ({ $: 'Con', head, tail }), { $: 'Nil' })
const array = (items) => { const out = []; for (let at = items; at.$ === 'Con'; at = at.tail) out.push(at.head); return out }
const some = (value) => (value.$ === 'Some' ? value.value : undefined)
const text = (value) => String(value ?? '').trim()
const whole = (value) => Math.max(0, Math.floor(Number(value) || 0))
const kinds = (words) => list(words.map((word) => bend.kind_of(word)))

export const core = {
  slug: (name) => bend.slug(name),
  /** What is missing from a definition; empty when it is one. */
  problems: (def) => array(bend.problems(def.name, def.answers, def.objects.length, def.axioms.length, def.examples.length, def.non_examples.length,
    list(def.criteria.map((c) => ({ $: 'Criterion', name: c.name, kind: c.kind, weight: c.weight, command: c.command, rubric: c.rubric }))))),
  notDefined: (what) => bend.not_defined(list(what)),
  /** A definition, written out in notation. */
  written(def) {
    const weightOf = (kind) => def.criteria.filter((c) => c.kind === kind).reduce((sum, c) => sum + c.weight, 0)
    return bend.written(def.name, def.answers,
      list(def.objects.map((o) => ({ $: 'Object', symbol: o.symbol, sort: o.type, meaning: o.meaning }))), list(def.primitives),
      list(def.axioms.map((a) => ({ $: 'Axiom', name: a.name, statement: a.statement, stipulated: a.stipulated }))),
      list(def.examples), list(def.non_examples), def.bend,
      list(def.criteria.map((c) => ({ $: 'Shown', name: c.name, kind: c.gate ? `${c.kind}, gate` : c.kind, weight: c.weight, statement: c.statement,
        how: c.kind === 'judged' ? c.rubric : c.command, lo: String(c.worst), hi: String(c.best), higher: c.best >= c.worst }))),
      bend.climbable(weightOf('exact'), weightOf('proxy'), weightOf('judged')))
  },
  defined: (name, folder, written) => bend.defined(name, folder, written),
  noDefinition: (name, known) => bend.no_definition(name, list(known)),
  /** The number a command printed, if its last line is one. */
  reading: (out) => some(bend.reading(out)),
  /** Where a reading stands between worst and best, in thousandths. */
  position: (value, worst, best) => bend.position(Math.fround(value), Math.fround(Math.min(worst, best)), Math.fround(Math.max(worst, best)), best >= worst),
  /** What a judge gave, in thousandths, if it gave a number. */
  judged: (reply) => some(bend.judged(reply)),
  /** A score held under its gates: never higher than where the candidate stands on any of them. */
  gated: (score, gates) => bend.gated(score, list(gates)),
  score: (marks) => bend.score(list(marks.map(({ weight, at }) => ({ $: 'Mark', weight, at })))),
  standing: (measuredKinds, unmeasured) => bend.standing(kinds(measuredKinds), unmeasured),
  verified: (measuredKinds, unmeasured) => bend.verified(kinds(measuredKinds), unmeasured),
  row: (c, measured, at, note) => bend.row(c.name, c.gate ? `${c.kind}, gate` : c.kind, c.weight, measured, at, note ?? ''),
  measured: (name, candidate, score, standing, rows) => bend.measured(name, candidate, score, standing, list(rows)),
  noNumber: (code, said) => bend.no_number(whole(code), said),
  judgeAsk: (written, c, candidate) => bend.judge_ask(written, c.name, c.statement, c.rubric, bend.shown_to_judge(candidate)),
  versusAsk: (written, a, b) => bend.versus_ask(written, bend.shown_to_judge(a), bend.shown_to_judge(b)),
  needsJudge: (words) => bend.needs_judge(kinds(words)),
  /** How a judge's reply, or two scores, decide a comparison: "First", "Second" or "Draw". */
  verdict: (reply) => bend.verdict(reply).$,
  byScores: (a, b) => bend.by_scores(a, b).$,
  /** The two ratings after a comparison. */
  rated(a, b, outcome) {
    const { first, second } = bend.rated(a, b, { $: outcome })
    return [first, second]
  },
  start: () => bend.start(),
  ranked: (name, judge, games, rated) => bend.ranked(name, bend.decided_by(judge), games,
    bend.sorted(list(rated.map(({ name, rating, played }) => ({ $: 'Rated', name, rating, played }))))),
  /** Whether an attempt takes the place of the best so far, and the best score after it. */
  keeps: (best, attempt) => bend.keeps(best, attempt),
  kept: (best, attempt) => bend.kept(best, attempt),
  climbBrief: (written, file, report, hint) => bend.climb_brief(written, file, report, hint ?? ''),
  attemptLine: (round, n, score, best, how) => bend.attempt_line(round, n, score, best, how ?? ''),
  climbed: (name, file, from, to, standing, lines, backup) => bend.climbed(name, file, from, to, standing, list(lines), backup),
  agentArgs: (model, sessionModel, thinking, sessionThinking) => array(bend.agent_args(model ?? '', sessionModel ?? '', thinking ?? '', sessionThinking ?? '')),
  method: (hillclimb, jacobian, home, saved) => bend.method(hillclimb ?? '', jacobian ?? '', home, list(saved)),
}

// ---- what only Node can do --------------------------------------------------------------------

/** Where a program is: its name when it is on PATH, its full path when wizardry has it in `bin`, undefined when nowhere. */
function found(program, bin) {
  const runs = (file) => {
    try {
      accessSync(file, constants.X_OK)
      return true
    } catch {
      return false
    }
  }
  if (runs(join(bin, program))) return join(bin, program)
  return (process.env.PATH ?? '').split(delimiter).filter(Boolean).some((dir) => runs(join(dir, program))) ? program : undefined
}

/** Run a command and resolve with how it ended and what it printed. Never rejects. */
function run(command, args, { cwd, env, timeoutMs, signal, shell }) {
  return new Promise((done) => {
    let out = ''
    let err = ''
    let child
    try {
      child = spawn(command, args, { cwd, env, shell, stdio: ['ignore', 'pipe', 'pipe'] })
    } catch (error) {
      return done({ code: 1, out: '', err: String(error?.message ?? error) })
    }
    let why
    const stop = () => { why ??= 'stopped'; child.kill('SIGTERM') }
    const timer = setTimeout(() => { why = 'timed out'; child.kill('SIGTERM') }, timeoutMs)
    timer.unref?.()
    signal?.addEventListener('abort', stop, { once: true })
    child.stdout.on('data', (chunk) => { out += chunk })
    child.stderr.on('data', (chunk) => { err += chunk })
    const finish = (code) => {
      clearTimeout(timer)
      signal?.removeEventListener('abort', stop)
      done({ code, out: out.trim(), err: why ?? err.trim() })
    }
    child.on('error', (error) => { err = String(error.message); finish(1) })
    child.on('close', (code) => finish(why ? 1 : code ?? 1))
  })
}

const textOf = (content) => (typeof content === 'string' ? content
  : Array.isArray(content) ? content.filter((part) => part?.type === 'text').map((part) => String(part.text ?? '')).join('\n') : '')

export function apply(ctx, config) {
  const home = join(ctx.plugins.home, 'defintire')
  const cfg = { ...DEFAULTS, ...(config ?? {}) }
  /** Where tools installed for wizardry are linked: jacobian and hillclimb, when they were asked for. */
  const bin = join(ctx.plugins.home, 'bin')
  const withTools = () => ({ ...process.env, PATH: `${bin}${delimiter}${process.env.PATH ?? ''}` })

  // ---- the definitions kept --------------------------------------------------------------

  const known = () => {
    try {
      return readdirSync(home).filter((entry) => existsSync(join(home, entry, 'definition.json'))).sort()
    } catch {
      return []
    }
  }
  /** A kept definition by its name, with the folder it is in; throws with what there is when there is none. */
  const kept = (asked) => {
    const folder = join(home, core.slug(text(asked)))
    try {
      return { ...JSON.parse(readFileSync(join(folder, 'definition.json'), 'utf8')), folder }
    } catch {
      throw new Error(core.noDefinition(text(asked), known()))
    }
  }

  // The one thing defintire does besides its actions, by the owner's exception: a habit of mind
  // and the names of what is defined go into the standing prompt, read again at every turn.
  // wizardry lets this plugin in by name and cuts the text short (core.bend, "The one way in").
  try {
    ctx.get('pi')?.mind(() => bend.mind(list(known().slice(0, 6).map((slug) => {
      try {
        const def = JSON.parse(readFileSync(join(home, slug, 'definition.json'), 'utf8'))
        return { $: 'Known', name: String(def.name ?? slug), answers: String(def.answers ?? '') }
      } catch {
        return { $: 'Known', name: slug, answers: '' }
      }
    }))))
  } catch {}

  // ---- the judge -------------------------------------------------------------------------

  const judge = (piCtx) => {
    if (cfg.complete) return (user) => cfg.complete({ system: bend.judge_system(), user })
    const model = piCtx?.model
    const registry = piCtx?.modelRegistry
    try {
      if (!model || !registry?.hasConfiguredAuth(model)) return undefined
    } catch {
      return undefined
    }
    return async (user) => {
      const message = await registry.complete(model, {
        systemPrompt: bend.judge_system(),
        messages: [{ role: 'user', content: [{ type: 'text', text: user }], timestamp: Date.now() }],
      }, { signal: AbortSignal.timeout(120_000) })
      if (message.stopReason === 'error' || message.stopReason === 'aborted') throw new Error(message.errorMessage || `the model stopped: ${message.stopReason}`)
      return textOf(message.content)
    }
  }

  // ---- measuring -------------------------------------------------------------------------

  /** Score the file at `path` against a definition. What each reading comes to is decided in Bend. */
  async function measure(def, path, label, env) {
    const ask = judge(env.pi)
    const written = core.written(def)
    let candidate
    const one = async (c) => {
      if (c.kind === 'judged') {
        if (!ask) return { note: bend.no_judge() }
        candidate ??= readFileSync(path, 'utf8')
        try {
          const at = core.judged(await ask(core.judgeAsk(written, c, candidate)))
          return at === undefined ? { note: bend.judge_said_nothing() } : { at }
        } catch (error) {
          return { note: String(error?.message ?? error) }
        }
      }
      const ran = await run(`${c.command} "$DEFINTIRE_CANDIDATE"`, [], {
        cwd: existsSync(def.root) ? def.root : env.cwd, shell: true, signal: env.signal, timeoutMs: cfg.commandSeconds * 1000,
        env: { ...withTools(), DEFINTIRE_CANDIDATE: path, DEFINTIRE_DEFINITION: def.folder },
      })
      const value = ran.code === 0 ? core.reading(ran.out) : undefined
      return value === undefined ? { note: core.noNumber(ran.code, ran.err || ran.out) } : { at: core.position(value, c.worst, c.best), note: `read ${value}` }
    }
    const results = await Promise.all(def.criteria.map(one))
    const done = def.criteria.map((c, i) => ({ c, ...results[i] }))
    const marked = done.filter((each) => each.at !== undefined)
    // A gate that could not be measured holds the score at nothing: an axiom not shown to hold is not taken to.
    const score = core.gated(core.score(marked.map(({ c, at }) => ({ weight: c.weight, at }))), done.filter(({ c }) => c.gate).map(({ at }) => at ?? 0))
    const standing = core.standing(marked.map(({ c }) => c.kind), done.length - marked.length)
    const rows = done.map(({ c, at, note }) => core.row(c, at !== undefined, at ?? 0, note))
    try {
      appendFileSync(join(def.folder, 'scores.jsonl'), `${JSON.stringify({ at: new Date().toISOString(), candidate: label, score, standing,
        criteria: done.map(({ c, at, note }) => ({ name: c.name, kind: c.kind, at: at ?? null, note: note ?? '' })) })}\n`)
    } catch {}
    return { score, standing, text: core.measured(def.name, label, score, standing, rows) }
  }

  /** What is to be scored, as a file: the path given, or the text given written to one. */
  const candidateFile = (def, given, env) => {
    const asked = text(given?.candidate)
    const path = asked ? resolve(env.cwd, asked) : ''
    if (path && existsSync(path) && statSync(path).isFile()) return { path, label: relative(env.cwd, path) || asked }
    if (typeof given?.text !== 'string' || !given.text) throw new Error(bend.no_candidate(asked))
    const dir = join(def.folder, 'texts')
    mkdirSync(dir, { recursive: true })
    const label = text(given?.name) || `text-${readdirSync(dir).length + 1}`
    const file = join(dir, `${core.slug(label)}.txt`)
    writeFileSync(file, given.text)
    return { path: file, label }
  }

  // ---- the actions -----------------------------------------------------------------------

  ctx.actions.register({
    name: 'defintire',
    title: 'defintire method',
    description: bend.describe(),
    parameters: { type: 'object', properties: {} },
    execute: () => core.method(found('hillclimb', bin), found('jacobian', bin), ctx.plugins.home, known()),
  })

  const strings = (description) => ({ type: 'array', items: { type: 'string' }, description })
  ctx.actions.register({
    name: 'defintire_define',
    title: 'defintire define',
    description: bend.describe_define(),
    parameters: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'What is being defined.' },
        answers: { type: 'string', description: 'The question the definition answers: what could not be decided or measured without it.' },
        objects: { type: 'array', description: 'The things the definition speaks of.', items: { type: 'object', properties: {
          symbol: { type: 'string', description: 'In notation: m, G = (V, E), f.' },
          type: { type: 'string', description: 'What kind of thing it is: String, Graph, X \\to \\mathbb{R}.' },
          meaning: { type: 'string', description: 'What it stands for, in words.' } }, required: ['symbol', 'type', 'meaning'] } },
        primitives: strings('What is left undefined on purpose.'),
        axioms: { type: 'array', description: 'The conditions that hold of exactly the things defined.', items: { type: 'object', properties: {
          name: { type: 'string' },
          statement: { type: 'string', description: 'In mathematical notation (LaTeX).' },
          stipulated: { type: 'boolean', description: 'True when this is a choice the definer makes rather than a fact found.' } }, required: ['name', 'statement'] } },
        examples: strings('Things that fall under the definition.'),
        non_examples: strings('Things that do not, and which axiom each fails. Near misses are the useful ones.'),
        bend: { type: 'string', description: 'The definition in Bend, where Bend can say it: a type for the objects, defs or laws for axioms.' },
        criteria: { type: 'array', description: 'What ties numbers to the definition.', items: { type: 'object', properties: {
          name: { type: 'string' },
          statement: { type: 'string', description: 'The quantity, in notation.' },
          kind: { type: 'string', enum: ['exact', 'proxy', 'judged'] },
          weight: { type: 'number', description: 'How much it counts beside the others. Default 1.' },
          command: { type: 'string', description: 'For exact and proxy: a shell command that prints the reading as its last line. The candidate\'s path is its last argument and $DEFINTIRE_CANDIDATE.' },
          gate: { type: 'boolean', description: 'True when this criterion stands for an axiom: the score is never higher than where the candidate stands on it.' },
          rubric: { type: 'string', description: 'For judged: what 0 looks like and what 100 looks like.' },
          worst: { type: 'number', description: 'The reading that scores 0. Default 0.' },
          best: { type: 'number', description: 'The reading that scores 100. Default 1. Below `worst` when lower readings are better.' } }, required: ['name', 'statement', 'kind'] } },
      },
      required: ['name', 'answers', 'objects', 'axioms', 'examples', 'non_examples', 'criteria'],
    },
    execute(given, env) {
      const items = (value) => (Array.isArray(value) ? value : [])
      const number = (value, otherwise) => (Number.isFinite(Number(value)) && value !== undefined && value !== null && value !== '' ? Number(value) : otherwise)
      const def = {
        name: text(given?.name),
        answers: text(given?.answers),
        objects: items(given?.objects).map((o) => ({ symbol: text(o?.symbol), type: text(o?.type), meaning: text(o?.meaning) })),
        primitives: items(given?.primitives).map(text).filter(Boolean),
        axioms: items(given?.axioms).map((a) => ({ name: text(a?.name), statement: text(a?.statement), stipulated: a?.stipulated === true })),
        examples: items(given?.examples).map(text).filter(Boolean),
        non_examples: items(given?.non_examples).map(text).filter(Boolean),
        bend: String(given?.bend ?? ''),
        criteria: items(given?.criteria).map((c) => ({
          name: text(c?.name), statement: text(c?.statement), kind: text(c?.kind), weight: whole(c?.weight ?? 1),
          command: text(c?.command), rubric: text(c?.rubric), gate: c?.gate === true,
          worst: text(c?.kind) === 'judged' ? 0 : number(c?.worst, 0), best: text(c?.kind) === 'judged' ? 100 : number(c?.best, 1),
        })),
        root: env.cwd,
        at: new Date().toISOString(),
      }
      // Whether it is a definition is decided in Bend.
      const missing = core.problems(def)
      if (missing.length) return core.notDefined(missing)
      const folder = join(home, core.slug(def.name))
      const written = core.written(def)
      mkdirSync(folder, { recursive: true })
      writeFileSync(join(folder, 'definition.json'), `${JSON.stringify(def, null, 2)}\n`)
      writeFileSync(join(folder, 'definition.md'), written)
      return core.defined(def.name, folder, written)
    },
  })

  const which = { type: 'string', description: 'The name of a kept definition.' }
  ctx.actions.register({
    name: 'defintire_measure',
    title: 'defintire measure',
    description: bend.describe_measure(),
    parameters: {
      type: 'object',
      properties: {
        definition: which,
        candidate: { type: 'string', description: 'The file to score.' },
        text: { type: 'string', description: 'Or the text to score, when it is not in a file.' },
        name: { type: 'string', description: 'What to call a text in the record.' },
      },
      required: ['definition'],
    },
    async execute(given, env) {
      const def = kept(given?.definition)
      const { path, label } = candidateFile(def, given, env)
      return (await measure(def, path, label, env)).text
    },
  })

  ctx.actions.register({
    name: 'defintire_rank',
    title: 'defintire rank',
    description: bend.describe_rank(),
    parameters: {
      type: 'object',
      properties: {
        definition: which,
        candidates: { type: 'array', description: 'The files to compare, two or more.', items: { type: 'string' } },
      },
      required: ['definition', 'candidates'],
    },
    async execute(given, env) {
      const def = kept(given?.definition)
      const candidates = (Array.isArray(given?.candidates) ? given.candidates : []).map((each) => candidateFile(def, { candidate: each }, env))
      if (candidates.length < 2) return bend.needs_two()
      // Whether a judge is needed is decided in Bend: only when a criterion is judged.
      const byJudge = core.needsJudge(def.criteria.map((c) => c.kind))
      const ask = byJudge ? judge(env.pi) : undefined
      if (byJudge && !ask) return bend.cannot_judge()
      const written = core.written(def)
      const scores = byJudge ? [] : await Promise.all(candidates.map((each) => measure(def, each.path, each.label, env)))
      const texts = byJudge ? candidates.map((each) => readFileSync(each.path, 'utf8')) : []

      const file = join(def.folder, 'ratings.json')
      let ratings = {}
      try { ratings = JSON.parse(readFileSync(file, 'utf8')) } catch {}
      for (const each of candidates) ratings[each.label] ??= { rating: core.start(), played: 0 }
      let games = 0
      for (let i = 0; i < candidates.length; i++) {
        for (let j = i + 1; j < candidates.length; j++) {
          const outcome = byJudge ? core.verdict(await ask(core.versusAsk(written, texts[i], texts[j]))) : core.byScores(scores[i].score, scores[j].score)
          const [a, b] = [ratings[candidates[i].label], ratings[candidates[j].label]]
          // How the ratings move is decided in Bend, where it is proven that their sum stays.
          ;[a.rating, b.rating] = core.rated(a.rating, b.rating, outcome)
          a.played++
          b.played++
          games++
        }
      }
      writeFileSync(file, `${JSON.stringify(ratings, null, 2)}\n`)
      return core.ranked(def.name, byJudge, games, Object.entries(ratings).map(([name, each]) => ({ name, ...each })))
    },
  })

  ctx.actions.register({
    name: 'defintire_climb',
    title: 'defintire climb',
    description: bend.describe_climb(),
    parameters: {
      type: 'object',
      properties: {
        definition: which,
        file: { type: 'string', description: 'The file to improve.' },
        rounds: { type: 'number', description: 'How many rounds of attempts. Default 3.' },
        attempts: { type: 'number', description: 'How many agents try at once in each round. Default 2.' },
        hint: { type: 'string', description: 'Anything the agents should know or try.' },
      },
      required: ['definition', 'file'],
    },
    async execute(given, env) {
      const def = kept(given?.definition)
      const target = resolve(env.cwd, text(given?.file))
      if (!existsSync(target) || !statSync(target).isFile()) return bend.no_candidate(text(given?.file))
      const file = basename(target)
      const label = relative(env.cwd, target) || file
      const rounds = whole(given?.rounds ?? 3) || 1
      const attempts = whole(given?.attempts ?? 2) || 1
      const climb = join(def.folder, 'climbs', new Date().toISOString().replace(/[:.]/g, '-'))
      const place = (name) => {
        mkdirSync(join(climb, name), { recursive: true })
        return join(climb, name, file)
      }
      const backup = place('original')
      const best = place('best')
      copyFileSync(target, backup)
      copyFileSync(target, best)

      // The agents run on what the user chose for deployed agents (/default-agent), else on this session's.
      let chosen = {}
      try { chosen = JSON.parse(readFileSync(join(ctx.plugins.home, 'division.json'), 'utf8')) } catch {}
      let thinking = ''
      try { thinking = String(ctx.root.get('pi')?.api?.getThinkingLevel?.() ?? '') } catch {}
      const sessionModel = env.pi?.model ? `${env.pi.model.provider}/${env.pi.model.id}` : ''
      const agent = Array.isArray(cfg.agent) && cfg.agent.length
        ? cfg.agent.map(String)
        : [process.execPath, ...process.execArgv, process.argv[1], '-p', '--no-session', ...core.agentArgs(chosen.model, sessionModel, chosen.thinking, thinking)]

      const written = core.written(def)
      let now = await measure(def, best, label, env)
      const from = now.score
      const lines = []
      for (let round = 1; round <= rounds && !env.signal?.aborted; round++) {
        env.update?.(`round ${round} of ${rounds}: best so far ${now.score / 10}/100`)
        const brief = core.climbBrief(written, file, now.text, text(given?.hint))
        const tried = await Promise.all(Array.from({ length: attempts }, async (_, n) => {
          const at = place(`round-${round}-attempt-${n + 1}`)
          copyFileSync(best, at)
          const dir = join(at, '..')
          // The agent may write only the file it is improving (division's fence, when division is loaded).
          const fence = JSON.stringify({ root: dir, depth: 99, name: 'climb', owns: [file], laws: [], check: '' })
          const ran = await run(agent[0], [...agent.slice(1), brief], {
            cwd: dir, signal: env.signal, timeoutMs: cfg.timeoutMinutes * 60_000,
            env: { ...withTools(), WIZARDRY_DIVISION: fence, WIZARDRY_NO_UPDATE: '1' },
          })
          return { at, how: ran.code === 0 ? '' : ran.err || `ended with status ${ran.code}`, ...(await measure(def, at, `${label} (round ${round}, attempt ${n + 1})`, env)) }
        }))
        // Which attempt is kept is decided in Bend, where it is proven that the best never goes down.
        tried.forEach((each, n) => {
          lines.push(core.attemptLine(round, n + 1, each.score, now.score, each.how))
          if (core.keeps(now.score, each.score)) {
            copyFileSync(each.at, best)
            now = each
          }
        })
      }
      if (core.keeps(from, now.score)) copyFileSync(best, target)
      return core.climbed(def.name, label, from, now.score, now.standing, lines, backup)
    },
  })
}
