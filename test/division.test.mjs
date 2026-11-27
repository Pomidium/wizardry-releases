// The division default: a large task cut in two, each half done by its own agent at once.
//
// Its laws (defaults/division/LAWS.bend) are proven for every cut. These tests cover what the laws
// do not say: that the compiled Bend is the one in the repo and answers as plain JavaScript would,
// that the agents really are started together and really are stopped from writing each other's
// files, and that the check is what decides whether the halves fit.

import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs'
import { homedir, tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { boot as bootWizardry } from '../dist/index.js'
import { brief, core, declaredLaws, entry, method, DEFAULTS as CFG } from '../defaults/division/index.js'

const ROOT = fileURLToPath(new URL('..', import.meta.url))
const DIVISION = join(ROOT, 'defaults', 'division')
const find = (name, extra) => [...(process.env.PATH ?? '').split(':'), extra].map((dir) => join(dir, name)).find((file) => existsSync(file))
const BEND = find('bend', join(homedir(), '.bend', 'bin'))
const LEAN = find('lean', join(homedir(), '.elan', 'bin'))
const boot = (options) => bootWizardry({ shipped: join(tmpdir(), 'wizardry-no-shipped-defaults'), ...options })

let seed = 20261119
const random = () => ((seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) / 2 ** 32)
const below = (n) => Math.floor(random() * n)
const pick = (items) => items[below(items.length)]
const some = (items, max) => [...new Set(Array.from({ length: below(max + 1) }, () => pick(items)))]

function scratch() {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-division-'))
  const home = join(dir, 'home')
  const cwd = join(dir, 'work')
  mkdirSync(home)
  mkdirSync(cwd)
  return { home, cwd }
}

test('division: the proofs check, and the compiled Bend in the repo is what the source compiles to', { skip: !BEND && 'bend is not installed' }, () => {
  const env = { ...process.env, BEND_NO_TELEMETRY: '1', PATH: `${LEAN ? join(LEAN, '..') : ''}:${process.env.PATH}` }
  const proof = spawnSync(BEND, ['PROOF.bend', ...(LEAN ? ['--verdict'] : [])], { cwd: DIVISION, encoding: 'utf8', env })
  assert.match(proof.stdout + proof.stderr, /ALL PROOFS CHECK/)
  const laws = [...readFileSync(join(DIVISION, 'LAWS.bend'), 'utf8').matchAll(/^law (\w+):/gm)].map((match) => match[1])
  const proofs = [...readFileSync(join(DIVISION, 'PROOF.bend'), 'utf8').matchAll(/^def Laws\.(\w+)\(/gm)].map((match) => match[1])
  assert.deepEqual([...proofs].sort(), [...laws].sort())
  assert.equal(laws.length, 16)
  const out = join(mkdtempSync(join(tmpdir(), 'wizardry-division-core-')), 'core.mjs')
  execFileSync(BEND, ['division.bend', '-o', out], { cwd: DIVISION, env })
  assert.equal(readFileSync(join(DIVISION, 'core.mjs'), 'utf8'), readFileSync(out, 'utf8'), 'defaults/division/core.mjs is stale: run `npm run core`')
})

test('division: who may write what, and whether a cut is made, answer as plain JavaScript does', () => {
  const PATHS = ['a.bend', 'b.bend', 'src/', 'src/a.bend', 'src/b/', 'src/b/c.bend', 'src/bb.bend', 'lib/', 'lib/x/y.bend', 'LAWS.bend']
  const covers = (own, path) => own === path || (own.endsWith('/') && path.startsWith(own))
  const may = (owns, path) => !owns || owns.some((own) => covers(own, path))
  const overlap = (xs, ys) => xs.some((x) => ys.some((y) => covers(x, y) || covers(y, x)))
  const twice = (xs) => xs.some((x, i) => xs.indexOf(x) !== i)
  const seen = new Set()
  const sizes = new Set()
  for (let i = 0; i < 8000; i++) {
    const parent = pick([undefined, undefined, some(PATHS, 3)])
    // However many parts: none, one, two, five.
    const parts = Array.from({ length: below(6) }, (_, n) => ({
      name: pick([`part${n}`, `part${n}`, `part${n}`, 'same']), owns: some(PATHS, pick([0, 1, 1, 2])), laws: some(['p', 'q', 'r', 's', 't', 'u'], pick([0, 0, 1, 2])),
    }))
    const depth = below(5)
    const expected =
      depth >= 3 ? 'TooDeep'
      : !parts.length ? 'NoParts'
      : twice(parts.map((part) => part.name)) ? 'SameName'
      : twice(parts.flatMap((part) => part.laws)) ? 'SharedLaw'
      : !parts.every((part) => part.owns.every((own) => may(parent, own))) ? 'Outside'
      : parts.some((part, a) => parts.some((other, b) => a < b && overlap(part.owns, other.owns))) ? 'Trample'
      : 'Divide'
    assert.equal(core.judge(depth, 3, parent, parts), expected, JSON.stringify({ depth, parent, parts }))
    seen.add(expected)
    const path = pick(PATHS)
    assert.equal(core.may(parent, path), may(parent, path))
    // What the laws promise, seen from here: a cut that is made never gives one path two writers.
    if (expected === 'Divide') {
      sizes.add(parts.length)
      for (const each of PATHS) assert.ok(parts.filter((part) => may(part.owns, each)).length <= 1, each)
    }
  }
  assert.equal(seen.size, 7, `every verdict was reached: ${[...seen]}`)
  assert.deepEqual([...sizes].sort(), [1, 2, 3, 4, 5], 'a cut is not refused for how many parts it has')
})

test('division: paths are taken relative to the task, and laws are found where they are declared', () => {
  const { cwd } = scratch()
  mkdirSync(join(cwd, 'src', 'deep'), { recursive: true })
  writeFileSync(join(cwd, 'LAWS.bend'), 'import Base\n\nlaw double:\n  for x: Nat\n  Nat\n\n# law commented:\nlaw Nat.twice :\n  Nat\n')
  writeFileSync(join(cwd, 'src', 'deep', 'more.bend'), 'law inner:\n  Nat\n  law indented:\n')
  assert.equal(entry(cwd, 'src/a.bend'), 'src/a.bend')
  assert.equal(entry(cwd, join(cwd, 'src')), 'src/', 'a folder that exists')
  assert.equal(entry(cwd, 'new/'), 'new/', 'a folder that does not, said with a slash')
  assert.equal(entry(cwd, './src/../src/deep/x.bend'), 'src/deep/x.bend')
  for (const outside of ['../x', '/etc/passwd', '.', '']) assert.equal(entry(cwd, outside), undefined, outside)
  assert.deepEqual([...declaredLaws(cwd)].sort(), ['Nat.twice', 'double', 'inner'])
  assert.match(method(), /You have the whole task/)
  assert.match(method({ depth: 2, name: 'parser', owns: ['src/'], laws: ['parses'], check: 'bend PROOF.bend' }), /a part of a divided task, 2 cuts down: "parser"/)
  assert.doesNotMatch(method(), /\d+ minutes|cut in two|halves/, 'the method names no number of parts and no size')
  const others = [{ name: 'b', task: 'Do B.', owns: ['b.bend'], laws: ['q'] }, { name: 'c', task: 'Look into C.', owns: [], laws: [] }]
  const told = brief({ name: 'a', task: 'Do A.', owns: ['a.bend'], laws: ['p'] }, others, 'All of it.', 'bend PROOF.bend')
  for (const part of ['Your part: a', 'Do A.', 'All of it.', 'Files you own: a.bend', 'Laws you must prove: p', '- "b": Do B. It proves: q', '- "c": Look into C.', 'Check your work with: bend PROOF.bend']) assert.ok(told.includes(part), part)
  const reader = brief(others[1], [], '', '')
  assert.match(reader, /You own no file: read whatever you need, write nothing/)
  assert.doesNotMatch(reader, /Laws you must prove|Check your work with|The other parts/)
})

/** An agent that does what it was told without a model: it fills its law from a file it owns, and says so. */
const FAKE = `
import { appendFileSync, writeFileSync } from 'node:fs'
const place = JSON.parse(process.env.WIZARDRY_DIVISION)
const stamp = (what) => appendFileSync('times.log', place.name + ' ' + what + ' ' + Date.now() + '\\n')
stamp('start')
await new Promise((done) => setTimeout(done, 500))
if (!place.owns.length) { stamp('end'); console.log(place.name + ' only read'); process.exit(0) }
const fill = {
  notes: "notes\\n",
  doubling: "import Base\\nimport ./LAWS.bend as L\\n\\ndef L.double(x):\\n  match x:\\n    case 0n:\\n      0n\\n    case 1n+p:\\n      2n+L.double(p)\\n",
  quadrupling: "import Base\\nimport ./LAWS.bend as L\\nimport ./a.bend as A\\n\\ndef L.quad(x):\\n  L.double(L.double(x))\\n",
  lazy: "import Base\\nimport ./LAWS.bend as L\\nimport ./a.bend as A\\n",
}
writeFileSync(place.owns[0], fill[place.name])
stamp('end')
if (!process.argv.at(-1).includes('Your part: ' + place.name)) process.exit(3)
console.log(place.name + ' filled ' + place.owns[0] + ' at depth ' + place.depth + ' for: ' + place.laws.join(','))
`

function project() {
  const { home, cwd } = scratch()
  writeFileSync(join(cwd, 'LAWS.bend'), 'import Base\n\nlaw double:\n  for x: Nat\n  Nat\n\nlaw quad:\n  for x: Nat\n  Nat\n')
  writeFileSync(join(cwd, 'a.bend'), 'import Base\nimport ./LAWS.bend as L\n')
  writeFileSync(join(cwd, 'b.bend'), 'import Base\nimport ./LAWS.bend as L\nimport ./a.bend as A\n')
  writeFileSync(join(cwd, 'PROOF.bend'), 'import Base\nimport ./LAWS.bend as L\nimport ./a.bend as A\nimport ./b.bend as B\n')
  writeFileSync(join(cwd, 'fake.mjs'), FAKE)
  return { home, cwd }
}

const firstHalf = { name: 'doubling', task: 'Write double.', owns: ['a.bend'], laws: ['double'] }
const secondHalf = { name: 'quadrupling', task: 'Write quad with double.', owns: ['b.bend'], laws: ['quad'] }
const first = firstHalf
const second = secondHalf

test('division: a cut that would let agents collide is refused and starts nothing; nothing else is', async () => {
  const { home, cwd } = project()
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DIVISION, { agent: [process.execPath, join(cwd, 'fake.mjs')] }, { cwd })
  const split = ({ first: a = first, second: b = second, more = [] }) => root.get('actions').invoke('division_split', { parts: [a, b, ...more] }, { cwd })
  const refused = async (args, why) => {
    const said = await split(args)
    assert.match(said, /^Not divided: /)
    assert.match(said, why)
    assert.ok(!existsSync(join(cwd, 'times.log')), 'no agent was started')
  }
  await refused({ second: { ...second, owns: ['a.bend'] } }, /a file in common/)
  await refused({ first: { ...first, owns: ['./'] } }, /outside/)
  await refused({ first: { ...first, owns: ['src/'] }, second: { ...second, owns: ['src/b.bend'] } }, /a folder that holds another's file/)
  await refused({ more: [{ name: 'third', task: 'T.', owns: ['c.bend'] }, { name: 'fourth', task: 'F.', owns: ['c.bend'] }] }, /a file in common/)
  await refused({ more: [{ name: 'third', task: '' }] }, /a name and a task/)
  await refused({ second: { ...second, laws: ['double'] } }, /every law has one prover/)
  await refused({ second: { ...second, laws: ['octuple'] } }, /no \.bend file here declares `law octuple`/)
  await refused({ second: { ...second, name: 'doubling' } }, /the same name/)
  await refused({ first: { ...first, owns: ['../elsewhere.bend'] } }, /outside/)
  assert.match(await root.get('actions').invoke('division', {}, { cwd }), /You have the whole task/)
  await root.fiber.dispose()
})

test('division: both halves run at the same time, each in its own file, and the check decides whether they fit', { skip: !BEND && 'bend is not installed' }, async () => {
  const { home, cwd } = project()
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DIVISION, { agent: [process.execPath, join(cwd, 'fake.mjs')] }, { cwd })
  const updates = []
  const said = await root.get('actions').invoke('division_split', { parts: [first, second], whole: 'Double and quadruple.' }, { cwd, update: (text) => updates.push(text) })
  assert.match(said, /## doubling: done in/)
  assert.match(said, /doubling filled a\.bend at depth 1 for: double/)
  assert.match(said, /quadrupling filled b\.bend at depth 1 for: quad/)
  assert.match(said, /## The check: bend PROOF\.bend\nIt passes: the parts fit\./)
  assert.match(said, /ALL PROOFS CHECK/)
  assert.equal(updates.at(-1), 'doubling: done\nquadrupling: done')

  // Together, not one after the other: each started before the other ended.
  const times = Object.fromEntries(readFileSync(join(cwd, 'times.log'), 'utf8').trim().split('\n').map((line) => line.split(' ')).map(([who, what, at]) => [`${who} ${what}`, Number(at)]))
  assert.ok(times['doubling start'] < times['quadrupling end'] && times['quadrupling start'] < times['doubling end'], JSON.stringify(times))

  const runs = readFileSync(join(home, 'division', 'runs.jsonl'), 'utf8').trim().split('\n').map((line) => JSON.parse(line))
  assert.deepEqual(runs.map((run) => [run.event, run.depth]), [['cut', 0], ['joined', 0]])
  assert.equal(runs[1].fits, true)

  // A half that did not do its part: the check says so, and so does the report.
  writeFileSync(join(cwd, 'b.bend'), 'import Base\nimport ./LAWS.bend as L\nimport ./a.bend as A\n')
  const again = await root.get('actions').invoke('division_split', { parts: [first, { ...second, name: 'lazy' }] }, { cwd })
  assert.match(again, /It FAILS: the parts do not fit yet/)
  assert.match(again, /SOME PROOFS FAIL/)

  // As many parts as the task has, with or without laws: one that proves, one that writes prose,
  // one that only reads. The check is whatever says the parts fit, or none.
  const three = await root.get('actions').invoke('division_split', { check: 'test -s notes.md', parts: [
    first, { name: 'notes', task: 'Write the notes.', owns: ['notes.md'] }, { name: 'reader', task: 'Find out how doubling is used.' }] }, { cwd })
  assert.match(three, /^Every part is back after/)
  assert.match(three, /## notes: done in[^\n]*\nOwned: notes\.md\nLaws: \(none\)/)
  assert.match(three, /## reader: done in[^\n]*\nOwned: \(none\)\nLaws: \(none\)\n\nreader only read/)
  assert.match(three, /## The check: test -s notes\.md\nIt passes: the parts fit\./)
  const alone = await root.get('actions').invoke('division_split', { parts: [{ name: 'reader', task: 'Read.' }] }, { cwd: join(cwd, '..') })
  assert.match(alone, /reader only read[\s\S]*## No check was given\nWhether the parts fit is yours to see/)
  await root.fiber.dispose()
})

test('division: a half is stopped from writing a file it was not handed, and from cutting past the limit', async () => {
  const { home, cwd } = project()
  mkdirSync(join(cwd, 'src'))
  const place = { root: cwd, depth: 3, name: 'doubling', owns: ['a.bend', 'src/'], laws: ['double'], check: 'bend PROOF.bend' }
  process.env.WIZARDRY_DIVISION = JSON.stringify(place)
  try {
    const { root, plugins } = await boot({ home, cwd, defaults: ['cordis', 'fs'] })
    await plugins.load(DIVISION, undefined, { cwd })
    const actions = root.get('actions')
    await actions.invoke('write', { path: join(cwd, 'a.bend'), content: 'mine\n' }, { cwd })
    await actions.invoke('write', { path: join(cwd, 'src', 'deep', 'new.bend'), content: 'mine too\n' }, { cwd })
    assert.equal(readFileSync(join(cwd, 'src', 'deep', 'new.bend'), 'utf8'), 'mine too\n')
    for (const path of [join(cwd, 'b.bend'), join(cwd, 'LAWS.bend'), join(cwd, 'src', '..', 'PROOF.bend'), join(cwd, '..', 'outside.bend'), 'relative-to-somewhere-else.bend', '/tmp/wizardry-division-elsewhere']) {
      await assert.rejects(actions.invoke('write', { path, content: 'trampled\n' }, { cwd }), /is not yours to write: your part \("doubling"\) owns a\.bend, src\//, path)
      await assert.rejects(actions.invoke('edit', { path, edits: [{ oldText: 'import', newText: 'x' }] }, { cwd }), /is not yours to write/, path)
    }
    assert.equal(readFileSync(join(cwd, 'b.bend'), 'utf8'), 'import Base\nimport ./LAWS.bend as L\nimport ./a.bend as A\n', 'the other half\'s file is as it was')
    assert.match((await actions.invoke('read', { path: join(cwd, 'b.bend') }, { cwd })).text, /import/, 'reading anything is fine')

    assert.match(await actions.invoke('division', {}, { cwd }), /a part of a divided task, 3 cuts down: "doubling"/)
    const deeper = await actions.invoke('division_split', { parts: [{ ...first, owns: ['a.bend'] }, { ...second, owns: ['src/q.bend'] }] }, { cwd })
    assert.match(deeper, /Not divided: this task has already been cut 3 times/)
    await root.fiber.dispose()

    // One cut higher it may cut again, but only among its own files.
    process.env.WIZARDRY_DIVISION = JSON.stringify({ ...place, depth: 2 })
    const next = await boot({ home, cwd, defaults: ['cordis'] })
    await next.plugins.load(DIVISION, { agent: [process.execPath, join(cwd, 'fake.mjs')] }, { cwd })
    const outside = await next.root.get('actions').invoke('division_split', { parts: [first, second] }, { cwd })
    assert.match(outside, /Not divided: a part was given a file that is not yours to hand out/)
    await next.root.fiber.dispose()
  } finally {
    delete process.env.WIZARDRY_DIVISION
  }
})

test('division: /default-agent and /division choose what deployed agents run on, and the choice is kept', async () => {
  const { home, cwd } = project()
  // An agent that only says what it was started with.
  writeFileSync(join(cwd, 'echo.mjs'), `console.log('ARGS ' + JSON.stringify(process.argv.slice(2, -1)))`)
  const start = async () => {
    const { root, plugins } = await boot({ home, cwd, defaults: ['pi', 'cordis'] })
    await plugins.load(DIVISION, undefined, { cwd })
    const commands = {}
    root.get('pi').attach({ registerTool() {}, on() {}, getThinkingLevel: () => 'high', registerCommand: (name, command) => { commands[name] = command } })
    return { root, plugins, command: commands.division, agent: commands['default-agent'] }
  }
  const said = []
  const picks = []
  const models = [{ provider: 'radius', id: 'claude-fable-5-2' }, { provider: 'radius', id: 'claude-opus-5-5' }, { provider: 'openai', id: 'gpt-5' }]
  const piCtx = {
    model: models[1],
    modelRegistry: { getAvailable: () => models },
    ui: { notify: (text, kind) => said.push([kind, text]), select: async (title, options) => (picks.push([title, options]), options[1]) },
  }
  const first = await start()
  assert.deepEqual(first.command.getArgumentCompletions(''), [{ value: 'model', label: 'model' }, { value: 'thinking', label: 'thinking' }])
  await first.command.handler('', piCtx)
  assert.match(said.at(-1)[1], /model: radius\/claude-opus-5-5 \(the same as this session\)\n  thinking: high \(the same as this session\)/)

  await first.command.handler('model openai/gpt-5', piCtx)
  await first.command.handler('thinking low', piCtx)
  assert.match(said.at(-1)[1], /model: openai\/gpt-5 \(chosen\)\n  thinking: low \(chosen\)/)
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')), { model: 'openai/gpt-5', thinking: 'low' })

  // With no value, a list to pick from; a part of a name is enough when it names one model.
  await first.command.handler('model', piCtx)
  assert.deepEqual(picks.at(-1)[1], ['same (as this session)', 'radius/claude-fable-5-2', 'radius/claude-opus-5-5', 'openai/gpt-5'])
  assert.match(said.at(-1)[1], /model: radius\/claude-fable-5-2 \(chosen\)/)
  await first.command.handler('thinking', piCtx)
  assert.deepEqual(picks.at(-1)[1], ['same (as this session)', 'off', 'minimal', 'low', 'medium', 'high', 'xhigh', 'max'])
  assert.match(said.at(-1)[1], /thinking: off \(chosen\)/)
  await first.command.handler('model fable', piCtx)
  assert.match(said.at(-1)[1], /model: radius\/claude-fable-5-2 \(chosen\)/)

  for (const [bad, why] of [['model nothing-like-it', /No model "nothing-like-it" is signed in/], ['model claude', /did you mean radius\/claude-fable-5-2, radius\/claude-opus-5-5/], ['thinking enormous', /No thinking level "enormous"/], ['speed fast', /^Usage: \/division/]]) {
    await first.command.handler(bad, piCtx)
    assert.deepEqual([said.at(-1)[0], why.test(said.at(-1)[1])], ['warning', true], bad)
  }
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')), { model: 'radius/claude-fable-5-2', thinking: 'off' }, 'a refused choice changes nothing')
  await first.root.fiber.dispose()

  // The next session starts with the choice, and the halves are started on it.
  writeFileSync(join(home, 'division.json'), JSON.stringify({ model: 'radius/claude-fable-5-2', thinking: 'off', agent: [process.execPath, join(cwd, 'echo.mjs'), '--no-session'] }))
  const split = async (session) => {
    const report = await session.root.get('actions').invoke('division_split', { parts: [firstHalf, secondHalf], check: 'true' }, { cwd, pi: piCtx })
    return JSON.parse(/ARGS (.*)/.exec(report)[1])
  }
  const second = await start()
  assert.deepEqual(await split(second), ['--no-session'], 'a command of your own is run as it is')
  await second.root.fiber.dispose()

  // wizardry's own agent gets the choice as --model and --thinking; with "same", the session's.
  const { halfArgs } = await import('../defaults/division/index.js')
  assert.deepEqual(halfArgs({ model: 'radius/claude-fable-5-2', thinking: 'off' }, 'radius/claude-opus-5-5', 'high'), ['--model', 'radius/claude-fable-5-2', '--thinking', 'off'])
  assert.deepEqual(halfArgs({ model: '', thinking: '' }, 'radius/claude-opus-5-5', 'high'), ['--model', 'radius/claude-opus-5-5', '--thinking', 'high'])
  assert.deepEqual(halfArgs({ model: '', thinking: 'max' }, '', ''), ['--thinking', 'max'])
  const third = await start()
  await third.command.handler('model same', piCtx)
  await third.command.handler('thinking same', piCtx)
  assert.match(said.at(-1)[1], /model: radius\/claude-opus-5-5 \(the same as this session\)\n  thinking: high \(the same as this session\)/)
  assert.equal(JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')).model, '')

  // /default-agent: this session's setup becomes the agents', a model can be named, and "same" gives it back.
  await third.agent.handler('', piCtx)
  assert.match(said.at(-1)[1], /^The agents you deploy run on\n  model: radius\/claude-opus-5-5 \(chosen\)\n  thinking: high \(chosen\)/)
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')), { model: 'radius/claude-opus-5-5', thinking: 'high', agent: [process.execPath, join(cwd, 'echo.mjs'), '--no-session'] })
  await third.agent.handler('gpt', piCtx)
  assert.match(said.at(-1)[1], /model: openai\/gpt-5 \(chosen\)\n  thinking: high \(chosen\)/)
  await third.agent.handler('nothing-like-it', piCtx)
  assert.deepEqual([said.at(-1)[0], /No model "nothing-like-it" is signed in/.test(said.at(-1)[1])], ['warning', true])
  assert.equal(JSON.parse(readFileSync(join(home, 'division.json'), 'utf8')).model, 'openai/gpt-5')
  await third.agent.handler('same', piCtx)
  assert.match(said.at(-1)[1], /model: radius\/claude-opus-5-5 \(the same as this session\)\n  thinking: high \(the same as this session\)/)
  assert.deepEqual(third.agent.getArgumentCompletions(''), [{ value: 'same', label: 'same' }])
  await third.root.fiber.dispose()
})

test('division: a file changed outside every part\'s files is named when the parts are back, and one that hangs is ended', async () => {
  const { home, cwd } = scratch()
  // An agent that writes as a command would, past the write tools: its own file, and for one part a file nobody owns.
  writeFileSync(join(cwd, 'agent.mjs'), `import { writeFileSync, mkdirSync } from 'node:fs'
const place = JSON.parse(process.env.WIZARDRY_DIVISION)
writeFileSync(place.owns[0], place.name)
if (place.name === 'careless') { mkdirSync('shared', { recursive: true }); writeFileSync('shared/config.txt', 'changed'); mkdirSync('.cache', { recursive: true }); writeFileSync('.cache/x', 'x'); writeFileSync('.env', 'x') }
if (place.name === 'stuck') setTimeout(() => {}, 60000)
console.log(place.name + ' done')`)
  writeFileSync(join(cwd, 'untouched.txt'), 'as it was')
  await new Promise((resolve) => setTimeout(resolve, 20))
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DIVISION, { agent: [process.execPath, join(cwd, 'agent.mjs')], timeoutMinutes: 0.02 }, { cwd })
  const split = (parts) => root.get('actions').invoke('division_split', { parts, check: 'true' }, { cwd })

  const tidy = await split([{ name: 'one', task: 'One.', owns: ['a.txt'] }, { name: 'two', task: 'Two.', owns: ['lib/'] }].map((part) => ({ ...part, owns: part.owns[0] === 'lib/' ? ['b.txt'] : part.owns })))
  assert.doesNotMatch(tidy, /OUTSIDE|Not looked at/, 'nothing strayed, nothing said')

  const said = await split([{ name: 'careful', task: 'C.', owns: ['c.txt'] }, { name: 'careless', task: 'D.', owns: ['d.txt'] }])
  assert.match(said, /CHANGED OUTSIDE EVERY PART'S FILES \(by a command, not the write tools\): \.env, shared\/config\.txt\. No part owned these/)
  assert.doesNotMatch(said, /untouched|agent\.mjs|c\.txt,|\.cache/, 'hidden folders are not looked into')
  const runs = readFileSync(join(home, 'division', 'runs.jsonl'), 'utf8').trim().split('\n').map((line) => JSON.parse(line)).filter((run) => run.event === 'joined')
  assert.deepEqual(runs.map((run) => run.strays), [[], ['.env', 'shared/config.txt']])

  // One part hangs: it is ended at the limit, said to have timed out, and the other's work stands.
  const started = Date.now()
  const hung = await split([{ name: 'quick', task: 'Q.', owns: ['q.txt'] }, { name: 'stuck', task: 'S.', owns: ['s.txt'] }])
  assert.ok(Date.now() - started < 10_000, 'not the minute the part would have taken')
  assert.match(hung, /## quick: done in/)
  assert.match(hung, /## stuck: [^\n]*timed out/)
  assert.equal(readFileSync(join(cwd, 'q.txt'), 'utf8'), 'quick')
  await root.fiber.dispose()
})
