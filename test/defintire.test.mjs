// The defintire default: definitions, criteria, measurement, ratings and climbing.
//
// Its laws (defaults/defintire/LAWS.bend) are proven for every input. These tests cover what the
// laws do not say: that each def answers as the rule reads when written a second time in plain
// JavaScript, and that the plugin, loaded on a real Cordis root, keeps a definition, runs its
// commands, asks its judge and climbs a file. The agents and the judge are stand-ins: a real
// one needs a model.

import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, writeFileSync } from 'node:fs'
import { homedir, tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { boot as bootWizardry } from '../dist/index.js'
import { core } from '../defaults/defintire/index.js'

const DEFINTIRE = fileURLToPath(new URL('../defaults/defintire', import.meta.url))
const BEND = [...(process.env.PATH ?? '').split(':'), join(homedir(), '.bend', 'bin')].map((dir) => join(dir, 'bend')).find((file) => existsSync(file))
const boot = (options) => bootWizardry({ shipped: join(tmpdir(), 'wizardry-no-shipped-defaults'), ...options })

let seed = 20261121
const below = (n) => Math.floor(((seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) / 2 ** 32) * n)
const pick = (items) => items[below(items.length)]

function scratch() {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-defintire-'))
  const home = join(dir, 'home')
  const cwd = join(dir, 'work')
  mkdirSync(home)
  mkdirSync(cwd)
  return { home, cwd }
}

test('defintire: the proofs check, and the compiled Bend in the repo is what the source compiles to', { skip: !BEND && 'bend is not installed' }, () => {
  const env = { ...process.env, BEND_NO_TELEMETRY: '1' }
  const proof = spawnSync(BEND, ['PROOF.bend'], { cwd: DEFINTIRE, encoding: 'utf8', env })
  assert.match(proof.stdout + proof.stderr, /ALL PROOFS CHECK/)
  const laws = [...readFileSync(join(DEFINTIRE, 'LAWS.bend'), 'utf8').matchAll(/^law (\w+):/gm)].map((match) => match[1])
  const proofs = [...readFileSync(join(DEFINTIRE, 'PROOF.bend'), 'utf8').matchAll(/^def Laws\.(\w+)\(/gm)].map((match) => match[1])
  assert.deepEqual([...proofs].sort(), [...laws].sort())
  assert.equal(laws.length, 9)
  const out = join(mkdtempSync(join(tmpdir(), 'wizardry-defintire-core-')), 'core.mjs')
  execFileSync(BEND, ['defintire.bend', '-o', out], { cwd: DEFINTIRE, env })
  assert.equal(readFileSync(join(DEFINTIRE, 'core.mjs'), 'utf8'), readFileSync(out, 'utf8'), 'defaults/defintire/core.mjs is stale: run `npm run core`')
})

test('defintire: readings, scores, ratings and climbing answer as the rules read', () => {
  // Where a reading stands: clamped between worst and best, turned round when lower is better.
  for (let i = 0; i < 3000; i++) {
    const [worst, best] = [below(200) - 100, below(200) - 100]
    const value = below(400) - 200 + pick([0, 0.25, 0.5])
    const at = core.position(value, worst, best)
    const expected = worst === best ? 0 : Math.round(1000 * Math.min(1, Math.max(0, (value - worst) / (best - worst))))
    assert.ok(Math.abs(at - expected) <= 1, JSON.stringify({ value, worst, best, at, expected }))
    assert.ok(at >= 0 && at <= 1000)
  }
  assert.equal(core.position(72, 100, 50), 560, 'lower is better: 72 between 100 (worst) and 50 (best)')
  assert.equal(core.position(NaN, 0, 1), 0)
  assert.equal(core.position(Infinity, 0, 1), 1000)
  assert.equal(core.reading('nan'), undefined, 'what is not a number is not a reading')

  assert.equal(core.reading('building...\nscore follows\n 0.75 \n'), 0.75)
  assert.equal(core.reading('12\n\n'), 12)
  assert.equal(core.reading('      87 /tmp/message.txt'), 87, 'as wc prints it')
  assert.equal(core.reading('no number here'), undefined)
  assert.equal(core.reading(''), undefined)
  assert.equal(core.judged('85\nClear and specific.'), 850)
  assert.equal(core.judged('Score: 7 out of 100, because 3 things'), 70)
  assert.equal(core.judged('250'), 1000, 'a judge cannot give more than all of it')
  assert.equal(core.judged('none'), undefined)
  assert.equal(core.judged(`${'x'.repeat(200_000)} 40`), 400, 'however long the reply')

  for (let i = 0; i < 2000; i++) {
    const marks = Array.from({ length: below(6) }, () => ({ weight: 1 + below(5), at: below(1001) }))
    const all = marks.reduce((sum, mark) => sum + mark.weight, 0)
    assert.equal(core.score(marks), all ? Math.floor(marks.reduce((sum, mark) => sum + mark.weight * mark.at, 0) / all) : 0)
  }

  // Verified only when everything measured was exact and nothing was left out.
  for (let i = 0; i < 2000; i++) {
    const kinds = Array.from({ length: below(5) }, () => pick(['exact', 'exact', 'proxy', 'judged']))
    const unmeasured = pick([0, 0, 1, 3])
    const verified = kinds.length > 0 && unmeasured === 0 && kinds.every((kind) => kind === 'exact')
    assert.equal(core.verified(kinds, unmeasured), verified, JSON.stringify({ kinds, unmeasured }))
    assert.equal(core.standing(kinds, unmeasured).startsWith('verified'), verified)
  }
  assert.equal(core.standing(['exact', 'judged'], 0), 'estimated: it rests on a proxy or a judgment')
  assert.equal(core.standing(['exact'], 2), 'partial: 2 criteria could not be measured')

  // Ratings: the table is Elo's expectation with K = 32, and points only move between the two.
  const favored = (gap) => (gap < 25 ? 16 : gap < 75 ? 14 : gap < 125 ? 12 : gap < 175 ? 10 : gap < 250 ? 8 : gap < 350 ? 5 : gap < 500 ? 3 : 1)
  for (const gap of [0, 50, 100, 150, 200, 300, 400, 700]) {
    const elo = 32 * (1 - 1 / (1 + 10 ** (-gap / 400)))
    assert.ok(Math.abs(favored(gap) - elo) <= 1.5, `${gap}: ${favored(gap)} against ${elo}`)
  }
  for (let i = 0; i < 4000; i++) {
    const [a, b] = [pick([0, 5, 20, 900, 1000, 1000, 1040, 1200, 1700]), pick([0, 10, 1000, 1000, 1100, 1500])]
    const outcome = pick(['First', 'Second', 'Draw'])
    const gap = Math.abs(a - b)
    const points = outcome === 'Draw' ? 16 - favored(gap) : (outcome === 'First') === (a >= b) ? favored(gap) : 32 - favored(gap)
    const toFirst = outcome === 'First' || (outcome === 'Draw' && a < b)
    const moved = Math.min(points, toFirst ? b : a)
    assert.deepEqual(core.rated(a, b, outcome), toFirst ? [a + moved, b - moved] : [a - moved, b + moved], JSON.stringify({ a, b, outcome }))
    const [x, y] = core.rated(a, b, outcome)
    assert.equal(x + y, a + b, 'the sum stays')
  }
  assert.deepEqual(core.rated(1000, 1000, 'First'), [1016, 984])
  assert.deepEqual(core.rated(1000, 1000, 'Draw'), [1000, 1000])
  assert.deepEqual(core.rated(1000, 1400, 'First'), [1029, 1371], 'an upset moves many points')
  assert.deepEqual([core.verdict('A\nIt is shorter.'), core.verdict(' b.'), core.verdict('DRAW'), core.verdict('About the same'), core.verdict('')], ['First', 'Second', 'Draw', 'Draw', 'Draw'])
  assert.deepEqual([core.byScores(3, 2), core.byScores(2, 3), core.byScores(2, 2)], ['First', 'Second', 'Draw'])

  for (let i = 0; i < 500; i++) {
    const [best, attempt] = [below(1001), below(1001)]
    assert.equal(core.keeps(best, attempt), attempt > best)
    assert.equal(core.kept(best, attempt), Math.max(best, attempt))
  }
  assert.equal(core.slug('  A Good Commit Message! '), 'a-good-commit-message')
  assert.equal(core.slug('fast_parser v2'), 'fast-parser-v2')
})

// A definition of something that is not mathematics, with one criterion of each kind.
const COMMIT = {
  name: 'Good commit message',
  answers: 'Given a message m for a change, can a reader tell from the subject alone what the change does?',
  objects: [{ symbol: 'm', type: 'String', meaning: 'the message' }, { symbol: 's(m)', type: 'String', meaning: 'its first line, the subject' }],
  primitives: ['what a change does'],
  axioms: [
    { name: 'short', statement: '|s(m)| \\le 72', stipulated: true },
    { name: 'imperative', statement: 's(m) \\text{ begins with a verb in the imperative}', stipulated: true }],
  examples: ['Fix the crash when the list is empty'],
  non_examples: ['fixed stuff (fails imperative)', 'A subject that goes on and on past seventy-two characters until nobody reads it (fails short)'],
  bend: 'def short(s: String) -> Bool:\n  Nat.is_le(String.length(s), 72n)\n',
  criteria: [
    { name: 'brevity', statement: '|s(m)|', kind: 'exact', weight: 2, command: 'sh -c \'head -n 1 "$1" | tr -d "\\n" | wc -c\' sh', worst: 100, best: 20 },
    { name: 'verbs', statement: '\\#\\{\\text{known verbs in } s(m)\\}', kind: 'proxy', command: 'sh -c \'head -n 1 "$1" | grep -c -i -E "^(fix|add|remove|make)" || true\' sh', worst: 0, best: 1 },
    { name: 'clarity', statement: 'P(\\text{reader states the change} \\mid s(m))', kind: 'judged', rubric: '0: says nothing of the change. 100: the change is plain from the subject.' }],
}

/** A judge that counts words: the more a text says "because", the better, and A beats B when it is longer. */
const complete = async ({ user }) => {
  if (user.includes('----- A -----')) {
    const [, a, b] = /----- A -----\n([\s\S]*?)\n\n----- B -----\n([\s\S]*?)\n----- END -----/.exec(user)
    return a.length === b.length ? 'DRAW' : a.length > b.length ? 'A\nIt says more.' : 'B\nIt says more.'
  }
  const judgedText = /----- WHAT IS JUDGED -----\n([\s\S]*?)\n----- END -----/.exec(user)[1]
  return `${judgedText.includes('because') ? 90 : 40}\nBy the rubric.`
}

test('defintire: a definition is kept only when it is one, and is written out in notation', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DEFINTIRE, { complete }, { cwd })
  const actions = root.get('actions')
  assert.deepEqual(plugins.list().find((plugin) => plugin.name === 'defintire').actions, ['defintire', 'defintire_define', 'defintire_measure', 'defintire_rank', 'defintire_climb'])

  const method = await actions.invoke('defintire', {}, { cwd })
  assert.match(method, /^DEFINTIRE: say what a thing is, in mathematical form/)
  assert.match(method, /Nothing is defined yet\.$/)
  assert.match(method, new RegExp(`jacobian \\(exact, typed mathematical operations\\) is not installed\\.[^\\n]*ask before installing it: \`UV_TOOL_DIR=${home}/tools UV_TOOL_BIN_DIR=${home}/bin [^\\n]*uv tool install --python 3\\.12 jacobian\``))

  // A tool installed for wizardry is found in its own bin, named by its full path, and on the PATH of a criterion's command.
  mkdirSync(join(home, 'bin'))
  writeFileSync(join(home, 'bin', 'jacobian'), '#!/bin/sh\necho 7\n', { mode: 0o755 })
  assert.match(await actions.invoke('defintire', {}, { cwd }), new RegExp(`jacobian is installed \\(\`${join(home, 'bin', 'jacobian')}\`\\)`))
  await actions.invoke('defintire_define', { ...COMMIT, name: 'Seven', criteria: [{ name: 'seven', statement: '7', kind: 'exact', command: 'jacobian', worst: 0, best: 10 }] }, { cwd })
  assert.match(await actions.invoke('defintire_measure', { definition: 'seven', text: 'x' }, { cwd }), /70\.0\/100 \(verified/)

  const refused = await actions.invoke('defintire_define', { ...COMMIT, answers: '', non_examples: [], criteria: [
    { name: 'a', statement: 'x', kind: 'exact' }, { name: 'a', statement: 'y', kind: 'judged' }, { name: 'c', statement: 'z', kind: 'vibes', weight: 0 }] }, { cwd })
  assert.match(refused, /^Not a definition yet:/)
  for (const why of [/say what question the definition answers/, /a definition that excludes nothing defines nothing/, /two criteria have the same name/,
    /"a" is exact and needs a command/, /"a" is judged and needs a rubric/, /"c" is "vibes": say exact, proxy or judged/, /"c" weighs nothing/, /Nothing was saved\.$/]) assert.match(refused, why)
  assert.ok(!existsSync(join(home, 'defintire', 'good-commit-message')))

  const defined = await actions.invoke('defintire_define', COMMIT, { cwd })
  const folder = join(home, 'defintire', 'good-commit-message')
  assert.match(defined, new RegExp(`^Defined "Good commit message", kept in ${folder}\\.`))
  const written = readFileSync(join(folder, 'definition.md'), 'utf8')
  for (const part of ['# Definition: Good commit message', '**Answers:** Given a message m', '- $m : String$ — the message', '## Primitives (left undefined)',
    '- **(short)** $|s(m)| \\le 72$ *(stipulated: a choice, not a finding)*', '## Non-examples', '```bend\ndef short(s: String) -> Bool:', '- **brevity** (exact, weight 2): $|s(m)|$ — from 100 (worst) to 20 (best), lower readings being better.',
    '- **clarity** (judged, weight 1)', 'Hill-climbable: 50% of the weight is exact, 25% proxy, 25% judged.']) assert.ok(written.includes(part), part)
  assert.equal(JSON.parse(readFileSync(join(folder, 'definition.json'), 'utf8')).root, cwd)
  assert.match(await actions.invoke('defintire', {}, { cwd }), /Defined so far: good-commit-message, seven$/)
  await assert.rejects(actions.invoke('defintire_measure', { definition: 'nothing', text: 'x' }, { cwd }), /No definition named "nothing"\. Defined so far: good-commit-message, seven\./)
  await root.fiber.dispose()
})

test('defintire: a candidate is scored by the definition\'s criteria, and the score says what it rests on', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DEFINTIRE, { complete }, { cwd })
  const actions = root.get('actions')
  await actions.invoke('defintire_define', COMMIT, { cwd })

  writeFileSync(join(cwd, 'good.txt'), 'Fix the crash when the list is empty\n\nIt crashed because nothing checked the length.\n')
  const good = await actions.invoke('defintire_measure', { definition: 'Good commit message', candidate: 'good.txt' }, { cwd })
  // brevity: 36 characters between 100 and 20 is 800; verbs: 1 of 1 is 1000; clarity: the judge said 90.
  assert.match(good, /^"good\.txt" against "Good commit message": 87\.5\/100 \(estimated: it rests on a proxy or a judgment\)/)
  assert.match(good, /brevity \[exact, weight 2\]: 80\.0\/100 \(read 36\)/)
  assert.match(good, /verbs \[proxy, weight 1\]: 100\.0\/100 \(read 1\)/)
  assert.match(good, /clarity \[judged, weight 1\]: 90\.0\/100/)
  const bad = await actions.invoke('defintire_measure', { definition: 'good commit message', text: 'various changes and some fixes to things all over the place, and also other stuff too', name: 'vague' }, { cwd })
  assert.match(bad, /^"vague" against "Good commit message": 19\.\d\/100/)
  await assert.rejects(actions.invoke('defintire_measure', { definition: 'good commit message', candidate: 'missing.txt' }, { cwd }), /"missing\.txt" is not a file here, and no text was given/)
  const scores = readFileSync(join(home, 'defintire', 'good-commit-message', 'scores.jsonl'), 'utf8').trim().split('\n').map((line) => JSON.parse(line))
  assert.deepEqual(scores.map((each) => [each.candidate, each.score]), [['good.txt', 875], ['vague', scores[1].score]])

  // With only exact criteria the score is verified; a command that fails leaves it partial, and says why.
  await actions.invoke('defintire_define', { ...COMMIT, name: 'Short subject', criteria: [COMMIT.criteria[0]] }, { cwd })
  assert.match(await actions.invoke('defintire_measure', { definition: 'short subject', candidate: 'good.txt' }, { cwd }), /80\.0\/100 \(verified: every criterion is exact\)/)
  await actions.invoke('defintire_define', { ...COMMIT, name: 'Broken', criteria: [COMMIT.criteria[0], { name: 'broken', statement: 'x', kind: 'exact', command: 'sh -c "echo no; exit 3"' }, { name: 'wordy', statement: 'y', kind: 'exact', command: 'echo words' }] }, { cwd })
  const partial = await actions.invoke('defintire_measure', { definition: 'broken', candidate: 'good.txt' }, { cwd })
  assert.match(partial, /80\.0\/100 \(partial: 2 criteria could not be measured\)/)
  assert.match(partial, /broken \[exact, weight 1\]: not measured \(its command ended with status 3: no\)/)
  assert.match(partial, /wordy \[exact, weight 1\]: not measured \(its command printed no number at the start of its last line: words/)
  await root.fiber.dispose()

  // Without a model, what is judged is left out and the score says so.
  const alone = await boot({ home, cwd, defaults: ['cordis'] })
  await alone.plugins.load(DEFINTIRE, undefined, { cwd })
  const unjudged = await alone.root.get('actions').invoke('defintire_measure', { definition: 'good commit message', candidate: 'good.txt' }, { cwd })
  assert.match(unjudged, /86\.6\/100 \(partial: 1 criterion could not be measured\)/)
  assert.match(unjudged, /clarity \[judged, weight 1\]: not measured \(no model is signed in to judge with\)/)
  assert.match(await alone.root.get('actions').invoke('defintire_rank', { definition: 'good commit message', candidates: ['good.txt', 'good.txt'] }, { cwd }), /no model is signed in to judge with\. Nothing was compared\./)
  await alone.root.fiber.dispose()
})

test('defintire: candidates are rated by comparing them two at a time, and the ratings carry on', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DEFINTIRE, { complete }, { cwd })
  const actions = root.get('actions')
  await actions.invoke('defintire_define', COMMIT, { cwd })
  await actions.invoke('defintire_define', { ...COMMIT, name: 'Short subject', criteria: [COMMIT.criteria[0]] }, { cwd })
  for (const [file, text] of [['a.txt', 'Fix it\n'], ['b.txt', 'Fix the crash on an empty list\n'], ['c.txt', 'Fix the crash on an empty list, because nothing checked\n']]) writeFileSync(join(cwd, file), text)

  assert.equal(await actions.invoke('defintire_rank', { definition: 'short subject', candidates: ['a.txt'] }, { cwd }), 'A ranking needs at least two candidates.')
  // By a judge, since a criterion is judged: the stand-in prefers the longer text, so c beats b beats a.
  const judged = await actions.invoke('defintire_rank', { definition: 'good commit message', candidates: ['a.txt', 'b.txt', 'c.txt'] }, { cwd })
  assert.match(judged, /^Ratings under "Good commit message" after 3 comparisons, each decided by a judge reading both against the definition:\n  1\. c\.txt: 1032 \(2 comparisons\)\n  2\. b\.txt: 1000 \(2 comparisons\)\n  3\. a\.txt: 968 \(2 comparisons\)\n/)
  const ratings = () => JSON.parse(readFileSync(join(home, 'defintire', 'good-commit-message', 'ratings.json'), 'utf8'))
  assert.equal(Object.values(ratings()).reduce((sum, each) => sum + each.rating, 0), 3000, 'points only moved between candidates')
  const again = await actions.invoke('defintire_rank', { definition: 'good commit message', candidates: ['a.txt', 'c.txt'] }, { cwd })
  assert.match(again, /after 1 comparison[\s\S]*1\. c\.txt: 10\d\d \(3 comparisons\)[\s\S]*b\.txt: 1000 \(2 comparisons\)/, 'what was rated before is still there')
  assert.equal(Object.values(ratings()).reduce((sum, each) => sum + each.rating, 0), 3000)

  // By the measured scores when every criterion is a command: the subject nearest 20 characters wins.
  const scored = await actions.invoke('defintire_rank', { definition: 'short subject', candidates: ['a.txt', 'b.txt', 'c.txt'] }, { cwd })
  assert.match(scored, /each decided by the measured scores:\n  1\. a\.txt: 1032 [^\n]*\n  2\. b\.txt: 1000 [^\n]*\n  3\. c\.txt: 968 /)
  await root.fiber.dispose()
})

/** An agent that improves the file it is given without a model: it shortens the subject by ten characters, or ruins it. */
const CLIMBER = `
import { readFileSync, writeFileSync, appendFileSync } from 'node:fs'
const place = JSON.parse(process.env.WIZARDRY_DIVISION)
const file = place.owns[0]
const text = readFileSync(file, 'utf8')
const [subject, ...rest] = text.split('\\n')
const brief = process.argv.at(-1)
if (!brief.includes('# Definition: Short subject') || !brief.includes('HOW IT SCORES NOW')) process.exit(3)
appendFileSync(process.env.CLIMB_LOG, process.cwd() + '\\n')
const ruin = process.cwd().endsWith('attempt-2')
writeFileSync(file, [ruin ? subject + ' and a great deal more that nobody asked to read here' : subject.slice(0, Math.max(20, subject.length - 10)), ...rest].join('\\n'))
console.log(ruin ? 'made it longer' : 'made it shorter')
`

test('defintire: a climb keeps only attempts that score higher, and changes the file only for something better', async () => {
  const { home, cwd } = scratch()
  writeFileSync(join(cwd, 'climber.mjs'), CLIMBER)
  process.env.CLIMB_LOG = join(cwd, 'climb.log')
  const { root, plugins } = await boot({ home, cwd, defaults: ['cordis'] })
  await plugins.load(DEFINTIRE, { agent: [process.execPath, join(cwd, 'climber.mjs')] }, { cwd })
  const actions = root.get('actions')
  await actions.invoke('defintire_define', { ...COMMIT, name: 'Short subject', criteria: [COMMIT.criteria[0]] }, { cwd })
  const subject = 'Fix the crash that happened whenever the list of items was empty'
  writeFileSync(join(cwd, 'message.txt'), `${subject}\n\nBody.\n`)

  const updates = []
  const said = await actions.invoke('defintire_climb', { definition: 'short subject', file: 'message.txt', rounds: 3, attempts: 2, hint: 'Shorter.' }, { cwd, update: (text) => updates.push(text) })
  // 64 characters is 45.0; each round one agent takes ten off and the other adds fifty-two.
  assert.match(said, /^Climbed "message\.txt" against "Short subject": 45\.0\/100 to 82\.5\/100 \(verified: every criterion is exact\)\./)
  assert.match(said, /round 1, attempt 1: 57\.5\/100 — kept\n  round 1, attempt 2: 0\.0\/100\n  round 2, attempt 1: 70\.0\/100 — kept\n  round 2, attempt 2: 0\.0\/100\n  round 3, attempt 1: 82\.5\/100 — kept\n  round 3, attempt 2: 3\.8\/100\n/)
  assert.equal(readFileSync(join(cwd, 'message.txt'), 'utf8'), `${subject.slice(0, 34)}\n\nBody.\n`, 'the file holds the best attempt, and the rest of it is as it was')
  const [climb] = readdirSync(join(home, 'defintire', 'short-subject', 'climbs'))
  const kept = join(home, 'defintire', 'short-subject', 'climbs', climb)
  assert.match(said, new RegExp(`message\\.txt now holds the best attempt\\. What it was before is in ${join(kept, 'original', 'message.txt')}\\.$`))
  assert.equal(readFileSync(join(kept, 'original', 'message.txt'), 'utf8'), `${subject}\n\nBody.\n`)
  assert.equal(readFileSync(process.env.CLIMB_LOG, 'utf8').trim().split('\n').length, 6, 'two agents a round, each in a directory of its own')
  assert.deepEqual(updates, ['round 1 of 3: best so far 45/100', 'round 2 of 3: best so far 57.5/100', 'round 3 of 3: best so far 70/100'])

  // Nothing better found: the file is not touched.
  writeFileSync(join(cwd, 'short.txt'), 'Fix the empty list\n')
  const before = readFileSync(join(cwd, 'short.txt'), 'utf8')
  const flat = await actions.invoke('defintire_climb', { definition: 'short subject', file: 'short.txt', rounds: 1 }, { cwd })
  assert.match(flat, /100\.0\/100 to 100\.0\/100[\s\S]*No attempt scored higher, so short\.txt is as it was\.$/)
  assert.equal(readFileSync(join(cwd, 'short.txt'), 'utf8'), before)
  assert.match(await actions.invoke('defintire_climb', { definition: 'short subject', file: 'nowhere.txt' }, { cwd }), /is not a file here/)
  delete process.env.CLIMB_LOG
  await root.fiber.dispose()
})
