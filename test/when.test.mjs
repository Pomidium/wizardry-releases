// The when default: if-then rules that cost nothing until they fire.
//
// Its laws (defaults/when/LAWS.bend) are proven for every input. These tests cover what the laws
// do not say: that the compiled Bend is the one in the repo, that cues read as documented, and
// that what fires reaches the agent in the right place, once, and otherwise not at all.

import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs'
import { homedir, tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { boot as bootWizardry } from '../dist/index.js'
import { core } from '../defaults/when/index.js'

const WHEN = fileURLToPath(new URL('../defaults/when', import.meta.url))
const find = (name, extra) => [...(process.env.PATH ?? '').split(':'), extra].map((dir) => join(dir, name)).find((file) => existsSync(file))
const BEND = find('bend', join(homedir(), '.bend', 'bin'))
const LEAN = find('lean', join(homedir(), '.elan', 'bin'))

test('when: the proofs check, and the compiled Bend in the repo is what the source compiles to', { skip: !BEND && 'bend is not installed' }, () => {
  const env = { ...process.env, BEND_NO_TELEMETRY: '1', PATH: `${LEAN ? join(LEAN, '..') : ''}:${process.env.PATH}` }
  const proof = spawnSync(BEND, ['PROOF.bend', ...(LEAN ? ['--verdict'] : [])], { cwd: WHEN, encoding: 'utf8', env })
  assert.match(proof.stdout + proof.stderr, /ALL PROOFS CHECK/)
  const laws = [...readFileSync(join(WHEN, 'LAWS.bend'), 'utf8').matchAll(/^law (\w+):/gm)].map((match) => match[1])
  const proofs = [...readFileSync(join(WHEN, 'PROOF.bend'), 'utf8').matchAll(/^def Laws\.(\w+)\(/gm)].map((match) => match[1])
  assert.deepEqual([...proofs].sort(), [...laws].sort())
  assert.equal(laws.length, 5)
  const out = join(mkdtempSync(join(tmpdir(), 'wizardry-when-core-')), 'core.mjs')
  execFileSync(BEND, ['when.bend', '-o', out], { cwd: WHEN, env })
  assert.equal(readFileSync(join(WHEN, 'core.mjs'), 'utf8'), readFileSync(out, 'utf8'), 'defaults/when/core.mjs is stale: run `npm run core`')
})

test('when: a cue is whole words, phrases joined by +, and a final * for any ending', () => {
  const cases = [
    ['ui', 'make a UI please', true], ['ui', 'build a quick guide', false],
    ['landing page', 'a Landing-Page, now', true], ['landing page', 'a page for landing', false],
    ['write + html', 'write /x/index.html', true], ['write + html', 'read /x/index.html', false], ['html + write', 'write /x/index.html', true],
    ['component*', 'two new Components', true], ['component*', 'compose', false],
    ['', 'anything', false], ['+', 'anything', false], ['*', 'anything', false], ['ui', '', false],
  ]
  for (const [cue, text, hits] of cases) assert.equal(core.hits(cue, text), hits, `${JSON.stringify(cue)} on ${JSON.stringify(text)}`)
  assert.equal(core.hits('needle', `${'hay '.repeat(12000)}needle`), true, 'a long text costs no stack')
  const rules = [{ name: 'a', when: { asked: ['ui'] } }, { name: 'b', when: { asked: 'ui', doing: ['write'] } }, { name: 'c', when: {} }]
  assert.deepEqual(core.due(rules, 'asked', [], 'a ui'), ['a', 'b'])
  assert.deepEqual(core.due(rules, 'asked', ['a'], 'a ui'), ['b'])
  assert.deepEqual(core.due(rules, 'thinking', [], 'a ui'), [])
  assert.equal(core.told([]), '')
  assert.equal(core.doing('write', ['/a/b.css', 'body {}\n/* html */']), 'write /a/b.css body {}', 'past its first line, a file\'s content is not read for cues')
})

/** A wizardry with only `when`, and a stand-in for Pi that keeps the handlers it is given. */
async function session(rules) {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-when-'))
  const home = join(dir, 'home')
  mkdirSync(join(home, 'when'), { recursive: true })
  const file = join(home, 'when', 'rules.json')
  if (rules) writeFileSync(file, JSON.stringify(rules))
  const { root, plugins } = await bootWizardry({ home, cwd: dir, shipped: join(tmpdir(), 'wizardry-no-shipped-defaults'), defaults: [] })
  await plugins.load(WHEN)
  const on = {}
  const entries = []
  root.emit('pi/ready', { on: (event, handler) => { on[event] = handler; return () => delete on[event] }, appendEntry: (type, data) => entries.push({ type: 'custom', customType: type, data }) })
  const piCtx = { cwd: dir, sessionManager: { getBranch: () => entries } }
  return { on, piCtx, file, entries, plugins, call: (event, fields) => on[event]({ type: event, ...fields }, piCtx) }
}

const BLUE = { name: 'blue-ui', when: { asked: ['ui', 'landing page'], doing: ['write + html', 'write + css'], thinking: ['stylesheet'], seen: ['tailwind'] }, then: 'Make the UI blue.' }

test('when: with nothing to say, nothing reaches the agent', async () => {
  const { call } = await session([BLUE])
  assert.equal(await call('before_agent_start', { prompt: 'fix the parser bug in src/parse.rs' }), undefined)
  assert.equal(await call('message_end', { message: { role: 'assistant', content: [{ type: 'thinking', thinking: 'the lexer is off by one' }] } }), undefined)
  assert.equal(await call('tool_call', { toolName: 'write', input: { path: 'src/parse.rs', content: 'fn main() {\n// html css ui\n}' } }), undefined)
  assert.equal(await call('tool_result', { content: [{ type: 'text', text: 'ok' }] }), undefined)
  const empty = await session()
  assert.equal(await empty.call('before_agent_start', { prompt: 'make a ui' }), undefined)
})

test('when: a rule is said where the agent is, once', async () => {
  const asked = await session([BLUE])
  const first = await asked.call('before_agent_start', { prompt: 'build me a landing page' })
  assert.deepEqual(first, { message: { customType: 'when', content: '[when: blue-ui] Make the UI blue.', display: true } })
  assert.equal(await asked.call('before_agent_start', { prompt: 'now another ui' }), undefined)
  assert.equal(await asked.call('tool_call', { toolName: 'write', input: { path: 'index.html', content: '' } }), undefined)
  assert.deepEqual(asked.entries.map((entry) => entry.data), [{ name: 'blue-ui' }])
  // A resumed session knows what was said; after a compaction it is said again.
  asked.call('session_start', {})
  assert.equal(await asked.call('before_agent_start', { prompt: 'a ui' }), undefined)
  asked.call('session_compact', {})
  assert.ok(await asked.call('before_agent_start', { prompt: 'a ui' }))

  const doing = await session([BLUE])
  await doing.call('message_end', { message: { role: 'assistant', content: [] } })
  const held = await doing.call('tool_call', { toolName: 'write', input: { path: '/site/index.html', content: '<html>' } })
  assert.equal(held.block, true)
  assert.match(held.reason, /^Not run yet: .*\n\[when: blue-ui\] Make the UI blue\.\nMake the call again/)
  assert.match((await doing.call('tool_call', { toolName: 'write', input: { path: '/site/style.css', content: '' } })).reason, /held with another call of this step/)
  await doing.call('message_end', { message: { role: 'assistant', content: [] } })
  assert.equal(await doing.call('tool_call', { toolName: 'write', input: { path: '/site/index.html', content: '<html>' } }), undefined)

  const thinking = await session([BLUE])
  await thinking.call('message_end', { message: { role: 'assistant', content: [{ type: 'thinking', thinking: 'I need a stylesheet first' }] } })
  assert.equal(await thinking.call('tool_call', { toolName: 'ls', input: {} }), undefined)
  assert.deepEqual(await thinking.call('tool_result', { content: [{ type: 'text', text: 'a b' }] }), { content: [{ type: 'text', text: 'a b' }, { type: 'text', text: '[when: blue-ui] Make the UI blue.' }] })

  const seen = await session([BLUE])
  assert.equal((await seen.call('tool_result', { content: [{ type: 'text', text: 'deps: tailwind 4' }] })).content[1].text, '[when: blue-ui] Make the UI blue.')
})

test('when: a rule can run a command, is read again when the file changes, and how to write one is itself a rule', async () => {
  const { call, file, plugins, on } = await session([{ name: 'branch', when: { asked: ['commit'] }, then: 'Branch:', run: 'echo main' }])
  assert.equal((await call('before_agent_start', { prompt: 'commit this' })).message.content, '[when: branch] Branch:\nmain')
  writeFileSync(file, JSON.stringify([{ name: 'tabs', when: { asked: ['python'] }, then: 'Use tabs.' }, { then: 'no name' }, 7]))
  assert.equal((await call('before_agent_start', { prompt: 'a python script' })).message.content, '[when: tabs] Use tabs.')
  writeFileSync(file, '{ not json')
  assert.equal(await call('before_agent_start', { prompt: 'a python script' }), undefined)
  const taught = (await call('before_agent_start', { prompt: 'whenever you write tests, use vitest' })).message.content
  assert.match(taught, /^\[when: when\] If the user is stating a standing preference/)
  assert.ok(taught.includes(file))
  assert.equal(await call('before_agent_start', { prompt: 'and always use pnpm' }), undefined)
  assert.deepEqual(plugins.list().find((plugin) => plugin.name === 'when').actions, [], 'it puts nothing in the tool list')
  await plugins.unload('when')
  assert.deepEqual(Object.keys(on), [])
})
