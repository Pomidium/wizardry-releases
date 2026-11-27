// The queue default: tasks that wait, each started when the agent is done with the one before.
//
// Its laws (defaults/queue/LAWS.bend) are proven for every input. These tests cover what the laws
// do not say: that the compiled Bend is the one in the repo, that `/queue ...` reads as
// documented, and that the next task reaches Pi at the right moment, once, and otherwise not.

import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, mkdtempSync, readFileSync } from 'node:fs'
import { homedir, tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { boot as bootWizardry } from '../dist/index.js'
import { core } from '../defaults/queue/index.js'

const QUEUE = fileURLToPath(new URL('../defaults/queue', import.meta.url))
const find = (name, extra) => [...(process.env.PATH ?? '').split(':'), extra].map((dir) => join(dir, name)).find((file) => existsSync(file))
const BEND = find('bend', join(homedir(), '.bend', 'bin'))
const LEAN = find('lean', join(homedir(), '.elan', 'bin'))

test('queue: the proofs check, and the compiled Bend in the repo is what the source compiles to', { skip: !BEND && 'bend is not installed' }, () => {
  const env = { ...process.env, BEND_NO_TELEMETRY: '1', PATH: `${LEAN ? join(LEAN, '..') : ''}:${process.env.PATH}` }
  const proof = spawnSync(BEND, ['PROOF.bend', ...(LEAN ? ['--verdict'] : [])], { cwd: QUEUE, encoding: 'utf8', env })
  assert.match(proof.stdout + proof.stderr, /ALL PROOFS CHECK/)
  const laws = [...readFileSync(join(QUEUE, 'LAWS.bend'), 'utf8').matchAll(/^law (\w+):/gm)].map((match) => match[1])
  const proofs = [...readFileSync(join(QUEUE, 'PROOF.bend'), 'utf8').matchAll(/^def Laws\.(\w+)\(/gm)].map((match) => match[1])
  assert.deepEqual([...proofs].sort(), [...laws].sort())
  assert.equal(laws.length, 10)
  const out = join(mkdtempSync(join(tmpdir(), 'wizardry-queue-core-')), 'core.mjs')
  execFileSync(BEND, ['queue.bend', '-o', out], { cwd: QUEUE, env })
  assert.equal(readFileSync(join(QUEUE, 'core.mjs'), 'utf8'), readFileSync(out, 'utf8'), 'defaults/queue/core.mjs is stale: run `npm run core`')
})

test('queue: tasks go first in first out, blanks are no tasks, and /queue reads a few words and takes the rest as a task', () => {
  assert.deepEqual(core.add(['a'], [' b ', '', ' \n', 'c\n']), ['a', 'b', 'c'])
  assert.equal(core.next(['a', 'b']), 'a')
  assert.deepEqual(core.rest(['a', 'b']), ['b'])
  assert.deepEqual(core.drop(['a', 'b', 'c'], 2), ['a', 'c'])
  assert.deepEqual(core.drop(['a'], 5), ['a'])
  assert.deepEqual(core.drop(['a'], 0), ['a'])
  const cases = [
    ['', { $: 'Show' }], ['list', { $: 'Show' }], ['drop', { $: 'Show' }], [' clear ', { $: 'Clear' }], ['pause', { $: 'Pause' }],
    ['go', { $: 'Go' }], ['resume', { $: 'Go' }], ['drop 2', { $: 'Drop', n: 2 }],
    ['drop the old table', { $: 'Add', task: 'drop the old table' }], ['go through the logs', { $: 'Add', task: 'go through the logs' }],
    [' fix the tests ', { $: 'Add', task: 'fix the tests' }],
  ]
  for (const [args, command] of cases) assert.deepEqual(core.command(args), command, JSON.stringify(args))
  const long = 'word '.repeat(40000)
  assert.equal(core.add([], [long])[0].length, long.length - 1, 'a long task costs no stack')
  assert.match(core.listed(['fix the tests\nall of them', 'write the changelog'], false), /^Queued, next first:\n1\. fix the tests all of them\n2\. write the changelog\nEach starts/)
  assert.match(core.listed([], false), /^Nothing is queued\./)
})

/** A wizardry with Pi and `queue`, and a stand-in for Pi's API that keeps what it is given. */
async function session(entries = []) {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-queue-'))
  const { root, plugins } = await bootWizardry({ home: join(dir, 'home'), cwd: dir, shipped: join(tmpdir(), 'wizardry-no-shipped-defaults'), defaults: ['pi'] })
  await plugins.load(QUEUE)
  const actions = root.get('actions')
  const on = {}
  const commands = {}
  const sent = []
  const said = []
  const state = { idle: true }
  root.get('pi').attach({
    registerTool() {}, getAllTools: () => [], getActiveTools: () => [], setActiveTools() {}, getThinkingLevel: () => 'high',
    registerCommand: (name, command) => { commands[name] = command },
    on: (event, handler) => { (on[event] ??= []).push(handler); return () => { on[event] = on[event].filter((other) => other !== handler) } },
    appendEntry: (type, data) => entries.push({ type: 'custom', customType: type, data }),
    sendUserMessage: (text) => { sent.push(text); state.idle = false },
  })
  const piCtx = { cwd: dir, mode: 'print', isIdle: () => state.idle, ui: { notify: (text) => said.push(text) }, sessionManager: { getBranch: () => entries } }
  const call = async (event, fields) => { for (const handler of on[event] ?? []) await handler({ type: event, ...fields }, piCtx) }
  /** The agent is done with what it was on. */
  const done = async (fields) => { state.idle = true; await call('agent_settled', { aborted: false, ...fields }) }
  const queue = (args) => commands.queue.handler(args, piCtx)
  const waits = () => entries.filter((entry) => entry.customType === 'queue:state').at(-1)?.data
  await call('session_start', {})
  return { on, call, done, queue, sent, said, state, entries, waits, plugins, actions, root, piCtx }
}

test('queue: each task starts when the agent is done with the one before, in order, and never before', async () => {
  const { done, queue, sent, said, state, waits, actions } = await session()
  await done()
  assert.deepEqual(sent, [], 'with nothing queued, nothing is ever sent')

  state.idle = false // the agent is on a task of the user's
  await queue('fix the tests')
  await queue('write the changelog')
  assert.match(await actions.invoke('queue', { add: ['tag the release', '  '] }), /^Queued, next first:\n1\. fix the tests\n2\. write the changelog\n3\. tag the release\nDo not start these now\./)
  assert.deepEqual(sent, [], 'nothing starts while the agent works')
  assert.deepEqual(waits(), { items: ['fix the tests', 'write the changelog', 'tag the release'], paused: false })

  await done()
  assert.deepEqual(sent, ['fix the tests'])
  assert.match(said.at(-1), /^Queue: on to fix the tests \(2 waiting after it\)\.$/)
  await done()
  await done()
  assert.deepEqual(sent, ['fix the tests', 'write the changelog', 'tag the release'])
  assert.deepEqual(waits(), { items: [], paused: false })
  await done()
  assert.equal(sent.length, 3, 'each is handed over once')

  // With the agent on nothing, a queued task is one it can start at once.
  await queue('one more')
  assert.deepEqual(sent.at(-1), 'one more')
  assert.equal(await actions.invoke('queue', {}), 'Nothing is queued.')
})

test('queue: a task that was stopped or failed holds the queue until /queue go', async () => {
  const { done, queue, call, sent, said, state, waits } = await session()
  state.idle = false
  await queue('second')
  await queue('third')
  await done({ aborted: true })
  assert.deepEqual(sent, [], 'Escape does not lead into the next task')
  assert.match(said.at(-1), /^Queue held with 2 waiting: the last task was stopped\. \/queue go carries on/)
  assert.deepEqual(waits(), { items: ['second', 'third'], paused: true })
  await done()
  assert.deepEqual(sent, [], 'and it stays held through the tasks the user gives meanwhile')
  await queue('go')
  assert.deepEqual(sent, ['second'])

  await call('message_end', { message: { role: 'assistant', stopReason: 'error', content: [] } })
  await done()
  assert.deepEqual(sent, ['second'], 'an error does not lead into the next task either')
  assert.match(said.at(-1), /the last task ended in an error/)
  state.idle = false
  await queue('go')
  assert.deepEqual(sent, ['second'], 'go while the agent works waits for it to be done')
  assert.match(said.at(-1), /^Queue carries on/)
  await call('message_end', { message: { role: 'assistant', stopReason: 'stop', content: [] } })
  await done()
  assert.deepEqual(sent, ['second', 'third'])

  // pause, drop and clear.
  state.idle = false
  await queue('a')
  await queue('b')
  await queue('c')
  await queue('pause')
  await queue('drop 2')
  assert.deepEqual(waits(), { items: ['a', 'c'], paused: true })
  await done()
  assert.equal(sent.length, 2)
  await queue('clear')
  assert.deepEqual(waits(), { items: [], paused: false })
  await done()
  assert.equal(sent.length, 2)
})

test('queue: it belongs to the conversation, comes back held, and goes with the plugin', async () => {
  const first = await session()
  first.state.idle = false
  await first.queue('later')
  // The same conversation, opened again by another process.
  const again = await session(first.entries.map((entry) => ({ ...entry })))
  assert.match(again.said.at(-1), /^Queue held with 1 waiting: this session was opened again\./)
  await again.done()
  assert.deepEqual(again.sent, [], 'a queue from before does not start by itself')
  await again.queue('go')
  assert.deepEqual(again.sent, ['later'])
  // A conversation with no queue in it starts with none.
  const fresh = await session()
  assert.equal(fresh.waits(), undefined)
  assert.equal(fresh.said.length, 0)

  assert.deepEqual(again.plugins.list().find((plugin) => plugin.name === 'queue').actions, ['queue'])
  await again.plugins.unload('queue')
  assert.equal(again.actions.get('queue'), undefined)
  assert.equal(again.on.agent_settled?.length ?? 0, 0, 'its hooks into Pi go with it')
  await again.root.fiber.dispose()
})

test('queue: an agent deployed on a part of a task has no queue', async () => {
  process.env.WIZARDRY_DIVISION = '{}'
  try {
    const { actions, on } = await session()
    assert.equal(actions.get('queue'), undefined)
    assert.equal(on.agent_settled, undefined)
  } finally { delete process.env.WIZARDRY_DIVISION }
})
