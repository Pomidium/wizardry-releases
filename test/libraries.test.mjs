// The libraries wizardry stands on, checked against what wizardry counts on them to do.
//
// wizardry's own decisions are written in Bend and proven (LAWS.bend). Cordis, Pi, pi-tui and jiti
// are other people's JavaScript, which no proof reaches, so each behaviour wizardry relies on is
// pinned here instead. When a dependency is upgraded and one of these fails, the library changed
// under wizardry: fix the caller named in the test, not the test.

import assert from 'node:assert/strict'
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { Context, Service } from '@deepseek-ai/cordis'
import * as pi from '@earendil-works/pi-coding-agent'
import { Text, truncateToWidth, visibleWidth, wrapTextWithAnsi } from '@earendil-works/pi-tui'
import { createJiti } from 'jiti'

const scratch = () => mkdtempSync(join(tmpdir(), 'wizardry-lib-'))

test('cordis: effect runs its setup at once and keeps the returned function for unload (actions.ts)', async () => {
  const root = new Context()
  const seen = []
  const fiber = root.plugin({
    name: 'probe',
    apply(ctx) {
      ctx.effect(() => {
        seen.push('setup')
        return () => seen.push('cleanup')
      })
      seen.push('after effect')
    },
  })
  await fiber.await()
  assert.deepEqual(seen, ['setup', 'after effect'])
  await fiber.dispose()
  assert.deepEqual(seen, ['setup', 'after effect', 'cleanup'])
})

test('cordis: a plugin\'s fiber is named after it, and unloading removes its listeners (plugins.ts, actions.ts)', async () => {
  const root = new Context()
  const heard = []
  let name
  const fiber = root.plugin({
    name: 'listener',
    apply(ctx) {
      name = ctx.fiber.name
      ctx.on('probe/event', (value) => { heard.push(value) })
    },
  })
  await fiber.await()
  assert.equal(name, 'listener')
  root.emit('probe/event', 1)
  await fiber.dispose()
  root.emit('probe/event', 2)
  assert.deepEqual(heard, [1])
})

test('cordis: serial stops at the first listener that answers (action/before refusals, actions.ts)', async () => {
  const root = new Context()
  const asked = []
  root.on('probe/ask', () => { asked.push('first') })
  root.on('probe/ask', () => { asked.push('second'); return 'no' })
  root.on('probe/ask', () => { asked.push('third'); return 'never' })
  assert.equal(await root.serial('probe/ask'), 'no')
  assert.deepEqual(asked, ['first', 'second'])
  const quiet = new Context()
  assert.equal(await quiet.serial('probe/ask'), undefined)
})

test('cordis: a service is reachable by name, and a plugin that injects a missing one waits for it (pi.ts, self.ts)', async () => {
  const root = new Context()
  class Clock extends Service {
    constructor(ctx) {
      super(ctx, 'clock')
    }
    now() {
      return 42
    }
  }
  let started = 0
  const waiting = root.plugin({ name: 'needs-clock', inject: ['clock'], apply(ctx) { started = ctx.clock.now() } })
  await new Promise((resolve) => setTimeout(resolve, 20))
  assert.equal(started, 0, 'it does not start without the service')
  await root.plugin(Clock)
  await waiting.await()
  assert.equal(started, 42)
  assert.equal(root.get('clock').now(), 42)
  assert.equal(root.get('nothing'), undefined)
})

test('cordis: a plugin that throws rejects its fiber (plugins.ts reports it and cleans up)', async () => {
  const root = new Context()
  const fiber = root.plugin({ name: 'broken', apply() { throw new Error('boom') } })
  await assert.rejects(fiber.await(), /boom/)
})

test('pi: parseArgs separates messages and @files from options (restartArgs in boot.ts)', () => {
  const parsed = pi.parseArgs(['--model', 'x', '-p', 'hello there', '@notes.txt', '--thinking', 'low'])
  assert.deepEqual(parsed.messages, ['hello there'])
  assert.deepEqual(parsed.fileArgs, ['notes.txt'])
  assert.deepEqual(pi.parseArgs([]).messages, [])
})

test('pi: the tool definitions wizardry turns into actions exist under the names it shows (fs.ts, shell.ts)', async () => {
  const dir = scratch()
  const made = [
    pi.createReadToolDefinition, pi.createWriteToolDefinition, pi.createEditToolDefinition,
    pi.createGrepToolDefinition, pi.createFindToolDefinition, pi.createLsToolDefinition, pi.createBashToolDefinition,
  ].map((create) => create(dir))
  assert.deepEqual(made.map((tool) => tool.name), ['read', 'write', 'edit', 'grep', 'find', 'ls', 'bash'])
  for (const tool of made) {
    assert.equal(typeof tool.description, 'string')
    assert.equal(typeof tool.execute, 'function')
    assert.equal(tool.parameters.type, 'object')
  }
  const text = (result) => result.content.map((part) => part.text).join('\n')
  const [read, write, edit, , , ls, bash] = made

  await write.execute('t1', { path: 'note.txt', content: 'one\ntwo\n' }, undefined, undefined, undefined)
  assert.equal(readFileSync(join(dir, 'note.txt'), 'utf8'), 'one\ntwo\n', 'write puts the content in the file, relative to its cwd')
  assert.match(text(await read.execute('t2', { path: 'note.txt' }, undefined, undefined, undefined)), /one\ntwo/)
  await edit.execute('t3', { path: 'note.txt', edits: [{ oldText: 'two', newText: 'three' }] }, undefined, undefined, undefined)
  assert.equal(readFileSync(join(dir, 'note.txt'), 'utf8'), 'one\nthree\n', 'edit replaces exactly the text named')
  assert.match(text(await ls.execute('t4', {}, undefined, undefined, undefined)), /note\.txt/)
  assert.match(text(await bash.execute('t5', { command: 'printf "%s" "$PWD" && echo " ok"' }, undefined, undefined, undefined)), / ok/)
  await assert.rejects(read.execute('t6', { path: 'missing.txt' }, undefined, undefined, undefined), 'a failed tool call rejects rather than answering')
})

test('pi: the entry point and the header helpers wizardry calls are exported (pi.ts, look.ts)', () => {
  assert.equal(typeof pi.main, 'function')
  for (const helper of ['keyHint', 'keyText', 'rawKeyHint']) assert.equal(typeof pi[helper], 'function', helper)
  pi.initTheme('dark', false) // the key hints colour themselves with Pi's current theme
  assert.equal(typeof pi.rawKeyHint('/', 'commands'), 'string')
  assert.match(pi.rawKeyHint('/', 'commands'), /commands/)
})

test('pi-tui: widths ignore colour codes, and cutting or wrapping never exceeds the width (look.ts)', () => {
  const purple = (value) => `\x1b[35m${value}\x1b[0m`
  assert.equal(visibleWidth('wizardry'), 8)
  assert.equal(visibleWidth(purple('wizardry')), 8)
  assert.equal(visibleWidth(''), 0)
  for (const width of [1, 5, 12, 40]) {
    const cut = truncateToWidth(purple('a line that is rather long for the room it has'), width)
    assert.ok(visibleWidth(cut) <= width, `cut to ${width}`)
    const wrapped = wrapTextWithAnsi(purple('several words that will not fit on one line of the header'), width)
    assert.ok(wrapped.length >= 1)
    for (const line of wrapped) assert.ok(visibleWidth(line) <= Math.max(width, 7), `wrapped to ${width}`)
    assert.equal(wrapped.join('').replace(/\x1b\[[0-9;]*m/g, '').replace(/\s/g, ''), 'severalwordsthatwillnotfitononelineoftheheader', 'wrapping loses no text')
  }
  assert.equal(truncateToWidth('short', 40), 'short')
  const component = new Text('', 0, 0)
  component.setText('hello')
  assert.ok(component.render(20).join('\n').includes('hello'), 'Text shows what setText gave it')
})

test('jiti: loads TypeScript and ES module plugins, and reads the file again after an edit (plugins.ts)', async () => {
  const dir = scratch()
  const jiti = createJiti(import.meta.url, { moduleCache: false, fsCache: false })
  const file = join(dir, 'plugin.ts')
  writeFileSync(file, `export const name: string = 'one'\nexport default function apply(): number { return 1 }\n`)
  const first = await jiti.import(file)
  assert.equal(first.name, 'one')
  assert.equal(first.default(), 1)
  writeFileSync(file, `export const name: string = 'two'\nexport default function apply(): number { return 2 }\n`)
  const second = await jiti.import(file)
  assert.equal(second.name, 'two', 'an edited plugin is loaded fresh, which is what plugin_reload promises')

  mkdirSync(join(dir, 'pkg'))
  writeFileSync(join(dir, 'pkg', 'index.mjs'), `export const actions = [{ name: 'x' }]\n`)
  assert.equal((await jiti.import(join(dir, 'pkg', 'index.mjs'))).actions[0].name, 'x')
  await assert.rejects(jiti.import(join(dir, 'absent.js')))
  writeFileSync(join(dir, 'broken.ts'), `export const = \n`)
  await assert.rejects(jiti.import(join(dir, 'broken.ts')), 'a file that does not parse is an error, not an empty module')
})

test('pi: its directory follows PI_CODING_AGENT_DIR, read when asked and not when loaded (apart.ts)', () => {
  const kept = process.env.PI_CODING_AGENT_DIR
  try {
    process.env.PI_CODING_AGENT_DIR = '/somewhere/wizardry/pi'
    assert.equal(pi.getAgentDir(), '/somewhere/wizardry/pi')
    process.env.PI_CODING_AGENT_DIR = '/somewhere/else'
    assert.equal(pi.getAgentDir(), '/somewhere/else', 'setting it after Pi is imported is not too late')
  } finally {
    if (kept === undefined) delete process.env.PI_CODING_AGENT_DIR
    else process.env.PI_CODING_AGENT_DIR = kept
  }
})

test('pi: the options that keep it from reading what lies around it are still its options (pi_args in core.bend)', () => {
  const parsed = pi.parseArgs(['--no-themes', '--no-mcp', '--no-approve', '--no-extensions', '--no-skills', '--no-prompt-templates', '--no-context-files', '--no-builtin-tools', 'hello'])
  assert.deepEqual(parsed.messages, ['hello'], 'none of them is taken for a message')
  assert.equal(parsed.noThemes, true)
  assert.equal(parsed.noMcp, true)
  assert.equal(parsed.projectTrustOverride, false, '--no-approve: project-local files are not trusted, and nobody is asked')
  assert.deepEqual([parsed.noExtensions, parsed.noSkills, parsed.noPromptTemplates, parsed.noContextFiles], [true, true, true, true])
  assert.deepEqual(parsed.diagnostics ?? [], [])
})

test('pi: a bash tool can be given the environment its commands see (shell.ts)', async () => {
  const bash = pi.createBashToolDefinition(scratch(), { spawnHook: (context) => ({ ...context, env: { ...context.env, WIZARDRY_SEEN: 'as it was' } }) })
  const result = await bash.execute('t1', { command: 'printf "%s" "$WIZARDRY_SEEN"' }, undefined, undefined, undefined)
  assert.match(result.content.map((part) => part.text).join(''), /as it was/)
})

test('pi runs the tool calls of one step at the same time, and no tool of wizardry\'s asks to run alone', async () => {
  // "Calls in one step" is how the standing prompt says independent work is done at once: it
  // counts on Pi's agent executing them concurrently, and on no tool being marked sequential.
  const { Agent } = await import('@earendil-works/pi-agent-core')
  assert.equal(new Agent({}).toolExecution, 'parallel')
  const { boot } = await import('../dist/index.js')
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-libraries-'))
  const { root } = await boot({ home: join(dir, 'home'), cwd: dir, defaults: ['pi', 'fs', 'shell', 'cordis', 'self'] })
  const tools = []
  root.get('pi').attach({ registerTool: (tool) => tools.push(tool), registerCommand() {}, on() {} })
  assert.ok(tools.length > 10)
  assert.deepEqual(tools.filter((tool) => tool.executionMode === 'sequential').map((tool) => tool.name), [])
  await root.fiber.dispose()
})
