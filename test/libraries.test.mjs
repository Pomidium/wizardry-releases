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
