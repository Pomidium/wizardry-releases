// The Bend core (bend/core.bend, compiled to core/core.mjs) against what it replaced.
//
// The laws in LAWS.bend are proven for every input. These tests cover what the laws do not say:
// that each def still answers as the TypeScript it took over from did, on thousands of generated
// inputs, that the compiled module in the repo is the one the Bend source compiles to, and that a
// long text costs no stack.

import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, mkdtempSync, readFileSync } from 'node:fs'
import { homedir, tmpdir } from 'node:os'
import { basename, extname, join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { core } from '../dist/core.js'

const ROOT = fileURLToPath(new URL('..', import.meta.url))
const BEND = [...(process.env.PATH ?? '').split(':'), join(homedir(), '.bend', 'bin')]
  .map((dir) => join(dir, 'bend')).find((file) => existsSync(file))

// A small deterministic generator, so a failure can be run again.
let seed = 20261118
const random = () => ((seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) / 2 ** 32)
const below = (n) => Math.floor(random() * n)
const pick = (items) => items[below(items.length)]
const some = (items, max) => Array.from({ length: below(max + 1) }, () => pick(items))
const text = (alphabet, max) => some(alphabet, max).join('')

// Lean, which `bend --verdict` rechecks the proofs with. Not everyone has it; bend alone still checks them.
const LEAN = [...(process.env.PATH ?? '').split(':'), join(homedir(), '.elan', 'bin')]
  .map((dir) => join(dir, 'lean')).find((file) => existsSync(file))

test('the proofs check, and the compiled core in the repo is what the Bend source compiles to', { skip: !BEND && 'bend is not installed' }, () => {
  const proof = spawnSync(BEND, ['PROOF.bend'], { cwd: ROOT, encoding: 'utf8', env: { ...process.env, BEND_NO_TELEMETRY: '1' } })
  assert.match(proof.stdout + proof.stderr, /ALL PROOFS CHECK/)
  // Every law has a proof: a law left open, or a proof of none, would both slip past a count.
  const laws = [...readFileSync(join(ROOT, 'LAWS.bend'), 'utf8').matchAll(/^law (\w+):/gm)].map((match) => match[1])
  const proofs = [...readFileSync(join(ROOT, 'PROOF.bend'), 'utf8').matchAll(/^def Laws\.(\w+)\(/gm)].map((match) => match[1])
  assert.deepEqual([...proofs].sort(), [...laws].sort())
  assert.ok(laws.length >= 48, `${laws.length} laws`)
  const out = join(mkdtempSync(join(tmpdir(), 'wizardry-core-')), 'core.mjs')
  execFileSync(BEND, ['bend/core.bend', '-o', out], { cwd: ROOT, env: { ...process.env, BEND_NO_TELEMETRY: '1' } })
  assert.equal(readFileSync(join(ROOT, 'core', 'core.mjs'), 'utf8'), readFileSync(out, 'utf8'), 'core/core.mjs is stale: run `npm run core`')
})

test('boot loads what the old rules loaded: shipped defaults step aside, switched-off plugins stay off', () => {
  const NAMES = ['bend', 'echo', 'mem', 'model', 'x']
  const entries = (where) => [...new Set(some(NAMES, 4))].map((name) => ({ name, path: `/${where}/${name}.js` }))
  for (let i = 0; i < 2000; i++) {
    const shipped = entries('shipped')
    const found = [...entries('home'), ...entries('cwd')]
    const disabled = some(NAMES, 3)
    const taken = new Set(found.map((entry) => entry.name))
    const expected = [...shipped.filter((entry) => !taken.has(entry.name)), ...found].filter((entry) => !disabled.includes(entry.name))
    assert.deepEqual(core.plan(shipped, found, disabled), expected)
  }
})

test('plugin files are recognised and named as before', () => {
  const MODULE_FILES = ['.ts', '.mts', '.js', '.mjs']
  const FILES = ['bend.js', 'a.ts', 'b.mts', 'c.mjs', 'README.md', '.hidden.js', '_folder', 'notes', 'x.y.js', 'data.json', 'a.', 'my.plugin', '']
  for (const name of FILES) {
    for (const folder of [true, false]) {
      for (const entry of [true, false]) {
        const expected = !(name.startsWith('.') || name.startsWith('_') || name === '') && (folder ? entry : MODULE_FILES.includes(extname(name)))
        assert.equal(core.usable(name, folder, entry), expected, `usable ${name} ${folder} ${entry}`)
      }
    }
    if (name && !name.startsWith('.')) assert.equal(core.stem(name), basename(name, extname(name)), `stem ${name}`)
  }
  const pickName = (candidates) => candidates.find((value) => typeof value === 'string' && value && value !== 'apply' && value !== 'default')
  for (let i = 0; i < 500; i++) {
    const candidates = [...some([undefined, '', 'apply', 'default', 'echo', 'weather', 42], 4), 'fallback']
    assert.equal(core.pickName(candidates), pickName(candidates))
  }
})

test('the command line is read as before', () => {
  const PI_ONLY = new Set(['install', 'remove', 'uninstall', 'list', 'config', 'mcp'])
  const commandOf = (first) => first === '--help' || first === '-h' ? 'Help'
    : first === '--version' || first === '-v' ? 'Version'
    : first && PI_ONLY.has(first) ? 'PiOnly' : first === 'auth' ? 'Auth' : first === 'update' ? 'Update' : 'Run'
  for (const first of [undefined, '', '--help', '-h', '--version', '-v', ...PI_ONLY, 'auth', 'update', 'plugins', 'hello', '-p'])
    assert.equal(core.commandOf(first), commandOf(first), `command ${first}`)

  const splitArgs = (argv) => {
    const extra = []
    const rest = []
    for (let i = 0; i < argv.length; i++) {
      const arg = argv[i]
      if (arg === '--') {
        rest.push(...argv.slice(i))
        break
      }
      if (arg === '--gate') extra.push('gate')
      else if (arg === '--plugin') {
        const source = argv[++i]
        if (!source) return undefined
        extra.push(source)
      } else rest.push(arg)
    }
    return { extra, rest }
  }
  const WORDS = ['--gate', '--plugin', '--', '-p', 'hi', '', './x.js', '--model', 'gate', '--session-dir', '--no-session', '--use-theme']
  for (let i = 0; i < 4000; i++) {
    const argv = some(WORDS, 7)
    assert.deepEqual(core.splitArgs(argv), splitArgs(argv), JSON.stringify(argv))
    const piArgs = [
      '--no-builtin-tools', '--no-extensions', '--no-skills', '--no-prompt-templates', '--no-context-files',
      ...(argv.includes('--session-dir') || argv.includes('--no-session') ? [] : ['--session-dir', '/s']),
      '--theme', '/t', ...(argv.includes('--use-theme') ? [] : ['--use-theme', 'a/b']),
      ...argv,
    ]
    assert.deepEqual(core.piArgs(argv, '/s', '/t', 'a/b'), piArgs, JSON.stringify(argv))
  }
})

test('a restart carries over the arguments the old rules carried over', () => {
  const restartArgs = (rest, saidBefore, session) => {
    const said = [...saidBefore]
    const kept = []
    for (let i = rest.length - 1; i >= 0; i--) {
      const at = said.lastIndexOf(rest[i])
      if (at >= 0) said.splice(at, 1)
      else if (rest[i] !== '--') kept.unshift(rest[i])
    }
    const args = []
    for (let i = 0; i < kept.length; i++) {
      if (['-c', '--continue', '-r', '--resume'].includes(kept[i])) continue
      if (['--session', '--fork', '--session-id'].includes(kept[i])) i++
      else args.push(kept[i])
    }
    return session ? [...args, '--session', session] : args
  }
  const WORDS = ['-c', '--continue', '-r', '--resume', '--session', '--fork', '--session-id', '--', 'hi', 'there', '@f.txt', '--model', 'm', '-p']
  for (let i = 0; i < 4000; i++) {
    const rest = some(WORDS, 8)
    const said = some(['hi', 'there', '@f.txt', 'absent', '-p'], 3)
    const session = pick([undefined, '/sessions/a.jsonl'])
    assert.deepEqual(core.restartArgs(rest, said, session), restartArgs(rest, said, session), JSON.stringify({ rest, said, session }))
  }
})

test('calls and results read as before', () => {
  const words = (value) => value.replace(/[_\-\s]+/g, ' ').trim()
  const actionTitle = (action) => {
    if (action.title) return action.title
    if (action.native) return action.name
    const owner = words(action.owner)
    const name = words(action.name)
    return name === owner || name.startsWith(`${owner} `) ? name : `${owner} ${name}`
  }
  const brief = (value) => {
    const line = value.replace(/\s+/g, ' ').trim()
    if (!line) return '""'
    return line.length > 72 ? `${line.slice(0, 71)}…` : line
  }
  const whole = (value) => value.replace(/\r/g, '').replace(/\t/g, '   ').split('\n').join('\n    ')
  const resultView = (output, expanded) => {
    const lines = output.replace(/\r/g, '').replace(/\t/g, '   ').trimEnd().split('\n')
    const shown = expanded ? lines : lines.slice(0, 10)
    return { shown, more: lines.length - shown.length }
  }
  const LETTERS = ['a', 'b', 'é', '_', '-', ' ', '\t', '\n', 'cordis', 'plugin', 'load']
  for (let i = 0; i < 3000; i++) {
    const name = text(LETTERS, 6)
    const owner = text(LETTERS, 3)
    assert.equal(core.words(name), words(name), JSON.stringify(name))
    for (const title of [undefined, '', 'code review']) {
      for (const native of [false, true]) {
        assert.equal(core.actionTitle(title, native, name, owner), actionTitle({ title, native, name, owner }), JSON.stringify({ title, native, name, owner }))
      }
    }
    assert.equal(core.mine(name, owner), name === owner || name.startsWith(`${owner} `))
    const value = text(['x', 'yz ', ' ', '\n', '\t', '\r', 'word', '{"a":1}', 'é'], 60)
    assert.equal(core.brief(value), brief(value), JSON.stringify(value))
    assert.equal(core.expand(value, '    '), whole(value), JSON.stringify(value))
    const output = text(['row', ' ', '\n', '\n', '\r\n', '\t', 'x'], 40)
    for (const expanded of [false, true]) assert.deepEqual(core.resultView(output, expanded), resultView(output, expanded), JSON.stringify(output))
  }
})

test('focus, rtk, the updater and the words about plugins answer as before', () => {
  const NAMES = ['focus', 'bash', 'read', 'write', 'think', 'become']
  for (let i = 0; i < 3000; i++) {
    const current = [...new Set(some(NAMES, 6))]
    const drop = some(NAMES, 4)
    const take = some(NAMES, 4)
    const active = new Set(current)
    for (const name of drop) if (name !== 'focus') active.delete(name)
    for (const name of take) active.add(name)
    assert.deepEqual(core.focusActive(current, drop, take), [...active], JSON.stringify({ current, drop, take }))
    assert.deepEqual(core.without(NAMES, current), NAMES.filter((name) => !current.includes(name)))
    assert.deepEqual(core.only(drop, current), drop.filter((name) => current.includes(name)))

    const command = text(['rtk', ' ', '\t', 'git', 'rtkx', ' status', '\n'], 4)
    for (const raw of [false, true]) {
      assert.equal(core.rtkSkips(raw, command), raw || !command.trim() || /^\s*rtk(\s|$)/.test(command), JSON.stringify(command))
    }

    const said = text(['wizardry: ', 'updated to abc', 'up to date', '\n', '\n', 'x'], 6)
    const line = said.split('\n').filter(Boolean).at(-1)?.replace(/^wizardry: /, '') ?? 'the update did not say what happened'
    assert.equal(core.updateLine(said), line, JSON.stringify(said))
    assert.equal(core.updated(line), line.startsWith('updated to'))

    const state = pick(['active', 'pending', 'failed'])
    const actions = some(NAMES, 3)
    assert.equal(core.label('echo', state), state === 'active' ? 'echo' : `echo (${state})`)
    assert.equal(core.inspectLine('echo', state, '/p/echo.js', actions), `echo [${state}] /p/echo.js\n  actions: ${actions.join(', ') || '(none)'}`)
    assert.equal(core.loadedText('Loaded', 'echo', state, actions), state === 'pending'
      ? 'Loaded "echo" [pending]: it injects a service nothing provides yet, and starts when one does.'
      : `Loaded "echo" [${state}]. Actions: ${actions.join(', ') || '(none)'}`)
    const notes = some(['', 'a note', 'another'], 3)
    assert.equal(core.described('What it does.', notes), ['What it does.', ...notes.filter(Boolean)].join('\n\n'))
  }
  assert.equal(core.systemPrompt('base', ''), 'base')
  assert.equal(core.systemPrompt('base', 'careful'), 'base\n\nWhat you have chosen to be:\ncareful')
  assert.match(core.basePrompt('/work', '2026-11-18'), /^You are wizardry[\s\S]*\nWorking directory: \/work\nDate: 2026-11-18$/)
})

test('the proofs pass the kernel that is itself proven in Lean, with nothing unsafe or foreign under them', { skip: (!BEND || !LEAN) && 'bend --verdict needs Lean' }, () => {
  const env = { ...process.env, BEND_NO_TELEMETRY: '1', PATH: `${join(LEAN, '..')}:${process.env.PATH}` }
  const verdict = spawnSync(BEND, ['PROOF.bend', '--verdict'], { cwd: ROOT, encoding: 'utf8', env })
  assert.match(verdict.stdout + verdict.stderr, /ALL PROOFS CHECK/)
  assert.doesNotMatch(verdict.stdout + verdict.stderr, /SOME PROOFS FAIL|unsafe/)
})

test('switching plugins, the update words and the caps answer as the TypeScript they replaced did', () => {
  const NAMES = ['pi', 'cordis', 'fs', 'shell', 'self', 'rtk', 'update', 'memory', 'bend']
  for (let i = 0; i < 3000; i++) {
    const defaults = [...new Set(some(NAMES, 7))]
    const disabled = [...new Set(some(NAMES, 4))]
    const name = pick(NAMES)
    assert.deepEqual(core.builtinsAtBoot(defaults, disabled), defaults.filter((each) => !disabled.includes(each)))
    assert.deepEqual(core.switchedOff(disabled, name), disabled.includes(name) ? disabled : [...disabled, name])
    assert.deepEqual(core.switchedOn(disabled, name), disabled.filter((each) => each !== name))
    // The round trips the laws promise, seen from here.
    assert.ok(!core.builtinsAtBoot(defaults, core.switchedOff(disabled, name)).includes(name))
    assert.equal(core.builtinsAtBoot(defaults, core.switchedOn(disabled, name)).includes(name), defaults.includes(name))

    const loaded = [...new Set(some(NAMES, 7))]
    const wanted = [...new Set(some(NAMES, 7))]
    assert.deepEqual(core.restoreUnloads(loaded, wanted), loaded.filter((each) => !wanted.includes(each) && each !== 'pi' && each !== 'cordis'))
    assert.equal(core.isCore(name), name === 'pi' || name === 'cordis')

    const word = pick([undefined, '', 'on', 'off', 'On', 'now', 'off ', 'o'])
    assert.equal(core.updateAsked(word), !word ? 'Now' : word === 'on' ? 'On' : word === 'off' ? 'Off' : 'Unclear', JSON.stringify(word))
  }
  for (const builtin of [false, true]) for (const isDefault of [false, true]) assert.equal(core.remembered(builtin, isDefault), !builtin || !isDefault)
  assert.deepEqual([core.switchAct(true, false), core.switchAct(false, true), core.switchAct(true, true), core.switchAct(false, false)], ['Loads', 'Unloads', 'Stays', 'Stays'])

  // The caps, as look.ts drew them before they moved to Bend.
  const HAT = [
    String.raw`         /\         `,
    String.raw`        /  \        `,
    String.raw`       / *  \       `,
    String.raw`      /    . \      `,
    String.raw`     /  *     \     `,
    String.raw` ___/__________\___ `,
    String.raw`(__________________)`,
  ]
  const SPARKS = [[2, 9, '*+*.  .*'], [3, 11, '. .*+*. '], [4, 8, '*.  .*+*'], [0, 13, '  .*.   '], [1, 5, '     .*.'], [2, 16, ' .+.    ']]
  const hatFrame = (frame) => {
    const rows = HAT.map((row) => [...row])
    for (const [row, col, frames] of SPARKS) rows[row][col] = frames[frame % 8]
    return rows.map((row) => row.join(''))
  }
  assert.deepEqual(core.hat(), HAT)
  for (let frame = 0; frame < 40; frame++) assert.deepEqual(core.hatFrame(frame), hatFrame(frame), `frame ${frame}`)
  assert.deepEqual(core.smallHat(), [String.raw`_/\_   `, String.raw`_/\_.  `, String.raw`_/\_*  `, String.raw`_/\_ + `, String.raw`_/\_ * `, String.raw`_/\_  .`])
  const ink = (part) => (part === '+' ? 'text' : part === '*' ? 'mdLink' : part === '.' ? 'dim' : 'accent')
  for (const part of ['+', '*', '.', '/', ' ', '_', '(', ')', '\\', '   /', '___']) assert.equal(core.ink(part), ink(part[0]), JSON.stringify(part))
})

test('the header, the session, rtk and the home directory answer as the TypeScript they replaced did', () => {
  // The header: packing, where the text goes, and which row holds what.
  const oldPack = (items, separator, width) => {
    const lines = []
    for (const item of items) {
      const last = lines.at(-1)
      if (last !== undefined && (last + separator + item).length <= width) lines[lines.length - 1] = last + separator + item
      else lines.push(item)
    }
    return lines
  }
  const oldRows = (hat, hatWidth, width, text) => {
    const beside = width - 1 - hatWidth - 3
    let rows
    if (beside >= 36) {
      const lines = text(beside)
      const offset = Math.max(0, hat.length - lines.length)
      const height = Math.max(hat.length, lines.length)
      rows = Array.from({ length: height }, (_, i) => {
        const line = lines[i - offset]
        return (hat[i] ?? ' '.repeat(hatWidth)) + (line ? ' '.repeat(3) + line : '')
      })
    } else {
      rows = [...hat, '', ...text(width - 1)]
    }
    return rows.map((row) => ' ' + row)
  }
  const hat = core.hat()
  for (let i = 0; i < 3000; i++) {
    const items = Array.from({ length: below(9) }, () => 'x'.repeat(1 + below(14)))
    const separator = pick([' · ', ', ', ' '])
    const width = below(70) - 3
    let at = 0
    const packed = core.pack(items.map((item) => item.length), separator.length, width).map((count) => items.slice(at, (at += count)).join(separator))
    assert.deepEqual(packed, oldPack(items, separator, width), JSON.stringify({ items, separator, width }))

    const wide = below(130)
    const lines = (room) => Array.from({ length: (room * 7 + i) % 12 }, (_, n) => (n % 3 === 1 ? '' : `line ${n} in ${room}`))
    const { where, room } = core.layout(wide, 20)
    assert.equal(where, wide - 24 >= 36 ? 'Beside' : 'Under')
    assert.equal(room, where === 'Beside' ? wide - 24 : Math.max(1, wide - 1))
    // Under the cap the old code wrapped to at least one column, which is the room Bend answers.
    const now = where === 'Beside' ? core.headerBeside(hat, lines(room), 20) : core.headerUnder(hat, lines(room))
    assert.deepEqual(now, oldRows(hat, 20, wide, (given) => lines(Math.max(1, given))), `width ${wide}`)

    const shown = some(['', 'a', 'b'], 2)
    const more = below(3)
    assert.equal(core.blankView(shown, more), shown.length === 1 && !shown[0] && !more)
    assert.equal(core.capMoves(i % 2 === 0, i % 3 === 0), i % 2 === 0 || i % 3 === 0)
    assert.equal(core.nextFrame(i % 40), (i % 40 + 1) % 8)

    // The session.
    const words = some(['on', 'off', 'once', 'model', 'thinking'], 4)
    const typed = pick(['', 'o', 'on', ' of ', 'x', 'th', '  m'])
    assert.deepEqual(core.completions(words, typed), words.filter((word) => word.startsWith(typed.trim())))
    const written = some(['', 'careful', 'terse'], 4)
    assert.equal(core.lastIdentity(written), written.at(-1) ?? '')
    const [wanted, attached, tui, idle, active] = [below(2), below(2), below(2), below(2), below(2)].map(Boolean)
    assert.equal(core.restartsNow(wanted, attached, tui, idle), wanted && attached && tui && idle)
    assert.equal(core.staysAway(wanted, attached, active), wanted && attached && !active)

    // rtk.
    const command = pick(['git status', 'ls', 'echo hi'])
    const out = pick(['', '  ', 'rtk git status\n', ' rtk ls ', command, `${command}\n`])
    const code = pick([0, 1, 2, 3, 4, 127])
    assert.equal(core.rtkTakes(code, out, command), (code === 0 || code === 3) && out.trim() && out.trim() !== command ? out.trim() : undefined, JSON.stringify({ code, out, command }))

    // Where wizardry keeps its things.
    const [chosen, oldChosen] = [pick(['', '/w']), pick(['', '/i'])]
    const [hasHome, hasOld, link, named] = [below(2), below(2), below(2), below(2)].map(Boolean)
    assert.equal(core.homeOf(chosen, oldChosen, '/h/.wizardry', '/h/.izardry', hasHome, hasOld), chosen || oldChosen || (!hasHome && hasOld ? '/h/.izardry' : '/h/.wizardry'))
    assert.equal(core.adoptsHome(named, hasHome, hasOld, link), !named && !hasHome && hasOld && !link)
    assert.equal(core.adoptsCommand('izardry', link, hasHome), link && !hasHome)
    assert.equal(core.isBuiltinSource(named, hasHome, hasOld), hasHome && (named || !hasOld))
  }
  assert.equal(core.adoptsCommand('wizardry', true, false), false)
  assert.equal(core.adopted(false, false), undefined)
  assert.equal(core.adopted(true, false), 'izardry is now wizardry: your plugins and sessions are now in ~/.wizardry.')
  assert.equal(core.adopted(true, true), 'izardry is now wizardry: your plugins and sessions are now in ~/.wizardry, and the command is now `wizardry`.')
  assert.deepEqual(core.rtkPlaces('/x/rtk', ['/a'], '/h'), ['/x/rtk'])
  assert.deepEqual(core.rtkPlaces(undefined, ['/a', '', '/b/'], '/h'), ['/a/rtk', '/b/rtk', '/opt/homebrew/bin/rtk', '/usr/local/bin/rtk', '/h/.cargo/bin/rtk', '/h/.local/bin/rtk'])
  assert.deepEqual(core.pluginDirs('/h/plugins', '/h/plugins'), ['/h/plugins'])
  assert.deepEqual(core.pluginDirs('/h/plugins', '/w/plugins'), ['/h/plugins', '/w/plugins'])
  assert.deepEqual([core.underHome('~/p.js'), core.underHome('/p.js'), core.underHome('~x')], ['p.js', undefined, undefined])
  assert.deepEqual([0, 1, 2, 3, 4, 5, 6, 99].map(core.stateName), ['pending', 'loading', 'active', 'failed', 'disposed', 'unloading', 'unknown', 'unknown'])
  assert.equal(core.listing('fs', 'active', 'builtin:fs', ['read', 'write']), 'fs [active] builtin:fs\n  read, write\n')
  assert.equal(core.listing('rtk', 'active', 'builtin:rtk', []), 'rtk [active] builtin:rtk\n')
  assert.deepEqual(core.saidOf(['hi'], ['a.md', 'b.md']), ['hi', '@a.md', '@b.md'])
  assert.equal(core.carriedOn(), 'wizardry updated; this session carried on')
  assert.equal(core.carriedOn('updated to abc (x)'), 'wizardry updated to abc (x); this session carried on')
  assert.deepEqual(core.pluginRows([{ name: 'fs', state: 'active', source: 'builtin:fs' }, { name: 'self', state: 'pending', source: 'builtin:self' }]),
    ['  fs              builtin:fs', '  self (pending)  builtin:self'])
  assert.equal(core.gateSummary('x'.repeat(2000)).length, 1500)
  assert.match(core.help(), /^wizardry - Pi on Cordis\.[\s\S]*--plugin <name\|path>[\s\S]*Nothing asks for approval unless you pass --gate\.\n$/)
  assert.match(core.inspectText(['a [active] builtin:a\n  actions: (none)'], []), /^Loaded plugins:\na \[active\] builtin:a\n  actions: \(none\)\n\nBuiltin plugins not loaded: \(none\)\n\nA plugin is a \.ts or \.js file\.[\s\S]*call cordis_map: the map of the framework you run on\.$/)
})

test('a very long text or result costs no stack', () => {
  const long = 'some words_and-more\t'.repeat(200_000)
  assert.equal(core.brief(long).length, 72)
  assert.equal(core.words('a_'.repeat(300_000)).length, 599_999)
  assert.equal(core.expand('a\n'.repeat(300_000), '  ').length, 1_200_000)
  const view = core.resultView(`${'line\n'.repeat(500_000)}${' \n'.repeat(200_000)}`, false)
  assert.deepEqual(view, { shown: Array(10).fill('line'), more: 499_990 })
  assert.equal(core.resultView('line\n'.repeat(500_000), true).shown.length, 500_000)
})
