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
    : first && PI_ONLY.has(first) ? 'PiOnly' : first === 'auth' ? 'Auth' : first === 'update' ? 'Update'
    : first === 'export' ? 'Export' : first === 'delete' ? 'Delete' : 'Run'
  for (const first of [undefined, '', '--help', '-h', '--version', '-v', ...PI_ONLY, 'auth', 'update', 'export', 'delete', 'plugins', 'hello', '-p', '--export', 'exports'])
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
      '--no-themes', '--no-mcp', '--no-approve',
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
    for (const [returned, waits] of [[false, false], [false, true], [true, false], [true, true]]) {
      // wanted: bound; attached: Pi knows the tool.
      assert.equal(core.inFront(wanted, attached, active, returned, waits), !wanted || (!attached || returned ? !waits : active))
    }

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
  assert.match(core.help(), /^wizardry - Pi on Cordis\.[\s\S]*wizardry export \[folder\][\s\S]*--plugin <name\|path>[\s\S]*Nothing asks for approval unless you pass --gate\.\n[\s\S]*removes nothing until you add --yes; it exports first\.\n$/)
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

// Kept apart, export and delete. There was no TypeScript before these: the references below are
// the rules as they are said, written a second time, and the laws in LAWS.bend say what must
// hold of them for every input.

const inside = (path, root) => path === root || path.startsWith(root.endsWith('/') ? root : `${root}/`)
const inDir = (dir, file) => (dir.endsWith('/') ? `${dir}${file}` : `${dir}/${file}`)

test('Pi is pointed at wizardry\'s own directory, and only logins and the named settings come over', () => {
  assert.equal(core.ownPi('/h/.wizardry'), '/h/.wizardry/pi')
  assert.equal(core.oldPi('', '/h'), '/h/.pi/agent')
  assert.equal(core.oldPi('/elsewhere/pi', '/h'), '/elsewhere/pi')
  assert.deepEqual(core.piEnv('/w'), [
    { name: 'PI_CODING_AGENT_DIR', value: '/w/pi' }, { name: 'PI_SKIP_VERSION_CHECK', value: '1' }, { name: 'PI_TELEMETRY', value: '0' }])
  assert.deepEqual(core.piEnvCleared(), ['PI_CODING_AGENT_SESSION_DIR', 'PI_PACKAGE_DIR'])
  assert.deepEqual(core.piEnvTouched(), ['PI_CODING_AGENT_DIR', 'PI_SKIP_VERSION_CHECK', 'PI_TELEMETRY', 'PI_CODING_AGENT_SESSION_DIR', 'PI_PACKAGE_DIR'])
  assert.deepEqual(core.broughtFiles(), ['auth.json', 'models.json'])

  const KEPT = ['defaultProvider', 'defaultModel', 'defaultThinkingLevel', 'modelThinkingLevels', 'enabledModels', 'httpProxy', 'shellPath', 'shellCommandPrefix']
  const ADDONS = ['packages', 'extensions', 'skills', 'prompts', 'themes', 'enableSkillCommands', 'sessionDir', 'defaultProjectTrust', 'selfUpdateCommand']
  const KEYS = [...KEPT, ...ADDONS, 'theme', 'lastChangelogVersion', 'quietStartup', '', 'Packages']
  for (let i = 0; i < 2000; i++) {
    const keys = some(KEYS, 12)
    const brought = core.settingsBrought(keys)
    assert.deepEqual(brought, keys.filter((key) => KEPT.includes(key)), JSON.stringify(keys))
    assert.ok(!brought.some((key) => ADDONS.includes(key)))
  }
  for (const hasOwn of [true, false]) for (const hasOld of [true, false]) for (const [old, own] of [['/a', '/b'], ['/a', '/a']]) {
    assert.equal(core.brings(hasOwn, hasOld, old, own), !hasOwn && hasOld && old !== own)
  }
  assert.equal(core.broughtSaid(['auth.json', 'settings.json'], '/w/pi', '/h/.pi/agent'),
    'logins and settings are now its own, in /w/pi. Brought over auth.json, settings.json from /h/.pi/agent, which is no longer read: `wizardry delete old` removes it, and `wizardry auth login` signs in here.')
  assert.match(core.broughtSaid([], '/w/pi', '/h/.pi/agent'), /There was nothing to bring over from \/h\/\.pi\/agent, which is no longer read/)
})

test('export and delete read their arguments as they say they do', () => {
  const KNOWN = ['--yes', '-y', '--no-export', '--to']
  const bare = (argv) => {
    const out = []
    let value = false
    for (const arg of argv) {
      if (!value && !arg.startsWith('-')) out.push(arg)
      value = !value && arg === '--to'
    }
    return out
  }
  const WORDS = ['old', 'all', 'conversations', 'memories', '--yes', '-y', '--no-export', '--to', '/out', 'out', '--force', '', '-x']
  for (let i = 0; i < 4000; i++) {
    const argv = some(WORDS, 6)
    const words = bare(argv)
    const options = argv.filter((arg) => arg.startsWith('-'))
    const at = argv.indexOf('--to')
    assert.deepEqual(core.deleteAsked(argv), {
      what: words[0] ?? '',
      yes: argv.includes('--yes') || argv.includes('-y'),
      waived: argv.includes('--no-export'),
      to: at >= 0 ? argv[at + 1] ?? '' : '',
      clear: words.length === 1 && options.every((option) => KNOWN.includes(option)),
    }, JSON.stringify(argv))
    assert.equal(core.exportAsked(argv), options.length === 0 && words.length < 2 ? words[0] ?? '' : undefined, JSON.stringify(argv))
  }
  assert.equal(core.exportAsked([]), '')
  assert.equal(core.exportAsked(['~/keep']), '~/keep')
})

test('delete names only what was asked for, and nothing when that would take the home directory, the export or wizardry along', () => {
  const HOMES = ['/h/.wizardry', '/h/.wizardry/', '/h', '/', '', 'rel/.wizardry', '/h/.pi/agent/w', '/data/w']
  const OLDS = ['/h/.pi/agent', '/h/.wizardry/pi', '/h/.wizardry', '/h', '/', '/opt/pi', 'rel/pi', '', '/data']
  const USERS = ['/h', '/h/user', '/']
  const TOS = ['', '/h/out', '/h/.wizardry/out', '/h/.wizardry/sessions/x', '/h/.wizardry/memory', '/h/.pi/agent/out', '/opt/pi', '/data/w', '/h/.wizardry']
  const WHATS = ['conversations', 'memories', 'old', 'all', 'everything', '']
  const wanted = (what, home, old) => {
    if (!home.startsWith('/')) return []
    if (what === 'old') return inside(old, home) || inside(home, old) ? [] : [old]
    return what === 'conversations' ? [inDir(home, 'sessions')] : what === 'memories' ? [inDir(home, 'memory')] : what === 'all' ? [home] : []
  }
  let some_go = 0
  for (const what of WHATS) for (const home of HOMES) for (const old of OLDS) for (const userhome of USERS) for (const to of TOS) {
    const said = JSON.stringify({ what, home, old, userhome, to })
    const paths = wanted(what, home, old)
    const safe = paths.every((path) => path.startsWith('/')) && !paths.some((path) => inside(userhome, path)) && !paths.some((path) => inside(to, path))
    const doomed = core.doomed(what, home, old, userhome, to)
    assert.deepEqual(doomed, safe ? paths : [], said)
    assert.equal(core.whyNot(what, home, old, userhome, to) === '', doomed.length > 0, `a reason is given exactly when nothing goes: ${said}`)
    for (const path of doomed) {
      assert.ok(path.startsWith('/') && path !== '/', said)
      assert.ok(!inside(userhome, path) && !inside(to, path), said)
      if (what === 'old') assert.ok(!inside(home, path) && !inside(path, home), said)
      else assert.ok(inside(path, home), `only wizardry's own: ${said}`)
    }
    some_go += doomed.length
    for (const yes of [true, false]) for (const exported of ['Kept', 'Failed', 'Waived']) {
      assert.deepEqual(core.goes(doomed, yes, exported), yes && exported !== 'Failed' ? doomed : [], said)
    }
    if (what !== 'old') assert.deepEqual(core.emptied(what, doomed, userhome), [])
  }
  assert.ok(some_go > 500)

  assert.deepEqual(core.doomed('old', '/h/.wizardry', '/h/.pi/agent', '/h', '/h/out'), ['/h/.pi/agent'])
  assert.deepEqual(core.emptied('old', ['/h/.pi/agent'], '/h'), ['/h/.pi'], '~/.pi goes too if that leaves it empty')
  assert.deepEqual(core.emptied('old', ['/h/agent'], '/h'), [], 'but never the home directory')
  assert.deepEqual(core.dangling([
    { path: '/h/.local/bin/pi', target: '/h/.pi/agent/bin/pi' }, { path: '/h/.local/bin/wizardry', target: '/h/.wizardry/app/dist/bin.js' },
    { path: '/h/.local/bin/agent', target: '/h/.pi/agent' }, { path: '/h/.local/bin/near', target: '/h/.pi/agents/x' }], ['/h/.pi/agent']),
  ['/h/.local/bin/pi', '/h/.local/bin/agent'])
  assert.deepEqual(core.linkDirs('/h/.local/bin/wizardry', '', '/h'), ['/h/.local/bin'])
  assert.deepEqual(core.linkDirs('/opt/bin/wizardry', '/custom/bin', '/h'), ['/opt/bin', '/custom/bin', '/h/.local/bin'])

  assert.equal(core.deletePreview('old', [{ path: '/h/.pi/agent', bytes: 163_000_000 }], ['/h/.local/bin/pi'], '/h/out', false), [
    'wizardry delete old would delete:',
    '  /h/.pi/agent  (163 MB)',
    '  /h/.local/bin/pi  (a command that points into it)',
    'First, every conversation and memory is exported to /h/out.',
    'Nothing has been deleted. To go ahead: wizardry delete old --yes',
    ''].join('\n'))
  assert.match(core.deletePreview('all', [{ path: '/w', bytes: 999 }, { path: '/x', bytes: 1 }, { path: '/y', bytes: 45_300 }, { path: '/z', bytes: 7_000_000_000 }], [], '', true),
    /\/w  \(999 bytes\)\n  \/x  \(1 byte\)\n  \/y  \(45 KB\)\n  \/z  \(7 GB\)\nNothing is exported first: you said --no-export\.\nNothing has been deleted\. To go ahead: wizardry delete all --yes --no-export\n$/)
  assert.match(core.deletedSaid([{ path: '/w/sessions', bytes: 2000 }], [], '/h/out', false), /^deleted:\n  \/w\/sessions  \(2 KB\)\nEvery conversation and memory was exported first, to \/h\/out\.\n$/)
  assert.match(core.deleteUsage(), /^usage: wizardry delete <what> \[--yes\]/)
})

test('an export puts each conversation under where it came from, and writes it to read', () => {
  assert.equal(core.exportDir('', '/h', '2026-11-21', 0), '/h/wizardry-export-2026-11-21')
  assert.equal(core.exportDir('', '/h', '2026-11-21', 1), '/h/wizardry-export-2026-11-21-2')
  assert.equal(core.exportDir('/keep/here', '/h', '2026-11-21', 3), '/keep/here')
  assert.deepEqual(core.origins('/h/.wizardry', '/h/.pi/agent'), [
    { name: 'wizardry', dir: '/h/.wizardry/sessions' }, { name: 'pi', dir: '/h/.pi/agent/sessions' }])
  assert.equal(core.sessionsDir('/h/.wizardry'), '/h/.wizardry/sessions')
  for (const [dir, fits] of [['/h/out', true], ['/h/.wizardry/sessions', false], ['/h/.wizardry/sessions/x', false], ['/h/.pi/agent/sessions/y', false], ['/h/.wizardry/sessions2', true]]) {
    assert.equal(core.exportFits(dir, '/h/.wizardry', '/h/.pi/agent'), fits, dir)
  }
  assert.equal(core.conversationTo('/out', 'pi', '--proj--/a.jsonl'), '/out/conversations/pi/--proj--/a.jsonl')
  assert.equal(core.readable('/out/a.jsonl'), '/out/a.md')
  assert.equal(core.readable('/out/a'), '/out/a.md')
  assert.ok(core.isConversation('x.jsonl') && !core.isConversation('x.json'))
  assert.deepEqual(core.leftOver(['app', 'bin', 'memory', 'pi', 'plugins', 'sessions', 'tools', 'notes'], ['conversations', 'memory']), ['notes'], 'programs are not exported')

  const at = '2026-11-20 19:16:34'
  assert.equal(core.transcriptHead('a.jsonl', '/work', at), '# Conversation of 2026-11-20 19:16\n\n- Directory: /work\n- Kept whole in: a.jsonl\n\n')
  assert.equal(core.piece('user', '', at, 'hello\nthere\n\n'), '## User · 2026-11-20 19:16\n\nhello\nthere\n\n')
  assert.equal(core.piece('assistant', '', at, 'hi'), '## Assistant · 2026-11-20 19:16\n\nhi\n\n')
  assert.equal(core.piece('assistant', '', at, '  \n'), '', 'nothing said, nothing written')
  assert.equal(core.piece('toolCall', 'bash', at, '{"command":"ls\\n -la"}'), '> **bash** {"command":"ls\\n -la"}\n\n')
  assert.equal(core.piece('toolResult', 'bash', at, 'a\nb\n'), '    a\n    b\n\n')
  assert.equal(core.piece('toolResult', 'bash', at, Array.from({ length: 14 }, (_, i) => `line ${i + 1}`).join('\n')),
    `${Array.from({ length: 10 }, (_, i) => `    line ${i + 1}`).join('\n')}\n    ... 4 more lines, in the .jsonl\n\n`)
  assert.equal(core.piece('bashExecution', 'ls', at, 'a'), '> **$** ls\n\n    a\n\n')
  assert.equal(core.piece('image', '', at, ''), '*(an image)*\n\n')
  assert.equal(core.piece('compaction', '', at, 'so far'), '## Summary of what came before · 2026-11-20 19:16\n\nso far\n\n')
  for (const kind of ['thinking', 'system', 'custom', 'model_change', 'session', '']) assert.equal(core.piece(kind, 'n', at, 'text'), '', kind)

  // However long a conversation runs, writing it down costs no stack.
  const long = 'some words\n'.repeat(300_000)
  assert.equal(core.piece('assistant', '', at, long).length, '## Assistant · 2026-11-20 19:16\n\n'.length + long.length + 1)
  assert.match(core.piece('toolResult', 'bash', at, long), /\.\.\. 299990 more lines, in the \.jsonl\n\n$/)
  assert.equal(core.piece('toolCall', 'write', at, JSON.stringify({ content: long })).length, '> **write** \n\n'.length + 200)

  const lines = core.exportLines([{ name: 'wizardry', from: '/w/sessions', count: 3 }, { name: 'pi', from: '/p/sessions', count: 1 }, { name: 'x', from: '/x', count: 0 }], ['58 memories, in memory/'])
  assert.deepEqual(lines, ['3 conversations from /w/sessions, in conversations/wizardry/', '1 conversation from /p/sessions, in conversations/pi/', '58 memories, in memory/'])
  assert.deepEqual(core.exportLines([], []), ['nothing: no conversation and no memory was found'])
  assert.match(core.exportReadme('2026-11-21', lines), /^# wizardry export of 2026-11-21\n\nEverything here is a copy[\s\S]*\n- 3 conversations from \/w\/sessions, in conversations\/wizardry\/\n[\s\S]*wizardry --session <that file>/)
  assert.equal(core.exportSaid('/out', lines), `exported to /out:\n${lines.map((line) => `  ${line}`).join('\n')}\n`)
})
