import assert from 'node:assert/strict'
import { execFileSync, spawnSync } from 'node:child_process'
import { existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, statSync, symlinkSync, utimesSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { boot as bootWizardry, keepApart, restartArgs } from '../dist/index.js'

const DEFAULTS_DIR = fileURLToPath(new URL('../defaults', import.meta.url))
/** Boot without the shipped defaults unless a test asks for them, so each test sees only its own plugins. */
const boot = (options) => bootWizardry({ shipped: join(tmpdir(), 'wizardry-no-shipped-defaults'), ...options })

const DEFAULTS = ['fs', 'shell', 'cordis', 'self'] // everything but Pi itself, which needs a model

function scratch() {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-'))
  const home = join(dir, 'home')
  const cwd = join(dir, 'work')
  mkdirSync(home)
  mkdirSync(cwd)
  return { home, cwd }
}

const pluginSource = (reply) => `
export const name = 'echo'
export const actions = [{
  name: 'echo',
  description: 'Echo text back.',
  parameters: { type: 'object', properties: { text: { type: 'string' } } },
  execute: ({ text }) => '${reply}' + text,
}]
`

test('builtin plugins register their actions, owned by the plugin', async () => {
  const { home, cwd } = scratch()
  const { root, plugins, failures } = await boot({ home, cwd, defaults: DEFAULTS })
  assert.deepEqual(failures, [])
  const byName = Object.fromEntries(plugins.list().map((plugin) => [plugin.name, plugin]))
  assert.deepEqual(byName.fs.actions, ['read', 'write', 'edit', 'grep', 'find', 'ls'])
  assert.deepEqual(byName.shell.actions, ['bash'])
  assert.deepEqual(byName.cordis.actions, ['cordis_inspect', 'cordis_map', 'plugin_load', 'plugin_unload', 'plugin_reload'])
  assert.equal(root.get('actions').get('bash').owner, 'shell')
  // `self` injects `pi`, which is not loaded here: it waits instead of failing or hanging.
  assert.equal(byName.self.state, 'pending')
  assert.deepEqual(byName.self.actions, [])
  await root.fiber.dispose()
})

test('the agent-facing actions load, reload and unload a plugin file', async () => {
  const { home, cwd } = scratch()
  const { root } = await boot({ home, cwd, defaults: ['cordis'] })
  const actions = root.get('actions')
  const file = join(cwd, 'echo.ts')
  writeFileSync(file, pluginSource('one:'))

  const seen = []
  root.on('action/registered', (action) => seen.push(`+${action.name}`))
  root.on('action/unregistered', (action) => seen.push(`-${action.name}`))

  assert.match(await actions.invoke('plugin_load', { source: 'echo.ts' }, { cwd }), /Loaded "echo" \[active\]\. Actions: echo/)
  assert.equal(await actions.invoke('echo', { text: 'hi' }), 'one:hi')

  writeFileSync(file, pluginSource('two:'))
  await actions.invoke('plugin_reload', { name: 'echo' })
  assert.equal(await actions.invoke('echo', { text: 'hi' }), 'two:hi')

  await actions.invoke('plugin_unload', { name: 'echo' })
  assert.equal(actions.get('echo'), undefined)
  await assert.rejects(actions.invoke('echo', { text: 'hi' }), /no action named "echo"/)
  assert.deepEqual(seen, ['+echo', '-echo', '+echo', '-echo'])

  assert.match(await actions.invoke('cordis_inspect', {}), /Builtin plugins not loaded: pi, fs, shell, self, rtk, update, gate/)
  // The framework map the agent can retrieve in-session is the repo's AGENTS.md.
  assert.match(await actions.invoke('cordis_map', {}), /# AGENTS\.md/)
  assert.match(await actions.invoke('cordis_map', {}), /Cordis rules that bite/)
  await assert.rejects(actions.invoke('plugin_unload', { name: 'cordis' }), /cannot be unloaded/)
  await root.fiber.dispose()
})

test('plugins in the home and project directories load at boot; persisted choices survive', async () => {
  const { home, cwd } = scratch()
  mkdirSync(join(home, 'plugins'))
  writeFileSync(join(home, 'plugins', 'echo.ts'), pluginSource('home:'))
  mkdirSync(join(cwd, '.wizardry', 'plugins'), { recursive: true })
  writeFileSync(join(cwd, '.wizardry', 'plugins', 'shout.mjs'), `
    export default function shout(ctx) {
      ctx.actions.register({ name: 'shout', description: 'Upper-case.', execute: ({ text }) => text.toUpperCase() })
    }`)
  const elsewhere = join(cwd, 'extra.mjs')
  writeFileSync(elsewhere, `export const actions = [{ name: 'extra', description: 'x', execute: () => 'extra' }]`)

  const first = await boot({ home, cwd, defaults: ['cordis', 'shell'] })
  const actions = first.root.get('actions')
  assert.deepEqual(first.failures, [])
  assert.equal(await actions.invoke('echo', { text: 'a' }), 'home:a')
  assert.equal(await actions.invoke('shout', { text: 'a' }), 'A')
  await actions.invoke('plugin_load', { source: elsewhere, persist: true })
  await actions.invoke('plugin_unload', { name: 'shell', persist: true })
  await first.root.fiber.dispose()

  const saved = JSON.parse(readFileSync(join(home, 'plugins.json'), 'utf8'))
  assert.deepEqual(saved, { load: [{ source: elsewhere }], disabled: ['shell'] })

  const second = await boot({ home, cwd, defaults: ['cordis', 'shell'] })
  assert.deepEqual(second.plugins.list().map((plugin) => plugin.name), ['cordis', 'echo', 'shout', 'extra'])
  await second.root.fiber.dispose()
})

test('a listener on action/before can refuse a call; gate refuses when there is no one to ask', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['fs'] })
  const actions = root.get('actions')
  writeFileSync(join(cwd, 'note.txt'), 'hello')

  const outcomes = []
  root.on('action/after', (action, _params, outcome) => outcomes.push([action.name, outcome.error ? 'error' : 'ok']))
  assert.match((await actions.invoke('read', { path: join(cwd, 'note.txt') })).text, /hello/)

  await plugins.load('gate', { actions: ['read'] })
  await assert.rejects(actions.invoke('read', { path: join(cwd, 'note.txt') }), /needs the user's approval/)
  await plugins.unload('gate')
  assert.match((await actions.invoke('read', { path: join(cwd, 'note.txt') })).text, /hello/)
  assert.deepEqual(outcomes, [['read', 'ok'], ['read', 'ok']])
  await root.fiber.dispose()
})

test('bad plugins fail with a reason and leave nothing behind', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['fs'] })
  writeFileSync(join(cwd, 'empty.mjs'), 'export const nothing = 1')
  writeFileSync(join(cwd, 'clash.mjs'), `export const actions = [{ name: 'read', description: 'x', execute: () => '' }]`)
  writeFileSync(join(cwd, 'throws.mjs'), `export function apply() { throw new Error('boom') }`)
  await assert.rejects(plugins.load('empty.mjs', undefined, { cwd }), /a plugin exports/)
  await assert.rejects(plugins.load('clash.mjs', undefined, { cwd }), /already registered by plugin "fs"/)
  await assert.rejects(plugins.load('throws.mjs', undefined, { cwd }), /boom/)
  await assert.rejects(plugins.load('missing.mjs', undefined, { cwd }), /no plugin at/)
  assert.deepEqual(plugins.list().map((plugin) => plugin.name), ['fs'])
  assert.equal(root.get('actions').get('read').owner, 'fs')
  await root.fiber.dispose()
})

test('rtk wraps bash: rewrites through `rtk rewrite`, declares itself, and steps aside for raw calls', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: ['shell'] })
  const actions = root.get('actions')
  const bash = () => actions.get('bash')

  // A stand-in rtk: rewrites `echo original` (exit 3, as rtk does for most commands), nothing else (exit 1).
  const fake = join(cwd, 'rtk')
  writeFileSync(fake, '#!/bin/sh\nif [ "$1" = rewrite ] && [ "$2" = "echo original" ]; then printf "echo condensed"; exit 3; fi\nexit 1\n', { mode: 0o755 })

  assert.match((await actions.invoke('bash', { command: 'echo original' })).text, /original/)
  assert.equal(actions.describe(bash()).parameters.properties.raw, undefined)

  const changes = []
  root.on('action/changed', (action) => changes.push(action.name))
  await plugins.load('rtk', { binary: fake })
  const shown = actions.describe(bash())
  assert.match(shown.description, /raw: true/)
  assert.equal(shown.parameters.properties.raw.type, 'boolean')
  assert.ok(shown.parameters.properties.command, 'the original parameters are kept')

  assert.match((await actions.invoke('bash', { command: 'echo original' })).text, /condensed/)
  assert.match((await actions.invoke('bash', { command: 'echo original', raw: true })).text, /original/)
  assert.match((await actions.invoke('bash', { command: 'echo other' })).text, /other/)

  await plugins.unload('rtk')
  assert.match((await actions.invoke('bash', { command: 'echo original' })).text, /original/)
  assert.equal(actions.describe(bash()).parameters.properties.raw, undefined)
  assert.deepEqual(changes, ['bash', 'bash'])

  await assert.rejects(plugins.load('rtk', { binary: join(cwd, 'absent') }), /no rtk executable at/)
  assert.ok(!plugins.list().some((plugin) => plugin.name === 'rtk'))
  await root.fiber.dispose()
})

test('the header draws the wizard cap and fits any width', async () => {
  const { HAT, Header } = await import('../dist/look.js')
  const { visibleWidth } = await import('@earendil-works/pi-tui')
  const { initTheme } = await import('@earendil-works/pi-coding-agent')
  initTheme('dark', false) // Pi's key hints color themselves with its current theme
  const plain = { fg: (_color, text) => text, bold: (text) => text }
  const header = new Header(plain)
  for (const width of [200, 100, 60, 44, 20, 8]) {
    for (const expanded of [false, true]) {
      header.setExpanded(expanded)
      const rows = header.render(width)
      for (const row of rows) assert.ok(visibleWidth(row) <= width, `${visibleWidth(row)} columns in a width of ${width}`)
      if (width >= 21) for (const line of HAT) assert.ok(rows.some((row) => row.includes(line.trimEnd())), 'the whole cap is drawn')
    }
  }
  header.setExpanded(false)
  const rows = header.render(100)
  assert.equal(rows.length, HAT.length, 'collapsed, the text sits beside the cap')
  assert.match(rows.join('\n'), /wizardry v\d/)
  header.setExpanded(true)
  assert.ok(header.render(100).length > HAT.length)

  const loaded = [
    { name: 'fs', source: 'builtin:fs', state: 'active' },
    { name: 'claude-mem', source: '/home/plugins/claude-mem.js', state: 'active' },
    { name: 'self', source: 'builtin:self', state: 'pending' },
  ]
  const listing = new Header(plain, () => loaded)
  assert.deepEqual(listing.render(100).slice(HAT.length), ['', '[Plugins]', '  fs, claude-mem, self (pending)'])
  loaded.pop()
  assert.equal(listing.render(100).at(-1), '  fs, claude-mem', 'the list follows what is loaded')
  listing.setExpanded(true)
  assert.ok(listing.render(100).includes('  fs          builtin:fs'))
  for (const width of [20, 8]) for (const row of listing.render(width)) assert.ok(visibleWidth(row) <= width)
})

test('the cap twinkles in blues and greys, and only while it is on screen', async () => {
  const { HAT, HAT_FRAMES, HAT_INTERVAL_MS, hatFrame, hatLines, Header, SMALL_HAT, workingIndicator } = await import('../dist/look.js')
  const { visibleWidth } = await import('@earendil-works/pi-tui')
  assert.deepEqual(hatFrame(0), HAT, 'still, it is the plain logo')
  assert.deepEqual(hatFrame(HAT_FRAMES), HAT, 'and it comes back round to it')
  const frames = Array.from({ length: HAT_FRAMES }, (_, i) => hatFrame(i))
  assert.equal(new Set(frames.map((rows) => rows.join('\n'))).size, HAT_FRAMES, 'every frame differs')
  for (const rows of frames) assert.deepEqual(rows.map((row) => row.length), HAT.map((row) => row.length))

  const used = new Set()
  const theme = { fg: (color, text) => (used.add(color), text), bold: (text) => text }
  for (let i = 0; i < HAT_FRAMES; i++) hatLines(theme, i)
  const working = workingIndicator(theme)
  assert.deepEqual([...used].sort(), ['accent', 'dim', 'mdLink', 'text'], 'no gold, green or red')
  // Bend proves the caps are drawn in these four theme colors and no other (LAWS.bend,
  // caps_are_blue_and_grey). What no proof reaches is the theme files: in both, each of the four
  // is a blue, or so unsaturated that it is a grey.
  const { THEME_DIR, THEME_PAIR } = await import('../dist/look.js')
  for (const name of THEME_PAIR.split('/')) {
    const file = JSON.parse(readFileSync(join(THEME_DIR, `${name}.json`), 'utf8'))
    for (const color of used) {
      const value = file.vars[file.colors[color]] ?? file.colors[color]
      const [, hue, saturation] = /^okhsl\((\d+) (\d+)% \d+%\)$/.exec(value).map(Number)
      assert.ok(saturation <= 15 || (hue >= 235 && hue <= 265), `${name}: ${color} is ${value}, neither a blue nor a grey`)
    }
  }
  assert.deepEqual(working.frames, SMALL_HAT)
  assert.equal(new Set(SMALL_HAT.map((row) => visibleWidth(row))).size, 1, 'the message beside the small cap does not jump')
  assert.ok(SMALL_HAT.every((row) => row.startsWith('_/\\_')) && new Set(SMALL_HAT).size === SMALL_HAT.length)

  const { mock } = await import('node:test')
  mock.timers.enable({ apis: ['setInterval'] })
  try {
    const tui = { previousViewportTop: 0, renders: 0, requestRender() { this.renders++ } }
    const header = new Header(theme, undefined, tui)
    const cap = () => header.render(100).slice(0, HAT.length).map((row) => row.slice(1, 1 + HAT[0].length))
    assert.deepEqual(cap(), HAT)
    mock.timers.tick(HAT_INTERVAL_MS)
    assert.deepEqual(cap(), hatFrame(1))
    assert.equal(tui.renders, 1)
    tui.previousViewportTop = 5 // the cap has scrolled away: redrawing it would repaint the whole scrollback
    mock.timers.tick(HAT_INTERVAL_MS * 3)
    assert.deepEqual([cap(), tui.renders], [hatFrame(1), 1])
    delete tui.previousViewportTop // a pi-tui that no longer says where the viewport is
    mock.timers.tick(HAT_INTERVAL_MS)
    assert.equal(tui.renders, 1)
    tui.previousViewportTop = 0
    mock.timers.tick(HAT_INTERVAL_MS)
    assert.equal(tui.renders, 2)
    header.dispose()
    mock.timers.tick(HAT_INTERVAL_MS * 3)
    assert.equal(tui.renders, 2, 'disposed, it stops')
  } finally {
    mock.timers.reset()
  }
})

test('the blue themes ship as a light/dark pair and Pi is pointed at them', async () => {
  const { THEME_DIR, THEME_PAIR, themeArgs } = await import('../dist/look.js')
  const [light, dark] = THEME_PAIR.split('/').map((name) => JSON.parse(readFileSync(join(THEME_DIR, `${name}.json`), 'utf8')))
  assert.deepEqual([light.name, light.appearance, dark.name, dark.appearance], ['wizardry-light', 'light', 'wizardry', 'dark'])
  for (const theme of [light, dark]) {
    assert.deepEqual(Object.keys(theme.colors), Object.keys(dark.colors))
    for (const value of [...Object.values(theme.colors), ...Object.values(theme.vars)]) {
      assert.ok(/^okhsl\(/.test(value) || value in theme.vars, `${theme.name}: "${value}" is neither a color nor a variable`)
    }
  }
  assert.deepEqual(themeArgs(['-p', 'hi']), ['--theme', THEME_DIR, '--use-theme', THEME_PAIR])
  assert.deepEqual(themeArgs(['--use-theme', 'dark']), ['--theme', THEME_DIR])
})

test('a call is named after its plugin, then the action, with its arguments beside it', async () => {
  const { actionTitle, callText, resultText } = await import('../dist/look.js')
  const { initTheme } = await import('@earendil-works/pi-coding-agent')
  initTheme('dark', false)
  const tagged = { fg: (color, text) => (color === 'accent' ? `<${text}>` : text), bold: (text) => text }

  assert.equal(actionTitle({ owner: 'cordis', name: 'plugin_load' }), 'cordis plugin load')
  assert.equal(actionTitle({ owner: 'cordis', name: 'cordis_inspect' }), 'cordis inspect')
  assert.equal(actionTitle({ owner: 'subagent', name: 'subagent_create' }), 'subagent create')
  assert.equal(actionTitle({ owner: 'dice', name: 'dice' }), 'dice')
  assert.equal(actionTitle({ owner: 'subagent', name: 'review_changes', title: 'code review' }), 'code review')
  assert.equal(actionTitle({ owner: 'fs', name: 'read', native: {} }), 'read', "Pi's own tools keep their names")

  const create = { owner: 'subagent', name: 'subagent_create' }
  const args = { role: 'reviewer', task: `line one\n${'x'.repeat(200)}`, tools: ['read', 'grep'], limit: null }
  const collapsed = callText(create, args, tagged, false)
  assert.ok(collapsed.startsWith('<subagent> create  role: reviewer · task: line one xxx'), collapsed)
  assert.ok(collapsed.endsWith('… · tools: read, grep'), 'long values are cut, and arguments left out are not shown')
  assert.ok(!collapsed.includes('\n'))
  const expanded = callText(create, args, tagged, true)
  assert.deepEqual(expanded.split('\n').slice(0, 3), ['<subagent> create', '  role: reviewer', '  task: line one'])
  assert.ok(expanded.includes('x'.repeat(200)) && expanded.endsWith('  tools: read, grep'))
  assert.equal(callText({ owner: 'cordis', name: 'cordis_inspect' }, {}, tagged, false), '<cordis> inspect')
  assert.equal(callText({ owner: 'subagent', name: 'review_changes', title: 'code review' }, { range: 'a..b' }, tagged, false), 'code review  range: a..b')

  const output = Array.from({ length: 14 }, (_, i) => `row ${i + 1}`).join('\n')
  const preview = resultText(output, tagged, false).split('\n')
  assert.deepEqual(preview.slice(0, 2), ['', 'row 1'])
  assert.match(preview.at(-1), /4 more lines/)
  assert.ok(resultText(output, tagged, true).endsWith('row 14'))
  assert.equal(resultText('', tagged, false), '')
})

test('update follows the installed checkout, rolls back a build that fails, and can be switched off', async () => {
  const { managed, updateNow, SCRIPT } = await import('../dist/plugins/update.js')
  const { home, cwd } = scratch()
  const git = (dir, ...args) => execFileSync('git', ['-c', 'user.name=t', '-c', 'user.email=t@t', ...args], { cwd: dir, encoding: 'utf8' }).trim()
  const origin = join(cwd, 'origin')
  const app = join(home, 'app')
  const release = (build, message) => {
    writeFileSync(join(origin, 'package.json'), JSON.stringify({ name: 'fake', private: true, scripts: { build } }))
    git(origin, 'add', '-A')
    git(origin, 'commit', '-q', '-m', message)
    return git(origin, 'rev-parse', 'HEAD')
  }
  const built = () => (existsSync(join(app, 'built.txt')) ? readFileSync(join(app, 'built.txt'), 'utf8') : undefined)
  const background = () => execFileSync('sh', ['-c', SCRIPT, 'sh', app, home, 'background', 'install'], { encoding: 'utf8', stdio: 'pipe' })
  const notice = () => readFileSync(join(home, 'update-notice'), 'utf8').trim()

  Object.assign(process.env, { GIT_AUTHOR_NAME: 't', GIT_AUTHOR_EMAIL: 't@t', GIT_COMMITTER_NAME: 't', GIT_COMMITTER_EMAIL: 't@t' })
  mkdirSync(origin)
  git(origin, 'init', '-q', '-b', 'main')
  writeFileSync(join(origin, 'notes.txt'), 'notes\n')
  writeFileSync(join(origin, '.gitignore'), 'built.txt\nnode_modules\npackage-lock.json\n')
  const one = release(`node -e "require('fs').writeFileSync('built.txt','one')"`, 'one')
  git(cwd, 'clone', '-q', `file://${origin}`, app)
  git(app, 'checkout', '-q', '--detach')

  assert.ok(managed(app, home))
  assert.ok(!managed(origin, home), 'a checkout that is not <home>/app is left alone')
  assert.equal(updateNow(app, home), 0)
  assert.equal(built(), undefined, 'already current: nothing is rebuilt')

  const two = release(`node -e "require('fs').writeFileSync('built.txt','two')"`, 'second release')
  assert.match(background(), /updated to \w+ \(second release\)/)
  assert.equal(git(app, 'rev-parse', 'HEAD'), two)
  assert.equal(built(), 'two')
  assert.match(notice(), /^updated to \w+ \(second release\)$/)

  const three = release('exit 1', 'broken')
  assert.throws(background, (error) => /failed to build; still on/.test(error.stdout))
  assert.equal(git(app, 'rev-parse', 'HEAD'), two, 'rolled back')
  assert.match(notice(), /failed to build/)
  assert.equal(readFileSync(join(home, 'update-failed'), 'utf8').trim(), three)
  assert.equal(background(), '', 'the broken commit is not retried in the background')

  // A clone someone works in is updated with their work carried along, or not touched at all.
  const clone = join(cwd, 'clone')
  const inClone = (mode) => execFileSync('sh', ['-c', SCRIPT, 'sh', clone, home, mode, 'clone'], { encoding: 'utf8', stdio: 'pipe' })
  const head = (...rev) => git(clone, 'rev-parse', ...(rev.length ? rev : ['HEAD']))
  const still = (file) => utimesSync(join(clone, file), new Date(Date.now() - 600_000), new Date(Date.now() - 600_000))
  git(cwd, 'clone', '-q', `file://${origin}`, clone)
  git(clone, 'reset', '-q', '--hard', two)
  const four = release(`node -e "require('fs').writeFileSync('built.txt','four')"`, 'fourth release')

  writeFileSync(join(clone, 'notes.txt'), 'work in progress\n')
  assert.equal(inClone('background'), '', 'being edited right now: left alone, silently')
  assert.match(inClone('foreground'), /edited in the last two minutes/)
  assert.equal(head(), two)
  still('notes.txt')
  assert.match(inClone('background'), /updated to \w+ \(fourth release\)/)
  assert.equal(head(), four)
  assert.equal(git(clone, 'symbolic-ref', '--short', 'HEAD'), 'main', 'still on its branch')
  assert.equal(readFileSync(join(clone, 'notes.txt'), 'utf8'), 'work in progress\n', 'uncommitted work is back on top')
  assert.equal(readFileSync(join(clone, 'built.txt'), 'utf8'), 'four')
  assert.equal(readFileSync(join(clone, '.git', 'wizardry-built'), 'utf8').trim(), four)

  git(clone, 'commit', '-qam', 'local work')
  assert.match(inClone('foreground'), /up to date/, 'ahead of the repo is up to date')
  const five = release(`node -e "require('fs').writeFileSync('built.txt','five')"`, 'fifth release')
  assert.match(inClone('background'), /updated to \w+ \(fifth release\)/)
  assert.equal(head('HEAD~1'), five, 'the unpushed commit now sits on the new version')
  assert.equal(git(clone, 'log', '-1', '--format=%s'), 'local work')

  const before = head()
  writeFileSync(join(clone, 'package.json'), '{"name":"mine"}')
  still('package.json')
  release(`node -e "require('fs').writeFileSync('built.txt','six')"`, 'sixth release')
  assert.match(inClone('foreground'), /your uncommitted changes in .* do not apply on top of it/)
  assert.equal(head(), before, 'exactly as it was')
  assert.equal(readFileSync(join(clone, 'package.json'), 'utf8'), '{"name":"mine"}')
  assert.equal(git(clone, 'stash', 'list'), '')
  assert.equal(readFileSync(join(clone, 'built.txt'), 'utf8'), 'five')
  git(clone, 'checkout', '-q', '--', 'package.json')
  assert.match(inClone('foreground'), /updated to \w+ \(sixth release\)/)

  // The plugin shows the pending notice once, and is a default that can be persisted off.
  process.env.WIZARDRY_NO_UPDATE = '1'
  const first = await boot({ home, cwd, defaults: [] })
  await first.plugins.load('update', { app })
  assert.ok(!existsSync(join(home, 'update-notice')))
  await first.plugins.unload('update', { persist: true })
  await first.root.fiber.dispose()
  const second = await boot({ home, cwd, defaults: ['update'] })
  assert.deepEqual(second.plugins.list().map((plugin) => plugin.name), [])
  await second.root.fiber.dispose()
  delete process.env.WIZARDRY_NO_UPDATE

  // Starting, and finishing a task, each start a check.
  const log = join(home, 'update.log')
  const checked = async (again) => {
    for (let i = 0; i < 40; i++) {
      if (existsSync(log) && readFileSync(log, 'utf8').includes('up to date')) return true
      again?.()
      await new Promise((done) => setTimeout(done, 250))
    }
    return false
  }
  const third = await boot({ home, cwd, defaults: [] })
  await third.plugins.load('update', { app: clone })
  assert.ok(await checked(), 'checked on start')
  writeFileSync(log, '')
  assert.ok(await checked(() => third.root.emit('task/end')), 'checked when a task ended')
  await third.root.fiber.dispose()
  assert.ok(one !== two)
})

test('pi announces ready and session-start through cordis events', async () => {
  const { home, cwd } = scratch()
  const { root, plugins } = await boot({ home, cwd, defaults: [] })
  await plugins.load('pi')
  const pi = root.get('pi')
  const seen = []
  root.on('pi/ready', (api) => seen.push(['ready', typeof api.registerTool]))
  root.on('pi/session-start', (api, piCtx) => seen.push(['session-start', piCtx.cwd, api === fakeApi]))
  root.on('task/end', () => seen.push(['task/end']))
  const handlers = {}
  const fakeApi = {
    registerTool() {}, registerCommand() {},
    on: (event, handler) => { handlers[event] = handler },
  }
  pi.attach(fakeApi)
  assert.deepEqual(seen, [['ready', 'function']])
  handlers.session_start({}, { cwd, mode: 'json', sessionManager: { getBranch: () => [] } })
  handlers.agent_end()
  assert.deepEqual(seen, [['ready', 'function'], ['session-start', cwd, true], ['task/end']])

  // A -p run ends before the check that follows the agent's last word: Pi's context for a
  // session that is over throws when read, and nothing reads it.
  let over = false
  handlers.session_start({}, { cwd, get mode() { if (over) throw new Error('this ctx is stale'); return 'print' }, sessionManager: { getBranch: () => [] } })
  over = true
  handlers.agent_end()
  await new Promise((resolve) => setTimeout(resolve, 260))

  // In the terminal UI, wizardry's cap replaces both Pi's logo and its spinner.
  const ui = { theme: { fg: (_color, text) => text, bold: (text) => text }, setHeader(factory) { this.header = factory }, setWorkingIndicator(options) { this.working = options } }
  handlers.session_start({}, { cwd, mode: 'tui', ui, sessionManager: { getBranch: () => [] } })
  assert.equal(typeof ui.header, 'function')
  assert.ok(ui.working.frames.length > 1 && ui.working.frames.every((frame) => frame.includes('/\\')))
  await root.fiber.dispose()
})

test('a session that restarts onto new code keeps its options, session and plugins', async () => {
  const { home, cwd } = scratch()
  const session = join(cwd, 'session.jsonl')
  writeFileSync(session, '')
  assert.deepEqual(
    restartArgs(['--model', 'big', '-c', '--thinking', 'high', 'fix the bug', '@notes.md'], session),
    ['--model', 'big', '--thinking', 'high', '--session', session])
  assert.deepEqual(restartArgs(['--session', 'old.jsonl', '--', 'hello'], join(cwd, 'gone.jsonl')), [], 'a session never written is not asked for')

  const file = join(cwd, 'echo.ts')
  writeFileSync(file, pluginSource('one:'))
  const first = await boot({ home, cwd, defaults: ['cordis', 'shell', 'fs'] })
  await first.plugins.load(file)
  await first.plugins.unload('shell')
  const snapshot = JSON.parse(JSON.stringify(first.plugins.snapshot()))
  await first.root.fiber.dispose()

  const second = await boot({ home, cwd, defaults: ['cordis', 'shell', 'fs'] })
  assert.deepEqual(await second.plugins.restore(snapshot, cwd), [])
  assert.deepEqual(second.plugins.list().map((plugin) => plugin.name).sort(), ['cordis', 'echo', 'fs'])
  await second.root.fiber.dispose()
})

test('shipped defaults load at boot, step aside for a home plugin of the same name, and can be switched off', async () => {
  const { home, cwd } = scratch()
  const shipped = join(cwd, 'shipped')
  mkdirSync(shipped)
  writeFileSync(join(shipped, 'echo.mjs'), `export const actions = [{ name: 'echo', description: 'e', execute: () => 'shipped' }]`)
  writeFileSync(join(shipped, 'other.mjs'), `export const actions = [{ name: 'other', description: 'o', execute: () => 'other' }]`)

  const first = await boot({ home, cwd, shipped, defaults: ['cordis'] })
  assert.deepEqual(first.failures, [])
  assert.equal(await first.root.get('actions').invoke('echo', {}), 'shipped')
  await first.root.get('actions').invoke('plugin_unload', { name: 'other', persist: true })
  await first.root.fiber.dispose()

  mkdirSync(join(home, 'plugins'))
  writeFileSync(join(home, 'plugins', 'echo.mjs'), `export const actions = [{ name: 'echo', description: 'e', execute: () => 'mine' }]`)
  const second = await boot({ home, cwd, shipped, defaults: ['cordis'] })
  assert.deepEqual(second.failures, [])
  assert.deepEqual(second.plugins.list().map((plugin) => plugin.name), ['cordis', 'echo'])
  assert.equal(await second.root.get('actions').invoke('echo', {}), 'mine')
  await second.root.fiber.dispose()
})

test('a plugin switched off stays off, comes back when switched on, and no other is touched', async () => {
  // What LAWS.bend proves of the decision (off_stays_off, on_comes_back, off_touches_one,
  // on_touches_one, off_files_stay_off), seen end to end through boot and plugins.json.
  const { home, cwd } = scratch()
  const shipped = join(cwd, 'shipped')
  mkdirSync(shipped)
  writeFileSync(join(shipped, 'memo.mjs'), `export const actions = [{ name: 'memo', description: 'm', execute: () => 'memo' }]`)
  const names = async (act) => {
    const { root, plugins } = await boot({ home, cwd, shipped, defaults: ['cordis', 'shell', 'fs'] })
    await act?.(root.get('actions'))
    const loaded = plugins.list().map((plugin) => plugin.name)
    await root.fiber.dispose()
    return loaded
  }
  assert.deepEqual(await names(), ['cordis', 'shell', 'fs', 'memo'])
  await names(async (actions) => {
    await actions.invoke('plugin_unload', { name: 'shell', persist: true })
    await actions.invoke('plugin_unload', { name: 'memo', persist: true })
  })
  assert.deepEqual(await names(), ['cordis', 'fs'], 'both stay off, and fs was not touched')
  assert.deepEqual(await names(), ['cordis', 'fs'], 'however many times it starts')
  await names((actions) => actions.invoke('plugin_load', { source: 'shell', persist: true }))
  assert.deepEqual(await names(), ['cordis', 'shell', 'fs'], 'shell is back, and memo is still off')
  await names((actions) => actions.invoke('plugin_load', { source: join(shipped, 'memo.mjs'), persist: true }))
  assert.deepEqual((await names()).sort(), ['cordis', 'fs', 'memo', 'shell'])
  await assert.rejects(names((actions) => actions.invoke('plugin_unload', { name: 'cordis', persist: true })), /cannot be unloaded/)
  assert.ok((await names()).includes('cordis'), 'what the session runs on cannot be switched off from inside it')
})

test('the bend default puts its rules in the action description and returns the guide', async () => {
  const { home, cwd } = scratch()
  const rules = [
    'When using Bend:',
    '- run `bend guide` to learn it',
    '- use `LAWS.bend` to keep important rules',
    '- run `bend PROOF.bend` before committing',
    '- parallelize the code whenever possible',
  ].join('\n')
  const fake = join(cwd, 'bend')
  writeFileSync(fake, '#!/bin/sh\n[ "$1" = guide ] && echo "# Bend guide text"\n', { mode: 0o755 })

  const { root, plugins, failures } = await boot({ home, cwd, shipped: DEFAULTS_DIR, defaults: ['cordis'] })
  assert.deepEqual(failures, [])
  const actions = root.get('actions')
  assert.ok(actions.get('bend').description.includes(rules))
  // Bend is what the agent writes in unless there is a reason not to, said where every session sees it.
  assert.match(actions.get('bend').description, /Bend is your default language\. When you write code, write in Bend everything Bend can express/)
  assert.match(actions.get('bend').description, /Use another language only for those calls, for a codebase that is already in one .*or when the user asks for one/)

  await actions.invoke('plugin_unload', { name: 'bend' })
  await plugins.load(join(DEFAULTS_DIR, 'bend.js'), { bin: fake })
  const withBend = await actions.invoke('bend', {})
  assert.ok(withBend.startsWith(rules))
  assert.match(withBend, /Bend is your default language/)
  assert.match(withBend, /# Bend guide text/)

  await actions.invoke('plugin_unload', { name: 'bend' })
  await plugins.load(join(DEFAULTS_DIR, 'bend.js'), { bin: join(cwd, 'missing') })
  const without = await actions.invoke('bend', {})
  assert.ok(without.startsWith(rules))
  assert.match(without, /curl -fsSL https:\/\/bend-lang\.com\/install\.sh \| sh/)
  await root.fiber.dispose()
})

test('an install under the old name izardry is carried over once, and the old paths keep working', () => {
  const dir = mkdtempSync(join(tmpdir(), 'wizardry-rename-'))
  const fakeHome = join(dir, 'user')
  mkdirSync(join(fakeHome, '.izardry', 'plugins'), { recursive: true })
  writeFileSync(join(fakeHome, '.izardry', 'plugins', 'echo.mjs'), `export const actions = [{ name: 'echo', description: 'e', execute: () => 'echo' }]`)
  mkdirSync(join(fakeHome, 'bin'))
  execFileSync('ln', ['-s', fileURLToPath(new URL('../dist/bin.js', import.meta.url)), join(fakeHome, 'bin', 'izardry')])
  const env = { ...process.env, HOME: fakeHome, WIZARDRY_NO_UPDATE: '1' }
  delete env.WIZARDRY_HOME
  const run = (command) => spawnSync(process.execPath, [join(fakeHome, 'bin', command), 'plugins'], { env, cwd: dir, encoding: 'utf8' })

  const first = run('izardry')
  assert.match(first.stderr, /izardry is now wizardry: your plugins and sessions are now in ~\/\.wizardry, and the command is now `wizardry`\./)
  assert.match(first.stdout, /^echo \[active\]/m, 'the plugins came along')
  assert.ok(existsSync(join(fakeHome, '.wizardry', 'plugins', 'echo.mjs')))
  assert.ok(existsSync(join(fakeHome, '.izardry', 'plugins', 'echo.mjs')), 'the old path still leads there')

  const second = run('wizardry')
  assert.equal(second.stderr, '', 'it is said once')
  assert.match(second.stdout, /^echo \[active\]/m)
})

test('the memory default observes a session, keeps it under the home, recalls it, and leaves nothing behind', async () => {
  const { home, cwd } = scratch()
  process.env.CLAUDE_MEM_DATA_DIR = join(cwd, 'no-claude-mem')
  const { root, plugins, failures } = await boot({ home, cwd, shipped: DEFAULTS_DIR, defaults: ['cordis'] })
  assert.deepEqual(failures, [])
  const actions = root.get('actions')
  const loaded = plugins.list().find((plugin) => plugin.name === 'memory')
  assert.equal(loaded.source, join(DEFAULTS_DIR, 'memory', 'index.js'))
  assert.deepEqual(loaded.actions, ['mem_search', 'mem_timeline', 'mem_get_observations'])
  assert.match(await actions.invoke('mem_search', {}, { cwd }), /Memory holds nothing for project "work" yet\./)
  assert.ok(existsSync(join(home, 'memory', 'memory.db')), 'the store is a file under the home, with no worker behind it')

  // The same plugin with a stand-in for the model, driven by the events wizardry emits.
  await actions.invoke('plugin_unload', { name: 'memory' })
  const expose = {}
  const asked = []
  await plugins.load(join(DEFAULTS_DIR, 'memory'), {
    expose,
    complete: async (request) => {
      asked.push(request)
      return { text: '2026-11-19 10:02 | decision | Chose the blue theme over the green one', cost: 0 }
    },
  })
  const branch = []
  let n = 0
  const say = (role, text) => branch.push({ type: 'message', id: `e${++n}`, timestamp: '2026-11-19T10:02:00', message: { role, content: [{ type: 'text', text }] } })
  const handlers = {}
  const api = {
    appendEntry: (customType, data) => branch.push({ type: 'custom', id: `e${++n}`, customType, data }),
    on: (event, handler) => { handlers[event] = handler; return () => delete handlers[event] },
  }
  const piCtx = { cwd, mode: 'print', ui: { notify() {} }, sessionManager: { getSessionId: () => 's1', getBranch: () => branch } }
  root.emit('pi/session-start', api, piCtx)
  say('user', `Which theme? <private>my token is hunter2</private> ${'Think about it carefully. '.repeat(400)}`)
  say('assistant', 'Blue.')
  root.emit('task/end')
  await expose.settle()
  assert.equal(asked.length, 1, 'the agent stopping is what gets the leftover observed')
  assert.doesNotMatch(asked[0].user, /hunter2/)
  assert.equal(branch.filter((entry) => entry.customType === 'memory:observed').length, 1)
  assert.match(await actions.invoke('mem_search', { query: 'theme' }, { cwd }), /decision  \[work\]  Chose the blue theme over the green one/)

  const keep = branch.length
  say('user', 'And the font?')
  const compacted = await handlers.session_before_compact({ preparation: { firstKeptEntryId: `e${keep + 1}`, tokensBefore: 9, settings: {} } }, piCtx)
  assert.match(compacted.compaction.summary, /## Observations\n2026-11-19 10:02 \[decision\] Chose the blue theme over the green one/)
  assert.equal(compacted.compaction.firstKeptEntryId, `e${keep + 1}`)

  await actions.invoke('plugin_unload', { name: 'memory' })
  await actions.invoke('plugin_unload', { name: 'when' }) // the other default that listens to Pi
  assert.equal(actions.get('mem_search'), undefined)
  assert.deepEqual(Object.keys(handlers), [], 'its hooks into Pi go with it')
  delete process.env.CLAUDE_MEM_DATA_DIR
  await root.fiber.dispose()
})

test('the memory default ships the Bend it was compiled from', () => {
  // defaults/memory is built in https://github.com/Pomidium/wizardry-memory (memory.bend, LAWS.bend,
  // PROOF.bend) and copied here by its `npm run ship`. Nothing in it is edited in this repository.
  const core = readFileSync(join(DEFAULTS_DIR, 'memory', 'core.mjs'), 'utf8')
  for (const def of ['chunks', 'strip_private', 'promoted', 'nearest', 'block', 'observer_system']) assert.ok(core.includes(`"${def}":`), def)
})

// Kept apart, export and delete, on a machine of their own: a home directory with Pi's own setup
// in it (logins, settings that name packages and extensions, a conversation, the pi program) and
// a wizardry beside it.

const BIN = fileURLToPath(new URL('../dist/bin.js', import.meta.url))

function machine() {
  const user = realpathSync(mkdtempSync(join(tmpdir(), 'wizardry-machine-')))
  const pi = join(user, '.pi', 'agent')
  const home = join(user, '.wizardry')
  mkdirSync(join(pi, 'sessions', '--work--'), { recursive: true })
  mkdirSync(join(pi, 'bin'))
  mkdirSync(join(user, '.local', 'bin'), { recursive: true })
  mkdirSync(join(user, 'work'))
  writeFileSync(join(pi, 'auth.json'), '{"acme":{"type":"api_key","key":"sk-secret"}}', { mode: 0o600 })
  writeFileSync(join(pi, 'settings.json'), JSON.stringify({
    defaultProvider: 'acme', defaultModel: 'big', packages: ['npm:bloat'], extensions: ['~/ext.ts'], skills: ['~/skills'],
    themes: ['~/themes'], prompts: ['~/prompts'], sessionDir: '~/elsewhere', theme: 'dark', lastChangelogVersion: '1.6.0',
  }))
  writeFileSync(join(pi, 'bin', 'pi'), '#!/bin/sh\n')
  symlinkSync('../../.pi/agent/bin/pi', join(user, '.local', 'bin', 'pi'))
  symlinkSync('/bin/sh', join(user, '.local', 'bin', 'sh-too'))
  const entry = (n, extra) => JSON.stringify({ id: `e${n}`, timestamp: `2026-11-19T10:0${n}:00.000Z`, ...extra })
  const conversation = (cwd, said) => [
    JSON.stringify({ type: 'session', version: 3, id: 's', timestamp: '2026-11-19T10:00:00.000Z', cwd }),
    entry(1, { type: 'model_change', provider: 'acme', modelId: 'big' }),
    entry(2, { type: 'message', message: { role: 'user', content: [{ type: 'text', text: said }] } }),
    entry(3, { type: 'message', message: { role: 'assistant', content: [
      { type: 'thinking', thinking: 'a private thought' }, { type: 'text', text: 'Looking.' },
      { type: 'toolCall', id: 'c1', name: 'bash', arguments: { command: 'seq 14' } }] } }),
    entry(4, { type: 'message', message: { role: 'toolResult', toolName: 'bash', content: [{ type: 'text', text: Array.from({ length: 14 }, (_, i) => i + 1).join('\n') }] } }),
    entry(5, { type: 'custom', customType: 'memory:observed', data: { v: 1 } }),
    entry(6, { type: 'message', message: { role: 'assistant', content: [{ type: 'text', text: 'Fourteen lines.' }] } }),
  ].join('\n') + '\n'
  writeFileSync(join(pi, 'sessions', '--work--', 'old.jsonl'), conversation('/work', 'count for pi'))
  mkdirSync(join(home, 'sessions'), { recursive: true })
  writeFileSync(join(home, 'sessions', 'new.jsonl'), conversation('/work', 'count for wizardry'))
  const env = { ...process.env, HOME: user, WIZARDRY_NO_UPDATE: '1', CLAUDE_MEM_DATA_DIR: join(user, 'no-claude-mem') }
  for (const name of ['WIZARDRY_HOME', 'IZARDRY_HOME', 'WIZARDRY_BIN_DIR', 'PI_CODING_AGENT_DIR', 'PI_CODING_AGENT_SESSION_DIR', 'PI_PACKAGE_DIR']) delete env[name]
  const run = (args, more = {}) => spawnSync(process.execPath, [BIN, ...args], { env: { ...env, ...more }, cwd: join(user, 'work'), encoding: 'utf8' })
  return { user, pi, home, run }
}

/** Every file under a directory, as paths relative to it. */
const tree = (dir, under = '') => readdirSync(join(dir, under), { withFileTypes: true })
  .flatMap((entry) => (entry.isDirectory() ? tree(dir, join(under, entry.name)) : [join(under, entry.name)])).sort()

test('wizardry keeps its own logins and settings: Pi\'s come over once, without what Pi\'s setup adds to a session', () => {
  const { user, pi, home, run } = machine()
  const before = tree(pi).map((file) => [file, readFileSync(join(pi, file), 'utf8')])

  const first = run(['plugins'])
  assert.equal(first.status, 0, first.stderr)
  assert.match(first.stderr, new RegExp(`^wizardry: logins and settings are now its own, in ${home}/pi\\. Brought over auth\\.json, settings\\.json from ${pi}, which is no longer read`, 'm'))
  assert.equal(readFileSync(join(home, 'pi', 'auth.json'), 'utf8'), '{"acme":{"type":"api_key","key":"sk-secret"}}')
  assert.equal(statSync(join(home, 'pi', 'auth.json')).mode & 0o077, 0, 'logins are readable by their owner only')
  assert.equal(statSync(join(home, 'pi')).mode & 0o077, 0)
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'pi', 'settings.json'), 'utf8')), { defaultProvider: 'acme', defaultModel: 'big' },
    'which model is talked to comes over; packages, extensions, skills, themes, prompts and a session directory do not')
  assert.deepEqual(tree(pi).map((file) => [file, readFileSync(join(pi, file), 'utf8')]), before, 'Pi\'s own setup is only read')

  // Once: what wizardry then has is its own, whatever happens to Pi's.
  writeFileSync(join(home, 'pi', 'auth.json'), '{"acme":{"type":"api_key","key":"sk-own"}}')
  const second = run(['plugins'])
  assert.doesNotMatch(second.stderr, /Brought over/)
  assert.equal(readFileSync(join(home, 'pi', 'auth.json'), 'utf8'), '{"acme":{"type":"api_key","key":"sk-own"}}')

  // Where the environment names another directory for Pi, that one is the setup of Pi's own: it
  // is what would be read, once, and it is never written to.
  const where = run(['plugins'], { PI_CODING_AGENT_DIR: join(user, 'somewhere-else'), WIZARDRY_HOME: join(user, 'other-home') })
  assert.equal(where.status, 0, where.stderr)
  assert.doesNotMatch(where.stderr, /Brought over/)
  assert.ok(!existsSync(join(user, 'somewhere-else')) && !existsSync(join(user, 'other-home', 'pi', 'auth.json')))
})

test('a command the agent runs sees the environment wizardry was started in, not the one it makes for Pi', async () => {
  const { home, cwd } = scratch()
  const kept = { ...process.env }
  process.env.PI_CODING_AGENT_DIR = join(cwd, 'the-users-pi')
  delete process.env.PI_SKIP_VERSION_CHECK
  process.env.PI_PACKAGE_DIR = '/nix/store/pi'
  try {
    keepApart(home)
    assert.equal(process.env.PI_CODING_AGENT_DIR, join(home, 'pi'), 'Pi is pointed at wizardry\'s own directory')
    assert.equal(process.env.PI_SKIP_VERSION_CHECK, '1', 'and does not offer its own update inside wizardry')
    assert.equal(process.env.PI_PACKAGE_DIR, undefined)
    assert.ok(!existsSync(join(home, 'pi')), 'with no setup of Pi\'s to bring over, nothing is made up')
    const { root } = await boot({ home, cwd, defaults: ['shell'] })
    const out = await root.get('actions').invoke('bash', { command: 'printf "%s|%s|%s" "$PI_CODING_AGENT_DIR" "${PI_SKIP_VERSION_CHECK-unset}" "$PI_PACKAGE_DIR"' }, { cwd })
    assert.match(out.text ?? out, new RegExp(`${join(cwd, 'the-users-pi')}\\|unset\\|/nix/store/pi`))
    await root.fiber.dispose()
  } finally {
    for (const name of Object.keys(process.env)) if (!(name in kept)) delete process.env[name]
    Object.assign(process.env, kept)
  }
})

test('export copies every conversation and memory to a folder of its own, and never over one that is there', async () => {
  const { user, pi, home, run } = machine()
  const { openStore } = await import('../defaults/memory/store.js')
  const store = await openStore(join(home, 'memory', 'memory.db'))
  store.add({ kind: 'observation', project: 'work', time: '2026-11-19 10:02', type: 'decision', title: 'Chose blue', text: 'Chose the blue theme over the green one' })
  store.close()
  mkdirSync(join(home, 'notes'))
  writeFileSync(join(home, 'notes', 'kept.txt'), 'by a plugin that is not loaded')
  run(['plugins'])

  const done = run(['export', join(user, 'keep')])
  assert.equal(done.status, 0, done.stderr)
  assert.equal(done.stdout, [
    `wizardry: exported to ${join(user, 'keep')}:`,
    `  1 conversation from ${join(home, 'sessions')}, in conversations/wizardry/`,
    `  1 conversation from ${join(pi, 'sessions')}, in conversations/pi/`,
    '  1 memory, in memory/',
    '  notes/ as it was kept: no loaded plugin exported it',
    ''].join('\n'))
  assert.deepEqual(tree(join(user, 'keep')), [
    'README.md', 'conversations/pi/--work--/old.jsonl', 'conversations/pi/--work--/old.md', 'conversations/wizardry/new.jsonl',
    'conversations/wizardry/new.md', 'memory/memories.json', 'memory/memories.md', 'memory/memory.db', 'notes/kept.txt'])
  assert.ok(!tree(join(user, 'keep')).some((file) => /auth\.json|settings\.json/.test(file)), 'logins are not conversations: they stay where they are')
  assert.equal(readFileSync(join(user, 'keep', 'conversations', 'wizardry', 'new.jsonl'), 'utf8'), readFileSync(join(home, 'sessions', 'new.jsonl'), 'utf8'), 'a conversation is kept exactly as it was')

  const text = readFileSync(join(user, 'keep', 'conversations', 'pi', '--work--', 'old.md'), 'utf8')
  assert.match(text, /^# Conversation of 2026-11-19 \d\d:\d\d\n\n- Directory: \/work\n- Kept whole in: old\.jsonl\n\n## User · 2026-11-19 \d\d:\d\d\n\ncount for pi\n\n## Assistant · [^\n]*\n\nLooking\.\n\n> \*\*bash\*\* \{"command":"seq 14"\}\n\n    1\n    2\n/)
  assert.match(text, /    10\n    \.\.\. 4 more lines, in the \.jsonl\n\n## Assistant · [^\n]*\n\nFourteen lines\.\n\n$/)
  assert.doesNotMatch(text, /a private thought|memory:observed|model_change/)
  assert.match(readFileSync(join(user, 'keep', 'memory', 'memories.md'), 'utf8'), /## work\n\n### #1 · observation \(decision\) · 2026-11-19 10:02\n\nChose blue\n\nChose the blue theme over the green one\n/)
  assert.match(readFileSync(join(user, 'keep', 'README.md'), 'utf8'), /- 1 memory, in memory\/\n/)

  // The same folder is not written over, and with no folder named each export of a day gets its own.
  const again = run(['export', join(user, 'keep')])
  assert.equal(again.status, 1)
  assert.match(again.stderr, /is not empty\. Name a new folder, so that nothing in it is overwritten\./)
  const [one, two] = [run(['export']), run(['export'])]
  const named = (out) => out.stdout.match(/exported to (.*):/)[1]
  assert.match(named(one), new RegExp(`^${user}/wizardry-export-\\d{4}-\\d\\d-\\d\\d$`))
  assert.equal(named(two), `${named(one)}-2`)
  assert.equal(run(['export', join(home, 'sessions', 'inside')]).status, 1, 'nor into the conversations it copies')
  assert.equal(run(['export', 'a', 'b']).status, 2)
})

test('delete says what would go and removes nothing until --yes; then it exports first, and removes only what was named', () => {
  const { user, pi, home, run } = machine()
  run(['plugins'])
  const all = () => [...tree(user)]
  const whole = all()

  // Asking is safe.
  const preview = run(['delete', 'old'])
  assert.equal(preview.status, 0)
  assert.match(preview.stdout, new RegExp(`^wizardry delete old would delete:\\n  ${pi}  \\(\\d+ (bytes|KB)\\)\\n  ${user}/.local/bin/pi  \\(a command that points into it\\)\\nFirst, every conversation and memory is exported to ${user}/wizardry-export-[-\\d]+\\.\\nNothing has been deleted\\. To go ahead: wizardry delete old --yes\\n$`))
  assert.equal(run(['delete']).status, 2)
  assert.equal(run(['delete', 'old', '--force']).status, 2, 'an option it does not know is not guessed at')
  assert.match(run(['delete', 'everything', '--yes']).stderr, /say what to delete: conversations, memories, old or all/)
  // Nor is anything removed when the export could not be kept, or wizardry's directory is the home directory itself.
  assert.match(run(['delete', 'old', '--yes', '--to', join(pi, 'out')]).stderr, /the export would go to .*inside what is deleted/)
  writeFileSync(join(user, 'taken'), 'a file where the export should go')
  const failed = run(['delete', 'conversations', '--yes', '--to', join(user, 'taken')])
  assert.equal(failed.status, 1)
  assert.match(failed.stderr, /nothing was deleted: the export did not finish/)
  assert.match(run(['delete', 'all', '--yes', '--no-export'], { WIZARDRY_HOME: user }).stderr, /nothing was deleted: that would take your home directory along/)
  assert.match(run(['delete', 'old', '--yes', '--no-export'], { PI_CODING_AGENT_DIR: join(home, 'pi') }).stderr, /so it is not an old setup/)
  assert.deepEqual(all().filter((file) => !file.startsWith('pi/')), [...whole, 'taken'].sort(), 'none of that removed or exported anything')

  // The old setup goes: Pi's directory, the command that pointed into it, and the folder that held it.
  const old = run(['delete', 'old', '--yes', '--to', join(user, 'kept-old')])
  assert.equal(old.status, 0, old.stderr)
  assert.match(old.stdout, new RegExp(`^wizardry: deleted:\\n  ${pi}  .*\\n  ${user}/.local/bin/pi  .*\\nEvery conversation and memory was exported first, to ${user}/kept-old\\.\\n$`))
  assert.ok(!existsSync(join(user, '.pi')), '~/.pi is gone, as nothing else was in it')
  assert.throws(() => lstatSync(join(user, '.local', 'bin', 'pi')), 'no command is left pointing at nothing')
  assert.ok(lstatSync(join(user, '.local', 'bin', 'sh-too')).isSymbolicLink(), 'a command that points elsewhere stays')
  assert.equal(readFileSync(join(user, 'kept-old', 'conversations', 'pi', '--work--', 'old.jsonl'), 'utf8').includes('count for pi'), true, 'its conversations are in the export')
  assert.equal(readFileSync(join(home, 'pi', 'auth.json'), 'utf8'), '{"acme":{"type":"api_key","key":"sk-secret"}}', 'wizardry is whole, and still signed in')
  assert.ok(existsSync(join(home, 'sessions', 'new.jsonl')))
  assert.match(run(['delete', 'old', '--yes']).stdout, /nothing to delete: there is no setup of Pi's own on this machine/)

  // Conversations go, and nothing else of wizardry's.
  const gone = run(['delete', 'conversations', '--yes'])
  assert.equal(gone.status, 0, gone.stderr)
  const kept = gone.stdout.match(/exported first, to (.*)\.\n$/)[1]
  assert.ok(existsSync(join(kept, 'conversations', 'wizardry', 'new.md')))
  assert.ok(!existsSync(join(home, 'sessions')) && existsSync(join(home, 'pi', 'auth.json')) && existsSync(join(home, 'memory')))

  // All of it goes, with the command that ran it when that was part of it.
  mkdirSync(join(home, 'app'))
  writeFileSync(join(home, 'app', 'bin.js'), '')
  symlinkSync(join(home, 'app', 'bin.js'), join(user, '.local', 'bin', 'wizardry'))
  const none = run(['delete', 'all', '--yes', '--no-export'])
  assert.equal(none.status, 0, none.stderr)
  assert.match(none.stdout, /Nothing is exported first: you said --no-export\./)
  assert.ok(!existsSync(home))
  assert.throws(() => lstatSync(join(user, '.local', 'bin', 'wizardry')))
  assert.ok(existsSync(kept) && existsSync(join(user, 'kept-old')) && existsSync(join(user, 'work')), 'the exports and everything else in the home directory are untouched')
})

test('/default makes this session\'s model, thinking level and plugins what the next one starts with', async () => {
  const { home, cwd } = scratch()
  mkdirSync(join(home, 'plugins'))
  writeFileSync(join(home, 'plugins', 'echo.mjs'), pluginSource('home:'))
  const extra = join(cwd, 'extra.mjs')
  writeFileSync(extra, pluginSource('extra:').replaceAll('echo', 'extra'))
  mkdirSync(join(home, 'pi'))
  writeFileSync(join(home, 'pi', 'settings.json'), JSON.stringify({ defaultProvider: 'old', defaultModel: 'small', httpProxy: 'http://proxy' }))

  const first = await boot({ home, cwd, defaults: ['pi', 'cordis', 'fs', 'shell'] })
  const commands = {}
  first.root.get('pi').attach({ registerTool() {}, on() {}, getAllTools: () => [], getActiveTools: () => [], setActiveTools() {}, getThinkingLevel: () => 'high', registerCommand: (name, command) => { commands[name] = command } })
  // This session: without the shell and the home plugin, with one loaded by hand and the gate.
  await first.plugins.unload('shell')
  await first.plugins.unload('echo')
  await first.plugins.load(extra)
  await first.plugins.load('gate')
  const said = []
  await commands.default.handler('', { model: { provider: 'acme', id: 'big' }, ui: { notify: (text) => said.push(text) } })
  assert.equal(said[0], 'New sessions now start as this one. Model: acme/big. Thinking: high. Plugins: pi, cordis, fs, extra, gate.')
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'pi', 'settings.json'), 'utf8')),
    { defaultProvider: 'acme', defaultModel: 'big', httpProxy: 'http://proxy', defaultThinkingLevel: 'high' }, 'the settings it does not speak of are as they were')
  await first.root.fiber.dispose()

  const second = await boot({ home, cwd, defaults: ['pi', 'cordis', 'fs', 'shell'] })
  assert.deepEqual(second.failures, [])
  assert.deepEqual(second.plugins.list().map((plugin) => plugin.name).sort(), ['cordis', 'extra', 'fs', 'gate', 'pi'])
  // And back: with everything loaded again, nothing stays switched off.
  await second.plugins.load('shell')
  await second.plugins.load(join(home, 'plugins', 'echo.mjs'))
  second.plugins.keep()
  assert.deepEqual(JSON.parse(readFileSync(join(home, 'plugins.json'), 'utf8')).disabled, [])
  await second.root.fiber.dispose()
  const third = await boot({ home, cwd, defaults: ['pi', 'cordis', 'fs', 'shell'] })
  assert.deepEqual(third.plugins.list().map((plugin) => plugin.name).sort(), ['cordis', 'echo', 'extra', 'fs', 'gate', 'pi', 'shell'])
  await third.root.fiber.dispose()
})
