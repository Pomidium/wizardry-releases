import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { keyHint, keyText, rawKeyHint, type Theme } from '@earendil-works/pi-coding-agent'
import { isViewportTUI, truncateToWidth, visibleWidth, wrapTextWithAnsi, type Component, type TUI } from '@earendil-works/pi-tui'
import type { RegisteredAction } from './actions.js'
import { core } from './core.js'

/** How wizardry looks in the terminal: its logo, its startup header, its colors and how tool calls read. None of it reaches the agent. */

export const VERSION: string = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version

/** The blue themes shipped with wizardry, and the light/dark pair Pi picks from. */
export const THEME_DIR = fileURLToPath(new URL('../themes', import.meta.url))
export const THEME_PAIR = 'wizardry-light/wizardry'

/** Pi arguments that put wizardry's colors on, unless the user asked for a theme of their own. */
export function themeArgs(argv: string[]) {
  return core.themeArgs(argv, THEME_DIR, THEME_PAIR)
}

/**
 * The logo: a wizard's cap. Its rows, its sparks and what each shows on each frame are in Bend
 * (bend/core.bend), where it is proven that every frame has the plain cap's shape and that frame 0
 * is the plain cap, so a header that never animates shows the logo.
 */
export const HAT = core.hat()
export const HAT_FRAMES = 8
export const HAT_INTERVAL_MS = 320

const FRAMES = Array.from({ length: HAT_FRAMES }, (_, frame) => core.hatFrame(frame))

/** The cap's rows on one frame of its twinkle. Every frame has HAT's size. */
export function hatFrame(frame: number) {
  return [...FRAMES[((frame % HAT_FRAMES) + HAT_FRAMES) % HAT_FRAMES]]
}

/**
 * Blues and greys only: the cap in the accent blue, a spark pale blue at its brightest and grey as
 * it fades. Which theme color a piece gets is decided in Bend, where it is proven to be one of four.
 */
function paint(row: string, theme: Theme) {
  return row.replace(/[*+.]|[^*+.]+/g, (part) => {
    const color = core.ink(part)
    const painted = theme.fg(color as Parameters<Theme['fg']>[0], part)
    return color === 'text' ? theme.bold(painted) : painted
  })
}

export function hatLines(theme: Theme, frame = 0) {
  return hatFrame(frame).map((row) => paint(row, theme))
}

/**
 * The small cap that stands where Pi's spinner did while the agent works: one row, a spark
 * drifting off its tip. Every frame is the same width, so the message beside it stays put.
 */
export const SMALL_HAT = core.smallHat()

/** What `ui.setWorkingIndicator` takes. Pi draws custom frames as given, so they carry their own colors. */
export function workingIndicator(theme: Theme) {
  return { frames: SMALL_HAT.map((row) => paint(row, theme)), intervalMs: 140 }
}

function compactHints() {
  return [
    keyHint('app.interrupt', 'interrupt'),
    rawKeyHint(`${keyText('app.clear')}/${keyText('app.exit')}`, 'clear/exit'),
    rawKeyHint('/', 'commands'),
    rawKeyHint('!', 'bash'),
    keyHint('app.tools.expand', 'more'),
  ]
}

/**
 * Join items onto as few lines as the width allows, without breaking one in two. How many go on
 * each line is decided in Bend from their widths, where it is proven that every item is placed.
 */
function pack(items: string[], separator: string, width: number) {
  let at = 0
  return core.pack(items.map((item) => visibleWidth(item)), visibleWidth(separator), width)
    .map((count) => items.slice(at, (at += count)).join(separator))
}

function expandedHints() {
  return [
    keyHint('app.interrupt', 'to interrupt'),
    keyHint('app.clear', 'to clear'),
    rawKeyHint(`${keyText('app.clear')} twice`, 'to exit'),
    keyHint('app.exit', 'to exit (empty)'),
    keyHint('app.suspend', 'to suspend'),
    keyHint('tui.editor.deleteToLineEnd', 'to delete to end'),
    keyHint('app.thinking.cycle', 'to cycle thinking level'),
    rawKeyHint(`${keyText('app.model.cycleForward')}/${keyText('app.model.cycleBackward')}`, 'to cycle models'),
    keyHint('app.model.select', 'to select model'),
    keyHint('app.tools.expand', 'to expand tools'),
    keyHint('app.thinking.toggle', 'to expand thinking'),
    keyHint('app.editor.external', 'for external editor'),
    rawKeyHint('/', 'for commands'),
    rawKeyHint('!', 'to run bash'),
    rawKeyHint('!!', 'to run bash (no context)'),
    keyHint('app.message.followUp', 'to queue follow-up'),
    keyHint('app.message.dequeue', 'to edit all queued messages'),
    keyHint('app.clipboard.pasteImage', 'to paste files on macOS, images, or text'),
    rawKeyHint('drop files', 'to attach'),
  ]
}

/** What the header says about one loaded plugin. */
export interface PluginLine {
  name: string
  source: string
  state: string
}

/** The part of Pi's TUI the header needs to animate itself. */
type Screen = Pick<TUI, 'requestRender'>

/** The startup header: the twinkling cap, with the name and key hints beside it. Replaces Pi's logo. */
export class Header implements Component {
  private expanded = false
  private frame = 0
  private timer?: ReturnType<typeof setInterval>

  /**
   * `plugins` is asked on every draw, so the list follows what is loaded now. Given the `tui`, the
   * cap twinkles for as long as it is on screen; without one it is drawn still.
   */
  constructor(private theme: Theme, private plugins?: () => PluginLine[], private tui?: Screen) {
    if (!tui) return
    this.timer = setInterval(() => this.tick(), HAT_INTERVAL_MS)
    this.timer.unref?.()
  }

  /**
   * On the main screen pi-tui clears and redraws everything, scrollback included, when a line
   * above the viewport changes. So the cap only moves while nothing has scrolled away; if that
   * cannot be told, it stays still.
   */
  private tick() {
    const tui = this.tui as (Screen & { previousViewportTop?: unknown }) | undefined
    if (!tui) return
    if (!core.capMoves(isViewportTUI(tui as TUI), tui.previousViewportTop === 0)) return
    this.frame = core.nextFrame(this.frame)
    tui.requestRender()
  }

  /** Pi calls this when the header is replaced or the session ends. */
  dispose() {
    if (this.timer) clearInterval(this.timer)
    this.timer = undefined
  }

  /** Pi calls this when the user toggles expansion (ctrl+o by default). */
  setExpanded(expanded: boolean) {
    this.expanded = expanded
  }

  invalidate() {}

  render(width: number): string[] {
    const { theme } = this
    const hat = hatLines(theme, this.frame)
    const hatWidth = visibleWidth(HAT[0])
    const title = `${theme.bold(theme.fg('accent', 'wizardry'))} ${theme.fg('dim', `v${VERSION}`)}`
    const text = (room: number) => [
      title,
      theme.fg('muted', 'Pi on Cordis'),
      ...(this.expanded ? ['', ...expandedHints()] : pack(compactHints(), theme.fg('muted', ' · '), room)),
    ].flatMap((line) => (line ? wrapTextWithAnsi(line, Math.max(1, room)) : ['']))

    // Where the text goes, and which row holds what, is decided in Bend: beside the cap, against
    // its brim, when there is room, and under it otherwise. Wrapping and cutting are pi-tui's.
    const { where, room } = core.layout(width, hatWidth)
    const rows = where === 'Beside' ? core.headerBeside(hat, text(room), hatWidth) : core.headerUnder(hat, text(room))
    return [...rows, ...this.pluginRows(width)].map((row) => truncateToWidth(row, width))
  }

  /** Every loaded Cordis plugin, in the place and style Pi lists its extensions (of which wizardry is the only one). */
  private pluginRows(width: number) {
    const { theme } = this
    const plugins = this.plugins?.() ?? []
    if (!plugins.length) return []
    const body = this.expanded
      ? core.pluginRows(plugins)
      : core.indented(wrapTextWithAnsi(core.pluginLine(plugins), Math.max(1, width - 2)))
    return ['', theme.fg('mdHeading', '[Plugins]'), ...body.map((line) => theme.fg('dim', line))]
  }
}

/**
 * What the user sees a call named as: the plugin, then what it did. `plugin_load` from `cordis`
 * reads "cordis plugin load", `subagent_create` from `subagent` reads "subagent create". Pi's own
 * tools keep their names (read, bash, ...), and an action's `title` overrides all of it.
 */
export function actionTitle(action: Pick<RegisteredAction, 'name' | 'owner' | 'title' | 'native'>) {
  return core.actionTitle(action.title, !!action.native, action.name, action.owner)
}

/** A list of plain values reads as "a, b"; anything else nested stays JSON. */
function plain(value: unknown) {
  if (typeof value === 'string') return value
  if (Array.isArray(value) && value.every((item) => item === null || typeof item !== 'object')) return value.join(', ')
  return undefined
}

/** On the title line a value is cut to 72 characters; the rest is one ctrl+o away. */
function brief(value: unknown) {
  return core.brief(plain(value) ?? JSON.stringify(value) ?? String(value))
}

function whole(value: unknown) {
  return core.expand(plain(value) ?? JSON.stringify(value, null, 2) ?? String(value), '    ')
}

/**
 * The line a call is announced with: its title, the plugin's name in the accent color, then its
 * arguments. Collapsed they follow on the same line, each cut short; expanded each gets its own
 * line in full. Arguments left out (null under strict schemas) are not shown.
 */
export function callText(action: Pick<RegisteredAction, 'name' | 'owner' | 'title' | 'native'>, args: unknown, theme: Theme, expanded: boolean) {
  const title = actionTitle(action)
  const owner = core.words(action.owner)
  const mine = core.mine(title, owner)
  const head = mine
    ? theme.bold(theme.fg('accent', owner)) + theme.bold(theme.fg('toolTitle', title.slice(owner.length)))
    : theme.bold(theme.fg('toolTitle', title))
  const given = args && typeof args === 'object' && !Array.isArray(args)
    ? Object.entries(args).filter(([, value]) => value !== null && value !== undefined)
    : []
  if (!given.length) return head
  const key = (name: string) => theme.fg('muted', `${name}:`)
  if (expanded) return [head, ...given.map(([name, value]) => `  ${key(name)} ${theme.fg('text', whole(value))}`)].join('\n')
  return `${head}  ${given.map(([name, value]) => `${key(name)} ${theme.fg('text', brief(value))}`).join(theme.fg('muted', ' · '))}`
}

/** What a call came back with, below its title: the first lines, and how many more there are. */
export function resultText(output: string, theme: Theme, expanded: boolean) {
  // The first ten lines unless expanded; which and how many are hidden is decided in Bend.
  const { shown, more } = core.resultView(output, expanded)
  if (core.blankView(shown, more)) return ''
  const hint = more > 0
    ? `\n${theme.fg('muted', core.moreHint(more))} ${keyHint('app.tools.expand', 'to expand')}${theme.fg('muted', ')')}`
    : ''
  return `\n${shown.map((line) => theme.fg('toolOutput', line)).join('\n')}${hint}`
}
