import {
  copyFileSync, cpSync, existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, readlinkSync, realpathSync, rmdirSync,
  rmSync, writeFileSync,
} from 'node:fs'
import { homedir } from 'node:os'
import { basename, dirname, join, relative, resolve } from 'node:path'
import { oldPi } from './apart.js'
import { boot, wizardryHome } from './boot.js'
import { core, type Exported } from './core.js'

declare module '@deepseek-ai/cordis' {
  interface Events {
    /**
     * The user asked for a copy of everything of theirs (`wizardry export`, and before every
     * `wizardry delete`). A plugin that keeps data in `<home>/<name>/` writes it into
     * `<dir>/<name>/` and tells `wrote`, in one line, what it put there. A folder no plugin
     * exported is copied as it is. A listener that throws stops the export, and so the deletion.
     */
    'export'(dir: string, wrote: (line: string) => void): void | Promise<void>
  }
}

/**
 * `wizardry export` and `wizardry delete`: a copy of every conversation and memory, and the way
 * to remove a setup once it is copied. Where things go, what a transcript reads like, what may be
 * deleted and when are decided in Bend (bend/core.bend, "Export" and "Delete"), where it is
 * proven that nothing is deleted unasked, before its export, or outside what was named. This
 * file reads the disk and does what Bend answered.
 */

/** A path with every link in it followed, as far as it exists. */
function real(path: string): string {
  const full = resolve(path)
  try {
    return realpathSync(full)
  } catch {}
  const up = dirname(full)
  return up === full ? full : join(real(up), basename(full))
}

/** The directories everything here is about, as the disk names them. */
export function places() {
  return { userhome: real(homedir()), home: real(wizardryHome()), old: real(oldPi()) }
}

export type Places = ReturnType<typeof places>

/** Now, in local time, as "2026-11-20 19:16:34". */
const stamp = (at: unknown) => {
  const date = new Date(at as any)
  return Number.isNaN(date.getTime()) ? '' : date.toLocaleString('sv-SE')
}

/** Every conversation under `dir`, as paths relative to it. */
function conversations(dir: string) {
  const found: string[] = []
  const walk = (at: string) => {
    for (const entry of readdirSync(at, { withFileTypes: true })) {
      const path = join(at, entry.name)
      if (entry.isDirectory()) walk(path)
      else if (entry.isFile() && core.isConversation(entry.name)) found.push(relative(dir, path))
    }
  }
  if (existsSync(dir)) walk(dir)
  return found.sort()
}

function textOf(content: unknown) {
  if (typeof content === 'string') return content
  if (!Array.isArray(content)) return ''
  return content.filter((part) => part?.type === 'text' && typeof part.text === 'string').map((part) => part.text).join('\n')
}

const jsonOf = (value: unknown) => {
  if (typeof value === 'string') return value
  try {
    return JSON.stringify(value) ?? ''
  } catch {
    return ''
  }
}

/** A session entry as the pieces Bend writes down: each with its kind, a name, and its text. */
function pieces(entry: any): { kind: string; name: string; text: string }[] {
  const one = (kind: unknown, name: unknown, text: string) => ({ kind: String(kind ?? ''), name: String(name ?? ''), text })
  const message = entry?.message
  if (entry?.type !== 'message' || !message) return [one(entry?.type, '', textOf(entry?.summary ?? entry?.content))]
  const content = typeof message.content === 'string' ? [{ type: 'text', text: message.content }] : Array.isArray(message.content) ? message.content : []
  const out = content.map((part: any) => part?.type === 'text'
    ? one(message.role, message.toolName, String(part.text ?? ''))
    : one(part?.type, part?.name, jsonOf(part?.arguments ?? '')))
  if (message.role === 'bashExecution') out.push(one(message.role, message.command, String(message.output ?? '')))
  if (message.errorMessage) out.push(one('error', '', String(message.errorMessage)))
  return out
}

/** A conversation as text to read. */
function transcript(file: string) {
  const out: string[] = []
  for (const line of readFileSync(file, 'utf8').split('\n')) {
    if (!line.trim()) continue
    let entry: any
    try {
      entry = JSON.parse(line)
    } catch {
      continue
    }
    const at = stamp(entry?.timestamp)
    if (entry?.type === 'session') out.push(core.transcriptHead(basename(file), String(entry.cwd ?? ''), at))
    else for (const piece of pieces(entry)) out.push(core.piece(piece.kind, piece.name, at, piece.text))
  }
  return out.join('')
}

const folders = (dir: string) => (existsSync(dir) ? readdirSync(dir, { withFileTypes: true }).filter((entry) => entry.isDirectory()).map((entry) => entry.name) : [])

/**
 * Copy every conversation and memory into `dir`. Returns what was exported, line by line; throws
 * when it could not be finished.
 */
export async function exportTo(dir: string, at: Places = places()) {
  if (!core.exportFits(dir, at.home, at.old)) throw new Error(core.exportInside(dir))
  if (taken(dir)) throw new Error(core.exportTaken(dir))
  mkdirSync(dir, { recursive: true })
  const tallies = core.origins(at.home, at.old).map(({ name, dir: from }) => {
    const files = conversations(from)
    for (const rel of files) {
      const to = core.conversationTo(dir, name, rel)
      mkdirSync(dirname(to), { recursive: true })
      copyFileSync(join(from, rel), to)
      writeFileSync(core.readable(to), transcript(to))
    }
    return { name, from, count: files.length }
  })

  // What plugins keep is theirs to export: each writes its own folder and says what it wrote.
  const wrote: string[] = []
  const quiet = process.env.WIZARDRY_NO_UPDATE
  process.env.WIZARDRY_NO_UPDATE = '1'
  const { root } = await boot({ home: at.home })
  try {
    await root.parallel('export', dir, (line: string) => { wrote.push(line) })
  } finally {
    await root.fiber.dispose()
    if (quiet === undefined) delete process.env.WIZARDRY_NO_UPDATE
    else process.env.WIZARDRY_NO_UPDATE = quiet
  }
  for (const name of core.leftOver(folders(at.home), folders(dir))) {
    cpSync(join(at.home, name), join(dir, name), { recursive: true })
    wrote.push(core.leftOverLine(name))
  }

  const lines = core.exportLines(tallies, wrote)
  writeFileSync(join(dir, 'README.md'), core.exportReadme(core.day(stamp(Date.now())), lines))
  return lines
}

/** Whether something is already at `dir`: an export is only written to a folder that is new or empty. */
function taken(dir: string) {
  try {
    return readdirSync(dir).length > 0
  } catch {
    return existsSync(dir)
  }
}

/** Where an export goes when the user said `chosen` (empty for nothing): then, the first name of the day that is free. */
function exportDir(chosen: string, at: Places) {
  const day = core.day(stamp(Date.now()))
  let again = 0
  let dir = real(core.exportDir(chosen ? resolve(chosen) : '', at.userhome, day, again))
  while (!chosen && taken(dir)) dir = real(core.exportDir('', at.userhome, day, ++again))
  return dir
}

/** `wizardry export [folder]`. Returns the exit code. */
export async function exportCommand(argv: string[]) {
  const asked = core.exportAsked(argv)
  if (asked === undefined) {
    process.stderr.write(`${core.exportUsage()}\n`)
    return 2
  }
  const at = places()
  const dir = exportDir(asked, at)
  try {
    process.stdout.write(core.updateSaid(core.exportSaid(dir, await exportTo(dir, at))))
    return 0
  } catch (error: any) {
    process.stderr.write(`${core.updateSaid(core.exportBroke(String(error?.message ?? error)))}\n`)
    return 1
  }
}

/** How much is under a path, in bytes. Links are counted, not followed. */
function bytes(path: string): number {
  try {
    const stat = lstatSync(path)
    if (!stat.isDirectory()) return stat.size
    return readdirSync(path).reduce((total, name) => total + bytes(join(path, name)), 0)
  } catch {
    return 0
  }
}

const isLink = (path: string) => {
  try {
    return lstatSync(path).isSymbolicLink()
  } catch {
    return false
  }
}

/** The links among `paths`, each with what it points to. */
function linksAmong(paths: string[]) {
  return paths.filter(isLink).map((path) => ({ path, target: real(resolve(dirname(path), readlinkSync(path))) }))
}

/** `wizardry delete <what> [--yes] [--to <folder>] [--no-export]`. Returns the exit code. */
export async function deleteCommand(argv: string[], invoked = process.argv[1]) {
  const asked = core.deleteAsked(argv)
  if (!asked.clear) {
    process.stderr.write(core.deleteUsage())
    return 2
  }
  const at = places()
  const to = asked.waived ? '' : exportDir(asked.to, at)
  // What may go is decided in Bend, where it is proven that it never includes the user's home
  // directory or the export, and that the old setup never includes wizardry.
  const why = core.whyNot(asked.what, at.home, at.old, at.userhome, to)
  if (why) {
    process.stderr.write(`${core.updateSaid(why)}\n`)
    return 1
  }
  const doomed = core.doomed(asked.what, at.home, at.old, at.userhome, to).filter((path) => existsSync(path))
  if (!doomed.length) {
    process.stdout.write(`${core.updateSaid(core.nothingThere(asked.what))}\n`)
    return 0
  }
  const dirs = core.linkDirs(invoked ?? '', process.env.WIZARDRY_BIN_DIR ?? '', at.userhome)
  const candidates = [...dirs.flatMap((dir) => (existsSync(dir) ? readdirSync(dir).map((name) => join(dir, name)) : [])), core.oldHomeLink(at.userhome)]
  const links = core.dangling(linksAmong(candidates), doomed)
  const rows = doomed.map((path) => ({ path, bytes: bytes(path) }))
  if (!asked.yes) {
    process.stdout.write(core.deletePreview(asked.what, rows, links, to, asked.waived))
    return 0
  }

  let exported: Exported = 'Waived'
  if (!asked.waived) {
    try {
      await exportTo(to, at)
      exported = 'Kept'
    } catch (error: any) {
      exported = 'Failed'
      process.stderr.write(`${core.updateSaid(core.exportFirstFailed(String(error?.message ?? error)))}\n`)
    }
  }
  // Whether anything goes now is decided in Bend: nothing without --yes, nothing after an export that failed.
  const going = core.goes(doomed, asked.yes, exported)
  if (!going.length) return 1
  for (const path of going) rmSync(path, { recursive: true, force: true })
  // A folder named two ways lists its links twice: a link already gone is gone.
  for (const link of core.goes(links, asked.yes, exported)) rmSync(link, { force: true })
  for (const dir of core.goes(core.emptied(asked.what, doomed, at.userhome), asked.yes, exported)) {
    try {
      rmdirSync(dir)
    } catch {}
  }
  process.stdout.write(core.updateSaid(core.deletedSaid(rows, links, to, asked.waived)))
  return 0
}
