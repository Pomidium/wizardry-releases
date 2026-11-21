// The store: one SQLite file holding every memory, searchable in full text.
//
// It keeps and finds; it decides nothing. What is worth keeping, what a search asks for and how
// a result reads are decided in Bend (core.mjs). SQLite is Node's own (node:sqlite), so there is
// no worker to start and nothing to install.

import { createHash } from 'node:crypto'
import { existsSync, mkdirSync } from 'node:fs'
import { dirname } from 'node:path'

const SCHEMA = `
CREATE TABLE IF NOT EXISTS memories (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  kind TEXT NOT NULL,
  project TEXT NOT NULL,
  session TEXT NOT NULL DEFAULT '',
  time TEXT NOT NULL,
  epoch INTEGER NOT NULL,
  type TEXT NOT NULL DEFAULT '',
  title TEXT NOT NULL DEFAULT '',
  summary TEXT NOT NULL DEFAULT '',
  text TEXT NOT NULL,
  tokens INTEGER NOT NULL DEFAULT 0,
  source TEXT NOT NULL DEFAULT 'wizardry',
  folded INTEGER NOT NULL DEFAULT 0,
  hash TEXT NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS memories_once ON memories(kind, project, session, hash);
CREATE INDEX IF NOT EXISTS memories_recent ON memories(project, kind, epoch DESC, id DESC);
CREATE VIRTUAL TABLE IF NOT EXISTS memories_fts USING fts5(
  title, summary, text, content='memories', content_rowid='id', tokenize='porter unicode61'
);
CREATE TRIGGER IF NOT EXISTS memories_ai AFTER INSERT ON memories BEGIN
  INSERT INTO memories_fts(rowid, title, summary, text) VALUES (new.id, new.title, new.summary, new.text);
END;
CREATE TRIGGER IF NOT EXISTS memories_ad AFTER DELETE ON memories BEGIN
  INSERT INTO memories_fts(memories_fts, rowid, title, summary, text) VALUES ('delete', old.id, old.title, old.summary, old.text);
END;
CREATE TRIGGER IF NOT EXISTS memories_au AFTER UPDATE OF title, summary, text ON memories BEGIN
  INSERT INTO memories_fts(memories_fts, rowid, title, summary, text) VALUES ('delete', old.id, old.title, old.summary, old.text);
  INSERT INTO memories_fts(rowid, title, summary, text) VALUES (new.id, new.title, new.summary, new.text);
END;
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
`

const COLUMNS = 'id, kind, project, session, time, epoch, type, title, summary, text, tokens, source, folded'
const hashOf = (text) => createHash('sha256').update(text).digest('hex').slice(0, 32)

/** node:sqlite, without the "experimental" warning older Node versions print over the terminal. */
async function sqlite() {
  const emit = process.emitWarning
  process.emitWarning = function (warning, ...rest) {
    if (String(warning?.message ?? warning).includes('SQLite')) return
    return emit.call(this, warning, ...rest)
  }
  try {
    return await import('node:sqlite')
  } finally {
    process.emitWarning = emit
  }
}

/** "2026-11-19 14:05" in local time. */
export function minute(at) {
  const d = new Date(at)
  const two = (n) => String(n).padStart(2, '0')
  return `${d.getFullYear()}-${two(d.getMonth() + 1)}-${two(d.getDate())} ${two(d.getHours())}:${two(d.getMinutes())}`
}

const epochOf = (time) => {
  const at = new Date(time.replace(' ', 'T')).getTime()
  return Number.isFinite(at) ? at : Date.now()
}

/** Open (creating if need be) the store at `file`. Throws when this Node has no SQLite. */
export async function openStore(file) {
  const { DatabaseSync } = await sqlite()
  if (file !== ':memory:') mkdirSync(dirname(file), { recursive: true })
  const db = new DatabaseSync(file)
  db.exec('PRAGMA journal_mode = WAL; PRAGMA busy_timeout = 5000; PRAGMA synchronous = NORMAL;')
  db.exec(SCHEMA)

  const insert = db.prepare(`INSERT OR IGNORE INTO memories (kind, project, session, time, epoch, type, title, summary, text, tokens, source, hash)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`)
  const find = db.prepare('SELECT id FROM memories WHERE kind = ? AND project = ? AND session = ? AND hash = ?')
  const getMeta = db.prepare('SELECT value FROM meta WHERE key = ?')
  const setMeta = db.prepare('INSERT INTO meta (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value')

  /** Add a memory once: the same text in the same place is the same memory. Returns its id. */
  function add(row) {
    const hash = row.hash ?? hashOf(row.text)
    const session = row.session ?? ''
    const epoch = row.epoch ?? epochOf(row.time)
    insert.run(row.kind, row.project, session, row.time, epoch, row.type ?? '', row.title ?? '', row.summary ?? '',
      row.text, row.tokens ?? 0, row.source ?? 'wizardry', hash)
    return Number(find.get(row.kind, row.project, session, hash).id)
  }

  const transaction = (work) => {
    db.exec('BEGIN IMMEDIATE')
    try {
      const result = work()
      db.exec('COMMIT')
      return result
    } catch (error) {
      db.exec('ROLLBACK')
      throw error
    }
  }

  const marks = (items) => items.map(() => '?').join(', ')

  return {
    file,
    add,
    addAll: (rows) => transaction(() => rows.map(add)),

    /** The memories with these ids, in the order asked for. */
    byIds(ids) {
      if (!ids.length) return []
      const rows = db.prepare(`SELECT ${COLUMNS} FROM memories WHERE id IN (${marks(ids)})`).all(...ids)
      const byId = new Map(rows.map((row) => [Number(row.id), row]))
      return ids.map((id) => byId.get(Number(id))).filter(Boolean)
    },

    /** A project's observations not yet folded into topics, newest first. */
    pool(project) {
      return db.prepare(`SELECT ${COLUMNS} FROM memories WHERE kind = 'observation' AND project = ? AND folded = 0
        ORDER BY epoch DESC, id DESC`).all(project)
    },

    fold(ids) {
      if (ids.length) db.prepare(`UPDATE memories SET folded = 1 WHERE id IN (${marks(ids)})`).run(...ids)
    },

    /** A project's topics, the most recently written first. */
    topics(project) {
      return db.prepare(`SELECT ${COLUMNS} FROM memories WHERE kind = 'topic' AND project = ? ORDER BY epoch DESC, id DESC`).all(project)
    },

    /** Write a topic, replacing the one filed under the same name. */
    putTopic(project, topic, at = Date.now()) {
      const existing = find.get('topic', project, '', topic.slug)
      if (existing) {
        db.prepare('UPDATE memories SET title = ?, summary = ?, text = ?, tokens = ?, time = ?, epoch = ? WHERE id = ?')
          .run(topic.title, topic.summary, topic.body, topic.tokens, minute(at), at, existing.id)
        return Number(existing.id)
      }
      return add({ kind: 'topic', project, time: minute(at), epoch: at, type: topic.slug, title: topic.title,
        summary: topic.summary, text: topic.body, tokens: topic.tokens, hash: topic.slug })
    },

    journey(project) {
      return db.prepare(`SELECT ${COLUMNS} FROM memories WHERE kind = 'journey' AND project = ?`).get(project)
    },

    putJourney(project, text, tokens, at = Date.now()) {
      const existing = find.get('journey', project, '', 'journey')
      if (existing) {
        db.prepare('UPDATE memories SET text = ?, tokens = ?, time = ?, epoch = ? WHERE id = ?').run(text, tokens, minute(at), at, existing.id)
        return Number(existing.id)
      }
      return add({ kind: 'journey', project, time: minute(at), epoch: at, title: 'Journey', text, tokens, hash: 'journey' })
    },

    /** Memories matching `match` (an FTS query, best first), or the most recent when there is none. */
    search({ match, project, kind, limit = 10 }) {
      const where = []
      const args = []
      if (project) { where.push('m.project = ?'); args.push(project) }
      if (kind) { where.push('m.kind = ?'); args.push(kind) }
      const columns = COLUMNS.split(', ').map((column) => `m.${column}`).join(', ')
      if (match) {
        return db.prepare(`SELECT ${columns} FROM memories_fts f JOIN memories m ON m.id = f.rowid
          WHERE memories_fts MATCH ? ${where.map((clause) => `AND ${clause}`).join(' ')}
          ORDER BY bm25(memories_fts, 4.0, 2.0, 1.0), m.epoch DESC LIMIT ?`).all(match, ...args, limit)
      }
      return db.prepare(`SELECT ${columns} FROM memories m ${where.length ? `WHERE ${where.join(' AND ')}` : ''}
        ORDER BY m.epoch DESC, m.id DESC LIMIT ?`).all(...args, limit)
    },

    /** What a project's memory held just before and just after one memory, oldest first, the memory included. */
    around(id, before, after) {
      const anchor = db.prepare(`SELECT ${COLUMNS} FROM memories WHERE id = ?`).get(id)
      if (!anchor) return undefined
      const timed = `kind IN ('observation', 'prompt') AND project = ?`
      const earlier = db.prepare(`SELECT ${COLUMNS} FROM memories WHERE ${timed} AND (epoch < ? OR (epoch = ? AND id < ?))
        ORDER BY epoch DESC, id DESC LIMIT ?`).all(anchor.project, anchor.epoch, anchor.epoch, anchor.id, before).reverse()
      const later = db.prepare(`SELECT ${COLUMNS} FROM memories WHERE ${timed} AND (epoch > ? OR (epoch = ? AND id > ?))
        ORDER BY epoch ASC, id ASC LIMIT ?`).all(anchor.project, anchor.epoch, anchor.epoch, anchor.id, after)
      return { anchor, rows: [...earlier, anchor, ...later] }
    },

    /** Every memory, by project and then in the order it was made. */
    all() {
      return db.prepare(`SELECT ${COLUMNS} FROM memories ORDER BY project, epoch, id`).all()
    },

    /** Write the whole store to `to` as a database of its own, complete as of now. */
    snapshot(to) {
      db.prepare('VACUUM INTO ?').run(to)
    },

    counts(project) {
      const rows = db.prepare(`SELECT kind, COUNT(*) AS n FROM memories ${project ? 'WHERE project = ?' : ''} GROUP BY kind`)
        .all(...(project ? [project] : []))
      return Object.fromEntries(rows.map((row) => [row.kind, Number(row.n)]))
    },

    meta: (key) => getMeta.get(key)?.value,
    setMeta: (key, value) => { setMeta.run(key, String(value)) },

    /** Take a job only one process may do at a time. A holder silent for `staleMs` has died. */
    claim(key, staleMs = 10 * 60_000) {
      return transaction(() => {
        const held = Number(getMeta.get(key)?.value ?? 0)
        if (held && Date.now() - held < staleMs) return false
        setMeta.run(key, String(Date.now()))
        return true
      })
    },
    release: (key) => { db.prepare('DELETE FROM meta WHERE key = ?').run(key) },

    /**
     * Bring over what claude-mem (https://github.com/thedotmack/claude-mem) remembered, once:
     * its observations, session summaries and prompts stay searchable here. Its file is only read.
     */
    async importClaudeMem(path, size) {
      if (getMeta.get('imported:claude-mem') || !existsSync(path)) return 0
      const old = new DatabaseSync(path, { readOnly: true })
      const rows = []
      const all = (sql) => {
        try { return old.prepare(sql).all() } catch { return [] }
      }
      const lines = (json) => {
        try {
          const parsed = JSON.parse(json)
          return Array.isArray(parsed) ? parsed.join('\n') : ''
        } catch {
          return ''
        }
      }
      try {
        for (const o of all('SELECT * FROM observations')) {
          const text = [o.subtitle, o.narrative, lines(o.facts), o.text].filter(Boolean).join('\n')
          if (!text.trim() && !o.title) continue
          rows.push({ kind: 'observation', project: o.project, session: o.memory_session_id, time: minute(o.created_at_epoch),
            epoch: o.created_at_epoch, type: o.type || 'discovery', title: o.title || '', text: text || o.title, folded: 1 })
        }
        for (const s of all('SELECT * FROM session_summaries')) {
          const text = [['Request', s.request], ['Investigated', s.investigated], ['Learned', s.learned], ['Completed', s.completed],
            ['Next steps', s.next_steps], ['Notes', s.notes]].filter(([, value]) => value).map(([label, value]) => `${label}: ${value}`).join('\n')
          if (!text) continue
          rows.push({ kind: 'observation', project: s.project, session: s.memory_session_id, time: minute(s.created_at_epoch),
            epoch: s.created_at_epoch, type: 'discovery', title: s.request || 'Session summary', text, folded: 1 })
        }
        const prompts = all(`SELECT p.*, s.project AS project FROM user_prompts p LEFT JOIN sdk_sessions s ON s.id = p.session_db_id`)
        for (const p of prompts) {
          if (!String(p.prompt_text ?? '').trim()) continue
          rows.push({ kind: 'prompt', project: p.project || 'unknown', session: p.content_session_id, time: minute(p.created_at_epoch),
            epoch: p.created_at_epoch, text: p.prompt_text })
        }
      } finally {
        old.close()
      }
      transaction(() => {
        for (const row of rows) {
          const id = add({ ...row, tokens: size(row.text), source: 'claude-mem' })
          // What came from claude-mem is history: it does not join the pool waiting to be folded.
          if (row.folded) db.prepare('UPDATE memories SET folded = 1 WHERE id = ?').run(id)
        }
        setMeta.run('imported:claude-mem', String(Date.now()))
      })
      return rows.length
    },

    close() {
      try { db.close() } catch {}
    },
  }
}
