# Export and delete: what an export holds, how a conversation reads in it, what `delete` may
# remove and when. Part of wizardry's decisions (../core.bend); compiled to core/keep.mjs.
# LAWS.bend and PROOF.bend here say what must hold.

import Base
import ../core.bend as C
import ../look/look.bend as L

# Paths
# -----

def with_slash(+dir: String) -> String:
  Bool.pick(String, String.ends_with(dir, "/"), dir, String.append(dir, "/"))

# Whether `path` is `root` or lies somewhere under it.
def inside(+path: String, +root: String) -> Bool:
  Bool.or(String.eq(path, root), String.starts_with(path, with_slash(root)))

# Whether deleting any of `paths` would take `keep` along.
def takes(paths: List<&2, String>, +keep: String) -> Bool:
  match paths:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(inside(keep, h), takes(t, keep))

# `paths`, or nothing at all when deleting them would take `keep` along.
def sparing(+paths: List<&2, String>, +keep: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, takes(paths, keep), Nil{}, paths)

def all_rooted(paths: List<&2, String>) -> Bool:
  match paths:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(String.starts_with(h, "/"), all_rooted(t))

# `paths`, or nothing at all unless every one of them is a full path.
def rooted(+paths: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, all_rooted(paths), paths, Nil{})

# `rev` is a path backwards: what holds it starts after the first slash met.
def parent_go(rev: String) -> String:
  match rev:
    case SNil{}:
      SNil{}
    case SCon{h, +t}:
      Bool.pick(String, Char.is_eq(h, '/'), String.reverse(t), parent_go(t))

# The directory a path is in.
def parent(path: String) -> String:
  parent_go(String.reverse(path))

def parents(paths: List<&2, String>) -> List<&2, String>:
  match paths:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      parent(h) <> parents(t)

# Export
# ------

# Where conversations are kept.
def sessions_dir(+home: String) -> String:
  C.in_dir(home, "sessions")

# Where an export goes: where the user said, else a folder in their home directory named for the
# day, and for which export of that day it is when the name is taken.
def export_dir(+chosen: String, userhome: String, day: String, +again: Nat) -> String:
  Bool.pick(String, String.is_empty(chosen),
    String.concat([userhome, "/wizardry-export-", day, Bool.pick(String, Nat.is_eq(again, 0n), "", String.append("-", Nat.show(1n+again)))]),
    chosen)

# A setup that keeps conversations, and where it keeps them.
type Origin is Data:
  Origin{name: String, dir: String}

# The conversations an export copies: wizardry's own, and those of Pi's own setup.
def origins(+home: String, +old: String) -> List<&2, Origin>:
  [Origin{"wizardry", sessions_dir(home)}, Origin{"pi", C.in_dir(old, "sessions")}]

def origin_dirs(origins: List<&2, Origin>) -> List<&2, String>:
  match origins:
    case Nil{}:
      Nil{}
    case Con{Origin{name, dir}, t}:
      dir <> origin_dirs(t)

# Whether an export may be written to `dir`: not into the very folders it copies from.
def export_fits(+dir: String, +home: String, +old: String) -> Bool:
  Bool.not(takes(origin_dirs(origins(home, old)), dir))

# Whether a file is a conversation.
def is_conversation(name: String) -> Bool:
  String.ends_with(name, ".jsonl")

# Where a conversation goes in an export: under the name of the setup it came from, at the path
# it had there.
def conversation_to(dir: String, origin: String, rel: String) -> String:
  String.append(dir, String.concat(["/conversations/", origin, "/", rel]))

# The file beside a conversation that holds it as text to read.
def readable(+path: String) -> String:
  Bool.pick(String, String.ends_with(path, ".jsonl"),
    String.append(String.take(path, Nat.sub(String.length(path), 6n)), ".md"), String.append(path, ".md"))

# A time to the minute: "2026-11-20 19:16:34" is "2026-11-20 19:16".
def minute(stamp: String) -> String:
  String.take(stamp, 16n)

def transcript_head(file: String, cwd: String, started: String) -> String:
  String.concat(["# Conversation of ", minute(started), "\n\n- Directory: ", cwd, "\n- Kept whole in: ", file, "\n\n"])

# How a piece of a conversation is written down.
type Voice is Data:
  Said{who: String}
  Call{}
  Result{}
  Ran{}
  Image{}
  Silent{}

# What each kind of piece is. Thinking, the system prompt and everything that is not conversation
# (model changes, what plugins note for themselves) are left to the .jsonl.
def voice_of(+kind: String) -> Voice:
  Bool.pick(Voice, String.eq(kind, "user"), Said{"User"},
    Bool.pick(Voice, String.eq(kind, "assistant"), Said{"Assistant"},
      Bool.pick(Voice, String.eq(kind, "toolCall"), Call{},
        Bool.pick(Voice, String.eq(kind, "toolResult"), Result{},
          Bool.pick(Voice, String.eq(kind, "bashExecution"), Ran{},
            Bool.pick(Voice, String.eq(kind, "image"), Image{},
              Bool.pick(Voice, C.has(["compaction", "branch_summary"], kind), Said{"Summary of what came before"},
                Bool.pick(Voice, String.eq(kind, "custom_message"), Said{"Note"},
                  Bool.pick(Voice, String.eq(kind, "error"), Said{"Error"}, Silent{})))))))))

def said_block(who: String, at: String, +body: String) -> String:
  Bool.pick(String, String.is_empty(body), "", String.concat(["## ", who, " · ", minute(at), "\n\n", body, "\n\n"]))

def more_lines(+more: Nat) -> String:
  Bool.pick(String, Nat.is_eq(more, 0n), "", String.concat(["\n    ... ", Nat.show(more), " more lines, in the .jsonl"]))

def shown_block(view: L.View) -> String:
  match view:
    case L.View{shown, more}:
      String.concat(["    ", String.join(shown, "\n    "), more_lines(more), "\n\n"])

# What a call came back with: its first lines, set apart as a block.
def result_block(text: String) -> String:
  shown_block(L.result_view(text, False{}))

def call_line(name: String, args: String) -> String:
  String.concat(["> **", name, "** ", C.clip(C.squash(args, False{}), 200n), "\n\n"])

def piece_as(voice: Voice, name: String, at: String, text: String) -> String:
  match voice:
    case Said{who}:
      said_block(who, at, String.trim_end(text))
    case Call{}:
      call_line(name, text)
    case Result{}:
      result_block(text)
    case Ran{}:
      String.append(call_line("$", name), result_block(text))
    case Image{}:
      "*(an image)*\n\n"
    case Silent{}:
      ""

# One piece of a conversation as text to read: what was said in full, a call on one line, what
# it came back with by its first lines. Empty for what is not written down.
def piece(kind: String, name: String, at: String, text: String) -> String:
  piece_as(voice_of(kind), name, at, text)

# How many conversations an export took from one setup.
type Tally is Data:
  Tally{name: String, from: String, count: Nat}

def tally_lines(tallies: List<&2, Tally>) -> List<&2, String>:
  match tallies:
    case Nil{}:
      Nil{}
    case Con{Tally{name, from, +count}, t}:
      C.keep_if(Bool.not(Nat.is_eq(count, 0n)),
        String.concat([C.counted(count, "conversation", "conversations"), " from ", from, ", in conversations/", name, "/"]), tally_lines(t))

def or_nothing(lines: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}:
      ["nothing: no conversation and no memory was found"]
    case Con{h, t}:
      h <> t

# The folders of wizardry's directory that are not a plugin's data: the program, the plugins,
# the conversations (copied one by one), Pi's directory, whose logins stay where they are, and
# the tools installed for plugins (`tools`, `bin`), which are programs and can be installed again.
def own_folders() -> List<&2, String>:
  ["app", "plugins", "sessions", "pi", "update.lock", "tools", "bin", "node"]

# A plugin that keeps data keeps it in a folder of wizardry's directory and exports it into a
# folder of the same name. The folders nobody exported are copied as they are, so that nothing
# kept is missing from an export because its plugin was switched off or does not export.
def left_over(folders: List<&2, String>, written: List<&2, String>) -> List<&2, String>:
  C.without(C.without(folders, own_folders()), written)

def left_over_line(name: String) -> String:
  String.concat([name, "/ as it was kept: no loaded plugin exported it"])

# What an export holds: the conversations taken from each setup, then what each plugin wrote.
def export_lines(tallies: List<&2, Tally>, wrote: List<&2, String>) -> List<&2, String>:
  or_nothing(List.append(&2, String, tally_lines(tallies), wrote))

# The note left in an export, saying what is in it.
def export_readme(day: String, +lines: List<&2, String>) -> String:
  String.concat(["# wizardry export of ", day, "\n\n",
    "Everything here is a copy: nothing was removed from where it was kept.\n\n",
    String.join(C.bulleted(lines), "\n"), "\n\n",
    "Each conversation is here twice. The `.jsonl` is the session exactly as it was kept, and\n",
    "`wizardry --session <that file>` carries it on. The `.md` beside it is the same conversation\n",
    "as text to read.\n"])

# What `wizardry export` says when it is done.
def export_said(dir: String, lines: List<&2, String>) -> String:
  String.concat(["exported to ", dir, ":\n", String.join(L.indented(lines), "\n"), "\n"])

def export_inside(dir: String) -> String:
  String.concat(["not exported: ", dir, " is inside the conversations it would copy. Name another folder."])

def export_taken(dir: String) -> String:
  String.concat(["not exported: ", dir, " is not empty. Name a new folder, so that nothing in it is overwritten."])

def export_broke(why: String) -> String:
  String.append("the export did not finish: ", why)

def export_usage() -> String:
  "usage: wizardry export [folder]"

# The command line of export and delete
# -------------------------------------

def is_option(arg: String) -> Bool:
  String.starts_with(arg, "-")

# The arguments that are neither options nor the value of --to. `value` is set while reading it.
def bare(argv: List<&2, String>, +value: Bool) -> List<&2, String>:
  match argv:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      C.keep_if(Bool.not(Bool.or(value, is_option(h))), h, bare(t, Bool.and(Bool.not(value), String.eq(h, "--to"))))

def options(argv: List<&2, String>) -> List<&2, String>:
  match argv:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      C.keep_if(is_option(h), h, options(t))

def first_of(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      h

# What follows `flag` among the arguments, or nothing.
def value_after(argv: List<&2, String>, +flag: String) -> String:
  match argv:
    case Nil{}:
      ""
    case Con{h, +t}:
      Bool.pick(String, String.eq(h, flag), first_of(t), value_after(t, flag))

# `wizardry export [folder]`: the folder asked for (empty for none), or nothing when unclear.
def export_asked(+argv: List<&2, String>) -> Maybe<&2, String>:
  +words = bare(argv, False{})
  Bool.pick(Maybe<&2, String>, Bool.and(List.is_empty(&2, String, options(argv)), Nat.is_lt(List.length(&2, String, words), 2n)),
    Some{first_of(words)}, None{})

# What `wizardry delete` was asked: what to delete, whether to go ahead, whether the export is
# waived, where the export goes, and whether all of that was clear.
type Removal is Data:
  Removal{what: String, yes: Bool, waived: Bool, to: String, clear: Bool}

def delete_asked(+argv: List<&2, String>) -> Removal:
  +words = bare(argv, False{})
  Removal{first_of(words), Bool.or(C.has(argv, "--yes"), C.has(argv, "-y")), C.has(argv, "--no-export"), value_after(argv, "--to"),
    Bool.and(Nat.is_eq(List.length(&2, String, words), 1n), C.covers(["--yes", "-y", "--no-export", "--to"], options(argv)))}

# Delete
# ------

# What can be deleted.
type What is Data:
  Conversations{}
  Memories{}
  Old{}
  All{}
  Unknown{}

def what_pick(conversations: Bool, memories: Bool, old: Bool, all: Bool) -> What:
  match conversations memories old all:
    case True{} _ _ _:
      Conversations{}
    case False{} True{} _ _:
      Memories{}
    case False{} False{} True{} _:
      Old{}
    case False{} False{} False{} True{}:
      All{}
    case False{} False{} False{} False{}:
      Unknown{}

def what_of(+word: String) -> What:
  what_pick(String.eq(word, "conversations"), String.eq(word, "memories"), String.eq(word, "old"), String.eq(word, "all"))

# Pi's own setup counts as old only when it is neither wizardry's directory nor inside it.
def old_wanted(+old: String, +home: String) -> List<&2, String>:
  sparing(Bool.pick(List<&2, String>, inside(old, home), Nil{}, [old]), home)

# `paths`, or nothing at all unless wizardry's directory is itself a full path.
def based(+home: String, paths: List<&2, String>) -> List<&2, String>:
  C.unless(Bool.not(String.starts_with(home, "/")), paths)

# What each word names: wizardry's conversations, its memories, Pi's own setup, or all of wizardry.
def wanted(what: What, +home: String, +old: String) -> List<&2, String>:
  match what:
    case Conversations{}:
      based(home, [sessions_dir(home)])
    case Memories{}:
      based(home, [C.in_dir(home, "memory")])
    case Old{}:
      based(home, old_wanted(old, home))
    case All{}:
      based(home, [home])
    case Unknown{}:
      Nil{}

# What `wizardry delete <what>` removes. It is nothing at all unless every path is a full one,
# and nothing at all when removing them would take the user's home directory along, or the
# export that was just made of them.
def doomed(what: What, +home: String, +old: String, +userhome: String, +to: String) -> List<&2, String>:
  sparing(sparing(rooted(wanted(what, home, old)), userhome), to)

# How an export asked for before a deletion ended.
type Exported is Data:
  Kept{}
  Failed{}
  Waived{}

# Of what would be removed, what is: all of it once the user said --yes and the export is kept
# (or was waived with --no-export), and otherwise nothing.
def goes(paths: List<&2, String>, yes: Bool, exported: Exported) -> List<&2, String>:
  match yes exported:
    case True{} Kept{}:
      paths
    case True{} Waived{}:
      paths
    case True{} Failed{}:
      Nil{}
    case False{} _:
      Nil{}

# The folders left empty by deleting Pi's own setup (~/.pi, once ~/.pi/agent is gone). They are
# removed only if empty, and never the user's home directory.
def emptied(what: What, doomed: List<&2, String>, +userhome: String) -> List<&2, String>:
  match what:
    case Old{}:
      sparing(rooted(parents(doomed)), userhome)
    case Conversations{}:
      Nil{}
    case Memories{}:
      Nil{}
    case All{}:
      Nil{}
    case Unknown{}:
      Nil{}

# A command on the PATH that is a link, and what it points to.
type Link is Data:
  Link{path: String, target: String}

# The links that would point at nothing once `doomed` is deleted. They go with it.
def dangling(links: List<&2, Link>, +doomed: List<&2, String>) -> List<&2, String>:
  match links:
    case Nil{}:
      Nil{}
    case Con{Link{path, target}, t}:
      C.keep_if(takes(doomed, target), path, dangling(t, doomed))

# Where commands that are links are looked for: beside the one wizardry was started by, where the
# installer puts them, and the link an old install left at ~/.izardry.
def link_dirs(invoked: String, named: String, userhome: String) -> List<&2, String>:
  C.without(C.add(C.add([parent(invoked)], named), String.append(userhome, "/.local/bin")), [""])

def old_home_link(userhome: String) -> String:
  String.append(userhome, "/.izardry")

def delete_usage() -> String:
  String.join([
    "usage: wizardry delete <what> [--yes] [--to <folder>] [--no-export]",
    "",
    "  conversations   every conversation wizardry has kept",
    "  memories        everything wizardry remembers",
    "  old             Pi's own setup, which wizardry no longer reads: its logins, settings,",
    "                  conversations, extensions and the pi program",
    "  all             all of wizardry: the program, its plugins, logins, conversations and memories",
    "",
    "Without --yes it says what would be deleted and deletes nothing. With --yes it first exports",
    "every conversation and memory (to --to <folder>, else ~/wizardry-export-<day>), and deletes",
    "only once that is done; --no-export skips the export.",
    ""], "\n")

def why_pick(unknown: Bool, based: Bool, none: Bool, loose: Bool, home: Bool, export: Bool, +old: String, +to: String) -> String:
  match unknown based none loose home export:
    case True{} _ _ _ _ _:
      "say what to delete: conversations, memories, old or all"
    case False{} False{} _ _ _ _:
      "nothing was deleted: wizardry's directory is not a full path"
    case False{} True{} True{} _ _ _:
      String.concat(["nothing to delete: Pi's own directory (", old, ") is wizardry's, inside it, or holds it, so it is not an old setup"])
    case False{} True{} False{} True{} _ _:
      String.concat(["nothing was deleted: ", old, " is not a full path"])
    case False{} True{} False{} False{} True{} _:
      "nothing was deleted: that would take your home directory along"
    case False{} True{} False{} False{} False{} True{}:
      String.concat(["nothing was deleted: the export would go to ", to, ", inside what is deleted. Name another folder with --to."])
    case False{} True{} False{} False{} False{} False{}:
      ""

def is_unknown(what: What) -> Bool:
  match what:
    case Unknown{}:
      True{}
    case Conversations{}:
      False{}
    case Memories{}:
      False{}
    case Old{}:
      False{}
    case All{}:
      False{}

# Why `wizardry delete <what>` removes nothing, or empty when it would remove something.
def why_not(+what: What, +home: String, +old: String, +userhome: String, +to: String) -> String:
  +paths = wanted(what, home, old)
  why_pick(is_unknown(what), String.starts_with(home, "/"), List.is_empty(&2, String, paths), Bool.not(all_rooted(paths)),
    takes(paths, userhome), takes(paths, to), old, to)

# A path that would be deleted, and how much is in it.
type Row is Data:
  Row{path: String, bytes: Nat}

def size_text(+bytes: Nat) -> String:
  Bool.pick(String, Nat.is_lt(bytes, 1000n), C.counted(bytes, "byte", "bytes"),
    Bool.pick(String, Nat.is_lt(bytes, 1000000n), String.append(Nat.show(Nat.div(bytes, 1000n)), " KB"),
      Bool.pick(String, Nat.is_lt(bytes, 1000000000n), String.append(Nat.show(Nat.div(bytes, 1000000n)), " MB"),
        String.append(Nat.show(Nat.div(bytes, 1000000000n)), " GB"))))

def row_lines(rows: List<&2, Row>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{Row{path, bytes}, t}:
      String.concat(["  ", path, "  (", size_text(bytes), ")"]) <> row_lines(t)

def link_lines(links: List<&2, String>) -> List<&2, String>:
  match links:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.concat(["  ", h, "  (a command that points into it)"]) <> link_lines(t)

def export_line(waived: Bool, to: String, first: String, then: String) -> String:
  match waived:
    case True{}:
      "Nothing is exported first: you said --no-export."
    case False{}:
      String.concat([first, to, then])

# What `wizardry delete <what>` says without --yes: what would go, and that nothing has.
def delete_preview(+word: String, rows: List<&2, Row>, links: List<&2, String>, to: String, +waived: Bool) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["wizardry delete ", word, " would delete:"])],
    row_lines(rows),
    link_lines(links),
    [export_line(waived, to, "First, every conversation and memory is exported to ", "."),
      String.concat(["Nothing has been deleted. To go ahead: wizardry delete ", word, " --yes", Bool.pick(String, waived, " --no-export", "")]),
      ""]]), "\n")

# What it says once it has deleted.
def deleted_said(rows: List<&2, Row>, links: List<&2, String>, to: String, waived: Bool) -> String:
  String.join(List.concat(&2, String, [
    ["deleted:"],
    row_lines(rows),
    link_lines(links),
    [export_line(waived, to, "Every conversation and memory was exported first, to ", "."), ""]]), "\n")

# What is said when what was named is not on this machine.
def nothing_there(what: What) -> String:
  match what:
    case Conversations{}:
      "nothing to delete: wizardry has kept no conversation"
    case Memories{}:
      "nothing to delete: wizardry remembers nothing"
    case Old{}:
      "nothing to delete: there is no setup of Pi's own on this machine"
    case All{}:
      "nothing to delete: wizardry's directory is not there"
    case Unknown{}:
      "nothing to delete"

def export_first_failed(why: String) -> String:
  String.concat(["nothing was deleted: the export did not finish (", why, "). Fix that, or pass --no-export to delete without one."])
