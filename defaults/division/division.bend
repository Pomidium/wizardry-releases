# division's decisions, in Bend.
#
# A task is cut into parts, each part is handed to its own agent, and a part may be cut again.
# What keeps the agents out of each other's way is decided here: which files each may write, which
# laws each must prove, and whether a cut can be made at all. How many parts there are and how
# large each is are the cutting agent's to judge, and nothing here refuses a cut for them.
# index.js asks these defs and then starts the agents; LAWS.bend states what must hold of them and
# PROOF.bend proves it.
#
# `npm run core` in wizardry checks the proofs and compiles this file to core.mjs.

import Base
import ../../bend/core.bend as C

# Who may write what
# ------------------

# A path is a file, or a folder and everything under it: a folder's entry ends in "/".
def is_folder(entry: String) -> Bool:
  String.ends_with(entry, "/")

# Whether owning `entry` is owning `path`.
def covers(+entry: String, +path: String) -> Bool:
  Bool.or(String.eq(entry, path), Bool.and(is_folder(entry), String.starts_with(path, entry)))

# Whether an agent that owns `entries` may write `path`.
def may_write(entries: List<&2, String>, +path: String) -> Bool:
  match entries:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(covers(h, path), may_write(t, path))

# What an agent may write: everything, when it was given the whole task, or only what it was handed.
type Owns is Data:
  All{}
  Only{entries: List<&2, String>}

def may(owns: Owns, +path: String) -> Bool:
  match owns:
    case All{}:
      True{}
    case Only{entries}:
      may_write(entries, path)

# Whether owning one of two entries is owning the other, or part of it.
def clash(+a: String, +b: String) -> Bool:
  Bool.or(covers(a, b), covers(b, a))

def clashes(+a: String, bs: List<&2, String>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(clash(a, h), clashes(a, t))

# Whether two agents would own a file in common.
def overlap(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(clashes(h, ys), overlap(t, ys))

# Whether everything in `entries` is the parent's to hand out.
def inside(entries: List<&2, String>, +parent: Owns) -> Bool:
  match entries:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(may(parent, h), inside(t, parent))

# Whether a cut is made
# ---------------------

# One part of a cut: what it is called, the files it owns, and the laws it must prove. Either
# list may be empty: a part that owns nothing only reads and reports, and a part with no law is
# checked by the check alone.
type Piece is Data:
  Piece{name: String, owns: List<&2, String>, laws: List<&2, String>}

def names_of(pieces: List<&2, Piece>) -> List<&2, String>:
  match pieces:
    case Nil{}:
      Nil{}
    case Con{Piece{name, owns, laws}, t}:
      name <> names_of(t)

def owns_of(pieces: List<&2, Piece>) -> List<&2, List<&2, String>>:
  match pieces:
    case Nil{}:
      Nil{}
    case Con{Piece{name, owns, laws}, t}:
      owns <> owns_of(t)

def laws_of(pieces: List<&2, Piece>) -> List<&2, String>:
  match pieces:
    case Nil{}:
      Nil{}
    case Con{Piece{name, owns, laws}, t}:
      List.append(&2, String, laws, laws_of(t))

# Whether no name is there twice.
def distinct(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(C.has(t, h)), distinct(t))

# Whether an agent that owns `mine` would own a file in common with any of the others.
def shares(+mine: List<&2, String>, others: List<&2, List<&2, String>>) -> Bool:
  match others:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(overlap(mine, h), shares(mine, t))

# Whether no two of the agents own a file in common.
def disjoint(owns: List<&2, List<&2, String>>) -> Bool:
  match owns:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(shares(h, t)), disjoint(t))

# Whether everything each agent is handed is the parent's to hand out.
def all_inside(owns: List<&2, List<&2, String>>, +parent: Owns) -> Bool:
  match owns:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(inside(h, parent), all_inside(t, parent))

def one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# How many of the agents may write `path`.
def writers(owns: List<&2, List<&2, String>>, +path: String) -> Nat:
  match owns:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(one_if(may_write(h, path)), writers(t, path))

type Reason is Data:
  TooDeep{}
  NoParts{}
  SameName{}
  SharedLaw{}
  Outside{}
  Trample{}

type Verdict is Data:
  Divide{}
  Refuse{why: Reason}

# `rest`, unless something is wrong.
def guard(bad: Bool, why: Reason, rest: Verdict) -> Verdict:
  match bad:
    case True{}:
      Refuse{why}
    case False{}:
      rest

def verdict(deep: Bool, none: Bool, names: Bool, laws: Bool, outside: Bool, trample: Bool) -> Verdict:
  guard(deep, TooDeep{},
    guard(none, NoParts{},
      guard(names, SameName{},
        guard(laws, SharedLaw{},
          guard(outside, Outside{},
            guard(trample, Trample{},
              Divide{}))))))

# Whether a task is cut here, into however many parts it was cut. How large a part should be and
# how many there are is the judgment of the agent that cuts. What is refused is only what would
# let agents undo each other or never end: two parts with one name, a law given to two, a file a
# part does not have to hand out, a file handed to two, and a tree already `limit` cuts deep.
def judge(depth: Nat, limit: Nat, +parent: Owns, +pieces: List<&2, Piece>) -> Verdict:
  verdict(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, Piece, pieces), Bool.not(distinct(names_of(pieces))),
    Bool.not(distinct(laws_of(pieces))), Bool.not(all_inside(owns_of(pieces), parent)), Bool.not(disjoint(owns_of(pieces))))

# What the agents run on
# ----------------------

# What a part's agent runs on: what the user chose with /default-agent or /division, and otherwise what the session is on.
def runs_on(+choice: String, session: String) -> String:
  Bool.pick(String, String.is_empty(choice), session, choice)

# The choice that is kept: "same" is no choice, the agents follow the session again.
def kept(+value: String) -> String:
  Bool.pick(String, String.eq(value, "same"), "", value)

# The thinking levels an agent can be given, and "same".
def levels() -> List<&2, String>:
  ["same", "off", "minimal", "low", "medium", "high", "xhigh", "max"]

# What /division was asked for.
type Wants is Data:
  Show{}
  Model{}
  Thinking{}
  Unclear{}

def wants_pick(empty: Bool, model: Bool, thinking: Bool) -> Wants:
  match empty model thinking:
    case True{} _ _:
      Show{}
    case False{} True{} _:
      Model{}
    case False{} False{} True{}:
      Thinking{}
    case False{} False{} False{}:
      Unclear{}

# By the first word after /division: nothing shows the choices, "model" and "thinking" set one.
def wants(+word: String) -> Wants:
  wants_pick(String.is_empty(word), String.eq(word, "model"), String.eq(word, "thinking"))

# Reading the codebase
# --------------------

def is_name_start(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Char.is_eq(c, '_'))

def is_name_char(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c), Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.'))))

def name_put(keep: Bool, c: Char, rest: String) -> String:
  match keep:
    case True{}:
      SCon{c, rest}
    case False{}:
      SNil{}

# The run of name characters `s` starts with.
def name_of(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      name_put(is_name_char(c), c, name_of(t))

def starts_name(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      is_name_start(c)

def starts_space(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_space(c)

# `law name:` at the start of a line declares a law; what follows `law` is taken from `after`.
def declared_in(+after: String) -> Maybe<&2, String>:
  +rest = String.trim_start(after)
  +name = name_of(rest)
  Bool.pick(Maybe<&2, String>,
    Bool.and(starts_space(after), Bool.and(starts_name(rest),
      String.starts_with(String.trim_start(String.drop(rest, String.length(name))), ":"))),
    Some{name}, None{})

# The law a line declares, if it declares one.
def law_on(+line: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(line, "law"), declared_in(String.drop(line, 3n)), None{})

def found_put(found: Maybe<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match found:
    case None{}:
      acc
    case Some{name}:
      name <> acc

# `acc` is what was found so far, backwards: a file may be long, so this is a tail call.
def laws_go(lines: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{h, t}:
      laws_go(t, found_put(law_on(h), acc))

# The names of the laws a Bend file declares, in order.
def laws_in(text: String) -> List<&2, String>:
  laws_go(C.lines(text), Nil{})

def slashed_put(back: Bool, c: Char, acc: String) -> String:
  match back:
    case True{}:
      SCon{'/', acc}
    case False{}:
      SCon{c, acc}

def slashed_go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, t}:
      slashed_go(t, slashed_put(Char.is_eq(c, '\\'), c, acc))

# A path with "/" between its names, whatever the system puts there.
def slashed(path: String) -> String:
  slashed_go(path, SNil{})

def entry_pick(outside: Bool, folder: Bool, +clean: String) -> Maybe<&2, String>:
  match outside folder:
    case True{} _:
      None{}
    case False{} True{}:
      Some{String.append(clean, "/")}
    case False{} False{}:
      Some{clean}

# A path as the laws take it, from where it is relative to the task: none when that is the task's
# own folder or outside it; a folder ends in "/".
def entry_of(+rel: String, absolute: Bool, folder: Bool) -> Maybe<&2, String>:
  entry_pick(Bool.or(String.is_empty(rel), Bool.or(String.starts_with(rel, ".."), absolute)), folder, slashed(rel))

# What is said
# ------------

def why(reason: Reason, depth: Nat) -> String:
  match reason:
    case TooDeep{}:
      String.concat(["this task has already been cut ", Nat.show(depth), " times on the way here; do this part yourself"])
    case NoParts{}:
      "no part was given"
    case SameName{}:
      "two parts have the same name"
    case SharedLaw{}:
      "a law was given to two parts; every law has one prover"
    case Outside{}:
      "a part was given a file that is not yours to hand out"
    case Trample{}:
      "two parts were given a file in common, or one a folder that holds another's file"

def refused(why: String) -> String:
  String.concat(["Not divided: ", why, ". Nothing was started. Cut it differently, or do the task yourself."])

def ticked(names: List<&2, String>) -> List<&2, String>:
  match names:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.concat(["`law ", h, "`"]) <> ticked(t)

def laws_missing(names: List<&2, String>) -> String:
  String.concat(["no .bend file here declares ", String.join(ticked(names), ", "), "; write the laws at the cut first"])

# The laws named that no file declares.
def missing(named: List<&2, String>, +declared: List<&2, String>) -> List<&2, String>:
  C.without(named, declared)

# A text cut to `max` characters, saying how many were left out.
def clip(+text: String, +max: Nat) -> String:
  Bool.pick(String, C.fits(text, max), text,
    String.concat([String.take(text, max), "\n... (", Nat.show(Nat.sub(String.length(text), max)), " more characters)"]))

# Milliseconds as minutes, to a tenth.
def minutes(ms: Nat) -> String:
  +tenths = Nat.div(Nat.add(ms, 3000n), 6000n)
  String.concat([Nat.show(Nat.div(tenths, 10n)), ".", Nat.show(Nat.mod(tenths, 10n)), " min"])

# How an agent or a check ended: stopped early (and why), or with the status it left.
type Ended is Data:
  Ended{code: Nat, stopped: String}

def state_pick(stopped: Bool, ok: Bool, why: String, code: Nat) -> String:
  match stopped ok:
    case True{} _:
      why
    case False{} True{}:
      "done"
    case False{} False{}:
      String.append("ended with status ", Nat.show(code))

# A part's state, in a word or two, while the others are still working.
def state(ended: Ended) -> String:
  match ended:
    case Ended{+code, +stopped}:
      state_pick(Bool.not(String.is_empty(stopped)), Nat.is_eq(code, 0n), stopped, code)

def how_pick(stopped: Bool, ok: Bool, why: String, code: Nat, +took: String) -> String:
  match stopped ok:
    case True{} _:
      String.concat([why, " after ", took])
    case False{} True{}:
      String.append("done in ", took)
    case False{} False{}:
      String.concat(["ended with status ", Nat.show(code), " after ", took])

def how(ended: Ended, ms: Nat) -> String:
  match ended:
    case Ended{+code, +stopped}:
      how_pick(Bool.not(String.is_empty(stopped)), Nat.is_eq(code, 0n), stopped, code, minutes(ms))

def first_said(+out: String, +err: String) -> String:
  Bool.pick(String, String.is_empty(out), Bool.pick(String, String.is_empty(err), "(it said nothing)", err), out)

def or_none(+text: String) -> String:
  Bool.pick(String, String.is_empty(text), "(none)", text)

# What the agent that cut is told of one part.
def half_report(name: String, owns: List<&2, String>, laws: List<&2, String>, ended: Ended, ms: Nat, out: String, err: String) -> String:
  String.concat(["## ", name, ": ", how(ended, ms), "\nOwned: ", or_none(String.join(owns, ", ")), "\nLaws: ", or_none(String.join(laws, ", ")),
    "\n\n", clip(first_said(out, err), 6000n)])

# Whether the parts fit: the check ended well, was not stopped, and no proof failed.
def fits(ended: Ended, +said: String) -> Bool:
  match ended:
    case Ended{code, stopped}:
      Bool.and(Nat.is_eq(code, 0n), Bool.and(String.is_empty(stopped), Bool.not(String.contains(said, "SOME PROOFS FAIL"))))

def check_said(fit: Bool, +stopped: String) -> String:
  match fit:
    case True{}:
      "It passes: the parts fit."
    case False{}:
      String.concat(["It FAILS", Bool.pick(String, String.is_empty(stopped), "", String.concat([" (", stopped, ")"])),
        ": the parts do not fit yet. Repair it yourself if it is small; if a law was wrong, change it and cut again."])

def check_lines(none: Bool, check: String, fit: Bool, stopped: String, +said: String) -> List<&2, String>:
  match none:
    case True{}:
      ["## No check was given", "Whether the parts fit is yours to see: read what each said, and what is in the files."]
    case False{}:
      [String.append("## The check: ", check), check_said(fit, stopped),
        clip(Bool.pick(String, String.is_empty(said), "(no output)", said), 4000n)]

# Strays
# ------
#
# The write tools refuse a part a file that is not its own; a command it runs is not fenced. So
# when the parts are back, every file changed since the cut is looked at: one that no part owns
# is a stray, and the agent that cut is told, since nobody answers for it.
def stray(owns: List<&2, List<&2, String>>, +path: String) -> Bool:
  Nat.is_eq(writers(owns, path), 0n)

def stray_put(yes: Bool, path: String, rest: List<&2, String>) -> List<&2, String>:
  match yes:
    case True{}:
      path <> rest
    case False{}:
      rest

def strays(changed: List<&2, String>, +owns: List<&2, List<&2, String>>) -> List<&2, String>:
  match changed:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      stray_put(stray(owns, h), h, strays(t, owns))

# `looked` is false when the folder was too large to look through: that is said, not passed over.
def stray_lines(looked: Bool, found: List<&2, String>) -> List<&2, String>:
  match looked found:
    case False{} _:
      ["Not looked at: whether a part changed a file outside its own (the folder is too large to look through).", ""]
    case True{} Nil{}:
      Nil{}
    case True{} Con{h, t}:
      [String.concat(["CHANGED OUTSIDE EVERY PART'S FILES (by a command, not the write tools): ", String.join(h <> t, ", "),
        ". No part owned these: look at each before you count on it."]), ""]

# What the agent that cut is told when every part is back.
def joined(ms: Nat, reports: List<&2, String>, looked: Bool, strayed: List<&2, String>, +check: String, fit: Bool, stopped: String, said: String) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["Every part is back after ", minutes(ms), ". Every file is yours again."]), ""],
    reports,
    [""],
    stray_lines(looked, strayed),
    check_lines(String.is_empty(check), check, fit, stopped, said)]), "\n")

def stopped_early() -> String:
  "Stopped: the parts were ended before they finished. What they wrote so far is in their files."

def not_yours(path: String, name: String, owns: List<&2, String>) -> String:
  String.concat(["\"", path, "\" is not yours to write: your part (\"", name, "\") owns ", or_none(String.join(owns, ", ")),
    ". If the task cannot be done without it, stop and say so in your reply."])

def option(flag: String, +value: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(value), Nil{}, [flag, value])

# The options a part's agent is started with, so that it runs on the user's choice, or else on what the
# session is on.
def half_args(model: String, session_model: String, thinking: String, session_thinking: String) -> List<&2, String>:
  List.append(&2, String, option("--model", runs_on(model, session_model)), option("--thinking", runs_on(thinking, session_thinking)))

def showing_line(what: String, +choice: String, session: String) -> String:
  +on = runs_on(choice, session)
  String.concat(["  ", what, ": ", Bool.pick(String, String.is_empty(on), "Pi's default", on),
    Bool.pick(String, String.is_empty(choice), " (the same as this session)", " (chosen)")])

# What /division and /default-agent show.
def showing(model: String, session_model: String, thinking: String, session_thinking: String) -> String:
  String.join(["The agents you deploy run on", showing_line("model", model, session_model),
    showing_line("thinking", thinking, session_thinking),
    "/default-agent makes this session's model and thinking level theirs; /default-agent same follows each session again."], "\n")

# What /default-agent was asked for: nothing takes the session's setup, "same" takes the choice
# back, and anything else names a model.
type Agent is Data:
  Current{}
  Follow{}
  Named{}

def agent_pick(empty: Bool, same: Bool) -> Agent:
  match empty same:
    case True{} _:
      Current{}
    case False{} True{}:
      Follow{}
    case False{} False{}:
      Named{}

def agent_wants(+word: String) -> Agent:
  agent_pick(String.is_empty(word), String.eq(word, "same"))

def cuts(+depth: Nat) -> String:
  String.concat([Nat.show(depth), " cut", Bool.pick(String, Nat.is_eq(depth, 1n), "", "s")])

# What a part is told of where it stands; nothing for the agent with the whole task.
type Place is Data:
  Whole{}
  Half{depth: Nat, name: String, owns: List<&2, String>, laws: List<&2, String>, check: String}

def standing(place: Place) -> List<&2, String>:
  match place:
    case Whole{}:
      ["You have the whole task: every file is yours to hand out."]
    case Half{depth, name, owns, laws, check}:
      [ String.concat(["You are a part of a divided task, ", cuts(depth), " down: \"", name, "\"."]),
        String.append("Files you own: ", or_none(String.join(owns, ", "))),
        String.append("Laws you must prove: ", or_none(String.join(laws, ", "))),
        String.append("The check: ", or_none(check))]

# The method: what `division` returns. It is a way of working, not a set of limits: how many
# parts, how large, and whether to cut at all are the agent's to judge.
def method(place: Place) -> String:
  String.join(List.concat(&2, String, [
    ["DIVISION: a task cut into parts, each done by its own agent at the same time.", ""],
    standing(place),
    [ "",
      "When it helps",
      "- When the parts can go on at the same time without waiting for each other, and what one needs",
      "  of another can be said plainly beforehand. Cut where little crosses.",
      "- An agent starts from nothing and costs a start, so a part should be worth one. How many parts",
      "  and how large is yours to judge: two, five, one for the part you would rather not hold in",
      "  your own context. Work you can simply do is done faster by doing it.",
      "- A part that owns no file only reads and reports: finding something out can be a part too.",
      "",
      "How to cut",
      "1. Give each part a name, a task said in full, and the files that are its own. Create the files",
      "   or folders first if that makes the cut clearer. No file may be in two parts.",
      "2. Say what crosses between parts. The strongest way is Bend laws in a file you keep (call",
      "   `bend` for the language): a `law` with only a type is a signature one part provides, a `law`",
      "   with an equation is what the others may count on, and each law is given to the one part",
      "   that proves it, in a file of its own (`import ./LAWS.bend as L`, `def L.name(..): ...`).",
      "   Where laws do not fit the work (prose, configuration, another language), say it in the tasks",
      "   and give a check that tells whether the parts fit: a test run, a build, a script.",
      "3. Call `division_split` with the parts. They all run now, in this directory, and you get each",
      "   one's report and the result of the check when all are back.",
      "",
      "What holds while the parts work (proven in division's LAWS.bend)",
      "- A part may write only the files it was handed, and no file is handed to two.",
      "- A part may count on every law at the cut, proven or not: another part is proving it now.",
      "  Until it has, the checker reports that def as missing; that is expected.",
      "- A part does not change a law. If one cannot be proven as written, it stops and says why, and",
      "  the agent that cut decides: that is you, for your own cut.",
      "- A part may cut again among its own files, and so may its parts.",
      "",
      "When the parts are back",
      "- Every file is yours again. If the check fails, read what each part said: repair it yourself",
      "  when it is small, change what crosses and cut again when that was wrong."]]), "\n")

def whole_lines(+whole: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(whole), Nil{}, ["The whole task, so you know what yours is part of:", whole, ""])

# Another part of the same cut, as a part is told of it.
type Other is Data:
  Other{name: String, task: String, laws: List<&2, String>}

def other_lines(others: List<&2, Other>) -> List<&2, String>:
  match others:
    case Nil{}:
      Nil{}
    case Con{Other{name, task, +laws}, t}:
      String.concat(["- \"", name, "\": ", task, Bool.pick(String, List.is_empty(&2, String, laws), "", String.append(" It proves: ", String.join(laws, ", ")))])
        <> other_lines(t)

def others_part(others: List<&2, Other>) -> List<&2, String>:
  match others:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.concat(&2, String, [["The other parts, which are not yours to do and are being done right now in this same directory:"], other_lines(h <> t), [""]])

def owns_part(owns: List<&2, String>) -> List<&2, String>:
  match owns:
    case Nil{}:
      ["You own no file: read whatever you need, write nothing, and put what you find in your reply.", ""]
    case Con{h, t}:
      [ String.append("Files you own: ", String.join(h <> t, ", ")),
        "You may create and change only these (a name ending in \"/\" is a folder and everything in it). You may read anything. A write anywhere else is refused.",
        ""]

def laws_part(laws: List<&2, String>) -> List<&2, String>:
  match laws:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      [ String.append("Laws you must prove: ", String.join(h <> t, ", ")),
        "They are declared in the .bend files here. Prove each with a def of the same name in a file you own (call the `bend` action first if you have not used Bend).",
        "Laws another part is proving are named above: count on them as if they were proven, and on any signature among them as if it were written. Until that part is done the checker reports those defs as missing, which is expected and not yours to fix.",
        "Do not change a law. If one of yours cannot be proven as written, or you need something nothing gives you, stop and say exactly what and why.",
        ""]

def check_part(+check: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(check), Nil{}, [String.append("Check your work with: ", check)])

# What a part is told. It starts from nothing, so everything it needs is here.
def brief(name: String, task: String, owns: List<&2, String>, laws: List<&2, String>, others: List<&2, Other>, whole: String, check: String) -> String:
  String.join(List.concat(&2, String, [
    [ "You are one part of a larger task that was cut into parts, each done by its own agent.",
      "",
      String.append("Your part: ", name),
      task,
      ""],
    whole_lines(whole),
    others_part(others),
    owns_part(owns),
    laws_part(laws),
    check_part(check),
    [ "If your part turns out to hold work that would go faster as parts of its own, you may cut again among your files (call `division` for how). That is yours to judge.",
      "",
      "When you are done, reply with what you did, what is proven or checked, and anything the agent that cut the task needs to know. That reply is all it will see of your work besides the files."]]), "\n")

def describe_division() -> String:
  String.concat(["A way to deploy agents on a task: cut it into parts that separate agents do at the same time, each owning its own files, ",
    "with what crosses between parts said beforehand, best as Bend laws. ",
    "Returns the method and puts division_split in front of you from the next step. Whether to cut at all is yours to judge."])

def describe_split() -> String:
  String.concat(["Cut the task you have into parts and run them all now, each as its own agent in this directory. ",
    "Returns when every part is back, with what each said and the result of the check. ",
    "Refused, with the reason, only when two parts would own the same file, a part is handed a file that is not yours, a law is given to two parts, or two parts share a name."])
