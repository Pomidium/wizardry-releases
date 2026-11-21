# division's decisions, in Bend.
#
# A large task is cut in two, each half is handed to its own agent, and a half that is still large
# is cut again. What keeps the agents out of each other's way is decided here: which files each may
# write, which laws each must prove, and whether a cut is worth making at all. index.js asks these
# defs and then starts the agents; LAWS.bend states what must hold of them and PROOF.bend proves it.
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

# One half of a cut: what it is called, the files it owns, the laws it must prove, and how many
# minutes of work the agent making the cut takes it to be.
type Piece is Data:
  Piece{name: String, owns: List<&2, String>, laws: List<&2, String>, minutes: Nat}

type Reason is Data:
  TooDeep{}
  TooSmall{}
  NoFiles{}
  NoLaws{}
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

# Whether a task is cut in two here. It is not when the tree is `limit` deep already, when either
# half is under `chunk` minutes (an agent costs more to start than that saves), when a half owns no
# file or has no law to prove (nothing would check its work), when a law is given to both, when a
# half owns what the agent cutting does not, or when the halves own a file in common.
def judge(depth: Nat, limit: Nat, +chunk: Nat, +parent: Owns, first: Piece, second: Piece) -> Verdict:
  match first second:
    case Piece{n1, +o1, +l1, m1} Piece{n2, +o2, +l2, m2}:
      guard(Bool.not(Nat.is_lt(depth, limit)), TooDeep{},
        guard(Bool.not(Bool.and(Nat.is_ge(m1, chunk), Nat.is_ge(m2, chunk))), TooSmall{},
          guard(Bool.or(List.is_empty(&2, String, o1), List.is_empty(&2, String, o2)), NoFiles{},
            guard(Bool.or(List.is_empty(&2, String, l1), List.is_empty(&2, String, l2)), NoLaws{},
              guard(String.eq(n1, n2), SameName{},
                guard(C.overlaps(l1, l2), SharedLaw{},
                  guard(Bool.not(Bool.and(inside(o1, parent), inside(o2, parent))), Outside{},
                    guard(overlap(o1, o2), Trample{},
                      Divide{}))))))))

# What the halves run on
# ----------------------

# What a half runs on: what the user chose with /division, and otherwise what the session is on.
def runs_on(+choice: String, session: String) -> String:
  Bool.pick(String, String.is_empty(choice), session, choice)

# The choice that is kept: "same" is no choice, the halves follow the session again.
def kept(+value: String) -> String:
  Bool.pick(String, String.eq(value, "same"), "", value)

# The thinking levels a half can be given, and "same".
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

def why(reason: Reason, chunk: Nat, depth: Nat) -> String:
  match reason:
    case TooDeep{}:
      String.concat(["this task has already been cut ", Nat.show(depth), " times on the way here"])
    case TooSmall{}:
      String.concat(["a half under ", Nat.show(chunk), " minutes of work is not worth an agent of its own"])
    case NoFiles{}:
      "each half needs at least one file or folder that is its own"
    case NoLaws{}:
      "each half needs at least one law to prove, or nothing checks its work"
    case SameName{}:
      "the halves need different names"
    case SharedLaw{}:
      "a law was given to both halves; every law has one prover"
    case Outside{}:
      "a half was given a file that is not yours to hand out"
    case Trample{}:
      "the halves were given a file in common, or one a folder that holds the other's file"

def refused(why: String) -> String:
  String.concat(["Not divided: ", why, ". Nothing was started. Do this task yourself, or cut it differently."])

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

# A half's state, in a word or two, while the other is still working.
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

# What the agent that cut is told of one half.
def half_report(name: String, owns: List<&2, String>, laws: List<&2, String>, ended: Ended, ms: Nat, out: String, err: String) -> String:
  String.concat(["## ", name, ": ", how(ended, ms), "\nOwned: ", String.join(owns, ", "), "\nLaws: ", String.join(laws, ", "),
    "\n\n", clip(first_said(out, err), 6000n)])

# Whether the halves fit: the check ended well, was not stopped, and no proof failed.
def fits(ended: Ended, +said: String) -> Bool:
  match ended:
    case Ended{code, stopped}:
      Bool.and(Nat.is_eq(code, 0n), Bool.and(String.is_empty(stopped), Bool.not(String.contains(said, "SOME PROOFS FAIL"))))

def check_said(fit: Bool, +stopped: String) -> String:
  match fit:
    case True{}:
      "It passes: the halves fit."
    case False{}:
      String.concat(["It FAILS", Bool.pick(String, String.is_empty(stopped), "", String.concat([" (", stopped, ")"])),
        ": the halves do not fit yet. Repair it yourself if it is small; if a law was wrong, change it and cut again."])

# What the agent that cut is told when both halves are back.
def joined(ms: Nat, reports: List<&2, String>, check: String, fit: Bool, stopped: String, +said: String) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["Both halves are back after ", minutes(ms), ". Every file is yours again."]), ""],
    reports,
    ["", String.append("## The check: ", check), check_said(fit, stopped),
      clip(Bool.pick(String, String.is_empty(said), "(no output)", said), 4000n)]]), "\n")

def stopped_early() -> String:
  "Stopped: both halves were ended before they finished. What they wrote so far is in their files."

def not_yours(path: String, name: String, owns: List<&2, String>) -> String:
  String.concat(["\"", path, "\" is not yours to write: your half (\"", name, "\") owns ", String.join(owns, ", "),
    ". If the task cannot be done without it, stop and say so in your reply."])

def option(flag: String, +value: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(value), Nil{}, [flag, value])

# The options a half is started with, so that it runs on the user's choice, or else on what the
# session is on.
def half_args(model: String, session_model: String, thinking: String, session_thinking: String) -> List<&2, String>:
  List.append(&2, String, option("--model", runs_on(model, session_model)), option("--thinking", runs_on(thinking, session_thinking)))

def showing_line(what: String, +choice: String, session: String) -> String:
  +on = runs_on(choice, session)
  String.concat(["  ", what, ": ", Bool.pick(String, String.is_empty(on), "Pi's default", on),
    Bool.pick(String, String.is_empty(choice), " (the same as this session)", " (chosen)")])

# What /division shows.
def showing(model: String, session_model: String, thinking: String, session_thinking: String) -> String:
  String.join(["The agents division starts run on", showing_line("model", model, session_model),
    showing_line("thinking", thinking, session_thinking), "Change with /division model and /division thinking."], "\n")

def cuts(+depth: Nat) -> String:
  String.concat([Nat.show(depth), " cut", Bool.pick(String, Nat.is_eq(depth, 1n), "", "s")])

# What a half is told of where it stands; nothing for the agent with the whole task.
type Place is Data:
  Whole{}
  Half{depth: Nat, name: String, owns: List<&2, String>, laws: List<&2, String>, check: String}

def standing(place: Place) -> List<&2, String>:
  match place:
    case Whole{}:
      ["You have the whole task: every file is yours to hand out."]
    case Half{depth, name, owns, laws, check}:
      [ String.concat(["You are a half of a divided task, ", cuts(depth), " down: \"", name, "\"."]),
        String.append("Files you own: ", String.join(owns, ", ")),
        String.append("Laws you must prove: ", String.join(laws, ", ")),
        String.append("The check: ", check)]

# The method: what `division` returns.
def method(+chunk: Nat, depth: Nat, place: Place) -> String:
  String.join(List.concat(&2, String, [
    ["DIVISION: a large task cut in two, each half done by its own agent at the same time.", ""],
    standing(place),
    [ "",
      "When to cut",
      String.concat(["- Only when you take each half to be at least ", Nat.show(chunk), " minutes of work for an agent, and the"]),
      "  place where the halves meet can be said exactly, as Bend laws. Otherwise do the task yourself:",
      "  a cut costs a planning step and two agents starting from nothing.",
      "- Not when the work is finding something out (a bug, a design, how a library behaves), and not",
      "  when the halves would each need most of what the other makes. Cut where little crosses.",
      "",
      "How to cut",
      "1. Write the laws at the cut, in a .bend file you own, before anything else (call `bend` for the",
      "   language). A `law` with only a type is a signature: it says what one half provides. A `law`",
      "   with an equation says what the other half may count on. Example, in LAWS.bend:",
      "       law double:            # the first half provides this",
      "         for x: Nat",
      "         Nat",
      "       law double_even:       # and the second half may count on this",
      "         for +x: Nat",
      "         {even(double(x)) == True{} : Bool}",
      "2. Give each half files of its own, and create them: a half fills a law from its own file, with",
      "   `import ./LAWS.bend as L` and `def L.double(x): ...`. Work flows one way: the half that uses",
      "   the other's defs imports the other's file, never both ways.",
      "3. Make one file the gate (PROOF.bend) that imports the laws and every half's files, so that",
      "   `bend PROOF.bend` prints ALL PROOFS CHECK only when every law at every cut is proven.",
      "4. Call `division_split` with the two halves. Both run now, in this directory, and you get",
      "   their reports and the result of the check when both are done.",
      "",
      "What holds while the halves work (proven in division's LAWS.bend)",
      "- A half may write only the files it was handed, and no file is handed to both.",
      "- A half may count on every law at the cut, proven or not: the other half is proving it now.",
      "  Until it has, the checker reports that def as missing; that is expected.",
      "- A half does not change a law. If one cannot be proven as written, it stops and says why, and",
      "  the agent that cut decides: that is you, for your own cut.",
      String.concat(["- A half that finds divisible work in what it was handed cuts again, and so do its halves, up to ", Nat.show(depth), " cuts deep:"]),
      "  whoever holds work that passes \"When to cut\" splits it instead of doing both parts in a row.",
      "",
      "When the halves are back",
      "- Every file is yours again. If the check fails, read what each half said: repair it yourself",
      "  when it is small, change the law and cut again when the law was wrong."]]), "\n")

def whole_lines(+whole: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(whole), Nil{}, ["The whole task, so you know what yours is part of:", whole, ""])

# What a half is told. It starts from nothing, so everything it needs is here.
def brief(name: String, task: String, owns: List<&2, String>, laws: List<&2, String>,
  other: String, other_task: String, other_laws: List<&2, String>, whole: String, check: String, chunk: Nat) -> String:
  String.join(List.concat(&2, String, [
    [ "You are one half of a larger task that was cut in two. Another agent is doing the other half right now, in this same directory.",
      "",
      String.append("Your half: ", name),
      task,
      ""],
    whole_lines(whole),
    [ String.concat(["The other half (\"", other, "\"), which is not yours to do: ", other_task]),
      "",
      String.append("Files you own: ", String.join(owns, ", ")),
      "You may create and change only these (a name ending in \"/\" is a folder and everything in it). You may read anything. A write anywhere else is refused.",
      "",
      String.append("Laws you must prove: ", String.join(laws, ", ")),
      "They are declared in the .bend files here. Prove each with a def of the same name in a file you own (call the `bend` action first if you have not used Bend).",
      String.concat(["Laws the other half is proving: ", String.join(other_laws, ", "), ". Count on them as if they were proven, and on any signature among them as if it were written: until the other half is done the checker reports those defs as missing, which is expected and not yours to fix."]),
      "Do not change a law. If one of yours cannot be proven as written, or you need something no law gives you, stop and say exactly what and why.",
      "",
      String.append("Check your work with: ", check),
      String.concat(["Before you start, and again whenever the work turns out larger than it looked, look for a cut in your own half: if you find two parts of at least ", Nat.show(chunk), " minutes each that meet at something you can state as Bend laws, cut again (call `division` for how) instead of doing them in a row. The halves you start are told the same. Do it directly only when there is no such cut."]),
      "",
      "When you are done, reply with what you did, which of your laws are proven, and anything the agent that cut the task needs to know. That reply is all it will see of your work besides the files."]]), "\n")

def describe_division(+chunk: Nat) -> String:
  String.concat(["For a LARGE task only: one you take to be at least ", Nat.show(Nat.add(chunk, chunk)), " minutes of work, that cuts cleanly in two. ",
    "Division cuts it in two halves that separate agents do at the same time, held together by Bend laws written at the cut: ",
    "each half owns its own files, proves its own laws, and counts on the other's before they are proven. ",
    "Returns the method and where you stand in the tree. Do not call it for a small task, for one whose halves would each need ",
    "most of what the other makes, or for work that is finding something out: do those yourself."])

def describe_split(chunk: Nat) -> String:
  String.concat(["Cut the task you have in two and run both halves now, each as its own agent in this directory. Call `division` first for the method. ",
    "Write the laws at the cut before calling. Returns when both halves are done, with what each said and the result of the check. ",
    "Refused, with the reason, when a half is under ", Nat.show(chunk), " minutes of work, has no law to prove, or the halves share a file."])
