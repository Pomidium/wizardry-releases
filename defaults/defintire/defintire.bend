# defintire's decisions, in Bend.
#
# A definition says, in mathematical form, what a thing is: the objects it speaks of, the axioms
# that hold of them, and what does and does not fall under it. Criteria tie numbers to it, so that
# anything said to fall under the definition can be scored by how well it does what the definition
# says, and whatever can be scored can be improved one step at a time. What counts as a definition,
# how a reading becomes a score, when a score may be called verified, how ratings move after a
# comparison and which attempt a climb keeps are decided here. index.js asks these defs and then
# runs the verifiers, the judge and the agents; LAWS.bend states what must hold and PROOF.bend
# proves it.
#
# `npm run core` in wizardry checks the proofs and compiles this file to core.mjs.

import Base
import ../../bend/core.bend as C

# How a criterion is measured
# ---------------------------

# Exact: a command computes the very quantity the definition names. Proxy: a command computes
# something that stands in for it. Judged: a model reads the candidate and gives a number.
type How is Data:
  Exact{}
  Proxy{}
  Judged{}
  Unknown{}

def kind_pick(exact: Bool, proxy: Bool, judged: Bool) -> How:
  match exact proxy judged:
    case True{} _ _:
      Exact{}
    case False{} True{} _:
      Proxy{}
    case False{} False{} True{}:
      Judged{}
    case False{} False{} False{}:
      Unknown{}

def kind_of(+word: String) -> How:
  kind_pick(String.eq(word, "exact"), String.eq(word, "proxy"), String.eq(word, "judged"))

def is_exact(kind: How) -> Bool:
  match kind:
    case Exact{}:
      True{}
    case Proxy{}:
      False{}
    case Judged{}:
      False{}
    case Unknown{}:
      False{}

def all_exact(kinds: List<&2, How>) -> Bool:
  match kinds:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(is_exact(h), all_exact(t))

# Whether a score may be called verified: something was measured, all of it by exact criteria,
# and nothing the definition asks for was left unmeasured.
def verified(kinds: List<&2, How>, unmeasured: Nat) -> Bool:
  match kinds:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.and(Nat.is_eq(unmeasured, 0n), all_exact(h <> t))

# What counts as a definition
# ---------------------------

# One thing a number is tied to: its name, how it is measured, how much it weighs, the command
# that measures it (exact and proxy) and the rubric a judge reads (judged).
type Criterion is Data:
  Criterion{name: String, kind: String, weight: Nat, command: String, rubric: String}

def say_if(bad: Bool, text: String) -> List<&2, String>:
  match bad:
    case True{}:
      [text]
    case False{}:
      Nil{}

def needs_command(kind: How) -> Bool:
  match kind:
    case Exact{}:
      True{}
    case Proxy{}:
      True{}
    case Judged{}:
      False{}
    case Unknown{}:
      False{}

def needs_rubric(kind: How) -> Bool:
  match kind:
    case Judged{}:
      True{}
    case Exact{}:
      False{}
    case Proxy{}:
      False{}
    case Unknown{}:
      False{}

def is_unknown(kind: How) -> Bool:
  match kind:
    case Unknown{}:
      True{}
    case Exact{}:
      False{}
    case Proxy{}:
      False{}
    case Judged{}:
      False{}

def criterion_problems(c: Criterion) -> List<&2, String>:
  match c:
    case Criterion{+name, +kind, weight, command, rubric}:
      List.concat(&2, String, [
        say_if(String.is_empty(name), "a criterion has no name"),
        say_if(is_unknown(kind_of(kind)), String.concat(["criterion \"", name, "\" is \"", kind, "\": say exact, proxy or judged"])),
        say_if(Nat.is_eq(weight, 0n), String.concat(["criterion \"", name, "\" weighs nothing: give it a weight of 1 or more"])),
        say_if(Bool.and(needs_command(kind_of(kind)), String.is_empty(command)),
          String.concat(["criterion \"", name, "\" is ", kind, " and needs a command that prints its number"])),
        say_if(Bool.and(needs_rubric(kind_of(kind)), String.is_empty(rubric)),
          String.concat(["criterion \"", name, "\" is judged and needs a rubric: what 0 and what 100 look like"]))])

def criteria_problems(cs: List<&2, Criterion>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.append(&2, String, criterion_problems(h), criteria_problems(t))

def criterion_names(cs: List<&2, Criterion>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Criterion{name, kind, weight, command, rubric}, t}:
      name <> criterion_names(t)

def distinct(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(C.has(t, h)), distinct(t))

# What is missing from a definition, or nothing when it is one. A definition names what it
# defines and the question it answers, speaks of at least one object, states at least one axiom,
# shows something that falls under it and something that does not (a definition that excludes
# nothing defines nothing), and ties at least one number to itself.
def problems(name: String, answers: String, objects: Nat, axioms: Nat, examples: Nat, non_examples: Nat, +criteria: List<&2, Criterion>) -> List<&2, String>:
  List.concat(&2, String, [
    say_if(String.is_empty(name), "name what is being defined"),
    say_if(String.is_empty(answers), "say what question the definition answers: what one could not decide or measure without it"),
    say_if(Nat.is_eq(objects, 0n), "name at least one object the definition speaks of, with its type"),
    say_if(Nat.is_eq(axioms, 0n), "state at least one axiom: a condition that holds of exactly the things defined"),
    say_if(Nat.is_eq(examples, 0n), "give at least one example that falls under the definition"),
    say_if(Nat.is_eq(non_examples, 0n), "give at least one non-example: a definition that excludes nothing defines nothing"),
    say_if(List.is_empty(&2, Criterion, criteria), "tie at least one criterion to it, or nothing can be scored against it"),
    say_if(Bool.not(distinct(criterion_names(criteria))), "two criteria have the same name"),
    criteria_problems(criteria)])

def not_defined(what: List<&2, String>) -> String:
  String.concat(["Not a definition yet:\n- ", String.join(what, "\n- "), "\nNothing was saved."])

# From a reading to a score
# -------------------------

def unit(+x: F32) -> F32:
  Bool.pick(F32, Bool.and(F32.is_ge(x, 0.0), F32.is_le(x, 1.0)), x, 0.0)

def along(v: F32, +lo: F32, +hi: F32) -> F32:
  unit(F32.clamp(F32.div(F32.sub(v, lo), F32.sub(hi, lo)), 0.0, 1.0))

def turned(higher: Bool, +x: F32) -> F32:
  match higher:
    case True{}:
      x
    case False{}:
      F32.sub(1.0, x)

# Where a reading stands between the worst and the best the criterion allows, in thousandths:
# 0 at the worst or beyond it, 1000 at the best or beyond it. A range that is no range gives 0,
# and so does a reading that is not a number.
# Whether a reading is a number at all: not what a division by nothing leaves behind.
def real(+v: F32) -> Bool:
  Bool.or(F32.is_ge(v, 0.0), F32.is_lt(v, 0.0))

def position(+v: F32, +lo: F32, +hi: F32, higher: Bool) -> Nat:
  Nat.min(Bool.pick(Nat, Bool.and(F32.is_lt(lo, hi), real(v)), F32.to_nat(F32.round(F32.mul(1000.0, turned(higher, along(v, lo, hi))))), 0n), 1000n)

def real_only(found: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match found:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, F32>, real(v), Some{v}, None{})

def first_real(words: List<&2, String>) -> Maybe<&2, F32>:
  match words:
    case Nil{}:
      None{}
    case Con{+h, t}:
      Maybe.or(&2, F32, real_only(F32.read(h)), first_real(t))

# What a verifier measured: the first number on the last line it printed (`wc -c file` prints
# the count and then the name).
def reading(out: String) -> Maybe<&2, F32>:
  first_real(String.split(String.trim(C.last_said(String.lines(out), "")), ' '))

def digit_put(keep: Bool, c: Char, acc: String) -> String:
  match keep:
    case True{}:
      SCon{c, acc}
    case False{}:
      acc

# The first run of digits in a text. `done` is set once that run has ended.
def digit_run(s: String, +started: Bool, +done: Bool, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, t}:
      digit_run(t, Bool.or(started, Char.is_digit(c)), Bool.or(done, Bool.and(started, Bool.not(Char.is_digit(c)))),
        digit_put(Bool.and(Char.is_digit(c), Bool.not(done)), c, acc))

def capped(found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match found:
    case None{}:
      None{}
    case Some{n}:
      Some{Nat.mul(Nat.min(n, 100n), 10n)}

# What a judge gave: the first whole number in its reply, taken as out of 100, in thousandths.
def judged(reply: String) -> Maybe<&2, Nat>:
  capped(Nat.read(String.take(digit_run(reply, False{}, False{}, SNil{}), 6n)))

# One criterion as measured: how much it weighs, and where the candidate stands on it.
type Mark is Data:
  Mark{weight: Nat, at: Nat}

def weighed(marks: List<&2, Mark>) -> Nat:
  match marks:
    case Nil{}:
      0n
    case Con{Mark{weight, at}, t}:
      Nat.add(Nat.mul(weight, at), weighed(t))

def heft(marks: List<&2, Mark>) -> Nat:
  match marks:
    case Nil{}:
      0n
    case Con{Mark{weight, at}, t}:
      Nat.add(weight, heft(t))

# The score: the weighted mean of where the candidate stands, in thousandths; 0 with nothing measured.
def score(+marks: List<&2, Mark>) -> Nat:
  +all = heft(marks)
  Bool.pick(Nat, Nat.is_eq(all, 0n), 0n, Nat.div(weighed(marks), all))

# A score held under its gates. A gate is a criterion that stands for an axiom: something that
# fails it is not an instance, however well it does elsewhere, so the score cannot be higher
# than where the candidate stands on any gate.
def gated(score: Nat, gates: List<&2, Nat>) -> Nat:
  match gates:
    case Nil{}:
      score
    case Con{h, t}:
      Nat.min(gated(score, t), h)

# Ratings: one number per candidate, moved by comparisons
# -------------------------------------------------------

# What the higher rated of two gains by winning, by how far ahead it was: the Elo expectation
# with K = 32, as a table. Level, a win is worth 16; far ahead, a win was expected and is worth 1.
def favored_pick(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool) -> Nat:
  match b1 b2 b3 b4 b5 b6 b7:
    case True{} _ _ _ _ _ _:
      16n
    case False{} True{} _ _ _ _ _:
      14n
    case False{} False{} True{} _ _ _ _:
      12n
    case False{} False{} False{} True{} _ _ _:
      10n
    case False{} False{} False{} False{} True{} _ _:
      8n
    case False{} False{} False{} False{} False{} True{} _:
      5n
    case False{} False{} False{} False{} False{} False{} True{}:
      3n
    case False{} False{} False{} False{} False{} False{} False{}:
      1n

def favored(+ahead: Nat) -> Nat:
  favored_pick(Nat.is_lt(ahead, 25n), Nat.is_lt(ahead, 75n), Nat.is_lt(ahead, 125n), Nat.is_lt(ahead, 175n),
    Nat.is_lt(ahead, 250n), Nat.is_lt(ahead, 350n), Nat.is_lt(ahead, 500n))

type Ratings is Data:
  Ratings{first: Nat, second: Nat}

def least(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+least(ap, bp)

# `points` move from the second to the first, or as many as the second has.
def to_first(a: Nat, +b: Nat, +points: Nat) -> Ratings:
  Ratings{Nat.add(a, least(points, b)), Nat.sub(b, least(points, b))}

# `points` move from the first to the second, or as many as the first has.
def to_second(+a: Nat, b: Nat, +points: Nat) -> Ratings:
  Ratings{Nat.sub(a, least(points, a)), Nat.add(b, least(points, a))}

type Outcome is Data:
  First{}
  Second{}
  Draw{}

# The ratings after a comparison. `ahead` says whether the first was rated at least as high, and
# `gap` how far apart they were. A win by the one ahead moves few points, a win by the one behind
# many, and a draw moves some toward the one behind.
def settle(outcome: Outcome, ahead: Bool, +a: Nat, +b: Nat, +gap: Nat) -> Ratings:
  match outcome ahead:
    case First{} True{}:
      to_first(a, b, favored(gap))
    case First{} False{}:
      to_first(a, b, Nat.sub(32n, favored(gap)))
    case Second{} True{}:
      to_second(a, b, Nat.sub(32n, favored(gap)))
    case Second{} False{}:
      to_second(a, b, favored(gap))
    case Draw{} True{}:
      to_second(a, b, Nat.sub(16n, favored(gap)))
    case Draw{} False{}:
      to_first(a, b, Nat.sub(16n, favored(gap)))

def rated(+a: Nat, +b: Nat, outcome: Outcome) -> Ratings:
  settle(outcome, Nat.is_ge(a, b), a, b, Nat.add(Nat.sub(a, b), Nat.sub(b, a)))

def total(r: Ratings) -> Nat:
  match r:
    case Ratings{first, second}:
      Nat.add(first, second)

# What every candidate starts at.
def start() -> Nat:
  1000n

def verdict_pick(a: Bool, b: Bool) -> Outcome:
  match a b:
    case True{} _:
      First{}
    case False{} True{}:
      Second{}
    case False{} False{}:
      Draw{}

# What a judge decided between A and B: the first word of its reply; anything else is a draw.
def verdict(reply: String) -> Outcome:
  +said = String.to_upper(String.trim(reply))
  verdict_pick(Bool.and(String.starts_with(said, "A"), Bool.not(String.starts_with(said, "AB"))), String.starts_with(said, "B"))

def by_scores_pick(more: Bool, less: Bool) -> Outcome:
  match more less:
    case True{} _:
      First{}
    case False{} True{}:
      Second{}
    case False{} False{}:
      Draw{}

# The outcome when both were measured: the higher score wins.
def by_scores(+a: Nat, +b: Nat) -> Outcome:
  by_scores_pick(Nat.is_gt(a, b), Nat.is_lt(a, b))

# Climbing
# --------

# Whether an attempt takes the place of the best so far: only when it scores strictly higher.
def keeps(best: Nat, attempt: Nat) -> Bool:
  Nat.is_lt(best, attempt)

# The best score after an attempt.
def kept(+best: Nat, +attempt: Nat) -> Nat:
  Nat.max(best, attempt)

# What is said
# ------------

def slug_put(+c: Char, +acc: String) -> String:
  Bool.pick(String, Bool.or(Char.is_alpha(c), Char.is_digit(c)), SCon{Char.to_lower(c), acc},
    Bool.pick(String, String.starts_with(acc, "-"), acc, SCon{'-', acc}))

def slug_go(s: String, +acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(Bool.pick(String, String.starts_with(acc, "-"), String.drop(acc, 1n), acc))
    case SCon{c, t}:
      slug_go(t, slug_put(c, acc))

# The folder a definition is kept in: its name in lower case, with dashes for everything else.
def slug(name: String) -> String:
  slug_go(String.trim(name), SNil{})

def thousandths(+n: Nat) -> String:
  String.concat([Nat.show(Nat.div(n, 10n)), ".", Nat.show(Nat.mod(n, 10n))])

# An object the definition speaks of.
type Object is Data:
  Object{symbol: String, sort: String, meaning: String}

def object_lines(os: List<&2, Object>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Con{Object{symbol, sort, meaning}, t}:
      String.concat(["- $", symbol, " : ", sort, "$ — ", meaning]) <> object_lines(t)

# A condition of the definition. One that is stipulated is a choice the definer made, not a
# fact found: the definition says so, so that nobody takes the choice for a discovery.
type Axiom is Data:
  Axiom{name: String, statement: String, stipulated: Bool}

def axiom_lines(xs: List<&2, Axiom>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Axiom{name, statement, stipulated}, t}:
      String.concat(["- **(", name, ")** $", statement, "$", Bool.pick(String, stipulated, " *(stipulated: a choice, not a finding)*", "")]) <> axiom_lines(t)

def section(title: String, lines: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.concat(&2, String, [[String.append("## ", title), ""], h <> t, [""]])

def code_block(+source: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(String.trim(source)), Nil{}, ["```bend", String.trim_end(source), "```"])

# A criterion as the definition shows it.
type Shown is Data:
  Shown{name: String, kind: String, weight: Nat, statement: String, how: String, lo: String, hi: String, higher: Bool}

def shown_lines(cs: List<&2, Shown>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Shown{name, kind, weight, statement, how, lo, hi, higher}, t}:
      String.concat(["- **", name, "** (", kind, ", weight ", Nat.show(weight), "): $", statement, "$ — from ", lo, " (worst) to ", hi, " (best)",
        Bool.pick(String, higher, "", ", lower readings being better"), ". Measured by: `", C.clip(C.squash(how, False{}), 300n), "`"]) <> shown_lines(t)

def share(part: Nat, +all: Nat) -> String:
  String.append(Nat.show(Bool.pick(Nat, Nat.is_eq(all, 0n), 0n, Nat.div(Nat.mul(part, 100n), all))), "%")

# How far a definition can be climbed on evidence: how much of its weight is measured exactly,
# how much by a stand-in, and how much by judgment.
def climbable(+exact: Nat, +proxy: Nat, +judged: Nat) -> String:
  +all = Nat.add(exact, Nat.add(proxy, judged))
  String.concat(["Hill-climbable: ", share(exact, all), " of the weight is exact, ", share(proxy, all), " proxy, ", share(judged, all),
    " judged. Only a score with every criterion exact is called verified."])

# A definition, written out.
def written(name: String, answers: String, objects: List<&2, Object>, primitives: List<&2, String>, axioms: List<&2, Axiom>,
  examples: List<&2, String>, non_examples: List<&2, String>, bend: String, criteria: List<&2, Shown>, climb: String) -> String:
  String.join(List.concat(&2, String, [
    [String.append("# Definition: ", name), "", String.append("**Answers:** ", answers), ""],
    section("Objects", object_lines(objects)),
    section("Primitives (left undefined)", C.bulleted(primitives)),
    section("Axioms", axiom_lines(axioms)),
    section("Examples", C.bulleted(examples)),
    section("Non-examples", C.bulleted(non_examples)),
    section("In Bend", code_block(bend)),
    section("Criteria", shown_lines(criteria)),
    [climb, ""]]), "\n")

def defined(name: String, folder: String, text: String) -> String:
  String.concat(["Defined \"", name, "\", kept in ", folder, ".\n\n", text])

def no_definition(name: String, +known: List<&2, String>) -> String:
  String.concat(["No definition named \"", name, "\". Defined so far: ",
    Bool.pick(String, List.is_empty(&2, String, known), "(none)", String.join(known, ", ")), "."])

# One criterion in a measurement.
def row(name: String, kind: String, weight: Nat, measured: Bool, at: Nat, +note: String) -> String:
  String.concat(["  ", name, " [", kind, ", weight ", Nat.show(weight), "]: ",
    Bool.pick(String, measured, String.concat([thousandths(at), "/100"]), "not measured"),
    Bool.pick(String, String.is_empty(note), "", String.concat([" (", C.clip(C.squash(note, False{}), 200n), ")"]))])

def standing_pick(verified: Bool, none: Bool, +unmeasured: Nat) -> String:
  match verified none:
    case True{} _:
      "verified: every criterion is exact"
    case False{} True{}:
      "estimated: it rests on a proxy or a judgment"
    case False{} False{}:
      String.concat(["partial: ", C.counted(unmeasured, "criterion", "criteria"), " could not be measured"])

# What a score rests on.
def standing(+kinds: List<&2, How>, +unmeasured: Nat) -> String:
  standing_pick(verified(kinds, unmeasured), Nat.is_eq(unmeasured, 0n), unmeasured)

# What a measurement says.
def measured(name: String, candidate: String, +score: Nat, standing: String, rows: List<&2, String>) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["\"", candidate, "\" against \"", name, "\": ", thousandths(score), "/100 (", standing, ")"])],
    rows]), "\n")

def judge_system() -> String:
  String.join([
    "You are a judge. You are given a definition and something to judge against it.",
    "Judge only by what the definition and the rubric say, not by what you would have preferred.",
    "Be consistent: the same thing gets the same answer every time."], "\n")

def judge_ask(definition: String, criterion: String, statement: String, rubric: String, candidate: String) -> String:
  String.join([
    "----- THE DEFINITION -----", definition, "",
    String.concat(["----- THE CRITERION: ", criterion, " -----"]), statement, "", "Rubric:", rubric, "",
    "----- WHAT IS JUDGED -----", candidate, "----- END -----", "",
    "Reply with one whole number from 0 to 100 on the first line: where this stands on the criterion, by the rubric.",
    "Then one sentence saying why."], "\n")

def versus_ask(definition: String, a: String, b: String) -> String:
  String.join([
    "----- THE DEFINITION -----", definition, "",
    "----- A -----", a, "", "----- B -----", b, "----- END -----", "",
    "Which of the two does better what the definition says, by its axioms and criteria?",
    "Reply with A, B or DRAW on the first line. Then one sentence saying why."], "\n")

# A candidate and its rating.
type Rated is Data:
  Rated{name: String, rating: Nat, played: Nat}

def rated_lines(rs: List<&2, Rated>, +place: Nat) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Rated{name, rating, played}, t}:
      String.concat(["  ", Nat.show(place), ". ", name, ": ", Nat.show(rating), " (", C.counted(played, "comparison", "comparisons"), ")"]) <> rated_lines(t, 1n+place)

# What a ranking says: the candidates, best first, each with its rating.
def ranked(name: String, by: String, games: Nat, rs: List<&2, Rated>) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["Ratings under \"", name, "\" after ", C.counted(games, "comparison", "comparisons"), ", each decided by ", by, ":"])],
    rated_lines(rs, 1n),
    ["Every candidate starts at 1000. Points only move between the two compared, so the ratings say who does better, not by how much on any scale."]]), "\n")

def hint_lines(+hint: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(hint), Nil{}, ["What the one who asked for this suggests:", hint, ""])

# What an agent is told when it is sent to improve a candidate.
def climb_brief(definition: String, file: String, report: String, hint: String) -> String:
  String.join(List.concat(&2, String, [
    [ String.concat(["Improve the file `", file, "` in this directory so that it scores higher against the definition below."]),
      "It is scored by the definition's criteria and by nothing else: read them, find what holds the score down, and change that.",
      "Change only that file. Keep what already scores well. When you are done, reply in two sentences with what you changed and why it should score higher.",
      "",
      "----- THE DEFINITION -----", definition, "",
      "----- HOW IT SCORES NOW -----", report, ""],
    hint_lines(hint)]), "\n")

# One attempt of a climb.
def attempt_line(round: Nat, n: Nat, +score: Nat, +best: Nat, +how: String) -> String:
  String.concat(["  round ", Nat.show(round), ", attempt ", Nat.show(n), ": ", thousandths(score), "/100",
    Bool.pick(String, keeps(best, score), " — kept", ""), Bool.pick(String, String.is_empty(how), "", String.concat([" (", how, ")"]))])

def climbed_end(better: Bool, +file: String, backup: String) -> String:
  match better:
    case True{}:
      String.concat([file, " now holds the best attempt. What it was before is in ", backup, "."])
    case False{}:
      String.concat(["No attempt scored higher, so ", file, " is as it was."])

# What a climb says when it is over.
def climbed(name: String, +file: String, +from: Nat, +to: Nat, standing: String, lines: List<&2, String>, backup: String) -> String:
  String.join(List.concat(&2, String, [
    [String.concat(["Climbed \"", file, "\" against \"", name, "\": ", thousandths(from), "/100 to ", thousandths(to), "/100 (", standing, ")."])],
    lines,
    [climbed_end(Nat.is_lt(from, to), file, backup)]]), "\n")

# How a tool that is not there is installed, inside wizardry's own directory, so that it is
# apart from everything else on the machine and goes when wizardry does.
def install_line(+home: String, tool: String) -> String:
  String.concat(["`UV_TOOL_DIR=", home, "/tools UV_TOOL_BIN_DIR=", home, "/bin UV_PYTHON_INSTALL_DIR=", home, "/tools/python uv tool install --python 3.12 ", tool, "`"])

def jacobian_line(+at: String, home: String) -> String:
  Bool.pick(String, String.is_empty(at),
    String.concat(["- jacobian (exact, typed mathematical operations) is not installed. Exact criteria are then scripts of your own. It takes about 350 MB, so ask before installing it: ", install_line(home, "jacobian")]),
    String.concat(["- jacobian is installed (`", at, "`): for a criterion that is a mathematical quantity, let its command call `", at, " run <operation> --json '{...}'` (`", at, " catalog` lists the operations, `", at, " inspect <operation>` shows one contract). It answers in JSON, and its results are exact where they claim to be, which is what an exact criterion needs."]))

def hillclimb_line(+at: String, home: String) -> String:
  Bool.pick(String, String.is_empty(at),
    String.concat(["- hillclimb (long searches over programs, scored by a verifier) is not installed. `defintire_climb` climbs any file with the agents this session deploys. It takes about 250 MB, so ask before installing it: ", install_line(home, "hillclimb")]),
    String.concat(["- hillclimb is installed (`", at, "`): when every criterion is a command and the thing improved is a program, a long search is its work. In a folder of its own: `", at, " init`, `", at, " climber get greedy`, `", at, " problem new <id>`; put the definition's commands in the problem's `score.py` (it writes {\"score\": ...} to $HILLCLIMB_RESULT) and set `metric` and `higher_is_better` in `problem.yaml`; `", at, " verify <id>` after every edit; then `", at, " run <id> --budget 1h`, which carries on in the background (`", at, " status`, `", at, " summit`)."]))

def tool_lines(hillclimb: String, jacobian: String, +home: String) -> List<&2, String>:
  ["On this machine", jacobian_line(jacobian, home), hillclimb_line(hillclimb, home), ""]

def saved_lines(saved: List<&2, String>) -> List<&2, String>:
  match saved:
    case Nil{}:
      ["Nothing is defined yet."]
    case Con{h, t}:
      [String.append("Defined so far: ", String.join(h <> t, ", "))]

# The method: what `defintire` returns.
def method(hillclimb: String, jacobian: String, home: String, saved: List<&2, String>) -> String:
  String.join(List.concat(&2, String, [
    [ "DEFINTIRE: say what a thing is, in mathematical form, so that it can be measured and then improved.",
      "",
      "It works for anything: a mathematical object, a good commit message, a fair schedule, a fast parser.",
      "A definition turns the word into objects and axioms; criteria turn the axioms into numbers; a number can be climbed.",
      "",
      "1. Define (`defintire_define`)",
      "- Start from the question the definition answers: what could nobody decide or measure without it? A definition",
      "  that answers no question is a description.",
      "- Objects: the things it speaks of, each with a symbol and a type ($m$ : String, $G = (V, E)$ : Graph, $f : X \\to \\mathbb{R}$).",
      "- Primitives: what is left undefined on purpose. Every definition stops somewhere; say where.",
      "- Axioms: conditions in notation, each holding of exactly the things defined ($|s(m)| \\le 72$, $\\forall x \\in X.\\ f(x) \\ge 0$).",
      "  Outside mathematics most axioms are choices: mark those `stipulated`, so that a choice is not read as a finding.",
      "- Examples and non-examples, and near misses above all: the thing that fails one axiom and no other is what",
      "  shows that axiom is needed. If no non-example can be found for an axiom, drop the axiom.",
      "- Try to break it before you keep it: look for something that satisfies every axiom and plainly is not the",
      "  thing, and for something that plainly is and fails one. Either is a reason to change the definition.",
      "- Where Bend can say it, say it in Bend too (`bend`): a type for the objects, a def or law for an axiom. Then",
      "  whether something is an instance is a check, not an opinion.",
      "",
      "2. Make it quantitative: criteria",
      "- A criterion ties a number to an axiom or to the definition's purpose: a name, a statement in notation, a",
      "  weight, the readings that count as worst and best, and how the reading is taken.",
      "- exact: a command computes the very quantity (a count, a test passing, a proof checking). Prefer these.",
      "- proxy: a command computes a stand-in (a readability formula for clarity). Say what it stands in for.",
      "- judged: a model reads the candidate against a rubric and gives 0 to 100. Use it for what no script reaches,",
      "  and write the rubric so that two judges would agree: what 0 looks like, what 100 looks like.",
      "- gate: true on a criterion makes it stand for an axiom: the score can never be higher than where the",
      "  candidate stands on a gate, so what fails an axiom cannot score well by doing well elsewhere. Give a gate a",
      "  reading that still falls as the failure gets worse, or a climb has nothing to follow.",
      "- A command runs in the directory the definition was made in, with the candidate's path in $DEFINTIRE_CANDIDATE",
      "  and as its last argument, and prints the reading first on the last line of its output. Tools installed",
      "  for wizardry (below) are on its PATH.",
      "",
      "3. Measure and compare",
      "- `defintire_measure` scores one candidate out of 100, criterion by criterion, and says what the score rests on:",
      "  verified (all exact), estimated (a proxy or a judgment is in it), or partial.",
      "- `defintire_rank` compares candidates two at a time and keeps a rating for each, as in chess: where no absolute",
      "  number can be trusted, which of two is better usually can.",
      "",
      "4. Climb (`defintire_climb`)",
      "- Agents take turns improving a file; every attempt is measured, and only one that scores strictly higher",
      "  replaces the best. The score never goes down, and the file is only changed for something better.",
      "- A climb is as good as its criteria. If the score rises and the thing gets worse, the definition is wrong:",
      "  fix the definition, not the candidate.",
      ""],
    tool_lines(hillclimb, jacobian, home),
    saved_lines(saved)]), "\n")

def describe() -> String:
  String.concat(["The defintire skill: turn anything, mathematical or not, into an explicit formal definition (objects, axioms, examples and non-examples, in ",
    "mathematical notation and in Bend where Bend can say it), tie numbers to it, and improve things against it. ",
    "Returns the method, which tools for it are on this machine, and the definitions kept so far. Call it before defining, measuring or climbing."])

def describe_define() -> String:
  "Keep a definition: what is defined, the question it answers, its objects, axioms, examples, non-examples, and the criteria that score things against it. Call `defintire` first for the method. Refused, with what is missing, when it is not yet a definition."

def describe_measure() -> String:
  "Score a candidate (a file, or text) against a kept definition, out of 100, criterion by criterion. Says whether the score is verified (every criterion exact), estimated or partial."

def describe_rank() -> String:
  "Compare candidates two at a time under a kept definition and give each a rating (Elo, from 1000). Decided by the measured scores when every criterion is a command, and by a judge reading both otherwise. Ratings are kept and carry on from earlier comparisons."

def describe_climb() -> String:
  "Improve a file against a kept definition: agents make attempts, each is measured, and only an attempt that scores strictly higher is kept. The file is changed only when something better was found; what it was is kept beside the climb."

# What the host asks besides
# --------------------------

def is_judged(kind: How) -> Bool:
  match kind:
    case Judged{}:
      True{}
    case Exact{}:
      False{}
    case Proxy{}:
      False{}
    case Unknown{}:
      False{}

# Whether a comparison under these criteria needs a judge: it does when any of them is judged.
# Otherwise both candidates are measured and the higher score wins.
def needs_judge(kinds: List<&2, How>) -> Bool:
  match kinds:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(is_judged(h), needs_judge(t))

def decided_by(judge: Bool) -> String:
  match judge:
    case True{}:
      "a judge reading both against the definition"
    case False{}:
      "the measured scores"

def placed(+r: Rated, rs: List<&2, Rated>) -> List<&2, Rated>:
  match r rs:
    case Rated{n, x, p} Nil{}:
      [Rated{n, x, p}]
    case Rated{n, x, p} Con{Rated{+hn, +hx, +hp}, +t}:
      Bool.pick(List<&2, Rated>, Nat.is_ge(x, hx), Rated{n, x, p} <> Rated{hn, hx, hp} <> t, Rated{hn, hx, hp} <> placed(Rated{n, x, p}, t))

# The candidates, highest rating first.
def sorted(rs: List<&2, Rated>) -> List<&2, Rated>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      placed(h, sorted(t))

# What a judge is shown of a candidate: all of it, up to sixty thousand characters.
def shown_to_judge(text: String) -> String:
  C.clip(text, 60000n)

def option(flag: String, +value: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(value), Nil{}, [flag, value])

def first_set(+a: String, b: String) -> String:
  Bool.pick(String, String.is_empty(a), b, a)

# What an agent sent to climb runs on: what the user chose for deployed agents (/default-agent),
# and otherwise what this session is on.
def agent_args(model: String, session_model: String, thinking: String, session_thinking: String) -> List<&2, String>:
  List.append(&2, String, option("--model", first_set(model, session_model)), option("--thinking", first_set(thinking, session_thinking)))

def no_judge() -> String:
  "no model is signed in to judge with"

def no_number(+code: Nat, +said: String) -> String:
  String.concat([Bool.pick(String, Nat.is_eq(code, 0n), "its command printed no number at the start of its last line", String.append("its command ended with status ", Nat.show(code))),
    Bool.pick(String, String.is_empty(said), "", String.append(": ", said))])

def judge_said_nothing() -> String:
  "the judge gave no number"

def needs_two() -> String:
  "A ranking needs at least two candidates."

def cannot_judge() -> String:
  "This definition has judged criteria, so a comparison needs a judge, and no model is signed in to judge with. Nothing was compared."

def no_candidate(what: String) -> String:
  String.concat(["There is nothing to score: \"", what, "\" is not a file here, and no text was given."])

# What defintire puts in the agent's head
# ---------------------------------------

# A definition kept, as the agent is reminded of it.
type Known is Data:
  Known{name: String, answers: String}

def known_lines(known: List<&2, Known>, room: Nat) -> List<&2, String>:
  match known room:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      ["- and more: `defintire` lists them"]
    case Con{Known{name, answers}, t} 1n+p:
      String.concat(["- ", name, ": ", C.clip(C.squash(answers, False{}), 110n)]) <> known_lines(t, p)

def known_part(known: List<&2, Known>) -> List<&2, String>:
  match known:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      "Defined already (score against these with `defintire_measure` rather than by feel):" <> known_lines(h <> t, 5n)

# The little that defintire adds to the standing prompt: a habit of mind, and what is defined.
# wizardry lets it in by name and cuts it short; every other plugin reaches the agent by actions.
def mind(known: List<&2, Known>) -> String:
  String.join(List.append(&2, String, [
    "A habit you keep (from defintire): when what you are asked to make, judge or improve is vague, say what it is before you work on it — the things it speaks of, the condition that must hold of them, and one thing that fails it. When something is called better, name the number that would show it. Keep this to a line or two unless asked for more; `defintire` holds the full method."],
    known_part(known)), "\n")
