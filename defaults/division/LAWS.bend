# What must hold of division's decisions (division.bend), whatever the task and however it is cut.
#
# Each law is a claim; PROOF.bend proves it. A law speaks of the decision: that two halves are
# never handed a file in common is proven here; that an agent is then stopped from writing what
# it was not handed is what index.js does with the answer, and what the tests see.

import Base
import ../../bend/core.bend as C
import ./division.bend as D

# Two agents whose files do not overlap can never both be allowed to write the same path.
law no_trample:
  for +a: List<&2, String>
  for +b: List<&2, String>
  for +path: String
  for apart: {D.overlap(a, b) == False{} : Bool}
  for mine: {D.may_write(a, path) == True{} : Bool}
  {D.may_write(b, path) == False{} : Bool}

# What an agent is handed never reaches past what the agent handing it out may write itself:
# down the tree, ownership only narrows.
law stays_inside:
  for +entries: List<&2, String>
  for +parent: D.Owns
  for +path: String
  for within: {D.inside(entries, parent) == True{} : Bool}
  for mine: {D.may_write(entries, path) == True{} : Bool}
  {D.may(parent, path) == True{} : Bool}

# When a cut is made, no path can be written by both halves.
law halves_never_share_a_file:
  for depth: Nat
  for limit: Nat
  for +chunk: Nat
  for +parent: D.Owns
  for +n1: String
  for +o1: List<&2, String>
  for +l1: List<&2, String>
  for +m1: Nat
  for +n2: String
  for +o2: List<&2, String>
  for +l2: List<&2, String>
  for +m2: Nat
  for +path: String
  for cut: {D.judge(depth, limit, chunk, parent, D.Piece{n1, o1, l1, m1}, D.Piece{n2, o2, l2, m2}) == D.Divide{} : D.Verdict}
  for mine: {D.may_write(o1, path) == True{} : Bool}
  {D.may_write(o2, path) == False{} : Bool}

# When a cut is made, both halves own only what the agent cutting may write.
law halves_stay_inside:
  for depth: Nat
  for limit: Nat
  for +chunk: Nat
  for +parent: D.Owns
  for +n1: String
  for +o1: List<&2, String>
  for +l1: List<&2, String>
  for +m1: Nat
  for +n2: String
  for +o2: List<&2, String>
  for +l2: List<&2, String>
  for +m2: Nat
  for cut: {D.judge(depth, limit, chunk, parent, D.Piece{n1, o1, l1, m1}, D.Piece{n2, o2, l2, m2}) == D.Divide{} : D.Verdict}
  {D.inside(o1, parent) == True{} : Bool} & {D.inside(o2, parent) == True{} : Bool}

# When a cut is made, every law at it has one prover: a law one half must prove is not the
# other's too.
law one_prover_per_law:
  for depth: Nat
  for limit: Nat
  for +chunk: Nat
  for +parent: D.Owns
  for +n1: String
  for +o1: List<&2, String>
  for +l1: List<&2, String>
  for +m1: Nat
  for +n2: String
  for +o2: List<&2, String>
  for +l2: List<&2, String>
  for +m2: Nat
  for +claim: String
  for cut: {D.judge(depth, limit, chunk, parent, D.Piece{n1, o1, l1, m1}, D.Piece{n2, o2, l2, m2}) == D.Divide{} : D.Verdict}
  for mine: {C.has(l1, claim) == True{} : Bool}
  {C.has(l2, claim) == False{} : Bool}

# When a cut is made, each half has a law to prove: no agent's work goes unchecked.
law every_half_is_checked:
  for depth: Nat
  for limit: Nat
  for +chunk: Nat
  for +parent: D.Owns
  for +n1: String
  for +o1: List<&2, String>
  for +l1: List<&2, String>
  for +m1: Nat
  for +n2: String
  for +o2: List<&2, String>
  for +l2: List<&2, String>
  for +m2: Nat
  for cut: {D.judge(depth, limit, chunk, parent, D.Piece{n1, o1, l1, m1}, D.Piece{n2, o2, l2, m2}) == D.Divide{} : D.Verdict}
  {List.is_empty(&2, String, l1) == False{} : Bool} & {List.is_empty(&2, String, l2) == False{} : Bool}

# A cut is made only of a large task: each half is at least a chunk of work, and the tree is not
# yet as deep as it may get.
law only_large_tasks_divide:
  for +depth: Nat
  for +limit: Nat
  for +chunk: Nat
  for +parent: D.Owns
  for +n1: String
  for +o1: List<&2, String>
  for +l1: List<&2, String>
  for +m1: Nat
  for +n2: String
  for +o2: List<&2, String>
  for +l2: List<&2, String>
  for +m2: Nat
  for +cut: {D.judge(depth, limit, chunk, parent, D.Piece{n1, o1, l1, m1}, D.Piece{n2, o2, l2, m2}) == D.Divide{} : D.Verdict}
  ({Nat.is_ge(m1, chunk) == True{} : Bool} & {Nat.is_ge(m2, chunk) == True{} : Bool}) & {Nat.is_lt(depth, limit) == True{} : Bool}

# A model or thinking level chosen with /division is what the halves run on, whatever the
# session is on.
law choice_runs:
  for c: Char
  for rest: String
  for session: String
  {D.runs_on(SCon{c, rest}, session) == SCon{c, rest} : String}

# With no choice, the halves run on what the session is on.
law no_choice_follows_session:
  for session: String
  {D.runs_on("", session) == session : String}

# Choosing "same" is taking the choice back: the halves follow the session again.
law same_follows_session:
  for session: String
  {D.runs_on(D.kept("same"), session) == session : String}

# /division alone shows the choices; "model" and "thinking" are the two that can be set.
law division_words:
  ({D.wants("") == D.Show{} : D.Wants} & {D.wants("model") == D.Model{} : D.Wants}) & {D.wants("thinking") == D.Thinking{} : D.Wants}

# The halves are never said to fit when the check ended badly or was stopped, whatever it printed.
law a_failed_check_never_fits:
  for code: Nat
  for c: Char
  for why: String
  for +said: String
  {D.fits(D.Ended{1n+code, ""}, said) == False{} : Bool} & {D.fits(D.Ended{0n, SCon{c, why}}, said) == False{} : Bool}
