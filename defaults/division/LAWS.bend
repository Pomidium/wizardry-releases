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

# However many agents there are, when no two of them own a file in common, no path has more
# than one of them that may write it.
law one_writer:
  for +owns: List<&2, List<&2, String>>
  for +path: String
  for +apart: {D.disjoint(owns) == True{} : Bool}
  {Nat.is_le(D.writers(owns, path), 1n) == True{} : Bool}

# When a cut is made, into however many parts, no two parts own a file in common.
law parts_never_share_a_file:
  for depth: Nat
  for limit: Nat
  for +parent: D.Owns
  for +pieces: List<&2, D.Piece>
  for cut: {D.judge(depth, limit, parent, pieces) == D.Divide{} : D.Verdict}
  {D.disjoint(D.owns_of(pieces)) == True{} : Bool}

# When a cut is made, every part owns only what the agent cutting may write.
law parts_stay_inside:
  for depth: Nat
  for limit: Nat
  for +parent: D.Owns
  for +pieces: List<&2, D.Piece>
  for cut: {D.judge(depth, limit, parent, pieces) == D.Divide{} : D.Verdict}
  {D.all_inside(D.owns_of(pieces), parent) == True{} : Bool}

# When a cut is made, every law at it has one prover: no law is given to two parts, and no two
# parts go by one name.
law one_prover_per_law:
  for +depth: Nat
  for +limit: Nat
  for +parent: D.Owns
  for +pieces: List<&2, D.Piece>
  for +cut: {D.judge(depth, limit, parent, pieces) == D.Divide{} : D.Verdict}
  {D.distinct(D.laws_of(pieces)) == True{} : Bool} & {D.distinct(D.names_of(pieces)) == True{} : Bool}

# Cutting ends: a cut is made only while the tree is not yet as deep as it may get.
law cutting_ends:
  for +depth: Nat
  for +limit: Nat
  for +parent: D.Owns
  for +pieces: List<&2, D.Piece>
  for cut: {D.judge(depth, limit, parent, pieces) == D.Divide{} : D.Verdict}
  {Nat.is_lt(depth, limit) == True{} : Bool}

# Nothing else is asked of a cut: how many parts there are and how large each is are not what a
# cut is refused for. Parts with names of their own, files of their own inside what is the
# cutter's, and laws of their own, are cut.
law nothing_else_is_asked:
  for depth: Nat
  for limit: Nat
  for +parent: D.Owns
  for +h: D.Piece
  for +t: List<&2, D.Piece>
  for shallow: {Nat.is_lt(depth, limit) == True{} : Bool}
  for names: {D.distinct(D.names_of(h <> t)) == True{} : Bool}
  for laws: {D.distinct(D.laws_of(h <> t)) == True{} : Bool}
  for within: {D.all_inside(D.owns_of(h <> t), parent) == True{} : Bool}
  for apart: {D.disjoint(D.owns_of(h <> t)) == True{} : Bool}
  {D.judge(depth, limit, parent, h <> t) == D.Divide{} : D.Verdict}

# A model or thinking level chosen with /default-agent or /division is what the agents run on, whatever the
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

# /default-agent alone takes this session's setup for the agents, and "same" gives it back.
law default_agent_words:
  {D.agent_wants("") == D.Current{} : D.Agent} & {D.agent_wants("same") == D.Follow{} : D.Agent}

# The halves are never said to fit when the check ended badly or was stopped, whatever it printed.
law a_failed_check_never_fits:
  for code: Nat
  for c: Char
  for why: String
  for +said: String
  {D.fits(D.Ended{1n+code, ""}, said) == False{} : Bool} & {D.fits(D.Ended{0n, SCon{c, why}}, said) == False{} : Bool}
