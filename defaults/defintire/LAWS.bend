# What must hold of defintire's decisions (defintire.bend), whatever is defined and however it scores.
#
# Each law is a claim; PROOF.bend proves it. A law speaks of the decision: that a score resting
# on a judgment is never called verified is proven here; that the judge was then asked, and the
# verifier run, is what index.js does and what the tests see.

import Base
import ./defintire.bend as D

# A score is never called verified when any criterion in it is a proxy or a judgment, wherever
# among the criteria it stands.
law one_soft_criterion_spoils:
  for +a: List<&2, D.How>
  for +b: List<&2, D.How>
  {D.all_exact(List.append(&2, D.How, a, D.Proxy{} <> b)) == False{} : Bool} & {D.all_exact(List.append(&2, D.How, a, D.Judged{} <> b)) == False{} : Bool}

law soft_is_never_verified:
  for kinds: List<&2, D.How>
  for unmeasured: Nat
  for soft: {D.all_exact(kinds) == False{} : Bool}
  {D.verified(kinds, unmeasured) == False{} : Bool}

# Nor when a criterion of the definition could not be measured, nor when nothing was.
law unmeasured_is_never_verified:
  for kinds: List<&2, D.How>
  for unmeasured: Nat
  {D.verified(kinds, 1n+unmeasured) == False{} : Bool} & {D.verified(Nil{}, unmeasured) == False{} : Bool}

# Whatever a verifier prints, and whatever range the criterion gives, where the candidate stands
# is between 0 and 1000 thousandths: no reading can score past the best.
law position_in_range:
  for +v: F32
  for +lo: F32
  for +hi: F32
  for higher: Bool
  {Nat.is_le(D.position(v, lo, hi, higher), 1000n) == True{} : Bool}

# A comparison only moves points between the two compared: whoever wins, whoever was ahead and
# by however much, the two ratings add up to what they did.
law ratings_are_conserved:
  for outcome: D.Outcome
  for ahead: Bool
  for +a: Nat
  for +b: Nat
  for +gap: Nat
  {D.total(D.settle(outcome, ahead, a, b, gap)) == Nat.add(a, b) : Nat}

# A win is always worth something to the one ahead, and never more than half of what is at stake.
law a_win_is_worth_something:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for b5: Bool
  for b6: Bool
  for b7: Bool
  {Nat.is_le(1n, D.favored_pick(b1, b2, b3, b4, b5, b6, b7)) == True{} : Bool} & {Nat.is_le(D.favored_pick(b1, b2, b3, b4, b5, b6, b7), 16n) == True{} : Bool}

# A climb never goes downhill: the best score after an attempt is at least the best before it.
law never_downhill:
  for +best: Nat
  for +attempt: Nat
  {Nat.is_ge(D.kept(best, attempt), best) == True{} : Bool}

# An attempt that only equals the best does not replace it: the file changes for something better.
law a_tie_changes_nothing:
  for best: Nat
  {D.keeps(best, best) == False{} : Bool}

# The three ways a criterion is measured go by their words, and no other word is one.
law kinds_by_word:
  ({D.kind_of("exact") == D.Exact{} : D.How} & {D.kind_of("proxy") == D.Proxy{} : D.How}) & ({D.kind_of("judged") == D.Judged{} : D.How} & {D.kind_of("") == D.Unknown{} : D.How})
