# Proofs of the laws in LAWS.bend. `bend PROOF.bend` must print ALL PROOFS CHECK before a commit.
#
# The lemmas about adding (P.add_zero, P.add_succ) are wizardry's own, from its PROOF.bend.

import Base
import ../../PROOF.bend as P
import ./defintire.bend as D
import ./LAWS.bend as Laws

def and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def spoils_proxy(a: List<&2, D.How>, -b: List<&2, D.How>) -> {D.all_exact(List.append(&2, D.How, a, D.Proxy{} <> b)) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, D.all_exact(List.append(&2, D.How, t, D.Proxy{} <> b)), False{}, spoils_proxy(t, b)) : {Bool.and(D.is_exact(h), _) == False{} : Bool}
      and_false(D.is_exact(h))

def spoils_judged(a: List<&2, D.How>, -b: List<&2, D.How>) -> {D.all_exact(List.append(&2, D.How, a, D.Judged{} <> b)) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, D.all_exact(List.append(&2, D.How, t, D.Judged{} <> b)), False{}, spoils_judged(t, b)) : {Bool.and(D.is_exact(h), _) == False{} : Bool}
      and_false(D.is_exact(h))

def Laws.one_soft_criterion_spoils(a, b):
  (spoils_proxy(a, b), spoils_judged(a, b))

def Laws.soft_is_never_verified(kinds, unmeasured, soft):
  match kinds:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, D.all_exact(h <> t), False{}, soft) : {Bool.and(Nat.is_eq(unmeasured, 0n), _) == False{} : Bool}
      and_false(Nat.is_eq(unmeasured, 0n))

def none_left(kinds: List<&2, D.How>, -unmeasured: Nat) -> {D.verified(kinds, 1n+unmeasured) == False{} : Bool}:
  match kinds:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def Laws.unmeasured_is_never_verified(kinds, unmeasured):
  (none_left(kinds, unmeasured), {==})

# The lesser of two is at most the second.
def least_fits(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      least_fits(ap, bp)

def Laws.position_in_range(v, lo, hi, higher):
  least_fits(Bool.pick(Nat, Bool.and(F32.is_lt(lo, hi), D.real(v)), F32.to_nat(F32.round(F32.mul(1000.0, D.turned(higher, D.along(v, lo, hi))))), 0n), 1000n)

# Points given to the first are taken from the second: the sum is as it was.
def first_keeps(+a: Nat, +p: Nat, +b: Nat) -> {Nat.add(Nat.add(a, D.least(p, b)), Nat.sub(b, D.least(p, b))) == Nat.add(a, b) : Nat}:
  match p b:
    case 0n 0n:
      P.add_zero(Nat.add(a, 0n))
    case 0n 1n+bp:
      %Equal.sym(Nat, Nat.add(a, 0n), a, P.add_zero(a)) : {Nat.add(_, 1n+bp) == Nat.add(a, 1n+bp) : Nat}
      {==}
    case 1n+pp 0n:
      P.add_zero(Nat.add(a, 0n))
    case 1n+pp 1n+bp:
      %Equal.sym(Nat, Nat.add(a, 1n+D.least(pp, bp)), 1n+Nat.add(a, D.least(pp, bp)), P.add_succ(a, D.least(pp, bp))) : {Nat.add(_, Nat.sub(bp, D.least(pp, bp))) == Nat.add(a, 1n+bp) : Nat}
      %Equal.sym(Nat, Nat.add(a, 1n+bp), 1n+Nat.add(a, bp), P.add_succ(a, bp)) : {1n+Nat.add(Nat.add(a, D.least(pp, bp)), Nat.sub(bp, D.least(pp, bp))) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(a, D.least(pp, bp)), Nat.sub(bp, D.least(pp, bp))), Nat.add(a, bp), first_keeps(a, pp, bp))

# Points given to the second are taken from the first: the sum is as it was.
def second_keeps(+p: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.sub(a, D.least(p, a)), Nat.add(b, D.least(p, a))) == Nat.add(a, b) : Nat}:
  match p a:
    case 0n 0n:
      P.add_zero(b)
    case 0n 1n+ap:
      %Equal.sym(Nat, Nat.add(b, 0n), b, P.add_zero(b)) : {1n+Nat.add(ap, _) == 1n+Nat.add(ap, b) : Nat}
      {==}
    case 1n+pp 0n:
      P.add_zero(b)
    case 1n+pp 1n+ap:
      %Equal.sym(Nat, Nat.add(b, 1n+D.least(pp, ap)), 1n+Nat.add(b, D.least(pp, ap)), P.add_succ(b, D.least(pp, ap))) : {Nat.add(Nat.sub(ap, D.least(pp, ap)), _) == 1n+Nat.add(ap, b) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(ap, D.least(pp, ap)), 1n+Nat.add(b, D.least(pp, ap))), 1n+Nat.add(Nat.sub(ap, D.least(pp, ap)), Nat.add(b, D.least(pp, ap))), P.add_succ(Nat.sub(ap, D.least(pp, ap)), Nat.add(b, D.least(pp, ap)))) : {_ == 1n+Nat.add(ap, b) : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.sub(ap, D.least(pp, ap)), Nat.add(b, D.least(pp, ap))), Nat.add(ap, b), second_keeps(pp, ap, b))

def Laws.ratings_are_conserved(outcome, ahead, a, b, gap):
  match outcome ahead:
    case D.First{} True{}:
      first_keeps(a, D.favored(gap), b)
    case D.First{} False{}:
      first_keeps(a, Nat.sub(32n, D.favored(gap)), b)
    case D.Second{} True{}:
      second_keeps(Nat.sub(32n, D.favored(gap)), a, b)
    case D.Second{} False{}:
      second_keeps(D.favored(gap), a, b)
    case D.Draw{} True{}:
      second_keeps(Nat.sub(16n, D.favored(gap)), a, b)
    case D.Draw{} False{}:
      first_keeps(a, Nat.sub(16n, D.favored(gap)), b)

def Laws.a_win_is_worth_something(b1, b2, b3, b4, b5, b6, b7):
  match b1 b2 b3 b4 b5 b6 b7:
    case True{} _ _ _ _ _ _:
      ({==}, {==})
    case False{} True{} _ _ _ _ _:
      ({==}, {==})
    case False{} False{} True{} _ _ _ _:
      ({==}, {==})
    case False{} False{} False{} True{} _ _ _:
      ({==}, {==})
    case False{} False{} False{} False{} True{} _ _:
      ({==}, {==})
    case False{} False{} False{} False{} False{} True{} _:
      ({==}, {==})
    case False{} False{} False{} False{} False{} False{} True{}:
      ({==}, {==})
    case False{} False{} False{} False{} False{} False{} False{}:
      ({==}, {==})

def Laws.never_downhill(best, attempt):
  Nat.max_ge_l(best, attempt)

def Laws.a_tie_changes_nothing(best):
  match best:
    case 0n:
      {==}
    case 1n+p:
      Laws.a_tie_changes_nothing(p)

def Laws.kinds_by_word():
  (({==}, {==}), ({==}, {==}))
