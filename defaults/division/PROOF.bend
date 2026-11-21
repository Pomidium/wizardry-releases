# Proofs of the laws in LAWS.bend. `bend PROOF.bend` must print ALL PROOFS CHECK before a commit.
#
# The lemmas about names (P.alike, P.same and the rest) are wizardry's own, from its PROOF.bend.

import Base
import ../../bend/core.bend as C
import ../../PROOF.bend as P
import ./division.bend as D
import ./LAWS.bend as Laws

# Booleans
# --------

# When both of two hold, the first does.
def and_left(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

# When both of two hold, the second does.
def and_right(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      P.not_false({b == True{} : Bool}, e)
    case True{}:
      e

# What is not false is true.
def not_not(a: Bool, e: {Bool.not(a) == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      P.not_true({False{} == True{} : Bool}, e)
    case True{}:
      {==}

# Characters that compare equal are the same character
# ----------------------------------------------------

def cmp_eq(-x: Word(32n), -y: Word(32n), r: Cmp, er: {Word.cmp(32n, x, y) == r : Cmp}, e: {Cmp.is_eq(r) == True{} : Bool}) -> {Word.cmp(32n, x, y) == EQ{} : Cmp}:
  match r:
    case LT{}:
      P.not_false({Word.cmp(32n, x, y) == EQ{} : Cmp}, e)
    case EQ{}:
      er
    case GT{}:
      P.not_false({Word.cmp(32n, x, y) == EQ{} : Cmp}, e)

def char_alike(a: Char, b: Char, e: {Char.is_eq(a, b) == True{} : Bool}) -> {a == b : Char}:
  match a b:
    case Chr{U32{+x}} Chr{U32{+y}}:
      %P.word_sound(32n, x, y, cmp_eq(x, y, Word.cmp(32n, x, y), {==}, e)) : {Chr{U32{x}} == Chr{U32{_}} : Char}
      {==}

# Beginnings of texts
# -------------------
# String.starts_with.go(x, y) says that y begins with x.

def line_step(
  c1: Bool, c2: Bool, +x: Char, +y: Char, +z: Char, -at: String, -bt: String, -pt: String,
  e1: {Char.is_eq(z, x) == c1 : Bool},
  e2: {Char.is_eq(z, y) == c2 : Bool},
  h1: {String.starts_with.go.if(at, pt, c1) == True{} : Bool},
  h2: {String.starts_with.go.if(bt, pt, c2) == True{} : Bool},
  ih: {String.starts_with.go(at, pt) == True{} : Bool} -> {String.starts_with.go(bt, pt) == True{} : Bool} ->
    {Bool.or(String.starts_with.go(at, bt), String.starts_with.go(bt, at)) == True{} : Bool}
) -> {Bool.or(String.starts_with.go.if(at, bt, Char.is_eq(y, x)), String.starts_with.go.if(bt, at, Char.is_eq(x, y))) == True{} : Bool}:
  match c1 c2:
    case False{} _:
      P.not_false({Bool.or(String.starts_with.go.if(at, bt, Char.is_eq(y, x)), String.starts_with.go.if(bt, at, Char.is_eq(x, y))) == True{} : Bool}, h1)
    case True{} False{}:
      P.not_false({Bool.or(String.starts_with.go.if(at, bt, Char.is_eq(y, x)), String.starts_with.go.if(bt, at, Char.is_eq(x, y))) == True{} : Bool}, h2)
    case True{} True{}:
      %char_alike(z, x, e1) : {Bool.or(String.starts_with.go.if(at, bt, Char.is_eq(y, _)), String.starts_with.go.if(bt, at, Char.is_eq(_, y))) == True{} : Bool}
      %char_alike(z, y, e2) : {Bool.or(String.starts_with.go.if(at, bt, Char.is_eq(_, z)), String.starts_with.go.if(bt, at, Char.is_eq(z, _))) == True{} : Bool}
      %Equal.sym(Bool, Char.is_eq(z, z), True{}, P.char_same(z)) : {Bool.or(String.starts_with.go.if(at, bt, _), String.starts_with.go.if(bt, at, _)) == True{} : Bool}
      ih(h1)(h2)

# Two beginnings of the same text: one of them begins the other.
def in_line(a: String, b: String, p: String,
  h1: {String.starts_with.go(a, p) == True{} : Bool},
  h2: {String.starts_with.go(b, p) == True{} : Bool}
) -> {Bool.or(String.starts_with.go(a, b), String.starts_with.go(b, a)) == True{} : Bool}:
  match a b p:
    case SNil{} _ _:
      {==}
    case SCon{x, at} SNil{} _:
      {==}
    case SCon{x, at} SCon{y, bt} SNil{}:
      P.not_false({Bool.or(String.starts_with.go(SCon{x, at}, SCon{y, bt}), String.starts_with.go(SCon{y, bt}, SCon{x, at})) == True{} : Bool}, h1)
    case SCon{+x, +at} SCon{+y, +bt} SCon{+z, +pt}:
      line_step(Char.is_eq(z, x), Char.is_eq(z, y), x, y, z, at, bt, pt, {==}, {==}, h1, h2, k1 => k2 => in_line(at, bt, pt, k1, k2))

def through_step(
  c1: Bool, c2: Bool, +x: Char, +y: Char, +z: Char, -at: String, -bt: String, -ct: String,
  e1: {Char.is_eq(y, x) == c1 : Bool},
  e2: {Char.is_eq(z, y) == c2 : Bool},
  h1: {String.starts_with.go.if(at, bt, c1) == True{} : Bool},
  h2: {String.starts_with.go.if(bt, ct, c2) == True{} : Bool},
  ih: {String.starts_with.go(at, bt) == True{} : Bool} -> {String.starts_with.go(bt, ct) == True{} : Bool} ->
    {String.starts_with.go(at, ct) == True{} : Bool}
) -> {String.starts_with.go.if(at, ct, Char.is_eq(z, x)) == True{} : Bool}:
  match c1 c2:
    case False{} _:
      P.not_false({String.starts_with.go.if(at, ct, Char.is_eq(z, x)) == True{} : Bool}, h1)
    case True{} False{}:
      P.not_false({String.starts_with.go.if(at, ct, Char.is_eq(z, x)) == True{} : Bool}, h2)
    case True{} True{}:
      %char_alike(y, x, e1) : {String.starts_with.go.if(at, ct, Char.is_eq(z, _)) == True{} : Bool}
      %Equal.sym(Bool, Char.is_eq(z, y), True{}, e2) : {String.starts_with.go.if(at, ct, _) == True{} : Bool}
      ih(h1)(h2)

# What begins the beginning of a text begins the text.
def through(a: String, b: String, c: String,
  h1: {String.starts_with.go(a, b) == True{} : Bool},
  h2: {String.starts_with.go(b, c) == True{} : Bool}
) -> {String.starts_with.go(a, c) == True{} : Bool}:
  match a b c:
    case SNil{} _ _:
      {==}
    case SCon{x, at} SNil{} _:
      P.not_false({String.starts_with.go(SCon{x, at}, c) == True{} : Bool}, h1)
    case SCon{x, at} SCon{y, bt} SNil{}:
      P.not_false({False{} == True{} : Bool}, h2)
    case SCon{+x, +at} SCon{+y, +bt} SCon{+z, +ct}:
      through_step(Char.is_eq(y, x), Char.is_eq(z, y), x, y, z, at, bt, ct, {==}, {==}, h1, h2, k1 => k2 => through(at, bt, ct, k1, k2))

# Owning and writing
# ------------------

def spread(u: Bool, s: Bool, v: Bool, -t: Bool, e: {Bool.or(s, t) == True{} : Bool}) -> {Bool.or(Bool.or(u, s), Bool.or(v, t)) == True{} : Bool}:
  match u s v:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      e

# Owning `b` is owning `a` when `a` is the path `b` covers.
def onto(-a: String, -b: String, -p: String, e: {a == p : String}, h: {D.covers(b, p) == True{} : Bool}) -> {D.covers(b, a) == True{} : Bool}:
  %Equal.sym(String, a, p, e) : {D.covers(b, _) == True{} : Bool}
  h

def both_step(
  qa: Bool, qb: Bool, +a: String, +b: String, +p: String,
  ea: {String.eq(a, p) == qa : Bool},
  eb: {String.eq(b, p) == qb : Bool},
  +h1: {Bool.or(qa, Bool.and(D.is_folder(a), String.starts_with.go(a, p))) == True{} : Bool},
  +h2: {Bool.or(qb, Bool.and(D.is_folder(b), String.starts_with.go(b, p))) == True{} : Bool},
  w1: {D.covers(a, p) == True{} : Bool},
  w2: {D.covers(b, p) == True{} : Bool}
) -> {D.clash(a, b) == True{} : Bool}:
  match qa qb:
    case True{} _:
      %Equal.sym(Bool, D.covers(b, a), True{}, onto(a, b, p, P.alike(a, p, ea), w2)) : {Bool.or(D.covers(a, b), _) == True{} : Bool}
      P.or_true(D.covers(a, b))
    case False{} True{}:
      %Equal.sym(Bool, D.covers(a, b), True{}, onto(b, a, p, P.alike(b, p, eb), w1)) : {Bool.or(_, D.covers(b, a)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, D.is_folder(a), True{}, and_left(D.is_folder(a), String.starts_with.go(a, p), h1)) : {Bool.or(Bool.or(String.eq(a, b), Bool.and(_, String.starts_with.go(a, b))), Bool.or(String.eq(b, a), Bool.and(D.is_folder(b), String.starts_with.go(b, a)))) == True{} : Bool}
      %Equal.sym(Bool, D.is_folder(b), True{}, and_left(D.is_folder(b), String.starts_with.go(b, p), h2)) : {Bool.or(Bool.or(String.eq(a, b), String.starts_with.go(a, b)), Bool.or(String.eq(b, a), Bool.and(_, String.starts_with.go(b, a)))) == True{} : Bool}
      spread(String.eq(a, b), String.starts_with.go(a, b), String.eq(b, a), String.starts_with.go(b, a),
        in_line(a, b, p, and_right(D.is_folder(a), String.starts_with.go(a, p), h1), and_right(D.is_folder(b), String.starts_with.go(b, p), h2)))

# Two entries that cover the same path clash.
def both(+a: String, +b: String, +p: String, +h1: {D.covers(a, p) == True{} : Bool}, +h2: {D.covers(b, p) == True{} : Bool}) -> {D.clash(a, b) == True{} : Bool}:
  both_step(String.eq(a, p), String.eq(b, p), a, b, p, {==}, {==}, h1, h2, h1, h2)

def clash_step(
  c: Bool, +a: String, +h: String, -t: List<&2, String>, +p: String,
  ec: {D.covers(h, p) == c : Bool},
  +h1: {D.covers(a, p) == True{} : Bool},
  h2: {Bool.or(c, D.may_write(t, p)) == True{} : Bool},
  ih: {D.may_write(t, p) == True{} : Bool} -> {D.clashes(a, t) == True{} : Bool}
) -> {Bool.or(D.clash(a, h), D.clashes(a, t)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, D.clash(a, h), True{}, both(a, h, p, h1, ec)) : {Bool.or(_, D.clashes(a, t)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, D.clashes(a, t), True{}, ih(h2)) : {Bool.or(D.clash(a, h), _) == True{} : Bool}
      P.or_true(D.clash(a, h))

# An entry that covers a path clashes with any set of entries that may write it.
def clash_in(+a: String, bs: List<&2, String>, +p: String, +h1: {D.covers(a, p) == True{} : Bool}, h2: {D.may_write(bs, p) == True{} : Bool}) -> {D.clashes(a, bs) == True{} : Bool}:
  match bs:
    case Nil{}:
      h2
    case Con{+h, +t}:
      clash_step(D.covers(h, p), a, h, t, p, {==}, h1, h2, k => clash_in(a, t, p, h1, k))

def meet_step(
  c: Bool, +h: String, -t: List<&2, String>, +bs: List<&2, String>, +p: String,
  ec: {D.covers(h, p) == c : Bool},
  h1: {Bool.or(c, D.may_write(t, p)) == True{} : Bool},
  h2: {D.may_write(bs, p) == True{} : Bool},
  ih: {D.may_write(t, p) == True{} : Bool} -> {D.may_write(bs, p) == True{} : Bool} -> {D.overlap(t, bs) == True{} : Bool}
) -> {Bool.or(D.clashes(h, bs), D.overlap(t, bs)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, D.clashes(h, bs), True{}, clash_in(h, bs, p, ec, h2)) : {Bool.or(_, D.overlap(t, bs)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, D.overlap(t, bs), True{}, ih(h1)(h2)) : {Bool.or(D.clashes(h, bs), _) == True{} : Bool}
      P.or_true(D.clashes(h, bs))

# Two sets of entries that may both write a path overlap.
def meet(xs: List<&2, String>, +bs: List<&2, String>, +p: String, h1: {D.may_write(xs, p) == True{} : Bool}, h2: {D.may_write(bs, p) == True{} : Bool}) -> {D.overlap(xs, bs) == True{} : Bool}:
  match xs:
    case Nil{}:
      h1
    case Con{+h, +t}:
      meet_step(D.covers(h, p), h, t, bs, p, {==}, h1, h2, k1 => k2 => meet(t, bs, p, k1, k2))

def trample_step(
  m: Bool, +a: List<&2, String>, +b: List<&2, String>, +path: String,
  em: {D.may_write(b, path) == m : Bool},
  apart: {D.overlap(a, b) == False{} : Bool},
  mine: {D.may_write(a, path) == True{} : Bool}
) -> {m == False{} : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, D.overlap(a, b), False{}, Equal.sym(Bool, D.overlap(a, b), True{}, meet(a, b, path, mine, em)), apart)

def Laws.no_trample(a, b, path, apart, mine):
  trample_step(D.may_write(b, path), a, b, path, {==}, apart, mine)

def reach_step(
  q1: Bool, q2: Bool, +pe: String, +e: String, +p: String,
  e1: {String.eq(pe, e) == q1 : Bool},
  e2: {String.eq(e, p) == q2 : Bool},
  +h1: {Bool.or(q1, Bool.and(D.is_folder(pe), String.starts_with.go(pe, e))) == True{} : Bool},
  +h2: {Bool.or(q2, Bool.and(D.is_folder(e), String.starts_with.go(e, p))) == True{} : Bool},
  w2: {D.covers(e, p) == True{} : Bool}
) -> {D.covers(pe, p) == True{} : Bool}:
  match q1 q2:
    case True{} _:
      %Equal.sym(String, pe, e, P.alike(pe, e, e1)) : {D.covers(_, p) == True{} : Bool}
      w2
    case False{} True{}:
      %P.alike(e, p, e2) : {D.covers(pe, _) == True{} : Bool}
      %Equal.sym(Bool, String.eq(pe, e), False{}, e1) : {Bool.or(_, Bool.and(D.is_folder(pe), String.starts_with.go(pe, e))) == True{} : Bool}
      h1
    case False{} False{}:
      %Equal.sym(Bool, D.is_folder(pe), True{}, and_left(D.is_folder(pe), String.starts_with.go(pe, e), h1)) : {Bool.or(String.eq(pe, p), Bool.and(_, String.starts_with.go(pe, p))) == True{} : Bool}
      %Equal.sym(Bool, String.starts_with.go(pe, p), True{}, through(pe, e, p, and_right(D.is_folder(pe), String.starts_with.go(pe, e), h1), and_right(D.is_folder(e), String.starts_with.go(e, p), h2))) : {Bool.or(String.eq(pe, p), _) == True{} : Bool}
      P.or_true(String.eq(pe, p))

# Owning what owns a path is owning the path.
def reach(+pe: String, +e: String, +p: String, +h1: {D.covers(pe, e) == True{} : Bool}, +h2: {D.covers(e, p) == True{} : Bool}) -> {D.covers(pe, p) == True{} : Bool}:
  reach_step(String.eq(pe, e), String.eq(e, p), pe, e, p, {==}, {==}, h1, h2, h2)

def hand_step(
  c: Bool, +pe: String, -t: List<&2, String>, +e: String, +p: String,
  ec: {D.covers(pe, e) == c : Bool},
  h1: {Bool.or(c, D.may_write(t, e)) == True{} : Bool},
  +h2: {D.covers(e, p) == True{} : Bool},
  ih: {D.may_write(t, e) == True{} : Bool} -> {D.may_write(t, p) == True{} : Bool}
) -> {Bool.or(D.covers(pe, p), D.may_write(t, p)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, D.covers(pe, p), True{}, reach(pe, e, p, ec, h2)) : {Bool.or(_, D.may_write(t, p)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, D.may_write(t, p), True{}, ih(h1)) : {Bool.or(D.covers(pe, p), _) == True{} : Bool}
      P.or_true(D.covers(pe, p))

# Who may write an entry may write every path the entry covers.
def hand(pes: List<&2, String>, +e: String, +p: String, h1: {D.may_write(pes, e) == True{} : Bool}, +h2: {D.covers(e, p) == True{} : Bool}) -> {D.may_write(pes, p) == True{} : Bool}:
  match pes:
    case Nil{}:
      h1
    case Con{+pe, +t}:
      hand_step(D.covers(pe, e), pe, t, e, p, {==}, h1, h2, k => hand(t, e, p, k, h2))

def within_step(
  c: Bool, +e: String, -t: List<&2, String>, +pes: List<&2, String>, +p: String,
  ec: {D.covers(e, p) == c : Bool},
  +within: {Bool.and(D.may_write(pes, e), D.inside(t, D.Only{pes})) == True{} : Bool},
  mine: {Bool.or(c, D.may_write(t, p)) == True{} : Bool},
  ih: {D.inside(t, D.Only{pes}) == True{} : Bool} -> {D.may_write(t, p) == True{} : Bool} -> {D.may_write(pes, p) == True{} : Bool}
) -> {D.may_write(pes, p) == True{} : Bool}:
  match c:
    case True{}:
      hand(pes, e, p, and_left(D.may_write(pes, e), D.inside(t, D.Only{pes}), within), ec)
    case False{}:
      ih(and_right(D.may_write(pes, e), D.inside(t, D.Only{pes}), within))(mine)

def within_only(entries: List<&2, String>, +pes: List<&2, String>, +p: String,
  within: {D.inside(entries, D.Only{pes}) == True{} : Bool},
  mine: {D.may_write(entries, p) == True{} : Bool}
) -> {D.may_write(pes, p) == True{} : Bool}:
  match entries:
    case Nil{}:
      P.not_false({D.may_write(pes, p) == True{} : Bool}, mine)
    case Con{+e, +t}:
      within_step(D.covers(e, p), e, t, pes, p, {==}, within, mine, k1 => k2 => within_only(t, pes, p, k1, k2))

def Laws.stays_inside(entries, parent, path, within, mine):
  match parent:
    case D.All{}:
      {==}
    case D.Only{pes}:
      within_only(entries, pes, path, within, mine)

# Whether a cut is made
# ---------------------

def IsDivide(v: D.Verdict) -> Type:
  match v:
    case D.Divide{}:
      Unit
    case D.Refuse{why}:
      Empty

def divide_is(-v: D.Verdict, e: {D.Divide{} == v : D.Verdict}) -> IsDivide(v):
  %e : IsDivide(_)
  Unit{}

# A guard that let a cut through did not find what it guards against.
def let_through(bad: Bool, -why: D.Reason, -rest: D.Verdict, e: {D.guard(bad, why, rest) == D.Divide{} : D.Verdict}) -> {bad == False{} : Bool}:
  match bad:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, divide_is(D.Refuse{why}, Equal.sym(D.Verdict, D.Refuse{why}, D.Divide{}, e)))

# A guard that let a cut through left the rest to say so.
def and_then(bad: Bool, -why: D.Reason, -rest: D.Verdict, e: {D.guard(bad, why, rest) == D.Divide{} : D.Verdict}) -> {rest == D.Divide{} : D.Verdict}:
  match bad:
    case False{}:
      e
    case True{}:
      Empty.absurd({rest == D.Divide{} : D.Verdict}, divide_is(D.Refuse{why}, Equal.sym(D.Verdict, D.Refuse{why}, D.Divide{}, e)))

# A cut that is made got past every guard.
def past_1(b1: Bool, -b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {b1 == False{} : Bool}:
  let_through(b1, D.TooDeep{}, D.guard(b2, D.NoParts{}, D.guard(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))))), e)

def rest_1(b1: Bool, -b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {D.guard(b2, D.NoParts{}, D.guard(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))))) == D.Divide{} : D.Verdict}:
  and_then(b1, D.TooDeep{}, D.guard(b2, D.NoParts{}, D.guard(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))))), e)

def rest_2(b1: Bool, b2: Bool, -b3: Bool, -b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {D.guard(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{})))) == D.Divide{} : D.Verdict}:
  and_then(b2, D.NoParts{}, D.guard(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{})))), rest_1(b1, b2, b3, b4, b5, b6, e))

def rest_3(b1: Bool, b2: Bool, b3: Bool, -b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))) == D.Divide{} : D.Verdict}:
  and_then(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))), rest_2(b1, b2, b3, b4, b5, b6, e))

def rest_4(b1: Bool, b2: Bool, b3: Bool, b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{})) == D.Divide{} : D.Verdict}:
  and_then(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{})), rest_3(b1, b2, b3, b4, b5, b6, e))

def rest_5(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {D.guard(b6, D.Trample{}, D.Divide{}) == D.Divide{} : D.Verdict}:
  and_then(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}), rest_4(b1, b2, b3, b4, b5, b6, e))

def past_3(b1: Bool, b2: Bool, b3: Bool, -b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {b3 == False{} : Bool}:
  let_through(b3, D.SameName{}, D.guard(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}))), rest_2(b1, b2, b3, b4, b5, b6, e))

def past_4(b1: Bool, b2: Bool, b3: Bool, b4: Bool, -b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {b4 == False{} : Bool}:
  let_through(b4, D.SharedLaw{}, D.guard(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{})), rest_3(b1, b2, b3, b4, b5, b6, e))

def past_5(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, -b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {b5 == False{} : Bool}:
  let_through(b5, D.Outside{}, D.guard(b6, D.Trample{}, D.Divide{}), rest_4(b1, b2, b3, b4, b5, b6, e))

def past_6(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, e: {D.verdict(b1, b2, b3, b4, b5, b6) == D.Divide{} : D.Verdict}) -> {b6 == False{} : Bool}:
  let_through(b6, D.Trample{}, D.Divide{}, rest_5(b1, b2, b3, b4, b5, b6, e))

# What is not true is false.
def not_so(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      P.not_false({True{} == False{} : Bool}, e)

def both_true(a: Bool, b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a b:
    case True{} True{}:
      ({==}, {==})
    case True{} False{}:
      (P.not_false({True{} == True{} : Bool}, e), e)
    case False{} _:
      (e, P.not_false({b == True{} : Bool}, e))

def neither(a: Bool, b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool} & {b == False{} : Bool}:
  match a b:
    case False{} False{}:
      ({==}, {==})
    case False{} True{}:
      (P.not_true({False{} == False{} : Bool}, e), e)
    case True{} _:
      (e, P.not_true({b == False{} : Bool}, e))

# One of the agents may write a path: then none of the others that share no file with it may.
def none_step(
  -h: List<&2, String>, -t: List<&2, List<&2, String>>, -path: String,
  eh: {D.may_write(h, path) == False{} : Bool},
  et: {D.writers(t, path) == 0n : Nat}
) -> {D.writers(h <> t, path) == 0n : Nat}:
  %Equal.sym(Bool, D.may_write(h, path), False{}, eh) : {Nat.add(D.one_if(_), D.writers(t, path)) == 0n : Nat}
  et

def none_write(+mine: List<&2, String>, others: List<&2, List<&2, String>>, +path: String,
  +apart: {D.shares(mine, others) == False{} : Bool},
  +writes: {D.may_write(mine, path) == True{} : Bool}
) -> {D.writers(others, path) == 0n : Nat}:
  match others:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      none_step(h, t, path,
        Laws.no_trample(mine, h, path, P.or_left(D.overlap(mine, h), D.shares(mine, t), apart), writes),
        none_write(mine, t, path, P.or_right(D.overlap(mine, h), D.shares(mine, t), apart), writes))

def writer_step(
  w: Bool, +h: List<&2, String>, +t: List<&2, List<&2, String>>, +path: String,
  ew: {D.may_write(h, path) == w : Bool},
  +apart: {D.shares(h, t) == False{} : Bool},
  ih: {Nat.is_le(D.writers(t, path), 1n) == True{} : Bool}
) -> {Nat.is_le(Nat.add(D.one_if(w), D.writers(t, path)), 1n) == True{} : Bool}:
  match w:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Nat, D.writers(t, path), 0n, none_write(h, t, path, apart, ew)) : {Nat.is_le(1n+_, 1n) == True{} : Bool}
      {==}

def Laws.one_writer(owns, path, apart):
  match owns:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      writer_step(D.may_write(h, path), h, t, path, {==},
        not_so(D.shares(h, t), and_left(Bool.not(D.shares(h, t)), D.disjoint(t), apart)),
        Laws.one_writer(t, path, and_right(Bool.not(D.shares(h, t)), D.disjoint(t), apart)))

def Laws.parts_never_share_a_file(depth, limit, parent, pieces, cut):
  not_not(D.disjoint(D.owns_of(pieces)), past_6(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, D.Piece, pieces), Bool.not(D.distinct(D.names_of(pieces))), Bool.not(D.distinct(D.laws_of(pieces))), Bool.not(D.all_inside(D.owns_of(pieces), parent)), Bool.not(D.disjoint(D.owns_of(pieces))), cut))

def Laws.parts_stay_inside(depth, limit, parent, pieces, cut):
  not_not(D.all_inside(D.owns_of(pieces), parent), past_5(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, D.Piece, pieces), Bool.not(D.distinct(D.names_of(pieces))), Bool.not(D.distinct(D.laws_of(pieces))), Bool.not(D.all_inside(D.owns_of(pieces), parent)), Bool.not(D.disjoint(D.owns_of(pieces))), cut))

def Laws.one_prover_per_law(depth, limit, parent, pieces, cut):
  (not_not(D.distinct(D.laws_of(pieces)), past_4(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, D.Piece, pieces), Bool.not(D.distinct(D.names_of(pieces))), Bool.not(D.distinct(D.laws_of(pieces))), Bool.not(D.all_inside(D.owns_of(pieces), parent)), Bool.not(D.disjoint(D.owns_of(pieces))), cut)),
   not_not(D.distinct(D.names_of(pieces)), past_3(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, D.Piece, pieces), Bool.not(D.distinct(D.names_of(pieces))), Bool.not(D.distinct(D.laws_of(pieces))), Bool.not(D.all_inside(D.owns_of(pieces), parent)), Bool.not(D.disjoint(D.owns_of(pieces))), cut)))

def Laws.cutting_ends(depth, limit, parent, pieces, cut):
  not_not(Nat.is_lt(depth, limit), past_1(Bool.not(Nat.is_lt(depth, limit)), List.is_empty(&2, D.Piece, pieces), Bool.not(D.distinct(D.names_of(pieces))), Bool.not(D.distinct(D.laws_of(pieces))), Bool.not(D.all_inside(D.owns_of(pieces), parent)), Bool.not(D.disjoint(D.owns_of(pieces))), cut))

def Laws.nothing_else_is_asked(depth, limit, parent, h, t, shallow, names, laws, within, apart):
  %Equal.sym(Bool, Nat.is_lt(depth, limit), True{}, shallow) : {D.verdict(Bool.not(_), False{}, Bool.not(D.distinct(D.names_of(h <> t))), Bool.not(D.distinct(D.laws_of(h <> t))), Bool.not(D.all_inside(D.owns_of(h <> t), parent)), Bool.not(D.disjoint(D.owns_of(h <> t)))) == D.Divide{} : D.Verdict}
  %Equal.sym(Bool, D.distinct(D.names_of(h <> t)), True{}, names) : {D.verdict(False{}, False{}, Bool.not(_), Bool.not(D.distinct(D.laws_of(h <> t))), Bool.not(D.all_inside(D.owns_of(h <> t), parent)), Bool.not(D.disjoint(D.owns_of(h <> t)))) == D.Divide{} : D.Verdict}
  %Equal.sym(Bool, D.distinct(D.laws_of(h <> t)), True{}, laws) : {D.verdict(False{}, False{}, False{}, Bool.not(_), Bool.not(D.all_inside(D.owns_of(h <> t), parent)), Bool.not(D.disjoint(D.owns_of(h <> t)))) == D.Divide{} : D.Verdict}
  %Equal.sym(Bool, D.all_inside(D.owns_of(h <> t), parent), True{}, within) : {D.verdict(False{}, False{}, False{}, False{}, Bool.not(_), Bool.not(D.disjoint(D.owns_of(h <> t)))) == D.Divide{} : D.Verdict}
  %Equal.sym(Bool, D.disjoint(D.owns_of(h <> t)), True{}, apart) : {D.verdict(False{}, False{}, False{}, False{}, False{}, Bool.not(_)) == D.Divide{} : D.Verdict}
  {==}

# What the halves run on
# ----------------------

def Laws.choice_runs(c, rest, session):
  {==}

def Laws.no_choice_follows_session(session):
  {==}

def Laws.same_follows_session(session):
  {==}

def Laws.division_words():
  (({==}, {==}), {==})

def Laws.default_agent_words():
  ({==}, {==})

def Laws.a_failed_check_never_fits(code, c, why, said):
  ({==}, {==})
