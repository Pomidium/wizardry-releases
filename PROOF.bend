# Proofs of the laws in LAWS.bend. `bend PROOF.bend` must print ALL PROOFS CHECK before a commit.

import Base
import ./bend/core.bend as C
import ./LAWS.bend as Laws

# Removing the entries named in `bad` leaves no name in `bad`.
def named_step(
  b: Bool, -name: String, -path: String, -rest: List<&2, C.Entry>, -bad: List<&2, String>,
  eb: {C.has(bad, name) == b : Bool},
  ih: {C.overlaps(C.names(rest), bad) == False{} : Bool}
) -> {C.overlaps(C.names(C.keep_entry(Bool.not(b), C.Entry{name, path}, rest)), bad) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, C.has(bad, name), False{}, eb) : {Bool.or(_, C.overlaps(C.names(rest), bad)) == False{} : Bool}
      ih

def named_clean(es: List<&2, C.Entry>, +bad: List<&2, String>) ->
  {C.overlaps(C.names(C.without_named(es, bad)), bad) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{+name, path}, t}:
      named_step(C.has(bad, name), name, path, C.without_named(t, bad), bad, {==}, named_clean(t, bad))

def Laws.disabled_never_load(shipped, found, disabled):
  named_clean(List.append(&2, C.Entry, C.shipped_kept(shipped, found), found), disabled)

def Laws.home_replaces_shipped(shipped, found):
  named_clean(shipped, C.names(found))

# Removing the names in `bad` leaves no name in `bad`.
def clean_step(
  b: Bool, -h: String, -rest: List<&2, String>, -bad: List<&2, String>,
  eb: {C.has(bad, h) == b : Bool},
  ih: {C.overlaps(rest, bad) == False{} : Bool}
) -> {C.overlaps(C.keep_if(Bool.not(b), h, rest), bad) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, C.has(bad, h), False{}, eb) : {Bool.or(_, C.overlaps(rest, bad)) == False{} : Bool}
      ih

def clean(xs: List<&2, String>, +bad: List<&2, String>) -> {C.overlaps(C.without(xs, bad), bad) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      clean_step(C.has(bad, h), h, C.without(t, bad), bad, {==}, clean(t, bad))

def Laws.focus_stays(drop):
  clean(drop, ["focus"])

def Laws.dashes_pass(rest):
  {==}

# An argument that is kept is not one that resumes a session.
def strip_step(
  s: Bool, r: Bool, c: Bool, -h: String, -rest: List<&2, String>,
  er: {C.resumes(h) == r : Bool},
  ih: {C.any_resumes(rest) == False{} : Bool}
) -> {C.any_resumes(C.keep_if(Bool.not(Bool.or(s, Bool.or(r, c))), h, rest)) == False{} : Bool}:
  match s r c:
    case True{} _ _:
      ih
    case False{} True{} _:
      ih
    case False{} False{} True{}:
      ih
    case False{} False{} False{}:
      %Equal.sym(Bool, C.resumes(h), False{}, er) : {Bool.or(_, C.any_resumes(rest)) == False{} : Bool}
      ih

def Laws.restart_forgets_resume(xs, skip):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      strip_step(skip, C.resumes(h), C.chooses(h), h, C.strip(t, Bool.and(Bool.not(skip), C.chooses(h))), {==},
        Laws.restart_forgets_resume(t, Bool.and(Bool.not(skip), C.chooses(h))))

# What is left of a text after the cut, with its ellipsis, fits.
def cut_fits(s: String, p: Nat) -> {C.fits(String.append(String.take(s, p), "…"), 1n+p) == True{} : Bool}:
  match s p:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+q:
      cut_fits(t, q)

def clip_step(
  b: Bool, -s: String, -p: Nat,
  eb: {C.fits(s, 1n+p) == b : Bool},
  cut: {C.fits(String.append(String.take(s, p), "…"), 1n+p) == True{} : Bool}
) -> {C.fits(Bool.pick(String, b, s, C.clip_at(s, 1n+p)), 1n+p) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      cut

def Laws.clip_fits(s, p):
  clip_step(C.fits(s, 1n+p), s, p, {==}, cut_fits(s, p))

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

# Counting on top of `acc` is the length plus `acc`.
def count_len(xs: List<&2, String>, -acc: Nat) -> {C.count(xs, acc) == Nat.add(List.length(&2, String, xs), acc) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, C.count(t, 1n+acc), Nat.add(List.length(&2, String, t), 1n+acc),
        1n+Nat.add(List.length(&2, String, t), acc),
        count_len(t, 1n+acc), add_succ(List.length(&2, String, t), acc))

def Laws.view_counts_all(lines, limit):
  match lines limit:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      %add_zero(List.length(&2, String, t)) : {C.count(t, 1n) == 1n+_ : Nat}
      Equal.trans(Nat, C.count(t, 1n), Nat.add(List.length(&2, String, t), 1n),
        1n+Nat.add(List.length(&2, String, t), 0n),
        count_len(t, 1n), add_succ(List.length(&2, String, t), 0n))
    case Con{h, +t} 1n+p:
      %Laws.view_counts_all(t, p) : {1n+Nat.add(List.length(&2, String, C.first(t, p)), C.beyond(t, p)) == 1n+_ : Nat}
      {==}

# Names are themselves, and names that compare equal are the same name
# -------------------------------------------------------------------

def CmpIsEq(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Empty

# Whatever equals EQ is EQ.
def eq_is(-c: Cmp, e: {EQ{} == c : Cmp}) -> CmpIsEq(c):
  %e : CmpIsEq(_)
  Unit{}

def not_lt(-A: Type, e: {LT{} == EQ{} : Cmp}) -> A:
  Empty.absurd(A, eq_is(LT{}, Equal.sym(Cmp, LT{}, EQ{}, e)))

def not_gt(-A: Type, e: {GT{} == EQ{} : Cmp}) -> A:
  Empty.absurd(A, eq_is(GT{}, Equal.sym(Cmp, GT{}, EQ{}, e)))

def BoolIsTrue(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def true_is(-b: Bool, e: {True{} == b : Bool}) -> BoolIsTrue(b):
  %e : BoolIsTrue(_)
  Unit{}

def not_false(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, true_is(False{}, Equal.sym(Bool, False{}, True{}, e)))

def bit_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def word_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{b, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          bit_refl(b)

def bit_sound(-p: Nat, a: Bool, b: Bool, -t: Word(p), e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {WCon{a, t} == WCon{b, t} : Word(1n+p)}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      not_lt({WCon{False{}, t} == WCon{True{}, t} : Word(1n+p)}, e)
    case True{} False{}:
      not_gt({WCon{True{}, t} == WCon{False{}, t} : Word(1n+p)}, e)
    case True{} True{}:
      {==}

def word_step(
  -p: Nat, a: Bool, b: Bool, -at: Word(p), -bt: Word(p), r: Cmp,
  er: {Word.cmp(p, at, bt) == r : Cmp},
  e: {Word.cmp.fin(a, b, r) == EQ{} : Cmp},
  ih: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)}
) -> {WCon{a, at} == WCon{b, bt} : Word(1n+p)}:
  match r:
    case LT{}:
      not_lt({WCon{a, at} == WCon{b, bt} : Word(1n+p)}, e)
    case EQ{}:
      %ih(er) : {WCon{a, at} == WCon{b, _} : Word(1n+p)}
      bit_sound(p, a, b, at, e)
    case GT{}:
      not_gt({WCon{a, at} == WCon{b, bt} : Word(1n+p)}, e)

def word_sound(+n: Nat, a: Word(n), b: Word(n), e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          word_step(p, ab, bb, at, bt, Word.cmp(p, at, bt), {==}, e, e2 => word_sound(p, at, bt, e2))

# A comparison already decided stays decided.
def order_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def order_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{U32{x}}, t}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word_refl(32n, x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      order_refl(t)

# A name is itself.
def same(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def order_step(
  -x: Word(32n), -y: Word(32n), +t1: String, +t2: String, r: Cmp,
  er: {Word.cmp(32n, x, y) == r : Cmp},
  e: {String.order.go(t1, t2, r) == EQ{} : Cmp},
  ws: {Word.cmp(32n, x, y) == EQ{} : Cmp} -> {x == y : Word(32n)},
  ih: {String.order.go(t1, t2, EQ{}) == EQ{} : Cmp} -> {t1 == t2 : String}
) -> {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String}:
  match r:
    case LT{}:
      not_lt({SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String},
        Equal.trans(Cmp, LT{}, String.order.go(t1, t2, LT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, order_lt(t1, t2)), e))
    case EQ{}:
      %ih(e) : {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, _} : String}
      %ws(er) : {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{_}}, t1} : String}
      {==}
    case GT{}:
      not_gt({SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String},
        Equal.trans(Cmp, GT{}, String.order.go(t1, t2, GT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, order_gt(t1, t2)), e))

def order_sound(a: String, b: String, e: {String.order.go(a, b, EQ{}) == EQ{} : Cmp}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      not_lt({SNil{} == SCon{h, t} : String}, e)
    case SCon{h, t} SNil{}:
      not_gt({SCon{h, t} == SNil{} : String}, e)
    case SCon{Chr{U32{+x}}, +t1} SCon{Chr{U32{+y}}, +t2}:
      order_step(x, y, t1, t2, Word.cmp(32n, x, y), {==}, e, e2 => word_sound(32n, x, y, e2), e2 => order_sound(t1, t2, e2))

def is_eq_step(-a: String, -b: String, r: Cmp, er: {String.order.go(a, b, EQ{}) == r : Cmp}, e: {Cmp.is_eq(r) == True{} : Bool}) -> {String.order.go(a, b, EQ{}) == EQ{} : Cmp}:
  match r:
    case LT{}:
      not_false({String.order.go(a, b, EQ{}) == EQ{} : Cmp}, e)
    case EQ{}:
      er
    case GT{}:
      not_false({String.order.go(a, b, EQ{}) == EQ{} : Cmp}, e)

# Two names that compare equal are the same name.
def alike(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  order_sound(a, b, is_eq_step(a, b, String.order.go(a, b, EQ{}), {==}, e))

# Laws that hold by running the code
# ----------------------------------

def Laws.cap_starts_plain():
  {==}

def Laws.small_cap_stays_put():
  {==}

def Laws.title_examples():
  ({==}, {==})

def Laws.update_words():
  (({==}, {==}), {==})

def Laws.hidden_files_skip(rest, folder, entry):
  ({==}, {==})

def Laws.title_wins(c, rest, native, name, owner):
  {==}

def Laws.native_keeps_name(name, owner):
  {==}

def Laws.expanded_shows_all(lines, limit):
  {==}

def Laws.pi_adds_nothing(rest, sessions, themes, pair):
  {==}

def Laws.raw_runs_as_written(command):
  {==}

def Laws.prompt_is_only_base(base):
  {==}

def Laws.switch_settles(on, loaded):
  match on loaded:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Booleans
# --------

def not_true(-A: Type, e: {True{} == False{} : Bool}) -> A:
  not_false(A, Equal.sym(Bool, True{}, False{}, e))

def or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# When neither of two holds, the first does not.
def or_left(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      e

# When neither of two holds, the second does not.
def or_right(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      not_true({b == False{} : Bool}, e)

# Names in lists
# --------------

# A name is in two lists joined when it is in either.
def has_append(xs: List<&2, String>, -ys: List<&2, String>, +x: String) ->
  {C.has(List.append(&2, String, xs, ys), x) == Bool.or(C.has(xs, x), C.has(ys, x)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Bool, C.has(List.append(&2, String, t, ys), x), Bool.or(C.has(t, x), C.has(ys, x)), has_append(t, ys, x)) : {Bool.or(String.eq(h, x), _) == Bool.or(Bool.or(String.eq(h, x), C.has(t, x)), C.has(ys, x)) : Bool}
      or_assoc(String.eq(h, x), C.has(t, x), C.has(ys, x))

# A list has the same of two names that are the same name.
def has_same(-bad: List<&2, String>, +h: String, +x: String, q: {String.eq(h, x) == True{} : Bool}) -> {C.has(bad, h) == C.has(bad, x) : Bool}:
  %alike(h, x, q) : {C.has(bad, h) == C.has(bad, _) : Bool}
  {==}

def gone_step(
  b: Bool, q: Bool, +h: String, +x: String, -bad: List<&2, String>, -rest: List<&2, String>,
  eb: {C.has(bad, h) == b : Bool},
  eq: {String.eq(h, x) == q : Bool},
  e: {C.has(bad, x) == True{} : Bool},
  ih: {C.has(rest, x) == False{} : Bool}
) -> {C.has(C.keep_if(Bool.not(b), h, rest), x) == False{} : Bool}:
  match b q:
    case True{} _:
      ih
    case False{} False{}:
      %Equal.sym(Bool, String.eq(h, x), False{}, eq) : {Bool.or(_, C.has(rest, x)) == False{} : Bool}
      ih
    case False{} True{}:
      not_false({C.has(h <> rest, x) == False{} : Bool},
        Equal.trans(Bool, False{}, C.has(bad, x), True{},
          Equal.trans(Bool, False{}, C.has(bad, h), C.has(bad, x), Equal.sym(Bool, C.has(bad, h), False{}, eb), has_same(bad, h, x, eq)), e))

# A name among those taken out is not in what is left.
def gone(xs: List<&2, String>, +bad: List<&2, String>, +x: String, +e: {C.has(bad, x) == True{} : Bool}) ->
  {C.has(C.without(xs, bad), x) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      gone_step(C.has(bad, h), String.eq(h, x), h, x, bad, C.without(t, bad), {==}, {==}, e, gone(t, bad, x, e))

def stays_step(
  b: Bool, q: Bool, +h: String, +x: String, -bad: List<&2, String>, -t: List<&2, String>, -rest: List<&2, String>,
  eb: {C.has(bad, h) == b : Bool},
  eq: {String.eq(h, x) == q : Bool},
  inn: {Bool.or(q, C.has(t, x)) == True{} : Bool},
  out: {C.has(bad, x) == False{} : Bool},
  ih: {C.has(t, x) == True{} : Bool} -> {C.has(rest, x) == True{} : Bool}
) -> {C.has(C.keep_if(Bool.not(b), h, rest), x) == True{} : Bool}:
  match b q:
    case True{} True{}:
      not_true({C.has(rest, x) == True{} : Bool},
        Equal.trans(Bool, True{}, C.has(bad, x), False{},
          Equal.trans(Bool, True{}, C.has(bad, h), C.has(bad, x), Equal.sym(Bool, C.has(bad, h), True{}, eb), has_same(bad, h, x, eq)), out))
    case True{} False{}:
      ih(inn)
    case False{} True{}:
      %Equal.sym(Bool, String.eq(h, x), True{}, eq) : {Bool.or(_, C.has(rest, x)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, String.eq(h, x), False{}, eq) : {Bool.or(_, C.has(rest, x)) == True{} : Bool}
      ih(inn)

# A name that is there, and not among those taken out, is in what is left.
def stays(xs: List<&2, String>, +bad: List<&2, String>, +x: String, inn: {C.has(xs, x) == True{} : Bool}, +out: {C.has(bad, x) == False{} : Bool}) ->
  {C.has(C.without(xs, bad), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      inn
    case Con{+h, +t}:
      stays_step(C.has(bad, h), String.eq(h, x), h, x, bad, t, C.without(t, bad), {==}, {==}, inn, out, e => stays(t, bad, x, e, out))

def add_has_step(b: Bool, +xs: List<&2, String>, +x: String, eb: {C.has(xs, x) == b : Bool}) ->
  {C.has(Bool.pick(List<&2, String>, b, xs, List.append(&2, String, xs, [x])), x) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      %Equal.sym(Bool, C.has(List.append(&2, String, xs, [x]), x), Bool.or(C.has(xs, x), C.has([x], x)), has_append(xs, [x], x)) : {_ == True{} : Bool}
      %Equal.sym(Bool, String.eq(x, x), True{}, same(x)) : {Bool.or(C.has(xs, x), Bool.or(_, False{})) == True{} : Bool}
      or_true(C.has(xs, x))

# A name added to a list is in it.
def add_has(+xs: List<&2, String>, +x: String) -> {C.has(C.add(xs, x), x) == True{} : Bool}:
  add_has_step(C.has(xs, x), xs, x, {==})

def add_keeps_step(b: Bool, +xs: List<&2, String>, -h: String, +x: String, e: {C.has(xs, x) == True{} : Bool}) ->
  {C.has(Bool.pick(List<&2, String>, b, xs, List.append(&2, String, xs, [h])), x) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      %Equal.sym(Bool, C.has(List.append(&2, String, xs, [h]), x), Bool.or(C.has(xs, x), C.has([h], x)), has_append(xs, [h], x)) : {_ == True{} : Bool}
      %Equal.sym(Bool, C.has(xs, x), True{}, e) : {Bool.or(_, C.has([h], x)) == True{} : Bool}
      {==}

# Adding a name to a list takes none out.
def add_keeps(+xs: List<&2, String>, +h: String, +x: String, e: {C.has(xs, x) == True{} : Bool}) -> {C.has(C.add(xs, h), x) == True{} : Bool}:
  add_keeps_step(C.has(xs, h), xs, h, x, e)

def add_all_keeps(ys: List<&2, String>, +xs: List<&2, String>, +x: String, e: {C.has(xs, x) == True{} : Bool}) ->
  {C.has(C.add_all(ys, xs), x) == True{} : Bool}:
  match ys:
    case Nil{}:
      e
    case Con{+h, t}:
      add_all_keeps(t, C.add(xs, h), x, add_keeps(xs, h, x, e))

def carry(-xs: List<&2, String>, -h: String, -x: String, a: {h == x : String}, p: {C.has(xs, h) == True{} : Bool}) -> {C.has(xs, x) == True{} : Bool}:
  %a : {C.has(xs, _) == True{} : Bool}
  p

def takes_step(
  q: Bool, +h: String, +x: String, -t: List<&2, String>, -G: Type,
  eq: {String.eq(h, x) == q : Bool},
  inn: {Bool.or(q, C.has(t, x)) == True{} : Bool},
  hit: {h == x : String} -> G,
  ih: {C.has(t, x) == True{} : Bool} -> G
) -> G:
  match q:
    case True{}:
      hit(alike(h, x, eq))
    case False{}:
      ih(inn)

# Every name added is in the list afterwards.
def add_all_takes(ys: List<&2, String>, +xs: List<&2, String>, +x: String, e: {C.has(ys, x) == True{} : Bool}) ->
  {C.has(C.add_all(ys, xs), x) == True{} : Bool}:
  match ys:
    case Nil{}:
      not_false({C.has(xs, x) == True{} : Bool}, e)
    case Con{+h, +t}:
      takes_step(String.eq(h, x), h, x, t, {C.has(C.add_all(t, C.add(xs, h)), x) == True{} : Bool}, {==}, e,
        a => add_all_keeps(t, C.add(xs, h), x, carry(C.add(xs, h), h, x, a, add_has(xs, h))),
        e2 => add_all_takes(t, C.add(xs, h), x, e2))

# The agent's own tools
# ---------------------

def Laws.focus_survives(active, drop, take, there):
  add_all_keeps(take, C.without(active, C.droppable(drop)), "focus",
    stays(active, C.droppable(drop), "focus", there, gone(drop, ["focus"], "focus", {==})))

def Laws.taken_is_active(active, drop, take, name, asked):
  add_all_takes(take, C.without(active, C.droppable(drop)), name, asked)

def Laws.dropped_is_gone(active, drop):
  clean(active, C.droppable(drop))

def Laws.restore_keeps_core(loaded, wanted):
  clean(C.without(loaded, wanted), C.core_plugins())

# Switching plugins off and on
# ----------------------------

def Laws.off_stays_off(defaults, disabled, name):
  gone(defaults, C.add(disabled, name), name, add_has(disabled, name))

# A list of one name has that name.
def one_has(+x: String) -> {C.has([x], x) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(x, x), True{}, same(x)) : {Bool.or(_, False{}) == True{} : Bool}
  {==}

def Laws.on_comes_back(defaults, disabled, name, default):
  stays(defaults, C.without(disabled, [name]), name, default, gone(disabled, [name], name, one_has(name)))

def off_one_step(b: Bool, +disabled: List<&2, String>, -name: String, +other: String, differs: {String.eq(name, other) == False{} : Bool}) ->
  {C.has(Bool.pick(List<&2, String>, b, disabled, List.append(&2, String, disabled, [name])), other) == C.has(disabled, other) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, C.has(List.append(&2, String, disabled, [name]), other), Bool.or(C.has(disabled, other), C.has([name], other)), has_append(disabled, [name], other)) : {_ == C.has(disabled, other) : Bool}
      %Equal.sym(Bool, String.eq(name, other), False{}, differs) : {Bool.or(C.has(disabled, other), Bool.or(_, False{})) == C.has(disabled, other) : Bool}
      or_false(C.has(disabled, other))

def Laws.off_touches_one(disabled, name, other, differs):
  off_one_step(C.has(disabled, name), disabled, name, other, differs)

def swap(-n: String, -h: String, -o: String, a: {n == h : String}, p: {String.eq(n, o) == False{} : Bool}) -> {String.eq(h, o) == False{} : Bool}:
  %a : {String.eq(_, o) == False{} : Bool}
  p

def on_one_step(
  q: Bool, +n: String, +h: String, -o: String, -t: List<&2, String>, -rest: List<&2, String>,
  eq: {String.eq(n, h) == q : Bool},
  differs: {String.eq(n, o) == False{} : Bool},
  ih: {C.has(rest, o) == C.has(t, o) : Bool}
) -> {C.has(C.keep_if(Bool.not(Bool.or(q, False{})), h, rest), o) == Bool.or(String.eq(h, o), C.has(t, o)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, String.eq(h, o), False{}, swap(n, h, o, alike(n, h, eq), differs)) : {C.has(rest, o) == Bool.or(_, C.has(t, o)) : Bool}
      ih
    case False{}:
      %ih : {Bool.or(String.eq(h, o), C.has(rest, o)) == Bool.or(String.eq(h, o), _) : Bool}
      {==}

def Laws.on_touches_one(disabled, name, other, differs):
  match disabled:
    case Nil{}:
      {==}
    case Con{+h, t}:
      on_one_step(String.eq(name, h), name, h, other, t, C.without(t, [name]), {==}, differs, Laws.on_touches_one(t, name, other, differs))

# What loads at boot
# ------------------

def names_without_step(b: Bool, -name: String, -path: String, -rest: List<&2, C.Entry>, -other: List<&2, String>,
  ih: {C.names(rest) == other : List<&2, String>}
) -> {C.names(C.keep_entry(b, C.Entry{name, path}, rest)) == C.keep_if(b, name, other) : List<&2, String>}:
  match b:
    case False{}:
      ih
    case True{}:
      %ih : {name <> C.names(rest) == name <> _ : List<&2, String>}
      {==}

# Taking entries out by name is taking their names out.
def names_without(es: List<&2, C.Entry>, +bad: List<&2, String>) ->
  {C.names(C.without_named(es, bad)) == C.without(C.names(es), bad) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{+name, path}, t}:
      names_without_step(Bool.not(C.has(bad, name)), name, path, C.without_named(t, bad), C.without(C.names(t), bad), names_without(t, bad))

def names_append(a: List<&2, C.Entry>, -b: List<&2, C.Entry>) ->
  {C.names(List.append(&2, C.Entry, a, b)) == List.append(&2, String, C.names(a), C.names(b)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{C.Entry{name, path}, t}:
      %names_append(t, b) : {name <> C.names(List.append(&2, C.Entry, t, b)) == name <> _ : List<&2, String>}
      {==}

# The names boot loads: the shipped ones nobody replaced, then the ones found, less the ones switched off.
def plan_names(+shipped: List<&2, C.Entry>, +found: List<&2, C.Entry>, +disabled: List<&2, String>) ->
  {C.names(C.plan(shipped, found, disabled)) == C.without(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), disabled) : List<&2, String>}:
  %names_without(shipped, C.names(found)) : {C.names(C.plan(shipped, found, disabled)) == C.without(List.append(&2, String, _, C.names(found)), disabled) : List<&2, String>}
  %names_append(C.shipped_kept(shipped, found), found) : {C.names(C.plan(shipped, found, disabled)) == C.without(_, disabled) : List<&2, String>}
  names_without(List.append(&2, C.Entry, C.shipped_kept(shipped, found), found), disabled)

def Laws.off_files_stay_off(shipped, found, disabled, name):
  %Equal.sym(List<&2, String>, C.names(C.plan(shipped, found, C.add(disabled, name))),
    C.without(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), C.add(disabled, name)),
    plan_names(shipped, found, C.add(disabled, name))) : {C.has(_, name) == False{} : Bool}
  gone(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), C.add(disabled, name), name, add_has(disabled, name))

# A name found in a plugin directory is among the names to load before any is switched off.
def found_among(+kept: List<&2, String>, -found: List<&2, String>, +name: String, there: {C.has(found, name) == True{} : Bool}) ->
  {C.has(List.append(&2, String, kept, found), name) == True{} : Bool}:
  %Equal.sym(Bool, C.has(List.append(&2, String, kept, found), name), Bool.or(C.has(kept, name), C.has(found, name)), has_append(kept, found, name)) : {_ == True{} : Bool}
  %Equal.sym(Bool, C.has(found, name), True{}, there) : {Bool.or(C.has(kept, name), _) == True{} : Bool}
  or_true(C.has(kept, name))

# A shipped name nobody replaced is among the names to load before any is switched off.
def kept_among(+kept: List<&2, String>, -found: List<&2, String>, +name: String, there: {C.has(kept, name) == True{} : Bool}) ->
  {C.has(List.append(&2, String, kept, found), name) == True{} : Bool}:
  %Equal.sym(Bool, C.has(List.append(&2, String, kept, found), name), Bool.or(C.has(kept, name), C.has(found, name)), has_append(kept, found, name)) : {_ == True{} : Bool}
  %Equal.sym(Bool, C.has(kept, name), True{}, there) : {Bool.or(_, C.has(found, name)) == True{} : Bool}
  {==}

def Laws.found_plugins_load(shipped, found, disabled, name, there, on):
  %Equal.sym(List<&2, String>, C.names(C.plan(shipped, found, disabled)),
    C.without(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), disabled),
    plan_names(shipped, found, disabled)) : {C.has(_, name) == True{} : Bool}
  stays(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), disabled, name,
    found_among(C.without(C.names(shipped), C.names(found)), C.names(found), name, there), on)

def shipped_step(
  q: Bool, +shipped: List<&2, C.Entry>, +found: List<&2, C.Entry>, +disabled: List<&2, String>, +name: String,
  eq: {C.has(C.names(found), name) == q : Bool},
  there: {C.has(C.names(shipped), name) == True{} : Bool},
  +on: {C.has(disabled, name) == False{} : Bool}
) -> {C.has(C.names(C.plan(shipped, found, disabled)), name) == True{} : Bool}:
  match q:
    case True{}:
      Laws.found_plugins_load(shipped, found, disabled, name, eq, on)
    case False{}:
      %Equal.sym(List<&2, String>, C.names(C.plan(shipped, found, disabled)),
        C.without(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), disabled),
        plan_names(shipped, found, disabled)) : {C.has(_, name) == True{} : Bool}
      stays(List.append(&2, String, C.without(C.names(shipped), C.names(found)), C.names(found)), disabled, name,
        kept_among(C.without(C.names(shipped), C.names(found)), C.names(found), name,
          stays(C.names(shipped), C.names(found), name, there, eq)), on)

def Laws.shipped_defaults_load(shipped, found, disabled, name, there, on):
  shipped_step(C.has(C.names(found), name), shipped, found, disabled, name, {==}, there, on)

def entries_without_none(es: List<&2, C.Entry>) -> {C.without_named(es, Nil{}) == es : List<&2, C.Entry>}:
  match es:
    case Nil{}:
      {==}
    case Con{C.Entry{name, path}, t}:
      %entries_without_none(t) : {C.Entry{name, path} <> C.without_named(t, Nil{}) == C.Entry{name, path} <> _ : List<&2, C.Entry>}
      {==}

def entries_append_none(es: List<&2, C.Entry>) -> {List.append(&2, C.Entry, es, Nil{}) == es : List<&2, C.Entry>}:
  match es:
    case Nil{}:
      {==}
    case Con{h, t}:
      %entries_append_none(t) : {h <> List.append(&2, C.Entry, t, Nil{}) == h <> _ : List<&2, C.Entry>}
      {==}

def Laws.defaults_all_load(shipped):
  %entries_without_none(shipped) : {C.without_named(List.append(&2, C.Entry, C.without_named(shipped, Nil{}), Nil{}), Nil{}) == _ : List<&2, C.Entry>}
  %entries_append_none(C.without_named(shipped, Nil{})) : {C.without_named(List.append(&2, C.Entry, C.without_named(shipped, Nil{}), Nil{}), Nil{}) == _ : List<&2, C.Entry>}
  entries_without_none(List.append(&2, C.Entry, C.without_named(shipped, Nil{}), Nil{}))

# Texts and their beginnings
# --------------------------

def char_same(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{U32{x}}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# A text begins with itself.
def starts_self(p: String) -> {String.starts_with.go(p, p) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, char_same(h)) : {String.starts_with.go.if(t, t, _) == True{} : Bool}
      starts_self(t)

# A text with more after it begins with itself.
def starts(p: String, -rest: String) -> {String.starts_with.go(p, String.append(p, rest)) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, char_same(h)) : {String.starts_with.go.if(t, String.append(t, rest), _) == True{} : Bool}
      starts(t, rest)

# A text, a space and more begins with the text and a space.
def starts_spaced(p: String, -rest: String) -> {String.starts_with.go(String.append(p, " "), String.append(p, SCon{' ', rest})) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, char_same(h)) : {String.starts_with.go.if(String.append(t, " "), String.append(t, SCon{' ', rest}), _) == True{} : Bool}
      starts_spaced(t, rest)

def label_step(b: Bool, +name: String, -state: String) ->
  {String.starts_with(Bool.pick(String, b, name, String.concat([name, " (", state, ")"])), name) == True{} : Bool}:
  match b:
    case True{}:
      starts_self(name)
    case False{}:
      starts(name, String.concat([" (", state, ")"]))

def Laws.plugin_is_named(name, state):
  label_step(String.eq(state, "active"), name, state)

def prompt_step(b: Bool, +base: String, -identity: String) ->
  {String.starts_with(Bool.pick(String, b, base, String.concat([base, "\n\nWhat you have chosen to be:\n", identity])), base) == True{} : Bool}:
  match b:
    case True{}:
      starts_self(base)
    case False{}:
      starts(base, String.concat(["\n\nWhat you have chosen to be:\n", identity]))

def Laws.prompt_keeps_base(base, identity):
  prompt_step(String.is_empty(identity), base, identity)

def by_plugin_step(m: Bool, -name: String, +said: String, +owner: String, em: {C.mine(said, owner) == m : Bool}) ->
  {C.mine(C.title_pick(False{}, False{}, m, "", name, said, owner), owner) == True{} : Bool}:
  match m:
    case True{}:
      em
    case False{}:
      %Equal.sym(Bool, String.starts_with.go(String.append(owner, " "), String.append(owner, SCon{' ', said})), True{}, starts_spaced(owner, said)) : {Bool.or(String.eq(String.append(owner, SCon{' ', said}), owner), _) == True{} : Bool}
      or_true(String.eq(String.append(owner, SCon{' ', said}), owner))

def Laws.named_by_plugin(name, owner):
  by_plugin_step(C.mine(C.words(name), C.words(owner)), name, C.words(name), C.words(owner), {==})

# The caps
# --------

def ink_in(plus: Bool, star: Bool, dot: Bool) -> {C.has(C.inks(), C.ink_pick(plus, star, dot)) == True{} : Bool}:
  match plus star dot:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def Laws.caps_are_blue_and_grey(part):
  match part:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      ink_in(Char.is_eq(h, '+'), Char.is_eq(h, '*'), Char.is_eq(h, '.'))

# Putting a character in place of another leaves a text as long as it was.
def put_length(s: String, col: Nat, -c: Char) -> {String.length(C.put(s, col, c)) == String.length(s) : Nat}:
  match s col:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %put_length(t, p, c) : {1n+String.length(C.put(t, p, c)) == 1n+_ : Nat}
      {==}

def row_widths(rows: List<&2, String>, row: Nat, col: Nat, -c: Char) -> {C.widths(C.put_row(rows, row, col, c)) == C.widths(rows) : List<&2, Nat>}:
  match rows row:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %put_length(h, col, c) : {String.length(C.put(h, col, c)) <> C.widths(t) == _ <> C.widths(t) : List<&2, Nat>}
      {==}
    case Con{h, t} 1n+p:
      %row_widths(t, p, col, c) : {String.length(h) <> C.widths(C.put_row(t, p, col, c)) == String.length(h) <> _ : List<&2, Nat>}
      {==}

# However many sparks show whatever they show, every row is as wide as it was.
def twinkle_widths(sparks: List<&2, C.Spark>, +rows: List<&2, String>, +at: Nat) -> {C.widths(C.twinkle(sparks, rows, at)) == C.widths(rows) : List<&2, Nat>}:
  match sparks:
    case Nil{}:
      {==}
    case Con{C.Spark{+row, +col, +frames}, t}:
      Equal.trans(List<&2, Nat>,
        C.widths(C.twinkle(t, C.put_row(rows, row, col, C.glyph(String.get(frames, at))), at)),
        C.widths(C.put_row(rows, row, col, C.glyph(String.get(frames, at)))),
        C.widths(rows),
        twinkle_widths(t, C.put_row(rows, row, col, C.glyph(String.get(frames, at))), at),
        row_widths(rows, row, col, C.glyph(String.get(frames, at))))

def Laws.cap_keeps_its_shape(frame):
  twinkle_widths(C.sparks(), C.hat(), Nat.mod(frame, 8n))

# What the user sees
# ------------------

def brief_step(line: String) -> {C.fits(Bool.pick(String, String.is_empty(line), "\"\"", C.clip(line, 72n)), 72n) == True{} : Bool}:
  match line:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Laws.clip_fits(SCon{h, t}, 71n)

def Laws.brief_fits(text):
  brief_step(C.squash(text, False{}))

def NatIsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_is(-n: Nat, e: {0n == n : Nat}) -> NatIsZero(n):
  %e : NatIsZero(_)
  Unit{}

# A count that starts at one is not zero.
def counted(-A: Type, +t: List<&2, String>, none: {C.count(t, 1n) == 0n : Nat}) -> A:
  Empty.absurd(A, zero_is(1n+Nat.add(List.length(&2, String, t), 0n),
    Equal.trans(Nat, 0n, C.count(t, 1n), 1n+Nat.add(List.length(&2, String, t), 0n),
      Equal.sym(Nat, C.count(t, 1n), 0n, none),
      Equal.trans(Nat, C.count(t, 1n), Nat.add(List.length(&2, String, t), 1n), 1n+Nat.add(List.length(&2, String, t), 0n),
        count_len(t, 1n), add_succ(List.length(&2, String, t), 0n)))))

def Laws.nothing_hidden_unsaid(lines, limit, none):
  match lines limit:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      counted({Nil{} == h <> t : List<&2, String>}, t, none)
    case Con{h, t} 1n+p:
      %Laws.nothing_hidden_unsaid(t, p, none) : {h <> C.first(t, p) == h <> _ : List<&2, String>}
      {==}

# The command line
# ----------------

def Laws.own_theme_wins(rest, themes, pair, asked):
  %Equal.sym(Bool, C.has(rest, "--use-theme"), True{}, asked) : {"--theme" <> themes <> C.unless(_, ["--use-theme", pair]) == ["--theme", themes] : List<&2, String>}
  {==}

# An argument that is kept is not one that names a session.
def chooses_step(
  s: Bool, r: Bool, c: Bool, -h: String, -rest: List<&2, String>,
  ec: {C.chooses(h) == c : Bool},
  ih: {C.any_chooses(rest) == False{} : Bool}
) -> {C.any_chooses(C.keep_if(Bool.not(Bool.or(s, Bool.or(r, c))), h, rest)) == False{} : Bool}:
  match s r c:
    case True{} _ _:
      ih
    case False{} True{} _:
      ih
    case False{} False{} True{}:
      ih
    case False{} False{} False{}:
      %Equal.sym(Bool, C.chooses(h), False{}, ec) : {Bool.or(_, C.any_chooses(rest)) == False{} : Bool}
      ih

def Laws.restart_names_one_session(xs, skip):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      chooses_step(skip, C.resumes(h), C.chooses(h), h, C.strip(t, Bool.and(Bool.not(skip), C.chooses(h))), {==},
        Laws.restart_names_one_session(t, Bool.and(Bool.not(skip), C.chooses(h))))

def names_append_none(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %names_append_none(t) : {h <> List.append(&2, String, t, Nil{}) == h <> _ : List<&2, String>}
      {==}

def append_assoc(a: List<&2, String>, -b: List<&2, String>, -c: List<&2, String>) ->
  {List.append(&2, String, a, List.append(&2, String, b, c)) == List.append(&2, String, List.append(&2, String, a, b), c) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_assoc(t, b, c) : {h <> List.append(&2, String, t, List.append(&2, String, b, c)) == h <> _ : List<&2, String>}
      {==}

# Three lists joined one way are the same three joined the other way.
def regroup(+u: List<&2, String>, +t: List<&2, String>, +rest: List<&2, String>) ->
  {List.append(&2, String, u, List.append(&2, String, t, List.append(&2, String, rest, Nil{}))) == List.append(&2, String, List.append(&2, String, u, t), rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, List.append(&2, String, rest, Nil{}), rest, names_append_none(rest)) : {List.append(&2, String, u, List.append(&2, String, t, _)) == List.append(&2, String, List.append(&2, String, u, t), rest) : List<&2, String>}
  append_assoc(u, t, rest)

def user_args_proof(+rest: List<&2, String>, +sessions: String, +themes: String, +pair: String) ->
  {C.pi_args(rest, sessions, themes, pair) == List.append(&2, String,
    List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"],
      List.append(&2, String,
        C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]),
        C.theme_args(rest, themes, pair))), rest) : List<&2, String>}:
  %regroup(C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]), C.theme_args(rest, themes, pair), rest) : {C.pi_args(rest, sessions, themes, pair) == List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"], _) : List<&2, String>}
  {==}

def Laws.user_args_reach_pi(rest, sessions, themes, pair):
  (List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"],
    List.append(&2, String,
      C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]),
      C.theme_args(rest, themes, pair))),
   user_args_proof(rest, sessions, themes, pair))

def extras_dash(d: Bool, -h: String, -next: List<&2, String>, ih: {next == Nil{} : List<&2, String>}) ->
  {C.extras_pick(False{}, d, False{}, h, next) == Nil{} : List<&2, String>}:
  match d:
    case True{}:
      {==}
    case False{}:
      ih

# With no --plugin and no --gate, wizardry takes no argument for itself.
def no_extras(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}, +gate: {C.has(argv, "--gate") == False{} : Bool}) ->
  {C.extras(argv, False{}) == Nil{} : List<&2, String>}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--gate"), False{}, or_left(String.eq(h, "--gate"), C.has(t, "--gate"), gate)) : {C.extras_pick(False{}, String.eq(h, "--"), _, h, C.extras(t, String.eq(h, "--plugin"))) == Nil{} : List<&2, String>}
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {C.extras_pick(False{}, String.eq(h, "--"), False{}, h, C.extras(t, _)) == Nil{} : List<&2, String>}
      extras_dash(String.eq(h, "--"), h, C.extras(t, False{}),
        no_extras(t, or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin), or_right(String.eq(h, "--gate"), C.has(t, "--gate"), gate)))

def passes_dash(d: Bool, -h: String, -t: List<&2, String>, -next: List<&2, String>, ih: {next == t : List<&2, String>}) ->
  {C.passes_pick(False{}, d, False{}, False{}, h, t, next) == h <> t : List<&2, String>}:
  match d:
    case True{}:
      {==}
    case False{}:
      %ih : {h <> next == h <> _ : List<&2, String>}
      {==}

# With no --plugin and no --gate, every argument is left for Pi.
def all_pass(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}, +gate: {C.has(argv, "--gate") == False{} : Bool}) ->
  {C.passes(argv, False{}) == argv : List<&2, String>}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--gate"), False{}, or_left(String.eq(h, "--gate"), C.has(t, "--gate"), gate)) : {C.passes_pick(False{}, String.eq(h, "--"), _, String.eq(h, "--plugin"), h, t, C.passes(t, String.eq(h, "--plugin"))) == h <> t : List<&2, String>}
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {C.passes_pick(False{}, String.eq(h, "--"), False{}, _, h, t, C.passes(t, _)) == h <> t : List<&2, String>}
      passes_dash(String.eq(h, "--"), h, t, C.passes(t, False{}),
        all_pass(t, or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin), or_right(String.eq(h, "--gate"), C.has(t, "--gate"), gate)))

def complete_dash(d: Bool, -empty: Bool, -next: Bool, ih: {next == True{} : Bool}) -> {C.complete_pick(False{}, d, empty, next) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      ih

# With no --plugin, none is left without a value.
def is_complete(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}) -> {C.complete(argv, False{}) == True{} : Bool}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {C.complete_pick(False{}, String.eq(h, "--"), String.is_empty(h), C.complete(t, _)) == True{} : Bool}
      complete_dash(String.eq(h, "--"), String.is_empty(h), C.complete(t, False{}),
        is_complete(t, or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)))

def Laws.plain_args_pass(argv, plugin, gate):
  %Equal.sym(List<&2, String>, C.extras(argv, False{}), Nil{}, no_extras(argv, plugin, gate)) : {Bool.pick(Maybe<&2, C.Args>, C.complete(argv, False{}), Some{C.Args{_, C.passes(argv, False{})}}, None{}) == Some{C.Args{Nil{}, argv}} : Maybe<&2, C.Args>}
  %Equal.sym(List<&2, String>, C.passes(argv, False{}), argv, all_pass(argv, plugin, gate)) : {Bool.pick(Maybe<&2, C.Args>, C.complete(argv, False{}), Some{C.Args{Nil{}, _}}, None{}) == Some{C.Args{Nil{}, argv}} : Maybe<&2, C.Args>}
  %Equal.sym(Bool, C.complete(argv, False{}), True{}, is_complete(argv, plugin)) : {Bool.pick(Maybe<&2, C.Args>, _, Some{C.Args{Nil{}, argv}}, None{}) == Some{C.Args{Nil{}, argv}} : Maybe<&2, C.Args>}
  {==}

# The session, the header and the rest
# ------------------------------------

def Laws.restart_waits(wanted, attached, tui, idle):
  match wanted attached tui:
    case False{} _ _:
      ({==}, {==})
    case True{} False{} _:
      ({==}, {==})
    case True{} True{} False{}:
      ({==}, {==})
    case True{} True{} True{}:
      ({==}, {==})

def emit_total(count: Nat, -rest: List<&2, Nat>) -> {Laws.total(C.emit(count, rest)) == Nat.add(count, Laws.total(rest)) : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pack_step(
  f: Bool, +count: Nat, -used: Nat, -w: Nat, -t: List<&2, Nat>, -sep: Nat, -width: Nat,
  ih: {Laws.total(C.pack_go(t, Bool.pick(Nat, f, 1n+count, 1n), Bool.pick(Nat, f, Nat.add(used, Nat.add(sep, w)), w), sep, width))
    == Nat.add(Bool.pick(Nat, f, 1n+count, 1n), List.length(&2, Nat, t)) : Nat}
) -> {Laws.total(C.emit(Bool.pick(Nat, f, 0n, count), C.pack_go(t, Bool.pick(Nat, f, 1n+count, 1n), Bool.pick(Nat, f, Nat.add(used, Nat.add(sep, w)), w), sep, width)))
    == Nat.add(count, 1n+List.length(&2, Nat, t)) : Nat}:
  match f:
    case True{}:
      Equal.trans(Nat,
        Laws.total(C.pack_go(t, 1n+count, Nat.add(used, Nat.add(sep, w)), sep, width)),
        1n+Nat.add(count, List.length(&2, Nat, t)),
        Nat.add(count, 1n+List.length(&2, Nat, t)),
        ih,
        Equal.sym(Nat, Nat.add(count, 1n+List.length(&2, Nat, t)), 1n+Nat.add(count, List.length(&2, Nat, t)), add_succ(count, List.length(&2, Nat, t))))
    case False{}:
      %ih : {Laws.total(C.emit(count, C.pack_go(t, 1n, w, sep, width))) == Nat.add(count, _) : Nat}
      emit_total(count, C.pack_go(t, 1n, w, sep, width))

# The lines hold the items of the line being filled and all that are still to come.
def pack_total(widths: List<&2, Nat>, +count: Nat, +used: Nat, +sep: Nat, +width: Nat) ->
  {Laws.total(C.pack_go(widths, count, used, sep, width)) == Nat.add(count, List.length(&2, Nat, widths)) : Nat}:
  match widths:
    case Nil{}:
      emit_total(count, Nil{})
    case Con{+w, t}:
      pack_step(Bool.and(Nat.is_gt(count, 0n), Nat.is_le(Nat.add(used, Nat.add(sep, w)), width)), count, used, w, t, sep, width,
        pack_total(t,
          Bool.pick(Nat, Bool.and(Nat.is_gt(count, 0n), Nat.is_le(Nat.add(used, Nat.add(sep, w)), width)), 1n+count, 1n),
          Bool.pick(Nat, Bool.and(Nat.is_gt(count, 0n), Nat.is_le(Nat.add(used, Nat.add(sep, w)), width)), Nat.add(used, Nat.add(sep, w)), w),
          sep, width))

def Laws.pack_places_all(widths, sep, width):
  pack_total(widths, 0n, 0n, sep, width)

def Laws.rtk_needs_a_rewrite(code, out, command, zero, three):
  %Equal.sym(Bool, Nat.is_eq(code, 0n), False{}, zero) : {C.rtk_pick(Bool.or(_, Nat.is_eq(code, 3n)), String.trim(out), command) == None{} : Maybe<&2, String>}
  %Equal.sym(Bool, Nat.is_eq(code, 3n), False{}, three) : {C.rtk_pick(_, String.trim(out), command) == None{} : Maybe<&2, String>}
  {==}

def Laws.named_home_wins(c, rest, old_chosen, home, old, has_home, has_old):
  {==}

def Laws.adopting_overwrites_nothing(named, has_home, has_old, link):
  match named:
    case False{}:
      ({==}, {==})
    case True{}:
      ({==}, {==})

def Laws.cap_rests_off_screen():
  {==}

# Kept apart, export and delete
# -----------------------------

def Laws.pi_dir_is_wizardrys(home):
  starts(home, "/pi")

def Laws.pi_is_pointed_home(home):
  {==}

def Laws.pi_reads_nothing_around(rest, sessions, themes, pair):
  {==}

def Laws.addons_stay_behind():
  {==}

# A name that is kept is one of the good ones.
def named_step2(
  b: Bool, -h: String, -rest: List<&2, String>, -good: List<&2, String>,
  eb: {C.has(good, h) == b : Bool},
  ih: {C.covers(good, rest) == True{} : Bool}
) -> {C.covers(good, C.keep_if(b, h, rest)) == True{} : Bool}:
  match b:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Bool, C.has(good, h), True{}, eb) : {Bool.and(_, C.covers(good, rest)) == True{} : Bool}
      ih

def only_good(xs: List<&2, String>, +good: List<&2, String>) -> {C.covers(good, C.only(xs, good)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      named_step2(C.has(good, h), h, C.only(t, good), good, {==}, only_good(t, good))

def Laws.only_named_settings_come(keys):
  only_good(keys, C.brought_settings())

def never_onto_itself(has_own: Bool, has_old: Bool, +dir: String) -> {C.brings(has_own, has_old, dir, dir) == False{} : Bool}:
  match has_own has_old:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      %Equal.sym(Bool, String.eq(dir, dir), True{}, same(dir)) : {Bool.not(_) == False{} : Bool}
      {==}

def Laws.logins_overwrite_nothing(has_own, has_old, old, own, dir):
  ({==}, never_onto_itself(has_own, has_old, dir))

def Laws.words_of_keeping():
  ({==}, {==})

def Laws.export_stays_in_its_folder(dir, origin, rel):
  starts(dir, String.concat(["/conversations/", origin, "/", rel]))

def Laws.delete_asks_first(paths, exported):
  {==}

def Laws.delete_waits_for_export(paths, yes):
  match yes:
    case True{}:
      {==}
    case False{}:
      {==}

# What is spared for `keep` does not take `keep` along.
def spared_step(b: Bool, -paths: List<&2, String>, -keep: String, e: {C.takes(paths, keep) == b : Bool}) ->
  {C.takes(Bool.pick(List<&2, String>, b, Nil{}, paths), keep) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def spared(+paths: List<&2, String>, +keep: String) -> {C.takes(C.sparing(paths, keep), keep) == False{} : Bool}:
  spared_step(C.takes(paths, keep), paths, keep, {==})

# Paths that take nothing along still take nothing when they are all dropped.
def still(b: Bool, -paths: List<&2, String>, -keep: String, e: {C.takes(paths, keep) == False{} : Bool}) ->
  {C.takes(Bool.pick(List<&2, String>, b, Nil{}, paths), keep) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def still_rooted(b: Bool, -paths: List<&2, String>, -keep: String, e: {C.takes(paths, keep) == False{} : Bool}) ->
  {C.takes(Bool.pick(List<&2, String>, b, paths, Nil{}), keep) == False{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

def Laws.delete_keeps_the_export(what, home, old, userhome, to):
  spared(C.sparing(C.rooted(C.wanted(what, home, old)), userhome), to)

def Laws.delete_spares_your_home(what, home, old, userhome, to):
  still(C.takes(C.sparing(C.rooted(C.wanted(what, home, old)), userhome), to),
    C.sparing(C.rooted(C.wanted(what, home, old)), userhome), userhome,
    spared(C.rooted(C.wanted(what, home, old)), userhome))

# The same two steps for paths none of which is inside `root`.
def out_still(b: Bool, -paths: List<&2, String>, -root: String, e: {Laws.any_inside(paths, root) == False{} : Bool}) ->
  {Laws.any_inside(Bool.pick(List<&2, String>, b, Nil{}, paths), root) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def out_rooted(b: Bool, -paths: List<&2, String>, -root: String, e: {Laws.any_inside(paths, root) == False{} : Bool}) ->
  {Laws.any_inside(Bool.pick(List<&2, String>, b, paths, Nil{}), root) == False{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# Pi's own setup is asked for only when it is not inside wizardry's directory.
def old_out_step(b: Bool, -old: String, -home: String, e: {C.inside(old, home) == b : Bool}) ->
  {Laws.any_inside(Bool.pick(List<&2, String>, b, Nil{}, [old]), home) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, C.inside(old, home), False{}, e) : {Bool.or(_, False{}) == False{} : Bool}
      {==}

# Dropping all of them unless a condition holds changes neither.
def unless_takes(b: Bool, -paths: List<&2, String>, -keep: String, e: {C.takes(paths, keep) == False{} : Bool}) ->
  {C.takes(C.unless(b, paths), keep) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def unless_out(b: Bool, -paths: List<&2, String>, -root: String, e: {Laws.any_inside(paths, root) == False{} : Bool}) ->
  {Laws.any_inside(C.unless(b, paths), root) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def old_takes(+home: String, +old: String, +userhome: String, +to: String) ->
  {C.takes(C.doomed(C.Old{}, home, old, userhome, to), home) == False{} : Bool}:
  still(C.takes(C.sparing(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), to),
    C.sparing(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), home,
    still(C.takes(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), C.rooted(C.based(home, C.old_wanted(old, home))), home,
      still_rooted(C.all_rooted(C.based(home, C.old_wanted(old, home))), C.based(home, C.old_wanted(old, home)), home,
        unless_takes(Bool.not(String.starts_with(home, "/")), C.old_wanted(old, home), home,
          spared(Bool.pick(List<&2, String>, C.inside(old, home), Nil{}, [old]), home)))))

def old_inside(+home: String, +old: String, +userhome: String, +to: String) ->
  {Laws.any_inside(C.doomed(C.Old{}, home, old, userhome, to), home) == False{} : Bool}:
  out_still(C.takes(C.sparing(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), to),
    C.sparing(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), home,
    out_still(C.takes(C.rooted(C.based(home, C.old_wanted(old, home))), userhome), C.rooted(C.based(home, C.old_wanted(old, home))), home,
      out_rooted(C.all_rooted(C.based(home, C.old_wanted(old, home))), C.based(home, C.old_wanted(old, home)), home,
        unless_out(Bool.not(String.starts_with(home, "/")), C.old_wanted(old, home), home,
          out_still(C.takes(Bool.pick(List<&2, String>, C.inside(old, home), Nil{}, [old]), home),
            Bool.pick(List<&2, String>, C.inside(old, home), Nil{}, [old]), home,
            old_out_step(C.inside(old, home), old, home, {==}))))))

def Laws.old_spares_wizardry(home, old, userhome, to):
  (old_takes(home, old, userhome, to), old_inside(home, old, userhome, to))
