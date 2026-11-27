# Proofs of the laws in LAWS.bend. Shared lemmas are wizardry's own (../../PROOF.bend).

import Base
import ../../PROOF.bend as P
import ../core.bend as C
import ./look.bend as L
import ./LAWS.bend as Laws

# Counting on top of `acc` is the length plus `acc`.
def count_len(xs: List<&2, String>, -acc: Nat) -> {L.count(xs, acc) == Nat.add(List.length(&2, String, xs), acc) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.trans(Nat, L.count(t, 1n+acc), Nat.add(List.length(&2, String, t), 1n+acc),
        1n+Nat.add(List.length(&2, String, t), acc),
        count_len(t, 1n+acc), P.add_succ(List.length(&2, String, t), acc))

def Laws.view_counts_all(lines, limit):
  match lines limit:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      %P.add_zero(List.length(&2, String, t)) : {L.count(t, 1n) == 1n+_ : Nat}
      Equal.trans(Nat, L.count(t, 1n), Nat.add(List.length(&2, String, t), 1n),
        1n+Nat.add(List.length(&2, String, t), 0n),
        count_len(t, 1n), P.add_succ(List.length(&2, String, t), 0n))
    case Con{h, +t} 1n+p:
      %Laws.view_counts_all(t, p) : {1n+Nat.add(List.length(&2, String, L.first(t, p)), L.beyond(t, p)) == 1n+_ : Nat}
      {==}

# Names are themselves, and names that compare equal are the same name
# -------------------------------------------------------------------

def Laws.cap_starts_plain():
  {==}

def Laws.small_cap_stays_put():
  {==}

def Laws.title_examples():
  ({==}, {==})

def Laws.title_wins(c, rest, native, name, owner):
  {==}

def Laws.native_keeps_name(name, owner):
  {==}

def Laws.expanded_shows_all(lines, limit):
  {==}

# A text, a space and more begins with the text and a space.
def starts_spaced(p: String, -rest: String) -> {String.starts_with.go(String.append(p, " "), String.append(p, SCon{' ', rest})) == True{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %Equal.sym(Bool, Char.is_eq(h, h), True{}, P.char_same(h)) : {String.starts_with.go.if(String.append(t, " "), String.append(t, SCon{' ', rest}), _) == True{} : Bool}
      starts_spaced(t, rest)

def by_plugin_step(m: Bool, -name: String, +said: String, +owner: String, em: {L.mine(said, owner) == m : Bool}) ->
  {L.mine(L.title_pick(False{}, False{}, m, "", name, said, owner), owner) == True{} : Bool}:
  match m:
    case True{}:
      em
    case False{}:
      %Equal.sym(Bool, String.starts_with.go(String.append(owner, " "), String.append(owner, SCon{' ', said})), True{}, starts_spaced(owner, said)) : {Bool.or(String.eq(String.append(owner, SCon{' ', said}), owner), _) == True{} : Bool}
      P.or_true(String.eq(String.append(owner, SCon{' ', said}), owner))

def Laws.named_by_plugin(name, owner):
  by_plugin_step(L.mine(L.words(name), L.words(owner)), name, L.words(name), L.words(owner), {==})

# The caps
# --------

def ink_in(plus: Bool, star: Bool, dot: Bool) -> {C.has(L.inks(), L.ink_pick(plus, star, dot)) == True{} : Bool}:
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
def put_length(s: String, col: Nat, -c: Char) -> {String.length(L.put(s, col, c)) == String.length(s) : Nat}:
  match s col:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      %put_length(t, p, c) : {1n+String.length(L.put(t, p, c)) == 1n+_ : Nat}
      {==}

def row_widths(rows: List<&2, String>, row: Nat, col: Nat, -c: Char) -> {L.widths(L.put_row(rows, row, col, c)) == L.widths(rows) : List<&2, Nat>}:
  match rows row:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      %put_length(h, col, c) : {String.length(L.put(h, col, c)) <> L.widths(t) == _ <> L.widths(t) : List<&2, Nat>}
      {==}
    case Con{h, t} 1n+p:
      %row_widths(t, p, col, c) : {String.length(h) <> L.widths(L.put_row(t, p, col, c)) == String.length(h) <> _ : List<&2, Nat>}
      {==}

# However many sparks show whatever they show, every row is as wide as it was.
def twinkle_widths(sparks: List<&2, L.Spark>, +rows: List<&2, String>, +at: Nat) -> {L.widths(L.twinkle(sparks, rows, at)) == L.widths(rows) : List<&2, Nat>}:
  match sparks:
    case Nil{}:
      {==}
    case Con{L.Spark{+row, +col, +frames}, t}:
      Equal.trans(List<&2, Nat>,
        L.widths(L.twinkle(t, L.put_row(rows, row, col, L.glyph(String.get(frames, at))), at)),
        L.widths(L.put_row(rows, row, col, L.glyph(String.get(frames, at)))),
        L.widths(rows),
        twinkle_widths(t, L.put_row(rows, row, col, L.glyph(String.get(frames, at))), at),
        row_widths(rows, row, col, L.glyph(String.get(frames, at))))

def Laws.cap_keeps_its_shape(frame):
  twinkle_widths(L.sparks(), L.hat(), Nat.mod(frame, 8n))

# What the user sees
# ------------------

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
def counted(-A: Type, +t: List<&2, String>, none: {L.count(t, 1n) == 0n : Nat}) -> A:
  Empty.absurd(A, zero_is(1n+Nat.add(List.length(&2, String, t), 0n),
    Equal.trans(Nat, 0n, L.count(t, 1n), 1n+Nat.add(List.length(&2, String, t), 0n),
      Equal.sym(Nat, L.count(t, 1n), 0n, none),
      Equal.trans(Nat, L.count(t, 1n), Nat.add(List.length(&2, String, t), 1n), 1n+Nat.add(List.length(&2, String, t), 0n),
        count_len(t, 1n), P.add_succ(List.length(&2, String, t), 0n)))))

def Laws.nothing_hidden_unsaid(lines, limit, none):
  match lines limit:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      counted({Nil{} == h <> t : List<&2, String>}, t, none)
    case Con{h, t} 1n+p:
      %Laws.nothing_hidden_unsaid(t, p, none) : {h <> L.first(t, p) == h <> _ : List<&2, String>}
      {==}

# The command line
# ----------------

def emit_total(count: Nat, -rest: List<&2, Nat>) -> {Laws.total(L.emit(count, rest)) == Nat.add(count, Laws.total(rest)) : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pack_step(
  f: Bool, +count: Nat, -used: Nat, -w: Nat, -t: List<&2, Nat>, -sep: Nat, -width: Nat,
  ih: {Laws.total(L.pack_go(t, Bool.pick(Nat, f, 1n+count, 1n), Bool.pick(Nat, f, Nat.add(used, Nat.add(sep, w)), w), sep, width))
    == Nat.add(Bool.pick(Nat, f, 1n+count, 1n), List.length(&2, Nat, t)) : Nat}
) -> {Laws.total(L.emit(Bool.pick(Nat, f, 0n, count), L.pack_go(t, Bool.pick(Nat, f, 1n+count, 1n), Bool.pick(Nat, f, Nat.add(used, Nat.add(sep, w)), w), sep, width)))
    == Nat.add(count, 1n+List.length(&2, Nat, t)) : Nat}:
  match f:
    case True{}:
      Equal.trans(Nat,
        Laws.total(L.pack_go(t, 1n+count, Nat.add(used, Nat.add(sep, w)), sep, width)),
        1n+Nat.add(count, List.length(&2, Nat, t)),
        Nat.add(count, 1n+List.length(&2, Nat, t)),
        ih,
        Equal.sym(Nat, Nat.add(count, 1n+List.length(&2, Nat, t)), 1n+Nat.add(count, List.length(&2, Nat, t)), P.add_succ(count, List.length(&2, Nat, t))))
    case False{}:
      %ih : {Laws.total(L.emit(count, L.pack_go(t, 1n, w, sep, width))) == Nat.add(count, _) : Nat}
      emit_total(count, L.pack_go(t, 1n, w, sep, width))

# The lines hold the items of the line being filled and all that are still to come.
def pack_total(widths: List<&2, Nat>, +count: Nat, +used: Nat, +sep: Nat, +width: Nat) ->
  {Laws.total(L.pack_go(widths, count, used, sep, width)) == Nat.add(count, List.length(&2, Nat, widths)) : Nat}:
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

def Laws.cap_rests_off_screen():
  {==}

# Kept apart, export and delete
# -----------------------------
