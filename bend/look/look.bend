# What the user sees: how calls and results read, and the header. Part of wizardry's decisions
# (../core.bend); compiled to core/look.mjs. LAWS.bend and PROOF.bend here say what must hold.

import Base
import ../core.bend as C

# What the user sees
# ------------------

# The logo: a wizard's cap. Plain ASCII, every row the same width.
def hat() -> List<&2, String>:
  [ "         /\\         ",
    "        /  \\        ",
    "       / *  \\       ",
    "      /    . \\      ",
    "     /  *     \\     ",
    " ___/__________\\___ ",
    "(__________________)"]

# A spark on or around the cap: where it sits, and what it shows on each of the eight frames.
type Spark is Data:
  Spark{row: Nat, col: Nat, frames: String}

# The first frame of every spark is what the plain cap has there.
def sparks() -> List<&2, Spark>:
  [ Spark{2n, 9n, "*+*.  .*"},
    Spark{3n, 11n, ". .*+*. "},
    Spark{4n, 8n, "*.  .*+*"},
    Spark{0n, 13n, "  .*.   "},
    Spark{1n, 5n, "     .*."},
    Spark{2n, 16n, " .+.    "}]

# `s` with `c` in place of its character at `col`. A text that short is left as it is.
def put(s: String, col: Nat, c: Char) -> String:
  match s col:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SCon{c, t}
    case SCon{h, t} 1n+p:
      SCon{h, put(t, p, c)}

def put_row(rows: List<&2, String>, row: Nat, col: Nat, c: Char) -> List<&2, String>:
  match rows row:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      put(h, col, c) <> t
    case Con{h, t} 1n+p:
      h <> put_row(t, p, col, c)

def glyph(found: Maybe<&2, Char>) -> Char:
  match found:
    case None{}:
      ' '
    case Some{c}:
      c

# `rows` with every spark showing what it shows on frame `at`.
def twinkle(sparks: List<&2, Spark>, rows: List<&2, String>, +at: Nat) -> List<&2, String>:
  match sparks:
    case Nil{}:
      rows
    case Con{Spark{row, col, frames}, t}:
      twinkle(t, put_row(rows, row, col, glyph(String.get(frames, at))), at)

# The cap's rows on one frame of its twinkle; the frames come round every eight.
def hat_frame(frame: Nat) -> List<&2, String>:
  twinkle(sparks(), hat(), Nat.mod(frame, 8n))

# The small cap that stands where Pi's spinner did while the agent works: a spark drifting off
# its tip, one frame per row.
def small_hat() -> List<&2, String>:
  [ "_/\\_   ",
    "_/\\_.  ",
    "_/\\_*  ",
    "_/\\_ + ",
    "_/\\_ * ",
    "_/\\_  ."]

# How wide each row is.
def widths(rows: List<&2, String>) -> List<&2, Nat>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.length(h) <> widths(t)

# The theme colors the caps are drawn in: blues and greys, in both themes.
def inks() -> List<&2, String>:
  ["accent", "mdLink", "dim", "text"]

def ink_pick(plus: Bool, star: Bool, dot: Bool) -> String:
  match plus star dot:
    case True{} _ _:
      "text"
    case False{} True{} _:
      "mdLink"
    case False{} False{} True{}:
      "dim"
    case False{} False{} False{}:
      "accent"

def ink_of(+c: Char) -> String:
  ink_pick(Char.is_eq(c, '+'), Char.is_eq(c, '*'), Char.is_eq(c, '.'))

# The theme color a piece of a cap is drawn in, by its first character: the cap in the accent
# blue, a spark pale blue at its brightest and grey as it fades.
def ink(part: String) -> String:
  match part:
    case SNil{}:
      "accent"
    case SCon{h, t}:
      ink_of(h)

# A name as words: "plugin_load" is "plugin load".
def words(text: String) -> String:
  C.squash(text, True{})

# Whether a title already starts with the plugin's name.
def mine(+title: String, +owner: String) -> Bool:
  Bool.or(String.eq(title, owner), String.starts_with(title, String.append(owner, " ")))

def title_pick(titled: Bool, native: Bool, mine: Bool, title: String, name: String, +said: String, owner: String) -> String:
  match titled native mine:
    case True{} _ _:
      title
    case False{} True{} _:
      name
    case False{} False{} True{}:
      said
    case False{} False{} False{}:
      String.append(owner, SCon{' ', said})

# What the user sees a call named as: the plugin, then what it did. `plugin_load` from `cordis`
# reads "cordis plugin load". Pi's own tools keep their names, and an action's title overrides all.
def action_title(+title: String, native: Bool, +name: String, +owner: String) -> String:
  title_pick(Bool.not(String.is_empty(title)), native, mine(words(name), words(owner)), title, name, words(name), words(owner))

def expand_put(cr: Bool, tab: Bool, nl: Bool, c: Char, pad: String, acc: String) -> String:
  match cr tab nl:
    case True{} _ _:
      acc
    case False{} True{} _:
      SCon{' ', SCon{' ', SCon{' ', acc}}}
    case False{} False{} True{}:
      String.append(String.reverse(pad), SCon{'\n', acc})
    case False{} False{} False{}:
      SCon{c, acc}

def expand_go(s: String, +pad: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, t}:
      expand_go(t, pad, expand_put(Char.is_eq(c, '\r'), Char.is_eq(c, '\t'), Char.is_eq(c, '\n'), c, pad, acc))

# Text as the terminal shows it: no carriage returns, tabs as three spaces, `pad` after each newline.
def expand(s: String, pad: String) -> String:
  expand_go(s, pad, SNil{})

# The first `limit` of `xs`.
def first(xs: List<&2, String>, limit: Nat) -> List<&2, String>:
  match xs limit:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Nil{}
    case Con{h, t} 1n+p:
      h <> first(t, p)

# How many `xs` there are, on top of `acc`.
def count(xs: List<&2, String>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      count(t, 1n+acc)

# How many of `xs` are past the first `limit`.
def beyond(xs: List<&2, String>, limit: Nat) -> Nat:
  match xs limit:
    case Nil{} _:
      0n
    case Con{h, t} 0n:
      count(t, 1n)
    case Con{h, t} 1n+p:
      beyond(t, p)

# The part of a result the user is shown, and how many lines are one keypress away.
type View is Data:
  View{shown: List<&2, String>, more: Nat}

def view_of(expanded: Bool, +lines: List<&2, String>, +limit: Nat) -> View:
  match expanded:
    case True{}:
      View{lines, 0n}
    case False{}:
      shown more = first(lines, limit) beyond(lines, limit)
      View{shown, more}

# What a call came back with: its lines, the first ten unless expanded.
def result_view(output: String, expanded: Bool) -> View:
  view_of(expanded, C.lines(String.trim_end(expand(output, ""))), 10n)

# The header
# ----------

# A line of `count` items, when there is one, before the lines after it.
def emit(count: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match count:
    case 0n:
      rest
    case 1n+p:
      Con{1n+p, rest}

# `count` items make the line being filled, `used` columns wide. The next item joins it when
# there is one and the item fits after a separator; otherwise the line ends and the item starts
# the next.
def pack_go(widths: List<&2, Nat>, +count: Nat, +used: Nat, +sep: Nat, +width: Nat) -> List<&2, Nat>:
  match widths:
    case Nil{}:
      emit(count, Nil{})
    case Con{+w, t}:
      +fits = Bool.and(Nat.is_gt(count, 0n), Nat.is_le(Nat.add(used, Nat.add(sep, w)), width))
      emit(Bool.pick(Nat, fits, 0n, count),
        pack_go(t, Bool.pick(Nat, fits, 1n+count, 1n), Bool.pick(Nat, fits, Nat.add(used, Nat.add(sep, w)), w), sep, width))

# Items of these widths on as few lines as `width` allows, none broken in two: how many go on
# each line, in order.
def pack(widths: List<&2, Nat>, sep: Nat, width: Nat) -> List<&2, Nat>:
  pack_go(widths, 0n, 0n, sep, width)

# Where the header's text goes: beside the cap when at least 36 columns are left there, and
# under it otherwise. `room` is how wide the text may be.
type Layout is Data:
  Beside{room: Nat}
  Under{room: Nat}

def layout_pick(beside: Bool, room: Nat, under: Nat) -> Layout:
  match beside:
    case True{}:
      Beside{room}
    case False{}:
      Under{under}

# One column of margin, the cap, three of gap, then the text.
def layout(+width: Nat, hat_width: Nat) -> Layout:
  +room = Nat.sub(width, Nat.add(4n, hat_width))
  layout_pick(Nat.is_ge(room, 36n), room, Nat.max(1n, Nat.sub(width, 1n)))

# `xs`, made `n` long with `fill` at the end; a longer list is left as it is.
def pad_end(n: Nat, xs: List<&2, String>, +fill: String) -> List<&2, String>:
  match n xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      fill <> pad_end(p, Nil{}, fill)
    case 1n+p Con{h, t}:
      h <> pad_end(p, t, fill)

def blanks(n: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      "" <> blanks(p)

def beside_row(+left: String, +line: String) -> String:
  Bool.pick(String, String.is_empty(line), left, String.concat([left, "   ", line]))

def beside_zip(lefts: List<&2, String>, lines: List<&2, String>) -> List<&2, String>:
  match lefts lines:
    case Nil{} _:
      Nil{}
    case Con{h, t} Nil{}:
      h <> beside_zip(t, Nil{})
    case Con{h, t} Con{l, lt}:
      beside_row(h, l) <> beside_zip(t, lt)

def margined(rows: List<&2, String>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      SCon{' ', h} <> margined(t)

# The header with its text beside the cap: the text sits against the brim, and when there is more
# of it than cap it starts at the tip and runs on below.
def header_beside(+hat: List<&2, String>, +lines: List<&2, String>, hat_width: Nat) -> List<&2, String>:
  +tall = Nat.max(List.length(&2, String, hat), List.length(&2, String, lines))
  margined(beside_zip(pad_end(tall, hat, String.repeat(" ", hat_width)),
    pad_end(tall, List.append(&2, String, blanks(Nat.sub(List.length(&2, String, hat), List.length(&2, String, lines))), lines), "")))

# The header with its text under the cap.
def header_under(hat: List<&2, String>, lines: List<&2, String>) -> List<&2, String>:
  margined(List.append(&2, String, hat, "" <> lines))

# The cap moves only while redrawing it is cheap: on a screen of its own, or while nothing has
# scrolled away above it.
def cap_moves(viewport: Bool, at_top: Bool) -> Bool:
  Bool.or(viewport, at_top)

def next_frame(frame: Nat) -> Nat:
  Nat.mod(1n+frame, 8n)

def blank_lines(shown: List<&2, String>) -> Bool:
  match shown:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.and(String.is_empty(h), List.is_empty(&2, String, t))

# Whether a result has nothing to show: one empty line and none hidden.
def blank_view(shown: List<&2, String>, more: Nat) -> Bool:
  Bool.and(blank_lines(shown), Nat.is_eq(more, 0n))

def more_hint(more: Nat) -> String:
  String.concat(["... (", Nat.show(more), " more lines,"])

# A plugin that is loaded: what the header and the listings say of it.
type Loaded is Data:
  Loaded{name: String, state: String, source: String}

def labels(plugins: List<&2, Loaded>) -> List<&2, String>:
  match plugins:
    case Nil{}:
      Nil{}
    case Con{Loaded{name, state, source}, t}:
      C.label(name, state) <> labels(t)

def widest(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(String.length(h), widest(t))

def pad_right(+s: String, n: Nat) -> String:
  String.append(s, String.repeat(" ", Nat.sub(n, String.length(s))))

def wide_rows(plugins: List<&2, Loaded>, +wide: Nat) -> List<&2, String>:
  match plugins:
    case Nil{}:
      Nil{}
    case Con{Loaded{name, state, source}, t}:
      String.concat(["  ", pad_right(C.label(name, state), wide), "  ", source]) <> wide_rows(t, wide)

# The plugins, one to a row with where each comes from, the names in a column.
def plugin_rows(+plugins: List<&2, Loaded>) -> List<&2, String>:
  wide_rows(plugins, widest(labels(plugins)))

# The plugins on one line, to be wrapped to the width.
def plugin_line(plugins: List<&2, Loaded>) -> String:
  String.join(labels(plugins), ", ")

def indented(rows: List<&2, String>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.append("  ", h) <> indented(t)
