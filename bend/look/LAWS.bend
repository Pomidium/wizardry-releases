# What must hold of bend/look/look.bend, whatever the input. PROOF.bend proves each law.

import Base
import ../core.bend as C
import ./look.bend as L

# A collapsed result accounts for every line: the ones shown plus the ones counted as hidden.
law view_counts_all:
  for +lines: List<&2, String>
  for +limit: Nat
  {Nat.add(List.length(&2, String, L.first(lines, limit)), L.beyond(lines, limit)) == List.length(&2, String, lines) : Nat}

# Plugins: a default comes switched on, and is easy to change or remove
# ---------------------------------------------------------------------

# A title an action sets for itself is shown as it is.
law title_wins:
  for c: Char
  for rest: String
  for native: Bool
  for +name: String
  for +owner: String
  {L.action_title(SCon{c, rest}, native, name, owner) == SCon{c, rest} : String}

# Pi's own tools keep their names: read, write, edit, bash.
law native_keeps_name:
  for +name: String
  for +owner: String
  {L.action_title("", True{}, name, owner) == name : String}

# Every other call is shown under the name of the plugin it comes from.
law named_by_plugin:
  for +name: String
  for +owner: String
  {L.mine(L.action_title("", False{}, name, owner), L.words(owner)) == True{} : Bool}

# `subagent_create` from `subagent` reads "subagent create", `plugin_load` from `cordis`
# "cordis plugin load".
law title_examples:
  {L.action_title("", False{}, "subagent_create", "subagent") == "subagent create" : String} & {L.action_title("", False{}, "plugin_load", "cordis") == "cordis plugin load" : String}

# An expanded result is shown whole.
law expanded_shows_all:
  for +lines: List<&2, String>
  for +limit: Nat
  {L.view_of(True{}, lines, limit) == L.View{lines, 0n} : L.View}

# When no line is counted as hidden, none is: the result is shown whole.
law nothing_hidden_unsaid:
  for lines: List<&2, String>
  for limit: Nat
  for none: {L.beyond(lines, limit) == 0n : Nat}
  {L.first(lines, limit) == lines : List<&2, String>}

# The command line: Pi gets what is Pi's, and adds nothing to the agent by itself
# ------------------------------------------------------------------------------

# Every frame of the cap has the plain cap's shape, so nothing beside or below it moves.
law cap_keeps_its_shape:
  for frame: Nat
  {L.widths(L.hat_frame(frame)) == L.widths(L.hat()) : List<&2, Nat>}

# Still, the cap is the plain logo.
law cap_starts_plain:
  {L.hat_frame(0n) == L.hat() : List<&2, String>}

# Every frame of the small cap is seven wide, so the message beside it stays put.
law small_cap_stays_put:
  {L.widths(L.small_hat()) == [7n, 7n, 7n, 7n, 7n, 7n] : List<&2, Nat>}

# Every piece of a cap is drawn in one of four theme colors. That those four are blues and greys
# in both themes is a test (test/wizardry.test.mjs): no proof reaches the theme files.
law caps_are_blue_and_grey:
  for part: String
  {C.has(L.inks(), L.ink(part)) == True{} : Bool}

# The session, the header and the rest of what moved from TypeScript
# ------------------------------------------------------------------

# How many there are on all the lines together.
def total(counts: List<&2, Nat>) -> Nat:
  match counts:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(h, total(t))

# Packing the header's hints onto lines places every one of them, whatever the width.
law pack_places_all:
  for widths: List<&2, Nat>
  for +sep: Nat
  for +width: Nat
  {total(L.pack(widths, sep, width)) == List.length(&2, Nat, widths) : Nat}

# The cap stays still once it has scrolled away on the main screen.
law cap_rests_off_screen:
  {L.cap_moves(False{}, False{}) == False{} : Bool}

# Kept apart: wizardry's logins, settings, conversations and memories are its own
# -------------------------------------------------------------------------------
