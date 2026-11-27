# What must hold of bend/keep/keep.bend, whatever the input. PROOF.bend proves each law.

import Base
import ./keep.bend as K

# Every conversation an export copies is written inside the export's folder.
law export_stays_in_its_folder:
  for +dir: String
  for origin: String
  for rel: String
  {String.starts_with(K.conversation_to(dir, origin, rel), dir) == True{} : Bool}

# Without --yes, nothing is deleted.
law delete_asks_first:
  for paths: List<&2, String>
  for exported: K.Exported
  {K.goes(paths, False{}, exported) == Nil{} : List<&2, String>}

# When the export that comes first did not finish, nothing is deleted.
law delete_waits_for_export:
  for paths: List<&2, String>
  for yes: Bool
  {K.goes(paths, yes, K.Failed{}) == Nil{} : List<&2, String>}

# The export is never among what is deleted: no deleted path is its folder or holds it.
law delete_keeps_the_export:
  for what: K.What
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {K.takes(K.doomed(what, home, old, userhome, to), to) == False{} : Bool}

# Whatever wizardry's directory was set to, deleting never takes the user's home directory, nor
# anything that holds it.
law delete_spares_your_home:
  for +what: K.What
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {K.takes(K.doomed(what, home, old, userhome, to), userhome) == False{} : Bool}

# Whether any of `paths` is `root` or inside it.
def any_inside(paths: List<&2, String>, +root: String) -> Bool:
  match paths:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(K.inside(h, root), any_inside(t, root))

# Deleting the old setup leaves wizardry whole: nothing deleted is wizardry's directory, holds
# it, or is inside it.
law old_spares_wizardry:
  for +home: String
  for +old: String
  for +userhome: String
  for +to: String
  {K.takes(K.doomed(K.Old{}, home, old, userhome, to), home) == False{} : Bool} & {any_inside(K.doomed(K.Old{}, home, old, userhome, to), home) == False{} : Bool}

# /default
# --------
