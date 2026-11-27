# Proofs of the laws in LAWS.bend. Shared lemmas are wizardry's own (../../PROOF.bend).

import Base
import ../../PROOF.bend as P
import ../core.bend as C
import ./keep.bend as K
import ./LAWS.bend as Laws

def Laws.export_stays_in_its_folder(dir, origin, rel):
  P.starts(dir, String.concat(["/conversations/", origin, "/", rel]))

def Laws.delete_asks_first(paths, exported):
  {==}

def Laws.delete_waits_for_export(paths, yes):
  match yes:
    case True{}:
      {==}
    case False{}:
      {==}

# What is spared for `keep` does not take `keep` along.
def spared_step(b: Bool, -paths: List<&2, String>, -keep: String, e: {K.takes(paths, keep) == b : Bool}) ->
  {K.takes(Bool.pick(List<&2, String>, b, Nil{}, paths), keep) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def spared(+paths: List<&2, String>, +keep: String) -> {K.takes(K.sparing(paths, keep), keep) == False{} : Bool}:
  spared_step(K.takes(paths, keep), paths, keep, {==})

# Paths that take nothing along still take nothing when they are all dropped.
def still(b: Bool, -paths: List<&2, String>, -keep: String, e: {K.takes(paths, keep) == False{} : Bool}) ->
  {K.takes(Bool.pick(List<&2, String>, b, Nil{}, paths), keep) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def still_rooted(b: Bool, -paths: List<&2, String>, -keep: String, e: {K.takes(paths, keep) == False{} : Bool}) ->
  {K.takes(Bool.pick(List<&2, String>, b, paths, Nil{}), keep) == False{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

def Laws.delete_keeps_the_export(what, home, old, userhome, to):
  spared(K.sparing(K.rooted(K.wanted(what, home, old)), userhome), to)

def Laws.delete_spares_your_home(what, home, old, userhome, to):
  still(K.takes(K.sparing(K.rooted(K.wanted(what, home, old)), userhome), to),
    K.sparing(K.rooted(K.wanted(what, home, old)), userhome), userhome,
    spared(K.rooted(K.wanted(what, home, old)), userhome))

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
def old_out_step(b: Bool, -old: String, -home: String, e: {K.inside(old, home) == b : Bool}) ->
  {Laws.any_inside(Bool.pick(List<&2, String>, b, Nil{}, [old]), home) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, K.inside(old, home), False{}, e) : {Bool.or(_, False{}) == False{} : Bool}
      {==}

# Dropping all of them unless a condition holds changes neither.
def unless_takes(b: Bool, -paths: List<&2, String>, -keep: String, e: {K.takes(paths, keep) == False{} : Bool}) ->
  {K.takes(C.unless(b, paths), keep) == False{} : Bool}:
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
  {K.takes(K.doomed(K.Old{}, home, old, userhome, to), home) == False{} : Bool}:
  still(K.takes(K.sparing(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), to),
    K.sparing(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), home,
    still(K.takes(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), K.rooted(K.based(home, K.old_wanted(old, home))), home,
      still_rooted(K.all_rooted(K.based(home, K.old_wanted(old, home))), K.based(home, K.old_wanted(old, home)), home,
        unless_takes(Bool.not(String.starts_with(home, "/")), K.old_wanted(old, home), home,
          spared(Bool.pick(List<&2, String>, K.inside(old, home), Nil{}, [old]), home)))))

def old_inside(+home: String, +old: String, +userhome: String, +to: String) ->
  {Laws.any_inside(K.doomed(K.Old{}, home, old, userhome, to), home) == False{} : Bool}:
  out_still(K.takes(K.sparing(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), to),
    K.sparing(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), home,
    out_still(K.takes(K.rooted(K.based(home, K.old_wanted(old, home))), userhome), K.rooted(K.based(home, K.old_wanted(old, home))), home,
      out_rooted(K.all_rooted(K.based(home, K.old_wanted(old, home))), K.based(home, K.old_wanted(old, home)), home,
        unless_out(Bool.not(String.starts_with(home, "/")), K.old_wanted(old, home), home,
          out_still(K.takes(Bool.pick(List<&2, String>, K.inside(old, home), Nil{}, [old]), home),
            Bool.pick(List<&2, String>, K.inside(old, home), Nil{}, [old]), home,
            old_out_step(K.inside(old, home), old, home, {==}))))))

def Laws.old_spares_wizardry(home, old, userhome, to):
  (old_takes(home, old, userhome, to), old_inside(home, old, userhome, to))
