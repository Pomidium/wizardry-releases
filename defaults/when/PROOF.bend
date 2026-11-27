# Proofs of the laws in LAWS.bend. `bend PROOF.bend` must print ALL PROOFS CHECK before a commit.

import Base
import ../../bend/core.bend as C
import ./when.bend as W
import ./LAWS.bend as Laws

def Laws.no_rules_nothing_fires(fired, text):
  {==}

# Whether it fired already or not, a rule no cue of which hits is not due.
def quiet(fired: Bool, -name: String) -> {W.due_one(fired, False{}, name, Nil{}) == Nil{} : List<&2, String>}:
  match fired:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.no_cue_no_fire(name, fired, toks):
  quiet(C.has(fired, name), name)

def Laws.empty_cue_hits_nothing(toks):
  {==}

def Laws.fires_once(name, cues, fired, toks, was):
  %Equal.sym(Bool, C.has(fired, name), True{}, was) : {W.due_one(_, W.any_hits(cues, toks), name, Nil{}) == Nil{} : List<&2, String>}
  {==}

def Laws.nothing_fired_nothing_said():
  {==}
