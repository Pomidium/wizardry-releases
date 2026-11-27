# Proofs of the laws in LAWS.bend. `bend PROOF.bend` must print ALL PROOFS CHECK before a commit.

import Base
import ../../bend/core.bend as C
import ./queue.bend as Q
import ./LAWS.bend as Laws

def Laws.empty_never_starts(busy, paused):
  match busy paused:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.busy_never_starts(paused, items):
  {==}

def Laws.held_never_starts(busy, items):
  match busy:
    case True{}:
      {==}
    case False{}:
      {==}

# A queue held because something waits starts nothing; one with nothing waiting has nothing to start.
def waits(items: List<&2, String>) -> {Q.starts(False{}, Q.waiting(items), items) == False{} : Bool}:
  match items:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def Laws.stopped_does_not_run_on(paused, failed, items):
  match paused:
    case True{}:
      {==}
    case False{}:
      waits(items)

def Laws.failed_does_not_run_on(paused, aborted, items):
  match paused aborted:
    case True{} _:
      {==}
    case False{} True{}:
      waits(items)
    case False{} False{}:
      waits(items)

def Laws.done_runs_on(h, t):
  {==}

def Laws.first_stays_first(h, t, tasks):
  {==}

def Laws.nothing_added_nothing_changes(items):
  match items:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Laws.nothing_added_nothing_changes(t) : {h <> List.append(&2, String, t, Nil{}) == h <> _ : List<&2, String>}
      {==}

def Laws.blank_is_no_task():
  {==}

def Laws.taking_loses_nothing(h, t):
  {==}
