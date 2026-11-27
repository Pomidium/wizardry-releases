# What must hold of the queue's decisions (queue.bend), whatever is queued and whatever happens.
#
# The point of the plugin is that the next task starts by itself. These say when it may not, and
# that what starts is what was asked for first.

import Base
import ../../bend/core.bend as C
import ./queue.bend as Q

# With nothing queued, nothing starts: the agent is never handed a message nobody wrote.
law empty_never_starts:
  for busy: Bool
  for paused: Bool
  {Q.starts(busy, paused, Nil{}) == False{} : Bool}

# While the agent is on a task, the next one does not start: one task at a time.
law busy_never_starts:
  for paused: Bool
  for items: List<&2, String>
  {Q.starts(True{}, paused, items) == False{} : Bool}

# A held queue starts nothing.
law held_never_starts:
  for busy: Bool
  for items: List<&2, String>
  {Q.starts(busy, True{}, items) == False{} : Bool}

# A task the user stopped does not lead into the next one.
law stopped_does_not_run_on:
  for paused: Bool
  for failed: Bool
  for items: List<&2, String>
  {Q.starts(False{}, Q.pauses(paused, True{}, failed, items), items) == False{} : Bool}

# Nor does a task that ended in an error.
law failed_does_not_run_on:
  for paused: Bool
  for aborted: Bool
  for items: List<&2, String>
  {Q.starts(False{}, Q.pauses(paused, aborted, True{}, items), items) == False{} : Bool}

# A task that was done leads into the next one, when one waits and the queue was not held.
law done_runs_on:
  for h: String
  for t: List<&2, String>
  {Q.starts(False{}, Q.pauses(False{}, False{}, False{}, h <> t), h <> t) == True{} : Bool}

# First in, first out: whatever is added, the task whose turn it was is still the next.
law first_stays_first:
  for h: String
  for t: List<&2, String>
  for tasks: List<&2, String>
  {Q.next(Q.add(h <> t, tasks)) == h : String}

# Adding nothing changes nothing.
law nothing_added_nothing_changes:
  for items: List<&2, String>
  {Q.add(items, Nil{}) == items : List<&2, String>}

# A blank is not a task.
law blank_is_no_task:
  {Q.clean(["", "  ", "\n\t "]) == Nil{} : List<&2, String>}

# Taking the next task loses none: it and the ones behind it are the queue that was.
law taking_loses_nothing:
  for h: String
  for t: List<&2, String>
  {Q.next(h <> t) <> Q.rest(h <> t) == h <> t : List<&2, String>}
