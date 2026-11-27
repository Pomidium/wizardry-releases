# queue: tasks that wait their turn. When the agent is completely done with what it is on, the
# first one waiting is handed to it as the next message, and so on down the list.
#
# What is decided here: what counts as a task, in which order they go, whether the next one starts
# now, when the queue holds instead, how `/queue ...` reads, and every text said about it.

import Base
import ../../bend/core.bend as C

# Tasks
# -----

# A task with nothing in it is not a task.
def keep_task(task: String, rest: List<&2, String>) -> List<&2, String>:
  match task:
    case SNil{}:
      rest
    case SCon{h, t}:
      SCon{h, t} <> rest

# The tasks among what was given: each without the space around it, and none of them blank.
def clean(tasks: List<&2, String>) -> List<&2, String>:
  match tasks:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      keep_task(String.trim(h), clean(t))

# New tasks go behind the ones that wait.
def add(items: List<&2, String>, tasks: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, items, clean(tasks))

# The task whose turn it is, and the ones that wait behind it.
def next(items: List<&2, String>) -> String:
  match items:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      h

def rest(items: List<&2, String>) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def drop_at(items: List<&2, String>, n: Nat) -> List<&2, String>:
  match items n:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      t
    case Con{h, t} 1n+p:
      h <> drop_at(t, p)

# The queue without its `n`th task, counted from 1 as it is listed. No such task, nothing removed.
def drop(items: List<&2, String>, n: Nat) -> List<&2, String>:
  match n:
    case 0n:
      items
    case 1n+p:
      drop_at(items, p)

def waiting(items: List<&2, String>) -> Bool:
  match items:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

# When the next one starts
# ------------------------

# Whether the task whose turn it is starts now: only when the agent is on nothing, the queue is
# not held, and something waits.
def starts(busy: Bool, paused: Bool, items: List<&2, String>) -> Bool:
  match busy paused:
    case True{} _:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      waiting(items)

# Whether the queue is held once a task has ended. A task the user stopped, or one that ended in
# an error, was not done: what waits behind it does not run on until the user says so. A session
# opened again is read the same way, as a task that was stopped.
def pauses(paused: Bool, aborted: Bool, failed: Bool, items: List<&2, String>) -> Bool:
  match paused aborted failed:
    case True{} _ _:
      True{}
    case False{} True{} _:
      waiting(items)
    case False{} False{} True{}:
      waiting(items)
    case False{} False{} False{}:
      False{}

# What the user types
# -------------------

type Cmd is Data:
  Show{}
  Clear{}
  Pause{}
  Go{}
  Drop{n: Nat}
  Add{task: String}

def drop_or_add(n: Maybe<&2, U32>, all: String) -> Cmd:
  match n:
    case None{}:
      Add{all}
    case Some{x}:
      Drop{U32.to_nat(x)}

def command_of(+a: String) -> Cmd:
  Bool.pick(Cmd, C.has(["", "list", "show", "drop"], a), Show{},
    Bool.pick(Cmd, String.eq(a, "clear"), Clear{},
      Bool.pick(Cmd, C.has(["pause", "hold", "stop"], a), Pause{},
        Bool.pick(Cmd, C.has(["go", "resume", "start", "continue"], a), Go{},
          Bool.pick(Cmd, String.starts_with(a, "drop "), drop_or_add(U32.read(String.trim(String.drop(a, 5n))), a),
            Add{a})))))

# `/queue ...`: one of a few words alone, `drop` and a number, and anything else is a task. So
# "drop the old table" is a task and "drop 2" removes the second.
def command(args: String) -> Cmd:
  command_of(String.trim(args))

# What is said
# ------------

def numbered(items: List<&2, String>, +n: Nat) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.concat([Nat.show(n), ". ", C.brief(h)]) <> numbered(t, 1n+n)

def how() -> String:
  "/queue <task> adds one, /queue drop <n> removes one, /queue clear empties it, /queue pause holds it, /queue go carries on."

# What `/queue` shows.
def listed(+items: List<&2, String>, paused: Bool) -> String:
  match items:
    case Nil{}:
      String.concat(["Nothing is queued", Bool.pick(String, paused, ", and the queue is held", ""),
        ". /queue <task> adds one: it starts as soon as the agent is done with what it is on.\n", how()])
    case Con{h, t}:
      String.concat(["Queued, next first:\n", String.join(numbered(h <> t, 1n), "\n"), "\n",
        Bool.pick(String, paused, "Held: nothing starts until /queue go.", "Each starts as soon as the agent is done with the one before."),
        "\n", how()])

# The action, as the agent reads it in its tool list.
def about() -> String:
  String.concat([
    "The queue: tasks for after the one you are on. When you have answered, the first one waiting is handed to you as the next message, ",
    "and so on. Use it when the user gives work for later (\"after this, do X\", a list to get through): one task each, worded to stand ",
    "by itself. Not for the steps of the task you are on. With no arguments it returns what waits."])

def about_add() -> String:
  "Tasks to put at the end, in order."

def about_drop() -> String:
  "Remove the task at this position (1 is next)."

def about_clear() -> String:
  "Remove every task that waits."

# What the agent is told after it touched the queue.
def told(+items: List<&2, String>, paused: Bool) -> String:
  match items:
    case Nil{}:
      "Nothing is queued."
    case Con{h, t}:
      String.concat(["Queued, next first:\n", String.join(numbered(h <> t, 1n), "\n"), "\n",
        Bool.pick(String, paused,
          "The queue is held: nothing starts until the user types /queue go.",
          "Do not start these now. Finish what you are on and answer; the first is then handed to you.")])

def after(left: Nat) -> String:
  match left:
    case 0n:
      "nothing waits after it"
    case 1n+p:
      String.concat([Nat.show(1n+p), " waiting after it"])

# Said to the user as a queued task starts.
def starting(task: String, left: List<&2, String>) -> String:
  String.concat(["Queue: on to ", C.brief(task), " (", after(List.length(&2, String, left)), ")."])

def why(aborted: Bool, failed: Bool) -> String:
  match aborted failed:
    case True{} _:
      "the last task was stopped"
    case False{} True{}:
      "the last task ended in an error"
    case False{} False{}:
      "this session was opened again"

# Said to the user when the queue is held with tasks in it.
def held(aborted: Bool, failed: Bool, items: List<&2, String>) -> String:
  String.concat(["Queue held with ", Nat.show(List.length(&2, String, items)), " waiting: ", why(aborted, failed),
    ". /queue go carries on, /queue shows what waits."])

def paused_now() -> String:
  "Queue held: nothing starts until /queue go."

def cleared() -> String:
  "Queue emptied."

def busy_go() -> String:
  "Queue carries on: the next task starts as soon as the agent is done with what it is on."
