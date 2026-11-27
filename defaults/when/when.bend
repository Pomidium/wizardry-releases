# when: rules of the form "when the agent is in this state, then this reaches it".
#
# A rule costs nothing until it fires. Whether one fires is decided here, on the words of what the
# agent was just asked, thought, is about to do or has just seen: no model is asked and nothing is
# kept in the standing prompt. What fires is said once, in the conversation, where it is needed.

import Base
import ../../bend/core.bend as C

# Words
# -----

# Whether a character is part of a word. In a cue, `*` and `+` are too: they are its syntax.
def is_word(c: Char, cue: Bool) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.or(Char.is_alpha(Chr{x}), Char.is_digit(Chr{x})),
        Bool.or(U32.is_ge(x, 128), Bool.and(cue, Bool.or(U32.is_eq(x, 42), U32.is_eq(x, 43)))))

# The word read so far (backwards) goes in front of the ones before it, when there is one.
def push(word: String, acc: List<&2, String>) -> List<&2, String>:
  match word:
    case SNil{}:
      acc
    case SCon{h, t}:
      String.reverse(SCon{h, t}) <> acc

# A tail call per character, so a long text costs no stack.
def words_go(s: String, +cue: Bool, +word: String, +acc: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      List.reverse(&2, String, push(word, acc))
    case SCon{+c, t}:
      words_go(t, cue,
        Bool.pick(String, is_word(c, cue), SCon{Char.to_lower(c), word}, SNil{}),
        Bool.pick(List<&2, String>, is_word(c, cue), acc, push(word, acc)))

# A text as its words, in lower case: "src/App.tsx" is app, src, tsx in the order they stand.
def words(s: String, cue: Bool) -> List<&2, String>:
  words_go(s, cue, SNil{}, Nil{})

# Cues
# ----
#
# A cue is a phrase, or phrases joined by `+`. A phrase hits when its words stand next to each
# other in the text; a cue hits when every phrase of it does, anywhere. A word ending in `*`
# stands for every word that starts with it. "landing page", "write + html", "component*".

# Whether a word of a cue stands for a word of the text.
def word_hits(pat: String, tok: String) -> Bool:
  match pat tok:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{h, t}:
      False{}
    case SCon{p, pt} SNil{}:
      Char.is_eq(p, '*')
    case SCon{+p, pt} SCon{h, t}:
      Bool.or(Char.is_eq(p, '*'), Bool.and(Char.is_eq(p, h), word_hits(pt, t)))

# A word of a cue that is only `*` stands for nothing: it would stand for everything.
def names(pat: String, tok: String) -> Bool:
  match pat:
    case SNil{}:
      False{}
    case SCon{+p, pt}:
      Bool.and(Bool.not(Char.is_eq(p, '*')), word_hits(SCon{p, pt}, tok))

def split_put(plus: Bool, h: String, rest: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match plus rest:
    case True{} rest:
      Nil{} <> rest
    case False{} Nil{}:
      [[h]]
    case False{} Con{p, ps}:
      (h <> p) <> ps

# The phrases of a cue's words: cut at every `+`.
def phrases(ws: List<&2, String>) -> List<&2, List<&2, String>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      split_put(String.eq(h, "+"), h, phrases(t))

# Whether the text starts with the phrase.
def starts(phrase: List<&2, String>, toks: List<&2, String>) -> Bool:
  match phrase toks:
    case Nil{} _:
      True{}
    case Con{p, pt} Nil{}:
      False{}
    case Con{p, pt} Con{h, t}:
      Bool.and(names(p, h), starts(pt, t))

# Whether the phrase stands somewhere in the text. A tail call per word: a long text costs no stack.
def occurs_go(toks: List<&2, String>, +phrase: List<&2, String>, found: Bool) -> Bool:
  match toks:
    case Nil{}:
      found
    case Con{+h, +t}:
      occurs_go(t, phrase, Bool.or(found, starts(phrase, h <> t)))

def occurs(toks: List<&2, String>, phrase: List<&2, String>) -> Bool:
  occurs_go(toks, phrase, False{})

# Whether every phrase stands in the text. `some` is whether one with words in it was seen: a cue
# with no words in it hits nothing, so an empty cue can never fire a rule on everything.
def all_occur(ps: List<&2, List<&2, String>>, +toks: List<&2, String>, some: Bool) -> Bool:
  match ps:
    case Nil{}:
      some
    case Con{Nil{}, rest}:
      all_occur(rest, toks, some)
    case Con{Con{w, ws}, rest}:
      Bool.and(occurs(toks, w <> ws), all_occur(rest, toks, True{}))

# Whether a cue hits a text, given as its words.
def cue_hits(cue: String, toks: List<&2, String>) -> Bool:
  all_occur(phrases(words(cue, True{})), toks, False{})

# Whether any of the cues hits.
def any_hits(cues: List<&2, String>, +toks: List<&2, String>) -> Bool:
  match cues:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(cue_hits(h, toks), any_hits(t, toks))

# Rules
# -----

# A rule as it stands for one state: its name, and its cues for that state.
type Rule is Data:
  Rule{name: String, cues: List<&2, String>}

def due_one(fired: Bool, hits: Bool, name: String, rest: List<&2, String>) -> List<&2, String>:
  match fired hits:
    case True{} _:
      rest
    case False{} False{}:
      rest
    case False{} True{}:
      name <> rest

# The rules that fire on a text: the ones a cue of which hits, less the ones that fired already.
def due_on(rules: List<&2, Rule>, +fired: List<&2, String>, +toks: List<&2, String>) -> List<&2, String>:
  match rules:
    case Nil{}:
      Nil{}
    case Con{Rule{+name, cues}, t}:
      due_one(C.has(fired, name), any_hits(cues, toks), name, due_on(t, fired, toks))

def due(rules: List<&2, Rule>, fired: List<&2, String>, text: String) -> List<&2, String>:
  due_on(rules, fired, words(text, False{}))

# The first line of a text, and of that at most `n` characters.
def first_line(s: String, n: Nat) -> String:
  match s n:
    case SNil{} _:
      SNil{}
    case SCon{h, t} 0n:
      SNil{}
    case SCon{+h, t} 1n+p:
      Bool.pick(String, Char.is_eq(h, '\n'), SNil{}, SCon{h, first_line(t, p)})

# What the agent is about to do, as a text: the action's name, then the first line of each
# argument. A path or a command is read; the body of a file being written is not, so
# "write + css" is about where it goes, not what it says.
def doing_args(args: List<&2, String>) -> String:
  match args:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.append(SCon{' ', first_line(h, 400n)}, doing_args(t))

def doing(tool: String, args: List<&2, String>) -> String:
  String.append(tool, doing_args(args))

# What is said
# ------------

def with_output(out: String) -> String:
  match out:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      String.append("\n", C.clip(SCon{h, t}, 2000n))

# One rule that fired: what it says, then what its command printed.
def note(name: String, then: String, out: String) -> String:
  String.concat(["[when: ", name, "] ", String.trim(then), with_output(String.trim(out))])

# Rules that fired, as they reach the agent. Nothing fired, nothing said.
def told(notes: List<&2, String>) -> String:
  String.join(notes, "\n")

# A call a rule applied to is not run: the rule reaches the agent before the thing is done.
def held(notes: List<&2, String>) -> String:
  String.concat(["Not run yet: a standing rule of the user's applies to this first.\n", told(notes),
    "\nMake the call again with that in mind."])

def also_held() -> String:
  "Not run: held with another call of this step, which a standing rule applied to. Read that one, then call again."

# How rules are made is itself a rule: it reaches the agent only when the user sounds like they
# are stating one, so the agent carries no action and no instructions for it until then.
def teach_name() -> String:
  "when"

def teach_cues() -> List<&2, String>:
  ["every time", "everytime", "each time", "any time", "anytime", "whenever", "from now on", "always",
   "when you", "if you", "remember", "prefer*", "rule*"]

def teach(file: String) -> String:
  String.concat([
    "If the user is stating a standing preference (\"whenever X, do Y\"), keep it as a rule in ", file,
    ", a JSON list you edit with write/edit; it holds from the next step, in every session. A rule:\n",
    "{\"name\": \"blue-ui\", \"when\": {\"asked\": [\"ui\", \"website\", \"landing page\", \"component*\"], ",
    "\"doing\": [\"write + html\", \"write + css\", \"edit + tsx\"]}, \"then\": \"Make the UI blue.\", \"run\": \"\"}\n",
    "`when` holds cues per state: asked (the user's message), thinking (your own reasoning and replies), ",
    "doing (an action's name and the first line of each argument, before it runs), seen (an action's result). A cue is a phrase of whole words, ",
    "case ignored; `+` joins phrases that must all occur; a final `*` matches any ending. Any cue hitting fires the rule, ",
    "once per session: `then` is shown to you at that moment and at no other, with the output of the shell command `run` if set. ",
    "Choose cues wide enough to catch the situation however it is worded, and few states. ",
    "Do not keep the preference anywhere else. If the user is not stating one, ignore this."])

def listed_one(name: String, then: String) -> String:
  String.concat([name, ": ", C.clip(String.trim(then), 80n)])

# What `/when` shows.
def listed(file: String, lines: List<&2, String>, problem: String) -> String:
  match lines problem:
    case Nil{} SNil{}:
      String.concat(["No rules yet. Tell the agent a preference (\"whenever you make a UI, make it blue\"), or edit ", file, "."])
    case Con{h, t} SNil{}:
      String.concat([String.join(h <> t, "\n"), "\n(", file, ")"])
    case _ SCon{h, t}:
      String.concat([file, " cannot be read as a list of rules: ", SCon{h, t}])
