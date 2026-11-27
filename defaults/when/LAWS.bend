# What must hold of when's decisions (when.bend), whatever the rules and whatever the agent does.
#
# The point of the plugin is that a rule costs nothing until it is needed. These say so.

import Base
import ../../bend/core.bend as C
import ./when.bend as W

# With no rules, nothing fires, whatever is said or done.
law no_rules_nothing_fires:
  for fired: List<&2, String>
  for text: String
  {W.due(Nil{}, fired, text) == Nil{} : List<&2, String>}

# A rule with no cue for the state the agent is in does not fire in it.
law no_cue_no_fire:
  for name: String
  for fired: List<&2, String>
  for toks: List<&2, String>
  {W.due_on([W.Rule{name, Nil{}}], fired, toks) == Nil{} : List<&2, String>}

# A cue with no words in it hits nothing: no rule can be made to fire on everything.
law empty_cue_hits_nothing:
  for toks: List<&2, String>
  {W.cue_hits("", toks) == False{} : Bool}

# A rule that fired does not fire again: what it says is said once.
law fires_once:
  for +name: String
  for cues: List<&2, String>
  for +fired: List<&2, String>
  for toks: List<&2, String>
  for was: {C.has(fired, name) == True{} : Bool}
  {W.due_on([W.Rule{name, cues}], fired, toks) == Nil{} : List<&2, String>}

# When nothing fired, nothing is said: not a word reaches the agent.
law nothing_fired_nothing_said:
  {W.told(Nil{}) == "" : String}
