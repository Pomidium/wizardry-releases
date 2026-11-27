# What must hold of bend/args/args.bend, whatever the input. PROOF.bend proves each law.

import Base
import ../core.bend as C
import ./args.bend as A

# Everything from `--` on is Pi's, unread: no option after it is taken for wizardry's.
law dashes_pass:
  for +rest: List<&2, String>
  {A.split_args("--" <> rest) == Some{A.Args{Nil{}, "--" <> rest}} : Maybe<&2, A.Args>}

# Arguments with no --plugin and no --gate among them all go to Pi, unchanged.
law plain_args_pass:
  for +argv: List<&2, String>
  for +plugin: {C.has(argv, "--plugin") == False{} : Bool}
  for +gate: {C.has(argv, "--gate") == False{} : Bool}
  {A.split_args(argv) == Some{A.Args{Nil{}, argv}} : Maybe<&2, A.Args>}

# Pi always starts with its own tools, extensions, skills, prompt templates and context files
# off: what the agent can do comes only from plugins.
law pi_adds_nothing:
  for +rest: List<&2, String>
  for sessions: String
  for themes: String
  for pair: String
  {C.covers(A.pi_args(rest, sessions, themes, pair),
    ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files"]) == True{} : Bool}

# Everything the user passed for Pi reaches it, in order, after what wizardry puts in front.
law user_args_reach_pi:
  for +rest: List<&2, String>
  for +sessions: String
  for +themes: String
  for +pair: String
  exs before: List<&2, String>
  {A.pi_args(rest, sessions, themes, pair) == List.append(&2, String, before, rest) : List<&2, String>}

# A theme the user asked for is not overridden by wizardry's.
law own_theme_wins:
  for rest: List<&2, String>
  for themes: String
  for pair: String
  for asked: {C.has(rest, "--use-theme") == True{} : Bool}
  {A.theme_args(rest, themes, pair) == ["--theme", themes] : List<&2, String>}

# Pi always starts with theme discovery, MCP servers and project-local files off: nothing lying
# around a project, and nothing another setup installed, is read.
law pi_reads_nothing_around:
  for +rest: List<&2, String>
  for sessions: String
  for themes: String
  for pair: String
  {C.covers(A.pi_args(rest, sessions, themes, pair), ["--no-themes", "--no-mcp", "--no-approve"]) == True{} : Bool}

# `export` and `delete` are wizardry's own commands.
law words_of_keeping:
  {A.command_of("export") == A.Export{} : A.Command} & {A.command_of("delete") == A.Delete{} : A.Command}
