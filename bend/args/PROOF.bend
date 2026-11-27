# Proofs of the laws in LAWS.bend. Shared lemmas are wizardry's own (../../PROOF.bend).

import Base
import ../../PROOF.bend as P
import ../core.bend as C
import ./args.bend as A
import ./LAWS.bend as Laws

def Laws.dashes_pass(rest):
  {==}

def Laws.pi_adds_nothing(rest, sessions, themes, pair):
  {==}

def Laws.own_theme_wins(rest, themes, pair, asked):
  %Equal.sym(Bool, C.has(rest, "--use-theme"), True{}, asked) : {"--theme" <> themes <> C.unless(_, ["--use-theme", pair]) == ["--theme", themes] : List<&2, String>}
  {==}

def names_append_none(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %names_append_none(t) : {h <> List.append(&2, String, t, Nil{}) == h <> _ : List<&2, String>}
      {==}

def append_assoc(a: List<&2, String>, -b: List<&2, String>, -c: List<&2, String>) ->
  {List.append(&2, String, a, List.append(&2, String, b, c)) == List.append(&2, String, List.append(&2, String, a, b), c) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_assoc(t, b, c) : {h <> List.append(&2, String, t, List.append(&2, String, b, c)) == h <> _ : List<&2, String>}
      {==}

# Three lists joined one way are the same three joined the other way.
def regroup(+u: List<&2, String>, +t: List<&2, String>, +rest: List<&2, String>) ->
  {List.append(&2, String, u, List.append(&2, String, t, List.append(&2, String, rest, Nil{}))) == List.append(&2, String, List.append(&2, String, u, t), rest) : List<&2, String>}:
  %Equal.sym(List<&2, String>, List.append(&2, String, rest, Nil{}), rest, names_append_none(rest)) : {List.append(&2, String, u, List.append(&2, String, t, _)) == List.append(&2, String, List.append(&2, String, u, t), rest) : List<&2, String>}
  append_assoc(u, t, rest)

def user_args_proof(+rest: List<&2, String>, +sessions: String, +themes: String, +pair: String) ->
  {A.pi_args(rest, sessions, themes, pair) == List.append(&2, String,
    List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"],
      List.append(&2, String,
        C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]),
        A.theme_args(rest, themes, pair))), rest) : List<&2, String>}:
  %regroup(C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]), A.theme_args(rest, themes, pair), rest) : {A.pi_args(rest, sessions, themes, pair) == List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"], _) : List<&2, String>}
  {==}

def Laws.user_args_reach_pi(rest, sessions, themes, pair):
  (List.append(&2, String, ["--no-builtin-tools", "--no-extensions", "--no-skills", "--no-prompt-templates", "--no-context-files", "--no-themes", "--no-mcp", "--no-approve"],
    List.append(&2, String,
      C.unless(Bool.or(C.has(rest, "--session-dir"), C.has(rest, "--no-session")), ["--session-dir", sessions]),
      A.theme_args(rest, themes, pair))),
   user_args_proof(rest, sessions, themes, pair))

def extras_dash(d: Bool, -h: String, -next: List<&2, String>, ih: {next == Nil{} : List<&2, String>}) ->
  {A.extras_pick(False{}, d, False{}, h, next) == Nil{} : List<&2, String>}:
  match d:
    case True{}:
      {==}
    case False{}:
      ih

# With no --plugin and no --gate, wizardry takes no argument for itself.
def no_extras(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}, +gate: {C.has(argv, "--gate") == False{} : Bool}) ->
  {A.extras(argv, False{}) == Nil{} : List<&2, String>}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--gate"), False{}, P.or_left(String.eq(h, "--gate"), C.has(t, "--gate"), gate)) : {A.extras_pick(False{}, String.eq(h, "--"), _, h, A.extras(t, String.eq(h, "--plugin"))) == Nil{} : List<&2, String>}
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, P.or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {A.extras_pick(False{}, String.eq(h, "--"), False{}, h, A.extras(t, _)) == Nil{} : List<&2, String>}
      extras_dash(String.eq(h, "--"), h, A.extras(t, False{}),
        no_extras(t, P.or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin), P.or_right(String.eq(h, "--gate"), C.has(t, "--gate"), gate)))

def passes_dash(d: Bool, -h: String, -t: List<&2, String>, -next: List<&2, String>, ih: {next == t : List<&2, String>}) ->
  {A.passes_pick(False{}, d, False{}, False{}, h, t, next) == h <> t : List<&2, String>}:
  match d:
    case True{}:
      {==}
    case False{}:
      %ih : {h <> next == h <> _ : List<&2, String>}
      {==}

# With no --plugin and no --gate, every argument is left for Pi.
def all_pass(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}, +gate: {C.has(argv, "--gate") == False{} : Bool}) ->
  {A.passes(argv, False{}) == argv : List<&2, String>}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--gate"), False{}, P.or_left(String.eq(h, "--gate"), C.has(t, "--gate"), gate)) : {A.passes_pick(False{}, String.eq(h, "--"), _, String.eq(h, "--plugin"), h, t, A.passes(t, String.eq(h, "--plugin"))) == h <> t : List<&2, String>}
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, P.or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {A.passes_pick(False{}, String.eq(h, "--"), False{}, _, h, t, A.passes(t, _)) == h <> t : List<&2, String>}
      passes_dash(String.eq(h, "--"), h, t, A.passes(t, False{}),
        all_pass(t, P.or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin), P.or_right(String.eq(h, "--gate"), C.has(t, "--gate"), gate)))

def complete_dash(d: Bool, -empty: Bool, -next: Bool, ih: {next == True{} : Bool}) -> {A.complete_pick(False{}, d, empty, next) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      ih

# With no --plugin, none is left without a value.
def is_complete(argv: List<&2, String>, +plugin: {C.has(argv, "--plugin") == False{} : Bool}) -> {A.complete(argv, False{}) == True{} : Bool}:
  match argv:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(h, "--plugin"), False{}, P.or_left(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)) : {A.complete_pick(False{}, String.eq(h, "--"), String.is_empty(h), A.complete(t, _)) == True{} : Bool}
      complete_dash(String.eq(h, "--"), String.is_empty(h), A.complete(t, False{}),
        is_complete(t, P.or_right(String.eq(h, "--plugin"), C.has(t, "--plugin"), plugin)))

def Laws.plain_args_pass(argv, plugin, gate):
  %Equal.sym(List<&2, String>, A.extras(argv, False{}), Nil{}, no_extras(argv, plugin, gate)) : {Bool.pick(Maybe<&2, A.Args>, A.complete(argv, False{}), Some{A.Args{_, A.passes(argv, False{})}}, None{}) == Some{A.Args{Nil{}, argv}} : Maybe<&2, A.Args>}
  %Equal.sym(List<&2, String>, A.passes(argv, False{}), argv, all_pass(argv, plugin, gate)) : {Bool.pick(Maybe<&2, A.Args>, A.complete(argv, False{}), Some{A.Args{Nil{}, _}}, None{}) == Some{A.Args{Nil{}, argv}} : Maybe<&2, A.Args>}
  %Equal.sym(Bool, A.complete(argv, False{}), True{}, is_complete(argv, plugin)) : {Bool.pick(Maybe<&2, A.Args>, _, Some{A.Args{Nil{}, argv}}, None{}) == Some{A.Args{Nil{}, argv}} : Maybe<&2, A.Args>}
  {==}

# The session, the header and the rest
# ------------------------------------

def Laws.pi_reads_nothing_around(rest, sessions, themes, pair):
  {==}

def Laws.words_of_keeping():
  ({==}, {==})
