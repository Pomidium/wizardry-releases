function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT" : a === b ? "EQ" : "GT"};
}

function tup_new(a, b) {
  return {$: "Tuple", fst: a, snd: b};
}

function nat_divmod(a, b) {
  return tup_new(b && Math.trunc(a / b), b ? a % b : a);
}

function nat_chk(n) {
  if (n > 281474976710655) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function nat_in(n) {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {
    throw "bend: expected a Nat host number: an integer from 0 to 2^53";
  }
  return n;
}

function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && f32_round(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace("Infinity", "inf");
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^[\t\n\v\f\r ]*[+-]?((\d+(?:\.\d*)?|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  return re.test(s) ? {$: "Some", value: f32_round(
    s.replace(/inf\w*/i, "Infinity"))} : {$: "None"};
}

const f32_round = function f32_round(s) {
  const d = Number(s);
  const a = Math.abs(d);
  const f = Math.fround(a);
  const g = 2 * a - Math.min(f, 2 ** 128);
  if (g === f || Math.fround(g) !== g || g === Infinity) {
    return Math.sign(d) * f;
  }
  let k = 0;
  while (a * 2 ** k % 1 !== 0) {
    k += 1;
  }
  const [, i, r, e] = /(\d*)\.?(\d*)(?:e([+-]?\d+))?$/i.exec(s);
  const n = Number(e ?? 0) - r.length;
  const x = BigInt(i + r) * 2n ** BigInt(k) * 10n ** BigInt(Math.max(n, 0));
  const y = BigInt(a * 2 ** k) * 10n ** BigInt(Math.max(-n, 0));
  return Math.sign(d) * (x === y || x > y !== g > f ? f : g);
};

const char_new = function char_new(c) {
  return c < 55296 || c >= 57344 && c <= 1114111 ? String.fromCodePoint(c) : String.fromCharCode(56320, c >>> 22, c >>> 11 & 2047, c & 2047);
};

function char_len(s, at = 0) {
  return s[at] === "\uDC00" ? 4 : s.codePointAt(at) > 0xFFFF ? 2 : 1;
}

function char_code(s) {
  return s.length < 4 ? s.codePointAt(0)
    : (s.charCodeAt(1) << 22 | s.charCodeAt(2) << 11 | s.charCodeAt(3)) >>> 0;
}

function string_contains(s, p) {
  // A match starts at a Char, not inside a packed U32 code.
  for (let at = 0; at <= s.length; at += char_len(s, at)) {
    if (s.startsWith(p, at)) {
      return true;
    }
  }
  return false;
}

function str_out(s) {
  return s.replace(/\uDC00[^]{3}/gu, "\uFFFD");
}

function str_in(s) {
  return s.replace(/\p{Cs}/gu, "\uFFFD");
}

// Array
// =====

function array_new(d, v, lgs) {
  if (d > 31 - lgs) {
    throw "bend: an array past the deepest block class 31 (depth + log2 words per cell)";
  }
  return Array(2 ** d).fill(v);
}

function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_rmw(a, i, f) {
  const old = a[i %= a.length];
  a[i] = f(old);
  return tup_new(a, old);
}

// Run
// ===

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}

// Effect
// ======

const $0eff = Object.create(null);
const io_file_append = new Set();

function io_eff(k, run) {
  if (arguments.length > 2) {
    throw new Error("bend: " + k + " takes no need: an effect that waits parks itself");
  }
  if (k in $0eff) {
    throw new Error("bend: two effects register " + k);
  }
  $0eff[k] = run;
}
// Program
// =======

function $______bend_core_has(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_1 = $$String_eq(_h_0, _x_0);
    const _x_2 = $$______bend_core_has(_t_0, _x_0);
    return (_x_1 || _x_2);
  }
}

function $______bend_core_keep_if(_keep_0, _h_0, _rest_0) {
  if (!_keep_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $______bend_core_without(_xs_0, _bad_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $______bend_core_keep_if($$Bool_not($$______bend_core_has(_bad_0, _h_0)), _h_0, $$______bend_core_without(_t_0, _bad_0));
  }
}

function $______bend_core_only(_xs_0, _good_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $______bend_core_keep_if($$______bend_core_has(_good_0, _h_0), _h_0, $$______bend_core_only(_t_0, _good_0));
  }
}

function $______bend_core_overlaps(_xs_0, _bad_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$______bend_core_has(_bad_0, _h_0);
    const _x_1 = $$______bend_core_overlaps(_t_0, _bad_0);
    return (_x_0 || _x_1);
  }
}

function $______bend_core_add(_xs_0, _x_0) {
  return $Bool_pick($$______bend_core_has(_xs_0, _x_0), _xs_0, $$List_append(_xs_0, {$: "Con", "head": _x_0, "tail": {$: "Nil"}}));
}

function $______bend_core_add_all($0, $1) {
  for (;;) {
    {
      const _ys_0 = $0;
      const _xs_0 = $1;
      if (_ys_0.$ === "Nil") {
        return _xs_0;
      } else {
        const _h_0 = _ys_0["head"];
        const _t_0 = _ys_0["tail"];
        $0 = _t_0;
        $1 = $$______bend_core_add(_xs_0, _h_0);
        continue;
      }
    }
  }
}

function $______bend_core_covers(_xs_0, _need_0) {
  if (_need_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _need_0["head"];
    const _t_0 = _need_0["tail"];
    return $Bool_and($$______bend_core_has(_xs_0, _h_0), $$______bend_core_covers(_xs_0, _t_0));
  }
}

function $______bend_core_names(_es_0) {
  if (_es_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _es_0["head"];
    const _name_0 = _t_0["name"];
    const _t_1 = _es_0["tail"];
    return {$: "Con", "head": _name_0, "tail": $$______bend_core_names(_t_1)};
  }
}

function $______bend_core_keep_entry(_keep_0, _e_0, _rest_0) {
  if (!_keep_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _e_0, "tail": _rest_0};
  }
}

function $______bend_core_without_named(_es_0, _bad_0) {
  if (_es_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _es_0["head"];
    const _name_0 = _t_0["name"];
    const _path_0 = _t_0["path"];
    const _t_1 = _es_0["tail"];
    return $______bend_core_keep_entry($$Bool_not($$______bend_core_has(_bad_0, _name_0)), {$: "Entry", "name": _name_0, "path": _path_0}, $$______bend_core_without_named(_t_1, _bad_0));
  }
}

function $______bend_core_shipped_kept(_shipped_0, _found_0) {
  return $______bend_core_without_named(_shipped_0, $$______bend_core_names(_found_0));
}

function $______bend_core_plan(_shipped_0, _found_0, _disabled_0) {
  return $______bend_core_without_named($$List_append($$______bend_core_shipped_kept(_shipped_0, _found_0), _found_0), _disabled_0);
}

function $______bend_core_builtins_at_boot(_defaults_0, _disabled_0) {
  return $______bend_core_without(_defaults_0, _disabled_0);
}

function $______bend_core_switched_off(_disabled_0, _name_0) {
  return $______bend_core_add(_disabled_0, _name_0);
}

function $______bend_core_switched_on(_disabled_0, _name_0) {
  return $______bend_core_without(_disabled_0, {$: "Con", "head": _name_0, "tail": {$: "Nil"}});
}

function $______bend_core_remembered(_builtin_0, _default_0) {
  return $Bool_not($$Bool_and(_builtin_0, _default_0));
}

function $______bend_core_core_plugins() {
  return {$: "Con", "head": "pi", "tail": {$: "Con", "head": "cordis", "tail": {$: "Nil"}}};
}

function $______bend_core_is_core(_name_0) {
  return $______bend_core_has($$______bend_core_core_plugins(), _name_0);
}

function $______bend_core_restore_unloads(_loaded_0, _wanted_0) {
  return $______bend_core_without($$______bend_core_without(_loaded_0, _wanted_0), $$______bend_core_core_plugins());
}

function $______bend_core_ends_with_any(_s_0, _exts_0) {
  if (_exts_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _exts_0["head"];
    const _t_0 = _exts_0["tail"];
    const _x_0 = $$String_ends_with(_s_0, _h_0);
    const _x_1 = $$______bend_core_ends_with_any(_s_0, _t_0);
    return (_x_0 || _x_1);
  }
}

function $______bend_core_hidden_char(_c_0) {
  const _c_1 = _c_0;
  const _x_0 = $$Char_is_eq(_c_1, ".");
  const _x_1 = $$Char_is_eq(_c_1, "_");
  return (_x_0 || _x_1);
}

function $______bend_core_hidden(_name_0) {
  if (_name_0 === "") {
    return true;
  } else {
    const _h_0 = _name_0.slice(0, char_len(_name_0));
    return $______bend_core_hidden_char(_h_0);
  }
}

function $______bend_core_usable(_name_0, _folder_0, _entry_0) {
  return $Bool_and($$Bool_not($$______bend_core_hidden(_name_0)), $$Bool_pick(_folder_0, _entry_0, $$______bend_core_ends_with_any(_name_0, {$: "Con", "head": ".ts", "tail": {$: "Con", "head": ".mts", "tail": {$: "Con", "head": ".js", "tail": {$: "Con", "head": ".mjs", "tail": {$: "Nil"}}}}})));
}

function $______bend_core_stem_pick(_dot_0, _cut_0, _more_0) {
  if (!_dot_0) {
    return _more_0;
  } else {
    return _cut_0;
  }
}

function $______bend_core_stem_go(_whole_0, _rev_0) {
  if (_rev_0 === "") {
    return _whole_0;
  } else {
    const _h_0 = _rev_0.slice(0, char_len(_rev_0));
    const _t_0 = _rev_0.slice(char_len(_rev_0));
    return $______bend_core_stem_pick($$Char_is_eq(_h_0, "."), $$Bool_pick($$String_is_empty(_t_0), _whole_0, $$String_reverse(_t_0)), $$______bend_core_stem_go(_whole_0, _t_0));
  }
}

function $______bend_core_stem(_name_0) {
  return $______bend_core_stem_go(_name_0, $$String_reverse(_name_0));
}

function $______bend_core_pick_name(_candidates_0) {
  if (_candidates_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _candidates_0["head"];
    const _t_0 = _candidates_0["tail"];
    return $Bool_pick($$______bend_core_has({$: "Con", "head": "", "tail": {$: "Con", "head": "apply", "tail": {$: "Con", "head": "default", "tail": {$: "Nil"}}}}, _h_0), $$______bend_core_pick_name(_t_0), _h_0);
  }
}

function $______bend_core_command_pick(_help_0, _version_0, _pi_0, _auth_0, _update_0, _export_0, _delete_0) {
  if (_help_0) {
    return {$: "Help"};
  } else {
    if (_version_0) {
      return {$: "Version"};
    } else {
      if (_pi_0) {
        return {$: "PiOnly"};
      } else {
        if (_auth_0) {
          return {$: "Auth"};
        } else {
          if (_update_0) {
            return {$: "Update"};
          } else {
            if (_export_0) {
              return {$: "Export"};
            } else {
              if (_delete_0) {
                return {$: "Delete"};
              } else {
                return {$: "Run"};
              }
            }
          }
        }
      }
    }
  }
}

function $______bend_core_command_of(_first_0) {
  return $______bend_core_command_pick($$______bend_core_has({$: "Con", "head": "--help", "tail": {$: "Con", "head": "-h", "tail": {$: "Nil"}}}, _first_0), $$______bend_core_has({$: "Con", "head": "--version", "tail": {$: "Con", "head": "-v", "tail": {$: "Nil"}}}, _first_0), $$______bend_core_has({$: "Con", "head": "install", "tail": {$: "Con", "head": "remove", "tail": {$: "Con", "head": "uninstall", "tail": {$: "Con", "head": "list", "tail": {$: "Con", "head": "config", "tail": {$: "Con", "head": "mcp", "tail": {$: "Nil"}}}}}}}, _first_0), $$String_eq(_first_0, "auth"), $$String_eq(_first_0, "update"), $$String_eq(_first_0, "export"), $$String_eq(_first_0, "delete"));
}

function $______bend_core_extras_pick(_value_0, _dashes_0, _gate_0, _h_0, _next_0) {
  if (_value_0) {
    return {$: "Con", "head": _h_0, "tail": _next_0};
  } else {
    if (_dashes_0) {
      return {$: "Nil"};
    } else {
      if (_gate_0) {
        return {$: "Con", "head": "gate", "tail": _next_0};
      } else {
        return _next_0;
      }
    }
  }
}

function $______bend_core_extras(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $______bend_core_extras_pick(_value_0, $$String_eq(_h_0, "--"), $$String_eq(_h_0, "--gate"), _h_0, $$______bend_core_extras(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $______bend_core_passes_pick(_value_0, _dashes_0, _gate_0, _plugin_0, _h_0, _t_0, _next_0) {
  if (_value_0) {
    return _next_0;
  } else {
    if (_dashes_0) {
      return {$: "Con", "head": _h_0, "tail": _t_0};
    } else {
      if (_gate_0) {
        return _next_0;
      } else {
        if (_plugin_0) {
          return _next_0;
        } else {
          return {$: "Con", "head": _h_0, "tail": _next_0};
        }
      }
    }
  }
}

function $______bend_core_passes(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $______bend_core_passes_pick(_value_0, $$String_eq(_h_0, "--"), $$String_eq(_h_0, "--gate"), $$String_eq(_h_0, "--plugin"), _h_0, _t_0, $$______bend_core_passes(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $______bend_core_complete_pick(_value_0, _dashes_0, _empty_0, _next_0) {
  if (_value_0) {
    return $Bool_and($$Bool_not(_empty_0), _next_0);
  } else {
    if (_dashes_0) {
      return true;
    } else {
      return _next_0;
    }
  }
}

function $______bend_core_complete(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return $Bool_not(_value_0);
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $______bend_core_complete_pick(_value_0, $$String_eq(_h_0, "--"), $$String_is_empty(_h_0), $$______bend_core_complete(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $______bend_core_split_args(_argv_0) {
  const _extra_0 = $$______bend_core_extras(_argv_0, false);
  const _rest_0 = $$______bend_core_passes(_argv_0, false);
  return $Bool_pick($$______bend_core_complete(_argv_0, false), {$: "Some", "value": {$: "Args", "extra": _extra_0, "rest": _rest_0}}, {$: "None"});
}

function $______bend_core_unless(_skip_0, _xs_0) {
  if (!_skip_0) {
    return _xs_0;
  } else {
    return {$: "Nil"};
  }
}

function $______bend_core_theme_args(_rest_0, _themes_0, _pair_0) {
  return $List_append({$: "Con", "head": "--theme", "tail": {$: "Con", "head": _themes_0, "tail": {$: "Nil"}}}, $$______bend_core_unless($$______bend_core_has(_rest_0, "--use-theme"), {$: "Con", "head": "--use-theme", "tail": {$: "Con", "head": _pair_0, "tail": {$: "Nil"}}}));
}

function $______bend_core_pi_bare() {
  return {$: "Con", "head": "--no-builtin-tools", "tail": {$: "Con", "head": "--no-extensions", "tail": {$: "Con", "head": "--no-skills", "tail": {$: "Con", "head": "--no-prompt-templates", "tail": {$: "Con", "head": "--no-context-files", "tail": {$: "Nil"}}}}}};
}

function $______bend_core_pi_apart() {
  return {$: "Con", "head": "--no-themes", "tail": {$: "Con", "head": "--no-mcp", "tail": {$: "Con", "head": "--no-approve", "tail": {$: "Nil"}}}};
}

function $______bend_core_pi_args(_rest_0, _sessions_0, _themes_0, _pair_0) {
  const _x_0 = $$______bend_core_has(_rest_0, "--session-dir");
  const _x_1 = $$______bend_core_has(_rest_0, "--no-session");
  return $List_concat({$: "Con", "head": $$______bend_core_pi_bare(), "tail": {$: "Con", "head": $$______bend_core_pi_apart(), "tail": {$: "Con", "head": $$______bend_core_unless((_x_0 || _x_1), {$: "Con", "head": "--session-dir", "tail": {$: "Con", "head": _sessions_0, "tail": {$: "Nil"}}}), "tail": {$: "Con", "head": $$______bend_core_theme_args(_rest_0, _themes_0, _pair_0), "tail": {$: "Con", "head": _rest_0, "tail": {$: "Nil"}}}}}});
}

function $______bend_core_remove_one(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Bool_pick($$String_eq(_h_0, _x_0), _t_0, {$: "Con", "head": _h_0, "tail": $$______bend_core_remove_one(_t_0, _x_0)});
  }
}

function $______bend_core_unsaid($0, $1, $2) {
  for (;;) {
    {
      const _rev_0 = $0;
      const _said_0 = $1;
      const _acc_0 = $2;
      if (_rev_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _rev_0["head"];
        const _t_0 = _rev_0["tail"];
        const _x_0 = $$______bend_core_has(_said_0, _h_0);
        const _x_1 = $$String_eq(_h_0, "--");
        $0 = _t_0;
        $1 = $$Bool_pick($$______bend_core_has(_said_0, _h_0), $$______bend_core_remove_one(_said_0, _h_0), _said_0);
        $2 = $$Bool_pick((_x_0 || _x_1), _acc_0, {$: "Con", "head": _h_0, "tail": _acc_0});
        continue;
      }
    }
  }
}

function $______bend_core_resumes(_arg_0) {
  return $______bend_core_has({$: "Con", "head": "-c", "tail": {$: "Con", "head": "--continue", "tail": {$: "Con", "head": "-r", "tail": {$: "Con", "head": "--resume", "tail": {$: "Nil"}}}}}, _arg_0);
}

function $______bend_core_chooses(_arg_0) {
  return $______bend_core_has({$: "Con", "head": "--session", "tail": {$: "Con", "head": "--fork", "tail": {$: "Con", "head": "--session-id", "tail": {$: "Nil"}}}}, _arg_0);
}

function $______bend_core_strip(_xs_0, _skip_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$______bend_core_resumes(_h_0);
    const _x_1 = $$______bend_core_chooses(_h_0);
    const _x_2 = (_x_0 || _x_1);
    return $______bend_core_keep_if($$Bool_not((_skip_0 || _x_2)), _h_0, $$______bend_core_strip(_t_0, $$Bool_and($$Bool_not(_skip_0), $$______bend_core_chooses(_h_0))));
  }
}

function $______bend_core_any_resumes(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$______bend_core_resumes(_h_0);
    const _x_1 = $$______bend_core_any_resumes(_t_0);
    return (_x_0 || _x_1);
  }
}

function $______bend_core_any_chooses(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$______bend_core_chooses(_h_0);
    const _x_1 = $$______bend_core_any_chooses(_t_0);
    return (_x_0 || _x_1);
  }
}

function $______bend_core_session_args(_session_0) {
  if (_session_0.$ === "None") {
    return {$: "Nil"};
  } else {
    const _file_0 = _session_0["value"];
    return {$: "Con", "head": "--session", "tail": {$: "Con", "head": _file_0, "tail": {$: "Nil"}}};
  }
}

function $______bend_core_restart_args(_rest_0, _said_0, _session_0) {
  return $List_append($$______bend_core_strip($$______bend_core_unsaid($$List_reverse(_rest_0), _said_0, {$: "Nil"}), false), $$______bend_core_session_args(_session_0));
}

function $______bend_core_hat() {
  return {$: "Con", "head": "         /\\         ", "tail": {$: "Con", "head": "        /  \\        ", "tail": {$: "Con", "head": "       / *  \\       ", "tail": {$: "Con", "head": "      /    . \\      ", "tail": {$: "Con", "head": "     /  *     \\     ", "tail": {$: "Con", "head": " ___/__________\\___ ", "tail": {$: "Con", "head": "(__________________)", "tail": {$: "Nil"}}}}}}}};
}

function $______bend_core_sparks() {
  return {$: "Con", "head": {$: "Spark", "row": 2, "col": 9, "frames": "*+*.  .*"}, "tail": {$: "Con", "head": {$: "Spark", "row": 3, "col": 11, "frames": ". .*+*. "}, "tail": {$: "Con", "head": {$: "Spark", "row": 4, "col": 8, "frames": "*.  .*+*"}, "tail": {$: "Con", "head": {$: "Spark", "row": 0, "col": 13, "frames": "  .*.   "}, "tail": {$: "Con", "head": {$: "Spark", "row": 1, "col": 5, "frames": "     .*."}, "tail": {$: "Con", "head": {$: "Spark", "row": 2, "col": 16, "frames": " .+.    "}, "tail": {$: "Nil"}}}}}}};
}

function $______bend_core_put(_s_0, _col_0, _c_0) {
  if (_s_0 === "") {
    return "";
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    if (_col_0 == 0) {
      return (_c_0 + _t_0);
    } else {
      const _p_0 = (_col_0 - 1);
      return (_h_0 + $$______bend_core_put(_t_0, _p_0, _c_0));
    }
  }
}

function $______bend_core_put_row(_rows_0, _row_0, _col_0, _c_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    if (_row_0 == 0) {
      return {$: "Con", "head": $$______bend_core_put(_h_0, _col_0, _c_0), "tail": _t_0};
    } else {
      const _p_0 = (_row_0 - 1);
      return {$: "Con", "head": _h_0, "tail": $$______bend_core_put_row(_t_0, _p_0, _col_0, _c_0)};
    }
  }
}

function $______bend_core_glyph(_found_0) {
  if (_found_0.$ === "None") {
    return " ";
  } else {
    const _c_0 = _found_0["value"];
    return _c_0;
  }
}

function $______bend_core_twinkle($0, $1, $2) {
  for (;;) {
    {
      const _sparks_0 = $0;
      const _rows_0 = $1;
      const _at_0 = $2;
      if (_sparks_0.$ === "Nil") {
        return _rows_0;
      } else {
        const _t_0 = _sparks_0["head"];
        const _row_0 = _t_0["row"];
        const _col_0 = _t_0["col"];
        const _frames_0 = _t_0["frames"];
        const _t_1 = _sparks_0["tail"];
        $0 = _t_1;
        $1 = $$______bend_core_put_row(_rows_0, _row_0, _col_0, $$______bend_core_glyph($$String_get(_frames_0, _at_0)));
        $2 = _at_0;
        continue;
      }
    }
  }
}

function $______bend_core_hat_frame(_frame_0) {
  return $______bend_core_twinkle($$______bend_core_sparks(), $$______bend_core_hat(), $$Nat_mod(_frame_0, 8));
}

function $______bend_core_small_hat() {
  return {$: "Con", "head": "_/\\_   ", "tail": {$: "Con", "head": "_/\\_.  ", "tail": {$: "Con", "head": "_/\\_*  ", "tail": {$: "Con", "head": "_/\\_ + ", "tail": {$: "Con", "head": "_/\\_ * ", "tail": {$: "Con", "head": "_/\\_  .", "tail": {$: "Nil"}}}}}}};
}

function $______bend_core_widths(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": [...str_out(_h_0)].length, "tail": $$______bend_core_widths(_t_0)};
  }
}

function $______bend_core_inks() {
  return {$: "Con", "head": "accent", "tail": {$: "Con", "head": "mdLink", "tail": {$: "Con", "head": "dim", "tail": {$: "Con", "head": "text", "tail": {$: "Nil"}}}}};
}

function $______bend_core_ink_pick(_plus_0, _star_0, _dot_0) {
  if (_plus_0) {
    return "text";
  } else {
    if (_star_0) {
      return "mdLink";
    } else {
      if (_dot_0) {
        return "dim";
      } else {
        return "accent";
      }
    }
  }
}

function $______bend_core_ink_of(_c_0) {
  return $______bend_core_ink_pick($$Char_is_eq(_c_0, "+"), $$Char_is_eq(_c_0, "*"), $$Char_is_eq(_c_0, "."));
}

function $______bend_core_ink(_part_0) {
  if (_part_0 === "") {
    return "accent";
  } else {
    const _h_0 = _part_0.slice(0, char_len(_part_0));
    return $______bend_core_ink_of(_h_0);
  }
}

function $______bend_core_is_sep(_c_0, _loose_0) {
  const _x_0 = $$Char_is_eq(_c_0, "_");
  const _x_1 = $$Char_is_eq(_c_0, "-");
  const _x_2 = $$Char_is_space(_c_0);
  const _x_3 = $$Bool_and(_loose_0, (_x_0 || _x_1));
  return (_x_2 || _x_3);
}

function $______bend_core_squash_put(_sep_0, _pending_0, _c_0, _acc_0) {
  if (_sep_0) {
    return _acc_0;
  } else {
    if (_pending_0) {
      return (_c_0 + (" " + _acc_0));
    } else {
      return (_c_0 + _acc_0);
    }
  }
}

function $______bend_core_squash_go($0, $1, $2, $3, $4) {
  for (;;) {
    {
      const _s_0 = $0;
      const _loose_0 = $1;
      const _started_0 = $2;
      const _pending_0 = $3;
      const _acc_0 = $4;
      if (_s_0 === "") {
        return $String_reverse(_acc_0);
      } else {
        const _c_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        const _x_0 = $$Bool_not($$______bend_core_is_sep(_c_0, _loose_0));
        $0 = _t_0;
        $1 = _loose_0;
        $2 = (_started_0 || _x_0);
        $3 = $$Bool_and(_started_0, $$______bend_core_is_sep(_c_0, _loose_0));
        $4 = $$______bend_core_squash_put($$______bend_core_is_sep(_c_0, _loose_0), _pending_0, _c_0, _acc_0);
        continue;
      }
    }
  }
}

function $______bend_core_squash(_s_0, _loose_0) {
  return $______bend_core_squash_go(_s_0, _loose_0, false, false, "");
}

function $______bend_core_words(_text_0) {
  return $______bend_core_squash(_text_0, true);
}

function $______bend_core_mine(_title_0, _owner_0) {
  const _x_0 = $$String_eq(_title_0, _owner_0);
  const _x_1 = $$String_starts_with(_title_0, (_owner_0 + " "));
  return (_x_0 || _x_1);
}

function $______bend_core_title_pick(_titled_0, _native_0, _mine_0, _title_0, _name_0, _said_0, _owner_0) {
  if (_titled_0) {
    return _title_0;
  } else {
    if (_native_0) {
      return _name_0;
    } else {
      if (_mine_0) {
        return _said_0;
      } else {
        const _x_0 = (" " + _said_0);
        return (_owner_0 + _x_0);
      }
    }
  }
}

function $______bend_core_action_title(_title_0, _native_0, _name_0, _owner_0) {
  return $______bend_core_title_pick($$Bool_not($$String_is_empty(_title_0)), _native_0, $$______bend_core_mine($$______bend_core_words(_name_0), $$______bend_core_words(_owner_0)), _title_0, _name_0, $$______bend_core_words(_name_0), $$______bend_core_words(_owner_0));
}

function $______bend_core_fits($0, $1) {
  for (;;) {
    {
      const _s_0 = $0;
      const _n_0 = $1;
      if (_s_0 === "") {
        return true;
      } else {
        const _t_0 = _s_0.slice(char_len(_s_0));
        if (_n_0 == 0) {
          return false;
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $______bend_core_clip_at(_s_0, _n_0) {
  if (_n_0 == 0) {
    return "";
  } else {
    const _p_0 = (_n_0 - 1);
    const _x_0 = $$String_take(_s_0, _p_0);
    return (_x_0 + "…");
  }
}

function $______bend_core_clip(_s_0, _n_0) {
  return $Bool_pick($$______bend_core_fits(_s_0, _n_0), _s_0, $$______bend_core_clip_at(_s_0, _n_0));
}

function $______bend_core_brief(_text_0) {
  const _line_0 = $$______bend_core_squash(_text_0, false);
  return $Bool_pick($$String_is_empty(_line_0), "\"\"", $$______bend_core_clip(_line_0, 72));
}

function $______bend_core_expand_put(_cr_0, _tab_0, _nl_0, _c_0, _pad_0, _acc_0) {
  if (_cr_0) {
    return _acc_0;
  } else {
    if (_tab_0) {
      return (" " + (" " + (" " + _acc_0)));
    } else {
      if (_nl_0) {
        const _x_0 = $$String_reverse(_pad_0);
        const _x_1 = ("\n" + _acc_0);
        return (_x_0 + _x_1);
      } else {
        return (_c_0 + _acc_0);
      }
    }
  }
}

function $______bend_core_expand_go($0, $1, $2) {
  for (;;) {
    {
      const _s_0 = $0;
      const _pad_0 = $1;
      const _acc_0 = $2;
      if (_s_0 === "") {
        return $String_reverse(_acc_0);
      } else {
        const _c_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = _pad_0;
        $2 = $$______bend_core_expand_put($$Char_is_eq(_c_0, "\r"), $$Char_is_eq(_c_0, "\t"), $$Char_is_eq(_c_0, "\n"), _c_0, _pad_0, _acc_0);
        continue;
      }
    }
  }
}

function $______bend_core_expand(_s_0, _pad_0) {
  return $______bend_core_expand_go(_s_0, _pad_0, "");
}

function $______bend_core_line_cur(_nl_0, _c_0, _cur_0) {
  if (_nl_0) {
    return "";
  } else {
    return (_c_0 + _cur_0);
  }
}

function $______bend_core_line_done(_nl_0, _cur_0, _done_0) {
  if (_nl_0) {
    return {$: "Con", "head": $$String_reverse(_cur_0), "tail": _done_0};
  } else {
    return _done_0;
  }
}

function $______bend_core_lines_go($0, $1, $2) {
  for (;;) {
    {
      const _s_0 = $0;
      const _cur_0 = $1;
      const _done_0 = $2;
      if (_s_0 === "") {
        return $List_reverse({$: "Con", "head": $$String_reverse(_cur_0), "tail": _done_0});
      } else {
        const _c_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = $$______bend_core_line_cur($$Char_is_eq(_c_0, "\n"), _c_0, _cur_0);
        $2 = $$______bend_core_line_done($$Char_is_eq(_c_0, "\n"), _cur_0, _done_0);
        continue;
      }
    }
  }
}

function $______bend_core_lines(_s_0) {
  return $______bend_core_lines_go(_s_0, "", {$: "Nil"});
}

function $______bend_core_first(_xs_0, _limit_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    if (_limit_0 == 0) {
      return {$: "Nil"};
    } else {
      const _p_0 = (_limit_0 - 1);
      return {$: "Con", "head": _h_0, "tail": $$______bend_core_first(_t_0, _p_0)};
    }
  }
}

function $______bend_core_count($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = nat_chk(_acc_0 + 1);
        continue;
      }
    }
  }
}

function $______bend_core_beyond($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _limit_0 = $1;
      if (_xs_0.$ === "Nil") {
        return 0;
      } else {
        const _t_0 = _xs_0["tail"];
        if (_limit_0 == 0) {
          return $______bend_core_count(_t_0, 1);
        } else {
          const _p_0 = (_limit_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $______bend_core_view_of(_expanded_0, _lines_0, _limit_0) {
  if (_expanded_0) {
    return {$: "View", "shown": _lines_0, "more": 0};
  } else {
    const _shown_0 = $$______bend_core_first(_lines_0, _limit_0);
    const _more_0 = $$______bend_core_beyond(_lines_0, _limit_0);
    return {$: "View", "shown": _shown_0, "more": _more_0};
  }
}

function $______bend_core_result_view(_output_0, _expanded_0) {
  return $______bend_core_view_of(_expanded_0, $$______bend_core_lines($$String_trim_end($$______bend_core_expand(_output_0, ""))), 10);
}

function $______bend_core_droppable(_drop_0) {
  return $______bend_core_without(_drop_0, {$: "Con", "head": "focus", "tail": {$: "Nil"}});
}

function $______bend_core_focus_active(_active_0, _drop_0, _take_0) {
  return $______bend_core_add_all(_take_0, $$______bend_core_without(_active_0, $$______bend_core_droppable(_drop_0)));
}

function $______bend_core_after_rtk(_rest_0) {
  if (_rest_0 === "") {
    return true;
  } else {
    const _h_0 = _rest_0.slice(0, char_len(_rest_0));
    return $Char_is_space(_h_0);
  }
}

function $______bend_core_rtk_skips(_raw_0, _command_0) {
  const _line_0 = $$String_trim_start(_command_0);
  const _x_0 = $$String_is_empty(_line_0);
  const _x_1 = $$Bool_and($$String_starts_with(_line_0, "rtk"), $$______bend_core_after_rtk($$String_drop(_line_0, 3)));
  const _x_2 = (_x_0 || _x_1);
  return (_raw_0 || _x_2);
}

function $______bend_core_last_said($0, $1) {
  for (;;) {
    {
      const _lines_0 = $0;
      const _best_0 = $1;
      if (_lines_0.$ === "Nil") {
        return _best_0;
      } else {
        const _h_0 = _lines_0["head"];
        const _t_0 = _lines_0["tail"];
        $0 = _t_0;
        $1 = $$Bool_pick($$String_is_empty(_h_0), _best_0, _h_0);
        continue;
      }
    }
  }
}

function $______bend_core_unprefixed(_line_0) {
  return $Bool_pick($$String_starts_with(_line_0, "wizardry: "), $$String_drop(_line_0, 10), _line_0);
}

function $______bend_core_update_line(_said_0) {
  return $______bend_core_unprefixed($$______bend_core_last_said($$String_lines(_said_0), "wizardry: the update did not say what happened"));
}

function $______bend_core_updated(_line_0) {
  return $String_starts_with(_line_0, "updated to");
}

function $______bend_core_asked_pick(_empty_0, _on_0, _off_0) {
  if (_empty_0) {
    return {$: "Now"};
  } else {
    if (_on_0) {
      return {$: "On"};
    } else {
      if (_off_0) {
        return {$: "Off"};
      } else {
        return {$: "Unclear"};
      }
    }
  }
}

function $______bend_core_update_asked(_word_0) {
  return $______bend_core_asked_pick($$String_is_empty(_word_0), $$String_eq(_word_0, "on"), $$String_eq(_word_0, "off"));
}

function $______bend_core_switch_act(_on_0, _loaded_0) {
  if (_on_0) {
    if (!_loaded_0) {
      return {$: "Loads"};
    } else {
      return {$: "Stays"};
    }
  } else {
    if (_loaded_0) {
      return {$: "Unloads"};
    } else {
      return {$: "Stays"};
    }
  }
}

function $______bend_core_listed(_actions_0) {
  if (_actions_0.$ === "Nil") {
    return "(none)";
  } else {
    const _h_0 = _actions_0["head"];
    const _t_0 = _actions_0["tail"];
    return $String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", ");
  }
}

function $______bend_core_label(_name_0, _state_0) {
  return $Bool_pick($$String_eq(_state_0, "active"), _name_0, $$String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " (", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}}}));
}

function $______bend_core_inspect_line(_name_0, _state_0, _source_0, _actions_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "] ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Con", "head": "\n  actions: ", "tail": {$: "Con", "head": $$______bend_core_listed(_actions_0), "tail": {$: "Nil"}}}}}}}});
}

function $______bend_core_loaded_text(_verb_0, _name_0, _state_0, _actions_0) {
  return $Bool_pick($$String_eq(_state_0, "pending"), $$String_concat({$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" [pending]: it injects a service nothing provides yet, and starts when one does.", "tail": {$: "Nil"}}}}}), $$String_concat({$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "]. Actions: ", "tail": {$: "Con", "head": $$______bend_core_listed(_actions_0), "tail": {$: "Nil"}}}}}}}}));
}

function $______bend_core_described(_description_0, _notes_0) {
  return $String_join({$: "Con", "head": _description_0, "tail": $$______bend_core_without(_notes_0, {$: "Con", "head": "", "tail": {$: "Nil"}})}, "\n\n");
}

function $______bend_core_base_prompt(_cwd_0, _date_0) {
  return $String_join({$: "Con", "head": "You are wizardry, an agent working in a terminal on the user's machine.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "The user states outcomes. How you reach them is yours to decide.", "tail": {$: "Con", "head": "Everything you can do is a tool call. Tools are actions open to you, not procedures you owe anyone: take the ones that serve the outcome and leave the rest. Each comes from a plugin, and you can inspect, load, write and unload plugins while you work. No action waits for approval.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Working directory: " + _cwd_0), "tail": {$: "Con", "head": ("Date: " + _date_0), "tail": {$: "Nil"}}}}}}}}, "\n");
}

function $______bend_core_system_prompt(_base_0, _identity_0) {
  return $Bool_pick($$String_is_empty(_identity_0), _base_0, $$String_concat({$: "Con", "head": _base_0, "tail": {$: "Con", "head": "\n\nWhat you have chosen to be:\n", "tail": {$: "Con", "head": _identity_0, "tail": {$: "Nil"}}}}));
}

function $______bend_core_among(_xs_0, _x_0) {
  return $______bend_core_has(_xs_0, _x_0);
}

function $______bend_core_first_said(_a_0, _b_0) {
  return $Bool_pick($$String_is_empty(_a_0), _b_0, _a_0);
}

function $______bend_core_home_pick(_chosen_0, _said_0, _moved_0, _home_0, _old_0) {
  if (_chosen_0) {
    return _said_0;
  } else {
    if (_moved_0) {
      return _old_0;
    } else {
      return _home_0;
    }
  }
}

function $______bend_core_home_of(_chosen_0, _old_chosen_0, _home_0, _old_0, _has_home_0, _has_old_0) {
  return $______bend_core_home_pick($$Bool_not($$String_is_empty($$______bend_core_first_said(_chosen_0, _old_chosen_0))), $$______bend_core_first_said(_chosen_0, _old_chosen_0), $$Bool_and($$Bool_not(_has_home_0), _has_old_0), _home_0, _old_0);
}

function $______bend_core_adopts_home(_named_0, _has_home_0, _has_old_0, _old_is_link_0) {
  return $Bool_and($$Bool_not(_named_0), $$Bool_and($$Bool_not(_has_home_0), $$Bool_and(_has_old_0, $$Bool_not(_old_is_link_0))));
}

function $______bend_core_adopts_command(_invoked_0, _is_link_0, _has_command_0) {
  return $Bool_and($$String_eq(_invoked_0, "izardry"), $$Bool_and(_is_link_0, $$Bool_not(_has_command_0)));
}

function $______bend_core_moved_list(_home_0, _command_0) {
  return $List_append($$______bend_core_unless($$Bool_not(_home_0), {$: "Con", "head": "your plugins and sessions are now in ~/.wizardry", "tail": {$: "Nil"}}), $$______bend_core_unless($$Bool_not(_command_0), {$: "Con", "head": "the command is now `wizardry`", "tail": {$: "Nil"}}));
}

function $______bend_core_adopted_say(_moved_0) {
  if (_moved_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _h_0 = _moved_0["head"];
    const _t_0 = _moved_0["tail"];
    return {$: "Some", "value": $$String_concat({$: "Con", "head": "izardry is now wizardry: ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", and "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}})};
  }
}

function $______bend_core_adopted(_home_0, _command_0) {
  return $______bend_core_adopted_say($$______bend_core_moved_list(_home_0, _command_0));
}

function $______bend_core_plugin_dirs(_home_0, _cwd_0) {
  return $______bend_core_add({$: "Con", "head": _home_0, "tail": {$: "Nil"}}, _cwd_0);
}

function $______bend_core_under_home(_source_0) {
  return $Bool_pick($$String_starts_with(_source_0, "~/"), {$: "Some", "value": $$String_drop(_source_0, 2)}, {$: "None"});
}

function $______bend_core_is_builtin_source(_prefixed_0, _builtin_0, _exists_0) {
  const _x_0 = $$Bool_not(_exists_0);
  return $Bool_and(_builtin_0, (_prefixed_0 || _x_0));
}

function $______bend_core_nth($0, $1, $2) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _n_0 = $1;
      const _otherwise_0 = $2;
      if (_xs_0.$ === "Nil") {
        return _otherwise_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        if (_n_0 == 0) {
          return _h_0;
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          $2 = _otherwise_0;
          continue;
        }
      }
    }
  }
}

function $______bend_core_state_name(_n_0) {
  return $______bend_core_nth({$: "Con", "head": "pending", "tail": {$: "Con", "head": "loading", "tail": {$: "Con", "head": "active", "tail": {$: "Con", "head": "failed", "tail": {$: "Con", "head": "disposed", "tail": {$: "Con", "head": "unloading", "tail": {$: "Nil"}}}}}}}, _n_0, "unknown");
}

function $______bend_core_already_loaded(_name_0) {
  return $String_concat({$: "Con", "head": "plugin \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is already loaded; reload or unload it first", "tail": {$: "Nil"}}}});
}

function $______bend_core_not_loaded(_name_0) {
  return $String_concat({$: "Con", "head": "no plugin named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is loaded", "tail": {$: "Nil"}}}});
}

function $______bend_core_runs_on_it(_name_0, _verb_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is what this session runs on and cannot be ", "tail": {$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " from inside it", "tail": {$: "Nil"}}}}}});
}

function $______bend_core_no_builtin(_name_0, _builtins_0) {
  return $String_concat({$: "Con", "head": "no builtin plugin named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"; builtins: ", "tail": {$: "Con", "head": $$String_join(_builtins_0, ", "), "tail": {$: "Nil"}}}}});
}

function $______bend_core_no_plugin_at(_path_0) {
  return ("no plugin at " + _path_0);
}

function $______bend_core_no_entry(_path_0) {
  return (_path_0 + " has no index.ts, index.js or package.json \"main\"");
}

function $______bend_core_load_failed(_source_0, _why_0) {
  return $String_concat({$: "Con", "head": _source_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": _why_0, "tail": {$: "Nil"}}}});
}

function $______bend_core_needs_execute(_name_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" needs an execute function", "tail": {$: "Nil"}}}});
}

function $______bend_core_already_registered(_name_0, _owner_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is already registered by plugin \"", "tail": {$: "Con", "head": _owner_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}}}});
}

function $______bend_core_no_action(_name_0) {
  return $String_concat({$: "Con", "head": "no action named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}});
}

function $______bend_core_action_gone(_name_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is gone: its plugin was unloaded", "tail": {$: "Nil"}}}});
}

function $______bend_core_command_gone(_name_0) {
  return $String_concat({$: "Con", "head": "/", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": " is gone: its plugin was unloaded", "tail": {$: "Nil"}}}});
}

function $______bend_core_no_such_actions(_names_0) {
  const _x_0 = $$String_join(_names_0, ", ");
  return ("no such action: " + _x_0);
}

function $______bend_core_unloaded_text(_name_0) {
  return $String_concat({$: "Con", "head": "Unloaded \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\".", "tail": {$: "Nil"}}}});
}

function $______bend_core_help() {
  return $String_join({$: "Con", "head": "wizardry - Pi on Cordis. Every plugin is a tool call; the agent chooses which to make.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Usage:", "tail": {$: "Con", "head": "  wizardry [options] [messages...]     Start a session (interactive unless -p)", "tail": {$: "Con", "head": "  wizardry plugins                     List loaded plugins and the actions they provide", "tail": {$: "Con", "head": "  wizardry update [on|off]             Update now, or turn automatic updates on or off", "tail": {$: "Con", "head": "  wizardry auth <command>              Log in or out (wizardry keeps its own logins, apart from Pi's)", "tail": {$: "Con", "head": "  wizardry export [folder]             Copy every conversation and memory to a folder you keep", "tail": {$: "Con", "head": "  wizardry delete <what> [--yes]       Delete conversations, memories, old (Pi's own setup) or all", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Options:", "tail": {$: "Con", "head": "  --plugin <name|path>   Load a plugin for this run (repeatable)", "tail": {$: "Con", "head": "  --gate                 Load the \"gate\" plugin: ask before bash, write, edit and plugin changes", "tail": {$: "Con", "head": "  --version, -v          Show the version", "tail": {$: "Con", "head": "  --help, -h             Show this help", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Every other option goes to Pi unchanged: --model, --thinking, -p/--print, -c/--continue,", "tail": {$: "Con", "head": "-r/--resume, --mode json|rpc, --no-session, and so on (see `pi --help`).", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Plugins load from ~/.wizardry/plugins/, ./.wizardry/plugins/, and ~/.wizardry/plugins.json.", "tail": {$: "Con", "head": "wizardry updates itself in the background whenever it can; /update off in a session stops that.", "tail": {$: "Con", "head": "Nothing asks for approval unless you pass --gate.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "wizardry is kept apart: its logins, settings, conversations and memories are all in ~/.wizardry,", "tail": {$: "Con", "head": "and nothing of Pi's own setup (~/.pi) or of a project's .pi folder is read. `wizardry delete`", "tail": {$: "Con", "head": "says what it would remove and removes nothing until you add --yes; it exports first.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}}}}}}}}}}, "\n");
}

function $______bend_core_pi_only_text(_first_0, _argv_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _first_0, "tail": {$: "Con", "head": "\" is a Pi command and wizardry does not use Pi's extensions or packages. Run `pi ", "tail": {$: "Con", "head": $$String_join(_argv_0, " "), "tail": {$: "Con", "head": "` instead.\n", "tail": {$: "Nil"}}}}}});
}

function $______bend_core_lists_plugins(_rest_0) {
  if (_rest_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _rest_0["head"];
    return $String_eq(_h_0, "plugins");
  }
}

function $______bend_core_listing_actions(_actions_0) {
  if (_actions_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _actions_0["head"];
    const _t_0 = _actions_0["tail"];
    return $String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", "), "tail": {$: "Con", "head": "\n", "tail": {$: "Nil"}}}});
  }
}

function $______bend_core_listing(_name_0, _state_0, _source_0, _actions_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "] ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Con", "head": "\n", "tail": {$: "Con", "head": $$______bend_core_listing_actions(_actions_0), "tail": {$: "Nil"}}}}}}}});
}

function $______bend_core_switch_said(_on_0) {
  return $String_concat({$: "Con", "head": "Automatic updates are ", "tail": {$: "Con", "head": $$Bool_pick(_on_0, "on", "off"), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}});
}

function $______bend_core_at_file(_file_0) {
  return ("@" + _file_0);
}

function $______bend_core_at_files(_files_0) {
  if (_files_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _files_0["head"];
    const _t_0 = _files_0["tail"];
    return {$: "Con", "head": $$______bend_core_at_file(_h_0), "tail": $$______bend_core_at_files(_t_0)};
  }
}

function $______bend_core_said_of(_messages_0, _files_0) {
  return $List_append(_messages_0, $$______bend_core_at_files(_files_0));
}

function $______bend_core_restarts_now(_wanted_0, _attached_0, _tui_0, _idle_0) {
  return $Bool_and(_wanted_0, $$Bool_and(_attached_0, $$Bool_and(_tui_0, _idle_0)));
}

function $______bend_core_stays_away(_bound_0, _known_0, _active_0) {
  return $Bool_and(_bound_0, $$Bool_and(_known_0, $$Bool_not(_active_0)));
}

function $______bend_core_last_of($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _last_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _last_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = _h_0;
        continue;
      }
    }
  }
}

function $______bend_core_last_identity(_written_0) {
  return $______bend_core_last_of(_written_0, "");
}

function $______bend_core_tidy(_identity_0) {
  return $String_trim(_identity_0);
}

function $______bend_core_become_said(_identity_0) {
  return $Bool_pick($$String_is_empty(_identity_0), "Cleared.", "Set. It applies from the next turn.");
}

function $______bend_core_keep_starting(_word_0, _prefix_0, _rest_0) {
  return $______bend_core_keep_if($$String_starts_with(_word_0, _prefix_0), _word_0, _rest_0);
}

function $______bend_core_completions_go(_words_0, _prefix_0) {
  if (_words_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _words_0["head"];
    const _t_0 = _words_0["tail"];
    return $______bend_core_keep_starting(_h_0, _prefix_0, $$______bend_core_completions_go(_t_0, _prefix_0));
  }
}

function $______bend_core_completions(_words_0, _typed_0) {
  return $______bend_core_completions_go(_words_0, $$String_trim(_typed_0));
}

function $______bend_core_day(_iso_0) {
  return $String_take(_iso_0, 10);
}

function $______bend_core_focus_said(_active_0, _away_0) {
  return $String_concat({$: "Con", "head": "In front of you: ", "tail": {$: "Con", "head": $$String_join(_active_0, ", "), "tail": {$: "Con", "head": "\nPut away: ", "tail": {$: "Con", "head": $$______bend_core_listed(_away_0), "tail": {$: "Nil"}}}}});
}

function $______bend_core_think_levels() {
  return {$: "Con", "head": "off", "tail": {$: "Con", "head": "minimal", "tail": {$: "Con", "head": "low", "tail": {$: "Con", "head": "medium", "tail": {$: "Con", "head": "high", "tail": {$: "Con", "head": "xhigh", "tail": {$: "Con", "head": "max", "tail": {$: "Nil"}}}}}}}};
}

function $______bend_core_think_describe() {
  return $String_concat({$: "Con", "head": "Set how much reasoning you spend per step from here on: ", "tail": {$: "Con", "head": $$String_join($$______bend_core_think_levels(), ", "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}});
}

function $______bend_core_think_said(_level_0) {
  return ("Thinking level: " + _level_0);
}

function $______bend_core_kind_of(_managed_0) {
  return $Bool_pick(_managed_0, "install", "clone");
}

function $______bend_core_carried_on(_what_0) {
  return $String_concat({$: "Con", "head": "wizardry ", "tail": {$: "Con", "head": $$Maybe_default(_what_0, "updated"), "tail": {$: "Con", "head": "; this session carried on", "tail": {$: "Nil"}}}});
}

function $______bend_core_update_said(_line_0) {
  return ("wizardry: " + _line_0);
}

function $______bend_core_not_a_checkout(_app_0) {
  return (_app_0 + " is not a git checkout, so there is nothing to update from.");
}

function $______bend_core_rtk_pick(_ok_0, _out_0, _command_0) {
  return $Bool_pick($$Bool_and(_ok_0, $$Bool_and($$Bool_not($$String_is_empty(_out_0)), $$Bool_not($$String_eq(_out_0, _command_0)))), {$: "Some", "value": _out_0}, {$: "None"});
}

function $______bend_core_rtk_takes(_code_0, _out_0, _command_0) {
  const _x_0 = $$Nat_is_eq(_code_0, 0);
  const _x_1 = $$Nat_is_eq(_code_0, 3);
  return $______bend_core_rtk_pick((_x_0 || _x_1), $$String_trim(_out_0), _command_0);
}

function $______bend_core_in_dir(_dir_0, _file_0) {
  return $Bool_pick($$String_ends_with(_dir_0, "/"), (_dir_0 + _file_0), $$String_concat({$: "Con", "head": _dir_0, "tail": {$: "Con", "head": "/", "tail": {$: "Con", "head": _file_0, "tail": {$: "Nil"}}}}));
}

function $______bend_core_in_dirs(_dirs_0) {
  if (_dirs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _dirs_0["head"];
    const _t_0 = _dirs_0["tail"];
    return $______bend_core_keep_if($$Bool_not($$String_is_empty(_h_0)), $$______bend_core_in_dir(_h_0, "rtk"), $$______bend_core_in_dirs(_t_0));
  }
}

function $______bend_core_rtk_places(_configured_0, _dirs_0, _home_0) {
  if (_configured_0.$ === "Some") {
    const _file_0 = _configured_0["value"];
    return {$: "Con", "head": _file_0, "tail": {$: "Nil"}};
  } else {
    return $List_append($$______bend_core_in_dirs(_dirs_0), {$: "Con", "head": "/opt/homebrew/bin/rtk", "tail": {$: "Con", "head": "/usr/local/bin/rtk", "tail": {$: "Con", "head": $$______bend_core_in_dir(_home_0, ".cargo/bin/rtk"), "tail": {$: "Con", "head": $$______bend_core_in_dir(_home_0, ".local/bin/rtk"), "tail": {$: "Nil"}}}}});
  }
}

function $______bend_core_rtk_missing(_configured_0) {
  if (_configured_0.$ === "Some") {
    const _file_0 = _configured_0["value"];
    return $String_concat({$: "Con", "head": "no rtk executable at ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": "; bash output stays unfiltered", "tail": {$: "Nil"}}}});
  } else {
    return "rtk is not installed (brew install rtk, or see https://github.com/rtk-ai/rtk); bash output stays unfiltered";
  }
}

function $______bend_core_gated() {
  return {$: "Con", "head": "bash", "tail": {$: "Con", "head": "write", "tail": {$: "Con", "head": "edit", "tail": {$: "Con", "head": "plugin_load", "tail": {$: "Con", "head": "plugin_unload", "tail": {$: "Con", "head": "plugin_reload", "tail": {$: "Nil"}}}}}}};
}

function $______bend_core_gate_summary(_params_0) {
  return $String_take(_params_0, (1500 ));
}

function $______bend_core_gate_asks(_title_0) {
  return $String_concat({$: "Con", "head": "Allow ", "tail": {$: "Con", "head": _title_0, "tail": {$: "Con", "head": "?", "tail": {$: "Nil"}}}});
}

function $______bend_core_gate_no_one(_name_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" needs the user's approval and there is no one to ask in this mode", "tail": {$: "Nil"}}}});
}

function $______bend_core_gate_declined(_name_0) {
  return $String_concat({$: "Con", "head": "the user declined \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}});
}

function $______bend_core_emit(_count_0, _rest_0) {
  if (_count_0 == 0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _count_0, "tail": _rest_0};
  }
}

function $______bend_core_pack_go(_widths_0, _count_0, _used_0, _sep_0, _width_0) {
  if (_widths_0.$ === "Nil") {
    return $______bend_core_emit(_count_0, {$: "Nil"});
  } else {
    const _w_0 = _widths_0["head"];
    const _t_0 = _widths_0["tail"];
    const _x_0 = nat_chk(_sep_0 + _w_0);
    const _fits_0 = $$Bool_and($$Nat_is_gt(_count_0, 0), $$Nat_is_le(nat_chk(_used_0 + _x_0), _width_0));
    const _x_1 = nat_chk(_sep_0 + _w_0);
    return $______bend_core_emit($$Bool_pick(_fits_0, 0, _count_0), $$______bend_core_pack_go(_t_0, $$Bool_pick(_fits_0, nat_chk(_count_0 + 1), 1), $$Bool_pick(_fits_0, nat_chk(_used_0 + _x_1), _w_0), _sep_0, _width_0));
  }
}

function $______bend_core_pack(_widths_0, _sep_0, _width_0) {
  return $______bend_core_pack_go(_widths_0, 0, 0, _sep_0, _width_0);
}

function $______bend_core_layout_pick(_beside_0, _room_0, _under_0) {
  if (_beside_0) {
    return {$: "Beside", "room": _room_0};
  } else {
    return {$: "Under", "room": _under_0};
  }
}

function $______bend_core_layout(_width_0, _hat_width_0) {
  const _x_0 = nat_chk(4 + _hat_width_0);
  const _room_0 = (_width_0 < _x_0 ? 0 : _width_0 - _x_0);
  const _x_1 = (_width_0 < 1 ? 0 : _width_0 - 1);
  return $______bend_core_layout_pick($$Nat_is_ge(_room_0, 36), _room_0, (1 > _x_1 ? 1 : _x_1));
}

function $______bend_core_pad_end(_n_0, _xs_0, _fill_0) {
  if (_n_0 == 0) {
    return _xs_0;
  } else {
    const _p_0 = (_n_0 - 1);
    if (_xs_0.$ === "Nil") {
      return {$: "Con", "head": _fill_0, "tail": $$______bend_core_pad_end(_p_0, {$: "Nil"}, _fill_0)};
    } else {
      const _h_0 = _xs_0["head"];
      const _t_0 = _xs_0["tail"];
      return {$: "Con", "head": _h_0, "tail": $$______bend_core_pad_end(_p_0, _t_0, _fill_0)};
    }
  }
}

function $______bend_core_blanks(_n_0) {
  if (_n_0 == 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    return {$: "Con", "head": "", "tail": $$______bend_core_blanks(_p_0)};
  }
}

function $______bend_core_beside_row(_left_0, _line_0) {
  return $Bool_pick($$String_is_empty(_line_0), _left_0, $$String_concat({$: "Con", "head": _left_0, "tail": {$: "Con", "head": "   ", "tail": {$: "Con", "head": _line_0, "tail": {$: "Nil"}}}}));
}

function $______bend_core_beside_zip(_lefts_0, _lines_0) {
  if (_lefts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _lefts_0["head"];
    const _t_0 = _lefts_0["tail"];
    if (_lines_0.$ === "Nil") {
      return {$: "Con", "head": _h_0, "tail": $$______bend_core_beside_zip(_t_0, {$: "Nil"})};
    } else {
      const _l_0 = _lines_0["head"];
      const _lt_0 = _lines_0["tail"];
      return {$: "Con", "head": $$______bend_core_beside_row(_h_0, _l_0), "tail": $$______bend_core_beside_zip(_t_0, _lt_0)};
    }
  }
}

function $______bend_core_margined(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": (" " + _h_0), "tail": $$______bend_core_margined(_t_0)};
  }
}

function $______bend_core_header_beside(_hat_0, _lines_0, _hat_width_0) {
  const _x_0 = $$List_length(_hat_0);
  const _x_1 = $$List_length(_lines_0);
  const _tall_0 = (_x_0 > _x_1 ? _x_0 : _x_1);
  const _x_2 = $$List_length(_hat_0);
  const _x_3 = $$List_length(_lines_0);
  return $______bend_core_margined($$______bend_core_beside_zip($$______bend_core_pad_end(_tall_0, _hat_0, $$String_repeat(" ", _hat_width_0)), $$______bend_core_pad_end(_tall_0, $$List_append($$______bend_core_blanks((_x_2 < _x_3 ? 0 : _x_2 - _x_3)), _lines_0), "")));
}

function $______bend_core_header_under(_hat_0, _lines_0) {
  return $______bend_core_margined($$List_append(_hat_0, {$: "Con", "head": "", "tail": _lines_0}));
}

function $______bend_core_cap_moves(_viewport_0, _at_top_0) {
  return (_viewport_0 || _at_top_0);
}

function $______bend_core_next_frame(_frame_0) {
  return $Nat_mod(nat_chk(_frame_0 + 1), 8);
}

function $______bend_core_blank_lines(_shown_0) {
  if (_shown_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _shown_0["head"];
    const _t_0 = _shown_0["tail"];
    return $Bool_and($$String_is_empty(_h_0), $$List_is_empty(_t_0));
  }
}

function $______bend_core_blank_view(_shown_0, _more_0) {
  return $Bool_and($$______bend_core_blank_lines(_shown_0), $$Nat_is_eq(_more_0, 0));
}

function $______bend_core_more_hint(_more_0) {
  return $String_concat({$: "Con", "head": "... (", "tail": {$: "Con", "head": $$Nat_show(_more_0), "tail": {$: "Con", "head": " more lines,", "tail": {$: "Nil"}}}});
}

function $______bend_core_labels(_plugins_0) {
  if (_plugins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _plugins_0["head"];
    const _name_0 = _t_0["name"];
    const _state_0 = _t_0["state"];
    const _t_1 = _plugins_0["tail"];
    return {$: "Con", "head": $$______bend_core_label(_name_0, _state_0), "tail": $$______bend_core_labels(_t_1)};
  }
}

function $______bend_core_widest(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = [...str_out(_h_0)].length;
    const _x_1 = $$______bend_core_widest(_t_0);
    return (_x_0 > _x_1 ? _x_0 : _x_1);
  }
}

function $______bend_core_pad_right(_s_0, _n_0) {
  const _x_0 = [...str_out(_s_0)].length;
  const _x_1 = $$String_repeat(" ", (_n_0 < _x_0 ? 0 : _n_0 - _x_0));
  return (_s_0 + _x_1);
}

function $______bend_core_wide_rows(_plugins_0, _wide_0) {
  if (_plugins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _plugins_0["head"];
    const _name_0 = _t_0["name"];
    const _state_0 = _t_0["state"];
    const _source_0 = _t_0["source"];
    const _t_1 = _plugins_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": $$______bend_core_pad_right($$______bend_core_label(_name_0, _state_0), _wide_0), "tail": {$: "Con", "head": "  ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Nil"}}}}}), "tail": $$______bend_core_wide_rows(_t_1, _wide_0)};
  }
}

function $______bend_core_plugin_rows(_plugins_0) {
  return $______bend_core_wide_rows(_plugins_0, $$______bend_core_widest($$______bend_core_labels(_plugins_0)));
}

function $______bend_core_plugin_line(_plugins_0) {
  return $String_join($$______bend_core_labels(_plugins_0), ", ");
}

function $______bend_core_indented(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": ("  " + _h_0), "tail": $$______bend_core_indented(_t_0)};
  }
}

function $______bend_core_shape() {
  return $String_join({$: "Con", "head": "A plugin is a .ts or .js file. The smallest one needs no imports:", "tail": {$: "Con", "head": "  export const name = \"weather\"", "tail": {$: "Con", "head": "  export const actions = [{", "tail": {$: "Con", "head": "    name: \"weather\", description: \"Current weather for a city.\",", "tail": {$: "Con", "head": "    parameters: { type: \"object\", properties: { city: { type: \"string\" } }, required: [\"city\"] },", "tail": {$: "Con", "head": "    async execute({ city }, env) { return \"text for the agent\" },   // env: { cwd, signal, update(text), pi (ExtensionContext) }", "tail": {$: "Con", "head": "  }]", "tail": {$: "Con", "head": "For lifecycle or services, export `apply(ctx, config)` (or a default function/class) and use the Cordis context:", "tail": {$: "Con", "head": "ctx.actions.register(action), ctx.on(event, listener), ctx.provide(name, value), `export const inject = [...]`.", "tail": {$: "Con", "head": "ctx.effect(setup) runs setup IMMEDIATELY and keeps its return value as the cleanup on unload; passing the cleanup itself undoes the setup at once.", "tail": {$: "Con", "head": "Events: action/registered, action/changed, action/unregistered, action/before (return a string to refuse the call), action/after, task/end,", "tail": {$: "Con", "head": "pi/ready (Pi's ExtensionAPI is live), pi/session-start (api, piCtx; per-session choices go here: api.setModel, api.setThinkingLevel).", "tail": {$: "Con", "head": "export (dir, wrote): `wizardry export` asks for a copy of what you keep; write <home>/<name>/ into <dir>/<name>/ and call wrote(one line).", "tail": {$: "Con", "head": "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.", "tail": {$: "Con", "head": "Everything a plugin registers is removed when it is unloaded.", "tail": {$: "Con", "head": "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.", "tail": {$: "Con", "head": "Before editing wizardry itself, call cordis_map: the map of the framework you run on.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}, "\n");
}

function $______bend_core_inspect_text(_lines_0, _idle_0) {
  const _x_0 = $$______bend_core_listed(_idle_0);
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "Loaded plugins:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": _lines_0, "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Builtin plugins not loaded: " + _x_0), "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": $$______bend_core_shape(), "tail": {$: "Nil"}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $______bend_core_no_map(_app_0) {
  return $String_concat({$: "Con", "head": "No AGENTS.md in ", "tail": {$: "Con", "head": _app_0, "tail": {$: "Con", "head": ". This wizardry predates it; the repo has it: https://github.com/Pomidium/wizardry", "tail": {$: "Nil"}}}});
}

function $______bend_core_own_pi(_home_0) {
  return (_home_0 + "/pi");
}

function $______bend_core_old_pi(_named_0, _userhome_0) {
  return $Bool_pick($$String_is_empty(_named_0), (_userhome_0 + "/.pi/agent"), _named_0);
}

function $______bend_core_pi_env(_home_0) {
  return {$: "Con", "head": {$: "Var", "name": "PI_CODING_AGENT_DIR", "value": $$______bend_core_own_pi(_home_0)}, "tail": {$: "Con", "head": {$: "Var", "name": "PI_SKIP_VERSION_CHECK", "value": "1"}, "tail": {$: "Con", "head": {$: "Var", "name": "PI_TELEMETRY", "value": "0"}, "tail": {$: "Nil"}}}};
}

function $______bend_core_pi_env_cleared() {
  return {$: "Con", "head": "PI_CODING_AGENT_SESSION_DIR", "tail": {$: "Con", "head": "PI_PACKAGE_DIR", "tail": {$: "Nil"}}};
}

function $______bend_core_var_names(_vars_0) {
  if (_vars_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _vars_0["head"];
    const _name_0 = _t_0["name"];
    const _t_1 = _vars_0["tail"];
    return {$: "Con", "head": _name_0, "tail": $$______bend_core_var_names(_t_1)};
  }
}

function $______bend_core_pi_env_touched() {
  return $List_append($$______bend_core_var_names($$______bend_core_pi_env("")), $$______bend_core_pi_env_cleared());
}

function $______bend_core_brought_files() {
  return {$: "Con", "head": "auth.json", "tail": {$: "Con", "head": "models.json", "tail": {$: "Nil"}}};
}

function $______bend_core_brought_settings() {
  return {$: "Con", "head": "defaultProvider", "tail": {$: "Con", "head": "defaultModel", "tail": {$: "Con", "head": "defaultThinkingLevel", "tail": {$: "Con", "head": "modelThinkingLevels", "tail": {$: "Con", "head": "enabledModels", "tail": {$: "Con", "head": "httpProxy", "tail": {$: "Con", "head": "shellPath", "tail": {$: "Con", "head": "shellCommandPrefix", "tail": {$: "Nil"}}}}}}}}};
}

function $______bend_core_pi_addons() {
  return {$: "Con", "head": "packages", "tail": {$: "Con", "head": "extensions", "tail": {$: "Con", "head": "skills", "tail": {$: "Con", "head": "prompts", "tail": {$: "Con", "head": "themes", "tail": {$: "Con", "head": "enableSkillCommands", "tail": {$: "Con", "head": "sessionDir", "tail": {$: "Con", "head": "defaultProjectTrust", "tail": {$: "Con", "head": "selfUpdateCommand", "tail": {$: "Nil"}}}}}}}}}};
}

function $______bend_core_settings_brought(_keys_0) {
  return $______bend_core_only(_keys_0, $$______bend_core_brought_settings());
}

function $______bend_core_brings(_has_own_0, _has_old_0, _old_0, _own_0) {
  return $Bool_and($$Bool_not(_has_own_0), $$Bool_and(_has_old_0, $$Bool_not($$String_eq(_old_0, _own_0))));
}

function $______bend_core_brought_list(_files_0) {
  if (_files_0.$ === "Nil") {
    return "There was nothing to bring over from ";
  } else {
    const _h_0 = _files_0["head"];
    const _t_0 = _files_0["tail"];
    return $String_concat({$: "Con", "head": "Brought over ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", "), "tail": {$: "Con", "head": " from ", "tail": {$: "Nil"}}}});
  }
}

function $______bend_core_brought_said(_files_0, _own_0, _old_0) {
  return $String_concat({$: "Con", "head": "logins and settings are now its own, in ", "tail": {$: "Con", "head": _own_0, "tail": {$: "Con", "head": ". ", "tail": {$: "Con", "head": $$______bend_core_brought_list(_files_0), "tail": {$: "Con", "head": _old_0, "tail": {$: "Con", "head": ", which is no longer read: `wizardry delete old` removes it, and `wizardry auth login` signs in here.", "tail": {$: "Nil"}}}}}}});
}

function $______bend_core_with_slash(_dir_0) {
  return $Bool_pick($$String_ends_with(_dir_0, "/"), _dir_0, (_dir_0 + "/"));
}

function $______bend_core_inside(_path_0, _root_0) {
  const _x_0 = $$String_eq(_path_0, _root_0);
  const _x_1 = $$String_starts_with(_path_0, $$______bend_core_with_slash(_root_0));
  return (_x_0 || _x_1);
}

function $______bend_core_takes(_paths_0, _keep_0) {
  if (_paths_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    const _x_0 = $$______bend_core_inside(_keep_0, _h_0);
    const _x_1 = $$______bend_core_takes(_t_0, _keep_0);
    return (_x_0 || _x_1);
  }
}

function $______bend_core_sparing(_paths_0, _keep_0) {
  return $Bool_pick($$______bend_core_takes(_paths_0, _keep_0), {$: "Nil"}, _paths_0);
}

function $______bend_core_all_rooted(_paths_0) {
  if (_paths_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    return $Bool_and($$String_starts_with(_h_0, "/"), $$______bend_core_all_rooted(_t_0));
  }
}

function $______bend_core_rooted(_paths_0) {
  return $Bool_pick($$______bend_core_all_rooted(_paths_0), _paths_0, {$: "Nil"});
}

function $______bend_core_parent_go(_rev_0) {
  if (_rev_0 === "") {
    return "";
  } else {
    const _h_0 = _rev_0.slice(0, char_len(_rev_0));
    const _t_0 = _rev_0.slice(char_len(_rev_0));
    return $Bool_pick($$Char_is_eq(_h_0, "/"), $$String_reverse(_t_0), $$______bend_core_parent_go(_t_0));
  }
}

function $______bend_core_parent(_path_0) {
  return $______bend_core_parent_go($$String_reverse(_path_0));
}

function $______bend_core_parents(_paths_0) {
  if (_paths_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    return {$: "Con", "head": $$______bend_core_parent(_h_0), "tail": $$______bend_core_parents(_t_0)};
  }
}

function $______bend_core_sessions_dir(_home_0) {
  return $______bend_core_in_dir(_home_0, "sessions");
}

function $______bend_core_export_dir(_chosen_0, _userhome_0, _day_0, _again_0) {
  const _x_0 = $$Nat_show(nat_chk(_again_0 + 1));
  return $Bool_pick($$String_is_empty(_chosen_0), $$String_concat({$: "Con", "head": _userhome_0, "tail": {$: "Con", "head": "/wizardry-export-", "tail": {$: "Con", "head": _day_0, "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_again_0, 0), "", ("-" + _x_0)), "tail": {$: "Nil"}}}}}), _chosen_0);
}

function $______bend_core_origins(_home_0, _old_0) {
  return {$: "Con", "head": {$: "Origin", "name": "wizardry", "dir": $$______bend_core_sessions_dir(_home_0)}, "tail": {$: "Con", "head": {$: "Origin", "name": "pi", "dir": $$______bend_core_in_dir(_old_0, "sessions")}, "tail": {$: "Nil"}}};
}

function $______bend_core_origin_dirs(_origins_0) {
  if (_origins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _origins_0["head"];
    const _dir_0 = _t_0["dir"];
    const _t_1 = _origins_0["tail"];
    return {$: "Con", "head": _dir_0, "tail": $$______bend_core_origin_dirs(_t_1)};
  }
}

function $______bend_core_export_fits(_dir_0, _home_0, _old_0) {
  return $Bool_not($$______bend_core_takes($$______bend_core_origin_dirs($$______bend_core_origins(_home_0, _old_0)), _dir_0));
}

function $______bend_core_is_conversation(_name_0) {
  return $String_ends_with(_name_0, ".jsonl");
}

function $______bend_core_conversation_to(_dir_0, _origin_0, _rel_0) {
  const _x_0 = $$String_concat({$: "Con", "head": "/conversations/", "tail": {$: "Con", "head": _origin_0, "tail": {$: "Con", "head": "/", "tail": {$: "Con", "head": _rel_0, "tail": {$: "Nil"}}}}});
  return (_dir_0 + _x_0);
}

function $______bend_core_readable(_path_0) {
  const _x_0 = [...str_out(_path_0)].length;
  const _x_1 = $$String_take(_path_0, (_x_0 < 6 ? 0 : _x_0 - 6));
  return $Bool_pick($$String_ends_with(_path_0, ".jsonl"), (_x_1 + ".md"), (_path_0 + ".md"));
}

function $______bend_core_minute(_stamp_0) {
  return $String_take(_stamp_0, 16);
}

function $______bend_core_transcript_head(_file_0, _cwd_0, _started_0) {
  return $String_concat({$: "Con", "head": "# Conversation of ", "tail": {$: "Con", "head": $$______bend_core_minute(_started_0), "tail": {$: "Con", "head": "\n\n- Directory: ", "tail": {$: "Con", "head": _cwd_0, "tail": {$: "Con", "head": "\n- Kept whole in: ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}}}});
}

function $______bend_core_voice_of(_kind_0) {
  return $Bool_pick($$String_eq(_kind_0, "user"), {$: "Said", "who": "User"}, $$Bool_pick($$String_eq(_kind_0, "assistant"), {$: "Said", "who": "Assistant"}, $$Bool_pick($$String_eq(_kind_0, "toolCall"), {$: "Call"}, $$Bool_pick($$String_eq(_kind_0, "toolResult"), {$: "Result"}, $$Bool_pick($$String_eq(_kind_0, "bashExecution"), {$: "Ran"}, $$Bool_pick($$String_eq(_kind_0, "image"), {$: "Image"}, $$Bool_pick($$______bend_core_has({$: "Con", "head": "compaction", "tail": {$: "Con", "head": "branch_summary", "tail": {$: "Nil"}}}, _kind_0), {$: "Said", "who": "Summary of what came before"}, $$Bool_pick($$String_eq(_kind_0, "custom_message"), {$: "Said", "who": "Note"}, $$Bool_pick($$String_eq(_kind_0, "error"), {$: "Said", "who": "Error"}, {$: "Silent"})))))))));
}

function $______bend_core_said_block(_who_0, _at_0, _body_0) {
  return $Bool_pick($$String_is_empty(_body_0), "", $$String_concat({$: "Con", "head": "## ", "tail": {$: "Con", "head": _who_0, "tail": {$: "Con", "head": " · ", "tail": {$: "Con", "head": $$______bend_core_minute(_at_0), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": _body_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}}}}));
}

function $______bend_core_more_lines(_more_0) {
  return $Bool_pick($$Nat_is_eq(_more_0, 0), "", $$String_concat({$: "Con", "head": "\n    ... ", "tail": {$: "Con", "head": $$Nat_show(_more_0), "tail": {$: "Con", "head": " more lines, in the .jsonl", "tail": {$: "Nil"}}}}));
}

function $______bend_core_shown_block(_view_0) {
  const _shown_0 = _view_0["shown"];
  const _more_0 = _view_0["more"];
  return $String_concat({$: "Con", "head": "    ", "tail": {$: "Con", "head": $$String_join(_shown_0, "\n    "), "tail": {$: "Con", "head": $$______bend_core_more_lines(_more_0), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}});
}

function $______bend_core_result_block(_text_0) {
  return $______bend_core_shown_block($$______bend_core_result_view(_text_0, false));
}

function $______bend_core_call_line(_name_0, _args_0) {
  return $String_concat({$: "Con", "head": "> **", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "** ", "tail": {$: "Con", "head": $$______bend_core_clip($$______bend_core_squash(_args_0, false), 200), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}});
}

function $______bend_core_piece_as(_voice_0, _name_0, _at_0, _text_0) {
  if (_voice_0.$ === "Said") {
    const _who_0 = _voice_0["who"];
    return $______bend_core_said_block(_who_0, _at_0, $$String_trim_end(_text_0));
  } else if (_voice_0.$ === "Call") {
    return $______bend_core_call_line(_name_0, _text_0);
  } else if (_voice_0.$ === "Result") {
    return $______bend_core_result_block(_text_0);
  } else if (_voice_0.$ === "Ran") {
    const _x_0 = $$______bend_core_call_line("$", _name_0);
    const _x_1 = $$______bend_core_result_block(_text_0);
    return (_x_0 + _x_1);
  } else if (_voice_0.$ === "Image") {
    return "*(an image)*\n\n";
  } else {
    return "";
  }
}

function $______bend_core_piece(_kind_0, _name_0, _at_0, _text_0) {
  return $______bend_core_piece_as($$______bend_core_voice_of(_kind_0), _name_0, _at_0, _text_0);
}

function $______bend_core_counted(_n_0, _one_0, _many_0) {
  return $String_concat({$: "Con", "head": $$Nat_show(_n_0), "tail": {$: "Con", "head": " ", "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_n_0, 1), _one_0, _many_0), "tail": {$: "Nil"}}}});
}

function $______bend_core_tally_lines(_tallies_0) {
  if (_tallies_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _tallies_0["head"];
    const _name_0 = _t_0["name"];
    const _from_0 = _t_0["from"];
    const _count_0 = _t_0["count"];
    const _t_1 = _tallies_0["tail"];
    return $______bend_core_keep_if($$Bool_not($$Nat_is_eq(_count_0, 0)), $$String_concat({$: "Con", "head": $$______bend_core_counted(_count_0, "conversation", "conversations"), "tail": {$: "Con", "head": " from ", "tail": {$: "Con", "head": _from_0, "tail": {$: "Con", "head": ", in conversations/", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "/", "tail": {$: "Nil"}}}}}}}), $$______bend_core_tally_lines(_t_1));
  }
}

function $______bend_core_bulleted(_lines_0) {
  if (_lines_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _lines_0["head"];
    const _t_0 = _lines_0["tail"];
    return {$: "Con", "head": ("- " + _h_0), "tail": $$______bend_core_bulleted(_t_0)};
  }
}

function $______bend_core_or_nothing(_lines_0) {
  if (_lines_0.$ === "Nil") {
    return {$: "Con", "head": "nothing: no conversation and no memory was found", "tail": {$: "Nil"}};
  } else {
    const _h_0 = _lines_0["head"];
    const _t_0 = _lines_0["tail"];
    return {$: "Con", "head": _h_0, "tail": _t_0};
  }
}

function $______bend_core_own_folders() {
  return {$: "Con", "head": "app", "tail": {$: "Con", "head": "plugins", "tail": {$: "Con", "head": "sessions", "tail": {$: "Con", "head": "pi", "tail": {$: "Con", "head": "update.lock", "tail": {$: "Con", "head": "tools", "tail": {$: "Con", "head": "bin", "tail": {$: "Nil"}}}}}}}};
}

function $______bend_core_left_over(_folders_0, _written_0) {
  return $______bend_core_without($$______bend_core_without(_folders_0, $$______bend_core_own_folders()), _written_0);
}

function $______bend_core_left_over_line(_name_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": "/ as it was kept: no loaded plugin exported it", "tail": {$: "Nil"}}});
}

function $______bend_core_export_lines(_tallies_0, _wrote_0) {
  return $______bend_core_or_nothing($$List_append($$______bend_core_tally_lines(_tallies_0), _wrote_0));
}

function $______bend_core_export_readme(_day_0, _lines_0) {
  return $String_concat({$: "Con", "head": "# wizardry export of ", "tail": {$: "Con", "head": _day_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": "Everything here is a copy: nothing was removed from where it was kept.\n\n", "tail": {$: "Con", "head": $$String_join($$______bend_core_bulleted(_lines_0), "\n"), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": "Each conversation is here twice. The `.jsonl` is the session exactly as it was kept, and\n", "tail": {$: "Con", "head": "`wizardry --session <that file>` carries it on. The `.md` beside it is the same conversation\n", "tail": {$: "Con", "head": "as text to read.\n", "tail": {$: "Nil"}}}}}}}}}});
}

function $______bend_core_export_said(_dir_0, _lines_0) {
  return $String_concat({$: "Con", "head": "exported to ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": ":\n", "tail": {$: "Con", "head": $$String_join($$______bend_core_indented(_lines_0), "\n"), "tail": {$: "Con", "head": "\n", "tail": {$: "Nil"}}}}}});
}

function $______bend_core_export_inside(_dir_0) {
  return $String_concat({$: "Con", "head": "not exported: ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": " is inside the conversations it would copy. Name another folder.", "tail": {$: "Nil"}}}});
}

function $______bend_core_export_taken(_dir_0) {
  return $String_concat({$: "Con", "head": "not exported: ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": " is not empty. Name a new folder, so that nothing in it is overwritten.", "tail": {$: "Nil"}}}});
}

function $______bend_core_export_broke(_why_0) {
  return ("the export did not finish: " + _why_0);
}

function $______bend_core_export_usage() {
  return "usage: wizardry export [folder]";
}

function $______bend_core_is_option(_arg_0) {
  return $String_starts_with(_arg_0, "-");
}

function $______bend_core_bare(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    const _x_0 = $$______bend_core_is_option(_h_0);
    return $______bend_core_keep_if($$Bool_not((_value_0 || _x_0)), _h_0, $$______bend_core_bare(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--to"))));
  }
}

function $______bend_core_options(_argv_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $______bend_core_keep_if($$______bend_core_is_option(_h_0), _h_0, $$______bend_core_options(_t_0));
  }
}

function $______bend_core_first_of(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _xs_0["head"];
    return _h_0;
  }
}

function $______bend_core_value_after(_argv_0, _flag_0) {
  if (_argv_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $Bool_pick($$String_eq(_h_0, _flag_0), $$______bend_core_first_of(_t_0), $$______bend_core_value_after(_t_0, _flag_0));
  }
}

function $______bend_core_export_asked(_argv_0) {
  const _words_0 = $$______bend_core_bare(_argv_0, false);
  const _x_0 = $$List_length(_words_0);
  return $Bool_pick($$Bool_and($$List_is_empty($$______bend_core_options(_argv_0)), (_x_0 < 2)), {$: "Some", "value": $$______bend_core_first_of(_words_0)}, {$: "None"});
}

function $______bend_core_delete_asked(_argv_0) {
  const _words_0 = $$______bend_core_bare(_argv_0, false);
  const _x_0 = $$______bend_core_has(_argv_0, "--yes");
  const _x_1 = $$______bend_core_has(_argv_0, "-y");
  return {$: "Removal", "what": $$______bend_core_first_of(_words_0), "yes": (_x_0 || _x_1), "waived": $$______bend_core_has(_argv_0, "--no-export"), "to": $$______bend_core_value_after(_argv_0, "--to"), "clear": $$Bool_and($$Nat_is_eq($$List_length(_words_0), 1), $$______bend_core_covers({$: "Con", "head": "--yes", "tail": {$: "Con", "head": "-y", "tail": {$: "Con", "head": "--no-export", "tail": {$: "Con", "head": "--to", "tail": {$: "Nil"}}}}}, $$______bend_core_options(_argv_0)))};
}

function $______bend_core_what_pick(_conversations_0, _memories_0, _old_0, _all_0) {
  if (_conversations_0) {
    return {$: "Conversations"};
  } else {
    if (_memories_0) {
      return {$: "Memories"};
    } else {
      if (_old_0) {
        return {$: "Old"};
      } else {
        if (_all_0) {
          return {$: "All"};
        } else {
          return {$: "Unknown"};
        }
      }
    }
  }
}

function $______bend_core_what_of(_word_0) {
  return $______bend_core_what_pick($$String_eq(_word_0, "conversations"), $$String_eq(_word_0, "memories"), $$String_eq(_word_0, "old"), $$String_eq(_word_0, "all"));
}

function $______bend_core_old_wanted(_old_0, _home_0) {
  return $______bend_core_sparing($$Bool_pick($$______bend_core_inside(_old_0, _home_0), {$: "Nil"}, {$: "Con", "head": _old_0, "tail": {$: "Nil"}}), _home_0);
}

function $______bend_core_based(_home_0, _paths_0) {
  return $______bend_core_unless($$Bool_not($$String_starts_with(_home_0, "/")), _paths_0);
}

function $______bend_core_wanted(_what_0, _home_0, _old_0) {
  if (_what_0.$ === "Conversations") {
    return $______bend_core_based(_home_0, {$: "Con", "head": $$______bend_core_sessions_dir(_home_0), "tail": {$: "Nil"}});
  } else if (_what_0.$ === "Memories") {
    return $______bend_core_based(_home_0, {$: "Con", "head": $$______bend_core_in_dir(_home_0, "memory"), "tail": {$: "Nil"}});
  } else if (_what_0.$ === "Old") {
    return $______bend_core_based(_home_0, $$______bend_core_old_wanted(_old_0, _home_0));
  } else if (_what_0.$ === "All") {
    return $______bend_core_based(_home_0, {$: "Con", "head": _home_0, "tail": {$: "Nil"}});
  } else {
    return {$: "Nil"};
  }
}

function $______bend_core_doomed(_what_0, _home_0, _old_0, _userhome_0, _to_0) {
  return $______bend_core_sparing($$______bend_core_sparing($$______bend_core_rooted($$______bend_core_wanted(_what_0, _home_0, _old_0)), _userhome_0), _to_0);
}

function $______bend_core_goes(_paths_0, _yes_0, _exported_0) {
  if (_yes_0) {
    if (_exported_0.$ === "Kept") {
      return _paths_0;
    } else if (_exported_0.$ === "Waived") {
      return _paths_0;
    } else {
      return {$: "Nil"};
    }
  } else {
    return {$: "Nil"};
  }
}

function $______bend_core_emptied(_what_0, _doomed_0, _userhome_0) {
  if (_what_0.$ === "Old") {
    return $______bend_core_sparing($$______bend_core_rooted($$______bend_core_parents(_doomed_0)), _userhome_0);
  } else if (_what_0.$ === "Conversations") {
    return {$: "Nil"};
  } else if (_what_0.$ === "Memories") {
    return {$: "Nil"};
  } else if (_what_0.$ === "All") {
    return {$: "Nil"};
  } else {
    return {$: "Nil"};
  }
}

function $______bend_core_dangling(_links_0, _doomed_0) {
  if (_links_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _links_0["head"];
    const _path_0 = _t_0["path"];
    const _target_0 = _t_0["target"];
    const _t_1 = _links_0["tail"];
    return $______bend_core_keep_if($$______bend_core_takes(_doomed_0, _target_0), _path_0, $$______bend_core_dangling(_t_1, _doomed_0));
  }
}

function $______bend_core_link_dirs(_invoked_0, _named_0, _userhome_0) {
  return $______bend_core_without($$______bend_core_add($$______bend_core_add({$: "Con", "head": $$______bend_core_parent(_invoked_0), "tail": {$: "Nil"}}, _named_0), (_userhome_0 + "/.local/bin")), {$: "Con", "head": "", "tail": {$: "Nil"}});
}

function $______bend_core_old_home_link(_userhome_0) {
  return (_userhome_0 + "/.izardry");
}

function $______bend_core_delete_usage() {
  return $String_join({$: "Con", "head": "usage: wizardry delete <what> [--yes] [--to <folder>] [--no-export]", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "  conversations   every conversation wizardry has kept", "tail": {$: "Con", "head": "  memories        everything wizardry remembers", "tail": {$: "Con", "head": "  old             Pi's own setup, which wizardry no longer reads: its logins, settings,", "tail": {$: "Con", "head": "                  conversations, extensions and the pi program", "tail": {$: "Con", "head": "  all             all of wizardry: the program, its plugins, logins, conversations and memories", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Without --yes it says what would be deleted and deletes nothing. With --yes it first exports", "tail": {$: "Con", "head": "every conversation and memory (to --to <folder>, else ~/wizardry-export-<day>), and deletes", "tail": {$: "Con", "head": "only once that is done; --no-export skips the export.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}}}}}}}}, "\n");
}

function $______bend_core_why_pick(_unknown_0, _based_0, _none_0, _loose_0, _home_0, _export_0, _old_0, _to_0) {
  if (_unknown_0) {
    return "say what to delete: conversations, memories, old or all";
  } else {
    if (!_based_0) {
      return "nothing was deleted: wizardry's directory is not a full path";
    } else {
      if (_none_0) {
        return $String_concat({$: "Con", "head": "nothing to delete: Pi's own directory (", "tail": {$: "Con", "head": _old_0, "tail": {$: "Con", "head": ") is wizardry's, inside it, or holds it, so it is not an old setup", "tail": {$: "Nil"}}}});
      } else {
        if (_loose_0) {
          return $String_concat({$: "Con", "head": "nothing was deleted: ", "tail": {$: "Con", "head": _old_0, "tail": {$: "Con", "head": " is not a full path", "tail": {$: "Nil"}}}});
        } else {
          if (_home_0) {
            return "nothing was deleted: that would take your home directory along";
          } else {
            if (_export_0) {
              return $String_concat({$: "Con", "head": "nothing was deleted: the export would go to ", "tail": {$: "Con", "head": _to_0, "tail": {$: "Con", "head": ", inside what is deleted. Name another folder with --to.", "tail": {$: "Nil"}}}});
            } else {
              return "";
            }
          }
        }
      }
    }
  }
}

function $______bend_core_is_unknown(_what_0) {
  if (_what_0.$ === "Unknown") {
    return true;
  } else if (_what_0.$ === "Conversations") {
    return false;
  } else if (_what_0.$ === "Memories") {
    return false;
  } else if (_what_0.$ === "Old") {
    return false;
  } else {
    return false;
  }
}

function $______bend_core_why_not(_what_0, _home_0, _old_0, _userhome_0, _to_0) {
  const _paths_0 = $$______bend_core_wanted(_what_0, _home_0, _old_0);
  return $______bend_core_why_pick($$______bend_core_is_unknown(_what_0), $$String_starts_with(_home_0, "/"), $$List_is_empty(_paths_0), $$Bool_not($$______bend_core_all_rooted(_paths_0)), $$______bend_core_takes(_paths_0, _userhome_0), $$______bend_core_takes(_paths_0, _to_0), _old_0, _to_0);
}

function $______bend_core_size_text(_bytes_0) {
  const _x_0 = (1000 );
  const _x_1 = (1000000 );
  const _x_2 = $$Nat_show($$Nat_div(_bytes_0, (1000 )));
  const _x_3 = (1000000000 );
  const _x_4 = $$Nat_show($$Nat_div(_bytes_0, (1000000 )));
  const _x_5 = $$Nat_show($$Nat_div(_bytes_0, (1000000000 )));
  return $Bool_pick((_bytes_0 < _x_0), $$______bend_core_counted(_bytes_0, "byte", "bytes"), $$Bool_pick((_bytes_0 < _x_1), (_x_2 + " KB"), $$Bool_pick((_bytes_0 < _x_3), (_x_4 + " MB"), (_x_5 + " GB"))));
}

function $______bend_core_row_lines(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _rows_0["head"];
    const _path_0 = _t_0["path"];
    const _bytes_0 = _t_0["bytes"];
    const _t_1 = _rows_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": _path_0, "tail": {$: "Con", "head": "  (", "tail": {$: "Con", "head": $$______bend_core_size_text(_bytes_0), "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}}}}), "tail": $$______bend_core_row_lines(_t_1)};
  }
}

function $______bend_core_link_lines(_links_0) {
  if (_links_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _links_0["head"];
    const _t_0 = _links_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": "  (a command that points into it)", "tail": {$: "Nil"}}}}), "tail": $$______bend_core_link_lines(_t_0)};
  }
}

function $______bend_core_export_line(_waived_0, _to_0, _first_0, _then_0) {
  if (_waived_0) {
    return "Nothing is exported first: you said --no-export.";
  } else {
    return $String_concat({$: "Con", "head": _first_0, "tail": {$: "Con", "head": _to_0, "tail": {$: "Con", "head": _then_0, "tail": {$: "Nil"}}}});
  }
}

function $______bend_core_delete_preview(_word_0, _rows_0, _links_0, _to_0, _waived_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": $$String_concat({$: "Con", "head": "wizardry delete ", "tail": {$: "Con", "head": _word_0, "tail": {$: "Con", "head": " would delete:", "tail": {$: "Nil"}}}}), "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$______bend_core_row_lines(_rows_0), "tail": {$: "Con", "head": $$______bend_core_link_lines(_links_0), "tail": {$: "Con", "head": {$: "Con", "head": $$______bend_core_export_line(_waived_0, _to_0, "First, every conversation and memory is exported to ", "."), "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "Nothing has been deleted. To go ahead: wizardry delete ", "tail": {$: "Con", "head": _word_0, "tail": {$: "Con", "head": " --yes", "tail": {$: "Con", "head": $$Bool_pick(_waived_0, " --no-export", ""), "tail": {$: "Nil"}}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}, "tail": {$: "Nil"}}}}}), "\n");
}

function $______bend_core_deleted_said(_rows_0, _links_0, _to_0, _waived_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "deleted:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$______bend_core_row_lines(_rows_0), "tail": {$: "Con", "head": $$______bend_core_link_lines(_links_0), "tail": {$: "Con", "head": {$: "Con", "head": $$______bend_core_export_line(_waived_0, _to_0, "Every conversation and memory was exported first, to ", "."), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Nil"}}}}}), "\n");
}

function $______bend_core_nothing_there(_what_0) {
  if (_what_0.$ === "Conversations") {
    return "nothing to delete: wizardry has kept no conversation";
  } else if (_what_0.$ === "Memories") {
    return "nothing to delete: wizardry remembers nothing";
  } else if (_what_0.$ === "Old") {
    return "nothing to delete: there is no setup of Pi's own on this machine";
  } else if (_what_0.$ === "All") {
    return "nothing to delete: wizardry's directory is not there";
  } else {
    return "nothing to delete";
  }
}

function $______bend_core_export_first_failed(_why_0) {
  return $String_concat({$: "Con", "head": "nothing was deleted: the export did not finish (", "tail": {$: "Con", "head": _why_0, "tail": {$: "Con", "head": "). Fix that, or pass --no-export to delete without one.", "tail": {$: "Nil"}}}});
}

function $______bend_core_setting(_name_0, _value_0) {
  return $Bool_pick($$String_is_empty(_value_0), {$: "Nil"}, {$: "Con", "head": {$: "Var", "name": _name_0, "value": _value_0}, "tail": {$: "Nil"}});
}

function $______bend_core_default_settings(_provider_0, _model_0, _thinking_0) {
  return $List_concat({$: "Con", "head": $$______bend_core_setting("defaultProvider", _provider_0), "tail": {$: "Con", "head": $$______bend_core_setting("defaultModel", _model_0), "tail": {$: "Con", "head": $$______bend_core_setting("defaultThinkingLevel", _thinking_0), "tail": {$: "Nil"}}}});
}

function $______bend_core_kept_off(_would_load_0, _loaded_0) {
  return $______bend_core_without(_would_load_0, _loaded_0);
}

function $______bend_core_or_unset(_value_0) {
  return $Bool_pick($$String_is_empty(_value_0), "as it was", _value_0);
}

function $______bend_core_default_said(_model_0, _thinking_0, _plugins_0) {
  return $String_concat({$: "Con", "head": "New sessions now start as this one. Model: ", "tail": {$: "Con", "head": $$______bend_core_or_unset(_model_0), "tail": {$: "Con", "head": ". Thinking: ", "tail": {$: "Con", "head": $$______bend_core_or_unset(_thinking_0), "tail": {$: "Con", "head": ". Plugins: ", "tail": {$: "Con", "head": $$String_join(_plugins_0, ", "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}}}}}});
}

function $is_folder(_entry_0) {
  return $String_ends_with(_entry_0, "/");
}

function $covers(_entry_0, _path_0) {
  const _x_0 = $$String_eq(_entry_0, _path_0);
  const _x_1 = $$Bool_and($$is_folder(_entry_0), $$String_starts_with(_path_0, _entry_0));
  return (_x_0 || _x_1);
}

function $may_write(_entries_0, _path_0) {
  if (_entries_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _entries_0["head"];
    const _t_0 = _entries_0["tail"];
    const _x_0 = $$covers(_h_0, _path_0);
    const _x_1 = $$may_write(_t_0, _path_0);
    return (_x_0 || _x_1);
  }
}

function $may(_owns_0, _path_0) {
  if (_owns_0.$ === "All") {
    return true;
  } else {
    const _entries_0 = _owns_0["entries"];
    return $may_write(_entries_0, _path_0);
  }
}

function $clash(_a_0, _b_0) {
  const _x_0 = $$covers(_a_0, _b_0);
  const _x_1 = $$covers(_b_0, _a_0);
  return (_x_0 || _x_1);
}

function $clashes(_a_0, _bs_0) {
  if (_bs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _bs_0["head"];
    const _t_0 = _bs_0["tail"];
    const _x_0 = $$clash(_a_0, _h_0);
    const _x_1 = $$clashes(_a_0, _t_0);
    return (_x_0 || _x_1);
  }
}

function $overlap(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$clashes(_h_0, _ys_0);
    const _x_1 = $$overlap(_t_0, _ys_0);
    return (_x_0 || _x_1);
  }
}

function $inside(_entries_0, _parent_0) {
  if (_entries_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _entries_0["head"];
    const _t_0 = _entries_0["tail"];
    return $Bool_and($$may(_parent_0, _h_0), $$inside(_t_0, _parent_0));
  }
}

function $names_of(_pieces_0) {
  if (_pieces_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _pieces_0["head"];
    const _name_0 = _t_0["name"];
    const _t_1 = _pieces_0["tail"];
    return {$: "Con", "head": _name_0, "tail": $$names_of(_t_1)};
  }
}

function $owns_of(_pieces_0) {
  if (_pieces_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _pieces_0["head"];
    const _owns_0 = _t_0["owns"];
    const _t_1 = _pieces_0["tail"];
    return {$: "Con", "head": _owns_0, "tail": $$owns_of(_t_1)};
  }
}

function $laws_of(_pieces_0) {
  if (_pieces_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _pieces_0["head"];
    const _laws_0 = _t_0["laws"];
    const _t_1 = _pieces_0["tail"];
    return $List_append(_laws_0, $$laws_of(_t_1));
  }
}

function $distinct(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Bool_and($$Bool_not($$______bend_core_has(_t_0, _h_0)), $$distinct(_t_0));
  }
}

function $shares(_mine_0, _others_0) {
  if (_others_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _others_0["head"];
    const _t_0 = _others_0["tail"];
    const _x_0 = $$overlap(_mine_0, _h_0);
    const _x_1 = $$shares(_mine_0, _t_0);
    return (_x_0 || _x_1);
  }
}

function $disjoint(_owns_0) {
  if (_owns_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _owns_0["head"];
    const _t_0 = _owns_0["tail"];
    return $Bool_and($$Bool_not($$shares(_h_0, _t_0)), $$disjoint(_t_0));
  }
}

function $all_inside(_owns_0, _parent_0) {
  if (_owns_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _owns_0["head"];
    const _t_0 = _owns_0["tail"];
    return $Bool_and($$inside(_h_0, _parent_0), $$all_inside(_t_0, _parent_0));
  }
}

function $one_if(_b_0) {
  if (_b_0) {
    return 1;
  } else {
    return 0;
  }
}

function $writers(_owns_0, _path_0) {
  if (_owns_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _owns_0["head"];
    const _t_0 = _owns_0["tail"];
    const _x_0 = $$one_if($$may_write(_h_0, _path_0));
    const _x_1 = $$writers(_t_0, _path_0);
    return nat_chk(_x_0 + _x_1);
  }
}

function $guard(_bad_0, _why_0, _rest_0) {
  if (_bad_0) {
    return {$: "Refuse", "why": _why_0};
  } else {
    return _rest_0;
  }
}

function $verdict(_deep_0, _none_0, _names_0, _laws_0, _outside_0, _trample_0) {
  return $guard(_deep_0, {$: "TooDeep"}, $$guard(_none_0, {$: "NoParts"}, $$guard(_names_0, {$: "SameName"}, $$guard(_laws_0, {$: "SharedLaw"}, $$guard(_outside_0, {$: "Outside"}, $$guard(_trample_0, {$: "Trample"}, {$: "Divide"}))))));
}

function $judge(_depth_0, _limit_0, _parent_0, _pieces_0) {
  return $verdict($$Bool_not((_depth_0 < _limit_0)), $$List_is_empty(_pieces_0), $$Bool_not($$distinct($$names_of(_pieces_0))), $$Bool_not($$distinct($$laws_of(_pieces_0))), $$Bool_not($$all_inside($$owns_of(_pieces_0), _parent_0)), $$Bool_not($$disjoint($$owns_of(_pieces_0))));
}

function $runs_on(_choice_0, _session_0) {
  return $Bool_pick($$String_is_empty(_choice_0), _session_0, _choice_0);
}

function $kept(_value_0) {
  return $Bool_pick($$String_eq(_value_0, "same"), "", _value_0);
}

function $levels() {
  return {$: "Con", "head": "same", "tail": {$: "Con", "head": "off", "tail": {$: "Con", "head": "minimal", "tail": {$: "Con", "head": "low", "tail": {$: "Con", "head": "medium", "tail": {$: "Con", "head": "high", "tail": {$: "Con", "head": "xhigh", "tail": {$: "Con", "head": "max", "tail": {$: "Nil"}}}}}}}}};
}

function $wants_pick(_empty_0, _model_0, _thinking_0) {
  if (_empty_0) {
    return {$: "Show"};
  } else {
    if (_model_0) {
      return {$: "Model"};
    } else {
      if (_thinking_0) {
        return {$: "Thinking"};
      } else {
        return {$: "Unclear"};
      }
    }
  }
}

function $wants(_word_0) {
  return $wants_pick($$String_is_empty(_word_0), $$String_eq(_word_0, "model"), $$String_eq(_word_0, "thinking"));
}

function $is_name_start(_c_0) {
  const _x_0 = $$Char_is_alpha(_c_0);
  const _x_1 = $$Char_is_eq(_c_0, "_");
  return (_x_0 || _x_1);
}

function $is_name_char(_c_0) {
  const _x_0 = $$Char_is_eq(_c_0, "_");
  const _x_1 = $$Char_is_eq(_c_0, ".");
  const _x_2 = $$Char_is_digit(_c_0);
  const _x_3 = (_x_0 || _x_1);
  const _x_4 = $$Char_is_alpha(_c_0);
  const _x_5 = (_x_2 || _x_3);
  return (_x_4 || _x_5);
}

function $name_put(_keep_0, _c_0, _rest_0) {
  if (_keep_0) {
    return (_c_0 + _rest_0);
  } else {
    return "";
  }
}

function $name_of(_s_0) {
  if (_s_0 === "") {
    return "";
  } else {
    const _c_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    return $name_put($$is_name_char(_c_0), _c_0, $$name_of(_t_0));
  }
}

function $starts_name(_s_0) {
  if (_s_0 === "") {
    return false;
  } else {
    const _c_0 = _s_0.slice(0, char_len(_s_0));
    return $is_name_start(_c_0);
  }
}

function $starts_space(_s_0) {
  if (_s_0 === "") {
    return false;
  } else {
    const _c_0 = _s_0.slice(0, char_len(_s_0));
    return $Char_is_space(_c_0);
  }
}

function $declared_in(_after_0) {
  const _rest_0 = $$String_trim_start(_after_0);
  const _name_0 = $$name_of(_rest_0);
  return $Bool_pick($$Bool_and($$starts_space(_after_0), $$Bool_and($$starts_name(_rest_0), $$String_starts_with($$String_trim_start($$String_drop(_rest_0, [...str_out(_name_0)].length)), ":"))), {$: "Some", "value": _name_0}, {$: "None"});
}

function $law_on(_line_0) {
  return $Bool_pick($$String_starts_with(_line_0, "law"), $$declared_in($$String_drop(_line_0, 3)), {$: "None"});
}

function $found_put(_found_0, _acc_0) {
  if (_found_0.$ === "None") {
    return _acc_0;
  } else {
    const _name_0 = _found_0["value"];
    return {$: "Con", "head": _name_0, "tail": _acc_0};
  }
}

function $laws_go($0, $1) {
  for (;;) {
    {
      const _lines_0 = $0;
      const _acc_0 = $1;
      if (_lines_0.$ === "Nil") {
        return $List_reverse(_acc_0);
      } else {
        const _h_0 = _lines_0["head"];
        const _t_0 = _lines_0["tail"];
        $0 = _t_0;
        $1 = $$found_put($$law_on(_h_0), _acc_0);
        continue;
      }
    }
  }
}

function $laws_in(_text_0) {
  return $laws_go($$______bend_core_lines(_text_0), {$: "Nil"});
}

function $slashed_put(_back_0, _c_0, _acc_0) {
  if (_back_0) {
    return ("/" + _acc_0);
  } else {
    return (_c_0 + _acc_0);
  }
}

function $slashed_go($0, $1) {
  for (;;) {
    {
      const _s_0 = $0;
      const _acc_0 = $1;
      if (_s_0 === "") {
        return $String_reverse(_acc_0);
      } else {
        const _c_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = $$slashed_put($$Char_is_eq(_c_0, "\\"), _c_0, _acc_0);
        continue;
      }
    }
  }
}

function $slashed(_path_0) {
  return $slashed_go(_path_0, "");
}

function $entry_pick(_outside_0, _folder_0, _clean_0) {
  if (_outside_0) {
    return {$: "None"};
  } else {
    if (_folder_0) {
      return {$: "Some", "value": (_clean_0 + "/")};
    } else {
      return {$: "Some", "value": _clean_0};
    }
  }
}

function $entry_of(_rel_0, _absolute_0, _folder_0) {
  const _x_0 = $$String_starts_with(_rel_0, "..");
  const _x_1 = $$String_is_empty(_rel_0);
  const _x_2 = (_x_0 || _absolute_0);
  return $entry_pick((_x_1 || _x_2), _folder_0, $$slashed(_rel_0));
}

function $why(_reason_0, _depth_0) {
  if (_reason_0.$ === "TooDeep") {
    return $String_concat({$: "Con", "head": "this task has already been cut ", "tail": {$: "Con", "head": $$Nat_show(_depth_0), "tail": {$: "Con", "head": " times on the way here; do this part yourself", "tail": {$: "Nil"}}}});
  } else if (_reason_0.$ === "NoParts") {
    return "no part was given";
  } else if (_reason_0.$ === "SameName") {
    return "two parts have the same name";
  } else if (_reason_0.$ === "SharedLaw") {
    return "a law was given to two parts; every law has one prover";
  } else if (_reason_0.$ === "Outside") {
    return "a part was given a file that is not yours to hand out";
  } else {
    return "two parts were given a file in common, or one a folder that holds another's file";
  }
}

function $refused(_why_0) {
  return $String_concat({$: "Con", "head": "Not divided: ", "tail": {$: "Con", "head": _why_0, "tail": {$: "Con", "head": ". Nothing was started. Cut it differently, or do the task yourself.", "tail": {$: "Nil"}}}});
}

function $ticked(_names_0) {
  if (_names_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _names_0["head"];
    const _t_0 = _names_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "`law ", "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": "`", "tail": {$: "Nil"}}}}), "tail": $$ticked(_t_0)};
  }
}

function $laws_missing(_names_0) {
  return $String_concat({$: "Con", "head": "no .bend file here declares ", "tail": {$: "Con", "head": $$String_join($$ticked(_names_0), ", "), "tail": {$: "Con", "head": "; write the laws at the cut first", "tail": {$: "Nil"}}}});
}

function $missing(_named_0, _declared_0) {
  return $______bend_core_without(_named_0, _declared_0);
}

function $clip(_text_0, _max_0) {
  const _x_0 = [...str_out(_text_0)].length;
  return $Bool_pick($$______bend_core_fits(_text_0, _max_0), _text_0, $$String_concat({$: "Con", "head": $$String_take(_text_0, _max_0), "tail": {$: "Con", "head": "\n... (", "tail": {$: "Con", "head": $$Nat_show((_x_0 < _max_0 ? 0 : _x_0 - _max_0)), "tail": {$: "Con", "head": " more characters)", "tail": {$: "Nil"}}}}}));
}

function $minutes(_ms_0) {
  const _x_0 = (3000 );
  const _tenths_0 = $$Nat_div(nat_chk(_ms_0 + _x_0), (6000 ));
  return $String_concat({$: "Con", "head": $$Nat_show($$Nat_div(_tenths_0, 10)), "tail": {$: "Con", "head": ".", "tail": {$: "Con", "head": $$Nat_show($$Nat_mod(_tenths_0, 10)), "tail": {$: "Con", "head": " min", "tail": {$: "Nil"}}}}});
}

function $state_pick(_stopped_0, _ok_0, _why_0, _code_0) {
  if (_stopped_0) {
    return _why_0;
  } else {
    if (_ok_0) {
      return "done";
    } else {
      const _x_0 = $$Nat_show(_code_0);
      return ("ended with status " + _x_0);
    }
  }
}

function $state(_ended_0) {
  const _code_0 = _ended_0["code"];
  const _stopped_0 = _ended_0["stopped"];
  return $state_pick($$Bool_not($$String_is_empty(_stopped_0)), $$Nat_is_eq(_code_0, 0), _stopped_0, _code_0);
}

function $how_pick(_stopped_0, _ok_0, _why_0, _code_0, _took_0) {
  if (_stopped_0) {
    return $String_concat({$: "Con", "head": _why_0, "tail": {$: "Con", "head": " after ", "tail": {$: "Con", "head": _took_0, "tail": {$: "Nil"}}}});
  } else {
    if (_ok_0) {
      return ("done in " + _took_0);
    } else {
      return $String_concat({$: "Con", "head": "ended with status ", "tail": {$: "Con", "head": $$Nat_show(_code_0), "tail": {$: "Con", "head": " after ", "tail": {$: "Con", "head": _took_0, "tail": {$: "Nil"}}}}});
    }
  }
}

function $how(_ended_0, _ms_0) {
  const _code_0 = _ended_0["code"];
  const _stopped_0 = _ended_0["stopped"];
  return $how_pick($$Bool_not($$String_is_empty(_stopped_0)), $$Nat_is_eq(_code_0, 0), _stopped_0, _code_0, $$minutes(_ms_0));
}

function $first_said(_out_0, _err_0) {
  return $Bool_pick($$String_is_empty(_out_0), $$Bool_pick($$String_is_empty(_err_0), "(it said nothing)", _err_0), _out_0);
}

function $or_none(_text_0) {
  return $Bool_pick($$String_is_empty(_text_0), "(none)", _text_0);
}

function $half_report(_name_0, _owns_0, _laws_0, _ended_0, _ms_0, _out_0, _err_0) {
  return $String_concat({$: "Con", "head": "## ", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": $$how(_ended_0, _ms_0), "tail": {$: "Con", "head": "\nOwned: ", "tail": {$: "Con", "head": $$or_none($$String_join(_owns_0, ", ")), "tail": {$: "Con", "head": "\nLaws: ", "tail": {$: "Con", "head": $$or_none($$String_join(_laws_0, ", ")), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": $$clip($$first_said(_out_0, _err_0), (6000 )), "tail": {$: "Nil"}}}}}}}}}}});
}

function $fits(_ended_0, _said_0) {
  const _code_0 = _ended_0["code"];
  const _stopped_0 = _ended_0["stopped"];
  return $Bool_and($$Nat_is_eq(_code_0, 0), $$Bool_and($$String_is_empty(_stopped_0), $$Bool_not(string_contains(_said_0, "SOME PROOFS FAIL"))));
}

function $check_said(_fit_0, _stopped_0) {
  if (_fit_0) {
    return "It passes: the parts fit.";
  } else {
    return $String_concat({$: "Con", "head": "It FAILS", "tail": {$: "Con", "head": $$Bool_pick($$String_is_empty(_stopped_0), "", $$String_concat({$: "Con", "head": " (", "tail": {$: "Con", "head": _stopped_0, "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}})), "tail": {$: "Con", "head": ": the parts do not fit yet. Repair it yourself if it is small; if a law was wrong, change it and cut again.", "tail": {$: "Nil"}}}});
  }
}

function $check_lines(_none_0, _check_0, _fit_0, _stopped_0, _said_0) {
  if (_none_0) {
    return {$: "Con", "head": "## No check was given", "tail": {$: "Con", "head": "Whether the parts fit is yours to see: read what each said, and what is in the files.", "tail": {$: "Nil"}}};
  } else {
    return {$: "Con", "head": ("## The check: " + _check_0), "tail": {$: "Con", "head": $$check_said(_fit_0, _stopped_0), "tail": {$: "Con", "head": $$clip($$Bool_pick($$String_is_empty(_said_0), "(no output)", _said_0), (4000 )), "tail": {$: "Nil"}}}};
  }
}

function $joined(_ms_0, _reports_0, _check_0, _fit_0, _stopped_0, _said_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": $$String_concat({$: "Con", "head": "Every part is back after ", "tail": {$: "Con", "head": $$minutes(_ms_0), "tail": {$: "Con", "head": ". Every file is yours again.", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Con", "head": _reports_0, "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$check_lines($$String_is_empty(_check_0), _check_0, _fit_0, _stopped_0, _said_0), "tail": {$: "Nil"}}}}}), "\n");
}

function $stopped_early() {
  return "Stopped: the parts were ended before they finished. What they wrote so far is in their files.";
}

function $not_yours(_path_0, _name_0, _owns_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _path_0, "tail": {$: "Con", "head": "\" is not yours to write: your part (\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\") owns ", "tail": {$: "Con", "head": $$or_none($$String_join(_owns_0, ", ")), "tail": {$: "Con", "head": ". If the task cannot be done without it, stop and say so in your reply.", "tail": {$: "Nil"}}}}}}}});
}

function $option(_flag_0, _value_0) {
  return $Bool_pick($$String_is_empty(_value_0), {$: "Nil"}, {$: "Con", "head": _flag_0, "tail": {$: "Con", "head": _value_0, "tail": {$: "Nil"}}});
}

function $half_args(_model_0, _session_model_0, _thinking_0, _session_thinking_0) {
  return $List_append($$option("--model", $$runs_on(_model_0, _session_model_0)), $$option("--thinking", $$runs_on(_thinking_0, _session_thinking_0)));
}

function $showing_line(_what_0, _choice_0, _session_0) {
  const _on_0 = $$runs_on(_choice_0, _session_0);
  return $String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": _what_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": $$Bool_pick($$String_is_empty(_on_0), "Pi's default", _on_0), "tail": {$: "Con", "head": $$Bool_pick($$String_is_empty(_choice_0), " (the same as this session)", " (chosen)"), "tail": {$: "Nil"}}}}}});
}

function $showing(_model_0, _session_model_0, _thinking_0, _session_thinking_0) {
  return $String_join({$: "Con", "head": "The agents you deploy run on", "tail": {$: "Con", "head": $$showing_line("model", _model_0, _session_model_0), "tail": {$: "Con", "head": $$showing_line("thinking", _thinking_0, _session_thinking_0), "tail": {$: "Con", "head": "/default-agent makes this session's model and thinking level theirs; /default-agent same follows each session again.", "tail": {$: "Nil"}}}}}, "\n");
}

function $agent_pick(_empty_0, _same_0) {
  if (_empty_0) {
    return {$: "Current"};
  } else {
    if (_same_0) {
      return {$: "Follow"};
    } else {
      return {$: "Named"};
    }
  }
}

function $agent_wants(_word_0) {
  return $agent_pick($$String_is_empty(_word_0), $$String_eq(_word_0, "same"));
}

function $cuts(_depth_0) {
  return $String_concat({$: "Con", "head": $$Nat_show(_depth_0), "tail": {$: "Con", "head": " cut", "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_depth_0, 1), "", "s"), "tail": {$: "Nil"}}}});
}

function $standing(_place_0) {
  if (_place_0.$ === "Whole") {
    return {$: "Con", "head": "You have the whole task: every file is yours to hand out.", "tail": {$: "Nil"}};
  } else {
    const _depth_0 = _place_0["depth"];
    const _name_0 = _place_0["name"];
    const _owns_0 = _place_0["owns"];
    const _laws_0 = _place_0["laws"];
    const _check_0 = _place_0["check"];
    const _x_0 = $$or_none($$String_join(_owns_0, ", "));
    const _x_1 = $$or_none($$String_join(_laws_0, ", "));
    const _x_2 = $$or_none(_check_0);
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "You are a part of a divided task, ", "tail": {$: "Con", "head": $$cuts(_depth_0), "tail": {$: "Con", "head": " down: \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\".", "tail": {$: "Nil"}}}}}}), "tail": {$: "Con", "head": ("Files you own: " + _x_0), "tail": {$: "Con", "head": ("Laws you must prove: " + _x_1), "tail": {$: "Con", "head": ("The check: " + _x_2), "tail": {$: "Nil"}}}}};
  }
}

function $method(_place_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "DIVISION: a task cut into parts, each done by its own agent at the same time.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Con", "head": $$standing(_place_0), "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": "When it helps", "tail": {$: "Con", "head": "- When the parts can go on at the same time without waiting for each other, and what one needs", "tail": {$: "Con", "head": "  of another can be said plainly beforehand. Cut where little crosses.", "tail": {$: "Con", "head": "- An agent starts from nothing and costs a start, so a part should be worth one. How many parts", "tail": {$: "Con", "head": "  and how large is yours to judge: two, five, one for the part you would rather not hold in", "tail": {$: "Con", "head": "  your own context. Work you can simply do is done faster by doing it.", "tail": {$: "Con", "head": "- A part that owns no file only reads and reports: finding something out can be a part too.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "How to cut", "tail": {$: "Con", "head": "1. Give each part a name, a task said in full, and the files that are its own. Create the files", "tail": {$: "Con", "head": "   or folders first if that makes the cut clearer. No file may be in two parts.", "tail": {$: "Con", "head": "2. Say what crosses between parts. The strongest way is Bend laws in a file you keep (call", "tail": {$: "Con", "head": "   `bend` for the language): a `law` with only a type is a signature one part provides, a `law`", "tail": {$: "Con", "head": "   with an equation is what the others may count on, and each law is given to the one part", "tail": {$: "Con", "head": "   that proves it, in a file of its own (`import ./LAWS.bend as L`, `def L.name(..): ...`).", "tail": {$: "Con", "head": "   Where laws do not fit the work (prose, configuration, another language), say it in the tasks", "tail": {$: "Con", "head": "   and give a check that tells whether the parts fit: a test run, a build, a script.", "tail": {$: "Con", "head": "3. Call `division_split` with the parts. They all run now, in this directory, and you get each", "tail": {$: "Con", "head": "   one's report and the result of the check when all are back.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "What holds while the parts work (proven in division's LAWS.bend)", "tail": {$: "Con", "head": "- A part may write only the files it was handed, and no file is handed to two.", "tail": {$: "Con", "head": "- A part may count on every law at the cut, proven or not: another part is proving it now.", "tail": {$: "Con", "head": "  Until it has, the checker reports that def as missing; that is expected.", "tail": {$: "Con", "head": "- A part does not change a law. If one cannot be proven as written, it stops and says why, and", "tail": {$: "Con", "head": "  the agent that cut decides: that is you, for your own cut.", "tail": {$: "Con", "head": "- A part may cut again among its own files, and so may its parts.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "When the parts are back", "tail": {$: "Con", "head": "- Every file is yours again. If the check fails, read what each part said: repair it yourself", "tail": {$: "Con", "head": "  when it is small, change what crosses and cut again when that was wrong.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $whole_lines(_whole_0) {
  return $Bool_pick($$String_is_empty(_whole_0), {$: "Nil"}, {$: "Con", "head": "The whole task, so you know what yours is part of:", "tail": {$: "Con", "head": _whole_0, "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}});
}

function $other_lines(_others_0) {
  if (_others_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _others_0["head"];
    const _name_0 = _t_0["name"];
    const _task_0 = _t_0["task"];
    const _laws_0 = _t_0["laws"];
    const _t_1 = _others_0["tail"];
    const _x_0 = $$String_join(_laws_0, ", ");
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "- \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\": ", "tail": {$: "Con", "head": _task_0, "tail": {$: "Con", "head": $$Bool_pick($$List_is_empty(_laws_0), "", (" It proves: " + _x_0)), "tail": {$: "Nil"}}}}}}), "tail": $$other_lines(_t_1)};
  }
}

function $others_part(_others_0) {
  if (_others_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _others_0["head"];
    const _t_0 = _others_0["tail"];
    return $List_concat({$: "Con", "head": {$: "Con", "head": "The other parts, which are not yours to do and are being done right now in this same directory:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$other_lines({$: "Con", "head": _h_0, "tail": _t_0}), "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Nil"}}, "tail": {$: "Nil"}}}});
  }
}

function $owns_part(_owns_0) {
  if (_owns_0.$ === "Nil") {
    return {$: "Con", "head": "You own no file: read whatever you need, write nothing, and put what you find in your reply.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}};
  } else {
    const _h_0 = _owns_0["head"];
    const _t_0 = _owns_0["tail"];
    const _x_0 = $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", ");
    return {$: "Con", "head": ("Files you own: " + _x_0), "tail": {$: "Con", "head": "You may create and change only these (a name ending in \"/\" is a folder and everything in it). You may read anything. A write anywhere else is refused.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}};
  }
}

function $laws_part(_laws_0) {
  if (_laws_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _laws_0["head"];
    const _t_0 = _laws_0["tail"];
    const _x_0 = $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", ");
    return {$: "Con", "head": ("Laws you must prove: " + _x_0), "tail": {$: "Con", "head": "They are declared in the .bend files here. Prove each with a def of the same name in a file you own (call the `bend` action first if you have not used Bend).", "tail": {$: "Con", "head": "Laws another part is proving are named above: count on them as if they were proven, and on any signature among them as if it were written. Until that part is done the checker reports those defs as missing, which is expected and not yours to fix.", "tail": {$: "Con", "head": "Do not change a law. If one of yours cannot be proven as written, or you need something nothing gives you, stop and say exactly what and why.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}};
  }
}

function $check_part(_check_0) {
  return $Bool_pick($$String_is_empty(_check_0), {$: "Nil"}, {$: "Con", "head": ("Check your work with: " + _check_0), "tail": {$: "Nil"}});
}

function $brief(_name_0, _task_0, _owns_0, _laws_0, _others_0, _whole_0, _check_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "You are one part of a larger task that was cut into parts, each done by its own agent.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Your part: " + _name_0), "tail": {$: "Con", "head": _task_0, "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}, "tail": {$: "Con", "head": $$whole_lines(_whole_0), "tail": {$: "Con", "head": $$others_part(_others_0), "tail": {$: "Con", "head": $$owns_part(_owns_0), "tail": {$: "Con", "head": $$laws_part(_laws_0), "tail": {$: "Con", "head": $$check_part(_check_0), "tail": {$: "Con", "head": {$: "Con", "head": "If your part turns out to hold work that would go faster as parts of its own, you may cut again among your files (call `division` for how). That is yours to judge.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "When you are done, reply with what you did, what is proven or checked, and anything the agent that cut the task needs to know. That reply is all it will see of your work besides the files.", "tail": {$: "Nil"}}}}, "tail": {$: "Nil"}}}}}}}}), "\n");
}

function $describe_division() {
  return $String_concat({$: "Con", "head": "A way to deploy agents on a task: cut it into parts that separate agents do at the same time. ", "tail": {$: "Con", "head": "Each part owns its own files, so no two agents write the same one, and what crosses between parts is said beforehand, ", "tail": {$: "Con", "head": "best as Bend laws that each part proves and the others count on. ", "tail": {$: "Con", "head": "Returns the method and where you stand in the tree. How many parts, how large, and whether to cut at all are yours to judge.", "tail": {$: "Nil"}}}}});
}

function $describe_split() {
  return $String_concat({$: "Con", "head": "Cut the task you have into parts and run them all now, each as its own agent in this directory. Call `division` first for the method. ", "tail": {$: "Con", "head": "Returns when every part is back, with what each said and the result of the check. ", "tail": {$: "Con", "head": "Refused, with the reason, only when two parts would own the same file, a part is handed a file that is not yours, a law is given to two parts, or two parts share a name.", "tail": {$: "Nil"}}}});
}

function $String_eq(_a_0, _b_0) {
  return $Cmp_is_eq($$String_order(_a_0, _b_0));
}

function $Bool_not(_b_0) {
  if (!_b_0) {
    return true;
  } else {
    return false;
  }
}

function $Bool_pick(_c_0, _a_0, _b_0) {
  if (!_c_0) {
    return _b_0;
  } else {
    return _a_0;
  }
}

function $List_append(_xs_0, _ys_0) {
  if (_xs_0.$ === "Nil") {
    return _ys_0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return {$: "Con", "head": _h_0, "tail": $$List_append(_t_0, _ys_0)};
  }
}

function $Bool_and(_a_0, _b_0) {
  if (!_a_0) {
    return false;
  } else {
    return _b_0;
  }
}

function $String_ends_with(_s_0, _p_0) {
  return $String_starts_with($$String_reverse(_s_0), $$String_reverse(_p_0));
}

function $Char_is_eq(_a_0, _b_0) {
  const _x_0 = char_code(_a_0);
  const _y_0 = char_code(_b_0);
  return (_x_0 === _y_0);
}

function $String_is_empty(_s_0) {
  if (_s_0 === "") {
    return true;
  } else {
    return false;
  }
}

function $String_reverse(_s_0) {
  return $String_reverse_go(_s_0, "");
}

function $List_concat(_xss_0) {
  if (_xss_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xss_0["head"];
    const _t_0 = _xss_0["tail"];
    return $List_append(_h_0, $$List_concat(_t_0));
  }
}

function $List_reverse(_xs_0) {
  return $List_reverse_go(_xs_0, {$: "Nil"});
}

function $String_get($0, $1) {
  for (;;) {
    {
      const _s_0 = $0;
      const _n_0 = $1;
      if (_s_0 === "") {
        return {$: "None"};
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        if (_n_0 == 0) {
          return {$: "Some", "value": _h_0};
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $Nat_mod(_a_0, _b_0) {
  return $Pair_snd(nat_divmod(_a_0, _b_0));
}

function $Char_is_space(_c_0) {
  const _x_0 = char_code(_c_0);
  const _x_1 = (_x_0 === 32);
  const _x_2 = $$Bool_and((_x_0 >= 9), (_x_0 <= 13));
  return (_x_1 || _x_2);
}

function $String_starts_with(_s_0, _p_0) {
  return $String_starts_with_go(_p_0, _s_0);
}

function $String_take(_s_0, _n_0) {
  if (_s_0 === "") {
    return "";
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    if (_n_0 == 0) {
      return "";
    } else {
      const _p_0 = (_n_0 - 1);
      return (_h_0 + $$String_take(_t_0, _p_0));
    }
  }
}

function $String_trim_end(_s_0) {
  return $String_reverse($$String_trim_start($$String_reverse(_s_0)));
}

function $String_trim_start($0, $1, $2) {
  let $pc = 0;
  for (;;) switch ($pc) {
    case 0: {
      const _s_0 = $0;
      if (_s_0 === "") {
        return "";
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = _h_0;
        $2 = $$Char_is_space(_h_0);
        $pc = 1; continue;
      }
    }
    case 1: {
      const _t_0 = $0;
      const _h_0 = $1;
      const _space_0 = $2;
      if (!_space_0) {
        return (_h_0 + _t_0);
      } else {
        $0 = _t_0;
        $pc = 0; continue;
      }
    }
  }
}

function $String_drop($0, $1) {
  for (;;) {
    {
      const _s_0 = $0;
      const _n_0 = $1;
      if (_s_0 === "") {
        return "";
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        if (_n_0 == 0) {
          return (_h_0 + _t_0);
        } else {
          const _p_0 = (_n_0 - 1);
          $0 = _t_0;
          $1 = _p_0;
          continue;
        }
      }
    }
  }
}

function $String_lines(_s_0) {
  return $String_split(_s_0, "\n");
}

function $String_join(_xs_0, _sep_0) {
  if (_xs_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $String_join_go(_t_0, _h_0, _sep_0);
  }
}

function $String_concat(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$String_concat(_t_0);
    return (_h_0 + _x_0);
  }
}

function $String_trim(_s_0) {
  return $String_trim_end($$String_trim_start(_s_0));
}

function $Maybe_default(_m_0, _d_0) {
  if (_m_0.$ === "None") {
    return _d_0;
  } else {
    const _x_0 = _m_0["value"];
    return _x_0;
  }
}

function $Nat_is_eq(_a_0, _b_0) {
  return $Cmp_is_eq(cmp_new(_a_0, _b_0));
}

function $Nat_is_gt(_a_0, _b_0) {
  return $Cmp_is_gt(cmp_new(_a_0, _b_0));
}

function $Nat_is_le(_a_0, _b_0) {
  return $Cmp_is_le(cmp_new(_a_0, _b_0));
}

function $Nat_is_ge(_a_0, _b_0) {
  return $Cmp_is_ge(cmp_new(_a_0, _b_0));
}

function $List_length(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _t_0 = _xs_0["tail"];
    return nat_chk($$List_length(_t_0) + 1);
  }
}

function $String_repeat(_s_0, _n_0) {
  if (_n_0 == 0) {
    return "";
  } else {
    const _p_0 = (_n_0 - 1);
    const _x_0 = $$String_repeat(_s_0, _p_0);
    return (_s_0 + _x_0);
  }
}

function $List_is_empty(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return true;
  } else {
    return false;
  }
}

function $Nat_show(_n_0) {
  const _m_0 = _n_0;
  return $Nat_show_fin(_m_0, "", $$Nat_show_put(nat_divmod(_m_0, 10)));
}

function $Nat_div(_a_0, _b_0) {
  return $Pair_fst(nat_divmod(_a_0, _b_0));
}

function $Char_is_alpha(_c_0) {
  const _x_0 = $$Char_is_upper(_c_0);
  const _x_1 = $$Char_is_lower(_c_0);
  return (_x_0 || _x_1);
}

function $Char_is_digit(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 48), (_x_0 <= 57));
}

function $Cmp_is_eq(_c_0) {
  if (_c_0.$ === "EQ") {
    return true;
  } else {
    return false;
  }
}

function $String_order(_a_0, _b_0) {
  return $String_order_go(_a_0, _b_0, {$: "EQ"});
}

function $String_reverse_go($0, $1) {
  for (;;) {
    {
      const _s_0 = $0;
      const _acc_0 = $1;
      if (_s_0 === "") {
        return _acc_0;
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = (_h_0 + _acc_0);
        continue;
      }
    }
  }
}

function $List_reverse_go($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _acc_0 = $1;
      if (_xs_0.$ === "Nil") {
        return _acc_0;
      } else {
        const _h_0 = _xs_0["head"];
        const _t_0 = _xs_0["tail"];
        $0 = _t_0;
        $1 = {$: "Con", "head": _h_0, "tail": _acc_0};
        continue;
      }
    }
  }
}

function $Pair_snd(_p_0) {
  const _b_0 = _p_0["snd"];
  return _b_0;
}

function $String_starts_with_go($0, $1, $2) {
  let $pc = 0;
  for (;;) switch ($pc) {
    case 0: {
      const _p_0 = $0;
      const _s_0 = $1;
      if (_p_0 === "") {
        return true;
      } else {
        const _y_0 = _p_0.slice(0, char_len(_p_0));
        const _yt_0 = _p_0.slice(char_len(_p_0));
        if (_s_0 === "") {
          return false;
        } else {
          const _x_0 = _s_0.slice(0, char_len(_s_0));
          const _xt_0 = _s_0.slice(char_len(_s_0));
          $0 = _yt_0;
          $1 = _xt_0;
          $2 = $$Char_is_eq(_x_0, _y_0);
          $pc = 1; continue;
        }
      }
    }
    case 1: {
      const _pt_0 = $0;
      const _t_0 = $1;
      const _same_0 = $2;
      if (!_same_0) {
        return false;
      } else {
        $0 = _pt_0;
        $1 = _t_0;
        $pc = 0; continue;
      }
    }
  }
}

function $String_trim_start_if($0, $1, $2) {
  let $pc = 1;
  for (;;) switch ($pc) {
    case 0: {
      const _s_0 = $0;
      if (_s_0 === "") {
        return "";
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = _h_0;
        $2 = $$Char_is_space(_h_0);
        $pc = 1; continue;
      }
    }
    case 1: {
      const _t_0 = $0;
      const _h_0 = $1;
      const _space_0 = $2;
      if (!_space_0) {
        return (_h_0 + _t_0);
      } else {
        $0 = _t_0;
        $pc = 0; continue;
      }
    }
  }
}

function $String_split(_s_0, _sep_0) {
  if (_s_0 === "") {
    return {$: "Con", "head": "", "tail": {$: "Nil"}};
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    return $String_split_fin(_h_0, $$String_split(_t_0, _sep_0), $$Char_is_eq(_h_0, _sep_0));
  }
}

function $String_join_go(_xs_0, _h_0, _sep_0) {
  if (_xs_0.$ === "Nil") {
    return _h_0;
  } else {
    const _h2_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$String_join_go(_t_0, _h2_0, _sep_0);
    const _x_1 = (_sep_0 + _x_0);
    return (_h_0 + _x_1);
  }
}

function $Cmp_is_gt(_c_0) {
  if (_c_0.$ === "GT") {
    return true;
  } else {
    return false;
  }
}

function $Cmp_is_le(_c_0) {
  if (_c_0.$ === "GT") {
    return false;
  } else {
    return true;
  }
}

function $Cmp_is_ge(_c_0) {
  if (_c_0.$ === "LT") {
    return false;
  } else {
    return true;
  }
}

function $Nat_show_fin($0, $1, $2) {
  let $pc = 0;
  for (;;) switch ($pc) {
    case 0: {
      const _g_0 = $0;
      const _acc_0 = $1;
      const _dq_0 = $2;
      const _d_0 = _dq_0["fst"];
      const _t_0 = _dq_0["snd"];
      if (_t_0 == 0) {
        return (_d_0 + _acc_0);
      } else {
        $0 = _g_0;
        $1 = _t_0;
        $2 = (_d_0 + _acc_0);
        $pc = 1; continue;
      }
    }
    case 1: {
      const _f_0 = $0;
      const _n_0 = $1;
      const _acc_0 = $2;
      if (_f_0 == 0) {
        return _acc_0;
      } else {
        const _g_0 = (_f_0 - 1);
        $0 = _g_0;
        $1 = _acc_0;
        $2 = $$Nat_show_put(nat_divmod(_n_0, 10));
        $pc = 0; continue;
      }
    }
  }
}

function $Nat_show_put(_qr_0) {
  const _q_0 = _qr_0["fst"];
  const _r_0 = _qr_0["snd"];
  const _x_0 = nat_chk(48 + _r_0);
  return {$: "Tuple", "fst": char_new((_x_0 >>>0)), "snd": _q_0};
}

function $Pair_fst(_p_0) {
  const _a_0 = _p_0["fst"];
  return _a_0;
}

function $Char_is_upper(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 65), (_x_0 <= 90));
}

function $Char_is_lower(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 97), (_x_0 <= 122));
}

function $String_contains_if($0, $1, $2) {
  let $pc = 0;
  for (;;) switch ($pc) {
    case 0: {
      const _t_0 = $0;
      const _p_0 = $1;
      const _here_0 = $2;
      if (!_here_0) {
        $0 = _t_0;
        $1 = _p_0;
        $pc = 1; continue;
      } else {
        return true;
      }
    }
    case 1: {
      const _s_0 = $0;
      const _p_0 = $1;
      if (_s_0 === "") {
        return $String_is_empty(_p_0);
      } else {
        const _h_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = _p_0;
        $2 = $$String_starts_with((_h_0 + _t_0), _p_0);
        $pc = 0; continue;
      }
    }
  }
}

function $String_order_go($0, $1, $2) {
  for (;;) {
    {
      const _a_0 = $0;
      const _b_0 = $1;
      const _c_0 = $2;
      if (_a_0 === "") {
        if (_b_0 !== "") {
          if (_c_0.$ === "EQ") {
            return {$: "LT"};
          } else {
            return _c_0;
          }
        } else {
          return _c_0;
        }
      } else {
        const _t_1 = _a_0.slice(0, char_len(_a_0));
        const _x_0 = char_code(_t_1);
        const _t_2 = _a_0.slice(char_len(_a_0));
        if (_b_0 === "") {
          if (_c_0.$ === "EQ") {
            return {$: "GT"};
          } else {
            return _c_0;
          }
        } else {
          const _t_3 = _b_0.slice(0, char_len(_b_0));
          const _y_0 = char_code(_t_3);
          const _t2_0 = _b_0.slice(char_len(_b_0));
          if (_c_0.$ === "EQ") {
            $0 = _t_2;
            $1 = _t2_0;
            $2 = cmp_new(_x_0, _y_0);
            continue;
          } else {
            return _c_0;
          }
        }
      }
    }
  }
}

function $String_starts_with_go_if($0, $1, $2) {
  let $pc = 1;
  for (;;) switch ($pc) {
    case 0: {
      const _p_0 = $0;
      const _s_0 = $1;
      if (_p_0 === "") {
        return true;
      } else {
        const _y_0 = _p_0.slice(0, char_len(_p_0));
        const _yt_0 = _p_0.slice(char_len(_p_0));
        if (_s_0 === "") {
          return false;
        } else {
          const _x_0 = _s_0.slice(0, char_len(_s_0));
          const _xt_0 = _s_0.slice(char_len(_s_0));
          $0 = _yt_0;
          $1 = _xt_0;
          $2 = $$Char_is_eq(_x_0, _y_0);
          $pc = 1; continue;
        }
      }
    }
    case 1: {
      const _pt_0 = $0;
      const _t_0 = $1;
      const _same_0 = $2;
      if (!_same_0) {
        return false;
      } else {
        $0 = _pt_0;
        $1 = _t_0;
        $pc = 0; continue;
      }
    }
  }
}

function $String_split_fin(_c_0, _r_0, _cut_0) {
  if (!_cut_0) {
    return $String_split_push(_c_0, _r_0);
  } else {
    return {$: "Con", "head": "", "tail": _r_0};
  }
}

function $Nat_show_go($0, $1, $2) {
  let $pc = 1;
  for (;;) switch ($pc) {
    case 0: {
      const _g_0 = $0;
      const _acc_0 = $1;
      const _dq_0 = $2;
      const _d_0 = _dq_0["fst"];
      const _t_0 = _dq_0["snd"];
      if (_t_0 == 0) {
        return (_d_0 + _acc_0);
      } else {
        $0 = _g_0;
        $1 = _t_0;
        $2 = (_d_0 + _acc_0);
        $pc = 1; continue;
      }
    }
    case 1: {
      const _f_0 = $0;
      const _n_0 = $1;
      const _acc_0 = $2;
      if (_f_0 == 0) {
        return _acc_0;
      } else {
        const _g_0 = (_f_0 - 1);
        $0 = _g_0;
        $1 = _acc_0;
        $2 = $$Nat_show_put(nat_divmod(_n_0, 10));
        $pc = 0; continue;
      }
    }
  }
}

function $String_split_push(_c_0, _ps_0) {
  if (_ps_0.$ === "Nil") {
    return {$: "Con", "head": (_c_0 + ""), "tail": {$: "Nil"}};
  } else {
    const _h_0 = _ps_0["head"];
    const _t_0 = _ps_0["tail"];
    return {$: "Con", "head": (_c_0 + _h_0), "tail": _t_0};
  }
}

const $$String_eq = $String_eq;
const $$______bend_core_has = $______bend_core_has;
const $$Bool_not = $Bool_not;
const $$______bend_core_without = $______bend_core_without;
const $$______bend_core_only = $______bend_core_only;
const $$______bend_core_overlaps = $______bend_core_overlaps;
const $$List_append = $List_append;
const $$______bend_core_add = $______bend_core_add;
const $$______bend_core_covers = $______bend_core_covers;
const $$______bend_core_names = $______bend_core_names;
const $$______bend_core_without_named = $______bend_core_without_named;
const $$______bend_core_shipped_kept = $______bend_core_shipped_kept;
const $$Bool_and = $Bool_and;
const $$______bend_core_core_plugins = $______bend_core_core_plugins;
const $$String_ends_with = $String_ends_with;
const $$______bend_core_ends_with_any = $______bend_core_ends_with_any;
const $$Char_is_eq = $Char_is_eq;
const $$______bend_core_hidden = $______bend_core_hidden;
const $$Bool_pick = $Bool_pick;
const $$String_is_empty = $String_is_empty;
const $$String_reverse = $String_reverse;
const $$______bend_core_stem_go = $______bend_core_stem_go;
const $$______bend_core_pick_name = $______bend_core_pick_name;
const $$______bend_core_extras = $______bend_core_extras;
const $$______bend_core_passes = $______bend_core_passes;
const $$______bend_core_complete = $______bend_core_complete;
const $$______bend_core_unless = $______bend_core_unless;
const $$______bend_core_pi_bare = $______bend_core_pi_bare;
const $$______bend_core_pi_apart = $______bend_core_pi_apart;
const $$______bend_core_theme_args = $______bend_core_theme_args;
const $$______bend_core_remove_one = $______bend_core_remove_one;
const $$______bend_core_resumes = $______bend_core_resumes;
const $$______bend_core_chooses = $______bend_core_chooses;
const $$______bend_core_strip = $______bend_core_strip;
const $$______bend_core_any_resumes = $______bend_core_any_resumes;
const $$______bend_core_any_chooses = $______bend_core_any_chooses;
const $$List_reverse = $List_reverse;
const $$______bend_core_unsaid = $______bend_core_unsaid;
const $$______bend_core_session_args = $______bend_core_session_args;
const $$______bend_core_put = $______bend_core_put;
const $$______bend_core_put_row = $______bend_core_put_row;
const $$String_get = $String_get;
const $$______bend_core_glyph = $______bend_core_glyph;
const $$______bend_core_sparks = $______bend_core_sparks;
const $$______bend_core_hat = $______bend_core_hat;
const $$Nat_mod = $Nat_mod;
const $$______bend_core_widths = $______bend_core_widths;
const $$Char_is_space = $Char_is_space;
const $$______bend_core_is_sep = $______bend_core_is_sep;
const $$______bend_core_squash_put = $______bend_core_squash_put;
const $$String_starts_with = $String_starts_with;
const $$______bend_core_words = $______bend_core_words;
const $$______bend_core_mine = $______bend_core_mine;
const $$String_take = $String_take;
const $$______bend_core_fits = $______bend_core_fits;
const $$______bend_core_clip_at = $______bend_core_clip_at;
const $$______bend_core_squash = $______bend_core_squash;
const $$______bend_core_clip = $______bend_core_clip;
const $$______bend_core_expand_put = $______bend_core_expand_put;
const $$______bend_core_line_cur = $______bend_core_line_cur;
const $$______bend_core_line_done = $______bend_core_line_done;
const $$______bend_core_first = $______bend_core_first;
const $$______bend_core_beyond = $______bend_core_beyond;
const $$______bend_core_expand = $______bend_core_expand;
const $$String_trim_end = $String_trim_end;
const $$______bend_core_lines = $______bend_core_lines;
const $$______bend_core_droppable = $______bend_core_droppable;
const $$String_trim_start = $String_trim_start;
const $$String_drop = $String_drop;
const $$______bend_core_after_rtk = $______bend_core_after_rtk;
const $$String_lines = $String_lines;
const $$______bend_core_last_said = $______bend_core_last_said;
const $$String_concat = $String_concat;
const $$______bend_core_listed = $______bend_core_listed;
const $$______bend_core_first_said = $______bend_core_first_said;
const $$String_join = $String_join;
const $$______bend_core_moved_list = $______bend_core_moved_list;
const $$______bend_core_listing_actions = $______bend_core_listing_actions;
const $$______bend_core_at_file = $______bend_core_at_file;
const $$______bend_core_at_files = $______bend_core_at_files;
const $$______bend_core_completions_go = $______bend_core_completions_go;
const $$String_trim = $String_trim;
const $$______bend_core_think_levels = $______bend_core_think_levels;
const $$Maybe_default = $Maybe_default;
const $$Nat_is_eq = $Nat_is_eq;
const $$______bend_core_in_dir = $______bend_core_in_dir;
const $$______bend_core_in_dirs = $______bend_core_in_dirs;
const $$Nat_is_gt = $Nat_is_gt;
const $$Nat_is_le = $Nat_is_le;
const $$______bend_core_pack_go = $______bend_core_pack_go;
const $$Nat_is_ge = $Nat_is_ge;
const $$______bend_core_pad_end = $______bend_core_pad_end;
const $$______bend_core_blanks = $______bend_core_blanks;
const $$______bend_core_beside_zip = $______bend_core_beside_zip;
const $$______bend_core_beside_row = $______bend_core_beside_row;
const $$______bend_core_margined = $______bend_core_margined;
const $$List_length = $List_length;
const $$String_repeat = $String_repeat;
const $$List_is_empty = $List_is_empty;
const $$______bend_core_blank_lines = $______bend_core_blank_lines;
const $$Nat_show = $Nat_show;
const $$______bend_core_label = $______bend_core_label;
const $$______bend_core_labels = $______bend_core_labels;
const $$______bend_core_widest = $______bend_core_widest;
const $$______bend_core_pad_right = $______bend_core_pad_right;
const $$______bend_core_wide_rows = $______bend_core_wide_rows;
const $$______bend_core_indented = $______bend_core_indented;
const $$______bend_core_shape = $______bend_core_shape;
const $$List_concat = $List_concat;
const $$______bend_core_own_pi = $______bend_core_own_pi;
const $$______bend_core_var_names = $______bend_core_var_names;
const $$______bend_core_pi_env = $______bend_core_pi_env;
const $$______bend_core_pi_env_cleared = $______bend_core_pi_env_cleared;
const $$______bend_core_brought_settings = $______bend_core_brought_settings;
const $$______bend_core_brought_list = $______bend_core_brought_list;
const $$______bend_core_with_slash = $______bend_core_with_slash;
const $$______bend_core_inside = $______bend_core_inside;
const $$______bend_core_takes = $______bend_core_takes;
const $$______bend_core_all_rooted = $______bend_core_all_rooted;
const $$______bend_core_parent_go = $______bend_core_parent_go;
const $$______bend_core_parent = $______bend_core_parent;
const $$______bend_core_parents = $______bend_core_parents;
const $$______bend_core_sessions_dir = $______bend_core_sessions_dir;
const $$______bend_core_origin_dirs = $______bend_core_origin_dirs;
const $$______bend_core_origins = $______bend_core_origins;
const $$______bend_core_minute = $______bend_core_minute;
const $$______bend_core_more_lines = $______bend_core_more_lines;
const $$______bend_core_result_view = $______bend_core_result_view;
const $$______bend_core_call_line = $______bend_core_call_line;
const $$______bend_core_result_block = $______bend_core_result_block;
const $$______bend_core_voice_of = $______bend_core_voice_of;
const $$______bend_core_counted = $______bend_core_counted;
const $$______bend_core_tally_lines = $______bend_core_tally_lines;
const $$______bend_core_bulleted = $______bend_core_bulleted;
const $$______bend_core_own_folders = $______bend_core_own_folders;
const $$______bend_core_is_option = $______bend_core_is_option;
const $$______bend_core_bare = $______bend_core_bare;
const $$______bend_core_options = $______bend_core_options;
const $$______bend_core_first_of = $______bend_core_first_of;
const $$______bend_core_value_after = $______bend_core_value_after;
const $$______bend_core_old_wanted = $______bend_core_old_wanted;
const $$______bend_core_wanted = $______bend_core_wanted;
const $$______bend_core_rooted = $______bend_core_rooted;
const $$______bend_core_sparing = $______bend_core_sparing;
const $$______bend_core_dangling = $______bend_core_dangling;
const $$______bend_core_is_unknown = $______bend_core_is_unknown;
const $$Nat_div = $Nat_div;
const $$______bend_core_size_text = $______bend_core_size_text;
const $$______bend_core_row_lines = $______bend_core_row_lines;
const $$______bend_core_link_lines = $______bend_core_link_lines;
const $$______bend_core_export_line = $______bend_core_export_line;
const $$______bend_core_setting = $______bend_core_setting;
const $$______bend_core_or_unset = $______bend_core_or_unset;
const $$is_folder = $is_folder;
const $$covers = $covers;
const $$may_write = $may_write;
const $$clash = $clash;
const $$clashes = $clashes;
const $$overlap = $overlap;
const $$may = $may;
const $$inside = $inside;
const $$names_of = $names_of;
const $$owns_of = $owns_of;
const $$laws_of = $laws_of;
const $$distinct = $distinct;
const $$shares = $shares;
const $$disjoint = $disjoint;
const $$all_inside = $all_inside;
const $$one_if = $one_if;
const $$writers = $writers;
const $$guard = $guard;
const $$Char_is_alpha = $Char_is_alpha;
const $$Char_is_digit = $Char_is_digit;
const $$is_name_char = $is_name_char;
const $$name_of = $name_of;
const $$starts_space = $starts_space;
const $$starts_name = $starts_name;
const $$declared_in = $declared_in;
const $$law_on = $law_on;
const $$found_put = $found_put;
const $$slashed_put = $slashed_put;
const $$slashed = $slashed;
const $$ticked = $ticked;
const $$minutes = $minutes;
const $$how = $how;
const $$or_none = $or_none;
const $$first_said = $first_said;
const $$clip = $clip;
const $$check_said = $check_said;
const $$check_lines = $check_lines;
const $$runs_on = $runs_on;
const $$option = $option;
const $$showing_line = $showing_line;
const $$cuts = $cuts;
const $$standing = $standing;
const $$other_lines = $other_lines;
const $$whole_lines = $whole_lines;
const $$others_part = $others_part;
const $$owns_part = $owns_part;
const $$laws_part = $laws_part;
const $$check_part = $check_part;
const $$String_order = $String_order;
const $$Nat_show_put = $Nat_show_put;
const $$Char_is_upper = $Char_is_upper;
const $$Char_is_lower = $Char_is_lower;
const $$String_split = $String_split;
const $$String_join_go = $String_join_go;export default {
  "../../bend/core:has": run_lib((a0,a1) => run_loop($______bend_core_has(a0,str_in(a1))), 2),
  "../../bend/core:keep_if": run_lib((a0,a1,a2) => run_loop($______bend_core_keep_if(a0,str_in(a1),a2)), 3),
  "../../bend/core:without": run_lib((a0,a1) => run_loop($______bend_core_without(a0,a1)), 2),
  "../../bend/core:only": run_lib((a0,a1) => run_loop($______bend_core_only(a0,a1)), 2),
  "../../bend/core:overlaps": run_lib((a0,a1) => run_loop($______bend_core_overlaps(a0,a1)), 2),
  "../../bend/core:add": run_lib((a0,a1) => run_loop($______bend_core_add(a0,str_in(a1))), 2),
  "../../bend/core:add_all": run_lib((a0,a1) => run_loop($______bend_core_add_all(a0,a1)), 2),
  "../../bend/core:covers": run_lib((a0,a1) => run_loop($______bend_core_covers(a0,a1)), 2),
  "../../bend/core:names": run_lib((a0) => run_loop($______bend_core_names(a0)), 1),
  "../../bend/core:keep_entry": run_lib((a0,a1,a2) => run_loop($______bend_core_keep_entry(a0,a1,a2)), 3),
  "../../bend/core:without_named": run_lib((a0,a1) => run_loop($______bend_core_without_named(a0,a1)), 2),
  "../../bend/core:shipped_kept": run_lib((a0,a1) => run_loop($______bend_core_shipped_kept(a0,a1)), 2),
  "../../bend/core:plan": run_lib((a0,a1,a2) => run_loop($______bend_core_plan(a0,a1,a2)), 3),
  "../../bend/core:builtins_at_boot": run_lib((a0,a1) => run_loop($______bend_core_builtins_at_boot(a0,a1)), 2),
  "../../bend/core:switched_off": run_lib((a0,a1) => run_loop($______bend_core_switched_off(a0,str_in(a1))), 2),
  "../../bend/core:switched_on": run_lib((a0,a1) => run_loop($______bend_core_switched_on(a0,str_in(a1))), 2),
  "../../bend/core:remembered": run_lib((a0,a1) => run_loop($______bend_core_remembered(a0,a1)), 2),
  "../../bend/core:core_plugins": run_lib(() => run_loop($______bend_core_core_plugins()), 0),
  "../../bend/core:is_core": run_lib((a0) => run_loop($______bend_core_is_core(str_in(a0))), 1),
  "../../bend/core:restore_unloads": run_lib((a0,a1) => run_loop($______bend_core_restore_unloads(a0,a1)), 2),
  "../../bend/core:ends_with_any": run_lib((a0,a1) => run_loop($______bend_core_ends_with_any(str_in(a0),a1)), 2),
  "../../bend/core:hidden_char": run_lib((a0) => run_loop($______bend_core_hidden_char(str_in(a0))), 1),
  "../../bend/core:hidden": run_lib((a0) => run_loop($______bend_core_hidden(str_in(a0))), 1),
  "../../bend/core:usable": run_lib((a0,a1,a2) => run_loop($______bend_core_usable(str_in(a0),a1,a2)), 3),
  "../../bend/core:stem_pick": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_stem_pick(a0,str_in(a1),str_in(a2)))), 3),
  "../../bend/core:stem_go": run_lib((a0,a1) => str_out(run_loop($______bend_core_stem_go(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:stem": run_lib((a0) => str_out(run_loop($______bend_core_stem(str_in(a0)))), 1),
  "../../bend/core:pick_name": run_lib((a0) => str_out(run_loop($______bend_core_pick_name(a0))), 1),
  "../../bend/core:command_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($______bend_core_command_pick(a0,a1,a2,a3,a4,a5,a6)), 7),
  "../../bend/core:command_of": run_lib((a0) => run_loop($______bend_core_command_of(str_in(a0))), 1),
  "../../bend/core:extras_pick": run_lib((a0,a1,a2,a3,a4) => run_loop($______bend_core_extras_pick(a0,a1,a2,str_in(a3),a4)), 5),
  "../../bend/core:extras": run_lib((a0,a1) => run_loop($______bend_core_extras(a0,a1)), 2),
  "../../bend/core:passes_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($______bend_core_passes_pick(a0,a1,a2,a3,str_in(a4),a5,a6)), 7),
  "../../bend/core:passes": run_lib((a0,a1) => run_loop($______bend_core_passes(a0,a1)), 2),
  "../../bend/core:complete_pick": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_complete_pick(a0,a1,a2,a3)), 4),
  "../../bend/core:complete": run_lib((a0,a1) => run_loop($______bend_core_complete(a0,a1)), 2),
  "../../bend/core:split_args": run_lib((a0) => run_loop($______bend_core_split_args(a0)), 1),
  "../../bend/core:unless": run_lib((a0,a1) => run_loop($______bend_core_unless(a0,a1)), 2),
  "../../bend/core:theme_args": run_lib((a0,a1,a2) => run_loop($______bend_core_theme_args(a0,str_in(a1),str_in(a2))), 3),
  "../../bend/core:pi_bare": run_lib(() => run_loop($______bend_core_pi_bare()), 0),
  "../../bend/core:pi_apart": run_lib(() => run_loop($______bend_core_pi_apart()), 0),
  "../../bend/core:pi_args": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_pi_args(a0,str_in(a1),str_in(a2),str_in(a3))), 4),
  "../../bend/core:remove_one": run_lib((a0,a1) => run_loop($______bend_core_remove_one(a0,str_in(a1))), 2),
  "../../bend/core:unsaid": run_lib((a0,a1,a2) => run_loop($______bend_core_unsaid(a0,a1,a2)), 3),
  "../../bend/core:resumes": run_lib((a0) => run_loop($______bend_core_resumes(str_in(a0))), 1),
  "../../bend/core:chooses": run_lib((a0) => run_loop($______bend_core_chooses(str_in(a0))), 1),
  "../../bend/core:strip": run_lib((a0,a1) => run_loop($______bend_core_strip(a0,a1)), 2),
  "../../bend/core:any_resumes": run_lib((a0) => run_loop($______bend_core_any_resumes(a0)), 1),
  "../../bend/core:any_chooses": run_lib((a0) => run_loop($______bend_core_any_chooses(a0)), 1),
  "../../bend/core:session_args": run_lib((a0) => run_loop($______bend_core_session_args(a0)), 1),
  "../../bend/core:restart_args": run_lib((a0,a1,a2) => run_loop($______bend_core_restart_args(a0,a1,a2)), 3),
  "../../bend/core:hat": run_lib(() => run_loop($______bend_core_hat()), 0),
  "../../bend/core:sparks": run_lib(() => run_loop($______bend_core_sparks()), 0),
  "../../bend/core:put": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_put(str_in(a0),nat_in(a1),str_in(a2)))), 3),
  "../../bend/core:put_row": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_put_row(a0,nat_in(a1),nat_in(a2),str_in(a3))), 4),
  "../../bend/core:glyph": run_lib((a0) => str_out(run_loop($______bend_core_glyph(a0))), 1),
  "../../bend/core:twinkle": run_lib((a0,a1,a2) => run_loop($______bend_core_twinkle(a0,a1,nat_in(a2))), 3),
  "../../bend/core:hat_frame": run_lib((a0) => run_loop($______bend_core_hat_frame(nat_in(a0))), 1),
  "../../bend/core:small_hat": run_lib(() => run_loop($______bend_core_small_hat()), 0),
  "../../bend/core:widths": run_lib((a0) => run_loop($______bend_core_widths(a0)), 1),
  "../../bend/core:inks": run_lib(() => run_loop($______bend_core_inks()), 0),
  "../../bend/core:ink_pick": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_ink_pick(a0,a1,a2))), 3),
  "../../bend/core:ink_of": run_lib((a0) => str_out(run_loop($______bend_core_ink_of(str_in(a0)))), 1),
  "../../bend/core:ink": run_lib((a0) => str_out(run_loop($______bend_core_ink(str_in(a0)))), 1),
  "../../bend/core:is_sep": run_lib((a0,a1) => run_loop($______bend_core_is_sep(str_in(a0),a1)), 2),
  "../../bend/core:squash_put": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_squash_put(a0,a1,str_in(a2),str_in(a3)))), 4),
  "../../bend/core:squash_go": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($______bend_core_squash_go(str_in(a0),a1,a2,a3,str_in(a4)))), 5),
  "../../bend/core:squash": run_lib((a0,a1) => str_out(run_loop($______bend_core_squash(str_in(a0),a1))), 2),
  "../../bend/core:words": run_lib((a0) => str_out(run_loop($______bend_core_words(str_in(a0)))), 1),
  "../../bend/core:mine": run_lib((a0,a1) => run_loop($______bend_core_mine(str_in(a0),str_in(a1))), 2),
  "../../bend/core:title_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => str_out(run_loop($______bend_core_title_pick(a0,a1,a2,str_in(a3),str_in(a4),str_in(a5),str_in(a6)))), 7),
  "../../bend/core:action_title": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_action_title(str_in(a0),a1,str_in(a2),str_in(a3)))), 4),
  "../../bend/core:fits": run_lib((a0,a1) => run_loop($______bend_core_fits(str_in(a0),nat_in(a1))), 2),
  "../../bend/core:clip_at": run_lib((a0,a1) => str_out(run_loop($______bend_core_clip_at(str_in(a0),nat_in(a1)))), 2),
  "../../bend/core:clip": run_lib((a0,a1) => str_out(run_loop($______bend_core_clip(str_in(a0),nat_in(a1)))), 2),
  "../../bend/core:brief": run_lib((a0) => str_out(run_loop($______bend_core_brief(str_in(a0)))), 1),
  "../../bend/core:expand_put": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($______bend_core_expand_put(a0,a1,a2,str_in(a3),str_in(a4),str_in(a5)))), 6),
  "../../bend/core:expand_go": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_expand_go(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:expand": run_lib((a0,a1) => str_out(run_loop($______bend_core_expand(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:line_cur": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_line_cur(a0,str_in(a1),str_in(a2)))), 3),
  "../../bend/core:line_done": run_lib((a0,a1,a2) => run_loop($______bend_core_line_done(a0,str_in(a1),a2)), 3),
  "../../bend/core:lines_go": run_lib((a0,a1,a2) => run_loop($______bend_core_lines_go(str_in(a0),str_in(a1),a2)), 3),
  "../../bend/core:lines": run_lib((a0) => run_loop($______bend_core_lines(str_in(a0))), 1),
  "../../bend/core:first": run_lib((a0,a1) => run_loop($______bend_core_first(a0,nat_in(a1))), 2),
  "../../bend/core:count": run_lib((a0,a1) => run_loop($______bend_core_count(a0,nat_in(a1))), 2),
  "../../bend/core:beyond": run_lib((a0,a1) => run_loop($______bend_core_beyond(a0,nat_in(a1))), 2),
  "../../bend/core:view_of": run_lib((a0,a1,a2) => run_loop($______bend_core_view_of(a0,a1,nat_in(a2))), 3),
  "../../bend/core:result_view": run_lib((a0,a1) => run_loop($______bend_core_result_view(str_in(a0),a1)), 2),
  "../../bend/core:droppable": run_lib((a0) => run_loop($______bend_core_droppable(a0)), 1),
  "../../bend/core:focus_active": run_lib((a0,a1,a2) => run_loop($______bend_core_focus_active(a0,a1,a2)), 3),
  "../../bend/core:after_rtk": run_lib((a0) => run_loop($______bend_core_after_rtk(str_in(a0))), 1),
  "../../bend/core:rtk_skips": run_lib((a0,a1) => run_loop($______bend_core_rtk_skips(a0,str_in(a1))), 2),
  "../../bend/core:last_said": run_lib((a0,a1) => str_out(run_loop($______bend_core_last_said(a0,str_in(a1)))), 2),
  "../../bend/core:unprefixed": run_lib((a0) => str_out(run_loop($______bend_core_unprefixed(str_in(a0)))), 1),
  "../../bend/core:update_line": run_lib((a0) => str_out(run_loop($______bend_core_update_line(str_in(a0)))), 1),
  "../../bend/core:updated": run_lib((a0) => run_loop($______bend_core_updated(str_in(a0))), 1),
  "../../bend/core:asked_pick": run_lib((a0,a1,a2) => run_loop($______bend_core_asked_pick(a0,a1,a2)), 3),
  "../../bend/core:update_asked": run_lib((a0) => run_loop($______bend_core_update_asked(str_in(a0))), 1),
  "../../bend/core:switch_act": run_lib((a0,a1) => run_loop($______bend_core_switch_act(a0,a1)), 2),
  "../../bend/core:listed": run_lib((a0) => str_out(run_loop($______bend_core_listed(a0))), 1),
  "../../bend/core:label": run_lib((a0,a1) => str_out(run_loop($______bend_core_label(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:inspect_line": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_inspect_line(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "../../bend/core:loaded_text": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_loaded_text(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "../../bend/core:described": run_lib((a0,a1) => str_out(run_loop($______bend_core_described(str_in(a0),a1))), 2),
  "../../bend/core:base_prompt": run_lib((a0,a1) => str_out(run_loop($______bend_core_base_prompt(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:system_prompt": run_lib((a0,a1) => str_out(run_loop($______bend_core_system_prompt(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:among": run_lib((a0,a1) => run_loop($______bend_core_among(a0,str_in(a1))), 2),
  "../../bend/core:first_said": run_lib((a0,a1) => str_out(run_loop($______bend_core_first_said(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:home_pick": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($______bend_core_home_pick(a0,str_in(a1),a2,str_in(a3),str_in(a4)))), 5),
  "../../bend/core:home_of": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($______bend_core_home_of(str_in(a0),str_in(a1),str_in(a2),str_in(a3),a4,a5))), 6),
  "../../bend/core:adopts_home": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_adopts_home(a0,a1,a2,a3)), 4),
  "../../bend/core:adopts_command": run_lib((a0,a1,a2) => run_loop($______bend_core_adopts_command(str_in(a0),a1,a2)), 3),
  "../../bend/core:moved_list": run_lib((a0,a1) => run_loop($______bend_core_moved_list(a0,a1)), 2),
  "../../bend/core:adopted_say": run_lib((a0) => run_loop($______bend_core_adopted_say(a0)), 1),
  "../../bend/core:adopted": run_lib((a0,a1) => run_loop($______bend_core_adopted(a0,a1)), 2),
  "../../bend/core:plugin_dirs": run_lib((a0,a1) => run_loop($______bend_core_plugin_dirs(str_in(a0),str_in(a1))), 2),
  "../../bend/core:under_home": run_lib((a0) => run_loop($______bend_core_under_home(str_in(a0))), 1),
  "../../bend/core:is_builtin_source": run_lib((a0,a1,a2) => run_loop($______bend_core_is_builtin_source(a0,a1,a2)), 3),
  "../../bend/core:nth": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_nth(a0,nat_in(a1),str_in(a2)))), 3),
  "../../bend/core:state_name": run_lib((a0) => str_out(run_loop($______bend_core_state_name(nat_in(a0)))), 1),
  "../../bend/core:already_loaded": run_lib((a0) => str_out(run_loop($______bend_core_already_loaded(str_in(a0)))), 1),
  "../../bend/core:not_loaded": run_lib((a0) => str_out(run_loop($______bend_core_not_loaded(str_in(a0)))), 1),
  "../../bend/core:runs_on_it": run_lib((a0,a1) => str_out(run_loop($______bend_core_runs_on_it(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:no_builtin": run_lib((a0,a1) => str_out(run_loop($______bend_core_no_builtin(str_in(a0),a1))), 2),
  "../../bend/core:no_plugin_at": run_lib((a0) => str_out(run_loop($______bend_core_no_plugin_at(str_in(a0)))), 1),
  "../../bend/core:no_entry": run_lib((a0) => str_out(run_loop($______bend_core_no_entry(str_in(a0)))), 1),
  "../../bend/core:load_failed": run_lib((a0,a1) => str_out(run_loop($______bend_core_load_failed(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:needs_execute": run_lib((a0) => str_out(run_loop($______bend_core_needs_execute(str_in(a0)))), 1),
  "../../bend/core:already_registered": run_lib((a0,a1) => str_out(run_loop($______bend_core_already_registered(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:no_action": run_lib((a0) => str_out(run_loop($______bend_core_no_action(str_in(a0)))), 1),
  "../../bend/core:action_gone": run_lib((a0) => str_out(run_loop($______bend_core_action_gone(str_in(a0)))), 1),
  "../../bend/core:command_gone": run_lib((a0) => str_out(run_loop($______bend_core_command_gone(str_in(a0)))), 1),
  "../../bend/core:no_such_actions": run_lib((a0) => str_out(run_loop($______bend_core_no_such_actions(a0))), 1),
  "../../bend/core:unloaded_text": run_lib((a0) => str_out(run_loop($______bend_core_unloaded_text(str_in(a0)))), 1),
  "../../bend/core:help": run_lib(() => str_out(run_loop($______bend_core_help())), 0),
  "../../bend/core:pi_only_text": run_lib((a0,a1) => str_out(run_loop($______bend_core_pi_only_text(str_in(a0),a1))), 2),
  "../../bend/core:lists_plugins": run_lib((a0) => run_loop($______bend_core_lists_plugins(a0)), 1),
  "../../bend/core:listing_actions": run_lib((a0) => str_out(run_loop($______bend_core_listing_actions(a0))), 1),
  "../../bend/core:listing": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_listing(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "../../bend/core:switch_said": run_lib((a0) => str_out(run_loop($______bend_core_switch_said(a0))), 1),
  "../../bend/core:at_file": run_lib((a0) => str_out(run_loop($______bend_core_at_file(str_in(a0)))), 1),
  "../../bend/core:at_files": run_lib((a0) => run_loop($______bend_core_at_files(a0)), 1),
  "../../bend/core:said_of": run_lib((a0,a1) => run_loop($______bend_core_said_of(a0,a1)), 2),
  "../../bend/core:restarts_now": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_restarts_now(a0,a1,a2,a3)), 4),
  "../../bend/core:stays_away": run_lib((a0,a1,a2) => run_loop($______bend_core_stays_away(a0,a1,a2)), 3),
  "../../bend/core:last_of": run_lib((a0,a1) => str_out(run_loop($______bend_core_last_of(a0,str_in(a1)))), 2),
  "../../bend/core:last_identity": run_lib((a0) => str_out(run_loop($______bend_core_last_identity(a0))), 1),
  "../../bend/core:tidy": run_lib((a0) => str_out(run_loop($______bend_core_tidy(str_in(a0)))), 1),
  "../../bend/core:become_said": run_lib((a0) => str_out(run_loop($______bend_core_become_said(str_in(a0)))), 1),
  "../../bend/core:keep_starting": run_lib((a0,a1,a2) => run_loop($______bend_core_keep_starting(str_in(a0),str_in(a1),a2)), 3),
  "../../bend/core:completions_go": run_lib((a0,a1) => run_loop($______bend_core_completions_go(a0,str_in(a1))), 2),
  "../../bend/core:completions": run_lib((a0,a1) => run_loop($______bend_core_completions(a0,str_in(a1))), 2),
  "../../bend/core:day": run_lib((a0) => str_out(run_loop($______bend_core_day(str_in(a0)))), 1),
  "../../bend/core:focus_said": run_lib((a0,a1) => str_out(run_loop($______bend_core_focus_said(a0,a1))), 2),
  "../../bend/core:think_levels": run_lib(() => run_loop($______bend_core_think_levels()), 0),
  "../../bend/core:think_describe": run_lib(() => str_out(run_loop($______bend_core_think_describe())), 0),
  "../../bend/core:think_said": run_lib((a0) => str_out(run_loop($______bend_core_think_said(str_in(a0)))), 1),
  "../../bend/core:kind_of": run_lib((a0) => str_out(run_loop($______bend_core_kind_of(a0))), 1),
  "../../bend/core:carried_on": run_lib((a0) => str_out(run_loop($______bend_core_carried_on(a0))), 1),
  "../../bend/core:update_said": run_lib((a0) => str_out(run_loop($______bend_core_update_said(str_in(a0)))), 1),
  "../../bend/core:not_a_checkout": run_lib((a0) => str_out(run_loop($______bend_core_not_a_checkout(str_in(a0)))), 1),
  "../../bend/core:rtk_pick": run_lib((a0,a1,a2) => run_loop($______bend_core_rtk_pick(a0,str_in(a1),str_in(a2))), 3),
  "../../bend/core:rtk_takes": run_lib((a0,a1,a2) => run_loop($______bend_core_rtk_takes(nat_in(a0),str_in(a1),str_in(a2))), 3),
  "../../bend/core:in_dir": run_lib((a0,a1) => str_out(run_loop($______bend_core_in_dir(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:in_dirs": run_lib((a0) => run_loop($______bend_core_in_dirs(a0)), 1),
  "../../bend/core:rtk_places": run_lib((a0,a1,a2) => run_loop($______bend_core_rtk_places(a0,a1,str_in(a2))), 3),
  "../../bend/core:rtk_missing": run_lib((a0) => str_out(run_loop($______bend_core_rtk_missing(a0))), 1),
  "../../bend/core:gated": run_lib(() => run_loop($______bend_core_gated()), 0),
  "../../bend/core:gate_summary": run_lib((a0) => str_out(run_loop($______bend_core_gate_summary(str_in(a0)))), 1),
  "../../bend/core:gate_asks": run_lib((a0) => str_out(run_loop($______bend_core_gate_asks(str_in(a0)))), 1),
  "../../bend/core:gate_no_one": run_lib((a0) => str_out(run_loop($______bend_core_gate_no_one(str_in(a0)))), 1),
  "../../bend/core:gate_declined": run_lib((a0) => str_out(run_loop($______bend_core_gate_declined(str_in(a0)))), 1),
  "../../bend/core:emit": run_lib((a0,a1) => run_loop($______bend_core_emit(nat_in(a0),a1)), 2),
  "../../bend/core:pack_go": run_lib((a0,a1,a2,a3,a4) => run_loop($______bend_core_pack_go(a0,nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4))), 5),
  "../../bend/core:pack": run_lib((a0,a1,a2) => run_loop($______bend_core_pack(a0,nat_in(a1),nat_in(a2))), 3),
  "../../bend/core:layout_pick": run_lib((a0,a1,a2) => run_loop($______bend_core_layout_pick(a0,nat_in(a1),nat_in(a2))), 3),
  "../../bend/core:layout": run_lib((a0,a1) => run_loop($______bend_core_layout(nat_in(a0),nat_in(a1))), 2),
  "../../bend/core:pad_end": run_lib((a0,a1,a2) => run_loop($______bend_core_pad_end(nat_in(a0),a1,str_in(a2))), 3),
  "../../bend/core:blanks": run_lib((a0) => run_loop($______bend_core_blanks(nat_in(a0))), 1),
  "../../bend/core:beside_row": run_lib((a0,a1) => str_out(run_loop($______bend_core_beside_row(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:beside_zip": run_lib((a0,a1) => run_loop($______bend_core_beside_zip(a0,a1)), 2),
  "../../bend/core:margined": run_lib((a0) => run_loop($______bend_core_margined(a0)), 1),
  "../../bend/core:header_beside": run_lib((a0,a1,a2) => run_loop($______bend_core_header_beside(a0,a1,nat_in(a2))), 3),
  "../../bend/core:header_under": run_lib((a0,a1) => run_loop($______bend_core_header_under(a0,a1)), 2),
  "../../bend/core:cap_moves": run_lib((a0,a1) => run_loop($______bend_core_cap_moves(a0,a1)), 2),
  "../../bend/core:next_frame": run_lib((a0) => run_loop($______bend_core_next_frame(nat_in(a0))), 1),
  "../../bend/core:blank_lines": run_lib((a0) => run_loop($______bend_core_blank_lines(a0)), 1),
  "../../bend/core:blank_view": run_lib((a0,a1) => run_loop($______bend_core_blank_view(a0,nat_in(a1))), 2),
  "../../bend/core:more_hint": run_lib((a0) => str_out(run_loop($______bend_core_more_hint(nat_in(a0)))), 1),
  "../../bend/core:labels": run_lib((a0) => run_loop($______bend_core_labels(a0)), 1),
  "../../bend/core:widest": run_lib((a0) => run_loop($______bend_core_widest(a0)), 1),
  "../../bend/core:pad_right": run_lib((a0,a1) => str_out(run_loop($______bend_core_pad_right(str_in(a0),nat_in(a1)))), 2),
  "../../bend/core:wide_rows": run_lib((a0,a1) => run_loop($______bend_core_wide_rows(a0,nat_in(a1))), 2),
  "../../bend/core:plugin_rows": run_lib((a0) => run_loop($______bend_core_plugin_rows(a0)), 1),
  "../../bend/core:plugin_line": run_lib((a0) => str_out(run_loop($______bend_core_plugin_line(a0))), 1),
  "../../bend/core:indented": run_lib((a0) => run_loop($______bend_core_indented(a0)), 1),
  "../../bend/core:shape": run_lib(() => str_out(run_loop($______bend_core_shape())), 0),
  "../../bend/core:inspect_text": run_lib((a0,a1) => str_out(run_loop($______bend_core_inspect_text(a0,a1))), 2),
  "../../bend/core:no_map": run_lib((a0) => str_out(run_loop($______bend_core_no_map(str_in(a0)))), 1),
  "../../bend/core:own_pi": run_lib((a0) => str_out(run_loop($______bend_core_own_pi(str_in(a0)))), 1),
  "../../bend/core:old_pi": run_lib((a0,a1) => str_out(run_loop($______bend_core_old_pi(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:pi_env": run_lib((a0) => run_loop($______bend_core_pi_env(str_in(a0))), 1),
  "../../bend/core:pi_env_cleared": run_lib(() => run_loop($______bend_core_pi_env_cleared()), 0),
  "../../bend/core:var_names": run_lib((a0) => run_loop($______bend_core_var_names(a0)), 1),
  "../../bend/core:pi_env_touched": run_lib(() => run_loop($______bend_core_pi_env_touched()), 0),
  "../../bend/core:brought_files": run_lib(() => run_loop($______bend_core_brought_files()), 0),
  "../../bend/core:brought_settings": run_lib(() => run_loop($______bend_core_brought_settings()), 0),
  "../../bend/core:pi_addons": run_lib(() => run_loop($______bend_core_pi_addons()), 0),
  "../../bend/core:settings_brought": run_lib((a0) => run_loop($______bend_core_settings_brought(a0)), 1),
  "../../bend/core:brings": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_brings(a0,a1,str_in(a2),str_in(a3))), 4),
  "../../bend/core:brought_list": run_lib((a0) => str_out(run_loop($______bend_core_brought_list(a0))), 1),
  "../../bend/core:brought_said": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_brought_said(a0,str_in(a1),str_in(a2)))), 3),
  "../../bend/core:with_slash": run_lib((a0) => str_out(run_loop($______bend_core_with_slash(str_in(a0)))), 1),
  "../../bend/core:inside": run_lib((a0,a1) => run_loop($______bend_core_inside(str_in(a0),str_in(a1))), 2),
  "../../bend/core:takes": run_lib((a0,a1) => run_loop($______bend_core_takes(a0,str_in(a1))), 2),
  "../../bend/core:sparing": run_lib((a0,a1) => run_loop($______bend_core_sparing(a0,str_in(a1))), 2),
  "../../bend/core:all_rooted": run_lib((a0) => run_loop($______bend_core_all_rooted(a0)), 1),
  "../../bend/core:rooted": run_lib((a0) => run_loop($______bend_core_rooted(a0)), 1),
  "../../bend/core:parent_go": run_lib((a0) => str_out(run_loop($______bend_core_parent_go(str_in(a0)))), 1),
  "../../bend/core:parent": run_lib((a0) => str_out(run_loop($______bend_core_parent(str_in(a0)))), 1),
  "../../bend/core:parents": run_lib((a0) => run_loop($______bend_core_parents(a0)), 1),
  "../../bend/core:sessions_dir": run_lib((a0) => str_out(run_loop($______bend_core_sessions_dir(str_in(a0)))), 1),
  "../../bend/core:export_dir": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_export_dir(str_in(a0),str_in(a1),str_in(a2),nat_in(a3)))), 4),
  "../../bend/core:origins": run_lib((a0,a1) => run_loop($______bend_core_origins(str_in(a0),str_in(a1))), 2),
  "../../bend/core:origin_dirs": run_lib((a0) => run_loop($______bend_core_origin_dirs(a0)), 1),
  "../../bend/core:export_fits": run_lib((a0,a1,a2) => run_loop($______bend_core_export_fits(str_in(a0),str_in(a1),str_in(a2))), 3),
  "../../bend/core:is_conversation": run_lib((a0) => run_loop($______bend_core_is_conversation(str_in(a0))), 1),
  "../../bend/core:conversation_to": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_conversation_to(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:readable": run_lib((a0) => str_out(run_loop($______bend_core_readable(str_in(a0)))), 1),
  "../../bend/core:minute": run_lib((a0) => str_out(run_loop($______bend_core_minute(str_in(a0)))), 1),
  "../../bend/core:transcript_head": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_transcript_head(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:voice_of": run_lib((a0) => run_loop($______bend_core_voice_of(str_in(a0))), 1),
  "../../bend/core:said_block": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_said_block(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:more_lines": run_lib((a0) => str_out(run_loop($______bend_core_more_lines(nat_in(a0)))), 1),
  "../../bend/core:shown_block": run_lib((a0) => str_out(run_loop($______bend_core_shown_block(a0))), 1),
  "../../bend/core:result_block": run_lib((a0) => str_out(run_loop($______bend_core_result_block(str_in(a0)))), 1),
  "../../bend/core:call_line": run_lib((a0,a1) => str_out(run_loop($______bend_core_call_line(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:piece_as": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_piece_as(a0,str_in(a1),str_in(a2),str_in(a3)))), 4),
  "../../bend/core:piece": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_piece(str_in(a0),str_in(a1),str_in(a2),str_in(a3)))), 4),
  "../../bend/core:counted": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_counted(nat_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:tally_lines": run_lib((a0) => run_loop($______bend_core_tally_lines(a0)), 1),
  "../../bend/core:bulleted": run_lib((a0) => run_loop($______bend_core_bulleted(a0)), 1),
  "../../bend/core:or_nothing": run_lib((a0) => run_loop($______bend_core_or_nothing(a0)), 1),
  "../../bend/core:own_folders": run_lib(() => run_loop($______bend_core_own_folders()), 0),
  "../../bend/core:left_over": run_lib((a0,a1) => run_loop($______bend_core_left_over(a0,a1)), 2),
  "../../bend/core:left_over_line": run_lib((a0) => str_out(run_loop($______bend_core_left_over_line(str_in(a0)))), 1),
  "../../bend/core:export_lines": run_lib((a0,a1) => run_loop($______bend_core_export_lines(a0,a1)), 2),
  "../../bend/core:export_readme": run_lib((a0,a1) => str_out(run_loop($______bend_core_export_readme(str_in(a0),a1))), 2),
  "../../bend/core:export_said": run_lib((a0,a1) => str_out(run_loop($______bend_core_export_said(str_in(a0),a1))), 2),
  "../../bend/core:export_inside": run_lib((a0) => str_out(run_loop($______bend_core_export_inside(str_in(a0)))), 1),
  "../../bend/core:export_taken": run_lib((a0) => str_out(run_loop($______bend_core_export_taken(str_in(a0)))), 1),
  "../../bend/core:export_broke": run_lib((a0) => str_out(run_loop($______bend_core_export_broke(str_in(a0)))), 1),
  "../../bend/core:export_usage": run_lib(() => str_out(run_loop($______bend_core_export_usage())), 0),
  "../../bend/core:is_option": run_lib((a0) => run_loop($______bend_core_is_option(str_in(a0))), 1),
  "../../bend/core:bare": run_lib((a0,a1) => run_loop($______bend_core_bare(a0,a1)), 2),
  "../../bend/core:options": run_lib((a0) => run_loop($______bend_core_options(a0)), 1),
  "../../bend/core:first_of": run_lib((a0) => str_out(run_loop($______bend_core_first_of(a0))), 1),
  "../../bend/core:value_after": run_lib((a0,a1) => str_out(run_loop($______bend_core_value_after(a0,str_in(a1)))), 2),
  "../../bend/core:export_asked": run_lib((a0) => run_loop($______bend_core_export_asked(a0)), 1),
  "../../bend/core:delete_asked": run_lib((a0) => run_loop($______bend_core_delete_asked(a0)), 1),
  "../../bend/core:what_pick": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_what_pick(a0,a1,a2,a3)), 4),
  "../../bend/core:what_of": run_lib((a0) => run_loop($______bend_core_what_of(str_in(a0))), 1),
  "../../bend/core:old_wanted": run_lib((a0,a1) => run_loop($______bend_core_old_wanted(str_in(a0),str_in(a1))), 2),
  "../../bend/core:based": run_lib((a0,a1) => run_loop($______bend_core_based(str_in(a0),a1)), 2),
  "../../bend/core:wanted": run_lib((a0,a1,a2) => run_loop($______bend_core_wanted(a0,str_in(a1),str_in(a2))), 3),
  "../../bend/core:doomed": run_lib((a0,a1,a2,a3,a4) => run_loop($______bend_core_doomed(a0,str_in(a1),str_in(a2),str_in(a3),str_in(a4))), 5),
  "../../bend/core:goes": run_lib((a0,a1,a2) => run_loop($______bend_core_goes(a0,a1,a2)), 3),
  "../../bend/core:emptied": run_lib((a0,a1,a2) => run_loop($______bend_core_emptied(a0,a1,str_in(a2))), 3),
  "../../bend/core:dangling": run_lib((a0,a1) => run_loop($______bend_core_dangling(a0,a1)), 2),
  "../../bend/core:link_dirs": run_lib((a0,a1,a2) => run_loop($______bend_core_link_dirs(str_in(a0),str_in(a1),str_in(a2))), 3),
  "../../bend/core:old_home_link": run_lib((a0) => str_out(run_loop($______bend_core_old_home_link(str_in(a0)))), 1),
  "../../bend/core:delete_usage": run_lib(() => str_out(run_loop($______bend_core_delete_usage())), 0),
  "../../bend/core:why_pick": run_lib((a0,a1,a2,a3,a4,a5,a6,a7) => str_out(run_loop($______bend_core_why_pick(a0,a1,a2,a3,a4,a5,str_in(a6),str_in(a7)))), 8),
  "../../bend/core:is_unknown": run_lib((a0) => run_loop($______bend_core_is_unknown(a0)), 1),
  "../../bend/core:why_not": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($______bend_core_why_not(a0,str_in(a1),str_in(a2),str_in(a3),str_in(a4)))), 5),
  "../../bend/core:size_text": run_lib((a0) => str_out(run_loop($______bend_core_size_text(nat_in(a0)))), 1),
  "../../bend/core:row_lines": run_lib((a0) => run_loop($______bend_core_row_lines(a0)), 1),
  "../../bend/core:link_lines": run_lib((a0) => run_loop($______bend_core_link_lines(a0)), 1),
  "../../bend/core:export_line": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_export_line(a0,str_in(a1),str_in(a2),str_in(a3)))), 4),
  "../../bend/core:delete_preview": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($______bend_core_delete_preview(str_in(a0),a1,a2,str_in(a3),a4))), 5),
  "../../bend/core:deleted_said": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_deleted_said(a0,a1,str_in(a2),a3))), 4),
  "../../bend/core:nothing_there": run_lib((a0) => str_out(run_loop($______bend_core_nothing_there(a0))), 1),
  "../../bend/core:export_first_failed": run_lib((a0) => str_out(run_loop($______bend_core_export_first_failed(str_in(a0)))), 1),
  "../../bend/core:setting": run_lib((a0,a1) => run_loop($______bend_core_setting(str_in(a0),str_in(a1))), 2),
  "../../bend/core:default_settings": run_lib((a0,a1,a2) => run_loop($______bend_core_default_settings(str_in(a0),str_in(a1),str_in(a2))), 3),
  "../../bend/core:kept_off": run_lib((a0,a1) => run_loop($______bend_core_kept_off(a0,a1)), 2),
  "../../bend/core:or_unset": run_lib((a0) => str_out(run_loop($______bend_core_or_unset(str_in(a0)))), 1),
  "../../bend/core:default_said": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_default_said(str_in(a0),str_in(a1),a2))), 3),
  "is_folder": run_lib((a0) => run_loop($is_folder(str_in(a0))), 1),
  "covers": run_lib((a0,a1) => run_loop($covers(str_in(a0),str_in(a1))), 2),
  "may_write": run_lib((a0,a1) => run_loop($may_write(a0,str_in(a1))), 2),
  "may": run_lib((a0,a1) => run_loop($may(a0,str_in(a1))), 2),
  "clash": run_lib((a0,a1) => run_loop($clash(str_in(a0),str_in(a1))), 2),
  "clashes": run_lib((a0,a1) => run_loop($clashes(str_in(a0),a1)), 2),
  "overlap": run_lib((a0,a1) => run_loop($overlap(a0,a1)), 2),
  "inside": run_lib((a0,a1) => run_loop($inside(a0,a1)), 2),
  "names_of": run_lib((a0) => run_loop($names_of(a0)), 1),
  "owns_of": run_lib((a0) => run_loop($owns_of(a0)), 1),
  "laws_of": run_lib((a0) => run_loop($laws_of(a0)), 1),
  "distinct": run_lib((a0) => run_loop($distinct(a0)), 1),
  "shares": run_lib((a0,a1) => run_loop($shares(a0,a1)), 2),
  "disjoint": run_lib((a0) => run_loop($disjoint(a0)), 1),
  "all_inside": run_lib((a0,a1) => run_loop($all_inside(a0,a1)), 2),
  "one_if": run_lib((a0) => run_loop($one_if(a0)), 1),
  "writers": run_lib((a0,a1) => run_loop($writers(a0,str_in(a1))), 2),
  "guard": run_lib((a0,a1,a2) => run_loop($guard(a0,a1,a2)), 3),
  "verdict": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($verdict(a0,a1,a2,a3,a4,a5)), 6),
  "judge": run_lib((a0,a1,a2,a3) => run_loop($judge(nat_in(a0),nat_in(a1),a2,a3)), 4),
  "runs_on": run_lib((a0,a1) => str_out(run_loop($runs_on(str_in(a0),str_in(a1)))), 2),
  "kept": run_lib((a0) => str_out(run_loop($kept(str_in(a0)))), 1),
  "levels": run_lib(() => run_loop($levels()), 0),
  "wants_pick": run_lib((a0,a1,a2) => run_loop($wants_pick(a0,a1,a2)), 3),
  "wants": run_lib((a0) => run_loop($wants(str_in(a0))), 1),
  "is_name_start": run_lib((a0) => run_loop($is_name_start(str_in(a0))), 1),
  "is_name_char": run_lib((a0) => run_loop($is_name_char(str_in(a0))), 1),
  "name_put": run_lib((a0,a1,a2) => str_out(run_loop($name_put(a0,str_in(a1),str_in(a2)))), 3),
  "name_of": run_lib((a0) => str_out(run_loop($name_of(str_in(a0)))), 1),
  "starts_name": run_lib((a0) => run_loop($starts_name(str_in(a0))), 1),
  "starts_space": run_lib((a0) => run_loop($starts_space(str_in(a0))), 1),
  "declared_in": run_lib((a0) => run_loop($declared_in(str_in(a0))), 1),
  "law_on": run_lib((a0) => run_loop($law_on(str_in(a0))), 1),
  "found_put": run_lib((a0,a1) => run_loop($found_put(a0,a1)), 2),
  "laws_go": run_lib((a0,a1) => run_loop($laws_go(a0,a1)), 2),
  "laws_in": run_lib((a0) => run_loop($laws_in(str_in(a0))), 1),
  "slashed_put": run_lib((a0,a1,a2) => str_out(run_loop($slashed_put(a0,str_in(a1),str_in(a2)))), 3),
  "slashed_go": run_lib((a0,a1) => str_out(run_loop($slashed_go(str_in(a0),str_in(a1)))), 2),
  "slashed": run_lib((a0) => str_out(run_loop($slashed(str_in(a0)))), 1),
  "entry_pick": run_lib((a0,a1,a2) => run_loop($entry_pick(a0,a1,str_in(a2))), 3),
  "entry_of": run_lib((a0,a1,a2) => run_loop($entry_of(str_in(a0),a1,a2)), 3),
  "why": run_lib((a0,a1) => str_out(run_loop($why(a0,nat_in(a1)))), 2),
  "refused": run_lib((a0) => str_out(run_loop($refused(str_in(a0)))), 1),
  "ticked": run_lib((a0) => run_loop($ticked(a0)), 1),
  "laws_missing": run_lib((a0) => str_out(run_loop($laws_missing(a0))), 1),
  "missing": run_lib((a0,a1) => run_loop($missing(a0,a1)), 2),
  "clip": run_lib((a0,a1) => str_out(run_loop($clip(str_in(a0),nat_in(a1)))), 2),
  "minutes": run_lib((a0) => str_out(run_loop($minutes(nat_in(a0)))), 1),
  "state_pick": run_lib((a0,a1,a2,a3) => str_out(run_loop($state_pick(a0,a1,str_in(a2),nat_in(a3)))), 4),
  "state": run_lib((a0) => str_out(run_loop($state(a0))), 1),
  "how_pick": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($how_pick(a0,a1,str_in(a2),nat_in(a3),str_in(a4)))), 5),
  "how": run_lib((a0,a1) => str_out(run_loop($how(a0,nat_in(a1)))), 2),
  "first_said": run_lib((a0,a1) => str_out(run_loop($first_said(str_in(a0),str_in(a1)))), 2),
  "or_none": run_lib((a0) => str_out(run_loop($or_none(str_in(a0)))), 1),
  "half_report": run_lib((a0,a1,a2,a3,a4,a5,a6) => str_out(run_loop($half_report(str_in(a0),a1,a2,a3,nat_in(a4),str_in(a5),str_in(a6)))), 7),
  "fits": run_lib((a0,a1) => run_loop($fits(a0,str_in(a1))), 2),
  "check_said": run_lib((a0,a1) => str_out(run_loop($check_said(a0,str_in(a1)))), 2),
  "check_lines": run_lib((a0,a1,a2,a3,a4) => run_loop($check_lines(a0,str_in(a1),a2,str_in(a3),str_in(a4))), 5),
  "joined": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($joined(nat_in(a0),a1,str_in(a2),a3,str_in(a4),str_in(a5)))), 6),
  "stopped_early": run_lib(() => str_out(run_loop($stopped_early())), 0),
  "not_yours": run_lib((a0,a1,a2) => str_out(run_loop($not_yours(str_in(a0),str_in(a1),a2))), 3),
  "option": run_lib((a0,a1) => run_loop($option(str_in(a0),str_in(a1))), 2),
  "half_args": run_lib((a0,a1,a2,a3) => run_loop($half_args(str_in(a0),str_in(a1),str_in(a2),str_in(a3))), 4),
  "showing_line": run_lib((a0,a1,a2) => str_out(run_loop($showing_line(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "showing": run_lib((a0,a1,a2,a3) => str_out(run_loop($showing(str_in(a0),str_in(a1),str_in(a2),str_in(a3)))), 4),
  "agent_pick": run_lib((a0,a1) => run_loop($agent_pick(a0,a1)), 2),
  "agent_wants": run_lib((a0) => run_loop($agent_wants(str_in(a0))), 1),
  "cuts": run_lib((a0) => str_out(run_loop($cuts(nat_in(a0)))), 1),
  "standing": run_lib((a0) => run_loop($standing(a0)), 1),
  "method": run_lib((a0) => str_out(run_loop($method(a0))), 1),
  "whole_lines": run_lib((a0) => run_loop($whole_lines(str_in(a0))), 1),
  "other_lines": run_lib((a0) => run_loop($other_lines(a0)), 1),
  "others_part": run_lib((a0) => run_loop($others_part(a0)), 1),
  "owns_part": run_lib((a0) => run_loop($owns_part(a0)), 1),
  "laws_part": run_lib((a0) => run_loop($laws_part(a0)), 1),
  "check_part": run_lib((a0) => run_loop($check_part(str_in(a0))), 1),
  "brief": run_lib((a0,a1,a2,a3,a4,a5,a6) => str_out(run_loop($brief(str_in(a0),str_in(a1),a2,a3,a4,str_in(a5),str_in(a6)))), 7),
  "describe_division": run_lib(() => str_out(run_loop($describe_division())), 0),
  "describe_split": run_lib(() => str_out(run_loop($describe_split())), 0),
};
