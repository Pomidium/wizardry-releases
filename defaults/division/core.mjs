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

function $______bend_core_command_pick(_help_0, _version_0, _pi_0, _auth_0, _update_0) {
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
            return {$: "Run"};
          }
        }
      }
    }
  }
}

function $______bend_core_command_of(_first_0) {
  return $______bend_core_command_pick($$______bend_core_has({$: "Con", "head": "--help", "tail": {$: "Con", "head": "-h", "tail": {$: "Nil"}}}, _first_0), $$______bend_core_has({$: "Con", "head": "--version", "tail": {$: "Con", "head": "-v", "tail": {$: "Nil"}}}, _first_0), $$______bend_core_has({$: "Con", "head": "install", "tail": {$: "Con", "head": "remove", "tail": {$: "Con", "head": "uninstall", "tail": {$: "Con", "head": "list", "tail": {$: "Con", "head": "config", "tail": {$: "Con", "head": "mcp", "tail": {$: "Nil"}}}}}}}, _first_0), $$String_eq(_first_0, "auth"), $$String_eq(_first_0, "update"));
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

function $______bend_core_pi_args(_rest_0, _sessions_0, _themes_0, _pair_0) {
  const _x_0 = $$______bend_core_has(_rest_0, "--session-dir");
  const _x_1 = $$______bend_core_has(_rest_0, "--no-session");
  return $List_concat({$: "Con", "head": {$: "Con", "head": "--no-builtin-tools", "tail": {$: "Con", "head": "--no-extensions", "tail": {$: "Con", "head": "--no-skills", "tail": {$: "Con", "head": "--no-prompt-templates", "tail": {$: "Con", "head": "--no-context-files", "tail": {$: "Nil"}}}}}}, "tail": {$: "Con", "head": $$______bend_core_unless((_x_0 || _x_1), {$: "Con", "head": "--session-dir", "tail": {$: "Con", "head": _sessions_0, "tail": {$: "Nil"}}}), "tail": {$: "Con", "head": $$______bend_core_theme_args(_rest_0, _themes_0, _pair_0), "tail": {$: "Con", "head": _rest_0, "tail": {$: "Nil"}}}}});
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
  return $String_join({$: "Con", "head": "wizardry - Pi on Cordis. Every plugin is a tool call; the agent chooses which to make.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Usage:", "tail": {$: "Con", "head": "  wizardry [options] [messages...]     Start a session (interactive unless -p)", "tail": {$: "Con", "head": "  wizardry plugins                     List loaded plugins and the actions they provide", "tail": {$: "Con", "head": "  wizardry update [on|off]             Update now, or turn automatic updates on or off", "tail": {$: "Con", "head": "  wizardry auth <command>              Pi's credential commands (wizardry shares Pi's logins)", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Options:", "tail": {$: "Con", "head": "  --plugin <name|path>   Load a plugin for this run (repeatable)", "tail": {$: "Con", "head": "  --gate                 Load the \"gate\" plugin: ask before bash, write, edit and plugin changes", "tail": {$: "Con", "head": "  --version, -v          Show the version", "tail": {$: "Con", "head": "  --help, -h             Show this help", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Every other option goes to Pi unchanged: --model, --thinking, -p/--print, -c/--continue,", "tail": {$: "Con", "head": "-r/--resume, --mode json|rpc, --no-session, and so on (see `pi --help`).", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Plugins load from ~/.wizardry/plugins/, ./.wizardry/plugins/, and ~/.wizardry/plugins.json.", "tail": {$: "Con", "head": "wizardry updates itself in the background whenever it can; /update off in a session stops that.", "tail": {$: "Con", "head": "Nothing asks for approval unless you pass --gate.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}}}}, "\n");
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
  return $String_join({$: "Con", "head": "A plugin is a .ts or .js file. The smallest one needs no imports:", "tail": {$: "Con", "head": "  export const name = \"weather\"", "tail": {$: "Con", "head": "  export const actions = [{", "tail": {$: "Con", "head": "    name: \"weather\", description: \"Current weather for a city.\",", "tail": {$: "Con", "head": "    parameters: { type: \"object\", properties: { city: { type: \"string\" } }, required: [\"city\"] },", "tail": {$: "Con", "head": "    async execute({ city }, env) { return \"text for the agent\" },   // env: { cwd, signal, update(text), pi (ExtensionContext) }", "tail": {$: "Con", "head": "  }]", "tail": {$: "Con", "head": "For lifecycle or services, export `apply(ctx, config)` (or a default function/class) and use the Cordis context:", "tail": {$: "Con", "head": "ctx.actions.register(action), ctx.on(event, listener), ctx.provide(name, value), `export const inject = [...]`.", "tail": {$: "Con", "head": "ctx.effect(setup) runs setup IMMEDIATELY and keeps its return value as the cleanup on unload; passing the cleanup itself undoes the setup at once.", "tail": {$: "Con", "head": "Events: action/registered, action/changed, action/unregistered, action/before (return a string to refuse the call), action/after, task/end,", "tail": {$: "Con", "head": "pi/ready (Pi's ExtensionAPI is live), pi/session-start (api, piCtx; per-session choices go here: api.setModel, api.setThinkingLevel).", "tail": {$: "Con", "head": "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.", "tail": {$: "Con", "head": "Everything a plugin registers is removed when it is unloaded.", "tail": {$: "Con", "head": "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.", "tail": {$: "Con", "head": "Before editing wizardry itself, call cordis_map: the map of the framework you run on.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}, "\n");
}

function $______bend_core_inspect_text(_lines_0, _idle_0) {
  const _x_0 = $$______bend_core_listed(_idle_0);
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "Loaded plugins:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": _lines_0, "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Builtin plugins not loaded: " + _x_0), "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": $$______bend_core_shape(), "tail": {$: "Nil"}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $______bend_core_no_map(_app_0) {
  return $String_concat({$: "Con", "head": "No AGENTS.md in ", "tail": {$: "Con", "head": _app_0, "tail": {$: "Con", "head": ". This wizardry predates it; the repo has it: https://github.com/Pomidium/wizardry", "tail": {$: "Nil"}}}});
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

function $guard(_bad_0, _why_0, _rest_0) {
  if (_bad_0) {
    return {$: "Refuse", "why": _why_0};
  } else {
    return _rest_0;
  }
}

function $judge(_depth_0, _limit_0, _chunk_0, _parent_0, _first_0, _second_0) {
  const _n1_0 = _first_0["name"];
  const _o1_0 = _first_0["owns"];
  const _l1_0 = _first_0["laws"];
  const _m1_0 = _first_0["minutes"];
  const _n2_0 = _second_0["name"];
  const _o2_0 = _second_0["owns"];
  const _l2_0 = _second_0["laws"];
  const _m2_0 = _second_0["minutes"];
  const _x_0 = $$List_is_empty(_o1_0);
  const _x_1 = $$List_is_empty(_o2_0);
  const _x_2 = $$List_is_empty(_l1_0);
  const _x_3 = $$List_is_empty(_l2_0);
  return $guard($$Bool_not((_depth_0 < _limit_0)), {$: "TooDeep"}, $$guard($$Bool_not($$Bool_and($$Nat_is_ge(_m1_0, _chunk_0), $$Nat_is_ge(_m2_0, _chunk_0))), {$: "TooSmall"}, $$guard((_x_0 || _x_1), {$: "NoFiles"}, $$guard((_x_2 || _x_3), {$: "NoLaws"}, $$guard($$String_eq(_n1_0, _n2_0), {$: "SameName"}, $$guard($$______bend_core_overlaps(_l1_0, _l2_0), {$: "SharedLaw"}, $$guard($$Bool_not($$Bool_and($$inside(_o1_0, _parent_0), $$inside(_o2_0, _parent_0))), {$: "Outside"}, $$guard($$overlap(_o1_0, _o2_0), {$: "Trample"}, {$: "Divide"}))))))));
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

function $why(_reason_0, _chunk_0, _depth_0) {
  if (_reason_0.$ === "TooDeep") {
    return $String_concat({$: "Con", "head": "this task has already been cut ", "tail": {$: "Con", "head": $$Nat_show(_depth_0), "tail": {$: "Con", "head": " times on the way here", "tail": {$: "Nil"}}}});
  } else if (_reason_0.$ === "TooSmall") {
    return $String_concat({$: "Con", "head": "a half under ", "tail": {$: "Con", "head": $$Nat_show(_chunk_0), "tail": {$: "Con", "head": " minutes of work is not worth an agent of its own", "tail": {$: "Nil"}}}});
  } else if (_reason_0.$ === "NoFiles") {
    return "each half needs at least one file or folder that is its own";
  } else if (_reason_0.$ === "NoLaws") {
    return "each half needs at least one law to prove, or nothing checks its work";
  } else if (_reason_0.$ === "SameName") {
    return "the halves need different names";
  } else if (_reason_0.$ === "SharedLaw") {
    return "a law was given to both halves; every law has one prover";
  } else if (_reason_0.$ === "Outside") {
    return "a half was given a file that is not yours to hand out";
  } else {
    return "the halves were given a file in common, or one a folder that holds the other's file";
  }
}

function $refused(_why_0) {
  return $String_concat({$: "Con", "head": "Not divided: ", "tail": {$: "Con", "head": _why_0, "tail": {$: "Con", "head": ". Nothing was started. Do this task yourself, or cut it differently.", "tail": {$: "Nil"}}}});
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

function $half_report(_name_0, _owns_0, _laws_0, _ended_0, _ms_0, _out_0, _err_0) {
  return $String_concat({$: "Con", "head": "## ", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": $$how(_ended_0, _ms_0), "tail": {$: "Con", "head": "\nOwned: ", "tail": {$: "Con", "head": $$String_join(_owns_0, ", "), "tail": {$: "Con", "head": "\nLaws: ", "tail": {$: "Con", "head": $$String_join(_laws_0, ", "), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": $$clip($$first_said(_out_0, _err_0), (6000 )), "tail": {$: "Nil"}}}}}}}}}}});
}

function $fits(_ended_0, _said_0) {
  const _code_0 = _ended_0["code"];
  const _stopped_0 = _ended_0["stopped"];
  return $Bool_and($$Nat_is_eq(_code_0, 0), $$Bool_and($$String_is_empty(_stopped_0), $$Bool_not(string_contains(_said_0, "SOME PROOFS FAIL"))));
}

function $check_said(_fit_0, _stopped_0) {
  if (_fit_0) {
    return "It passes: the halves fit.";
  } else {
    return $String_concat({$: "Con", "head": "It FAILS", "tail": {$: "Con", "head": $$Bool_pick($$String_is_empty(_stopped_0), "", $$String_concat({$: "Con", "head": " (", "tail": {$: "Con", "head": _stopped_0, "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}})), "tail": {$: "Con", "head": ": the halves do not fit yet. Repair it yourself if it is small; if a law was wrong, change it and cut again.", "tail": {$: "Nil"}}}});
  }
}

function $joined(_ms_0, _reports_0, _check_0, _fit_0, _stopped_0, _said_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": $$String_concat({$: "Con", "head": "Both halves are back after ", "tail": {$: "Con", "head": $$minutes(_ms_0), "tail": {$: "Con", "head": ". Every file is yours again.", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Con", "head": _reports_0, "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": ("## The check: " + _check_0), "tail": {$: "Con", "head": $$check_said(_fit_0, _stopped_0), "tail": {$: "Con", "head": $$clip($$Bool_pick($$String_is_empty(_said_0), "(no output)", _said_0), (4000 )), "tail": {$: "Nil"}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $stopped_early() {
  return "Stopped: both halves were ended before they finished. What they wrote so far is in their files.";
}

function $not_yours(_path_0, _name_0, _owns_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _path_0, "tail": {$: "Con", "head": "\" is not yours to write: your half (\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\") owns ", "tail": {$: "Con", "head": $$String_join(_owns_0, ", "), "tail": {$: "Con", "head": ". If the task cannot be done without it, stop and say so in your reply.", "tail": {$: "Nil"}}}}}}}});
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
  return $String_join({$: "Con", "head": "The agents division starts run on", "tail": {$: "Con", "head": $$showing_line("model", _model_0, _session_model_0), "tail": {$: "Con", "head": $$showing_line("thinking", _thinking_0, _session_thinking_0), "tail": {$: "Con", "head": "Change with /division model and /division thinking.", "tail": {$: "Nil"}}}}}, "\n");
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
    const _x_0 = $$String_join(_owns_0, ", ");
    const _x_1 = $$String_join(_laws_0, ", ");
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "You are a half of a divided task, ", "tail": {$: "Con", "head": $$cuts(_depth_0), "tail": {$: "Con", "head": " down: \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\".", "tail": {$: "Nil"}}}}}}), "tail": {$: "Con", "head": ("Files you own: " + _x_0), "tail": {$: "Con", "head": ("Laws you must prove: " + _x_1), "tail": {$: "Con", "head": ("The check: " + _check_0), "tail": {$: "Nil"}}}}};
  }
}

function $method(_chunk_0, _depth_0, _place_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "DIVISION: a large task cut in two, each half done by its own agent at the same time.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Con", "head": $$standing(_place_0), "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": "When to cut", "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "- Only when you take each half to be at least ", "tail": {$: "Con", "head": $$Nat_show(_chunk_0), "tail": {$: "Con", "head": " minutes of work for an agent, and the", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "  place where the halves meet can be said exactly, as Bend laws. Otherwise do the task yourself:", "tail": {$: "Con", "head": "  a cut costs a planning step and two agents starting from nothing.", "tail": {$: "Con", "head": "- Not when the work is finding something out (a bug, a design, how a library behaves), and not", "tail": {$: "Con", "head": "  when the halves would each need most of what the other makes. Cut where little crosses.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "How to cut", "tail": {$: "Con", "head": "1. Write the laws at the cut, in a .bend file you own, before anything else (call `bend` for the", "tail": {$: "Con", "head": "   language). A `law` with only a type is a signature: it says what one half provides. A `law`", "tail": {$: "Con", "head": "   with an equation says what the other half may count on. Example, in LAWS.bend:", "tail": {$: "Con", "head": "       law double:            # the first half provides this", "tail": {$: "Con", "head": "         for x: Nat", "tail": {$: "Con", "head": "         Nat", "tail": {$: "Con", "head": "       law double_even:       # and the second half may count on this", "tail": {$: "Con", "head": "         for +x: Nat", "tail": {$: "Con", "head": "         {even(double(x)) == True{} : Bool}", "tail": {$: "Con", "head": "2. Give each half files of its own, and create them: a half fills a law from its own file, with", "tail": {$: "Con", "head": "   `import ./LAWS.bend as L` and `def L.double(x): ...`. Work flows one way: the half that uses", "tail": {$: "Con", "head": "   the other's defs imports the other's file, never both ways.", "tail": {$: "Con", "head": "3. Make one file the gate (PROOF.bend) that imports the laws and every half's files, so that", "tail": {$: "Con", "head": "   `bend PROOF.bend` prints ALL PROOFS CHECK only when every law at every cut is proven.", "tail": {$: "Con", "head": "4. Call `division_split` with the two halves. Both run now, in this directory, and you get", "tail": {$: "Con", "head": "   their reports and the result of the check when both are done.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "What holds while the halves work (proven in division's LAWS.bend)", "tail": {$: "Con", "head": "- A half may write only the files it was handed, and no file is handed to both.", "tail": {$: "Con", "head": "- A half may count on every law at the cut, proven or not: the other half is proving it now.", "tail": {$: "Con", "head": "  Until it has, the checker reports that def as missing; that is expected.", "tail": {$: "Con", "head": "- A half does not change a law. If one cannot be proven as written, it stops and says why, and", "tail": {$: "Con", "head": "  the agent that cut decides: that is you, for your own cut.", "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "- A half that finds divisible work in what it was handed cuts again, and so do its halves, up to ", "tail": {$: "Con", "head": $$Nat_show(_depth_0), "tail": {$: "Con", "head": " cuts deep:", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "  whoever holds work that passes \"When to cut\" splits it instead of doing both parts in a row.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "When the halves are back", "tail": {$: "Con", "head": "- Every file is yours again. If the check fails, read what each half said: repair it yourself", "tail": {$: "Con", "head": "  when it is small, change the law and cut again when the law was wrong.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $whole_lines(_whole_0) {
  return $Bool_pick($$String_is_empty(_whole_0), {$: "Nil"}, {$: "Con", "head": "The whole task, so you know what yours is part of:", "tail": {$: "Con", "head": _whole_0, "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}});
}

function $brief(_name_0, _task_0, _owns_0, _laws_0, _other_0, _other_task_0, _other_laws_0, _whole_0, _check_0, _chunk_0) {
  const _x_0 = $$String_join(_owns_0, ", ");
  const _x_1 = $$String_join(_laws_0, ", ");
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "You are one half of a larger task that was cut in two. Another agent is doing the other half right now, in this same directory.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Your half: " + _name_0), "tail": {$: "Con", "head": _task_0, "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}, "tail": {$: "Con", "head": $$whole_lines(_whole_0), "tail": {$: "Con", "head": {$: "Con", "head": $$String_concat({$: "Con", "head": "The other half (\"", "tail": {$: "Con", "head": _other_0, "tail": {$: "Con", "head": "\"), which is not yours to do: ", "tail": {$: "Con", "head": _other_task_0, "tail": {$: "Nil"}}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Files you own: " + _x_0), "tail": {$: "Con", "head": "You may create and change only these (a name ending in \"/\" is a folder and everything in it). You may read anything. A write anywhere else is refused.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Laws you must prove: " + _x_1), "tail": {$: "Con", "head": "They are declared in the .bend files here. Prove each with a def of the same name in a file you own (call the `bend` action first if you have not used Bend).", "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "Laws the other half is proving: ", "tail": {$: "Con", "head": $$String_join(_other_laws_0, ", "), "tail": {$: "Con", "head": ". Count on them as if they were proven, and on any signature among them as if it were written: until the other half is done the checker reports those defs as missing, which is expected and not yours to fix.", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "Do not change a law. If one of yours cannot be proven as written, or you need something no law gives you, stop and say exactly what and why.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Check your work with: " + _check_0), "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "Before you start, and again whenever the work turns out larger than it looked, look for a cut in your own half: if you find two parts of at least ", "tail": {$: "Con", "head": $$Nat_show(_chunk_0), "tail": {$: "Con", "head": " minutes each that meet at something you can state as Bend laws, cut again (call `division` for how) instead of doing them in a row. The halves you start are told the same. Do it directly only when there is no such cut.", "tail": {$: "Nil"}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "When you are done, reply with what you did, which of your laws are proven, and anything the agent that cut the task needs to know. That reply is all it will see of your work besides the files.", "tail": {$: "Nil"}}}}}}}}}}}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $describe_division(_chunk_0) {
  return $String_concat({$: "Con", "head": "For a LARGE task only: one you take to be at least ", "tail": {$: "Con", "head": $$Nat_show(nat_chk(_chunk_0 + _chunk_0)), "tail": {$: "Con", "head": " minutes of work, that cuts cleanly in two. ", "tail": {$: "Con", "head": "Division cuts it in two halves that separate agents do at the same time, held together by Bend laws written at the cut: ", "tail": {$: "Con", "head": "each half owns its own files, proves its own laws, and counts on the other's before they are proven. ", "tail": {$: "Con", "head": "Returns the method and where you stand in the tree. Do not call it for a small task, for one whose halves would each need ", "tail": {$: "Con", "head": "most of what the other makes, or for work that is finding something out: do those yourself.", "tail": {$: "Nil"}}}}}}}});
}

function $describe_split(_chunk_0) {
  return $String_concat({$: "Con", "head": "Cut the task you have in two and run both halves now, each as its own agent in this directory. Call `division` first for the method. ", "tail": {$: "Con", "head": "Write the laws at the cut before calling. Returns when both halves are done, with what each said and the result of the check. ", "tail": {$: "Con", "head": "Refused, with the reason, when a half is under ", "tail": {$: "Con", "head": $$Nat_show(_chunk_0), "tail": {$: "Con", "head": " minutes of work, has no law to prove, or the halves share a file.", "tail": {$: "Nil"}}}}}});
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

function $Char_is_alpha(_c_0) {
  const _x_0 = $$Char_is_upper(_c_0);
  const _x_1 = $$Char_is_lower(_c_0);
  return (_x_0 || _x_1);
}

function $Char_is_digit(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 48), (_x_0 <= 57));
}

function $Nat_div(_a_0, _b_0) {
  return $Pair_fst(nat_divmod(_a_0, _b_0));
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

function $Char_is_upper(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 65), (_x_0 <= 90));
}

function $Char_is_lower(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 97), (_x_0 <= 122));
}

function $Pair_fst(_p_0) {
  const _a_0 = _p_0["fst"];
  return _a_0;
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
const $$is_folder = $is_folder;
const $$covers = $covers;
const $$may_write = $may_write;
const $$clash = $clash;
const $$clashes = $clashes;
const $$overlap = $overlap;
const $$may = $may;
const $$inside = $inside;
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
const $$Nat_div = $Nat_div;
const $$minutes = $minutes;
const $$how = $how;
const $$first_said = $first_said;
const $$clip = $clip;
const $$check_said = $check_said;
const $$runs_on = $runs_on;
const $$option = $option;
const $$showing_line = $showing_line;
const $$cuts = $cuts;
const $$standing = $standing;
const $$whole_lines = $whole_lines;
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
  "../../bend/core:command_pick": run_lib((a0,a1,a2,a3,a4) => run_loop($______bend_core_command_pick(a0,a1,a2,a3,a4)), 5),
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
  "is_folder": run_lib((a0) => run_loop($is_folder(str_in(a0))), 1),
  "covers": run_lib((a0,a1) => run_loop($covers(str_in(a0),str_in(a1))), 2),
  "may_write": run_lib((a0,a1) => run_loop($may_write(a0,str_in(a1))), 2),
  "may": run_lib((a0,a1) => run_loop($may(a0,str_in(a1))), 2),
  "clash": run_lib((a0,a1) => run_loop($clash(str_in(a0),str_in(a1))), 2),
  "clashes": run_lib((a0,a1) => run_loop($clashes(str_in(a0),a1)), 2),
  "overlap": run_lib((a0,a1) => run_loop($overlap(a0,a1)), 2),
  "inside": run_lib((a0,a1) => run_loop($inside(a0,a1)), 2),
  "guard": run_lib((a0,a1,a2) => run_loop($guard(a0,a1,a2)), 3),
  "judge": run_lib((a0,a1,a2,a3,a4,a5) => run_loop($judge(nat_in(a0),nat_in(a1),nat_in(a2),a3,a4,a5)), 6),
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
  "why": run_lib((a0,a1,a2) => str_out(run_loop($why(a0,nat_in(a1),nat_in(a2)))), 3),
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
  "half_report": run_lib((a0,a1,a2,a3,a4,a5,a6) => str_out(run_loop($half_report(str_in(a0),a1,a2,a3,nat_in(a4),str_in(a5),str_in(a6)))), 7),
  "fits": run_lib((a0,a1) => run_loop($fits(a0,str_in(a1))), 2),
  "check_said": run_lib((a0,a1) => str_out(run_loop($check_said(a0,str_in(a1)))), 2),
  "joined": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($joined(nat_in(a0),a1,str_in(a2),a3,str_in(a4),str_in(a5)))), 6),
  "stopped_early": run_lib(() => str_out(run_loop($stopped_early())), 0),
  "not_yours": run_lib((a0,a1,a2) => str_out(run_loop($not_yours(str_in(a0),str_in(a1),a2))), 3),
  "option": run_lib((a0,a1) => run_loop($option(str_in(a0),str_in(a1))), 2),
  "half_args": run_lib((a0,a1,a2,a3) => run_loop($half_args(str_in(a0),str_in(a1),str_in(a2),str_in(a3))), 4),
  "showing_line": run_lib((a0,a1,a2) => str_out(run_loop($showing_line(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "showing": run_lib((a0,a1,a2,a3) => str_out(run_loop($showing(str_in(a0),str_in(a1),str_in(a2),str_in(a3)))), 4),
  "cuts": run_lib((a0) => str_out(run_loop($cuts(nat_in(a0)))), 1),
  "standing": run_lib((a0) => run_loop($standing(a0)), 1),
  "method": run_lib((a0,a1,a2) => str_out(run_loop($method(nat_in(a0),nat_in(a1),a2))), 3),
  "whole_lines": run_lib((a0) => run_loop($whole_lines(str_in(a0))), 1),
  "brief": run_lib((a0,a1,a2,a3,a4,a5,a6,a7,a8,a9) => str_out(run_loop($brief(str_in(a0),str_in(a1),a2,a3,str_in(a4),str_in(a5),a6,str_in(a7),str_in(a8),nat_in(a9)))), 10),
  "describe_division": run_lib((a0) => str_out(run_loop($describe_division(nat_in(a0)))), 1),
  "describe_split": run_lib((a0) => str_out(run_loop($describe_split(nat_in(a0)))), 1),
};
