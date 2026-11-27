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

function $has(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_1 = $$String_eq(_h_0, _x_0);
    const _x_2 = $$has(_t_0, _x_0);
    return (_x_1 || _x_2);
  }
}

function $keep_if(_keep_0, _h_0, _rest_0) {
  if (!_keep_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _h_0, "tail": _rest_0};
  }
}

function $without(_xs_0, _bad_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $keep_if($$Bool_not($$has(_bad_0, _h_0)), _h_0, $$without(_t_0, _bad_0));
  }
}

function $only(_xs_0, _good_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $keep_if($$has(_good_0, _h_0), _h_0, $$only(_t_0, _good_0));
  }
}

function $overlaps(_xs_0, _bad_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$has(_bad_0, _h_0);
    const _x_1 = $$overlaps(_t_0, _bad_0);
    return (_x_0 || _x_1);
  }
}

function $add(_xs_0, _x_0) {
  return $Bool_pick($$has(_xs_0, _x_0), _xs_0, $$List_append(_xs_0, {$: "Con", "head": _x_0, "tail": {$: "Nil"}}));
}

function $add_all($0, $1) {
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
        $1 = $$add(_xs_0, _h_0);
        continue;
      }
    }
  }
}

function $covers(_xs_0, _need_0) {
  if (_need_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _need_0["head"];
    const _t_0 = _need_0["tail"];
    return $Bool_and($$has(_xs_0, _h_0), $$covers(_xs_0, _t_0));
  }
}

function $names(_es_0) {
  if (_es_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _es_0["head"];
    const _name_0 = _t_0["name"];
    const _t_1 = _es_0["tail"];
    return {$: "Con", "head": _name_0, "tail": $$names(_t_1)};
  }
}

function $keep_entry(_keep_0, _e_0, _rest_0) {
  if (!_keep_0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _e_0, "tail": _rest_0};
  }
}

function $without_named(_es_0, _bad_0) {
  if (_es_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _es_0["head"];
    const _name_0 = _t_0["name"];
    const _path_0 = _t_0["path"];
    const _t_1 = _es_0["tail"];
    return $keep_entry($$Bool_not($$has(_bad_0, _name_0)), {$: "Entry", "name": _name_0, "path": _path_0}, $$without_named(_t_1, _bad_0));
  }
}

function $shipped_kept(_shipped_0, _found_0) {
  return $without_named(_shipped_0, $$names(_found_0));
}

function $plan(_shipped_0, _found_0, _disabled_0) {
  return $without_named($$List_append($$shipped_kept(_shipped_0, _found_0), _found_0), _disabled_0);
}

function $builtins_at_boot(_defaults_0, _disabled_0) {
  return $without(_defaults_0, _disabled_0);
}

function $switched_off(_disabled_0, _name_0) {
  return $add(_disabled_0, _name_0);
}

function $switched_on(_disabled_0, _name_0) {
  return $without(_disabled_0, {$: "Con", "head": _name_0, "tail": {$: "Nil"}});
}

function $remembered(_builtin_0, _default_0) {
  return $Bool_not($$Bool_and(_builtin_0, _default_0));
}

function $core_plugins() {
  return {$: "Con", "head": "pi", "tail": {$: "Con", "head": "cordis", "tail": {$: "Nil"}}};
}

function $is_core(_name_0) {
  return $has($$core_plugins(), _name_0);
}

function $restore_unloads(_loaded_0, _wanted_0) {
  return $without($$without(_loaded_0, _wanted_0), $$core_plugins());
}

function $ends_with_any(_s_0, _exts_0) {
  if (_exts_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _exts_0["head"];
    const _t_0 = _exts_0["tail"];
    const _x_0 = $$String_ends_with(_s_0, _h_0);
    const _x_1 = $$ends_with_any(_s_0, _t_0);
    return (_x_0 || _x_1);
  }
}

function $hidden_char(_c_0) {
  const _c_1 = _c_0;
  const _x_0 = $$Char_is_eq(_c_1, ".");
  const _x_1 = $$Char_is_eq(_c_1, "_");
  return (_x_0 || _x_1);
}

function $hidden(_name_0) {
  if (_name_0 === "") {
    return true;
  } else {
    const _h_0 = _name_0.slice(0, char_len(_name_0));
    return $hidden_char(_h_0);
  }
}

function $usable(_name_0, _folder_0, _entry_0) {
  return $Bool_and($$Bool_not($$hidden(_name_0)), $$Bool_pick(_folder_0, _entry_0, $$ends_with_any(_name_0, {$: "Con", "head": ".ts", "tail": {$: "Con", "head": ".mts", "tail": {$: "Con", "head": ".js", "tail": {$: "Con", "head": ".mjs", "tail": {$: "Nil"}}}}})));
}

function $stem_pick(_dot_0, _cut_0, _more_0) {
  if (!_dot_0) {
    return _more_0;
  } else {
    return _cut_0;
  }
}

function $stem_go(_whole_0, _rev_0) {
  if (_rev_0 === "") {
    return _whole_0;
  } else {
    const _h_0 = _rev_0.slice(0, char_len(_rev_0));
    const _t_0 = _rev_0.slice(char_len(_rev_0));
    return $stem_pick($$Char_is_eq(_h_0, "."), $$Bool_pick($$String_is_empty(_t_0), _whole_0, $$String_reverse(_t_0)), $$stem_go(_whole_0, _t_0));
  }
}

function $stem(_name_0) {
  return $stem_go(_name_0, $$String_reverse(_name_0));
}

function $pick_name(_candidates_0) {
  if (_candidates_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _candidates_0["head"];
    const _t_0 = _candidates_0["tail"];
    return $Bool_pick($$has({$: "Con", "head": "", "tail": {$: "Con", "head": "apply", "tail": {$: "Con", "head": "default", "tail": {$: "Nil"}}}}, _h_0), $$pick_name(_t_0), _h_0);
  }
}

function $command_pick(_help_0, _version_0, _pi_0, _auth_0, _update_0, _export_0, _delete_0) {
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

function $command_of(_first_0) {
  return $command_pick($$has({$: "Con", "head": "--help", "tail": {$: "Con", "head": "-h", "tail": {$: "Nil"}}}, _first_0), $$has({$: "Con", "head": "--version", "tail": {$: "Con", "head": "-v", "tail": {$: "Nil"}}}, _first_0), $$has({$: "Con", "head": "install", "tail": {$: "Con", "head": "remove", "tail": {$: "Con", "head": "uninstall", "tail": {$: "Con", "head": "list", "tail": {$: "Con", "head": "config", "tail": {$: "Con", "head": "mcp", "tail": {$: "Nil"}}}}}}}, _first_0), $$String_eq(_first_0, "auth"), $$String_eq(_first_0, "update"), $$String_eq(_first_0, "export"), $$String_eq(_first_0, "delete"));
}

function $extras_pick(_value_0, _dashes_0, _gate_0, _h_0, _next_0) {
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

function $extras(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $extras_pick(_value_0, $$String_eq(_h_0, "--"), $$String_eq(_h_0, "--gate"), _h_0, $$extras(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $passes_pick(_value_0, _dashes_0, _gate_0, _plugin_0, _h_0, _t_0, _next_0) {
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

function $passes(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $passes_pick(_value_0, $$String_eq(_h_0, "--"), $$String_eq(_h_0, "--gate"), $$String_eq(_h_0, "--plugin"), _h_0, _t_0, $$passes(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $complete_pick(_value_0, _dashes_0, _empty_0, _next_0) {
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

function $complete(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return $Bool_not(_value_0);
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $complete_pick(_value_0, $$String_eq(_h_0, "--"), $$String_is_empty(_h_0), $$complete(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--plugin"))));
  }
}

function $split_args(_argv_0) {
  const _extra_0 = $$extras(_argv_0, false);
  const _rest_0 = $$passes(_argv_0, false);
  return $Bool_pick($$complete(_argv_0, false), {$: "Some", "value": {$: "Args", "extra": _extra_0, "rest": _rest_0}}, {$: "None"});
}

function $unless(_skip_0, _xs_0) {
  if (!_skip_0) {
    return _xs_0;
  } else {
    return {$: "Nil"};
  }
}

function $theme_args(_rest_0, _themes_0, _pair_0) {
  return $List_append({$: "Con", "head": "--theme", "tail": {$: "Con", "head": _themes_0, "tail": {$: "Nil"}}}, $$unless($$has(_rest_0, "--use-theme"), {$: "Con", "head": "--use-theme", "tail": {$: "Con", "head": _pair_0, "tail": {$: "Nil"}}}));
}

function $pi_bare() {
  return {$: "Con", "head": "--no-builtin-tools", "tail": {$: "Con", "head": "--no-extensions", "tail": {$: "Con", "head": "--no-skills", "tail": {$: "Con", "head": "--no-prompt-templates", "tail": {$: "Con", "head": "--no-context-files", "tail": {$: "Nil"}}}}}};
}

function $pi_apart() {
  return {$: "Con", "head": "--no-themes", "tail": {$: "Con", "head": "--no-mcp", "tail": {$: "Con", "head": "--no-approve", "tail": {$: "Nil"}}}};
}

function $pi_args(_rest_0, _sessions_0, _themes_0, _pair_0) {
  const _x_0 = $$has(_rest_0, "--session-dir");
  const _x_1 = $$has(_rest_0, "--no-session");
  return $List_concat({$: "Con", "head": $$pi_bare(), "tail": {$: "Con", "head": $$pi_apart(), "tail": {$: "Con", "head": $$unless((_x_0 || _x_1), {$: "Con", "head": "--session-dir", "tail": {$: "Con", "head": _sessions_0, "tail": {$: "Nil"}}}), "tail": {$: "Con", "head": $$theme_args(_rest_0, _themes_0, _pair_0), "tail": {$: "Con", "head": _rest_0, "tail": {$: "Nil"}}}}}});
}

function $remove_one(_xs_0, _x_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    return $Bool_pick($$String_eq(_h_0, _x_0), _t_0, {$: "Con", "head": _h_0, "tail": $$remove_one(_t_0, _x_0)});
  }
}

function $unsaid($0, $1, $2) {
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
        const _x_0 = $$has(_said_0, _h_0);
        const _x_1 = $$String_eq(_h_0, "--");
        $0 = _t_0;
        $1 = $$Bool_pick($$has(_said_0, _h_0), $$remove_one(_said_0, _h_0), _said_0);
        $2 = $$Bool_pick((_x_0 || _x_1), _acc_0, {$: "Con", "head": _h_0, "tail": _acc_0});
        continue;
      }
    }
  }
}

function $resumes(_arg_0) {
  return $has({$: "Con", "head": "-c", "tail": {$: "Con", "head": "--continue", "tail": {$: "Con", "head": "-r", "tail": {$: "Con", "head": "--resume", "tail": {$: "Nil"}}}}}, _arg_0);
}

function $chooses(_arg_0) {
  return $has({$: "Con", "head": "--session", "tail": {$: "Con", "head": "--fork", "tail": {$: "Con", "head": "--session-id", "tail": {$: "Nil"}}}}, _arg_0);
}

function $strip(_xs_0, _skip_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$resumes(_h_0);
    const _x_1 = $$chooses(_h_0);
    const _x_2 = (_x_0 || _x_1);
    return $keep_if($$Bool_not((_skip_0 || _x_2)), _h_0, $$strip(_t_0, $$Bool_and($$Bool_not(_skip_0), $$chooses(_h_0))));
  }
}

function $any_resumes(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$resumes(_h_0);
    const _x_1 = $$any_resumes(_t_0);
    return (_x_0 || _x_1);
  }
}

function $any_chooses(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = $$chooses(_h_0);
    const _x_1 = $$any_chooses(_t_0);
    return (_x_0 || _x_1);
  }
}

function $session_args(_session_0) {
  if (_session_0.$ === "None") {
    return {$: "Nil"};
  } else {
    const _file_0 = _session_0["value"];
    return {$: "Con", "head": "--session", "tail": {$: "Con", "head": _file_0, "tail": {$: "Nil"}}};
  }
}

function $restart_args(_rest_0, _said_0, _session_0) {
  return $List_append($$strip($$unsaid($$List_reverse(_rest_0), _said_0, {$: "Nil"}), false), $$session_args(_session_0));
}

function $hat() {
  return {$: "Con", "head": "         /\\         ", "tail": {$: "Con", "head": "        /  \\        ", "tail": {$: "Con", "head": "       / *  \\       ", "tail": {$: "Con", "head": "      /    . \\      ", "tail": {$: "Con", "head": "     /  *     \\     ", "tail": {$: "Con", "head": " ___/__________\\___ ", "tail": {$: "Con", "head": "(__________________)", "tail": {$: "Nil"}}}}}}}};
}

function $sparks() {
  return {$: "Con", "head": {$: "Spark", "row": 2, "col": 9, "frames": "*+*.  .*"}, "tail": {$: "Con", "head": {$: "Spark", "row": 3, "col": 11, "frames": ". .*+*. "}, "tail": {$: "Con", "head": {$: "Spark", "row": 4, "col": 8, "frames": "*.  .*+*"}, "tail": {$: "Con", "head": {$: "Spark", "row": 0, "col": 13, "frames": "  .*.   "}, "tail": {$: "Con", "head": {$: "Spark", "row": 1, "col": 5, "frames": "     .*."}, "tail": {$: "Con", "head": {$: "Spark", "row": 2, "col": 16, "frames": " .+.    "}, "tail": {$: "Nil"}}}}}}};
}

function $put(_s_0, _col_0, _c_0) {
  if (_s_0 === "") {
    return "";
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    if (_col_0 == 0) {
      return (_c_0 + _t_0);
    } else {
      const _p_0 = (_col_0 - 1);
      return (_h_0 + $$put(_t_0, _p_0, _c_0));
    }
  }
}

function $put_row(_rows_0, _row_0, _col_0, _c_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    if (_row_0 == 0) {
      return {$: "Con", "head": $$put(_h_0, _col_0, _c_0), "tail": _t_0};
    } else {
      const _p_0 = (_row_0 - 1);
      return {$: "Con", "head": _h_0, "tail": $$put_row(_t_0, _p_0, _col_0, _c_0)};
    }
  }
}

function $glyph(_found_0) {
  if (_found_0.$ === "None") {
    return " ";
  } else {
    const _c_0 = _found_0["value"];
    return _c_0;
  }
}

function $twinkle($0, $1, $2) {
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
        $1 = $$put_row(_rows_0, _row_0, _col_0, $$glyph($$String_get(_frames_0, _at_0)));
        $2 = _at_0;
        continue;
      }
    }
  }
}

function $hat_frame(_frame_0) {
  return $twinkle($$sparks(), $$hat(), $$Nat_mod(_frame_0, 8));
}

function $small_hat() {
  return {$: "Con", "head": "_/\\_   ", "tail": {$: "Con", "head": "_/\\_.  ", "tail": {$: "Con", "head": "_/\\_*  ", "tail": {$: "Con", "head": "_/\\_ + ", "tail": {$: "Con", "head": "_/\\_ * ", "tail": {$: "Con", "head": "_/\\_  .", "tail": {$: "Nil"}}}}}}};
}

function $widths(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": [...str_out(_h_0)].length, "tail": $$widths(_t_0)};
  }
}

function $inks() {
  return {$: "Con", "head": "accent", "tail": {$: "Con", "head": "mdLink", "tail": {$: "Con", "head": "dim", "tail": {$: "Con", "head": "text", "tail": {$: "Nil"}}}}};
}

function $ink_pick(_plus_0, _star_0, _dot_0) {
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

function $ink_of(_c_0) {
  return $ink_pick($$Char_is_eq(_c_0, "+"), $$Char_is_eq(_c_0, "*"), $$Char_is_eq(_c_0, "."));
}

function $ink(_part_0) {
  if (_part_0 === "") {
    return "accent";
  } else {
    const _h_0 = _part_0.slice(0, char_len(_part_0));
    return $ink_of(_h_0);
  }
}

function $is_sep(_c_0, _loose_0) {
  const _x_0 = $$Char_is_eq(_c_0, "_");
  const _x_1 = $$Char_is_eq(_c_0, "-");
  const _x_2 = $$Char_is_space(_c_0);
  const _x_3 = $$Bool_and(_loose_0, (_x_0 || _x_1));
  return (_x_2 || _x_3);
}

function $squash_put(_sep_0, _pending_0, _c_0, _acc_0) {
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

function $squash_go($0, $1, $2, $3, $4) {
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
        const _x_0 = $$Bool_not($$is_sep(_c_0, _loose_0));
        $0 = _t_0;
        $1 = _loose_0;
        $2 = (_started_0 || _x_0);
        $3 = $$Bool_and(_started_0, $$is_sep(_c_0, _loose_0));
        $4 = $$squash_put($$is_sep(_c_0, _loose_0), _pending_0, _c_0, _acc_0);
        continue;
      }
    }
  }
}

function $squash(_s_0, _loose_0) {
  return $squash_go(_s_0, _loose_0, false, false, "");
}

function $words(_text_0) {
  return $squash(_text_0, true);
}

function $mine(_title_0, _owner_0) {
  const _x_0 = $$String_eq(_title_0, _owner_0);
  const _x_1 = $$String_starts_with(_title_0, (_owner_0 + " "));
  return (_x_0 || _x_1);
}

function $title_pick(_titled_0, _native_0, _mine_0, _title_0, _name_0, _said_0, _owner_0) {
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

function $action_title(_title_0, _native_0, _name_0, _owner_0) {
  return $title_pick($$Bool_not($$String_is_empty(_title_0)), _native_0, $$mine($$words(_name_0), $$words(_owner_0)), _title_0, _name_0, $$words(_name_0), $$words(_owner_0));
}

function $fits($0, $1) {
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

function $clip_at(_s_0, _n_0) {
  if (_n_0 == 0) {
    return "";
  } else {
    const _p_0 = (_n_0 - 1);
    const _x_0 = $$String_take(_s_0, _p_0);
    return (_x_0 + "…");
  }
}

function $clip(_s_0, _n_0) {
  return $Bool_pick($$fits(_s_0, _n_0), _s_0, $$clip_at(_s_0, _n_0));
}

function $brief(_text_0) {
  const _line_0 = $$squash(_text_0, false);
  return $Bool_pick($$String_is_empty(_line_0), "\"\"", $$clip(_line_0, 72));
}

function $expand_put(_cr_0, _tab_0, _nl_0, _c_0, _pad_0, _acc_0) {
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

function $expand_go($0, $1, $2) {
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
        $2 = $$expand_put($$Char_is_eq(_c_0, "\r"), $$Char_is_eq(_c_0, "\t"), $$Char_is_eq(_c_0, "\n"), _c_0, _pad_0, _acc_0);
        continue;
      }
    }
  }
}

function $expand(_s_0, _pad_0) {
  return $expand_go(_s_0, _pad_0, "");
}

function $line_cur(_nl_0, _c_0, _cur_0) {
  if (_nl_0) {
    return "";
  } else {
    return (_c_0 + _cur_0);
  }
}

function $line_done(_nl_0, _cur_0, _done_0) {
  if (_nl_0) {
    return {$: "Con", "head": $$String_reverse(_cur_0), "tail": _done_0};
  } else {
    return _done_0;
  }
}

function $lines_go($0, $1, $2) {
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
        $1 = $$line_cur($$Char_is_eq(_c_0, "\n"), _c_0, _cur_0);
        $2 = $$line_done($$Char_is_eq(_c_0, "\n"), _cur_0, _done_0);
        continue;
      }
    }
  }
}

function $lines(_s_0) {
  return $lines_go(_s_0, "", {$: "Nil"});
}

function $first(_xs_0, _limit_0) {
  if (_xs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    if (_limit_0 == 0) {
      return {$: "Nil"};
    } else {
      const _p_0 = (_limit_0 - 1);
      return {$: "Con", "head": _h_0, "tail": $$first(_t_0, _p_0)};
    }
  }
}

function $count($0, $1) {
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

function $beyond($0, $1) {
  for (;;) {
    {
      const _xs_0 = $0;
      const _limit_0 = $1;
      if (_xs_0.$ === "Nil") {
        return 0;
      } else {
        const _t_0 = _xs_0["tail"];
        if (_limit_0 == 0) {
          return $count(_t_0, 1);
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

function $view_of(_expanded_0, _lines_0, _limit_0) {
  if (_expanded_0) {
    return {$: "View", "shown": _lines_0, "more": 0};
  } else {
    const _shown_0 = $$first(_lines_0, _limit_0);
    const _more_0 = $$beyond(_lines_0, _limit_0);
    return {$: "View", "shown": _shown_0, "more": _more_0};
  }
}

function $result_view(_output_0, _expanded_0) {
  return $view_of(_expanded_0, $$lines($$String_trim_end($$expand(_output_0, ""))), 10);
}

function $droppable(_drop_0) {
  return $without(_drop_0, {$: "Con", "head": "focus", "tail": {$: "Nil"}});
}

function $focus_active(_active_0, _drop_0, _take_0) {
  return $add_all(_take_0, $$without(_active_0, $$droppable(_drop_0)));
}

function $after_rtk(_rest_0) {
  if (_rest_0 === "") {
    return true;
  } else {
    const _h_0 = _rest_0.slice(0, char_len(_rest_0));
    return $Char_is_space(_h_0);
  }
}

function $rtk_skips(_raw_0, _command_0) {
  const _line_0 = $$String_trim_start(_command_0);
  const _x_0 = $$String_is_empty(_line_0);
  const _x_1 = $$Bool_and($$String_starts_with(_line_0, "rtk"), $$after_rtk($$String_drop(_line_0, 3)));
  const _x_2 = (_x_0 || _x_1);
  return (_raw_0 || _x_2);
}

function $last_said($0, $1) {
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

function $unprefixed(_line_0) {
  return $Bool_pick($$String_starts_with(_line_0, "wizardry: "), $$String_drop(_line_0, 10), _line_0);
}

function $update_line(_said_0) {
  return $unprefixed($$last_said($$String_lines(_said_0), "wizardry: the update did not say what happened"));
}

function $updated(_line_0) {
  return $String_starts_with(_line_0, "updated to");
}

function $asked_pick(_empty_0, _on_0, _off_0) {
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

function $update_asked(_word_0) {
  return $asked_pick($$String_is_empty(_word_0), $$String_eq(_word_0, "on"), $$String_eq(_word_0, "off"));
}

function $switch_act(_on_0, _loaded_0) {
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

function $listed(_actions_0) {
  if (_actions_0.$ === "Nil") {
    return "(none)";
  } else {
    const _h_0 = _actions_0["head"];
    const _t_0 = _actions_0["tail"];
    return $String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", ");
  }
}

function $label(_name_0, _state_0) {
  return $Bool_pick($$String_eq(_state_0, "active"), _name_0, $$String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " (", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}}}));
}

function $inspect_line(_name_0, _state_0, _source_0, _actions_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "] ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Con", "head": "\n  actions: ", "tail": {$: "Con", "head": $$listed(_actions_0), "tail": {$: "Nil"}}}}}}}});
}

function $loaded_text(_verb_0, _name_0, _state_0, _actions_0) {
  return $Bool_pick($$String_eq(_state_0, "pending"), $$String_concat({$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" [pending]: it injects a service nothing provides yet, and starts when one does.", "tail": {$: "Nil"}}}}}), $$String_concat({$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "]. Actions: ", "tail": {$: "Con", "head": $$listed(_actions_0), "tail": {$: "Nil"}}}}}}}}));
}

function $described(_description_0, _notes_0) {
  return $String_join({$: "Con", "head": _description_0, "tail": $$without(_notes_0, {$: "Con", "head": "", "tail": {$: "Nil"}})}, "\n\n");
}

function $base_prompt(_cwd_0, _date_0) {
  return $String_join({$: "Con", "head": "You are wizardry, an agent working in a terminal on the user's machine.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "The user states outcomes, often loosely, and may never have used a terminal. Act on the likeliest reading and say in a sentence what you took it to mean; ask first only when a wrong guess could not be undone. What only the user knows, leave as a marked blank. Answer in plain words: what now exists and how to use it.", "tail": {$: "Con", "head": "Everything you can do is a tool call. Tools are actions open to you, not procedures you owe anyone: take the ones that serve the outcome and leave the rest. Each comes from a plugin, and you can inspect, load, write and unload plugins while you work. No action waits for approval.", "tail": {$: "Con", "head": "When nothing you have does what is needed, make it (a script, an install, a plugin you write and load), and remove it afterwards unless it will be needed again. When an approach has failed twice, change the approach, not the wording.", "tail": {$: "Con", "head": "Independent work runs at the same time: calls in one step, parts given to agents of their own. Work that does not split is not split.", "tail": {$: "Con", "head": "Done means checked: run what you made, and say what you could not check. Add nothing the outcome does not need.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Working directory: " + _cwd_0), "tail": {$: "Con", "head": ("Date: " + _date_0), "tail": {$: "Nil"}}}}}}}}}}}, "\n");
}

function $system_prompt(_base_0, _identity_0) {
  return $Bool_pick($$String_is_empty(_identity_0), _base_0, $$String_concat({$: "Con", "head": _base_0, "tail": {$: "Con", "head": "\n\nWhat you have chosen to be:\n", "tail": {$: "Con", "head": _identity_0, "tail": {$: "Nil"}}}}));
}

function $among(_xs_0, _x_0) {
  return $has(_xs_0, _x_0);
}

function $first_said(_a_0, _b_0) {
  return $Bool_pick($$String_is_empty(_a_0), _b_0, _a_0);
}

function $home_pick(_chosen_0, _said_0, _moved_0, _home_0, _old_0) {
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

function $home_of(_chosen_0, _old_chosen_0, _home_0, _old_0, _has_home_0, _has_old_0) {
  return $home_pick($$Bool_not($$String_is_empty($$first_said(_chosen_0, _old_chosen_0))), $$first_said(_chosen_0, _old_chosen_0), $$Bool_and($$Bool_not(_has_home_0), _has_old_0), _home_0, _old_0);
}

function $adopts_home(_named_0, _has_home_0, _has_old_0, _old_is_link_0) {
  return $Bool_and($$Bool_not(_named_0), $$Bool_and($$Bool_not(_has_home_0), $$Bool_and(_has_old_0, $$Bool_not(_old_is_link_0))));
}

function $adopts_command(_invoked_0, _is_link_0, _has_command_0) {
  return $Bool_and($$String_eq(_invoked_0, "izardry"), $$Bool_and(_is_link_0, $$Bool_not(_has_command_0)));
}

function $moved_list(_home_0, _command_0) {
  return $List_append($$unless($$Bool_not(_home_0), {$: "Con", "head": "your plugins and sessions are now in ~/.wizardry", "tail": {$: "Nil"}}), $$unless($$Bool_not(_command_0), {$: "Con", "head": "the command is now `wizardry`", "tail": {$: "Nil"}}));
}

function $adopted_say(_moved_0) {
  if (_moved_0.$ === "Nil") {
    return {$: "None"};
  } else {
    const _h_0 = _moved_0["head"];
    const _t_0 = _moved_0["tail"];
    return {$: "Some", "value": $$String_concat({$: "Con", "head": "izardry is now wizardry: ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", and "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}})};
  }
}

function $adopted(_home_0, _command_0) {
  return $adopted_say($$moved_list(_home_0, _command_0));
}

function $plugin_dirs(_home_0, _cwd_0) {
  return $add({$: "Con", "head": _home_0, "tail": {$: "Nil"}}, _cwd_0);
}

function $under_home(_source_0) {
  return $Bool_pick($$String_starts_with(_source_0, "~/"), {$: "Some", "value": $$String_drop(_source_0, 2)}, {$: "None"});
}

function $is_builtin_source(_prefixed_0, _builtin_0, _exists_0) {
  const _x_0 = $$Bool_not(_exists_0);
  return $Bool_and(_builtin_0, (_prefixed_0 || _x_0));
}

function $nth($0, $1, $2) {
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

function $state_name(_n_0) {
  return $nth({$: "Con", "head": "pending", "tail": {$: "Con", "head": "loading", "tail": {$: "Con", "head": "active", "tail": {$: "Con", "head": "failed", "tail": {$: "Con", "head": "disposed", "tail": {$: "Con", "head": "unloading", "tail": {$: "Nil"}}}}}}}, _n_0, "unknown");
}

function $already_loaded(_name_0) {
  return $String_concat({$: "Con", "head": "plugin \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is already loaded; reload or unload it first", "tail": {$: "Nil"}}}});
}

function $not_loaded(_name_0) {
  return $String_concat({$: "Con", "head": "no plugin named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is loaded", "tail": {$: "Nil"}}}});
}

function $runs_on_it(_name_0, _verb_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is what this session runs on and cannot be ", "tail": {$: "Con", "head": _verb_0, "tail": {$: "Con", "head": " from inside it", "tail": {$: "Nil"}}}}}});
}

function $no_builtin(_name_0, _builtins_0) {
  return $String_concat({$: "Con", "head": "no builtin plugin named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"; builtins: ", "tail": {$: "Con", "head": $$String_join(_builtins_0, ", "), "tail": {$: "Nil"}}}}});
}

function $no_plugin_at(_path_0) {
  return ("no plugin at " + _path_0);
}

function $no_entry(_path_0) {
  return (_path_0 + " has no index.ts, index.js or package.json \"main\"");
}

function $load_failed(_source_0, _why_0) {
  return $String_concat({$: "Con", "head": _source_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": _why_0, "tail": {$: "Nil"}}}});
}

function $needs_execute(_name_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" needs an execute function", "tail": {$: "Nil"}}}});
}

function $already_registered(_name_0, _owner_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is already registered by plugin \"", "tail": {$: "Con", "head": _owner_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}}}});
}

function $no_action(_name_0) {
  return $String_concat({$: "Con", "head": "no action named \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}});
}

function $action_gone(_name_0) {
  return $String_concat({$: "Con", "head": "action \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" is gone: its plugin was unloaded", "tail": {$: "Nil"}}}});
}

function $command_gone(_name_0) {
  return $String_concat({$: "Con", "head": "/", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": " is gone: its plugin was unloaded", "tail": {$: "Nil"}}}});
}

function $no_such_actions(_names_0) {
  const _x_0 = $$String_join(_names_0, ", ");
  return ("no such action: " + _x_0);
}

function $unloaded_text(_name_0) {
  return $String_concat({$: "Con", "head": "Unloaded \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\".", "tail": {$: "Nil"}}}});
}

function $help() {
  return $String_join({$: "Con", "head": "wizardry - Pi on Cordis. Every plugin is a tool call; the agent chooses which to make.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Usage:", "tail": {$: "Con", "head": "  wizardry [options] [messages...]     Start a session (interactive unless -p)", "tail": {$: "Con", "head": "  wizardry plugins                     List loaded plugins and the actions they provide", "tail": {$: "Con", "head": "  wizardry update [on|off]             Update now, or turn automatic updates on or off", "tail": {$: "Con", "head": "  wizardry auth <command>              Log in or out (wizardry keeps its own logins, apart from Pi's)", "tail": {$: "Con", "head": "  wizardry export [folder]             Copy every conversation and memory to a folder you keep", "tail": {$: "Con", "head": "  wizardry delete <what> [--yes]       Delete conversations, memories, old (Pi's own setup) or all", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Options:", "tail": {$: "Con", "head": "  --plugin <name|path>   Load a plugin for this run (repeatable)", "tail": {$: "Con", "head": "  --gate                 Load the \"gate\" plugin: ask before bash, write, edit and plugin changes", "tail": {$: "Con", "head": "  --version, -v          Show the version", "tail": {$: "Con", "head": "  --help, -h             Show this help", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Every other option goes to Pi unchanged: --model, --thinking, -p/--print, -c/--continue,", "tail": {$: "Con", "head": "-r/--resume, --mode json|rpc, --no-session, and so on (see `pi --help`).", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Plugins load from ~/.wizardry/plugins/, ./.wizardry/plugins/, and ~/.wizardry/plugins.json.", "tail": {$: "Con", "head": "wizardry updates itself in the background whenever it can; /update off in a session stops that.", "tail": {$: "Con", "head": "Nothing asks for approval unless you pass --gate.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "wizardry is kept apart: its logins, settings, conversations and memories are all in ~/.wizardry,", "tail": {$: "Con", "head": "and nothing of Pi's own setup (~/.pi) or of a project's .pi folder is read. `wizardry delete`", "tail": {$: "Con", "head": "says what it would remove and removes nothing until you add --yes; it exports first.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}}}}}}}}}}, "\n");
}

function $pi_only_text(_first_0, _argv_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _first_0, "tail": {$: "Con", "head": "\" is a Pi command and wizardry does not use Pi's extensions or packages. Run `pi ", "tail": {$: "Con", "head": $$String_join(_argv_0, " "), "tail": {$: "Con", "head": "` instead.\n", "tail": {$: "Nil"}}}}}});
}

function $lists_plugins(_rest_0) {
  if (_rest_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _rest_0["head"];
    return $String_eq(_h_0, "plugins");
  }
}

function $listing_actions(_actions_0) {
  if (_actions_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _actions_0["head"];
    const _t_0 = _actions_0["tail"];
    return $String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", "), "tail": {$: "Con", "head": "\n", "tail": {$: "Nil"}}}});
  }
}

function $listing(_name_0, _state_0, _source_0, _actions_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": " [", "tail": {$: "Con", "head": _state_0, "tail": {$: "Con", "head": "] ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Con", "head": "\n", "tail": {$: "Con", "head": $$listing_actions(_actions_0), "tail": {$: "Nil"}}}}}}}});
}

function $switch_said(_on_0) {
  return $String_concat({$: "Con", "head": "Automatic updates are ", "tail": {$: "Con", "head": $$Bool_pick(_on_0, "on", "off"), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}});
}

function $at_file(_file_0) {
  return ("@" + _file_0);
}

function $at_files(_files_0) {
  if (_files_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _files_0["head"];
    const _t_0 = _files_0["tail"];
    return {$: "Con", "head": $$at_file(_h_0), "tail": $$at_files(_t_0)};
  }
}

function $said_of(_messages_0, _files_0) {
  return $List_append(_messages_0, $$at_files(_files_0));
}

function $restarts_now(_wanted_0, _attached_0, _tui_0, _idle_0) {
  return $Bool_and(_wanted_0, $$Bool_and(_attached_0, $$Bool_and(_tui_0, _idle_0)));
}

function $waits(_behind_0, _names_0, _called_0) {
  return $Bool_and($$has(_names_0, _behind_0), $$Bool_not($$has(_called_0, _behind_0)));
}

function $waiting(_ws_0, _names_0, _called_0) {
  if (_ws_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ws_0["head"];
    const _name_0 = _t_0["name"];
    const _behind_0 = _t_0["behind"];
    const _t_1 = _ws_0["tail"];
    return $keep_if($$waits(_behind_0, _names_0, _called_0), _name_0, $$waiting(_t_1, _names_0, _called_0));
  }
}

function $in_front(_bound_0, _known_0, _active_0, _returned_0, _waits_0) {
  if (!_bound_0) {
    return true;
  } else {
    const _x_0 = $$Bool_not(_known_0);
    return $Bool_pick((_x_0 || _returned_0), $$Bool_not(_waits_0), _active_0);
  }
}

function $last_of($0, $1) {
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

function $last_identity(_written_0) {
  return $last_of(_written_0, "");
}

function $tidy(_identity_0) {
  return $String_trim(_identity_0);
}

function $become_said(_identity_0) {
  return $Bool_pick($$String_is_empty(_identity_0), "Cleared.", "Set. It applies from the next turn.");
}

function $keep_starting(_word_0, _prefix_0, _rest_0) {
  return $keep_if($$String_starts_with(_word_0, _prefix_0), _word_0, _rest_0);
}

function $completions_go(_words_0, _prefix_0) {
  if (_words_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _words_0["head"];
    const _t_0 = _words_0["tail"];
    return $keep_starting(_h_0, _prefix_0, $$completions_go(_t_0, _prefix_0));
  }
}

function $completions(_words_0, _typed_0) {
  return $completions_go(_words_0, $$String_trim(_typed_0));
}

function $day(_iso_0) {
  return $String_take(_iso_0, 10);
}

function $focus_said(_active_0, _away_0) {
  return $String_concat({$: "Con", "head": "In front of you: ", "tail": {$: "Con", "head": $$String_join(_active_0, ", "), "tail": {$: "Con", "head": "\nPut away: ", "tail": {$: "Con", "head": $$listed(_away_0), "tail": {$: "Nil"}}}}});
}

function $think_levels() {
  return {$: "Con", "head": "off", "tail": {$: "Con", "head": "minimal", "tail": {$: "Con", "head": "low", "tail": {$: "Con", "head": "medium", "tail": {$: "Con", "head": "high", "tail": {$: "Con", "head": "xhigh", "tail": {$: "Con", "head": "max", "tail": {$: "Nil"}}}}}}}};
}

function $think_describe() {
  return $String_concat({$: "Con", "head": "Set how much reasoning you spend per step from here on: ", "tail": {$: "Con", "head": $$String_join($$think_levels(), ", "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}});
}

function $think_said(_level_0) {
  return ("Thinking level: " + _level_0);
}

function $kind_of(_managed_0) {
  return $Bool_pick(_managed_0, "install", "clone");
}

function $carried_on(_what_0) {
  return $String_concat({$: "Con", "head": "wizardry ", "tail": {$: "Con", "head": $$Maybe_default(_what_0, "updated"), "tail": {$: "Con", "head": "; this session carried on", "tail": {$: "Nil"}}}});
}

function $update_said(_line_0) {
  return ("wizardry: " + _line_0);
}

function $not_a_checkout(_app_0) {
  return (_app_0 + " is not a git checkout, so there is nothing to update from.");
}

function $rtk_pick(_ok_0, _out_0, _command_0) {
  return $Bool_pick($$Bool_and(_ok_0, $$Bool_and($$Bool_not($$String_is_empty(_out_0)), $$Bool_not($$String_eq(_out_0, _command_0)))), {$: "Some", "value": _out_0}, {$: "None"});
}

function $rtk_takes(_code_0, _out_0, _command_0) {
  const _x_0 = $$Nat_is_eq(_code_0, 0);
  const _x_1 = $$Nat_is_eq(_code_0, 3);
  return $rtk_pick((_x_0 || _x_1), $$String_trim(_out_0), _command_0);
}

function $in_dir(_dir_0, _file_0) {
  return $Bool_pick($$String_ends_with(_dir_0, "/"), (_dir_0 + _file_0), $$String_concat({$: "Con", "head": _dir_0, "tail": {$: "Con", "head": "/", "tail": {$: "Con", "head": _file_0, "tail": {$: "Nil"}}}}));
}

function $in_dirs(_dirs_0) {
  if (_dirs_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _dirs_0["head"];
    const _t_0 = _dirs_0["tail"];
    return $keep_if($$Bool_not($$String_is_empty(_h_0)), $$in_dir(_h_0, "rtk"), $$in_dirs(_t_0));
  }
}

function $rtk_places(_configured_0, _dirs_0, _home_0) {
  if (_configured_0.$ === "Some") {
    const _file_0 = _configured_0["value"];
    return {$: "Con", "head": _file_0, "tail": {$: "Nil"}};
  } else {
    return $List_append($$in_dirs(_dirs_0), {$: "Con", "head": "/opt/homebrew/bin/rtk", "tail": {$: "Con", "head": "/usr/local/bin/rtk", "tail": {$: "Con", "head": $$in_dir(_home_0, ".cargo/bin/rtk"), "tail": {$: "Con", "head": $$in_dir(_home_0, ".local/bin/rtk"), "tail": {$: "Nil"}}}}});
  }
}

function $rtk_missing(_configured_0) {
  if (_configured_0.$ === "Some") {
    const _file_0 = _configured_0["value"];
    return $String_concat({$: "Con", "head": "no rtk executable at ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": "; bash output stays unfiltered", "tail": {$: "Nil"}}}});
  } else {
    return "rtk is not installed (brew install rtk, or see https://github.com/rtk-ai/rtk); bash output stays unfiltered";
  }
}

function $gated() {
  return {$: "Con", "head": "bash", "tail": {$: "Con", "head": "write", "tail": {$: "Con", "head": "edit", "tail": {$: "Con", "head": "plugin_load", "tail": {$: "Con", "head": "plugin_unload", "tail": {$: "Con", "head": "plugin_reload", "tail": {$: "Nil"}}}}}}};
}

function $gate_summary(_params_0) {
  return $String_take(_params_0, (1500 ));
}

function $gate_asks(_title_0) {
  return $String_concat({$: "Con", "head": "Allow ", "tail": {$: "Con", "head": _title_0, "tail": {$: "Con", "head": "?", "tail": {$: "Nil"}}}});
}

function $gate_no_one(_name_0) {
  return $String_concat({$: "Con", "head": "\"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\" needs the user's approval and there is no one to ask in this mode", "tail": {$: "Nil"}}}});
}

function $gate_declined(_name_0) {
  return $String_concat({$: "Con", "head": "the user declined \"", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "\"", "tail": {$: "Nil"}}}});
}

function $emit(_count_0, _rest_0) {
  if (_count_0 == 0) {
    return _rest_0;
  } else {
    return {$: "Con", "head": _count_0, "tail": _rest_0};
  }
}

function $pack_go(_widths_0, _count_0, _used_0, _sep_0, _width_0) {
  if (_widths_0.$ === "Nil") {
    return $emit(_count_0, {$: "Nil"});
  } else {
    const _w_0 = _widths_0["head"];
    const _t_0 = _widths_0["tail"];
    const _x_0 = nat_chk(_sep_0 + _w_0);
    const _fits_0 = $$Bool_and($$Nat_is_gt(_count_0, 0), $$Nat_is_le(nat_chk(_used_0 + _x_0), _width_0));
    const _x_1 = nat_chk(_sep_0 + _w_0);
    return $emit($$Bool_pick(_fits_0, 0, _count_0), $$pack_go(_t_0, $$Bool_pick(_fits_0, nat_chk(_count_0 + 1), 1), $$Bool_pick(_fits_0, nat_chk(_used_0 + _x_1), _w_0), _sep_0, _width_0));
  }
}

function $pack(_widths_0, _sep_0, _width_0) {
  return $pack_go(_widths_0, 0, 0, _sep_0, _width_0);
}

function $layout_pick(_beside_0, _room_0, _under_0) {
  if (_beside_0) {
    return {$: "Beside", "room": _room_0};
  } else {
    return {$: "Under", "room": _under_0};
  }
}

function $layout(_width_0, _hat_width_0) {
  const _x_0 = nat_chk(4 + _hat_width_0);
  const _room_0 = (_width_0 < _x_0 ? 0 : _width_0 - _x_0);
  const _x_1 = (_width_0 < 1 ? 0 : _width_0 - 1);
  return $layout_pick($$Nat_is_ge(_room_0, 36), _room_0, (1 > _x_1 ? 1 : _x_1));
}

function $pad_end(_n_0, _xs_0, _fill_0) {
  if (_n_0 == 0) {
    return _xs_0;
  } else {
    const _p_0 = (_n_0 - 1);
    if (_xs_0.$ === "Nil") {
      return {$: "Con", "head": _fill_0, "tail": $$pad_end(_p_0, {$: "Nil"}, _fill_0)};
    } else {
      const _h_0 = _xs_0["head"];
      const _t_0 = _xs_0["tail"];
      return {$: "Con", "head": _h_0, "tail": $$pad_end(_p_0, _t_0, _fill_0)};
    }
  }
}

function $blanks(_n_0) {
  if (_n_0 == 0) {
    return {$: "Nil"};
  } else {
    const _p_0 = (_n_0 - 1);
    return {$: "Con", "head": "", "tail": $$blanks(_p_0)};
  }
}

function $beside_row(_left_0, _line_0) {
  return $Bool_pick($$String_is_empty(_line_0), _left_0, $$String_concat({$: "Con", "head": _left_0, "tail": {$: "Con", "head": "   ", "tail": {$: "Con", "head": _line_0, "tail": {$: "Nil"}}}}));
}

function $beside_zip(_lefts_0, _lines_0) {
  if (_lefts_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _lefts_0["head"];
    const _t_0 = _lefts_0["tail"];
    if (_lines_0.$ === "Nil") {
      return {$: "Con", "head": _h_0, "tail": $$beside_zip(_t_0, {$: "Nil"})};
    } else {
      const _l_0 = _lines_0["head"];
      const _lt_0 = _lines_0["tail"];
      return {$: "Con", "head": $$beside_row(_h_0, _l_0), "tail": $$beside_zip(_t_0, _lt_0)};
    }
  }
}

function $margined(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": (" " + _h_0), "tail": $$margined(_t_0)};
  }
}

function $header_beside(_hat_0, _lines_0, _hat_width_0) {
  const _x_0 = $$List_length(_hat_0);
  const _x_1 = $$List_length(_lines_0);
  const _tall_0 = (_x_0 > _x_1 ? _x_0 : _x_1);
  const _x_2 = $$List_length(_hat_0);
  const _x_3 = $$List_length(_lines_0);
  return $margined($$beside_zip($$pad_end(_tall_0, _hat_0, $$String_repeat(" ", _hat_width_0)), $$pad_end(_tall_0, $$List_append($$blanks((_x_2 < _x_3 ? 0 : _x_2 - _x_3)), _lines_0), "")));
}

function $header_under(_hat_0, _lines_0) {
  return $margined($$List_append(_hat_0, {$: "Con", "head": "", "tail": _lines_0}));
}

function $cap_moves(_viewport_0, _at_top_0) {
  return (_viewport_0 || _at_top_0);
}

function $next_frame(_frame_0) {
  return $Nat_mod(nat_chk(_frame_0 + 1), 8);
}

function $blank_lines(_shown_0) {
  if (_shown_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _shown_0["head"];
    const _t_0 = _shown_0["tail"];
    return $Bool_and($$String_is_empty(_h_0), $$List_is_empty(_t_0));
  }
}

function $blank_view(_shown_0, _more_0) {
  return $Bool_and($$blank_lines(_shown_0), $$Nat_is_eq(_more_0, 0));
}

function $more_hint(_more_0) {
  return $String_concat({$: "Con", "head": "... (", "tail": {$: "Con", "head": $$Nat_show(_more_0), "tail": {$: "Con", "head": " more lines,", "tail": {$: "Nil"}}}});
}

function $labels(_plugins_0) {
  if (_plugins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _plugins_0["head"];
    const _name_0 = _t_0["name"];
    const _state_0 = _t_0["state"];
    const _t_1 = _plugins_0["tail"];
    return {$: "Con", "head": $$label(_name_0, _state_0), "tail": $$labels(_t_1)};
  }
}

function $widest(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return 0;
  } else {
    const _h_0 = _xs_0["head"];
    const _t_0 = _xs_0["tail"];
    const _x_0 = [...str_out(_h_0)].length;
    const _x_1 = $$widest(_t_0);
    return (_x_0 > _x_1 ? _x_0 : _x_1);
  }
}

function $pad_right(_s_0, _n_0) {
  const _x_0 = [...str_out(_s_0)].length;
  const _x_1 = $$String_repeat(" ", (_n_0 < _x_0 ? 0 : _n_0 - _x_0));
  return (_s_0 + _x_1);
}

function $wide_rows(_plugins_0, _wide_0) {
  if (_plugins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _plugins_0["head"];
    const _name_0 = _t_0["name"];
    const _state_0 = _t_0["state"];
    const _source_0 = _t_0["source"];
    const _t_1 = _plugins_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": $$pad_right($$label(_name_0, _state_0), _wide_0), "tail": {$: "Con", "head": "  ", "tail": {$: "Con", "head": _source_0, "tail": {$: "Nil"}}}}}), "tail": $$wide_rows(_t_1, _wide_0)};
  }
}

function $plugin_rows(_plugins_0) {
  return $wide_rows(_plugins_0, $$widest($$labels(_plugins_0)));
}

function $plugin_line(_plugins_0) {
  return $String_join($$labels(_plugins_0), ", ");
}

function $indented(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _rows_0["head"];
    const _t_0 = _rows_0["tail"];
    return {$: "Con", "head": ("  " + _h_0), "tail": $$indented(_t_0)};
  }
}

function $shape() {
  return $String_join({$: "Con", "head": "A plugin is a .ts or .js file. The smallest one needs no imports:", "tail": {$: "Con", "head": "  export const name = \"weather\"", "tail": {$: "Con", "head": "  export const actions = [{", "tail": {$: "Con", "head": "    name: \"weather\", description: \"Current weather for a city.\",", "tail": {$: "Con", "head": "    parameters: { type: \"object\", properties: { city: { type: \"string\" } }, required: [\"city\"] },", "tail": {$: "Con", "head": "    async execute({ city }, env) { return \"text for the agent\" },   // env: { cwd, signal, update(text), pi (ExtensionContext) }", "tail": {$: "Con", "head": "  }]", "tail": {$: "Con", "head": "For lifecycle or services, export `apply(ctx, config)` (or a default function/class) and use the Cordis context:", "tail": {$: "Con", "head": "ctx.actions.register(action), ctx.on(event, listener), ctx.provide(name, value), `export const inject = [...]`.", "tail": {$: "Con", "head": "ctx.effect(setup) runs setup IMMEDIATELY and keeps its return value as the cleanup on unload; passing the cleanup itself undoes the setup at once.", "tail": {$: "Con", "head": "Events: action/registered, action/changed, action/unregistered, action/before (return a string to refuse the call), action/after, task/end,", "tail": {$: "Con", "head": "pi/ready (Pi's ExtensionAPI is live), pi/session-start (api, piCtx; per-session choices go here: api.setModel, api.setThinkingLevel).", "tail": {$: "Con", "head": "export (dir, wrote): `wizardry export` asks for a copy of what you keep; write <home>/<name>/ into <dir>/<name>/ and call wrote(one line).", "tail": {$: "Con", "head": "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.", "tail": {$: "Con", "head": "Everything a plugin registers is removed when it is unloaded.", "tail": {$: "Con", "head": "An action with `after: \"other\"` stays out of the agent's tool list until `other` has been called: give a skill one short action that explains it, and put the ones with long schemas after it.", "tail": {$: "Con", "head": "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.", "tail": {$: "Con", "head": "Before editing wizardry itself, call cordis_map: the map of the framework you run on.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}, "\n");
}

function $inspect_text(_lines_0, _idle_0) {
  const _x_0 = $$listed(_idle_0);
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "Loaded plugins:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": _lines_0, "tail": {$: "Con", "head": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Builtin plugins not loaded: " + _x_0), "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": $$shape(), "tail": {$: "Nil"}}}}}, "tail": {$: "Nil"}}}}), "\n");
}

function $no_map(_app_0) {
  return $String_concat({$: "Con", "head": "No AGENTS.md in ", "tail": {$: "Con", "head": _app_0, "tail": {$: "Con", "head": ". This wizardry predates it; the repo has it: https://github.com/Pomidium/wizardry", "tail": {$: "Nil"}}}});
}

function $own_pi(_home_0) {
  return (_home_0 + "/pi");
}

function $old_pi(_named_0, _userhome_0) {
  return $Bool_pick($$String_is_empty(_named_0), (_userhome_0 + "/.pi/agent"), _named_0);
}

function $pi_env(_home_0) {
  return {$: "Con", "head": {$: "Var", "name": "PI_CODING_AGENT_DIR", "value": $$own_pi(_home_0)}, "tail": {$: "Con", "head": {$: "Var", "name": "PI_SKIP_VERSION_CHECK", "value": "1"}, "tail": {$: "Con", "head": {$: "Var", "name": "PI_TELEMETRY", "value": "0"}, "tail": {$: "Nil"}}}};
}

function $pi_env_cleared() {
  return {$: "Con", "head": "PI_CODING_AGENT_SESSION_DIR", "tail": {$: "Con", "head": "PI_PACKAGE_DIR", "tail": {$: "Nil"}}};
}

function $var_names(_vars_0) {
  if (_vars_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _vars_0["head"];
    const _name_0 = _t_0["name"];
    const _t_1 = _vars_0["tail"];
    return {$: "Con", "head": _name_0, "tail": $$var_names(_t_1)};
  }
}

function $pi_env_touched() {
  return $List_append($$var_names($$pi_env("")), $$pi_env_cleared());
}

function $brought_files() {
  return {$: "Con", "head": "auth.json", "tail": {$: "Con", "head": "models.json", "tail": {$: "Nil"}}};
}

function $brought_settings() {
  return {$: "Con", "head": "defaultProvider", "tail": {$: "Con", "head": "defaultModel", "tail": {$: "Con", "head": "defaultThinkingLevel", "tail": {$: "Con", "head": "modelThinkingLevels", "tail": {$: "Con", "head": "enabledModels", "tail": {$: "Con", "head": "httpProxy", "tail": {$: "Con", "head": "shellPath", "tail": {$: "Con", "head": "shellCommandPrefix", "tail": {$: "Nil"}}}}}}}}};
}

function $pi_addons() {
  return {$: "Con", "head": "packages", "tail": {$: "Con", "head": "extensions", "tail": {$: "Con", "head": "skills", "tail": {$: "Con", "head": "prompts", "tail": {$: "Con", "head": "themes", "tail": {$: "Con", "head": "enableSkillCommands", "tail": {$: "Con", "head": "sessionDir", "tail": {$: "Con", "head": "defaultProjectTrust", "tail": {$: "Con", "head": "selfUpdateCommand", "tail": {$: "Nil"}}}}}}}}}};
}

function $settings_brought(_keys_0) {
  return $only(_keys_0, $$brought_settings());
}

function $brings(_has_own_0, _has_old_0, _old_0, _own_0) {
  return $Bool_and($$Bool_not(_has_own_0), $$Bool_and(_has_old_0, $$Bool_not($$String_eq(_old_0, _own_0))));
}

function $brought_list(_files_0) {
  if (_files_0.$ === "Nil") {
    return "There was nothing to bring over from ";
  } else {
    const _h_0 = _files_0["head"];
    const _t_0 = _files_0["tail"];
    return $String_concat({$: "Con", "head": "Brought over ", "tail": {$: "Con", "head": $$String_join({$: "Con", "head": _h_0, "tail": _t_0}, ", "), "tail": {$: "Con", "head": " from ", "tail": {$: "Nil"}}}});
  }
}

function $brought_said(_files_0, _own_0, _old_0) {
  return $String_concat({$: "Con", "head": "logins and settings are now its own, in ", "tail": {$: "Con", "head": _own_0, "tail": {$: "Con", "head": ". ", "tail": {$: "Con", "head": $$brought_list(_files_0), "tail": {$: "Con", "head": _old_0, "tail": {$: "Con", "head": ", which is no longer read: `wizardry delete old` removes it, and `wizardry auth login` signs in here.", "tail": {$: "Nil"}}}}}}});
}

function $with_slash(_dir_0) {
  return $Bool_pick($$String_ends_with(_dir_0, "/"), _dir_0, (_dir_0 + "/"));
}

function $inside(_path_0, _root_0) {
  const _x_0 = $$String_eq(_path_0, _root_0);
  const _x_1 = $$String_starts_with(_path_0, $$with_slash(_root_0));
  return (_x_0 || _x_1);
}

function $takes(_paths_0, _keep_0) {
  if (_paths_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    const _x_0 = $$inside(_keep_0, _h_0);
    const _x_1 = $$takes(_t_0, _keep_0);
    return (_x_0 || _x_1);
  }
}

function $sparing(_paths_0, _keep_0) {
  return $Bool_pick($$takes(_paths_0, _keep_0), {$: "Nil"}, _paths_0);
}

function $all_rooted(_paths_0) {
  if (_paths_0.$ === "Nil") {
    return true;
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    return $Bool_and($$String_starts_with(_h_0, "/"), $$all_rooted(_t_0));
  }
}

function $rooted(_paths_0) {
  return $Bool_pick($$all_rooted(_paths_0), _paths_0, {$: "Nil"});
}

function $parent_go(_rev_0) {
  if (_rev_0 === "") {
    return "";
  } else {
    const _h_0 = _rev_0.slice(0, char_len(_rev_0));
    const _t_0 = _rev_0.slice(char_len(_rev_0));
    return $Bool_pick($$Char_is_eq(_h_0, "/"), $$String_reverse(_t_0), $$parent_go(_t_0));
  }
}

function $parent(_path_0) {
  return $parent_go($$String_reverse(_path_0));
}

function $parents(_paths_0) {
  if (_paths_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _paths_0["head"];
    const _t_0 = _paths_0["tail"];
    return {$: "Con", "head": $$parent(_h_0), "tail": $$parents(_t_0)};
  }
}

function $sessions_dir(_home_0) {
  return $in_dir(_home_0, "sessions");
}

function $export_dir(_chosen_0, _userhome_0, _day_0, _again_0) {
  const _x_0 = $$Nat_show(nat_chk(_again_0 + 1));
  return $Bool_pick($$String_is_empty(_chosen_0), $$String_concat({$: "Con", "head": _userhome_0, "tail": {$: "Con", "head": "/wizardry-export-", "tail": {$: "Con", "head": _day_0, "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_again_0, 0), "", ("-" + _x_0)), "tail": {$: "Nil"}}}}}), _chosen_0);
}

function $origins(_home_0, _old_0) {
  return {$: "Con", "head": {$: "Origin", "name": "wizardry", "dir": $$sessions_dir(_home_0)}, "tail": {$: "Con", "head": {$: "Origin", "name": "pi", "dir": $$in_dir(_old_0, "sessions")}, "tail": {$: "Nil"}}};
}

function $origin_dirs(_origins_0) {
  if (_origins_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _origins_0["head"];
    const _dir_0 = _t_0["dir"];
    const _t_1 = _origins_0["tail"];
    return {$: "Con", "head": _dir_0, "tail": $$origin_dirs(_t_1)};
  }
}

function $export_fits(_dir_0, _home_0, _old_0) {
  return $Bool_not($$takes($$origin_dirs($$origins(_home_0, _old_0)), _dir_0));
}

function $is_conversation(_name_0) {
  return $String_ends_with(_name_0, ".jsonl");
}

function $conversation_to(_dir_0, _origin_0, _rel_0) {
  const _x_0 = $$String_concat({$: "Con", "head": "/conversations/", "tail": {$: "Con", "head": _origin_0, "tail": {$: "Con", "head": "/", "tail": {$: "Con", "head": _rel_0, "tail": {$: "Nil"}}}}});
  return (_dir_0 + _x_0);
}

function $readable(_path_0) {
  const _x_0 = [...str_out(_path_0)].length;
  const _x_1 = $$String_take(_path_0, (_x_0 < 6 ? 0 : _x_0 - 6));
  return $Bool_pick($$String_ends_with(_path_0, ".jsonl"), (_x_1 + ".md"), (_path_0 + ".md"));
}

function $minute(_stamp_0) {
  return $String_take(_stamp_0, 16);
}

function $transcript_head(_file_0, _cwd_0, _started_0) {
  return $String_concat({$: "Con", "head": "# Conversation of ", "tail": {$: "Con", "head": $$minute(_started_0), "tail": {$: "Con", "head": "\n\n- Directory: ", "tail": {$: "Con", "head": _cwd_0, "tail": {$: "Con", "head": "\n- Kept whole in: ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}}}});
}

function $voice_of(_kind_0) {
  return $Bool_pick($$String_eq(_kind_0, "user"), {$: "Said", "who": "User"}, $$Bool_pick($$String_eq(_kind_0, "assistant"), {$: "Said", "who": "Assistant"}, $$Bool_pick($$String_eq(_kind_0, "toolCall"), {$: "Call"}, $$Bool_pick($$String_eq(_kind_0, "toolResult"), {$: "Result"}, $$Bool_pick($$String_eq(_kind_0, "bashExecution"), {$: "Ran"}, $$Bool_pick($$String_eq(_kind_0, "image"), {$: "Image"}, $$Bool_pick($$has({$: "Con", "head": "compaction", "tail": {$: "Con", "head": "branch_summary", "tail": {$: "Nil"}}}, _kind_0), {$: "Said", "who": "Summary of what came before"}, $$Bool_pick($$String_eq(_kind_0, "custom_message"), {$: "Said", "who": "Note"}, $$Bool_pick($$String_eq(_kind_0, "error"), {$: "Said", "who": "Error"}, {$: "Silent"})))))))));
}

function $said_block(_who_0, _at_0, _body_0) {
  return $Bool_pick($$String_is_empty(_body_0), "", $$String_concat({$: "Con", "head": "## ", "tail": {$: "Con", "head": _who_0, "tail": {$: "Con", "head": " · ", "tail": {$: "Con", "head": $$minute(_at_0), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": _body_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}}}}));
}

function $more_lines(_more_0) {
  return $Bool_pick($$Nat_is_eq(_more_0, 0), "", $$String_concat({$: "Con", "head": "\n    ... ", "tail": {$: "Con", "head": $$Nat_show(_more_0), "tail": {$: "Con", "head": " more lines, in the .jsonl", "tail": {$: "Nil"}}}}));
}

function $shown_block(_view_0) {
  const _shown_0 = _view_0["shown"];
  const _more_0 = _view_0["more"];
  return $String_concat({$: "Con", "head": "    ", "tail": {$: "Con", "head": $$String_join(_shown_0, "\n    "), "tail": {$: "Con", "head": $$more_lines(_more_0), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}});
}

function $result_block(_text_0) {
  return $shown_block($$result_view(_text_0, false));
}

function $call_line(_name_0, _args_0) {
  return $String_concat({$: "Con", "head": "> **", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "** ", "tail": {$: "Con", "head": $$clip($$squash(_args_0, false), 200), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Nil"}}}}}});
}

function $piece_as(_voice_0, _name_0, _at_0, _text_0) {
  if (_voice_0.$ === "Said") {
    const _who_0 = _voice_0["who"];
    return $said_block(_who_0, _at_0, $$String_trim_end(_text_0));
  } else if (_voice_0.$ === "Call") {
    return $call_line(_name_0, _text_0);
  } else if (_voice_0.$ === "Result") {
    return $result_block(_text_0);
  } else if (_voice_0.$ === "Ran") {
    const _x_0 = $$call_line("$", _name_0);
    const _x_1 = $$result_block(_text_0);
    return (_x_0 + _x_1);
  } else if (_voice_0.$ === "Image") {
    return "*(an image)*\n\n";
  } else {
    return "";
  }
}

function $piece(_kind_0, _name_0, _at_0, _text_0) {
  return $piece_as($$voice_of(_kind_0), _name_0, _at_0, _text_0);
}

function $counted(_n_0, _one_0, _many_0) {
  return $String_concat({$: "Con", "head": $$Nat_show(_n_0), "tail": {$: "Con", "head": " ", "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_n_0, 1), _one_0, _many_0), "tail": {$: "Nil"}}}});
}

function $tally_lines(_tallies_0) {
  if (_tallies_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _tallies_0["head"];
    const _name_0 = _t_0["name"];
    const _from_0 = _t_0["from"];
    const _count_0 = _t_0["count"];
    const _t_1 = _tallies_0["tail"];
    return $keep_if($$Bool_not($$Nat_is_eq(_count_0, 0)), $$String_concat({$: "Con", "head": $$counted(_count_0, "conversation", "conversations"), "tail": {$: "Con", "head": " from ", "tail": {$: "Con", "head": _from_0, "tail": {$: "Con", "head": ", in conversations/", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "/", "tail": {$: "Nil"}}}}}}}), $$tally_lines(_t_1));
  }
}

function $bulleted(_lines_0) {
  if (_lines_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _lines_0["head"];
    const _t_0 = _lines_0["tail"];
    return {$: "Con", "head": ("- " + _h_0), "tail": $$bulleted(_t_0)};
  }
}

function $or_nothing(_lines_0) {
  if (_lines_0.$ === "Nil") {
    return {$: "Con", "head": "nothing: no conversation and no memory was found", "tail": {$: "Nil"}};
  } else {
    const _h_0 = _lines_0["head"];
    const _t_0 = _lines_0["tail"];
    return {$: "Con", "head": _h_0, "tail": _t_0};
  }
}

function $own_folders() {
  return {$: "Con", "head": "app", "tail": {$: "Con", "head": "plugins", "tail": {$: "Con", "head": "sessions", "tail": {$: "Con", "head": "pi", "tail": {$: "Con", "head": "update.lock", "tail": {$: "Con", "head": "tools", "tail": {$: "Con", "head": "bin", "tail": {$: "Nil"}}}}}}}};
}

function $left_over(_folders_0, _written_0) {
  return $without($$without(_folders_0, $$own_folders()), _written_0);
}

function $left_over_line(_name_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": "/ as it was kept: no loaded plugin exported it", "tail": {$: "Nil"}}});
}

function $export_lines(_tallies_0, _wrote_0) {
  return $or_nothing($$List_append($$tally_lines(_tallies_0), _wrote_0));
}

function $export_readme(_day_0, _lines_0) {
  return $String_concat({$: "Con", "head": "# wizardry export of ", "tail": {$: "Con", "head": _day_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": "Everything here is a copy: nothing was removed from where it was kept.\n\n", "tail": {$: "Con", "head": $$String_join($$bulleted(_lines_0), "\n"), "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": "Each conversation is here twice. The `.jsonl` is the session exactly as it was kept, and\n", "tail": {$: "Con", "head": "`wizardry --session <that file>` carries it on. The `.md` beside it is the same conversation\n", "tail": {$: "Con", "head": "as text to read.\n", "tail": {$: "Nil"}}}}}}}}}});
}

function $export_said(_dir_0, _lines_0) {
  return $String_concat({$: "Con", "head": "exported to ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": ":\n", "tail": {$: "Con", "head": $$String_join($$indented(_lines_0), "\n"), "tail": {$: "Con", "head": "\n", "tail": {$: "Nil"}}}}}});
}

function $export_inside(_dir_0) {
  return $String_concat({$: "Con", "head": "not exported: ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": " is inside the conversations it would copy. Name another folder.", "tail": {$: "Nil"}}}});
}

function $export_taken(_dir_0) {
  return $String_concat({$: "Con", "head": "not exported: ", "tail": {$: "Con", "head": _dir_0, "tail": {$: "Con", "head": " is not empty. Name a new folder, so that nothing in it is overwritten.", "tail": {$: "Nil"}}}});
}

function $export_broke(_why_0) {
  return ("the export did not finish: " + _why_0);
}

function $export_usage() {
  return "usage: wizardry export [folder]";
}

function $is_option(_arg_0) {
  return $String_starts_with(_arg_0, "-");
}

function $bare(_argv_0, _value_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    const _x_0 = $$is_option(_h_0);
    return $keep_if($$Bool_not((_value_0 || _x_0)), _h_0, $$bare(_t_0, $$Bool_and($$Bool_not(_value_0), $$String_eq(_h_0, "--to"))));
  }
}

function $options(_argv_0) {
  if (_argv_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $keep_if($$is_option(_h_0), _h_0, $$options(_t_0));
  }
}

function $first_of(_xs_0) {
  if (_xs_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _xs_0["head"];
    return _h_0;
  }
}

function $value_after(_argv_0, _flag_0) {
  if (_argv_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _argv_0["head"];
    const _t_0 = _argv_0["tail"];
    return $Bool_pick($$String_eq(_h_0, _flag_0), $$first_of(_t_0), $$value_after(_t_0, _flag_0));
  }
}

function $export_asked(_argv_0) {
  const _words_0 = $$bare(_argv_0, false);
  const _x_0 = $$List_length(_words_0);
  return $Bool_pick($$Bool_and($$List_is_empty($$options(_argv_0)), (_x_0 < 2)), {$: "Some", "value": $$first_of(_words_0)}, {$: "None"});
}

function $delete_asked(_argv_0) {
  const _words_0 = $$bare(_argv_0, false);
  const _x_0 = $$has(_argv_0, "--yes");
  const _x_1 = $$has(_argv_0, "-y");
  return {$: "Removal", "what": $$first_of(_words_0), "yes": (_x_0 || _x_1), "waived": $$has(_argv_0, "--no-export"), "to": $$value_after(_argv_0, "--to"), "clear": $$Bool_and($$Nat_is_eq($$List_length(_words_0), 1), $$covers({$: "Con", "head": "--yes", "tail": {$: "Con", "head": "-y", "tail": {$: "Con", "head": "--no-export", "tail": {$: "Con", "head": "--to", "tail": {$: "Nil"}}}}}, $$options(_argv_0)))};
}

function $what_pick(_conversations_0, _memories_0, _old_0, _all_0) {
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

function $what_of(_word_0) {
  return $what_pick($$String_eq(_word_0, "conversations"), $$String_eq(_word_0, "memories"), $$String_eq(_word_0, "old"), $$String_eq(_word_0, "all"));
}

function $old_wanted(_old_0, _home_0) {
  return $sparing($$Bool_pick($$inside(_old_0, _home_0), {$: "Nil"}, {$: "Con", "head": _old_0, "tail": {$: "Nil"}}), _home_0);
}

function $based(_home_0, _paths_0) {
  return $unless($$Bool_not($$String_starts_with(_home_0, "/")), _paths_0);
}

function $wanted(_what_0, _home_0, _old_0) {
  if (_what_0.$ === "Conversations") {
    return $based(_home_0, {$: "Con", "head": $$sessions_dir(_home_0), "tail": {$: "Nil"}});
  } else if (_what_0.$ === "Memories") {
    return $based(_home_0, {$: "Con", "head": $$in_dir(_home_0, "memory"), "tail": {$: "Nil"}});
  } else if (_what_0.$ === "Old") {
    return $based(_home_0, $$old_wanted(_old_0, _home_0));
  } else if (_what_0.$ === "All") {
    return $based(_home_0, {$: "Con", "head": _home_0, "tail": {$: "Nil"}});
  } else {
    return {$: "Nil"};
  }
}

function $doomed(_what_0, _home_0, _old_0, _userhome_0, _to_0) {
  return $sparing($$sparing($$rooted($$wanted(_what_0, _home_0, _old_0)), _userhome_0), _to_0);
}

function $goes(_paths_0, _yes_0, _exported_0) {
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

function $emptied(_what_0, _doomed_0, _userhome_0) {
  if (_what_0.$ === "Old") {
    return $sparing($$rooted($$parents(_doomed_0)), _userhome_0);
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

function $dangling(_links_0, _doomed_0) {
  if (_links_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _links_0["head"];
    const _path_0 = _t_0["path"];
    const _target_0 = _t_0["target"];
    const _t_1 = _links_0["tail"];
    return $keep_if($$takes(_doomed_0, _target_0), _path_0, $$dangling(_t_1, _doomed_0));
  }
}

function $link_dirs(_invoked_0, _named_0, _userhome_0) {
  return $without($$add($$add({$: "Con", "head": $$parent(_invoked_0), "tail": {$: "Nil"}}, _named_0), (_userhome_0 + "/.local/bin")), {$: "Con", "head": "", "tail": {$: "Nil"}});
}

function $old_home_link(_userhome_0) {
  return (_userhome_0 + "/.izardry");
}

function $delete_usage() {
  return $String_join({$: "Con", "head": "usage: wizardry delete <what> [--yes] [--to <folder>] [--no-export]", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "  conversations   every conversation wizardry has kept", "tail": {$: "Con", "head": "  memories        everything wizardry remembers", "tail": {$: "Con", "head": "  old             Pi's own setup, which wizardry no longer reads: its logins, settings,", "tail": {$: "Con", "head": "                  conversations, extensions and the pi program", "tail": {$: "Con", "head": "  all             all of wizardry: the program, its plugins, logins, conversations and memories", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "Without --yes it says what would be deleted and deletes nothing. With --yes it first exports", "tail": {$: "Con", "head": "every conversation and memory (to --to <folder>, else ~/wizardry-export-<day>), and deletes", "tail": {$: "Con", "head": "only once that is done; --no-export skips the export.", "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}}}}}}}}}}, "\n");
}

function $why_pick(_unknown_0, _based_0, _none_0, _loose_0, _home_0, _export_0, _old_0, _to_0) {
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

function $is_unknown(_what_0) {
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

function $why_not(_what_0, _home_0, _old_0, _userhome_0, _to_0) {
  const _paths_0 = $$wanted(_what_0, _home_0, _old_0);
  return $why_pick($$is_unknown(_what_0), $$String_starts_with(_home_0, "/"), $$List_is_empty(_paths_0), $$Bool_not($$all_rooted(_paths_0)), $$takes(_paths_0, _userhome_0), $$takes(_paths_0, _to_0), _old_0, _to_0);
}

function $size_text(_bytes_0) {
  const _x_0 = (1000 );
  const _x_1 = (1000000 );
  const _x_2 = $$Nat_show($$Nat_div(_bytes_0, (1000 )));
  const _x_3 = (1000000000 );
  const _x_4 = $$Nat_show($$Nat_div(_bytes_0, (1000000 )));
  const _x_5 = $$Nat_show($$Nat_div(_bytes_0, (1000000000 )));
  return $Bool_pick((_bytes_0 < _x_0), $$counted(_bytes_0, "byte", "bytes"), $$Bool_pick((_bytes_0 < _x_1), (_x_2 + " KB"), $$Bool_pick((_bytes_0 < _x_3), (_x_4 + " MB"), (_x_5 + " GB"))));
}

function $row_lines(_rows_0) {
  if (_rows_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _rows_0["head"];
    const _path_0 = _t_0["path"];
    const _bytes_0 = _t_0["bytes"];
    const _t_1 = _rows_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": _path_0, "tail": {$: "Con", "head": "  (", "tail": {$: "Con", "head": $$size_text(_bytes_0), "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}}}}), "tail": $$row_lines(_t_1)};
  }
}

function $link_lines(_links_0) {
  if (_links_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _links_0["head"];
    const _t_0 = _links_0["tail"];
    return {$: "Con", "head": $$String_concat({$: "Con", "head": "  ", "tail": {$: "Con", "head": _h_0, "tail": {$: "Con", "head": "  (a command that points into it)", "tail": {$: "Nil"}}}}), "tail": $$link_lines(_t_0)};
  }
}

function $export_line(_waived_0, _to_0, _first_0, _then_0) {
  if (_waived_0) {
    return "Nothing is exported first: you said --no-export.";
  } else {
    return $String_concat({$: "Con", "head": _first_0, "tail": {$: "Con", "head": _to_0, "tail": {$: "Con", "head": _then_0, "tail": {$: "Nil"}}}});
  }
}

function $delete_preview(_word_0, _rows_0, _links_0, _to_0, _waived_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": $$String_concat({$: "Con", "head": "wizardry delete ", "tail": {$: "Con", "head": _word_0, "tail": {$: "Con", "head": " would delete:", "tail": {$: "Nil"}}}}), "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$row_lines(_rows_0), "tail": {$: "Con", "head": $$link_lines(_links_0), "tail": {$: "Con", "head": {$: "Con", "head": $$export_line(_waived_0, _to_0, "First, every conversation and memory is exported to ", "."), "tail": {$: "Con", "head": $$String_concat({$: "Con", "head": "Nothing has been deleted. To go ahead: wizardry delete ", "tail": {$: "Con", "head": _word_0, "tail": {$: "Con", "head": " --yes", "tail": {$: "Con", "head": $$Bool_pick(_waived_0, " --no-export", ""), "tail": {$: "Nil"}}}}}), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}}, "tail": {$: "Nil"}}}}}), "\n");
}

function $deleted_said(_rows_0, _links_0, _to_0, _waived_0) {
  return $String_join($$List_concat({$: "Con", "head": {$: "Con", "head": "deleted:", "tail": {$: "Nil"}}, "tail": {$: "Con", "head": $$row_lines(_rows_0), "tail": {$: "Con", "head": $$link_lines(_links_0), "tail": {$: "Con", "head": {$: "Con", "head": $$export_line(_waived_0, _to_0, "Every conversation and memory was exported first, to ", "."), "tail": {$: "Con", "head": "", "tail": {$: "Nil"}}}, "tail": {$: "Nil"}}}}}), "\n");
}

function $nothing_there(_what_0) {
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

function $export_first_failed(_why_0) {
  return $String_concat({$: "Con", "head": "nothing was deleted: the export did not finish (", "tail": {$: "Con", "head": _why_0, "tail": {$: "Con", "head": "). Fix that, or pass --no-export to delete without one.", "tail": {$: "Nil"}}}});
}

function $setting(_name_0, _value_0) {
  return $Bool_pick($$String_is_empty(_value_0), {$: "Nil"}, {$: "Con", "head": {$: "Var", "name": _name_0, "value": _value_0}, "tail": {$: "Nil"}});
}

function $default_settings(_provider_0, _model_0, _thinking_0) {
  return $List_concat({$: "Con", "head": $$setting("defaultProvider", _provider_0), "tail": {$: "Con", "head": $$setting("defaultModel", _model_0), "tail": {$: "Con", "head": $$setting("defaultThinkingLevel", _thinking_0), "tail": {$: "Nil"}}}});
}

function $kept_off(_would_load_0, _loaded_0) {
  return $without(_would_load_0, _loaded_0);
}

function $or_unset(_value_0) {
  return $Bool_pick($$String_is_empty(_value_0), "as it was", _value_0);
}

function $default_said(_model_0, _thinking_0, _plugins_0) {
  return $String_concat({$: "Con", "head": "New sessions now start as this one. Model: ", "tail": {$: "Con", "head": $$or_unset(_model_0), "tail": {$: "Con", "head": ". Thinking: ", "tail": {$: "Con", "head": $$or_unset(_thinking_0), "tail": {$: "Con", "head": ". Plugins: ", "tail": {$: "Con", "head": $$String_join(_plugins_0, ", "), "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}}}}}});
}

function $minds() {
  return {$: "Con", "head": "defintire", "tail": {$: "Nil"}};
}

function $little() {
  return 240;
}

function $thought_of(_owner_0, _text_0) {
  const _x_0 = $$little();
  return $Bool_pick($$has($$minds(), _owner_0), $$clip($$String_trim(_text_0), nat_chk(5 * _x_0)), "");
}

function $minded(_base_0, _thought_0) {
  return $Bool_pick($$String_is_empty(_thought_0), _base_0, $$String_concat({$: "Con", "head": _base_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": _thought_0, "tail": {$: "Nil"}}}}));
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
const $$has = $has;
const $$Bool_not = $Bool_not;
const $$without = $without;
const $$only = $only;
const $$overlaps = $overlaps;
const $$List_append = $List_append;
const $$add = $add;
const $$covers = $covers;
const $$names = $names;
const $$without_named = $without_named;
const $$shipped_kept = $shipped_kept;
const $$Bool_and = $Bool_and;
const $$core_plugins = $core_plugins;
const $$String_ends_with = $String_ends_with;
const $$ends_with_any = $ends_with_any;
const $$Char_is_eq = $Char_is_eq;
const $$hidden = $hidden;
const $$Bool_pick = $Bool_pick;
const $$String_is_empty = $String_is_empty;
const $$String_reverse = $String_reverse;
const $$stem_go = $stem_go;
const $$pick_name = $pick_name;
const $$extras = $extras;
const $$passes = $passes;
const $$complete = $complete;
const $$unless = $unless;
const $$pi_bare = $pi_bare;
const $$pi_apart = $pi_apart;
const $$theme_args = $theme_args;
const $$remove_one = $remove_one;
const $$resumes = $resumes;
const $$chooses = $chooses;
const $$strip = $strip;
const $$any_resumes = $any_resumes;
const $$any_chooses = $any_chooses;
const $$List_reverse = $List_reverse;
const $$unsaid = $unsaid;
const $$session_args = $session_args;
const $$put = $put;
const $$put_row = $put_row;
const $$String_get = $String_get;
const $$glyph = $glyph;
const $$sparks = $sparks;
const $$hat = $hat;
const $$Nat_mod = $Nat_mod;
const $$widths = $widths;
const $$Char_is_space = $Char_is_space;
const $$is_sep = $is_sep;
const $$squash_put = $squash_put;
const $$String_starts_with = $String_starts_with;
const $$words = $words;
const $$mine = $mine;
const $$String_take = $String_take;
const $$fits = $fits;
const $$clip_at = $clip_at;
const $$squash = $squash;
const $$clip = $clip;
const $$expand_put = $expand_put;
const $$line_cur = $line_cur;
const $$line_done = $line_done;
const $$first = $first;
const $$beyond = $beyond;
const $$expand = $expand;
const $$String_trim_end = $String_trim_end;
const $$lines = $lines;
const $$droppable = $droppable;
const $$String_trim_start = $String_trim_start;
const $$String_drop = $String_drop;
const $$after_rtk = $after_rtk;
const $$String_lines = $String_lines;
const $$last_said = $last_said;
const $$String_concat = $String_concat;
const $$listed = $listed;
const $$first_said = $first_said;
const $$String_join = $String_join;
const $$moved_list = $moved_list;
const $$listing_actions = $listing_actions;
const $$at_file = $at_file;
const $$at_files = $at_files;
const $$waits = $waits;
const $$waiting = $waiting;
const $$completions_go = $completions_go;
const $$String_trim = $String_trim;
const $$think_levels = $think_levels;
const $$Maybe_default = $Maybe_default;
const $$Nat_is_eq = $Nat_is_eq;
const $$in_dir = $in_dir;
const $$in_dirs = $in_dirs;
const $$Nat_is_gt = $Nat_is_gt;
const $$Nat_is_le = $Nat_is_le;
const $$pack_go = $pack_go;
const $$Nat_is_ge = $Nat_is_ge;
const $$pad_end = $pad_end;
const $$blanks = $blanks;
const $$beside_zip = $beside_zip;
const $$beside_row = $beside_row;
const $$margined = $margined;
const $$List_length = $List_length;
const $$String_repeat = $String_repeat;
const $$List_is_empty = $List_is_empty;
const $$blank_lines = $blank_lines;
const $$Nat_show = $Nat_show;
const $$label = $label;
const $$labels = $labels;
const $$widest = $widest;
const $$pad_right = $pad_right;
const $$wide_rows = $wide_rows;
const $$indented = $indented;
const $$shape = $shape;
const $$List_concat = $List_concat;
const $$own_pi = $own_pi;
const $$var_names = $var_names;
const $$pi_env = $pi_env;
const $$pi_env_cleared = $pi_env_cleared;
const $$brought_settings = $brought_settings;
const $$brought_list = $brought_list;
const $$with_slash = $with_slash;
const $$inside = $inside;
const $$takes = $takes;
const $$all_rooted = $all_rooted;
const $$parent_go = $parent_go;
const $$parent = $parent;
const $$parents = $parents;
const $$sessions_dir = $sessions_dir;
const $$origin_dirs = $origin_dirs;
const $$origins = $origins;
const $$minute = $minute;
const $$more_lines = $more_lines;
const $$result_view = $result_view;
const $$call_line = $call_line;
const $$result_block = $result_block;
const $$voice_of = $voice_of;
const $$counted = $counted;
const $$tally_lines = $tally_lines;
const $$bulleted = $bulleted;
const $$own_folders = $own_folders;
const $$is_option = $is_option;
const $$bare = $bare;
const $$options = $options;
const $$first_of = $first_of;
const $$value_after = $value_after;
const $$old_wanted = $old_wanted;
const $$wanted = $wanted;
const $$rooted = $rooted;
const $$sparing = $sparing;
const $$dangling = $dangling;
const $$is_unknown = $is_unknown;
const $$Nat_div = $Nat_div;
const $$size_text = $size_text;
const $$row_lines = $row_lines;
const $$link_lines = $link_lines;
const $$export_line = $export_line;
const $$setting = $setting;
const $$or_unset = $or_unset;
const $$minds = $minds;
const $$little = $little;
const $$String_order = $String_order;
const $$Nat_show_put = $Nat_show_put;
const $$String_split = $String_split;
const $$String_join_go = $String_join_go;export default {
  "has": run_lib((a0,a1) => run_loop($has(a0,str_in(a1))), 2),
  "keep_if": run_lib((a0,a1,a2) => run_loop($keep_if(a0,str_in(a1),a2)), 3),
  "without": run_lib((a0,a1) => run_loop($without(a0,a1)), 2),
  "only": run_lib((a0,a1) => run_loop($only(a0,a1)), 2),
  "overlaps": run_lib((a0,a1) => run_loop($overlaps(a0,a1)), 2),
  "add": run_lib((a0,a1) => run_loop($add(a0,str_in(a1))), 2),
  "add_all": run_lib((a0,a1) => run_loop($add_all(a0,a1)), 2),
  "covers": run_lib((a0,a1) => run_loop($covers(a0,a1)), 2),
  "names": run_lib((a0) => run_loop($names(a0)), 1),
  "keep_entry": run_lib((a0,a1,a2) => run_loop($keep_entry(a0,a1,a2)), 3),
  "without_named": run_lib((a0,a1) => run_loop($without_named(a0,a1)), 2),
  "shipped_kept": run_lib((a0,a1) => run_loop($shipped_kept(a0,a1)), 2),
  "plan": run_lib((a0,a1,a2) => run_loop($plan(a0,a1,a2)), 3),
  "builtins_at_boot": run_lib((a0,a1) => run_loop($builtins_at_boot(a0,a1)), 2),
  "switched_off": run_lib((a0,a1) => run_loop($switched_off(a0,str_in(a1))), 2),
  "switched_on": run_lib((a0,a1) => run_loop($switched_on(a0,str_in(a1))), 2),
  "remembered": run_lib((a0,a1) => run_loop($remembered(a0,a1)), 2),
  "core_plugins": run_lib(() => run_loop($core_plugins()), 0),
  "is_core": run_lib((a0) => run_loop($is_core(str_in(a0))), 1),
  "restore_unloads": run_lib((a0,a1) => run_loop($restore_unloads(a0,a1)), 2),
  "ends_with_any": run_lib((a0,a1) => run_loop($ends_with_any(str_in(a0),a1)), 2),
  "hidden_char": run_lib((a0) => run_loop($hidden_char(str_in(a0))), 1),
  "hidden": run_lib((a0) => run_loop($hidden(str_in(a0))), 1),
  "usable": run_lib((a0,a1,a2) => run_loop($usable(str_in(a0),a1,a2)), 3),
  "stem_pick": run_lib((a0,a1,a2) => str_out(run_loop($stem_pick(a0,str_in(a1),str_in(a2)))), 3),
  "stem_go": run_lib((a0,a1) => str_out(run_loop($stem_go(str_in(a0),str_in(a1)))), 2),
  "stem": run_lib((a0) => str_out(run_loop($stem(str_in(a0)))), 1),
  "pick_name": run_lib((a0) => str_out(run_loop($pick_name(a0))), 1),
  "command_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($command_pick(a0,a1,a2,a3,a4,a5,a6)), 7),
  "command_of": run_lib((a0) => run_loop($command_of(str_in(a0))), 1),
  "extras_pick": run_lib((a0,a1,a2,a3,a4) => run_loop($extras_pick(a0,a1,a2,str_in(a3),a4)), 5),
  "extras": run_lib((a0,a1) => run_loop($extras(a0,a1)), 2),
  "passes_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => run_loop($passes_pick(a0,a1,a2,a3,str_in(a4),a5,a6)), 7),
  "passes": run_lib((a0,a1) => run_loop($passes(a0,a1)), 2),
  "complete_pick": run_lib((a0,a1,a2,a3) => run_loop($complete_pick(a0,a1,a2,a3)), 4),
  "complete": run_lib((a0,a1) => run_loop($complete(a0,a1)), 2),
  "split_args": run_lib((a0) => run_loop($split_args(a0)), 1),
  "unless": run_lib((a0,a1) => run_loop($unless(a0,a1)), 2),
  "theme_args": run_lib((a0,a1,a2) => run_loop($theme_args(a0,str_in(a1),str_in(a2))), 3),
  "pi_bare": run_lib(() => run_loop($pi_bare()), 0),
  "pi_apart": run_lib(() => run_loop($pi_apart()), 0),
  "pi_args": run_lib((a0,a1,a2,a3) => run_loop($pi_args(a0,str_in(a1),str_in(a2),str_in(a3))), 4),
  "remove_one": run_lib((a0,a1) => run_loop($remove_one(a0,str_in(a1))), 2),
  "unsaid": run_lib((a0,a1,a2) => run_loop($unsaid(a0,a1,a2)), 3),
  "resumes": run_lib((a0) => run_loop($resumes(str_in(a0))), 1),
  "chooses": run_lib((a0) => run_loop($chooses(str_in(a0))), 1),
  "strip": run_lib((a0,a1) => run_loop($strip(a0,a1)), 2),
  "any_resumes": run_lib((a0) => run_loop($any_resumes(a0)), 1),
  "any_chooses": run_lib((a0) => run_loop($any_chooses(a0)), 1),
  "session_args": run_lib((a0) => run_loop($session_args(a0)), 1),
  "restart_args": run_lib((a0,a1,a2) => run_loop($restart_args(a0,a1,a2)), 3),
  "hat": run_lib(() => run_loop($hat()), 0),
  "sparks": run_lib(() => run_loop($sparks()), 0),
  "put": run_lib((a0,a1,a2) => str_out(run_loop($put(str_in(a0),nat_in(a1),str_in(a2)))), 3),
  "put_row": run_lib((a0,a1,a2,a3) => run_loop($put_row(a0,nat_in(a1),nat_in(a2),str_in(a3))), 4),
  "glyph": run_lib((a0) => str_out(run_loop($glyph(a0))), 1),
  "twinkle": run_lib((a0,a1,a2) => run_loop($twinkle(a0,a1,nat_in(a2))), 3),
  "hat_frame": run_lib((a0) => run_loop($hat_frame(nat_in(a0))), 1),
  "small_hat": run_lib(() => run_loop($small_hat()), 0),
  "widths": run_lib((a0) => run_loop($widths(a0)), 1),
  "inks": run_lib(() => run_loop($inks()), 0),
  "ink_pick": run_lib((a0,a1,a2) => str_out(run_loop($ink_pick(a0,a1,a2))), 3),
  "ink_of": run_lib((a0) => str_out(run_loop($ink_of(str_in(a0)))), 1),
  "ink": run_lib((a0) => str_out(run_loop($ink(str_in(a0)))), 1),
  "is_sep": run_lib((a0,a1) => run_loop($is_sep(str_in(a0),a1)), 2),
  "squash_put": run_lib((a0,a1,a2,a3) => str_out(run_loop($squash_put(a0,a1,str_in(a2),str_in(a3)))), 4),
  "squash_go": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($squash_go(str_in(a0),a1,a2,a3,str_in(a4)))), 5),
  "squash": run_lib((a0,a1) => str_out(run_loop($squash(str_in(a0),a1))), 2),
  "words": run_lib((a0) => str_out(run_loop($words(str_in(a0)))), 1),
  "mine": run_lib((a0,a1) => run_loop($mine(str_in(a0),str_in(a1))), 2),
  "title_pick": run_lib((a0,a1,a2,a3,a4,a5,a6) => str_out(run_loop($title_pick(a0,a1,a2,str_in(a3),str_in(a4),str_in(a5),str_in(a6)))), 7),
  "action_title": run_lib((a0,a1,a2,a3) => str_out(run_loop($action_title(str_in(a0),a1,str_in(a2),str_in(a3)))), 4),
  "fits": run_lib((a0,a1) => run_loop($fits(str_in(a0),nat_in(a1))), 2),
  "clip_at": run_lib((a0,a1) => str_out(run_loop($clip_at(str_in(a0),nat_in(a1)))), 2),
  "clip": run_lib((a0,a1) => str_out(run_loop($clip(str_in(a0),nat_in(a1)))), 2),
  "brief": run_lib((a0) => str_out(run_loop($brief(str_in(a0)))), 1),
  "expand_put": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($expand_put(a0,a1,a2,str_in(a3),str_in(a4),str_in(a5)))), 6),
  "expand_go": run_lib((a0,a1,a2) => str_out(run_loop($expand_go(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "expand": run_lib((a0,a1) => str_out(run_loop($expand(str_in(a0),str_in(a1)))), 2),
  "line_cur": run_lib((a0,a1,a2) => str_out(run_loop($line_cur(a0,str_in(a1),str_in(a2)))), 3),
  "line_done": run_lib((a0,a1,a2) => run_loop($line_done(a0,str_in(a1),a2)), 3),
  "lines_go": run_lib((a0,a1,a2) => run_loop($lines_go(str_in(a0),str_in(a1),a2)), 3),
  "lines": run_lib((a0) => run_loop($lines(str_in(a0))), 1),
  "first": run_lib((a0,a1) => run_loop($first(a0,nat_in(a1))), 2),
  "count": run_lib((a0,a1) => run_loop($count(a0,nat_in(a1))), 2),
  "beyond": run_lib((a0,a1) => run_loop($beyond(a0,nat_in(a1))), 2),
  "view_of": run_lib((a0,a1,a2) => run_loop($view_of(a0,a1,nat_in(a2))), 3),
  "result_view": run_lib((a0,a1) => run_loop($result_view(str_in(a0),a1)), 2),
  "droppable": run_lib((a0) => run_loop($droppable(a0)), 1),
  "focus_active": run_lib((a0,a1,a2) => run_loop($focus_active(a0,a1,a2)), 3),
  "after_rtk": run_lib((a0) => run_loop($after_rtk(str_in(a0))), 1),
  "rtk_skips": run_lib((a0,a1) => run_loop($rtk_skips(a0,str_in(a1))), 2),
  "last_said": run_lib((a0,a1) => str_out(run_loop($last_said(a0,str_in(a1)))), 2),
  "unprefixed": run_lib((a0) => str_out(run_loop($unprefixed(str_in(a0)))), 1),
  "update_line": run_lib((a0) => str_out(run_loop($update_line(str_in(a0)))), 1),
  "updated": run_lib((a0) => run_loop($updated(str_in(a0))), 1),
  "asked_pick": run_lib((a0,a1,a2) => run_loop($asked_pick(a0,a1,a2)), 3),
  "update_asked": run_lib((a0) => run_loop($update_asked(str_in(a0))), 1),
  "switch_act": run_lib((a0,a1) => run_loop($switch_act(a0,a1)), 2),
  "listed": run_lib((a0) => str_out(run_loop($listed(a0))), 1),
  "label": run_lib((a0,a1) => str_out(run_loop($label(str_in(a0),str_in(a1)))), 2),
  "inspect_line": run_lib((a0,a1,a2,a3) => str_out(run_loop($inspect_line(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "loaded_text": run_lib((a0,a1,a2,a3) => str_out(run_loop($loaded_text(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "described": run_lib((a0,a1) => str_out(run_loop($described(str_in(a0),a1))), 2),
  "base_prompt": run_lib((a0,a1) => str_out(run_loop($base_prompt(str_in(a0),str_in(a1)))), 2),
  "system_prompt": run_lib((a0,a1) => str_out(run_loop($system_prompt(str_in(a0),str_in(a1)))), 2),
  "among": run_lib((a0,a1) => run_loop($among(a0,str_in(a1))), 2),
  "first_said": run_lib((a0,a1) => str_out(run_loop($first_said(str_in(a0),str_in(a1)))), 2),
  "home_pick": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($home_pick(a0,str_in(a1),a2,str_in(a3),str_in(a4)))), 5),
  "home_of": run_lib((a0,a1,a2,a3,a4,a5) => str_out(run_loop($home_of(str_in(a0),str_in(a1),str_in(a2),str_in(a3),a4,a5))), 6),
  "adopts_home": run_lib((a0,a1,a2,a3) => run_loop($adopts_home(a0,a1,a2,a3)), 4),
  "adopts_command": run_lib((a0,a1,a2) => run_loop($adopts_command(str_in(a0),a1,a2)), 3),
  "moved_list": run_lib((a0,a1) => run_loop($moved_list(a0,a1)), 2),
  "adopted_say": run_lib((a0) => run_loop($adopted_say(a0)), 1),
  "adopted": run_lib((a0,a1) => run_loop($adopted(a0,a1)), 2),
  "plugin_dirs": run_lib((a0,a1) => run_loop($plugin_dirs(str_in(a0),str_in(a1))), 2),
  "under_home": run_lib((a0) => run_loop($under_home(str_in(a0))), 1),
  "is_builtin_source": run_lib((a0,a1,a2) => run_loop($is_builtin_source(a0,a1,a2)), 3),
  "nth": run_lib((a0,a1,a2) => str_out(run_loop($nth(a0,nat_in(a1),str_in(a2)))), 3),
  "state_name": run_lib((a0) => str_out(run_loop($state_name(nat_in(a0)))), 1),
  "already_loaded": run_lib((a0) => str_out(run_loop($already_loaded(str_in(a0)))), 1),
  "not_loaded": run_lib((a0) => str_out(run_loop($not_loaded(str_in(a0)))), 1),
  "runs_on_it": run_lib((a0,a1) => str_out(run_loop($runs_on_it(str_in(a0),str_in(a1)))), 2),
  "no_builtin": run_lib((a0,a1) => str_out(run_loop($no_builtin(str_in(a0),a1))), 2),
  "no_plugin_at": run_lib((a0) => str_out(run_loop($no_plugin_at(str_in(a0)))), 1),
  "no_entry": run_lib((a0) => str_out(run_loop($no_entry(str_in(a0)))), 1),
  "load_failed": run_lib((a0,a1) => str_out(run_loop($load_failed(str_in(a0),str_in(a1)))), 2),
  "needs_execute": run_lib((a0) => str_out(run_loop($needs_execute(str_in(a0)))), 1),
  "already_registered": run_lib((a0,a1) => str_out(run_loop($already_registered(str_in(a0),str_in(a1)))), 2),
  "no_action": run_lib((a0) => str_out(run_loop($no_action(str_in(a0)))), 1),
  "action_gone": run_lib((a0) => str_out(run_loop($action_gone(str_in(a0)))), 1),
  "command_gone": run_lib((a0) => str_out(run_loop($command_gone(str_in(a0)))), 1),
  "no_such_actions": run_lib((a0) => str_out(run_loop($no_such_actions(a0))), 1),
  "unloaded_text": run_lib((a0) => str_out(run_loop($unloaded_text(str_in(a0)))), 1),
  "help": run_lib(() => str_out(run_loop($help())), 0),
  "pi_only_text": run_lib((a0,a1) => str_out(run_loop($pi_only_text(str_in(a0),a1))), 2),
  "lists_plugins": run_lib((a0) => run_loop($lists_plugins(a0)), 1),
  "listing_actions": run_lib((a0) => str_out(run_loop($listing_actions(a0))), 1),
  "listing": run_lib((a0,a1,a2,a3) => str_out(run_loop($listing(str_in(a0),str_in(a1),str_in(a2),a3))), 4),
  "switch_said": run_lib((a0) => str_out(run_loop($switch_said(a0))), 1),
  "at_file": run_lib((a0) => str_out(run_loop($at_file(str_in(a0)))), 1),
  "at_files": run_lib((a0) => run_loop($at_files(a0)), 1),
  "said_of": run_lib((a0,a1) => run_loop($said_of(a0,a1)), 2),
  "restarts_now": run_lib((a0,a1,a2,a3) => run_loop($restarts_now(a0,a1,a2,a3)), 4),
  "waits": run_lib((a0,a1,a2) => run_loop($waits(str_in(a0),a1,a2)), 3),
  "waiting": run_lib((a0,a1,a2) => run_loop($waiting(a0,a1,a2)), 3),
  "in_front": run_lib((a0,a1,a2,a3,a4) => run_loop($in_front(a0,a1,a2,a3,a4)), 5),
  "last_of": run_lib((a0,a1) => str_out(run_loop($last_of(a0,str_in(a1)))), 2),
  "last_identity": run_lib((a0) => str_out(run_loop($last_identity(a0))), 1),
  "tidy": run_lib((a0) => str_out(run_loop($tidy(str_in(a0)))), 1),
  "become_said": run_lib((a0) => str_out(run_loop($become_said(str_in(a0)))), 1),
  "keep_starting": run_lib((a0,a1,a2) => run_loop($keep_starting(str_in(a0),str_in(a1),a2)), 3),
  "completions_go": run_lib((a0,a1) => run_loop($completions_go(a0,str_in(a1))), 2),
  "completions": run_lib((a0,a1) => run_loop($completions(a0,str_in(a1))), 2),
  "day": run_lib((a0) => str_out(run_loop($day(str_in(a0)))), 1),
  "focus_said": run_lib((a0,a1) => str_out(run_loop($focus_said(a0,a1))), 2),
  "think_levels": run_lib(() => run_loop($think_levels()), 0),
  "think_describe": run_lib(() => str_out(run_loop($think_describe())), 0),
  "think_said": run_lib((a0) => str_out(run_loop($think_said(str_in(a0)))), 1),
  "kind_of": run_lib((a0) => str_out(run_loop($kind_of(a0))), 1),
  "carried_on": run_lib((a0) => str_out(run_loop($carried_on(a0))), 1),
  "update_said": run_lib((a0) => str_out(run_loop($update_said(str_in(a0)))), 1),
  "not_a_checkout": run_lib((a0) => str_out(run_loop($not_a_checkout(str_in(a0)))), 1),
  "rtk_pick": run_lib((a0,a1,a2) => run_loop($rtk_pick(a0,str_in(a1),str_in(a2))), 3),
  "rtk_takes": run_lib((a0,a1,a2) => run_loop($rtk_takes(nat_in(a0),str_in(a1),str_in(a2))), 3),
  "in_dir": run_lib((a0,a1) => str_out(run_loop($in_dir(str_in(a0),str_in(a1)))), 2),
  "in_dirs": run_lib((a0) => run_loop($in_dirs(a0)), 1),
  "rtk_places": run_lib((a0,a1,a2) => run_loop($rtk_places(a0,a1,str_in(a2))), 3),
  "rtk_missing": run_lib((a0) => str_out(run_loop($rtk_missing(a0))), 1),
  "gated": run_lib(() => run_loop($gated()), 0),
  "gate_summary": run_lib((a0) => str_out(run_loop($gate_summary(str_in(a0)))), 1),
  "gate_asks": run_lib((a0) => str_out(run_loop($gate_asks(str_in(a0)))), 1),
  "gate_no_one": run_lib((a0) => str_out(run_loop($gate_no_one(str_in(a0)))), 1),
  "gate_declined": run_lib((a0) => str_out(run_loop($gate_declined(str_in(a0)))), 1),
  "emit": run_lib((a0,a1) => run_loop($emit(nat_in(a0),a1)), 2),
  "pack_go": run_lib((a0,a1,a2,a3,a4) => run_loop($pack_go(a0,nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4))), 5),
  "pack": run_lib((a0,a1,a2) => run_loop($pack(a0,nat_in(a1),nat_in(a2))), 3),
  "layout_pick": run_lib((a0,a1,a2) => run_loop($layout_pick(a0,nat_in(a1),nat_in(a2))), 3),
  "layout": run_lib((a0,a1) => run_loop($layout(nat_in(a0),nat_in(a1))), 2),
  "pad_end": run_lib((a0,a1,a2) => run_loop($pad_end(nat_in(a0),a1,str_in(a2))), 3),
  "blanks": run_lib((a0) => run_loop($blanks(nat_in(a0))), 1),
  "beside_row": run_lib((a0,a1) => str_out(run_loop($beside_row(str_in(a0),str_in(a1)))), 2),
  "beside_zip": run_lib((a0,a1) => run_loop($beside_zip(a0,a1)), 2),
  "margined": run_lib((a0) => run_loop($margined(a0)), 1),
  "header_beside": run_lib((a0,a1,a2) => run_loop($header_beside(a0,a1,nat_in(a2))), 3),
  "header_under": run_lib((a0,a1) => run_loop($header_under(a0,a1)), 2),
  "cap_moves": run_lib((a0,a1) => run_loop($cap_moves(a0,a1)), 2),
  "next_frame": run_lib((a0) => run_loop($next_frame(nat_in(a0))), 1),
  "blank_lines": run_lib((a0) => run_loop($blank_lines(a0)), 1),
  "blank_view": run_lib((a0,a1) => run_loop($blank_view(a0,nat_in(a1))), 2),
  "more_hint": run_lib((a0) => str_out(run_loop($more_hint(nat_in(a0)))), 1),
  "labels": run_lib((a0) => run_loop($labels(a0)), 1),
  "widest": run_lib((a0) => run_loop($widest(a0)), 1),
  "pad_right": run_lib((a0,a1) => str_out(run_loop($pad_right(str_in(a0),nat_in(a1)))), 2),
  "wide_rows": run_lib((a0,a1) => run_loop($wide_rows(a0,nat_in(a1))), 2),
  "plugin_rows": run_lib((a0) => run_loop($plugin_rows(a0)), 1),
  "plugin_line": run_lib((a0) => str_out(run_loop($plugin_line(a0))), 1),
  "indented": run_lib((a0) => run_loop($indented(a0)), 1),
  "shape": run_lib(() => str_out(run_loop($shape())), 0),
  "inspect_text": run_lib((a0,a1) => str_out(run_loop($inspect_text(a0,a1))), 2),
  "no_map": run_lib((a0) => str_out(run_loop($no_map(str_in(a0)))), 1),
  "own_pi": run_lib((a0) => str_out(run_loop($own_pi(str_in(a0)))), 1),
  "old_pi": run_lib((a0,a1) => str_out(run_loop($old_pi(str_in(a0),str_in(a1)))), 2),
  "pi_env": run_lib((a0) => run_loop($pi_env(str_in(a0))), 1),
  "pi_env_cleared": run_lib(() => run_loop($pi_env_cleared()), 0),
  "var_names": run_lib((a0) => run_loop($var_names(a0)), 1),
  "pi_env_touched": run_lib(() => run_loop($pi_env_touched()), 0),
  "brought_files": run_lib(() => run_loop($brought_files()), 0),
  "brought_settings": run_lib(() => run_loop($brought_settings()), 0),
  "pi_addons": run_lib(() => run_loop($pi_addons()), 0),
  "settings_brought": run_lib((a0) => run_loop($settings_brought(a0)), 1),
  "brings": run_lib((a0,a1,a2,a3) => run_loop($brings(a0,a1,str_in(a2),str_in(a3))), 4),
  "brought_list": run_lib((a0) => str_out(run_loop($brought_list(a0))), 1),
  "brought_said": run_lib((a0,a1,a2) => str_out(run_loop($brought_said(a0,str_in(a1),str_in(a2)))), 3),
  "with_slash": run_lib((a0) => str_out(run_loop($with_slash(str_in(a0)))), 1),
  "inside": run_lib((a0,a1) => run_loop($inside(str_in(a0),str_in(a1))), 2),
  "takes": run_lib((a0,a1) => run_loop($takes(a0,str_in(a1))), 2),
  "sparing": run_lib((a0,a1) => run_loop($sparing(a0,str_in(a1))), 2),
  "all_rooted": run_lib((a0) => run_loop($all_rooted(a0)), 1),
  "rooted": run_lib((a0) => run_loop($rooted(a0)), 1),
  "parent_go": run_lib((a0) => str_out(run_loop($parent_go(str_in(a0)))), 1),
  "parent": run_lib((a0) => str_out(run_loop($parent(str_in(a0)))), 1),
  "parents": run_lib((a0) => run_loop($parents(a0)), 1),
  "sessions_dir": run_lib((a0) => str_out(run_loop($sessions_dir(str_in(a0)))), 1),
  "export_dir": run_lib((a0,a1,a2,a3) => str_out(run_loop($export_dir(str_in(a0),str_in(a1),str_in(a2),nat_in(a3)))), 4),
  "origins": run_lib((a0,a1) => run_loop($origins(str_in(a0),str_in(a1))), 2),
  "origin_dirs": run_lib((a0) => run_loop($origin_dirs(a0)), 1),
  "export_fits": run_lib((a0,a1,a2) => run_loop($export_fits(str_in(a0),str_in(a1),str_in(a2))), 3),
  "is_conversation": run_lib((a0) => run_loop($is_conversation(str_in(a0))), 1),
  "conversation_to": run_lib((a0,a1,a2) => str_out(run_loop($conversation_to(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "readable": run_lib((a0) => str_out(run_loop($readable(str_in(a0)))), 1),
  "minute": run_lib((a0) => str_out(run_loop($minute(str_in(a0)))), 1),
  "transcript_head": run_lib((a0,a1,a2) => str_out(run_loop($transcript_head(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "voice_of": run_lib((a0) => run_loop($voice_of(str_in(a0))), 1),
  "said_block": run_lib((a0,a1,a2) => str_out(run_loop($said_block(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "more_lines": run_lib((a0) => str_out(run_loop($more_lines(nat_in(a0)))), 1),
  "shown_block": run_lib((a0) => str_out(run_loop($shown_block(a0))), 1),
  "result_block": run_lib((a0) => str_out(run_loop($result_block(str_in(a0)))), 1),
  "call_line": run_lib((a0,a1) => str_out(run_loop($call_line(str_in(a0),str_in(a1)))), 2),
  "piece_as": run_lib((a0,a1,a2,a3) => str_out(run_loop($piece_as(a0,str_in(a1),str_in(a2),str_in(a3)))), 4),
  "piece": run_lib((a0,a1,a2,a3) => str_out(run_loop($piece(str_in(a0),str_in(a1),str_in(a2),str_in(a3)))), 4),
  "counted": run_lib((a0,a1,a2) => str_out(run_loop($counted(nat_in(a0),str_in(a1),str_in(a2)))), 3),
  "tally_lines": run_lib((a0) => run_loop($tally_lines(a0)), 1),
  "bulleted": run_lib((a0) => run_loop($bulleted(a0)), 1),
  "or_nothing": run_lib((a0) => run_loop($or_nothing(a0)), 1),
  "own_folders": run_lib(() => run_loop($own_folders()), 0),
  "left_over": run_lib((a0,a1) => run_loop($left_over(a0,a1)), 2),
  "left_over_line": run_lib((a0) => str_out(run_loop($left_over_line(str_in(a0)))), 1),
  "export_lines": run_lib((a0,a1) => run_loop($export_lines(a0,a1)), 2),
  "export_readme": run_lib((a0,a1) => str_out(run_loop($export_readme(str_in(a0),a1))), 2),
  "export_said": run_lib((a0,a1) => str_out(run_loop($export_said(str_in(a0),a1))), 2),
  "export_inside": run_lib((a0) => str_out(run_loop($export_inside(str_in(a0)))), 1),
  "export_taken": run_lib((a0) => str_out(run_loop($export_taken(str_in(a0)))), 1),
  "export_broke": run_lib((a0) => str_out(run_loop($export_broke(str_in(a0)))), 1),
  "export_usage": run_lib(() => str_out(run_loop($export_usage())), 0),
  "is_option": run_lib((a0) => run_loop($is_option(str_in(a0))), 1),
  "bare": run_lib((a0,a1) => run_loop($bare(a0,a1)), 2),
  "options": run_lib((a0) => run_loop($options(a0)), 1),
  "first_of": run_lib((a0) => str_out(run_loop($first_of(a0))), 1),
  "value_after": run_lib((a0,a1) => str_out(run_loop($value_after(a0,str_in(a1)))), 2),
  "export_asked": run_lib((a0) => run_loop($export_asked(a0)), 1),
  "delete_asked": run_lib((a0) => run_loop($delete_asked(a0)), 1),
  "what_pick": run_lib((a0,a1,a2,a3) => run_loop($what_pick(a0,a1,a2,a3)), 4),
  "what_of": run_lib((a0) => run_loop($what_of(str_in(a0))), 1),
  "old_wanted": run_lib((a0,a1) => run_loop($old_wanted(str_in(a0),str_in(a1))), 2),
  "based": run_lib((a0,a1) => run_loop($based(str_in(a0),a1)), 2),
  "wanted": run_lib((a0,a1,a2) => run_loop($wanted(a0,str_in(a1),str_in(a2))), 3),
  "doomed": run_lib((a0,a1,a2,a3,a4) => run_loop($doomed(a0,str_in(a1),str_in(a2),str_in(a3),str_in(a4))), 5),
  "goes": run_lib((a0,a1,a2) => run_loop($goes(a0,a1,a2)), 3),
  "emptied": run_lib((a0,a1,a2) => run_loop($emptied(a0,a1,str_in(a2))), 3),
  "dangling": run_lib((a0,a1) => run_loop($dangling(a0,a1)), 2),
  "link_dirs": run_lib((a0,a1,a2) => run_loop($link_dirs(str_in(a0),str_in(a1),str_in(a2))), 3),
  "old_home_link": run_lib((a0) => str_out(run_loop($old_home_link(str_in(a0)))), 1),
  "delete_usage": run_lib(() => str_out(run_loop($delete_usage())), 0),
  "why_pick": run_lib((a0,a1,a2,a3,a4,a5,a6,a7) => str_out(run_loop($why_pick(a0,a1,a2,a3,a4,a5,str_in(a6),str_in(a7)))), 8),
  "is_unknown": run_lib((a0) => run_loop($is_unknown(a0)), 1),
  "why_not": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($why_not(a0,str_in(a1),str_in(a2),str_in(a3),str_in(a4)))), 5),
  "size_text": run_lib((a0) => str_out(run_loop($size_text(nat_in(a0)))), 1),
  "row_lines": run_lib((a0) => run_loop($row_lines(a0)), 1),
  "link_lines": run_lib((a0) => run_loop($link_lines(a0)), 1),
  "export_line": run_lib((a0,a1,a2,a3) => str_out(run_loop($export_line(a0,str_in(a1),str_in(a2),str_in(a3)))), 4),
  "delete_preview": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($delete_preview(str_in(a0),a1,a2,str_in(a3),a4))), 5),
  "deleted_said": run_lib((a0,a1,a2,a3) => str_out(run_loop($deleted_said(a0,a1,str_in(a2),a3))), 4),
  "nothing_there": run_lib((a0) => str_out(run_loop($nothing_there(a0))), 1),
  "export_first_failed": run_lib((a0) => str_out(run_loop($export_first_failed(str_in(a0)))), 1),
  "setting": run_lib((a0,a1) => run_loop($setting(str_in(a0),str_in(a1))), 2),
  "default_settings": run_lib((a0,a1,a2) => run_loop($default_settings(str_in(a0),str_in(a1),str_in(a2))), 3),
  "kept_off": run_lib((a0,a1) => run_loop($kept_off(a0,a1)), 2),
  "or_unset": run_lib((a0) => str_out(run_loop($or_unset(str_in(a0)))), 1),
  "default_said": run_lib((a0,a1,a2) => str_out(run_loop($default_said(str_in(a0),str_in(a1),a2))), 3),
  "minds": run_lib(() => run_loop($minds()), 0),
  "little": run_lib(() => run_loop($little()), 0),
  "thought_of": run_lib((a0,a1) => str_out(run_loop($thought_of(str_in(a0),str_in(a1)))), 2),
  "minded": run_lib((a0,a1) => str_out(run_loop($minded(str_in(a0),str_in(a1)))), 2),
};
