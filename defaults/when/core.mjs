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

function $______bend_core_unless(_skip_0, _xs_0) {
  if (!_skip_0) {
    return _xs_0;
  } else {
    return {$: "Nil"};
  }
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
  return $String_join({$: "Con", "head": "You are wizardry, an agent working in a terminal on the user's machine.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": "The user states outcomes, often loosely, and may never have used a terminal. Act on the likeliest reading and say in a sentence what you took it to mean; ask first only when a wrong guess could not be undone: what stands in the way and can be put back as it was (a lock, a setting) is moved, put back, and said. What only the user knows, leave as a marked blank. What you make for them opens with a double-click (a page, a document) unless they ask for a program. Answer in plain words: what now exists and how to use it.", "tail": {$: "Con", "head": "Everything you can do is a tool call. Tools are actions open to you, not procedures you owe anyone: take the ones that serve the outcome and leave the rest. No action waits for approval.", "tail": {$: "Con", "head": "When nothing you have does what is needed, make it (a script, an install, or a plugin: `cordis_inspect` says how and brings the actions that load one), and remove it afterwards unless it will be needed again. When an approach has failed twice, change the approach, not the wording.", "tail": {$: "Con", "head": "Independent work runs at the same time: calls in one step, parts given to agents of their own. Work that does not split is not split.", "tail": {$: "Con", "head": "Done means checked: run what you made, and say what you could not check. Add nothing the outcome does not need.", "tail": {$: "Con", "head": "", "tail": {$: "Con", "head": ("Working directory: " + _cwd_0), "tail": {$: "Con", "head": ("Date: " + _date_0), "tail": {$: "Nil"}}}}}}}}}}}, "\n");
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

function $______bend_core_restarts_now(_wanted_0, _attached_0, _tui_0, _idle_0) {
  return $Bool_and(_wanted_0, $$Bool_and(_attached_0, $$Bool_and(_tui_0, _idle_0)));
}

function $______bend_core_waits(_behind_0, _names_0, _called_0) {
  return $Bool_and($$______bend_core_has(_names_0, _behind_0), $$Bool_not($$______bend_core_has(_called_0, _behind_0)));
}

function $______bend_core_waiting(_ws_0, _names_0, _called_0) {
  if (_ws_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _ws_0["head"];
    const _name_0 = _t_0["name"];
    const _behind_0 = _t_0["behind"];
    const _t_1 = _ws_0["tail"];
    return $______bend_core_keep_if($$______bend_core_waits(_behind_0, _names_0, _called_0), _name_0, $$______bend_core_waiting(_t_1, _names_0, _called_0));
  }
}

function $______bend_core_fails_after(_failed_0, _before_0) {
  if (_failed_0) {
    return nat_chk(_before_0 + 1);
  } else {
    return 0;
  }
}

function $______bend_core_walled(_fails_0, _said_0) {
  return $Bool_pick($$Nat_is_ge(_fails_0, 2), $$String_concat({$: "Con", "head": _said_0, "tail": {$: "Con", "head": "\n\nThis same call has now failed ", "tail": {$: "Con", "head": $$Nat_show(_fails_0), "tail": {$: "Con", "head": " times. Do not make it again unchanged: change the approach (another route, another tool, or make what is missing).", "tail": {$: "Nil"}}}}}), _said_0);
}

function $______bend_core_fs_describe(_name_0, _pi_0) {
  return $Bool_pick($$String_eq(_name_0, "edit"), "Edit a single file by exact text replacement.", $$Bool_pick($$String_eq(_name_0, "read"), "Read a file: text, or an image (jpg, png, gif, webp, bmp). Text is cut at 2000 lines or 50KB: continue with offset.", _pi_0));
}

function $______bend_core_in_front(_bound_0, _known_0, _active_0, _returned_0, _waits_0) {
  if (!_bound_0) {
    return true;
  } else {
    const _x_0 = $$Bool_not(_known_0);
    return $Bool_pick((_x_0 || _returned_0), $$Bool_not(_waits_0), _active_0);
  }
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

function $______bend_core_shape() {
  return $String_join({$: "Con", "head": "A plugin is a .ts or .js file. The smallest one needs no imports:", "tail": {$: "Con", "head": "  export const name = \"weather\"", "tail": {$: "Con", "head": "  export const actions = [{", "tail": {$: "Con", "head": "    name: \"weather\", description: \"Current weather for a city.\",", "tail": {$: "Con", "head": "    parameters: { type: \"object\", properties: { city: { type: \"string\" } }, required: [\"city\"] },", "tail": {$: "Con", "head": "    async execute({ city }, env) { return \"text for the agent\" },   // env: { cwd, signal, update(text), pi (ExtensionContext) }", "tail": {$: "Con", "head": "  }]", "tail": {$: "Con", "head": "For lifecycle or services, export `apply(ctx, config)` (or a default function/class) and use the Cordis context:", "tail": {$: "Con", "head": "ctx.actions.register(action), ctx.on(event, listener), ctx.provide(name, value), `export const inject = [...]`.", "tail": {$: "Con", "head": "ctx.effect(setup) runs setup IMMEDIATELY and keeps its return value as the cleanup on unload; passing the cleanup itself undoes the setup at once.", "tail": {$: "Con", "head": "Events: action/registered, action/changed, action/unregistered, action/before (return a string to refuse the call), action/after, task/end,", "tail": {$: "Con", "head": "pi/ready (Pi's ExtensionAPI is live), pi/session-start (api, piCtx; per-session choices go here: api.setModel, api.setThinkingLevel).", "tail": {$: "Con", "head": "export (dir, wrote): `wizardry export` asks for a copy of what you keep; write <home>/<name>/ into <dir>/<name>/ and call wrote(one line).", "tail": {$: "Con", "head": "Services (ctx.pi, ctx.actions, ctx.plugins) come through a tracing proxy: call their methods, but never patch, subclass or store them.", "tail": {$: "Con", "head": "Everything a plugin registers is removed when it is unloaded.", "tail": {$: "Con", "head": "An action with `after: \"other\"` stays out of the agent's tool list until `other` has been called: give a skill one short action that explains it, and put the ones with long schemas after it.", "tail": {$: "Con", "head": "The user sees a call named after the plugin, then the action (\"weather forecast\" for weather_forecast); an action can set `title` to name it differently.", "tail": {$: "Con", "head": "Before editing wizardry itself, call cordis_map: the map of the framework you run on.", "tail": {$: "Nil"}}}}}}}}}}}}}}}}}}}, "\n");
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

function $______bend_core_counted(_n_0, _one_0, _many_0) {
  return $String_concat({$: "Con", "head": $$Nat_show(_n_0), "tail": {$: "Con", "head": " ", "tail": {$: "Con", "head": $$Bool_pick($$Nat_is_eq(_n_0, 1), _one_0, _many_0), "tail": {$: "Nil"}}}});
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

function $______bend_core_minds() {
  return {$: "Con", "head": "defintire", "tail": {$: "Nil"}};
}

function $______bend_core_little() {
  return 240;
}

function $______bend_core_thought_of(_owner_0, _text_0) {
  const _x_0 = $$______bend_core_little();
  return $Bool_pick($$______bend_core_has($$______bend_core_minds(), _owner_0), $$______bend_core_clip($$String_trim(_text_0), nat_chk(5 * _x_0)), "");
}

function $______bend_core_minded(_base_0, _thought_0) {
  return $Bool_pick($$String_is_empty(_thought_0), _base_0, $$String_concat({$: "Con", "head": _base_0, "tail": {$: "Con", "head": "\n\n", "tail": {$: "Con", "head": _thought_0, "tail": {$: "Nil"}}}}));
}

function $is_word(_c_0, _cue_0) {
  const _x_0 = char_code(_c_0);
  const _x_1 = $$Char_is_alpha(_c_0);
  const _x_2 = $$Char_is_digit(_c_0);
  const _x_3 = (_x_0 === 42);
  const _x_4 = (_x_0 === 43);
  const _x_5 = (_x_0 >= 128);
  const _x_6 = $$Bool_and(_cue_0, (_x_3 || _x_4));
  const _x_7 = (_x_1 || _x_2);
  const _x_8 = (_x_5 || _x_6);
  return (_x_7 || _x_8);
}

function $push(_word_0, _acc_0) {
  if (_word_0 === "") {
    return _acc_0;
  } else {
    const _h_0 = _word_0.slice(0, char_len(_word_0));
    const _t_0 = _word_0.slice(char_len(_word_0));
    return {$: "Con", "head": $$String_reverse((_h_0 + _t_0)), "tail": _acc_0};
  }
}

function $words_go($0, $1, $2, $3) {
  for (;;) {
    {
      const _s_0 = $0;
      const _cue_0 = $1;
      const _word_0 = $2;
      const _acc_0 = $3;
      if (_s_0 === "") {
        return $List_reverse($$push(_word_0, _acc_0));
      } else {
        const _c_0 = _s_0.slice(0, char_len(_s_0));
        const _t_0 = _s_0.slice(char_len(_s_0));
        $0 = _t_0;
        $1 = _cue_0;
        $2 = $$Bool_pick($$is_word(_c_0, _cue_0), ($$Char_to_lower(_c_0) + _word_0), "");
        $3 = $$Bool_pick($$is_word(_c_0, _cue_0), _acc_0, $$push(_word_0, _acc_0));
        continue;
      }
    }
  }
}

function $words(_s_0, _cue_0) {
  return $words_go(_s_0, _cue_0, "", {$: "Nil"});
}

function $word_hits(_pat_0, _tok_0) {
  if (_pat_0 === "") {
    if (_tok_0 === "") {
      return true;
    } else {
      return false;
    }
  } else {
    const _p_0 = _pat_0.slice(0, char_len(_pat_0));
    const _pt_0 = _pat_0.slice(char_len(_pat_0));
    if (_tok_0 === "") {
      return $Char_is_eq(_p_0, "*");
    } else {
      const _h_1 = _tok_0.slice(0, char_len(_tok_0));
      const _t_1 = _tok_0.slice(char_len(_tok_0));
      const _x_0 = $$Char_is_eq(_p_0, "*");
      const _x_1 = $$Bool_and($$Char_is_eq(_p_0, _h_1), $$word_hits(_pt_0, _t_1));
      return (_x_0 || _x_1);
    }
  }
}

function $names(_pat_0, _tok_0) {
  if (_pat_0 === "") {
    return false;
  } else {
    const _p_0 = _pat_0.slice(0, char_len(_pat_0));
    const _pt_0 = _pat_0.slice(char_len(_pat_0));
    return $Bool_and($$Bool_not($$Char_is_eq(_p_0, "*")), $$word_hits((_p_0 + _pt_0), _tok_0));
  }
}

function $split_put(_plus_0, _h_0, _rest_0) {
  if (_plus_0) {
    return {$: "Con", "head": {$: "Nil"}, "tail": _rest_0};
  } else {
    if (_rest_0.$ === "Nil") {
      return {$: "Con", "head": {$: "Con", "head": _h_0, "tail": {$: "Nil"}}, "tail": {$: "Nil"}};
    } else {
      const _p_0 = _rest_0["head"];
      const _ps_0 = _rest_0["tail"];
      return {$: "Con", "head": {$: "Con", "head": _h_0, "tail": _p_0}, "tail": _ps_0};
    }
  }
}

function $phrases(_ws_0) {
  if (_ws_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _ws_0["head"];
    const _t_0 = _ws_0["tail"];
    return $split_put($$String_eq(_h_0, "+"), _h_0, $$phrases(_t_0));
  }
}

function $starts(_phrase_0, _toks_0) {
  if (_phrase_0.$ === "Nil") {
    return true;
  } else {
    const _p_0 = _phrase_0["head"];
    const _pt_0 = _phrase_0["tail"];
    if (_toks_0.$ === "Nil") {
      return false;
    } else {
      const _h_0 = _toks_0["head"];
      const _t_0 = _toks_0["tail"];
      return $Bool_and($$names(_p_0, _h_0), $$starts(_pt_0, _t_0));
    }
  }
}

function $occurs_go($0, $1, $2) {
  for (;;) {
    {
      const _toks_0 = $0;
      const _phrase_0 = $1;
      const _found_0 = $2;
      if (_toks_0.$ === "Nil") {
        return _found_0;
      } else {
        const _h_0 = _toks_0["head"];
        const _t_0 = _toks_0["tail"];
        const _x_0 = $$starts(_phrase_0, {$: "Con", "head": _h_0, "tail": _t_0});
        $0 = _t_0;
        $1 = _phrase_0;
        $2 = (_found_0 || _x_0);
        continue;
      }
    }
  }
}

function $occurs(_toks_0, _phrase_0) {
  return $occurs_go(_toks_0, _phrase_0, false);
}

function $all_occur($0, $1, $2) {
  for (;;) {
    {
      const _ps_0 = $0;
      const _toks_0 = $1;
      const _some_0 = $2;
      if (_ps_0.$ === "Nil") {
        return _some_0;
      } else {
        const _t_0 = _ps_0["head"];
        if (_t_0.$ === "Nil") {
          const _rest_0 = _ps_0["tail"];
          $0 = _rest_0;
          $1 = _toks_0;
          $2 = _some_0;
          continue;
        } else {
          const _w_0 = _t_0["head"];
          const _ws_0 = _t_0["tail"];
          const _rest_1 = _ps_0["tail"];
          return $Bool_and($$occurs(_toks_0, {$: "Con", "head": _w_0, "tail": _ws_0}), $$all_occur(_rest_1, _toks_0, true));
        }
      }
    }
  }
}

function $cue_hits(_cue_0, _toks_0) {
  return $all_occur($$phrases($$words(_cue_0, true)), _toks_0, false);
}

function $any_hits(_cues_0, _toks_0) {
  if (_cues_0.$ === "Nil") {
    return false;
  } else {
    const _h_0 = _cues_0["head"];
    const _t_0 = _cues_0["tail"];
    const _x_0 = $$cue_hits(_h_0, _toks_0);
    const _x_1 = $$any_hits(_t_0, _toks_0);
    return (_x_0 || _x_1);
  }
}

function $due_one(_fired_0, _hits_0, _name_0, _rest_0) {
  if (_fired_0) {
    return _rest_0;
  } else {
    if (!_hits_0) {
      return _rest_0;
    } else {
      return {$: "Con", "head": _name_0, "tail": _rest_0};
    }
  }
}

function $due_on(_rules_0, _fired_0, _toks_0) {
  if (_rules_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _t_0 = _rules_0["head"];
    const _name_0 = _t_0["name"];
    const _cues_0 = _t_0["cues"];
    const _t_1 = _rules_0["tail"];
    return $due_one($$______bend_core_has(_fired_0, _name_0), $$any_hits(_cues_0, _toks_0), _name_0, $$due_on(_t_1, _fired_0, _toks_0));
  }
}

function $due(_rules_0, _fired_0, _text_0) {
  return $due_on(_rules_0, _fired_0, $$words(_text_0, false));
}

function $first_line(_s_0, _n_0) {
  if (_s_0 === "") {
    return "";
  } else {
    const _h_0 = _s_0.slice(0, char_len(_s_0));
    const _t_0 = _s_0.slice(char_len(_s_0));
    if (_n_0 == 0) {
      return "";
    } else {
      const _p_0 = (_n_0 - 1);
      return $Bool_pick($$Char_is_eq(_h_0, "\n"), "", (_h_0 + $$first_line(_t_0, _p_0)));
    }
  }
}

function $doing_args(_args_0) {
  if (_args_0.$ === "Nil") {
    return "";
  } else {
    const _h_0 = _args_0["head"];
    const _t_0 = _args_0["tail"];
    const _x_0 = (" " + $$first_line(_h_0, (400 )));
    const _x_1 = $$doing_args(_t_0);
    return (_x_0 + _x_1);
  }
}

function $doing(_tool_0, _args_0) {
  const _x_0 = $$doing_args(_args_0);
  return (_tool_0 + _x_0);
}

function $with_output(_out_0) {
  if (_out_0 === "") {
    return "";
  } else {
    const _h_0 = _out_0.slice(0, char_len(_out_0));
    const _t_0 = _out_0.slice(char_len(_out_0));
    const _x_0 = $$______bend_core_clip((_h_0 + _t_0), (2000 ));
    return ("\n" + _x_0);
  }
}

function $note(_name_0, _then_0, _out_0) {
  return $String_concat({$: "Con", "head": "[when: ", "tail": {$: "Con", "head": _name_0, "tail": {$: "Con", "head": "] ", "tail": {$: "Con", "head": $$String_trim(_then_0), "tail": {$: "Con", "head": $$with_output($$String_trim(_out_0)), "tail": {$: "Nil"}}}}}});
}

function $told(_notes_0) {
  return $String_join(_notes_0, "\n");
}

function $held(_notes_0) {
  return $String_concat({$: "Con", "head": "Not run yet: a standing rule of the user's applies to this first.\n", "tail": {$: "Con", "head": $$told(_notes_0), "tail": {$: "Con", "head": "\nMake the call again with that in mind.", "tail": {$: "Nil"}}}});
}

function $also_held() {
  return "Not run: held with another call of this step, which a standing rule applied to. Read that one, then call again.";
}

function $teach_name() {
  return "when";
}

function $teach_cues() {
  return {$: "Con", "head": "every time", "tail": {$: "Con", "head": "everytime", "tail": {$: "Con", "head": "each time", "tail": {$: "Con", "head": "any time", "tail": {$: "Con", "head": "anytime", "tail": {$: "Con", "head": "whenever", "tail": {$: "Con", "head": "from now on", "tail": {$: "Con", "head": "always", "tail": {$: "Con", "head": "when you", "tail": {$: "Con", "head": "if you", "tail": {$: "Con", "head": "remember", "tail": {$: "Con", "head": "prefer*", "tail": {$: "Con", "head": "rule*", "tail": {$: "Nil"}}}}}}}}}}}}}};
}

function $teach(_file_0) {
  return $String_concat({$: "Con", "head": "If the user is stating a standing preference (\"whenever X, do Y\"), keep it as a rule in ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": ", a JSON list you edit with write/edit; it holds from the next step, in every session. A rule:\n", "tail": {$: "Con", "head": "{\"name\": \"blue-ui\", \"when\": {\"asked\": [\"ui\", \"website\", \"landing page\", \"component*\"], ", "tail": {$: "Con", "head": "\"doing\": [\"write + html\", \"write + css\", \"edit + tsx\"]}, \"then\": \"Make the UI blue.\", \"run\": \"\"}\n", "tail": {$: "Con", "head": "`when` holds cues per state: asked (the user's message), thinking (your own reasoning and replies), ", "tail": {$: "Con", "head": "doing (an action's name and the first line of each argument, before it runs), seen (an action's result). A cue is a phrase of whole words, ", "tail": {$: "Con", "head": "case ignored; `+` joins phrases that must all occur; a final `*` matches any ending. Any cue hitting fires the rule, ", "tail": {$: "Con", "head": "once per session: `then` is shown to you at that moment and at no other, with the output of the shell command `run` if set. ", "tail": {$: "Con", "head": "Choose cues wide enough to catch the situation however it is worded, and few states. ", "tail": {$: "Con", "head": "Do not keep the preference anywhere else. If the user is not stating one, ignore this.", "tail": {$: "Nil"}}}}}}}}}}}});
}

function $listed_one(_name_0, _then_0) {
  return $String_concat({$: "Con", "head": _name_0, "tail": {$: "Con", "head": ": ", "tail": {$: "Con", "head": $$______bend_core_clip($$String_trim(_then_0), 80), "tail": {$: "Nil"}}}});
}

function $listed(_file_0, _lines_0, _problem_0) {
  if (_lines_0.$ === "Nil") {
    if (_problem_0 === "") {
      return $String_concat({$: "Con", "head": "No rules yet. Tell the agent a preference (\"whenever you make a UI, make it blue\"), or edit ", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": ".", "tail": {$: "Nil"}}}});
    } else {
      const _h_0 = _problem_0.slice(0, char_len(_problem_0));
      const _t_0 = _problem_0.slice(char_len(_problem_0));
      return $String_concat({$: "Con", "head": _file_0, "tail": {$: "Con", "head": " cannot be read as a list of rules: ", "tail": {$: "Con", "head": (_h_0 + _t_0), "tail": {$: "Nil"}}}});
    }
  } else {
    const _h_1 = _lines_0["head"];
    const _t_1 = _lines_0["tail"];
    if (_problem_0 === "") {
      return $String_concat({$: "Con", "head": $$String_join({$: "Con", "head": _h_1, "tail": _t_1}, "\n"), "tail": {$: "Con", "head": "\n(", "tail": {$: "Con", "head": _file_0, "tail": {$: "Con", "head": ")", "tail": {$: "Nil"}}}}});
    } else {
      const _h_2 = _problem_0.slice(0, char_len(_problem_0));
      const _t_2 = _problem_0.slice(char_len(_problem_0));
      return $String_concat({$: "Con", "head": _file_0, "tail": {$: "Con", "head": " cannot be read as a list of rules: ", "tail": {$: "Con", "head": (_h_2 + _t_2), "tail": {$: "Nil"}}}});
    }
  }
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

function $List_reverse(_xs_0) {
  return $List_reverse_go(_xs_0, {$: "Nil"});
}

function $Char_is_space(_c_0) {
  const _x_0 = char_code(_c_0);
  const _x_1 = (_x_0 === 32);
  const _x_2 = $$Bool_and((_x_0 >= 9), (_x_0 <= 13));
  return (_x_1 || _x_2);
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

function $String_starts_with(_s_0, _p_0) {
  return $String_starts_with_go(_p_0, _s_0);
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

function $Nat_is_ge(_a_0, _b_0) {
  return $Cmp_is_ge(cmp_new(_a_0, _b_0));
}

function $Nat_show(_n_0) {
  const _m_0 = _n_0;
  return $Nat_show_fin(_m_0, "", $$Nat_show_put(nat_divmod(_m_0, 10)));
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

function $List_concat(_xss_0) {
  if (_xss_0.$ === "Nil") {
    return {$: "Nil"};
  } else {
    const _h_0 = _xss_0["head"];
    const _t_0 = _xss_0["tail"];
    return $List_append(_h_0, $$List_concat(_t_0));
  }
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

function $Char_to_lower(_c_0) {
  const _x_0 = char_code(_c_0);
  const _x_1 = $$Bool_to_u32($$Char_is_upper(_c_0));
  const _x_2 = (Math.imul(_x_1, 32) >>> 0);
  return char_new(((_x_0 + _x_2) >>> 0));
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

function $String_trim_end(_s_0) {
  return $String_reverse($$String_trim_start($$String_reverse(_s_0)));
}

function $Char_is_upper(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 65), (_x_0 <= 90));
}

function $Char_is_lower(_c_0) {
  const _x_0 = char_code(_c_0);
  return $Bool_and((_x_0 >= 97), (_x_0 <= 122));
}

function $Bool_to_u32(_b_0) {
  if (!_b_0) {
    return 0;
  } else {
    return 1;
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
const $$______bend_core_remove_one = $______bend_core_remove_one;
const $$______bend_core_resumes = $______bend_core_resumes;
const $$______bend_core_chooses = $______bend_core_chooses;
const $$______bend_core_strip = $______bend_core_strip;
const $$______bend_core_any_resumes = $______bend_core_any_resumes;
const $$______bend_core_any_chooses = $______bend_core_any_chooses;
const $$List_reverse = $List_reverse;
const $$______bend_core_unsaid = $______bend_core_unsaid;
const $$______bend_core_session_args = $______bend_core_session_args;
const $$Char_is_space = $Char_is_space;
const $$______bend_core_is_sep = $______bend_core_is_sep;
const $$______bend_core_squash_put = $______bend_core_squash_put;
const $$String_take = $String_take;
const $$______bend_core_fits = $______bend_core_fits;
const $$______bend_core_clip_at = $______bend_core_clip_at;
const $$______bend_core_squash = $______bend_core_squash;
const $$______bend_core_clip = $______bend_core_clip;
const $$______bend_core_line_cur = $______bend_core_line_cur;
const $$______bend_core_line_done = $______bend_core_line_done;
const $$______bend_core_droppable = $______bend_core_droppable;
const $$String_trim_start = $String_trim_start;
const $$String_starts_with = $String_starts_with;
const $$String_drop = $String_drop;
const $$______bend_core_after_rtk = $______bend_core_after_rtk;
const $$String_lines = $String_lines;
const $$______bend_core_last_said = $______bend_core_last_said;
const $$String_concat = $String_concat;
const $$______bend_core_listed = $______bend_core_listed;
const $$______bend_core_first_said = $______bend_core_first_said;
const $$______bend_core_unless = $______bend_core_unless;
const $$String_join = $String_join;
const $$______bend_core_moved_list = $______bend_core_moved_list;
const $$______bend_core_waits = $______bend_core_waits;
const $$______bend_core_waiting = $______bend_core_waiting;
const $$Nat_is_ge = $Nat_is_ge;
const $$Nat_show = $Nat_show;
const $$______bend_core_completions_go = $______bend_core_completions_go;
const $$String_trim = $String_trim;
const $$______bend_core_think_levels = $______bend_core_think_levels;
const $$Maybe_default = $Maybe_default;
const $$Nat_is_eq = $Nat_is_eq;
const $$______bend_core_in_dir = $______bend_core_in_dir;
const $$______bend_core_in_dirs = $______bend_core_in_dirs;
const $$______bend_core_shape = $______bend_core_shape;
const $$List_concat = $List_concat;
const $$______bend_core_own_pi = $______bend_core_own_pi;
const $$______bend_core_var_names = $______bend_core_var_names;
const $$______bend_core_pi_env = $______bend_core_pi_env;
const $$______bend_core_pi_env_cleared = $______bend_core_pi_env_cleared;
const $$______bend_core_brought_settings = $______bend_core_brought_settings;
const $$______bend_core_brought_list = $______bend_core_brought_list;
const $$______bend_core_bulleted = $______bend_core_bulleted;
const $$______bend_core_setting = $______bend_core_setting;
const $$______bend_core_or_unset = $______bend_core_or_unset;
const $$______bend_core_minds = $______bend_core_minds;
const $$______bend_core_little = $______bend_core_little;
const $$Char_is_alpha = $Char_is_alpha;
const $$Char_is_digit = $Char_is_digit;
const $$push = $push;
const $$is_word = $is_word;
const $$Char_to_lower = $Char_to_lower;
const $$word_hits = $word_hits;
const $$phrases = $phrases;
const $$names = $names;
const $$starts = $starts;
const $$occurs = $occurs;
const $$all_occur = $all_occur;
const $$words = $words;
const $$cue_hits = $cue_hits;
const $$any_hits = $any_hits;
const $$due_on = $due_on;
const $$first_line = $first_line;
const $$doing_args = $doing_args;
const $$with_output = $with_output;
const $$told = $told;
const $$String_order = $String_order;
const $$Nat_show_put = $Nat_show_put;
const $$Char_is_upper = $Char_is_upper;
const $$Char_is_lower = $Char_is_lower;
const $$Bool_to_u32 = $Bool_to_u32;
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
  "../../bend/core:unless": run_lib((a0,a1) => run_loop($______bend_core_unless(a0,a1)), 2),
  "../../bend/core:remove_one": run_lib((a0,a1) => run_loop($______bend_core_remove_one(a0,str_in(a1))), 2),
  "../../bend/core:unsaid": run_lib((a0,a1,a2) => run_loop($______bend_core_unsaid(a0,a1,a2)), 3),
  "../../bend/core:resumes": run_lib((a0) => run_loop($______bend_core_resumes(str_in(a0))), 1),
  "../../bend/core:chooses": run_lib((a0) => run_loop($______bend_core_chooses(str_in(a0))), 1),
  "../../bend/core:strip": run_lib((a0,a1) => run_loop($______bend_core_strip(a0,a1)), 2),
  "../../bend/core:any_resumes": run_lib((a0) => run_loop($______bend_core_any_resumes(a0)), 1),
  "../../bend/core:any_chooses": run_lib((a0) => run_loop($______bend_core_any_chooses(a0)), 1),
  "../../bend/core:session_args": run_lib((a0) => run_loop($______bend_core_session_args(a0)), 1),
  "../../bend/core:restart_args": run_lib((a0,a1,a2) => run_loop($______bend_core_restart_args(a0,a1,a2)), 3),
  "../../bend/core:is_sep": run_lib((a0,a1) => run_loop($______bend_core_is_sep(str_in(a0),a1)), 2),
  "../../bend/core:squash_put": run_lib((a0,a1,a2,a3) => str_out(run_loop($______bend_core_squash_put(a0,a1,str_in(a2),str_in(a3)))), 4),
  "../../bend/core:squash_go": run_lib((a0,a1,a2,a3,a4) => str_out(run_loop($______bend_core_squash_go(str_in(a0),a1,a2,a3,str_in(a4)))), 5),
  "../../bend/core:squash": run_lib((a0,a1) => str_out(run_loop($______bend_core_squash(str_in(a0),a1))), 2),
  "../../bend/core:fits": run_lib((a0,a1) => run_loop($______bend_core_fits(str_in(a0),nat_in(a1))), 2),
  "../../bend/core:clip_at": run_lib((a0,a1) => str_out(run_loop($______bend_core_clip_at(str_in(a0),nat_in(a1)))), 2),
  "../../bend/core:clip": run_lib((a0,a1) => str_out(run_loop($______bend_core_clip(str_in(a0),nat_in(a1)))), 2),
  "../../bend/core:brief": run_lib((a0) => str_out(run_loop($______bend_core_brief(str_in(a0)))), 1),
  "../../bend/core:line_cur": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_line_cur(a0,str_in(a1),str_in(a2)))), 3),
  "../../bend/core:line_done": run_lib((a0,a1,a2) => run_loop($______bend_core_line_done(a0,str_in(a1),a2)), 3),
  "../../bend/core:lines_go": run_lib((a0,a1,a2) => run_loop($______bend_core_lines_go(str_in(a0),str_in(a1),a2)), 3),
  "../../bend/core:lines": run_lib((a0) => run_loop($______bend_core_lines(str_in(a0))), 1),
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
  "../../bend/core:restarts_now": run_lib((a0,a1,a2,a3) => run_loop($______bend_core_restarts_now(a0,a1,a2,a3)), 4),
  "../../bend/core:waits": run_lib((a0,a1,a2) => run_loop($______bend_core_waits(str_in(a0),a1,a2)), 3),
  "../../bend/core:waiting": run_lib((a0,a1,a2) => run_loop($______bend_core_waiting(a0,a1,a2)), 3),
  "../../bend/core:fails_after": run_lib((a0,a1) => run_loop($______bend_core_fails_after(a0,nat_in(a1))), 2),
  "../../bend/core:walled": run_lib((a0,a1) => str_out(run_loop($______bend_core_walled(nat_in(a0),str_in(a1)))), 2),
  "../../bend/core:fs_describe": run_lib((a0,a1) => str_out(run_loop($______bend_core_fs_describe(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:in_front": run_lib((a0,a1,a2,a3,a4) => run_loop($______bend_core_in_front(a0,a1,a2,a3,a4)), 5),
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
  "../../bend/core:counted": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_counted(nat_in(a0),str_in(a1),str_in(a2)))), 3),
  "../../bend/core:bulleted": run_lib((a0) => run_loop($______bend_core_bulleted(a0)), 1),
  "../../bend/core:setting": run_lib((a0,a1) => run_loop($______bend_core_setting(str_in(a0),str_in(a1))), 2),
  "../../bend/core:default_settings": run_lib((a0,a1,a2) => run_loop($______bend_core_default_settings(str_in(a0),str_in(a1),str_in(a2))), 3),
  "../../bend/core:kept_off": run_lib((a0,a1) => run_loop($______bend_core_kept_off(a0,a1)), 2),
  "../../bend/core:or_unset": run_lib((a0) => str_out(run_loop($______bend_core_or_unset(str_in(a0)))), 1),
  "../../bend/core:default_said": run_lib((a0,a1,a2) => str_out(run_loop($______bend_core_default_said(str_in(a0),str_in(a1),a2))), 3),
  "../../bend/core:minds": run_lib(() => run_loop($______bend_core_minds()), 0),
  "../../bend/core:little": run_lib(() => run_loop($______bend_core_little()), 0),
  "../../bend/core:thought_of": run_lib((a0,a1) => str_out(run_loop($______bend_core_thought_of(str_in(a0),str_in(a1)))), 2),
  "../../bend/core:minded": run_lib((a0,a1) => str_out(run_loop($______bend_core_minded(str_in(a0),str_in(a1)))), 2),
  "is_word": run_lib((a0,a1) => run_loop($is_word(str_in(a0),a1)), 2),
  "push": run_lib((a0,a1) => run_loop($push(str_in(a0),a1)), 2),
  "words_go": run_lib((a0,a1,a2,a3) => run_loop($words_go(str_in(a0),a1,str_in(a2),a3)), 4),
  "words": run_lib((a0,a1) => run_loop($words(str_in(a0),a1)), 2),
  "word_hits": run_lib((a0,a1) => run_loop($word_hits(str_in(a0),str_in(a1))), 2),
  "names": run_lib((a0,a1) => run_loop($names(str_in(a0),str_in(a1))), 2),
  "split_put": run_lib((a0,a1,a2) => run_loop($split_put(a0,str_in(a1),a2)), 3),
  "phrases": run_lib((a0) => run_loop($phrases(a0)), 1),
  "starts": run_lib((a0,a1) => run_loop($starts(a0,a1)), 2),
  "occurs_go": run_lib((a0,a1,a2) => run_loop($occurs_go(a0,a1,a2)), 3),
  "occurs": run_lib((a0,a1) => run_loop($occurs(a0,a1)), 2),
  "all_occur": run_lib((a0,a1,a2) => run_loop($all_occur(a0,a1,a2)), 3),
  "cue_hits": run_lib((a0,a1) => run_loop($cue_hits(str_in(a0),a1)), 2),
  "any_hits": run_lib((a0,a1) => run_loop($any_hits(a0,a1)), 2),
  "due_one": run_lib((a0,a1,a2,a3) => run_loop($due_one(a0,a1,str_in(a2),a3)), 4),
  "due_on": run_lib((a0,a1,a2) => run_loop($due_on(a0,a1,a2)), 3),
  "due": run_lib((a0,a1,a2) => run_loop($due(a0,a1,str_in(a2))), 3),
  "first_line": run_lib((a0,a1) => str_out(run_loop($first_line(str_in(a0),nat_in(a1)))), 2),
  "doing_args": run_lib((a0) => str_out(run_loop($doing_args(a0))), 1),
  "doing": run_lib((a0,a1) => str_out(run_loop($doing(str_in(a0),a1))), 2),
  "with_output": run_lib((a0) => str_out(run_loop($with_output(str_in(a0)))), 1),
  "note": run_lib((a0,a1,a2) => str_out(run_loop($note(str_in(a0),str_in(a1),str_in(a2)))), 3),
  "told": run_lib((a0) => str_out(run_loop($told(a0))), 1),
  "held": run_lib((a0) => str_out(run_loop($held(a0))), 1),
  "also_held": run_lib(() => str_out(run_loop($also_held())), 0),
  "teach_name": run_lib(() => str_out(run_loop($teach_name())), 0),
  "teach_cues": run_lib(() => run_loop($teach_cues()), 0),
  "teach": run_lib((a0) => str_out(run_loop($teach(str_in(a0)))), 1),
  "listed_one": run_lib((a0,a1) => str_out(run_loop($listed_one(str_in(a0),str_in(a1)))), 2),
  "listed": run_lib((a0,a1,a2) => str_out(run_loop($listed(str_in(a0),a1,str_in(a2)))), 3),
};
