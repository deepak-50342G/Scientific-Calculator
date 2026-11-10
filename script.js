"use strict";
/* =====================================================================
   SCIENTIFIC CALCULATOR
   - Safe expression parser (no eval)
   - Shift / Alpha layers, memory + variables A-F, M, X
   - DEG / RAD / GRAD, hyperbolic & inverse trig, log, ln, roots, powers
   - nCr, nPr, factorial, percent, integral, derivative, CALC
   - S<=>D (fraction), DMS (o,,,), ENG notation, history (up/down)
   ===================================================================== */

// ---------------------------------------------------------------- DOM
const exprEl   = document.querySelector("#ress");     // expression line
const resEl    = document.querySelector("#result");   // result line
const displayEl= document.querySelector("#displayDiv");
const stShift  = document.querySelector("#stShift");
const stAlpha  = document.querySelector("#stAlpha");
const stHyp    = document.querySelector("#stHyp");
const stAngle  = document.querySelector("#stAngle");
const stMem    = document.querySelector("#stMem");
const stMsg    = document.querySelector("#stMsg");

// ---------------------------------------------------------------- State
let tokens = [];          // expression as a list of tokens (strings)
let cur = 0;              // cursor position inside tokens
let shift = false;
let alpha = false;
let pend = null;          // null | "STO" | "RCL"
let hypOn = false;
let angle = "DEG";        // DEG | RAD | GRAD
let power = true;
let ans = 0;
let vars = { A: 0, B: 0, C: 0, D: 0, E: 0, F: 0, M: 0, X: 0 };
let justEval = false;     // true right after "="
let resultNum = null;     // last numeric result
let dispMode = "dec";     // dec | frac | dms | eng
let history = [];
let hIdx = -1;
let msgTimer = null;

// ---------------------------------------------------------------- Errors
class CalcError extends Error {}
const syn  = () => new CalcError("Syntax ERROR");
const math = () => new CalcError("Math ERROR");

// ---------------------------------------------------------------- Lexer
function lex(s) {
    const out = [];
    let i = 0;
    const fnRe = /^(asinh|acosh|atanh|sinh|cosh|tanh|asin|acos|atan|sin|cos|tan|logb|log|ln|abs|d\/dx|√|∛|∫)(?=\()/;
    while (i < s.length) {
        const r = s.slice(i);
        let m;
        if ((m = r.match(/^(\d+\.?\d*|\.\d+)/))) {
            out.push({ k: "num", v: parseFloat(m[0]) });
            i += m[0].length; continue;
        }
        if ((m = r.match(fnRe))) {
            out.push({ k: "fn", v: m[1] });
            i += m[1].length; continue;
        }
        if ((m = r.match(/^(Ans|Ran#)/))) {
            out.push({ k: "const", v: m[1] });
            i += m[1].length; continue;
        }
        if ((m = r.match(/^(nCr|nPr)/))) {
            out.push({ k: "op", v: m[1] });
            i += 3; continue;
        }
        if (r.startsWith("⁻¹")) { out.push({ k: "post", v: "inv" }); i += 2; continue; }
        if (r.startsWith("ˣ√")) { out.push({ k: "op", v: "ˣ√" }); i += 2; continue; }
        const c = s[i];
        if (c === "+") out.push({ k: "op", v: "+" });
        else if (c === "−" || c === "-") out.push({ k: "op", v: "−" });
        else if (c === "×" || c === "*") out.push({ k: "op", v: "×" });
        else if (c === "÷" || c === "/") out.push({ k: "op", v: "÷" });
        else if (c === "^") out.push({ k: "op", v: "^" });
        else if (c === "²" || c === "³" || c === "!" || c === "%") out.push({ k: "post", v: c });
        else if (c === "(") out.push({ k: "lp" });
        else if (c === ")") out.push({ k: "rp" });
        else if (c === ",") out.push({ k: "comma" });
        else if ("πeABCDEFMX".includes(c)) out.push({ k: "const", v: c });
        else throw syn();
        i++;
    }
    return out;
}

// ---------------------------------------------------------------- Parser
function parse(toks) {
    let p = 0;
    const isOp = (v) => toks[p] && toks[p].k === "op" && toks[p].v === v;
    const startsOperand = (t) => t && (t.k === "num" || t.k === "const" || t.k === "fn" || t.k === "lp");

    function expr() {
        let l = term();
        while (isOp("+") || isOp("−")) {
            const o = toks[p++].v;
            l = { k: "bin", o, l, r: term() };
        }
        return l;
    }
    function term() {
        let l = unary();
        for (;;) {
            if (isOp("×") || isOp("÷")) {
                const o = toks[p++].v;
                l = { k: "bin", o, l, r: unary() };
            } else if (startsOperand(toks[p])) {      // implicit multiplication: 2π, 3(4), 2sin(30)
                l = { k: "bin", o: "×", l, r: unary() };
            } else break;
        }
        return l;
    }
    function unary() {
        if (isOp("−")) { p++; return { k: "neg", a: unary() }; }
        if (isOp("+")) { p++; return unary(); }
        return comb();
    }
    function comb() {
        let l = power();
        while (isOp("nCr") || isOp("nPr")) {
            const o = toks[p++].v;
            l = { k: "bin", o, l, r: power() };
        }
        return l;
    }
    function power() {
        const l = postfix();
        if (isOp("^")) { p++; return { k: "bin", o: "^", l, r: expUnary() }; }
        if (isOp("ˣ√")) { p++; return { k: "bin", o: "root", l, r: expUnary() }; }
        return l;
    }
    function expUnary() {
        if (isOp("−")) { p++; return { k: "neg", a: expUnary() }; }
        if (isOp("+")) { p++; return expUnary(); }
        return power();
    }
    function postfix() {
        let n = primary();
        while (toks[p] && toks[p].k === "post") {
            n = { k: "post", o: toks[p++].v, a: n };
        }
        return n;
    }
    function primary() {
        const t = toks[p];
        if (!t) throw syn();
        if (t.k === "num")   { p++; return { k: "num", v: t.v }; }
        if (t.k === "const") { p++; return { k: "const", v: t.v }; }
        if (t.k === "lp") {
            p++;
            const e = expr();
            if (toks[p] && toks[p].k === "rp") p++;
            else if (p < toks.length) throw syn();      // missing ")" at the very end is allowed
            return e;
        }
        if (t.k === "fn") {
            p++;
            if (!toks[p] || toks[p].k !== "lp") throw syn();
            p++;
            const args = [expr()];
            while (toks[p] && toks[p].k === "comma") { p++; args.push(expr()); }
            if (toks[p] && toks[p].k === "rp") p++;
            else if (p < toks.length) throw syn();
            return { k: "fn", v: t.v, a: args };
        }
        throw syn();
    }

    if (!toks.length) throw syn();
    const tree = expr();
    if (p < toks.length) throw syn();
    return tree;
}

// ---------------------------------------------------------------- Maths helpers
const toRad = (x) => angle === "DEG" ? x * Math.PI / 180 : angle === "GRAD" ? x * Math.PI / 200 : x;
const fromRad = (x) => angle === "DEG" ? x * 180 / Math.PI : angle === "GRAD" ? x * 200 / Math.PI : x;
const tiny = (x) => Math.abs(x) < 1e-12 ? 0 : x;
const isInt = (x) => Number.isInteger(x);

function factorial(n) {
    if (!isInt(n) || n < 0 || n > 170) throw math();
    let r = 1;
    for (let i = 2; i <= n; i++) r *= i;
    return r;
}
function nPr(n, r) {
    if (!isInt(n) || !isInt(r) || n < 0 || r < 0 || r > n) throw math();
    let v = 1;
    for (let i = 0; i < r; i++) v *= (n - i);
    return v;
}
function nCr(n, r) {
    if (!isInt(n) || !isInt(r) || n < 0 || r < 0 || r > n) throw math();
    r = Math.min(r, n - r);
    let v = 1;
    for (let i = 1; i <= r; i++) v = v * (n - r + i) / i;
    return Math.round(v);
}
function powFn(a, b) {
    if (a === 0 && b === 0) throw math();
    const r = Math.pow(a, b);
    if (!Number.isFinite(r)) throw math();
    return r;
}
function rootFn(deg, x) {
    if (deg === 0) throw math();
    if (x < 0) {
        if (isInt(deg) && Math.abs(deg) % 2 === 1) return -Math.pow(-x, 1 / deg);
        throw math();
    }
    return Math.pow(x, 1 / deg);
}

// ---------------------------------------------------------------- Evaluator
function ev(n, env) {
    switch (n.k) {
        case "num":   return n.v;
        case "const": return constVal(n.v, env);
        case "neg":   return -ev(n.a, env);
        case "post": {
            const a = ev(n.a, env);
            switch (n.o) {
                case "²":   return a * a;
                case "³":   return a * a * a;
                case "inv": if (a === 0) throw math(); return 1 / a;
                case "!":   return factorial(a);
                case "%":   return a / 100;
            }
            throw syn();
        }
        case "bin": {
            const a = ev(n.l, env), b = ev(n.r, env);
            switch (n.o) {
                case "+": return a + b;
                case "−": return a - b;
                case "×": return a * b;
                case "÷": if (b === 0) throw math(); return a / b;
                case "^": return powFn(a, b);
                case "root": return rootFn(a, b);
                case "nCr": return nCr(a, b);
                case "nPr": return nPr(a, b);
            }
            throw syn();
        }
        case "fn": return callFn(n, env);
    }
    throw syn();
}

function constVal(v, env) {
    switch (v) {
        case "π": return Math.PI;
        case "e": return Math.E;
        case "Ans": return env.Ans;
        case "Ran#": return Math.random();
        default: return env[v] ?? 0;
    }
}

function callFn(n, env) {
    const need = { "logb": 2, "∫": 3, "d/dx": 2 }[n.v] || 1;
    if (n.a.length !== need) throw syn();

    // calculus: arguments are evaluated lazily with X substituted
    if (n.v === "∫") {
        const a = ev(n.a[1], env), b = ev(n.a[2], env);
        const N = 1000, h = (b - a) / N;
        let sum = 0;
        for (let i = 0; i <= N; i++) {
            const y = ev(n.a[0], { ...env, X: a + i * h });
            if (!Number.isFinite(y)) throw math();
            sum += (i === 0 || i === N ? 1 : i % 2 ? 4 : 2) * y;
        }
        return sum * h / 3;
    }
    if (n.v === "d/dx") {
        const a = ev(n.a[1], env), h = 1e-3;
        const f = (x) => ev(n.a[0], { ...env, X: x });
        const d = (f(a - 2 * h) - 8 * f(a - h) + 8 * f(a + h) - f(a + 2 * h)) / (12 * h);
        if (!Number.isFinite(d)) throw math();
        return d;
    }

    const x = ev(n.a[0], env);
    let r;
    switch (n.v) {
        case "sin":  r = tiny(Math.sin(toRad(x))); break;
        case "cos":  r = tiny(Math.cos(toRad(x))); break;
        case "tan": {
            const c = Math.cos(toRad(x));
            if (Math.abs(c) < 1e-12) throw math();
            r = tiny(Math.sin(toRad(x)) / c); break;
        }
        case "asin": if (Math.abs(x) > 1) throw math(); r = fromRad(Math.asin(x)); break;
        case "acos": if (Math.abs(x) > 1) throw math(); r = fromRad(Math.acos(x)); break;
        case "atan": r = fromRad(Math.atan(x)); break;
        case "sinh": r = Math.sinh(x); break;
        case "cosh": r = Math.cosh(x); break;
        case "tanh": r = Math.tanh(x); break;
        case "asinh": r = Math.asinh(x); break;
        case "acosh": if (x < 1) throw math(); r = Math.acosh(x); break;
        case "atanh": if (Math.abs(x) >= 1) throw math(); r = Math.atanh(x); break;
        case "log":  if (x <= 0) throw math(); r = Math.log10(x); break;
        case "ln":   if (x <= 0) throw math(); r = Math.log(x); break;
        case "logb": {
            const base = x, v = ev(n.a[1], env);
            if (base <= 0 || base === 1 || v <= 0) throw math();
            r = Math.log(v) / Math.log(base); break;
        }
        case "abs": r = Math.abs(x); break;
        case "√":   if (x < 0) throw math(); r = Math.sqrt(x); break;
        case "∛":   r = Math.cbrt(x); break;
        default: throw syn();
    }
    if (!Number.isFinite(r)) throw math();
    return r;
}

function evaluate(toks) {
    const tree = parse(lex(toks.join("")));
    const v = ev(tree, { ...vars, Ans: ans });
    if (!Number.isFinite(v)) throw math();
    return v;
}

// ---------------------------------------------------------------- Number formatting
function sci(x, eng) {
    const [mRaw, eRaw] = x.toExponential(9).split("e");
    let m = parseFloat(mRaw), e = parseInt(eRaw, 10);
    if (eng) {
        const e3 = Math.floor(e / 3) * 3;
        m = parseFloat((m * Math.pow(10, e - e3)).toPrecision(10));
        e = e3;
    }
    return m + "×10^" + e;
}
function fmt(x) {
    if (x === 0 || Object.is(x, -0)) return "0";
    const abs = Math.abs(x);
    if (abs >= 1e10 || abs < 1e-9) return sci(x, false);
    const r = parseFloat(x.toPrecision(10));
    return r.toLocaleString("en-US", { useGrouping: false, maximumSignificantDigits: 10 });
}
function toFraction(x) {
    if (isInt(x)) return null;
    const sign = x < 0 ? -1 : 1;
    const t = Math.abs(x);
    let h0 = 0, h1 = 1, k0 = 1, k1 = 0, b = t;
    for (let i = 0; i < 40; i++) {
        const a = Math.floor(b);
        const h2 = a * h1 + h0, k2 = a * k1 + k0;
        h0 = h1; h1 = h2; k0 = k1; k1 = k2;
        if (k1 > 10000) return null;
        if (Math.abs(t - h1 / k1) < 1e-10 * Math.max(1, t)) break;
        const f = b - a;
        if (f < 1e-12) break;
        b = 1 / f;
    }
    if (k1 > 10000 || Math.abs(t - h1 / k1) > 1e-8 * Math.max(1, t)) return null;
    return { n: sign * h1, d: k1 };
}
function toDMS(x) {
    const sign = x < 0 ? "-" : "";
    x = Math.abs(x);
    let d = Math.floor(x);
    const mF = (x - d) * 60;
    let m = Math.floor(mF + 1e-9);
    let s = Math.round((mF - m) * 60 * 100) / 100;
    if (s >= 60) { s -= 60; m++; }
    if (m >= 60) { m -= 60; d++; }
    return `${sign}${d}°${m}′${s}″`;
}

// ---------------------------------------------------------------- Rendering
function render() {
    // expression with caret
    exprEl.textContent = "";
    exprEl.append(tokens.slice(0, cur).join(""));
    const caret = document.createElement("span");
    caret.className = "caret";
    if (justEval) caret.style.visibility = "hidden";
    exprEl.append(caret);
    exprEl.append(tokens.slice(cur).join(""));
    const L = caret.offsetLeft, W = exprEl.clientWidth;
    if (L > exprEl.scrollLeft + W - 12) exprEl.scrollLeft = L - W + 12;
    else if (L < exprEl.scrollLeft) exprEl.scrollLeft = Math.max(0, L - 12);

    // status bar
    stShift.classList.toggle("on", shift);
    stAlpha.classList.toggle("on", alpha);
    stAlpha.textContent = pend || "A";
    stHyp.classList.toggle("on", hypOn);
    stAngle.classList.add("on");
    stAngle.textContent = angle === "DEG" ? "D" : angle === "RAD" ? "R" : "G";
    stMem.classList.toggle("on", vars.M !== 0);
    document.querySelector("#shift").classList.toggle("active", shift);
    document.querySelector("#alpha").classList.toggle("active", alpha);
    displayEl.classList.toggle("off", !power);
}
function setResult(text, isError) {
    resEl.textContent = text;
    resEl.classList.toggle("error", !!isError);
}
function flash(text) {
    stMsg.textContent = text;
    stMsg.classList.add("on");
    clearTimeout(msgTimer);
    msgTimer = setTimeout(() => { stMsg.textContent = ""; }, 1800);
}
function showValue(v) {
    resultNum = v;
    dispMode = "dec";
    setResult(fmt(v), false);
}

// ---------------------------------------------------------------- Editing
function prepare(kind) {
    if (!justEval) return;
    tokens = (kind === "op" || kind === "post") ? ["Ans"] : [];
    cur = tokens.length;
    justEval = false;
    setResult("", false);
}
function insert(list, kind = "num") {
    prepare(kind);
    tokens.splice(cur, 0, ...list);
    cur += list.length;
    hIdx = -1;
}
function pressDigit(d) {
    prepare("num");
    if (d === ".") {
        for (let i = cur - 1; i >= 0 && /^[0-9.]$/.test(tokens[i]); i--) {
            if (tokens[i] === ".") return;      // only one dot per number
        }
    }
    insert([d]);
}
function backspace() {
    if (justEval) { justEval = false; cur = tokens.length; }
    if (cur > 0) { tokens.splice(cur - 1, 1); cur--; }
}
function clearAll() {
    tokens = []; cur = 0; justEval = false; hIdx = -1;
    resultNum = null; dispMode = "dec";
    setResult("0", false);
}
function moveCursor(dir) {
    if (justEval) { justEval = false; cur = tokens.length; }
    cur = Math.max(0, Math.min(tokens.length, cur + dir));
}

// ---------------------------------------------------------------- Actions
function showError(e) {
    if (e instanceof CalcError) { setResult(e.message, true); justEval = false; }
    else { setResult("Syntax ERROR", true); justEval = false; console.error(e); }
}
function equals() {
    if (!tokens.length) return true;
    if (justEval) return true;
    try {
        const v = evaluate(tokens);
        ans = v;
        justEval = true;
        showValue(v);
        if (!history.length || history[history.length - 1].join("") !== tokens.join("")) {
            history.push([...tokens]);
            if (history.length > 50) history.shift();
        }
        hIdx = -1;
        return true;
    } catch (e) { showError(e); return false; }
}
function calcKey() {
    if (!tokens.length) return;
    if (justEval) { justEval = false; }
    const used = [...new Set(tokens.filter(t => /^[A-FMX]$/.test(t)))];
    for (const name of used) {
        const input = window.prompt(`${name} = ?`, vars[name]);
        if (input === null) return;
        const val = parseFloat(input);
        if (Number.isNaN(val)) { showError(math()); return; }
        vars[name] = val;
    }
    equals();
}
function memAdd(sign) {
    if (tokens.length && !justEval) { if (!equals()) return; }
    if (!tokens.length) return;
    vars.M += sign * ans;
    flash(sign > 0 ? "M+" : "M-");
}
function storeVar(letter) {
    if (tokens.length && !justEval) { if (!equals()) return; }
    vars[letter] = ans;
    flash(`${ans === 0 ? 0 : fmt(ans)} → ${letter}`);
}
function cycleAngle() {
    angle = angle === "DEG" ? "RAD" : angle === "RAD" ? "GRAD" : "DEG";
    flash(angle);
}
function clearMemory() {
    for (const k in vars) vars[k] = 0;
    flash("CLR");
}
function toggleFraction() {
    if (resultNum === null) return;
    if (dispMode === "frac") { showValue(resultNum); return; }
    const f = toFraction(resultNum);
    if (f) { dispMode = "frac"; setResult(`${f.n}/${f.d}`, false); }
}
function showDMS() {
    if (resultNum === null) return;
    dispMode = "dms";
    setResult(toDMS(resultNum), false);
}
function showENG() {
    if (resultNum === null || resultNum === 0) return;
    if (dispMode === "eng") { showValue(resultNum); return; }
    dispMode = "eng";
    setResult(sci(resultNum, true), false);
}
function loadHistory() {
    tokens = [...history[hIdx]];
    cur = tokens.length;
    justEval = false;
}
function histUp() {
    if (!history.length) return;
    hIdx = hIdx === -1 ? history.length - 1 : Math.max(0, hIdx - 1);
    loadHistory();
}
function histDown() {
    if (hIdx === -1) return;
    hIdx++;
    if (hIdx >= history.length) { hIdx = -1; tokens = []; cur = 0; justEval = false; return; }
    loadHistory();
}
function powerOff() {
    power = false;
    shift = alpha = false; pend = null;
}
function powerOn() {
    power = true;
    shift = alpha = false; pend = null; hypOn = false;
    clearAll();
}
function tenPower() {
    const prev = justEval ? "Ans" : tokens[cur - 1];
    const needsMantissa = prev === undefined || /^(\+|−|×|÷|\^|\(|,|.*\()$/.test(prev);
    insert([needsMantissa ? "10^" : "×10^"], "op");
}

// ---------------------------------------------------------------- Key map
// n = normal, s = shift, a = alpha letter, sl = shift label, al = alpha label
const ins  = (t, kind) => () => insert(Array.isArray(t) ? t : [t], kind);
const trig = (name) => ({
    n: () => { insert([name + (hypOn ? "h" : "") + "("]); hypOn = false; },
    s: () => { insert(["a" + name + (hypOn ? "h" : "") + "("]); hypOn = false; },
});

const keys = {
    // digits
    zero:  { n: () => pressDigit("0") }, one:   { n: () => pressDigit("1") },
    two:   { n: () => pressDigit("2") }, three: { n: () => pressDigit("3") },
    four:  { n: () => pressDigit("4") }, five:  { n: () => pressDigit("5") },
    six:   { n: () => pressDigit("6") }, seven: { n: () => pressDigit("7") },
    eight: { n: () => pressDigit("8") }, nine:  { n: () => pressDigit("9") },
    dot:   { n: () => pressDigit(".") },

    // basic operators
    plus:     { n: ins("+", "op") },
    minus:    { n: ins("−", "op") },
    multiply: { n: ins("×", "op") },
    devide:   { n: ins("÷", "op") },
    divided:  { n: ins("÷", "op") },
    equal:    { n: () => { equals(); } },
    DEL:      { n: backspace },
    AC:       { n: clearAll },
    Ans:      { n: ins("Ans"), s: ins("e"), sl: "e" },
    ten:      { n: tenPower, s: ins("π"), sl: "π" },

    // powers / roots / logs
    sqroot:   { n: ins("√("), s: ins("∛("), sl: "∛" },
    square:   { n: ins("²", "post"), s: ins("³", "post"), sl: "x³" },
    power:    { n: ins("^", "op"), s: ins("ˣ√", "op"), sl: "ˣ√" },
    x_pow_m_one: { n: ins("⁻¹", "post"), s: ins("!", "post"), sl: "x!" },
    log:      { n: ins("log("), s: ins("10^("), sl: "10ˣ" },
    ln:       { n: ins("ln("), s: ins("e^("), sl: "eˣ" },
    logerithm:{ n: () => { insert(["logb(", ","]); cur -= 1; } },

    // trig
    sin: { ...trig("sin"), a: "D", sl: "sin⁻¹", al: "D" },
    cos: { ...trig("cos"), a: "E", sl: "cos⁻¹", al: "E" },
    tan: { ...trig("tan"), a: "F", sl: "tan⁻¹", al: "F" },
    hyp: { n: () => { hypOn = !hypOn; }, a: "C", al: "C" },

    // brackets & misc
    brackets:      { n: ins("−"), s: ins("abs("), sl: "Abs", a: "A", al: "A" },
    odotdot:       { n: showDMS, a: "B", al: "B" },
    left_bracket:  { n: ins("(") },
    right_bracket: { n: ins(")", "post"), s: ins(",", "post"), sl: ",", a: "X", al: "X" },
    RCE:  { n: () => { alpha = true; pend = "RCL"; }, s: () => { alpha = true; pend = "STO"; }, sl: "STO" },
    ENG:  { n: showENG, s: ins("Ran#"), sl: "Ran#" },
    sd:   { n: toggleFraction },
    M_plus: { n: () => memAdd(1), s: () => memAdd(-1), sl: "M−", a: "M", al: "M" },

    // top block
    up:         { n: histUp, s: ins("nPr", "op"), sl: "nPr" },
    down:       { n: histDown, s: ins("%", "post"), sl: "%" },
    left:       { n: () => moveCursor(-1) },
    right:      { n: () => moveCursor(1) },
    calc:       { n: calcKey, s: ins("nCr", "op"), sl: "nCr" },
    integrate:  { n: () => { insert(["∫(", ",", ","]); cur -= 2; },
                  s: () => { insert(["d/dx(", ","]); cur -= 1; }, sl: "d/dx" },
    mode_setup: { n: cycleAngle, s: clearMemory, sl: "CLR" },
    on:         { n: powerOn, s: powerOff, sl: "OFF" },
};

// ---------------------------------------------------------------- Key handling
function press(id) {
    if (id === "shift") {
        if (!power) return;
        shift = !shift; alpha = false; pend = null;
        render(); return;
    }
    if (id === "alpha") {
        if (!power) return;
        alpha = !alpha; shift = false; pend = null;
        render(); return;
    }
    const k = keys[id];
    if (!k) return;
    if (!power && id !== "on") return;

    const useShift = shift, useAlpha = alpha, pending = pend;
    shift = false; alpha = false; pend = null;

    if (id === "on") {
        (useShift ? powerOff : powerOn)();
    } else if (useAlpha && k.a) {
        if (pending === "STO") storeVar(k.a);
        else insert([k.a]);
    } else if (useShift && k.s) {
        k.s();
    } else {
        k.n();
    }
    render();
}

// ---------------------------------------------------------------- Wire up buttons + labels
Object.keys(keys).forEach((id) => {
    const btn = document.getElementById(id);
    if (!btn) return;
    btn.addEventListener("click", () => { press(id); btn.blur(); });

    const k = keys[id];
    if (k.sl || k.al) {                      // little yellow (shift) / red (alpha) hints
        const lbl = document.createElement("span");
        lbl.className = "lbl";
        lbl.innerHTML = `<b class="ls">${k.sl || ""}</b><b class="la">${k.al || ""}</b>`;
        btn.parentElement.insertBefore(lbl, btn);
    }
});
document.getElementById("shift").addEventListener("click", () => press("shift"));
document.getElementById("alpha").addEventListener("click", () => press("alpha"));
[...document.querySelectorAll("#table1 td, #table2 td, #table3 td")].forEach((td) => {
    if (!td.querySelector(".lbl") && td.querySelector("button")) {
        const spacer = document.createElement("span");
        spacer.className = "lbl";
        td.insertBefore(spacer, td.firstChild);      // keeps every row the same height
    }
});

// ---------------------------------------------------------------- Keyboard support
const keyMap = {
    "0": "zero", "1": "one", "2": "two", "3": "three", "4": "four", "5": "five",
    "6": "six", "7": "seven", "8": "eight", "9": "nine", ".": "dot",
    "+": "plus", "-": "minus", "*": "multiply", "/": "devide",
    "(": "left_bracket", ")": "right_bracket", "^": "power",
    "!": "x_pow_m_one_fact", "%": "percent",
    "Enter": "equal", "=": "equal", "Backspace": "DEL", "Delete": "DEL", "Escape": "AC",
    "ArrowLeft": "left", "ArrowRight": "right", "ArrowUp": "up", "ArrowDown": "down",
};
document.addEventListener("keydown", (e) => {
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    const id = keyMap[e.key];
    if (!id) return;
    e.preventDefault();
    if (!power) return;
    if (id === "x_pow_m_one_fact") { insert(["!"], "post"); render(); return; }
    if (id === "percent") { insert(["%"], "post"); render(); return; }
    shift = false; alpha = false; pend = null;
    keys[id].n();
    render();
});

// ---------------------------------------------------------------- Init
setResult("0", false);
render();