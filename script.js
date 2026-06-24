/* ═══════════════════════════════════════════════════════════════
   NUMERIX — Plataforma de Métodos Numéricos
   script.js — Lógica completa

   © 2026 Fernando Granja & Alejandra Tinoco
   Todos los derechos reservados.

   Este software fue desarrollado con fines académicos.
   Queda prohibida su reproducción, distribución o modificación
   parcial o total sin autorización expresa de los autores.
═══════════════════════════════════════════════════════════════ */

"use strict";

/* Identificación del sistema en runtime */
const NUMERIX = {
  name:      'NUMERIX',
  version:   '1.0.0',
  authors:   ['Fernando Granja', 'Alejandra Tinoco'],
  year:      2026,
  rights:    'Todos los derechos reservados',
  toString() { return this.name + ' v' + this.version + ' © ' + this.year + ' ' + this.authors.join(' & '); }
};

/* ══════════════════════════════════════════════════════════════
   0. ESTADO GLOBAL
══════════════════════════════════════════════════════════════ */
const state = {
  currentTheme:  "t2",
  currentSection: "verify",
  lastRoot:       null,
  lastMethod:     null,
  lastFunction:   null,
};

/* ══════════════════════════════════════════════════════════════
   1. PARSER / EVALUADOR MATEMÁTICO SEGURO
══════════════════════════════════════════════════════════════ */

/**
 * Evalúa f(x) de forma segura.
 * Soporta: sin cos tan asin acos atan exp ln log log10 sqrt cbrt abs pi e ^ sen
 */
function evalF(exprRaw, xVal) {
  if (!exprRaw || exprRaw.trim() === "") throw new Error("La función no puede estar vacía.");

  /* Rechazar caracteres y palabras peligrosas */
  if (/[`'"\\;{}[\]|@#$%&=~?<>]/.test(exprRaw)) throw new Error("La función contiene caracteres no permitidos.");
  if (/(function|return|var|let|const|class|import|export|document|window|eval|alert|fetch|setTimeout|setInterval)/i.test(exprRaw))
    throw new Error("La función contiene palabras reservadas no permitidas.");

  let expr = exprRaw.trim();

  /* Normalizar alias */
  expr = expr.replace(/\bsen\b/gi,   "sin");
  expr = expr.replace(/\bln\b/gi,    "___LN___");
  expr = expr.replace(/\blog10\b/gi, "___LOG10___");
  expr = expr.replace(/\blog\b/gi,   "___LOG10___");

  /* Constantes */
  expr = expr.replace(/\bpi\b/gi, "Math.PI");
  expr = expr.replace(/\be\b(?!\^)/g, "Math.E");

  /* Funciones */
  expr = expr.replace(/\bsin\b/gi,  "Math.sin");
  expr = expr.replace(/\bcos\b/gi,  "Math.cos");
  expr = expr.replace(/\btan\b/gi,  "Math.tan");
  expr = expr.replace(/\basin\b/gi, "Math.asin");
  expr = expr.replace(/\bacos\b/gi, "Math.acos");
  expr = expr.replace(/\batan\b/gi, "Math.atan");
  expr = expr.replace(/\bexp\b/gi,  "Math.exp");
  expr = expr.replace(/\bsqrt\b/gi, "Math.sqrt");
  expr = expr.replace(/\bcbrt\b/gi, "Math.cbrt");
  expr = expr.replace(/\babs\b/gi,  "Math.abs");
  expr = expr.replace(/___LN___/g,    "Math.log");
  expr = expr.replace(/___LOG10___/g, "Math.log10");

  /* e^x → exp(x) */
  expr = expr.replace(/Math\.E\^([A-Za-z0-9_.()]+)/g, "Math.exp($1)");
  expr = expr.replace(/Math\.E\^/g, "Math.exp");

  /* Potencias */
  expr = expr.replace(/\^/g, "**");

  /* Multiplicación implícita */
  expr = expr.replace(/(\d)(Math\.|x\b)/g,    "$1*$2");
  expr = expr.replace(/(\))\s*(\(|x\b|Math\.)/g, "$1*$2");

  /* Sustituir x */
  expr = expr.replace(/\bx\b/g, `(${xVal})`);

  try {
    const result = Function('"use strict"; return (' + expr + ')')();
    if (!isFinite(result)) throw new Error("Resultado no finito — posible división por cero o dominio inválido.");
    if (isNaN(result))     throw new Error("Resultado NaN — dominio de función inválido para x = " + xVal);
    return result;
  } catch (e) {
    if (e.message.startsWith("Resultado")) throw e;
    throw new Error("Error al evaluar f(x): " + e.message);
  }
}

/** Derivada numérica por diferencias centrales */
function numericalDerivative(expr, x, h = 1e-7) {
  return (evalF(expr, x + h) - evalF(expr, x - h)) / (2 * h);
}

/** Evalúa sin lanzar (retorna NaN en error) */
function safeEval(expr, x) {
  try { return evalF(expr, x); } catch { return NaN; }
}

/* ══════════════════════════════════════════════════════════════
   VALIDACIÓN: aviso de X mayúscula
   La variable independiente siempre es x (minúscula).
   X mayúscula se usa para matrices/vectores — es un error común.
══════════════════════════════════════════════════════════════ */
function checkUpperX(expr, alertId) {
  if (!expr) return false;
  /* Detectar X aislada (no parte de palabras como exp, sqrt, xmin...) */
  if (/(?<![a-zA-Z])X(?![a-zA-Z])/.test(expr)) {
    showAlert(alertId, 'warning',
      '⚠ Usa <strong>x minúscula</strong> como variable independiente, no <code>X</code>. ' +
      'En métodos numéricos <code>x</code> es la incógnita escalar; ' +
      '<code>X</code> mayúscula se reserva para matrices y vectores. ' +
      'Corrige la expresión e intenta de nuevo.');
    return true; /* detiene la ejecución */
  }
  return false;
}

/* ══════════════════════════════════════════════════════════════
   2. MÉTODOS NUMÉRICOS
══════════════════════════════════════════════════════════════ */

/* ── Bisección ─────────────────────────────────────────────── */
function bisection(expr, a, b, tol, maxIter) {
  if (evalF(expr, a) * evalF(expr, b) >= 0)
    throw new Error("No hay cambio de signo en [a, b]. Verifique el intervalo.");

  const rows = [];
  let xOld = a;

  for (let i = 1; i <= maxIter; i++) {
    const fa  = evalF(expr, a);
    const fb  = evalF(expr, b);
    const xr  = (a + b) / 2;
    const fxr = evalF(expr, xr);
    const ea  = i === 1 ? null : Math.abs(xr - xOld);
    const er  = (i > 1 && Math.abs(xr) > 1e-14) ? (ea / Math.abs(xr)) * 100 : null;

    rows.push({ iter: i, a, b, xr, fa, fb, fxr, ea, er });

    if (i > 1 && ea < tol) { rows.at(-1).converged = true; return { root: xr, rows, converged: true, iterations: i }; }

    if (fa * fxr < 0) b = xr; else a = xr;
    xOld = xr;
  }
  return { root: rows.at(-1).xr, rows, converged: false, iterations: maxIter };
}

/* ── Regla Falsa ───────────────────────────────────────────── */
function falsePosition(expr, a, b, tol, maxIter) {
  if (evalF(expr, a) * evalF(expr, b) >= 0)
    throw new Error("No hay cambio de signo en [a, b]. Verifique el intervalo.");

  const rows = [];
  let xOld = null;

  for (let i = 1; i <= maxIter; i++) {
    const fa  = evalF(expr, a);
    const fb  = evalF(expr, b);
    const xr  = b - (fb * (a - b)) / (fa - fb);
    const fxr = evalF(expr, xr);
    const ea  = xOld !== null ? Math.abs(xr - xOld) : null;
    const er  = (ea !== null && Math.abs(xr) > 1e-14) ? (ea / Math.abs(xr)) * 100 : null;

    rows.push({ iter: i, a, b, xr, fa, fb, fxr, ea, er });

    if (ea !== null && ea < tol) { rows.at(-1).converged = true; return { root: xr, rows, converged: true, iterations: i }; }

    if (fa * fxr < 0) b = xr; else a = xr;
    xOld = xr;
  }
  return { root: rows.at(-1).xr, rows, converged: false, iterations: maxIter };
}

/* ── Newton-Raphson ────────────────────────────────────────── */
function newtonRaphson(expr, x0, tol, maxIter) {
  const rows = [];
  let x = x0;

  for (let i = 1; i <= maxIter; i++) {
    const fx  = evalF(expr, x);
    const fpx = numericalDerivative(expr, x);

    if (Math.abs(fpx) < 1e-14)
      throw new Error(`Iteración ${i}: Derivada ≈ 0 en x=${x.toFixed(6)}. El método no puede continuar.`);

    const x1 = x - fx / fpx;
    const ea = Math.abs(x1 - x);
    const er = Math.abs(x1) > 1e-14 ? (ea / Math.abs(x1)) * 100 : null;

    rows.push({ iter: i, x, fx, fpx, x1, ea, er });
    x = x1;

    if (ea < tol) { rows.at(-1).converged = true; return { root: x, rows, converged: true, iterations: i }; }
  }
  return { root: x, rows, converged: false, iterations: maxIter };
}

/* ── Secante ───────────────────────────────────────────────── */
function secant(expr, x0, x1, tol, maxIter) {
  const rows = [];
  let xa = x0, xb = x1;

  for (let i = 1; i <= maxIter; i++) {
    const fa = evalF(expr, xa);
    const fb = evalF(expr, xb);
    const denom = fb - fa;

    if (Math.abs(denom) < 1e-14)
      throw new Error(`Iteración ${i}: División por cero — f(x1) ≈ f(x0).`);

    const x2 = xb - fb * (xb - xa) / denom;
    const ea = Math.abs(x2 - xb);
    const er = Math.abs(x2) > 1e-14 ? (ea / Math.abs(x2)) * 100 : null;

    rows.push({ iter: i, x0: xa, x1: xb, fx0: fa, fx1: fb, x2, ea, er });
    xa = xb; xb = x2;

    if (ea < tol) { rows.at(-1).converged = true; return { root: x2, rows, converged: true, iterations: i }; }
  }
  return { root: xb, rows, converged: false, iterations: maxIter };
}

/* ══════════════════════════════════════════════════════════════
   PUNTO FIJO — LABORATORIO DE TRANSFORMADAS
   Genera múltiples g(x) = x − λ·f(x), evalúa convergencia
   |g'(x)| < 1 y ejecuta iteraciones con la g(x) seleccionada
══════════════════════════════════════════════════════════════ */

/* ── Estado del laboratorio ────────────────────────────────── */
/* ══════════════════════════════════════════════════════════════
   PUNTO FIJO — LABORATORIO DE TRANSFORMADAS
   Lógica basada en RootFinderMN:
   λ_óptimo = −1/f'(x₀)  →  g(x) = x + λ·f(x)
   Umbral convergencia: |g'(x₀)| < 0.98
══════════════════════════════════════════════════════════════ */

/* Estado del laboratorio */
const pfLab = {
  transforms: [],   // candidatas generadas
  selected:   null, // { lambda, gExpr, gEval, gAtX0, deriv, convergent, reason }
  expr:       '',   // f(x) guardada al generar
};

/* ── Derivada numérica central (h=1e-7, igual que RootFinder) ── */
function pfNumDeriv(fn, x) {
  const h = 1e-7;
  try {
    const hi = fn(x + h), lo = fn(x - h);
    if (!isFinite(hi) || !isFinite(lo)) return NaN;
    return (hi - lo) / (2 * h);
  } catch(e) { return NaN; }
}

/* ── Construir evaluador de g(x) = x + λ·f(x) ─────────────────
   Nota: cuando λ es negativo esto es g(x) = x − |λ|·f(x)       */
function pfMakeG(fExpr, lambda) {
  return function(xVal) {
    const fx = evalF(fExpr, xVal);
    return xVal + lambda * fx;
  };
}

/* ── Expresión legible de g(x) ──────────────────────────────── */
function pfGExprStr(fExpr, lambda) {
  const lAbs = Math.abs(lambda).toFixed(10).replace(/\.?0+$/, '');
  if (lambda >= 0) return `x + ${lAbs}·f(x)`;
  return `x − ${lAbs}·f(x)`;
}

/* ── Generar candidatas — lógica exacta de RootFinderMN ─────── */
function pfGenerateTransforms(fExpr, x0) {
  const THRESHOLD = 0.98;   // umbral igual que RootFinder
  const candidates = [];
  const seen = new Set();

  /* f'(x₀) para calcular λ_óptimo */
  const fpx0 = pfNumDeriv(xv => evalF(fExpr, xv), x0);

  /* Conjunto de λ a probar */
  const rawLambdas = [];
  if (isFinite(fpx0) && Math.abs(fpx0) > 1e-8) {
    const opt = -1 / fpx0;           // ← el λ que hace |g'(x₀)| ≈ 0
    rawLambdas.push(opt, opt*0.5, opt*1.5, opt*0.25, opt*0.75);
  }
  /* Complemento fijo para cubrir todos los signos */
  rawLambdas.push(-1, -0.5, -0.25, -0.1, 0.1, 0.25, 0.5, 1);

  for (const rawLambda of rawLambdas) {
    if (!isFinite(rawLambda) || Math.abs(rawLambda) < 1e-12) continue;

    /* Redondear a 10 decimales igual que RootFinder */
    const lambda  = parseFloat(rawLambda.toFixed(10));
    const gExprStr = pfGExprStr(fExpr, lambda);

    if (seen.has(gExprStr)) continue;
    seen.add(gExprStr);

    const gEval = pfMakeG(fExpr, lambda);
    let gAtX0 = NaN, deriv = NaN, convergent = false, reason = '';

    try {
      gAtX0 = gEval(x0);
      if (!isFinite(gAtX0)) throw new Error('no finito');

      deriv = pfNumDeriv(gEval, x0);
      const derivAbs = isFinite(deriv) ? Math.abs(deriv) : Infinity;

      convergent = derivAbs < THRESHOLD;
      reason     = convergent
        ? `|g'(x₀)| = ${derivAbs.toFixed(6)} < ${THRESHOLD}`
        : `|g'(x₀)| = ${derivAbs.toFixed(6)} ≥ ${THRESHOLD}`;

    } catch(e) {
      reason = 'No se pudo evaluar de forma estable';
    }

    candidates.push({ lambda, gExprStr, gEval, gAtX0, deriv, convergent, reason });
  }

  /* Orden: convergentes primero, luego por menor |g'| */
  candidates.sort((a, b) => {
    if (a.convergent !== b.convergent) return a.convergent ? -1 : 1;
    const da = isFinite(a.deriv) ? Math.abs(a.deriv) : Infinity;
    const db = isFinite(b.deriv) ? Math.abs(b.deriv) : Infinity;
    return da - db;
  });

  return candidates;
}

/* ── Iteración de Punto Fijo con g(x) seleccionada ─────────── */
function fixedPointWithG(gEval, fExpr, x0, tol, maxIter) {
  const rows = [];
  let x = x0;

  for (let i = 1; i <= maxIter; i++) {
    let x1, fxi;
    try {
      x1  = gEval(x);
      fxi = evalF(fExpr, x);
    } catch(e) {
      throw new Error(`Iteración ${i}: ${e.message}`);
    }

    if (!isFinite(x1) || Math.abs(x1) > 1e15) {
      rows.push({ iter: i, xn: x, x1: NaN, ea: NaN, er: null, fxi });
      return { root: x, rows, converged: false, iterations: i };
    }

    const ea = Math.abs(x1 - x);
    const er = Math.abs(x1) > 1e-14 ? (ea / Math.abs(x1)) * 100 : null;

    rows.push({ iter: i, xn: x, x1, ea, er, fxi });
    x = x1;

    /* Doble criterio igual que RootFinder: Ea < tol  OR  |f(xi)| < 1e-15 */
    if (ea < tol || Math.abs(fxi) < 1e-15) {
      rows.at(-1).converged = true;
      return { root: x, rows, converged: true, iterations: i };
    }
  }
  return { root: x, rows, converged: false, iterations: maxIter };
}

/* ── Tabla de iteraciones ───────────────────────────────────── */
function buildFixedTable(rows) {
  const hdr = `<tr>
    <th>#</th>
    <th>x<sub>n</sub></th>
    <th>x<sub>n+1</sub> = g(x<sub>n</sub>)</th>
    <th>E<sub>a</sub></th>
    <th>E<sub>r</sub>%</th>
  </tr>`;
  const bdy = rows.map(r => `<tr${rowClass(r)}>
    <td>${r.iter}</td>
    <td class="pf-col-xn">${fmt(r.xn)}</td>
    <td class="pf-col-gxn">${isFinite(r.x1) ? fmt(r.x1) : '∞ diverge'}</td>
    <td class="pf-col-ea">${isFinite(r.ea) ? fmtSci(r.ea) : '—'}</td>
    <td>${r.er !== null && isFinite(r.er) ? fmt(r.er, 4) + '%' : '—'}</td>
  </tr>`).join('');
  return `<div class="table-wrapper pf-iter-table"><table><thead>${hdr}</thead><tbody>${bdy}</tbody></table></div>`;
}

/* ── Renderizar tarjetas ────────────────────────────────────── */
function pfRenderCards(transforms, selectedIdx) {
  const container = document.getElementById('pf-transform-cards');
  if (!container) return;

  const bestIdx = transforms.findIndex(t => t.convergent);

  container.innerHTML = transforms.map((t, i) => {
    const isSelected = i === selectedIdx;
    const isBest     = i === bestIdx;
    const derivAbs   = isFinite(t.deriv) ? Math.abs(t.deriv) : Infinity;
    /* Barra: 100% = |g'| = 1, escala lineal, máx 100% */
    const barPct   = Math.min(100, derivAbs * 100);
    const barClass = t.convergent ? 'ok' : 'bad';
    const derivStr = isFinite(derivAbs) ? derivAbs.toFixed(6) : '∞';
    const lambdaDisplay = t.lambda >= 0
      ? `+${t.lambda.toFixed(6)}`
      : t.lambda.toFixed(6);

    return `
    <div class="pf-card ${t.convergent ? 'convergent' : 'divergent'} ${isSelected ? 'selected' : ''} ${isBest ? 'best' : ''}"
         onclick="pfSelectCard(${i})">
      <div class="pf-card-header">
        <span class="pf-lambda-badge">λ = ${lambdaDisplay}</span>
        <span class="pf-card-title">Transformada ${i + 1}</span>
      </div>
      <div class="pf-card-expr">g(x) = ${t.gExprStr}</div>
      <div class="pf-card-metrics">
        <span class="pf-metric">g(x₀) = ${isFinite(t.gAtX0) ? t.gAtX0.toFixed(6) : '∞'}</span>
        <span class="pf-conv-badge ${t.convergent ? 'ok' : 'bad'}">
          ${t.convergent ? '✓ Convergente' : '✗ Divergente'}
        </span>
      </div>
      <div class="pf-deriv-bar-wrap">
        <div class="pf-deriv-bar-label">
          <span>|g'(x₀)| = ${derivStr}</span>
          <span>${t.convergent ? '< 0.98 ✓' : '≥ 0.98 ✗'}</span>
        </div>
        <div class="pf-deriv-bar-track">
          <div class="pf-deriv-bar-fill ${barClass}" style="width:${barPct}%;"></div>
        </div>
      </div>
      <div style="margin-top:.4rem;font-size:.7rem;color:var(--gray-400);font-family:var(--font-main);">${t.reason}</div>
    </div>`;
  }).join('');
}

/* ── Renderizar transformación activa ───────────────────────── */
function pfRenderActive(t) {
  const box = document.getElementById('pf-active-box');
  const sec = document.getElementById('pf-active-transform');
  if (!box || !sec) return;
  sec.style.display = 'block';

  const derivAbs    = isFinite(t.deriv) ? Math.abs(t.deriv) : Infinity;
  const statusColor = t.convergent ? '#065f46' : '#991b1b';
  const statusIcon  = t.convergent ? '✓' : '✗';
  const lambdaSign  = t.lambda >= 0 ? `+${t.lambda.toFixed(8)}` : t.lambda.toFixed(8);

  box.innerHTML = `
    <div class="pf-active-item">
      <div class="pf-active-label">λ usado</div>
      <div class="pf-active-val">${lambdaSign}</div>
    </div>
    <div class="pf-active-item" style="flex:2;">
      <div class="pf-active-label">g(x) activa</div>
      <div class="pf-active-val mono-expr">g(x) = ${t.gExprStr}</div>
    </div>
    <div class="pf-active-item">
      <div class="pf-active-label">g(x₀)</div>
      <div class="pf-active-val">${isFinite(t.gAtX0) ? t.gAtX0.toFixed(8) : '∞'}</div>
    </div>
    <div class="pf-active-item">
      <div class="pf-active-label">|g'(x₀)|</div>
      <div class="pf-active-val" style="color:${statusColor};">
        ${isFinite(derivAbs) ? derivAbs.toFixed(8) : '∞'}
      </div>
    </div>
    <div class="pf-active-item" style="flex:2;">
      <div class="pf-active-label">Criterio de convergencia</div>
      <div class="pf-active-val" style="color:${statusColor};font-size:.85rem;">
        ${statusIcon} ${t.reason}
      </div>
    </div>`;
}

/* ── Selección manual de tarjeta ────────────────────────────── */
function pfSelectCard(idx) {
  const mode = document.querySelector('input[name="pfMode"]:checked')?.value;
  if (mode !== 'manual') return;
  pfLab.selected = pfLab.transforms[idx];
  pfRenderCards(pfLab.transforms, idx);
  pfRenderActive(pfLab.selected);
}
window.pfSelectCard = pfSelectCard;

/* ── BOTÓN: Generar transformadas ───────────────────────────── */
document.getElementById('btnGenerateG').addEventListener('click', () => {
  clearAlert('fixedAlert');
  const expr = getVal('func_fixed');
  const x0   = getNum('fixed_x0');

  const err = validate([
    [!expr,    'Ingrese la función f(x).'],
    [isNaN(x0),'El valor x₀ debe ser numérico.'],
  ]);
  if (err) { showAlert('fixedAlert', 'danger', err); return; }

  try { evalF(expr, x0); } catch(e) {
    showAlert('fixedAlert', 'danger', 'Error al evaluar f(x): ' + e.message); return;
  }

  /* Generar */
  pfLab.expr       = expr;
  pfLab.transforms = pfGenerateTransforms(expr, x0);

  /* Selección automática: primera convergente (menor |g'|) */
  const bestIdx  = pfLab.transforms.findIndex(t => t.convergent);
  const autoIdx  = bestIdx >= 0 ? bestIdx : 0;
  pfLab.selected = pfLab.transforms[autoIdx];

  /* Mostrar UI */
  document.getElementById('pf-transforms-section').style.display = 'block';
  pfRenderCards(pfLab.transforms, autoIdx);
  pfRenderActive(pfLab.selected);

  const nConv = pfLab.transforms.filter(t => t.convergent).length;
  const lBest = pfLab.selected.lambda.toFixed(6);
  showAlert('fixedAlert', nConv > 0 ? 'success' : 'warning',
    nConv > 0
      ? `${nConv}/${pfLab.transforms.length} transformadas convergentes. ` +
        `Mejor: λ = ${lBest}, |g'(x₀)| = ${Math.abs(pfLab.selected.deriv).toFixed(6)}`
      : `Ninguna transformada cumple |g'(x₀)| < 0.98 en x₀ = ${x0}. ` +
        `Pruebe un x₀ más cercano a la raíz.`
  );
});

/* ── Cambio modo auto ↔ manual ──────────────────────────────── */
document.querySelectorAll('input[name="pfMode"]').forEach(r => {
  r.addEventListener('change', () => {
    if (!pfLab.transforms.length) return;
    if (r.value === 'auto' && r.checked) {
      const bestIdx = pfLab.transforms.findIndex(t => t.convergent);
      const idx     = bestIdx >= 0 ? bestIdx : 0;
      pfLab.selected = pfLab.transforms[idx];
      pfRenderCards(pfLab.transforms, idx);
      pfRenderActive(pfLab.selected);
    } else {
      /* Manual: mostrar todas seleccionables */
      pfRenderCards(pfLab.transforms, pfLab.transforms.indexOf(pfLab.selected));
    }
  });
});

/* ── BOTÓN: Ejecutar Punto Fijo ─────────────────────────────── */
document.getElementById('btnFixed').addEventListener('click', () => {
  clearAlert('fixedAlert');
  document.getElementById('methodIterTable').innerHTML = '';

  const expr = getVal('func_fixed');
  const x0   = getNum('fixed_x0');
  const tol  = getNum('fixed_tol');
  const it   = getInt('fixed_iter');

  const err = validate([
    [!expr,              'Ingrese la función f(x).'],
    [isNaN(x0),          'x₀ inválido.'],
    [isNaN(tol)||tol<=0, 'Tolerancia inválida.'],
    [isNaN(it)||it<1,    'Máx. iteraciones inválido.'],
    [!pfLab.selected,    'Primero presione "Generar Transformadas g(x)".'],
  ]);
  if (err) { showAlert('fixedAlert', 'danger', err); return; }

  if (expr !== pfLab.expr) {
    showAlert('fixedAlert', 'warning',
      'La función f(x) cambió. Presione "Generar Transformadas" de nuevo.'); return;
  }

  try {
    const g   = pfLab.selected;
    const res = fixedPointWithG(g.gEval, expr, x0, tol, it);

    /* Cabecera con info de la transformada usada */
    const lambdaSign = g.lambda >= 0 ? `+${g.lambda.toFixed(8)}` : g.lambda.toFixed(8);
    const header = `
      <div class="card" style="margin-bottom:1rem;background:linear-gradient(135deg,#fdf2f8,#fce7f3);border:1.5px solid #f9a8d4;padding:.875rem 1.25rem;">
        <div style="display:flex;align-items:center;gap:.875rem;flex-wrap:wrap;">
          <span style="font-family:var(--font-main);font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.5px;color:#9d174d;">Transformada usada</span>
          <code style="font-family:var(--font-mono);font-size:.85rem;color:#831843;background:rgba(157,23,77,.1);padding:3px 10px;border-radius:5px;">
            g(x) = ${g.gExprStr}
          </code>
          <code style="font-family:var(--font-mono);font-size:.82rem;color:#9d174d;background:rgba(157,23,77,.07);padding:3px 8px;border-radius:5px;">
            λ = ${lambdaSign}
          </code>
          <code style="font-family:var(--font-mono);font-size:.82rem;color:#9d174d;background:rgba(157,23,77,.07);padding:3px 8px;border-radius:5px;">
            |g'(x₀)| = ${Math.abs(g.deriv).toFixed(6)}
          </code>
          <span class="badge ${g.convergent ? 'badge-success' : 'badge-warning'}" style="margin-left:auto;">
            ${g.convergent ? '✓ Convergente' : '⚠ No garantiza convergencia'}
          </span>
        </div>
      </div>`;

    const tableHtml = header + buildFixedTable(res.rows);
    const msg = handleResult(res, 'Punto Fijo', expr, tableHtml);
    showAlert('fixedAlert', res.converged ? 'success' : 'warning',
      msg + ` · λ = ${g.lambda.toFixed(6)} · g(x) = ${g.gExprStr}`);

  } catch(e) { showAlert('fixedAlert', 'danger', e.message); }
});

/* ══════════════════════════════════════════════════════════════
   3. RENDERIZADO DE TABLAS
══════════════════════════════════════════════════════════════ */

const fmt    = (v, d = 8) => (v === null || v === undefined) ? "—" : Number(v).toFixed(d);
const fmtSci = (v, d = 4) => (v === null || v === undefined) ? "—" : Number(v).toExponential(d);
/* ══════════════════════════════════════════════════════════════
   MODO AUTOMÁTICO — BÚSQUEDA DE TODAS LAS RAÍCES
   ─────────────────────────────────────────────────────────────
   scanRoots()  → escanea el rango [A,B] y devuelve subintervalos
                  con cambio de signo
   autoAllRoots() → aplica el método seleccionado en cada
                    subintervalo y devuelve lista completa de raíces
══════════════════════════════════════════════════════════════ */

/**
 * Escanea [A, B] con tamaño de paso `step`.
 * Retorna array de { a, b, fa, fb } donde hay cambio de signo.
 * También detecta si f(xi) ≈ 0 exactamente.
 */
/**
 * calcStepInfo(A, B, stepUsuario)
 *   Calcula step dinámico y genera advertencias.
 *   Retorna { stepFinal, stepAuto, warnings[] }
 */
function calcStepInfo(A, B, stepUsuario) {
  const rango    = B - A;
  /* Paso automático más fino: rango/500 para no perder raíces cercanas.
     Máximo 0.05 para rangos grandes, mínimo 1e-4 para rangos pequeños. */
  const stepAuto  = Math.max(1e-4, Math.min(rango / 500, 0.05));
  const stepFinal = Math.min(stepUsuario, stepAuto);
  const warnings  = [];

  if (stepUsuario > stepAuto) {
    warnings.push({
      level: 'warning',
      msg: `⚠ El paso ingresado (${stepUsuario}) es mayor al recomendado (${stepAuto.toFixed(4)}). Pueden perderse raíces. Se usará el paso automático: ${stepFinal.toFixed(4)}.`
    });
  }
  if (stepUsuario < stepAuto / 10) {
    warnings.push({
      level: 'info',
      msg: `ℹ El paso es muy pequeño (${stepUsuario}). Esto puede afectar el rendimiento en rangos grandes.`
    });
  }

  return { stepFinal, stepAuto, stepUsuario, warnings };
}

/**
 * scanRoots(expr, A, B, step)
 *   Escanea [A, B] con tamaño de paso `step`.
 *   — Doble pasada: paso normal + paso/2 desplazado para no perder raíces
 *   — Corrige el else-if que podía saltar cambios de signo
 */
function scanRoots(expr, A, B, step) {
  const intervals  = [];
  const exactZeros = [];
  const posibles   = [];

  /* Función auxiliar: añadir intervalo si no es duplicado */
  function addInterval(a, b, fa, fb) {
    const isDup = intervals.some(iv =>
      Math.abs(iv.a - a) < step * 0.5 && Math.abs(iv.b - b) < step * 0.5
    );
    if (!isDup) intervals.push({ a, b, fa, fb, tipo: 'cambio_signo' });
  }

  /* Función auxiliar: escanear con un offset dado */
  function scan(offset) {
    let xi = A + offset;
    while (xi < B) {
      const xi1 = Math.min(xi + step, B);
      let fi, fi1;
      try { fi  = evalF(expr, xi);  } catch(e) { xi = xi1; continue; }
      try { fi1 = evalF(expr, xi1); } catch(e) { xi = xi1; continue; }
      if (!isFinite(fi) || !isFinite(fi1)) { xi = xi1; continue; }

      /* Raíz exacta en xi */
      if (Math.abs(fi) < 1e-11) {
        const isDup = exactZeros.some(z => Math.abs(z - xi) < step * 0.5);
        if (!isDup) exactZeros.push(xi);
      }
      /* Raíz exacta en xi1 */
      if (Math.abs(fi1) < 1e-11) {
        const isDup = exactZeros.some(z => Math.abs(z - xi1) < step * 0.5);
        if (!isDup) exactZeros.push(xi1);
      }

      /* Cambio de signo — SIEMPRE verificar, independiente de raíces exactas */
      if (fi * fi1 < 0) {
        addInterval(xi, xi1, fi, fi1);
      }

      /* Posible raíz: valor muy pequeño pero sin cambio de signo */
      if (fi  * fi1 >= 0 && Math.abs(fi)  < 1e-6) {
        const isDup = posibles.some(p => Math.abs(p.x - xi) < step * 0.5)
                   || exactZeros.some(z => Math.abs(z - xi) < step * 0.5);
        if (!isDup) posibles.push({ x: xi, fx: fi, tipo: 'posible' });
      }
      if (fi  * fi1 >= 0 && Math.abs(fi1) < 1e-6) {
        const isDup = posibles.some(p => Math.abs(p.x - xi1) < step * 0.5)
                   || exactZeros.some(z => Math.abs(z - xi1) < step * 0.5);
        if (!isDup) posibles.push({ x: xi1, fx: fi1, tipo: 'posible' });
      }

      xi = xi1;
    }
  }

  /* Pasada única — el paso fino (rango/500) es suficiente para detectar todos los cambios de signo */
  scan(0);

  return { intervals, exactZeros, posibles };
}

/**
 * autoAllRoots(expr, A, B, stepUsuario, tol, maxIter, methodName)
 *   - Calcula step dinámico con calcStepInfo()
 *   - Llama scanRoots() con el step final
 *   - Aplica el método en cada subintervalo
 *   - Clasifica cada raíz con tipo: "exacta" | "cambio_signo" | "posible"
 *   - Retorna { roots, intervalsDetected, exactZeros, posibles, stepInfo, warnings }
 */
function autoAllRoots(expr, A, B, stepUsuario, tol, maxIter, methodName) {
  /* Step dinámico */
  const stepInfo = calcStepInfo(A, B, stepUsuario);
  const step     = stepInfo.stepFinal;

  const { intervals, exactZeros, posibles } = scanRoots(expr, A, B, step);
  const found = [];

  /* Umbral de deduplicación: al menos 2 veces el paso para evitar duplicados
     del doble-scan, pero no tan grande que fusione raíces reales cercanas */
  const dedupThr = Math.max(step * 1.5, tol * 10);

  /* Deduplicar intervalos ANTES de correr los métodos
     (el scanner puede generar [a,b] y [a,b+ε] para la misma raíz) */
  const uniqueIntervals = [];
  intervals.forEach(iv => {
    const center = (iv.a + iv.b) / 2;
    const already = uniqueIntervals.some(u => Math.abs((u.a + u.b)/2 - center) < step);
    if (!already) uniqueIntervals.push(iv);
  });

  /* Raíces exactas → tipo "exacta"
     Solo si NO hay ya un intervalo que cubra esa raíz
     (para evitar contarla dos veces) */
  const coveredByInterval = (x) =>
    uniqueIntervals.some(iv => x >= iv.a - step && x <= iv.b + step);

  exactZeros.forEach(x => {
    if (coveredByInterval(x)) return; // ya se maneja via intervalo
    const isDup = found.some(f => Math.abs(f.root - x) < dedupThr);
    if (!isDup) found.push({
      root: x, interval: { a: x, b: x },
      tipo: 'exacta', exact: true, result: null
    });
  });

  /* Cambio de signo → tipo "cambio_signo" */
  uniqueIntervals.forEach(({ a, b }) => {
    try {
      let res;
      if      (methodName === 'bisection') res = bisection(expr, a, b, tol, maxIter);
      else if (methodName === 'false')     res = falsePosition(expr, a, b, tol, maxIter);
      else if (methodName === 'newton')    res = newtonRaphson(expr, (a + b) / 2, tol, maxIter);
      else if (methodName === 'secant')    res = secant(expr, a, b, tol, maxIter);
      else return;

      if (!isFinite(res.root)) return;
      const isDup = found.some(f => Math.abs(f.root - res.root) < dedupThr);
      if (!isDup) found.push({
        root: res.root, interval: { a, b },
        tipo: 'cambio_signo', exact: false, result: res
      });
    } catch(e) { /* subintervalo sin convergencia */ }
  });

  /* Posibles → tipo "posible" (solo si no ya están como raíz confirmada) */
  posibles.forEach(({ x, fx }) => {
    const isDup = found.some(f => Math.abs(f.root - x) < dedupThr);
    if (!isDup) found.push({
      root: x, interval: { a: x, b: x },
      tipo: 'posible', exact: false, result: null,
      fxVal: fx
    });
  });

  found.sort((a, b) => a.root - b.root);
  found.forEach((f, i) => { f.rootNum = i + 1; });

  return {
    roots:              found,
    intervalsDetected:  uniqueIntervals,
    exactZeros,
    posibles,
    stepInfo,
    warnings:           stepInfo.warnings
  };
}

/* ── Render: panel multi-raíces ─────────────────────────────── */
function renderMultiRootsResult(data, expr, methodLabel, buildTableFn, A, B, stepUsuario) {
  const { roots, intervalsDetected, exactZeros, posibles, stepInfo, warnings } = data;
  const COLORS = ['#4f46e5','#10b981','#f59e0b','#ec4899','#ef4444','#14b8a6','#8b5cf6'];

  /* Colores y etiquetas por tipo */
  const TIPO_META = {
    cambio_signo: { label: 'cambio de signo', badge: 'Bolzano ✓',  bg: 'var(--success-light)', color: '#065f46', border: '#6ee7b7' },
    exacta:       { label: 'exacta',           badge: 'Exacta',     bg: '#f0fdf4',              color: '#065f46', border: '#6ee7b7' },
    posible:      { label: 'posible',           badge: '? Posible',  bg: 'var(--warning-light)', color: '#92400e', border: '#fcd34d' },
  };

  const container = document.getElementById('methodIterTable');
  let html = '';

  /* ── 0. Advertencias de step ── */
  if (warnings && warnings.length > 0) {
    warnings.forEach(w => {
      html += '<div class="alert alert-' + (w.level === 'warning' ? 'warning' : 'info') + '" style="margin-bottom:.75rem;">';
      html += '<span class="alert-icon">' + (w.level === 'warning' ? '⚠' : 'ℹ') + '</span>';
      html += '<span>' + w.msg + '</span></div>';
    });
  }

  /* ── 1. Panel resumen ── */
  html += '<div class="card" style="margin-bottom:1.25rem;border-top:4px solid var(--primary);">';
  html += '<div class="card-header">';
  html += '<div class="card-header-icon purple">🔎</div>';
  html += '<div>';
  html += '<div class="card-title">Modo Automático — ' + methodLabel + '</div>';

  /* Info de step dinámico */
  const si = stepInfo;
  let stepDesc = 'f(x) = ' + expr + '  ·  Rango [' + A + ', ' + B + ']';
  if (si) {
    stepDesc += '  ·  Paso ingresado: ' + si.stepUsuario;
    if (si.stepFinal !== si.stepUsuario) {
      stepDesc += '  →  <strong style="color:var(--primary-dark);">Paso aplicado: ' + si.stepFinal.toFixed(4) + '</strong>';
      stepDesc += '  (auto = ' + si.stepAuto.toFixed(4) + ')';
    } else {
      stepDesc += '  ·  Paso auto: ' + si.stepAuto.toFixed(4);
    }
  }
  html += '<div class="card-subtitle">' + stepDesc + '</div>';
  html += '</div>';

  html += '<div style="margin-left:auto;display:flex;gap:.5rem;align-items:center;flex-wrap:wrap;">';

  /* Badges de conteo por tipo */
  const nBolzano = roots.filter(r => r.tipo === 'cambio_signo').length;
  const nExacta  = roots.filter(r => r.tipo === 'exacta').length;
  const nPosible = roots.filter(r => r.tipo === 'posible').length;

  html += '<span style="background:var(--primary-light);color:var(--primary-dark);font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #a5b4fc;">';
  html += intervalsDetected.length + ' intervalo' + (intervalsDetected.length !== 1 ? 's' : '') + '</span>';

  if (nBolzano > 0)
    html += '<span style="background:var(--success-light);color:#065f46;font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #6ee7b7;">' + nBolzano + ' Bolzano</span>';
  if (nExacta > 0)
    html += '<span style="background:#f0fdf4;color:#065f46;font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #6ee7b7;">' + nExacta + ' exacta' + (nExacta>1?'s':'') + '</span>';
  if (nPosible > 0)
    html += '<span style="background:var(--warning-light);color:#92400e;font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #fcd34d;">' + nPosible + ' posible' + (nPosible>1?'s':'') + '</span>';

  html += '</div></div>';

  /* Tarjetas de raíces */
  const confirmedRoots = roots.filter(r => r.tipo !== 'posible');
  if (confirmedRoots.length > 0) {
    html += '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:.75rem;padding:0 1.5rem 1rem;">';
    confirmedRoots.forEach((r, i) => {
      const col  = COLORS[i % COLORS.length];
      const meta = TIPO_META[r.tipo] || TIPO_META.cambio_signo;
      let fVal = '?';
      try { fVal = evalF(expr, r.root).toExponential(3); } catch(e) {}

      /* Determinar si es raíz exacta real */
      const isExact = r.tipo === 'exacta';
      const typeLabel = isExact
        ? '<span style="background:#f0fdf4;color:#065f46;font-family:var(--font-main);font-size:.62rem;font-weight:700;padding:.1rem .45rem;border-radius:4px;border:1px solid #6ee7b7;">✓ Real exacta</span>'
        : '<span style="background:#eff6ff;color:#1d4ed8;font-family:var(--font-main);font-size:.62rem;font-weight:700;padding:.1rem .45rem;border-radius:4px;border:1px solid #93c5fd;">✓ Real</span>';

      html += '<div style="border-radius:var(--radius-sm);border:1.5px solid ' + col + '33;border-left:5px solid ' + col + ';padding:.875rem 1rem;background:var(--gray-50);">';
      html += '<div style="display:flex;align-items:center;gap:.4rem;margin-bottom:.5rem;flex-wrap:wrap;">';
      html += '<span style="background:' + col + ';color:#fff;font-family:var(--font-main);font-size:.65rem;font-weight:700;padding:.15rem .55rem;border-radius:4px;">r' + r.rootNum + '</span>';
      html += typeLabel;
      html += '<span style="background:' + meta.bg + ';color:' + meta.color + ';font-family:var(--font-main);font-size:.62rem;font-weight:600;padding:.1rem .45rem;border-radius:4px;border:1px solid ' + meta.border + ';">' + meta.badge + '</span>';
      if (r.result) html += '<span style="font-family:var(--font-main);font-size:.62rem;color:var(--gray-400);margin-left:auto;">' + r.result.iterations + ' iter.</span>';
      html += '</div>';
      html += '<div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:' + col + ';margin-bottom:.25rem;">' + r.root.toFixed(8) + '</div>';
      html += '<div style="font-family:var(--font-mono);font-size:.72rem;color:var(--gray-500);">f(r) ≈ ' + fVal + '</div>';
      html += '<div style="font-family:var(--font-main);font-size:.7rem;color:var(--gray-400);margin-top:.2rem;">[' + r.interval.a.toFixed(4) + ', ' + r.interval.b.toFixed(4) + ']</div>';
      html += '</div>';
    });
    html += '</div>';

    /* Nota sobre raíces complejas */
    html += '<div style="padding:.5rem 1.5rem 1rem;font-family:var(--font-main);font-size:.78rem;color:var(--gray-500);">';
    html += '💡 Solo se muestran raíces <strong>reales</strong>. Los métodos numéricos de esta sección operan en ℝ. ';
    html += 'Si el polinomio tiene raíces complejas (no cruzarán el eje x), usa <strong>Tema 3 → Bairstow o Müller</strong> para encontrarlas.';
    html += '</div>';
  } else {
    html += '<div style="padding:1rem 1.5rem;font-family:var(--font-main);font-size:.88rem;color:var(--gray-500);">No se detectaron raíces confirmadas. Pruebe un rango más amplio o un paso más pequeño.</div>';
  }
  html += '</div>'; /* cierre card resumen */

  /* ── 2. Raíces posibles (sección separada) ── */
  if (nPosible > 0) {
    html += '<div class="card" style="margin-bottom:1.25rem;border-left:4px solid var(--warning);">';
    html += '<div class="card-header"><div class="card-header-icon amber">❓</div>';
    html += '<div><div class="card-title">Candidatos Posibles — Verificación Manual</div>';
    html += '<div class="card-subtitle">|f(x)| &lt; 1×10⁻⁶ en el muestreo, sin cambio de signo detectado. Pueden ser raíces de multiplicidad par o mínimos.</div></div></div>';
    html += '<div style="overflow-x:auto;"><table style="width:100%;border-collapse:collapse;font-size:.82rem;">';
    html += '<thead><tr style="background:var(--warning-light);">';
    ['x candidato','f(x)','Tipo','Sugerencia'].forEach(h2 => {
      html += '<th style="padding:.6rem 1rem;text-align:left;font-family:var(--font-main);font-size:.7rem;font-weight:700;color:#92400e;border-bottom:2px solid #fcd34d;">' + h2 + '</th>';
    });
    html += '</tr></thead><tbody>';
    roots.filter(r => r.tipo === 'posible').forEach(r => {
      const fx = r.fxVal !== undefined ? r.fxVal.toExponential(4) : '?';
      const tdS = 'padding:.55rem 1rem;border-bottom:1px solid var(--warning-light);font-family:var(--font-mono);font-size:.8rem;';
      html += '<tr>';
      html += '<td style="' + tdS + 'font-weight:600;color:#92400e;">' + r.root.toFixed(8) + '</td>';
      html += '<td style="' + tdS + '">' + fx + '</td>';
      html += '<td style="' + tdS + '"><span style="background:var(--warning-light);color:#92400e;padding:.1rem .4rem;border-radius:4px;font-family:var(--font-main);font-size:.68rem;font-weight:600;">posible</span></td>';
      html += '<td style="' + tdS + 'font-family:var(--font-main);font-size:.78rem;color:var(--gray-500);">Verificar manualmente o reducir el paso</td>';
      html += '</tr>';
    });
    html += '</tbody></table></div></div>';
  }

  /* ── 3. Subintervalos detectados ── */
  if (intervalsDetected.length > 0) {
    html += '<div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">';
    html += '<div style="padding:1rem 1.5rem .75rem;border-bottom:1px solid var(--border);display:flex;align-items:center;gap:.75rem;">';
    html += '<div class="card-header-icon purple">📍</div>';
    html += '<div><div class="card-title">Subintervalos con Cambio de Signo</div>';
    html += '<div class="card-subtitle">f(a)·f(b) &lt; 0 garantiza al menos una raíz en cada intervalo (Teorema de Bolzano)</div></div></div>';
    html += '<div style="overflow-x:auto;"><table style="width:100%;border-collapse:collapse;font-size:.82rem;">';
    html += '<thead><tr style="background:var(--primary-light);">';
    ['#','[a, b]','f(a)','f(b)','f(a)·f(b)','Raíz encontrada'].forEach(h2 => {
      html += '<th style="padding:.6rem 1rem;text-align:left;font-family:var(--font-main);font-size:.7rem;font-weight:700;color:var(--primary-dark);border-bottom:2px solid #a5b4fc;white-space:nowrap;">' + h2 + '</th>';
    });
    html += '</tr></thead><tbody>';
    intervalsDetected.forEach(({ a, b, fa, fb }, i) => {
      /* Buscar la raíz que corresponde a este intervalo (comparación aproximada) */
      const matchingRoot = roots.find(r =>
        r.interval && Math.abs(r.interval.a - a) < 1e-9 && Math.abs(r.interval.b - b) < 1e-9
      ) || roots.find(r =>
        r.interval && r.root >= a - 1e-6 && r.root <= b + 1e-6
      );
      const rootVal = matchingRoot ? matchingRoot.root.toFixed(8) : '—';
      const col = COLORS[(matchingRoot ? matchingRoot.rootNum - 1 : i) % COLORS.length];
      const tdS = 'padding:.55rem 1rem;border-bottom:1px solid var(--primary-light);font-family:var(--font-mono);font-size:.8rem;';
      html += '<tr>';
      html += '<td style="' + tdS + 'font-family:var(--font-main);font-weight:700;color:var(--primary-dark);">' + (i+1) + '</td>';
      html += '<td style="' + tdS + '">[' + a.toFixed(4) + ', ' + b.toFixed(4) + ']</td>';
      html += '<td style="' + tdS + 'color:' + (fa<0?'var(--danger)':'var(--success)') + ';">' + fa.toFixed(6) + '</td>';
      html += '<td style="' + tdS + 'color:' + (fb<0?'var(--danger)':'var(--success)') + ';">' + fb.toFixed(6) + '</td>';
      html += '<td style="' + tdS + '"><span style="color:var(--danger);font-weight:600;">' + (fa*fb).toExponential(3) + ' &lt; 0</span></td>';
      html += '<td style="' + tdS + 'color:' + col + ';font-weight:600;">' + rootVal + '</td>';
      html += '</tr>';
    });
    html += '</tbody></table></div></div>';
  }

  /* ── 4. Iteraciones por raíz ── */
  const rootsConIter = roots.filter(r => r.result && r.result.rows.length > 0);
  if (rootsConIter.length > 0) {
    html += '<div class="card" style="margin-bottom:1.25rem;">';
    html += '<div class="card-header"><div class="card-header-icon purple">📋</div>';
    html += '<div><div class="card-title">Iteraciones por Raíz</div>';
    html += '<div class="card-subtitle">Tabla completa del método aplicado en cada subintervalo</div></div></div>';
    html += '<div style="padding:1.25rem 1.5rem;">';

    rootsConIter.forEach((r, i) => {
      const col  = COLORS[roots.indexOf(r) % COLORS.length];
      const meta = TIPO_META[r.tipo] || TIPO_META.cambio_signo;
      let fVal = '?';
      try { fVal = evalF(expr, r.root).toExponential(3); } catch(e) {}

      html += '<div style="margin-bottom:1.25rem;">';
      html += '<div style="display:flex;align-items:center;gap:.75rem;margin-bottom:.65rem;padding:.65rem 1rem;';
      html += 'background:' + col + '0D;border-radius:var(--radius-sm);border:1.5px solid ' + col + '33;">';
      html += '<span style="background:' + col + ';color:#fff;font-family:var(--font-main);font-size:.78rem;font-weight:700;padding:.25rem .7rem;border-radius:5px;">r' + r.rootNum + '</span>';
      html += '<span style="background:' + meta.bg + ';color:' + meta.color + ';font-family:var(--font-main);font-size:.65rem;font-weight:600;padding:.1rem .45rem;border-radius:4px;border:1px solid ' + meta.border + ';">' + meta.badge + '</span>';
      html += '<div style="flex:1;">';
      html += '<div style="font-family:var(--font-mono);font-size:.95rem;font-weight:700;color:' + col + ';">' + r.root.toFixed(8) + '</div>';
      html += '<div style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);margin-top:2px;">';
      html += '[' + r.interval.a.toFixed(4) + ', ' + r.interval.b.toFixed(4) + ']';
      html += ' · ' + r.result.iterations + ' iter.';
      html += ' · ' + (r.result.converged ? '<span style="color:var(--success);">✓ Convergió</span>' : '<span style="color:var(--warning);">⚠ Máx. iter.</span>');
      html += ' · f(r) ≈ ' + fVal;
      html += '</div></div>';
      html += '<span style="font-family:var(--font-main);font-size:.7rem;color:var(--gray-400);">' + methodLabel + '</span>';
      html += '</div>';

      if (buildTableFn) html += buildTableFn(r.result.rows);
      html += '</div>';
    });

    html += '</div></div>';
  }

  container.innerHTML = html;
}


function rowClass(r) { return r.converged ? ' class="converged-row"' : ""; }

function buildBisectionTable(rows) {
  const hdr = `<tr><th>#</th><th>a</th><th>b</th><th>xr</th><th>f(a)</th><th>f(b)</th><th>f(xr)</th><th>Ea</th><th>Er%</th></tr>`;
  const bdy = rows.map(r => `<tr${rowClass(r)}>
    <td>${r.iter}</td><td>${fmt(r.a)}</td><td>${fmt(r.b)}</td><td>${fmt(r.xr)}</td>
    <td>${fmt(r.fa)}</td><td>${fmt(r.fb)}</td><td>${fmt(r.fxr)}</td>
    <td>${r.ea !== null ? fmtSci(r.ea) : "—"}</td>
    <td>${r.er !== null ? fmt(r.er, 4) : "—"}</td></tr>`).join("");
  return wrap(hdr, bdy);
}

function buildNewtonTable(rows) {
  const hdr = `<tr><th>#</th><th>x_i</th><th>f(x_i)</th><th>f'(x_i)</th><th>x_{i+1}</th><th>Ea</th><th>Er%</th></tr>`;
  const bdy = rows.map(r => `<tr${rowClass(r)}>
    <td>${r.iter}</td><td>${fmt(r.x)}</td><td>${fmt(r.fx)}</td><td>${fmt(r.fpx)}</td>
    <td>${fmt(r.x1)}</td>
    <td>${r.ea !== null ? fmtSci(r.ea) : "—"}</td>
    <td>${r.er !== null ? fmt(r.er, 4) : "—"}</td></tr>`).join("");
  return wrap(hdr, bdy);
}

function buildSecantTable(rows) {
  const hdr = `<tr><th>#</th><th>x₀</th><th>x₁</th><th>f(x₀)</th><th>f(x₁)</th><th>x₂</th><th>Ea</th><th>Er%</th></tr>`;
  const bdy = rows.map(r => `<tr${rowClass(r)}>
    <td>${r.iter}</td><td>${fmt(r.x0)}</td><td>${fmt(r.x1)}</td>
    <td>${fmt(r.fx0)}</td><td>${fmt(r.fx1)}</td><td>${fmt(r.x2)}</td>
    <td>${r.ea !== null ? fmtSci(r.ea) : "—"}</td>
    <td>${r.er !== null ? fmt(r.er, 4) : "—"}</td></tr>`).join("");
  return wrap(hdr, bdy);
}

/* buildFixedTable — definido en la sección LABORATORIO DE TRANSFORMADAS */

function wrap(hdr, bdy) {
  return `<div class="table-wrapper"><table><thead>${hdr}</thead><tbody>${bdy}</tbody></table></div>`;
}

/* ══════════════════════════════════════════════════════════════
   4. UI HELPERS
══════════════════════════════════════════════════════════════ */

function showAlert(id, type, msg) {
  const icons = { success: "✓", danger: "✕", warning: "⚠", info: "ℹ" };
  const el = document.getElementById(id);
  if (el) el.innerHTML = `<div class="alert alert-${type}"><span class="alert-icon">${icons[type]||"•"}</span><span>${msg}</span></div>`;
}

function clearAlert(id) {
  const el = document.getElementById(id);
  if (el) el.innerHTML = "";
}

function getVal(id)  { return document.getElementById(id)?.value?.trim() ?? ""; }
function getNum(id)  { return parseFloat(document.getElementById(id)?.value ?? ""); }
function getInt(id)  { return parseInt(document.getElementById(id)?.value  ?? ""); }

function validate(checks) {
  for (const [cond, msg] of checks) if (cond) return msg;
  return null;
}

/* ══════════════════════════════════════════════════════════════
   5. NAVEGACIÓN DE TEMAS
══════════════════════════════════════════════════════════════ */

function switchTheme(themeId) {
  /* Ocultar todos los paneles de tema */
  document.querySelectorAll(".theme-panel").forEach(p => p.classList.remove("active"));
  document.querySelectorAll(".theme-tab").forEach(t => t.classList.remove("active"));

  const panel = document.getElementById("panel-" + themeId);
  const tab   = document.querySelector(`.theme-tab[data-theme="${themeId}"]`);

  if (panel) panel.classList.add("active");
  if (tab)   tab.classList.add("active");

  state.currentTheme = themeId;

  /* Si es t2, renderizar gráfica si esa sección está activa */
  if (themeId === "t2" && state.currentSection === "graph") graphDraw();
}

/* ══════════════════════════════════════════════════════════════
   6. NAVEGACIÓN INTERNA (Tema 2)
══════════════════════════════════════════════════════════════ */

function navigateTo(sectionId) {
  document.querySelectorAll(".section").forEach(s => s.classList.remove("active"));
  document.querySelectorAll(".nav-item").forEach(n => n.classList.remove("active"));
  document.querySelectorAll(".mobile-inner-item").forEach(n => n.classList.remove("active"));

  const sec = document.getElementById("sec-" + sectionId);
  if (sec) sec.classList.add("active");

  document.querySelectorAll(`[data-nav="${sectionId}"]`).forEach(el => el.classList.add("active"));

  state.currentSection = sectionId;

  if (sectionId === "graph") {
    const gf = document.getElementById("graph_func");
    if (gf && !gf.value && state.lastFunction) gf.value = state.lastFunction;
    renderGraph();
  }
}

/* ══════════════════════════════════════════════════════════════
   7. VERIFICACIÓN
══════════════════════════════════════════════════════════════ */

document.getElementById("btnVerify").addEventListener("click", () => {
  clearAlert("verifyAlert");
  document.getElementById("verifyResults").innerHTML = "";

  const expr = getVal("funcInput");
  const a    = getNum("intervalA");
  const b    = getNum("intervalB");

  const err = validate([
    [!expr,      "Ingrese una función f(x)."],
    [isNaN(a),   "El valor de 'a' debe ser numérico."],
    [isNaN(b),   "El valor de 'b' debe ser numérico."],
    [a >= b,     "Se requiere a < b."],
  ]);
  if (err) { showAlert("verifyAlert", "danger", err); return; }

  try {
    const mid  = (a + b) / 2;
    const fa   = evalF(expr, a);
    const fb   = evalF(expr, b);
    const fmid = evalF(expr, mid);
    const sc   = fa * fb < 0;

    document.getElementById("verifyResults").innerHTML = `
      <div class="verify-grid">
        <div class="verify-item">
          <div class="label">f(a) = f(${a})</div>
          <div class="value">${fmt(fa)}</div>
        </div>
        <div class="verify-item">
          <div class="label">f((a+b)/2) = f(${fmt(mid,3)})</div>
          <div class="value">${fmt(fmid)}</div>
        </div>
        <div class="verify-item">
          <div class="label">f(b) = f(${b})</div>
          <div class="value">${fmt(fb)}</div>
        </div>
      </div>
      <div class="sign-status ${sc ? "ok" : "warn"}">
        <span>${sc ? "✓" : "⚠"}</span>
        ${sc
          ? `Cambio de signo confirmado en [${a}, ${b}] — existe al menos una raíz (Teorema de Bolzano).`
          : `Sin cambio de signo en [${a}, ${b}]. Puede no haber raíz real o haber raíces de multiplicidad par.`}
      </div>`;

    showAlert("verifyAlert", "success", `Función verificada: f(x) = ${expr}`);
    syncFuncToMethods(expr, a, b);
  } catch (e) {
    showAlert("verifyAlert", "danger", e.message);
  }
});

function syncFuncToMethods(expr, a, b) {
  ["bisect","false","newton","secant","fixed"].forEach(id => {
    const el = document.getElementById("func_" + id);
    if (el) el.value = expr;
  });
  [["bisect_a",a],["bisect_b",b],["false_a",a],["false_b",b]].forEach(([id,v]) => {
    const el = document.getElementById(id);
    if (el) el.value = v;
  });
  const mid = (a + b) / 2;
  ["newton_x0","fixed_x0"].forEach(id => {
    const el = document.getElementById(id);
    if (el && !el.value) el.value = mid.toFixed(4);
  });
  const sx0 = document.getElementById("sec_x0"), sx1 = document.getElementById("sec_x1");
  if (sx0 && !sx0.value) sx0.value = a;
  if (sx1 && !sx1.value) sx1.value = b;
}

/* ══════════════════════════════════════════════════════════════
   8. MÉTODO TABS
══════════════════════════════════════════════════════════════ */

document.querySelectorAll(".method-tab").forEach(tab => {
  tab.addEventListener("click", () => {
    document.querySelectorAll(".method-tab").forEach(t => t.classList.remove("active"));
    document.querySelectorAll(".method-panel").forEach(p => p.classList.remove("active"));
    tab.classList.add("active");
    document.getElementById("panel-" + tab.dataset.method).classList.add("active");
    document.getElementById("methodIterTable").innerHTML = "";
    ["bisectAlert","falseAlert","newtonAlert","secantAlert","fixedAlert"].forEach(clearAlert);
  });
});

/* ══════════════════════════════════════════════════════════════
   9. EJECUTAR MÉTODOS
══════════════════════════════════════════════════════════════ */

function handleResult(res, method, expr, tableHtml) {
  const { root, rows, converged, iterations } = res;
  const last = rows.at(-1);

  state.lastRoot      = root;
  state.lastMethod    = method;
  state.lastFunction  = expr;
  state.lastAllRoots  = [];    // modo normal: limpiar raíces múltiples

  document.getElementById("methodIterTable").innerHTML = tableHtml;

  updateResults(method, expr, root, last.ea, last.er, iterations, converged);
  saveToHistory(method, expr, root, last.ea, last.er, iterations, converged);

  /* Mostrar botón de descarga T2 */
  if (typeof numerixExport !== 'undefined') numerixExport.showT2Bar();

  /* En mobile, hacer scroll al resultado */
  if (window.innerWidth <= 768) {
    setTimeout(() => {
      const el = document.getElementById('methodIterTable');
      if (el) el.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }, 100);
  }

  return converged
    ? `Convergencia en ${iterations} iteración(es). Raíz ≈ ${fmt(root,8)}`
    : `Máximo de ${iterations} iteraciones alcanzado. Raíz aprox ≈ ${fmt(root,8)}`;
}

/* Bisección */
document.getElementById("btnBisect").addEventListener("click", () => {
  clearAlert("bisectAlert");
  document.getElementById("methodIterTable").innerHTML = "";
  const expr = getVal("func_bisect");
  const mode = document.querySelector('input[name="bisect_mode"]:checked')?.value || 'single';
  const tol  = getNum(mode === 'auto' ? "bisect_tol_auto" : "bisect_tol");
  if (checkUpperX(expr, "bisectAlert")) return;
  const it   = getInt("bisect_iter") || 100;

  if (mode === 'auto') {
    const A    = getNum("bisect_A");
    const B    = getNum("bisect_B");
    const stepUsuario = getNum("bisect_step") || 0.5;
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(A),"Rango A inválido."], [isNaN(B),"Rango B inválido."],
      [A>=B,"Se requiere A < B."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
      [stepUsuario<=0,"El paso debe ser positivo."],
    ]);
    if (err) { showAlert("bisectAlert","danger",err); return; }
    try {
      const data = autoAllRoots(expr, A, B, stepUsuario, tol, it, 'bisection');
      /* Guardar todas las raíces para la gráfica */
      state.lastFunction  = expr;
      state.lastRoot      = null;
      state.lastAllRoots  = data.roots
        .filter(r => r.tipo !== 'posible' && isFinite(r.root))
        .map(r => r.root);
      renderMultiRootsResult(data, expr, 'Bisección', buildBisectionTable, A, B, stepUsuario);
      if (typeof numerixExport !== 'undefined') numerixExport.showT2Bar();
      const n = data.roots.length;
      showAlert("bisectAlert", n > 0 ? "success" : "warning",
        n > 0
          ? n + ' raíz' + (n>1?'ces':'') + ' encontrada' + (n>1?'s':'') + ' en [' + A + ', ' + B + ']. ' + data.intervalsDetected.length + ' subintervalo' + (data.intervalsDetected.length>1?'s':'') + ' detectado' + (data.intervalsDetected.length>1?'s':'') + '.'
          : 'No se encontraron raíces en [' + A + ', ' + B + ']. Pruebe un rango más amplio o un paso más pequeño.');
    } catch(e) { showAlert("bisectAlert","danger",e.message); }
  } else {
    const a = getNum("bisect_a"), b = getNum("bisect_b");
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(a),"'a' inválido."], [isNaN(b),"'b' inválido."],
      [a>=b,"Se requiere a < b."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
      [isNaN(it)||it<1,"Máx. iteraciones inválido."],
    ]);
    if (err) { showAlert("bisectAlert","danger",err); return; }
    try {
      const res = bisection(expr, a, b, tol, it);
      const msg = handleResult(res, "Bisección", expr, buildBisectionTable(res.rows));
      showAlert("bisectAlert", res.converged ? "success" : "warning", msg);
    } catch(e) { showAlert("bisectAlert","danger",e.message); }
  }
});

/* Regla Falsa */
document.getElementById("btnFalse").addEventListener("click", () => {
  clearAlert("falseAlert");
  document.getElementById("methodIterTable").innerHTML = "";
  const expr = getVal("func_false");
  const mode = document.querySelector('input[name="false_mode"]:checked')?.value || 'single';
  const tol  = getNum(mode === 'auto' ? "false_tol_auto" : "false_tol");
  if (checkUpperX(expr, "falseAlert")) return;
  const it   = getInt("false_iter") || 100;

  if (mode === 'auto') {
    const A    = getNum("false_A");
    const B    = getNum("false_B");
    const stepUsuario = getNum("false_step") || 0.5;
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(A),"Rango A inválido."], [isNaN(B),"Rango B inválido."],
      [A>=B,"Se requiere A < B."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
      [stepUsuario<=0,"El paso debe ser positivo."],
    ]);
    if (err) { showAlert("falseAlert","danger",err); return; }
    try {
      const data = autoAllRoots(expr, A, B, stepUsuario, tol, it, 'false');
      /* Guardar todas las raíces para la gráfica */
      state.lastFunction  = expr;
      state.lastRoot      = null;
      state.lastAllRoots  = data.roots
        .filter(r => r.tipo !== 'posible' && isFinite(r.root))
        .map(r => r.root);
      renderMultiRootsResult(data, expr, 'Regla Falsa', buildBisectionTable, A, B, stepUsuario);
      if (typeof numerixExport !== 'undefined') numerixExport.showT2Bar();
      const n = data.roots.length;
      showAlert("falseAlert", n > 0 ? "success" : "warning",
        n > 0
          ? n + ' raíz' + (n>1?'ces':'') + ' encontrada' + (n>1?'s':'') + ' en [' + A + ', ' + B + '].'
          : 'No se encontraron raíces en [' + A + ', ' + B + '].');
    } catch(e) { showAlert("falseAlert","danger",e.message); }
  } else {
    const a = getNum("false_a"), b = getNum("false_b");
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(a),"'a' inválido."], [isNaN(b),"'b' inválido."],
      [a>=b,"Se requiere a < b."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
    ]);
    if (err) { showAlert("falseAlert","danger",err); return; }
    try {
      const res = falsePosition(expr, a, b, tol, it);
      const msg = handleResult(res, "Regla Falsa", expr, buildBisectionTable(res.rows));
      showAlert("falseAlert", res.converged ? "success" : "warning", msg);
    } catch(e) { showAlert("falseAlert","danger",e.message); }
  }
});

/* Newton-Raphson */
document.getElementById("btnNewton").addEventListener("click", () => {
  clearAlert("newtonAlert");
  document.getElementById("methodIterTable").innerHTML = "";
  const expr = getVal("func_newton");
  const mode = document.querySelector('input[name="newton_mode"]:checked')?.value || 'single';
  const tol  = getNum(mode === 'auto' ? "newton_tol_auto" : "newton_tol");
  if (checkUpperX(expr, "newtonAlert")) return;
  const it   = getInt("newton_iter") || 100;

  if (mode === 'auto') {
    const A    = getNum("newton_A");
    const B    = getNum("newton_B");
    const stepUsuario = getNum("newton_step") || 0.5;
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(A),"Rango A inválido."], [isNaN(B),"Rango B inválido."],
      [A>=B,"Se requiere A < B."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
      [stepUsuario<=0,"El paso debe ser positivo."],
    ]);
    if (err) { showAlert("newtonAlert","danger",err); return; }
    try {
      const data = autoAllRoots(expr, A, B, stepUsuario, tol, it, 'newton');
      /* Guardar todas las raíces para la gráfica */
      state.lastFunction  = expr;
      state.lastRoot      = null;
      state.lastAllRoots  = data.roots
        .filter(r => r.tipo !== 'posible' && isFinite(r.root))
        .map(r => r.root);
      renderMultiRootsResult(data, expr, 'Newton-Raphson', buildNewtonTable, A, B, stepUsuario);
      if (typeof numerixExport !== 'undefined') numerixExport.showT2Bar();
      const n = data.roots.length;
      showAlert("newtonAlert", n > 0 ? "success" : "warning",
        n > 0
          ? n + ' raíz' + (n>1?'ces':'') + ' encontrada' + (n>1?'s':'') + ' en [' + A + ', ' + B + '].'
          : 'No se encontraron raíces en [' + A + ', ' + B + '].');
    } catch(e) { showAlert("newtonAlert","danger",e.message); }
  } else {
    const x0 = getNum("newton_x0");
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(x0),"x₀ inválido."],
      [isNaN(tol)||tol<=0,"Tolerancia inválida."],
    ]);
    if (err) { showAlert("newtonAlert","danger",err); return; }
    try {
      const res = newtonRaphson(expr, x0, tol, it);
      const msg = handleResult(res, "Newton-Raphson", expr, buildNewtonTable(res.rows));
      showAlert("newtonAlert", res.converged ? "success" : "warning", msg);
    } catch(e) { showAlert("newtonAlert","danger",e.message); }
  }
});

/* Secante */
document.getElementById("btnSecant").addEventListener("click", () => {
  clearAlert("secantAlert");
  document.getElementById("methodIterTable").innerHTML = "";
  const expr = getVal("func_secant");
  const mode = document.querySelector('input[name="secant_mode"]:checked')?.value || 'single';
  const tol  = getNum(mode === 'auto' ? "secant_tol_auto" : "sec_tol");
  if (checkUpperX(expr, "secantAlert")) return;
  const it   = getInt("sec_iter") || 100;

  if (mode === 'auto') {
    const A    = getNum("secant_A");
    const B    = getNum("secant_B");
    const stepUsuario = getNum("secant_step") || 0.5;
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(A),"Rango A inválido."], [isNaN(B),"Rango B inválido."],
      [A>=B,"Se requiere A < B."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
      [stepUsuario<=0,"El paso debe ser positivo."],
    ]);
    if (err) { showAlert("secantAlert","danger",err); return; }
    try {
      const data = autoAllRoots(expr, A, B, stepUsuario, tol, it, 'secant');
      /* Guardar todas las raíces para la gráfica */
      state.lastFunction  = expr;
      state.lastRoot      = null;
      state.lastAllRoots  = data.roots
        .filter(r => r.tipo !== 'posible' && isFinite(r.root))
        .map(r => r.root);
      renderMultiRootsResult(data, expr, 'Secante', buildSecantTable, A, B, stepUsuario);
      if (typeof numerixExport !== 'undefined') numerixExport.showT2Bar();
      const n = data.roots.length;
      showAlert("secantAlert", n > 0 ? "success" : "warning",
        n > 0
          ? n + ' raíz' + (n>1?'ces':'') + ' encontrada' + (n>1?'s':'') + ' en [' + A + ', ' + B + '].'
          : 'No se encontraron raíces en [' + A + ', ' + B + '].');
    } catch(e) { showAlert("secantAlert","danger",e.message); }
  } else {
    const x0 = getNum("sec_x0"), x1 = getNum("sec_x1");
    const err = validate([
      [!expr,"Ingrese f(x)."], [isNaN(x0),"x₀ inválido."], [isNaN(x1),"x₁ inválido."],
      [x0===x1,"x₀ y x₁ no pueden ser iguales."], [isNaN(tol)||tol<=0,"Tolerancia inválida."],
    ]);
    if (err) { showAlert("secantAlert","danger",err); return; }
    try {
      const res = secant(expr, x0, x1, tol, it);
      const msg = handleResult(res, "Secante", expr, buildSecantTable(res.rows));
      showAlert("secantAlert", res.converged ? "success" : "warning", msg);
    } catch(e) { showAlert("secantAlert","danger",e.message); }
  }
});

/* Punto Fijo — manejado por el laboratorio (ver sección LABORATORIO DE TRANSFORMADAS) */

/* ══════════════════════════════════════════════════════════════
   10. RESULTADOS
══════════════════════════════════════════════════════════════ */

function updateResults(method, expr, root, ea, er, iterations, converged) {
  const badge = converged
    ? `<span class="badge badge-success">✓ Convergió</span>`
    : `<span class="badge badge-warning">⚠ No convergió</span>`;

  document.getElementById("resultsContent").innerHTML = `
    <div class="results-grid">
      <div class="result-card">
        <div class="result-label">Método</div>
        <div class="result-value" style="font-size:.9rem;font-family:var(--font-main);">${method}</div>
      </div>
      <div class="result-card">
        <div class="result-label">Raíz aproximada</div>
        <div class="result-value highlight">${fmt(root, 10)}</div>
      </div>
      <div class="result-card">
        <div class="result-label">Error absoluto Ea</div>
        <div class="result-value">${ea !== null ? fmtSci(ea) : "N/A"}</div>
      </div>
      <div class="result-card">
        <div class="result-label">Error relativo Er%</div>
        <div class="result-value">${er !== null ? fmt(er,6)+"%" : "N/A"}</div>
      </div>
      <div class="result-card">
        <div class="result-label">Iteraciones</div>
        <div class="result-value">${iterations}</div>
      </div>
      <div class="result-card">
        <div class="result-label">Estado</div>
        <div class="result-value" style="font-family:var(--font-main);font-size:.88rem;">${badge}</div>
      </div>
    </div>
    <hr class="divider">
    <div style="display:flex;gap:1rem;flex-wrap:wrap;align-items:center;">
      <span class="text-muted">Función:</span>
      <code style="font-family:var(--font-mono);font-size:.88rem;background:var(--gray-100);padding:2px 8px;border-radius:4px;">f(x) = ${expr}</code>
      <span class="text-muted">f(x*) ≈</span>
      <code style="font-family:var(--font-mono);font-size:.88rem;background:var(--gray-100);padding:2px 8px;border-radius:4px;">${fmtSci(safeEval(expr,root))}</code>
    </div>
    <div class="btn-group">
      <button class="btn btn-primary" onclick="navigateTo('graph')">📈 Ver Gráfica</button>
      <button class="btn btn-secondary" onclick="navigateTo('history')">📋 Ver Historial</button>
    </div>`;
}

/* ══════════════════════════════════════════════════════════════
   11. HISTORIAL
══════════════════════════════════════════════════════════════ */

const HISTORY_KEY = "nm_history_v2";

function loadHistory()    { try { return JSON.parse(localStorage.getItem(HISTORY_KEY)) || []; } catch { return []; } }
function saveHistoryData(d) { localStorage.setItem(HISTORY_KEY, JSON.stringify(d)); }

function saveToHistory(method, expr, root, ea, er, iterations, converged) {
  const items = loadHistory();
  items.unshift({ id: Date.now(), date: new Date().toLocaleString("es-ES"), method, expr, root, ea, er, iterations, converged });
  if (items.length > 50) items.pop();
  saveHistoryData(items);
  renderHistory();
}

function renderHistory() {
  const items = loadHistory();
  document.getElementById("historyCount").textContent = `${items.length} registro(s)`;

  if (!items.length) {
    document.getElementById("historyList").innerHTML = `
      <div class="history-empty">
        <div class="empty-icon">📂</div>
        <p>El historial está vacío.</p>
        <p class="text-muted mt-1" style="font-size:.82rem;">Los resultados se guardan aquí automáticamente.</p>
      </div>`;
    return;
  }

  document.getElementById("historyList").innerHTML = items.map(item => `
    <div class="history-item">
      <div class="history-badge">${item.method}</div>
      <div class="history-info">
        <div class="history-func">f(x) = ${item.expr}</div>
        <div class="history-meta">${item.date} · ${item.iterations} iter · ${item.converged ? "Convergió" : "No convergió"}</div>
      </div>
      <div class="history-root">x* ≈ ${Number(item.root).toFixed(6)}</div>
      <div class="history-actions">
        <button class="btn btn-sm btn-secondary" onclick="loadFromHistory(${item.id})">↑ Cargar</button>
        <button class="btn btn-sm btn-danger"    onclick="deleteHistoryItem(${item.id})">✕</button>
      </div>
    </div>`).join("");
}

function loadFromHistory(id) {
  const item = loadHistory().find(i => i.id === id);
  if (!item) return;
  document.getElementById("funcInput").value = item.expr;
  ["bisect","false","newton","secant","fixed"].forEach(m => {
    const el = document.getElementById("func_" + m);
    if (el) el.value = item.expr;
  });
  navigateTo("verify");
  showAlert("verifyAlert", "info", `Función cargada desde historial: f(x) = ${item.expr}`);
}

function deleteHistoryItem(id) {
  saveHistoryData(loadHistory().filter(i => i.id !== id));
  renderHistory();
}

document.getElementById("btnClearHistory").addEventListener("click", () => {
  if (confirm("¿Eliminar todo el historial?")) { saveHistoryData([]); renderHistory(); }
});

document.getElementById("btnExportHistory").addEventListener("click", () => {
  const items = loadHistory();
  if (!items.length) { alert("No hay historial para exportar."); return; }
  const blob = new Blob([JSON.stringify(items, null, 2)], { type: "application/json" });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement("a");
  a.href = url; a.download = "historial_metodos_numericos.json"; a.click();
  URL.revokeObjectURL(url);
});

/* ══════════════════════════════════════════════════════════════
   12. GRÁFICA CANVAS
══════════════════════════════════════════════════════════════ */

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA — Motor estilo GeoGebra
   · Pan con arrastre (mouse + touch)
   · Zoom con rueda del ratón (centrado en cursor)
   · Tooltip de coordenadas en tiempo real
   · Grid adaptativo con etiquetas limpias
   · Marcado de raíces calculadas (modo normal y automático)
   · Línea vertical de seguimiento al cursor
══════════════════════════════════════════════════════════════ */

const graph = {
  /* Vista (coordenadas matemáticas) */
  xMin: -8, xMax: 8, yMin: -6, yMax: 6,

  /* Estado de interacción */
  expr:      '',
  dragging:  false,
  lastMouse: { x: 0, y: 0 },
  mouseWorld:{ x: 0, y: 0 },   // posición del cursor en coordenadas matemáticas
  hoverOn:   false,

  /* Canvas */
  canvas: null,
  ctx:    null,

  /* Colores */
  C: {
    bg:       '#ffffff',
    grid:     '#f1f5f9',
    gridMaj:  '#e2e8f0',
    axis:     '#94a3b8',
    axisNum:  '#94a3b8',
    curve:    '#4f46e5',
    zero:     '#10b981',
    root:     '#ef4444',
    rootAuto: ['#ef4444','#6366f1','#10b981','#f59e0b','#ec4899','#14b8a6','#8b5cf6'],
    hover:    'rgba(79,70,229,0.08)',
    crosshair:'rgba(100,116,139,0.4)',
  },
};

function graphInit() {
  const canvas = document.getElementById('graphCanvas');
  if (!canvas) return;
  graph.canvas = canvas;
  graph.ctx    = canvas.getContext('2d');

  /* Tamaño responsivo */
  graphResize();
  window.addEventListener('resize', graphResize);

  /* ── Eventos mouse ── */
  canvas.addEventListener('mousedown', e => {
    graph.dragging  = true;
    graph.lastMouse = { x: e.clientX, y: e.clientY };
    canvas.style.cursor = 'grabbing';
  });
  canvas.addEventListener('mouseup',   () => { graph.dragging = false; canvas.style.cursor = 'crosshair'; });
  canvas.addEventListener('mouseleave',() => {
    graph.dragging = false;
    graph.hoverOn  = false;
    canvas.style.cursor = 'crosshair';
    document.getElementById('graphCoords').innerHTML = 'x = — &nbsp; y = —';
    graphDraw();
  });
  canvas.addEventListener('mousemove', e => {
    const rect = canvas.getBoundingClientRect();
    const px   = (e.clientX - rect.left) * (canvas.width  / rect.width);
    const py   = (e.clientY - rect.top)  * (canvas.height / rect.height);
    graph.mouseWorld = graphToWorld(px, py);
    graph.hoverOn    = true;

    /* Actualizar coordenadas */
    const wx = graph.mouseWorld.x, wy = graph.mouseWorld.y;
    document.getElementById('graphCoords').innerHTML =
      `x = ${fmtCoord(wx)} &nbsp; y = ${fmtCoord(wy)}`;

    /* Tooltip con f(x) si hay función */
    if (graph.expr) {
      try {
        const fy = evalF(graph.expr, wx);
        const tip = document.getElementById('graphTooltip');
        if (isFinite(fy)) {
          tip.textContent = `f(${fmtCoord(wx)}) = ${fmtCoord(fy)}`;
          const bx = px * (rect.width / canvas.width) + 14;
          const by = py * (rect.height / canvas.height) - 30;
          tip.style.left    = Math.min(bx, rect.width  - 160) + 'px';
          tip.style.top     = Math.max(by, 4)                 + 'px';
          tip.style.display = 'block';
        } else {
          tip.style.display = 'none';
        }
      } catch(e) {
        document.getElementById('graphTooltip').style.display = 'none';
      }
    }

    if (graph.dragging) {
      const dx = (e.clientX - graph.lastMouse.x) / canvas.getBoundingClientRect().width
               * (graph.xMax - graph.xMin);
      const dy = (e.clientY - graph.lastMouse.y) / canvas.getBoundingClientRect().height
               * (graph.yMax - graph.yMin);
      graph.xMin -= dx; graph.xMax -= dx;
      graph.yMin += dy; graph.yMax += dy;
      graph.lastMouse = { x: e.clientX, y: e.clientY };
    }
    graphDraw();
  });

  /* ── Zoom con rueda ── */
  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    const factor = e.deltaY > 0 ? 1.12 : 0.89;
    const rect   = canvas.getBoundingClientRect();
    const px     = (e.clientX - rect.left) * (canvas.width  / rect.width);
    const py     = (e.clientY - rect.top)  * (canvas.height / rect.height);
    const { x: wx, y: wy } = graphToWorld(px, py);

    graph.xMin = wx + (graph.xMin - wx) * factor;
    graph.xMax = wx + (graph.xMax - wx) * factor;
    graph.yMin = wy + (graph.yMin - wy) * factor;
    graph.yMax = wy + (graph.yMax - wy) * factor;
    graphDraw();
  }, { passive: false });

  /* ── Touch (mobile) ── */
  let lastTouch = null, lastPinchDist = null;
  canvas.addEventListener('touchstart', e => {
    e.preventDefault();
    if (e.touches.length === 1) {
      lastTouch = { x: e.touches[0].clientX, y: e.touches[0].clientY };
      lastPinchDist = null;
    } else if (e.touches.length === 2) {
      lastPinchDist = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
    }
  }, { passive: false });
  canvas.addEventListener('touchmove', e => {
    e.preventDefault();
    if (e.touches.length === 1 && lastTouch) {
      const rect = canvas.getBoundingClientRect();
      const dx   = (e.touches[0].clientX - lastTouch.x) / rect.width  * (graph.xMax - graph.xMin);
      const dy   = (e.touches[0].clientY - lastTouch.y) / rect.height * (graph.yMax - graph.yMin);
      graph.xMin -= dx; graph.xMax -= dx;
      graph.yMin += dy; graph.yMax += dy;
      lastTouch  = { x: e.touches[0].clientX, y: e.touches[0].clientY };
      graphDraw();
    } else if (e.touches.length === 2 && lastPinchDist) {
      const d = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
      const factor = lastPinchDist / d;
      const cx     = (graph.xMin + graph.xMax) / 2;
      const cy     = (graph.yMin + graph.yMax) / 2;
      const hw     = (graph.xMax - graph.xMin) / 2 * factor;
      const hh     = (graph.yMax - graph.yMin) / 2 * factor;
      graph.xMin   = cx - hw; graph.xMax = cx + hw;
      graph.yMin   = cy - hh; graph.yMax = cy + hh;
      lastPinchDist = d;
      graphDraw();
    }
  }, { passive: false });
  canvas.addEventListener('touchend', () => { lastTouch = null; lastPinchDist = null; });

  graphDraw();
}

function graphResize() {
  const canvas = graph.canvas;
  if (!canvas) return;
  const w = canvas.parentElement.clientWidth || 800;
  const h = Math.max(420, Math.round(w * 0.56));
  canvas.width  = w;
  canvas.height = h;
  graphDraw();
}

/* Coordenadas mundo → canvas */
function graphToCanvas(wx, wy) {
  const { canvas, xMin, xMax, yMin, yMax } = graph;
  return {
    x: (wx - xMin) / (xMax - xMin) * canvas.width,
    y: canvas.height - (wy - yMin) / (yMax - yMin) * canvas.height,
  };
}

/* Coordenadas canvas → mundo */
function graphToWorld(px, py) {
  const { canvas, xMin, xMax, yMin, yMax } = graph;
  return {
    x: xMin + (px / canvas.width)  * (xMax - xMin),
    y: yMin + (1 - py / canvas.height) * (yMax - yMin),
  };
}

/* Zoom programático centrado en origen */
function graphZoom(factor) {
  const cx = (graph.xMin + graph.xMax) / 2;
  const cy = (graph.yMin + graph.yMax) / 2;
  const hw = (graph.xMax - graph.xMin) / 2 * factor;
  const hh = (graph.yMax - graph.yMin) / 2 * factor;
  graph.xMin = cx - hw; graph.xMax = cx + hw;
  graph.yMin = cy - hh; graph.yMax = cy + hh;
  graphDraw();
}

function fmtCoord(v) {
  if (!isFinite(v)) return '—';
  const abs = Math.abs(v);
  if (abs === 0) return '0';
  if (abs >= 1000 || abs < 0.001) return v.toExponential(3);
  if (abs < 0.1)  return v.toFixed(5);
  if (abs < 10)   return v.toFixed(4);
  if (abs < 100)  return v.toFixed(3);
  return v.toFixed(2);
}

function graphNiceStep(range, targetLines) {
  const rough = range / targetLines;
  const mag   = Math.pow(10, Math.floor(Math.log10(rough)));
  const norm  = rough / mag;
  const n     = norm < 1.5 ? 1 : norm < 3.5 ? 2 : norm < 7.5 ? 5 : 10;
  return n * mag;
}

function graphDraw() {
  const { canvas, ctx, xMin, xMax, yMin, yMax, expr, C, hoverOn, mouseWorld } = graph;
  if (!ctx) return;
  const W = canvas.width, H = canvas.height;

  ctx.clearRect(0, 0, W, H);

  /* ── Fondo ── */
  ctx.fillStyle = C.bg;
  ctx.fillRect(0, 0, W, H);

  const toC = (wx, wy) => graphToCanvas(wx, wy);

  /* ── Grid secundario (líneas finas) ── */
  const xStep = graphNiceStep(xMax - xMin, 12);
  const yStep = graphNiceStep(yMax - yMin, 8);

  ctx.strokeStyle = C.grid;
  ctx.lineWidth   = 1;
  for (let gx = Math.ceil(xMin / xStep) * xStep; gx <= xMax + xStep; gx += xStep) {
    const { x: px } = toC(gx, 0);
    ctx.beginPath(); ctx.moveTo(px, 0); ctx.lineTo(px, H); ctx.stroke();
  }
  for (let gy = Math.ceil(yMin / yStep) * yStep; gy <= yMax + yStep; gy += yStep) {
    const { y: py } = toC(0, gy);
    ctx.beginPath(); ctx.moveTo(0, py); ctx.lineTo(W, py); ctx.stroke();
  }

  /* ── Ejes principales ── */
  ctx.strokeStyle = C.axis;
  ctx.lineWidth   = 1.5;
  /* Eje X */
  if (yMin <= 0 && yMax >= 0) {
    const { y: ay } = toC(0, 0);
    ctx.beginPath(); ctx.moveTo(0, ay); ctx.lineTo(W, ay); ctx.stroke();
  }
  /* Eje Y */
  if (xMin <= 0 && xMax >= 0) {
    const { x: ax } = toC(0, 0);
    ctx.beginPath(); ctx.moveTo(ax, 0); ctx.lineTo(ax, H); ctx.stroke();
  }

  /* ── Etiquetas de los ejes ── */
  ctx.fillStyle    = C.axisNum;
  ctx.font         = '11px "JetBrains Mono", monospace';
  ctx.textBaseline = 'middle';

  const { y: axisY } = toC(0, 0);   // posición Y del eje X en canvas
  const { x: axisX } = toC(0, 0);   // posición X del eje Y en canvas
  const labelY  = Math.max(14, Math.min(H - 8, axisY + 16));
  const labelX  = Math.max(36, Math.min(W - 40, axisX - 8));

  for (let gx = Math.ceil(xMin / xStep) * xStep; gx <= xMax; gx += xStep) {
    if (Math.abs(gx) < xStep * 0.01) continue;
    const { x: px } = toC(gx, 0);
    /* Tick */
    ctx.strokeStyle = C.axis;
    ctx.lineWidth   = 1;
    ctx.beginPath(); ctx.moveTo(px, axisY - 4); ctx.lineTo(px, axisY + 4); ctx.stroke();
    ctx.textAlign   = 'center';
    ctx.fillText(fmtCoord(gx), px, labelY);
  }
  for (let gy = Math.ceil(yMin / yStep) * yStep; gy <= yMax; gy += yStep) {
    if (Math.abs(gy) < yStep * 0.01) continue;
    const { y: py } = toC(0, gy);
    ctx.strokeStyle = C.axis;
    ctx.lineWidth   = 1;
    ctx.beginPath(); ctx.moveTo(axisX - 4, py); ctx.lineTo(axisX + 4, py); ctx.stroke();
    ctx.textAlign   = 'right';
    ctx.fillText(fmtCoord(gy), labelX, py);
  }

  /* Etiqueta "0" */
  ctx.textAlign = 'right';
  ctx.fillText('0', labelX, labelY);

  /* ── Curva f(x) ── */
  if (expr) {
    const steps  = W * 2;
    const dx     = (xMax - xMin) / steps;
    const crossings = [];
    let   prevY  = null, prevX = null, drawing = false;

    ctx.beginPath();
    ctx.strokeStyle = C.curve;
    ctx.lineWidth   = 2.5;
    ctx.lineJoin    = 'round';
    ctx.lineCap     = 'round';

    for (let i = 0; i <= steps; i++) {
      const wx = xMin + i * dx;
      let wy;
      try { wy = evalF(expr, wx); } catch { wy = NaN; }

      if (!isFinite(wy) || Math.abs(wy) > (yMax - yMin) * 50) {
        if (drawing) ctx.stroke();
        drawing = false;
        ctx.beginPath();
        prevY = null; continue;
      }

      if (prevY !== null && prevY * wy < 0)
        crossings.push((prevX + wx) / 2);

      const { x: px, y: py } = toC(wx, wy);
      if (!drawing) { ctx.moveTo(px, py); drawing = true; }
      else          { ctx.lineTo(px, py); }
      prevY = wy; prevX = wx;
    }
    ctx.stroke();

    /* Cruces por cero — puntos verdes pequeños */
    crossings.forEach(cx_ => {
      const { x: px, y: py } = toC(cx_, 0);
      ctx.beginPath(); ctx.arc(px, py, 4, 0, Math.PI * 2);
      ctx.fillStyle   = C.zero;
      ctx.fill();
      ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.5; ctx.stroke();
    });

    /* ── Raíces calculadas ── */
    const isAutoMode = state.lastAllRoots && state.lastAllRoots.length > 0
                       && state.lastFunction === expr;
    const roots = isAutoMode
      ? state.lastAllRoots.filter(r => isFinite(r))
      : (state.lastRoot !== null && state.lastFunction === expr && isFinite(state.lastRoot))
        ? [state.lastRoot] : [];

    roots.forEach((rx, idx) => {
      if (rx < xMin || rx > xMax) return;
      const col = isAutoMode ? C.rootAuto[idx % C.rootAuto.length] : C.root;
      const { x: px, y: py0 } = toC(rx, 0);

      /* Línea vertical punteada hasta la curva */
      let ry = NaN;
      try { ry = evalF(expr, rx); } catch {}
      if (isFinite(ry)) {
        const { y: pyCurve } = toC(rx, Math.max(yMin, Math.min(yMax, ry)));
        ctx.save();
        ctx.setLineDash([4, 4]);
        ctx.strokeStyle  = col;
        ctx.lineWidth    = 1.5;
        ctx.globalAlpha  = 0.5;
        ctx.beginPath(); ctx.moveTo(px, py0); ctx.lineTo(px, pyCurve); ctx.stroke();
        ctx.restore();
      }

      /* Halo */
      ctx.save();
      ctx.globalAlpha  = 0.15;
      ctx.beginPath(); ctx.arc(px, py0, 14, 0, Math.PI * 2);
      ctx.fillStyle    = col; ctx.fill();
      ctx.restore();

      /* Punto en el eje x */
      ctx.beginPath(); ctx.arc(px, py0, 7, 0, Math.PI * 2);
      ctx.fillStyle   = col; ctx.fill();
      ctx.strokeStyle = '#fff'; ctx.lineWidth = 2.5; ctx.stroke();

      /* Etiqueta con fondo */
      const label = isAutoMode
        ? `r${idx + 1} = ${Number(rx).toFixed(6)}`
        : `x* = ${Number(rx).toFixed(6)}`;

      ctx.font = '700 11px "Poppins", sans-serif';
      const tw  = ctx.measureText(label).width;
      const pw  = tw + 12, ph = 22, pr = 5;
      let   bx  = px - pw / 2;
      let   by  = py0 - 14 - ph;
      if (by < 4)          by = py0 + 14;
      if (bx < 4)          bx = 4;
      if (bx + pw > W - 4) bx = W - pw - 4;

      ctx.save();
      ctx.shadowColor   = 'rgba(0,0,0,0.1)'; ctx.shadowBlur = 6; ctx.shadowOffsetY = 2;
      ctx.fillStyle     = '#fff';
      ctx.beginPath(); ctx.roundRect(bx, by, pw, ph, pr); ctx.fill();
      ctx.restore();

      ctx.strokeStyle = col; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.roundRect(bx, by, pw, ph, pr); ctx.stroke();

      ctx.fillStyle     = col;
      ctx.textAlign     = 'left';
      ctx.textBaseline  = 'middle';
      ctx.fillText(label, bx + 6, by + ph / 2);
      ctx.textBaseline  = 'alphabetic';
    });

    /* ── Línea de seguimiento vertical al cursor ── */
    if (hoverOn) {
      const { x: mx, y: my } = toC(mouseWorld.x, mouseWorld.y);
      ctx.save();
      ctx.strokeStyle = C.crosshair;
      ctx.lineWidth   = 1;
      ctx.setLineDash([3, 3]);
      ctx.beginPath(); ctx.moveTo(mx, 0); ctx.lineTo(mx, H); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(0, my); ctx.lineTo(W, my); ctx.stroke();
      ctx.restore();

      /* Punto de intersección cursor × curva */
      try {
        const fy = evalF(expr, mouseWorld.x);
        if (isFinite(fy)) {
          const { y: pyCurve } = toC(mouseWorld.x, fy);
          ctx.beginPath(); ctx.arc(mx, pyCurve, 4, 0, Math.PI * 2);
          ctx.fillStyle   = C.curve;
          ctx.globalAlpha = 0.7;
          ctx.fill();
          ctx.globalAlpha = 1;
        }
      } catch {}
    }
  }

  /* ── Watermark ── */
  ctx.save();
  ctx.font         = '600 11px "Poppins", sans-serif';
  ctx.fillStyle    = 'rgba(148,163,184,0.5)';
  ctx.textAlign    = 'right';
  ctx.textBaseline = 'bottom';
  ctx.fillText('NUMERIX © 2026', W - 10, H - 8);
  ctx.restore();

  /* ── Panel de info ── */
  const infoEl = document.getElementById('graphInfo');
  if (!infoEl || !expr) return;

  const rangeW  = xMax - xMin, rangeH = yMax - yMin;
  const xZero   = xMin <= 0 && xMax >= 0;
  const yZero   = yMin <= 0 && yMax >= 0;

  let info = `<h4>f(x) = <code style="font-family:var(--font-mono);color:var(--primary)">${expr}</code></h4>
    <p style="margin-top:.3rem;color:var(--gray-500);font-size:.82rem;">
      Vista: x ∈ [${fmtCoord(xMin)}, ${fmtCoord(xMax)}] · y ∈ [${fmtCoord(yMin)}, ${fmtCoord(yMax)}]
    </p>`;

  /* Raíces */
  const isAuto2 = state.lastAllRoots && state.lastAllRoots.length > 0 && state.lastFunction === expr;
  if (isAuto2) {
    const RCOLS = ['#ef4444','#6366f1','#10b981','#f59e0b','#ec4899','#14b8a6','#8b5cf6'];
    info += `<div style="margin-top:.5rem;display:flex;flex-wrap:wrap;gap:.35rem;">`;
    state.lastAllRoots.forEach((rx, i) => {
      const col = RCOLS[i % RCOLS.length];
      info += `<span style="background:${col}18;color:${col};font-family:var(--font-mono);
        font-size:.78rem;font-weight:700;padding:.2rem .55rem;border-radius:4px;border:1px solid ${col}44;">
        r${i+1} = ${Number(rx).toFixed(8)}</span>`;
    });
    info += `</div>`;
  } else if (state.lastRoot !== null && state.lastFunction === expr) {
    info += `<p style="margin-top:.4rem;color:#dc2626;font-size:.82rem;">
      Raíz (${state.lastMethod}): <strong>x* = ${Number(state.lastRoot).toFixed(8)}</strong></p>`;
  }

  infoEl.innerHTML = info;
}

function renderGraph() {
  const expr = (document.getElementById('graph_func')?.value?.trim()) || state.lastFunction || '';
  if (expr) {
    graph.expr         = expr;
    state.lastFunction = expr;
  } else {
    graph.expr = state.lastFunction || '';
  }

  /* Actualizar badge */
  const badge = document.getElementById('graphFuncBadge');
  if (badge) {
    if (graph.expr) {
      badge.textContent = 'f(x) = ' + graph.expr;
      badge.style.display = 'block';
    } else {
      badge.style.display = 'none';
    }
  }

  graphDraw();
}

function graphReset() {
  graph.xMin = -8; graph.xMax = 8;
  graph.yMin = -6; graph.yMax = 6;
  graphDraw();
}

window.graphZoom  = graphZoom;
window.graphReset = graphReset;

function niceStep(range, ticks) {
  const rough = range / ticks;
  const p = Math.pow(10, Math.floor(Math.log10(rough)));
  const n = rough / p;
  return (n < 1.5 ? 1 : n < 3.5 ? 2 : n < 7.5 ? 5 : 10) * p;
}

document.getElementById("btnRenderGraph").addEventListener("click", () => {
  const expr = document.getElementById('graph_func')?.value?.trim();
  if (expr) state.lastFunction = expr;
  renderGraph();
});

document.getElementById("btnGraphReset")?.addEventListener("click", graphReset);

/* ══════════════════════════════════════════════════════════════
   13. INIT
══════════════════════════════════════════════════════════════ */

document.addEventListener("DOMContentLoaded", () => {
  /* Iniciar gráficas interactivas */
  graphInit();
  t1GraphInit();

  /* Cargar historial */
  renderHistory();

  /* Tema activo por defecto */
  switchTheme("t2");
  navigateTo("verify");

  /* Vincular tabs de temas */
  document.querySelectorAll(".theme-tab").forEach(tab => {
    tab.addEventListener("click", () => switchTheme(tab.dataset.theme));
  });

  /* Vincular nav interno */
  document.querySelectorAll("[data-nav]").forEach(el => {
    el.addEventListener("click", () => navigateTo(el.dataset.nav));
  });

  /* ── Auto-mode toggles para cada método ── */
  const modeConfigs = [
    { name: 'bisect_mode',  single: 'bisect-single-fields',  auto: 'bisect-auto-fields',  tol: 'bisect_tol',  tolAuto: 'bisect_tol_auto'  },
    { name: 'false_mode',   single: 'false-single-fields',   auto: 'false-auto-fields',   tol: 'false_tol',   tolAuto: 'false_tol_auto'   },
    { name: 'newton_mode',  single: 'newton-single-fields',  auto: 'newton-auto-fields',  tol: 'newton_tol',  tolAuto: 'newton_tol_auto'  },
    { name: 'secant_mode',  single: 'secant-single-fields',  auto: 'secant-auto-fields',  tol: 'sec_tol',     tolAuto: 'secant_tol_auto'  },
  ];

  modeConfigs.forEach(({ name, single, auto: autoId, tol, tolAuto }) => {
    document.querySelectorAll(`input[name="${name}"]`).forEach(radio => {
      radio.addEventListener('change', () => {
        const isAuto = radio.value === 'auto' && radio.checked;
        const singleEl = document.getElementById(single);
        const autoEl   = document.getElementById(autoId);
        if (singleEl) singleEl.style.display = isAuto ? 'none' : 'block';
        if (autoEl)   autoEl.style.display   = isAuto ? 'block' : 'none';
        /* Sincronizar tolerancia entre modo normal y auto */
        if (isAuto) {
          const valN = document.getElementById(tol)?.value;
          const elA  = document.getElementById(tolAuto);
          if (elA && valN) elA.value = valN;
        } else {
          const valA = document.getElementById(tolAuto)?.value;
          const elN  = document.getElementById(tol);
          if (elN && valA) elN.value = valA;
        }
      });
    });
  });
});

/* Exponer globales para onclick en HTML */
window.navigateTo        = navigateTo;
window.switchTheme       = switchTheme;
window.loadFromHistory   = loadFromHistory;
window.deleteHistoryItem = deleteHistoryItem;
window.renderGraph       = renderGraph;


/* ══════════════════════════════════════════════════════════════
   TEMA 1 — SERIES DE TAYLOR
   Procedimiento completo paso a paso + 3 modos de cálculo:
     simple     → solo P_n(x)
     lagrange   → P_n(x) + R_n(x) + cota
     tolerancia → iterar hasta |R_n| < tol
══════════════════════════════════════════════════════════════ */

/* ── Navegación interna T1 ──────────────────────────────────── */
function t1GoTo(secId) {
  document.querySelectorAll('.t1-sec').forEach(s => s.style.display = 'none');
  document.querySelectorAll('.t1-nav').forEach(n => n.classList.remove('active'));
  const sec = document.getElementById(secId);
  if (sec) { sec.style.display = 'block'; sec.style.animation = 'fadeIn .2s ease'; }
  document.querySelectorAll('[data-t1="' + secId + '"]').forEach(el => el.classList.add('active'));
}

/* ── Mostrar / ocultar nav items de Lagrange ────────────────── */
function mostrarLagrange() {
  document.querySelectorAll('[data-t1="t1-lagrange"], [data-t1="t1-conclusion"]')
    .forEach(el => { el.style.display = ''; el.style.opacity = '1'; el.style.pointerEvents = ''; });
}
function ocultarLagrange() {
  document.querySelectorAll('[data-t1="t1-lagrange"], [data-t1="t1-conclusion"]')
    .forEach(el => { el.style.display = 'none'; });
}

/* ── Leer modo activo ───────────────────────────────────────── */
function t1GetMode() {
  const checked = document.querySelector('input[name="t1Mode"]:checked');
  return checked ? checked.value : 'simple';
}

/* ── Factorial ──────────────────────────────────────────────── */
function t1Fact(n) {
  if (n <= 1) return 1;
  let r = 1; for (let i = 2; i <= n; i++) r *= i; return r;
}

/* ── Derivada numérica orden k con h óptimo por orden ─────────
   Tabla de h calibrada empíricamente para double precision      */
function t1Deriv(expr, a, k) {
  if (k === 0) { try { return evalF(expr, a); } catch(e) { return NaN; } }
  if (k > 8) return NaN;
  const H = [0, 3e-6, 1e-4, 3.2e-4, 3.2e-3, 3.2e-3, 1e-2, 3.2e-2, 3.2e-2];
  const scale = Math.max(0.5, Math.abs(a));
  const h = H[k] * scale;
  const fn = xv => { try { const v = evalF(expr, xv); return isFinite(v) ? v : NaN; } catch(e) { return NaN; } };
  function d(f, x, ord) {
    if (ord === 0) { const v = f(x); return isFinite(v) ? v : NaN; }
    const hi = d(f, x + h, ord - 1);
    const lo = d(f, x - h, ord - 1);
    if (isNaN(hi) || isNaN(lo)) return NaN;
    return (hi - lo) / (2 * h);
  }
  return d(fn, a, k);
}

/* ── Calcular cota de Lagrange para orden n ─────────────────── */
function t1Cota(expr, a, x, n) {
  const lagOrder = n + 1;
  const lagFact  = t1Fact(lagOrder);
  const h        = x - a;
  const lo = Math.min(a, x), hi = Math.max(a, x);
  let M = 0;
  for (let s = 0; s <= 60; s++) {
    const t = lo + (s / 60) * (hi - lo);
    try {
      const v = Math.abs(t1Deriv(expr, t, lagOrder));
      if (isFinite(v) && v > M) M = v;
    } catch(e) {}
  }
  return (M / lagFact) * Math.pow(Math.abs(h), lagOrder);
}

/* ── Nombre simbólico derivada ──────────────────────────────── */
function t1DerivName(k) {
  const L = ['f(x)',"f'(x)","f''(x)","f'''(x)",'f⁽⁴⁾(x)','f⁽⁵⁾(x)','f⁽⁶⁾(x)','f⁽⁷⁾(x)','f⁽⁸⁾(x)'];
  return L[k] || ('f⁽' + k + '⁾(x)');
}
function t1DerivEvalName(k, a) {
  const L = ['f(a)',"f'(a)","f''(a)","f'''(a)",'f⁽⁴⁾(a)','f⁽⁵⁾(a)','f⁽⁶⁾(a)','f⁽⁷⁾(a)','f⁽⁸⁾(a)'];
  return (L[k] || ('f⁽' + k + '⁾(a)')).replace('a', a);
}

/* ── Expresión simbólica de la derivada (texto) ─────────────── */
function t1DerivExpr(funcExpr, k) {
  const clean = funcExpr.trim();
  const rules = {
    'sqrt(x)': ['√x','1/(2√x)','-1/(4x^(3/2))','3/(8x^(5/2))','-15/(16x^(7/2))','105/(32x^(9/2))'],
    'exp(x)':  ['eˣ','eˣ','eˣ','eˣ','eˣ','eˣ','eˣ','eˣ'],
    'sin(x)':  ['sin(x)','cos(x)','-sin(x)','-cos(x)','sin(x)','cos(x)','-sin(x)','-cos(x)'],
    'cos(x)':  ['cos(x)','-sin(x)','-cos(x)','sin(x)','cos(x)','-sin(x)','-cos(x)','sin(x)'],
    'ln(x)':   ['ln(x)','1/x','-1/x²','2/x³','-6/x⁴','24/x⁵','-120/x⁶'],
    'ln(x+1)': ['ln(x+1)','1/(x+1)','-1/(x+1)²','2/(x+1)³','-6/(x+1)⁴','24/(x+1)⁵'],
    '1/(1+x)': ['1/(1+x)','-1/(1+x)²','2/(1+x)³','-6/(1+x)⁴','24/(1+x)⁵'],
    'x^2':     ['x²','2x','2','0','0','0'],
    'x^3':     ['x³','3x²','6x','6','0','0'],
  };
  const match = rules[clean];
  if (match && k < match.length) return match[k];
  return k === 0 ? clean : 'f⁽' + k + '⁾(x)';
}

/* ── Formatear número ───────────────────────────────────────── */
function t1Fmt(v, d) {
  d = d === undefined ? 6 : d;
  if (v === null || v === undefined || isNaN(v) || !isFinite(v)) return '?';
  return Number(v).toFixed(d);
}

/* ══════════════════════════════════════════════════════════════
   MOTOR PRINCIPAL — calcularTaylor()
   Soporta los 3 modos: simple | lagrange | tolerancia
══════════════════════════════════════════════════════════════ */
function calcularTaylor() {
  const funcExpr = document.getElementById('t1Func').value.trim();
  const a        = parseFloat(document.getElementById('t1A').value);
  const x        = parseFloat(document.getElementById('t1X').value);
  let   n        = parseInt(document.getElementById('t1N').value);
  const mode     = t1GetMode();
  const tolInput = parseFloat(document.getElementById('t1Tol').value);
  const alertEl  = document.getElementById('t1Alert');
  alertEl.innerHTML = '';

  /* ── Validaciones comunes ── */
  const errBase =
    !funcExpr     ? 'Ingrese la función f(x).' :
    isNaN(a)      ? "El valor de 'a' debe ser numérico." :
    isNaN(x)      ? "El valor de 'x' debe ser numérico." :
    x === a       ? "x y a no pueden ser iguales." : null;
  if (errBase) { showAlert('t1Alert','danger', errBase); return; }

  /* ── Validación por modo ── */
  if (mode !== 'tolerancia') {
    if (isNaN(n) || n < 1) { showAlert('t1Alert','danger','El orden n debe ser entero ≥ 1.'); return; }
    if (n > 8)              { showAlert('t1Alert','danger','Máximo orden soportado: 8.'); return; }
  } else {
    if (isNaN(tolInput) || tolInput <= 0) {
      showAlert('t1Alert','danger','En modo "Por tolerancia" debe ingresar un valor de tolerancia > 0.');
      return;
    }
  }

  try { evalF(funcExpr, a); evalF(funcExpr, x); }
  catch(e) { showAlert('t1Alert','danger','Error al evaluar f(x): ' + e.message); return; }

  /* ── Modo tolerancia: buscar n automáticamente ── */
  if (mode === 'tolerancia') {
    calcularTaylorPorTolerancia(funcExpr, a, x, tolInput);
    return;
  }

  /* ── Modos simple y lagrange: n fijo ── */
  const h = x - a;
  const derivs = [];
  for (let k = 0; k <= n + 1; k++) derivs.push(t1Deriv(funcExpr, a, k));

  const terms = [];
  let polyAcc = 0;
  for (let k = 0; k <= n; k++) {
    const coef = derivs[k] / t1Fact(k);
    const pow  = Math.pow(h, k);
    const val  = coef * pow;
    polyAcc += val;
    terms.push({ k, deriv: derivs[k], fact: t1Fact(k), coef, h, pow, val, acc: polyAcc });
  }

  const fExact = evalF(funcExpr, x);
  const eaAbs  = Math.abs(fExact - polyAcc);

  /* Guardar estado para exportación */
  state.t1Last = { funcExpr, a, x, n, h, terms, polyAcc, fExact, eaAbs, mode };

  /* Actualizar gráfica de Taylor automáticamente */
  if (typeof t1GraphUpdate === 'function') {
    setTimeout(() => t1GraphUpdate(funcExpr, a, x, n), 50);
  }

  /* Lagrange (calculado siempre, mostrado solo en modo lagrange) */
  const lagOrder = n + 1;
  const lagFact  = t1Fact(lagOrder);
  const xi       = (a + x) / 2;
  const dXi      = t1Deriv(funcExpr, xi, lagOrder);
  const rLag     = isFinite(dXi) ? (dXi / lagFact) * Math.pow(h, lagOrder) : NaN;
  const cota     = t1Cota(funcExpr, a, x, n);

  /* Renderizar secciones siempre existentes */
  renderPlanteamiento(funcExpr, a, x, n, h, mode);
  renderDerivadas(funcExpr, a, n, derivs);
  renderPolinomio(funcExpr, a, x, n, h, derivs, terms, polyAcc);
  renderTabla(funcExpr, a, x, n, h, terms, polyAcc, fExact);
  renderResultado(funcExpr, a, x, n, polyAcc, fExact, eaAbs, mode);

  /* Lagrange y conclusión: condicional por modo */
  if (mode === 'lagrange') {
    mostrarLagrange();
    renderLagrange(funcExpr, a, x, n, lagOrder, lagFact, xi, dXi, rLag, t1Cota(funcExpr, a, x, n).__M || 0, cota, h);
    renderConclusion(eaAbs, cota, polyAcc, fExact);
  } else {
    ocultarLagrange();
    document.getElementById('t1-lagrange').innerHTML   = '';
    document.getElementById('t1-conclusion').innerHTML = '';
    /* Mostrar botón descarga también en modo simple */
    if (typeof numerixExport !== 'undefined') setTimeout(() => numerixExport.showT1Bar(), 100);
  }

  /* Mensaje de éxito */
  const modeLabel = mode === 'simple'
    ? '🔢 Modo: Solo aproximación'
    : '📐 Modo: Aproximación + Lagrange';
  alertEl.innerHTML = '<div class="alert alert-success"><span class="alert-icon">✓</span>' +
    '<span>' + modeLabel + ' — Procedimiento calculado. Navegue las secciones del panel izquierdo.</span></div>';

  t1GoTo('t1-planteamiento');
}

/* ══════════════════════════════════════════════════════════════
   MODO TOLERANCIA — Iteración automática
══════════════════════════════════════════════════════════════ */
function calcularTaylorPorTolerancia(funcExpr, a, x, tol) {
  const MAX_N  = 20;
  const fExact = evalF(funcExpr, x);
  const h      = x - a;
  const alertEl = document.getElementById('t1Alert');

  const iterHistory = [];  /* registro de cada n intentado */
  let polyAcc = 0;
  let finalN  = 0;
  let converged = false;

  /* Acumular términos iterando n */
  const derivs = [];
  for (let k = 0; k <= MAX_N + 1; k++) {
    const dk = t1Deriv(funcExpr, a, k);
    derivs.push(dk);
    if (k > MAX_N) break;

    /* Sumar término k */
    const term = (dk / t1Fact(k)) * Math.pow(h, k);
    polyAcc += term;
    const eaAbs = Math.abs(fExact - polyAcc);
    const cota  = t1Cota(funcExpr, a, x, k);

    iterHistory.push({ n: k, polyAcc, eaAbs, cota, term, converged: cota < tol });

    if (k >= 1 && cota < tol) {
      finalN    = k;
      converged = true;
      break;
    }
    finalN = k;
  }

  const eaFinal   = Math.abs(fExact - polyAcc);
  const cotaFinal = t1Cota(funcExpr, a, x, finalN);

  /* Renderizar secciones estándar con n final */
  mostrarLagrange();

  const termsArr = [];
  let acc2 = 0;
  for (let k = 0; k <= finalN; k++) {
    const coef = derivs[k] / t1Fact(k);
    const pow  = Math.pow(h, k);
    const val  = coef * pow;
    acc2 += val;
    termsArr.push({ k, deriv: derivs[k], fact: t1Fact(k), coef, h, pow, val, acc: acc2 });
  }

  renderPlanteamiento(funcExpr, a, x, finalN, h, 'tolerancia');
  renderDerivadas(funcExpr, a, finalN, derivs.slice(0, finalN + 2));
  renderPolinomio(funcExpr, a, x, finalN, h, derivs, termsArr, polyAcc);
  renderTabla(funcExpr, a, x, finalN, h, termsArr, polyAcc, fExact);
  renderResultado(funcExpr, a, x, finalN, polyAcc, fExact, eaFinal, 'tolerancia');
  renderIterTolerancia(iterHistory, tol, converged, fExact);

  const lagOrder = finalN + 1;
  const lagFact  = t1Fact(lagOrder);
  const xi       = (a + x) / 2;
  const dXi      = t1Deriv(funcExpr, xi, lagOrder);
  const rLag     = isFinite(dXi) ? (dXi / lagFact) * Math.pow(h, lagOrder) : NaN;
  renderLagrange(funcExpr, a, x, finalN, lagOrder, lagFact, xi, dXi, rLag, 0, cotaFinal, h);
  renderConclusion(eaFinal, cotaFinal, polyAcc, fExact);

  const msg = converged
    ? '🎯 Convergió en n = ' + finalN + ' (cota = ' + cotaFinal.toExponential(4) + ' &lt; tolerancia ' + tol + ')'
    : '⚠ No convergió en ' + MAX_N + ' iteraciones. Cota final = ' + cotaFinal.toExponential(4);
  alertEl.innerHTML = '<div class="alert alert-' + (converged ? 'success' : 'warning') + '">' +
    '<span class="alert-icon">' + (converged ? '✓' : '⚠') + '</span><span>' + msg + '</span></div>';

  t1GoTo('t1-planteamiento');
}

/* ── Renderiza sección extra: tabla de iteraciones por tolerancia */
function renderIterTolerancia(history, tol, converged, fExact) {
  const sec = document.getElementById('t1-resultado');
  /* Agregar bloque debajo del resultado existente */
  const existing = sec.innerHTML;

  let html = '<div class="paso-block" style="margin-top:1.25rem;">' +
    '<div class="paso-header">' +
      '<div class="paso-num" style="background:#f0fdf4;border-color:#6ee7b7;color:#065f46;">🎯</div>' +
      '<div><div class="paso-title">Iteraciones por Tolerancia</div>' +
      '<div class="paso-subtitle">Tolerancia requerida: ' + tol + ' — ' +
        (converged ? '✓ Convergió' : '⚠ No convergió en n ≤ 20') + '</div></div>' +
    '</div>' +
    '<div class="paso-body" style="padding:0;">' +
    '<div style="overflow-x:auto;">' +
    '<table style="width:100%;border-collapse:collapse;font-size:.82rem;">' +
    '<thead><tr style="background:#f0fdf4;">' +
      '<th style="padding:.65rem 1rem;text-align:center;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;">n</th>' +
      '<th style="padding:.65rem 1rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;">P<sub>n</sub>(x)</th>' +
      '<th style="padding:.65rem 1rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;">E<sub>a</sub> = |f(x)−P<sub>n</sub>|</th>' +
      '<th style="padding:.65rem 1rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;">Cota Lagrange</th>' +
      '<th style="padding:.65rem 1rem;text-align:center;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;">Cota &lt; Tol?</th>' +
    '</tr></thead><tbody>';

  history.forEach(row => {
    const ok = row.converged;
    html += '<tr style="' + (ok ? 'background:#f0fdf4;' : '') + '">' +
      '<td style="padding:.6rem 1rem;text-align:center;font-family:var(--font-main);font-weight:700;color:#065f46;background:#f0fdf4;">' + row.n + '</td>' +
      '<td style="padding:.6rem 1rem;font-family:var(--font-mono);font-size:.8rem;">' + t1Fmt(row.polyAcc, 8) + '</td>' +
      '<td style="padding:.6rem 1rem;font-family:var(--font-mono);font-size:.8rem;color:' + (row.eaAbs < tol ? '#065f46' : '#991b1b') + ';">' + row.eaAbs.toExponential(6) + '</td>' +
      '<td style="padding:.6rem 1rem;font-family:var(--font-mono);font-size:.8rem;color:' + (ok ? '#065f46' : '#991b1b') + ';font-weight:' + (ok ? '700' : '400') + ';">' + row.cota.toExponential(6) + '</td>' +
      '<td style="padding:.6rem 1rem;text-align:center;font-size:.9rem;">' + (ok ? '✅' : '❌') + '</td>' +
    '</tr>';
  });

  html += '</tbody></table></div></div></div>';
  sec.innerHTML = existing + html;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — Sin cambios en la lógica, solo agrega badge de modo
══════════════════════════════════════════════════════════════ */

/* ── PASO 1: PLANTEAMIENTO ──────────────────────────────────── */
function renderPlanteamiento(funcExpr, a, x, n, h, mode) {
  const sec  = document.getElementById('t1-planteamiento');
  const fA   = t1Fmt(evalF(funcExpr, a));
  const fX   = t1Fmt(evalF(funcExpr, x));
  const modeLabels = {
    simple:     { icon:'🔢', label:'Solo Aproximación',      cls:'simple' },
    lagrange:   { icon:'📐', label:'Aproximación + Lagrange', cls:'lagrange' },
    tolerancia: { icon:'🎯', label:'Por Tolerancia',          cls:'tolerancia' },
  };
  const ml = modeLabels[mode] || modeLabels.simple;

  sec.innerHTML =
    '<div class="page-header"><h2>Paso 1 — Planteamiento</h2>' +
    '<p>Identificación de todos los datos del problema antes de comenzar.</p></div>' +

    '<span class="mode-badge ' + ml.cls + '">' + ml.icon + ' Modo: ' + ml.label + '</span>' +

    '<div class="paso-block">' +
      '<div class="paso-header">' +
        '<div class="paso-num amber">1</div>' +
        '<div><div class="paso-title">Datos del problema</div>' +
        '<div class="paso-subtitle">Definir función, puntos y distancia h = x − a</div></div>' +
      '</div>' +
      '<div class="paso-body">' +
        '<div class="plan-grid">' +
          '<div class="plan-item"><div class="plan-item-label">Función f(x)</div><div class="plan-item-val">' + funcExpr + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">Punto de expansión a</div><div class="plan-item-val">' + a + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">Punto de evaluación x</div><div class="plan-item-val">' + x + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">Orden del polinomio n</div><div class="plan-item-val">' + n + (mode === 'tolerancia' ? ' (calculado)' : '') + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">h = x − a</div><div class="plan-item-val">' + t1Fmt(h) + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">f(a) verificación</div><div class="plan-item-val">' + fA + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">f(x) valor real</div><div class="plan-item-val">' + fX + '</div></div>' +
          '<div class="plan-item"><div class="plan-item-label">Número de términos</div><div class="plan-item-val">n + 1 = ' + (n + 1) + '</div></div>' +
        '</div>' +
        '<div style="background:#fffbeb;border:1px solid #fde68a;border-radius:var(--radius-sm);padding:.875rem 1rem;margin-top:.75rem;">' +
          '<p style="font-family:var(--font-main);font-size:.88rem;color:#92400e;">' +
          '<strong>Objetivo:</strong> Aproximar f(' + x + ') = f(' + a + ' + ' + t1Fmt(h) + ') mediante el polinomio de Taylor de orden ' + n + ' centrado en a = ' + a + '.' +
          '</p>' +
        '</div>' +
      '</div>' +
    '</div>';
}

/* ── PASO 2: DERIVADAS ──────────────────────────────────────── */
function renderDerivadas(funcExpr, a, n, derivs) {
  const sec = document.getElementById('t1-derivadas');
  let html =
    '<div class="page-header"><h2>Paso 2 — Derivadas</h2>' +
    '<p>Calcular f(x), f\'(x), … f<sup>(' + n + ')</sup>(x) y evaluarlas en a = ' + a + '.</p></div>';

  html +=
    '<div class="paso-block">' +
      '<div class="paso-header">' +
        '<div class="paso-num blue">2a</div>' +
        '<div><div class="paso-title">Expresiones simbólicas</div></div>' +
      '</div>' +
      '<div class="paso-body">';
  for (let k = 0; k <= n; k++) {
    html += '<div class="deriv-block">' +
      '<div class="deriv-row">' +
        '<span class="deriv-label">' + t1DerivName(k) + '</span>' +
        '<span class="deriv-expr">= ' + t1DerivExpr(funcExpr, k) + '</span>' +
      '</div></div>';
  }
  html += '</div></div>';

  html +=
    '<div class="paso-block">' +
      '<div class="paso-header">' +
        '<div class="paso-num blue">2b</div>' +
        '<div><div class="paso-title">Evaluación en a = ' + a + '</div></div>' +
      '</div>' +
      '<div class="paso-body">';
  for (let k = 0; k <= n; k++) {
    html += '<div class="deriv-block evaluated">' +
      '<div class="deriv-row">' +
        '<span class="deriv-label">' + t1DerivEvalName(k, a) + '</span>' +
        '<span class="deriv-expr">= ' + t1DerivExpr(funcExpr, k) + ' en x=' + a + ' → ' + t1DerivExpr(funcExpr, k).replace(/x/g, a) + '</span>' +
        '<span class="deriv-result">= ' + t1Fmt(derivs[k]) + '</span>' +
      '</div></div>';
  }

  html +=
    '<div style="margin-top:1.25rem;">' +
    '<div style="font-family:var(--font-main);font-size:.8rem;font-weight:700;color:var(--gray-600);text-transform:uppercase;letter-spacing:.4px;margin-bottom:.5rem;">Tabla resumen</div>' +
    '<div class="cuaderno-table-wrap">' +
    '<table class="cuaderno-table"><thead><tr>' +
    '<th style="text-align:center;">k</th><th>Derivada</th><th>Expresión</th><th style="text-align:right;">f⁽ᵏ⁾(a)</th>' +
    '</tr></thead><tbody>';
  for (let k = 0; k <= n; k++) {
    html += '<tr><td class="iter-num">' + k + '</td>' +
      '<td>' + t1DerivName(k) + '</td>' +
      '<td class="expr-col">' + t1DerivExpr(funcExpr, k) + '</td>' +
      '<td class="result-col">' + t1Fmt(derivs[k]) + '</td></tr>';
  }
  html += '</tbody></table></div></div></div></div>';
  sec.innerHTML = html;
}

/* ── PASO 3: POLINOMIO ──────────────────────────────────────── */
function renderPolinomio(funcExpr, a, x, n, h, derivs, terms, polyAcc) {
  const sec = document.getElementById('t1-polinomio');
  let formula = 'P<sub>' + n + '</sub>(x) = f(a)';
  for (let k = 1; k <= n; k++) {
    const fk = k<=1?"f'(a)":k<=2?"f''(a)":k<=3?"f'''(a)":'f<sup>(' + k + ')</sup>(a)';
    formula += ' + ' + fk + '/' + k + '! · (x−a)<sup>' + k + '</sup>';
  }

  let html =
    '<div class="page-header"><h2>Paso 3 — Polinomio de Taylor</h2>' +
    '<p>Construcción completa sustituyendo las derivadas evaluadas.</p></div>' +

    '<div class="paso-block">' +
      '<div class="paso-header"><div class="paso-num green">3a</div>' +
        '<div><div class="paso-title">Fórmula general</div></div></div>' +
      '<div class="paso-body">' +
        '<div class="poly-expand-box"><div class="poly-expand-formula">' + formula + '</div></div>' +
      '</div>' +
    '</div>' +

    '<div class="paso-block">' +
      '<div class="paso-header"><div class="paso-num green">3b</div>' +
        '<div><div class="paso-title">Sustitución término a término</div></div></div>' +
      '<div class="paso-body"><div class="poly-sust-box">';

  for (let k = 0; k <= n; k++) {
    const dk = t1Fmt(derivs[k]);
    const fact = t1Fact(k);
    const hk   = Math.pow(h, k);
    const coef = derivs[k] / fact;
    if (k === 0) {
      html += '<div class="poly-sust-line">  t<sub>0</sub> = f(a) = ' + dk + '</div>';
    } else {
      html += '<div class="poly-sust-line">  t<sub>' + k + '</sub> = ' +
        t1Fmt(derivs[k]) + ' / ' + fact + '! · (' + t1Fmt(h) + ')<sup>' + k + '</sup>' +
        ' = ' + t1Fmt(coef, 8) + ' · ' + t1Fmt(hk, 8) +
        ' = ' + t1Fmt(terms[k].val, 8) + '</div>';
    }
  }

  html += '<div class="poly-sust-line result">P<sub>' + n + '</sub>(' + x + ') = ' +
    terms.map(t => t1Fmt(t.val, 8)).join(' + ') +
    ' = <strong>' + t1Fmt(polyAcc, 10) + '</strong></div></div></div></div>';

  html += '<div class="paso-block">' +
    '<div class="paso-header"><div class="paso-num green">3c</div>' +
      '<div><div class="paso-title">Acumulación término a término</div></div></div>' +
    '<div class="paso-body">';
  let acc = 0;
  for (let k = 0; k <= n; k++) {
    acc += terms[k].val;
    html += '<div style="display:flex;align-items:center;gap:.75rem;margin-bottom:.4rem;font-family:var(--font-mono);font-size:.85rem;">' +
      '<span style="color:var(--gray-500);min-width:30px;">k=' + k + '</span>' +
      '<span style="color:var(--primary);">+ ' + t1Fmt(terms[k].val, 8) + '</span>' +
      '<span style="color:var(--gray-400);">→</span>' +
      '<span style="color:var(--gray-800);font-weight:600;">Acumulado = ' + t1Fmt(acc, 10) + '</span>' +
      '</div>';
  }
  html += '</div></div>';
  sec.innerHTML = html;
}

/* ── PASO 4: TABLA ──────────────────────────────────────────── */
function renderTabla(funcExpr, a, x, n, h, terms, polyAcc, fExact) {
  const sec = document.getElementById('t1-tabla');
  let html =
    '<div class="page-header"><h2>Paso 4 — Tabla de Iteraciones</h2>' +
    '<p>Formato cuaderno: Iteración | Expresión | Cálculo | Resultado</p></div>' +

    '<div class="paso-block"><div class="paso-header">' +
      '<div class="paso-num amber">4</div>' +
      '<div><div class="paso-title">Tabla de construcción del polinomio</div>' +
      '<div class="paso-subtitle">Iteración | Expresión | Cálculo | Resultado</div></div>' +
    '</div><div class="paso-body" style="padding:0;">' +
    '<div class="cuaderno-table-wrap"><table class="cuaderno-table">' +
    '<thead><tr>' +
      '<th style="text-align:center;">Iter.</th>' +
      '<th>Expresión</th><th>Cálculo</th>' +
      '<th style="text-align:right;">Resultado</th>' +
    '</tr></thead><tbody>';

  for (let k = 0; k <= n; k++) {
    const t   = terms[k];
    const dk6 = t1Fmt(t.deriv, 8);
    let exprStr, calcStr;
    if (k === 0) {
      exprStr = 'f(' + a + ')';
      calcStr = t1DerivExpr(funcExpr, 0).replace(/x/g, a) + ' = ' + dk6;
    } else if (k === 1) {
      exprStr = "f'(" + a + ') · (x − a)';
      calcStr = dk6 + ' × ' + t1Fmt(h, 6);
    } else {
      exprStr = 'f<sup>(' + k + ')</sup>(' + a + ') / ' + t.fact + '! · (x−a)<sup>' + k + '</sup>';
      calcStr = '(' + dk6 + ' / ' + t.fact + ') × (' + t1Fmt(h, 6) + ')<sup>' + k + '</sup> = ' +
                t1Fmt(t.coef, 8) + ' × ' + t1Fmt(t.pow, 8);
    }
    html += '<tr>' +
      '<td class="iter-num">' + k + '</td>' +
      '<td class="expr-col">' + exprStr + '</td>' +
      '<td class="calc-col">' + calcStr + '</td>' +
      '<td class="result-col">' + t1Fmt(t.val, 8) + '</td></tr>';
  }

  html += '</tbody><tfoot><tr>' +
    '<td colspan="3" style="text-align:right;font-family:var(--font-main);">P<sub>' + n + '</sub>(' + x + ') = SUMA =</td>' +
    '<td style="text-align:right;font-weight:700;color:#92400e;font-size:1rem;">' + t1Fmt(polyAcc, 10) + '</td>' +
    '</tr></tfoot></table></div></div></div>';

  sec.innerHTML = html;
}

/* ── PASO 5: RESULTADO ──────────────────────────────────────── */
function renderResultado(funcExpr, a, x, n, polyAcc, fExact, eaAbs, mode) {
  const erPct = Math.abs(fExact) > 1e-14 ? (eaAbs / Math.abs(fExact)) * 100 : 0;
  const sec   = document.getElementById('t1-resultado');

  const modeNote = mode === 'simple'
    ? '<div style="background:var(--secondary-light);border:1px solid #7dd3fc;border-radius:var(--radius-sm);padding:.75rem 1rem;margin-bottom:1rem;font-family:var(--font-main);font-size:.83rem;color:var(--t4-dark);">ℹ️ <strong>Modo Solo Aproximación:</strong> No se calcula el Resto de Lagrange. El error mostrado es el error real (comparación con f(x) exacto).</div>'
    : mode === 'tolerancia'
    ? '<div style="background:var(--success-light);border:1px solid #6ee7b7;border-radius:var(--radius-sm);padding:.75rem 1rem;margin-bottom:1rem;font-family:var(--font-main);font-size:.83rem;color:#065f46;">🎯 <strong>Modo Por Tolerancia:</strong> El orden n = ' + n + ' fue determinado automáticamente por el algoritmo.</div>'
    : '';

  sec.innerHTML =
    '<div class="page-header"><h2>Paso 5 — Resultado Final</h2>' +
    '<p>Comparación entre la aproximación de Taylor y el valor real de f(x).</p></div>' +
    modeNote +
    '<div class="paso-block">' +
      '<div class="paso-header"><div class="paso-num red">5</div>' +
        '<div><div class="paso-title">P<sub>' + n + '</sub>(' + x + ') vs f(' + x + ')</div></div></div>' +
      '<div class="paso-body">' +
        '<div class="resultado-grid">' +
          '<div class="resultado-card amber"><div class="rc-label">P<sub>' + n + '</sub>(' + x + ')</div>' +
            '<div class="rc-val">' + t1Fmt(polyAcc, 10) + '</div></div>' +
          '<div class="resultado-card green"><div class="rc-label">f(' + x + ') valor real</div>' +
            '<div class="rc-val">' + t1Fmt(fExact, 10) + '</div></div>' +
          '<div class="resultado-card red"><div class="rc-label">Error absoluto E<sub>a</sub></div>' +
            '<div class="rc-val">' + eaAbs.toExponential(6) + '</div></div>' +
          '<div class="resultado-card blue"><div class="rc-label">Error relativo E<sub>r</sub>%</div>' +
            '<div class="rc-val">' + erPct.toFixed(6) + ' %</div></div>' +
        '</div>' +
        '<div style="background:var(--gray-50);border:1px solid var(--border);border-radius:var(--radius-sm);padding:1rem;margin-top:.75rem;">' +
          '<div style="font-family:var(--font-mono);font-size:.88rem;line-height:2;">' +
            'E<sub>a</sub> = |f(x) − P<sub>' + n + '</sub>(x)| = |' + t1Fmt(fExact,8) + ' − ' + t1Fmt(polyAcc,8) + '| = <strong>' + eaAbs.toExponential(6) + '</strong>' +
          '</div>' +
        '</div>' +
      '</div>' +
    '</div>';
}

/* ── PASO 6: LAGRANGE ───────────────────────────────────────── */
function renderLagrange(funcExpr, a, x, n, lagOrder, lagFact, xi, dXi, rLag, _M, cota, h) {
  const sec = document.getElementById('t1-lagrange');
  sec.innerHTML =
    '<div class="page-header"><h2>Paso 6 — Resto de Lagrange</h2>' +
    '<p>Cálculo del error de truncamiento y su cota superior.</p></div>' +

    '<div class="paso-block"><div class="paso-header"><div class="paso-num teal">6a</div>' +
      '<div><div class="paso-title">Fórmula del Resto de Lagrange</div></div></div>' +
      '<div class="paso-body">' +
        '<div class="lagrange-step"><div class="lag-step-label">Expresión general</div>' +
          '<div class="lag-step-content">R<sub>' + n + '</sub>(x) = f<sup>(' + lagOrder + ')</sup>(ξ) / ' + lagOrder + '! · (x − a)<sup>' + lagOrder + '</sup>' +
          ',&nbsp; ξ ∈ (' + Math.min(a,x) + ', ' + Math.max(a,x) + ')</div></div>' +

        '<div class="lagrange-step"><div class="lag-step-label">Identificar n+1 = ' + lagOrder + '</div>' +
          '<div class="lag-step-content">' +
            '(n+1)! = ' + lagOrder + '! = ' + lagFact + '<br>' +
            '(x − a)<sup>' + lagOrder + '</sup> = (' + t1Fmt(h,6) + ')<sup>' + lagOrder + '</sup> = ' + t1Fmt(Math.pow(h,lagOrder),8) +
          '</div></div>' +

        '<div class="lagrange-step"><div class="lag-step-label">Derivada f<sup>(' + lagOrder + ')</sup>(ξ), ξ ≈ punto medio</div>' +
          '<div class="lag-step-content">ξ ≈ (' + a + ' + ' + x + ') / 2 = ' + t1Fmt(xi,6) + '<br>' +
            'f<sup>(' + lagOrder + ')</sup>(' + t1Fmt(xi,4) + ') ≈ ' + t1Fmt(dXi,8) +
          '</div></div>' +

        '<div class="lagrange-step"><div class="lag-step-label">Resolución de R<sub>' + n + '</sub>(x)</div>' +
          '<div class="lag-step-content">R<sub>' + n + '</sub>(' + x + ') = ' + t1Fmt(dXi,8) + ' / ' + lagFact + ' · ' + t1Fmt(Math.pow(h,lagOrder),8) + '<br>' +
            '= ' + t1Fmt(dXi/lagFact,8) + ' · ' + t1Fmt(Math.pow(h,lagOrder),8) + '</div>' +
          '<div class="lag-step-content highlight" style="margin-top:.5rem;">R<sub>' + n + '</sub>(' + x + ') ≈ ' +
            (isFinite(rLag) ? rLag.toExponential(6) : '?') + '</div></div>' +
      '</div></div>' +

    '<div class="paso-block"><div class="paso-header"><div class="paso-num teal">6b</div>' +
      '<div><div class="paso-title">Cota del Error</div></div></div>' +
      '<div class="paso-body">' +
        '<div class="lagrange-step"><div class="lag-step-label">Fórmula de la cota</div>' +
          '<div class="lag-step-content">|R<sub>' + n + '</sub>| ≤ M / (n+1)! · |x − a|<sup>n+1</sup><br>' +
            'M = máx |f<sup>(' + lagOrder + ')</sup>| en [' + Math.min(a,x).toFixed(4) + ', ' + Math.max(a,x).toFixed(4) + ']</div></div>' +

        '<div class="lagrange-step"><div class="lag-step-label">Muestreo para M (60 puntos)</div>' +
          '<div class="lag-step-content">M ≈ ' + t1Fmt(t1Cota.__M || cota * lagFact / Math.pow(Math.abs(h),lagOrder), 8) + '</div></div>' +

        '<div class="lagrange-step"><div class="lag-step-label">Cálculo de la cota</div>' +
          '<div class="lag-step-content">' +
            'Cota = M / ' + lagFact + ' · |' + t1Fmt(h,6) + '|<sup>' + lagOrder + '</sup>' +
          '</div>' +
          '<div class="lag-step-content highlight" style="margin-top:.5rem;">Cota ≤ ' + cota.toExponential(6) + '</div></div>' +
      '</div></div>';
}

/* ── PASO 7: CONCLUSIÓN ─────────────────────────────────────── */
function renderConclusion(eaAbs, cota, polyAcc, fExact) {
  const sec     = document.getElementById('t1-conclusion');
  const cotaOk  = isFinite(cota) && eaAbs <= cota * 1.05;
  const goodApx = eaAbs < 0.01;

  sec.innerHTML =
    '<div class="page-header"><h2>Paso 7 — Conclusión</h2>' +
    '<p>Validación de la aproximación y verificación del error frente a la cota de Lagrange.</p></div>' +

    '<div class="paso-block"><div class="paso-header"><div class="paso-num indigo">7</div>' +
      '<div><div class="paso-title">Análisis final</div></div></div>' +
      '<div class="paso-body">' +

        '<div class="concl-box ' + (cotaOk ? 'ok' : 'warn') + '">' +
          '<p><strong>Verificación de la cota:</strong><br>' +
          'Error absoluto E<sub>a</sub> = ' + eaAbs.toExponential(6) + '<br>' +
          'Cota de Lagrange = ' + cota.toExponential(6) + '<br>' +
          (cotaOk
            ? '✓ E<sub>a</sub> ≤ Cota — La aproximación <strong>cumple</strong> con el límite teórico del error.'
            : '⚠ Posible error numérico en la cota (derivadas de orden alto).') +
          '</p></div>' +

        '<div class="concl-box ' + (goodApx ? 'ok' : 'warn') + '">' +
          '<p><strong>Calidad de la aproximación:</strong><br>' +
          'P<sub>n</sub>(x) = ' + t1Fmt(polyAcc, 8) + '<br>' +
          'f(x) real = ' + t1Fmt(fExact, 8) + '<br>' +
          (goodApx
            ? '✓ Error < 0.01 — la aproximación es <strong>aceptable</strong>.'
            : '⚠ Error > 0.01 — considere aumentar n o elegir a más cercano a x.') +
          '</p></div>' +

        '<div style="background:var(--gray-50);border:1px solid var(--border);border-radius:var(--radius-sm);padding:1rem;margin-top:.75rem;">' +
          '<p style="font-family:var(--font-main);font-size:.88rem;color:var(--gray-700);line-height:1.7;">' +
          '<strong>Resumen:</strong> Error E<sub>a</sub> = ' + eaAbs.toExponential(4) +
          '. Cota Lagrange = ' + cota.toExponential(4) + '. ' +
          (goodApx ? 'Aproximación válida para fines prácticos.' :
            'Para mayor precisión, incremente n o acerque a a x.') +
          '</p></div>' +
      '</div></div>';

  /* Mostrar botón de descarga T1 */
  if (typeof numerixExport !== 'undefined') setTimeout(() => numerixExport.showT1Bar(), 100);
}

/* ── INIT TEMA 1 ────────────────────────────────────────────── */
document.addEventListener('DOMContentLoaded', () => {
  /* Vincular botón */
  const btn = document.getElementById('btnTaylor');
  if (btn) btn.addEventListener('click', calcularTaylor);

  /* Vincular nav T1 */
  document.querySelectorAll('.t1-nav[data-t1]').forEach(el => {
    el.addEventListener('click', () => t1GoTo(el.getAttribute('data-t1')));
  });

  /* Mostrar/ocultar input de tolerancia según modo */
  document.querySelectorAll('input[name="t1Mode"]').forEach(radio => {
    radio.addEventListener('change', () => {
      const isTol  = radio.value === 'tolerancia' && radio.checked;
      const tolGrp = document.getElementById('t1TolGroup');
      const nGrp   = document.getElementById('t1NGroup');
      if (tolGrp) tolGrp.style.display = isTol ? 'block' : 'none';
      if (nGrp)   nGrp.style.opacity   = isTol ? '0.4'   : '1';
      if (nGrp)   nGrp.style.pointerEvents = isTol ? 'none' : '';
    });
  });
});

window.calcularTaylor = calcularTaylor;
window.t1GoTo         = t1GoTo;

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA — TAYLOR
   Mismo motor que la gráfica de T2, adaptado para mostrar:
   · f(x) original en azul
   · Pₙ(x) polinomio de Taylor en ámbar (línea punteada)
   · Punto de expansión a (índigo)
   · Punto de evaluación x (rojo)
   · Error visual entre f(x) y Pₙ(x)
══════════════════════════════════════════════════════════════ */

const t1Graph = {
  xMin: -4, xMax: 4, yMin: -4, yMax: 4,
  dragging: false, lastMouse: { x:0, y:0 },
  mouseWorld: { x:0, y:0 }, hoverOn: false,
  canvas: null, ctx: null,
  /* Datos del último cálculo Taylor */
  funcExpr: '', a: 0, x: 0, n: 0, terms: [],
};

function t1GraphInit() {
  const canvas = document.getElementById('t1GraphCanvas');
  if (!canvas) return;
  t1Graph.canvas = canvas;
  t1Graph.ctx    = canvas.getContext('2d');

  /* Tamaño responsivo */
  t1GraphResize();
  window.addEventListener('resize', t1GraphResize);

  /* Mouse */
  canvas.addEventListener('mousedown', e => {
    t1Graph.dragging  = true;
    t1Graph.lastMouse = { x: e.clientX, y: e.clientY };
    canvas.style.cursor = 'grabbing';
  });
  canvas.addEventListener('mouseup',    () => { t1Graph.dragging = false; canvas.style.cursor = 'crosshair'; });
  canvas.addEventListener('mouseleave', () => {
    t1Graph.dragging = false; t1Graph.hoverOn = false;
    canvas.style.cursor = 'crosshair';
    document.getElementById('t1GraphCoords').innerHTML = 'x = — &nbsp; y = —';
    t1GraphDraw();
  });
  canvas.addEventListener('mousemove', e => {
    const rect  = canvas.getBoundingClientRect();
    const px    = (e.clientX - rect.left)  * (canvas.width  / rect.width);
    const py    = (e.clientY - rect.top)   * (canvas.height / rect.height);
    t1Graph.mouseWorld = t1GToWorld(px, py);
    t1Graph.hoverOn    = true;

    const wx = t1Graph.mouseWorld.x, wy = t1Graph.mouseWorld.y;
    document.getElementById('t1GraphCoords').innerHTML =
      `x = ${t1GFmt(wx)} &nbsp; y = ${t1GFmt(wy)}`;

    /* Tooltip con f(x) y Pn(x) */
    if (t1Graph.funcExpr) {
      let fLine = '', pLine = '';
      try { fLine = `f(x) = ${t1GFmt(evalF(t1Graph.funcExpr, wx))}`; } catch {}
      try { pLine = `Pₙ(x) = ${t1GFmt(t1GEvalPoly(wx))}`; } catch {}
      const tip = document.getElementById('t1GraphTooltip');
      if (fLine) {
        tip.innerHTML = fLine + (pLine ? '<br>' + pLine : '');
        const bx = (e.clientX - rect.left) + 14;
        const by = (e.clientY - rect.top)  - 50;
        tip.style.left    = Math.min(bx, rect.width  - 200) + 'px';
        tip.style.top     = Math.max(by, 4)                 + 'px';
        tip.style.display = 'block';
      } else { tip.style.display = 'none'; }
    }

    if (t1Graph.dragging) {
      const dx = (e.clientX - t1Graph.lastMouse.x) / rect.width  * (t1Graph.xMax - t1Graph.xMin);
      const dy = (e.clientY - t1Graph.lastMouse.y) / rect.height * (t1Graph.yMax - t1Graph.yMin);
      t1Graph.xMin -= dx; t1Graph.xMax -= dx;
      t1Graph.yMin += dy; t1Graph.yMax += dy;
      t1Graph.lastMouse = { x: e.clientX, y: e.clientY };
    }
    t1GraphDraw();
  });

  /* Zoom rueda */
  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    const factor = e.deltaY > 0 ? 1.12 : 0.89;
    const rect   = canvas.getBoundingClientRect();
    const px     = (e.clientX - rect.left) * (canvas.width  / rect.width);
    const py     = (e.clientY - rect.top)  * (canvas.height / rect.height);
    const { x: wx, y: wy } = t1GToWorld(px, py);
    t1Graph.xMin = wx + (t1Graph.xMin - wx) * factor;
    t1Graph.xMax = wx + (t1Graph.xMax - wx) * factor;
    t1Graph.yMin = wy + (t1Graph.yMin - wy) * factor;
    t1Graph.yMax = wy + (t1Graph.yMax - wy) * factor;
    t1GraphDraw();
  }, { passive: false });

  /* Touch */
  let lT = null, lPD = null;
  canvas.addEventListener('touchstart', e => {
    e.preventDefault();
    if (e.touches.length === 1) { lT = { x: e.touches[0].clientX, y: e.touches[0].clientY }; lPD = null; }
    else if (e.touches.length === 2) { lPD = Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY); }
  }, { passive: false });
  canvas.addEventListener('touchmove', e => {
    e.preventDefault();
    if (e.touches.length === 1 && lT) {
      const rect = canvas.getBoundingClientRect();
      const dx   = (e.touches[0].clientX - lT.x) / rect.width  * (t1Graph.xMax - t1Graph.xMin);
      const dy   = (e.touches[0].clientY - lT.y) / rect.height * (t1Graph.yMax - t1Graph.yMin);
      t1Graph.xMin -= dx; t1Graph.xMax -= dx; t1Graph.yMin += dy; t1Graph.yMax += dy;
      lT = { x: e.touches[0].clientX, y: e.touches[0].clientY };
      t1GraphDraw();
    } else if (e.touches.length === 2 && lPD) {
      const d  = Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
      const f  = lPD / d;
      const cx = (t1Graph.xMin + t1Graph.xMax) / 2, cy = (t1Graph.yMin + t1Graph.yMax) / 2;
      const hw = (t1Graph.xMax - t1Graph.xMin) / 2 * f, hh = (t1Graph.yMax - t1Graph.yMin) / 2 * f;
      t1Graph.xMin = cx-hw; t1Graph.xMax = cx+hw; t1Graph.yMin = cy-hh; t1Graph.yMax = cy+hh;
      lPD = d; t1GraphDraw();
    }
  }, { passive: false });
  canvas.addEventListener('touchend', () => { lT = null; lPD = null; });

  /* Botón reset */
  document.getElementById('btnT1GReset')?.addEventListener('click', t1GraphReset);

  t1GraphDraw();
}

function t1GraphResize() {
  const c = t1Graph.canvas; if (!c) return;
  const w = c.parentElement.clientWidth || 800;
  c.width  = w;
  c.height = Math.max(380, Math.round(w * 0.52));
  t1GraphDraw();
}

function t1GToCanvas(wx, wy) {
  const { canvas: c, xMin, xMax, yMin, yMax } = t1Graph;
  return { x: (wx-xMin)/(xMax-xMin)*c.width, y: c.height-(wy-yMin)/(yMax-yMin)*c.height };
}
function t1GToWorld(px, py) {
  const { canvas: c, xMin, xMax, yMin, yMax } = t1Graph;
  return { x: xMin + (px/c.width)*(xMax-xMin), y: yMin + (1-py/c.height)*(yMax-yMin) };
}
function t1GraphZoom(factor) {
  const cx = (t1Graph.xMin+t1Graph.xMax)/2, cy = (t1Graph.yMin+t1Graph.yMax)/2;
  const hw = (t1Graph.xMax-t1Graph.xMin)/2*factor, hh = (t1Graph.yMax-t1Graph.yMin)/2*factor;
  t1Graph.xMin=cx-hw; t1Graph.xMax=cx+hw; t1Graph.yMin=cy-hh; t1Graph.yMax=cy+hh;
  t1GraphDraw();
}
function t1GraphReset() {
  const cx = t1Graph.a || 0, cy = 0;
  const span = 6;
  t1Graph.xMin = cx - span; t1Graph.xMax = cx + span;
  t1Graph.yMin = cy - span * 0.7; t1Graph.yMax = cy + span * 0.7;
  t1GraphDraw();
}
function t1GFmt(v) {
  if (!isFinite(v)) return '—';
  const a = Math.abs(v);
  if (a === 0) return '0';
  if (a >= 1000 || a < 0.001) return v.toExponential(3);
  if (a < 0.1)  return v.toFixed(5);
  if (a < 10)   return v.toFixed(4);
  if (a < 100)  return v.toFixed(3);
  return v.toFixed(2);
}

/* Evalúa el polinomio de Taylor en un punto usando los términos almacenados */
function t1GEvalPoly(xVal) {
  if (!t1Graph.terms || t1Graph.terms.length === 0) return NaN;
  return t1Graph.terms.reduce((acc, t) => acc + t.val, 0) +
    /* recompute correctamente si x difiere del original */
    (() => {
      const { funcExpr, a, n } = t1Graph;
      if (!funcExpr) return 0;
      let sum = 0, hk = 1;
      for (let k = 0; k <= n; k++) {
        let dk;
        try { dk = t1Deriv(funcExpr, a, k); } catch { break; }
        sum += (dk / t1Fact(k)) * hk;
        hk *= (xVal - a);
      }
      return sum - t1Graph.terms.reduce((s, t) => s + t.val, 0); // delta
    })();
}

/* Evaluación correcta del polinomio en cualquier punto */
function t1GPolyAt(xVal) {
  const { funcExpr, a, n } = t1Graph;
  if (!funcExpr) return NaN;
  let sum = 0, hk = 1;
  for (let k = 0; k <= n; k++) {
    let dk;
    try { dk = t1Deriv(funcExpr, a, k); } catch { return NaN; }
    sum += (dk / t1Fact(k)) * hk;
    hk  *= (xVal - a);
  }
  return sum;
}

function t1GraphNiceStep(range, tgt) {
  const rough = range / tgt, mag = Math.pow(10, Math.floor(Math.log10(rough)));
  const n = rough/mag; return (n<1.5?1:n<3.5?2:n<7.5?5:10)*mag;
}

function t1GraphDraw() {
  const { canvas: c, ctx, xMin, xMax, yMin, yMax, funcExpr, a, x, n, hoverOn, mouseWorld } = t1Graph;
  if (!ctx) return;
  const W = c.width, H = c.height;
  ctx.clearRect(0, 0, W, H);

  /* Fondo */
  ctx.fillStyle = '#ffffff'; ctx.fillRect(0, 0, W, H);

  const toC = (wx, wy) => t1GToCanvas(wx, wy);
  const xStep = t1GraphNiceStep(xMax - xMin, 12);
  const yStep = t1GraphNiceStep(yMax - yMin, 8);

  /* Grid */
  ctx.strokeStyle = '#f1f5f9'; ctx.lineWidth = 1;
  for (let gx = Math.ceil(xMin/xStep)*xStep; gx <= xMax+xStep; gx += xStep) {
    const { x: px } = toC(gx, 0); ctx.beginPath(); ctx.moveTo(px,0); ctx.lineTo(px,H); ctx.stroke();
  }
  for (let gy = Math.ceil(yMin/yStep)*yStep; gy <= yMax+yStep; gy += yStep) {
    const { y: py } = toC(0, gy); ctx.beginPath(); ctx.moveTo(0,py); ctx.lineTo(W,py); ctx.stroke();
  }

  /* Ejes */
  ctx.strokeStyle = '#cbd5e1'; ctx.lineWidth = 1.5;
  const { y: axY } = toC(0, 0), { x: axX } = toC(0, 0);
  const lbY = Math.max(14, Math.min(H-8, axY+16));
  const lbX = Math.max(36, Math.min(W-40, axX-8));
  if (yMin<=0&&yMax>=0) { ctx.beginPath(); ctx.moveTo(0,axY); ctx.lineTo(W,axY); ctx.stroke(); }
  if (xMin<=0&&xMax>=0) { ctx.beginPath(); ctx.moveTo(axX,0); ctx.lineTo(axX,H); ctx.stroke(); }

  /* Etiquetas */
  ctx.fillStyle = '#94a3b8'; ctx.font = '11px "JetBrains Mono",monospace';
  ctx.textBaseline = 'middle';
  for (let gx = Math.ceil(xMin/xStep)*xStep; gx<=xMax; gx+=xStep) {
    if (Math.abs(gx)<xStep*0.01) continue;
    const { x: px } = toC(gx, 0);
    ctx.strokeStyle='#cbd5e1'; ctx.lineWidth=1;
    ctx.beginPath(); ctx.moveTo(px,axY-4); ctx.lineTo(px,axY+4); ctx.stroke();
    ctx.textAlign='center'; ctx.fillStyle='#94a3b8'; ctx.fillText(t1GFmt(gx), px, lbY);
  }
  for (let gy = Math.ceil(yMin/yStep)*yStep; gy<=yMax; gy+=yStep) {
    if (Math.abs(gy)<yStep*0.01) continue;
    const { y: py } = toC(0, gy);
    ctx.strokeStyle='#cbd5e1'; ctx.lineWidth=1;
    ctx.beginPath(); ctx.moveTo(axX-4,py); ctx.lineTo(axX+4,py); ctx.stroke();
    ctx.textAlign='right'; ctx.fillStyle='#94a3b8'; ctx.fillText(t1GFmt(gy), lbX, py);
  }
  ctx.textAlign='right'; ctx.fillText('0', lbX, lbY);

  if (!funcExpr) {
    /* Mensaje vacío */
    ctx.fillStyle = '#94a3b8'; ctx.font = '14px "Poppins",sans-serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('Ejecuta un cálculo de Taylor para ver la gráfica', W/2, H/2);
    ctx.textBaseline = 'alphabetic';

    /* Watermark */
    ctx.save(); ctx.font='600 11px "Poppins",sans-serif'; ctx.fillStyle='rgba(148,163,184,0.5)';
    ctx.textAlign='right'; ctx.textBaseline='bottom';
    ctx.fillText('NUMERIX © 2026', W-10, H-8); ctx.restore();
    return;
  }

  /* ── Curva f(x) — azul ── */
  const steps = W * 2, dx = (xMax-xMin)/steps;
  ctx.beginPath(); ctx.strokeStyle='#4f46e5'; ctx.lineWidth=2.5;
  ctx.lineJoin='round'; ctx.lineCap='round';
  let drawing = false;
  for (let i=0; i<=steps; i++) {
    const wx = xMin + i*dx;
    let wy; try { wy = evalF(funcExpr, wx); } catch { wy=NaN; }
    if (!isFinite(wy)||Math.abs(wy)>(yMax-yMin)*50) {
      if (drawing) ctx.stroke(); drawing=false; ctx.beginPath(); continue;
    }
    const { x: px, y: py } = toC(wx, wy);
    if (!drawing) { ctx.moveTo(px,py); drawing=true; } else ctx.lineTo(px,py);
  }
  if (drawing) ctx.stroke();

  /* ── Polinomio Pₙ(x) — ámbar punteado ── */
  ctx.beginPath(); ctx.strokeStyle='#f59e0b'; ctx.lineWidth=2.5;
  ctx.setLineDash([8, 5]);
  drawing = false;
  for (let i=0; i<=steps; i++) {
    const wx = xMin + i*dx;
    let wy; try { wy = t1GPolyAt(wx); } catch { wy=NaN; }
    if (!isFinite(wy)||Math.abs(wy)>(yMax-yMin)*80) {
      if (drawing) ctx.stroke(); drawing=false; ctx.beginPath(); continue;
    }
    const { x: px, y: py } = toC(wx, wy);
    if (!drawing) { ctx.moveTo(px,py); drawing=true; } else ctx.lineTo(px,py);
  }
  if (drawing) ctx.stroke();
  ctx.setLineDash([]);

  /* ── Franja de error (zona sombreada entre f y Pn) ── */
  ctx.save();
  ctx.globalAlpha = 0.07;
  ctx.fillStyle   = '#f59e0b';
  ctx.beginPath();
  let first = true;
  for (let i=0; i<=steps; i++) {
    const wx = xMin + i*dx;
    let fy, py_;
    try { fy = evalF(funcExpr, wx); } catch { fy=NaN; }
    try { py_ = t1GPolyAt(wx); }      catch { py_=NaN; }
    if (!isFinite(fy)||!isFinite(py_)||Math.abs(fy)>(yMax-yMin)*50||Math.abs(py_)>(yMax-yMin)*80) continue;
    const { x: px, y: pyF  } = toC(wx, fy);
    if (first) { ctx.moveTo(px, pyF); first=false; } else ctx.lineTo(px, pyF);
  }
  for (let i=steps; i>=0; i--) {
    const wx = xMin + i*dx;
    let fy, py_;
    try { fy = evalF(funcExpr, wx); } catch { fy=NaN; }
    try { py_ = t1GPolyAt(wx); }      catch { py_=NaN; }
    if (!isFinite(fy)||!isFinite(py_)) continue;
    const { x: px, y: pyP  } = toC(wx, py_);
    ctx.lineTo(px, pyP);
  }
  ctx.closePath(); ctx.fill();
  ctx.restore();

  /* ── Punto de expansión a (índigo) ── */
  if (isFinite(a) && a >= xMin && a <= xMax) {
    let fa; try { fa = evalF(funcExpr, a); } catch { fa = 0; }
    const { x: pax, y: pay } = toC(a, isFinite(fa)?fa:0);
    const { y: pa0 } = toC(a, 0);

    /* Línea vertical al eje */
    ctx.save(); ctx.setLineDash([4,4]); ctx.strokeStyle='#6366f1'; ctx.lineWidth=1.5; ctx.globalAlpha=0.5;
    ctx.beginPath(); ctx.moveTo(pax, pa0); ctx.lineTo(pax, pay); ctx.stroke(); ctx.restore();

    /* Halo */
    ctx.save(); ctx.globalAlpha=0.15; ctx.beginPath(); ctx.arc(pax, pay, 14, 0, Math.PI*2);
    ctx.fillStyle='#6366f1'; ctx.fill(); ctx.restore();

    ctx.beginPath(); ctx.arc(pax, pay, 7, 0, Math.PI*2);
    ctx.fillStyle='#6366f1'; ctx.fill();
    ctx.strokeStyle='#fff'; ctx.lineWidth=2.5; ctx.stroke();

    /* Etiqueta */
    const lbl = `a = ${t1GFmt(a)}`;
    ctx.font = '700 11px "Poppins",sans-serif';
    const tw = ctx.measureText(lbl).width, pw=tw+12, ph=22, pr=5;
    let bx = pax - pw/2, by = pay - 14 - ph;
    if (by<4) by=pay+14; if (bx<4) bx=4; if (bx+pw>W-4) bx=W-pw-4;
    ctx.save(); ctx.shadowColor='rgba(0,0,0,0.1)'; ctx.shadowBlur=6; ctx.shadowOffsetY=2;
    ctx.fillStyle='#fff'; ctx.beginPath(); ctx.roundRect(bx,by,pw,ph,pr); ctx.fill(); ctx.restore();
    ctx.strokeStyle='#6366f1'; ctx.lineWidth=1.5; ctx.beginPath(); ctx.roundRect(bx,by,pw,ph,pr); ctx.stroke();
    ctx.fillStyle='#6366f1'; ctx.textAlign='left'; ctx.textBaseline='middle';
    ctx.fillText(lbl, bx+6, by+ph/2); ctx.textBaseline='alphabetic';
  }

  /* ── Punto de evaluación x (rojo) ── */
  if (isFinite(x) && x >= xMin && x <= xMax && x !== a) {
    let fx, px_; try { fx = evalF(funcExpr, x); } catch { fx=NaN; }
    try { px_ = t1GPolyAt(x); } catch { px_=NaN; }
    const { x: pxx, y: pyF } = toC(x, isFinite(fx)?fx:0);
    const { y: pyP } = toC(x, isFinite(px_)?px_:0);

    /* Línea vertical guía */
    ctx.save(); ctx.setLineDash([4,4]); ctx.strokeStyle='#ef4444'; ctx.lineWidth=1.5; ctx.globalAlpha=0.5;
    ctx.beginPath(); ctx.moveTo(pxx,0); ctx.lineTo(pxx,H); ctx.stroke(); ctx.restore();

    /* Punto en f(x) */
    if (isFinite(fx)) {
      ctx.save(); ctx.globalAlpha=0.15; ctx.beginPath(); ctx.arc(pxx,pyF,12,0,Math.PI*2);
      ctx.fillStyle='#ef4444'; ctx.fill(); ctx.restore();
      ctx.beginPath(); ctx.arc(pxx,pyF,6,0,Math.PI*2);
      ctx.fillStyle='#ef4444'; ctx.fill(); ctx.strokeStyle='#fff'; ctx.lineWidth=2; ctx.stroke();
    }

    /* Punto en Pn(x) con color diferente */
    if (isFinite(px_)) {
      ctx.beginPath(); ctx.arc(pxx,pyP,5,0,Math.PI*2);
      ctx.fillStyle='#f59e0b'; ctx.fill(); ctx.strokeStyle='#fff'; ctx.lineWidth=1.5; ctx.stroke();
    }

    /* Segmento del error */
    if (isFinite(fx) && isFinite(px_) && Math.abs(pyF-pyP) > 3) {
      ctx.save(); ctx.strokeStyle='#ef4444'; ctx.lineWidth=2; ctx.globalAlpha=0.7;
      ctx.beginPath(); ctx.moveTo(pxx,pyF); ctx.lineTo(pxx,pyP); ctx.stroke();
      ctx.restore();
    }

    /* Etiqueta x */
    const lbl2 = `x = ${t1GFmt(x)}`;
    ctx.font = '700 11px "Poppins",sans-serif';
    const tw2=ctx.measureText(lbl2).width, pw2=tw2+12, ph2=22, pr2=5;
    const py2 = isFinite(fx) ? pyF : H/2;
    let bx2 = pxx - pw2/2, by2 = py2 - 14 - ph2;
    if (by2<4) by2=py2+14; if (bx2<4) bx2=4; if (bx2+pw2>W-4) bx2=W-pw2-4;
    ctx.save(); ctx.shadowColor='rgba(0,0,0,0.1)'; ctx.shadowBlur=6; ctx.shadowOffsetY=2;
    ctx.fillStyle='#fff'; ctx.beginPath(); ctx.roundRect(bx2,by2,pw2,ph2,pr2); ctx.fill(); ctx.restore();
    ctx.strokeStyle='#ef4444'; ctx.lineWidth=1.5; ctx.beginPath(); ctx.roundRect(bx2,by2,pw2,ph2,pr2); ctx.stroke();
    ctx.fillStyle='#ef4444'; ctx.textAlign='left'; ctx.textBaseline='middle';
    ctx.fillText(lbl2, bx2+6, by2+ph2/2); ctx.textBaseline='alphabetic';

    /* Tabla de valores en la gráfica */
    if (isFinite(fx) && isFinite(px_)) {
      const ea = Math.abs(fx - px_);
      const info = [
        { lbl: `f(${t1GFmt(x)})`, val: t1GFmt(fx),  col: '#4f46e5' },
        { lbl: `Pₙ(${t1GFmt(x)})`, val: t1GFmt(px_), col: '#f59e0b' },
        { lbl: '|Ea|',             val: ea.toExponential(3), col: '#ef4444' },
      ];
      const iW=160, iH=18, pad=8, gap=4;
      const totalH = info.length * (iH+gap) + pad*2;
      let ix = W - iW - 12, iy = 12;
      ctx.save();
      ctx.fillStyle='rgba(255,255,255,0.92)'; ctx.strokeStyle='#e2e8f0'; ctx.lineWidth=1;
      ctx.shadowColor='rgba(0,0,0,0.08)'; ctx.shadowBlur=8;
      ctx.beginPath(); ctx.roundRect(ix,iy,iW,totalH,6); ctx.fill(); ctx.stroke();
      ctx.restore();
      info.forEach(({ lbl: l, val: v, col }, i) => {
        const ry2 = iy + pad + i*(iH+gap);
        ctx.fillStyle='#64748b'; ctx.font='500 10px "Poppins",sans-serif';
        ctx.textAlign='left'; ctx.textBaseline='middle';
        ctx.fillText(l, ix+8, ry2+iH/2);
        ctx.fillStyle=col; ctx.font='700 10px "JetBrains Mono",monospace';
        ctx.textAlign='right';
        ctx.fillText(v, ix+iW-8, ry2+iH/2);
      });
      ctx.textBaseline='alphabetic';
    }
  }

  /* Crosshair hover */
  if (hoverOn) {
    const { x: mx, y: my } = toC(mouseWorld.x, mouseWorld.y);
    ctx.save(); ctx.strokeStyle='rgba(100,116,139,0.3)'; ctx.lineWidth=1; ctx.setLineDash([3,3]);
    ctx.beginPath(); ctx.moveTo(mx,0); ctx.lineTo(mx,H); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(0,my); ctx.lineTo(W,my); ctx.stroke();
    ctx.restore();
  }

  /* Watermark */
  ctx.save(); ctx.font='600 11px "Poppins",sans-serif'; ctx.fillStyle='rgba(148,163,184,0.5)';
  ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026', W-10, H-8); ctx.restore();
}

/** Actualizar datos del gráfico T1 y redibujar */
function t1GraphUpdate(funcExpr, a, x, n) {
  t1Graph.funcExpr = funcExpr;
  t1Graph.a        = a;
  t1Graph.x        = x;
  t1Graph.n        = n;

  /* Ajustar vista para que a y x queden centrados con margen */
  const cx   = (a + x) / 2;
  const span = Math.max(Math.abs(x - a) * 2.5, 4);
  t1Graph.xMin = cx - span; t1Graph.xMax = cx + span;
  t1Graph.yMin = -span * 0.7; t1Graph.yMax = span * 0.7;

  /* Actualizar badge */
  const lbl = document.getElementById('t1g-expr-label');
  if (lbl) lbl.textContent = `f(x) = ${funcExpr} · a = ${a} · x = ${x} · n = ${n}`;

  /* Inicializar canvas si no estaba listo */
  if (!t1Graph.canvas) t1GraphInit();
  t1GraphDraw();
}

window.t1GraphZoom   = t1GraphZoom;
window.t1GraphUpdate = t1GraphUpdate;

window.mostrarLagrange = mostrarLagrange;
window.ocultarLagrange = ocultarLagrange;

/* ══════════════════════════════════════════════════════════════
   TEMA 3 — RAÍCES DE POLINOMIOS
   Módulo 3.1: Método de Müller
   Convergencia automática — el sistema evalúa cuándo parar
══════════════════════════════════════════════════════════════ */

/* ── Navegación entre paneles T3 ────────────────────────────── */
function t3GoTo(panelId) {
  document.querySelectorAll('.t3-panel').forEach(p => p.style.display = 'none');
  document.querySelectorAll('.t3-method-nav').forEach(n => n.classList.remove('active'));
  const panel = document.getElementById(panelId);
  if (panel) { panel.style.display = 'block'; panel.style.animation = 'fadeIn .2s ease'; }
  document.querySelectorAll('[data-t3panel="' + panelId + '"]').forEach(el => el.classList.add('active'));
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMO DE MÜLLER
   Inputs : f(x), x0, x1, x2, tolerancia
   Outputs: raíz, tabla de iteraciones, pasos intermedios
   El sistema itera hasta que |Ea| < tol (convergencia real)
   o hasta maxIter como seguridad.
══════════════════════════════════════════════════════════════ */
function mullerMethod(expr, x0, x1, x2, tol) {
  const MAX_ITER = 50;
  const rows     = [];        // tabla de iteraciones
  const steps    = [];        // detalle paso a paso de cada iter

  let xa = x0, xb = x1, xc = x2;

  for (let i = 1; i <= MAX_ITER; i++) {
    const fa = evalF(expr, xa);
    const fb = evalF(expr, xb);
    const fc = evalF(expr, xc);

    // Diferencias divididas
    const h1  = xb - xa;
    const h2  = xc - xb;
    const dd10 = (fb - fa) / h1;          // f[x1,x0]
    const dd21 = (fc - fb) / h2;          // f[x2,x1]
    const dd210 = (dd21 - dd10) / (xc - xa); // f[x2,x1,x0]

    // Coeficientes de la parábola
    const a_c = dd210;
    const b_c = dd21 + h2 * dd210;
    const c_c = fc;

    // Discriminante
    const disc = b_c * b_c - 4 * a_c * c_c;

    // Elegir el signo del denominador más grande (para mayor estabilidad)
    const sqrtDisc = Math.sqrt(Math.abs(disc));
    const denom1 = b_c + sqrtDisc;
    const denom2 = b_c - sqrtDisc;
    const denom  = Math.abs(denom1) >= Math.abs(denom2) ? denom1 : denom2;

    if (Math.abs(denom) < 1e-14) {
      rows.push({ iter: i, xa, xb, xc, fa, fb, fc, h1, h2, dd10, dd21, dd210,
                  a: a_c, b: b_c, c: c_c, disc, denom, xNew: NaN,
                  ea: NaN, erPct: NaN, note: 'Denominador ≈ 0 — no se puede continuar' });
      return { root: xc, rows, steps, converged: false, iterations: i,
               isComplex: false, note: 'Denominador ≈ 0' };
    }

    const xNew = xc - (2 * c_c) / denom;
    const ea   = Math.abs(xNew - xc);
    const erPct = Math.abs(xNew) > 1e-14 ? (ea / Math.abs(xNew)) * 100 : 0;
    const fNew  = safeEval(expr, xNew);

    const isComplex = disc < 0;

    rows.push({
      iter: i, xa, xb, xc, fa, fb, fc,
      h1, h2, dd10, dd21, dd210,
      a: a_c, b: b_c, c: c_c, disc, sqrtDisc, denom,
      xNew, fNew, ea, erPct, isComplex,
      converged: ea < tol
    });

    steps.push({
      iter: i, xa, xb, xc, fa, fb, fc,
      h1, h2, dd10, dd21, dd210,
      a: a_c, b: b_c, c: c_c, disc, sqrtDisc, denom,
      xNew, fNew, ea, erPct, isComplex
    });

    // Convergencia: el sistema decide cuándo parar
    if (ea < tol) {
      return { root: xNew, rows, steps, converged: true, iterations: i,
               isComplex, fRoot: fNew };
    }

    // Avanzar ventana
    xa = xb;
    xb = xc;
    xc = xNew;
  }

  const lastRow = rows[rows.length - 1];
  return { root: lastRow.xNew, rows, steps, converged: false,
           iterations: MAX_ITER, isComplex: lastRow.isComplex,
           fRoot: safeEval(expr, lastRow.xNew) };
}

/* ── Formateo seguro ────────────────────────────────────────── */
function m3Fmt(v, d) {
  d = d === undefined ? 6 : d;
  if (v === null || v === undefined || isNaN(v) || !isFinite(v)) return '—';
  return Number(v).toFixed(d);
}
function m3FmtSci(v, d) {
  d = d === undefined ? 4 : d;
  if (v === null || v === undefined || isNaN(v) || !isFinite(v)) return '—';
  return Number(v).toExponential(d);
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO DEL RESULTADO
══════════════════════════════════════════════════════════════ */
function renderMullerResult(result, expr, x0, x1, x2, tol, allRootsHtml) {
  const { root, rows, steps, converged, iterations, isComplex, fRoot } = result;
  const container = document.getElementById('m3Result');
  const last = rows[rows.length - 1];

  let html = '';

  /* ── 0. Panel de todas las raíces (se inyecta desde fuera) ── */
  if (allRootsHtml) html += allRootsHtml;
  const statusBadge = converged
    ? '<span class="conv-badge-green">✓ Convergió en ' + iterations + ' iteración(es)</span>'
    : '<span class="conv-badge-warn">⚠ No convergió en ' + iterations + ' iteraciones</span>';

  html += '<div class="card" style="margin-bottom:1.25rem;">' +
    '<div class="card-header">' +
      '<div class="card-header-icon green">🎯</div>' +
      '<div><div class="card-title">Resultado del Método de Müller</div>' +
      '<div class="card-subtitle">f(x) = ' + expr + '  ·  x₀=' + x0 + '  x₁=' + x1 + '  x₂=' + x2 + '  tol=' + tol + '</div></div>' +
      '<div style="margin-left:auto;">' + statusBadge + '</div>' +
    '</div>' +

    '<div class="muller-result-grid">' +
      '<div class="muller-result-card">' +
        '<div class="mrc-label">Raíz aproximada</div>' +
        '<div class="mrc-val green">' + m3Fmt(root, 10) + '</div>' +
      '</div>' +
      '<div class="muller-result-card amber">' +
        '<div class="mrc-label">f(raíz) ≈</div>' +
        '<div class="mrc-val">' + m3FmtSci(fRoot, 6) + '</div>' +
      '</div>' +
      '<div class="muller-result-card red">' +
        '<div class="mrc-label">Error E<sub>a</sub> final</div>' +
        '<div class="mrc-val red">' + m3FmtSci(last.ea, 6) + '</div>' +
      '</div>' +
      '<div class="muller-result-card">' +
        '<div class="mrc-label">Iteraciones</div>' +
        '<div class="mrc-val">' + iterations + '</div>' +
      '</div>' +
    '</div>' +

    (isComplex ? '<div class="alert alert-info" style="margin-top:.75rem;"><span class="alert-icon">ℹ</span><span>El discriminante fue <strong>negativo</strong> en alguna iteración, lo que indica la presencia de <strong>raíces complejas</strong>. El resultado real es una aproximación al módulo.</span></div>' : '') +

  '</div>';

  /* ── 2. Tabla de iteraciones ── */
  html += '<div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">' +
    '<div style="padding:1rem 1.5rem .75rem;border-bottom:1px solid var(--border);display:flex;align-items:center;gap:.75rem;">' +
      '<div class="card-header-icon green">📋</div>' +
      '<div><div class="card-title">Tabla de Iteraciones</div>' +
      '<div class="card-subtitle">Convergencia automática — se detuvo cuando E<sub>a</sub> &lt; ' + tol + '</div></div>' +
    '</div>' +
    '<div style="overflow-x:auto;">' +
    '<div class="muller-table-wrap" style="border-radius:0;border:none;">' +
    '<table class="muller-table">' +
    '<thead><tr>' +
      '<th style="text-align:center;">Iter.</th>' +
      '<th>x<sub>a</sub></th>' +
      '<th>x<sub>b</sub></th>' +
      '<th>x<sub>c</sub></th>' +
      '<th>f(x<sub>a</sub>)</th>' +
      '<th>f(x<sub>b</sub>)</th>' +
      '<th>f(x<sub>c</sub>)</th>' +
      '<th>x<sub>nuevo</sub></th>' +
      '<th>E<sub>a</sub></th>' +
      '<th>E<sub>r</sub>%</th>' +
    '</tr></thead><tbody>';

  rows.forEach(r => {
    const isConv = r.converged;
    html += '<tr' + (isConv ? ' class="converged-row"' : '') + '>' +
      '<td>' + r.iter + '</td>' +
      '<td>' + m3Fmt(r.xa) + '</td>' +
      '<td>' + m3Fmt(r.xb) + '</td>' +
      '<td>' + m3Fmt(r.xc) + '</td>' +
      '<td>' + m3Fmt(r.fa) + '</td>' +
      '<td>' + m3Fmt(r.fb) + '</td>' +
      '<td>' + m3Fmt(r.fc) + '</td>' +
      '<td style="font-weight:' + (isConv ? '700' : '400') + ';color:' + (isConv ? 'var(--t3-dark)' : 'inherit') + ';">' + m3Fmt(r.xNew) + '</td>' +
      '<td>' + m3FmtSci(r.ea) + '</td>' +
      '<td>' + (isFinite(r.erPct) ? m3Fmt(r.erPct, 4) + '%' : '—') + '</td>' +
    '</tr>';
  });

  html += '</tbody></table></div></div></div>';

  /* ── 3. Desarrollo paso a paso ── */
  html += '<div class="card" style="margin-bottom:1.25rem;">' +
    '<div class="card-header">' +
      '<div class="card-header-icon green">🔍</div>' +
      '<div><div class="card-title">Desarrollo Paso a Paso</div>' +
      '<div class="card-subtitle">Cálculo completo de cada iteración</div></div>' +
    '</div>' +
    '<div style="padding:1.25rem 1.5rem;">';

  steps.forEach(s => {
    const isConv = s.ea < tol;
    html += '<div class="muller-step-block">' +
      '<div class="muller-step-header">' +
        '<div class="muller-step-num">' + s.iter + '</div>' +
        '<div class="muller-step-title">Iteración ' + s.iter +
          (isConv ? ' — <span style="color:var(--success);">✓ Convergencia alcanzada</span>' : '') + '</div>' +
      '</div>' +
      '<div class="muller-step-body">' +

        /* Puntos y evaluaciones */
        '<div class="muller-data-row"><div class="muller-data-label">Puntos de trabajo</div>' +
          '<div class="muller-data-val">x<sub>a</sub> = ' + m3Fmt(s.xa) + '</div>' +
          '<div class="muller-data-val">x<sub>b</sub> = ' + m3Fmt(s.xb) + '</div>' +
          '<div class="muller-data-val">x<sub>c</sub> = ' + m3Fmt(s.xc) + '</div>' +
        '</div>' +

        '<div class="muller-data-row"><div class="muller-data-label">Evaluaciones f(x)</div>' +
          '<div class="muller-data-val">f(x<sub>a</sub>) = ' + m3Fmt(s.fa) + '</div>' +
          '<div class="muller-data-val">f(x<sub>b</sub>) = ' + m3Fmt(s.fb) + '</div>' +
          '<div class="muller-data-val">f(x<sub>c</sub>) = ' + m3Fmt(s.fc) + '</div>' +
        '</div>' +

        /* Diferencias divididas */
        '<div class="muller-data-row"><div class="muller-data-label">h₁ y h₂</div>' +
          '<div class="muller-data-val">h₁ = x<sub>b</sub> − x<sub>a</sub> = ' + m3Fmt(s.h1) + '</div>' +
          '<div class="muller-data-val">h₂ = x<sub>c</sub> − x<sub>b</sub> = ' + m3Fmt(s.h2) + '</div>' +
        '</div>' +

        '<div class="muller-data-row"><div class="muller-data-label">Diferencias divididas</div>' +
          '<div class="muller-data-val">δ[x<sub>1</sub>,x<sub>0</sub>] = ' + m3Fmt(s.dd10) + '</div>' +
          '<div class="muller-data-val">δ[x<sub>2</sub>,x<sub>1</sub>] = ' + m3Fmt(s.dd21) + '</div>' +
          '<div class="muller-data-val">δ[x<sub>2</sub>,x<sub>1</sub>,x<sub>0</sub>] = ' + m3Fmt(s.dd210) + '</div>' +
        '</div>' +

        /* Coeficientes parábola */
        '<div class="muller-data-row"><div class="muller-data-label">Coeficientes parábola (a, b, c)</div>' +
          '<div class="muller-data-val">a = δ[x₂,x₁,x₀] = ' + m3Fmt(s.a) + '</div>' +
          '<div class="muller-data-val">b = δ[x₂,x₁] + h₂·a = ' + m3Fmt(s.b) + '</div>' +
          '<div class="muller-data-val">c = f(x<sub>c</sub>) = ' + m3Fmt(s.c) + '</div>' +
        '</div>' +

        /* Discriminante y raíz */
        '<div class="muller-data-row"><div class="muller-data-label">Discriminante b²−4ac</div>' +
          '<div class="muller-data-val ' + (s.disc < 0 ? 'purple' : '') + '">' +
            'disc = ' + m3Fmt(s.disc) + (s.disc < 0 ? ' &nbsp;<em>(negativo → raíz compleja)</em>' : '') + '</div>' +
          '<div class="muller-data-val">√|disc| = ' + m3Fmt(s.sqrtDisc) + '</div>' +
          '<div class="muller-data-val">denom = ' + m3Fmt(s.denom) + '</div>' +
        '</div>' +

        /* Resultado */
        '<div class="muller-data-row" style="grid-column:1/-1;border-color:var(--success);background:#f0fdf4;">' +
          '<div class="muller-data-label">Nueva raíz estimada</div>' +
          '<div class="muller-data-val accent" style="font-size:.95rem;">' +
            'x<sub>nuevo</sub> = x<sub>c</sub> − 2·f(x<sub>c</sub>) / denom = ' + m3Fmt(s.xNew, 8) + '</div>' +
          '<div class="muller-data-val muted">E<sub>a</sub> = |x<sub>nuevo</sub> − x<sub>c</sub>| = ' + m3FmtSci(s.ea) +
            ' &nbsp;|&nbsp; E<sub>r</sub>% = ' + m3Fmt(s.erPct, 4) + '%' +
            '&nbsp; ' + (isConv ? '<span style="color:var(--success);font-weight:700;">✓ E<sub>a</sub> &lt; ' + tol + '</span>' :
                                   '<span style="color:var(--gray-400);">E<sub>a</sub> ≥ ' + tol + ', continuar</span>') +
            '</div>' +
        '</div>' +

      '</div>' + /* muller-step-body */
    '</div>'; /* muller-step-block */
  });

  html += '</div></div>'; /* card body close */

  container.innerHTML = html;
  if (typeof numerixExport !== 'undefined') setTimeout(() => numerixExport.showT3Bar(), 50);
}

/* ══════════════════════════════════════════════════════════════
   MÜLLER — MOTOR COMPLETO CON DEFLACIÓN Y RAÍCES COMPLEJAS
   ─────────────────────────────────────────────────────────────
   Algoritmo:
   1. parsePolynomial()   → extrae coeficientes [aₙ,...,a₀]
   2. mullerAllRoots()    → bucle de deflación hasta grado 0
      a. mullerComplex()  → Müller con aritmética compleja
      b. newtonRefine()   → pulir raíz con Newton complejo
      c. deflatePolynomial() → dividir P(x)/(x−r) por Horner
      d. Si grado=2 → solveQuadratic() directo
   3. renderRootsResult() → panel visual completo
══════════════════════════════════════════════════════════════ */

/* ── Aritmética compleja ────────────────────────────────────── */
const CX = {
  make: (r, i=0) => ({ r, i }),
  add:  (a,b) => ({ r: a.r+b.r, i: a.i+b.i }),
  sub:  (a,b) => ({ r: a.r-b.r, i: a.i-b.i }),
  mul:  (a,b) => ({ r: a.r*b.r - a.i*b.i, i: a.r*b.i + a.i*b.r }),
  div:  (a,b) => {
    const d = b.r*b.r + b.i*b.i;
    if (d < 1e-30) return { r: NaN, i: NaN };
    return { r: (a.r*b.r + a.i*b.i)/d, i: (a.i*b.r - a.r*b.i)/d };
  },
  sqrt: (a) => {
    const m = Math.sqrt(a.r*a.r + a.i*a.i);
    return {
      r: Math.sqrt((m + a.r) / 2),
      i: (a.i >= 0 ? 1 : -1) * Math.sqrt((m - a.r) / 2)
    };
  },
  abs:  (a) => Math.sqrt(a.r*a.r + a.i*a.i),
  fromReal: (v) => ({ r: v, i: 0 }),
};

/* ── Evaluar polinomio complejo por Horner ──────────────────── */
function cxPolyEval(coeffs, z) {
  let p = CX.make(0);
  for (const c of coeffs) {
    const cc = (typeof c === 'number') ? CX.make(c) : c;
    p = CX.add(CX.mul(p, z), cc);
  }
  return p;
}

/* ── Evaluar P(z) y P'(z) por Horner (para Newton) ─────────── */
function cxPolyEvalDeriv(coeffs, z) {
  let p = CX.make(0), dp = CX.make(0);
  for (const c of coeffs) {
    const cc = (typeof c === 'number') ? CX.make(c) : c;
    dp = CX.add(CX.mul(dp, z), p);
    p  = CX.add(CX.mul(p, z), cc);
  }
  return { p, dp };
}

/* ── Refinado Newton complejo ───────────────────────────────── */
function cxNewtonRefine(coeffs, z0, maxIter=20) {
  let z = { ...z0 };
  for (let i = 0; i < maxIter; i++) {
    const { p, dp } = cxPolyEvalDeriv(coeffs, z);
    if (CX.abs(dp) < 1e-20) break;
    const dz = CX.div(p, dp);
    z = CX.sub(z, dz);
    if (CX.abs(dz) < 1e-14) break;
  }
  return z;
}

/* ── Deflación por Horner: P(x) ÷ (x − r) ──────────────────── */
function deflatePolynomial(coeffs, root) {
  /* coeffs = complejos  [aₙ, …, a₀] */
  const b = [{ ...coeffs[0] }];
  for (let i = 1; i < coeffs.length; i++) {
    const ci = (typeof coeffs[i] === 'number') ? CX.make(coeffs[i]) : coeffs[i];
    b.push(CX.add(CX.mul(b[i-1], root), ci));
  }
  const residue = b.pop(); // ≈ 0 si root es raíz exacta
  return { quotient: b, residue };
}

/* ── Limpiar parte imaginaria de ruido numérico ─────────────── */
function cxCleanCoeffs(coeffs, eps=1e-9) {
  return coeffs.map(c => CX.make(
    Math.abs(c.r) < eps ? 0 : c.r,
    Math.abs(c.i) < eps ? 0 : c.i
  ));
}

/* ── Resolver cuadrática az² + bz + c = 0 ──────────────────── */
function solveQuadratic(a, b, c) {
  const disc = CX.sub(CX.mul(b, b), CX.mul(CX.make(4), CX.mul(a, c)));
  const sqD  = CX.sqrt(disc);
  const twoA = CX.mul(CX.make(2), a);
  return [
    CX.div(CX.sub(CX.make(0), CX.add(b, sqD)), twoA),
    CX.div(CX.sub(CX.make(0), CX.sub(b, sqD)), twoA)
  ];
}

/* ── Un paso de Müller con aritmética compleja ──────────────── */
function mullerComplex(coeffs, x0c, x1c, x2c, tol, maxIter=100) {
  let xa = x0c, xb = x1c, xc = x2c;
  let lastXNew = xc;
  const rows = [];   // ← tabla de iteraciones completa

  for (let i = 1; i <= maxIter; i++) {
    const fa = cxPolyEval(coeffs, xa);
    const fb = cxPolyEval(coeffs, xb);
    const fc = cxPolyEval(coeffs, xc);

    const h1  = CX.sub(xb, xa);
    const h2  = CX.sub(xc, xb);
    if (CX.abs(h1) < 1e-15 || CX.abs(h2) < 1e-15) break;

    const dd10  = CX.div(CX.sub(fb, fa), h1);
    const dd21  = CX.div(CX.sub(fc, fb), h2);
    const dd210 = CX.div(CX.sub(dd21, dd10), CX.sub(xc, xa));

    const ac = dd210;
    const bc = CX.add(dd21, CX.mul(h2, dd210));
    const cc = fc;

    const disc = CX.sub(CX.mul(bc, bc), CX.mul(CX.make(4), CX.mul(ac, cc)));
    const sqD  = CX.sqrt(disc);
    const d1   = CX.add(bc, sqD);
    const d2   = CX.sub(bc, sqD);
    const denom = CX.abs(d1) >= CX.abs(d2) ? d1 : d2;

    if (CX.abs(denom) < 1e-20) break;

    const xNew = CX.sub(xc, CX.div(CX.mul(CX.make(2), cc), denom));
    if (!isFinite(xNew.r) || !isFinite(xNew.i) || CX.abs(xNew) > 1e10) break;

    const ea = CX.abs(CX.sub(xNew, xc));
    const erPct = CX.abs(xNew) > 1e-14 ? (ea / CX.abs(xNew)) * 100 : 0;
    const isComplex = disc.i !== 0 || disc.r < 0;

    rows.push({
      iter: i,
      xa: xa, xb: xb, xc: xc,
      fa: fa, fb: fb, fc: fc,
      h1: h1, h2: h2,
      dd10: dd10, dd21: dd21, dd210: dd210,
      a: ac, b: bc, c: cc,
      disc: disc, sqrtDisc: sqD, denom: denom,
      xNew: xNew, ea: ea, erPct: erPct,
      isComplexDisc: isComplex,
      converged: ea < tol
    });

    lastXNew = xNew;
    xa = xb; xb = xc; xc = xNew;

    if (ea < tol) return { root: xNew, converged: true, iters: i, rows };
  }
  return { root: lastXNew, converged: false, rows };
}

/* ── Conjuntos de semillas para distintos polinomios ────────── */
const MULLER_SEEDS = [
  [CX.make(0.5, 0.5), CX.make(0, 1),     CX.make(-0.5, 0.5)],
  [CX.make(1),        CX.make(2),         CX.make(3)],
  [CX.make(-1),       CX.make(-2),        CX.make(0)],
  [CX.make(2,  1),    CX.make(-1, 2),     CX.make(1, -1)],
  [CX.make(0.5),      CX.make(-0.5),      CX.make(1.5)],
  [CX.make(-2),       CX.make(0),         CX.make(2)],
  [CX.make(1, 1),     CX.make(-1, -1),    CX.make(0, 2)],
  [CX.make(3),        CX.make(0, 3),      CX.make(-3)],
  [CX.make(0.1),      CX.make(0.2),       CX.make(0.4)],
  [CX.make(-0.5,0.5), CX.make(0.5, 0.5), CX.make(0.5,-0.5)],
];

/* ── Motor principal: Müller + deflación iterativa ──────────── */
/**
 * mullerAllRoots(coeffsRaw, tol)
 *   coeffsRaw : array de números [aₙ, aₙ₋₁, …, a₀]
 *   tol       : tolerancia de convergencia
 *   Retorna   : array de objetos por cada raíz:
 *     {
 *       r, i,              — partes real/imaginaria
 *       iters, converged,  — info convergencia
 *       method,            — 'muller' | 'quadratic' | 'linear'
 *       rows,              — tabla iteraciones (Müller) o null
 *       quadraticSteps,    — pasos fórmula cuadrática o null
 *       polyBefore,        — coeficientes del polinomio ANTES de deflactar
 *       polyAfter,         — coeficientes DESPUÉS de deflactar
 *       seedUsed,          — semilla inicial usada
 *     }
 */
function mullerAllRoots(coeffsRaw, tol=1e-8) {
  let curr = coeffsRaw.map(c => CX.make(c));
  const results = [];

  while (curr.length > 1) {
    const n = curr.length - 1;
    if (n <= 0) break;

    const polyBefore = curr.map(c => ({ ...c }));

    /* ── Caso lineal: ax + b = 0  →  x = −b/a ── */
    if (n === 1) {
      const r = CX.div(CX.sub(CX.make(0), curr[1]), curr[0]);
      results.push({
        ...r, iters: 0, converged: true,
        method: 'linear',
        rows: null,
        quadraticSteps: null,
        polyBefore,
        polyAfter: [],
        seedUsed: null,
        a: curr[0], b: curr[1]   // para mostrar ax+b=0
      });
      break;
    }

    /* ── Caso cuadrático: fórmula general ── */
    if (n === 2) {
      const [a, b, c] = [curr[0], curr[1], curr[2]];
      const disc  = CX.sub(CX.mul(b, b), CX.mul(CX.make(4), CX.mul(a, c)));
      const sqD   = CX.sqrt(disc);
      const twoA  = CX.mul(CX.make(2), a);
      const r1    = CX.div(CX.sub(CX.make(0), CX.add(b, sqD)), twoA);
      const r2    = CX.div(CX.sub(CX.make(0), CX.sub(b, sqD)), twoA);

      // Pasos de la fórmula cuadrática para mostrar
      const quadraticSteps = {
        a, b, c,
        disc,
        sqrtDisc: sqD,
        r1, r2,
        discriminantReal: disc.r,
        discriminantImag: disc.i,
        isComplex: disc.r < 0 || Math.abs(disc.i) > 1e-9
      };

      results.push({
        ...r1, iters: 0, converged: true,
        method: 'quadratic', rows: null, quadraticSteps, polyBefore, polyAfter: [], seedUsed: null
      });
      results.push({
        ...r2, iters: 0, converged: true,
        method: 'quadratic', rows: null, quadraticSteps, polyBefore, polyAfter: [], seedUsed: null
      });
      break;
    }

    /* ── Grado ≥ 3: Müller complejo ── */
    let found = null;
    let seedUsed = null;

    for (const [p0, p1, p2] of MULLER_SEEDS) {
      const res = mullerComplex(curr, p0, p1, p2, tol);
      if (!isFinite(res.root.r) || !isFinite(res.root.i)) continue;

      // Refinar con Newton — preservar las rows de Müller
      const refined   = cxNewtonRefine(curr, res.root, 30);
      const fVal      = CX.abs(cxPolyEval(curr, refined));

      if (isFinite(refined.r) && fVal < 1e-4) {
        found = {
          ...refined, iters: res.iters, converged: true,
          rows: res.rows   // ← iteraciones de Müller
        };
        seedUsed = [p0, p1, p2];
        break;
      }
      if (res.converged && isFinite(res.root.r)) {
        found = {
          ...res.root, iters: res.iters, converged: true,
          rows: res.rows
        };
        seedUsed = [p0, p1, p2];
        break;
      }
    }

    /* Último recurso: Newton puro */
    if (!found) {
      for (const p of [CX.make(1), CX.make(-1), CX.make(0.5,0.5),
                       CX.make(-0.5,0.5), CX.make(2), CX.make(-2)]) {
        const ref  = cxNewtonRefine(curr, p, 60);
        const fVal = CX.abs(cxPolyEval(curr, ref));
        if (isFinite(ref.r) && fVal < 1e-4) {
          found = { ...ref, iters: 60, converged: true, rows: [] };
          seedUsed = [p, p, p];
          break;
        }
      }
    }

    if (!found) break;

    // Deflactar
    const { quotient } = deflatePolynomial(curr, found);
    const polyAfter = cxCleanCoeffs(quotient);

    results.push({
      r: found.r, i: found.i,
      iters: found.iters, converged: found.converged,
      method: 'muller',
      rows: found.rows || [],
      quadraticSteps: null,
      polyBefore,
      polyAfter,
      seedUsed
    });

    curr = polyAfter;
  }

  return results;
}

/* ── Parser: expresión de polinomio → coeficientes ─────────── */
/**
 * parsePolynomial("4x^3 + 2x^2 - 2x + 3")
 *   → [4, 2, -2, 3]
 * Soporta: coeficientes enteros, decimales, negativos, x^n, x^2, x, cte
 */
function parsePolynomial(expr) {
  if (!expr || !expr.trim()) throw new Error('Ingrese el polinomio.');

  // Normalizar: eliminar espacios extra, convertir ** a ^
  let e = expr.trim().replace(/\*\*/g, '^').replace(/\s+/g, '');

  // Tokenizar términos (separar por + y - que no son exponentes)
  // Insertar + antes de - que no sigue a ^ o e
  e = e.replace(/(?<![e^])-/g, '+-');
  const parts = e.split('+').filter(p => p !== '');

  const termMap = {};  // grado → coeficiente acumulado

  for (const part of parts) {
    if (!part) continue;
    let p = part.trim();
    if (!p) continue;

    let coef = 1, grado = 0;

    if (p.includes('x')) {
      const xIdx = p.indexOf('x');
      const coefStr = p.substring(0, xIdx).replace(/\*$/, '');

      if      (coefStr === ''  || coefStr === '+') coef = 1;
      else if (coefStr === '-')                    coef = -1;
      else {
        coef = parseFloat(coefStr);
        if (isNaN(coef)) throw new Error('Coeficiente inválido: "' + coefStr + '"');
      }

      const rest = p.substring(xIdx + 1);
      if (rest === '' || rest === '^1') {
        grado = 1;
      } else if (rest.startsWith('^')) {
        grado = parseInt(rest.substring(1));
        if (isNaN(grado)) throw new Error('Exponente inválido en: "' + p + '"');
      } else if (rest.startsWith('*x') || rest.startsWith('x')) {
        grado = 2; // caso raro, ignorar
      } else {
        grado = 1;
      }
    } else {
      // término constante
      coef = parseFloat(p);
      if (isNaN(coef)) throw new Error('Término inválido: "' + p + '"');
      grado = 0;
    }

    termMap[grado] = (termMap[grado] || 0) + coef;
  }

  if (Object.keys(termMap).length === 0) throw new Error('No se encontraron términos válidos.');

  const maxGrado = Math.max(...Object.keys(termMap).map(Number));
  if (maxGrado < 1) throw new Error('El polinomio debe ser de grado ≥ 1.');

  const coeffs = [];
  for (let g = maxGrado; g >= 0; g--) {
    coeffs.push(termMap[g] || 0);
  }

  // Quitar ceros líderes
  while (coeffs.length > 1 && coeffs[0] === 0) coeffs.shift();

  return { coeffs, maxGrado };
}

/* ── Formatear una raíz compleja para UI ────────────────────── */
function cxFmt(z, dec=8, tol=1e-6) {
  const re = Math.abs(z.r) < tol ? 0 : z.r;
  const im = Math.abs(z.i) < tol ? 0 : z.i;
  const isReal = Math.abs(im) < tol;

  if (isReal) return { text: re.toFixed(dec), type: 'real' };

  const reStr   = re.toFixed(6);
  const imStr   = Math.abs(im).toFixed(6);
  const sign    = im >= 0 ? ' + ' : ' − ';
  return { text: reStr + sign + imStr + 'i', type: 'complex' };
}

/* ── Reconstruir expresión del polinomio deflactado ─────────── */
function polyToString(coeffs) {
  if (!coeffs || coeffs.length === 0) return '0';
  const n = coeffs.length - 1;
  const parts = [];
  coeffs.forEach((c, idx) => {
    const g   = n - idx;
    const raw = typeof c === 'number' ? c : c.r;
    const v   = Math.abs(raw) < 1e-9 ? 0 : +raw.toFixed(6);
    if (v === 0) return;
    const sign    = v < 0 ? '−' : '+';
    const absV    = Math.abs(v);
    const coefStr = (absV === 1 && g > 0) ? '' : absV.toString();
    const xStr    = g === 0 ? '' : g === 1 ? 'x' : 'x^' + g;
    parts.push({ sign, str: (coefStr + xStr) || '1' });
  });
  if (parts.length === 0) return '0';
  return parts.map((p, i) =>
    (i === 0 && p.sign === '+' ? '' : p.sign + ' ') + p.str
  ).join(' ').trim();
}

/* ── Formatear número complejo como string limpio ───────────── */
function cxStr(z, dec=6) {
  if (!z || !isFinite(z.r)) return '—';
  const re = Math.abs(z.r) < 1e-9 ? 0 : z.r;
  const im = Math.abs(z.i) < 1e-9 ? 0 : z.i;
  if (Math.abs(im) < 1e-9) return re.toFixed(dec);
  const sign = im >= 0 ? ' + ' : ' − ';
  return re.toFixed(dec) + sign + Math.abs(im).toFixed(dec) + 'i';
}

/* ── Tabla de iteraciones Müller (modo complejo) ────────────── */
function buildMullerComplexTable(rows, tol, color) {
  if (!rows || rows.length === 0)
    return '<p style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-400);padding:.5rem 0;">Sin iteraciones registradas.</p>';

  const thStyle = 'padding:.6rem .875rem;text-align:right;font-family:var(--font-main);font-size:.7rem;font-weight:700;color:' + color + ';border-bottom:2px solid ' + color + '33;white-space:nowrap;text-transform:uppercase;letter-spacing:.3px;';
  const thC     = 'text-align:center;';

  let h = '<div style="overflow-x:auto;"><table class="muller-table" style="font-size:.8rem;">';
  h += '<thead><tr style="background:' + color + '10;">';
  h += '<th style="' + thStyle + thC + '">Iter.</th>';
  h += '<th style="' + thStyle + '">x<sub>a</sub></th>';
  h += '<th style="' + thStyle + '">x<sub>b</sub></th>';
  h += '<th style="' + thStyle + '">x<sub>c</sub></th>';
  h += '<th style="' + thStyle + '">f(x<sub>c</sub>)</th>';
  h += '<th style="' + thStyle + '">x<sub>nuevo</sub></th>';
  h += '<th style="' + thStyle + '">E<sub>a</sub></th>';
  h += '<th style="' + thStyle + '">E<sub>r</sub>%</th>';
  h += '</tr></thead><tbody>';

  rows.forEach(r => {
    const isConv = r.converged;
    const tdS = 'padding:.55rem .875rem;text-align:right;font-family:var(--font-mono);font-size:.78rem;border-bottom:1px solid ' + color + '18;';
    const rowStyle = isConv ? 'background:' + color + '15;font-weight:600;' : '';
    h += '<tr style="' + rowStyle + '">';
    h += '<td style="' + tdS + 'text-align:center;font-family:var(--font-main);font-weight:700;color:' + color + ';">' + r.iter + '</td>';
    h += '<td style="' + tdS + '">' + cxStr(r.xa) + '</td>';
    h += '<td style="' + tdS + '">' + cxStr(r.xb) + '</td>';
    h += '<td style="' + tdS + '">' + cxStr(r.xc) + '</td>';
    h += '<td style="' + tdS + '">' + cxStr(r.fc) + '</td>';
    h += '<td style="' + tdS + 'color:' + color + ';font-weight:' + (isConv?'700':'400') + ';">' + cxStr(r.xNew) + '</td>';
    h += '<td style="' + tdS + '">' + (isFinite(r.ea) ? r.ea.toExponential(4) : '—') + '</td>';
    h += '<td style="' + tdS + '">' + (isFinite(r.erPct) ? r.erPct.toFixed(4) + '%' : '—') + '</td>';
    h += '</tr>';
  });

  h += '</tbody></table></div>';
  return h;
}

/* ── Paso a paso Müller (bloques expandidos) ────────────────── */
function buildMullerStepBlocks(rows, tol, color) {
  if (!rows || rows.length === 0) return '';
  let h = '';

  rows.forEach(r => {
    const isConv = r.ea < tol;
    h += '<div class="muller-step-block" style="border-left:3px solid ' + color + ';">';
    h += '<div class="muller-step-header" style="background:' + color + '12;border-bottom:1px solid ' + color + '25;">';
    h += '<div class="muller-step-num" style="background:' + color + ';">' + r.iter + '</div>';
    h += '<div class="muller-step-title">Iteración ' + r.iter;
    if (isConv) h += ' — <span style="color:' + color + ';">✓ Convergencia alcanzada</span>';
    h += '</div></div>';
    h += '<div class="muller-step-body">';

    /* Puntos */
    h += '<div class="muller-data-row"><div class="muller-data-label">Puntos de trabajo</div>';
    h += '<div class="muller-data-val">x<sub>a</sub> = ' + cxStr(r.xa, 8) + '</div>';
    h += '<div class="muller-data-val">x<sub>b</sub> = ' + cxStr(r.xb, 8) + '</div>';
    h += '<div class="muller-data-val">x<sub>c</sub> = ' + cxStr(r.xc, 8) + '</div>';
    h += '</div>';

    /* Evaluaciones */
    h += '<div class="muller-data-row"><div class="muller-data-label">Evaluaciones f(x)</div>';
    h += '<div class="muller-data-val">f(x<sub>a</sub>) = ' + cxStr(r.fa, 8) + '</div>';
    h += '<div class="muller-data-val">f(x<sub>b</sub>) = ' + cxStr(r.fb, 8) + '</div>';
    h += '<div class="muller-data-val">f(x<sub>c</sub>) = ' + cxStr(r.fc, 8) + '</div>';
    h += '</div>';

    /* h1, h2 */
    h += '<div class="muller-data-row"><div class="muller-data-label">h₁ y h₂</div>';
    h += '<div class="muller-data-val">h₁ = x<sub>b</sub> − x<sub>a</sub> = ' + cxStr(r.h1, 8) + '</div>';
    h += '<div class="muller-data-val">h₂ = x<sub>c</sub> − x<sub>b</sub> = ' + cxStr(r.h2, 8) + '</div>';
    h += '</div>';

    /* Diferencias divididas */
    h += '<div class="muller-data-row"><div class="muller-data-label">Diferencias divididas</div>';
    h += '<div class="muller-data-val">δ[x<sub>1</sub>,x<sub>0</sub>] = ' + cxStr(r.dd10, 8) + '</div>';
    h += '<div class="muller-data-val">δ[x<sub>2</sub>,x<sub>1</sub>] = ' + cxStr(r.dd21, 8) + '</div>';
    h += '<div class="muller-data-val">δ[x<sub>2</sub>,x<sub>1</sub>,x<sub>0</sub>] = ' + cxStr(r.dd210, 8) + '</div>';
    h += '</div>';

    /* Coeficientes parábola */
    h += '<div class="muller-data-row"><div class="muller-data-label">Coeficientes parábola (a, b, c)</div>';
    h += '<div class="muller-data-val">a = ' + cxStr(r.a, 8) + '</div>';
    h += '<div class="muller-data-val">b = ' + cxStr(r.b, 8) + '</div>';
    h += '<div class="muller-data-val">c = f(x<sub>c</sub>) = ' + cxStr(r.c, 8) + '</div>';
    h += '</div>';

    /* Discriminante */
    const discColor = r.isComplexDisc ? 'var(--primary-dark)' : 'inherit';
    h += '<div class="muller-data-row"><div class="muller-data-label">Discriminante b²−4ac</div>';
    h += '<div class="muller-data-val" style="color:' + discColor + '">disc = ' + cxStr(r.disc, 8) + (r.isComplexDisc ? ' &nbsp;<em>(complejo)</em>' : '') + '</div>';
    h += '<div class="muller-data-val">√disc = ' + cxStr(r.sqrtDisc, 8) + '</div>';
    h += '<div class="muller-data-val">denom = ' + cxStr(r.denom, 8) + '</div>';
    h += '</div>';

    /* Resultado */
    h += '<div class="muller-data-row" style="grid-column:1/-1;border-color:' + color + ';background:' + color + '08;">';
    h += '<div class="muller-data-label">Nueva estimación</div>';
    h += '<div class="muller-data-val accent" style="color:' + color + ';font-size:.95rem;">x<sub>nuevo</sub> = x<sub>c</sub> − 2f(x<sub>c</sub>)/denom = <strong>' + cxStr(r.xNew, 8) + '</strong></div>';
    h += '<div class="muller-data-val muted">E<sub>a</sub> = ' + (isFinite(r.ea) ? r.ea.toExponential(4) : '—');
    h += ' &nbsp;|&nbsp; E<sub>r</sub>% = ' + (isFinite(r.erPct) ? r.erPct.toFixed(4) : '—') + '%';
    h += '&nbsp; ' + (isConv
      ? '<span style="color:' + color + ';font-weight:700;">✓ E<sub>a</sub> &lt; ' + tol + '</span>'
      : '<span style="color:var(--gray-400);">continuar</span>');
    h += '</div></div>';

    h += '</div></div>'; // step-body / step-block
  });

  return h;
}

/* ── Pasos de fórmula cuadrática ────────────────────────────── */
function buildQuadraticSteps(qs, color, rootIdx) {
  if (!qs) return '';
  const {a, b, c, disc, sqrtDisc, r1, r2} = qs;
  const sign = qs.isComplex ? ' (discriminante negativo → raíces complejas conjugadas)' : '';

  let h = '<div class="muller-step-block" style="border-left:3px solid ' + color + ';">';
  h += '<div class="muller-step-header" style="background:' + color + '12;border-bottom:1px solid ' + color + '25;">';
  h += '<div class="muller-step-num" style="background:' + color + ';font-size:.75rem;">Q</div>';
  h += '<div class="muller-step-title">Fórmula Cuadrática' + sign + '</div>';
  h += '</div><div class="muller-step-body">';

  h += '<div class="muller-data-row"><div class="muller-data-label">Polinomio residual ax²+bx+c</div>';
  h += '<div class="muller-data-val">a = ' + cxStr(a, 8) + '</div>';
  h += '<div class="muller-data-val">b = ' + cxStr(b, 8) + '</div>';
  h += '<div class="muller-data-val">c = ' + cxStr(c, 8) + '</div>';
  h += '</div>';

  h += '<div class="muller-data-row"><div class="muller-data-label">Discriminante Δ = b²−4ac</div>';
  h += '<div class="muller-data-val" style="color:' + (qs.isComplex ? 'var(--primary-dark)' : 'inherit') + '">Δ = ' + cxStr(disc, 8) + '</div>';
  h += '<div class="muller-data-val">√Δ = ' + cxStr(sqrtDisc, 8) + '</div>';
  h += '</div>';

  h += '<div class="muller-data-row" style="grid-column:1/-1;border-color:' + color + ';background:' + color + '08;">';
  h += '<div class="muller-data-label">Raíces x = (−b ± √Δ) / 2a</div>';
  h += '<div class="muller-data-val" style="color:' + color + ';font-weight:700;">r' + (rootIdx+1) + ' = ' + cxStr(r1, 8) + '</div>';
  h += '<div class="muller-data-val" style="color:' + color + ';font-weight:700;">r' + (rootIdx+2) + ' = ' + cxStr(r2, 8) + '</div>';
  h += '</div>';

  h += '</div></div>';
  return h;
}

/* ── Renderizar resultado completo con paso a paso ──────────── */
function renderRootsResult(results, coeffsRaw, expr, tol) {
  const container = document.getElementById('m3Result');
  const COLORS = ['#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6','#ef4444'];

  const realResults    = results.filter(r => Math.abs(r.i) < 1e-6);
  const complexResults = results.filter(r => Math.abs(r.i) >= 1e-6);

  let html = '';

  /* ════════════════════════════════════════════
     1. PANEL RESUMEN — todas las raíces
  ════════════════════════════════════════════ */
  html += '<div class="card" style="margin-bottom:1.25rem;border-top:4px solid #10b981;">';
  html += '<div class="card-header">';
  html += '<div class="card-header-icon green">🎯</div>';
  html += '<div>';
  html += '<div class="card-title">Todas las Raíces — Müller + Deflación</div>';
  html += '<div class="card-subtitle">f(x) = ' + expr + '  ·  grado ' + results.length + '  ·  tol = ' + tol + '</div>';
  html += '</div>';
  html += '<div style="margin-left:auto;display:flex;gap:.5rem;flex-wrap:wrap;">';
  if (realResults.length > 0)
    html += '<span style="background:var(--success-light);color:#065f46;font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #6ee7b7;">' + realResults.length + ' real' + (realResults.length>1?'es':'') + '</span>';
  if (complexResults.length > 0)
    html += '<span style="background:var(--primary-light);color:var(--primary-dark);font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #a5b4fc;">' + complexResults.length + ' compleja' + (complexResults.length>1?'s':'') + '</span>';
  html += '</div></div>';

  /* Tarjetas resumen */
  html += '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:.75rem;padding:0 1.5rem 1.25rem;">';
  results.forEach((res, i) => {
    const col    = COLORS[i % COLORS.length];
    const fmt    = cxFmt(res);
    const isReal = fmt.type === 'real';
    let fVal = '?';
    try { fVal = CX.abs(cxPolyEval(coeffsRaw.map(c=>CX.make(c)), res)).toExponential(3); } catch(e) {}
    const methodLabel = res.method === 'muller' ? 'Müller' : res.method === 'quadratic' ? 'Cuadrática' : 'Lineal';

    html += '<div style="border-radius:var(--radius-sm);border:1.5px solid ' + col + '33;border-left:5px solid ' + col + ';padding:.875rem 1rem;background:var(--gray-50);">';
    html += '<div style="display:flex;align-items:center;gap:.4rem;margin-bottom:.5rem;flex-wrap:wrap;">';
    html += '<span style="background:' + col + ';color:#fff;font-family:var(--font-main);font-size:.65rem;font-weight:700;padding:.15rem .55rem;border-radius:4px;">r' + (i+1) + '</span>';
    html += '<span style="font-family:var(--font-main);font-size:.65rem;font-weight:600;color:' + (isReal?'#065f46':'#3730a3') + ';background:' + (isReal?'#f0fdf4':'#eef2ff') + ';padding:.1rem .45rem;border-radius:4px;">' + (isReal?'Real':'Compleja') + '</span>';
    html += '<span style="font-family:var(--font-main);font-size:.62rem;color:var(--gray-400);margin-left:auto;">' + methodLabel;
    if (res.iters > 0) html += ' · ' + res.iters + ' iter.';
    html += '</span></div>';
    html += '<div style="font-family:var(--font-mono);font-size:.92rem;font-weight:700;color:' + col + ';margin-bottom:.3rem;word-break:break-all;">' + fmt.text + '</div>';
    html += '<div style="font-family:var(--font-mono);font-size:.72rem;color:var(--gray-500);">|f(r)| ≈ ' + fVal + '</div>';
    html += '</div>';
  });
  html += '</div></div>';

  /* ════════════════════════════════════════════
     2. TABLA DE VERIFICACIÓN
  ════════════════════════════════════════════ */
  html += '<div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">';
  html += '<div style="padding:1rem 1.5rem .75rem;border-bottom:1px solid var(--border);display:flex;align-items:center;gap:.75rem;">';
  html += '<div class="card-header-icon green">✓</div>';
  html += '<div><div class="card-title">Tabla de Verificación</div>';
  html += '<div class="card-subtitle">|f(r)| ≈ 0 para cada raíz</div></div></div>';
  html += '<div style="overflow-x:auto;"><table style="width:100%;border-collapse:collapse;font-size:.82rem;">';
  html += '<thead><tr style="background:var(--success-light);">';
  ['#','Raíz','Tipo','Método','Re(r)','Im(r)','|f(r)|','✓'].forEach(h2 => {
    html += '<th style="padding:.6rem 1rem;text-align:left;font-family:var(--font-main);font-size:.7rem;font-weight:700;color:#065f46;border-bottom:2px solid #6ee7b7;white-space:nowrap;">' + h2 + '</th>';
  });
  html += '</tr></thead><tbody>';
  results.forEach((res, i) => {
    const col    = COLORS[i % COLORS.length];
    const fmt    = cxFmt(res);
    const isReal = fmt.type === 'real';
    let fVal = NaN;
    try { fVal = CX.abs(cxPolyEval(coeffsRaw.map(c=>CX.make(c)), res)); } catch(e) {}
    const ok = isFinite(fVal) && fVal < 1e-3;
    const tdS = 'padding:.55rem 1rem;border-bottom:1px solid var(--success-light);';

    html += '<tr>';
    html += '<td style="' + tdS + '"><span style="background:' + col + ';color:#fff;font-size:.65rem;font-weight:700;padding:.1rem .45rem;border-radius:4px;">r' + (i+1) + '</span></td>';
    html += '<td style="' + tdS + 'font-family:var(--font-mono);color:' + col + ';font-weight:600;">' + fmt.text + '</td>';
    html += '<td style="' + tdS + 'font-family:var(--font-main);font-size:.72rem;color:' + (isReal?'#065f46':'#3730a3') + ';">' + (isReal?'Real':'Compleja') + '</td>';
    html += '<td style="' + tdS + 'font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);">' + (res.method==='muller'?'Müller':res.method==='quadratic'?'Cuadrática':'Lineal') + '</td>';
    html += '<td style="' + tdS + 'font-family:var(--font-mono);font-size:.8rem;">' + (Math.abs(res.r)<1e-9?'0':res.r.toFixed(8)) + '</td>';
    html += '<td style="' + tdS + 'font-family:var(--font-mono);font-size:.8rem;">' + (Math.abs(res.i)<1e-9?'0':res.i.toFixed(8)) + '</td>';
    html += '<td style="' + tdS + 'font-family:var(--font-mono);font-size:.8rem;color:' + (ok?'#065f46':'#991b1b') + ';font-weight:600;">' + (isFinite(fVal)?fVal.toExponential(4):'?') + '</td>';
    html += '<td style="' + tdS + 'font-size:.9rem;">' + (ok?'✅':'⚠️') + '</td>';
    html += '</tr>';
  });
  html += '</tbody></table></div></div>';

  /* ════════════════════════════════════════════
     3. PASO A PASO POR RAÍZ
  ════════════════════════════════════════════ */
  html += '<div class="card" style="margin-bottom:1.25rem;">';
  html += '<div class="card-header">';
  html += '<div class="card-header-icon green">🔍</div>';
  html += '<div><div class="card-title">Proceso Completo — Iteraciones por Raíz</div>';
  html += '<div class="card-subtitle">Deflación iterativa: cada raíz reduce el grado del polinomio</div></div>';
  html += '</div>';
  html += '<div style="padding:1.25rem 1.5rem;">';

  let quadraticDone = false; // para no repetir el bloque cuadrático (r1 y r2 comparten qs)

  results.forEach((res, i) => {
    const col  = COLORS[i % COLORS.length];
    const fmt  = cxFmt(res);
    const isReal = fmt.type === 'real';
    const polyBeforeStr = res.polyBefore ? polyToString(res.polyBefore) : '';
    const polyAfterStr  = res.polyAfter && res.polyAfter.length > 0 ? polyToString(res.polyAfter) : null;

    /* ── Separador de raíz ── */
    html += '<div style="margin-bottom:1.25rem;">';

    /* Cabecera de la raíz */
    html += '<div style="display:flex;align-items:center;gap:.75rem;margin-bottom:.75rem;padding:.75rem 1rem;';
    html += 'background:' + col + '0D;border-radius:var(--radius-sm);border:1.5px solid ' + col + '33;">';
    html += '<span style="background:' + col + ';color:#fff;font-family:var(--font-main);font-size:.78rem;font-weight:700;padding:.25rem .7rem;border-radius:5px;">r' + (i+1) + '</span>';
    html += '<div style="flex:1;">';
    html += '<div style="font-family:var(--font-mono);font-size:.95rem;font-weight:700;color:' + col + ';">' + fmt.text + '</div>';
    html += '<div style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);margin-top:2px;">';
    html += (isReal ? 'Raíz real' : 'Raíz compleja') + ' · ';
    if (res.method === 'muller')      html += 'Método de Müller (' + (res.iters||0) + ' iteraciones)';
    else if (res.method === 'quadratic') html += 'Fórmula cuadrática directa';
    else                               html += 'Ecuación lineal directa';
    html += '</div></div>';
    /* Polinomio que se estaba resolviendo */
    if (polyBeforeStr) {
      html += '<div style="font-family:var(--font-mono);font-size:.78rem;color:var(--gray-600);';
      html += 'background:rgba(0,0,0,.04);padding:.25rem .6rem;border-radius:4px;max-width:300px;overflow:hidden;text-overflow:ellipsis;">';
      html += 'P(x) = ' + polyBeforeStr + '</div>';
    }
    html += '</div>';

    /* ── Contenido según método ── */
    if (res.method === 'muller') {
      /* Semilla usada */
      if (res.seedUsed) {
        const [p0,p1,p2] = res.seedUsed;
        html += '<div style="font-family:var(--font-main);font-size:.75rem;color:var(--gray-500);margin-bottom:.5rem;">';
        html += '⚡ Semilla inicial: x₀=' + cxStr(p0,4) + '  x₁=' + cxStr(p1,4) + '  x₂=' + cxStr(p2,4);
        html += '</div>';
      }

      /* Tabla resumen + bloques detallados */
      html += '<div style="margin-bottom:.75rem;">';
      html += '<div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;letter-spacing:.4px;color:var(--gray-500);margin-bottom:.4rem;">Tabla de Iteraciones</div>';
      html += buildMullerComplexTable(res.rows, tol, col);
      html += '</div>';

      html += '<div>';
      html += '<div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;letter-spacing:.4px;color:var(--gray-500);margin-bottom:.4rem;">Desarrollo Paso a Paso</div>';
      html += buildMullerStepBlocks(res.rows, tol, col);
      html += '</div>';

    } else if (res.method === 'quadratic' && !quadraticDone) {
      /* Mostrar fórmula cuadrática una sola vez para el par */
      html += buildQuadraticSteps(res.quadraticSteps, col, i);
      quadraticDone = true;

    } else if (res.method === 'linear') {
      html += '<div class="muller-step-block" style="border-left:3px solid ' + col + ';">';
      html += '<div class="muller-step-header" style="background:' + col + '12;border-bottom:1px solid ' + col + '25;">';
      html += '<div class="muller-step-num" style="background:' + col + ';font-size:.75rem;">L</div>';
      html += '<div class="muller-step-title">Ecuación Lineal Residual</div>';
      html += '</div><div class="muller-step-body">';
      html += '<div class="muller-data-row" style="grid-column:1/-1;border-color:' + col + ';background:' + col + '08;">';
      html += '<div class="muller-data-label">ax + b = 0  →  x = −b/a</div>';
      if (res.a && res.b) {
        html += '<div class="muller-data-val">a = ' + cxStr(res.a, 8) + '</div>';
        html += '<div class="muller-data-val">b = ' + cxStr(res.b, 8) + '</div>';
      }
      html += '<div class="muller-data-val accent" style="color:' + col + ';font-size:.95rem;font-weight:700;">x = ' + fmt.text + '</div>';
      html += '</div></div></div>';
    }

    /* Deflación: polinomio resultante */
    if (res.method === 'muller' && polyAfterStr && res.polyAfter.length > 1) {
      html += '<div style="margin-top:.75rem;padding:.6rem 1rem;background:var(--gray-50);border-radius:5px;border:1px solid var(--border);">';
      html += '<span style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);">Polinomio deflactado (grado ' + (res.polyAfter.length-1) + '):</span> ';
      html += '<span style="font-family:var(--font-mono);font-size:.82rem;font-weight:600;color:var(--gray-700);">Q(x) = ' + polyAfterStr + '</span>';
      html += '</div>';
    }

    html += '</div>'; // cierre raíz i
  });

  html += '</div></div>'; // cierre card paso a paso

  container.innerHTML = html;
  if (typeof numerixExport !== 'undefined') setTimeout(() => numerixExport.showT3Bar(), 50);
}

/* ══════════════════════════════════════════════════════════════
   BÜSQUEDA POR SCAN (para la gráfica y compatibilidad)
   Se mantiene el m3FindAllRoots existente para el gráfico
══════════════════════════════════════════════════════════════ */

/* ── Evento botón Müller — lógica ACTUALIZADA ───────────────── */
document.addEventListener('DOMContentLoaded', () => {
  const btn = document.getElementById('btnMuller');
  if (btn) btn.addEventListener('click', () => {
    const expr  = document.getElementById('m3Func').value.trim();
    const x0    = parseFloat(document.getElementById('m3X0').value);
    const x1    = parseFloat(document.getElementById('m3X1').value);
    const x2    = parseFloat(document.getElementById('m3X2').value);
    const tol   = parseFloat(document.getElementById('m3Tol').value);
    const alertEl = document.getElementById('m3Alert');
    alertEl.innerHTML = '';
    document.getElementById('m3Result').innerHTML = '';

    /* Validaciones básicas */
    if (!expr)           { showAlert('m3Alert','danger','Ingrese la función f(x).'); return; }
    if (checkUpperX(expr, 'm3Alert')) return;
    if (isNaN(tol)||tol<=0) { showAlert('m3Alert','danger','La tolerancia debe ser positiva.'); return; }

    try {
      /* ── PASO 1: intentar parsear como polinomio con coeficientes ── */
      let coeffsRaw = null;
      let degree    = 0;
      try {
        const parsed = parsePolynomial(expr);
        coeffsRaw = parsed.coeffs;
        degree    = parsed.maxGrado;
      } catch(parseErr) {
        // No es polinomio estándar — usar modo evalF (scan)
      }

      if (coeffsRaw && degree >= 1) {
        /* ═══ MODO DEFLACIÓN: polinomio → todas las raíces ═══ */
        const roots = mullerAllRoots(coeffsRaw, tol < 1e-10 ? 1e-10 : tol);

        /* Renderizar resultado completo */
        renderRootsResult(roots, coeffsRaw, expr, tol);

        /* Gráfica: usar evalF sobre el rango visible */
        const xmin = -6;
        const xmax = 6;

        /* Construir un resultado principal para la gráfica (Müller estándar) */
        const mainRes = isNaN(x0)||isNaN(x1)||isNaN(x2)||(x0===x1||x1===x2||x0===x2)
          ? mullerMethod(expr, 0, 1, 2, tol)
          : mullerMethod(expr, x0, x1, x2, tol);

        /* Raíces reales para pintar en la gráfica */
        const realRootsForGraph = roots
          .filter(r => Math.abs(r.i) < 1e-5)
          .map(r => ({ root: r.r, converged: r.converged, iterations: r.iters || 0 }));

        m3InitGraph(mainRes.rows, expr, mainRes.root, realRootsForGraph);

        /* Alerta resumen */
        const nReal = roots.filter(r => Math.abs(r.i) < 1e-6).length;
        const nCplx = roots.length - nReal;
        const parts = [];
        if (nReal > 0) parts.push(nReal + ' real' + (nReal>1?'es':''));
        if (nCplx > 0) parts.push(nCplx + ' compleja' + (nCplx>1?'s':''));
        alertEl.innerHTML = '<div class="alert alert-success"><span class="alert-icon">✓</span><span>' +
          '<strong>' + roots.length + ' raíces encontradas</strong> (' + parts.join(' + ') + ') ' +
          'para f(x) = ' + expr +
          '</span></div>';

      } else {
        /* ═══ MODO SCAN: función general (no polinomio puro) ═══ */
        if (isNaN(x0)||isNaN(x1)||isNaN(x2))
          { showAlert('m3Alert','danger','Ingrese x₀, x₁, x₂ válidos.'); return; }
        if (x0===x1||x1===x2||x0===x2)
          { showAlert('m3Alert','danger','Los tres puntos iniciales deben ser distintos.'); return; }

        try { evalF(expr,x0); evalF(expr,x1); evalF(expr,x2); }
        catch(e) { showAlert('m3Alert','danger','Error al evaluar f(x): '+e.message); return; }

        const mainRes = mullerMethod(expr, x0, x1, x2, tol);
        const xmin = -6;
        const xmax = 6;
        const allRoots = m3FindAllRoots(expr, xmin, xmax, tol);
        if (mainRes.converged && isFinite(mainRes.root)) {
          const already = allRoots.some(r => Math.abs(r.root - mainRes.root) < tol*1000);
          if (!already) { allRoots.push(mainRes); allRoots.sort((a,b)=>a.root-b.root); }
        }
        const allRootsHtml = renderAllRootsPanel(allRoots, expr, tol);
        renderMullerResult(mainRes, expr, x0, x1, x2, tol, allRootsHtml);
        m3InitGraph(mainRes.rows, expr, mainRes.root, allRoots);

        const msg = mainRes.converged
          ? '✓ Convergió en '+mainRes.iterations+' iter. — Raíz ≈ '+m3Fmt(mainRes.root,8)
          : '⚠ No convergió. Pruebe otros puntos x₀, x₁, x₂';
        alertEl.innerHTML = '<div class="alert alert-'+(mainRes.converged?'success':'warning')+
          '"><span class="alert-icon">'+(mainRes.converged?'✓':'⚠')+'</span><span>'+msg+'</span></div>';
      }

    } catch(e) {
      showAlert('m3Alert','danger','Error: ' + e.message);
    }
  });

  /* Vincular nav T3 */
  document.querySelectorAll('.t3-method-nav[data-t3panel]').forEach(el => {
    el.addEventListener('click', () => t3GoTo(el.getAttribute('data-t3panel')));
  });
});

/* ══════════════════════════════════════════════════════════════
   MÜLLER — GRÁFICA EN VIVO CON CANVAS
   · Curva f(x) sobre fondo oscuro
   · Parábola interpolante de la iteración activa
   · Nodos x0, x1, x2 animados
   · Todas las raíces resaltadas con colores
   · Slider por iteración + animación automática
══════════════════════════════════════════════════════════════ */
function renderAllRootsPanel(allRoots, expr, tol) {
  const COLORS = ['#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6','#ef4444'];
  const n = allRoots.length;

  let html = '<div class="card" style="margin-bottom:1.25rem;border-top:3px solid #10b981;">';
  html += '<div class="card-header">';
  html += '<div class="card-header-icon green">🎯</div>';
  html += '<div>';
  html += '<div class="card-title">Todas las Raíces Reales encontradas</div>';
  html += '<div class="card-subtitle">Scan automático + Müller en cada intervalo detectado</div>';
  html += '</div>';
  html += '<span style="margin-left:auto;background:var(--success-light);color:#065f46;';
  html += 'font-family:var(--font-main);font-size:.78rem;font-weight:700;';
  html += 'padding:.3rem .95rem;border-radius:999px;border:1px solid #6ee7b7;">';
  html += n + ' raíz' + (n !== 1 ? 'ces' : '') + ' real' + (n !== 1 ? 'es' : '') + '</span>';
  html += '</div>';

  /* Tarjetas de raíces */
  html += '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:.75rem;padding:0 1.5rem 1.25rem;">';
  allRoots.forEach((r, i) => {
    const col = COLORS[i % COLORS.length];
    let fv = '?';
    try { fv = evalF(expr, r.root).toExponential(3); } catch(e) {}
    html += '<div style="border-radius:var(--radius-sm);border:1.5px solid ' + col + '33;';
    html += 'border-left:4px solid ' + col + ';padding:.875rem 1rem;background:var(--gray-50);">';
    /* Badge número */
    html += '<div style="display:flex;align-items:center;gap:.5rem;margin-bottom:.5rem;">';
    html += '<span style="background:' + col + ';color:#fff;font-family:var(--font-main);';
    html += 'font-size:.65rem;font-weight:700;padding:.15rem .55rem;border-radius:4px;">r' + (i+1) + '</span>';
    if (r.converged) {
      html += '<span style="font-family:var(--font-main);font-size:.65rem;color:var(--gray-400);">';
      html += r.iterations + ' iter.</span>';
    }
    html += '</div>';
    /* Valor */
    html += '<div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:' + col + ';margin-bottom:.3rem;">';
    html += 'x ≈ ' + m3Fmt(r.root, 8) + '</div>';
    /* f(raíz) */
    html += '<div style="font-family:var(--font-mono);font-size:.75rem;color:var(--gray-500);">';
    html += 'f(x) ≈ ' + fv + '</div>';
    html += '</div>';
  });
  html += '</div>';

  if (n === 0) {
    html += '<div style="padding:1rem 1.5rem;font-family:var(--font-main);font-size:.88rem;color:var(--gray-500);">';
    html += '⚠ No se detectaron raíces reales en el rango visible. Ajuste x min / x max y presione ↺ Redibujar.</div>';
  }

  html += '</div>';
  return html;
}

window.t3GoTo = t3GoTo;

/* ══════════════════════════════════════════════════════════════
   BAIRSTOW — Motor completo
   División sintética doble → deflación → todas las raíces
   reales y complejas conjugadas
══════════════════════════════════════════════════════════════ */

/**
 * bairstowStep(coeffs, r0, s0, tol, maxIter)
 *   Una sesión de Bairstow. Retorna:
 *   { r, s, rows, converged, iterations, quotient }
 */
function bairstowStep(coeffs, r0, s0, tol, maxIter) {
  let r = r0, s = s0;
  const n = coeffs.length - 1;
  const rows = [];

  for (let iter = 1; iter <= maxIter; iter++) {
    /* ── División sintética 1 → b ── */
    const b = new Array(n + 1).fill(0);
    b[0] = coeffs[0];
    if (n > 0) b[1] = coeffs[1] + r * b[0];
    for (let i = 2; i <= n; i++)
      b[i] = coeffs[i] + r * b[i-1] + s * b[i-2];

    /* ── División sintética 2 → c ── */
    const c = new Array(n).fill(0);
    c[0] = b[0];
    if (n > 1) c[1] = b[1] + r * c[0];
    for (let i = 2; i <= n - 1; i++)
      c[i] = b[i] + r * c[i-1] + s * c[i-2];

    const R   = b[n];
    const S   = b[n - 1];
    const cn2 = (c[n-2] !== undefined) ? c[n-2] : 0;
    const cn3 = (c[n-3] !== undefined) ? c[n-3] : 0;
    const cn1 = (c[n-1] !== undefined) ? c[n-1] : 0;

    /* ── Jacobiano y correcciones ── */
    const det = cn2 * cn2 - cn1 * cn3;
    if (Math.abs(det) < 1e-20) break;

    const dr = (-S * cn2 + R * cn3) / det;
    const ds = (-R * cn2 + S * cn1) / det;

    const ea_r = Math.abs(r + dr) > 1e-14 ? Math.abs(dr) / Math.abs(r + dr) * 100 : 0;
    const ea_s = Math.abs(s + ds) > 1e-14 ? Math.abs(ds) / Math.abs(s + ds) * 100 : 0;

    rows.push({ iter, r, s, b: [...b], c: [...c], R, S, dr, ds, ea_r, ea_s,
                converged: Math.abs(dr) < tol && Math.abs(ds) < tol });

    r += dr;  s += ds;
    if (!isFinite(r) || !isFinite(s) || Math.abs(r) > 1e10 || Math.abs(s) > 1e10) break;

    if (Math.abs(dr) < tol && Math.abs(ds) < tol) {
      /* Recalcular b final para el cociente */
      const bf = new Array(n + 1).fill(0);
      bf[0] = coeffs[0];
      if (n > 0) bf[1] = coeffs[1] + r * bf[0];
      for (let i = 2; i <= n; i++) bf[i] = coeffs[i] + r * bf[i-1] + s * bf[i-2];
      return { r, s, rows, converged: true, iterations: iter, quotient: bf.slice(0, n - 1) };
    }
  }

  /* No convergió — devolver quotient del último b */
  const bf = new Array(n + 1).fill(0);
  bf[0] = coeffs[0];
  if (n > 0) bf[1] = coeffs[1] + r * bf[0];
  for (let i = 2; i <= n; i++) bf[i] = coeffs[i] + r * bf[i-1] + s * bf[i-2];
  return { r, s, rows, converged: false, iterations: maxIter, quotient: bf.slice(0, n - 1) };
}

/* Raíces de x² − r·x − s = 0 */
function bsQuadRoots(r, s) {
  const disc = r * r + 4 * s;
  if (disc >= 0) {
    const sq = Math.sqrt(disc);
    return [{ re: (r + sq) / 2, im: 0 }, { re: (r - sq) / 2, im: 0 }];
  }
  const sq = Math.sqrt(-disc);
  return [{ re: r / 2, im: sq / 2 }, { re: r / 2, im: -sq / 2 }];
}

/**
 * bairstowAllRoots(coeffs, r0, s0, tol, maxIter)
 *   Motor principal con deflación iterativa.
 *   Retorna { roots, sessions }
 */
function bairstowAllRoots(coeffs, r0, s0, tol, maxIter) {
  let curr = [...coeffs];
  const roots = [], sessions = [];
  const SEEDS = [[r0,s0],[0.5,-1],[1,1],[-1,-1],[0,-1],[2,-2],[-0.5,0.5],[1,-2],[-1,1],[0.1,-0.5]];

  while (curr.length >= 3) {
    const n = curr.length - 1;

    /* Lineal: ax + b = 0 */
    if (n === 1) {
      const root = -curr[1] / curr[0];
      roots.push({ re: root, im: 0, type: 'linear' });
      sessions.push({ type: 'linear', root, rows: [], polyBefore: [...curr], polyAfter: [] });
      break;
    }

    /* Cuadrática residual: fórmula directa */
    if (n === 2) {
      const [a, b, c] = curr;
      const disc = b * b - 4 * a * c;
      if (disc >= 0) {
        roots.push({ re: (-b + Math.sqrt(disc)) / (2*a), im: 0, type: 'quadratic_direct' });
        roots.push({ re: (-b - Math.sqrt(disc)) / (2*a), im: 0, type: 'quadratic_direct' });
      } else {
        roots.push({ re: -b/(2*a), im:  Math.sqrt(-disc)/(2*a), type: 'quadratic_direct' });
        roots.push({ re: -b/(2*a), im: -Math.sqrt(-disc)/(2*a), type: 'quadratic_direct' });
      }
      sessions.push({ type: 'quadratic_direct', coeffs: [...curr], rows: [],
                      polyBefore: [...curr], polyAfter: [] });
      break;
    }

    /* Grado ≥ 3: Bairstow con semillas variadas */
    let found = null;
    for (const [sr, ss] of SEEDS) {
      const res = bairstowStep(curr, sr, ss, tol, maxIter);
      if (res.converged && isFinite(res.r) && isFinite(res.s)) { found = res; break; }
    }
    if (!found) break;

    const qRoots = bsQuadRoots(found.r, found.s);
    qRoots.forEach(z => roots.push({ ...z, type: 'bairstow' }));
    sessions.push({ type: 'bairstow', r: found.r, s: found.s,
                    rows: found.rows, roots: qRoots,
                    quotient: found.quotient, iterations: found.iterations,
                    polyBefore: [...curr], polyAfter: found.quotient });
    curr = found.quotient;
  }

  return { roots, sessions };
}

/* ── Tabla iteraciones Bairstow ─────────────────────────────── */
function buildBairstowTable(rows, tol, color) {
  if (!rows || rows.length === 0)
    return '<p style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-400);padding:.5rem 0;">Sin iteraciones.</p>';

  const thS = `padding:.6rem .875rem;font-family:var(--font-main);font-size:.7rem;font-weight:700;
    color:#fff;background:${color};border-bottom:2px solid rgba(255,255,255,.2);white-space:nowrap;text-align:right;`;

  let h = '<div style="overflow-x:auto;"><table class="muller-table" style="font-size:.8rem;"><thead><tr>';
  ['Iter.','r','s','b_{n−1} (S)','b_n (R)','Δr','Δs','Eₐ(r)%','Eₐ(s)%'].forEach((hh, i) =>
    h += `<th style="${thS}${i===0?'text-align:center;':''}">${hh}</th>`);
  h += '</tr></thead><tbody>';

  rows.forEach((row, i) => {
    const bg = row.converged ? 'var(--success-light)' : i % 2 ? 'var(--gray-50)' : '#fff';
    const fc = row.converged ? '#065f46' : 'var(--gray-700)';
    const td = (v, dec=8, center=false) => {
      const ts = `padding:.55rem .875rem;font-family:var(--font-mono);font-size:.78rem;
        text-align:${center?'center':'right'};background:${bg};color:${fc};border-bottom:1px solid var(--border);`;
      const txt = (v === null || v === undefined || !isFinite(v)) ? '—'
                : typeof v === 'number' ? v.toFixed(dec) : v;
      return `<td style="${ts}">${txt}</td>`;
    };
    h += '<tr>';
    h += td(row.iter, 0, true);
    h += td(row.r, 8);  h += td(row.s, 8);
    h += td(row.S, 8);  h += td(row.R, 8);
    h += td(row.dr, 8); h += td(row.ds, 8);
    h += td(row.ea_r, 4); h += td(row.ea_s, 4);
    h += '</tr>';
  });
  return h + '</tbody></table></div>';
}

/* ── Paso a paso Bairstow ────────────────────────────────────── */
function buildBairstowSteps(rows, tol, color) {
  if (!rows || rows.length === 0) return '';
  return rows.map(row => {
    const isConv = row.converged;
    return `
    <div class="muller-step-block" style="border-left:3px solid ${color};">
      <div class="muller-step-header" style="background:${color}12;border-bottom:1px solid ${color}25;">
        <div class="muller-step-num" style="background:${color};">${row.iter}</div>
        <div class="muller-step-title">Iteración ${row.iter}${isConv?` — <span style="color:${color};">✓ Convergencia</span>`:''}</div>
      </div>
      <div class="muller-step-body">
        <div class="muller-data-row">
          <div class="muller-data-label">Semillas actuales</div>
          <div class="muller-data-val">r = ${row.r.toFixed(8)}</div>
          <div class="muller-data-val">s = ${row.s.toFixed(8)}</div>
        </div>
        <div class="muller-data-row">
          <div class="muller-data-label">División sintética 1 → b</div>
          ${row.b.map((v,i)=>`<div class="muller-data-val">b[${i}] = ${typeof v==='number'?v.toFixed(6):'?'}</div>`).join('')}
        </div>
        <div class="muller-data-row">
          <div class="muller-data-label">División sintética 2 → c</div>
          ${row.c.map((v,i)=>`<div class="muller-data-val">c[${i}] = ${typeof v==='number'?v.toFixed(6):'?'}</div>`).join('')}
        </div>
        <div class="muller-data-row" style="grid-column:1/-1;border-color:${color};background:${color}08;">
          <div class="muller-data-label">Residuos y correcciones</div>
          <div class="muller-data-val">R = b[n] = ${row.R.toFixed(8)}</div>
          <div class="muller-data-val">S = b[n−1] = ${row.S.toFixed(8)}</div>
          <div class="muller-data-val accent" style="color:${color};font-weight:700;">Δr = ${row.dr.toFixed(8)}</div>
          <div class="muller-data-val accent" style="color:${color};font-weight:700;">Δs = ${row.ds.toFixed(8)}</div>
          <div class="muller-data-val muted">Eₐ(r)% = ${row.ea_r.toFixed(4)} · Eₐ(s)% = ${row.ea_s.toFixed(4)}
            ${isConv?`<span style="color:${color};font-weight:700;"> ✓ &lt; ${tol}</span>`:'  continuar'}
          </div>
        </div>
      </div>
    </div>`;
  }).join('');
}

/* ── Renderizar resultado Bairstow ───────────────────────────── */
function renderBairstowResult(data, expr, tol) {
  const container = document.getElementById('bsResult');
  const { roots, sessions } = data;
  const COLORS = ['#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6','#ef4444'];
  const realRoots = roots.filter(r => Math.abs(r.im) < 1e-6);
  const cplxRoots = roots.filter(r => Math.abs(r.im) >= 1e-6);

  let html = '';

  /* ── 1. Resumen ── */
  html += `<div class="card" style="margin-bottom:1.25rem;border-top:4px solid #10b981;">
    <div class="card-header">
      <div class="card-header-icon green">🎯</div>
      <div>
        <div class="card-title">Todas las Raíces — Bairstow + Deflación</div>
        <div class="card-subtitle">f(x) = ${expr}  ·  tol = ${tol}  ·  ${sessions.length} sesión(es)</div>
      </div>
      <div style="margin-left:auto;display:flex;gap:.5rem;flex-wrap:wrap;">
        ${realRoots.length?`<span style="background:var(--success-light);color:#065f46;font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #6ee7b7;">${realRoots.length} real${realRoots.length>1?'es':''}</span>`:''}
        ${cplxRoots.length?`<span style="background:var(--primary-light);color:var(--primary-dark);font-family:var(--font-main);font-size:.72rem;font-weight:700;padding:.25rem .75rem;border-radius:999px;border:1px solid #a5b4fc;">${cplxRoots.length} compleja${cplxRoots.length>1?'s':''}</span>`:''}
      </div>
    </div>`;

  /* Tarjetas */
  html += '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:.75rem;padding:0 1.5rem 1.25rem;">';
  roots.forEach((r, i) => {
    const col    = COLORS[i % COLORS.length];
    const isReal = Math.abs(r.im) < 1e-6;
    const val    = isReal ? r.re.toFixed(8)
                 : `${r.re.toFixed(6)} ${r.im >= 0 ? '+' : '−'} ${Math.abs(r.im).toFixed(6)}i`;
    html += `<div style="border-radius:var(--radius-sm);border:1.5px solid ${col}33;border-left:5px solid ${col};padding:.875rem 1rem;background:var(--gray-50);">
      <div style="display:flex;align-items:center;gap:.4rem;margin-bottom:.5rem;">
        <span style="background:${col};color:#fff;font-family:var(--font-main);font-size:.65rem;font-weight:700;padding:.15rem .55rem;border-radius:4px;">r${i+1}</span>
        <span style="font-family:var(--font-main);font-size:.65rem;font-weight:600;color:${isReal?'#065f46':'#3730a3'};background:${isReal?'#f0fdf4':'#eef2ff'};padding:.1rem .45rem;border-radius:4px;">${isReal?'Real':'Compleja'}</span>
      </div>
      <div style="font-family:var(--font-mono);font-size:.95rem;font-weight:700;color:${col};margin-bottom:.3rem;word-break:break-all;">${val}</div>
    </div>`;
  });
  html += '</div></div>';

  /* ── 2. Sesiones paso a paso ── */
  html += `<div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header">
      <div class="card-header-icon green">🔍</div>
      <div>
        <div class="card-title">Proceso Completo — Sesiones de Bairstow</div>
        <div class="card-subtitle">Cada sesión extrae un factor cuadrático (x² − r·x − s) por deflación</div>
      </div>
    </div>
    <div style="padding:1.25rem 1.5rem;">`;

  let rootIdx = 0;
  sessions.forEach((sess, si) => {
    const col = COLORS[si % COLORS.length];
    html += `<div style="margin-bottom:1.75rem;">`;

    /* Cabecera sesión */
    html += `<div style="display:flex;align-items:center;gap:.75rem;margin-bottom:.75rem;padding:.75rem 1rem;
      background:${col}0D;border-radius:var(--radius-sm);border:1.5px solid ${col}33;">
      <span style="background:${col};color:#fff;font-family:var(--font-main);font-size:.75rem;font-weight:700;padding:.2rem .65rem;border-radius:5px;">
        Sesión ${si+1}
      </span>`;

    if (sess.type === 'bairstow') {
      html += `<div style="flex:1;">`;
      sess.roots.forEach((z, zi) => {
        const isR = Math.abs(z.im) < 1e-6;
        const v   = isR ? z.re.toFixed(8) : `${z.re.toFixed(6)} ${z.im>=0?'+':'−'} ${Math.abs(z.im).toFixed(6)}i`;
        html += `<div style="font-family:var(--font-mono);font-size:.88rem;font-weight:700;color:${col};">r${rootIdx+zi+1} = ${v}</div>`;
      });
      html += `<div style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);margin-top:3px;">
        Factor cuadrático: x² − (${sess.r.toFixed(6)})x − (${sess.s.toFixed(6)})
        &nbsp;·&nbsp; ${sess.iterations} iteraciones
      </div></div>`;
      rootIdx += 2;
    } else if (sess.type === 'linear') {
      html += `<div style="font-family:var(--font-mono);font-size:.88rem;color:${col};font-weight:700;">
        Ecuación lineal → x = ${sess.root.toFixed(8)}</div>`;
      rootIdx++;
    } else {
      html += `<div style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-600);">
        Cuadrática residual — fórmula cuadrática directa</div>`;
      rootIdx += 2;
    }
    html += `</div>`; /* cierre cabecera */

    if (sess.type === 'bairstow' && sess.rows.length > 0) {
      /* Tabla */
      html += `<div style="margin-bottom:.75rem;">
        <div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;
          letter-spacing:.4px;color:var(--gray-500);margin-bottom:.4rem;">Tabla de Iteraciones</div>
        ${buildBairstowTable(sess.rows, tol, col)}
      </div>`;

      /* Paso a paso */
      html += `<div>
        <div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;
          letter-spacing:.4px;color:var(--gray-500);margin-bottom:.4rem;">Desarrollo Paso a Paso</div>
        ${buildBairstowSteps(sess.rows, tol, col)}
      </div>`;

      /* Polinomio deflactado */
      if (sess.polyAfter && sess.polyAfter.length > 1) {
        html += `<div style="margin-top:.75rem;padding:.6rem 1rem;background:var(--gray-50);border-radius:5px;border:1px solid var(--border);">
          <span style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);">Polinomio deflactado (grado ${sess.polyAfter.length-1}):</span>
          <span style="font-family:var(--font-mono);font-size:.82rem;font-weight:600;color:var(--gray-700);">
            Q(x) = ${polyToString(sess.polyAfter.map(v => CX.make(v)))}
          </span>
        </div>`;
      }
    } else if (sess.type === 'quadratic_direct') {
      /* Mostrar fórmula cuadrática */
      const [a, b, c] = sess.coeffs;
      const disc = b*b - 4*a*c;
      html += `<div class="muller-step-block" style="border-left:3px solid ${col};">
        <div class="muller-step-header" style="background:${col}12;border-bottom:1px solid ${col}25;">
          <div class="muller-step-num" style="background:${col};font-size:.75rem;">Q</div>
          <div class="muller-step-title">Cuadrática residual — fórmula directa</div>
        </div>
        <div class="muller-step-body">
          <div class="muller-data-row">
            <div class="muller-data-label">Coeficientes del cociente</div>
            <div class="muller-data-val">a = ${a.toFixed(6)}</div>
            <div class="muller-data-val">b = ${b.toFixed(6)}</div>
            <div class="muller-data-val">c = ${c.toFixed(6)}</div>
          </div>
          <div class="muller-data-row" style="grid-column:1/-1;border-color:${col};background:${col}08;">
            <div class="muller-data-label">Discriminante Δ = b²−4ac</div>
            <div class="muller-data-val">Δ = ${disc.toFixed(6)} ${disc<0?'(raíces complejas)':'(raíces reales)'}</div>
          </div>
        </div>
      </div>`;
    }

    html += `</div>`; /* cierre sesión */
  });

  html += '</div></div>'; /* cierre card */
  container.innerHTML = html;

  /* Guardar para export */
  if (typeof state !== 'undefined') state.bsLast = { data, expr, tol };

  /* Inicializar gráfica interactiva Bairstow */
  setTimeout(() => {
    if (typeof bsGraphInit === 'function') {
      bsGraphInit(
        /* coeffs raw */   (typeof parsePolynomial === 'function') ? (() => { try { return parsePolynomial(expr).coeffs; } catch(e) { return []; } })() : [],
        /* roots */        data.roots || [],
        /* sessions */     data.sessions || [],
        /* expr */         expr
      );
    }
    const b = document.getElementById('bs-download-bar');
    if (b) b.style.display = 'block';
  }, 50);
}

/* ── Evento botón Bairstow ───────────────────────────────────── */
document.addEventListener('DOMContentLoaded', () => {
  const btn = document.getElementById('btnBairstow');
  if (!btn) return;
  btn.addEventListener('click', () => {
    clearAlert('bsAlert');
    document.getElementById('bsResult').innerHTML = '';
    const expr = document.getElementById('bsFunc').value.trim();
    if (checkUpperX(expr, 'bsAlert')) return;
    const r0   = parseFloat(document.getElementById('bsR0').value);
    const s0   = parseFloat(document.getElementById('bsS0').value);
    const tol  = parseFloat(document.getElementById('bsTol').value);

    if (!expr)                { showAlert('bsAlert','danger','Ingrese el polinomio.'); return; }
    if (isNaN(r0)||isNaN(s0)) { showAlert('bsAlert','danger','r₀ y s₀ deben ser numéricos.'); return; }
    if (isNaN(tol)||tol<=0)   { showAlert('bsAlert','danger','Tolerancia inválida.'); return; }

    try {
      const parsed = parsePolynomial(expr);
      const data   = bairstowAllRoots(parsed.coeffs, r0, s0, tol, 200);
      renderBairstowResult(data, expr, tol);
      const nR = data.roots.filter(r => Math.abs(r.im) < 1e-6).length;
      const nC = data.roots.length - nR;
      const parts = [];
      if (nR > 0) parts.push(nR + ' real' + (nR > 1 ? 'es' : ''));
      if (nC > 0) parts.push(nC + ' compleja' + (nC > 1 ? 's' : ''));
      showAlert('bsAlert', 'success',
        `✓ ${data.roots.length} raíces encontradas (${parts.join(' + ')}) — ${data.sessions.length} sesión(es) de Bairstow`);
    } catch(e) { showAlert('bsAlert', 'danger', 'Error: ' + e.message); }
  });
});

/* ══════════════════════════════════════════════════════════════
   MÉTODO DE HORNER
   ─────────────────────────────────────────────────────────────
   Evalúa P(c) mediante la recurrencia anidada:
     bₙ = aₙ
     bₙ₋₁ = aₙ₋₁ + c·bₙ
     ...
     b₀ = a₀ + c·b₁  →  b₀ = P(c)
   El cociente Q(x) = P(x)/(x−c) tiene coeficientes b₁…bₙ.
   Segunda aplicación sobre Q(x) en c da P′(c) = Q(c).
══════════════════════════════════════════════════════════════ */

/**
 * hornerEval(coeffs, c)
 *   coeffs = [aₙ, aₙ₋₁, …, a₁, a₀]
 *   Retorna {
 *     pc      : P(c) = b₀,
 *     b       : array completo [bₙ, bₙ₋₁, …, b₀],
 *     quotient: [bₙ, …, b₁]  (coeficientes de Q(x)),
 *     steps   : array de pasos para mostrar
 *   }
 */
function hornerEval(coeffs, c) {
  const n = coeffs.length - 1;
  const b = new Array(coeffs.length);
  const steps = [];

  // bₙ = aₙ
  b[0] = coeffs[0];
  steps.push({
    k: n, ak: coeffs[0], cTimesPrev: null, bk: b[0],
    formula: `b_{${n}} = a_{${n}} = ${coeffs[0]}`
  });

  // bₙ₋ₖ = aₙ₋ₖ + c · bₙ₋ₖ₊₁
  for (let i = 1; i <= n; i++) {
    b[i] = coeffs[i] + c * b[i-1];
    const ki = n - i;
    const cTimesPrev = c * b[i-1];
    steps.push({
      k: ki, ak: coeffs[i], cTimesPrev, bk: b[i],
      formula: `b_{${ki}} = a_{${ki}} + c·b_{${ki+1}} = ${coeffs[i]} + (${c})(${b[i-1]}) = ${b[i]}`
    });
  }

  return { pc: b[n], b, quotient: b.slice(0, n), steps, n };
}

/* ── Tabla Horner de la profesora: columnas aₖ | c·bₖ₊₁ | bₖ ─ */
function buildHornerTable(steps, c, color) {
  const thS = `padding:.6rem .875rem;font-family:var(--font-main);font-size:.7rem;font-weight:700;
    color:#fff;background:${color};border-bottom:2px solid rgba(255,255,255,.2);white-space:nowrap;text-align:center;`;

  let h = `<div style="overflow-x:auto;margin-bottom:.75rem;">
    <table class="muller-table" style="font-size:.82rem;min-width:340px;">
      <thead><tr>
        <th style="${thS}">k</th>
        <th style="${thS}">aₖ</th>
        <th style="${thS}">c·b_{k+1}</th>
        <th style="${thS}">bₖ = aₖ + c·b_{k+1}</th>
      </tr></thead>
      <tbody>`;

  steps.forEach((step, i) => {
    const isLast = i === steps.length - 1;
    const bg = isLast ? `${color}20` : i % 2 ? 'var(--gray-50)' : '#fff';
    const fc = isLast ? color : 'var(--gray-700)';
    const fw = isLast ? '700' : '400';
    const tdS = `padding:.55rem .875rem;font-family:var(--font-mono);font-size:.8rem;
      text-align:center;background:${bg};color:${fc};font-weight:${fw};border-bottom:1px solid var(--border);`;
    const fmt = v => (v === null || v === undefined) ? '—' : Number(v).toFixed(6);

    h += `<tr>
      <td style="${tdS}">${step.k}</td>
      <td style="${tdS}">${fmt(step.ak)}</td>
      <td style="${tdS}">${step.cTimesPrev === null ? '—' : fmt(step.cTimesPrev)}</td>
      <td style="${tdS}${isLast?`border-left:2px solid ${color};`:''}">${fmt(step.bk)}</td>
    </tr>`;
  });

  const last = steps[steps.length - 1];
  h += `<tr style="background:${color}15;">
    <td colspan="3" style="padding:.6rem .875rem;font-family:var(--font-main);font-size:.8rem;
      text-align:right;font-weight:700;color:${color};border-top:2px solid ${color};">
      P(c) = b₀ =
    </td>
    <td style="padding:.6rem .875rem;font-family:var(--font-mono);font-size:.9rem;
      font-weight:700;color:${color};border-top:2px solid ${color};border-left:2px solid ${color};">
      ${Number(last.bk).toFixed(8)}
    </td>
  </tr>`;

  return h + '</tbody></table></div>';
}

/* ── Pasos escritos como en la pizarra de la profesora ─────── */
function buildHornerSteps(steps, c, color) {
  let h = `<div style="background:var(--gray-50);border:1px solid var(--border);
    border-radius:var(--radius-sm);padding:1rem 1.25rem;font-family:var(--font-mono);
    font-size:.85rem;line-height:2;">`;

  steps.forEach((step, i) => {
    const isLast = i === steps.length - 1;
    const color2 = isLast ? color : 'var(--gray-700)';
    const fw     = isLast ? '700' : '400';
    if (step.cTimesPrev === null) {
      h += `<div style="color:${color2};font-weight:${fw};">
        b<sub>${step.k}</sub> = a<sub>${step.k}</sub> = <strong>${Number(step.ak).toFixed(6)}</strong>
      </div>`;
    } else {
      h += `<div style="color:${color2};font-weight:${fw};">
        b<sub>${step.k}</sub> = a<sub>${step.k}</sub> + c·b<sub>${step.k+1}</sub>
        = ${Number(step.ak).toFixed(6)} + (${c})(${Number(steps[i-1].bk).toFixed(6)})
        = <strong style="color:${color};">${Number(step.bk).toFixed(6)}</strong>
      </div>`;
    }
  });

  const last = steps[steps.length - 1];
  h += `<div style="margin-top:.5rem;padding:.5rem .75rem;background:${color}15;
    border-radius:5px;border-left:3px solid ${color};color:${color};font-weight:700;">
    ∴ P(c) = b₀ = ${Number(last.bk).toFixed(8)}
  </div>`;

  return h + '</div>';
}

/**
 * hornerFullEval(coeffs, c)
 *   Aplica Horner DOS veces:
 *   1ra → P(c) con cociente Q(x)
 *   2da → Q(c) = P′(c)
 */
function hornerFullEval(coeffs, c) {
  const first  = hornerEval(coeffs, c);            // P(c)
  const second = hornerEval(first.quotient, c);    // Q(c) = P'(c)
  return { first, second, pc: first.pc, dpc: second.pc };
}

/* ── Renderizar resultado Horner ─────────────────────────────── */
function renderNHResult(data, expr, c) {
  const container = document.getElementById('nhResult');
  const { evals } = data;
  const COLORS = ['#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6','#ef4444'];
  let html = '';

  evals.forEach((ev, idx) => {
    const col   = COLORS[idx % COLORS.length];
    const { first, second, polyExpr, cVal } = ev;

    /* ── Card por polinomio ── */
    html += `<div class="card" style="margin-bottom:1.25rem;border-top:4px solid ${col};">
      <div class="card-header">
        <div class="card-header-icon green" style="background:${col}20;color:${col};">${idx === 0 ? 'P' : 'Q'}</div>
        <div>
          <div class="card-title">${idx === 0 ? 'Aplicación 1 — Evaluación de P(c)' : `Aplicación 2 — Evaluación de Q(c) = P′(c)`}</div>
          <div class="card-subtitle">${polyExpr}  ·  c = ${cVal}</div>
        </div>
        <div style="margin-left:auto;background:${col}15;border:1.5px solid ${col}33;
          border-radius:var(--radius-sm);padding:.5rem 1rem;text-align:center;">
          <div style="font-family:var(--font-main);font-size:.65rem;color:var(--gray-500);">
            ${idx === 0 ? 'P(c) =' : "P′(c) = Q(c) ="}
          </div>
          <div style="font-family:var(--font-mono);font-size:1.1rem;font-weight:700;color:${col};">
            ${Number(first.pc).toFixed(8)}
          </div>
        </div>
      </div>`;

    /* Coeficientes del polinomio */
    html += `<div style="padding:0 1.5rem .75rem;">
      <div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;
        letter-spacing:.4px;color:var(--gray-500);margin-bottom:.5rem;">Coeficientes aₖ</div>
      <div style="display:flex;flex-wrap:wrap;gap:.4rem;margin-bottom:1rem;">`;
    const n = first.steps.length - 1;
    first.steps.forEach(s => {
      html += `<div style="padding:.35rem .65rem;background:var(--gray-100);border-radius:5px;
        font-family:var(--font-mono);font-size:.8rem;border:1px solid var(--border);">
        a<sub>${s.k}</sub> = ${Number(s.ak).toFixed(s.ak % 1 === 0 ? 0 : 4)}
      </div>`;
    });
    html += `</div>`;

    /* Tabla Horner */
    html += `<div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;
      letter-spacing:.4px;color:var(--gray-500);margin-bottom:.4rem;">Tabla de Horner — P(c)</div>
      ${buildHornerTable(first.steps, cVal, col)}`;

    /* Pasos como en la pizarra */
    html += `<div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;text-transform:uppercase;
      letter-spacing:.4px;color:var(--gray-500);margin:.75rem 0 .4rem;">Desarrollo paso a paso</div>
      ${buildHornerSteps(first.steps, cVal, col)}`;

    /* Cociente Q(x) */
    if (first.quotient && first.quotient.length > 0) {
      const qStr = polyToString(first.quotient.map(v => CX.make(v)));
      html += `<div style="margin-top:.75rem;padding:.65rem 1rem;background:var(--gray-50);
        border-radius:5px;border:1px solid var(--border);border-left:3px solid ${col};">
        <span style="font-family:var(--font-main);font-size:.75rem;color:var(--gray-500);font-weight:600;">
          Cociente Q(x) = P(x)/(x − ${cVal})
        </span><br>
        <span style="font-family:var(--font-mono);font-size:.88rem;font-weight:600;color:${col};">
          Q(x) = ${qStr}
        </span>
        <span style="font-family:var(--font-main);font-size:.72rem;color:var(--gray-500);margin-left:.75rem;">
          con residuo P(c) = ${Number(first.pc).toFixed(6)}
        </span>
      </div>`;
    }

    html += `</div></div>`; /* cierre card */
  });

  /* ── Panel de conclusión ── */
  if (evals.length >= 2) {
    const ev0 = evals[0], ev1 = evals[1];
    const pc  = Number(ev0.first.pc);
    const dpc = Number(ev1.first.pc);
    html += `<div class="card" style="border-top:4px solid #10b981;margin-bottom:1.25rem;">
      <div class="card-header">
        <div class="card-header-icon green">✓</div>
        <div><div class="card-title">Conclusión</div>
        <div class="card-subtitle">Resultados de ambas aplicaciones de Horner</div></div>
      </div>
      <div style="display:grid;grid-template-columns:1fr 1fr;gap:1rem;padding:0 1.5rem 1.25rem;">
        <div style="padding:1rem;background:var(--success-light);border-radius:var(--radius-sm);border:1.5px solid #6ee7b7;text-align:center;">
          <div style="font-family:var(--font-main);font-size:.75rem;color:#065f46;font-weight:600;margin-bottom:.25rem;">P(c)</div>
          <div style="font-family:var(--font-mono);font-size:1.15rem;font-weight:700;color:#065f46;">${pc.toFixed(8)}</div>
        </div>
        <div style="padding:1rem;background:var(--primary-light);border-radius:var(--radius-sm);border:1.5px solid #a5b4fc;text-align:center;">
          <div style="font-family:var(--font-main);font-size:.75rem;color:var(--primary-dark);font-weight:600;margin-bottom:.25rem;">P′(c) = Q(c)</div>
          <div style="font-family:var(--font-mono);font-size:1.15rem;font-weight:700;color:var(--primary-dark);">${dpc.toFixed(8)}</div>
        </div>
      </div>
    </div>`;
  }

  container.innerHTML = html;
  if (typeof state !== 'undefined') state.nhLast = { data, expr, c };
  setTimeout(() => {
    /* Inicializar gráfica interactiva Horner */
    if (typeof nhGraphInit === 'function' && data?.evals?.length >= 2) {
      const first  = data.evals[0].first;
      const second = data.evals[1].first;
      const coeffs   = (typeof parsePolynomial === 'function') ? (() => { try { return parsePolynomial(expr).coeffs; } catch(e) { return []; } })() : [];
      const quotient = first?.quotient || [];
      nhGraphInit(coeffs, quotient, c, first?.pc, second?.pc, expr);
    }
    const b = document.getElementById('nh-download-bar');
    if (b) b.style.display = 'block';
    if (window.innerWidth <= 768) {
      const el = document.getElementById('nhResult');
      if (el) el.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }
  }, 80);
}

/* ── Evento botón Newton-Horner ──────────────────────────────── */
document.addEventListener('DOMContentLoaded', () => {
  const btn = document.getElementById('btnNewtonHorner');
  if (!btn) return;
  btn.addEventListener('click', () => {
    clearAlert('nhAlert');
    document.getElementById('nhResult').innerHTML = '';

    const expr = document.getElementById('nhFunc').value.trim();
    if (checkUpperX(expr, 'nhAlert')) return;
    const cVal = parseFloat(document.getElementById('nhX0').value);

    if (!expr)         { showAlert('nhAlert','danger','Ingrese el polinomio.'); return; }
    if (isNaN(cVal))   { showAlert('nhAlert','danger','El valor c debe ser numérico.'); return; }

    try {
      const parsed = parsePolynomial(expr);
      const coeffs = parsed.coeffs;

      /* 1ra aplicación: P(c) → cociente Q(x) */
      const first  = hornerEval(coeffs, cVal);
      const polyQStr = polyToString(first.quotient.map(v => CX.make(v)));

      /* 2da aplicación: Q(c) = P'(c) */
      const second = hornerEval(first.quotient, cVal);

      const data = {
        evals: [
          { first, polyExpr: expr,      cVal, label: 'P(x)' },
          { first: second, polyExpr: `Q(x) = ${polyQStr}`, cVal, label: 'Q(x)' }
        ]
      };

      renderNHResult(data, expr, cVal);
      showAlert('nhAlert', 'success',
        `✓ P(${cVal}) = ${first.pc.toFixed(6)}  ·  P′(${cVal}) = ${second.pc.toFixed(6)}  ·  Q(x) = ${polyQStr}`);
    } catch(e) { showAlert('nhAlert', 'danger', 'Error: ' + e.message); }
  });
});


/* ══════════════════════════════════════════════════════════════
   MÜLLER — BÚSQUEDA POR SCAN (para gráfica y funciones generales)
   Scan denso 500pts → cambios de signo → Müller → deduplicar
══════════════════════════════════════════════════════════════ */
function m3FindAllRoots(expr, xmin, xmax, tol) {
  const STEPS = 500;
  const dx    = (xmax - xmin) / STEPS;
  const seeds = [];

  let prevY = null, prevX = xmin;
  for (let i = 0; i <= STEPS; i++) {
    const x = xmin + i * dx;
    let y;
    try { y = evalF(expr, x); } catch(e) { prevY = null; continue; }
    if (!isFinite(y) || Math.abs(y) > 1e10) { prevY = null; continue; }

    if (prevY !== null && prevY * y < 0) {
      const a = prevX, b = x, mid = (a + b) / 2;
      seeds.push([a,              a+(b-a)*0.35, mid          ]);
      seeds.push([a+(b-a)*0.2,   mid,           b            ]);
      seeds.push([a+(b-a)*0.1,   a+(b-a)*0.5,   a+(b-a)*0.9 ]);
    }
    prevY = y; prevX = x;
  }

  for (let i = 1; i <= 24; i++) {
    const cx = xmin + (i / 24) * (xmax - xmin);
    seeds.push([cx - dx*3, cx, cx + dx*3]);
  }

  const found = [];
  seeds.forEach(([p0, p1, p2]) => {
    if (p0 === p1 || p1 === p2 || p0 === p2) return;
    try {
      const res = mullerMethod(expr, p0, p1, p2, tol);
      if (!res.converged) return;
      const r = res.root;
      if (!isFinite(r) || r < xmin - Math.abs(xmax-xmin)*0.6
                       || r > xmax + Math.abs(xmax-xmin)*0.6) return;
      if (found.some(f => Math.abs(f.root - r) < tol * 1000)) return;
      found.push(res);
    } catch(e) {}
  });

  found.sort((a, b) => a.root - b.root);
  return found;
}


/* ══════════════════════════════════════════════════════════════
   GRÁFICAS INTERACTIVAS — TEMA 3
   Motor compartido para Müller, Bairstow y Horner.
   Mismo estilo que T1 y T2: pan, zoom, tooltip, crosshair.
══════════════════════════════════════════════════════════════ */

/* ── Utilidades compartidas T3 ───────────────────────────────── */
function t3GFmt(v) {
  if (!isFinite(v)) return '—';
  const a = Math.abs(v);
  if (a === 0) return '0';
  if (a >= 1000 || a < 0.001) return v.toExponential(3);
  if (a < 0.1)  return v.toFixed(5);
  if (a < 10)   return v.toFixed(4);
  if (a < 100)  return v.toFixed(3);
  return v.toFixed(2);
}
function t3GNiceStep(range, tgt) {
  const rough = range/tgt, mag = Math.pow(10,Math.floor(Math.log10(rough)));
  const n = rough/mag; return (n<1.5?1:n<3.5?2:n<7.5?5:10)*mag;
}

/**
 * t3GMakeEngine(cfg)
 *   Crea un motor de gráfica interactiva reutilizable.
 *   cfg = { canvasId, tooltipId, coordsId, bgDark }
 */
function t3GMakeEngine(cfg) {
  const eng = {
    canvas: null, ctx: null,
    xMin: -6, xMax: 6, yMin: -5, yMax: 5,
    dragging: false, lastMouse: {x:0,y:0},
    mouseWorld: {x:0,y:0}, hoverOn: false,
    drawFn: null,   // función de dibujo específica del método
    bgDark: cfg.bgDark || false,
  };

  function init() {
    const c = document.getElementById(cfg.canvasId);
    if (!c) return;
    eng.canvas = c; eng.ctx = c.getContext('2d');
    resize();
    window.addEventListener('resize', resize);

    c.addEventListener('mousedown', e => { eng.dragging=true; eng.lastMouse={x:e.clientX,y:e.clientY}; c.style.cursor='grabbing'; });
    c.addEventListener('mouseup',   () => { eng.dragging=false; c.style.cursor='crosshair'; });
    c.addEventListener('mouseleave',() => {
      eng.dragging=false; eng.hoverOn=false; c.style.cursor='crosshair';
      const tip=document.getElementById(cfg.tooltipId); if(tip) tip.style.display='none';
      const coord=document.getElementById(cfg.coordsId); if(coord) coord.innerHTML='x = — &nbsp; y = —';
      if(eng.drawFn) eng.drawFn();
    });
    c.addEventListener('mousemove', e => {
      const rect=c.getBoundingClientRect();
      const px=(e.clientX-rect.left)*(c.width/rect.width);
      const py=(e.clientY-rect.top)*(c.height/rect.height);
      eng.mouseWorld=toWorld(px,py,eng); eng.hoverOn=true;
      const coord=document.getElementById(cfg.coordsId);
      if(coord) coord.innerHTML=`x = ${t3GFmt(eng.mouseWorld.x)} &nbsp; y = ${t3GFmt(eng.mouseWorld.y)}`;
      if(eng.dragging){
        const dx=(e.clientX-eng.lastMouse.x)/rect.width*(eng.xMax-eng.xMin);
        const dy=(e.clientY-eng.lastMouse.y)/rect.height*(eng.yMax-eng.yMin);
        eng.xMin-=dx; eng.xMax-=dx; eng.yMin+=dy; eng.yMax+=dy;
        eng.lastMouse={x:e.clientX,y:e.clientY};
      }
      if(eng.drawFn) eng.drawFn();
    });
    c.addEventListener('wheel', e => {
      e.preventDefault();
      const f=e.deltaY>0?1.12:0.89;
      const rect=c.getBoundingClientRect();
      const {x:wx,y:wy}=toWorld((e.clientX-rect.left)*(c.width/rect.width),(e.clientY-rect.top)*(c.height/rect.height),eng);
      eng.xMin=wx+(eng.xMin-wx)*f; eng.xMax=wx+(eng.xMax-wx)*f;
      eng.yMin=wy+(eng.yMin-wy)*f; eng.yMax=wy+(eng.yMax-wy)*f;
      if(eng.drawFn) eng.drawFn();
    },{passive:false});

    /* Touch */
    let lT=null,lPD=null;
    c.addEventListener('touchstart',e=>{e.preventDefault();if(e.touches.length===1){lT={x:e.touches[0].clientX,y:e.touches[0].clientY};lPD=null;}else if(e.touches.length===2){lPD=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);}},{passive:false});
    c.addEventListener('touchmove',e=>{e.preventDefault();const rect=c.getBoundingClientRect();if(e.touches.length===1&&lT){const dx=(e.touches[0].clientX-lT.x)/rect.width*(eng.xMax-eng.xMin);const dy=(e.touches[0].clientY-lT.y)/rect.height*(eng.yMax-eng.yMin);eng.xMin-=dx;eng.xMax-=dx;eng.yMin+=dy;eng.yMax+=dy;lT={x:e.touches[0].clientX,y:e.touches[0].clientY};}else if(e.touches.length===2&&lPD){const d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);const f=lPD/d;const cx=(eng.xMin+eng.xMax)/2,cy=(eng.yMin+eng.yMax)/2,hw=(eng.xMax-eng.xMin)/2*f,hh=(eng.yMax-eng.yMin)/2*f;eng.xMin=cx-hw;eng.xMax=cx+hw;eng.yMin=cy-hh;eng.yMax=cy+hh;lPD=d;}if(eng.drawFn)eng.drawFn();},{passive:false});
    c.addEventListener('touchend',()=>{lT=null;lPD=null;});
  }

  function resize() {
    const c=eng.canvas; if(!c) return;
    const w=c.parentElement.clientWidth||800;
    c.width=w; c.height=Math.max(340,Math.round(w*0.50));
    if(eng.drawFn) eng.drawFn();
  }

  function toWorld(px,py,e){ return {x:e.xMin+(px/e.canvas.width)*(e.xMax-e.xMin), y:e.yMin+(1-py/e.canvas.height)*(e.yMax-e.yMin)}; }
  function toCanvas(wx,wy,e){ return {x:(wx-e.xMin)/(e.xMax-e.xMin)*e.canvas.width, y:e.canvas.height-(wy-e.yMin)/(e.yMax-e.yMin)*e.canvas.height}; }

  function zoom(factor) {
    const cx=(eng.xMin+eng.xMax)/2,cy=(eng.yMin+eng.yMax)/2;
    const hw=(eng.xMax-eng.xMin)/2*factor,hh=(eng.yMax-eng.yMin)/2*factor;
    eng.xMin=cx-hw;eng.xMax=cx+hw;eng.yMin=cy-hh;eng.yMax=cy+hh;
    if(eng.drawFn) eng.drawFn();
  }

  /* Base de dibujo: fondo, grid, ejes, etiquetas */
  function drawBase() {
    /* bgDark se resuelve dinámicamente para responder al toggle de dark mode */
    const bgDark = document.body.classList.contains('dark-mode') ? true : (cfg.bgDark || false);
    eng.bgDark = bgDark;
    const {canvas:c,ctx,xMin,xMax,yMin,yMax}=eng;
    const W=c.width,H=c.height;
    ctx.clearRect(0,0,W,H);
    ctx.fillStyle=bgDark?'#0f172a':'#ffffff'; ctx.fillRect(0,0,W,H);
    const toC=(wx,wy)=>toCanvas(wx,wy,eng);
    const xSt=t3GNiceStep(xMax-xMin,12), ySt=t3GNiceStep(yMax-yMin,8);
    ctx.strokeStyle=bgDark?'rgba(148,163,184,0.08)':'#f1f5f9'; ctx.lineWidth=1;
    for(let gx=Math.ceil(xMin/xSt)*xSt;gx<=xMax+xSt;gx+=xSt){const{x:px}=toC(gx,0);ctx.beginPath();ctx.moveTo(px,0);ctx.lineTo(px,H);ctx.stroke();}
    for(let gy=Math.ceil(yMin/ySt)*ySt;gy<=yMax+ySt;gy+=ySt){const{y:py}=toC(0,gy);ctx.beginPath();ctx.moveTo(0,py);ctx.lineTo(W,py);ctx.stroke();}
    ctx.strokeStyle=bgDark?'rgba(148,163,184,0.3)':'#cbd5e1'; ctx.lineWidth=1.5;
    const{y:axY}=toC(0,0),{x:axX}=toC(0,0);
    if(yMin<=0&&yMax>=0){ctx.beginPath();ctx.moveTo(0,axY);ctx.lineTo(W,axY);ctx.stroke();}
    if(xMin<=0&&xMax>=0){ctx.beginPath();ctx.moveTo(axX,0);ctx.lineTo(axX,H);ctx.stroke();}
    const lbY=Math.max(14,Math.min(H-8,axY+16)),lbX=Math.max(36,Math.min(W-40,axX-8));
    ctx.fillStyle=bgDark?'rgba(148,163,184,0.6)':'#94a3b8'; ctx.font='11px "JetBrains Mono",monospace'; ctx.textBaseline='middle';
    for(let gx=Math.ceil(xMin/xSt)*xSt;gx<=xMax;gx+=xSt){if(Math.abs(gx)<xSt*0.01)continue;const{x:px}=toC(gx,0);ctx.strokeStyle=bgDark?'rgba(148,163,184,0.3)':'#cbd5e1';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(px,axY-4);ctx.lineTo(px,axY+4);ctx.stroke();ctx.textAlign='center';ctx.fillText(t3GFmt(gx),px,lbY);}
    for(let gy=Math.ceil(yMin/ySt)*ySt;gy<=yMax;gy+=ySt){if(Math.abs(gy)<ySt*0.01)continue;const{y:py}=toC(0,gy);ctx.strokeStyle=bgDark?'rgba(148,163,184,0.3)':'#cbd5e1';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(axX-4,py);ctx.lineTo(axX+4,py);ctx.stroke();ctx.textAlign='right';ctx.fillText(t3GFmt(gy),lbX,py);}
    ctx.textAlign='right'; ctx.fillText('0',lbX,lbY); ctx.textBaseline='alphabetic';
    return {toC,W,H,axY,axX};
  }

  /* Crosshair hover */
  function drawCrosshair(toC,W,H) {
    if(!eng.hoverOn) return;
    const{x:mx,y:my}=toC(eng.mouseWorld.x,eng.mouseWorld.y);
    eng.ctx.save(); eng.ctx.strokeStyle='rgba(100,116,139,0.35)'; eng.ctx.lineWidth=1; eng.ctx.setLineDash([3,3]);
    eng.ctx.beginPath();eng.ctx.moveTo(mx,0);eng.ctx.lineTo(mx,H);eng.ctx.stroke();
    eng.ctx.beginPath();eng.ctx.moveTo(0,my);eng.ctx.lineTo(W,my);eng.ctx.stroke();
    eng.ctx.restore();
  }

  /* Watermark */
  function drawWatermark(W,H,dark) {
    const ctx=eng.ctx; ctx.save();
    ctx.font='600 11px "Poppins",sans-serif';
    ctx.fillStyle=dark?'rgba(99,102,241,0.18)':'rgba(148,163,184,0.45)';
    ctx.textAlign='right'; ctx.textBaseline='bottom';
    ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.restore();
  }

  /* Curva f(x) */
  function drawCurve(expr,color,toC,W,H,xMin,xMax,yMin,yMax,ctx,dash) {
    const steps=W*2,dx=(xMax-xMin)/steps;
    if(dash) ctx.setLineDash(dash);
    ctx.beginPath(); ctx.strokeStyle=color; ctx.lineWidth=2.5; ctx.lineJoin='round'; ctx.lineCap='round';
    let dr=false;
    for(let i=0;i<=steps;i++){
      const wx=xMin+i*dx; let wy; try{wy=evalF(expr,wx);}catch{wy=NaN;}
      if(!isFinite(wy)||Math.abs(wy)>(yMax-yMin)*50){if(dr)ctx.stroke();ctx.beginPath();dr=false;continue;}
      const{x:px,y:py}=toC(wx,wy);
      if(!dr){ctx.moveTo(px,py);dr=true;}else ctx.lineTo(px,py);
    }
    if(dr)ctx.stroke();
    if(dash) ctx.setLineDash([]);
  }

  /* Tooltip con fondo */
  function drawRootLabel(ctx,col,label,px,py,W,bgDark) {
    ctx.font='700 11px "Poppins",sans-serif';
    const tw=ctx.measureText(label).width,pw=tw+12,ph=22,pr=5;
    let bx=px-pw/2, by=py-14-ph;
    if(by<4)by=py+14; if(bx<4)bx=4; if(bx+pw>W-4)bx=W-pw-4;
    ctx.save(); ctx.shadowColor='rgba(0,0,0,.12)'; ctx.shadowBlur=6; ctx.shadowOffsetY=2;
    ctx.fillStyle=bgDark?'#1e293b':'#fff';
    ctx.beginPath(); ctx.roundRect(bx,by,pw,ph,pr); ctx.fill(); ctx.restore();
    ctx.strokeStyle=col; ctx.lineWidth=1.5; ctx.beginPath(); ctx.roundRect(bx,by,pw,ph,pr); ctx.stroke();
    ctx.fillStyle=col; ctx.textAlign='left'; ctx.textBaseline='middle';
    ctx.fillText(label,bx+6,by+ph/2); ctx.textBaseline='alphabetic';
  }

  return { eng, init, resize, zoom, drawBase, drawCurve, drawCrosshair, drawWatermark, drawRootLabel, toCanvas: (wx,wy)=>toCanvas(wx,wy,eng) };
}

/* ══════════════════════════════════════════════════════════════
   MÜLLER — Motor interactivo renovado
   Conserva: animación por iteración, parábola, nodos x0/x1/x2
   Añade: pan, zoom, tooltip mejorado
══════════════════════════════════════════════════════════════ */
const m3Eng = t3GMakeEngine({ canvasId:'m3Canvas', tooltipId:'m3Tooltip', coordsId:'m3GraphCoords', bgDark:true });

const m3Graph = {
  rows: [], expr: '', root: NaN, allRoots: [],
  animTimer: null,
  get canvas(){ return m3Eng.eng.canvas; },
  get ctx()   { return m3Eng.eng.ctx;    },
  get xmin()  { return m3Eng.eng.xMin;   },
  get xmax()  { return m3Eng.eng.xMax;   },
  get ymin()  { return m3Eng.eng.yMin;   },
  get ymax()  { return m3Eng.eng.yMax;   },
};

function m3NiceStep(range,ticks){ return t3GNiceStep(range,ticks); }
function m3CalcYRange(expr,xmin,xmax){
  let ymin=Infinity,ymax=-Infinity;
  for(let i=0;i<=300;i++){const x=xmin+i/300*(xmax-xmin);try{const y=evalF(expr,x);if(isFinite(y)&&Math.abs(y)<1e6){if(y<ymin)ymin=y;if(y>ymax)ymax=y;}}catch(e){}}
  if(!isFinite(ymin)){ymin=-10;ymax=10;}
  const pad=Math.max(1,(ymax-ymin)*0.2);
  return{ymin:ymin-pad,ymax:ymax+pad};
}
function m3EvalParabola(row,x){const dx=x-row.xc;return row.fc+row.b*dx+row.a*dx*dx;}
function m3WorldToPx(wx,wy){const e=m3Eng.eng;return{px:(wx-e.xMin)/(e.xMax-e.xMin)*e.canvas.width,py:e.canvas.height-(wy-e.yMin)/(e.yMax-e.yMin)*e.canvas.height};}
function m3PxToWorld(px){const e=m3Eng.eng;return e.xMin+(px/e.canvas.width)*(e.xMax-e.xMin);}

function m3Draw(iterIdx) {
  const {eng,drawBase,drawCurve,drawCrosshair,drawWatermark,drawRootLabel,toCanvas}=m3Eng;
  if(!eng.canvas||!eng.ctx) return;
  const {rows,expr,root,allRoots}=m3Graph;
  if(!rows||rows.length===0) return;

  const {toC,W,H,axY}=drawBase();
  const ctx=eng.ctx;
  const {xMin:xmin,xMax:xmax,yMin:ymin,yMax:ymax}=eng;

  /* Curva f(x) - índigo brillante */
  drawCurve(expr,'#818cf8',toC,W,H,xmin,xmax,ymin,ymax,ctx,null);

  /* Parábola de la iteración activa */
  const row=rows[iterIdx];
  if(row&&isFinite(row.a)&&isFinite(row.b)&&isFinite(row.c)){
    const steps=W*2,dx=(xmax-xmin)/steps;
    ctx.beginPath(); ctx.strokeStyle='#fbbf24'; ctx.lineWidth=2; ctx.setLineDash([6,4]);
    let pd=false;
    for(let i=0;i<=steps;i++){const wx=xmin+i*dx;const wy=m3EvalParabola(row,wx);if(!isFinite(wy)||Math.abs(wy)>(ymax-ymin)*10){if(pd)ctx.stroke();ctx.beginPath();pd=false;continue;}const{x:px,y:py}=toC(wx,wy);if(!pd){ctx.moveTo(px,py);pd=true;}else ctx.lineTo(px,py);}
    ctx.stroke(); ctx.setLineDash([]);
  }

  /* Nodos históricos (tenues) */
  const NC=['#6366f1','#8b5cf6','#a855f7'];
  rows.slice(0,iterIdx).forEach((r,i)=>{
    const alpha=0.2+(i/Math.max(rows.length,1))*0.3;
    [r.xa,r.xb,r.xc].forEach((xx,ni)=>{
      let yy;try{yy=evalF(expr,xx);}catch{return;}if(!isFinite(yy))return;
      const{x:px,y:py}=toC(xx,yy);
      ctx.beginPath();ctx.arc(px,py,3,0,Math.PI*2);
      ctx.fillStyle=NC[ni]+(Math.round(alpha*255).toString(16).padStart(2,'0'));ctx.fill();
    });
  });

  /* Nodos activos x0,x1,x2 */
  if(row){
    [{x:row.xa,y:row.fa,col:'#6366f1',lbl:'x₀'},{x:row.xb,y:row.fb,col:'#8b5cf6',lbl:'x₁'},{x:row.xc,y:row.fc,col:'#a855f7',lbl:'x₂'}].forEach(nd=>{
      if(!isFinite(nd.x)||!isFinite(nd.y))return;
      const{x:px,y:py}=toC(nd.x,nd.y);
      ctx.save();ctx.setLineDash([3,3]);ctx.strokeStyle=nd.col+'80';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px,axY);ctx.stroke();ctx.restore();
      ctx.beginPath();ctx.arc(px,py,9,0,Math.PI*2);ctx.fillStyle=nd.col+'33';ctx.fill();
      ctx.beginPath();ctx.arc(px,py,5,0,Math.PI*2);ctx.fillStyle=nd.col;ctx.strokeStyle='rgba(255,255,255,.8)';ctx.lineWidth=1.5;ctx.fill();ctx.stroke();
      ctx.font='bold 10px Poppins,sans-serif';ctx.fillStyle=nd.col;ctx.textAlign='center';ctx.textBaseline='bottom';ctx.fillText(nd.lbl,px,py-10);
      ctx.font='9px "JetBrains Mono",monospace';ctx.fillStyle='rgba(226,232,240,0.6)';ctx.textBaseline='alphabetic';ctx.fillText(nd.x.toFixed(4),px,py+20);
    });
  }

  /* x_nuevo */
  if(row&&isFinite(row.xNew)){
    let yn=0;try{yn=evalF(expr,row.xNew);}catch{}
    if(isFinite(yn)){
      const{x:px,y:py}=toC(row.xNew,yn);
      ctx.beginPath();ctx.arc(px,py,13,0,Math.PI*2);ctx.strokeStyle='#34d39960';ctx.lineWidth=2;ctx.stroke();
      ctx.beginPath();ctx.arc(px,py,6,0,Math.PI*2);ctx.fillStyle='#10b981';ctx.strokeStyle='rgba(255,255,255,.9)';ctx.lineWidth=2;ctx.fill();ctx.stroke();
      ctx.font='bold 10px Poppins,sans-serif';ctx.fillStyle='#34d399';ctx.textAlign='center';ctx.textBaseline='bottom';ctx.fillText('xₙₑᵥ',px,py-14);
      ctx.font='9px "JetBrains Mono",monospace';ctx.fillStyle='rgba(52,211,153,.85)';ctx.textBaseline='alphabetic';ctx.fillText(row.xNew.toFixed(6),px,py+22);
    }
  }

  /* Todas las raíces sobre el eje X */
  const RC=['#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6','#ef4444'];
  if(allRoots&&allRoots.length>0){
    allRoots.forEach((rv,ri)=>{
      const r=rv.root; if(!isFinite(r)||r<xmin||r>xmax)return;
      const col=RC[ri%RC.length];
      const{x:px,y:py0}=toC(r,0);
      let yr=0;try{yr=evalF(expr,r);}catch{}
      const{y:pyCurve}=isFinite(yr)?toC(r,yr):{y:py0};
      ctx.save();ctx.setLineDash([4,4]);ctx.strokeStyle=col;ctx.lineWidth=1.5;ctx.globalAlpha=0.5;ctx.beginPath();ctx.moveTo(px,py0);ctx.lineTo(px,pyCurve);ctx.stroke();ctx.restore();
      ctx.save();ctx.globalAlpha=0.18;ctx.beginPath();ctx.arc(px,py0,13,0,Math.PI*2);ctx.fillStyle=col;ctx.fill();ctx.restore();
      ctx.beginPath();ctx.arc(px,py0,6,0,Math.PI*2);ctx.fillStyle=col;ctx.strokeStyle='rgba(255,255,255,.9)';ctx.lineWidth=2;ctx.fill();ctx.stroke();
      drawRootLabel(ctx,col,`r${ri+1} = ${r.toFixed(6)}`,px,py0-6,W,true);
    });
  } else if(isFinite(root)){
    const{x:px,y:py0}=toC(root,0);
    if(px>=0&&px<=W){
      ctx.save();ctx.globalAlpha=0.18;ctx.beginPath();ctx.arc(px,py0,13,0,Math.PI*2);ctx.fillStyle='#10b981';ctx.fill();ctx.restore();
      ctx.beginPath();ctx.arc(px,py0,7,0,Math.PI*2);ctx.fillStyle='#10b981';ctx.strokeStyle='rgba(255,255,255,.9)';ctx.lineWidth=2;ctx.fill();ctx.stroke();
      drawRootLabel(ctx,'#10b981',`Raíz = ${root.toFixed(6)}`,px,py0-6,W,true);
    }
  }

  /* Tooltip hover con f(x) */
  if(eng.hoverOn&&expr){
    const tip=document.getElementById('m3Tooltip');
    if(tip){
      const wx=eng.mouseWorld.x;
      let fy=NaN;try{fy=evalF(expr,wx);}catch{}
      if(isFinite(fy)){
        tip.textContent=`x = ${t3GFmt(wx)}   f(x) = ${t3GFmt(fy)}`;
        const {x:px,y:py}=toC(wx,fy);
        const rect=eng.canvas.getBoundingClientRect();
        const scale=rect.width/eng.canvas.width;
        tip.style.display='block';
        tip.style.left=(px*scale+14)+'px';
        tip.style.top=(Math.max(0,py*scale-38))+'px';
        /* Punto en la curva */
        ctx.beginPath();ctx.arc(px,py,4,0,Math.PI*2);ctx.fillStyle='#818cf8';ctx.globalAlpha=0.7;ctx.fill();ctx.globalAlpha=1;
      } else { tip.style.display='none'; }
    }
  }

  drawCrosshair(toC,W,H);
  drawWatermark(W,H,true);
  m3UpdateGraphInfo(row,iterIdx+1);
}

function m3UpdateGraphInfo(row,iter){
  const el=document.getElementById('m3GraphInfo');
  if(!el||!row)return;
  const ea=isFinite(row.ea)?row.ea.toExponential(4):'—';
  el.innerHTML=`<strong style="color:#10b981;">Iteración ${iter}</strong> &nbsp;|&nbsp; x<sub>a</sub>=${m3Fmt(row.xa)} &nbsp; x<sub>b</sub>=${m3Fmt(row.xb)} &nbsp; x<sub>c</sub>=${m3Fmt(row.xc)} &nbsp;→&nbsp; <strong>xₙ = ${m3Fmt(row.xNew,8)}</strong> &nbsp;|&nbsp; E<sub>a</sub> = <strong style="color:${row.converged?'#10b981':'#ef4444'};">${ea}</strong>${row.converged?' <span style="color:#10b981;font-weight:700;">✓</span>':''}`;
}

function m3InitCanvas(){
  m3Eng.init();
  m3Eng.eng.bgDark=true;
  m3Eng.eng.drawFn=()=>{
    const sl=document.getElementById('m3IterSlider');
    m3Draw(sl?Math.max(0,parseInt(sl.value)-1):0);
  };
  /* Slider */
  const sl=document.getElementById('m3IterSlider');
  if(sl) sl.addEventListener('input',()=>{
    const idx=Math.max(0,parseInt(sl.value)-1);
    document.getElementById('m3IterLabel').textContent=sl.value;
    m3Draw(idx);
  });
}

function m3GZoom(f){ m3Eng.zoom(f); }
function m3GReset(){
  if(!m3Graph.expr)return;
  const {ymin,ymax}=m3CalcYRange(m3Graph.expr,-6,6);
  const e=m3Eng.eng;e.xMin=-6;e.xMax=6;e.yMin=ymin;e.yMax=ymax;
  if(e.drawFn)e.drawFn();
}
window.m3GZoom=m3GZoom;

function m3InitGraph(rows,expr,root,allRoots){
  const {ymin,ymax}=m3CalcYRange(expr,-6,6);
  const e=m3Eng.eng;
  /* Centrar vista para incluir todas las raíces */
  let xSpan=6;
  if(allRoots&&allRoots.length>0){
    const xs=allRoots.map(r=>r.root).filter(r=>isFinite(r));
    if(xs.length>0){const lo=Math.min(...xs),hi=Math.max(...xs);xSpan=Math.max(xSpan,Math.abs(hi-lo)*1.5+2);}
  }
  e.xMin=-xSpan;e.xMax=xSpan;e.yMin=ymin;e.yMax=ymax;
  Object.assign(m3Graph,{rows,expr,root,allRoots:allRoots||[]});
  const card=document.getElementById('m3GraphCard');
  if(card)card.style.display='block';
  const sl=document.getElementById('m3IterSlider');
  if(sl){sl.max=rows.length;sl.value=rows.length;document.getElementById('m3IterLabel').textContent=rows.length;}
  if(!e.canvas)m3InitCanvas();
  m3Draw(rows.length-1);
}

function m3Animate(){
  const sl=document.getElementById('m3IterSlider');
  const btn=document.getElementById('btnM3Play');
  if(!sl)return;
  if(m3Graph.animTimer){clearInterval(m3Graph.animTimer);m3Graph.animTimer=null;if(btn)btn.textContent='▶ Animar';return;}
  if(parseInt(sl.value)>=parseInt(sl.max)){sl.value=1;}
  if(btn)btn.textContent='⏹ Detener';
  m3Graph.animTimer=setInterval(()=>{
    const cur=parseInt(sl.value),max=parseInt(sl.max);
    if(cur>=max){clearInterval(m3Graph.animTimer);m3Graph.animTimer=null;if(btn)btn.textContent='▶ Animar';return;}
    sl.value=cur+1;
    document.getElementById('m3IterLabel').textContent=sl.value;
    m3Draw(cur);
  },600);
}

/* ══════════════════════════════════════════════════════════════
   BAIRSTOW — Gráfica interactiva
   Muestra P(x) original + raíces reales y complejas (parte real)
══════════════════════════════════════════════════════════════ */
const bsEng = t3GMakeEngine({ canvasId:'bsCanvas', tooltipId:'bsTooltip', coordsId:'bsGraphCoords', bgDark:false });

const bsGState = { coeffs:[], expr:'', roots:[], sessions:[] };

function bsGPolyEval(coeffs,x){ let v=0;for(const a of coeffs)v=v*x+a;return v; }

function bsGraphDraw(){
  const {eng,drawBase,drawCurve,drawCrosshair,drawWatermark,drawRootLabel,toCanvas}=bsEng;
  if(!eng.canvas)return;
  const {coeffs,expr,roots}=bsGState;
  const {toC,W,H,axY}=drawBase();
  const ctx=eng.ctx;
  const {xMin,xMax,yMin,yMax}=eng;

  if(!coeffs.length&&!expr){
    ctx.fillStyle='#94a3b8';ctx.font='13px "Poppins",sans-serif';ctx.textAlign='center';ctx.textBaseline='middle';
    ctx.fillText('Ejecuta Bairstow para ver la gráfica',W/2,H/2);ctx.textBaseline='alphabetic';
    drawWatermark(W,H,false); return;
  }

  /* Curva P(x) */
  if(coeffs.length>0){
    const steps=W*2,dx=(xMax-xMin)/steps;
    ctx.beginPath();ctx.strokeStyle='#4f46e5';ctx.lineWidth=2.5;ctx.lineJoin='round';
    let dr=false;
    for(let i=0;i<=steps;i++){
      const wx=xMin+i*dx;let wy;try{wy=bsGPolyEval(coeffs,wx);}catch{wy=NaN;}
      if(!isFinite(wy)||Math.abs(wy)>(yMax-yMin)*50){if(dr)ctx.stroke();ctx.beginPath();dr=false;continue;}
      const{x:px,y:py}=toC(wx,wy);if(!dr){ctx.moveTo(px,py);dr=true;}else ctx.lineTo(px,py);
    }
    if(dr)ctx.stroke();
  } else if(expr){
    drawCurve(expr,'#4f46e5',toC,W,H,xMin,xMax,yMin,yMax,ctx,null);
  }

  /* Raíces */
  const RC=['#ef4444','#10b981','#6366f1','#f59e0b','#ec4899','#14b8a6','#8b5cf6'];
  roots.forEach((r,i)=>{
    const rx=r.re; if(!isFinite(rx)||rx<xMin||rx>xMax)return;
    const col=RC[i%RC.length];
    const isComplex=Math.abs(r.im)>1e-5;
    const{x:px,y:py0}=toC(rx,0);
    ctx.save();ctx.setLineDash([4,4]);ctx.strokeStyle=col;ctx.lineWidth=1.5;ctx.globalAlpha=0.45;
    let pyCurve=py0;
    if(!isComplex&&coeffs.length>0){let yr=bsGPolyEval(coeffs,rx);if(isFinite(yr)){const{y}=toC(rx,yr);pyCurve=y;}}
    ctx.beginPath();ctx.moveTo(px,py0);ctx.lineTo(px,pyCurve);ctx.stroke();ctx.restore();
    ctx.save();ctx.globalAlpha=0.15;ctx.beginPath();ctx.arc(px,py0,13,0,Math.PI*2);ctx.fillStyle=col;ctx.fill();ctx.restore();
    ctx.beginPath();ctx.arc(px,py0,6,0,Math.PI*2);ctx.fillStyle=col;ctx.strokeStyle='#fff';ctx.lineWidth=2.5;ctx.fill();ctx.stroke();
    const lbl=isComplex?`r${i+1}= ${r.re.toFixed(4)}±${Math.abs(r.im).toFixed(4)}i`:`r${i+1}= ${rx.toFixed(6)}`;
    drawRootLabel(ctx,col,lbl,px,py0-6,W,false);
  });

  /* Tooltip hover */
  if(eng.hoverOn&&coeffs.length>0){
    const tip=document.getElementById('bsTooltip');
    if(tip){const wx=eng.mouseWorld.x;let fy=NaN;try{fy=bsGPolyEval(coeffs,wx);}catch{}
      if(isFinite(fy)){tip.innerHTML=`x = ${t3GFmt(wx)}<br>P(x) = ${t3GFmt(fy)}`;
        const{x:px,y:py}=toC(wx,fy);const rect=eng.canvas.getBoundingClientRect();const scale=rect.width/eng.canvas.width;
        tip.style.display='block';tip.style.left=(px*scale+14)+'px';tip.style.top=(Math.max(0,py*scale-55))+'px';
        ctx.beginPath();ctx.arc(px,py,4,0,Math.PI*2);ctx.fillStyle='#4f46e5';ctx.globalAlpha=0.6;ctx.fill();ctx.globalAlpha=1;
      }else tip.style.display='none';
    }
  }

  drawCrosshair(toC,W,H);
  drawWatermark(W,H,false);
}

function bsGraphInit(coeffs,roots,sessions,expr){
  bsGState.coeffs=coeffs||[];bsGState.roots=roots||[];bsGState.sessions=sessions||[];bsGState.expr=expr||'';
  /* Calcular vista */
  const e=bsEng.eng;
  let xspan=6;
  const realRoots=roots.filter(r=>Math.abs(r.im)<1e-5&&isFinite(r.re));
  if(realRoots.length>0){const lo=Math.min(...realRoots.map(r=>r.re)),hi=Math.max(...realRoots.map(r=>r.re));xspan=Math.max(6,Math.abs(hi-lo)*1.5+3);}
  e.xMin=-xspan;e.xMax=xspan;
  /* y range */
  if(coeffs.length>0){let ymi=Infinity,yma=-Infinity;for(let i=0;i<=200;i++){const x=e.xMin+i/200*(e.xMax-e.xMin);const y=bsGPolyEval(coeffs,x);if(isFinite(y)&&Math.abs(y)<1e6){if(y<ymi)ymi=y;if(y>yma)yma=y;}}if(isFinite(ymi)){const pad=Math.max(1,(yma-ymi)*0.2);e.yMin=ymi-pad;e.yMax=yma+pad;}else{e.yMin=-6;e.yMax=6;}}else{e.yMin=-6;e.yMax=6;}
  if(!e.canvas){bsEng.init();bsEng.eng.drawFn=bsGraphDraw;}
  const card=document.getElementById('bsGraphCard');if(card)card.style.display='block';
  bsGraphDraw();
}
function bsGZoom(f){bsEng.zoom(f);}
function bsGReset(){bsEng.eng.xMin=-6;bsEng.eng.xMax=6;bsGraphDraw();}
window.bsGZoom=bsGZoom;window.bsGReset=bsGReset;

/* ══════════════════════════════════════════════════════════════
   HORNER — Gráfica interactiva
   Muestra P(x) + Q(x) + punto c marcado con f(c) y Q(c)=P'(c)
══════════════════════════════════════════════════════════════ */
const nhEng = t3GMakeEngine({ canvasId:'nhCanvas', tooltipId:'nhTooltip', coordsId:'nhGraphCoords', bgDark:false });

const nhGState = { coeffs:[], quotient:[], c:0, pc:NaN, dpc:NaN, expr:'' };

function nhGPolyEval(coeffs,x){let v=0;for(const a of coeffs)v=v*x+a;return v;}

function nhGraphDraw(){
  const {eng,drawBase,drawCurve,drawCrosshair,drawWatermark,drawRootLabel,toCanvas}=nhEng;
  if(!eng.canvas)return;
  const {coeffs,quotient,c,pc,dpc,expr}=nhGState;
  const {toC,W,H,axY}=drawBase();
  const ctx=eng.ctx;
  const {xMin,xMax,yMin,yMax}=eng;

  if(!coeffs.length){
    ctx.fillStyle='#94a3b8';ctx.font='13px "Poppins",sans-serif';ctx.textAlign='center';ctx.textBaseline='middle';
    ctx.fillText('Ejecuta el Método de Horner para ver la gráfica',W/2,H/2);ctx.textBaseline='alphabetic';
    drawWatermark(W,H,false);return;
  }

  /* P(x) - azul sólido */
  const steps=W*2,dx=(xMax-xMin)/steps;
  const drawPoly=(c_,color,dash)=>{
    if(dash)ctx.setLineDash(dash);
    ctx.beginPath();ctx.strokeStyle=color;ctx.lineWidth=2.5;ctx.lineJoin='round';
    let dr=false;
    for(let i=0;i<=steps;i++){
      const wx=xMin+i*dx;let wy;try{wy=nhGPolyEval(c_,wx);}catch{wy=NaN;}
      if(!isFinite(wy)||Math.abs(wy)>(yMax-yMin)*80){if(dr)ctx.stroke();ctx.beginPath();dr=false;continue;}
      const{x:px,y:py}=toC(wx,wy);if(!dr){ctx.moveTo(px,py);dr=true;}else ctx.lineTo(px,py);
    }
    if(dr)ctx.stroke();if(dash)ctx.setLineDash([]);
  };
  drawPoly(coeffs,'#4f46e5',null);
  if(quotient.length>0) drawPoly(quotient,'#10b981',[7,5]);

  /* Punto c sobre P(x) */
  if(isFinite(c)&&c>=xMin&&c<=xMax){
    const pcVal=nhGPolyEval(coeffs,c);
    const{x:px,y:py}=toC(c,isFinite(pcVal)?pcVal:0);
    const{y:py0}=toC(c,0);
    ctx.save();ctx.setLineDash([4,4]);ctx.strokeStyle='#ef4444';ctx.lineWidth=1.5;ctx.globalAlpha=0.5;
    ctx.beginPath();ctx.moveTo(px,py0);ctx.lineTo(px,py);ctx.stroke();ctx.restore();
    ctx.save();ctx.globalAlpha=0.15;ctx.beginPath();ctx.arc(px,py,13,0,Math.PI*2);ctx.fillStyle='#ef4444';ctx.fill();ctx.restore();
    ctx.beginPath();ctx.arc(px,py,6,0,Math.PI*2);ctx.fillStyle='#ef4444';ctx.strokeStyle='#fff';ctx.lineWidth=2.5;ctx.fill();ctx.stroke();
    const lbl=`c=${t3GFmt(c)}  P(c)=${t3GFmt(isFinite(pc)?pc:pcVal)}`;
    drawRootLabel(ctx,'#ef4444',lbl,px,py-6,W,false);

    /* Punto c sobre Q(x) */
    if(quotient.length>0){
      const qcVal=nhGPolyEval(quotient,c);
      const{y:pyQ}=toC(c,isFinite(qcVal)?qcVal:0);
      ctx.beginPath();ctx.arc(px,pyQ,5,0,Math.PI*2);ctx.fillStyle='#10b981';ctx.strokeStyle='#fff';ctx.lineWidth=2;ctx.fill();ctx.stroke();
      drawRootLabel(ctx,'#10b981',`P'(c)=${t3GFmt(isFinite(dpc)?dpc:qcVal)}`,px+16,pyQ-6,W,false);
    }
  }

  /* Leyenda */
  const leg=[{col:'#4f46e5',lbl:'P(x)'},{col:'#10b981',lbl:'Q(x) = P(x)/(x−c)'}];
  ctx.font='600 10px "Poppins",sans-serif';
  leg.forEach(({col,lbl},i)=>{
    const lx=10,ly=12+i*18;
    ctx.fillStyle=col;ctx.fillRect(lx,ly,16,3);
    ctx.fillStyle='#374151';ctx.textAlign='left';ctx.textBaseline='middle';ctx.fillText(lbl,lx+20,ly+1.5);
  });
  ctx.textBaseline='alphabetic';

  /* Tooltip hover */
  if(eng.hoverOn&&coeffs.length>0){
    const tip=document.getElementById('nhTooltip');
    if(tip){const wx=eng.mouseWorld.x;
      const pv=nhGPolyEval(coeffs,wx),qv=quotient.length>0?nhGPolyEval(quotient,wx):NaN;
      if(isFinite(pv)){
        tip.innerHTML=`x = ${t3GFmt(wx)}<br>P(x) = ${t3GFmt(pv)}`+(isFinite(qv)?`<br>Q(x) = ${t3GFmt(qv)}`:'');
        const{x:px,y:py}=toC(wx,pv);const rect=eng.canvas.getBoundingClientRect();const scale=rect.width/eng.canvas.width;
        tip.style.display='block';tip.style.left=(px*scale+14)+'px';tip.style.top=(Math.max(0,py*scale-65))+'px';
        ctx.beginPath();ctx.arc(px,py,4,0,Math.PI*2);ctx.fillStyle='#4f46e5';ctx.globalAlpha=0.6;ctx.fill();ctx.globalAlpha=1;
      }else tip.style.display='none';
    }
  }

  drawCrosshair(toC,W,H);
  drawWatermark(W,H,false);
}

function nhGraphInit(coeffs,quotient,c,pc,dpc,expr){
  nhGState.coeffs=coeffs||[];nhGState.quotient=quotient||[];nhGState.c=c;nhGState.pc=pc;nhGState.dpc=dpc;nhGState.expr=expr||'';
  const e=nhEng.eng;
  /* Vista centrada en c */
  const span=Math.max(4,Math.abs(c)*2+3);
  e.xMin=c-span;e.xMax=c+span;
  if(coeffs.length>0){let ymi=Infinity,yma=-Infinity;for(let i=0;i<=200;i++){const x=e.xMin+i/200*(e.xMax-e.xMin);const y=nhGPolyEval(coeffs,x);if(isFinite(y)&&Math.abs(y)<1e6){if(y<ymi)ymi=y;if(y>yma)yma=y;}}if(isFinite(ymi)){const pad=Math.max(1,(yma-ymi)*0.2);e.yMin=ymi-pad;e.yMax=yma+pad;}else{e.yMin=-6;e.yMax=6;}}else{e.yMin=-6;e.yMax=6;}
  if(!e.canvas){nhEng.init();nhEng.eng.drawFn=nhGraphDraw;}
  const card=document.getElementById('nhGraphCard');if(card)card.style.display='block';
  nhGraphDraw();
}
function nhGZoom(f){nhEng.zoom(f);}
function nhGReset(){nhEng.eng.xMin=-6;nhEng.eng.xMax=6;nhGraphDraw();}
window.nhGZoom=nhGZoom;window.nhGReset=nhGReset;

/* ── Inicialización T3 en DOMContentLoaded ──────────────────── */
document.addEventListener('DOMContentLoaded', () => {
  m3InitCanvas();
  bsEng.init(); bsEng.eng.drawFn=bsGraphDraw;
  nhEng.init(); nhEng.eng.drawFn=nhGraphDraw;

  /* Botón play Müller */
  document.getElementById('btnM3Play')?.addEventListener('click',m3Animate);
  /* Botón reset vista Müller */
  document.getElementById('btnM3GReset')?.addEventListener('click',m3GReset);

  document.querySelectorAll('.t3-method-nav[data-t3panel]').forEach(el=>{
    el.addEventListener('click',()=>t3GoTo(el.getAttribute('data-t3panel')));
  });
});



/* ══════════════════════════════════════════════════════════════
   NUMERIX EXPORT — Motor de exportación a Excel
   Genera archivos .xlsx profesionales con SheetJS
   Marca de agua NUMERIX © 2026 en cada hoja
══════════════════════════════════════════════════════════════ */
/* ══════════════════════════════════════════════════════════════
   INGENIERÍA ECONÓMICA — TIR
   Encuentra x* tal que VPN(x*) = 0 usando métodos numéricos.
══════════════════════════════════════════════════════════════ */

/** Construye la expresión VPN(x) a partir de un array de flujos */
function tirBuildExpr(flujos) {
  return flujos.map((f, t) =>
    t === 0 ? `(${f})` : `(${f})/((1+x)^${t})`
  ).join(' + ');
}

/** Genera la tabla HTML de ingreso de flujos */
function tirGenTabla() {
  const n  = parseInt(document.getElementById('tir_n')?.value) || 4;
  const f0 = parseFloat(document.getElementById('tir_f0')?.value) || -10000;
  const container = document.getElementById('tir-flujos-tabla');
  if (!container) return;

  let html = `<div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-size:.85rem;margin-bottom:.5rem;">
    <thead><tr style="background:var(--primary-light);">
      <th style="padding:.5rem .875rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:var(--primary-dark);border-bottom:2px solid #a5b4fc;">Periodo t</th>
      <th style="padding:.5rem .875rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:var(--primary-dark);border-bottom:2px solid #a5b4fc;">Flujo de Caja Fₜ</th>
      <th style="padding:.5rem .875rem;font-family:var(--font-main);font-size:.72rem;font-weight:700;color:var(--primary-dark);border-bottom:2px solid #a5b4fc;">Descripción (opcional)</th>
    </tr></thead><tbody>`;

  for (let t = 0; t <= n; t++) {
    const bg  = t === 0 ? '#fef2f2' : (t % 2 ? 'var(--gray-50)' : '#fff');
    const def = t === 0 ? f0 : '';
    const desc = t === 0 ? 'Inversión inicial' : '';
    html += `<tr style="background:${bg};">
      <td style="padding:.4rem .875rem;font-family:var(--font-mono);font-size:.82rem;font-weight:700;color:${t===0?'#991b1b':'var(--primary-dark)'};border-bottom:1px solid var(--border);">${t}</td>
      <td style="padding:.4rem .875rem;border-bottom:1px solid var(--border);">
        <input type="number" id="tir_flujo_${t}" value="${def}" step="any" placeholder="0"
          style="width:100%;padding:.3rem .55rem;border:1px solid var(--border);border-radius:4px;font-family:var(--font-mono);font-size:.82rem;background:var(--card);" />
      </td>
      <td style="padding:.4rem .875rem;border-bottom:1px solid var(--border);">
        <input type="text" id="tir_desc_${t}" value="${desc}" placeholder="—"
          style="width:100%;padding:.3rem .55rem;border:1px solid var(--border);border-radius:4px;font-family:var(--font-main);font-size:.78rem;color:var(--gray-500);background:var(--card);" />
      </td>
    </tr>`;
  }
  html += '</tbody></table></div>';
  container.innerHTML = html;
}

/** Renderiza el panel de resultado TIR */
function renderTirResult(tir, vpnTir, method, expr, flujos, iterations, converged, rows, buildTableFn) {
  const container = document.getElementById('tirResult');
  if (!container) return;
  const pct     = (tir * 100).toFixed(4);
  const ok      = converged && isFinite(tir) && tir > 0;
  const negTir  = converged && isFinite(tir) && tir <= 0;
  const accentC = ok ? '#065f46' : negTir ? '#92400e' : '#1e40af';
  const bgC     = ok ? 'var(--success-light)' : negTir ? '#fef3c7' : 'var(--primary-light)';
  const bdC     = ok ? '#6ee7b7' : negTir ? '#fcd34d' : '#a5b4fc';

  let html = '';

  /* ── Tarjeta principal ── */
  html += `<div class="card" style="margin-bottom:1.25rem;border-top:4px solid ${ok?'#10b981':'#f59e0b'};">
    <div class="card-header">
      <div class="card-header-icon ${ok?'green':'amber'}">${ok?'✅':'⚠️'}</div>
      <div>
        <div class="card-title">Tasa Interna de Retorno (TIR)</div>
        <div class="card-subtitle">${method} · ${iterations} iteraciones · ${converged?'✓ Convergió':'⚠ No convergió'}</div>
      </div>
      <div style="margin-left:auto;text-align:center;background:${bgC};border:1.5px solid ${bdC};border-radius:var(--radius-sm);padding:.5rem 1.25rem;min-width:120px;">
        <div style="font-family:var(--font-main);font-size:.65rem;color:${accentC};font-weight:600;">TIR =</div>
        <div style="font-family:var(--font-mono);font-size:1.5rem;font-weight:700;color:${accentC};">${pct}%</div>
        <div style="font-family:var(--font-mono);font-size:.75rem;color:var(--gray-400);">i* = ${tir.toFixed(8)}</div>
      </div>
    </div>
    <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:.75rem;padding:0 1.5rem 1.25rem;">
      <div style="padding:.875rem;background:var(--gray-50);border-radius:var(--radius-sm);border:1px solid var(--border);">
        <div style="font-family:var(--font-main);font-size:.7rem;color:var(--gray-500);margin-bottom:.2rem;">TIR (decimal)</div>
        <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:700;">${tir.toFixed(10)}</div>
      </div>
      <div style="padding:.875rem;background:var(--gray-50);border-radius:var(--radius-sm);border:1px solid var(--border);">
        <div style="font-family:var(--font-main);font-size:.7rem;color:var(--gray-500);margin-bottom:.2rem;">VPN(TIR)</div>
        <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:700;color:${Math.abs(vpnTir)<1?'#065f46':'#dc2626'};">${isFinite(vpnTir)?vpnTir.toExponential(4):'—'}</div>
      </div>
      <div style="padding:.875rem;background:${bgC};border-radius:var(--radius-sm);border:1px solid ${bdC};">
        <div style="font-family:var(--font-main);font-size:.7rem;color:${accentC};font-weight:600;margin-bottom:.2rem;">Interpretación</div>
        <div style="font-family:var(--font-main);font-size:.8rem;font-weight:600;color:${accentC};">
          ${ok?'TIR > 0% → Compara con TMAR para decidir':negTir?'TIR ≤ 0% → Proyecto no rentable':'Verifica los flujos ingresados'}
        </div>
      </div>
    </div>
  </div>`;

  /* ── Tabla de flujos descontados ── */
  if (flujos && flujos.length > 0) {
    html += `<div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
      <div style="padding:1rem 1.5rem .75rem;border-bottom:1px solid var(--border);display:flex;align-items:center;gap:.75rem;">
        <div class="card-header-icon purple">📊</div>
        <div><div class="card-title">Flujos Descontados a TIR = ${pct}%</div>
        <div class="card-subtitle">VPN(TIR) = Σ Fₜ/(1+TIR)ᵗ ≈ 0</div></div>
      </div>
      <div style="overflow-x:auto;"><table style="width:100%;border-collapse:collapse;font-size:.82rem;">
        <thead><tr style="background:var(--primary-light);">`;
    ['t','Flujo Fₜ','(1+TIR)ᵗ','Fₜ/(1+TIR)ᵗ','VPN acumulado'].forEach(h2 =>
      html += `<th style="padding:.6rem 1rem;font-family:var(--font-main);font-size:.7rem;font-weight:700;color:var(--primary-dark);border-bottom:2px solid #a5b4fc;text-align:right;">${h2}</th>`
    );
    html += `</tr></thead><tbody>`;
    let acum = 0;
    flujos.forEach((f, t) => {
      const den  = Math.pow(1 + tir, t);
      const fd   = f / den;
      acum      += fd;
      const tdS  = `padding:.55rem 1rem;font-family:var(--font-mono);font-size:.8rem;text-align:right;border-bottom:1px solid #e0e7ff;background:${t%2?'var(--gray-50)':'#fff'};`;
      html += `<tr>
        <td style="${tdS}text-align:center;font-weight:700;color:var(--primary-dark);">${t}</td>
        <td style="${tdS}color:${f<0?'#991b1b':'#065f46'};">${f.toLocaleString('es',{minimumFractionDigits:2})}</td>
        <td style="${tdS}">${den.toFixed(6)}</td>
        <td style="${tdS}color:${fd<0?'#991b1b':'#065f46'};">${fd.toFixed(6)}</td>
        <td style="${tdS}color:${Math.abs(acum)<1?'#065f46':acum<0?'#991b1b':'var(--gray-600)'};">${acum.toFixed(6)}</td>
      </tr>`;
    });
    html += `</tbody></table></div></div>`;
  }

  /* ── Función VPN usada ── */
  html += `<div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header"><div class="card-header-icon purple">ƒ</div>
    <div><div class="card-title">Función VPN(x) utilizada</div></div></div>
    <div style="padding:.75rem 1.5rem 1.25rem;">
      <code style="font-family:var(--font-mono);font-size:.82rem;background:var(--gray-50);
        padding:.5rem .875rem;border-radius:5px;border:1px solid var(--border);display:block;word-break:break-all;">
        VPN(x) = ${expr}
      </code>
    </div>
  </div>`;

  /* ── Iteraciones del método ── */
  if (rows && rows.length > 0 && buildTableFn) {
    html += `<div class="card" style="margin-bottom:1.25rem;">
      <div class="card-header"><div class="card-header-icon purple">📋</div>
      <div><div class="card-title">Iteraciones — ${method}</div>
      <div class="card-subtitle">f(x) = VPN(x)  ·  raíz buscada = TIR</div></div></div>
      <div style="padding:1.25rem 1.5rem;">${buildTableFn(rows)}</div>
    </div>`;
  }

  container.innerHTML = html;
}

/* ── Inicialización TIR (en DOMContentLoaded) ──────────────── */
document.addEventListener('DOMContentLoaded', () => {
  /* Generar tabla inicial */
  tirGenTabla();

  const genBtn = document.getElementById('btnTirGenTabla');
  if (genBtn) genBtn.addEventListener('click', tirGenTabla);

  /* Toggle flujos / función directa */
  document.querySelectorAll('input[name="tir_mode"]').forEach(radio => {
    radio.addEventListener('change', () => {
      const isFlujos = radio.value === 'flujos' && radio.checked;
      const ff = document.getElementById('tir-flujos-fields');
      const fn = document.getElementById('tir-funcion-fields');
      if (ff) ff.style.display = isFlujos ? 'block' : 'none';
      if (fn) fn.style.display = isFlujos ? 'none'  : 'block';
    });
  });

  /* Botón Calcular TIR */
  const tirBtn = document.getElementById('btnCalcularTIR');
  if (!tirBtn) return;

  tirBtn.addEventListener('click', () => {
    clearAlert('tirAlert');
    const tirRes = document.getElementById('tirResult');
    if (tirRes) tirRes.innerHTML = '';

    const mode   = document.querySelector('input[name="tir_mode"]:checked')?.value || 'flujos';
    const metodo = document.getElementById('tir_metodo')?.value || 'newton';
    const i0     = parseFloat(document.getElementById('tir_i0')?.value ?? '0');
    const i1     = parseFloat(document.getElementById('tir_i1')?.value ?? '1');
    const tol    = parseFloat(document.getElementById('tir_tol')?.value ?? '0.000001') || 1e-6;
    const IT     = 300;

    let expr = '', flujos = null;

    if (mode === 'flujos') {
      const n = parseInt(document.getElementById('tir_n')?.value) || 4;
      flujos  = [];
      for (let t = 0; t <= n; t++) {
        const el = document.getElementById(`tir_flujo_${t}`);
        flujos.push(el ? (parseFloat(el.value) || 0) : 0);
      }
      expr = tirBuildExpr(flujos);
    } else {
      expr = document.getElementById('tir_func')?.value?.trim() || '';
      if (!expr) { showAlert('tirAlert','danger','Ingrese la función VPN(x).'); return; }
      if (checkUpperX(expr, 'tirAlert')) return;
    }

    if (isNaN(i0) || isNaN(i1) || i0 >= i1) {
      showAlert('tirAlert','danger','Ingrese un rango válido con i₀ &lt; i₁.'); return;
    }

    /* Evaluar en los límites para info */
    let vpn0 = NaN, vpn1 = NaN;
    try { vpn0 = evalF(expr, i0); } catch(e) {}
    try { vpn1 = evalF(expr, i1); } catch(e) {}

    let res;
    const methodLabel = {bisection:'Bisección',false:'Regla Falsa',newton:'Newton-Raphson',secant:'Secante'}[metodo];

    try {
      if (metodo === 'bisection') {
        if (isFinite(vpn0) && isFinite(vpn1) && vpn0 * vpn1 >= 0)
          showAlert('tirAlert','warning',`⚠ VPN(${i0}) y VPN(${i1}) tienen el mismo signo. Es posible que no haya TIR en este rango o existan múltiples TIR.`);
        res = bisection(expr, i0, i1, tol, IT);
      } else if (metodo === 'false') {
        if (isFinite(vpn0) && isFinite(vpn1) && vpn0 * vpn1 >= 0)
          showAlert('tirAlert','warning',`⚠ No se detectó cambio de signo en [${i0}, ${i1}].`);
        res = falsePosition(expr, i0, i1, tol, IT);
      } else if (metodo === 'newton') {
        res = newtonRaphson(expr, (i0 + i1) / 2, tol, IT);
      } else {
        res = secant(expr, i0, i1, tol, IT);
      }
    } catch(e) { showAlert('tirAlert','danger','Error en el método: ' + e.message); return; }

    if (!isFinite(res.root)) {
      showAlert('tirAlert','danger','El método no convergió. Prueba otro rango o método.'); return;
    }

    let vpnTir = NaN;
    try { vpnTir = evalF(expr, res.root); } catch(e) {}

    const buildFn = metodo === 'newton'  ? buildNewtonTable
                  : metodo === 'secant'  ? buildSecantTable
                  : buildBisectionTable;

    renderTirResult(res.root, vpnTir, methodLabel, expr, flujos,
                    res.iterations, res.converged, res.rows, buildFn);

    showAlert('tirAlert', res.converged ? 'success' : 'warning',
      `${res.converged?'✓':' ⚠'} TIR = ${(res.root*100).toFixed(4)}%  ·  VPN(TIR) ≈ ${isFinite(vpnTir)?vpnTir.toExponential(3):'?'}  ·  ${res.iterations} iteraciones`);
  });
});


const numerixExport = (function () {
  "use strict";
  const C = {
    // Fondos de cabecera por tema
    T1_HEAD:   '92400E',   // ámbar oscuro (Taylor)
    T2_HEAD:   '3730A3',   // índigo oscuro (Métodos)
    T3_HEAD:   '065F46',   // verde oscuro  (Müller)
    // Fondos suaves
    T1_BAND:   'FEF3C7',
    T2_BAND:   'EDE9FE',
    T3_BAND:   'D1FAE5',
    // Texto cabecera
    WHITE:     'FFFFFF',
    // Fila convergida
    CONV_BG:   'D1FAE5',
    CONV_FG:   '065F46',
    // Posible
    POSIB_BG:  'FEF3C7',
    POSIB_FG:  '92400E',
    // Marca de agua (gris muy claro)
    MARK_BG:   'F1F5F9',
    MARK_FG:   '94A3B8',
    // Alternado de filas
    ALT:       'F9FAFB',
    BORDER:    'E5E7EB',
  };

  /* ── Helper: crear celda con estilo completo ──────────────── */
  function cell(v, opts = {}) {
    const c = { v, t: typeof v === 'number' ? 'n' : 's' };
    const s = {};

    if (opts.bold || opts.head) s.font = { bold: true, color: { rgb: opts.headColor || '000000' }, sz: opts.sz || (opts.head ? 11 : 10), name: 'Arial' };
    else                         s.font = { sz: opts.sz || 10, name: 'Arial', color: { rgb: opts.color || '1F2937' } };

    if (opts.bg)    s.fill = { fgColor: { rgb: opts.bg }, patternType: 'solid' };
    if (opts.align) s.alignment = { horizontal: opts.align, vertical: 'center', wrapText: !!opts.wrap };
    else            s.alignment = { vertical: 'center' };

    if (opts.border !== false) {
      const b = { style: 'thin', color: { rgb: C.BORDER } };
      s.border = { top: b, bottom: b, left: b, right: b };
    }

    if (opts.numFmt) s.numFmt = opts.numFmt;
    if (opts.italic) { s.font = s.font || {}; s.font.italic = true; }
    c.s = s;
    return c;
  }

  /* ── Helper: número formateado en celda ───────────────────── */
  function numCell(v, opts = {}) {
    if (v === null || v === undefined || !isFinite(v)) return cell('—', opts);
    return cell(v, { ...opts, t: 'n', numFmt: opts.numFmt || '0.00000000' });
  }

  /* ── Escribir array de arrays en un Sheet ─────────────────── */
  function aoa2ws(aoa) {
    const ws = {};
    let maxCol = 0;
    aoa.forEach((row, R) => {
      row.forEach((val, C_) => {
        if (C_ > maxCol) maxCol = C_;
        const ref = XLSX.utils.encode_cell({ r: R, c: C_ });
        if (val && typeof val === 'object' && 'v' in val) {
          ws[ref] = val;
        } else {
          ws[ref] = { v: val === undefined ? '' : val, t: typeof val === 'number' ? 'n' : 's' };
        }
      });
    });
    ws['!ref'] = XLSX.utils.encode_range({ s: { r: 0, c: 0 }, e: { r: aoa.length - 1, c: maxCol } });
    return ws;
  }

  /* ── Hoja de marca de agua / portada ──────────────────────── */
  function makeCoverSheet(tema, subtema, func, extra = []) {
    const now   = new Date();
    const fecha = now.toLocaleDateString('es-ES', { day:'2-digit', month:'long', year:'numeric' });
    const hora  = now.toLocaleTimeString('es-ES', { hour:'2-digit', minute:'2-digit' });

    const rows = [
      [ cell('', {bg: '0F172A', border:false}) ],
      [ cell('NUMERIX', {bg:'0F172A', color:'FBBF24', bold:true, sz:22, align:'center', border:false}) ],
      [ cell('Plataforma de Métodos Numéricos', {bg:'0F172A', color:'94A3B8', sz:11, align:'center', border:false}) ],
      [ cell('', {bg:'0F172A', border:false}) ],
      [ cell('© 2026 Fernando Granja & Alejandra Tinoco', {bg:'0F172A', color:'6B7280', sz:9, align:'center', italic:true, border:false}) ],
      [ cell('Todos los derechos reservados · Uso académico', {bg:'0F172A', color:'6B7280', sz:9, align:'center', italic:true, border:false}) ],
      [ cell('', {bg:'0F172A', border:false}) ],
      [ cell('──────────────────────────────────────────', {bg:'0F172A', color:'1E40AF', sz:9, align:'center', border:false}) ],
      [ cell('', {border:false}) ],
      [ cell('Tema:', {bold:true, sz:11}), cell(tema, {sz:11, color:'1D4ED8'}) ],
      [ cell('Subtema / Método:', {bold:true, sz:11}), cell(subtema, {sz:11, color:'1D4ED8'}) ],
      [ cell('Función f(x):', {bold:true, sz:11}), cell(func || '—', {sz:11, color:'1D4ED8', bold:true}) ],
    ];
    extra.forEach(([k,v]) => rows.push([ cell(k, {bold:true, sz:11}), cell(v, {sz:11, color:'374151'}) ]));
    rows.push([ cell('') ]);
    rows.push([ cell('Generado el:', {bold:true, sz:10}), cell(fecha + ' a las ' + hora, {sz:10, color:'6B7280'}) ]);
    rows.push([ cell('Software:', {bold:true, sz:10}), cell('NUMERIX v1.0.0 — numerix.app', {sz:10, color:'6B7280'}) ]);

    const ws = aoa2ws(rows);
    ws['!cols'] = [{ wch: 22 }, { wch: 45 }];
    ws['!rows'] = rows.map((_, i) => ({ hpt: i < 8 ? 22 : 18 }));
    return ws;
  }

  /* ── Cabecera de tabla estilizada ─────────────────────────── */
  function makeHeader(cols, bgHex, textHex = 'FFFFFF') {
    return cols.map(c => cell(c, { bg: bgHex, color: textHex, bold: true, align: 'center', sz: 10 }));
  }

  /* ── Fila de datos con alternado ──────────────────────────── */
  function dataRow(vals, rowIdx, opts = {}) {
    const bg = opts.conv ? C.CONV_BG : opts.posib ? C.POSIB_BG : (rowIdx % 2 === 0 ? 'FFFFFF' : C.ALT);
    const fc = opts.conv ? C.CONV_FG : opts.posib ? C.POSIB_FG : '1F2937';
    return vals.map((v, ci) => {
      const isNum = typeof v === 'number' && isFinite(v);
      if (isNum) return cell(v, { bg, color: fc, numFmt: ci === 0 ? '0' : '0.00000000E+00', align: ci === 0 ? 'center' : 'right' });
      return cell(v === null || v === undefined ? '—' : String(v), { bg, color: fc, align: ci === 0 ? 'center' : 'right' });
    });
  }

  /* ── Ajuste automático de columnas ───────────────────────── */
  function autoCols(data) {
    if (!data || !data.length) return [];
    const ncols = Math.max(...data.map(r => r.length));
    return Array.from({ length: ncols }, (_, c) => {
      const max = Math.max(...data.map(r => (r[c] !== undefined ? String(r[c].v ?? r[c] ?? '').length : 0)));
      return { wch: Math.min(Math.max(max + 2, 8), 28) };
    });
  }

  /* ════════════════════════════════════════════════════════════
     TEMA 1 — SERIES DE TAYLOR
  ════════════════════════════════════════════════════════════ */
  function t1() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible. Recargue la página.'); return; }

    const d = (typeof state !== 'undefined' && state.t1Last) ? state.t1Last : null;
    const func = d ? d.funcExpr : (document.getElementById('t1Func')?.value?.trim() || '?');
    const aVal = d ? d.a : (document.getElementById('t1A')?.value || '?');
    const xVal = d ? d.x : (document.getElementById('t1X')?.value || '?');
    const nVal = d ? d.n : (document.getElementById('t1N')?.value || '?');

    const wb = XLSX.utils.book_new();

    /* ── Portada ── */
    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 1 — Aproximaciones de Taylor',
      'Polinomio de Taylor de grado ' + nVal,
      func,
      [
        ['Punto de expansión a:', String(aVal)],
        ['Punto de evaluación x:', String(xVal)],
        ['Grado n:', String(nVal)],
        ['h = x − a:', d ? String(d.h.toFixed(8)) : '?'],
        ['f(x) exacto:', d ? d.fExact.toFixed(10) : '?'],
        ['P_n(x) aprox:', d ? d.polyAcc.toFixed(10) : '?'],
        ['Error |Ea|:', d ? d.eaAbs.toExponential(6) : '?'],
      ]
    ), 'Portada');

    /* ── Hoja de términos ── */
    const headers = ['Término k', 'Derivada f⁽ᵏ⁾(a)', 'k!', 'Coeficiente f⁽ᵏ⁾(a)/k!', 'h = (x−a)', '(x−a)^k', 'Término = coef·(x−a)^k', 'P_n(x) acumulado'];
    const rows = [ makeHeader(headers, C.T1_HEAD) ];

    if (d && d.terms) {
      d.terms.forEach((t, i) => {
        const isLast = i === d.terms.length - 1;
        const bg     = isLast ? 'FEF3C7' : i % 2 ? C.ALT : 'FFFFFF';
        rows.push([
          cell(t.k,      { bg, color: C.T1_HEAD, bold: true, align: 'center' }),
          cell(t.deriv,  { bg, numFmt: '0.00000000', align: 'right' }),
          cell(t.fact,   { bg, numFmt: '0', align: 'center' }),
          cell(t.coef,   { bg, numFmt: '0.00000000', align: 'right' }),
          cell(t.h,      { bg, numFmt: '0.00000000', align: 'right' }),
          cell(t.pow,    { bg, numFmt: '0.00000000', align: 'right' }),
          cell(t.val,    { bg, numFmt: '0.00000000', align: 'right' }),
          cell(t.acc,    { bg, numFmt: '0.00000000', align: 'right', bold: isLast, color: isLast ? C.T1_HEAD : '1F2937' }),
        ]);
      });

      /* Fila de resultado final */
      rows.push([
        cell('RESULTADO', { bg: C.T1_HEAD, color:'FBBF24', bold:true, align:'center' }),
        cell('',  { bg: C.T1_HEAD }),
        cell('',  { bg: C.T1_HEAD }),
        cell('',  { bg: C.T1_HEAD }),
        cell('',  { bg: C.T1_HEAD }),
        cell('',  { bg: C.T1_HEAD }),
        cell('P_n(x) =', { bg: C.T1_HEAD, color:'FBBF24', bold:true, align:'right' }),
        cell(d.polyAcc,  { bg: C.T1_HEAD, color:'FBBF24', bold:true, numFmt:'0.0000000000', align:'right' }),
      ]);
    } else {
      /* Fallback: leer desde DOM */
      const tableEl = document.querySelector('#t1-tabla .cuaderno-table tbody');
      if (tableEl) {
        tableEl.querySelectorAll('tr').forEach((tr, i) => {
          const tds = tr.querySelectorAll('td');
          const vals = Array.from(tds).map(td => td.textContent.trim());
          rows.push(vals.map((v, ci) => {
            const n = parseFloat(v);
            return cell(isNaN(n) ? v : n, { bg: i%2 ? C.ALT:'FFFFFF', align: ci===0?'center':'right',
              numFmt: !isNaN(n) && ci > 0 ? '0.00000000' : undefined });
          }));
        });
      }
    }

    const ws1 = aoa2ws(rows);
    ws1['!cols'] = [{ wch:12 },{ wch:18 },{ wch:8 },{ wch:22 },{ wch:16 },{ wch:16 },{ wch:26 },{ wch:26 }];
    ws1['!rows'] = rows.map(() => ({ hpt: 20 }));
    XLSX.utils.book_append_sheet(wb, ws1, 'Términos Taylor');

    /* ── Hoja de resumen ── */
    const resRows = [
      makeHeader(['Parámetro', 'Valor'], C.T1_HEAD),
      [ cell('Función f(x)',       {bold:true}), cell(func,                            {color:'92400E', bold:true}) ],
      [ cell('Punto expansión a'), cell(String(aVal),                                   {color:'374151'}) ],
      [ cell('Punto evaluación x'),cell(String(xVal),                                   {color:'374151'}) ],
      [ cell('Grado n'),           cell(String(nVal),                                   {color:'374151'}) ],
      [ cell('h = x − a'),         cell(d ? d.h       : '?',                            {numFmt:'0.00000000', color:'374151'}) ],
      [ cell(''),                  cell('') ],
      makeHeader(['Resultado', 'Valor'], C.T1_HEAD),
      [ cell('P_n(x) aproximado',  {bold:true}), cell(d ? d.polyAcc : '?', {numFmt:'0.0000000000', color:'92400E', bold:true}) ],
      [ cell('f(x) valor exacto',  {bold:true}), cell(d ? d.fExact  : '?', {numFmt:'0.0000000000', color:'065F46', bold:true}) ],
      [ cell('Error |Ea|',         {bold:true}), cell(d ? d.eaAbs   : '?', {numFmt:'0.00000000E+00', color:'991B1B', bold:true}) ],
    ];

    /* Agregar info de resultado del DOM si existe */
    document.getElementById('t1-resultado')?.querySelectorAll('.result-card').forEach(card => {
      const lbl = card.querySelector('.result-label')?.textContent?.trim();
      const val = card.querySelector('.result-value, .result-val')?.textContent?.trim();
      if (lbl && val && !['f(x)', 'P_n(x)', 'Error'].some(k => lbl.includes(k)))
        resRows.push([ cell(lbl, {bold:true}), cell(val, {color:'374151'}) ]);
    });

    const ws2 = aoa2ws(resRows);
    ws2['!cols'] = [{ wch:28 },{ wch:32 }];
    ws2['!rows'] = resRows.map(() => ({ hpt: 20 }));
    XLSX.utils.book_append_sheet(wb, ws2, 'Resumen');

    _download(wb, `NUMERIX_T1_Taylor_f(${_slug(func)})_a${aVal}_x${xVal}.xlsx`);
  }

  /* ════════════════════════════════════════════════════════════
     TEMA 2 — MÉTODOS DE RESOLUCIÓN
  ════════════════════════════════════════════════════════════ */
  function t2() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible. Recargue la página.'); return; }

    const method = state.lastMethod || '?';
    const expr   = state.lastFunction || '?';
    const wb     = XLSX.utils.book_new();

    /* Portada */
    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 2 — Métodos de Resolución de Ecuaciones',
      method,
      expr,
      [['Raíz encontrada:', state.lastRoot !== null ? Number(state.lastRoot).toFixed(10) : '?']]
    ), 'Portada');

    /* Detectar si es modo automático o normal */
    const iterContainer = document.getElementById('methodIterTable');
    const isAutoMode    = iterContainer && iterContainer.querySelector('.card-title')?.textContent?.includes('Automático');

    if (isAutoMode) {
      _t2ExportAuto(wb, method, expr, iterContainer);
    } else {
      _t2ExportSingle(wb, method, expr, iterContainer);
    }

    /* Hoja de resultado */
    const resRows = [ makeHeader(['Parámetro','Valor'], C.T2_HEAD) ];
    document.getElementById('resultsContent')?.querySelectorAll('.result-card').forEach(card => {
      const lbl = card.querySelector('.result-label')?.textContent?.trim();
      const val = card.querySelector('.result-value, .result-val')?.textContent?.trim();
      if (lbl && val) resRows.push([ cell(lbl, {bold:true}), cell(val, {color:'3730A3', bold:false}) ]);
    });
    if (resRows.length > 1) {
      const ws = aoa2ws(resRows);
      ws['!cols'] = [{ wch:25 },{ wch:35 }];
      XLSX.utils.book_append_sheet(wb, ws, 'Resultado Final');
    }

    _download(wb, `NUMERIX_T2_${_slug(method)}_${_slug(expr)}.xlsx`);
  }

  function _t2ExportSingle(wb, method, expr, container) {
    /* Leer encabezados y filas de la tabla HTML */
    const table  = container?.querySelector('table');
    if (!table) return;

    const headers = Array.from(table.querySelectorAll('thead th')).map(th => th.textContent.trim());
    const bgMap   = { 'Bisección':'3730A3','Regla Falsa':'1D4ED8','Newton-Raphson':'065F46','Secante':'92400E','Punto Fijo':'831843' };
    const bg      = bgMap[method] || C.T2_HEAD;

    const rows    = [ makeHeader(headers, bg) ];
    table.querySelectorAll('tbody tr').forEach((tr, i) => {
      const tds     = Array.from(tr.querySelectorAll('td'));
      const isConv  = tr.classList.contains('converged-row');
      rows.push(tds.map((td, ci) => {
        const raw = td.textContent.trim().replace('—','');
        const num = parseFloat(raw);
        const v   = raw === '' || raw === '—' ? null : isNaN(num) ? raw : num;
        return cell(v ?? '—', {
          bg: isConv ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF',
          color: isConv ? C.CONV_FG : '1F2937',
          numFmt: typeof v === 'number' && ci > 0 ? '0.00000000E+00' : undefined,
          align: ci === 0 ? 'center' : 'right'
        });
      }));
    });

    const ws = aoa2ws(rows);
    ws['!cols'] = autoCols(rows.map(r => r.map(c => c)));
    ws['!rows'] = rows.map(() => ({ hpt: 18 }));
    XLSX.utils.book_append_sheet(wb, ws, `Iteraciones ${method.substring(0,18)}`);
  }

  function _t2ExportAuto(wb, method, expr, container) {
    /* Hoja 1: resumen de raíces */
    const cards = container.querySelectorAll('[style*="border-left:5px solid"]');
    const summaryRows = [ makeHeader(['r#','Raíz x*','f(r)','Tipo','Intervalo [a,b]','Iteraciones','Convergió'], C.T2_HEAD) ];
    cards.forEach((card, i) => {
      const lines = Array.from(card.querySelectorAll('div')).map(d => d.textContent.trim()).filter(Boolean);
      summaryRows.push([
        cell(i+1, {align:'center', bold:true, color:'3730A3'}),
        cell(lines[1] || '?', {color:'3730A3', bold:true}),
        cell(lines[2] || '?'),
        cell(lines[0] || '?'),
        cell(lines[3] || '?'),
        cell('—'), cell('—')
      ]);
    });
    const ws0 = aoa2ws(summaryRows);
    ws0['!cols'] = [{wch:6},{wch:20},{wch:18},{wch:16},{wch:20},{wch:12},{wch:12}];
    XLSX.utils.book_append_sheet(wb, ws0, 'Raíces Encontradas');

    /* Hoja 2: subintervalos */
    const intrTable = container.querySelector('table');
    if (intrTable) {
      const headers = Array.from(intrTable.querySelectorAll('thead th')).map(th => th.textContent.trim());
      const rows2   = [ makeHeader(headers, C.T2_HEAD) ];
      intrTable.querySelectorAll('tbody tr').forEach((tr, i) => {
        rows2.push(Array.from(tr.querySelectorAll('td')).map((td, ci) => {
          const raw = td.textContent.trim();
          const num = parseFloat(raw);
          return cell(isNaN(num) ? raw : num, {
            bg: i%2 ? C.ALT : 'FFFFFF',
            numFmt: !isNaN(num) && ci > 1 ? '0.000000' : undefined,
            align: ci === 0 ? 'center' : 'right'
          });
        }));
      });
      const ws1 = aoa2ws(rows2);
      ws1['!cols'] = autoCols(rows2);
      XLSX.utils.book_append_sheet(wb, ws1, 'Subintervalos');
    }

    /* Hojas 3+: iteraciones por raíz */
    container.querySelectorAll('.card:last-child > div > div[style*="margin-bottom"]').forEach((block, idx) => {
      const tbl = block.querySelector('table');
      if (!tbl) return;
      const hh  = Array.from(tbl.querySelectorAll('thead th')).map(th => th.textContent.trim());
      const rws = [ makeHeader(hh, C.T2_HEAD) ];
      tbl.querySelectorAll('tbody tr').forEach((tr, i) => {
        const isConv = tr.classList.contains('converged-row');
        rws.push(Array.from(tr.querySelectorAll('td')).map((td, ci) => {
          const raw = td.textContent.trim();
          const num = parseFloat(raw);
          return cell(isNaN(num) ? raw : num, {
            bg: isConv ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF',
            color: isConv ? C.CONV_FG : '1F2937',
            numFmt: !isNaN(num) && ci > 0 ? '0.00000000E+00' : undefined,
            align: ci === 0 ? 'center' : 'right'
          });
        }));
      });
      const ws2 = aoa2ws(rws);
      ws2['!cols'] = autoCols(rws);
      XLSX.utils.book_append_sheet(wb, ws2, `r${idx+1} Iteraciones`);
    });
  }

  /* ════════════════════════════════════════════════════════════
     TEMA 3 — MÜLLER / RAÍCES DE POLINOMIOS
  ════════════════════════════════════════════════════════════ */
  function t3() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible. Recargue la página.'); return; }

    const func = document.getElementById('m3Func')?.value?.trim() || '?';
    const tol  = document.getElementById('m3Tol')?.value || '?';
    const wb   = XLSX.utils.book_new();
    const res  = document.getElementById('m3Result');

    /* Portada */
    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 3 — Raíces de Polinomios',
      'Método de Müller + Deflación',
      func,
      [['Tolerancia:', tol]]
    ), 'Portada');

    /* ── Hoja 1: Resumen de raíces ── */
    const rootCards = res?.querySelectorAll('[style*="border-left:5px solid"]') || [];
    const sumRows   = [ makeHeader(['r#','Valor raíz','Tipo','Método','|f(r)|','Iteraciones'], C.T3_HEAD) ];

    rootCards.forEach((card, i) => {
      const spans  = Array.from(card.querySelectorAll('span'));
      const rNum   = spans[0]?.textContent?.trim() || ('r'+(i+1));
      const tipo   = spans[1]?.textContent?.trim() || '?';
      const iters  = spans[2]?.textContent?.trim() || '?';
      const val    = card.querySelectorAll('div')[2]?.textContent?.trim() || '?';
      const fval   = card.querySelectorAll('div')[3]?.textContent?.trim().replace('|f(r)| ≈ ','') || '?';
      const isReal = tipo.includes('Real');

      sumRows.push([
        cell(rNum,   { bg: C.T3_HEAD, color:'FFFFFF', bold:true, align:'center' }),
        cell(val,    { color:'065F46', bold:true }),
        cell(tipo,   { color: isReal ? '065F46' : '3730A3' }),
        cell('Müller', {}),
        cell(fval,   { align:'right' }),
        cell(iters,  { align:'center' }),
      ]);
    });

    const ws0 = aoa2ws(sumRows);
    ws0['!cols'] = [{wch:8},{wch:28},{wch:12},{wch:14},{wch:18},{wch:12}];
    XLSX.utils.book_append_sheet(wb, ws0, 'Raíces');

    /* ── Hojas 2+: iteraciones Müller por raíz ── */
    const stepBlocks = res?.querySelectorAll('.muller-step-block') || [];
    const raizGroups = {};

    /* Agrupar pasos por raíz (cada raíz tiene su propio color identificador) */
    res?.querySelectorAll('[style*="margin-bottom:1.25rem"]').forEach((block, bi) => {
      const mullerTables = block.querySelectorAll('.muller-table');
      if (!mullerTables.length) return;

      const titleEl = block.querySelector('[style*="font-mono"]');
      const rootVal = titleEl?.textContent?.trim() || ('raíz_' + (bi+1));
      const sheetName = `r${bi+1} Müller`.substring(0,31);

      mullerTables.forEach(tbl => {
        const hh  = Array.from(tbl.querySelectorAll('thead th')).map(th => th.textContent.trim());
        const rws = [ makeHeader(hh, C.T3_HEAD) ];
        tbl.querySelectorAll('tbody tr').forEach((tr, i) => {
          const isConv = tr.classList.contains('converged-row');
          rws.push(Array.from(tr.querySelectorAll('td')).map((td, ci) => {
            const raw = td.textContent.trim();
            const num = parseFloat(raw);
            return cell(isNaN(num) ? (raw||'—') : num, {
              bg: isConv ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF',
              color: isConv ? C.CONV_FG : '1F2937',
              numFmt: !isNaN(num) && ci > 0 ? '0.00000000E+00' : undefined,
              align: ci === 0 ? 'center' : 'right'
            });
          }));
        });
        const ws = aoa2ws(rws);
        ws['!cols'] = autoCols(rws);
        ws['!rows'] = rws.map(() => ({ hpt: 18 }));
        XLSX.utils.book_append_sheet(wb, ws, sheetName);
      });
    });

    /* Si modo Müller clásico (sin deflación) */
    const classicTable = res?.querySelector('.muller-table');
    if (classicTable && !rootCards.length) {
      const hh  = Array.from(classicTable.querySelectorAll('thead th')).map(th => th.textContent.trim());
      const rws = [ makeHeader(hh, C.T3_HEAD) ];
      classicTable.querySelectorAll('tbody tr').forEach((tr, i) => {
        const isConv = tr.classList.contains('converged-row');
        rws.push(Array.from(tr.querySelectorAll('td')).map((td, ci) => {
          const raw = td.textContent.trim();
          const num = parseFloat(raw);
          return cell(isNaN(num) ? (raw||'—') : num, {
            bg: isConv ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF',
            color: isConv ? C.CONV_FG : '1F2937',
            numFmt: !isNaN(num) && ci > 0 ? '0.00000000E+00' : undefined,
            align: ci === 0 ? 'center' : 'right'
          });
        }));
      });
      const ws = aoa2ws(rws);
      ws['!cols'] = autoCols(rws);
      XLSX.utils.book_append_sheet(wb, ws, 'Iteraciones Müller');
    }

    _download(wb, `NUMERIX_T3_Muller_${_slug(func)}.xlsx`);
  }

  /* ── Utilidades internas ─────────────────────────────────── */
  function _slug(s) {
    return (s || 'funcion').replace(/[^a-zA-Z0-9]/g, '_').substring(0, 24);
  }

  function _download(wb, filename) {
    try {
      XLSX.writeFile(wb, filename);
    } catch(e) {
      alert('Error al generar el Excel: ' + e.message);
    }
  }

  /* ── Export T3.2 Bairstow ────────────────────────────────── */
  function t3Bairstow() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible.'); return; }
    const d = (typeof state !== 'undefined') ? state.bsLast : null;
    if (!d) { alert('Ejecuta Bairstow primero para generar datos.'); return; }
    const { data, expr, tol } = d;
    const wb = XLSX.utils.book_new();

    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 3.2 — Método de Bairstow',
      'Deflación por factores cuadráticos (x² − r·x − s)',
      expr,
      [['Tolerancia:', String(tol)],
       ['Raíces encontradas:', String(data.roots.length)],
       ['Sesiones Bairstow:', String(data.sessions.length)]]
    ), 'Portada');

    /* Hoja de resumen de raíces */
    const sumRows = [ makeHeader(['r#','Parte Real','Parte Imag.','Tipo','Método'], C.T3_HEAD) ];
    data.roots.forEach((r, i) => {
      const isReal = Math.abs(r.im) < 1e-6;
      sumRows.push([
        cell('r'+(i+1), { bg: C.T3_HEAD, color:'FFFFFF', bold:true, align:'center' }),
        cell(r.re, { numFmt:'0.00000000', align:'right' }),
        cell(isReal ? 0 : r.im, { numFmt:'0.00000000', align:'right' }),
        cell(isReal ? 'Real' : 'Compleja', { color: isReal?'065F46':'3730A3' }),
        cell(r.type || 'bairstow', {}),
      ]);
    });
    const ws0 = aoa2ws(sumRows);
    ws0['!cols'] = [{wch:6},{wch:20},{wch:20},{wch:12},{wch:20}];
    XLSX.utils.book_append_sheet(wb, ws0, 'Raíces');

    /* Una hoja por sesión con tabla completa */
    data.sessions.forEach((sess, si) => {
      if (!sess.rows || sess.rows.length === 0) return;
      const hh  = makeHeader(['Iter.','r','s','b[n-1] (S)','b[n] (R)','Δr','Δs','Ea(r)%','Ea(s)%'], C.T3_HEAD);
      const rws = [hh];
      sess.rows.forEach((row, i) => {
        const bg = row.converged ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF';
        const fc = row.converged ? C.CONV_FG : '1F2937';
        rws.push([
          cell(row.iter,  { bg, color:fc, align:'center', bold:row.converged }),
          cell(row.r,     { bg, color:fc, numFmt:'0.00000000', align:'right' }),
          cell(row.s,     { bg, color:fc, numFmt:'0.00000000', align:'right' }),
          cell(row.S,     { bg, color:fc, numFmt:'0.00000000E+00', align:'right' }),
          cell(row.R,     { bg, color:fc, numFmt:'0.00000000E+00', align:'right' }),
          cell(row.dr,    { bg, color:fc, numFmt:'0.00000000E+00', align:'right' }),
          cell(row.ds,    { bg, color:fc, numFmt:'0.00000000E+00', align:'right' }),
          cell(row.ea_r,  { bg, color:fc, numFmt:'0.0000', align:'right' }),
          cell(row.ea_s,  { bg, color:fc, numFmt:'0.0000', align:'right' }),
        ]);
      });
      const ws = aoa2ws(rws);
      ws['!cols'] = [{wch:6},{wch:16},{wch:16},{wch:18},{wch:18},{wch:18},{wch:18},{wch:10},{wch:10}];
      ws['!rows'] = rws.map(() => ({hpt:18}));
      const rPairs = sess.roots ? sess.roots.map((z,zi) => {
        const v = Math.abs(z.im)<1e-6 ? z.re.toFixed(4) : `${z.re.toFixed(3)}±${Math.abs(z.im).toFixed(3)}i`;
        return v;
      }).join(',') : '';
      XLSX.utils.book_append_sheet(wb, ws, `Sesion${si+1}`.substring(0,31));
    });

    _download(wb, `NUMERIX_T3_Bairstow_${_slug(expr)}.xlsx`);
  }

  /* ── Export T3.3 Horner ──────────────────────────────────── */
  function t3NewtonHorner() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible.'); return; }
    const d = (typeof state !== 'undefined') ? state.nhLast : null;
    if (!d) { alert('Ejecuta el Método de Horner primero.'); return; }
    const { data, expr, c } = d;
    const wb = XLSX.utils.book_new();

    /* Calcular resultados */
    const first  = data?.evals?.[0]?.first;
    const second = data?.evals?.[1]?.first;

    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 3.3 — Método de Horner',
      'Evaluación de P(c) y P\'(c) por recurrencia anidada',
      expr,
      [['Punto de evaluación c:', String(c)],
       ['P(c) =', first ? first.pc.toFixed(10) : '?'],
       ["P'(c) = Q(c) =", second ? second.pc.toFixed(10) : '?']]
    ), 'Portada');

    /* Una hoja por aplicación de Horner */
    if (data?.evals) {
      data.evals.forEach((ev, idx) => {
        if (!ev?.first?.steps) return;
        const sheetName = (idx === 0 ? '1ra Aplic P(c)' : '2da Aplic Q(c)=P_prima_c').substring(0,31);
        const hh  = makeHeader(['k','a_k','c × b_(k+1)','b_k  =  a_k + c×b_(k+1)'], C.T3_HEAD);
        const rws = [hh];

        ev.first.steps.forEach((step, i) => {
          const isLast = i === ev.first.steps.length - 1;
          const bg = isLast ? 'FEF3C7' : i%2 ? C.ALT : 'FFFFFF';
          const fc = isLast ? C.T1_HEAD : '1F2937';
          rws.push([
            cell(step.k,   { bg, color:fc, align:'center', bold:isLast }),
            cell(step.ak,  { bg, color:fc, numFmt:'0.00000000', align:'right', bold:isLast }),
            cell(step.cTimesPrev !== null ? step.cTimesPrev : '', { bg, numFmt:'0.00000000', align:'right' }),
            cell(step.bk,  { bg, color: isLast ? C.T1_HEAD : fc, numFmt:'0.00000000', align:'right', bold:isLast }),
          ]);
        });

        /* Fila resultado final */
        const pcVal = ev.first.pc;
        rws.push([
          cell(idx===0 ? 'P(c) =' : "P'(c) = Q(c) =", { bg:C.T3_HEAD, color:'FFFFFF', bold:true, align:'right' }),
          cell('', {bg:C.T3_HEAD}), cell('', {bg:C.T3_HEAD}),
          cell(pcVal, { bg:C.T3_HEAD, color:'FBBF24', bold:true, numFmt:'0.0000000000', align:'right' }),
        ]);

        const ws = aoa2ws(rws);
        ws['!cols'] = [{wch:6},{wch:18},{wch:22},{wch:26}];
        ws['!rows'] = rws.map(() => ({hpt:20}));
        XLSX.utils.book_append_sheet(wb, ws, sheetName);
      });
    }

    _download(wb, `NUMERIX_T3_Horner_${_slug(expr)}_c${c}.xlsx`);
  }

  /* ── Export T4 Newton-Raphson Sistemas ──────────────────── */
  function t4() {
    if (typeof XLSX === 'undefined') { alert('SheetJS no disponible.'); return; }
    const d = (typeof state !== 'undefined') ? state.t4Last : null;
    if (!d) { alert('Ejecuta el sistema primero para generar datos.'); return; }
    const { result, exprs, vars, tol } = d;
    const { solution, iterations } = result;
    const n    = vars.length;
    const last = iterations.at(-1);
    const conv = last?.converged;
    const wb   = XLSX.utils.book_new();

    /* ── Portada ── */
    XLSX.utils.book_append_sheet(wb, makeCoverSheet(
      'Tema 4 — Newton-Raphson Sistemas No Lineales',
      'X^(k+1) = X^(k) − [J(X^(k))]⁻¹ · F(X^(k))',
      exprs.map((e,i) => `f${i+1} = ${e}`).join('  |  '),
      [
        ['Variables:', vars.join(', ')],
        ['Tolerancia ‖ΔX‖:', String(tol)],
        ['Iteraciones:', String(iterations.length)],
        ['Convergencia:', conv ? 'Sí ✓' : 'No (máx. iteraciones)'],
        ...vars.map((v,i) => [`${v}* =`, solution[i].toFixed(10)]),
      ]
    ), 'Portada');

    /* ── Hoja: Tabla de iteraciones ── */
    const T4_HEAD = '0369A1';
    const hdrs = ['Iter.', ...vars.map(v=>`${v}(k)`), ...exprs.map((_,i)=>`f${i+1}(X)`),
                  ...vars.map(v=>`Δ${v}`), '‖ΔX‖', '‖F‖'];
    const iterRows = [ makeHeader(hdrs, T4_HEAD) ];

    iterations.forEach((it, i) => {
      const bg = it.converged ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF';
      const fc = it.converged ? C.CONV_FG : '1F2937';
      const row = [
        cell(it.k, { bg, color: T4_HEAD, bold:true, align:'center' }),
        ...it.X.map(v   => cell(v,          { bg, color:fc, numFmt:'0.00000000', align:'right' })),
        ...it.F.map(v   => cell(v,          { bg, color: Math.abs(v)<0.001?'065F46':'991B1B', numFmt:'0.00000000E+00', align:'right' })),
        ...it.deltaX.map(v => cell(v,       { bg, color:fc, numFmt:'0.00000000', align:'right' })),
        cell(it.normDx, { bg, color: it.converged?'065F46':fc, numFmt:'0.00000000E+00', align:'right', bold:it.converged }),
        cell(it.normF,  { bg, color:fc, numFmt:'0.00000000E+00', align:'right' }),
      ];
      iterRows.push(row);
    });

    const ws0 = aoa2ws(iterRows);
    ws0['!cols'] = [{wch:6}, ...vars.map(()=>({wch:16})), ...exprs.map(()=>({wch:16})),
                   ...vars.map(()=>({wch:16})), {wch:16}, {wch:16}];
    ws0['!rows'] = iterRows.map(()=>({hpt:18}));
    XLSX.utils.book_append_sheet(wb, ws0, 'Iteraciones');

    /* ── Hoja: Jacobiana por iteración ── */
    const jacHdrs = ['Iter.', ...vars.map(v=>`x=(${v})`),
                     ...vars.flatMap((vi,i) => vars.map((vj,j) => `∂f${i+1}/∂${vj}`))];
    const jacRows = [ makeHeader(jacHdrs, T4_HEAD) ];
    iterations.forEach((it, i) => {
      const bg = it.converged ? C.CONV_BG : i%2 ? C.ALT : 'FFFFFF';
      const fc = it.converged ? C.CONV_FG : '1F2937';
      const flatJ = it.J.flat();
      jacRows.push([
        cell(it.k, { bg, color:T4_HEAD, bold:true, align:'center' }),
        ...it.X.map(v => cell(v, { bg, color:fc, numFmt:'0.000000', align:'right' })),
        ...flatJ.map(v => cell(v, { bg, color:fc, numFmt:'0.000000', align:'right' })),
      ]);
    });
    const ws1 = aoa2ws(jacRows);
    ws1['!cols'] = [{wch:6}, ...vars.map(()=>({wch:14})),
                   ...vars.flatMap(()=>vars.map(()=>({wch:16})))];
    ws1['!rows'] = jacRows.map(()=>({hpt:18}));
    XLSX.utils.book_append_sheet(wb, ws1, 'Jacobianas');

    /* ── Hoja: Solución y verificación ── */
    const solRows = [
      makeHeader(['Variable','Valor solución','f(X*) verificación','Estado'], T4_HEAD),
    ];
    vars.forEach((v, i) => {
      let fv = NaN;
      try { fv = (typeof t4EvalF === 'function') ? t4EvalF(exprs[i], vars, solution) : NaN; } catch{}
      const ok = isFinite(fv) && Math.abs(fv) < 1e-3;
      solRows.push([
        cell(v+'*',          { color: T4_HEAD, bold:true }),
        cell(solution[i],    { numFmt:'0.0000000000', color: T4_HEAD, bold:true }),
        cell(isFinite(fv)?fv:NaN, { numFmt:'0.00000000E+00', color: ok?'065F46':'991B1B' }),
        cell(ok?'✓ OK':'⚠ Revisar', { color: ok?'065F46':'991B1B', bold:true }),
      ]);
    });
    solRows.push([cell(''),cell(''),cell(''),cell('')]);
    solRows.push([
      cell('Convergencia', {bold:true}),
      cell(conv?'Sí':'No', {color:conv?'065F46':'991B1B',bold:true}),
      cell('Iteraciones', {bold:true}),
      cell(iterations.length, {align:'center'}),
    ]);
    const ws2 = aoa2ws(solRows);
    ws2['!cols'] = [{wch:12},{wch:24},{wch:24},{wch:14}];
    ws2['!rows'] = solRows.map(()=>({hpt:20}));
    XLSX.utils.book_append_sheet(wb, ws2, 'Solución');

    _download(wb, `NUMERIX_T4_NR_Sistemas_${vars.join('')}.xlsx`);
  }

  /* Exponer botones de descarga cuando hay datos */
  function showT1Bar()  { const b = document.getElementById('t1-download-bar');  if (b) b.style.display='block'; }
  function showT2Bar()  { const b = document.getElementById('t2-download-bar');  if (b) b.style.display='block'; }
  function showT3Bar()  { const b = document.getElementById('t3-download-bar');  if (b) b.style.display='block'; }
  function showBsBar()  { const b = document.getElementById('bs-download-bar');  if (b) b.style.display='block'; }
  function showNhBar()  { const b = document.getElementById('nh-download-bar');  if (b) b.style.display='block'; }

  return { t1, t2, t3, t3Bairstow, t3NewtonHorner, t4, showT1Bar, showT2Bar, showT3Bar, showBsBar, showNhBar };
})();

window.numerixExport = numerixExport;

/* ══════════════════════════════════════════════════════════════
   TEMA 4 — NEWTON-RAPHSON PARA SISTEMAS NO LINEALES
   X^(k+1) = X^(k) - [J(X^(k))]^(-1) · F(X^(k))
   Jacobiana por diferencias centrales numéricas
══════════════════════════════════════════════════════════════ */

const T4_VARS = ['x','y','z','w'];

/* ── Evaluar función multivariable segura ──────────────────── */
function t4EvalF(exprRaw, vars, vals) {
  let e = exprRaw;
  /* Reemplazar variables de mayor longitud primero */
  vars.forEach((v, i) => {
    e = e.replace(new RegExp('\\b' + v + '\\b', 'g'), '(' + vals[i] + ')');
  });
  e = e.replace(/\^/g, '**')
       .replace(/\bsin\b/g,'Math.sin').replace(/\bcos\b/g,'Math.cos')
       .replace(/\btan\b/g,'Math.tan').replace(/\bexp\b/g,'Math.exp')
       .replace(/\bln\b/g,'Math.log').replace(/\bsqrt\b/g,'Math.sqrt')
       .replace(/\babs\b/g,'Math.abs').replace(/\bpi\b/g,'Math.PI')
       .replace(/\be\b/g,'Math.E');
  return Function('"use strict"; return (' + e + ')')();
}

/* ── Derivada parcial numérica ─────────────────────────────── */
function t4Partial(expr, vars, vals, i, h=1e-7) {
  const v1 = [...vals], v2 = [...vals];
  v1[i] += h; v2[i] -= h;
  return (t4EvalF(expr, vars, v1) - t4EvalF(expr, vars, v2)) / (2*h);
}

/* ── Resolver sistema lineal Ax=b por eliminación Gaussiana ── */
function t4GaussElim(A, b) {
  const n = b.length;
  /* Clonar */
  const M = A.map((row,i) => [...row, b[i]]);

  for (let col = 0; col < n; col++) {
    /* Pivoteo parcial */
    let maxRow = col;
    for (let row = col+1; row < n; row++)
      if (Math.abs(M[row][col]) > Math.abs(M[maxRow][col])) maxRow = row;
    [M[col], M[maxRow]] = [M[maxRow], M[col]];

    if (Math.abs(M[col][col]) < 1e-15) return null; /* singular */

    for (let row = col+1; row < n; row++) {
      const f = M[row][col] / M[col][col];
      for (let k = col; k <= n; k++) M[row][k] -= f * M[col][k];
    }
  }

  /* Sustitución regresiva */
  const x = new Array(n).fill(0);
  for (let i = n-1; i >= 0; i--) {
    x[i] = M[i][n];
    for (let j = i+1; j < n; j++) x[i] -= M[i][j] * x[j];
    x[i] /= M[i][i];
  }
  return x;
}

/* ── Motor principal Newton-Raphson Sistemas ────────────────── */
function t4NewtonSystems(exprs, vars, x0, tol, maxIter) {
  let X = [...x0];
  const n = exprs.length;
  const iterations = [];

  for (let k = 0; k < maxIter; k++) {
    /* Evaluar F(X) */
    let F;
    try {
      F = exprs.map(expr => t4EvalF(expr, vars, X));
    } catch(e) { throw new Error('Error evaluando ecuaciones en X=(' + X.map(v=>v.toFixed(4)).join(', ') + '): ' + e.message); }

    if (F.some(v => !isFinite(v)))
      throw new Error('F(X) contiene valores no finitos. Revisa las ecuaciones o el punto inicial.');

    /* Construir Jacobiana J(X) */
    const J = [];
    for (let i = 0; i < n; i++) {
      J.push([]);
      for (let j = 0; j < n; j++)
        J[i].push(t4Partial(exprs[i], vars, X, j));
    }

    /* Resolver J·ΔX = -F */
    const negF = F.map(v => -v);
    const deltaX = t4GaussElim(J, negF);
    if (!deltaX)
      throw new Error('Jacobiana singular en la iteración ' + (k+1) + '. Intenta con un punto inicial diferente.');

    const normF  = Math.sqrt(F.reduce((s,v)=>s+v*v, 0));
    const normDx = Math.sqrt(deltaX.reduce((s,v)=>s+v*v, 0));

    /* Calcular Ea relativo por componente */
    const ea = deltaX.map((dx, i) => Math.abs(X[i]) > 1e-14 ? Math.abs(dx/X[i])*100 : Math.abs(dx)*100);

    iterations.push({
      k: k+1,
      X:      [...X],
      F:      [...F],
      J:      J.map(row=>[...row]),
      deltaX: [...deltaX],
      normF, normDx, ea,
      converged: normDx < tol
    });

    X = X.map((xi, i) => xi + deltaX[i]);

    if (normDx < tol) break;
  }

  return { solution: X, iterations };
}

/* ── Renderizar resultado T4 ────────────────────────────────── */
function t4RenderResult(result, exprs, vars, tol) {
  const container = document.getElementById('t4Result');
  const { solution, iterations } = result;
  const converged = iterations.at(-1)?.converged || false;
  const COLORS = ['#4f46e5','#10b981','#f59e0b','#ef4444'];
  let html = '';

  /* ══ 1. SOLUCIÓN ══ */
  html += `
  <div class="card t4r-card" style="border-top:4px solid ${converged?'#10b981':'#f59e0b'}">
    <div class="card-header">
      <div class="card-header-icon ${converged?'green':'amber'}">${converged?'✅':'⚠️'}</div>
      <div>
        <div class="card-title">Solución del Sistema</div>
        <div class="card-subtitle">${iterations.length} iter. · ${converged?'✓ Convergió':'⚠ Máx. iteraciones'}</div>
      </div>
    </div>
    <div class="t4r-sol-grid">
      ${vars.map((v,i)=>{
        const col=COLORS[i%COLORS.length];
        return `<div class="t4r-sol-card" style="border-left-color:${col}">
          <div class="t4r-sol-lbl" style="color:${col}">${v}*</div>
          <div class="t4r-sol-val" style="color:${col}">${solution[i].toFixed(10)}</div>
        </div>`;
      }).join('')}
    </div>
    <div class="t4r-chips">
      ${exprs.map((expr,i)=>{
        let fv=NaN; try{fv=t4EvalF(expr,vars,solution);}catch{}
        const ok=isFinite(fv)&&Math.abs(fv)<1e-3;
        return `<span class="t4r-chip ${ok?'t4r-chip-ok':'t4r-chip-err'}">f${i+1}(X*)=${isFinite(fv)?fv.toExponential(3):'?'} ${ok?'✓':'⚠'}</span>`;
      }).join('')}
    </div>
  </div>`;

  /* ══ 2. TABLA ══ */
  html += `
  <div class="card t4r-card" style="padding:0">
    <div class="t4r-card-hdr">
      <div class="card-header-icon blue">📋</div>
      <div>
        <div class="card-title">Tabla de Iteraciones</div>
        <div class="card-subtitle">X<sup>(k+1)</sup> = X<sup>(k)</sup> − [J]<sup>−1</sup>·F</div>
      </div>
    </div>
    <div class="t4r-tbl-wrap">
      <table class="t4r-tbl">
        <thead><tr>
          <th class="t4r-th" style="text-align:center">k</th>
          ${vars.map(v=>`<th class="t4r-th">${v}<sup>(k)</sup></th>`).join('')}
          ${exprs.map((_,i)=>`<th class="t4r-th">f${i+1}</th>`).join('')}
          ${vars.map(v=>`<th class="t4r-th">Δ${v}</th>`).join('')}
          <th class="t4r-th">‖ΔX‖</th>
          <th class="t4r-th">‖F‖</th>
        </tr></thead>
        <tbody>
          ${iterations.map((it,i)=>{
            const bg=it.converged?'var(--success-light)':i%2?'var(--gray-50)':'#fff';
            const fc=it.converged?'#065f46':'var(--gray-700)';
            const td=(val,extra='')=>`<td class="t4r-td" style="background:${bg};color:${fc};${extra}">${val}</td>`;
            return `<tr>
              ${td(it.k,'text-align:center;font-weight:700;color:var(--primary-dark)')}
              ${it.X.map(v=>td(v.toFixed(6))).join('')}
              ${it.F.map(v=>td(v.toExponential(3),`color:${Math.abs(v)<0.001?'#065f46':'#991b1b'}`)).join('')}
              ${it.deltaX.map(v=>td(v.toFixed(6))).join('')}
              ${td(it.normDx.toExponential(3),`font-weight:${it.converged?700:400};color:${it.converged?'#065f46':fc}`)}
              ${td(it.normF.toExponential(3))}
            </tr>`;
          }).join('')}
        </tbody>
      </table>
    </div>
  </div>`;

  /* ══ 3. PASO A PASO ══ */
  html += `
  <div class="card t4r-card">
    <div class="card-header">
      <div class="card-header-icon blue">🔍</div>
      <div>
        <div class="card-title">Desarrollo Paso a Paso</div>
        <div class="card-subtitle">F(X), Jacobiana y ΔX por iteración</div>
      </div>
    </div>
    <div class="t4r-steps">
      ${iterations.map(it=>{
        const col=it.converged?'#10b981':'#4f46e5';
        const Xnew=it.X.map((xi,i)=>xi+it.deltaX[i]);
        return `
        <div class="muller-step-block t4r-step" style="border-left-color:${col}">
          <div class="muller-step-header" style="background:${col}14;border-bottom-color:${col}30">
            <div class="muller-step-num" style="background:${col};flex-shrink:0">${it.k}</div>
            <div class="t4r-step-ttl">Iter.${it.k} — (${it.X.map(v=>v.toFixed(3)).join(', ')})${it.converged?` <span style="color:${col}">✓</span>`:''}</div>
          </div>
          <div class="muller-step-body t4r-step-body">

            <div class="muller-data-row">
              <div class="muller-data-label">F(X<sup>(k)</sup>)</div>
              ${it.F.map((v,i)=>`<div class="muller-data-val">f${i+1} = ${v.toFixed(8)}</div>`).join('')}
            </div>

            <div class="muller-data-row">
              <div class="muller-data-label">Jacobiana J</div>
              ${it.J.map((row,i)=>row.map((v,j)=>`<div class="muller-data-val t4r-jac">∂f${i+1}/∂${vars[j]}=${v.toFixed(5)}</div>`).join('')).join('')}
            </div>

            <div class="muller-data-row t4r-delta" style="grid-column:1/-1;border-color:${col};background:${col}08">
              <div class="muller-data-label">ΔX → X<sup>(k+1)</sup></div>
              ${it.deltaX.map((v,i)=>`<div class="muller-data-val">Δ${vars[i]}=${v.toFixed(8)}</div>`).join('')}
              ${Xnew.map((v,i)=>`<div class="muller-data-val" style="color:${col};font-weight:700">${vars[i]}*=${v.toFixed(8)}</div>`).join('')}
              <div class="muller-data-val muted">‖ΔX‖=${it.normDx.toExponential(4)} ‖F‖=${it.normF.toExponential(4)}${it.converged?` <span style="color:${col};font-weight:700">✓&lt;${tol}</span>`:''}</div>
            </div>

          </div>
        </div>`;
      }).join('')}
    </div>
  </div>`;

  container.innerHTML = html;
  if (typeof state !== 'undefined') state.t4Last = { result, exprs, vars, tol };
  setTimeout(()=>{ const b=document.getElementById('t4-download-bar'); if(b) b.style.display='block'; }, 50);
}

/* ── UI dinámica: generar campos según n ────────────────────── */
function t4BuildUI() {
  const n      = parseInt(document.getElementById('t4_n')?.value) || 2;
  const vars   = T4_VARS.slice(0, n);

  /* Ecuaciones */
  const eqCont = document.getElementById('t4-eqs-container');
  if (!eqCont) return;
  eqCont.innerHTML = '';
  const defaults2 = ['x^2 + x*y - 10', 'y + 3*x*y^2 - 57'];
  const defaults3 = ['x + y + z - 3', 'x^2 + y^2 - 2', 'x*z - 1'];
  const defaults4 = ['x + y + z + w - 4', 'x^2 + y^2 - 2', 'z^2 + w^2 - 2', 'x*y*z*w - 1'];
  const defs = n===2 ? defaults2 : n===3 ? defaults3 : defaults4;

  vars.forEach((v, i) => {
    const div = document.createElement('div');
    div.className = 'form-group';
    div.style.marginBottom = '.75rem';
    div.innerHTML = `
      <label for="t4_eq_${i}">
        Ecuación f<sub>${i+1}</sub>(${vars.join(', ')}) = 0
      </label>
      <input type="text" id="t4_eq_${i}" class="mono"
        value="${defs[i] || ''}"
        placeholder="Ej: ${defs[i] || 'x^2 + y - 1'}" />
      <div class="hint">Variables disponibles: ${vars.join(', ')} · Usa ^ para potencias</div>`;
    eqCont.appendChild(div);
  });

  /* Vector inicial */
  const x0Cont = document.getElementById('t4-x0-container');
  if (!x0Cont) return;
  x0Cont.innerHTML = '';
  const defX0_2=[1.5,3.5], defX0_3=[1,1,1], defX0_4=[1,1,1,1];
  const defX0 = n===2 ? defX0_2 : n===3 ? defX0_3 : defX0_4;
  vars.forEach((v, i) => {
    const div = document.createElement('div');
    div.className = 'form-group';
    div.style.flex = '1';
    div.style.minWidth = '100px';
    div.innerHTML = `<label for="t4_x0_${i}">${v}<sub>₀</sub></label>
      <input type="number" id="t4_x0_${i}" value="${defX0[i]}" step="any" />`;
    x0Cont.appendChild(div);
  });
}

/* ── Gráfica interactiva para sistemas 2×2 ──────────────────── */
const t4Eng = t3GMakeEngine({ canvasId:'t4Canvas', tooltipId:'t4Tooltip', coordsId:'t4GraphCoords', bgDark:false });
const t4GState = { exprs:[], vars:[], solution:[], iterations:[] };

function t4GraphDraw() {
  const {eng, drawBase, drawCrosshair, drawWatermark, drawRootLabel} = t4Eng;
  if (!eng.canvas) return;
  const {exprs, vars, solution, iterations} = t4GState;
  const {toC, W, H} = drawBase();
  const ctx = eng.ctx;
  const {xMin, xMax, yMin, yMax} = eng;

  if (!exprs.length) {
    ctx.fillStyle='#94a3b8'; ctx.font='13px "Poppins",sans-serif'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('Resuelve el sistema para ver la gráfica', W/2, H/2); ctx.textBaseline='alphabetic';
    drawWatermark(W,H,false); return;
  }

  /* Dibujar curvas de nivel f1=0 y f2=0 usando marching squares simplificado */
  const CURVE_COLORS = ['#4f46e5','#10b981'];
  const CURVE_NAMES  = ['f₁(x,y) = 0','f₂(x,y) = 0'];
  const STEPS = 120;
  const dx = (xMax - xMin) / STEPS, dy = (yMax - yMin) / STEPS;

  exprs.slice(0,2).forEach((expr, ci) => {
    ctx.strokeStyle = CURVE_COLORS[ci]; ctx.lineWidth = 2.5;
    /* Precompute grid */
    const grid = [];
    for (let j = 0; j <= STEPS; j++) {
      grid.push([]);
      for (let i = 0; i <= STEPS; i++) {
        const wx = xMin + i * dx, wy = yMin + j * dy;
        let v = NaN;
        try { v = t4EvalF(expr, vars, [wx, wy]); } catch {}
        grid[j].push(isFinite(v) ? v : NaN);
      }
    }
    /* Draw contour f=0 by linear interpolation on cell edges */
    for (let j = 0; j < STEPS; j++) {
      for (let i = 0; i < STEPS; i++) {
        const v00=grid[j][i], v10=grid[j][i+1], v01=grid[j+1][i], v11=grid[j+1][i+1];
        if ([v00,v10,v01,v11].some(v=>isNaN(v))) continue;
        const pts = [];
        const interp = (v0,v1,t0,t1) => t0 + (t1-t0)*(-v0)/(v1-v0);
        if (v00*v10<0) pts.push({x:interp(v00,v10,xMin+i*dx,xMin+(i+1)*dx), y:yMin+j*dy});
        if (v10*v11<0) pts.push({x:xMin+(i+1)*dx, y:interp(v10,v11,yMin+j*dy,yMin+(j+1)*dy)});
        if (v01*v11<0) pts.push({x:interp(v01,v11,xMin+i*dx,xMin+(i+1)*dx), y:yMin+(j+1)*dy});
        if (v00*v01<0) pts.push({x:xMin+i*dx, y:interp(v00,v01,yMin+j*dy,yMin+(j+1)*dy)});
        if (pts.length >= 2) {
          const {x:px0,y:py0}=toC(pts[0].x,pts[0].y), {x:px1,y:py1}=toC(pts[1].x,pts[1].y);
          ctx.beginPath(); ctx.moveTo(px0,py0); ctx.lineTo(px1,py1); ctx.stroke();
        }
      }
    }
  });

  /* Trayectoria de iteraciones */
  if (iterations.length > 0) {
    ctx.save(); ctx.setLineDash([4,3]); ctx.strokeStyle='#f59e0b'; ctx.lineWidth=1.5; ctx.globalAlpha=0.7;
    ctx.beginPath();
    iterations.forEach((it, i) => {
      const {x:px,y:py}=toC(it.X[0],it.X[1]);
      if(i===0) ctx.moveTo(px,py); else ctx.lineTo(px,py);
    });
    const last=iterations.at(-1);
    const Xfin=[last.X[0]+last.deltaX[0], last.X[1]+last.deltaX[1]];
    const{x:pxf,y:pyf}=toC(Xfin[0],Xfin[1]);
    ctx.lineTo(pxf,pyf);
    ctx.stroke(); ctx.restore();

    /* Puntos de iteraciones */
    iterations.forEach((it, i) => {
      const {x:px,y:py}=toC(it.X[0],it.X[1]);
      ctx.beginPath(); ctx.arc(px,py,4,0,Math.PI*2);
      ctx.fillStyle='#f59e0b'; ctx.strokeStyle='#fff'; ctx.lineWidth=1.5; ctx.fill(); ctx.stroke();
      if (i===0 || i===iterations.length-1) {
        ctx.font='700 10px "Poppins",sans-serif'; ctx.fillStyle='#92400e';
        ctx.textAlign='left'; ctx.textBaseline='bottom';
        ctx.fillText(i===0?'X⁰':'X⁽'+i+'⁾', px+6, py-4);
        ctx.textBaseline='alphabetic';
      }
    });
  }

  /* Punto solución */
  if (solution.length >= 2 && isFinite(solution[0]) && isFinite(solution[1])) {
    const {x:px,y:py}=toC(solution[0],solution[1]);
    if (px>=0&&px<=W&&py>=0&&py<=H) {
      ctx.save(); ctx.globalAlpha=0.15; ctx.beginPath(); ctx.arc(px,py,16,0,Math.PI*2);
      ctx.fillStyle='#ef4444'; ctx.fill(); ctx.restore();
      ctx.beginPath(); ctx.arc(px,py,7,0,Math.PI*2);
      ctx.fillStyle='#ef4444'; ctx.strokeStyle='#fff'; ctx.lineWidth=2.5; ctx.fill(); ctx.stroke();
      drawRootLabel(ctx,'#ef4444',`(${solution[0].toFixed(4)}, ${solution[1].toFixed(4)})`,px,py-8,W,false);
    }
  }

  /* Leyenda */
  CURVE_COLORS.forEach((col, i) => {
    ctx.fillStyle=col; ctx.fillRect(10,12+i*18,18,3);
    ctx.fillStyle='#374151'; ctx.font='600 10px "Poppins",sans-serif';
    ctx.textAlign='left'; ctx.textBaseline='middle'; ctx.fillText(CURVE_NAMES[i],32,12+i*18+1.5);
  });
  ctx.fillStyle='#f59e0b'; ctx.fillRect(10,12+2*18,18,3);
  ctx.fillStyle='#374151'; ctx.fillText('Trayectoria iteraciones',32,12+2*18+1.5);
  ctx.textBaseline='alphabetic';

  /* Tooltip hover */
  if (eng.hoverOn && exprs.length >= 2) {
    const tip=document.getElementById('t4Tooltip');
    if (tip) {
      const wx=eng.mouseWorld.x, wy=eng.mouseWorld.y;
      let f1=NaN,f2=NaN;
      try{f1=t4EvalF(exprs[0],vars,[wx,wy]);}catch{}
      try{f2=t4EvalF(exprs[1],vars,[wx,wy]);}catch{}
      if (isFinite(f1)||isFinite(f2)) {
        const parts = [];
        if (isFinite(f1)) parts.push(`f₁(${t3GFmt(wx)},${t3GFmt(wy)}) = ${t3GFmt(f1)}`);
        if (isFinite(f2)) parts.push(`f₂(${t3GFmt(wx)},${t3GFmt(wy)}) = ${t3GFmt(f2)}`);
        tip.innerHTML=parts.join('<br>');
        const {x:pxm,y:pym}=toC(wx,wy);
        const rect=eng.canvas.getBoundingClientRect(),scale=rect.width/eng.canvas.width;
        tip.style.display='block'; tip.style.left=(pxm*scale+14)+'px'; tip.style.top=(Math.max(0,pym*scale-60))+'px';
      } else { tip.style.display='none'; }
    }
  }

  drawCrosshair(toC,W,H);
  drawWatermark(W,H,false);
}

function t4GraphInit(exprs, vars, solution, iterations) {
  Object.assign(t4GState, { exprs, vars, solution, iterations });
  const e = t4Eng.eng;
  /* Vista centrada en la solución */
  if (solution.length >= 2 && isFinite(solution[0])) {
    const cx=solution[0], cy=solution[1], span=Math.max(3,Math.abs(cx)*1.5+2,Math.abs(cy)*1.5+2);
    e.xMin=cx-span; e.xMax=cx+span; e.yMin=cy-span; e.yMax=cy+span;
  } else { e.xMin=-6; e.xMax=6; e.yMin=-6; e.yMax=6; }
  if (!e.canvas) { t4Eng.init(); t4Eng.eng.drawFn=t4GraphDraw; }
  document.getElementById('t4GraphCard').style.display='block';
  t4GraphDraw();
}
function t4GZoom(f){ t4Eng.zoom(f); }
function t4GReset(){ const e=t4Eng.eng;e.xMin=-6;e.xMax=6;e.yMin=-6;e.yMax=6;t4GraphDraw(); }
window.t4GZoom=t4GZoom; window.t4GReset=t4GReset;

/* ── DOMContentLoaded ────────────────────────────────────── */
document.addEventListener('DOMContentLoaded', () => {
  /* Inicializar gráfica T4 */
  t4Eng.init(); t4Eng.eng.drawFn=t4GraphDraw;

  /* Construir UI inicial */
  t4BuildUI();

  /* Cambio de n ecuaciones */
  document.getElementById('t4_n')?.addEventListener('change', t4BuildUI);

  /* Botón resolver */
  document.getElementById('btnT4Resolver')?.addEventListener('click', () => {
    clearAlert('t4Alert');
    document.getElementById('t4Result').innerHTML = '';
    document.getElementById('t4GraphCard').style.display = 'none';

    const n   = parseInt(document.getElementById('t4_n').value) || 2;
    const vars = T4_VARS.slice(0, n);
    const tol  = parseFloat(document.getElementById('t4_tol').value) || 1e-4;
    const maxI = parseInt(document.getElementById('t4_maxiter').value) || 50;

    /* Leer ecuaciones */
    const exprs = [];
    for (let i = 0; i < n; i++) {
      const v = document.getElementById(`t4_eq_${i}`)?.value?.trim();
      if (!v) { showAlert('t4Alert','danger',`Ecuación f${i+1} vacía.`); return; }
      if (checkUpperX(v,'t4Alert')) return;
      exprs.push(v);
    }

    /* Leer vector inicial */
    const x0 = [];
    for (let i = 0; i < n; i++) {
      const v = parseFloat(document.getElementById(`t4_x0_${i}`)?.value);
      if (isNaN(v)) { showAlert('t4Alert','danger',`Valor inicial ${vars[i]}₀ inválido.`); return; }
      x0.push(v);
    }

    try {
      const result = t4NewtonSystems(exprs, vars, x0, tol, maxI);
      t4RenderResult(result, exprs, vars, tol);
      const last = result.iterations.at(-1);
      const conv = last?.converged;
      showAlert('t4Alert', conv?'success':'warning',
        `${conv?'✓ Convergencia':'⚠ Máx. iteraciones'} en ${result.iterations.length} iteraciones. Solución: (${result.solution.map(v=>v.toFixed(6)).join(', ')})`);
      /* Gráfica solo para 2×2 */
      if (n === 2) t4GraphInit(exprs, vars, result.solution, result.iterations);
    } catch(e) {
      showAlert('t4Alert', 'danger', 'Error: ' + e.message);
    }
  });
});

/* ══════════════════════════════════════════════════════════════
   MODO OSCURO — Dark Mode
   Botón 🌙/☀️ en el header. Persiste en localStorage.
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {
  const btn  = document.getElementById('btnDarkMode');
  const body = document.body;

  function applyTheme(dark) {
    if (dark) {
      body.classList.add('dark-mode');
      if (btn) { btn.textContent = '☀️'; btn.title = 'Cambiar a modo claro'; }
    } else {
      body.classList.remove('dark-mode');
      if (btn) { btn.textContent = '🌙'; btn.title = 'Cambiar a modo oscuro'; }
    }
    /* Redibujar gráficas */
    try { if (typeof graphDraw    === 'function') graphDraw();    } catch(e) {}
    try { if (typeof t1GraphDraw  === 'function') t1GraphDraw();  } catch(e) {}
    /* T3: Müller, Bairstow, Horner */
    try { if (typeof m3Draw       === 'function') m3Draw();       } catch(e) {}
    try { if (typeof bsGraphDraw  === 'function') bsGraphDraw();  } catch(e) {}
    try { if (typeof nhGraphDraw  === 'function') nhGraphDraw();  } catch(e) {}
    /* T4: Newton-Raphson Sistemas */
    try { if (typeof t4GraphDraw  === 'function') t4GraphDraw();  } catch(e) {}
    /* T5: Sistemas Lineales Iterativos */
    try { if (typeof t5DrawGraph  === 'function') t5DrawGraph();  } catch(e) {}
    /* T6: Ajuste de Curvas */
    try { if (typeof t6DrawLin    === 'function') t6DrawLin();    } catch(e) {}
    /* T7: Interpolación Polinomial */
    try { if (typeof t7DrawGraph  === 'function') t7DrawGraph();  } catch(e) {}
    /* T7 Splines */
    try { if (typeof splDrawGraph  === 'function') splDrawGraph();  } catch(e) {}
    /* T8: Diferenciación — sin gráfica, nada que redibujar */
    /* T11: Métodos de un paso EDO */
    try { if (typeof t11DrawGraph === 'function') t11DrawGraph(); } catch(e) {}
    /* T12: Sistemas de EDO */
    try { if (typeof t12DrawGraphT === 'function') t12DrawGraphT(); } catch(e) {}
    try { if (typeof t12DrawGraphFase === 'function') t12DrawGraphFase(); } catch(e) {}
  }

  /* Cargar preferencia guardada */
  const saved = localStorage.getItem('numerix-dark');
  if (saved === 'true') applyTheme(true);
  else applyTheme(false);

  /* Toggle al hacer clic */
  if (btn) {
    btn.addEventListener('click', () => {
      const isDark = body.classList.contains('dark-mode');
      applyTheme(!isDark);
      localStorage.setItem('numerix-dark', String(!isDark));
    });
  }
});


/* ══════════════════════════════════════════════════════════════
   TEMA 5 — SISTEMAS LINEALES ITERATIVOS
   Jacobi y Gauss-Seidel
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

/* ── Variables de color T5 ─────────────────────────────────── */
const T5_COLOR  = '#db2777';
const T5_LIGHT  = '#fce7f3';
const T5_DARK   = '#9d174d';
const T5_VARS   = ['x₁','x₂','x₃','x₄','x₅'];

/* ── Estado T5 ─────────────────────────────────────────────── */
const t5State = {
  last: null   // { A, b, x0, n, method, tol, maxIter, iters, solution, converged }
};

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS NUMÉRICOS
══════════════════════════════════════════════════════════════ */

/**
 * Verifica si la matriz es diagonal dominante.
 * Retorna array de { row, lhs, rhs, ok } por cada fila.
 */
function t5DiagDominant(A, n) {
  return Array.from({ length: n }, (_, i) => {
    const lhs = Math.abs(A[i][i]);
    const rhs = A[i].reduce((s, v, j) => j !== i ? s + Math.abs(v) : s, 0);
    return { row: i, lhs, rhs, ok: lhs > rhs };
  });
}

/**
 * Método de Jacobi
 * Usa todos los valores x^(k) para calcular x^(k+1)
 */
function t5Jacobi(A, b, x0, tol, maxIter, n) {
  let x = [...x0];
  const iters = [];

  for (let k = 0; k < maxIter; k++) {
    const xNew = new Array(n).fill(0);

    for (let i = 0; i < n; i++) {
      let sum = 0;
      for (let j = 0; j < n; j++) {
        if (j !== i) sum += A[i][j] * x[j];   // usa x^(k) completo
      }
      xNew[i] = (b[i] - sum) / A[i][i];
    }

    // Error absoluto máximo entre componentes
    const ea = xNew.map((xi, i) => Math.abs(xi - x[i]));
    const eaMax = Math.max(...ea);
    const erPct = xNew.map((xi, i) =>
      Math.abs(xi) > 1e-14 ? (Math.abs(xi - x[i]) / Math.abs(xi)) * 100 : null
    );

    iters.push({
      k: k + 1,
      xPrev: [...x],
      xNew:  [...xNew],
      ea,
      eaMax,
      erPct,
      converged: eaMax < tol
    });

    x = xNew;
    if (eaMax < tol) break;
  }

  return { solution: x, iters };
}

/**
 * Método de Gauss-Seidel
 * Usa los x^(k+1) ya calculados en la misma iteración
 */
function t5GaussSeidel(A, b, x0, tol, maxIter, n) {
  let x = [...x0];
  const iters = [];

  for (let k = 0; k < maxIter; k++) {
    const xPrevSnap = [...x];   // snapshot para guardar en tabla
    const xNew = [...x];        // se va actualizando in-place

    for (let i = 0; i < n; i++) {
      let sum = 0;
      for (let j = 0; j < n; j++) {
        if (j !== i) sum += A[i][j] * xNew[j];  // usa valores más recientes
      }
      xNew[i] = (b[i] - sum) / A[i][i];
    }

    const ea = xNew.map((xi, i) => Math.abs(xi - xPrevSnap[i]));
    const eaMax = Math.max(...ea);
    const erPct = xNew.map((xi, i) =>
      Math.abs(xi) > 1e-14 ? (Math.abs(xi - xPrevSnap[i]) / Math.abs(xi)) * 100 : null
    );

    iters.push({
      k: k + 1,
      xPrev: xPrevSnap,
      xNew:  [...xNew],
      ea,
      eaMax,
      erPct,
      converged: eaMax < tol
    });

    x = [...xNew];
    if (eaMax < tol) break;
  }

  return { solution: x, iters };
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO
══════════════════════════════════════════════════════════════ */

/** Renderiza la verificación de diagonal dominante */
function t5RenderDomCheck(checks, n) {
  const card = document.getElementById('t5DomCard');
  const cont = document.getElementById('t5DomContent');
  if (!card || !cont) return;
  card.style.display = 'block';

  const allOk = checks.every(c => c.ok);
  const statusColor = allOk ? '#065f46' : '#92400e';
  const statusBg    = allOk ? '#d1fae5' : '#fef3c7';
  const statusBorder= allOk ? '#6ee7b7' : '#fcd34d';
  const statusIcon  = allOk ? '✓' : '⚠';
  const statusText  = allOk
    ? 'La matriz es diagonal dominante — convergencia garantizada'
    : 'La matriz NO es estrictamente diagonal dominante — puede converger de todas formas, pero no está garantizado';

  let html = `
    <div style="display:flex;align-items:center;gap:.75rem;padding:.75rem 1.25rem;margin-bottom:1rem;
                background:${statusBg};border:1.5px solid ${statusBorder};border-radius:var(--radius-sm);">
      <span style="font-size:1.3rem;">${statusIcon}</span>
      <span style="font-family:var(--font-main);font-size:.85rem;font-weight:600;color:${statusColor};">${statusText}</span>
    </div>
    <div style="overflow-x:auto;padding:0 1.25rem 1.25rem;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.8rem;">
      <thead>
        <tr style="background:${T5_LIGHT};">
          <th style="padding:.5rem .75rem;text-align:left;color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Fila</th>
          <th style="padding:.5rem .75rem;text-align:center;color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">|a<sub>ii</sub>|</th>
          <th style="padding:.5rem .75rem;text-align:center;color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Σ<sub>j≠i</sub>|a<sub>ij</sub>|</th>
          <th style="padding:.5rem .75rem;text-align:center;color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">¿Domina?</th>
        </tr>
      </thead>
      <tbody>`;

  checks.forEach(c => {
    const rowBg = c.ok ? '' : 'background:#fef9c3;';
    html += `<tr style="${rowBg}">
      <td style="padding:.45rem .75rem;border-bottom:1px solid var(--border);">
        <strong>Ecuación ${c.row + 1}</strong> (a<sub>${c.row+1}${c.row+1}</sub>)
      </td>
      <td style="padding:.45rem .75rem;text-align:center;border-bottom:1px solid var(--border);">
        ${c.lhs.toFixed(6)}
      </td>
      <td style="padding:.45rem .75rem;text-align:center;border-bottom:1px solid var(--border);">
        ${c.rhs.toFixed(6)}
      </td>
      <td style="padding:.45rem .75rem;text-align:center;border-bottom:1px solid var(--border);">
        <span style="font-weight:700;color:${c.ok ? '#065f46' : '#b45309'};">
          ${c.ok ? '✓ Sí' : '✗ No'}
        </span>
      </td>
    </tr>`;
  });

  html += `</tbody></table></div>`;
  cont.innerHTML = html;
}

/** Renderiza las fórmulas despejadas del método */
function t5RenderFormulas(A, b, n, method) {
  const card = document.getElementById('t5FormulasCard');
  const cont = document.getElementById('t5FormulasContent');
  if (!card || !cont) return;
  card.style.display = 'block';

  const methodLabel = method === 'jacobi' ? 'Jacobi' : 'Gauss-Seidel';
  let html = `<div style="padding:1rem 1.25rem;">
    <div style="font-family:var(--font-main);font-size:.78rem;font-weight:600;
                color:${T5_DARK};text-transform:uppercase;letter-spacing:.4px;margin-bottom:1rem;">
      ${methodLabel} — Ecuaciones despejadas
    </div>`;

  for (let i = 0; i < n; i++) {
    // Construir el string de la suma
    let sumStr = '';
    for (let j = 0; j < n; j++) {
      if (j === i) continue;
      const coef = A[i][j];
      if (coef === 0) continue;
      const sign  = sumStr === '' ? (coef < 0 ? '−' : '') : (coef < 0 ? ' − ' : ' + ');
      const absV  = Math.abs(coef);
      const coefStr = Number.isInteger(absV) ? String(absV) : absV.toFixed(4).replace(/\.?0+$/, '');

      let xLabel;
      if (method === 'gauss' && j < i) {
        xLabel = `x<sub>${j+1}</sub><sup>(k+1)</sup>`;
      } else {
        xLabel = `x<sub>${j+1}</sub><sup>(k)</sup>`;
      }
      sumStr += `${sign}${coefStr}·${xLabel}`;
    }

    const aii    = A[i][i];
    const aiiStr = Number.isInteger(Math.abs(aii)) ? String(aii) : aii.toFixed(4).replace(/\.?0+$/, '');
    const biStr  = Number.isInteger(Math.abs(b[i]))  ? String(b[i])  : b[i].toFixed(4).replace(/\.?0+$/, '');
    const bSign  = b[i] < 0 ? `(${biStr})` : biStr;

    const inner = sumStr
      ? `<span style="color:#4b5563;">${bSign}</span> <span style="color:#6b7280;font-size:.85em;">−</span> <span style="color:#4b5563;">(${sumStr})</span>`
      : `<span style="color:#4b5563;">${bSign}</span>`;

    html += `
      <div class="t5-formula-row">
        <div class="t5-formula-lhs">
          x<sub>${i+1}</sub><sup>(k+1)</sup> =
        </div>
        <div class="t5-formula-frac">
          <div class="t5-frac-num">${inner}</div>
          <div class="t5-frac-line"></div>
          <div class="t5-frac-den">${aiiStr}</div>
        </div>
      </div>`;
  }

  html += `</div>`;
  cont.innerHTML = html;
}

/** Renderiza la tabla de iteraciones */
function t5RenderTable(iters, n, method) {
  const card = document.getElementById('t5TableCard');
  const cont = document.getElementById('t5TableContent');
  const sub  = document.getElementById('t5TableSubtitle');
  if (!card || !cont) return;
  card.style.display = 'block';

  const conv  = iters.at(-1)?.converged;
  const label = method === 'jacobi' ? 'Jacobi' : 'Gauss-Seidel';
  if (sub) sub.textContent = `${label} — ${iters.length} iteraciones · ${conv ? 'Convergió' : 'Máx. iteraciones alcanzado'}`;

  // Encabezado
  let hdr = `<tr>
    <th style="background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">k</th>`;
  for (let i = 0; i < n; i++) {
    hdr += `<th style="background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">
      x<sub>${i+1}</sub><sup>(k)</sup></th>`;
  }
  for (let i = 0; i < n; i++) {
    hdr += `<th style="background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">
      x<sub>${i+1}</sub><sup>(k+1)</sup></th>`;
  }
  hdr += `<th style="background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Ea máx</th>
    <th style="background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Er% máx</th>
  </tr>`;

  // Filas
  let bdy = '';
  iters.forEach(it => {
    const rowStyle = it.converged
      ? 'background:linear-gradient(90deg,#f0fdf4,#dcfce7);font-weight:600;'
      : '';
    bdy += `<tr style="${rowStyle}">
      <td style="text-align:center;font-weight:700;color:${T5_COLOR};">${it.k}</td>`;

    // xPrev
    it.xPrev.forEach(v => {
      bdy += `<td style="font-family:var(--font-mono);font-size:.78rem;">${v.toFixed(8)}</td>`;
    });
    // xNew
    it.xNew.forEach((v, i) => {
      const changed = Math.abs(v - it.xPrev[i]) > 1e-10;
      bdy += `<td style="font-family:var(--font-mono);font-size:.78rem;color:${changed ? T5_COLOR : 'inherit'};">
        ${v.toFixed(8)}</td>`;
    });

    // Ea max
    bdy += `<td style="font-family:var(--font-mono);font-size:.78rem;">${it.eaMax.toExponential(4)}</td>`;
    // Er% max
    const erMax = Math.max(...it.erPct.map(v => v ?? 0));
    bdy += `<td style="font-family:var(--font-mono);font-size:.78rem;">${erMax.toFixed(4)}%</td>`;

    if (it.converged) {
      bdy += `</tr><tr style="background:linear-gradient(90deg,#f0fdf4,#dcfce7);">
        <td colspan="${1 + 2*n + 2}" style="text-align:center;font-family:var(--font-main);
            font-size:.78rem;color:#065f46;font-weight:700;padding:.4rem;">
          ✓ Convergencia alcanzada — Ea = ${it.eaMax.toExponential(4)} &lt; tolerancia
        </td></tr>`;
    } else {
      bdy += `</tr>`;
    }
  });

  cont.innerHTML = `<table style="width:100%;border-collapse:collapse;font-size:.8rem;">
    <thead>${hdr}</thead><tbody>${bdy}</tbody></table>`;
}

/** Renderiza la solución final con verificación Ax=b */
function t5RenderResult(A, b, x, n, method, tol, iters) {
  const card = document.getElementById('t5ResultCard');
  const cont = document.getElementById('t5ResultContent');
  const sub  = document.getElementById('t5ResultSubtitle');
  if (!card || !cont) return;
  card.style.display = 'block';

  const conv  = iters.at(-1)?.converged;
  const label = method === 'jacobi' ? 'Jacobi' : 'Gauss-Seidel';
  const COLORS = [T5_COLOR,'#4f46e5','#10b981','#f59e0b','#0ea5e9'];

  if (sub) sub.textContent = `${label} — ${conv ? '✓ Convergencia' : '⚠ Máx. iteraciones'} en ${iters.length} iter.`;

  // Tarjetas de solución
  let solCards = `<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(140px,1fr));gap:.75rem;padding:1.25rem 1.25rem .75rem;">`;
  x.forEach((xi, i) => {
    solCards += `
      <div style="border-radius:var(--radius-sm);border:2px solid ${COLORS[i%COLORS.length]}33;
                  border-left:5px solid ${COLORS[i%COLORS.length]};padding:.875rem 1rem;
                  background:var(--gray-50);">
        <div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;
                    color:${COLORS[i%COLORS.length]};text-transform:uppercase;margin-bottom:.35rem;">
          x<sub>${i+1}</sub>
        </div>
        <div style="font-family:var(--font-mono);font-size:1.05rem;font-weight:700;
                    color:${COLORS[i%COLORS.length]};">${xi.toFixed(10)}</div>
      </div>`;
  });
  solCards += `</div>`;

  // Verificación Ax = b
  let verif = `<div style="padding:.5rem 1.25rem 1.25rem;">
    <div style="font-family:var(--font-main);font-size:.78rem;font-weight:700;
                color:var(--gray-600);text-transform:uppercase;letter-spacing:.4px;margin-bottom:.625rem;">
      Verificación Ax = b
    </div>
    <div style="overflow-x:auto;">
    <table style="border-collapse:collapse;font-family:var(--font-mono);font-size:.78rem;">
      <thead><tr>
        <th style="padding:.4rem .65rem;background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Ecuación</th>
        <th style="padding:.4rem .65rem;background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">A·x (calculado)</th>
        <th style="padding:.4rem .65rem;background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">b (esperado)</th>
        <th style="padding:.4rem .65rem;background:${T5_LIGHT};color:${T5_DARK};border-bottom:2px solid ${T5_COLOR}33;">Residuo |Ax−b|</th>
      </tr></thead><tbody>`;

  for (let i = 0; i < n; i++) {
    const ax  = A[i].reduce((s, aij, j) => s + aij * x[j], 0);
    const res = Math.abs(ax - b[i]);
    const ok  = res < tol * 100;
    verif += `<tr>
      <td style="padding:.35rem .65rem;border-bottom:1px solid var(--border);">f<sub>${i+1}</sub></td>
      <td style="padding:.35rem .65rem;border-bottom:1px solid var(--border);">${ax.toFixed(8)}</td>
      <td style="padding:.35rem .65rem;border-bottom:1px solid var(--border);">${b[i].toFixed(8)}</td>
      <td style="padding:.35rem .65rem;border-bottom:1px solid var(--border);color:${ok?'#065f46':'#b45309'};">
        ${res.toExponential(4)} ${ok?'✓':'⚠'}
      </td></tr>`;
  }
  verif += `</tbody></table></div></div>`;

  cont.innerHTML = solCards + verif;
}

/** Gráfica de convergencia (error máximo por iteración, escala log) */
function t5DrawGraph() {
  const canvas = document.getElementById('t5Canvas');
  if (!canvas || !t5State.last) return;
  const { iters, n } = t5State.last;
  if (!iters || iters.length === 0) return;

  const isDark = document.body.classList.contains('dark-mode');
  const W = canvas.parentElement.clientWidth || 700;
  canvas.width  = W;
  canvas.height = Math.max(280, Math.round(W * 0.38));
  const H = canvas.height;
  const ctx = canvas.getContext('2d');
  const PAD = { top: 28, right: 28, bottom: 48, left: 72 };
  const PW = W - PAD.left - PAD.right;
  const PH = H - PAD.top  - PAD.bottom;

  // Fondo
  ctx.fillStyle = isDark ? '#0f172a' : '#ffffff';
  ctx.fillRect(0, 0, W, H);

  // Datos: eaMax por iteración
  const eaVals = iters.map(it => it.eaMax);
  const logMin = Math.log10(Math.min(...eaVals.filter(v => v > 0)) * 0.5);
  const logMax = Math.log10(Math.max(...eaVals) * 2);
  const ks     = iters.map(it => it.k);
  const kMin   = 0, kMax = ks.at(-1) + 1;

  const toX = k  => PAD.left + ((k - kMin) / (kMax - kMin)) * PW;
  const toY = ea => PAD.top  + (1 - (Math.log10(Math.max(ea, 1e-20)) - logMin) / (logMax - logMin)) * PH;

  // Grid horizontal (líneas de potencias de 10)
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.08)' : '#f1f5f9';
  ctx.lineWidth = 1;
  for (let p = Math.floor(logMin); p <= Math.ceil(logMax); p++) {
    const py = toY(Math.pow(10, p));
    if (py < PAD.top || py > PAD.top + PH) continue;
    ctx.beginPath(); ctx.moveTo(PAD.left, py); ctx.lineTo(PAD.left + PW, py); ctx.stroke();
    // Label
    ctx.fillStyle = isDark ? 'rgba(148,163,184,.6)' : '#94a3b8';
    ctx.font = '10px "JetBrains Mono",monospace';
    ctx.textAlign = 'right';
    ctx.fillText(`10^${p}`, PAD.left - 6, py + 4);
  }

  // Grid vertical
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.08)' : '#f1f5f9';
  for (let k = 1; k <= kMax; k++) {
    const px = toX(k);
    ctx.beginPath(); ctx.moveTo(px, PAD.top); ctx.lineTo(px, PAD.top + PH); ctx.stroke();
  }

  // Ejes
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.3)' : '#cbd5e1';
  ctx.lineWidth = 1.5;
  ctx.beginPath(); ctx.moveTo(PAD.left, PAD.top); ctx.lineTo(PAD.left, PAD.top + PH); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(PAD.left, PAD.top + PH); ctx.lineTo(PAD.left + PW, PAD.top + PH); ctx.stroke();

  // Línea de tolerancia
  const tolLine = toY(t5State.last.tol);
  if (tolLine >= PAD.top && tolLine <= PAD.top + PH) {
    ctx.save();
    ctx.strokeStyle = '#10b981'; ctx.lineWidth = 1.5; ctx.setLineDash([5,4]);
    ctx.beginPath(); ctx.moveTo(PAD.left, tolLine); ctx.lineTo(PAD.left + PW, tolLine); ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = '#10b981'; ctx.font = '10px "Poppins",sans-serif'; ctx.textAlign = 'left';
    ctx.fillText('Tolerancia', PAD.left + 4, tolLine - 4);
    ctx.restore();
  }

  // Curva de error máximo
  ctx.beginPath(); ctx.strokeStyle = T5_COLOR; ctx.lineWidth = 2.5;
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  iters.forEach((it, idx) => {
    const px = toX(it.k), py = toY(it.eaMax);
    if (idx === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
  });
  ctx.stroke();

  // Puntos
  iters.forEach(it => {
    const px = toX(it.k), py = toY(it.eaMax);
    ctx.beginPath();
    ctx.arc(px, py, it.converged ? 5 : 3.5, 0, Math.PI * 2);
    ctx.fillStyle = it.converged ? '#10b981' : T5_COLOR;
    ctx.fill();
  });

  // Etiquetas eje X
  ctx.fillStyle = isDark ? 'rgba(148,163,184,.6)' : '#94a3b8';
  ctx.font = '10px "JetBrains Mono",monospace';
  ctx.textAlign = 'center';
  for (let k = 1; k <= kMax - 1; k++) {
    if (kMax > 20 && k % 5 !== 0) continue;
    ctx.fillText(k, toX(k), PAD.top + PH + 16);
  }

  // Títulos de ejes
  ctx.fillStyle = isDark ? '#94a3b8' : '#64748b';
  ctx.font = '11px "Poppins",sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText('Iteración (k)', PAD.left + PW / 2, H - 8);

  ctx.save();
  ctx.translate(14, PAD.top + PH / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText('Error Ea (log)', 0, 0);
  ctx.restore();

  // Watermark
  ctx.fillStyle = isDark ? 'rgba(219,39,119,.15)' : 'rgba(148,163,184,.4)';
  ctx.font = '600 11px "Poppins",sans-serif';
  ctx.textAlign = 'right'; ctx.textBaseline = 'bottom';
  ctx.fillText('NUMERIX © 2026', W - 10, H - 8);
  ctx.textBaseline = 'alphabetic';
}
window.t5DrawGraph = t5DrawGraph;

function t5GReset() { t5DrawGraph(); }
window.t5GReset = t5GReset;

/* ══════════════════════════════════════════════════════════════
   CONSTRUCCIÓN DE UI DINÁMICA
══════════════════════════════════════════════════════════════ */

function t5BuildUI() {
  const n = parseInt(document.getElementById('t5_n')?.value) || 3;

  // Matriz A
  const mCont = document.getElementById('t5-matrix-container');
  if (mCont) {
    let html = `<div style="overflow-x:auto;"><table class="t5-matrix-table">`;
    for (let i = 0; i < n; i++) {
      html += `<tr>`;
      for (let j = 0; j < n; j++) {
        html += `<td><input type="number" id="t5_a_${i}_${j}"
          class="t5-matrix-input" value="0" step="any"
          style="${i === j ? 'border-color:'+T5_COLOR+';font-weight:700;' : ''}" /></td>`;
      }
      html += `</tr>`;
    }
    html += `</table></div>`;
    mCont.innerHTML = html;
  }

  // Vector b
  const bCont = document.getElementById('t5-b-container');
  if (bCont) {
    bCont.innerHTML = Array.from({ length: n }, (_, i) => `
      <div class="form-group" style="min-width:100px;max-width:130px;">
        <label>b<sub>${i+1}</sub></label>
        <input type="number" id="t5_b_${i}" value="0" step="any" />
      </div>`).join('');
  }

  // Vector x0
  const x0Cont = document.getElementById('t5-x0-container');
  if (x0Cont) {
    x0Cont.innerHTML = Array.from({ length: n }, (_, i) => `
      <div class="form-group" style="min-width:100px;max-width:130px;">
        <label>x<sub>${i+1}</sub><sup>(0)</sup></label>
        <input type="number" id="t5_x0_${i}" value="0" step="any" />
      </div>`).join('');
  }

  // Ocultar resultados previos
  ['t5DomCard','t5FormulasCard','t5TableCard','t5ResultCard','t5GraphCard'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.style.display = 'none';
  });
  const dl = document.getElementById('t5-download-bar');
  if (dl) dl.style.display = 'none';
}

/* ══════════════════════════════════════════════════════════════
   LECTURA DE INPUTS
══════════════════════════════════════════════════════════════ */

function t5ReadMatrix() {
  const n = parseInt(document.getElementById('t5_n')?.value) || 3;
  const A = [];
  for (let i = 0; i < n; i++) {
    A.push([]);
    for (let j = 0; j < n; j++) {
      const v = parseFloat(document.getElementById(`t5_a_${i}_${j}`)?.value);
      A[i].push(isNaN(v) ? 0 : v);
    }
  }
  return A;
}

function t5ReadVector(prefix, n) {
  return Array.from({ length: n }, (_, i) => {
    const v = parseFloat(document.getElementById(`${prefix}_${i}`)?.value);
    return isNaN(v) ? 0 : v;
  });
}

/* ══════════════════════════════════════════════════════════════
   EJEMPLO DE CLASE (sistema 3×3 de las fotos)
   A = [[10,-1,0],[-1,10,-2],[0,-2,10]]  b = [9,7,6]  x0 = [0,0,0]
══════════════════════════════════════════════════════════════ */

function t5LoadExample() {
  const A = [[10,-1,0],[-1,10,-2],[0,-2,10]];
  const b = [9,7,6];

  document.getElementById('t5_n').value = '3';
  t5BuildUI();

  A.forEach((row, i) => row.forEach((v, j) => {
    const el = document.getElementById(`t5_a_${i}_${j}`);
    if (el) el.value = v;
  }));
  b.forEach((v, i) => {
    const el = document.getElementById(`t5_b_${i}`);
    if (el) el.value = v;
  });

  showAlert('t5Alert','info','📋 Ejemplo de clase cargado — sistema 3×3 del 08/05/26. Presiona ▶ Resolver para ver el procedimiento.');
}

/* ══════════════════════════════════════════════════════════════
   BOTÓN RESOLVER — FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */

document.addEventListener('DOMContentLoaded', () => {

  t5BuildUI();

  document.getElementById('t5_n')?.addEventListener('change', t5BuildUI);

  document.getElementById('btnT5Ejemplo')?.addEventListener('click', () => {
    clearAlert('t5Alert');
    t5LoadExample();
  });

  document.getElementById('btnT5Resolver')?.addEventListener('click', () => {
    clearAlert('t5Alert');

    const n      = parseInt(document.getElementById('t5_n')?.value) || 3;
    const method = document.getElementById('t5_method')?.value || 'jacobi';
    const tol    = parseFloat(document.getElementById('t5_tol')?.value) || 1e-5;
    const maxIter= parseInt(document.getElementById('t5_maxiter')?.value) || 100;

    const A  = t5ReadMatrix();
    const b  = t5ReadVector('t5_b', n);
    const x0 = t5ReadVector('t5_x0', n);

    // Validar diagonal no nula
    for (let i = 0; i < n; i++) {
      if (Math.abs(A[i][i]) < 1e-14) {
        showAlert('t5Alert','danger',
          `El elemento diagonal a<sub>${i+1}${i+1}</sub> = 0. Reordena las ecuaciones para que la diagonal no tenga ceros.`);
        return;
      }
    }

    try {
      // 1. Diagonal dominante
      const domChecks = t5DiagDominant(A, n);
      t5RenderDomCheck(domChecks, n);

      // 2. Fórmulas despejadas
      t5RenderFormulas(A, b, n, method);

      // 3. Iterar
      let result;
      if (method === 'jacobi') {
        result = t5Jacobi(A, b, x0, tol, maxIter, n);
      } else {
        result = t5GaussSeidel(A, b, x0, tol, maxIter, n);
      }

      const { solution, iters } = result;
      const conv = iters.at(-1)?.converged;
      const label = method === 'jacobi' ? 'Jacobi' : 'Gauss-Seidel';

      // 4. Tabla
      t5RenderTable(iters, n, method);

      // 5. Solución
      t5RenderResult(A, b, solution, n, method, tol, iters);

      // 6. Gráfica
      const gc = document.getElementById('t5GraphCard');
      if (gc) gc.style.display = 'block';

      // Guardar estado
      t5State.last = { A, b, x0, n, method, tol, maxIter, iters, solution, converged: conv };

      setTimeout(() => {
        t5DrawGraph();
        const dl = document.getElementById('t5-download-bar');
        if (dl) dl.style.display = 'block';
      }, 50);

      showAlert('t5Alert', conv ? 'success' : 'warning',
        `${conv ? '✓' : '⚠'} ${label}: ${conv ? 'Convergencia' : 'Máx. iteraciones'} en ${iters.length} iteraciones · ` +
        `Solución: (${solution.map(v => v.toFixed(6)).join(', ')})`);

    } catch(e) {
      showAlert('t5Alert','danger','Error: ' + e.message);
    }
  });

  // Redibujar gráfica T5 al cambiar tamaño
  window.addEventListener('resize', () => {
    if (t5State.last) t5DrawGraph();
  });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T5
══════════════════════════════════════════════════════════════ */
// Se integra en el objeto numerixExport después de su definición
(function patchT5Export() {
  document.addEventListener('DOMContentLoaded', () => {
    if (typeof numerixExport === 'undefined') return;
    numerixExport.t5 = function() {
      const d = t5State.last;
      if (!d) { alert('Ejecuta el método primero para generar datos.'); return; }

      const { A, b, solution, iters, n, method, tol } = d;
      const label = method === 'jacobi' ? 'Jacobi' : 'Gauss-Seidel';
      const wb = XLSX.utils.book_new();

      /* ── Hoja 1: Información general ── */
      const info = [
        ['NUMERIX — Sistemas Lineales Iterativos', '', '© 2026 Fernando Granja & Alejandra Tinoco'],
        [],
        ['Método:', label],
        ['Tamaño:', `${n} × ${n}`],
        ['Tolerancia:', tol],
        ['Iteraciones:', iters.length],
        ['Convergió:', iters.at(-1)?.converged ? 'Sí' : 'No'],
        [],
        ['SOLUCIÓN'],
        ...solution.map((v, i) => [`x${i+1}`, v]),
        [],
        ['MATRIZ A'],
        ...A.map((row, i) => [`Fila ${i+1}`, ...row]),
        [],
        ['VECTOR b'],
        ...b.map((v, i) => [`b${i+1}`, v]),
      ];
      XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet(info), 'Resumen');

      /* ── Hoja 2: Tabla de iteraciones ── */
      const hdr = ['k', ...Array.from({length:n},(_,i)=>`x${i+1}(k)`),
                        ...Array.from({length:n},(_,i)=>`x${i+1}(k+1)`),
                        'Ea_max', 'Er%_max'];
      const rows = iters.map(it => {
        const erMax = Math.max(...it.erPct.map(v => v ?? 0));
        return [it.k, ...it.xPrev, ...it.xNew, it.eaMax, erMax];
      });
      XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet([hdr, ...rows]), 'Iteraciones');

      XLSX.writeFile(wb, `NUMERIX_T5_${label}_${n}x${n}.xlsx`);
    };
    numerixExport.showT5Bar = function() {
      const b = document.getElementById('t5-download-bar');
      if (b) b.style.display = 'block';
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 6 — AJUSTE DE CURVAS DISCRETAS
   Regresión Lineal Simple · Regresión Polinomial Cuadrática
   Método de Mínimos Cuadrados Ordinarios
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T6_COLOR  = '#059669';   /* verde esmeralda */
const T6_LIGHT  = '#d1fae5';
const T6_DARK   = '#065f46';
const T6_ACCENT = '#0ea5e9';   /* azul para recta */

/* ── Estado global T6 ───────────────────────────────────────── */
const t6State = {
  data:    [],          // [{x, y}]
  lineal:  null,        // resultado regresión lineal
  pol:     null,        // resultado regresión polinomial
  mode:    'lineal',
  labelX:  'X',
  labelY:  'Y',
  /* motor gráfica lineal */
  graph: {
    canvas: null, ctx: null,
    xMin:-1, xMax:10, yMin:-1, yMax:15,
    dragging:false, lastMouse:{x:0,y:0},
    mouseWorld:{x:0,y:0}, hoverOn:false,
    drawFn: null,
  }
};

/* ══════════════════════════════════════════════════════════════
   NAVEGACIÓN INTERNA T6
══════════════════════════════════════════════════════════════ */
function t6GoTo(secId) {
  document.querySelectorAll('.t6-sec').forEach(s => s.style.display = 'none');
  document.querySelectorAll('.t6-nav').forEach(n => n.classList.remove('active'));
  const sec = document.getElementById(secId);
  if (sec) sec.style.display = 'block';
  document.querySelectorAll(`[data-t6="${secId}"]`).forEach(el => el.classList.add('active'));
  /* Mostrar download bar si ya hay resultados calculados y no estamos en la pantalla de datos */
  const dl = document.getElementById('t6-download-bar');
  if (dl && dl.dataset.ready === '1' && secId !== 't6-input') {
    dl.style.display = 'block';
  }
}
window.t6GoTo = t6GoTo;

/* ══════════════════════════════════════════════════════════════
   TABLA DE DATOS DINÁMICA
══════════════════════════════════════════════════════════════ */
function t6RenderDataTable() {
  const tbody = document.getElementById('t6DataBody');
  if (!tbody) return;
  const n = t6State.data.length;
  tbody.innerHTML = t6State.data.map((pt, i) => `
    <tr>
      <td style="text-align:center;font-family:var(--font-mono);font-size:.8rem;
                 color:var(--gray-400);">${i + 1}</td>
      <td><input type="number" class="t6-cell-input" id="t6_x_${i}"
          value="${pt.x}" step="any" onchange="t6UpdateCell(${i},'x',this.value)" /></td>
      <td><input type="number" class="t6-cell-input" id="t6_y_${i}"
          value="${pt.y}" step="any" onchange="t6UpdateCell(${i},'y',this.value)" /></td>
    </tr>`).join('');
}

function t6UpdateCell(i, field, val) {
  if (!t6State.data[i]) return;
  t6State.data[i][field] = parseFloat(val) || 0;
}
window.t6UpdateCell = t6UpdateCell;

function t6AddRow() {
  t6State.data.push({ x: 0, y: 0 });
  t6RenderDataTable();
}

function t6RemRow() {
  if (t6State.data.length <= 2) return;
  t6State.data.pop();
  t6RenderDataTable();
}

function t6ReadData() {
  /* Leer valores actuales de inputs antes de procesar */
  t6State.data.forEach((pt, i) => {
    const xEl = document.getElementById(`t6_x_${i}`);
    const yEl = document.getElementById(`t6_y_${i}`);
    if (xEl) pt.x = parseFloat(xEl.value) || 0;
    if (yEl) pt.y = parseFloat(yEl.value) || 0;
  });
  return t6State.data.map(p => ({ x: p.x, y: p.y }));
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS — REGRESIÓN LINEAL
══════════════════════════════════════════════════════════════ */
function t6RegLineal(pts) {
  const n   = pts.length;
  const sx  = pts.reduce((s, p) => s + p.x,         0);
  const sy  = pts.reduce((s, p) => s + p.y,         0);
  const sx2 = pts.reduce((s, p) => s + p.x * p.x,   0);
  const sxy = pts.reduce((s, p) => s + p.x * p.y,   0);
  const xm  = sx / n;
  const ym  = sy / n;

  const beta1 = (n * sxy - sx * sy) / (n * sx2 - sx * sx);
  const beta0 = ym - beta1 * xm;

  /* Predicciones y residuos */
  const pred = pts.map(p => ({ x: p.x, y: p.y, yhat: beta0 + beta1 * p.x, e: p.y - (beta0 + beta1 * p.x) }));

  /* R² por fórmula de la maestra */
  const num = pts.reduce((s, p) => s + (p.x - xm) * (p.y - ym), 0);
  const den = Math.sqrt(
    pts.reduce((s, p) => s + (p.x - xm) ** 2, 0) *
    pts.reduce((s, p) => s + (p.y - ym) ** 2, 0)
  );
  const r   = den > 1e-14 ? num / den : 0;
  const R2  = r * r;

  /* Error estándar Sy/x = sqrt(Σ(yi-ŷi)² / (n-2)) */
  const SRR  = pred.reduce((s, p) => s + p.e * p.e, 0);
  const Syx  = Math.sqrt(SRR / (n - 2));

  return { n, sx, sy, sx2, sxy, xm, ym, beta0, beta1, pred, r, R2, SRR, Syx };
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS — REGRESIÓN POLINOMIAL (cuadrática)
   Construye sistema 3×3 y lo resuelve por Gauss-Jordan
══════════════════════════════════════════════════════════════ */
function t6RegPolinomial(pts) {
  const n   = pts.length;
  const sx  = pts.reduce((s, p) => s + p.x,             0);
  const sy  = pts.reduce((s, p) => s + p.y,             0);
  const sx2 = pts.reduce((s, p) => s + p.x**2,          0);
  const sx3 = pts.reduce((s, p) => s + p.x**3,          0);
  const sx4 = pts.reduce((s, p) => s + p.x**4,          0);
  const sxy  = pts.reduce((s, p) => s + p.x   * p.y,    0);
  const sx2y = pts.reduce((s, p) => s + p.x**2 * p.y,   0);

  /* Sistema aumentado [A|b] 3×4 */
  const sums = { n, sx, sy, sx2, sx3, sx4, sxy, sx2y };
  const M0 = [
    [n,   sx,  sx2, sy   ],
    [sx,  sx2, sx3, sxy  ],
    [sx2, sx3, sx4, sx2y ],
  ];

  /* Pasos de Gauss-Jordan con snapshots para mostrar */
  const steps = [];
  const M = M0.map(r => [...r]);
  const snap = () => M.map(r => [...r]);
  steps.push({ label: 'Sistema original (matriz ampliada)', M: snap() });

  /* Eliminación hacia adelante */
  for (let col = 0; col < 3; col++) {
    /* Buscar pivot */
    let pivot = col;
    for (let row = col + 1; row < 3; row++)
      if (Math.abs(M[row][col]) > Math.abs(M[pivot][col])) pivot = row;
    if (pivot !== col) {
      [M[col], M[pivot]] = [M[pivot], M[col]];
      steps.push({ label: `Intercambio f${col+1} ↔ f${pivot+1}`, M: snap() });
    }

    /* Normalizar fila pivot */
    const div = M[col][col];
    if (Math.abs(div) < 1e-14) continue;
    for (let k = col; k < 4; k++) M[col][k] /= div;
    steps.push({ label: `f${col+1} = f${col+1} / ${div.toFixed(4)}`, M: snap() });

    /* Eliminar columna en otras filas */
    for (let row = 0; row < 3; row++) {
      if (row === col) continue;
      const factor = M[row][col];
      if (Math.abs(factor) < 1e-14) continue;
      for (let k = col; k < 4; k++) M[row][k] -= factor * M[col][k];
      steps.push({
        label: `f${row+1} = f${row+1} − (${factor.toFixed(4)})·f${col+1}`,
        M: snap()
      });
    }
  }

  const b0 = M[0][3], b1 = M[1][3], b2 = M[2][3];

  /* Predicciones */
  const pred = pts.map(p => {
    const yhat = b0 + b1 * p.x + b2 * p.x * p.x;
    return { x: p.x, y: p.y, yhat, e: p.y - yhat };
  });

  /* R² = 1 - SR²/Sy² */
  const ym   = sy / n;
  const SR2  = pred.reduce((s, p) => s + p.e ** 2,             0);
  const Sy2  = pts.reduce( (s, p) => s + (p.y - ym) ** 2,     0);
  const R2   = Sy2 > 1e-14 ? 1 - SR2 / Sy2 : 0;

  return { n, sums, M0, steps, b0, b1, b2, pred, R2, SR2, Sy2, ym };
}

/* ══════════════════════════════════════════════════════════════
   FORMATO AUXILIAR
══════════════════════════════════════════════════════════════ */
const t6Fmt = (v, d = 6) => (v === null || v === undefined || isNaN(v)) ? '—' : Number(v).toFixed(d);
const t6Sci = (v, d = 4) => (v === null || v === undefined || isNaN(v)) ? '—' : Number(v).toExponential(d);

function t6FmtCoef(v) {
  /* Para mostrar coeficientes en la ecuación: reduce decimales innecesarios */
  if (Math.abs(v) >= 1000 || (Math.abs(v) < 0.001 && v !== 0)) return v.toExponential(4);
  return parseFloat(v.toFixed(6)).toString();
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — REGRESIÓN LINEAL
══════════════════════════════════════════════════════════════ */

/** Sección 1: Tabla auxiliar (n, x, y, x², xy, sumas) */
function t6RenderLinTabla(res, pts, lx, ly) {
  const sec = document.getElementById('t6-lin-tabla');
  if (!sec) return;

  let html = `
  <div class="page-header">
    <h2>Regresión Lineal — Tabla Auxiliar</h2>
    <p>Cálculo de las sumas necesarias para obtener los coeficientes β₀ y β₁</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t6-icon">📋</div>
      <div>
        <div class="card-title">Tabla de sumas — Método de Mínimos Cuadrados</div>
        <div class="card-subtitle">n = ${res.n} · X: ${lx} · Y: ${ly}</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.8rem;">
      <thead>
        <tr style="background:${T6_LIGHT};">
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">i</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">xᵢ</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">yᵢ</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">xᵢ²</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">xᵢyᵢ</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">(xᵢ−x̄)</th>
          <th style="padding:.5rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;text-align:center;">(yᵢ−ȳ)</th>
        </tr>
      </thead>
      <tbody>`;

  pts.forEach((p, i) => {
    html += `<tr style="${i%2===1?'background:var(--gray-50)':''}">
      <td style="text-align:center;padding:.4rem .75rem;">${i+1}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.x,4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.y,4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.x*p.x,4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.x*p.y,4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.x - res.xm,4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${t6Fmt(p.y - res.ym,4)}</td>
    </tr>`;
  });

  html += `
      <tr style="background:${T6_LIGHT};font-weight:700;border-top:2px solid ${T6_COLOR}33;">
        <td style="padding:.5rem .75rem;color:${T6_DARK};">Σ</td>
        <td style="text-align:right;padding:.5rem .75rem;color:${T6_DARK};">${t6Fmt(res.sx,4)}</td>
        <td style="text-align:right;padding:.5rem .75rem;color:${T6_DARK};">${t6Fmt(res.sy,4)}</td>
        <td style="text-align:right;padding:.5rem .75rem;color:${T6_DARK};">${t6Fmt(res.sx2,4)}</td>
        <td style="text-align:right;padding:.5rem .75rem;color:${T6_DARK};">${t6Fmt(res.sxy,4)}</td>
        <td style="text-align:center;padding:.5rem .75rem;color:var(--gray-400);">—</td>
        <td style="text-align:center;padding:.5rem .75rem;color:var(--gray-400);">—</td>
      </tr>
      <tr style="background:var(--gray-50);">
        <td style="padding:.4rem .75rem;color:var(--gray-500);font-family:var(--font-main);font-size:.75rem;">Media</td>
        <td style="text-align:right;padding:.4rem .75rem;color:var(--gray-600);">x̄ = ${t6Fmt(res.xm,4)}</td>
        <td style="text-align:right;padding:.4rem .75rem;color:var(--gray-600);">ȳ = ${t6Fmt(res.ym,4)}</td>
        <td colspan="4"></td>
      </tr>
    </tbody>
    </table></div>
  </div>
  <div style="margin-top:.75rem;text-align:right;">
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-lin-coef')">
      Siguiente: Coeficientes β →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/** Sección 2: Coeficientes β con sustitución numérica */
function t6RenderLinCoef(res) {
  const sec = document.getElementById('t6-lin-coef');
  if (!sec) return;

  const b1n = res.n * res.sxy - res.sx * res.sy;
  const b1d = res.n * res.sx2 - res.sx * res.sx;

  let html = `
  <div class="page-header">
    <h2>Regresión Lineal — Cálculo de Coeficientes</h2>
    <p>Sustitución de las sumas en las fórmulas de mínimos cuadrados</p>
  </div>

  <!-- β₁ -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T6_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t6-icon">β</div>
      <div><div class="card-title">Pendiente β₁</div></div>
    </div>
    <div class="t6-step-body">
      <div class="t6-paso-formula">
        β₁ = <span class="t6-frac-inline">
          <span class="t6-frac-n">n·Σxᵢyᵢ − (Σxᵢ)(Σyᵢ)</span>
          <span class="t6-frac-d">n·Σxᵢ² − (Σxᵢ)²</span>
        </span>
      </div>
      <div class="t6-paso-sust">
        = <span class="t6-frac-inline">
          <span class="t6-frac-n">${res.n}·${t6Fmt(res.sxy,4)} − (${t6Fmt(res.sx,4)})(${t6Fmt(res.sy,4)})</span>
          <span class="t6-frac-d">${res.n}·${t6Fmt(res.sx2,4)} − (${t6Fmt(res.sx,4)})²</span>
        </span>
        = <span class="t6-frac-inline">
          <span class="t6-frac-n">${t6Fmt(b1n,4)}</span>
          <span class="t6-frac-d">${t6Fmt(b1d,4)}</span>
        </span>
      </div>
      <div class="t6-paso-result">
        β₁ = <strong style="color:${T6_COLOR};font-size:1.15rem;">${t6Fmt(res.beta1,6)}</strong>
      </div>
    </div>
  </div>

  <!-- β₀ -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T6_ACCENT};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${T6_ACCENT};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;font-weight:700;color:#fff;">β</div>
      <div><div class="card-title">Intercepto β₀</div></div>
    </div>
    <div class="t6-step-body">
      <div class="t6-paso-formula">β₀ = Ȳ − β₁ · X̄</div>
      <div class="t6-paso-sust">
        = ${t6Fmt(res.ym,6)} − ${t6Fmt(res.beta1,6)} · ${t6Fmt(res.xm,6)}
        = ${t6Fmt(res.ym,6)} − ${t6Fmt(res.beta1 * res.xm,6)}
      </div>
      <div class="t6-paso-result">
        β₀ = <strong style="color:${T6_ACCENT};font-size:1.15rem;">${t6Fmt(res.beta0,6)}</strong>
      </div>
    </div>
  </div>

  <!-- Modelo final -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T6_LIGHT},#f0fdf4);border:2px solid ${T6_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t6-icon">🎯</div>
      <div><div class="card-title">Modelo de Regresión Lineal</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;font-family:var(--font-mono);font-size:1.05rem;text-align:center;">
      <div style="margin-bottom:.5rem;color:var(--gray-500);font-size:.8rem;font-family:var(--font-main);">Ecuación de la recta de regresión:</div>
      <div style="font-size:1.3rem;font-weight:700;color:${T6_DARK};">
        Ŷ = ${t6FmtCoef(res.beta0)} + ${t6FmtCoef(res.beta1)} · X
      </div>
    </div>
  </div>

  <div style="margin-top:.75rem;display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t6GoTo('t6-lin-tabla')">← Tabla auxiliar</button>
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-lin-error')">Siguiente: Análisis del error →</button>
  </div>`;
  sec.innerHTML = html;
}

/** Sección 3: Análisis del error (R², r, Sy/x, residuos) */
function t6RenderLinError(res, pts) {
  const sec = document.getElementById('t6-lin-error');
  if (!sec) return;

  const rLabel   = Math.abs(res.r) >= 0.9 ? '✓ Altamente significativo' :
                   Math.abs(res.r) >= 0.7 ? '⚠ Moderado' : '✗ Débil';
  const rColor   = Math.abs(res.r) >= 0.9 ? '#065f46' :
                   Math.abs(res.r) >= 0.7 ? '#92400e' : '#991b1b';
  const R2pct    = (res.R2 * 100).toFixed(2);

  let html = `
  <div class="page-header">
    <h2>Regresión Lineal — Análisis del Error</h2>
    <p>Coeficiente de correlación · Coeficiente de determinación · Error estándar · Residuos</p>
  </div>

  <!-- Indicadores principales -->
  <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:.875rem;margin-bottom:1.25rem;">
    <div class="t6-metric-card" style="border-left-color:${T6_COLOR};">
      <div class="t6-metric-label">R² (determinación)</div>
      <div class="t6-metric-val" style="color:${T6_COLOR};">${t6Fmt(res.R2, 6)}</div>
      <div class="t6-metric-sub">El ${R2pct}% de la variabilidad de Y es explicada por X</div>
    </div>
    <div class="t6-metric-card" style="border-left-color:${rColor};">
      <div class="t6-metric-label">r (correlación)</div>
      <div class="t6-metric-val" style="color:${rColor};">${t6Fmt(res.r, 6)}</div>
      <div class="t6-metric-sub">${rLabel} · rango [−1, 1]</div>
    </div>
    <div class="t6-metric-card" style="border-left-color:${T6_ACCENT};">
      <div class="t6-metric-label">Sy/x (error estándar)</div>
      <div class="t6-metric-val" style="color:${T6_ACCENT};">${t6Fmt(res.Syx, 6)}</div>
      <div class="t6-metric-sub">√[Σ(yᵢ−ŷᵢ)² / (n−2)]</div>
    </div>
    <div class="t6-metric-card" style="border-left-color:#8b5cf6;">
      <div class="t6-metric-label">n (observaciones)</div>
      <div class="t6-metric-val" style="color:#8b5cf6;">${res.n}</div>
      <div class="t6-metric-sub">Grados de libertad: n − 2 = ${res.n - 2}</div>
    </div>
  </div>

  <!-- Cálculo detallado R² -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T6_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t6-icon">📊</div>
      <div><div class="card-title">Cálculo de R²</div></div>
    </div>
    <div class="t6-step-body">
      <div class="t6-paso-formula">
        R² = <span class="t6-frac-inline">
          <span class="t6-frac-n">[Σ(xᵢ−x̄)(yᵢ−ȳ)]²</span>
          <span class="t6-frac-d">Σ(xᵢ−x̄)² · Σ(yᵢ−ȳ)²</span>
        </span>
        &nbsp;·&nbsp; r = √R²
      </div>
      <div class="t6-paso-result">
        R² = <strong style="color:${T6_COLOR};">${t6Fmt(res.R2,6)}</strong>
        &nbsp;→&nbsp; r = <strong style="color:${rColor};">${t6Fmt(res.r,6)}</strong>
        &nbsp; ${rLabel}
      </div>
    </div>
  </div>

  <!-- Tabla de residuos -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t6-icon">📋</div>
      <div>
        <div class="card-title">Tabla de residuos — eᵢ = yᵢ − ŷᵢ</div>
        <div class="card-subtitle">ŷᵢ = ${t6FmtCoef(res.beta0)} + ${t6FmtCoef(res.beta1)}·xᵢ</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.8rem;">
      <thead>
        <tr style="background:${T6_LIGHT};">
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">i</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">xᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">yᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">ŷᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">eᵢ = yᵢ−ŷᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">eᵢ²</th>
        </tr>
      </thead>
      <tbody>`;

  let sumE2 = 0;
  res.pred.forEach((p, i) => {
    const e2 = p.e * p.e;
    sumE2 += e2;
    const ec = p.e >= 0 ? T6_COLOR : '#ef4444';
    html += `<tr style="${i%2===1?'background:var(--gray-50)':''}">
      <td style="text-align:center;padding:.35rem .75rem;">${i+1}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.x,4)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.y,4)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.yhat,6)}</td>
      <td style="text-align:right;padding:.35rem .75rem;color:${ec};font-weight:600;">${t6Fmt(p.e,6)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(e2,6)}</td>
    </tr>`;
  });

  html += `
      <tr style="background:${T6_LIGHT};font-weight:700;border-top:2px solid ${T6_COLOR}33;">
        <td colspan="5" style="padding:.45rem .75rem;color:${T6_DARK};">Σeᵢ²  (Suma de residuos cuadrados)</td>
        <td style="text-align:right;padding:.45rem .75rem;color:${T6_DARK};">${t6Fmt(sumE2,6)}</td>
      </tr>
    </tbody></table></div>
  </div>

  <div style="margin-top:.75rem;display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t6GoTo('t6-lin-coef')">← Coeficientes</button>
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-lin-grafica');setTimeout(t6DrawLin,80);">
      Siguiente: Gráfica →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA — REGRESIÓN LINEAL
══════════════════════════════════════════════════════════════ */
function t6InitLinGraph() {
  const g = t6State.graph;
  const c = document.getElementById('t6LinCanvas');
  if (!c || g.canvas) return;
  g.canvas = c; g.ctx = c.getContext('2d');

  const resize = () => {
    const w = c.parentElement.clientWidth || 700;
    c.width = w; c.height = Math.max(340, Math.round(w * 0.52));
    if (g.drawFn) g.drawFn();
  };
  resize();
  window.addEventListener('resize', resize);

  /* Pan */
  c.addEventListener('mousedown', e => { g.dragging = true; g.lastMouse = { x: e.clientX, y: e.clientY }; c.style.cursor = 'grabbing'; });
  c.addEventListener('mouseup',   () => { g.dragging = false; c.style.cursor = 'crosshair'; });
  c.addEventListener('mouseleave',() => {
    g.dragging = false; g.hoverOn = false; c.style.cursor = 'crosshair';
    const tip = document.getElementById('t6LinTooltip'); if (tip) tip.style.display = 'none';
    if (g.drawFn) g.drawFn();
  });
  c.addEventListener('mousemove', e => {
    const rect = c.getBoundingClientRect();
    const px = (e.clientX - rect.left) * (c.width / rect.width);
    const py = (e.clientY - rect.top)  * (c.height / rect.height);
    g.mouseWorld = t6LinToWorld(px, py);
    g.hoverOn = true;
    const coord = document.getElementById('t6LinCoords');
    if (coord) coord.innerHTML = `x = ${g.mouseWorld.x.toFixed(3)} &nbsp; y = ${g.mouseWorld.y.toFixed(3)}`;
    if (g.dragging) {
      const dx = (e.clientX - g.lastMouse.x) / rect.width  * (g.xMax - g.xMin);
      const dy = (e.clientY - g.lastMouse.y) / rect.height * (g.yMax - g.yMin);
      g.xMin -= dx; g.xMax -= dx; g.yMin += dy; g.yMax += dy;
      g.lastMouse = { x: e.clientX, y: e.clientY };
    }
    if (g.drawFn) g.drawFn();
  });
  c.addEventListener('wheel', e => {
    e.preventDefault();
    const f = e.deltaY > 0 ? 1.12 : 0.89;
    const rect = c.getBoundingClientRect();
    const { x: wx, y: wy } = t6LinToWorld(
      (e.clientX - rect.left) * (c.width / rect.width),
      (e.clientY - rect.top) * (c.height / rect.height)
    );
    g.xMin = wx + (g.xMin - wx) * f; g.xMax = wx + (g.xMax - wx) * f;
    g.yMin = wy + (g.yMin - wy) * f; g.yMax = wy + (g.yMax - wy) * f;
    if (g.drawFn) g.drawFn();
  }, { passive: false });

  g.drawFn = t6DrawLin;
}

function t6LinToCanvas(wx, wy) {
  const g = t6State.graph;
  const PAD = { t: 24, r: 24, b: 44, l: 56 };
  const W = g.canvas.width, H = g.canvas.height;
  const PW = W - PAD.l - PAD.r, PH = H - PAD.t - PAD.b;
  return {
    x: PAD.l + (wx - g.xMin) / (g.xMax - g.xMin) * PW,
    y: PAD.t + (1 - (wy - g.yMin) / (g.yMax - g.yMin)) * PH
  };
}

function t6LinToWorld(px, py) {
  const g = t6State.graph;
  const PAD = { t: 24, r: 24, b: 44, l: 56 };
  const W = g.canvas.width, H = g.canvas.height;
  const PW = W - PAD.l - PAD.r, PH = H - PAD.t - PAD.b;
  return {
    x: g.xMin + (px - PAD.l) / PW * (g.xMax - g.xMin),
    y: g.yMin + (1 - (py - PAD.t) / PH) * (g.yMax - g.yMin)
  };
}

function t6DrawLin() {
  const g   = t6State.graph;
  const res = t6State.lineal;
  if (!g.canvas || !res) return;

  const isDark = document.body.classList.contains('dark-mode');
  const W = g.canvas.width, H = g.canvas.height;
  const ctx = g.ctx;
  const PAD = { t: 24, r: 24, b: 44, l: 56 };
  const PW = W - PAD.l - PAD.r, PH = H - PAD.t - PAD.b;
  const toC = (wx, wy) => t6LinToCanvas(wx, wy);
  const niceStep = (range, tgt) => {
    const r = range / tgt, m = Math.pow(10, Math.floor(Math.log10(r)));
    const n = r / m; return (n < 1.5 ? 1 : n < 3.5 ? 2 : n < 7.5 ? 5 : 10) * m;
  };

  ctx.fillStyle = isDark ? '#0f172a' : '#fff';
  ctx.fillRect(0, 0, W, H);

  /* Grid */
  const xSt = niceStep(g.xMax - g.xMin, 10), ySt = niceStep(g.yMax - g.yMin, 8);
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.08)' : '#f1f5f9'; ctx.lineWidth = 1;
  for (let gx = Math.ceil(g.xMin / xSt) * xSt; gx <= g.xMax; gx += xSt) {
    const { x: px } = toC(gx, 0); ctx.beginPath(); ctx.moveTo(px, PAD.t); ctx.lineTo(px, PAD.t + PH); ctx.stroke();
  }
  for (let gy = Math.ceil(g.yMin / ySt) * ySt; gy <= g.yMax; gy += ySt) {
    const { y: py } = toC(0, gy); ctx.beginPath(); ctx.moveTo(PAD.l, py); ctx.lineTo(PAD.l + PW, py); ctx.stroke();
  }

  /* Ejes */
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.3)' : '#cbd5e1'; ctx.lineWidth = 1.5;
  const { y: axY } = toC(0, 0), { x: axX } = toC(0, 0);
  if (g.yMin <= 0 && g.yMax >= 0) { ctx.beginPath(); ctx.moveTo(PAD.l, axY); ctx.lineTo(PAD.l + PW, axY); ctx.stroke(); }
  if (g.xMin <= 0 && g.xMax >= 0) { ctx.beginPath(); ctx.moveTo(axX, PAD.t); ctx.lineTo(axX, PAD.t + PH); ctx.stroke(); }

  /* Labels ejes */
  ctx.fillStyle = isDark ? 'rgba(148,163,184,.6)' : '#94a3b8';
  ctx.font = '10px "JetBrains Mono",monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  const lbY = Math.max(PAD.t + 10, Math.min(PAD.t + PH - 4, axY + 16));
  const lbX = Math.max(PAD.l + 28, Math.min(PAD.l + PW - 4, axX - 8));
  for (let gx = Math.ceil(g.xMin / xSt) * xSt; gx <= g.xMax; gx += xSt) {
    if (Math.abs(gx) < xSt * 0.01) continue;
    const { x: px } = toC(gx, 0); ctx.fillText(gx % 1 === 0 ? gx : gx.toFixed(1), px, lbY);
  }
  ctx.textAlign = 'right';
  for (let gy = Math.ceil(g.yMin / ySt) * ySt; gy <= g.yMax; gy += ySt) {
    if (Math.abs(gy) < ySt * 0.01) continue;
    const { y: py } = toC(0, gy); ctx.fillText(gy % 1 === 0 ? gy : gy.toFixed(1), lbX, py);
  }
  ctx.textBaseline = 'alphabetic';

  /* Recta de regresión */
  const rxMin = toC(g.xMin, res.beta0 + res.beta1 * g.xMin);
  const rxMax = toC(g.xMax, res.beta0 + res.beta1 * g.xMax);
  ctx.beginPath(); ctx.strokeStyle = T6_ACCENT; ctx.lineWidth = 2.5;
  ctx.setLineDash([6, 3]); ctx.moveTo(rxMin.x, rxMin.y); ctx.lineTo(rxMax.x, rxMax.y); ctx.stroke();
  ctx.setLineDash([]);

  /* Puntos de datos */
  t6State.data.forEach((p, i) => {
    const { x: px, y: py } = toC(p.x, p.y);
    if (px < PAD.l - 8 || px > PAD.l + PW + 8 || py < PAD.t - 8 || py > PAD.t + PH + 8) return;
    ctx.beginPath(); ctx.arc(px, py, 5.5, 0, Math.PI * 2);
    ctx.fillStyle = T6_COLOR; ctx.fill();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.5; ctx.stroke();
    /* Línea residuo */
    const { y: pyHat } = toC(p.x, res.beta0 + res.beta1 * p.x);
    ctx.beginPath(); ctx.strokeStyle = 'rgba(239,68,68,.4)'; ctx.lineWidth = 1;
    ctx.setLineDash([2, 2]); ctx.moveTo(px, py); ctx.lineTo(px, pyHat); ctx.stroke();
    ctx.setLineDash([]);
  });

  /* Tooltip hover */
  if (g.hoverOn) {
    const nearest = t6State.data.reduce((best, p) => {
      const { x: px, y: py } = toC(p.x, p.y);
      const d = Math.hypot(px - toC(g.mouseWorld.x, g.mouseWorld.y).x, py - toC(g.mouseWorld.x, g.mouseWorld.y).y);
      return d < best.d ? { d, p } : best;
    }, { d: Infinity, p: null });
    const tip = document.getElementById('t6LinTooltip');
    if (tip && nearest.p && nearest.d < 20) {
      const { x: px, y: py } = toC(nearest.p.x, nearest.p.y);
      tip.style.display = 'block';
      tip.style.left = (px + 12) + 'px'; tip.style.top = (py - 10) + 'px';
      const yhat = res.beta0 + res.beta1 * nearest.p.x;
      tip.innerHTML = `x = ${nearest.p.x}<br>y = ${nearest.p.y}<br>ŷ = ${yhat.toFixed(4)}<br>e = ${(nearest.p.y - yhat).toFixed(4)}`;
    } else if (tip) { tip.style.display = 'none'; }
  }

  /* Leyenda */
  ctx.font = '11px "Poppins",sans-serif'; ctx.textBaseline = 'middle';
  const ly = PAD.t + 14;
  ctx.fillStyle = T6_COLOR; ctx.beginPath(); ctx.arc(PAD.l + 12, ly, 5, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = isDark ? '#e2e8f0' : '#374151'; ctx.textAlign = 'left'; ctx.fillText('Datos (xᵢ, yᵢ)', PAD.l + 22, ly);
  ctx.strokeStyle = T6_ACCENT; ctx.lineWidth = 2; ctx.setLineDash([5, 3]);
  ctx.beginPath(); ctx.moveTo(PAD.l + 140, ly); ctx.lineTo(PAD.l + 162, ly); ctx.stroke();
  ctx.setLineDash([]); ctx.fillStyle = isDark ? '#e2e8f0' : '#374151';
  ctx.fillText(`Ŷ = ${t6FmtCoef(res.beta0)} + ${t6FmtCoef(res.beta1)}·X   R²=${res.R2.toFixed(4)}`, PAD.l + 168, ly);
  ctx.textBaseline = 'alphabetic';

  /* Watermark */
  ctx.fillStyle = isDark ? 'rgba(5,150,105,.15)' : 'rgba(148,163,184,.4)';
  ctx.font = '600 11px "Poppins",sans-serif'; ctx.textAlign = 'right'; ctx.textBaseline = 'bottom';
  ctx.fillText('NUMERIX © 2026', W - 10, H - 8); ctx.textBaseline = 'alphabetic';
}
window.t6DrawLin = t6DrawLin;

function t6LinZoom(f) {
  const g = t6State.graph;
  const cx = (g.xMin + g.xMax) / 2, cy = (g.yMin + g.yMax) / 2;
  const hw = (g.xMax - g.xMin) / 2 * f, hh = (g.yMax - g.yMin) / 2 * f;
  g.xMin = cx - hw; g.xMax = cx + hw; g.yMin = cy - hh; g.yMax = cy + hh;
  t6DrawLin();
}
window.t6LinZoom = t6LinZoom;

function t6LinReset() {
  const pts = t6State.data;
  if (!pts.length) return;
  const xs = pts.map(p => p.x), ys = pts.map(p => p.y);
  const xr = Math.max(...xs) - Math.min(...xs), yr = Math.max(...ys) - Math.min(...ys);
  const g = t6State.graph;
  g.xMin = Math.min(...xs) - xr * 0.15; g.xMax = Math.max(...xs) + xr * 0.15;
  g.yMin = Math.min(...ys) - yr * 0.2;  g.yMax = Math.max(...ys) + yr * 0.2;
  t6DrawLin();
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — REGRESIÓN POLINOMIAL
══════════════════════════════════════════════════════════════ */

/** Sección 5: Sistema 3×3 con sumas */
function t6RenderPolSistema(res) {
  const sec = document.getElementById('t6-pol-sistema');
  if (!sec) return;
  const s = res.sums;

  let html = `
  <div class="page-header">
    <h2>Regresión Polinomial — Sistema 3×3</h2>
    <p>Construcción del sistema de ecuaciones normales para obtener β₀, β₁, β₂</p>
  </div>

  <!-- Tabla de sumas -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t6-icon">∑</div>
      <div><div class="card-title">Sumas necesarias (n = ${s.n})</div></div>
    </div>
    <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:.5rem;padding:1rem 1.25rem;">`;

  const sums = [
    ['n', s.n], ['Σxᵢ', s.sx], ['Σyᵢ', s.sy],
    ['Σxᵢ²', s.sx2], ['Σxᵢ³', s.sx3], ['Σxᵢ⁴', s.sx4],
    ['ΣxᵢYᵢ', s.sxy], ['Σxᵢ²Yᵢ', s.sx2y],
  ];
  sums.forEach(([label, val]) => {
    html += `<div style="background:${T6_LIGHT};border:1px solid ${T6_COLOR}22;border-radius:var(--radius-sm);
                          padding:.6rem .875rem;">
      <div style="font-family:var(--font-main);font-size:.72rem;color:${T6_DARK};font-weight:600;">${label}</div>
      <div style="font-family:var(--font-mono);font-size:.95rem;font-weight:700;color:${T6_DARK};">${t6Fmt(val, 4)}</div>
    </div>`;
  });
  html += `</div></div>

  <!-- Sistema matricial -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T6_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t6-icon">⚙</div>
      <div>
        <div class="card-title">Sistema de ecuaciones normales</div>
        <div class="card-subtitle">Ax = b donde las incógnitas son β₀, β₁, β₂</div>
      </div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-main);font-size:.85rem;color:var(--gray-600);margin-bottom:.75rem;">
        Modelo: Y = β₀ + β₁X + β₂X²
      </div>
      <div style="overflow-x:auto;">
      <table class="t6-system-table">
        <tbody>`;

  const rows = [
    [`${t6Fmt(s.n,0)}·β₀`, `${t6Fmt(s.sx,4)}·β₁`, `${t6Fmt(s.sx2,4)}·β₂`, `= ${t6Fmt(s.sy,4)}`],
    [`${t6Fmt(s.sx,4)}·β₀`, `${t6Fmt(s.sx2,4)}·β₁`, `${t6Fmt(s.sx3,4)}·β₂`, `= ${t6Fmt(s.sxy,4)}`],
    [`${t6Fmt(s.sx2,4)}·β₀`, `${t6Fmt(s.sx3,4)}·β₁`, `${t6Fmt(s.sx4,4)}·β₂`, `= ${t6Fmt(s.sx2y,4)}`],
  ];
  rows.forEach((row, i) => {
    html += `<tr>`;
    row.forEach((cell, j) => {
      const sep = j > 0 && j < 3 ? ' + ' : '';
      html += `<td style="padding:.4rem .65rem;font-family:var(--font-mono);font-size:.82rem;">
        ${sep}${cell}</td>`;
    });
    html += `</tr>`;
  });

  html += `</tbody></table></div>
    </div>
  </div>

  <!-- Matriz ampliada inicial -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T6_ACCENT};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${T6_ACCENT};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;font-weight:700;color:#fff;font-size:.9rem;">M</div>
      <div>
        <div class="card-title">Matriz ampliada [A | b]</div>
        <div class="card-subtitle">Lista para aplicar eliminación de Gauss-Jordan</div>
      </div>
    </div>
    <div class="t6-step-body" style="overflow-x:auto;">
      ${t6MatrixHtml(res.M0, ['β₀','β₁','β₂','b'])}
    </div>
  </div>

  <div style="margin-top:.75rem;text-align:right;">
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-pol-gauss')">Siguiente: Gauss-Jordan →</button>
  </div>`;
  sec.innerHTML = html;
}

/** Helper: renderiza matriz como tabla */
function t6MatrixHtml(M, headers) {
  let h = `<table style="border-collapse:separate;border-spacing:4px;font-family:var(--font-mono);font-size:.82rem;">`;
  if (headers) {
    h += `<thead><tr>${headers.map((hd,i) => `<th style="padding:.3rem .7rem;background:${T6_LIGHT};
      color:${T6_DARK};border-radius:4px;${i===headers.length-1?'border-left:2px solid '+T6_COLOR+';':''}">${hd}</th>`).join('')}</tr></thead>`;
  }
  h += `<tbody>`;
  M.forEach(row => {
    h += `<tr>${row.map((v,j) => `<td style="padding:.35rem .7rem;background:var(--gray-50);
      border-radius:4px;text-align:right;${j===row.length-1?'border-left:2px solid '+T6_COLOR+'44;font-weight:700;color:'+T6_DARK+';':''}">
      ${Math.abs(v) > 1000 || (Math.abs(v) < 0.001 && v !== 0) ? v.toExponential(4) : t6Fmt(v,4)}</td>`).join('')}</tr>`;
  });
  h += `</tbody></table>`;
  return h;
}

/** Sección 6: Pasos de Gauss-Jordan */
function t6RenderPolGauss(res) {
  const sec = document.getElementById('t6-pol-gauss');
  if (!sec) return;

  let html = `
  <div class="page-header">
    <h2>Regresión Polinomial — Eliminación de Gauss-Jordan</h2>
    <p>Proceso de reducción paso a paso hasta obtener la matriz identidad</p>
  </div>`;

  res.steps.forEach((step, i) => {
    const isLast = i === res.steps.length - 1;
    html += `
    <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${isLast ? '#10b981' : T6_COLOR};">
      <div class="card-header" style="padding:.6rem 1.25rem;">
        <div class="card-header-icon" style="background:${isLast?'#10b981':T6_COLOR};width:32px;height:32px;
          border-radius:8px;display:flex;align-items:center;justify-content:center;
          color:#fff;font-size:.78rem;font-weight:700;flex-shrink:0;">${i}</div>
        <div style="font-family:var(--font-mono);font-size:.85rem;color:var(--gray-700);">${step.label}</div>
      </div>
      <div class="t6-step-body" style="overflow-x:auto;">
        ${t6MatrixHtml(step.M, null)}
      </div>
    </div>`;
  });

  html += `
  <div style="margin-top:.75rem;display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t6GoTo('t6-pol-sistema')">← Sistema</button>
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-pol-resultado')">Siguiente: Modelo y R² →</button>
  </div>`;
  sec.innerHTML = html;
}

/** Sección 7: Resultado polinomial + R² */
function t6RenderPolResultado(res, lx, ly) {
  const sec = document.getElementById('t6-pol-resultado');
  if (!sec) return;

  const R2pct = (res.R2 * 100).toFixed(2);
  const signB1 = res.b1 >= 0 ? `+ ${t6FmtCoef(res.b1)}` : `− ${t6FmtCoef(Math.abs(res.b1))}`;
  const signB2 = res.b2 >= 0 ? `+ ${t6FmtCoef(res.b2)}` : `− ${t6FmtCoef(Math.abs(res.b2))}`;

  let html = `
  <div class="page-header">
    <h2>Regresión Polinomial — Modelo y Análisis</h2>
    <p>Coeficientes β₀, β₁, β₂ · Coeficiente de determinación R² · Residuos</p>
  </div>

  <!-- Coeficientes -->
  <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:.875rem;margin-bottom:1.25rem;">
    ${['β₀','β₁','β₂'].map((label, i) => {
      const val = [res.b0, res.b1, res.b2][i];
      const col = [T6_COLOR, T6_ACCENT, '#8b5cf6'][i];
      return `<div class="t6-metric-card" style="border-left-color:${col};">
        <div class="t6-metric-label">${label} (${['intercepto','pendiente','cuadrático'][i]})</div>
        <div class="t6-metric-val" style="color:${col};">${t6Fmt(val, 8)}</div>
      </div>`;
    }).join('')}
    <div class="t6-metric-card" style="border-left-color:#10b981;">
      <div class="t6-metric-label">R²</div>
      <div class="t6-metric-val" style="color:#10b981;">${t6Fmt(res.R2, 6)}</div>
      <div class="t6-metric-sub">El ${R2pct}% de la variabilidad explicada</div>
    </div>
  </div>

  <!-- Modelo final -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T6_LIGHT},#f0fdf4);border:2px solid ${T6_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t6-icon">🎯</div>
      <div><div class="card-title">Modelo de Regresión Polinomial Cuadrático</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;font-family:var(--font-mono);font-size:1.05rem;text-align:center;">
      <div style="margin-bottom:.5rem;color:var(--gray-500);font-size:.8rem;font-family:var(--font-main);">Ecuación del modelo:</div>
      <div style="font-size:1.25rem;font-weight:700;color:${T6_DARK};">
        Ŷ = ${t6FmtCoef(res.b0)} ${signB1}·X ${signB2}·X²
      </div>
    </div>
  </div>

  <!-- Tabla de predicciones y residuos -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t6-icon">📋</div>
      <div>
        <div class="card-title">Predicciones y residuos</div>
        <div class="card-subtitle">eᵢ = yᵢ − ŷᵢ</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.8rem;">
      <thead>
        <tr style="background:${T6_LIGHT};">
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">i</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">xᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">yᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">ŷᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">eᵢ</th>
          <th style="padding:.45rem .75rem;color:${T6_DARK};border-bottom:2px solid ${T6_COLOR}33;">eᵢ²</th>
        </tr>
      </thead>
      <tbody>`;

  let sumE2 = 0;
  res.pred.forEach((p, i) => {
    const e2 = p.e * p.e; sumE2 += e2;
    const ec = p.e >= 0 ? T6_COLOR : '#ef4444';
    html += `<tr style="${i%2===1?'background:var(--gray-50)':''}">
      <td style="text-align:center;padding:.35rem .75rem;">${i+1}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.x,4)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.y,4)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(p.yhat,6)}</td>
      <td style="text-align:right;padding:.35rem .75rem;color:${ec};font-weight:600;">${t6Fmt(p.e,6)}</td>
      <td style="text-align:right;padding:.35rem .75rem;">${t6Fmt(e2,6)}</td>
    </tr>`;
  });

  html += `
      <tr style="background:${T6_LIGHT};font-weight:700;border-top:2px solid ${T6_COLOR}33;">
        <td colspan="5" style="padding:.45rem .75rem;color:${T6_DARK};">Σeᵢ² (SR²)</td>
        <td style="text-align:right;padding:.45rem .75rem;color:${T6_DARK};">${t6Fmt(sumE2,6)}</td>
      </tr>
    </tbody></table></div>
  </div>

  <div style="margin-top:.75rem;display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t6GoTo('t6-pol-gauss')">← Gauss-Jordan</button>
    <button class="btn t6-btn-primary" onclick="t6GoTo('t6-input')">🔁 Nuevos datos</button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL — BOTÓN CALCULAR
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Inicializar tabla con 4 filas vacías */
  t6State.data = Array.from({ length: 4 }, () => ({ x: 0, y: 0 }));
  t6RenderDataTable();

  /* Navegación interna T6 */
  document.querySelectorAll('.t6-nav[data-t6]').forEach(el => {
    el.addEventListener('click', () => t6GoTo(el.getAttribute('data-t6')));
  });

  /* Agregar / quitar filas */
  document.getElementById('btnT6AddRow')?.addEventListener('click', t6AddRow);
  document.getElementById('btnT6RemRow')?.addEventListener('click', t6RemRow);

  /* Ejemplo clase — Publicidad (foto 7) */
  document.getElementById('btnT6Ejemplo')?.addEventListener('click', () => {
    t6State.data = [
      { x: 1, y: 2 }, { x: 2, y: 4 }, { x: 3, y: 5 }, { x: 6, y: 11 }
    ];
    document.getElementById('t6LabelX').value = 'Inversión en publicidad (miles $)';
    document.getElementById('t6LabelY').value = 'Ventas obtenidas (miles $)';
    document.querySelector('input[name="t6Mode"][value="lineal"]').checked = true;
    t6RenderDataTable();
    clearAlert('t6Alert');
    showAlert('t6Alert','info','📋 Ejemplo de clase cargado — publicidad vs ventas. Presiona ▶ Calcular.');
  });

  /* Ejemplo polinomial (foto 8) */
  document.getElementById('btnT6EjemploPol')?.addEventListener('click', () => {
    t6State.data = [
      {x:4,y:4.84},{x:5,y:5.99},{x:6,y:6.67},{x:7,y:5.42},{x:8,y:7.88},
      {x:9,y:6.84},{x:10,y:8.26},{x:11,y:8.95},{x:12,y:10.71},{x:13,y:9.83},{x:14,y:10.52}
    ];
    document.getElementById('t6LabelX').value = 'X';
    document.getElementById('t6LabelY').value = 'Y';
    document.querySelector('input[name="t6Mode"][value="polinomial"]').checked = true;
    t6RenderDataTable();
    clearAlert('t6Alert');
    showAlert('t6Alert','info','📋 Ejemplo polinomial de clase cargado (27/05/26). Presiona ▶ Calcular.');
  });

  /* Calcular */
  document.getElementById('btnT6Calcular')?.addEventListener('click', () => {
    clearAlert('t6Alert');
    clearAlert('t6AlertGlobal');
    const pts  = t6ReadData();
    const mode = document.querySelector('input[name="t6Mode"]:checked')?.value || 'lineal';
    const lx   = document.getElementById('t6LabelX')?.value?.trim() || 'X';
    const ly   = document.getElementById('t6LabelY')?.value?.trim() || 'Y';

    if (pts.length < 3) { showAlert('t6Alert','danger','Se necesitan al menos 3 puntos.'); return; }
    if ((mode === 'polinomial' || mode === 'ambos') && pts.length < 4) {
      showAlert('t6Alert','danger','La regresión polinomial necesita al menos 4 puntos.'); return;
    }

    try {
      t6State.mode = mode; t6State.labelX = lx; t6State.labelY = ly;

      if (mode === 'lineal' || mode === 'ambos') {
        t6State.lineal = t6RegLineal(pts);
        t6RenderLinTabla(t6State.lineal, pts, lx, ly);
        t6RenderLinCoef(t6State.lineal);
        t6RenderLinError(t6State.lineal, pts);
      }
      if (mode === 'polinomial' || mode === 'ambos') {
        t6State.pol = t6RegPolinomial(pts);
        t6RenderPolSistema(t6State.pol);
        t6RenderPolGauss(t6State.pol);
        t6RenderPolResultado(t6State.pol, lx, ly);
      }

      /* Marcar download como listo — se mostrará junto a la sección activa */
      const dlBar = document.getElementById('t6-download-bar');
      if (dlBar) { dlBar.dataset.ready = '1'; }

      /* Inicializar gráfica lineal */
      if (mode === 'lineal' || mode === 'ambos') {
        t6LinReset();
        setTimeout(() => { t6InitLinGraph(); t6DrawLin(); }, 100);
        t6GoTo('t6-lin-tabla');
        showAlert('t6AlertGlobal','success',
          `✓ Regresión Lineal: Ŷ = ${t6FmtCoef(t6State.lineal.beta0)} + ${t6FmtCoef(t6State.lineal.beta1)}·X · R² = ${t6State.lineal.R2.toFixed(6)}`);
      } else {
        t6GoTo('t6-pol-sistema');
        showAlert('t6AlertGlobal','success',
          `✓ Regresión Polinomial: Ŷ = ${t6FmtCoef(t6State.pol.b0)} + ${t6FmtCoef(t6State.pol.b1)}·X + ${t6FmtCoef(t6State.pol.b2)}·X² · R² = ${t6State.pol.R2.toFixed(6)}`);
      }

    } catch(e) { showAlert('t6Alert','danger','Error: ' + e.message); }
  });

  window.addEventListener('resize', () => {
    if (t6State.lineal) t6DrawLin();
  });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T6
══════════════════════════════════════════════════════════════ */
(function patchT6Export() {
  document.addEventListener('DOMContentLoaded', () => {
    if (typeof numerixExport === 'undefined') return;
    numerixExport.t6 = function() {
      const lin = t6State.lineal, pol = t6State.pol;
      if (!lin && !pol) { alert('Ejecuta el cálculo primero.'); return; }
      const pts = t6State.data;
      const wb  = XLSX.utils.book_new();

      if (lin) {
        /* Hoja lineal */
        const hdrL = ['i','xi','yi','xi²','xi·yi','ŷi','ei','ei²'];
        const rowsL = pts.map((p,i) => {
          const yhat = lin.beta0 + lin.beta1 * p.x;
          const e    = p.y - yhat;
          return [i+1, p.x, p.y, p.x*p.x, p.x*p.y, yhat, e, e*e];
        });
        const sumRow = ['Σ', lin.sx, lin.sy, lin.sx2, lin.sxy,'','', lin.SRR];
        const blank  = [];
        const info   = [
          ['NUMERIX — Regresión Lineal','','© 2026 Fernando Granja & Alejandra Tinoco'],
          [], ['n', lin.n], ['β₁', lin.beta1], ['β₀', lin.beta0],
          ['Modelo', `Y = ${t6FmtCoef(lin.beta0)} + ${t6FmtCoef(lin.beta1)}·X`],
          ['R²', lin.R2], ['r', lin.r], ['Sy/x', lin.Syx],
        ];
        XLSX.utils.book_append_sheet(wb,
          XLSX.utils.aoa_to_sheet([...info, blank, [hdrL], ...rowsL, sumRow]),
          'Regresion Lineal');
      }

      if (pol) {
        /* Hoja polinomial */
        const hdrP = ['i','xi','yi','xi²','xi³','xi⁴','xi·yi','xi²·yi','ŷi','ei','ei²'];
        const rowsP = pts.map((p,i) => {
          const yhat = pol.b0 + pol.b1*p.x + pol.b2*p.x*p.x;
          const e    = p.y - yhat;
          return [i+1, p.x, p.y, p.x**2, p.x**3, p.x**4, p.x*p.y, p.x**2*p.y, yhat, e, e*e];
        });
        const infoP = [
          ['NUMERIX — Regresión Polinomial','','© 2026 Fernando Granja & Alejandra Tinoco'],
          [], ['n', pol.n], ['β₀', pol.b0], ['β₁', pol.b1], ['β₂', pol.b2],
          ['Modelo', `Y = ${t6FmtCoef(pol.b0)} + ${t6FmtCoef(pol.b1)}·X + ${t6FmtCoef(pol.b2)}·X²`],
          ['R²', pol.R2],
        ];
        XLSX.utils.book_append_sheet(wb,
          XLSX.utils.aoa_to_sheet([...infoP, [], [hdrP], ...rowsP]),
          'Regresion Polinomial');
      }

      XLSX.writeFile(wb, `NUMERIX_T6_AjusteCurvas.xlsx`);
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 7 — INTERPOLACIÓN POLINOMIAL
   Newton por Diferencias Divididas · Lagrange
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T7_COLOR  = '#7c3aed';   /* violeta */
const T7_LIGHT  = '#ede9fe';
const T7_DARK   = '#4c1d95';
const T7_NEWTON = '#0ea5e9';   /* azul para Newton */
const T7_LAG    = '#f59e0b';   /* ámbar para Lagrange */

/* ── Estado T7 ──────────────────────────────────────────────── */
const t7State = {
  data:    [],       /* [{x, y}] */
  xPred:   null,
  mode:    'ambos',
  newton:  null,     /* resultado Newton */
  lagrange: null,    /* resultado Lagrange */
  graph:   { canvas:null, ctx:null, xMin:-4, xMax:4, yMin:-10, yMax:10,
             dragging:false, lastMouse:{x:0,y:0}, hoverOn:false }
};

/* ══════════════════════════════════════════════════════════════
   NAVEGACIÓN INTERNA T7
══════════════════════════════════════════════════════════════ */
function t7GoTo(secId) {
  document.querySelectorAll('.t7-sec').forEach(s => s.style.display = 'none');
  document.querySelectorAll('.t7-nav').forEach(n => n.classList.remove('active'));
  const sec = document.getElementById(secId);
  if (sec) sec.style.display = 'block';
  document.querySelectorAll(`[data-t7="${secId}"]`).forEach(el => el.classList.add('active'));
  /* Mantener download bar si ya hay resultados */
  const dl = document.getElementById('t7-download-bar');
  if (dl && dl.dataset.ready === '1' && secId !== 't7-input') dl.style.display = 'block';
}
window.t7GoTo = t7GoTo;

/* ══════════════════════════════════════════════════════════════
   TABLA DE DATOS DINÁMICA
══════════════════════════════════════════════════════════════ */
function t7RenderDataTable() {
  const tbody = document.getElementById('t7DataBody');
  if (!tbody) return;
  tbody.innerHTML = t7State.data.map((pt, i) => `
    <tr>
      <td style="text-align:center;font-family:var(--font-mono);font-size:.8rem;
                 color:var(--gray-400);">${i}</td>
      <td><input type="number" class="t6-cell-input" id="t7_x_${i}"
          value="${pt.x}" step="any" onchange="t7UpdateCell(${i},'x',this.value)" /></td>
      <td><input type="number" class="t6-cell-input" id="t7_y_${i}"
          value="${pt.y}" step="any" onchange="t7UpdateCell(${i},'y',this.value)" /></td>
    </tr>`).join('');
}

function t7UpdateCell(i, field, val) {
  if (t7State.data[i]) t7State.data[i][field] = parseFloat(val) || 0;
}
window.t7UpdateCell = t7UpdateCell;

function t7ReadData() {
  t7State.data.forEach((pt, i) => {
    const xEl = document.getElementById(`t7_x_${i}`);
    const yEl = document.getElementById(`t7_y_${i}`);
    if (xEl) pt.x = parseFloat(xEl.value) || 0;
    if (yEl) pt.y = parseFloat(yEl.value) || 0;
  });
  return t7State.data.map(p => ({ x: p.x, y: p.y }));
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMO — NEWTON DIFERENCIAS DIVIDIDAS
══════════════════════════════════════════════════════════════ */
function t7Newton(pts, xPred) {
  const n  = pts.length;
  const xs = pts.map(p => p.x);
  const ys = pts.map(p => p.y);

  /* Construir tabla completa de DD [n × n] */
  /* dd[i][0] = f(xᵢ),  dd[i][j] = f[xᵢ, …, xᵢ₊ⱼ] */
  const dd = Array.from({ length: n }, (_, i) => new Array(n).fill(null));
  for (let i = 0; i < n; i++) dd[i][0] = ys[i];

  for (let j = 1; j < n; j++) {
    for (let i = 0; i < n - j; i++) {
      dd[i][j] = (dd[i + 1][j - 1] - dd[i][j - 1]) / (xs[i + j] - xs[i]);
    }
  }

  /* Coeficientes: primera fila de cada orden */
  const coefs = Array.from({ length: n }, (_, j) => dd[0][j]);

  /* Evaluar Pₙ(xPred) por algoritmo de Horner anidado */
  const evalNewton = (x) => {
    let result = coefs[n - 1];
    for (let i = n - 2; i >= 0; i--) {
      result = result * (x - xs[i]) + coefs[i];
    }
    return result;
  };

  const pred = evalNewton(xPred);

  /* Construir string del polinomio expandido */
  const polyStr = t7NewtonPolyStr(coefs, xs, n);

  return { n, pts, xs, ys, dd, coefs, pred, xPred, polyStr, evalFn: evalNewton };
}

/** Construye string legible del polinomio de Newton */
function t7NewtonPolyStr(coefs, xs, n) {
  const fmt = v => {
    if (Math.abs(v) > 9999 || (Math.abs(v) < 0.0001 && v !== 0)) return v.toExponential(4);
    return parseFloat(v.toFixed(6)).toString();
  };
  let parts = [];
  for (let i = 0; i < n; i++) {
    if (Math.abs(coefs[i]) < 1e-12) continue;
    let term = fmt(coefs[i]);
    for (let j = 0; j < i; j++) {
      const xj = xs[j];
      term += xj === 0 ? '·x' : xj < 0 ? `·(x+${fmt(Math.abs(xj))})` : `·(x−${fmt(xj)})`;
    }
    parts.push(term);
  }
  return parts.length ? parts.join(' + ').replace(/\+ -/g, '− ') : '0';
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMO — LAGRANGE
══════════════════════════════════════════════════════════════ */
function t7Lagrange(pts, xPred) {
  const n  = pts.length;
  const xs = pts.map(p => p.x);
  const ys = pts.map(p => p.y);

  /* Calcular cada Lᵢ(xPred) y guardar factores para mostrar */
  const bases = xs.map((xi, i) => {
    let num = 1, den = 1;
    const factors = [];
    for (let j = 0; j < n; j++) {
      if (j === i) continue;
      num *= (xPred - xs[j]);
      den *= (xi - xs[j]);
      factors.push({ xj: xs[j], xi, xPred });
    }
    const Li = den !== 0 ? num / den : 0;
    return { i, xi, yi: ys[i], num, den, Li, factors, contrib: ys[i] * Li };
  });

  const pred = bases.reduce((s, b) => s + b.contrib, 0);

  /* Función de evaluación para la gráfica */
  const evalFn = (x) => {
    let sum = 0;
    for (let i = 0; i < n; i++) {
      let num = 1, den = 1;
      for (let j = 0; j < n; j++) {
        if (j === i) continue;
        num *= (x - xs[j]);
        den *= (xs[i] - xs[j]);
      }
      sum += ys[i] * (den !== 0 ? num / den : 0);
    }
    return sum;
  };

  return { n, pts, xs, ys, bases, pred, xPred, evalFn };
}

/* ══════════════════════════════════════════════════════════════
   FORMATO AUXILIAR T7
══════════════════════════════════════════════════════════════ */
const t7Fmt  = (v, d = 6) => isNaN(v) ? '—' : Number(v).toFixed(d);
const t7FmtC = (v) => {
  if (Math.abs(v) > 9999 || (Math.abs(v) < 0.0001 && v !== 0)) return v.toExponential(4);
  return parseFloat(Number(v).toFixed(8)).toString();
};

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — NEWTON
══════════════════════════════════════════════════════════════ */

/** Sección 1: Tabla de diferencias divididas */
function t7RenderNewtonTabla(res) {
  const sec = document.getElementById('t7-newton-tabla');
  if (!sec) return;
  const { n, xs, ys, dd } = res;

  let html = `
  <div class="page-header">
    <h2>Newton — Tabla de Diferencias Divididas</h2>
    <p>Construcción escalonada de las diferencias divididas f[xᵢ, …, xⱼ].<br>
       Los coeficientes del polinomio son la <strong>primera fila diagonal</strong> (celdas resaltadas).</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t7-icon">📋</div>
      <div>
        <div class="card-title">Tabla de Diferencias Divididas — ${n} puntos · Grado ${n-1} (${['','Lineal','Cuadrático','Cúbico','Cuártico','Quíntico'][n-1]||'Grado '+(n-1)})</div>
        <div class="card-subtitle">f[xᵢ] = orden 0 · f[xᵢ,xᵢ₊₁] = orden 1 · f[xᵢ,xᵢ₊₁,xᵢ₊₂] = orden 2 …</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.78rem;">
      <thead>
        <tr style="background:${T7_LIGHT};">
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">i</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">xᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">f(xᵢ) — Orden 0</th>`;

  for (let j = 1; j < n; j++) {
    html += `<th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">
      Orden ${j}${j === 1 ? '' : ''}</th>`;
  }
  html += `</tr></thead><tbody>`;

  for (let i = 0; i < n; i++) {
    html += `<tr style="${i % 2 === 1 ? 'background:var(--gray-50)' : ''}">
      <td style="text-align:center;padding:.4rem .75rem;font-weight:700;color:${T7_COLOR};">${i}</td>
      <td style="text-align:right;padding:.4rem .75rem;font-weight:600;">${t7Fmt(xs[i], 4)}</td>`;

    for (let j = 0; j < n; j++) {
      const val = dd[i][j];
      const isCoef = (i === 0);    /* primera fila = coeficientes */
      const isDiag = (i + j < n); /* dentro del triángulo válido */

      if (!isDiag) {
        html += `<td style="padding:.4rem .75rem;text-align:center;color:var(--gray-300);">—</td>`;
      } else {
        const bg    = isCoef ? `background:${T7_LIGHT};` : '';
        const fw    = isCoef ? 'font-weight:700;' : '';
        const color = isCoef ? `color:${T7_DARK};` : '';
        const badge = isCoef ? `<span style="display:inline-block;margin-left:.3rem;
          background:${T7_COLOR};color:#fff;font-size:.6rem;padding:.1rem .3rem;
          border-radius:3px;vertical-align:middle;">a${j}</span>` : '';
        html += `<td style="padding:.4rem .75rem;text-align:right;${bg}${fw}${color}">
          ${t7Fmt(val, 6)}${badge}</td>`;
      }
    }
    html += `</tr>`;
  }

  html += `</tbody></table></div>
  </div>

  <!-- Coeficientes extraídos -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#f5f3ff);
    border:2px solid ${T7_COLOR}33;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🔑</div>
      <div><div class="card-title">Coeficientes del Polinomio</div>
      <div class="card-subtitle">Primera diagonal — se usan en la fórmula de Newton</div></div>
    </div>
    <div style="display:flex;flex-wrap:wrap;gap:.625rem;padding:.5rem 1.25rem 1.25rem;">`;

  res.coefs.forEach((c, j) => {
    html += `<div style="border-radius:var(--radius-sm);border:2px solid ${T7_COLOR}33;
                border-left:5px solid ${T7_COLOR};padding:.625rem .875rem;background:var(--gray-50);">
      <div style="font-family:var(--font-main);font-size:.7rem;font-weight:700;
                  color:${T7_DARK};text-transform:uppercase;">a${j} = f[x₀…x${j}]</div>
      <div style="font-family:var(--font-mono);font-size:.95rem;font-weight:700;
                  color:${T7_COLOR};">${t7Fmt(c, 8)}</div>
    </div>`;
  });

  html += `</div></div>
  <div style="text-align:right;">
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-newton-pol')">
      Siguiente: Polinomio →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/** Sección 2: Polinomio de Newton + evaluación */
function t7RenderNewtonPol(res) {
  const sec = document.getElementById('t7-newton-pol');
  if (!sec) return;
  const { n, xs, coefs, pred, xPred } = res;

  /* Construir cada término del polinomio con sustitución */
  let termsHtml = '';
  for (let i = 0; i < n; i++) {
    if (Math.abs(coefs[i]) < 1e-12) continue;
    let termLabel = `a${i}`;
    let factorsLabel = '';
    for (let j = 0; j < i; j++) {
      const xj = xs[j];
      const sign = xj < 0 ? `+${t7Fmt(Math.abs(xj),4)}` : xj === 0 ? '' : `−${t7Fmt(xj,4)}`;
      factorsLabel += `·(x${sign === '' ? '' : sign})`;
    }

    /* Evaluar el término en xPred */
    let termVal = coefs[i];
    for (let j = 0; j < i; j++) termVal *= (xPred - xs[j]);

    termsHtml += `
    <div class="t6-formula-row" style="border-left-color:${T7_COLOR};">
      <div style="font-family:var(--font-mono);font-size:.88rem;font-weight:700;
                  color:${T7_COLOR};min-width:40px;">T${i}:</div>
      <div style="font-family:var(--font-mono);font-size:.85rem;flex:1;">
        ${t7FmtC(coefs[i])}${factorsLabel}
      </div>
      <div style="font-family:var(--font-mono);font-size:.85rem;color:var(--gray-500);">
        = <strong>${t7Fmt(termVal, 6)}</strong>
      </div>
    </div>`;
  }

  let html = `
  <div class="page-header">
    <h2>Newton — Polinomio ${['','Lineal','Cuadrático','Cúbico','Cuártico','Quíntico'][n-1]||'Grado '+(n-1)}</h2>
    <p>Sustitución de coeficientes y evaluación en x = ${xPred} · Grado ${n-1}</p>
  </div>

  <!-- Forma general -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T7_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t7-icon">Pₙ</div>
      <div><div class="card-title">Forma General del Polinomio de Newton</div></div>
    </div>
    <div class="t6-step-body" style="font-family:var(--font-mono);font-size:.88rem;">
      <div style="color:var(--gray-500);margin-bottom:.5rem;">P${n-1}(x) = a₀ + a₁(x−x₀) + a₂(x−x₀)(x−x₁) + …</div>
      <div style="font-weight:700;color:${T7_DARK};word-break:break-all;">
        P${n-1}(x) = ${res.polyStr}
      </div>
    </div>
  </div>

  <!-- Términos con valores -->
  <div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🔢</div>
      <div>
        <div class="card-title">Evaluación en x = ${xPred}</div>
        <div class="card-subtitle">Contribución de cada término Tᵢ</div>
      </div>
    </div>
    <div style="padding:.5rem 1.25rem 1rem;">${termsHtml}</div>
  </div>

  <!-- Resultado final -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#f5f3ff);
    border:2px solid ${T7_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🎯</div>
      <div><div class="card-title">Resultado — Newton</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;text-align:center;">
      <div style="font-family:var(--font-mono);font-size:1.4rem;font-weight:700;color:${T7_COLOR};">
        P${n-1}(${xPred}) = <span style="color:${T7_NEWTON};">${t7Fmt(pred, 8)}</span>
      </div>
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t7GoTo('t7-newton-tabla')">← Tabla DD</button>
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-lag-bases')">Siguiente: Lagrange →</button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — LAGRANGE
══════════════════════════════════════════════════════════════ */

/** Sección 3: Bases de Lagrange Lᵢ(x) */
function t7RenderLagBases(res) {
  const sec = document.getElementById('t7-lag-bases');
  if (!sec) return;
  const { n, xs, ys, bases, xPred } = res;

  let html = `
  <div class="page-header">
    <h2>Lagrange — Funciones Base Lᵢ(x) · Grado ${n-1}</h2>
    <p>Cada Lᵢ(x) vale 1 en xᵢ y 0 en todos los demás puntos.<br>
       Se evalúan en x = ${xPred}.</p>
  </div>`;

  bases.forEach(b => {
    const COLORS = [T7_COLOR, T7_NEWTON, T7_LAG, '#ef4444', '#10b981'];
    const col = COLORS[b.i % COLORS.length];

    /* Construir string del numerador y denominador */
    let numParts = [], denParts = [];
    for (let j = 0; j < n; j++) {
      if (j === b.i) continue;
      const xj = xs[j];
      const xjStr = xj < 0 ? `+${Math.abs(xj)}` : xj === 0 ? '' : `−${xj}`;
      numParts.push(`(${xPred}${xjStr !== '' ? xjStr.replace('+','−').replace('−','+') : ''})`);

      /* Denominador con valores reales */
      const diff = b.xi - xj;
      denParts.push(`(${t7FmtC(b.xi)}−${t7FmtC(xj)}) = ${t7FmtC(diff)}`);
    }

    html += `
    <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${col};">
      <div class="card-header">
        <div class="card-header-icon" style="background:${col};width:38px;height:38px;
          border-radius:10px;display:flex;align-items:center;justify-content:center;
          color:#fff;font-weight:700;font-size:.85rem;flex-shrink:0;">L${b.i}</div>
        <div>
          <div class="card-title">L${b.i}(x) — punto (x${b.i} = ${b.xi}, f(x${b.i}) = ${b.yi})</div>
        </div>
      </div>
      <div class="t6-step-body">
        <!-- Fórmula simbólica -->
        <div style="font-family:var(--font-mono);font-size:.82rem;color:var(--gray-600);margin-bottom:.25rem;">
          L${b.i}(x) = ∏ (x−xⱼ)/(x${b.i}−xⱼ)  para j ≠ ${b.i}
        </div>
        <!-- Sustitución numérica -->
        <div style="font-family:var(--font-mono);font-size:.82rem;
                    background:var(--gray-50);border-radius:var(--radius-sm);padding:.5rem .75rem;">
          <div style="color:var(--gray-500);margin-bottom:.3rem;">Sustituyendo x = ${xPred}:</div>
          <div style="display:flex;flex-direction:column;gap:.2rem;">
            <div>Numerador: <span style="color:${col};">${t7Fmt(b.num, 8)}</span></div>
            <div>Denominador: <span style="color:${col};">${t7Fmt(b.den, 8)}</span></div>
          </div>
        </div>
        <!-- Resultado L_i(xPred) -->
        <div style="font-family:var(--font-mono);font-size:.9rem;">
          L${b.i}(${xPred}) = ${t7Fmt(b.num,6)} / ${t7Fmt(b.den,6)} =
          <strong style="color:${col};">${t7Fmt(b.Li, 8)}</strong>
        </div>
        <!-- Contribución -->
        <div style="font-family:var(--font-mono);font-size:.85rem;color:var(--gray-600);">
          f(x${b.i})·L${b.i}(${xPred}) = ${t7FmtC(b.yi)} · ${t7Fmt(b.Li, 6)} =
          <strong style="color:${col};">${t7Fmt(b.contrib, 8)}</strong>
        </div>
      </div>
    </div>`;
  });

  html += `
  <div style="text-align:right;">
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-lag-pol')">Siguiente: Polinomio →</button>
  </div>`;
  sec.innerHTML = html;
}

/** Sección 4: Polinomio de Lagrange + resultado final */
function t7RenderLagPol(res, newtonRes) {
  const sec = document.getElementById('t7-lag-pol');
  if (!sec) return;
  const { n, bases, pred, xPred } = res;

  /* Suma de contribuciones */
  let sumaHtml = bases.map(b => {
    const COLORS = [T7_COLOR, T7_NEWTON, T7_LAG, '#ef4444', '#10b981'];
    const col = COLORS[b.i % COLORS.length];
    return `<span style="color:${col};">${t7Fmt(b.contrib, 6)}</span>`;
  }).join(' + ');

  const match = newtonRes && Math.abs(newtonRes.pred - pred) < 1e-6;

  let html = `
  <div class="page-header">
    <h2>Lagrange — Resultado Final</h2>
    <p>Suma ponderada de las funciones base · Evaluación en x = ${xPred}</p>
  </div>

  <!-- Fórmula suma -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T7_LAG};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${T7_LAG};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">Pₙ</div>
      <div><div class="card-title">Suma de contribuciones f(xᵢ)·Lᵢ(${xPred})</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.88rem;">
        P${n-1}(${xPred}) = ${sumaHtml}
      </div>
      <div style="font-family:var(--font-mono);font-size:.88rem;margin-top:.25rem;">
        = <strong style="color:${T7_LAG};font-size:1.1rem;">${t7Fmt(pred, 8)}</strong>
      </div>
    </div>
  </div>

  <!-- Tabla comparativa si hay ambos métodos -->
  ${newtonRes ? `
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#fffbeb);
    border:2px solid ${match ? '#10b981' : '#ef4444'}44;">
    <div class="card-header">
      <div class="card-header-icon" style="background:${match?'#10b981':'#ef4444'};width:38px;height:38px;
        border-radius:10px;display:flex;align-items:center;justify-content:center;
        color:#fff;font-size:1.1rem;">
        ${match ? '✓' : '⚠'}
      </div>
      <div>
        <div class="card-title">Comparación Newton vs Lagrange</div>
        <div class="card-subtitle">${match ? 'Ambos métodos producen el mismo resultado ✓' : 'Diferencia detectada — revisar datos'}</div>
      </div>
    </div>
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:1rem;padding:.5rem 1.25rem 1.25rem;">
      <div style="background:${T7_LIGHT};border-radius:var(--radius-sm);padding:.875rem;text-align:center;">
        <div style="font-size:.72rem;font-weight:700;color:${T7_DARK};text-transform:uppercase;margin-bottom:.25rem;">
          Newton — P${n-1}(${xPred})
        </div>
        <div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:${T7_NEWTON};">
          ${t7Fmt(newtonRes.pred, 8)}
        </div>
      </div>
      <div style="background:#fffbeb;border-radius:var(--radius-sm);padding:.875rem;text-align:center;">
        <div style="font-size:.72rem;font-weight:700;color:#92400e;text-transform:uppercase;margin-bottom:.25rem;">
          Lagrange — P${n-1}(${xPred})
        </div>
        <div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:${T7_LAG};">
          ${t7Fmt(pred, 8)}
        </div>
      </div>
    </div>
  </div>` : `
  <!-- Solo Lagrange -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#fffbeb);
    border:2px solid ${T7_LAG}44;">
    <div class="card-header">
      <div class="card-header-icon" style="background:${T7_LAG};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-size:1.1rem;">🎯</div>
      <div><div class="card-title">Resultado Final — Lagrange</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;text-align:center;">
      <div style="font-family:var(--font-mono);font-size:1.4rem;font-weight:700;color:${T7_LAG};">
        P${n-1}(${xPred}) = ${t7Fmt(pred, 8)}
      </div>
    </div>
  </div>`}

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t7GoTo('t7-lag-bases')">← Bases Lᵢ</button>
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-grafica');setTimeout(t7DrawGraph,80);">
      📈 Ver Gráfica →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA T7
══════════════════════════════════════════════════════════════ */
function t7InitGraph() {
  const g = t7State.graph;
  const c = document.getElementById('t7Canvas');
  if (!c || g.canvas) return;
  g.canvas = c; g.ctx = c.getContext('2d');

  const resize = () => {
    const w = c.parentElement.clientWidth || 700;
    c.width = w; c.height = Math.max(340, Math.round(w * 0.52));
    t7DrawGraph();
  };
  resize();
  window.addEventListener('resize', resize);

  c.addEventListener('mousedown', e => { g.dragging = true; g.lastMouse = { x: e.clientX, y: e.clientY }; c.style.cursor='grabbing'; });
  c.addEventListener('mouseup',   () => { g.dragging = false; c.style.cursor='crosshair'; });
  c.addEventListener('mouseleave',() => { g.dragging = false; g.hoverOn = false; c.style.cursor='crosshair';
    const tip = document.getElementById('t7Tooltip'); if (tip) tip.style.display='none'; t7DrawGraph(); });
  c.addEventListener('mousemove', e => {
    const rect = c.getBoundingClientRect();
    const px = (e.clientX - rect.left) * (c.width / rect.width);
    const py = (e.clientY - rect.top)  * (c.height / rect.height);
    const mw = t7ToWorld(px, py);
    g.hoverOn = true;
    const coord = document.getElementById('t7Coords');
    if (coord) coord.innerHTML = `x = ${mw.x.toFixed(3)} &nbsp; y = ${mw.y.toFixed(3)}`;
    if (g.dragging) {
      const dx = (e.clientX - g.lastMouse.x) / rect.width  * (g.xMax - g.xMin);
      const dy = (e.clientY - g.lastMouse.y) / rect.height * (g.yMax - g.yMin);
      g.xMin -= dx; g.xMax -= dx; g.yMin += dy; g.yMax += dy;
      g.lastMouse = { x: e.clientX, y: e.clientY };
    }
    t7DrawGraph();
  });
  c.addEventListener('wheel', e => {
    e.preventDefault();
    const f = e.deltaY > 0 ? 1.12 : 0.89;
    const rect = c.getBoundingClientRect();
    const { x: wx, y: wy } = t7ToWorld(
      (e.clientX - rect.left) * (c.width / rect.width),
      (e.clientY - rect.top)  * (c.height / rect.height)
    );
    g.xMin = wx + (g.xMin-wx)*f; g.xMax = wx + (g.xMax-wx)*f;
    g.yMin = wy + (g.yMin-wy)*f; g.yMax = wy + (g.yMax-wy)*f;
    t7DrawGraph();
  }, { passive:false });
}

function t7ToCanvas(wx, wy) {
  const g = t7State.graph;
  const PAD = { t:24, r:24, b:44, l:60 };
  const W = g.canvas.width, H = g.canvas.height;
  return {
    x: PAD.l + (wx - g.xMin) / (g.xMax - g.xMin) * (W - PAD.l - PAD.r),
    y: PAD.t + (1 - (wy - g.yMin) / (g.yMax - g.yMin)) * (H - PAD.t - PAD.b)
  };
}
function t7ToWorld(px, py) {
  const g = t7State.graph;
  const PAD = { t:24, r:24, b:44, l:60 };
  const W = g.canvas.width, H = g.canvas.height;
  return {
    x: g.xMin + (px - PAD.l) / (W - PAD.l - PAD.r) * (g.xMax - g.xMin),
    y: g.yMin + (1 - (py - PAD.t) / (H - PAD.t - PAD.b)) * (g.yMax - g.yMin)
  };
}

function t7DrawGraph() {
  const g  = t7State.graph;
  const nr = t7State.newton;
  const lr = t7State.lagrange;
  const evalFn = nr?.evalFn || lr?.evalFn;
  if (!g.canvas || !evalFn) return;

  const isDark = document.body.classList.contains('dark-mode');
  const W = g.canvas.width, H = g.canvas.height;
  const ctx = g.ctx;
  const PAD = { t:24, r:24, b:44, l:60 };
  const PW = W-PAD.l-PAD.r, PH = H-PAD.t-PAD.b;
  const niceStep = (range, tgt) => {
    const r = range/tgt, m = Math.pow(10, Math.floor(Math.log10(r)));
    const n2 = r/m; return (n2<1.5?1:n2<3.5?2:n2<7.5?5:10)*m;
  };

  ctx.fillStyle = isDark ? '#0f172a' : '#fff';
  ctx.fillRect(0, 0, W, H);

  /* Grid */
  const xSt = niceStep(g.xMax-g.xMin, 10), ySt = niceStep(g.yMax-g.yMin, 8);
  ctx.strokeStyle = isDark ? 'rgba(148,163,184,.08)' : '#f1f5f9'; ctx.lineWidth=1;
  for (let gx = Math.ceil(g.xMin/xSt)*xSt; gx<=g.xMax; gx+=xSt) {
    const {x:px}=t7ToCanvas(gx,0); ctx.beginPath(); ctx.moveTo(px,PAD.t); ctx.lineTo(px,PAD.t+PH); ctx.stroke();
  }
  for (let gy = Math.ceil(g.yMin/ySt)*ySt; gy<=g.yMax; gy+=ySt) {
    const {y:py}=t7ToCanvas(0,gy); ctx.beginPath(); ctx.moveTo(PAD.l,py); ctx.lineTo(PAD.l+PW,py); ctx.stroke();
  }

  /* Ejes */
  ctx.strokeStyle = isDark?'rgba(148,163,184,.3)':'#cbd5e1'; ctx.lineWidth=1.5;
  const {y:axY}=t7ToCanvas(0,0), {x:axX}=t7ToCanvas(0,0);
  if (g.yMin<=0&&g.yMax>=0) { ctx.beginPath(); ctx.moveTo(PAD.l,axY); ctx.lineTo(PAD.l+PW,axY); ctx.stroke(); }
  if (g.xMin<=0&&g.xMax>=0) { ctx.beginPath(); ctx.moveTo(axX,PAD.t); ctx.lineTo(axX,PAD.t+PH); ctx.stroke(); }

  /* Labels ejes */
  ctx.fillStyle = isDark?'rgba(148,163,184,.6)':'#94a3b8';
  ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
  const lbY=Math.max(PAD.t+10,Math.min(PAD.t+PH-4,axY+16));
  const lbX=Math.max(PAD.l+28,Math.min(PAD.l+PW-4,axX-8));
  for (let gx=Math.ceil(g.xMin/xSt)*xSt; gx<=g.xMax; gx+=xSt) {
    if (Math.abs(gx)<xSt*.01) continue;
    const {x:px}=t7ToCanvas(gx,0); ctx.fillText(gx%1===0?gx:gx.toFixed(1), px, lbY);
  }
  ctx.textAlign='right';
  for (let gy=Math.ceil(g.yMin/ySt)*ySt; gy<=g.yMax; gy+=ySt) {
    if (Math.abs(gy)<ySt*.01) continue;
    const {y:py}=t7ToCanvas(0,gy); ctx.fillText(gy%1===0?gy:gy.toFixed(1), lbX, py);
  }
  ctx.textBaseline='alphabetic';

  /* Curva del polinomio interpolante */
  const STEPS = 300;
  const dx = (g.xMax - g.xMin) / STEPS;
  const colors = nr && lr ? [T7_NEWTON, T7_LAG] : [T7_COLOR];
  const fns    = nr && lr ? [nr.evalFn, lr.evalFn] : [evalFn];
  const labels = nr && lr ? ['Newton','Lagrange'] : [nr ? 'Newton' : 'Lagrange'];
  const dashes = [[], [5,3]];

  fns.forEach((fn, fi) => {
    ctx.beginPath(); ctx.strokeStyle = colors[fi]; ctx.lineWidth=2.5;
    if (dashes[fi].length) ctx.setLineDash(dashes[fi]); else ctx.setLineDash([]);
    let first = true;
    for (let k=0; k<=STEPS; k++) {
      const wx = g.xMin + k*dx;
      try {
        const wy = fn(wx);
        if (!isFinite(wy) || Math.abs(wy)>1e6) { first=true; continue; }
        const {x:px,y:py}=t7ToCanvas(wx,wy);
        if (first) { ctx.moveTo(px,py); first=false; } else ctx.lineTo(px,py);
      } catch(e) { first=true; }
    }
    ctx.stroke(); ctx.setLineDash([]);
  });

  /* Puntos de datos */
  const pts = t7State.data;
  pts.forEach(p => {
    const {x:px,y:py}=t7ToCanvas(p.x,p.y);
    if (px<PAD.l-8||px>PAD.l+PW+8||py<PAD.t-8||py>PAD.t+PH+8) return;
    ctx.beginPath(); ctx.arc(px,py,5.5,0,Math.PI*2);
    ctx.fillStyle=T7_COLOR; ctx.fill();
    ctx.strokeStyle='#fff'; ctx.lineWidth=1.5; ctx.stroke();
    /* Etiqueta del punto */
    ctx.fillStyle=isDark?'#e2e8f0':'#374151';
    ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center';
    ctx.fillText(`(${p.x},${p.y})`,px,py-10);
  });

  /* Punto predicho */
  const xP = t7State.xPred;
  const yP = evalFn(xP);
  if (isFinite(yP)) {
    const {x:ppx,y:ppy}=t7ToCanvas(xP,yP);
    ctx.beginPath(); ctx.arc(ppx,ppy,7,0,Math.PI*2);
    ctx.fillStyle='#ef4444'; ctx.fill();
    ctx.strokeStyle='#fff'; ctx.lineWidth=2; ctx.stroke();
    ctx.fillStyle='#ef4444'; ctx.font='bold 11px "Poppins",sans-serif'; ctx.textAlign='center';
    ctx.fillText(`P(${xP})=${yP.toFixed(4)}`,ppx,ppy-13);
  }

  /* Leyenda */
  ctx.font='11px "Poppins",sans-serif'; ctx.textBaseline='middle';
  const ly=PAD.t+14; let lx=PAD.l+8;
  ctx.fillStyle=T7_COLOR; ctx.beginPath(); ctx.arc(lx+5,ly,5,0,Math.PI*2); ctx.fill();
  ctx.fillStyle=isDark?'#e2e8f0':'#374151'; ctx.textAlign='left';
  ctx.fillText('Datos', lx+14, ly); lx+=70;
  fns.forEach((fn,fi) => {
    ctx.strokeStyle=colors[fi]; ctx.lineWidth=2.5;
    if (dashes[fi].length) ctx.setLineDash(dashes[fi]); else ctx.setLineDash([]);
    ctx.beginPath(); ctx.moveTo(lx,ly); ctx.lineTo(lx+22,ly); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle=isDark?'#e2e8f0':'#374151'; ctx.fillText(labels[fi], lx+27, ly);
    lx += 90;
  });
  ctx.beginPath(); ctx.arc(lx+5,ly,5,0,Math.PI*2); ctx.fillStyle='#ef4444'; ctx.fill();
  ctx.fillStyle=isDark?'#e2e8f0':'#374151'; ctx.fillText(`x=${xP}`, lx+14, ly);
  ctx.textBaseline='alphabetic';

  /* Watermark */
  ctx.fillStyle=isDark?'rgba(124,58,237,.15)':'rgba(148,163,184,.4)';
  ctx.font='600 11px "Poppins",sans-serif'; ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.textBaseline='alphabetic';
}
window.t7DrawGraph = t7DrawGraph;

function t7Zoom(f) {
  const g=t7State.graph;
  const cx=(g.xMin+g.xMax)/2, cy=(g.yMin+g.yMax)/2;
  const hw=(g.xMax-g.xMin)/2*f, hh=(g.yMax-g.yMin)/2*f;
  g.xMin=cx-hw; g.xMax=cx+hw; g.yMin=cy-hh; g.yMax=cy+hh;
  t7DrawGraph();
}
window.t7Zoom = t7Zoom;

function t7ResetView() {
  const pts=t7State.data;
  if (!pts.length) return;
  const xs=pts.map(p=>p.x), ys=pts.map(p=>p.y);
  const xr=Math.max(...xs)-Math.min(...xs)||2;
  const yr=Math.max(...ys)-Math.min(...ys)||2;
  const g=t7State.graph;
  g.xMin=Math.min(...xs)-xr*.2; g.xMax=Math.max(...xs)+xr*.2;
  g.yMin=Math.min(...ys)-yr*.3; g.yMax=Math.max(...ys)+yr*.3;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL — BOTÓN INTERPOLAR
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Inicializar tabla con 3 filas */
  t7State.data = [{x:-3,y:-2},{x:0,y:4},{x:1,y:2}];
  t7RenderDataTable();

  /* Navegación interna */
  document.querySelectorAll('.t7-nav[data-t7]').forEach(el => {
    el.addEventListener('click', () => t7GoTo(el.getAttribute('data-t7')));
  });

  /* Agregar / quitar filas */
  document.getElementById('btnT7AddRow')?.addEventListener('click', () => {
    t7State.data.push({ x: 0, y: 0 });
    t7RenderDataTable();
  });
  document.getElementById('btnT7RemRow')?.addEventListener('click', () => {
    if (t7State.data.length > 2) { t7State.data.pop(); t7RenderDataTable(); }
  });

  /* Ejemplo Newton (fotos 10-12: tabla de DD) */
  document.getElementById('btnT7EjNewton')?.addEventListener('click', () => {
    t7State.data = [{x:-3,y:-2},{x:0,y:4},{x:1,y:2}];
    document.getElementById('t7XPred').value = '-1.5';
    document.getElementById('t7Grado').value = '2';
    document.querySelector('input[name="t7Mode"][value="ambos"]').checked = true;
    t7RenderDataTable();
    if (typeof t7UpdateGradoHint === 'function') t7UpdateGradoHint();
    const gh = document.getElementById('t7GradoHint');
    if (gh) gh.textContent = 'Modelo Cuadrático — usará los primeros 3 puntos de la tabla';
    clearAlert('t7Alert');
    showAlert('t7Alert','info','📋 Ejemplo Newton/Lagrange (cuadrático, 3 puntos). Presiona ▶ Interpolar.');
  });

  /* Ejemplo Lagrange (fotos 13-16: puntos (1,3) y (2,6)) */
  document.getElementById('btnT7EjLag')?.addEventListener('click', () => {
    t7State.data = [{x:1,y:3},{x:2,y:6}];
    document.getElementById('t7XPred').value = '1.5';
    document.getElementById('t7Grado').value = '1';
    document.querySelector('input[name="t7Mode"][value="lagrange"]').checked = true;
    t7RenderDataTable();
    const gh = document.getElementById('t7GradoHint');
    if (gh) gh.textContent = 'Modelo Lineal — usará los primeros 2 puntos de la tabla';
    clearAlert('t7Alert');
    showAlert('t7Alert','info','📋 Ejemplo Lagrange de clase — 2 puntos, grado 1. Presiona ▶ Interpolar.');
  });

  /* Mostrar/ocultar campos extra de Splines según modo */
  const t7ModeRadios = document.querySelectorAll('input[name="t7Mode"]');
  const t7SplExtra   = document.getElementById('t7SplExtra');
  const t7UpdateMode = () => {
    const mode = document.querySelector('input[name="t7Mode"]:checked')?.value;
    if (t7SplExtra) t7SplExtra.style.display = mode === 'splines' ? 'block' : 'none';
    /* Cambiar label del botón calcular */
    const btn = document.getElementById('btnT7Calcular');
    if (btn) btn.textContent = mode === 'splines' ? '▶ Construir Spline' : '▶ Interpolar';
  };
  t7ModeRadios.forEach(r => r.addEventListener('change', t7UpdateMode));
  window.t7UpdateMode = t7UpdateMode;
  t7UpdateMode();

  /* Actualizar hint de grado dinámicamente */
  const t7GradoSel = document.getElementById('t7Grado');
  const t7GradoHint = document.getElementById('t7GradoHint');
  const t7UpdateGradoHint = () => {
    const g = parseInt(t7GradoSel?.value || 3);
    const pts = g + 1;
    const nombres = ['','Lineal','Cuadrático','Cúbico','Cuártico','Quíntico'];
    if (t7GradoHint) t7GradoHint.textContent =
      `Modelo ${nombres[g] || 'Grado '+g} — usará los primeros ${pts} punto${pts>1?'s':''} de la tabla`;
  };
  t7GradoSel?.addEventListener('change', t7UpdateGradoHint);
  t7UpdateGradoHint();

  /* Botón Interpolar */
  document.getElementById('btnT7Calcular')?.addEventListener('click', () => {
    clearAlert('t7Alert');
    clearAlert('t7AlertGlobal');

    const pts   = t7ReadData();
    const xPred = parseFloat(document.getElementById('t7XPred')?.value);
    const mode  = document.querySelector('input[name="t7Mode"]:checked')?.value || 'ambos';

    /* ── Si modo = splines, derivar al flujo de Trazadores ── */
    if (mode === 'splines') {
      const xEvalSpl = parseFloat(document.getElementById('splXEval')?.value);
      if (pts.length < 3) { showAlert('t7Alert','danger','El spline cúbico necesita al menos 3 puntos.'); return; }
      if (isNaN(xEvalSpl)) { showAlert('t7Alert','danger','Ingresa el valor de x a evaluar para el spline.'); return; }
      const ptsSorted = [...pts].sort((a,b) => a.x - b.x);
      /* Verificar xᵢ distintos */
      for (let i=1; i<ptsSorted.length; i++) {
        if (ptsSorted[i].x <= ptsSorted[i-1].x) {
          showAlert('t7Alert','danger','Los xᵢ deben ser distintos entre sí.'); return;
        }
      }
      if (xEvalSpl < ptsSorted[0].x || xEvalSpl > ptsSorted[ptsSorted.length-1].x) {
        showAlert('t7Alert','warning',`⚠ x = ${xEvalSpl} está fuera del rango [${ptsSorted[0].x}, ${ptsSorted[ptsSorted.length-1].x}].`);
      }
      try {
        splState.data   = ptsSorted;
        const res = splCompute(ptsSorted, xEvalSpl);
        splState.result = res;
        splRenderHi(res);
        splRenderSistema(res);
        splRenderCoef(res);
        splRenderEval(res);
        splResetView();
        t7GoTo('t7-splines-hi');
        const dl = document.getElementById('t7-download-bar');
        if (dl) { dl.dataset.ready = '1'; dl.style.display = 'block'; }
        showAlert('t7AlertGlobal','success',
          `✓ Spline Cúbico Natural — ${res.n} tramos · S(${xEvalSpl}) = ${t7Fmt(res.yEval,8)} · Tramo S${res.tramIdx}`);
      } catch(e) { showAlert('t7Alert','danger','Error: ' + e.message); }
      return;
    }

    const grado  = parseInt(document.getElementById('t7Grado')?.value || 3);
    const nPts   = grado + 1;   /* puntos necesarios = grado + 1 */

    if (pts.length < 2) { showAlert('t7Alert','danger','Se necesitan al menos 2 puntos.'); return; }
    if (pts.length < nPts) {
      showAlert('t7Alert','danger',
        `Para un polinomio de grado ${grado} se necesitan ${nPts} puntos. Tienes ${pts.length} — agrega más puntos o reduce el grado.`);
      return;
    }
    if (isNaN(xPred)) { showAlert('t7Alert','danger','Ingresa el valor de x a predecir.'); return; }

    /* Tomar solo los primeros nPts puntos */
    const ptsUsados = pts.slice(0, nPts);

    /* Verificar xᵢ distintos entre los puntos usados */
    const xs = ptsUsados.map(p => p.x);
    const xSet = new Set(xs.map(v => v.toFixed(10)));
    if (xSet.size !== ptsUsados.length) {
      showAlert('t7Alert','danger','Los valores de xᵢ deben ser distintos entre sí.'); return;
    }

    try {
      t7State.xPred = xPred;
      t7State.grado = grado;
      t7State.newton   = null;
      t7State.lagrange = null;

      if (mode === 'newton' || mode === 'ambos') {
        t7State.newton = t7Newton(ptsUsados, xPred);
        t7RenderNewtonTabla(t7State.newton);
        t7RenderNewtonPol(t7State.newton);
      }
      if (mode === 'lagrange' || mode === 'ambos') {
        t7State.lagrange = t7Lagrange(ptsUsados, xPred);
        t7RenderLagBases(t7State.lagrange);
        t7RenderLagPol(t7State.lagrange, t7State.newton);
      }

      /* Download bar */
      const dl = document.getElementById('t7-download-bar');
      if (dl) dl.dataset.ready = '1';

      /* Resetear vista gráfica con puntos usados */
      t7State.data = ptsUsados;
      t7ResetView();

      /* Navegar a primera sección relevante */
      if (mode === 'newton' || mode === 'ambos') {
        t7GoTo('t7-newton-tabla');
      } else {
        t7GoTo('t7-lag-bases');
      }

      /* Alert global */
      const resVal = t7State.newton?.pred ?? t7State.lagrange?.pred;
      const nombres = ['','Lineal','Cuadrático','Cúbico','Cuártico','Quíntico'];
      showAlert('t7AlertGlobal','success',
        `✓ Modelo ${nombres[grado]||'Grado '+grado} — P${grado}(${xPred}) = ${t7Fmt(resVal,8)} · usando ${nPts} puntos`);

    } catch(e) { showAlert('t7Alert','danger','Error: ' + e.message); }
  });

  window.addEventListener('resize', () => { if (t7State.newton || t7State.lagrange) t7DrawGraph(); });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T7
══════════════════════════════════════════════════════════════ */
(function patchT7Export() {
  document.addEventListener('DOMContentLoaded', () => {
    if (typeof numerixExport === 'undefined') return;
    numerixExport.t7 = function() {
      const nr = t7State.newton, lr = t7State.lagrange;
      if (!nr && !lr) { alert('Ejecuta la interpolación primero.'); return; }
      const pts = t7State.data;
      const wb  = XLSX.utils.book_new();

      if (nr) {
        /* Hoja Newton: tabla de DD */
        const { n, xs, ys, dd, coefs, pred, xPred } = nr;
        const hdrDD = ['i','xi','f(xi)', ...Array.from({length:n-1},(_,j)=>`Orden ${j+1}`)];
        const rowsDD = xs.map((xi,i) => {
          const row = [i, xi, ys[i]];
          for (let j=1; j<n; j++) row.push(dd[i][j] !== null && i+j < n ? dd[i][j] : '');
          return row;
        });
        const info = [
          ['NUMERIX — Newton Diferencias Divididas','','© 2026 Fernando Granja & Alejandra Tinoco'],
          [], ['n puntos', n], ['Grado', n-1], ['x predecir', xPred],
          ['P(x)', pred],
          [], ['Coeficientes:'], ...coefs.map((c,j)=>[`a${j}`,c]),
        ];
        XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet([...info,[],[hdrDD],...rowsDD]), 'Newton DD');
      }

      if (lr) {
        /* Hoja Lagrange: bases */
        const { n, xs, ys, bases, pred, xPred } = lr;
        const hdrL = ['i','xi','f(xi)','Li(x)','f(xi)*Li(x)'];
        const rowsL = bases.map(b => [b.i, b.xi, b.yi, b.Li, b.contrib]);
        const sumR  = ['','','Suma P(x)','',pred];
        const infoL = [
          ['NUMERIX — Lagrange','','© 2026 Fernando Granja & Alejandra Tinoco'],
          [], ['n puntos', n], ['Grado', n-1], ['x predecir', xPred], ['P(x)', pred],
        ];
        XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet([...infoL,[],[hdrL],...rowsL,sumR]), 'Lagrange');
      }

      XLSX.writeFile(wb, `NUMERIX_T7_Interpolacion.xlsx`);
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TRAZADORES CÚBICOS NATURALES (CUBIC SPLINES)
   Integrado en T7 — Interpolación Polinomial
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const SPL_COLORS = ['#7c3aed','#0ea5e9','#10b981','#f59e0b','#ef4444','#8b5cf6','#06b6d4','#f97316'];

/* ── Estado Spline ──────────────────────────────────────────── */
const splState = {
  data:   [],     /* [{x,y}] ordenados */
  xEval:  null,
  result: null,   /* {n, xs, ys, hs, Ms, splines, xEval, yEval, tramIdx} */
  graph:  { canvas:null, ctx:null, xMin:-1, xMax:11, yMin:-1, yMax:12,
            dragging:false, lastMouse:{x:0,y:0}, hoverOn:false }
};

/* ══════════════════════════════════════════════════════════════
   TABLA DE DATOS DINÁMICA
══════════════════════════════════════════════════════════════ */
function splRenderTable() {
  const tb = document.getElementById('splDataBody');
  if (!tb) return;
  tb.innerHTML = splState.data.map((p, i) => `
    <tr>
      <td style="text-align:center;font-family:var(--font-mono);font-size:.8rem;
                 color:var(--gray-400);">${i}</td>
      <td><input type="number" class="t6-cell-input" id="spl_x_${i}"
          value="${p.x}" step="any" onchange="splUpdateCell(${i},'x',this.value)"/></td>
      <td><input type="number" class="t6-cell-input" id="spl_y_${i}"
          value="${p.y}" step="any" onchange="splUpdateCell(${i},'y',this.value)"/></td>
    </tr>`).join('');
}
function splUpdateCell(i,f,v){ if(splState.data[i]) splState.data[i][f]=parseFloat(v)||0; }
window.splUpdateCell = splUpdateCell;

function splReadData() {
  splState.data.forEach((p,i) => {
    const xe = document.getElementById(`spl_x_${i}`);
    const ye = document.getElementById(`spl_y_${i}`);
    if(xe) p.x = parseFloat(xe.value)||0;
    if(ye) p.y = parseFloat(ye.value)||0;
  });
  /* Ordenar por x ascendente */
  return [...splState.data].sort((a,b) => a.x - b.x);
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMO — SPLINE CÚBICO NATURAL
   Notación: n+1 puntos → n tramos → índices 0..n
   Mᵢ = S''(xᵢ) = segunda derivada en el nodo i
   Condición natural: M₀ = Mₙ = 0
══════════════════════════════════════════════════════════════ */
function splCompute(pts, xEval) {
  const n  = pts.length - 1;   /* número de tramos */
  const xs = pts.map(p => p.x);
  const ys = pts.map(p => p.y);

  /* ── Paso 1: hᵢ = xᵢ₊₁ − xᵢ ── */
  const hs = Array.from({length: n}, (_,i) => xs[i+1] - xs[i]);

  /* ── Paso 2: Sistema tridiagonal para M₁..Mₙ₋₁ ──
     Sistema de n-1 ecuaciones (nodos interiores)
     hᵢ₋₁·Mᵢ₋₁ + 2(hᵢ₋₁+hᵢ)·Mᵢ + hᵢ·Mᵢ₊₁ = 6·dᵢ
     donde dᵢ = (yᵢ₊₁−yᵢ)/hᵢ − (yᵢ−yᵢ₋₁)/hᵢ₋₁
     Con M₀ = Mₙ = 0 (condición natural) */

  const m  = n - 1;            /* tamaño del sistema interior */
  /* Diagonales del sistema tridiagonal */
  const diagA = new Array(m).fill(0); /* subdiagonal */
  const diagB = new Array(m).fill(0); /* diagonal principal */
  const diagC = new Array(m).fill(0); /* superdiagonal */
  const rhs   = new Array(m).fill(0); /* lado derecho */

  /* Guardar sistema original para mostrarlo */
  const sysRows = [];

  for (let k = 0; k < m; k++) {
    const i = k + 1;             /* nodo interior i=1..n-1 */
    diagA[k] = k > 0   ? hs[i-1] : 0;
    diagB[k] = 2 * (hs[i-1] + hs[i]);
    diagC[k] = k < m-1 ? hs[i]   : 0;
    rhs[k]   = 6 * ((ys[i+1] - ys[i]) / hs[i] - (ys[i] - ys[i-1]) / hs[i-1]);
    sysRows.push({
      i,
      hPrev: hs[i-1], hNext: hs[i],
      a: diagA[k], b: diagB[k], c: diagC[k], d: rhs[k]
    });
  }

  /* ── Resolver sistema tridiagonal — Algoritmo de Thomas ── */
  const Ms_inner = solveTridiagonal(diagA, diagB, diagC, rhs, m);

  /* M completo incluyendo extremos naturales M₀=0, Mₙ=0 */
  const Ms = [0, ...Ms_inner, 0];

  /* ── Paso 3: Calcular coeficientes aᵢ,bᵢ,cᵢ,dᵢ para cada tramo ── */
  const splines = Array.from({length: n}, (_,i) => {
    const hi = hs[i];
    const ai = ys[i];
    const bi = (ys[i+1] - ys[i]) / hi - hi * (2*Ms[i] + Ms[i+1]) / 6;
    const ci = Ms[i] / 2;
    const di = (Ms[i+1] - Ms[i]) / (6 * hi);
    return { i, x0: xs[i], x1: xs[i+1], ai, bi, ci, di, hi, Mi: Ms[i], Mi1: Ms[i+1] };
  });

  /* ── Paso 4: Evaluar S(xEval) en el tramo correcto ── */
  let tramIdx = n - 1;   /* por defecto último tramo */
  for (let i = 0; i < n; i++) {
    if (xEval >= xs[i] && xEval <= xs[i+1]) { tramIdx = i; break; }
  }
  const sp = splines[tramIdx];
  const dx = xEval - sp.x0;
  const yEval = sp.ai + sp.bi*dx + sp.ci*dx*dx + sp.di*dx*dx*dx;

  /* Guardar pasos de resolución Thomas */
  const thomasSteps = solveTridiagonalSteps(diagA.slice(), diagB.slice(), diagC.slice(), rhs.slice(), m);

  return { n, pts, xs, ys, hs, Ms, splines, xEval, yEval, tramIdx, sysRows, thomasSteps };
}

/* ── Algoritmo de Thomas (eliminación tridiagonal) ── */
function solveTridiagonal(a, b, c, d, m) {
  const B = [...b], D = [...d];
  /* Forward sweep */
  for (let i = 1; i < m; i++) {
    const w = a[i] / B[i-1];
    B[i] -= w * c[i-1];
    D[i] -= w * D[i-1];
  }
  /* Back substitution */
  const x = new Array(m).fill(0);
  x[m-1] = D[m-1] / B[m-1];
  for (let i = m-2; i >= 0; i--) {
    x[i] = (D[i] - c[i] * x[i+1]) / B[i];
  }
  return x;
}

/* ── Thomas con snapshots para mostrar pasos ── */
function solveTridiagonalSteps(a, b, c, d, m) {
  const steps = [];
  const B = [...b], D = [...d];
  steps.push({ label: 'Sistema original', rows: buildTriSnap(a,B,c,D,m) });

  for (let i = 1; i < m; i++) {
    const w = a[i] / B[i-1];
    B[i] -= w * c[i-1];
    D[i] -= w * D[i-1];
    steps.push({ label: `Eliminación fila ${i+1}: factor w = ${w.toFixed(4)}`, rows: buildTriSnap(a,B,c,D,m) });
  }

  const x = new Array(m).fill(0);
  x[m-1] = D[m-1] / B[m-1];
  steps.push({ label: `Back-sub: M${m} = ${x[m-1].toFixed(6)}`, rows: buildTriSnap(a,B,c,D,m), sols: [...x] });

  for (let i = m-2; i >= 0; i--) {
    x[i] = (D[i] - c[i] * x[i+1]) / B[i];
    steps.push({ label: `Back-sub: M${i+2} = ${x[i].toFixed(6)}`, rows: buildTriSnap(a,B,c,D,m), sols: [...x] });
  }
  return steps;
}

function buildTriSnap(a, b, c, d, m) {
  return Array.from({length: m}, (_,i) => ({ a: a[i], b: b[i], c: c[i], d: d[i] }));
}

/* ══════════════════════════════════════════════════════════════
   FORMATO
══════════════════════════════════════════════════════════════ */
const splFmt  = (v, d=6) => isNaN(v)?'—':Number(v).toFixed(d);
const splFmtC = v => { if(Math.abs(v)>9999||(Math.abs(v)<0.0001&&v!==0)) return v.toExponential(4); return parseFloat(Number(v).toFixed(8)).toString(); };

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — SECCIÓN 7: Intervalos hᵢ + Mᵢ segundas derivadas
══════════════════════════════════════════════════════════════ */
function splRenderHi(res) {
  const sec = document.getElementById('t7-splines-hi');
  if (!sec) return;
  const { n, xs, ys, hs, Ms } = res;

  let html = `
  <div class="page-header">
    <h2>Trazadores Cúbicos — Intervalos hᵢ</h2>
    <p>hᵢ = xᵢ₊₁ − xᵢ · Se calcula la longitud de cada subintervalo antes de armar el sistema.</p>
  </div>

  <!-- Tabla hᵢ -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t7-icon">hᵢ</div>
      <div>
        <div class="card-title">Tabla de intervalos — n = ${n} tramos · ${n+1} puntos</div>
        <div class="card-subtitle">hᵢ = xᵢ₊₁ − xᵢ para i = 0, 1, …, n−1</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.82rem;">
      <thead>
        <tr style="background:${T7_LIGHT};">
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">i</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">xᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">yᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">xᵢ₊₁</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">yᵢ₊₁</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;background:${T7_LIGHT};">hᵢ = xᵢ₊₁−xᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">(yᵢ₊₁−yᵢ)/hᵢ</th>
        </tr>
      </thead>
      <tbody>`;

  for (let i = 0; i < n; i++) {
    const slope = (ys[i+1]-ys[i])/hs[i];
    html += `<tr style="${i%2===1?'background:var(--gray-50)':''}">
      <td style="text-align:center;padding:.4rem .75rem;font-weight:700;color:${SPL_COLORS[i%SPL_COLORS.length]};">${i}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${splFmt(xs[i],4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${splFmt(ys[i],4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${splFmt(xs[i+1],4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${splFmt(ys[i+1],4)}</td>
      <td style="text-align:right;padding:.4rem .75rem;font-weight:700;color:${T7_COLOR};background:${T7_LIGHT};">${splFmt(hs[i],6)}</td>
      <td style="text-align:right;padding:.4rem .75rem;">${splFmt(slope,6)}</td>
    </tr>`;
  }
  /* Fila xₙ */
  html += `<tr style="background:var(--gray-50);">
    <td style="text-align:center;padding:.4rem .75rem;font-weight:700;color:var(--gray-400);">${n}</td>
    <td style="text-align:right;padding:.4rem .75rem;">${splFmt(xs[n],4)}</td>
    <td style="text-align:right;padding:.4rem .75rem;">${splFmt(ys[n],4)}</td>
    <td colspan="4" style="padding:.4rem .75rem;color:var(--gray-400);font-size:.75rem;">— último nodo —</td>
  </tr>`;

  html += `</tbody></table></div></div>

  <!-- Condición natural -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#f5f3ff);border:2px solid ${T7_COLOR}33;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🔑</div>
      <div>
        <div class="card-title">Condición Natural (Spline Natural)</div>
        <div class="card-subtitle">La segunda derivada es cero en los extremos → los extremos no tienen curvatura</div>
      </div>
    </div>
    <div style="padding:.75rem 1.25rem 1.25rem;display:flex;gap:1.5rem;flex-wrap:wrap;">
      <div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:${T7_COLOR};">
        M₀ = S''(x₀) = <span style="color:#10b981;">0</span>
      </div>
      <div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:${T7_COLOR};">
        M${n} = S''(x${n}) = <span style="color:#10b981;">0</span>
      </div>
    </div>
  </div>

  <div style="text-align:right;">
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-splines-sistema')">
      Siguiente: Sistema tridiagonal →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — SECCIÓN 8: Sistema tridiagonal + resolución Thomas
══════════════════════════════════════════════════════════════ */
function splRenderSistema(res) {
  const sec = document.getElementById('t7-splines-sistema');
  if (!sec) return;
  const { n, sysRows, thomasSteps, Ms } = res;

  let html = `
  <div class="page-header">
    <h2>Trazadores Cúbicos — Sistema Tridiagonal</h2>
    <p>Se plantea un sistema de ${n-1} ecuaciones para las segundas derivadas interiores M₁…M${n-1}.<br>
       Se resuelve con el <strong>Algoritmo de Thomas</strong> (eliminación tridiagonal eficiente).</p>
  </div>

  <!-- Ecuación general -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T7_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t7-icon">∑</div>
      <div>
        <div class="card-title">Ecuación General del Sistema</div>
        <div class="card-subtitle">Para cada nodo interior i = 1, 2, …, n−1</div>
      </div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.88rem;color:${T7_DARK};font-weight:600;">
        hᵢ₋₁·Mᵢ₋₁ + 2(hᵢ₋₁+hᵢ)·Mᵢ + hᵢ·Mᵢ₊₁ = 6·[(yᵢ₊₁−yᵢ)/hᵢ − (yᵢ−yᵢ₋₁)/hᵢ₋₁]
      </div>
      <div style="font-family:var(--font-main);font-size:.8rem;color:var(--gray-500);margin-top:.25rem;">
        Con M₀ = 0 y M${n} = 0 (condición natural)
      </div>
    </div>
  </div>

  <!-- Sistema numérico -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t7-icon">📋</div>
      <div>
        <div class="card-title">Sistema numérico [tridiagonal | b] — ${n-1} ecuaciones</div>
        <div class="card-subtitle">Incógnitas: M₁${n>2?', M₂'+( n>3?'...':'')+(n>2?', M'+(n-1):''):''}  (M₀=M${n}=0)</div>
      </div>
    </div>
    <div style="overflow-x:auto;padding:1rem 1.25rem;">
    <table style="border-collapse:separate;border-spacing:3px;font-family:var(--font-mono);font-size:.82rem;">
      <thead>
        <tr>
          <th style="padding:.4rem .65rem;background:${T7_LIGHT};color:${T7_DARK};border-radius:4px;">Ec.</th>
          <th style="padding:.4rem .65rem;background:${T7_LIGHT};color:${T7_DARK};border-radius:4px;">Sub-diag (hᵢ₋₁)</th>
          <th style="padding:.4rem .65rem;background:${T7_LIGHT};color:${T7_DARK};border-radius:4px;">Diag. princ 2(hᵢ₋₁+hᵢ)</th>
          <th style="padding:.4rem .65rem;background:${T7_LIGHT};color:${T7_DARK};border-radius:4px;">Super-diag (hᵢ)</th>
          <th style="padding:.4rem .65rem;background:${T7_LIGHT};color:${T7_DARK};border-radius:4px;border-left:2px solid ${T7_COLOR}44;">RHS</th>
        </tr>
      </thead>
      <tbody>`;

  sysRows.forEach((r,k) => {
    html += `<tr>
      <td style="padding:.35rem .65rem;background:${T7_LIGHT};border-radius:4px;font-weight:700;color:${T7_COLOR};">E${k+1} (M${r.i})</td>
      <td style="padding:.35rem .65rem;background:var(--gray-50);border-radius:4px;text-align:right;">${r.a !== 0 ? splFmt(r.a,4) : '—'}</td>
      <td style="padding:.35rem .65rem;background:var(--gray-50);border-radius:4px;text-align:right;font-weight:700;">${splFmt(r.b,4)}</td>
      <td style="padding:.35rem .65rem;background:var(--gray-50);border-radius:4px;text-align:right;">${r.c !== 0 ? splFmt(r.c,4) : '—'}</td>
      <td style="padding:.35rem .65rem;background:var(--gray-50);border-radius:4px;text-align:right;font-weight:700;color:${T7_DARK};border-left:2px solid ${T7_COLOR}44;">${splFmt(r.d,6)}</td>
    </tr>`;
  });
  html += `</tbody></table></div></div>

  <!-- Pasos Thomas -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid #0ea5e9;">
    <div class="card-header">
      <div class="card-header-icon" style="background:#0ea5e9;width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-size:.78rem;font-weight:700;">T</div>
      <div>
        <div class="card-title">Algoritmo de Thomas — Eliminación progresiva</div>
        <div class="card-subtitle">Resolución eficiente O(n) del sistema tridiagonal</div>
      </div>
    </div>
    <div style="padding:.75rem 1.25rem 1.25rem;display:flex;flex-direction:column;gap:.75rem;">`;

  thomasSteps.forEach((step, si) => {
    const isLast = si === thomasSteps.length - 1;
    html += `
    <div style="border-radius:var(--radius-sm);border:1px solid var(--border);
                border-left:4px solid ${isLast?'#10b981':'#0ea5e9'};
                padding:.5rem .875rem;background:var(--gray-50);">
      <div style="font-family:var(--font-main);font-size:.75rem;font-weight:700;
                  color:${isLast?'#065f46':'#0c4a6e'};margin-bottom:.3rem;">
        Paso ${si}: ${step.label}
      </div>
      <div style="font-family:var(--font-mono);font-size:.75rem;color:var(--gray-600);">
        [${step.rows.map(r=>`${splFmt(r.b,4)}M|${splFmt(r.d,4)}`).join('  ·  ')}]
        ${step.sols ? ' → M = ['+step.sols.map(v=>splFmt(v,6)).join(', ')+']' : ''}
      </div>
    </div>`;
  });

  /* Soluciones M finales */
  html += `</div></div>

  <!-- Mᵢ resultantes -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#f5f3ff);border:2px solid ${T7_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">✓</div>
      <div><div class="card-title">Segundas Derivadas Mᵢ = S''(xᵢ)</div></div>
    </div>
    <div style="display:flex;flex-wrap:wrap;gap:.625rem;padding:.5rem 1.25rem 1.25rem;">`;

  Ms.forEach((m,i) => {
    const isNatural = i===0 || i===Ms.length-1;
    html += `<div style="border-radius:var(--radius-sm);border:2px solid ${T7_COLOR}33;
                border-left:5px solid ${isNatural?'#10b981':T7_COLOR};
                padding:.5rem .875rem;background:var(--gray-50);min-width:120px;">
      <div style="font-size:.7rem;font-weight:700;color:${isNatural?'#065f46':T7_DARK};
                  font-family:var(--font-main);text-transform:uppercase;">
        M${i}${isNatural?' (natural)':''}
      </div>
      <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:700;
                  color:${isNatural?'#10b981':T7_COLOR};">
        ${splFmt(m,8)}
      </div>
    </div>`;
  });

  html += `</div></div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t7GoTo('t7-splines-hi')">← Intervalos hᵢ</button>
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-splines-coef')">Siguiente: Coeficientes →</button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — SECCIÓN 9: Coeficientes aᵢ,bᵢ,cᵢ,dᵢ
══════════════════════════════════════════════════════════════ */
function splRenderCoef(res) {
  const sec = document.getElementById('t7-splines-coef');
  if (!sec) return;
  const { n, splines } = res;

  let html = `
  <div class="page-header">
    <h2>Trazadores Cúbicos — Coeficientes por Tramo</h2>
    <p>Para cada tramo i: Sᵢ(x) = aᵢ + bᵢ(x−xᵢ) + cᵢ(x−xᵢ)² + dᵢ(x−xᵢ)³</p>
  </div>

  <!-- Fórmulas de coeficientes -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T7_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t7-icon">📐</div>
      <div><div class="card-title">Fórmulas de los coeficientes</div></div>
    </div>
    <div class="t6-step-body" style="font-family:var(--font-mono);font-size:.82rem;gap:.4rem;">
      <div>aᵢ = yᵢ</div>
      <div>bᵢ = (yᵢ₊₁−yᵢ)/hᵢ − hᵢ·(2Mᵢ + Mᵢ₊₁)/6</div>
      <div>cᵢ = Mᵢ/2</div>
      <div>dᵢ = (Mᵢ₊₁ − Mᵢ)/(6hᵢ)</div>
    </div>
  </div>

  <!-- Tabla de coeficientes -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t7-icon">📋</div>
      <div>
        <div class="card-title">Tabla de coeficientes — ${n} tramos</div>
        <div class="card-subtitle">Sᵢ(x) = aᵢ + bᵢ(x−xᵢ) + cᵢ(x−xᵢ)² + dᵢ(x−xᵢ)³</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.78rem;">
      <thead>
        <tr style="background:${T7_LIGHT};">
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">Tramo</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">Intervalo</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">aᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">bᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">cᵢ</th>
          <th style="padding:.5rem .75rem;color:${T7_DARK};border-bottom:2px solid ${T7_COLOR}33;">dᵢ</th>
        </tr>
      </thead>
      <tbody>`;

  splines.forEach((sp, i) => {
    const col = SPL_COLORS[i % SPL_COLORS.length];
    html += `<tr style="${i%2===1?'background:var(--gray-50)':''}">
      <td style="padding:.4rem .75rem;font-weight:700;color:${col};">S${i}(x)</td>
      <td style="padding:.4rem .75rem;">[${splFmt(sp.x0,4)}, ${splFmt(sp.x1,4)}]</td>
      <td style="padding:.4rem .75rem;text-align:right;">${splFmt(sp.ai,8)}</td>
      <td style="padding:.4rem .75rem;text-align:right;">${splFmt(sp.bi,8)}</td>
      <td style="padding:.4rem .75rem;text-align:right;">${splFmt(sp.ci,8)}</td>
      <td style="padding:.4rem .75rem;text-align:right;">${splFmt(sp.di,8)}</td>
    </tr>`;
  });

  html += `</tbody></table></div></div>

  <!-- Polinomios explícitos -->
  <div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">Sᵢ</div>
      <div><div class="card-title">Polinomios cúbicos explícitos por tramo</div></div>
    </div>
    <div style="padding:.75rem 1.25rem 1.25rem;display:flex;flex-direction:column;gap:.5rem;">`;

  splines.forEach((sp, i) => {
    const col = SPL_COLORS[i % SPL_COLORS.length];
    const x0s = sp.x0 === 0 ? '' : sp.x0 < 0 ? `+${splFmtC(Math.abs(sp.x0))}` : `−${splFmtC(sp.x0)}`;
    const signB = sp.bi >= 0 ? `+ ${splFmtC(sp.bi)}` : `− ${splFmtC(Math.abs(sp.bi))}`;
    const signC = sp.ci >= 0 ? `+ ${splFmtC(sp.ci)}` : `− ${splFmtC(Math.abs(sp.ci))}`;
    const signD = sp.di >= 0 ? `+ ${splFmtC(sp.di)}` : `− ${splFmtC(Math.abs(sp.di))}`;
    html += `
    <div style="border-left:4px solid ${col};padding:.5rem .875rem;background:var(--gray-50);
                border-radius:0 var(--radius-sm) var(--radius-sm) 0;
                font-family:var(--font-mono);font-size:.78rem;">
      <span style="color:${col};font-weight:700;">S${i}(x)</span>
      <span style="color:var(--gray-400);font-size:.7rem;"> [${splFmt(sp.x0,4)} ≤ x ≤ ${splFmt(sp.x1,4)}]</span><br>
      <span style="color:var(--gray-600);">
        = ${splFmtC(sp.ai)} ${signB}·(x${x0s}) ${signC}·(x${x0s})² ${signD}·(x${x0s})³
      </span>
    </div>`;
  });

  html += `</div></div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t7GoTo('t7-splines-sistema')">← Sistema</button>
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-splines-eval')">Siguiente: Evaluación →</button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — SECCIÓN 10: Evaluación S(x)
══════════════════════════════════════════════════════════════ */
function splRenderEval(res) {
  const sec = document.getElementById('t7-splines-eval');
  if (!sec) return;
  const { n, splines, xEval, yEval, tramIdx, Ms } = res;
  const sp  = splines[tramIdx];
  const col = SPL_COLORS[tramIdx % SPL_COLORS.length];
  const dx  = xEval - sp.x0;

  let html = `
  <div class="page-header">
    <h2>Trazadores Cúbicos — Evaluación S(${xEval})</h2>
    <p>Se identifica el tramo correcto y se evalúa el polinomio cúbico correspondiente.</p>
  </div>

  <!-- Identificación de tramo -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${col};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${col};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">S${tramIdx}</div>
      <div>
        <div class="card-title">Tramo seleccionado: S${tramIdx}(x)</div>
        <div class="card-subtitle">x = ${xEval} ∈ [${splFmt(sp.x0,4)}, ${splFmt(sp.x1,4)}]</div>
      </div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.85rem;color:var(--gray-600);">
        Identificación: ${splFmt(sp.x0,4)} ≤ ${xEval} ≤ ${splFmt(sp.x1,4)} ✓
      </div>
      <div style="font-family:var(--font-mono);font-size:.85rem;">
        Δx = x − x${tramIdx} = ${xEval} − ${splFmt(sp.x0,4)} = <strong style="color:${col};">${splFmt(dx,6)}</strong>
      </div>
    </div>
  </div>

  <!-- Sustitución paso a paso -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T7_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🔢</div>
      <div><div class="card-title">Sustitución numérica</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.82rem;color:var(--gray-500);">
        S${tramIdx}(x) = a${tramIdx} + b${tramIdx}·Δx + c${tramIdx}·Δx² + d${tramIdx}·Δx³
      </div>
      <div style="font-family:var(--font-mono);font-size:.82rem;background:var(--gray-50);
                  border-radius:var(--radius-sm);padding:.5rem .75rem;">
        <div>a${tramIdx} = <strong>${splFmt(sp.ai,8)}</strong></div>
        <div>b${tramIdx}·Δx = ${splFmt(sp.bi,8)} × ${splFmt(dx,6)} = <strong>${splFmt(sp.bi*dx,8)}</strong></div>
        <div>c${tramIdx}·Δx² = ${splFmt(sp.ci,8)} × ${splFmt(dx*dx,6)} = <strong>${splFmt(sp.ci*dx*dx,8)}</strong></div>
        <div>d${tramIdx}·Δx³ = ${splFmt(sp.di,8)} × ${splFmt(dx*dx*dx,6)} = <strong>${splFmt(sp.di*dx*dx*dx,8)}</strong></div>
      </div>
      <div style="font-family:var(--font-mono);font-size:.88rem;margin-top:.25rem;">
        Suma = ${splFmt(sp.ai,6)} + ${splFmt(sp.bi*dx,6)} + ${splFmt(sp.ci*dx*dx,6)} + ${splFmt(sp.di*dx*dx*dx,6)}
      </div>
    </div>
  </div>

  <!-- Resultado -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T7_LIGHT},#f5f3ff);border:2px solid ${T7_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t7-icon">🎯</div>
      <div><div class="card-title">Resultado</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;text-align:center;">
      <div style="font-family:var(--font-mono);font-size:1.4rem;font-weight:700;color:${T7_COLOR};">
        S(${xEval}) = S${tramIdx}(${xEval}) = <span style="color:${col};">${splFmt(yEval,8)}</span>
      </div>
      <div style="font-family:var(--font-main);font-size:.8rem;color:var(--gray-400);margin-top:.5rem;">
        Evaluado con el tramo ${tramIdx} en el intervalo [${splFmt(sp.x0,4)}, ${splFmt(sp.x1,4)}]
      </div>
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t7GoTo('t7-splines-coef')">← Coeficientes</button>
    <button class="btn t7-btn-primary" onclick="t7GoTo('t7-splines-grafica');setTimeout(splDrawGraph,80);">
      📈 Ver Gráfica →
    </button>
  </div>`;
  sec.innerHTML = html;
}

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA — SPLINES
══════════════════════════════════════════════════════════════ */
function splInitGraph() {
  const g = splState.graph;
  const c = document.getElementById('splCanvas');
  if (!c || g.canvas) return;
  g.canvas = c; g.ctx = c.getContext('2d');

  const resize = () => {
    const w = c.parentElement.clientWidth || 700;
    c.width = w; c.height = Math.max(340, Math.round(w * 0.52));
    splDrawGraph();
  };
  resize();
  window.addEventListener('resize', resize);

  c.addEventListener('mousedown', e => { g.dragging=true; g.lastMouse={x:e.clientX,y:e.clientY}; c.style.cursor='grabbing'; });
  c.addEventListener('mouseup',   () => { g.dragging=false; c.style.cursor='crosshair'; });
  c.addEventListener('mouseleave',() => { g.dragging=false; g.hoverOn=false; c.style.cursor='crosshair';
    const tip=document.getElementById('splTooltip'); if(tip) tip.style.display='none'; splDrawGraph(); });
  c.addEventListener('mousemove', e => {
    const rect=c.getBoundingClientRect();
    const px=(e.clientX-rect.left)*(c.width/rect.width);
    const py=(e.clientY-rect.top)*(c.height/rect.height);
    const mw=splToWorld(px,py);
    g.hoverOn=true;
    const coord=document.getElementById('splCoords');
    if(coord) coord.innerHTML=`x = ${mw.x.toFixed(3)} &nbsp; y = ${mw.y.toFixed(3)}`;
    if(g.dragging){
      const dx=(e.clientX-g.lastMouse.x)/rect.width*(g.xMax-g.xMin);
      const dy=(e.clientY-g.lastMouse.y)/rect.height*(g.yMax-g.yMin);
      g.xMin-=dx; g.xMax-=dx; g.yMin+=dy; g.yMax+=dy;
      g.lastMouse={x:e.clientX,y:e.clientY};
    }
    splDrawGraph();
  });
  c.addEventListener('wheel', e => {
    e.preventDefault();
    const f=e.deltaY>0?1.12:0.89;
    const rect=c.getBoundingClientRect();
    const {x:wx,y:wy}=splToWorld((e.clientX-rect.left)*(c.width/rect.width),(e.clientY-rect.top)*(c.height/rect.height));
    g.xMin=wx+(g.xMin-wx)*f; g.xMax=wx+(g.xMax-wx)*f;
    g.yMin=wy+(g.yMin-wy)*f; g.yMax=wy+(g.yMax-wy)*f;
    splDrawGraph();
  }, {passive:false});
}

function splToCanvas(wx,wy) {
  const g=splState.graph, PAD={t:24,r:24,b:44,l:60};
  const W=g.canvas.width, H=g.canvas.height;
  return {
    x: PAD.l+(wx-g.xMin)/(g.xMax-g.xMin)*(W-PAD.l-PAD.r),
    y: PAD.t+(1-(wy-g.yMin)/(g.yMax-g.yMin))*(H-PAD.t-PAD.b)
  };
}
function splToWorld(px,py) {
  const g=splState.graph, PAD={t:24,r:24,b:44,l:60};
  const W=g.canvas.width, H=g.canvas.height;
  return {
    x: g.xMin+(px-PAD.l)/(W-PAD.l-PAD.r)*(g.xMax-g.xMin),
    y: g.yMin+(1-(py-PAD.t)/(H-PAD.t-PAD.b))*(g.yMax-g.yMin)
  };
}

function splDrawGraph() {
  const g   = splState.graph;
  const res = splState.result;
  if (!g.canvas || !res) return;
  const { splines, xEval, yEval, tramIdx } = res;

  const isDark = document.body.classList.contains('dark-mode');
  const W=g.canvas.width, H=g.canvas.height, ctx=g.ctx;
  const PAD={t:24,r:24,b:44,l:60};
  const PW=W-PAD.l-PAD.r, PH=H-PAD.t-PAD.b;
  const niceStep = (range,tgt) => {
    const r=range/tgt, m=Math.pow(10,Math.floor(Math.log10(r)));
    const n=r/m; return (n<1.5?1:n<3.5?2:n<7.5?5:10)*m;
  };

  ctx.fillStyle = isDark?'#0f172a':'#fff';
  ctx.fillRect(0,0,W,H);

  /* Grid */
  const xSt=niceStep(g.xMax-g.xMin,10), ySt=niceStep(g.yMax-g.yMin,8);
  ctx.strokeStyle=isDark?'rgba(148,163,184,.08)':'#f1f5f9'; ctx.lineWidth=1;
  for(let gx=Math.ceil(g.xMin/xSt)*xSt; gx<=g.xMax; gx+=xSt){
    const{x:px}=splToCanvas(gx,0); ctx.beginPath(); ctx.moveTo(px,PAD.t); ctx.lineTo(px,PAD.t+PH); ctx.stroke();
  }
  for(let gy=Math.ceil(g.yMin/ySt)*ySt; gy<=g.yMax; gy+=ySt){
    const{y:py}=splToCanvas(0,gy); ctx.beginPath(); ctx.moveTo(PAD.l,py); ctx.lineTo(PAD.l+PW,py); ctx.stroke();
  }

  /* Ejes */
  ctx.strokeStyle=isDark?'rgba(148,163,184,.3)':'#cbd5e1'; ctx.lineWidth=1.5;
  const{y:axY}=splToCanvas(0,0), {x:axX}=splToCanvas(0,0);
  if(g.yMin<=0&&g.yMax>=0){ctx.beginPath();ctx.moveTo(PAD.l,axY);ctx.lineTo(PAD.l+PW,axY);ctx.stroke();}
  if(g.xMin<=0&&g.xMax>=0){ctx.beginPath();ctx.moveTo(axX,PAD.t);ctx.lineTo(axX,PAD.t+PH);ctx.stroke();}

  /* Labels */
  ctx.fillStyle=isDark?'rgba(148,163,184,.6)':'#94a3b8';
  ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
  const lbY=Math.max(PAD.t+10,Math.min(PAD.t+PH-4,axY+16));
  const lbX=Math.max(PAD.l+28,Math.min(PAD.l+PW-4,axX-8));
  for(let gx=Math.ceil(g.xMin/xSt)*xSt;gx<=g.xMax;gx+=xSt){
    if(Math.abs(gx)<xSt*.01)continue;
    const{x:px}=splToCanvas(gx,0); ctx.fillText(gx%1===0?gx:gx.toFixed(1),px,lbY);
  }
  ctx.textAlign='right';
  for(let gy=Math.ceil(g.yMin/ySt)*ySt;gy<=g.yMax;gy+=ySt){
    if(Math.abs(gy)<ySt*.01)continue;
    const{y:py}=splToCanvas(0,gy); ctx.fillText(gy%1===0?gy:gy.toFixed(1),lbX,py);
  }
  ctx.textBaseline='alphabetic';

  /* Curva spline — cada tramo con su color */
  const STEPS = 120;
  splines.forEach((sp, si) => {
    const col = SPL_COLORS[si % SPL_COLORS.length];
    ctx.beginPath(); ctx.strokeStyle=col; ctx.lineWidth=2.5; ctx.setLineDash([]);
    const dx2 = (sp.x1 - sp.x0) / STEPS;
    let first = true;
    for(let k=0; k<=STEPS; k++){
      const wx = sp.x0 + k*dx2;
      const dx = wx - sp.x0;
      const wy = sp.ai + sp.bi*dx + sp.ci*dx*dx + sp.di*dx*dx*dx;
      if(!isFinite(wy)) { first=true; continue; }
      const {x:px,y:py}=splToCanvas(wx,wy);
      if(first){ctx.moveTo(px,py);first=false;}else ctx.lineTo(px,py);
    }
    ctx.stroke();

    /* Línea vertical en nodo de unión */
    if(si < splines.length-1){
      const {x:nx,y:ny}=splToCanvas(sp.x1,0);
      ctx.save();
      ctx.strokeStyle=isDark?'rgba(148,163,184,.2)':'rgba(0,0,0,.1)';
      ctx.lineWidth=1; ctx.setLineDash([3,3]);
      ctx.beginPath(); ctx.moveTo(nx,PAD.t); ctx.lineTo(nx,PAD.t+PH); ctx.stroke();
      ctx.restore();
    }
  });

  /* Puntos de datos */
  res.pts.forEach((p,i) => {
    const{x:px,y:py}=splToCanvas(p.x,p.y);
    if(px<PAD.l-8||px>PAD.l+PW+8||py<PAD.t-8||py>PAD.t+PH+8) return;
    ctx.beginPath(); ctx.arc(px,py,5.5,0,Math.PI*2);
    ctx.fillStyle=T7_COLOR; ctx.fill();
    ctx.strokeStyle='#fff'; ctx.lineWidth=1.5; ctx.stroke();
    ctx.fillStyle=isDark?'#e2e8f0':'#374151';
    ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center';
    ctx.textBaseline='alphabetic';
    ctx.fillText(`(${p.x},${p.y})`,px,py-10);
  });

  /* Punto evaluado */
  if(isFinite(yEval)){
    const{x:epx,y:epy}=splToCanvas(xEval,yEval);
    ctx.beginPath(); ctx.arc(epx,epy,7,0,Math.PI*2);
    ctx.fillStyle='#ef4444'; ctx.fill();
    ctx.strokeStyle='#fff'; ctx.lineWidth=2; ctx.stroke();
    ctx.fillStyle='#ef4444'; ctx.font='bold 11px "Poppins",sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='alphabetic';
    ctx.fillText(`S(${xEval})=${yEval.toFixed(4)}`,epx,epy-13);
  }

  /* Leyenda de tramos */
  ctx.textBaseline='middle'; ctx.font='10px "Poppins",sans-serif';
  let lx=PAD.l+6, ly=PAD.t+12;
  splines.forEach((sp,si) => {
    if(lx > PAD.l+PW-60) return;
    const col=SPL_COLORS[si%SPL_COLORS.length];
    ctx.strokeStyle=col; ctx.lineWidth=2.5; ctx.setLineDash([]);
    ctx.beginPath(); ctx.moveTo(lx,ly); ctx.lineTo(lx+18,ly); ctx.stroke();
    ctx.fillStyle=isDark?'#e2e8f0':'#374151'; ctx.textAlign='left';
    ctx.fillText(`S${si}`,lx+22,ly); lx+=50;
  });
  ctx.textBaseline='alphabetic';

  /* Watermark */
  ctx.fillStyle=isDark?'rgba(124,58,237,.15)':'rgba(148,163,184,.4)';
  ctx.font='600 11px "Poppins",sans-serif'; ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.textBaseline='alphabetic';
}
window.splDrawGraph = splDrawGraph;

function splZoom(f) {
  const g=splState.graph;
  const cx=(g.xMin+g.xMax)/2, cy=(g.yMin+g.yMax)/2;
  const hw=(g.xMax-g.xMin)/2*f, hh=(g.yMax-g.yMin)/2*f;
  g.xMin=cx-hw; g.xMax=cx+hw; g.yMin=cy-hh; g.yMax=cy+hh;
  splDrawGraph();
}
window.splZoom = splZoom;

function splResetView() {
  const pts = splState.result?.pts || splState.data;
  if (!pts.length) return;
  const xs=pts.map(p=>p.x), ys=pts.map(p=>p.y);
  const xr=Math.max(...xs)-Math.min(...xs)||2;
  const yr=Math.max(...ys)-Math.min(...ys)||2;
  const g=splState.graph;
  g.xMin=Math.min(...xs)-xr*.15; g.xMax=Math.max(...xs)+xr*.15;
  g.yMin=Math.min(...ys)-yr*.25; g.yMax=Math.max(...ys)+yr*.25;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL — BOTÓN CONSTRUIR SPLINE
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Datos iniciales */
  splState.data = [{x:1,y:1},{x:2,y:0.5},{x:3,y:0.333},{x:4,y:0.25}];
  splRenderTable();

  /* Agregar / quitar filas */
  document.getElementById('btnSplAddRow')?.addEventListener('click', () => {
    splState.data.push({x:0,y:0}); splRenderTable();
  });
  document.getElementById('btnSplRemRow')?.addEventListener('click', () => {
    if(splState.data.length>3){ splState.data.pop(); splRenderTable(); }
  });

  /* Ejemplo 1 — 4 puntos clásico (1,1)(2,½)(3,⅓)(4,¼) */
  document.getElementById('btnSplEj1')?.addEventListener('click', () => {
    t7State.data = [{x:1,y:1},{x:2,y:0.5},{x:3,y:0.333333},{x:4,y:0.25}];
    document.getElementById('splXEval').value = '1.5';
    document.querySelector('input[name="t7Mode"][value="splines"]').checked = true;
    t7RenderDataTable();
    t7UpdateMode();
    clearAlert('t7Alert');
    showAlert('t7Alert','info','📋 Ejemplo 1 — f(x)=1/x en [1,4] · 4 puntos. Presiona ▶ Construir Spline.');
  });

  /* Ejemplo 2 — 5 puntos (2,5)(4,6)(5,9)(8,5)(10,4) */
  document.getElementById('btnSplEj2')?.addEventListener('click', () => {
    t7State.data = [{x:2,y:5},{x:4,y:6},{x:5,y:9},{x:8,y:5},{x:10,y:4}];
    document.getElementById('splXEval').value = '3';
    document.querySelector('input[name="t7Mode"][value="splines"]').checked = true;
    t7RenderDataTable();
    t7UpdateMode();
    clearAlert('t7Alert');
    showAlert('t7Alert','info','📋 Ejemplo 2 — 5 puntos, 4 tramos. Presiona ▶ Construir Spline.');
  });

  /* btnSplCalc eliminado — el flujo ahora pasa por btnT7Calcular con mode=splines */

  /* Resize gráfica */
  window.addEventListener('resize', () => { if(splState.result) splDrawGraph(); });
});

/* ── Parchar dark mode para Splines ── */
(function() {
  const orig = window.applyTheme;
  if(orig) return; /* ya parchado desde script principal */
})();

/* ══════════════════════════════════════════════════════════════
   PARCHAR EXPORTACIÓN EXCEL T7 para incluir Splines
══════════════════════════════════════════════════════════════ */
(function patchT7SplExport() {
  document.addEventListener('DOMContentLoaded', () => {
    if(typeof numerixExport === 'undefined') return;
    const prev = numerixExport.t7;
    numerixExport.t7 = function() {
      /* Correr exportación previa (Newton + Lagrange) */
      if(prev) {
        try{ prev(); return; } catch(e){}
      }
    };

    /* Exportación independiente Splines */
    numerixExport.t7spl = function() {
      const res = splState.result;
      if(!res){ alert('Construye el spline primero.'); return; }
      const wb = XLSX.utils.book_new();

      /* Hoja 1: Resumen */
      const info = [
        ['NUMERIX — Trazadores Cúbicos Naturales','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],
        ['n+1 puntos', res.pts.length], ['n tramos', res.n],
        ['x evaluado', res.xEval], ['S(x)', res.yEval],
        ['Tramo usado', `S${res.tramIdx}`],
        [],
        ['PUNTOS DE DATOS'],['i','xi','yi'],
        ...res.pts.map((p,i) => [i, p.x, p.y]),
        [],
        ['SEGUNDAS DERIVADAS Mᵢ'],['i','Mᵢ = S\'\'(xᵢ)'],
        ...res.Ms.map((m,i) => [i, m]),
      ];
      XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet(info), 'Resumen');

      /* Hoja 2: Coeficientes */
      const hdrC = ['Tramo','x_ini','x_fin','aᵢ','bᵢ','cᵢ','dᵢ'];
      const rowsC = res.splines.map(sp => [
        `S${sp.i}`, sp.x0, sp.x1, sp.ai, sp.bi, sp.ci, sp.di
      ]);
      XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet([hdrC,...rowsC]), 'Coeficientes');

      XLSX.writeFile(wb, `NUMERIX_T7_SplinesCubicos.xlsx`);
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 8 — DIFERENCIACIÓN NUMÉRICA
   Diferencias Finitas Adelante · Atrás · Central
   Segunda Derivada · Extrapolación de Richardson
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T8_COLOR  = '#ea580c';
const T8_LIGHT  = '#fff7ed';
const T8_DARK   = '#9a3412';

/* ── Estado T8 ──────────────────────────────────────────────── */
const t8State = {
  mode:     'funcion',   /* 'funcion' | 'tabla' */
  fx:       'sin(x)',
  fxExacta: 'cos(x)',
  x0:       0,
  h:        0.2,
  tableData: [],
  result:   null
};

/* ══════════════════════════════════════════════════════════════
   EVALUACIÓN SEGURA DE f(x)
══════════════════════════════════════════════════════════════ */
function t8Eval(expr, x) {
  try {
    const fn = new Function('x','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict"; return (${expr});`);
    return fn(x, Math.PI, Math.sin, Math.cos, Math.tan, Math.exp, Math.log, Math.sqrt, Math.pow, Math.abs);
  } catch(e) { return NaN; }
}

/* ══════════════════════════════════════════════════════════════
   NAVEGACIÓN INTERNA T8
══════════════════════════════════════════════════════════════ */
function t8GoTo(secId) {
  document.querySelectorAll('.t8-sec').forEach(s => s.style.display = 'none');
  document.querySelectorAll('.t8-nav').forEach(n => n.classList.remove('active'));
  const sec = document.getElementById(secId);
  if (sec) sec.style.display = 'block';
  document.querySelectorAll(`[data-t8="${secId}"]`).forEach(el => el.classList.add('active'));
  const dl = document.getElementById('t8-download-bar');
  if (dl && dl.dataset.ready === '1' && secId !== 't8-input') dl.style.display = 'block';
}
window.t8GoTo = t8GoTo;

/* ══════════════════════════════════════════════════════════════
   TABLA DE DATOS DINÁMICA
══════════════════════════════════════════════════════════════ */
function t8RenderTable() {
  const tb = document.getElementById('t8DataBody');
  if (!tb) return;
  tb.innerHTML = t8State.tableData.map((p, i) => `
    <tr>
      <td style="text-align:center;font-family:var(--font-mono);font-size:.8rem;color:var(--gray-400);">${i}</td>
      <td><input type="number" class="t6-cell-input" id="t8_x_${i}" value="${p.x}" step="any"
          onchange="t8UpdateCell(${i},'x',this.value)"/></td>
      <td><input type="number" class="t6-cell-input" id="t8_y_${i}" value="${p.y}" step="any"
          onchange="t8UpdateCell(${i},'y',this.value)"/></td>
    </tr>`).join('');
}
function t8UpdateCell(i,f,v){ if(t8State.tableData[i]) t8State.tableData[i][f]=parseFloat(v)||0; }
window.t8UpdateCell = t8UpdateCell;

function t8ReadTable() {
  t8State.tableData.forEach((p,i) => {
    const xe = document.getElementById(`t8_x_${i}`);
    const ye = document.getElementById(`t8_y_${i}`);
    if(xe) p.x = parseFloat(xe.value)||0;
    if(ye) p.y = parseFloat(ye.value)||0;
  });
  return [...t8State.tableData].sort((a,b) => a.x - b.x);
}

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS — DIFERENCIAS FINITAS
══════════════════════════════════════════════════════════════ */

/** Obtener f(x0-h), f(x0), f(x0+h) según modo */
function t8GetVals(x0, h) {
  if (t8State.mode === 'funcion') {
    return {
      fxMH: t8Eval(t8State.fx, x0 - h),
      fx0:  t8Eval(t8State.fx, x0),
      fxPH: t8Eval(t8State.fx, x0 + h),
      fxPH2: t8Eval(t8State.fx, x0 + h/2),
      fxMH2: t8Eval(t8State.fx, x0 - h/2),
    };
  } else {
    /* Modo tabla: buscar los valores por interpolación lineal */
    const pts = t8ReadTable();
    const interp = (xTarget) => {
      /* Buscar exacto primero */
      const exact = pts.find(p => Math.abs(p.x - xTarget) < 1e-10);
      if (exact) return exact.y;
      /* Interpolar lineal entre los dos más cercanos */
      let lo = null, hi = null;
      for (const p of pts) {
        if (p.x <= xTarget) lo = p;
        if (p.x >= xTarget && !hi) hi = p;
      }
      if (lo && hi && lo !== hi) {
        return lo.y + (hi.y - lo.y) * (xTarget - lo.x) / (hi.x - lo.x);
      }
      return NaN;
    };
    return {
      fxMH:  interp(x0 - h),
      fx0:   interp(x0),
      fxPH:  interp(x0 + h),
      fxPH2: interp(x0 + h/2),
      fxMH2: interp(x0 - h/2),
    };
  }
}

function t8Compute(x0, h) {
  const v = t8GetVals(x0, h);
  const { fxMH, fx0, fxPH, fxPH2, fxMH2 } = v;

  /* Primera derivada */
  const adelante  = (fxPH - fx0)         / h;
  const atras     = (fx0  - fxMH)        / h;
  const central   = (fxPH - fxMH)        / (2*h);

  /* Segunda derivada */
  const segunda   = (fxPH - 2*fx0 + fxMH) / (h*h);

  /* Richardson: R = [4f(h/2) - f(h)] / 3
     f(h)   = diferencia central con paso h
     f(h/2) = diferencia central con paso h/2  */
  const centralH2   = (t8Eval(t8State.fx, x0+h/2) - t8Eval(t8State.fx, x0-h/2)) / h;
  const richardson  = (4*centralH2 - central) / 3;

  /* Valor exacto (solo modo función) */
  let exacto = null, errAd = null, errAt = null, errCen = null, errRich = null;
  if (t8State.mode === 'funcion' && t8State.fxExacta.trim()) {
    exacto  = t8Eval(t8State.fxExacta, x0);
    errAd   = Math.abs(exacto - adelante);
    errAt   = Math.abs(exacto - atras);
    errCen  = Math.abs(exacto - central);
    errRich = Math.abs(exacto - richardson);
  }

  return {
    x0, h, v,
    adelante, atras, central, segunda, richardson,
    exacto, errAd, errAt, errCen, errRich,
    centralH2
  };
}

/* ══════════════════════════════════════════════════════════════
   FORMATO
══════════════════════════════════════════════════════════════ */
const t8Fmt  = (v,d=8) => (v===null||v===undefined||isNaN(v)) ? '—' : Number(v).toFixed(d);
const t8FmtE = (v) => (v===null||v===undefined||isNaN(v)) ? '—' : v.toExponential(4);

/* ══════════════════════════════════════════════════════════════
   HELPER: renderizar una sección de diferencia
══════════════════════════════════════════════════════════════ */
function t8RenderDif(secId, title, formula, sustitucion, resultado, error, exacto, nextSec, prevSec, color) {
  const sec = document.getElementById(secId);
  if (!sec) return;

  const errBlock = (exacto !== null && !isNaN(exacto)) ? `
    <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:.75rem;margin-top:1rem;">
      <div class="t8-metric-card" style="border-left-color:${color};">
        <div class="t8-metric-label">Valor aproximado</div>
        <div class="t8-metric-val" style="color:${color};">${t8Fmt(resultado)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#10b981;">
        <div class="t8-metric-label">Valor exacto f'(x₀)</div>
        <div class="t8-metric-val" style="color:#10b981;">${t8Fmt(exacto)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#ef4444;">
        <div class="t8-metric-label">Error absoluto |ε|</div>
        <div class="t8-metric-val" style="color:#ef4444;">${t8FmtE(error)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#f59e0b;">
        <div class="t8-metric-label">Error relativo</div>
        <div class="t8-metric-val" style="color:#f59e0b;">${exacto !== 0 ? t8Fmt(Math.abs(error/exacto)*100,4)+'%' : '—'}</div>
      </div>
    </div>` : `
    <div style="display:inline-flex;align-items:center;gap:1rem;margin-top:.75rem;">
      <div style="background:${color}15;border:2px solid ${color}33;border-radius:var(--radius-sm);
                  padding:.75rem 1.5rem;text-align:center;">
        <div style="font-family:var(--font-main);font-size:.72rem;font-weight:700;color:${color};
                    text-transform:uppercase;margin-bottom:.25rem;">f'(x₀) ≈</div>
        <div style="font-family:var(--font-mono);font-size:1.3rem;font-weight:700;color:${color};">
          ${t8Fmt(resultado)}
        </div>
      </div>
    </div>`;

  sec.innerHTML = `
  <div class="page-header">
    <h2>${title}</h2>
    <p>Aproximación de la primera derivada en x₀ = ${t8State.x0} con h = ${t8State.h}</p>
  </div>

  <!-- Fórmula general -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${color};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${color};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-size:.85rem;font-weight:700;">f'</div>
      <div><div class="card-title">Fórmula general</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:600;color:${color};">
        ${formula}
      </div>
    </div>
  </div>

  <!-- Sustitución numérica -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T8_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🔢</div>
      <div><div class="card-title">Sustitución numérica</div></div>
    </div>
    <div class="t6-step-body">
      ${sustitucion.map(s => `<div style="font-family:var(--font-mono);font-size:.85rem;">${s}</div>`).join('')}
    </div>
  </div>

  <!-- Resultado y error -->
  <div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🎯</div>
      <div><div class="card-title">Resultado</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;">
      ${errBlock}
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    ${prevSec ? `<button class="btn btn-secondary" onclick="t8GoTo('${prevSec}')">← Anterior</button>` : ''}
    <button class="btn t8-btn-primary" onclick="t8GoTo('${nextSec}')">Siguiente →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO DE SECCIONES
══════════════════════════════════════════════════════════════ */
function t8RenderAdelante(res) {
  const { x0, h, v, adelante, exacto, errAd } = res;
  const sustitucion = [
    `f'(x₀) ≈ [f(x₀+h) − f(x₀)] / h`,
    `= [f(${x0}+${h}) − f(${x0})] / ${h}`,
    `= [f(${x0+h}) − f(${x0})] / ${h}`,
    `= [${t8Fmt(v.fxPH,8)} − ${t8Fmt(v.fx0,8)}] / ${h}`,
    `= ${t8Fmt(v.fxPH-v.fx0,8)} / ${h}`,
    `= ${t8Fmt(adelante,8)}`,
  ];
  t8RenderDif('t8-adelante',
    'Diferencia hacia adelante',
    "f'(x₀) ≈ [f(x₀+h) − f(x₀)] / h",
    sustitucion, adelante, errAd, exacto,
    't8-atras', 't8-input', '#3b82f6');
}

function t8RenderAtras(res) {
  const { x0, h, v, atras, exacto, errAt } = res;
  const sustitucion = [
    `f'(x₀) ≈ [f(x₀) − f(x₀−h)] / h`,
    `= [f(${x0}) − f(${x0}−${h})] / ${h}`,
    `= [f(${x0}) − f(${x0-h})] / ${h}`,
    `= [${t8Fmt(v.fx0,8)} − ${t8Fmt(v.fxMH,8)}] / ${h}`,
    `= ${t8Fmt(v.fx0-v.fxMH,8)} / ${h}`,
    `= ${t8Fmt(atras,8)}`,
  ];
  t8RenderDif('t8-atras',
    'Diferencia hacia atrás',
    "f'(x₀) ≈ [f(x₀) − f(x₀−h)] / h",
    sustitucion, atras, errAt, exacto,
    't8-central', 't8-adelante', '#8b5cf6');
}

function t8RenderCentral(res) {
  const { x0, h, v, central, exacto, errCen } = res;
  const sustitucion = [
    `f'(x₀) ≈ [f(x₀+h) − f(x₀−h)] / 2h`,
    `= [f(${x0+h}) − f(${x0-h})] / ${2*h}`,
    `= [${t8Fmt(v.fxPH,8)} − ${t8Fmt(v.fxMH,8)}] / ${2*h}`,
    `= ${t8Fmt(v.fxPH-v.fxMH,8)} / ${2*h}`,
    `= ${t8Fmt(central,8)}  ⭐ Más recomendada`,
  ];
  t8RenderDif('t8-central',
    'Diferencia central ⭐ (más recomendada)',
    "f'(x₀) ≈ [f(x₀+h) − f(x₀−h)] / 2h",
    sustitucion, central, errCen, exacto,
    't8-segunda', 't8-atras', T8_COLOR);
}

function t8RenderSegunda(res) {
  const sec = document.getElementById('t8-segunda');
  if (!sec) return;
  const { x0, h, v, segunda } = res;

  sec.innerHTML = `
  <div class="page-header">
    <h2>Segunda Derivada</h2>
    <p>Aproxima f''(x₀) — aceleración, curvatura o variación de la tasa de cambio.</p>
  </div>

  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T8_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t8-icon">f''</div>
      <div><div class="card-title">Fórmula de diferencia central de segundo orden</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:600;color:${T8_COLOR};">
        f''(x) ≈ [f(x+h) − 2f(x) + f(x−h)] / h²
      </div>
    </div>
  </div>

  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T8_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🔢</div>
      <div><div class="card-title">Sustitución numérica — x₀ = ${x0}, h = ${h}</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.85rem;">f''(${x0}) ≈ [f(${x0+h}) − 2f(${x0}) + f(${x0-h})] / (${h})²</div>
      <div style="font-family:var(--font-mono);font-size:.85rem;">= [${t8Fmt(v.fxPH,8)} − 2(${t8Fmt(v.fx0,8)}) + ${t8Fmt(v.fxMH,8)}] / ${h*h}</div>
      <div style="font-family:var(--font-mono);font-size:.85rem;">= [${t8Fmt(v.fxPH - 2*v.fx0 + v.fxMH,8)}] / ${h*h}</div>
    </div>
  </div>

  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T8_LIGHT},#fff7ed);border:2px solid ${T8_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🎯</div>
      <div><div class="card-title">Resultado — Segunda Derivada</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;text-align:center;">
      <div style="font-family:var(--font-mono);font-size:1.3rem;font-weight:700;color:${T8_COLOR};">
        f''(${x0}) ≈ ${t8Fmt(segunda,8)}
      </div>
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t8GoTo('t8-central')">← Dif. central</button>
    <button class="btn t8-btn-primary" onclick="t8GoTo('t8-richardson')">Siguiente: Richardson →</button>
  </div>`;
}

function t8RenderRichardson(res) {
  const sec = document.getElementById('t8-richardson');
  if (!sec) return;
  const { x0, h, central, centralH2, richardson, exacto, errRich } = res;

  const errBlock = (exacto !== null && !isNaN(exacto)) ? `
    <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:.75rem;margin-top:.75rem;">
      <div class="t8-metric-card" style="border-left-color:#0891b2;">
        <div class="t8-metric-label">f(h) — Dif. central paso h</div>
        <div class="t8-metric-val" style="color:#0891b2;">${t8Fmt(central)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#7c3aed;">
        <div class="t8-metric-label">f(h/2) — Dif. central paso h/2</div>
        <div class="t8-metric-val" style="color:#7c3aed;">${t8Fmt(centralH2)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:${T8_COLOR};">
        <div class="t8-metric-label">R(x) — Richardson</div>
        <div class="t8-metric-val" style="color:${T8_COLOR};">${t8Fmt(richardson)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#10b981;">
        <div class="t8-metric-label">Valor exacto</div>
        <div class="t8-metric-val" style="color:#10b981;">${t8Fmt(exacto)}</div>
      </div>
      <div class="t8-metric-card" style="border-left-color:#ef4444;">
        <div class="t8-metric-label">Error Richardson |ε|</div>
        <div class="t8-metric-val" style="color:#ef4444;">${t8FmtE(errRich)}</div>
      </div>
    </div>` : `
    <div class="t8-metric-card" style="border-left-color:${T8_COLOR};margin-top:.75rem;max-width:300px;">
      <div class="t8-metric-label">R(x₀) — Richardson</div>
      <div class="t8-metric-val" style="color:${T8_COLOR};">${t8Fmt(richardson)}</div>
    </div>`;

  sec.innerHTML = `
  <div class="page-header">
    <h2>Extrapolación de Richardson</h2>
    <p>Mejora la precisión combinando dos diferencias centrales con pasos h y h/2.<br>
       El error de la diferencia central es proporcional a h² — Richardson lo cancela.</p>
  </div>

  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T8_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t8-icon">R</div>
      <div><div class="card-title">Fórmula de Richardson</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.9rem;font-weight:600;color:${T8_COLOR};">
        R(x) = [4·f(h/2) − f(h)] / 3
      </div>
      <div style="font-family:var(--font-main);font-size:.8rem;color:var(--gray-500);">
        donde f(h) = dif. central con paso h · f(h/2) = dif. central con paso h/2
      </div>
    </div>
  </div>

  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T8_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🔢</div>
      <div><div class="card-title">Sustitución — x₀ = ${x0}, h = ${h}, h/2 = ${h/2}</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.82rem;">f(h)   = [f(${x0+h}) − f(${x0-h})] / ${2*h} = ${t8Fmt(central,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.82rem;">f(h/2) = [f(${x0+h/2}) − f(${x0-h/2})] / ${h} = ${t8Fmt(centralH2,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.82rem;">R(${x0}) = [4·(${t8Fmt(centralH2,6)}) − (${t8Fmt(central,6)})] / 3</div>
      <div style="font-family:var(--font-mono);font-size:.82rem;">R(${x0}) = [${t8Fmt(4*centralH2,6)} − ${t8Fmt(central,6)}] / 3</div>
      <div style="font-family:var(--font-mono);font-size:.82rem;">R(${x0}) = ${t8Fmt(4*centralH2-central,6)} / 3 = <strong style="color:${T8_COLOR};">${t8Fmt(richardson,8)}</strong></div>
    </div>
  </div>

  <div class="card" style="margin-bottom:1.25rem;">
    <div class="card-header">
      <div class="card-header-icon t8-icon">🎯</div>
      <div><div class="card-title">Comparación de precisión</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;">
      ${errBlock}
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t8GoTo('t8-segunda')">← Segunda deriv.</button>
    <button class="btn t8-btn-primary" onclick="t8GoTo('t8-resumen')">Ver Resumen →</button>
  </div>`;
}

function t8RenderResumen(res) {
  const sec = document.getElementById('t8-resumen');
  if (!sec) return;
  const { x0, h, adelante, atras, central, segunda, richardson, exacto, errAd, errAt, errCen, errRich } = res;

  const COLS = ['#3b82f6','#8b5cf6',T8_COLOR,'#0891b2'];
  const methods = [
    { label:'Diferencia adelante',  val:adelante,  err:errAd,  col:COLS[0] },
    { label:'Diferencia atrás',     val:atras,     err:errAt,  col:COLS[1] },
    { label:'Diferencia central ⭐', val:central,   err:errCen, col:COLS[2] },
    { label:'Richardson',           val:richardson, err:errRich,col:COLS[3] },
  ];

  let rows = methods.map(m => `
    <tr>
      <td style="padding:.45rem .75rem;font-family:var(--font-main);font-size:.82rem;font-weight:600;color:${m.col};">${m.label}</td>
      <td style="padding:.45rem .75rem;font-family:var(--font-mono);font-size:.82rem;text-align:right;">${t8Fmt(m.val)}</td>
      ${exacto !== null ? `<td style="padding:.45rem .75rem;font-family:var(--font-mono);font-size:.82rem;text-align:right;color:#ef4444;">${t8FmtE(m.err)}</td>` : ''}
      ${exacto !== null ? `<td style="padding:.45rem .75rem;font-family:var(--font-mono);font-size:.82rem;text-align:right;">${exacto !== 0 ? t8Fmt(Math.abs(m.err/exacto)*100,4)+'%' : '—'}</td>` : ''}
    </tr>`).join('');

  sec.innerHTML = `
  <div class="page-header">
    <h2>Resumen — Comparación de Métodos</h2>
    <p>x₀ = ${x0} · h = ${h}${exacto !== null ? ' · f\'(x₀) exacta = '+t8Fmt(exacto,8) : ''}</p>
  </div>

  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t8-icon">📊</div>
      <div><div class="card-title">Tabla comparativa — Primera derivada f'(${x0})</div></div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-size:.85rem;">
      <thead>
        <tr style="background:${T8_LIGHT};">
          <th style="padding:.5rem .75rem;color:${T8_DARK};border-bottom:2px solid ${T8_COLOR}33;">Método</th>
          <th style="padding:.5rem .75rem;color:${T8_DARK};border-bottom:2px solid ${T8_COLOR}33;text-align:right;">f'(x₀) ≈</th>
          ${exacto !== null ? `<th style="padding:.5rem .75rem;color:${T8_DARK};border-bottom:2px solid ${T8_COLOR}33;text-align:right;">Error |ε|</th>` : ''}
          ${exacto !== null ? `<th style="padding:.5rem .75rem;color:${T8_DARK};border-bottom:2px solid ${T8_COLOR}33;text-align:right;">Error %</th>` : ''}
        </tr>
      </thead>
      <tbody>${rows}</tbody>
    </table>
    </div>
  </div>

  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T8_LIGHT},#fff7ed);border:2px solid ${T8_COLOR}33;">
    <div class="card-header">
      <div class="card-header-icon t8-icon">f''</div>
      <div><div class="card-title">Segunda Derivada f''(${x0})</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;text-align:center;">
      <div style="font-family:var(--font-mono);font-size:1.2rem;font-weight:700;color:${T8_COLOR};">
        f''(${x0}) ≈ ${t8Fmt(segunda,8)}
      </div>
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t8GoTo('t8-richardson')">← Richardson</button>
    <button class="btn t8-btn-primary" onclick="t8GoTo('t8-input')">🔁 Nuevos datos</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Tabla inicial */
  t8State.tableData = [
    {x:0,y:25},{x:1,y:28},{x:2,y:32},{x:3,y:34}
  ];
  t8RenderTable();

  /* Modo toggle */
  const t8Radios = document.querySelectorAll('input[name="t8Mode"]');
  const t8PanFx  = document.getElementById('t8PanelFuncion');
  const t8PanTab = document.getElementById('t8PanelTabla');
  const t8UpdateMode = () => {
    const mode = document.querySelector('input[name="t8Mode"]:checked')?.value || 'funcion';
    t8State.mode = mode;
    if (t8PanFx)  t8PanFx.style.display  = mode === 'funcion' ? 'block' : 'none';
    if (t8PanTab) t8PanTab.style.display = mode === 'tabla'   ? 'block' : 'none';
  };
  t8Radios.forEach(r => r.addEventListener('change', t8UpdateMode));
  t8UpdateMode();

  /* Agregar/quitar filas */
  document.getElementById('btnT8AddRow')?.addEventListener('click', () => {
    t8State.tableData.push({x:0,y:0}); t8RenderTable();
  });
  document.getElementById('btnT8RemRow')?.addEventListener('click', () => {
    if(t8State.tableData.length > 3){ t8State.tableData.pop(); t8RenderTable(); }
  });

  /* Navegación interna */
  document.querySelectorAll('.t8-nav[data-t8]').forEach(el => {
    el.addEventListener('click', () => t8GoTo(el.getAttribute('data-t8')));
  });

  /* Ejemplo función (f(x)=sen(x), h=0.2, x0=0 — foto 4) */
  document.getElementById('btnT8EjFx')?.addEventListener('click', () => {
    document.querySelector('input[name="t8Mode"][value="funcion"]').checked = true;
    t8UpdateMode();
    document.getElementById('t8Fx').value        = 'sin(x)';
    document.getElementById('t8FxExacta').value  = 'cos(x)';
    document.getElementById('t8X0').value         = '0';
    document.getElementById('t8H').value          = '0.2';
    clearAlert('t8Alert');
    showAlert('t8Alert','info','📋 Ejemplo clase cargado — f(x)=sen(x), x₀=0, h=0.2. Resultado exacto: f\'(0)=1.');
  });

  /* Ejemplo tabla temperatura (foto 2) */
  document.getElementById('btnT8EjTab')?.addEventListener('click', () => {
    document.querySelector('input[name="t8Mode"][value="tabla"]').checked = true;
    t8UpdateMode();
    t8State.tableData = [{x:0,y:25},{x:1,y:28},{x:2,y:32},{x:3,y:34}];
    document.getElementById('t8X0Tab').value = '2';
    t8RenderTable();
    clearAlert('t8Alert');
    showAlert('t8Alert','info','📋 Ejemplo temperatura cargado — t=2s, h=1. Resultado clase: adelante=2, atrás=4, central=3 °C/s.');
  });

  /* Ejemplo dron (foto 3) */
  document.getElementById('btnT8EjDron')?.addEventListener('click', () => {
    document.querySelector('input[name="t8Mode"][value="tabla"]').checked = true;
    t8UpdateMode();
    t8State.tableData = [{x:0.0,y:0.0},{x:0.5,y:1.2},{x:1.0,y:4.5},{x:1.5,y:9.3},{x:2.0,y:15.0}];
    document.getElementById('t8X0Tab').value = '1';
    t8RenderTable();
    clearAlert('t8Alert');
    showAlert('t8Alert','info','📋 Ejemplo dron cargado — velocidad en t=1s y aceleración. Resultados clase: v(1)=8.1 m/s, a(1)=6.0 m/s².');
  });

  /* Botón calcular */
  document.getElementById('btnT8Calc')?.addEventListener('click', () => {
    clearAlert('t8Alert');
    clearAlert('t8AlertGlobal');

    const mode = document.querySelector('input[name="t8Mode"]:checked')?.value || 'funcion';
    t8State.mode = mode;

    let x0, h;
    if (mode === 'funcion') {
      t8State.fx       = document.getElementById('t8Fx')?.value?.trim() || 'sin(x)';
      t8State.fxExacta = document.getElementById('t8FxExacta')?.value?.trim() || '';
      x0 = parseFloat(document.getElementById('t8X0')?.value);
      h  = parseFloat(document.getElementById('t8H')?.value);
    } else {
      t8ReadTable();
      x0 = parseFloat(document.getElementById('t8X0Tab')?.value);
      h  = t8State.tableData.length >= 2
        ? t8State.tableData[1].x - t8State.tableData[0].x
        : 1;
    }

    if (isNaN(x0)) { showAlert('t8Alert','danger','Ingresa el valor de x₀.'); return; }
    if (isNaN(h) || h === 0) { showAlert('t8Alert','danger','El paso h no puede ser cero.'); return; }

    t8State.x0 = x0; t8State.h = h;

    try {
      const res = t8Compute(x0, h);
      t8State.result = res;

      t8RenderAdelante(res);
      t8RenderAtras(res);
      t8RenderCentral(res);
      t8RenderSegunda(res);
      t8RenderRichardson(res);
      t8RenderResumen(res);

      const dl = document.getElementById('t8-download-bar');
      if (dl) { dl.dataset.ready = '1'; dl.style.display = 'block'; }

      t8GoTo('t8-adelante');
      showAlert('t8AlertGlobal','success',
        `✓ Dif. adelante=${t8Fmt(res.adelante,6)} · Atrás=${t8Fmt(res.atras,6)} · Central=${t8Fmt(res.central,6)} · Richardson=${t8Fmt(res.richardson,6)}`);

    } catch(e) { showAlert('t8Alert','danger','Error: ' + e.message); }
  });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T8
══════════════════════════════════════════════════════════════ */
(function patchT8Export() {
  document.addEventListener('DOMContentLoaded', () => {
    if (typeof numerixExport === 'undefined') return;
    numerixExport.t8 = function() {
      const res = t8State.result;
      if (!res) { alert('Ejecuta el cálculo primero.'); return; }
      const wb = XLSX.utils.book_new();

      const info = [
        ['NUMERIX — Diferenciación Numérica','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],
        ['Modo', t8State.mode === 'funcion' ? 'Función f(x)' : 'Tabla de datos'],
        t8State.mode === 'funcion' ? ['f(x)', t8State.fx] : [],
        t8State.mode === 'funcion' ? ["f'(x) exacta", t8State.fxExacta] : [],
        ['x₀', res.x0], ['h', res.h],
        [],
        ['RESULTADOS — Primera derivada f\'(x₀)'],
        ['Método', 'Valor aproximado', res.exacto !== null ? 'Error |ε|' : ''],
        ['Diferencia adelante',  res.adelante,  res.errAd  ?? ''],
        ['Diferencia atrás',     res.atras,     res.errAt  ?? ''],
        ['Diferencia central',   res.central,   res.errCen ?? ''],
        ['Richardson',           res.richardson, res.errRich ?? ''],
        [],
        ['Segunda derivada f\'\'(x₀)', res.segunda],
        [],
        res.exacto !== null ? ['Valor exacto f\'(x₀)', res.exacto] : [],
      ].filter(r => r.length > 0);

      XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet(info), 'Diferenciacion');

      if (t8State.mode === 'tabla' && t8State.tableData.length > 0) {
        const hdr = ['i','xi','f(xi)'];
        const rows = t8State.tableData.map((p,i) => [i,p.x,p.y]);
        XLSX.utils.book_append_sheet(wb, XLSX.utils.aoa_to_sheet([hdr,...rows]), 'Tabla datos');
      }

      XLSX.writeFile(wb, `NUMERIX_T8_DiferenciacionNumerica.xlsx`);
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 9 — INTEGRACIÓN POR APROXIMACIÓN
   Trapecio Simple/Compuesta · Simpson 1/3 · Simpson 3/8
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T9_COLOR = '#4338ca';
const T9_LIGHT = '#eef2ff';
const T9_DARK  = '#312e81';

/* ── Estado T9 ──────────────────────────────────────────────── */
const t9State = {
  fx: 'exp(x)', a: 0, b: 2, n: 4, exacto: null,
  result: null
};

/* ── Evaluador ──────────────────────────────────────────────── */
function t9Eval(expr, x) {
  try {
    return new Function('x','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict";return(${expr});`)(x,Math.PI,Math.sin,Math.cos,Math.tan,Math.exp,Math.log,Math.sqrt,Math.pow,Math.abs);
  } catch(e){ return NaN; }
}

/* ── Navegación T9 ──────────────────────────────────────────── */
function t9GoTo(secId) {
  document.querySelectorAll('.t9-sec').forEach(s => s.style.display='none');
  document.querySelectorAll('.t9-nav').forEach(n => n.classList.remove('active'));
  const sec=document.getElementById(secId);
  if(sec) sec.style.display='block';
  document.querySelectorAll(`[data-t9="${secId}"]`).forEach(el=>el.classList.add('active'));
  const dl=document.getElementById('t9-download-bar');
  if(dl && dl.dataset.ready==='1' && secId!=='t9-input') dl.style.display='block';
}
window.t9GoTo = t9GoTo;

/* ── Formato ────────────────────────────────────────────────── */
const t9Fmt  = (v,d=8) => (v===null||isNaN(v)) ? '—' : Number(v).toFixed(d);
const t9FmtE = v => (v===null||isNaN(v)) ? '—' : Number(v).toExponential(4);
const t9Frac = (n,d) => {
  const g=(a,b)=>b===0?a:g(b,a%b);
  const div=g(Math.abs(n),Math.abs(d));
  return (n/div)===(d/div) ? String(n/div) : `${n/div}/${d/div}`;
};

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS
══════════════════════════════════════════════════════════════ */

/** Genera n+1 nodos uniformes en [a,b] */
function t9Nodes(a, b, n) {
  const h = (b-a)/n;
  return Array.from({length:n+1}, (_,i) => a + i*h);
}

/** Evalúa f en todos los nodos */
function t9EvalNodes(fx, xs) {
  return xs.map(x => t9Eval(fx, x));
}

/** Trapecio Simple: n=1, h=b-a */
function t9TrapSimple(fx, a, b) {
  const h  = b-a;
  const fa = t9Eval(fx,a), fb = t9Eval(fx,b);
  const I  = (h/2)*(fa+fb);
  return { h, fa, fb, I, xs:[a,b], ys:[fa,fb] };
}

/** Trapecio Compuesta: n subintervalos */
function t9TrapComp(fx, a, b, n) {
  const h   = (b-a)/n;
  const xs  = t9Nodes(a,b,n);
  const ys  = t9EvalNodes(fx,xs);
  const sum = ys.slice(1,-1).reduce((s,v)=>s+v,0);
  const I   = (h/2)*(ys[0] + 2*sum + ys[n]);
  return { h, xs, ys, sum, I, n };
}

/** Simpson 1/3 Simple: n=2, h=(b-a)/2 */
function t9S13Simple(fx, a, b) {
  const h   = (b-a)/2;
  const xs  = [a, a+h, b];
  const ys  = xs.map(x=>t9Eval(fx,x));
  const I   = (h/3)*(ys[0] + 4*ys[1] + ys[2]);
  return { h, xs, ys, I };
}

/** Simpson 1/3 Compuesta: n par */
function t9S13Comp(fx, a, b, n) {
  if(n%2 !== 0) n = n%2===1 ? n+1 : n; // forzar par
  const h   = (b-a)/n;
  const xs  = t9Nodes(a,b,n);
  const ys  = t9EvalNodes(fx,xs);
  // impares (1,3,5...) coef 4; pares (2,4,6...) coef 2
  let sumImp=0, sumPar=0;
  for(let i=1; i<n; i++){
    if(i%2===1) sumImp+=ys[i];
    else        sumPar+=ys[i];
  }
  const I = (h/3)*(ys[0] + 4*sumImp + 2*sumPar + ys[n]);
  return { h, xs, ys, sumImp, sumPar, I, n };
}

/** Simpson 3/8 Simple: n=3, h=(b-a)/3 */
function t9S38Simple(fx, a, b) {
  const h   = (b-a)/3;
  const xs  = [a, a+h, a+2*h, b];
  const ys  = xs.map(x=>t9Eval(fx,x));
  const I   = (3*h/8)*(ys[0] + 3*ys[1] + 3*ys[2] + ys[3]);
  return { h, xs, ys, I };
}

/** Simpson 3/8 Compuesta: n múltiplo de 3 */
function t9S38Comp(fx, a, b, n) {
  // ajustar n al múltiplo de 3 más cercano
  while(n%3 !== 0) n++;
  const h   = (b-a)/n;
  const xs  = t9Nodes(a,b,n);
  const ys  = t9EvalNodes(fx,xs);
  let sum3=0, sum2=0;
  for(let i=1; i<n; i++){
    if(i%3!==0) sum3+=ys[i]; // múltiplos de 3 → coef 2; resto → coef 3
    else        sum2+=ys[i];
  }
  const I = (3*h/8)*(ys[0] + 3*sum3 + 2*sum2 + ys[n]);
  return { h, xs, ys, sum3, sum2, I, n };
}

/** Compute all */
function t9Compute(fx, a, b, n, exacto) {
  const ts  = t9TrapSimple(fx,a,b);
  const tc  = t9TrapComp(fx,a,b,n);
  // Simpson 1/3: asegurar n par para compuesta
  const nS13 = n%2===0 ? n : n+1;
  const s13s = t9S13Simple(fx,a,b);
  const s13c = t9S13Comp(fx,a,b,nS13);
  // Simpson 3/8: asegurar n múltiplo de 3
  let nS38 = n; while(nS38%3!==0) nS38++;
  const s38s = t9S38Simple(fx,a,b);
  const s38c = t9S38Comp(fx,a,b,nS38);

  const err = (I) => exacto!==null && !isNaN(exacto) ? Math.abs(exacto-I) : null;

  return {
    fx, a, b, n, exacto,
    ts:  { ...ts,  err: err(ts.I)  },
    tc:  { ...tc,  err: err(tc.I)  },
    s13s:{ ...s13s,err: err(s13s.I)},
    s13c:{ ...s13c,err: err(s13c.I)},
    s38s:{ ...s38s,err: err(s38s.I)},
    s38c:{ ...s38c,err: err(s38c.I)},
  };
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — HELPER TABLA DE NODOS
══════════════════════════════════════════════════════════════ */
function t9NodeTable(xs, ys, coefs, color) {
  const hdr = ['i','xᵢ','f(xᵢ)','Coef.','Coef. × f(xᵢ)'];
  let html = `<div style="overflow-x:auto;">
  <table style="width:100%;border-collapse:collapse;font-family:var(--font-mono);font-size:.78rem;">
    <thead><tr style="background:${T9_LIGHT};">
      ${hdr.map(h=>`<th style="padding:.4rem .65rem;color:${T9_DARK};border-bottom:2px solid ${color}33;">${h}</th>`).join('')}
    </tr></thead><tbody>`;
  xs.forEach((x,i) => {
    const c = coefs[i];
    const bg = i===0||i===xs.length-1 ? `background:${T9_LIGHT};` : '';
    html += `<tr style="${bg}">
      <td style="padding:.35rem .65rem;text-align:center;font-weight:700;color:${color};">${i}</td>
      <td style="padding:.35rem .65rem;text-align:right;">${t9Fmt(x,6)}</td>
      <td style="padding:.35rem .65rem;text-align:right;">${t9Fmt(ys[i],8)}</td>
      <td style="padding:.35rem .65rem;text-align:center;font-weight:700;">${c}</td>
      <td style="padding:.35rem .65rem;text-align:right;">${t9Fmt(c*ys[i],8)}</td>
    </tr>`;
  });
  html += `</tbody></table></div>`;
  return html;
}

/* ── Helper: card de resultado con error ── */
function t9ResultCard(I, exacto, err, color) {
  const hasExacto = exacto!==null && !isNaN(exacto);
  return `
  <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:.75rem;margin-top:.75rem;">
    <div class="t8-metric-card" style="border-left-color:${color};">
      <div class="t8-metric-label">Resultado ∫</div>
      <div class="t8-metric-val" style="color:${color};font-size:1.1rem;">${t9Fmt(I,10)}</div>
    </div>
    ${hasExacto ? `
    <div class="t8-metric-card" style="border-left-color:#10b981;">
      <div class="t8-metric-label">Valor exacto</div>
      <div class="t8-metric-val" style="color:#10b981;">${t9Fmt(exacto,10)}</div>
    </div>
    <div class="t8-metric-card" style="border-left-color:#ef4444;">
      <div class="t8-metric-label">Error |ε|</div>
      <div class="t8-metric-val" style="color:#ef4444;">${t9FmtE(err)}</div>
    </div>` : ''}
  </div>`;
}

/* ── Botones de navegación ── */
function t9NavBtns(prev, next) {
  return `<div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;margin-top:1rem;">
    ${prev?`<button class="btn btn-secondary" onclick="t9GoTo('${prev}')">← Anterior</button>`:''}
    <button class="btn t9-btn-primary" onclick="t9GoTo('${next}')">Siguiente →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — TRAPECIO SIMPLE
══════════════════════════════════════════════════════════════ */
function t9RenderTrapSimple(res) {
  const sec=document.getElementById('t9-trap-simple'); if(!sec) return;
  const {ts,a,b,exacto}=res;
  const COL='#3b82f6';
  sec.innerHTML=`
  <div class="page-header">
    <h2>Trapecio Simple</h2>
    <p>Aproxima la integral con <strong>n=1</strong> (un solo trapecio) usando los dos extremos del intervalo.</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">∫</div>
      <div><div class="card-title">Fórmula del Trapecio Simple</div></div>
    </div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.9rem;color:${COL};font-weight:600;">∫ₐᵇ f(x)dx ≈ (h/2)·[f(a) + f(b)] &nbsp; donde h = b−a</div>
    </div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Sustitución — [${a}, ${b}]</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">h = ${b}−${a} = <strong>${t9Fmt(ts.h,6)}</strong></div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">f(a) = f(${a}) = <strong>${t9Fmt(ts.fa,8)}</strong></div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">f(b) = f(${b}) = <strong>${t9Fmt(ts.fb,8)}</strong></div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (${t9Fmt(ts.h,4)}/2)·[${t9Fmt(ts.fa,6)} + ${t9Fmt(ts.fb,6)}]</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ ${t9Fmt(ts.h/2,6)} · ${t9Fmt(ts.fa+ts.fb,6)} = <strong style="color:${COL};">${t9Fmt(ts.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(ts.I,exacto,ts.err,COL)}</div>
  ${t9NavBtns('t9-input','t9-trap-comp')}`;
}

/* ── Trapecio Compuesta ── */
function t9RenderTrapComp(res) {
  const sec=document.getElementById('t9-trap-comp'); if(!sec) return;
  const {tc,a,b,exacto}=res; const COL='#3b82f6';
  const coefs=[1,...new Array(tc.n-1).fill(2),1];
  sec.innerHTML=`
  <div class="page-header">
    <h2>Trapecio Compuesta</h2>
    <p>n = ${tc.n} subintervalos · h = ${t9Fmt(tc.h,6)} · Suma interior × 2</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header"><div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">∫</div>
      <div><div class="card-title">Fórmula Compuesta del Trapecio</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.88rem;color:${COL};font-weight:600;">∫ ≈ (h/2)·[f(x₀) + 2·Σf(xᵢ) + f(xₙ)] &nbsp; h=(b−a)/n</div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📋</div>
      <div><div class="card-title">Tabla de nodos — n=${tc.n}, h=${t9Fmt(tc.h,6)}</div></div></div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${t9NodeTable(tc.xs,tc.ys,coefs,COL)}</div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Cálculo</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">Σ interior = ${t9Fmt(tc.sum,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (${t9Fmt(tc.h,6)}/2)·[${t9Fmt(tc.ys[0],6)} + 2·(${t9Fmt(tc.sum,6)}) + ${t9Fmt(tc.ys[tc.n],6)}]</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">= ${t9Fmt(tc.h/2,6)} · ${t9Fmt(tc.ys[0]+2*tc.sum+tc.ys[tc.n],6)} = <strong style="color:${COL};">${t9Fmt(tc.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(tc.I,exacto,tc.err,COL)}</div>
  ${t9NavBtns('t9-trap-simple','t9-s13-simple')}`;
}

/* ── Simpson 1/3 Simple ── */
function t9RenderS13Simple(res) {
  const sec=document.getElementById('t9-s13-simple'); if(!sec) return;
  const {s13s,a,b,exacto}=res; const COL='#059669';
  sec.innerHTML=`
  <div class="page-header">
    <h2>Simpson 1/3 Simple</h2>
    <p>n=2 · h=(b−a)/2 · Aproxima con una parábola (polinomio de Lagrange grado 2)</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header"><div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">⌒</div>
      <div><div class="card-title">Fórmula Simpson 1/3 Simple</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.88rem;color:${COL};font-weight:600;">∫ₐᵇ f(x)dx ≈ (h/3)·[f(x₀) + 4f(x₁) + f(x₂)] &nbsp; h=(b−a)/2</div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📋</div>
      <div><div class="card-title">Nodos — x₀=${t9Fmt(s13s.xs[0],4)}, x₁=${t9Fmt(s13s.xs[1],4)}, x₂=${t9Fmt(s13s.xs[2],4)}</div></div></div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${t9NodeTable(s13s.xs,s13s.ys,[1,4,1],COL)}</div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Sustitución</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">h = (${b}−${a})/2 = ${t9Fmt(s13s.h,6)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (${t9Fmt(s13s.h,4)}/3)·[${t9Fmt(s13s.ys[0],6)} + 4·${t9Fmt(s13s.ys[1],6)} + ${t9Fmt(s13s.ys[2],6)}]</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">= ${t9Fmt(s13s.h/3,6)} · ${t9Fmt(s13s.ys[0]+4*s13s.ys[1]+s13s.ys[2],6)} = <strong style="color:${COL};">${t9Fmt(s13s.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(s13s.I,exacto,s13s.err,COL)}</div>
  ${t9NavBtns('t9-trap-comp','t9-s13-comp')}`;
}

/* ── Simpson 1/3 Compuesta ── */
function t9RenderS13Comp(res) {
  const sec=document.getElementById('t9-s13-comp'); if(!sec) return;
  const {s13c,a,b,exacto}=res; const COL='#059669';
  const coefs=s13c.xs.map((_,i)=>{
    if(i===0||i===s13c.n) return 1;
    return i%2===1 ? 4 : 2;
  });
  sec.innerHTML=`
  <div class="page-header">
    <h2>Simpson 1/3 Compuesta</h2>
    <p>n=${s13c.n} (par) · h=${t9Fmt(s13c.h,6)} · Coeficientes: 1, 4, 2, 4, 2, …, 4, 1</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header"><div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">⌣</div>
      <div><div class="card-title">Fórmula Compuesta Simpson 1/3</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.82rem;color:${COL};font-weight:600;">∫ ≈ (h/3)·[f(x₀) + 4·Σ(imp) + 2·Σ(par) + f(xₙ)]</div>
      <div style="font-family:var(--font-main);font-size:.78rem;color:var(--gray-500);">imp = índices impares (1,3,5…) · par = índices pares interiores (2,4,6…)</div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📋</div>
      <div><div class="card-title">Tabla de nodos — n=${s13c.n}, h=${t9Fmt(s13c.h,6)}</div></div></div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${t9NodeTable(s13c.xs,s13c.ys,coefs,COL)}</div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Cálculo</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">Σ impares (×4) = ${t9Fmt(s13c.sumImp,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">Σ pares int.(×2) = ${t9Fmt(s13c.sumPar,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (${t9Fmt(s13c.h,4)}/3)·[${t9Fmt(s13c.ys[0],4)} + 4·(${t9Fmt(s13c.sumImp,4)}) + 2·(${t9Fmt(s13c.sumPar,4)}) + ${t9Fmt(s13c.ys[s13c.n],4)}]</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">= <strong style="color:${COL};">${t9Fmt(s13c.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(s13c.I,exacto,s13c.err,COL)}</div>
  ${t9NavBtns('t9-s13-simple','t9-s38-simple')}`;
}

/* ── Simpson 3/8 Simple ── */
function t9RenderS38Simple(res) {
  const sec=document.getElementById('t9-s38-simple'); if(!sec) return;
  const {s38s,a,b,exacto}=res; const COL='#d97706';
  sec.innerHTML=`
  <div class="page-header">
    <h2>Simpson 3/8 Simple</h2>
    <p>n=3 · h=(b−a)/3 · Aproxima con un polinomio cúbico (4 puntos)</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header"><div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">∫</div>
      <div><div class="card-title">Fórmula Simpson 3/8 Simple</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.88rem;color:${COL};font-weight:600;">∫ₐᵇ f(x)dx ≈ (3h/8)·[f(x₀) + 3f(x₁) + 3f(x₂) + f(x₃)] &nbsp; h=(b−a)/3</div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📋</div>
      <div><div class="card-title">Nodos — 4 puntos</div></div></div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${t9NodeTable(s38s.xs,s38s.ys,[1,3,3,1],COL)}</div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Sustitución</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">h = (${b}−${a})/3 = ${t9Fmt(s38s.h,6)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (3·${t9Fmt(s38s.h,4)}/8)·[${t9Fmt(s38s.ys[0],4)} + 3·${t9Fmt(s38s.ys[1],4)} + 3·${t9Fmt(s38s.ys[2],4)} + ${t9Fmt(s38s.ys[3],4)}]</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">= ${t9Fmt(3*s38s.h/8,6)} · ${t9Fmt(s38s.ys[0]+3*s38s.ys[1]+3*s38s.ys[2]+s38s.ys[3],6)} = <strong style="color:${COL};">${t9Fmt(s38s.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(s38s.I,exacto,s38s.err,COL)}</div>
  ${t9NavBtns('t9-s13-comp','t9-s38-comp')}`;
}

/* ── Simpson 3/8 Compuesta ── */
function t9RenderS38Comp(res) {
  const sec=document.getElementById('t9-s38-comp'); if(!sec) return;
  const {s38c,a,b,exacto}=res; const COL='#d97706';
  const coefs=s38c.xs.map((_,i)=>{
    if(i===0||i===s38c.n) return 1;
    return i%3===0 ? 2 : 3;
  });
  sec.innerHTML=`
  <div class="page-header">
    <h2>Simpson 3/8 Compuesta</h2>
    <p>n=${s38c.n} (múltiplo de 3) · h=${t9Fmt(s38c.h,6)} · Coeficientes: 1, 3, 3, 2, 3, 3, 2, …, 1</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${COL};">
    <div class="card-header"><div class="card-header-icon" style="background:${COL};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">∬</div>
      <div><div class="card-title">Fórmula Compuesta Simpson 3/8</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.82rem;color:${COL};font-weight:600;">∫ ≈ (3h/8)·[f(x₀) + 3·Σ(no múlt.3) + 2·Σ(múlt.3) + f(xₙ)]</div>
      <div style="font-family:var(--font-main);font-size:.78rem;color:var(--gray-500);">n debe ser múltiplo de 3</div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📋</div>
      <div><div class="card-title">Tabla de nodos — n=${s38c.n}, h=${t9Fmt(s38c.h,6)}</div></div></div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${t9NodeTable(s38c.xs,s38c.ys,coefs,COL)}</div>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${T9_COLOR};">
    <div class="card-header"><div class="card-header-icon t9-icon">🔢</div>
      <div><div class="card-title">Cálculo</div></div></div>
    <div class="t6-step-body">
      <div style="font-family:var(--font-mono);font-size:.83rem;">Σ (coef 3) = ${t9Fmt(s38c.sum3,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">Σ (coef 2) = ${t9Fmt(s38c.sum2,8)}</div>
      <div style="font-family:var(--font-mono);font-size:.83rem;">∫ ≈ (3·${t9Fmt(s38c.h,4)}/8)·[...] = <strong style="color:${COL};">${t9Fmt(s38c.I,10)}</strong></div>
    </div>
  </div>
  <div class="card" style="margin-bottom:1rem;">${t9ResultCard(s38c.I,exacto,s38c.err,COL)}</div>
  ${t9NavBtns('t9-s38-simple','t9-resumen')}`;
}

/* ── Resumen comparativo ── */
function t9RenderResumen(res) {
  const sec=document.getElementById('t9-resumen'); if(!sec) return;
  const {ts,tc,s13s,s13c,s38s,s38c,exacto,a,b,n}=res;
  const hasE=exacto!==null&&!isNaN(exacto);

  const methods=[
    {label:'Trapecio Simple',       I:ts.I,   err:ts.err,   col:'#3b82f6'},
    {label:`Trapecio Compuesta n=${tc.n}`, I:tc.I,   err:tc.err,   col:'#6366f1'},
    {label:'Simpson 1/3 Simple',    I:s13s.I, err:s13s.err, col:'#059669'},
    {label:`Simpson 1/3 Comp. n=${s13c.n}`,I:s13c.I, err:s13c.err, col:'#10b981'},
    {label:'Simpson 3/8 Simple',    I:s38s.I, err:s38s.err, col:'#d97706'},
    {label:`Simpson 3/8 Comp. n=${s38c.n}`,I:s38c.I, err:s38c.err, col:'#f59e0b'},
  ];

  const rows=methods.map(m=>`<tr>
    <td style="padding:.4rem .75rem;font-family:var(--font-main);font-size:.82rem;font-weight:600;color:${m.col};">${m.label}</td>
    <td style="padding:.4rem .75rem;font-family:var(--font-mono);font-size:.8rem;text-align:right;">${t9Fmt(m.I,10)}</td>
    ${hasE?`<td style="padding:.4rem .75rem;font-family:var(--font-mono);font-size:.8rem;text-align:right;color:#ef4444;">${t9FmtE(m.err)}</td>`:''}
  </tr>`).join('');

  sec.innerHTML=`
  <div class="page-header">
    <h2>Resumen — Comparación de Métodos</h2>
    <p>∫${a}^${b} f(x)dx${hasE?' · Exacto = '+t9Fmt(exacto,10):''}</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t9-icon">📊</div>
      <div><div class="card-title">Tabla comparativa</div></div></div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;">
      <thead><tr style="background:${T9_LIGHT};">
        <th style="padding:.5rem .75rem;color:${T9_DARK};border-bottom:2px solid ${T9_COLOR}33;">Método</th>
        <th style="padding:.5rem .75rem;color:${T9_DARK};border-bottom:2px solid ${T9_COLOR}33;text-align:right;">∫ aproximada</th>
        ${hasE?`<th style="padding:.5rem .75rem;color:${T9_DARK};border-bottom:2px solid ${T9_COLOR}33;text-align:right;">Error |ε|</th>`:''}
      </tr></thead>
      <tbody>${rows}</tbody>
    </table></div>
  </div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;flex-wrap:wrap;">
    <button class="btn btn-secondary" onclick="t9GoTo('t9-s38-comp')">← Anterior</button>
    <button class="btn t9-btn-primary" onclick="t9GoTo('t9-input')">🔁 Nuevos datos</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Hint dinámico para n */
  document.getElementById('t9N')?.addEventListener('input', function() {
    const n=parseInt(this.value)||4;
    const hint=document.getElementById('t9NHint');
    if(hint) {
      const par=n%2===0?'✓':'✗ (se usará '+(n+1)+')';
      let m3=n; while(m3%3!==0) m3++;
      hint.textContent=`n=${n}: par ${par} para S1/3 · múlt.3: ${n%3===0?'✓':'✗ (se usará '+m3+')'}`;
    }
  });

  /* Navegación interna */
  document.querySelectorAll('.t9-nav[data-t9]').forEach(el=>{
    el.addEventListener('click',()=>t9GoTo(el.getAttribute('data-t9')));
  });

  /* Ejemplo clase: ∫₀² eˣdx */
  document.getElementById('btnT9EjEx')?.addEventListener('click',()=>{
    document.getElementById('t9Fx').value      = 'exp(x)';
    document.getElementById('t9A').value       = '0';
    document.getElementById('t9B').value       = '2';
    document.getElementById('t9N').value       = '4';
    document.getElementById('t9Exacto').value  = '6.38905609893065';
    clearAlert('t9Alert');
    showAlert('t9Alert','info','📋 Ejemplo clase — ∫₀² eˣdx. Exacto = e²−1 = 6.38905609893065. Presiona ▶ Calcular.');
  });

  /* Botón calcular */
  document.getElementById('btnT9Calc')?.addEventListener('click',()=>{
    clearAlert('t9Alert'); clearAlert('t9AlertGlobal');
    const fx     = document.getElementById('t9Fx')?.value?.trim()||'exp(x)';
    const a      = parseFloat(document.getElementById('t9A')?.value);
    const b      = parseFloat(document.getElementById('t9B')?.value);
    const n      = parseInt(document.getElementById('t9N')?.value)||4;
    const exVal  = document.getElementById('t9Exacto')?.value?.trim();
    const exacto = exVal ? parseFloat(exVal) : null;

    if(isNaN(a)||isNaN(b)){ showAlert('t9Alert','danger','Ingresa los límites a y b.'); return; }
    if(a>=b){ showAlert('t9Alert','danger','El límite a debe ser menor que b.'); return; }
    if(n<1){ showAlert('t9Alert','danger','n debe ser ≥ 1.'); return; }
    if(isNaN(t9Eval(fx,a))){ showAlert('t9Alert','danger','La función f(x) no es válida.'); return; }

    try {
      const res=t9Compute(fx,a,b,n,exacto);
      t9State.result=res;
      Object.assign(t9State,{fx,a,b,n,exacto});

      t9RenderTrapSimple(res);
      t9RenderTrapComp(res);
      t9RenderS13Simple(res);
      t9RenderS13Comp(res);
      t9RenderS38Simple(res);
      t9RenderS38Comp(res);
      t9RenderResumen(res);

      const dl=document.getElementById('t9-download-bar');
      if(dl){ dl.dataset.ready='1'; dl.style.display='block'; }

      t9GoTo('t9-trap-simple');
      showAlert('t9AlertGlobal','success',
        `✓ Trap.Simple=${t9Fmt(res.ts.I,6)} · Trap.Comp=${t9Fmt(res.tc.I,6)} · S1/3=${t9Fmt(res.s13s.I,6)} · S3/8=${t9Fmt(res.s38s.I,6)}`);

    } catch(e){ showAlert('t9Alert','danger','Error: '+e.message); }
  });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T9
══════════════════════════════════════════════════════════════ */
(function patchT9Export(){
  document.addEventListener('DOMContentLoaded',()=>{
    if(typeof numerixExport==='undefined') return;
    numerixExport.t9=function(){
      const res=t9State.result;
      if(!res){ alert('Ejecuta el cálculo primero.'); return; }
      const wb=XLSX.utils.book_new();
      const hasE=res.exacto!==null&&!isNaN(res.exacto);

      /* Resumen */
      const info=[
        ['NUMERIX — Integración por Aproximación','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],['f(x)',res.fx],['a',res.a],['b',res.b],['n',res.n],
        hasE?['Exacto',res.exacto]:[],
        [],
        ['RESULTADOS'],
        ['Método','∫ aprox.',hasE?'Error |ε|':''],
        ['Trapecio Simple',      res.ts.I,   hasE?res.ts.err:''],
        [`Trapecio Comp. n=${res.tc.n}`, res.tc.I,hasE?res.tc.err:''],
        ['Simpson 1/3 Simple',   res.s13s.I, hasE?res.s13s.err:''],
        [`S1/3 Comp. n=${res.s13c.n}`,  res.s13c.I,hasE?res.s13c.err:''],
        ['Simpson 3/8 Simple',   res.s38s.I, hasE?res.s38s.err:''],
        [`S3/8 Comp. n=${res.s38c.n}`,  res.s38c.I,hasE?res.s38c.err:''],
      ].filter(r=>r.length>0);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet(info),'Resumen');

      /* Nodos por método */
      const addSheet=(name,xs,ys,coefs)=>{
        const hdr=['i','xi','f(xi)','Coef','Coef×f(xi)'];
        const rows=xs.map((x,i)=>[i,x,ys[i],coefs[i],coefs[i]*ys[i]]);
        XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet([hdr,...rows]),name);
      };
      const tcCoefs=[1,...new Array(res.tc.n-1).fill(2),1];
      addSheet(`Trap n=${res.tc.n}`,res.tc.xs,res.tc.ys,tcCoefs);
      const s13Coefs=res.s13c.xs.map((_,i)=>i===0||i===res.s13c.n?1:i%2===1?4:2);
      addSheet(`S13 n=${res.s13c.n}`,res.s13c.xs,res.s13c.ys,s13Coefs);
      const s38Coefs=res.s38c.xs.map((_,i)=>i===0||i===res.s38c.n?1:i%3===0?2:3);
      addSheet(`S38 n=${res.s38c.n}`,res.s38c.xs,res.s38c.ys,s38Coefs);

      XLSX.writeFile(wb,'NUMERIX_T9_Integracion.xlsx');
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 10 — INTEGRACIÓN DE ROMBERG
   Trapecio Compuesta + Extrapolación de Richardson
   Fórmula maestra: Iⱼ,ₖ = [4^(k-1)·Iⱼ₊₁,ₖ₋₁ − Iⱼ,ₖ₋₁] / (4^(k-1)−1)
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T10_COLOR = '#0891b2';
const T10_LIGHT = '#ecfeff';
const T10_DARK  = '#164e63';

/* ── Estado T10 ─────────────────────────────────────────────── */
const t10State = {
  fx:'exp(x)', a:0, b:2, maxJ:5, tol:1e-5, exacto:null,
  result:null
};

/* ── Evaluador ──────────────────────────────────────────────── */
function t10Eval(expr,x) {
  try {
    return new Function('x','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict";return(${expr});`)(x,Math.PI,Math.sin,Math.cos,Math.tan,Math.exp,Math.log,Math.sqrt,Math.pow,Math.abs);
  } catch(e){return NaN;}
}

/* ── Navegación T10 ─────────────────────────────────────────── */
function t10GoTo(secId){
  document.querySelectorAll('.t10-sec').forEach(s=>s.style.display='none');
  document.querySelectorAll('.t10-nav').forEach(n=>n.classList.remove('active'));
  const sec=document.getElementById(secId);
  if(sec) sec.style.display='block';
  document.querySelectorAll(`[data-t10="${secId}"]`).forEach(el=>el.classList.add('active'));
  const dl=document.getElementById('t10-download-bar');
  if(dl&&dl.dataset.ready==='1'&&secId!=='t10-input') dl.style.display='block';
}
window.t10GoTo = t10GoTo;

/* ── Formato ────────────────────────────────────────────────── */
const t10Fmt  = (v,d=8) => (v===null||v===undefined||isNaN(v)) ? '—' : Number(v).toFixed(d);
const t10FmtE = v => (v===null||isNaN(v)) ? '—' : Number(v).toExponential(4);

/* ══════════════════════════════════════════════════════════════
   ALGORITMO — ROMBERG
══════════════════════════════════════════════════════════════ */

/** Trapecio compuesta para n subintervalos */
function t10Trapecio(fx, a, b, n) {
  const h   = (b-a)/n;
  let sum = 0;
  for(let i=1; i<n; i++) sum += t10Eval(fx, a + i*h);
  const fa = t10Eval(fx,a), fb = t10Eval(fx,b);
  const I  = (h/2)*(fa + 2*sum + fb);
  /* guardar nodos para mostrar */
  const xs = Array.from({length:n+1},(_,i)=>a+i*h);
  const ys = xs.map(x=>t10Eval(fx,x));
  return { I, h, n, fa, fb, sum, xs, ys };
}

/** Construir tabla de Romberg completa */
function t10Compute(fx, a, b, maxJ, tol, exacto) {
  /* R[j][k] — índices base 0 internamente, 1-based en display */
  const R   = [];
  const col1Details = [];   /* detalle de cada Iⱼ,₁ */
  let converged = false;
  let convJ = null, convK = null, convEps = null;

  /* Columna 1: Trapecio con n = 2^j */
  for(let j=0; j<maxJ; j++){
    R.push(new Array(maxJ).fill(null));
    const n   = Math.pow(2, j+1);    /* j=0→n=2, j=1→n=4, j=2→n=8 … */
    const det = t10Trapecio(fx, a, b, n);
    R[j][0]   = det.I;
    col1Details.push({ j:j+1, n, ...det });
  }

  /* Columnas K≥2: extrapolación de Richardson */
  for(let k=1; k<maxJ; k++){
    for(let j=0; j<maxJ-k; j++){
      const pow4 = Math.pow(4, k);
      R[j][k]   = (pow4 * R[j+1][k-1] - R[j][k-1]) / (pow4 - 1);
    }
    /* Verificar convergencia en la diagonal: I[0][k] vs I[0][k-1] */
    if(R[0][k] !== null && R[0][k-1] !== null) {
      const eps = Math.abs(R[0][k] - R[0][k-1]);
      if(eps < tol && !converged) {
        converged=true; convJ=1; convK=k+1; convEps=eps;
      }
    }
  }

  const best = R[0][maxJ-1] ?? R[0].find(v=>v!==null);
  const errFinal = (exacto!==null&&!isNaN(exacto)) ? Math.abs(exacto-best) : null;

  return { R, col1Details, maxJ, fx, a, b, tol, exacto, best, errFinal, converged, convJ, convK, convEps };
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO
══════════════════════════════════════════════════════════════ */

/** Sección 1: Columna K=1 — detalle de cada Iⱼ,₁ */
function t10RenderCol1(res) {
  const sec=document.getElementById('t10-col1'); if(!sec) return;
  const {col1Details, a, b} = res;

  let cards='';
  col1Details.forEach(d => {
    const COLORS=['#0891b2','#4338ca','#059669','#d97706','#7c3aed','#ef4444','#f59e0b','#10b981','#3b82f6','#8b5cf6'];
    const col=COLORS[(d.j-1)%COLORS.length];
    /* Mostrar hasta 8 nodos, truncar si hay más */
    const showN = Math.min(d.xs.length, 9);
    const truncated = d.xs.length > 9;
    let nodeRows='';
    for(let i=0;i<showN;i++){
      nodeRows+=`<tr style="${i%2===1?'background:var(--gray-50)':''}">
        <td style="padding:.3rem .65rem;text-align:center;font-weight:700;color:${col};">${i}</td>
        <td style="padding:.3rem .65rem;text-align:right;font-family:var(--font-mono);font-size:.78rem;">${t10Fmt(d.xs[i],6)}</td>
        <td style="padding:.3rem .65rem;text-align:right;font-family:var(--font-mono);font-size:.78rem;">${t10Fmt(d.ys[i],8)}</td>
        <td style="padding:.3rem .65rem;text-align:center;font-weight:700;font-family:var(--font-mono);font-size:.75rem;">${i===0||i===d.n?'1':'2'}</td>
      </tr>`;
    }
    if(truncated) nodeRows+=`<tr><td colspan="4" style="text-align:center;padding:.3rem;color:var(--gray-400);font-size:.75rem;font-family:var(--font-main);">… ${d.xs.length-showN} nodos más (n=${d.n})</td></tr>`;

    cards+=`
    <div class="card t6-step-card" style="margin-bottom:1rem;border-left:5px solid ${col};">
      <div class="card-header">
        <div class="card-header-icon" style="background:${col};width:38px;height:38px;border-radius:10px;
          display:flex;align-items:center;justify-content:center;color:#fff;font-size:.78rem;font-weight:700;">
          I${d.j},₁
        </div>
        <div>
          <div class="card-title">I<sub>${d.j},1</sub> — Trapecio con n = 2<sup>${d.j}</sup> = ${d.n} subintervalos</div>
          <div class="card-subtitle">h = (${b}−${a})/${d.n} = ${t10Fmt(d.h,6)}</div>
        </div>
        <div style="margin-left:auto;font-family:var(--font-mono);font-size:.95rem;font-weight:700;color:${col};">
          ${t10Fmt(d.I,8)}
        </div>
      </div>
      <div style="padding:.5rem 1.25rem 1rem;">
        <div style="font-family:var(--font-mono);font-size:.8rem;color:var(--gray-600);margin-bottom:.5rem;">
          I<sub>${d.j},1</sub> ≈ (${t10Fmt(d.h,4)}/2)·[f(${a}) + 2·Σ + f(${b})]
          = (${t10Fmt(d.h,4)}/2)·[${t10Fmt(d.fa,6)} + 2·(${t10Fmt(d.sum,6)}) + ${t10Fmt(d.fb,6)}]
        </div>
        <div style="overflow-x:auto;">
        <table style="border-collapse:collapse;font-size:.78rem;min-width:320px;">
          <thead><tr style="background:${T10_LIGHT};">
            <th style="padding:.3rem .65rem;color:${T10_DARK};">i</th>
            <th style="padding:.3rem .65rem;color:${T10_DARK};text-align:right;">xᵢ</th>
            <th style="padding:.3rem .65rem;color:${T10_DARK};text-align:right;">f(xᵢ)</th>
            <th style="padding:.3rem .65rem;color:${T10_DARK};text-align:center;">Coef.</th>
          </tr></thead>
          <tbody>${nodeRows}</tbody>
        </table>
        </div>
      </div>
    </div>`;
  });

  sec.innerHTML=`
  <div class="page-header">
    <h2>Romberg — Columna K=1 (Trapecio)</h2>
    <p>Primera columna de la tabla: se aplica la Regla del Trapecio Compuesta con n = 2, 4, 8, 16… subintervalos.</p>
  </div>
  ${cards}
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t10GoTo('t10-input')">← Datos</button>
    <button class="btn t10-btn-primary" onclick="t10GoTo('t10-tabla')">Ver Tabla de Romberg →</button>
  </div>`;
}

/** Sección 2: Tabla triangular de Romberg */
function t10RenderTabla(res) {
  const sec=document.getElementById('t10-tabla'); if(!sec) return;
  const {R, maxJ, tol, exacto, converged, convJ, convK, convEps} = res;

  /* Encabezado de columnas */
  let hdr=`<tr style="background:${T10_LIGHT};">
    <th style="padding:.5rem .75rem;color:${T10_DARK};border-bottom:2px solid ${T10_COLOR}33;">j \\ k</th>`;
  for(let k=1;k<=maxJ;k++)
    hdr+=`<th style="padding:.5rem .75rem;color:${T10_DARK};border-bottom:2px solid ${T10_COLOR}33;text-align:center;">K=${k}</th>`;
  hdr+=`</tr>`;

  /* Filas */
  let rows='';
  for(let j=0;j<maxJ;j++){
    rows+=`<tr style="${j%2===1?'background:var(--gray-50)':''}">
      <td style="padding:.45rem .75rem;font-weight:700;color:${T10_COLOR};font-family:var(--font-mono);">j=${j+1}</td>`;
    for(let k=0;k<maxJ;k++){
      const val=R[j][k];
      /* ¿Es valor de la diagonal superior (best path)? */
      const isDiag = (j+k===maxJ-1) && val!==null;
      /* ¿Es el punto de convergencia? */
      const isConv = converged && j===0 && k===convK-1;
      let cellStyle=`padding:.45rem .75rem;text-align:center;font-family:var(--font-mono);font-size:.78rem;`;
      if(val===null)        cellStyle+='color:var(--gray-300);';
      else if(isConv)       cellStyle+=`background:linear-gradient(135deg,#f0fdf4,#dcfce7);font-weight:700;color:#065f46;border:2px solid #10b981;border-radius:4px;`;
      else if(isDiag)       cellStyle+=`background:${T10_LIGHT};font-weight:700;color:${T10_COLOR};`;
      else if(k===0)        cellStyle+=`color:#4338ca;`;

      rows+=`<td style="${cellStyle}">${val===null?'—':t10Fmt(val,8)}</td>`;
    }
    rows+=`</tr>`;
  }

  /* Explicación de extrapolaciones */
  let extHtml='';
  for(let k=1;k<maxJ;k++){
    const pow4=Math.pow(4,k);
    for(let j=0;j<maxJ-k;j++){
      if(R[j][k]===null) continue;
      extHtml+=`
      <div style="border-left:4px solid ${T10_COLOR};padding:.4rem .75rem;background:var(--gray-50);
                  border-radius:0 var(--radius-sm) var(--radius-sm) 0;margin-bottom:.4rem;
                  font-family:var(--font-mono);font-size:.75rem;">
        <span style="color:${T10_COLOR};font-weight:700;">I<sub>${j+1},${k+1}</sub></span> =
        [4<sup>${k}</sup>·I<sub>${j+2},${k}</sub> − I<sub>${j+1},${k}</sub>] / (4<sup>${k}</sup>−1) =
        [${pow4}·(${t10Fmt(R[j+1][k-1],6)}) − (${t10Fmt(R[j][k-1],6)})] / ${pow4-1} =
        <strong style="color:${T10_COLOR};">${t10Fmt(R[j][k],8)}</strong>
        ${(()=>{
          const eps=exacto!==null&&!isNaN(exacto)?`· ε=${t10FmtE(Math.abs(exacto-R[j][k]))}`:''
          return eps;
        })()}
      </div>`;
    }
  }

  sec.innerHTML=`
  <div class="page-header">
    <h2>Romberg — Tabla Triangular I<sub>j,k</sub></h2>
    <p>Fórmula: I<sub>j,k</sub> ≈ [4<sup>k-1</sup>·I<sub>j+1,k-1</sub> − I<sub>j,k-1</sub>] / (4<sup>k-1</sup>−1)
       · Tolerancia: ${tol}</p>
  </div>

  <!-- Tabla triangular -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t10-icon">📋</div>
      <div>
        <div class="card-title">Tabla de Romberg</div>
        <div class="card-subtitle">
          K=1: Trapecio · K≥2: Extrapolación de Richardson ·
          <span style="background:#d1fae5;color:#065f46;padding:.1rem .4rem;border-radius:4px;font-weight:700;">
            Verde = convergencia
          </span>
          <span style="background:${T10_LIGHT};color:${T10_COLOR};padding:.1rem .4rem;border-radius:4px;margin-left:.5rem;font-weight:700;">
            Azul = diagonal principal
          </span>
        </div>
      </div>
    </div>
    <div style="overflow-x:auto;padding:1rem 1.25rem;">
    <table style="border-collapse:separate;border-spacing:3px;font-family:var(--font-mono);font-size:.8rem;">
      <thead>${hdr}</thead>
      <tbody>${rows}</tbody>
    </table>
    </div>
  </div>

  <!-- Extrapolaciones paso a paso -->
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T10_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t10-icon">⚙</div>
      <div>
        <div class="card-title">Extrapolaciones de Richardson — paso a paso</div>
        <div class="card-subtitle">Cada celda de K≥2 calculada explícitamente</div>
      </div>
    </div>
    <div style="padding:.75rem 1.25rem 1.25rem;">${extHtml}</div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t10GoTo('t10-col1')">← Columna K=1</button>
    <button class="btn t10-btn-primary" onclick="t10GoTo('t10-resultado')">Ver Resultado →</button>
  </div>`;
}

/** Sección 3: Resultado final */
function t10RenderResultado(res) {
  const sec=document.getElementById('t10-resultado'); if(!sec) return;
  const {best, errFinal, exacto, converged, convJ, convK, convEps, tol, maxJ, R} = res;

  const hasE=exacto!==null&&!isNaN(exacto);
  const convMsg=converged
    ? `✓ Convergencia en I<sub>${convJ},${convK}</sub> — ε = ${t10FmtE(convEps)} &lt; ${tol}`
    : `⚠ No se alcanzó la tolerancia en ${maxJ} filas — se tomó el mejor valor disponible`;
  const convColor=converged?'#065f46':'#92400e';
  const convBg=converged?'linear-gradient(135deg,#f0fdf4,#dcfce7)':'linear-gradient(135deg,#fffbeb,#fef3c7)';

  /* Progresión de errores por fila */
  let progRows='';
  for(let j=0;j<maxJ;j++){
    const val=R[j][Math.min(j,maxJ-1)] ?? R[j].filter(v=>v!==null).at(-1);
    if(val===null) continue;
    const e=hasE?Math.abs(exacto-val):null;
    progRows+=`<tr>
      <td style="padding:.35rem .75rem;text-align:center;font-weight:700;color:${T10_COLOR};font-family:var(--font-mono);">j=${j+1}, K=${Math.min(j+1,maxJ)}</td>
      <td style="padding:.35rem .75rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;">${t10Fmt(val,10)}</td>
      ${hasE?`<td style="padding:.35rem .75rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:#ef4444;">${t10FmtE(e)}</td>`:''}
    </tr>`;
  }

  sec.innerHTML=`
  <div class="page-header">
    <h2>Romberg — Resultado Final</h2>
    <p>Mejor aproximación de la diagonal superior de la tabla de Romberg.</p>
  </div>

  <!-- Badge de convergencia -->
  <div style="padding:.875rem 1.25rem;background:${convBg};border:1.5px solid ${converged?'#6ee7b7':'#fcd34d'};
              border-radius:var(--radius-sm);margin-bottom:1.25rem;
              font-family:var(--font-main);font-size:.88rem;font-weight:600;color:${convColor};">
    ${convMsg}
  </div>

  <!-- Resultado principal -->
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T10_LIGHT},#ecfeff);
    border:2px solid ${T10_COLOR}44;">
    <div class="card-header">
      <div class="card-header-icon t10-icon">🎯</div>
      <div><div class="card-title">Mejor aproximación — Romberg</div></div>
    </div>
    <div style="padding:.5rem 1.25rem 1.25rem;">
      <div style="text-align:center;font-family:var(--font-mono);font-size:1.4rem;font-weight:700;color:${T10_COLOR};">
        ∫ ≈ ${t10Fmt(best,10)}
      </div>
      ${hasE?`
      <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:.75rem;margin-top:1rem;">
        <div class="t8-metric-card" style="border-left-color:${T10_COLOR};">
          <div class="t8-metric-label">Romberg</div>
          <div class="t8-metric-val" style="color:${T10_COLOR};">${t10Fmt(best,10)}</div>
        </div>
        <div class="t8-metric-card" style="border-left-color:#10b981;">
          <div class="t8-metric-label">Valor exacto</div>
          <div class="t8-metric-val" style="color:#10b981;">${t10Fmt(exacto,10)}</div>
        </div>
        <div class="t8-metric-card" style="border-left-color:#ef4444;">
          <div class="t8-metric-label">Error |ε|</div>
          <div class="t8-metric-val" style="color:#ef4444;">${t10FmtE(errFinal)}</div>
        </div>
      </div>`:''}
    </div>
  </div>

  <!-- Progresión diagonal -->
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t10-icon">📈</div>
      <div>
        <div class="card-title">Progresión de la diagonal — convergencia</div>
        <div class="card-subtitle">Cada fila muestra la mejor estimación disponible al llegar a esa fila</div>
      </div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;font-size:.82rem;">
      <thead><tr style="background:${T10_LIGHT};">
        <th style="padding:.45rem .75rem;color:${T10_DARK};border-bottom:2px solid ${T10_COLOR}33;">Estimación</th>
        <th style="padding:.45rem .75rem;color:${T10_DARK};border-bottom:2px solid ${T10_COLOR}33;text-align:right;">Valor</th>
        ${hasE?`<th style="padding:.45rem .75rem;color:${T10_DARK};border-bottom:2px solid ${T10_COLOR}33;text-align:right;">Error |ε|</th>`:''}
      </tr></thead>
      <tbody>${progRows}</tbody>
    </table>
    </div>
  </div>

  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t10GoTo('t10-tabla')">← Tabla</button>
    <button class="btn t10-btn-primary" onclick="t10GoTo('t10-input')">🔁 Nuevos datos</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  document.querySelectorAll('.t10-nav[data-t10]').forEach(el=>{
    el.addEventListener('click',()=>t10GoTo(el.getAttribute('data-t10')));
  });

  /* Ejemplo clase */
  document.getElementById('btnT10Ej')?.addEventListener('click',()=>{
    document.getElementById('t10Fx').value     = 'exp(x)';
    document.getElementById('t10A').value      = '0';
    document.getElementById('t10B').value      = '2';
    document.getElementById('t10MaxJ').value   = '3';
    document.getElementById('t10Tol').value    = '0.00001';
    document.getElementById('t10Exacto').value = '6.38905609893065';
    clearAlert('t10Alert');
    showAlert('t10Alert','info','📋 Ejemplo clase ∫₀² eˣdx — 3 filas (K=1,2,3). Exacto = 6.38905609893065. Presiona ▶');
  });

  /* Calcular */
  document.getElementById('btnT10Calc')?.addEventListener('click',()=>{
    clearAlert('t10Alert'); clearAlert('t10AlertGlobal');
    const fx     = document.getElementById('t10Fx')?.value?.trim()||'exp(x)';
    const a      = parseFloat(document.getElementById('t10A')?.value);
    const b      = parseFloat(document.getElementById('t10B')?.value);
    const maxJ   = parseInt(document.getElementById('t10MaxJ')?.value)||5;
    const tol    = parseFloat(document.getElementById('t10Tol')?.value)||1e-5;
    const exStr  = document.getElementById('t10Exacto')?.value?.trim();
    const exacto = exStr ? parseFloat(exStr) : null;

    if(isNaN(a)||isNaN(b)){ showAlert('t10Alert','danger','Ingresa los límites a y b.'); return; }
    if(a>=b){ showAlert('t10Alert','danger','a debe ser menor que b.'); return; }
    if(maxJ<2||maxJ>10){ showAlert('t10Alert','danger','Máximo de filas debe ser entre 2 y 10.'); return; }
    if(isNaN(t10Eval(fx,a))){ showAlert('t10Alert','danger','La función no es válida.'); return; }

    try {
      const res=t10Compute(fx,a,b,maxJ,tol,exacto);
      t10State.result=res;
      Object.assign(t10State,{fx,a,b,maxJ,tol,exacto});

      t10RenderCol1(res);
      t10RenderTabla(res);
      t10RenderResultado(res);

      const dl=document.getElementById('t10-download-bar');
      if(dl){ dl.dataset.ready='1'; dl.style.display='block'; }

      t10GoTo('t10-col1');
      const msg=res.converged
        ? `✓ Convergencia — ∫ ≈ ${t10Fmt(res.best,8)} · ε = ${t10FmtE(res.convEps)}`
        : `⚠ Máx. filas — mejor aprox: ∫ ≈ ${t10Fmt(res.best,8)}`;
      showAlert('t10AlertGlobal',res.converged?'success':'warning',msg);

    } catch(e){ showAlert('t10Alert','danger','Error: '+e.message); }
  });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T10
══════════════════════════════════════════════════════════════ */
(function patchT10Export(){
  document.addEventListener('DOMContentLoaded',()=>{
    if(typeof numerixExport==='undefined') return;
    numerixExport.t10=function(){
      const res=t10State.result;
      if(!res){ alert('Ejecuta el cálculo primero.'); return; }
      const wb=XLSX.utils.book_new();
      const {R,maxJ,fx,a,b,tol,exacto,best,errFinal,converged}=res;

      /* Hoja 1: Tabla de Romberg */
      const hdr=['j \\ k',...Array.from({length:maxJ},(_,k)=>`K=${k+1}`)];
      const rows=R.map((row,j)=>[`j=${j+1}`,...row.map(v=>v===null?'':v)]);
      const info=[
        ['NUMERIX — Integración de Romberg','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],['f(x)',fx],['a',a],['b',b],['Filas',maxJ],['Tolerancia',tol],
        exacto!==null?['Exacto',exacto]:[],
        [],['Mejor aprox.',best],errFinal!==null?['Error |ε|',errFinal]:[],
        ['Convergió',converged?'Sí':'No'],
        [],[],[hdr],...rows
      ].filter(r=>r.length>0);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet(info),'Tabla Romberg');

      /* Hoja 2: Detalle columna 1 */
      const hdr2=['j','n','h','I(j,1)'];
      const rows2=res.col1Details.map(d=>[d.j,d.n,d.h,d.I]);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet([hdr2,...rows2]),'Col K=1 Trapecio');

      XLSX.writeFile(wb,'NUMERIX_T10_Romberg.xlsx');
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 11 — MÉTODOS DE UN PASO PARA EDO
   Euler · Euler Mejorado (Heun) · Runge-Kutta 4to Orden
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T11_COLOR = '#be185d';
const T11_LIGHT = '#fdf2f8';
const T11_DARK  = '#831843';
const T11_EULER = '#3b82f6';
const T11_HEUN  = '#0d9488';
const T11_RK4   = '#7c3aed';
const T11_EXACT = '#10b981';

/* ── Estado T11 ─────────────────────────────────────────────── */
const t11State = {
  fxy:'x+y', x0:0, y0:1, h:0.1, xn:0.5, exacta:'', method:'euler',
  result:null,
  graph:{canvas:null,ctx:null,xMin:-1,xMax:1,yMin:-1,yMax:3,dragging:false,lastMouse:{x:0,y:0},hoverOn:false}
};

/* ── Evaluador f(x,y) ───────────────────────────────────────── */
function t11Eval(expr,x,y) {
  try {
    return new Function('x','y','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict";return(${expr});`)(x,y,Math.PI,Math.sin,Math.cos,Math.tan,Math.exp,Math.log,Math.sqrt,Math.pow,Math.abs);
  } catch(e){return NaN;}
}
/* ── Evaluador y(x) exacta (solo x) ──────────────────────────── */
function t11EvalExacta(expr,x) {
  if(!expr || !expr.trim()) return null;
  try {
    return new Function('x','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict";return(${expr});`)(x,Math.PI,Math.sin,Math.cos,Math.tan,Math.exp,Math.log,Math.sqrt,Math.pow,Math.abs);
  } catch(e){return null;}
}

/* ── Navegación T11 ─────────────────────────────────────────── */
function t11GoTo(secId){
  document.querySelectorAll('.t11-sec').forEach(s=>s.style.display='none');
  document.querySelectorAll('.t11-nav').forEach(n=>n.classList.remove('active'));
  const sec=document.getElementById(secId);
  if(sec) sec.style.display='block';
  document.querySelectorAll(`[data-t11="${secId}"]`).forEach(el=>el.classList.add('active'));
  const dl=document.getElementById('t11-download-bar');
  if(dl&&dl.dataset.ready==='1'&&secId!=='t11-input') dl.style.display='block';
}
window.t11GoTo = t11GoTo;

/* ── Formato ────────────────────────────────────────────────── */
const t11Fmt  = (v,d=8) => (v===null||v===undefined||isNaN(v)) ? '—' : Number(v).toFixed(d);
const t11FmtE = v => (v===null||isNaN(v)) ? '—' : Number(v).toExponential(4);

/* ══════════════════════════════════════════════════════════════
   ALGORITMOS
══════════════════════════════════════════════════════════════ */

/** Método de Euler */
function t11Euler(fxy, x0, y0, h, n) {
  const pts=[{x:x0,y:y0,slope:t11Eval(fxy,x0,y0)}];
  let x=x0, y=y0;
  for(let i=0;i<n;i++){
    const f = t11Eval(fxy,x,y);
    const yNew = y + h*f;
    const xNew = x + h;
    pts.push({x:xNew,y:yNew,slope:t11Eval(fxy,xNew,yNew),f0:f,h});
    x=xNew; y=yNew;
  }
  return pts;
}

/** Euler Mejorado (Heun) */
function t11Heun(fxy, x0, y0, h, n) {
  const pts=[{x:x0,y:y0}];
  let x=x0, y=y0;
  for(let i=0;i<n;i++){
    const f0 = t11Eval(fxy,x,y);
    const yPred = y + h*f0;
    const xNew  = x + h;
    const f1 = t11Eval(fxy,xNew,yPred);
    const yNew  = y + (h/2)*(f0+f1);
    pts.push({x:xNew,y:yNew,f0,yPred,f1,h});
    x=xNew; y=yNew;
  }
  return pts;
}

/** Runge-Kutta 4to orden */
function t11RK4(fxy, x0, y0, h, n) {
  const pts=[{x:x0,y:y0}];
  let x=x0, y=y0;
  for(let i=0;i<n;i++){
    const k1 = h*t11Eval(fxy, x,       y);
    const k2 = h*t11Eval(fxy, x+h/2,   y+k1/2);
    const k3 = h*t11Eval(fxy, x+h/2,   y+k2/2);
    const k4 = h*t11Eval(fxy, x+h,     y+k3);
    const yNew = y + (k1+2*k2+2*k3+k4)/6;
    const xNew = x+h;
    pts.push({x:xNew,y:yNew,k1,k2,k3,k4,h});
    x=xNew; y=yNew;
  }
  return pts;
}

/** Compute all 3 methods */
function t11Compute(fxy, x0, y0, h, xn, exacta) {
  const n = Math.round((xn-x0)/h);
  const euler = t11Euler(fxy,x0,y0,h,n);
  const heun  = t11Heun(fxy,x0,y0,h,n);
  const rk4   = t11RK4(fxy,x0,y0,h,n);

  /* Agregar valor exacto y error a cada punto */
  const addExact = (pts) => pts.map(p => {
    const ex = t11EvalExacta(exacta, p.x);
    return { ...p, exact:ex, err: ex!==null ? Math.abs(ex-p.y) : null };
  });

  return {
    fxy, x0, y0, h, xn, n, exacta,
    euler: addExact(euler),
    heun:  addExact(heun),
    rk4:   addExact(rk4),
  };
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — FÓRMULA DEL MÉTODO SELECCIONADO
══════════════════════════════════════════════════════════════ */
function t11RenderFormula(res, method) {
  const sec=document.getElementById('t11-formula'); if(!sec) return;
  const {fxy,x0,y0,h} = res;
  const labels={euler:'Euler',heun:'Euler Mejorado (Heun)',rk4:'Runge-Kutta 4to Orden'};
  const colors={euler:T11_EULER,heun:T11_HEUN,rk4:T11_RK4};
  const col=colors[method];

  let formulaHtml='';
  if(method==='euler'){
    formulaHtml=`
    <div style="font-family:var(--font-mono);font-size:1rem;font-weight:700;color:${col};text-align:center;padding:1rem;">
      yᵢ₊₁ = yᵢ + h·f(xᵢ,yᵢ)
    </div>
    <div style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-600);text-align:center;">
      Se usa la pendiente al <strong>inicio</strong> del intervalo para extrapolar linealmente.
    </div>`;
  } else if(method==='heun'){
    formulaHtml=`
    <div style="display:flex;flex-direction:column;gap:.5rem;padding:1rem;">
      <div style="font-family:var(--font-mono);font-size:.92rem;color:${col};font-weight:600;">
        <strong>Predictor:</strong> y*ᵢ₊₁ = yᵢ + h·f(xᵢ,yᵢ)
      </div>
      <div style="font-family:var(--font-mono);font-size:.92rem;color:${col};font-weight:600;">
        <strong>Corrector:</strong> yᵢ₊₁ = yᵢ + (h/2)·[f(xᵢ,yᵢ) + f(xᵢ₊₁, y*ᵢ₊₁)]
      </div>
    </div>
    <div style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-600);text-align:center;">
      Promedia la pendiente inicial con la pendiente al final del intervalo (usando la predicción de Euler).
    </div>`;
  } else {
    formulaHtml=`
    <div style="display:flex;flex-direction:column;gap:.4rem;padding:1rem;font-family:var(--font-mono);font-size:.85rem;color:${col};font-weight:600;">
      <div>k₁ = h·f(xᵢ, yᵢ)</div>
      <div>k₂ = h·f(xᵢ + h/2, yᵢ + k₁/2)</div>
      <div>k₃ = h·f(xᵢ + h/2, yᵢ + k₂/2)</div>
      <div>k₄ = h·f(xᵢ + h, yᵢ + k₃)</div>
      <div style="border-top:1px solid ${col}33;padding-top:.4rem;margin-top:.2rem;">
        yᵢ₊₁ = yᵢ + (1/6)·(k₁ + 2k₂ + 2k₃ + k₄)
      </div>
    </div>
    <div style="font-family:var(--font-main);font-size:.82rem;color:var(--gray-600);text-align:center;">
      Promedia 4 pendientes (inicio, dos en el punto medio, final) con pesos 1:2:2:1.
    </div>`;
  }

  sec.innerHTML=`
  <div class="page-header">
    <h2>${labels[method]} — Fórmula</h2>
    <p>PVI: dy/dx = ${fxy} &nbsp;·&nbsp; y(${x0}) = ${y0} &nbsp;·&nbsp; h = ${h}</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${col};">
    <div class="card-header">
      <div class="card-header-icon" style="background:${col};width:38px;height:38px;border-radius:10px;
        display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;font-size:.8rem;">
        ${method==='euler'?'①':method==='heun'?'②':'③'}
      </div>
      <div><div class="card-title">${labels[method]}</div></div>
    </div>
    ${formulaHtml}
  </div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t11GoTo('t11-input')">← Datos</button>
    <button class="btn t11-btn-primary" onclick="t11GoTo('t11-iteraciones')">Ver Iteraciones →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — ITERACIONES PASO A PASO
══════════════════════════════════════════════════════════════ */
function t11RenderIteraciones(res, method) {
  const sec=document.getElementById('t11-iteraciones'); if(!sec) return;
  const pts = res[method];
  const colors={euler:T11_EULER,heun:T11_HEUN,rk4:T11_RK4};
  const col=colors[method];
  const labels={euler:'Euler',heun:'Heun',rk4:'RK4'};

  let cards='';
  const showMax=Math.min(pts.length,8);
  for(let i=1;i<showMax;i++){
    const p=pts[i], prev=pts[i-1];
    let detail='';
    if(method==='euler'){
      detail=`
        <div style="font-family:var(--font-mono);font-size:.8rem;">f(x${i-1},y${i-1}) = f(${t11Fmt(prev.x,4)}, ${t11Fmt(prev.y,6)}) = ${t11Fmt(p.f0,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.8rem;">y${i} = ${t11Fmt(prev.y,6)} + (${t11Fmt(p.h,4)})(${t11Fmt(p.f0,6)}) = <strong style="color:${col};">${t11Fmt(p.y,8)}</strong></div>`;
    } else if(method==='heun'){
      detail=`
        <div style="font-family:var(--font-mono);font-size:.8rem;">f(x${i-1},y${i-1}) = ${t11Fmt(p.f0,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.8rem;">y*${i} (predictor) = ${t11Fmt(prev.y,6)} + (${t11Fmt(p.h,4)})(${t11Fmt(p.f0,6)}) = ${t11Fmt(p.yPred,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.8rem;">f(x${i},y*${i}) = ${t11Fmt(p.f1,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.8rem;">y${i} = ${t11Fmt(prev.y,6)} + (${t11Fmt(p.h,4)}/2)[${t11Fmt(p.f0,6)}+${t11Fmt(p.f1,6)}] = <strong style="color:${col};">${t11Fmt(p.y,8)}</strong></div>`;
    } else {
      detail=`
        <div style="font-family:var(--font-mono);font-size:.78rem;">k₁ = ${t11Fmt(p.k1,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.78rem;">k₂ = ${t11Fmt(p.k2,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.78rem;">k₃ = ${t11Fmt(p.k3,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.78rem;">k₄ = ${t11Fmt(p.k4,8)}</div>
        <div style="font-family:var(--font-mono);font-size:.78rem;">y${i} = ${t11Fmt(prev.y,6)} + (1/6)[${t11Fmt(p.k1,4)}+2(${t11Fmt(p.k2,4)})+2(${t11Fmt(p.k3,4)})+${t11Fmt(p.k4,4)}] = <strong style="color:${col};">${t11Fmt(p.y,8)}</strong></div>`;
    }

    cards+=`
    <div class="card t6-step-card" style="margin-bottom:.875rem;border-left:5px solid ${col};">
      <div class="card-header" style="padding:.6rem 1.25rem;">
        <div class="card-header-icon" style="background:${col};width:32px;height:32px;border-radius:8px;
          display:flex;align-items:center;justify-content:center;color:#fff;font-size:.75rem;font-weight:700;">i=${i}</div>
        <div><div class="card-title" style="font-size:.92rem;">x${i} = ${t11Fmt(p.x,4)}</div></div>
        <div style="margin-left:auto;font-family:var(--font-mono);font-weight:700;color:${col};">y${i}=${t11Fmt(p.y,6)}</div>
      </div>
      <div style="padding:.5rem 1.25rem 1rem;display:flex;flex-direction:column;gap:.3rem;">${detail}</div>
    </div>`;
  }
  const truncMsg = pts.length>8 ? `<div style="text-align:center;color:var(--gray-400);font-size:.82rem;padding:.5rem;">… ${pts.length-8} iteraciones más — ver tabla completa →</div>` : '';

  sec.innerHTML=`
  <div class="page-header">
    <h2>${labels[method]} — Iteraciones Paso a Paso</h2>
    <p>Cálculo detallado de cada paso desde x₀=${res.x0} hasta x=${pts.at(-1).x.toFixed(4)}</p>
  </div>
  ${cards}${truncMsg}
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t11GoTo('t11-formula')">← Fórmula</button>
    <button class="btn t11-btn-primary" onclick="t11GoTo('t11-tabla')">Ver Tabla completa →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — TABLA DE RESULTADOS
══════════════════════════════════════════════════════════════ */
function t11RenderTabla(res, method) {
  const sec=document.getElementById('t11-tabla'); if(!sec) return;
  const pts=res[method];
  const colors={euler:T11_EULER,heun:T11_HEUN,rk4:T11_RK4};
  const col=colors[method];
  const labels={euler:'Euler',heun:'Euler Mejorado (Heun)',rk4:'Runge-Kutta 4'};
  const hasExacta = pts[0].exact!==null;

  let rows=pts.map((p,i)=>`<tr style="${i%2===1?'background:var(--gray-50)':''}">
    <td style="padding:.4rem .7rem;text-align:center;font-weight:700;color:${col};">${i}</td>
    <td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;">${t11Fmt(p.x,4)}</td>
    <td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;font-weight:600;">${t11Fmt(p.y,8)}</td>
    ${hasExacta?`<td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:${T11_EXACT};">${t11Fmt(p.exact,8)}</td>`:''}
    ${hasExacta?`<td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:#ef4444;">${t11FmtE(p.err)}</td>`:''}
  </tr>`).join('');

  sec.innerHTML=`
  <div class="page-header">
    <h2>${labels[method]} — Tabla Completa</h2>
    <p>n = ${res.n} pasos · h = ${res.h}</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon" style="background:${col};width:38px;height:38px;border-radius:10px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;">📋</div>
      <div><div class="card-title">Tabla de aproximaciones</div></div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;">
      <thead><tr style="background:${T11_LIGHT};">
        <th style="padding:.45rem .7rem;color:${T11_DARK};border-bottom:2px solid ${col}33;">i</th>
        <th style="padding:.45rem .7rem;color:${T11_DARK};border-bottom:2px solid ${col}33;text-align:right;">xᵢ</th>
        <th style="padding:.45rem .7rem;color:${T11_DARK};border-bottom:2px solid ${col}33;text-align:right;">yᵢ aprox.</th>
        ${hasExacta?`<th style="padding:.45rem .7rem;color:${T11_DARK};border-bottom:2px solid ${col}33;text-align:right;">y(x) exacta</th>`:''}
        ${hasExacta?`<th style="padding:.45rem .7rem;color:${T11_DARK};border-bottom:2px solid ${col}33;text-align:right;">Error |ε|</th>`:''}
      </tr></thead>
      <tbody>${rows}</tbody>
    </table>
    </div>
  </div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t11GoTo('t11-iteraciones')">← Iteraciones</button>
    <button class="btn t11-btn-primary" onclick="t11GoTo('t11-grafica');setTimeout(t11DrawGraph,80);">Ver Gráfica →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   GRÁFICA INTERACTIVA — COMPARACIÓN DE LOS 3 MÉTODOS
══════════════════════════════════════════════════════════════ */
function t11InitGraph() {
  const g=t11State.graph;
  const c=document.getElementById('t11Canvas');
  if(!c||g.canvas) return;
  g.canvas=c; g.ctx=c.getContext('2d');
  const resize=()=>{ const w=c.parentElement.clientWidth||700; c.width=w; c.height=Math.max(340,Math.round(w*0.52)); t11DrawGraph(); };
  resize(); window.addEventListener('resize',resize);

  c.addEventListener('mousedown',e=>{g.dragging=true;g.lastMouse={x:e.clientX,y:e.clientY};c.style.cursor='grabbing';});
  c.addEventListener('mouseup',()=>{g.dragging=false;c.style.cursor='crosshair';});
  c.addEventListener('mouseleave',()=>{g.dragging=false;g.hoverOn=false;c.style.cursor='crosshair';
    const tip=document.getElementById('t11Tooltip');if(tip)tip.style.display='none';t11DrawGraph();});
  c.addEventListener('mousemove',e=>{
    const rect=c.getBoundingClientRect();
    const px=(e.clientX-rect.left)*(c.width/rect.width);
    const py=(e.clientY-rect.top)*(c.height/rect.height);
    const mw=t11ToWorld(px,py);
    g.hoverOn=true;
    const coord=document.getElementById('t11Coords');
    if(coord) coord.innerHTML=`x = ${mw.x.toFixed(3)} &nbsp; y = ${mw.y.toFixed(3)}`;
    if(g.dragging){
      const dx=(e.clientX-g.lastMouse.x)/rect.width*(g.xMax-g.xMin);
      const dy=(e.clientY-g.lastMouse.y)/rect.height*(g.yMax-g.yMin);
      g.xMin-=dx;g.xMax-=dx;g.yMin+=dy;g.yMax+=dy;
      g.lastMouse={x:e.clientX,y:e.clientY};
    }
    t11DrawGraph();
  });
  c.addEventListener('wheel',e=>{
    e.preventDefault();
    const f=e.deltaY>0?1.12:0.89;
    const rect=c.getBoundingClientRect();
    const {x:wx,y:wy}=t11ToWorld((e.clientX-rect.left)*(c.width/rect.width),(e.clientY-rect.top)*(c.height/rect.height));
    g.xMin=wx+(g.xMin-wx)*f;g.xMax=wx+(g.xMax-wx)*f;
    g.yMin=wy+(g.yMin-wy)*f;g.yMax=wy+(g.yMax-wy)*f;
    t11DrawGraph();
  },{passive:false});
}
function t11ToCanvas(wx,wy){
  const g=t11State.graph,PAD={t:24,r:24,b:44,l:60};
  const W=g.canvas.width,H=g.canvas.height;
  return {x:PAD.l+(wx-g.xMin)/(g.xMax-g.xMin)*(W-PAD.l-PAD.r), y:PAD.t+(1-(wy-g.yMin)/(g.yMax-g.yMin))*(H-PAD.t-PAD.b)};
}
function t11ToWorld(px,py){
  const g=t11State.graph,PAD={t:24,r:24,b:44,l:60};
  const W=g.canvas.width,H=g.canvas.height;
  return {x:g.xMin+(px-PAD.l)/(W-PAD.l-PAD.r)*(g.xMax-g.xMin), y:g.yMin+(1-(py-PAD.t)/(H-PAD.t-PAD.b))*(g.yMax-g.yMin)};
}
function t11DrawGraph() {
  const g=t11State.graph, res=t11State.result;
  if(!g.canvas||!res) return;
  const isDark=document.body.classList.contains('dark-mode');
  const W=g.canvas.width,H=g.canvas.height,ctx=g.ctx;
  const PAD={t:24,r:24,b:44,l:60};
  const PW=W-PAD.l-PAD.r,PH=H-PAD.t-PAD.b;
  const niceStep=(range,tgt)=>{const r=range/tgt,m=Math.pow(10,Math.floor(Math.log10(r)));const n=r/m;return(n<1.5?1:n<3.5?2:n<7.5?5:10)*m;};

  ctx.fillStyle=isDark?'#0f172a':'#fff'; ctx.fillRect(0,0,W,H);

  const xSt=niceStep(g.xMax-g.xMin,10), ySt=niceStep(g.yMax-g.yMin,8);
  ctx.strokeStyle=isDark?'rgba(148,163,184,.08)':'#f1f5f9'; ctx.lineWidth=1;
  for(let gx=Math.ceil(g.xMin/xSt)*xSt;gx<=g.xMax;gx+=xSt){const{x:px}=t11ToCanvas(gx,0);ctx.beginPath();ctx.moveTo(px,PAD.t);ctx.lineTo(px,PAD.t+PH);ctx.stroke();}
  for(let gy=Math.ceil(g.yMin/ySt)*ySt;gy<=g.yMax;gy+=ySt){const{y:py}=t11ToCanvas(0,gy);ctx.beginPath();ctx.moveTo(PAD.l,py);ctx.lineTo(PAD.l+PW,py);ctx.stroke();}

  ctx.strokeStyle=isDark?'rgba(148,163,184,.3)':'#cbd5e1'; ctx.lineWidth=1.5;
  const{y:axY}=t11ToCanvas(0,0),{x:axX}=t11ToCanvas(0,0);
  if(g.yMin<=0&&g.yMax>=0){ctx.beginPath();ctx.moveTo(PAD.l,axY);ctx.lineTo(PAD.l+PW,axY);ctx.stroke();}
  if(g.xMin<=0&&g.xMax>=0){ctx.beginPath();ctx.moveTo(axX,PAD.t);ctx.lineTo(axX,PAD.t+PH);ctx.stroke();}

  ctx.fillStyle=isDark?'rgba(148,163,184,.6)':'#94a3b8';
  ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
  const lbY=Math.max(PAD.t+10,Math.min(PAD.t+PH-4,axY+16));
  const lbX=Math.max(PAD.l+28,Math.min(PAD.l+PW-4,axX-8));
  for(let gx=Math.ceil(g.xMin/xSt)*xSt;gx<=g.xMax;gx+=xSt){if(Math.abs(gx)<xSt*.01)continue;const{x:px}=t11ToCanvas(gx,0);ctx.fillText(gx%1===0?gx:gx.toFixed(1),px,lbY);}
  ctx.textAlign='right';
  for(let gy=Math.ceil(g.yMin/ySt)*ySt;gy<=g.yMax;gy+=ySt){if(Math.abs(gy)<ySt*.01)continue;const{y:py}=t11ToCanvas(0,gy);ctx.fillText(gy%1===0?gy:gy.toFixed(1),lbX,py);}
  ctx.textBaseline='alphabetic';

  /* Curva exacta (si existe) */
  if(res.euler[0].exact!==null){
    ctx.beginPath(); ctx.strokeStyle=T11_EXACT; ctx.lineWidth=2; ctx.setLineDash([]);
    const STEPS=150; const dx=(res.xn-res.x0)/STEPS;
    let first=true;
    for(let k=0;k<=STEPS;k++){
      const wx=res.x0+k*dx; const wy=t11EvalExacta(res.exacta,wx);
      if(wy===null||!isFinite(wy)){first=true;continue;}
      const{x:px,y:py}=t11ToCanvas(wx,wy);
      if(first){ctx.moveTo(px,py);first=false;}else ctx.lineTo(px,py);
    }
    ctx.stroke();
  }

  /* 3 métodos */
  const methods=[{pts:res.euler,col:T11_EULER},{pts:res.heun,col:T11_HEUN},{pts:res.rk4,col:T11_RK4}];
  methods.forEach(m=>{
    ctx.beginPath(); ctx.strokeStyle=m.col; ctx.lineWidth=2; ctx.setLineDash([4,3]);
    m.pts.forEach((p,i)=>{const{x:px,y:py}=t11ToCanvas(p.x,p.y); if(i===0)ctx.moveTo(px,py);else ctx.lineTo(px,py);});
    ctx.stroke(); ctx.setLineDash([]);
    m.pts.forEach(p=>{const{x:px,y:py}=t11ToCanvas(p.x,p.y); ctx.beginPath();ctx.arc(px,py,3.5,0,Math.PI*2);ctx.fillStyle=m.col;ctx.fill();});
  });

  /* Leyenda */
  ctx.font='10px "Poppins",sans-serif'; ctx.textBaseline='middle';
  let lx=PAD.l+6, ly=PAD.t+12;
  const legend=[{lbl:'Exacta',col:T11_EXACT,show:res.euler[0].exact!==null},{lbl:'Euler',col:T11_EULER,show:true},{lbl:'Heun',col:T11_HEUN,show:true},{lbl:'RK4',col:T11_RK4,show:true}];
  legend.filter(l=>l.show).forEach(l=>{
    ctx.strokeStyle=l.col;ctx.lineWidth=2.5;ctx.beginPath();ctx.moveTo(lx,ly);ctx.lineTo(lx+18,ly);ctx.stroke();
    ctx.fillStyle=isDark?'#e2e8f0':'#374151';ctx.textAlign='left';ctx.fillText(l.lbl,lx+23,ly);
    lx+=65;
  });
  ctx.textBaseline='alphabetic';

  ctx.fillStyle=isDark?'rgba(190,24,93,.15)':'rgba(148,163,184,.4)';
  ctx.font='600 11px "Poppins",sans-serif'; ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.textBaseline='alphabetic';
}
window.t11DrawGraph=t11DrawGraph;
function t11Zoom(f){const g=t11State.graph;const cx=(g.xMin+g.xMax)/2,cy=(g.yMin+g.yMax)/2;const hw=(g.xMax-g.xMin)/2*f,hh=(g.yMax-g.yMin)/2*f;g.xMin=cx-hw;g.xMax=cx+hw;g.yMin=cy-hh;g.yMax=cy+hh;t11DrawGraph();}
window.t11Zoom=t11Zoom;
function t11ResetView(res){
  const allY=[...res.euler,...res.heun,...res.rk4].map(p=>p.y);
  const allX=res.euler.map(p=>p.x);
  const xr=Math.max(...allX)-Math.min(...allX)||1, yr=Math.max(...allY)-Math.min(...allY)||1;
  const g=t11State.graph;
  g.xMin=Math.min(...allX)-xr*.15; g.xMax=Math.max(...allX)+xr*.15;
  g.yMin=Math.min(...allY)-yr*.25; g.yMax=Math.max(...allY)+yr*.25;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — COMPARACIÓN DE LOS 3 MÉTODOS
══════════════════════════════════════════════════════════════ */
function t11RenderComparar(res) {
  const sec=document.getElementById('t11-comparar'); if(!sec) return;
  const hasExacta = res.euler[0].exact!==null;
  const final = {
    euler: res.euler.at(-1), heun: res.heun.at(-1), rk4: res.rk4.at(-1)
  };

  let rows=`<tr>
    <td style="padding:.45rem .75rem;font-weight:700;color:${T11_EULER};">① Euler</td>
    <td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);">${t11Fmt(final.euler.y,8)}</td>
    ${hasExacta?`<td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);color:#ef4444;">${t11FmtE(final.euler.err)}</td>`:''}
  </tr>
  <tr style="background:var(--gray-50);">
    <td style="padding:.45rem .75rem;font-weight:700;color:${T11_HEUN};">② Euler Mejorado (Heun)</td>
    <td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);">${t11Fmt(final.heun.y,8)}</td>
    ${hasExacta?`<td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);color:#ef4444;">${t11FmtE(final.heun.err)}</td>`:''}
  </tr>
  <tr>
    <td style="padding:.45rem .75rem;font-weight:700;color:${T11_RK4};">③ Runge-Kutta 4</td>
    <td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);">${t11Fmt(final.rk4.y,8)}</td>
    ${hasExacta?`<td style="padding:.45rem .75rem;text-align:right;font-family:var(--font-mono);color:#ef4444;">${t11FmtE(final.rk4.err)}</td>`:''}
  </tr>`;

  sec.innerHTML=`
  <div class="page-header">
    <h2>Comparación — Euler vs Heun vs RK4</h2>
    <p>Resultado final en x = ${final.euler.x.toFixed(4)}${hasExacta?` · y exacta = ${t11Fmt(final.euler.exact,8)}`:''}</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.75rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t11-icon">⚖</div>
      <div><div class="card-title">Precisión relativa de los 3 métodos</div></div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;">
      <thead><tr style="background:${T11_LIGHT};">
        <th style="padding:.5rem .75rem;color:${T11_DARK};border-bottom:2px solid ${T11_COLOR}33;">Método</th>
        <th style="padding:.5rem .75rem;color:${T11_DARK};border-bottom:2px solid ${T11_COLOR}33;text-align:right;">y final</th>
        ${hasExacta?`<th style="padding:.5rem .75rem;color:${T11_DARK};border-bottom:2px solid ${T11_COLOR}33;text-align:right;">Error |ε|</th>`:''}
      </tr></thead>
      <tbody>${rows}</tbody>
    </table>
    </div>
  </div>
  ${hasExacta?`
  <div class="card" style="margin-bottom:1.25rem;background:linear-gradient(135deg,${T11_LIGHT},#fdf2f8);border:2px solid ${T11_COLOR}33;">
    <div class="card-header"><div class="card-header-icon t11-icon">💡</div><div><div class="card-title">Conclusión</div></div></div>
    <div style="padding:.5rem 1.25rem 1.25rem;font-family:var(--font-main);font-size:.85rem;color:var(--gray-600);">
      A igual tamaño de paso h, <strong style="color:${T11_RK4};">Runge-Kutta 4</strong> ofrece la mayor precisión (error O(h⁴)),
      seguido de <strong style="color:${T11_HEUN};">Heun</strong> (O(h²)) y por último <strong style="color:${T11_EULER};">Euler</strong> (O(h)).
    </div>
  </div>`:''}
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t11GoTo('t11-grafica')">← Gráfica</button>
    <button class="btn t11-btn-primary" onclick="t11GoTo('t11-input')">🔁 Nuevos datos</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  document.getElementById('t11H')?.addEventListener('input', t11UpdateHint);
  document.getElementById('t11X0')?.addEventListener('input', t11UpdateHint);
  document.getElementById('t11Xn')?.addEventListener('input', t11UpdateHint);
  function t11UpdateHint(){
    const x0=parseFloat(document.getElementById('t11X0')?.value)||0;
    const xn=parseFloat(document.getElementById('t11Xn')?.value)||0;
    const h=parseFloat(document.getElementById('t11H')?.value)||0.1;
    const n=Math.round((xn-x0)/h);
    const hint=document.getElementById('t11NHint');
    if(hint) hint.textContent=`${n} pasos desde x₀=${x0} hasta xₙ=${xn}`;
  }
  t11UpdateHint();

  document.querySelectorAll('.t11-nav[data-t11]').forEach(el=>{
    el.addEventListener('click',()=>t11GoTo(el.getAttribute('data-t11')));
  });

  /* Ejemplo 1: y'=x+y, y(0)=1 */
  document.getElementById('btnT11Ej1')?.addEventListener('click',()=>{
    document.getElementById('t11Fxy').value='x+y';
    document.getElementById('t11X0').value='0';
    document.getElementById('t11Y0').value='1';
    document.getElementById('t11H').value='0.1';
    document.getElementById('t11Xn').value='0.5';
    document.getElementById('t11Exacta').value='-x-1+2*exp(x)';
    t11UpdateHint();
    clearAlert('t11Alert');
    showAlert('t11Alert','info','📋 Ejemplo clase — y\'=x+y, y(0)=1. Exacta: y=-x-1+2eˣ. Presiona ▶ Resolver.');
  });

  /* Ejemplo 2: y'=x-y, y(0)=2 */
  document.getElementById('btnT11Ej2')?.addEventListener('click',()=>{
    document.getElementById('t11Fxy').value='x-y';
    document.getElementById('t11X0').value='0';
    document.getElementById('t11Y0').value='2';
    document.getElementById('t11H').value='0.1';
    document.getElementById('t11Xn').value='0.5';
    document.getElementById('t11Exacta').value='x-1+3*exp(-x)';
    t11UpdateHint();
    clearAlert('t11Alert');
    showAlert('t11Alert','info','📋 Ejemplo clase — y\'=x−y, y(0)=2. Exacta: y=x-1+3e⁻ˣ. Presiona ▶ Resolver.');
  });

  /* Botón resolver */
  document.getElementById('btnT11Calc')?.addEventListener('click',()=>{
    clearAlert('t11Alert'); clearAlert('t11AlertGlobal');
    const fxy    = document.getElementById('t11Fxy')?.value?.trim()||'x+y';
    const x0     = parseFloat(document.getElementById('t11X0')?.value);
    const y0     = parseFloat(document.getElementById('t11Y0')?.value);
    const h      = parseFloat(document.getElementById('t11H')?.value);
    const xn     = parseFloat(document.getElementById('t11Xn')?.value);
    const exacta = document.getElementById('t11Exacta')?.value?.trim()||'';
    const method = document.querySelector('input[name="t11Method"]:checked')?.value||'euler';

    if(isNaN(x0)||isNaN(y0)){ showAlert('t11Alert','danger','Ingresa x₀ y y₀.'); return; }
    if(isNaN(h)||h<=0){ showAlert('t11Alert','danger','h debe ser positivo.'); return; }
    if(isNaN(xn)||xn<=x0){ showAlert('t11Alert','danger','xₙ debe ser mayor que x₀.'); return; }
    if(isNaN(t11Eval(fxy,x0,y0))){ showAlert('t11Alert','danger','f(x,y) no es válida.'); return; }

    try {
      const res=t11Compute(fxy,x0,y0,h,xn,exacta);
      t11State.result=res;
      t11State.method=method;
      Object.assign(t11State,{fxy,x0,y0,h,xn,exacta});

      t11RenderFormula(res,method);
      t11RenderIteraciones(res,method);
      t11RenderTabla(res,method);
      t11RenderComparar(res);

      const dl=document.getElementById('t11-download-bar');
      if(dl){ dl.dataset.ready='1'; dl.style.display='block'; }

      t11ResetView(res);
      setTimeout(()=>{ t11InitGraph(); t11DrawGraph(); }, 100);

      t11GoTo('t11-formula');
      const labels={euler:'Euler',heun:'Heun',rk4:'RK4'};
      showAlert('t11AlertGlobal','success',
        `✓ ${labels[method]}: y(${xn})≈${t11Fmt(res[method].at(-1).y,6)} · Euler=${t11Fmt(res.euler.at(-1).y,6)} · Heun=${t11Fmt(res.heun.at(-1).y,6)} · RK4=${t11Fmt(res.rk4.at(-1).y,6)}`);

    } catch(e){ showAlert('t11Alert','danger','Error: '+e.message); }
  });

  window.addEventListener('resize',()=>{ if(t11State.result) t11DrawGraph(); });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T11
══════════════════════════════════════════════════════════════ */
(function patchT11Export(){
  document.addEventListener('DOMContentLoaded',()=>{
    if(typeof numerixExport==='undefined') return;
    numerixExport.t11=function(){
      const res=t11State.result;
      if(!res){ alert('Ejecuta el cálculo primero.'); return; }
      const wb=XLSX.utils.book_new();
      const hasE=res.euler[0].exact!==null;

      const info=[
        ['NUMERIX — Métodos de un Paso para EDO','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],['f(x,y)',res.fxy],['x0',res.x0],['y0',res.y0],['h',res.h],['xn',res.xn],['n pasos',res.n],
        hasE?['y(x) exacta',res.exacta]:[],
      ].filter(r=>r.length>0);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet(info),'Info');

      const addSheet=(name,pts)=>{
        const hdr=['i','xi','yi',...(hasE?['y exacta','Error |ε|']:[])];
        const rows=pts.map((p,i)=>[i,p.x,p.y,...(hasE?[p.exact,p.err]:[])]);
        XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet([hdr,...rows]),name);
      };
      addSheet('Euler',res.euler);
      addSheet('Heun',res.heun);
      addSheet('RK4',res.rk4);

      XLSX.writeFile(wb,'NUMERIX_T11_EDO_UnPaso.xlsx');
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   TEMA 12 — SISTEMAS DE ECUACIONES DIFERENCIALES ORDINARIAS
   Runge-Kutta 4to Orden acoplado (2 y 3 variables)
   © 2026 Fernando Granja & Alejandra Tinoco
══════════════════════════════════════════════════════════════ */

const T12_COLOR = '#65a30d';
const T12_LIGHT = '#f7fee7';
const T12_DARK  = '#3f6212';
const T12_X = '#0ea5e9';
const T12_Y = '#f59e0b';
const T12_Z = '#a855f7';

/* ── Estado T12 ─────────────────────────────────────────────── */
const t12State = {
  size:2, fx:'x-y', fy:'x+y', fz:'x+y-z', t0:0, x0:1, y0:0, z0:0, h:0.1, tn:0.5,
  result:null,
  graphT:{canvas:null,ctx:null,xMin:-1,xMax:1,yMin:-2,yMax:2,dragging:false,lastMouse:{x:0,y:0}},
  graphFase:{canvas:null,ctx:null,xMin:-2,xMax:2,yMin:-2,yMax:2,dragging:false,lastMouse:{x:0,y:0}}
};

/* ── Evaluador f(t,x,y,z) ───────────────────────────────────── */
function t12Eval(expr,t,x,y,z) {
  try {
    return new Function('t','x','y','z','PI','sin','cos','tan','exp','log','sqrt','pow','abs',
      `"use strict";return(${expr});`)(t,x,y,z??0,Math.PI,Math.sin,Math.cos,Math.tan,Math.exp,Math.log,Math.sqrt,Math.pow,Math.abs);
  } catch(e){return NaN;}
}

/* ── Navegación T12 ────────────────────────────────────────── */
function t12GoTo(secId){
  document.querySelectorAll('.t12-sec').forEach(s=>s.style.display='none');
  document.querySelectorAll('.t12-nav').forEach(n=>n.classList.remove('active'));
  const sec=document.getElementById(secId);
  if(sec) sec.style.display='block';
  document.querySelectorAll(`[data-t12="${secId}"]`).forEach(el=>el.classList.add('active'));
  const dl=document.getElementById('t12-download-bar');
  if(dl&&dl.dataset.ready==='1'&&secId!=='t12-input') dl.style.display='block';
}
window.t12GoTo = t12GoTo;

/* ── Formato ───────────────────────────────────────────────── */
const t12Fmt = (v,d=8) => (v===null||v===undefined||isNaN(v)) ? '—' : Number(v).toFixed(d);

/* ══════════════════════════════════════════════════════════════
   ALGORITMO — RK4 PARA SISTEMAS 2×2 y 3×3
══════════════════════════════════════════════════════════════ */
function t12RK4System(fx, fy, fz, t0, x0, y0, z0, h, n, size) {
  const pts=[{t:t0, x:x0, y:y0, z:z0}];
  let t=t0, x=x0, y=y0, z=z0;

  for(let i=0;i<n;i++){
    let k1x,k1y,k1z, k2x,k2y,k2z, k3x,k3y,k3z, k4x,k4y,k4z;

    if(size===2){
      k1x = h*t12Eval(fx,t,x,y);
      k1y = h*t12Eval(fy,t,x,y);

      k2x = h*t12Eval(fx, t+h/2, x+k1x/2, y+k1y/2);
      k2y = h*t12Eval(fy, t+h/2, x+k1x/2, y+k1y/2);

      k3x = h*t12Eval(fx, t+h/2, x+k2x/2, y+k2y/2);
      k3y = h*t12Eval(fy, t+h/2, x+k2x/2, y+k2y/2);

      k4x = h*t12Eval(fx, t+h, x+k3x, y+k3y);
      k4y = h*t12Eval(fy, t+h, x+k3x, y+k3y);

      const xNew = x + (k1x+2*k2x+2*k3x+k4x)/6;
      const yNew = y + (k1y+2*k2y+2*k3y+k4y)/6;
      const tNew = t+h;

      pts.push({t:tNew,x:xNew,y:yNew,z:0,
        k1x,k1y,k2x,k2y,k3x,k3y,k4x,k4y,h});
      t=tNew; x=xNew; y=yNew;

    } else {
      k1x = h*t12Eval(fx,t,x,y,z);
      k1y = h*t12Eval(fy,t,x,y,z);
      k1z = h*t12Eval(fz,t,x,y,z);

      k2x = h*t12Eval(fx, t+h/2, x+k1x/2, y+k1y/2, z+k1z/2);
      k2y = h*t12Eval(fy, t+h/2, x+k1x/2, y+k1y/2, z+k1z/2);
      k2z = h*t12Eval(fz, t+h/2, x+k1x/2, y+k1y/2, z+k1z/2);

      k3x = h*t12Eval(fx, t+h/2, x+k2x/2, y+k2y/2, z+k2z/2);
      k3y = h*t12Eval(fy, t+h/2, x+k2x/2, y+k2y/2, z+k2z/2);
      k3z = h*t12Eval(fz, t+h/2, x+k2x/2, y+k2y/2, z+k2z/2);

      k4x = h*t12Eval(fx, t+h, x+k3x, y+k3y, z+k3z);
      k4y = h*t12Eval(fy, t+h, x+k3x, y+k3y, z+k3z);
      k4z = h*t12Eval(fz, t+h, x+k3x, y+k3y, z+k3z);

      const xNew = x + (k1x+2*k2x+2*k3x+k4x)/6;
      const yNew = y + (k1y+2*k2y+2*k3y+k4y)/6;
      const zNew = z + (k1z+2*k2z+2*k3z+k4z)/6;
      const tNew = t+h;

      pts.push({t:tNew,x:xNew,y:yNew,z:zNew,
        k1x,k1y,k1z,k2x,k2y,k2z,k3x,k3y,k3z,k4x,k4y,k4z,h});
      t=tNew; x=xNew; y=yNew; z=zNew;
    }
  }
  return pts;
}

function t12Compute(fx, fy, fz, t0, x0, y0, z0, h, tn, size) {
  const n = Math.round((tn-t0)/h);
  const pts = t12RK4System(fx, fy, fz, t0, x0, y0, z0, h, n, size);
  return { fx, fy, fz, t0, x0, y0, z0, h, tn, n, size, pts };
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — FÓRMULA
══════════════════════════════════════════════════════════════ */
function t12RenderFormula(res) {
  const sec=document.getElementById('t12-formula'); if(!sec) return;
  const {fx,fy,fz,t0,x0,y0,z0,h,size} = res;

  let formulaHtml = size===2 ? `
    <div style="font-family:var(--font-mono);font-size:.85rem;display:flex;flex-direction:column;gap:.4rem;padding:1rem;">
      <div style="color:${T12_X};font-weight:600;">k₁ₓ=h·f(t,x,y) &nbsp;·&nbsp; k₁ᵥ=h·g(t,x,y)</div>
      <div style="color:${T12_X};font-weight:600;">k₂ₓ=h·f(t+h/2,x+k₁ₓ/2,y+k₁ᵥ/2) &nbsp;·&nbsp; k₂ᵥ=h·g(t+h/2,x+k₁ₓ/2,y+k₁ᵥ/2)</div>
      <div style="color:${T12_X};font-weight:600;">k₃ₓ=h·f(t+h/2,x+k₂ₓ/2,y+k₂ᵥ/2) &nbsp;·&nbsp; k₃ᵥ=h·g(t+h/2,x+k₂ₓ/2,y+k₂ᵥ/2)</div>
      <div style="color:${T12_X};font-weight:600;">k₄ₓ=h·f(t+h,x+k₃ₓ,y+k₃ᵥ) &nbsp;·&nbsp; k₄ᵥ=h·g(t+h,x+k₃ₓ,y+k₃ᵥ)</div>
      <div style="border-top:1px solid ${T12_COLOR}33;padding-top:.5rem;margin-top:.25rem;color:${T12_COLOR};font-weight:700;">
        xᵢ₊₁ = xᵢ + (k₁ₓ+2k₂ₓ+2k₃ₓ+k₄ₓ)/6<br>
        yᵢ₊₁ = yᵢ + (k₁ᵥ+2k₂ᵥ+2k₃ᵥ+k₄ᵥ)/6
      </div>
    </div>` : `
    <div style="font-family:var(--font-mono);font-size:.8rem;color:${T12_COLOR};font-weight:600;padding:1rem;">
      Mismo procedimiento RK4 con 3 ecuaciones acopladas (x,y,z) — se calculan k, l, m en paralelo en cada etapa.
    </div>`;

  sec.innerHTML=`
  <div class="page-header">
    <h2>Sistema ${size}×${size} — Fórmula RK4</h2>
    <p>dx/dt = ${fx} &nbsp;·&nbsp; dy/dt = ${fy}${size===3?` &nbsp;·&nbsp; dz/dt = ${fz}`:''}<br>
       x(${t0})=${x0} &nbsp;·&nbsp; y(${t0})=${y0}${size===3?` &nbsp;·&nbsp; z(${t0})=${z0}`:''} &nbsp;·&nbsp; h=${h}</p>
  </div>
  <div class="card t6-step-card" style="margin-bottom:1.25rem;border-left:5px solid ${T12_COLOR};">
    <div class="card-header">
      <div class="card-header-icon t12-icon">RK4</div>
      <div><div class="card-title">Runge-Kutta 4to Orden — Sistema Acoplado</div></div>
    </div>
    ${formulaHtml}
  </div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t12GoTo('t12-input')">← Datos</button>
    <button class="btn t12-btn-primary" onclick="t12GoTo('t12-iteraciones')">Ver Iteraciones →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — ITERACIONES PASO A PASO
══════════════════════════════════════════════════════════════ */
function t12RenderIteraciones(res) {
  const sec=document.getElementById('t12-iteraciones'); if(!sec) return;
  const {pts, size} = res;

  let cards='';
  const showMax=Math.min(pts.length,7);
  for(let i=1;i<showMax;i++){
    const p=pts[i], prev=pts[i-1];

    let kBlock = `
      <div style="font-family:var(--font-mono);font-size:.76rem;">k₁ₓ=${t12Fmt(p.k1x,6)} &nbsp; k₁ᵥ=${t12Fmt(p.k1y,6)}${size===3?` &nbsp; k₁ᵤ=${t12Fmt(p.k1z,6)}`:''}</div>
      <div style="font-family:var(--font-mono);font-size:.76rem;">k₂ₓ=${t12Fmt(p.k2x,6)} &nbsp; k₂ᵥ=${t12Fmt(p.k2y,6)}${size===3?` &nbsp; k₂ᵤ=${t12Fmt(p.k2z,6)}`:''}</div>
      <div style="font-family:var(--font-mono);font-size:.76rem;">k₃ₓ=${t12Fmt(p.k3x,6)} &nbsp; k₃ᵥ=${t12Fmt(p.k3y,6)}${size===3?` &nbsp; k₃ᵤ=${t12Fmt(p.k3z,6)}`:''}</div>
      <div style="font-family:var(--font-mono);font-size:.76rem;">k₄ₓ=${t12Fmt(p.k4x,6)} &nbsp; k₄ᵥ=${t12Fmt(p.k4y,6)}${size===3?` &nbsp; k₄ᵤ=${t12Fmt(p.k4z,6)}`:''}</div>
      <div style="font-family:var(--font-mono);font-size:.8rem;margin-top:.3rem;">
        x${i} = ${t12Fmt(prev.x,6)} + (${t12Fmt(p.k1x,4)}+2(${t12Fmt(p.k2x,4)})+2(${t12Fmt(p.k3x,4)})+${t12Fmt(p.k4x,4)})/6 = <strong style="color:${T12_X};">${t12Fmt(p.x,8)}</strong>
      </div>
      <div style="font-family:var(--font-mono);font-size:.8rem;">
        y${i} = ${t12Fmt(prev.y,6)} + (...)/6 = <strong style="color:${T12_Y};">${t12Fmt(p.y,8)}</strong>
      </div>
      ${size===3?`<div style="font-family:var(--font-mono);font-size:.8rem;">z${i} = ${t12Fmt(prev.z,6)} + (...)/6 = <strong style="color:${T12_Z};">${t12Fmt(p.z,8)}</strong></div>`:''}
    `;

    cards+=`
    <div class="card t6-step-card" style="margin-bottom:.875rem;border-left:5px solid ${T12_COLOR};">
      <div class="card-header" style="padding:.6rem 1.25rem;">
        <div class="card-header-icon" style="background:${T12_COLOR};width:32px;height:32px;border-radius:8px;
          display:flex;align-items:center;justify-content:center;color:#fff;font-size:.75rem;font-weight:700;">i=${i}</div>
        <div><div class="card-title" style="font-size:.92rem;">t${i} = ${t12Fmt(p.t,4)}</div></div>
      </div>
      <div style="padding:.5rem 1.25rem 1rem;display:flex;flex-direction:column;gap:.25rem;">${kBlock}</div>
    </div>`;
  }
  const truncMsg = pts.length>7 ? `<div style="text-align:center;color:var(--gray-400);font-size:.82rem;padding:.5rem;">… ${pts.length-7} iteraciones más — ver tabla completa →</div>` : '';

  sec.innerHTML=`
  <div class="page-header">
    <h2>Iteraciones Paso a Paso — RK4</h2>
    <p>Cálculo detallado de k₁,k₂,k₃,k₄ para cada variable en cada paso.</p>
  </div>
  ${cards}${truncMsg}
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t12GoTo('t12-formula')">← Fórmula</button>
    <button class="btn t12-btn-primary" onclick="t12GoTo('t12-tabla')">Ver Tabla completa →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   RENDERIZADO — TABLA
══════════════════════════════════════════════════════════════ */
function t12RenderTabla(res) {
  const sec=document.getElementById('t12-tabla'); if(!sec) return;
  const {pts, size} = res;

  let rows=pts.map((p,i)=>`<tr style="${i%2===1?'background:var(--gray-50)':''}">
    <td style="padding:.4rem .7rem;text-align:center;font-weight:700;color:${T12_COLOR};">${i}</td>
    <td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;">${t12Fmt(p.t,4)}</td>
    <td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:${T12_X};font-weight:600;">${t12Fmt(p.x,8)}</td>
    <td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:${T12_Y};font-weight:600;">${t12Fmt(p.y,8)}</td>
    ${size===3?`<td style="padding:.4rem .7rem;text-align:right;font-family:var(--font-mono);font-size:.8rem;color:${T12_Z};font-weight:600;">${t12Fmt(p.z,8)}</td>`:''}
  </tr>`).join('');

  sec.innerHTML=`
  <div class="page-header">
    <h2>Tabla de Resultados — Sistema ${size}×${size}</h2>
    <p>n=${res.n} pasos · h=${res.h}</p>
  </div>
  <div class="card" style="padding:0;overflow:hidden;margin-bottom:1.25rem;">
    <div class="card-header" style="padding:.65rem 1.25rem;border-bottom:1px solid var(--border);">
      <div class="card-header-icon t12-icon">📋</div>
      <div><div class="card-title">Tabla de aproximaciones x(t), y(t)${size===3?', z(t)':''}</div></div>
    </div>
    <div style="overflow-x:auto;">
    <table style="width:100%;border-collapse:collapse;">
      <thead><tr style="background:${T12_LIGHT};">
        <th style="padding:.45rem .7rem;color:${T12_DARK};border-bottom:2px solid ${T12_COLOR}33;">i</th>
        <th style="padding:.45rem .7rem;color:${T12_DARK};border-bottom:2px solid ${T12_COLOR}33;text-align:right;">tᵢ</th>
        <th style="padding:.45rem .7rem;color:${T12_X};border-bottom:2px solid ${T12_COLOR}33;text-align:right;">xᵢ</th>
        <th style="padding:.45rem .7rem;color:${T12_Y};border-bottom:2px solid ${T12_COLOR}33;text-align:right;">yᵢ</th>
        ${size===3?`<th style="padding:.45rem .7rem;color:${T12_Z};border-bottom:2px solid ${T12_COLOR}33;text-align:right;">zᵢ</th>`:''}
      </tr></thead>
      <tbody>${rows}</tbody>
    </table>
    </div>
  </div>
  <div style="display:flex;gap:.75rem;justify-content:flex-end;">
    <button class="btn btn-secondary" onclick="t12GoTo('t12-iteraciones')">← Iteraciones</button>
    <button class="btn t12-btn-primary" onclick="t12GoTo('t12-grafica');setTimeout(t12DrawGraphT,80);">Ver Gráfica →</button>
  </div>`;
}

/* ══════════════════════════════════════════════════════════════
   GRÁFICA x(t),y(t) vs t
══════════════════════════════════════════════════════════════ */
function t12InitGraphT() {
  const g=t12State.graphT;
  const c=document.getElementById('t12Canvas');
  if(!c||g.canvas) return;
  g.canvas=c; g.ctx=c.getContext('2d');
  const resize=()=>{ const w=c.parentElement.clientWidth||700; c.width=w; c.height=Math.max(320,Math.round(w*0.48)); t12DrawGraphT(); };
  resize(); window.addEventListener('resize',resize);
  t12AttachPanZoom(c,g,t12DrawGraphT,'t12Coords','t');
}

function t12InitGraphFase() {
  const g=t12State.graphFase;
  const c=document.getElementById('t12CanvasFase');
  if(!c||g.canvas) return;
  g.canvas=c; g.ctx=c.getContext('2d');
  const resize=()=>{ const w=c.parentElement.clientWidth||700; c.width=w; c.height=Math.max(360,Math.round(w*0.62)); t12DrawGraphFase(); };
  resize(); window.addEventListener('resize',resize);
  t12AttachPanZoom(c,g,t12DrawGraphFase,'t12CoordsFase','fase');
}

function t12AttachPanZoom(c,g,drawFn,coordId,kind) {
  c.addEventListener('mousedown',e=>{g.dragging=true;g.lastMouse={x:e.clientX,y:e.clientY};c.style.cursor='grabbing';});
  c.addEventListener('mouseup',()=>{g.dragging=false;c.style.cursor='crosshair';});
  c.addEventListener('mouseleave',()=>{g.dragging=false;c.style.cursor='crosshair';});
  c.addEventListener('mousemove',e=>{
    const rect=c.getBoundingClientRect();
    const px=(e.clientX-rect.left)*(c.width/rect.width);
    const py=(e.clientY-rect.top)*(c.height/rect.height);
    const PAD={t:24,r:24,b:44,l:60};
    const W=c.width,H=c.height;
    const wx=g.xMin+(px-PAD.l)/(W-PAD.l-PAD.r)*(g.xMax-g.xMin);
    const wy=g.yMin+(1-(py-PAD.t)/(H-PAD.t-PAD.b))*(g.yMax-g.yMin);
    const coord=document.getElementById(coordId);
    if(coord) coord.innerHTML = kind==='t'
      ? `t = ${wx.toFixed(3)} &nbsp; valor = ${wy.toFixed(3)}`
      : `x = ${wx.toFixed(3)} &nbsp; y = ${wy.toFixed(3)}`;
    if(g.dragging){
      const dx=(e.clientX-g.lastMouse.x)/rect.width*(g.xMax-g.xMin);
      const dy=(e.clientY-g.lastMouse.y)/rect.height*(g.yMax-g.yMin);
      g.xMin-=dx;g.xMax-=dx;g.yMin+=dy;g.yMax+=dy;
      g.lastMouse={x:e.clientX,y:e.clientY};
    }
    drawFn();
  });
  c.addEventListener('wheel',e=>{
    e.preventDefault();
    const f=e.deltaY>0?1.12:0.89;
    const cx=(g.xMin+g.xMax)/2, cy=(g.yMin+g.yMax)/2;
    const hw=(g.xMax-g.xMin)/2*f, hh=(g.yMax-g.yMin)/2*f;
    g.xMin=cx-hw;g.xMax=cx+hw;g.yMin=cy-hh;g.yMax=cy+hh;
    drawFn();
  },{passive:false});
}

function t12ToCanvasGeneric(g,wx,wy) {
  const PAD={t:24,r:24,b:44,l:60};
  const W=g.canvas.width,H=g.canvas.height;
  return {x:PAD.l+(wx-g.xMin)/(g.xMax-g.xMin)*(W-PAD.l-PAD.r), y:PAD.t+(1-(wy-g.yMin)/(g.yMax-g.yMin))*(H-PAD.t-PAD.b)};
}

function t12DrawAxesGrid(g, isDark) {
  const W=g.canvas.width,H=g.canvas.height,ctx=g.ctx;
  const PAD={t:24,r:24,b:44,l:60};
  const PW=W-PAD.l-PAD.r,PH=H-PAD.t-PAD.b;
  const niceStep=(range,tgt)=>{const r=range/tgt,m=Math.pow(10,Math.floor(Math.log10(r)));const n=r/m;return(n<1.5?1:n<3.5?2:n<7.5?5:10)*m;};

  ctx.fillStyle=isDark?'#0f172a':'#fff'; ctx.fillRect(0,0,W,H);
  const xSt=niceStep(g.xMax-g.xMin,10), ySt=niceStep(g.yMax-g.yMin,8);
  ctx.strokeStyle=isDark?'rgba(148,163,184,.08)':'#f1f5f9'; ctx.lineWidth=1;
  for(let gx=Math.ceil(g.xMin/xSt)*xSt;gx<=g.xMax;gx+=xSt){const{x:px}=t12ToCanvasGeneric(g,gx,0);ctx.beginPath();ctx.moveTo(px,PAD.t);ctx.lineTo(px,PAD.t+PH);ctx.stroke();}
  for(let gy=Math.ceil(g.yMin/ySt)*ySt;gy<=g.yMax;gy+=ySt){const{y:py}=t12ToCanvasGeneric(g,0,gy);ctx.beginPath();ctx.moveTo(PAD.l,py);ctx.lineTo(PAD.l+PW,py);ctx.stroke();}

  ctx.strokeStyle=isDark?'rgba(148,163,184,.3)':'#cbd5e1'; ctx.lineWidth=1.5;
  const{y:axY}=t12ToCanvasGeneric(g,0,0),{x:axX}=t12ToCanvasGeneric(g,0,0);
  if(g.yMin<=0&&g.yMax>=0){ctx.beginPath();ctx.moveTo(PAD.l,axY);ctx.lineTo(PAD.l+PW,axY);ctx.stroke();}
  if(g.xMin<=0&&g.xMax>=0){ctx.beginPath();ctx.moveTo(axX,PAD.t);ctx.lineTo(axX,PAD.t+PH);ctx.stroke();}

  ctx.fillStyle=isDark?'rgba(148,163,184,.6)':'#94a3b8';
  ctx.font='10px "JetBrains Mono",monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
  const lbY=Math.max(PAD.t+10,Math.min(PAD.t+PH-4,axY+16));
  const lbX=Math.max(PAD.l+28,Math.min(PAD.l+PW-4,axX-8));
  for(let gx=Math.ceil(g.xMin/xSt)*xSt;gx<=g.xMax;gx+=xSt){if(Math.abs(gx)<xSt*.01)continue;const{x:px}=t12ToCanvasGeneric(g,gx,0);ctx.fillText(gx%1===0?gx:gx.toFixed(1),px,lbY);}
  ctx.textAlign='right';
  for(let gy=Math.ceil(g.yMin/ySt)*ySt;gy<=g.yMax;gy+=ySt){if(Math.abs(gy)<ySt*.01)continue;const{y:py}=t12ToCanvasGeneric(g,0,gy);ctx.fillText(gy%1===0?gy:gy.toFixed(1),lbX,py);}
  ctx.textBaseline='alphabetic';

  return {PAD,PW,PH};
}

function t12DrawGraphT() {
  const g=t12State.graphT, res=t12State.result;
  if(!g.canvas||!res) return;
  const isDark=document.body.classList.contains('dark-mode');
  t12DrawAxesGrid(g, isDark);
  const ctx=g.ctx, W=g.canvas.width, H=g.canvas.height;

  const series=[{key:'x',col:T12_X,lbl:'x(t)'},{key:'y',col:T12_Y,lbl:'y(t)'}];
  if(res.size===3) series.push({key:'z',col:T12_Z,lbl:'z(t)'});

  series.forEach(s=>{
    ctx.beginPath(); ctx.strokeStyle=s.col; ctx.lineWidth=2.5; ctx.setLineDash([]);
    res.pts.forEach((p,i)=>{const{x:px,y:py}=t12ToCanvasGeneric(g,p.t,p[s.key]); if(i===0)ctx.moveTo(px,py);else ctx.lineTo(px,py);});
    ctx.stroke();
    res.pts.forEach(p=>{const{x:px,y:py}=t12ToCanvasGeneric(g,p.t,p[s.key]); ctx.beginPath();ctx.arc(px,py,3,0,Math.PI*2);ctx.fillStyle=s.col;ctx.fill();});
  });

  /* Leyenda */
  ctx.font='11px "Poppins",sans-serif'; ctx.textBaseline='middle';
  let lx=70, ly=24;
  series.forEach(s=>{
    ctx.strokeStyle=s.col;ctx.lineWidth=2.5;ctx.beginPath();ctx.moveTo(lx,ly);ctx.lineTo(lx+20,ly);ctx.stroke();
    ctx.fillStyle=isDark?'#e2e8f0':'#374151';ctx.textAlign='left';ctx.fillText(s.lbl,lx+25,ly);
    lx+=80;
  });
  ctx.textBaseline='alphabetic';
  ctx.fillStyle=isDark?'rgba(101,163,13,.15)':'rgba(148,163,184,.4)';
  ctx.font='600 11px "Poppins",sans-serif'; ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.textBaseline='alphabetic';
}
window.t12DrawGraphT = t12DrawGraphT;

function t12DrawGraphFase() {
  const g=t12State.graphFase, res=t12State.result;
  if(!g.canvas||!res) return;
  const isDark=document.body.classList.contains('dark-mode');
  t12DrawAxesGrid(g, isDark);
  const ctx=g.ctx, W=g.canvas.width, H=g.canvas.height;

  /* Trayectoria x vs y */
  ctx.beginPath(); ctx.strokeStyle=T12_COLOR; ctx.lineWidth=2.5;
  res.pts.forEach((p,i)=>{const{x:px,y:py}=t12ToCanvasGeneric(g,p.x,p.y); if(i===0)ctx.moveTo(px,py);else ctx.lineTo(px,py);});
  ctx.stroke();

  /* Puntos con gradiente de color (inicio verde, fin rojo) */
  res.pts.forEach((p,i)=>{
    const t=i/(res.pts.length-1);
    const r=Math.round(16+(239-16)*t), gg=Math.round(185+(68-185)*t), b=Math.round(129+(68-129)*t);
    const{x:px,y:py}=t12ToCanvasGeneric(g,p.x,p.y);
    ctx.beginPath();ctx.arc(px,py,i===0||i===res.pts.length-1?6:3,0,Math.PI*2);
    ctx.fillStyle=`rgb(${r},${gg},${b})`;ctx.fill();
    if(i===0||i===res.pts.length-1){ ctx.strokeStyle='#fff'; ctx.lineWidth=1.5; ctx.stroke(); }
  });

  /* Etiquetas inicio/fin */
  const p0=res.pts[0], pf=res.pts.at(-1);
  const c0=t12ToCanvasGeneric(g,p0.x,p0.y), cf=t12ToCanvasGeneric(g,pf.x,pf.y);
  ctx.font='10px "Poppins",sans-serif'; ctx.textAlign='center'; ctx.fillStyle=isDark?'#e2e8f0':'#374151';
  ctx.fillText('Inicio',c0.x,c0.y-12);
  ctx.fillText('Fin',cf.x,cf.y-12);

  ctx.fillStyle=isDark?'rgba(101,163,13,.15)':'rgba(148,163,184,.4)';
  ctx.font='600 11px "Poppins",sans-serif'; ctx.textAlign='right'; ctx.textBaseline='bottom';
  ctx.fillText('NUMERIX © 2026',W-10,H-8); ctx.textBaseline='alphabetic';
}
window.t12DrawGraphFase = t12DrawGraphFase;

function t12Zoom(f,kind) {
  const g = kind==='t' ? t12State.graphT : t12State.graphFase;
  const cx=(g.xMin+g.xMax)/2, cy=(g.yMin+g.yMax)/2;
  const hw=(g.xMax-g.xMin)/2*f, hh=(g.yMax-g.yMin)/2*f;
  g.xMin=cx-hw;g.xMax=cx+hw;g.yMin=cy-hh;g.yMax=cy+hh;
  if(kind==='t') t12DrawGraphT(); else t12DrawGraphFase();
}
window.t12Zoom = t12Zoom;

function t12ResetViews(res) {
  const ts=res.pts.map(p=>p.t);
  const allVals=[...res.pts.map(p=>p.x),...res.pts.map(p=>p.y),...(res.size===3?res.pts.map(p=>p.z):[])];
  const tr=Math.max(...ts)-Math.min(...ts)||1, vr=Math.max(...allVals)-Math.min(...allVals)||1;
  const gT=t12State.graphT;
  gT.xMin=Math.min(...ts)-tr*.1; gT.xMax=Math.max(...ts)+tr*.1;
  gT.yMin=Math.min(...allVals)-vr*.2; gT.yMax=Math.max(...allVals)+vr*.2;

  const xs=res.pts.map(p=>p.x), ys=res.pts.map(p=>p.y);
  const xr=Math.max(...xs)-Math.min(...xs)||1, yr=Math.max(...ys)-Math.min(...ys)||1;
  const gF=t12State.graphFase;
  gF.xMin=Math.min(...xs)-xr*.2; gF.xMax=Math.max(...xs)+xr*.2;
  gF.yMin=Math.min(...ys)-yr*.2; gF.yMax=Math.max(...ys)+yr*.2;
}

/* ══════════════════════════════════════════════════════════════
   FLUJO PRINCIPAL
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {

  /* Toggle tamaño del sistema 2x2 / 3x3 */
  const t12SizeRadios=document.querySelectorAll('input[name="t12Size"]');
  const updateSizeUI=()=>{
    const size=document.querySelector('input[name="t12Size"]:checked')?.value||'2';
    const show3=size==='3';
    document.getElementById('t12FzGroup').style.display = show3?'block':'none';
    document.getElementById('t12Z0Group').style.display = show3?'block':'none';
    document.getElementById('t12Zlabel1').style.display = show3?'inline':'none';
    document.getElementById('t12Zlabel2').style.display = show3?'inline':'none';
  };
  t12SizeRadios.forEach(r=>r.addEventListener('change',updateSizeUI));
  updateSizeUI();

  /* Hint de pasos */
  const updateHint=()=>{
    const t0=parseFloat(document.getElementById('t12T0')?.value)||0;
    const tn=parseFloat(document.getElementById('t12Tn')?.value)||0;
    const h=parseFloat(document.getElementById('t12H')?.value)||0.1;
    const n=Math.round((tn-t0)/h);
    const hint=document.getElementById('t12NHint');
    if(hint) hint.textContent=`${n} pasos desde t₀=${t0} hasta tₙ=${tn}`;
  };
  ['t12T0','t12Tn','t12H'].forEach(id=>document.getElementById(id)?.addEventListener('input',updateHint));
  updateHint();

  document.querySelectorAll('.t12-nav[data-t12]').forEach(el=>{
    el.addEventListener('click',()=>t12GoTo(el.getAttribute('data-t12')));
  });

  /* Ejemplo 1: oscilador x'=x-y, y'=x+y */
  document.getElementById('btnT12Ej1')?.addEventListener('click',()=>{
    document.querySelector('input[name="t12Size"][value="2"]').checked=true; updateSizeUI();
    document.getElementById('t12Fx').value='x-y';
    document.getElementById('t12Fy').value='x+y';
    document.getElementById('t12T0').value='0';
    document.getElementById('t12X0').value='1';
    document.getElementById('t12Y0').value='0';
    document.getElementById('t12H').value='0.1';
    document.getElementById('t12Tn').value='0.5';
    updateHint();
    clearAlert('t12Alert');
    showAlert('t12Alert','info','📋 Ejemplo oscilador — x\'=x−y, y\'=x+y, x(0)=1, y(0)=0. Presiona ▶ Resolver.');
  });

  /* Ejemplo 2: depredador-presa simplificado */
  document.getElementById('btnT12Ej2')?.addEventListener('click',()=>{
    document.querySelector('input[name="t12Size"][value="2"]').checked=true; updateSizeUI();
    document.getElementById('t12Fx').value='x*(1-y)';
    document.getElementById('t12Fy').value='y*(x-1)*0.5';
    document.getElementById('t12T0').value='0';
    document.getElementById('t12X0').value='2';
    document.getElementById('t12Y0').value='1';
    document.getElementById('t12H').value='0.1';
    document.getElementById('t12Tn').value='2';
    updateHint();
    clearAlert('t12Alert');
    showAlert('t12Alert','info','📋 Ejemplo depredador-presa — x\'=x(1−y), y\'=0.5y(x−1). Presiona ▶ Resolver.');
  });

  /* Botón resolver */
  document.getElementById('btnT12Calc')?.addEventListener('click',()=>{
    clearAlert('t12Alert'); clearAlert('t12AlertGlobal');
    const size = parseInt(document.querySelector('input[name="t12Size"]:checked')?.value)||2;
    const fx = document.getElementById('t12Fx')?.value?.trim()||'x-y';
    const fy = document.getElementById('t12Fy')?.value?.trim()||'x+y';
    const fz = document.getElementById('t12Fz')?.value?.trim()||'x+y-z';
    const t0 = parseFloat(document.getElementById('t12T0')?.value);
    const x0 = parseFloat(document.getElementById('t12X0')?.value);
    const y0 = parseFloat(document.getElementById('t12Y0')?.value);
    const z0 = parseFloat(document.getElementById('t12Z0')?.value)||0;
    const h  = parseFloat(document.getElementById('t12H')?.value);
    const tn = parseFloat(document.getElementById('t12Tn')?.value);

    if(isNaN(t0)||isNaN(x0)||isNaN(y0)){ showAlert('t12Alert','danger','Completa t₀, x₀, y₀.'); return; }
    if(size===3 && isNaN(z0)){ showAlert('t12Alert','danger','Completa z₀.'); return; }
    if(isNaN(h)||h<=0){ showAlert('t12Alert','danger','h debe ser positivo.'); return; }
    if(isNaN(tn)||tn<=t0){ showAlert('t12Alert','danger','tₙ debe ser mayor que t₀.'); return; }
    if(isNaN(t12Eval(fx,t0,x0,y0,z0))){ showAlert('t12Alert','danger','dx/dt no es válida.'); return; }
    if(isNaN(t12Eval(fy,t0,x0,y0,z0))){ showAlert('t12Alert','danger','dy/dt no es válida.'); return; }
    if(size===3 && isNaN(t12Eval(fz,t0,x0,y0,z0))){ showAlert('t12Alert','danger','dz/dt no es válida.'); return; }

    try {
      const res=t12Compute(fx,fy,fz,t0,x0,y0,z0,h,tn,size);
      t12State.result=res;
      Object.assign(t12State,{size,fx,fy,fz,t0,x0,y0,z0,h,tn});

      t12RenderFormula(res);
      t12RenderIteraciones(res);
      t12RenderTabla(res);

      const dl=document.getElementById('t12-download-bar');
      if(dl){ dl.dataset.ready='1'; dl.style.display='block'; }

      t12ResetViews(res);
      setTimeout(()=>{ t12InitGraphT(); t12InitGraphFase(); t12DrawGraphT(); t12DrawGraphFase(); }, 100);

      t12GoTo('t12-formula');
      const final=res.pts.at(-1);
      showAlert('t12AlertGlobal','success',
        `✓ Sistema ${size}×${size} resuelto — x(${tn})≈${t12Fmt(final.x,6)} · y(${tn})≈${t12Fmt(final.y,6)}${size===3?` · z(${tn})≈${t12Fmt(final.z,6)}`:''}`);

    } catch(e){ showAlert('t12Alert','danger','Error: '+e.message); }
  });

  window.addEventListener('resize',()=>{ if(t12State.result){ t12DrawGraphT(); t12DrawGraphFase(); } });
});

/* ══════════════════════════════════════════════════════════════
   EXPORTACIÓN EXCEL T12
══════════════════════════════════════════════════════════════ */
(function patchT12Export(){
  document.addEventListener('DOMContentLoaded',()=>{
    if(typeof numerixExport==='undefined') return;
    numerixExport.t12=function(){
      const res=t12State.result;
      if(!res){ alert('Ejecuta el cálculo primero.'); return; }
      const wb=XLSX.utils.book_new();

      const info=[
        ['NUMERIX — Sistemas de EDO (RK4)','','© 2026 Fernando Granja & Alejandra Tinoco'],
        [],['Tamaño',`${res.size}×${res.size}`],
        ['dx/dt',res.fx],['dy/dt',res.fy], res.size===3?['dz/dt',res.fz]:[],
        ['t0',res.t0],['x0',res.x0],['y0',res.y0], res.size===3?['z0',res.z0]:[],
        ['h',res.h],['tn',res.tn],['n pasos',res.n],
      ].filter(r=>r.length>0);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet(info),'Info');

      const hdr=['i','t','x','y',...(res.size===3?['z']:[])];
      const rows=res.pts.map((p,i)=>[i,p.t,p.x,p.y,...(res.size===3?[p.z]:[])]);
      XLSX.utils.book_append_sheet(wb,XLSX.utils.aoa_to_sheet([hdr,...rows]),'Resultados RK4');

      XLSX.writeFile(wb,'NUMERIX_T12_SistemasEDO.xlsx');
    };
  });
})();


/* ══════════════════════════════════════════════════════════════
   FIX — NAVEGACIÓN DE TEMAS: SCROLL HORIZONTAL CON MOUSE
   Antes: solo se podía desplazar con touch (celular) o
   shift+rueda del mouse (poco intuitivo, casi nadie lo sabe).
   Ahora: drag con clic sostenido + botones de flecha ‹ ›
══════════════════════════════════════════════════════════════ */
document.addEventListener('DOMContentLoaded', () => {
  const nav = document.getElementById('themeNav');
  const btnLeft  = document.getElementById('themeNavArrowLeft');
  const btnRight = document.getElementById('themeNavArrowRight');
  if (!nav) return;

  /* ── Drag-to-scroll con el mouse ── */
  let isDown = false, startX = 0, startScroll = 0;

  nav.addEventListener('mousedown', (e) => {
    isDown = true;
    nav.classList.add('is-dragging');
    startX = e.pageX;
    startScroll = nav.scrollLeft;
  });

  window.addEventListener('mouseup', () => {
    isDown = false;
    nav.classList.remove('is-dragging');
  });

  window.addEventListener('mousemove', (e) => {
    if (!isDown) return;
    e.preventDefault();
    const dx = e.pageX - startX;
    nav.scrollLeft = startScroll - dx;
  });

  /* Evitar que el drag dispare el click del botón de tab al soltar */
  let dragDistance = 0;
  nav.addEventListener('mousedown', (e) => { dragDistance = 0; startX = e.pageX; });
  nav.addEventListener('mousemove', (e) => { if (isDown) dragDistance = Math.abs(e.pageX - startX); });
  nav.addEventListener('click', (e) => {
    if (dragDistance > 6) { e.preventDefault(); e.stopPropagation(); }
  }, true);

  /* ── Botones de flecha ── */
  const SCROLL_STEP = 220;
  btnLeft?.addEventListener('click', () => {
    nav.scrollBy({ left: -SCROLL_STEP, behavior: 'smooth' });
  });
  btnRight?.addEventListener('click', () => {
    nav.scrollBy({ left: SCROLL_STEP, behavior: 'smooth' });
  });

  /* ── Habilitar/deshabilitar flechas según posición ── */
  function updateArrowState() {
    if (!btnLeft || !btnRight) return;
    const maxScroll = nav.scrollWidth - nav.clientWidth;
    btnLeft.disabled  = nav.scrollLeft <= 2;
    btnRight.disabled = nav.scrollLeft >= maxScroll - 2;
    /* Si no hay overflow real, ocultar ambas flechas */
    const noOverflow = maxScroll <= 2;
    btnLeft.style.display  = noOverflow ? 'none' : '';
    btnRight.style.display = noOverflow ? 'none' : '';
  }

  nav.addEventListener('scroll', updateArrowState);
  window.addEventListener('resize', updateArrowState);
  /* Estado inicial (con pequeño delay para asegurar layout calculado) */
  setTimeout(updateArrowState, 100);

  /* ── Al hacer clic en un tab, centrarlo si quedó cerca del borde ── */
  nav.addEventListener('click', (e) => {
    const tab = e.target.closest('.theme-tab');
    if (!tab) return;
    const tabRect = tab.getBoundingClientRect();
    const navRect = nav.getBoundingClientRect();
    if (tabRect.left < navRect.left + 20 || tabRect.right > navRect.right - 20) {
      tab.scrollIntoView({ behavior: 'smooth', inline: 'center', block: 'nearest' });
    }
  });
});
