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
    const {canvas:c,ctx,xMin,xMax,yMin,yMax,bgDark}=eng;
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
    try { if (typeof graphDraw   === 'function') graphDraw();   } catch(e) {}
    try { if (typeof t1GraphDraw === 'function') t1GraphDraw(); } catch(e) {}
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
