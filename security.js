/* ══════════════════════════════════════════════════════════════
   NUMERIX — MÓDULO DE PROTECCIÓN Y AUTORÍA
   ────────────────────────────────────────────────────────────
   Autores: Fernando Granja · Alejandra Tinoco
   Universidad Nacional de Ingeniería (UNI) — Managua, Nicaragua
   © 2026 — Todos los derechos reservados.

   AVISO LEGAL DE AUTORÍA:
   Este software fue desarrollado íntegramente por Fernando Granja
   y Alejandra Tinoco como proyecto académico para la asignatura
   de Métodos Numéricos. Queda prohibida su reproducción total o
   parcial, distribución, o presentación como obra propia por
   terceros sin autorización expresa de los autores.

   NOTA TÉCNICA HONESTA:
   Estas medidas disuaden la copia casual (clic derecho, atajos
   de teclado, curiosidad de compañeros de clase) y dejan
   evidencia de autoría. NO constituyen cifrado ni hacen el
   código "irrompible" — cualquier persona con conocimientos de
   desarrollo web puede acceder al código fuente de cualquier
   sitio que se ejecuta en su navegador. Esa es una limitación
   estructural de la web, no un defecto de esta implementación.
══════════════════════════════════════════════════════════════ */

(function() {
  'use strict';

  /* ── Identificador único de build (hash simple) ──────────── */
  const BUILD_ID = 'NMX-' + (function(s){
    let h = 0;
    for (let i = 0; i < s.length; i++) {
      h = ((h << 5) - h + s.charCodeAt(i)) | 0;
    }
    return Math.abs(h).toString(36).toUpperCase();
  })('Fernando Granja & Alejandra Tinoco - UNI - Metodos Numericos - 2026');

  const AUTHORS = 'Fernando Granja & Alejandra Tinoco';
  const INSTITUTION = 'Universidad Nacional de Ingeniería (UNI) · Managua, Nicaragua';
  const COURSE = 'Métodos Numéricos · 2026';

  /* ══════════════════════════════════════════════════════════
     1. MENSAJE DE AUTORÍA EN CONSOLA
     Si alguien abre la consola, lo primero que ve es esto.
  ══════════════════════════════════════════════════════════ */
  function printConsoleNotice() {
    const line = '─'.repeat(64);
    console.log('%c' + line, 'color:#7c3aed;font-weight:bold;');
    console.log('%cNUMERIX — Plataforma de Métodos Numéricos', 'color:#7c3aed;font-size:16px;font-weight:bold;');
    console.log('%cAutores: ' + AUTHORS, 'color:#475569;font-size:13px;');
    console.log('%c' + INSTITUTION, 'color:#475569;font-size:12px;');
    console.log('%c' + COURSE, 'color:#475569;font-size:12px;');
    console.log('%cBuild ID: ' + BUILD_ID, 'color:#94a3b8;font-size:11px;font-family:monospace;');
    console.log('%c' + line, 'color:#7c3aed;font-weight:bold;');
    console.log('%c⚠ AVISO DE AUTORÍA', 'color:#dc2626;font-size:14px;font-weight:bold;');
    console.log('%cEste proyecto es trabajo académico original de los autores arriba mencionados.\nSu copia, redistribución o presentación como obra propia sin autorización\nconstituye plagio académico.', 'color:#475569;font-size:12px;');
    console.log('%c' + line, 'color:#7c3aed;font-weight:bold;');
  }

  /* ══════════════════════════════════════════════════════════
     2. BLOQUEO DE CLIC DERECHO
  ══════════════════════════════════════════════════════════ */
  function blockContextMenu() {
    document.addEventListener('contextmenu', function(e) {
      e.preventDefault();
      showProtectionToast('Clic derecho deshabilitado — Proyecto de ' + AUTHORS);
    }, false);
  }

  /* ══════════════════════════════════════════════════════════
     3. BLOQUEO DE ATAJOS DE TECLADO COMUNES
     F12, Ctrl+U (ver código fuente), Ctrl+S (guardar página),
     Ctrl+Shift+I/J/C (DevTools), Ctrl+P (imprimir a PDF)
  ══════════════════════════════════════════════════════════ */
  function blockKeyShortcuts() {
    document.addEventListener('keydown', function(e) {
      const key = e.key;
      const ctrl = e.ctrlKey || e.metaKey;
      const shift = e.shiftKey;

      const blocked =
        key === 'F12' ||
        (ctrl && key.toLowerCase() === 'u') ||
        (ctrl && key.toLowerCase() === 's') ||
        (ctrl && shift && ['i','j','c'].includes(key.toLowerCase())) ||
        (ctrl && key.toLowerCase() === 'p');

      if (blocked) {
        e.preventDefault();
        showProtectionToast('Acción restringida — Proyecto de ' + AUTHORS);
      }
    }, false);
  }

  /* ══════════════════════════════════════════════════════════
     4. DETECCIÓN BÁSICA DE DEVTOOLS ABIERTAS
     Heurística por diferencia de tamaño de ventana — no es
     infalible (puede dar falsos positivos/negativos) pero
     funciona razonablemente bien en la mayoría de navegadores.
  ══════════════════════════════════════════════════════════ */
  function detectDevTools() {
    let warned = false;
    const threshold = 160;

    function check() {
      const widthDiff = window.outerWidth - window.innerWidth > threshold;
      const heightDiff = window.outerHeight - window.innerHeight > threshold;
      if ((widthDiff || heightDiff) && !warned) {
        warned = true;
        showDevToolsOverlay();
      } else if (!widthDiff && !heightDiff) {
        warned = false;
        hideDevToolsOverlay();
      }
    }
    setInterval(check, 1000);
  }

  function showDevToolsOverlay() {
    let overlay = document.getElementById('nmx-devtools-warning');
    if (overlay) { overlay.style.display = 'flex'; return; }
    overlay = document.createElement('div');
    overlay.id = 'nmx-devtools-warning';
    overlay.innerHTML = `
      <div class="nmx-warning-box">
        <div class="nmx-warning-icon">⚠</div>
        <div class="nmx-warning-title">Herramientas de desarrollo detectadas</div>
        <div class="nmx-warning-text">
          Este es un proyecto académico original de <strong>${AUTHORS}</strong><br>
          ${INSTITUTION}<br><br>
          Si eres profesor o evaluador, puedes continuar revisando con normalidad.<br>
          Si buscas copiar el código, te recordamos que esto constituye plagio académico.
        </div>
        <button class="nmx-warning-close" onclick="document.getElementById('nmx-devtools-warning').style.display='none'">
          Entendido, continuar
        </button>
      </div>`;
    document.body.appendChild(overlay);
  }
  function hideDevToolsOverlay() {
    const overlay = document.getElementById('nmx-devtools-warning');
    if (overlay) overlay.style.display = 'none';
  }

  /* ══════════════════════════════════════════════════════════
     5. TOAST DE NOTIFICACIÓN (clic derecho / atajo bloqueado)
  ══════════════════════════════════════════════════════════ */
  let toastTimeout = null;
  function showProtectionToast(msg) {
    let toast = document.getElementById('nmx-protection-toast');
    if (!toast) {
      toast = document.createElement('div');
      toast.id = 'nmx-protection-toast';
      document.body.appendChild(toast);
    }
    toast.textContent = '🔒 ' + msg;
    toast.classList.add('nmx-toast-show');
    clearTimeout(toastTimeout);
    toastTimeout = setTimeout(() => toast.classList.remove('nmx-toast-show'), 2200);
  }

  /* ══════════════════════════════════════════════════════════
     6. WATERMARK VISIBLE EN EL FOOTER (si existe)
  ══════════════════════════════════════════════════════════ */
  function injectFooterWatermark() {
    document.addEventListener('DOMContentLoaded', function() {
      const footer = document.querySelector('footer, .footer, #footer');
      if (!footer) return;
      const wm = document.createElement('div');
      wm.style.cssText = 'text-align:center;padding:.5rem;font-size:.68rem;' +
        'color:var(--gray-400, #94a3b8);font-family:monospace;opacity:.7;';
      wm.textContent = `Build ${BUILD_ID} · © 2026 ${AUTHORS} · ${INSTITUTION}`;
      footer.appendChild(wm);
    });
  }

  /* ══════════════════════════════════════════════════════════
     7. SELECCIÓN DE TEXTO DESHABILITADA (opcional, vía CSS)
     Se aplica clase global; inputs/textareas quedan exentos
     mediante las reglas CSS correspondientes en styles.css
  ══════════════════════════════════════════════════════════ */
  function disableTextSelection() {
    document.documentElement.classList.add('nmx-no-select');
  }

  /* ══════════════════════════════════════════════════════════
     INICIALIZACIÓN
  ══════════════════════════════════════════════════════════ */
  function init() {
    printConsoleNotice();
    blockContextMenu();
    blockKeyShortcuts();
    detectDevTools();
    injectFooterWatermark();
    disableTextSelection();

    /* Re-imprimir aviso si alguien limpia la consola */
    setInterval(printConsoleNotice, 30000);

    /* Exponer metadatos de forma controlada, por si se necesita verificar autoría */
    window.NUMERIX_META = Object.freeze({
      authors: AUTHORS,
      institution: INSTITUTION,
      course: COURSE,
      buildId: BUILD_ID,
      year: 2026
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
