/*
 * GoLean interactive board — plain-JS React component for the Lean infoview.
 *
 * View-only: every click/button builds an ActionDto and calls the Lean RPC
 * method 'GoLean.update'; the Lean core computes all rules. The client-held
 * state is the event log ({ config, actions }) plus the last ViewDto.
 */
import * as React from 'react';
import { useRpcSession, mapRpcError } from '@leanprover/infoview';

const h = React.createElement;

/* Mirrors of GoLean.Ruleset presets — form-filling convenience only;
 * the Lean side re-validates and is the sole authority on the rules. */
const PRESETS = {
  'japanese': { ko: 'simple', scoring: 'territory', selfCaptureAllowed: false, komi: 6.5 },
  'chinese': { ko: 'positional', scoring: 'area', selfCaptureAllowed: false, komi: 7.5 },
  'tromp-taylor': { ko: 'positional', scoring: 'area', selfCaptureAllowed: true, komi: 7.5 },
  'aga': { ko: 'situational', scoring: 'area', selfCaptureAllowed: false, komi: 7.5 },
};

const DEFAULT_FORM = {
  preset: 'japanese',
  sizeChoice: '19',
  rows: 19, cols: 19,
  blackName: 'Black', whiteName: 'White',
  handicap: 0, komi: 6.5,
  ko: 'simple', scoring: 'territory',
  selfCaptureAllowed: false, passesToScore: 2,
  sgfText: '',
};

const COLORS = {
  wood: '#dcb35c',
  line: '#54432b',
  black: '#1c1c1c',
  white: '#f4f4f4',
  territoryBlack: 'rgba(20,20,20,0.85)',
  territoryWhite: 'rgba(250,250,250,0.95)',
  marker: '#e0452b',
};

function formToConfig(f) {
  return {
    rows: Math.max(2, Number(f.rows) || 19),
    cols: Math.max(2, Number(f.cols) || 19),
    handicap: Math.max(0, Number(f.handicap) || 0),
    komi2: Math.round((Number(f.komi) || 0) * 2),
    blackName: f.blackName || 'Black',
    whiteName: f.whiteName || 'White',
    ko: f.ko,
    scoring: f.scoring,
    selfCaptureAllowed: !!f.selfCaptureAllowed,
    passesToScore: Math.max(1, Number(f.passesToScore) || 2),
    setupBlack: [],
    setupWhite: [],
    firstToMove: '',
  };
}

/* ---------------- board (SVG) ---------------- */

function Board({ view, phase, onClickPoint }) {
  const [hover, setHover] = React.useState(null);
  const rows = view.rows, cols = view.cols;
  const u = 24, pad = 30, sr = 10.8;
  const W = 2 * pad + (cols - 1) * u, H = 2 * pad + (rows - 1) * u;
  const x = (c) => pad + c * u, y = (r) => pad + r * u;
  const els = [];

  els.push(h('rect', { key: 'bg', x: 2, y: 2, width: W - 4, height: H - 4, rx: 6, fill: COLORS.wood }));

  for (let r = 0; r < rows; r++)
    els.push(h('line', { key: 'hl' + r, x1: x(0), y1: y(r), x2: x(cols - 1), y2: y(r), stroke: COLORS.line, strokeWidth: r === 0 || r === rows - 1 ? 1.6 : 0.9 }));
  for (let c = 0; c < cols; c++)
    els.push(h('line', { key: 'vl' + c, x1: x(c), y1: y(0), x2: x(c), y2: y(rows - 1), stroke: COLORS.line, strokeWidth: c === 0 || c === cols - 1 ? 1.6 : 0.9 }));

  const lbl = (key, tx, ty, text) =>
    h('text', { key, x: tx, y: ty, fontSize: 9.5, fill: COLORS.line, textAnchor: 'middle', dominantBaseline: 'middle', fontFamily: 'sans-serif' }, text);
  for (let c = 0; c < cols; c++) {
    const lblText = view.colLabels[c] || '';
    els.push(lbl('ct' + c, x(c), pad - 17, lblText));
    els.push(lbl('cb' + c, x(c), H - pad + 17, lblText));
  }
  for (let r = 0; r < rows; r++) {
    const t = view.rowLabels[r] || '';
    els.push(lbl('rl' + r, pad - 17, y(r), t));
    els.push(lbl('rr' + r, W - pad + 17, y(r), t));
  }

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const cell = view.board[r][c];
      const cx = x(c), cy = y(r);
      const k = r + '-' + c;

      if (cell.hoshi && !cell.stone)
        els.push(h('circle', { key: 'h' + k, cx, cy, r: 3, fill: COLORS.line }));

      if (cell.territory && !cell.stone && !(phase === 'playing'))
        els.push(h('rect', {
          key: 't' + k, x: cx - 4, y: cy - 4, width: 8, height: 8,
          fill: cell.territory === 'black' ? COLORS.territoryBlack : COLORS.territoryWhite,
          stroke: COLORS.line, strokeWidth: 0.6,
        }));

      if (cell.stone) {
        els.push(h('circle', {
          key: 's' + k, cx, cy, r: sr,
          fill: cell.stone === 'black' ? COLORS.black : COLORS.white,
          stroke: cell.stone === 'black' ? '#000' : '#777',
          strokeWidth: 0.8,
          opacity: cell.dead ? 0.45 : 1,
        }));
        if (cell.dead) {
          els.push(h('line', { key: 'dx1' + k, x1: cx - 5, y1: cy - 5, x2: cx + 5, y2: cy + 5, stroke: COLORS.marker, strokeWidth: 2 }));
          els.push(h('line', { key: 'dx2' + k, x1: cx - 5, y1: cy + 5, x2: cx + 5, y2: cy - 5, stroke: COLORS.marker, strokeWidth: 2 }));
        }
        if (cell.lastMove)
          els.push(h('circle', { key: 'lm' + k, cx, cy, r: 5, fill: 'none', stroke: COLORS.marker, strokeWidth: 2 }));
      }

      if (phase === 'playing' && !cell.stone && hover && hover[0] === r && hover[1] === c)
        els.push(h('circle', {
          key: 'g' + k, cx, cy, r: sr, pointerEvents: 'none',
          fill: view.toMove === 'black' ? COLORS.black : COLORS.white, opacity: 0.45,
        }));

      const clickable = (phase === 'playing' && !cell.stone) || (phase === 'scoring' && cell.stone);
      els.push(h('rect', {
        key: 'c' + k, x: cx - u / 2, y: cy - u / 2, width: u, height: u,
        fill: 'transparent', style: { cursor: clickable ? 'pointer' : 'default' },
        onClick: () => onClickPoint(r, c),
        onMouseEnter: () => setHover([r, c]),
        onMouseLeave: () => setHover(null),
      }));
    }
  }

  return h('svg', {
    viewBox: `0 0 ${W} ${H}`,
    style: { width: '100%', maxWidth: (W * 1.2) + 'px', display: 'block', userSelect: 'none' },
  }, els);
}

/* ---------------- chrome ---------------- */

function PlayerCard({ name, color, captures, active, accepted, phase }) {
  return h('div', {
    style: {
      display: 'flex', alignItems: 'center', gap: '0.5em',
      padding: '0.3em 0.6em', borderRadius: '4px',
      border: active ? `2px solid ${COLORS.marker}` : '2px solid transparent',
      background: 'rgba(128,128,128,0.12)',
    },
  },
    h('span', {
      style: {
        display: 'inline-block', width: '0.9em', height: '0.9em', borderRadius: '50%',
        background: color === 'black' ? COLORS.black : COLORS.white,
        border: '1px solid #888',
      },
    }),
    h('span', { style: { fontWeight: 'bold' } }, name),
    h('span', { style: { opacity: 0.8 } }, `captures: ${captures}`),
    (phase === 'scoring' || phase === 'finished')
      ? h('span', { title: 'agreed to the score' }, accepted ? '✓ agreed' : '· undecided') : null,
  );
}

function ScoreTable({ card, blackName, whiteName }) {
  if (!card) return null;
  const row = (label, b, w) => h('tr', { key: label },
    h('td', { style: { padding: '0.1em 0.7em', opacity: 0.8 } }, label),
    h('td', { style: { padding: '0.1em 0.7em', textAlign: 'right' } }, b),
    h('td', { style: { padding: '0.1em 0.7em', textAlign: 'right' } }, w));
  const isArea = card.method === 'area';
  return h('table', { style: { borderCollapse: 'collapse', fontSize: '0.95em', margin: '0.4em 0' } },
    h('thead', {}, h('tr', {},
      h('th', { style: { padding: '0.1em 0.7em' } }, `${card.method} scoring`),
      h('th', { style: { padding: '0.1em 0.7em', textAlign: 'right' } }, blackName),
      h('th', { style: { padding: '0.1em 0.7em', textAlign: 'right' } }, whiteName))),
    h('tbody', {},
      row('territory', card.blackTerritory, card.whiteTerritory),
      isArea ? row('stones', card.blackStones, card.whiteStones)
             : row('prisoners', card.blackPrisoners, card.whitePrisoners),
      row('komi', '—', card.komi),
      row('total', h('b', {}, card.blackScore), h('b', {}, card.whiteScore))));
}

/* ---------------- setup form ---------------- */

function labeled(label, input) {
  return h('label', { style: { display: 'flex', gap: '0.5em', alignItems: 'center', justifyContent: 'space-between' } },
    h('span', {}, label), input);
}

function SetupForm({ form, setForm, onStart, onImport, error, busy }) {
  const set = (k) => (e) => {
    const v = e.target.type === 'checkbox' ? e.target.checked : e.target.value;
    setForm((f) => ({ ...f, [k]: v }));
  };
  const applyPreset = (e) => {
    const p = e.target.value;
    setForm((f) => {
      const nf = { ...f, preset: p };
      if (PRESETS[p]) Object.assign(nf, PRESETS[p]);
      return nf;
    });
  };
  const applySize = (e) => {
    const v = e.target.value;
    setForm((f) => v === 'custom' ? { ...f, sizeChoice: v }
      : { ...f, sizeChoice: v, rows: Number(v), cols: Number(v) });
  };
  const sel = (value, onChange, opts) =>
    h('select', { value, onChange, style: { minWidth: '9em' } },
      opts.map(([v, t]) => h('option', { key: v, value: v }, t)));
  const num = (k, min, step) =>
    h('input', { type: 'number', value: form[k], min, step: step || 1, onChange: set(k), style: { width: '5em' } });
  const txt = (k) =>
    h('input', { type: 'text', value: form[k], onChange: set(k), style: { width: '9em' } });

  return h('div', { style: { display: 'flex', flexDirection: 'column', gap: '0.45em', maxWidth: '22em', padding: '0.5em 0' } },
    h('h3', { style: { margin: '0 0 0.2em 0' } }, 'New game of Go'),
    labeled('Ruleset preset', sel(form.preset, applyPreset, [
      ['japanese', 'Japanese'], ['chinese', 'Chinese'],
      ['tromp-taylor', 'Tromp–Taylor'], ['aga', 'AGA'], ['custom', 'Custom']])),
    labeled('Board size', sel(form.sizeChoice, applySize, [
      ['9', '9×9'], ['13', '13×13'], ['19', '19×19'], ['custom', 'Custom']])),
    form.sizeChoice === 'custom'
      ? h('div', { style: { display: 'flex', gap: '1em' } },
          labeled('rows', num('rows', 2)), labeled('cols', num('cols', 2)))
      : null,
    labeled('Black', txt('blackName')),
    labeled('White', txt('whiteName')),
    labeled('Handicap', num('handicap', 0)),
    labeled('Komi', num('komi', -100, 0.5)),
    h('details', {},
      h('summary', { style: { cursor: 'pointer', opacity: 0.85 } }, 'Rule toggles'),
      h('div', { style: { display: 'flex', flexDirection: 'column', gap: '0.4em', paddingTop: '0.4em' } },
        labeled('Ko rule', sel(form.ko, set('ko'), [
          ['simple', 'simple ko'], ['positional', 'positional superko'],
          ['situational', 'situational superko'], ['none', 'none']])),
        labeled('Scoring', sel(form.scoring, set('scoring'), [
          ['territory', 'territory'], ['area', 'area']])),
        labeled('Self-capture allowed',
          h('input', { type: 'checkbox', checked: form.selfCaptureAllowed, onChange: set('selfCaptureAllowed') })),
        labeled('Passes to end play', num('passesToScore', 1)))),
    h('details', {},
      h('summary', { style: { cursor: 'pointer', opacity: 0.85 } }, 'Load from SGF'),
      h('div', { style: { display: 'flex', flexDirection: 'column', gap: '0.4em', paddingTop: '0.4em' } },
        h('textarea', {
          value: form.sgfText, onChange: set('sgfText'), rows: 5,
          placeholder: '(;GM[1]FF[4]SZ[19]...;B[pd];W[dp]...)',
          style: { width: '100%', fontFamily: 'monospace', boxSizing: 'border-box' },
        }),
        h('button', { onClick: onImport, disabled: busy, style: { padding: '0.3em', cursor: 'pointer' } },
          busy ? 'Loading…' : 'Load SGF game'))),
    error ? h('div', { style: { color: COLORS.marker } }, error) : null,
    h('button', { onClick: onStart, disabled: busy, style: { padding: '0.35em', fontWeight: 'bold', cursor: 'pointer' } },
      busy ? 'Starting…' : 'Start game'));
}

/* ---------------- main component ---------------- */

export default function GoGame(props) {
  const rs = useRpcSession();
  const initialGame = (props && props.game) ? props.game : null;
  const [screen, setScreen] = React.useState(initialGame ? 'loading' : 'setup');
  const [form, setForm] = React.useState(DEFAULT_FORM);
  const [game, setGame] = React.useState(null);
  const [view, setView] = React.useState(null);
  const [setupError, setSetupError] = React.useState(null);
  const [toast, setToast] = React.useState(null);
  const [busy, setBusy] = React.useState(false);
  // Review mode: null = live game; a number = move index currently shown.
  const [review, setReview] = React.useState(null);
  const pendingReview = React.useRef(null);

  React.useEffect(() => {
    if (!toast) return;
    const t = setTimeout(() => setToast(null), 3500);
    return () => clearTimeout(t);
  }, [toast]);

  // A game handed over by `#go "file.sgf"` / `#go from …` loads on mount.
  const loadedRef = React.useRef(false);
  React.useEffect(() => {
    if (!initialGame || loadedRef.current) return;
    loadedRef.current = true;
    (async () => {
      const resp = await call(initialGame, null, null);
      if (!resp) { setScreen('setup'); return; }
      if (resp.error && !resp.view) { setSetupError(resp.error); setScreen('setup'); return; }
      const warns = (props && props.warnings) || [];
      if (warns.length) setToast(warns.join(' — '));
      await openLoaded(resp, true);
    })();
  }, []);

  async function call(g, action, reviewAt, importSgf) {
    setBusy(true);
    try {
      const resp = await rs.call('GoLean.update', {
        game: g,
        action: action || null,
        review: (reviewAt === undefined || reviewAt === null) ? null : reviewAt,
        importSgf: (importSgf === undefined || importSgf === null) ? null : importSgf,
      });
      return resp;
    } catch (e) {
      setToast(mapRpcError(e).message);
      return null;
    } finally {
      setBusy(false);
    }
  }

  /* Open a freshly created/loaded game; loaded games with moves open in
   * review mode at move 0 (the natural way to study an imported record). */
  async function openLoaded(resp, startInReview) {
    setGame(resp.game);
    if (resp.warning) setToast(resp.warning);
    const total = resp.view ? resp.view.totalMoves : 0;
    if (startInReview && total > 0) {
      const r2 = await call(resp.game, null, 0);
      if (r2 && r2.view) {
        setView(r2.view); setReview(0); setScreen('game');
        return;
      }
    }
    setView(resp.view); setReview(null); setScreen('game');
  }

  async function onStart() {
    setSetupError(null);
    const g0 = { config: formToConfig(form), actions: [] };
    const resp = await call(g0, null);
    if (!resp) return;
    if (resp.error && !resp.view) { setSetupError(resp.error); return; }
    setGame(resp.game); setView(resp.view); setScreen('game');
  }

  async function onImportSgf() {
    setSetupError(null);
    const text = (form.sgfText || '').trim();
    if (!text) { setSetupError('Paste an SGF string first.'); return; }
    const dummy = { config: formToConfig(form), actions: [] };
    const resp = await call(dummy, null, null, text);
    if (!resp) return;
    if (resp.error && !resp.view) { setSetupError(resp.error); return; }
    await openLoaded(resp, true);
  }

  async function doAction(kind, r, c, who) {
    if (!game || busy) return;
    const resp = await call(game, { kind, r: r || 0, c: c || 0, who: who || '' });
    if (!resp) return;
    if (resp.error && !resp.view) { setToast(resp.error); return; }
    setGame(resp.game); setView(resp.view);
    if (resp.error) setToast(resp.error);
  }

  function onClickPoint(r, c) {
    if (!view) return;
    if (view.phase === 'playing') doAction('play', r, c);
    else if (view.phase === 'scoring') doAction('toggleDead', r, c);
    // 'review' and 'finished': the board is read-only.
  }

  /* -------- review mode: read-only navigation through the move list -------- */

  async function doReview(k) {
    if (!game) return;
    if (busy) { pendingReview.current = k; return; }
    const resp = await call(game, null, k);
    if (!resp || !resp.view) return;
    setView(resp.view);
    setReview(resp.view.reviewMove);
    if (pendingReview.current !== null && pendingReview.current !== k) {
      const next = pendingReview.current;
      pendingReview.current = null;
      doReview(next);
    } else {
      pendingReview.current = null;
    }
  }

  function enterReview() {
    if (view) doReview(view.totalMoves);
  }

  async function exitReview() {
    if (!game) return;
    const resp = await call(game, null, null);
    if (!resp || !resp.view) return;
    setView(resp.view);
    setReview(null);
    pendingReview.current = null;
  }

  function exportRecord() {
    const text = JSON.stringify(game, null, 2);
    if (navigator.clipboard) navigator.clipboard.writeText(text);
    setToast('Game record (JSON) copied to clipboard.');
  }

  function exportSgf() {
    if (!view || !view.sgf) { setToast('No SGF available yet.'); return; }
    if (navigator.clipboard) navigator.clipboard.writeText(view.sgf);
    setToast('SGF copied to clipboard — paste into a .sgf file.');
  }

  if (screen === 'loading')
    return h('div', { style: { padding: '0.5em' } }, 'Loading game…');

  if (screen === 'setup')
    return h(SetupForm, { form, setForm, onStart, onImport: onImportSgf, error: setupError, busy });

  if (!view) return h('div', {}, 'Loading…');

  const phase = view.phase;
  const btn = (label, onClick, opts) =>
    h('button', {
      onClick, disabled: busy || (opts && opts.disabled),
      title: (opts && opts.title) || '',
      style: { padding: '0.25em 0.7em', cursor: 'pointer' },
    }, label);

  const buttons = [];
  if (phase === 'playing') {
    buttons.push(btn('Pass', () => doAction('pass')));
    buttons.push(btn('Undo', () => doAction('undo')));
    buttons.push(btn('Resign', () => doAction('resign'), { title: `${view.toMove} resigns` }));
  } else if (phase === 'scoring') {
    buttons.push(btn(`${view.blackName} accepts`, () => doAction('accept', 0, 0, 'black'),
      { disabled: view.blackAccepted }));
    buttons.push(btn(`${view.whiteName} accepts`, () => doAction('accept', 0, 0, 'white'),
      { disabled: view.whiteAccepted }));
    buttons.push(btn('Resume play', () => doAction('resume')));
  }
  if (phase !== 'review')
    buttons.push(btn('Review moves', enterReview,
      { title: 'step back and forth through the game (the game itself is untouched)', disabled: view.totalMoves === 0 }));
  buttons.push(btn('Copy SGF', exportSgf, { title: 'copy the game in Smart Game Format (paste into a .sgf file)' }));
  buttons.push(btn('Copy JSON', exportRecord, { title: 'copy the game record (config + moves) as JSON' }));
  buttons.push(btn('New game', () => {
    setScreen('setup'); setGame(null); setView(null);
    setReview(null); pendingReview.current = null;
  }));

  const k = view.reviewMove, N = view.totalMoves;
  const reviewBar = phase !== 'review' ? null :
    h('div', { style: { display: 'flex', gap: '0.4em', alignItems: 'center', flexWrap: 'wrap' } },
      btn('⏮', () => doReview(0), { disabled: k === 0, title: 'first position' }),
      btn('◀', () => doReview(Math.max(0, k - 1)), { disabled: k === 0, title: 'previous move' }),
      h('input', {
        type: 'range', min: 0, max: N, value: k,
        onChange: (e) => doReview(Number(e.target.value)),
        style: { flex: '1 1 8em', minWidth: '6em' },
      }),
      btn('▶', () => doReview(Math.min(N, k + 1)), { disabled: k === N, title: 'next move' }),
      btn('⏭', () => doReview(N), { disabled: k === N, title: 'last position' }),
      btn('Back to game', exitReview));

  const status =
    phase === 'review'
      ? h('div', {}, `Reviewing: position after move ${k} of ${N}`
          + (k < N ? ` — ${view.toMove === 'black' ? view.blackName : view.whiteName} played next.` : ' (current position).'))
      : phase === 'finished' ? null :
        phase === 'scoring'
          ? h('div', {}, 'Click a chain to mark it dead/alive; both players must accept the score.')
          : view.handicapLeft > 0
            ? h('div', {}, `${view.blackName} places ${view.handicapLeft} more handicap stone(s).`)
            : h('div', {}, `Move ${view.moveNum} — ${view.toMove === 'black' ? view.blackName : view.whiteName} to play.`
                + (view.consecPasses > 0 ? ` (${view.consecPasses}/${view.passesToScore} passes)` : ''));

  return h('div', { style: { display: 'flex', flexDirection: 'column', gap: '0.5em', maxWidth: '40em', padding: '0.3em 0', fontFamily: 'sans-serif' } },
    h('div', { style: { display: 'flex', gap: '0.6em', flexWrap: 'wrap' } },
      h(PlayerCard, { name: view.blackName, color: 'black', captures: view.blackCaptures, active: (phase === 'playing' || phase === 'review') && view.toMove === 'black', accepted: view.blackAccepted, phase }),
      h(PlayerCard, { name: view.whiteName, color: 'white', captures: view.whiteCaptures, active: (phase === 'playing' || phase === 'review') && view.toMove === 'white', accepted: view.whiteAccepted, phase })),
    phase === 'finished'
      ? h('div', { style: { fontSize: '1.25em', fontWeight: 'bold', padding: '0.2em 0' } },
          `Game over: ${view.result}` +
          (view.result && view.result.startsWith('B') ? ` — ${view.blackName} wins`
            : view.result && view.result.startsWith('W') ? ` — ${view.whiteName} wins` : ''))
      : null,
    status,
    reviewBar,
    h(Board, { view, phase, onClickPoint }),
    (phase === 'scoring' || phase === 'finished')
      ? h(ScoreTable, { card: view.scoreCard, blackName: view.blackName, whiteName: view.whiteName })
      : null,
    h('div', { style: { display: 'flex', gap: '0.5em', flexWrap: 'wrap' } }, buttons),
    h('div', { style: { opacity: 0.7, fontSize: '0.85em' } }, view.rulesSummary),
    toast ? h('div', {
      style: {
        position: 'sticky', bottom: 0, padding: '0.4em 0.8em', borderRadius: '4px',
        background: COLORS.marker, color: 'white', fontWeight: 'bold', width: 'fit-content',
      },
    }, toast) : null);
}
