/* ==========================================================================
   Storyflow — visual story planning workspace
   Vanilla JS, no dependencies. Open index.html to run.

   Architecture overview
   ---------------------
   1. Constants & metadata       5. Core operations (create / update / link / delete)
   2. State & data model         6. Rendering (dashboard, panels, views, inspector)
   3. Persistence (localStorage) 7. Canvas, timeline & resizer interactions
   4. History (undo / redo)      8. Modals, toasts, actions, shortcuts, init

   Data model (one project object, one source of truth)
   ----------------------------------------------------
   project = {
     id, title, description, createdAt, updatedAt, view,
     ideas[], characters[], events[], locations[], notes[],   // story elements
     storylines[], sections[],                                // story structure
     relationships[]  { id, a, b, label }                     // links between ANY two elements
     positions { board:{id:{x,y}}, graph:{id:{x,y}} }         // per-view canvas positions
   }
   An element exists exactly once. Views only *project* it: the Idea Board shows
   every element that has a board position, the Connections view shows every
   element, the Timeline shows events in array order. Editing anywhere re-renders
   everywhere. Relationships are stored once and reused by all views, so a "related
   character" on an event is simply a link between the two elements.
   ========================================================================== */
'use strict';

/* ==========================================================================
   1. Constants & metadata
   ========================================================================== */
const STORAGE_KEY = 'storyflow.v1';
const SCHEMA_VERSION = 1;
const HISTORY_LIMIT = 80;
const CANVAS_W = 3600;
const CANVAS_H = 2400;
const GRID = 24;
const CARD_W = 224;

/** Element kinds. `list` is the project array that stores them. */
const KINDS = {
  idea:      { label: 'Idea',      plural: 'Ideas',      icon: 'idea', list: 'ideas',      color: '#B98AFF', hint: 'Capture an idea…' },
  character: { label: 'Character', plural: 'Characters', icon: 'user', list: 'characters', color: '#7DB4FF', hint: 'Add a character…' },
  event:     { label: 'Event',     plural: 'Events',     icon: 'event', list: 'events',    color: '#F0B968', hint: 'Add an event…' },
  location:  { label: 'Location',  plural: 'Locations',  icon: 'pin',  list: 'locations',  color: '#5FD1C0', hint: 'Add a location…' },
  note:      { label: 'Note',      plural: 'Notes',      icon: 'note', list: 'notes',      color: '#9A9AAE', hint: 'Jot down a note…' },
};
const KIND_ORDER = Object.keys(KINDS);
const PALETTE = ['#B98AFF', '#7DB4FF', '#5FD1C0', '#8FD18A', '#F0B968', '#F08FA8', '#9A9AAE'];
const VIEWS = ['board', 'timeline', 'graph'];
const GRAPH_COLUMNS = { character: 80, event: 360, idea: 640, location: 920, note: 1200 };

const DEFAULT_PREFS = {
  sidebarWidth: 300,        // px
  structFraction: 0.38,     // share of the sidebar used by the Structure panel
  sidebarCollapsed: false,
  maximized: false,
  snapToGrid: false,
};

/* ==========================================================================
   2. State & helpers
   ========================================================================== */
const $ = (sel, root = document) => root.querySelector(sel);
const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));
const clamp = (n, lo, hi) => Math.min(hi, Math.max(lo, n));
const now = () => Date.now();
const uid = prefix => `${prefix}_${Date.now().toString(36)}${Math.random().toString(36).slice(2, 7)}`;
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const icon = (name, cls = '') => `<svg class="ic ${cls}" aria-hidden="true"><use href="#i-${name}"/></svg>`;
const str = (v, fallback = '') => (typeof v === 'string' ? v : fallback);
const num = (v, fallback = 0) => (typeof v === 'number' && Number.isFinite(v) ? v : fallback);
const isMobile = () => window.matchMedia('(max-width: 860px)').matches;

/** Persisted data: all projects plus layout preferences. */
const store = { projects: [], prefs: { ...DEFAULT_PREFS } };

/** The project currently open (a reference into store.projects), or null on the dashboard. */
let project = null;
/** id -> { kind, obj } lookup, rebuilt whenever data changes. */
let entityIndex = new Map();

/** Non-persisted UI state. */
const ui = {
  selection: null,            // { type:'entity'|'rel', id }
  search: '',
  filter: null,               // { type:'storyline'|'section', id }
  elementsTab: 'idea',
  connectFrom: null,          // id of the element currently being linked
  editingStruct: null,        // id of the structure item being renamed inline
  popover: null,              // 'add' | 'layout' | null
  addKind: 'idea',
  graphKinds: new Set(KIND_ORDER),
  drawerOpen: false,
  renderedView: null,         // which view shell is currently mounted
  scroll: { board: { left: 0, top: 0 }, graph: { left: 0, top: 0 }, timeline: { left: 0, top: 0 } },
  dragEventId: null,
  dropTarget: null,
  flashId: null,
  clip: null,                 // { kind, obj } copied with Ctrl+C
};

/* ---------- Small data helpers ---------- */
function reindex() {
  entityIndex = new Map();
  if (!project) return;
  for (const kind of KIND_ORDER) for (const obj of project[KINDS[kind].list]) entityIndex.set(obj.id, { kind, obj });
}
const getEntity = id => entityIndex.get(id) || null;
const entityName = (kind, e) => e.title || `Untitled ${KINDS[kind].label.toLowerCase()}`;
const entityColor = (kind, e) => e.color || KINDS[kind].color;
const linksOf = id => project.relationships.filter(r => r.a === id || r.b === id);
const relatedEntities = id => linksOf(id)
  .map(rel => ({ rel, ...(getEntity(rel.a === id ? rel.b : rel.a) || {}) }))
  .filter(x => x.obj);
const storylineById = id => project.storylines.find(s => s.id === id) || null;
const sectionById = id => project.sections.find(s => s.id === id) || null;
const isSelected = id => ui.selection?.type === 'entity' && ui.selection.id === id;

/** Does an element match the current search text? */
function matchesSearch(e) {
  const q = ui.search.trim().toLowerCase();
  if (!q) return true;
  return [e.title, e.description, e.role, e.notes, e.date].some(v => str(v).toLowerCase().includes(q));
}
/** Events can be filtered by the storyline / chapter picked in the Structure panel. */
function eventMatchesFilter(ev) {
  if (!ui.filter) return true;
  return ui.filter.type === 'storyline' ? ev.storylineId === ui.filter.id : ev.sectionId === ui.filter.id;
}
/** Dimmed = visible but de-emphasised (search miss, or event outside the active filter). */
function isDimmed(kind, e) {
  if (!matchesSearch(e)) return true;
  return kind === 'event' && !eventMatchesFilter(e);
}

/** Parse an event "date" into a sortable number, or null when it is free-form text.
 *  Accepts plain sequence numbers ("3") and ISO-style dates ("2024-05-01"). */
function parseEventDate(text) {
  const s = str(text).trim();
  if (!s) return null;
  if (/^-?\d+(\.\d+)?$/.test(s)) return Number(s);
  if (/^\d{4}(-\d{1,2}(-\d{1,2})?)?$/.test(s)) {
    const t = Date.parse(s.length === 4 ? `${s}-01-01` : s);
    return Number.isFinite(t) ? t : null;
  }
  return null;
}

function formatRelative(ts) {
  const diff = now() - ts;
  const min = 60e3, hour = 60 * min, day = 24 * hour;
  if (diff < min) return 'just now';
  if (diff < hour) return `${Math.floor(diff / min)} min ago`;
  if (diff < day) return `${Math.floor(diff / hour)} h ago`;
  if (diff < 7 * day) return `${Math.floor(diff / day)} d ago`;
  return new Date(ts).toLocaleDateString(undefined, { year: 'numeric', month: 'short', day: 'numeric' });
}
const initials = s => (str(s).trim().split(/\s+/).map(w => w[0]).join('').slice(0, 2) || '?').toUpperCase();
const slug = s => str(s, 'story').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '') || 'story';

/* ==========================================================================
   3. Persistence (localStorage) — defensive: bad data must never crash the app
   ========================================================================== */
let saveTimer = null;
const removedIds = new Set();          // projects deleted in this tab (so a merge never resurrects them)

/** Pull in stories written by another tab so saving here never overwrites them. */
function mergeExternal() {
  let raw = null;
  try { raw = localStorage.getItem(STORAGE_KEY); } catch (e) { return; }
  if (!raw) return;
  try {
    const stored = JSON.parse(raw);
    for (const sp of Array.isArray(stored.projects) ? stored.projects : []) {
      if (!sp || typeof sp.id !== 'string' || removedIds.has(sp.id)) continue;
      const i = store.projects.findIndex(p => p.id === sp.id);
      if (i < 0) { const n = normalizeProject(sp); if (n) store.projects.push(n); }
      else if (store.projects[i] !== project && num(sp.updatedAt) > store.projects[i].updatedAt) { const n = normalizeProject(sp); if (n) store.projects[i] = n; }
    }
  } catch (e) { /* unreadable: ignore, our copy is still written below */ }
}

/** Validate & repair a project loaded from storage (or created programmatically). */
function normalizeProject(raw) {
  if (!raw || typeof raw !== 'object' || typeof raw.id !== 'string' || !raw.id) return null;
  const t = now();
  const seen = new Set();                                  // ids are unique across the whole project
  const list = v => (Array.isArray(v) ? v : []).filter(x => x && typeof x === 'object' && typeof x.id === 'string' && x.id && !seen.has(x.id) && seen.add(x.id));
  const color = c => (typeof c === 'string' && /^#[0-9a-f]{6}$/i.test(c) ? c : null);
  const base = x => ({ id: x.id, title: str(x.title), description: str(x.description), color: color(x.color), createdAt: num(x.createdAt, t), updatedAt: num(x.updatedAt, t) });

  const p = {
    id: raw.id,
    title: str(raw.title, 'Untitled story'),
    description: str(raw.description),
    createdAt: num(raw.createdAt, t),
    updatedAt: num(raw.updatedAt, t),
    view: VIEWS.includes(raw.view) ? raw.view : 'board',
    storylines: list(raw.storylines).map(x => ({ id: x.id, name: str(x.name, 'Storyline'), color: color(x.color) || PALETTE[0] })),
    sections: list(raw.sections).map(x => ({ id: x.id, name: str(x.name, 'Chapter') })),
    ideas: list(raw.ideas).map(base),
    characters: list(raw.characters).map(x => ({ ...base(x), role: str(x.role), notes: str(x.notes) })),
    events: list(raw.events).map(x => ({ ...base(x), date: str(x.date), storylineId: x.storylineId || null, sectionId: x.sectionId || null })),
    locations: list(raw.locations).map(base),
    notes: list(raw.notes).map(base),
    relationships: [],
    positions: { board: {}, graph: {} },
  };
  // Drop dangling structure references on events
  for (const ev of p.events) {
    if (!p.storylines.some(s => s.id === ev.storylineId)) ev.storylineId = null;
    if (!p.sections.some(s => s.id === ev.sectionId)) ev.sectionId = null;
  }
  // Relationships: both ends must exist, no self-links, no duplicates (in either direction)
  const ids = new Set(KIND_ORDER.flatMap(k => p[KINDS[k].list].map(e => e.id)));
  const pairs = new Set();
  for (const r of Array.isArray(raw.relationships) ? raw.relationships : []) {
    if (!r || typeof r.a !== 'string' || typeof r.b !== 'string' || r.a === r.b || !ids.has(r.a) || !ids.has(r.b)) continue;
    const key = [r.a, r.b].sort().join('|');
    if (pairs.has(key)) continue;
    pairs.add(key);
    p.relationships.push({ id: typeof r.id === 'string' && r.id ? r.id : uid('rel'), a: r.a, b: r.b, label: str(r.label) });
  }
  // Positions
  for (const mode of ['board', 'graph']) {
    const src = raw.positions && typeof raw.positions[mode] === 'object' && raw.positions[mode] ? raw.positions[mode] : {};
    for (const [id, pos] of Object.entries(src)) {
      if (ids.has(id) && pos && Number.isFinite(pos.x) && Number.isFinite(pos.y)) p.positions[mode][id] = { x: pos.x, y: pos.y };
    }
  }
  return p;
}

function sanitizePrefs(raw) {
  const out = { ...DEFAULT_PREFS };
  if (!raw || typeof raw !== 'object') return out;
  out.sidebarWidth = clamp(num(raw.sidebarWidth, out.sidebarWidth), 220, 560);
  out.structFraction = clamp(num(raw.structFraction, out.structFraction), 0.15, 0.7);
  out.sidebarCollapsed = raw.sidebarCollapsed === true;
  out.maximized = raw.maximized === true;
  out.snapToGrid = raw.snapToGrid === true;
  return out;
}

function loadStore() {
  let raw = null;
  try { raw = localStorage.getItem(STORAGE_KEY); } catch (e) { /* storage unavailable */ }
  if (!raw) return;
  try {
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') throw new Error('bad shape');
    store.prefs = sanitizePrefs(parsed.prefs);
    store.projects = (Array.isArray(parsed.projects) ? parsed.projects : []).map(normalizeProject).filter(Boolean);
  } catch (e) {
    // Keep a copy of the unreadable data so nothing is silently lost, then start clean.
    try { localStorage.setItem(`${STORAGE_KEY}.corrupt`, raw); } catch (_) { /* ignore */ }
    store.projects = [];
    store.prefs = { ...DEFAULT_PREFS };
  }
}

function setSaveStatus(state) {
  const el = $('#save-status');
  if (!el) return;
  el.dataset.state = state;
  el.lastElementChild.textContent = { saved: 'Saved', saving: 'Saving…', error: 'Not saved' }[state];
}
/** Debounced save: shows "Saving…" immediately, writes shortly after the last change. */
function scheduleSave() {
  setSaveStatus('saving');
  clearTimeout(saveTimer);
  saveTimer = setTimeout(flushSave, 350);
}
function flushSave() {
  clearTimeout(saveTimer);
  saveTimer = null;
  mergeExternal();
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify({ version: SCHEMA_VERSION, projects: store.projects, prefs: store.prefs }));
    setSaveStatus('saved');
    return true;
  } catch (e) {
    setSaveStatus('error');
    toast('Could not save — browser storage may be full or disabled.');
    return false;
  }
}

/* ==========================================================================
   4. History (undo / redo) — snapshot based, coalescing rapid typing
   ========================================================================== */
const hist = { undo: [], redo: [], lastKey: null, lastTime: 0 };

/** Apply a change to the open project. Records an undo snapshot first. */
function mutate(fn, { coalesce = null } = {}) {
  const t = now();
  const merge = coalesce && coalesce === hist.lastKey && t - hist.lastTime < 1200;
  if (!merge) {
    hist.undo.push(JSON.stringify(project));
    if (hist.undo.length > HISTORY_LIMIT) hist.undo.shift();
    hist.redo.length = 0;
  }
  hist.lastKey = coalesce;
  hist.lastTime = t;
  fn(project);
  project.updatedAt = t;
  afterDataChange();
  scheduleSave();
}
/** mutate + re-render. `skip` lists render regions to leave alone (e.g. the inspector while typing in it). */
function act(fn, opts = {}) {
  mutate(fn, opts);
  renderAll(opts.skip || []);
}
function afterDataChange() {
  reindex();
  const sel = ui.selection;
  if (sel && sel.type === 'entity' && !entityIndex.has(sel.id)) ui.selection = null;
  if (sel && sel.type === 'rel' && !project.relationships.some(r => r.id === sel.id)) ui.selection = null;
  if (ui.connectFrom && !entityIndex.has(ui.connectFrom)) ui.connectFrom = null;
  if (ui.filter) {
    const pool = ui.filter.type === 'storyline' ? project.storylines : project.sections;
    if (!pool.some(x => x.id === ui.filter.id)) ui.filter = null;
  }
}
function restoreSnapshot(json) {
  const restored = normalizeProject(JSON.parse(json));
  if (!restored) return;
  restored.view = project.view;                       // undo should never switch the current view
  const i = store.projects.findIndex(p => p.id === restored.id);
  store.projects[i] = restored;
  project = restored;
  hist.lastKey = null;
  afterDataChange();
  scheduleSave();
  $('#story-title').value = project.title;
  renderAll();
}
function undo() {
  if (!hist.undo.length) return;
  hist.redo.push(JSON.stringify(project));
  restoreSnapshot(hist.undo.pop());
}
function redo() {
  if (!hist.redo.length) return;
  hist.undo.push(JSON.stringify(project));
  restoreSnapshot(hist.redo.pop());
}

/* ==========================================================================
   5. Core operations
   ========================================================================== */

/* ---------- Projects ---------- */
function createProject(title) {
  const t = now();
  const p = normalizeProject({ id: uid('proj'), title: title.trim() || 'Untitled story', createdAt: t, updatedAt: t, view: 'board' });
  store.projects.unshift(p);
  flushSave();
  return p;
}

function openProject(id) {
  const p = store.projects.find(x => x.id === id);
  if (!p) return;
  project = p;
  reindex();
  hist.undo = []; hist.redo = []; hist.lastKey = null;
  Object.assign(ui, {
    selection: null, search: '', filter: null, connectFrom: null, editingStruct: null, popover: null,
    drawerOpen: false, elementsTab: 'idea', renderedView: null, addKind: 'idea', flashId: null,
    scroll: { board: { left: 0, top: 0 }, graph: { left: 0, top: 0 }, timeline: { left: 0, top: 0 } },
  });
  ui.graphKinds = new Set(KIND_ORDER);
  $('#dashboard').hidden = true;
  $('#workspace').hidden = false;
  $('#story-title').value = p.title;
  $('#search').value = '';
  $('#view-root').innerHTML = '';
  closePopovers();
  try { location.hash = `story=${encodeURIComponent(p.id)}`; } catch (e) { /* ignore */ }
  applyLayout();
  renderAll();
}

function closeProject() {
  flushSave();
  project = null;
  entityIndex = new Map();
  $('#workspace').hidden = true;
  $('#dashboard').hidden = false;
  try { location.hash = ''; } catch (e) { /* ignore */ }
  renderDashboard();
}

/* ---------- Elements ---------- */
/** Find a free spot on the Idea Board near the visible area, so new cards never stack exactly. */
function findFreeBoardSpot() {
  const sc = currentScroll('board');
  const sx = sc.left + 60, sy = sc.top + 60;
  const taken = Object.values(project.positions.board);
  const collides = (x, y) => taken.some(p => Math.abs(p.x - x) < 200 && Math.abs(p.y - y) < 120);
  let x = sx, y = sy;
  for (let i = 0; i < 400; i++) {
    if (!collides(x, y)) break;
    x += 36; y += 36;
    if (i % 10 === 9) { x = sx + (i / 10 + 1) * 250; y = sy; }
  }
  return { x: clamp(x, 0, CANVAS_W - CARD_W), y: clamp(y, 0, CANVAS_H - 160) };
}
/** Connections view: elements are laid out in one column per kind until the user moves them. */
function nextGraphSpot(kind) {
  const x = GRAPH_COLUMNS[kind];
  const taken = Object.values(project.positions.graph);
  let y = 80;
  while (taken.some(p => Math.abs(p.x - x) < 160 && Math.abs(p.y - y) < 60) && y < CANVAS_H - 120) y += 72;
  return { x, y };
}
/** Ensure every element has a Connections position (silent: not an undoable user action). */
function ensureGraphPositions() {
  let changed = false;
  for (const kind of KIND_ORDER) {
    for (const e of project[KINDS[kind].list]) {
      if (!project.positions.graph[e.id]) { project.positions.graph[e.id] = nextGraphSpot(kind); changed = true; }
    }
  }
  if (changed) scheduleSave();
}

function createEntity(kind, { title = '', description = '', select = true, focus = false, pos = null, graphPos = null, insertAt = null } = {}) {
  const t = now();
  const id = uid(kind);
  const obj = { id, title, description, color: null, createdAt: t, updatedAt: t };
  if (kind === 'character') { obj.role = ''; obj.notes = ''; }
  if (kind === 'event') {
    obj.date = '';
    obj.storylineId = ui.filter?.type === 'storyline' ? ui.filter.id : null;   // new events join the active filter
    obj.sectionId = ui.filter?.type === 'section' ? ui.filter.id : null;
  }
  const onBoard = pos || kind === 'idea' || project.view === 'board';
  if (select) ui.selection = { type: 'entity', id };
  if (project.view === 'graph') ui.graphKinds.add(kind);   // never create something the view is hiding
  act(p => {
    const arr = p[KINDS[kind].list];
    if (insertAt == null) arr.push(obj); else arr.splice(insertAt, 0, obj);
    if (onBoard) p.positions.board[id] = pos || findFreeBoardSpot();
    if (graphPos) p.positions.graph[id] = graphPos;
  });
  if (focus) focusInspectorTitle();
  if (select && project.view !== 'board') requestAnimationFrame(revealSelection);
  return id;
}

function setField(id, field, value, opts = {}) {
  act(p => {
    const found = KIND_ORDER.map(k => p[KINDS[k].list].find(e => e.id === id)).find(Boolean);
    if (found) { found[field] = value; found.updatedAt = now(); }
  }, { coalesce: `${id}.${field}`, ...opts });
}

/** Turn one kind of element into another, keeping its id-links and positions. */
function convertKind(id, newKind) {
  const found = getEntity(id);
  if (!found || found.kind === newKind) return;
  const old = found.obj;
  const newId = uid(newKind);
  const next = { id: newId, title: old.title, description: old.description, color: old.color, createdAt: old.createdAt, updatedAt: now() };
  if (newKind === 'character') { next.role = str(old.role); next.notes = str(old.notes); }
  if (newKind === 'event') { next.date = str(old.date); next.storylineId = old.storylineId || null; next.sectionId = old.sectionId || null; }
  ui.selection = { type: 'entity', id: newId };
  if (ui.connectFrom === id) ui.connectFrom = newId;
  act(p => {
    const oldArr = p[KINDS[found.kind].list];
    const idx = oldArr.findIndex(e => e.id === id);
    if (idx >= 0) oldArr.splice(idx, 1);
    p[KINDS[newKind].list].push(next);
    for (const r of p.relationships) { if (r.a === id) r.a = newId; if (r.b === id) r.b = newId; }
    for (const mode of ['board', 'graph']) {
      if (p.positions[mode][id]) { p.positions[mode][newId] = p.positions[mode][id]; delete p.positions[mode][id]; }
    }
  });
  toast(`Converted to ${KINDS[newKind].label.toLowerCase()}`);
}

async function deleteEntity(id) {
  const found = getEntity(id);
  if (!found) return;
  const name = entityName(found.kind, found.obj);
  act(p => {
    const arr = p[KINDS[found.kind].list];
    arr.splice(arr.findIndex(e => e.id === id), 1);
    p.relationships = p.relationships.filter(r => r.a !== id && r.b !== id);
    delete p.positions.board[id];
    delete p.positions.graph[id];
  });
  toast(`Deleted “${name}”`, { label: 'Undo', fn: undo });
}

/* ---------- Duplicate, copy / paste, nudge ---------- */
function insertCopy(kind, src, { at = null, board = null, graph = null } = {}) {
  const copy = JSON.parse(JSON.stringify(src));
  copy.id = uid(kind); copy.createdAt = copy.updatedAt = now();
  ui.selection = { type: 'entity', id: copy.id };
  act(p => {
    const arr = p[KINDS[kind].list];
    if (at == null) arr.push(copy); else arr.splice(at, 0, copy);
    if (board) p.positions.board[copy.id] = board;
    if (graph) p.positions.graph[copy.id] = graph;
  });
  return copy.id;
}
/** Duplicate an element (connections are not copied). `pos` places the copy in the given canvas mode. */
function duplicateEntity(id, { mode = null, pos = null } = {}) {
  const found = getEntity(id);
  if (!found) return null;
  const off = p => (p ? { x: clamp(p.x + 32, 0, CANVAS_W - CARD_W), y: clamp(p.y + 32, 0, CANVAS_H - 160) } : null);
  const b = project.positions.board[id], g = project.positions.graph[id];
  const copyId = insertCopy(found.kind, found.obj, {
    at: project[KINDS[found.kind].list].findIndex(e => e.id === id) + 1,
    board: mode === 'board' && pos ? pos : off(b),
    graph: mode === 'graph' && pos ? pos : off(g),
  });
  toast(`${KINDS[found.kind].label} duplicated`, { label: 'Undo', fn: undo, duration: 2400 });
  return copyId;
}
function copySelected() {
  const found = ui.selection?.type === 'entity' ? getEntity(ui.selection.id) : null;
  if (!found) return false;
  ui.clip = { kind: found.kind, obj: JSON.parse(JSON.stringify(found.obj)) };
  toast(`${KINDS[found.kind].label} copied`, { duration: 1500 });
  return true;
}
function pasteClip() {
  if (!ui.clip) return false;
  const { kind, obj } = ui.clip;
  const onBoard = kind === 'idea' || project.view === 'board';
  insertCopy(kind, obj, { board: onBoard ? findFreeBoardSpot() : null });
  toast(`${KINDS[kind].label} pasted`, { duration: 1500 });
  return true;
}
/** Arrow keys move the selected card; returns false when there is nothing to move. */
function nudgeSelected(dx, dy) {
  const sel = ui.selection;
  if (sel?.type !== 'entity' || project.view === 'timeline') return false;
  const mode = project.view, pos = project.positions[mode][sel.id];
  if (!pos) return false;
  act(p => { p.positions[mode][sel.id] = { x: clamp(pos.x + dx, 0, CANVAS_W - CARD_W), y: clamp(pos.y + dy, 0, CANVAS_H - 60) }; },
    { coalesce: `nudge-${sel.id}`, skip: ['inspector', 'sidebar'] });
  return true;
}

/* ---------- Relationships ---------- */
function addLink(a, b) {
  if (!a || !b || a === b || !entityIndex.has(a) || !entityIndex.has(b)) return false;
  if (project.relationships.some(r => (r.a === a && r.b === b) || (r.a === b && r.b === a))) {
    toast('Those two are already connected');
    return false;
  }
  act(p => { p.relationships.push({ id: uid('rel'), a, b, label: '' }); });
  const A = getEntity(a), B = getEntity(b);
  toast(`Connected “${entityName(A.kind, A.obj)}” and “${entityName(B.kind, B.obj)}”`);
  return true;
}
function removeLink(relId) {
  act(p => { p.relationships = p.relationships.filter(r => r.id !== relId); });
  toast('Connection removed', { label: 'Undo', fn: undo });
}

/* ---------- Structure (storylines & chapters) ---------- */
function addStructItem(type) {
  const isStory = type === 'storyline';
  const arr = isStory ? project.storylines : project.sections;
  const item = { id: uid(type), name: `${isStory ? 'Storyline' : 'Chapter'} ${arr.length + 1}` };
  if (isStory) item.color = PALETTE[arr.length % PALETTE.length];
  ui.editingStruct = item.id;
  act(p => { (isStory ? p.storylines : p.sections).push(item); });
}
function findStructItem(id) { return project.storylines.find(x => x.id === id) || project.sections.find(x => x.id === id) || null; }
function commitStructEdit(input) {
  const id = ui.editingStruct;
  if (!id) return;
  ui.editingStruct = null;
  const name = input.value.trim();
  if (input.dataset.cancel || !name) { renderStructure(); return; }
  act(p => { const it = p.storylines.find(x => x.id === id) || p.sections.find(x => x.id === id); if (it) it.name = name; });
}
async function deleteStructItem(id) {
  const item = findStructItem(id);
  if (!item) return;
  const isStory = project.storylines.some(x => x.id === id);
  const used = project.events.filter(e => (isStory ? e.storylineId : e.sectionId) === id).length;
  act(p => {
    if (isStory) { p.storylines = p.storylines.filter(x => x.id !== id); p.events.forEach(e => { if (e.storylineId === id) e.storylineId = null; }); }
    else { p.sections = p.sections.filter(x => x.id !== id); p.events.forEach(e => { if (e.sectionId === id) e.sectionId = null; }); }
  });
  toast(`Deleted “${item.name}”${used ? ` — ${used} event${used > 1 ? 's' : ''} kept` : ''}`, { label: 'Undo', fn: undo });
}

/* ---------- Timeline ordering ---------- */
function moveEventTo(id, targetId, after) {
  if (id === targetId) return;
  act(p => {
    const from = p.events.findIndex(e => e.id === id);
    if (from < 0) return;
    const [ev] = p.events.splice(from, 1);
    let to = p.events.findIndex(e => e.id === targetId);
    if (to < 0) { p.events.splice(from, 0, ev); return; }
    if (after) to++;
    p.events.splice(to, 0, ev);
  });
  ui.flashId = id; renderView();
}
/** Move one step up/down relative to the next *visible* event (respects the active filter). */
function moveEventStep(id, dir) {
  const arr = project.events;
  const i = arr.findIndex(e => e.id === id);
  let j = i + dir;
  while (j >= 0 && j < arr.length && !eventMatchesFilter(arr[j])) j += dir;
  if (i < 0 || j < 0 || j >= arr.length) return;
  act(p => { const [ev] = p.events.splice(i, 1); p.events.splice(j, 0, ev); });
  ui.flashId = id; renderView();
}
/** Sort dated events chronologically, leaving undated events exactly where they are. */
function sortEventsByDate() {
  const slots = [];
  project.events.forEach((e, i) => { if (parseEventDate(e.date) !== null) slots.push(i); });
  if (slots.length < 2) { toast('Add dates (like 2024-05-01 or 3) to sort events'); return; }
  act(p => {
    const dated = slots.map(i => p.events[i]).sort((x, y) => parseEventDate(x.date) - parseEventDate(y.date));
    slots.forEach((slot, n) => { p.events[slot] = dated[n]; });
  });
  toast('Events sorted by date', { label: 'Undo', fn: undo });
}

/* ---------- Selection ---------- */
function select(sel, { reveal = false } = {}) {
  ui.selection = sel ? (typeof sel === 'string' ? { type: 'entity', id: sel } : sel) : null;
  renderInspector();
  applySelectionClasses();
  if (reveal) revealSelection();
}
function applySelectionClasses() {
  const id = ui.selection?.type === 'entity' ? ui.selection.id : null;
  $$('.node, .row, .tl-item').forEach(n => n.classList.toggle('selected', !!id && n.dataset.id === id));
  $$('.node').forEach(n => n.setAttribute('aria-pressed', String(!!id && n.dataset.id === id)));
  drawLinks();
}
function revealSelection() {
  const id = ui.selection?.type === 'entity' ? ui.selection.id : null;
  if (!id) return;
  const el = $(`#view-root .node[data-id="${id}"]`) || $(`#view-root .tl-item[data-id="${id}"]`);
  if (el) el.scrollIntoView({ block: 'center', inline: 'center', behavior: 'smooth' });
}
function focusInspectorTitle() {
  requestAnimationFrame(() => { const i = $('#inspector [data-field="title"]'); if (i) { i.focus(); i.select(); } });
}

/* ==========================================================================
   6. Rendering
   ========================================================================== */
function renderAll(skip = []) {
  if (!project) return;
  renderHeader();
  if (!skip.includes('sidebar')) { renderStructure(); renderElements(); }
  renderViewbar();
  if (!skip.includes('view')) renderView();
  if (!skip.includes('inspector')) renderInspector();
}

/* ---------- Dashboard ---------- */
function renderDashboard() {
  const grid = $('#project-grid');
  const projects = [...store.projects].sort((a, b) => b.updatedAt - a.updatedAt);
  if (!projects.length) {
    grid.innerHTML = `<div class="empty-hero">
      ${icon('logo', 'logo')}
      <h2>Start your first story</h2>
      <p>Collect scattered ideas on a board, turn them into events and characters, then connect everything into a story — all in one calm workspace.</p>
      <div class="hero-actions">
        <button class="btn primary lg" data-action="new-story">${icon('plus')}New Story</button>
        <button class="btn ghost lg" data-action="load-sample">Explore a sample story</button>
      </div></div>`;
    return;
  }
  grid.innerHTML = projects.map(p => {
    const counts = [['idea', p.ideas.length], ['character', p.characters.length], ['event', p.events.length]]
      .filter(([, n]) => n).map(([k, n]) => `<span class="chip">${n} ${(n === 1 ? KINDS[k].label : KINDS[k].plural).toLowerCase()}</span>`).join('');
    return `<article class="project-card" data-action="open-project" data-id="${p.id}" tabindex="0" aria-label="Open ${esc(p.title || 'Untitled story')}">
      <div class="pc-top">
        <h3>${esc(p.title || 'Untitled story')}</h3>
        <div class="pc-actions">
          <button class="icon-btn xs" data-action="rename-project" data-id="${p.id}" title="Rename" aria-label="Rename story">${icon('edit')}</button>
          <button class="icon-btn xs" data-action="delete-project" data-id="${p.id}" title="Delete" aria-label="Delete story">${icon('trash')}</button>
        </div>
      </div>
      <p class="pc-desc${p.description ? '' : ' none'}">${esc(p.description || 'No description yet')}</p>
      <div class="pc-stats">${counts || '<span class="chip">Empty</span>'}</div>
      <div class="pc-foot" title="${esc(new Date(p.updatedAt).toLocaleString())}">Edited ${formatRelative(p.updatedAt)}</div>
    </article>`;
  }).join('') + `<button class="project-card new-tile" data-action="new-story">${icon('plus')}<span>New Story</span></button>`;
}

/* ---------- Header ---------- */
function renderHeader() {
  const title = $('#story-title');
  if (document.activeElement !== title) title.value = project.title;
  $('#btn-undo').disabled = !hist.undo.length;
  $('#btn-redo').disabled = !hist.redo.length;
  $('#lbl-snap').textContent = `Snap cards to grid: ${store.prefs.snapToGrid ? 'On' : 'Off'}`;
  renderKindPicker();
}
function renderKindPicker() {
  $('#kind-picker').innerHTML = KIND_ORDER.map(k =>
    `<button type="button" class="chip toggle${ui.addKind === k ? ' on' : ''}" data-action="set-add-kind" data-kind="${k}" style="--c:${KINDS[k].color}">${icon(KINDS[k].icon)}${KINDS[k].label}</button>`).join('');
  $('#quick-input').placeholder = `${KINDS[ui.addKind].hint.replace('…', '')} and press Enter`;
}

/* ---------- View bar ---------- */
function renderViewbar() {
  $$('#view-tabs button').forEach(b => b.setAttribute('aria-selected', String(b.dataset.view === project.view)));
  let chip = '';
  if (ui.filter) {
    const item = ui.filter.type === 'storyline' ? storylineById(ui.filter.id) : sectionById(ui.filter.id);
    if (item) chip = `<span class="chip filter">${icon(ui.filter.type === 'storyline' ? 'event' : 'bookmark')}Showing: ${esc(item.name)}<button data-action="clear-filter" title="Clear filter" aria-label="Clear filter">${icon('close')}</button></span>`;
  }
  $('#filter-chip').innerHTML = chip;
}

/* ---------- Structure panel ---------- */
function renderStructure() {
  const group = (title, type, items, emptyText) => {
    const rows = items.map(it => {
      const active = ui.filter && ui.filter.type === type && ui.filter.id === it.id;
      const n = project.events.filter(e => (type === 'storyline' ? e.storylineId : e.sectionId) === it.id).length;
      const lead = type === 'storyline'
        ? `<button class="s-dot" style="--c:${it.color}" data-action="cycle-color" data-id="${it.id}" title="Change color" aria-label="Change color"></button>`
        : `<span class="s-ico">${icon('bookmark')}</span>`;
      const name = ui.editingStruct === it.id
        ? `<input class="s-edit" type="text" maxlength="80" value="${esc(it.name)}" data-id="${it.id}" aria-label="Name">`
        : `<button class="s-name" data-action="toggle-filter" data-type="${type}" data-id="${it.id}" title="Click to filter · double-click to rename">${esc(it.name)}</button>`;
      return `<li class="s-row${active ? ' active' : ''}">${lead}${name}<span class="s-count" title="Events">${n}</span>
        <span class="s-actions"><button class="icon-btn xs" data-action="rename-struct" data-id="${it.id}" title="Rename" aria-label="Rename">${icon('edit')}</button><button class="icon-btn xs" data-action="delete-struct" data-id="${it.id}" title="Delete" aria-label="Delete">${icon('trash')}</button></span></li>`;
    }).join('');
    return `<div class="s-group"><div class="s-group-head"><span>${title}</span>
      <button class="icon-btn xs" data-action="add-struct" data-type="${type}" title="Add ${type === 'storyline' ? 'storyline' : 'chapter'}" aria-label="Add ${type}">${icon('plus')}</button></div>
      ${rows ? `<ul>${rows}</ul>` : `<div class="mini-hint">${emptyText}</div>`}</div>`;
  };
  $('#struct-lists').innerHTML =
    group('Storylines', 'storyline', project.storylines, 'Optional — group events into parallel plots.') +
    group('Chapters &amp; groups', 'section', project.sections, 'Optional — sections of your story.');
  const input = $('.s-edit');
  if (input) { input.focus(); input.select(); }
}

/* ---------- Story elements panel ---------- */
function renderElements() {
  $('#el-tabs').innerHTML = KIND_ORDER.map(k => {
    const m = KINDS[k];
    return `<button class="tab${ui.elementsTab === k ? ' active' : ''}" role="tab" aria-selected="${ui.elementsTab === k}" data-action="set-tab" data-kind="${k}" title="${m.plural}">
      ${icon(m.icon)}<span class="tab-label">${m.plural}</span><span class="tab-count">${project[m.list].length}</span></button>`;
  }).join('');
  const kind = ui.elementsTab;
  $('#el-input').placeholder = KINDS[kind].hint;

  const items = project[KINDS[kind].list].filter(e => matchesSearch(e) && (kind !== 'event' || eventMatchesFilter(e)));
  if (!items.length) {
    const searching = ui.search.trim() || ui.filter;
    $('#el-list').innerHTML = `<li class="empty-mini">${searching && project[KINDS[kind].list].length ? 'Nothing matches the current search or filter.' : `No ${KINDS[kind].plural.toLowerCase()} yet.<br>Type above and press Enter.`}</li>`;
    return;
  }
  $('#el-list').innerHTML = items.map(e => {
    let sub = '';
    if (kind === 'character') sub = e.role;
    else if (kind === 'event') sub = [e.date, storylineById(e.storylineId)?.name].filter(Boolean).join(' · ');
    else sub = e.description;
    const n = linksOf(e.id).length;
    return `<li class="row${isSelected(e.id) ? ' selected' : ''}" data-action="select" data-id="${e.id}" data-reveal="1" tabindex="0" style="--c:${entityColor(kind, e)}">
      <span class="swatch"></span>
      <div class="row-main"><div class="row-title${e.title ? '' : ' untitled'}">${esc(entityName(kind, e))}</div>${sub ? `<div class="row-sub">${esc(sub)}</div>` : ''}</div>
      ${n ? `<span class="badge" title="${n} connection${n > 1 ? 's' : ''}">${icon('link')}${n}</span>` : ''}
      <button class="icon-btn xs row-del" data-action="delete-entity" data-id="${e.id}" title="Delete" aria-label="Delete">${icon('trash')}</button></li>`;
  }).join('');
}

/* ---------- Main view dispatch ---------- */
function renderView() {
  const root = $('#view-root');
  if (project.view === 'timeline') renderTimelineView(root);
  else renderCanvasView(root, project.view);
  root.classList.toggle('connecting', !!ui.connectFrom);
}
function captureScroll() {
  const rv = ui.renderedView;
  if (!rv) return;
  const el = rv === 'timeline' ? $('#tl-scroll') : $('#canvas-scroll');
  if (el) ui.scroll[rv] = { left: el.scrollLeft, top: el.scrollTop };
}
function currentScroll(view) {
  if (ui.renderedView === view) {
    const el = view === 'timeline' ? $('#tl-scroll') : $('#canvas-scroll');
    if (el) return { left: el.scrollLeft, top: el.scrollTop };
  }
  return ui.scroll[view] || { left: 0, top: 0 };
}
function setView(view) {
  if (!VIEWS.includes(view) || project.view === view) return;
  captureScroll();
  project.view = view;                    // view choice is a preference, not an undoable edit
  project.updatedAt = now();
  scheduleSave();
  renderAll();
}

/* ---------- Canvas views (Idea Board + Connections share one engine) ---------- */
function renderCanvasView(root, mode) {
  if (ui.renderedView !== mode) {
    captureScroll();
    root.innerHTML = `<div class="canvas-scroll" id="canvas-scroll"><div class="canvas-inner" id="canvas-inner">
        <svg class="links" id="links" aria-hidden="true"></svg><div class="nodes" id="nodes"></div></div></div>
      <div class="canvas-overlay" id="canvas-overlay"></div>`;
    ui.renderedView = mode;
    const sc = $('#canvas-scroll');
    initCanvasInteractions(sc, mode);
    sc.scrollLeft = ui.scroll[mode].left;
    sc.scrollTop = ui.scroll[mode].top;
  }
  if (mode === 'graph') ensureGraphPositions();

  let html = '';
  let count = 0;
  for (const kind of KIND_ORDER) {
    if (mode === 'graph' && !ui.graphKinds.has(kind)) continue;
    for (const e of project[KINDS[kind].list]) {
      const pos = project.positions[mode][e.id];
      if (!pos) continue;
      count++;
      html += mode === 'board' ? boardCardHTML(kind, e, pos) : graphNodeHTML(kind, e, pos);
    }
  }
  $('#nodes').innerHTML = html;
  $('#canvas-scroll').classList.toggle('connecting', !!ui.connectFrom);
  renderCanvasOverlay(mode, count);
  drawLinks();
}

function boardCardHTML(kind, e, pos) {
  const m = KINDS[kind];
  const n = linksOf(e.id).length;
  const sub = kind === 'character' ? e.role : kind === 'event' ? e.date : '';
  return `<div class="node card${isSelected(e.id) ? ' selected' : ''}${isDimmed(kind, e) ? ' dim' : ''}${ui.connectFrom === e.id ? ' linking' : ''}"
      data-id="${e.id}" data-kind="${kind}" tabindex="0" role="button" aria-pressed="${isSelected(e.id)}" style="left:${pos.x}px;top:${pos.y}px;--c:${entityColor(kind, e)}">
    <div class="card-head"><span class="kind-tag">${icon(m.icon)}${m.label}</span>${n ? `<span class="link-count" title="${n} connection${n > 1 ? 's' : ''}">${icon('link')}${n}</span>` : ''}</div>
    <h4 class="card-title${e.title ? '' : ' untitled'}">${esc(entityName(kind, e))}</h4>
    ${sub ? `<div class="card-sub">${esc(sub)}</div>` : ''}
    ${e.description ? `<p class="card-desc">${esc(e.description)}</p>` : ''}
  </div>`;
}
function graphNodeHTML(kind, e, pos) {
  return `<div class="node gnode${isSelected(e.id) ? ' selected' : ''}${isDimmed(kind, e) ? ' dim' : ''}${ui.connectFrom === e.id ? ' linking' : ''}"
      data-id="${e.id}" data-kind="${kind}" tabindex="0" role="button" aria-pressed="${isSelected(e.id)}" style="left:${pos.x}px;top:${pos.y}px;--c:${entityColor(kind, e)}" title="${esc(KINDS[kind].label)}">
    <span class="g-ic">${icon(KINDS[kind].icon)}</span><span class="g-title${e.title ? '' : ' untitled'}">${esc(entityName(kind, e))}</span></div>`;
}

function renderCanvasOverlay(mode, count) {
  let html = '';
  if (ui.connectFrom) {
    const f = getEntity(ui.connectFrom);
    html += `<div class="connect-banner">${icon('link')}<span>Connecting “${esc(f ? entityName(f.kind, f.obj) : '')}” — click another ${mode === 'board' ? 'card' : 'node'}</span>
      <button class="btn sm" data-action="cancel-connect">Cancel</button></div>`;
  }
  if (mode === 'graph') {
    html += `<div class="overlay-top" ${ui.connectFrom ? 'style="top:58px"' : ''}>${KIND_ORDER.map(k =>
      `<button class="chip toggle${ui.graphKinds.has(k) ? ' on' : ''}" data-action="toggle-graph-kind" data-kind="${k}" style="--c:${KINDS[k].color}">${icon(KINDS[k].icon)}${KINDS[k].plural} ${project[KINDS[k].list].length}</button>`).join('')}</div>
      <div class="overlay-bottom"><button class="btn sm" data-action="tidy-graph">${icon('wand')}Tidy layout</button>
      <span class="overlay-hint">Select a node, then use Connect — or pick “Link to…” in the details panel</span></div>`;
  } else if (count) {
    html += `<div class="overlay-bottom"><span class="overlay-hint">Double-click empty space to add an idea · drag to arrange</span></div>`;
  }
  if (!count) {
    const total = KIND_ORDER.reduce((s, k) => s + project[KINDS[k].list].length, 0);
    const guide = `<ol class="guide"><li>${icon('idea')}<span><b>Capture</b> — add an idea, or press N to add anything quickly.</span></li>
      <li>${icon('board')}<span><b>Organize</b> — group events into storylines and chapters in the sidebar.</span></li>
      <li>${icon('graph')}<span><b>Explore</b> — switch to Timeline or Connections to see how it fits.</span></li></ol>`;
    html += mode === 'board'
      ? (total
        ? `<div class="empty-state">${icon('board', 'big')}<h3>Nothing on the board yet</h3><p>Add an idea, or turn on “Show on Idea Board” in an element’s details.</p>
          <button class="btn primary" data-action="add-idea">${icon('plus')}Add an idea</button></div>`
        : `<div class="empty-state">${icon('idea', 'big')}<h3>Start with one idea</h3><p>A scene, a twist, a character. You can organize it later.</p>
          <button class="btn primary" data-action="add-idea">${icon('plus')}Add your first idea</button>${guide}</div>`)
      : `<div class="empty-state">${icon('graph', 'big')}<h3>Nothing to connect yet</h3><p>${total ? 'All element types are hidden — turn one back on above.' : 'Add ideas, characters or events, then link them to see how your story fits together.'}</p>
          ${total ? '' : `<button class="btn primary" data-action="add-idea">${icon('plus')}Add an idea</button>`}</div>`;
  }
  $('#canvas-overlay').innerHTML = html;
}

/** Draw relationship lines between visible nodes. Called after render and on every drag move. */
function drawLinks() {
  const svg = $('#links');
  if (!svg || !project || project.view === 'timeline') return;
  const nodes = new Map($$('#nodes .node').map(n => [n.dataset.id, n]));
  const selRel = ui.selection?.type === 'rel' ? ui.selection.id : null;
  const selEnt = ui.selection?.type === 'entity' ? ui.selection.id : null;
  let out = '';
  for (const r of project.relationships) {
    const a = nodes.get(r.a), b = nodes.get(r.b);
    if (!a || !b) continue;
    const ca = { x: a.offsetLeft + a.offsetWidth / 2, y: a.offsetTop + a.offsetHeight / 2 };
    const cb = { x: b.offsetLeft + b.offsetWidth / 2, y: b.offsetTop + b.offsetHeight / 2 };
    const p1 = edgePoint(a, ca, cb), p2 = edgePoint(b, cb, ca);
    if (!p1 || !p2) continue;                              // nodes overlap: nothing sensible to draw
    const cls = `link${r.id === selRel ? ' sel' : ''}${selEnt && (r.a === selEnt || r.b === selEnt) ? ' hl' : ''}`;
    const mid = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
    out += `<g class="${cls}" data-rel="${r.id}"><line class="hit" x1="${p1.x}" y1="${p1.y}" x2="${p2.x}" y2="${p2.y}"/>
      <line class="vis" x1="${p1.x}" y1="${p1.y}" x2="${p2.x}" y2="${p2.y}"/>
      <circle class="end" cx="${p1.x}" cy="${p1.y}" r="3"/><circle class="end" cx="${p2.x}" cy="${p2.y}" r="3"/>
      ${r.label ? `<text x="${mid.x}" y="${mid.y - 6}">${esc(r.label)}</text>` : ''}</g>`;
  }
  svg.innerHTML = out;
}
/** Point where the line from this node's centre toward `to` leaves the node's rectangle. */
function edgePoint(node, from, to) {
  const dx = to.x - from.x, dy = to.y - from.y;
  const hw = node.offsetWidth / 2, hh = node.offsetHeight / 2;
  if (!dx && !dy) return null;
  const s = Math.min(hw / Math.max(Math.abs(dx), 1e-6), hh / Math.max(Math.abs(dy), 1e-6));
  if (s >= 1) return null;
  return { x: Math.round(from.x + dx * s), y: Math.round(from.y + dy * s) };
}

/* ---------- Timeline view ---------- */
function renderTimelineView(root) {
  if (ui.renderedView !== 'timeline') {
    captureScroll();
    root.innerHTML = `<div class="timeline-scroll" id="tl-scroll"><div class="tl">
        <div class="tl-head">
          <form class="quick-add" id="tl-add" autocomplete="off"><input type="text" name="title" placeholder="Add an event and press Enter…" aria-label="New event title"><button class="btn primary sm" type="submit">${icon('plus')}Add event</button></form>
          <button class="btn ghost sm" id="tl-sort" data-action="sort-events" title="Sort events that have dates; undated events keep their place">${icon('wand')}Sort by date</button>
        </div>
        <div id="tl-body"></div></div></div>`;
    ui.renderedView = 'timeline';
    const sc = $('#tl-scroll');
    initTimelineInteractions(sc);
    sc.scrollLeft = ui.scroll.timeline.left;
    sc.scrollTop = ui.scroll.timeline.top;
  }
  const events = project.events;
  $('#tl-sort').disabled = events.filter(e => parseEventDate(e.date) !== null).length < 2;
  if (!events.length) {
    $('#tl-body').innerHTML = `<div class="empty-state" style="position:static;transform:none;margin:40px auto 0">${icon('timeline', 'big')}<h3>No events yet</h3>
      <p>Events are the moments that make your story. Add one above — dates are optional, and you can drag events into any order.</p></div>`;
    return;
  }
  const visible = events.filter(eventMatchesFilter);
  if (!visible.length) {
    $('#tl-body').innerHTML = `<div class="empty-mini">No events in this ${ui.filter?.type === 'section' ? 'chapter' : 'storyline'} yet.</div>`;
    return;
  }
  const html = events.map((ev, i) => (eventMatchesFilter(ev) ? timelineItemHTML(ev, i) : '')).join('');
  $('#tl-body').innerHTML = `<ol class="tl-list" id="tl-list">${html}</ol>`;
  ui.flashId = null;
}

function timelineItemHTML(ev, i) {
  const line = storylineById(ev.storylineId);
  const section = sectionById(ev.sectionId);
  const rel = relatedEntities(ev.id);
  const chars = rel.filter(x => x.kind === 'character');
  const locs = rel.filter(x => x.kind === 'location');
  const ideas = rel.filter(x => x.kind === 'idea');
  const c = line ? line.color : entityColor('event', ev);
  const avatars = chars.length ? `<span class="avatars">${chars.slice(0, 5).map(x => `<span class="avatar" style="--c:${entityColor('character', x.obj)}" title="${esc(entityName('character', x.obj))}">${esc(initials(x.obj.title))}</span>`).join('')}${chars.length > 5 ? `<span class="avatar more">+${chars.length - 5}</span>` : ''}</span>` : '';
  const meta = [
    avatars,
    ...locs.slice(0, 2).map(x => `<span class="chip" style="--c:${KINDS.location.color}">${icon('pin')}${esc(entityName('location', x.obj))}</span>`),
    locs.length > 2 ? `<span class="chip">+${locs.length - 2}</span>` : '',
    ideas.length ? `<span class="chip" style="--c:${KINDS.idea.color}">${icon('idea')}${ideas.length} idea${ideas.length > 1 ? 's' : ''}</span>` : '',
    line ? `<span class="chip" style="--c:${line.color}">${icon('event')}${esc(line.name)}</span>` : '',
    section ? `<span class="chip">${icon('bookmark')}${esc(section.name)}</span>` : '',
  ].join('');
  return `<li class="tl-item${isSelected(ev.id) ? ' selected' : ''}${matchesSearch(ev) ? '' : ' dim'}${ui.flashId === ev.id ? ' flash' : ''}" data-id="${ev.id}" draggable="true" style="--c:${c}">
    <span class="tl-dot"></span>
    <article class="tl-card" data-action="select" data-id="${ev.id}" tabindex="0">
      <div class="tl-top"><span class="tl-num">#${i + 1}</span>${ev.date ? `<span class="tl-date">${esc(ev.date)}</span>` : ''}
        <span class="tl-tools"><button class="icon-btn xs" data-action="move-event" data-id="${ev.id}" data-dir="-1" title="Move earlier" aria-label="Move earlier">${icon('up')}</button>
        <button class="icon-btn xs" data-action="move-event" data-id="${ev.id}" data-dir="1" title="Move later" aria-label="Move later">${icon('down')}</button>
        <span class="tl-grip" title="Drag to reorder">${icon('grip')}</span></span></div>
      <h3 class="tl-title${ev.title ? '' : ' untitled'}">${esc(entityName('event', ev))}</h3>
      ${ev.description ? `<p class="tl-desc">${esc(ev.description)}</p>` : ''}
      <div class="tl-meta">${meta}</div>
    </article>
    <div class="tl-gap"><button class="tl-insert" data-action="insert-event" data-index="${i + 1}" title="Insert an event here" aria-label="Insert an event here">${icon('plus')}</button></div>
  </li>`;
}

/* ---------- Inspector (contextual details, no page navigation) ---------- */
function renderInspector() {
  const el = $('#inspector');
  const sel = ui.selection;
  if (!sel) { el.classList.remove('open'); el.innerHTML = ''; return; }
  el.classList.add('open');
  el.innerHTML = sel.type === 'rel' ? relationshipInspectorHTML(sel.id) : entityInspectorHTML(sel.id);
}

function relationshipInspectorHTML(relId) {
  const r = project.relationships.find(x => x.id === relId);
  if (!r) return '';
  const A = getEntity(r.a), B = getEntity(r.b);
  const chip = f => `<button class="chip-btn" data-action="select" data-id="${f.obj.id}" data-reveal="1" style="--c:${entityColor(f.kind, f.obj)}">${icon(KINDS[f.kind].icon)}<span>${esc(entityName(f.kind, f.obj))}</span></button>`;
  return `<div class="insp-head"><span class="kind-badge">${icon('link')}Connection</span>
      <button class="icon-btn" data-action="deselect" title="Close" aria-label="Close">${icon('close')}</button></div>
    <div class="insp-body">
      <div class="rel-pair">${A ? chip(A) : ''}${B ? chip(B) : ''}</div>
      <label class="field"><span>Label (optional)</span><input type="text" data-rel-label value="${esc(r.label)}" placeholder="e.g. rivals, owns, happens at" maxlength="60"></label>
    </div>
    <div class="insp-foot"><button class="btn danger-ghost sm" data-action="remove-link" data-rel="${r.id}">${icon('trash')}Remove connection</button></div>`;
}

function entityInspectorHTML(id) {
  const found = getEntity(id);
  if (!found) return '';
  const { kind, obj: e } = found;
  const m = KINDS[kind];
  const color = entityColor(kind, e);
  const canConnect = project.view !== 'timeline' && !!project.positions[project.view][id];

  let fields = '';
  if (kind === 'character') {
    fields += `<label class="field"><span>Role</span><input type="text" data-field="role" value="${esc(e.role)}" placeholder="Protagonist, mentor, rival…" maxlength="80"></label>`;
  }
  if (kind === 'event') {
    fields += `<label class="field"><span>Date or sequence position</span><input type="text" data-field="date" value="${esc(e.date)}" placeholder="e.g. 2024-05-01, Year 3, or 4" maxlength="40"></label>
      <label class="field"><span>Storyline</span><select data-change="storyline"><option value="">None</option>${project.storylines.map(s => `<option value="${s.id}"${s.id === e.storylineId ? ' selected' : ''}>${esc(s.name)}</option>`).join('')}</select></label>
      <label class="field"><span>Chapter / group</span><select data-change="section"><option value="">None</option>${project.sections.map(s => `<option value="${s.id}"${s.id === e.sectionId ? ' selected' : ''}>${esc(s.name)}</option>`).join('')}</select></label>`;
  }
  fields += `<label class="field"><span>${kind === 'note' ? 'Text' : 'Description'}</span><textarea data-field="description" rows="${kind === 'note' ? 9 : 4}" placeholder="${kind === 'note' ? 'Write freely…' : 'Optional — add detail whenever you are ready'}">${esc(e.description)}</textarea></label>`;
  if (kind === 'character') {
    fields += `<label class="field"><span>Notes</span><textarea data-field="notes" rows="3" placeholder="Backstory, voice, secrets…">${esc(e.notes)}</textarea></label>`;
  }

  const swatches = `<div class="field"><span>Color</span><div class="swatches">
      <button class="sw auto${e.color ? '' : ' on'}" style="--c:${m.color}" data-action="set-color" data-color="" title="Automatic" aria-label="Automatic color"></button>
      ${PALETTE.map(c => `<button class="sw${e.color === c ? ' on' : ''}" style="--c:${c}" data-action="set-color" data-color="${c}" aria-label="Color ${c}"></button>`).join('')}</div></div>`;

  const pin = kind === 'idea' ? '' : `<label class="check"><input type="checkbox" data-change="pin"${project.positions.board[id] ? ' checked' : ''}>Show on Idea Board</label>`;

  return `<div class="insp-head"><span class="kind-badge" style="--c:${color}">${icon(m.icon)}${m.label}</span>
      <div>${canConnect ? `<button class="icon-btn" data-action="start-connect" title="Connect to another card (C)" aria-label="Connect to another card">${icon('link')}</button>` : ''}
      <button class="icon-btn" data-action="deselect" title="Close (Esc)" aria-label="Close">${icon('close')}</button></div></div>
    <div class="insp-body">
      <label class="field"><span>Type</span><select data-change="convert">${KIND_ORDER.map(k => `<option value="${k}"${k === kind ? ' selected' : ''}>${KINDS[k].label}</option>`).join('')}</select></label>
      <label class="field"><span>${kind === 'character' ? 'Name' : 'Title'}</span><input type="text" data-field="title" value="${esc(e.title)}" placeholder="${kind === 'character' ? 'Character name' : `Untitled ${m.label.toLowerCase()}`}" maxlength="140"></label>
      ${fields}${swatches}${pin}
      ${relatedSectionHTML(id)}
    </div>
    <div class="insp-foot"><button class="btn danger-ghost sm" data-action="delete-entity" data-id="${id}">${icon('trash')}Delete</button>
      <span class="meta">Edited ${formatRelative(e.updatedAt)}</span></div>`;
}

/** "Connections" block: everything linked to this element, grouped by kind, plus a picker to link more. */
function relatedSectionHTML(id) {
  const rel = relatedEntities(id);
  const linkedIds = new Set(rel.map(x => x.obj.id));
  const groups = KIND_ORDER.map(k => {
    const items = rel.filter(x => x.kind === k);
    if (!items.length) return '';
    return `<div class="rel-group"><h6>${KINDS[k].plural}</h6>${items.map(x => `<div class="rel-item">
      <button class="chip-btn" data-action="select" data-id="${x.obj.id}" data-reveal="1" style="--c:${entityColor(k, x.obj)}">${icon(KINDS[k].icon)}<span>${esc(entityName(k, x.obj))}</span>${x.rel.label ? `<span class="lbl">${esc(x.rel.label)}</span>` : ''}</button>
      <button class="icon-btn xs" data-action="remove-link" data-rel="${x.rel.id}" title="Remove connection" aria-label="Remove connection">${icon('close')}</button></div>`).join('')}</div>`;
  }).join('');
  const options = KIND_ORDER.map(k => {
    const opts = project[KINDS[k].list].filter(o => o.id !== id && !linkedIds.has(o.id));
    return opts.length ? `<optgroup label="${KINDS[k].plural}">${opts.map(o => `<option value="${o.id}">${esc(entityName(k, o))}</option>`).join('')}</optgroup>` : '';
  }).join('');
  return `<div class="rel-section"><h5>Connections</h5>${groups || '<div class="mini-hint" style="padding-left:0">Not connected to anything yet.</div>'}
    ${options ? `<select data-change="add-link"><option value="">Link to…</option>${options}</select>` : ''}</div>`;
}

/* ==========================================================================
   7. Interactions: canvas, timeline drag & drop, resizers
   ========================================================================== */
function canvasPoint(e) {
  const r = $('#canvas-inner').getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
}

/** Pointer-based dragging for cards/nodes, drag-to-pan on empty space, click-to-select / click-to-connect. */
function initCanvasInteractions(scrollEl, mode) {
  let drag = null;

  scrollEl.addEventListener('pointerdown', e => {
    if (e.button !== 0) return;
    const node = e.target.closest('.node');
    if (node) {
      const pt = canvasPoint(e);
      drag = { type: 'node', id: node.dataset.id, node, startX: e.clientX, startY: e.clientY, offX: pt.x - node.offsetLeft, offY: pt.y - node.offsetTop, ox: node.offsetLeft, oy: node.offsetTop, moved: false };
      try { node.setPointerCapture(e.pointerId); } catch (_) { /* ignore */ }
      return;
    }
    if (e.target.closest('.link .hit')) return;          // lines handle their own click
    if (e.pointerType === 'mouse') {
      drag = { type: 'pan', startX: e.clientX, startY: e.clientY, sl: scrollEl.scrollLeft, st: scrollEl.scrollTop, moved: false };
      try { scrollEl.setPointerCapture(e.pointerId); } catch (_) { /* ignore */ }
    } else {
      drag = { type: 'tap', moved: false };              // touch: native scrolling; a tap on empty space deselects
    }
  });

  scrollEl.addEventListener('pointermove', e => {
    if (!drag) return;
    const dx = e.clientX - drag.startX, dy = e.clientY - drag.startY;
    if (!drag.moved && Math.hypot(dx, dy) < 4) return;
    drag.moved = true;
    if (drag.type === 'pan') {
      scrollEl.classList.add('panning');
      scrollEl.scrollLeft = drag.sl - dx;
      scrollEl.scrollTop = drag.st - dy;
      return;
    }
    if (drag.type !== 'node') return;
    // Position follows the pointer in canvas coordinates, so edge auto-scroll stays consistent.
    const pt = canvasPoint(e);
    let x = clamp(pt.x - drag.offX, 0, CANVAS_W - drag.node.offsetWidth);
    let y = clamp(pt.y - drag.offY, 0, CANVAS_H - drag.node.offsetHeight);
    if (store.prefs.snapToGrid && !e.shiftKey) { x = Math.round(x / GRID) * GRID; y = Math.round(y / GRID) * GRID; }
    drag.node.style.left = `${x}px`;
    drag.node.style.top = `${y}px`;
    drag.node.classList.add('dragging');
    drag.node.classList.toggle('copying', e.altKey);            // Alt held: dropping leaves the original and creates a copy
    drag.nx = x; drag.ny = y;
    drawLinks();
    const r = scrollEl.getBoundingClientRect();                 // gentle auto-scroll near the edges
    if (e.clientX > r.right - 40) scrollEl.scrollLeft += 16; else if (e.clientX < r.left + 40) scrollEl.scrollLeft -= 16;
    if (e.clientY > r.bottom - 40) scrollEl.scrollTop += 16; else if (e.clientY < r.top + 40) scrollEl.scrollTop -= 16;
  });

  const finish = e => {
    if (!drag) return;
    const d = drag; drag = null;
    scrollEl.classList.remove('panning');
    if (d.type === 'pan' || d.type === 'tap') { if (!d.moved) onCanvasBackgroundClick(); return; }
    d.node.classList.remove('dragging', 'copying');
    if (d.moved && e.type === 'pointerup' && e.altKey) {
      d.node.style.left = `${d.ox}px`; d.node.style.top = `${d.oy}px`;
      duplicateEntity(d.id, { mode, pos: { x: d.nx, y: d.ny } });
    } else if (d.moved && e.type === 'pointerup') {
      // Dragging a card selects it and saves its new position (one undo step per drop).
      ui.selection = { type: 'entity', id: d.id };
      act(p => { p.positions[mode][d.id] = { x: d.nx, y: d.ny }; });
    } else if (!d.moved) {
      onNodeClick(d.id);
    } else {
      renderView();                                            // drag cancelled by the browser: snap back
    }
  };
  scrollEl.addEventListener('pointerup', finish);
  scrollEl.addEventListener('pointercancel', finish);

  // Clicking a connection line selects it
  scrollEl.addEventListener('click', e => {
    const g = e.target.closest('.link');
    if (g) select({ type: 'rel', id: g.dataset.rel });
  });

  // Double-click: edit a card, or capture a new idea at that point
  scrollEl.addEventListener('dblclick', e => {
    const node = e.target.closest('.node');
    if (node) { select(node.dataset.id); focusInspectorTitle(); return; }
    if (e.target.closest('.link') || e.target.closest('.canvas-overlay')) return;
    const pt = canvasPoint(e);
    const at = { x: clamp(pt.x - (mode === 'board' ? CARD_W / 2 : 60), 0, CANVAS_W - CARD_W), y: clamp(pt.y - 20, 0, CANVAS_H - 160) };
    createEntity('idea', { focus: true, pos: mode === 'board' ? at : null, graphPos: mode === 'graph' ? at : null });
  });

  // Keyboard on a focused card
  scrollEl.addEventListener('keydown', e => {
    const node = e.target.closest?.('.node');
    if (!node) return;
    if (e.key === 'Enter') { e.preventDefault(); select(node.dataset.id); focusInspectorTitle(); }
    else if (e.key === ' ') { e.preventDefault(); onNodeClick(node.dataset.id); }
  });
}

function onNodeClick(id) {
  if (ui.connectFrom) {
    if (ui.connectFrom === id) { cancelConnect(); return; }
    const from = ui.connectFrom;
    ui.connectFrom = null;
    if (addLink(from, id)) { select(from); return; }
    renderView();
    return;
  }
  select(id);
}
function onCanvasBackgroundClick() {
  if (ui.connectFrom) { cancelConnect(); return; }
  if (ui.selection) select(null);
}
function startConnect() {
  if (ui.selection?.type !== 'entity') return;
  if (project.view === 'timeline') { toast('Switch to Idea Board or Connections to link visually'); return; }
  ui.connectFrom = ui.selection.id;
  renderView();
}
function cancelConnect() {
  if (!ui.connectFrom) return;
  ui.connectFrom = null;
  renderView();
}

/** Native drag & drop to reorder events (move buttons provide a keyboard / touch alternative). */
function initTimelineInteractions(scrollEl) {
  const clearMarks = () => $$('.tl-item', scrollEl).forEach(n => n.classList.remove('drop-before', 'drop-after', 'dragging'));
  scrollEl.addEventListener('dragstart', e => {
    const li = e.target.closest?.('.tl-item');
    if (!li) return;
    ui.dragEventId = li.dataset.id;
    e.dataTransfer.effectAllowed = 'move';
    try { e.dataTransfer.setData('text/plain', li.dataset.id); } catch (_) { /* ignore */ }
    li.classList.add('dragging');
  });
  scrollEl.addEventListener('dragover', e => {
    const li = e.target.closest?.('.tl-item');
    if (!ui.dragEventId || !li || li.dataset.id === ui.dragEventId) return;
    e.preventDefault();
    const r = li.getBoundingClientRect();
    const after = e.clientY > r.top + r.height / 2;
    $$('.tl-item', scrollEl).forEach(n => n.classList.remove('drop-before', 'drop-after'));
    li.classList.add(after ? 'drop-after' : 'drop-before');
    ui.dropTarget = { id: li.dataset.id, after };
  });
  scrollEl.addEventListener('drop', e => {
    if (!ui.dragEventId || !ui.dropTarget) return;
    e.preventDefault();
    const { id, after } = ui.dropTarget;
    const dragged = ui.dragEventId;
    ui.dragEventId = null; ui.dropTarget = null;
    clearMarks();
    moveEventTo(dragged, id, after);
  });
  scrollEl.addEventListener('dragend', () => { ui.dragEventId = null; ui.dropTarget = null; clearMarks(); });
}

/** Sidebar width, sidebar split and collapse. Values persist in store.prefs. */
function applyLayout() {
  const ws = $('#workspace');
  const pr = store.prefs;
  ws.style.setProperty('--sidebar-w', `${pr.sidebarWidth}px`);
  ws.style.setProperty('--struct', `${(pr.structFraction * 100).toFixed(1)}%`);
  ws.classList.toggle('sidebar-collapsed', pr.sidebarCollapsed);
  ws.classList.toggle('maximized', pr.maximized);
  ws.classList.toggle('drawer-open', ui.drawerOpen);
  $('#split-v').setAttribute('aria-valuenow', String(pr.sidebarWidth));
}
function savePrefs() { scheduleSave(); }
function toggleSidebar() {
  if (isMobile()) ui.drawerOpen = !ui.drawerOpen;
  else { store.prefs.sidebarCollapsed = !store.prefs.sidebarCollapsed; if (store.prefs.sidebarCollapsed === false) store.prefs.maximized = false; }
  applyLayout(); savePrefs(); if (project) renderHeader();
}
function toggleMaximize() {
  store.prefs.maximized = !store.prefs.maximized;
  ui.drawerOpen = false;
  applyLayout(); savePrefs(); renderHeader();
}
function resetLayout() {
  Object.assign(store.prefs, { sidebarWidth: DEFAULT_PREFS.sidebarWidth, structFraction: DEFAULT_PREFS.structFraction, sidebarCollapsed: false, maximized: false });
  applyLayout(); savePrefs(); renderHeader();
  toast('Layout reset');
}

function initResizers() {
  const splitV = $('#split-v'), splitH = $('#split-h');
  const dragger = (handle, onMove, onReset) => {
    handle.addEventListener('pointerdown', e => {
      if (e.button !== 0 || isMobile()) return;
      e.preventDefault();
      handle.setPointerCapture(e.pointerId);
      handle.classList.add('active');
      document.body.style.userSelect = 'none';
      const move = ev => onMove(ev);
      const up = () => {
        handle.removeEventListener('pointermove', move);
        handle.removeEventListener('pointerup', up);
        handle.removeEventListener('pointercancel', up);
        handle.classList.remove('active');
        document.body.style.userSelect = '';
        savePrefs();
      };
      handle.addEventListener('pointermove', move);
      handle.addEventListener('pointerup', up);
      handle.addEventListener('pointercancel', up);
    });
    handle.addEventListener('dblclick', () => { onReset(); applyLayout(); savePrefs(); });
  };
  dragger(splitV, ev => {
    store.prefs.sidebarWidth = clamp(ev.clientX - $('#sidebar').getBoundingClientRect().left, 220, 560);
    applyLayout();
  }, () => { store.prefs.sidebarWidth = DEFAULT_PREFS.sidebarWidth; });
  dragger(splitH, ev => {
    const r = $('#sidebar').getBoundingClientRect();
    store.prefs.structFraction = clamp((ev.clientY - r.top) / r.height, 0.15, 0.7);
    applyLayout();
  }, () => { store.prefs.structFraction = DEFAULT_PREFS.structFraction; });
  // Keyboard-accessible: arrow keys nudge the sidebar width
  splitV.addEventListener('keydown', e => {
    if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return;
    e.preventDefault();
    store.prefs.sidebarWidth = clamp(store.prefs.sidebarWidth + (e.key === 'ArrowRight' ? 16 : -16), 220, 560);
    applyLayout(); savePrefs();
  });
}

/* ==========================================================================
   8. Modals, toasts, popovers, actions, shortcuts, init
   ========================================================================== */

/** Small promise-based dialog. Resolves to field values, `true` (no fields) or `null` when cancelled. */
function openModal({ title, message = '', fields = [], confirmLabel = 'Save', danger = false }) {
  return new Promise(resolve => {
    const root = $('#modal-root');
    const prevFocus = document.activeElement;
    root.innerHTML = `<div class="modal-backdrop"><form class="modal" role="dialog" aria-modal="true" aria-labelledby="modal-title">
      <h2 id="modal-title">${esc(title)}</h2>${message ? `<p>${esc(message)}</p>` : ''}
      ${fields.map(f => `<label class="field"><span>${esc(f.label)}</span>${f.multiline
        ? `<textarea name="${f.name}" rows="3" placeholder="${esc(f.placeholder || '')}">${esc(f.value || '')}</textarea>`
        : `<input type="text" name="${f.name}" value="${esc(f.value || '')}" placeholder="${esc(f.placeholder || '')}" maxlength="${f.max || 120}" autocomplete="off">`}</label>`).join('')}
      <div class="modal-actions"><button type="button" class="btn ghost" data-cancel>Cancel</button>
      <button type="submit" class="btn ${danger ? 'danger' : 'primary'}">${esc(confirmLabel)}</button></div></form></div>`;
    const form = $('form', root);
    const close = value => { root.innerHTML = ''; if (prevFocus && prevFocus.focus) prevFocus.focus(); resolve(value); };
    form.addEventListener('submit', e => {
      e.preventDefault();
      const values = {};
      fields.forEach(f => { values[f.name] = form.elements[f.name].value; });
      close(fields.length ? values : true);
    });
    $('[data-cancel]', root).addEventListener('click', () => close(null));
    $('.modal-backdrop', root).addEventListener('mousedown', e => { if (e.target.classList.contains('modal-backdrop')) close(null); });
    form.addEventListener('keydown', e => {
      if (e.key === 'Escape') { e.stopPropagation(); close(null); return; }
      if (e.key !== 'Tab') return;                                   // keep Tab inside the dialog
      const f = $$('input, textarea, button', form), first = f[0], last = f[f.length - 1];
      if (e.shiftKey && document.activeElement === first) { e.preventDefault(); last.focus(); }
      else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
    });
    const first = form.querySelector('input, textarea') || form.querySelector('button[type="submit"]');
    first.focus();
    if (first.select) first.select();
  });
}

function toast(message, { label = '', fn = null, duration = 3600 } = {}) {
  const root = $('#toast-root');
  while (root.children.length >= 3) root.firstChild.remove();
  const el = document.createElement('div');
  el.className = 'toast';
  el.innerHTML = `<span>${esc(message)}</span>${label ? `<button class="toast-btn">${esc(label)}</button>` : ''}`;
  if (label) $('.toast-btn', el).addEventListener('click', () => { el.remove(); if (fn) fn(); });
  root.appendChild(el);
  setTimeout(() => el.classList.add('out'), duration);
  setTimeout(() => el.remove(), duration + 300);
}

/* ---------- Keyboard shortcuts dialog ---------- */
const SHORTCUTS = [
  ['General', [['N', 'Quick capture'], ['/ or Ctrl K', 'Search'], ['1 · 2 · 3', 'Board · Timeline · Connections'], ['Ctrl B', 'Toggle sidebar'], ['Esc', 'Close / deselect'], ['?', 'This list']]],
  ['Editing', [['Ctrl Z', 'Undo'], ['Ctrl Shift Z or Ctrl Y', 'Redo'], ['Ctrl D', 'Duplicate selected'], ['Ctrl C', 'Copy element'], ['Ctrl V', 'Paste element'], ['Enter', 'Edit selected in details'], ['C', 'Connect selected to another'], ['Del', 'Delete selected'], ['Ctrl S', 'Save now']]],
  ['Board & Connections', [['Alt + drag', 'Drop a copy, keep the original'], ['Shift + drag', 'Ignore grid snapping'], ['← ↑ → ↓', 'Nudge selected card'], ['Shift + arrows', 'Nudge further']]],
  ['Timeline', [['Alt + ↑ / ↓', 'Move selected event earlier / later']]],
];
function showShortcuts() {
  const root = $('#modal-root');
  if (root.firstChild) return;
  const prev = document.activeElement;
  const keys = k => k.split(' or ').map(g => `<kbd>${esc(g.trim())}</kbd>`).join(' or ');
  root.innerHTML = `<div class="modal-backdrop"><div class="modal wide" role="dialog" aria-modal="true" aria-labelledby="sc-title">
    <h2 id="sc-title">Keyboard shortcuts</h2>
    ${SHORTCUTS.map(([g, rows]) => `<h3 class="sc-group">${g}</h3><ul class="sc-list">${rows.map(([k, d]) => `<li><span>${esc(d)}</span><span class="sc-keys">${keys(k)}</span></li>`).join('')}</ul>`).join('')}
    <div class="modal-actions"><button type="button" class="btn primary" data-close>Done</button></div></div></div>`;
  const close = () => { root.innerHTML = ''; if (prev && prev.focus) prev.focus(); };
  $('[data-close]', root).addEventListener('click', close);
  $('.modal-backdrop', root).addEventListener('mousedown', e => { if (e.target.classList.contains('modal-backdrop')) close(); });
  $('.modal', root).addEventListener('keydown', e => { if (e.key === 'Escape') { e.stopPropagation(); close(); } });
  $('[data-close]', root).focus();
}

/* ---------- Popovers ---------- */
function closePopovers() {
  ui.popover = null;
  $$('.popover').forEach(p => { p.hidden = true; });
  $$('[data-action="toggle-popover"]').forEach(b => b.setAttribute('aria-expanded', 'false'));
}
function togglePopover(name) {
  const open = ui.popover === name;
  closePopovers();
  if (open) return;
  ui.popover = name;
  $(`#pop-${name}`).hidden = false;
  $(`[data-pop="${name}"]`).setAttribute('aria-expanded', 'true');
  if (name === 'add') { renderKindPicker(); $('#quick-input').focus(); }
}

/* ---------- Sample story (helps first-time users see the idea) ---------- */
function buildSampleProject() {
  const t = now();
  const p = normalizeProject({
    id: uid('proj'), title: 'The Lighthouse Keeper’s Daughter', createdAt: t, updatedAt: t, view: 'board',
    description: 'A sample story to explore Storyflow — edit, rearrange or delete anything.',
  });
  const mk = (kind, title, description, extra = {}) => {
    const e = { id: uid(kind), title, description, color: null, createdAt: t, updatedAt: t, ...extra };
    p[KINDS[kind].list].push(e);
    return e;
  };
  const main = { id: uid('storyline'), name: 'Mara’s search', color: PALETTE[0] };
  const past = { id: uid('storyline'), name: 'The old keeper', color: PALETTE[4] };
  p.storylines.push(main, past);
  const act1 = { id: uid('section'), name: 'Act I — The storm' };
  p.sections.push(act1);

  const mara = mk('character', 'Mara', 'Sixteen, stubborn, knows every rock along the coast.', { role: 'Protagonist', notes: 'Hides her fear of deep water.' });
  const elias = mk('character', 'Elias Vane', 'The last keeper of the Gull Point light. Disappeared the night of the storm.', { role: 'Missing father', notes: '' });
  const harbor = mk('location', 'Gull Point Lighthouse', 'White tower on black rock. The lamp has not burned in a year.');
  const village = mk('location', 'Saltwick village', 'Fishing town that pretends not to remember.');
  const e1 = mk('event', 'The lamp lights itself', 'Mara sees the beam sweep the bay — from a tower that has no keeper.', { date: '1', storylineId: main.id, sectionId: act1.id });
  const e2 = mk('event', 'Elias’s logbook is found', 'Pages torn out, a single page of coordinates left.', { date: '2', storylineId: main.id, sectionId: act1.id });
  const e3 = mk('event', 'The night of the storm', 'Told in fragments: what really happened to Elias.', { date: '0', storylineId: past.id });
  const i1 = mk('idea', 'The light answers questions', 'Each sweep of the beam means yes or no — but who is asking?');
  const i2 = mk('idea', 'Villagers share one secret', 'Everyone in Saltwick helped hide something that night.');
  const i3 = mk('idea', 'What if Mara is the keeper?', 'A twist: the lamp only lights for her bloodline.');
  const n1 = mk('note', 'Tone', 'Quiet, salt-stained, a little uncanny. Think slow dread, not jump scares.');

  const L = (a, b, label = '') => p.relationships.push({ id: uid('rel'), a: a.id, b: b.id, label });
  L(mara, e1, 'witnesses'); L(mara, e2); L(elias, e3, 'vanishes'); L(e1, harbor); L(e2, elias); L(e3, harbor);
  L(i1, e1); L(i2, village); L(i2, e3); L(i3, mara, 'twist'); L(mara, village);

  const spots = [[60, 70, mara], [330, 70, elias], [600, 70, harbor], [60, 260, i1], [330, 260, e1], [600, 260, e2], [60, 450, i3], [330, 450, i2], [600, 450, e3], [870, 70, village], [870, 260, n1]];
  for (const [x, y, e] of spots) p.positions.board[e.id] = { x, y };
  return normalizeProject(p);
}

/* ---------- Export ---------- */
function exportProject() {
  const blob = new Blob([JSON.stringify({ app: 'storyflow', version: SCHEMA_VERSION, project }, null, 2)], { type: 'application/json' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `${slug(project.title)}.storyflow.json`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
  toast('Story exported as JSON');
}

/* ---------- Dashboard dialogs ---------- */
async function newStoryFlow() {
  const res = await openModal({ title: 'New story', message: 'Give it a working title — you can change everything later.',
    fields: [{ name: 'title', label: 'Title', placeholder: 'Untitled story' }], confirmLabel: 'Create story' });
  if (!res) return;
  openProject(createProject(res.title).id);
}
async function renameProjectFlow(id) {
  const p = store.projects.find(x => x.id === id);
  if (!p) return;
  const res = await openModal({ title: 'Rename story', fields: [
    { name: 'title', label: 'Title', value: p.title },
    { name: 'description', label: 'Short description (optional)', value: p.description, multiline: true, placeholder: 'What is this story about?' }], confirmLabel: 'Save' });
  if (!res) return;
  p.title = res.title.trim() || 'Untitled story';
  p.description = res.description.trim();
  p.updatedAt = now();
  flushSave();
  renderDashboard();
}
async function deleteProjectFlow(id) {
  const p = store.projects.find(x => x.id === id);
  if (!p) return;
  const ok = await openModal({ title: `Delete “${p.title || 'Untitled story'}”?`, message: 'The story and all of its cards, events and connections will be permanently removed from this browser.', confirmLabel: 'Delete story', danger: true });
  if (!ok) return;
  removedIds.add(id);
  store.projects = store.projects.filter(x => x.id !== id);
  flushSave();
  renderDashboard();
  toast('Story deleted');
}

/* ---------- Central action handler (event delegation via data-action) ---------- */
function handleAction(action, el, e) {
  const id = el.dataset.id;
  switch (action) {
    // Dashboard
    case 'new-story': newStoryFlow(); break;
    case 'import-story': $('#import-file').click(); break;
    case 'open-project': openProject(id); break;
    case 'rename-project': e.stopPropagation(); renameProjectFlow(id); break;
    case 'delete-project': e.stopPropagation(); deleteProjectFlow(id); break;
    case 'load-sample': { const p = buildSampleProject(); store.projects.unshift(p); flushSave(); openProject(p.id); break; }

    // Workspace chrome
    case 'go-dashboard': closeProject(); break;
    case 'toggle-sidebar': closePopovers(); toggleSidebar(); break;
    case 'close-drawer': ui.drawerOpen = false; applyLayout(); break;
    case 'toggle-maximize': closePopovers(); toggleMaximize(); break;
    case 'reset-layout': closePopovers(); resetLayout(); break;
    case 'toggle-snap': store.prefs.snapToGrid = !store.prefs.snapToGrid; savePrefs(); renderHeader(); toast(`Snap to grid ${store.prefs.snapToGrid ? 'on' : 'off'}`); break;
    case 'export-json': closePopovers(); exportProject(); break;
    case 'show-shortcuts': closePopovers(); showShortcuts(); break;
    case 'undo': undo(); break;
    case 'redo': redo(); break;
    case 'toggle-popover': togglePopover(el.dataset.pop); break;
    case 'set-add-kind': ui.addKind = el.dataset.kind; renderKindPicker(); $('#quick-input').focus(); break;
    case 'set-view': setView(el.dataset.view); break;
    case 'clear-filter': ui.filter = null; renderAll(['inspector']); break;
    case 'primary-add':
    case 'add-idea':
      if (project.view === 'timeline') createEntity('event', { focus: true });
      else createEntity('idea', { focus: true });
      break;

    // Selection & elements
    case 'select':
      if (e.target.closest('[data-action="move-event"], [data-action="insert-event"]')) break;
      select(id, { reveal: el.dataset.reveal === '1' });
      if (isMobile() && el.classList.contains('row')) { ui.drawerOpen = false; applyLayout(); }
      break;
    case 'deselect': select(null); break;
    case 'set-tab': ui.elementsTab = el.dataset.kind; renderElements(); $('#el-input').focus(); break;
    case 'delete-entity': e.stopPropagation(); deleteEntity(id); break;
    case 'set-color': if (ui.selection?.type === 'entity') setField(ui.selection.id, 'color', el.dataset.color || null); break;
    case 'remove-link': removeLink(el.dataset.rel); break;
    case 'start-connect': startConnect(); break;
    case 'cancel-connect': cancelConnect(); break;
    case 'toggle-graph-kind': {
      const k = el.dataset.kind;
      if (ui.graphKinds.has(k)) ui.graphKinds.delete(k); else ui.graphKinds.add(k);
      renderView();
      break;
    }
    case 'tidy-graph':
      act(p => { p.positions.graph = {}; ensureGraphPositions(); });
      toast('Layout tidied', { label: 'Undo', fn: undo });
      break;

    // Structure
    case 'add-struct': addStructItem(el.dataset.type); break;
    case 'rename-struct': ui.editingStruct = id; renderStructure(); break;
    case 'delete-struct': deleteStructItem(id); break;
    case 'toggle-filter': {
      const same = ui.filter && ui.filter.id === id;
      ui.filter = same ? null : { type: el.dataset.type, id };
      renderAll(['inspector']);
      break;
    }
    case 'cycle-color': {
      const s = project.storylines.find(x => x.id === id);
      if (s) act(p => { const t = p.storylines.find(x => x.id === id); t.color = PALETTE[(PALETTE.indexOf(t.color) + 1) % PALETTE.length]; });
      break;
    }

    // Timeline
    case 'sort-events': sortEventsByDate(); break;
    case 'move-event': e.stopPropagation(); moveEventStep(id, Number(el.dataset.dir)); break;
    case 'insert-event': e.stopPropagation(); createEntity('event', { insertAt: Number(el.dataset.index), focus: true }); break;
    default: break;
  }
}

function initEvents() {
  // One delegated click handler for every [data-action]
  document.addEventListener('click', e => {
    if (ui.popover && !e.target.closest('.pop-anchor')) closePopovers();
    const el = e.target.closest('[data-action]');
    if (!el) return;
    handleAction(el.dataset.action, el, e);
  });
  // Cards in lists respond to Enter
  document.addEventListener('keydown', e => {
    const t = e.target;
    if (e.key === 'Enter' && t.matches?.('.row, .tl-card, .project-card')) { e.preventDefault(); t.click(); }
  });

  // Inline structure rename
  document.addEventListener('keydown', e => {
    if (!e.target.matches?.('.s-edit')) return;
    if (e.key === 'Enter') { e.preventDefault(); e.target.blur(); }
    else if (e.key === 'Escape') { e.target.dataset.cancel = '1'; e.target.blur(); }
    e.stopPropagation();
  }, true);
  document.addEventListener('focusout', e => { if (e.target.matches?.('.s-edit')) commitStructEdit(e.target); });
  document.addEventListener('dblclick', e => {
    const name = e.target.closest?.('.s-name');
    if (name) { ui.editingStruct = name.dataset.id; renderStructure(); }
  });

  // Import a story exported earlier (JSON)
  $('#import-file').addEventListener('change', async e => {
    const file = e.target.files[0];
    e.target.value = '';
    if (!file) return;
    try {
      const data = JSON.parse(await file.text());
      const src = data && data.project ? data.project : data;
      if (!src || !['ideas', 'characters', 'events', 'locations', 'notes'].some(k => Array.isArray(src[k]))) throw new Error('not a story');
      const p = normalizeProject({ ...src, id: uid('proj'), updatedAt: now() });
      store.projects.unshift(p);
      flushSave();
      renderDashboard();
      toast(`Imported “${p.title}”`);
    } catch (err) { toast('That file is not a Storyflow export.'); }
  });

  // Browser Back / Forward moves between the dashboard and a story
  window.addEventListener('hashchange', () => {
    const m = location.hash.match(/^#story=(.+)$/);
    const id = m ? decodeURIComponent(m[1]) : null;
    if (id && (!project || project.id !== id) && store.projects.some(p => p.id === id)) openProject(id);
    else if (!id && project) closeProject();
  });
  // Another tab saved: refresh the dashboard (an open story is merged on the next save)
  window.addEventListener('storage', e => { if (e.key === STORAGE_KEY && !project) { mergeExternal(); renderDashboard(); } });
  window.addEventListener('pagehide', () => { if (saveTimer) flushSave(); });

  // Header: story title
  const title = $('#story-title');
  title.addEventListener('input', () => act(p => { p.title = title.value; }, { coalesce: 'project-title', skip: ['sidebar', 'view', 'inspector'] }));
  title.addEventListener('keydown', e => { if (e.key === 'Enter') title.blur(); });

  // Search (applies to every view and the elements list)
  $('#search').addEventListener('input', e => { ui.search = e.target.value; renderAll(['inspector']); });

  // Quick capture popover
  $('#quick-form').addEventListener('submit', e => {
    e.preventDefault();
    const input = $('#quick-input');
    const v = input.value.trim();
    if (!v) return;
    createEntity(ui.addKind, { title: v, select: false });
    input.value = '';
    toast(`${KINDS[ui.addKind].label} added`, { duration: 1800 });
    input.focus();
  });

  // Elements panel quick add
  $('#el-add').addEventListener('submit', e => {
    e.preventDefault();
    const input = $('#el-input');
    const v = input.value.trim();
    createEntity(ui.elementsTab, { title: v, select: true, focus: !v });
    input.value = '';
    if (v) input.focus();
  });

  // Timeline quick add
  document.addEventListener('submit', e => {
    if (e.target.id !== 'tl-add') return;
    e.preventDefault();
    const input = e.target.elements.title;
    const v = input.value.trim();
    createEntity('event', { title: v, select: !v, focus: !v });
    input.value = '';
    input.focus();
    const sc = $('#tl-scroll');
    if (sc && v) requestAnimationFrame(() => { sc.scrollTop = sc.scrollHeight; });
  });

  // Inspector: live editing (inputs) and discrete changes (selects, checkboxes)
  const insp = $('#inspector');
  insp.addEventListener('input', e => {
    const t = e.target, sel = ui.selection;
    if (!sel) return;
    if (t.dataset.field && sel.type === 'entity') setField(sel.id, t.dataset.field, t.value, { skip: ['inspector'] });
    else if (t.dataset.relLabel !== undefined && sel.type === 'rel') {
      act(p => { const r = p.relationships.find(x => x.id === sel.id); if (r) r.label = t.value; }, { coalesce: `rel-${sel.id}`, skip: ['inspector', 'sidebar'] });
    }
  });
  insp.addEventListener('change', e => {
    const t = e.target, sel = ui.selection;
    if (!sel || sel.type !== 'entity' || !t.dataset.change) return;
    switch (t.dataset.change) {
      case 'convert': convertKind(sel.id, t.value); break;
      case 'storyline': setField(sel.id, 'storylineId', t.value || null); break;
      case 'section': setField(sel.id, 'sectionId', t.value || null); break;
      case 'add-link': if (t.value) addLink(sel.id, t.value); break;
      case 'pin':
        act(p => { if (t.checked) p.positions.board[sel.id] = findFreeBoardSpot(); else delete p.positions.board[sel.id]; });
        toast(t.checked ? 'Added to the Idea Board' : 'Removed from the Idea Board');
        break;
      default: break;
    }
  });

  // Keyboard shortcuts
  document.addEventListener('keydown', onGlobalKey);
  window.addEventListener('beforeunload', () => { if (saveTimer) flushSave(); });
  document.addEventListener('visibilitychange', () => { if (document.hidden && saveTimer) flushSave(); });
  window.matchMedia('(max-width: 860px)').addEventListener?.('change', () => { ui.drawerOpen = false; applyLayout(); });
}

function onGlobalKey(e) {
  if ($('#modal-root').firstChild) return;                               // dialogs manage their own keys
  const mod = e.ctrlKey || e.metaKey;
  const key = /^Key[A-Z]$/.test(e.code) ? e.code.slice(3).toLowerCase() : e.key.toLowerCase();   // by physical key, so shortcuts work on any layout
  const typing = /^(INPUT|TEXTAREA|SELECT)$/.test(e.target.tagName) || e.target.isContentEditable;

  if (mod && key === 's') { e.preventDefault(); if (project || store.projects.length) { flushSave(); toast('Saved'); } return; }

  if (!project) { if (!mod && !typing && key === 'n') { e.preventDefault(); newStoryFlow(); } return; }

  if (mod && key === 'b') { e.preventDefault(); toggleSidebar(); return; }
  if (mod && !typing && key === 'z') { e.preventDefault(); if (e.shiftKey) redo(); else undo(); return; }
  if (mod && !typing && key === 'y') { e.preventDefault(); redo(); return; }

  if (e.key === 'Escape') {
    if (e.target.id === 'search' && ui.search) { ui.search = ''; e.target.value = ''; renderAll(['inspector']); return; }
    if (ui.popover && e.target.closest?.('.popover')) { const name = ui.popover; closePopovers(); $(`[data-pop="${name}"]`)?.focus(); return; }
    if (typing && e.target.id !== 'search') { e.target.blur(); return; }
    if (ui.popover) closePopovers();
    else if (ui.connectFrom) cancelConnect();
    else if (ui.selection) select(null);
    else if (ui.drawerOpen) { ui.drawerOpen = false; applyLayout(); }
    else if (store.prefs.maximized) toggleMaximize();
    return;
  }
  const sel = ui.selection?.type === 'entity' ? getEntity(ui.selection.id) : null;
  if (mod && key === 'k') { e.preventDefault(); $('#search').focus(); return; }
  if (mod && !typing && sel && !window.getSelection().toString()) {
    if (key === 'd') { e.preventDefault(); duplicateEntity(sel.obj.id); return; }
    if (key === 'c') { e.preventDefault(); copySelected(); return; }
  }
  if (mod && !typing && key === 'v' && ui.clip) { e.preventDefault(); pasteClip(); return; }
  if (!typing && !mod && e.altKey && sel?.kind === 'event' && project.view === 'timeline' && (key === 'arrowup' || key === 'arrowdown')) {
    e.preventDefault(); moveEventStep(sel.obj.id, key === 'arrowup' ? -1 : 1); return;
  }
  if (typing || mod || e.altKey) return;

  switch (key) {
    case 'arrowleft': case 'arrowright': case 'arrowup': case 'arrowdown': {
      const step = store.prefs.snapToGrid ? GRID : (e.shiftKey ? 48 : 8);
      const [dx, dy] = { arrowleft: [-1, 0], arrowright: [1, 0], arrowup: [0, -1], arrowdown: [0, 1] }[key];
      if (nudgeSelected(dx * step, dy * step)) e.preventDefault();
      break;
    }
    case '?': e.preventDefault(); showShortcuts(); break;
    case 'n': e.preventDefault(); togglePopover('add'); break;
    case '/': e.preventDefault(); $('#search').focus(); break;
    case '1': setView('board'); break;
    case '2': setView('timeline'); break;
    case '3': setView('graph'); break;
    case 'c': if (ui.selection?.type === 'entity') { e.preventDefault(); startConnect(); } break;
    case 'delete':
    case 'backspace':
      if (ui.selection?.type === 'entity') { e.preventDefault(); deleteEntity(ui.selection.id); }
      else if (ui.selection?.type === 'rel') { e.preventDefault(); removeLink(ui.selection.id); }
      break;
    case 'enter': if (ui.selection?.type === 'entity') { e.preventDefault(); focusInspectorTitle(); } break;
    default: break;
  }
}

/* ---------- Init ---------- */
function init() {
  loadStore();
  initEvents();
  initResizers();
  renderDashboard();
  // Reopen the story named in the URL hash (so a refresh returns you to your work)
  const m = location.hash.match(/^#story=(.+)$/);
  if (m) {
    const id = decodeURIComponent(m[1]);
    if (store.projects.some(p => p.id === id)) openProject(id);
  }
}
init();