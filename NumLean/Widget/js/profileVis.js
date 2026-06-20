import * as React from 'react'

const VERSION = 'htuple-profile-vis-v6'

function displayProfile(text) {
  const s = text || '•'
  if (s.startsWith('hp(') && s.endsWith(')')) return s.slice(3, -1)
  return s
}

function skipSpaces(text, i) {
  while (i < text.length && /\s/.test(text[i])) i += 1
  return i
}

function parseProfileAt(text, i) {
  i = skipSpaces(text, i)
  if (text[i] === '•' || text[i] === '*') {
    return [{ kind: 'leaf' }, i + 1]
  }
  if (text[i] !== '(') throw new Error('expected ( or •')
  const leftResult = parseProfileAt(text, i + 1)
  const left = leftResult[0]
  i = skipSpaces(text, leftResult[1])
  if (text[i] !== ',') throw new Error('expected comma')
  const rightResult = parseProfileAt(text, i + 1)
  const right = rightResult[0]
  i = skipSpaces(text, rightResult[1])
  if (text[i] !== ')') throw new Error('expected )')
  return [{ kind: 'prod', left, right }, i + 1]
}

function parseProfile(text) {
  const result = parseProfileAt(text || '•', 0)
  return result[0]
}

function measure(node) {
  if (node.kind === 'leaf') return { leaves: 1, depth: 0 }
  const left = measure(node.left)
  const right = measure(node.right)
  return { leaves: left.leaves + right.leaves, depth: 1 + Math.max(left.depth, right.depth) }
}

function assignSemanticPositions(node, counter) {
  if (node.kind === 'leaf') {
    node.pos = counter.value
    counter.value += 1
    return
  }
  assignSemanticPositions(node.left, counter)
  node.pos = counter.value
  counter.value += 1
  assignSemanticPositions(node.right, counter)
}

function layout(node, depth, nodes, edges, parentId) {
  const id = nodes.length
  const entry = { id, kind: node.kind, depth, x: node.pos == null ? 0 : node.pos }
  nodes.push(entry)
  if (parentId !== null) edges.push({ from: parentId, to: id })
  if (node.kind === 'leaf') return entry.x
  layout(node.left, depth + 1, nodes, edges, id)
  layout(node.right, depth + 1, nodes, edges, id)
  return entry.x
}

function useElementWidth() {
  const ref = React.useRef(null)
  const [width, setWidth] = React.useState(900)
  React.useEffect(() => {
    const el = ref.current
    if (!el) return
    const update = () => setWidth(el.clientWidth || 900)
    update()
    if (typeof ResizeObserver === 'undefined') {
      window.addEventListener('resize', update)
      return () => window.removeEventListener('resize', update)
    }
    const observer = new ResizeObserver(update)
    observer.observe(el)
    return () => observer.disconnect()
  }, [])
  return [ref, width]
}

function Style() {
  return React.createElement('style', null, `
    .profile-vis {
      --bg: #0d1017;
      --panel: #151b26;
      --text: #edf2fb;
      --muted: #aab6ca;
      --line: #30394a;
      --leaf: #9bd6ff;
      --node: #ffd166;
      color: var(--text);
      background: radial-gradient(circle at 15% 0%, rgba(77, 99, 150, .42), transparent 34%), linear-gradient(180deg, #111827, var(--bg));
      border: 1px solid var(--line);
      border-radius: 16px;
      padding: 14px;
      width: 100%;
      overflow: hidden;
      font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    }
    .profile-vis .formula {
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
      font-size: 18px;
      font-weight: 800;
      color: #f4f7ff;
      background: rgba(255,255,255,.055);
      border: 1px solid rgba(255,255,255,.1);
      border-radius: 12px;
      padding: 10px 12px;
      margin-bottom: 12px;
      white-space: nowrap;
      width: max-content;
      min-width: 100%;
    }
    .profile-vis .tree-panel {
      background: rgba(16,22,33,.72);
      border: 1px solid rgba(255,255,255,.08);
      border-radius: 13px;
      padding: 10px;
      overflow: hidden;
    }
    .profile-vis .tree-scale-shell { transform-origin: top left; }
    .profile-vis svg { display: block; }
    .profile-vis .edge { stroke: #8190aa; stroke-width: 2; opacity: .88; }
    .profile-vis .prod { fill: var(--node); stroke: rgba(0,0,0,.38); stroke-width: 1.5; }
    .profile-vis .leaf { fill: var(--leaf); stroke: rgba(0,0,0,.38); stroke-width: 1.5; }
    .profile-vis text { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-weight: 900; fill: #071018; text-anchor: middle; dominant-baseline: central; }
    .profile-vis .profile-grid { display: grid; gap: 14px; }
    .profile-vis .profile-row { display: flex; flex-wrap: wrap; gap: 14px; align-items: start; }
    .profile-vis .profile-card { flex: 1 1 260px; min-width: 220px; }
  `)
}

function TreeSvg({ tree, source, availableWidth }) {
  const stats = measure(tree)
  const nodes = []
  const edges = []
  const counter = { value: 0 }
  assignSemanticPositions(tree, counter)
  layout(tree, 0, nodes, edges, null)
  const tokenStep = 54
  const yStep = 72
  const marginX = 36
  const marginY = 32
  const tokenCount = Math.max(1, counter.value)
  const width = Math.max(220, marginX * 2 + Math.max(1, tokenCount - 1) * tokenStep)
  const height = Math.max(140, marginY * 2 + stats.depth * yStep)
  const scale = Math.min(1, Math.max(0.1, (availableWidth - 4) / Math.max(1, width)))
  const byId = new Map()
  for (let i = 0; i < nodes.length; i++) byId.set(nodes[i].id, nodes[i])
  function pos(n) {
    return { x: marginX + n.x * tokenStep, y: marginY + n.depth * yStep }
  }
  return React.createElement('div', { style: { width: width * scale, height: height * scale } },
    React.createElement('div', { className: 'tree-scale-shell', style: { transform: `scale(${scale})`, width, height } },
      React.createElement('svg', { viewBox: `0 0 ${width} ${height}`, width, height, role: 'img' },
        edges.map((e, i) => {
          const a = pos(byId.get(e.from))
          const b = pos(byId.get(e.to))
          return React.createElement('line', { key: `e${i}`, className: 'edge', x1: a.x, y1: a.y, x2: b.x, y2: b.y })
        }),
        nodes.map((n) => {
          const p = pos(n)
          if (n.kind === 'leaf') {
            return React.createElement('g', { key: n.id },
              React.createElement('circle', { className: 'leaf', cx: p.x, cy: p.y, r: 18 }),
              React.createElement('text', { x: p.x, y: p.y + 1, fontSize: 20 }, '•')
            )
          }
          return React.createElement('g', { key: n.id },
            React.createElement('rect', { className: 'prod', x: p.x - 18, y: p.y - 18, width: 36, height: 36, rx: 9 }),
            React.createElement('text', { x: p.x, y: p.y, fontSize: 18 }, ',')
          )
        })
      )
    )
  )
}

function ProfileCard(props) {
  const [treeRef, treeWidth] = useElementWidth()
  const profileText = displayProfile(props.profile)
  let tree
  let error = null
  try {
    tree = parseProfile(profileText)
  } catch (e) {
    error = String(e && e.message ? e.message : e)
    tree = { kind: 'leaf' }
  }
  return React.createElement('div', { className: 'profile-card' },
    React.createElement('div', { className: 'formula' }, profileText),
    React.createElement('div', { ref: treeRef, className: 'tree-panel' },
      React.createElement(TreeSvg, { tree, source: profileText, availableWidth: treeWidth })
    )
  )
}

function asGridRows(props) {
  if (Array.isArray(props.rows)) {
    return props.rows.map((row) => Array.isArray(row) ? row : [])
  }
  return [[props]]
}

function ProfileGrid(props) {
  const rows = asGridRows(props)
  return React.createElement('div', { className: 'profile-grid' },
    rows.map((row, r) => React.createElement('div', { key: `r${r}`, className: 'profile-row' },
      row.map((item, c) => React.createElement(ProfileCard, Object.assign({ key: `c${c}` }, item)))
    ))
  )
}

export default function ProfileVis(props) {
  return React.createElement('div', { className: 'profile-vis', 'data-version': VERSION },
    React.createElement(Style),
    React.createElement(ProfileGrid, props)
  )
}
