import * as React from 'react'

const VERSION = 'numlean-visualize-v42'
const RANK_GAP = 3
const RANK_BLOCK_GAP = 7
const RANK_STAMP_BORDER = 2
const CELL_RADIUS = 4
const HIERARCHY_EDGE_MAX_HALF_ANGLE = (5 * Math.PI) / 12
const HIERARCHY_EDGE_SOFT_HALF_ANGLE = Math.PI / 4
const HIERARCHY_EDGE_MIN_DY = 30
const HIERARCHY_EDGE_DIRECTION_STRENGTH = 0.22
const MATHJAX_URL = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js'
const D3_URL = 'https://cdn.jsdelivr.net/npm/d3@7/dist/d3.min.js'

let mathJaxPromise = null
let d3Promise = null

function loadD3() {
  if (globalThis.d3 && typeof globalThis.d3.forceSimulation === 'function') {
    return Promise.resolve(globalThis.d3)
  }
  if (d3Promise) return d3Promise
  d3Promise = new Promise((resolve, reject) => {
    const script = document.createElement('script')
    script.src = D3_URL
    script.async = true
    script.onload = () => {
      if (globalThis.d3 && typeof globalThis.d3.forceSimulation === 'function') resolve(globalThis.d3)
      else reject(new Error(`loaded ${D3_URL}, but d3.forceSimulation is unavailable`))
    }
    script.onerror = () => reject(new Error(`failed to load ${D3_URL}`))
    document.head.appendChild(script)
  })
  return d3Promise
}

function loadMathJax() {
  if (globalThis.MathJax && typeof globalThis.MathJax.tex2svgPromise === 'function') {
    return Promise.resolve(globalThis.MathJax)
  }
  if (mathJaxPromise) return mathJaxPromise
  globalThis.MathJax = {
    ...(globalThis.MathJax || {}),
    tex: { inlineMath: [['$', '$'], ['\\(', '\\)']], ...(globalThis.MathJax && globalThis.MathJax.tex) },
    svg: { fontCache: 'global', ...(globalThis.MathJax && globalThis.MathJax.svg) },
    startup: { typeset: false, ...(globalThis.MathJax && globalThis.MathJax.startup) }
  }
  const ready = () => {
    const mathjax = globalThis.MathJax
    if (mathjax && mathjax.startup && mathjax.startup.promise) {
      return mathjax.startup.promise.then(() => mathjax)
    }
    return Promise.resolve(mathjax)
  }
  mathJaxPromise = new Promise((resolve, reject) => {
    const script = document.createElement('script')
    script.src = MATHJAX_URL
    script.async = true
    script.onload = () => ready().then(resolve, reject)
    script.onerror = () => reject(new Error(`failed to load ${MATHJAX_URL}`))
    document.head.appendChild(script)
  })
  return mathJaxPromise
}

function trimMathJaxSvg(node) {
  const svg = node && node.querySelector && node.querySelector('svg')
  if (!svg || typeof svg.getBBox !== 'function') return
  try {
    const box = svg.getBBox()
    if (!box || box.width <= 0 || box.height <= 0) return
    const pad = 60
    const width = box.width + 2 * pad
    const height = box.height + 2 * pad
    svg.setAttribute('viewBox', `${box.x - pad} ${box.y - pad} ${width} ${height}`)
    svg.setAttribute('preserveAspectRatio', 'xMidYMid meet')
    svg.removeAttribute('width')
    svg.removeAttribute('height')
    svg.style.maxWidth = '100%'
    svg.style.width = '100%'
    svg.style.maxHeight = '100%'
    svg.style.height = '100%'
    svg.style.verticalAlign = 'top'
  } catch (_e) {}
}

function displayStyleTex(source) {
  const text = source || ''
  return text.trimStart().startsWith('\\displaystyle') ? text : `\\displaystyle ${text}`
}

function asNumber(x) {
  if (typeof x === 'bigint') return Number(x)
  return Number(x == null ? 0 : x)
}

function asArray(xs) {
  return Array.isArray(xs) ? xs : []
}

function displayText(text) {
  const s = text || ''
  if (s.startsWith('hp(') && s.endsWith(')')) return s.slice(3, -1)
  return s
}

function skipSpaces(text, i) {
  while (i < text.length && /\s/.test(text[i])) i += 1
  return i
}

function parseTreeAt(text, i) {
  i = skipSpaces(text, i)
  if (text[i] === '(') {
    const leftResult = parseTreeAt(text, i + 1)
    const left = leftResult[0]
    i = skipSpaces(text, leftResult[1])
    if (text[i] !== ',') throw new Error('expected comma')
    const rightResult = parseTreeAt(text, i + 1)
    const right = rightResult[0]
    i = skipSpaces(text, rightResult[1])
    if (text[i] !== ')') throw new Error('expected )')
    return [{ kind: 'prod', left, right, label: ',' }, i + 1]
  }
  let j = i
  while (j < text.length && text[j] !== ',' && text[j] !== ')' && !/\s/.test(text[j])) j += 1
  const label = text.slice(i, j) || '•'
  return [{ kind: 'leaf', label }, j]
}

function parseTree(text) {
  return parseTreeAt(text || '•', 0)[0]
}

function measure(node) {
  if (node.kind === 'leaf') return { depth: 0 }
  const left = measure(node.left)
  const right = measure(node.right)
  return { depth: 1 + Math.max(left.depth, right.depth) }
}

function assignPositions(node, counter) {
  if (node.kind === 'leaf') {
    node.pos = counter.value
    counter.value += 1
    return
  }
  assignPositions(node.left, counter)
  node.pos = counter.value
  counter.value += 1
  assignPositions(node.right, counter)
}

function collectTree(node, depth, nodes, edges, parentId) {
  const id = nodes.length
  nodes.push({ id, kind: node.kind, label: node.label, depth, x: node.pos == null ? 0 : node.pos })
  if (parentId !== null) edges.push({ from: parentId, to: id })
  if (node.kind !== 'leaf') {
    collectTree(node.left, depth + 1, nodes, edges, id)
    collectTree(node.right, depth + 1, nodes, edges, id)
  }
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

function minMax(values) {
  const nums = asArray(values).map(asNumber)
  if (!nums.length) return { min: 0, max: 0 }
  let min = nums[0]
  let max = nums[0]
  for (let i = 1; i < nums.length; i++) {
    if (nums[i] < min) min = nums[i]
    if (nums[i] > max) max = nums[i]
  }
  return { min, max }
}

function colorForValue(value, min, max) {
  if (max === min) return 'hsl(218 82% 76%)'
  const t = Math.max(0, Math.min(1, (value - min) / (max - min)))
  const hue = 245 - 215 * t
  return `hsl(${hue.toFixed(1)} 82% 73%)`
}

function selectedSet(selected) {
  return new Set(asArray(selected).map((x) => asNumber(x)))
}

function angleFromDownward(dx, dy) {
  let angle = Math.atan2(dy, dx)
  angle = ((angle - Math.PI / 2 + Math.PI * 3) % (Math.PI * 2)) - Math.PI
  return Math.abs(angle)
}

function hierarchyDirectionForce(links) {
  return () => {
    for (const link of links) {
      const source = link.source
      const target = link.target
      if (!source || !target || source === target) continue
      const dx = target.x - source.x
      const dy = target.y - source.y
      const angle = angleFromDownward(dx, dy)
      const distance = Math.hypot(dx, dy) || 1
      const side = dx === 0 ? 0 : dx > 0 ? 1 : -1

      let targetAngle = Math.PI / 2
      let penalty = 0
      if (angle > HIERARCHY_EDGE_MAX_HALF_ANGLE) {
        targetAngle = side === 0 ? Math.PI / 2 : Math.PI / 2 - side * HIERARCHY_EDGE_MAX_HALF_ANGLE
        penalty = 1
      } else if (angle > HIERARCHY_EDGE_SOFT_HALF_ANGLE) {
        targetAngle = side === 0 ? Math.PI / 2 : Math.PI / 2 - side * HIERARCHY_EDGE_SOFT_HALF_ANGLE
        penalty = Math.min(1, (angle - HIERARCHY_EDGE_SOFT_HALF_ANGLE) / Math.max(1e-6, HIERARCHY_EDGE_MAX_HALF_ANGLE - HIERARCHY_EDGE_SOFT_HALF_ANGLE))
      }

      if (penalty > 0) {
        const desiredDx = Math.cos(targetAngle) * distance
        const desiredDy = Math.abs(Math.sin(targetAngle)) * distance
        const pullX = (desiredDx - dx) * HIERARCHY_EDGE_DIRECTION_STRENGTH * penalty
        const pullY = (desiredDy - dy) * HIERARCHY_EDGE_DIRECTION_STRENGTH * penalty
        source.vx -= pullX
        source.vy -= pullY
        target.vx += pullX
        target.vy += pullY
      }

      if (dy < HIERARCHY_EDGE_MIN_DY) {
        const downPull = (HIERARCHY_EDGE_MIN_DY - dy) * HIERARCHY_EDGE_DIRECTION_STRENGTH * 0.35
        source.vy -= downPull
        target.vy += downPull
      }
    }
  }
}

function Style() {
  return React.createElement('style', null, `
    .numlean-vis {
      --bg: #0d1017;
      --panel: #151b26;
      --text: #edf2fb;
      --muted: #aab6ca;
      --line: #30394a;
      --leaf: #9bd6ff;
      --node: #ffd166;
      --slice: #ffe38a;
      color: var(--text);
      background: radial-gradient(circle at 10% 0%, rgba(77, 99, 150, .42), transparent 34%), linear-gradient(180deg, #111827, var(--bg));
      border: 1px solid var(--line);
      border-radius: 16px;
      padding: 14px;
      width: 100%;
      overflow: auto;
      font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    }
    .numlean-vis * { box-sizing: border-box; }
    .numlean-vis .flow { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(280px, 100%), 1fr)); gap: 14px; align-items: start; }
    .numlean-vis .rows { display: grid; gap: 14px; }
    .numlean-vis .row { display: flex; flex-wrap: wrap; gap: 14px; align-items: start; }
    .numlean-vis .card { background: rgba(16,22,33,.72); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; padding: 12px; overflow: hidden; flex: 1 1 280px; min-width: 0; }
    .numlean-vis .flow > .card { min-width: min(220px, 100%); }
    .numlean-vis .pair { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); min-width: 0; min-height: 0; overflow: hidden; }
    .numlean-vis .pair-cell { min-width: 0; min-height: 0; overflow: hidden; display: flex; }
    .numlean-vis .pair-cell > * { width: 100%; height: 100%; min-width: 0; min-height: 0; }
    .numlean-vis .formula { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-size: 18px; font-weight: 800; color: #f4f7ff; background: rgba(255,255,255,.055); border: 1px solid rgba(255,255,255,.1); border-radius: 12px; padding: 10px 12px; margin-bottom: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%; }
    .numlean-vis .latex-card { background: rgba(16,22,33,.72); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; padding: 14px; overflow: hidden; flex: 1 1 280px; min-width: 0; min-height: 0; display: flex; flex-direction: column; }
    .numlean-vis .latex-formula { display: flex; align-items: center; justify-content: center; flex: 1 1 auto; min-height: 0; max-width: 100%; max-height: 100%; overflow: hidden; color: #f8fbff; background: linear-gradient(180deg, rgba(255,255,255,.075), rgba(255,255,255,.035)); border: 1px solid rgba(255,255,255,.12); border-radius: 12px; padding: 12px 14px; font-family: "STIX Two Math", "Cambria Math", "Latin Modern Math", Georgia, serif; font-size: 23px; line-height: 1.35; white-space: pre-wrap; }
    .numlean-vis .latex-formula.rendered { line-height: 0; }
    .numlean-vis .latex-formula mjx-container { display: flex !important; align-items: center !important; justify-content: center !important; width: 100% !important; height: 100% !important; max-width: 100% !important; max-height: 100% !important; overflow: hidden !important; margin: 0 !important; text-align: left !important; }
    .numlean-vis .latex-formula mjx-container svg { display: block; width: 100% !important; height: 100% !important; max-width: 100% !important; max-height: 100% !important; vertical-align: 0 !important; }
    .numlean-vis .latex-error { margin-top: 8px; color: #ffb4b4; font-size: 12px; }
    .numlean-vis .tree-panel { overflow: hidden; }
    .numlean-vis .tree-scale-shell { transform-origin: top left; }
    .numlean-vis svg { display: block; }
    .numlean-vis .edge { stroke: #8190aa; stroke-width: 2; opacity: .88; }
    .numlean-vis .prod { fill: var(--node); stroke: rgba(0,0,0,.38); stroke-width: 1.5; }
    .numlean-vis .leaf { fill: var(--leaf); stroke: rgba(0,0,0,.38); stroke-width: 1.5; }
    .numlean-vis text { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-weight: 900; fill: #071018; text-anchor: middle; dominant-baseline: central; }
    .numlean-vis .heat { display: grid; width: max-content; max-width: 100%; gap: 4px; }
    .numlean-vis .cell { display: flex; align-items: center; justify-content: center; border: 1px solid rgba(255,255,255,.18); color: #071018; font-weight: 800; line-height: 1; user-select: none; overflow: hidden; }
    .numlean-vis .cell.unselected { background: #242b36 !important; color: #778399; border-color: rgba(255,255,255,.08); }
    .numlean-vis .cell.selected { outline: 3px solid var(--slice); outline-offset: -3px; box-shadow: 0 0 0 1px rgba(0,0,0,.4), 0 0 15px rgba(255,227,138,.3); }
    .numlean-vis .rank-card { background: rgba(16,22,33,.72); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; padding: 12px; overflow: hidden; min-width: 0; }
    .numlean-vis .rank-shell { overflow: hidden; width: 100%; }
    .numlean-vis .rank-scale { transform-origin: top left; }
    .numlean-vis .rank-block { display: grid; gap: ${RANK_BLOCK_GAP}px; }
    .numlean-vis .rank-stamp { padding: ${RANK_GAP}px; border-radius: 10px; border: ${RANK_STAMP_BORDER}px solid rgba(244,247,255,.55); background: rgba(255,255,255,.05); box-shadow: inset 0 0 0 1px rgba(0,0,0,.18), 0 4px 14px rgba(0,0,0,.16); overflow: hidden; }
    .numlean-vis .rank-leaf { display: grid; gap: ${RANK_GAP}px; }
    .numlean-vis .rank-cell { display: flex; align-items: center; justify-content: center; border: 1px solid rgba(255,255,255,.18); color: #071018; font-weight: 850; line-height: 1; overflow: hidden; }
    .numlean-vis .panels { display: grid; grid-template-columns: minmax(0, 1.4fr) minmax(180px, .8fr); gap: 10px; align-items: start; }
    .numlean-vis .hierarchy { display: grid; grid-template-columns: minmax(0, 1fr) minmax(240px, 320px); gap: 12px; align-items: stretch; min-height: 520px; }
    .numlean-vis .hierarchy-graph { background: rgba(8,13,22,.66); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; overflow: auto; min-width: 0; }
    .numlean-vis .hierarchy-side { background: rgba(16,22,33,.82); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; padding: 12px; overflow: auto; }
    .numlean-vis .hierarchy-title { color: #f4f7ff; font-size: 14px; font-weight: 850; margin-bottom: 8px; }
    .numlean-vis .hierarchy-help { color: var(--muted); font-size: 12px; line-height: 1.35; margin-bottom: 10px; }
    .numlean-vis .hierarchy-tags { display: grid; gap: 6px; margin-bottom: 12px; padding: 8px; border-radius: 10px; background: rgba(255,255,255,.04); border: 1px solid rgba(255,255,255,.08); }
    .numlean-vis .hierarchy-tag { display: flex; align-items: center; gap: 7px; color: #dce8ff; font-size: 12px; cursor: pointer; user-select: none; }
    .numlean-vis .hierarchy-tag input { accent-color: #ffd166; }
    .numlean-vis .hierarchy-instance { width: 100%; text-align: left; border: 1px solid rgba(255,255,255,.1); border-radius: 10px; background: rgba(255,255,255,.045); color: #edf2fb; padding: 8px 9px; margin-bottom: 8px; cursor: pointer; font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-size: 12px; }
    .numlean-vis .hierarchy-instance:hover, .numlean-vis .hierarchy-instance.active { border-color: rgba(255,209,102,.8); background: rgba(255,209,102,.12); }
    .numlean-vis .hierarchy-instance.inactive { opacity: .32; filter: grayscale(1); }
    .numlean-vis .hierarchy-io { color: var(--muted); font-size: 11px; margin-top: 5px; white-space: normal; line-height: 1.35; }
    .numlean-vis .hierarchy-layout-error { margin: 10px; color: #ffb4b4; font-size: 12px; }
    .numlean-vis .hierarchy-edge-extends { stroke: #7cc7ff; stroke-width: 2.2; opacity: .82; }
    .numlean-vis .hierarchy-edge-assumes { stroke: #ffd166; stroke-width: 2; stroke-dasharray: 8 6; opacity: .72; }
    .numlean-vis .hierarchy-edge-instance { stroke: #8ff0c7; stroke-width: 2.4; opacity: .98; }
    .numlean-vis .hierarchy-edge-instance-assumption { stroke: #7cc7ff; stroke-width: 2.4; opacity: .98; }
    .numlean-vis .hierarchy-edge-instance-inactive { opacity: .16; }
    .numlean-vis .hierarchy-node.assumption rect { fill: #7cc7ff; stroke: #7cc7ff; }
    .numlean-vis .hierarchy-node.inferred rect { fill: #8ff0c7; stroke: #d9ffef; }
    .numlean-vis .hierarchy-node rect { fill: #dcecff; stroke: rgba(255,255,255,.45); stroke-width: 1.5; }
    .numlean-vis .hierarchy-node text { fill: #071018; font-size: 12px; }
    .numlean-vis .hierarchy-node.inactive { opacity: .25; filter: grayscale(1); }
    .numlean-vis .hierarchy-edge-inactive { opacity: .12; filter: grayscale(1); }
    .numlean-vis .hierarchy-node.selected rect { fill: #ffd166; stroke: #fff1b8; stroke-width: 3; }
    .numlean-vis .hierarchy-node.input rect { fill: #8ff0c7; stroke: #d9ffef; stroke-width: 3; }
    .numlean-vis .hierarchy-node.output rect { fill: #ffd166; stroke: #fff1b8; stroke-width: 3; }
    @media (max-width: 760px) { .numlean-vis .hierarchy { grid-template-columns: 1fr; } }
    @media (max-width: 760px) { .numlean-vis .pair, .numlean-vis .panels { grid-template-columns: 1fr; } }
  `)
}

function TreeSvg({ text, availableWidth }) {
  let tree
  try { tree = parseTree(text) } catch (_e) { tree = { kind: 'leaf', label: text || '•' } }
  const stats = measure(tree)
  const nodes = []
  const edges = []
  const counter = { value: 0 }
  assignPositions(tree, counter)
  collectTree(tree, 0, nodes, edges, null)
  const tokenStep = 54
  const yStep = 72
  const marginX = 36
  const marginY = 32
  const width = Math.max(220, marginX * 2 + Math.max(1, counter.value - 1) * tokenStep)
  const height = Math.max(120, marginY * 2 + stats.depth * yStep)
  const scale = Math.min(1, Math.max(0.1, (availableWidth - 4) / Math.max(1, width)))
  const byId = new Map()
  for (let i = 0; i < nodes.length; i++) byId.set(nodes[i].id, nodes[i])
  function pos(n) { return { x: marginX + n.x * tokenStep, y: marginY + n.depth * yStep } }
  return React.createElement('div', { style: { width: width * scale, height: height * scale } },
    React.createElement('div', { className: 'tree-scale-shell', style: { transform: `scale(${scale})`, width, height } },
      React.createElement('svg', { viewBox: `0 0 ${width} ${height}`, width, height },
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
              React.createElement('text', { x: p.x, y: p.y + 1, fontSize: 16 }, n.label || '•')
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

function TreeCard({ text }) {
  const [ref, width] = useElementWidth()
  const shown = displayText(text)
  return React.createElement('div', { className: 'card' },
    React.createElement('div', { className: 'formula' }, shown),
    React.createElement('div', { ref, className: 'tree-panel' }, React.createElement(TreeSvg, { text: shown, availableWidth: width }))
  )
}

function fitCell(cols, width, maxCell = 54) {
  const gap = cols > 16 ? 2 : 4
  const available = Math.max(48, width - 16)
  return { cell: Math.max(10, Math.min(maxCell, Math.floor((available - Math.max(0, cols - 1) * gap) / Math.max(1, cols)))), gap }
}

function HeatGrid({ rows, cols, values, labels, selected, dimUnselected = false }) {
  const [ref, width] = useElementWidth()
  const { cell, gap } = fitCell(cols, width)
  const { min, max } = minMax(values)
  const labelArray = asArray(labels)
  const selectedIndices = selected ? selectedSet(selected) : null
  const cells = []
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const idx = r * cols + c
      const value = asNumber(asArray(values)[idx])
      const label = labelArray[idx] == null ? String(value) : labelArray[idx]
      const isSelected = !selectedIndices || selectedIndices.has(idx)
      const cls = ['cell']
      if (selectedIndices && isSelected) cls.push('selected')
      if (selectedIndices && !isSelected && dimUnselected) cls.push('unselected')
      cells.push(React.createElement('div', {
        key: `${r},${c}`,
        className: cls.join(' '),
        style: {
          width: cell,
          height: cell,
          borderRadius: CELL_RADIUS,
          fontSize: Math.max(7, Math.min(11, cell * 0.26)),
          background: colorForValue(value, min, max)
        }
      }, label))
    }
  }
  return React.createElement('div', { ref },
    React.createElement('div', { className: 'heat', style: { gridTemplateColumns: `repeat(${cols}, ${cell}px)`, gap } }, cells)
  )
}

function LayoutCard({ item }) {
  return React.createElement('div', { className: 'card' },
    React.createElement(HeatGrid, {
      rows: asNumber(item.rows),
      cols: asNumber(item.cols),
      values: item.values,
      labels: item.labels
    })
  )
}

function parseShape(text) {
  return parseTree(displayText(text))
}

function shapeSize(node) {
  if (!node || node.kind === 'leaf') return Math.max(1, asNumber(node && node.label))
  return shapeSize(node.left) * shapeSize(node.right)
}

function isLeaf(node) {
  return !node || node.kind === 'leaf'
}

function isSimpleMatrixShape(node) {
  return isLeaf(node) || (node.kind === 'prod' && isLeaf(node.left) && isLeaf(node.right))
}

function highRankMatrix(node, orientation) {
  if (!node || node.kind === 'leaf') {
    const n = shapeSize(node)
    if (orientation === 'col') {
      return { rows: n, cols: 1, size: n, idx: Array.from({ length: n }, (_, i) => [i]) }
    }
    return { rows: 1, cols: n, size: n, idx: [Array.from({ length: n }, (_, i) => i)] }
  }
  const left = highRankMatrix(node.left, 'col')
  const right = highRankMatrix(node.right, 'row')
  const rows = left.rows * right.rows
  const cols = left.cols * right.cols
  const idx = []
  for (let lr = 0; lr < left.rows; lr++) {
    for (let rr = 0; rr < right.rows; rr++) {
      const row = []
      for (let lc = 0; lc < left.cols; lc++) {
        for (let rc = 0; rc < right.cols; rc++) {
          row.push(left.idx[lr][lc] + left.size * right.idx[rr][rc])
        }
      }
      idx.push(row)
    }
  }
  return { rows, cols, size: left.size * right.size, idx }
}

function estimateRankSize(shape, orientation, cell) {
  if (isLeaf(shape)) {
    const n = shapeSize(shape)
    if (orientation === 'col') {
      return { width: cell, height: n * cell + Math.max(0, n - 1) * RANK_GAP }
    }
    return { width: n * cell + Math.max(0, n - 1) * RANK_GAP, height: cell }
  }
  const left = highRankMatrix(shape.left, 'col')
  const right = estimateRankSize(shape.right, 'row', cell)
  const stamp = !isSimpleMatrixShape(shape)
    ? { width: right.width + 2 * (RANK_GAP + RANK_STAMP_BORDER), height: right.height + 2 * (RANK_GAP + RANK_STAMP_BORDER) }
    : right
  return {
    width: left.cols * stamp.width + Math.max(0, left.cols - 1) * RANK_BLOCK_GAP,
    height: left.rows * stamp.height + Math.max(0, left.rows - 1) * RANK_BLOCK_GAP
  }
}

function HighRankCells({ item, matrix, cell, radius }) {
  const values = asArray(item.values)
  const labels = asArray(item.labels)
  const nums = values.map(asNumber)
  const { min, max } = minMax(nums)
  const cells = []
  for (let r = 0; r < matrix.rows; r++) {
    for (let c = 0; c < matrix.cols; c++) {
      const idx = matrix.idx[r][c]
      const value = asNumber(values[idx])
      const label = labels[idx] == null ? String(value) : labels[idx]
      cells.push(React.createElement('div', {
        key: `${r},${c}`,
        className: 'rank-cell',
        style: {
          width: cell,
          height: cell,
          borderRadius: radius,
          fontSize: Math.max(6, Math.min(10, cell * 0.25)),
          background: colorForValue(value, min, max)
        }
      }, label))
    }
  }
  return React.createElement('div', {
    className: 'rank-leaf',
    style: { gridTemplateColumns: `repeat(${matrix.cols}, ${cell}px)` }
  }, cells)
}

function HighRankNode({ item, shape, orientation, index, cell, radius }) {
  if (isLeaf(shape)) {
    const matrix = highRankMatrix(shape, orientation)
    const mapped = {
      rows: matrix.rows,
      cols: matrix.cols,
      idx: matrix.idx.map((row) => row.map(index))
    }
    return React.createElement(HighRankCells, { item, matrix: mapped, cell, radius })
  }

  const left = highRankMatrix(shape.left, 'col')
  const rightSize = shapeSize(shape.right)
  const leftSize = shapeSize(shape.left)
  const stampB = !isSimpleMatrixShape(shape)
  const stamps = []
  for (let r = 0; r < left.rows; r++) {
    for (let c = 0; c < left.cols; c++) {
      const leftIdx = left.idx[r][c]
      const child = React.createElement(HighRankNode, {
        item,
        shape: shape.right,
        orientation: 'row',
        index: (rightIdx) => index(leftIdx + leftSize * rightIdx),
        cell,
        radius
      })
      stamps.push(React.createElement('div', { key: `${r},${c}`, className: stampB ? 'rank-stamp' : null },
        child
      ))
    }
  }
  return React.createElement('div', {
    className: 'rank-block',
    style: { gridTemplateColumns: `repeat(${left.cols}, max-content)` }
  }, stamps)
}

function HighRankLayoutCard({ item }) {
  const [ref, width] = useElementWidth()
  const shape = parseShape(item.shape)
  const matrix = highRankMatrix(shape, 'row')
  const cell = matrix.size > 32 ? 24 : 34
  const radius = CELL_RADIUS
  const rootSize = estimateRankSize(shape, 'row', cell)
  const rootWidth = Math.max(1, rootSize.width)
  const scale = Math.min(1, Math.max(0.12, (width - 4) / rootWidth))
  return React.createElement('div', { className: 'rank-card' },
    React.createElement('div', { ref, className: 'rank-shell' },
      React.createElement('div', { style: { width: rootSize.width * scale, height: rootSize.height * scale } },
        React.createElement('div', { className: 'rank-scale', style: { transform: `scale(${scale})`, width: rootSize.width, height: rootSize.height } },
          React.createElement(HighRankNode, {
            item,
            shape,
            orientation: 'row',
            index: (i) => i,
            cell,
            radius
          })
        )
      )
    )
  )
}

function SliceCard({ item }) {
  return React.createElement('div', { className: 'card' },
    React.createElement('div', { className: 'panels' },
      React.createElement(HeatGrid, { rows: asNumber(item.sourceRows), cols: asNumber(item.sourceCols), values: item.sourceValues, selected: item.selected, dimUnselected: true }),
      React.createElement(HeatGrid, { rows: asNumber(item.sliceRows), cols: asNumber(item.sliceCols), values: item.sliceValues, labels: item.sliceLabels })
    )
  )
}

function LaTeXCard({ source }) {
  const ref = React.useRef(null)
  const [error, setError] = React.useState(null)
  React.useEffect(() => {
    if (!ref.current) return
    let cancelled = false
    setError(null)
    ref.current.classList.remove('rendered')
    loadMathJax().then((mathjax) => mathjax.tex2svgPromise(displayStyleTex(source), { display: false })).then((node) => {
      if (cancelled || !ref.current) return
      ref.current.classList.add('rendered')
      ref.current.replaceChildren(node)
      requestAnimationFrame(() => {
        if (!cancelled) trimMathJaxSvg(ref.current)
      })
    }).catch((err) => {
      if (!cancelled) setError(err && err.message ? err.message : 'failed to render LaTeX')
    })
    return () => { cancelled = true }
  }, [source])
  return React.createElement('div', { className: 'latex-card' },
    React.createElement('div', { ref, className: 'latex-formula' }, source || ''),
    error ? React.createElement('div', { className: 'latex-error' }, error) : null
  )
}

function Row({ items }) {
  return React.createElement('div', { className: 'row' }, asArray(items).map((item, i) => React.createElement(Item, { key: i, item })))
}

function nameText(value) {
  if (typeof value === 'string') return value
  if (value && typeof value === 'object') {
    if (typeof value.name === 'string') return value.name
    if (typeof value.fullName === 'string') return value.fullName
  }
  return String(value == null ? '' : value)
}

function shortName(value) {
  const text = nameText(value)
  const parts = text.split('.')
  return parts[parts.length - 1] || text
}

function hierarchyInitialLayout(nodes, edges, width, height) {
  const ids = nodes.map((n) => nameText(n.name))
  const indeg = new Map(ids.map((id) => [id, 0]))
  const out = new Map(ids.map((id) => [id, []]))
  for (const edge of edges) {
    const source = nameText(edge.source)
    const target = nameText(edge.target)
    if (!indeg.has(source) || !indeg.has(target)) continue
    indeg.set(target, indeg.get(target) + 1)
    out.get(source).push(target)
  }
  const depth = new Map(ids.map((id) => [id, 0]))
  const queue = ids.filter((id) => indeg.get(id) === 0)
  for (let i = 0; i < queue.length; i++) {
    const id = queue[i]
    for (const target of out.get(id) || []) {
      depth.set(target, Math.max(depth.get(target), depth.get(id) + 1))
      indeg.set(target, indeg.get(target) - 1)
      if (indeg.get(target) === 0) queue.push(target)
    }
  }
  const layers = new Map()
  for (const id of ids) {
    const d = depth.get(id) || 0
    if (!layers.has(d)) layers.set(d, [])
    layers.get(d).push(id)
  }
  const maxDepth = Math.max(0, ...Array.from(layers.keys()))
  const pos = new Map()
  for (const [d, layer] of layers.entries()) {
    layer.sort((a, b) => shortName(a).localeCompare(shortName(b)))
    for (let i = 0; i < layer.length; i++) {
      pos.set(layer[i], {
        x: 100 + (width - 200) * ((i + 1) / (layer.length + 1)),
        y: 80 + (height - 160) * (maxDepth === 0 ? 0.5 : d / maxDepth)
      })
    }
  }
  return pos
}

function itemTags(item) {
  const tags = asArray(item && item.tags).map(nameText).filter(Boolean)
  if (!tags.length && item && item.tag != null) tags.push(nameText(item.tag))
  return tags
}

function tagList(nodes, instances) {
  const seen = new Set()
  for (const item of [...nodes, ...instances]) {
    for (const tag of itemTags(item)) seen.add(tag)
  }
  return Array.from(seen).sort()
}

function itemActive(item, activeTags) {
  const tags = itemTags(item)
  return tags.length === 0 || tags.some((tag) => activeTags.has(tag))
}

function effectiveNodeTags(nodes, _edges, instances) {
  const tagsById = new Map(nodes.map((node) => [nameText(node.name), new Set(itemTags(node))]))
  function addTags(id, tags) {
    if (!tagsById.has(id)) tagsById.set(id, new Set())
    const target = tagsById.get(id)
    for (const tag of tags) target.add(tag)
  }
  for (const inst of instances) {
    const tags = itemTags(inst)
    addTags(nameText(inst.output), tags)
  }
  return tagsById
}

function tagsActive(tags, activeTags) {
  return !tags || tags.size === 0 || Array.from(tags).some((tag) => activeTags.has(tag))
}

function useHierarchyForceLayout(nodes, edges, width, height) {
  const [positions, setPositions] = React.useState(new Map())
  const [error, setError] = React.useState(null)
  const simulationRef = React.useRef(null)
  const nodeByIdRef = React.useRef(new Map())

  const setNodePosition = React.useCallback((id, x, y, pin = true) => {
    const node = nodeByIdRef.current.get(id)
    if (!node) return
    node.x = x
    node.y = y
    node.vx = 0
    node.vy = 0
    if (pin) {
      node.fx = x
      node.fy = y
    } else {
      node.fx = null
      node.fy = null
    }
    if (simulationRef.current) simulationRef.current.alpha(0.28).restart()
    setPositions((old) => {
      const next = new Map(old)
      next.set(id, { x, y })
      return next
    })
  }, [])

  const releaseNode = React.useCallback((id) => {
    const node = nodeByIdRef.current.get(id)
    if (!node) return
    node.fx = null
    node.fy = null
    if (simulationRef.current) simulationRef.current.alpha(0.12).alphaTarget(0)
  }, [])

  React.useEffect(() => {
    let cancelled = false
    let simulation = null
    simulationRef.current = null
    setError(null)
    loadD3().then((d3) => {
      if (cancelled) return
      const initial = hierarchyInitialLayout(nodes, edges, width, height)
      const simNodes = nodes.map((node) => {
        const id = nameText(node.name)
        const p = initial.get(id) || { x: width / 2, y: height / 2 }
        return { id, x: p.x, y: p.y, label: node.label || shortName(id) }
      })
      const nodeIds = new Set(simNodes.map((node) => node.id))
      nodeByIdRef.current = new Map(simNodes.map((node) => [node.id, node]))
      const links = edges.map((edge) => ({
        source: nameText(edge.source),
        target: nameText(edge.target),
        kind: edge.kind === 'extends' || edge.kind && edge.kind.extends != null ? 'extends' : 'assumes'
      })).filter((edge) => nodeIds.has(edge.source) && nodeIds.has(edge.target))
      simulation = d3.forceSimulation(simNodes)
        .force('link', d3.forceLink(links).id((d) => d.id).distance((d) => d.kind === 'extends' ? 150 : 115).strength((d) => d.kind === 'extends' ? 0.72 : 0.38))
        .force('direction', hierarchyDirectionForce(links))
        .force('charge', d3.forceManyBody().strength(-620))
        .force('x', d3.forceX((d) => (initial.get(d.id) || { x: width / 2 }).x).strength(0.06))
        .force('y', d3.forceY((d) => (initial.get(d.id) || { y: height / 2 }).y).strength(0.18))
        .force('collision', d3.forceCollide(88).strength(0.9))
        .alpha(1)
        .alphaDecay(0.045)
      simulationRef.current = simulation
      let tick = 0
      simulation.on('tick', () => {
        tick += 1
        if (cancelled || tick % 2 !== 0) return
        setPositions(new Map(simNodes.map((node) => [node.id, { x: node.x, y: node.y }])))
      })
      simulation.on('end', () => {
        if (!cancelled) setPositions(new Map(simNodes.map((node) => [node.id, { x: node.x, y: node.y }])))
      })
      }).catch((err) => {
      if (!cancelled) {
        setError(err && err.message ? err.message : 'failed to load D3')
        setPositions(hierarchyInitialLayout(nodes, edges, width, height))
        nodeByIdRef.current = new Map()
      }
    })
    return () => {
      cancelled = true
      if (simulation) simulation.stop()
      simulationRef.current = null
    }
  }, [nodes, edges, width, height])
  return { positions, error, setNodePosition, releaseNode, simulationRef, nodeByIdRef }
}

function nodeBoundaryPoint(from, to) {
  const halfW = 70
  const halfH = 20
  const dx = to.x - from.x
  const dy = to.y - from.y
  if (dx === 0 && dy === 0) return { x: from.x, y: from.y }
  const scale = Math.min(Math.abs(halfW / (dx || 1e-6)), Math.abs(halfH / (dy || 1e-6)))
  return { x: from.x + dx * scale, y: from.y + dy * scale }
}

function HierarchyGraphCard({ item }) {
  const nodes = asArray(item.classes)
  const edges = asArray(item.classEdges)
  const instances = asArray(item.instances)
  const tags = React.useMemo(() => tagList(nodes, instances), [nodes, instances])
  const [enabledTags, setEnabledTags] = React.useState(() => new Set(tags))
  const [selectedClass, setSelectedClass] = React.useState(nodes[0] ? nameText(nodes[0].name) : null)
  const [selectedInstance, setSelectedInstance] = React.useState(null)
  const [view, setView] = React.useState({ scale: 1, x: 0, y: 0 })
  const graphRef = React.useRef(null)
  const dragRef = React.useRef(null)
  const ignoreNodeClickRef = React.useRef(false)
  const width = Math.max(900, 170 * Math.ceil(Math.sqrt(Math.max(1, nodes.length))) + 260)
  const height = Math.max(560, 120 * Math.ceil(Math.sqrt(Math.max(1, nodes.length))) + 220)
  const { positions, error: layoutError, setNodePosition, releaseNode } = useHierarchyForceLayout(nodes, edges, width, height)
  const nodeTags = React.useMemo(() => effectiveNodeTags(nodes, edges, instances), [nodes, edges, instances])
  const inferredByInstances = React.useMemo(() => instances.filter((inst) => nameText(inst.output) === selectedClass), [instances, selectedClass])
  const inferableFromSelected = React.useMemo(() => {
    if (!selectedClass) return []
    return instances.filter((inst) => asArray(inst.inputs).map(nameText).includes(selectedClass))
  }, [instances, selectedClass])
  const inferableInstances = React.useMemo(() => {
    const blocked = new Set(inferredByInstances.map((inst) => nameText(inst.name)))
    return inferableFromSelected.filter((inst) => !blocked.has(nameText(inst.name)))
  }, [inferredByInstances, inferableFromSelected])
  const activeInstance = selectedInstance == null ? null : instances.find((inst) => nameText(inst.name) === selectedInstance)
  const activeInstanceInputs = React.useMemo(() => activeInstance ? asArray(activeInstance.inputs).map(nameText) : [], [activeInstance])
  const activeInstanceInputSet = React.useMemo(() => new Set(activeInstanceInputs), [activeInstanceInputs])
  const output = activeInstance ? nameText(activeInstance.output) : null
  const selectedInstanceMode = React.useMemo(() => {
    if (!activeInstance || !selectedClass) return null
    if (output === selectedClass) return 'inferredBy'
    if (activeInstanceInputSet.has(selectedClass)) return 'canInfer'
    return null
  }, [activeInstance, selectedClass, output, activeInstanceInputSet])
  const selectedInstanceEdges = React.useMemo(() => {
    if (!activeInstance || !selectedInstanceMode) return []
    const out = output
    if (!out) return []
    return activeInstanceInputs.map((input) => ({
      source: nameText(input),
      target: out,
      mode: selectedInstanceMode === 'canInfer'
        ? (selectedClass === nameText(input) ? 'canInfer' : 'assumption')
        : 'instance'
    })).filter((edge) => edge.source && edge.target)
  }, [activeInstanceInputs, output, selectedClass, selectedInstanceMode])
  function resolveNodeClick(id) {
    if (ignoreNodeClickRef.current) {
      ignoreNodeClickRef.current = false
      return
    }
    selectClass(id)
  }
  function selectClass(id) {
    setSelectedClass(id)
    setSelectedInstance(null)
  }
  React.useEffect(() => {
    setEnabledTags((old) => {
      const next = new Set()
      for (const tag of tags) {
        if (old.size === 0 || old.has(tag)) next.add(tag)
      }
      return next.size === 0 && tags.length > 0 ? new Set(tags) : next
    })
  }, [tags])
  function toggleTag(tag) {
    setEnabledTags((old) => {
      const next = new Set(old)
      if (next.has(tag)) next.delete(tag)
      else next.add(tag)
      return next
    })
  }
  function graphPoint(event) {
    const graph = graphRef.current || event.currentTarget
    const rect = graph && graph.getBoundingClientRect ? graph.getBoundingClientRect() : { left: 0, top: 0 }
    return { x: event.clientX - rect.left, y: event.clientY - rect.top }
  }
  function onWheel(event) {
    event.preventDefault()
    const point = graphPoint(event)
    setView((old) => {
      const factor = Math.exp(-event.deltaY * 0.001)
      const scale = Math.max(0.25, Math.min(3.5, old.scale * factor))
      const worldX = (point.x - old.x) / old.scale
      const worldY = (point.y - old.y) / old.scale
      return { scale, x: point.x - worldX * scale, y: point.y - worldY * scale }
    })
  }
  function toWorld(event, viewState) {
    const point = graphPoint(event)
    return {
      x: (point.x - viewState.x) / viewState.scale,
      y: (point.y - viewState.y) / viewState.scale
    }
  }
  function onPointerDown(event) {
    if (event.target && event.target.closest && event.target.closest('.hierarchy-node')) return
    if (event.button !== 0 && event.button !== 1 && event.button !== 2) return
    event.preventDefault()
    event.currentTarget.setPointerCapture(event.pointerId)
    const point = graphPoint(event)
    dragRef.current = {
      pointerId: event.pointerId,
      mode: event.button === 2 ? 'zoom' : 'pan',
      startX: event.clientX,
      startY: event.clientY,
      anchorX: point.x,
      anchorY: point.y,
      view,
      moved: false
    }
  }
  function onPointerMove(event) {
    const drag = dragRef.current
    if (!drag || drag.pointerId !== event.pointerId) return
    if (drag.mode === 'node') {
      const world = toWorld(event, drag.view)
      const nodeId = drag.nodeId
      if (nodeId) {
        const dx = event.clientX - drag.startX
        const dy = event.clientY - drag.startY
        if (drag.moved || Math.abs(dx) + Math.abs(dy) > 3) {
          drag.moved = true
          const offsetX = drag.offsetX || 0
          const offsetY = drag.offsetY || 0
          setNodePosition(nodeId, world.x - offsetX, world.y - offsetY, true)
        }
      }
      return
    }
    const dx = event.clientX - drag.startX
    const dy = event.clientY - drag.startY
    if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true
    if (drag.mode === 'zoom') {
      const scale = Math.max(0.25, Math.min(3.5, drag.view.scale * Math.exp(-dy * 0.008)))
      const worldX = (drag.anchorX - drag.view.x) / drag.view.scale
      const worldY = (drag.anchorY - drag.view.y) / drag.view.scale
      setView({ scale, x: drag.anchorX - worldX * scale, y: drag.anchorY - worldY * scale })
    } else {
      setView({ ...drag.view, x: drag.view.x + dx, y: drag.view.y + dy })
    }
  }
  function onPointerUp(event) {
    const drag = dragRef.current
    if (drag && drag.pointerId === event.pointerId) {
      if (drag.mode === 'node') {
        if (drag.nodeId) releaseNode(drag.nodeId)
        if (drag.moved) ignoreNodeClickRef.current = true
      }
      dragRef.current = null
      try { event.currentTarget.releasePointerCapture(event.pointerId) } catch (_e) {}
    }
  }
  function onNodePointerDown(event, nodeId) {
    if (event.button !== 0) return
    event.preventDefault()
    event.stopPropagation()
    ignoreNodeClickRef.current = false
    event.currentTarget.setPointerCapture(event.pointerId)
    const world = toWorld(event, view)
    const start = positions.get(nodeId)
    const offsetX = start ? world.x - start.x : 0
    const offsetY = start ? world.y - start.y : 0
    dragRef.current = {
      pointerId: event.pointerId,
      mode: 'node',
      nodeId,
      startX: event.clientX,
      startY: event.clientY,
      view,
      offsetX,
      offsetY,
      moved: false
    }
  }
  function resetView() {
    setView({ scale: 1, x: 0, y: 0 })
  }
  return React.createElement('div', { className: 'hierarchy' },
    React.createElement('div', { className: 'hierarchy-graph' },
      layoutError ? React.createElement('div', { className: 'hierarchy-layout-error' }, layoutError) : null,
      React.createElement('svg', {
        width,
        height,
        viewBox: `0 0 ${width} ${height}`,
        onWheel,
        ref: graphRef,
        onPointerDown,
        onPointerMove,
        onPointerUp,
        onPointerCancel: onPointerUp,
        onContextMenu: (event) => event.preventDefault(),
        onDoubleClick: resetView,
        style: { touchAction: 'none', cursor: dragRef.current ? 'grabbing' : 'grab' }
      },
        React.createElement('defs', null,
          React.createElement('marker', { id: 'hierarchy-arrow', markerWidth: 10, markerHeight: 10, refX: 9, refY: 3, orient: 'auto', markerUnits: 'strokeWidth' },
            React.createElement('path', { d: 'M0,0 L0,6 L9,3 z', fill: '#dbeafe' })
          ),
          React.createElement('marker', { id: 'hierarchy-arrow-instance', markerWidth: 10, markerHeight: 10, refX: 9, refY: 3, orient: 'auto', markerUnits: 'strokeWidth' },
            React.createElement('path', { d: 'M0,0 L0,6 L9,3 z', fill: '#8ff0c7' })
          ),
          React.createElement('marker', { id: 'hierarchy-arrow-instance-assumption', markerWidth: 10, markerHeight: 10, refX: 9, refY: 3, orient: 'auto', markerUnits: 'strokeWidth' },
            React.createElement('path', { d: 'M0,0 L0,6 L9,3 z', fill: '#7cc7ff' })
          )
        ),
        React.createElement('rect', { x: 0, y: 0, width, height, fill: 'transparent' }),
        React.createElement('g', { transform: `translate(${view.x} ${view.y}) scale(${view.scale})` },
          edges.map((edge, i) => {
            const sourceId = nameText(edge.source)
            const targetId = nameText(edge.target)
            const source = positions.get(sourceId)
            const target = positions.get(targetId)
            if (!source || !target) return null
            const kind = edge.kind === 'extends' || edge.kind && edge.kind.extends != null ? 'extends' : 'assumes'
            const start = nodeBoundaryPoint(source, target)
            const end = nodeBoundaryPoint(target, source)
            const active = tagsActive(nodeTags.get(sourceId), enabledTags) && tagsActive(nodeTags.get(targetId), enabledTags)
            return React.createElement('line', { key: i, className: `hierarchy-edge-${kind}${active ? '' : ' hierarchy-edge-inactive'}`, x1: start.x, y1: start.y, x2: end.x, y2: end.y, markerEnd: 'url(#hierarchy-arrow)' })
          }),
          selectedInstanceEdges.length === 0 ? null : selectedInstanceEdges.map((edge, i) => {
            const source = positions.get(edge.source)
            const target = positions.get(edge.target)
            if (!source || !target) return null
            const start = nodeBoundaryPoint(source, target)
            const end = nodeBoundaryPoint(target, source)
            const active = tagsActive(nodeTags.get(edge.source), enabledTags) && tagsActive(nodeTags.get(edge.target), enabledTags)
            const edgeClass = edge.mode === 'assumption' ? 'hierarchy-edge-instance-assumption' : 'hierarchy-edge-instance'
            const edgeMarker = edge.mode === 'assumption' ? 'url(#hierarchy-arrow-instance-assumption)' : 'url(#hierarchy-arrow-instance)'
            return React.createElement('line', {
              key: `instance-edge-${i}-${edge.source}-${edge.target}`,
              className: `${edgeClass}${active ? '' : ' hierarchy-edge-instance-inactive'}`,
              x1: start.x,
              y1: start.y,
              x2: end.x,
              y2: end.y,
              markerEnd: edgeMarker
            })
          }),
          nodes.map((node) => {
            const id = nameText(node.name)
            const p = positions.get(id) || { x: width / 2, y: height / 2 }
            const cls = ['hierarchy-node']
            if (id === selectedClass) cls.push('selected')
            if (selectedInstanceMode === 'canInfer') {
              if (id === output) cls.push('inferred')
              if (activeInstanceInputSet.has(id) && id !== selectedClass) cls.push('assumption')
            } else if (activeInstanceInputSet.has(id)) {
              cls.push('input')
            } else if (output === id) {
              cls.push('output')
            }
            if (!tagsActive(nodeTags.get(id), enabledTags)) cls.push('inactive')
            return React.createElement('g', { key: id, className: cls.join(' '), transform: `translate(${p.x - 70}, ${p.y - 20})`, onPointerDown: (event) => onNodePointerDown(event, id), onClick: () => resolveNodeClick(id), style: { cursor: 'pointer' } },
              React.createElement('rect', { width: 140, height: 40, rx: 11 }),
              React.createElement('text', { x: 70, y: 21 }, node.label || shortName(id))
            )
          })
        )
      )
    ),
    React.createElement('div', { className: 'hierarchy-side' },
      React.createElement('div', { className: 'hierarchy-title' }, selectedClass ? shortName(selectedClass) : 'Hierarchy graph'),
      tags.length ? React.createElement('div', { className: 'hierarchy-tags' },
        tags.map((tag) => React.createElement('label', { key: tag, className: 'hierarchy-tag' },
          React.createElement('input', { type: 'checkbox', checked: enabledTags.has(tag), onChange: () => toggleTag(tag) }),
          tag
        ))
      ) : null,
      React.createElement('div', { className: 'hierarchy-help' }, selectedClass
        ? 'Green: inferred class. Light blue: parallel assumptions. Click one to highlight connections.'
        : 'Click a class node to list instances.'
      ),
      React.createElement('div', { className: 'hierarchy-help' }, inferredByInstances.length === 0 ? 'No marked instances infer this class.' : 'Instances that directly infer this class:'),
      inferredByInstances.length === 0 ? null : inferredByInstances.map((inst) => {
        const id = nameText(inst.name)
        const active = selectedInstance === id
        const enabled = itemActive(inst, enabledTags)
        return React.createElement('button', { key: id, className: `hierarchy-instance${active ? ' active' : ''}${enabled ? '' : ' inactive'}`, onClick: () => setSelectedInstance(active ? null : id) },
          inst.label || shortName(id),
          React.createElement('div', { className: 'hierarchy-io' }, `${asArray(inst.inputs).map(shortName).join(', ') || '∅'} ⇒ ${shortName(inst.output)}`)
        )
      }),
      React.createElement('div', { className: 'hierarchy-help' }, inferableInstances.length === 0 ? 'No marked instances can be inferred by this class.' : 'Instances this class can infer:'),
      inferableInstances.length === 0 ? null : inferableInstances.map((inst) => {
        const id = nameText(inst.name)
        const active = selectedInstance === id
        const enabled = itemActive(inst, enabledTags)
        return React.createElement('button', { key: id, className: `hierarchy-instance${active ? ' active' : ''}${enabled ? '' : ' inactive'}`, onClick: () => setSelectedInstance(active ? null : id) },
          inst.label || shortName(id),
          React.createElement('div', { className: 'hierarchy-io' }, `${asArray(inst.inputs).map(shortName).join(', ') || '∅'} ⇒ ${shortName(inst.output)}`)
        )
      })
    )
  )
}

function ratioPair(value, fallbackA = 1, fallbackB = 1) {
  const xs = asArray(value)
  const a = Math.max(1, asNumber(xs[0] == null ? fallbackA : xs[0]))
  const b = Math.max(1, asNumber(xs[1] == null ? fallbackB : xs[1]))
  return [a, b]
}

function itemKind(item) {
  if (!item || typeof item !== 'object') return null
  if (item.kind) return item.kind
  if (item.profile != null) return 'profile'
  if (item.source != null) return 'latex'
  if (item.sourceRows != null || item.sourceValues != null || item.selected != null) return 'slice'
  if (item.items != null) return 'flow'
  if (item.left != null && item.right != null) return 'prod'
  if (item.classes != null && item.classEdges != null && item.instances != null) return 'hierarchyGraph'
  if (item.rows != null && item.cols == null) return 'grid'
  if (item.tree != null) return 'shape'
  if (item.shape != null && item.values != null) return 'highRankLayout'
  if (item.shape != null) return 'shape'
  if (item.rows != null && item.cols != null && item.values != null) return 'layout'
  return null
}

function Item({ item }) {
  if (!item || typeof item !== 'object') return React.createElement(TreeCard, { text: String(item) })
  const kind = itemKind(item)
  if (kind === 'profile') return React.createElement(TreeCard, { text: item.profile })
  if (kind === 'shape') return React.createElement(TreeCard, { text: item.tree || item.shape })
  if (kind === 'layout') return React.createElement(LayoutCard, { item })
  if (kind === 'latex') return React.createElement(LaTeXCard, { source: item.source })
  if (kind === 'highRankLayout') return React.createElement(HighRankLayoutCard, { item })
  if (kind === 'slice') return React.createElement(SliceCard, { item })
  if (kind === 'hierarchyGraph') return React.createElement(HierarchyGraphCard, { item })
  if (kind === 'prod') {
    const options = item.options || {}
    const direction = item.direction || options.direction || 'horizontal'
    const weights = ratioPair(item.weights || options.weights, 1, 1)
    const aspectRatio = item.aspectRatio || options.aspectRatio
    const aspect = aspectRatio ? ratioPair(aspectRatio, 1, 1) : null
    const style = {
      gap: asNumber(item.gap || options.gap || 10),
      alignItems: item.alignItems || options.alignItems || 'start',
      justifyItems: item.justifyItems || options.justifyItems || 'stretch',
      gridTemplateColumns: direction === 'vertical' ? '1fr' : `${weights[0]}fr ${weights[1]}fr`,
      gridTemplateRows: direction === 'vertical' ? `${weights[0]}fr ${weights[1]}fr` : undefined,
      aspectRatio: aspect ? `${aspect[0]} / ${aspect[1]}` : undefined
    }
    return React.createElement('div', { className: 'card' },
      React.createElement('div', { className: 'pair', style },
        React.createElement('div', { className: 'pair-cell' }, React.createElement(Item, { item: item.left })),
        React.createElement('div', { className: 'pair-cell' }, React.createElement(Item, { item: item.right }))
      )
    )
  }
  if (kind === 'flow') {
    return React.createElement('div', { className: 'flow' }, asArray(item.items).map((child, i) => React.createElement(Item, { key: i, item: child })))
  }
  if (kind === 'grid') {
    return React.createElement('div', { className: 'rows' }, asArray(item.rows).map((row, i) => React.createElement(Row, { key: i, items: row })))
  }
  return React.createElement(TreeCard, { text: JSON.stringify(item) })
}

function visualPayload(props) {
  if (props && typeof props === 'object' && props.pos && props.props && typeof props.props === 'object') {
    return props.props
  }
  return props
}

export default function Visualize(props) {
  return React.createElement('div', { className: 'numlean-vis', 'data-version': VERSION },
    React.createElement(Style),
    React.createElement(Item, { item: visualPayload(props) })
  )
}
