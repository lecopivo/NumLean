import * as React from 'react'

const VERSION = 'numlean-visualize-v17'
const RANK_GAP = 3
const RANK_BLOCK_GAP = 7
const RANK_STAMP_BORDER = 2
const CELL_RADIUS = 4

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
    .numlean-vis .pair > .card { min-width: 0; padding: 8px; }
    .numlean-vis .pair { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); }
    .numlean-vis .formula { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace; font-size: 18px; font-weight: 800; color: #f4f7ff; background: rgba(255,255,255,.055); border: 1px solid rgba(255,255,255,.1); border-radius: 12px; padding: 10px 12px; margin-bottom: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%; }
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

function Row({ items }) {
  return React.createElement('div', { className: 'row' }, asArray(items).map((item, i) => React.createElement(Item, { key: i, item })))
}

function Item({ item }) {
  if (!item || typeof item !== 'object') return React.createElement(TreeCard, { text: String(item) })
  if (item.kind === 'profile') return React.createElement(TreeCard, { text: item.profile })
  if (item.kind === 'shape') return React.createElement(TreeCard, { text: item.shape })
  if (item.kind === 'layout') return React.createElement(LayoutCard, { item })
  if (item.kind === 'highRankLayout') return React.createElement(HighRankLayoutCard, { item })
  if (item.kind === 'slice') return React.createElement(SliceCard, { item })
  if (item.kind === 'prod') {
    const style = {
      gap: asNumber(item.gap || 10),
      alignItems: item.alignItems || 'start',
      justifyItems: item.justifyItems || 'stretch'
    }
    return React.createElement('div', { className: 'card' },
      React.createElement('div', { className: 'pair', style },
        React.createElement(Item, { item: item.left }),
        React.createElement(Item, { item: item.right })
      )
    )
  }
  if (item.kind === 'flow') {
    return React.createElement('div', { className: 'flow' }, asArray(item.items).map((child, i) => React.createElement(Item, { key: i, item: child })))
  }
  if (item.kind === 'grid') {
    return React.createElement('div', { className: 'rows' }, asArray(item.rows).map((row, i) => React.createElement(Row, { key: i, items: row })))
  }
  return React.createElement(TreeCard, { text: JSON.stringify(item) })
}

export default function Visualize(props) {
  return React.createElement('div', { className: 'numlean-vis', 'data-version': VERSION },
    React.createElement(Style),
    React.createElement(Item, { item: props })
  )
}
