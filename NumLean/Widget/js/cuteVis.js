import * as React from 'react'

const VERSION = 'cute-vis-v7'

function asNumber(x) {
  if (typeof x === 'bigint') return Number(x)
  return Number(x == null ? 0 : x)
}

function asArray(xs) {
  return Array.isArray(xs) ? xs : []
}

function valueAt(values, cols, r, c) {
  return asNumber(values[r * cols + c])
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

function cellKey(r, c) { return `${r},${c}` }

function selectedSet(selected) {
  return new Set(asArray(selected).map((x) => asNumber(x)))
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

function fitCell(rows, cols, width, maxCell = 54) {
  const gap = cols > 16 ? 2 : 4
  const available = Math.max(160, width - 32)
  const cell = Math.max(18, Math.min(maxCell, Math.floor((available - Math.max(0, cols - 1) * gap) / Math.max(1, cols))))
  return { cell, gap }
}

function Style() {
  return React.createElement('style', null, `
    .cute-vis {
      --bg: #0d1017;
      --panel: #151b26;
      --panel2: #101621;
      --text: #edf2fb;
      --muted: #aab6ca;
      --line: #30394a;
      --accent: #9bc2ff;
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
    .cute-vis * { box-sizing: border-box; }
    .cute-vis .grid { display: grid; width: max-content; gap: 4px; }
    .cute-vis .cell {
      display: flex;
      align-items: center;
      justify-content: center;
      border-radius: 9px;
      border: 1px solid rgba(255,255,255,.18);
      color: #071018;
      font-weight: 800;
      font-size: 11px;
      line-height: 1;
      position: relative;
      user-select: none;
      transition: transform .12s ease, box-shadow .12s ease;
    }
    .cute-vis .cell:hover { transform: translateY(-1px); box-shadow: 0 5px 18px rgba(0,0,0,.25); z-index: 2; }
    .cute-vis .cell.unselected { background: #242b36 !important; color: #778399; border-color: rgba(255,255,255,.08); }
    .cute-vis .cell.selected { outline: 3px solid var(--slice); outline-offset: -3px; box-shadow: 0 0 0 1px rgba(0,0,0,.4), 0 0 15px rgba(255,227,138,.3); }
    .cute-vis .cell.highlight { box-shadow: 0 0 0 2px #fff, 0 0 16px rgba(255,255,255,.35); z-index: 5; }
    .cute-vis .panels { display: grid; grid-template-columns: minmax(0, 1.4fr) minmax(260px, .8fr); gap: 14px; align-items: start; }
    .cute-vis .panel { background: rgba(16,22,33,.72); border: 1px solid rgba(255,255,255,.08); border-radius: 13px; padding: 12px; overflow: auto; }
    .cute-vis .vis-grid { display: grid; gap: 14px; }
    .cute-vis .vis-row { display: flex; flex-wrap: wrap; gap: 14px; align-items: start; }
    .cute-vis .vis-card { flex: 1 1 340px; min-width: 260px; }
    @media (max-width: 760px) { .cute-vis .panels { grid-template-columns: 1fr; } }
  `)
}

function HeatGrid({ rows, cols, values, labels, selected, highlight, setHighlight, dimUnselected = false }) {
  const { min, max } = minMax(values)
  const [ref, width] = useElementWidth()
  const { cell, gap } = fitCell(rows, cols, width)
  const selectedIndices = selected ? selectedSet(selected) : null
  const cells = []
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const idx = r * cols + c
      const v = valueAt(values, cols, r, c)
      const labelArray = asArray(labels)
      const label = labelArray[idx] == null ? String(v) : labelArray[idx]
      const isSelected = !selectedIndices || selectedIndices.has(idx)
      const cls = ['cell']
      if (selectedIndices && isSelected) cls.push('selected')
      if (selectedIndices && !isSelected && dimUnselected) cls.push('unselected')
      if (highlight === idx) cls.push('highlight')
      cells.push(React.createElement('div', {
        key: cellKey(r, c),
        className: cls.join(' '),
        style: { width: cell, height: cell, background: colorForValue(v, min, max) },
        onMouseEnter: () => { if (setHighlight) setHighlight(idx) },
        onMouseLeave: () => { if (setHighlight) setHighlight(null) }
      }, label))
    }
  }
  return React.createElement('div', { ref },
    React.createElement('div', { className: 'grid', style: { gridTemplateColumns: `repeat(${cols}, ${cell}px)`, gap } }, cells)
  )
}

function LayoutItem(props) {
  const rows = asNumber(props.rows)
  const cols = asNumber(props.cols)
  const [highlight, setHighlight] = React.useState(null)
  return React.createElement('div', { className: 'vis-card' },
    React.createElement('div', { className: 'panel' },
      React.createElement(HeatGrid, {
        rows,
        cols,
        values: props.values,
        labels: props.labels,
        highlight,
        setHighlight
      })
    )
  )
}

function SliceItem(props) {
  const [highlight, setHighlight] = React.useState(null)
  const sourceRows = asNumber(props.sourceRows)
  const sourceCols = asNumber(props.sourceCols)
  const sliceRows = asNumber(props.sliceRows)
  const sliceCols = asNumber(props.sliceCols)
  return React.createElement('div', { className: 'vis-card' },
    React.createElement('div', { className: 'panels' },
      React.createElement('section', { className: 'panel' },
        React.createElement(HeatGrid, {
          rows: sourceRows,
          cols: sourceCols,
          values: props.sourceValues,
          selected: props.selected,
          highlight,
          setHighlight,
          dimUnselected: true
        })
      ),
      React.createElement('section', { className: 'panel' },
        React.createElement(HeatGrid, {
          rows: sliceRows,
          cols: sliceCols,
          values: props.sliceValues,
          labels: props.sliceLabels,
          highlight: null,
          setHighlight: null
        })
      )
    )
  )
}

function ItemView(props) {
  if (Object.prototype.hasOwnProperty.call(props, 'sourceValues')) {
    return React.createElement(SliceItem, props)
  }
  return React.createElement(LayoutItem, props)
}

function asGridRows(props) {
  if (Array.isArray(props.rows)) {
    return props.rows.map((row) => Array.isArray(row) ? row : [])
  }
  return [[props]]
}

export default function CuteVis(props) {
  const rows = asGridRows(props)
  return React.createElement('div', { className: 'cute-vis', 'data-version': VERSION },
    React.createElement(Style),
    React.createElement('div', { className: 'vis-grid' },
      rows.map((row, r) => React.createElement('div', { key: `r${r}`, className: 'vis-row' },
        row.map((item, c) => React.createElement(ItemView, Object.assign({ key: `c${c}` }, item)))
      ))
    )
  )
}
