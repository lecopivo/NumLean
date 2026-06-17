import * as React from 'react'

const WIDGET_VERSION = 'layout-vis-no-title-v15'

const idxKey = (idx) => idx.join(',')
const cellKey = (r, c) => `${r},${c}`
const idxLabel = (idx) => `(${idx.join(',')})`

const colorModeLabels = {
  source: 'source',
  linear: 'linear memory',
  target: 'target'
}

function linearHue(value, valueMax) {
  if (valueMax <= 1) return 220
  const t = Math.max(0, Math.min(1, value / (valueMax - 1)))
  return 245 - 215 * t
}

function linearHueFromOffset(off, memorySize) {
  if (memorySize <= 1) return 220
  const t = Math.max(0, Math.min(1, off / (memorySize - 1)))
  return 245 - 215 * t
}

function colorForOffset(off, memorySize) {
  if (off < 0 || off >= memorySize) return '#4a2b34'
  return `hsl(${linearHueFromOffset(off, memorySize).toFixed(1)} 82% 72%)`
}

function colorForOrdinal(value, total) {
  if (total <= 1) return 'hsl(220 82% 72%)'
  const hue = linearHue(value, total)
  return `hsl(${hue.toFixed(1)} 82% 72%)`
}

function colorFromList(values) {
  const palette = [...new Set(values)]
  if (!palette.length) return null
  if (palette.length === 1) return palette[0]
  const step = 100 / palette.length
  const stops = palette.map((c, idx) => {
    const a = (idx * step).toFixed(2)
    const b = ((idx + 1) * step).toFixed(2)
    return `${c} ${a}% ${b}%`
  })
  return `conic-gradient(from -90deg, ${stops.join(', ')})`
}

function allIndices(shape) {
  const out = []
  function rec(prefix, dim) {
    if (dim === shape.length) {
      out.push(prefix)
      return
    }
    for (let i = 0; i < shape[dim]; i++) rec([...prefix, i], dim + 1)
  }
  rec([], 0)
  return out
}

function sourceGridSpec(shape) {
  if (shape.length === 0) return { rows: 1, cols: 1 }
  if (shape.length === 1) return { rows: 1, cols: shape[0] }
  if (shape.length === 2) return { rows: shape[0], cols: shape[1] }
  const rows = shape.slice(0, -1).reduce((a, b) => a * b, 1)
  return { rows, cols: shape[shape.length - 1] }
}

function layoutOffset(base, strides, idx) {
  return idx.reduce((sum, v, d) => sum + v * (strides[d] ?? 0), base)
}

function targetCell(targetShape, off) {
  if (targetShape.length === 1) return [0, off]
  const cols = targetShape[targetShape.length - 1] || 1
  return [Math.floor(off / cols), ((off % cols) + cols) % cols]
}

function getTargetDims(targetShape) {
  if (targetShape.length <= 1) {
    const rows = 1
    const cols = Math.max(1, targetShape[0] ?? 1)
    return { rows, cols, total: Math.max(1, cols) }
  }
  const rows = targetShape.slice(0, -1).reduce((a, b) => a * Math.max(1, b), 1)
  const cols = Math.max(1, targetShape[targetShape.length - 1] ?? 1)
  return { rows, cols, total: Math.max(1, rows * cols) }
}

function buildTargetColorByCell(targetShape) {
  const { rows, cols, total } = getTargetDims(targetShape)
  const colorByCell = new Map()
  let idx = 0
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      colorByCell.set(cellKey(r, c), colorForOrdinal(idx, total))
      idx += 1
    }
  }
  return colorByCell
}

function inBoundsTarget(targetShape, target) {
  const { rows, cols } = getTargetDims(targetShape)
  const row = target[0]
  const col = target[1]
  return row >= 0 && row < rows && col >= 0 && col < cols
}

function sourceColorsForMaps(maps, colorMode, props, sourceColorByIndex, targetColorByCell) {
  const out = []
  for (const m of maps) {
    if (colorMode === 'source') {
      const color = sourceColorByIndex.get(idxKey(m.idx))
      if (color) out.push(color)
      continue
    }
    if (colorMode === 'linear') {
      if (m.inBounds) out.push(colorForOffset(m.off, props.memorySize))
      continue
    }
    if (colorMode === 'target' && inBoundsTarget(props.targetShape, m.target)) {
      const tcolor = targetColorByCell.get(cellKey(m.target[0], m.target[1]))
      if (tcolor) out.push(tcolor)
    }
  }
  return out
}

function buildMaps(props) {
  const indices = allIndices(props.sourceShape)
  const maps = indices.map((idx) => {
    const off = layoutOffset(props.base, props.strides, idx)
    return {
      idx,
      off,
      inBounds: off >= 0 && off < props.memorySize,
      target: targetCell(props.targetShape, off)
    }
  })
  const byOff = new Map()
  const byTarget = new Map()
  for (const m of maps) {
    if (!byOff.has(m.off)) byOff.set(m.off, [])
    byOff.get(m.off).push(m)
    if (m.inBounds) {
      const k = cellKey(m.target[0], m.target[1])
      if (!byTarget.has(k)) byTarget.set(k, [])
      byTarget.get(k).push(m)
    }
  }
  return { indices, maps, byOff, byTarget }
}

function useElementSize() {
  const ref = React.useRef(null)
  const [size, setSize] = React.useState({ width: 900, height: 720 })
  React.useEffect(() => {
    const el = ref.current
    if (!el) return
    const update = () => setSize({ width: el.clientWidth || 900, height: el.clientHeight || 720 })
    update()
    const win = typeof window !== 'undefined' ? window : null
    if (typeof ResizeObserver === 'undefined' || !win) {
      if (!win) return
      win.addEventListener('resize', update)
      return () => win.removeEventListener('resize', update)
    }
    const observer = new ResizeObserver(update)
    observer.observe(el)
    return () => observer.disconnect()
  }, [])
  return [ref, size]
}

function scaledSize(naturalWidth, naturalHeight, maxWidth, maxHeight) {
  const scale = Math.min(1, maxWidth / Math.max(1, naturalWidth), maxHeight / Math.max(1, naturalHeight))
  const safeScale = Math.max(0.05, scale)
  return {
    scale: safeScale,
    width: naturalWidth * safeScale,
    height: naturalHeight * safeScale
  }
}

function Style() {
  return React.createElement('style', null, `
    .nl-layout-vis {
      --bg: #0d1017;
      --panel: #161b25;
      --panel2: #10141c;
      --text: #edf2fb;
      --muted: #a9b3c5;
      --line: #303847;
      --gap: #2b303a;
      --invalid: #3b2830;
      --unmapped: #252a34;
      --accent: #94b8ff;
      --warn: #ffd166;
      --alias: #ff8a72;
      color: var(--text);
      background: radial-gradient(circle at 15% 0%, rgba(47, 65, 105, .42), transparent 35%), linear-gradient(180deg, #0f1320, var(--bg));
      border: 1px solid var(--line);
      border-radius: 15px;
      padding: 12px;
      font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      overflow: hidden;
      width: 100%;
      aspect-ratio: 1 / 1;
      min-height: 0;
      display: block;
    }
    .nl-layout-vis * { box-sizing: border-box; }
    .nl-layout-vis .viz-stack { display: grid; grid-template-rows: 2fr 1fr 2fr; gap: 8px; min-height: 0; height: 100%; }
    .nl-layout-vis .viz-stack > div { min-height: 0; }
    .nl-layout-vis .viz-stack > div > .panel { height: 100%; }
    .nl-layout-vis .panel { min-height: 0; display: flex; flex-direction: column; }
    .nl-layout-vis .mode-btn { display: inline-flex; align-items: center; justify-content: center; border: 1px solid rgba(255,255,255,.22); margin: 0; padding: 5px 10px; font-size: 11px; line-height: 1; font-weight: 700; color: #e5ebfb; background: rgba(255,255,255,0.05); border-radius: 999px; cursor: pointer; box-shadow: inset 0 0 0 1px rgba(0,0,0,.35); transition: background .15s ease, border-color .15s ease, box-shadow .15s ease, color .15s ease; }
    .nl-layout-vis .mode-btn:hover { color: #f8fbff; background: rgba(148,184,255,.14); border-color: #96b6ff; }
    .nl-layout-vis .mode-btn.active { color: #edf2fb; background: #1f2734; border-color: #7ea7ff; box-shadow: 0 0 0 2px rgba(148,184,255,.35), inset 0 0 0 1px rgba(255,255,255,.22); }
    .nl-layout-vis .title { color: var(--muted); font-size: 12px; display: flex; align-items: baseline; justify-content: space-between; gap: 10px; margin-bottom: 9px; }
    .nl-layout-vis .title b { color: #dbe5f5; font-size: 13px; }
    .nl-layout-vis .scaled-frame { min-height: 0; flex: 1 1 auto; overflow: visible; display: flex; align-items: center; justify-content: center; padding: 4px 0; }
    .nl-layout-vis .scaled-shell { overflow: visible; }
    .nl-layout-vis .scaled-content { transform-origin: top left; }
    .nl-layout-vis .grid { display: grid; width: max-content; gap: 4px; }
    .nl-layout-vis .cell, .nl-layout-vis .memcell { border: 1px solid rgba(255,255,255,.14); color: #071018; font-weight: 800; user-select: none; cursor: pointer; position: relative; text-align: center; }
    .nl-layout-vis .cell { border-radius: 9px; display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 1px; font-size: 10px; line-height: 1; }
    .nl-layout-vis .cell small { font-size: 9px; line-height: 1; opacity: .74; }
    .nl-layout-vis .cell.oob { background: var(--invalid) !important; color: #ffd9df; }
    .nl-layout-vis .cell.unmapped { background: var(--unmapped); color: #768094; cursor: default; }
    .nl-layout-vis .cell.alias, .nl-layout-vis .memcell.alias { outline: 3px solid var(--alias); outline-offset: -2px; }
    .nl-layout-vis .cell.highlight, .nl-layout-vis .memcell.highlight { box-shadow: 0 0 0 3px #fff, 0 0 25px 6px rgba(148,184,255,.62); z-index: 8; }
    .nl-layout-vis .memory { display: grid; gap: 3px; width: 100%; }
    .nl-layout-vis .memcell { border-radius: 8px; display: flex; flex-direction: column; align-items: center; justify-content: center; font-size: 11px; line-height: 1; }
    .nl-layout-vis .memcell small { margin-top: 2px; font-size: 8px; opacity: .68; }
    .nl-layout-vis .memcell.gap { background: var(--gap); color: #858fa2; cursor: default; }
    .nl-layout-vis .memcell.base::before { content: "▼"; position: absolute; top: -19px; left: 50%; transform: translateX(-50%); color: var(--warn); font-size: 13px; }
    .nl-layout-vis .ok { color: #7ee787; }
    .nl-layout-vis .warn { color: var(--warn); }
    @media (max-width: 640px) { .nl-layout-vis { padding: 8px; border-radius: 12px; } }
  `)
}

function ModeTab({ selectedMode, mode, onChange }) {
  return React.createElement('button', {
    type: 'button',
    className: mode === selectedMode ? 'mode-btn active' : 'mode-btn',
    onClick: () => onChange(mode)
  },
    colorModeLabels[mode]
  )
}

function SourceGrid({ props, indices, byOff, byTarget, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width, height }) {
  const spec = sourceGridSpec(props.sourceShape)
  const cell = 36
  const gap = 4
  const naturalWidth = spec.cols * cell + Math.max(0, spec.cols - 1) * gap
  const naturalHeight = spec.rows * cell + Math.max(0, spec.rows - 1) * gap
  const fit = scaledSize(naturalWidth, naturalHeight, width, height)
  return React.createElement('section', { className: 'panel' },
    React.createElement('div', { className: 'title' },
      React.createElement(ModeTab, { selectedMode: colorMode, mode: 'source', onChange: setColorMode })
    ),
    React.createElement('div', { className: 'scaled-frame' },
      React.createElement('div', { className: 'scaled-shell', style: { width: fit.width, height: fit.height } },
        React.createElement('div', { className: 'scaled-content', style: { transform: `scale(${fit.scale})` } },
        React.createElement('div', { className: 'grid', style: { gridTemplateColumns: `repeat(${spec.cols}, ${cell}px)` } },
            indices.map((idx) => {
              const off = layoutOffset(props.base, props.strides, idx)
              const map = { idx, off, inBounds: off >= 0 && off < props.memorySize, target: targetCell(props.targetShape, off) }
              const aliases = byOff.get(off) || []
              const targetKey = cellKey(map.target[0], map.target[1])
              const aliasList = colorMode === 'target'
                ? (byTarget.get(targetKey) || [])
                : aliases
              const cls = ['cell']
              const colors = sourceColorsForMaps([map], colorMode, props, sourceColorByIndex, targetColorByCell)
              const background = colorFromList(colors)
              const sourceInTarget = inBoundsTarget(props.targetShape, map.target)
              const isUnmapped = colors.length === 0 && colorMode !== 'source'
              const isTargetOob = colorMode === 'target' && !sourceInTarget
              if (isUnmapped || isTargetOob) cls.push('oob')
              if (aliasList.length > 1) cls.push('alias')
              if (highlight && (highlight.idx === idxKey(idx) || highlight.off === off)) cls.push('highlight')
              return React.createElement('div', {
                key: idxKey(idx),
                className: cls.join(' '),
                style: { width: cell, height: cell, background },
                onClick: (event) => { event.stopPropagation(); setHighlight({ idx: idxKey(idx), off }) }
              }, React.createElement('span', null, idxLabel(idx)), React.createElement('small', null, off))
            })
          )
        )
      )
    )
  )
}

function MemoryGrid({ props, byOff, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width, height }) {
  const cells = []
  const gap = 3
  const targetColToRowRatio = 5
  const minCell = 18
  const targetRows = Math.max(1, Math.round(Math.sqrt(Math.max(1, props.memorySize) / targetColToRowRatio)))
  const colsFromAspect = Math.max(1, Math.ceil(props.memorySize / targetRows))
  const maxColsByWidth = Math.max(1, Math.floor((width + gap) / (minCell + gap)))
  const cols = Math.min(props.memorySize, Math.max(colsFromAspect, maxColsByWidth))
  const rows = Math.max(1, Math.ceil(props.memorySize / cols))
  const cell = Math.max(1, (width - (cols - 1) * gap) / cols)
  const cellHeight = Math.max(10, Math.round(cell * 1.45))
  const naturalHeight = rows * cellHeight + Math.max(0, rows - 1) * gap
  const scaleY = Math.min(1, height / Math.max(1, naturalHeight))
  const scaledGap = Math.max(0.5, gap * scaleY)
  for (let off = 0; off < props.memorySize; off++) {
    const arr = byOff.get(off) || []
    const mapObjects = arr.map((m) => ({
      idx: m.idx,
      off: m.off,
      inBounds: m.inBounds,
      target: m.target
    }))
    const colors = colorMode === 'linear'
      ? [colorForOffset(off, props.memorySize)]
      : sourceColorsForMaps(mapObjects, colorMode, props, sourceColorByIndex, targetColorByCell)
    const background = colorFromList(colors)
    const cls = ['memcell']
    if (!arr.length) cls.push('gap')
    if (arr.length > 1) cls.push('alias')
    if (off === props.base) cls.push('base')
    if (highlight && highlight.off === off) cls.push('highlight')
    const isUnmapped = colorMode !== 'linear' && !arr.length
    cells.push(React.createElement('div', {
      key: off,
      className: cls.join(' '),
      style: { width: cell, height: cellHeight * scaleY, ...(background ? { background } : {}), ...(isUnmapped ? { background: 'var(--gap)' } : {}) },
      onClick: arr.length ? (event) => { event.stopPropagation(); setHighlight({ off }) } : undefined
    }))
  }
  return React.createElement('section', { className: 'panel' },
    React.createElement('div', { className: 'title' },
      React.createElement(ModeTab, { selectedMode: colorMode, mode: 'linear', onChange: setColorMode })
    ),
    React.createElement('div', { className: 'scaled-frame' },
      React.createElement('div', { className: 'scaled-shell', style: { width: width, height: naturalHeight * scaleY } },
        React.createElement('div', { className: 'scaled-content', style: { transform: 'scale(1)', transformOrigin: 'top left' } },
          React.createElement('div', { className: 'memory', style: { gridTemplateColumns: `repeat(${cols}, ${cell}px)`, gridGap: `${scaledGap}px`, width } }, cells)
        )
      )
    )
  )
}

function TargetGrid({ props, byTarget, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width, height }) {
  const { rows, cols } = getTargetDims(props.targetShape)
  const cell = 36
  const gap = 4
  const naturalWidth = cols * cell + Math.max(0, cols - 1) * gap
  const naturalHeight = rows * cell + Math.max(0, rows - 1) * gap
  const fit = scaledSize(naturalWidth, naturalHeight, width, height)
  const cells = []
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const arr = byTarget.get(cellKey(r, c)) || []
      const mapObjects = arr.map((m) => ({
        idx: m.idx,
        off: m.off,
        inBounds: m.inBounds,
        target: m.target
      }))
      const mappedColors = sourceColorsForMaps(mapObjects, colorMode, props, sourceColorByIndex, targetColorByCell)
      const baseColor = targetColorByCell.get(cellKey(r, c))
      const colors = arr.length
        ? mappedColors
        : (colorMode === 'target' && baseColor ? [baseColor] : [])
      const background = colorFromList(colors.length ? colors : (baseColor ? [baseColor] : []))
      if (!arr.length) {
        const style = { width: cell, height: cell, ...(colorMode === 'target' && background ? { background } : {}) }
        const cls = colorMode === 'target' ? ['cell'] : ['cell', 'unmapped']
        cells.push(React.createElement('div', { key: cellKey(r, c), className: cls.join(' '), style }, '-'))
        continue
      }
      const off = arr[0].off
      const cls = ['cell']
      if (arr.length > 1) cls.push('alias')
      if (highlight && highlight.off === off) cls.push('highlight')
      cells.push(React.createElement('div', {
        key: cellKey(r, c),
        className: cls.join(' '),
        style: { width: cell, height: cell, ...(background ? { background } : {}) },
        onClick: (event) => { event.stopPropagation(); setHighlight({ off }) }
      }, arr.length > 1 ? React.createElement('span', null, `x${arr.length}`) : React.createElement('span', null, idxLabel(arr[0].idx)), React.createElement('small', null, off)))
    }
  }
  return React.createElement('section', { className: 'panel' },
    React.createElement('div', { className: 'title' },
      React.createElement(ModeTab, { selectedMode: colorMode, mode: 'target', onChange: setColorMode })
    ),
    React.createElement('div', { className: 'scaled-frame' },
      React.createElement('div', { className: 'scaled-shell', style: { width: fit.width, height: fit.height } },
        React.createElement('div', { className: 'scaled-content', style: { transform: `scale(${fit.scale})` } },
          React.createElement('div', { className: 'grid', style: { gridTemplateColumns: `repeat(${cols}, ${cell}px)` } }, cells)
        )
      )
    )
  )
}

function Annotations({ props, indices, maps, byOff }) {
  const inBounds = maps.filter((m) => m.inBounds).length
  const mappedOffsets = [...byOff.keys()].filter((o) => o >= 0 && o < props.memorySize).length
  const aliasOffsets = [...byOff.entries()].filter(([, a]) => a.length > 1).length
  const aliasSources = [...byOff.values()].reduce((sum, a) => sum + (a.length > 1 ? a.length : 0), 0)
  return React.createElement('section', { className: 'ann' },
    React.createElement('div', { className: 'ann-grid' },
      React.createElement('div', null, 'Shape'), React.createElement('div', null, `source = [${props.sourceShape.join(', ')}], target = [${props.targetShape.join(', ')}]`),
      React.createElement('div', null, 'Layout'), React.createElement('div', null, `base = ${props.base}, strides = [${props.strides.join(', ')}]`),
      React.createElement('div', null, 'Formula'), React.createElement('div', null, props.formula),
      React.createElement('div', null, 'Derivation'), React.createElement('div', null, props.derivation),
      React.createElement('div', null, 'Coverage'), React.createElement('div', null, `${indices.length} source cells · ${inBounds} in-bounds mappings · ${mappedOffsets} / ${props.memorySize} memory cells reached`),
      React.createElement('div', null, 'Aliasing'), React.createElement('div', { className: aliasOffsets ? 'warn' : 'ok' }, aliasOffsets ? `${aliasSources} source cells share ${aliasOffsets} memory offsets` : 'No aliasing over this shape')
    ),
    React.createElement('div', { className: 'chips' },
      React.createElement('span', { className: 'pill' }, 'hue = source/target row-major · memory = offset'),
      React.createElement('span', { className: 'pill' }, 'gray = unmapped / unreachable'),
      React.createElement('span', { className: 'pill' }, 'coral outline = alias'),
      React.createElement('span', { className: 'pill' }, 'yellow tick = base')
    )
  )
}

export default function LayoutVis(props) {
  const [rootRef, size] = useElementSize()
  const [highlight, setHighlight] = React.useState(null)
  const [colorMode, setColorMode] = React.useState('source')
  const model = buildMaps(props)
  const sourceColorByIndex = new Map()
  model.indices.forEach((idx, index) => sourceColorByIndex.set(idxKey(idx), colorForOrdinal(index, model.indices.length)))
  const targetColorByCell = buildTargetColorByCell(props.targetShape)
  const pad = size.width < 640 ? 16 : 24
  const stackWidth = Math.max(160, size.width - pad)
  const stackHeight = Math.max(160, size.height - pad)
  const gapTotal = 16
  const unit = Math.max(20, (stackHeight - gapTotal) / 5)
  const sourceHeight = unit * 2
  const memoryHeight = unit
  const targetHeight = unit * 2
  const innerWidth = Math.max(120, stackWidth)
  const titleHeight = size.width < 420 ? 24 : 30
  return React.createElement('div', { ref: rootRef, className: 'nl-layout-vis', 'data-version': WIDGET_VERSION, onClick: () => setHighlight(null) },
    React.createElement(Style),
    React.createElement('div', { className: 'viz-stack', style: { height: stackHeight } },
      React.createElement('div', { style: { height: sourceHeight, minHeight: 0 } },
        React.createElement(SourceGrid, { props, indices: model.indices, byOff: model.byOff, byTarget: model.byTarget, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width: innerWidth, height: Math.max(40, sourceHeight - titleHeight) })
      ),
      React.createElement('div', { style: { height: memoryHeight, minHeight: 0 } },
        React.createElement(MemoryGrid, { props, byOff: model.byOff, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width: innerWidth, height: Math.max(30, memoryHeight - titleHeight) })
      ),
      React.createElement('div', { style: { height: targetHeight, minHeight: 0 } },
        React.createElement(TargetGrid, { props, byTarget: model.byTarget, colorMode, sourceColorByIndex, targetColorByCell, highlight, setHighlight, setColorMode, width: innerWidth, height: Math.max(40, targetHeight - titleHeight) })
      )
    )
  )
}
