import { useCallback, useEffect, useMemo, useRef, useState } from 'react'
import * as d3 from 'd3'
import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import treemapData from '../assets/mathlib_treemap.json'
import '../App.css'

type TreemapNode = {
  name: string
  path?: string
  series: Record<string, number>
  children?: TreemapNode[]
  isLeaf?: boolean
}

type TreemapData = {
  root: TreemapNode
  seriesKeys: string[]
}
type UploadedEntry = { path: string; series: Record<string, number> }
type UploadedData = {
  root?: TreemapNode
  seriesKeys?: string[]
  entries?: UploadedEntry[]
}
type ColorMode = 'global' | 'per_parent'
type ColorScale = { low: string; high: string }
type CompiledRegex = { pattern: string; key: string; regex: RegExp }
type LayoutNode = {
  name: string
  path?: string
  series: Record<string, number>
  isLeaf?: boolean
  x0: number
  y0: number
  x1: number
  y1: number
  fill: string
  parentName?: string
}
type LayoutPayload = {
  parentNodes: LayoutNode[]
  childNodes: LayoutNode[]
  labelSuffix: string
}

type MathlibPageProps = {
  embedded?: boolean
}

declare global {
  interface Window {
    acquireVsCodeApi?: () => { postMessage: (message: unknown) => void }
    __vscodeApi?: { postMessage: (message: unknown) => void }
  }
}

type BuildNode = {
  name: string
  path: string
  children: Map<string, BuildNode>
  size: number
  count: number
  loc: number
  commentLines: number
  codeLines: number
  portingNotes: number
  adaptationNotes: number
  noteTotal: number
  regexCounts: Record<string, number>
}

const MAX_DEPTH = 5
const MIN_PERCENT = 0.01
const GROUP_BY = 'loc'
const portingNoteRegex = /porting[\s_-]*note/gi
const adaptationNoteRegex = /#adaptation_note\b/gi

const makeRegexKey = (pattern: string) => `regex:${pattern}`

const compileRegexPatterns = (patterns: string[]): CompiledRegex[] => {
  const compiled: CompiledRegex[] = []
  patterns.forEach((pattern) => {
    if (!pattern.trim()) {
      return
    }
    try {
      compiled.push({
        pattern,
        key: makeRegexKey(pattern),
        regex: new RegExp(pattern, 'g'),
      })
    } catch (error) {
      console.warn('Invalid regex pattern', pattern, error)
    }
  })
  return compiled
}

const analyzeLeanContent = (content: string, regexPatterns: CompiledRegex[]) => {
  const lines = content.split(/\r\n|\r|\n/)
  const loc = lines.length
  const portingNotes = Array.from(content.matchAll(portingNoteRegex)).length
  const adaptationNotes = Array.from(content.matchAll(adaptationNoteRegex)).length
  const regexCounts: Record<string, number> = {}
  regexPatterns.forEach(({ key, regex }) => {
    regexCounts[key] = content.match(regex)?.length ?? 0
  })
  let commentLines = 0
  let inBlock = false
  for (const line of lines) {
    const trimmed = line.trim()
    if (inBlock) {
      commentLines += 1
      if (trimmed.includes('-/')) {
        inBlock = false
      }
      continue
    }
    if (trimmed.startsWith('--')) {
      commentLines += 1
      continue
    }
    if (trimmed.includes('/-')) {
      commentLines += 1
      if (!trimmed.includes('-/')) {
        inBlock = true
      }
    }
  }
  const codeLines = Math.max(0, loc - commentLines)
  return {
    loc,
    commentLines,
    codeLines,
    portingNotes,
    adaptationNotes,
    noteTotal: portingNotes + adaptationNotes,
    regexCounts,
  }
}

const makeRootNode = (): BuildNode => ({
  name: 'Mathlib',
  path: 'Mathlib',
  children: new Map<string, BuildNode>(),
  size: 0,
  count: 0,
  loc: 0,
  commentLines: 0,
  codeLines: 0,
  portingNotes: 0,
  adaptationNotes: 0,
  noteTotal: 0,
  regexCounts: {},
})

const addBuildFile = (
  root: BuildNode,
  relativePath: string,
  size: number,
  metrics: ReturnType<typeof analyzeLeanContent>,
) => {
  const parts = relativePath.split('/').filter(Boolean)
  if (parts[0] === 'Mathlib') {
    parts.shift()
  }
  const fileName = parts.pop()
  if (!fileName) {
    return
  }
  const baseName = fileName.replace(/\.lean$/, '')
  const segments = [...parts, baseName].filter(Boolean)
  const depth = Math.min(segments.length, MAX_DEPTH)

  let node = root
  node.size += size
  node.count += 1
  node.loc += metrics.loc
  node.commentLines += metrics.commentLines
  node.codeLines += metrics.codeLines
  node.portingNotes += metrics.portingNotes
  node.adaptationNotes += metrics.adaptationNotes
  node.noteTotal += metrics.noteTotal
  Object.entries(metrics.regexCounts).forEach(([key, value]) => {
    node.regexCounts[key] = (node.regexCounts[key] ?? 0) + value
  })

  for (let i = 0; i < depth; i += 1) {
    const name = segments[i]
    let child = node.children.get(name)
    if (!child) {
      child = {
        name,
        path: node.path ? `${node.path}/${name}` : name,
        children: new Map<string, BuildNode>(),
        size: 0,
        count: 0,
        loc: 0,
        commentLines: 0,
        codeLines: 0,
        portingNotes: 0,
        adaptationNotes: 0,
        noteTotal: 0,
        regexCounts: {},
      }
      node.children.set(name, child)
    }
    child.size += size
    child.count += 1
    child.loc += metrics.loc
    child.commentLines += metrics.commentLines
    child.codeLines += metrics.codeLines
    child.portingNotes += metrics.portingNotes
    child.adaptationNotes += metrics.adaptationNotes
    child.noteTotal += metrics.noteTotal
    Object.entries(metrics.regexCounts).forEach(([key, value]) => {
      child.regexCounts[key] = (child.regexCounts[key] ?? 0) + value
    })
    node = child
  }
}

const sumSeriesValue = (node: TreemapNode, key: string): number => {
  const current = node.series?.[key]
  if (typeof current === 'number') {
    return current
  }
  return (node.children ?? []).reduce((sum, child) => sum + sumSeriesValue(child, key), 0)
}

const normalizeNode = (node: TreemapNode): TreemapNode => {
  if (!node.children || node.children.length === 0) {
    return node
  }
  const normalizedChildren = node.children.map(normalizeNode)
  const key = node.series?.[GROUP_BY] !== undefined ? GROUP_BY : 'bytes'
  const total = normalizedChildren.reduce((sum, child) => sum + sumSeriesValue(child, key), 0)
  if (total === 0) {
    return { ...node, children: normalizedChildren }
  }
  const keep: TreemapNode[] = []
  const otherChildren: TreemapNode[] = []
  for (const child of normalizedChildren) {
    const childValue = sumSeriesValue(child, key)
    if (childValue / total < MIN_PERCENT) {
      otherChildren.push(child)
    } else {
      keep.push(child)
    }
  }
  if (otherChildren.length === 0 || keep.length === 0) {
    return { ...node, children: normalizedChildren }
  }
  const seriesKeys = new Set<string>()
  for (const child of otherChildren) {
    Object.keys(child.series ?? {}).forEach((seriesKey) => seriesKeys.add(seriesKey))
  }
  const otherSeries: Record<string, number> = {}
  for (const seriesKey of seriesKeys) {
    otherSeries[seriesKey] = otherChildren.reduce(
      (sum, child) => sum + sumSeriesValue(child, seriesKey),
      0,
    )
  }
  const otherNode: TreemapNode = normalizeNode({
    name: 'Miscellaneous',
    path: node.path ? `${node.path}/Miscellaneous` : 'Miscellaneous',
    children: otherChildren,
    series: otherSeries,
  })
  return { ...node, children: [...keep, otherNode] }
}

const buildTreemapFromFiles = async (files: FileList, regexPatterns: string[]) => {
  const root = makeRootNode()
  const compiledRegexes = compileRegexPatterns(regexPatterns)
  const firstRelative = Array.from(files)[0]?.webkitRelativePath?.replace(/\\/g, '/') ?? ''
  const baseFolder = firstRelative.includes('/') ? firstRelative.split('/')[0] : ''
  const readFiles = Array.from(files)
    .filter((file) => file.name.endsWith('.lean'))
    .map(async (file) => {
      const content = await file.text()
      const metrics = analyzeLeanContent(content, compiledRegexes)
      const rawPath = (file.webkitRelativePath || file.name).replace(/\\/g, '/')
      const relativePath = baseFolder && rawPath.startsWith(`${baseFolder}/`)
        ? rawPath.slice(baseFolder.length + 1)
        : rawPath
      addBuildFile(root, relativePath, file.size, metrics)
    })
  await Promise.all(readFiles)

  const toTreemapNode = (node: BuildNode): TreemapNode => {
    const children = Array.from(node.children.values()).map(toTreemapNode)
    const commentRatio = node.codeLines > 0 ? node.commentLines / node.codeLines : 0
    const series = {
      bytes: node.size,
      file_count: node.count,
      loc: node.loc,
      comment_lines: node.commentLines,
      code_lines: node.codeLines,
      comment_ratio: commentRatio,
      porting_notes: node.portingNotes,
      adaptation_notes: node.adaptationNotes,
      notes_total: node.noteTotal,
      ...node.regexCounts,
    }
    return {
      name: node.name,
      path: node.path,
      children: children.length > 0 ? children : undefined,
      series,
    }
  }

  const outputRoot = normalizeNode(toTreemapNode(root))
  const seriesKeys = new Set<string>()
  const collectKeys = (node: TreemapNode) => {
    Object.keys(node.series ?? {}).forEach((key) => seriesKeys.add(key))
    node.children?.forEach(collectKeys)
  }
  collectKeys(outputRoot)
  return { root: outputRoot, seriesKeys: Array.from(seriesKeys).sort() }
}

const useTreemap = (
  containerRef: React.RefObject<HTMLDivElement>,
  data: TreemapNode,
  sizeSeries: string,
  colorSeries: string,
  colorMode: ColorMode,
  theme: 'highk' | 'reticle',
  zoomPath: string[],
  setZoomPath: (path: string[]) => void,
  colors: string[],
  hoveredGroup: string | null,
  tooltipRef: React.RefObject<HTMLDivElement>,
  colorScale: ColorScale,
  mathlibPath: string,
  openFileTarget: (fullPath: string, link: string) => void,
  warnMissingMathlibPath: () => void,
  isTauri: boolean,
  vscodePath: string,
) => {
  const workerRef = useRef<Worker | null>(null)
  const requestIdRef = useRef(0)
  const [layout, setLayout] = useState<LayoutPayload | null>(null)

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    const worker = new Worker(
      new URL('../workers/treemapWorker.ts', import.meta.url),
      { type: 'module' },
    )
    workerRef.current = worker
    const handleMessage = (event: MessageEvent) => {
      const payload = event.data as { type?: string; requestId?: number; payload?: LayoutPayload }
      if (payload.type !== 'layout' || !payload.payload) {
        return
      }
      if (payload.requestId !== requestIdRef.current) {
        return
      }
      setLayout(payload.payload)
    }
    worker.addEventListener('message', handleMessage)
    return () => {
      worker.removeEventListener('message', handleMessage)
      worker.terminate()
      workerRef.current = null
    }
  }, [])

  useEffect(() => {
    const container = containerRef.current
    if (!container) {
      return
    }
    const width = container.clientWidth
    if (!width) {
      return
    }
    const worker = workerRef.current
    if (!worker) {
      return
    }
    const requestId = requestIdRef.current + 1
    requestIdRef.current = requestId
    worker.postMessage({
      type: 'layout',
      requestId,
      payload: {
        data,
        sizeSeries,
        colorSeries,
        colorMode,
        theme,
        zoomPath,
        width,
        height: 840,
        colors,
        colorScale,
      },
    })
  }, [
    containerRef,
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    zoomPath,
    colors,
    colorScale,
  ])

  useEffect(() => {
    const container = containerRef.current
    if (!container || !layout) {
      return
    }

    const width = container.clientWidth
    const height = 840

    container.innerHTML = ''
    const svg = d3
      .select(container)
      .append('svg')
      .attr('class', 'treemap-svg')
      .attr('width', width)
      .attr('height', height)

    const tooltip = tooltipRef.current
    const formatter = new Intl.NumberFormat('en-US')

    const setTooltip = (
      event: MouseEvent,
      labelParts: string[],
      value: number,
      suffix: string,
    ) => {
      if (!tooltip) {
        return
      }
      const bounds = container.getBoundingClientRect()
      tooltip.textContent = `${labelParts.join(' / ')} · ${formatter.format(value)} ${suffix}`
      tooltip.style.left = `${event.clientX - bounds.left + 12}px`
      tooltip.style.top = `${event.clientY - bounds.top + 12}px`
      tooltip.classList.add('is-visible')
    }

    const hideTooltip = () => {
      if (!tooltip) {
        return
      }
      tooltip.classList.remove('is-visible')
    }

    const labelSuffix = layout.labelSuffix
    const parentNodes = layout.parentNodes
    const childNodes = layout.childNodes
    const basePath = isTauri ? mathlibPath : vscodePath
    const normalizedBasePath = basePath.trim().replace(/\/+$/, '')
    const buildFileTarget = (node: LayoutNode) => {
      if (!normalizedBasePath) {
        return null
      }
      const nodePath = node.path?.replace(/^\/+/, '')
      if (!nodePath) {
        return null
      }
      const fullPath = `${normalizedBasePath}/${nodePath}.lean`
      return { fullPath, link: `vscode://file/${encodeURI(fullPath)}` }
    }

    const parents = svg.selectAll('g.parent').data(parentNodes).enter().append('g').attr('class', 'parent')
    parents
      .append('rect')
      .attr('x', (d) => d.x0)
      .attr('y', (d) => d.y0)
      .attr('width', (d) => d.x1 - d.x0)
      .attr('height', (d) => d.y1 - d.y0)
      .attr('class', 'treemap-rect treemap-parent')
      .classed('is-leaf', (d) => !!d.isLeaf)
      .classed('is-folder', (d) => !d.isLeaf)
      .attr('fill', (d) => d.fill)

      .attr('data-group', (d) => d.name)
      .on('click', (_, d) => {
        if (d.isLeaf) {
          const target = buildFileTarget(d)
          if (target) {
            void openFileTarget(target.fullPath, target.link)
          } else {
            void warnMissingMathlibPath()
          }
          return
        }
        setZoomPath([...zoomPath, d.name])
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mousemove', (event, d) => {
        const label = [...zoomPath, d.name].filter(Boolean)
        const sizeValue = d.series?.[sizeSeries] ?? 0
        const colorValue = d.series?.[colorSeries] ?? 0
        setTooltip(event, label, sizeValue, labelSuffix)
        if (tooltip) {
          tooltip.textContent = `${label.join(' / ')} · ${formatter.format(sizeValue)} ${labelSuffix} · ${formatter.format(colorValue)} ${colorSeries.replace(/_/g, ' ')}`
        }
      })
      .on('mouseout', function () {
        d3.select(this).classed('is-hovered', false)
        hideTooltip()
      })

    parents
      .append('text')
      .attr('x', (d) => d.x0 + 6)
      .attr('y', (d) => d.y0 + 14)
      .attr('class', 'treemap-parent-label')
      .text((d) => d.name)

    const nodes = svg.selectAll('g.child').data(childNodes).enter().append('g').attr('class', 'child')

    const clipId = (_: LayoutNode, i: number) => (
      `treemap-clip-${sizeSeries}-${i}`
    )
    const defs = svg.append('defs')
    defs
      .selectAll('clipPath')
      .data(childNodes)
      .enter()
      .append('clipPath')
      .attr('id', clipId)
      .attr('clipPathUnits', 'userSpaceOnUse')
      .append('rect')
      .attr('x', (d) => d.x0 + 2)
      .attr('y', (d) => d.y0 + 2)
      .attr('width', (d) => Math.max(0, d.x1 - d.x0 - 4))
      .attr('height', (d) => Math.max(0, d.y1 - d.y0 - 4))
    nodes
      .append('rect')
      .attr('x', (d) => d.x0)
      .attr('y', (d) => d.y0)
      .attr('width', (d) => d.x1 - d.x0)
      .attr('height', (d) => d.y1 - d.y0)
      .attr('class', 'treemap-rect treemap-child')
      .classed('is-leaf', (d) => !!d.isLeaf)
      .classed('is-folder', (d) => !d.isLeaf)
      .attr('fill', (d) => d.fill)
      .attr('data-group', (d) => d.parentName ?? '')
      .on('click', (_, d) => {
        if (d.isLeaf) {
          const target = buildFileTarget(d)
          if (target) {
            void openFileTarget(target.fullPath, target.link)
          } else {
            void warnMissingMathlibPath()
          }
          return
        }
        const parent = d.parentName
        if (parent) {
          setZoomPath([...zoomPath, parent, d.name])
        }
      })
      .on('mousemove', (event, d) => {
        const parent = d.parentName ?? ''
        const label = [...zoomPath, parent, d.name].filter(Boolean)
        const sizeValue = d.series?.[sizeSeries] ?? 0
        const colorValue = d.series?.[colorSeries] ?? 0
        setTooltip(event, label, sizeValue, labelSuffix)
        if (tooltip) {
          tooltip.textContent = `${label.join(' / ')} · ${formatter.format(sizeValue)} ${labelSuffix} · ${formatter.format(colorValue)} ${colorSeries.replace(/_/g, ' ')}`
        }
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mouseout', function () {
        d3.select(this).classed('is-hovered', false)
        hideTooltip()
      })

    nodes
      .append('text')
      .attr('x', (d) => d.x0 + 6)
      .attr('y', (d) => d.y0 + 6)
      .attr('class', 'treemap-label')
      .attr('dominant-baseline', 'hanging')
      .attr('clip-path', (d, i) => `url(#${clipId(d, i)})`)
      .text((d) => d.name)
      .style('display', (d) => (
        (d.x1 - d.x0 < 28 || d.y1 - d.y0 < 14) ? 'none' : 'block'
      ))

    if (hoveredGroup) {
      svg
        .selectAll<SVGRectElement, LayoutNode>('.treemap-child')
        .classed('is-dim', (d) => (d.parentName ?? '') !== hoveredGroup)
        .classed('is-group-hovered', (d) => (d.parentName ?? '') === hoveredGroup)
    }

    return () => {
      container.innerHTML = ''
    }
  }, [
    containerRef,
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    zoomPath,
    setZoomPath,
    colors,
    hoveredGroup,
    tooltipRef,
    colorScale,
    mathlibPath,
    openFileTarget,
    warnMissingMathlibPath,
    isTauri,
    vscodePath,
    layout,
  ])
}

export const MathlibPage = ({ embedded = false }: MathlibPageProps) => {
  const { mode, setMode, theme } = useThemeMode()
  const treemapRef = useRef<HTMLDivElement>(null)
  const tooltipRef = useRef<HTMLDivElement>(null)
  const rawData = treemapData as unknown as TreemapData
  const defaultData = useMemo<TreemapNode>(() => (
    rawData.root ?? (treemapData as unknown as TreemapNode)
  ), [rawData])
  const defaultSeriesKeys = useMemo<string[]>(() => (
    rawData.seriesKeys ?? []
  ), [rawData.seriesKeys])
  const [data, setData] = useState<TreemapNode>(defaultData)
  const [seriesKeys, setSeriesKeys] = useState<string[]>(defaultSeriesKeys)
  const [sizeSeries, setSizeSeries] = useState<string>('loc')
  const [colorSeries, setColorSeries] = useState<string>('porting_notes')
  const [colorMode, setColorMode] = useState<ColorMode>('global')
  const [zoomPath, setZoomPath] = useState<string[]>([])
  const [hoveredGroup, setHoveredGroup] = useState<string | null>(null)
  const [regexInput, setRegexInput] = useState<string>('')
  const [regexError, setRegexError] = useState<string>('')
  const [regexPatterns, setRegexPatterns] = useState<string[]>([])
  const [isRebuilding, setIsRebuilding] = useState<boolean>(false)
  const rebuildStartRef = useRef<number | null>(null)
  const regexCountRef = useRef<number>(0)
  const mathlibFolderRef = useRef<HTMLInputElement>(null)
  const [mathlibPath, setMathlibPath] = useState<string>('')
  const [vscodePath, setVscodePath] = useState<string>('')
  const vscodeApi = typeof window !== 'undefined'
    ? (window.__vscodeApi ?? (window.acquireVsCodeApi ? (window.__vscodeApi = window.acquireVsCodeApi()) : null))
    : null
  const isVscode = !!vscodeApi
  const isTauri = typeof window !== 'undefined' && (
    !!(window as { __TAURI__?: unknown }).__TAURI__ ||
    !!(window as { __TAURI_INTERNALS__?: unknown }).__TAURI_INTERNALS__
  )
  const pastel = useMemo(() => ([
    '#ffd8be',
    '#cde7f0',
    '#d7f3d0',
    '#f7d6e0',
    '#e6defa',
    '#ffeaa7',
    '#c9f6f4',
    '#f6f0b2',
    '#f6c9d0',
    '#d0e6ff',
    '#e7f0c3',
    '#f4e1c1',
  ]), [])
  const pastelDark = useMemo(() => ([
    '#6e3b2c',
    '#2e4a56',
    '#355843',
    '#5b2f3d',
    '#3f355f',
    '#5b4b1f',
    '#2f5656',
    '#5a5524',
    '#5a2e36',
    '#2f4058',
    '#3e4a2a',
    '#57412a',
  ]), [])
  const palette = useMemo(() => (
    theme === 'reticle' ? pastelDark : pastel
  ), [pastel, pastelDark, theme])
  const colorScale = useMemo(() => (
    theme === 'reticle'
      ? { low: '#3d7cc8', high: '#c9773a' }
      : { low: '#2d72c4', high: '#e38c4a' }
  ), [theme])

  const warnMissingMathlibPath = async () => {
    const message = 'Set a Mathlib path to open files directly in VS Code.'
    if (isVscode) {
      vscodeApi?.postMessage({ type: 'showWarning', text: message })
      return
    }
    if (isTauri) {
      try {
        const dialog = await import(/* @vite-ignore */ '@tauri-apps/plugin-dialog')
        await dialog.message(message, { title: 'Mathlib path needed', kind: 'warning' })
        return
      } catch (error) {
        console.warn('Failed to show dialog', error)
      }
    }
    window.alert(message)
  }

  const openFileTarget = (fullPath: string, link: string) => {
    if (isVscode) {
      vscodeApi?.postMessage({ type: 'openFile', path: fullPath })
      return
    }
    void openVscodeLink(link)
  }

  const openVscodeLink = async (link: string) => {
    if (isTauri) {
      try {
        const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
        await core.invoke('open_external', { url: link })
      } catch (error) {
        console.warn('Failed to open external link', error)
      }
      return
    }
    window.location.href = link
  }

  const beginRebuild = useCallback((label: string) => {
    const now = typeof performance !== 'undefined' ? performance.now() : Date.now()
    rebuildStartRef.current = now
    setIsRebuilding(true)
    console.log(`[treemap] rebuild start (${label})`)
  }, [])

  const finishRebuild = useCallback((label: string) => {
    const now = typeof performance !== 'undefined' ? performance.now() : Date.now()
    const start = rebuildStartRef.current
    setIsRebuilding(false)
    if (start !== null) {
      const durationMs = now - start
      console.log(`[treemap] rebuild end (${label}) ${durationMs.toFixed(1)}ms`)
      rebuildStartRef.current = null
    }
  }, [])

  const addRegexPattern = () => {
    const pattern = regexInput.trim()
    if (!pattern) {
      return
    }
    try {
      new RegExp(pattern)
    } catch (error) {
      setRegexError('Invalid regex')
      return
    }
    if (regexPatterns.includes(pattern)) {
      setRegexError('Regex already added')
      return
    }
    setRegexPatterns((current) => [...current, pattern])
    setRegexInput('')
    setRegexError('')
  }

  const removeRegexPattern = (pattern: string) => {
    setRegexPatterns((current) => current.filter((item) => item !== pattern))
  }

  const notifyMissingRebuildPath = async () => {
    const message = 'Set a Mathlib path before rebuilding.'
    if (isVscode) {
      vscodeApi?.postMessage({ type: 'showWarning', text: message })
      return
    }
    if (isTauri) {
      try {
        const dialog = await import(/* @vite-ignore */ '@tauri-apps/plugin-dialog')
        await dialog.message(message, { title: 'Mathlib path needed', kind: 'warning' })
        return
      } catch (error) {
        console.warn('Failed to show dialog', error)
      }
    }
    window.alert(message)
  }

  const handleRebuild = async () => {
    if (isVscode) {
      if (!vscodePath.trim()) {
        await notifyMissingRebuildPath()
        return
      }
      vscodeApi?.postMessage({ type: 'requestRebuild', path: vscodePath })
      return
    }
    if (isTauri) {
      if (!mathlibPath.trim()) {
        await notifyMissingRebuildPath()
        return
      }
      beginRebuild('tauri-manual')
      try {
        const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
        const result = await core.invoke<UploadedData>('scan_mathlib', {
          path: mathlibPath,
          regexPatterns,
        })
        if (result?.root) {
          const root = result.root
          const keys = result.seriesKeys ?? Object.keys(root.series ?? {})
          window.setTimeout(() => {
            setData(root)
            setSeriesKeys(keys)
            finishRebuild('tauri-manual')
          }, 0)
        } else {
          finishRebuild('tauri-manual')
        }
      } catch (error) {
        finishRebuild('tauri-manual')
        console.warn('Failed to rescan mathlib', error)
      }
    }
  }

  useEffect(() => {
    if (!(isVscode || isTauri)) {
      regexCountRef.current = regexPatterns.length
      return
    }
    if (regexPatterns.length > regexCountRef.current) {
      void handleRebuild()
    }
    regexCountRef.current = regexPatterns.length
  }, [handleRebuild, isTauri, isVscode, regexPatterns])

  useTreemap(
    treemapRef,
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    zoomPath,
    setZoomPath,
    palette,
    hoveredGroup,
    tooltipRef,
    colorScale,
    mathlibPath,
    openFileTarget,
    warnMissingMathlibPath,
    isTauri,
    vscodePath,
  )

  useEffect(() => {
    setHoveredGroup(null)
  }, [zoomPath])

  useEffect(() => {
    if (seriesKeys.length > 0) {
      setSizeSeries((current) => (seriesKeys.includes(current) ? current : (seriesKeys.includes('loc') ? 'loc' : seriesKeys[0])))
      setColorSeries((current) => (seriesKeys.includes(current) ? current : (seriesKeys.includes('porting_notes') ? 'porting_notes' : seriesKeys[0])))
    }
  }, [seriesKeys])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    if (isTauri) {
      setMathlibPath(window.localStorage.getItem('mathlibPath') ?? '')
    } else {
      setVscodePath(window.localStorage.getItem('vscodePath') ?? '')
    }
  }, [isTauri])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    if (isTauri) {
      window.localStorage.setItem('mathlibPath', mathlibPath)
    } else {
      window.localStorage.setItem('vscodePath', vscodePath)
    }
  }, [mathlibPath, vscodePath, isTauri])

  useEffect(() => {
    if (!isVscode) {
      return
    }
    vscodeApi?.postMessage({ type: 'setRegexPatterns', patterns: regexPatterns })
  }, [isVscode, vscodeApi, regexPatterns])

  useEffect(() => {
    if (!isVscode) {
      return
    }
    const handle = window.setTimeout(() => {
      vscodeApi?.postMessage({ type: 'setMathlibPath', path: vscodePath })
    }, 600)
    return () => {
      window.clearTimeout(handle)
    }
  }, [isVscode, vscodeApi, vscodePath])

  // Manual rebuild only; no automatic watch in Tauri.

  useEffect(() => {
    if (!mathlibFolderRef.current) {
      return
    }
    mathlibFolderRef.current.setAttribute('webkitdirectory', '')
    mathlibFolderRef.current.setAttribute('directory', '')
  }, [])

  const getMathlibFolderFromFiles = (files: FileList | null) => {
    if (!files || files.length === 0) {
      return ''
    }
    const first = files[0] as File & { path?: string; webkitRelativePath?: string }
    const relativePath = (first.webkitRelativePath ?? '').replace(/\\/g, '/')
    const nativePath = first.path ? first.path.replace(/\\/g, '/') : ''
    if (nativePath && relativePath && nativePath.endsWith(relativePath)) {
      return nativePath.slice(0, nativePath.length - relativePath.length).replace(/\/+$/, '')
    }
    if (nativePath) {
      return nativePath.replace(/\/[^/]+$/, '')
    }
    if (relativePath) {
      return relativePath.split('/')[0]
    }
    return ''
  }

  const handleMathlibFolderSelect = (event: React.ChangeEvent<HTMLInputElement>) => {
    const files = event.target.files
    if (!files || files.length === 0) {
      return
    }
    const nextPath = getMathlibFolderFromFiles(files)
    if (nextPath) {
      setMathlibPath(nextPath)
    }
    void (async () => {
      beginRebuild('file-build')
      const built = await buildTreemapFromFiles(files, regexPatterns)
      window.setTimeout(() => {
        setData(built.root)
        setSeriesKeys(built.seriesKeys)
        finishRebuild('file-build')
      }, 0)
    })()
  }

  const handlePickMathlibFolder = async () => {
    try {
      if (isTauri) {
        const dialog = await import(/* @vite-ignore */ '@tauri-apps/plugin-dialog')
        const selected = await dialog.open({
          directory: true,
          multiple: false,
        })
          if (typeof selected === 'string') {
            setMathlibPath(selected)
          }
        return
      }
      mathlibFolderRef.current?.click()
    } catch (error) {
      console.warn('Folder picker unavailable', error)
    }
  }

  const handleResetMathlibPath = () => {
    setMathlibPath('')
    setData(defaultData)
    setSeriesKeys(defaultSeriesKeys)
    setZoomPath([])
    if (isTauri) {
      void (async () => {
        try {
          const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
          await core.invoke('stop_mathlib_watch')
        } catch (error) {
          console.warn('Failed to stop mathlib watch', error)
        }
      })()
    }
  }

  const buildTreeFromEntries = (entries: UploadedEntry[]): TreemapNode => {
    const rootName = entries[0]?.path.split('/').filter(Boolean)[0] ?? 'Root'
    const rootNode: TreemapNode = { name: rootName, path: rootName, series: {}, children: [] }
    const index = new Map<string, TreemapNode>()
    index.set('', rootNode)
    for (const entry of entries) {
      const parts = entry.path.split('/').filter(Boolean)
      let currentPath = ''
      let current = rootNode
      parts.forEach((part, idx) => {
        currentPath = currentPath ? `${currentPath}/${part}` : part
        let child = index.get(currentPath)
        if (!child) {
          child = { name: part, path: currentPath, series: {}, children: [] }
          current.children = current.children ?? []
          current.children.push(child)
          index.set(currentPath, child)
        }
        if (idx === parts.length - 1) {
          child.series = entry.series
        }
        current = child
      })
    }
    const children = rootNode.children ?? []
    if (children.length === 1 && Object.keys(rootNode.series ?? {}).length === 0) {
      return children[0]
    }
    return rootNode
  }

  const applyUploadedData = useCallback((parsed: UploadedData) => {
    if (parsed.root) {
      setData(parsed.root)
      setZoomPath([])
      setSeriesKeys(parsed.seriesKeys ?? Object.keys(parsed.root.series ?? {}))
      return
    }
    if (parsed.entries) {
      const built = buildTreeFromEntries(parsed.entries)
      setData(built)
      setZoomPath([])
      const keys = new Set<string>()
      parsed.entries.forEach((entry) => {
        Object.keys(entry.series ?? {}).forEach((key) => keys.add(key))
      })
      setSeriesKeys(Array.from(keys))
    }
  }, [])


  const handleUpload = (event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0]
    if (!file) {
      return
    }
    const reader = new FileReader()
    reader.onload = () => {
      try {
        const parsed = JSON.parse(String(reader.result ?? '{}')) as UploadedData
        applyUploadedData(parsed)
      } catch (error) {
        console.error('Failed to load JSON', error)
      }
    }
    reader.readAsText(file)
  }

  const requestVsCodeJson = () => {
    vscodeApi?.postMessage({ type: 'pickJson' })
  }

  useEffect(() => {
    if (!isVscode) {
      return
    }
    vscodeApi?.postMessage({ type: 'webviewReady' })
    const handler = (event: MessageEvent) => {
      const message = event.data as {
        type?: string
        text?: string
        path?: string
        status?: string
      }
      if (message.type === 'loadJson' && typeof message.text === 'string') {
        const text = message.text
        window.setTimeout(() => {
          try {
            const parsed = JSON.parse(text) as UploadedData
            applyUploadedData(parsed)
            finishRebuild('vscode-load')
          } catch (error) {
            console.error('Failed to parse JSON from VS Code', error)
            finishRebuild('vscode-load')
          }
        }, 0)
      }
      if (message.type === 'setMathlibPath' && message.path) {
        const normalized = message.path.replace(/\/+$/, '')
        const basePath = normalized.endsWith('/Mathlib')
          ? normalized.slice(0, Math.max(0, normalized.length - '/Mathlib'.length))
          : normalized
        setVscodePath(basePath)
      }
      if (message.type === 'rebuildStatus') {
        if (message.status === 'start') {
          beginRebuild('vscode-watch')
        } else if (message.status === 'end') {
          finishRebuild('vscode-watch')
        }
      }
    }
    window.addEventListener('message', handler)
    return () => window.removeEventListener('message', handler)
  }, [applyUploadedData, beginRebuild, finishRebuild, isVscode])

  const handleReset = () => {
    setData(defaultData)
    setSeriesKeys(defaultSeriesKeys)
    setSizeSeries(defaultSeriesKeys.includes('loc') ? 'loc' : (defaultSeriesKeys[0] ?? 'loc'))
    setColorSeries(defaultSeriesKeys.includes('porting_notes') ? 'porting_notes' : (defaultSeriesKeys[0] ?? 'porting_notes'))
    setColorMode('global')
    setZoomPath([])
  }

  return (
    <div className={`page theme-${theme}`}>
      {embedded ? null : <SiteHeader mode={mode} onModeChange={setMode} />}

      {embedded ? null : (
        <section className="intro">
          <h1>TR-004 · Repo Metrics Map</h1>
          <p>Interactive treemap for any repository metrics JSON.</p>
        </section>
      )}

      <section className="samples">
        {embedded ? null : (
          <>
            <div className="panel-header">
              <div>
                <h2>Section A · Module coverage</h2>
                <p>Distribution of files and metrics across the loaded dataset.</p>
              </div>
            </div>
            <div className="panel">
              <p className="treemap-note">
                Coloring: blue → low, orange → high. Zero values are black in dark mode and white in light mode.
                Global mode scales across the visible leaves; per parent normalizes within each parent block.
              </p>
            </div>
          </>
        )}
        <div className="treemap-menu">
          {embedded ? null : (
            <>
              <label className="treemap-select">
                <span>DATA</span>
                <input type="file" accept="application/json" onChange={handleUpload} />
              </label>
              {isVscode ? (
                <button className="ghost-button" type="button" onClick={requestVsCodeJson}>
                  OPEN JSON
                </button>
              ) : null}
              {isTauri ? (
                <div className="treemap-select">
                  <span>MATHLIB PATH (mathlib)</span>
                  <button
                    className="ghost-button"
                    type="button"
                    onClick={handlePickMathlibFolder}
                  >
                    Choose Folder
                  </button>
                  <button
                    className="ghost-button"
                    type="button"
                    onClick={handleResetMathlibPath}
                  >
                    Reset
                  </button>
                  <input
                    ref={mathlibFolderRef}
                    className="treemap-hidden-input"
                    type="file"
                    onChange={handleMathlibFolderSelect}
                    aria-label="Select mathlib folder"
                  />
                  <span className="treemap-path-preview">
                    {mathlibPath || 'Choose a mathlib folder'}
                  </span>
                </div>
              ) : (
                <label className="treemap-select">
                  <span>MATHLIB PATH</span>
                  <input
                    type="text"
                    value={vscodePath}
                    onChange={(event) => setVscodePath(event.target.value)}
                    placeholder="/absolute/path/to/mathlib4"
                  />
                </label>
              )}
              <button className="ghost-button" onClick={handleReset}>
                RESET DEFAULT
              </button>
            </>
          )}
          {isVscode || isTauri ? (
            <button className="ghost-button" type="button" onClick={handleRebuild}>
              REBUILD
            </button>
          ) : null}
          <label className="treemap-select">
            <span>SIZE</span>
            <select
              value={sizeSeries}
              onChange={(event) => setSizeSeries(event.target.value)}
            >
              {seriesKeys.map((key) => (
                <option key={key} value={key}>
                  {key.replace(/_/g, ' ')}
                </option>
              ))}
            </select>
          </label>
          <label className="treemap-select">
            <span>COLOR</span>
            <select
              value={colorSeries}
              onChange={(event) => setColorSeries(event.target.value)}
            >
              {seriesKeys.map((key) => (
                <option key={key} value={key}>
                  {key.replace(/_/g, ' ')}
                </option>
              ))}
            </select>
          </label>
          <label className="treemap-select">
            <span>MODE</span>
            <select
              value={colorMode}
              onChange={(event) => setColorMode(event.target.value as ColorMode)}
            >
              <option value="global">global</option>
              <option value="per_parent">per parent</option>
            </select>
          </label>
          {isVscode || isTauri ? (
            <>
              <label className="treemap-select treemap-regex-input">
                <span>REGEX</span>
                <input
                  type="text"
                  value={regexInput}
                  onChange={(event) => {
                    setRegexInput(event.target.value)
                    if (regexError) {
                      setRegexError('')
                    }
                  }}
                  onKeyDown={(event) => {
                    if (event.key === 'Enter') {
                      event.preventDefault()
                      addRegexPattern()
                    }
                  }}
                  placeholder={String.raw`e.g. \bTODO\b`}
                />
              </label>
              <button className="ghost-button" type="button" onClick={addRegexPattern}>
                ADD REGEX
              </button>
            </>
          ) : null}
        </div>
        {isVscode || isTauri ? (
          <>
            {regexError ? <div className="treemap-regex-error">{regexError}</div> : null}
            {regexPatterns.length > 0 ? (
              <div className="treemap-regex-list">
                {regexPatterns.map((pattern) => (
                  <div key={pattern} className="treemap-regex-chip">
                    <span className="treemap-regex-label">{pattern}</span>
                    <button
                      className="ghost-button"
                      type="button"
                      onClick={() => removeRegexPattern(pattern)}
                    >
                      REMOVE
                    </button>
                  </div>
                ))}
              </div>
            ) : null}
          </>
        ) : null}
        <div className="treemap-separator" />
        <div className="treemap-breadcrumb">
          <button className="ghost-button" onClick={() => setZoomPath([])}>
            {data.name?.toUpperCase?.() ?? 'ROOT'}
          </button>
          {zoomPath.map((segment, index) => {
            const nextPath = zoomPath.slice(0, index + 1)
            return (
              <span key={`${segment}-${index}`} className="breadcrumb-item">
                <span className="breadcrumb-sep">/</span>
                <button className="ghost-button" onClick={() => setZoomPath(nextPath)}>
                  {segment}
                </button>
              </span>
            )
          })}
        </div>
        <div className="treemap-panel">
          {isRebuilding ? (
            <div className="treemap-rebuild">
              <span className="treemap-spinner" aria-hidden="true" />
              <span>Rebuilding</span>
            </div>
          ) : null}
          <div className="treemap-canvas" ref={treemapRef} />
          <div className="treemap-tooltip" ref={tooltipRef} />
        </div>
      </section>

      {embedded ? null : (
        <section className="samples">
          <div className="panel-header">
            <div>
              <h2>Section B · JSON format</h2>
              <p>Load local metrics using a simple tree schema or a flat entries list.</p>
            </div>
          </div>
          <div className="panel">
            <div className="code-block-header">
              <h3>Tree schema</h3>
              <button
                className="ghost-button"
                onClick={() => {
                  void navigator.clipboard.writeText(`{
  "root": {
    "name": "Demo",
    "series": { "foo": 210, "bar": 9 },
    "children": [
      {
        "name": "Core",
        "series": { "foo": 150, "bar": 6 },
        "children": [
          { "name": "Basics.lean", "series": { "foo": 90, "bar": 4 } },
          { "name": "Logic.lean", "series": { "foo": 60, "bar": 2 } }
        ]
      },
      { "name": "Extras", "series": { "foo": 60, "bar": 3 } }
    ]
  },
  "seriesKeys": ["foo", "bar"]
}`)
                }}
              >
                COPY
              </button>
            </div>
            <pre className="code-block">{`{
  "root": {
    "name": "Demo",
    "series": { "foo": 210, "bar": 9 },
    "children": [
      {
        "name": "Core",
        "series": { "foo": 150, "bar": 6 },
        "children": [
          { "name": "Basics.lean", "series": { "foo": 90, "bar": 4 } },
          { "name": "Logic.lean", "series": { "foo": 60, "bar": 2 } }
        ]
      },
      { "name": "Extras", "series": { "foo": 60, "bar": 3 } }
    ]
  },
  "seriesKeys": ["foo", "bar"]
}`}</pre>
            <div className="code-block-header">
              <h3>Entries schema</h3>
              <button
                className="ghost-button"
                onClick={() => {
                  void navigator.clipboard.writeText(`{
  "entries": [
    { "path": "Demo/Core/Basics.lean", "series": { "foo": 90, "bar": 4 } },
    { "path": "Demo/Core/Logic.lean", "series": { "foo": 60, "bar": 2 } },
    { "path": "Demo/Extras", "series": { "foo": 60, "bar": 3 } }
  ]
}`)
                }}
              >
                COPY
              </button>
            </div>
            <pre className="code-block">{`{
  "entries": [
    { "path": "Demo/Core/Basics.lean", "series": { "foo": 90, "bar": 4 } },
    { "path": "Demo/Core/Logic.lean", "series": { "foo": 60, "bar": 2 } },
    { "path": "Demo/Extras", "series": { "foo": 60, "bar": 3 } }
  ]
}`}</pre>
          </div>
        </section>
      )}
    </div>
  )
}
