import { useCallback, useEffect, useMemo, useRef, useState } from 'react'
import * as d3 from 'd3'
import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import '../App.css'

type TreemapNode = {
  name: string
  path?: string
  series: Record<string, number>
  kind?: string
  span?: {
    file?: string
    line?: number
    col?: number
    end_line?: number
    end_col?: number
  }
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
type CompiledRegex = { pattern: string; key: string; regex: RegExp }
type LayoutNode = {
  name: string
  path?: string
  series: Record<string, number>
  kind?: string
  span?: TreemapNode['span']
  isLeaf?: boolean
  x0: number
  y0: number
  x1: number
  y1: number
  fill: string
  parentName?: string
}
type LayoutPayload = {
  leafNodes: LayoutNode[]
  groupNodes: {
    name: string
    path?: string
    kind?: string
    depth: number
    x0: number
    y0: number
    x1: number
    y1: number
  }[]
}

type MathlibPageProps = {
  embedded?: boolean
}

type BorderMode = 'none' | 'modules' | 'modules_files'
type ColorMode = 'global' | 'per_parent'

type MetricsNode = {
  name: string
  path?: string
  kind?: string
  metrics?: Record<string, number>
  span?: TreemapNode['span']
  children?: MetricsNode[]
}

type MetricsReport = {
  schema_version?: string
  root?: MetricsNode
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

const emptyTreemapRoot: TreemapNode = {
  name: 'Mathlib',
  path: 'Mathlib',
  series: {},
  children: [],
}

const portingNoteRegex = /porting[\s_-]*note/gi
const adaptationNoteRegex = /#adaptation_note\b/gi
const jblowMetricKeys = [
  'if_density_bp',
  'if_depth_max',
  'loop_depth_max',
  'assignments',
  'global_reads',
  'global_writes',
  'heap_allocations',
  'heap_frees',
  'call_locality_module_bp',
  'call_locality_file_bp',
  'call_constancy_bp',
]

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
  const depth = segments.length

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
    return {
      ...node,
      kind: node.kind ?? 'file',
    }
  }
  const normalizedChildren = node.children.map(normalizeNode)
  return {
    ...node,
    kind: node.kind ?? 'module',
    children: normalizedChildren,
  }
}

const sanitizePath = (path?: string) => (
  path ? path.replace(/^\.\/+/, '') : path
)

const collectSeriesKeys = (node: TreemapNode, keys: Set<string>) => {
  Object.keys(node.series ?? {}).forEach((key) => keys.add(key))
  node.children?.forEach((child) => collectSeriesKeys(child, keys))
}

const buildTreeFromEntries = (entries: UploadedEntry[]): TreemapNode => {
  const rootName = entries[0]?.path.split('/').filter(Boolean)[0] ?? 'Root'
  const rootNode: TreemapNode = {
    name: rootName,
    path: rootName,
    series: {},
    children: [],
    kind: 'module',
  }
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
        const isLeaf = idx === parts.length - 1
        child = {
          name: part,
          path: currentPath,
          series: {},
          children: [],
          kind: isLeaf ? 'file' : 'module',
          isLeaf: isLeaf || undefined,
        }
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

const convertMetricsNode = (node: MetricsNode): TreemapNode => {
  const children = node.children?.map(convertMetricsNode) ?? []
  const metrics = node.metrics ?? {}
  const series: Record<string, number> = {}
  Object.entries(metrics).forEach(([key, value]) => {
    if (typeof value === 'number') {
      series[key] = value
    }
  })
  const kind = node.kind
  const isLeaf = kind === 'decl' || kind === 'command' || children.length === 0
  return {
    name: node.name,
    path: sanitizePath(node.path),
    series,
    kind,
    span: node.span,
    children: children.length > 0 ? children : undefined,
    isLeaf: isLeaf || undefined,
  }
}

const convertMetricsReport = (report: MetricsReport): TreemapData | null => {
  if (!report.root) {
    return null
  }
  const root = normalizeNode(convertMetricsNode(report.root))
  const seriesKeys = new Set<string>()
  collectSeriesKeys(root, seriesKeys)
  return { root, seriesKeys: Array.from(seriesKeys).sort() }
}

const isMetricsReport = (value: unknown): value is MetricsReport => {
  if (!value || typeof value !== 'object') {
    return false
  }
  const root = (value as { root?: unknown }).root
  if (!root || typeof root !== 'object') {
    return false
  }
  const rootObj = root as { metrics?: unknown; kind?: unknown }
  return typeof rootObj.metrics === 'object' && typeof rootObj.kind === 'string'
}

const parseTreemapPayload = (parsed: UploadedData | MetricsReport): TreemapData | null => {
  if (isMetricsReport(parsed)) {
    return convertMetricsReport(parsed)
  }
  if (parsed.root) {
    const normalized = normalizeNode(parsed.root)
    if (parsed.seriesKeys) {
      return { root: normalized, seriesKeys: parsed.seriesKeys }
    }
    const keys = new Set<string>()
    collectSeriesKeys(normalized, keys)
    return { root: normalized, seriesKeys: Array.from(keys) }
  }
  if (parsed.entries) {
    const built = normalizeNode(buildTreeFromEntries(parsed.entries))
    const keys = new Set<string>()
    parsed.entries.forEach((entry) => {
      Object.keys(entry.series ?? {}).forEach((key) => keys.add(key))
    })
    return { root: built, seriesKeys: Array.from(keys) }
  }
  return null
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
    const kind = children.length > 0 ? 'module' : 'file'
    return {
      name: node.name,
      path: node.path,
      children: children.length > 0 ? children : undefined,
      series,
      kind,
      isLeaf: children.length > 0 ? undefined : true,
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
  borderMode: BorderMode,
  theme: 'highk' | 'reticle',
  colors: string[],
  mathlibPath: string,
  openFileTarget: (fullPath: string, link: string, span?: TreemapNode['span']) => void,
  warnMissingMathlibPath: () => void,
  isTauri: boolean,
  vscodePath: string,
  onHoverLeaf: (node: LayoutNode | null) => void,
) => {
  const workerRef = useRef<Worker | null>(null)
  const requestIdRef = useRef(0)
  const [layout, setLayout] = useState<LayoutPayload | null>(null)
  const renderScale = 8

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
        width: width * renderScale,
        height: 600 * renderScale,
        colors,
      },
    })
  }, [
    containerRef,
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    colors,
  ])

  useEffect(() => {
    const container = containerRef.current
    if (!container || !layout) {
      return
    }

    const width = container.clientWidth
    const height = 600
    const scaledWidth = width * renderScale
    const scaledHeight = height * renderScale

    container.innerHTML = ''
    const svg = d3
      .select(container)
      .append('svg')
      .attr('class', 'treemap-svg')
      .attr('width', width)
      .attr('height', height)
      .attr('viewBox', `0 0 ${scaledWidth} ${scaledHeight}`)

    const g = svg.append('g').attr('class', 'treemap-zoom')
    const zoomBehavior = d3
      .zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.6, 1000])
      .on('zoom', (event) => {
        g.attr('transform', event.transform.toString())
      })
    svg.call(
      zoomBehavior as unknown as (
        selection: d3.Selection<SVGSVGElement, unknown, null, undefined>,
      ) => void,
    )
    svg.on('dblclick.zoom', null)

    const leafNodes = layout.leafNodes
    const basePath = isTauri ? mathlibPath : vscodePath
    const normalizedBasePath = basePath.trim().replace(/\/+$/, '')
    const buildFileTarget = (node: LayoutNode) => {
      const rawPath = (node.span?.file ?? node.path)?.replace(/^\/+/, '')
      if (!rawPath) {
        return null
      }
      const normalizedPath = rawPath.replace(/^\.\/+/, '')
      const hasLeanExt = normalizedPath.endsWith('.lean')
      const relativePath = hasLeanExt ? normalizedPath : `${normalizedPath}.lean`
      const isAbsolute = /^([A-Za-z]:[\\/]|\/)/.test(relativePath)
      const fullPath = isAbsolute
        ? relativePath
        : (normalizedBasePath ? `${normalizedBasePath}/${relativePath}` : null)
      if (!fullPath) {
        return null
      }
      const line = node.span?.line
      const col = node.span?.col
      const lineSuffix = typeof line === 'number' ? `:${line}:${col ?? 0}` : ''
      return { fullPath, link: `vscode://file/${encodeURI(fullPath)}${lineSuffix}`, span: node.span }
    }

    g
      .selectAll('rect')
      .data(leafNodes)
      .enter()
      .append('rect')
      .attr('x', (d) => d.x0)
      .attr('y', (d) => d.y0)
      .attr('width', (d) => d.x1 - d.x0)
      .attr('height', (d) => d.y1 - d.y0)
      .attr('class', 'treemap-rect treemap-child')
      .attr('fill', (d) => d.fill)
      .style('stroke-width', (d) => (
        borderMode === 'modules_files' && d.kind === 'file' ? 1 : 0
      ))
      .on('click', (_, d) => {
        const target = buildFileTarget(d)
        if (target) {
          void openFileTarget(target.fullPath, target.link, target.span)
        } else {
          void warnMissingMathlibPath()
        }
      })
      .on('mousemove', (_, d) => {
        onHoverLeaf(d)
      })
      .on('mouseout', () => {
        onHoverLeaf(null)
      })

    const wantsModuleBorders = borderMode === 'modules' || borderMode === 'modules_files'
    const wantsFileBorders = borderMode === 'modules_files'
    if (wantsModuleBorders || wantsFileBorders) {
      const borderNodes = layout.groupNodes.filter((node) => {
        const kind = node.kind ?? 'module'
        if (kind === 'file') {
          return wantsFileBorders
        }
        return wantsModuleBorders
      })
      g
        .append('g')
        .attr('class', 'treemap-borders')
        .selectAll('rect')
        .data(borderNodes)
        .enter()
        .append('rect')
        .attr('x', (d) => d.x0)
        .attr('y', (d) => d.y0)
        .attr('width', (d) => d.x1 - d.x0)
        .attr('height', (d) => d.y1 - d.y0)
        .attr('class', (d) => `treemap-border treemap-border-${d.kind ?? 'module'}`)
        .style('pointer-events', 'none')
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
    borderMode,
    theme,
    colors,
    mathlibPath,
    openFileTarget,
    warnMissingMathlibPath,
    isTauri,
    vscodePath,
    onHoverLeaf,
    layout,
  ])
}

export const MathlibPage = ({ embedded = false }: MathlibPageProps) => {
  const { mode, setMode, theme } = useThemeMode()
  const treemapRef = useRef<HTMLDivElement>(null)
  const hasCustomDataRef = useRef(false)
  const [defaultData, setDefaultData] = useState<TreemapNode>(emptyTreemapRoot)
  const [defaultSeriesKeys, setDefaultSeriesKeys] = useState<string[]>([])
  const [data, setData] = useState<TreemapNode>(emptyTreemapRoot)
  const [seriesKeys, setSeriesKeys] = useState<string[]>([])
  const [isDefaultLoading, setIsDefaultLoading] = useState<boolean>(true)
  const [sizeSeries, setSizeSeries] = useState<string>('loc')
  const [colorSeries, setColorSeries] = useState<string>('porting_notes')
  const [colorMode, setColorMode] = useState<ColorMode>('global')
  const [borderMode, setBorderMode] = useState<BorderMode>('none')
  const [blendWeights, setBlendWeights] = useState<Record<string, number>>({})
  const [hoveredLeaf, setHoveredLeaf] = useState<LayoutNode | null>(null)
  const [regexInput, setRegexInput] = useState<string>('')
  const [regexError, setRegexError] = useState<string>('')
  const [regexPatterns, setRegexPatterns] = useState<string[]>([])
  const [isRebuilding, setIsRebuilding] = useState<boolean>(false)
  const rebuildStartRef = useRef<number | null>(null)
  const regexCountRef = useRef<number>(0)
  const mathlibFolderRef = useRef<HTMLInputElement>(null)
  const isTauri = typeof window !== 'undefined' && (
    !!(window as { __TAURI__?: unknown }).__TAURI__ ||
    !!(window as { __TAURI_INTERNALS__?: unknown }).__TAURI_INTERNALS__
  )
  const [mathlibPath, setMathlibPath] = useState<string>('')
  const [vscodePath, setVscodePath] = useState<string>('')
  const [mathlibPathLoaded, setMathlibPathLoaded] = useState<boolean>(!isTauri)
  const vscodeApi = typeof window !== 'undefined'
    ? (window.__vscodeApi ?? (window.acquireVsCodeApi ? (window.__vscodeApi = window.acquireVsCodeApi()) : null))
    : null
  const isVscode = !!vscodeApi
  const showPrimaryControls = !embedded || !isTauri
  const showHeader = !embedded || (!isTauri && !isVscode)
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
  const blendKeys = useMemo(() => (
    jblowMetricKeys.filter((key) => seriesKeys.includes(key))
  ), [seriesKeys])
  const blendActive = useMemo(() => (
    Object.values(blendWeights).some((value) => value !== 0)
  ), [blendWeights])

  useEffect(() => {
    if (typeof window === 'undefined') {
      setIsDefaultLoading(false)
      return
    }
    let active = true
    const loadDefault = async () => {
      try {
        const url = new URL('./mathlib_treemap.json', window.location.href)
        const response = await fetch(url.toString())
        if (!response.ok) {
          throw new Error(`Failed to load default treemap data: ${response.status}`)
        }
        const parsed = await response.json() as UploadedData | MetricsReport
        const normalized = parseTreemapPayload(parsed)
        if (!normalized || !active) {
          return
        }
        setDefaultData(normalized.root)
        setDefaultSeriesKeys(normalized.seriesKeys)
        if (!hasCustomDataRef.current) {
          setData(normalized.root)
          setSeriesKeys(normalized.seriesKeys)
        }
      } catch (error) {
        console.warn('Failed to load default treemap data', error)
      } finally {
        if (active) {
          setIsDefaultLoading(false)
        }
      }
    }
    void loadDefault()
    return () => {
      active = false
    }
  }, [])

  useEffect(() => {
    if (blendKeys.length === 0) {
      setBlendWeights({})
      return
    }
    setBlendWeights((current) => {
      const next: Record<string, number> = {}
      blendKeys.forEach((key) => {
        next[key] = current[key] ?? 0
      })
      return next
    })
  }, [blendKeys])

  const blendedData = useMemo(() => {
    if (!blendActive) {
      return data
    }
    const applyBlend = (node: TreemapNode): TreemapNode => {
      const children = node.children?.map(applyBlend)
      const series = { ...node.series }
      let blendValue = 0
      Object.entries(blendWeights).forEach(([key, weight]) => {
        if (weight === 0) {
          return
        }
        const value = series[key]
        if (typeof value === 'number') {
          blendValue += value * weight
        }
      })
      series.blend = blendValue
      return {
        ...node,
        series,
        children,
      }
    }
    return applyBlend(data)
  }, [blendActive, blendWeights, data])

  const activeSeriesKeys = useMemo(() => {
    if (!blendActive) {
      return seriesKeys
    }
    return seriesKeys.includes('blend')
      ? seriesKeys
      : ['blend', ...seriesKeys]
  }, [blendActive, seriesKeys])

  const warnMissingMathlibPath = useCallback(async () => {
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
  }, [isTauri, isVscode, vscodeApi])

  const openVscodeLink = useCallback(async (link: string) => {
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
  }, [isTauri])

  const openFileTarget = useCallback((fullPath: string, link: string, span?: TreemapNode['span']) => {
    if (isVscode) {
      vscodeApi?.postMessage({
        type: 'openFile',
        path: fullPath,
        line: span?.line,
        col: span?.col,
      })
      return
    }
    void openVscodeLink(link)
  }, [isVscode, openVscodeLink, vscodeApi])

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
            hasCustomDataRef.current = true
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
    blendedData,
    sizeSeries,
    colorSeries,
    colorMode,
    borderMode,
    theme,
    palette,
    mathlibPath,
    openFileTarget,
    warnMissingMathlibPath,
    isTauri,
    vscodePath,
    setHoveredLeaf,
  )

  useEffect(() => {
    if (activeSeriesKeys.length > 0) {
      setSizeSeries((current) => {
        if (activeSeriesKeys.includes(current)) {
          return current
        }
        if (activeSeriesKeys.includes('infotree_nodes_total')) {
          return 'infotree_nodes_total'
        }
        if (activeSeriesKeys.includes('loc')) {
          return 'loc'
        }
        return activeSeriesKeys[0]
      })
      setColorSeries((current) => {
        if (activeSeriesKeys.includes(current)) {
          return current
        }
        if (activeSeriesKeys.includes('infotree_tactic_state_items')) {
          return 'infotree_tactic_state_items'
        }
        if (activeSeriesKeys.includes('infotree_diagnostic_items')) {
          return 'infotree_diagnostic_items'
        }
        if (activeSeriesKeys.includes('porting_notes')) {
          return 'porting_notes'
        }
        return activeSeriesKeys[0]
      })
    }
  }, [activeSeriesKeys])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    if (isTauri) {
      let active = true
      const loadPath = async () => {
        try {
          const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
          const stored = await core.invoke<string | null>('load_mathlib_path')
          if (active && stored) {
            setMathlibPath(stored)
            setMathlibPathLoaded(true)
            return
          }
        } catch (error) {
          console.warn('Failed to load mathlib path from Tauri storage', error)
        }
        if (active) {
          setMathlibPath(window.localStorage.getItem('mathlibPath') ?? '')
          setMathlibPathLoaded(true)
        }
      }
      void loadPath()
      return () => {
        active = false
      }
    } else {
      setVscodePath(window.localStorage.getItem('vscodePath') ?? '')
    }
  }, [isTauri])

  useEffect(() => {
    if (typeof window === 'undefined') {
      return
    }
    if (isTauri) {
      if (!mathlibPathLoaded) {
        return
      }
      const savePath = async () => {
        try {
          const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
          await core.invoke('save_mathlib_path', { path: mathlibPath })
        } catch (error) {
          console.warn('Failed to save mathlib path to Tauri storage', error)
          window.localStorage.setItem('mathlibPath', mathlibPath)
        }
      }
      void savePath()
    } else {
      window.localStorage.setItem('vscodePath', vscodePath)
    }
  }, [mathlibPath, mathlibPathLoaded, vscodePath, isTauri])

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
        hasCustomDataRef.current = true
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
    hasCustomDataRef.current = false
    setData(defaultData)
    setSeriesKeys(defaultSeriesKeys)
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

  const applyUploadedData = useCallback((parsed: UploadedData | MetricsReport) => {
    const normalized = parseTreemapPayload(parsed)
    if (!normalized) {
      return
    }
    setData(normalized.root)
    setSeriesKeys(normalized.seriesKeys)
    hasCustomDataRef.current = true
  }, [])


  const handleUpload = (event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0]
    if (!file) {
      return
    }
    const reader = new FileReader()
    reader.onload = () => {
      try {
        const parsed = JSON.parse(String(reader.result ?? '{}')) as UploadedData | MetricsReport
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
            const parsed = JSON.parse(text) as UploadedData | MetricsReport
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
    hasCustomDataRef.current = false
    setData(defaultData)
    setSeriesKeys(defaultSeriesKeys)
    setSizeSeries(defaultSeriesKeys.includes('infotree_nodes_total')
      ? 'infotree_nodes_total'
      : (defaultSeriesKeys.includes('loc') ? 'loc' : (defaultSeriesKeys[0] ?? 'loc')))
    setColorSeries(defaultSeriesKeys.includes('infotree_tactic_state_items')
      ? 'infotree_tactic_state_items'
      : (defaultSeriesKeys.includes('infotree_diagnostic_items')
        ? 'infotree_diagnostic_items'
        : (defaultSeriesKeys.includes('porting_notes')
          ? 'porting_notes'
          : (defaultSeriesKeys[0] ?? 'porting_notes'))))
    setColorMode('global')
    setBorderMode('none')
    setBlendWeights({})
  }

  const formatMetricValue = (key: string, value: number | undefined) => {
    if (value === undefined) {
      return '0'
    }
    if (key === 'comment_ratio') {
      return value.toFixed(6)
    }
    if (key.endsWith('_bp')) {
      return (value / 10000).toFixed(4)
    }
    if (key === 'blend') {
      return value.toFixed(3)
    }
    return value
  }

  const metricValueWidth = (key: string) => {
    switch (key) {
      case 'comment_ratio':
        return '10ch'
      case 'blend':
        return '9ch'
      case 'code_lines':
        return '6ch'
      case 'loc':
        return '7ch'
      case 'bytes':
        return '7ch'
      default:
        if (key.endsWith('_bp')) {
          return '7ch'
        }
        return '4ch'
    }
  }

  return (
    <div className={`page theme-${theme}`}>
      {showHeader ? <SiteHeader mode={mode} onModeChange={setMode} /> : null}

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
                Coloring: blue → low, orange → high. Zero values are dark red in dark mode and bright red in light mode.
                Global mode scales across the visible leaves; per parent normalizes within each parent block.
              </p>
            </div>
          </>
        )}
        <div className="treemap-menu">
          {showPrimaryControls ? (
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
          ) : null}
          {embedded && isTauri ? (
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
          ) : null}
          {isVscode || isTauri ? (
            <button className="ghost-button" type="button" onClick={handleRebuild}>
              REBUILD
            </button>
          ) : null}
          <>
            <label className="treemap-select">
              <span>SIZE</span>
              <select
                value={sizeSeries}
                onChange={(event) => setSizeSeries(event.target.value)}
              >
                {activeSeriesKeys.map((key) => (
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
                {activeSeriesKeys.map((key) => (
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
            <label className="treemap-select">
              <span>BORDERS</span>
              <select
                value={borderMode}
                onChange={(event) => setBorderMode(event.target.value as BorderMode)}
              >
                <option value="none">none</option>
                <option value="modules">modules</option>
                <option value="modules_files">modules + files</option>
              </select>
            </label>
            {!embedded && (isVscode || isTauri) ? (
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
          </>
        </div>
        {blendKeys.length > 0 ? (
          <div className="treemap-blend">
            <div className="treemap-blend-header">
              <span>BLEND WEIGHTS</span>
              <button
                className="ghost-button"
                type="button"
                onClick={() => {
                  setBlendWeights(() => {
                    const next: Record<string, number> = {}
                    blendKeys.forEach((key) => {
                      next[key] = 0
                    })
                    return next
                  })
                }}
              >
                RESET
              </button>
            </div>
            <div className="treemap-blend-grid">
              {blendKeys.map((key) => (
                <label key={key} className="treemap-blend-item">
                  <span>{key.replace(/_/g, ' ')}</span>
                  <input
                    type="number"
                    step="0.1"
                    value={blendWeights[key] ?? 0}
                    onChange={(event) => {
                      const nextValue = Number(event.target.value)
                      setBlendWeights((current) => ({
                        ...current,
                        [key]: Number.isFinite(nextValue) ? nextValue : 0,
                      }))
                    }}
                  />
                </label>
              ))}
            </div>
          </div>
        ) : null}
        {!embedded && (isVscode || isTauri) ? (
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
        <div className="treemap-panel">
          {isRebuilding ? (
            <div className="treemap-rebuild">
              <span className="treemap-spinner" aria-hidden="true" />
              <span>Rebuilding</span>
            </div>
          ) : null}
          {isDefaultLoading ? (
            <div className="treemap-rebuild">
              <span className="treemap-spinner" aria-hidden="true" />
              <span>Loading default dataset</span>
            </div>
          ) : null}
          <div className="treemap-canvas" ref={treemapRef} />
        </div>
        <div className="treemap-readout">
          <span className={`treemap-readout-path${hoveredLeaf ? '' : ' treemap-readout-empty'}`}>
            {hoveredLeaf ? (hoveredLeaf.path ?? hoveredLeaf.name) : 'Hover a leaf to see metrics'}
          </span>
          <span className="treemap-readout-metrics">
            {activeSeriesKeys.map((key) => {
              if (key === 'file_count' || key.startsWith('infotree_')) {
                return null
              }
              const value = hoveredLeaf?.series?.[key]
              const formattedValue = formatMetricValue(key, value)
              return (
                <span
                  key={key}
                  className={`treemap-readout-item${hoveredLeaf ? '' : ' treemap-readout-empty'}`}
                >
                  <span className="treemap-readout-key">{key.replace(/_/g, ' ')}</span>
                  <span className="treemap-readout-sep">:</span>
                  <span
                    className="treemap-readout-value"
                    style={{ minWidth: metricValueWidth(key) }}
                  >
                    {formattedValue}
                  </span>
                </span>
              )
            })}
          </span>
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
