import { useEffect, useMemo, useRef, useState } from 'react'
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
type ColorMode = 'absolute' | 'relative'
type ColorScale = { low: string; high: string }

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
}

const MAX_DEPTH = 5
const MIN_PERCENT = 0.01
const GROUP_BY = 'loc'
const portingNoteRegex = /porting[\s_-]*note/gi
const adaptationNoteRegex = /#adaptation_note\b/gi

const analyzeLeanContent = (content: string) => {
  const lines = content.split(/\r\n|\r|\n/)
  const loc = lines.length
  const portingNotes = Array.from(content.matchAll(portingNoteRegex)).length
  const adaptationNotes = Array.from(content.matchAll(adaptationNoteRegex)).length
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

const buildTreemapFromFiles = async (files: FileList) => {
  const root = makeRootNode()
  const firstRelative = Array.from(files)[0]?.webkitRelativePath?.replace(/\\/g, '/') ?? ''
  const baseFolder = firstRelative.includes('/') ? firstRelative.split('/')[0] : ''
  const readFiles = Array.from(files)
    .filter((file) => file.name.endsWith('.lean'))
    .map(async (file) => {
      const content = await file.text()
      const metrics = analyzeLeanContent(content)
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
    return {
      name: node.name,
      path: node.path,
      children: children.length > 0 ? children : undefined,
      series: {
        bytes: node.size,
        file_count: node.count,
        loc: node.loc,
        comment_lines: node.commentLines,
        code_lines: node.codeLines,
        comment_ratio: commentRatio,
        porting_notes: node.portingNotes,
        adaptation_notes: node.adaptationNotes,
        notes_total: node.noteTotal,
      },
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
  openVscodeLink: (link: string, fallbackPath?: string) => void,
  isTauri: boolean,
  vscodePath: string,
) => {
  useEffect(() => {
    const container = containerRef.current
    if (!container) {
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

    const valueForSeries = (node: TreemapNode, key: string) => node.series?.[key] ?? 0

    const root = d3
      .hierarchy<TreemapNode>(data)
      .sum((d) => valueForSeries(d, sizeSeries))
      .sort((a, b) => (b.value ?? 0) - (a.value ?? 0))

    const findNode = (node: d3.HierarchyNode<TreemapNode>, path: string[]) => {
      let current = node
      for (const segment of path) {
        const next = current.children?.find((child) => child.data.name === segment)
        if (!next) {
          return current
        }
        current = next
      }
      return current
    }

    const zoomRoot = findNode(root, zoomPath)
    const topLevel = zoomRoot.children ?? []

    const displayRoot = d3.hierarchy({
      name: zoomRoot.data.name,
      path: zoomRoot.data.path,
      children: topLevel.map((child) => {
        const grandChildren = child.children ?? []
        if (grandChildren.length === 0) {
          return {
            name: child.data.name,
            path: child.data.path,
            series: child.data.series ?? {},
            isLeaf: true,
          }
        }
        return {
          name: child.data.name,
          path: child.data.path,
          children: grandChildren.map((g) => ({
            name: g.data.name,
            path: g.data.path,
            series: g.data.series ?? {},
            isLeaf: !(g.children && g.children.length > 0),
          })),
          isLeaf: false,
        }
      }),
    } as TreemapNode)

    displayRoot.sum((d) => valueForSeries(d, sizeSeries))
    const tiledRoot = d3
      .treemap<TreemapNode>()
      .size([width, height])
      .paddingOuter(2)
      .paddingInner(3)
      .paddingTop((d) => (d.depth === 1 ? 18 : 2))(displayRoot)

    const relativeValue = (
      node: d3.HierarchyNode<TreemapNode>,
    ) => {
      const parent = node.parent
      if (!parent?.children?.length) {
        return valueForSeries(node.data, colorSeries)
      }
      const total = parent.children.reduce(
        (sum, child) => sum + valueForSeries(child.data, colorSeries),
        0,
      )
      if (total <= 0) {
        return 0
      }
      return valueForSeries(node.data, colorSeries) / total
    }

    const colorIndexByName = new Map(
      topLevel.map((child, index) => [child.data.name, index]),
    )
    const color = (name: string) => {
      const index = colorIndexByName.get(name) ?? 0
      return colors[index % colors.length]
    }
    const colorMax = Math.max(
      0,
      ...topLevel.map((child) => (
        colorMode === 'relative'
          ? relativeValue(child)
          : valueForSeries(child.data, colorSeries)
      )),
    )
    const colorScaleFn = d3
      .scaleLinear<string>()
      .domain([0, colorMax || 1])
      .range([colorScale.low, colorScale.high])

    const fillForNode = (
      node: d3.HierarchyRectangularNode<TreemapNode>,
      fallbackName: string,
    ) => {
      const seriesValue = colorMode === 'relative'
        ? relativeValue(node)
        : valueForSeries(node.data, colorSeries)
      if (seriesValue <= 0) {
        return theme === 'reticle' ? '#000000' : '#ffffff'
      }
      if (!Number.isFinite(seriesValue)) {
        return color(fallbackName)
      }
      return colorScaleFn(seriesValue)
    }

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

    const labelSuffix = sizeSeries.replace(/_/g, ' ')

    const parentNodes = tiledRoot.descendants().filter((d) => d.depth === 1)
    const childNodes = tiledRoot.descendants().filter((d) => d.depth === 2)
    const basePath = isTauri ? mathlibPath : vscodePath
    const normalizedBasePath = basePath.trim().replace(/\/+$/, '')
    const buildVscodeLink = (node: d3.HierarchyRectangularNode<TreemapNode>) => {
      if (!normalizedBasePath) {
        return null
      }
      const nodePath = node.data.path?.replace(/^\/+/, '')
      if (!nodePath) {
        return null
      }
      const fullPath = `${normalizedBasePath}/${nodePath}.lean`
      return `vscode://file/${encodeURI(fullPath)}`
    }

    const parents = svg.selectAll('g.parent').data(parentNodes).enter().append('g').attr('class', 'parent')
    parents
      .append('rect')
      .attr('x', (d) => d.x0)
      .attr('y', (d) => d.y0)
      .attr('width', (d) => d.x1 - d.x0)
      .attr('height', (d) => d.y1 - d.y0)
      .attr('class', 'treemap-rect treemap-parent')
      .classed('is-leaf', (d) => !!d.data.isLeaf)
      .classed('is-folder', (d) => !d.data.isLeaf)
      .attr('fill', (d) => fillForNode(d, d.data.name))

      .attr('data-group', (d) => d.data.name)
      .on('click', (_, d) => {
        if (d.data.isLeaf) {
          const link = buildVscodeLink(d)
          if (link) {
            void openVscodeLink(link, d.data.path)
            return
          }
          if (!isTauri) {
            void openVscodeLink('about:blank', d.data.path)
            return
          }
        }
        setZoomPath([...zoomPath, d.data.name])
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mousemove', (event, d) => {
        const label = [...zoomPath, d.data.name].filter(Boolean)
        const sizeValue = d.data ? valueForSeries(d.data, sizeSeries) : d.value ?? 0
        const colorValue = d.data ? valueForSeries(d.data, colorSeries) : 0
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
      .text((d) => d.data.name)

    const nodes = svg.selectAll('g.child').data(childNodes).enter().append('g').attr('class', 'child')

    const clipId = (_: d3.HierarchyRectangularNode<TreemapNode>, i: number) => (
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
      .classed('is-leaf', (d) => !!d.data.isLeaf)
      .classed('is-folder', (d) => !d.data.isLeaf)
      .attr('fill', (d) => fillForNode(d, d.parent?.data.name ?? ''))
      .attr('data-group', (d) => d.parent?.data.name ?? '')
      .on('click', (_, d) => {
        if (d.data.isLeaf) {
          const link = buildVscodeLink(d)
          if (link) {
            void openVscodeLink(link, d.data.path)
            return
          }
          if (!isTauri) {
            void openVscodeLink('about:blank', d.data.path)
            return
          }
        }
        const parent = d.parent?.data.name
        if (parent) {
          setZoomPath([...zoomPath, parent, d.data.name])
        }
      })
      .on('mousemove', (event, d) => {
        const parent = d.parent?.data.name ?? ''
        const label = [...zoomPath, parent, d.data.name].filter(Boolean)
        const sizeValue = d.data ? valueForSeries(d.data, sizeSeries) : d.value ?? 0
        const colorValue = d.data ? valueForSeries(d.data, colorSeries) : 0
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
      .text((d) => d.data.name)
      .style('display', (d) => (
        (d.x1 - d.x0 < 28 || d.y1 - d.y0 < 14) ? 'none' : 'block'
      ))

    if (hoveredGroup) {
      svg
        .selectAll<SVGRectElement, d3.HierarchyRectangularNode<TreemapNode>>('.treemap-child')
        .classed('is-dim', (d) => (d.parent?.data.name ?? '') !== hoveredGroup)
        .classed('is-group-hovered', (d) => (d.parent?.data.name ?? '') === hoveredGroup)
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
    openVscodeLink,
    isTauri,
    vscodePath,
  ])
}

export const MathlibPage = () => {
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
  const [colorMode, setColorMode] = useState<ColorMode>('absolute')
  const [zoomPath, setZoomPath] = useState<string[]>([])
  const [hoveredGroup, setHoveredGroup] = useState<string | null>(null)
  const mathlibFolderRef = useRef<HTMLInputElement>(null)
  const [mathlibPath, setMathlibPath] = useState<string>('')
  const [vscodePath, setVscodePath] = useState<string>('')
  const isTauri = typeof window !== 'undefined' && (
    !!(window as { __TAURI__?: unknown }).__TAURI__ ||
    !!(window as { __TAURI_INTERNALS__?: unknown }).__TAURI_INTERNALS__
  )
  const pastel = [
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
  ]
  const pastelDark = [
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
  ]
  const palette = theme === 'reticle' ? pastelDark : pastel
  const colorScale = theme === 'reticle'
    ? { low: '#3d7cc8', high: '#c9773a' }
    : { low: '#2d72c4', high: '#e38c4a' }

  const openVscodeLink = async (link: string, fallbackPath?: string) => {
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
    openVscodeLink,
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
    if (!isTauri) {
      return
    }
    let unlisten: (() => void) | null = null
    void (async () => {
      const event = await import(/* @vite-ignore */ '@tauri-apps/api/event')
      unlisten = await event.listen<UploadedData>('mathlib:treemap-updated', (event) => {
        const payload = event.payload
        if (payload?.root) {
          setData(payload.root)
          setSeriesKeys(payload.seriesKeys ?? Object.keys(payload.root.series ?? {}))
          setZoomPath([])
        }
      })
    })()
    return () => {
      if (unlisten) {
        unlisten()
      }
      void (async () => {
        try {
          const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
          await core.invoke('stop_mathlib_watch')
        } catch (error) {
          console.warn('Failed to stop mathlib watch', error)
        }
      })()
    }
  }, [isTauri])

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
      const built = await buildTreemapFromFiles(files)
      setData(built.root)
      setSeriesKeys(built.seriesKeys)
      setZoomPath([])
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
          const core = await import(/* @vite-ignore */ '@tauri-apps/api/core')
          const result = await core.invoke<UploadedData>('scan_mathlib', { path: selected })
          if (result?.root) {
            setData(result.root)
            setSeriesKeys(result.seriesKeys ?? Object.keys(result.root.series ?? {}))
            setZoomPath([])
          }
          await core.invoke('start_mathlib_watch', { path: selected, debounceMs: 1200 })
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

  const handleUpload = (event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0]
    if (!file) {
      return
    }
    const reader = new FileReader()
    reader.onload = () => {
      try {
        const parsed = JSON.parse(String(reader.result ?? '{}')) as UploadedData
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
      } catch (error) {
        console.error('Failed to load JSON', error)
      }
    }
    reader.readAsText(file)
  }

  const handleReset = () => {
    setData(defaultData)
    setSeriesKeys(defaultSeriesKeys)
    setSizeSeries(defaultSeriesKeys.includes('loc') ? 'loc' : (defaultSeriesKeys[0] ?? 'loc'))
    setColorSeries(defaultSeriesKeys.includes('porting_notes') ? 'porting_notes' : (defaultSeriesKeys[0] ?? 'porting_notes'))
    setColorMode('absolute')
    setZoomPath([])
  }

  return (
    <div className={`page theme-${theme}`}>
      <SiteHeader mode={mode} onModeChange={setMode} />

      <section className="intro">
        <h1>TR-004 · Repo Metrics Map</h1>
        <p>Interactive treemap for any repository metrics JSON.</p>
      </section>

      <section className="samples">
        <div className="panel-header">
          <div>
            <h2>Section A · Module coverage</h2>
            <p>Distribution of files and metrics across the loaded dataset.</p>
          </div>
        </div>
        <div className="panel">
          <p className="treemap-note">
            Coloring: blue → low, orange → high. Zero values are black in dark mode and white in light mode.
            Relative mode normalizes within siblings; absolute mode uses raw values.
          </p>
        </div>
        <div className="treemap-menu">
          <label className="treemap-select">
            <span>DATA</span>
            <input type="file" accept="application/json" onChange={handleUpload} />
          </label>
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
              <option value="absolute">absolute</option>
              <option value="relative">relative</option>
            </select>
          </label>
        </div>
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
          <div className="treemap-canvas" ref={treemapRef} />
          <div className="treemap-tooltip" ref={tooltipRef} />
        </div>
      </section>

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
    </div>
  )
}
