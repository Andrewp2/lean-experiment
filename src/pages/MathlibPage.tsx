import { useEffect, useMemo, useRef, useState } from 'react'
import * as d3 from 'd3'
import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import treemapData from '../assets/mathlib_treemap.json'
import '../App.css'

type TreemapNode = {
  name: string
  value?: number
  count?: number
  loc?: number
  commentLines?: number
  codeLines?: number
  portingNotes?: number
  adaptationNotes?: number
  noteTotal?: number
  children?: TreemapNode[]
  isLeaf?: boolean
}

type TreemapMode = 'size' | 'count' | 'porting' | 'adaptation' | 'notes' | 'comments'
type PortingScale = { low: string; high: string }

const useTreemap = (
  containerRef: React.RefObject<HTMLDivElement>,
  data: TreemapNode,
  mode: TreemapMode,
  zoomPath: string[],
  setZoomPath: (path: string[]) => void,
  colors: string[],
  hoveredGroup: string | null,
  tooltipRef: React.RefObject<HTMLDivElement>,
  portingScale: PortingScale,
  commentScale: PortingScale,
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

    const valueForMode = (node: TreemapNode) => {
      if (mode === 'count') {
        return node.count ?? 0
      }
      if (mode === 'porting' || mode === 'adaptation' || mode === 'notes' || mode === 'comments') {
        return node.loc ?? 0
      }
      return node.value ?? 0
    }

    const root = d3
      .hierarchy<TreemapNode>(data)
      .sum((d) => valueForMode(d))
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
    const noteMode = mode === 'porting' || mode === 'adaptation' || mode === 'notes'
    const noteValueForMode = (node: TreemapNode) => {
      if (mode === 'adaptation') {
        return node.adaptationNotes ?? 0
      }
      if (mode === 'notes') {
        return node.noteTotal ?? 0
      }
      return node.portingNotes ?? 0
    }
    const commentRatio = (node: TreemapNode) => {
      const comments = node.commentLines ?? 0
      const code = node.codeLines ?? 0
      if (comments + code === 0) {
        return 0
      }
      return comments / Math.max(1, code)
    }

    const topLevel = (zoomRoot.children ?? [])
      .filter((child) => (noteMode ? noteValueForMode(child.data) > 0 : true))
      .sort((a, b) => {
        if (noteMode) {
          return noteValueForMode(b.data) - noteValueForMode(a.data)
        }
        return (b.value ?? 0) - (a.value ?? 0)
      })

    const displayRoot = d3.hierarchy({
      name: zoomRoot.data.name,
      children: topLevel.map((child) => {
        const grandChildren = child.children ?? []
        if (grandChildren.length === 0) {
          return {
            name: child.data.name,
            value: child.data.value ?? 0,
            count: child.data.count ?? 0,
            loc: child.data.loc ?? 0,
            commentLines: child.data.commentLines ?? 0,
            codeLines: child.data.codeLines ?? 0,
            portingNotes: child.data.portingNotes ?? 0,
            adaptationNotes: child.data.adaptationNotes ?? 0,
            noteTotal: child.data.noteTotal ?? 0,
            isLeaf: true,
          }
        }
        const filteredGrandChildren = (noteMode
          ? grandChildren.filter((g) => noteValueForMode(g.data) > 0)
          : grandChildren
        ).sort((a, b) => {
          if (noteMode) {
            return noteValueForMode(b.data) - noteValueForMode(a.data)
          }
          return (b.value ?? 0) - (a.value ?? 0)
        })
        return {
          name: child.data.name,
          children: filteredGrandChildren.map((g) => ({
            name: g.data.name,
            value: g.data.value ?? 0,
            count: g.data.count ?? 0,
            loc: g.data.loc ?? 0,
            commentLines: g.data.commentLines ?? 0,
            codeLines: g.data.codeLines ?? 0,
            portingNotes: g.data.portingNotes ?? 0,
            adaptationNotes: g.data.adaptationNotes ?? 0,
            noteTotal: g.data.noteTotal ?? 0,
            isLeaf: !(g.children && g.children.length > 0),
          })),
          isLeaf: false,
        }
      }),
    } as TreemapNode)

    displayRoot.sum((d) => valueForMode(d))
    const tiledRoot = d3
      .treemap<TreemapNode>()
      .size([width, height])
      .paddingOuter(2)
      .paddingInner(3)
      .paddingTop((d) => (d.depth === 1 ? 18 : 2))(displayRoot)

    const colorIndexByName = new Map(
      topLevel.map((child, index) => [child.data.name, index]),
    )
    const color = (name: string) => {
      const index = colorIndexByName.get(name) ?? 0
      return colors[index % colors.length]
    }
    const portingMax = Math.max(0, ...topLevel.map((child) => noteValueForMode(child.data)))
    const portingScaleFn = d3
      .scaleLinear<string>()
      .domain([0, portingMax || 1])
      .range([portingScale.low, portingScale.high])
    const commentMax = Math.max(0, ...topLevel.map((child) => commentRatio(child.data)))
    const commentScaleFn = d3
      .scaleLinear<string>()
      .domain([0, commentMax || 1])
      .range([commentScale.low, commentScale.high])

    const fillForNode = (node: TreemapNode, fallbackName: string) => {
      if (mode === 'porting' || mode === 'adaptation' || mode === 'notes') {
        return portingScaleFn(noteValueForMode(node))
      }
      if (mode === 'comments') {
        return commentScaleFn(commentRatio(node))
      }
      return color(fallbackName)
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

    const labelSuffix = mode === 'count'
      ? 'files'
      : (mode === 'porting' || mode === 'adaptation' || mode === 'notes' || mode === 'comments')
        ? 'loc'
        : 'bytes'

    const parentNodes = tiledRoot.descendants().filter((d) => d.depth === 1)
    const childNodes = tiledRoot.descendants().filter((d) => d.depth === 2)

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
      .attr('fill', (d) => (d.data.isLeaf ? fillForNode(d.data, d.data.name) : 'none'))
      .attr('data-group', (d) => d.data.name)
      .on('click', (_, d) => {
        setZoomPath([...zoomPath, d.data.name])
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mousemove', (event, d) => {
        const label = [...zoomPath, d.data.name].filter(Boolean)
        if (mode === 'porting' || mode === 'adaptation' || mode === 'notes') {
          const loc = d.data.loc ?? 0
          const notes = noteValueForMode(d.data)
          const notesLabel = mode === 'adaptation' ? 'adaptation notes'
            : mode === 'notes' ? 'notes total'
              : 'porting notes'
          setTooltip(event, label, notes, notesLabel)
          if (tooltip) {
            tooltip.textContent = `${label.join(' / ')} · ${formatter.format(notes)} ${notesLabel} · ${formatter.format(loc)} loc`
          }
          return
        }
        if (mode === 'comments') {
          const comments = d.data.commentLines ?? 0
          const code = d.data.codeLines ?? 0
          const ratio = code > 0 ? (comments / code) : 0
          setTooltip(event, label, comments, 'comment lines')
          if (tooltip) {
            tooltip.textContent = `${label.join(' / ')} · ${formatter.format(comments)} comment lines · ${formatter.format(code)} code lines · ${(ratio * 100).toFixed(1)}%`
          }
          return
        }
        const value = d.data ? valueForMode(d.data) : d.value ?? 0
        setTooltip(event, label, value, labelSuffix)
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
    nodes
      .append('rect')
      .attr('x', (d) => d.x0)
      .attr('y', (d) => d.y0)
      .attr('width', (d) => d.x1 - d.x0)
      .attr('height', (d) => d.y1 - d.y0)
      .attr('class', 'treemap-rect treemap-child')
      .classed('is-leaf', (d) => !!d.data.isLeaf)
      .classed('is-folder', (d) => !d.data.isLeaf)
      .attr('fill', (d) => fillForNode(d.data, d.parent?.data.name ?? ''))
      .attr('data-group', (d) => d.parent?.data.name ?? '')
      .on('click', (_, d) => {
        const parent = d.parent?.data.name
        if (parent) {
          setZoomPath([...zoomPath, parent, d.data.name])
        }
      })
      .on('mousemove', (event, d) => {
        const parent = d.parent?.data.name ?? ''
        const label = [...zoomPath, parent, d.data.name].filter(Boolean)
        if (mode === 'porting' || mode === 'adaptation' || mode === 'notes') {
          const loc = d.data.loc ?? 0
          const notes = noteValueForMode(d.data)
          const notesLabel = mode === 'adaptation' ? 'adaptation notes'
            : mode === 'notes' ? 'notes total'
              : 'porting notes'
          setTooltip(event, label, notes, notesLabel)
          if (tooltip) {
            tooltip.textContent = `${label.join(' / ')} · ${formatter.format(notes)} ${notesLabel} · ${formatter.format(loc)} loc`
          }
          return
        }
        if (mode === 'comments') {
          const comments = d.data.commentLines ?? 0
          const code = d.data.codeLines ?? 0
          const ratio = code > 0 ? (comments / code) : 0
          setTooltip(event, label, comments, 'comment lines')
          if (tooltip) {
            tooltip.textContent = `${label.join(' / ')} · ${formatter.format(comments)} comment lines · ${formatter.format(code)} code lines · ${(ratio * 100).toFixed(1)}%`
          }
          return
        }
        const value = d.data ? valueForMode(d.data) : d.value ?? 0
        setTooltip(event, label, value, labelSuffix)
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mouseout', function () {
        d3.select(this).classed('is-hovered', false)
        hideTooltip()
      })

    nodes
      .append('clipPath')
      .attr('id', (_, i) => `treemap-clip-${mode}-${i}`)
      .append('rect')
      .attr('x', (d) => d.x0 + 2)
      .attr('y', (d) => d.y0 + 2)
      .attr('width', (d) => Math.max(0, d.x1 - d.x0 - 4))
      .attr('height', (d) => Math.max(0, d.y1 - d.y0 - 4))

    nodes
      .append('text')
      .attr('x', (d) => d.x0 + 6)
      .attr('y', (d) => d.y0 + 16)
      .attr('class', 'treemap-label')
      .attr('clip-path', (_, i) => `url(#treemap-clip-${mode}-${i})`)
      .text((d) => d.data.name)
      .style('display', 'block')

    if (hoveredGroup) {
      svg
        .selectAll<SVGRectElement, d3.HierarchyRectangularNode<TreemapNode>>('.treemap-child')
        .classed('is-dim', (d) => (d.parent?.data.name ?? '') !== hoveredGroup)
        .classed('is-group-hovered', (d) => (d.parent?.data.name ?? '') === hoveredGroup)
    }

    return () => {
      container.innerHTML = ''
    }
  }, [containerRef, data, mode, zoomPath, setZoomPath, colors, hoveredGroup, tooltipRef, portingScale, commentScale])
}

export const MathlibPage = () => {
  const { mode, setMode, theme } = useThemeMode()
  const treemapRef = useRef<HTMLDivElement>(null)
  const tooltipRef = useRef<HTMLDivElement>(null)
  const [activeView, setActiveView] = useState<TreemapMode>('size')
  const [zoomPath, setZoomPath] = useState<string[]>([])
  const [hoveredGroup, setHoveredGroup] = useState<string | null>(null)
  const data = useMemo(() => treemapData as TreemapNode, [])
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
  const portingScale = theme === 'reticle'
    ? { low: '#1e2a31', high: '#7a3b44' }
    : { low: '#f6f0d4', high: '#c55b63' }
  const commentScale = theme === 'reticle'
    ? { low: '#25313a', high: '#4f6a63' }
    : { low: '#eaf7ea', high: '#7bbf9a' }

  useTreemap(
    treemapRef,
    data,
    activeView,
    zoomPath,
    setZoomPath,
    palette,
    hoveredGroup,
    tooltipRef,
    portingScale,
    commentScale,
  )

  useEffect(() => {
    setHoveredGroup(null)
  }, [zoomPath])

  return (
    <div className={`page theme-${theme}`}>
      <SiteHeader mode={mode} onModeChange={setMode} />

      <section className="intro">
        <h1>TR-004 · Mathlib Treemap</h1>
        <p>Overview of Mathlib modules, definitions, and lemma density.</p>
      </section>

      <section className="samples">
        <div className="panel-header">
          <div>
            <h2>Section A · Module coverage</h2>
            <p>Distribution of files and definitions across Mathlib.</p>
          </div>
        </div>
        <div className="treemap-menu">
          <button
            className={`ghost-button ${activeView === 'size' ? 'active' : ''}`}
            onClick={() => setActiveView('size')}
          >
            BYTES
          </button>
          <button
            className={`ghost-button ${activeView === 'count' ? 'active' : ''}`}
            onClick={() => setActiveView('count')}
          >
            FILE COUNT
          </button>
          <button
            className={`ghost-button ${activeView === 'porting' ? 'active' : ''}`}
            onClick={() => setActiveView('porting')}
          >
            PORTING NOTES
          </button>
          <button
            className={`ghost-button ${activeView === 'adaptation' ? 'active' : ''}`}
            onClick={() => setActiveView('adaptation')}
          >
            ADAPTATION NOTES
          </button>
          <button
            className={`ghost-button ${activeView === 'notes' ? 'active' : ''}`}
            onClick={() => setActiveView('notes')}
          >
            NOTES TOTAL
          </button>
          <button
            className={`ghost-button ${activeView === 'comments' ? 'active' : ''}`}
            onClick={() => setActiveView('comments')}
          >
            COMMENT RATIO
          </button>
        </div>
        <div className="treemap-separator" />
        <div className="treemap-breadcrumb">
          <button className="ghost-button" onClick={() => setZoomPath([])}>
            MATHLIB
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

    </div>
  )
}
