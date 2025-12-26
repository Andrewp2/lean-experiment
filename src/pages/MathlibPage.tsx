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
  children?: TreemapNode[]
  isLeaf?: boolean
}

const useTreemap = (
  containerRef: React.RefObject<HTMLDivElement>,
  data: TreemapNode,
  mode: 'size' | 'count',
  zoomPath: string[],
  setZoomPath: (path: string[]) => void,
  colors: string[],
  hoveredGroup: string | null,
  tooltipRef: React.RefObject<HTMLDivElement>,
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

    const root = d3
      .hierarchy<TreemapNode>(data)
      .sum((d) => (mode === 'count' ? d.count ?? 0 : d.value ?? 0))
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
      children: topLevel.map((child) => {
        const grandChildren = child.children ?? []
        if (grandChildren.length === 0) {
          return {
            name: child.data.name,
            value: child.data.value ?? 0,
            count: child.data.count ?? 0,
            isLeaf: true,
          }
        }
        return {
          name: child.data.name,
          children: grandChildren.map((g) => ({
            name: g.data.name,
            value: g.data.value ?? 0,
            count: g.data.count ?? 0,
            isLeaf: !(g.children && g.children.length > 0),
          })),
          isLeaf: false,
        }
      }),
    } as TreemapNode)

    displayRoot.sum((d) => (mode === 'count' ? d.count ?? 0 : d.value ?? 0))
    d3
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

    const labelSuffix = mode === 'count' ? 'files' : 'bytes'

    const parentNodes = displayRoot.descendants().filter((d) => d.depth === 1)
    const childNodes = displayRoot.descendants().filter((d) => d.depth === 2)

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
      .attr('fill', (d) => (d.data.isLeaf ? color(d.data.name) : 'none'))
      .attr('data-group', (d) => d.data.name)
      .on('click', (_, d) => {
        setZoomPath([...zoomPath, d.data.name])
      })
      .on('mouseover', function () {
        d3.select(this).classed('is-hovered', true)
      })
      .on('mousemove', (event, d) => {
        const value = mode === 'count' ? d.data.count ?? d.value ?? 0 : d.data.value ?? d.value ?? 0
        const label = [...zoomPath, d.data.name].filter(Boolean)
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
      .attr('fill', (d) => color(d.parent?.data.name ?? ''))
      .attr('data-group', (d) => d.parent?.data.name ?? '')
      .on('click', (_, d) => {
        const parent = d.parent?.data.name
        if (parent) {
          setZoomPath([...zoomPath, parent, d.data.name])
        }
      })
      .on('mousemove', (event, d) => {
        const value = mode === 'count' ? d.data.count ?? d.value ?? 0 : d.data.value ?? d.value ?? 0
        const parent = d.parent?.data.name ?? ''
        const label = [...zoomPath, parent, d.data.name].filter(Boolean)
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
  }, [containerRef, data, mode, zoomPath, setZoomPath, colors, hoveredGroup, tooltipRef])
}

export const MathlibPage = () => {
  const { mode, setMode, theme } = useThemeMode()
  const treemapRef = useRef<HTMLDivElement>(null)
  const tooltipRef = useRef<HTMLDivElement>(null)
  const [activeView, setActiveView] = useState<'size' | 'count'>('size')
  const [zoomPath, setZoomPath] = useState<string[]>([])
  const [hoveredGroup, setHoveredGroup] = useState<string | null>(null)
  const data = useMemo(() => treemapData as TreemapNode, [])
  const findNode = (node: TreemapNode, path: string[]) => {
    let current: TreemapNode = node
    for (const segment of path) {
      const next = current.children?.find((child) => child.name === segment)
      if (!next) {
        return current
      }
      current = next
    }
    return current
  }
  const currentTopNames = useMemo(() => {
    const node = findNode(data, zoomPath)
    return (node.children ?? []).map((child) => child.name)
  }, [data, zoomPath])
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
  const palette = mode === 'dark' ? pastelDark : pastel
  const colorIndexByName = useMemo(() => {
    return new Map(currentTopNames.map((name, index) => [name, index]))
  }, [currentTopNames])
  const colorForName = (name: string) => {
    const index = colorIndexByName.get(name) ?? 0
    return palette[index % palette.length]
  }

  useTreemap(treemapRef, data, activeView, zoomPath, setZoomPath, palette, hoveredGroup, tooltipRef)

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
        {/*
        <div className="treemap-legend">
          {currentTopNames.map((name) => (
            <div
              key={name}
              className="legend-item"
              onMouseEnter={() => setHoveredGroup(name)}
              onMouseLeave={() => setHoveredGroup(null)}
            >
              <span className="legend-swatch" style={{ background: colorForName(name) }} />
              <span>{name}</span>
            </div>
          ))}
        </div>
        */}
        <div className="treemap-panel">
          <div className="treemap-canvas" ref={treemapRef} />
          <div className="treemap-tooltip" ref={tooltipRef} />
        </div>
      </section>

    </div>
  )
}
