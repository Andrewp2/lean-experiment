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
type PortingScale = { low: string; high: string }

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
  portingScale: PortingScale,
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
      children: topLevel.map((child) => {
        const grandChildren = child.children ?? []
        if (grandChildren.length === 0) {
          return {
            name: child.data.name,
            series: child.data.series ?? {},
            isLeaf: true,
          }
        }
        return {
          name: child.data.name,
          children: grandChildren.map((g) => ({
            name: g.data.name,
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
    const portingScaleFn = d3
      .scaleLinear<string>()
      .domain([0, colorMax || 1])
      .range([portingScale.low, portingScale.high])

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
      return portingScaleFn(seriesValue)
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
      .attr('fill', (d) => (d.data.isLeaf ? fillForNode(d, d.data.name) : 'none'))
      .attr('data-group', (d) => d.data.name)
      .on('click', (_, d) => {
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
      .append('clipPath')
      .attr('id', (_, i) => `treemap-clip-${sizeSeries}-${i}`)
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
      .attr('clip-path', (_, i) => `url(#treemap-clip-${sizeSeries}-${i})`)
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
    portingScale,
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
    ? { low: '#3d7cc8', high: '#c9773a' }
    : { low: '#2d72c4', high: '#e38c4a' }

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
    portingScale,
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

  const buildTreeFromEntries = (entries: UploadedEntry[]): TreemapNode => {
    const rootName = entries[0]?.path.split('/').filter(Boolean)[0] ?? 'Root'
    const rootNode: TreemapNode = { name: rootName, series: {}, children: [] }
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
          child = { name: part, series: {}, children: [] }
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
