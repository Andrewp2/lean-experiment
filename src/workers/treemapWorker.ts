import { hierarchy, treemap } from 'd3-hierarchy'
import { scaleLinear } from 'd3-scale'

type TreemapNode = {
  name: string
  path?: string
  series: Record<string, number>
  children?: TreemapNode[]
  isLeaf?: boolean
}

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

type LayoutRequest = {
  type: 'layout'
  requestId: number
  payload: {
    data: TreemapNode
    sizeSeries: string
    colorSeries: string
    colorMode: 'global' | 'per_parent'
    theme: 'highk' | 'reticle'
    zoomPath: string[]
    width: number
    height: number
    colors: string[]
    colorScale: { low: string; high: string }
  }
}

const valueForSeries = (node: TreemapNode, key: string) => node.series?.[key] ?? 0

const findNode = (
  node: ReturnType<typeof hierarchy<TreemapNode>>,
  path: string[],
) => {
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

const buildLayout = (payload: LayoutRequest['payload']): LayoutPayload => {
  const {
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    zoomPath,
    width,
    height,
    colors,
    colorScale,
  } = payload

  const root = hierarchy<TreemapNode>(data)
    .sum((d) => valueForSeries(d, sizeSeries))
    .sort((a, b) => (b.value ?? 0) - (a.value ?? 0))
  const zoomRoot = findNode(root, zoomPath)
  const topLevel = zoomRoot.children ?? []

  const displayRoot = hierarchy({
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
        series: child.data.series ?? {},
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

  const sizeValueForLayout = (node: TreemapNode) => (
    node.children && node.children.length > 0 ? 0 : valueForSeries(node, sizeSeries)
  )

  displayRoot.sum(sizeValueForLayout)
  const tiledRoot = treemap<TreemapNode>()
    .size([width, height])
    .paddingOuter(2)
    .paddingInner(3)
    .paddingTop((d) => (d.depth === 1 ? 18 : 2))(displayRoot)

  const parentNodes = tiledRoot.descendants().filter((d) => d.depth === 1)
  const childNodes = tiledRoot.descendants().filter((d) => d.depth === 2)

  const colorIndexByName = new Map(
    parentNodes.map((child, index) => [child.data.name, index]),
  )
  const color = (name: string) => {
    const index = colorIndexByName.get(name) ?? 0
    return colors[index % colors.length]
  }
  const displayNodes = childNodes.length > 0 ? childNodes : parentNodes
  const absoluteValues = displayNodes.map((node) => valueForSeries(node.data, colorSeries))
  const maxAbsolute = Math.max(0, ...absoluteValues)
  const minAbsoluteNonZero = Math.min(
    ...absoluteValues.filter((value) => value > 0),
  )
  const colorMax = maxAbsolute
  const colorMin = Number.isFinite(minAbsoluteNonZero) ? minAbsoluteNonZero : 0
  const colorDomainMax = colorMax > 0 ? colorMax : 1
  const colorDomainMin = colorMin > 0 ? colorMin : 0
  const colorScaleFn = scaleLinear<string>()
    .domain([
      colorDomainMin,
      colorDomainMax === colorDomainMin ? colorDomainMin + 1 : colorDomainMax,
    ])
    .range([colorScale.low, colorScale.high])

  const baseZeroColor = theme === 'reticle' ? '#000000' : '#ffffff'
  const relativeFill = (value: number, minNonZero: number, max: number) => {
    if (value <= 0 || max <= 0) {
      return baseZeroColor
    }
    if (minNonZero > 0 && max === minNonZero) {
      return colorScale.high
    }
    const scale = scaleLinear<string>()
      .domain([minNonZero > 0 ? minNonZero : 0, max])
      .range([colorScale.low, colorScale.high])
    return scale(value)
  }

  const absoluteFill = (value: number, fallbackName: string) => {
    if (value <= 0) {
      return baseZeroColor
    }
    if (!Number.isFinite(value)) {
      return color(fallbackName)
    }
    return colorScaleFn(value)
  }

  const childGroups = new Map<string, { minNonZero: number; max: number }>()
  childNodes.forEach((node) => {
    const parentName = node.parent?.data.name ?? ''
    const value = valueForSeries(node.data, colorSeries)
    if (!childGroups.has(parentName)) {
      childGroups.set(parentName, { minNonZero: Number.POSITIVE_INFINITY, max: 0 })
    }
    const group = childGroups.get(parentName)!
    if (value > 0) {
      group.minNonZero = Math.min(group.minNonZero, value)
      group.max = Math.max(group.max, value)
    }
  })
  const parentMinNonZero = Math.min(
    ...parentNodes.map((node) => valueForSeries(node.data, colorSeries)).filter((value) => value > 0),
  )
  const parentMax = Math.max(
    0,
    ...parentNodes.map((node) => valueForSeries(node.data, colorSeries)),
  )

  const parentLayout = parentNodes.map((node) => ({
    name: node.data.name,
    path: node.data.path,
    series: node.data.series ?? {},
    isLeaf: node.data.isLeaf,
    x0: node.x0,
    y0: node.y0,
    x1: node.x1,
    y1: node.y1,
    fill: colorMode === 'per_parent'
      ? relativeFill(
        valueForSeries(node.data, colorSeries),
        Number.isFinite(parentMinNonZero) ? parentMinNonZero : 0,
        parentMax,
      )
      : absoluteFill(valueForSeries(node.data, colorSeries), node.data.name),
  }))

  const childLayout = childNodes.map((node) => ({
    name: node.data.name,
    path: node.data.path,
    series: node.data.series ?? {},
    isLeaf: node.data.isLeaf,
    x0: node.x0,
    y0: node.y0,
    x1: node.x1,
    y1: node.y1,
    fill: colorMode === 'per_parent'
      ? (() => {
        const parentName = node.parent?.data.name ?? ''
        const group = childGroups.get(parentName) ?? { minNonZero: 0, max: 0 }
        return relativeFill(
          valueForSeries(node.data, colorSeries),
          Number.isFinite(group.minNonZero) ? group.minNonZero : 0,
          group.max,
        )
      })()
      : absoluteFill(valueForSeries(node.data, colorSeries), node.parent?.data.name ?? ''),
    parentName: node.parent?.data.name ?? '',
  }))

  return {
    parentNodes: parentLayout,
    childNodes: childLayout,
    labelSuffix: sizeSeries.replace(/_/g, ' '),
  }
}

self.onmessage = (event: MessageEvent<LayoutRequest>) => {
  const message = event.data
  if (message.type !== 'layout') {
    return
  }
  const payload = buildLayout(message.payload)
  self.postMessage({ type: 'layout', requestId: message.requestId, payload })
}
