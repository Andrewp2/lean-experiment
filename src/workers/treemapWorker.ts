import { hierarchy, treemap } from 'd3-hierarchy'
import { interpolateHcl } from 'd3-interpolate'

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

type LayoutRequest = {
  type: 'layout'
  requestId: number
  payload: {
    data: TreemapNode
    sizeSeries: string
    colorSeries: string
    colorMode: 'global' | 'per_parent'
    theme: 'highk' | 'reticle'
    width: number
    height: number
    colors: string[]
  }
}

const valueForSeries = (node: TreemapNode, key: string) => node.series?.[key] ?? 0

const pruneToLeaves = (node: TreemapNode): TreemapNode => {
  if (node.isLeaf) {
    return { ...node, children: undefined }
  }
  if (!node.children || node.children.length === 0) {
    return node
  }
  return {
    ...node,
    children: node.children.map(pruneToLeaves),
  }
}

const isLeafNode = (node: TreemapNode) => (
  node.isLeaf === true || !node.children || node.children.length === 0
)

const buildLayout = (payload: LayoutRequest['payload']): LayoutPayload => {
  const {
    data,
    sizeSeries,
    colorSeries,
    colorMode,
    theme,
    width,
    height,
    colors,
  } = payload

  const prunedData = pruneToLeaves(data)
  const root = hierarchy<TreemapNode>(prunedData)
    .sum((d) => (isLeafNode(d) ? valueForSeries(d, sizeSeries) : 0))
    .sort((a, b) => (b.value ?? 0) - (a.value ?? 0))

  const tiledRoot = treemap<TreemapNode>()
    .size([width, height])
    .paddingOuter((node) => (node.depth === 0 ? 0 : 1))
    .paddingInner((node) => (node.depth === 0 ? 0 : 1))
    .paddingTop((node) => (node.depth === 0 ? 0 : 1))(root)

  const leafNodes = tiledRoot.descendants().filter((d) => !d.children || d.children.length === 0)

  const colorIndexByName = new Map(
    leafNodes.map((child, index) => [child.data.name, index]),
  )
  const color = (name: string) => {
    const index = colorIndexByName.get(name) ?? 0
    return colors[index % colors.length]
  }
  const clamp01 = (value: number) => Math.max(0, Math.min(1, value))
  const colorLow = '#2d72c4'
  const colorHigh = '#e38c4a'
  const absoluteValues = leafNodes.map((node) => valueForSeries(node.data, colorSeries))
  const maxAbsolute = Math.max(0, ...absoluteValues)
  const minAbsoluteNonZero = Math.min(
    ...absoluteValues.filter((value) => value > 0),
  )
  const colorMax = maxAbsolute > 0 ? maxAbsolute : 1
  const colorMin = Number.isFinite(minAbsoluteNonZero) ? minAbsoluteNonZero : 0
  const zeroColor = theme === 'reticle' ? '#1a0b0b' : '#ffebe0'
  const relativeFill = (value: number, minNonZero: number, max: number) => {
    if (!Number.isFinite(value) || value <= 0 || max <= 0) {
      return zeroColor
    }
    if (minNonZero > 0 && max === minNonZero) {
      return interpolateHcl(colorLow, colorHigh)(1)
    }
    const t = clamp01((value - Math.max(0, minNonZero)) / (max - Math.max(0, minNonZero)))
    return interpolateHcl(colorLow, colorHigh)(t)
  }

  const absoluteFill = (value: number, fallbackName: string) => {
    if (!Number.isFinite(value) || value <= 0) {
      return zeroColor
    }
    if (colorMax === colorMin) {
      return interpolateHcl(colorLow, colorHigh)(1)
    }
    const t = clamp01((value - colorMin) / (colorMax - colorMin))
    return Number.isFinite(t)
      ? interpolateHcl(colorLow, colorHigh)(t)
      : color(fallbackName)
  }

  const childGroups = new Map<string, { minNonZero: number; max: number }>()
  leafNodes.forEach((node) => {
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
  const leafLayout = leafNodes.map((node) => ({
    name: node.data.name,
    path: node.data.path,
    series: node.data.series ?? {},
    kind: node.data.kind,
    span: node.data.span,
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

  const groupNodes = tiledRoot
    .descendants()
    .filter((node) => node.children && node.depth > 0)
    .map((node) => ({
      name: node.data.name,
      path: node.data.path,
      kind: node.data.kind,
      depth: node.depth,
      x0: node.x0,
      y0: node.y0,
      x1: node.x1,
      y1: node.y1,
    }))

  return {
    leafNodes: leafLayout,
    groupNodes,
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
