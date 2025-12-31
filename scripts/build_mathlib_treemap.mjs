#!/usr/bin/env node
import fs from 'node:fs'
import path from 'node:path'

const projectRoot = process.cwd()
const mathlibPath = process.argv[2] || process.env.MATHLIB_PATH
const maxDepth = Number(process.env.MAX_DEPTH ?? '5')
const minPercent = Number(process.env.MIN_PERCENT ?? '0.01')
const outputPath =
  process.argv[3] || path.join(projectRoot, 'src', 'assets', 'mathlib_treemap.json')
const groupByKey = process.env.GROUP_BY ?? 'loc'
const infotreeRoot = process.env.INFOTREE_ROOT || process.argv[4] || ''
const infotreeExt = process.env.INFOTREE_EXT || '.json'

if (!mathlibPath) {
  console.error('Provide Mathlib path via MATHLIB_PATH or as the first argument.')
  process.exit(1)
}

const rootDir = path.resolve(mathlibPath)
const mathlibDir = fs.existsSync(path.join(rootDir, 'Mathlib'))
  ? path.join(rootDir, 'Mathlib')
  : rootDir

const root = {
  name: 'Mathlib',
  children: new Map(),
  size: 0,
  count: 0,
  loc: 0,
  commentLines: 0,
  codeLines: 0,
  portingNotes: 0,
  adaptationNotes: 0,
  noteTotal: 0,
  infotreeNodesTotal: 0,
  infotreeContextNodes: 0,
  infotreeHoles: 0,
  infotreeInfoItemsTotal: 0,
  infotreeTacticStateItems: 0,
  infotreeTermInfoItems: 0,
  infotreeDiagnosticItems: 0,
  infotreeWidgetItems: 0,
  infotreeCommandsCount: 0,
  infotreeTacticSteps: 0,
}
let totalFiles = 0
const sampleFiles = []
const portingNoteRegex = /porting note/gi
const adaptationNoteRegex = /#adaptation_note\b/gi

const infotreeKeys = [
  'infotreeNodesTotal',
  'infotreeContextNodes',
  'infotreeHoles',
  'infotreeInfoItemsTotal',
  'infotreeTacticStateItems',
  'infotreeTermInfoItems',
  'infotreeDiagnosticItems',
  'infotreeWidgetItems',
  'infotreeCommandsCount',
  'infotreeTacticSteps',
]

const infotreeKeyAliases = {
  infotreeNodesTotal: 'infotree_nodes_total',
  infotreeContextNodes: 'infotree_context_nodes',
  infotreeHoles: 'infotree_holes',
  infotreeInfoItemsTotal: 'infotree_info_items_total',
  infotreeTacticStateItems: 'infotree_tactic_state_items',
  infotreeTermInfoItems: 'infotree_term_info_items',
  infotreeDiagnosticItems: 'infotree_diagnostic_items',
  infotreeWidgetItems: 'infotree_widget_items',
  infotreeCommandsCount: 'infotree_commands_count',
  infotreeTacticSteps: 'infotree_tactic_steps',
}

const emptyInfotreeCounts = () => (
  Object.fromEntries(infotreeKeys.map((key) => [key, 0]))
)

const readInfotreeCounts = (relativePath) => {
  if (!infotreeRoot) {
    return emptyInfotreeCounts()
  }
  const infotreePath = path.join(
    infotreeRoot,
    relativePath.replace(/\.lean$/, infotreeExt),
  )
  if (!fs.existsSync(infotreePath)) {
    return emptyInfotreeCounts()
  }
  try {
    const raw = JSON.parse(fs.readFileSync(infotreePath, 'utf8'))
    const metrics = raw.metrics ?? raw
    const counts = emptyInfotreeCounts()
    infotreeKeys.forEach((key) => {
      const value = metrics?.[key] ?? metrics?.[infotreeKeyAliases[key]]
      counts[key] = Number.isFinite(value) ? Number(value) : 0
    })
    return counts
  } catch (error) {
    console.warn(`Failed to parse infotree metrics at ${infotreePath}:`, error)
    return emptyInfotreeCounts()
  }
}

const addFile = (
  relativePath,
  size,
  loc,
  commentLines,
  codeLines,
  portingNotes,
  adaptationNotes,
  infotreeCounts,
) => {
  const parts = relativePath.split(path.sep).filter(Boolean)
  if (parts[0] === 'Mathlib') {
    parts.shift()
  }
  const fileName = parts.pop()
  if (!fileName) {
    return
  }
  const baseName = fileName.replace(/\.lean$/, '')
  const segments = [...parts, baseName].filter(Boolean)
  const depth = Math.min(segments.length, maxDepth)

  let node = root
  node.size += size
  node.count += 1
  node.loc += loc
  node.commentLines += commentLines
  node.codeLines += codeLines
  node.portingNotes += portingNotes
  node.adaptationNotes += adaptationNotes
  node.noteTotal += portingNotes + adaptationNotes
  infotreeKeys.forEach((key) => {
    node[key] += infotreeCounts[key] ?? 0
  })
  totalFiles += 1
  if (sampleFiles.length < 5) {
    sampleFiles.push(relativePath)
  }

  for (let i = 0; i < depth; i += 1) {
    const name = segments[i]
    let child = node.children.get(name)
    if (!child) {
      child = {
        name,
        children: new Map(),
        size: 0,
        count: 0,
        loc: 0,
        commentLines: 0,
        codeLines: 0,
        portingNotes: 0,
        adaptationNotes: 0,
        noteTotal: 0,
        infotreeNodesTotal: 0,
        infotreeContextNodes: 0,
        infotreeHoles: 0,
        infotreeInfoItemsTotal: 0,
        infotreeTacticStateItems: 0,
        infotreeTermInfoItems: 0,
        infotreeDiagnosticItems: 0,
        infotreeWidgetItems: 0,
        infotreeCommandsCount: 0,
        infotreeTacticSteps: 0,
      }
      node.children.set(name, child)
    }
    child.size += size
    child.count += 1
    child.loc += loc
    child.commentLines += commentLines
    child.codeLines += codeLines
    child.portingNotes += portingNotes
    child.adaptationNotes += adaptationNotes
    child.noteTotal += portingNotes + adaptationNotes
    infotreeKeys.forEach((key) => {
      child[key] += infotreeCounts[key] ?? 0
    })
    node = child
  }
}

const walk = (dir, baseDir) => {
  const entries = fs.readdirSync(dir, { withFileTypes: true })
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name)
    if (entry.isDirectory()) {
      walk(fullPath, baseDir)
    } else if (entry.isFile() && entry.name.endsWith('.lean')) {
      const stats = fs.statSync(fullPath)
      const content = fs.readFileSync(fullPath, 'utf8')
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
      const relativePath = path.relative(baseDir, fullPath)
      const infotreeCounts = readInfotreeCounts(relativePath.replace(/\\/g, '/'))
      addFile(
        relativePath,
        stats.size,
        loc,
        commentLines,
        codeLines,
        portingNotes,
        adaptationNotes,
        infotreeCounts,
      )
    }
  }
}

walk(mathlibDir, rootDir)

if (totalFiles < 50) {
  console.warn(`Warning: only ${totalFiles} .lean files found under ${mathlibDir}`)
  console.warn('Sample files:', sampleFiles)
}

const sumSeriesValue = (node, key) => {
  const current = node.series?.[key]
  if (typeof current === 'number') {
    return current
  }
  return (node.children ?? []).reduce((sum, child) => sum + sumSeriesValue(child, key), 0)
}

const normalizeNode = (node) => {
  if (!node.children || node.children.length === 0) {
    return node
  }

  const normalizedChildren = node.children.map(normalizeNode)
  const key = node.series?.[groupByKey] !== undefined ? groupByKey : 'bytes'
  const total = normalizedChildren.reduce((sum, child) => sum + sumSeriesValue(child, key), 0)
  if (total === 0) {
    return { ...node, children: normalizedChildren }
  }

  const keep = []
  const otherChildren = []

  for (const child of normalizedChildren) {
    const childValue = sumSeriesValue(child, key)
    if (childValue / total < minPercent) {
      otherChildren.push(child)
    } else {
      keep.push(child)
    }
  }

  if (otherChildren.length === 0 || keep.length === 0) {
    return { ...node, children: normalizedChildren }
  }

  const seriesKeys = new Set()
  for (const child of otherChildren) {
    Object.keys(child.series ?? {}).forEach((seriesKey) => seriesKeys.add(seriesKey))
  }
  const otherSeries = {}
  for (const seriesKey of seriesKeys) {
    otherSeries[seriesKey] = otherChildren.reduce(
      (sum, child) => sum + sumSeriesValue(child, seriesKey),
      0,
    )
  }
  const otherNode = normalizeNode({
    name: 'Miscellaneous',
    path: `${node.path}/Miscellaneous`,
    children: otherChildren,
    series: otherSeries,
  })

  return { ...node, children: [...keep, otherNode] }
}

const toJson = (node, currentPath) => {
  const nodePath = currentPath ? `${currentPath}/${node.name}` : node.name
  const children = node.children
    ? Array.from(node.children.values()).map((child) => toJson(child, nodePath))
    : []
  const commentRatio = node.codeLines > 0 ? node.commentLines / node.codeLines : 0
  const infotreeSeries = {
    infotree_nodes_total: node.infotreeNodesTotal,
    infotree_context_nodes: node.infotreeContextNodes,
    infotree_holes: node.infotreeHoles,
    infotree_info_items_total: node.infotreeInfoItemsTotal,
    infotree_tactic_state_items: node.infotreeTacticStateItems,
    infotree_term_info_items: node.infotreeTermInfoItems,
    infotree_diagnostic_items: node.infotreeDiagnosticItems,
    infotree_widget_items: node.infotreeWidgetItems,
    infotree_commands_count: node.infotreeCommandsCount,
    infotree_tactic_steps: node.infotreeTacticSteps,
  }
  if (children.length === 0) {
    return {
      name: node.name,
      path: nodePath,
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
        ...infotreeSeries,
      },
    }
  }

  return {
    name: node.name,
    children,
    path: nodePath,
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
      ...infotreeSeries,
    },
  }
}

const collectSeriesKeys = (node, keys) => {
  Object.keys(node.series ?? {}).forEach((key) => keys.add(key))
  node.children?.forEach((child) => collectSeriesKeys(child, keys))
}

const outputRoot = normalizeNode(toJson(root, ''))
const seriesKeys = new Set()
collectSeriesKeys(outputRoot, seriesKeys)
const output = { root: outputRoot, seriesKeys: Array.from(seriesKeys).sort() }
fs.mkdirSync(path.dirname(outputPath), { recursive: true })
fs.writeFileSync(outputPath, JSON.stringify(output, null, 2))

console.log(`Wrote treemap data to ${outputPath}`)
