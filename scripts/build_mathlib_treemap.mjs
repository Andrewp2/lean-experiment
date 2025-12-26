#!/usr/bin/env node
import fs from 'node:fs'
import path from 'node:path'

const projectRoot = process.cwd()
const mathlibPath = process.argv[2] || process.env.MATHLIB_PATH
const maxDepth = Number(process.env.MAX_DEPTH ?? '5')
const minPercent = Number(process.env.MIN_PERCENT ?? '0.01')
const outputPath =
  process.argv[3] || path.join(projectRoot, 'src', 'assets', 'mathlib_treemap.json')

if (!mathlibPath) {
  console.error('Provide Mathlib path via MATHLIB_PATH or as the first argument.')
  process.exit(1)
}

const rootDir = path.resolve(mathlibPath)
const mathlibDir = fs.existsSync(path.join(rootDir, 'Mathlib'))
  ? path.join(rootDir, 'Mathlib')
  : rootDir

const root = { name: 'Mathlib', children: new Map(), size: 0, count: 0 }
let totalFiles = 0
const sampleFiles = []

const addFile = (relativePath, size) => {
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
  totalFiles += 1
  if (sampleFiles.length < 5) {
    sampleFiles.push(relativePath)
  }

  for (let i = 0; i < depth; i += 1) {
    const name = segments[i]
    let child = node.children.get(name)
    if (!child) {
      child = { name, children: new Map(), size: 0, count: 0 }
      node.children.set(name, child)
    }
    child.size += size
    child.count += 1
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
      const relativePath = path.relative(baseDir, fullPath)
      addFile(relativePath, stats.size)
    }
  }
}

walk(mathlibDir, rootDir)

if (totalFiles < 50) {
  console.warn(`Warning: only ${totalFiles} .lean files found under ${mathlibDir}`)
  console.warn('Sample files:', sampleFiles)
}

const sumValue = (node) => {
  if (typeof node.value === 'number') {
    return node.value
  }
  return (node.children ?? []).reduce((sum, child) => sum + sumValue(child), 0)
}

const sumCount = (node) => {
  if (typeof node.count === 'number') {
    return node.count
  }
  return (node.children ?? []).reduce((sum, child) => sum + sumCount(child), 0)
}

const normalizeNode = (node) => {
  if (!node.children || node.children.length === 0) {
    return node
  }

  const normalizedChildren = node.children.map(normalizeNode)
  const total = normalizedChildren.reduce((sum, child) => sum + sumValue(child), 0)
  if (total === 0) {
    return { ...node, children: normalizedChildren }
  }

  const keep = []
  const otherChildren = []

  for (const child of normalizedChildren) {
    const childValue = sumValue(child)
    if (childValue / total < minPercent) {
      otherChildren.push(child)
    } else {
      keep.push(child)
    }
  }

  if (otherChildren.length === 0 || keep.length === 0) {
    return { ...node, children: normalizedChildren }
  }

  const otherNode = normalizeNode({
    name: 'Miscellaneous',
    children: otherChildren,
    value: otherChildren.reduce((sum, child) => sum + sumValue(child), 0),
    count: otherChildren.reduce((sum, child) => sum + sumCount(child), 0),
  })

  return { ...node, children: [...keep, otherNode] }
}

const toJson = (node) => {
  const children = node.children ? Array.from(node.children.values()).map(toJson) : []
  if (children.length === 0) {
    return { name: node.name, value: node.size, count: node.count }
  }

  return {
    name: node.name,
    children,
    value: node.size,
    count: node.count,
  }
}

const output = normalizeNode(toJson(root))
fs.mkdirSync(path.dirname(outputPath), { recursive: true })
fs.writeFileSync(outputPath, JSON.stringify(output, null, 2))

console.log(`Wrote treemap data to ${outputPath}`)
