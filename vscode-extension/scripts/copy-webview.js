const { cpSync, existsSync, rmSync } = require('node:fs')
const { join, resolve } = require('node:path')

const repoRoot = resolve(__dirname, '..', '..')
const source = join(repoRoot, 'dist')
const target = join(repoRoot, 'vscode-extension', 'media')

if (!existsSync(source)) {
  console.error('dist/ not found. Run `npm run build` at the repo root first.')
  process.exit(1)
}

rmSync(target, { recursive: true, force: true })
cpSync(source, target, { recursive: true })
