import * as vscode from 'vscode'
import { readFile } from 'node:fs/promises'
import { join } from 'node:path'

const WEBVIEW_DIST = 'media'
const WEBVIEW_ENTRY = 'mathlib-vscode.html'

const rewriteWebviewHtml = (
  html: string,
  webview: vscode.Webview,
  extensionUri: vscode.Uri,
) => {
  const mediaRoot = vscode.Uri.joinPath(extensionUri, WEBVIEW_DIST)
  const withCsp = html.replace(
    '<head>',
    `<head>
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src ${webview.cspSource} data:; style-src ${webview.cspSource} 'unsafe-inline'; script-src ${webview.cspSource} 'unsafe-inline'; font-src ${webview.cspSource};">`,
  )
  return withCsp.replace(/(href|src)=\"(.+?)\"/g, (match, attr, value) => {
    if (!value.startsWith('./')) {
      return match
    }
    const resourceUri = webview.asWebviewUri(vscode.Uri.joinPath(mediaRoot, value))
    return `${attr}="${resourceUri.toString()}"`
  })
}

const openTreemapPanel = async (context: vscode.ExtensionContext) => {
  const panel = vscode.window.createWebviewPanel(
    'mathlibTreemap',
    'Mathlib Treemap',
    vscode.ViewColumn.One,
    {
      enableScripts: true,
      retainContextWhenHidden: true,
      localResourceRoots: [vscode.Uri.joinPath(context.extensionUri, WEBVIEW_DIST)],
    },
  )

  try {
    const htmlPath = join(context.extensionPath, WEBVIEW_DIST, WEBVIEW_ENTRY)
    const html = await readFile(htmlPath, 'utf8')
    panel.webview.html = rewriteWebviewHtml(html, panel.webview, context.extensionUri)
  } catch (error) {
    panel.webview.html = `<html><body><h2>Missing webview assets.</h2><p>Build the webview and run <code>npm run copy-webview</code> from <code>vscode-extension</code>.</p></body></html>`
    console.error('Failed to load webview HTML', error)
  }

  panel.webview.onDidReceiveMessage(async (message) => {
    if (message?.type === 'openFile' && typeof message.path === 'string') {
      try {
        const uri = vscode.Uri.file(message.path)
        const doc = await vscode.workspace.openTextDocument(uri)
        await vscode.window.showTextDocument(doc, { preview: true })
      } catch (error) {
        void vscode.window.showErrorMessage('Unable to open file in VS Code.')
        console.error('Failed to open file', error)
      }
      return
    }

    if (message?.type === 'pickJson') {
      const selected = await vscode.window.showOpenDialog({
        canSelectMany: false,
        filters: { JSON: ['json'] },
        openLabel: 'Open Metrics JSON',
      })
      const uri = selected?.[0]
      if (!uri) {
        return
      }
      try {
        const text = await readFile(uri.fsPath, 'utf8')
        await panel.webview.postMessage({ type: 'loadJson', text })
      } catch (error) {
        void vscode.window.showErrorMessage('Unable to read JSON file.')
        console.error('Failed to read JSON', error)
      }
    }
  })
}

export const activate = (context: vscode.ExtensionContext) => {
  context.subscriptions.push(
    vscode.commands.registerCommand('leanExperiment.openTreemap', () => {
      void openTreemapPanel(context)
    }),
  )
}

export const deactivate = () => undefined
