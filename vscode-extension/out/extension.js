"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode = __importStar(require("vscode"));
const promises_1 = require("node:fs/promises");
const node_path_1 = require("node:path");
const WEBVIEW_DIST = 'media';
const WEBVIEW_ENTRY = 'mathlib-vscode.html';
const rewriteWebviewHtml = (html, webview, extensionUri) => {
    const mediaRoot = vscode.Uri.joinPath(extensionUri, WEBVIEW_DIST);
    const withCsp = html.replace('<head>', `<head>
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src ${webview.cspSource} data:; style-src ${webview.cspSource} 'unsafe-inline'; script-src ${webview.cspSource} 'unsafe-inline'; font-src ${webview.cspSource};">`);
    return withCsp.replace(/(href|src)=\"(.+?)\"/g, (match, attr, value) => {
        if (!value.startsWith('./')) {
            return match;
        }
        const resourceUri = webview.asWebviewUri(vscode.Uri.joinPath(mediaRoot, value));
        return `${attr}="${resourceUri.toString()}"`;
    });
};
const openTreemapPanel = async (context) => {
    const panel = vscode.window.createWebviewPanel('mathlibTreemap', 'Mathlib Treemap', vscode.ViewColumn.One, {
        enableScripts: true,
        retainContextWhenHidden: true,
        localResourceRoots: [vscode.Uri.joinPath(context.extensionUri, WEBVIEW_DIST)],
    });
    try {
        const htmlPath = (0, node_path_1.join)(context.extensionPath, WEBVIEW_DIST, WEBVIEW_ENTRY);
        const html = await (0, promises_1.readFile)(htmlPath, 'utf8');
        panel.webview.html = rewriteWebviewHtml(html, panel.webview, context.extensionUri);
    }
    catch (error) {
        panel.webview.html = `<html><body><h2>Missing webview assets.</h2><p>Build the webview and run <code>npm run copy-webview</code> from <code>vscode-extension</code>.</p></body></html>`;
        console.error('Failed to load webview HTML', error);
    }
    panel.webview.onDidReceiveMessage(async (message) => {
        if (message?.type === 'openFile' && typeof message.path === 'string') {
            try {
                const uri = vscode.Uri.file(message.path);
                const doc = await vscode.workspace.openTextDocument(uri);
                await vscode.window.showTextDocument(doc, { preview: true });
            }
            catch (error) {
                void vscode.window.showErrorMessage('Unable to open file in VS Code.');
                console.error('Failed to open file', error);
            }
            return;
        }
        if (message?.type === 'pickJson') {
            const selected = await vscode.window.showOpenDialog({
                canSelectMany: false,
                filters: { JSON: ['json'] },
                openLabel: 'Open Metrics JSON',
            });
            const uri = selected?.[0];
            if (!uri) {
                return;
            }
            try {
                const text = await (0, promises_1.readFile)(uri.fsPath, 'utf8');
                await panel.webview.postMessage({ type: 'loadJson', text });
            }
            catch (error) {
                void vscode.window.showErrorMessage('Unable to read JSON file.');
                console.error('Failed to read JSON', error);
            }
        }
    });
};
const activate = (context) => {
    context.subscriptions.push(vscode.commands.registerCommand('leanExperiment.openTreemap', () => {
        void openTreemapPanel(context);
    }));
};
exports.activate = activate;
const deactivate = () => undefined;
exports.deactivate = deactivate;
