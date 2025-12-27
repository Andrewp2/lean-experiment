# Lean Experiment

Lean Experiment is a small lab for exploring Lean tooling UX. It ships a proof walkthrough generator (LLM-backed),
an interactive Mathlib treemap, and reference/visualization pages that experiment with how proof state can be taught
and inspected.

## What’s inside

- Proof walkthrough generator: paste a Lean proof and get a step-by-step explanation from an LLM.
- Mathlib treemap: D3 visualization of Mathlib file metrics, with local folder scanning support in the Tauri app.
- Tactic reference: quick lookup table of common Lean tactics and examples.
- Visualizer scaffold: mock UI for goal-state graphs, tactic timelines, and dependency views.

## Project layout

- `src/App.tsx`: main proof walkthrough UI.
- `src/pages/MathlibPage.tsx`: treemap visualization and Mathlib scanner.
- `src/pages/TacticsPage.tsx`: tactic reference page.
- `src/pages/VisualizerPage.tsx`: proof-state visualizer scaffold.
- `api/`: Vercel serverless endpoints, including `/api/explain` and Lean session proxy stubs.

## Requirements

- Node.js + npm
- `OPENAI_API_KEY` for `/api/explain` (used by the walkthrough generator)

## Local development

Run the dev server:

```shell
npm run dev
```

Build for production:

```shell
npm run build
```

## VS Code extension (treemap)

Build the webview bundle and copy it into the extension:

```shell
npm run build
node vscode-extension/scripts/copy-webview.js
```

Compile the extension:

```shell
cd vscode-extension
npm install
npm run compile
```

In VS Code, run the command `Lean Experiment: Open Mathlib Treemap`.

## Desktop (Tauri)

Ubuntu 24.04 dependencies (from the Tauri docs):

```shell
sudo apt update
sudo apt install libwebkit2gtk-4.1-dev \
  build-essential \
  curl \
  wget \
  file \
  libxdo-dev \
  libssl-dev \
  libayatana-appindicator3-dev \
  librsvg2-dev
```

Start the desktop app in dev mode:

```shell
npm run tauri:dev
```

Build the desktop app:

```shell
npm run tauri:build
```

If you want to build without running the dev server, use `npm run tauri:build`.
