# US Graphics style guide for a website

## Design goals
- High signal, low ornament
- Strong technical vibe: engineering labels, part numbers, documentation structure
- High contrast by default, with fluorescent accents used sparingly
- Layouts that read like instruments: grids, tables, aligned columns, clear hierarchy

## Color system

### Base neutrals
Use neutrals for almost everything. Reserve saturated colors for status and emphasis only.
- Black: #000000
- White: #FFFFFF
- Gray: #999999

### Fluorescent accents
Use these for small, high impact accents (links, focus rings, status, small UI indicators).
- FL Red: #FF0000
- FL Green: #00FF00
- FL Blue: #0000FF
- FL Cyan: #00FFFF
- FL Magenta: #FF00FF
- FL Yellow: #FFFF00
- FL Orange: #FF6600

### Secondary muted accents
Use these for larger areas when you need color but want to keep contrast comfortable.
- Maroon: #660000
- Green: #00A645
- Blue: #000066
- Cyan: #006666
- Magenta: #660066
- Yellow: #FFBF00
- Olive: #666600

### Site themes
Adopt a named theme system, with two primary modes and optional variants.

Primary:
- Light Mode: light mode, white background with dark text
- Dark Mode: dark mode, black background with bright text

Optional variants (for special sections, campaigns, or internal tools):
- POLYIMIDE: amber leaning
- EPITAXY: magenta leaning
- METALGATE: cyan leaning

Rules:
- Keep backgrounds neutral. Use color mostly in text, thin strokes, small chips, and inline indicators.
- Avoid gradients unless they are purely functional (charts).
- Prefer thin 1px to 2px strokes over filled shapes.

## Typography

### Typeface
- Use a monospace family as the primary brand voice.
- Prefer a condensed cut for dense UI and documentation layouts.

Fallback stack example:
- Primary: Berkeley Mono Condensed (or closest available)
- Fallbacks: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, Liberation Mono, monospace

### Styling rules
- Default: no italics
- Headings: tight, compact, minimal punctuation
- Labels: uppercase, short, part-number-like naming
- Numbers: align vertically in tables, favor tabular numerals

### Type scale (suggested)
- H1: large, compact, left aligned
- H2: medium, used as section dividers
- Body: comfortable size, slightly tight leading
- Captions: smaller, used for metadata, revisions, timestamps

## Layout and grid

### Core layout
- Left aligned by default
- Content column should feel like a terminal or report, not a magazine
- Favor a fixed measure for reading: target 80ch to 96ch for documentation pages

### Spacing
- Use a strict spacing ramp (example): 4, 8, 12, 16, 24, 32, 48
- Keep vertical rhythm consistent across sections
- Use generous whitespace around major sections, tighter spacing inside tables

### Grids and rules
- Use visible structure: thin rules, separators, aligned columns
- Prefer tables and definition lists over decorative cards

## Components

### Header and navigation
- Minimal header: wordmark left, navigation as compact text links
- Navigation labels should be short and technical (Work, Notes, Spec, Tools, Contact)

### Buttons
- Rectangular, thin border, no heavy shadows
- States:
  - Default: neutral border
  - Hover: slightly brighter border or text
  - Active: invert or increase contrast
  - Focus: fluorescent ring (cyan or yellow)

### Links
- Underline by default
- Hover: color shift to a fluorescent accent, but keep it readable

### Tables
Tables are first-class UI.
- Strong column alignment
- Right align numeric columns
- Use subtle row separators
- Provide a header row with clear labels

### Callouts
- Use sparingly and keep them strict.
- Types: NOTE, WARN, ERROR, OK
- Visual: thin left rule plus a small colored label chip

### Forms
- Inputs: simple border, no rounded pill shapes
- Use monospace in inputs when content is code, IDs, or numbers
- Errors: red text plus a small inline indicator, not large banners

## Imagery and graphics
- Prefer technical visuals: diagrams, schematics, screenshots, tables, plots
- Icons should be monoline and minimal, used as UI affordances only
- Avoid stock photography unless it is documentary and neutral

## Motion
- Prefer no animation to minimal animation
- Prefer minimal animation to maximal animation

## Content voice and labeling
- Write like documentation and reports
- Use metadata blocks for authority: revision, date, version, SKU, part number
- Use short paragraphs and lists
- Name sections like instruments or spec sheets:
  - TR-### for reports
  - PN ####-### for components
  - REV A, REV B for revisions

## Accessibility
- Contrast first: Light Mode and Dark Mode should both meet strong contrast targets
- Visible focus states on all interactive controls
- Do not rely on color alone for status: include a label or icon
- Ensure tables are readable on mobile via horizontal scroll and sticky headers when needed

## Implementation notes (design tokens)
- Define tokens as named primitives (BLACK, WHITE, FL_CYAN) and theme mappings (DARK_BG, DARK_FG).
- Keep the token set small. Avoid large component-specific token sprawl.


# Design Philosophy

Design philosophy
Emergent over prescribed aesthetics.
Expose state and inner workings.
Dense, not sparse.
Explicit is better than implicit.
Engineered for human vision and perception.
Regiment functionalism.
Performance is design.
Verbosity over opacity.
Ignore design trends. Timeless and unfashionable.
Flat, not hierarchical.
Diametrically opposite of minimalism, as complex as it needs to be.
Driven by objective reasoning and common sense.
Don't infantilize users.
