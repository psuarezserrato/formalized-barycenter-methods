# Formalized Barycenter Methods (`BCG`)

Machine-checked Lean 4 (`v4.35.0`) formalization of the **Besson–Courtois–Gallot (1995)** and **Souto (2008)** barycenter method, **Yuping Ruan's (2024)** repair of the octonionic gap on the Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$, and downstream non-smooth extensions to $\mathsf{RCD}(K, N)$ and Alexandrov spaces.

## Repository Architecture

This umbrella repository houses the core smooth & rank-one `BCG` library and mounts two standalone journal subrepositories as Git submodules:

| Component | Path / Subrepository | Scope & Target Audience |
| :--- | :--- | :--- |
| **Core Barycenter Engine** | [`BCG.lean`](BCG.lean), [`BCG/`](BCG/), [`DifferentialGeometry/`](DifferentialGeometry/) | Smooth $\mathbb{R}\mathbf{H}^n$, associative $\mathbb{K}\mathbf{H}^m$ ($\mathbb{R}, \mathbb{C}, \mathbb{H}$), and Ruan's $\mathbb{O}\mathbf{H}^2$ repair (`12` modules, `5,247` LOC, `27` green blueprint nodes, `227` declarations, `0 sorryAx`). |
| **RCD & Alexandrov Rigidity** | [`rcd-entropy-degree-rigidity/`](rcd-entropy-degree-rigidity/) | *Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces* (Sturm $\mathsf{CAT}(0)$ barycenter + CMMP orientation currents + Theorem 1.1 inequality & smoothness rigidity). |
| **Alexandrov Applications** | [`alexandrov-entropy-degree-applications/`](alexandrov-entropy-degree-applications/) | *The entropy-degree theorem for Alexandrov spaces* (`arXiv:2606.30403`: §5 degree bridge, Theorem 1.1, Remark 1.15, and all 14 downstream corollaries & theorems). |

## Verification Metrics (Core `BCG` Library)

- **Lean Toolchain:** `leanprover/lean4:v4.35.0` + `mathlib4` (`v4.35.0`)
- **Vendored Geometry Dependency:** [`DifferentialGeometry/`](DifferentialGeometry/) — the 509 modules transitively imported by `BCG` from [`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry) (`v0.1.5`, Apache-2.0) with `v4.35.0` compatibility patches (see [`DifferentialGeometry/NOTICE.md`](DifferentialGeometry/NOTICE.md))
- **Blueprint & Audit:** `27/27` green nodes (`19` proved `#1CAC78` + `8` definitions `#B0ECA3`), `227` declarations verified with `0 sorryAx` and only standard axioms `{propext, Classical.choice, Quot.sound}`
- **Executive Report:** [`report/bcg_executive_report.pdf`](report/bcg_executive_report.pdf) (`REPORT.md` provides a detailed module catalog)
- **Interactive Blueprint:** [`blueprint/web/index.html`](blueprint/web/index.html) · [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html) · [`blueprint/print/print.pdf`](blueprint/print/print.pdf)

## Quick Start

```bash
# Clone with both companion journal subrepositories
git clone --recursive https://github.com/psuarezserrato/formalized-barycenter-methods.git
cd formalized-barycenter-methods

# Fetch Mathlib cache and build the core BCG library
lake exe cache get
lake build
```

To rebuild the core blueprint website and PDF dependency graph (requires `leanblueprint`, `graphviz`, and `pdflatex`):

```bash
./blueprint/export_dep_graph.sh
```

## License

Apache License, Version 2.0 (see [`LICENSE`](LICENSE) and [`DifferentialGeometry/LICENSE`](DifferentialGeometry/LICENSE)).
