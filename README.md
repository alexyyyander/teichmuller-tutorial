# Über Teichmüller's Einheitliches Programm

> *Fortsetzung von Oswald Teichmüller's unvollendetem Werk: Veränderliche Riemannsche Flächen als verifizierbares formales System*

**[中文版本](README.zh-CN.md)** | **[English](#vision)**

[![Build PDF](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml/badge.svg)](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**[中文版本](README.zh-CN.md)**

---

## Vision

**Recover Teichmüller's unified route from 1944, reunifying complex geometry, topology, and arithmetic within a single framework.**

In 1944, Oswald Teichmüller published *Veränderliche Riemannsche Flächen* (Variable Riemann Surfaces), proposing a unified program for studying how Riemann surfaces vary. This program was interrupted by his death at age 30. Since then, his ideas were inherited separately by quasiconformal analysis (Ahlfors, Bers), deformation theory (Kodaira, Spencer), moduli functors (Grothendieck), and hyperbolic geometry (Fenchel, Nielsen).

**This project reunifies these streams into a formally verifiable system.**

---

## For Beginners

**This repository serves as a comprehensive learning resource for Teichmüller theory and related foundations.**

Our tutorials provide a structured path from basic mathematics to advanced topics:

| Level | Document | What You'll Learn |
|-------|----------|-------------------|
| 📚 Foundation | [Foundations Introduction](docs/tutorial/foundations/foundations_intro.tex) | Sets → Functions → Groups → Complex Analysis → Topology → Riemann Surfaces → Moduli Spaces |
| 🎓 Advanced | [Teichmüller Program](docs/tutorial/advanced/teichmuller_program.tex) | Formalization boundaries, Lean 4 implementation, research frontiers |

**No prior knowledge of Teichmüller theory is required.** The tutorials are designed to be self-contained, building up from high school mathematics level.

---

## For Researchers & AI Agents

**We welcome collaborative exploration of the grand unification program, subject to rigorous review.**

### Open Research Framework

This project supports multi-agent exploration of Teichmüller theory's unification route. Contributions from human researchers and AI agents (Claude, GPT, Gemini, etc.) are encouraged, provided they pass our verification pipeline.

### Review Process

```
Agent Exploration → Mathematical Verification → Formal Check → Peer Review → Merge
```

| Stage | Requirement | Reviewer |
|-------|-------------|----------|
| 1. Mathematical Soundness | Correct definitions, valid proofs | Human expert |
| 2. Formal Verification | Lean 4 compilation, type checking | Automated + Human |
| 3. Integration | Compatible with existing codebase | Maintainer |
| 4. Documentation | Clear explanation, references | Community |

**Note:** Our rigorous review mechanism is still being refined. We aim to maintain the highest standards while enabling efficient collaboration.

### Current Exploration Frontiers

- **Beltrami Equation Solutions**: Completing the measurable Riemann mapping theorem
- **Universal Family Construction**: Proving existence for arbitrary genus
- **Coordinate Comparisons**: Unifying turning-piece, Fenchel-Nielsen, and period coordinates

---

## Teichmüller's Papers

| Paper | Year | Links | Core Contributions |
|-------|------|-------|-------------------|
| *Extremale quasikonforme Abbildungen und quadratische Differentiale* | 1939 | [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0152) | Teichmüller distance, extremal quasiconformal mappings, quadratic differentials |
| *Veränderliche Riemannsche Flächen* | 1944 | [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0174) | Marked Riemann surfaces, analytic families, local deformation coordinates |
| *Gesammelte Abhandlungen* | 1982 | [Springer](https://link.springer.com/book/10.1007/978-3-642-46204-7) | Collected works, ed. Ahlfors & Gehring |

---

## Formalization Progress

### Lean 4 Implementation (`lean/Teichmuller/`)

| Component | File | Status | Description |
|-----------|------|--------|-------------|
| Topology | `Topology.lean` | ✅ Complete | Topological spaces, continuous maps, homotopy closure |
| Complex Structure | `Complex.lean` | ✅ Complete | Charts, atlases, holomorphic transitions |
| Analytic Families | `Family.lean` | ✅ Complete | Dependent sum total spaces, pullbacks, universal properties |
| Modular Group | `Modular.lean` | ✅ Complete | SL₂(ℤ) matrix algebra, upper half-plane action |
| Mathlib Bridge | `MathlibTopology.lean` | ✅ Complete | Standard Mathlib topology objects |
| Complex Atlas | `MathlibComplex.lean` | ✅ Complete | Concrete ℂ charts with `DifferentiableOn` |
| Fiber Bundle | `MathlibFiberBundle.lean` | ✅ Complete | Local trivializations, pullback bundles |
| Beltrami | `MathlibBeltrami.lean` | 🔄 In Progress | Measurable coefficients, transport cocycles |

### Current Boundaries

**Proven:**
- Marking compatibility relation is an equivalence relation
- Teichmüller space as quotient is well-defined
- SL₂(ℤ) determinant-one multiplication with associativity
- Upper half-plane fundamental domain representative theorem
- j-type weight-zero quotient function construction

**In Progress:**
- Measurable Riemann mapping theorem (Beltrami equation existence/uniqueness)
- Complete chart-level cocycle compatibility
- Global universal family existence

---

## Tutorials

| Document | Language | Content |
|----------|----------|---------|
| [Foundations](docs/tutorial/foundations/foundations_intro.tex) | 中文 | From high school math to moduli spaces |
| [Foundations](docs/tutorial/foundations/foundations_intro_en.tex) | English | Complete introductory route |
| [Advanced](docs/tutorial/advanced/teichmuller_program.tex) | 中文 | Lean formalization boundaries |
| [Advanced](docs/tutorial/advanced/teichmuller_program_en.tex) | English | Code correspondence |

---

## Build

```bash
# Install dependencies (requires TeX Live with XeLaTeX)
./scripts/build.sh

# Or manually
latexmk -xelatex -outdir=build docs/tutorial/foundations/foundations_intro.tex

# Lean 4
lake build
```

---

## Research Roadmap

```
P₀  Unified symbols         ✅
P₁  Topology & markings      ✅
P₁.₅ Mathlib integration     ✅
P₂  Analytic families        ✅
P₃  Beltrami equations       🔄
P₄  Modular functions        🔄
P₅  Universal family         ⏳
```

### Next Steps

1. **Beltrami Layer Completion**: Finish measurable differential cocycle, prove existence/uniqueness via contraction mapping
2. **Modular Function Bridge**: Connect j-invariant to Teichmüller space via period mapping
3. **Universal Family**: Construct classification functor for arbitrary marked analytic families

---

## References

- Teichmüller, O. (1944). *Veränderliche Riemannsche Flächen*. Deutsche Mathematik, 7, 344-359. [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0174)
- Ahlfors, L. V. (1966). *Lectures on Quasiconformal Mappings*. Van Nostrand.
- Bers, L. (1970). *Thom's Theorem and Riemann Surfaces*. Lecture Notes in Math.
- Hubbard, J. H. (2006). *Teichmüller Theory and Applications*. Matrix Editions.
- Schappacher, N. & Scholz, E. (1992). *Oswald Teichmüller – Leben und Werk*. Jahresber. DMV. [Online](http://dml.math.uni-bielefeld.de/JB_DMV/)

---

## Contributing

```bash
git clone https://github.com/alexyyyander/teichmuller-tutorial.git
cd teichmuller-tutorial
./scripts/build.sh
```

---

*In memory of Oswald Teichmüller (1913–1943)*