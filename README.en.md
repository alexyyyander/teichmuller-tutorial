# Teichmüller's Unified Research Program

> *Continuing Oswald Teichmüller's unfinished work: unifying variable Riemann surface theory into a verifiable formal system*

[![Build PDF](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml/badge.svg)](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Core Vision

**Recover Teichmüller's unified route from 1944, reunifying complex geometry, topology, and arithmetic within a single framework.**

```
Topological Surface → Complex Structure → Marked Riemann Surface → T(S) → M(S) → Analytic Families
         ↑                                                                    ↓
         └──────────────── Formal Verification (Lean 4) ────────────────────┘
```

---

## Teichmüller and His Legacy

**Oswald Teichmüller** (1913–1943), one of the last heirs of the Göttingen school.

| Paper | Year | Core Contributions |
|-------|------|-------------------|
| *Extremale quasikonforme Abbildungen* | 1939 | Teichmüller distance, extremal mappings, quadratic differentials |
| *Veränderliche Riemannsche Flächen* | 1944 | Marked surfaces, analytic families, local deformation coordinates |

The 1944 posthumous paper proposed a **unified route interrupted by history**. Subsequently, core ideas were inherited by separate branches:

```
        Teichmüller (1944)
              │
    ┌─────────┼─────────┬─────────┐
    ↓         ↓         ↓         ↓
  Ahlfors   Kodaira   Grothendieck  Fenchel
  Bers      Spencer   Mumford      Nielsen
 Quasiconf. Deform.   Moduli       Hyperbolic
```

**This project aims to: reunify these divergent streams into a verifiable formal core.**

---

## Project Structure

```
teichmuller-tutorial/
├── docs/tutorial/           # Mathematical tutorials (bilingual)
│   ├── foundations/          # From high school math to moduli spaces
│   └── advanced/            # Lean formalization boundaries
├── lean/Teichmuller/        # Lean 4 formalization code
│   ├── Topology.lean        # Topology layer
│   ├── Complex.lean         # Complex structure atlases
│   ├── Family.lean          # Analytic family interfaces
│   └── Modular.lean         # Modular group algebra
└── scripts/                 # Build tools
```

---

## Quick Start

### Reading the Tutorial

| Document | Language | Content |
|----------|----------|---------|
| [Foundations](docs/tutorial/foundations/foundations_intro.tex) | 中文 | Complete route from functions to moduli |
| [Foundations](docs/tutorial/foundations/foundations_intro_en.tex) | English | Foundations introduction |
| [Advanced](docs/tutorial/advanced/teichmuller_program.tex) | 中文 | Lean formalization boundaries |

### Building PDFs

```bash
# Local build
./scripts/build.sh

# Or manual build
latexmk -xelatex -outdir=build docs/tutorial/foundations/foundations_intro.tex
```

### Lean Code

```bash
lake build
```

---

## Research Phases

| Phase | Objective | Status |
|-------|-----------|--------|
| P₀ | Unified symbols for four basic axes | ✅ |
| P₁ | Topology, homotopy, and markings | ✅ |
| P₁.₅ | Mathlib entity layer integration | ✅ |
| P₂ | Analytic family structural interfaces | ✅ |
| P₃ | Beltrami equations & quasiconformal deformations | 🔄 |
| P₄ | Modular functions & period mappings | 🔄 |
| P₅ | Universal family construction | ⏳ |

---

## Roadmap

### Near-term (1-2 years)
- Formalize the measurable Riemann mapping theorem
- Complete existence/uniqueness for Beltrami equation solutions
- Connect computable low-genus models

### Medium-term (3-5 years)
- Construct the universal property of Teichmüller space
- Compare turning-piece / Fenchel-Nielsen / period coordinates
- Bridge higher Teichmüller theory with geometric Langlands

### Long-term Vision
**Restore Göttingen school's leadership in complex geometry and moduli spaces.**

---

## References

1. Teichmüller, O. (1939). *Extremale quasikonforme Abbildungen und quadratische Differentiale*
2. Teichmüller, O. (1944). *Veränderliche Riemannsche Flächen*
3. Ahlfors, L. V. (1966). *Lectures on quasiconformal mappings*
4. Hubbard, J. H. (2006). *Teichmüller theory and applications*

---

## Contributing

Contributions of code, documentation, or suggestions are welcome!

```bash
git clone https://github.com/alexyyyander/teichmuller-tutorial.git
cd teichmuller-tutorial
./scripts/build.sh  # Verify build
```

---

*In memory of Oswald Teichmüller (1913–1943)*  
*May the light of mathematical unity illuminate the future*