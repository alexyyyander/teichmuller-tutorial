# Über Teichmüller's Einheitliches Programm

> *Fortsetzung von Oswald Teichmüller's unvollendetem Werk: Veränderliche Riemannsche Flächen als verifizierbares formales System*

**[中文版本](README.zh-CN.md)** | **[English](#vision)**

[![Build PDF](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml/badge.svg)](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## Vision

**Recover Teichmüller's unified route from 1944 as a research program connecting complex geometry, topology, and arithmetic.**

Oswald Teichmüller proposed a unified program for studying variable Riemann surfaces; *Veränderliche Riemannsche Flächen* was published posthumously in 1944, after his death in 1943. Since then, his ideas were inherited separately by quasiconformal analysis (Ahlfors, Bers), deformation theory (Kodaira, Spencer), moduli functors (Grothendieck), and hyperbolic geometry (Fenchel, Nielsen).

**This project studies how these streams can be connected through explicit mathematical interfaces and Lean-checked components. It does not claim that the full theory has already been formalized.**

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
| Topology | `Topology.lean` | 🟡 Interface layer | Topological spaces, continuous maps, homotopy closure |
| Complex Structure | `Complex.lean` | 🟡 Structural interface | Charts, atlases, holomorphicity fields |
| Analytic Families | `Family.lean` | 🟡 Structural interface | Dependent sum total spaces, pullbacks, classification fields |
| Modular Group | `Modular.lean` | 🟡 Algebra/action layer | SL₂(ℤ) matrix algebra and action specifications |
| Mathlib Bridge | `MathlibTopology.lean` | 🟡 Selected bridge | Standard Mathlib topology objects |
| Complex Atlas | `MathlibComplex.lean` | 🟡 Concrete partial layer | Selected ℂ charts with `DifferentiableOn` transitions |
| Fiber Bundle | `MathlibFiberBundle.lean` | 🟡 Interface layer | Local trivializations and pullback structures |
| Čech Descent | `MathlibCech.lean` | 🟡 First concrete layer | Open covers, local global families, biholomorphic overlap maps, triple-overlap cocycle |
| Čech Quotient | `MathlibCechDescent.lean` | 🟡 Concrete quotient skeleton | Disjoint-union local total space, gluing equivalence closure, descended total space and continuous base projection |
| Beltrami | `MathlibBeltrami.lean` | 🔄 In Progress | Measurable coefficients, transport cocycles |

### Latest Concrete Milestone

The open-subspace atlas layer is now implemented in `MathlibComplex.lean`. For an open
`U`, `ComplexSurfaceChart.restrictOpenSubspace` constructs restricted charts,
`ComplexSurfaceAtlas.restrictOpenSubspace` restricts the covered region and proves
that `DifferentiableOn` transition compatibility is inherited, and
`ComplexSurfaceFamilyAtlas.restrictOpenSubspace` preserves the continuous family
projection and the first base-coordinate identity. The key transition statement
is proved on the restricted overlap rather than asserted as a global equality.
For an open base subset `V`, `GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness`
now constructs the global atlas on the canonical subtype pullback by restricting
the old atlas to `projection ⁻¹' V` and transporting it across the canonical
homeomorphism; `restrictBaseOpen` exposes the resulting global analytic family.
The new `canonicalPullback_iterated_homeomorph` identifies the two-stage
pullback with the direct pullback, and
`GlobalHolomorphicMarkedFamily.nestedOpenRestrictionComparison` specializes
this to successive open restrictions `W ⊂ V ⊂ B`, giving the comparison
homeomorphism needed for local gluing. `transportAlongHomeomorph` now
transports the full global atlas along such a comparison, and
`directOpenRestriction` constructs the direct restriction as a global
holomorphic marked family rather than leaving it as a bare topological family.
The three-stage analogue `canonicalPullback_triple_homeomorph`, together with
`tripleOpenRestrictionComparison` and `tripleDirectOpenRestriction`, now
records the first associativity coherence for three successive open restrictions.
The companion `canonicalPullback_triple_right_homeomorph` factors the same
comparison through the other parenthesization, and
`canonicalPullback_triple_factorizations_eq` proves that the two transported
homeomorphisms agree pointwise. The corresponding `*_apply` lemmas make the
identity-on-dependent-sums content explicit, which is the coherence datum
needed before transporting chart atlases along iterated restrictions.
At the chart and atlas layers, `ComplexSurfaceChart.transport_trans` and
`ComplexSurfaceAtlas.transport_trans` now prove that successive transport is
literally the transport along the composite homeomorphism. The global-family
wrapper `GlobalHolomorphicMarkedFamily.transportAlongHomeomorph_trans` lifts
the same coherence to transported family atlases, with the composite
projection law recorded explicitly.
The new `MathlibCech.lean` layer packages an actual open cover, a global
holomorphic marked family over every subtype base, pointwise biholomorphic
overlap maps with chartwise holomorphicity and marking compatibility, and an
equality of homeomorphisms on every triple overlap. This is the first concrete
descent datum in the project; the remaining step is to construct a descended
global family from such data rather than only record the cocycle.
The new `MathlibCechDescent.lean` layer now takes the first quotient step:
it forms the disjoint union of the local total spaces, closes the elementary
overlap gluings under equivalence, and defines the quotient total space.
The local base projection descends through that quotient and is proved
continuous; each recorded overlap transition is proved to identify the two
corresponding quotient points. The descended complex atlas and global marking
are intentionally still the next layer, since they require chart descent
rather than only quotienting the underlying topological carriers.

### Current Boundaries

**Proven at the current interface or selected-concrete level:**
- Marking compatibility relation is an equivalence relation
- Teichmüller space as quotient is well-defined
- SL₂(ℤ) determinant-one multiplication with associativity
- Upper half-plane fundamental domain representative theorem
- j-type weight-zero quotient function construction

These items do not by themselves constitute a formalization of the standard
Teichmüller space, the measurable Riemann mapping theorem, the moduli functor,
or the existence of a universal family.

**In Progress:**
- Measurable Riemann mapping theorem (Beltrami equation existence/uniqueness)
- Complete chart-level cocycle compatibility
- Global universal family existence

---

## Tutorials

| Document | Language | Content |
|----------|----------|---------|
| [Foundations](docs/tutorial/foundations/foundations_intro.tex) | 中文 | From high school math to moduli spaces |
| [Foundations](docs/tutorial/foundations/foundations_intro_en.tex) | English | English foundations draft |
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
P₀  Unified symbols         🟡
P₁  Topology & markings      🟡
P₁.₅ Mathlib integration     🟡
P₂  Analytic families        🟡
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
