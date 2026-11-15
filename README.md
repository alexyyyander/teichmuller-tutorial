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
| Complex Atlas | `MathlibComplex.lean` | 🟡 Concrete partial layer | Selected ℂ charts with `DifferentiableOn` transitions, fixed-parameter fibre slices, and marked fibre construction |
| Fiber Bundle | `MathlibFiberBundle.lean` | 🟡 Interface layer | Local trivializations and pullback structures |
| Čech Descent | `MathlibCech.lean` | 🟡 First concrete layer | Open covers, local global families, biholomorphic overlap maps, inverse law, triple-overlap cocycle |
| Čech Quotient | `MathlibCechDescent.lean` | 🟡 Concrete quotient skeleton | Disjoint-union local total space, cocycle-compatible gluing steps, local injectivity, overlap total-space homeomorphisms, and descended chart transport |
| Concrete Čech Family | `MathlibCechConcrete.lean` | 🟡 Concrete atlas-comparison layer | Multi-patch restrictions, overlap atlases, exact atlas transport equality, jointly holomorphic transition, and descended atlas witness |
| Torus Čech Bridge | `MathlibTorusCech.lean` | 🟡 Selected compact-fibre layer | Genus-one lift/deck witness, pointwise source/target overlap-to-lift coordinate comparison, and explicit Čech descent |
| Beltrami | `MathlibBeltrami.lean` | 🔄 In Progress | Measurable coefficients, transport cocycles |
| Beltrami Family Bridge | `MathlibBeltramiFamily.lean` | 🟡 Concrete bridge | Parameter model, anchored quotient, coefficient-level classification, transported marked-surface family, data-carrying `AnalyticFamily`, joint-coordinate families, and a conditional local total-space chart witness |
| Scaled Neumann Family | `MathlibBeltramiNeumannOperatorFamily.lean` | 🟡 Concrete operator shape | Continuous scalar coefficients, fixed operator scaling `K_b = μ_b • S`, uniform contraction radius, and continuous fixed-point family |
| Multiplier Neumann Family | `MathlibBeltramiNeumannMultiplierFamily.lean` | 🟡 Concrete (L^p) family | Parameter-dependent coefficient multipliers `M_{μ_b}`, fixed singular operator `B`, operator-norm continuity, uniform contraction, and continuous Neumann solution family |
| Beurling L² Family | `MathlibBeltramiNeumannBeurlingFamily.lean` | 🟡 Closed-subdisk model | Constant-coefficient (L^2) multipliers `M_μ = μ id`, Fourier-defined Beurling operator, uniform radius on `‖μ‖ ≤ r < 1`, and continuous Neumann family |
| Profile Beurling Family | `MathlibBeltramiNeumannProfileFamily.lean` | 🟡 Spatial-profile model | Fixed bounded measurable profile `a(z)`, scaled coefficients `μ_b(z) = b a(z)`, exact multiplier identity `M_{μ_b} = b M_a`, and uniform `L²` Neumann family on `‖b‖ ≤ r` with `r‖a‖∞ < 1` |
| Neumann State Bridge | `MathlibBeltramiNeumannBridge.lean` | 🟡 Conditional analytic bridge | Continuous fixed-point states, continuous state evaluation into pointwise/a.e. Beltrami families, and inverse-evaluation data feeding the local chart continuity gate |

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
The new `GlobalHolomorphicMarkedFamily.PullbackWitness.toIterated` transports
any direct witness for `f ∘ g` to an actual atlas witness on the iterated
pullback by `canonicalPullback_iterated_homeomorph`; it proves cover, topology,
projection, and base-coordinate compatibility. `pullbackOfIterated` packages
that transported atlas as a global holomorphic marked family, so the direct
versus iterated distinction is now present at the full total-space level.
The reverse map `GlobalHolomorphicMarkedFamily.IteratedPullbackWitness.toDirect`
transports an iterated witness back to the one-stage presentation. The global
classifier constructor `GlobalHolomorphicFamilyClassification.pullbackWithIteratedWitness`
now consumes an iterated witness at the universal-property boundary, converts
it through this inverse transport, and returns the standard direct-pullback
classification with the composite classifying map. This establishes a
two-way atlas bridge without claiming that the two dependent-sum topologies
are definitionally equal; the remaining coherence target is compatibility of
successive classifier base changes with the three-stage atlas comparison.
The analytic composition layer is now also concrete: `ChartwiseHolomorphicMap.trans`
proves chartwise holomorphicity by decomposing the source domain according to
the open chart pieces of the intermediate atlas, `AtlasHolomorphicEquiv.trans`
packages the forward and inverse proofs, and `HolomorphicFiberwiseEquiv.trans`
lifts the result over a marked family. Finally,
`GlobalHolomorphicFamilyClassification.composeWithWitness` composes two global
classifiers using the second classifier's pullback atlas and an iterated
pullback witness for the first. Its classifying map is proved to be the
composite `c.map ∘ d.map`, while the atlas topology remains explicit data.
The next coherence target is the equality of the two parenthesizations for
three successive classifier compositions. This target is now represented by
`GlobalHolomorphicMarkedFamily.TriplePullbackWitness`, whose explicit atlas on
the three-stage iterated pullback transports to both parenthesizations through
`toLeftIterated` and `toRightIterated`. The theorem
`GlobalHolomorphicFamilyClassification.composeWithWitness_assoc_map` proves
that the two witnessed classifier composites have the same classifying map,
and `composeWithWitness_assoc_realization_map` proves pointwise equality of
their actual fibrewise analytic realizations. The lower-level
`HolomorphicFiberwiseEquiv.trans_assoc_map` records the corresponding
associativity of biholomorphic fibre maps.
The fine-moduli interface now consumes that result: given a universal family
`u`, a witnessed classification `d : F → G`, and the required pullback atlas
witnesses, `GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp`
proves that the unique classifying map for `G` is exactly the composite of the
classifying map for `F` with `d.map`. Thus the universal-property layer now
records functoriality of Teichmüller classifying maps, while still exposing the
geometric witness needed to make the composition analytic.
Its three-step companion
`GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp_comp` derives the
corresponding (U \to F \to G \to H) composite by applying the universal
uniqueness theorem twice, making the higher associativity visible at the
moduli-map level.
The explicit nonzero affine Beltrami family now closes its own coefficient
round trip: `constantBeltramiAffinePointwiseFamilyWitness_recover_coefficient`
proves that the coefficient recovered from the real `fderiv` of the normalized
solution is exactly the original parameter at every point. This is a concrete
family-level regression theorem, while remaining deliberately separate from
holomorphic-family classification and from the general measurable Riemann
mapping theorem.
The operator-family layer now also exposes a concrete scalar specialization:
`ScaledNeumannOperatorFamily` records a continuous scalar coefficient
`μ : B → ℂ`, a fixed continuous-linear operator `S`, a uniform
radius `r < 1`, and the bound
`‖μ b‖ * ‖S‖ ≤ r`. Its
`toNeumannOperatorFamily` constructor builds the actual kernel
`K b = μ b • S`; Lean proves the operator-norm bound, continuity of the
kernel, and continuity of the resulting fixed-point state. This is the precise
operator shape needed before replacing the abstract kernel by a Beurling or
coefficient-multiplier construction.
The next layer now performs that replacement on `L^p`: `MultiplierNeumannOperatorFamily`
records a parameterized `BoundedScalarCoefficient`, the operator-norm continuity
of its concrete multiplier `M_{μ_b}`, a fixed candidate singular operator `B`,
and a uniform bound on `‖M_{μ_b} B‖`. Its constructor builds
`K_b = M_{μ_b} ∘ B` and reuses the proved variable-kernel fixed-point theorem.
The continuity of the multiplier family is deliberately an explicit analytic
input: pointwise continuity of representatives alone does not imply operator-norm
continuity on `L^p`.
The new `MathlibBeltramiNeumannBeurlingFamily.lean` closes a concrete (L^2)
model on the closed subdisk `‖μ‖ ≤ r` with `r < 1`. For constant coefficients,
Lean proves `M_μ = μ • id` as an equality of continuous linear maps; taking the
Fourier-defined `beurlingL2Operator` as the fixed singular operator therefore
produces `K_μ = M_μ ∘ 𝓑₂`, a uniform contraction family with continuous fixed-point
solutions. The restriction to a closed subdisk is essential: the whole open unit
disk has no single radius strictly below one.
The new `MathlibBeltramiNeumannProfileFamily.lean` removes the spatial constancy
while keeping the first model honest and controllable. Given one bounded measurable
profile `a : ℂ → ℂ` with an a.e. NNReal bound, it defines
`μ_b(z) = b * a(z)` for `‖b‖ ≤ r`. Lean proves the exact operator identity
`M_{μ_b} = b • M_a`, upgrades it to operator-norm continuity in `b`, and combines it
with the Fourier-defined `beurlingL2Operator`. The uniform contraction hypothesis is
now visibly `r * ‖a‖∞ < 1`, so the resulting fixed-point state is continuous on the
closed parameter disk. This is a genuinely spatially varying coefficient layer, but it
still fixes the profile `a`; arbitrary parameter-dependent profiles and the principal-
value/Fourier identification of the singular operator remain subsequent goals.
The new `MathlibBeltramiNeumannBridge.lean` makes the next analytic boundary
explicit. `NeumannOperatorFamily.continuous_solution` supplies continuity of
the Banach fixed-point state under a uniform contraction radius. A separate
`NeumannBeltramiEvaluationBridge` then requires a jointly continuous evaluation
map from the state space and coordinate to `ℂ`, and derives the joint continuity
of the pointwise and a.e. Beltrami solution families. The companion
`NeumannBeltramiInverseEvaluationBridge` feeds a jointly continuous inverse
evaluation into `MathlibFormal.NormalizedBeltramiInverseContinuityWitness`.
Thus the formal chain now separates fixed-point stability, map decoding, and
inverse-coordinate regularity; none of these bridges is misreported as the
general measurable Riemann mapping theorem.
The new `NormalizedBeltramiParameterModel` packages the next reusable layer:
it records coefficient recovery, an anchored parameter map, continuity, and
parameter separation, and exports the existing
`ParameterContinuousBeltramiFamilyData`. The affine instance
`constantBeltramiAffineParameterModel` is then embedded into the actual
constant-plane total space by
`NormalizedBeltramiParameterModel.toConstantPlaneCompatibleFamily`, with the
projection equality and open-embedding statement checked in Lean.
The same interface now exposes the anchored `Setoid` and its quotient, together
with a proved equivalence back to the original parameter space. A separate
`NormalizedBeltramiParameterClassification` records a continuous classifying
map and equality of the complete coefficient functions; anchor injectivity
proves uniqueness of that map. Continuous injective reparametrizations and the
corresponding affine classification witness are also formalized. This is a
coefficient-level classification layer, not yet the full marked holomorphic
Teichmuller quotient.
The next bridge is now explicit: `beltramiSolutionChart` transports a one-chart
complex structure along the inverse of each normalized solution, while the solution
itself is retained as the marking. `NormalizedBeltramiParameterModel.toMarkedSurfaceFamily`
assembles these fibres into the existing `Family` interface, and
`toMarkedSurfaceFamilyEquiv` proves the fibrewise chartwise biholomorphism from the
constant marked plane. The identity-base witness
`toMarkedSurfaceFamilyClassification` therefore reaches
`HolomorphicFamilyClassification`; the affine disk has the concrete wrapper
`constantBeltramiAffineMarkedSurfaceClassification`. The total-family field still
uses the constant-plane topology and `analyticVariation := True`, so this is not yet
a jointly holomorphic two-dimensional family, a universal property, or the full
Teichmuller marked quotient.
The next refinement makes the boundary data-carrying. `toAnalyticFamily` supplies an
actual trivial-bundle witness and the fibrewise holomorphic maps;
`toLocalJointlyHolomorphicFamily` and `toJointlyHolomorphicFamily` supply the joint
coordinate function (the second projection) and prove its `Differentiable` field.
The remaining topological input is isolated as
`NormalizedBeltramiInverseContinuityWitness`: joint continuity of the inverse solution
map. Given that witness,
`toLocalJointlyHolomorphicChartWitness` constructs the local total-space homeomorphism
and the open coordinate range. No general inverse-continuity theorem is claimed here;
this is precisely the analytic gate that must be proved for a genuine parametrized
Beltrami/Riemann mapping theorem.
For the constant-coefficient affine disk this gate is now discharged explicitly:
`constantBeltramiAffineInverseContinuityWitness` proves joint continuity of the
closed-form inverse on `constantBeltramiParameter × ℂ`,
`constantBeltramiParameterComplexBaseChart` supplies the tautological open unit-disk
base chart, and `constantBeltramiAffineLocalJointlyHolomorphicChartWitness` instantiates
the generic constructor. Thus this affine regression model has an actual local
total-space `Homeomorph` and open coordinate range, while the general measurable
Riemann mapping theorem remains outside the formalized claim.
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
corresponding quotient points. The generic descended chart family is now also
constructed once an open quotient witness is available, rather than leaving
chart descent as an untyped future step.
The same layer now derives the pointwise inverse law for an overlap transition
from the self-overlap and triple-overlap axioms, and uses it to prove that
`gluingStep` is reflexive, symmetric, and transitive. Consequently
`gluingEqvGen_iff_gluingStep` identifies the equivalence closure with one
actual cocycle-compatible gluing step. Thus the quotient relation is backed
by actual cocycle data, not only by an unchecked relation symbol.
The same file now defines the continuous `localQuotient` map for every local
total space, proves its compatibility with every overlap transition, and
proves `localQuotient_injective`: a local piece has no extra identifications
inside the quotient. Under the precisely isolated hypothesis that the global
quotient map is open, the same file proves that every `localQuotient` is an
open embedding, that `localChartImage` is open, and constructs
`localChartHomeomorph_of_isOpenMap_quotientMk`. The remaining geometric input
is the construction of the descended chart transitions as jointly holomorphic
maps.
The new `OpenGluingWitness` isolates the exact missing topological input:
every open set must remain open after one-step gluing saturation. This is not
left as a slogan: `quotientMk_preimage_image` proves that the preimage of a
quotient image is exactly `gluingStepImage`, using the cocycle-derived
equivalence-closure theorem, and `isOpenMap_quotientMk_of_openGluing` upgrades
that witness to a genuine global open quotient map. The remaining geometric
work is now isolated more sharply. `CechOverlapSourceTotal` and
`CechOverlapTargetTotal` are the dependent-sum total spaces over an overlap,
with topologies induced from the local total spaces. The range lemmas prove
that both inclusion maps have open images, and hence are open maps. The
`gluingStepImage_eq_iUnion_overlapImages` theorem expresses one-step
saturation as the union of target images of source preimages. Consequently a
`TotalOverlapHomeomorphWitness`—an actual homeomorphism of overlap total
spaces whose function is the varying transition—produces
`openGluingWitness_of_totalOverlapHomeomorph`, rather than assuming global
quotient openness. `descendedChartFamily_of_totalOverlapHomeomorph` then
transports the chart family directly. For the concrete multi-patch data coming
from one global family, `multiPatchOverlapHomeomorph` supplies the required
joint overlap homeomorphism, so the open quotient witness and descended chart
family are now actual definitions. For arbitrary local families, the remaining
task is still to construct this joint overlap homeomorphism from analytic
variation; fibrewise holomorphic transition data alone is not enough.
The new `JointlyContinuousTransitionData` makes that boundary constructive:
it separates the joint transition and inverse, their two inverse laws, both
continuity proofs, and the equality with the original fibrewise transition.
`totalOverlapHomeomorphWitness_of_jointlyContinuous` bundles exactly these
fields into the quotient-facing witness. Thus the current proof obligation is
now a finite, inspectable list of joint-variation obligations rather than an
opaque global openness assumption. The convenience constructors
`openGluingWitness_of_jointlyContinuous` and
`descendedChartFamily_of_jointlyContinuous` expose the complete downstream
pipeline from this list of fields.
As a concrete regression case, `MathlibCechConcrete.lean` now takes any
existing `GlobalHolomorphicMarkedFamily`, restricts it to the one-patch cover
`Set.univ`, and constructs the identity-on-overlap Čech data. The theorem
`singlePatchJointlyContinuousTransition` then fills the joint fields by the
subsingleton-indexed self-law. This verifies that the interface is realizable
from an actual analytic family in the trivial-cover case. The same file now
also defines `multiPatchCechDescentData`: for an arbitrary open cover
`cover : I → Set B`, it restricts the one global family on every patch and
constructs the actual fibrewise identity transitions on overlaps, including
marking compatibility and the triple-overlap cocycle. The joint continuity
step is isolated into an explicit comparison with the overlap pullback
topology, rather than identifying differently tagged local total spaces by
definitional equality.
The new `multiPatchOverlapHomeomorph` construction now supplies the
corresponding actual homeomorphism for every overlap by comparing both
restricted spaces with the same direct pullback of the global family. This
proves the topological comparison layer. The new
`canonicalPullback_comp_homeomorph_apply` identity lemma and an explicit
base-point equality discharge the dependent transport, proving that this
total-space map is exactly the declared fibrewise transition.
The topology comparison is now explicit in `MathlibFamily.lean`:
`pullbackTopology_eq_induced_total_of_isInducing` proves equality of the
canonical pullback topology with the topology induced by the map into the old
total space whenever the base map carries the inducing-topology equality.
In `MathlibCechDescent.lean`, the two overlap inclusions are also proved to be
actual `IsOpenEmbedding`s (not merely open maps), with injectivity and open
image checked separately. The dependent-transport step identifying
`multiPatchOverlapHomeomorph` with the declared fibrewise transition is now
proved. `multiPatchJointlyContinuousTransition` packages the resulting
homeomorphisms, inverse laws, continuity, and agreement theorem into
`JointlyContinuousTransitionData` for arbitrary open covers.
The new theorem `GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness_chart_apply_val`
makes the local coordinate calculation explicit: after the canonical pullback
homeomorphism, a restricted chart has exactly the same coordinate value as the
original global chart. `multiPatchLocalChart_apply_val_eq_global` exposes the
same fact directly at the multi-patch Čech layer. In addition,
`multiPatchOverlapAtlas_coverSet_eq_targetTransport` proves that the target
overlap cover set agrees with the transport of the source cover set. These are
genuine pointwise and set-theoretic comparison lemmas. The dependent atlas
equality is now also proved by `multiPatchOverlapAtlas_eq_targetTransport`:
domain/range equality and pointwise equality of the restricted global charts
are assembled into the exact atlas transport statement.
The atlas layer now also contains `ComplexSurfaceAtlas.ext`: after the
topology, index, cover set, and dependent chart fields have been identified,
the atlas-level transition proof is discharged by proof irrelevance. This
turns the remaining multi-patch comparison into a finite list of geometric
chart equalities rather than repeated structure-elimination bookkeeping.
The local analytic input is now exposed separately as well:
`multiPatchLocalAtlas_transition_differentiableOn` and its Čech-data
specialization obtain every local chart transition from the actual atlas of
`GlobalHolomorphicMarkedFamily.restrictBaseOpen`. For arbitrary separately
specified local families, the remaining gap is still the stronger
joint-holomorphic statement for the overlap total-space transition; for the
concrete multi-patch restriction of one global family, that comparison is
closed below by `multiPatchOverlapAtlas_eq_targetTransport`.
The next geometric layer is now concrete too. `overlapSourceFibreMap` and
`overlapTargetFibreMap` identify the two dependent-sum overlap spaces with
open subspaces of the corresponding local family total spaces; their range
equalities, continuity, injectivity, and open-image proofs combine into actual
`IsOpenEmbedding`s. `overlapSourceAtlas` and `overlapTargetAtlas` then restrict
the genuine two-complex-dimensional local surface atlases and transport them
back along those open embeddings. Their topologies are proved to be exactly
`cechOverlapSourceTopology` and `cechOverlapTargetTopology`, and their chart
transitions inherit concrete `DifferentiableOn` proofs. This advances the
formal chain from overlap topology to overlap complex geometry.
`multiPatchOverlapAtlas_eq_targetTransport` now identifies the two transported
atlases exactly for the concrete global-family construction, and the concrete
`multiPatchJointlyHolomorphicTransition` is consequently inhabited. The new
`multiPatchOpenGluingWitness` and `multiPatchDescendedChartFamily` complete the
topological quotient descent for this concrete construction. The remaining
geometric/analytic work is the descended chart-transition holomorphic witness,
as well as the corresponding joint-variation theorem for arbitrary local
families.

The next analytic refinement is now represented by actual atlas data as well:
`MathlibComplex.lean` defines `ComplexSurfaceAtlas.HolomorphicMap` and
`ComplexSurfaceAtlas.HolomorphicEquiv` by transporting target charts to the
source and asking for the resulting two-variable chart transitions to be
`DifferentiableOn`. The theorems
`ComplexSurfaceAtlas.transport_holomorphicMap` and
`ComplexSurfaceAtlas.commonTransport_holomorphicMap` prove the canonical
transport cases; `commonTransport_holomorphicEquiv` packages the same
cancellation in both directions when two atlases come from one mother atlas.
`MathlibCechDescent.lean` then defines
`JointlyHolomorphicTransitionData` and its constructor
`ofHolomorphicEquiv`, refining the continuous overlap witness by forward and
inverse chartwise holomorphic fields for `overlapSourceAtlas` and
`overlapTargetAtlas`. The remaining multi-patch theorem is now sharply typed:
construct the common-mother-atlas comparison for the concrete overlap
restriction, rather than assert an undifferentiated analytic proposition.

That comparison is now represented by
`CommonMotherAtlasTransitionWitness`. It records a mother atlas, source and
target homeomorphisms into it, the two atlas transport equalities, and the
comparison-composition identity. Its `toHolomorphic` method invokes
`commonTransport_holomorphicEquiv`, so the analytic witness is generated from
the geometric data. The one-patch model is fully closed:
`singlePatchCommonMotherAtlasWitness_holomorphic` constructs actual jointly
holomorphic transition data from the global marked family. For the genuine
multi-patch construction,
`multiPatchCommonMotherAtlasWitness_of_targetTransport` and
`multiPatchJointlyHolomorphicTransition_of_targetTransport` isolate the exact
remaining obligation:
`overlapTargetAtlas = transport overlapSourceAtlas (joint transition)⁻¹` on
every overlap. Thus the current code does not claim the multi-patch analytic
step as an opaque proposition; it turns it into one concrete atlas-comparison theorem.
That theorem is now proved for the global-family multi-patch construction:
`multiPatchOverlapAtlas_eq_targetTransport` establishes the exact dependent
chart equality, using the overlap domain/range comparisons and the pointwise
identity of the restricted global coordinates. Consequently
`multiPatchCommonMotherAtlasWitness` and
`multiPatchJointlyHolomorphicTransition` are actual definitions with no
remaining target-atlas hypothesis. The concrete quotient-side topological
descent is now also named by `multiPatchOpenGluingWitness` and
`multiPatchDescendedChartFamily`; the remaining boundary is the holomorphic
transition field of `DescendedAtlasHolomorphicWitness`.
This turn adds reusable chart-level infrastructure for that comparison:
`ComplexSurfaceChart.transport_range` and `ComplexSurfaceChart.ext`, together
with `retopologizeHomeomorph_subtype_val_apply`, make the domain/range/chart
fields and proof-irrelevant subtype transports explicit. It also proves
`multiPatchJointlyTransitionHomeomorphInv_apply_id`: after the overlap base
point equality is exposed, the inverse joint transition is literally the
identity on the dependent-sum carrier. The remaining obstruction is now
confined to comparing the dependent local chart fields on different base
subtypes. In particular, `retopologizeHomeomorph` now keeps the original
`toFun` and `invFun` definitionally and transports only the continuity proofs;
this removes an avoidable `Eq.rec` layer from later chart calculations. No
multi-patch analytic theorem is claimed prematurely.

The first descended holomorphic boundary is now closed in a genuine base case.
`ComplexSurfaceChart.transitionMap_self_differentiableOn` proves directly that
every chart's self-transition is differentiable on its overlap. For a
subsingleton cover index, `localQuotient_surjective_of_subsingleton` upgrades
the already-proved local quotient injection to surjectivity, and
`localQuotientHomeomorph_of_isOpenMap_of_subsingleton` packages the local
quotient map as an actual homeomorphism of total spaces. If the descended chart
index is subsingleton, `descendedAtlasHolomorphicWitness_of_subsingleton_index`
then constructs the complete `DescendedAtlasHolomorphicWitness`; the concrete
one-patch wrapper is
`singlePatchDescendedAtlasHolomorphicWitness`. This is a proved regression
case, not a placeholder for the general multi-chart transition theorem.

The current turn advances the general multi-patch quotient interface. The
new `quotientMk_eq_iff_gluingStep` turns equality in the quotient into one
explicit cocycle gluing step. The source and target overlap atlases now have
pointwise coordinate compatibility lemmas,
`overlapSourceAtlas_chart_apply_val` and
`overlapTargetAtlas_chart_apply_val`, proved from restriction and transport
of the actual local surface charts. Most importantly,
`descendedChart_overlap_subset_joint_overlap` proves that every overlap of
two descended quotient charts is contained in the corresponding overlap of
the transported Čech charts. The proof extracts local representatives, uses
quotient equality and the cocycle gluing relation to recover a common Čech
overlap point, and then compares descended chart coordinates with local
coordinates. This is a genuine multi-patch theorem, not a subsingleton
reduction.

The remaining analytic step is now closed. `retopologizeBothHomeomorph` and
`jointTransitionHomeomorph` isolate the equality between the Čech overlap
topologies and the overlap-atlas topologies. The theorem
`descendedChart_transitionMap_eq_joint_transition` then proves, pointwise on
every descended chart overlap, that the quotient chart transition is exactly
the jointly holomorphic Čech transition. Hence
`descendedTransitionCompatibility_of_jointlyHolomorphic` constructs the
compatibility structure without an extra axiom, and
`descendedAtlasHolomorphicWitness_of_jointlyHolomorphic_transition` produces
the actual descended holomorphic atlas witness. The concrete multi-patch
wrapper `multiPatchDescendedAtlasHolomorphicWitness` now closes the pipeline
from a global holomorphic marked family and an open cover to a descended
complex atlas with verified transition differentiability.

The quotient atlas is now also connected back to the family direction. The
generic `descendedFamilyAtlas` takes the common parameter-coordinate
compatibility of the local families and proves that every descended chart has
the same first coordinate as the descended projection. The concrete wrapper
`multiPatchDescendedFamilyAtlas` obtains this compatibility definitionally from
the restricted local families, so open-cover descent now produces a genuine
`ComplexSurfaceFamilyAtlas` with continuous projection. This is a family-atlas
construction, not yet a construction of a descended marking, a fibrewise
universal family, or a moduli classification theorem.

The next boundary is now also closed at the marking level. `DescendedFiber`
records the fibre of the quotient projection, `descendedMarking` chooses one
cover chart for a base point, and `descendedMarking_eq_local` proves that every
local representative gives the same quotient point by the actual
`transition_marking_commutes` law. `DescendedMarkingWitness` packages this
choice-independent marking, while `DescendedMarkedAtlas` combines it with the
descended family atlas. The concrete wrappers
`multiPatchDescendedMarkingWitness` and `multiPatchDescendedMarkedAtlas` apply
this construction to the multi-patch global family.

The fibre-slice layer has now been made explicit in `MathlibComplex.lean`.
`ComplexSurfaceFamilyAtlas.Fiber` and `fiberDomain` define the fixed-parameter
fibre and its chart domains, while
`ComplexSurfaceFamilyAtlas.FiberSliceAtlasWitness` records the minimal local
slice inverse and the equality between the fibre coordinate and the second
coordinate of the total-space chart.  From this witness,
`FiberSliceAtlasWitness.toComplexAtlas` constructs a genuine one-dimensional
`ComplexAtlas`.  The theorem
`FiberSliceAtlasWitness.total_transition_eq_slice_transition` identifies its
transition with the second component of the total transition at constant base
coordinate, and `FiberSliceAtlasWitness.transition_holomorphic` derives
holomorphicity by composition with that constant-coordinate embedding.

Finally, `MarkedFiberSliceAtlasWitness` and
`MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface` attach an actual
homeomorphic marking to the fixed fibre.  This closes the logical gap between
a two-complex-dimensional descended total-space atlas and a marked
one-complex-dimensional fibre.  It still does not claim that every descended
quotient already carries such slice witnesses: supplying them uniformly in
the base, proving their joint analytic variation, and comparing the dependent
sum topology with the descended total space remain separate inputs.

The next assembly layer is now explicit in MathlibFamily.lean.  The structure
MarkedFiberSliceFamilyAssemblyWitness packages a marked slice for every base
point, a topology on the dependent sum of slice carriers, a homeomorphism from
that dependent sum to the original total space, and compatibility with the
family projection.  Its toFamily construction produces an actual
ComplexSurfaceFamily.Family; the existing analyticVariation : Prop field is
carried through unchanged, so this constructor does not claim the missing
joint holomorphic-variation theorem.

The next step is now formalized as well.  `ComplexSurfaceAtlas.transport_univ`
transports the two-dimensional atlas to a dependent-sum carrier even when the
carrier universe is larger than the source universe; the only bookkeeping is
an `ULift` of the chart index.  The induced
`MarkedFiberSliceFamilyAssemblyWitness.toFamilyAtlas` keeps the family
projection as the first dependent-sum coordinate and transports all chart
transitions without changing their holomorphicity.  If the original covered
region is all of the total space, the conditional constructor
`toGlobalHolomorphicMarkedFamily` produces a genuine global family atlas.
The condition is intentional: joint analytic variation is still an explicit
input, not a consequence of fibrewise slice atlases.

The Čech layer now names the same boundary instead of leaving it implicit.
`HolomorphicCechDescentData.DescendedFiberSliceFamilyAssemblyWitness` packages
the descended atlas, the descended fibre markings, the parameter-coordinate
compatibility, and the remaining uniform slice/comparison witness.  Its
`toFamily` and `toGlobal` constructors call the genuine family assembly above.
Thus the quotient construction is connected to the family layer, but only
under explicit slice and total-space comparison data; it still does not assert
that an arbitrary Čech quotient has those data.  The concrete multi-patch
regression file fixes the fibre-carrier universe explicitly, making this
conditional bridge stable under the universe-polymorphic family interface.

The joint-variation interface has also been made computationally directional.
For JointlyHolomorphicFamily, sliceCoordinate extracts the coordinate at a
fixed parameter, sliceCoordinate_eq_chart identifies it with the selected
fibre chart, and slice_differentiable proves its complex differentiability by
the chain rule.  Thus the formal implication

jointly holomorphic coordinate => fibrewise holomorphic slice

is now an actual theorem; the converse remains deliberately unavailable.

The next layer is no longer tied to a globally chosen base coordinate:
JointlyHolomorphicFamilyOver accepts any complex normed base B, while
ComplexBaseChart records an open base subset, an open subset of ℂ, and their
actual Homeomorph.  LocalJointlyHolomorphicFamily now depends on the
underlying Family itself (rather than on the larger AnalyticFamily wrapper),
so a family equality can be used directly as a dependent-type transport.  It
states joint holomorphicity in that local coordinate and proves the
corresponding fixed-point slice theorem.  The Čech quotient exposes the same
requirement through LocalJointlyHolomorphicVariationWitness: in the first
same-carrier-universe specialization, every patch must supply a base chart,
an analytic-family witness identified with the stored local family, and a
joint variation witness.  It now also records a differentiable coordinate
change for every ordered pair of patches and proves its equality with the two
base coordinates on overlaps.  CechJointlyHolomorphicVariationWitness
extends this data with a genuine ℂ × ℂ → ℂ fibre-transition coordinate, its
Differentiable certificate, and an agreement equation with the actual Čech
transition; a theorem then identifies the target joint coordinate with the
target fibre chart.  This is an adapter for future descent, not an existence
theorem for arbitrary local analytic data or a fully universe-polymorphic
construction.  The new `jointTransitionCoordinate` assembles the base
coordinate and fibre coordinate into a genuine `ℂ × ℂ → ℂ × ℂ` map, proves its
`Differentiable` certificate by `prodMk`, and identifies its value on an
overlap with the target base coordinate and target fibre coordinate.  The
`LocalJointlyHolomorphicChartWitness` layer now adds the missing topological
content: it records a local trivialization of the dependent total space, an
open coordinate range, and a genuine `ComplexSurfaceChart`; its unit-index
atlas inherits self-transition differentiability.  The Čech witness now
requires one such local chart on every cover patch and exposes it through
`localAtlas`.  The new `localChartSourceMap` and `localChartTargetMap` insert
each Čech overlap into the corresponding base-chart domain; Lean proves that
both maps are open embeddings by comparing their induced topologies with the
open ranges of `overlapSourceFibreMap` and `overlapTargetFibreMap`.  Restricting
the local atlas to those open images and transporting it back gives
`localChartSourceAtlas` and `localChartTargetAtlas` on the actual overlap
carriers.  Finally, `CechLocalChartComparisonWitness` records the remaining
chartwise `ComplexSurfaceAtlas.HolomorphicEquiv` comparisons with
`overlapSourceAtlas` and `overlapTargetAtlas`, using the identity map on the
overlap carrier.  This is an explicit compatibility interface: its existence
is not inferred from fibrewise homeomorphisms, and its next use is to feed the
comparison into `JointlyHolomorphicTransitionData`.  The identity comparison
for a transported atlas is now proved once and for all, so explicit atlas
equalities can be normalized into a `CechLocalChartComparisonWitness`.  The
new `CechLocalTransitionAssemblyWitness` then takes a holomorphic transition
in the selected local charts and, by dependent atlas casting, produces an
actual `JointlyHolomorphicTransitionData`.  The remaining analytic input is
therefore visible as `localHolomorphic`, rather than hidden in a coercion.
The newer `CechLocalCoordinateTransitionWitness` makes that input more
constructive: it asks for a globally `Differentiable` coordinate model for
each forward and inverse chart pair and an equality with the genuine
`transitionMap` on its overlap; `toAssembly` turns these fields into the
bundled `HolomorphicEquiv`.  Conversely, `ofJointlyHolomorphic` adapts an
already constructed concrete `JointlyHolomorphicTransitionData` whenever the
selected local atlases are explicitly identified with the canonical overlap
atlases.  Thus the current formal boundary is now the chart-transition
equalities themselves, not the conversion from coordinates to a holomorphic
map.

The affine-plane regression model now fills the local-chart layer with actual
data. `ComplexBaseChart.openSubset` represents an open subset of the original
complex base, and `JointlyHolomorphicFamily.restrictToBaseOpen` restricts the
jointly holomorphic family to that chart. The definitions
`affinePlaneTotalHomeomorph` and `affinePlaneLocalTotalHomeomorph` prove the
global and open-subset total-space product identifications. The explicit
homeomorphism `complexShear` models `(a,z) ↦ (a,z-a)`, and
`affinePlaneLocalChartWitness` packages it with the open range
`U ×ˢ univ`; its `toComplexSurfaceChart` and `toComplexSurfaceAtlas` outputs
are genuine local complex-surface charts. This completes the selected
concrete implication

analytic family + local base chart => actual local complex-surface chart

for the translated-plane family. It does not yet produce a nontrivial
Teichmüller deformation or derive arbitrary Čech local chart witnesses from
fibrewise data alone.

The nontrivial genus-one test family now has an explicit transition cocycle.
For a local holomorphic parameter map `F`,
`complexTorusLocalHolomorphicParameterDeckHomeomorph` acts on the ambient
coordinate plane by
`(c,z) ↦ (c,z + m + n * F.map c)`.  Lean proves the unit, additive-composition,
and inverse laws, packages them as
`complexTorusLocalHolomorphicParameterDeckAddAction`, and proves that the
action leaves the pulled-back quotient total-space point unchanged.  Thus the
parameterized chart sheets are not merely individually holomorphic: their
integer shifts already carry the algebraic cocycle needed for double and
triple-overlap descent.  The remaining boundary is no longer the quotient
construction itself, but a reusable compact-fibre interface.  The current
`LocalJointlyHolomorphicFamily` model intentionally uses a global model fibre
`ℂ`, so it cannot be applied to an entire compact torus fibre.

That compact-fibre gap now has a concrete adapter. MathlibTorusCech.lean uses
the radius-1/4 ambient parameter balls
complexTorusLocalHolomorphicParameterCechCover to cover the local parameter
base, then constructs complexTorusLocalHolomorphicParameterCechData, its
jointly holomorphic transition data, and the descended marked atlas
complexTorusLocalHolomorphicParameterCechDescendedMarkedAtlas. On overlaps
the fibre transition is the identity on the common quotient torus; the
nontrivial analytic transition remains visible in the unquotiented local
surface charts through the deck action above. Thus the adapter does not
pretend that a compact torus is globally a copy of the complex plane, while
still placing the explicit genus-one family inside the existing Cech
quotient/atlas machinery.

The concrete compact-fibre replacement is now explicit in
`ComplexTorusLocalJointlyHolomorphicLiftWitness`. It records the local
two-dimensional quotient charts, their parameter-coordinate identity, the
jointly holomorphic lift coordinate, the parameter-dependent deck
homeomorphisms, their `DifferentiableOn` transition-sheet certificates, the
additive cocycle, and invariance after passage to the quotient. This is a
genuine joint-variation certificate for the genus-one lifted family, while
remaining local in the fibre direction and therefore avoiding a false global
`ℂ`-trivialization.

The reusable compact-fibre interface is now explicit as
CompactFiberHolomorphicCechDescentData. It extends ordinary
HolomorphicCechDescentData with a compact_fiber field for every actual local
fibre and its stored topology. The theorem
complexTorusLocalHolomorphicParameterGlobalFamily_fiber_compact instantiates
this field for the varying genus-one family, and
complexTorusLocalHolomorphicParameterCompactCechData packages the complete
parameter-ball cover as compact Cech data. The companion theorem
complexTorusLocalHolomorphicParameterGlobalFamily_fiber_no_global_plane
proves that no local fibre can be globally homeomorphic to the plane. This
formalizes both sides of the design choice: compactness is retained as data,
while the impossible global-plane shortcut is ruled out.

The next descent step is now an explicit witness rather than an untyped
compactness claim. DescendedFiberCompactnessWitness records a chosen cover
index, its base-membership proof, and an actual Homeomorph from that local
fibre to the descended fibre. Its compactSpace_of_local theorem combines
this homeomorphism with CompactFiberHolomorphicCechDescentData.compact_fiber
and constructs CompactSpace for DescendedFiber. The concrete genus-one
construction now supplies this witness for every parameter-ball fibre and,
by centering a ball at any base point, for every descended fibre.

The quotient restriction itself is now proved at the correct intermediate
level. CechLocalFiberSlice is the fibre of one local total space equipped with
the induced subspace topology. Under the existing open-gluing hypothesis,
cechLocalFiberSliceHomeomorph gives an actual Homeomorph from this slice to
the descended fibre: injectivity comes from the local open embedding, while
surjectivity explicitly changes representatives across a Cech overlap. The
concrete varying-torus layer now closes the remaining comparison as well:
complexTorusTotalMkFiberSlice_isQuotientMap proves the fixed-parameter quotient
map, complexTorusTotalFiberSliceHomeomorph identifies its slice with the
quotient torus, and canonicalPullbackFiberSliceHomeomorph transports this
comparison through a pullback. Pullback associativity then yields
complexTorusCechLocalFiberSliceHomeomorph for the parameter-ball restriction;
complexTorusCechLocalFiberTopologyComparison identifies the stored fibre
topology with the slice topology. The descended compactness witness and
CompactSpace instance are consequently constructed for every base point of
the explicit genus-one Cech family. The new
complexTorusFiberSliceTotalHomeomorph assembles all fixed-parameter slice
maps into one parameter-preserving continuous total-space homeomorphism, and
complexTorusLocalFiberSliceTotalHomeomorph gives the corresponding pullback
family over an analytic test base. Its map back to the original quotient total
space is continuous. This is a genuine uniform topological family. The
concrete lifted family now also has an explicit joint holomorphic/deck
certificate; what remains is to connect that certificate to the generic Čech
local-chart comparison and descended holomorphic-transition interfaces, and
to formulate the corresponding reusable theory for arbitrary compact
complex fibres.

That connection has now been made at the family/Čech boundary. The witness
constructs an actual `ComplexSurfaceAtlas` and a parameter-compatible
`ComplexSurfaceFamilyAtlas`, then packages them as
`ComplexTorusLocalJointlyHolomorphicLiftWitness.toGlobalFamily`. The companion
`toCechData`, `toCechTransition`, `toCechOpenGluing`, and
`toCechDescendedAtlas` definitions feed this concrete family into the generic
multi-patch restriction, overlap, open-gluing, and descended-holomorphic-atlas
constructors. Thus the specialized certificate is no longer merely parallel
to the generic Čech layer. The named genus-one Cech data, transition, and
descended atlas are now identified with these outputs by explicit Lean
equalities. The remaining gap is no longer the existence of a quotient-overlap
comparison. The next pointwise deck-sheet comparison is now proved for the
genus-one model; the remaining abstraction target is to formulate the same
lift-to-Čech comparison for arbitrary compact complex fibres.

The next audit shows why this cannot be done by a direct coercion. The
predecessor of `CechLocalChartComparisonWitness`, namely
`CechJointlyHolomorphicVariationWitness`, requires a global homeomorphism
`ℂ ≃ₜ fibre` on every local patch. For every nonempty local torus parameter
map, `complexTorusLocalCechVariation_no_global_plane_model` proves that such a
witness would contradict compactness of the torus. The identity test family
has the corresponding explicit corollary. This is now a checked type-level
boundary, not merely an informal warning: the correct next interface must
compare lifted compact-fibre charts and deck descent without introducing a
global plane model.

The first replacement bridge is now bundled as
`ComplexTorusCompactFiberCechLiftBridge`. It carries the concrete lift/deck
witness together with an explicit lift-sheet witness, a pointwise
`ComplexTorusCompactFiberCechLiftCoordinateWitness`, and overlap-atlas witness, the common-mother
Čech atlas, the joint holomorphic transition, and the descended holomorphic
atlas. The overlap witness proves that the actual target overlap atlas is the
transport of the actual source overlap atlas, that both atlas transition maps
are `DifferentiableOn`, and that the restricted source/target chart values
agree on every common parameter point. The generic
`multiPatchOverlapSourceChart_apply_val_eq_global` and
`multiPatchOverlapTargetChart_apply_val_eq_global` theorems now identify each
quotient-overlap chart value with the corresponding global family chart after
the canonical pullback subtype homeomorphism; the torus specializations
`complexTorusLocalCechOverlapAtlas_source_chart_eq_lift_chart` and
`..._target_chart_eq_lift_chart` land in the actual lifted surface charts.
Thus the source/target atlases are now real quotient-overlap constructions,
and their coordinate values have a formal lift-side comparison. The new
`complexTorusLocalHolomorphicParameterSurfaceChart_transition_eq_deck_at`
selects a concrete `(ℤ × ℤ)` sheet at each common lifted chart point, while
`complexTorusLocalCechOverlapAtlas_transition_eq_deck_at` transports that
choice back to the actual quotient overlap charts. The bundled
`ComplexTorusCompactFiberCechDeckComparisonWitness` is now a field of
`ComplexTorusCompactFiberCechLiftBridge`. What remains is to remove the
explicit chart-domain hypotheses where possible. The generic
`ComplexSurfaceChartDeckTransitionCover.chart_transition_eq_deck_at` now
abstracts the lifted sheet selection, and
`CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_deck` packages
the coordinate-comparison step without mentioning the torus or a global
plane model; the torus Čech theorem now constructs and consumes this generic
interface. The generic cover now also has a noncomputable overlap selector,
`sheetSelector`, with `sheetSelector_eq_of_mem` under pairwise disjointness
and `eventually_sheetSelector_eq` when sheet sources are open. These two facts
are now packaged as `isLocallyConstant_sheetSelector`, and with the discrete
topology on the sheet index as `continuous_sheetSelector`. The torus
parameterized deck sheets satisfy the required pairwise-disjointness theorem
`complexTorusLocalHolomorphicParameterDeckOverlap_pairwise_disjoint`, so its
selector is locally constant and continuous. The generic
`selectedDeckMap` is the deck map selected by that branch;
`transitionMap_eq_selectedDeckMap` identifies it pointwise with the actual
chart transition on the overlap, and
`continuous_selectedDeckMap` /
`continuous_transitionMap_on_overlap` prove the resulting piecewise map is
continuous. The torus specialization now verifies these two continuity
statements for its parameter-dependent affine deck transformations, while the
Čech comparison can now use the named
`CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_selectedDeckMap`
interface directly. At the explicit formula level,
`ComplexTorusLocalHolomorphicParameterMap.deckTransition_continuousOn` and
`..._differentiableOn`, together with
`complexTorusLocalHolomorphicParameterDeckHomeomorph_continuousOn` and
`..._differentiableOn`, certify the joint dependence on the test parameter and
the lift coordinate before the map is restricted to a chosen chart overlap.
The remaining work is to supply analogous separation and chart systems for
arbitrary compact complex fibres.

The lift-sheet witness now stores the actual `ComplexSurfaceChartTransitionCover`, not only its derived
coverage and transition equalities. This makes the local lifted atlas a reusable object: the cover itself
records the sheet index, source/target inclusions, and differentiability certificate.

### Current Boundaries

**Proven at the current interface or selected-concrete level:**
- Marking compatibility relation is an equivalence relation
- Teichmüller space as quotient is well-defined
- SL₂(ℤ) determinant-one multiplication with associativity
- Upper half-plane fundamental domain representative theorem
- j-type weight-zero quotient function construction
- Exact multi-patch overlap atlas transport and a jointly holomorphic transition witness
- General multi-patch descended-overlap inclusion and coordinate compatibility
- General descended transition equality and holomorphic atlas witness from joint Čech holomorphicity
- Concrete multi-patch descended family atlas with continuous projection and verified base-coordinate charts
- Choice-independent descended marking witness and concrete marked descended total-space atlas
- Concrete compact-fibre Čech adapter for the genus-one parameter-ball family, including local compactness fields,
  quotient-fibre Homeomorphs, topology comparison, and descended `CompactSpace` at every base point
- Uniform topological assembly of the varying-torus fibre-slice Homeomorphs over the full parameter space and over
  a holomorphic test base, with a continuous map back to the original quotient total space
- Concrete genus-one joint lift/deck certificate with local two-dimensional charts, `DifferentiableOn` transition sheets,
  additive cocycle, and quotient invariance, without assuming a global `ℂ`-fibre trivialization
- Conversion of the concrete genus-one lift/deck witness into a genuine family atlas and global holomorphic marked family,
  followed by explicit entry points into generic multi-patch Čech gluing and descended holomorphic-atlas construction
- Explicit equality of the concrete witness outputs with the named genus-one global family, Čech data, joint transition,
  and descended holomorphic atlas
- Formal nonexistence of the global-plane `CechJointlyHolomorphicVariationWitness` for every nonempty local torus
  parameter map, including the identity-family corollary
- `ComplexTorusCompactFiberCechLiftBridge`, bundling the lifted/deck certificate with the common-mother Čech atlas,
  joint holomorphic transition, descended holomorphic atlas, and explicit source/target overlap-atlas witness without
  a global plane model
- Torus-specialized source/target overlap-atlas transport, holomorphic transition differentiability, and local chart
  coordinate agreement, all obtained from the actual multi-patch quotient construction
- Generic and torus-specialized pointwise source/target overlap-chart equalities after canonical pullback transport,
  bundled as `ComplexTorusCompactFiberCechLiftCoordinateWitness`
- Pointwise selection of a concrete `(ℤ × ℤ)` deck sheet and identification of the quotient-overlap target coordinate
  with the corresponding deck homeomorphism of the source coordinate, bundled as
  `ComplexTorusCompactFiberCechDeckComparisonWitness` and included in `ComplexTorusCompactFiberCechLiftBridge`
- Generic deck-transition-cover sheet selection and the compact-fibre
  lift-to-Čech coordinate-comparison interface, via
  `ComplexSurfaceChartDeckTransitionCover.chart_transition_eq_deck_at` and
  `CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_deck`
- Generic overlap `sheetSelector`, uniqueness under pairwise disjoint sheet
 sources, local constancy for open sheet sources, and continuity into a
 discrete sheet index; the selected deck map is continuous and agrees with
 the actual overlap transition, and the torus deck cover now proves the
 corresponding parameter-dependent statements
- Generic chart-transition cocycle on successive overlaps via
  `ComplexSurfaceChart.transitionMap_comp_on_overlap`, and its selected-deck
  refinement via `ComplexSurfaceChartDeckTransitionCover.selectedDeckMap_comp_on_overlap`;
  the torus parameterized deck cover instantiates the same triple-overlap law
- The Čech cocycle is now lifted to actual dependent-sum overlap points via
  `HolomorphicCechDescentData.overlapTransitionMap_comp_apply`; jointly
  continuous (hence jointly holomorphic) transitions inherit the same law through
  `JointlyContinuousTransitionData.toFun_comp_apply`, with a torus-specific
  theorem `complexTorusLocalHolomorphicParameterCechTransition_comp_apply`
- Successive chart-overlap hypotheses now also produce the direct source/target
  overlap via `ComplexSurfaceChart.overlap_mem_of_transitionMap_mem`; the
  quotient atlas packages this membership together with its coordinate cocycle in
  `descendedChart_overlap_comp_on_overlap`; the chart-family form is exposed by
  `descendedChartFamily_overlap_comp_on_overlap`
- `DescendedTransitionCompatibility.joint_transitionMap_comp_on_overlap` transports
  the descended chart cocycle back to the source/target Čech coordinate transitions,
  closing the coordinate-level loop between quotient charts and local analytic data
- Explicit lift-side chart-overlap coverage by `(ℤ × ℤ)` deck sheets and equality of each local chart transition
  with its deck homeomorphism on the corresponding sheet
- The actual `ComplexSurfaceChartTransitionCover` stored in the lift-sheet witness, including its sheet index and
  differentiability/coverage fields
- Generic fixed-parameter fibre slice witness, its induced one-dimensional complex atlas, and the resulting marked fibre surface
- Conditional assembly of uniformly marked fibre slices into a ComplexSurfaceFamily.Family, given an explicit total-space homeomorphism and projection compatibility
- Universe-polymorphic transport of the total-space atlas to the dependent-sum carrier
- Conditional global holomorphic marked family from the transported atlas when the source cover is universal
- Named Čech-quotient-to-family bridge with actual `toFamily` and `toGlobal` constructors, conditional on uniform slice/comparison data
- `DescendedGlobalUniversalPropertyWitness` binds a descended global family to the
  genuine classification quantifiers; `toGlobalFineHolomorphicUniversalMarkedFamily`,
  `classify`, and `classify_map_unique` expose the resulting universal-property target
  without asserting that such a witness exists automatically
- `ComplexTorusLocalRestrictedFineHolomorphicUniversalMarkedFamily` quantifies the
  concrete genus-one classification over all local holomorphic parameter maps at once,
  while retaining the explicit parameter-point equation and map uniqueness
- `ComplexTorusGlobalMarkedSurfaceFamilyWitness` now records the additional global atlas
  required to promote the concrete marked torus family to the global-atlas interface.
  This is intentionally a conditional witness: the quotient atlas currently covers only
  the proved local parameter neighbourhood, so the code does not silently claim a global
  upper-half-plane atlas.
- `complexTorusLocalHolomorphicParameterGlobalClassification` is parameterized by that
  witness and supplies a genuine global classification object for each explicit local torus
  test family.  Its map is still proved to be the concrete `parameterPoint`.
- `ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness` upgrades this
  conditional global classifier with the ambient `DifferentiableOn` certificate for its
  classifying map.  The canonical witness uses the actual holomorphic test map, and its
  `precompose` constructor proves the chain-rule stability under base change.
- The ambient analytic certificates also satisfy one-step and two-step composition laws,
  including comparison with precomposition by `G.compose H`; this records analytic
  functoriality without pretending that the subtype-valued upper-half-plane base is a
  complex vector space.
- `HolomorphicFiberwiseEquiv.pullback` now gives the generic fibrewise base-change
  operation, and `pullback_pullback_map` verifies its iterated classifying map.  The
  `HolomorphicFiberwiseEquiv.canonicalPullback_comp` upgrades the direct/iterated
  comparison to a marked fibrewise biholomorphism.  `pullbackDirect` packages the
  one-stage classifier used by the global interface; the iterated and direct dependent
  sums remain only canonically homeomorphic, not definitionally equal.
- `ComplexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily` quantifies these
  ambient analytic classification witnesses over the whole restricted test category,
  retaining parameter-point uniqueness and exposing the precomposition law at the
  universal-object level.
- `ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.ofGlobalFine`
  gives the constructive specialization from the generic global fine-moduli interface
  to the explicit torus test category.  No converse is claimed: extending a restricted
  torus classifier to arbitrary global analytic families remains a genuine universal-family
  problem.
- `ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily` packages the
  preceding conditional witnesses over the same restricted test class and records its
  Čech-compatible parameter-point theorem; this remains restricted and does not instantiate
  the generic descended universal-property quantifier over arbitrary global families.
- The same layer now proves classification-map composition and iterated composition under
  holomorphic base change, constructs explicit direct/transported global pullback witnesses,
  and feeds them into `GlobalHolomorphicFamilyClassification.pullbackWithWitness`.  The
  auxiliary `ComplexSurfaceFamilyAtlas.cast_*` lemmas make the dependent Family transports
  explicit at the cover, topology, and projection fields.
- Fixed-parameter slice of a jointly holomorphic family, including its chart-coordinate equality and differentiability theorem
- Arbitrary complex-normed-base joint variation, local base-chart coordinates, and a same-universe Čech local-variation adapter
- Open-base restriction of a jointly holomorphic family, including the identity and original-base open-subset chart constructors
- A selected-concrete local total-space Homeomorph and full local `ComplexSurfaceChart`/atlas witness for the translated-plane family
- Fibre-coordinate transport across the local-family equality, plus a Čech fibre-transition coordinate with a genuine joint differentiability certificate and target-chart comparison theorem
- Čech overlap insertion into the selected local chart domain as open embeddings, transported local overlap atlases, and an explicit chartwise `HolomorphicEquiv` comparison interface
- Identity holomorphicity for transported surface atlases, normalization of comparison witnesses from explicit atlas equalities, and conditional assembly of a local-chart holomorphic transition into `JointlyHolomorphicTransitionData`
- Coordinate-level local Čech transition witnesses, their automatic conversion to forward/inverse `HolomorphicEquiv`, and an adapter from existing jointly holomorphic Čech data
- The nontrivial upper-half-plane torus family’s parameterized deck action, including unit, composition, inverse, and quotient-invariance laws for the local transition sheets
- Two-universe `ComplexSurfaceAtlas.HolomorphicMap`/`HolomorphicEquiv` interfaces, with verified high-universe forward and inverse transport certificates via `transport_univ_holomorphicMap` and `transport_univ_holomorphicEquiv`
- Self-transition holomorphicity and descended atlas holomorphicity for the
  subsingleton-index base case

These items do not by themselves constitute a formalization of the standard
Teichmüller space, the measurable Riemann mapping theorem, the moduli functor,
or the existence of a universal family.

**In Progress:**
- Measurable Riemann mapping theorem (Beltrami equation existence/uniqueness)
- Fully universe-polymorphic fibre-transition data and its direct assembly into the descended total-space holomorphic transition witness
- Construction of concrete nontrivial instances of `CechLocalChartComparisonWitness` from local analytic chart data
- Concrete chart systems for arbitrary compact complex fibres, including
  separation/local-continuity input needed to instantiate the generic
  selected-sheet interface beyond the torus test family
- Joint holomorphic variation of the assembled fibre-slice comparisons and a reusable general compact-fibre Čech interface
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
