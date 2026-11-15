import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Teichmuller.MathlibFamily

namespace Teichmuller
namespace MathlibFormal

universe u w

namespace ComplexSurfaceFamily

/-!
This file connects the concrete family interface to Mathlib's standard notion of
a locally trivial bundle.  The older `Family.analyticVariation : Prop` is kept
as a compatibility boundary; `FiberBundleWitness` is the first data-carrying
replacement for that placeholder.
-/

/--
A concrete locally-trivial topological witness for a family of marked complex
surfaces.  The model fibre is only topological here.  The complex/holomorphic
strengthening is deliberately a later layer, expressed chart by chart.
-/
structure FiberBundleWitness {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) where
  model : Type u
  modelTopology : TopologicalSpace model
  modelNonempty : Nonempty model
  modelHomeomorph : ∀ b,
    @Homeomorph model (F.fiber b).carrier
      modelTopology (F.fiber b).topology
  bundleTopology :
    TopologicalSpace
      (Bundle.TotalSpace model (fun b => (F.fiber b).carrier))
  totalSpaceHomeomorph :
    @Homeomorph
      (Sigma fun b => (F.fiber b).carrier)
      (Bundle.TotalSpace model (fun b => (F.fiber b).carrier))
      F.totalTopology bundleTopology
  bundle : @FiberBundle B model inferInstance modelTopology
    (fun b => (F.fiber b).carrier)
    bundleTopology
    (fun b => (F.fiber b).topology)

/-- A topological bundle witness upgraded by chartwise biholomorphic
identifications of every fibre with the model surface. -/
structure HolomorphicFiberBundleWitness {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) where
  topology : FiberBundleWitness F
  modelSurface :
    @ComplexRiemannSurface topology.model topology.modelTopology
  fiberHolomorphic : ∀ b,
    letI : TopologicalSpace topology.model := topology.modelTopology
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    @AtlasHolomorphicEquiv
      topology.model (F.fiber b).carrier
      topology.modelTopology (F.fiber b).topology
      modelSurface.atlas (F.fiber b).surface.atlas
      (topology.modelHomeomorph b)

/-- A family carrying the concrete locally-trivial and chartwise holomorphic
variation data, without asking the legacy `analyticVariation : Prop` field to
encode that data. -/
structure AnalyticFamily (S : Type u) (B : Type w)
    [TopologicalSpace S] [TopologicalSpace B] where
  family : Family S B
  variation : HolomorphicFiberBundleWitness family

/-! ### Joint holomorphicity in a chosen trivializing coordinate -/

/--
The first data-carrying refinement of `Family.analyticVariation` in the base
direction.  We restrict to a complex base and a common complex model fibre,
then record a chosen fibre coordinate and a chosen atlas chart in each fibre.
The resulting coordinate function on `ℂ × ℂ` must be genuinely Mathlib-
differentiable.  This is deliberately weaker than a full complex manifold
definition for the total space, but it prevents the phrase “analytic family”
from meaning only “each fibre is analytic in isolation”.
-/
structure JointlyHolomorphicFamily (S : Type u)
    [TopologicalSpace S]
    (F : AnalyticFamily S ℂ) where
  fiberEquiv : ∀ a,
    @Homeomorph ℂ (F.family.fiber a).carrier
      inferInstance (F.family.fiber a).topology
  chartIndex : ∀ a,
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    (F.family.fiber a).surface.atlas.index
  jointCoordinate : ℂ × ℂ → ℂ
  jointCoordinate_eq_chart : ∀ (a z : ℂ),
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    jointCoordinate (a, z) =
      ((F.family.fiber a).surface.atlas.chart (chartIndex a)).toComplex
        (fiberEquiv a z)
  jointlyHolomorphic : Differentiable ℂ jointCoordinate

/-! The joint coordinate really contains the fibrewise holomorphic
information.  We expose the constant-parameter restriction explicitly rather
than leaving this implication at the level of informal commentary. -/

def JointlyHolomorphicFamily.sliceCoordinate
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F) (a : ℂ) : ℂ → ℂ :=
  fun z => J.jointCoordinate (a, z)

@[simp] theorem JointlyHolomorphicFamily.sliceCoordinate_eq_chart
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F) (a z : ℂ) :
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    J.sliceCoordinate a z =
      ((F.family.fiber a).surface.atlas.chart (J.chartIndex a)).toComplex
        (J.fiberEquiv a z) := by
  letI : TopologicalSpace (F.family.fiber a).carrier :=
    (F.family.fiber a).topology
  exact J.jointCoordinate_eq_chart a z

theorem JointlyHolomorphicFamily.slice_differentiable
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F) (a : ℂ) :
    Differentiable ℂ (J.sliceCoordinate a) := by
  have hparameter : Differentiable ℂ (fun z : ℂ => (a, z)) := by
    exact (differentiable_const _).prodMk differentiable_id
  change Differentiable ℂ (fun z : ℂ => J.jointCoordinate (a, z))
  exact J.jointlyHolomorphic.fun_comp hparameter

/-! ### Joint variation over an arbitrary complex normed base

The preceding structure is the smallest useful compatibility model over
the complex numbers.  The same implication is independent of that
one-dimensional choice, so we expose it for any complex normed base.  This is
the interface that can later be applied after choosing a local complex
coordinate on a general parameter space. -/

structure JointlyHolomorphicFamilyOver (S : Type u) {B : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (F : AnalyticFamily S B) where
  fiberEquiv : ∀ a,
    @Homeomorph ℂ (F.family.fiber a).carrier
      inferInstance (F.family.fiber a).topology
  chartIndex : ∀ a,
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    (F.family.fiber a).surface.atlas.index
  jointCoordinate : B × ℂ → ℂ
  jointCoordinate_eq_chart : ∀ (a : B) (z : ℂ),
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    jointCoordinate (a, z) =
      ((F.family.fiber a).surface.atlas.chart (chartIndex a)).toComplex
        (fiberEquiv a z)
  jointlyHolomorphic : Differentiable ℂ jointCoordinate

def JointlyHolomorphicFamilyOver.sliceCoordinate
    {S : Type u} {B : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {F : AnalyticFamily S B}
    (J : JointlyHolomorphicFamilyOver S F) (a : B) : ℂ → ℂ :=
  fun z => J.jointCoordinate (a, z)

@[simp] theorem JointlyHolomorphicFamilyOver.sliceCoordinate_eq_chart
    {S : Type u} {B : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {F : AnalyticFamily S B}
    (J : JointlyHolomorphicFamilyOver S F) (a : B) (z : ℂ) :
    letI : TopologicalSpace (F.family.fiber a).carrier :=
      (F.family.fiber a).topology
    J.sliceCoordinate a z =
      ((F.family.fiber a).surface.atlas.chart (J.chartIndex a)).toComplex
        (J.fiberEquiv a z) := by
  letI : TopologicalSpace (F.family.fiber a).carrier :=
    (F.family.fiber a).topology
  exact J.jointCoordinate_eq_chart a z

theorem JointlyHolomorphicFamilyOver.slice_differentiable
    {S : Type u} {B : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {F : AnalyticFamily S B}
    (J : JointlyHolomorphicFamilyOver S F) (a : B) :
    Differentiable ℂ (J.sliceCoordinate a) := by
  have hparameter : Differentiable ℂ (fun z : ℂ => (a, z)) := by
    exact (differentiable_const _).prodMk differentiable_id
  change Differentiable ℂ (fun z : ℂ => J.jointCoordinate (a, z))
  exact J.jointlyHolomorphic.fun_comp hparameter

def JointlyHolomorphicFamily.toOver
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F) :
    JointlyHolomorphicFamilyOver S F :=
  { fiberEquiv := J.fiberEquiv
    chartIndex := J.chartIndex
    jointCoordinate := J.jointCoordinate
    jointCoordinate_eq_chart := J.jointCoordinate_eq_chart
    jointlyHolomorphic := J.jointlyHolomorphic }

/-! ### Local complex coordinates on a topological parameter space -/

structure ComplexBaseChart (B : Type w) [TopologicalSpace B] where
  domain : Set B
  domain_open : IsOpen domain
  range : Set ℂ
  range_open : IsOpen range
  chart : {b : B // b ∈ domain} ≃ₜ {z : ℂ // z ∈ range}

/-! The identity coordinate on an open subset of the complex line is the first
concrete base-chart constructor.  It is useful when a local family is obtained
by restricting a family already parametrized by `ℂ`: no extra choice of a
coordinate homeomorphism is needed, and the Lean subtype carries the open-set
topology automatically. -/

noncomputable def ComplexBaseChart.idOnOpen
    (U : Set ℂ) (hU : IsOpen U) : ComplexBaseChart U where
  domain := Set.univ
  domain_open := isOpen_univ
  range := U
  range_open := hU
  chart := @Homeomorph.Set.univ U inferInstance

/-! The same open set can also be used as a chart domain inside the original
complex base.  This variant is convenient when the local total space is the
subspace of a pre-existing family total space. -/

noncomputable def ComplexBaseChart.openSubset
    (U : Set ℂ) (hU : IsOpen U) : ComplexBaseChart ℂ where
  domain := U
  domain_open := hU
  range := U
  range_open := hU
  chart := @Homeomorph.refl {z : ℂ // z ∈ U} inferInstance

noncomputable def ComplexBaseChart.coordinate
    {B : Type w} [TopologicalSpace B]
    (C : ComplexBaseChart B) (b : B) (hb : b ∈ C.domain) : ℂ :=
  C.chart ⟨b, hb⟩

@[simp] theorem ComplexBaseChart.idOnOpen_coordinate
    {U : Set ℂ} (hU : IsOpen U) (b : U)
    (hb : b ∈ (ComplexBaseChart.idOnOpen U hU).domain) :
    (ComplexBaseChart.idOnOpen U hU).coordinate b hb = (b : ℂ) := by
  rfl

@[simp] theorem ComplexBaseChart.openSubset_coordinate
    {U : Set ℂ} (hU : IsOpen U) (b : ℂ) (hb : b ∈ U) :
    (ComplexBaseChart.openSubset U hU).coordinate b hb = b := by
  rfl

noncomputable def ComplexBaseChart.coordinateOn
    {B : Type w} [TopologicalSpace B]
    (C : ComplexBaseChart B) :
    {b : B // b ∈ C.domain} → ℂ :=
  fun b => C.chart b

@[simp] theorem ComplexBaseChart.coordinateOn_apply
    {B : Type w} [TopologicalSpace B]
    (C : ComplexBaseChart B) (b : B) (hb : b ∈ C.domain) :
    C.coordinateOn ⟨b, hb⟩ = C.coordinate b hb := by
  rfl

theorem ComplexBaseChart.continuous_coordinateOn
    {B : Type w} [TopologicalSpace B]
    (C : ComplexBaseChart B) :
    Continuous C.coordinateOn := by
  exact continuous_subtype_val.comp C.chart.continuous

structure LocalJointlyHolomorphicFamily (S : Type u) {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (C : ComplexBaseChart B) where
  fiberEquiv : ∀ (b : B) (hb : b ∈ C.domain),
    @Homeomorph ℂ (F.fiber b).carrier
      inferInstance (F.fiber b).topology
  chartIndex : ∀ (b : B) (hb : b ∈ C.domain),
    letI : TopologicalSpace (F.fiber b).carrier :=
      (F.fiber b).topology
    (F.fiber b).surface.atlas.index
  jointCoordinate : ℂ × ℂ → ℂ
  jointCoordinate_eq_chart : ∀ (b : B) (hb : b ∈ C.domain) (z : ℂ),
    letI : TopologicalSpace (F.fiber b).carrier :=
      (F.fiber b).topology
    jointCoordinate (C.coordinate b hb, z) =
      ((F.fiber b).surface.atlas.chart
        (chartIndex b hb)).toComplex (fiberEquiv b hb z)
  jointlyHolomorphic : Differentiable ℂ jointCoordinate

noncomputable def LocalJointlyHolomorphicFamily.sliceCoordinate
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    (J : LocalJointlyHolomorphicFamily S F C)
    (b : B) (hb : b ∈ C.domain) : ℂ → ℂ :=
  fun z => J.jointCoordinate (C.coordinate b hb, z)

@[simp] theorem LocalJointlyHolomorphicFamily.sliceCoordinate_eq_chart
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    (J : LocalJointlyHolomorphicFamily S F C)
    (b : B) (hb : b ∈ C.domain) (z : ℂ) :
    letI : TopologicalSpace (F.fiber b).carrier :=
      (F.fiber b).topology
    J.sliceCoordinate b hb z =
      ((F.fiber b).surface.atlas.chart
        (J.chartIndex b hb)).toComplex (J.fiberEquiv b hb z) := by
  letI : TopologicalSpace (F.fiber b).carrier :=
    (F.fiber b).topology
  exact J.jointCoordinate_eq_chart b hb z

theorem LocalJointlyHolomorphicFamily.slice_differentiable
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    (J : LocalJointlyHolomorphicFamily S F C)
    (b : B) (hb : b ∈ C.domain) :
    Differentiable ℂ (J.sliceCoordinate b hb) := by
  have hparameter :
      Differentiable ℂ (fun z : ℂ => (C.coordinate b hb, z)) := by
    exact (differentiable_const _).prodMk differentiable_id
  change Differentiable ℂ
    (fun z : ℂ => J.jointCoordinate (C.coordinate b hb, z))
  exact J.jointlyHolomorphic.fun_comp hparameter

/-! Restriction to an open subset of the complex base is now a genuine
local-family construction.  The pullback family keeps the original fibre
surface and the identity base chart supplies the missing local coordinate. -/

noncomputable def JointlyHolomorphicFamily.restrictToOpen
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F)
    (U : Set ℂ) (hU : IsOpen U) :
    LocalJointlyHolomorphicFamily S
      (canonicalPullback F.family
        (fun b : U => (b : ℂ)) continuous_subtype_val)
      (ComplexBaseChart.idOnOpen U hU) where
  fiberEquiv := fun b _ => J.fiberEquiv (b : ℂ)
  chartIndex := fun b _ => J.chartIndex (b : ℂ)
  jointCoordinate := J.jointCoordinate
  jointCoordinate_eq_chart := by
    intro b hb z
    letI : TopologicalSpace
        ((canonicalPullback F.family
          (fun b : U => (b : ℂ)) continuous_subtype_val).fiber b).carrier :=
      ((canonicalPullback F.family
        (fun b : U => (b : ℂ)) continuous_subtype_val).fiber b).topology
    letI : TopologicalSpace (F.family.fiber (b : ℂ)).carrier :=
      (F.family.fiber (b : ℂ)).topology
    change J.jointCoordinate ((b : ℂ), z) =
      ((F.family.fiber (b : ℂ)).surface.atlas.chart
        (J.chartIndex (b : ℂ))).toComplex
        (J.fiberEquiv (b : ℂ) z)
    exact J.jointCoordinate_eq_chart (b : ℂ) z
  jointlyHolomorphic := J.jointlyHolomorphic

noncomputable def JointlyHolomorphicFamily.restrictToBaseOpen
    {S : Type u} [TopologicalSpace S]
    {F : AnalyticFamily S ℂ}
    (J : JointlyHolomorphicFamily S F)
    (U : Set ℂ) (hU : IsOpen U) :
    LocalJointlyHolomorphicFamily S F.family
      (ComplexBaseChart.openSubset U hU) where
  fiberEquiv := fun b _ => J.fiberEquiv b
  chartIndex := fun b _ => J.chartIndex b
  jointCoordinate := J.jointCoordinate
  jointCoordinate_eq_chart := by
    intro b hb z
    letI : TopologicalSpace (F.family.fiber b).carrier :=
      (F.family.fiber b).topology
    change J.jointCoordinate (b, z) =
      ((F.family.fiber b).surface.atlas.chart
        (J.chartIndex b)).toComplex (J.fiberEquiv b z)
    exact J.jointCoordinate_eq_chart b z
  jointlyHolomorphic := J.jointlyHolomorphic

/-! ### From a joint coordinate to an actual local total-space chart

`LocalJointlyHolomorphicFamily` deliberately stops at a differentiable
coordinate function.  The next layer records the extra topological data that
is needed before that function can be called a chart: a trivialization of the
dependent total space over the base-chart domain, an open coordinate range,
and a homeomorphism onto that range.  Nothing about a varying family is
silently inferred from fibrewise homeomorphisms. -/

abbrev BaseChartDomain {B : Type w} [TopologicalSpace B]
    (C : ComplexBaseChart B) := {b : B // b ∈ C.domain}

abbrev LocalBaseTotal {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (C : ComplexBaseChart B) :=
  Sigma fun b : BaseChartDomain C => (F.fiber b.1).carrier

def localBaseTotalMap {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (C : ComplexBaseChart B) :
    LocalBaseTotal F C → Sigma fun b : B => (F.fiber b).carrier :=
  fun z => ⟨z.1.1, z.2⟩

def localBaseTotalTopology {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (C : ComplexBaseChart B) :
    TopologicalSpace (LocalBaseTotal F C) :=
  TopologicalSpace.induced (localBaseTotalMap F C) F.totalTopology

noncomputable def LocalJointlyHolomorphicFamily.jointCoordinateMap
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    (J : LocalJointlyHolomorphicFamily S F C) :
    BaseChartDomain C × ℂ → ℂ × ℂ :=
  fun p =>
    (C.coordinateOn p.1,
      J.jointCoordinate (C.coordinateOn p.1, p.2))

structure LocalJointlyHolomorphicChartWitness
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    (J : LocalJointlyHolomorphicFamily S F C) where
  localTrivialization :
    @Homeomorph
      (BaseChartDomain C × ℂ)
      (LocalBaseTotal F C)
      inferInstance
      (localBaseTotalTopology F C)
  localTrivialization_apply : ∀ p,
    localTrivialization p =
      ⟨p.1,
        J.fiberEquiv p.1.1 p.1.2 p.2⟩
  range : Set (ℂ × ℂ)
  range_open : IsOpen range
  jointChart :
    @Homeomorph
      (BaseChartDomain C × ℂ)
      {z : ℂ × ℂ // z ∈ range}
      inferInstance
      inferInstance
  jointChart_apply : ∀ p,
    (jointChart p).1 = J.jointCoordinateMap p

noncomputable def LocalJointlyHolomorphicChartWitness.domainHomeomorph
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    {J : LocalJointlyHolomorphicFamily S F C}
    (W : LocalJointlyHolomorphicChartWitness J) :
    @Homeomorph
      {x : LocalBaseTotal F C // x ∈ (Set.univ : Set (LocalBaseTotal F C))}
      (BaseChartDomain C × ℂ)
      (TopologicalSpace.induced Subtype.val
        (localBaseTotalTopology F C))
      inferInstance := by
  letI : TopologicalSpace (LocalBaseTotal F C) :=
    localBaseTotalTopology F C
  refine
    { toFun := fun x => W.localTrivialization.symm x.1
      invFun := fun p => ⟨W.localTrivialization p, by trivial⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro p
        simp
      continuous_toFun := by
        exact W.localTrivialization.continuous_invFun.comp
          continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact W.localTrivialization.continuous_toFun }

noncomputable def LocalJointlyHolomorphicChartWitness.toComplexSurfaceChart
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    {J : LocalJointlyHolomorphicFamily S F C}
    (W : LocalJointlyHolomorphicChartWitness J) :
    @ComplexSurfaceChart (LocalBaseTotal F C)
      (localBaseTotalTopology F C) := by
  letI : TopologicalSpace (LocalBaseTotal F C) :=
    localBaseTotalTopology F C
  exact
    { domain := Set.univ
      range := W.range
      domain_open := isOpen_univ
      range_open := W.range_open
      chart := W.domainHomeomorph.trans W.jointChart }

theorem LocalJointlyHolomorphicChartWitness.chart_apply_jointCoordinateMap
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    {J : LocalJointlyHolomorphicFamily S F C}
    (W : LocalJointlyHolomorphicChartWitness J)
    (p : BaseChartDomain C × ℂ) :
    (W.toComplexSurfaceChart.chart
      ⟨W.localTrivialization p, by trivial⟩).1 =
      J.jointCoordinateMap p := by
  letI : TopologicalSpace (LocalBaseTotal F C) :=
    localBaseTotalTopology F C
  change
    (W.jointChart
      (W.domainHomeomorph
        ⟨W.localTrivialization p, by trivial⟩)).1 =
      J.jointCoordinateMap p
  have hdomain : W.domainHomeomorph
      ⟨W.localTrivialization p, by trivial⟩ = p := by
    change W.localTrivialization.symm (W.localTrivialization p) = p
    simp
  rw [hdomain]
  exact W.jointChart_apply p

noncomputable def LocalJointlyHolomorphicChartWitness.toComplexSurfaceAtlas
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} {C : ComplexBaseChart B}
    {J : LocalJointlyHolomorphicFamily S F C}
    (W : LocalJointlyHolomorphicChartWitness J) :
    ComplexSurfaceAtlas (LocalBaseTotal F C) := by
  letI : TopologicalSpace (LocalBaseTotal F C) :=
    localBaseTotalTopology F C
  refine
    { toComplexSurfaceChartFamily :=
        { topology := localBaseTotalTopology F C
          index := ULift Unit
          chart := fun _ => W.toComplexSurfaceChart
          coverSet := Set.univ
          covers := by
            intro x hx
            exact ⟨ULift.up (), by trivial⟩ }
      transition_differentiableOn := by
        intro _ _
        exact ComplexSurfaceChart.transitionMap_self_differentiableOn
          W.toComplexSurfaceChart }

/-! ### A first inhabited analytic family -/

/-- The underlying equivalence between a dependent-sum presentation of the
constant family and Mathlib's bundled total space. -/
def constantComplexPlaneTotalEquiv (B : Type w) [TopologicalSpace B] :
    (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) ≃
      Bundle.TotalSpace complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier) where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.proj, z.snd⟩
  left_inv := by
    intro z
    cases z
    rfl
  right_inv := by
    intro z
    cases z
    rfl

/-- Give the preceding equivalence its canonical homeomorphism structure when
the dependent-sum topology is induced from the trivial-bundle total space. -/
noncomputable def constantComplexPlaneTotalHomeomorph
    (B : Type w) [TopologicalSpace B] :
    @Homeomorph
      (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
      (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
      (TopologicalSpace.induced (constantComplexPlaneTotalEquiv B).toFun
        (@Bundle.Trivial.topologicalSpace B
          complexPlaneMarkedSurface.carrier inferInstance
          complexPlaneMarkedSurface.topology))
      (@Bundle.Trivial.topologicalSpace B
        complexPlaneMarkedSurface.carrier inferInstance
        complexPlaneMarkedSurface.topology) := by
  letI : TopologicalSpace
      (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) :=
    TopologicalSpace.induced (constantComplexPlaneTotalEquiv B).toFun
      (@Bundle.Trivial.topologicalSpace B
        complexPlaneMarkedSurface.carrier inferInstance
        complexPlaneMarkedSurface.topology)
  letI : TopologicalSpace
      (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier)) :=
    @Bundle.Trivial.topologicalSpace B
      complexPlaneMarkedSurface.carrier inferInstance
      complexPlaneMarkedSurface.topology
  exact (constantComplexPlaneTotalEquiv B).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The constant family whose fibre is the marked complex plane.  Its total
space uses Mathlib's product topology for the trivial bundle, rather than the
disjoint-union topology on a dependent sum. -/
noncomputable abbrev constantComplexPlaneFamily (B : Type w) [TopologicalSpace B] :
    Family ℂ B where
  fiber := fun _ => complexPlaneMarkedSurface
  totalTopology := TopologicalSpace.induced
    (constantComplexPlaneTotalEquiv B).toFun
    (@Bundle.Trivial.topologicalSpace B
      complexPlaneMarkedSurface.carrier inferInstance
      complexPlaneMarkedSurface.topology)
  projection_continuous := by
    letI : TopologicalSpace complexPlaneMarkedSurface.carrier :=
      complexPlaneMarkedSurface.topology
    letI : TopologicalSpace
        (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) :=
      TopologicalSpace.induced (constantComplexPlaneTotalEquiv B).toFun
        (@Bundle.Trivial.topologicalSpace B
          complexPlaneMarkedSurface.carrier inferInstance
          complexPlaneMarkedSurface.topology)
    letI : FiberBundle complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier) :=
      Bundle.Trivial.fiberBundle B complexPlaneMarkedSurface.carrier
    have hproj : @Continuous
        (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
          (Bundle.Trivial B complexPlaneMarkedSurface.carrier)) B
        (@Bundle.Trivial.topologicalSpace B
          complexPlaneMarkedSurface.carrier inferInstance
          complexPlaneMarkedSurface.topology)
        inferInstance Bundle.TotalSpace.proj :=
      FiberBundle.continuous_proj complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier)
    have hcomp := hproj.comp (continuous_induced_dom : @Continuous
      (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
      (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
        (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
      (TopologicalSpace.induced (constantComplexPlaneTotalEquiv B).toFun
        (@Bundle.Trivial.topologicalSpace B
          complexPlaneMarkedSurface.carrier inferInstance
          complexPlaneMarkedSurface.topology))
      (@Bundle.Trivial.topologicalSpace B
        complexPlaneMarkedSurface.carrier inferInstance
        complexPlaneMarkedSurface.topology)
      (constantComplexPlaneTotalEquiv B).toFun)
    simpa [constantComplexPlaneTotalEquiv, Function.comp_def] using hcomp
  analyticVariation := True

/-- The standard trivial-bundle witness for the constant complex-plane family. -/
noncomputable def constantComplexPlaneBundleWitness
    (B : Type w) [TopologicalSpace B] :
    FiberBundleWitness (constantComplexPlaneFamily B) where
  model := complexPlaneMarkedSurface.carrier
  modelTopology := complexPlaneMarkedSurface.topology
  modelNonempty := ⟨0⟩
  modelHomeomorph := fun _ => @Homeomorph.refl
    complexPlaneMarkedSurface.carrier complexPlaneMarkedSurface.topology
  bundleTopology := @Bundle.Trivial.topologicalSpace B
      complexPlaneMarkedSurface.carrier inferInstance complexPlaneMarkedSurface.topology
  totalSpaceHomeomorph := constantComplexPlaneTotalHomeomorph B
  bundle := by
    exact Bundle.Trivial.fiberBundle B complexPlaneMarkedSurface.carrier

/-- A fully populated holomorphic-family witness for the constant plane. -/
noncomputable def constantComplexPlaneAnalyticFamily
    (B : Type w) [TopologicalSpace B] :
    AnalyticFamily ℂ B where
  family := constantComplexPlaneFamily B
  variation :=
    { topology := constantComplexPlaneBundleWitness B
      modelSurface := complexPlaneMarkedSurface.surface
      fiberHolomorphic := by
        intro b
        letI : TopologicalSpace complexPlaneMarkedSurface.carrier :=
          complexPlaneMarkedSurface.topology
        exact AtlasHolomorphicEquiv.refl complexPlaneMarkedSurface.surface.atlas }

/-- A parameter-dependent family whose fibre at `a` uses the translated global
coordinate `z ↦ z - a`.  The underlying topological bundle is still trivial;
the variation is visible in the actual complex atlas. -/
noncomputable abbrev affinePlaneFamily : Family ℂ ℂ where
  fiber := fun a => affinePlaneMarkedSurface a
  totalTopology := (constantComplexPlaneFamily ℂ).totalTopology
  projection_continuous := (constantComplexPlaneFamily ℂ).projection_continuous
  analyticVariation := True

/-! The affine family has an explicit total-space coordinate.  The first
homeomorphism changes the dependent-sum presentation to the trivial bundle;
Mathlib's standard trivial-bundle homeomorphism then exposes the product
coordinates `(base, fibre)`. -/

noncomputable def affinePlaneTotalHomeomorph :
    @Homeomorph
      (Sigma fun a => (affinePlaneFamily.fiber a).carrier)
      (ℂ × ℂ)
      affinePlaneFamily.totalTopology inferInstance := by
  letI : TopologicalSpace
      (Sigma fun a => (affinePlaneFamily.fiber a).carrier) :=
    affinePlaneFamily.totalTopology
  exact (constantComplexPlaneTotalHomeomorph ℂ).trans
    (Bundle.Trivial.homeomorphProd ℂ ℂ)

@[simp] theorem affinePlaneTotalHomeomorph_apply (a z : ℂ) :
    affinePlaneTotalHomeomorph ⟨a, z⟩ = (a, z) := by
  rfl

/-- The standard topological bundle witness for the translated-coordinate
family. -/
noncomputable def affinePlaneBundleWitness :
    FiberBundleWitness affinePlaneFamily where
  model := ℂ
  modelTopology := inferInstance
  modelNonempty := ⟨0⟩
  modelHomeomorph := fun _ => @Homeomorph.refl ℂ inferInstance
  bundleTopology := @Bundle.Trivial.topologicalSpace ℂ ℂ inferInstance inferInstance
  totalSpaceHomeomorph := constantComplexPlaneTotalHomeomorph ℂ
  bundle := by
    exact Bundle.Trivial.fiberBundle ℂ ℂ

/-- The translated-coordinate family with an explicit chartwise holomorphic
witness for every parameter. -/
noncomputable def affinePlaneAnalyticFamily : AnalyticFamily ℂ ℂ where
  family := affinePlaneFamily
  variation :=
    { topology := affinePlaneBundleWitness
      modelSurface := complexPlane
      fiberHolomorphic := by
        intro a
        exact affinePlaneIdentityHolomorphic a }

/-- The translated-coordinate family is jointly holomorphic in the base and
the fibre coordinate: its universal coordinate is `(a, z) ↦ z - a`. -/
noncomputable def affinePlaneJointlyHolomorphic :
    JointlyHolomorphicFamily ℂ affinePlaneAnalyticFamily where
  fiberEquiv := fun _ => @Homeomorph.refl ℂ inferInstance
  chartIndex := fun a => by
    letI : TopologicalSpace (affinePlaneFamily.fiber a).carrier :=
      (affinePlaneFamily.fiber a).topology
    exact PUnit.unit
  jointCoordinate := fun p => p.2 - p.1
  jointCoordinate_eq_chart := by
    intro a z
    letI : TopologicalSpace (affinePlaneFamily.fiber a).carrier :=
      (affinePlaneFamily.fiber a).topology
    rfl
  jointlyHolomorphic := by
    simpa using
      (differentiable_snd.sub differentiable_fst :
        Differentiable ℂ (fun p : ℂ × ℂ => p.2 - p.1))

/-! The preceding global family now has an explicit local analytic-family
instance on every open base neighbourhood.  This is the first concrete
object that can later be fed into a local Cech chart comparison. -/

noncomputable def affinePlaneLocalJointlyHolomorphicFamily
    (U : Set ℂ) (hU : IsOpen U) :
    LocalJointlyHolomorphicFamily ℂ
      (canonicalPullback affinePlaneAnalyticFamily.family
        (fun b : U => (b : ℂ)) continuous_subtype_val)
      (ComplexBaseChart.idOnOpen U hU) :=
  affinePlaneJointlyHolomorphic.restrictToOpen U hU

/-! On an open base subset the affine total space is not merely abstractly
locally trivial: its chosen local total-space topology is homeomorphic to the
literal product `U × ℂ`. -/

noncomputable def affinePlaneLocalTotalHomeomorph
    (U : Set ℂ) (hU : IsOpen U) :
    @Homeomorph
      (LocalBaseTotal affinePlaneFamily
        (ComplexBaseChart.openSubset U hU))
      (U × ℂ)
      (localBaseTotalTopology affinePlaneFamily
        (ComplexBaseChart.openSubset U hU)) inferInstance := by
  let C := ComplexBaseChart.openSubset U hU
  let m := localBaseTotalMap affinePlaneFamily C
  let H := affinePlaneTotalHomeomorph
  letI : TopologicalSpace
      (Sigma fun a => (affinePlaneFamily.fiber a).carrier) :=
    affinePlaneFamily.totalTopology
  letI : TopologicalSpace (LocalBaseTotal affinePlaneFamily C) :=
    localBaseTotalTopology affinePlaneFamily C
  refine
    { toFun := fun x => (x.1, x.2)
      invFun := fun p => ⟨⟨p.1, p.1.property⟩, p.2⟩
      left_inv := by
        intro x
        cases x with
        | mk b z =>
          apply Sigma.ext
          · apply Subtype.ext
            rfl
          · rfl
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · rfl
      continuous_toFun := by
        have hm : @Continuous
            (LocalBaseTotal affinePlaneFamily C)
            (Sigma fun a => (affinePlaneFamily.fiber a).carrier)
            (localBaseTotalTopology affinePlaneFamily C)
            affinePlaneFamily.totalTopology m :=
          continuous_induced_dom
        have hbase : @Continuous
            (LocalBaseTotal affinePlaneFamily C) U
            (localBaseTotalTopology affinePlaneFamily C) inferInstance
            (fun x => x.1) := by
          apply Continuous.subtype_mk
          have hproj : @Continuous
              (Sigma fun a => (affinePlaneFamily.fiber a).carrier) ℂ
              affinePlaneFamily.totalTopology inferInstance (fun z => z.1) :=
            affinePlaneFamily.projection_continuous
          have hproj := hproj.comp hm
          simpa [m, localBaseTotalMap, Function.comp_def] using hproj
        have hfibre : @Continuous
            (LocalBaseTotal affinePlaneFamily C) ℂ
            (localBaseTotalTopology affinePlaneFamily C) inferInstance
            (fun x => x.2) := by
          have hprod := H.continuous_toFun.comp hm
          have hsnd := continuous_snd.comp hprod
          simpa [H, m, localBaseTotalMap, Function.comp_def,
            affinePlaneTotalHomeomorph_apply] using hsnd
        exact hbase.prodMk hfibre
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        have hbase : Continuous (fun p : U × ℂ => (p.1 : ℂ)) :=
          continuous_subtype_val.comp continuous_fst
        have hprod : Continuous (fun p : U × ℂ => ((p.1 : ℂ), p.2)) :=
          hbase.prodMk continuous_snd
        have hback := H.continuous_invFun.comp hprod
        convert hback using 1
        }

/-! The translated coordinate is itself a homeomorphism of the product.  We
record it separately so that the local chart range can be built by restricting
it to `U × ℂ`. -/

noncomputable def complexShear : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toFun := fun p => (p.1, p.2 - p.1)
  invFun := fun p => (p.1, p.2 + p.1)
  left_inv := by
    intro p
    apply Prod.ext
    · rfl
    · simp
  right_inv := by
    intro p
    apply Prod.ext
    · rfl
    · simp
  continuous_toFun := by
    exact continuous_fst.prodMk (continuous_snd.sub continuous_fst)
  continuous_invFun := by
    exact continuous_fst.prodMk (continuous_snd.add continuous_fst)

/-! The affine-plane family now reaches the full local-chart witness: the
local trivialization, open range, and the translated coordinate chart are all
explicit data. -/

noncomputable def affinePlaneLocalChartWitness
    (U : Set ℂ) (hU : IsOpen U) :
    LocalJointlyHolomorphicChartWitness
      (affinePlaneJointlyHolomorphic.restrictToBaseOpen U hU) := by
  let C := ComplexBaseChart.openSubset U hU
  let J := affinePlaneJointlyHolomorphic.restrictToBaseOpen U hU
  let hset : (U ×ˢ (Set.univ : Set ℂ) : Set (ℂ × ℂ)) =
      {p : ℂ × ℂ | p.1 ∈ U} := by
    ext p
    simp
  let hprod :
      {p : ℂ × ℂ // p ∈ U ×ˢ (Set.univ : Set ℂ)} ≃ₜ U × ℂ :=
    (Homeomorph.Set.prod U (Set.univ : Set ℂ)).trans
      ((Homeomorph.refl U).prodCongr (Homeomorph.Set.univ ℂ))
  let hpred :
      {p : ℂ × ℂ // p ∈ U ×ˢ (Set.univ : Set ℂ)} ≃ₜ
        {p : ℂ × ℂ // p.1 ∈ U} :=
    Homeomorph.setCongr hset
  let hshear :
      {p : ℂ × ℂ // p.1 ∈ U} ≃ₜ {p : ℂ × ℂ // p.1 ∈ U} :=
    complexShear.subtype (fun p => Iff.rfl)
  letI : TopologicalSpace (LocalBaseTotal affinePlaneFamily C) :=
    localBaseTotalTopology affinePlaneFamily C
  refine
    { localTrivialization :=
        (affinePlaneLocalTotalHomeomorph U hU).symm
      localTrivialization_apply := by
        intro p
        rfl
      range := U ×ˢ (Set.univ : Set ℂ)
      range_open := hU.prod isOpen_univ
      jointChart :=
        hprod.symm.trans (hpred.trans (hshear.trans hpred.symm))
      jointChart_apply := by
        intro p
        change (C.coordinateOn p.1,
            p.2 - C.coordinateOn p.1) =
          (C.coordinateOn p.1,
            J.jointCoordinate (C.coordinateOn p.1, p.2))
        rfl }

noncomputable def affinePlaneLocalComplexSurfaceChart
    (U : Set ℂ) (hU : IsOpen U) :
    @ComplexSurfaceChart
      (LocalBaseTotal affinePlaneFamily
        (ComplexBaseChart.openSubset U hU))
      (localBaseTotalTopology affinePlaneFamily
        (ComplexBaseChart.openSubset U hU)) :=
  (affinePlaneLocalChartWitness U hU).toComplexSurfaceChart

noncomputable def affinePlaneLocalComplexSurfaceAtlas
    (U : Set ℂ) (hU : IsOpen U) :
    ComplexSurfaceAtlas
      (LocalBaseTotal affinePlaneFamily
        (ComplexBaseChart.openSubset U hU)) :=
  (affinePlaneLocalChartWitness U hU).toComplexSurfaceAtlas

/-- The Mathlib local trivialization over a chosen base point. -/
noncomputable def localTrivialization
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} (W : FiberBundleWitness F) (b : B) :
    @Bundle.Trivialization B W.model
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier))
      inferInstance W.modelTopology W.bundleTopology
      (fun z => z.1) := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  exact FiberBundle.trivializationAt W.model (fun b => (F.fiber b).carrier) b

theorem localTrivialization_mem_baseSet
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} (W : FiberBundleWitness F) (b : B) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    b ∈ (localTrivialization W b).baseSet := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  exact FiberBundle.mem_baseSet_trivializationAt W.model
    (fun b => (F.fiber b).carrier) b

theorem localTrivialization_source_eq
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : Family S B} (W : FiberBundleWitness F) (b : B) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    (localTrivialization W b).source =
      (fun z : Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier) => z.1) ⁻¹'
        (localTrivialization W b).baseSet := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  exact (localTrivialization W b).source_eq

/-! ### Standard Mathlib pullbacks -/

/-- Pull back a continuous map into a `ContinuousMap`, so Mathlib's standard
fiber-bundle pullback construction can be used without introducing a second
abstract pullback notion. -/
def asContinuousMap {C B : Type w} [TopologicalSpace C] [TopologicalSpace B]
    (f : C → B) (hf : Continuous f) : ContinuousMap C B :=
  { toFun := f
    continuous_toFun := hf }

/-- The standard Mathlib `FiberBundle` instance on the pullback total space,
made explicit as data rather than left solely to instance synthesis. -/
@[reducible] noncomputable def pullbackFiberBundle
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F : Family S B} (W : FiberBundleWitness F)
    (f : ContinuousMap C B) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
      fun b => (F.fiber b).topology
    letI : (b : B) → Nonempty (F.fiber b).carrier :=
      fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
    letI : (b : B) → Zero (F.fiber b).carrier :=
      fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
    @FiberBundle C W.model inferInstance W.modelTopology
      ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier))
      inferInstance
      (fun c => (F.fiber (f c)).topology) := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : (b : B) → Nonempty (F.fiber b).carrier :=
    fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
  letI : (b : B) → Zero (F.fiber b).carrier :=
    fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  exact @FiberBundle.pullback B W.model
    (fun b => (F.fiber b).carrier) C
    inferInstance W.bundleTopology W.modelTopology inferInstance
    inferInstance
    (ContinuousMap C B) inferInstance inferInstance
    (fun b => (F.fiber b).topology) W.bundle f

/-- The local trivialization obtained from Mathlib's canonical pullback
construction.  The `letI` bindings expose the topologies stored in the
witness to the typeclass-driven Mathlib API. -/
noncomputable def pullbackLocalTrivialization
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F : Family S B} (W : FiberBundleWitness F)
    (f : ContinuousMap C B) (c : C) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
      fun b => (F.fiber b).topology
    letI : (b : B) → Nonempty (F.fiber b).carrier :=
      fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
    letI : (b : B) → Zero (F.fiber b).carrier :=
      fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
    @Bundle.Trivialization C W.model
      (Bundle.TotalSpace W.model
        ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier)))
      inferInstance W.modelTopology inferInstance
      (fun z => z.1) := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : (b : B) → Nonempty (F.fiber b).carrier :=
    fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
  letI : (b : B) → Zero (F.fiber b).carrier :=
    fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  letI : FiberBundle W.model
      ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier)) :=
    pullbackFiberBundle W f
  exact FiberBundle.trivializationAt W.model
    ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier)) c

theorem pullbackLocalTrivialization_baseSet_eq
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F : Family S B} (W : FiberBundleWitness F)
    (f : ContinuousMap C B) (c : C) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
      fun b => (F.fiber b).topology
    (pullbackLocalTrivialization W f c).baseSet =
      (f : C → B) ⁻¹' (localTrivialization W (f c)).baseSet := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : (b : B) → Nonempty (F.fiber b).carrier :=
    fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
  letI : (b : B) → Zero (F.fiber b).carrier :=
    fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  change (f : C → B) ⁻¹' (localTrivialization W (f c)).baseSet =
    (f : C → B) ⁻¹' (localTrivialization W (f c)).baseSet
  rfl

theorem pullbackLocalTrivialization_mem_baseSet
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F : Family S B} (W : FiberBundleWitness F)
    (f : ContinuousMap C B) (c : C) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
      fun b => (F.fiber b).topology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model
          ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier))) := inferInstance
    c ∈ (pullbackLocalTrivialization W f c).baseSet := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : (b : B) → Nonempty (F.fiber b).carrier :=
    fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
  letI : (b : B) → Zero (F.fiber b).carrier :=
    fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  change (f c) ∈ (localTrivialization W (f c)).baseSet
  exact localTrivialization_mem_baseSet W (f c)

theorem pullbackLocalTrivialization_source_eq
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F : Family S B} (W : FiberBundleWitness F)
    (f : ContinuousMap C B) (c : C) :
    letI : TopologicalSpace W.model := W.modelTopology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
      W.bundleTopology
    letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
      fun b => (F.fiber b).topology
    letI : TopologicalSpace
        (Bundle.TotalSpace W.model
          ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier))) := inferInstance
    (pullbackLocalTrivialization W f c).source =
      (fun z : Bundle.TotalSpace W.model
        ((f : C → B) *ᵖ (fun b => (F.fiber b).carrier)) => z.1) ⁻¹'
        (pullbackLocalTrivialization W f c).baseSet := by
  letI : TopologicalSpace W.model := W.modelTopology
  letI : TopologicalSpace
      (Bundle.TotalSpace W.model (fun b => (F.fiber b).carrier)) :=
    W.bundleTopology
  letI : (b : B) → TopologicalSpace (F.fiber b).carrier :=
    fun b => (F.fiber b).topology
  letI : (b : B) → Nonempty (F.fiber b).carrier :=
    fun b => Nonempty.map (W.modelHomeomorph b) W.modelNonempty
  letI : (b : B) → Zero (F.fiber b).carrier :=
    fun b => ⟨Classical.choice (inferInstance : Nonempty (F.fiber b).carrier)⟩
  letI : FiberBundle W.model (fun b => (F.fiber b).carrier) := W.bundle
  exact (pullbackLocalTrivialization W f c).source_eq

end ComplexSurfaceFamily

/-! ### Holomorphic fibrewise equivalence and classification -/

/-- A fibrewise equivalence whose maps are biholomorphic with respect to the
actual atlases carried by the two families. -/
structure HolomorphicFiberwiseEquiv {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F G : ComplexSurfaceFamily.Family S B) where
  map : ∀ b,
    @Homeomorph
      (F.fiber b).carrier (G.fiber b).carrier
      (F.fiber b).topology (G.fiber b).topology
  holomorphic : ∀ b,
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    @AtlasHolomorphicEquiv
      (F.fiber b).carrier (G.fiber b).carrier
      (F.fiber b).topology (G.fiber b).topology
      (F.fiber b).surface.atlas (G.fiber b).surface.atlas (map b)
  marking_commutes : ∀ (b : B) (s : S),
    map b ((F.fiber b).marking s) = (G.fiber b).marking s

namespace HolomorphicFiberwiseEquiv

/-- Forget only the chartwise holomorphic proofs. -/
def toFiberwiseEquiv {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : HolomorphicFiberwiseEquiv F G) :
    FiberwiseEquiv F G where
  map := e.map
  marking_commutes := e.marking_commutes

/-- Reverse a fibrewise biholomorphic equivalence while preserving the marking. -/
def symm {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : HolomorphicFiberwiseEquiv F G) :
    HolomorphicFiberwiseEquiv G F where
  map := fun b => by
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    exact (e.map b).symm
  holomorphic := by
    intro b
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    exact AtlasHolomorphicEquiv.symm (e.holomorphic b)
  marking_commutes := by
    intro b s
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    apply (e.map b).injective
    simpa using (e.marking_commutes b s).symm

def refl {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : ComplexSurfaceFamily.Family S B) :
    HolomorphicFiberwiseEquiv F F where
  map := fun b => @Homeomorph.refl (F.fiber b).carrier (F.fiber b).topology
  holomorphic := by
    intro b
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    exact AtlasHolomorphicEquiv.refl (F.fiber b).surface.atlas
  marking_commutes := by
    intro b s
    rfl

/-! Fibrewise biholomorphisms compose.  The chartwise composition theorem is
    proved in MathlibComplex.lean; this wrapper lifts it pointwise over the
    common base while preserving the fixed marking. -/

def trans {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G H : ComplexSurfaceFamily.Family S B}
    (e₁ : HolomorphicFiberwiseEquiv F G)
    (e₂ : HolomorphicFiberwiseEquiv G H) :
    HolomorphicFiberwiseEquiv F H where
  map := fun b => by
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
    exact (e₁.map b).trans (e₂.map b)
  holomorphic := by
    intro b
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
    exact AtlasHolomorphicEquiv.trans
      (e₁.holomorphic b) (e₂.holomorphic b)
  marking_commutes := by
    intro b s
    change
      (e₂.map b) ((e₁.map b) ((F.fiber b).marking s)) =
        (H.fiber b).marking s
    rw [e₁.marking_commutes, e₂.marking_commutes]

@[simp] theorem trans_map {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G H : ComplexSurfaceFamily.Family S B}
    (e₁ : HolomorphicFiberwiseEquiv F G)
    (e₂ : HolomorphicFiberwiseEquiv G H) :
    ∀ b, (e₁.trans e₂).map b = by
      letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
      letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
      letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
      exact (e₁.map b).trans (e₂.map b) := by
  intro b
  rfl

@[simp] theorem trans_assoc_map {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G H K : ComplexSurfaceFamily.Family S B}
    (e₁ : HolomorphicFiberwiseEquiv F G)
    (e₂ : HolomorphicFiberwiseEquiv G H)
    (e₃ : HolomorphicFiberwiseEquiv H K) :
    ∀ b,
      ((e₁.trans e₂).trans e₃).map b =
        (e₁.trans (e₂.trans e₃)).map b := by
  intro b
  letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
  letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
  letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
  letI : TopologicalSpace (K.fiber b).carrier := (K.fiber b).topology
  apply Homeomorph.ext
  intro x
  rfl

/-! Pulling back a fibrewise biholomorphism along a continuous base map is
    completely formal at the fibre level.  The global atlas of the pullback
    is a separate issue and is therefore intentionally absent here. -/

def pullback {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : HolomorphicFiberwiseEquiv F G)
    (g : C → B) (hg : Continuous g) :
    HolomorphicFiberwiseEquiv
      (ComplexSurfaceFamily.canonicalPullback F g hg)
      (ComplexSurfaceFamily.canonicalPullback G g hg) where
  map := fun c => e.map (g c)
  holomorphic := by
    intro c
    exact e.holomorphic (g c)
  marking_commutes := by
    intro c s
    exact e.marking_commutes (g c) s

@[simp] theorem pullback_map {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : HolomorphicFiberwiseEquiv F G)
    (g : C → B) (hg : Continuous g) :
    (e.pullback g hg).map = fun c => e.map (g c) := by
  rfl

theorem pullback_pullback_map {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : HolomorphicFiberwiseEquiv F G)
    (g : C → B) (k : D → C)
    (hg : Continuous g) (hk : Continuous k) :
    ((e.pullback g hg).pullback k hk).map =
      fun d => e.map (g (k d)) := by
  rfl

/-! The direct and iterated pullbacks have definitionally identical fibres,
    even though their dependent-sum topologies are only canonically
    homeomorphic.  This upgrades the existing topological comparison to the
    holomorphic marked-fibre level. -/

def canonicalPullback_comp {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : ComplexSurfaceFamily.Family S B)
    (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) :
    HolomorphicFiberwiseEquiv
      (ComplexSurfaceFamily.canonicalPullback F (fun d => f (g d))
        (hf.comp hg))
      (ComplexSurfaceFamily.canonicalPullback
        (ComplexSurfaceFamily.canonicalPullback F f hf) g hg) where
  map := fun d => by
    change @Homeomorph
      (F.fiber (f (g d))).carrier (F.fiber (f (g d))).carrier
      (F.fiber (f (g d))).topology (F.fiber (f (g d))).topology
    exact @Homeomorph.refl
      (F.fiber (f (g d))).carrier (F.fiber (f (g d))).topology
  holomorphic := by
    intro d
    letI : TopologicalSpace (F.fiber (f (g d))).carrier :=
      (F.fiber (f (g d))).topology
    change @AtlasHolomorphicEquiv
      (F.fiber (f (g d))).carrier (F.fiber (f (g d))).carrier
      (F.fiber (f (g d))).topology (F.fiber (f (g d))).topology
      (F.fiber (f (g d))).surface.atlas
      (F.fiber (f (g d))).surface.atlas
      (@Homeomorph.refl
        (F.fiber (f (g d))).carrier (F.fiber (f (g d))).topology)
    exact AtlasHolomorphicEquiv.refl _
  marking_commutes := by
    intro d s
    rfl

@[simp] theorem canonicalPullback_comp_map {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : ComplexSurfaceFamily.Family S B)
    (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) :
    (canonicalPullback_comp F f g hf hg).map =
      fun d => @Homeomorph.refl
        (F.fiber (f (g d))).carrier (F.fiber (f (g d))).topology := by
  rfl

end HolomorphicFiberwiseEquiv

/-- A classification witness whose fibrewise realization is chartwise
biholomorphic, while the base map is still only required to be continuous. -/
structure HolomorphicFamilyClassification {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : ComplexSurfaceFamily.Family S B)
    (F : ComplexSurfaceFamily.Family S C) where
  map : C → B
  map_continuous : Continuous map
  realization :
      HolomorphicFiberwiseEquiv F
      (ComplexSurfaceFamily.canonicalPullback U map map_continuous)

/-! A direct base change keeps the target as the one-stage canonical
    pullback.  It is intentionally separate from the later `pullback`
    operation, whose target is the iterated pullback of the already
    classified family. -/

def HolomorphicFamilyClassification.pullbackDirect
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g) :
    HolomorphicFamilyClassification U
      (ComplexSurfaceFamily.canonicalPullback F g hg) where
  map := fun d => c.map (g d)
  map_continuous := c.map_continuous.comp hg
  realization :=
    { map := fun d => c.realization.map (g d)
      holomorphic := by
        intro d
        exact c.realization.holomorphic (g d)
      marking_commutes := by
        intro d s
        exact c.realization.marking_commutes (g d) s }

@[simp] theorem HolomorphicFamilyClassification.pullbackDirect_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g) :
    (c.pullbackDirect g hg).map = fun d => c.map (g d) := by
  rfl

/-! ### Classification with a global pullback atlas

`HolomorphicFamilyClassification` still classifies the fibres of a pullback,
but it does not require the pulled-back total space to carry a global atlas.
The following refinement keeps the same fibrewise realization and adds an
actual `ComplexSurfaceFamilyAtlas` on the canonical pullback total space.
Thus the universal-property interface can distinguish “the fibres are
biholomorphic” from “the pulled-back analytic family exists globally”.
-/

structure GlobalHolomorphicFamilyClassification
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)) where
  map : C → B
  map_continuous : Continuous map
  realization :
    HolomorphicFiberwiseEquiv F.family
      (ComplexSurfaceFamily.canonicalPullback U.family map map_continuous)
  pullback_atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback U.family map map_continuous))
      C inferInstance
  pullback_cover_univ : pullback_atlas.coverSet = Set.univ
  pullback_topology_eq :
    pullback_atlas.toComplexSurfaceAtlas.topology =
      (ComplexSurfaceFamily.canonicalPullback U.family map map_continuous).totalTopology
  pullback_projection_eq : ∀ x,
    pullback_atlas.projection x =
      ComplexSurfaceFamily.projection
        (ComplexSurfaceFamily.canonicalPullback U.family map map_continuous) x

namespace GlobalHolomorphicFamilyClassification

def toHolomorphicFamilyClassification
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F) :
    HolomorphicFamilyClassification U.family F.family where
  map := c.map
  map_continuous := c.map_continuous
  realization := c.realization

theorem map_eq_toHolomorphicFamilyClassification_map
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F) :
    c.toHolomorphicFamilyClassification.map = c.map :=
  rfl

theorem pullback_cover
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (x : ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback U.family c.map c.map_continuous)) :
    x ∈ c.pullback_atlas.coverSet := by
  rw [c.pullback_cover_univ]
  trivial

end GlobalHolomorphicFamilyClassification

/-! A base homeomorphism gives a canonical global classification witness.  The
realization is the fibrewise identity, while the pulled-back atlas is the one
constructed by `GlobalHolomorphicMarkedFamily.pullback`. -/

noncomputable def GlobalHolomorphicFamilyClassification.ofBaseHomeomorph
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (e : @Homeomorph C B inferInstance inferInstance) :
    GlobalHolomorphicFamilyClassification U
      (U.pullback e) where
  map := e
  map_continuous := e.continuous
  realization := HolomorphicFiberwiseEquiv.refl _
  pullback_atlas := (U.pullback e).atlas
  pullback_cover_univ := (U.pullback e).cover_univ
  pullback_topology_eq := (U.pullback e).topology_eq
  pullback_projection_eq := (U.pullback e).projection_eq

/-! A witnessed global pullback gives the genuinely functorial analytic
    base-change operation.  The witness is explicit because a continuous map
    alone does not supply a global atlas on the dependent-sum pullback. -/

def GlobalHolomorphicFamilyClassification.pullbackWithWitness
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g)
    (W_F : F.PullbackWitness g hg)
    (W_U : U.PullbackWitness (fun d => c.map (g d))
      (c.map_continuous.comp hg)) :
    GlobalHolomorphicFamilyClassification U (F.pullbackOf g hg W_F) where
  map := fun d => c.map (g d)
  map_continuous := c.map_continuous.comp hg
  realization := c.toHolomorphicFamilyClassification.pullbackDirect g hg |>.realization
  pullback_atlas := W_U.atlas
  pullback_cover_univ := W_U.cover_univ
  pullback_topology_eq := W_U.topology_eq
  pullback_projection_eq := W_U.projection_eq

@[simp] theorem GlobalHolomorphicFamilyClassification.pullbackWithWitness_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g)
    (W_F : F.PullbackWitness g hg)
    (W_U : U.PullbackWitness (fun d => c.map (g d))
      (c.map_continuous.comp hg)) :
    (c.pullbackWithWitness g hg W_F W_U).map = fun d => c.map (g d) := by
  rfl

/-! The iterated atlas presentation is accepted directly at the universal
    classification boundary.  Its reverse transport supplies the direct
    pullback witness required by `pullbackWithWitness`; the resulting
    classifier is therefore the same classifier, with the same composite map,
    while the target family remains the one-stage pullback. -/

noncomputable def GlobalHolomorphicFamilyClassification.pullbackWithIteratedWitness
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g)
    (W_F : F.PullbackWitness g hg)
    (W_U : U.IteratedPullbackWitness c.map g c.map_continuous hg) :
    GlobalHolomorphicFamilyClassification U (F.pullbackOf g hg W_F) :=
  c.pullbackWithWitness g hg W_F W_U.toDirect

@[simp] theorem GlobalHolomorphicFamilyClassification.pullbackWithIteratedWitness_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g)
    (W_F : F.PullbackWitness g hg)
    (W_U : U.IteratedPullbackWitness c.map g c.map_continuous hg) :
    (c.pullbackWithIteratedWitness g hg W_F W_U).map = fun d => c.map (g d) := by
  rfl

/-! Two global classification witnesses compose once the two total-space
    pullback atlases are supplied.  The first classifier is pulled back along
    the second classifying map; its fibrewise realization is then composed
    with the second classifier's realization.  The atlas on the final direct
    pullback is the one transported from the iterated witness, so the
    construction retains the distinction between fibrewise composition and
    total-space topology. -/

noncomputable def GlobalHolomorphicFamilyClassification.composeWithWitness
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    {G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (d : GlobalHolomorphicFamilyClassification F G)
    (W_F : F.PullbackWitness d.map d.map_continuous)
    (W_U : U.IteratedPullbackWitness
      c.map d.map c.map_continuous d.map_continuous) :
    GlobalHolomorphicFamilyClassification U G := by
  let c' :=
    c.pullbackWithIteratedWitness d.map d.map_continuous W_F W_U
  refine
    { map := fun x => c.map (d.map x)
      map_continuous := c.map_continuous.comp d.map_continuous
      realization := ?_
      pullback_atlas := c'.pullback_atlas
      pullback_cover_univ := c'.pullback_cover_univ
      pullback_topology_eq := c'.pullback_topology_eq
      pullback_projection_eq := c'.pullback_projection_eq }
  simpa [c'] using d.realization.trans c'.realization

@[simp] theorem GlobalHolomorphicFamilyClassification.composeWithWitness_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    {G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (d : GlobalHolomorphicFamilyClassification F G)
    (W_F : F.PullbackWitness d.map d.map_continuous)
    (W_U : U.IteratedPullbackWitness
      c.map d.map c.map_continuous d.map_continuous) :
    (c.composeWithWitness d W_F W_U).map =
      fun x => c.map (d.map x) := by
  rfl

/-! Three successive witnessed classifications can now be composed along one
    common triple pullback atlas.  The left and right constructions retain
    their own transported atlas records, but their classifying maps are the
    same composite; the pointwise realization coherence is supplied by
    `HolomorphicFiberwiseEquiv.trans_assoc_map`. -/

theorem GlobalHolomorphicFamilyClassification.composeWithWitness_assoc_map
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    {G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D)}
    {H : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := E)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (d : GlobalHolomorphicFamilyClassification F G)
    (e : GlobalHolomorphicFamilyClassification G H)
    (W_F_cd : F.PullbackWitness d.map d.map_continuous)
    (W_U_cd : U.IteratedPullbackWitness
      c.map d.map c.map_continuous d.map_continuous)
    (W_G_de : G.PullbackWitness e.map e.map_continuous)
    (W_F_de : F.IteratedPullbackWitness
      d.map e.map d.map_continuous e.map_continuous)
    (W_U_cde : U.TriplePullbackWitness
      c.map d.map e.map c.map_continuous d.map_continuous e.map_continuous) :
    ((c.composeWithWitness d W_F_cd W_U_cd).composeWithWitness
        e W_G_de W_U_cde.toLeftIterated).map =
      (c.composeWithWitness
        (d.composeWithWitness e W_G_de W_F_de)
        W_F_de.toDirect W_U_cde.toRightIterated).map := by
  rfl

theorem GlobalHolomorphicFamilyClassification.composeWithWitness_assoc_realization_map
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    {G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D)}
    {H : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := E)}
    (c : GlobalHolomorphicFamilyClassification U F)
    (d : GlobalHolomorphicFamilyClassification F G)
    (e : GlobalHolomorphicFamilyClassification G H)
    (W_F_cd : F.PullbackWitness d.map d.map_continuous)
    (W_U_cd : U.IteratedPullbackWitness
      c.map d.map c.map_continuous d.map_continuous)
    (W_G_de : G.PullbackWitness e.map e.map_continuous)
    (W_F_de : F.IteratedPullbackWitness
      d.map e.map d.map_continuous e.map_continuous)
    (W_U_cde : U.TriplePullbackWitness
      c.map d.map e.map c.map_continuous d.map_continuous e.map_continuous) :
    ∀ (b : E) (x : (H.family.fiber b).carrier),
      (((c.composeWithWitness d W_F_cd W_U_cd).composeWithWitness
        e W_G_de W_U_cde.toLeftIterated).realization.map b) x =
      ((c.composeWithWitness
        (d.composeWithWitness e W_G_de W_F_de)
        W_F_de.toDirect W_U_cde.toRightIterated).realization.map b) x := by
  intro b x
  rfl

/-! The same witness-based operation becomes an analytic base-change theorem
    once the classifying maps and the base change are given genuine complex
    differentiability certificates. -/

structure GlobalDifferentiableFamilyClassification
    {S : Type u} {B C : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C))
    extends GlobalHolomorphicFamilyClassification U F where
  map_differentiable : Differentiable ℂ map

theorem GlobalDifferentiableFamilyClassification.continuous
    {S : Type u} {B C : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalDifferentiableFamilyClassification U F) :
    Continuous c.map :=
  c.toGlobalHolomorphicFamilyClassification.map_continuous

def GlobalDifferentiableFamilyClassification.pullbackWithWitness
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalDifferentiableFamilyClassification U F)
    (g : D → C) (hg : Differentiable ℂ g)
    (W_F : F.PullbackWitness g hg.continuous)
    (W_U : U.PullbackWitness (fun d => c.map (g d))
      (c.toGlobalHolomorphicFamilyClassification.map_continuous.comp hg.continuous)) :
    GlobalDifferentiableFamilyClassification U
      (F.pullbackOf g hg.continuous W_F) where
  toGlobalHolomorphicFamilyClassification :=
    GlobalHolomorphicFamilyClassification.pullbackWithWitness
      c.toGlobalHolomorphicFamilyClassification g hg.continuous W_F W_U
  map_differentiable := c.map_differentiable.fun_comp hg

@[simp] theorem GlobalDifferentiableFamilyClassification.pullbackWithWitness_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)}
    (c : GlobalDifferentiableFamilyClassification U F)
    (g : D → C) (hg : Differentiable ℂ g)
    (W_F : F.PullbackWitness g hg.continuous)
    (W_U : U.PullbackWitness (fun d => c.map (g d))
      (c.toGlobalHolomorphicFamilyClassification.map_continuous.comp hg.continuous)) :
    (c.pullbackWithWitness g hg W_F W_U).map = fun d => c.map (g d) := by
  rfl

/-! A fine-moduli interface whose quantifiers range over the actual global
analytic-family objects above, not over the legacy `analyticVariation : Prop`
field.  No instance is claimed here: constructing one is the global
Teichmüller universal-family problem. -/

structure GlobalFineHolomorphicUniversalMarkedFamily
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)) where
  universal : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C)),
    GlobalHolomorphicFamilyClassification U F
  classify_unique : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C))
    (c₁ c₂ : GlobalHolomorphicFamilyClassification U F),
    c₁.map = c₂.map

/-! Fine universality turns the witnessed composition theorem into an actual
    functoriality statement for classifying maps.  The atlas witnesses are
    still explicit hypotheses: this theorem does not claim that an arbitrary
    continuous base map automatically carries a global analytic pullback. -/

theorem GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    (u : GlobalFineHolomorphicUniversalMarkedFamily U)
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C))
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D))
    (d : GlobalHolomorphicFamilyClassification F G)
    (W_F : F.PullbackWitness d.map d.map_continuous)
    (W_U : U.IteratedPullbackWitness
      (u.universal F).map d.map
      (u.universal F).map_continuous d.map_continuous) :
    (u.universal G).map =
      fun x => (u.universal F).map (d.map x) := by
  symm
  exact u.classify_unique G
    ((u.universal F).composeWithWitness d W_F W_U)
    (u.universal G)

theorem GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp_comp
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    (u : GlobalFineHolomorphicUniversalMarkedFamily U)
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := C))
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := D))
    (H : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := E))
    (d : GlobalHolomorphicFamilyClassification F G)
    (e : GlobalHolomorphicFamilyClassification G H)
    (W_F : F.PullbackWitness d.map d.map_continuous)
    (W_U : U.IteratedPullbackWitness
      (u.universal F).map d.map
      (u.universal F).map_continuous d.map_continuous)
    (W_G : G.PullbackWitness e.map e.map_continuous)
    (W_UG : U.IteratedPullbackWitness
      (u.universal G).map e.map
      (u.universal G).map_continuous e.map_continuous) :
    (u.universal H).map =
      fun x => (u.universal F).map (d.map (e.map x)) := by
  have hGH := GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp
    u G H e W_G W_UG
  have hFG := GlobalFineHolomorphicUniversalMarkedFamily.classify_map_comp
    u F G d W_F W_U
  funext x
  rw [hGH, hFG]

/-! A classification witness is stable under base change.  The new witness is
    obtained by evaluating the old fibrewise biholomorphism at the pulled-back
    base point; its classifying map is exactly the composite of the old map
    with the base-change map.  This is the first explicit functorial action on
    the universal-property data, rather than only on the underlying family. -/

def HolomorphicFamilyClassification.pullback
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g) :
    HolomorphicFamilyClassification U
      (ComplexSurfaceFamily.canonicalPullback F g hg) where
  map := fun d => c.map (g d)
  map_continuous := c.map_continuous.comp hg
  realization :=
    { map := fun d => c.realization.map (g d)
      holomorphic := by
        intro d
        exact c.realization.holomorphic (g d)
      marking_commutes := by
        intro d s
        exact c.realization.marking_commutes (g d) s }

@[simp] theorem HolomorphicFamilyClassification.pullback_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F)
    (g : D → C) (hg : Continuous g) :
    (c.pullback g hg).map = fun d => c.map (g d) := by
  rfl

theorem HolomorphicFamilyClassification.pullback_pullback_map
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F)
    (g : D → C) (k : E → D)
    (hg : Continuous g) (hk : Continuous k) :
    ((c.pullback g hg).pullback k hk).map =
      (c.pullback (fun e => g (k e)) (hg.comp hk)).map := by
  rfl

/-!
### Holomorphicity of the classifying map

The preceding classification witness asks for a continuous map on the base and
for biholomorphic identifications of the fibres.  For a genuinely analytic
moduli problem this is still one step short: the classifying map itself must be
holomorphic in the parameter.  The following refinement is stated for complex
model bases (normed complex vector spaces); it is deliberately separate from
`HolomorphicFamilyClassification`, so existing topological classifications do
not silently acquire an unproved analytic claim.
-/

structure DifferentiableFamilyClassification {S : Type u} {B C : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    (U : ComplexSurfaceFamily.Family S B)
    (F : ComplexSurfaceFamily.Family S C)
    extends HolomorphicFamilyClassification U F where
  map_differentiable : Differentiable ℂ map

theorem DifferentiableFamilyClassification.continuous
    {S : Type u} {B C : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : DifferentiableFamilyClassification U F) :
    Continuous c.map :=
  c.toHolomorphicFamilyClassification.map_continuous

/-! The analytic classifying-map certificate is functorial under a
    differentiable change of test base.  The holomorphic realization is the
    preceding pullback construction, while the new derivative certificate is
    the ordinary chain rule for `Differentiable.comp`. -/

def DifferentiableFamilyClassification.pullback
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : DifferentiableFamilyClassification U F)
    (g : D → C) (hg : Differentiable ℂ g) :
    DifferentiableFamilyClassification U
      (ComplexSurfaceFamily.canonicalPullback F g hg.continuous) where
  toHolomorphicFamilyClassification :=
    c.toHolomorphicFamilyClassification.pullback g hg.continuous
  map_differentiable := c.map_differentiable.fun_comp hg

@[simp] theorem DifferentiableFamilyClassification.pullback_map
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : DifferentiableFamilyClassification U F)
    (g : D → C) (hg : Differentiable ℂ g) :
    (c.pullback g hg).map = fun d => c.map (g d) := by
  simp [DifferentiableFamilyClassification.pullback,
    HolomorphicFamilyClassification.pullback]

theorem DifferentiableFamilyClassification.pullback_pullback_map
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : DifferentiableFamilyClassification U F)
    (g : D → C) (k : E → D)
    (hg : Differentiable ℂ g) (hk : Differentiable ℂ k) :
    ((c.pullback g hg).pullback k hk).map =
      (c.pullback (fun e => g (k e)) (hg.fun_comp hk)).map := by
  simp [DifferentiableFamilyClassification.pullback,
    HolomorphicFamilyClassification.pullback]

def HolomorphicFamilyClassification.toFamilyClassification
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    {U : ComplexSurfaceFamily.Family S B}
    {F : ComplexSurfaceFamily.Family S C}
    (c : HolomorphicFamilyClassification U F) :
    FamilyClassification U F where
  map := c.map
  map_continuous := c.map_continuous
  realization := c.realization.toFiberwiseEquiv

/-- The holomorphic upgrade of the universal-family interface. -/
structure HolomorphicUniversalMarkedFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family S B) where
  classify : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C),
    HolomorphicFamilyClassification U F

/-!
### Fine holomorphic classification

Existence of a holomorphic fibrewise realization and uniqueness of its base map
are logically different assertions.  In particular, the latter cannot be
obtained by pretending that two dependent torus fibres are definitionally the
same type.  This refinement records the missing fine-moduli statement as an
explicit field, so a future proof has a precise target and cannot silently
weaken it to topological classification.
-/

structure FineHolomorphicUniversalMarkedFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family S B) where
  universal : HolomorphicUniversalMarkedFamily U
  classify_unique : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C)
    (c₁ c₂ : HolomorphicFamilyClassification U F),
    c₁.map = c₂.map

namespace FineHolomorphicUniversalMarkedFamily

def classify {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {U : ComplexSurfaceFamily.Family S B}
    (u : FineHolomorphicUniversalMarkedFamily U)
    {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C) :
    HolomorphicFamilyClassification U F :=
  u.universal.classify F

theorem classify_map_unique {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {U : ComplexSurfaceFamily.Family S B}
    (u : FineHolomorphicUniversalMarkedFamily U)
    {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C)
    (c₁ c₂ : HolomorphicFamilyClassification U F) :
    c₁.map = c₂.map :=
  u.classify_unique F c₁ c₂

end FineHolomorphicUniversalMarkedFamily

/-- Classification of a constant plane family by the one-point base.  This is
an actual inhabited instance of the classification interface, not a claim
that the one-point base classifies arbitrary marked surfaces. -/
noncomputable def constantComplexPlaneClassification
    (C : Type w) [TopologicalSpace C] :
    HolomorphicFamilyClassification
      (ComplexSurfaceFamily.constantComplexPlaneFamily PUnit)
      (ComplexSurfaceFamily.constantComplexPlaneFamily C) where
  map := fun _ => PUnit.unit
  map_continuous := continuous_const
  realization :=
    { map := fun _ => @Homeomorph.refl
        complexPlaneMarkedSurface.carrier complexPlaneMarkedSurface.topology
      holomorphic := by
        intro c
        letI : TopologicalSpace complexPlaneMarkedSurface.carrier :=
          complexPlaneMarkedSurface.topology
        exact AtlasHolomorphicEquiv.refl complexPlaneMarkedSurface.surface.atlas
      marking_commutes := by
        intro c s
        rfl }

theorem constantComplexPlaneClassification_map_unique
    {C : Type w} [TopologicalSpace C]
    (c : HolomorphicFamilyClassification
      (ComplexSurfaceFamily.constantComplexPlaneFamily PUnit)
      (ComplexSurfaceFamily.constantComplexPlaneFamily C)) :
    c.map = (fun _ => PUnit.unit) := by
  funext c'
  exact Subsingleton.elim _ _

/-- The parameter-dependent translated-coordinate family is also classified by
the one-point base, because every fibre is biholomorphic to the standard
plane. -/
noncomputable def affinePlaneClassification :
    HolomorphicFamilyClassification
      (ComplexSurfaceFamily.constantComplexPlaneFamily PUnit)
      ComplexSurfaceFamily.affinePlaneFamily where
  map := fun _ => PUnit.unit
  map_continuous := continuous_const
  realization :=
    { map := fun _ => @Homeomorph.refl ℂ inferInstance
      holomorphic := by
        intro a
        change @AtlasHolomorphicEquiv ℂ ℂ inferInstance inferInstance
          (affinePlaneAtlas a) complexPlaneAtlas (@Homeomorph.refl ℂ inferInstance)
        exact AtlasHolomorphicEquiv.symm (affinePlaneIdentityHolomorphic a)
      marking_commutes := by
        intro a s
        rfl }

theorem affinePlaneClassification_map_unique
    (c : HolomorphicFamilyClassification
      (ComplexSurfaceFamily.constantComplexPlaneFamily PUnit)
      ComplexSurfaceFamily.affinePlaneFamily) :
    c.map = (fun _ => PUnit.unit) := by
  funext a
  exact Subsingleton.elim _ _

/-! The affine-plane test family also satisfies the stronger requirement that
the classifying map is differentiable.  This is the first populated example of
the analytic (rather than merely continuous) classification interface. -/

noncomputable def affinePlaneDifferentiableClassification :
    DifferentiableFamilyClassification
      (ComplexSurfaceFamily.constantComplexPlaneFamily PUnit)
      ComplexSurfaceFamily.affinePlaneFamily where
  toHolomorphicFamilyClassification := affinePlaneClassification
  map_differentiable := by
    change Differentiable ℂ (fun _ : ℂ => PUnit.unit)
    simpa using
      (differentiable_const (c := PUnit.unit) :
        Differentiable ℂ (fun _ : ℂ => PUnit.unit))

end MathlibFormal
end Teichmuller
