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
  realization :=
    { map := fun d => c.realization.map (g d)
      holomorphic := by
        intro d
        exact c.realization.holomorphic (g d)
      marking_commutes := by
        intro d s
        exact c.realization.marking_commutes (g d) s }
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
