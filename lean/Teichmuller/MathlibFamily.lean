import Teichmuller.MathlibComplex

namespace Teichmuller
namespace MathlibFormal

/-!
Mathlib-backed families and the universal-property interface.

The total space is a dependent sum of the concrete carriers of the fibres.
The topology on that total space is supplied as part of the family, while the
canonical pullback topology is generated from the map into the product of the
new base and the old total space.  This is enough to prove continuity of the
pullback projection with Mathlib's ordinary `Continuous` theorem.

The analytic local-triviality and existence theorems are intentionally still
fields of the family/classification data.  What is now concrete is the
topological transport: fibres are actual complex-atlas objects, markings are
actual homeomorphisms, and pullback uses Mathlib's topology rather than the
self-contained topology from `Topology.lean`.
-/

universe u w v

namespace ComplexSurfaceFamily

/-! Reuse a homeomorphism when the codomain topology is represented by an
equal structure value.  This small transport lemma is useful because a global
family stores both its total-space topology and the atlas topology, together
with an explicit equality between them. -/

def retopologizeHomeomorph
    {X Y : Type*}
    {topologyX : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY) (heq : topologyY = topologyY') :
    @Homeomorph X Y topologyX topologyY' := by
  refine
    { toFun := h.toFun
      invFun := h.invFun
      left_inv := h.left_inv
      right_inv := h.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · cases heq
    exact h.continuous_toFun
  · cases heq
    exact h.continuous_invFun

@[simp] theorem retopologizeHomeomorph_apply
    {X Y : Type*}
    {topologyX : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY) (heq : topologyY = topologyY')
    (x : X) : retopologizeHomeomorph h heq x = h x := by
  cases heq
  rfl

@[simp] theorem retopologizeHomeomorph_subtype_val_apply
    {X Y : Type*} {s : Set Y}
    {topologyX : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace {y : Y // y ∈ s}}
    (h : @Homeomorph X {y : Y // y ∈ s} topologyX topologyY)
    (heq : topologyY = topologyY') (x : X) :
    (retopologizeHomeomorph h heq x).1 = (h x).1 := by
  exact congrArg Subtype.val (retopologizeHomeomorph_apply h heq x)

/-- A dependent family of actual complex surfaces before a fixed topological
    marking has been chosen.  Keeping this layer separate makes the remaining
    marking problem explicit rather than encoding it as an opaque proposition. -/
structure UnmarkedFamily (B : Type w)
    [TopologicalSpace B] where
  fiber : B → Type u
  fiberTopology : ∀ b, TopologicalSpace (fiber b)
  surface : ∀ b,
    @ComplexRiemannSurface (fiber b) (fiberTopology b)
  totalTopology : TopologicalSpace (Sigma fiber)
  projection_continuous :
    @Continuous (Sigma fiber) B totalTopology inferInstance (fun z => z.1)

def UnmarkedTotal {B : Type w}
    [TopologicalSpace B] (F : UnmarkedFamily B) :=
  Sigma F.fiber

def unmarkedProjection {B : Type w}
    [TopologicalSpace B] (F : UnmarkedFamily B) :
    UnmarkedTotal F → B :=
  fun z => z.1

theorem unmarkedProjection_fiber {B : Type w}
    [TopologicalSpace B] (F : UnmarkedFamily B) (b : B)
    (x : F.fiber b) :
    unmarkedProjection F ⟨b, x⟩ = b :=
  rfl

/-! ### Concrete pullback of an unmarked family

The dependent-sum presentation makes the canonical pullback explicit.  Its
topology is induced by the map into the product of the new base and the old
total space, exactly as for the legacy Family interface below. -/

def unmarkedPullbackMap {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) :
    (Sigma fun c => F.fiber (f c)) → C × Sigma F.fiber :=
  fun z => (z.1, ⟨f z.1, z.2⟩)

@[reducible] def unmarkedPullbackTopology {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) :
    TopologicalSpace (Sigma fun c => F.fiber (f c)) := by
  letI : TopologicalSpace (Sigma F.fiber) := F.totalTopology
  exact TopologicalSpace.induced (unmarkedPullbackMap F f) inferInstance

theorem unmarkedPullback_projection_continuous {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) :
    @Continuous
      (Sigma fun c => F.fiber (f c)) C
      (unmarkedPullbackTopology F f) inferInstance (fun z => z.1) := by
  letI : TopologicalSpace (Sigma F.fiber) := F.totalTopology
  letI : TopologicalSpace (Sigma fun c => F.fiber (f c)) :=
    unmarkedPullbackTopology F f
  have hmap :
      @Continuous
        (Sigma fun c => F.fiber (f c)) (C × Sigma F.fiber)
        (unmarkedPullbackTopology F f) inferInstance
        (unmarkedPullbackMap F f) :=
    continuous_induced_dom
  have hfst :
      @Continuous (C × Sigma F.fiber) C inferInstance inferInstance
        Prod.fst :=
    continuous_fst
  have hcomp :
      @Continuous
        (Sigma fun c => F.fiber (f c)) C
        (unmarkedPullbackTopology F f) inferInstance
        (fun z => Prod.fst (unmarkedPullbackMap F f z)) :=
    hfst.comp hmap
  simpa [unmarkedPullbackMap] using hcomp

def UnmarkedFamily.canonicalPullback {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) (_hf : Continuous f) :
    UnmarkedFamily C where
  fiber := fun c => F.fiber (f c)
  fiberTopology := fun c => F.fiberTopology (f c)
  surface := fun c => F.surface (f c)
  totalTopology := unmarkedPullbackTopology F f
  projection_continuous := unmarkedPullback_projection_continuous F f

@[simp] theorem UnmarkedFamily.canonicalPullback_fiber {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) (hf : Continuous f) (c : C) :
    (F.canonicalPullback f hf).fiber c = F.fiber (f c) :=
  rfl

@[simp] theorem UnmarkedFamily.canonicalPullback_surface {B : Type w} {C : Type v}
    [TopologicalSpace B] [TopologicalSpace C]
    (F : UnmarkedFamily B) (f : C → B) (hf : Continuous f) (c : C) :
    (F.canonicalPullback f hf).surface c = F.surface (f c) :=
  rfl

/-- A concrete total-space atlas attached to an unmarked family.  The atlas
may cover a distinguished open/local region of the total space; the field
`projection_eq` prevents the chart projection from silently drifting away
from the family projection. -/
structure UnmarkedFamilyAtlas {B : Type w}
    [TopologicalSpace B] (F : UnmarkedFamily B) (X : Type u) where
  atlas : MathlibFormal.ComplexSurfaceFamilyAtlas X B
  totalPoint : X → UnmarkedTotal F
  projection_eq : ∀ x, atlas.projection x = unmarkedProjection F (totalPoint x)

theorem unmarked_projection_fiber {B : Type w}
    [TopologicalSpace B] (F : UnmarkedFamily B) (b : B)
    (x : F.fiber b) :
    (fun z : UnmarkedTotal F => z.1) ⟨b, x⟩ = b :=
  rfl

/-! A fixed-reference marking can be added independently of analytic
local-triviality.  This is the concrete bridge from an unmarked dependent
family to the marked-family interface below; its parameter-direction
holomorphicity is intentionally not included here. -/

structure MarkedUnmarkedFamily (S : Type u) (B : Type w)
    [TopologicalSpace S] [TopologicalSpace B] where
  family : UnmarkedFamily.{u, w} B
  marking : ∀ b,
    @Homeomorph S (family.fiber b) inferInstance (family.fiberTopology b)

def MarkedUnmarkedFamily.canonicalPullback {S : Type u} {B : Type w} {C : Type v}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : MarkedUnmarkedFamily S B) (f : C → B) (hf : Continuous f) :
    MarkedUnmarkedFamily S C where
  family := F.family.canonicalPullback f hf
  marking := fun c => F.marking (f c)

@[simp] theorem MarkedUnmarkedFamily.canonicalPullback_marking
    {S : Type u} {B : Type w} {C : Type v}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : MarkedUnmarkedFamily S B) (f : C → B) (hf : Continuous f)
    (c : C) :
    (F.canonicalPullback f hf).marking c = F.marking (f c) :=
  rfl

/-- A family of marked complex surfaces over a topological base. -/
structure Family.{uF, wF, vF} (S : Type uF) (B : Type wF)
    [TopologicalSpace S] [TopologicalSpace B] where
  fiber : B → MarkedComplexRiemannSurface.{uF, vF} S
  totalTopology :
    TopologicalSpace (Sigma fun b => (fiber b).carrier)
  projection_continuous :
    @Continuous
      (Sigma fun b => (fiber b).carrier) B
      totalTopology inferInstance (fun z => z.1)
  analyticVariation : Prop

/-! ### Assembly from uniformly supplied fibre slices

The fixed-parameter slice construction in MathlibComplex.lean is not yet a
family construction: the dependent sum of the slice carriers need not carry
the topology of a pre-existing total space merely because its projection is
continuous.  The following witness records exactly the missing comparison
data.  Its analyticVariation field is deliberately the same proposition
used by the legacy Family interface; no joint holomorphic variation is
silently inferred from fibrewise atlases.
-/

structure MarkedFiberSliceFamilyAssemblyWitness {S : Type u} {X : Type v}
    {B : Type w} [TopologicalSpace S] [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) where
  slice : ∀ b,
    _root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness
      (S := S) A b
  totalTopology :
    TopologicalSpace
      (Sigma fun b =>
        (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (slice b)).carrier)
  totalSpaceHomeomorph :
    @Homeomorph
      (Sigma fun b =>
        (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (slice b)).carrier)
      X
      totalTopology
      A.toComplexSurfaceAtlas.topology
  projection_eq : ∀ z,
    A.projection (totalSpaceHomeomorph z) = z.1
  analyticVariation : Prop

noncomputable def MarkedFiberSliceFamilyAssemblyWitness.toFamily
    {S : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B}
    (W : MarkedFiberSliceFamilyAssemblyWitness (S := S) A) :
    @Family S B inferInstance inferInstance := by
  refine
    { fiber := fun b =>
        _root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (W.slice b)
      totalTopology := W.totalTopology
      projection_continuous := ?_
      analyticVariation := W.analyticVariation }
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  letI : TopologicalSpace
      (Sigma fun b =>
        (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (W.slice b)).carrier) :=
    W.totalTopology
  have hA :
      @Continuous X B A.toComplexSurfaceAtlas.topology inferInstance
        A.projection :=
    A.projection_continuous
  have hcomp :
      @Continuous
        (Sigma fun b =>
          (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
            (W.slice b)).carrier)
        B W.totalTopology inferInstance
        (fun z => A.projection (W.totalSpaceHomeomorph z)) :=
    by
      have hhomeo :
          @Continuous
            (Sigma fun b =>
              (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
                (W.slice b)).carrier)
            X W.totalTopology A.toComplexSurfaceAtlas.topology
            W.totalSpaceHomeomorph :=
        W.totalSpaceHomeomorph.continuous
      exact hA.comp hhomeo
  have heq :
      (fun z => A.projection (W.totalSpaceHomeomorph z)) =
        (fun z :
          Sigma fun b =>
            (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
              (W.slice b)).carrier => z.1) := by
    funext z
    exact W.projection_eq z
  rw [← heq]
  exact hcomp

@[simp] theorem MarkedFiberSliceFamilyAssemblyWitness.toFamily_fiber
    {S : Type u} {X : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B}
    (W : MarkedFiberSliceFamilyAssemblyWitness (S := S) A) (b : B) :
    (W.toFamily).fiber b =
      _root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
        (W.slice b) :=
  rfl

/-! The same comparison homeomorphism transports the given two-dimensional
total-space atlas to the dependent-sum presentation of the assembled family.
The first-coordinate identity is preserved because the comparison map
commutes with the original projection. -/

noncomputable def MarkedFiberSliceFamilyAssemblyWitness.toFamilyAtlas
    {S : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B}
    (W : MarkedFiberSliceFamilyAssemblyWitness (S := S) A) :
    @ComplexSurfaceFamilyAtlas
      (Sigma fun b =>
        (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (W.slice b)).carrier)
      B inferInstance := by
  letI : TopologicalSpace
      (Sigma fun b =>
        (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
          (W.slice b)).carrier) :=
    W.totalTopology
  let e := W.totalSpaceHomeomorph
  refine
    { toComplexSurfaceAtlas :=
        ComplexSurfaceAtlas.transport_univ A.toComplexSurfaceAtlas e
      projection := fun z => z.1
      parameterCoordinate := A.parameterCoordinate
      projection_continuous := ?_
      chart_base_coordinate := ?_ }
  · exact W.toFamily.projection_continuous
  · intro i z hz
    have hzA : e z ∈ (A.chart i.down).domain := hz
    have hcoord := A.chart_base_coordinate i.down hzA
    have htransport := ComplexSurfaceChart.transport_chart_val_univ
      (e := e) (A := A.chart i.down) (x := z) (hx := hz)
    calc
      (((ComplexSurfaceAtlas.transport_univ A.toComplexSurfaceAtlas e).chart i).chart
          ⟨z, hz⟩).1.1 =
          ((A.chart i.down).chart ⟨e z, hzA⟩).1.1 := by
            exact congrArg Prod.fst htransport
      _ = A.parameterCoordinate (A.projection (e z)) := hcoord
      _ = A.parameterCoordinate z.1 := by
        rw [W.projection_eq z]

def Total {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) :=
  Sigma fun b => (F.fiber b).carrier

def projection {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) : Total F → B :=
  fun z => z.1

theorem projection_fiber {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (b : B) (x : (F.fiber b).carrier) :
    projection F ⟨b, x⟩ = b :=
  rfl

theorem projection_continuous_of_family {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) :
    @Continuous (Total F) B F.totalTopology inferInstance (projection F) :=
  F.projection_continuous

/-- The map from a pullback total space into the old base-total product. -/
def pullbackMap {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (f : C → B) :
    (Sigma fun c => (F.fiber (f c)).carrier) → C × Total F :=
  fun z => (z.1, ⟨f z.1, z.2⟩)

/-- The canonical induced topology on the dependent-sum pullback. -/
@[reducible] def pullbackTopology {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (f : C → B) :
    TopologicalSpace (Sigma fun c => (F.fiber (f c)).carrier) := by
  letI : TopologicalSpace (Total F) := F.totalTopology
  exact TopologicalSpace.induced (pullbackMap F f) inferInstance

theorem pullback_projection_continuous {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (f : C → B) :
    @Continuous
      (Sigma fun c => (F.fiber (f c)).carrier) C
      (pullbackTopology F f) inferInstance (fun z => z.1) := by
  letI : TopologicalSpace (Total F) := F.totalTopology
  have hmap :
      @Continuous
        (Sigma fun c => (F.fiber (f c)).carrier) (C × Total F)
        (pullbackTopology F f) inferInstance (pullbackMap F f) :=
    continuous_induced_dom
  have hfst : @Continuous (C × Total F) C inferInstance inferInstance Prod.fst :=
    continuous_fst
  letI : TopologicalSpace (Sigma fun c => (F.fiber (f c)).carrier) :=
    pullbackTopology F f
  have hcomp := hfst.comp hmap
  simpa [Function.comp_def, pullbackMap, pullbackTopology, Total, projection] using hcomp

theorem pullbackTopology_eq_induced_total_of_isInducing
    {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (g : C → B) (_hg : Continuous g)
    (hg_ind :
      @TopologicalSpace.induced C B g inferInstance =
        (inferInstance : TopologicalSpace C)) :
    pullbackTopology F g =
      @TopologicalSpace.induced
        (Sigma fun c => (F.fiber (g c)).carrier)
        (Total F)
        (fun z => (⟨g z.1, z.2⟩ : Total F)) F.totalTopology := by
  let P := Sigma fun c => (F.fiber (g c)).carrier
  let inner : P → Total F := fun z => ⟨g z.1, z.2⟩
  letI : TopologicalSpace (Total F) := F.totalTopology
  apply le_antisymm
  · letI : TopologicalSpace P := pullbackTopology F g
    have hmap :
        @Continuous P (C × Total F)
          (pullbackTopology F g) inferInstance (pullbackMap F g) :=
      continuous_induced_dom
    have h := (@continuous_snd C (Total F)
      inferInstance inferInstance).comp hmap
    have hcont : @Continuous P (Total F)
        (pullbackTopology F g) F.totalTopology inner := by
      simpa [inner, Function.comp_def, pullbackMap] using h
    exact continuous_iff_le_induced.mp hcont
  · letI : TopologicalSpace P :=
        @TopologicalSpace.induced P (Total F) inner F.totalTopology
    have hcont : @Continuous P P
        (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
        (pullbackTopology F g) id := by
      apply continuous_induced_rng.mpr
      have hinner :
          @Continuous P (Total F)
            (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
            F.totalTopology inner :=
        continuous_induced_dom
      have hbase_old :
          @Continuous P B
            (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
            inferInstance (fun z => g z.1) := by
        have hproj :
            @Continuous (Total F) B F.totalTopology inferInstance
              (projection F) :=
          F.projection_continuous
        have hcomp :
            @Continuous P B
              (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
              inferInstance (projection F ∘ inner) :=
          hproj.comp hinner
        simpa [inner, projection, Function.comp_def] using hcomp
      have hbase :
          @Continuous P C
            (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
            inferInstance (fun z => z.1) := by
        rw [← hg_ind]
        apply continuous_induced_rng.mpr
        simpa [Function.comp_def] using hbase_old
      have hpair :
          @Continuous P (C × Total F)
            (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
            inferInstance (fun z => (z.1, inner z)) :=
        hbase.prodMk hinner
      change @Continuous P (C × Total F)
        (@TopologicalSpace.induced P (Total F) inner F.totalTopology)
        inferInstance (pullbackMap F g)
      exact hpair
    simpa only [induced_id] using
      (continuous_iff_le_induced.mp hcont)

/-- Pull a family back along a continuous map of bases. -/
def canonicalPullback {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (f : C → B) (_hf : Continuous f) : Family S C where
  fiber := fun c => F.fiber (f c)
  totalTopology := pullbackTopology F f
  projection_continuous := pullback_projection_continuous F f
  analyticVariation := F.analyticVariation

theorem canonicalPullback_fiber {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B) (f : C → B) (hf : Continuous f) (c : C) :
    (canonicalPullback F f hf).fiber c = F.fiber (f c) :=
  rfl

/-! A base homeomorphism gives a canonical homeomorphism from the pulled-back
total space to the original total space.  The fibre terms are definitionally
the same; the only nontrivial content is continuity for the induced
pullback topologies. -/

noncomputable def canonicalPullback_homeomorph
    {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : Family S B)
    (e : @Homeomorph C B inferInstance inferInstance) :
    @Homeomorph
      (Total (canonicalPullback F e e.continuous)) (Total F)
      (canonicalPullback F e e.continuous).totalTopology F.totalTopology := by
  let P := canonicalPullback F e e.continuous
  letI : TopologicalSpace (Total F) := F.totalTopology
  letI : TopologicalSpace (Total P) := P.totalTopology
  letI : TopologicalSpace (C × Total F) := inferInstance
  letI : TopologicalSpace (C × Total P) := inferInstance
  let inv : Total F → Total P := fun z =>
    ⟨e.symm z.1, by
      simpa [P, canonicalPullback] using z.2⟩
  exact
    { toFun := fun z => ⟨e z.1, z.2⟩
      invFun := inv
      left_inv := by
        intro z
        cases z with
        | mk c x =>
          apply Sigma.ext
          · exact e.symm_apply_apply c
          · simp [inv, P, canonicalPullback]
      right_inv := by
        intro z
        apply Sigma.ext
        · simp [inv]
        · simp [inv, P, canonicalPullback]
      continuous_toFun := by
        have hmap : @Continuous (Total P) (C × Total F)
            P.totalTopology inferInstance (pullbackMap F e) :=
          continuous_induced_dom
        have h := (@continuous_snd C (Total F) inferInstance inferInstance).comp hmap
        simpa [Function.comp_def, pullbackMap, P, canonicalPullback] using h
      continuous_invFun := by
        change @Continuous (Sigma fun b => (F.fiber b).carrier)
          (Sigma fun c => (P.fiber c).carrier) F.totalTopology
          (pullbackTopology F e) inv
        apply continuous_induced_rng.mpr
        have hfirst : @Continuous (Total F) C F.totalTopology inferInstance
            (fun z => e.symm (projection F z)) :=
          e.continuous_invFun.comp F.projection_continuous
        have hsecond : @Continuous (Total F) (Total F) F.totalTopology
            F.totalTopology (fun z => z) :=
          @continuous_id (Total F) F.totalTopology
        have h : @Continuous (Total F) (C × Total F) F.totalTopology inferInstance
            (fun z => (e.symm (projection F z), z)) :=
          hfirst.prodMk hsecond
        convert h using 1
        funext z
        apply Prod.ext
        · rfl
        · apply Sigma.ext
          · simp [pullbackMap, inv, P, canonicalPullback]
          · cases z
            simp [pullbackMap, inv, P, canonicalPullback] }

/-! The pullback along a subtype-valued base map is not merely an abstract
    dependent sum.  It is canonically homeomorphic to the corresponding
    subspace of the original total space.  This is the topological starting
    point for restricting an analytic family to an open base neighbourhood. -/

noncomputable def canonicalPullback_subtype_homeomorph
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) (V : Set B) :
    @Homeomorph
      (Total
        (canonicalPullback F (fun v : V => (v : B))
          continuous_subtype_val))
      {x : Total F // projection F x ∈ V}
      (pullbackTopology F (fun v : V => (v : B)))
      (TopologicalSpace.induced Subtype.val F.totalTopology) := by
  let P := canonicalPullback F (fun v : V => (v : B))
    continuous_subtype_val
  let R := {x : Total F // projection F x ∈ V}
  letI : TopologicalSpace (Total F) := F.totalTopology
  letI : TopologicalSpace (Total P) := P.totalTopology
  letI : TopologicalSpace R :=
    TopologicalSpace.induced Subtype.val F.totalTopology
  let toRestricted : Total P → R := fun z =>
    ⟨⟨(z.1 : B), z.2⟩, by
      change (z.1 : B) ∈ V
      exact z.1.property⟩
  let fromRestricted : R → Total P := fun z =>
    ⟨⟨z.1.1, z.2⟩, z.1.2⟩
  exact
    { toFun := toRestricted
      invFun := fromRestricted
      left_inv := by
        intro z
        cases z with
        | mk v x =>
          apply Sigma.ext
          · apply Subtype.ext
            rfl
          · rfl
      right_inv := by
        intro z
        apply Subtype.ext
        apply Sigma.ext
        · rfl
        · rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hmap :
            @Continuous (Total P) (V × Total F)
              P.totalTopology inferInstance (pullbackMap F
                (fun v : V => (v : B))) :=
          continuous_induced_dom
        have h :=
          (@continuous_snd V (Total F) inferInstance inferInstance).comp hmap
        change @Continuous (Total P) (Total F)
          P.totalTopology F.totalTopology
          (fun z => ⟨(z.1 : B), z.2⟩)
        simpa only [Function.comp_def, pullbackMap] using h
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        have hfirst :
            @Continuous R V inferInstance inferInstance
              (fun z => ⟨projection F z.1, z.2⟩) := by
          apply Continuous.subtype_mk
          have hval :
              @Continuous R (Total F)
                (TopologicalSpace.induced Subtype.val F.totalTopology)
                F.totalTopology Subtype.val :=
            continuous_subtype_val
          have hp :
              @Continuous (Total F) B F.totalTopology inferInstance
                (projection F) :=
            F.projection_continuous
          exact hp.comp hval
        have hsecond :
            @Continuous R (Total F) inferInstance F.totalTopology
              (fun z => z.1) :=
          continuous_subtype_val
        have hpair := hfirst.prodMk hsecond
        convert hpair using 1 }

theorem projection_preimage_isOpen
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : Family S B) {V : Set B} (hV : IsOpen V) :
    @IsOpen (Total F) F.totalTopology (projection F ⁻¹' V) := by
  letI : TopologicalSpace (Total F) := F.totalTopology
  exact hV.preimage (projection_continuous_of_family F)

/-! Pullback is functorial also for the Mathlib-backed family interface.  The
    two dependent sums have the same underlying terms, but their induced
    topologies are constructed in two stages.  The identity map is therefore
    promoted to a genuine homeomorphism.  This is the concrete topological
    form of the base-change associativity used later by analytic families. -/

def canonicalPullback_comp_homeomorph {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : Family S B) (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) :
    @Homeomorph
      (Sigma fun d => (F.fiber (f (g d))).carrier)
      (Sigma fun d =>
        ((canonicalPullback F f hf).fiber (g d)).carrier)
      (pullbackTopology F (fun d => f (g d)))
      (pullbackTopology (canonicalPullback F f hf) g) := by
  let A := Sigma fun d => (F.fiber (f (g d))).carrier
  let CTotal := Sigma fun c => (F.fiber (f c)).carrier
  let Iter := Sigma fun d => ((canonicalPullback F f hf).fiber (g d)).carrier
  let τF : TopologicalSpace (Total F) := F.totalTopology
  let τC : TopologicalSpace CTotal := pullbackTopology F f
  let τA : TopologicalSpace A := pullbackTopology F (fun d => f (g d))
  let τI : TopologicalSpace Iter := pullbackTopology (canonicalPullback F f hf) g
  letI : TopologicalSpace (Total F) := τF
  letI : TopologicalSpace CTotal := τC
  letI : TopologicalSpace A := τA
  letI : TopologicalSpace Iter := τI
  letI : TopologicalSpace (Total (canonicalPullback F f hf)) :=
    (canonicalPullback F f hf).totalTopology
  change @Homeomorph A Iter τA τI
  have hdirect :
      @Continuous A (D × Total F) τA inferInstance
        (pullbackMap F (fun d => f (g d))) := by
    exact continuous_induced_dom
  have hdirect_fst : @Continuous A D τA inferInstance (fun z => z.1) := by
    have h := (@continuous_fst D (Total F) inferInstance inferInstance).comp hdirect
    convert h using 1 <;> rfl
  have hdirect_snd :
      @Continuous A (Total F) τA inferInstance
        (fun z => (⟨f (g z.1), z.2⟩ : Total F)) := by
    have h := (@continuous_snd D (Total F) inferInstance inferInstance).comp hdirect
    convert h using 1 <;> rfl
  have h_to_intermediate :
      @Continuous A CTotal τA τC (fun z => ⟨g z.1, z.2⟩) := by
    apply continuous_induced_rng.mpr
    have hpair := (hg.comp hdirect_fst).prodMk hdirect_snd
    change @Continuous A (C × Total F) τA inferInstance
      (fun z => (g z.1, (⟨f (g z.1), z.2⟩ : Total F)))
    exact hpair
  have hiter_map :
      @Continuous A (D × CTotal) τA inferInstance
        (pullbackMap (canonicalPullback F f hf) g) := by
    have hpair := hdirect_fst.prodMk h_to_intermediate
    change @Continuous A (D × CTotal) τA inferInstance
      (fun z => (z.1, (⟨g z.1, z.2⟩ : CTotal)))
    exact hpair
  have hforward : @Continuous A Iter τA τI (fun z => z) := by
    apply continuous_induced_rng.mpr
    convert hiter_map using 1 <;> rfl
  have hiter :
      @Continuous Iter (D × CTotal) τI inferInstance
        (pullbackMap (canonicalPullback F f hf) g) := by
    exact continuous_induced_dom
  have hiter_fst : @Continuous Iter D τI inferInstance (fun z => z.1) := by
    have h := (@continuous_fst D (Total (canonicalPullback F f hf))
      inferInstance inferInstance).comp hiter
    convert h using 1 <;> rfl
  have hintermediate_to_total :
      @Continuous CTotal (Total F) τC inferInstance
        (fun z => (⟨f z.1, z.2⟩ : Total F)) := by
    have hqf : @Continuous CTotal (C × Total F) τC inferInstance
        (pullbackMap F f) := continuous_induced_dom
    have h := (@continuous_snd C (Total F) inferInstance inferInstance).comp hqf
    convert h using 1 <;> rfl
  have hiter_to_intermediate : @Continuous Iter CTotal τI τC (fun z => ⟨g z.1, z.2⟩) := by
    have h := (@continuous_snd D (Total (canonicalPullback F f hf))
      inferInstance inferInstance).comp hiter
    convert h using 1 <;> rfl
  have hiter_snd : @Continuous Iter (Total F) τI inferInstance
      (fun z => (⟨f (g z.1), z.2⟩ : Total F)) := by
    have h := hintermediate_to_total.comp hiter_to_intermediate
    convert h using 1 <;> rfl
  have hdirect_again :
      @Continuous Iter (D × Total F) τI inferInstance
        (pullbackMap F (fun d => f (g d))) := by
    exact hiter_fst.prodMk hiter_snd
  have hreverse : @Continuous Iter A τI τA (fun z => z) := by
    apply continuous_induced_rng.mpr
    convert hdirect_again using 1 <;> rfl
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      continuous_toFun := hforward
      continuous_invFun := hreverse }

@[simp] theorem canonicalPullback_comp_homeomorph_apply
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : Family S B) (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g)
    (z : Sigma fun d => (F.fiber (f (g d))).carrier) :
    canonicalPullback_comp_homeomorph F f g hf hg z =
      (⟨z.1, z.2⟩ : Sigma fun d =>
        ((canonicalPullback F f hf).fiber (g d)).carrier) := by
  unfold canonicalPullback_comp_homeomorph
  rfl

/-! The preceding comparison is oriented from the direct pullback to the
    iterated one.  The reverse orientation is the one used when a restriction
    is performed in stages: first over `C`, then over `D`. -/

def canonicalPullback_iterated_homeomorph {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : Family S B) (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) :
    @Homeomorph
      (Total (canonicalPullback (canonicalPullback F f hf) g hg))
      (Total (canonicalPullback F (fun d => f (g d)) (hf.comp hg)))
      (canonicalPullback (canonicalPullback F f hf) g hg).totalTopology
      (canonicalPullback F (fun d => f (g d)) (hf.comp hg)).totalTopology :=
  by
    letI : TopologicalSpace
        (Total (canonicalPullback (canonicalPullback F f hf) g hg)) :=
      (canonicalPullback (canonicalPullback F f hf) g hg).totalTopology
    letI : TopologicalSpace
        (Total (canonicalPullback F (fun d => f (g d)) (hf.comp hg))) :=
      (canonicalPullback F (fun d => f (g d)) (hf.comp hg)).totalTopology
    change @Homeomorph
      (Sigma fun d =>
        ((canonicalPullback F f hf).fiber (g d)).carrier)
      (Sigma fun d => (F.fiber (f (g d))).carrier)
      (pullbackTopology (canonicalPullback F f hf) g)
      (pullbackTopology F (fun d => f (g d)))
    letI : TopologicalSpace
        (Sigma fun d =>
          ((canonicalPullback F f hf).fiber (g d)).carrier) :=
      pullbackTopology (canonicalPullback F f hf) g
    letI : TopologicalSpace
        (Sigma fun d => (F.fiber (f (g d))).carrier) :=
      pullbackTopology F (fun d => f (g d))
    let h := canonicalPullback_comp_homeomorph F f g hf hg
    exact
      { toFun := h.invFun
        invFun := h.toFun
        left_inv := h.right_inv
        right_inv := h.left_inv
        continuous_toFun := h.continuous_invFun
        continuous_invFun := h.continuous_toFun }

@[simp] theorem canonicalPullback_iterated_homeomorph_apply
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : Family S B) (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g)
    (z : Total (canonicalPullback (canonicalPullback F f hf) g hg)) :
    canonicalPullback_iterated_homeomorph F f g hf hg z = z := by
  letI : TopologicalSpace
      (Total (canonicalPullback (canonicalPullback F f hf) g hg)) :=
    (canonicalPullback (canonicalPullback F f hf) g hg).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F (fun d => f (g d)) (hf.comp hg))) :=
    (canonicalPullback F (fun d => f (g d)) (hf.comp hg)).totalTopology
  unfold canonicalPullback_iterated_homeomorph
  rfl

/-! The three-stage version is obtained by composing two instances of the
    two-stage comparison.  This records the first nontrivial associativity
    coherence needed for iterated local restrictions. -/

def canonicalPullback_triple_homeomorph
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (F : Family S B) (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    @Homeomorph
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh))
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh))))
      (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
      (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology := by
  let first := canonicalPullback_iterated_homeomorph
    (canonicalPullback F f hf) g h hg hh
  let second := canonicalPullback_iterated_homeomorph
    F f (fun e => g (h e)) hf (hg.comp hh)
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback F f hf) (fun e => g (h e)) (hg.comp hh))) :=
    (canonicalPullback
      (canonicalPullback F f hf) (fun e => g (h e)) (hg.comp hh)).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  change @Homeomorph
    (Total (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh))
    (Total (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))))
    _ _
  exact first.trans second

/-! The same triple comparison can be factored by first comparing the inner
    two pullbacks, then pulling that comparison through the third base map.
    At the level of dependent sums all these comparison maps are the identity;
    the content is that the identity is continuous for the three induced
    topologies. -/

def canonicalPullback_triple_right_homeomorph
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (F : Family S B) (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    @Homeomorph
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh))
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh))))
      (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
      (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology := by
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  let q : D → B := fun d => f (g d)
  have hq : Continuous q := hf.comp hg
  letI : TopologicalSpace (Total (canonicalPullback F q hq)) :=
    (canonicalPullback F q hq).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback (canonicalPullback F q hq) h hh)) :=
    (canonicalPullback (canonicalPullback F q hq) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F (fun e => q (h e)) (hq.comp hh))) :=
    (canonicalPullback F (fun e => q (h e)) (hq.comp hh)).totalTopology
  letI : TopologicalSpace
      (Sigma fun e => (F.fiber (q (h e))).carrier) :=
    pullbackTopology F (fun e => q (h e))
  letI : TopologicalSpace
      (Sigma fun e =>
        ((canonicalPullback F q hq).fiber (h e)).carrier) :=
    pullbackTopology (canonicalPullback F q hq) h
  let left := canonicalPullback_triple_homeomorph F f g h hf hg hh
  let directToRight := canonicalPullback_comp_homeomorph F q h hq hh
  let rightIteration := canonicalPullback_iterated_homeomorph F q h hq hh
  change @Homeomorph
    (Total (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh))
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh))))
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  exact
    { toFun := fun z => rightIteration (directToRight (left z))
      invFun := fun z => left.symm (directToRight.symm (rightIteration.symm z))
      left_inv := by
        intro z
        simp
      right_inv := by
        intro z
        simp
      continuous_toFun := by
        exact rightIteration.continuous_toFun.comp
          (directToRight.continuous_toFun.comp left.continuous_toFun)
      continuous_invFun := by
        exact left.continuous_invFun.comp
          (directToRight.continuous_invFun.comp rightIteration.continuous_invFun) }

@[simp] theorem canonicalPullback_triple_homeomorph_apply
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (F : Family S B) (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (z : Total (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :
    canonicalPullback_triple_homeomorph F f g h hf hg hh z = z := by
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  unfold canonicalPullback_triple_homeomorph
  rfl

@[simp] theorem canonicalPullback_triple_right_homeomorph_apply
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (F : Family S B) (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (z : Total (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :
    canonicalPullback_triple_right_homeomorph F f g h hf hg hh z = z := by
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  unfold canonicalPullback_triple_right_homeomorph
  rfl

theorem canonicalPullback_triple_factorizations_eq
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (F : Family S B) (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    canonicalPullback_triple_homeomorph F f g h hf hg hh =
      canonicalPullback_triple_right_homeomorph F f g h hf hg hh := by
  letI : TopologicalSpace
      (Total (canonicalPullback
        (canonicalPullback (canonicalPullback F f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback F f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (Total (canonicalPullback F
        (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback F
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  apply Homeomorph.ext
  intro z
  rw [canonicalPullback_triple_homeomorph_apply,
    canonicalPullback_triple_right_homeomorph_apply]

/-! A marked unmarked family can be repackaged as the single Mathlib family
interface whose fibres carry both their atlases and their markings.  This is a
literal data conversion: no existence proposition is introduced and the total
space topology is preserved. -/

def MarkedUnmarkedFamily.toFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : MarkedUnmarkedFamily S B) :
    Family S B where
  fiber := fun b =>
    { carrier := F.family.fiber b
      topology := F.family.fiberTopology b
      surface := F.family.surface b
      marking := F.marking b }
  totalTopology := F.family.totalTopology
  projection_continuous := F.family.projection_continuous
  analyticVariation := True

@[simp] theorem MarkedUnmarkedFamily.toFamily_fiber
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : MarkedUnmarkedFamily S B) (b : B) :
    (F.toFamily).fiber b =
      { carrier := F.family.fiber b
        topology := F.family.fiberTopology b
        surface := F.family.surface b
        marking := F.marking b } :=
  rfl

/-! ### A global total-space analytic family

The legacy `Family` structure carries actual marked fibres and a topology on
their dependent-sum total space, but its `analyticVariation` field is only a
proposition.  The following refinement replaces that placeholder with an
actual two-complex-dimensional atlas on the whole total space.  The atlas is
required to cover every point, to use the family topology, and to have the
same projection as the dependent-sum family.  This is the first global
family-level object in this file; it is intentionally separate from the
universal classification interface until a genuine pullback atlas is built.
-/

structure GlobalHolomorphicMarkedFamily.{uF, wF, vF}
    {S : Type uF} {B : Type wF}
    [TopologicalSpace S] [TopologicalSpace B] where
  family : ComplexSurfaceFamily.Family.{uF, wF, vF} S B
  atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total family) B inferInstance
  cover_univ : atlas.coverSet = Set.univ
  topology_eq : atlas.toComplexSurfaceAtlas.topology = family.totalTopology
  projection_eq : ∀ x, atlas.projection x =
    ComplexSurfaceFamily.projection family x

/-! If the original total-space atlas already covers all of its carrier, the
transported family atlas is a genuine global object.  This theorem is
deliberately conditional: the slice assembly and the comparison homeomorphism
are the geometric input, while the equality `hcover` is the exact remaining
globality requirement. -/

noncomputable def MarkedFiberSliceFamilyAssemblyWitness.toGlobalHolomorphicMarkedFamily
    {S : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B}
    (W : MarkedFiberSliceFamilyAssemblyWitness (S := S) A)
    (hcover : A.coverSet = Set.univ) :
    GlobalHolomorphicMarkedFamily (S := S) (B := B) := by
  refine
    { family := W.toFamily
      atlas := ?_
      cover_univ := ?_
      topology_eq := ?_
      projection_eq := ?_ }
  · change
      @ComplexSurfaceFamilyAtlas
        (Sigma fun b =>
          (_root_.Teichmuller.MathlibFormal.MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
            (W.slice b)).carrier)
        B inferInstance
    exact W.toFamilyAtlas
  · change W.toFamilyAtlas.coverSet = Set.univ
    change
      (ComplexSurfaceAtlas.transport_univ A.toComplexSurfaceAtlas
        W.totalSpaceHomeomorph).coverSet = Set.univ
    rw [ComplexSurfaceAtlas.transport_univ_coverSet, hcover]
    ext z
    simp
  · change W.toFamilyAtlas.toComplexSurfaceAtlas.topology = W.totalTopology
    rfl
  · intro z
    change W.toFamilyAtlas.projection z = z.1
    rfl

namespace GlobalHolomorphicMarkedFamily

theorem cover {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (x : ComplexSurfaceFamily.Total G.family) :
    x ∈ G.atlas.coverSet := by
  rw [G.cover_univ]
  trivial

theorem projection_eq_family {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (x : ComplexSurfaceFamily.Total G.family) :
    G.atlas.projection x = ComplexSurfaceFamily.projection G.family x :=
  G.projection_eq x

theorem transition_differentiableOn {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (i j : G.atlas.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        (G.atlas.chart i) (G.atlas.chart j))
      (ComplexSurfaceChart.overlap
        (G.atlas.chart i) (G.atlas.chart j)) :=
  G.atlas.transition_differentiableOn i j

end GlobalHolomorphicMarkedFamily

/-! A continuous base change need not automatically carry a global complex
    atlas: the map into the old total space is generally not a homeomorphism.
    The following witness records exactly the missing geometric datum.  It is
    deliberately stronger than a fibrewise pullback and weaker than claiming
    that every continuous (or differentiable) map has such an atlas. -/

structure GlobalHolomorphicMarkedFamily.PullbackWitness
    {S : Type u} {B D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (g : D → B) (hg : Continuous g) where
  atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total
        (canonicalPullback U.family g hg)) D inferInstance
  cover_univ : atlas.coverSet = Set.univ
  topology_eq :
    atlas.toComplexSurfaceAtlas.topology =
      (canonicalPullback U.family g hg).totalTopology
  projection_eq : ∀ x,
    atlas.projection x =
      ComplexSurfaceFamily.projection
        (canonicalPullback U.family g hg) x

/-! A direct pullback witness can also be transported across the canonical
    associativity homeomorphism to the iterated pullback.  The separate
    structure keeps the two dependent-sum carriers visible instead of
    pretending that their topologies are definitionally equal. -/

structure GlobalHolomorphicMarkedFamily.IteratedPullbackWitness
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) where
  atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total
        (canonicalPullback (canonicalPullback U.family f hf) g hg)) D inferInstance
  cover_univ : atlas.coverSet = Set.univ
  topology_eq :
    atlas.toComplexSurfaceAtlas.topology =
      (canonicalPullback (canonicalPullback U.family f hf) g hg).totalTopology
  projection_eq : ∀ x,
    atlas.projection x =
      ComplexSurfaceFamily.projection
        (canonicalPullback (canonicalPullback U.family f hf) g hg) x

/-! The three-stage witness is the common geometric source for both
    parenthesizations of a triple base change.  Keeping the atlas on the
    genuinely iterated total space makes the later associativity statement
    compare transported atlases, rather than relying on proof-irrelevant
    equality of induced topologies. -/

structure GlobalHolomorphicMarkedFamily.TriplePullbackWitness
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (f : C → B) (g : D → C) (h : E → D)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) where
  atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total
        (canonicalPullback
          (canonicalPullback (canonicalPullback U.family f hf) g hg) h hh))
      E inferInstance
  cover_univ : atlas.coverSet = Set.univ
  topology_eq :
    atlas.toComplexSurfaceAtlas.topology =
      (canonicalPullback
        (canonicalPullback (canonicalPullback U.family f hf) g hg) h hh).totalTopology
  projection_eq : ∀ x,
    atlas.projection x =
      ComplexSurfaceFamily.projection
        (canonicalPullback
          (canonicalPullback (canonicalPullback U.family f hf) g hg) h hh) x

noncomputable def GlobalHolomorphicMarkedFamily.PullbackWitness.toIterated
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {f : C → B} {g : D → C}
    {hf : Continuous f} {hg : Continuous g}
    (W : U.PullbackWitness (fun d => f (g d)) (hf.comp hg)) :
    GlobalHolomorphicMarkedFamily.IteratedPullbackWitness U f g hf hg := by
  let e₀ := ComplexSurfaceFamily.canonicalPullback_iterated_homeomorph
    U.family f g hf hg
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀ W.topology_eq.symm
  let transported := ComplexSurfaceAtlas.transport
    W.atlas.toComplexSurfaceAtlas e
  refine
    { atlas :=
        { toComplexSurfaceAtlas := transported
          projection := fun x => x.1
          parameterCoordinate := W.atlas.parameterCoordinate
          projection_continuous := by
            exact ComplexSurfaceFamily.pullback_projection_continuous
              (canonicalPullback U.family f hf) g
          chart_base_coordinate := by
            intro i x hx
            have hxW : e x ∈ (W.atlas.chart i).domain := by
              exact hx
            have hcoord := W.atlas.chart_base_coordinate i hxW
            have htransport := ComplexSurfaceChart.transport_chart_val
              (e := e) (A := W.atlas.chart i) (x := x) (hx := hx)
            change
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                ⟨x, hx⟩).1.1 = W.atlas.parameterCoordinate (x.1)
            calc
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                  ⟨x, hx⟩).1.1 =
                  ((W.atlas.chart i).chart ⟨e x, hxW⟩).1.1 := by
                exact congrArg Prod.fst htransport
              _ = W.atlas.parameterCoordinate (W.atlas.projection (e x)) :=
                hcoord
              _ = W.atlas.parameterCoordinate (x.1) := by
                congr 1
                rw [W.projection_eq]
                rfl }
      cover_univ := by
        rw [ComplexSurfaceAtlas.transport_coverSet, W.cover_univ]
        exact Set.preimage_univ
      topology_eq := by
        rfl
      projection_eq := by
        intro x
        rfl }

noncomputable def GlobalHolomorphicMarkedFamily.IteratedPullbackWitness.toDirect
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    {U : GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {f : C → B} {g : D → C}
    {hf : Continuous f} {hg : Continuous g}
    (W : U.IteratedPullbackWitness f g hf hg) :
    U.PullbackWitness (fun d => f (g d)) (hf.comp hg) := by
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (canonicalPullback (canonicalPullback U.family f hf) g hg)) :=
    (canonicalPullback (canonicalPullback U.family f hf) g hg).totalTopology
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (canonicalPullback U.family (fun d => f (g d)) (hf.comp hg))) :=
    (canonicalPullback U.family (fun d => f (g d)) (hf.comp hg)).totalTopology
  let e₀ := ComplexSurfaceFamily.canonicalPullback_iterated_homeomorph
    U.family f g hf hg
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀.symm W.topology_eq.symm
  let transported := ComplexSurfaceAtlas.transport
    W.atlas.toComplexSurfaceAtlas e
  refine
    { atlas :=
        { toComplexSurfaceAtlas := transported
          projection := fun x => x.1
          parameterCoordinate := W.atlas.parameterCoordinate
          projection_continuous := by
            exact ComplexSurfaceFamily.pullback_projection_continuous
              U.family (fun d => f (g d))
          chart_base_coordinate := by
            intro i x hx
            have hxW : e x ∈ (W.atlas.chart i).domain := by
              exact hx
            have hcoord := W.atlas.chart_base_coordinate i hxW
            have htransport := ComplexSurfaceChart.transport_chart_val
              (e := e) (A := W.atlas.chart i) (x := x) (hx := hx)
            change
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                ⟨x, hx⟩).1.1 = W.atlas.parameterCoordinate (x.1)
            calc
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                  ⟨x, hx⟩).1.1 =
                  ((W.atlas.chart i).chart ⟨e x, hxW⟩).1.1 := by
                exact congrArg Prod.fst htransport
              _ = W.atlas.parameterCoordinate (W.atlas.projection (e x)) :=
                hcoord
              _ = W.atlas.parameterCoordinate (x.1) := by
                congr 1
                rw [W.projection_eq]
                change (e₀.symm x).1 = x.1
                rfl }
      cover_univ := by
        rw [ComplexSurfaceAtlas.transport_coverSet, W.cover_univ]
        exact Set.preimage_univ
      topology_eq := by
        rfl
      projection_eq := by
        intro x
        rfl }

/-! Collapse a triple witness to the one-stage pullback.  The proof is the
    same atlas transport used for two stages, now driven by the explicit
    three-stage comparison homeomorphism. -/

noncomputable def GlobalHolomorphicMarkedFamily.TriplePullbackWitness.toDirect
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {f : C → B} {g : D → C} {h : E → D}
    {hf : Continuous f} {hg : Continuous g} {hh : Continuous h}
    (W : U.TriplePullbackWitness f g h hf hg hh) :
    U.PullbackWitness (fun e => f (g (h e)))
      (hf.comp (hg.comp hh)) := by
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (canonicalPullback
          (canonicalPullback (canonicalPullback U.family f hf) g hg) h hh)) :=
    (canonicalPullback
      (canonicalPullback (canonicalPullback U.family f hf) g hg) h hh).totalTopology
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (canonicalPullback U.family
          (fun e => f (g (h e))) (hf.comp (hg.comp hh)))) :=
    (canonicalPullback U.family
      (fun e => f (g (h e))) (hf.comp (hg.comp hh))).totalTopology
  let e₀ := ComplexSurfaceFamily.canonicalPullback_triple_homeomorph
    U.family f g h hf hg hh
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀.symm W.topology_eq.symm
  let transported := ComplexSurfaceAtlas.transport
    W.atlas.toComplexSurfaceAtlas e
  refine
    { atlas :=
        { toComplexSurfaceAtlas := transported
          projection := fun x => x.1
          parameterCoordinate := W.atlas.parameterCoordinate
          projection_continuous := by
            exact ComplexSurfaceFamily.pullback_projection_continuous
              U.family (fun e => f (g (h e)))
          chart_base_coordinate := by
            intro i x hx
            have hxW : e x ∈ (W.atlas.chart i).domain := by
              exact hx
            have hcoord := W.atlas.chart_base_coordinate i hxW
            have htransport := ComplexSurfaceChart.transport_chart_val
              (e := e) (A := W.atlas.chart i) (x := x) (hx := hx)
            change
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                ⟨x, hx⟩).1.1 = W.atlas.parameterCoordinate (x.1)
            calc
              ((ComplexSurfaceChart.transport e (W.atlas.chart i)).chart
                  ⟨x, hx⟩).1.1 =
                  ((W.atlas.chart i).chart ⟨e x, hxW⟩).1.1 := by
                exact congrArg Prod.fst htransport
              _ = W.atlas.parameterCoordinate (W.atlas.projection (e x)) :=
                hcoord
              _ = W.atlas.parameterCoordinate (x.1) := by
                congr 1
                rw [W.projection_eq]
                change (e₀.symm x).1 = x.1
                rfl }
      cover_univ := by
        rw [ComplexSurfaceAtlas.transport_coverSet, W.cover_univ]
        exact Set.preimage_univ
      topology_eq := by
        rfl
      projection_eq := by
        intro x
        rfl }

/-! The same triple atlas supplies the two possible two-stage witnesses. -/

noncomputable def GlobalHolomorphicMarkedFamily.TriplePullbackWitness.toLeftIterated
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {f : C → B} {g : D → C} {h : E → D}
    {hf : Continuous f} {hg : Continuous g} {hh : Continuous h}
    (W : U.TriplePullbackWitness f g h hf hg hh) :
    U.IteratedPullbackWitness (fun d => f (g d)) h
      (hf.comp hg) hh := by
  exact GlobalHolomorphicMarkedFamily.PullbackWitness.toIterated
    (f := fun d => f (g d)) (g := h)
    (hf := hf.comp hg) (hg := hh) W.toDirect

noncomputable def GlobalHolomorphicMarkedFamily.TriplePullbackWitness.toRightIterated
    {S : Type u} {B C D E : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    {U : GlobalHolomorphicMarkedFamily (S := S) (B := B)}
    {f : C → B} {g : D → C} {h : E → D}
    {hf : Continuous f} {hg : Continuous g} {hh : Continuous h}
    (W : U.TriplePullbackWitness f g h hf hg hh) :
    U.IteratedPullbackWitness f (fun e => g (h e))
      hf (hg.comp hh) := by
  exact GlobalHolomorphicMarkedFamily.PullbackWitness.toIterated
    (f := f) (g := fun e => g (h e))
    (hf := hf) (hg := hg.comp hh) W.toDirect

/-! An open base subset is a case where the missing pullback atlas can be
constructed rather than supplied as an extra witness.  The proof factors
through the canonical homeomorphism from the subtype pullback to the open
subspace of the old total space, restricts the old atlas there, and transports
the restricted atlas back to the pullback total space. -/

noncomputable def GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V) :
    G.PullbackWitness (fun v : V => (v : B)) continuous_subtype_val := by
  let P := canonicalPullback G.family (fun v : V => (v : B))
    continuous_subtype_val
  let Rset : Set (Total G.family) :=
    projection G.family ⁻¹' V
  have hR_family : @IsOpen (Total G.family) G.family.totalTopology Rset := by
    exact projection_preimage_isOpen G.family hV
  have hR_atlas : @IsOpen (Total G.family)
      G.atlas.toComplexSurfaceAtlas.topology Rset := by
    rw [G.topology_eq]
    exact hR_family
  let restricted :=
    ComplexSurfaceFamilyAtlas.restrictOpenSubspace
      G.atlas Rset hR_atlas
  let hsub := canonicalPullback_subtype_homeomorph G.family V
  have htopR :
      TopologicalSpace.induced Subtype.val G.family.totalTopology =
        restricted.toComplexSurfaceAtlas.topology := by
    change TopologicalSpace.induced Subtype.val G.family.totalTopology =
      TopologicalSpace.induced Subtype.val G.atlas.toComplexSurfaceAtlas.topology
    rw [G.topology_eq]
    rfl
  let hsub' :=
    ComplexSurfaceFamily.retopologizeHomeomorph hsub htopR
  let transported :=
    ComplexSurfaceAtlas.transport restricted.toComplexSurfaceAtlas hsub'
  refine
    { atlas :=
        { toComplexSurfaceAtlas := transported
          projection := fun z => z.1
          parameterCoordinate := fun v : V => G.atlas.parameterCoordinate (v : B)
          projection_continuous := by
            exact pullback_projection_continuous G.family
              (fun v : V => (v : B))
          chart_base_coordinate := by
            intro i x hx
            have hx_restricted : hsub' x ∈ (restricted.chart i).domain := by
              exact hx
            have hcoord := restricted.chart_base_coordinate i hx_restricted
            have htransport := ComplexSurfaceChart.transport_chart_val
              (e := hsub') (A := restricted.chart i) (x := x) (hx := hx)
            change
              ((ComplexSurfaceChart.transport hsub' (restricted.chart i)).chart
                ⟨x, hx⟩).1.1 =
                G.atlas.parameterCoordinate ((x.1 : V) : B)
            calc
              ((ComplexSurfaceChart.transport hsub' (restricted.chart i)).chart
                  ⟨x, hx⟩).1.1 =
                  ((restricted.chart i).chart ⟨hsub' x, hx_restricted⟩).1.1 := by
                exact congrArg Prod.fst htransport
              _ = restricted.parameterCoordinate (restricted.projection (hsub' x)) :=
                hcoord
              _ = G.atlas.parameterCoordinate ((x.1 : V) : B) := by
                change G.atlas.parameterCoordinate (G.atlas.projection (hsub' x)) =
                  G.atlas.parameterCoordinate ((x.1 : V) : B)
                have hproj : G.atlas.projection (hsub' x) =
                    ((x.1 : V) : B) := by
                  rw [G.projection_eq]
                  rw [retopologizeHomeomorph_apply hsub htopR x]
                  rfl
                exact congrArg G.atlas.parameterCoordinate hproj }
      cover_univ := by
        rw [ComplexSurfaceAtlas.transport_coverSet]
        change (fun x => hsub' x) ⁻¹' (Subtype.val ⁻¹' G.atlas.coverSet) = Set.univ
        rw [G.cover_univ]
        ext x
        constructor
        · intro _
          trivial
        · intro _
          simpa [ComplexSurfaceFamily.projection] using (hsub' x).property
      topology_eq := by
        rfl
      projection_eq := by
        intro x
        rfl }

theorem GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness_chart_apply_val
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V) (i : G.atlas.index)
    (x : ComplexSurfaceFamily.Total
      (canonicalPullback G.family (fun v : V => (v : B))
        continuous_subtype_val))
    (hx : x ∈
      ((G.baseOpenPullbackWitness V hV).atlas.chart i).domain)
    (hxo :
      ((canonicalPullback_subtype_homeomorph G.family V x).1 ∈
        (G.atlas.chart i).domain)) :
    (((G.baseOpenPullbackWitness V hV).atlas.chart i).chart
      ⟨x, hx⟩).1 =
      ((G.atlas.chart i).chart
        ⟨(canonicalPullback_subtype_homeomorph G.family V x).1, hxo⟩).1 := by
  rfl

theorem GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness_chart_domain
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V) (i : G.atlas.index) :
    ((G.baseOpenPullbackWitness V hV).atlas.chart i).domain =
      (fun x =>
        (canonicalPullback_subtype_homeomorph G.family V x).1) ⁻¹'
        (G.atlas.chart i).domain := by
  rfl

def GlobalHolomorphicMarkedFamily.pullbackOf
    {S : Type u} {B D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (g : D → B) (hg : Continuous g)
    (W : U.PullbackWitness g hg) :
    GlobalHolomorphicMarkedFamily (S := S) (B := D) where
  family := canonicalPullback U.family g hg
  atlas := W.atlas
  cover_univ := W.cover_univ
  topology_eq := W.topology_eq
  projection_eq := W.projection_eq

noncomputable def GlobalHolomorphicMarkedFamily.pullbackOfIterated
    {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g)
    (W : U.PullbackWitness (fun d => f (g d)) (hf.comp hg)) :
    GlobalHolomorphicMarkedFamily (S := S) (B := D) where
  family := canonicalPullback (canonicalPullback U.family f hf) g hg
  atlas := (W.toIterated).atlas
  cover_univ := (W.toIterated).cover_univ
  topology_eq := (W.toIterated).topology_eq
  projection_eq := (W.toIterated).projection_eq

/-! For an open base subset the preceding witness is canonical, so the
restricted global analytic family can be named directly. -/

noncomputable def GlobalHolomorphicMarkedFamily.restrictBaseOpen
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V) :
    GlobalHolomorphicMarkedFamily (S := S) (B := V) :=
  G.pullbackOf (fun v : V => (v : B)) continuous_subtype_val
    (G.baseOpenPullbackWitness V hV)

namespace GlobalHolomorphicMarkedFamily

theorem pullbackOf_cover
    {S : Type u} {B D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (g : D → B) (hg : Continuous g)
    (W : U.PullbackWitness g hg)
    (x : ComplexSurfaceFamily.Total
      (canonicalPullback U.family g hg)) :
    x ∈ (U.pullbackOf g hg W).atlas.coverSet := by
  rw [(U.pullbackOf g hg W).cover_univ]
  trivial

theorem pullbackOf_projection
    {S : Type u} {B D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace D]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (g : D → B) (hg : Continuous g)
    (W : U.PullbackWitness g hg)
    (x : ComplexSurfaceFamily.Total
      (canonicalPullback U.family g hg)) :
    (U.pullbackOf g hg W).atlas.projection x =
      ComplexSurfaceFamily.projection
        (canonicalPullback U.family g hg) x :=
  (U.pullbackOf g hg W).projection_eq x

/-! Transport a global family atlas along a homeomorphism of total spaces.
    The base projection compatibility is the precise condition that lets the
    first chart coordinate remain the same parameter coordinate. -/

noncomputable def transportAlongHomeomorph
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (F : ComplexSurfaceFamily.Family S B)
    (e : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.atlas.toComplexSurfaceAtlas.topology)
    (he : ∀ x,
      U.atlas.projection (e x) =
        ComplexSurfaceFamily.projection F x) :
    GlobalHolomorphicMarkedFamily (S := S) (B := B) where
  family := F
  atlas := by
    let transported :=
      ComplexSurfaceAtlas.transport U.atlas.toComplexSurfaceAtlas e
    exact
      { toComplexSurfaceAtlas := transported
        projection := ComplexSurfaceFamily.projection F
        parameterCoordinate := U.atlas.parameterCoordinate
        projection_continuous := by
          change @Continuous
            (ComplexSurfaceFamily.Total F) B F.totalTopology inferInstance
            (ComplexSurfaceFamily.projection F)
          exact F.projection_continuous
        chart_base_coordinate := by
          intro i x hx
          have hx_old : e x ∈ (U.atlas.chart i).domain := by
            exact hx
          have hcoord := U.atlas.chart_base_coordinate i hx_old
          have htransport := ComplexSurfaceChart.transport_chart_val
            (e := e) (A := U.atlas.chart i) (x := x) (hx := hx)
          calc
            ((ComplexSurfaceChart.transport e (U.atlas.chart i)).chart
                ⟨x, hx⟩).1.1 =
                ((U.atlas.chart i).chart ⟨e x, hx_old⟩).1.1 := by
              exact congrArg Prod.fst htransport
            _ = U.atlas.parameterCoordinate
                (U.atlas.projection (e x)) := hcoord
            _ = U.atlas.parameterCoordinate
                (ComplexSurfaceFamily.projection F x) := by
              exact congrArg U.atlas.parameterCoordinate (he x) }
  cover_univ := by
    rw [ComplexSurfaceAtlas.transport_coverSet, U.cover_univ]
    exact Set.preimage_univ
  topology_eq := by
    rfl
  projection_eq := by
    intro x
    rfl

/-! Transporting a global family atlas is associative as well.  The second
    comparison homeomorphism is allowed to have its own projection witness;
    the final witness records the corresponding composite projection law. -/

theorem transportAlongHomeomorph_trans
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (F G : ComplexSurfaceFamily.Family S B)
    (e : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.atlas.toComplexSurfaceAtlas.topology)
    (d : @Homeomorph
      (ComplexSurfaceFamily.Total G)
      (ComplexSurfaceFamily.Total F)
      G.totalTopology F.totalTopology)
    (he : ∀ x,
      U.atlas.projection (e x) =
        ComplexSurfaceFamily.projection F x)
    (hd : ∀ x,
      (U.transportAlongHomeomorph F e he).atlas.projection (d x) =
        ComplexSurfaceFamily.projection G x)
    (hcomp : ∀ x,
      U.atlas.projection
          (@Homeomorph.trans
            (ComplexSurfaceFamily.Total G)
            (ComplexSurfaceFamily.Total F)
            (ComplexSurfaceFamily.Total U.family)
            G.totalTopology F.totalTopology
            U.atlas.toComplexSurfaceAtlas.topology d e x) =
        ComplexSurfaceFamily.projection G x) :
    (U.transportAlongHomeomorph F e he).transportAlongHomeomorph G d hd =
      U.transportAlongHomeomorph G
        (@Homeomorph.trans
          (ComplexSurfaceFamily.Total G)
          (ComplexSurfaceFamily.Total F)
          (ComplexSurfaceFamily.Total U.family)
          G.totalTopology F.totalTopology
          U.atlas.toComplexSurfaceAtlas.topology d e)
        hcomp := by
  rfl

/-! The comparison homeomorphism used by two-stage open restriction.  Here
    `W` is an open subset of the already restricted base `V`; the direct
    family over `W` uses the composite inclusion into `B`.  The proof is the
    generic pullback associativity theorem, while the global analytic atlases
    are supplied by `restrictBaseOpen` on each stage. -/

noncomputable def nestedOpenRestrictionComparison
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V)
    (W : Set V) (hW : IsOpen W) :
    @Homeomorph
      (ComplexSurfaceFamily.Total
        ((G.restrictBaseOpen V hV).restrictBaseOpen W hW).family)
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback G.family
          (fun w : W => ((w : V) : B))
          (continuous_subtype_val.comp continuous_subtype_val)))
      ((G.restrictBaseOpen V hV).restrictBaseOpen W hW).family.totalTopology
      (ComplexSurfaceFamily.canonicalPullback G.family
        (fun w : W => ((w : V) : B))
        (continuous_subtype_val.comp continuous_subtype_val)).totalTopology := by
  let f : V → B := fun v => (v : B)
  let g : W → V := fun w => (w : V)
  have hf : Continuous f := continuous_subtype_val
  have hg : Continuous g := continuous_subtype_val
  have hassoc := ComplexSurfaceFamily.canonicalPullback_iterated_homeomorph
    G.family f g hf hg
  change @Homeomorph
    (ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback
        (ComplexSurfaceFamily.canonicalPullback G.family f hf) g hg))
    (ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback G.family
        (fun w : W => f (g w)) (hf.comp hg)))
    (ComplexSurfaceFamily.canonicalPullback
      (ComplexSurfaceFamily.canonicalPullback G.family f hf) g hg).totalTopology
    (ComplexSurfaceFamily.canonicalPullback G.family
      (fun w : W => f (g w)) (hf.comp hg)).totalTopology
  simpa [f, g] using hassoc

/-! The direct open restriction inherits an actual global atlas from the
    two-stage restriction.  Thus the comparison is no longer only a
    homeomorphism of family total spaces: it transports the analytic charts. -/

noncomputable def directOpenRestriction
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V)
    (W : Set V) (hW : IsOpen W) :
    GlobalHolomorphicMarkedFamily (S := S) (B := W) := by
  let U := (G.restrictBaseOpen V hV).restrictBaseOpen W hW
  let F :=
    ComplexSurfaceFamily.canonicalPullback G.family
      (fun w : W => ((w : V) : B))
      (continuous_subtype_val.comp continuous_subtype_val)
  let h := nestedOpenRestrictionComparison G V hV W hW
  letI : TopologicalSpace (ComplexSurfaceFamily.Total F) := F.totalTopology
  letI : TopologicalSpace (ComplexSurfaceFamily.Total U.family) :=
    U.family.totalTopology
  let hsymm : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.family.totalTopology := h.symm
  let e : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.atlas.toComplexSurfaceAtlas.topology :=
    ComplexSurfaceFamily.retopologizeHomeomorph hsymm U.topology_eq.symm
  apply GlobalHolomorphicMarkedFamily.transportAlongHomeomorph U F e
  intro x
  rw [U.projection_eq]
  rfl

/-! A three-level open restriction is the concrete specialization of the
    triple pullback comparison. -/

noncomputable def tripleOpenRestrictionComparison
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V)
    (W : Set V) (hW : IsOpen W)
    (Z : Set W) (hZ : IsOpen Z) :
    @Homeomorph
      (ComplexSurfaceFamily.Total
        (GlobalHolomorphicMarkedFamily.restrictBaseOpen
          ((G.restrictBaseOpen V hV).restrictBaseOpen W hW) Z hZ).family)
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback G.family
          (fun z : Z => (((z : W) : V) : B))
          (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_subtype_val))))
      (GlobalHolomorphicMarkedFamily.restrictBaseOpen
        ((G.restrictBaseOpen V hV).restrictBaseOpen W hW) Z hZ).family.totalTopology
      (ComplexSurfaceFamily.canonicalPullback G.family
        (fun z : Z => (((z : W) : V) : B))
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_subtype_val))).totalTopology := by
  let f : V → B := fun v => (v : B)
  let g : W → V := fun w => (w : V)
  let k : Z → W := fun z => (z : W)
  have hf : Continuous f := continuous_subtype_val
  have hg : Continuous g := continuous_subtype_val
  have hk : Continuous k := continuous_subtype_val
  have hassoc := ComplexSurfaceFamily.canonicalPullback_triple_homeomorph
    G.family f g k hf hg hk
  change @Homeomorph
    (ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback
        (ComplexSurfaceFamily.canonicalPullback
          (ComplexSurfaceFamily.canonicalPullback G.family f hf) g hg) k hk))
    (ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback G.family
        (fun z : Z => f (g (k z))) (hf.comp (hg.comp hk))))
    (ComplexSurfaceFamily.canonicalPullback
      (ComplexSurfaceFamily.canonicalPullback
        (ComplexSurfaceFamily.canonicalPullback G.family f hf) g hg) k hk).totalTopology
    (ComplexSurfaceFamily.canonicalPullback G.family
      (fun z : Z => f (g (k z))) (hf.comp (hg.comp hk))).totalTopology
  simpa [f, g, k] using hassoc

/-! The triple direct restriction carries the transported global atlas, so the
    three-stage coherence is visible at the analytic-family level. -/

noncomputable def tripleDirectOpenRestriction
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (V : Set B) (hV : IsOpen V)
    (W : Set V) (hW : IsOpen W)
    (Z : Set W) (hZ : IsOpen Z) :
    GlobalHolomorphicMarkedFamily (S := S) (B := Z) := by
  let U := GlobalHolomorphicMarkedFamily.restrictBaseOpen
    ((G.restrictBaseOpen V hV).restrictBaseOpen W hW) Z hZ
  let F :=
    ComplexSurfaceFamily.canonicalPullback G.family
      (fun z : Z => (((z : W) : V) : B))
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val))
  let h := tripleOpenRestrictionComparison G V hV W hW Z hZ
  letI : TopologicalSpace (ComplexSurfaceFamily.Total F) := F.totalTopology
  letI : TopologicalSpace (ComplexSurfaceFamily.Total U.family) :=
    U.family.totalTopology
  let hsymm : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.family.totalTopology := h.symm
  let e : @Homeomorph
      (ComplexSurfaceFamily.Total F)
      (ComplexSurfaceFamily.Total U.family)
      F.totalTopology U.atlas.toComplexSurfaceAtlas.topology :=
    ComplexSurfaceFamily.retopologizeHomeomorph hsymm U.topology_eq.symm
  apply GlobalHolomorphicMarkedFamily.transportAlongHomeomorph U F e
  intro x
  rw [U.projection_eq]
  rfl

end GlobalHolomorphicMarkedFamily

/-! Base change of a global family along a homeomorphism of bases.  The
dependent-sum homeomorphism transports the entire complex atlas, so this is a
genuine pullback operation on global analytic-family data. -/

noncomputable def GlobalHolomorphicMarkedFamily.pullback
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (e : @Homeomorph C B inferInstance inferInstance) :
    GlobalHolomorphicMarkedFamily (S := S) (B := C) where
  family := canonicalPullback U.family e e.continuous
  atlas := by
    let P := canonicalPullback U.family e e.continuous
    let h := canonicalPullback_homeomorph U.family e
    let oldProjection := U.atlas.projection
    let newProjection : Total P → C := fun z => e.symm (oldProjection (h z))
    let newParameterCoordinate : C → ℂ := fun c => U.atlas.parameterCoordinate (e c)
    letI : TopologicalSpace (Total P) := P.totalTopology
    let h' : @Homeomorph (Total P) (Total U.family)
        P.totalTopology U.atlas.toComplexSurfaceAtlas.topology :=
      retopologizeHomeomorph h U.topology_eq.symm
    let transported := ComplexSurfaceAtlas.transport U.atlas.toComplexSurfaceAtlas h'
    exact
      { toComplexSurfaceAtlas := transported
        projection := newProjection
        parameterCoordinate := newParameterCoordinate
        projection_continuous := by
          letI : TopologicalSpace (Total P) := P.totalTopology
          letI : TopologicalSpace (Total U.family) :=
            U.atlas.toComplexSurfaceAtlas.topology
          apply e.continuous_invFun.comp
          apply U.atlas.projection_continuous.comp
          convert h'.continuous_toFun using 1
        chart_base_coordinate := by
          intro i x hx
          have hx_old : h' x ∈ (U.atlas.chart i).domain := hx
          have hchart := U.atlas.chart_base_coordinate i hx_old
          have hh : h' x = h x :=
            retopologizeHomeomorph_apply h U.topology_eq.symm x
          change
            ((ComplexSurfaceChart.transport h' (U.atlas.chart i)).chart
              ⟨x, hx⟩).1.1 =
              U.atlas.parameterCoordinate
                (e (e.symm (U.atlas.projection (h x))))
          have hcoord := ComplexSurfaceChart.transport_chart_val
            (e := h') (A := U.atlas.chart i) (x := x) (hx := hx)
          calc
            ((ComplexSurfaceChart.transport h' (U.atlas.chart i)).chart
                ⟨x, hx⟩).1.1 =
                ((U.atlas.chart i).chart ⟨h' x, hx_old⟩).1.1 := by
              simpa using congrArg Prod.fst hcoord
            _ = U.atlas.parameterCoordinate (U.atlas.projection (h' x)) :=
              hchart
            _ = U.atlas.parameterCoordinate
                (e (e.symm (U.atlas.projection (h x)))) := by
              rw [hh]
              simp }
  cover_univ := by
    rw [ComplexSurfaceAtlas.transport_coverSet, U.cover_univ]
    exact Set.preimage_univ
  topology_eq := by
    rfl
  projection_eq := by
    intro x
    change e.symm (U.atlas.projection
      (canonicalPullback_homeomorph U.family e x)) = projection
        (canonicalPullback U.family e e.continuous) x
    have hproj := U.projection_eq
      (canonicalPullback_homeomorph U.family e x)
    simp [projection, canonicalPullback_homeomorph] at hproj ⊢
    exact hproj.symm ▸ e.symm_apply_apply _

namespace GlobalHolomorphicMarkedFamily

theorem pullback_cover
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (e : @Homeomorph C B inferInstance inferInstance)
    (x : Total (canonicalPullback U.family e e.continuous)) :
    x ∈ (U.pullback e).atlas.coverSet := by
  rw [(U.pullback e).cover_univ]
  trivial

theorem pullback_projection
    {S : Type u} {B C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : GlobalHolomorphicMarkedFamily (S := S) (B := B))
    (e : @Homeomorph C B inferInstance inferInstance)
    (x : Total (canonicalPullback U.family e e.continuous)) :
    (U.pullback e).atlas.projection x =
      projection (canonicalPullback U.family e e.continuous) x :=
  (U.pullback e).projection_eq x

end GlobalHolomorphicMarkedFamily

end ComplexSurfaceFamily

/-! Fibrewise equivalence and the universal-property data. -/

structure FiberwiseEquiv {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F G : ComplexSurfaceFamily.Family S B) where
  map : ∀ b,
    @Homeomorph
      (F.fiber b).carrier (G.fiber b).carrier
      (F.fiber b).topology (G.fiber b).topology
  marking_commutes : ∀ (b : B) (s : S),
    map b ((F.fiber b).marking s) = (G.fiber b).marking s

namespace FiberwiseEquiv

def refl {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : ComplexSurfaceFamily.Family S B) : FiberwiseEquiv F F where
  map := fun b => @Homeomorph.refl (F.fiber b).carrier
    (F.fiber b).topology
  marking_commutes := by
    intro b s
    rfl

def symm {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G : ComplexSurfaceFamily.Family S B}
    (e : FiberwiseEquiv F G) : FiberwiseEquiv G F where
  map := fun b => by
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    exact (e.map b).symm
  marking_commutes := by
    intro b s
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    apply (e.map b).injective
    simpa using (e.marking_commutes b s).symm

def comp {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F G H : ComplexSurfaceFamily.Family S B}
    (eFG : FiberwiseEquiv F G) (eGH : FiberwiseEquiv G H) :
    FiberwiseEquiv F H where
  map := fun b => by
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
    exact (eFG.map b).trans (eGH.map b)
  marking_commutes := by
    intro b s
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    letI : TopologicalSpace (G.fiber b).carrier := (G.fiber b).topology
    letI : TopologicalSpace (H.fiber b).carrier := (H.fiber b).topology
    rw [Homeomorph.trans_apply, eFG.marking_commutes, eGH.marking_commutes]

end FiberwiseEquiv

/-! The same base-change associativity is visible fibrewise: the direct
    pullback and the iterated pullback have the same marked fibre at every
    point of the final base. -/

def canonicalPullback_comp_fiberwiseEquiv {S : Type u} {B C D : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D]
    (F : ComplexSurfaceFamily.Family S B) (f : C → B) (g : D → C)
    (hf : Continuous f) (hg : Continuous g) :
  FiberwiseEquiv
      (ComplexSurfaceFamily.canonicalPullback F (fun d => f (g d)) (hf.comp hg))
      (ComplexSurfaceFamily.canonicalPullback
        (ComplexSurfaceFamily.canonicalPullback F f hf) g hg) where
  map := fun d => by
    change @Homeomorph
      (F.fiber (f (g d))).carrier (F.fiber (f (g d))).carrier
      (F.fiber (f (g d))).topology (F.fiber (f (g d))).topology
    exact @Homeomorph.refl
      (F.fiber (f (g d))).carrier (F.fiber (f (g d))).topology
  marking_commutes := by
    intro d s
    rfl

structure FamilyClassification.{uF, wF, vF}
    {S : Type uF} {B : Type wF} {C : Type wF}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : ComplexSurfaceFamily.Family.{uF, wF, vF} S B)
    (F : ComplexSurfaceFamily.Family.{uF, wF, vF} S C) where
  map : C → B
  map_continuous : Continuous map
  realization :
    FiberwiseEquiv F
      (ComplexSurfaceFamily.canonicalPullback U map map_continuous)

structure UniversalMarkedFamily.{uF, wF, vF}
    {S : Type uF} {B : Type wF}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family.{uF, wF, vF} S B) where
  classify : ∀ {C : Type wF} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family.{uF, wF, vF} S C),
    FamilyClassification U F

structure FineUniversalMarkedFamily.{uF, wF, vF}
    {S : Type uF} {B : Type wF}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family.{uF, wF, vF} S B) where
  universal : UniversalMarkedFamily.{uF, wF, vF} U
  classify_unique : ∀ {C : Type wF} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family.{uF, wF, vF} S C)
    (c₁ c₂ : FamilyClassification U F),
    c₁.map = c₂.map

end MathlibFormal
end Teichmuller
