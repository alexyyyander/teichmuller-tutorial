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
  cases heq
  exact h

@[simp] theorem retopologizeHomeomorph_apply
    {X Y : Type*}
    {topologyX : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY) (heq : topologyY = topologyY')
    (x : X) : retopologizeHomeomorph h heq x = h x := by
  cases heq
  rfl

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
structure Family (S : Type u) (B : Type w)
    [TopologicalSpace S] [TopologicalSpace B] where
  fiber : B → MarkedComplexRiemannSurface S
  totalTopology :
    TopologicalSpace (Sigma fun b => (fiber b).carrier)
  projection_continuous :
    @Continuous
      (Sigma fun b => (fiber b).carrier) B
      totalTopology inferInstance (fun z => z.1)
  analyticVariation : Prop

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

structure GlobalHolomorphicMarkedFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B] where
  family : ComplexSurfaceFamily.Family S B
  atlas :
    @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total family) B inferInstance
  cover_univ : atlas.coverSet = Set.univ
  topology_eq : atlas.toComplexSurfaceAtlas.topology = family.totalTopology
  projection_eq : ∀ x, atlas.projection x =
    ComplexSurfaceFamily.projection family x

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
          funext z
          exact (retopologizeHomeomorph_apply h U.topology_eq.symm z).symm
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

structure FamilyClassification {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (U : ComplexSurfaceFamily.Family S B)
    (F : ComplexSurfaceFamily.Family S C) where
  map : C → B
  map_continuous : Continuous map
  realization :
    FiberwiseEquiv F
      (ComplexSurfaceFamily.canonicalPullback U map map_continuous)

structure UniversalMarkedFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family S B) where
  classify : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C),
    FamilyClassification U F

structure FineUniversalMarkedFamily {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (U : ComplexSurfaceFamily.Family S B) where
  universal : UniversalMarkedFamily U
  classify_unique : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S C)
    (c₁ c₂ : FamilyClassification U F),
    c₁.map = c₂.map

end MathlibFormal
end Teichmuller
