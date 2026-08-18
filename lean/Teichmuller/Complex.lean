import Teichmuller.Topology

namespace Teichmuller
namespace Formal

/-!
The second concrete layer records a complex atlas without claiming that
holomorphicity has already been reduced to real differentiability.  A chart is
an explicit local topological equivalence, including its domain, range,
inverse laws, and relative continuity.  Analytic compatibility is supplied as
the parameter

  isHolomorphicOn : Set M → (M → M) → Prop.

When Mathlib is available, M can be Complex and this parameter can be
instantiated with the appropriate DifferentiableOn predicate.  Keeping it as
an explicit parameter prevents the current core from confusing an atlas
record with a proof of the analytic theorems.
-/

universe u v w

def ContinuousOn {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y)
    (s : Set X) (f : X → Y) : Prop :=
  ∀ U, τY.isOpen U →
    τX.isOpen (Set.inter s (Set.preimage f U))

structure LocalChart {S : Type u} (τS : Topology S)
    {M : Type v} (τM : Topology M) where
  domain : Set S
  range : Set M
  domain_open : τS.isOpen domain
  range_open : τM.isOpen range
  toModel : S → M
  fromModel : M → S
  maps_into : ∀ x, domain x → range (toModel x)
  inverse_into : ∀ z, range z → domain (fromModel z)
  left_inv : ∀ x, domain x → fromModel (toModel x) = x
  right_inv : ∀ z, range z → toModel (fromModel z) = z
  continuous_toModel : ContinuousOn τS τM domain toModel
  continuous_fromModel : ContinuousOn τM τS range fromModel

namespace LocalChart

def overlap {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (i j : LocalChart τS τM) : Set M :=
  fun z => i.range z ∧ j.domain (i.fromModel z)

def transitionMap {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (i j : LocalChart τS τM) : M → M :=
  fun z => j.toModel (i.fromModel z)

theorem transitionMap_agrees_on_overlap
    {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (i j : LocalChart τS τM) {z : M}
    (_hz : overlap i j z) :
    transitionMap i j z = j.toModel (i.fromModel z) := by
  rfl

theorem chart_inverse_on_domain
    {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (c : LocalChart τS τM) {x : S} (hx : c.domain x) :
    c.fromModel (c.toModel x) = x :=
  c.left_inv x hx

theorem chart_inverse_on_range
    {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (c : LocalChart τS τM) {z : M} (hz : c.range z) :
    c.toModel (c.fromModel z) = z :=
  c.right_inv z hz

end LocalChart

/-!
`HolomorphicTheory` is a small algebraic contract for the analytic predicate.
It does not assert the existence of complex derivatives.  It records the
closure properties that a later Mathlib instantiation must prove: identity,
restriction to a smaller domain, and composition on the appropriate
preimage-domain.
-/
structure HolomorphicTheory {M : Type v} (τM : Topology M) where
  isHolomorphicOn : Set M → (M → M) → Prop
  identity : ∀ s, isHolomorphicOn s id
  restrict : ∀ {s t : Set M} {f : M → M},
    isHolomorphicOn s f → Subset t s → isHolomorphicOn t f
  comp : ∀ {s : Set M} {f g : M → M},
    isHolomorphicOn s f →
    isHolomorphicOn (Set.preimage f s) g →
    isHolomorphicOn s (fun x => g (f x))

structure HolomorphicMap {M : Type v} {τM : Topology M}
    (H : HolomorphicTheory τM)
    (s : Set M) where
  toFun : M → M
  isHolomorphic : H.isHolomorphicOn s toFun

instance {M : Type v} {τM : Topology M}
    {H : HolomorphicTheory τM} {s : Set M} :
    CoeFun (HolomorphicMap H s) (fun _ => M → M) :=
  ⟨HolomorphicMap.toFun⟩

namespace HolomorphicMap

def id {M : Type v} {τM : Topology M}
    (H : HolomorphicTheory τM) (s : Set M) : HolomorphicMap H s where
  toFun := fun x => x
  isHolomorphic := H.identity s

def restrict {M : Type v} {τM : Topology M}
    {H : HolomorphicTheory τM} {s t : Set M}
    (f : HolomorphicMap H s) (ht : Subset t s) : HolomorphicMap H t where
  toFun := f.toFun
  isHolomorphic := H.restrict f.isHolomorphic ht

def comp {M : Type v} {τM : Topology M}
    {H : HolomorphicTheory τM} {s : Set M}
    (f : HolomorphicMap H s)
    (g : HolomorphicMap H (Set.preimage f.toFun s)) : HolomorphicMap H s where
  toFun := fun x => g (f x)
  isHolomorphic := H.comp f.isHolomorphic g.isHolomorphic

@[simp] theorem comp_apply {M : Type v} {τM : Topology M}
    {H : HolomorphicTheory τM} {s : Set M}
    (f : HolomorphicMap H s)
    (g : HolomorphicMap H (Set.preimage f.toFun s)) (x : M) :
    comp f g x = g (f x) := rfl

end HolomorphicMap

structure TransitionData {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (i j : LocalChart τS τM)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  map : M → M
  agrees_on_overlap : ∀ z, LocalChart.overlap i j z →
    map z = LocalChart.transitionMap i j z
  holomorphic_on_overlap :
    isHolomorphicOn (LocalChart.overlap i j) map

def TransitionData.asHolomorphicMap
    {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    (H : HolomorphicTheory τM)
    {i j : LocalChart τS τM}
    (d : TransitionData i j H.isHolomorphicOn) :
    HolomorphicMap H (LocalChart.overlap i j) where
  toFun := d.map
  isHolomorphic := d.holomorphic_on_overlap

structure ComplexAtlas {S : Type u} (τS : Topology S)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  index : Type u
  chart : index → LocalChart τS τM
  covers : ∀ x, ∃ i, (chart i).domain x
  transition : ∀ i j, TransitionData (chart i) (chart j) isHolomorphicOn

namespace ComplexAtlas

def chartAt {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (A : ComplexAtlas τS τM isHolomorphicOn)
    (i : A.index) : LocalChart τS τM :=
  A.chart i

theorem has_chart_at {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (A : ComplexAtlas τS τM isHolomorphicOn) (x : S) :
    ∃ i, (A.chart i).domain x :=
  A.covers x

theorem transition_is_explicit {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (A : ComplexAtlas τS τM isHolomorphicOn) (i j : A.index) :
    isHolomorphicOn
      (LocalChart.overlap (A.chart i) (A.chart j))
      (A.transition i j).map :=
  (A.transition i j).holomorphic_on_overlap

end ComplexAtlas

/-- A Riemann-surface-shaped object over an explicit coordinate model. -/
structure AtlasRiemannSurface {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  carrier : Type v
  topology : Topology carrier
  atlas : ComplexAtlas topology τM isHolomorphicOn

/-- A topological marking on an atlas-based surface. -/
structure MarkedAtlasSurface {S : Type u} (τS : Topology S)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  surface : AtlasRiemannSurface τM isHolomorphicOn
  marking : TopologicalEquiv τS surface.topology

/-- The analytic part of an equivalence is kept as named data for now. -/
structure AtlasEquiv {M : Type v} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (X Y : AtlasRiemannSurface τM isHolomorphicOn) where
  underlying : TopologicalEquiv X.topology Y.topology
  chartwise_holomorphic : Prop
  inverse_chartwise_holomorphic : Prop

end Formal
end Teichmuller
