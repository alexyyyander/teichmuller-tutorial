import Teichmuller.MathlibFiberBundle

namespace Teichmuller
namespace MathlibFormal

universe u w v t

/-!
  Čech descent data for local holomorphic marked families.

  The local families live over the actual subtype bases `cover i`.  On an
  overlap, the transition is recorded pointwise as a genuine biholomorphic
  homeomorphism between the corresponding marked fibres.  This keeps the
  first descent layer concrete: no existence proposition is used for the
  transition maps, and the triple-overlap equation is an equality of actual
  homeomorphisms.
-/

def CechOverlap {B : Type w} (cover : v → Set B) (i j : v) :=
  cover i ∩ cover j

def CechTripleOverlap {B : Type w} (cover : v → Set B) (i j k : v) :=
  (cover i ∩ cover j) ∩ cover k

def CechOverlap.leftPoint
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) : cover i :=
  ⟨x.1, x.2.1⟩

def CechOverlap.rightPoint
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) : cover j :=
  ⟨x.1, x.2.2⟩

def cechOverlapSwap
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) : CechOverlap cover j i :=
  ⟨x.1, ⟨x.2.2, x.2.1⟩⟩

theorem cechOverlapSwap_leftPoint
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) :
    CechOverlap.leftPoint cover j i (cechOverlapSwap cover i j x) =
      CechOverlap.rightPoint cover i j x := by
  rfl

theorem cechOverlapSwap_rightPoint
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) :
    CechOverlap.rightPoint cover j i (cechOverlapSwap cover i j x) =
      CechOverlap.leftPoint cover i j x := by
  rfl

noncomputable def cechOverlapSwapHomeomorph
    {B : Type w} [TopologicalSpace B]
    (cover : v → Set B) (i j : v) :
    @Homeomorph
      (CechOverlap cover i j) (CechOverlap cover j i)
      inferInstance inferInstance := by
  exact
    { toFun := cechOverlapSwap cover i j
      invFun := cechOverlapSwap cover j i
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val }

def CechTripleOverlap.toIJ
    {B : Type w} (cover : v → Set B) (i j k : v)
    (x : CechTripleOverlap cover i j k) : CechOverlap cover i j :=
  ⟨x.1, x.2.1⟩

def CechTripleOverlap.toJK
    {B : Type w} (cover : v → Set B) (i j k : v)
    (x : CechTripleOverlap cover i j k) : CechOverlap cover j k :=
  ⟨x.1, ⟨x.2.1.2, x.2.2⟩⟩

def CechTripleOverlap.toIK
    {B : Type w} (cover : v → Set B) (i j k : v)
    (x : CechTripleOverlap cover i j k) : CechOverlap cover i k :=
  ⟨x.1, ⟨x.2.1.1, x.2.2⟩⟩

def CechTripleOverlap.selfRight
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) : CechTripleOverlap cover i j i :=
  ⟨x.1, ⟨x.2, x.2.1⟩⟩

theorem CechTripleOverlap.selfRight_toIJ
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) :
    CechTripleOverlap.toIJ cover i j i
      (CechTripleOverlap.selfRight cover i j x) = x := by
  rfl

theorem CechTripleOverlap.selfRight_toJK
    {B : Type w} (cover : v → Set B) (i j : v)
    (x : CechOverlap cover i j) :
    CechTripleOverlap.toJK cover i j i
      (CechTripleOverlap.selfRight cover i j x) =
      cechOverlapSwap cover i j x := by
  rfl

theorem CechTripleOverlap.middlePoint_eq
    {B : Type w} (cover : v → Set B) (i j k : v)
    (x : CechTripleOverlap cover i j k) :
  CechOverlap.rightPoint cover i j
        (CechTripleOverlap.toIJ cover i j k x) =
      CechOverlap.leftPoint cover j k
        (CechTripleOverlap.toJK cover i j k x) := by
  apply Subtype.ext
  change x.1 = x.1
  rfl

structure HolomorphicCechDescentData
    (S : Type u) (B : Type w) (I : Type v)
    [TopologicalSpace S] [TopologicalSpace B] where
  cover : I → Set B
  cover_open : ∀ i, IsOpen (cover i)
  cover_univ : ⋃ i, cover i = Set.univ
  localFamily : ∀ i,
    ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, t}
      (S := S) (B := cover i)
  transition : ∀ (i j : I) (x : CechOverlap cover i j),
    @Homeomorph
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).carrier
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).carrier
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).topology
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).topology
  transition_holomorphic : ∀ (i j : I)
    (x : CechOverlap cover i j),
    letI : TopologicalSpace
        ((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i j x)).carrier :=
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).topology
    letI : TopologicalSpace
        ((localFamily j).family.fiber
          (CechOverlap.rightPoint cover i j x)).carrier :=
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).topology
    @AtlasHolomorphicEquiv
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).carrier
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).carrier
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).topology
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).topology
      ((localFamily i).family.fiber
        (CechOverlap.leftPoint cover i j x)).surface.atlas
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).surface.atlas
      (transition i j x)
  transition_marking_commutes : ∀ (i j : I)
    (x : CechOverlap cover i j) (s : S),
    transition i j x
        (((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i j x)).marking s) =
      ((localFamily j).family.fiber
        (CechOverlap.rightPoint cover i j x)).marking s
  transition_self : ∀ (i : I) (x : CechOverlap cover i i),
    transition i i x =
      @Homeomorph.refl
        ((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i i x)).carrier
        ((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i i x)).topology
  transition_comp : ∀ (i j k : I)
    (x : CechTripleOverlap cover i j k),
    transition i k (CechTripleOverlap.toIK cover i j k x) =
      @Homeomorph.trans
        ((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i j
            (CechTripleOverlap.toIJ cover i j k x))).carrier
        ((localFamily j).family.fiber
          (CechOverlap.rightPoint cover i j
            (CechTripleOverlap.toIJ cover i j k x))).carrier
        ((localFamily k).family.fiber
          (CechOverlap.rightPoint cover j k
            (CechTripleOverlap.toJK cover i j k x))).carrier
        ((localFamily i).family.fiber
          (CechOverlap.leftPoint cover i j
            (CechTripleOverlap.toIJ cover i j k x))).topology
        ((localFamily j).family.fiber
          (CechOverlap.rightPoint cover i j
            (CechTripleOverlap.toIJ cover i j k x))).topology
        ((localFamily k).family.fiber
          (CechOverlap.rightPoint cover j k
            (CechTripleOverlap.toJK cover i j k x))).topology
        (transition i j (CechTripleOverlap.toIJ cover i j k x))
        (by
          rw [CechTripleOverlap.middlePoint_eq cover i j k x]
          exact transition j k (CechTripleOverlap.toJK cover i j k x))

namespace HolomorphicCechDescentData

theorem transition_self_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i : I) (x : CechOverlap D.cover i i) (s : S) :
    D.transition i i x
        (((D.localFamily i).family.fiber
          (CechOverlap.leftPoint D.cover i i x)).marking s) =
      ((D.localFamily i).family.fiber
        (CechOverlap.rightPoint D.cover i i x)).marking s := by
  exact D.transition_marking_commutes i i x s

theorem transition_comp_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i j k : I) (x : CechTripleOverlap D.cover i j k)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j
        (CechTripleOverlap.toIJ D.cover i j k x))).carrier) :
    D.transition i k (CechTripleOverlap.toIK D.cover i j k x) z =
      D.transition j k (CechTripleOverlap.toJK D.cover i j k x)
        (D.transition i j (CechTripleOverlap.toIJ D.cover i j k x) z) := by
  rw [D.transition_comp i j k x]
  rfl

theorem transition_inverse_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (x : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j x)).carrier) :
    D.transition j i (cechOverlapSwap D.cover i j x)
        (D.transition i j x z) = z := by
  have hcomp := D.transition_comp_apply i j i
    (CechTripleOverlap.selfRight D.cover i j x) z
  have hself := D.transition_self i
    (CechTripleOverlap.toIK D.cover i j i
      (CechTripleOverlap.selfRight D.cover i j x))
  have hcomp' :
      D.transition i i (CechTripleOverlap.toIK D.cover i j i
        (CechTripleOverlap.selfRight D.cover i j x)) z =
        D.transition j i (cechOverlapSwap D.cover i j x)
          (D.transition i j x z) := by
    convert hcomp using 1
  have hself_apply :
      D.transition i i (CechTripleOverlap.toIK D.cover i j i
        (CechTripleOverlap.selfRight D.cover i j x)) z = z := by
    rw [hself]
    rfl
  exact hcomp'.symm.trans hself_apply

end HolomorphicCechDescentData

end MathlibFormal
end Teichmuller
