import Mathlib.Topology.Homotopy.Basic
import Teichmuller.Topology

namespace Teichmuller
namespace MathlibFormal

/-!
This file is the Mathlib realization of the topological part of the program.

The earlier `Teichmuller.Formal` layer deliberately supplied its own small
topology and a closure-generated homotopy relation.  Here we use Mathlib's
actual `TopologicalSpace`, `Homeomorph`, `ContinuousMap`, and the standard
unit interval `unitInterval.I`.  In particular, `ContinuousMap.Homotopic` is
already an equivalence relation because Mathlib contains the reversal and
concatenation constructions for homotopies.

The carrier of a marked object is allowed to vary.  Its topology is stored as
data rather than installed globally as an instance; the definitions below use
explicit topology arguments so that two fibres with different carriers can be
handled without ambiguity.
-/

universe u v

/-- A topological object equipped with a marking from a fixed reference space. -/
structure MarkedTopologicalObject (S : Type u) [TopologicalSpace S] where
  carrier : Type v
  topology : TopologicalSpace carrier
  marking : @Homeomorph S carrier inferInstance topology

namespace MarkedTopologicalObject

/-- The marking as a Mathlib continuous map. -/
def markingMap {S : Type u} [TopologicalSpace S]
    (X : MarkedTopologicalObject S) :
    @ContinuousMap S X.carrier inferInstance X.topology := by
  letI : TopologicalSpace X.carrier := X.topology
  exact {
    toFun := X.marking
    continuous_toFun := X.marking.continuous_toFun
  }

/-- A homeomorphism, regarded as a continuous map, with all topologies explicit. -/
def homeomorphMap {S : Type u} [TopologicalSpace S]
    {X Y : MarkedTopologicalObject S}
    (e : @Homeomorph X.carrier Y.carrier X.topology Y.topology) :
    @ContinuousMap X.carrier Y.carrier X.topology Y.topology := by
  letI : TopologicalSpace X.carrier := X.topology
  letI : TopologicalSpace Y.carrier := Y.topology
  exact {
    toFun := e
    continuous_toFun := e.continuous_toFun
  }

theorem markingMap_apply {S : Type u} [TopologicalSpace S]
    (X : MarkedTopologicalObject S) (s : S) :
    markingMap X s = X.marking s :=
  by
    change X.marking s = X.marking s
    rfl

theorem homeomorphMap_apply {S : Type u} [TopologicalSpace S]
    {X Y : MarkedTopologicalObject S}
    (e : @Homeomorph X.carrier Y.carrier X.topology Y.topology) (x : X.carrier) :
    homeomorphMap e x = e x :=
  by
    change e x = e x
    rfl

end MarkedTopologicalObject

/-!
Two markings are related when a homeomorphism of the carriers makes the
induced maps from the reference space homotopic.  This is the Mathlib form of

  e ∘ m_X ≃ m_Y.

The standard interval is built into `ContinuousMap.Homotopy`, so the relation
now uses the actual unit interval rather than an abstract parameter with two
distinguished points.
-/
def MarkingRelated {S : Type u} [TopologicalSpace S]
    (X Y : MarkedTopologicalObject S) : Prop :=
  letI : TopologicalSpace X.carrier := X.topology
  letI : TopologicalSpace Y.carrier := Y.topology
  ∃ e : X.carrier ≃ₜ Y.carrier,
    ContinuousMap.Homotopic
      ((MarkedTopologicalObject.homeomorphMap e).comp
        (MarkedTopologicalObject.markingMap X))
      (MarkedTopologicalObject.markingMap Y)

theorem markingRelated_refl {S : Type u} [TopologicalSpace S]
    (X : MarkedTopologicalObject S) : MarkingRelated X X := by
  letI : TopologicalSpace X.carrier := X.topology
  let e : @Homeomorph X.carrier X.carrier X.topology X.topology :=
    @Homeomorph.refl X.carrier X.topology
  refine ⟨e, ?_⟩
  have hmap :
      (MarkedTopologicalObject.homeomorphMap e).comp
        (MarkedTopologicalObject.markingMap X) =
        MarkedTopologicalObject.markingMap X := by
    ext s
    rfl
  rw [hmap]

theorem markingRelated_symm {S : Type u} [TopologicalSpace S]
    {X Y : MarkedTopologicalObject S} (h : MarkingRelated X Y) :
    MarkingRelated Y X := by
  letI : TopologicalSpace X.carrier := X.topology
  letI : TopologicalSpace Y.carrier := Y.topology
  rcases h with ⟨e, h⟩
  let eInv : @Homeomorph Y.carrier X.carrier Y.topology X.topology := e.symm
  refine ⟨eInv, ?_⟩
  let eInvMap := MarkedTopologicalObject.homeomorphMap eInv
  have hpost :
      ContinuousMap.Homotopic
        (eInvMap.comp
          ((MarkedTopologicalObject.homeomorphMap e).comp
            (MarkedTopologicalObject.markingMap X)))
        (eInvMap.comp (MarkedTopologicalObject.markingMap Y)) :=
    ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl eInvMap) h
  have hreverse := hpost.symm
  have hcancel :
      eInvMap.comp
          ((MarkedTopologicalObject.homeomorphMap e).comp
            (MarkedTopologicalObject.markingMap X)) =
        MarkedTopologicalObject.markingMap X := by
    ext s
    exact e.left_inv _
  rw [hcancel] at hreverse
  exact hreverse

theorem markingRelated_trans {S : Type u} [TopologicalSpace S]
    {X Y Z : MarkedTopologicalObject S}
    (hXY : MarkingRelated X Y) (hYZ : MarkingRelated Y Z) :
    MarkingRelated X Z := by
  letI : TopologicalSpace X.carrier := X.topology
  letI : TopologicalSpace Y.carrier := Y.topology
  letI : TopologicalSpace Z.carrier := Z.topology
  rcases hXY with ⟨e, hXY⟩
  rcases hYZ with ⟨f, hYZ⟩
  let ef : @Homeomorph X.carrier Z.carrier X.topology Z.topology := e.trans f
  refine ⟨ef, ?_⟩
  let fMap := MarkedTopologicalObject.homeomorphMap f
  have hpost :
      ContinuousMap.Homotopic
        (fMap.comp
          ((MarkedTopologicalObject.homeomorphMap e).comp
            (MarkedTopologicalObject.markingMap X)))
        (fMap.comp (MarkedTopologicalObject.markingMap Y)) :=
    ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl fMap) hXY
  have hchain := hpost.trans hYZ
  have hcompose :
      (MarkedTopologicalObject.homeomorphMap ef).comp
          (MarkedTopologicalObject.markingMap X) =
        fMap.comp
          ((MarkedTopologicalObject.homeomorphMap e).comp
            (MarkedTopologicalObject.markingMap X)) := by
    ext s
    rfl
  rw [hcompose]
  exact hchain

/-- The Mathlib setoid of marked topological objects. -/
def markingSetoid {S : Type u} [TopologicalSpace S] :
    Setoid (MarkedTopologicalObject S) where
  r := MarkingRelated
  iseqv := {
    refl := markingRelated_refl
    symm := by
      intro X Y h
      exact markingRelated_symm h
    trans := by
      intro X Y Z hXY hYZ
      exact markingRelated_trans hXY hYZ
  }

/-- The Mathlib-backed topological quotient underlying the Teichmüller space. -/
def TeichmullerSpace {S : Type u} [TopologicalSpace S] :=
  Quotient (markingSetoid (S := S) : Setoid (MarkedTopologicalObject S))

def teichmullerPoint {S : Type u} [TopologicalSpace S]
    (X : MarkedTopologicalObject S) : TeichmullerSpace (S := S) :=
  Quotient.mk (markingSetoid (S := S)) X

theorem teichmullerPoint_eq_of_markingRelated
    {S : Type u} [TopologicalSpace S]
    (X Y : MarkedTopologicalObject S) (h : MarkingRelated X Y) :
    teichmullerPoint X = teichmullerPoint Y := by
  exact @Quotient.sound _ (markingSetoid (S := S)) _ _ h

end MathlibFormal
end Teichmuller
