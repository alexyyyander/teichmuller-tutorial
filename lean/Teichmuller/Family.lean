import Teichmuller.Complex

namespace Teichmuller
namespace Formal

/-!
The third layer packages a varying collection of atlas-based surfaces over a
topological base.  The total space is represented by the dependent sum of the
fibres, so the fibre at a point is an actual type rather than an abstract
`Prop`.  A topology on the total space is supplied as data; this keeps the
construction honest while the generated-topology and analytic-local-triviality
machinery is still outside the self-contained core.
-/

universe u v w

structure SurfaceFamily {B : Type u} (τB : Topology B)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  fiber : B → AtlasRiemannSurface τM isHolomorphicOn
  totalTopology : Topology (Sigma fun b => (fiber b).carrier)
  projection_continuous :
    Continuous totalTopology τB (fun z => z.1)
  analyticVariation : Prop

namespace SurfaceFamily

def Total {B : Type u} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn) : Type (max u v) :=
  Sigma fun b => (F.fiber b).carrier

def projection {B : Type u} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn) : Total F → B :=
  fun z => z.1

theorem projection_continuous_of_family {B : Type u} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn) :
    Continuous F.totalTopology τB F.projection :=
  F.projection_continuous

theorem projection_fiber {B : Type u} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn) (b : B)
    (x : (F.fiber b).carrier) :
    F.projection ⟨b, x⟩ = b :=
  rfl

structure MarkedSurfaceFamily {S : Type u} (τS : Topology S)
    {B : Type w} (τB : Topology B)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  family : SurfaceFamily τB τM isHolomorphicOn
  marking : ∀ b, TopologicalEquiv τS (family.fiber b).topology

def pullback {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τC : Topology C} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B)
    (_hf : Continuous τC τB f)
    (τP : Topology (Sigma fun c => (F.fiber (f c)).carrier))
    (hP : Continuous τP τC (fun z => z.1)) :
    SurfaceFamily τC τM isHolomorphicOn where
  fiber := fun c => F.fiber (f c)
  totalTopology := τP
  projection_continuous := hP
  analyticVariation := F.analyticVariation

theorem pullback_fiber {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τC : Topology C} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B)
    (hf : Continuous τC τB f)
    (τP : Topology (Sigma fun c => (F.fiber (f c)).carrier))
    (hP : Continuous τP τC (fun z => z.1)) (c : C) :
    (pullback F f hf τP hP).fiber c = F.fiber (f c) :=
  rfl

/-!
The canonical pullback topology is induced by the map sending
`(c, x)` to `(c, (f c, x))` in the product of the new base with the old total
space.  This gives a concrete topology on the dependent-sum pullback and
makes its projection continuous by composition with the first projection.
-/
def pullbackMap {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) :
    (Sigma fun c => (F.fiber (f c)).carrier) → C × F.Total :=
  fun z => (z.1, ⟨f z.1, z.2⟩)

def pullbackTopology {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (τC : Topology C)
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) :
    Topology (Sigma fun c => (F.fiber (f c)).carrier) :=
  Topology.induced (pullbackMap F f)
    (Topology.prod τC F.totalTopology)

theorem pullback_projection_continuous {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (τC : Topology C)
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) :
    Continuous (pullbackTopology τC F f) τC
      (fun z : Sigma fun c => (F.fiber (f c)).carrier => z.1) := by
  have hmap := continuous_induced (pullbackMap F f)
    (Topology.prod τC F.totalTopology)
  have hfst := continuous_fst τC F.totalTopology
  have hcomp := continuous_comp hfst hmap
  simpa [pullbackTopology, pullbackMap, Total] using hcomp

def canonicalPullback {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (τC : Topology C)
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) : SurfaceFamily τC τM isHolomorphicOn where
  fiber := fun c => F.fiber (f c)
  totalTopology := pullbackTopology τC F f
  projection_continuous := pullback_projection_continuous τC F f
  analyticVariation := F.analyticVariation

theorem canonicalPullback_fiber {B : Type u} {C : Type w} {M : Type v}
    {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (τC : Topology C)
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) (c : C) :
    (canonicalPullback τC F f).fiber c = F.fiber (f c) :=
  rfl

/-!
Pullback is functorial at the topological level.  The two total spaces for
pulling back first along `f` and then along `g`, or directly along `f ∘ g`,
are definitionally the same dependent sum; the induced topologies need not be
definitionally equal.  The identity therefore becomes a genuine
`TopologicalEquiv`.  The only hypothesis needed is continuity of the second
map, which is exactly what is required to transport the first induced
topology into the iterated one.
-/
def canonicalPullback_comp_equiv {B : Type u} {C : Type w} {D : Type w}
    {M : Type v}
    {τB : Topology B} {τC : Topology C} {τD : Topology D} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily τB τM isHolomorphicOn)
    (f : C → B) (g : D → C)
    (hg : Continuous τD τC g) :
    TopologicalEquiv
      (pullbackTopology τD F (fun d => f (g d)))
      (pullbackTopology τD (canonicalPullback τC F f) g) := by
  have hdirect :
      Continuous (pullbackTopology τD F (fun d => f (g d)))
        (Topology.prod τD F.totalTopology)
        (pullbackMap F (fun d => f (g d))) :=
    continuous_induced (pullbackMap F (fun d => f (g d)))
      (Topology.prod τD F.totalTopology)
  have hdirect_fst :
      Continuous (pullbackTopology τD F (fun d => f (g d))) τD
        (fun z => z.1) := by
    have h := continuous_comp (continuous_fst τD F.totalTopology) hdirect
    simpa [pullbackMap] using h
  have hdirect_snd :
      Continuous (pullbackTopology τD F (fun d => f (g d))) F.totalTopology
        (fun z => (⟨f (g z.1), z.2⟩ : F.Total)) := by
    have h := continuous_comp (continuous_snd τD F.totalTopology) hdirect
    simpa [pullbackMap, Total] using h
  have h_to_intermediate :
      Continuous (pullbackTopology τD F (fun d => f (g d)))
        (pullbackTopology τC F f)
        (fun z => ⟨g z.1, z.2⟩) := by
    apply continuous_to_induced (pullbackMap F f)
      (Topology.prod τC F.totalTopology)
    have hpair := continuous_prod_mk (continuous_comp hg hdirect_fst) hdirect_snd
    change Continuous (pullbackTopology τD F (fun d => f (g d)))
      (Topology.prod τC F.totalTopology)
      (fun z => (g z.1, (⟨f (g z.1), z.2⟩ : F.Total)))
    exact hpair
  have hiter_map :
      Continuous (pullbackTopology τD F (fun d => f (g d)))
        (Topology.prod τD (canonicalPullback τC F f).totalTopology)
        (pullbackMap (canonicalPullback τC F f) g) := by
    have hpair := continuous_prod_mk hdirect_fst h_to_intermediate
    change Continuous (pullbackTopology τD F (fun d => f (g d)))
      (Topology.prod τD (pullbackTopology τC F f))
      (fun z => (z.1, (⟨g z.1, z.2⟩ :
        Sigma fun c => (F.fiber (f c)).carrier)))
    exact hpair
  have hforward :
      Continuous (pullbackTopology τD F (fun d => f (g d)))
        (pullbackTopology τD (canonicalPullback τC F f) g)
        (fun z => z) := by
    apply continuous_to_induced
      (pullbackMap (canonicalPullback τC F f) g)
      (Topology.prod τD (canonicalPullback τC F f).totalTopology)
    exact hiter_map
  have hiter :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g)
        (Topology.prod τD (canonicalPullback τC F f).totalTopology)
        (pullbackMap (canonicalPullback τC F f) g) :=
    continuous_induced (pullbackMap (canonicalPullback τC F f) g)
      (Topology.prod τD (canonicalPullback τC F f).totalTopology)
  have hiter_fst :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g) τD
        (fun z => z.1) := by
    have h := continuous_comp
      (continuous_fst τD (canonicalPullback τC F f).totalTopology) hiter
    simpa [pullbackMap] using h
  have hintermediate_to_total :
      Continuous (pullbackTopology τC F f) F.totalTopology
        (fun z => (⟨f z.1, z.2⟩ : F.Total)) := by
    have hqf := continuous_induced (pullbackMap F f)
      (Topology.prod τC F.totalTopology)
    have h := continuous_comp (continuous_snd τC F.totalTopology) hqf
    simpa [pullbackTopology, pullbackMap, Total] using h
  have hiter_to_intermediate :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g)
        (pullbackTopology τC F f)
        (fun z => ⟨g z.1, z.2⟩) := by
    have h := continuous_comp
      (continuous_snd τD (canonicalPullback τC F f).totalTopology) hiter
    simpa [pullbackMap, canonicalPullback] using h
  have hiter_snd :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g)
        F.totalTopology
        (fun z => (⟨f (g z.1), z.2⟩ : F.Total)) := by
    have h := continuous_comp hintermediate_to_total hiter_to_intermediate
    simpa [canonicalPullback] using h
  have hdirect_again :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g)
        (Topology.prod τD F.totalTopology)
        (pullbackMap F (fun d => f (g d))) := by
    apply continuous_prod_mk hiter_fst hiter_snd
  have hreverse :
      Continuous (pullbackTopology τD (canonicalPullback τC F f) g)
        (pullbackTopology τD F (fun d => f (g d)))
        (fun z => z) := by
    apply continuous_to_induced (pullbackMap F (fun d => f (g d)))
      (Topology.prod τD F.totalTopology)
    exact hdirect_again
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      continuous_toFun := hforward
      continuous_invFun := hreverse }

def markedPullback {S : Type u} {B : Type w} {C : Type w} {M : Type v}
    {τS : Topology S} {τB : Topology B} {τC : Topology C}
    {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : MarkedSurfaceFamily τS τB τM isHolomorphicOn)
    (f : C → B)
    (hf : Continuous τC τB f)
    (τP : Topology (Sigma fun c => (F.family.fiber (f c)).carrier))
    (hP : Continuous τP τC (fun z => z.1)) :
    MarkedSurfaceFamily τS τC τM isHolomorphicOn :=
  { family := pullback F.family f hf τP hP
    marking := fun c => F.marking (f c) }

def canonicalMarkedPullback {S : Type u} {B : Type w} {C : Type w} {M : Type v}
    {τS : Topology S} {τB : Topology B}
    {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (τC : Topology C)
    (F : MarkedSurfaceFamily τS τB τM isHolomorphicOn)
    (f : C → B) :
    MarkedSurfaceFamily τS τC τM isHolomorphicOn :=
  { family := canonicalPullback τC F.family f
    marking := fun c => F.marking (f c) }

end SurfaceFamily

/-!
An equivalence of marked families is explicit fibrewise data.  The marking
compatibility equation is the concrete replacement for a bare equivalence
proposition in the universal-family layer.
-/
structure FiberwiseEquiv {S : Type u} (τS : Topology S)
    {B : Type w} (τB : Topology B)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop)
    (F G : SurfaceFamily.MarkedSurfaceFamily τS τB τM isHolomorphicOn) where
  map : ∀ b, TopologicalEquiv (F.family.fiber b).topology (G.family.fiber b).topology
  marking_commutes : ∀ (b : B) (s : S),
    (map b).toFun ((F.marking b).toFun s) = (G.marking b).toFun s

namespace FiberwiseEquiv

def refl {S : Type u} {B : Type w} {M : Type v}
    {τS : Topology S} {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (F : SurfaceFamily.MarkedSurfaceFamily τS τB τM isHolomorphicOn) :
    FiberwiseEquiv τS τB τM isHolomorphicOn F F where
  map := fun b => TopologicalEquiv.refl (F.family.fiber b).topology
  marking_commutes := by
    intro b s
    rfl

def symm {S : Type u} {B : Type w} {M : Type v}
    {τS : Topology S} {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    {F G : SurfaceFamily.MarkedSurfaceFamily τS τB τM isHolomorphicOn}
    (e : FiberwiseEquiv τS τB τM isHolomorphicOn F G) :
    FiberwiseEquiv τS τB τM isHolomorphicOn G F where
  map := fun b => (e.map b).symm
  marking_commutes := by
    intro b s
    change (e.map b).invFun ((G.marking b).toFun s) = (F.marking b).toFun s
    calc
      (e.map b).invFun ((G.marking b).toFun s) =
          (e.map b).invFun ((e.map b).toFun ((F.marking b).toFun s)) := by
        rw [e.marking_commutes b s]
      _ = (F.marking b).toFun s := (e.map b).left_inv _

def comp {S : Type u} {B : Type w} {M : Type v}
    {τS : Topology S} {τB : Topology B} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    {F G H : SurfaceFamily.MarkedSurfaceFamily τS τB τM isHolomorphicOn}
    (eFG : FiberwiseEquiv τS τB τM isHolomorphicOn F G)
    (eGH : FiberwiseEquiv τS τB τM isHolomorphicOn G H) :
    FiberwiseEquiv τS τB τM isHolomorphicOn F H where
  map := fun b => TopologicalEquiv.comp (eGH.map b) (eFG.map b)
  marking_commutes := by
    intro b s
    rw [TopologicalEquiv.comp_apply]
    rw [eFG.marking_commutes, eGH.marking_commutes]

end FiberwiseEquiv

/-!
`FamilyClassification` is an explicit universal-property witness for one test
family.  It contains the classifying map, its continuity, and a fibrewise
equivalence with the canonical induced-topology pullback of the universal
family.
-/
structure FamilyClassification {S : Type u} (τS : Topology S)
    {B : Type w} (τB : Topology B)
    {C : Type w} (τC : Topology C)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop)
    (U : SurfaceFamily.MarkedSurfaceFamily τS τB τM isHolomorphicOn)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) where
  map : C → B
  map_continuous : Continuous τC τB map
  realization :
    FiberwiseEquiv τS τC τM isHolomorphicOn F
      (SurfaceFamily.canonicalMarkedPullback τC U map)

structure UniversalMarkedFamily {S : Type u} (τS : Topology S)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  base : Type w
  baseTopology : Topology base
  family : SurfaceFamily.MarkedSurfaceFamily τS baseTopology τM isHolomorphicOn
  classifying :
    ∀ {C : Type w} (τC : Topology C),
      (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) →
      FamilyClassification τS baseTopology τC τM isHolomorphicOn family F

namespace UniversalMarkedFamily

def classify {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (U : UniversalMarkedFamily τS τM isHolomorphicOn)
    {C : Type w} (τC : Topology C)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) : C → U.base :=
  (U.classifying τC F).map

def classification {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (U : UniversalMarkedFamily τS τM isHolomorphicOn)
    {C : Type w} (τC : Topology C)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) :
    FamilyClassification τS U.baseTopology τC τM isHolomorphicOn U.family F :=
  U.classifying τC F

theorem classify_continuous {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (U : UniversalMarkedFamily τS τM isHolomorphicOn)
    {C : Type w} (τC : Topology C)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) :
    Continuous τC U.baseTopology (U.classify τC F) :=
  (U.classifying τC F).map_continuous

end UniversalMarkedFamily

/-!
`UniversalMarkedFamily` records existence of a classification witness.  The
fine-moduli strengthening below separates the additional uniqueness claim
from that existence data.  This is deliberately a new structure: the current
self-contained layer should not pretend that uniqueness follows merely from
having a continuous projection and fibrewise topological equivalences.
-/
structure FineUniversalMarkedFamily {S : Type u} (τS : Topology S)
    {M : Type v} (τM : Topology M)
    (isHolomorphicOn : Set M → (M → M) → Prop) where
  universal : UniversalMarkedFamily τS τM isHolomorphicOn
  classification_unique :
    ∀ {C : Type w} (τC : Topology C)
      (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn)
      (c₁ c₂ : FamilyClassification τS universal.baseTopology τC τM
        isHolomorphicOn universal.family F),
      c₁.map = c₂.map

namespace FineUniversalMarkedFamily

def classify {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (U : FineUniversalMarkedFamily τS τM isHolomorphicOn)
    {C : Type w} (τC : Topology C)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn) :
      C → U.universal.base :=
  U.universal.classify τC F

theorem classify_unique {S : Type u} {M : Type v}
    {τS : Topology S} {τM : Topology M}
    {isHolomorphicOn : Set M → (M → M) → Prop}
    (U : FineUniversalMarkedFamily τS τM isHolomorphicOn)
    {C : Type w} (τC : Topology C)
    (F : SurfaceFamily.MarkedSurfaceFamily τS τC τM isHolomorphicOn)
    (c₁ c₂ : FamilyClassification τS U.universal.baseTopology τC τM
      isHolomorphicOn U.universal.family F) :
    c₁.map = c₂.map :=
  U.classification_unique τC F c₁ c₂

end FineUniversalMarkedFamily

end Formal
end Teichmuller
