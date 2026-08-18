import Std

namespace Teichmuller
namespace Formal

/-!
This file is the first concrete replacement for the structural `Prop` fields in
`Teichmuller.Core`.  It is intentionally self-contained while the Mathlib
dependency is unavailable in the current checkout:

* `Set` and `Topology` give the usual point-set topology axioms;
* `Continuous` and `ContinuousMap` are actual predicates/structures;
* `Homotopy` uses an explicitly supplied topological parameter with two
  endpoints;
* `HomotopyRelation` is the equivalence closure of direct homotopies;
* `MarkingRelated` says that two markings differ by a topological equivalence
  and a homotopy of the induced maps.

The later Mathlib adapter can identify these interfaces with
`TopologicalSpace`, `Continuous`, `ContinuousMap`, and standard homotopies.
The proofs below do not assert local Euclidean structure, complex charts, or
analytic existence theorems.
-/

universe u v w

/-- A small set-theoretic interface, used until Mathlib supplies `Set`. -/
def Set (X : Type u) := X → Prop

namespace Set

protected def univ : Set X := fun _ => True

protected def empty : Set X := fun _ => False

protected def inter (s t : Set X) : Set X := fun x => s x ∧ t x

protected def union (s t : Set X) : Set X := fun x => s x ∨ t x

protected def iUnion {ι : Type v} (s : ι → Set X) : Set X :=
  fun x => ∃ i, s i x

protected def sUnion (𝒰 : Set (Set X)) : Set X :=
  fun x => ∃ U, 𝒰 U ∧ U x

protected def preimage (f : X → Y) (s : Set Y) : Set X :=
  fun x => s (f x)

theorem ext {s t : Set X} (h : ∀ x, s x ↔ t x) : s = t := by
  funext x
  exact propext (h x)

theorem inter_comm (s t : Set X) : Set.inter s t = Set.inter t s := by
  apply ext
  intro x
  constructor <;> intro h
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩

end Set

/-- The usual subset relation for the local set interface. -/
def Subset (s t : Set X) : Prop := ∀ ⦃x⦄, s x → t x

/-- A topological space presented by its open-set predicate. -/
structure Topology (X : Type u) where
  isOpen : Set X → Prop
  isOpen_univ : isOpen Set.univ
  isOpen_inter : ∀ U V, isOpen U → isOpen V → isOpen (Set.inter U V)
  isOpen_sUnion : ∀ 𝒰 : Set (Set X),
    (∀ U, 𝒰 U → isOpen U) → isOpen (Set.sUnion 𝒰)

namespace Topology

/-!
The product topology is characterized by the existence of an open rectangle
around every point.  This is equivalent to the usual generated-topology
construction and is convenient for proving continuity of projections and
homotopies without any imported set library.
-/
def prod {X : Type u} {Y : Type v} (τX : Topology X) (τY : Topology Y) :
    Topology (X × Y) where
  isOpen U := ∀ p, U p → ∃ A B,
    τX.isOpen A ∧ τY.isOpen B ∧ A p.1 ∧ B p.2 ∧
      (∀ q, A q.1 → B q.2 → U q)
  isOpen_univ := by
    intro p hp
    exact ⟨Set.univ, Set.univ, τX.isOpen_univ, τY.isOpen_univ,
      trivial, trivial, by intro q _ _; trivial⟩
  isOpen_inter := by
    intro U V hU hV p hp
    rcases hU p hp.1 with ⟨A₁, B₁, hA₁, hB₁, hpA₁, hpB₁, hUV₁⟩
    rcases hV p hp.2 with ⟨A₂, B₂, hA₂, hB₂, hpA₂, hpB₂, hUV₂⟩
    refine ⟨Set.inter A₁ A₂, Set.inter B₁ B₂,
      τX.isOpen_inter _ _ hA₁ hA₂, τY.isOpen_inter _ _ hB₁ hB₂,
      ⟨hpA₁, hpA₂⟩, ⟨hpB₁, hpB₂⟩, ?_⟩
    intro q hA hB
    exact ⟨hUV₁ q hA.1 hB.1, hUV₂ q hA.2 hB.2⟩
  isOpen_sUnion := by
    intro 𝒰 h𝒰 p hp
    rcases hp with ⟨U, hU, hpi⟩
    rcases h𝒰 U hU p hpi with ⟨A, B, hA, hB, hpA, hpB, hsub⟩
    exact ⟨A, B, hA, hB, hpA, hpB, by
      intro q hAq hBq
      exact ⟨U, hU, hsub q hAq hBq⟩⟩

/-!
The induced topology is the bridge between the local self-contained layer and
the usual `induced`/subspace constructions.  Its open sets are exactly the
inverse images of open sets in the source topology; this is sufficient here
because inverse images preserve arbitrary unions and finite intersections.
-/
def induced {X : Type u} {Y : Type v}
    (f : Y → X) (τX : Topology X) : Topology Y where
  isOpen U := ∃ V, τX.isOpen V ∧ U = Set.preimage f V
  isOpen_univ := by
    exact ⟨Set.univ, τX.isOpen_univ, by
      apply Set.ext
      intro y
      trivial⟩
  isOpen_inter := by
    intro U V hU hV
    rcases hU with ⟨U', hU', rfl⟩
    rcases hV with ⟨V', hV', rfl⟩
    refine ⟨Set.inter U' V', τX.isOpen_inter _ _ hU' hV', ?_⟩
    apply Set.ext
    intro y
    rfl
  isOpen_sUnion := by
    intro 𝒰 h𝒰
    let 𝒱 : Set (Set X) := fun V =>
      ∃ U, 𝒰 U ∧ τX.isOpen V ∧ U = Set.preimage f V
    refine ⟨Set.sUnion 𝒱, ?_, ?_⟩
    · exact τX.isOpen_sUnion 𝒱 (by
        intro V hV
        rcases hV with ⟨U, hU, hV, hEq⟩
        exact hV)
    · apply Set.ext
      intro y
      constructor
      · intro hy
        rcases hy with ⟨U, hU, hyU⟩
        rcases h𝒰 U hU with ⟨V, hV, hEq⟩
        refine ⟨V, ⟨U, hU, hV, hEq⟩, ?_⟩
        have hEqAt := congrFun hEq y
        have hforward : Set.preimage f V y := hEqAt.mp hyU
        simpa [Set.preimage] using hforward
      · intro hy
        rcases hy with ⟨V, hV, hyV⟩
        rcases hV with ⟨U, hU, hV, hEq⟩
        refine ⟨U, hU, ?_⟩
        have hEqAt := congrFun hEq y
        have hback : Set.preimage f V y := by
          simpa [Set.preimage] using hyV
        exact hEqAt.mpr hback

def subtype {X : Type u} (τX : Topology X) (s : Set X) :
    Topology {x // s x} :=
  induced Subtype.val τX

end Topology

/-- Continuity is expressed by inverse images of open sets. -/
def Continuous {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y) (f : X → Y) : Prop :=
  ∀ U, τY.isOpen U → τX.isOpen (Set.preimage f U)

theorem continuous_induced {X : Type u} {Y : Type v}
    (f : Y → X) (τX : Topology X) :
    Continuous (Topology.induced f τX) τX f := by
  intro U hU
  exact ⟨U, hU, rfl⟩

theorem continuous_to_induced {X : Type u} {Y : Type v} {Z : Type w}
    (f : Y → X) (τX : Topology X) (τZ : Topology Z)
    (g : Z → Y)
    (h : Continuous τZ τX (fun z => f (g z))) :
    Continuous τZ (Topology.induced f τX) g := by
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩
  have hpreimage :
      Set.preimage (fun z => f (g z)) V =
        Set.preimage g (Set.preimage f V) := by
    rfl
  have hopen := h V hV
  rw [hpreimage] at hopen
  exact hopen

theorem continuous_subtype_val {X : Type u} (τX : Topology X) (s : Set X) :
    Continuous (Topology.subtype τX s) τX Subtype.val := by
  exact continuous_induced Subtype.val τX

theorem continuous_id {X : Type u} (τX : Topology X) :
    Continuous τX τX id := by
  intro U hU
  exact hU

theorem continuous_comp
    {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    {f : X → Y} {g : Y → Z}
    (hg : Continuous τY τZ g) (hf : Continuous τX τY f) :
    Continuous τX τZ (fun x => g (f x)) := by
  intro U hU
  exact hf (Set.preimage g U) (hg U hU)

theorem continuous_fst {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y) :
    Continuous (Topology.prod τX τY) τX Prod.fst := by
  intro U hU p hp
  exact ⟨U, Set.univ, hU, τY.isOpen_univ, hp, trivial,
    by intro q hq _; exact hq⟩

theorem continuous_snd {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y) :
    Continuous (Topology.prod τX τY) τY Prod.snd := by
  intro U hU p hp
  exact ⟨Set.univ, U, τX.isOpen_univ, hU, trivial, hp,
    by intro q _ hq; exact hq⟩

theorem continuous_prod_mk {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    {f : Z → X} {g : Z → Y}
    (hf : Continuous τZ τX f) (hg : Continuous τZ τY g) :
    Continuous τZ (Topology.prod τX τY) (fun z => (f z, g z)) := by
  intro U hU
  let 𝒱 : Set (Set Z) := fun V =>
    ∃ A B, τX.isOpen A ∧ τY.isOpen B ∧
      V = Set.inter (Set.preimage f A) (Set.preimage g B) ∧
      (∀ z, V z → U (f z, g z))
  have hEq : Set.preimage (fun z => (f z, g z)) U = Set.sUnion 𝒱 := by
    apply Set.ext
    intro z
    constructor
    · intro hz
      rcases hU (f z, g z) hz with
        ⟨A, B, hA, hB, hzA, hzB, hsub⟩
      refine ⟨Set.inter (Set.preimage f A) (Set.preimage g B), ?_, ?_⟩
      · refine ⟨A, B, hA, hB, rfl, ?_⟩
        intro q hq
        exact hsub (f q, g q) hq.1 hq.2
      · change A (f z) ∧ B (g z)
        exact ⟨hzA, hzB⟩
    · intro hz
      rcases hz with ⟨V, hV, hzV⟩
      rcases hV with ⟨A, B, hA, hB, hVEq, hsub⟩
      exact hsub z hzV
  rw [hEq]
  exact τZ.isOpen_sUnion 𝒱 (by
    intro V hV
    rcases hV with ⟨A, B, hA, hB, hVEq, hsub⟩
    rw [hVEq]
    exact τZ.isOpen_inter _ _ (hf A hA) (hg B hB))

/-- A map bundled with the proof that it is continuous. -/
structure ContinuousMap {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y) where
  toFun : X → Y
  continuous_toFun : Continuous τX τY toFun

instance {X : Type u} {Y : Type v} {τX : Topology X} {τY : Topology Y} :
    CoeFun (ContinuousMap τX τY) (fun _ => X → Y) :=
  ⟨ContinuousMap.toFun⟩

namespace ContinuousMap

def id {X : Type u} (τX : Topology X) : ContinuousMap τX τX where
  toFun := fun x => x
  continuous_toFun := continuous_id τX

def comp {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    (g : ContinuousMap τY τZ) (f : ContinuousMap τX τY) :
    ContinuousMap τX τZ where
  toFun := fun x => g (f x)
  continuous_toFun := continuous_comp g.continuous_toFun f.continuous_toFun

@[simp] theorem comp_apply {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    (g : ContinuousMap τY τZ) (f : ContinuousMap τX τY) (x : X) :
    comp g f x = g (f x) := rfl

end ContinuousMap

/-- A homeomorphism whose two directions are continuous. -/
structure TopologicalEquiv {X : Type u} {Y : Type v}
    (τX : Topology X) (τY : Topology Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : Continuous τX τY toFun
  continuous_invFun : Continuous τY τX invFun

instance {X : Type u} {Y : Type v} {τX : Topology X} {τY : Topology Y} :
    CoeFun (TopologicalEquiv τX τY) (fun _ => X → Y) :=
  ⟨TopologicalEquiv.toFun⟩

namespace TopologicalEquiv

def refl {X : Type u} (τX : Topology X) : TopologicalEquiv τX τX where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := continuous_id τX
  continuous_invFun := continuous_id τX

def symm {X : Type u} {Y : Type v} {τX : Topology X} {τY : Topology Y}
    (e : TopologicalEquiv τX τY) : TopologicalEquiv τY τX where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

def comp {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    (g : TopologicalEquiv τY τZ) (f : TopologicalEquiv τX τY) :
    TopologicalEquiv τX τZ where
  toFun := fun x => g.toFun (f.toFun x)
  invFun := fun z => f.invFun (g.invFun z)
  left_inv := by
    intro x
    rw [g.left_inv, f.left_inv]
  right_inv := by
    intro z
    rw [f.right_inv, g.right_inv]
  continuous_toFun := continuous_comp g.continuous_toFun f.continuous_toFun
  continuous_invFun := continuous_comp f.continuous_invFun g.continuous_invFun

@[simp] theorem comp_apply {X : Type u} {Y : Type v} {Z : Type w}
    {τX : Topology X} {τY : Topology Y} {τZ : Topology Z}
    (g : TopologicalEquiv τY τZ) (f : TopologicalEquiv τX τY) (x : X) :
    comp g f x = g (f x) := rfl

end TopologicalEquiv

/-- A topological parameter with two distinguished endpoints. -/
structure HomotopyParameter where
  carrier : Type u
  topology : Topology carrier
  zero : carrier
  one : carrier

/-- A direct homotopy witness over a supplied parameter. -/
def Homotopy {X : Type v} {Y : Type w}
    (I : HomotopyParameter) (τX : Topology X) (τY : Topology Y)
    (f g : X → Y) : Prop :=
  ∃ H : I.carrier × X → Y,
    Continuous (Topology.prod I.topology τX) τY H ∧
      (∀ x, H (I.zero, x) = f x) ∧
      (∀ x, H (I.one, x) = g x)

/-!
Direct homotopy is the familiar cylinder condition.  Since this file does not
yet import the real unit interval and its reversal/concatenation maps, the
relation used below is its explicit equivalence closure.  This makes the
algebraic facts about marking classes available without hiding interval
analysis inside an axiom.
-/
inductive HomotopyRelation {X : Type v} {Y : Type w}
    (I : HomotopyParameter) (τX : Topology X) (τY : Topology Y) :
    (X → Y) → (X → Y) → Prop
  | refl (f : X → Y) : HomotopyRelation I τX τY f f
  | ofHomotopy {f g : X → Y} :
      Homotopy I τX τY f g → HomotopyRelation I τX τY f g
  | symm {f g : X → Y} :
      HomotopyRelation I τX τY f g → HomotopyRelation I τX τY g f
  | trans {f g h : X → Y} :
      HomotopyRelation I τX τY f g →
      HomotopyRelation I τX τY g h →
      HomotopyRelation I τX τY f h

namespace HomotopyRelation

theorem postcompose {X : Type v} {Y : Type w} {Z : Type u}
    {I : HomotopyParameter} {τX : Topology X} {τY : Topology Y}
    {τZ : Topology Z} {f g : X → Y}
    (h : HomotopyRelation I τX τY f g)
    {k : Y → Z} (hk : Continuous τY τZ k) :
    HomotopyRelation I τX τZ (fun x => k (f x)) (fun x => k (g x)) := by
  induction h with
  | refl f => exact HomotopyRelation.refl (fun x => k (f x))
  | ofHomotopy h =>
      rcases h with ⟨H, hH, hzero, hone⟩
      apply HomotopyRelation.ofHomotopy
      refine ⟨fun p => k (H p), continuous_comp hk hH, ?_, ?_⟩
      · intro x
        simpa using congrArg k (hzero x)
      · intro x
        simpa using congrArg k (hone x)
  | symm h ih => exact HomotopyRelation.symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact HomotopyRelation.trans ih₁ ih₂

end HomotopyRelation

/-- A topological object marked by a fixed reference space. -/
structure MarkedTopologicalObject {S : Type u} (τS : Topology S) where
  carrier : Type v
  topology : Topology carrier
  marking : TopologicalEquiv τS topology

/-- Compatibility of two markings, expressed through isotopy data. -/
def MarkingRelated {S : Type u} {τS : Topology S}
    (I : HomotopyParameter)
    (X Y : MarkedTopologicalObject τS) : Prop :=
  ∃ e : TopologicalEquiv X.topology Y.topology,
    HomotopyRelation I τS Y.topology
      (fun s => e.toFun (X.marking.toFun s)) Y.marking.toFun

theorem markingRelated_refl {S : Type u} {τS : Topology S}
    (I : HomotopyParameter) (X : MarkedTopologicalObject τS) :
    MarkingRelated I X X := by
  refine ⟨TopologicalEquiv.refl X.topology, ?_⟩
  exact HomotopyRelation.refl X.marking.toFun

theorem markingRelated_symm {S : Type u} {τS : Topology S}
    (I : HomotopyParameter) {X Y : MarkedTopologicalObject τS}
    (h : MarkingRelated I X Y) :
    MarkingRelated I Y X := by
  rcases h with ⟨e, h⟩
  refine ⟨e.symm, ?_⟩
  have hpost := HomotopyRelation.postcompose h e.continuous_invFun
  have hs := HomotopyRelation.symm hpost
  simpa [TopologicalEquiv.symm, e.left_inv] using hs

theorem markingRelated_trans {S : Type u} {τS : Topology S}
    (I : HomotopyParameter) {X Y Z : MarkedTopologicalObject τS}
    (hXY : MarkingRelated I X Y) (hYZ : MarkingRelated I Y Z) :
    MarkingRelated I X Z := by
  rcases hXY with ⟨e, hXY⟩
  rcases hYZ with ⟨f, hYZ⟩
  refine ⟨TopologicalEquiv.comp f e, ?_⟩
  have hXY' := HomotopyRelation.postcompose hXY f.continuous_toFun
  exact HomotopyRelation.trans (by
    simpa only [TopologicalEquiv.comp_apply] using hXY') hYZ

def markingSetoid {S : Type u} (τS : Topology S)
    (I : HomotopyParameter) : Setoid (MarkedTopologicalObject τS) where
  r := MarkingRelated I
  iseqv := {
    refl := markingRelated_refl I
    symm := by
      intro X Y h
      exact markingRelated_symm I h
    trans := by
      intro X Y Z hXY hYZ
      exact markingRelated_trans I hXY hYZ
  }

def TeichmullerSpace {S : Type u} (τS : Topology S)
    (I : HomotopyParameter) :=
  Quotient (markingSetoid τS I)

def teichmullerPoint {S : Type u} (τS : Topology S)
    (I : HomotopyParameter) (X : MarkedTopologicalObject τS) :
    TeichmullerSpace τS I :=
  Quotient.mk (markingSetoid τS I) X

theorem teichmullerPoint_eq_of_markingRelated
    {S : Type u} (τS : Topology S)
    (I : HomotopyParameter) (X Y : MarkedTopologicalObject τS)
    (h : MarkingRelated I X Y) :
    teichmullerPoint τS I X = teichmullerPoint τS I Y := by
  exact @Quotient.sound _ (markingSetoid τS I) _ _ h

end Formal
end Teichmuller
