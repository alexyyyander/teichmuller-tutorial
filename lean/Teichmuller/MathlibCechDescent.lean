import Teichmuller.MathlibCech

namespace Teichmuller
namespace MathlibFormal

universe u w v

/-!
  The first quotient layer of Čech descent.

  `HolomorphicCechDescentData` stores local total spaces over the subtype
  bases `cover i`.  The definitions below form their disjoint union, record
  the elementary gluing steps induced by the overlap homeomorphisms, and take
  the equivalence closure of those steps.  This is deliberately the first
  quotient skeleton: it already has a well-defined descended base projection,
  while the descended atlas and marking are constructed in the next layer.
-/

namespace HolomorphicCechDescentData

def retopologizeSourceHomeomorph
    {X Y : Type*}
    {topologyX topologyX' : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY)
    (heq : topologyX = topologyX') :
    @Homeomorph X Y topologyX' topologyY := by
  cases heq
  exact h

@[simp] theorem retopologizeSourceHomeomorph_apply
    {X Y : Type*}
    {topologyX topologyX' : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY)
    (heq : topologyX = topologyX') (x : X) :
    retopologizeSourceHomeomorph h heq x = h x := by
  cases heq
  rfl

def retopologizeBothHomeomorph
    {X Y : Type*}
    {topologyX topologyX' : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY)
    (heqX : topologyX = topologyX')
    (heqY : topologyY = topologyY') :
    @Homeomorph X Y topologyX' topologyY' := by
  cases heqX
  cases heqY
  exact h

@[simp] theorem retopologizeBothHomeomorph_apply
    {X Y : Type*}
    {topologyX topologyX' : TopologicalSpace X}
    {topologyY topologyY' : TopologicalSpace Y}
    (h : @Homeomorph X Y topologyX topologyY)
    (heqX : topologyX = topologyX')
    (heqY : topologyY = topologyY') (x : X) :
    retopologizeBothHomeomorph h heqX heqY x = h x := by
  cases heqX
  cases heqY
  rfl

abbrev LocalTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :=
  Sigma fun i =>
    ComplexSurfaceFamily.Total (D.localFamily i).family

def localTotalTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    TopologicalSpace (LocalTotal D) := by
  letI : ∀ i, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    fun i => (D.localFamily i).family.totalTopology
  exact inferInstance

instance instLocalTotalTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    TopologicalSpace (LocalTotal D) :=
  localTotalTopology D

def localBase
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) : LocalTotal D → B :=
  fun z => (ComplexSurfaceFamily.projection
    (D.localFamily z.1).family z.2 : D.cover z.1) 

def gluingSource
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (x : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j x)).carrier) : LocalTotal D :=
  ⟨i, ⟨CechOverlap.leftPoint D.cover i j x, z⟩⟩

def gluingTarget
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (x : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j x)).carrier) : LocalTotal D :=
  ⟨j, ⟨CechOverlap.rightPoint D.cover i j x,
    D.transition i j x z⟩⟩

def gluingStep
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    LocalTotal D → LocalTotal D → Prop :=
  fun x y =>
    ∃ (i j : I) (p : CechOverlap D.cover i j) (z :
      ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j p)).carrier),
      x = gluingSource D p z ∧ y = gluingTarget D p z

theorem gluingStep_localBase_eq
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y : LocalTotal D} (h : gluingStep D x y) :
    localBase D x = localBase D y := by
  rcases h with ⟨i, j, p, z, rfl, rfl⟩
  rfl

def gluingSetoid
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) : Setoid (LocalTotal D) :=
  Relation.EqvGen.setoid (gluingStep D)

def DescendedTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :=
  Quotient (gluingSetoid D)

instance instDescendedTotalTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
  (D : HolomorphicCechDescentData S B I) :
    TopologicalSpace (DescendedTotal D) := by
  exact @instTopologicalSpaceQuotient
    (LocalTotal D) (gluingSetoid D) (localTotalTopology D)

def quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
  (D : HolomorphicCechDescentData S B I) :
    LocalTotal D → DescendedTotal D :=
  Quotient.mk (gluingSetoid D)

theorem gluingEqvGen_localBase_eq
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    ∀ {x y : LocalTotal D},
      Relation.EqvGen (gluingStep D) x y →
      localBase D x = localBase D y := by
  intro x y h
  induction h with
  | rel x y h => exact gluingStep_localBase_eq D h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def descendedProjection
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    DescendedTotal D → B :=
  Quotient.lift (localBase D) (fun x y h => by
    change Relation.EqvGen (gluingStep D) x y at h
    exact gluingEqvGen_localBase_eq D h)

@[simp] theorem descendedProjection_quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (x : LocalTotal D) :
    descendedProjection D (quotientMk D x) = localBase D x :=
  rfl

/-! ### Descent of the marking

The quotient total space has a fibre over each base point.  A local marking
lands in that fibre after applying the quotient map; the only non-canonical
choice is the member of the open cover used to represent the base point.  The
Čech marking-commutation law below is precisely what makes this choice
irrelevant. -/

def DescendedFiber
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (b : B) :=
  {q : DescendedTotal D // descendedProjection D q = b}

def localMarkedPoint
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i : I) (b : D.cover i) (s : S) : LocalTotal D :=
  ⟨i, ⟨b, ((D.localFamily i).family.fiber b).marking s⟩⟩

def localMarkedPointQuotient
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i : I) (b : D.cover i) (s : S) : DescendedFiber D (b : B) :=
  ⟨quotientMk D (localMarkedPoint D i b s), by
    rw [descendedProjection_quotientMk]
    rfl⟩

noncomputable def chosenCoverIndex
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (b : B) : I :=
  Classical.choose (show ∃ i, b ∈ D.cover i by
    have hb : b ∈ ⋃ i, D.cover i := by
      rw [D.cover_univ]
      exact Set.mem_univ b
    exact Set.mem_iUnion.mp hb)

theorem chosenCoverIndex_mem
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (b : B) :
    b ∈ D.cover (chosenCoverIndex D b) := by
  exact Classical.choose_spec (show ∃ i, b ∈ D.cover i by
    have hb : b ∈ ⋃ i, D.cover i := by
      rw [D.cover_univ]
      exact Set.mem_univ b
    exact Set.mem_iUnion.mp hb)

noncomputable def descendedMarking
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (b : B) (s : S) :
    DescendedFiber D b :=
  localMarkedPointQuotient D (chosenCoverIndex D b)
    ⟨b, chosenCoverIndex_mem D b⟩ s

theorem continuous_localBase
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    @Continuous (LocalTotal D) B (localTotalTopology D)
      inferInstance (localBase D) := by
  letI : ∀ i, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    fun i => (D.localFamily i).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  apply continuous_sigma
  intro i
  change Continuous
    (fun z : ComplexSurfaceFamily.Total (D.localFamily i).family =>
      ((ComplexSurfaceFamily.projection (D.localFamily i).family z : D.cover i) : B))
  exact continuous_subtype_val.comp
    (D.localFamily i).family.projection_continuous

theorem continuous_descendedProjection
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    @Continuous (DescendedTotal D) B inferInstance inferInstance
      (descendedProjection D) := by
  apply Continuous.quotient_lift
  exact continuous_localBase D

theorem quotientMk_gluingStep
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    quotientMk D (gluingSource D p z) =
      quotientMk D (gluingTarget D p z) := by
  change Quotient.mk (gluingSetoid D) (gluingSource D p z) =
    Quotient.mk (gluingSetoid D) (gluingTarget D p z)
  apply Quotient.sound
  change Relation.EqvGen (gluingStep D)
    (gluingSource D p z) (gluingTarget D p z)
  exact Relation.EqvGen.rel _ _ ⟨i, j, p, z, rfl, rfl⟩

theorem quotientMk_localMarkedPoint_gluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j) (s : S) :
    quotientMk D (localMarkedPoint D i
        (CechOverlap.leftPoint D.cover i j p) s) =
      quotientMk D (localMarkedPoint D j
        (CechOverlap.rightPoint D.cover i j p) s) := by
  let z := ((D.localFamily i).family.fiber
    (CechOverlap.leftPoint D.cover i j p)).marking s
  have hmark := D.transition_marking_commutes i j p s
  change quotientMk D (gluingSource D p z) =
    quotientMk D ⟨j, ⟨CechOverlap.rightPoint D.cover i j p,
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j p)).marking s⟩⟩
  rw [← hmark]
  exact quotientMk_gluingStep D p z

theorem gluingStep_symm
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y : LocalTotal D} (h : gluingStep D x y) :
    gluingStep D y x := by
  rcases h with ⟨i, j, p, z, rfl, rfl⟩
  refine ⟨j, i, Teichmuller.MathlibFormal.cechOverlapSwap D.cover i j p,
    D.transition i j p z, rfl, ?_⟩
  congr 1
  exact (D.transition_inverse_apply p z).symm

theorem gluingStep_refl
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (x : LocalTotal D) :
    gluingStep D x x := by
  rcases x with ⟨i, ⟨b, z⟩⟩
  let p : CechOverlap D.cover i i := ⟨b, ⟨b.property, b.property⟩⟩
  refine ⟨i, i, p, z, ?_, ?_⟩
  · rfl
  · simp only [gluingTarget, D.transition_self]
    rfl

theorem gluingStep_trans
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y z : LocalTotal D}
    (hxy : gluingStep D x y) (hyz : gluingStep D y z) :
    gluingStep D x z := by
  rcases hxy with ⟨i, j, p, a, rfl, hxy⟩
  rcases p with ⟨pval, ⟨hi, hj⟩⟩
  rcases hyz with ⟨j', k, q, b, hyz, rfl⟩
  rcases q with ⟨qval, ⟨hj', hk⟩⟩
  let p₀ : CechOverlap D.cover i j := ⟨pval, ⟨hi, hj⟩⟩
  let q₀ : CechOverlap D.cover j' k := ⟨qval, ⟨hj', hk⟩⟩
  have hmiddle : gluingTarget D p₀ a = gluingSource D q₀ b := by
    simpa [p₀, q₀] using hxy.symm.trans hyz
  have hindex : j = j' := congrArg Sigma.fst hmiddle
  cases hindex
  have hbase : pval = qval := congrArg (localBase D) hmiddle
  cases hbase
  let q₁ : CechOverlap D.cover j k := ⟨pval, ⟨hj', hk⟩⟩
  have htotal :
      (gluingTarget D p₀ a).2 = (gluingSource D q₁ b).2 := by
    simpa [p₀, q₁] using eq_of_heq (Sigma.ext_iff.mp hmiddle).2
  have hfiber : D.transition i j p₀ a = b := by
    exact eq_of_heq (Sigma.ext_iff.mp htotal).2
  let t : CechTripleOverlap D.cover i j k :=
    ⟨pval, ⟨⟨hi, hj⟩, hk⟩⟩
  have hcomp := D.transition_comp_apply i j k t a
  refine ⟨i, k, CechTripleOverlap.toIK D.cover i j k t, a, rfl, ?_⟩
  change gluingTarget D q₁ b =
    gluingTarget D (CechTripleOverlap.toIK D.cover i j k t) a
  unfold gluingTarget
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      rw [← hfiber]
      convert hcomp.symm using 1

theorem gluingEqvGen_iff_gluingStep
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y : LocalTotal D} :
    Relation.EqvGen (gluingStep D) x y ↔ gluingStep D x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact h
    | refl x => exact gluingStep_refl D x
    | symm x y h ih => exact gluingStep_symm D ih
    | trans x y z hxy hyz ihxy ihyz => exact gluingStep_trans D ihxy ihyz
  · intro h
    exact Relation.EqvGen.rel _ _ h

theorem quotientMk_eq_iff_gluingStep
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y : LocalTotal D} :
    quotientMk D x = quotientMk D y ↔ gluingStep D x y := by
  constructor
  · intro h
    apply (gluingEqvGen_iff_gluingStep D).1
    change (gluingSetoid D).r x y
    exact Quotient.exact h
  · intro h
    apply Quotient.sound
    change Relation.EqvGen (gluingStep D) x y
    exact Relation.EqvGen.rel _ _ h

theorem descendedMarking_eq_local
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i : I) (b : D.cover i) (s : S) :
    descendedMarking D (b : B) s = localMarkedPointQuotient D i b s := by
  apply Subtype.ext
  apply (quotientMk_eq_iff_gluingStep D).2
  let j := chosenCoverIndex D (b : B)
  let bj : D.cover j := ⟨(b : B), chosenCoverIndex_mem D (b : B)⟩
  let p : CechOverlap D.cover j i :=
    ⟨(b : B), ⟨bj.property, b.property⟩⟩
  have hleft : CechOverlap.leftPoint D.cover j i p = bj := by
    apply Subtype.ext
    rfl
  have hright : CechOverlap.rightPoint D.cover j i p = b := by
    apply Subtype.ext
    rfl
  cases hleft
  cases hright
  let z := ((D.localFamily j).family.fiber bj).marking s
  refine ⟨j, i, p, z, ?_, ?_⟩
  · change localMarkedPoint D j bj s = gluingSource D p z
    simp only [localMarkedPoint, gluingSource]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Sigma.ext
      · rfl
      · rfl
  · change localMarkedPoint D i b s = gluingTarget D p z
    simp only [localMarkedPoint, gluingTarget]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        convert (D.transition_marking_commutes j i p s).symm using 1 <;> rfl

structure DescendedMarkingWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) where
  marking : ∀ b : B, S → DescendedFiber D b
  marking_eq_local : ∀ (i : I) (b : D.cover i) (s : S),
    marking (b : B) s = localMarkedPointQuotient D i b s

noncomputable def descendedMarkingWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    DescendedMarkingWitness D where
  marking := descendedMarking D
  marking_eq_local := descendedMarking_eq_local D

/-! This bundles the two pieces already constructed: the descended analytic
    atlas over the base and the marking of each descended fibre.  It is not
    yet the full `ComplexSurfaceFamily.Family`, because extracting a
    one-complex-dimensional atlas on every fibre requires a separate slice
    construction. -/

structure DescendedMarkedAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) where
  atlas : @ComplexSurfaceFamilyAtlas (DescendedTotal D) B inferInstance
  marking : DescendedMarkingWitness D

noncomputable def descendedMarkedAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (A : @ComplexSurfaceFamilyAtlas (DescendedTotal D) B inferInstance) :
    DescendedMarkedAtlas D :=
  { atlas := A
    marking := descendedMarkingWitness D }

/-! ### Total-space overlap charts

The fibrewise transition homeomorphisms in `MathlibCech.lean` do not yet
assert continuity in the overlap parameter.  The following dependent-sum
spaces make that missing datum explicit: the source and target are the
total spaces over an overlap, with the topologies induced from the local
total spaces.  A homeomorphism between these two spaces is precisely a
jointly continuous total transition, rather than only a family of fibrewise
homeomorphisms.
-/

abbrev CechOverlapSourceTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :=
  Sigma fun p : CechOverlap D.cover i j =>
    ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier

abbrev CechOverlapTargetTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :=
  Sigma fun p : CechOverlap D.cover i j =>
    ((D.localFamily j).family.fiber
      (CechOverlap.rightPoint D.cover i j p)).carrier

def overlapSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapSourceTotal D i j → LocalTotal D :=
  fun z => ⟨i, ⟨CechOverlap.leftPoint D.cover i j z.1, z.2⟩⟩

def overlapTargetInclusion
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapTargetTotal D i j → LocalTotal D :=
  fun z => ⟨j, ⟨CechOverlap.rightPoint D.cover i j z.1, z.2⟩⟩

def overlapTransitionMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapSourceTotal D i j → CechOverlapTargetTotal D i j :=
  fun z => ⟨z.1, D.transition i j z.1 z.2⟩

/-! The fibrewise Čech cocycle lifts to the dependent-sum overlap spaces.
    The subtype proofs in the three projections are propositionally invisible,
    so the resulting statement is an equality of actual total-space points,
    not merely an equality after forgetting the base coordinate. -/

theorem overlapTransitionMap_comp_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (i j k : I) (x : CechTripleOverlap D.cover i j k)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j
        (CechTripleOverlap.toIJ D.cover i j k x))).carrier) :
    overlapTransitionMap D i k
        ⟨CechTripleOverlap.toIK D.cover i j k x, z⟩ =
      ⟨CechTripleOverlap.toIK D.cover i j k x,
        D.transition j k (CechTripleOverlap.toJK D.cover i j k x)
          (D.transition i j
            (CechTripleOverlap.toIJ D.cover i j k x) z)⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact D.transition_comp_apply i j k x z

def overlapTransitionInverseMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapTargetTotal D i j → CechOverlapSourceTotal D i j :=
  fun z => ⟨z.1,
    (@Homeomorph.symm
      ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j z.1)).carrier
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j z.1)).carrier
      ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j z.1)).topology
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j z.1)).topology
      (D.transition i j z.1)) z.2⟩

def overlapTargetMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapSourceTotal D i j → LocalTotal D :=
  overlapTargetInclusion D i j ∘ overlapTransitionMap D i j

def cechOverlapSourceTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    TopologicalSpace (CechOverlapSourceTotal D i j) :=
  TopologicalSpace.induced (overlapSourceMap D i j) (localTotalTopology D)

def cechOverlapTargetTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    TopologicalSpace (CechOverlapTargetTotal D i j) :=
  TopologicalSpace.induced (overlapTargetInclusion D i j) (localTotalTopology D)

theorem isOpenEmbedding_cechOverlap_leftPoint
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlap D.cover i j) (D.cover i)
      inferInstance inferInstance
      (CechOverlap.leftPoint D.cover i j) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply Continuous.subtype_mk
    exact continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : D.cover i => (z : B)) hxy
  · intro s hs
    rcases isOpen_induced_iff.mp hs with ⟨V, hV, hVs⟩
    let t : Set (D.cover i) :=
      (fun z : D.cover i => (z : B)) ⁻¹' V ∩
        (fun z : D.cover i => (z : B)) ⁻¹' D.cover j
    have ht : IsOpen t := by
      exact (hV.preimage continuous_subtype_val).inter
        ((D.cover_open j).preimage continuous_subtype_val)
    have himage :
        CechOverlap.leftPoint D.cover i j '' s = t := by
      ext u
      constructor
      · rintro ⟨x, hxs, rfl⟩
        have hxV : (x : B) ∈ V := by
          have hx : x ∈
              (fun z : CechOverlap D.cover i j => (z : B)) ⁻¹' V := by
            rw [hVs]
            exact hxs
          exact hx
        exact ⟨hxV, x.2.2⟩
      · intro hu
        let x : CechOverlap D.cover i j :=
          ⟨(u : B), ⟨u.property, hu.2⟩⟩
        refine ⟨x, ?_, ?_⟩
        · rw [← hVs]
          simpa [x] using hu.1
        · apply Subtype.ext
          rfl
    rw [himage]
    exact ht

theorem isOpenEmbedding_cechOverlap_rightPoint
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlap D.cover i j) (D.cover j)
      inferInstance inferInstance
      (CechOverlap.rightPoint D.cover i j) := by
  have hswap := (cechOverlapSwapHomeomorph D.cover i j).isOpenEmbedding
  have hleft := isOpenEmbedding_cechOverlap_leftPoint D j i
  have hcomp := hleft.comp hswap
  convert hcomp using 1

theorem cechOverlapSourceTopology_eq_pullbackTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    cechOverlapSourceTopology D i j =
      ComplexSurfaceFamily.pullbackTopology
        (D.localFamily i).family
        (CechOverlap.leftPoint D.cover i j) := by
  let F := (D.localFamily i).family
  let g := CechOverlap.leftPoint D.cover i j
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  have hg_ind :
      @TopologicalSpace.induced
          (CechOverlap D.cover i j) (D.cover i) g inferInstance =
        (inferInstance : TopologicalSpace (CechOverlap D.cover i j)) :=
    (isOpenEmbedding_cechOverlap_leftPoint D i j).isInducing.eq_induced.symm
  have hpull :=
    ComplexSurfaceFamily.pullbackTopology_eq_induced_total_of_isInducing
      F g (isOpenEmbedding_cechOverlap_leftPoint D i j).continuous hg_ind
  have hsigma :
      F.totalTopology =
        @TopologicalSpace.induced
          (ComplexSurfaceFamily.Total F) (LocalTotal D)
          (fun z => (⟨i, z⟩ : LocalTotal D))
          (localTotalTopology D) := by
    exact
      (Topology.IsEmbedding.sigmaMk
        (σ := fun k => ComplexSurfaceFamily.Total
          (D.localFamily k).family) (i := i)).isInducing.eq_induced
  let inner : CechOverlapSourceTotal D i j →
      ComplexSurfaceFamily.Total F :=
    fun z => ⟨CechOverlap.leftPoint D.cover i j z.1, z.2⟩
  have hind :
      cechOverlapSourceTopology D i j =
        @TopologicalSpace.induced
          (CechOverlapSourceTotal D i j)
          (ComplexSurfaceFamily.Total F) inner F.totalTopology := by
    change
      @TopologicalSpace.induced
          (CechOverlapSourceTotal D i j) (LocalTotal D)
          ((fun z : CechOverlapSourceTotal D i j =>
            (⟨i, inner z⟩ : LocalTotal D))) (localTotalTopology D) = _
    rw [show (fun z : CechOverlapSourceTotal D i j =>
        (⟨i, inner z⟩ : LocalTotal D)) =
        (fun z => (⟨i, z⟩ : LocalTotal D)) ∘ inner by rfl]
    rw [← induced_compose, ← hsigma]
  calc
    cechOverlapSourceTopology D i j =
        @TopologicalSpace.induced
          (CechOverlapSourceTotal D i j)
          (ComplexSurfaceFamily.Total F) inner F.totalTopology := hind
    _ = ComplexSurfaceFamily.pullbackTopology F g := hpull.symm

theorem cechOverlapTargetTopology_eq_pullbackTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    cechOverlapTargetTopology D i j =
      ComplexSurfaceFamily.pullbackTopology
        (D.localFamily j).family
        (CechOverlap.rightPoint D.cover i j) := by
  let F := (D.localFamily j).family
  let g := CechOverlap.rightPoint D.cover i j
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  have hg_ind :
      @TopologicalSpace.induced
          (CechOverlap D.cover i j) (D.cover j) g inferInstance =
        (inferInstance : TopologicalSpace (CechOverlap D.cover i j)) :=
    (isOpenEmbedding_cechOverlap_rightPoint D i j).isInducing.eq_induced.symm
  have hpull :=
    ComplexSurfaceFamily.pullbackTopology_eq_induced_total_of_isInducing
      F g (isOpenEmbedding_cechOverlap_rightPoint D i j).continuous hg_ind
  have hsigma :
      F.totalTopology =
        @TopologicalSpace.induced
          (ComplexSurfaceFamily.Total F) (LocalTotal D)
          (fun z => (⟨j, z⟩ : LocalTotal D))
          (localTotalTopology D) := by
    exact
      (Topology.IsEmbedding.sigmaMk
        (σ := fun k => ComplexSurfaceFamily.Total
          (D.localFamily k).family) (i := j)).isInducing.eq_induced
  let inner : CechOverlapTargetTotal D i j →
      ComplexSurfaceFamily.Total F :=
    fun z => ⟨CechOverlap.rightPoint D.cover i j z.1, z.2⟩
  have hind :
      cechOverlapTargetTopology D i j =
        @TopologicalSpace.induced
          (CechOverlapTargetTotal D i j)
          (ComplexSurfaceFamily.Total F) inner F.totalTopology := by
    change
      @TopologicalSpace.induced
          (CechOverlapTargetTotal D i j) (LocalTotal D)
          ((fun z : CechOverlapTargetTotal D i j =>
            (⟨j, inner z⟩ : LocalTotal D))) (localTotalTopology D) = _
    rw [show (fun z : CechOverlapTargetTotal D i j =>
        (⟨j, inner z⟩ : LocalTotal D)) =
        (fun z => (⟨j, z⟩ : LocalTotal D)) ∘ inner by rfl]
    rw [← induced_compose, ← hsigma]
  calc
    cechOverlapTargetTopology D i j =
        @TopologicalSpace.induced
          (CechOverlapTargetTotal D i j)
          (ComplexSurfaceFamily.Total F) inner F.totalTopology := hind
    _ = ComplexSurfaceFamily.pullbackTopology F g := hpull.symm

/-! The same overlap total spaces can also be viewed inside the individual
local family total spaces.  This second presentation is the one needed for
transporting the actual local surface atlases to the overlap. -/

def overlapSourceFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapSourceTotal D i j →
      ComplexSurfaceFamily.Total (D.localFamily i).family :=
  fun z => ⟨CechOverlap.leftPoint D.cover i j z.1, z.2⟩

def overlapTargetFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    CechOverlapTargetTotal D i j →
      ComplexSurfaceFamily.Total (D.localFamily j).family :=
  fun z => ⟨CechOverlap.rightPoint D.cover i j z.1, z.2⟩

theorem cechOverlapSourceTopology_eq_induced_fibre_total
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    cechOverlapSourceTopology D i j =
      @TopologicalSpace.induced
        (CechOverlapSourceTotal D i j)
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (overlapSourceFibreMap D i j)
        (D.localFamily i).family.totalTopology := by
  let F := (D.localFamily i).family
  let g := CechOverlap.leftPoint D.cover i j
  have hg_ind :
      @TopologicalSpace.induced
          (CechOverlap D.cover i j) (D.cover i) g inferInstance =
        (inferInstance : TopologicalSpace (CechOverlap D.cover i j)) :=
    (isOpenEmbedding_cechOverlap_leftPoint D i j).isInducing.eq_induced.symm
  calc
    cechOverlapSourceTopology D i j =
        ComplexSurfaceFamily.pullbackTopology F g :=
      cechOverlapSourceTopology_eq_pullbackTopology D i j
    _ = @TopologicalSpace.induced
        (CechOverlapSourceTotal D i j)
        (ComplexSurfaceFamily.Total F)
        (overlapSourceFibreMap D i j) F.totalTopology := by
      exact ComplexSurfaceFamily.pullbackTopology_eq_induced_total_of_isInducing
        F g (isOpenEmbedding_cechOverlap_leftPoint D i j).continuous hg_ind
    _ = @TopologicalSpace.induced
        (CechOverlapSourceTotal D i j)
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (overlapSourceFibreMap D i j)
        (D.localFamily i).family.totalTopology := by
      rfl

theorem cechOverlapTargetTopology_eq_induced_fibre_total
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    cechOverlapTargetTopology D i j =
      @TopologicalSpace.induced
        (CechOverlapTargetTotal D i j)
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (overlapTargetFibreMap D i j)
        (D.localFamily j).family.totalTopology := by
  let F := (D.localFamily j).family
  let g := CechOverlap.rightPoint D.cover i j
  have hg_ind :
      @TopologicalSpace.induced
          (CechOverlap D.cover i j) (D.cover j) g inferInstance =
        (inferInstance : TopologicalSpace (CechOverlap D.cover i j)) :=
    (isOpenEmbedding_cechOverlap_rightPoint D i j).isInducing.eq_induced.symm
  calc
    cechOverlapTargetTopology D i j =
        ComplexSurfaceFamily.pullbackTopology F g :=
      cechOverlapTargetTopology_eq_pullbackTopology D i j
    _ = @TopologicalSpace.induced
        (CechOverlapTargetTotal D i j)
        (ComplexSurfaceFamily.Total F)
        (overlapTargetFibreMap D i j) F.totalTopology := by
      exact ComplexSurfaceFamily.pullbackTopology_eq_induced_total_of_isInducing
        F g (isOpenEmbedding_cechOverlap_rightPoint D i j).continuous hg_ind
    _ = @TopologicalSpace.induced
        (CechOverlapTargetTotal D i j)
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (overlapTargetFibreMap D i j)
        (D.localFamily j).family.totalTopology := by
      rfl

theorem continuous_overlapSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Continuous (CechOverlapSourceTotal D i j) (LocalTotal D)
      (cechOverlapSourceTopology D i j) (localTotalTopology D)
      (overlapSourceMap D i j) := by
  exact continuous_induced_dom

theorem continuous_overlapTargetInclusion
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Continuous (CechOverlapTargetTotal D i j) (LocalTotal D)
      (cechOverlapTargetTopology D i j) (localTotalTopology D)
      (overlapTargetInclusion D i j) := by
  exact continuous_induced_dom

theorem overlapSourceMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Set.range (overlapSourceMap D i j) =
      Set.range (fun z : ComplexSurfaceFamily.Total
        (D.localFamily i).family => (⟨i, z⟩ : LocalTotal D)) ∩
        (localBase D ⁻¹' D.cover j) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨⟨CechOverlap.leftPoint D.cover i j z.1, z.2⟩, rfl⟩, ?_⟩
    change (CechOverlap.leftPoint D.cover i j z.1 : B) ∈ D.cover j
    exact z.1.2.2
  · rintro ⟨⟨z, rfl⟩, hz⟩
    let p : CechOverlap D.cover i j :=
      ⟨(z.1 : B), ⟨z.1.property, hz⟩⟩
    have hp : CechOverlap.leftPoint D.cover i j p = z.1 := by
      apply Subtype.ext
      rfl
    let z' : ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j p)).carrier :=
      cast (congrArg (fun b : D.cover i =>
        ((D.localFamily i).family.fiber b).carrier) hp.symm) z.2
    refine ⟨⟨p, z'⟩, ?_⟩
    unfold overlapSourceMap
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      cases hp
      rfl

theorem overlapTargetInclusion_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Set.range (overlapTargetInclusion D i j) =
      Set.range (fun z : ComplexSurfaceFamily.Total
        (D.localFamily j).family => (⟨j, z⟩ : LocalTotal D)) ∩
        (localBase D ⁻¹' D.cover i) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨⟨CechOverlap.rightPoint D.cover i j z.1, z.2⟩, rfl⟩, ?_⟩
    change (CechOverlap.rightPoint D.cover i j z.1 : B) ∈ D.cover i
    exact z.1.2.1
  · rintro ⟨⟨z, rfl⟩, hz⟩
    let p : CechOverlap D.cover i j :=
      ⟨(z.1 : B), ⟨hz, z.1.property⟩⟩
    have hp : CechOverlap.rightPoint D.cover i j p = z.1 := by
      apply Subtype.ext
      rfl
    let z' : ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j p)).carrier :=
      cast (congrArg (fun b : D.cover j =>
        ((D.localFamily j).family.fiber b).carrier) hp.symm) z.2
    refine ⟨⟨p, z'⟩, ?_⟩
    unfold overlapTargetInclusion
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      cases hp
      rfl

theorem isOpen_overlapSourceRange
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (LocalTotal D) (localTotalTopology D)
      (Set.range (overlapSourceMap D i j)) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  rw [overlapSourceMap_range D i j]
  exact isOpen_range_sigmaMk.inter
    ((D.cover_open j).preimage (continuous_localBase D))

theorem isOpen_overlapTargetRange
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (LocalTotal D) (localTotalTopology D)
      (Set.range (overlapTargetInclusion D i j)) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  rw [overlapTargetInclusion_range D i j]
  exact isOpen_range_sigmaMk.inter
    ((D.cover_open i).preimage (continuous_localBase D))

theorem isOpenMap_induced_of_isOpen_range
    {X Y : Type*} [TopologicalSpace Y]
    (f : X → Y) (hrange : IsOpen (Set.range f)) :
    @IsOpenMap X Y (TopologicalSpace.induced f inferInstance)
      inferInstance f := by
  intro U hU
  rcases (isOpen_induced_iff.mp hU) with ⟨V, hV, hVU⟩
  have himage : f '' U = V ∩ Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ f ⁻¹' V := by
        rw [hVU]
        exact hx
      exact ⟨hxV, ⟨x, rfl⟩⟩
    · rintro ⟨hyV, ⟨x, rfl⟩⟩
      refine ⟨x, ?_, rfl⟩
      rw [← hVU]
      exact hyV
  rw [himage]
  exact hV.inter hrange

theorem isOpenMap_overlapSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpenMap
      (CechOverlapSourceTotal D i j) (LocalTotal D)
      (cechOverlapSourceTopology D i j) (localTotalTopology D)
      (overlapSourceMap D i j) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  exact isOpenMap_induced_of_isOpen_range
    (overlapSourceMap D i j) (isOpen_overlapSourceRange D i j)

theorem isOpenMap_overlapTargetInclusion
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpenMap
      (CechOverlapTargetTotal D i j) (LocalTotal D)
      (cechOverlapTargetTopology D i j) (localTotalTopology D)
      (overlapTargetInclusion D i j) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  exact isOpenMap_induced_of_isOpen_range
    (overlapTargetInclusion D i j) (isOpen_overlapTargetRange D i j)

theorem injective_overlapSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Function.Injective (overlapSourceMap D i j) := by
  intro x y hxy
  rcases x with ⟨p, x⟩
  rcases y with ⟨q, y⟩
  have hpq : p = q := by
    apply Subtype.ext
    exact congrArg (fun z : LocalTotal D => localBase D z) hxy
  subst q
  have hinner :
      (⟨CechOverlap.leftPoint D.cover i j p, x⟩ :
        ComplexSurfaceFamily.Total (D.localFamily i).family) =
        ⟨CechOverlap.leftPoint D.cover i j p, y⟩ := by
    exact eq_of_heq (Sigma.ext_iff.mp hxy).2
  exact Sigma.ext (by rfl) ((Sigma.ext_iff.mp hinner).2)

theorem injective_overlapTargetInclusion
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Function.Injective (overlapTargetInclusion D i j) := by
  intro x y hxy
  rcases x with ⟨p, x⟩
  rcases y with ⟨q, y⟩
  have hpq : p = q := by
    apply Subtype.ext
    exact congrArg (fun z : LocalTotal D => localBase D z) hxy
  subst q
  have hinner :
      (⟨CechOverlap.rightPoint D.cover i j p, x⟩ :
        ComplexSurfaceFamily.Total (D.localFamily j).family) =
        ⟨CechOverlap.rightPoint D.cover i j p, y⟩ := by
    exact eq_of_heq (Sigma.ext_iff.mp hxy).2
  exact Sigma.ext (by rfl) ((Sigma.ext_iff.mp hinner).2)

theorem isOpenEmbedding_overlapSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapSourceTotal D i j) (LocalTotal D)
      (cechOverlapSourceTopology D i j) (localTotalTopology D)
      (overlapSourceMap D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_overlapSourceMap D i j
  · exact injective_overlapSourceMap D i j
  · exact isOpenMap_overlapSourceMap D i j

theorem isOpenEmbedding_overlapTargetInclusion
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapTargetTotal D i j) (LocalTotal D)
      (cechOverlapTargetTopology D i j) (localTotalTopology D)
      (overlapTargetInclusion D i j) := by
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_overlapTargetInclusion D i j
  · exact injective_overlapTargetInclusion D i j
  · exact isOpenMap_overlapTargetInclusion D i j

/-! The fibre presentations are open embeddings into the corresponding local
family total spaces.  These are the geometric inclusions on which the local
surface atlases will be restricted. -/

theorem overlapSourceFibreMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Set.range (overlapSourceFibreMap D i j) =
      ComplexSurfaceFamily.projection (D.localFamily i).family ⁻¹'
        ((fun b : D.cover i => (b : B)) ⁻¹' D.cover j) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change (CechOverlap.leftPoint D.cover i j w.1 : B) ∈ D.cover j
    exact w.1.2.2
  · intro hz
    let p : CechOverlap D.cover i j :=
      ⟨(z.1 : B), ⟨z.1.property, hz⟩⟩
    have hp : CechOverlap.leftPoint D.cover i j p = z.1 := by
      apply Subtype.ext
      rfl
    let z' : ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j p)).carrier :=
      cast (congrArg (fun b : D.cover i =>
        ((D.localFamily i).family.fiber b).carrier) hp.symm) z.2
    refine ⟨⟨p, z'⟩, ?_⟩
    unfold overlapSourceFibreMap
    apply Sigma.ext hp
    apply heq_of_eq
    cases hp
    rfl

theorem overlapTargetFibreMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Set.range (overlapTargetFibreMap D i j) =
      ComplexSurfaceFamily.projection (D.localFamily j).family ⁻¹'
        ((fun b : D.cover j => (b : B)) ⁻¹' D.cover i) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change (CechOverlap.rightPoint D.cover i j w.1 : B) ∈ D.cover i
    exact w.1.2.1
  · intro hz
    let p : CechOverlap D.cover i j :=
      ⟨(z.1 : B), ⟨hz, z.1.property⟩⟩
    have hp : CechOverlap.rightPoint D.cover i j p = z.1 := by
      apply Subtype.ext
      rfl
    let z' : ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j p)).carrier :=
      cast (congrArg (fun b : D.cover j =>
        ((D.localFamily j).family.fiber b).carrier) hp.symm) z.2
    refine ⟨⟨p, z'⟩, ?_⟩
    unfold overlapTargetFibreMap
    apply Sigma.ext hp
    apply heq_of_eq
    cases hp
    rfl

theorem isOpen_overlapSourceFibreMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (D.localFamily i).family.totalTopology
      (Set.range (overlapSourceFibreMap D i j)) := by
  rw [overlapSourceFibreMap_range D i j]
  have hbase : @Continuous
      (ComplexSurfaceFamily.Total (D.localFamily i).family) B
      (D.localFamily i).family.totalTopology inferInstance
      (fun z => ((ComplexSurfaceFamily.projection
        (D.localFamily i).family z : D.cover i) : B)) := by
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
      (D.localFamily i).family.totalTopology
    exact (continuous_subtype_val :
      @Continuous (D.cover i) B inferInstance inferInstance
        (fun b : D.cover i => (b : B))).comp
      (ComplexSurfaceFamily.projection_continuous_of_family
        (D.localFamily i).family)
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  exact (D.cover_open j).preimage hbase

theorem isOpen_overlapTargetFibreMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (ComplexSurfaceFamily.Total (D.localFamily j).family)
      (D.localFamily j).family.totalTopology
      (Set.range (overlapTargetFibreMap D i j)) := by
  rw [overlapTargetFibreMap_range D i j]
  have hbase : @Continuous
      (ComplexSurfaceFamily.Total (D.localFamily j).family) B
      (D.localFamily j).family.totalTopology inferInstance
      (fun z => ((ComplexSurfaceFamily.projection
        (D.localFamily j).family z : D.cover j) : B)) := by
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
      (D.localFamily j).family.totalTopology
    exact (continuous_subtype_val :
      @Continuous (D.cover j) B inferInstance inferInstance
        (fun b : D.cover j => (b : B))).comp
      (ComplexSurfaceFamily.projection_continuous_of_family
        (D.localFamily j).family)
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
    (D.localFamily j).family.totalTopology
  exact (D.cover_open i).preimage hbase

theorem injective_overlapSourceFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Function.Injective (overlapSourceFibreMap D i j) := by
  intro x y hxy
  rcases x with ⟨p, x⟩
  rcases y with ⟨q, y⟩
  have hpq : p = q := by
    apply Subtype.ext
    exact congrArg (fun z => (z.1 : B)) (congrArg Sigma.fst hxy)
  subst q
  change (⟨CechOverlap.leftPoint D.cover i j p, x⟩ :
      ComplexSurfaceFamily.Total (D.localFamily i).family) =
    ⟨CechOverlap.leftPoint D.cover i j p, y⟩ at hxy
  apply Sigma.ext (by rfl)
  exact (Sigma.ext_iff.mp hxy).2

theorem injective_overlapTargetFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    Function.Injective (overlapTargetFibreMap D i j) := by
  intro x y hxy
  rcases x with ⟨p, x⟩
  rcases y with ⟨q, y⟩
  have hpq : p = q := by
    apply Subtype.ext
    exact congrArg (fun z => (z.1 : B)) (congrArg Sigma.fst hxy)
  subst q
  change (⟨CechOverlap.rightPoint D.cover i j p, x⟩ :
      ComplexSurfaceFamily.Total (D.localFamily j).family) =
    ⟨CechOverlap.rightPoint D.cover i j p, y⟩ at hxy
  apply Sigma.ext (by rfl)
  exact (Sigma.ext_iff.mp hxy).2

theorem isOpenEmbedding_overlapSourceFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapSourceTotal D i j)
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (cechOverlapSourceTopology D i j)
      (D.localFamily i).family.totalTopology
      (overlapSourceFibreMap D i j) := by
  rw [cechOverlapSourceTopology_eq_induced_fibre_total D i j]
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    TopologicalSpace.induced (overlapSourceFibreMap D i j)
      (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_induced_dom
  · exact injective_overlapSourceFibreMap D i j
  · exact isOpenMap_induced_of_isOpen_range
      (overlapSourceFibreMap D i j)
      (isOpen_overlapSourceFibreMap_range D i j)

theorem isOpenEmbedding_overlapTargetFibreMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapTargetTotal D i j)
      (ComplexSurfaceFamily.Total (D.localFamily j).family)
      (cechOverlapTargetTopology D i j)
      (D.localFamily j).family.totalTopology
      (overlapTargetFibreMap D i j) := by
  rw [cechOverlapTargetTopology_eq_induced_fibre_total D i j]
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    TopologicalSpace.induced (overlapTargetFibreMap D i j)
      (D.localFamily j).family.totalTopology
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
    (D.localFamily j).family.totalTopology
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_induced_dom
  · exact injective_overlapTargetFibreMap D i j
  · exact isOpenMap_induced_of_isOpen_range
      (overlapTargetFibreMap D i j)
      (isOpen_overlapTargetFibreMap_range D i j)

theorem isOpen_overlapSourceFibreMap_range_atlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (D.localFamily i).atlas.toComplexSurfaceAtlas.topology
      (Set.range (overlapSourceFibreMap D i j)) := by
  rw [(D.localFamily i).topology_eq]
  exact isOpen_overlapSourceFibreMap_range D i j

theorem isOpen_overlapTargetFibreMap_range_atlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    @IsOpen (ComplexSurfaceFamily.Total (D.localFamily j).family)
      (D.localFamily j).atlas.toComplexSurfaceAtlas.topology
      (Set.range (overlapTargetFibreMap D i j)) := by
  rw [(D.localFamily j).topology_eq]
  exact isOpen_overlapTargetFibreMap_range D i j

/-! Restricting the local surface atlas to an overlap, and then transporting it
back along the open embedding, gives an actual complex surface atlas on the
overlap source/target.  The topology equalities above are what make the
retopologization in these definitions definitional rather than axiomatic. -/

noncomputable def overlapSourceAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    ComplexSurfaceAtlas (CechOverlapSourceTotal D i j) := by
  let A := (D.localFamily i).atlas.toComplexSurfaceAtlas
  let U := Set.range (overlapSourceFibreMap D i j)
  have hU : @IsOpen (ComplexSurfaceFamily.Total (D.localFamily i).family)
      A.topology U := by
    dsimp [A, U]
    exact isOpen_overlapSourceFibreMap_range_atlas D i j
  let restricted := ComplexSurfaceAtlas.restrictOpenSubspace A U hU
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  let hrange :=
    (isOpenEmbedding_overlapSourceFibreMap D i j).isEmbedding
  let e₀ := hrange.toHomeomorph
  have htop :
      TopologicalSpace.induced Subtype.val
          (D.localFamily i).family.totalTopology =
        restricted.toComplexSurfaceChartFamily.topology := by
    change TopologicalSpace.induced Subtype.val
        (D.localFamily i).family.totalTopology =
      TopologicalSpace.induced Subtype.val
        (D.localFamily i).atlas.toComplexSurfaceAtlas.topology
    exact congrArg
      (fun t => TopologicalSpace.induced Subtype.val t)
      ((D.localFamily i).topology_eq).symm
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀ htop
  exact ComplexSurfaceAtlas.transport restricted e

noncomputable def overlapTargetAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    ComplexSurfaceAtlas (CechOverlapTargetTotal D i j) := by
  let A := (D.localFamily j).atlas.toComplexSurfaceAtlas
  let U := Set.range (overlapTargetFibreMap D i j)
  have hU : @IsOpen (ComplexSurfaceFamily.Total (D.localFamily j).family)
      A.topology U := by
    dsimp [A, U]
    exact isOpen_overlapTargetFibreMap_range_atlas D i j
  let restricted := ComplexSurfaceAtlas.restrictOpenSubspace A U hU
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
    (D.localFamily j).family.totalTopology
  let hrange :=
    (isOpenEmbedding_overlapTargetFibreMap D i j).isEmbedding
  let e₀ := hrange.toHomeomorph
  have htop :
      TopologicalSpace.induced Subtype.val
          (D.localFamily j).family.totalTopology =
        restricted.toComplexSurfaceChartFamily.topology := by
    change TopologicalSpace.induced Subtype.val
        (D.localFamily j).family.totalTopology =
      TopologicalSpace.induced Subtype.val
        (D.localFamily j).atlas.toComplexSurfaceAtlas.topology
    exact congrArg
      (fun t => TopologicalSpace.induced Subtype.val t)
      ((D.localFamily j).topology_eq).symm
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀ htop
  exact ComplexSurfaceAtlas.transport restricted e

theorem overlapSourceAtlas_topology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    (overlapSourceAtlas D i j).topology =
      cechOverlapSourceTopology D i j := by
  rfl

theorem overlapTargetAtlas_topology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I) :
    (overlapTargetAtlas D i j).topology =
      cechOverlapTargetTopology D i j := by
  rfl

theorem overlapSourceAtlas_chart_apply_val
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I)
    (c : (D.localFamily i).atlas.index)
    (z : CechOverlapSourceTotal D i j)
    (hz : z ∈ ((overlapSourceAtlas D i j).chart c).domain)
    (hx : overlapSourceFibreMap D i j z ∈
      ((D.localFamily i).atlas.chart c).domain) :
    (((overlapSourceAtlas D i j).chart c).chart ⟨z, hz⟩).1 =
      (((D.localFamily i).atlas.chart c).chart
        ⟨overlapSourceFibreMap D i j z, hx⟩).1 := by
  classical
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  let A := (D.localFamily i).atlas.toComplexSurfaceAtlas
  let U := Set.range (overlapSourceFibreMap D i j)
  have hU : @IsOpen (ComplexSurfaceFamily.Total (D.localFamily i).family)
      A.topology U := by
    dsimp [A, U]
    exact isOpen_overlapSourceFibreMap_range_atlas D i j
  let restricted := ComplexSurfaceAtlas.restrictOpenSubspace A U hU
  let hrange := (isOpenEmbedding_overlapSourceFibreMap D i j).isEmbedding
  let e₀ := hrange.toHomeomorph
  have htop :
      TopologicalSpace.induced Subtype.val
          (D.localFamily i).family.totalTopology =
        restricted.toComplexSurfaceChartFamily.topology := by
    change TopologicalSpace.induced Subtype.val
        (D.localFamily i).family.totalTopology =
      TopologicalSpace.induced Subtype.val
        (D.localFamily i).atlas.toComplexSurfaceAtlas.topology
    exact congrArg
      (fun t => TopologicalSpace.induced Subtype.val t)
      ((D.localFamily i).topology_eq).symm
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀ htop
  have hAtlas : overlapSourceAtlas D i j =
      ComplexSurfaceAtlas.transport restricted e := by
    rfl
  let cR : restricted.index := c
  let cT : (ComplexSurfaceAtlas.transport restricted e).index := c
  have hz' : z ∈ ((ComplexSurfaceAtlas.transport restricted e).chart cT).domain := by
    change z ∈ ((ComplexSurfaceAtlas.transport restricted e).chart cT).domain at hz
    exact hz
  have hcoordTransport :
      (((ComplexSurfaceAtlas.transport restricted e).chart cT).chart
        ⟨z, hz'⟩).1 =
        (((D.localFamily i).atlas.chart c).chart
          ⟨overlapSourceFibreMap D i j z, hx⟩).1 := by
    have hzR : e z ∈ (restricted.chart cR).domain := by
      change e z ∈ (restricted.chart cR).domain at hz'
      exact hz'
    change
      ((ComplexSurfaceChart.transport e (restricted.chart cR)).chart
        ⟨z, hz'⟩).1 = _
    rw [ComplexSurfaceChart.transport_chart_apply]
    change
      (((A.chart cR).restrictOpenSubspace U hU).chart
        ⟨e z, hzR⟩).1 = _
    rw [ComplexSurfaceChart.restrictOpenSubspace_chart_apply]
    change
      ((A.chart cR).chart
        ⟨overlapSourceFibreMap D i j z, _⟩).1 = _
    congr 1
  change
    (((ComplexSurfaceAtlas.transport restricted e).chart cT).chart
      ⟨z, hz'⟩).1 = _
  exact hcoordTransport

theorem overlapTargetAtlas_chart_apply_val
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I)
    (d : (D.localFamily j).atlas.index)
    (z : CechOverlapTargetTotal D i j)
    (hz : z ∈ ((overlapTargetAtlas D i j).chart d).domain)
    (hx : overlapTargetFibreMap D i j z ∈
      ((D.localFamily j).atlas.chart d).domain) :
    (((overlapTargetAtlas D i j).chart d).chart ⟨z, hz⟩).1 =
      (((D.localFamily j).atlas.chart d).chart
        ⟨overlapTargetFibreMap D i j z, hx⟩).1 := by
  classical
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
    (D.localFamily j).family.totalTopology
  let A := (D.localFamily j).atlas.toComplexSurfaceAtlas
  let U := Set.range (overlapTargetFibreMap D i j)
  have hU : @IsOpen (ComplexSurfaceFamily.Total (D.localFamily j).family)
      A.topology U := by
    dsimp [A, U]
    exact isOpen_overlapTargetFibreMap_range_atlas D i j
  let restricted := ComplexSurfaceAtlas.restrictOpenSubspace A U hU
  let hrange := (isOpenEmbedding_overlapTargetFibreMap D i j).isEmbedding
  let e₀ := hrange.toHomeomorph
  have htop :
      TopologicalSpace.induced Subtype.val
          (D.localFamily j).family.totalTopology =
        restricted.toComplexSurfaceChartFamily.topology := by
    change TopologicalSpace.induced Subtype.val
        (D.localFamily j).family.totalTopology =
      TopologicalSpace.induced Subtype.val
        (D.localFamily j).atlas.toComplexSurfaceAtlas.topology
    exact congrArg
      (fun t => TopologicalSpace.induced Subtype.val t)
      ((D.localFamily j).topology_eq).symm
  let e := ComplexSurfaceFamily.retopologizeHomeomorph e₀ htop
  have hAtlas : overlapTargetAtlas D i j =
      ComplexSurfaceAtlas.transport restricted e := by
    rfl
  let dR : restricted.index := d
  let dT : (ComplexSurfaceAtlas.transport restricted e).index := d
  have hz' : z ∈
      ((ComplexSurfaceAtlas.transport restricted e).chart dT).domain := by
    change z ∈ ((ComplexSurfaceAtlas.transport restricted e).chart dT).domain at hz
    exact hz
  have hcoordTransport :
      (((ComplexSurfaceAtlas.transport restricted e).chart dT).chart
        ⟨z, hz'⟩).1 =
        (((D.localFamily j).atlas.chart d).chart
          ⟨overlapTargetFibreMap D i j z, hx⟩).1 := by
    have hzR : e z ∈ (restricted.chart dR).domain := by
      change e z ∈ (restricted.chart dR).domain at hz'
      exact hz'
    change
      ((ComplexSurfaceChart.transport e (restricted.chart dR)).chart
        ⟨z, hz'⟩).1 = _
    rw [ComplexSurfaceChart.transport_chart_apply]
    change
      (((A.chart dR).restrictOpenSubspace U hU).chart
        ⟨e z, hzR⟩).1 = _
    rw [ComplexSurfaceChart.restrictOpenSubspace_chart_apply]
    change
      ((A.chart dR).chart
        ⟨overlapTargetFibreMap D i j z, _⟩).1 = _
    congr 1
  change
    (((ComplexSurfaceAtlas.transport restricted e).chart dT).chart
      ⟨z, hz'⟩).1 = _
  exact hcoordTransport

theorem overlapSourceAtlas_transition_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I)
    (c d : (overlapSourceAtlas D i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i j).chart c)
        ((overlapSourceAtlas D i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapSourceAtlas D i j).chart c)
        ((overlapSourceAtlas D i j).chart d)) :=
  (overlapSourceAtlas D i j).transition_differentiableOn c d

theorem overlapTargetAtlas_transition_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i j : I)
    (c d : (overlapTargetAtlas D i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapTargetAtlas D i j).chart c)
        ((overlapTargetAtlas D i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapTargetAtlas D i j).chart c)
        ((overlapTargetAtlas D i j).chart d)) :=
  (overlapTargetAtlas D i j).transition_differentiableOn c d

structure TotalOverlapHomeomorphWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) where
  transition_homeomorph : ∀ i j,
    @Homeomorph
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j)
  transition_homeomorph_apply : ∀ i j z,
    transition_homeomorph i j z = overlapTransitionMap D i j z

/-! The homeomorphism witness above is the convenient interface for the
quotient argument.  For analytic input, however, it is useful to expose the
actual proof obligations instead of asking for a bundled `Homeomorph` at once:
a joint transition map, a joint inverse, the two inverse laws, continuity in
the overlap parameter, and agreement with the given fibrewise transition.
This structure is therefore the next refinement of the old fibrewise-only
`HolomorphicCechDescentData.transition` field. -/

structure JointlyContinuousTransitionData
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) where
  toFun : ∀ i j,
    CechOverlapSourceTotal D i j → CechOverlapTargetTotal D i j
  invFun : ∀ i j,
    CechOverlapTargetTotal D i j → CechOverlapSourceTotal D i j
  left_inv : ∀ i j z, invFun i j (toFun i j z) = z
  right_inv : ∀ i j z, toFun i j (invFun i j z) = z
  continuous_toFun : ∀ i j,
    @Continuous
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j)
      (toFun i j)
  continuous_invFun : ∀ i j,
    @Continuous
      (CechOverlapTargetTotal D i j)
      (CechOverlapSourceTotal D i j)
      (cechOverlapTargetTopology D i j)
      (cechOverlapSourceTopology D i j)
      (invFun i j)
  toFun_agrees : ∀ i j z,
    toFun i j z = overlapTransitionMap D i j z

def JointlyContinuousTransitionData.homeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyContinuousTransitionData D) (i j : I) :
    @Homeomorph
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  exact
    { toFun := J.toFun i j
      invFun := J.invFun i j
      left_inv := J.left_inv i j
      right_inv := J.right_inv i j
      continuous_toFun := J.continuous_toFun i j
      continuous_invFun := J.continuous_invFun i j }

@[simp] theorem JointlyContinuousTransitionData.homeomorph_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyContinuousTransitionData D) (i j : I)
    (z : CechOverlapSourceTotal D i j) :
    J.homeomorph i j z = J.toFun i j z :=
  by
    change J.toFun i j z = J.toFun i j z
    rfl

def totalOverlapHomeomorphWitness_of_jointlyContinuous
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (J : JointlyContinuousTransitionData D) :
    TotalOverlapHomeomorphWitness D where
  transition_homeomorph := J.homeomorph
  transition_homeomorph_apply := by
    intro i j z
    rw [JointlyContinuousTransitionData.homeomorph_apply]
    exact J.toFun_agrees i j z

theorem jointlyContinuousTransition_toFun_eq_fibrewise
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyContinuousTransitionData D) {i j : I}
    (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    J.toFun i j ⟨p, z⟩ =
      ⟨p, D.transition i j p z⟩ := by
  exact J.toFun_agrees i j ⟨p, z⟩

theorem JointlyContinuousTransitionData.toFun_comp_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyContinuousTransitionData D)
    (i j k : I) (x : CechTripleOverlap D.cover i j k)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j
        (CechTripleOverlap.toIJ D.cover i j k x))).carrier) :
    J.toFun i k
        ⟨CechTripleOverlap.toIK D.cover i j k x, z⟩ =
      ⟨CechTripleOverlap.toIK D.cover i j k x,
        D.transition j k (CechTripleOverlap.toJK D.cover i j k x)
          (D.transition i j
            (CechTripleOverlap.toIJ D.cover i j k x) z)⟩ := by
  rw [J.toFun_agrees i k]
  exact overlapTransitionMap_comp_apply D i j k x z

/-! A jointly continuous total transition becomes jointly holomorphic only
after the two overlap total spaces are equipped with their actual transported
surface atlases.  The following refinement records both chartwise directions
using `ComplexSurfaceAtlas.HolomorphicMap`; it is stronger than the old
fibrewise `transition_holomorphic` field and is the precise input needed by a
complex-analytic quotient descent. -/

structure JointlyHolomorphicTransitionData
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    extends JointlyContinuousTransitionData D where
  forward_holomorphic : ∀ i j,
    ComplexSurfaceAtlas.HolomorphicMap
      (overlapSourceAtlas D i j)
      (overlapTargetAtlas D i j)
      (toJointlyContinuousTransitionData.homeomorph i j)
  inverse_holomorphic : ∀ i j,
    ComplexSurfaceAtlas.HolomorphicMap
      (overlapTargetAtlas D i j)
      (overlapSourceAtlas D i j)
      (@Homeomorph.symm
        (CechOverlapSourceTotal D i j)
        (CechOverlapTargetTotal D i j)
        (cechOverlapSourceTopology D i j)
        (cechOverlapTargetTopology D i j)
        (toJointlyContinuousTransitionData.homeomorph i j))

def JointlyHolomorphicTransitionData.toContinuous
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyHolomorphicTransitionData D) :
    JointlyContinuousTransitionData D :=
  J.toJointlyContinuousTransitionData

def JointlyHolomorphicTransitionData.ofHolomorphicEquiv
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (J : JointlyContinuousTransitionData D)
    (H : ∀ i j,
      ComplexSurfaceAtlas.HolomorphicEquiv
        (overlapSourceAtlas D i j)
        (overlapTargetAtlas D i j)
        (J.homeomorph i j)) :
    JointlyHolomorphicTransitionData D :=
  { toJointlyContinuousTransitionData := J
    forward_holomorphic := fun i j => (H i j).forward
    inverse_holomorphic := fun i j => (H i j).inverse }

/-! A common-mother-atlas witness is the concrete geometric input from which
    the preceding holomorphic transition structure can be generated.  It
    records more than a bare equivalence: both overlap atlases must literally
    be transports of one mother atlas, and the total-space comparison must
    satisfy the corresponding composition law. -/

structure CommonMotherAtlasTransitionWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    extends JointlyContinuousTransitionData D where
  motherCarrier : ∀ i j, Type (max u w)
  motherAtlas : ∀ i j, ComplexSurfaceAtlas (motherCarrier i j)
  sourceHomeomorph : ∀ i j,
    @Homeomorph
      (CechOverlapSourceTotal D i j)
      (motherCarrier i j)
      (cechOverlapSourceTopology D i j)
      (motherAtlas i j).topology
  targetHomeomorph : ∀ i j,
    @Homeomorph
      (CechOverlapTargetTotal D i j)
      (motherCarrier i j)
      (cechOverlapTargetTopology D i j)
      (motherAtlas i j).topology
  source_atlas_eq : ∀ i j,
    overlapSourceAtlas D i j =
      ComplexSurfaceAtlas.transport
        (motherAtlas i j) (sourceHomeomorph i j)
  target_atlas_eq : ∀ i j,
    overlapTargetAtlas D i j =
      ComplexSurfaceAtlas.transport
        (motherAtlas i j) (targetHomeomorph i j)
  comparison_comp : ∀ i j,
    @Homeomorph.trans
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (motherCarrier i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j)
      (motherAtlas i j).topology
      (toJointlyContinuousTransitionData.homeomorph i j)
      (targetHomeomorph i j) =
      sourceHomeomorph i j

def CommonMotherAtlasTransitionWitness.toHolomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    (W : CommonMotherAtlasTransitionWitness D) :
    JointlyHolomorphicTransitionData D := by
  apply JointlyHolomorphicTransitionData.ofHolomorphicEquiv
    W.toJointlyContinuousTransitionData
  intro i j
  have h := ComplexSurfaceAtlas.commonTransport_holomorphicEquiv
    (W.motherAtlas i j)
    (W.sourceHomeomorph i j)
    (W.targetHomeomorph i j)
    (W.toJointlyContinuousTransitionData.homeomorph i j)
    (W.comparison_comp i j)
  exact ComplexSurfaceAtlas.HolomorphicEquiv.castAtlases
    (W.source_atlas_eq i j).symm
    (W.target_atlas_eq i j).symm
    (HEq.rfl)
    h

theorem overlapTargetMap_eq_overlapSourceMap_of_self
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (z : CechOverlapSourceTotal D i i) :
    overlapTargetMap D i i z = overlapSourceMap D i i z := by
  rcases z with ⟨p, z⟩
  unfold overlapTargetMap overlapTargetInclusion overlapTransitionMap
    overlapSourceMap Function.comp
  simp only [D.transition_self]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem overlapSourceMap_inverse_eq_overlapTargetInclusion_of_self
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (z : CechOverlapTargetTotal D i i) :
    overlapSourceMap D i i (overlapTransitionInverseMap D i i z) =
      overlapTargetInclusion D i i z := by
  rcases z with ⟨p, z⟩
  unfold overlapTransitionInverseMap overlapTargetInclusion
    overlapSourceMap
  simp only [D.transition_self]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

/-! A one-chart (more generally, subsingleton-indexed) cover has no genuine
off-diagonal transition.  The cocycle self-law therefore supplies a fully
constructive base case for the joint-transition interface.  This is useful as
a regression theorem: the new continuity obligations are discharged from the
induced overlap topologies themselves, not postulated globally. -/

noncomputable def jointlyContinuousTransition_of_subsingleton
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B] [Subsingleton I]
    (D : HolomorphicCechDescentData S B I) :
    JointlyContinuousTransitionData D := by
  classical
  refine
    { toFun := fun i j => by
        have hij : j = i := Subsingleton.elim _ _
        subst j
        exact overlapTransitionMap D i i
      invFun := fun i j => by
        have hij : j = i := Subsingleton.elim _ _
        subst j
        exact overlapTransitionInverseMap D i i
      left_inv := by
        intro i j z
        have hij : j = i := Subsingleton.elim _ _
        subst j
        rcases z with ⟨p, z⟩
        simp [overlapTransitionMap, overlapTransitionInverseMap,
          D.transition_self] <;> rfl
      right_inv := by
        intro i j z
        have hij : j = i := Subsingleton.elim _ _
        subst j
        rcases z with ⟨p, z⟩
        simp [overlapTransitionMap, overlapTransitionInverseMap,
          D.transition_self] <;> rfl
      continuous_toFun := by
        intro i j
        have hij : j = i := Subsingleton.elim _ _
        subst j
        letI : TopologicalSpace (CechOverlapSourceTotal D i i) :=
          cechOverlapSourceTopology D i i
        letI : TopologicalSpace (CechOverlapTargetTotal D i i) :=
          cechOverlapTargetTopology D i i
        apply continuous_induced_rng.mpr
        have hmap :
            overlapTargetInclusion D i i ∘ overlapTransitionMap D i i =
              overlapSourceMap D i i := by
          funext z
          exact overlapTargetMap_eq_overlapSourceMap_of_self D i z
        rw [hmap]
        exact continuous_overlapSourceMap D i i
      continuous_invFun := by
        intro i j
        have hij : j = i := Subsingleton.elim _ _
        subst j
        letI : TopologicalSpace (CechOverlapSourceTotal D i i) :=
          cechOverlapSourceTopology D i i
        letI : TopologicalSpace (CechOverlapTargetTotal D i i) :=
          cechOverlapTargetTopology D i i
        apply continuous_induced_rng.mpr
        have hmap :
            overlapSourceMap D i i ∘ overlapTransitionInverseMap D i i =
              overlapTargetInclusion D i i := by
          funext z
          exact overlapSourceMap_inverse_eq_overlapTargetInclusion_of_self D i z
        rw [hmap]
        exact continuous_overlapTargetInclusion D i i
      toFun_agrees := by
        intro i j z
        have hij : j = i := Subsingleton.elim _ _
        subst j
        rfl }

theorem overlapSourceMap_sigma_eq_gluingSource
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    overlapSourceMap D i j ⟨p, z⟩ = gluingSource D p z :=
  rfl

theorem overlapTargetMap_sigma_eq_gluingTarget
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    overlapTargetMap D i j ⟨p, z⟩ = gluingTarget D p z :=
  rfl

theorem gluingStep_iff_overlapMaps
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {x y : LocalTotal D} :
    gluingStep D x y ↔
      ∃ i j, ∃ z : CechOverlapSourceTotal D i j,
        x = overlapSourceMap D i j z ∧
        y = overlapTargetMap D i j z := by
  constructor
  · rintro ⟨i, j, p, z, rfl, rfl⟩
    exact ⟨i, j, ⟨p, z⟩, rfl, rfl⟩
  · rintro ⟨i, j, ⟨p, z⟩, rfl, rfl⟩
    exact ⟨i, j, p, z, rfl, rfl⟩

def gluingStepImage
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (U : Set (LocalTotal D)) : Set (LocalTotal D) :=
  {y | ∃ x ∈ U, gluingStep D x y}

theorem gluingStepImage_eq_iUnion_overlapImages
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (U : Set (LocalTotal D)) :
    gluingStepImage D U =
      ⋃ i, ⋃ j,
        overlapTargetMap D i j ''
          (overlapSourceMap D i j ⁻¹' U) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rcases (gluingStep_iff_overlapMaps D).1 hxy with
      ⟨i, j, z, rfl, rfl⟩
    refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    refine ⟨z, ?_, rfl⟩
    exact hx
  · intro hy
    rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨j, hy⟩
    rcases hy with ⟨z, hzU, rfl⟩
    exact ⟨overlapSourceMap D i j z, hzU,
      (gluingStep_iff_overlapMaps D).2 ⟨i, j, z, rfl, rfl⟩⟩

theorem continuous_overlapTransitionMap_of_witness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) (i j : I) :
    @Continuous
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j)
      (overlapTransitionMap D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  have heq :
      (W.transition_homeomorph i j :
        CechOverlapSourceTotal D i j → CechOverlapTargetTotal D i j) =
        overlapTransitionMap D i j := by
    funext z
    exact W.transition_homeomorph_apply i j z
  rw [← heq]
  exact (W.transition_homeomorph i j).continuous

theorem isOpenMap_overlapTransitionMap_of_witness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) (i j : I) :
    @IsOpenMap
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (cechOverlapSourceTopology D i j)
      (cechOverlapTargetTopology D i j)
      (overlapTransitionMap D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  have heq :
      (W.transition_homeomorph i j :
        CechOverlapSourceTotal D i j → CechOverlapTargetTotal D i j) =
        overlapTransitionMap D i j := by
    funext z
    exact W.transition_homeomorph_apply i j z
  rw [← heq]
  exact (W.transition_homeomorph i j).isOpenMap

theorem continuous_overlapTargetMap_of_witness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) (i j : I) :
    @Continuous
      (CechOverlapSourceTotal D i j) (LocalTotal D)
      (cechOverlapSourceTopology D i j) (localTotalTopology D)
      (overlapTargetMap D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  change Continuous
    (overlapTargetInclusion D i j ∘ overlapTransitionMap D i j)
  exact (continuous_overlapTargetInclusion D i j).comp
    (continuous_overlapTransitionMap_of_witness D W i j)

theorem isOpenMap_overlapTargetMap_of_witness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) (i j : I) :
    @IsOpenMap
      (CechOverlapSourceTotal D i j) (LocalTotal D)
      (cechOverlapSourceTopology D i j) (localTotalTopology D)
      (overlapTargetMap D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  change IsOpenMap
    (overlapTargetInclusion D i j ∘ overlapTransitionMap D i j)
  exact (isOpenMap_overlapTargetInclusion D i j).comp
    (isOpenMap_overlapTransitionMap_of_witness D W i j)

structure OpenGluingWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) where
  gluingStepImage_isOpen : ∀ U : Set (LocalTotal D),
    IsOpen U → IsOpen (gluingStepImage D U)

theorem openGluingWitness_of_totalOverlapHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) :
    OpenGluingWitness D := by
  refine ⟨?_⟩
  intro U hU
  rw [gluingStepImage_eq_iUnion_overlapImages D U]
  apply isOpen_iUnion
  intro i
  apply isOpen_iUnion
  intro j
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  have hpre : @IsOpen
      (CechOverlapSourceTotal D i j)
      (cechOverlapSourceTopology D i j)
      (overlapSourceMap D i j ⁻¹' U) :=
    hU.preimage (continuous_overlapSourceMap D i j)
  exact (isOpenMap_overlapTargetMap_of_witness D W i j)
    _ hpre

theorem quotientMk_preimage_image
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (U : Set (LocalTotal D)) :
    quotientMk D ⁻¹' (quotientMk D '' U) = gluingStepImage D U := by
  ext y
  constructor
  · intro hy
    change quotientMk D y ∈ quotientMk D '' U at hy
    rcases hy with ⟨x, hx, hq⟩
    refine ⟨x, hx, ?_⟩
    have hrel : Relation.EqvGen (gluingStep D) x y := by
      change (gluingSetoid D).r x y
      exact Quotient.exact hq
    exact (gluingEqvGen_iff_gluingStep D).1 hrel
  · intro hy
    rcases hy with ⟨x, hx, hxy⟩
    change quotientMk D y ∈ quotientMk D '' U
    refine ⟨x, hx, ?_⟩
    change quotientMk D x = quotientMk D y
    apply Quotient.sound
    change Relation.EqvGen (gluingStep D) x y
    exact Relation.EqvGen.rel _ _ hxy

theorem isOpenMap_quotientMk_of_openGluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : OpenGluingWitness D) :
    @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D) := by
  letI : ∀ i, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    fun i => (D.localFamily i).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  intro U hU
  have hquot : @Topology.IsQuotientMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D) := by
    exact @isQuotientMap_quotient_mk'
      (LocalTotal D) (localTotalTopology D) (gluingSetoid D)
  have hcoind : Topology.IsCoinducing (quotientMk D) := hquot.isCoinducing
  apply ((Topology.isCoinducing_iff.mp hcoind)
    (quotientMk D '' U)).mp
  rw [quotientMk_preimage_image D U]
  exact W.gluingStepImage_isOpen U hU

theorem descendedProjection_gluingSource
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    descendedProjection D (quotientMk D (gluingSource D p z)) = p.1 :=
  rfl

theorem descendedProjection_gluingTarget
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    descendedProjection D (quotientMk D (gluingTarget D p z)) = p.1 :=
  rfl

/-! ### Local maps into the descended total space

The quotient construction has a canonical map from each local total space.
The maps are not yet declared to be local homeomorphisms: that requires the
next chart-injectivity argument.  What is already concrete here is their
continuity, their compatibility with the descended base, and their agreement
on every recorded overlap transition.
-/

def localQuotient
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I) :
    ComplexSurfaceFamily.Total (D.localFamily i).family → DescendedTotal D :=
  fun z => quotientMk D ⟨i, z⟩

theorem localQuotient_injective
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I) :
    Function.Injective (localQuotient D i) := by
  intro z z' h
  have hrel : Relation.EqvGen (gluingStep D)
      (⟨i, z⟩ : LocalTotal D) ⟨i, z'⟩ := by
    change quotientMk D ⟨i, z⟩ = quotientMk D ⟨i, z'⟩ at h
    change (gluingSetoid D).r
      (⟨i, z⟩ : LocalTotal D) ⟨i, z'⟩
    exact Quotient.exact h
  have hstep : gluingStep D (⟨i, z⟩ : LocalTotal D) ⟨i, z'⟩ :=
    (gluingEqvGen_iff_gluingStep D).1 hrel
  rcases hstep with ⟨a, b, p, w, hx, hy⟩
  have ha : a = i := by
    exact (congrArg Sigma.fst hx).symm
  have hb : b = i := by
    exact (congrArg Sigma.fst hy).symm
  cases ha
  cases hb
  have hw := D.transition_self i p
  have hz : z = (gluingSource D p w).2 :=
    eq_of_heq (Sigma.ext_iff.mp hx).2
  have hz' : z' = (gluingTarget D p w).2 :=
    eq_of_heq (Sigma.ext_iff.mp hy).2
  have hst : (gluingSource D p w).2 = (gluingTarget D p w).2 := by
    unfold gluingSource gluingTarget
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      have hp : CechOverlap.leftPoint D.cover i i p =
          CechOverlap.rightPoint D.cover i i p := by
        apply Subtype.ext
        rfl
      cases hp
      rw [hw]
      rfl
  exact hz.trans (hst.trans hz'.symm)

theorem localQuotient_surjective_of_subsingleton
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    [Subsingleton I]
    (D : HolomorphicCechDescentData S B I) (i : I) :
    Function.Surjective (localQuotient D i) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rcases x with ⟨j, z⟩
  have hij : j = i := Subsingleton.elim _ _
  subst j
  exact ⟨z, rfl⟩

theorem localQuotient_projection
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (z : ComplexSurfaceFamily.Total (D.localFamily i).family) :
    descendedProjection D (localQuotient D i z) =
      (z.1 : B) :=
  rfl

theorem continuous_localQuotient
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I) :
    @Continuous
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (DescendedTotal D)
      (D.localFamily i).family.totalTopology inferInstance
      (localQuotient D i) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  exact continuous_quotient_mk'.comp continuous_sigmaMk

theorem localQuotient_transition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    {i j : I} (p : CechOverlap D.cover i j)
    (z : ((D.localFamily i).family.fiber
      (CechOverlap.leftPoint D.cover i j p)).carrier) :
    localQuotient D i
        ⟨CechOverlap.leftPoint D.cover i j p, z⟩ =
      localQuotient D j
        ⟨CechOverlap.rightPoint D.cover i j p, D.transition i j p z⟩ :=
  quotientMk_gluingStep D p z

/-! ### The local-homeomorphism boundary

The quotient topology gives continuity for free, but openness of the quotient
map is the genuinely geometric part of the gluing theorem.  We keep that
obligation explicit as a hypothesis here.  Once it is supplied, the local
maps are open embeddings, so their chart images are open and the chart
homeomorphisms are obtained by restriction of an actual embedding.
-/

theorem isOpenMap_localQuotient_of_isOpenMap_quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @IsOpenMap
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (DescendedTotal D)
      (D.localFamily i).family.totalTopology inferInstance
      (localQuotient D i) := by
  letI : ∀ k, TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily k).family) :=
    fun k => (D.localFamily k).family.totalTopology
  letI : TopologicalSpace (LocalTotal D) := localTotalTopology D
  change IsOpenMap ((quotientMk D) ∘ (Sigma.mk i))
  exact hquot.comp isOpenMap_sigmaMk

theorem isOpenEmbedding_localQuotient_of_isOpenMap_quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @Topology.IsOpenEmbedding
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (DescendedTotal D)
      (D.localFamily i).family.totalTopology inferInstance
      (localQuotient D i) :=
  by
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
      (D.localFamily i).family.totalTopology
    exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_localQuotient D i)
      (localQuotient_injective D i)
      (isOpenMap_localQuotient_of_isOpenMap_quotientMk D i hquot)

noncomputable def localQuotientHomeomorph_of_isOpenMap_of_subsingleton
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    [Subsingleton I]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @Homeomorph
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (DescendedTotal D)
      (D.localFamily i).family.totalTopology inferInstance := by
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  exact
    (isOpenEmbedding_localQuotient_of_isOpenMap_quotientMk D i hquot).isEmbedding
      |>.toHomeomorphOfSurjective
        (localQuotient_surjective_of_subsingleton D i)

def localChartImage
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (c : (D.localFamily i).atlas.index) : Set (DescendedTotal D) :=
  localQuotient D i '' ((D.localFamily i).atlas.chart c).domain

noncomputable def localChartHomeomorph_of_isOpenMap_quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (c : (D.localFamily i).atlas.index) :
    @Homeomorph
      {z // z ∈ ((D.localFamily i).atlas.chart c).domain}
      {q // q ∈ localChartImage D i c}
      (TopologicalSpace.induced Subtype.val
        (D.localFamily i).family.totalTopology)
      (TopologicalSpace.induced Subtype.val inferInstance) := by
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  exact
      (isOpenEmbedding_localQuotient_of_isOpenMap_quotientMk D i hquot).isEmbedding
      |>.homeomorphImage ((D.localFamily i).atlas.chart c).domain

@[simp] theorem localChartHomeomorph_apply_val
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (c : (D.localFamily i).atlas.index)
    (z : {x // x ∈ ((D.localFamily i).atlas.chart c).domain}) :
    (localChartHomeomorph_of_isOpenMap_quotientMk D i hquot c z).1 =
      localQuotient D i z.1 := by
  rfl

theorem isOpen_localChartImage_of_isOpenMap_quotientMk
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) (i : I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (c : (D.localFamily i).atlas.index) :
    IsOpen (localChartImage D i c) := by
  have hdomain : @IsOpen
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (D.localFamily i).family.totalTopology
      ((D.localFamily i).atlas.chart c).domain := by
    rw [← (D.localFamily i).topology_eq]
    exact (D.localFamily i).atlas.chart c |>.domain_open
  exact (isOpenMap_localQuotient_of_isOpenMap_quotientMk D i hquot)
    _ hdomain

theorem isOpenEmbedding_localQuotient_of_openGluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : OpenGluingWitness D) (i : I) :
    @Topology.IsOpenEmbedding
      (ComplexSurfaceFamily.Total (D.localFamily i).family)
      (DescendedTotal D)
      (D.localFamily i).family.totalTopology inferInstance
      (localQuotient D i) :=
  isOpenEmbedding_localQuotient_of_isOpenMap_quotientMk D i
    (isOpenMap_quotientMk_of_openGluing D W)

theorem isOpen_localChartImage_of_openGluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : OpenGluingWitness D) (i : I)
    (c : (D.localFamily i).atlas.index) :
    IsOpen (localChartImage D i c) :=
  isOpen_localChartImage_of_isOpenMap_quotientMk D i
    (isOpenMap_quotientMk_of_openGluing D W) c

noncomputable def localChartHomeomorph_of_openGluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : OpenGluingWitness D) (i : I)
    (c : (D.localFamily i).atlas.index) :
    @Homeomorph
      {z // z ∈ ((D.localFamily i).atlas.chart c).domain}
      {q // q ∈ localChartImage D i c}
      (TopologicalSpace.induced Subtype.val
        (D.localFamily i).family.totalTopology)
      (TopologicalSpace.induced Subtype.val inferInstance) :=
  localChartHomeomorph_of_isOpenMap_quotientMk D i
    (isOpenMap_quotientMk_of_openGluing D W) c

theorem localChartImage_cover_univ
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :
    ⋃ i, ⋃ c, localChartImage D i c = Set.univ := by
  ext q
  constructor
  · intro _
    trivial
  · intro _
    refine Quotient.inductionOn q ?_
    intro x
    rcases (D.localFamily x.1).atlas.has_chart_at
      ((D.localFamily x.1).cover x.2) with ⟨c, hc⟩
    refine Set.mem_iUnion.2 ⟨x.1, Set.mem_iUnion.2 ⟨c, ?_⟩⟩
    exact ⟨x.2, hc, rfl⟩

/-! ### The descended chart family

The topological part of the descended atlas can now be assembled.  Its index
is the dependent sum of local chart indices; the chart domain is the open
image in the quotient, and its coordinate map is the local chart composed
with the inverse of the local quotient homeomorphism.  The remaining
holomorphic transition statement is deliberately a separate witness: the
fibrewise `AtlasHolomorphicEquiv` fields in `HolomorphicCechDescentData` do
not, by themselves, assert joint holomorphic dependence on the base.
-/

abbrev DescendedChartIndex
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I) :=
  Sigma fun i => (D.localFamily i).atlas.index

noncomputable def descendedChart
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (a : DescendedChartIndex D) :
    @ComplexSurfaceChart (DescendedTotal D) inferInstance := by
  rcases a with ⟨i, c⟩
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      {z // z ∈ ((D.localFamily i).atlas.chart c).domain} :=
    TopologicalSpace.induced Subtype.val
      (D.localFamily i).family.totalTopology
  let hlocal := localChartHomeomorph_of_isOpenMap_quotientMk D i hquot c
  let hchart : @Homeomorph
      {z // z ∈ ((D.localFamily i).atlas.chart c).domain}
      {p // p ∈ ((D.localFamily i).atlas.chart c).range}
      (TopologicalSpace.induced Subtype.val
        (D.localFamily i).family.totalTopology)
      inferInstance :=
    retopologizeSourceHomeomorph
      ((D.localFamily i).atlas.chart c).chart
      (congrArg (fun t => TopologicalSpace.induced Subtype.val t)
        (D.localFamily i).topology_eq)
  exact
    { domain := localChartImage D i c
      range := ((D.localFamily i).atlas.chart c).range
      domain_open := isOpen_localChartImage_of_isOpenMap_quotientMk D i hquot c
      range_open := ((D.localFamily i).atlas.chart c).range_open
      chart := hlocal.symm.trans hchart }

noncomputable def descendedChartFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @ComplexSurfaceChartFamily (DescendedTotal D) :=
  { topology := inferInstance
    index := DescendedChartIndex D
    chart := descendedChart D hquot
    coverSet := Set.univ
    covers := by
      intro q hq
      have hmem : q ∈ ⋃ i, ⋃ c, localChartImage D i c := by
        rw [localChartImage_cover_univ D]
        trivial
      rcases Set.mem_iUnion.1 hmem with ⟨i, hmem⟩
      rcases Set.mem_iUnion.1 hmem with ⟨c, hqc⟩
      refine ⟨⟨i, c⟩, ?_⟩
      change q ∈ localChartImage D i c
      exact hqc }

noncomputable def descendedChartFamily_of_openGluing
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : OpenGluingWitness D) :
    @ComplexSurfaceChartFamily (DescendedTotal D) :=
  descendedChartFamily D (isOpenMap_quotientMk_of_openGluing D W)

noncomputable def descendedChartFamily_of_totalOverlapHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (W : TotalOverlapHomeomorphWitness D) :
    @ComplexSurfaceChartFamily (DescendedTotal D) :=
  descendedChartFamily_of_openGluing D
    (openGluingWitness_of_totalOverlapHomeomorph D W)

noncomputable def openGluingWitness_of_jointlyContinuous
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (J : JointlyContinuousTransitionData D) :
    OpenGluingWitness D :=
  openGluingWitness_of_totalOverlapHomeomorph D
    (totalOverlapHomeomorphWitness_of_jointlyContinuous D J)

noncomputable def descendedChartFamily_of_jointlyContinuous
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (J : JointlyContinuousTransitionData D) :
    @ComplexSurfaceChartFamily (DescendedTotal D) :=
  descendedChartFamily_of_openGluing D
    (openGluingWitness_of_jointlyContinuous D J)

theorem descendedChart_overlap_subset_joint_overlap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D)
    (i j : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    {p : ℂ × ℂ} (hp : p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩)) :
    p ∈ ComplexSurfaceChart.overlap
      ((overlapSourceAtlas D i j).chart c)
      (((overlapTargetAtlas D i j).chart d).transport
        (J.toJointlyContinuousTransitionData.homeomorph i j)) := by
  classical
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  change ∃ hpRange : p ∈
      ((descendedChartFamily D hquot).chart ⟨i, c⟩).range,
    (((descendedChartFamily D hquot).chart ⟨i, c⟩).chart.symm
      ⟨p, hpRange⟩).1 ∈
      ((descendedChartFamily D hquot).chart ⟨j, d⟩).domain at hp
  rcases hp with ⟨hpRange, hpTarget⟩
  let sourceChart := (descendedChartFamily D hquot).chart ⟨i, c⟩
  let targetChart := (descendedChartFamily D hquot).chart ⟨j, d⟩
  let q : DescendedTotal D :=
    (sourceChart.chart.symm ⟨p, hpRange⟩).1
  have hqSource : q ∈ localChartImage D i c := by
    change q ∈ sourceChart.domain
    exact (sourceChart.chart.symm ⟨p, hpRange⟩).property
  have hqTarget : q ∈ localChartImage D j d := by
    change q ∈ targetChart.domain at hpTarget
    exact hpTarget
  rcases hqSource with ⟨z, hzDomain, hzq⟩
  rcases hqTarget with ⟨w, hwDomain, hwq⟩
  have hquotient : quotientMk D (⟨i, z⟩ : LocalTotal D) =
      quotientMk D (⟨j, w⟩ : LocalTotal D) := by
    change localQuotient D i z = localQuotient D j w
    exact hzq.trans hwq.symm
  have hstep : gluingStep D (⟨i, z⟩ : LocalTotal D)
      (⟨j, w⟩ : LocalTotal D) :=
    (quotientMk_eq_iff_gluingStep D).1 hquotient
  rcases hstep with ⟨i₀, j₀, overlapPoint, fibrePoint, hsource, htarget⟩
  have hi₀ : i₀ = i := by
    exact (congrArg Sigma.fst hsource).symm
  have hj₀ : j₀ = j := by
    exact (congrArg Sigma.fst htarget).symm
  subst i₀
  subst j₀
  let overlapSourcePoint : CechOverlapSourceTotal D i j :=
    ⟨overlapPoint, fibrePoint⟩
  have hzSource : z =
      (overlapSourceMap D i j overlapSourcePoint).2 := by
    exact eq_of_heq (Sigma.ext_iff.mp hsource).2
  have hwTarget : w =
      (overlapTargetMap D i j overlapSourcePoint).2 := by
    exact eq_of_heq (Sigma.ext_iff.mp htarget).2
  let zDomain : {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    ⟨z, hzDomain⟩
  let hlocal := localChartHomeomorph_of_isOpenMap_quotientMk D i hquot c
  have hlocalValue : (hlocal zDomain).1 = q := by
    rw [localChartHomeomorph_apply_val]
    exact hzq
  have hsourceInverse :
      sourceChart.chart.symm ⟨p, hpRange⟩ = hlocal zDomain := by
    apply Subtype.ext
    exact hlocalValue.symm
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    TopologicalSpace.induced Subtype.val
      (D.localFamily i).family.totalTopology
  have hcoordinate : p =
      (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
    have hleft := sourceChart.chart.apply_symm_apply
      (⟨p, hpRange⟩ : {q // q ∈ sourceChart.range})
    have hleftVal := congrArg Subtype.val hleft
    calc
      p = (sourceChart.chart
          (sourceChart.chart.symm ⟨p, hpRange⟩)).1 := hleftVal.symm
      _ = (sourceChart.chart (hlocal zDomain)).1 := by
        exact congrArg (fun x => (sourceChart.chart x).1) hsourceInverse
      _ = (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
        change
          (retopologizeSourceHomeomorph
            ((D.localFamily i).atlas.chart c).chart _
            (hlocal.symm (hlocal zDomain))).1 = _
        rw [hlocal.symm_apply_apply]
        rw [retopologizeSourceHomeomorph_apply]
  have hzFibre :
      overlapSourceFibreMap D i j overlapSourcePoint = z := by
    change (overlapSourceMap D i j overlapSourcePoint).2 = z
    exact hzSource.symm
  have hsourceOverlapDomain :
      overlapSourcePoint ∈ ((overlapSourceAtlas D i j).chart c).domain := by
    change overlapSourceFibreMap D i j overlapSourcePoint ∈
      ((D.localFamily i).atlas.chart c).domain
    rw [hzFibre]
    exact hzDomain
  have hsourceCoord :
      (((overlapSourceAtlas D i j).chart c).chart
        ⟨overlapSourcePoint, hsourceOverlapDomain⟩).1 = p := by
    have hcoord := overlapSourceAtlas_chart_apply_val D i j c
      overlapSourcePoint hsourceOverlapDomain (by
        rw [hzFibre]
        exact hzDomain)
    calc
      (((overlapSourceAtlas D i j).chart c).chart
          ⟨overlapSourcePoint, hsourceOverlapDomain⟩).1 =
          (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
            simpa [zDomain, hzFibre] using hcoord
      _ = p := hcoordinate.symm
  have hsourceRange :
      p ∈ ((overlapSourceAtlas D i j).chart c).range := by
    rw [← hsourceCoord]
    exact (((overlapSourceAtlas D i j).chart c).chart
      ⟨overlapSourcePoint, hsourceOverlapDomain⟩).property
  have htargetOverlapDomain :
      overlapTransitionMap D i j overlapSourcePoint ∈
        ((overlapTargetAtlas D i j).chart d).domain := by
    change overlapTargetFibreMap D i j
        (overlapTransitionMap D i j overlapSourcePoint) ∈
      ((D.localFamily j).atlas.chart d).domain
    have htargetFibre :
        overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint) =
          (overlapTargetMap D i j overlapSourcePoint).2 := by
      rfl
    rw [htargetFibre, ← hwTarget]
    exact hwDomain
  let e := J.toJointlyContinuousTransitionData.homeomorph i j
  have hepoint : e overlapSourcePoint =
      overlapTransitionMap D i j overlapSourcePoint := by
    rw [JointlyContinuousTransitionData.homeomorph_apply]
    exact J.toJointlyContinuousTransitionData.toFun_agrees i j
      overlapSourcePoint
  have htargetTransportDomain :
      overlapSourcePoint ∈
        (((overlapTargetAtlas D i j).chart d).transport e).domain := by
    change e overlapSourcePoint ∈
      ((overlapTargetAtlas D i j).chart d).domain
    rw [hepoint]
    exact htargetOverlapDomain
  have hsourcePointEq :
      ((overlapSourceAtlas D i j).chart c).chart.symm
          ⟨p, hsourceRange⟩ =
        ⟨overlapSourcePoint, hsourceOverlapDomain⟩ := by
    apply ((overlapSourceAtlas D i j).chart c).chart.injective
    apply Subtype.ext
    simpa using hsourceCoord.symm
  refine ⟨hsourceRange, ?_⟩
  change
    (((overlapSourceAtlas D i j).chart c).chart.symm
      ⟨p, hsourceRange⟩).1 ∈
      (((overlapTargetAtlas D i j).chart d).transport
        (J.toJointlyContinuousTransitionData.homeomorph i j)).domain
  rw [hsourcePointEq]
  exact htargetTransportDomain

noncomputable def jointTransitionHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (J : JointlyHolomorphicTransitionData D) (i j : I) :
    @Homeomorph
      (CechOverlapSourceTotal D i j)
      (CechOverlapTargetTotal D i j)
      (overlapSourceAtlas D i j).topology
    (overlapTargetAtlas D i j).topology := by
  exact retopologizeBothHomeomorph
    (J.toJointlyContinuousTransitionData.homeomorph i j)
    (overlapSourceAtlas_topology D i j).symm
    (overlapTargetAtlas_topology D i j).symm

@[simp] theorem jointTransitionHomeomorph_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (J : JointlyHolomorphicTransitionData D) (i j : I)
    (z : CechOverlapSourceTotal D i j) :
    jointTransitionHomeomorph D J i j z =
      J.toJointlyContinuousTransitionData.homeomorph i j z := by
  simp [jointTransitionHomeomorph]

theorem descendedChart_transitionMap_eq_retagged_joint_transition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D)
    (i j : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    {p : ℂ × ℂ} (hp : p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩)) :
    ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩) p =
      ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i j).chart c)
        (((overlapTargetAtlas D i j).chart d).transport
          (jointTransitionHomeomorph D J i j)) p := by
  classical
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  change ∃ hpRange : p ∈
      ((descendedChartFamily D hquot).chart ⟨i, c⟩).range,
    (((descendedChartFamily D hquot).chart ⟨i, c⟩).chart.symm
      ⟨p, hpRange⟩).1 ∈
      ((descendedChartFamily D hquot).chart ⟨j, d⟩).domain at hp
  rcases hp with ⟨hpRange, hpTarget⟩
  let sourceChart := (descendedChartFamily D hquot).chart ⟨i, c⟩
  let targetChart := (descendedChartFamily D hquot).chart ⟨j, d⟩
  let q : DescendedTotal D :=
    (sourceChart.chart.symm ⟨p, hpRange⟩).1
  have hqSource : q ∈ localChartImage D i c := by
    change q ∈ sourceChart.domain
    exact (sourceChart.chart.symm ⟨p, hpRange⟩).property
  have hqTarget : q ∈ localChartImage D j d := by
    change q ∈ targetChart.domain at hpTarget
    exact hpTarget
  rcases hqSource with ⟨z, hzDomain, hzq⟩
  have hqTargetImage : q ∈ localChartImage D j d := hqTarget
  rcases hqTarget with ⟨w, hwDomain, hwq⟩
  have hquotient : quotientMk D (⟨i, z⟩ : LocalTotal D) =
      quotientMk D (⟨j, w⟩ : LocalTotal D) := by
    change localQuotient D i z = localQuotient D j w
    exact hzq.trans hwq.symm
  have hstep : gluingStep D (⟨i, z⟩ : LocalTotal D)
      (⟨j, w⟩ : LocalTotal D) :=
    (quotientMk_eq_iff_gluingStep D).1 hquotient
  rcases hstep with ⟨i₀, j₀, overlapPoint, fibrePoint, hsource, htarget⟩
  have hi₀ : i₀ = i := by
    exact (congrArg Sigma.fst hsource).symm
  have hj₀ : j₀ = j := by
    exact (congrArg Sigma.fst htarget).symm
  subst i₀
  subst j₀
  let overlapSourcePoint : CechOverlapSourceTotal D i j :=
    ⟨overlapPoint, fibrePoint⟩
  have hzSource : z =
      (overlapSourceMap D i j overlapSourcePoint).2 := by
    exact eq_of_heq (Sigma.ext_iff.mp hsource).2
  have hwTarget : w =
      (overlapTargetMap D i j overlapSourcePoint).2 := by
    exact eq_of_heq (Sigma.ext_iff.mp htarget).2
  let zDomain : {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    ⟨z, hzDomain⟩
  let wDomain : {x // x ∈ ((D.localFamily j).atlas.chart d).domain} :=
    ⟨w, hwDomain⟩
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    TopologicalSpace.induced Subtype.val
      (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
    (D.localFamily j).family.totalTopology
  letI : TopologicalSpace
      {x // x ∈ ((D.localFamily j).atlas.chart d).domain} :=
    TopologicalSpace.induced Subtype.val
      (D.localFamily j).family.totalTopology
  let hlocal := localChartHomeomorph_of_isOpenMap_quotientMk D i hquot c
  let hlocalTarget :=
    localChartHomeomorph_of_isOpenMap_quotientMk D j hquot d
  have hlocalValue : (hlocal zDomain).1 = q := by
    rw [localChartHomeomorph_apply_val]
    exact hzq
  have hlocalTargetValue : (hlocalTarget wDomain).1 = q := by
    rw [localChartHomeomorph_apply_val]
    exact hwq
  have hsourceInverse :
      sourceChart.chart.symm ⟨p, hpRange⟩ = hlocal zDomain := by
    apply Subtype.ext
    exact hlocalValue.symm
  have hsourceCoordinate : p =
      (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
    have hleft := sourceChart.chart.apply_symm_apply
      (⟨p, hpRange⟩ : {q // q ∈ sourceChart.range})
    have hleftVal := congrArg Subtype.val hleft
    calc
      p = (sourceChart.chart
          (sourceChart.chart.symm ⟨p, hpRange⟩)).1 := hleftVal.symm
      _ = (sourceChart.chart (hlocal zDomain)).1 := by
        exact congrArg (fun x => (sourceChart.chart x).1) hsourceInverse
      _ = (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
        change
          (retopologizeSourceHomeomorph
            ((D.localFamily i).atlas.chart c).chart _
            (hlocal.symm (hlocal zDomain))).1 = _
        rw [hlocal.symm_apply_apply]
        rw [retopologizeSourceHomeomorph_apply]
  have hzFibre :
      overlapSourceFibreMap D i j overlapSourcePoint = z := by
    change (overlapSourceMap D i j overlapSourcePoint).2 = z
    exact hzSource.symm
  have hsourceOverlapDomain :
      overlapSourcePoint ∈ ((overlapSourceAtlas D i j).chart c).domain := by
    change overlapSourceFibreMap D i j overlapSourcePoint ∈
      ((D.localFamily i).atlas.chart c).domain
    rw [hzFibre]
    exact hzDomain
  have hsourceCoord :
      (((overlapSourceAtlas D i j).chart c).chart
        ⟨overlapSourcePoint, hsourceOverlapDomain⟩).1 = p := by
    have hcoord := overlapSourceAtlas_chart_apply_val D i j c
      overlapSourcePoint hsourceOverlapDomain (by
        rw [hzFibre]
        exact hzDomain)
    calc
      (((overlapSourceAtlas D i j).chart c).chart
          ⟨overlapSourcePoint, hsourceOverlapDomain⟩).1 =
          (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
            simpa [zDomain, hzFibre] using hcoord
      _ = p := hsourceCoordinate.symm
  have hsourceRange :
      p ∈ ((overlapSourceAtlas D i j).chart c).range := by
    rw [← hsourceCoord]
    exact (((overlapSourceAtlas D i j).chart c).chart
      ⟨overlapSourcePoint, hsourceOverlapDomain⟩).property
  have htargetOverlapDomain :
      overlapTransitionMap D i j overlapSourcePoint ∈
        ((overlapTargetAtlas D i j).chart d).domain := by
    change overlapTargetFibreMap D i j
        (overlapTransitionMap D i j overlapSourcePoint) ∈
      ((D.localFamily j).atlas.chart d).domain
    have htargetFibre :
        overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint) =
          (overlapTargetMap D i j overlapSourcePoint).2 := by
      rfl
    rw [htargetFibre, ← hwTarget]
    exact hwDomain
  have htargetCoord :
      (((overlapTargetAtlas D i j).chart d).chart
        ⟨overlapTransitionMap D i j overlapSourcePoint,
          htargetOverlapDomain⟩).1 =
      (((D.localFamily j).atlas.chart d).chart wDomain).1 := by
    have hcoord := overlapTargetAtlas_chart_apply_val D i j d
      (overlapTransitionMap D i j overlapSourcePoint)
      htargetOverlapDomain (by
        change overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint) ∈
          ((D.localFamily j).atlas.chart d).domain
        have htargetFibre :
            overlapTargetFibreMap D i j
                (overlapTransitionMap D i j overlapSourcePoint) =
              (overlapTargetMap D i j overlapSourcePoint).2 := by
          rfl
        rw [htargetFibre, ← hwTarget]
        exact hwDomain)
    have htargetFibreMap :
        overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint) =
          (overlapTargetMap D i j overlapSourcePoint).2 := by
      rfl
    have htargetFibre :
        overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint) = w := by
      exact htargetFibreMap.trans hwTarget.symm
    have hpoint :
        (⟨overlapTargetFibreMap D i j
            (overlapTransitionMap D i j overlapSourcePoint), by
              rw [htargetFibre]
              exact hwDomain⟩ :
          {x // x ∈ ((D.localFamily j).atlas.chart d).domain}) =
          wDomain := by
      apply Subtype.ext
      exact htargetFibre
    rw [hpoint] at hcoord
    exact hcoord
  let e := jointTransitionHomeomorph D J i j
  have hepoint : e overlapSourcePoint =
      overlapTransitionMap D i j overlapSourcePoint := by
    rw [jointTransitionHomeomorph_apply]
    rw [JointlyContinuousTransitionData.homeomorph_apply]
    exact J.toJointlyContinuousTransitionData.toFun_agrees i j
      overlapSourcePoint
  have htargetTransportDomain :
      overlapSourcePoint ∈
        (((overlapTargetAtlas D i j).chart d).transport e).domain := by
    change e overlapSourcePoint ∈
      ((overlapTargetAtlas D i j).chart d).domain
    rw [hepoint]
    exact htargetOverlapDomain
  have hsourcePointEq :
      ((overlapSourceAtlas D i j).chart c).chart.symm
          ⟨p, hsourceRange⟩ =
        ⟨overlapSourcePoint, hsourceOverlapDomain⟩ := by
    apply ((overlapSourceAtlas D i j).chart c).chart.injective
    apply Subtype.ext
    simpa using hsourceCoord.symm
  have hjointOverlap : p ∈ ComplexSurfaceChart.overlap
      ((overlapSourceAtlas D i j).chart c)
      (((overlapTargetAtlas D i j).chart d).transport e) := by
    refine ⟨hsourceRange, ?_⟩
    change e
        (((overlapSourceAtlas D i j).chart c).chart.symm
          ⟨p, hsourceRange⟩).1 ∈
      ((overlapTargetAtlas D i j).chart d).domain
    rw [hsourcePointEq]
    exact htargetTransportDomain
  have hdescTargetInput :
      (⟨(sourceChart.chart.symm ⟨p, hpRange⟩).1,
        by
          change (sourceChart.chart.symm ⟨p, hpRange⟩).1 ∈
            targetChart.domain
          exact hpTarget⟩ : {x // x ∈ targetChart.domain}) =
        ⟨q, hqTargetImage⟩ := by
    apply Subtype.ext
    rfl
  have hlocalTargetPoint :
      hlocalTarget.symm ⟨q, hqTargetImage⟩ = wDomain := by
    apply hlocalTarget.injective
    apply Subtype.ext
    rw [hlocalTarget.apply_symm_apply]
    exact hlocalTargetValue.symm
  have hdescTargetCoord :
      (targetChart.chart ⟨q, hqTargetImage⟩).1 =
        (((D.localFamily j).atlas.chart d).chart wDomain).1 := by
    change
      (retopologizeSourceHomeomorph
        ((D.localFamily j).atlas.chart d).chart _
        (hlocalTarget.symm ⟨q, hqTargetImage⟩)).1 = _
    rw [hlocalTargetPoint]
    rw [retopologizeSourceHomeomorph_apply]
  have hdescTransition :
      ComplexSurfaceChart.transitionMap sourceChart targetChart p =
        (((D.localFamily j).atlas.chart d).chart wDomain).1 := by
    rw [ComplexSurfaceChart.transitionMap_on_overlap
      sourceChart targetChart ⟨hpRange, hpTarget⟩]
    rw [hdescTargetInput]
    exact hdescTargetCoord
  let xTransport :
      {x // x ∈ (((overlapTargetAtlas D i j).chart d).transport e).domain} :=
    ⟨((overlapSourceAtlas D i j).chart c).chart.symm
        ⟨p, hsourceRange⟩, by
          exact ComplexSurfaceChart.overlapSourceRangeProof_spec
            ((overlapSourceAtlas D i j).chart c)
            (((overlapTargetAtlas D i j).chart d).transport e)
            hjointOverlap⟩
  have hxTransport : xTransport =
      ⟨overlapSourcePoint, htargetTransportDomain⟩ := by
    apply Subtype.ext
    simpa [xTransport] using congrArg Subtype.val hsourcePointEq
  have hjointTransition :
      ComplexSurfaceChart.transitionMap
          ((overlapSourceAtlas D i j).chart c)
          (((overlapTargetAtlas D i j).chart d).transport e) p =
        (((D.localFamily j).atlas.chart d).chart wDomain).1 := by
    rw [ComplexSurfaceChart.transitionMap_on_overlap
      ((overlapSourceAtlas D i j).chart c)
      (((overlapTargetAtlas D i j).chart d).transport e) hjointOverlap]
    change
      ((((overlapTargetAtlas D i j).chart d).transport e).chart xTransport).1 = _
    have heDomain : e overlapSourcePoint ∈
        ((overlapTargetAtlas D i j).chart d).domain := by
      change e overlapSourcePoint ∈
        ((overlapTargetAtlas D i j).chart d).domain
      rw [hepoint]
      exact htargetOverlapDomain
    let yTarget : {x // x ∈ ((overlapTargetAtlas D i j).chart d).domain} :=
      ⟨e overlapSourcePoint, heDomain⟩
    have htransportVal :
        ((((overlapTargetAtlas D i j).chart d).transport e).chart
          ⟨overlapSourcePoint, htargetTransportDomain⟩).1 =
          (((overlapTargetAtlas D i j).chart d).chart yTarget).1 := by
      have htransportVal' := ComplexSurfaceChart.transport_chart_val
        (e := e) (A := (overlapTargetAtlas D i j).chart d)
        (x := overlapSourcePoint) (hx := htargetTransportDomain)
      simpa [yTarget] using htransportVal'
    have htargetPoint :
        yTarget =
        ⟨overlapTransitionMap D i j overlapSourcePoint,
          htargetOverlapDomain⟩ := by
      apply Subtype.ext
      exact hepoint
    calc
      ((((overlapTargetAtlas D i j).chart d).transport e).chart xTransport).1 =
          ((((overlapTargetAtlas D i j).chart d).transport e).chart
            ⟨overlapSourcePoint, htargetTransportDomain⟩).1 := by
              rw [hxTransport]
      _ = (((overlapTargetAtlas D i j).chart d).chart
          yTarget).1 := htransportVal
      _ = (((overlapTargetAtlas D i j).chart d).chart
          ⟨overlapTransitionMap D i j overlapSourcePoint,
            htargetOverlapDomain⟩).1 := by
          exact congrArg
            (fun x => (((overlapTargetAtlas D i j).chart d).chart x).1)
            htargetPoint
      _ = (((D.localFamily j).atlas.chart d).chart wDomain).1 := htargetCoord
  exact hdescTransition.trans hjointTransition.symm

theorem descendedChart_transitionMap_eq_joint_transition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D)
    (i j : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    {p : ℂ × ℂ} (hp : p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩)) :
    ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩) p =
      ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i j).chart c)
        (((overlapTargetAtlas D i j).chart d).transport
          (J.toJointlyContinuousTransitionData.homeomorph i j)) p := by
  classical
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  let source := (overlapSourceAtlas D i j).chart c
  let target := (overlapTargetAtlas D i j).chart d
  let e := jointTransitionHomeomorph D J i j
  let h := J.toJointlyContinuousTransitionData.homeomorph i j
  have heq (x : CechOverlapSourceTotal D i j) :
      e x = h x := by
    simp [e, h]
  have hpDirect : p ∈ ComplexSurfaceChart.overlap source
      (target.transport h) := by
    exact descendedChart_overlap_subset_joint_overlap
      D hquot J i j c d hp
  have hpRetagged : p ∈ ComplexSurfaceChart.overlap source
      (target.transport e) := by
    rcases hpDirect with ⟨hpRange, hpTarget⟩
    refine ⟨hpRange, ?_⟩
    change e (source.chart.symm ⟨p, hpRange⟩).1 ∈ target.domain
    change h (source.chart.symm ⟨p, hpRange⟩).1 ∈ target.domain at hpTarget
    rw [heq]
    exact hpTarget
  have htransitionEq :
      ComplexSurfaceChart.transitionMap source (target.transport e) p =
        ComplexSurfaceChart.transitionMap source (target.transport h) p := by
    let rE := ComplexSurfaceChart.overlapSourceRangeProof
      source (target.transport e) hpRetagged
    let rH := ComplexSurfaceChart.overlapSourceRangeProof
      source (target.transport h) hpDirect
    have hr : rE = rH := Subsingleton.elim _ _
    have hsourcePoint : source.chart.symm ⟨p, rE⟩ =
        source.chart.symm ⟨p, rH⟩ := by
      rw [hr]
    let xE := source.chart.symm ⟨p, rE⟩
    let xH := source.chart.symm ⟨p, rH⟩
    have hxE : xE.1 ∈ (target.transport e).domain := by
      exact ComplexSurfaceChart.overlapSourceRangeProof_spec
        source (target.transport e) hpRetagged
    have hxH : xH.1 ∈ (target.transport h).domain := by
      exact ComplexSurfaceChart.overlapSourceRangeProof_spec
        source (target.transport h) hpDirect
    let xE' : {x // x ∈ (target.transport e).domain} :=
      ⟨xE.1, hxE⟩
    let xH' : {x // x ∈ (target.transport h).domain} :=
      ⟨xH.1, hxH⟩
    have hsourcePoint' : xE.1 = xH.1 := by
      exact congrArg Subtype.val hsourcePoint
    have hvalE := ComplexSurfaceChart.transport_chart_val
      (e := e) (A := target)
      (x := xE.1) (hx := hxE)
    have hvalH := ComplexSurfaceChart.transport_chart_val
      (e := h) (A := target)
      (x := xH.1) (hx := hxH)
    let yE : {y // y ∈ target.domain} :=
      ⟨e xE.1, by exact hxE⟩
    let yH : {y // y ∈ target.domain} :=
      ⟨h xH.1, by exact hxH⟩
    have hy : yE = yH := by
      apply Subtype.ext
      dsimp [yE, yH]
      rw [heq]
    have hxErepr : xE' = ⟨xE.1, hxE⟩ := by
      apply Subtype.ext
      rfl
    have hxHrepr : xH' = ⟨xH.1, hxH⟩ := by
      apply Subtype.ext
      rfl
    have hvalE' : ((target.transport e).chart xE').1 =
        (target.chart yE).1 := by
      rw [hxErepr]
      simpa [yE] using hvalE
    have hvalH' : ((target.transport h).chart xH').1 =
        (target.chart yH).1 := by
      change ((target.transport h).chart ⟨xH.1, hxH⟩).1 =
        (target.chart ⟨h xH.1, hxH⟩).1
      exact hvalH
    have htransE := ComplexSurfaceChart.transitionMap_on_overlap
      source (target.transport e) hpRetagged
    have htransH := ComplexSurfaceChart.transitionMap_on_overlap
      source (target.transport h) hpDirect
    have htransH' :
        ComplexSurfaceChart.transitionMap source (target.transport h) p =
          ((target.transport h).chart xH').1 := by
      change ComplexSurfaceChart.transitionMap source (target.transport h) p =
        ((target.transport h).chart
          ⟨(source.chart.symm ⟨p, rH⟩).1,
            ComplexSurfaceChart.overlapSourceRangeProof_spec
              source (target.transport h) hpDirect⟩).1
      exact htransH
    calc
      ComplexSurfaceChart.transitionMap source (target.transport e) p =
          ((target.transport e).chart xE').1 := by
            simpa [xE', xE] using htransE
      _ = (target.chart yE).1 := hvalE'
      _ = (target.chart yH).1 := by
            exact congrArg (fun x => (target.chart x).1) hy
      _ = ((target.transport h).chart xH').1 := by
            exact hvalH'.symm
      _ = ComplexSurfaceChart.transitionMap source (target.transport h) p := by
            exact htransH'.symm
  have hretagged :=
    descendedChart_transitionMap_eq_retagged_joint_transition
      D hquot J i j c d hp
  exact hretagged.trans (by
    change ComplexSurfaceChart.transitionMap source (target.transport e) p =
      ComplexSurfaceChart.transitionMap source (target.transport h) p
    exact htransitionEq)

/-! Successive overlap hypotheses in the descended atlas produce both the
    direct source-to-target overlap and the actual chart cocycle.  This is the
    quotient-level packaging of the local chart lemma: later analytic
    comparison theorems can use the first component to enter the target chart
    overlap and the second component to rewrite the coordinate transition. -/

theorem descendedChart_overlap_comp_on_overlap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (i j k : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    (e : (D.localFamily k).atlas.index)
    {p : ℂ × ℂ}
    (hp₁₂ : p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart ⟨i, c⟩)
      ((descendedChartFamily D hquot).chart ⟨j, d⟩))
    (hp₂₃ : ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩) p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart ⟨j, d⟩)
        ((descendedChartFamily D hquot).chart ⟨k, e⟩)) :
    p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart ⟨i, c⟩)
      ((descendedChartFamily D hquot).chart ⟨k, e⟩) ∧
      ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart ⟨i, c⟩)
          ((descendedChartFamily D hquot).chart ⟨k, e⟩) p =
        ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart ⟨j, d⟩)
          ((descendedChartFamily D hquot).chart ⟨k, e⟩)
          (ComplexSurfaceChart.transitionMap
            ((descendedChartFamily D hquot).chart ⟨i, c⟩)
            ((descendedChartFamily D hquot).chart ⟨j, d⟩) p) := by
  let sourceChart := (descendedChartFamily D hquot).chart ⟨i, c⟩
  let middleChart := (descendedChartFamily D hquot).chart ⟨j, d⟩
  let targetChart := (descendedChartFamily D hquot).chart ⟨k, e⟩
  have hp₁₃ : p ∈ ComplexSurfaceChart.overlap sourceChart targetChart :=
    ComplexSurfaceChart.overlap_mem_of_transitionMap_mem
      sourceChart middleChart targetChart hp₁₂ hp₂₃
  have hcomp := ComplexSurfaceChart.transitionMap_comp_on_overlap
    sourceChart middleChart targetChart hp₁₂ hp₂₃
  exact ⟨by simpa [sourceChart, middleChart, targetChart] using hp₁₃,
    by simpa [sourceChart, middleChart, targetChart] using hcomp⟩


theorem descendedChartFamily_overlap_comp_on_overlap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (a b c : (descendedChartFamily D hquot).index)
    {p : ℂ × ℂ}
    (hpab : p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart a)
      ((descendedChartFamily D hquot).chart b))
    (hpbc : ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart a)
        ((descendedChartFamily D hquot).chart b) p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart b)
        ((descendedChartFamily D hquot).chart c)) :
    p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart a)
      ((descendedChartFamily D hquot).chart c) ∧
      ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart a)
          ((descendedChartFamily D hquot).chart c) p =
        ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart b)
          ((descendedChartFamily D hquot).chart c)
          (ComplexSurfaceChart.transitionMap
            ((descendedChartFamily D hquot).chart a)
            ((descendedChartFamily D hquot).chart b) p) := by
  rcases a with ⟨i, c₁⟩
  rcases b with ⟨j, c₂⟩
  rcases c with ⟨k, c₃⟩
  simpa only using
    (descendedChart_overlap_comp_on_overlap D hquot i j k c₁ c₂ c₃ hpab hpbc)


/-! The analytic descent step separates cleanly into two inputs.  The first is
    the genuine joint holomorphic transition on the two overlap atlases; the
    second is only a pointwise coordinate comparison on the descended overlap.
    Keeping the comparison as an explicit structure makes the remaining
    topological retagging problem inspectable instead of hiding it in the
    final atlas witness. -/

structure DescendedTransitionCompatibility
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D) : Prop where
  transition_eq : ∀ (i j : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    {p : ℂ × ℂ},
    p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart ⟨i, c⟩)
      ((descendedChartFamily D hquot).chart ⟨j, d⟩) →
    ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩) p =
      ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i j).chart c)
        (((overlapTargetAtlas D i j).chart d).transport
          (J.toJointlyContinuousTransitionData.homeomorph i j)) p

theorem DescendedTransitionCompatibility.joint_transitionMap_comp_on_overlap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D)
    (C : DescendedTransitionCompatibility D hquot J)
    (i j k : I)
    (c : (D.localFamily i).atlas.index)
    (d : (D.localFamily j).atlas.index)
    (e : (D.localFamily k).atlas.index)
    {p : ℂ × ℂ}
    (hp₁₂ : p ∈ ComplexSurfaceChart.overlap
      ((descendedChartFamily D hquot).chart ⟨i, c⟩)
      ((descendedChartFamily D hquot).chart ⟨j, d⟩))
    (hp₂₃ : ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart ⟨i, c⟩)
        ((descendedChartFamily D hquot).chart ⟨j, d⟩) p ∈
      ComplexSurfaceChart.overlap
        ((descendedChartFamily D hquot).chart ⟨j, d⟩)
        ((descendedChartFamily D hquot).chart ⟨k, e⟩)) :
    ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i k).chart c)
        (((overlapTargetAtlas D i k).chart e).transport
          (J.toJointlyContinuousTransitionData.homeomorph i k)) p =
      ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D j k).chart d)
        (((overlapTargetAtlas D j k).chart e).transport
          (J.toJointlyContinuousTransitionData.homeomorph j k))
        (ComplexSurfaceChart.transitionMap
          ((overlapSourceAtlas D i j).chart c)
          (((overlapTargetAtlas D i j).chart d).transport
            (J.toJointlyContinuousTransitionData.homeomorph i j)) p) := by
  have hp₁₃ := descendedChart_overlap_comp_on_overlap
    D hquot i j k c d e hp₁₂ hp₂₃
  have hdesc₁₃ := C.transition_eq i k c e hp₁₃.1
  have hdesc₁₂ := C.transition_eq i j c d hp₁₂
  have hdesc₂₃ := C.transition_eq j k d e hp₂₃
  calc
    ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas D i k).chart c)
        (((overlapTargetAtlas D i k).chart e).transport
          (J.toJointlyContinuousTransitionData.homeomorph i k)) p =
        ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart ⟨i, c⟩)
          ((descendedChartFamily D hquot).chart ⟨k, e⟩) p :=
      hdesc₁₃.symm
    _ = ComplexSurfaceChart.transitionMap
          ((descendedChartFamily D hquot).chart ⟨j, d⟩)
          ((descendedChartFamily D hquot).chart ⟨k, e⟩)
          (ComplexSurfaceChart.transitionMap
            ((descendedChartFamily D hquot).chart ⟨i, c⟩)
            ((descendedChartFamily D hquot).chart ⟨j, d⟩) p) :=
      hp₁₃.2
    _ = ComplexSurfaceChart.transitionMap
          ((overlapSourceAtlas D j k).chart d)
          (((overlapTargetAtlas D j k).chart e).transport
            (J.toJointlyContinuousTransitionData.homeomorph j k))
          (ComplexSurfaceChart.transitionMap
            ((descendedChartFamily D hquot).chart ⟨i, c⟩)
            ((descendedChartFamily D hquot).chart ⟨j, d⟩) p) := by
      exact hdesc₂₃
    _ = ComplexSurfaceChart.transitionMap
          ((overlapSourceAtlas D j k).chart d)
          (((overlapTargetAtlas D j k).chart e).transport
            (J.toJointlyContinuousTransitionData.homeomorph j k))
          (ComplexSurfaceChart.transitionMap
            ((overlapSourceAtlas D i j).chart c)
            (((overlapTargetAtlas D i j).chart d).transport
              (J.toJointlyContinuousTransitionData.homeomorph i j)) p) := by
      exact congrArg
        (fun q => ComplexSurfaceChart.transitionMap
          ((overlapSourceAtlas D j k).chart d)
          (((overlapTargetAtlas D j k).chart e).transport
            (J.toJointlyContinuousTransitionData.homeomorph j k)) q)
        hdesc₁₂

noncomputable def descendedTransitionCompatibility_of_jointlyHolomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D) :
    DescendedTransitionCompatibility D hquot J where
  transition_eq := by
    intro i j c d p hp
    exact descendedChart_transitionMap_eq_joint_transition
      D hquot J i j c d hp



structure DescendedAtlasHolomorphicWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) where
  transition_differentiableOn : ∀ a b,
      DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((descendedChartFamily D hquot).chart a)
        ((descendedChartFamily D hquot).chart b))
            (ComplexSurfaceChart.overlap
              ((descendedChartFamily D hquot).chart a)
              ((descendedChartFamily D hquot).chart b))

noncomputable def descendedAtlasHolomorphicWitness_of_jointlyHolomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D)
    (C : DescendedTransitionCompatibility D hquot J) :
    DescendedAtlasHolomorphicWitness D hquot := by
  refine { transition_differentiableOn := ?_ }
  intro a b
  rcases a with ⟨i, c⟩
  rcases b with ⟨j, d⟩
  have hsubset :
      ComplexSurfaceChart.overlap
          ((descendedChartFamily D hquot).chart ⟨i, c⟩)
          ((descendedChartFamily D hquot).chart ⟨j, d⟩) ⊆
        ComplexSurfaceChart.overlap
          ((overlapSourceAtlas D i j).chart c)
          (((overlapTargetAtlas D i j).chart d).transport
            (J.toJointlyContinuousTransitionData.homeomorph i j)) := by
    intro p hp
    exact descendedChart_overlap_subset_joint_overlap
      D hquot J i j c d hp
  have hjoint := (J.forward_holomorphic i j).differentiableOn c d
  have hrestricted := hjoint.mono hsubset
  exact hrestricted.congr (fun p hp => C.transition_eq i j c d hp)

noncomputable def descendedAtlasHolomorphicWitness_of_jointlyHolomorphic_transition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (J : JointlyHolomorphicTransitionData D) :
    DescendedAtlasHolomorphicWitness D hquot :=
  descendedAtlasHolomorphicWitness_of_jointlyHolomorphic D hquot J
    (descendedTransitionCompatibility_of_jointlyHolomorphic D hquot J)

noncomputable def descendedAtlasHolomorphicWitness_of_subsingleton_index
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    [Subsingleton (DescendedChartIndex D)] :
    DescendedAtlasHolomorphicWitness D hquot := by
  letI : Subsingleton ((descendedChartFamily D hquot).index) := by
    change Subsingleton (DescendedChartIndex D)
    infer_instance
  refine { transition_differentiableOn := ?_ }
  intro a b
  have hab : a = b := Subsingleton.elim _ _
  subst b
  exact ComplexSurfaceChart.transitionMap_self_differentiableOn
    ((descendedChartFamily D hquot).chart a)

noncomputable def descendedAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData S B I}
    {hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)}
    (W : DescendedAtlasHolomorphicWitness D hquot) :
    @ComplexSurfaceAtlas (DescendedTotal D) :=
  { toComplexSurfaceChartFamily := descendedChartFamily D hquot
    transition_differentiableOn := W.transition_differentiableOn }

/-! The quotient atlas also remembers the family direction.  The local
    families may live over different subtype bases, so the only additional
    input needed here is that their parameter coordinates are restrictions of
    one common map `B → ℂ`.  The theorem below turns that compatibility into
    the actual first-coordinate identity for every descended chart. -/

noncomputable def descendedFamilyAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B)) :
    @ComplexSurfaceFamilyAtlas (DescendedTotal D) B inferInstance := by
  refine
    { toComplexSurfaceAtlas := descendedAtlas W
      projection := descendedProjection D
      parameterCoordinate := parameterCoordinate
      projection_continuous := continuous_descendedProjection D
      chart_base_coordinate := ?_ }
  intro a q hq
  rcases a with ⟨i, c⟩
  have hq_image := hq
  change q ∈ localChartImage D i c at hq_image
  rcases hq_image with ⟨z, hz, hzq⟩
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  letI : TopologicalSpace
      {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    TopologicalSpace.induced Subtype.val
      (D.localFamily i).family.totalTopology
  let zDomain : {x // x ∈ ((D.localFamily i).atlas.chart c).domain} :=
    ⟨z, hz⟩
  let hlocal := localChartHomeomorph_of_isOpenMap_quotientMk D i hquot c
  have hlocalValue : (hlocal zDomain).1 = q := by
    rw [localChartHomeomorph_apply_val]
    exact hzq
  have hlocalPoint :
      hlocal.symm ⟨q, hq⟩ = zDomain := by
    apply hlocal.injective
    apply Subtype.ext
    rw [hlocal.apply_symm_apply]
    exact hlocalValue.symm
  have hchartValue :
      (((descendedChartFamily D hquot).chart ⟨i, c⟩).chart
        ⟨q, hq⟩).1 =
      (((D.localFamily i).atlas.chart c).chart zDomain).1 := by
    change
      (retopologizeSourceHomeomorph
        ((D.localFamily i).atlas.chart c).chart _
        (hlocal.symm ⟨q, hq⟩)).1 = _
    rw [hlocalPoint]
    rw [retopologizeSourceHomeomorph_apply]
  have hlocalProjection :
      (D.localFamily i).atlas.projection z = z.1 := by
    rw [(D.localFamily i).projection_eq]
    rfl
  have hdescendedProjection :
      descendedProjection D q = (z.1 : B) := by
    rw [← hzq]
    exact localQuotient_projection D i z
  calc
    (((descendedChartFamily D hquot).chart ⟨i, c⟩).chart
        ⟨q, hq⟩).1.1 =
        (((D.localFamily i).atlas.chart c).chart zDomain).1.1 := by
          exact congrArg Prod.fst hchartValue
    _ = (D.localFamily i).atlas.parameterCoordinate
          ((D.localFamily i).atlas.projection z) := by
          simpa [zDomain] using
            (D.localFamily i).atlas.chart_base_coordinate c hz
    _ = (D.localFamily i).atlas.parameterCoordinate z.1 := by
          rw [hlocalProjection]
    _ = parameterCoordinate (z.1 : B) := hparam i z.1
    _ = parameterCoordinate (descendedProjection D q) := by
          rw [hdescendedProjection]

/-! ### From the descended atlas to an assembled marked family

The quotient construction has now supplied the descended total-space atlas and
the marking of each quotient fibre.  The remaining family-level input is
exactly the same slice-and-comparison datum used by MathlibFamily.lean.
Naming that specialization here makes the logical boundary visible at the
Čech layer: no fibrewise atlas is silently promoted to a family. -/

abbrev DescendedFiberSliceFamilyAssemblyWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B)) :=
  ComplexSurfaceFamily.MarkedFiberSliceFamilyAssemblyWitness
    (S := S)
    (A := descendedFamilyAtlas D hquot W parameterCoordinate hparam)

noncomputable def DescendedFiberSliceFamilyAssemblyWitness.toFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam) :
    ComplexSurfaceFamily.Family S B :=
  ComplexSurfaceFamily.MarkedFiberSliceFamilyAssemblyWitness.toFamily H

noncomputable def DescendedFiberSliceFamilyAssemblyWitness.toGlobal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam) :
    ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily (S := S) (B := B) :=
  ComplexSurfaceFamily.MarkedFiberSliceFamilyAssemblyWitness.toGlobalHolomorphicMarkedFamily H
    (by rfl)

/-! ### Binding the descended family to the universal-property target

The quotient construction now has a genuine global marked family, but that
construction alone does not classify arbitrary test families.  The following
structure names the exact remaining input at the Čech level: for the
descended global family, every global test family receives a global pullback
classification witness, and the classifying map is unique.  Its fields are
deliberately data-valued rather than a legacy `Prop`, so the bridge can be
consumed by the existing fine-moduli interface without asserting existence
for free.
-/

structure DescendedGlobalUniversalPropertyWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam) where
  universal : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (S := S) (B := C)),
    GlobalHolomorphicFamilyClassification
      (DescendedFiberSliceFamilyAssemblyWitness.toGlobal
        D hquot W parameterCoordinate hparam H) F
  classify_unique : ∀ {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (S := S) (B := C))
    (c₁ c₂ : GlobalHolomorphicFamilyClassification
      (DescendedFiberSliceFamilyAssemblyWitness.toGlobal
        D hquot W parameterCoordinate hparam H) F),
    c₁.map = c₂.map

namespace DescendedGlobalUniversalPropertyWitness

noncomputable def toGlobalFineHolomorphicUniversalMarkedFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam)
    (P : DescendedGlobalUniversalPropertyWitness
      D hquot W parameterCoordinate hparam H) :
    GlobalFineHolomorphicUniversalMarkedFamily
      (DescendedFiberSliceFamilyAssemblyWitness.toGlobal
        D hquot W parameterCoordinate hparam H) where
  universal := P.universal
  classify_unique := P.classify_unique

def classify
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam)
    (P : DescendedGlobalUniversalPropertyWitness
      D hquot W parameterCoordinate hparam H)
    {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (S := S) (B := C)) :
    GlobalHolomorphicFamilyClassification
      (DescendedFiberSliceFamilyAssemblyWitness.toGlobal
        D hquot W parameterCoordinate hparam H) F :=
  P.universal F

theorem classify_map_unique
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData S B I)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D))
    (W : DescendedAtlasHolomorphicWitness D hquot)
    (parameterCoordinate : B → ℂ)
    (hparam : ∀ (i : I) (b : D.cover i),
      (D.localFamily i).atlas.parameterCoordinate b =
        parameterCoordinate (b : B))
    (H : DescendedFiberSliceFamilyAssemblyWitness
      D hquot W parameterCoordinate hparam)
    (P : DescendedGlobalUniversalPropertyWitness
      D hquot W parameterCoordinate hparam H)
    {C : Type w} [TopologicalSpace C]
    (F : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (S := S) (B := C))
    (c₁ c₂ : GlobalHolomorphicFamilyClassification
      (DescendedFiberSliceFamilyAssemblyWitness.toGlobal
        D hquot W parameterCoordinate hparam H) F) :
    c₁.map = c₂.map :=
  P.classify_unique F c₁ c₂

end DescendedGlobalUniversalPropertyWitness

/-! ### Local analytic coordinates on a Čech cover

The descended object already contains local global-family data, but it does
not by itself provide a locally trivial analytic-family witness in the sense
of MathlibFiberBundle.  The following same-carrier-universe adapter records
that missing input explicitly: each patch receives a complex base chart, an
analytic family whose underlying family is identified with the given local
family, and a joint coordinate witness. -/

structure LocalJointlyHolomorphicVariationWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, u} S B I) where
  baseChart : ∀ i, ComplexSurfaceFamily.ComplexBaseChart (D.cover i)
  baseChart_covers : ∀ (i : I) (b : D.cover i),
    b ∈ (baseChart i).domain
  baseTransition : ∀ i j, ℂ → ℂ
  baseTransition_differentiable : ∀ i j,
    Differentiable ℂ (baseTransition i j)
  baseTransition_agrees : ∀ (i j : I)
      (x : CechOverlap D.cover i j),
    baseTransition i j
        (ComplexSurfaceFamily.ComplexBaseChart.coordinate
          (baseChart i)
          (CechOverlap.leftPoint D.cover i j x)
          (baseChart_covers i (CechOverlap.leftPoint D.cover i j x))) =
      ComplexSurfaceFamily.ComplexBaseChart.coordinate
        (baseChart j)
        (CechOverlap.rightPoint D.cover i j x)
        (baseChart_covers j (CechOverlap.rightPoint D.cover i j x))
  localAnalyticFamily : ∀ i, ComplexSurfaceFamily.AnalyticFamily S (D.cover i)
  localFamily_eq : ∀ i,
    (localAnalyticFamily i).family = (D.localFamily i).family
  localVariation : ∀ i,
    ComplexSurfaceFamily.LocalJointlyHolomorphicFamily S
      (localAnalyticFamily i).family (baseChart i)

noncomputable def LocalJointlyHolomorphicVariationWitness.localVariationOnCechFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : LocalJointlyHolomorphicVariationWitness D) (i : I) :
    ComplexSurfaceFamily.LocalJointlyHolomorphicFamily S
      (D.localFamily i).family (W.baseChart i) := by
  rw [← W.localFamily_eq i]
  exact W.localVariation i

theorem LocalJointlyHolomorphicVariationWitness.local_slice_differentiable
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : LocalJointlyHolomorphicVariationWitness D)
    (i : I) (b : D.cover i) (hb : b ∈ (W.baseChart i).domain) :
    Differentiable ℂ
      ((W.localVariation i).sliceCoordinate b hb) :=
  (W.localVariation i).slice_differentiable b hb

theorem LocalJointlyHolomorphicVariationWitness.local_slice_differentiableOnCechFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : LocalJointlyHolomorphicVariationWitness D)
    (i : I) (b : D.cover i) (hb : b ∈ (W.baseChart i).domain) :
    Differentiable ℂ
      ((W.localVariationOnCechFamily i).sliceCoordinate b hb) :=
  (W.localVariationOnCechFamily i).slice_differentiable b hb

/-! ### Fibre-direction compatibility on overlaps

The preceding witness gives a jointly holomorphic coordinate on each cover
piece.  To compare those coordinates, the pointwise Čech transition must be
expressed in the same fibre coordinates.  The following refinement records a
genuine extension of that coordinate transition to `ℂ × ℂ`; its
`Differentiable` field is the missing fibre-direction analytic input, while
the agreement equation ties it back to the actual transition stored in the
descent datum. -/

structure CechJointlyHolomorphicVariationWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, u} S B I)
    extends LocalJointlyHolomorphicVariationWitness D where
  transitionCoordinate : ∀ i j, ℂ × ℂ → ℂ
  transitionCoordinate_differentiable : ∀ i j,
    Differentiable ℂ (transitionCoordinate i j)
  localChart : ∀ i,
    ComplexSurfaceFamily.LocalJointlyHolomorphicChartWitness
      (LocalJointlyHolomorphicVariationWitness.localVariationOnCechFamily
        toLocalJointlyHolomorphicVariationWitness i)
  transitionCoordinate_agrees : ∀ (i j : I)
      (x : CechOverlap D.cover i j) (z : ℂ),
    letI : TopologicalSpace
        ((D.localFamily i).family.fiber
          (CechOverlap.leftPoint D.cover i j x)).carrier :=
      ((D.localFamily i).family.fiber
        (CechOverlap.leftPoint D.cover i j x)).topology
    letI : TopologicalSpace
        ((D.localFamily j).family.fiber
          (CechOverlap.rightPoint D.cover i j x)).carrier :=
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).topology
    transitionCoordinate i j
        (ComplexSurfaceFamily.ComplexBaseChart.coordinate
          (baseChart i)
          (CechOverlap.leftPoint D.cover i j x)
          (baseChart_covers i
            (CechOverlap.leftPoint D.cover i j x)), z) =
      ((LocalJointlyHolomorphicVariationWitness.localVariationOnCechFamily
          toLocalJointlyHolomorphicVariationWitness j).fiberEquiv
          (CechOverlap.rightPoint D.cover i j x)
          (baseChart_covers j
            (CechOverlap.rightPoint D.cover i j x))).symm
        (D.transition i j x
          ((LocalJointlyHolomorphicVariationWitness.localVariationOnCechFamily
              toLocalJointlyHolomorphicVariationWitness i).fiberEquiv
            (CechOverlap.leftPoint D.cover i j x)
            (baseChart_covers i
              (CechOverlap.leftPoint D.cover i j x)) z))

noncomputable def CechJointlyHolomorphicVariationWitness.localAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i : I) :
    ComplexSurfaceAtlas
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i)) :=
  (W.localChart i).toComplexSurfaceAtlas

/-! The local chart lives over the base-chart domain, whereas the Čech
overlap total space is indexed by the overlap itself.  The following maps
insert an overlap point into that local chart domain.  They are kept as
explicit maps because the proof that their images carry the expected open
subspace topology is part of the descent data, not a definitional shortcut. -/

def CechJointlyHolomorphicVariationWitness.localChartSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    CechOverlapSourceTotal D i j →
      ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i) :=
  fun z =>
    ⟨⟨CechOverlap.leftPoint D.cover i j z.1,
        W.baseChart_covers i
          (CechOverlap.leftPoint D.cover i j z.1)⟩, z.2⟩

def CechJointlyHolomorphicVariationWitness.localChartTargetMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    CechOverlapTargetTotal D i j →
      ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily j).family (W.baseChart j) :=
  fun z =>
    ⟨⟨CechOverlap.rightPoint D.cover i j z.1,
        W.baseChart_covers j
          (CechOverlap.rightPoint D.cover i j z.1)⟩, z.2⟩

theorem CechJointlyHolomorphicVariationWitness.localChartSourceMap_toTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I)
    (z : CechOverlapSourceTotal D i j) :
    ComplexSurfaceFamily.localBaseTotalMap
        (D.localFamily i).family (W.baseChart i)
        (W.localChartSourceMap i j z) =
      overlapSourceFibreMap D i j z := by
  rfl

theorem CechJointlyHolomorphicVariationWitness.localChartTargetMap_toTotal
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I)
    (z : CechOverlapTargetTotal D i j) :
    ComplexSurfaceFamily.localBaseTotalMap
        (D.localFamily j).family (W.baseChart j)
        (W.localChartTargetMap i j z) =
      overlapTargetFibreMap D i j z := by
  rfl

theorem CechJointlyHolomorphicVariationWitness.injective_localBaseTotalMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i : I) :
    Function.Injective
      (ComplexSurfaceFamily.localBaseTotalMap
        (D.localFamily i).family (W.baseChart i)) := by
  intro x y hxy
  rcases x with ⟨x, xval⟩
  rcases y with ⟨y, yval⟩
  have hbase : x = y := by
    apply Subtype.ext
    exact congrArg Sigma.fst hxy
  subst y
  change (⟨x.1, xval⟩ : Sigma fun b =>
      ((D.localFamily i).family.fiber b).carrier) =
    ⟨x.1, yval⟩ at hxy
  exact Sigma.ext rfl
    (heq_of_eq (eq_of_heq (Sigma.ext_iff.mp hxy).2))

theorem CechJointlyHolomorphicVariationWitness.localChartSourceMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    Set.range (W.localChartSourceMap i j) =
      (ComplexSurfaceFamily.localBaseTotalMap
        (D.localFamily i).family (W.baseChart i)) ⁻¹'
        Set.range (overlapSourceFibreMap D i j) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (W.localChartSourceMap_toTotal i j z).symm⟩
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply W.injective_localBaseTotalMap i
    exact Eq.trans (W.localChartSourceMap_toTotal i j z) hz

theorem CechJointlyHolomorphicVariationWitness.localChartTargetMap_range
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    Set.range (W.localChartTargetMap i j) =
      (ComplexSurfaceFamily.localBaseTotalMap
        (D.localFamily j).family (W.baseChart j)) ⁻¹'
        Set.range (overlapTargetFibreMap D i j) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (W.localChartTargetMap_toTotal i j z).symm⟩
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply W.injective_localBaseTotalMap j
    exact Eq.trans (W.localChartTargetMap_toTotal i j z) hz

theorem CechJointlyHolomorphicVariationWitness.localChartSourceMap_topology_eq_induced
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    cechOverlapSourceTopology D i j =
      @TopologicalSpace.induced
        (CechOverlapSourceTotal D i j)
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i))
        (W.localChartSourceMap i j)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i)) := by
  let F := (D.localFamily i).family
  let C := W.baseChart i
  rw [cechOverlapSourceTopology_eq_induced_fibre_total D i j]
  have hcomp : overlapSourceFibreMap D i j =
      ComplexSurfaceFamily.localBaseTotalMap F C ∘
        W.localChartSourceMap i j := by
    funext z
    rfl
  rw [hcomp]
  rw [ComplexSurfaceFamily.localBaseTotalTopology]
  rw [induced_compose]
  rfl

theorem CechJointlyHolomorphicVariationWitness.localChartTargetMap_topology_eq_induced
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    cechOverlapTargetTopology D i j =
      @TopologicalSpace.induced
        (CechOverlapTargetTotal D i j)
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j))
        (W.localChartTargetMap i j)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j)) := by
  let F := (D.localFamily j).family
  let C := W.baseChart j
  rw [cechOverlapTargetTopology_eq_induced_fibre_total D i j]
  have hcomp : overlapTargetFibreMap D i j =
      ComplexSurfaceFamily.localBaseTotalMap F C ∘
        W.localChartTargetMap i j := by
    funext z
    rfl
  rw [hcomp]
  rw [ComplexSurfaceFamily.localBaseTotalTopology]
  rw [induced_compose]
  rfl

theorem CechJointlyHolomorphicVariationWitness.isOpenEmbedding_localChartSourceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapSourceTotal D i j)
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i))
      (cechOverlapSourceTopology D i j)
      (ComplexSurfaceFamily.localBaseTotalTopology
        (D.localFamily i).family (W.baseChart i))
      (W.localChartSourceMap i j) := by
  let F := (D.localFamily i).family
  let C := W.baseChart i
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (ComplexSurfaceFamily.LocalBaseTotal F C) :=
    ComplexSurfaceFamily.localBaseTotalTopology F C
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · rw [W.localChartSourceMap_topology_eq_induced i j]
    apply continuous_induced_rng.mpr
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i))
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))
        (D.localFamily i).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily i).family (W.baseChart i)) :=
      continuous_induced_dom
    letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
      TopologicalSpace.induced (W.localChartSourceMap i j)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))
    have hsource : @Continuous
        (CechOverlapSourceTotal D i j)
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i))
        (TopologicalSpace.induced (W.localChartSourceMap i j)
          (ComplexSurfaceFamily.localBaseTotalTopology
            (D.localFamily i).family (W.baseChart i)))
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))
        (W.localChartSourceMap i j) :=
      continuous_induced_dom
    convert hlocal.comp hsource using 1
  · intro x y hxy
    apply injective_overlapSourceFibreMap D i j
    rw [← W.localChartSourceMap_toTotal i j x,
      ← W.localChartSourceMap_toTotal i j y]
    exact congrArg
      (ComplexSurfaceFamily.localBaseTotalMap F C) hxy
  · rw [W.localChartSourceMap_topology_eq_induced i j]
    apply isOpenMap_induced_of_isOpen_range
    rw [W.localChartSourceMap_range i j]
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
      (D.localFamily i).family.totalTopology
    have hopen : @IsOpen
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (D.localFamily i).family.totalTopology
        (Set.range (overlapSourceFibreMap D i j)) := by
      rw [← (D.localFamily i).topology_eq]
      letI : TopologicalSpace
          (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
        (D.localFamily i).atlas.toComplexSurfaceAtlas.topology
      exact isOpen_overlapSourceFibreMap_range_atlas D i j
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i))
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))
        (D.localFamily i).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily i).family (W.baseChart i)) :=
      continuous_induced_dom
    exact hopen.preimage hlocal

theorem CechJointlyHolomorphicVariationWitness.isOpenEmbedding_localChartTargetMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    @Topology.IsOpenEmbedding
      (CechOverlapTargetTotal D i j)
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily j).family (W.baseChart j))
      (cechOverlapTargetTopology D i j)
      (ComplexSurfaceFamily.localBaseTotalTopology
        (D.localFamily j).family (W.baseChart j))
      (W.localChartTargetMap i j) := by
  let F := (D.localFamily j).family
  let C := W.baseChart j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace (ComplexSurfaceFamily.LocalBaseTotal F C) :=
    ComplexSurfaceFamily.localBaseTotalTopology F C
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · rw [W.localChartTargetMap_topology_eq_induced i j]
    apply continuous_induced_rng.mpr
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j))
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))
        (D.localFamily j).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily j).family (W.baseChart j)) :=
      continuous_induced_dom
    letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
      TopologicalSpace.induced (W.localChartTargetMap i j)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))
    have hsource : @Continuous
        (CechOverlapTargetTotal D i j)
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j))
        (TopologicalSpace.induced (W.localChartTargetMap i j)
          (ComplexSurfaceFamily.localBaseTotalTopology
            (D.localFamily j).family (W.baseChart j)))
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))
        (W.localChartTargetMap i j) :=
      continuous_induced_dom
    convert hlocal.comp hsource using 1
  · intro x y hxy
    apply injective_overlapTargetFibreMap D i j
    rw [← W.localChartTargetMap_toTotal i j x,
      ← W.localChartTargetMap_toTotal i j y]
    exact congrArg
      (ComplexSurfaceFamily.localBaseTotalMap F C) hxy
  · rw [W.localChartTargetMap_topology_eq_induced i j]
    apply isOpenMap_induced_of_isOpen_range
    rw [W.localChartTargetMap_range i j]
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
      (D.localFamily j).family.totalTopology
    have hopen : @IsOpen
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (D.localFamily j).family.totalTopology
        (Set.range (overlapTargetFibreMap D i j)) := by
      rw [← (D.localFamily j).topology_eq]
      letI : TopologicalSpace
          (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
        (D.localFamily j).atlas.toComplexSurfaceAtlas.topology
      exact isOpen_overlapTargetFibreMap_range_atlas D i j
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j))
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))
        (D.localFamily j).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily j).family (W.baseChart j)) :=
      continuous_induced_dom
    exact hopen.preimage hlocal

noncomputable def CechJointlyHolomorphicVariationWitness.localChartSourceRangeHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    @Homeomorph
      (CechOverlapSourceTotal D i j)
      {x : ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i) //
        x ∈ Set.range (W.localChartSourceMap i j)}
      (cechOverlapSourceTopology D i j)
      (TopologicalSpace.induced Subtype.val
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i)) :=
    ComplexSurfaceFamily.localBaseTotalTopology
      (D.localFamily i).family (W.baseChart i)
  exact (W.isOpenEmbedding_localChartSourceMap i j).isEmbedding.toHomeomorph

noncomputable def CechJointlyHolomorphicVariationWitness.localChartTargetRangeHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    @Homeomorph
      (CechOverlapTargetTotal D i j)
      {x : ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j) //
        x ∈ Set.range (W.localChartTargetMap i j)}
      (cechOverlapTargetTopology D i j)
      (TopologicalSpace.induced Subtype.val
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))) := by
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily j).family (W.baseChart j)) :=
    ComplexSurfaceFamily.localBaseTotalTopology
      (D.localFamily j).family (W.baseChart j)
  exact (W.isOpenEmbedding_localChartTargetMap i j).isEmbedding.toHomeomorph

noncomputable def CechJointlyHolomorphicVariationWitness.localChartSourceAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    ComplexSurfaceAtlas (CechOverlapSourceTotal D i j) := by
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i)) :=
    ComplexSurfaceFamily.localBaseTotalTopology
      (D.localFamily i).family (W.baseChart i)
  have hU : @IsOpen
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily i).family (W.baseChart i))
      (ComplexSurfaceFamily.localBaseTotalTopology
        (D.localFamily i).family (W.baseChart i))
      (Set.range (W.localChartSourceMap i j)) := by
    rw [W.localChartSourceMap_range i j]
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
      (D.localFamily i).family.totalTopology
    have hopen : @IsOpen
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (D.localFamily i).family.totalTopology
        (Set.range (overlapSourceFibreMap D i j)) := by
      rw [← (D.localFamily i).topology_eq]
      letI : TopologicalSpace
          (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
        (D.localFamily i).atlas.toComplexSurfaceAtlas.topology
      exact isOpen_overlapSourceFibreMap_range_atlas D i j
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily i).family (W.baseChart i))
        (ComplexSurfaceFamily.Total (D.localFamily i).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily i).family (W.baseChart i))
        (D.localFamily i).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily i).family (W.baseChart i)) :=
      continuous_induced_dom
    exact hopen.preimage hlocal
  exact ComplexSurfaceAtlas.transport
    ((W.localAtlas i).restrictOpenSubspace
      (Set.range (W.localChartSourceMap i j)) hU)
    (W.localChartSourceRangeHomeomorph i j)

noncomputable def CechJointlyHolomorphicVariationWitness.localChartTargetAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    ComplexSurfaceAtlas (CechOverlapTargetTotal D i j) := by
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  letI : TopologicalSpace
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily j).family (W.baseChart j)) :=
    ComplexSurfaceFamily.localBaseTotalTopology
      (D.localFamily j).family (W.baseChart j)
  have hU : @IsOpen
      (ComplexSurfaceFamily.LocalBaseTotal
        (D.localFamily j).family (W.baseChart j))
      (ComplexSurfaceFamily.localBaseTotalTopology
        (D.localFamily j).family (W.baseChart j))
      (Set.range (W.localChartTargetMap i j)) := by
    rw [W.localChartTargetMap_range i j]
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
      (D.localFamily j).family.totalTopology
    have hopen : @IsOpen
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (D.localFamily j).family.totalTopology
        (Set.range (overlapTargetFibreMap D i j)) := by
      rw [← (D.localFamily j).topology_eq]
      letI : TopologicalSpace
          (ComplexSurfaceFamily.Total (D.localFamily j).family) :=
        (D.localFamily j).atlas.toComplexSurfaceAtlas.topology
      exact isOpen_overlapTargetFibreMap_range_atlas D i j
    have hlocal : @Continuous
        (ComplexSurfaceFamily.LocalBaseTotal
          (D.localFamily j).family (W.baseChart j))
        (ComplexSurfaceFamily.Total (D.localFamily j).family)
        (ComplexSurfaceFamily.localBaseTotalTopology
          (D.localFamily j).family (W.baseChart j))
        (D.localFamily j).family.totalTopology
        (ComplexSurfaceFamily.localBaseTotalMap
          (D.localFamily j).family (W.baseChart j)) :=
      continuous_induced_dom
    exact hopen.preimage hlocal
  exact ComplexSurfaceAtlas.transport
    ((W.localAtlas j).restrictOpenSubspace
      (Set.range (W.localChartTargetMap i j)) hU)
    (W.localChartTargetRangeHomeomorph i j)

/-! The two atlases on an overlap now have the same carrier and the same
topology, but their chart functions need not be definitionally equal: one is
the selected joint chart, the other is the atlas inherited from the local
family.  The next witness records exactly the missing chartwise comparison.
Its identity homeomorphism is intentional; the content is the
`HolomorphicEquiv` proof for every source/target chart pair. -/

structure CechLocalChartComparisonWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) where
  sourceHolomorphic : ∀ i j,
    ComplexSurfaceAtlas.HolomorphicEquiv
      (W.localChartSourceAtlas i j)
      (overlapSourceAtlas D i j)
      (@Homeomorph.refl (CechOverlapSourceTotal D i j)
        (cechOverlapSourceTopology D i j))
  targetHolomorphic : ∀ i j,
    ComplexSurfaceAtlas.HolomorphicEquiv
      (W.localChartTargetAtlas i j)
      (overlapTargetAtlas D i j)
      (@Homeomorph.refl (CechOverlapTargetTotal D i j)
        (cechOverlapTargetTopology D i j))

noncomputable def CechLocalChartComparisonWitness.ofAtlasEquality
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D)
    (source_atlas_eq : ∀ i j,
      W.localChartSourceAtlas i j = overlapSourceAtlas D i j)
    (target_atlas_eq : ∀ i j,
      W.localChartTargetAtlas i j = overlapTargetAtlas D i j) :
    CechLocalChartComparisonWitness W := by
  refine
    { sourceHolomorphic := ?_
      targetHolomorphic := ?_ }
  · intro i j
    have H := ComplexSurfaceAtlas.HolomorphicEquiv.refl
      (W.localChartSourceAtlas i j)
    exact ComplexSurfaceAtlas.HolomorphicEquiv.castAtlases
      rfl (source_atlas_eq i j)
      (ComplexSurfaceAtlas.Homeomorph.refl_heq_of_atlas_eq
        (source_atlas_eq i j)) H
  · intro i j
    have H := ComplexSurfaceAtlas.HolomorphicEquiv.refl
      (W.localChartTargetAtlas i j)
    exact ComplexSurfaceAtlas.HolomorphicEquiv.castAtlases
      rfl (target_atlas_eq i j)
      (ComplexSurfaceAtlas.Homeomorph.refl_heq_of_atlas_eq
        (target_atlas_eq i j)) H

/-! The comparison witness above is the local-chart normalization layer.  The
next layer also records the actual holomorphic overlap transition in those
local charts, together with the identifications needed to cast it onto the
inherited Čech atlases.  We first expose a coordinate-level version of this
input: a globally differentiable coordinate model for each chart pair, plus
its equality with the genuine transition on the overlap. -/

structure CechLocalCoordinateTransitionWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) where
  continuous : JointlyContinuousTransitionData D
  forwardCoordinate : ∀ i j,
    (W.localChartSourceAtlas i j).index →
      (W.localChartTargetAtlas i j).index →
      ℂ × ℂ → ℂ × ℂ
  forward_differentiable : ∀ i j c d,
    Differentiable ℂ (forwardCoordinate i j c d)
  forward_transition_eq : ∀ i j c d (p : ℂ × ℂ),
    p ∈ ComplexSurfaceChart.overlap
      ((W.localChartSourceAtlas i j).chart c)
      (((W.localChartTargetAtlas i j).chart d).transport
        (continuous.homeomorph i j)) →
    ComplexSurfaceChart.transitionMap
      ((W.localChartSourceAtlas i j).chart c)
      (((W.localChartTargetAtlas i j).chart d).transport
        (continuous.homeomorph i j)) p =
      forwardCoordinate i j c d p
  inverseCoordinate : ∀ i j,
    (W.localChartTargetAtlas i j).index →
      (W.localChartSourceAtlas i j).index →
      ℂ × ℂ → ℂ × ℂ
  inverse_differentiable : ∀ i j d c,
    Differentiable ℂ (inverseCoordinate i j d c)
  inverse_transition_eq : ∀ i j d c (p : ℂ × ℂ),
    p ∈ ComplexSurfaceChart.overlap
      ((W.localChartTargetAtlas i j).chart d)
      (((W.localChartSourceAtlas i j).chart c).transport
        (@Homeomorph.symm
          (CechOverlapSourceTotal D i j)
          (CechOverlapTargetTotal D i j)
          (cechOverlapSourceTopology D i j)
          (cechOverlapTargetTopology D i j)
          (continuous.homeomorph i j))) →
    ComplexSurfaceChart.transitionMap
      ((W.localChartTargetAtlas i j).chart d)
      (((W.localChartSourceAtlas i j).chart c).transport
        (@Homeomorph.symm
          (CechOverlapSourceTotal D i j)
          (CechOverlapTargetTotal D i j)
          (cechOverlapSourceTopology D i j)
          (cechOverlapTargetTopology D i j)
          (continuous.homeomorph i j))) p =
      inverseCoordinate i j d c p
  source_atlas_eq : ∀ i j,
    W.localChartSourceAtlas i j = overlapSourceAtlas D i j
  target_atlas_eq : ∀ i j,
    W.localChartTargetAtlas i j = overlapTargetAtlas D i j

/-! The coordinate witness above is the analytic input in an explicit form.
The assembly structure below remains useful as a lower-level interface for
proofs that already construct the bundled `HolomorphicEquiv` directly. -/

structure CechLocalTransitionAssemblyWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) where
  continuous : JointlyContinuousTransitionData D
  localHolomorphic : ∀ i j,
    ComplexSurfaceAtlas.HolomorphicEquiv
      (W.localChartSourceAtlas i j)
      (W.localChartTargetAtlas i j)
      (continuous.homeomorph i j)
  source_atlas_eq : ∀ i j,
    W.localChartSourceAtlas i j = overlapSourceAtlas D i j
  target_atlas_eq : ∀ i j,
    W.localChartTargetAtlas i j = overlapTargetAtlas D i j

def CechLocalTransitionAssemblyWitness.ofJointlyHolomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    {W : CechJointlyHolomorphicVariationWitness D}
    (J : JointlyHolomorphicTransitionData D)
    (source_atlas_eq : ∀ i j,
      W.localChartSourceAtlas i j = overlapSourceAtlas D i j)
    (target_atlas_eq : ∀ i j,
      W.localChartTargetAtlas i j = overlapTargetAtlas D i j) :
    CechLocalTransitionAssemblyWitness W := by
  refine
    { continuous := J.toContinuous
      localHolomorphic := ?_
      source_atlas_eq := source_atlas_eq
      target_atlas_eq := target_atlas_eq }
  intro i j
  exact ComplexSurfaceAtlas.HolomorphicEquiv.castAtlases
    (source_atlas_eq i j).symm
    (target_atlas_eq i j).symm
    (ComplexSurfaceAtlas.Homeomorph.self_heq_of_atlas_eq
      (J.toContinuous.homeomorph i j)
      (source_atlas_eq i j).symm
      (target_atlas_eq i j).symm)
    { forward := J.forward_holomorphic i j
      inverse := J.inverse_holomorphic i j }

def CechLocalCoordinateTransitionWitness.toAssembly
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    {W : CechJointlyHolomorphicVariationWitness D}
    (Q : CechLocalCoordinateTransitionWitness W) :
    CechLocalTransitionAssemblyWitness W := by
  refine
    { continuous := Q.continuous
      localHolomorphic := ?_
      source_atlas_eq := Q.source_atlas_eq
      target_atlas_eq := Q.target_atlas_eq }
  intro i j
  refine { forward := ?_, inverse := ?_ }
  · apply ComplexSurfaceAtlas.HolomorphicMapCoordinateWitness.toHolomorphicMap
    exact
      { coordinate := Q.forwardCoordinate i j
        coordinate_differentiable := Q.forward_differentiable i j
        transition_eq := Q.forward_transition_eq i j }
  · apply ComplexSurfaceAtlas.HolomorphicMapCoordinateWitness.toHolomorphicMap
    exact
      { coordinate := Q.inverseCoordinate i j
        coordinate_differentiable := Q.inverse_differentiable i j
        transition_eq := Q.inverse_transition_eq i j }

def CechLocalTransitionAssemblyWitness.toJointlyHolomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    {W : CechJointlyHolomorphicVariationWitness D}
    (A : CechLocalTransitionAssemblyWitness W) :
    JointlyHolomorphicTransitionData D := by
  apply JointlyHolomorphicTransitionData.ofHolomorphicEquiv A.continuous
  intro i j
  exact ComplexSurfaceAtlas.HolomorphicEquiv.castAtlases
    (A.source_atlas_eq i j)
    (A.target_atlas_eq i j)
    (ComplexSurfaceAtlas.Homeomorph.self_heq_of_atlas_eq
      (A.continuous.homeomorph i j)
      (A.source_atlas_eq i j)
      (A.target_atlas_eq i j))
    (A.localHolomorphic i j)

theorem CechLocalChartComparisonWitness.source_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    {W : CechJointlyHolomorphicVariationWitness D}
    (C : CechLocalChartComparisonWitness W) (i j : I)
    (c : (W.localChartSourceAtlas i j).index)
    (d : (overlapSourceAtlas D i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((W.localChartSourceAtlas i j).chart c)
        (((overlapSourceAtlas D i j).chart d).transport
          (@Homeomorph.refl (CechOverlapSourceTotal D i j)
            (cechOverlapSourceTopology D i j))))
      (ComplexSurfaceChart.overlap
        ((W.localChartSourceAtlas i j).chart c)
        (((overlapSourceAtlas D i j).chart d).transport
          (@Homeomorph.refl (CechOverlapSourceTotal D i j)
            (cechOverlapSourceTopology D i j)))) :=
  (C.sourceHolomorphic i j).forward.differentiableOn c d

theorem CechLocalChartComparisonWitness.target_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    {W : CechJointlyHolomorphicVariationWitness D}
    (C : CechLocalChartComparisonWitness W) (i j : I)
    (c : (W.localChartTargetAtlas i j).index)
    (d : (overlapTargetAtlas D i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((W.localChartTargetAtlas i j).chart c)
        (((overlapTargetAtlas D i j).chart d).transport
          (@Homeomorph.refl (CechOverlapTargetTotal D i j)
            (cechOverlapTargetTopology D i j))))
      (ComplexSurfaceChart.overlap
        ((W.localChartTargetAtlas i j).chart c)
        (((overlapTargetAtlas D i j).chart d).transport
          (@Homeomorph.refl (CechOverlapTargetTotal D i j)
            (cechOverlapTargetTopology D i j)))) :=
  (C.targetHolomorphic i j).forward.differentiableOn c d

theorem CechJointlyHolomorphicVariationWitness.transition_differentiable
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    Differentiable ℂ (W.transitionCoordinate i j) :=
  W.transitionCoordinate_differentiable i j

/-! The base coordinate and the fibre coordinate now assemble into the
    genuine two-complex-dimensional coordinate expression of the overlap
    transition.  This is a small but important distinction: a separately
    holomorphic fibre coordinate is not yet a holomorphic map of total spaces,
    while the product map below is. -/

noncomputable def CechJointlyHolomorphicVariationWitness.jointTransitionCoordinate
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    ℂ × ℂ → ℂ × ℂ :=
  fun p => (W.baseTransition i j p.1, W.transitionCoordinate i j p)

theorem CechJointlyHolomorphicVariationWitness.jointTransitionCoordinate_differentiable
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D) (i j : I) :
    Differentiable ℂ (W.jointTransitionCoordinate i j) := by
  have hbase : Differentiable ℂ
      (fun p : ℂ × ℂ => W.baseTransition i j p.1) := by
    exact (W.baseTransition_differentiable i j).comp differentiable_fst
  exact hbase.prodMk (W.transitionCoordinate_differentiable i j)

theorem CechJointlyHolomorphicVariationWitness.transitionCoordinate_eq_target_chart
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D)
    (i j : I) (x : CechOverlap D.cover i j) (z : ℂ) :
    letI : TopologicalSpace
        ((D.localFamily j).family.fiber
          (CechOverlap.rightPoint D.cover i j x)).carrier :=
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).topology
    (W.localVariationOnCechFamily j).jointCoordinate
        (ComplexSurfaceFamily.ComplexBaseChart.coordinate
          (W.baseChart j)
          (CechOverlap.rightPoint D.cover i j x)
          (W.baseChart_covers j
            (CechOverlap.rightPoint D.cover i j x)),
          W.transitionCoordinate i j
            (ComplexSurfaceFamily.ComplexBaseChart.coordinate
              (W.baseChart i)
              (CechOverlap.leftPoint D.cover i j x)
              (W.baseChart_covers i
                (CechOverlap.leftPoint D.cover i j x)), z)) =
      (((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).surface.atlas.chart
          ((W.localVariationOnCechFamily j).chartIndex
            (CechOverlap.rightPoint D.cover i j x)
            (W.baseChart_covers j
              (CechOverlap.rightPoint D.cover i j x)))).toComplex
        (D.transition i j x
          ((W.localVariationOnCechFamily i).fiberEquiv
            (CechOverlap.leftPoint D.cover i j x)
            (W.baseChart_covers i
              (CechOverlap.leftPoint D.cover i j x)) z)) := by
  letI : TopologicalSpace
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).carrier :=
    ((D.localFamily j).family.fiber
      (CechOverlap.rightPoint D.cover i j x)).topology
  rw [W.transitionCoordinate_agrees]
  let J := W.localVariationOnCechFamily j
  let b := CechOverlap.rightPoint D.cover i j x
  let hb := W.baseChart_covers j b
  let y := (J.fiberEquiv b hb).symm
    (D.transition i j x
      ((W.localVariationOnCechFamily i).fiberEquiv
        (CechOverlap.leftPoint D.cover i j x)
        (W.baseChart_covers i
          (CechOverlap.leftPoint D.cover i j x)) z))
  have hchart := J.jointCoordinate_eq_chart b hb y
  change J.jointCoordinate
      (ComplexSurfaceFamily.ComplexBaseChart.coordinate
        (W.baseChart j) b hb, y) = _
  rw [hchart]
  exact congrArg
    (fun q =>
      (((D.localFamily j).family.fiber b).surface.atlas.chart
        (J.chartIndex b hb)).toComplex q)
    ((J.fiberEquiv b hb).apply_symm_apply
      (D.transition i j x
        ((W.localVariationOnCechFamily i).fiberEquiv
          (CechOverlap.leftPoint D.cover i j x)
          (W.baseChart_covers i
            (CechOverlap.leftPoint D.cover i j x)) z)))

theorem CechJointlyHolomorphicVariationWitness.jointTransitionCoordinate_eq_target_coordinate
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    {D : HolomorphicCechDescentData.{u, w, v, u} S B I}
    (W : CechJointlyHolomorphicVariationWitness D)
    (i j : I) (x : CechOverlap D.cover i j) (z : ℂ) :
    letI : TopologicalSpace
        ((D.localFamily j).family.fiber
          (CechOverlap.rightPoint D.cover i j x)).carrier :=
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).topology
    W.jointTransitionCoordinate i j
        (ComplexSurfaceFamily.ComplexBaseChart.coordinate
          (W.baseChart i)
          (CechOverlap.leftPoint D.cover i j x)
          (W.baseChart_covers i
            (CechOverlap.leftPoint D.cover i j x)), z) =
      (ComplexSurfaceFamily.ComplexBaseChart.coordinate
          (W.baseChart j)
          (CechOverlap.rightPoint D.cover i j x)
          (W.baseChart_covers j
            (CechOverlap.rightPoint D.cover i j x)),
        W.transitionCoordinate i j
          (ComplexSurfaceFamily.ComplexBaseChart.coordinate
            (W.baseChart i)
            (CechOverlap.leftPoint D.cover i j x)
            (W.baseChart_covers i
              (CechOverlap.leftPoint D.cover i j x)), z)) := by
  letI : TopologicalSpace
      ((D.localFamily j).family.fiber
        (CechOverlap.rightPoint D.cover i j x)).carrier :=
    ((D.localFamily j).family.fiber
      (CechOverlap.rightPoint D.cover i j x)).topology
  apply Prod.ext
  · change W.baseTransition i j
      (ComplexSurfaceFamily.ComplexBaseChart.coordinate
        (W.baseChart i)
        (CechOverlap.leftPoint D.cover i j x)
        (W.baseChart_covers i
          (CechOverlap.leftPoint D.cover i j x))) = _
    exact W.baseTransition_agrees i j x
  · change W.transitionCoordinate i j
      (ComplexSurfaceFamily.ComplexBaseChart.coordinate
        (W.baseChart i)
        (CechOverlap.leftPoint D.cover i j x)
        (W.baseChart_covers i
          (CechOverlap.leftPoint D.cover i j x)), z) = _
    rfl

end HolomorphicCechDescentData

end MathlibFormal
end Teichmuller
