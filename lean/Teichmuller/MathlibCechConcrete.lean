import Teichmuller.MathlibCechDescent

namespace Teichmuller
namespace MathlibFormal

open HolomorphicCechDescentData

universe u w

/-! Concrete Čech input coming from one already constructed global family.

The one-patch cover is intentionally small: it tests that the new joint
transition interface can be populated from an actual `GlobalHolomorphicMarkedFamily`
without adding a global openness axiom.  The nontrivial multi-patch case will
reuse the same identity-on-overlap mechanism after the restriction comparison
homeomorphisms are made explicit.
-/

noncomputable def markedSurfaceIdentityHomeomorph
    {S : Type u} [TopologicalSpace S]
    (A B : MarkedComplexRiemannSurface S) (h : A = B) :
    @Homeomorph A.carrier B.carrier A.topology B.topology := by
  letI : TopologicalSpace A.carrier := A.topology
  letI : TopologicalSpace B.carrier := B.topology
  cases h
  exact @Homeomorph.refl A.carrier A.topology

noncomputable def singlePatchCechDescentData
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B)) :
    HolomorphicCechDescentData S B PUnit := by
  let H := G.restrictBaseOpen Set.univ isOpen_univ
  let cover : PUnit → Set B := fun _ => Set.univ
  let leftRightEq : ∀ (x : CechOverlap cover PUnit.unit PUnit.unit),
      CechOverlap.leftPoint cover PUnit.unit PUnit.unit x =
        CechOverlap.rightPoint cover PUnit.unit PUnit.unit x := by
    intro x
    apply Subtype.ext
    rfl
  refine
    { cover := cover
      cover_open := by
        intro i
        cases i
        exact isOpen_univ
      cover_univ := by
        ext b
        constructor
        · intro _
          trivial
        · intro _
          exact Set.mem_iUnion.2 ⟨PUnit.unit, Set.mem_univ b⟩
      localFamily := fun _ => H
      transition := by
        intro i j x
        cases i
        cases j
        exact markedSurfaceIdentityHomeomorph
          (H.family.fiber (CechOverlap.leftPoint cover PUnit.unit PUnit.unit x))
          (H.family.fiber (CechOverlap.rightPoint cover PUnit.unit PUnit.unit x))
          (congrArg H.family.fiber (leftRightEq x))
      transition_holomorphic := by
        intro i j x
        cases i
        cases j
        have hbase := leftRightEq x
        cases hbase
        let F := H.family.fiber
          (CechOverlap.leftPoint cover PUnit.unit PUnit.unit x)
        letI : TopologicalSpace F.carrier := F.topology
        exact AtlasHolomorphicEquiv.refl F.surface.atlas
      transition_marking_commutes := by
        intro i j x s
        cases i
        cases j
        have hbase := leftRightEq x
        cases hbase
        rfl
      transition_self := by
        intro i x
        cases i
        have hbase := leftRightEq x
        cases hbase
        rfl
      transition_comp := by
        intro i j k x
        cases i
        cases j
        cases k
        have h₁ := leftRightEq (CechTripleOverlap.toIJ cover PUnit.unit PUnit.unit PUnit.unit x)
        have h₂ := leftRightEq (CechTripleOverlap.toJK cover PUnit.unit PUnit.unit PUnit.unit x)
        have h₃ := leftRightEq (CechTripleOverlap.toIK cover PUnit.unit PUnit.unit PUnit.unit x)
        cases h₁
        cases h₂
        cases h₃
        rfl }

noncomputable def singlePatchJointlyContinuousTransition
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B)) :
    JointlyContinuousTransitionData (singlePatchCechDescentData G) :=
  jointlyContinuousTransition_of_subsingleton
    (singlePatchCechDescentData G)

noncomputable def singlePatchOpenGluingWitness
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B)) :
    OpenGluingWitness (singlePatchCechDescentData G) :=
  openGluingWitness_of_jointlyContinuous
    (singlePatchCechDescentData G)
    (singlePatchJointlyContinuousTransition G)

noncomputable def singlePatchDescendedAtlasHolomorphicWitness
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    [Subsingleton
      ((singlePatchCechDescentData G).localFamily PUnit.unit).atlas.index] :
    DescendedAtlasHolomorphicWitness
      (singlePatchCechDescentData G)
      (isOpenMap_quotientMk_of_openGluing
        (singlePatchCechDescentData G)
        (singlePatchOpenGluingWitness G)) := by
  let D := singlePatchCechDescentData G
  letI : Subsingleton (D.localFamily PUnit.unit).atlas.index := by
    infer_instance
  letI : Subsingleton (DescendedChartIndex D) := by
    constructor
    rintro ⟨i, c⟩ ⟨j, d⟩
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hcd : c = d := Subsingleton.elim _ _
    subst d
    rfl
  exact descendedAtlasHolomorphicWitness_of_subsingleton_index
    D (isOpenMap_quotientMk_of_openGluing D (singlePatchOpenGluingWitness G))

/-! The one-patch case also provides a small regression target for the
    common-mother-atlas interface.  The source overlap atlas is chosen as the
    mother; the only remaining comparison is the self-transition and its
    inverse. -/

noncomputable def singlePatchCommonMotherAtlasWitness
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B)) :
    CommonMotherAtlasTransitionWitness
      (singlePatchCechDescentData G) := by
  refine
    { toJointlyContinuousTransitionData :=
        singlePatchJointlyContinuousTransition G
      motherCarrier := fun _ _ =>
        CechOverlapSourceTotal
          (singlePatchCechDescentData G) PUnit.unit PUnit.unit
      motherAtlas := fun _ _ =>
        overlapSourceAtlas
          (singlePatchCechDescentData G) PUnit.unit PUnit.unit
      sourceHomeomorph := fun _ _ => by
        exact @Homeomorph.refl
          (CechOverlapSourceTotal
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit)
          (cechOverlapSourceTopology
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit)
      targetHomeomorph := fun i j => by
        cases i
        cases j
        letI : TopologicalSpace
            (CechOverlapSourceTotal
              (singlePatchCechDescentData G) PUnit.unit PUnit.unit) :=
          cechOverlapSourceTopology
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit
        letI : TopologicalSpace
            (CechOverlapTargetTotal
              (singlePatchCechDescentData G) PUnit.unit PUnit.unit) :=
          cechOverlapTargetTopology
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit
        exact ((singlePatchJointlyContinuousTransition G).homeomorph
          PUnit.unit PUnit.unit).symm
      source_atlas_eq := by
        intro i j
        cases i
        cases j
        exact (ComplexSurfaceAtlas.transport_refl
          (overlapSourceAtlas
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit)).symm
      target_atlas_eq := by
        intro i j
        cases i
        cases j
        rfl
      comparison_comp := by
        intro i j
        cases i
        cases j
        letI : TopologicalSpace
            (CechOverlapSourceTotal
              (singlePatchCechDescentData G) PUnit.unit PUnit.unit) :=
          cechOverlapSourceTopology
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit
        letI : TopologicalSpace
            (CechOverlapTargetTotal
              (singlePatchCechDescentData G) PUnit.unit PUnit.unit) :=
          cechOverlapTargetTopology
            (singlePatchCechDescentData G) PUnit.unit PUnit.unit
        apply Homeomorph.ext
        intro z
        change ((singlePatchJointlyContinuousTransition G).homeomorph
          PUnit.unit PUnit.unit).symm
            ((singlePatchJointlyContinuousTransition G).toFun
              PUnit.unit PUnit.unit z) = z
        exact ((singlePatchJointlyContinuousTransition G).homeomorph
          PUnit.unit PUnit.unit).symm_apply_apply z }

noncomputable def singlePatchCommonMotherAtlasWitness_holomorphic
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B)) :
    JointlyHolomorphicTransitionData
      (singlePatchCechDescentData G) :=
  (singlePatchCommonMotherAtlasWitness G).toHolomorphic

/-! The first genuinely multi-patch construction.  Every local family is the
restriction of one global analytic family to an open member of the cover.
On an overlap the two subtype points have the same underlying point of `B`,
so the transition is the identity after transporting the dependent fibre
along that equality.  The cocycle is consequently not an additional
postulate: it is the equality of three copies of the same global fibre. -/

noncomputable def multiPatchCechDescentData
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    HolomorphicCechDescentData S B I := by
  let localFamily : ∀ i,
      ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
        (S := S) (B := cover i) :=
    fun i => G.restrictBaseOpen (cover i) (cover_open i)
  refine
    { cover := cover
      cover_open := cover_open
      cover_univ := cover_univ
      localFamily := localFamily
      transition := by
        intro i j x
        have hbase :
            ((CechOverlap.leftPoint cover i j x : cover i) : B) =
              ((CechOverlap.rightPoint cover i j x : cover j) : B) := by
          rfl
        apply markedSurfaceIdentityHomeomorph
          ((localFamily i).family.fiber
            (CechOverlap.leftPoint cover i j x))
          ((localFamily j).family.fiber
            (CechOverlap.rightPoint cover i j x))
        change G.family.fiber
            ((CechOverlap.leftPoint cover i j x : cover i) : B) =
          G.family.fiber
            ((CechOverlap.rightPoint cover i j x : cover j) : B)
        exact congrArg G.family.fiber hbase
      transition_holomorphic := by
        intro i j x
        have hbase :
            ((CechOverlap.leftPoint cover i j x : cover i) : B) =
              ((CechOverlap.rightPoint cover i j x : cover j) : B) := by
          rfl
        cases hbase
        let F := (localFamily i).family.fiber
          (CechOverlap.leftPoint cover i j x)
        letI : TopologicalSpace F.carrier := F.topology
        exact AtlasHolomorphicEquiv.refl F.surface.atlas
      transition_marking_commutes := by
        intro i j x s
        have hbase :
            ((CechOverlap.leftPoint cover i j x : cover i) : B) =
              ((CechOverlap.rightPoint cover i j x : cover j) : B) := by
          rfl
        cases hbase
        rfl
      transition_self := by
        intro i x
        have hbase :
            ((CechOverlap.leftPoint cover i i x : cover i) : B) =
              ((CechOverlap.rightPoint cover i i x : cover i) : B) := by
          rfl
        cases hbase
        rfl
      transition_comp := by
        intro i j k x
        have h₁ :
            ((CechOverlap.leftPoint cover i k
                (CechTripleOverlap.toIK cover i j k x) : cover i) : B) =
              ((CechOverlap.rightPoint cover i k
                (CechTripleOverlap.toIK cover i j k x) : cover k) : B) := by
          rfl
        have h₂ :
            ((CechOverlap.leftPoint cover i j
                (CechTripleOverlap.toIJ cover i j k x) : cover i) : B) =
              ((CechOverlap.rightPoint cover i j
                (CechTripleOverlap.toIJ cover i j k x) : cover j) : B) := by
          rfl
        have h₃ :
            ((CechOverlap.leftPoint cover j k
                (CechTripleOverlap.toJK cover i j k x) : cover j) : B) =
              ((CechOverlap.rightPoint cover j k
                (CechTripleOverlap.toJK cover i j k x) : cover k) : B) := by
          rfl
        cases h₁
        cases h₂
        cases h₃
        rfl }

/-! The multi-patch object does not merely remember fibrewise complex
structures as an opaque proposition.  Each local chart transition is the
transition of the actual global atlas restricted to the corresponding open
base patch.  This lemma exposes that analytic input at the level at which
the later quotient-chart construction can consume it. -/

theorem multiPatchLocalAtlas_transition_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i : I)
    (a b :
      (G.restrictBaseOpen (cover i) (cover_open i)).atlas.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart a)
        ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart b))
      (ComplexSurfaceChart.overlap
        ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart a)
        ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart b)) := by
  exact ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.transition_differentiableOn
    (G.restrictBaseOpen (cover i) (cover_open i)) a b

theorem multiPatchCechDescentData_localAtlas_transition_differentiableOn
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i : I)
    (a b :
      (multiPatchCechDescentData G cover cover_open cover_univ).localFamily i
        |>.atlas.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i
          |>.atlas.chart a)
        ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i
          |>.atlas.chart b))
      (ComplexSurfaceChart.overlap
        ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i
          |>.atlas.chart a)
        ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i
          |>.atlas.chart b)) := by
  change DifferentiableOn ℂ
    (ComplexSurfaceChart.transitionMap
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart a)
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart b))
    (ComplexSurfaceChart.overlap
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart a)
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart b))
  exact multiPatchLocalAtlas_transition_differentiableOn
    G cover cover_open cover_univ i a b

/-! The restricted chart is not merely abstractly inherited from the global
    family: its actual coordinate value agrees with the original global chart
    after the canonical pullback-to-subtype homeomorphism.  This is the local
    pointwise interface used when comparing the source and target overlap
    atlases. -/

theorem multiPatchLocalChart_apply_val_eq_global
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (i : I) (k : G.atlas.index)
    (x : ComplexSurfaceFamily.Total
      (ComplexSurfaceFamily.canonicalPullback G.family
        (fun v : cover i => (v : B)) continuous_subtype_val))
    (hx : x ∈
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain)
    (hxo :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        G.family (cover i) x).1 ∈ (G.atlas.chart k).domain) ) :
    (((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).chart
      ⟨x, hx⟩).1 =
      ((G.atlas.chart k).chart
        ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
            G.family (cover i) x).1, hxo⟩).1 := by
  exact G.baseOpenPullbackWitness_chart_apply_val
    (cover i) (cover_open i) k x hx hxo

/-! The preceding restriction comparison can be composed with the quotient
    overlap chart calculation.  This is the pointwise bridge from a chart on
    the actual Cech-overlap total space to the original chart of the global
    family.  No choice of a plane model for the fibre is made here: the point
    is transported through the canonical pullback subtype homeomorphism. -/

theorem multiPatchOverlapSourceChart_apply_val_eq_global
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (z : CechOverlapSourceTotal
      (multiPatchCechDescentData G cover cover_open cover_univ) i j)
    (hz : z ∈
      ((overlapSourceAtlas
        (multiPatchCechDescentData G cover cover_open cover_univ) i j).chart k).domain)
    (hx : overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j z ∈
      (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).atlas.chart k).domain)
    (hxo :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        G.family (cover i)
        (overlapSourceFibreMap
          (multiPatchCechDescentData G cover cover_open cover_univ) i j z)).1 ∈
        (G.atlas.chart k).domain) ) :
    (((overlapSourceAtlas
      (multiPatchCechDescentData G cover cover_open cover_univ) i j).chart k).chart
      ⟨z, hz⟩).1 =
      ((G.atlas.chart k).chart
        ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
            G.family (cover i)
            (overlapSourceFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j z)).1,
          hxo⟩).1 := by
  rw [overlapSourceAtlas_chart_apply_val
    (multiPatchCechDescentData G cover cover_open cover_univ) i j k z hz hx]
  change
    (((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).chart
      ⟨overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j z, hx⟩).1 = _
  exact multiPatchLocalChart_apply_val_eq_global
    G cover cover_open i k
    (overlapSourceFibreMap
      (multiPatchCechDescentData G cover cover_open cover_univ) i j z)
    hx hxo

theorem multiPatchOverlapTargetChart_apply_val_eq_global
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (z : CechOverlapTargetTotal
      (multiPatchCechDescentData G cover cover_open cover_univ) i j)
    (hz : z ∈
      ((overlapTargetAtlas
        (multiPatchCechDescentData G cover cover_open cover_univ) i j).chart k).domain)
    (hx : overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j z ∈
      (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).atlas.chart k).domain)
    (hxo :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        G.family (cover j)
        (overlapTargetFibreMap
          (multiPatchCechDescentData G cover cover_open cover_univ) i j z)).1 ∈
        (G.atlas.chart k).domain) ) :
    (((overlapTargetAtlas
      (multiPatchCechDescentData G cover cover_open cover_univ) i j).chart k).chart
      ⟨z, hz⟩).1 =
      ((G.atlas.chart k).chart
        ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
            G.family (cover j)
            (overlapTargetFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j z)).1,
          hxo⟩).1 := by
  rw [overlapTargetAtlas_chart_apply_val
    (multiPatchCechDescentData G cover cover_open cover_univ) i j k z hz hx]
  change
    (((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).chart
      ⟨overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j z, hx⟩).1 = _
  exact multiPatchLocalChart_apply_val_eq_global
    G cover cover_open j k
    (overlapTargetFibreMap
      (multiPatchCechDescentData G cover cover_open cover_univ) i j z)
    hx hxo

/-! A reusable compact-fibre replacement for the impossible global-plane
    comparison interface.  The parameter type `P` may be an actual Cech
    overlap total space, while `X` is the common lifted total space.  The
    fields expose exactly the data that a concrete family must provide:
    source/target quotient coordinates agree with two lifted charts, and the
    lifted charts are controlled by an explicit deck-transition cover. -/

structure CompactFiberLiftToCechComparisonWitness
    {P X : Type u} [topology : TopologicalSpace X]
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    (M : Type u) where
  liftPoint : P → X
  sourceDomain : ∀ p, liftPoint p ∈ sourceChart.domain
  targetDomain : ∀ p, liftPoint p ∈ targetChart.domain
  sourceCoordinate : P → ℂ × ℂ
  targetCoordinate : P → ℂ × ℂ
  sourceCoordinate_eq_lift : ∀ p,
    sourceCoordinate p =
      (sourceChart.chart ⟨liftPoint p, sourceDomain p⟩).1
  targetCoordinate_eq_lift : ∀ p,
    targetCoordinate p =
      (targetChart.chart ⟨liftPoint p, targetDomain p⟩).1
  deckCover : ComplexSurfaceChartDeckTransitionCover
    topology sourceChart targetChart M

theorem CompactFiberLiftToCechComparisonWitness.sourceCoordinate_mem_overlap
    {P X M : Type u} [topology : TopologicalSpace X]
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (W : CompactFiberLiftToCechComparisonWitness
      sourceChart targetChart M)
    (p : P) :
    W.sourceCoordinate p ∈
      ComplexSurfaceChart.overlap sourceChart targetChart := by
  rw [W.sourceCoordinate_eq_lift]
  let x := W.liftPoint p
  let hx := W.sourceDomain p
  let hsourceRange :
      (sourceChart.chart ⟨x, hx⟩).1 ∈ sourceChart.range :=
    (sourceChart.chart ⟨x, hx⟩).property
  refine ⟨hsourceRange, ?_⟩
  have hpoint :
      (sourceChart.chart.symm
        ⟨(sourceChart.chart ⟨x, hx⟩).1, hsourceRange⟩).1 = x := by
    have hchart :
        (⟨(sourceChart.chart ⟨x, hx⟩).1, hsourceRange⟩ :
          {q : ℂ × ℂ // q ∈ sourceChart.range}) =
          sourceChart.chart ⟨x, hx⟩ := by
      apply Subtype.ext
      rfl
    calc
      (sourceChart.chart.symm
          ⟨(sourceChart.chart ⟨x, hx⟩).1, hsourceRange⟩).1 =
          (sourceChart.chart.symm (sourceChart.chart ⟨x, hx⟩)).1 := by
            exact congrArg Subtype.val
              (congrArg sourceChart.chart.symm hchart)
      _ = x := by
        exact congrArg Subtype.val
          (sourceChart.chart.symm_apply_apply ⟨x, hx⟩)
  rw [hpoint]
  exact W.targetDomain p

theorem CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_deck
    {P X M : Type u} [topology : TopologicalSpace X]
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (W : CompactFiberLiftToCechComparisonWitness
      sourceChart targetChart M)
    (p : P) :
    ∃ i : M,
      W.sourceCoordinate p ∈ (W.deckCover.sheet i).source ∧
      W.targetCoordinate p =
        W.deckCover.deck i (W.sourceCoordinate p) := by
  have h := W.deckCover.chart_transition_eq_deck_at
    (W.liftPoint p) (W.sourceDomain p) (W.targetDomain p)
  rcases h with ⟨i, hsource, htarget⟩
  refine ⟨i, ?_, ?_⟩
  · rw [W.sourceCoordinate_eq_lift]
    exact hsource
  · rw [W.targetCoordinate_eq_lift, W.sourceCoordinate_eq_lift]
    exact htarget

theorem CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_selected_deck
    {P X M : Type u} [topology : TopologicalSpace X]
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (W : CompactFiberLiftToCechComparisonWitness
      sourceChart targetChart M)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (W.deckCover.sheet i).source (W.deckCover.sheet j).source)
    (p : P) :
    W.targetCoordinate p =
      W.deckCover.deck
        (W.deckCover.sheetSelector
          ⟨W.sourceCoordinate p, W.sourceCoordinate_mem_overlap p⟩)
        (W.sourceCoordinate p) := by
  obtain ⟨i, hi, htarget⟩ := W.targetCoordinate_eq_deck p
  have hselector :
      W.deckCover.sheetSelector
          ⟨W.sourceCoordinate p, W.sourceCoordinate_mem_overlap p⟩ = i := by
    apply W.deckCover.sheetSelector_eq_of_mem pairwise_disjoint
    exact hi
  rw [hselector]
  exact htarget

theorem CompactFiberLiftToCechComparisonWitness.targetCoordinate_eq_selectedDeckMap
    {P X M : Type u} [topology : TopologicalSpace X]
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (W : CompactFiberLiftToCechComparisonWitness
      sourceChart targetChart M)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (W.deckCover.sheet i).source (W.deckCover.sheet j).source)
    (p : P) :
    W.targetCoordinate p =
      W.deckCover.selectedDeckMap
        ⟨W.sourceCoordinate p, W.sourceCoordinate_mem_overlap p⟩ := by
  exact W.targetCoordinate_eq_selected_deck pairwise_disjoint p

noncomputable def multiPatchOverlapHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) :
    @Homeomorph
      (CechOverlapSourceTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (CechOverlapTargetTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapSourceTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapTargetTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  let O := CechOverlap cover i j
  let q : O → B := fun p => (p : B)
  have hq : Continuous q := by
    exact continuous_subtype_val
  let Q := ComplexSurfaceFamily.canonicalPullback G.family q hq
  letI : TopologicalSpace (ComplexSurfaceFamily.Total Q) := Q.totalTopology
  let fi : cover i → B := fun b => (b : B)
  let fj : cover j → B := fun b => (b : B)
  let li : O → cover i := CechOverlap.leftPoint cover i j
  let rj : O → cover j := CechOverlap.rightPoint cover i j
  have hfi : Continuous fi := continuous_subtype_val
  have hfj : Continuous fj := continuous_subtype_val
  have hli : Continuous li :=
    (HolomorphicCechDescentData.isOpenEmbedding_cechOverlap_leftPoint D i j).continuous
  have hrj : Continuous rj :=
    (HolomorphicCechDescentData.isOpenEmbedding_cechOverlap_rightPoint D i j).continuous
  have hsource :
      @Homeomorph
        (ComplexSurfaceFamily.Total Q)
        (CechOverlapSourceTotal D i j)
        Q.totalTopology
        (cechOverlapSourceTopology D i j) := by
    have h_to :
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fi li hfi hli).toFun = (fun z => z) := by
      funext z
      exact ComplexSurfaceFamily.canonicalPullback_comp_homeomorph_apply
        G.family fi li hfi hli z
    letI : TopologicalSpace
        (Sigma fun d => (G.family.fiber (fi (li d))).carrier) :=
      Q.totalTopology
    letI : TopologicalSpace
        (Sigma fun d =>
          ((ComplexSurfaceFamily.canonicalPullback G.family fi hfi).fiber
            (li d)).carrier) :=
      cechOverlapSourceTopology D i j
    have h_inv :
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fi li hfi hli).invFun = (fun z => z) := by
      funext z
      have hz :=
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fi li hfi hli).right_inv z
      rw [h_to] at hz
      exact hz
    change @Homeomorph
      (Sigma fun d => (G.family.fiber (fi (li d))).carrier)
      (Sigma fun d =>
        ((ComplexSurfaceFamily.canonicalPullback G.family fi hfi).fiber
          (li d)).carrier)
      Q.totalTopology
      (cechOverlapSourceTopology D i j)
    refine
      { toFun := fun z => z
        invFun := fun z => z
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl
        continuous_toFun := ?_
        continuous_invFun := ?_ }
    · rw [HolomorphicCechDescentData.cechOverlapSourceTopology_eq_pullbackTopology
        D i j]
      change @Continuous _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fi (li d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fi hfi) li)
        (fun z => z)
      rw [← h_to]
      exact @Homeomorph.continuous_toFun _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fi (li d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fi hfi) li)
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fi li hfi hli)
    · rw [HolomorphicCechDescentData.cechOverlapSourceTopology_eq_pullbackTopology
        D i j]
      change @Continuous _ _
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fi hfi) li)
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fi (li d)))
        (fun z => z)
      rw [← h_inv]
      exact @Homeomorph.continuous_invFun _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fi (li d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fi hfi) li)
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fi li hfi hli)
  have htarget :
      @Homeomorph
        (ComplexSurfaceFamily.Total Q)
        (CechOverlapTargetTotal D i j)
        Q.totalTopology
        (cechOverlapTargetTopology D i j) := by
    have h_to :
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fj rj hfj hrj).toFun = (fun z => z) := by
      funext z
      exact ComplexSurfaceFamily.canonicalPullback_comp_homeomorph_apply
        G.family fj rj hfj hrj z
    letI : TopologicalSpace
        (Sigma fun d => (G.family.fiber (fj (rj d))).carrier) :=
      Q.totalTopology
    letI : TopologicalSpace
        (Sigma fun d =>
          ((ComplexSurfaceFamily.canonicalPullback G.family fj hfj).fiber
            (rj d)).carrier) :=
      cechOverlapTargetTopology D i j
    have h_inv :
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fj rj hfj hrj).invFun = (fun z => z) := by
      funext z
      have hz :=
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fj rj hfj hrj).right_inv z
      rw [h_to] at hz
      exact hz
    change @Homeomorph
      (Sigma fun d => (G.family.fiber (fj (rj d))).carrier)
      (Sigma fun d =>
        ((ComplexSurfaceFamily.canonicalPullback G.family fj hfj).fiber
          (rj d)).carrier)
      Q.totalTopology
      (cechOverlapTargetTopology D i j)
    refine
      { toFun := fun z => z
        invFun := fun z => z
        left_inv := by intro z; rfl
        right_inv := by intro z; rfl
        continuous_toFun := ?_
        continuous_invFun := ?_ }
    · rw [HolomorphicCechDescentData.cechOverlapTargetTopology_eq_pullbackTopology
        D i j]
      change @Continuous _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fj (rj d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fj hfj) rj)
        (fun z => z)
      rw [← h_to]
      exact @Homeomorph.continuous_toFun _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fj (rj d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fj hfj) rj)
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fj rj hfj hrj)
    · rw [HolomorphicCechDescentData.cechOverlapTargetTopology_eq_pullbackTopology
        D i j]
      change @Continuous _ _
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fj hfj) rj)
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fj (rj d)))
        (fun z => z)
      rw [← h_inv]
      exact @Homeomorph.continuous_invFun _ _
        (ComplexSurfaceFamily.pullbackTopology G.family (fun d => fj (rj d)))
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback G.family fj hfj) rj)
        (ComplexSurfaceFamily.canonicalPullback_comp_homeomorph
          G.family fj rj hfj hrj)
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  exact hsource.symm.trans htarget

theorem multiPatchOverlapHomeomorph_apply
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I)
    (z : CechOverlapSourceTotal
      (multiPatchCechDescentData G cover cover_open cover_univ) i j) :
    multiPatchOverlapHomeomorph G cover cover_open cover_univ i j z =
      overlapTransitionMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j z := by
  rcases z with ⟨p, x⟩
  simp only [multiPatchOverlapHomeomorph, multiPatchCechDescentData,
    HolomorphicCechDescentData.overlapTransitionMap, Function.id_def]
  rfl

noncomputable def multiPatchJointlyContinuousTransition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    JointlyContinuousTransitionData
      (multiPatchCechDescentData G cover cover_open cover_univ) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  refine
    { toFun := fun i j =>
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        multiPatchOverlapHomeomorph G cover cover_open cover_univ i j
      invFun := fun i j =>
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        (multiPatchOverlapHomeomorph
          G cover cover_open cover_univ i j).symm
      left_inv := by
        intro i j z
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        exact (multiPatchOverlapHomeomorph
          G cover cover_open cover_univ i j).symm_apply_apply z
      right_inv := by
        intro i j z
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        exact (multiPatchOverlapHomeomorph
          G cover cover_open cover_univ i j).apply_symm_apply z
      continuous_toFun := by
        intro i j
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        exact (multiPatchOverlapHomeomorph
          G cover cover_open cover_univ i j).continuous_toFun
      continuous_invFun := by
        intro i j
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        exact (multiPatchOverlapHomeomorph
          G cover cover_open cover_univ i j).continuous_invFun
      toFun_agrees := by
        intro i j z
        exact multiPatchOverlapHomeomorph_apply
          G cover cover_open cover_univ i j z }

noncomputable def multiPatchJointlyTransitionHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) :
    @Homeomorph
      (CechOverlapSourceTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (CechOverlapTargetTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapSourceTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapTargetTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  exact (multiPatchJointlyContinuousTransition
    G cover cover_open cover_univ).homeomorph i j

noncomputable def multiPatchJointlyTransitionHomeomorphInv
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) :
    @Homeomorph
      (CechOverlapTargetTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (CechOverlapSourceTotal
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapTargetTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j)
      (cechOverlapSourceTopology
        (multiPatchCechDescentData G cover cover_open cover_univ) i j) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
    cechOverlapSourceTopology D i j
  letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
    cechOverlapTargetTopology D i j
  exact (multiPatchJointlyTransitionHomeomorph
    G cover cover_open cover_univ i j).symm

theorem multiPatchJointlyTransitionHomeomorphInv_apply_id
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I)
    (z : CechOverlapTargetTotal
      (multiPatchCechDescentData G cover cover_open cover_univ) i j) :
    multiPatchJointlyTransitionHomeomorphInv
        G cover cover_open cover_univ i j z =
      ⟨z.1, z.2⟩ := by
  rcases z with ⟨p, x⟩
  rfl

theorem multiPatchOverlapAtlas_coverSet_eq_targetTransport
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) :
    (overlapTargetAtlas
        (multiPatchCechDescentData G cover cover_open cover_univ) i j).coverSet =
      (ComplexSurfaceAtlas.transport
        (overlapSourceAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j)
        (multiPatchJointlyTransitionHomeomorphInv
          G cover cover_open cover_univ i j)).coverSet := by
  rw [ComplexSurfaceAtlas.transport_coverSet]
  ext z
  rfl

/-! The fibrewise identity transition also identifies the restricted chart
    domains and coordinate values on each overlap.  These four elementary
    lemmas are kept explicit because the overlap atlases live on subtype
    total spaces, while the local family charts live on the unrestricted
    total spaces. -/

theorem multiPatchOverlap_local_coord
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (p : CechOverlap cover i j)
    (y : (G.family.fiber
      ((CechOverlap.rightPoint cover i j p : cover j) : B)).carrier)
    (ht : overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).domain)
    (hs : overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain) :
    (((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).chart
      ⟨overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩, ht⟩).1 =
    (((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).chart
      ⟨overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩, hs⟩).1 := by
  have hbase :
      ((CechOverlap.leftPoint cover i j p : cover i) : B) =
        ((CechOverlap.rightPoint cover i j p : cover j) : B) := by
    rfl
  cases hbase
  rfl

theorem multiPatchOverlap_local_domain
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (p : CechOverlap cover i j)
    (y : (G.family.fiber
      ((CechOverlap.rightPoint cover i j p : cover j) : B)).carrier)
    (ht : overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).domain) :
    overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain := by
  have hbase :
      ((CechOverlap.leftPoint cover i j p : cover i) : B) =
        ((CechOverlap.rightPoint cover i j p : cover j) : B) := by
    rfl
  cases hbase
  exact ht

theorem multiPatchOverlap_local_domain_rev
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (p : CechOverlap cover i j)
    (y : (G.family.fiber
      ((CechOverlap.leftPoint cover i j p : cover i) : B)).carrier)
    (hs : overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain) :
    overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).domain := by
  have hbase :
      ((CechOverlap.leftPoint cover i j p : cover i) : B) =
        ((CechOverlap.rightPoint cover i j p : cover j) : B) := by
    rfl
  cases hbase
  exact hs

theorem multiPatchOverlap_local_coord_rev
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) (k : G.atlas.index)
    (p : CechOverlap cover i j)
    (y : (G.family.fiber
      ((CechOverlap.leftPoint cover i j p : cover i) : B)).carrier)
    (hs : overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain)
    (ht : overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩ ∈
      ((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).domain) :
    (((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).chart
      ⟨overlapSourceFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩, hs⟩).1 =
    (((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).chart
      ⟨overlapTargetFibreMap
        (multiPatchCechDescentData G cover cover_open cover_univ) i j
        ⟨p, y⟩, ht⟩).1 := by
  have hbase :
      ((CechOverlap.leftPoint cover i j p : cover i) : B) =
        ((CechOverlap.rightPoint cover i j p : cover j) : B) := by
    rfl
  cases hbase
  rfl

theorem multiPatchOverlapAtlas_eq_targetTransport
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (i j : I) :
    overlapTargetAtlas
        (multiPatchCechDescentData G cover cover_open cover_univ) i j =
      ComplexSurfaceAtlas.transport
        (overlapSourceAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j)
        (multiPatchJointlyTransitionHomeomorphInv
          G cover cover_open cover_univ i j) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  unfold HolomorphicCechDescentData.overlapTargetAtlas
    HolomorphicCechDescentData.overlapSourceAtlas
  refine ComplexSurfaceAtlas.ext ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rw [ComplexSurfaceAtlas.transport_coverSet]
    ext z
    rfl
  · intro k
    dsimp [ComplexSurfaceAtlas.transport,
      ComplexSurfaceAtlas.restrictOpenSubspace] at k
    apply heq_of_eq
    let Achart :=
      (overlapTargetAtlas
        (multiPatchCechDescentData G cover cover_open cover_univ) i j).chart k
    let Bchart :=
      (ComplexSurfaceAtlas.transport
        (overlapSourceAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j)
        (multiPatchJointlyTransitionHomeomorphInv
          G cover cover_open cover_univ i j)).chart k
    change Achart = Bchart
    have hdom : Achart.domain = Bchart.domain := by
      simp only [Achart, Bchart, ComplexSurfaceAtlas.transport_chart,
        ComplexSurfaceChart.transport_domain, Set.mem_preimage]
      ext z
      rcases z with ⟨p, x⟩
      simp only [ComplexSurfaceAtlas.restrictOpenSubspace_chart,
        ComplexSurfaceChart.restrictOpenSubspace_domain,
        ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.restrictBaseOpen,
        ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.pullbackOf,
        ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.baseOpenPullbackWitness_chart_domain,
        ComplexSurfaceFamily.retopologizeHomeomorph_apply,
        ComplexSurfaceChart.transport_domain,
        multiPatchCechDescentData,
        Set.mem_preimage]
      change _ ↔
        multiPatchJointlyTransitionHomeomorphInv
            G cover cover_open cover_univ i j ⟨p, x⟩ ∈ _
      rw [multiPatchJointlyTransitionHomeomorphInv_apply_id]
      constructor <;> intro h <;> exact h
    have hrange : Achart.range = Bchart.range := by
      unfold HolomorphicCechDescentData.overlapTargetAtlas at Achart
      unfold HolomorphicCechDescentData.overlapSourceAtlas at Bchart
      simp only [Achart, Bchart,
        HolomorphicCechDescentData.overlapTargetAtlas,
        HolomorphicCechDescentData.overlapSourceAtlas,
        ComplexSurfaceAtlas.transport_chart,
        ComplexSurfaceChart.transport_range]
      simp only [ComplexSurfaceAtlas.restrictOpenSubspace_chart]
      rw [ComplexSurfaceChart.restrictOpenSubspace_range,
        ComplexSurfaceChart.restrictOpenSubspace_range]
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, ⟨x1, hx, hchart⟩, hxz⟩
        change (x1 : ComplexSurfaceFamily.Total
          ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).family) ∈
          Set.range
          (overlapTargetFibreMap
            (multiPatchCechDescentData G cover cover_open cover_univ) i j) at hx
        obtain ⟨q, hxy⟩ := hx
        have ht : overlapTargetFibreMap
            (multiPatchCechDescentData G cover cover_open cover_univ) i j q ∈
          ((G.restrictBaseOpen (cover j) (cover_open j)).atlas.chart k).domain := by
          rw [hxy]
          exact x1.property
        have hs := multiPatchOverlap_local_domain
          G cover cover_open cover_univ i j k q.1 q.2 ht
        have hcoord := multiPatchOverlap_local_coord
          G cover cover_open cover_univ i j k q.1 q.2 ht hs
        have hx1_eq : x1 =
            ⟨overlapTargetFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j
            q, ht⟩ := by
          apply Subtype.ext
          exact hxy.symm
        let s0 :=
          (⟨overlapSourceFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j
              q, hs⟩ :
            {x : ComplexSurfaceFamily.Total
                ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).family //
              x ∈ (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).atlas.chart k).domain})
        let c0 := (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).atlas.chart k).chart s0
        refine ⟨c0, ?_, ?_⟩
        · refine ⟨s0, ?_⟩
          constructor
          · exact ⟨q, rfl⟩
          · apply Subtype.ext
            rfl
        · have hcoord' :
              ((((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).atlas.chart k).chart x1).1 = c0.1 := by
            rw [hx1_eq]
            dsimp [s0, c0]
            convert hcoord using 1 <;> rfl
          calc
            (↑c0 : ℂ × ℂ) = (x : ℂ × ℂ) := hcoord'.symm ▸ congrArg Subtype.val hchart
            _ = z := hxz
      · rintro ⟨x, ⟨x1, hx, hchart⟩, hxz⟩
        change (x1 : ComplexSurfaceFamily.Total
          ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).family) ∈
          Set.range
          (overlapSourceFibreMap
            (multiPatchCechDescentData G cover cover_open cover_univ) i j) at hx
        obtain ⟨q, hxy⟩ := hx
        have hs : overlapSourceFibreMap
            (multiPatchCechDescentData G cover cover_open cover_univ) i j q ∈
          ((G.restrictBaseOpen (cover i) (cover_open i)).atlas.chart k).domain := by
          rw [hxy]
          exact x1.property
        have ht := multiPatchOverlap_local_domain_rev
          G cover cover_open cover_univ i j k q.1 q.2 hs
        have hcoord := multiPatchOverlap_local_coord_rev
          G cover cover_open cover_univ i j k q.1 q.2 hs ht
        have hx1_eq : x1 =
            ⟨overlapSourceFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j
              q, hs⟩ := by
          apply Subtype.ext
          exact hxy.symm
        let t0 :=
          (⟨overlapTargetFibreMap
              (multiPatchCechDescentData G cover cover_open cover_univ) i j
              ⟨q.1, q.2⟩, ht⟩ :
            {x : ComplexSurfaceFamily.Total
                ((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).family //
              x ∈ (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).atlas.chart k).domain})
        let c0 := (((multiPatchCechDescentData G cover cover_open cover_univ).localFamily j).atlas.chart k).chart t0
        refine ⟨c0, ?_, ?_⟩
        · refine ⟨t0, ?_⟩
          constructor
          · exact ⟨⟨q.1, q.2⟩, rfl⟩
          · apply Subtype.ext
            rfl
        · have hcoord' :
              ((((multiPatchCechDescentData G cover cover_open cover_univ).localFamily i).atlas.chart k).chart x1).1 = c0.1 := by
            rw [hx1_eq]
            dsimp [t0, c0]
            convert hcoord using 1 <;> rfl
          calc
            (↑c0 : ℂ × ℂ) = (x : ℂ × ℂ) := hcoord' ▸ congrArg Subtype.val hchart
            _ = z := hxz
    apply ComplexSurfaceChart.ext hdom hrange
    refine ComplexSurfaceChart.homeomorph_heq_of_pointwise _ _ Achart.chart Bchart.chart
      hdom hrange ?_
    intro x
    change (Achart.chart x).1 =
      (Bchart.chart ⟨x.1, _⟩).1
    dsimp [Achart, Bchart]
    simp only [HolomorphicCechDescentData.overlapTargetAtlas,
      HolomorphicCechDescentData.overlapSourceAtlas,
      ComplexSurfaceAtlas.transport_chart,
      ComplexSurfaceChart.transport_chart_apply,
      ComplexSurfaceChart.transport_chart_val,
      ComplexSurfaceChart.restrictOpenSubspace_chart_apply]
    dsimp [ComplexSurfaceChart.transport]
    simp only [ComplexSurfaceFamily.retopologizeHomeomorph_apply,
      ComplexSurfaceChart.restrictOpenSubspace_chart_apply,
      multiPatchJointlyTransitionHomeomorphInv_apply_id,
      Equiv.coe_fn_mk]
    rfl

noncomputable def multiPatchCommonMotherAtlasWitness_of_targetTransport
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (hTarget : ∀ i j,
      overlapTargetAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j =
        ComplexSurfaceAtlas.transport
          (overlapSourceAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j)
          (multiPatchJointlyTransitionHomeomorphInv
            G cover cover_open cover_univ i j)) :
    CommonMotherAtlasTransitionWitness
      (multiPatchCechDescentData G cover cover_open cover_univ) := by
  let D := multiPatchCechDescentData G cover cover_open cover_univ
  let J := multiPatchJointlyContinuousTransition G cover cover_open cover_univ
  refine
    { toJointlyContinuousTransitionData := J
      motherCarrier := fun i j => CechOverlapSourceTotal D i j
      motherAtlas := fun i j => overlapSourceAtlas D i j
      sourceHomeomorph := fun i j => by
        exact @Homeomorph.refl
          (CechOverlapSourceTotal D i j)
          (cechOverlapSourceTopology D i j)
      targetHomeomorph := fun i j => by
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        exact multiPatchJointlyTransitionHomeomorphInv
          G cover cover_open cover_univ i j
      source_atlas_eq := by
        intro i j
        exact (ComplexSurfaceAtlas.transport_refl
          (overlapSourceAtlas D i j)).symm
      target_atlas_eq := by
        intro i j
        exact hTarget i j
      comparison_comp := by
        intro i j
        letI : TopologicalSpace (CechOverlapSourceTotal D i j) :=
          cechOverlapSourceTopology D i j
        letI : TopologicalSpace (CechOverlapTargetTotal D i j) :=
          cechOverlapTargetTopology D i j
        apply Homeomorph.ext
        intro z
        change (J.homeomorph i j).symm (J.toFun i j z) = z
        exact (J.homeomorph i j).symm_apply_apply z }

noncomputable def multiPatchJointlyHolomorphicTransition_of_targetTransport
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ)
    (hTarget : ∀ i j,
      overlapTargetAtlas
          (multiPatchCechDescentData G cover cover_open cover_univ) i j =
        ComplexSurfaceAtlas.transport
          (overlapSourceAtlas
            (multiPatchCechDescentData G cover cover_open cover_univ) i j)
          (multiPatchJointlyTransitionHomeomorphInv
            G cover cover_open cover_univ i j)) :
    JointlyHolomorphicTransitionData
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  (multiPatchCommonMotherAtlasWitness_of_targetTransport
    G cover cover_open cover_univ hTarget).toHolomorphic

/-! The preceding conditional interface is now inhabited for the concrete
    multi-patch object: the exact chart equality above supplies its target
    hypothesis, so no residual atlas-comparison axiom is needed here. -/

noncomputable def multiPatchCommonMotherAtlasWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    CommonMotherAtlasTransitionWitness
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  multiPatchCommonMotherAtlasWitness_of_targetTransport
    G cover cover_open cover_univ
    (fun i j => multiPatchOverlapAtlas_eq_targetTransport
      G cover cover_open cover_univ i j)

noncomputable def multiPatchJointlyHolomorphicTransition
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    JointlyHolomorphicTransitionData
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  (multiPatchCommonMotherAtlasWitness G cover cover_open cover_univ).toHolomorphic

/-! The quotient-facing topological descent is now also named at the concrete
    multi-patch level.  No new openness axiom is introduced here: the
    `multiPatchJointlyContinuousTransition` already has an actual homeomorphism
    on every overlap, so the generic saturation argument constructs the open
    quotient witness and the descended chart family.  The holomorphic version
    is exposed separately to make clear that the same descended topological
    object can be reached from the stronger analytic transition data. -/

noncomputable def multiPatchOpenGluingWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    OpenGluingWitness
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  openGluingWitness_of_jointlyContinuous
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (multiPatchJointlyContinuousTransition G cover cover_open cover_univ)

noncomputable def multiPatchDescendedChartFamily
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    @ComplexSurfaceChartFamily
      (DescendedTotal (multiPatchCechDescentData G cover cover_open cover_univ)) :=
  descendedChartFamily_of_openGluing
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (multiPatchOpenGluingWitness G cover cover_open cover_univ)

noncomputable def multiPatchDescendedChartFamily_of_holomorphic
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    @ComplexSurfaceChartFamily
      (DescendedTotal (multiPatchCechDescentData G cover cover_open cover_univ)) :=
  descendedChartFamily_of_jointlyContinuous
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (multiPatchJointlyHolomorphicTransition G cover cover_open cover_univ).toContinuous

noncomputable def multiPatchDescendedAtlasHolomorphicWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    DescendedAtlasHolomorphicWitness
      (multiPatchCechDescentData G cover cover_open cover_univ)
      (isOpenMap_quotientMk_of_openGluing
        (multiPatchCechDescentData G cover cover_open cover_univ)
        (multiPatchOpenGluingWitness G cover cover_open cover_univ)) :=
  descendedAtlasHolomorphicWitness_of_jointlyHolomorphic_transition
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (isOpenMap_quotientMk_of_openGluing
      (multiPatchCechDescentData G cover cover_open cover_univ)
      (multiPatchOpenGluingWitness G cover cover_open cover_univ))
    (multiPatchJointlyHolomorphicTransition G cover cover_open cover_univ)

/-! The descended atlas is compatible with the original family parameter.  In
    the restricted local families the parameter coordinate is definitionally
    the restriction of `G.atlas.parameterCoordinate`, so the generic quotient
    lemma above applies without an additional compatibility axiom. -/

noncomputable def multiPatchDescendedFamilyAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    @ComplexSurfaceFamilyAtlas
      (DescendedTotal (multiPatchCechDescentData G cover cover_open cover_univ))
      B inferInstance :=
  descendedFamilyAtlas
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (isOpenMap_quotientMk_of_openGluing
      (multiPatchCechDescentData G cover cover_open cover_univ)
      (multiPatchOpenGluingWitness G cover cover_open cover_univ))
    (multiPatchDescendedAtlasHolomorphicWitness G cover cover_open cover_univ)
    G.atlas.parameterCoordinate
    (by
      intro i b
      rfl)

/-! The local marking data now descends on the same quotient.  This wrapper
    exposes the concrete multi-patch witness, while the generic theorem in
    `MathlibCechDescent` proves independence of the chosen cover chart. -/

noncomputable def multiPatchDescendedMarkingWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    DescendedMarkingWitness
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  descendedMarkingWitness
    (multiPatchCechDescentData G cover cover_open cover_univ)

noncomputable def multiPatchDescendedMarkedAtlas
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    DescendedMarkedAtlas
      (multiPatchCechDescentData G cover cover_open cover_univ) :=
  descendedMarkedAtlas
    (multiPatchCechDescentData G cover cover_open cover_univ)
    (multiPatchDescendedFamilyAtlas G cover cover_open cover_univ)

@[simp] theorem multiPatchDescendedChartFamily_coverSet
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (G : ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily.{u, w, u}
      (S := S) (B := B))
    (cover : I → Set B)
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    (multiPatchDescendedChartFamily G cover cover_open cover_univ).coverSet =
      Set.univ := by
  rfl

end MathlibFormal
end Teichmuller
