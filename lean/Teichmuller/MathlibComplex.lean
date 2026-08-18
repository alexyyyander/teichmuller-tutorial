import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Teichmuller.MathlibTopology

namespace Teichmuller
namespace MathlibFormal

/-!
Concrete complex-analytic atlas data over Mathlib's topology.

This is intentionally a chart-level definition rather than an attempt to use
the real-smooth manifold API as a synonym for a Riemann surface.  A chart has
an open domain and range, inverse laws, continuity in both directions, and a
model map into `ℂ`.  Compatibility is the actual Mathlib predicate
`DifferentiableOn ℂ` for the transition map on the overlap.

Thus the remaining existence problem is visible: proving that a collection of
charts with these fields exists is separate from proving consequences of an
already supplied atlas.
-/

universe u w

/-- A local complex coordinate with an explicit topological inverse. -/
structure ComplexChart (X : Type u) [TopologicalSpace X] where
  domain : Set X
  range : Set ℂ
  domain_open : IsOpen domain
  range_open : IsOpen range
  toComplex : X → ℂ
  fromComplex : ℂ → X
  maps_into : Set.MapsTo toComplex domain range
  inverse_into : Set.MapsTo fromComplex range domain
  left_inv : Set.LeftInvOn fromComplex toComplex domain
  right_inv : Set.RightInvOn fromComplex toComplex range
  continuous_toComplex : ContinuousOn toComplex domain
  continuous_fromComplex : ContinuousOn fromComplex range

namespace ComplexChart

def overlap {X : Type u} [TopologicalSpace X]
    (i j : ComplexChart X) : Set ℂ :=
  i.range ∩ i.fromComplex ⁻¹' j.domain

def transitionMap {X : Type u} [TopologicalSpace X]
    (i j : ComplexChart X) : ℂ → ℂ :=
  fun z => j.toComplex (i.fromComplex z)

theorem transitionMap_agrees {X : Type u} [TopologicalSpace X]
    (i j : ComplexChart X) (z : ℂ) :
    transitionMap i j z = j.toComplex (i.fromComplex z) :=
  rfl

theorem chart_inverse_on_domain {X : Type u} [TopologicalSpace X]
    (c : ComplexChart X) {x : X} (hx : x ∈ c.domain) :
    c.fromComplex (c.toComplex x) = x :=
  c.left_inv hx

theorem chart_inverse_on_range {X : Type u} [TopologicalSpace X]
    (c : ComplexChart X) {z : ℂ} (hz : z ∈ c.range) :
    c.toComplex (c.fromComplex z) = z :=
  c.right_inv hz

end ComplexChart

/-! ### Two-complex-dimensional local charts

The one-dimensional `ComplexChart` above is the right interface for a Riemann
surface.  A varying family has a total space with two complex coordinates
(parameter plus fibre lift), so it needs a separate modelled-chart interface.
The chart is stored as a homeomorphism between the relevant subtypes.  This
avoids pretending that a chart has a canonical value outside its domain while
still exposing the open domain, open range, and the actual topological
coordinate equivalence needed for later transition calculations.
-/

/-- A local chart on a complex surface, modelled on an open subset of `ℂ × ℂ`. -/
structure ComplexSurfaceChart (X : Type u) (topology : TopologicalSpace X) where
  domain : Set X
  range : Set (ℂ × ℂ)
  domain_open : @IsOpen X topology domain
  range_open : IsOpen range
  chart : @Homeomorph
    {x // x ∈ domain} {z // z ∈ range}
    (TopologicalSpace.induced Subtype.val topology) inferInstance

namespace ComplexSurfaceChart

/-! ### Transport along a topological change of total-space coordinates

The following construction is the chart-level operation needed for base
change.  A homeomorphism of total spaces pulls an open chart back by its
preimage and conjugates the chart homeomorphism.  In particular, this is a
genuine operation on the atlas data, not merely a statement that two spaces
are abstractly homeomorphic.
-/

noncomputable def transport
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY) :
    ComplexSurfaceChart X topologyX where
  domain := e ⁻¹' A.domain
  range := A.range
  domain_open := A.domain_open.preimage e.continuous
  range_open := A.range_open
  chart := by
    letI : TopologicalSpace {x // x ∈ e ⁻¹' A.domain} :=
      TopologicalSpace.induced Subtype.val topologyX
    letI : TopologicalSpace {z // z ∈ A.range} := inferInstance
    exact
      { toFun := fun x => A.chart ⟨e x, x.property⟩
        invFun := fun z => ⟨e.symm (A.chart.symm z), by
          change e (e.symm (A.chart.symm z)) ∈ A.domain
          simpa using (A.chart.symm z).property⟩
        left_inv := by
          intro x
          apply Subtype.ext
          simp
        right_inv := by
          intro z
          apply Subtype.ext
          simp
        continuous_toFun := by
          apply A.chart.continuous_toFun.comp
          apply Continuous.subtype_mk
          exact e.continuous.comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact e.continuous_invFun.comp
            (continuous_subtype_val.comp A.chart.continuous_invFun) }

@[simp] theorem transport_domain
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY) :
    (A.transport e).domain = e ⁻¹' A.domain :=
  rfl

@[simp] theorem transport_chart_apply
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY)
    {x : X} (hx : x ∈ (A.transport e).domain) :
    (A.transport e).chart ⟨x, hx⟩ =
      A.chart ⟨e x, hx⟩ :=
  rfl

@[simp] theorem transport_chart_symm_apply
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY)
    {z : ℂ × ℂ} {hz : z ∈ A.range} :
    (A.transport e).chart.symm ⟨z, hz⟩ =
      ⟨e.symm (A.chart.symm ⟨z, hz⟩), by
        change e (e.symm (A.chart.symm ⟨z, hz⟩)) ∈ A.domain
        simpa using (A.chart.symm ⟨z, hz⟩).property⟩ :=
  rfl

theorem transport_chart_symm_val
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY)
    {z : ℂ × ℂ} {hz : z ∈ A.range} :
    ((A.transport e).chart.symm ⟨z, hz⟩).1 =
      e.symm ((A.chart.symm ⟨z, hz⟩).1) :=
  rfl

theorem transport_chart_val
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY)
    {x : X} {hx : x ∈ (A.transport e).domain} :
    ((A.transport e).chart ⟨x, hx⟩).1 =
      (A.chart ⟨e x, hx⟩).1 :=
  rfl

/-- The coordinate overlap on the source chart where the target chart is
defined.  The existential proof keeps the definition total while retaining
the actual inverse of the source chart on the overlap. -/
def overlap {X : Type u} {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology) : Set (ℂ × ℂ) :=
  {p | ∃ hp : p ∈ sourceChart.range,
    (sourceChart.chart.symm ⟨p, hp⟩).1 ∈ targetChart.domain}

noncomputable def overlapSourceRangeProof {X : Type u}
    {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    {p : ℂ × ℂ} (hp : p ∈ overlap sourceChart targetChart) :
    p ∈ sourceChart.range :=
  Classical.choose hp

theorem overlapSourceRangeProof_spec {X : Type u}
    {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    {p : ℂ × ℂ} (hp : p ∈ overlap sourceChart targetChart) :
    (sourceChart.chart.symm
      ⟨p, overlapSourceRangeProof sourceChart targetChart hp⟩).1 ∈
        targetChart.domain :=
  Classical.choose_spec hp

/-- The total transition map associated to two surface charts.  Its value
outside the actual overlap is deliberately set to the origin; all analytic
claims below are restricted to the overlap. -/
noncomputable def transitionMap {X : Type u}
    {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology) :
    (ℂ × ℂ) → (ℂ × ℂ) :=
  by
    classical
    exact fun p => if hp : p ∈ overlap sourceChart targetChart then
      (targetChart.chart
        ⟨(sourceChart.chart.symm
            ⟨p, overlapSourceRangeProof sourceChart targetChart hp⟩).1,
          overlapSourceRangeProof_spec sourceChart targetChart hp⟩).1
    else (0, 0)

theorem transitionMap_on_overlap {X : Type u}
    {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    {p : ℂ × ℂ} (hp : p ∈ overlap sourceChart targetChart) :
    transitionMap sourceChart targetChart p =
      (targetChart.chart
        ⟨(sourceChart.chart.symm
            ⟨p, overlapSourceRangeProof sourceChart targetChart hp⟩).1,
          overlapSourceRangeProof_spec sourceChart targetChart hp⟩).1 := by
  classical
  simp [transitionMap, hp]

/-! Restrict a surface chart to an open subspace of its source.  The source
    subtype is first rearranged into the corresponding open subset of the
    old chart domain; the old chart is then restricted by Homeomorph.image,
    and the open embedding of the old range converts the range-subtype image
    back into an open subset of ℂ × ℂ. -/

noncomputable def restrictOpenSubspace
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U) :
    @ComplexSurfaceChart U (TopologicalSpace.induced Subtype.val topology) := by
  let D : Set {x : X // x ∈ A.domain} :=
    (fun x : {x : X // x ∈ A.domain} => (x : X)) ⁻¹' U
  let q : {x : U // (x : X) ∈ A.domain} ≃ₜ D :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.property⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  have hD : IsOpen D := hU.preimage continuous_subtype_val
  have himage : IsOpen (A.chart '' D) := A.chart.isOpenMap D hD
  have hrange :
      IsOpen
        ((fun z : {z : ℂ × ℂ // z ∈ A.range} => (z : ℂ × ℂ)) ''
          (A.chart '' D)) :=
    (A.range_open.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen
      (s := A.chart '' D)).mp himage
  refine
    { domain := Subtype.val ⁻¹' A.domain
      range :=
        ((fun z : {z : ℂ × ℂ // z ∈ A.range} => (z : ℂ × ℂ)) ''
          (A.chart '' D))
      domain_open := A.domain_open.preimage continuous_subtype_val
      range_open := hrange
      chart := ?_ }
  exact
    q.trans (A.chart.image D) |>.trans
      (A.range_open.isOpenEmbedding_subtypeVal.isEmbedding.homeomorphImage
        (A.chart '' D))

@[simp] theorem restrictOpenSubspace_domain
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U) :
    (A.restrictOpenSubspace U hU).domain =
      Subtype.val ⁻¹' A.domain :=
  rfl

@[simp] theorem restrictOpenSubspace_range
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U) :
    (A.restrictOpenSubspace U hU).range =
      ((fun z : {z : ℂ × ℂ // z ∈ A.range} => (z : ℂ × ℂ)) ''
        (A.chart '' ((fun x : {x : X // x ∈ A.domain} => (x : X)) ⁻¹' U))) :=
  rfl

end ComplexSurfaceChart

/-- A covering family of two-complex-dimensional local charts. -/
structure ComplexSurfaceChartFamily (X : Type u) where
  topology : TopologicalSpace X
  index : Type u
  chart : index → ComplexSurfaceChart X topology
  coverSet : Set X
  covers : ∀ x, x ∈ coverSet → ∃ i, x ∈ (chart i).domain

namespace ComplexSurfaceChartFamily

theorem has_chart_at {X : Type u}
    (A : ComplexSurfaceChartFamily X) {x : X} (hx : x ∈ A.coverSet) :
    ∃ i, x ∈ (A.chart i).domain :=
  A.covers x hx

end ComplexSurfaceChartFamily

/-- A complex surface atlas on an explicitly specified covered region.  Keeping
the covered region as data is useful for local analytic families: the current
torus construction is an atlas on the parameter neighborhood slice, not yet
an atlas for the entire varying family. -/
structure ComplexSurfaceAtlas (X : Type u)
    extends ComplexSurfaceChartFamily X where
  transition_differentiableOn : ∀ i j,
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap (chart i) (chart j))
      (ComplexSurfaceChart.overlap (chart i) (chart j))

namespace ComplexSurfaceAtlas

theorem transport_overlap_iff
    {X : Type u} {Y : Type u}
    {A : ComplexSurfaceAtlas Y}
    {topologyX : TopologicalSpace X}
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology)
    (i j : A.index) {p : ℂ × ℂ} :
    p ∈ ComplexSurfaceChart.overlap
        ((A.chart i).transport e) ((A.chart j).transport e) ↔
      p ∈ ComplexSurfaceChart.overlap (A.chart i) (A.chart j) := by
  letI : TopologicalSpace Y := A.toComplexSurfaceChartFamily.topology
  constructor
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    change ((A.chart i).chart.symm ⟨p, hp⟩).1 ∈ (A.chart j).domain
    change e (((A.chart i).transport e).chart.symm ⟨p, hp⟩).1 ∈
      (A.chart j).domain at hx
    rw [ComplexSurfaceChart.transport_chart_symm_val] at hx
    simpa using hx
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    change e.symm ((A.chart i).chart.symm ⟨p, hp⟩).1 ∈
      e ⁻¹' (A.chart j).domain
    change (((A.chart i).transport e).chart.symm ⟨p, hp⟩).1 ∈
      e ⁻¹' (A.chart j).domain
    rw [ComplexSurfaceChart.transport_chart_symm_val]
    simpa using hx

theorem transport_transitionMap
    {X : Type u} {Y : Type u}
    {A : ComplexSurfaceAtlas Y}
    {topologyX : TopologicalSpace X}
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology)
    (i j : A.index) :
    ComplexSurfaceChart.transitionMap
        ((A.chart i).transport e) ((A.chart j).transport e) =
      ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j) := by
  letI : TopologicalSpace Y := A.toComplexSurfaceChartFamily.topology
  funext p
  classical
  by_cases hp : p ∈ ComplexSurfaceChart.overlap (A.chart i) (A.chart j)
  · rw [ComplexSurfaceChart.transitionMap_on_overlap
      ((A.chart i).transport e) ((A.chart j).transport e)
      ((transport_overlap_iff e i j).2 hp)]
    rw [ComplexSurfaceChart.transitionMap_on_overlap
      (A.chart i) (A.chart j) hp]
    have htransport := ComplexSurfaceChart.transport_chart_val
      (e := e) (A := A.chart j)
      (x := (((A.chart i).transport e).chart.symm
        ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
          ((A.chart i).transport e) ((A.chart j).transport e)
          ((transport_overlap_iff e i j).2 hp)⟩).1)
      (hx := ComplexSurfaceChart.overlapSourceRangeProof_spec
        ((A.chart i).transport e) ((A.chart j).transport e)
        ((transport_overlap_iff e i j).2 hp))
    simpa only [ComplexSurfaceChart.transport_chart_symm_val,
      Homeomorph.apply_symm_apply] using htransport
  · have htransport : p ∉ ComplexSurfaceChart.overlap
        ((A.chart i).transport e) ((A.chart j).transport e) :=
      fun h => hp ((transport_overlap_iff e i j).1 h)
    simp [ComplexSurfaceChart.transitionMap, hp, htransport]

/-! A whole atlas can now be transported along the same total-space
homeomorphism.  The cover is pulled back, while every chart keeps its model
range and conjugates its source coordinate by the homeomorphism. -/

noncomputable def transport
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology) :
    @ComplexSurfaceAtlas X where
  toComplexSurfaceChartFamily :=
    { topology := topologyX
      index := A.index
      chart := fun i => (A.chart i).transport e
      coverSet := e ⁻¹' A.coverSet
      covers := by
        intro x hx
        rcases A.covers (e x) hx with ⟨i, hi⟩
        exact ⟨i, hi⟩ }
  transition_differentiableOn := by
    intro i j
    -- The transported transition is the original transition after the
    -- source and target charts' inverse coordinates cancel the conjugation.
    change DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((A.chart i).transport e) ((A.chart j).transport e))
      (ComplexSurfaceChart.overlap
        ((A.chart i).transport e) ((A.chart j).transport e))
    rw [ComplexSurfaceAtlas.transport_transitionMap e i j]
    have hset : ComplexSurfaceChart.overlap
        ((A.chart i).transport e) ((A.chart j).transport e) =
        ComplexSurfaceChart.overlap (A.chart i) (A.chart j) := by
      ext p
      exact ComplexSurfaceAtlas.transport_overlap_iff e i j
    rw [hset]
    exact A.transition_differentiableOn i j

@[simp] theorem transport_coverSet
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology) :
    (transport A e).coverSet = e ⁻¹' A.coverSet :=
  rfl

theorem has_chart_at {X : Type u} (A : ComplexSurfaceAtlas X)
    {x : X} (hx : x ∈ A.coverSet) :
    ∃ i, x ∈ (A.chart i).domain :=
  A.covers x hx

theorem transition_is_differentiableOn {X : Type u}
    (A : ComplexSurfaceAtlas X) (i j : A.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j))
      (ComplexSurfaceChart.overlap (A.chart i) (A.chart j)) :=
  A.transition_differentiableOn i j

end ComplexSurfaceAtlas

/-- A surface atlas whose first model coordinate is a genuine base parameter.
This is the minimal total-space interface needed to distinguish a family of
complex surfaces from an isolated complex surface: the atlas records the
projection, its continuity, and the fact that every chart's first coordinate
is that projection. -/
structure ComplexSurfaceFamilyAtlas (X : Type u) (B : Type w)
    [TopologicalSpace B] extends ComplexSurfaceAtlas X where
  projection : X → B
  parameterCoordinate : B → ℂ
  projection_continuous :
    @Continuous X B toComplexSurfaceAtlas.topology inferInstance projection
  chart_base_coordinate : ∀ i {x : X} (hx : x ∈ (chart i).domain),
    ((chart i).chart ⟨x, hx⟩).1.1 = parameterCoordinate (projection x)

namespace ComplexSurfaceFamilyAtlas

theorem has_chart_at {X : Type u} {B : Type w}
    [TopologicalSpace B] (A : ComplexSurfaceFamilyAtlas X B)
    {x : X} (hx : x ∈ A.coverSet) :
    ∃ i, x ∈ (A.chart i).domain :=
  A.covers x hx

theorem transition_is_differentiableOn {X : Type u} {B : Type w}
    [TopologicalSpace B] (A : ComplexSurfaceFamilyAtlas X B)
    (i j : A.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j))
      (ComplexSurfaceChart.overlap (A.chart i) (A.chart j)) :=
  A.transition_differentiableOn i j

/-! ### Compatibility of the complex atlas with the family projection

The atlas definition records that the first coordinate of every chart is the
base coordinate of the same point.  The following theorem propagates that
identity through chart transitions.  It is the formal local statement that a
complex surface atlas is an atlas *over the base*, rather than merely an
unrelated atlas on the total space.
-/

theorem transition_first_coordinate_eq {X : Type u} {B : Type w}
    [TopologicalSpace B] (A : ComplexSurfaceFamilyAtlas X B)
    (i j : A.index) {p : ℂ × ℂ}
    (hp : p ∈ ComplexSurfaceChart.overlap (A.chart i) (A.chart j)) :
    (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j) p).1 =
      p.1 := by
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  let sourceChart := A.chart i
  let targetChart := A.chart j
  have hsource : p ∈ sourceChart.range :=
    ComplexSurfaceChart.overlapSourceRangeProof sourceChart targetChart hp
  let x : X :=
    (sourceChart.chart.symm ⟨p, hsource⟩).1
  have hx_source : x ∈ sourceChart.domain :=
    by
      change (sourceChart.chart.symm ⟨p, hsource⟩).1 ∈ sourceChart.domain
      exact (sourceChart.chart.symm ⟨p, hsource⟩).property
  have hx_target : x ∈ targetChart.domain :=
    by
      simpa [x] using ComplexSurfaceChart.overlapSourceRangeProof_spec
        sourceChart targetChart hp
  have hsource_chart :
      (sourceChart.chart ⟨x, hx_source⟩).1.1 = p.1 := by
    have happly := sourceChart.chart.apply_symm_apply
      (⟨p, hsource⟩ : {q : ℂ × ℂ // q ∈ sourceChart.range})
    simpa [x] using congrArg
      (fun q : {q : ℂ × ℂ // q ∈ sourceChart.range} => q.1.1) happly
  change (ComplexSurfaceChart.transitionMap sourceChart targetChart p).1 = p.1
  rw [ComplexSurfaceChart.transitionMap_on_overlap sourceChart targetChart hp]
  calc
    (targetChart.chart ⟨x, hx_target⟩).1.1 =
        A.parameterCoordinate (A.projection x) := by
      exact A.chart_base_coordinate j hx_target
    _ = (sourceChart.chart ⟨x, hx_source⟩).1.1 := by
      symm
      exact A.chart_base_coordinate i hx_source
    _ = p.1 := hsource_chart

end ComplexSurfaceFamilyAtlas

/-- One local holomorphic transition sheet between two surface charts.

The sheet formulation is useful before a global transition function has been
assembled: a chart overlap may have several connected components, and each
component can be represented by one holomorphic map. -/
structure ComplexSurfaceTransitionSheet where
  source : Set (ℂ × ℂ)
  target : Set (ℂ × ℂ)
  source_open : IsOpen source
  target_open : IsOpen target
  map : (ℂ × ℂ) → (ℂ × ℂ)
  maps_to : Set.MapsTo map source target
  differentiableOn : DifferentiableOn ℂ map source

/-! A transition sheet can now be tied to two actual surface charts.  The
coordinate map is still allowed to be defined on all of `ℂ × ℂ`, while the
compatibility field records that, on the source sheet, the two chart inverses
land at the same point of the underlying space. -/

structure ComplexSurfaceChartTransitionSheet {X : Type u}
    (topology : TopologicalSpace X)
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    extends ComplexSurfaceTransitionSheet where
  source_subset_range : source ⊆ sourceChart.range
  target_subset_range : target ⊆ targetChart.range
  compatible : ∀ {p : ℂ × ℂ} (hp : p ∈ source),
    (sourceChart.chart.symm ⟨p, source_subset_range hp⟩).1 =
      (targetChart.chart.symm
        ⟨map p, target_subset_range (maps_to hp)⟩).1

/-- A sheetwise transition cover of one surface-chart overlap by actual
chart-compatible holomorphic sheets. -/
structure ComplexSurfaceChartTransitionCover {X : Type u}
    (topology : TopologicalSpace X)
    (sourceChart targetChart : ComplexSurfaceChart X topology) where
  index : Type u
  sheet : index →
    ComplexSurfaceChartTransitionSheet topology sourceChart targetChart
  source_subset_overlap : ∀ i,
    (sheet i).source ⊆ ComplexSurfaceChart.overlap sourceChart targetChart
  covers : ComplexSurfaceChart.overlap sourceChart targetChart ⊆
    ⋃ i, (sheet i).source

theorem ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (S : ComplexSurfaceChartTransitionSheet topology sourceChart targetChart)
    (hsource_subset_overlap :
      S.source ⊆ ComplexSurfaceChart.overlap sourceChart targetChart)
    {p : ℂ × ℂ} (hp : p ∈ S.source) :
    ComplexSurfaceChart.transitionMap sourceChart targetChart p = S.map p := by
  classical
  have hpOverlap : p ∈ ComplexSurfaceChart.overlap sourceChart targetChart :=
    hsource_subset_overlap hp
  rw [ComplexSurfaceChart.transitionMap_on_overlap sourceChart targetChart hpOverlap]
  have hsourceRange :
      (⟨p, ComplexSurfaceChart.overlapSourceRangeProof
          sourceChart targetChart hpOverlap⟩ :
        {q : ℂ × ℂ // q ∈ sourceChart.range}) =
        (⟨p, S.source_subset_range hp⟩ :
          {q : ℂ × ℂ // q ∈ sourceChart.range}) := by
    apply Subtype.ext
    rfl
  have hsourceInv :
      sourceChart.chart.symm
          ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
            sourceChart targetChart hpOverlap⟩ =
        sourceChart.chart.symm ⟨p, S.source_subset_range hp⟩ := by
    exact congrArg sourceChart.chart.symm hsourceRange
  have hinv_val :
      (sourceChart.chart.symm
          ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
            sourceChart targetChart hpOverlap⟩).1 =
        (targetChart.chart.symm
          ⟨S.map p, S.target_subset_range (S.maps_to hp)⟩).1 := by
    calc
      (sourceChart.chart.symm
          ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
            sourceChart targetChart hpOverlap⟩).1 =
          (sourceChart.chart.symm ⟨p, S.source_subset_range hp⟩).1 :=
        congrArg Subtype.val hsourceInv
      _ = (targetChart.chart.symm
          ⟨S.map p, S.target_subset_range (S.maps_to hp)⟩).1 :=
        S.compatible hp
  have htargetPoint :
      (⟨(sourceChart.chart.symm
          ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
            sourceChart targetChart hpOverlap⟩).1,
        ComplexSurfaceChart.overlapSourceRangeProof_spec
          sourceChart targetChart hpOverlap⟩ :
        {x : X // x ∈ targetChart.domain}) =
        targetChart.chart.symm
          ⟨S.map p, S.target_subset_range (S.maps_to hp)⟩ := by
    apply Subtype.ext
    exact hinv_val
  rw [htargetPoint]
  simpa using congrArg Subtype.val
    (targetChart.chart.apply_symm_apply
      (⟨S.map p, S.target_subset_range (S.maps_to hp)⟩ :
        {q : ℂ × ℂ // q ∈ targetChart.range}))

/-! ### Sheetwise descent of holomorphic transitions

The quotient construction naturally produces several local sheets over one
chart overlap.  The following two theorems package the descent argument once
and for all: compatibility identifies each sheet map with the actual chart
transition, and an open sheet cover then glues the local differentiability
claims into a differentiability claim on the whole overlap. -/

theorem ComplexSurfaceChartTransitionCover.iUnion_source_eq_overlap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (C : ComplexSurfaceChartTransitionCover topology sourceChart targetChart) :
    (⋃ i, (C.sheet i).source) =
      ComplexSurfaceChart.overlap sourceChart targetChart := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hpi⟩
    exact C.source_subset_overlap i hpi
  · intro hp
    exact C.covers hp

theorem ComplexSurfaceChartTransitionCover.transition_differentiableOn
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    (C : ComplexSurfaceChartTransitionCover topology sourceChart targetChart)
    (source_open : ∀ i, IsOpen (C.sheet i).source) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap sourceChart targetChart)
      (ComplexSurfaceChart.overlap sourceChart targetChart) := by
  rw [← C.iUnion_source_eq_overlap]
  apply DifferentiableOn.iUnion_of_isOpen
  · intro i
    apply (C.sheet i).differentiableOn.congr
    intro p hp
    exact ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
      (C.sheet i) (C.source_subset_overlap i) hp
  · intro i
    exact source_open i

namespace ComplexSurfaceTransitionSheet

theorem map_mem_target (S : ComplexSurfaceTransitionSheet)
    {p : ℂ × ℂ} (hp : p ∈ S.source) : S.map p ∈ S.target :=
  S.maps_to hp

end ComplexSurfaceTransitionSheet

/-- A covering complex atlas whose transitions are holomorphic on overlaps. -/
structure ComplexAtlas (X : Type u) [TopologicalSpace X] where
  index : Type u
  chart : index → ComplexChart X
  covers : ∀ x, ∃ i, x ∈ (chart i).domain
  transition_holomorphic : ∀ i j,
    DifferentiableOn ℂ
      (ComplexChart.transitionMap (chart i) (chart j))
      (ComplexChart.overlap (chart i) (chart j))

namespace ComplexAtlas

theorem has_chart_at {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (x : X) :
    ∃ i, x ∈ (A.chart i).domain :=
  A.covers x

theorem transition_is_differentiableOn {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) :
    DifferentiableOn ℂ
      (ComplexChart.transitionMap (A.chart i) (A.chart j))
      (ComplexChart.overlap (A.chart i) (A.chart j)) :=
  A.transition_holomorphic i j

/-! ### Chartwise maps between two concrete atlases -/

/-- The coordinate expression of a map in a source and a target chart. -/
def chartMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y)
    (i : A.index) (j : B.index) : ℂ → ℂ :=
  fun z => (B.chart j).toComplex (f ((A.chart i).fromComplex z))

/-- The part of the source coordinate plane on which the target chart applies. -/
def chartMapDomain {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y)
    (i : A.index) (j : B.index) : Set ℂ :=
  (A.chart i).range ∩ (A.chart i).fromComplex ⁻¹' (f ⁻¹' (B.chart j).domain)

theorem chartMap_agrees {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y)
    (i : A.index) (j : B.index) (z : ℂ) :
    chartMap A B f i j z =
      (B.chart j).toComplex (f ((A.chart i).fromComplex z)) :=
  rfl

theorem chartMapDomain_mem_source_range
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y)
    (i : A.index) (j : B.index) {z : ℂ}
    (hz : z ∈ chartMapDomain A B f i j) :
    z ∈ (A.chart i).range :=
  hz.1

end ComplexAtlas

/-- A map is holomorphic when every chart expression is Mathlib-differentiable
on the region where both charts are defined. -/
structure ChartwiseHolomorphicMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y) : Prop where
  differentiable_on_charts : ∀ i j,
    DifferentiableOn ℂ
      (ComplexAtlas.chartMap A B f i j)
      (ComplexAtlas.chartMapDomain A B f i j)

/-- A homeomorphism is biholomorphic at the atlas level when both directions
are chartwise holomorphic. -/
structure AtlasHolomorphicEquiv {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y)
    (e : @Homeomorph X Y inferInstance inferInstance) : Prop where
  forward : ChartwiseHolomorphicMap A B e
  inverse : ChartwiseHolomorphicMap B A e.symm

namespace AtlasHolomorphicEquiv

/-- Reverse a chartwise biholomorphic equivalence. -/
def symm {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {A : ComplexAtlas X} {B : ComplexAtlas Y}
    {e : @Homeomorph X Y inferInstance inferInstance}
    (h : AtlasHolomorphicEquiv A B e) :
    AtlasHolomorphicEquiv B A e.symm where
  forward := h.inverse
  inverse := h.forward

/-- The identity homeomorphism is biholomorphic for every compatible atlas:
its chart expressions are precisely the atlas transition maps. -/
def refl {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) :
    AtlasHolomorphicEquiv A A (@Homeomorph.refl X inferInstance) where
  forward := by
    refine ⟨?_⟩
    intro i j
    have hfun :
        ComplexAtlas.chartMap A A (@Homeomorph.refl X inferInstance) i j =
          ComplexChart.transitionMap (A.chart i) (A.chart j) := by
      funext z
      rfl
    rw [hfun]
    exact A.transition_holomorphic i j
  inverse := by
    refine ⟨?_⟩
    intro i j
    have hfun :
        ComplexAtlas.chartMap A A
          (@Homeomorph.refl X inferInstance).symm i j =
          ComplexChart.transitionMap (A.chart i) (A.chart j) := by
      funext z
      rfl
    rw [hfun]
    exact A.transition_holomorphic i j

end AtlasHolomorphicEquiv

/-- A Riemann-surface-shaped object with an actual complex atlas. -/
structure ComplexRiemannSurface (X : Type u) [TopologicalSpace X] where
  atlas : ComplexAtlas X

/-- A complex surface marked by a fixed topological reference surface. -/
structure MarkedComplexRiemannSurface (S : Type u) [TopologicalSpace S] where
  carrier : Type u
  topology : TopologicalSpace carrier
  surface : @ComplexRiemannSurface carrier topology
  marking : @Homeomorph S carrier inferInstance topology

namespace ComplexRiemannSurface

/-- Forget the atlas while retaining the concrete Mathlib topological object. -/
def toMarkedTopological {S : Type u} [TopologicalSpace S]
    (X : MarkedComplexRiemannSurface S) :
    MathlibFormal.MarkedTopologicalObject S where
  carrier := X.carrier
  topology := X.topology
  marking := X.marking

end ComplexRiemannSurface

/-! A small sanity-check model: the complex plane with its one global chart. -/

def complexPlaneChart : ComplexChart ℂ where
  domain := Set.univ
  range := Set.univ
  domain_open := isOpen_univ
  range_open := isOpen_univ
  toComplex := id
  fromComplex := id
  maps_into := by
    intro x _
    trivial
  inverse_into := by
    intro z _
    trivial
  left_inv := by
    intro x _
    rfl
  right_inv := by
    intro z _
    rfl
  continuous_toComplex := continuous_id.continuousOn
  continuous_fromComplex := continuous_id.continuousOn

def complexPlaneAtlas : ComplexAtlas ℂ where
  index := PUnit
  chart := fun _ => complexPlaneChart
  covers := by
    intro x
    exact ⟨PUnit.unit, Set.mem_univ x⟩
  transition_holomorphic := by
    intro i j
    have hfun :
        ComplexChart.transitionMap complexPlaneChart complexPlaneChart = id := by
      funext z
      rfl
    have hset :
        ComplexChart.overlap complexPlaneChart complexPlaneChart =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexChart.overlap, complexPlaneChart]
    rw [hfun, hset]
    exact differentiableOn_id

noncomputable def complexPlane : ComplexRiemannSurface ℂ where
  atlas := complexPlaneAtlas

/-- The complex plane with its identity marking.  This is the smallest concrete
model used below for an actual (constant) marked family. -/
noncomputable abbrev complexPlaneMarkedSurface : MarkedComplexRiemannSurface ℂ where
  carrier := ℂ
  topology := inferInstance
  surface := complexPlane
  marking := @Homeomorph.refl ℂ inferInstance

/-! ### A parameter-dependent coordinate model -/

/-- A global coordinate on the plane translated by the parameter `a`. -/
def affinePlaneChart (a : ℂ) : ComplexChart ℂ where
  domain := Set.univ
  range := Set.univ
  domain_open := isOpen_univ
  range_open := isOpen_univ
  toComplex := fun z => z - a
  fromComplex := fun z => z + a
  maps_into := by
    intro z _
    trivial
  inverse_into := by
    intro z _
    trivial
  left_inv := by
    intro z _
    dsimp
    ring
  right_inv := by
    intro z _
    dsimp
    ring
  continuous_toComplex := (continuous_id.sub continuous_const).continuousOn
  continuous_fromComplex := (continuous_id.add continuous_const).continuousOn

/-- The one-chart atlas for the translated coordinate. -/
def affinePlaneAtlas (a : ℂ) : ComplexAtlas ℂ where
  index := PUnit
  chart := fun _ => affinePlaneChart a
  covers := by
    intro z
    exact ⟨PUnit.unit, Set.mem_univ z⟩
  transition_holomorphic := by
    intro i j
    cases i
    cases j
    have hfun :
        ComplexChart.transitionMap (affinePlaneChart a) (affinePlaneChart a) = id := by
      funext z
      simp [ComplexChart.transitionMap, affinePlaneChart]
    have hset :
        ComplexChart.overlap (affinePlaneChart a) (affinePlaneChart a) =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexChart.overlap, affinePlaneChart]
    rw [hfun, hset]
    exact differentiableOn_id

/-- A marked plane whose chosen global chart depends on `a`. -/
noncomputable abbrev affinePlaneMarkedSurface (a : ℂ) :
    MarkedComplexRiemannSurface ℂ where
  carrier := ℂ
  topology := inferInstance
  surface := { atlas := affinePlaneAtlas a }
  marking := @Homeomorph.refl ℂ inferInstance

/-- The identity between the standard and translated coordinates is
chartwise biholomorphic. -/
theorem affinePlaneIdentityHolomorphic (a : ℂ) :
    @AtlasHolomorphicEquiv ℂ ℂ inferInstance inferInstance
      complexPlaneAtlas (affinePlaneAtlas a) (@Homeomorph.refl ℂ inferInstance) := by
  refine { forward := ?_, inverse := ?_ }
  · refine ⟨?_⟩
    intro i j
    cases i
    cases j
    have hfun :
        ComplexAtlas.chartMap complexPlaneAtlas (affinePlaneAtlas a)
          (@Homeomorph.refl ℂ inferInstance) PUnit.unit PUnit.unit =
          (fun z : ℂ => z - a) := by
      funext z
      rfl
    have hset :
        ComplexAtlas.chartMapDomain complexPlaneAtlas (affinePlaneAtlas a)
          (@Homeomorph.refl ℂ inferInstance) PUnit.unit PUnit.unit =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexAtlas.chartMapDomain, complexPlaneAtlas, complexPlaneChart,
        affinePlaneAtlas, affinePlaneChart]
    rw [hfun, hset]
    exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
  · refine ⟨?_⟩
    intro i j
    cases i
    cases j
    have hfun :
        ComplexAtlas.chartMap (affinePlaneAtlas a) complexPlaneAtlas
          (@Homeomorph.refl ℂ inferInstance).symm PUnit.unit PUnit.unit =
          (fun z : ℂ => z + a) := by
      funext z
      rfl
    have hset :
        ComplexAtlas.chartMapDomain (affinePlaneAtlas a) complexPlaneAtlas
          (@Homeomorph.refl ℂ inferInstance).symm PUnit.unit PUnit.unit =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexAtlas.chartMapDomain, complexPlaneAtlas, complexPlaneChart,
        affinePlaneAtlas, affinePlaneChart]
    rw [hfun, hset]
    exact DifferentiableOn.add differentiableOn_id (differentiableOn_const _)

theorem affinePlaneChart_toComplex_eq_standard_iff (a : ℂ) :
    (affinePlaneChart a).toComplex = complexPlaneChart.toComplex ↔ a = 0 := by
  constructor
  · intro h
    have hzero : (0 : ℂ) - a = 0 := by
      simpa [affinePlaneChart, complexPlaneChart] using congrFun h 0
    exact (sub_eq_zero.mp hzero).symm
  · intro ha
    subst ha
    funext z
    simp [affinePlaneChart, complexPlaneChart]

theorem complexPlane_transition_holomorphic :
    DifferentiableOn ℂ
      (ComplexChart.transitionMap complexPlaneChart complexPlaneChart)
      (ComplexChart.overlap complexPlaneChart complexPlaneChart) :=
  complexPlaneAtlas.transition_holomorphic PUnit.unit PUnit.unit

theorem complexPlane_chartwise_id :
    ChartwiseHolomorphicMap complexPlaneAtlas complexPlaneAtlas id := by
  refine ⟨?_⟩
  intro i j
  cases i
  cases j
  have hfun :
      ComplexAtlas.chartMap complexPlaneAtlas complexPlaneAtlas id
        PUnit.unit PUnit.unit = id := by
    funext z
    rfl
  have hset :
      ComplexAtlas.chartMapDomain complexPlaneAtlas complexPlaneAtlas id
        PUnit.unit PUnit.unit = (Set.univ : Set ℂ) := by
    ext z
    simp [ComplexAtlas.chartMapDomain, complexPlaneAtlas, complexPlaneChart]
  rw [hfun, hset]
  exact differentiableOn_id

end MathlibFormal
end Teichmuller
