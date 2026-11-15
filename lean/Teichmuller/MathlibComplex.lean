import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.LocallyConstant.Basic
import Teichmuller.MathlibTopology

namespace Teichmuller
namespace MathlibFormal

open scoped Topology

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

universe u w v

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
    {X : Type v} {Y : Type u}
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

@[simp] theorem transport_range
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY) :
    (A.transport e).range = A.range :=
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

theorem transport_chart_symm_val_univ
    {X : Type v} {Y : Type u}
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

theorem transport_chart_val_univ
    {X : Type v} {Y : Type u}
    {topologyX : TopologicalSpace X} {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY)
    {x : X} {hx : x ∈ (A.transport e).domain} :
    ((A.transport e).chart ⟨x, hx⟩).1 =
      (A.chart ⟨e x, hx⟩).1 :=
  rfl

/-! Transport is associative at the chart level.  This is the local analytic
    counterpart of composing the total-space comparison homeomorphisms: the
    doubly transported chart and the chart transported along the composite
    have the same domain, range, and coordinate map. -/

theorem transport_trans
    {X : Type u} {Y : Type v} {Z : Type w}
    {topologyX : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    {topologyZ : TopologicalSpace Z}
    (e : @Homeomorph X Y topologyX topologyY)
    (f : @Homeomorph Y Z topologyY topologyZ)
    (A : ComplexSurfaceChart Z topologyZ) :
    (A.transport f).transport e = A.transport (e.trans f) := by
  rfl

/-! Transporting a chart to the other side of a homeomorphism and then back
    does not change its underlying chart.  These cancellation lemmas are the
    small geometric facts needed when a total-space transition is checked in
    both directions. -/

theorem transport_symm_trans
    {X : Type u} {Y : Type v}
    {topologyX : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart Y topologyY) :
    (A.transport e).transport e.symm = A := by
  rw [transport_trans]
  have he : e.symm.trans e =
      @Homeomorph.refl Y topologyY := by
    ext y
    simp
  rw [he]
  rfl

theorem transport_trans_symm
    {X : Type u} {Y : Type v}
    {topologyX : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    (e : @Homeomorph X Y topologyX topologyY)
    (A : ComplexSurfaceChart X topologyX) :
    (A.transport e.symm).transport e = A := by
  rw [transport_trans]
  have he : e.trans e.symm =
      @Homeomorph.refl X topologyX := by
    ext x
    simp
  rw [he]
  rfl

theorem ext
    {X : Type u} {topology : TopologicalSpace X}
    {A B : ComplexSurfaceChart X topology}
    (h_domain : A.domain = B.domain)
    (h_range : A.range = B.range)
    (h_chart : HEq A.chart B.chart) :
    A = B := by
  cases A
  cases B
  cases h_domain
  cases h_range
  cases h_chart
  rfl

/-! A dependent extensionality helper for chart homeomorphisms.  The source
    and range subtypes may be presented with propositionally equal carrier
    sets, so ordinary equality is not available until those equalities are
    eliminated.  The pointwise hypothesis is stated on underlying values,
    which keeps the lemma usable before the subtype proofs are aligned. -/

theorem homeomorph_heq_of_pointwise
    {X Y : Type*} (topologyX : TopologicalSpace X)
    (topologyY : TopologicalSpace Y)
    {D E : Set X} {R T : Set Y}
    (e : @Homeomorph {x // x ∈ D} {y // y ∈ R}
      (TopologicalSpace.induced Subtype.val topologyX)
      (TopologicalSpace.induced Subtype.val topologyY))
    (f : @Homeomorph {x // x ∈ E} {y // y ∈ T}
      (TopologicalSpace.induced Subtype.val topologyX)
      (TopologicalSpace.induced Subtype.val topologyY))
    (hD : D = E) (hR : R = T)
    (hpoint : ∀ x : {x // x ∈ D},
      (e x).1 = (f ⟨x.1, hD ▸ x.property⟩).1) :
    HEq e f := by
  cases hD
  cases hR
  apply heq_of_eq
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  exact hpoint x

theorem transport_refl
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology) :
    A.transport (@Homeomorph.refl X topology) = A := by
  apply ComplexSurfaceChart.ext
  · ext x
    simp
  · rfl
  · apply homeomorph_heq_of_pointwise topology
      (inferInstance : TopologicalSpace (ℂ × ℂ))
      (D := (@Homeomorph.refl X topology) ⁻¹' A.domain)
      (E := A.domain) (R := A.range) (T := A.range)
      (A.transport (@Homeomorph.refl X topology)).chart A.chart
      (by
        ext x
        simp)
      rfl
    intro x
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

theorem overlap_open {X : Type u} {topology : TopologicalSpace X}
    (sourceChart targetChart : ComplexSurfaceChart X topology) :
    IsOpen (overlap sourceChart targetChart) := by
  let V : Set {x // x ∈ sourceChart.domain} :=
    (fun x : {x // x ∈ sourceChart.domain} => (x : X)) ⁻¹'
      targetChart.domain
  have hV : IsOpen V :=
    targetChart.domain_open.preimage continuous_subtype_val
  have hchartV : IsOpen (sourceChart.chart '' V) :=
    sourceChart.chart.isOpenMap _ hV
  have himage : IsOpen
      ((fun z : {z // z ∈ sourceChart.range} => (z : ℂ × ℂ)) ''
        (sourceChart.chart '' V)) :=
    sourceChart.range_open.isOpenMap_subtype_val _ hchartV
  rw [show overlap sourceChart targetChart =
      (fun z : {z // z ∈ sourceChart.range} => (z : ℂ × ℂ)) ''
        (sourceChart.chart '' V) by
    ext p
    constructor
    · intro hp
      let hp' : p ∈ sourceChart.range :=
        overlapSourceRangeProof sourceChart targetChart hp
      let x := sourceChart.chart.symm ⟨p, hp'⟩
      refine ⟨sourceChart.chart x, ?_, ?_⟩
      · refine ⟨x, ?_, rfl⟩
        exact overlapSourceRangeProof_spec sourceChart targetChart hp
      · exact congrArg Subtype.val
          (sourceChart.chart.apply_symm_apply ⟨p, hp'⟩)
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(sourceChart.chart x).property, ?_⟩
      change (x : X) ∈ targetChart.domain at hx
      have hpoint :
          (sourceChart.chart.symm
            ⟨(sourceChart.chart x).1, (sourceChart.chart x).property⟩).1 =
            (x : X) := by
        exact congrArg Subtype.val (sourceChart.chart.symm_apply_apply x)
      convert hx using 1]
  exact himage

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

/-! The ordinary chart cocycle is already forced by the inverse laws.  The
statement is deliberately phrased with only the two successive overlap
hypotheses: the first overlap identifies the common point in the middle
chart, and the second overlap supplies the target-chart domain. -/

theorem transitionMap_comp_on_overlap
    {X : Type u} {topology : TopologicalSpace X}
    (sourceChart middleChart targetChart : ComplexSurfaceChart X topology)
    {p : ℂ × ℂ}
    (hp₁₂ : p ∈ overlap sourceChart middleChart)
    (hp₂₃ :
      transitionMap sourceChart middleChart p ∈
        overlap middleChart targetChart) :
    transitionMap sourceChart targetChart p =
      transitionMap middleChart targetChart
        (transitionMap sourceChart middleChart p) := by
  classical
  let x :=
    (sourceChart.chart.symm
      ⟨p, overlapSourceRangeProof sourceChart middleChart hp₁₂⟩).1
  have hx₂ : x ∈ middleChart.domain := by
    exact overlapSourceRangeProof_spec sourceChart middleChart hp₁₂
  have h₁₂ :
      transitionMap sourceChart middleChart p =
        (middleChart.chart ⟨x, hx₂⟩).1 := by
    rw [transitionMap_on_overlap sourceChart middleChart hp₁₂]
  have hx₃ : x ∈ targetChart.domain := by
    have h₂₃ :=
      overlapSourceRangeProof_spec middleChart targetChart hp₂₃
    have hmiddle :
        (middleChart.chart.symm
          ⟨transitionMap sourceChart middleChart p,
            overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 = x := by
      have hsub :
          (⟨transitionMap sourceChart middleChart p,
              overlapSourceRangeProof middleChart targetChart hp₂₃⟩ :
            {q : ℂ × ℂ // q ∈ middleChart.range}) =
          middleChart.chart ⟨x, hx₂⟩ := by
        apply Subtype.ext
        exact h₁₂
      calc
        (middleChart.chart.symm
            ⟨transitionMap sourceChart middleChart p,
              overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 =
            (middleChart.chart.symm (middleChart.chart ⟨x, hx₂⟩)).1 := by
              exact congrArg Subtype.val
                (congrArg middleChart.chart.symm hsub)
        _ = x := by
          exact congrArg Subtype.val
            (middleChart.chart.symm_apply_apply ⟨x, hx₂⟩)
    rw [hmiddle] at h₂₃
    exact h₂₃
  have hp₁₃ : p ∈ overlap sourceChart targetChart := by
    refine ⟨overlapSourceRangeProof sourceChart middleChart hp₁₂, ?_⟩
    have hsource :
        (sourceChart.chart.symm
          ⟨p, overlapSourceRangeProof sourceChart targetChart
            (show p ∈ overlap sourceChart targetChart from
              ⟨overlapSourceRangeProof sourceChart middleChart hp₁₂, by
                exact hx₃⟩)⟩).1 = x := by
      apply congrArg Subtype.val
      apply congrArg sourceChart.chart.symm
      apply Subtype.ext
      rfl
    exact hsource ▸ hx₃
  rw [transitionMap_on_overlap sourceChart targetChart hp₁₃]
  rw [transitionMap_on_overlap middleChart targetChart hp₂₃]
  apply congrArg Subtype.val
  apply congrArg targetChart.chart
  apply Subtype.ext
  have hsource :
      (sourceChart.chart.symm
        ⟨p, overlapSourceRangeProof sourceChart targetChart hp₁₃⟩).1 = x := by
    apply congrArg Subtype.val
    apply congrArg sourceChart.chart.symm
    apply Subtype.ext
    rfl
  have hmiddle :
      (middleChart.chart.symm
        ⟨transitionMap sourceChart middleChart p,
          overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 = x := by
    have hsub :
        (⟨transitionMap sourceChart middleChart p,
            overlapSourceRangeProof middleChart targetChart hp₂₃⟩ :
          {q : ℂ × ℂ // q ∈ middleChart.range}) =
        middleChart.chart ⟨x, hx₂⟩ := by
      apply Subtype.ext
      exact h₁₂
    calc
      (middleChart.chart.symm
          ⟨transitionMap sourceChart middleChart p,
            overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 =
          (middleChart.chart.symm (middleChart.chart ⟨x, hx₂⟩)).1 := by
            exact congrArg Subtype.val
              (congrArg middleChart.chart.symm hsub)
      _ = x := by
        exact congrArg Subtype.val
          (middleChart.chart.symm_apply_apply ⟨x, hx₂⟩)
  exact hsource.trans hmiddle.symm

theorem overlap_mem_of_transitionMap_mem
    {X : Type u} {topology : TopologicalSpace X}
    (sourceChart middleChart targetChart : ComplexSurfaceChart X topology)
    {p : ℂ × ℂ}
    (hp₁₂ : p ∈ overlap sourceChart middleChart)
    (hp₂₃ :
      transitionMap sourceChart middleChart p ∈
        overlap middleChart targetChart) :
    p ∈ overlap sourceChart targetChart := by
  classical
  let x :=
    (sourceChart.chart.symm
      ⟨p, overlapSourceRangeProof sourceChart middleChart hp₁₂⟩).1
  have hx₂ : x ∈ middleChart.domain := by
    exact overlapSourceRangeProof_spec sourceChart middleChart hp₁₂
  have h₁₂ :
      transitionMap sourceChart middleChart p =
        (middleChart.chart ⟨x, hx₂⟩).1 := by
    rw [transitionMap_on_overlap sourceChart middleChart hp₁₂]
  have hx₃ : x ∈ targetChart.domain := by
    have h₂₃ :=
      overlapSourceRangeProof_spec middleChart targetChart hp₂₃
    have hmiddle :
        (middleChart.chart.symm
          ⟨transitionMap sourceChart middleChart p,
            overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 = x := by
      have hsub :
          (⟨transitionMap sourceChart middleChart p,
              overlapSourceRangeProof middleChart targetChart hp₂₃⟩ :
            {q : ℂ × ℂ // q ∈ middleChart.range}) =
          middleChart.chart ⟨x, hx₂⟩ := by
        apply Subtype.ext
        exact h₁₂
      calc
        (middleChart.chart.symm
            ⟨transitionMap sourceChart middleChart p,
              overlapSourceRangeProof middleChart targetChart hp₂₃⟩).1 =
            (middleChart.chart.symm (middleChart.chart ⟨x, hx₂⟩)).1 := by
              exact congrArg Subtype.val
                (congrArg middleChart.chart.symm hsub)
        _ = x := by
          exact congrArg Subtype.val
            (middleChart.chart.symm_apply_apply ⟨x, hx₂⟩)
    rw [hmiddle] at h₂₃
    exact h₂₃
  refine ⟨overlapSourceRangeProof sourceChart middleChart hp₁₂, ?_⟩
  have hsource :
      (sourceChart.chart.symm
        ⟨p, overlapSourceRangeProof sourceChart middleChart hp₁₂⟩).1 = x := by
    apply congrArg Subtype.val
    apply congrArg sourceChart.chart.symm
    apply Subtype.ext
    rfl
  exact hsource ▸ hx₃

theorem transitionMap_self_differentiableOn {X : Type u}
    {topology : TopologicalSpace X}
    (chart : ComplexSurfaceChart X topology) :
    DifferentiableOn ℂ
      (transitionMap chart chart)
      (overlap chart chart) := by
  apply differentiableOn_id.congr
  intro p hp
  rw [transitionMap_on_overlap chart chart hp]
  exact congrArg (fun z : {z // z ∈ chart.range} => z.1)
    (chart.chart.apply_symm_apply
      ⟨p, overlapSourceRangeProof chart chart hp⟩)

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

theorem restrictOpenSubspace_range_subset
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U) :
    (A.restrictOpenSubspace U hU).range ⊆ A.range := by
  intro z hz
  rw [A.restrictOpenSubspace_range] at hz
  rcases hz with ⟨w, _, rfl⟩
  exact w.property

@[simp] theorem restrictOpenSubspace_chart_apply
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U)
    {x : U} (hx : x ∈ (A.restrictOpenSubspace U hU).domain) :
    ((A.restrictOpenSubspace U hU).chart ⟨x, hx⟩).1 =
      (A.chart ⟨(x : X), by simpa using hx⟩).1 := by
  rfl

theorem restrictOpenSubspace_chart_symm_val
    {X : Type u} {topology : TopologicalSpace X}
    (A : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U)
    {z : ℂ × ℂ} (hz : z ∈ (A.restrictOpenSubspace U hU).range) :
    ((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1.1 =
      (A.chart.symm
        ⟨z, A.restrictOpenSubspace_range_subset U hU hz⟩).1 := by
  let hA :
      ((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1.1 ∈ A.domain := by
    change ((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1 ∈
      (A.restrictOpenSubspace U hU).domain
    exact ((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).property
  let hzA : z ∈ A.range := A.restrictOpenSubspace_range_subset U hU hz
  have hchart :
      A.chart ⟨((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1.1, hA⟩ =
        ⟨z, hzA⟩ := by
    apply Subtype.ext
    have h := (A.restrictOpenSubspace U hU).chart.apply_symm_apply
      (⟨z, hz⟩ : {q : ℂ × ℂ // q ∈ (A.restrictOpenSubspace U hU).range})
    change ((A.restrictOpenSubspace U hU).chart
      ((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩)).1 = z
    exact congrArg Subtype.val h
  have hsource :
      (⟨((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1.1, hA⟩ :
        {x : X // x ∈ A.domain}) =
        A.chart.symm ⟨z, hzA⟩ := by
    apply A.chart.injective
    calc
      A.chart ⟨((A.restrictOpenSubspace U hU).chart.symm ⟨z, hz⟩).1.1, hA⟩ =
          ⟨z, hzA⟩ := hchart
      _ = A.chart (A.chart.symm ⟨z, hzA⟩) :=
        (A.chart.apply_symm_apply ⟨z, hzA⟩).symm
  exact congrArg Subtype.val hsource

theorem restrictOpenSubspace_overlap_subset
    {X : Type u} {topology : TopologicalSpace X}
    (A B : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U)
    {p : ℂ × ℂ}
    (hp : p ∈ overlap (A.restrictOpenSubspace U hU)
      (B.restrictOpenSubspace U hU)) :
    p ∈ overlap A B := by
  rcases hp with ⟨hpRange, hpTarget⟩
  refine ⟨A.restrictOpenSubspace_range_subset U hU hpRange, ?_⟩
  change ((A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩).1.1 ∈
    B.domain at hpTarget
  rw [← A.restrictOpenSubspace_chart_symm_val U hU hpRange]
  exact hpTarget

theorem restrictOpenSubspace_transitionMap_on_overlap
    {X : Type u} {topology : TopologicalSpace X}
    (A B : ComplexSurfaceChart X topology)
    (U : Set X) (hU : IsOpen U)
    {p : ℂ × ℂ}
    (hp : p ∈ overlap (A.restrictOpenSubspace U hU)
      (B.restrictOpenSubspace U hU)) :
    transitionMap (A.restrictOpenSubspace U hU)
      (B.restrictOpenSubspace U hU) p = transitionMap A B p := by
  have hpAB := restrictOpenSubspace_overlap_subset A B U hU hp
  rw [transitionMap_on_overlap
    (A.restrictOpenSubspace U hU) (B.restrictOpenSubspace U hU) hp]
  rw [transitionMap_on_overlap A B hpAB]
  rcases hp with ⟨hpRange, hpTarget⟩
  have htarget := B.restrictOpenSubspace_chart_apply U hU
    (x := (A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩)
    (hx := hpTarget)
  let hB0 :
      ((A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩).1.1 ∈ B.domain := by
    change ((A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩).1 ∈
      (B.restrictOpenSubspace U hU).domain at hpTarget
    exact hpTarget
  let hB1 := overlapSourceRangeProof_spec A B hpAB
  have hBsource :
      (⟨((A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩).1.1, hB0⟩ :
        {x : X // x ∈ B.domain}) =
        ⟨(A.chart.symm
          ⟨p, A.restrictOpenSubspace_range_subset U hU hpRange⟩).1, hB1⟩ := by
    apply Subtype.ext
    exact A.restrictOpenSubspace_chart_symm_val U hU hpRange
  calc
    ((B.restrictOpenSubspace U hU).chart
      ⟨(A.restrictOpenSubspace U hU).chart.symm ⟨p, hpRange⟩, hpTarget⟩).1 =
        (B.chart ⟨((A.restrictOpenSubspace U hU).chart.symm
          ⟨p, hpRange⟩).1.1, hB0⟩).1 := by
      exact htarget
    _ = (B.chart ⟨(A.chart.symm
          ⟨p, A.restrictOpenSubspace_range_subset U hU hpRange⟩).1, hB1⟩).1 := by
      exact congrArg Subtype.val (congrArg B.chart hBsource)

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

theorem transport_overlap_iff_univ
    {X : Type v} {Y : Type u}
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
    rw [ComplexSurfaceChart.transport_chart_symm_val_univ] at hx
    simpa using hx
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    change e.symm ((A.chart i).chart.symm ⟨p, hp⟩).1 ∈
      e ⁻¹' (A.chart j).domain
    change (((A.chart i).transport e).chart.symm ⟨p, hp⟩).1 ∈
      e ⁻¹' (A.chart j).domain
    rw [ComplexSurfaceChart.transport_chart_symm_val_univ]
    simpa using hx

theorem transport_transitionMap_univ
    {X : Type v} {Y : Type u}
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
      ((transport_overlap_iff_univ e i j).2 hp)]
    rw [ComplexSurfaceChart.transitionMap_on_overlap
      (A.chart i) (A.chart j) hp]
    have htransport := ComplexSurfaceChart.transport_chart_val_univ
      (e := e) (A := A.chart j)
      (x := (((A.chart i).transport e).chart.symm
        ⟨p, ComplexSurfaceChart.overlapSourceRangeProof
          ((A.chart i).transport e) ((A.chart j).transport e)
          ((transport_overlap_iff_univ e i j).2 hp)⟩).1)
      (hx := ComplexSurfaceChart.overlapSourceRangeProof_spec
        ((A.chart i).transport e) ((A.chart j).transport e)
        ((transport_overlap_iff_univ e i j).2 hp))
    simpa only [ComplexSurfaceChart.transport_chart_symm_val_univ,
      Homeomorph.apply_symm_apply] using htransport
  · have htransport : p ∉ ComplexSurfaceChart.overlap
        ((A.chart i).transport e) ((A.chart j).transport e) :=
      fun h => hp ((transport_overlap_iff_univ e i j).1 h)
    simp [ComplexSurfaceChart.transitionMap, hp, htransport]

/-! The preceding chart lemmas also allow an atlas to be transported when the
target carrier lives in a larger universe.  This is the form needed for a
dependent-sum total space: if the source carrier is in `Type u` and the
parameter is in `Type v`, then the dependent sum is in `Type (max u v)`.
The `ULift` on the index is bookkeeping only; it does not change any chart
or transition map. -/

noncomputable def transport_univ
    {X : Type (max u v)} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology) :
    @ComplexSurfaceAtlas X where
  toComplexSurfaceChartFamily :=
    { topology := topologyX
      index := ULift.{v} A.index
      chart := fun i => (A.chart i.down).transport e
      coverSet := e ⁻¹' A.coverSet
      covers := by
        intro x hx
        rcases A.covers (e x) hx with ⟨i, hi⟩
        exact ⟨ULift.up i, hi⟩ }
  transition_differentiableOn := by
    intro i j
    change DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((A.chart i.down).transport e) ((A.chart j.down).transport e))
      (ComplexSurfaceChart.overlap
        ((A.chart i.down).transport e) ((A.chart j.down).transport e))
    rw [ComplexSurfaceAtlas.transport_transitionMap_univ e i.down j.down]
    have hset : ComplexSurfaceChart.overlap
        ((A.chart i.down).transport e) ((A.chart j.down).transport e) =
        ComplexSurfaceChart.overlap (A.chart i.down) (A.chart j.down) := by
      ext p
      exact ComplexSurfaceAtlas.transport_overlap_iff_univ e i.down j.down
    rw [hset]
    exact A.transition_differentiableOn i.down j.down

@[simp] theorem transport_univ_chart
    {X : Type (max u v)} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology)
    (i : ULift.{v} A.index) :
    (transport_univ A e).chart i = (A.chart i.down).transport e :=
  rfl

@[simp] theorem transport_univ_coverSet
    {X : Type (max u v)} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology) :
    (transport_univ A e).coverSet = e ⁻¹' A.coverSet :=
  rfl

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

@[simp] theorem transport_chart
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.topology)
    (i : A.index) :
    (transport A e).chart i = (A.chart i).transport e :=
  rfl

@[simp] theorem transport_coverSet
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.toComplexSurfaceChartFamily.topology) :
    (transport A e).coverSet = e ⁻¹' A.coverSet :=
  rfl

/-! The atlas-level transport inherits the chart-level associativity. -/

theorem transport_trans
    {X : Type u} {Y : Type u} {Z : Type u}
    {topologyX : TopologicalSpace X}
    {topologyY : TopologicalSpace Y}
    (A : ComplexSurfaceAtlas Z)
    (e : @Homeomorph X Y topologyX topologyY)
    (f : @Homeomorph Y Z topologyY A.toComplexSurfaceChartFamily.topology) :
    (A.transport f).transport e = A.transport
      (@Homeomorph.trans X Y Z topologyX topologyY
        A.toComplexSurfaceChartFamily.topology e f) := by
  rfl

theorem transport_refl
    {X : Type u}
    (A : ComplexSurfaceAtlas X) :
    transport A (@Homeomorph.refl X A.topology) = A := by
  rfl

/-! Atlas equality is dependent because both the chart index and the chart
    source topology are stored inside the structure.  This extensionality
    lemma isolates that bookkeeping from the geometric chart comparison: once
    the topological carrier, index, covered region, and each dependent chart
    are identified, the transition proof is propositionally irrelevant. -/

theorem ext
    {X : Type u} {A B : ComplexSurfaceAtlas X}
    (h_topology : A.topology = B.topology)
    (h_index : A.index = B.index)
    (h_coverSet : A.coverSet = B.coverSet)
    (h_chart : ∀ i : A.index,
      HEq (A.chart i) (B.chart (h_index ▸ i))) :
    A = B := by
  cases A with
  | mk A hA =>
    cases B with
    | mk B hB =>
      have hAB : A = B := by
        cases A with
        | mk topologyA indexA chartA coverSetA coversA =>
          cases B with
          | mk topologyB indexB chartB coverSetB coversB =>
            cases h_topology
            cases h_index
            have hchart : chartA = chartB := by
              funext k
              exact eq_of_heq (h_chart k)
            cases hchart
            cases h_coverSet
            rfl
      cases hAB
      rfl

/-! ### Chartwise holomorphic maps between different total spaces

For two surface atlases on different carriers, the coordinate expression of a
homeomorphism is most cleanly written by transporting the target chart back
to the source.  This avoids introducing an arbitrary extension of a chart
map outside its genuine domain: the ordinary `ComplexSurfaceChart.transitionMap`
already has exactly the required overlap restriction. -/

structure HolomorphicMap
    {X : Type u} {Y : Type v}
    (A : ComplexSurfaceAtlas X) (B : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y A.topology B.topology) : Prop where
  differentiableOn : ∀ i j,
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        (A.chart i) ((B.chart j).transport e))
        (ComplexSurfaceChart.overlap
        (A.chart i) ((B.chart j).transport e))

/-! A coordinate-level certificate is often easier to obtain than a direct
DifferentiableOn proof of the chart transition.  This structure records a
globally differentiable model map for each chart pair and its equality with
the actual transition on the genuine overlap. -/

structure HolomorphicMapCoordinateWitness
    {X : Type u} {Y : Type v}
    (A : ComplexSurfaceAtlas X) (B : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y A.topology B.topology) where
  coordinate : ∀ i j, ℂ × ℂ → ℂ × ℂ
  coordinate_differentiable : ∀ i j,
    Differentiable ℂ (coordinate i j)
  transition_eq : ∀ i j (p : ℂ × ℂ),
    p ∈ ComplexSurfaceChart.overlap
      (A.chart i) ((B.chart j).transport e) →
      ComplexSurfaceChart.transitionMap
        (A.chart i) ((B.chart j).transport e) p =
        coordinate i j p

def HolomorphicMapCoordinateWitness.toHolomorphicMap
    {X : Type u} {Y : Type v}
    {A : ComplexSurfaceAtlas X} {B : ComplexSurfaceAtlas Y}
    {e : @Homeomorph X Y A.topology B.topology}
    (W : HolomorphicMapCoordinateWitness A B e) :
    HolomorphicMap A B e := by
  refine { differentiableOn := ?_ }
  intro i j
  exact (W.coordinate_differentiable i j).differentiableOn.congr
    (W.transition_eq i j)

structure HolomorphicEquiv
    {X : Type u} {Y : Type v}
    (A : ComplexSurfaceAtlas X) (B : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y A.topology B.topology) : Prop where
  forward : HolomorphicMap A B e
  inverse : @HolomorphicMap Y X B A
    (@Homeomorph.symm X Y A.topology B.topology e)

theorem HolomorphicEquiv.castAtlases
    {X : Type u} {Y : Type v}
    {A A' : ComplexSurfaceAtlas X}
    {B B' : ComplexSurfaceAtlas Y}
    {e : @Homeomorph X Y A.topology B.topology}
    {e' : @Homeomorph X Y A'.topology B'.topology}
    (hA : A = A') (hB : B = B') (he : HEq e e')
    (H : HolomorphicEquiv A B e) :
    HolomorphicEquiv A' B' e' := by
  cases hA
  cases hB
  cases he
  exact H

theorem transport_holomorphicMap
    {X : Type u} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.topology) :
    HolomorphicMap (transport A e) A e := by
  refine { differentiableOn := ?_ }
  intro i j
  change DifferentiableOn ℂ
    (ComplexSurfaceChart.transitionMap
      ((A.chart i).transport e) ((A.chart j).transport e))
    (ComplexSurfaceChart.overlap
      ((A.chart i).transport e) ((A.chart j).transport e))
  rw [transport_transitionMap e i j]
  have hset : ComplexSurfaceChart.overlap
      ((A.chart i).transport e) ((A.chart j).transport e) =
      ComplexSurfaceChart.overlap (A.chart i) (A.chart j) := by
    ext p
    exact transport_overlap_iff e i j
  rw [hset]
  exact A.transition_differentiableOn i j

theorem transport_univ_holomorphicMap
    {X : Type (max u v)} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.topology) :
    HolomorphicMap (transport_univ A e) A e := by
  refine { differentiableOn := ?_ }
  intro i j
  change DifferentiableOn ℂ
    (ComplexSurfaceChart.transitionMap
      ((A.chart i.down).transport e) ((A.chart j).transport e))
    (ComplexSurfaceChart.overlap
      ((A.chart i.down).transport e) ((A.chart j).transport e))
  rw [transport_transitionMap_univ e i.down j]
  have hset : ComplexSurfaceChart.overlap
      ((A.chart i.down).transport e) ((A.chart j).transport e) =
      ComplexSurfaceChart.overlap (A.chart i.down) (A.chart j) := by
    ext p
    exact transport_overlap_iff_univ e i.down j
  rw [hset]
  exact A.transition_differentiableOn i.down j

theorem transport_univ_holomorphicEquiv
    {X : Type (max u v)} {Y : Type u}
    {topologyX : TopologicalSpace X}
    (A : ComplexSurfaceAtlas Y)
    (e : @Homeomorph X Y topologyX A.topology) :
    HolomorphicEquiv (transport_univ A e) A e := by
  letI : TopologicalSpace Y := A.topology
  refine
    { forward := transport_univ_holomorphicMap A e
      inverse := ?_ }
  refine { differentiableOn := ?_ }
  intro j i
  cases i with
  | up i =>
    change DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        (A.chart j)
        (((A.chart i).transport e).transport e.symm))
      (ComplexSurfaceChart.overlap
        (A.chart j)
        (((A.chart i).transport e).transport e.symm))
    rw [ComplexSurfaceChart.transport_symm_trans e]
    exact A.transition_differentiableOn j i

theorem HolomorphicEquiv.refl
    {X : Type u}
    (A : ComplexSurfaceAtlas X) :
    HolomorphicEquiv A A
      (@Homeomorph.refl X A.topology) := by
  refine
    { forward := ?_
      inverse := ?_ }
  · refine { differentiableOn := ?_ }
    intro i j
    change DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        (A.chart i) ((A.chart j).transport
          (@Homeomorph.refl X A.topology)))
      (ComplexSurfaceChart.overlap
        (A.chart i) ((A.chart j).transport
          (@Homeomorph.refl X A.topology)))
    rw [ComplexSurfaceChart.transport_refl]
    exact A.transition_differentiableOn i j
  · refine { differentiableOn := ?_ }
    intro i j
    change DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        (A.chart i) ((A.chart j).transport
          (@Homeomorph.refl X A.topology)))
      (ComplexSurfaceChart.overlap
        (A.chart i) ((A.chart j).transport
          (@Homeomorph.refl X A.topology)))
    rw [ComplexSurfaceChart.transport_refl]
    exact A.transition_differentiableOn i j

theorem Homeomorph.refl_heq_of_atlas_eq
    {X : Type u} {A B : ComplexSurfaceAtlas X}
    (h : A = B) :
    HEq (@Homeomorph.refl X A.topology)
      (@Homeomorph.refl X B.topology) := by
  cases h
  rfl

theorem Homeomorph.self_heq_of_atlas_eq
    {X : Type u} {Y : Type v}
    {A A' : ComplexSurfaceAtlas X}
    {B B' : ComplexSurfaceAtlas Y}
    (e : @Homeomorph X Y A.topology B.topology)
    (hA : A = A') (hB : B = B') :
    HEq e e := by
  cases hA
  cases hB
  rfl

/-! If two spaces are both obtained from one mother atlas, their comparison
    map is holomorphic for the same cancellation reason as `transport`:
    transporting the target chart back along the comparison gives the source
    chart.  This is the reusable bridge from a common geometric model to the
    chartwise interface above. -/

theorem commonTransport_holomorphicMap
    {X Y Z : Type u}
    {topologyX : TopologicalSpace X}
    {topologyZ : TopologicalSpace Z}
    (A : ComplexSurfaceAtlas Y)
    (eX : @Homeomorph X Y topologyX A.topology)
    (eZ : @Homeomorph Z Y topologyZ A.topology)
    (e : @Homeomorph X Z topologyX topologyZ)
    (hcomp : @Homeomorph.trans X Z Y topologyX topologyZ A.topology e eZ = eX) :
    HolomorphicMap (transport A eX) (transport A eZ) e := by
  refine { differentiableOn := ?_ }
  intro i j
  have htarget :
      ((A.chart j).transport eZ).transport e =
        (A.chart j).transport eX := by
    rw [ComplexSurfaceChart.transport_trans, hcomp]
  change DifferentiableOn ℂ
    (ComplexSurfaceChart.transitionMap
      ((A.chart i).transport eX)
      (((A.chart j).transport eZ).transport e))
    (ComplexSurfaceChart.overlap
      ((A.chart i).transport eX)
      (((A.chart j).transport eZ).transport e))
  rw [htarget]
  exact (transport A eX).transition_differentiableOn i j

theorem commonTransport_holomorphicEquiv
    {X Y Z : Type u}
    {topologyX : TopologicalSpace X}
    {topologyZ : TopologicalSpace Z}
    (A : ComplexSurfaceAtlas Y)
    (eX : @Homeomorph X Y topologyX A.topology)
    (eZ : @Homeomorph Z Y topologyZ A.topology)
    (e : @Homeomorph X Z topologyX topologyZ)
    (hcomp : @Homeomorph.trans X Z Y topologyX topologyZ A.topology e eZ = eX) :
    HolomorphicEquiv (transport A eX) (transport A eZ) e := by
  letI : TopologicalSpace Y := A.topology
  have hcomp_symm :
      @Homeomorph.trans Z X Y topologyZ topologyX A.topology e.symm eX = eZ := by
    apply Homeomorph.ext
    intro z
    have h := congrArg (fun f => f (e.symm z)) hcomp
    simpa using h.symm
  exact
    { forward := commonTransport_holomorphicMap A eX eZ e hcomp
      inverse := commonTransport_holomorphicMap A eZ eX e.symm hcomp_symm }

/-! Restrict an atlas to an open subspace.  The index set is unchanged, each
chart is restricted by the chart-level construction above, and the covered
region is pulled back along the subtype inclusion.  The transition theorem
shows that no new analytic calculation is needed: on the restricted overlap
the coordinate map is the old transition map. -/

noncomputable def restrictOpenSubspace
    {X : Type u}
    (A : ComplexSurfaceAtlas X)
    (U : Set X) (hU : @IsOpen X A.topology U) :
    ComplexSurfaceAtlas U :=
  letI : TopologicalSpace X := A.topology
  { toComplexSurfaceChartFamily :=
      { topology := TopologicalSpace.induced Subtype.val A.topology
        index := A.index
        chart := fun i => (A.chart i).restrictOpenSubspace U hU
        coverSet := Subtype.val ⁻¹' A.coverSet
        covers := by
          intro x hx
          rcases A.covers (x : X) hx with ⟨i, hi⟩
          exact ⟨i, hi⟩ }
    transition_differentiableOn := by
      intro i j
      have hsubset :
          ComplexSurfaceChart.overlap
              ((A.chart i).restrictOpenSubspace U hU)
              ((A.chart j).restrictOpenSubspace U hU) ⊆
            ComplexSurfaceChart.overlap (A.chart i) (A.chart j) :=
        fun {p} hp => ComplexSurfaceChart.restrictOpenSubspace_overlap_subset
          (A.chart i) (A.chart j) U hU hp
      have hdiff := (A.transition_differentiableOn i j).mono hsubset
      refine hdiff.congr ?_
      intro p hp
      exact ComplexSurfaceChart.restrictOpenSubspace_transitionMap_on_overlap
        (A.chart i) (A.chart j) U hU hp }

    @[simp] theorem restrictOpenSubspace_coverSet
    {X : Type u}
    (A : ComplexSurfaceAtlas X)
    (U : Set X) (hU : @IsOpen X A.topology U) :
    (restrictOpenSubspace A U hU).coverSet = Subtype.val ⁻¹' A.coverSet :=
  rfl

@[simp] theorem restrictOpenSubspace_chart
    {X : Type u}
    (A : ComplexSurfaceAtlas X)
    (U : Set X) (hU : @IsOpen X A.topology U)
    (i : A.index) :
    (restrictOpenSubspace A U hU).chart i =
      (A.chart i).restrictOpenSubspace U hU :=
  rfl

theorem restrictOpenSubspace_transition_is_differentiableOn
    {X : Type u}
    (A : ComplexSurfaceAtlas X)
    (U : Set X) (hU : @IsOpen X A.topology U)
    (i j : A.index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((A.chart i).restrictOpenSubspace U hU)
        ((A.chart j).restrictOpenSubspace U hU))
      (ComplexSurfaceChart.overlap
        ((A.chart i).restrictOpenSubspace U hU)
        ((A.chart j).restrictOpenSubspace U hU)) :=
  (restrictOpenSubspace A U hU).transition_differentiableOn i j

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

/-! ### Fixed-parameter fibre slices

The total-space atlas does not by itself produce a one-dimensional atlas on a
fibre: a chart may have an arbitrary model range, and the existence of a
slice inverse is extra local geometry.  The following definitions record
exactly that missing datum.  Once supplied, holomorphicity of the fibre
transitions is not an additional axiom: it is obtained by restricting the
two-dimensional transition map to the constant base coordinate.
-/

def Fiber {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) :=
  {x : X // A.projection x = b}

abbrev FiberChart {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) :=
  @ComplexChart (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)

abbrev FiberChartOverlap {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (c₁ c₂ : FiberChart A b) : Set ℂ :=
  @ComplexChart.overlap (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)
    c₁ c₂

abbrev FiberChartTransitionMap {X : Type u} {B : Type w}
    [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (c₁ c₂ : FiberChart A b) : ℂ → ℂ :=
  @ComplexChart.transitionMap (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)
    c₁ c₂

abbrev fiberChartDomain {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (c : FiberChart A b) : Set (Fiber A b) :=
  @ComplexChart.domain (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)
    c

abbrev fiberChartToComplex {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (c : FiberChart A b) : Fiber A b → ℂ :=
  @ComplexChart.toComplex (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)
    c

abbrev fiberChartRange {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (c : FiberChart A b) : Set ℂ :=
  @ComplexChart.range (Fiber A b)
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)
    c

def fiberVal {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) : Fiber A b → X :=
  fun x => x.1

def fiberDomain {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) (i : A.index) :
    Set (Fiber A b) :=
  Subtype.val ⁻¹' (A.chart i).domain

structure FiberSliceAtlasWitness {X : Type u} {B : Type w}
    [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) where
  chart : ∀ i : A.index,
    FiberChart A b
  domain_eq : ∀ i, fiberChartDomain A b (chart i) = fiberDomain A b i
  coordinate_eq : ∀ i (x : Fiber A b)
      (hx : x ∈ fiberChartDomain A b (chart i))
      (hxA : x.1 ∈ (A.chart i).domain),
      fiberChartToComplex A b (chart i) x =
        ((A.chart i).chart ⟨x.1, hxA⟩).1.2
  fibre_covered : ∀ x : Fiber A b, x.1 ∈ A.coverSet

namespace FiberSliceAtlasWitness

theorem source_total_coordinate_eq
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (W : FiberSliceAtlasWitness A b) (i : A.index)
    {z : ℂ} (hz : z ∈ fiberChartRange A b (W.chart i)) :
    (A.parameterCoordinate b, z) ∈ (A.chart i).range := by
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  letI : TopologicalSpace (Fiber A b) :=
    TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology
  let x : Fiber A b := (W.chart i).fromComplex z
  have hx : x ∈ fiberChartDomain A b (W.chart i) :=
    (W.chart i).inverse_into hz
  have hxA : fiberVal A b x ∈ (A.chart i).domain := by
    rw [W.domain_eq i] at hx
    exact hx
  have hslice : fiberChartToComplex A b (W.chart i) x = z :=
    (W.chart i).right_inv hz
  have hcoord :
      ((A.chart i).chart ⟨fiberVal A b x, hxA⟩).1 =
        (A.parameterCoordinate b, z) := by
    apply Prod.ext
    · rw [A.chart_base_coordinate i hxA]
      exact congrArg A.parameterCoordinate x.property
    · calc
        ((A.chart i).chart ⟨fiberVal A b x, hxA⟩).1.2 =
            fiberChartToComplex A b (W.chart i) x := by
          symm
          exact W.coordinate_eq i x hx hxA
        _ = z := hslice
  have hmem := (A.chart i).chart ⟨fiberVal A b x, hxA⟩ |>.property
  simpa [hcoord] using hmem

theorem total_transition_eq_slice_transition
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (W : FiberSliceAtlasWitness A b) (i j : A.index)
    {z : ℂ}
    (hz : z ∈ FiberChartOverlap A b (W.chart i) (W.chart j)) :
    FiberChartTransitionMap A b (W.chart i) (W.chart j) z =
      (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j)
        (A.parameterCoordinate b, z)).2 := by
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  letI : TopologicalSpace (Fiber A b) :=
    TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology
  let x : Fiber A b := (W.chart i).fromComplex z
  have hzi : z ∈ (W.chart i).range := hz.1
  have hxi : x ∈ fiberChartDomain A b (W.chart i) :=
    (W.chart i).inverse_into hzi
  have hxj : x ∈ fiberChartDomain A b (W.chart j) := hz.2
  have hxiA : fiberVal A b x ∈ (A.chart i).domain := by
    rw [W.domain_eq i] at hxi
    exact hxi
  have hxjA : fiberVal A b x ∈ (A.chart j).domain := by
    rw [W.domain_eq j] at hxj
    exact hxj
  have hslice_i : fiberChartToComplex A b (W.chart i) x = z :=
    (W.chart i).right_inv hzi
  have hsource_coord :
      ((A.chart i).chart ⟨fiberVal A b x, hxiA⟩).1 =
        (A.parameterCoordinate b, z) := by
    apply Prod.ext
    · rw [A.chart_base_coordinate i hxiA]
      exact congrArg A.parameterCoordinate x.property
    · calc
        ((A.chart i).chart ⟨fiberVal A b x, hxiA⟩).1.2 =
            fiberChartToComplex A b (W.chart i) x := by
          symm
          exact W.coordinate_eq i x hxi hxiA
        _ = z := hslice_i
  have hsource_range :
      (A.parameterCoordinate b, z) ∈ (A.chart i).range := by
    have hmem := (A.chart i).chart ⟨fiberVal A b x, hxiA⟩ |>.property
    simpa [hsource_coord] using hmem
  have hsource_from :
      ((A.chart i).chart.symm
        ⟨(A.parameterCoordinate b, z), hsource_range⟩).1 =
          fiberVal A b x := by
    have h := (A.chart i).chart.left_inv
      ⟨fiberVal A b x, hxiA⟩
    have h' :
        (A.chart i).chart.symm
          ⟨(A.parameterCoordinate b, z), hsource_range⟩ =
          (⟨fiberVal A b x, hxiA⟩ :
            {y : X // y ∈ (A.chart i).domain}) := by
      apply (A.chart i).chart.injective
      rw [A.chart i |>.chart.apply_symm_apply]
      exact Subtype.ext hsource_coord.symm
    exact congrArg Subtype.val h'
  have htarget_overlap :
      (A.parameterCoordinate b, z) ∈
        ComplexSurfaceChart.overlap (A.chart i) (A.chart j) := by
    refine ⟨hsource_range, ?_⟩
    change ((A.chart i).chart.symm
      ⟨(A.parameterCoordinate b, z), hsource_range⟩).1 ∈
      (A.chart j).domain
    rw [hsource_from]
    exact hxjA
  have htotal := ComplexSurfaceChart.transitionMap_on_overlap
    (A.chart i) (A.chart j) htarget_overlap
  have htransition_value :
      ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j)
        (A.parameterCoordinate b, z) =
        ((A.chart j).chart ⟨fiberVal A b x, hxjA⟩).1 := by
    rw [htotal]
    have htarget_point :
        (⟨((A.chart i).chart.symm
            ⟨(A.parameterCoordinate b, z), hsource_range⟩).1,
          ComplexSurfaceChart.overlapSourceRangeProof_spec
            (A.chart i) (A.chart j) htarget_overlap⟩ :
          {y : X // y ∈ (A.chart j).domain}) =
        ⟨fiberVal A b x, hxjA⟩ := by
      apply Subtype.ext
      exact hsource_from
    exact congrArg (fun q : {y : X // y ∈ (A.chart j).domain} =>
      ((A.chart j).chart q).1) htarget_point
  rw [htransition_value]
  simpa [FiberChartTransitionMap, ComplexChart.transitionMap,
    fiberChartToComplex, fiberVal, x] using
    W.coordinate_eq j x hxj hxjA

theorem transition_holomorphic
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B)
    (W : FiberSliceAtlasWitness A b) (i j : A.index) :
    DifferentiableOn ℂ
      (FiberChartTransitionMap A b (W.chart i) (W.chart j))
      (FiberChartOverlap A b (W.chart i) (W.chart j)) := by
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  letI : TopologicalSpace (Fiber A b) :=
    TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology
  let U : Set (ℂ × ℂ) :=
    ComplexSurfaceChart.overlap (A.chart i) (A.chart j)
  let V : Set ℂ := FiberChartOverlap A b (W.chart i) (W.chart j)
  let g : ℂ → ℂ × ℂ := fun z => (A.parameterCoordinate b, z)
  have hg : Differentiable ℂ g := by
    dsimp [g]
    exact (differentiable_const _).prodMk differentiable_id
  have hmaps : Set.MapsTo g V U := by
    intro z hz
    exact (by
      simpa [g, U] using
        (source_total_coordinate_eq A b W i hz.1))
      |> fun hsource =>
        ⟨hsource, by
          have hslice_mem :
              (W.chart i).fromComplex z ∈
                fiberChartDomain A b (W.chart j) := hz.2
          have hsource_mem :
              (W.chart i).fromComplex z ∈
                fiberChartDomain A b (W.chart i) :=
            (W.chart i).inverse_into hz.1
          have hxiA :
              ((W.chart i).fromComplex z).1 ∈ (A.chart i).domain := by
            have hxi :
                (W.chart i).fromComplex z ∈
                  fiberChartDomain A b (W.chart i) :=
              (W.chart i).inverse_into hz.1
            rw [W.domain_eq i] at hxi
            exact hxi
          have hxjA :
              ((W.chart i).fromComplex z).1 ∈ (A.chart j).domain := by
            rw [W.domain_eq j] at hslice_mem
            exact hslice_mem
          have hsource_range := source_total_coordinate_eq A b W i hz.1
          have hfrom :
              ((A.chart i).chart.symm
                ⟨g z, hsource_range⟩).1 =
                ((W.chart i).fromComplex z).1 := by
            have hcoord :
                ((A.chart i).chart
                  ⟨((W.chart i).fromComplex z).1, hxiA⟩).1 =
                    g z := by
              apply Prod.ext
              · rw [A.chart_base_coordinate i hxiA]
                exact congrArg A.parameterCoordinate
                  ((W.chart i).fromComplex z).property
              · calc
                  ((A.chart i).chart
                    ⟨((W.chart i).fromComplex z).1, hxiA⟩).1.2 =
                      fiberChartToComplex A b (W.chart i)
                        ((W.chart i).fromComplex z) := by
                    symm
                    exact W.coordinate_eq i
                      ((W.chart i).fromComplex z) hsource_mem hxiA
                  _ = z := (W.chart i).right_inv hz.1
            have hpoint :
                (A.chart i).chart.symm ⟨g z, hsource_range⟩ =
                  (⟨((W.chart i).fromComplex z).1, hxiA⟩ :
                    {y : X // y ∈ (A.chart i).domain}) := by
              apply (A.chart i).chart.injective
              rw [A.chart i |>.chart.apply_symm_apply]
              exact Subtype.ext hcoord.symm
            exact congrArg Subtype.val hpoint
          change ((A.chart i).chart.symm
            ⟨g z, hsource_range⟩).1 ∈ (A.chart j).domain
          rw [hfrom]
          exact hxjA⟩
  have htotal : DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j)) U :=
    A.transition_differentiableOn i j
  have hcomp : DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j) ∘ g) V :=
    htotal.fun_comp hg.differentiableOn hmaps
  have hsecond : DifferentiableOn ℂ
      (fun z => (ComplexSurfaceChart.transitionMap (A.chart i) (A.chart j)
        (g z)).2) V := by
    have hsnd : DifferentiableOn ℂ (fun p : ℂ × ℂ => p.2) Set.univ :=
      (differentiable_snd :
        Differentiable ℂ (fun p : ℂ × ℂ => p.2)).differentiableOn
    have h := hsnd.fun_comp hcomp (fun _ _ => Set.mem_univ _)
    simpa [Function.comp_def] using h
  apply hsecond.congr
  intro z hz
  simpa [g] using total_transition_eq_slice_transition A b W i j hz

end FiberSliceAtlasWitness

/-! The atlas-level restriction preserves the family structure as well.  The
projection is simply restricted along the subtype inclusion, the parameter
coordinate is unchanged, and the first-coordinate identity is inherited from
the old chart by the chart-level computation. -/

noncomputable def restrictOpenSubspace
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B)
    (U : Set X)
    (hU : @IsOpen X A.toComplexSurfaceAtlas.topology U) :
    ComplexSurfaceFamilyAtlas U B := by
  letI : TopologicalSpace X := A.toComplexSurfaceAtlas.topology
  exact
    { toComplexSurfaceAtlas :=
        ComplexSurfaceAtlas.restrictOpenSubspace
          A.toComplexSurfaceAtlas U hU
      projection := fun x => A.projection (x : X)
      parameterCoordinate := A.parameterCoordinate
      projection_continuous := by
        exact A.projection_continuous.comp continuous_subtype_val
      chart_base_coordinate := by
        intro i x hx
        have hx_old : (x : X) ∈ (A.chart i).domain := by
          exact hx
        have hcoord := A.chart_base_coordinate i hx_old
        have hrestrict := ComplexSurfaceChart.restrictOpenSubspace_chart_apply
          (A.chart i) U hU hx
        calc
          (((ComplexSurfaceAtlas.restrictOpenSubspace
              A.toComplexSurfaceAtlas U hU).chart i).chart
              ⟨x, hx⟩).1.1 =
              ((A.chart i).chart ⟨(x : X), hx_old⟩).1.1 := by
            exact congrArg Prod.fst hrestrict
          _ = A.parameterCoordinate (A.projection (x : X)) := by
            simpa using hcoord }

@[simp] theorem restrictOpenSubspace_projection
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B)
    (U : Set X)
    (hU : @IsOpen X A.toComplexSurfaceAtlas.topology U)
    (x : U) :
    (restrictOpenSubspace A U hU).projection x = A.projection (x : X) :=
  rfl

@[simp] theorem restrictOpenSubspace_parameterCoordinate
    {X : Type u} {B : Type w} [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B)
    (U : Set X)
    (hU : @IsOpen X A.toComplexSurfaceAtlas.topology U) :
    (restrictOpenSubspace A U hU).parameterCoordinate =
      A.parameterCoordinate :=
  rfl

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

/-! A transition cover whose sheet maps are already identified with explicit
    homeomorphisms of the coordinate plane.  This is the generic lift/deck
    interface: the index type is arbitrary, so a concrete lattice such as
    `ℤ × ℤ` is only one possible instance. -/

structure ComplexSurfaceChartDeckTransitionCover {X : Type u}
    (topology : TopologicalSpace X)
    (sourceChart targetChart : ComplexSurfaceChart X topology)
    (M : Type u) where
  sheet : M → ComplexSurfaceChartTransitionSheet topology sourceChart targetChart
  source_subset_overlap : ∀ i,
    (sheet i).source ⊆ ComplexSurfaceChart.overlap sourceChart targetChart
  covers : ComplexSurfaceChart.overlap sourceChart targetChart ⊆
    ⋃ i : M, (sheet i).source
  deck : M → (ℂ × ℂ) ≃ₜ (ℂ × ℂ)
  map_eq_deck_on_source : ∀ i, Set.EqOn
    (fun p => (sheet i).map p)
    (deck i)
    (sheet i).source

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

theorem ComplexSurfaceChartDeckTransitionCover.exists_sheet_at
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    {p : ℂ × ℂ}
    (hp : p ∈ ComplexSurfaceChart.overlap sourceChart targetChart) :
    ∃ i : M,
      p ∈ (C.sheet i).source ∧
      ComplexSurfaceChart.transitionMap sourceChart targetChart p =
        C.deck i p := by
  rcases Set.mem_iUnion.mp (C.covers hp) with ⟨i, hpi⟩
  refine ⟨i, hpi, ?_⟩
  exact
    (ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
      (C.sheet i) (C.source_subset_overlap i) hpi).trans
      (C.map_eq_deck_on_source i hpi)

/-! The same sheet selection can be stated directly at a common point of the
    two lifted charts.  This is the generic form of the torus calculation:
    the source coordinate lands in one sheet and the target coordinate is
    the corresponding deck image. -/

theorem ComplexSurfaceChartDeckTransitionCover.chart_transition_eq_deck_at
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (x : X)
    (hx₁ : x ∈ sourceChart.domain)
    (hx₂ : x ∈ targetChart.domain) :
    ∃ i : M,
      (sourceChart.chart ⟨x, hx₁⟩).1 ∈ (C.sheet i).source ∧
      (targetChart.chart ⟨x, hx₂⟩).1 =
        C.deck i ((sourceChart.chart ⟨x, hx₁⟩).1) := by
  let p₁ := (sourceChart.chart ⟨x, hx₁⟩).1
  let p₂ := (targetChart.chart ⟨x, hx₂⟩).1
  have hsourceRange : p₁ ∈ sourceChart.range := by
    exact (sourceChart.chart ⟨x, hx₁⟩).property
  have hinv :
      (sourceChart.chart.symm ⟨p₁, hsourceRange⟩).1 = x := by
    have hchart :
        (⟨p₁, hsourceRange⟩ : {p : ℂ × ℂ // p ∈ sourceChart.range}) =
          sourceChart.chart ⟨x, hx₁⟩ := by
      apply Subtype.ext
      rfl
    calc
      (sourceChart.chart.symm ⟨p₁, hsourceRange⟩).1 =
          (sourceChart.chart.symm (sourceChart.chart ⟨x, hx₁⟩)).1 := by
            rw [← hchart]
      _ = x := by
        exact congrArg Subtype.val
          (sourceChart.chart.symm_apply_apply ⟨x, hx₁⟩)
  have hOverlap : p₁ ∈ ComplexSurfaceChart.overlap sourceChart targetChart := by
    refine ⟨hsourceRange, ?_⟩
    change (sourceChart.chart.symm ⟨p₁, hsourceRange⟩).1 ∈ targetChart.domain
    rw [hinv]
    exact hx₂
  have hsheet := C.exists_sheet_at hOverlap
  rcases hsheet with ⟨i, hpi, htransition⟩
  have htransition_point :
      ComplexSurfaceChart.transitionMap sourceChart targetChart p₁ = p₂ := by
    rw [ComplexSurfaceChart.transitionMap_on_overlap
      sourceChart targetChart hOverlap]
    have hpoint :
        (sourceChart.chart.symm
          ⟨p₁,
            ComplexSurfaceChart.overlapSourceRangeProof
              sourceChart targetChart hOverlap⟩).1 = x := by
      have hchart :
          (⟨p₁,
              ComplexSurfaceChart.overlapSourceRangeProof
                sourceChart targetChart hOverlap⟩ :
            {p : ℂ × ℂ // p ∈ sourceChart.range}) =
            sourceChart.chart ⟨x, hx₁⟩ := by
        apply Subtype.ext
        rfl
      calc
        (sourceChart.chart.symm
            ⟨p₁,
              ComplexSurfaceChart.overlapSourceRangeProof
                sourceChart targetChart hOverlap⟩).1 =
            (sourceChart.chart.symm (sourceChart.chart ⟨x, hx₁⟩)).1 := by
              rw [← hchart]
        _ = x := by
          exact congrArg Subtype.val
            (sourceChart.chart.symm_apply_apply ⟨x, hx₁⟩)
    have htarget :
        (⟨(sourceChart.chart.symm
            ⟨p₁,
              ComplexSurfaceChart.overlapSourceRangeProof
                sourceChart targetChart hOverlap⟩).1,
          ComplexSurfaceChart.overlapSourceRangeProof_spec
            sourceChart targetChart hOverlap⟩ :
          {x : X // x ∈ targetChart.domain}) =
        ⟨x, hx₂⟩ := by
      apply Subtype.ext
      exact hpoint
    rw [htarget]
  refine ⟨i, hpi, ?_⟩
  change p₂ = C.deck i p₁
  rw [← htransition_point]
  exact htransition

/-! A cover gives a useful local branch only after we record how the branch is
    chosen.  The following selector lives on the overlap subtype, so it does
    not need an artificial default index when the overlap is empty. -/

noncomputable def ComplexSurfaceChartDeckTransitionCover.sheetSelector
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart}) : M :=
  Classical.choose (Set.mem_iUnion.mp (C.covers p.property))

theorem ComplexSurfaceChartDeckTransitionCover.sheetSelector_mem
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart}) :
    (p : ℂ × ℂ) ∈ (C.sheet (C.sheetSelector p)).source := by
  exact Classical.choose_spec (Set.mem_iUnion.mp (C.covers p.property))

theorem ComplexSurfaceChartDeckTransitionCover.sheetSelector_eq_of_mem
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source)
    {p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart}}
    {i : M} (hpi : (p : ℂ × ℂ) ∈ (C.sheet i).source) :
    C.sheetSelector p = i := by
  by_contra hne
  exact Set.disjoint_left.1
    (pairwise_disjoint (C.sheetSelector p) i hne)
    (C.sheetSelector_mem p) hpi

/-! If the sheet source sets are open and pairwise disjoint, the selector is
    locally constant.  This is the precise local-stability statement needed
    before one can attach a topology or a continuity theorem to the discrete
    sheet index. -/

theorem ComplexSurfaceChartDeckTransitionCover.eventually_sheetSelector_eq
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (source_open : ∀ i, IsOpen (C.sheet i).source)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source)
    (p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart}) :
    ∀ᶠ q in 𝓝 p, C.sheetSelector q = C.sheetSelector p := by
  let i := C.sheetSelector p
  have hi : (p : ℂ × ℂ) ∈ (C.sheet i).source := by
    exact C.sheetSelector_mem p
  have hpreimage : IsOpen
      ((fun q : {r : ℂ × ℂ // r ∈
          ComplexSurfaceChart.overlap sourceChart targetChart} =>
        (q : ℂ × ℂ)) ⁻¹' (C.sheet i).source) := by
    exact (source_open i).preimage continuous_subtype_val
  have hnear : ∀ᶠ q : {r : ℂ × ℂ // r ∈
      ComplexSurfaceChart.overlap sourceChart targetChart} in 𝓝 p,
      (q : ℂ × ℂ) ∈ (C.sheet i).source := by
    exact hpreimage.mem_nhds hi
  filter_upwards [hnear] with q hq
  exact (C.sheetSelector_eq_of_mem pairwise_disjoint hq).trans
    (C.sheetSelector_eq_of_mem pairwise_disjoint hi).symm

theorem ComplexSurfaceChartDeckTransitionCover.isLocallyConstant_sheetSelector
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (source_open : ∀ i, IsOpen (C.sheet i).source)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source) :
    IsLocallyConstant C.sheetSelector := by
  apply (IsLocallyConstant.iff_eventually_eq C.sheetSelector).2
  intro p
  exact C.eventually_sheetSelector_eq source_open pairwise_disjoint p

theorem ComplexSurfaceChartDeckTransitionCover.continuous_sheetSelector
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u} [TopologicalSpace M] [DiscreteTopology M]
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (source_open : ∀ i, IsOpen (C.sheet i).source)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source) :
    Continuous C.sheetSelector := by
  exact (IsLocallyConstant.iff_continuous C.sheetSelector).1
    (C.isLocallyConstant_sheetSelector source_open pairwise_disjoint)

noncomputable def ComplexSurfaceChartDeckTransitionCover.selectedDeckMap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M) :
    {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart} →
      ℂ × ℂ :=
  fun p => C.deck (C.sheetSelector p) (p : ℂ × ℂ)

theorem ComplexSurfaceChartDeckTransitionCover.transitionMap_eq_selectedDeckMap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u}
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart}) :
    ComplexSurfaceChart.transitionMap sourceChart targetChart (p : ℂ × ℂ) =
      C.selectedDeckMap p := by
  let i := C.sheetSelector p
  have hsource : (p : ℂ × ℂ) ∈ (C.sheet i).source := by
    exact C.sheetSelector_mem p
  rw [ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
    (C.sheet i) (C.source_subset_overlap i) hsource]
  change (C.sheet i).map (p : ℂ × ℂ) = C.deck i (p : ℂ × ℂ)
  exact C.map_eq_deck_on_source i hsource

theorem ComplexSurfaceChartDeckTransitionCover.selectedDeckMap_comp_on_overlap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart middleChart targetChart : ComplexSurfaceChart X topology}
    {M₁ M₂ M₃ : Type u}
    (C₁₂ : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart middleChart M₁)
    (C₂₃ : ComplexSurfaceChartDeckTransitionCover
      topology middleChart targetChart M₂)
    (C₁₃ : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M₃)
    (p : {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart middleChart})
    (h₂₃ :
      C₁₂.selectedDeckMap p ∈
        ComplexSurfaceChart.overlap middleChart targetChart)
    (h₁₃ :
      (p : ℂ × ℂ) ∈
        ComplexSurfaceChart.overlap sourceChart targetChart) :
    C₂₃.selectedDeckMap
        ⟨C₁₂.selectedDeckMap p, h₂₃⟩ =
      C₁₃.selectedDeckMap ⟨p, h₁₃⟩ := by
  have h₂₃' :
      ComplexSurfaceChart.transitionMap sourceChart middleChart
          (p : ℂ × ℂ) ∈
        ComplexSurfaceChart.overlap middleChart targetChart := by
    rw [C₁₂.transitionMap_eq_selectedDeckMap p]
    exact h₂₃
  calc
    C₂₃.selectedDeckMap
          ⟨C₁₂.selectedDeckMap p, h₂₃⟩ =
        ComplexSurfaceChart.transitionMap middleChart targetChart
          (C₁₂.selectedDeckMap p) :=
      (C₂₃.transitionMap_eq_selectedDeckMap
        ⟨C₁₂.selectedDeckMap p, h₂₃⟩).symm
    _ =
        ComplexSurfaceChart.transitionMap middleChart targetChart
          (ComplexSurfaceChart.transitionMap sourceChart middleChart
            (p : ℂ × ℂ)) := by
      rw [C₁₂.transitionMap_eq_selectedDeckMap p]
    _ =
        ComplexSurfaceChart.transitionMap sourceChart targetChart
          (p : ℂ × ℂ) :=
      (ComplexSurfaceChart.transitionMap_comp_on_overlap
        sourceChart middleChart targetChart p.property h₂₃').symm
    _ = C₁₃.selectedDeckMap ⟨p, h₁₃⟩ :=
      C₁₃.transitionMap_eq_selectedDeckMap ⟨p, h₁₃⟩

theorem ComplexSurfaceChartDeckTransitionCover.continuous_selectedDeckMap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u} [TopologicalSpace M] [DiscreteTopology M]
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (source_open : ∀ i, IsOpen (C.sheet i).source)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source) :
    Continuous C.selectedDeckMap := by
  rw [continuous_iff_continuousAt]
  intro p
  let i := C.sheetSelector p
  have hbranch : ContinuousAt
      (fun q : {r : ℂ × ℂ // r ∈ ComplexSurfaceChart.overlap sourceChart targetChart} =>
        C.deck i (q : ℂ × ℂ)) p := by
    exact (C.deck i).continuous.continuousAt.comp
      continuous_subtype_val.continuousAt
  apply hbranch.congr_of_eventuallyEq
  filter_upwards [C.eventually_sheetSelector_eq source_open pairwise_disjoint p] with q hq
  change C.deck (C.sheetSelector q) (q : ℂ × ℂ) =
    C.deck i (q : ℂ × ℂ)
  rw [hq]

theorem ComplexSurfaceChartDeckTransitionCover.continuous_transitionMap_on_overlap
    {X : Type u} {topology : TopologicalSpace X}
    {sourceChart targetChart : ComplexSurfaceChart X topology}
    {M : Type u} [TopologicalSpace M] [DiscreteTopology M]
    (C : ComplexSurfaceChartDeckTransitionCover
      topology sourceChart targetChart M)
    (source_open : ∀ i, IsOpen (C.sheet i).source)
    (pairwise_disjoint : ∀ i j, i ≠ j →
      Disjoint (C.sheet i).source (C.sheet j).source) :
    Continuous (fun p :
      {q : ℂ × ℂ // q ∈ ComplexSurfaceChart.overlap sourceChart targetChart} =>
      ComplexSurfaceChart.transitionMap sourceChart targetChart (p : ℂ × ℂ)) := by
  have hselected := C.continuous_selectedDeckMap source_open pairwise_disjoint
  apply hselected.congr
  intro p
  exact (C.transitionMap_eq_selectedDeckMap p).symm

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

/-! A slice witness now assembles into an honest one-dimensional atlas. -/

noncomputable def ComplexSurfaceFamilyAtlas.FiberSliceAtlasWitness.toComplexAtlas
    {X : Type u} {B : Type w} [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B} {b : B}
    (W : ComplexSurfaceFamilyAtlas.FiberSliceAtlasWitness A b) :
    @ComplexAtlas (ComplexSurfaceFamilyAtlas.Fiber A b)
      (TopologicalSpace.induced Subtype.val
        A.toComplexSurfaceAtlas.topology) := by
  letI : TopologicalSpace (ComplexSurfaceFamilyAtlas.Fiber A b) :=
    TopologicalSpace.induced
      (fun x : ComplexSurfaceFamilyAtlas.Fiber A b => x.1)
      A.toComplexSurfaceAtlas.topology
  refine
    { index := A.index
      chart := W.chart
      covers := ?_
      transition_holomorphic := ?_ }
  · intro x
    obtain ⟨i, hi⟩ := A.covers
      (ComplexSurfaceFamilyAtlas.fiberVal A b x) (W.fibre_covered x)
    exact ⟨i, by
      change x ∈ ComplexSurfaceFamilyAtlas.fiberChartDomain A b (W.chart i)
      rw [W.domain_eq i]
      exact hi⟩
  · intro i j
    exact ComplexSurfaceFamilyAtlas.FiberSliceAtlasWitness.transition_holomorphic
      A b W i j

/-- A map is holomorphic when every chart expression is Mathlib-differentiable
on the region where both charts are defined. -/
structure ChartwiseHolomorphicMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y) (f : X → Y) : Prop where
  differentiable_on_charts : ∀ i j,
    DifferentiableOn ℂ
      (ComplexAtlas.chartMap A B f i j)
      (ComplexAtlas.chartMapDomain A B f i j)

namespace ChartwiseHolomorphicMap

/-! Chartwise holomorphicity is stable under composition.  The proof uses the
    atlas cover on the intermediate space: over each source chart, the part
    mapping into one fixed intermediate chart is open, and these pieces cover
    the target chart domain.  This is the local analytic closure needed for
    composing fibrewise biholomorphisms. -/

def trans
    {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : ComplexAtlas X} {B : ComplexAtlas Y} {C : ComplexAtlas Z}
    (e : @Homeomorph X Y inferInstance inferInstance)
    (f : @Homeomorph Y Z inferInstance inferInstance)
    (h₁ : ChartwiseHolomorphicMap A B e)
    (h₂ : ChartwiseHolomorphicMap B C f) :
    ChartwiseHolomorphicMap A C (e.trans f) := by
  refine ⟨?_⟩
  intro i k
  let s : B.index → Set ℂ := fun j =>
    ComplexAtlas.chartMapDomain A B e i j ∩
      ComplexAtlas.chartMapDomain A C (e.trans f) i k
  have hopen₁ (j : B.index) :
      IsOpen (ComplexAtlas.chartMapDomain A B e i j) := by
    unfold ComplexAtlas.chartMapDomain
    exact (A.chart i).continuous_fromComplex.isOpen_inter_preimage
      (A.chart i).range_open ((B.chart j).domain_open.preimage e.continuous)
  have hopen₂ :
      IsOpen (ComplexAtlas.chartMapDomain A C (e.trans f) i k) := by
    unfold ComplexAtlas.chartMapDomain
    exact (A.chart i).continuous_fromComplex.isOpen_inter_preimage
      (A.chart i).range_open
        ((C.chart k).domain_open.preimage (e.trans f).continuous)
  have hs_open : ∀ j : B.index, IsOpen (s j) := by
    intro j
    exact (hopen₁ j).inter hopen₂
  have hs_union :
      (⋃ j : B.index, s j) =
        ComplexAtlas.chartMapDomain A C (e.trans f) i k := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨j, hz⟩
      change z ∈ s j at hz
      exact hz.2
    · intro hz
      obtain ⟨j, hj⟩ :=
        B.covers (e ((A.chart i).fromComplex z))
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine ⟨?_, hz⟩
      refine ⟨hz.1, ?_⟩
      exact hj
  have hpiece :
      ∀ j : B.index,
        DifferentiableOn ℂ
          (ComplexAtlas.chartMap A C (e.trans f) i k) (s j) := by
    intro j
    have hmap :
        Set.MapsTo (ComplexAtlas.chartMap A B e i j) (s j)
          (ComplexAtlas.chartMapDomain B C f j k) := by
      intro z hz
      have hzAB : z ∈ ComplexAtlas.chartMapDomain A B e i j := hz.1
      have hzAC : z ∈ ComplexAtlas.chartMapDomain A C (e.trans f) i k := hz.2
      have hy :
          e ((A.chart i).fromComplex z) ∈ (B.chart j).domain := by
        exact hzAB.2
      refine ⟨(B.chart j).maps_into hy, ?_⟩
      change
        (B.chart j).fromComplex
            ((B.chart j).toComplex (e ((A.chart i).fromComplex z))) ∈
          f ⁻¹' (C.chart k).domain
      rw [ComplexChart.chart_inverse_on_domain (B.chart j) hy]
      exact hzAC.2
    have hcomp :
      DifferentiableOn ℂ
          (ComplexAtlas.chartMap B C f j k ∘
            ComplexAtlas.chartMap A B e i j) (s j) :=
      (h₂.differentiable_on_charts j k).comp
        ((h₁.differentiable_on_charts i j).mono Set.inter_subset_left) hmap
    exact hcomp.congr (by
      intro z hz
      have hy :
          e ((A.chart i).fromComplex z) ∈ (B.chart j).domain := by
        exact hz.1.2
      change
        (C.chart k).toComplex
            ((e.trans f) ((A.chart i).fromComplex z)) =
          (C.chart k).toComplex
            (f ((B.chart j).fromComplex
              ((B.chart j).toComplex
                (e ((A.chart i).fromComplex z)))))
      rw [ComplexChart.chart_inverse_on_domain (B.chart j) hy]
      rfl)
  rw [← hs_union]
  exact DifferentiableOn.iUnion_of_isOpen hpiece hs_open

end ChartwiseHolomorphicMap

/-- A homeomorphism is biholomorphic at the atlas level when both directions
are chartwise holomorphic. -/
structure AtlasHolomorphicEquiv {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : ComplexAtlas X) (B : ComplexAtlas Y)
    (e : @Homeomorph X Y inferInstance inferInstance) : Prop where
  forward : ChartwiseHolomorphicMap A B e
  inverse : ChartwiseHolomorphicMap B A e.symm

namespace AtlasHolomorphicEquiv

def trans
    {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : ComplexAtlas X} {B : ComplexAtlas Y} {C : ComplexAtlas Z}
    {e : @Homeomorph X Y inferInstance inferInstance}
    {f : @Homeomorph Y Z inferInstance inferInstance}
    (h₁ : AtlasHolomorphicEquiv A B e)
    (h₂ : AtlasHolomorphicEquiv B C f) :
    AtlasHolomorphicEquiv A C (e.trans f) where
  forward := ChartwiseHolomorphicMap.trans e f h₁.forward h₂.forward
  inverse := by
    have h :=
      ChartwiseHolomorphicMap.trans f.symm e.symm h₂.inverse h₁.inverse
    have he :
        (e.trans f).symm = f.symm.trans e.symm := by
      ext z
      rfl
    rw [he]
    exact h

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
  carrier : Type v
  topology : TopologicalSpace carrier
  surface : @ComplexRiemannSurface carrier topology
  marking : @Homeomorph S carrier inferInstance topology

/-! Adding a homeomorphic marking turns the fibre atlas into the actual marked
Riemann-surface object used by the family and Teichmüller interfaces. -/

structure MarkedFiberSliceAtlasWitness {S : Type u} {X : Type v}
    {B : Type w} [TopologicalSpace S] [TopologicalSpace B]
    (A : ComplexSurfaceFamilyAtlas X B) (b : B) where
  slice : ComplexSurfaceFamilyAtlas.FiberSliceAtlasWitness A b
  marking : @Homeomorph S (ComplexSurfaceFamilyAtlas.Fiber A b)
    inferInstance
    (TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology)

noncomputable def MarkedFiberSliceAtlasWitness.toMarkedComplexRiemannSurface
    {S : Type u} {X : Type v} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {A : ComplexSurfaceFamilyAtlas X B} {b : B}
    (W : MarkedFiberSliceAtlasWitness (S := S) A b) :
    @MarkedComplexRiemannSurface S inferInstance := by
  let fiberTopology : TopologicalSpace (ComplexSurfaceFamilyAtlas.Fiber A b) :=
    TopologicalSpace.induced Subtype.val A.toComplexSurfaceAtlas.topology
  letI : TopologicalSpace (ComplexSurfaceFamilyAtlas.Fiber A b) :=
    fiberTopology
  refine
    { carrier := ComplexSurfaceFamilyAtlas.Fiber A b
      topology := fiberTopology
      surface := { atlas := W.slice.toComplexAtlas }
      marking := W.marking }

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
