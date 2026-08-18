import Teichmuller.MathlibBeltramiAEEq
import Teichmuller.MathlibComplex
import Teichmuller.MathlibFamily
import Teichmuller.MathlibFiberBundle
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Teichmuller
namespace MathlibFormal

open MeasureTheory
open scoped Topology ContDiff

universe u w

/-!
### Local Beltrami data on actual complex charts

The global a.e. cocycle from MathlibBeltramiAEEq is intentionally stronger
than what a chart atlas supplies: a chart transition is canonical only on its
overlap. This file therefore introduces the local version first. Measures
are restricted to the relevant overlap, while the underlying maps are the
actual ComplexChart.transitionMaps from Mathlib-backed atlas data.
-/

namespace ComplexAtlas

def chartTransition {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) : ℂ → ℂ :=
  ComplexChart.transitionMap (A.chart j) (A.chart i)

def chartOverlap {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) : Set ℂ :=
  ComplexChart.overlap (A.chart j) (A.chart i)

noncomputable def overlapMeasure {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (measure : A.index → Measure ℂ)
    (i j : A.index) : Measure ℂ :=
  (measure j).restrict (chartOverlap A i j)

def tripleOverlap {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j k : A.index) : Set ℂ :=
  {z | z ∈ chartOverlap A j k ∧
    chartTransition A j k z ∈ chartOverlap A i j}

noncomputable def tripleOverlapMeasure {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (measure : A.index → Measure ℂ)
    (i j k : A.index) : Measure ℂ :=
  (measure k).restrict (tripleOverlap A i j k)

theorem chartOverlap_isOpen
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) :
    IsOpen (chartOverlap A i j) := by
  unfold chartOverlap ComplexChart.overlap
  exact (A.chart j).continuous_fromComplex.isOpen_inter_preimage
    (A.chart j).range_open (A.chart i).domain_open

theorem chartTransition_continuousOn
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) :
    ContinuousOn (chartTransition A i j) (chartOverlap A i j) := by
  unfold chartTransition chartOverlap ComplexChart.transitionMap
    ComplexChart.overlap
  exact (A.chart i).continuous_toComplex.comp'
    ((A.chart j).continuous_fromComplex.mono Set.inter_subset_left)
    (fun z hz => hz.2)

theorem tripleOverlap_isOpen
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j k : A.index) :
    IsOpen (tripleOverlap A i j k) := by
  unfold tripleOverlap
  exact (chartTransition_continuousOn A j k).isOpen_inter_preimage
    (chartOverlap_isOpen A j k) (chartOverlap_isOpen A i j)

theorem tripleOverlap_subset_chartOverlap
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j k : A.index) :
    tripleOverlap A i j k ⊆ chartOverlap A i k := by
  intro z hz
  let ci := A.chart i
  let cj := A.chart j
  let ck := A.chart k
  have hxj : ck.fromComplex z ∈ cj.domain := hz.1.2
  have hsource :
      cj.fromComplex (cj.toComplex (ck.fromComplex z)) =
        ck.fromComplex z :=
    cj.left_inv hxj
  refine ⟨hz.1.1, ?_⟩
  change ck.fromComplex z ∈ ci.domain
  have hi :
      cj.fromComplex (cj.toComplex (ck.fromComplex z)) ∈ ci.domain := hz.2.2
  rw [← hsource]
  exact hi

theorem chartTransition_differentiableOn
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) :
    DifferentiableOn ℂ (chartTransition A i j) (chartOverlap A i j) :=
  A.transition_is_differentiableOn j i

theorem chartTransition_fderiv_continuousOn_real
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j : A.index) :
    ContinuousOn
      (fun z => fderiv ℝ (chartTransition A i j) z)
      (chartOverlap A i j) := by
  have hcont :
      ContDiffOn ℂ ∞ (chartTransition A i j) (chartOverlap A i j) :=
    (chartTransition_differentiableOn A i j).contDiffOn
      (chartOverlap_isOpen A i j)
  have hcomplex :
      ContinuousOn (fderiv ℂ (chartTransition A i j))
        (chartOverlap A i j) :=
    hcont.continuousOn_fderiv_of_isOpen
      (chartOverlap_isOpen A i j) (by simp)
  have hrestrict :
      Continuous
        (ContinuousLinearMap.restrictScalars ℝ :
          (ℂ →L[ℂ] ℂ) → (ℂ →L[ℝ] ℂ)) :=
    ContinuousLinearMap.continuous_restrictScalars ℝ
  have hrestricted :
      ContinuousOn
        (fun z =>
          (fderiv ℂ (chartTransition A i j) z).restrictScalars ℝ)
        (chartOverlap A i j) :=
    hrestrict.comp_continuousOn hcomplex
  refine hrestricted.congr ?_
  intro z hz
  exact ((chartTransition_differentiableOn A i j).differentiableAt
    ((chartOverlap_isOpen A i j).mem_nhds hz)).fderiv_restrictScalars ℝ

theorem chartTransition_comp_on_tripleOverlap
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) (i j k : A.index) {z : ℂ}
    (hz : z ∈ tripleOverlap A i j k) :
    chartTransition A i k z =
      chartTransition A i j (chartTransition A j k z) := by
  let ci := A.chart i
  let cj := A.chart j
  let ck := A.chart k
  have hzk : z ∈ ck.range := hz.1.1
  have hxj : ck.fromComplex z ∈ cj.domain := hz.1.2
  have hsource :
      cj.fromComplex (cj.toComplex (ck.fromComplex z)) =
        ck.fromComplex z :=
    cj.left_inv hxj
  unfold chartTransition
  change ci.toComplex (ck.fromComplex z) =
    ci.toComplex (cj.fromComplex (cj.toComplex (ck.fromComplex z)))
  rw [hsource]

end ComplexAtlas

/-- A regularity enhancement of a concrete atlas for which the real
derivative of every transition is continuous on its genuine overlap.

This is the first constructive regularity layer beyond the bare
DifferentiableOn atlas: it is strong enough to make the fderivative field
strongly measurable after restricting to an overlap, while still leaving
measure transport and Beltrami compatibility as explicit analytic input.
-/
structure C1ComplexAtlas
    (X : Type u) [TopologicalSpace X] where
  atlas : ComplexAtlas X
  transition_fderiv_continuousOn : ∀ i j,
    ContinuousOn
      (fun z => fderiv ℝ (ComplexAtlas.chartTransition atlas i j) z)
      (ComplexAtlas.chartOverlap atlas i j)

noncomputable def ComplexAtlas.toC1ComplexAtlas
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) : C1ComplexAtlas X where
  atlas := A
  transition_fderiv_continuousOn :=
    ComplexAtlas.chartTransition_fderiv_continuousOn_real A

namespace C1ComplexAtlas

theorem transition_fderiv_aestronglyMeasurable_on_overlap
    {X : Type u} [TopologicalSpace X]
    (A : C1ComplexAtlas X) (measure : A.atlas.index → Measure ℂ)
    (i j : A.atlas.index) :
    AEStronglyMeasurable
      (fun z => fderiv ℝ (ComplexAtlas.chartTransition A.atlas i j) z)
      (ComplexAtlas.overlapMeasure A.atlas measure i j) :=
  (A.transition_fderiv_continuousOn i j).aestronglyMeasurable
    (ComplexAtlas.chartOverlap_isOpen A.atlas i j).measurableSet

end C1ComplexAtlas

/-- Local a.e. Beltrami differential data tied to a concrete complex atlas.

The fields are deliberately local to chart overlaps. The global
measurable-Riemann-mapping and integrability theorems are not hidden in this
definition; an actual construction must provide the displayed measurable and
a.e. compatibility data.
-/
structure LocalAEBeltramiDifferentialChartSystem
    {X : Type u} [TopologicalSpace X]
    (A : ComplexAtlas X) where
  measure : A.index → Measure ℂ
  coefficient : ∀ i, BeltramiCoefficient (measure i)
  differential : A.index → A.index → ℂ → ℂ →L[ℝ] ℂ
  transition_aemeasurable : ∀ i j,
    AEMeasurable (ComplexAtlas.chartTransition A i j)
      (ComplexAtlas.overlapMeasure A measure i j)
  transition_absolutelyContinuous_on_tripleOverlap : ∀ i j k,
    Measure.map (ComplexAtlas.chartTransition A j k)
        (ComplexAtlas.tripleOverlapMeasure A measure i j k) ≪
      ComplexAtlas.overlapMeasure A measure i j
  differential_aestronglyMeasurable : ∀ i j,
    AEStronglyMeasurable (differential i j) (measure j)
  coefficient_compatible_ae : ∀ i j,
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A measure i j,
      coefficient j z =
        differentialBeltramiTransform
          (coefficient i (ComplexAtlas.chartTransition A i j z))
          (differential i j z)
  differential_eq_fderiv_ae : ∀ i j,
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A measure i j,
      differential i j z =
        fderiv ℝ (ComplexAtlas.chartTransition A i j) z

/-- Minimal data from which the differential field of a local system can be
constructed rather than postulated.

The generated field is the indicator of the real derivative on the chart
overlap and zero outside it. The two genuinely analytic inputs that are not
formal consequences of C1ComplexAtlas are retained explicitly:
absolute continuity of the transported triple-overlap measure and the
Beltrami coefficient compatibility with the derivative.
-/
structure C1LocalBeltramiInput
    {X : Type u} [TopologicalSpace X]
    (A : C1ComplexAtlas X) where
  measure : A.atlas.index → Measure ℂ
  coefficient : ∀ i, BeltramiCoefficient (measure i)
  transition_absolutelyContinuous_on_tripleOverlap : ∀ i j k,
    Measure.map (ComplexAtlas.chartTransition A.atlas j k)
        (ComplexAtlas.tripleOverlapMeasure A.atlas measure i j k) ≪
      ComplexAtlas.overlapMeasure A.atlas measure i j
  coefficient_compatible_ae_with_fderiv : ∀ i j,
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A.atlas measure i j,
      coefficient j z =
          differentialBeltramiTransform
            (coefficient i (ComplexAtlas.chartTransition A.atlas i j z))
          (fderiv ℝ (ComplexAtlas.chartTransition A.atlas i j) z)

structure DominatedC1LocalBeltramiInput
    {X : Type u} [TopologicalSpace X]
    (A : C1ComplexAtlas X)
    extends C1LocalBeltramiInput A where
  majorant : A.atlas.index → ℂ → ℝ
  majorant_integrable : ∀ i, Integrable (majorant i) (measure i)
  coefficient_norm_le_majorant : ∀ i,
    ∀ᵐ z ∂measure i, ‖coefficient i z‖ ≤ majorant i z

namespace DominatedC1LocalBeltramiInput

theorem coefficient_integrable
    {X : Type u} [TopologicalSpace X]
    {A : C1ComplexAtlas X}
    (I : DominatedC1LocalBeltramiInput A) (i : A.atlas.index) :
    Integrable (I.coefficient i) (I.measure i) := by
  exact BeltramiCoefficient.integrable_of_majorant
    (I.coefficient i) (I.majorant_integrable i)
    (I.coefficient_norm_le_majorant i)

theorem coefficient_integrable_on_overlap
    {X : Type u} [TopologicalSpace X]
    {A : C1ComplexAtlas X}
    (I : DominatedC1LocalBeltramiInput A)
    (i j : A.atlas.index) :
    Integrable (I.coefficient j)
      (ComplexAtlas.overlapMeasure A.atlas I.measure i j) := by
  unfold ComplexAtlas.overlapMeasure
  exact (I.coefficient_integrable j).integrableOn

end DominatedC1LocalBeltramiInput

structure FiniteMeasureC1LocalBeltramiInput
    {X : Type u} [TopologicalSpace X]
    (A : C1ComplexAtlas X)
    extends C1LocalBeltramiInput A where
  measure_isFinite : ∀ i, IsFiniteMeasure (measure i)

namespace FiniteMeasureC1LocalBeltramiInput

theorem coefficient_integrable
    {X : Type u} [TopologicalSpace X]
    {A : C1ComplexAtlas X}
    (I : FiniteMeasureC1LocalBeltramiInput A) (i : A.atlas.index) :
    Integrable (I.coefficient i) (I.measure i) := by
  letI := I.measure_isFinite i
  exact BeltramiCoefficient.integrable (I.coefficient i)

theorem coefficient_integrable_on_overlap
    {X : Type u} [TopologicalSpace X]
    {A : C1ComplexAtlas X}
    (I : FiniteMeasureC1LocalBeltramiInput A)
    (i j : A.atlas.index) :
    Integrable (I.coefficient j)
      (ComplexAtlas.overlapMeasure A.atlas I.measure i j) := by
  letI := I.measure_isFinite j
  exact BeltramiCoefficient.integrable_restrict
    (I.coefficient j) (ComplexAtlas.chartOverlap A.atlas i j)

end FiniteMeasureC1LocalBeltramiInput

namespace C1LocalBeltramiInput

noncomputable def toLocal
    {X : Type u} [TopologicalSpace X]
    {A : C1ComplexAtlas X}
    (I : C1LocalBeltramiInput A) :
    LocalAEBeltramiDifferentialChartSystem A.atlas where
  measure := I.measure
  coefficient := I.coefficient
  differential := fun i j =>
    (ComplexAtlas.chartOverlap A.atlas i j).indicator
      (fun z => fderiv ℝ (ComplexAtlas.chartTransition A.atlas i j) z)
  transition_aemeasurable := by
    intro i j
    exact (ComplexAtlas.chartTransition_continuousOn A.atlas i j).aemeasurable
      (ComplexAtlas.chartOverlap_isOpen A.atlas i j).measurableSet
  transition_absolutelyContinuous_on_tripleOverlap :=
    I.transition_absolutelyContinuous_on_tripleOverlap
  differential_aestronglyMeasurable := by
    intro i j
    rw [aestronglyMeasurable_indicator_iff
      (ComplexAtlas.chartOverlap_isOpen A.atlas i j).measurableSet]
    exact A.transition_fderiv_aestronglyMeasurable_on_overlap
      I.measure i j
  coefficient_compatible_ae := by
    intro i j
    filter_upwards [I.coefficient_compatible_ae_with_fderiv i j,
      self_mem_ae_restrict
        (ComplexAtlas.chartOverlap_isOpen A.atlas i j).measurableSet] with
      z hz hmem
    simpa [hmem] using hz
  differential_eq_fderiv_ae := by
    intro i j
    filter_upwards [self_mem_ae_restrict
      (ComplexAtlas.chartOverlap_isOpen A.atlas i j).measurableSet] with
      z hmem
    simp [hmem]

end C1LocalBeltramiInput

namespace LocalAEBeltramiDifferentialChartSystem

theorem tripleOverlapMeasure_le_overlapMeasure_source
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    ComplexAtlas.tripleOverlapMeasure A C.measure i j k ≤
      ComplexAtlas.overlapMeasure A C.measure j k := by
  unfold ComplexAtlas.tripleOverlapMeasure ComplexAtlas.overlapMeasure
  exact Measure.restrict_mono_set _ (by
    intro z hz
    exact hz.1)

theorem tripleOverlapMeasure_le_overlapMeasure_target
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    ComplexAtlas.tripleOverlapMeasure A C.measure i j k ≤
      ComplexAtlas.overlapMeasure A C.measure i k := by
  unfold ComplexAtlas.tripleOverlapMeasure ComplexAtlas.overlapMeasure
  exact Measure.restrict_mono_set _
    (ComplexAtlas.tripleOverlap_subset_chartOverlap A i j k)

theorem transition_aemeasurable_on_tripleOverlap
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    AEMeasurable (ComplexAtlas.chartTransition A j k)
      (ComplexAtlas.tripleOverlapMeasure A C.measure i j k) :=
  (C.transition_aemeasurable j k).mono_measure
    (tripleOverlapMeasure_le_overlapMeasure_source C i j k)

theorem transition_differentiableOn
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j : A.index) :
    DifferentiableOn ℂ (ComplexAtlas.chartTransition A i j)
      (ComplexAtlas.chartOverlap A i j) :=
  ComplexAtlas.chartTransition_differentiableOn A i j

theorem coefficient_compatible_ae_with_fderiv
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j : A.index) :
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A C.measure i j,
      C.coefficient j z =
        differentialBeltramiTransform
          (C.coefficient i (ComplexAtlas.chartTransition A i j z))
          (fderiv ℝ (ComplexAtlas.chartTransition A i j) z) := by
  filter_upwards [C.coefficient_compatible_ae i j,
    C.differential_eq_fderiv_ae i j] with z hz hderiv
  rw [← hderiv]
  exact hz

theorem differential_comp_ae_on_tripleOverlap
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    ∀ᵐ z ∂ComplexAtlas.tripleOverlapMeasure A C.measure i j k,
      C.differential i k z =
        (C.differential i j
          (ComplexAtlas.chartTransition A j k z)).comp
            (C.differential j k z) := by
  have h_outer_map :
      ∀ᵐ y ∂Measure.map (ComplexAtlas.chartTransition A j k)
          (ComplexAtlas.tripleOverlapMeasure A C.measure i j k),
        C.differential i j y =
          fderiv ℝ (ComplexAtlas.chartTransition A i j) y :=
    (C.transition_absolutelyContinuous_on_tripleOverlap i j k).ae_le
      (C.differential_eq_fderiv_ae i j)
  have h_outer_pull :
      ∀ᵐ z ∂ComplexAtlas.tripleOverlapMeasure A C.measure i j k,
        C.differential i j (ComplexAtlas.chartTransition A j k z) =
          fderiv ℝ (ComplexAtlas.chartTransition A i j)
            (ComplexAtlas.chartTransition A j k z) :=
    ae_of_ae_map (C.transition_aemeasurable_on_tripleOverlap i j k)
      h_outer_map
  have h_inner := ae_mono
    (tripleOverlapMeasure_le_overlapMeasure_source C i j k)
    (C.differential_eq_fderiv_ae j k)
  have h_target := ae_mono
    (tripleOverlapMeasure_le_overlapMeasure_target C i j k)
    (C.differential_eq_fderiv_ae i k)
  have hmem :
      ∀ᵐ z ∂ComplexAtlas.tripleOverlapMeasure A C.measure i j k,
        z ∈ ComplexAtlas.tripleOverlap A i j k :=
    self_mem_ae_restrict (ComplexAtlas.tripleOverlap_isOpen A i j k).measurableSet
  filter_upwards [h_outer_pull, h_inner, h_target, hmem] with
    z houter hinner htarget hz
  have houter_diff :
      DifferentiableAt ℝ (ComplexAtlas.chartTransition A i j)
        (ComplexAtlas.chartTransition A j k z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp
      ((C.transition_differentiableOn i j).differentiableAt
        ((ComplexAtlas.chartOverlap_isOpen A i j).mem_nhds hz.2))).1
  have hinner_diff :
      DifferentiableAt ℝ (ComplexAtlas.chartTransition A j k) z :=
    (differentiableAt_complex_iff_differentiableAt_real.mp
      ((C.transition_differentiableOn j k).differentiableAt
        ((ComplexAtlas.chartOverlap_isOpen A j k).mem_nhds hz.1))).1
  rw [htarget, houter, hinner]
  have hfun :
      ComplexAtlas.chartTransition A i k =ᶠ[𝓝 z]
        (fun y => ComplexAtlas.chartTransition A i j
          (ComplexAtlas.chartTransition A j k y)) := by
    filter_upwards [
      (ComplexAtlas.tripleOverlap_isOpen A i j k).eventually_mem hz] with
      y hy
    exact ComplexAtlas.chartTransition_comp_on_tripleOverlap A i j k hy
  have hderiv :
      HasFDerivAt
        (fun y => ComplexAtlas.chartTransition A i j
          (ComplexAtlas.chartTransition A j k y))
        ((fderiv ℝ (ComplexAtlas.chartTransition A i j)
            (ComplexAtlas.chartTransition A j k z)).comp
          (fderiv ℝ (ComplexAtlas.chartTransition A j k) z)) z :=
    houter_diff.hasFDerivAt.comp z hinner_diff.hasFDerivAt
  exact (hderiv.congr_of_eventuallyEq hfun).fderiv

theorem differential_comp_ae_on_overlap
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A C.measure i k,
      z ∈ ComplexAtlas.tripleOverlap A i j k →
        C.differential i k z =
          (C.differential i j
            (ComplexAtlas.chartTransition A j k z)).comp
            (C.differential j k z) := by
  have hlocal :
      ∀ᵐ z ∂(ComplexAtlas.overlapMeasure A C.measure i k).restrict
          (ComplexAtlas.tripleOverlap A i j k),
        C.differential i k z =
          (C.differential i j
            (ComplexAtlas.chartTransition A j k z)).comp
            (C.differential j k z) := by
    have heq :
        (ComplexAtlas.overlapMeasure A C.measure i k).restrict
            (ComplexAtlas.tripleOverlap A i j k) =
          ComplexAtlas.tripleOverlapMeasure A C.measure i j k := by
      unfold ComplexAtlas.overlapMeasure ComplexAtlas.tripleOverlapMeasure
      exact Measure.restrict_restrict_of_subset
        (ComplexAtlas.tripleOverlap_subset_chartOverlap A i j k)
    rw [heq]
    exact C.differential_comp_ae_on_tripleOverlap i j k
  exact ae_imp_of_ae_restrict hlocal

theorem differential_comp_on_tripleOverlap
    {X : Type u} [TopologicalSpace X]
    {A : ComplexAtlas X}
    (C : LocalAEBeltramiDifferentialChartSystem A)
    (i j k : A.index) :
    ∀ᵐ z ∂ComplexAtlas.overlapMeasure A C.measure i k,
      z ∈ ComplexAtlas.tripleOverlap A i j k →
        C.differential i k z =
          (C.differential i j
            (ComplexAtlas.chartTransition A j k z)).comp
            (C.differential j k z) :=
  C.differential_comp_ae_on_overlap i j k

end LocalAEBeltramiDifferentialChartSystem

/-! ### A concrete one-chart regression model -/

noncomputable def complexPlaneLocalAEBeltramiDifferentialChartSystem
    (m : Measure ℂ) :
    LocalAEBeltramiDifferentialChartSystem complexPlaneAtlas where
  measure := fun _ => m
  coefficient := fun _ => zeroBeltramiCoefficient m
  differential := fun _ _ _ => ContinuousLinearMap.id ℝ ℂ
  transition_aemeasurable := by
    intro i j
    exact measurable_id.aemeasurable
  transition_absolutelyContinuous_on_tripleOverlap := by
    intro i j k
    cases i
    cases j
    cases k
    have hle :
        m.restrict (ComplexAtlas.tripleOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit) ≤
          m.restrict (ComplexAtlas.chartOverlap complexPlaneAtlas
            PUnit.unit PUnit.unit) :=
      Measure.restrict_mono_set _
        (ComplexAtlas.tripleOverlap_subset_chartOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit)
    change Measure.map id
        (m.restrict (ComplexAtlas.tripleOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit)) ≪
      m.restrict (ComplexAtlas.chartOverlap complexPlaneAtlas
        PUnit.unit PUnit.unit)
    rw [Measure.map_id]
    exact hle.absolutelyContinuous
  differential_aestronglyMeasurable := by
    intro i j
    exact aestronglyMeasurable_const
  coefficient_compatible_ae := by
    intro i j
    filter_upwards [] with z
    simp [ComplexAtlas.chartTransition, differentialBeltramiTransform,
      complexDerivativePart, antiComplexDerivativePart]
  differential_eq_fderiv_ae := by
    intro i j
    filter_upwards [] with z
    change (ContinuousLinearMap.id ℝ ℂ) = fderiv ℝ id z
    symm
    exact fderiv_id
@[simp] theorem complexPlaneLocalAEBeltramiDifferentialChartSystem_transition
    (m : Measure ℂ) (i j : complexPlaneAtlas.index) :
    ComplexAtlas.chartTransition complexPlaneAtlas i j = id := by
  cases i
  cases j
  funext z
  rfl

noncomputable def complexPlaneC1Atlas : C1ComplexAtlas ℂ :=
  ComplexAtlas.toC1ComplexAtlas complexPlaneAtlas

noncomputable def complexPlaneGeneratedC1Input
    (m : Measure ℂ) :
    C1LocalBeltramiInput complexPlaneC1Atlas where
  measure := fun _ => m
  coefficient := fun _ => zeroBeltramiCoefficient m
  transition_absolutelyContinuous_on_tripleOverlap := by
    intro i j k
    cases i
    cases j
    cases k
    have hle :
        m.restrict (ComplexAtlas.tripleOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit) ≤
          m.restrict (ComplexAtlas.chartOverlap complexPlaneAtlas
            PUnit.unit PUnit.unit) :=
      Measure.restrict_mono_set _
        (ComplexAtlas.tripleOverlap_subset_chartOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit)
    change Measure.map id
        (m.restrict (ComplexAtlas.tripleOverlap complexPlaneAtlas
          PUnit.unit PUnit.unit PUnit.unit)) ≪
      m.restrict (ComplexAtlas.chartOverlap complexPlaneAtlas
        PUnit.unit PUnit.unit)
    rw [Measure.map_id]
    exact hle.absolutelyContinuous
  coefficient_compatible_ae_with_fderiv := by
    intro i j
    cases i
    cases j
    filter_upwards [] with z
    change 0 =
      differentialBeltramiTransform 0 (fderiv ℝ id z)
    simp [differentialBeltramiTransform, complexDerivativePart,
      antiComplexDerivativePart]

noncomputable def complexPlaneFiniteMeasureC1Input
    {m : Measure ℂ} [IsFiniteMeasure m] :
    FiniteMeasureC1LocalBeltramiInput complexPlaneC1Atlas where
  toC1LocalBeltramiInput := complexPlaneGeneratedC1Input m
  measure_isFinite := by
    intro i
    cases i
    change IsFiniteMeasure m
    infer_instance

noncomputable def complexPlaneDominatedC1Input
    (m : Measure ℂ) :
    DominatedC1LocalBeltramiInput complexPlaneC1Atlas where
  toC1LocalBeltramiInput := complexPlaneGeneratedC1Input m
  majorant := fun _ _ => 0
  majorant_integrable := by
    intro i
    cases i
    change Integrable (fun _ : ℂ => (0 : ℝ)) m
    exact integrable_zero ℂ ℝ m
  coefficient_norm_le_majorant := by
    intro i
    cases i
    filter_upwards [] with z
    change ‖(zeroBeltramiCoefficient m) z‖ ≤ 0
    simp

noncomputable def complexPlaneGeneratedLocalAEBeltramiDifferentialChartSystem
    (m : Measure ℂ) :
    LocalAEBeltramiDifferentialChartSystem complexPlaneAtlas :=
  (complexPlaneGeneratedC1Input m).toLocal

/-!
The family-level wrapper makes the intended dependency explicit: each actual
fibre carries its own local chart system. No global family trivialization is
assumed here; that remains the next analytic-family bridge.
-/

structure FamilyLocalAEBeltramiData
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : ComplexSurfaceFamily.Family S B) where
  fibre : ∀ b,
    letI : TopologicalSpace (F.fiber b).carrier := (F.fiber b).topology
    LocalAEBeltramiDifferentialChartSystem
      (F.fiber b).surface.atlas

namespace FamilyLocalAEBeltramiData

end FamilyLocalAEBeltramiData

noncomputable def constantComplexPlaneFamilyLocalAEBeltramiData
    (B : Type w) [TopologicalSpace B] (m : Measure ℂ) :
    FamilyLocalAEBeltramiData
      (ComplexSurfaceFamily.constantComplexPlaneFamily B) where
  fibre := by
    intro b
    letI : TopologicalSpace
        ((ComplexSurfaceFamily.constantComplexPlaneFamily B).fiber b).carrier :=
      ((ComplexSurfaceFamily.constantComplexPlaneFamily B).fiber b).topology
    exact complexPlaneLocalAEBeltramiDifferentialChartSystem m

end MathlibFormal
end Teichmuller
