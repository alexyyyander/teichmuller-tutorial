import Teichmuller.ModularMathlib
import Teichmuller.MathlibComplex
import Teichmuller.MathlibFiberBundle
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.LocallyConstant.Basic

namespace Teichmuller

open Module
open scoped Topology

/-!
Concrete lattice-quotient data for the genus-one part of the Teichmüller route.

For a point tau of the upper half-plane, the two periods 1 and tau span a
rank-two additive lattice in the complex plane.  The quotient of the plane by
this lattice is the algebraic and topological carrier of the corresponding
complex torus.  This file does not yet pretend that the quotient has a
finished atlas; it makes the period parameter and quotient relation explicit,
so the next chart construction has a genuine object to act on.
-/

abbrev ComplexTorusParameter := MathlibUpperHalfPlane

/-- The two-period integer span attached to an upper-half-plane parameter. -/
noncomputable def complexTorusLattice (τ : ComplexTorusParameter) : Submodule ℤ ℂ :=
  Submodule.span ℤ
    (Set.range (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (τ : ℂ)))

@[simp]
theorem one_mem_complexTorusLattice (τ : ComplexTorusParameter) :
    (1 : ℂ) ∈ complexTorusLattice τ := by
  apply Submodule.subset_span
  exact ⟨0, by simp [complexTorusLattice]⟩

@[simp]
theorem tau_mem_complexTorusLattice (τ : ComplexTorusParameter) :
    (τ : ℂ) ∈ complexTorusLattice τ := by
  apply Submodule.subset_span
  exact ⟨1, by simp [complexTorusLattice]⟩

/-- The additive-group quotient of the plane by its two periods. -/
noncomputable abbrev ComplexTorus (τ : ComplexTorusParameter) :=
  ℂ ⧸ (complexTorusLattice τ).toAddSubgroup

/-- The quotient map from the universal cover to the torus carrier. -/
noncomputable def complexTorusMk (τ : ComplexTorusParameter) : ℂ → ComplexTorus τ :=
  QuotientAddGroup.mk' (complexTorusLattice τ).toAddSubgroup

@[simp]
theorem complexTorusMk_zero (τ : ComplexTorusParameter) :
    complexTorusMk τ 0 = 0 := by
  rfl

@[simp]
theorem complexTorusMk_add (τ : ComplexTorusParameter) (z w : ℂ) :
    complexTorusMk τ (z + w) =
      complexTorusMk τ z + complexTorusMk τ w := by
  rfl

@[simp]
theorem complexTorusMk_sub (τ : ComplexTorusParameter) (z w : ℂ) :
    complexTorusMk τ (z - w) =
      complexTorusMk τ z - complexTorusMk τ w := by
  rfl

@[simp]
theorem complexTorusMk_eq_zero_iff (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMk τ z = 0 ↔ z ∈ complexTorusLattice τ := by
  change ((z : ComplexTorus τ) = 0) ↔ z ∈ complexTorusLattice τ
  simpa using (QuotientAddGroup.eq_zero_iff z)

theorem complexTorusMk_eq_iff (τ : ComplexTorusParameter) (z w : ℂ) :
    complexTorusMk τ z = complexTorusMk τ w ↔
      z - w ∈ complexTorusLattice τ := by
  change ((z : ComplexTorus τ) = (w : ComplexTorus τ)) ↔
    z - w ∈ complexTorusLattice τ
  simpa using (QuotientAddGroup.eq_iff_sub_mem (N := (complexTorusLattice τ).toAddSubgroup))

theorem complexTorus_parameter_im_pos (τ : ComplexTorusParameter) :
    0 < (τ : ℂ).im :=
  τ.im_pos

private theorem complexTorus_periods_linearIndependent_aux
    (τ : ComplexTorusParameter) :
    LinearIndependent ℝ
      (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (τ : ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hreal := congrArg Complex.re hc
  have himag := congrArg Complex.im hc
  simp [Fin.sum_univ_two, smul_eq_mul] at hreal himag
  have hc1 : c 1 = 0 := by
    rcases himag with h | h
    · exact h
    · exact False.elim ((ne_of_gt τ.im_pos) h)
  have hc0 : c 0 = 0 := by
    simpa [hc1] using hreal
  fin_cases i
  · simpa using hc0
  · simpa using hc1

theorem complexTorus_periods_linearIndependent
    (τ : ComplexTorusParameter) :
    LinearIndependent ℝ
      (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (τ : ℂ)) :=
  complexTorus_periods_linearIndependent_aux τ

theorem complexTorus_periods_span_real_top
    (τ : ComplexTorusParameter) :
    Submodule.span ℝ
        (Set.range (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (τ : ℂ))) = ⊤ := by
  exact (complexTorus_periods_linearIndependent τ).span_eq_top_of_card_eq_finrank
    (by simp [Complex.finrank_real_complex])

theorem complexTorus_lattice_spans_real_plane
    (τ : ComplexTorusParameter) :
    Submodule.span ℝ ((complexTorusLattice τ : Set ℂ)) = ⊤ := by
  rw [complexTorusLattice]
  rw [Submodule.span_span_of_tower]
  exact complexTorus_periods_span_real_top τ

/-- The period vectors form a genuine real basis of the universal cover. -/
noncomputable def complexTorusPeriodBasis (τ : ComplexTorusParameter) :
    Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank
    (complexTorus_periods_linearIndependent τ)
    (by simp [Complex.finrank_real_complex])

@[simp]
theorem complexTorusPeriodBasis_apply (τ : ComplexTorusParameter) (i : Fin 2) :
    complexTorusPeriodBasis τ i =
      (if i = 0 then (1 : ℂ) else (τ : ℂ)) := by
  simp [complexTorusPeriodBasis]

theorem complexTorusLattice_eq_periodBasis_span (τ : ComplexTorusParameter) :
    complexTorusLattice τ =
      Submodule.span ℤ (Set.range (complexTorusPeriodBasis τ)) := by
  simp [complexTorusLattice, complexTorusPeriodBasis]

instance complexTorusLattice_discreteTopology (τ : ComplexTorusParameter) :
    DiscreteTopology (complexTorusLattice τ) := by
  rw [complexTorusLattice_eq_periodBasis_span]
  infer_instance

instance complexTorusLattice_addSubgroup_discreteTopology
    (τ : ComplexTorusParameter) :
    DiscreteTopology (complexTorusLattice τ).toAddSubgroup := by
  rw [complexTorusLattice_eq_periodBasis_span]
  infer_instance

instance complexTorusLattice_set_discreteTopology
    (τ : ComplexTorusParameter) :
    DiscreteTopology ((complexTorusLattice τ).toAddSubgroup : Set ℂ) := by
  let f : ((complexTorusLattice τ).toAddSubgroup : Set ℂ) → complexTorusLattice τ :=
    fun x => ⟨x, x.property⟩
  apply DiscreteTopology.of_continuous_injective (β := complexTorusLattice τ) (f := f)
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => x.property)
  · intro x y h
    exact Subtype.ext (congrArg Subtype.val h)

instance complexTorusLattice_submodule_set_discreteTopology
    (τ : ComplexTorusParameter) :
    DiscreteTopology (complexTorusLattice τ : Set ℂ) := by
  let f : {x : ℂ // x ∈ complexTorusLattice τ} → complexTorusLattice τ :=
    fun x => ⟨x, x.property⟩
  apply DiscreteTopology.of_continuous_injective (β := complexTorusLattice τ) (f := f)
  · exact Continuous.subtype_mk continuous_subtype_val (fun x => x.property)
  · intro x y h
    exact Subtype.ext (congrArg Subtype.val h)

noncomputable instance complexTorusLattice_isZLattice (τ : ComplexTorusParameter) :
    IsZLattice ℝ (complexTorusLattice τ) where
  span_top := complexTorus_lattice_spans_real_plane τ

theorem complexTorusMk_continuous (τ : ComplexTorusParameter) :
    Continuous (complexTorusMk τ) := by
  exact QuotientAddGroup.continuous_mk

/-! ### The quotient map as the topological covering behind the atlas

The lattice is not merely a period relation: its discreteness makes the
quotient map a covering map.  This is the topological theorem from which local
complex charts can be extracted.  We deliberately keep the covering statement
separate from the later holomorphic transition calculation.
-/

theorem complexTorusMk_isQuotientCoveringMap (τ : ComplexTorusParameter) :
    IsAddQuotientCoveringMap (complexTorusMk τ)
      (complexTorusLattice τ).toAddSubgroup := by
  apply AddSubgroup.isAddQuotientCoveringMap_of_comm
    (complexTorusLattice τ).toAddSubgroup
  exact DiscreteTopology.isDiscrete

theorem complexTorusMk_isCoveringMap (τ : ComplexTorusParameter) :
    IsCoveringMap (complexTorusMk τ) :=
  (complexTorusMk_isQuotientCoveringMap τ).isCoveringMap

theorem complexTorusMk_isLocalHomeomorph (τ : ComplexTorusParameter) :
    IsLocalHomeomorph (complexTorusMk τ) :=
  (complexTorusMk_isQuotientCoveringMap τ).isCoveringMap.isLocalHomeomorph

theorem complexTorus_has_local_complex_coordinate
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    ∃ e : OpenPartialHomeomorph (ComplexTorus τ) ℂ,
      x ∈ e.source ∧ IsOpen e.source ∧ IsOpen e.target := by
  obtain ⟨z, hz⟩ :=
    (QuotientAddGroup.mk'_surjective (complexTorusLattice τ).toAddSubgroup x)
  obtain ⟨e, hz_source, he⟩ := complexTorusMk_isLocalHomeomorph τ z
  refine ⟨e.symm, ?_, e.symm.open_source, e.symm.open_target⟩
  change x ∈ e.target
  rw [← hz]
  change complexTorusMk τ z ∈ e.target
  rw [he]
  exact e.map_source hz_source

/-! A local coordinate is useful only when its lift property is retained.
The next structure packages the open partial homeomorphism together with
that section equation, so later atlas construction does not have to recover
the quotient calculation from an existential proof. -/

structure ComplexTorusLocalChart (τ : ComplexTorusParameter) where
  chart : OpenPartialHomeomorph (ComplexTorus τ) ℂ
  section_eq : ∀ x, x ∈ chart.source → complexTorusMk τ (chart x) = x

theorem complexTorus_has_local_complex_coordinate_with_section
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    ∃ c : ComplexTorusLocalChart τ,
      x ∈ c.chart.source ∧ IsOpen c.chart.source ∧ IsOpen c.chart.target := by
  obtain ⟨z, hz⟩ :=
    (QuotientAddGroup.mk'_surjective (complexTorusLattice τ).toAddSubgroup x)
  obtain ⟨e, hz_source, he⟩ := complexTorusMk_isLocalHomeomorph τ z
  let c : ComplexTorusLocalChart τ :=
    { chart := e.symm
      section_eq := by
        intro y hy
        change complexTorusMk τ (e.symm y) = y
        rw [he]
        exact e.right_inv hy }
  refine ⟨c, ?_, c.chart.open_source, c.chart.open_target⟩
  change x ∈ e.target
  rw [← hz]
  change complexTorusMk τ z ∈ e.target
  rw [he]
  exact e.map_source hz_source

namespace ComplexTorusLocalChart

theorem section_eq_at {τ : ComplexTorusParameter} (c : ComplexTorusLocalChart τ)
    {x : ComplexTorus τ} (hx : x ∈ c.chart.source) :
    complexTorusMk τ (c.chart x) = x :=
  c.section_eq x hx

/-- Turn a quotient local chart into the concrete chart record used by the
    complex-atlas layer. -/
noncomputable def toComplexChart {τ : ComplexTorusParameter} (c : ComplexTorusLocalChart τ) :
    MathlibFormal.ComplexChart (ComplexTorus τ) where
  domain := c.chart.source
  range := c.chart.target
  domain_open := c.chart.open_source
  range_open := c.chart.open_target
  toComplex := c.chart
  fromComplex := c.chart.symm
  maps_into := fun x hx => c.chart.map_source hx
  inverse_into := fun z hz => c.chart.map_target hz
  left_inv := fun x hx => c.chart.left_inv hx
  right_inv := fun z hz => c.chart.right_inv hz
  continuous_toComplex := c.chart.continuousOn
  continuous_fromComplex := c.chart.continuousOn_symm

@[simp] theorem toComplexChart_domain {τ : ComplexTorusParameter}
    (c : ComplexTorusLocalChart τ) : c.toComplexChart.domain = c.chart.source := rfl

@[simp] theorem toComplexChart_range {τ : ComplexTorusParameter}
    (c : ComplexTorusLocalChart τ) : c.toComplexChart.range = c.chart.target := rfl

theorem transition_difference_mem_lattice {τ : ComplexTorusParameter}
    (c₁ c₂ : ComplexTorusLocalChart τ) {z : ℂ}
    (hz : z ∈ MathlibFormal.ComplexChart.overlap
      c₁.toComplexChart c₂.toComplexChart) :
    c₂.chart (c₁.chart.symm z) - z ∈ complexTorusLattice τ := by
  apply (complexTorusMk_eq_iff τ
    (c₂.chart (c₁.chart.symm z)) z).mp
  have hz₁ : c₁.chart.symm z ∈ c₁.chart.source :=
    c₁.chart.map_target hz.1
  have h₁z := c₁.section_eq (c₁.chart.symm z) hz₁
  have h₂z := c₂.section_eq (c₁.chart.symm z) hz.2
  rw [h₂z, ← h₁z, c₁.chart.right_inv hz.1]

theorem transition_differentiableOn {τ : ComplexTorusParameter}
    (c₁ c₂ : ComplexTorusLocalChart τ) :
    DifferentiableOn ℂ
      (MathlibFormal.ComplexChart.transitionMap
        c₁.toComplexChart c₂.toComplexChart)
      (MathlibFormal.ComplexChart.overlap c₁.toComplexChart c₂.toComplexChart) := by
  let S : Set ℂ := MathlibFormal.ComplexChart.overlap
    c₁.toComplexChart c₂.toComplexChart
  let d : ℂ → ℂ := fun z => c₂.chart (c₁.chart.symm z) - z
  have hd_mem : Set.MapsTo d S (complexTorusLattice τ : Set ℂ) := by
    intro z hz
    exact transition_difference_mem_lattice c₁ c₂ hz
  have hd_cont : ContinuousOn d S := by
    dsimp [d]
    have hcomp : ContinuousOn (c₂.chart ∘ c₁.chart.symm) S :=
      c₂.chart.continuousOn.comp
        (c₁.chart.continuousOn_symm.mono fun z hz => hz.1)
        (fun z hz => hz.2)
    exact hcomp.sub continuousOn_id
  let d' : S → (complexTorusLattice τ : Set ℂ) :=
    hd_mem.restrict d S (complexTorusLattice τ : Set ℂ)
  have hd'_cont : Continuous d' := hd_cont.mapsToRestrict hd_mem
  have hd'_locallyConstant : IsLocallyConstant d' :=
    (IsLocallyConstant.iff_continuous d').2 hd'_cont
  intro z hz
  have hde : ∀ᶠ w in 𝓝[S] z, d w = d z := by
    rw [← eventually_nhds_subtype_iff S ⟨z, hz⟩ (fun w => d w = d z)]
    filter_upwards [hd'_locallyConstant.eventually_eq ⟨z, hz⟩] with w hw
    exact congrArg Subtype.val hw
  have htransition : ∀ᶠ w in 𝓝[S] z,
      MathlibFormal.ComplexChart.transitionMap
          c₁.toComplexChart c₂.toComplexChart w = w + d z := by
    filter_upwards [hde] with w hw
    have hw' : c₂.chart (c₁.chart.symm w) = w + d z := by
      have h := (sub_eq_iff_eq_add).mp hw
      simpa [add_comm] using h
    exact hw'
  have hbase : DifferentiableWithinAt ℂ (fun w : ℂ => w + d z) S z := by
    exact (differentiableAt_id.add (differentiableAt_const (c := d z))).differentiableWithinAt
  exact hbase.congr_of_eventuallyEq htransition
    (htransition.self_of_nhdsWithin hz)

end ComplexTorusLocalChart


/-! ### Assembly of the actual complex atlas

The local existence theorem is now used with choice only at the atlas
assembly boundary.  All compatibility proofs remain explicit and reduce to
the preceding local translation theorem. -/

noncomputable def complexTorusLocalChartAt
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    ComplexTorusLocalChart τ :=
  Classical.choose (complexTorus_has_local_complex_coordinate_with_section τ x)

theorem complexTorusLocalChartAt_mem
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    x ∈ (complexTorusLocalChartAt τ x).chart.source := by
  exact (Classical.choose_spec
    (complexTorus_has_local_complex_coordinate_with_section τ x)).1

theorem complexTorusLocalChartAt_domain_open
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    IsOpen (complexTorusLocalChartAt τ x).chart.source := by
  exact (complexTorusLocalChartAt τ x).chart.open_source

theorem complexTorusLocalChartAt_range_open
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    IsOpen (complexTorusLocalChartAt τ x).chart.target := by
  exact (complexTorusLocalChartAt τ x).chart.open_target

noncomputable def complexTorusAtlas (τ : ComplexTorusParameter) :
    MathlibFormal.ComplexAtlas (ComplexTorus τ) where
  index := ComplexTorus τ
  chart := fun x => (complexTorusLocalChartAt τ x).toComplexChart
  covers := fun x => ⟨x, complexTorusLocalChartAt_mem τ x⟩
  transition_holomorphic := by
    intro i j
    exact ComplexTorusLocalChart.transition_differentiableOn
      (complexTorusLocalChartAt τ i) (complexTorusLocalChartAt τ j)

noncomputable def complexTorusRiemannSurface (τ : ComplexTorusParameter) :
    MathlibFormal.ComplexRiemannSurface (ComplexTorus τ) where
  atlas := complexTorusAtlas τ

/-! ### A fixed topological reference torus

The real period basis gives a canonical linear comparison from the reference
parameter `i` to every `τ`.  This is only a topological marking: it is not a
complex-linear map unless the parameters agree.
-/

noncomputable def complexTorusBaseParameter : ComplexTorusParameter :=
  ⟨Complex.I, by simp⟩

noncomputable def complexTorusMarkingLinearEquiv
    (τ : ComplexTorusParameter) : ℂ ≃ₗ[ℝ] ℂ :=
  (complexTorusPeriodBasis complexTorusBaseParameter).equiv
    (complexTorusPeriodBasis τ) (Equiv.refl (Fin 2))

theorem complexTorusMarkingLinearEquiv_map_period
    (τ : ComplexTorusParameter) (i : Fin 2) :
    complexTorusMarkingLinearEquiv τ
        (complexTorusPeriodBasis complexTorusBaseParameter i) =
      complexTorusPeriodBasis τ i := by
  change (complexTorusPeriodBasis complexTorusBaseParameter).equiv
      (complexTorusPeriodBasis τ) (Equiv.refl (Fin 2))
      (complexTorusPeriodBasis complexTorusBaseParameter i) =
    complexTorusPeriodBasis τ i
  exact Module.Basis.equiv_apply
    (complexTorusPeriodBasis complexTorusBaseParameter)
    i (complexTorusPeriodBasis τ) (Equiv.refl (Fin 2))

theorem complexTorusMarkingLinearEquiv_apply
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMarkingLinearEquiv τ z =
      (z.re : ℂ) + (z.im : ℂ) * (τ : ℂ) := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  have h0 : complexTorusMarkingLinearEquiv τ (1 : ℂ) = 1 := by
    simpa [complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period τ (0 : Fin 2))
  have h1 : complexTorusMarkingLinearEquiv τ Complex.I = (τ : ℂ) := by
    simpa [complexTorusBaseParameter, complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period τ (1 : Fin 2))
  rw [h0, h1]
  simp

/-! The chosen marked period basis separates parameters already at one
reference lift.  This is the elementary rigidity statement behind the
fine-moduli direction: any later classification theorem must refine this
lift-level uniqueness rather than identify two different parameters while
preserving the marking. -/

theorem complexTorusParameter_ext_of_marking_I
    {τ σ : ComplexTorusParameter}
    (h : complexTorusMarkingLinearEquiv τ Complex.I =
      complexTorusMarkingLinearEquiv σ Complex.I) :
    τ = σ := by
  apply UpperHalfPlane.ext
  have h' := h
  rw [complexTorusMarkingLinearEquiv_apply,
    complexTorusMarkingLinearEquiv_apply] at h'
  simpa using h'

theorem complexTorusMarking_coordinate_injective :
    Function.Injective
      (fun τ : ComplexTorusParameter =>
        complexTorusMarkingLinearEquiv τ Complex.I) := by
  intro τ σ h
  exact complexTorusParameter_ext_of_marking_I h

/-! The lift-level rigidity is useful independently of the eventual universal
property.  Package it as a small witness so later classification arguments can
state exactly which coordinate separates parameters, without identifying
dependent quotient fibres by definitional equality. -/

structure ComplexTorusParameterRigidityWitness where
  coordinate : ComplexTorusParameter → ℂ
  coordinate_eq_marking_I : ∀ τ,
    coordinate τ = complexTorusMarkingLinearEquiv τ Complex.I
  coordinate_injective : Function.Injective coordinate

noncomputable def complexTorusParameterRigidityWitness :
    ComplexTorusParameterRigidityWitness where
  coordinate := fun τ => complexTorusMarkingLinearEquiv τ Complex.I
  coordinate_eq_marking_I := by
    intro τ
    rfl
  coordinate_injective := complexTorusMarking_coordinate_injective

theorem complexTorusParameter_eq_of_rigidity_coordinate
    (w : ComplexTorusParameterRigidityWitness)
    {τ σ : ComplexTorusParameter}
    (h : w.coordinate τ = w.coordinate σ) :
    τ = σ :=
  w.coordinate_injective h

/-! A normalized complex-linear lift is the algebraic core of the usual
genus-one rigidity argument.  The structure deliberately records exact
period preservation, rather than quotient equality: the latter still allows
an unspecified deck translation and is not enough to identify parameters. -/

structure ComplexTorusMarkedComplexLinearLift
    (τ σ : ComplexTorusParameter) where
  lift : ℂ →ₗ[ℂ] ℂ
  lift_one : lift 1 = 1
  lift_tau : lift (τ : ℂ) = (σ : ℂ)

theorem ComplexTorusMarkedComplexLinearLift.lift_eq_id
    {τ σ : ComplexTorusParameter}
    (L : ComplexTorusMarkedComplexLinearLift τ σ) :
    L.lift = LinearMap.id := by
  apply LinearMap.ext
  intro z
  calc
    L.lift z = L.lift (z • (1 : ℂ)) := by simp
    _ = z • L.lift (1 : ℂ) := by rw [map_smul]
    _ = z := by simp [L.lift_one]

theorem complexTorusParameter_eq_of_markedComplexLinearLift
    {τ σ : ComplexTorusParameter}
    (L : ComplexTorusMarkedComplexLinearLift τ σ) :
    τ = σ := by
  apply UpperHalfPlane.ext
  calc
    (τ : ℂ) = L.lift (τ : ℂ) := by
      rw [L.lift_eq_id]
      rfl
    _ = (σ : ℂ) := L.lift_tau

theorem ComplexTorusMarkedComplexLinearLift.unique
    {τ σ : ComplexTorusParameter}
    (L₁ L₂ : ComplexTorusMarkedComplexLinearLift τ σ) :
    L₁.lift = L₂.lift := by
  rw [L₁.lift_eq_id, L₂.lift_eq_id]

/-! The canonical real-linear change of marking between two parameters sends
the source period basis to the target period basis.  If this transition is
actually complex-linear, the preceding normalized-lift theorem applies. -/

noncomputable def complexTorusMarkingTransition
    (τ σ : ComplexTorusParameter) : ℂ ≃ₗ[ℝ] ℂ :=
  (complexTorusMarkingLinearEquiv τ).symm.trans
    (complexTorusMarkingLinearEquiv σ)

theorem complexTorusMarkingTransition_map_one
    (τ σ : ComplexTorusParameter) :
    complexTorusMarkingTransition τ σ (1 : ℂ) = 1 := by
  have hτ : complexTorusMarkingLinearEquiv τ (1 : ℂ) = 1 := by
    simpa [complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period τ (0 : Fin 2))
  have hσ : complexTorusMarkingLinearEquiv σ (1 : ℂ) = 1 := by
    simpa [complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period σ (0 : Fin 2))
  have hτ_inv : (complexTorusMarkingLinearEquiv τ).symm (1 : ℂ) = 1 := by
    apply (complexTorusMarkingLinearEquiv τ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hτ.symm
  simp [complexTorusMarkingTransition, hτ_inv, hσ]

theorem complexTorusMarkingTransition_map_tau
    (τ σ : ComplexTorusParameter) :
    complexTorusMarkingTransition τ σ (τ : ℂ) = (σ : ℂ) := by
  have hτ : complexTorusMarkingLinearEquiv τ (Complex.I : ℂ) = (τ : ℂ) := by
    simpa [complexTorusBaseParameter, complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period τ (1 : Fin 2))
  have hσ : complexTorusMarkingLinearEquiv σ (Complex.I : ℂ) = (σ : ℂ) := by
    simpa [complexTorusBaseParameter, complexTorusPeriodBasis_apply] using
      (complexTorusMarkingLinearEquiv_map_period σ (1 : Fin 2))
  have hτ_inv : (complexTorusMarkingLinearEquiv τ).symm (τ : ℂ) = Complex.I := by
    apply (complexTorusMarkingLinearEquiv τ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hτ.symm
  simp [complexTorusMarkingTransition, hτ_inv, hσ]

def ComplexTorusMarkingTransitionIsComplexLinear
    (τ σ : ComplexTorusParameter) : Prop :=
  ∀ (a z : ℂ),
    complexTorusMarkingTransition τ σ (a • z) =
      a • complexTorusMarkingTransition τ σ z

noncomputable def complexTorusMarkingTransition_toComplexLinear
    {τ σ : ComplexTorusParameter}
    (h : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    ℂ →ₗ[ℂ] ℂ where
  toFun := complexTorusMarkingTransition τ σ
  map_add' := fun x y =>
    (complexTorusMarkingTransition τ σ).map_add x y
  map_smul' := fun a z => h a z

theorem complexTorusParameter_eq_of_markingTransition_isComplexLinear
    {τ σ : ComplexTorusParameter}
    (h : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    τ = σ := by
  apply complexTorusParameter_eq_of_markedComplexLinearLift
  exact
    { lift := complexTorusMarkingTransition_toComplexLinear h
      lift_one := complexTorusMarkingTransition_map_one τ σ
      lift_tau := complexTorusMarkingTransition_map_tau τ σ }

@[simp] theorem complexTorusMarkingTransition_self_eq_refl
    (τ : ComplexTorusParameter) :
    complexTorusMarkingTransition τ τ = LinearEquiv.refl ℝ ℂ := by
  simp [complexTorusMarkingTransition]

theorem complexTorusMarkingTransition_isComplexLinear_self
    (τ : ComplexTorusParameter) :
    ComplexTorusMarkingTransitionIsComplexLinear τ τ := by
  intro a z
  simp [complexTorusMarkingTransition_self_eq_refl]

theorem complexTorusMarkingTransition_isComplexLinear_iff
    (τ σ : ComplexTorusParameter) :
    ComplexTorusMarkingTransitionIsComplexLinear τ σ ↔ τ = σ := by
  constructor
  · intro h
    exact complexTorusParameter_eq_of_markingTransition_isComplexLinear h
  · intro h
    subst σ
    exact complexTorusMarkingTransition_isComplexLinear_self τ

theorem complexTorusMarkingTransition_isComplexLinear_symm
    {τ σ : ComplexTorusParameter}
    (h : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    ComplexTorusMarkingTransitionIsComplexLinear σ τ := by
  have h_eq : τ = σ :=
    complexTorusParameter_eq_of_markingTransition_isComplexLinear h
  subst σ
  exact complexTorusMarkingTransition_isComplexLinear_self τ

@[simp] theorem complexTorusMarkingLinearEquiv_base_eq_refl :
    complexTorusMarkingLinearEquiv complexTorusBaseParameter =
      LinearEquiv.refl ℝ ℂ := by
  ext z
  rw [complexTorusMarkingLinearEquiv_apply]
  simp [complexTorusBaseParameter]

theorem complexTorusMarkingLinearEquiv_parameter_formula_differentiableOn
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun τ : ℂ => (z.re : ℂ) + (z.im : ℂ) * τ)
      upperHalfPlaneSet := by
  fun_prop

/-! The preceding formula is a data-carrying partial witness for analytic
variation.  It controls the parameter direction of a fixed reference lift;
it does not assert that the real-linear marking is jointly holomorphic in a
fibre coordinate. -/

structure ComplexTorusParameterLiftWitness where
  lift : ℂ × ℂ → ℂ
  lift_eq_marking : ∀ (τ : ℂ) (hτ : τ ∈ upperHalfPlaneSet) (z : ℂ),
    lift (τ, z) =
      complexTorusMarkingLinearEquiv ⟨τ, hτ⟩ z
  parameter_differentiable : ∀ z : ℂ,
    DifferentiableOn ℂ (fun τ : ℂ => lift (τ, z)) upperHalfPlaneSet

noncomputable def complexTorusParameterLiftWitness :
    ComplexTorusParameterLiftWitness where
  lift := fun p => (p.2.re : ℂ) + (p.2.im : ℂ) * p.1
  lift_eq_marking := by
    intro τ hτ z
    exact (complexTorusMarkingLinearEquiv_apply ⟨τ, hτ⟩ z).symm
  parameter_differentiable := by
    intro z
    exact complexTorusMarkingLinearEquiv_parameter_formula_differentiableOn z

/-- The same marking lift, now named as an ambient map on the two real/complex
coordinates.  It is useful to state its regularity separately from the
holomorphic total-space coordinate: the real-linear dependence on `z` is
generally not complex-holomorphic in the fibre variable. -/
def complexTorusMarkingLift (p : ℂ × ℂ) : ℂ :=
  (p.2.re : ℂ) + (p.2.im : ℂ) * p.1

theorem complexTorusMarkingLift_eq_marking
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMarkingLift ((τ : ℂ), z) =
      complexTorusMarkingLinearEquiv τ z := by
  exact (complexTorusMarkingLinearEquiv_apply τ z).symm

theorem complexTorusMarkingLift_differentiable_real :
    Differentiable ℝ complexTorusMarkingLift := by
  change Differentiable ℝ
    (fun p : ℂ × ℂ => (p.2.re : ℂ) + (p.2.im : ℂ) * p.1)
  have hre : Differentiable ℝ (fun p : ℂ × ℂ => (p.2.re : ℂ)) := by
    exact Complex.ofRealCLM.differentiable.comp
      (Complex.reCLM.differentiable.comp differentiable_snd)
  have him : Differentiable ℝ (fun p : ℂ × ℂ => (p.2.im : ℂ)) := by
    exact Complex.ofRealCLM.differentiable.comp
      (Complex.imCLM.differentiable.comp differentiable_snd)
  exact hre.add (him.mul differentiable_fst)

theorem complexTorusMarkingLift_parameter_differentiableOn
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun τ : ℂ => complexTorusMarkingLift (τ, z))
      upperHalfPlaneSet := by
  simpa [complexTorusMarkingLift] using
    complexTorusMarkingLinearEquiv_parameter_formula_differentiableOn z

/-! ### Holomorphic test maps into the parameter space

The universal-property direction is tested by a base map into the upper
half-plane.  The following small structure keeps the domain, the condition
that the image remains in the upper half-plane, and the actual complex
differentiability proof together.  It is the first data-carrying analytic
replacement for a bare phrase such as “vary the parameter holomorphically”.
-/

structure ComplexTorusHolomorphicParameterMap where
  domain : Set ℂ
  domain_open : IsOpen domain
  map : ℂ → ℂ
  map_continuous : Continuous map
  map_mem_upperHalfPlane : Set.MapsTo map domain upperHalfPlaneSet
  map_differentiableOn : DifferentiableOn ℂ map domain

noncomputable def complexTorusIdentityHolomorphicParameterMap :
    ComplexTorusHolomorphicParameterMap where
  domain := upperHalfPlaneSet
  domain_open := by
    change IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  map := id
  map_continuous := continuous_id
  map_mem_upperHalfPlane := by
    intro z hz
    simpa using hz
  map_differentiableOn := differentiableOn_id

theorem ComplexTorusHolomorphicParameterMap.markingLift_differentiableOn
    (F : ComplexTorusHolomorphicParameterMap) (z : ℂ) :
    DifferentiableOn ℂ
      (fun c : ℂ => complexTorusMarkingLift (F.map c, z)) F.domain := by
  have hcomp :=
    (complexTorusMarkingLift_parameter_differentiableOn z).fun_comp
      F.map_differentiableOn F.map_mem_upperHalfPlane
  simpa [Function.comp_def] using hcomp

def ComplexTorusHolomorphicParameterMap.ambientBaseChange
    (F : ComplexTorusHolomorphicParameterMap) : ℂ × ℂ → ℂ × ℂ :=
  fun p => (F.map p.1, p.2)

theorem ComplexTorusHolomorphicParameterMap.ambientBaseChange_differentiableOn
    (F : ComplexTorusHolomorphicParameterMap) (r : ℝ) :
    DifferentiableOn ℂ F.ambientBaseChange
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) := by
  have hbase : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => F.map p.1)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) := by
    apply F.map_differentiableOn.fun_comp
      differentiable_fst.differentiableOn
    intro p hp
    exact hp.1
  have hfiber : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => p.2)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) :=
    differentiable_snd.differentiableOn
  exact hbase.prodMk hfiber

/-! A parameter-dependent deck transition on an analytic test base.  The
base coordinate is now the test variable `c`, while the lattice coefficient
uses the holomorphic parameter map `F.map c`. -/

def ComplexTorusHolomorphicParameterMap.deckTransition
    (F : ComplexTorusHolomorphicParameterMap) (m n : ℤ) :
    ℂ × ℂ → ℂ × ℂ :=
  fun p => (p.1, p.2 + (m : ℂ) + (n : ℂ) * F.map p.1)

theorem ComplexTorusHolomorphicParameterMap.deckTransition_first_coordinate
    (F : ComplexTorusHolomorphicParameterMap) (m n : ℤ) (p : ℂ × ℂ) :
    (F.deckTransition m n p).1 = p.1 := by
  rfl

theorem ComplexTorusHolomorphicParameterMap.deckTransition_continuousOn
    (F : ComplexTorusHolomorphicParameterMap) (m n : ℤ) (r : ℝ) :
    ContinuousOn (F.deckTransition m n)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) := by
  have hparam : ContinuousOn
      (fun p : ℂ × ℂ => F.map p.1)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) := by
    exact F.map_continuous.continuousOn.comp continuous_fst.continuousOn
      (fun p hp => hp.1)
  exact continuous_fst.continuousOn.prodMk
    ((continuous_snd.continuousOn.add continuousOn_const).add
      (continuousOn_const.mul hparam))

theorem ComplexTorusHolomorphicParameterMap.deckTransition_differentiableOn
    (F : ComplexTorusHolomorphicParameterMap) (m n : ℤ) (r : ℝ) :
    DifferentiableOn ℂ (F.deckTransition m n)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) := by
  let S : Set (ℂ × ℂ) := F.domain ×ˢ Metric.ball (0 : ℂ) r
  have hparam : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => F.map p.1)
      S := by
    apply F.map_differentiableOn.fun_comp
      differentiable_fst.differentiableOn
    intro p hp
    exact hp.1
  have hm : DifferentiableOn ℂ
      (fun _ : ℂ × ℂ => (m : ℂ)) S := differentiableOn_const _
  have hn : DifferentiableOn ℂ
      (fun _ : ℂ × ℂ => (n : ℂ)) S := differentiableOn_const _
  exact differentiable_fst.differentiableOn.prodMk
    ((differentiable_snd.differentiableOn.add hm).add (hn.mul hparam))

/-! ### A uniform local parameter/lift domain

To move from a fibrewise atlas to a total-space chart, choose a small
neighbourhood of the reference parameter i and a common disk around the zero
lift. The lower bound on nonzero lattice vectors makes the quotient map
injective on that disk for every parameter in the neighbourhood. -/

def complexTorusLocalParameterNeighborhood : Set ℂ :=
  {τ | |τ.im - 1| < (1 : ℝ) / 4}

theorem complexTorusLocalParameterNeighborhood_isOpen :
    IsOpen complexTorusLocalParameterNeighborhood := by
  change IsOpen {τ : ℂ | |τ.im - 1| < (1 : ℝ) / 4}
  exact isOpen_lt
    (continuous_abs.comp (Complex.imCLM.continuous.sub continuous_const))
    continuous_const

theorem complexTorusLocalParameterNeighborhood_contains_base :
    (Complex.I : ℂ) ∈ complexTorusLocalParameterNeighborhood := by
  change |(Complex.I : ℂ).im - 1| < (1 : ℝ) / 4
  norm_num

theorem complexTorusLocalParameterNeighborhood_im_pos
    {τ : ℂ} (hτ : τ ∈ complexTorusLocalParameterNeighborhood) :
    0 < τ.im := by
  change |τ.im - 1| < (1 : ℝ) / 4 at hτ
  rcases (abs_lt.mp hτ) with ⟨hleft, hright⟩
  linarith

/-! A local analytic test map is one whose image remains in the uniform
neighbourhood used by the quotient chart construction. -/

structure ComplexTorusLocalHolomorphicParameterMap
    extends ComplexTorusHolomorphicParameterMap where
  map_mem_localNeighborhood :
    Set.MapsTo map domain complexTorusLocalParameterNeighborhood

noncomputable def complexTorusIdentityLocalHolomorphicParameterMap :
    ComplexTorusLocalHolomorphicParameterMap where
  toComplexTorusHolomorphicParameterMap := {
    domain := complexTorusLocalParameterNeighborhood
    domain_open := complexTorusLocalParameterNeighborhood_isOpen
    map := id
    map_continuous := continuous_id
    map_mem_upperHalfPlane := by
      intro z hz
      change 0 < z.im
      exact complexTorusLocalParameterNeighborhood_im_pos hz
    map_differentiableOn := differentiableOn_id }
  map_mem_localNeighborhood := by
    intro z hz
    simpa using hz

/-! ### Composition of local analytic test bases

The local parameter maps are closed under the same base change that appears
in the universal-property interface.  If `G` lands in the domain of `F`,
then the composite `F ∘ G` is again a local holomorphic parameter map.  This
is the concrete upper-half-plane version of composing two holomorphic test
maps; the image condition is kept explicit so that the subtype-valued
parameter point never relies on an unproved coercion.
-/

def ComplexTorusLocalHolomorphicParameterMap.precompose
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    ComplexTorusLocalHolomorphicParameterMap where
  toComplexTorusHolomorphicParameterMap := {
    domain := G.domain
    domain_open := G.domain_open
    map := fun c => F.map (G.map c)
    map_continuous := F.map_continuous.comp G.map_continuous
    map_mem_upperHalfPlane := by
      intro c hc
      exact F.map_mem_upperHalfPlane (hG hc)
    map_differentiableOn := by
      exact F.map_differentiableOn.fun_comp G.map_differentiableOn hG }
  map_mem_localNeighborhood := by
    intro c hc
    exact F.map_mem_localNeighborhood (hG hc)

@[simp] theorem ComplexTorusLocalHolomorphicParameterMap.precompose_map
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (F.precompose G hG).map = fun c => F.map (G.map c) := by
  rfl

theorem ComplexTorusLocalHolomorphicParameterMap.precompose_map_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    DifferentiableOn ℂ (fun c => F.map (G.map c)) G.domain := by
  exact F.map_differentiableOn.fun_comp G.map_differentiableOn hG

/-! The corresponding composition operation on the ambient parameter-map
    structure is useful when the outer map is not itself a local map.  It
    makes associativity a theorem about actual data, rather than a slogan
    about function composition. -/

def ComplexTorusHolomorphicParameterMap.compose
    (F G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    ComplexTorusHolomorphicParameterMap where
  domain := G.domain
  domain_open := G.domain_open
  map := fun c => F.map (G.map c)
  map_continuous := F.map_continuous.comp G.map_continuous
  map_mem_upperHalfPlane := by
    intro c hc
    exact F.map_mem_upperHalfPlane (hG hc)
  map_differentiableOn := F.map_differentiableOn.fun_comp
    G.map_differentiableOn hG

@[simp] theorem ComplexTorusHolomorphicParameterMap.compose_map
    (F G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (F.compose G hG).map = fun c => F.map (G.map c) := by
  rfl

theorem ComplexTorusHolomorphicParameterMap.compose_identity_map
    (F : ComplexTorusHolomorphicParameterMap)
    (hF : Set.MapsTo id F.domain upperHalfPlaneSet) :
    (F.compose
      { domain := F.domain
        domain_open := F.domain_open
        map := id
        map_continuous := continuous_id
        map_mem_upperHalfPlane := by
          intro c hc
          simpa using hF hc
        map_differentiableOn := differentiableOn_id }
      (by
        intro c hc
        exact hc)).map = F.map := by
  funext c
  rfl

theorem ComplexTorusLocalHolomorphicParameterMap.precompose_precompose_map
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G H : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (hH : Set.MapsTo H.map H.domain G.domain)
    (hGH : Set.MapsTo (G.compose H hH).map
      (G.compose H hH).domain F.domain) :
    ((F.precompose G hG).precompose H hH).map =
      (F.precompose (G.compose H hH) hGH).map := by
  funext c
  rfl

def ComplexTorusHolomorphicParameterMap.parameterPoint
    (F : ComplexTorusHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) : ComplexTorusParameter :=
  ⟨F.map c, F.map_mem_upperHalfPlane c.2⟩

theorem ComplexTorusHolomorphicParameterMap.parameterPoint_continuous
    (F : ComplexTorusHolomorphicParameterMap) :
    Continuous F.parameterPoint := by
  apply continuous_induced_rng.2
  exact F.map_continuous.comp continuous_subtype_val

@[simp] theorem ComplexTorusLocalHolomorphicParameterMap.precompose_parameterPoint
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (c : {c : ℂ // c ∈ G.domain}) :
    (F.precompose G hG).toComplexTorusHolomorphicParameterMap.parameterPoint c =
      F.toComplexTorusHolomorphicParameterMap.parameterPoint
        ⟨G.map c, hG c.property⟩ := by
  rfl

theorem ComplexTorusLocalHolomorphicParameterMap.deckTransition_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap) (m n : ℤ) (r : ℝ) :
    DifferentiableOn ℂ
      (F.toComplexTorusHolomorphicParameterMap.deckTransition m n)
      (F.domain ×ˢ Metric.ball (0 : ℂ) r) :=
  F.toComplexTorusHolomorphicParameterMap.deckTransition_differentiableOn m n r

theorem complexTorusLattice_int_combination
    (τ : ComplexTorusParameter) {v : ℂ}
    (hv : v ∈ complexTorusLattice τ) :
    ∃ m n : ℤ, v = (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
  rw [complexTorusLattice_eq_periodBasis_span] at hv
  have hcoords := (complexTorusPeriodBasis τ).mem_span_iff_repr_mem ℤ v
  have h0 := hcoords.mp hv 0
  have h1 := hcoords.mp hv 1
  rcases h0 with ⟨m, hm⟩
  rcases h1 with ⟨n, hn⟩
  refine ⟨m, n, ?_⟩
  rw [← (complexTorusPeriodBasis τ).sum_repr v]
  simp only [Fin.sum_univ_two]
  rw [← hm, ← hn]
  simp [Fin.sum_univ_two, complexTorusPeriodBasis_apply, smul_eq_mul]

theorem complexTorusLattice_norm_lower_bound
    (τ : ComplexTorusParameter)
    (hτ : (τ : ℂ) ∈ complexTorusLocalParameterNeighborhood)
    {v : ℂ} (hv : v ∈ complexTorusLattice τ) (hv0 : v ≠ 0) :
    (3 : ℝ) / 4 ≤ ‖v‖ := by
  obtain ⟨m, n, hvrep⟩ := complexTorusLattice_int_combination τ hv
  have hτim : (3 : ℝ) / 4 < (τ : ℂ).im := by
    change |(τ : ℂ).im - 1| < (1 : ℝ) / 4 at hτ
    rcases (abs_lt.mp hτ) with ⟨hleft, hright⟩
    linarith
  have hτim_pos : 0 < (τ : ℂ).im := by linarith
  by_cases hn0 : n = 0
  · have hm0 : m ≠ 0 := by
      intro hm0
      apply hv0
      rw [hvrep, hm0, hn0]
      norm_num
    have hnorm : (1 : ℝ) ≤ ‖(m : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs hm0)
    simpa [hvrep, hn0] using
      ((by norm_num : (3 : ℝ) / 4 ≤ 1).trans hnorm)
  · have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hn0)
    have hprod : (3 : ℝ) / 4 ≤ |(n : ℝ)| * (τ : ℂ).im := by
      calc
        (3 : ℝ) / 4 ≤ (τ : ℂ).im := le_of_lt hτim
        _ = 1 * (τ : ℂ).im := by ring
        _ ≤ |(n : ℝ)| * (τ : ℂ).im :=
          mul_le_mul_of_nonneg_right hnabs (le_of_lt hτim_pos)
    have him : |v.im| = |(n : ℝ)| * (τ : ℂ).im := by
      rw [hvrep]
      simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im,
        Complex.intCast_re, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re,
        zero_mul, add_zero, zero_add, abs_mul, mul_eq_mul_left_iff,
        abs_eq_self, abs_eq_zero, Int.cast_eq_zero]
      exact Or.inl (le_of_lt τ.im_pos)
    exact hprod.trans (by rw [← him]; exact Complex.abs_im_le_norm v)

theorem complexTorusMk_injective_on_local_lift_ball
    (τ : ComplexTorusParameter)
    (hτ : (τ : ℂ) ∈ complexTorusLocalParameterNeighborhood) :
    Set.InjOn (complexTorusMk τ)
      (Metric.ball (0 : ℂ) ((1 : ℝ) / 4)) := by
  intro z hz w hw hzw
  by_contra hne
  have hd_mem : z - w ∈ complexTorusLattice τ :=
    (complexTorusMk_eq_iff τ z w).mp hzw
  have hd_ne : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hlow := complexTorusLattice_norm_lower_bound τ hτ hd_mem hd_ne
  have hz_norm : ‖z‖ < (1 : ℝ) / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hw_norm : ‖w‖ < (1 : ℝ) / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hupper : ‖z - w‖ < (1 : ℝ) / 2 := by
    calc
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      _ < (1 : ℝ) / 4 + 1 / 4 := add_lt_add hz_norm hw_norm
      _ = (1 : ℝ) / 2 := by norm_num
  exact (not_le_of_gt hupper)
    ((by norm_num : (1 : ℝ) / 2 ≤ 3 / 4).trans hlow)

abbrev ComplexTorusLocalLiftAt (c : ℂ) :=
  Metric.ball c ((1 : ℝ) / 4)

theorem complexTorusMk_injective_on_local_lift_ball_center
    (τ : ComplexTorusParameter)
    (hτ : (τ : ℂ) ∈ complexTorusLocalParameterNeighborhood)
    (c : ℂ) :
    Set.InjOn (complexTorusMk τ) (ComplexTorusLocalLiftAt c) := by
  intro z hz w hw hzw
  by_contra hne
  have hd_mem : z - w ∈ complexTorusLattice τ :=
    (complexTorusMk_eq_iff τ z w).mp hzw
  have hd_ne : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hlow := complexTorusLattice_norm_lower_bound τ hτ hd_mem hd_ne
  have hz_norm : ‖z - c‖ < (1 : ℝ) / 4 := by
    simpa [ComplexTorusLocalLiftAt, Metric.mem_ball, dist_eq_norm] using hz
  have hw_norm : ‖w - c‖ < (1 : ℝ) / 4 := by
    simpa [ComplexTorusLocalLiftAt, Metric.mem_ball, dist_eq_norm] using hw
  have hupper : ‖z - w‖ < (1 : ℝ) / 2 := by
    calc
      ‖z - w‖ = ‖(z - c) - (w - c)‖ := by congr 1 <;> ring
      _ ≤ ‖z - c‖ + ‖w - c‖ := norm_sub_le _ _
      _ < (1 : ℝ) / 4 + 1 / 4 := add_lt_add hz_norm hw_norm
      _ = (1 : ℝ) / 2 := by norm_num
  exact (not_le_of_gt hupper)
    ((by norm_num : (1 : ℝ) / 2 ≤ 3 / 4).trans hlow)

theorem complexTorusMarkingLinearEquiv_map_lattice
    (τ : ComplexTorusParameter) :
    (complexTorusLattice complexTorusBaseParameter).map
        ((complexTorusMarkingLinearEquiv τ).toAddEquiv.toAddMonoidHom.toIntLinearMap) =
      complexTorusLattice τ := by
  rw [complexTorusLattice_eq_periodBasis_span,
    complexTorusLattice_eq_periodBasis_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by
      simpa only [AddMonoidHom.coe_toIntLinearMap,
        AddEquiv.coe_toAddMonoidHom,
        LinearEquiv.coe_toAddEquiv,
        LinearEquiv.coe_addEquiv_apply] using
        (complexTorusMarkingLinearEquiv_map_period τ i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨complexTorusPeriodBasis complexTorusBaseParameter i,
      ⟨i, rfl⟩, ?_⟩
    simpa only [AddMonoidHom.coe_toIntLinearMap,
      AddEquiv.coe_toAddMonoidHom,
      LinearEquiv.coe_toAddEquiv,
      LinearEquiv.coe_addEquiv_apply] using
      complexTorusMarkingLinearEquiv_map_period τ i

noncomputable def complexTorusMarkingAddEquiv
    (τ : ComplexTorusParameter) :
    ComplexTorus complexTorusBaseParameter ≃+
      ComplexTorus τ :=
  QuotientAddGroup.congr
    (complexTorusLattice complexTorusBaseParameter).toAddSubgroup
    (complexTorusLattice τ).toAddSubgroup
    (complexTorusMarkingLinearEquiv τ).toAddEquiv (by
      have h := congrArg Submodule.toAddSubgroup
        (complexTorusMarkingLinearEquiv_map_lattice τ)
      rw [Submodule.map_toAddSubgroup] at h
      convert h using 1)

@[simp]
theorem complexTorusMarkingAddEquiv_mk
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMarkingAddEquiv τ
        (complexTorusMk complexTorusBaseParameter z) =
      complexTorusMk τ (complexTorusMarkingLinearEquiv τ z) :=
  rfl

theorem complexTorusMarkingAddEquiv_continuous
    (τ : ComplexTorusParameter) :
    Continuous (complexTorusMarkingAddEquiv τ) := by
  have hfun :
      (complexTorusMarkingAddEquiv τ ∘
          complexTorusMk complexTorusBaseParameter) =
        (complexTorusMk τ ∘ complexTorusMarkingLinearEquiv τ) := by
    funext z
    exact complexTorusMarkingAddEquiv_mk τ z
  apply (isQuotientMap_quotient_mk'.continuous_iff).2
  change Continuous (complexTorusMarkingAddEquiv τ ∘
    complexTorusMk complexTorusBaseParameter)
  rw [hfun]
  exact (complexTorusMk_continuous τ).comp
    (complexTorusMarkingLinearEquiv τ).toContinuousLinearEquiv.continuous_toFun

theorem complexTorusMarkingAddEquiv_symm_continuous
    (τ : ComplexTorusParameter) :
    Continuous (complexTorusMarkingAddEquiv τ).symm := by
  have hfun :
      ((complexTorusMarkingAddEquiv τ).symm ∘ complexTorusMk τ) =
        (complexTorusMk complexTorusBaseParameter ∘
          (complexTorusMarkingLinearEquiv τ).symm) := by
    funext z
    apply (complexTorusMarkingAddEquiv τ).injective
    simp [complexTorusMarkingAddEquiv_mk]
  apply (isQuotientMap_quotient_mk'.continuous_iff).2
  change Continuous ((complexTorusMarkingAddEquiv τ).symm ∘
    complexTorusMk τ)
  rw [hfun]
  exact (complexTorusMk_continuous complexTorusBaseParameter).comp
    (complexTorusMarkingLinearEquiv τ).symm.toContinuousLinearEquiv.continuous_toFun

noncomputable def complexTorusMarkingHomeomorph
    (τ : ComplexTorusParameter) :
    @Homeomorph
      (ComplexTorus complexTorusBaseParameter) (ComplexTorus τ)
      inferInstance inferInstance :=
  let hopen : IsOpenMap (complexTorusMarkingAddEquiv τ).toEquiv :=
    IsOpenMap.of_inverse
      (f := (complexTorusMarkingAddEquiv τ).toEquiv)
      (f' := (complexTorusMarkingAddEquiv τ).toEquiv.symm)
      (by
        change Continuous (complexTorusMarkingAddEquiv τ).symm
        exact complexTorusMarkingAddEquiv_symm_continuous τ)
      (complexTorusMarkingAddEquiv τ).toEquiv.right_inv
      (complexTorusMarkingAddEquiv τ).toEquiv.left_inv
  (complexTorusMarkingAddEquiv τ).toEquiv.toHomeomorphOfContinuousOpen
    (complexTorusMarkingAddEquiv_continuous τ)
    hopen

@[simp]
theorem complexTorusMarkingHomeomorph_mk
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMarkingHomeomorph τ
        (complexTorusMk complexTorusBaseParameter z) =
      complexTorusMk τ (complexTorusMarkingLinearEquiv τ z) :=
  rfl

@[simp] theorem complexTorusMarkingHomeomorph_base_eq_refl :
    complexTorusMarkingHomeomorph complexTorusBaseParameter =
      Homeomorph.refl (ComplexTorus complexTorusBaseParameter) := by
  apply Homeomorph.ext
  intro x
  rcases QuotientAddGroup.mk'_surjective
      (complexTorusLattice complexTorusBaseParameter).toAddSubgroup x with
    ⟨z, rfl⟩
  change complexTorusMarkingHomeomorph complexTorusBaseParameter
      (complexTorusMk complexTorusBaseParameter z) =
    complexTorusMk complexTorusBaseParameter z
  rw [complexTorusMarkingHomeomorph_mk]
  simp

/-! ### Quotient-level normalization of marked biholomorphisms

The marking is a homeomorphism from the fixed reference torus, so a map that
commutes with the marking is already determined on every quotient point.  The
following result separates this formal normalization from the genuinely
analytic question of whether the resulting canonical transition is
holomorphic. -/

structure ComplexTorusMarkedBiholomorphism
    (τ σ : ComplexTorusParameter) where
  map : @Homeomorph
    (ComplexTorus τ) (ComplexTorus σ) inferInstance inferInstance
  holomorphic : @MathlibFormal.AtlasHolomorphicEquiv
    (ComplexTorus τ) (ComplexTorus σ)
    inferInstance inferInstance
    (complexTorusRiemannSurface τ).atlas
    (complexTorusRiemannSurface σ).atlas map
  marking_commutes : ∀ s,
    map (complexTorusMarkingHomeomorph τ s) =
      complexTorusMarkingHomeomorph σ s

noncomputable def complexTorusMarkedTransitionHomeomorph
    (τ σ : ComplexTorusParameter) :
    @Homeomorph
      (ComplexTorus τ) (ComplexTorus σ) inferInstance inferInstance :=
  (complexTorusMarkingHomeomorph τ).symm.trans
    (complexTorusMarkingHomeomorph σ)

theorem complexTorusMarkedTransitionHomeomorph_mk
    (τ σ : ComplexTorusParameter) (z : ℂ) :
    complexTorusMarkedTransitionHomeomorph τ σ
        (complexTorusMk τ z) =
      complexTorusMk σ (complexTorusMarkingTransition τ σ z) := by
  let q := complexTorusMk complexTorusBaseParameter
      ((complexTorusMarkingLinearEquiv τ).symm z)
  have hq : complexTorusMarkingHomeomorph τ q =
      complexTorusMk τ z := by
    dsimp [q]
    change complexTorusMk τ
      (complexTorusMarkingLinearEquiv τ
        ((complexTorusMarkingLinearEquiv τ).symm z)) =
      complexTorusMk τ z
    rw [LinearEquiv.apply_symm_apply]
  change complexTorusMarkingHomeomorph σ
      ((complexTorusMarkingHomeomorph τ).symm
        (complexTorusMk τ z)) = _
  rw [← hq, (complexTorusMarkingHomeomorph τ).symm_apply_apply]
  rw [complexTorusMarkingHomeomorph_mk]
  rfl

theorem ComplexTorusLocalChart.canonicalTransition_difference_mem_lattice
    {τ σ : ComplexTorusParameter}
    (c₁ : ComplexTorusLocalChart τ) (c₂ : ComplexTorusLocalChart σ)
    {z : ℂ}
    (hz : z ∈ c₁.chart.target ∧
      complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm z) ∈ c₂.chart.source) :
    c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm z)) -
        complexTorusMarkingTransition τ σ z ∈
      complexTorusLattice σ := by
  apply (complexTorusMk_eq_iff σ _ _).mp
  have hz₁ : c₁.chart.symm z ∈ c₁.chart.source :=
    c₁.chart.map_target hz.1
  have hz₂ : complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm z) ∈ c₂.chart.source :=
    hz.2
  have h₁z := c₁.section_eq (c₁.chart.symm z) hz₁
  have h₂z := c₂.section_eq
    (complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm z)) hz₂
  have hcanon :
      complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm z) =
        complexTorusMk σ (complexTorusMarkingTransition τ σ z) := by
    rw [← h₁z, c₁.chart.right_inv hz.1,
      complexTorusMarkedTransitionHomeomorph_mk]
  rw [h₂z, hcanon]

theorem ComplexTorusLocalChart.canonicalTransition_differentiableOn
    {τ σ : ComplexTorusParameter}
    (hlinear : ComplexTorusMarkingTransitionIsComplexLinear τ σ)
    (c₁ : ComplexTorusLocalChart τ) (c₂ : ComplexTorusLocalChart σ) :
    DifferentiableOn ℂ
      (fun z => c₂.chart
        (complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm z)))
      {z : ℂ |
        z ∈ c₁.chart.target ∧
          complexTorusMarkedTransitionHomeomorph τ σ
            (c₁.chart.symm z) ∈ c₂.chart.source} := by
  let S : Set ℂ := {z : ℂ |
    z ∈ c₁.chart.target ∧
      complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm z) ∈ c₂.chart.source}
  let L : ℂ → ℂ := complexTorusMarkingTransition τ σ
  have hLformula : ∀ z : ℂ, L z = z * L 1 := by
    intro z
    simpa [L, smul_eq_mul] using hlinear z 1
  have hLdiff : Differentiable ℂ L := by
    have hfun : L = fun z : ℂ => z * L 1 := by
      funext z
      exact hLformula z
    rw [hfun]
    fun_prop
  have hcanon_cont : ContinuousOn
      (fun z : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm z)) S := by
    exact (complexTorusMarkedTransitionHomeomorph τ σ).continuous.continuousOn.comp
      (c₁.chart.continuousOn_symm.mono fun z hz => hz.1)
      (fun _ _ => Set.mem_univ _)
  have htarget_cont : ContinuousOn
      (fun z : ℂ => c₂.chart
        (complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm z))) S := by
    exact c₂.chart.continuousOn.comp hcanon_cont
      (fun z hz => hz.2)
  let d : ℂ → ℂ := fun z =>
    c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm z)) - L z
  have hd_mem : Set.MapsTo d S (complexTorusLattice σ : Set ℂ) := by
    intro z hz
    exact ComplexTorusLocalChart.canonicalTransition_difference_mem_lattice
      c₁ c₂ ⟨hz.1, hz.2⟩
  have hd_cont : ContinuousOn d S := by
    dsimp [d]
    exact htarget_cont.sub hLdiff.continuous.continuousOn
  let d' : S → (complexTorusLattice σ : Set ℂ) :=
    hd_mem.restrict d S (complexTorusLattice σ : Set ℂ)
  have hd'_cont : Continuous d' := hd_cont.mapsToRestrict hd_mem
  have hd'_locallyConstant : IsLocallyConstant d' :=
    (IsLocallyConstant.iff_continuous d').2 hd'_cont
  intro z hz
  have hde : ∀ᶠ w in 𝓝[S] z, d w = d z := by
    rw [← eventually_nhds_subtype_iff S ⟨z, hz⟩ (fun w => d w = d z)]
    filter_upwards [hd'_locallyConstant.eventually_eq ⟨z, hz⟩] with w hw
    exact congrArg Subtype.val hw
  have htransition : ∀ᶠ w in 𝓝[S] z,
      c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) = L w + d z := by
    filter_upwards [hde] with w hw
    have hw' : c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) = L w + d z := by
      change c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) - L w = d z at hw
      calc
        c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
            (c₁.chart.symm w)) =
            (c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
              (c₁.chart.symm w)) - L w) + L w := by ring
        _ = d z + L w := by rw [hw]
        _ = L w + d z := by ac_rfl
    exact hw'
  have hbase : DifferentiableWithinAt ℂ
      (fun w : ℂ => L w + d z) S z := by
    exact (hLdiff.differentiableAt.add
      (differentiableAt_const (c := d z))).differentiableWithinAt
  exact hbase.congr_of_eventuallyEq htransition
    (htransition.self_of_nhdsWithin hz)

theorem ComplexTorusLocalChart.canonicalTransition_differentiableAt_implies_markingTransition_differentiableAt
    {τ σ : ComplexTorusParameter}
    (c₁ : ComplexTorusLocalChart τ) (c₂ : ComplexTorusLocalChart σ)
    {z : ℂ}
    (hz : z ∈ c₁.chart.target ∧
      complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm z) ∈ c₂.chart.source)
    (h : DifferentiableAt ℂ
      (fun w => c₂.chart
        (complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w))) z) :
    DifferentiableAt ℂ (complexTorusMarkingTransition τ σ) z := by
  let S : Set ℂ := {w : ℂ |
    w ∈ c₁.chart.target ∧
      complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w) ∈ c₂.chart.source}
  let L : ℂ → ℂ := complexTorusMarkingTransition τ σ
  have hLcont : Continuous L := by
    dsimp [L]
    exact (complexTorusMarkingTransition τ σ).toContinuousLinearEquiv.continuous_toFun
  let d : ℂ → ℂ := fun w =>
    c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm w)) - L w
  have htarget_cont : ContinuousOn
      (fun w : ℂ => c₂.chart
        (complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w))) S := by
    exact c₂.chart.continuousOn.comp
      ((complexTorusMarkedTransitionHomeomorph τ σ).continuous.continuousOn.comp
        (c₁.chart.continuousOn_symm.mono fun w hw => hw.1)
        (fun _ _ => Set.mem_univ _))
      (fun w hw => hw.2)
  have hd_mem : Set.MapsTo d S (complexTorusLattice σ : Set ℂ) := by
    intro w hw
    exact ComplexTorusLocalChart.canonicalTransition_difference_mem_lattice
      c₁ c₂ ⟨hw.1, hw.2⟩
  have hd_cont : ContinuousOn d S := by
    dsimp [d]
    exact htarget_cont.sub hLcont.continuousOn
  let d' : S → (complexTorusLattice σ : Set ℂ) :=
    hd_mem.restrict d S (complexTorusLattice σ : Set ℂ)
  have hd'_cont : Continuous d' := hd_cont.mapsToRestrict hd_mem
  have hd'_locallyConstant : IsLocallyConstant d' :=
    (IsLocallyConstant.iff_continuous d').2 hd'_cont
  have hde : ∀ᶠ w in 𝓝 z, d w = d z := by
    have hS_nhds : S ∈ 𝓝 z := by
      have hcomp : ContinuousAt
          (fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
            (c₁.chart.symm w)) z :=
        have houter : ContinuousAt (complexTorusMarkedTransitionHomeomorph τ σ)
            (c₁.chart.symm z) :=
          (complexTorusMarkedTransitionHomeomorph τ σ).continuous.continuousAt
        houter.comp (c₁.chart.continuousAt_symm hz.1)
      have hpre :
          (fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
            (c₁.chart.symm w)) ⁻¹' c₂.chart.source ∈ 𝓝 z :=
        hcomp.preimage_mem_nhds (c₂.chart.open_source.mem_nhds hz.2)
      change c₁.chart.target ∩
        ((fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w)) ⁻¹' c₂.chart.source) ∈ 𝓝 z
      exact Filter.inter_mem (c₁.chart.open_target.mem_nhds hz.1) hpre
    have hdeWithin : ∀ᶠ w in 𝓝[S] z, d w = d z := by
      rw [← eventually_nhds_subtype_iff S ⟨z, hz⟩ (fun w => d w = d z)]
      filter_upwards [hd'_locallyConstant.eventually_eq ⟨z, hz⟩] with w hw
      exact congrArg Subtype.val hw
    have hde' : ∀ᶠ w in 𝓝 z, w ∈ S → d w = d z :=
      eventually_nhdsWithin_iff.1 hdeWithin
    filter_upwards [hde', hS_nhds] with w hw hws
    exact hw hws
  have htransition : ∀ᶠ w in 𝓝 z,
      c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) = L w + d z := by
    filter_upwards [hde] with w hw
    have hw' : c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) = L w + d z := by
      change c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) - L w = d z at hw
      calc
        c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
            (c₁.chart.symm w)) =
            (c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
              (c₁.chart.symm w)) - L w) + L w := by ring
        _ = d z + L w := by rw [hw]
        _ = L w + d z := by ac_rfl
    exact hw'
  have hsub : DifferentiableAt ℂ
      (fun w => c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) - d z) z := by
    exact h.sub (differentiableAt_const (c := d z))
  have hL_eq : ∀ᶠ w in 𝓝 z,
      L w = c₂.chart (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) - d z := by
    filter_upwards [htransition] with w hw
    rw [hw]
    ring
  exact hsub.congr_of_eventuallyEq hL_eq

theorem complexTorusMarkingTransition_isComplexLinear_of_differentiableAt
    {τ σ : ComplexTorusParameter} {z : ℂ}
    (h : DifferentiableAt ℂ
      (complexTorusMarkingTransition τ σ) z) :
    ComplexTorusMarkingTransitionIsComplexLinear τ σ := by
  let L : ℂ ≃ₗ[ℝ] ℂ := complexTorusMarkingTransition τ σ
  have h' : DifferentiableAt ℂ (L : ℂ → ℂ) z := by
    exact h
  have hcr :=
    (differentiableAt_complex_iff_differentiableAt_real.mp h').2
  have hfderiv : fderiv ℝ (L : ℂ → ℂ) z =
      (L.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) := by
    exact L.toContinuousLinearEquiv.fderiv
  rw [hfderiv] at hcr
  change L Complex.I = Complex.I • L 1 at hcr
  intro a b
  exact real_linearMap_map_smul_complex hcr a b

theorem complexTorusCanonicalTransition_forward_chartwise
    {τ σ : ComplexTorusParameter}
    (hlinear : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    MathlibFormal.ChartwiseHolomorphicMap
      (complexTorusRiemannSurface τ).atlas
      (complexTorusRiemannSurface σ).atlas
      (complexTorusMarkedTransitionHomeomorph τ σ) := by
  refine ⟨?_⟩
  intro i j
  let c₁ := complexTorusLocalChartAt τ i
  let c₂ := complexTorusLocalChartAt σ j
  change DifferentiableOn ℂ
    (fun z => c₂.chart
      (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm z)))
    {z : ℂ |
      z ∈ c₁.chart.target ∧
        complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm z) ∈ c₂.chart.source}
  exact c₁.canonicalTransition_differentiableOn hlinear c₂

theorem complexTorusCanonicalTransition_inverse_chartwise
    {τ σ : ComplexTorusParameter}
    (hlinear : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    MathlibFormal.ChartwiseHolomorphicMap
      (complexTorusRiemannSurface σ).atlas
      (complexTorusRiemannSurface τ).atlas
      (complexTorusMarkedTransitionHomeomorph τ σ).symm := by
  have hreverse : ComplexTorusMarkingTransitionIsComplexLinear σ τ :=
    complexTorusMarkingTransition_isComplexLinear_symm hlinear
  have hforward := complexTorusCanonicalTransition_forward_chartwise
    (τ := σ) (σ := τ) hreverse
  have hcanonical :
      (complexTorusMarkedTransitionHomeomorph τ σ).symm =
        complexTorusMarkedTransitionHomeomorph σ τ := by
    apply Homeomorph.ext
    intro x
    simp [complexTorusMarkedTransitionHomeomorph]
  rw [hcanonical]
  exact hforward

@[simp] theorem complexTorusMarkedTransitionHomeomorph_apply_marking
    (τ σ : ComplexTorusParameter) (s : ComplexTorus complexTorusBaseParameter) :
    complexTorusMarkedTransitionHomeomorph τ σ
        (complexTorusMarkingHomeomorph τ s) =
      complexTorusMarkingHomeomorph σ s := by
  simp [complexTorusMarkedTransitionHomeomorph]

theorem ComplexTorusMarkedBiholomorphism.map_eq_markedTransition
    {τ σ : ComplexTorusParameter}
    (E : ComplexTorusMarkedBiholomorphism τ σ) :
    E.map = complexTorusMarkedTransitionHomeomorph τ σ := by
  apply Homeomorph.ext
  intro x
  let s := (complexTorusMarkingHomeomorph τ).symm x
  have hs : complexTorusMarkingHomeomorph τ s = x := by
    exact (complexTorusMarkingHomeomorph τ).apply_symm_apply x
  rw [← hs, E.marking_commutes]
  exact (complexTorusMarkedTransitionHomeomorph_apply_marking τ σ s).symm

theorem ComplexTorusMarkedBiholomorphism.map_unique
    {τ σ : ComplexTorusParameter}
    (E₁ E₂ : ComplexTorusMarkedBiholomorphism τ σ) :
    E₁.map = E₂.map := by
  rw [E₁.map_eq_markedTransition, E₂.map_eq_markedTransition]

structure ComplexTorusCanonicalTransitionHolomorphic
    (τ σ : ComplexTorusParameter) where
  holomorphic : @MathlibFormal.AtlasHolomorphicEquiv
    (ComplexTorus τ) (ComplexTorus σ)
    inferInstance inferInstance
    (complexTorusRiemannSurface τ).atlas
    (complexTorusRiemannSurface σ).atlas
    (complexTorusMarkedTransitionHomeomorph τ σ)

theorem complexTorusMarkingTransition_isComplexLinear_of_canonicalTransitionHolomorphic
    {τ σ : ComplexTorusParameter}
    (H : ComplexTorusCanonicalTransitionHolomorphic τ σ) :
    ComplexTorusMarkingTransitionIsComplexLinear τ σ := by
  let x : ComplexTorus τ := 0
  let y : ComplexTorus σ := complexTorusMarkedTransitionHomeomorph τ σ x
  let c₁ := complexTorusLocalChartAt τ x
  let c₂ := complexTorusLocalChartAt σ y
  let z : ℂ := c₁.chart x
  have hx : x ∈ c₁.chart.source := by
    exact complexTorusLocalChartAt_mem τ x
  have hz₁ : z ∈ c₁.chart.target := by
    exact c₁.chart.map_source hx
  have hsymm : c₁.chart.symm z = x := by
    exact c₁.chart.left_inv hx
  have hy : y ∈ c₂.chart.source := by
    exact complexTorusLocalChartAt_mem σ y
  have hz₂ : complexTorusMarkedTransitionHomeomorph τ σ
      (c₁.chart.symm z) ∈ c₂.chart.source := by
    rw [hsymm]
    exact hy
  have hz : z ∈ {w : ℂ |
      w ∈ c₁.chart.target ∧
        complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w) ∈ c₂.chart.source} :=
    ⟨hz₁, hz₂⟩
  have hS_nhds : {w : ℂ |
      w ∈ c₁.chart.target ∧
        complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w) ∈ c₂.chart.source} ∈ 𝓝 z := by
    have hcomp : ContinuousAt
        (fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w)) z := by
      have houter : ContinuousAt (complexTorusMarkedTransitionHomeomorph τ σ)
          (c₁.chart.symm z) :=
        (complexTorusMarkedTransitionHomeomorph τ σ).continuous.continuousAt
      exact houter.comp (c₁.chart.continuousAt_symm hz₁)
    have hpre :
        (fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w)) ⁻¹' c₂.chart.source ∈ 𝓝 z :=
      hcomp.preimage_mem_nhds (c₂.chart.open_source.mem_nhds hz₂)
    change c₁.chart.target ∩
      ((fun w : ℂ => complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)) ⁻¹' c₂.chart.source) ∈ 𝓝 z
    exact Filter.inter_mem (c₁.chart.open_target.mem_nhds hz₁) hpre
  have hwithin := H.holomorphic.forward.differentiable_on_charts x y
  change DifferentiableOn ℂ
    (fun w => c₂.chart
      (complexTorusMarkedTransitionHomeomorph τ σ
        (c₁.chart.symm w)))
    {w : ℂ |
      w ∈ c₁.chart.target ∧
        complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w) ∈ c₂.chart.source} at hwithin
  have hcoord : DifferentiableAt ℂ
      (fun w => c₂.chart
        (complexTorusMarkedTransitionHomeomorph τ σ
          (c₁.chart.symm w))) z :=
    (hwithin z hz).differentiableAt hS_nhds
  have hL : DifferentiableAt ℂ
      (complexTorusMarkingTransition τ σ) z :=
    c₁.canonicalTransition_differentiableAt_implies_markingTransition_differentiableAt
      c₂ hz hcoord
  exact complexTorusMarkingTransition_isComplexLinear_of_differentiableAt hL

noncomputable def complexTorusCanonicalTransitionHolomorphic_of_complexLinear
    {τ σ : ComplexTorusParameter}
    (hlinear : ComplexTorusMarkingTransitionIsComplexLinear τ σ) :
    ComplexTorusCanonicalTransitionHolomorphic τ σ where
  holomorphic :=
    { forward := complexTorusCanonicalTransition_forward_chartwise hlinear
      inverse := complexTorusCanonicalTransition_inverse_chartwise hlinear }

theorem complexTorusCanonicalTransitionHolomorphic_nonempty_iff_markingTransition_isComplexLinear
    (τ σ : ComplexTorusParameter) :
    Nonempty (ComplexTorusCanonicalTransitionHolomorphic τ σ) ↔
      ComplexTorusMarkingTransitionIsComplexLinear τ σ := by
  constructor
  · rintro ⟨H⟩
    exact complexTorusMarkingTransition_isComplexLinear_of_canonicalTransitionHolomorphic H
  · intro hlinear
    exact ⟨complexTorusCanonicalTransitionHolomorphic_of_complexLinear hlinear⟩

theorem ComplexTorusMarkedBiholomorphism.canonicalTransition_holomorphic
    {τ σ : ComplexTorusParameter}
    (E : ComplexTorusMarkedBiholomorphism τ σ) :
    ComplexTorusCanonicalTransitionHolomorphic τ σ := by
  refine { holomorphic := ?_ }
  rw [← E.map_eq_markedTransition]
  exact E.holomorphic

noncomputable def ComplexTorusCanonicalTransitionHolomorphic.toMarkedBiholomorphism
    {τ σ : ComplexTorusParameter}
    (H : ComplexTorusCanonicalTransitionHolomorphic τ σ) :
    ComplexTorusMarkedBiholomorphism τ σ where
  map := complexTorusMarkedTransitionHomeomorph τ σ
  holomorphic := H.holomorphic
  marking_commutes := fun s =>
    complexTorusMarkedTransitionHomeomorph_apply_marking τ σ s

theorem complexTorusMarkedBiholomorphism_nonempty_iff_canonicalTransitionHolomorphic_nonempty
    (τ σ : ComplexTorusParameter) :
    Nonempty (ComplexTorusMarkedBiholomorphism τ σ) ↔
      Nonempty (ComplexTorusCanonicalTransitionHolomorphic τ σ) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.canonicalTransition_holomorphic⟩
  · rintro ⟨H⟩
    exact ⟨H.toMarkedBiholomorphism⟩

theorem complexTorusMarkedBiholomorphism_nonempty_iff_markingTransition_isComplexLinear
    (τ σ : ComplexTorusParameter) :
    Nonempty (ComplexTorusMarkedBiholomorphism τ σ) ↔
      ComplexTorusMarkingTransitionIsComplexLinear τ σ := by
  exact
    (complexTorusMarkedBiholomorphism_nonempty_iff_canonicalTransitionHolomorphic_nonempty
      τ σ).trans
      (complexTorusCanonicalTransitionHolomorphic_nonempty_iff_markingTransition_isComplexLinear
        τ σ)

noncomputable def complexTorusMarkedSurface
    (τ : ComplexTorusParameter) :
    MathlibFormal.MarkedComplexRiemannSurface
      (ComplexTorus complexTorusBaseParameter) where
  carrier := ComplexTorus τ
  topology := inferInstance
  surface := complexTorusRiemannSurface τ
  marking := complexTorusMarkingHomeomorph τ

/-! ### The parameter-dependent unmarked family

The carrier of the fibre genuinely changes with the parameter because it is
the corresponding additive quotient.  The dependent-sum total space and its
continuous projection are therefore recorded before asking for a fixed
topological marking. -/

/-! The total-space topology is now generated by the universal quotient map
from parameter-and-lift coordinates.  Using only the projection-induced
topology would erase the local lift direction and could not support a
total-space chart. -/

noncomputable def complexTorusTotalMk :
    ComplexTorusParameter × ℂ → Sigma ComplexTorus :=
  fun p => ⟨p.1, complexTorusMk p.1 p.2⟩

noncomputable def complexTorusTotalTopology :
    TopologicalSpace (Sigma ComplexTorus) :=
  TopologicalSpace.coinduced complexTorusTotalMk inferInstance

theorem complexTorusTotalMk_continuous :
    @Continuous (ComplexTorusParameter × ℂ) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology complexTorusTotalMk := by
  exact continuous_coinduced_rng

theorem complexTorusTotal_projection_continuous :
    @Continuous (Sigma ComplexTorus) ComplexTorusParameter
      complexTorusTotalTopology inferInstance (fun z => z.1) := by
  change @Continuous (Sigma ComplexTorus) ComplexTorusParameter
      (TopologicalSpace.coinduced complexTorusTotalMk inferInstance)
      inferInstance (fun z => z.1)
  rw [continuous_coinduced_dom]
  simpa [complexTorusTotalMk, Function.comp_def] using
    (continuous_fst : Continuous
      (fun p : ComplexTorusParameter × ℂ => p.1))

abbrev ComplexTorusLocalParameter :=
  {τ : ℂ // τ ∈ complexTorusLocalParameterNeighborhood}

abbrev ComplexTorusLocalLift :=
  Metric.ball (0 : ℂ) ((1 : ℝ) / 4)

noncomputable def complexTorusLocalParameterPoint
    (τ : ComplexTorusLocalParameter) : ComplexTorusParameter :=
  ⟨τ.1, complexTorusLocalParameterNeighborhood_im_pos τ.2⟩

theorem complexTorusLocalParameterPoint_continuous :
    Continuous complexTorusLocalParameterPoint := by
  change Continuous (fun τ : ComplexTorusLocalParameter =>
    (⟨τ.1, complexTorusLocalParameterNeighborhood_im_pos τ.2⟩ :
      ComplexTorusParameter))
  apply continuous_induced_rng.2
  exact continuous_subtype_val

noncomputable def complexTorusLocalLiftSection :
    ComplexTorusLocalParameter × ComplexTorusLocalLift → Sigma ComplexTorus :=
  fun p => ⟨complexTorusLocalParameterPoint p.1,
    complexTorusMk (complexTorusLocalParameterPoint p.1) p.2⟩

theorem complexTorusLocalLiftSection_continuous :
    @Continuous
      (ComplexTorusLocalParameter × ComplexTorusLocalLift) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology complexTorusLocalLiftSection := by
  have hpair : Continuous
      (fun p : ComplexTorusLocalParameter × ComplexTorusLocalLift =>
        (complexTorusLocalParameterPoint p.1, (p.2 : ℂ))) :=
    (complexTorusLocalParameterPoint_continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  change @Continuous
      (ComplexTorusLocalParameter × ComplexTorusLocalLift) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology
      (fun p => complexTorusTotalMk
        (complexTorusLocalParameterPoint p.1, (p.2 : ℂ)))
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  simpa [Function.comp_def] using
    complexTorusTotalMk_continuous.comp hpair

theorem complexTorusLocalLiftSection_injective :
    Function.Injective complexTorusLocalLiftSection := by
  rintro ⟨pτ, pz⟩ ⟨qτ, qz⟩ hpq
  have hbase :
      complexTorusLocalParameterPoint pτ =
        complexTorusLocalParameterPoint qτ :=
    congrArg Sigma.fst hpq
  have hbase_coe : (pτ : ℂ) = (qτ : ℂ) := by
    exact congrArg (fun τ : ComplexTorusParameter => (τ : ℂ)) hbase
  have hp_param : pτ = qτ := Subtype.ext hbase_coe
  cases hp_param
  have hfiber :
      complexTorusMk (complexTorusLocalParameterPoint pτ) pz =
        complexTorusMk (complexTorusLocalParameterPoint pτ) qz := by
    simpa using eq_of_heq (Sigma.mk.inj_iff.mp hpq).2
  have hp_lift : (pz : ℂ) = (qz : ℂ) :=
    (complexTorusMk_injective_on_local_lift_ball
      (complexTorusLocalParameterPoint pτ) (hτ := pτ.2))
      pz.2 qz.2 hfiber
  exact Prod.ext rfl (Subtype.ext hp_lift)

theorem complexTorusTotalMk_surjective :
    Function.Surjective complexTorusTotalMk := by
  rintro ⟨τ, x⟩
  obtain ⟨z, hz⟩ :=
    QuotientAddGroup.mk'_surjective (complexTorusLattice τ).toAddSubgroup x
  refine ⟨(τ, z), ?_⟩
  simpa [complexTorusTotalMk] using congrArg (fun y => Sigma.mk τ y) hz

theorem complexTorusTotalMk_isQuotientMap :
    @Topology.IsQuotientMap (ComplexTorusParameter × ℂ) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology complexTorusTotalMk := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  exact ⟨⟨rfl⟩, complexTorusTotalMk_surjective⟩

def complexTorusTotalFiberTranslateLift (c : ℂ) :
    ComplexTorusParameter × ℂ → ComplexTorusParameter × ℂ :=
  fun p => (p.1, p.2 + c)

theorem complexTorusTotalFiberTranslateLift_continuous (c : ℂ) :
    Continuous (complexTorusTotalFiberTranslateLift c) := by
  exact continuous_fst.prodMk (continuous_snd.add continuous_const)

noncomputable def complexTorusTotalFiberTranslate (c : ℂ) :
    @Homeomorph (Sigma ComplexTorus) (Sigma ComplexTorus)
      complexTorusTotalTopology complexTorusTotalTopology := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  refine
    { toFun := fun x =>
        ⟨x.1, x.2 + complexTorusMk x.1 c⟩
      invFun := fun x =>
        ⟨x.1, x.2 - complexTorusMk x.1 c⟩
      left_inv := by
        intro x
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          simp
      right_inv := by
        intro x
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          simp
      continuous_toFun := by
        have hcomp :
            (fun x : Sigma ComplexTorus =>
                ⟨x.1, x.2 + complexTorusMk x.1 c⟩) ∘
                complexTorusTotalMk =
                complexTorusTotalMk ∘
                complexTorusTotalFiberTranslateLift c := by
          funext p
          change
            (⟨p.1, complexTorusMk p.1 p.2 + complexTorusMk p.1 c⟩ :
              Sigma ComplexTorus) =
            ⟨p.1, complexTorusMk p.1 (p.2 + c)⟩
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            simp
        apply (complexTorusTotalMk_isQuotientMap.continuous_iff).2
        rw [hcomp]
        exact complexTorusTotalMk_continuous.comp
          (complexTorusTotalFiberTranslateLift_continuous c)
      continuous_invFun := by
        have hcomp :
            (fun x : Sigma ComplexTorus =>
                ⟨x.1, x.2 - complexTorusMk x.1 c⟩) ∘
                complexTorusTotalMk =
                complexTorusTotalMk ∘
                (fun p : ComplexTorusParameter × ℂ => (p.1, p.2 - c)) := by
          funext p
          change
            (⟨p.1, complexTorusMk p.1 p.2 - complexTorusMk p.1 c⟩ :
              Sigma ComplexTorus) =
            ⟨p.1, complexTorusMk p.1 (p.2 - c)⟩
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            simp
        apply (complexTorusTotalMk_isQuotientMap.continuous_iff).2
        rw [hcomp]
        exact complexTorusTotalMk_continuous.comp
          (continuous_fst.prodMk (continuous_snd.sub continuous_const)) }

theorem complexTorusTotalFiberTranslate_totalMk (c : ℂ)
    (p : ComplexTorusParameter × ℂ) :
    complexTorusTotalFiberTranslate c (complexTorusTotalMk p) =
      complexTorusTotalMk (complexTorusTotalFiberTranslateLift c p) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    simp [complexTorusTotalMk, complexTorusTotalFiberTranslate,
      complexTorusTotalFiberTranslateLift]

def complexTorusLocalDomain : Set (ComplexTorusParameter × ℂ) :=
  {p | (p.1 : ℂ) ∈ complexTorusLocalParameterNeighborhood ∧
    p.2 ∈ Metric.ball (0 : ℂ) ((1 : ℝ) / 4)}

theorem complexTorusLocalDomain_isOpen :
    IsOpen complexTorusLocalDomain := by
  change IsOpen ((fun p : ComplexTorusParameter × ℂ => (p.1 : ℂ)) ⁻¹'
    complexTorusLocalParameterNeighborhood ∩
    Prod.snd ⁻¹' Metric.ball (0 : ℂ) ((1 : ℝ) / 4))
  exact complexTorusLocalParameterNeighborhood_isOpen.preimage
      (UpperHalfPlane.continuous_coe.comp continuous_fst) |>.inter
    (Metric.isOpen_ball.preimage continuous_snd)

noncomputable def complexTorusLatticeShift (m n : ℤ) :
    ComplexTorusParameter × ℂ ≃ₜ ComplexTorusParameter × ℂ :=
  { toFun := fun p => (p.1, p.2 + (m : ℂ) + (n : ℂ) * (p.1 : ℂ))
    invFun := fun p => (p.1, p.2 - (m : ℂ) - (n : ℂ) * (p.1 : ℂ))
    left_inv := by intro p; ext <;> simp <;> ring
    right_inv := by intro p; ext <;> simp <;> ring
    continuous_toFun := by
      have hτ : Continuous (fun p : ComplexTorusParameter × ℂ => (p.1 : ℂ)) :=
        UpperHalfPlane.continuous_coe.comp continuous_fst
      have hm : Continuous (fun _ : ComplexTorusParameter × ℂ => (m : ℂ)) :=
        continuous_const
      have hn : Continuous (fun _ : ComplexTorusParameter × ℂ => (n : ℂ)) :=
        continuous_const
      apply continuous_fst.prodMk
      exact (continuous_snd.add hm).add (hn.mul hτ)
    continuous_invFun := by
      have hτ : Continuous (fun p : ComplexTorusParameter × ℂ => (p.1 : ℂ)) :=
        UpperHalfPlane.continuous_coe.comp continuous_fst
      have hm : Continuous (fun _ : ComplexTorusParameter × ℂ => (m : ℂ)) :=
        continuous_const
      have hn : Continuous (fun _ : ComplexTorusParameter × ℂ => (n : ℂ)) :=
        continuous_const
      apply continuous_fst.prodMk
      exact (continuous_snd.sub hm).sub (hn.mul hτ) }

theorem complexTorusLatticeShift_totalMk (m n : ℤ)
    (p : ComplexTorusParameter × ℂ) :
    complexTorusTotalMk (complexTorusLatticeShift m n p) =
      complexTorusTotalMk p := by
  change Sigma.mk p.1 (complexTorusMk p.1
      (p.2 + (m : ℂ) + (n : ℂ) * (p.1 : ℂ))) =
    Sigma.mk p.1 (complexTorusMk p.1 p.2)
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply (complexTorusMk_eq_iff p.1 _ _).2
    have hm : (m : ℂ) ∈ complexTorusLattice p.1 := by
      simpa using (Submodule.smul_mem (complexTorusLattice p.1) m
        (one_mem_complexTorusLattice p.1))
    have hn : (n : ℂ) * (p.1 : ℂ) ∈ complexTorusLattice p.1 := by
      simpa [smul_eq_mul] using (Submodule.smul_mem (complexTorusLattice p.1) n
        (tau_mem_complexTorusLattice p.1))
    have hmn := add_mem hm hn
    convert hmn using 1 <;> ring

/-! The deck shifts form an honest additive action, not merely a list of
homeomorphisms.  This is the algebraic quotient structure needed before a
universal-property statement can be made: the total quotient identifies
exactly the orbits of this action. -/

noncomputable def complexTorusDeckAddAction :
    AddAction (ℤ × ℤ) (ComplexTorusParameter × ℂ) where
  vadd := fun mn p => complexTorusLatticeShift mn.1 mn.2 p
  zero_vadd := by
    intro p
    change complexTorusLatticeShift 0 0 p = p
    ext <;> simp [complexTorusLatticeShift]
  add_vadd := by
    intro mn pq p
    change complexTorusLatticeShift (mn.1 + pq.1) (mn.2 + pq.2) p =
      complexTorusLatticeShift mn.1 mn.2
        (complexTorusLatticeShift pq.1 pq.2 p)
    ext <;> simp [complexTorusLatticeShift] <;> ring

theorem complexTorusDeckAddAction_vadd
    (mn : ℤ × ℤ) (p : ComplexTorusParameter × ℂ) :
    letI : AddAction (ℤ × ℤ) (ComplexTorusParameter × ℂ) :=
      complexTorusDeckAddAction
    mn +ᵥ p = complexTorusLatticeShift mn.1 mn.2 p := by
  rfl

theorem complexTorusDeckAddAction_totalMk_invariant
    (mn : ℤ × ℤ) (p : ComplexTorusParameter × ℂ) :
    letI : AddAction (ℤ × ℤ) (ComplexTorusParameter × ℂ) :=
      complexTorusDeckAddAction
    complexTorusTotalMk (mn +ᵥ p) = complexTorusTotalMk p := by
  change complexTorusTotalMk
      (complexTorusLatticeShift mn.1 mn.2 p) = complexTorusTotalMk p
  exact complexTorusLatticeShift_totalMk mn.1 mn.2 p

theorem complexTorusDeckAddAction_orbit_eq_fiber
    (p q : ComplexTorusParameter × ℂ) :
    letI : AddAction (ℤ × ℤ) (ComplexTorusParameter × ℂ) :=
      complexTorusDeckAddAction
    (complexTorusTotalMk p = complexTorusTotalMk q ↔
      ∃ mn : ℤ × ℤ, mn +ᵥ q = p) := by
  change (complexTorusTotalMk p = complexTorusTotalMk q ↔
    ∃ mn : ℤ × ℤ,
      complexTorusLatticeShift mn.1 mn.2 q = p)
  constructor
  · intro hpq
    have hbase : p.1 = q.1 := congrArg Sigma.fst hpq
    have hquot : complexTorusMk p.1 p.2 =
        complexTorusMk p.1 q.2 := by
      have hsecond := (Sigma.mk.inj_iff.mp hpq).2
      have hq' : q = (p.1, q.2) := Prod.ext hbase.symm rfl
      rw [hq'] at hsecond
      exact eq_of_heq hsecond
    have hdmem : p.2 - q.2 ∈ complexTorusLattice p.1 :=
      (complexTorusMk_eq_iff p.1 p.2 q.2).mp hquot
    obtain ⟨m, n, hmn⟩ := complexTorusLattice_int_combination p.1 hdmem
    refine ⟨(m, n), ?_⟩
    apply Prod.ext
    · exact hbase.symm
    · change q.2 + (m : ℂ) + (n : ℂ) * (q.1 : ℂ) = p.2
      rw [← hbase]
      calc
        q.2 + (m : ℂ) + (n : ℂ) * (p.1 : ℂ) =
            q.2 + ((m : ℂ) + (n : ℂ) * (p.1 : ℂ)) := by ring
        _ = q.2 + (p.2 - q.2) := by rw [← hmn]
        _ = p.2 := by ring
  · rintro ⟨mn, hmn⟩
    rw [← hmn]
    exact complexTorusLatticeShift_totalMk mn.1 mn.2 q

def complexTorusLocalImage : Set (Sigma ComplexTorus) :=
  complexTorusTotalMk '' complexTorusLocalDomain

theorem complexTorusTotalMk_preimage_localImage :
    complexTorusTotalMk ⁻¹' complexTorusLocalImage =
      ⋃ mn : ℤ × ℤ,
        complexTorusLatticeShift mn.1 mn.2 '' complexTorusLocalDomain := by
  ext p
  constructor
  · rintro ⟨y, hy, hpy⟩
    rcases y with ⟨τ, y⟩
    have hbase : τ = p.1 := congrArg Sigma.fst hpy
    subst τ
    have hquot : complexTorusMk p.1 p.2 = complexTorusMk p.1 y := by
      simpa [complexTorusTotalMk] using hpy.symm
    have hdmem : p.2 - y ∈ complexTorusLattice p.1 :=
      (complexTorusMk_eq_iff p.1 _ _).mp hquot
    obtain ⟨m, n, hmn⟩ := complexTorusLattice_int_combination p.1 hdmem
    refine Set.mem_iUnion.2 ⟨(m, n), ?_⟩
    refine ⟨(p.1, y), hy, ?_⟩
    apply Prod.ext
    · rfl
    · change y + (m : ℂ) + (n : ℂ) * (p.1 : ℂ) = p.2
      calc
        y + (m : ℂ) + (n : ℂ) * (p.1 : ℂ) =
            y + ((m : ℂ) + (n : ℂ) * (p.1 : ℂ)) := by ring
        _ = y + (p.2 - y) := by rw [← hmn]
        _ = p.2 := by ring
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨⟨m, n⟩, ⟨q, hq, hqeq⟩⟩
    refine ⟨q, hq, ?_⟩
    rw [← hqeq]
    exact (complexTorusLatticeShift_totalMk m n q).symm

theorem complexTorusTotalMk_preimage_image
    {V : Set (ComplexTorusParameter × ℂ)} :
    complexTorusTotalMk ⁻¹' (complexTorusTotalMk '' V) =
      ⋃ mn : ℤ × ℤ,
        complexTorusLatticeShift mn.1 mn.2 '' V := by
  ext p
  constructor
  · rintro ⟨y, hy, hpy⟩
    rcases y with ⟨τ, y⟩
    have hbase : τ = p.1 := congrArg Sigma.fst hpy
    subst τ
    have hquot : complexTorusMk p.1 p.2 = complexTorusMk p.1 y := by
      simpa [complexTorusTotalMk] using hpy.symm
    have hdmem : p.2 - y ∈ complexTorusLattice p.1 :=
      (complexTorusMk_eq_iff p.1 _ _).mp hquot
    obtain ⟨m, n, hmn⟩ := complexTorusLattice_int_combination p.1 hdmem
    refine Set.mem_iUnion.2 ⟨(m, n), ?_⟩
    refine ⟨(p.1, y), hy, ?_⟩
    apply Prod.ext
    · rfl
    · change y + (m : ℂ) + (n : ℂ) * (p.1 : ℂ) = p.2
      calc
        y + (m : ℂ) + (n : ℂ) * (p.1 : ℂ) =
            y + ((m : ℂ) + (n : ℂ) * (p.1 : ℂ)) := by ring
        _ = y + (p.2 - y) := by rw [← hmn]
        _ = p.2 := by ring
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨⟨m, n⟩, ⟨q, hq, hqeq⟩⟩
    refine ⟨q, hq, ?_⟩
    rw [← hqeq]
    exact (complexTorusLatticeShift_totalMk m n q).symm

theorem complexTorusTotalMk_image_isOpen
    {V : Set (ComplexTorusParameter × ℂ)} (hV : IsOpen V) :
    @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (complexTorusTotalMk '' V) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  have hopen_pre : IsOpen (complexTorusTotalMk ⁻¹' (complexTorusTotalMk '' V)) := by
    rw [complexTorusTotalMk_preimage_image]
    exact isOpen_iUnion fun mn =>
      (complexTorusLatticeShift mn.1 mn.2).isOpenMap _ hV
  exact (complexTorusTotalMk_isQuotientMap.isCoinducing.isOpen_preimage).mp hopen_pre

theorem complexTorusLocalImage_isOpen :
    @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      complexTorusLocalImage := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  have hopen_pre : IsOpen (complexTorusTotalMk ⁻¹' complexTorusLocalImage) := by
    rw [complexTorusTotalMk_preimage_localImage]
    exact isOpen_iUnion fun mn =>
      (complexTorusLatticeShift mn.1 mn.2).isOpenMap _ complexTorusLocalDomain_isOpen
  exact (complexTorusTotalMk_isQuotientMap.isCoinducing.isOpen_preimage).mp hopen_pre

def complexTorusLocalImageAt (c : ℂ) : Set (Sigma ComplexTorus) :=
  complexTorusTotalFiberTranslate c '' complexTorusLocalImage

def complexTorusLocalDomainAt (c : ℂ) :
    Set (ComplexTorusParameter × ℂ) :=
  {p | (p.1 : ℂ) ∈ complexTorusLocalParameterNeighborhood ∧
    p.2 ∈ ComplexTorusLocalLiftAt c}

theorem complexTorusLocalDomainAt_isOpen (c : ℂ) :
    IsOpen (complexTorusLocalDomainAt c) := by
  change IsOpen ((fun p : ComplexTorusParameter × ℂ => (p.1 : ℂ)) ⁻¹'
    complexTorusLocalParameterNeighborhood ∩
    Prod.snd ⁻¹' ComplexTorusLocalLiftAt c)
  exact complexTorusLocalParameterNeighborhood_isOpen.preimage
      (UpperHalfPlane.continuous_coe.comp continuous_fst) |>.inter
    (Metric.isOpen_ball.preimage continuous_snd)

theorem complexTorusLocalImageAt_eq_totalMk_image (c : ℂ) :
    complexTorusLocalImageAt c =
      complexTorusTotalMk '' complexTorusLocalDomainAt c := by
  ext x
  constructor
  · rintro ⟨y, ⟨p, hp, hpy⟩, hxy⟩
    rw [← hpy] at hxy
    refine ⟨complexTorusTotalFiberTranslateLift c p, ?_, ?_⟩
    · rcases hp with ⟨hpτ, hpz⟩
      refine ⟨hpτ, ?_⟩
      have hpz' : dist p.2 0 < (1 : ℝ) / 4 := hpz
      change dist (p.2 + c) c < (1 : ℝ) / 4
      simpa [dist_eq_norm, sub_eq_add_neg, add_assoc] using hpz'
    · exact (complexTorusTotalFiberTranslate_totalMk c p).trans hxy
  · rintro ⟨p, hp, hpx⟩
    refine ⟨complexTorusTotalMk
      (complexTorusTotalFiberTranslateLift (-c) p), ?_, ?_⟩
    · refine ⟨complexTorusTotalFiberTranslateLift (-c) p, ?_, rfl⟩
      rcases hp with ⟨hpτ, hpz⟩
      refine ⟨hpτ, ?_⟩
      have hpz' : dist p.2 c < (1 : ℝ) / 4 := hpz
      change dist (p.2 - c) 0 < (1 : ℝ) / 4
      simpa [complexTorusTotalFiberTranslateLift, dist_eq_norm,
        sub_eq_add_neg, add_assoc] using hpz'
    · rw [complexTorusTotalFiberTranslate_totalMk]
      rw [← hpx]
      apply congrArg complexTorusTotalMk
      apply Prod.ext
      · rfl
      · simp [complexTorusTotalFiberTranslateLift]

noncomputable instance complexTorusLocalImage_topologicalSpace :
    TopologicalSpace complexTorusLocalImage :=
  TopologicalSpace.induced Subtype.val complexTorusTotalTopology

theorem complexTorusLocalImageAt_isOpen (c : ℂ) :
    @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (complexTorusLocalImageAt c) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  exact (complexTorusTotalFiberTranslate c).isOpenMap _
    complexTorusLocalImage_isOpen

theorem complexTorusLocalImageAt_isOpen_via_domain (c : ℂ) :
    @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (complexTorusLocalImageAt c) := by
  rw [complexTorusLocalImageAt_eq_totalMk_image]
  exact complexTorusTotalMk_image_isOpen
    (complexTorusLocalDomainAt_isOpen c)

noncomputable instance complexTorusLocalImageAt_topologicalSpace (c : ℂ) :
    TopologicalSpace (complexTorusLocalImageAt c) :=
  TopologicalSpace.induced Subtype.val complexTorusTotalTopology

noncomputable def complexTorusLocalImageTranslateHomeomorph (c : ℂ) :
    complexTorusLocalImage ≃ₜ complexTorusLocalImageAt c := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  have hval : Continuous (Subtype.val :
      complexTorusLocalImage → Sigma ComplexTorus) :=
    continuous_subtype_val
  have hvalAt : Continuous (Subtype.val :
      complexTorusLocalImageAt c → Sigma ComplexTorus) :=
    continuous_subtype_val
  have h_inverse (y : complexTorusLocalImageAt c) :
      (complexTorusTotalFiberTranslate c).symm y.1 ∈
        complexTorusLocalImage := by
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨z, hz, hzy⟩
    have hzy' : (complexTorusTotalFiberTranslate c).symm y = z := by
      rw [← hzy]
      exact (complexTorusTotalFiberTranslate c).symm_apply_apply z
    rw [hzy']
    exact hz
  refine
    { toFun := fun y =>
        ⟨complexTorusTotalFiberTranslate c y.1,
          ⟨y.1, y.2, rfl⟩⟩
      invFun := fun y =>
        ⟨(complexTorusTotalFiberTranslate c).symm y.1, h_inverse y⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact (complexTorusTotalFiberTranslate c).left_inv y.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact (complexTorusTotalFiberTranslate c).right_inv y.1
      continuous_toFun := by
        apply continuous_induced_rng.2
        exact (complexTorusTotalFiberTranslate c).continuous.comp
          hval
      continuous_invFun := by
        apply continuous_induced_rng.2
        exact (complexTorusTotalFiberTranslate c).symm.continuous.comp
          hvalAt }

abbrev ComplexTorusLocalDomainPoint :=
  {p : ComplexTorusParameter × ℂ // p ∈ complexTorusLocalDomain}

noncomputable def complexTorusLocalDomainSection :
    ComplexTorusLocalDomainPoint → Sigma ComplexTorus :=
  fun p => complexTorusTotalMk p.1

theorem complexTorusLocalDomainSection_continuous :
    @Continuous ComplexTorusLocalDomainPoint (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology complexTorusLocalDomainSection := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  exact complexTorusTotalMk_continuous.comp continuous_subtype_val

theorem complexTorusTotalMk_injective_on_localDomain :
    Set.InjOn complexTorusTotalMk complexTorusLocalDomain := by
  intro p hp q hq hpq
  rcases hp with ⟨hpτ, hpz⟩
  rcases hq with ⟨hqτ, hqz⟩
  have hbase : p.1 = q.1 := congrArg Sigma.fst hpq
  have hfiber : complexTorusMk p.1 p.2 = complexTorusMk p.1 q.2 := by
    have hsecond := (Sigma.mk.inj_iff.mp hpq).2
    have hq' : q = (p.1, q.2) := Prod.ext hbase.symm rfl
    rw [hq'] at hsecond
    exact eq_of_heq hsecond
  have hlift : p.2 = q.2 :=
    (complexTorusMk_injective_on_local_lift_ball p.1 hpτ)
      hpz hqz hfiber
  exact Prod.ext hbase hlift

theorem complexTorusLocalDomainSection_injective :
    Function.Injective complexTorusLocalDomainSection := by
  intro p q hpq
  apply Subtype.ext
  exact complexTorusTotalMk_injective_on_localDomain p.2 q.2 (by
    simpa [complexTorusLocalDomainSection] using hpq)

noncomputable def complexTorusLocalDomainSectionIntoImage :
    ComplexTorusLocalDomainPoint → complexTorusLocalImage :=
  fun p => ⟨complexTorusLocalDomainSection p,
    ⟨p.1, p.2, rfl⟩⟩

theorem complexTorusLocalDomainSectionIntoImage_continuous :
    @Continuous ComplexTorusLocalDomainPoint complexTorusLocalImage
      inferInstance inferInstance complexTorusLocalDomainSectionIntoImage := by
  apply continuous_induced_rng.2
  exact complexTorusLocalDomainSection_continuous

theorem complexTorusLocalDomainSectionIntoImage_injective :
    Function.Injective complexTorusLocalDomainSectionIntoImage := by
  intro p q hpq
  have hval := congrArg Subtype.val hpq
  change complexTorusLocalDomainSection p =
    complexTorusLocalDomainSection q at hval
  exact complexTorusLocalDomainSection_injective hval

theorem complexTorusLocalDomainSectionIntoImage_surjective :
    Function.Surjective complexTorusLocalDomainSectionIntoImage := by
  rintro ⟨y, hy⟩
  rcases hy with ⟨p, hp, hpy⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  exact Subtype.ext hpy

theorem complexTorusLocalDomainSectionIntoImage_isOpenMap :
    IsOpenMap complexTorusLocalDomainSectionIntoImage := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  intro s hs
  have hsource : IsOpen
      ((fun p : ComplexTorusLocalDomainPoint =>
        (p : ComplexTorusParameter × ℂ)) '' s) :=
    (complexTorusLocalDomain_isOpen.isOpenEmbedding_subtypeVal).isOpen_iff_image_isOpen.mp hs
  have htotal : @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (complexTorusTotalMk ''
        ((fun p : ComplexTorusLocalDomainPoint =>
          (p : ComplexTorusParameter × ℂ)) '' s)) :=
    complexTorusTotalMk_image_isOpen hsource
  have htarget : @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (Subtype.val '' (complexTorusLocalDomainSectionIntoImage '' s)) := by
    convert htotal using 1
    ext y
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨(p : ComplexTorusParameter × ℂ), ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨complexTorusLocalDomainSectionIntoImage p,
        ⟨p, hp, rfl⟩, rfl⟩
  exact (complexTorusLocalImage_isOpen.isOpenEmbedding_subtypeVal).isOpen_iff_image_isOpen.mpr htarget

noncomputable def complexTorusLocalDomainHomeomorph :
    ComplexTorusLocalDomainPoint ≃ₜ complexTorusLocalImage := by
  let e : ComplexTorusLocalDomainPoint ≃ complexTorusLocalImage :=
    Equiv.ofBijective complexTorusLocalDomainSectionIntoImage
      ⟨complexTorusLocalDomainSectionIntoImage_injective,
        complexTorusLocalDomainSectionIntoImage_surjective⟩
  exact e.toHomeomorphOfContinuousOpen
    complexTorusLocalDomainSectionIntoImage_continuous
    complexTorusLocalDomainSectionIntoImage_isOpenMap

noncomputable def complexTorusLocalParameterLiftHomeomorph :
    (ComplexTorusLocalParameter × ComplexTorusLocalLift) ≃ₜ
      ComplexTorusLocalDomainPoint :=
  { toFun := fun p =>
      ⟨(complexTorusLocalParameterPoint p.1, (p.2 : ℂ)),
        ⟨p.1.2, p.2.2⟩⟩
    invFun := fun p =>
      (⟨(p.1.1 : ℂ), p.2.1⟩, ⟨p.1.2, p.2.2⟩)
    left_inv := by
      rintro ⟨τ, z⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      · exact (complexTorusLocalParameterPoint_continuous.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
    continuous_invFun := by
      have hτ : Continuous (fun p : ComplexTorusLocalDomainPoint =>
          (⟨(p.1.1 : ℂ), p.2.1⟩ : ComplexTorusLocalParameter)) := by
        apply Continuous.subtype_mk
        · exact UpperHalfPlane.continuous_coe.comp
            (continuous_fst.comp continuous_subtype_val)
      have hz : Continuous (fun p : ComplexTorusLocalDomainPoint =>
          (⟨p.1.2, p.2.2⟩ : ComplexTorusLocalLift)) := by
        apply Continuous.subtype_mk
        · exact continuous_snd.comp continuous_subtype_val
      exact hτ.prodMk hz }

noncomputable def complexTorusLocalParameterLiftToTotalHomeomorph :
    (ComplexTorusLocalParameter × ComplexTorusLocalLift) ≃ₜ
      complexTorusLocalImage :=
  complexTorusLocalParameterLiftHomeomorph.trans
    complexTorusLocalDomainHomeomorph

noncomputable def complexTorusLocalParameterLiftTranslateHomeomorph (c : ℂ) :
    (ComplexTorusLocalParameter × ComplexTorusLocalLiftAt c) ≃ₜ
      (ComplexTorusLocalParameter × ComplexTorusLocalLift) := by
  have h_to (p : ComplexTorusLocalParameter × ComplexTorusLocalLiftAt c) :
      (p.2 : ℂ) - c ∈ ComplexTorusLocalLift := by
    have hz' : dist (p.2 : ℂ) c < (1 : ℝ) / 4 := p.2.2
    have hz : ‖(p.2 : ℂ) - c‖ < (1 : ℝ) / 4 := by
      simpa [dist_eq_norm] using hz'
    simpa [ComplexTorusLocalLift, Metric.mem_ball, dist_eq_norm] using hz
  have h_inv (p : ComplexTorusLocalParameter × ComplexTorusLocalLift) :
      (p.2 : ℂ) + c ∈ ComplexTorusLocalLiftAt c := by
    have hz' : dist (p.2 : ℂ) 0 < (1 : ℝ) / 4 := p.2.2
    have hz : ‖(p.2 : ℂ)‖ < (1 : ℝ) / 4 := by
      simpa [dist_eq_norm] using hz'
    simpa [ComplexTorusLocalLiftAt, Metric.mem_ball, dist_eq_norm,
      sub_eq_add_neg, add_assoc] using hz
  refine
    { toFun := fun p =>
        (p.1, ⟨(p.2 : ℂ) - c, h_to p⟩)
      invFun := fun p =>
        (p.1, ⟨(p.2 : ℂ) + c, h_inv p⟩)
      left_inv := by
        rintro ⟨τ, z⟩
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp
      right_inv := by
        rintro ⟨τ, z⟩
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp
      continuous_toFun := by
        apply continuous_fst.prodMk
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
      continuous_invFun := by
        apply continuous_fst.prodMk
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_snd).add continuous_const }

noncomputable def complexTorusLocalParameterLiftToTotalHomeomorphAt (c : ℂ) :
    (ComplexTorusLocalParameter × ComplexTorusLocalLiftAt c) ≃ₜ
      complexTorusLocalImageAt c :=
  (complexTorusLocalParameterLiftTranslateHomeomorph c).trans
    complexTorusLocalParameterLiftToTotalHomeomorph |>.trans
      (complexTorusLocalImageTranslateHomeomorph c)

/-! ### The actual two-dimensional chart target

The preceding homeomorphism has source written as a product of subtypes.  The
following equivalence repackages that source as the subtype of the open set
`complexTorusLocalDomainAt c` in `ℂ × ℂ`.  This is the precise bridge from the
quotient construction to the dimension-two chart interface in `MathlibComplex`.
-/

noncomputable def complexTorusLocalParameterLiftAtHomeomorph (c : ℂ) :
    (ComplexTorusLocalParameter × ComplexTorusLocalLiftAt c) ≃ₜ
      {p : ComplexTorusParameter × ℂ // p ∈ complexTorusLocalDomainAt c} := by
  refine
    { toFun := fun p =>
        ⟨(complexTorusLocalParameterPoint p.1, (p.2 : ℂ)),
          ⟨p.1.2, p.2.2⟩⟩
      invFun := fun p =>
        (⟨(p.1.1 : ℂ), p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      left_inv := by
        rintro ⟨τ, z⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
      right_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (complexTorusLocalParameterPoint_continuous.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := by
        have hτ : Continuous (fun p : {p : ComplexTorusParameter × ℂ //
            p ∈ complexTorusLocalDomainAt c} =>
            (⟨(p.1.1 : ℂ), p.2.1⟩ : ComplexTorusLocalParameter)) := by
          apply Continuous.subtype_mk
          exact UpperHalfPlane.continuous_coe.comp
            (continuous_fst.comp continuous_subtype_val)
        have hz : Continuous (fun p : {p : ComplexTorusParameter × ℂ //
            p ∈ complexTorusLocalDomainAt c} =>
            (⟨p.1.2, p.2.2⟩ : ComplexTorusLocalLiftAt c)) := by
          apply Continuous.subtype_mk
          exact continuous_snd.comp continuous_subtype_val
        exact hτ.prodMk hz }

def complexTorusLocalAmbientDomainAt (c : ℂ) : Set (ℂ × ℂ) :=
  complexTorusLocalParameterNeighborhood ×ˢ ComplexTorusLocalLiftAt c

theorem complexTorusLocalAmbientDomainAt_isOpen (c : ℂ) :
    IsOpen (complexTorusLocalAmbientDomainAt c) := by
  exact complexTorusLocalParameterNeighborhood_isOpen.prod Metric.isOpen_ball

noncomputable def complexTorusLocalParameterLiftAtAmbientHomeomorph (c : ℂ) :
    (ComplexTorusLocalParameter × ComplexTorusLocalLiftAt c) ≃ₜ
      {p : ℂ × ℂ // p ∈ complexTorusLocalAmbientDomainAt c} := by
  refine
    { toFun := fun p =>
        ⟨((p.1 : ℂ), (p.2 : ℂ)), ⟨p.1.2, p.2.2⟩⟩
      invFun := fun p =>
        (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      left_inv := by
        rintro ⟨τ, z⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := by
        have hτ : Continuous (fun p : {p : ℂ × ℂ //
            p ∈ complexTorusLocalAmbientDomainAt c} =>
            (⟨p.1.1, p.2.1⟩ : ComplexTorusLocalParameter)) := by
          apply Continuous.subtype_mk
          exact continuous_fst.comp continuous_subtype_val
        have hz : Continuous (fun p : {p : ℂ × ℂ //
            p ∈ complexTorusLocalAmbientDomainAt c} =>
            (⟨p.1.2, p.2.2⟩ : ComplexTorusLocalLiftAt c)) := by
          apply Continuous.subtype_mk
          exact continuous_snd.comp continuous_subtype_val
        exact hτ.prodMk hz }

noncomputable def complexTorusLocalTotalChartHomeomorphAt (c : ℂ) :
    @Homeomorph
      {x : Sigma ComplexTorus // x ∈ complexTorusLocalImageAt c}
      {p : ℂ × ℂ // p ∈ complexTorusLocalAmbientDomainAt c}
      (TopologicalSpace.induced Subtype.val complexTorusTotalTopology)
      inferInstance := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  exact (complexTorusLocalParameterLiftToTotalHomeomorphAt c).symm.trans
    (complexTorusLocalParameterLiftAtAmbientHomeomorph c)

noncomputable def complexTorusTotalSurfaceChart (c : ℂ) :
    MathlibFormal.ComplexSurfaceChart
      (Sigma ComplexTorus) complexTorusTotalTopology where
  domain := complexTorusLocalImageAt c
  range := complexTorusLocalAmbientDomainAt c
  domain_open := complexTorusLocalImageAt_isOpen_via_domain c
  range_open := complexTorusLocalAmbientDomainAt_isOpen c
  chart := complexTorusLocalTotalChartHomeomorphAt c

theorem complexTorusTotalSurfaceChart_symm_apply
    (c : ℂ) {p : ℂ × ℂ}
    (hp : p ∈ complexTorusLocalAmbientDomainAt c) :
    ((complexTorusLocalTotalChartHomeomorphAt c).symm
      (⟨p, hp⟩ : {q : ℂ × ℂ //
        q ∈ complexTorusLocalAmbientDomainAt c})).1 =
      complexTorusTotalMk
        (complexTorusLocalParameterPoint ⟨p.1, hp.1⟩, p.2) := by
  simp [complexTorusLocalTotalChartHomeomorphAt,
    complexTorusLocalParameterLiftAtAmbientHomeomorph,
    complexTorusLocalParameterLiftToTotalHomeomorphAt,
    complexTorusLocalParameterLiftTranslateHomeomorph,
    complexTorusLocalParameterLiftToTotalHomeomorph,
    complexTorusLocalParameterLiftHomeomorph,
    complexTorusLocalDomainHomeomorph,
    complexTorusLocalDomainSectionIntoImage,
    complexTorusLocalDomainSection,
    complexTorusLocalImageTranslateHomeomorph,
    complexTorusTotalFiberTranslate,
    complexTorusTotalMk]

def complexTorusLocalTotalSlice : Set (Sigma ComplexTorus) :=
  {x | (x.1 : ℂ) ∈ complexTorusLocalParameterNeighborhood}

theorem complexTorusLocalTotalSlice_eq_iUnion_localImageAt :
    complexTorusLocalTotalSlice =
      ⋃ c : ℂ, complexTorusLocalImageAt c := by
  ext x
  constructor
  · intro hx
    change (x.1 : ℂ) ∈ complexTorusLocalParameterNeighborhood at hx
    obtain ⟨z, hz⟩ :=
      QuotientAddGroup.mk'_surjective (complexTorusLattice x.1).toAddSubgroup x.2
    refine Set.mem_iUnion.2 ⟨z, ?_⟩
    let y : Sigma ComplexTorus :=
      ⟨x.1, complexTorusMk x.1 0⟩
    have hy : y ∈ complexTorusLocalImage := by
      refine ⟨(x.1, 0), ⟨hx, ?_⟩, rfl⟩
      exact Metric.mem_ball_self (by norm_num)
    refine ⟨y, hy, ?_⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      simpa [y, complexTorusTotalFiberTranslate, complexTorusMk] using hz
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨c, ⟨y, hy, hxy⟩⟩
    change (x.1 : ℂ) ∈ complexTorusLocalParameterNeighborhood
    have hbase : y.1 = x.1 := by
      simpa [complexTorusTotalFiberTranslate] using congrArg Sigma.fst hxy
    rcases hy with ⟨p, hp, hpy⟩
    rw [← hbase]
    have hparam : (y.1 : ℂ) = (p.1 : ℂ) := by
      exact congrArg (fun τ : ComplexTorusParameter => (τ : ℂ))
        (congrArg Sigma.fst hpy).symm
    rw [hparam]
    exact hp.1

noncomputable def complexTorusTotalSurfaceChartFamily :
    MathlibFormal.ComplexSurfaceChartFamily (Sigma ComplexTorus) where
  topology := complexTorusTotalTopology
  index := ℂ
  chart := complexTorusTotalSurfaceChart
  coverSet := complexTorusLocalTotalSlice
  covers := by
    intro x hx
    rw [complexTorusLocalTotalSlice_eq_iUnion_localImageAt] at hx
    rcases Set.mem_iUnion.mp hx with ⟨c, hxc⟩
    exact ⟨c, hxc⟩

/-- The local lift coordinate itself is jointly holomorphic before quotienting.
This is the analytic seed for the total-space chart; the quotient descent is
handled by the lattice-period calculation above. -/
def complexTorusAmbientLiftCoordinate : ℂ × ℂ → ℂ := Prod.snd

theorem complexTorusAmbientLiftCoordinate_differentiable :
    Differentiable ℂ complexTorusAmbientLiftCoordinate := by
  exact differentiable_snd

theorem complexTorusAmbientLiftCoordinate_differentiableOn :
    DifferentiableOn ℂ complexTorusAmbientLiftCoordinate
      (complexTorusLocalParameterNeighborhood ×ˢ
        Metric.ball (0 : ℂ) ((1 : ℝ) / 4)) := by
  exact complexTorusAmbientLiftCoordinate_differentiable.differentiableOn

/-! ### Jointly holomorphic deck transitions

The local quotient chart is not merely topological.  On the lifted parameter
space, changing a representative by the lattice element `m + n * τ` is the
affine map `(τ, z) ↦ (τ, z + m + n * τ)`.  The next two lemmas make the
holomorphic descent mechanism explicit: the quotient identifies these maps,
and the maps themselves are jointly complex-differentiable. -/

def complexTorusAmbientLatticeShift (m n : ℤ) : ℂ × ℂ → ℂ × ℂ :=
  fun p => (p.1, p.2 + (m : ℂ) + (n : ℂ) * p.1)

theorem complexTorusAmbientLatticeShift_differentiable (m n : ℤ) :
    Differentiable ℂ (complexTorusAmbientLatticeShift m n) := by
  have hm : Differentiable ℂ (fun _ : ℂ × ℂ => (m : ℂ)) :=
    by fun_prop
  have hn : Differentiable ℂ (fun _ : ℂ × ℂ => (n : ℂ)) :=
    by fun_prop
  exact differentiable_fst.prodMk
    ((differentiable_snd.add hm).add (hn.mul differentiable_fst))

theorem complexTorusAmbientLatticeShift_differentiableOn
    (m n : ℤ) {V : Set (ℂ × ℂ)} :
    DifferentiableOn ℂ (complexTorusAmbientLatticeShift m n) V := by
  exact (complexTorusAmbientLatticeShift_differentiable m n).differentiableOn

noncomputable def complexTorusAmbientLatticeShiftHomeomorph (m n : ℤ) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  { toFun := complexTorusAmbientLatticeShift m n
    invFun := complexTorusAmbientLatticeShift (-m) (-n)
    left_inv := by
      rintro ⟨τ, z⟩
      apply Prod.ext
      · rfl
      · simp [complexTorusAmbientLatticeShift]
        ring
    right_inv := by
      rintro ⟨τ, z⟩
      apply Prod.ext
      · rfl
      · simp [complexTorusAmbientLatticeShift]
        ring
    continuous_toFun :=
      (complexTorusAmbientLatticeShift_differentiable m n).continuous
    continuous_invFun :=
      (complexTorusAmbientLatticeShift_differentiable (-m) (-n)).continuous }

@[simp]
theorem complexTorusAmbientLatticeShiftHomeomorph_apply
    (m n : ℤ) (p : ℂ × ℂ) :
    complexTorusAmbientLatticeShiftHomeomorph m n p =
      complexTorusAmbientLatticeShift m n p :=
  rfl

theorem complexTorusAmbientLatticeShiftHomeomorph_symm
    (m n : ℤ) :
    (complexTorusAmbientLatticeShiftHomeomorph m n).symm =
      complexTorusAmbientLatticeShiftHomeomorph (-m) (-n) := by
  ext p <;> rfl

theorem complexTorusAmbientLatticeShiftHomeomorph_trans
    (m n p q : ℤ) :
    (complexTorusAmbientLatticeShiftHomeomorph m n).trans
        (complexTorusAmbientLatticeShiftHomeomorph p q) =
      complexTorusAmbientLatticeShiftHomeomorph (m + p) (n + q) := by
  apply Homeomorph.ext
  intro x
  rcases x with ⟨τ, z⟩
  apply Prod.ext
  · rfl
  · change
      z + (m : ℂ) + (n : ℂ) * τ + (p : ℂ) + (q : ℂ) * τ =
        z + ((m + p : ℤ) : ℂ) + ((n + q : ℤ) : ℂ) * τ
    push_cast
    ring

/-! ### Holomorphic transition sheets and the lifted overlap cover

For two centred charts, a single integer pair need not describe the whole
overlap: different connected pieces can use different lattice translates.
The correct intermediate object is therefore a family of open transition
sheets, one for each `(m,n)`.  Each sheet is an honest jointly holomorphic
affine map, and the union theorem below says that these sheets cover the
lifted overlap before passing to the quotient.
-/

def complexTorusAmbientDeckTransitionOverlap
    (c₁ c₂ : ℂ) (m n : ℤ) : Set (ℂ × ℂ) :=
  complexTorusLocalAmbientDomainAt c₁ ∩
    (complexTorusAmbientLatticeShift m n) ⁻¹'
      complexTorusLocalAmbientDomainAt c₂

theorem complexTorusAmbientDeckTransitionOverlap_isOpen
    (c₁ c₂ : ℂ) (m n : ℤ) :
    IsOpen (complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n) := by
  exact (complexTorusLocalAmbientDomainAt_isOpen c₁).inter
    ((complexTorusLocalAmbientDomainAt_isOpen c₂).preimage
      (complexTorusAmbientLatticeShift_differentiable m n).continuous)

def complexTorusAmbientDeckTransitionTarget
    (c₁ c₂ : ℂ) (m n : ℤ) : Set (ℂ × ℂ) :=
  complexTorusAmbientLatticeShiftHomeomorph m n ''
    complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n

theorem complexTorusAmbientDeckTransitionTarget_isOpen
    (c₁ c₂ : ℂ) (m n : ℤ) :
    IsOpen (complexTorusAmbientDeckTransitionTarget c₁ c₂ m n) := by
  exact (complexTorusAmbientLatticeShiftHomeomorph m n).isOpenMap _
    (complexTorusAmbientDeckTransitionOverlap_isOpen c₁ c₂ m n)

noncomputable def complexTorusAmbientDeckTransitionSheet
    (c₁ c₂ : ℂ) (m n : ℤ) :
    MathlibFormal.ComplexSurfaceTransitionSheet where
  source := complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n
  target := complexTorusAmbientDeckTransitionTarget c₁ c₂ m n
  source_open := complexTorusAmbientDeckTransitionOverlap_isOpen c₁ c₂ m n
  target_open := complexTorusAmbientDeckTransitionTarget_isOpen c₁ c₂ m n
  map := complexTorusAmbientLatticeShiftHomeomorph m n
  maps_to := by
    intro p hp
    exact ⟨p, hp, rfl⟩
  differentiableOn :=
    (complexTorusAmbientLatticeShift_differentiable m n).differentiableOn

theorem complexTorusAmbientDeckTransitionSheet_descends
    (c₁ c₂ : ℂ) (m n : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n) :
    complexTorusTotalMk
        (complexTorusLatticeShift m n
          (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2)) =
      complexTorusTotalMk
        (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2) := by
  exact complexTorusLatticeShift_totalMk m n
    (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2)

theorem complexTorusAmbientDeckTransitionSheet_source_mem_targetImage
    (c₁ c₂ : ℂ) (m n : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n) :
    complexTorusTotalMk
        (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2) ∈
      complexTorusLocalImageAt c₂ := by
  rw [complexTorusLocalImageAt_eq_totalMk_image c₂]
  refine ⟨(complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩,
      (complexTorusAmbientLatticeShift m n p).2), ?_, ?_⟩
  · exact hp.2
  · have hshift :
        (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩,
          (complexTorusAmbientLatticeShift m n p).2) =
          complexTorusLatticeShift m n
            (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2) := by
      apply Prod.ext
      · rfl
      · rfl
    rw [hshift]
    exact complexTorusAmbientDeckTransitionSheet_descends c₁ c₂ m n hp

theorem complexTorusAmbientDeckTransitionSheet_chart_apply
    (c₁ c₂ : ℂ) (m n : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n) :
    complexTorusLocalTotalChartHomeomorphAt c₂
        ⟨complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2),
          complexTorusAmbientDeckTransitionSheet_source_mem_targetImage
            c₁ c₂ m n hp⟩ =
      (⟨complexTorusAmbientLatticeShift m n p, hp.2⟩ :
        {q : ℂ × ℂ // q ∈ complexTorusLocalAmbientDomainAt c₂}) := by
  let e := complexTorusLocalTotalChartHomeomorphAt c₂
  apply e.symm.injective
  simp only [e, Homeomorph.symm_apply_apply]
  apply Subtype.ext
  rw [complexTorusTotalSurfaceChart_symm_apply c₂ hp.2]
  have hparam :
      complexTorusLocalParameterPoint
          ⟨(complexTorusAmbientLatticeShift m n p).1, hp.2.1⟩ =
        complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩ := by
    apply UpperHalfPlane.ext
    rfl
  rw [hparam]
  have hshift :
      (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩,
        (complexTorusAmbientLatticeShift m n p).2) =
        complexTorusLatticeShift m n
          (complexTorusLocalParameterPoint ⟨p.1, hp.1.1⟩, p.2) := by
    apply Prod.ext
    · rfl
    · rfl
  rw [hshift]
  exact (complexTorusAmbientDeckTransitionSheet_descends c₁ c₂ m n hp).symm

theorem complexTorusAmbientDeckTransitionOverlap_subset_chartRange
    (c₁ c₂ : ℂ) (m n : ℤ) :
    complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n ⊆
      complexTorusLocalAmbientDomainAt c₁ := by
  intro p hp
  exact hp.1

theorem complexTorusAmbientDeckTransitionTarget_subset_chartRange
    (c₁ c₂ : ℂ) (m n : ℤ) :
    complexTorusAmbientDeckTransitionTarget c₁ c₂ m n ⊆
      complexTorusLocalAmbientDomainAt c₂ := by
  rintro q ⟨p, hp, rfl⟩
  simpa using hp.2

noncomputable def complexTorusQuotientTransitionSheet
    (c₁ c₂ : ℂ) (m n : ℤ) :
    MathlibFormal.ComplexSurfaceChartTransitionSheet
      complexTorusTotalTopology
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) where
  toComplexSurfaceTransitionSheet :=
    complexTorusAmbientDeckTransitionSheet c₁ c₂ m n
  source_subset_range := by
    exact complexTorusAmbientDeckTransitionOverlap_subset_chartRange c₁ c₂ m n
  target_subset_range := by
    exact complexTorusAmbientDeckTransitionTarget_subset_chartRange c₁ c₂ m n
  compatible := by
    intro p hp
    have hp' : p ∈ complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n := by
      exact hp
    have hsource := complexTorusTotalSurfaceChart_symm_apply c₁ hp'.1
    have htarget := complexTorusTotalSurfaceChart_symm_apply c₂ hp'.2
    change
      ((complexTorusLocalTotalChartHomeomorphAt c₁).symm
        ⟨p, hp'.1⟩).1 =
        ((complexTorusLocalTotalChartHomeomorphAt c₂).symm
          ⟨complexTorusAmbientLatticeShift m n p, hp'.2⟩).1
    rw [hsource, htarget]
    have hparam :
        complexTorusLocalParameterPoint
            ⟨(complexTorusAmbientLatticeShift m n p).1, hp'.2.1⟩ =
          complexTorusLocalParameterPoint ⟨p.1, hp'.1.1⟩ := by
      apply UpperHalfPlane.ext
      rfl
    rw [hparam]
    have hshift :
        (complexTorusLocalParameterPoint ⟨p.1, hp'.1.1⟩,
          (complexTorusAmbientLatticeShift m n p).2) =
          complexTorusLatticeShift m n
            (complexTorusLocalParameterPoint ⟨p.1, hp'.1.1⟩, p.2) := by
      apply Prod.ext
      · rfl
      · rfl
    rw [hshift]
    exact (complexTorusAmbientDeckTransitionSheet_descends c₁ c₂ m n hp').symm

theorem complexTorusTotalSurfaceChartOverlap_eq_iUnion_deckSheets
    (c₁ c₂ : ℂ) :
    MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusTotalSurfaceChart c₁)
        (complexTorusTotalSurfaceChart c₂) =
      ⋃ mn : ℤ × ℤ,
        complexTorusAmbientDeckTransitionOverlap c₁ c₂ mn.1 mn.2 := by
  ext p
  constructor
  · intro hp
    change (∃ hp₁ : p ∈ complexTorusLocalAmbientDomainAt c₁,
      ((complexTorusLocalTotalChartHomeomorphAt c₁).symm
        ⟨p, hp₁⟩).1 ∈ complexTorusLocalImageAt c₂) at hp
    rcases hp with ⟨hp₁, hp₂⟩
    rw [complexTorusTotalSurfaceChart_symm_apply c₁ hp₁] at hp₂
    rw [complexTorusLocalImageAt_eq_totalMk_image c₂] at hp₂
    have hr :
        (complexTorusLocalParameterPoint ⟨p.1, hp₁.1⟩, p.2) ∈
          complexTorusTotalMk ⁻¹'
            (complexTorusTotalMk '' complexTorusLocalDomainAt c₂) := by
      exact hp₂
    rw [complexTorusTotalMk_preimage_image] at hr
    rcases Set.mem_iUnion.mp hr with ⟨mn, hmn⟩
    rcases hmn with ⟨q, hq, hqp⟩
    have hbase : q.1 =
        complexTorusLocalParameterPoint ⟨p.1, hp₁.1⟩ := by
      have h := congrArg Prod.fst hqp
      simpa [complexTorusLatticeShift] using h
    have hbaseC : (q.1 : ℂ) = p.1 := by
      have h := congrArg (fun τ : ComplexTorusParameter => (τ : ℂ)) hbase
      simpa [complexTorusLocalParameterPoint] using h
    have hfiber :
        q.2 + (mn.1 : ℂ) + (mn.2 : ℂ) * (q.1 : ℂ) = p.2 := by
      have h := congrArg Prod.snd hqp
      simpa [complexTorusLatticeShift] using h
    have hamb :
        complexTorusAmbientLatticeShift (-mn.1) (-mn.2) p =
          ((q.1 : ℂ), q.2) := by
      apply Prod.ext
      · exact hbaseC.symm
      · change p.2 + ((-mn.1 : ℤ) : ℂ) +
          ((-mn.2 : ℤ) : ℂ) * p.1 = q.2
        push_cast
        rw [← hfiber, ← hbaseC]
        ring
    have hqAmbient :
        ((q.1 : ℂ), q.2) ∈ complexTorusLocalAmbientDomainAt c₂ := by
      exact hq
    have hshiftTarget :
        complexTorusAmbientLatticeShift (-mn.1) (-mn.2) p ∈
          complexTorusLocalAmbientDomainAt c₂ := by
      rw [hamb]
      exact hqAmbient
    exact Set.mem_iUnion.mpr ⟨(-mn.1, -mn.2), ⟨hp₁, hshiftTarget⟩⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨mn, hmn⟩
    change (∃ hp₁ : p ∈ complexTorusLocalAmbientDomainAt c₁,
      ((complexTorusLocalTotalChartHomeomorphAt c₁).symm
        ⟨p, hp₁⟩).1 ∈ complexTorusLocalImageAt c₂)
    refine ⟨hmn.1, ?_⟩
    rw [complexTorusTotalSurfaceChart_symm_apply c₁ hmn.1]
    exact complexTorusAmbientDeckTransitionSheet_source_mem_targetImage
      c₁ c₂ mn.1 mn.2 hmn

theorem complexTorusAmbientDeckTransitionOverlap_subset_surfaceChartOverlap
    (c₁ c₂ : ℂ) (m n : ℤ) :
    complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n ⊆
      MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusTotalSurfaceChart c₁)
        (complexTorusTotalSurfaceChart c₂) := by
  intro p hp
  change (∃ hp₁ : p ∈ complexTorusLocalAmbientDomainAt c₁,
    ((complexTorusLocalTotalChartHomeomorphAt c₁).symm
      ⟨p, hp₁⟩).1 ∈ complexTorusLocalImageAt c₂)
  refine ⟨hp.1, ?_⟩
  rw [complexTorusTotalSurfaceChart_symm_apply c₁ hp.1]
  exact complexTorusAmbientDeckTransitionSheet_source_mem_targetImage
    c₁ c₂ m n hp

noncomputable def complexTorusQuotientTransitionCover
    (c₁ c₂ : ℂ) :
    MathlibFormal.ComplexSurfaceChartTransitionCover
      complexTorusTotalTopology
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) where
  index := ℤ × ℤ
  sheet := fun mn =>
    complexTorusQuotientTransitionSheet c₁ c₂ mn.1 mn.2
  source_subset_overlap := by
    intro mn
    exact complexTorusAmbientDeckTransitionOverlap_subset_surfaceChartOverlap
      c₁ c₂ mn.1 mn.2
  covers := by
    rw [complexTorusTotalSurfaceChartOverlap_eq_iUnion_deckSheets]
    simpa [complexTorusQuotientTransitionSheet,
      complexTorusAmbientDeckTransitionSheet]

theorem complexTorusQuotientTransitionMap_eq_deck_on_sheet
    (c₁ c₂ : ℂ) (m n : ℤ) :
    Set.EqOn
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (complexTorusTotalSurfaceChart c₁)
        (complexTorusTotalSurfaceChart c₂))
      (complexTorusAmbientLatticeShift m n)
      (complexTorusAmbientDeckTransitionOverlap c₁ c₂ m n) := by
  intro p hp
  have h :=
    MathlibFormal.ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
      (complexTorusQuotientTransitionSheet c₁ c₂ m n)
      (complexTorusAmbientDeckTransitionOverlap_subset_surfaceChartOverlap
        c₁ c₂ m n) hp
  simpa [complexTorusQuotientTransitionSheet,
    complexTorusAmbientDeckTransitionSheet] using h

theorem complexTorusTotalSurfaceChart_transition_differentiableOn
    (c₁ c₂ : ℂ) :
    DifferentiableOn ℂ
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (complexTorusTotalSurfaceChart c₁)
        (complexTorusTotalSurfaceChart c₂))
      (MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusTotalSurfaceChart c₁)
        (complexTorusTotalSurfaceChart c₂)) := by
  apply MathlibFormal.ComplexSurfaceChartTransitionCover.transition_differentiableOn
    (complexTorusQuotientTransitionCover c₁ c₂)
  intro mn
  exact complexTorusAmbientDeckTransitionOverlap_isOpen c₁ c₂ mn.1 mn.2

noncomputable def complexTorusLocalComplexSurfaceAtlas :
    MathlibFormal.ComplexSurfaceAtlas (Sigma ComplexTorus) where
  toComplexSurfaceChartFamily := complexTorusTotalSurfaceChartFamily
  transition_differentiableOn := by
    intro c₁ c₂
    exact complexTorusTotalSurfaceChart_transition_differentiableOn c₁ c₂

theorem complexTorusTotalSurfaceChart_chart_fst
    (c : ℂ) {x : Sigma ComplexTorus}
    (hx : x ∈ complexTorusLocalImageAt c) :
    ((complexTorusTotalSurfaceChart c).chart ⟨x, hx⟩).1.1 = x.1 := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace {y : Sigma ComplexTorus //
      y ∈ complexTorusLocalImageAt c} :=
    TopologicalSpace.induced Subtype.val complexTorusTotalTopology
  let q := (complexTorusTotalSurfaceChart c).chart ⟨x, hx⟩
  have hsymm :
      (complexTorusTotalSurfaceChart c).chart.symm q = ⟨x, hx⟩ := by
    exact (complexTorusTotalSurfaceChart c).chart.symm_apply_apply ⟨x, hx⟩
  have hformula :
      ((complexTorusTotalSurfaceChart c).chart.symm q).1 =
        complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) := by
    exact complexTorusTotalSurfaceChart_symm_apply c q.2
  change q.1.1 = x.1
  calc
    q.1.1 =
        (complexTorusLocalParameterPoint
          ⟨q.1.1, q.2.1⟩ : ComplexTorusParameter).1 := by rfl
    _ = (complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2)).1 := by rfl
    _ = ((complexTorusTotalSurfaceChart c).chart.symm q).1.1 := by
      exact (congrArg (fun τ : ComplexTorusParameter => (τ : ℂ))
        (congrArg Sigma.fst hformula)).symm
    _ = (x.1 : ℂ) := congrArg (fun y => (y.1.1 : ℂ)) hsymm

noncomputable def complexTorusLocalComplexSurfaceFamilyAtlas :
    MathlibFormal.ComplexSurfaceFamilyAtlas
      (Sigma ComplexTorus) ComplexTorusParameter where
  toComplexSurfaceAtlas := complexTorusLocalComplexSurfaceAtlas
  projection := fun x => x.1
  parameterCoordinate := fun τ => (τ : ℂ)
  projection_continuous := by
    letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
    change @Continuous (Sigma ComplexTorus) ComplexTorusParameter
      complexTorusTotalTopology inferInstance (fun x => x.1)
    have hproj :
        @Continuous (Sigma ComplexTorus) ComplexTorusParameter
          complexTorusTotalTopology inferInstance (fun x => x.1) :=
      complexTorusTotal_projection_continuous
    exact hproj
  chart_base_coordinate := by
    intro c x hx
    change ((complexTorusTotalSurfaceChart c).chart ⟨x, hx⟩).1.1 =
      (x.1 : ℂ)
    exact complexTorusTotalSurfaceChart_chart_fst c hx

/-! The local quotient atlas is an atlas over the parameter space in the
strong sense: every chart transition fixes the first complex coordinate.
This is the family-compatibility statement needed before interpreting the
two-dimensional atlas as a holomorphic variation of one-dimensional fibres.
-/

theorem complexTorusTotalSurfaceChart_transition_first_coordinate_eq
    (c₁ c₂ : ℂ) {p : ℂ × ℂ}
    (hp : MathlibFormal.ComplexSurfaceChart.overlap
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) p) :
    (MathlibFormal.ComplexSurfaceChart.transitionMap
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) p).1 = p.1 := by
  exact MathlibFormal.ComplexSurfaceFamilyAtlas.transition_first_coordinate_eq
    complexTorusLocalComplexSurfaceFamilyAtlas c₁ c₂ hp

def complexTorusLiftedChartOverlap
    (c₁ c₂ : ℂ) : Set (ComplexTorusParameter × ℂ) :=
  complexTorusLocalDomainAt c₁ ∩
    complexTorusTotalMk ⁻¹' complexTorusLocalImageAt c₂

theorem complexTorusLiftedChartOverlap_eq_iUnion_deckSheets
    (c₁ c₂ : ℂ) :
    complexTorusLiftedChartOverlap c₁ c₂ =
      ⋃ mn : ℤ × ℤ,
        complexTorusLocalDomainAt c₁ ∩
          (complexTorusLatticeShift mn.1 mn.2 ''
            complexTorusLocalDomainAt c₂) := by
  ext p
  constructor
  · intro hp
    have hp₂ : complexTorusTotalMk p ∈ complexTorusLocalImageAt c₂ := hp.2
    rw [complexTorusLocalImageAt_eq_totalMk_image c₂] at hp₂
    have hp₂' : p ∈ complexTorusTotalMk ⁻¹'
        (complexTorusTotalMk '' complexTorusLocalDomainAt c₂) := hp₂
    rw [complexTorusTotalMk_preimage_image] at hp₂'
    rcases Set.mem_iUnion.mp hp₂' with ⟨mn, hmn⟩
    exact Set.mem_iUnion.mpr ⟨mn, ⟨hp.1, hmn⟩⟩
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨mn, hmn⟩
    rcases hmn.2 with ⟨q, hq, hqp⟩
    refine ⟨hmn.1, ?_⟩
    rw [complexTorusLocalImageAt_eq_totalMk_image c₂]
    refine ⟨q, hq, ?_⟩
    simpa [hqp] using
      (complexTorusLatticeShift_totalMk mn.1 mn.2 q).symm

theorem complexTorusLiftedChartOverlap_deckSheet_isOpen
    (c₁ c₂ : ℂ) (m n : ℤ) :
    IsOpen (complexTorusLocalDomainAt c₁ ∩
      (complexTorusLatticeShift m n '' complexTorusLocalDomainAt c₂)) := by
  exact (complexTorusLocalDomainAt_isOpen c₁).inter
    ((complexTorusLatticeShift m n).isOpenMap _
      (complexTorusLocalDomainAt_isOpen c₂))

structure ComplexTorusDeckPseudogroupWitness where
  map : ℤ × ℤ → (ℂ × ℂ) ≃ₜ (ℂ × ℂ)
  map_eq : ∀ mn : ℤ × ℤ,
    map mn = complexTorusAmbientLatticeShiftHomeomorph mn.1 mn.2
  inverse_law : ∀ mn : ℤ × ℤ,
    (map mn).symm = map (-mn.1, -mn.2)
  composition_law : ∀ mn pq : ℤ × ℤ,
    (map mn).trans (map pq) = map (mn.1 + pq.1, mn.2 + pq.2)
  jointlyDifferentiable : ∀ mn : ℤ × ℤ,
    Differentiable ℂ (map mn)
  descends : ∀ (m n : ℤ) (p : ComplexTorusParameter × ℂ),
    complexTorusTotalMk (complexTorusLatticeShift m n p) =
      complexTorusTotalMk p

noncomputable def complexTorusDeckPseudogroupWitness :
    ComplexTorusDeckPseudogroupWitness where
  map := fun mn => complexTorusAmbientLatticeShiftHomeomorph mn.1 mn.2
  map_eq := by intro mn; rfl
  inverse_law := by
    intro mn
    rw [complexTorusAmbientLatticeShiftHomeomorph_symm]
  composition_law := by
    intro mn pq
    exact complexTorusAmbientLatticeShiftHomeomorph_trans
      mn.1 mn.2 pq.1 pq.2
  jointlyDifferentiable := by
    intro mn
    change Differentiable ℂ (complexTorusAmbientLatticeShift mn.1 mn.2)
    exact complexTorusAmbientLatticeShift_differentiable mn.1 mn.2
  descends := complexTorusLatticeShift_totalMk

theorem complexTorusAmbientLatticeShift_restricts_to_total_shift
    (m n : ℤ) (p : ComplexTorusParameter × ℂ) :
    complexTorusAmbientLatticeShift m n
        ((p.1 : ℂ), p.2) =
      (((complexTorusLatticeShift m n p).1 : ℂ),
        (complexTorusLatticeShift m n p).2) := by
  rfl

theorem complexTorusAmbientLatticeShift_preserves_total_quotient
    (m n : ℤ) (p : ComplexTorusParameter × ℂ) :
    complexTorusTotalMk (complexTorusLatticeShift m n p) =
      complexTorusTotalMk p :=
  complexTorusLatticeShift_totalMk m n p

/-- A concrete local analytic-family witness for the varying torus quotient.

The witness is deliberately local: a compact torus cannot be represented by a
single global chart with target `ℂ`.  What is recorded here is the actual
two-complex-dimensional lifted chart, together with the holomorphic deck
transformations whose quotient produces the family. -/
structure ComplexTorusLocalAnalyticFamilyWitness where
  totalChart :
    (ComplexTorusLocalParameter × ComplexTorusLocalLift) ≃ₜ
      complexTorusLocalImage
  jointLiftCoordinate : ℂ × ℂ → ℂ
  jointLiftCoordinate_eq : ∀ (τ z : ℂ),
    jointLiftCoordinate (τ, z) = z
  jointlyDifferentiable : Differentiable ℂ jointLiftCoordinate
  deckTransition : ∀ (m n : ℤ),
      Differentiable ℂ (complexTorusAmbientLatticeShift m n)
  deckPseudogroup : ComplexTorusDeckPseudogroupWitness
  deckTransition_descends : ∀ (m n : ℤ) (p : ComplexTorusParameter × ℂ),
    complexTorusTotalMk (complexTorusLatticeShift m n p) =
      complexTorusTotalMk p
  transition_preserves_parameter : ∀ (c₁ c₂ : ℂ) {p : ℂ × ℂ},
    p ∈ MathlibFormal.ComplexSurfaceChart.overlap
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) →
    (MathlibFormal.ComplexSurfaceChart.transitionMap
      (complexTorusTotalSurfaceChart c₁)
      (complexTorusTotalSurfaceChart c₂) p).1 = p.1

noncomputable def complexTorusLocalAnalyticFamilyWitness :
    ComplexTorusLocalAnalyticFamilyWitness where
  totalChart := complexTorusLocalParameterLiftToTotalHomeomorph
  jointLiftCoordinate := complexTorusAmbientLiftCoordinate
  jointLiftCoordinate_eq := by
    intro τ z
    rfl
  jointlyDifferentiable := complexTorusAmbientLiftCoordinate_differentiable
  deckTransition := complexTorusAmbientLatticeShift_differentiable
  deckPseudogroup := complexTorusDeckPseudogroupWitness
  deckTransition_descends := complexTorusAmbientLatticeShift_preserves_total_quotient
  transition_preserves_parameter := by
    intro c₁ c₂ p hp
    exact complexTorusTotalSurfaceChart_transition_first_coordinate_eq
      c₁ c₂ hp

noncomputable abbrev complexTorusSurfaceFamily :
    MathlibFormal.ComplexSurfaceFamily.UnmarkedFamily
      ComplexTorusParameter where
  fiber := ComplexTorus
  fiberTopology := fun _ => inferInstance
  surface := fun τ => complexTorusRiemannSurface τ
  totalTopology := complexTorusTotalTopology
  projection_continuous := complexTorusTotal_projection_continuous

theorem complexTorusSurfaceFamily_projection_fiber
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    (fun z : MathlibFormal.ComplexSurfaceFamily.UnmarkedTotal
      complexTorusSurfaceFamily => z.1) ⟨τ, x⟩ = τ :=
  rfl

noncomputable def complexTorusLocalUnmarkedFamilyAtlas :
    @MathlibFormal.ComplexSurfaceFamily.UnmarkedFamilyAtlas
      ComplexTorusParameter inferInstance complexTorusSurfaceFamily
      (Sigma ComplexTorus) where
  atlas := complexTorusLocalComplexSurfaceFamilyAtlas
  totalPoint := fun x => ⟨x.1, x.2⟩
  projection_eq := by
    intro x
    change x.1 = x.1
    rfl

/-- The local bridge from the concrete quotient family to the two analytic
seeds used in the Teichmüller route.  The total-space witness is jointly
complex-differentiable on the lifted cover, while `parameterLift` records the
fixed-reference marking in the parameter direction.  Keeping both fields
visible prevents the latter real-linear marking from being mistaken for a
jointly holomorphic trivialization of the quotient family. -/
structure ComplexTorusLocalMarkedAnalyticSeed where
  atlas :
    @MathlibFormal.ComplexSurfaceFamily.UnmarkedFamilyAtlas
      ComplexTorusParameter inferInstance complexTorusSurfaceFamily
      (Sigma ComplexTorus)
  parameterLift : ComplexTorusParameterLiftWitness
  totalSpace : ComplexTorusLocalAnalyticFamilyWitness
  projection_eq_fst : ∀ x : Sigma ComplexTorus,
    atlas.atlas.projection x = x.1

noncomputable def complexTorusLocalMarkedAnalyticSeed :
    ComplexTorusLocalMarkedAnalyticSeed where
  atlas := complexTorusLocalUnmarkedFamilyAtlas
  parameterLift := complexTorusParameterLiftWitness
  totalSpace := complexTorusLocalAnalyticFamilyWitness
  projection_eq_fst := by
    intro x
    change x.1 = x.1
    rfl

theorem ComplexTorusLocalMarkedAnalyticSeed.parameter_differentiable
    (S : ComplexTorusLocalMarkedAnalyticSeed) (z : ℂ) :
    DifferentiableOn ℂ
      (fun τ : ℂ => S.parameterLift.lift (τ, z))
      upperHalfPlaneSet :=
  S.parameterLift.parameter_differentiable z

theorem ComplexTorusLocalMarkedAnalyticSeed.reference_lift_eq_identity
    (S : ComplexTorusLocalMarkedAnalyticSeed) (z : ℂ) :
    S.parameterLift.lift
        ((complexTorusBaseParameter : ℂ), z) = z := by
  have hbase : (complexTorusBaseParameter : ℂ) ∈ upperHalfPlaneSet := by
    simp [complexTorusBaseParameter, upperHalfPlaneSet]
  rw [S.parameterLift.lift_eq_marking
    (complexTorusBaseParameter : ℂ) hbase z]
  simp

noncomputable def complexTorusMarkedFamilySkeleton :
    MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily
      (ComplexTorus complexTorusBaseParameter) ComplexTorusParameter where
  family := complexTorusSurfaceFamily
  marking := fun τ => complexTorusMarkingHomeomorph τ

/-! The same marked torus family, now viewed through the unified family
interface used by the holomorphic classification layer. -/

noncomputable def complexTorusMarkedSurfaceFamily :
    MathlibFormal.ComplexSurfaceFamily.Family
      (ComplexTorus complexTorusBaseParameter) ComplexTorusParameter :=
  MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
    complexTorusMarkedFamilySkeleton

/-! The concrete marked torus family now has a genuine dependent-sum
pullback.  This is the data-carrying version of “a test base maps to the
Teichmüller parameter space and receives the pulled-back marked family”; no
analytic classification claim is hidden in the construction. -/

noncomputable def complexTorusMarkedFamilyPullback
    {C : Type*} [TopologicalSpace C]
    (f : C → ComplexTorusParameter) (hf : Continuous f) :
    MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily
      (ComplexTorus complexTorusBaseParameter) C :=
  MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.canonicalPullback
    complexTorusMarkedFamilySkeleton f hf

@[simp] theorem complexTorusMarkedFamilyPullback_fiber
    {C : Type*} [TopologicalSpace C]
    (f : C → ComplexTorusParameter) (hf : Continuous f) (c : C) :
    (complexTorusMarkedFamilyPullback f hf).family.fiber c =
      ComplexTorus (f c) :=
  rfl

@[simp] theorem complexTorusMarkedFamilyPullback_marking
    {C : Type*} [TopologicalSpace C]
    (f : C → ComplexTorusParameter) (hf : Continuous f) (c : C) :
    (complexTorusMarkedFamilyPullback f hf).marking c =
      complexTorusMarkingHomeomorph (f c) :=
  rfl

/-! ### Pullback along an analytic test base

Restricting a holomorphic parameter map to its open domain gives a genuine
topological test base.  The next definition feeds its continuous map into the
concrete marked torus pullback above; the resulting fibres are not merely
propositionally related to the expected tori, but reduce to them by equality.
-/

noncomputable def complexTorusHolomorphicParameterPullback
    (F : ComplexTorusHolomorphicParameterMap) :
    MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily
      (ComplexTorus complexTorusBaseParameter)
      {c : ℂ // c ∈ F.domain} :=
  complexTorusMarkedFamilyPullback
    F.parameterPoint F.parameterPoint_continuous

/-! The canonical pullback topology comes with a concrete map back to the
original quotient total space.  This is the topological half of transporting
the local quotient atlas to an analytic test base. -/

noncomputable def complexTorusHolomorphicParameterPullback_toTotal
    (F : ComplexTorusHolomorphicParameterMap) :
    (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
      ComplexTorus (F.parameterPoint c)) → Sigma ComplexTorus :=
  fun z =>
    (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackMap
      complexTorusSurfaceFamily F.parameterPoint z).2

theorem complexTorusHolomorphicParameterPullback_toTotal_continuous
    (F : ComplexTorusHolomorphicParameterMap) :
    @Continuous
      (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
        ComplexTorus (F.parameterPoint c))
      (Sigma ComplexTorus)
      (complexTorusHolomorphicParameterPullback F).family.totalTopology
      complexTorusTotalTopology
      (complexTorusHolomorphicParameterPullback_toTotal F) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace
      (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
        ComplexTorus (F.parameterPoint c)) :=
    (complexTorusHolomorphicParameterPullback F).family.totalTopology
  have hmap :
      @Continuous
        (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
          ComplexTorus (F.parameterPoint c))
        ({c : ℂ // c ∈ F.domain} × Sigma ComplexTorus)
        (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackTopology
          complexTorusSurfaceFamily F.parameterPoint)
        inferInstance
        (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackMap
          complexTorusSurfaceFamily F.parameterPoint) :=
    continuous_induced_dom
  have hcomp :
      @Continuous
        (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
          ComplexTorus (F.parameterPoint c))
        (Sigma ComplexTorus)
        (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackTopology
          complexTorusSurfaceFamily F.parameterPoint)
        complexTorusTotalTopology
        (fun z =>
          (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackMap
            complexTorusSurfaceFamily F.parameterPoint z).2) :=
    continuous_snd.comp hmap
  change @Continuous
    (Sigma fun c : {c : ℂ // c ∈ F.domain} =>
      ComplexTorus (F.parameterPoint c))
    (Sigma ComplexTorus)
    (MathlibFormal.ComplexSurfaceFamily.unmarkedPullbackTopology
      complexTorusSurfaceFamily F.parameterPoint)
    complexTorusTotalTopology
    (complexTorusHolomorphicParameterPullback_toTotal F)
  exact hcomp

noncomputable def complexTorusHolomorphicParameterPullbackLocalImageAt
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    Set (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
      ComplexTorus (F.parameterPoint b)) :=
  complexTorusHolomorphicParameterPullback_toTotal
      F.toComplexTorusHolomorphicParameterMap ⁻¹'
    complexTorusLocalImageAt c

theorem complexTorusHolomorphicParameterPullbackLocalImageAt_isOpen
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    @IsOpen
      (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
      (complexTorusHolomorphicParameterPullbackLocalImageAt F c) := by
  letI : TopologicalSpace
      (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
      ComplexTorus (F.parameterPoint b)) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  exact complexTorusLocalImageAt_isOpen c |>.preimage
    (complexTorusHolomorphicParameterPullback_toTotal_continuous
      F.toComplexTorusHolomorphicParameterMap)

theorem complexTorusHolomorphicParameterPullbackLocalImageAt_union
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (⋃ c : ℂ, complexTorusHolomorphicParameterPullbackLocalImageAt F c) =
      (Set.univ : Set (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) := by
  ext x
  constructor
  · intro hx
    trivial
  · intro _
    have hbase :
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint x.1 : ℂ) ∈
          complexTorusLocalParameterNeighborhood :=
      F.map_mem_localNeighborhood x.1.property
    have htotal :
        complexTorusHolomorphicParameterPullback_toTotal
            F.toComplexTorusHolomorphicParameterMap x ∈
          complexTorusLocalTotalSlice := by
      change (F.toComplexTorusHolomorphicParameterMap.parameterPoint x.1 : ℂ) ∈
        complexTorusLocalParameterNeighborhood
      exact hbase
    rw [complexTorusLocalTotalSlice_eq_iUnion_localImageAt] at htotal
    rcases Set.mem_iUnion.mp htotal with ⟨c, hc⟩
    exact Set.mem_iUnion.mpr ⟨c, hc⟩

@[simp] theorem complexTorusHolomorphicParameterPullback_fiber
    (F : ComplexTorusHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) :
    (complexTorusHolomorphicParameterPullback F).family.fiber c =
      ComplexTorus (F.parameterPoint c) :=
  rfl

@[simp] theorem complexTorusHolomorphicParameterPullback_marking
    (F : ComplexTorusHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) :
    (complexTorusHolomorphicParameterPullback F).marking c =
      complexTorusMarkingHomeomorph (F.parameterPoint c) :=
  rfl

noncomputable def complexTorusLocalHolomorphicParameterPullback
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily
      (ComplexTorus complexTorusBaseParameter)
      {c : ℂ // c ∈ F.domain} :=
  complexTorusHolomorphicParameterPullback
    F.toComplexTorusHolomorphicParameterMap

@[simp] theorem complexTorusLocalHolomorphicParameterPullback_fiber
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) :
    (complexTorusLocalHolomorphicParameterPullback F).family.fiber c =
      ComplexTorus
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint c) :=
  rfl

@[simp] theorem complexTorusLocalHolomorphicParameterPullback_marking
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) :
    (complexTorusLocalHolomorphicParameterPullback F).marking c =
      complexTorusMarkingHomeomorph
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint c) :=
  rfl

/-! The local analytic test base is classified by the actual parameter map into
the marked torus family.  The realization is fibrewise the identity: the
canonical pullback has exactly the same quotient fibre, atlas, topology and
marking as the concrete pullback constructed above. -/

noncomputable def complexTorusLocalHolomorphicParameterClassification
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F)) where
  map := fun c => F.toComplexTorusHolomorphicParameterMap.parameterPoint c
  map_continuous := F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous
  realization :=
    { map := fun c => @Homeomorph.refl (ComplexTorus
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint c)) inferInstance
      holomorphic := by
        intro c
        exact MathlibFormal.AtlasHolomorphicEquiv.refl
          (complexTorusRiemannSurface
            (F.toComplexTorusHolomorphicParameterMap.parameterPoint c)).atlas
      marking_commutes := by
        intro c s
        rfl }

/-! The local classification is not merely an existence construction.  Any
holomorphic classification of the same pulled-back marked family has the
same classifying map.  The proof follows the original marked-moduli logic:
the fibrewise realization commutes with the fixed marking, hence is a marked
biholomorphism of two concrete quotient tori; the quotient-level rigidity
theorem then forces equality of their upper-half-plane parameters. -/

theorem complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (C : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))) :
    C.map =
      (fun c => F.toComplexTorusHolomorphicParameterMap.parameterPoint c) := by
  funext c
  let E : ComplexTorusMarkedBiholomorphism
      (F.toComplexTorusHolomorphicParameterMap.parameterPoint c) (C.map c) :=
    { map := C.realization.map c
      holomorphic := C.realization.holomorphic c
      marking_commutes := C.realization.marking_commutes c }
  have hlinear :
      ComplexTorusMarkingTransitionIsComplexLinear
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint c) (C.map c) :=
    (complexTorusMarkedBiholomorphism_nonempty_iff_markingTransition_isComplexLinear
      (F.toComplexTorusHolomorphicParameterMap.parameterPoint c) (C.map c)).mp ⟨E⟩
  exact (complexTorusParameter_eq_of_markingTransition_isComplexLinear hlinear).symm

theorem complexTorusLocalHolomorphicParameterClassification_map_unique
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (C₁ C₂ : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))) :
    C₁.map = C₂.map := by
  rw [complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint F C₁,
    complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint F C₂]

/-! The classification theorem is stable under composition of analytic test
    bases.  The statement below is deliberately phrased for an arbitrary
    classification witness, not only for the canonical one: marked rigidity
    forces its map to be the composite parameter map. -/

theorem complexTorusLocalHolomorphicParameterClassification_map_eq_precompose
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (C : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback (F.precompose G hG)))) :
    C.map =
      (fun c : {c : ℂ // c ∈ G.domain} =>
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
          ⟨G.map (c : ℂ), hG c.2⟩) := by
  rw [complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint
    (F.precompose G hG) C]
  funext c
  exact ComplexTorusLocalHolomorphicParameterMap.precompose_parameterPoint
    F G hG c

theorem complexTorusLocalHolomorphicParameterClassification_map_eq_precompose_precompose
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G H : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (hH : Set.MapsTo H.map H.domain G.domain)
    (C : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback
          ((F.precompose G hG).precompose H hH)))) :
    C.map =
      (fun c : {c : ℂ // c ∈ H.domain} =>
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
          ⟨G.map (H.map (c : ℂ)), hG (hH c.2)⟩) := by
  rw [complexTorusLocalHolomorphicParameterClassification_map_eq_precompose
    (F.precompose G hG) H hH C]
  funext c
  exact ComplexTorusLocalHolomorphicParameterMap.precompose_parameterPoint
    F G hG ⟨H.map c, hH c.2⟩

/-! A concrete local fine-moduli certificate for the marked genus-one test
    family.  The structure records both existence and uniqueness instead of
    hiding either one in a proposition.  It is intentionally indexed by one
    local test map: this is the honest scope of the current rigidity theorem.
-/

structure ComplexTorusLocalFineModuliWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  classification :
    MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))
  classification_map_eq_parameterPoint :
    ∀ (C : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))),
      C.map =
        (fun c => F.toComplexTorusHolomorphicParameterMap.parameterPoint c)
  classification_map_unique :
    ∀ (C₁ C₂ : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))),
      C₁.map = C₂.map

noncomputable def complexTorusLocalFineModuliWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusLocalFineModuliWitness F where
  classification := complexTorusLocalHolomorphicParameterClassification F
  classification_map_eq_parameterPoint :=
    complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint F
  classification_map_unique :=
    complexTorusLocalHolomorphicParameterClassification_map_unique F

theorem ComplexTorusLocalFineModuliWitness.classification_map_eq
    (W : ComplexTorusLocalFineModuliWitness F)
    (C : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))) :
    C.map =
      (fun c => F.toComplexTorusHolomorphicParameterMap.parameterPoint c) :=
  W.classification_map_eq_parameterPoint C

theorem ComplexTorusLocalFineModuliWitness.classification_maps_unique
    (W : ComplexTorusLocalFineModuliWitness F)
    (C₁ C₂ : MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))) :
    C₁.map = C₂.map :=
  W.classification_map_unique C₁ C₂

noncomputable def ComplexTorusLocalFineModuliWitness.precompose
    (W : ComplexTorusLocalFineModuliWitness F)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    ComplexTorusLocalFineModuliWitness (F.precompose G hG) where
  classification := complexTorusLocalHolomorphicParameterClassification
    (F.precompose G hG)
  classification_map_eq_parameterPoint := by
    intro C
    exact complexTorusLocalHolomorphicParameterClassification_map_eq_precompose
      F G hG C
  classification_map_unique := by
    intro C₁ C₂
    exact complexTorusLocalHolomorphicParameterClassification_map_unique
      (F.precompose G hG) C₁ C₂

/-! The upper half-plane is a complex manifold rather than a complex vector
space.  For this reason the analytic classifying-map certificate is recorded
in its ambient complex coordinate: the subtype-valued map is the restriction
of a map `ℂ → ℂ` that is differentiable on the test domain. -/

structure ComplexTorusLocalHolomorphicClassificationWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  classification :
    MathlibFormal.HolomorphicFamilyClassification
      complexTorusMarkedSurfaceFamily
      (MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
        (complexTorusLocalHolomorphicParameterPullback F))
  ambientClassifyingMap : ℂ → ℂ
  ambientClassifyingMap_eq : ∀ (c : ℂ) (hc : c ∈ F.domain),
    ambientClassifyingMap c =
      (classification.map ⟨c, hc⟩ : ℂ)
  ambientClassifyingMap_differentiableOn :
    DifferentiableOn ℂ ambientClassifyingMap F.domain

noncomputable def complexTorusLocalHolomorphicClassificationWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusLocalHolomorphicClassificationWitness F where
  classification := complexTorusLocalHolomorphicParameterClassification F
  ambientClassifyingMap := F.toComplexTorusHolomorphicParameterMap.map
  ambientClassifyingMap_eq := by
    intro c hc
    rfl
  ambientClassifyingMap_differentiableOn :=
    F.toComplexTorusHolomorphicParameterMap.map_differentiableOn

/-- The canonical analytic classification witness for a composed test base.
The ambient classifying map is visibly the composite, so its differentiability
is inherited from the chain rule rather than from a newly postulated field. -/
noncomputable def complexTorusLocalHolomorphicClassificationWitness.precompose
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    ComplexTorusLocalHolomorphicClassificationWitness (F.precompose G hG) where
  classification := complexTorusLocalHolomorphicParameterClassification
    (F.precompose G hG)
  ambientClassifyingMap := fun c => F.map (G.map c)
  ambientClassifyingMap_eq := by
    intro c hc
    rfl
  ambientClassifyingMap_differentiableOn :=
    F.precompose_map_differentiableOn G hG

theorem ComplexTorusLocalHolomorphicParameterMap.parameterPoint_mem_localNeighborhood
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : {c : ℂ // c ∈ F.domain}) :
    (F.toComplexTorusHolomorphicParameterMap.parameterPoint c : ℂ) ∈
      complexTorusLocalParameterNeighborhood :=
  F.map_mem_localNeighborhood c.property

theorem ComplexTorusLocalHolomorphicParameterMap.pullback_deckTransition_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap) (m n : ℤ) :
    DifferentiableOn ℂ
      (F.toComplexTorusHolomorphicParameterMap.deckTransition m n)
      (F.domain ×ˢ Metric.ball (0 : ℂ) ((1 : ℝ) / 4)) :=
  F.deckTransition_differentiableOn m n ((1 : ℝ) / 4)

theorem ComplexTorusLocalHolomorphicParameterMap.pullback_deckTransition_differentiableOn_center
    (F : ComplexTorusLocalHolomorphicParameterMap) (m n : ℤ)
    (c : ℂ) (r : ℝ) :
    DifferentiableOn ℂ
      (F.toComplexTorusHolomorphicParameterMap.deckTransition m n)
      (F.domain ×ˢ Metric.ball c r) := by
  let G := F.toComplexTorusHolomorphicParameterMap
  let S : Set (ℂ × ℂ) := F.domain ×ˢ Metric.ball c r
  have hparam : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => G.map p.1) S := by
    apply G.map_differentiableOn.fun_comp
      differentiable_fst.differentiableOn
    intro p hp
    exact hp.1
  have hm : DifferentiableOn ℂ
      (fun _ : ℂ × ℂ => (m : ℂ)) S := differentiableOn_const _
  have hn : DifferentiableOn ℂ
      (fun _ : ℂ × ℂ => (n : ℂ)) S := differentiableOn_const _
  change DifferentiableOn ℂ
    (fun p : ℂ × ℂ =>
      (p.1, p.2 + (m : ℂ) + (n : ℂ) * G.map p.1)) S
  exact differentiable_fst.differentiableOn.prodMk
    ((differentiable_snd.differentiableOn.add hm).add (hn.mul hparam))

/-! ### A genuine local chart on the analytic pullback

The open pullback images above can now be equipped with actual coordinates.
The lifted section remembers the test-base point, so it remains injective even
when the parameter map itself is not injective. -/

noncomputable def complexTorusLocalHolomorphicParameterLiftSection
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    ({b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4)) →
      Sigma fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b) :=
  fun p => ⟨p.1, complexTorusMk (F.parameterPoint p.1) p.2⟩

theorem complexTorusLocalHolomorphicParameterLiftSection_mem_localImageAt
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ)
    (p : {b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4)) :
    complexTorusLocalHolomorphicParameterLiftSection F c p ∈
      complexTorusHolomorphicParameterPullbackLocalImageAt F c := by
  change complexTorusHolomorphicParameterPullback_toTotal
      F.toComplexTorusHolomorphicParameterMap
      (complexTorusLocalHolomorphicParameterLiftSection F c p) ∈
    complexTorusLocalImageAt c
  rw [complexTorusLocalImageAt_eq_totalMk_image c]
  refine ⟨(F.parameterPoint p.1, (p.2 : ℂ)), ?_, ?_⟩
  · exact ⟨F.map_mem_localNeighborhood p.1.property, p.2.property⟩
  · rfl

theorem complexTorusLocalHolomorphicParameterLiftSection_continuous
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    @Continuous
      ({b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4))
      (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))
      inferInstance
      (complexTorusLocalHolomorphicParameterPullback F).family.totalTopology
      (complexTorusLocalHolomorphicParameterLiftSection F c) := by
  letI : TopologicalSpace
      (Sigma fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  apply continuous_induced_rng.2
  change Continuous (fun p : {b : ℂ // b ∈ F.domain} ×
      Metric.ball c ((1 : ℝ) / 4) =>
      (p.1,
        (complexTorusTotalMk
          (F.parameterPoint p.1, (p.2 : ℂ)))))
  apply continuous_fst.prodMk
  exact complexTorusTotalMk_continuous.comp
    ((F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous.comp
      continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem complexTorusLocalHolomorphicParameterLiftSection_injective
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    Function.Injective
      (complexTorusLocalHolomorphicParameterLiftSection F c) := by
  intro p q hpq
  have hbase : p.1 = q.1 := congrArg Sigma.fst hpq
  have hq : q = (p.1, q.2) := Prod.ext hbase.symm rfl
  have hfiber :
      complexTorusMk (F.parameterPoint p.1) (p.2 : ℂ) =
        complexTorusMk (F.parameterPoint p.1) (q.2 : ℂ) := by
    have hsecond := (Sigma.mk.inj_iff.mp hpq).2
    rw [← hbase] at hsecond
    exact eq_of_heq hsecond
  rw [hq]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (p.2 : ℂ) = (q.2 : ℂ)
    exact (complexTorusMk_injective_on_local_lift_ball_center
        (F.parameterPoint p.1)
        (F.parameterPoint_mem_localNeighborhood p.1) c)
        p.2.2 q.2.2 hfiber

noncomputable def complexTorusLocalHolomorphicParameterLiftSectionInverse
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
      x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} →
      ({b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4)) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (complexTorusLocalImageAt c) :=
    TopologicalSpace.induced Subtype.val complexTorusTotalTopology
  intro y
  let q := (complexTorusLocalTotalChartHomeomorphAt c)
    ⟨complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩
  exact (y.1.1, ⟨q.1.2, q.2.2⟩)

theorem complexTorusLocalHolomorphicParameterLiftSectionInverse_left
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ)
    (p : {b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4)) :
    complexTorusLocalHolomorphicParameterLiftSectionInverse F c
        ⟨complexTorusLocalHolomorphicParameterLiftSection F c p,
          complexTorusLocalHolomorphicParameterLiftSection_mem_localImageAt F c p⟩ = p := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (complexTorusLocalImageAt c) :=
    TopologicalSpace.induced Subtype.val complexTorusTotalTopology
  let y : {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
      ComplexTorus (F.parameterPoint b)) //
    x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} :=
    ⟨complexTorusLocalHolomorphicParameterLiftSection F c p,
      complexTorusLocalHolomorphicParameterLiftSection_mem_localImageAt F c p⟩
  let q := (complexTorusLocalTotalChartHomeomorphAt c)
    ⟨complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩
  have hsymm :
      ((complexTorusLocalTotalChartHomeomorphAt c).symm q).1 =
        complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap y.1 := by
    exact congrArg Subtype.val
      ((complexTorusLocalTotalChartHomeomorphAt c).symm_apply_apply _)
  have hformula :
      ((complexTorusLocalTotalChartHomeomorphAt c).symm q).1 =
        complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) := by
    exact complexTorusTotalSurfaceChart_symm_apply c q.2
  have htotal :
      complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) =
        complexTorusTotalMk (F.parameterPoint p.1, (p.2 : ℂ)) := by
    calc
      complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) =
          ((complexTorusLocalTotalChartHomeomorphAt c).symm q).1 :=
        hformula.symm
      _ = complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap y.1 := hsymm
      _ = complexTorusTotalMk (F.parameterPoint p.1, (p.2 : ℂ)) := by
        rfl
  have hbase : q.1.1 = (F.parameterPoint p.1 : ℂ) := by
    have hbase' := congrArg Sigma.fst htotal
    exact congrArg (fun τ : ComplexTorusParameter => (τ : ℂ)) hbase'
  have hparam :
      complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩ = F.parameterPoint p.1 := by
    exact UpperHalfPlane.ext hbase
  have htotal' :
      complexTorusTotalMk (F.parameterPoint p.1, q.1.2) =
        complexTorusTotalMk (F.parameterPoint p.1, (p.2 : ℂ)) := by
    rw [hparam] at htotal
    exact htotal
  have hsecond := (Sigma.mk.inj_iff.mp htotal').2
  have hfiber :
      complexTorusMk (F.parameterPoint p.1) q.1.2 =
        complexTorusMk (F.parameterPoint p.1) (p.2 : ℂ) :=
    eq_of_heq hsecond
  have hqz : q.1.2 = (p.2 : ℂ) :=
    (complexTorusMk_injective_on_local_lift_ball_center
      (F.parameterPoint p.1)
      (F.parameterPoint_mem_localNeighborhood p.1) c)
      q.2.2 p.2.2 hfiber
  change (p.1, ⟨q.1.2, q.2.2⟩) = p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact hqz

theorem complexTorusLocalHolomorphicParameterLiftSectionInverse_right
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ)
    (y : {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
      x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c}) :
    complexTorusLocalHolomorphicParameterLiftSection F c
        (complexTorusLocalHolomorphicParameterLiftSectionInverse F c y) = y := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (complexTorusLocalImageAt c) :=
    TopologicalSpace.induced Subtype.val complexTorusTotalTopology
  let q := (complexTorusLocalTotalChartHomeomorphAt c)
    ⟨complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩
  have hsymm :
      ((complexTorusLocalTotalChartHomeomorphAt c).symm q).1 =
        complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap y.1 := by
    exact congrArg Subtype.val
      ((complexTorusLocalTotalChartHomeomorphAt c).symm_apply_apply _)
  have hformula :
      ((complexTorusLocalTotalChartHomeomorphAt c).symm q).1 =
        complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) := by
    exact complexTorusTotalSurfaceChart_symm_apply c q.2
  have htotal :
      complexTorusTotalMk
          (complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩, q.1.2) =
        complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap y.1 := by
    exact hformula.symm.trans hsymm
  have hbase : q.1.1 =
      (F.parameterPoint y.1.1 : ℂ) := by
    have hbase' := congrArg Sigma.fst htotal
    exact congrArg (fun τ : ComplexTorusParameter => (τ : ℂ)) hbase'
  have hparam :
      complexTorusLocalParameterPoint ⟨q.1.1, q.2.1⟩ =
        F.parameterPoint y.1.1 := by
    exact UpperHalfPlane.ext hbase
  have htotal' :
      complexTorusTotalMk (F.parameterPoint y.1.1, q.1.2) =
        complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap y.1 := by
    rw [hparam] at htotal
    exact htotal
  have htotal'' :
      complexTorusTotalMk (F.parameterPoint y.1.1, q.1.2) =
        (⟨F.parameterPoint y.1.1, y.1.2⟩ : Sigma ComplexTorus) := by
    change complexTorusTotalMk (F.parameterPoint y.1.1, q.1.2) =
      (⟨F.parameterPoint y.1.1, y.1.2⟩ : Sigma ComplexTorus)
    exact htotal'
  have hsecond := (Sigma.mk.inj_iff.mp htotal'').2
  have hfiber :
      complexTorusMk (F.parameterPoint y.1.1) q.1.2 = y.1.2 :=
    eq_of_heq hsecond
  change (⟨y.1.1, complexTorusMk (F.parameterPoint y.1.1) q.1.2⟩ :
      Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) = y.1
  apply Sigma.ext
  · rfl
  · exact heq_of_eq hfiber

noncomputable def complexTorusLocalHolomorphicParameterLiftHomeomorphAt
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    @Homeomorph
      ({b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4))
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c}
      inferInstance
      (TopologicalSpace.induced Subtype.val
        (complexTorusHolomorphicParameterPullback
          F.toComplexTorusHolomorphicParameterMap).family.totalTopology) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace (complexTorusLocalImageAt c) :=
    TopologicalSpace.induced Subtype.val complexTorusTotalTopology
  refine
    { toFun := fun p =>
        ⟨complexTorusLocalHolomorphicParameterLiftSection F c p,
          complexTorusLocalHolomorphicParameterLiftSection_mem_localImageAt F c p⟩
      invFun := complexTorusLocalHolomorphicParameterLiftSectionInverse F c
      left_inv := by
        intro p
        exact complexTorusLocalHolomorphicParameterLiftSectionInverse_left F c p
      right_inv := by
        intro y
        apply Subtype.ext
        exact complexTorusLocalHolomorphicParameterLiftSectionInverse_right F c y
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact complexTorusLocalHolomorphicParameterLiftSection_continuous F c
      continuous_invFun := by
        have hval : Continuous (Subtype.val :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} →
            Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b))) :=
          continuous_subtype_val
        have htotal : Continuous (fun y :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} =>
            complexTorusHolomorphicParameterPullback_toTotal
              F.toComplexTorusHolomorphicParameterMap y.1) := by
          exact complexTorusHolomorphicParameterPullback_toTotal_continuous
            F.toComplexTorusHolomorphicParameterMap |>.comp hval
        have hlocal : Continuous (fun y :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} =>
            (⟨complexTorusHolomorphicParameterPullback_toTotal
                F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩ :
              {x : Sigma ComplexTorus // x ∈ complexTorusLocalImageAt c})) := by
          apply Continuous.subtype_mk
          exact htotal
        have hchart : Continuous (fun y :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} =>
            (complexTorusLocalTotalChartHomeomorphAt c)
              (⟨complexTorusHolomorphicParameterPullback_toTotal
                F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩ :
              {x : Sigma ComplexTorus // x ∈ complexTorusLocalImageAt c})) := by
          exact (complexTorusLocalTotalChartHomeomorphAt c).continuous.comp hlocal
        have hcoord : Continuous (fun y :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} =>
            (((complexTorusLocalTotalChartHomeomorphAt c)
              (⟨complexTorusHolomorphicParameterPullback_toTotal
                F.toComplexTorusHolomorphicParameterMap y.1, y.2⟩ :
              {x : Sigma ComplexTorus // x ∈ complexTorusLocalImageAt c})).1.2 : ℂ)) := by
          exact continuous_snd.comp
            (continuous_subtype_val.comp hchart)
        have hbase : Continuous (fun y :
            {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b)) //
              x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} =>
            y.1.1) := by
          have hproj :
              @Continuous
                (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
                  ComplexTorus (F.parameterPoint b)))
                {b : ℂ // b ∈ F.domain}
                (complexTorusHolomorphicParameterPullback
                  F.toComplexTorusHolomorphicParameterMap).family.totalTopology
                inferInstance (fun z => z.1) :=
            (complexTorusHolomorphicParameterPullback
              F.toComplexTorusHolomorphicParameterMap).family.projection_continuous
          exact hproj.comp hval
        apply hbase.prodMk
        apply Continuous.subtype_mk
        exact hcoord }

def complexTorusLocalHolomorphicParameterAmbientDomainAt
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) : Set (ℂ × ℂ) :=
  F.domain ×ˢ Metric.ball c ((1 : ℝ) / 4)

theorem complexTorusLocalHolomorphicParameterAmbientDomainAt_isOpen
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    IsOpen (complexTorusLocalHolomorphicParameterAmbientDomainAt F c) := by
  exact F.domain_open.prod Metric.isOpen_ball

noncomputable def complexTorusLocalHolomorphicParameterAmbientHomeomorphAt
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    ({b : ℂ // b ∈ F.domain} × Metric.ball c ((1 : ℝ) / 4)) ≃ₜ
      {p : ℂ × ℂ // p ∈
        complexTorusLocalHolomorphicParameterAmbientDomainAt F c} := by
  refine
    { toFun := fun p =>
        ⟨((p.1 : ℂ), (p.2 : ℂ)), ⟨p.1.2, p.2.2⟩⟩
      invFun := fun p =>
        (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      left_inv := by
        rintro ⟨b, z⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := by
        have hb : Continuous (fun p : {p : ℂ × ℂ // p ∈
            complexTorusLocalHolomorphicParameterAmbientDomainAt F c} =>
            (⟨p.1.1, p.2.1⟩ : {b : ℂ // b ∈ F.domain})) := by
          apply Continuous.subtype_mk
          exact continuous_fst.comp continuous_subtype_val
        have hz : Continuous (fun p : {p : ℂ × ℂ // p ∈
            complexTorusLocalHolomorphicParameterAmbientDomainAt F c} =>
            (⟨p.1.2, p.2.2⟩ : Metric.ball c ((1 : ℝ) / 4))) := by
          apply Continuous.subtype_mk
          exact continuous_snd.comp continuous_subtype_val
        exact hb.prodMk hz }

noncomputable def complexTorusLocalHolomorphicParameterSurfaceChart
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    MathlibFormal.ComplexSurfaceChart
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)))
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology where
  domain := complexTorusHolomorphicParameterPullbackLocalImageAt F c
  range := complexTorusLocalHolomorphicParameterAmbientDomainAt F c
  domain_open := complexTorusHolomorphicParameterPullbackLocalImageAt_isOpen F c
  range_open := complexTorusLocalHolomorphicParameterAmbientDomainAt_isOpen F c
  chart := by
    letI : TopologicalSpace
        (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
          ComplexTorus (F.parameterPoint b))) :=
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
    letI : TopologicalSpace
        {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
          ComplexTorus (F.parameterPoint b)) //
          x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} :=
      TopologicalSpace.induced Subtype.val
        (complexTorusHolomorphicParameterPullback
          F.toComplexTorusHolomorphicParameterMap).family.totalTopology
    exact (complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c).symm.trans
      (complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c)

noncomputable def complexTorusLocalHolomorphicParameterSurfaceChartFamily
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    MathlibFormal.ComplexSurfaceChartFamily
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) where
  topology := (complexTorusHolomorphicParameterPullback
    F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  index := ℂ
  chart := complexTorusLocalHolomorphicParameterSurfaceChart F
  coverSet := Set.univ
  covers := by
    intro x _
    have hx : x ∈ ⋃ c : ℂ,
        complexTorusHolomorphicParameterPullbackLocalImageAt F c := by
      rw [complexTorusHolomorphicParameterPullbackLocalImageAt_union F]
      trivial
    rcases Set.mem_iUnion.mp hx with ⟨c, hxc⟩
    refine ⟨c, ?_⟩
    change x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c
    exact hxc

/-! ### Parameterized deck sheets for the pulled-back charts

The same affine deck transformation that acts on the original quotient now
uses the analytic test map in its lattice coefficient.  It is an honest
homeomorphism of the ambient coordinate plane; this is the transition map
that will be descended to the pullback chart overlap. -/

noncomputable def complexTorusLocalHolomorphicParameterDeckHomeomorph
    (F : ComplexTorusLocalHolomorphicParameterMap) (m n : ℤ) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) := by
  let G := F.toComplexTorusHolomorphicParameterMap
  refine
    { toFun := G.deckTransition m n
      invFun := fun p =>
        (p.1, p.2 - (m : ℂ) - (n : ℂ) * G.map p.1)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · simp [ComplexTorusHolomorphicParameterMap.deckTransition]
          ring
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · simp [ComplexTorusHolomorphicParameterMap.deckTransition]
          ring
      continuous_toFun := by
        change Continuous (fun p : ℂ × ℂ =>
          (p.1, p.2 + (m : ℂ) + (n : ℂ) * G.map p.1))
        apply continuous_fst.prodMk
        exact (continuous_snd.add continuous_const).add
          (continuous_const.mul (G.map_continuous.comp continuous_fst))
      continuous_invFun := by
        apply continuous_fst.prodMk
        exact (continuous_snd.sub continuous_const).sub
          (continuous_const.mul (G.map_continuous.comp continuous_fst)) }

theorem complexTorusLocalHolomorphicParameterDeckHomeomorph_apply
    (F : ComplexTorusLocalHolomorphicParameterMap) (m n : ℤ)
    (p : ℂ × ℂ) :
    complexTorusLocalHolomorphicParameterDeckHomeomorph F m n p =
      (p.1, p.2 + (m : ℂ) + (n : ℂ) *
        F.toComplexTorusHolomorphicParameterMap.map p.1) := by
  rfl

def complexTorusLocalHolomorphicParameterDeckOverlap
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) : Set (ℂ × ℂ) :=
  complexTorusLocalHolomorphicParameterAmbientDomainAt F c₁ ∩
    (complexTorusLocalHolomorphicParameterDeckHomeomorph F m n) ⁻¹'
      complexTorusLocalHolomorphicParameterAmbientDomainAt F c₂

theorem complexTorusLocalHolomorphicParameterDeckOverlap_isOpen
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    IsOpen (complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n) := by
  exact (complexTorusLocalHolomorphicParameterAmbientDomainAt_isOpen F c₁).inter
    ((complexTorusLocalHolomorphicParameterAmbientDomainAt_isOpen F c₂).preimage
      (complexTorusLocalHolomorphicParameterDeckHomeomorph F m n).continuous)

def complexTorusLocalHolomorphicParameterDeckTarget
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) : Set (ℂ × ℂ) :=
  complexTorusLocalHolomorphicParameterDeckHomeomorph F m n ''
    complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n

theorem complexTorusLocalHolomorphicParameterDeckTarget_isOpen
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    IsOpen (complexTorusLocalHolomorphicParameterDeckTarget F c₁ c₂ m n) := by
  exact (complexTorusLocalHolomorphicParameterDeckHomeomorph F m n).isOpenMap _
    (complexTorusLocalHolomorphicParameterDeckOverlap_isOpen F c₁ c₂ m n)

noncomputable def complexTorusLocalHolomorphicParameterDeckTransitionSheet
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    MathlibFormal.ComplexSurfaceTransitionSheet where
  source := complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n
  target := complexTorusLocalHolomorphicParameterDeckTarget F c₁ c₂ m n
  source_open := complexTorusLocalHolomorphicParameterDeckOverlap_isOpen F c₁ c₂ m n
  target_open := complexTorusLocalHolomorphicParameterDeckTarget_isOpen F c₁ c₂ m n
  map := complexTorusLocalHolomorphicParameterDeckHomeomorph F m n
  maps_to := by
    intro p hp
    exact ⟨p, hp, rfl⟩
  differentiableOn := by
    apply (F.pullback_deckTransition_differentiableOn_center m n c₁
      ((1 : ℝ) / 4)).mono
    intro p hp
    change p ∈ F.domain ×ˢ Metric.ball c₁ ((1 : ℝ) / 4)
    exact hp.1

theorem complexTorusLocalHolomorphicParameterLiftHomeomorphAmbient_symm_apply
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ)
    {p : ℂ × ℂ}
    (hp : p ∈ complexTorusLocalHolomorphicParameterAmbientDomainAt F c) :
    ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c)
      ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c).symm
        ⟨p, hp⟩)).1 =
      (⟨⟨p.1, hp.1⟩,
        complexTorusMk (F.parameterPoint ⟨p.1, hp.1⟩) p.2⟩ :
        Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
          ComplexTorus (F.parameterPoint b))) := by
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  change ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c).toFun
      ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c).symm
        ⟨p, hp⟩)).1 = _
  rfl

theorem complexTorusLocalHolomorphicParameterDeckSheet_compatible
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n) :
    ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
      ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
        ⟨p, hp.1⟩)).1 =
      ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₂)
        ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₂).symm
          ⟨complexTorusLocalHolomorphicParameterDeckHomeomorph F m n p,
            hp.2⟩)).1 := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change complexTorusMk
        (F.parameterPoint ⟨p.1, hp.1.1⟩) p.2 =
      complexTorusMk (F.parameterPoint ⟨p.1, hp.1.1⟩)
        (p.2 + (m : ℂ) + (n : ℂ) *
          F.toComplexTorusHolomorphicParameterMap.map p.1)
    have h := complexTorusLatticeShift_totalMk m n
      (F.parameterPoint ⟨p.1, hp.1.1⟩, p.2)
    have hsecond := (Sigma.mk.inj_iff.mp h).2
    exact eq_of_heq hsecond.symm

noncomputable def complexTorusLocalHolomorphicParameterChartTransitionSheet
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    MathlibFormal.ComplexSurfaceChartTransitionSheet
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) := by
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₁} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₂} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  refine
    { toComplexSurfaceTransitionSheet :=
        complexTorusLocalHolomorphicParameterDeckTransitionSheet F c₁ c₂ m n
      source_subset_range := by
        intro p hp
        exact hp.1
      target_subset_range := by
        rintro q ⟨p, hp, rfl⟩
        exact hp.2
      compatible := by
        intro p hp
        change
          ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
            ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
              ⟨p, hp.1⟩)).1 =
            ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₂)
              ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₂).symm
                ⟨complexTorusLocalHolomorphicParameterDeckHomeomorph F m n p,
                  hp.2⟩)).1
        exact complexTorusLocalHolomorphicParameterDeckSheet_compatible
          F c₁ c₂ m n hp }

theorem complexTorusLocalHolomorphicParameterDeckOverlap_mem_iUnion_iff
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) {p : ℂ × ℂ}
    (hp₁ : p ∈ complexTorusLocalHolomorphicParameterAmbientDomainAt F c₁) :
    complexTorusTotalMk
        (F.parameterPoint ⟨p.1, hp₁.1⟩, p.2) ∈
      complexTorusLocalImageAt c₂ ↔
      p ∈ ⋃ mn : ℤ × ℤ,
        complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ mn.1 mn.2 := by
  constructor
  · intro hp₂
    rw [complexTorusLocalImageAt_eq_totalMk_image c₂] at hp₂
    rcases hp₂ with ⟨q₀, hq₀, hq₀eq⟩
    have hpre :
        (F.parameterPoint ⟨p.1, hp₁.1⟩, p.2) ∈
          complexTorusTotalMk ⁻¹'
            (complexTorusTotalMk '' complexTorusLocalDomainAt c₂) := by
      exact ⟨q₀, hq₀, hq₀eq⟩
    rw [complexTorusTotalMk_preimage_image] at hpre
    rcases Set.mem_iUnion.mp hpre with ⟨mn, hmn⟩
    rcases hmn with ⟨q, hq, hqp⟩
    have hbase : q.1 =
        F.parameterPoint ⟨p.1, hp₁.1⟩ := by
      have h := congrArg Prod.fst hqp
      simpa [complexTorusLatticeShift] using h
    have hbaseC : (q.1 : ℂ) =
        F.toComplexTorusHolomorphicParameterMap.map p.1 := by
      have h := congrArg (fun τ : ComplexTorusParameter => (τ : ℂ)) hbase
      simpa [ComplexTorusHolomorphicParameterMap.parameterPoint] using h
    have hfiber :
        q.2 + (mn.1 : ℂ) + (mn.2 : ℂ) * (q.1 : ℂ) = p.2 := by
      have h := congrArg Prod.snd hqp
      simpa [complexTorusLatticeShift] using h
    have hamb :
        complexTorusLocalHolomorphicParameterDeckHomeomorph F
            (-mn.1) (-mn.2) p = (p.1, q.2) := by
      apply Prod.ext
      · rfl
      · change p.2 + ((-mn.1 : ℤ) : ℂ) +
          ((-mn.2 : ℤ) : ℂ) *
            F.toComplexTorusHolomorphicParameterMap.map p.1 = q.2
        calc
          p.2 + ((-mn.1 : ℤ) : ℂ) +
              ((-mn.2 : ℤ) : ℂ) *
                F.toComplexTorusHolomorphicParameterMap.map p.1 =
            (q.2 + (mn.1 : ℂ) + (mn.2 : ℂ) * (q.1 : ℂ)) +
              ((-mn.1 : ℤ) : ℂ) +
              ((-mn.2 : ℤ) : ℂ) *
                F.toComplexTorusHolomorphicParameterMap.map p.1 := by
                  rw [hfiber]
          _ = q.2 := by
            rw [hbaseC]
            push_cast
            ring
    refine Set.mem_iUnion.mpr ⟨(-mn.1, -mn.2), ?_⟩
    refine ⟨hp₁, ?_⟩
    change complexTorusLocalHolomorphicParameterDeckHomeomorph F
      (-mn.1) (-mn.2) p ∈
      complexTorusLocalHolomorphicParameterAmbientDomainAt F c₂
    rw [hamb]
    exact ⟨hp₁.1, hq.2⟩
  · intro hp₂
    rcases Set.mem_iUnion.mp hp₂ with ⟨mn, hmn⟩
    rw [complexTorusLocalImageAt_eq_totalMk_image c₂]
    refine ⟨(F.parameterPoint ⟨p.1, hp₁.1⟩,
      (complexTorusLocalHolomorphicParameterDeckHomeomorph F mn.1 mn.2 p).2), ?_, ?_⟩
    · refine ⟨F.parameterPoint_mem_localNeighborhood ⟨p.1, hp₁.1⟩, ?_⟩
      exact hmn.2.2
    · change complexTorusTotalMk
          (F.parameterPoint ⟨p.1, hp₁.1⟩,
            p.2 + (mn.1 : ℂ) + (mn.2 : ℂ) *
              F.toComplexTorusHolomorphicParameterMap.map p.1) =
        complexTorusTotalMk
          (F.parameterPoint ⟨p.1, hp₁.1⟩, p.2)
      exact complexTorusLatticeShift_totalMk mn.1 mn.2
        (F.parameterPoint ⟨p.1, hp₁.1⟩, p.2)

theorem complexTorusLocalHolomorphicParameterSurfaceChartOverlap_eq_iUnion_deckSheets
    (F : ComplexTorusLocalHolomorphicParameterMap) (c₁ c₂ : ℂ) :
    MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) =
      ⋃ mn : ℤ × ℤ,
        complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ mn.1 mn.2 := by
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₁} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₂} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  ext p
  constructor
  · intro hp
    change (∃ hp₁ : p ∈
        complexTorusLocalHolomorphicParameterAmbientDomainAt F c₁,
      ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
        ⟨p, hp₁⟩).1 ∈
        complexTorusHolomorphicParameterPullbackLocalImageAt F c₂) at hp
    rcases hp with ⟨hp₁, hp₂⟩
    have hchart :
        ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
          ⟨p, hp₁⟩).1 =
          ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
            ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
              ⟨p, hp₁⟩)).1 := by
      rfl
    have hp₂' :
        complexTorusHolomorphicParameterPullback_toTotal
            F.toComplexTorusHolomorphicParameterMap
            ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
              ⟨p, hp₁⟩).1 ∈ complexTorusLocalImageAt c₂ := by
      exact hp₂
    rw [hchart] at hp₂'
    change complexTorusTotalMk
        (F.parameterPoint ⟨p.1, hp₁.1⟩, p.2) ∈
      complexTorusLocalImageAt c₂ at hp₂'
    exact (complexTorusLocalHolomorphicParameterDeckOverlap_mem_iUnion_iff
      F c₁ c₂ hp₁).1 hp₂'
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨mn, hmn⟩
    change (∃ hp₁ : p ∈
        complexTorusLocalHolomorphicParameterAmbientDomainAt F c₁,
      ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
        ⟨p, hp₁⟩).1 ∈
        complexTorusHolomorphicParameterPullbackLocalImageAt F c₂)
    refine ⟨hmn.1, ?_⟩
    have hchart :
        ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
          ⟨p, hmn.1⟩).1 =
          ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
            ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
              ⟨p, hmn.1⟩)).1 := by
      rfl
    rw [hchart]
    change complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap
        ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
          ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
            ⟨p, hmn.1⟩)).1 ∈ complexTorusLocalImageAt c₂
    change complexTorusTotalMk
        (F.parameterPoint ⟨p.1, hmn.1.1⟩, p.2) ∈
      complexTorusLocalImageAt c₂
    exact (complexTorusLocalHolomorphicParameterDeckOverlap_mem_iUnion_iff
      F c₁ c₂ hmn.1).2 (Set.mem_iUnion.mpr ⟨mn, hmn⟩)

theorem complexTorusLocalHolomorphicParameterDeckOverlap_subset_surfaceChartOverlap
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n ⊆
      MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) := by
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₁} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c₂} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  intro p hp
  change (∃ hp₁ : p ∈
      complexTorusLocalHolomorphicParameterAmbientDomainAt F c₁,
    ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
      ⟨p, hp₁⟩).1 ∈
      complexTorusHolomorphicParameterPullbackLocalImageAt F c₂)
  refine ⟨hp.1, ?_⟩
  have hchart :
      ((complexTorusLocalHolomorphicParameterSurfaceChart F c₁).chart.symm
        ⟨p, hp.1⟩).1 =
        ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
          ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
            ⟨p, hp.1⟩)).1 := by
    rfl
  rw [hchart]
  change complexTorusHolomorphicParameterPullback_toTotal
      F.toComplexTorusHolomorphicParameterMap
      ((complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c₁)
        ((complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c₁).symm
          ⟨p, hp.1⟩)).1 ∈ complexTorusLocalImageAt c₂
  change complexTorusTotalMk
      (F.parameterPoint ⟨p.1, hp.1.1⟩, p.2) ∈
    complexTorusLocalImageAt c₂
  exact (complexTorusLocalHolomorphicParameterDeckOverlap_mem_iUnion_iff
    F c₁ c₂ hp.1).2 (Set.mem_iUnion.mpr ⟨(m, n), hp⟩)

noncomputable def complexTorusLocalHolomorphicParameterChartTransitionCover
    (F : ComplexTorusLocalHolomorphicParameterMap) (c₁ c₂ : ℂ) :
    @MathlibFormal.ComplexSurfaceChartTransitionCover
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)))
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) where
  index := ℤ × ℤ
  sheet := fun mn =>
    complexTorusLocalHolomorphicParameterChartTransitionSheet
      F c₁ c₂ mn.1 mn.2
  source_subset_overlap := by
    intro mn p hp
    rw [complexTorusLocalHolomorphicParameterSurfaceChartOverlap_eq_iUnion_deckSheets
      F c₁ c₂]
    exact Set.mem_iUnion.mpr ⟨mn, hp⟩
  covers := by
    rw [complexTorusLocalHolomorphicParameterSurfaceChartOverlap_eq_iUnion_deckSheets
      F c₁ c₂]
    intro p hp
    exact hp

theorem complexTorusLocalHolomorphicParameterChartTransitionMap_eq_deck_on_sheet
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c₁ c₂ : ℂ) (m n : ℤ) :
    Set.EqOn
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂))
      (complexTorusLocalHolomorphicParameterDeckHomeomorph F m n)
      (complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n) := by
  intro p hp
  have h :=
    MathlibFormal.ComplexSurfaceChartTransitionSheet.transitionMap_eq_map_on_source
      (complexTorusLocalHolomorphicParameterChartTransitionSheet
        F c₁ c₂ m n)
      (complexTorusLocalHolomorphicParameterDeckOverlap_subset_surfaceChartOverlap
        F c₁ c₂ m n)
      hp
  convert h using 1

theorem complexTorusLocalHolomorphicParameterSurfaceChart_transition_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap) (c₁ c₂ : ℂ) :
    DifferentiableOn ℂ
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂))
      (MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂)) := by
  apply MathlibFormal.ComplexSurfaceChartTransitionCover.transition_differentiableOn
    (complexTorusLocalHolomorphicParameterChartTransitionCover F c₁ c₂)
  intro mn
  exact complexTorusLocalHolomorphicParameterDeckOverlap_isOpen
    F c₁ c₂ mn.1 mn.2

noncomputable def complexTorusLocalHolomorphicParameterComplexSurfaceAtlas
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    MathlibFormal.ComplexSurfaceAtlas
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
  { toComplexSurfaceChartFamily :=
      complexTorusLocalHolomorphicParameterSurfaceChartFamily F
    transition_differentiableOn := by
      intro c₁ c₂
      exact complexTorusLocalHolomorphicParameterSurfaceChart_transition_differentiableOn
        F c₁ c₂ }

/-! The preceding atlas covers the whole pulled-back total space.  The next
    wrapper records that its first complex coordinate is the parameter of the
    actual base point, so it can be used as a genuine global family atlas
    rather than only as an isolated surface atlas. -/

theorem complexTorusLocalHolomorphicParameterSurfaceChart_chart_base_coordinate
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ)
    {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
      ComplexTorus (F.parameterPoint b))}
    (hx : x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c) :
    ((complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
      ⟨x, hx⟩).1.1 =
      (x.1 : ℂ) := by
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      {x : Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)) //
        x ∈ complexTorusHolomorphicParameterPullbackLocalImageAt F c} :=
    TopologicalSpace.induced Subtype.val
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  let L := complexTorusLocalHolomorphicParameterLiftHomeomorphAt F c
  let A := complexTorusLocalHolomorphicParameterAmbientHomeomorphAt F c
  let p := (complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
    ⟨x, hx⟩
  change (A (L.symm ⟨x, hx⟩)).1.1 = (x.1 : ℂ)
  have hp : A.symm p = L.symm ⟨x, hx⟩ := by
    change A.symm (A (L.symm ⟨x, hx⟩)) = L.symm ⟨x, hx⟩
    exact A.symm_apply_apply _
  have hL :=
    complexTorusLocalHolomorphicParameterLiftHomeomorphAmbient_symm_apply
      F c (p := p.1) p.2
  have hLp :
      L (A.symm p) = ⟨x, hx⟩ := by
    rw [hp]
    exact L.apply_symm_apply _
  have hpoint :
      (⟨⟨p.1.1, p.2.1⟩,
        complexTorusMk (F.parameterPoint ⟨p.1.1, p.2.1⟩) p.1.2⟩ :
        Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
          ComplexTorus (F.parameterPoint b))) = x := by
    have hL'' :
        (L (A.symm p)).1 =
          (⟨⟨p.1.1, p.2.1⟩,
            complexTorusMk (F.parameterPoint ⟨p.1.1, p.2.1⟩) p.1.2⟩ :
            Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
              ComplexTorus (F.parameterPoint b))) := by
      simpa using hL
    rw [hLp] at hL''
    exact hL''.symm
  have hfirst := congrArg Sigma.fst hpoint
  have hfirst' := congrArg (fun b : {b : ℂ // b ∈ F.domain} => (b : ℂ)) hfirst
  exact hfirst'

noncomputable def complexTorusLocalHolomorphicParameterComplexSurfaceFamilyAtlas
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    @MathlibFormal.ComplexSurfaceFamilyAtlas
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)))
      {b : ℂ // b ∈ F.domain} inferInstance where
  toComplexSurfaceAtlas :=
    complexTorusLocalHolomorphicParameterComplexSurfaceAtlas F
  projection := fun x => x.1
  parameterCoordinate := fun b => (b : ℂ)
  projection_continuous := by
    change @Continuous
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)))
      {b : ℂ // b ∈ F.domain}
      (complexTorusLocalHolomorphicParameterPullback F).family.totalTopology
      inferInstance (fun x => x.1)
    exact (complexTorusLocalHolomorphicParameterPullback F).family.projection_continuous
  chart_base_coordinate := by
    intro c x hx
    exact complexTorusLocalHolomorphicParameterSurfaceChart_chart_base_coordinate
      F c hx

noncomputable def complexTorusLocalHolomorphicParameterGlobalFamily
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    @MathlibFormal.ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (ComplexTorus complexTorusBaseParameter)
      {b : ℂ // b ∈ F.domain} inferInstance inferInstance where
  family :=
    MathlibFormal.ComplexSurfaceFamily.MarkedUnmarkedFamily.toFamily
      (complexTorusLocalHolomorphicParameterPullback F)
  atlas := complexTorusLocalHolomorphicParameterComplexSurfaceFamilyAtlas F
  cover_univ := by
    apply Set.Subset.antisymm
    · intro x _
      trivial
    · intro x _
      trivial
  topology_eq := by
    change (complexTorusLocalHolomorphicParameterComplexSurfaceAtlas F).topology =
      (complexTorusLocalHolomorphicParameterPullback F).family.totalTopology
    rfl
  projection_eq := by
    intro x
    rfl

/-! ### Transition differences and the discrete lattice

The next two statements isolate the actual transition calculation.  A local
coordinate is a lift through the quotient map; two such lifts differ by a
lattice element.  Since the lattice is discrete, continuity then makes the
difference constant on every preconnected overlap.  Holomorphicity of the
resulting translation is deferred to the atlas layer below this topological
calculation.
-/

theorem complexTorus_lift_difference_mem_lattice
    (τ : ComplexTorusParameter) {S : Set ℂ} {u v : ℂ → ℂ}
    (hu : ∀ z, z ∈ S → complexTorusMk τ (u z) = complexTorusMk τ z)
    (hv : ∀ z, z ∈ S → complexTorusMk τ (v z) = complexTorusMk τ z) :
    ∀ z, z ∈ S → u z - v z ∈ complexTorusLattice τ := by
  intro z hz
  apply (complexTorusMk_eq_iff τ (u z) (v z)).mp
  rw [hu z hz, hv z hz]

theorem complexTorus_openPartialHomeomorph_transition_mem_lattice
    (τ : ComplexTorusParameter)
    (e₁ e₂ : OpenPartialHomeomorph (ComplexTorus τ) ℂ)
    (h₁ : ∀ x, x ∈ e₁.source → complexTorusMk τ (e₁ x) = x)
    (h₂ : ∀ x, x ∈ e₂.source → complexTorusMk τ (e₂ x) = x)
    {z : ℂ} (hz : z ∈ e₁.target)
    (hz₂ : e₁.symm z ∈ e₂.source) :
    e₂ (e₁.symm z) - z ∈ complexTorusLattice τ := by
  apply (complexTorusMk_eq_iff τ (e₂ (e₁.symm z)) z).mp
  have hz₁ : e₁.symm z ∈ e₁.source := e₁.map_target hz
  have h₁z := h₁ (e₁.symm z) hz₁
  have h₂z := h₂ (e₁.symm z) hz₂
  rw [h₂z, ← h₁z, e₁.right_inv hz]

theorem complexTorus_transition_difference_constant
    {α : Type*} [TopologicalSpace α]
    (τ : ComplexTorusParameter) {S : Set α} {u v : α → ℂ}
    (hS : IsPreconnected S) (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hmem : ∀ x, x ∈ S → u x - v x ∈ complexTorusLattice τ) :
    ∃ latticeShift ∈ complexTorusLattice τ,
      Set.EqOn (fun x => u x - v x) (fun _ => latticeShift) S := by
  have hdisc : IsDiscrete (complexTorusLattice τ : Set ℂ) := by
    exact DiscreteTopology.isDiscrete
  exact hS.eqOn_const_of_mapsTo hdisc (hu.sub hv) hmem
    ⟨0, (complexTorusLattice τ).zero_mem⟩

theorem ComplexTorusLocalChart.transition_eq_translation_on_preconnected_overlap
    {τ : ComplexTorusParameter} (c₁ c₂ : ComplexTorusLocalChart τ)
    (hS : IsPreconnected
      (MathlibFormal.ComplexChart.overlap
        c₁.toComplexChart c₂.toComplexChart)) :
    ∃ d ∈ complexTorusLattice τ,
      Set.EqOn
        (MathlibFormal.ComplexChart.transitionMap
          c₁.toComplexChart c₂.toComplexChart)
        (fun z => z + d)
        (MathlibFormal.ComplexChart.overlap
          c₁.toComplexChart c₂.toComplexChart) := by
  let S : Set ℂ := MathlibFormal.ComplexChart.overlap
    c₁.toComplexChart c₂.toComplexChart
  let u : ℂ → ℂ := fun z => c₂.chart (c₁.chart.symm z)
  have hu : ContinuousOn u S := by
    dsimp [u]
    exact c₂.chart.continuousOn.comp
      (c₁.chart.continuousOn_symm.mono fun z hz => hz.1)
      (fun z hz => hz.2)
  have hv : ContinuousOn (fun z : ℂ => z) S := continuousOn_id
  have hmem : ∀ z, z ∈ S → u z - z ∈ complexTorusLattice τ := by
    intro z hz
    exact ComplexTorusLocalChart.transition_difference_mem_lattice c₁ c₂ hz
  obtain ⟨d, hd, hconst⟩ :=
    complexTorus_transition_difference_constant τ hS hu hv hmem
  refine ⟨d, hd, ?_⟩
  intro z hz
  have hz' : u z - z = d := hconst hz
  have hz'' : u z = d + z := (sub_eq_iff_eq_add).mp hz'
  have htransition :
      c₁.toComplexChart.transitionMap c₂.toComplexChart z = u z := by
    rfl
  rw [htransition]
  simpa [add_comm] using hz''

theorem complexTorusMk_periodic
    (τ : ComplexTorusParameter) (z w : ℂ)
    (hw : w ∈ complexTorusLattice τ) :
    complexTorusMk τ (z + w) = complexTorusMk τ z := by
  change ((z + w : ℂ) : ComplexTorus τ) = (z : ComplexTorus τ)
  rw [show ((z + w : ℂ) : ComplexTorus τ) =
      (z : ComplexTorus τ) + (w : ComplexTorus τ) by rfl]
  rw [show (w : ComplexTorus τ) = 0 by
    exact (complexTorusMk_eq_zero_iff τ w).2 hw]
  simp

theorem complexTorus_isCompact (τ : ComplexTorusParameter) :
    CompactSpace (ComplexTorus τ) := by
  rw [← isCompact_univ_iff]
  have hcompact := IsZLattice.isCompact_range_of_periodic
    (complexTorusLattice τ) (complexTorusMk τ)
    (complexTorusMk_continuous τ)
    (complexTorusMk_periodic τ)
  have hsurj : Function.Surjective (complexTorusMk τ) := by
    simpa [complexTorusMk] using
      (QuotientAddGroup.mk'_surjective
        (complexTorusLattice τ).toAddSubgroup)
  rw [hsurj.range_eq] at hcompact
  exact hcompact

theorem complexTorus_has_no_global_complex_plane_homeomorph
    (τ : ComplexTorusParameter) (e : ℂ ≃ₜ ComplexTorus τ) : False := by
  letI : CompactSpace (ComplexTorus τ) := complexTorus_isCompact τ
  letI : CompactSpace ℂ := e.symm.compactSpace
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ)) inferInstance

/-- The upper-half-plane translation corresponding to the modular generator T. -/
def complexTorusTranslate (τ : ComplexTorusParameter) : ComplexTorusParameter :=
  ⟨1 + (τ : ℂ), by simpa using τ.im_pos⟩

@[simp]
theorem complexTorusTranslate_coe (τ : ComplexTorusParameter) :
    (complexTorusTranslate τ : ℂ) = 1 + (τ : ℂ) :=
  rfl

theorem complexTorusTranslate_eq_modular_T_smul
    (τ : ComplexTorusParameter) :
    complexTorusTranslate τ = ModularGroup.T • τ := by
  apply UpperHalfPlane.ext
  have h := congrArg (fun z : MathlibUpperHalfPlane => (z : ℂ))
    (translation_generator τ)
  simpa [complexTorusTranslate] using h.symm

/-- The lattice is unchanged by the integral change of period basis
  (1, tau) maps to (1, 1 + tau). -/
theorem complexTorusLattice_translate_eq (τ : ComplexTorusParameter) :
    complexTorusLattice (complexTorusTranslate τ) =
      complexTorusLattice τ := by
  apply le_antisymm
  · rw [complexTorusLattice]
    refine Submodule.span_le.2 ?_
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact one_mem_complexTorusLattice τ
    · exact add_mem (one_mem_complexTorusLattice τ) (tau_mem_complexTorusLattice τ)
  · rw [complexTorusLattice]
    refine Submodule.span_le.2 ?_
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact one_mem_complexTorusLattice (complexTorusTranslate τ)
    · have hmem := tau_mem_complexTorusLattice (complexTorusTranslate τ)
      rw [complexTorusTranslate_coe] at hmem
      simpa using sub_mem hmem
        (one_mem_complexTorusLattice (complexTorusTranslate τ))

/-! The modular translation already identifies the two quotient groups:
the underlying map is induced by the identity on the universal cover, while
the period-lattice equality supplies the descent condition. -/

noncomputable def complexTorusTranslateAddEquiv
    (τ : ComplexTorusParameter) :
    ComplexTorus (complexTorusTranslate τ) ≃+
      ComplexTorus τ :=
  QuotientAddGroup.congr
    (complexTorusLattice (complexTorusTranslate τ)).toAddSubgroup
    (complexTorusLattice τ).toAddSubgroup
    (AddEquiv.refl ℂ) (by
      rw [complexTorusLattice_translate_eq τ]
      simp)

@[simp] theorem complexTorusTranslateAddEquiv_mk
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusTranslateAddEquiv τ
      (complexTorusMk (complexTorusTranslate τ) z) =
        complexTorusMk τ z :=
  rfl

theorem complexTorusTranslateAddEquiv_continuous
    (τ : ComplexTorusParameter) :
    Continuous (complexTorusTranslateAddEquiv τ) := by
  have hfun :
      (complexTorusTranslateAddEquiv τ ∘
          complexTorusMk (complexTorusTranslate τ)) =
        complexTorusMk τ := by
    funext z
    exact complexTorusTranslateAddEquiv_mk τ z
  apply (isQuotientMap_quotient_mk'.continuous_iff).2
  change Continuous (complexTorusTranslateAddEquiv τ ∘
    complexTorusMk (complexTorusTranslate τ))
  rw [hfun]
  exact complexTorusMk_continuous τ

theorem complexTorusTranslateAddEquiv_symm_continuous
    (τ : ComplexTorusParameter) :
    Continuous (complexTorusTranslateAddEquiv τ).symm := by
  have hfun :
      ((complexTorusTranslateAddEquiv τ).symm ∘ complexTorusMk τ) =
        complexTorusMk (complexTorusTranslate τ) := by
    funext z
    apply (complexTorusTranslateAddEquiv τ).injective
    simp
  apply (isQuotientMap_quotient_mk'.continuous_iff).2
  change Continuous ((complexTorusTranslateAddEquiv τ).symm ∘
    complexTorusMk τ)
  rw [hfun]
  exact complexTorusMk_continuous (complexTorusTranslate τ)

noncomputable def complexTorusTranslateHomeomorph
    (τ : ComplexTorusParameter) :
    @Homeomorph
      (ComplexTorus (complexTorusTranslate τ)) (ComplexTorus τ)
      inferInstance inferInstance :=
  let hopen : IsOpenMap (complexTorusTranslateAddEquiv τ).toEquiv :=
    IsOpenMap.of_inverse
      (f := (complexTorusTranslateAddEquiv τ).toEquiv)
      (f' := (complexTorusTranslateAddEquiv τ).toEquiv.symm)
      (by
        change Continuous (complexTorusTranslateAddEquiv τ).symm
        exact complexTorusTranslateAddEquiv_symm_continuous τ)
      (complexTorusTranslateAddEquiv τ).toEquiv.right_inv
      (complexTorusTranslateAddEquiv τ).toEquiv.left_inv
  (complexTorusTranslateAddEquiv τ).toEquiv.toHomeomorphOfContinuousOpen
    (complexTorusTranslateAddEquiv_continuous τ)
    hopen

@[simp] theorem complexTorusTranslateHomeomorph_mk
    (τ : ComplexTorusParameter) (z : ℂ) :
    complexTorusTranslateHomeomorph τ
      (complexTorusMk (complexTorusTranslate τ) z) =
        complexTorusMk τ z :=
  rfl

theorem complexTorus_translate_compact
    (τ : ComplexTorusParameter) :
    CompactSpace (ComplexTorus (complexTorusTranslate τ)) :=
  complexTorus_isCompact (complexTorusTranslate τ)

end Teichmuller
