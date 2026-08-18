import Teichmuller.MathlibBeltramiDifferential

namespace Teichmuller

open MeasureTheory

noncomputable section

/-!
### The constant-coefficient affine model

For a constant coefficient `μ` with `‖μ‖ < 1`, the real-linear map

`z ↦ (1 + μ)⁻¹ (z + μ ̅z)`

is an explicit normalized solution of the Beltrami equation.  This is not the
measurable Riemann mapping theorem; it is the first nonzero coefficient model
against which the later existence and uniqueness layer can be tested.
-/

theorem constantBeltramiAffineMap_hasFDerivAt
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    HasFDerivAt (constantBeltramiAffineMap μ)
      ((1 + μ)⁻¹ •
        (ContinuousLinearMap.id ℝ ℂ +
          μ • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) z := by
  let D : ℂ →L[ℝ] ℂ :=
    (1 + μ)⁻¹ •
      (ContinuousLinearMap.id ℝ ℂ +
        μ • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  have hD : HasFDerivAt (D : ℂ → ℂ) D z := D.hasFDerivAt
  have hfun : constantBeltramiAffineMap μ = (D : ℂ → ℂ) := by
    funext w
    simp [D, constantBeltramiAffineMap, Complex.conjCLE_apply]
    ring
  rw [hfun]
  exact hD

theorem constantBeltramiAffineMap_fderiv
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    fderiv ℝ (constantBeltramiAffineMap μ) z =
      (1 + μ)⁻¹ •
        (ContinuousLinearMap.id ℝ ℂ +
          μ • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := by
  exact (constantBeltramiAffineMap_hasFDerivAt hμ z).fderiv

theorem constantBeltramiAffineMap_complexDerivativePart
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    complexDerivativePart (fderiv ℝ (constantBeltramiAffineMap μ) z) =
      (1 + μ)⁻¹ := by
  rw [constantBeltramiAffineMap_fderiv hμ z]
  simp [complexDerivativePart, Complex.conjCLE_apply, pow_two, Complex.I_mul_I]
  field_simp [constantBeltrami_one_add_ne_zero hμ]
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  rw [hI2]
  ring

theorem constantBeltramiAffineMap_antiComplexDerivativePart
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    antiComplexDerivativePart (fderiv ℝ (constantBeltramiAffineMap μ) z) =
      μ * (1 + μ)⁻¹ := by
  rw [constantBeltramiAffineMap_fderiv hμ z]
  simp [antiComplexDerivativePart, Complex.conjCLE_apply, pow_two, Complex.I_mul_I]
  field_simp [constantBeltrami_one_add_ne_zero hμ]
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  rw [hI2]
  ring

theorem constantBeltramiAffineMap_beltramiEquation
    (m : Measure ℂ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    BeltramiEquationOn (constantBeltramiCoefficient m μ hμ)
      (constantBeltramiAffineMap μ) Set.univ := by
  intro z hz
  refine ⟨(constantBeltramiAffineMap_hasFDerivAt hμ z).differentiableAt, ?_⟩
  rw [constantBeltramiAffineMap_complexDerivativePart hμ z,
    constantBeltramiAffineMap_antiComplexDerivativePart hμ z]
  simp [constantBeltramiCoefficient_apply]

theorem constantBeltramiAffineMap_fderivBeltramiCoefficient
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    fderivBeltramiCoefficient (constantBeltramiAffineMap μ) z = μ := by
  unfold fderivBeltramiCoefficient
  rw [differentialBeltramiCoefficient]
  rw [constantBeltramiAffineMap_complexDerivativePart hμ z,
    constantBeltramiAffineMap_antiComplexDerivativePart hμ z]
  field_simp [constantBeltrami_one_add_ne_zero hμ]

theorem constantBeltramiAffineMap_normalized_zero
    {μ : ℂ} (hμ : ‖μ‖ < 1) :
    constantBeltramiAffineMap μ 0 = 0 := by
  simp [constantBeltramiAffineMap]

theorem constantBeltramiAffineMap_normalized_one
    {μ : ℂ} (hμ : ‖μ‖ < 1) :
    constantBeltramiAffineMap μ 1 = 1 := by
  simp [constantBeltramiAffineMap]
  field_simp [constantBeltrami_one_add_ne_zero hμ]

noncomputable def constantBeltramiAffinePointwiseWitness
    (m : Measure ℂ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    PointwiseNormalizedBeltramiHomeomorph
      (constantBeltramiCoefficient m μ hμ) where
  map := constantBeltramiAffineHomeomorph μ hμ
  mapAtInfinity := Homeomorph.onePointCongr
    (constantBeltramiAffineHomeomorph μ hμ)
  mapAtInfinity_coe := by
    intro z
    rfl
  mapAtInfinity_infty := by
    rfl
  equation_ae := beltramiEquationOn_univ_toAE
    (constantBeltramiAffineMap_beltramiEquation m hμ)
  map_zero := constantBeltramiAffineMap_normalized_zero hμ
  map_one := constantBeltramiAffineMap_normalized_one hμ
  equation := constantBeltramiAffineMap_beltramiEquation m hμ

@[simp] theorem constantBeltramiAffinePointwiseWitness_map_apply
    (m : Measure ℂ) {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    (constantBeltramiAffinePointwiseWitness m hμ).map z =
      constantBeltramiAffineMap μ z :=
  rfl

abbrev constantBeltramiParameter := {μ : ℂ // ‖μ‖ < 1}

noncomputable def constantBeltramiAffinePointwiseFamilyWitness
    (m : Measure ℂ) :
    PointwiseNormalizedBeltramiFamilyWitness constantBeltramiParameter m where
  coefficient := fun μ => constantBeltramiCoefficient m μ.1 μ.2
  coefficient_parameter_continuous := by
    intro z
    simpa using
      (continuous_subtype_val :
        Continuous (fun μ : constantBeltramiParameter => (μ : ℂ)))
  solution := fun μ => constantBeltramiAffinePointwiseWitness m μ.2
  solution_totalMap_continuous := by
    have hden :
        Continuous (fun p : constantBeltramiParameter × ℂ =>
          (1 + (p.1 : ℂ))⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro p
        exact constantBeltrami_one_add_ne_zero p.1.2
    have hmap :
        Continuous (fun p : constantBeltramiParameter × ℂ =>
          (1 + (p.1 : ℂ))⁻¹ *
            (p.2 + (p.1 : ℂ) * (starRingEnd ℂ) p.2)) := by
      fun_prop
    simpa [constantBeltramiAffinePointwiseWitness,
      constantBeltramiAffineHomeomorph, constantBeltramiAffineMap] using hmap

theorem constantBeltramiAffinePointwiseFamilyWitness_coefficient_apply
    (m : Measure ℂ) (μ : constantBeltramiParameter) (z : ℂ) :
    (constantBeltramiAffinePointwiseFamilyWitness m).coefficient μ z = μ :=
  rfl

theorem constantBeltramiAffinePointwiseFamilyWitness_map_apply
    (m : Measure ℂ) (μ : constantBeltramiParameter) (z : ℂ) :
    ((constantBeltramiAffinePointwiseFamilyWitness m).solution μ).map z =
      constantBeltramiAffineMap μ z :=
  rfl

end

end Teichmuller
