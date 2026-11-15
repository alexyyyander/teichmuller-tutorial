import Teichmuller.MathlibBeltramiNeumannBeurlingFamily

namespace Teichmuller

open Filter Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
### A genuinely spatially varying coefficient profile

The constant-coefficient family is useful for calibration, but it does not yet
vary in the spatial variable.  Fix a bounded measurable profile `a(z)` and let

`μ_b(z) = b * a(z)`.

The multiplier is then linear in the parameter:

`M_(μ_b) = b • M_a`.

This file proves that identity on `L²` and feeds it into the Fourier-defined
Beurling operator.  The only global restriction is the honest uniform one
`r * ‖a‖∞ < 1`; the parameter ranges over `‖b‖ ≤ r`.
-/

abbrev profileBeltramiL2Parameter (r : ℝ≥0) :=
  {b : ℂ // ‖b‖ ≤ (r : ℝ)}

noncomputable def profileScaledBoundedScalarCoefficient
    (a : BoundedScalarCoefficient ℂ (volume : Measure ℂ)) (b : ℂ) :
    BoundedScalarCoefficient ℂ (volume : Measure ℂ) where
  toFun := fun z => b * a z
  aestronglyMeasurable := by
    simpa [mul_comm] using a.aestronglyMeasurable.mul_const b
  bound := ‖b‖₊ * a.bound
  bound_ae := by
    filter_upwards [a.bound_ae] with z hz
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, norm_mul]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg b)

@[simp] theorem profileScaledBoundedScalarCoefficient_apply
    (a : BoundedScalarCoefficient ℂ (volume : Measure ℂ)) (b z : ℂ) :
    profileScaledBoundedScalarCoefficient a b z = b * a z :=
  rfl

theorem profileScaledBoundedScalarCoefficient_multiplier_eq_smul
    (a : BoundedScalarCoefficient ℂ (volume : Measure ℂ)) (b : ℂ) :
    (profileScaledBoundedScalarCoefficient a b).multiplier (p := (2 : ℝ≥0∞)) =
      b • a.multiplier (p := (2 : ℝ≥0∞)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    (profileScaledBoundedScalarCoefficient a b).coeFn_mulLp f,
    a.coeFn_mulLp f,
    Lp.coeFn_smul b (a.multiplier (p := (2 : ℝ≥0∞)) f)] with x hscaled ha hsmul
  change (profileScaledBoundedScalarCoefficient a b).mulLp f x =
    (b • a.multiplier (p := (2 : ℝ≥0∞)) f) x
  rw [hsmul]
  change (profileScaledBoundedScalarCoefficient a b).mulLp f x =
    b * a.multiplier (p := (2 : ℝ≥0∞)) f x
  rw [show a.multiplier (p := (2 : ℝ≥0∞)) f = a.mulLp f from rfl,
    ha, hscaled]
  change (b * a.toFun x) * f x = b * (a.toFun x * f x)
  ring

noncomputable def profileBeltramiL2NeumannFamily
    (a : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (r : ℝ≥0) (hr : (r : ℝ) * (a.bound : ℝ) < 1)
    (forcing : profileBeltramiL2Parameter r →
      Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))
    (hforcing : Continuous forcing) :
    MultiplierNeumannOperatorFamily
      (profileBeltramiL2Parameter r) ℂ (volume : Measure ℂ) 2 where
  coefficient := fun b => profileScaledBoundedScalarCoefficient a b.1
  multiplier_continuous := by
    apply Continuous.congr
      (continuous_subtype_val.smul
        (continuous_const : Continuous (fun _ : profileBeltramiL2Parameter r =>
          a.multiplier (p := (2 : ℝ≥0∞)))))
    intro b
    exact (profileScaledBoundedScalarCoefficient_multiplier_eq_smul a b.1).symm
  singularOperator := beurlingL2Operator
  radius := r * a.bound
  radius_lt_one := by
    exact_mod_cast hr
  coefficient_operator_norm_le := by
    intro b
    change
      (‖b.1‖ * (a.bound : ℝ)) * ‖beurlingL2Operator‖ ≤
        ((r * a.bound : ℝ≥0) : ℝ)
    calc
      (‖b.1‖ * (a.bound : ℝ)) * ‖beurlingL2Operator‖ ≤
          (‖b.1‖ * (a.bound : ℝ)) * 1 := by
        exact mul_le_mul_of_nonneg_left norm_beurlingL2Operator_le
          (mul_nonneg (norm_nonneg _) a.bound.coe_nonneg)
      _ ≤ (r : ℝ) * (a.bound : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right b.2 a.bound.coe_nonneg
      _ = ((r * a.bound : ℝ≥0) : ℝ) := by simp
  forcing := forcing
  forcing_continuous := hforcing

namespace ProfileBeltramiL2NeumannFamily

variable {a : BoundedScalarCoefficient ℂ (volume : Measure ℂ)}
  {r : ℝ≥0} {hr : (r : ℝ) * (a.bound : ℝ) < 1}
  {forcing : profileBeltramiL2Parameter r →
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)}
  {hforcing : Continuous forcing}

noncomputable def operatorFamily :
    NeumannOperatorFamily
      (profileBeltramiL2Parameter r)
      (Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :=
  (profileBeltramiL2NeumannFamily a r hr forcing hforcing).toNeumannOperatorFamily

theorem solution_continuous :
    Continuous (NeumannOperatorFamily.solution
      (operatorFamily (a := a) (r := r) (hr := hr)
        (forcing := forcing) (hforcing := hforcing))) :=
  MultiplierNeumannOperatorFamily.toNeumannOperatorFamily_solution_continuous
    (profileBeltramiL2NeumannFamily a r hr forcing hforcing)

theorem solution_equation
    (b : profileBeltramiL2Parameter r) :
    NeumannOperatorFamily.solution
        (operatorFamily (a := a) (r := r) (hr := hr)
          (forcing := forcing) (hforcing := hforcing)) b =
      forcing b +
        (profileScaledBoundedScalarCoefficient a b.1).multiplier.comp
          beurlingL2Operator
          (NeumannOperatorFamily.solution
            (operatorFamily (a := a) (r := r) (hr := hr)
              (forcing := forcing) (hforcing := hforcing)) b) :=
  MultiplierNeumannOperatorFamily.toNeumannOperatorFamily_solution_equation
    (profileBeltramiL2NeumannFamily a r hr forcing hforcing) b

theorem kernel_norm_le (b : profileBeltramiL2Parameter r) :
    ‖(operatorFamily (a := a) (r := r) (hr := hr)
      (forcing := forcing) (hforcing := hforcing)).kernel b‖ ≤
        ((r * a.bound : ℝ≥0) : ℝ) :=
  (operatorFamily (a := a) (r := r) (hr := hr)
    (forcing := forcing) (hforcing := hforcing)).kernel_norm_le b

end ProfileBeltramiL2NeumannFamily

end

end Teichmuller
