import Teichmuller.MathlibBeltramiNeumannMultiplierFamily
import Teichmuller.MathlibBeltramiFourier

namespace Teichmuller

open Filter Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

local instance constantL2FactOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-!
### A uniform closed-subdisk family for the `L²` Beurling model

The open unit disk is the natural constant-Beltrami parameter space, but it
does not admit one contraction radius strictly below one.  For a genuine
parameterized Neumann theorem we therefore work on a closed subdisk

`P_r = { μ : ℂ | ‖μ‖ ≤ r }`, with `r < 1`.

The coefficient is constant in the spatial variable, so its `L²` multiplier
is exactly scalar multiplication by `μ`.  This gives a fully explicit
operator-norm continuous multiplier family and lets the Fourier-defined
Beurling operator enter the variable-kernel Neumann layer.  No principal-value
identification is used here.
-/

abbrev constantBeltramiL2Parameter (r : ℝ≥0) :=
  {μ : ℂ // ‖μ‖ ≤ (r : ℝ)}

noncomputable def constantBoundedScalarCoefficient
    (r : ℝ≥0) (μ : ℂ) (hμ : ‖μ‖ ≤ (r : ℝ)) :
    BoundedScalarCoefficient ℂ (volume : Measure ℂ) where
  toFun := fun _ => μ
  aestronglyMeasurable := measurable_const.aestronglyMeasurable
  bound := r
  bound_ae := by
    filter_upwards [] with z
    rw [← NNReal.coe_le_coe]
    exact_mod_cast hμ

@[simp] theorem constantBoundedScalarCoefficient_apply
    (r : ℝ≥0) (μ : ℂ) (hμ : ‖μ‖ ≤ (r : ℝ)) (z : ℂ) :
    constantBoundedScalarCoefficient r μ hμ z = μ :=
  rfl

theorem constantBoundedScalarCoefficient_multiplier_eq_smul_id
    (r : ℝ≥0) (μ : ℂ) (hμ : ‖μ‖ ≤ (r : ℝ)) :
    (constantBoundedScalarCoefficient r μ hμ).multiplier (p := (2 : ℝ≥0∞)) =
      μ • (ContinuousLinearMap.id ℂ
        (Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    (constantBoundedScalarCoefficient r μ hμ).coeFn_mulLp f,
    Lp.coeFn_smul μ f] with x hmul hsmul
  change (constantBoundedScalarCoefficient r μ hμ).mulLp f x =
    (μ • f) x
  rw [hmul, hsmul]
  simp [constantBoundedScalarCoefficient]

noncomputable def constantBeltramiL2NeumannFamily
    (r : ℝ≥0) (hr : r < 1)
    (forcing : constantBeltramiL2Parameter r →
      Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))
    (hforcing : Continuous forcing) :
    MultiplierNeumannOperatorFamily
      (constantBeltramiL2Parameter r) ℂ (volume : Measure ℂ) 2 where
  coefficient := fun μ =>
    constantBoundedScalarCoefficient r μ.1 μ.2
  multiplier_continuous := by
    apply Continuous.congr
      (continuous_subtype_val.smul continuous_const)
    intro μ
    exact (constantBoundedScalarCoefficient_multiplier_eq_smul_id
      r μ.1 μ.2).symm
  singularOperator := beurlingL2Operator
  radius := r
  radius_lt_one := hr
  coefficient_operator_norm_le := by
    intro μ
    change (r : ℝ) * ‖beurlingL2Operator‖ ≤ (r : ℝ)
    calc
      (r : ℝ) * ‖beurlingL2Operator‖ ≤ (r : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left norm_beurlingL2Operator_le r.coe_nonneg
      _ = (r : ℝ) := by simp
  forcing := forcing
  forcing_continuous := hforcing

namespace ConstantBeltramiL2NeumannFamily

variable {r : ℝ≥0} {hr : r < 1}
  {forcing : constantBeltramiL2Parameter r →
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)}
  {hforcing : Continuous forcing}

noncomputable def operatorFamily :
    NeumannOperatorFamily
      (constantBeltramiL2Parameter r)
      (Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :=
  (constantBeltramiL2NeumannFamily r hr forcing hforcing).toNeumannOperatorFamily

theorem solution_continuous :
    Continuous (NeumannOperatorFamily.solution
      (operatorFamily (r := r) (hr := hr) (forcing := forcing)
        (hforcing := hforcing))) :=
  MultiplierNeumannOperatorFamily.toNeumannOperatorFamily_solution_continuous
    (constantBeltramiL2NeumannFamily r hr forcing hforcing)

theorem solution_equation
    (μ : constantBeltramiL2Parameter r) :
    NeumannOperatorFamily.solution
        (operatorFamily (r := r) (hr := hr) (forcing := forcing)
          (hforcing := hforcing)) μ =
      forcing μ +
        (constantBoundedScalarCoefficient r μ.1 μ.2).multiplier.comp
          beurlingL2Operator
          (NeumannOperatorFamily.solution
            (operatorFamily (r := r) (hr := hr) (forcing := forcing)
              (hforcing := hforcing)) μ) :=
  MultiplierNeumannOperatorFamily.toNeumannOperatorFamily_solution_equation
    (constantBeltramiL2NeumannFamily r hr forcing hforcing) μ

theorem kernel_norm_le (μ : constantBeltramiL2Parameter r) :
    ‖(operatorFamily (r := r) (hr := hr) (forcing := forcing)
      (hforcing := hforcing)).kernel μ‖ ≤ (r : ℝ) :=
  (operatorFamily (r := r) (hr := hr) (forcing := forcing)
    (hforcing := hforcing)).kernel_norm_le μ

end ConstantBeltramiL2NeumannFamily

end

end Teichmuller
