import Teichmuller.MathlibBeltramiNeumannOperatorFamily
import Teichmuller.MathlibBeltramiMultiplier

namespace Teichmuller

open Filter Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
### Parameter families of coefficient-multiplier Neumann operators

The scalar specialization in `MathlibBeltramiNeumannOperatorFamily` keeps a
fixed singular operator and scales it by a complex number.  The classical
Beltrami factorisation is more geometric:

`K_b = M_(μ_b) ∘ B`,

where `M_(μ_b)` is multiplication by the parameter-dependent coefficient and
`B` is a fixed singular operator.  This file makes that factorisation a
genuine family on `L^p`.  The continuity of the multiplier family is kept as
an explicit analytic input; it is not inferred merely from pointwise
continuity of representatives, since the relevant topology is the operator
norm topology on `L^p`.

The construction still does not identify `B` with the Beurling transform or
prove the Calderón--Zygmund theorem.  It only connects the concrete
coefficient multiplier layer to the already proved Neumann fixed-point layer.
-/

structure MultiplierNeumannOperatorFamily
    (B α : Type*)
    [TopologicalSpace B] [MeasurableSpace α]
    (m : Measure α) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  coefficient : B → BoundedScalarCoefficient α m
  multiplier_continuous :
    Continuous (fun b => (coefficient b).multiplier (p := p))
  singularOperator : Lp ℂ p m →L[ℂ] Lp ℂ p m
  radius : ℝ≥0
  radius_lt_one : radius < 1
  coefficient_operator_norm_le :
    ∀ b, (coefficient b).bound * ‖singularOperator‖ ≤ (radius : ℝ)
  forcing : B → Lp ℂ p m
  forcing_continuous : Continuous forcing

namespace MultiplierNeumannOperatorFamily

variable {B α : Type*}
  [TopologicalSpace B] [MeasurableSpace α]
  {m : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

noncomputable def toNeumannOperatorFamily
    (F : MultiplierNeumannOperatorFamily B α m p) :
    NeumannOperatorFamily B (Lp ℂ p m) where
  radius := F.radius
  radius_lt_one := F.radius_lt_one
  kernel := fun b => (F.coefficient b).kernel F.singularOperator
  kernel_norm_le := by
    intro b
    have hnorm :
        ‖(F.coefficient b).kernel F.singularOperator‖ ≤ (F.radius : ℝ) :=
      ((F.coefficient b).norm_kernel_le F.singularOperator).trans
        (F.coefficient_operator_norm_le b)
    exact_mod_cast hnorm
  kernel_continuous := by
    have hcomp :
        Continuous
          (fun q :
              (Lp ℂ p m →L[ℂ] Lp ℂ p m) ×
                (Lp ℂ p m →L[ℂ] Lp ℂ p m) =>
            q.1.comp q.2) := by
      exact (isBoundedBilinearMap_comp (𝕜 := ℂ)).continuous
    change Continuous
      (fun b => (F.coefficient b).multiplier.comp F.singularOperator)
    exact hcomp.comp
      (F.multiplier_continuous.prodMk
        (continuous_const : Continuous (fun _ : B => F.singularOperator)))
  forcing := F.forcing
  forcing_continuous := F.forcing_continuous

@[simp] theorem toNeumannOperatorFamily_kernel
    (F : MultiplierNeumannOperatorFamily B α m p) (b : B) :
    F.toNeumannOperatorFamily.kernel b =
      (F.coefficient b).multiplier.comp F.singularOperator :=
  rfl

theorem toNeumannOperatorFamily_solution_continuous
    (F : MultiplierNeumannOperatorFamily B α m p) :
    Continuous (NeumannOperatorFamily.solution F.toNeumannOperatorFamily) :=
  NeumannOperatorFamily.continuous_solution F.toNeumannOperatorFamily

theorem toNeumannOperatorFamily_solution_equation
    (F : MultiplierNeumannOperatorFamily B α m p) (b : B) :
    NeumannOperatorFamily.solution F.toNeumannOperatorFamily b =
      F.forcing b +
        (F.coefficient b).multiplier.comp F.singularOperator
          (NeumannOperatorFamily.solution F.toNeumannOperatorFamily b) := by
  exact NeumannOperatorFamily.solution_equation
    (F.toNeumannOperatorFamily) b

end MultiplierNeumannOperatorFamily

end

end Teichmuller
