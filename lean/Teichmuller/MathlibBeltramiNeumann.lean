import Teichmuller.MathlibBeltramiContraction
import Mathlib.Analysis.Normed.Operator.NNNorm

namespace Teichmuller

open Filter Function
open scoped NNReal Topology

noncomputable section

/-!
### The operator-theoretic Neumann layer

The measurable Riemann mapping theorem is often reduced analytically to a
fixed-point equation involving a coefficient multiplier and a singular
integral operator (in the classical plane model, the Beurling transform).
Mathlib does not provide that singular-integral theorem in the present
development, so this file isolates the part that is already exact:

* a bounded linear kernel on a complete normed space;
* the affine equation `u = g + K u`;
* the contraction criterion `‖K‖ < 1`;
* the fixed point, its convergence, uniqueness, and an a priori norm bound.

`ScaledNeumannBeltramiProblem` records the coefficient/operator shape
`K = μ • B`.  It does not claim that `B` is the Beurling transform, nor that
the resulting abstract state is already a homeomorphism solving the
Beltrami PDE.  Those are precisely the future analytic input fields.
-/

structure NeumannBeltramiProblem (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  forcing : E
  kernel : E →L[ℂ] E
  kernel_norm_lt_one : ‖kernel‖₊ < 1

def NeumannBeltramiProblem.affineOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) : E → E :=
  fun u => P.forcing + P.kernel u

theorem NeumannBeltramiProblem.affineOperator_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    LipschitzWith ‖P.kernel‖₊ P.affineOperator := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [NeumannBeltramiProblem.affineOperator] using
    P.kernel.dist_le_opNorm x y

def NeumannBeltramiProblem.contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    ContractingWith ‖P.kernel‖₊ P.affineOperator :=
  ⟨P.kernel_norm_lt_one, P.affineOperator_lipschitz⟩

noncomputable def NeumannBeltramiProblem.fixedPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) : E :=
  ContractingWith.fixedPoint P.affineOperator P.contraction

theorem NeumannBeltramiProblem.fixedPoint_isFixedPt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    IsFixedPt P.affineOperator P.fixedPoint :=
  P.contraction.fixedPoint_isFixedPt

theorem NeumannBeltramiProblem.fixedPoint_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    P.fixedPoint = P.forcing + P.kernel P.fixedPoint := by
  simpa [NeumannBeltramiProblem.affineOperator] using
    P.fixedPoint_isFixedPt.symm

theorem NeumannBeltramiProblem.fixedPoint_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) (u : E)
    (hu : u = P.forcing + P.kernel u) :
    u = P.fixedPoint := by
  apply P.contraction.fixedPoint_unique'
  · change P.affineOperator u = u
    simpa [NeumannBeltramiProblem.affineOperator] using hu.symm
  · exact P.fixedPoint_isFixedPt

theorem NeumannBeltramiProblem.fixedPoint_iterates_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    Tendsto (fun n => P.affineOperator^[n] (0 : E)) atTop
      (𝓝 P.fixedPoint) :=
  P.contraction.tendsto_iterate_fixedPoint 0

theorem NeumannBeltramiProblem.fixedPoint_iteration_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) (n : ℕ) :
    ‖P.affineOperator^[n] (0 : E) - P.fixedPoint‖ ≤
      ‖P.forcing‖ * (‖P.kernel‖ : ℝ) ^ n / (1 - ‖P.kernel‖) := by
  simpa [NeumannBeltramiProblem.fixedPoint, dist_eq_norm,
    NeumannBeltramiProblem.affineOperator] using
    P.contraction.apriori_dist_iterate_fixedPoint_le (0 : E) n

theorem NeumannBeltramiProblem.fixedPoint_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    ‖P.fixedPoint‖ ≤ ‖P.forcing‖ / (1 - ‖P.kernel‖) := by
  simpa [NeumannBeltramiProblem.fixedPoint, dist_eq_norm,
    NeumannBeltramiProblem.affineOperator] using
    P.contraction.dist_fixedPoint_le (0 : E)

theorem NeumannBeltramiProblem.exists_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : NeumannBeltramiProblem E) :
    ∃ u : E, u = P.forcing + P.kernel u :=
  ⟨P.fixedPoint, P.fixedPoint_equation⟩

structure ScaledNeumannBeltramiProblem (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  coefficient : ℂ
  singularOperator : E →L[ℂ] E
  forcing : E
  coefficient_operator_norm_lt_one :
    ‖coefficient‖ * ‖singularOperator‖ < 1

def ScaledNeumannBeltramiProblem.kernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) : E →L[ℂ] E :=
  P.coefficient • P.singularOperator

theorem ScaledNeumannBeltramiProblem.kernel_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) :
    ‖P.kernel‖ ≤ ‖P.coefficient‖ * ‖P.singularOperator‖ :=
  ContinuousLinearMap.opNorm_smul_le _ _

theorem ScaledNeumannBeltramiProblem.kernel_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) :
    ‖P.kernel‖ < 1 :=
  P.kernel_norm_le.trans_lt P.coefficient_operator_norm_lt_one

def ScaledNeumannBeltramiProblem.toNeumannProblem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) : NeumannBeltramiProblem E where
  forcing := P.forcing
  kernel := P.kernel
  kernel_norm_lt_one := by
    exact_mod_cast P.kernel_norm_lt_one

theorem ScaledNeumannBeltramiProblem.exists_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) :
    ∃ u : E, u = P.forcing + P.kernel u :=
  P.toNeumannProblem.exists_solution

theorem ScaledNeumannBeltramiProblem.solution_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : ScaledNeumannBeltramiProblem E) (u : E)
    (hu : u = P.forcing + P.kernel u) :
    u = P.toNeumannProblem.fixedPoint :=
  P.toNeumannProblem.fixedPoint_unique u hu

def complexScalarScaledNeumannProblem
    (μ g : ℂ) (hμ : ‖μ‖ < 1) :
    ScaledNeumannBeltramiProblem ℂ where
  coefficient := μ
  singularOperator := ContinuousLinearMap.id ℂ ℂ
  forcing := g
  coefficient_operator_norm_lt_one := by
    simpa using hμ

theorem complexScalarScaledNeumannProblem_solution_eq
    (μ g : ℂ) (hμ : ‖μ‖ < 1) :
    (complexScalarScaledNeumannProblem μ g hμ).toNeumannProblem.fixedPoint =
      (1 - μ)⁻¹ * g := by
  have hμ_ne_one : μ ≠ 1 := by
    intro h
    subst h
    norm_num at hμ
  have hden : 1 - μ ≠ 0 := sub_ne_zero.mpr hμ_ne_one.symm
  symm
  apply (complexScalarScaledNeumannProblem μ g hμ).solution_unique
  simp only [complexScalarScaledNeumannProblem,
    ScaledNeumannBeltramiProblem.kernel,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  have hinner : (1 - μ) * ((1 - μ)⁻¹ * g) = g := by
    rw [← mul_assoc, mul_inv_cancel₀ hden, one_mul]
  apply (mul_left_cancel₀ hden)
  calc
    (1 - μ) * ((1 - μ)⁻¹ * g) = g := hinner
    _ = (1 - μ) * (g + μ * ((1 - μ)⁻¹ * g)) := by
      calc
        g = (1 - μ) * g + μ * g := by ring
        _ = (1 - μ) * g +
            μ * ((1 - μ) * ((1 - μ)⁻¹ * g)) := by
          rw [hinner]
        _ = (1 - μ) * (g + μ * ((1 - μ)⁻¹ * g)) := by ring

end

end Teichmuller
