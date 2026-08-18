import Teichmuller.MathlibBeltramiNeumannFamily

namespace Teichmuller

open Filter Function
open scoped NNReal Topology

noncomputable section

/-!
### Continuous families of Neumann operators

The forcing-only family is not yet enough for a varying complex structure:
the coefficient or singular operator may vary with the parameter as well.
This file records the next abstract step.  A continuous family of bounded
complex-linear kernels is assumed to have one uniform contraction radius.
The fixed point then varies continuously, with an explicit estimate involving
both the forcing and operator differences.

The theorem is deliberately operator-theoretic.  It does not identify the
operator with a principal-value Beurling transform; that identification and
the uniform Calderón--Zygmund estimates remain analytic input.
-/

structure NeumannOperatorFamily (B E : Type*)
    [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  radius : ℝ≥0
  radius_lt_one : radius < 1
  kernel : B → E →L[ℂ] E
  kernel_norm_le : ∀ b, ‖kernel b‖₊ ≤ radius
  kernel_continuous : Continuous kernel
  forcing : B → E
  forcing_continuous : Continuous forcing

namespace NeumannOperatorFamily

variable {B E : Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def affineOperator (F : NeumannOperatorFamily B E) (b : B) : E → E :=
  fun u => F.forcing b + F.kernel b u

def contraction (F : NeumannOperatorFamily B E) (b : B) :
    ContractingWith F.radius (F.affineOperator b) :=
  ⟨F.radius_lt_one, by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    calc
      dist (F.affineOperator b x) (F.affineOperator b y) =
          dist (F.kernel b x) (F.kernel b y) := by
            change dist (F.forcing b + F.kernel b x)
              (F.forcing b + F.kernel b y) = _
            rw [dist_add_left]
      _ ≤ ‖F.kernel b‖₊ * dist x y := (F.kernel b).dist_le_opNorm x y
      _ ≤ F.radius * dist x y := by
        gcongr
        exact F.kernel_norm_le b⟩

noncomputable def solution (F : NeumannOperatorFamily B E) (b : B) : E :=
  (F.contraction b).fixedPoint

theorem solution_equation (F : NeumannOperatorFamily B E) (b : B) :
    F.solution b = F.forcing b + F.kernel b (F.solution b) := by
  have h := (F.contraction b).fixedPoint_isFixedPt
  change F.affineOperator b (F.solution b) = F.solution b at h
  simpa [affineOperator] using h.symm

theorem solution_norm_le (F : NeumannOperatorFamily B E) (b : B) :
    ‖F.solution b‖ ≤ ‖F.forcing b‖ / (1 - (F.radius : ℝ)) := by
  have hden : 0 < 1 - (F.radius : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast F.radius_lt_one
  have hstep :
      ‖F.solution b‖ ≤
        ‖F.forcing b‖ + (F.radius : ℝ) * ‖F.solution b‖ := by
    calc
      ‖F.solution b‖ = ‖F.forcing b + F.kernel b (F.solution b)‖ := by
        exact congrArg (fun z : E => ‖z‖) (F.solution_equation b)
      _ ≤
          ‖F.forcing b‖ + ‖F.kernel b (F.solution b)‖ := norm_add_le _ _
      _ ≤ ‖F.forcing b‖ + ‖F.kernel b‖ * ‖F.solution b‖ := by
        gcongr
        exact (F.kernel b).le_opNorm _
      _ ≤ ‖F.forcing b‖ + (F.radius : ℝ) * ‖F.solution b‖ := by
        gcongr
        exact_mod_cast F.kernel_norm_le b
  apply (le_div_iff₀ hden).2
  nlinarith

theorem solution_dist_le (F : NeumannOperatorFamily B E) (b₁ b₂ : B) :
    dist (F.solution b₁) (F.solution b₂) ≤
      (dist (F.forcing b₁) (F.forcing b₂) +
        ‖F.kernel b₁ - F.kernel b₂‖ * ‖F.solution b₂‖) /
        (1 - (F.radius : ℝ)) := by
  have hden : 0 < 1 - (F.radius : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast F.radius_lt_one
  have hfixed₁ := (F.contraction b₁).fixedPoint_isFixedPt
  have hfixed₂ := (F.contraction b₂).fixedPoint_isFixedPt
  change F.affineOperator b₂ (F.solution b₂) = F.solution b₂ at hfixed₂
  have hbase :
      dist (F.solution b₁) (F.solution b₂) ≤
        dist (F.affineOperator b₁ (F.solution b₂)) (F.solution b₂) /
          (1 - (F.radius : ℝ)) := by
    calc
      dist (F.solution b₁) (F.solution b₂) =
          dist (F.solution b₂) (F.solution b₁) := dist_comm _ _
      _ ≤ dist (F.solution b₂) (F.affineOperator b₁ (F.solution b₂)) /
          (1 - (F.radius : ℝ)) :=
        (F.contraction b₁).dist_le_of_fixedPoint (F.solution b₂) hfixed₁
      _ = dist (F.affineOperator b₁ (F.solution b₂)) (F.solution b₂) /
          (1 - (F.radius : ℝ)) := by rw [dist_comm]
  have hdist :
      dist (F.affineOperator b₁ (F.solution b₂)) (F.solution b₂) ≤
        dist (F.forcing b₁) (F.forcing b₂) +
          ‖F.kernel b₁ - F.kernel b₂‖ * ‖F.solution b₂‖ := by
    calc
      dist (F.affineOperator b₁ (F.solution b₂)) (F.solution b₂) =
          dist (F.affineOperator b₁ (F.solution b₂))
            (F.affineOperator b₂ (F.solution b₂)) := by
              rw [hfixed₂]
      _ ≤ dist (F.forcing b₁ + F.kernel b₁ (F.solution b₂))
            (F.forcing b₂ + F.kernel b₁ (F.solution b₂)) +
          dist (F.forcing b₂ + F.kernel b₁ (F.solution b₂))
            (F.forcing b₂ + F.kernel b₂ (F.solution b₂)) := by
              exact dist_triangle _ _ _
      _ = dist (F.forcing b₁) (F.forcing b₂) +
          dist (F.kernel b₁ (F.solution b₂)) (F.kernel b₂ (F.solution b₂)) := by
            rw [dist_add_right, dist_add_left]
      _ ≤ dist (F.forcing b₁) (F.forcing b₂) +
          ‖F.kernel b₁ - F.kernel b₂‖ * ‖F.solution b₂‖ := by
            gcongr
            simpa only [dist_eq_norm, ContinuousLinearMap.sub_apply] using
              (F.kernel b₁ - F.kernel b₂).le_opNorm (F.solution b₂)
  exact hbase.trans ((div_le_div_iff_of_pos_right hden).2 hdist)

theorem continuous_solution (F : NeumannOperatorFamily B E) :
    Continuous F.solution := by
  rw [Metric.continuous_iff']
  intro b ε hε
  have hden : 0 < 1 - (F.radius : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast F.radius_lt_one
  have hforcing :
      Tendsto (fun b' => dist (F.forcing b') (F.forcing b))
        (𝓝 b) (𝓝 0) := by
    simpa only [dist_self] using
      (F.forcing_continuous.continuousAt.dist
        (tendsto_const_nhds :
          Tendsto (fun _ : B => F.forcing b) (𝓝 b) (𝓝 (F.forcing b))))
  have hkernel_sub :
      Tendsto (fun b' => F.kernel b' - F.kernel b)
        (𝓝 b) (𝓝 0) := by
    simpa only [sub_self] using
      (F.kernel_continuous.continuousAt.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : B => F.kernel b) (𝓝 b) (𝓝 (F.kernel b)))).tendsto
  have hkernel :
      Tendsto (fun b' => ‖F.kernel b' - F.kernel b‖)
        (𝓝 b) (𝓝 0) := by
    simpa only [norm_zero] using hkernel_sub.norm
  have hproduct :
      Tendsto (fun b' => ‖F.kernel b' - F.kernel b‖ * ‖F.solution b‖)
        (𝓝 b) (𝓝 0) := by
    simpa only [zero_mul] using
      hkernel.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : B => ‖F.solution b‖) (𝓝 b) (𝓝 ‖F.solution b‖))
  have hnumerator :
      Tendsto
        (fun b' =>
          dist (F.forcing b') (F.forcing b) +
            ‖F.kernel b' - F.kernel b‖ * ‖F.solution b‖)
        (𝓝 b) (𝓝 0) := by
    simpa only [zero_add] using hforcing.add hproduct
  have hsmall' :=
    Metric.tendsto_nhds.1 hnumerator
      (ε * (1 - (F.radius : ℝ))) (mul_pos hε hden)
  filter_upwards [hsmall'] with b' hb'
  have hnonneg :
      0 ≤
        dist (F.forcing b') (F.forcing b) +
          ‖F.kernel b' - F.kernel b‖ * ‖F.solution b‖ :=
    add_nonneg dist_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hbnum :
      dist (F.forcing b') (F.forcing b) +
          ‖F.kernel b' - F.kernel b‖ * ‖F.solution b‖ <
        ε * (1 - (F.radius : ℝ)) := by
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hb'
  have hbound := F.solution_dist_le b' b
  have hmul :
      (dist (F.forcing b') (F.forcing b) +
          ‖F.kernel b' - F.kernel b‖ * ‖F.solution b‖) /
          (1 - (F.radius : ℝ)) < ε := by
    rw [div_lt_iff₀ hden]
    exact hbnum
  exact hbound.trans_lt hmul

end NeumannOperatorFamily

end

end Teichmuller
