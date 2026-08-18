import Teichmuller.MathlibBeltramiNeumann

namespace Teichmuller

open Filter Function
open scoped NNReal Topology

noncomputable section

/-!
### Continuous parameter families of Neumann solutions

This is the first family-level theorem on the operator side.  The kernel is
kept fixed while the forcing term varies continuously, and a single
contraction constant controls every parameter.  The fixed point therefore
inherits continuity from the forcing term with an explicit stability bound.
The more difficult case of a varying singular operator is left for the
Calderón--Zygmund input layer.
-/

structure NeumannForcingFamily (B E : Type*)
    [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  kernel : E →L[ℂ] E
  kernel_norm_lt_one : ‖kernel‖ < 1
  forcing : B → E
  forcing_continuous : Continuous forcing

namespace NeumannForcingFamily

variable {B E : Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def problem (F : NeumannForcingFamily B E) (b : B) :
    NeumannBeltramiProblem E where
  forcing := F.forcing b
  kernel := F.kernel
  kernel_norm_lt_one := by
    exact_mod_cast F.kernel_norm_lt_one

def solution (F : NeumannForcingFamily B E) (b : B) : E :=
  (F.problem b).fixedPoint

theorem solution_equation (F : NeumannForcingFamily B E) (b : B) :
    F.solution b = F.forcing b + F.kernel (F.solution b) :=
  (F.problem b).fixedPoint_equation

theorem solution_dist_le (F : NeumannForcingFamily B E) (b₁ b₂ : B) :
    dist (F.solution b₁) (F.solution b₂) ≤
      dist (F.forcing b₁) (F.forcing b₂) / (1 - ‖F.kernel‖) := by
  let P₁ := F.problem b₁
  let P₂ := F.problem b₂
  have h := P₁.contraction.fixedPoint_lipschitz_in_map P₂.contraction
    (C := dist (F.forcing b₁) (F.forcing b₂)) (fun z => by
      change dist (F.forcing b₁ + F.kernel z) (F.forcing b₂ + F.kernel z) ≤ _
      rw [dist_add_right])
  simpa [solution, P₁, P₂, problem, NeumannBeltramiProblem.fixedPoint] using h

theorem continuous_solution (F : NeumannForcingFamily B E) :
    Continuous F.solution := by
  rw [Metric.continuous_iff']
  intro b ε hε
  have hden : 0 < 1 - ‖F.kernel‖ := sub_pos.mpr F.kernel_norm_lt_one
  have hforcing :
      Tendsto (fun b' => dist (F.forcing b') (F.forcing b))
        (𝓝 b) (𝓝 0) := by
    simpa only [dist_self] using
      (F.forcing_continuous.continuousAt.dist
        (tendsto_const_nhds :
          Tendsto (fun _ : B => F.forcing b) (𝓝 b) (𝓝 (F.forcing b))))
  have hsmall :
      ∀ᶠ b' in 𝓝 b,
        dist (F.forcing b') (F.forcing b) <
          ε * (1 - ‖F.kernel‖) := by
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using
      (Metric.tendsto_nhds.1 hforcing
        (ε * (1 - ‖F.kernel‖)) (mul_pos hε hden))
  filter_upwards [hsmall] with b' hb'
  have hbound := F.solution_dist_le b' b
  have hmul : dist (F.forcing b') (F.forcing b) / (1 - ‖F.kernel‖) < ε := by
    rw [div_lt_iff₀ hden]
    simpa [mul_comm] using hb'
  exact hbound.trans_lt hmul

end NeumannForcingFamily

end

end Teichmuller
