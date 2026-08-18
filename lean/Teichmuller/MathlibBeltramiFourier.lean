import Teichmuller.MathlibBeltramiMultiplier
import Mathlib.Analysis.Fourier.LpSpace

namespace Teichmuller

open MeasureTheory
open scoped ComplexConjugate ENNReal FourierTransform NNReal Topology

noncomputable section

local instance complexL2FactOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-!
### The `L²` Fourier-side Beurling model

The classical Beurling transform has Fourier symbol

`m(ξ) = conj ξ / ξ` for `ξ ≠ 0`.

This file formalizes the corresponding `L²` spectral model.  Mathlib supplies
the Plancherel linear isometry equivalence, so the multiplier can be conjugated
back to the physical `L²` space.  This is an exact `L²` model, but it is not
yet the full Calderón--Zygmund theorem on `L^p` for `1 < p < ∞`, nor does it
identify the physical operator with a principal-value kernel.
-/

def beurlingSymbol (ξ : ℂ) : ℂ :=
  if ξ = 0 then 0 else conj ξ / ξ

theorem measurable_beurlingSymbol : Measurable beurlingSymbol := by
  apply Measurable.ite
  · exact measurableSet_singleton 0
  · exact measurable_const
  · exact (Complex.continuous_conj.measurable).div measurable_id

theorem beurlingSymbol_norm_le (ξ : ℂ) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [beurlingSymbol, hξ]
  · simp [beurlingSymbol, hξ, norm_div, RCLike.norm_conj,
      norm_ne_zero_iff.mpr hξ]

theorem beurlingSymbol_norm_eq_one {ξ : ℂ} (hξ : ξ ≠ 0) :
    ‖beurlingSymbol ξ‖ = 1 := by
  simp [beurlingSymbol, hξ, norm_div, RCLike.norm_conj,
    norm_ne_zero_iff.mpr hξ]

noncomputable def beurlingSymbolCoefficient :
    BoundedScalarCoefficient ℂ (volume : Measure ℂ) where
  toFun := beurlingSymbol
  aestronglyMeasurable := measurable_beurlingSymbol.aestronglyMeasurable
  bound := 1
  bound_ae := Filter.Eventually.of_forall fun ξ => by
    rw [← NNReal.coe_le_coe]
    exact_mod_cast beurlingSymbol_norm_le ξ

theorem beurlingSymbolCoefficient_bound :
    (beurlingSymbolCoefficient.bound : ℝ) = 1 :=
  rfl

noncomputable def beurlingFourierMultiplier :
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp (α := ℂ) ℂ 2 volume := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact beurlingSymbolCoefficient.multiplier

noncomputable def complexL2Fourier :
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp (α := ℂ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def complexL2FourierInv :
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp (α := ℂ) ℂ 2 volume :=
  (Lp.fourierTransformₗᵢ ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def beurlingL2Operator :
    Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp (α := ℂ) ℂ 2 volume :=
  complexL2FourierInv.comp (beurlingFourierMultiplier.comp complexL2Fourier)

/-!
The spectral model has an exact frequency-side equation.  This is a small
but useful normalization step: it turns the definition by conjugation with
Plancherel into the multiplier equation that a future physical-kernel proof
must match.
-/

theorem beurlingL2Operator_fourier_eq
    (f : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    complexL2Fourier (beurlingL2Operator f) =
      beurlingFourierMultiplier (complexL2Fourier f) := by
  simp [beurlingL2Operator, complexL2Fourier, complexL2FourierInv]

theorem beurlingL2Operator_fourier_eq_on_schwartz
    (φ : SchwartzMap ℂ ℂ) :
    complexL2Fourier (beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ))) =
      beurlingSymbolCoefficient.mulLp ((𝓕 φ).toLp 2 (volume : Measure ℂ)) := by
  rw [beurlingL2Operator_fourier_eq]
  rw [show complexL2Fourier (φ.toLp 2 (volume : Measure ℂ)) =
      (𝓕 φ).toLp 2 (volume : Measure ℂ) by
    exact SchwartzMap.toLp_fourier_eq φ]
  rfl

theorem beurlingL2Operator_fourier_eq_ae_on_schwartz
    (φ : SchwartzMap ℂ ℂ) :
    ∀ᵐ ξ ∂(volume : Measure ℂ),
      complexL2Fourier (beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ))) ξ =
        beurlingSymbol ξ * (𝓕 φ) ξ := by
  rw [beurlingL2Operator_fourier_eq_on_schwartz]
  filter_upwards [beurlingSymbolCoefficient.coeFn_mulLp
      ((𝓕 φ).toLp 2 (volume : Measure ℂ)),
    SchwartzMap.coeFn_toLp (𝓕 φ) 2 (volume : Measure ℂ)] with ξ hmul hφ
  exact hmul.trans (congrArg (fun z : ℂ => beurlingSymbol ξ * z) hφ)

theorem norm_beurlingFourierMultiplier_le :
    ‖beurlingFourierMultiplier‖ ≤ 1 := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖beurlingFourierMultiplier‖ ≤ beurlingSymbolCoefficient.bound := by
      simpa [beurlingFourierMultiplier] using
        (beurlingSymbolCoefficient.norm_multiplier_le (p := (2 : ℝ≥0∞)))
    _ = 1 := beurlingSymbolCoefficient_bound

theorem norm_complexL2Fourier_le : ‖complexL2Fourier‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa [complexL2Fourier] using
    (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map f |>.le

theorem norm_complexL2FourierInv_le : ‖complexL2FourierInv‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa [complexL2FourierInv] using
    (Lp.fourierTransformₗᵢ ℂ ℂ).symm.norm_map f |>.le

theorem norm_beurlingL2Operator_le : ‖beurlingL2Operator‖ ≤ 1 := by
  calc
    ‖beurlingL2Operator‖ ≤ ‖complexL2FourierInv‖ *
        ‖beurlingFourierMultiplier.comp complexL2Fourier‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖complexL2FourierInv‖ *
        (‖beurlingFourierMultiplier‖ * ‖complexL2Fourier‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖beurlingFourierMultiplier‖ * ‖complexL2Fourier‖) := by
      exact mul_le_mul_of_nonneg_right norm_complexL2FourierInv_le
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 1 * (1 * ‖complexL2Fourier‖) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right norm_beurlingFourierMultiplier_le
          (norm_nonneg (complexL2Fourier)))
    _ ≤ 1 * (1 * 1) := by
      simpa only [one_mul, mul_one] using
        (mul_le_mul_of_nonneg_right norm_complexL2Fourier_le
          (by norm_num : (0 : ℝ) ≤ 1))
    _ = 1 := by norm_num

theorem beurlingFourierMultiplier_norm_on_fourier_le
    (f : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    ‖beurlingFourierMultiplier (complexL2Fourier f)‖ ≤ ‖f‖ := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖beurlingFourierMultiplier (complexL2Fourier f)‖ =
        ‖beurlingSymbolCoefficient.mulLp (complexL2Fourier f)‖ := rfl
    _ ≤ beurlingSymbolCoefficient.bound * ‖complexL2Fourier f‖ :=
      beurlingSymbolCoefficient.norm_mulLp_le _
    _ = ‖f‖ := by
      rw [beurlingSymbolCoefficient_bound, one_mul]
      simpa [complexL2Fourier] using (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map f

theorem norm_beurlingFourierMultiplier_eq
    (f : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    ‖beurlingFourierMultiplier f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [beurlingSymbolCoefficient.coeFn_mulLp f,
    show ∀ᵐ ξ ∂(volume : Measure ℂ), ξ ≠ 0 by
      simp [ae_iff, measure_singleton]] with ξ hmul hξ
  change ‖beurlingSymbolCoefficient.mulLp f ξ‖ = ‖f ξ‖
  rw [hmul, norm_mul]
  change ‖beurlingSymbol ξ‖ * ‖f ξ‖ = ‖f ξ‖
  rw [beurlingSymbol_norm_eq_one hξ, one_mul]

theorem norm_beurlingL2Operator_eq
    (f : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    ‖beurlingL2Operator f‖ = ‖f‖ := by
  calc
    ‖beurlingL2Operator f‖ = ‖complexL2Fourier (beurlingL2Operator f)‖ := by
      symm
      simpa [complexL2Fourier] using (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map
        (beurlingL2Operator f)
    _ = ‖beurlingFourierMultiplier (complexL2Fourier f)‖ := by
      rw [beurlingL2Operator_fourier_eq]
    _ = ‖complexL2Fourier f‖ := norm_beurlingFourierMultiplier_eq _
    _ = ‖f‖ := by
      simpa [complexL2Fourier] using (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map f

theorem beurlingL2Operator_injective :
    Function.Injective beurlingL2Operator := by
  intro f g hfg
  have hnorm : ‖f - g‖ = 0 := by
    rw [← norm_beurlingL2Operator_eq (f - g), map_sub, hfg]
    simp
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem beurlingL2Operator_inner_eq_fourierMultiplier
    (f g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (beurlingL2Operator f) g =
      inner ℂ (beurlingFourierMultiplier (complexL2Fourier f)) (complexL2Fourier g) := by
  rw [← MeasureTheory.Lp.inner_fourier_eq (beurlingL2Operator f) g]
  change inner ℂ (complexL2Fourier (beurlingL2Operator f)) (complexL2Fourier g) = _
  rw [beurlingL2Operator_fourier_eq]

theorem beurlingL2Operator_inner_eq_fourierMultiplier_on_schwartz
    (φ : SchwartzMap ℂ ℂ) (g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ))) g =
      inner ℂ (beurlingSymbolCoefficient.mulLp ((𝓕 φ).toLp 2 (volume : Measure ℂ)))
        (complexL2Fourier g) := by
  rw [beurlingL2Operator_inner_eq_fourierMultiplier]
  rw [show complexL2Fourier (φ.toLp 2 (volume : Measure ℂ)) =
      (𝓕 φ).toLp 2 (volume : Measure ℂ) by
    exact SchwartzMap.toLp_fourier_eq φ]
  rfl

/-- The `L²` Neumann problem with the physical-side coefficient multiplier and
the Fourier-side Beurling model. -/
noncomputable def beurlingL2NeumannProblem
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))
    (hc : (c.bound : ℝ) < 1) :
    LpNeumannBeltramiProblem (volume : Measure ℂ) 2 where
  coefficient := c
  singularOperator := beurlingL2Operator
  forcing := g
  coefficient_operator_norm_lt_one := by
    calc
      (c.bound : ℝ) * ‖beurlingL2Operator‖ ≤ (c.bound : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left norm_beurlingL2Operator_le c.bound.coe_nonneg
      _ = (c.bound : ℝ) := by simp
      _ < 1 := hc

theorem beurlingL2NeumannProblem_kernel_norm_lt_one
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))
    (hc : (c.bound : ℝ) < 1) :
    ‖(beurlingL2NeumannProblem c g hc).kernel‖ < 1 :=
  (beurlingL2NeumannProblem c g hc).kernel_norm_lt_one

theorem beurlingL2NeumannProblem_exists_solution
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ))
    (hc : (c.bound : ℝ) < 1) :
    ∃ u : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ),
      u = g + (beurlingL2NeumannProblem c g hc).kernel u :=
  (beurlingL2NeumannProblem c g hc).exists_solution

noncomputable def BeltramiCoefficient.toBeurlingL2NeumannProblem
    (μ : BeltramiCoefficient (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)) :
    LpNeumannBeltramiProblem (volume : Measure ℂ) 2 :=
  let c :=
    { toFun := μ.toFun
      aestronglyMeasurable := μ.measurable.aestronglyMeasurable
      bound := (max (Classical.choose μ.essential_bound) 0).toNNReal
      bound_ae := by
        have hbound := (Classical.choose_spec μ.essential_bound).2
        filter_upwards [hbound] with z hz
        rw [← NNReal.coe_le_coe]
        rw [Real.coe_toNNReal _ (le_max_right _ _)]
        exact_mod_cast hz.trans (le_max_left _ _) }
  beurlingL2NeumannProblem c g (by
    have hk := (Classical.choose_spec μ.essential_bound).1
    have hmax : max (Classical.choose μ.essential_bound) 0 < 1 :=
      max_lt hk (by norm_num)
    rw [Real.coe_toNNReal _ (le_max_right _ _)]
    exact hmax)

end

end Teichmuller
