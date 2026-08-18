import Teichmuller.MathlibBeltrami

namespace Teichmuller

/-!
### Differential algebra behind the Beltrami transformation law

This file starts the derivative-dependent layer.  A real-linear differential
on `ℂ` has a complex-linear and an anti-linear coefficient; the first lemma
below reconstructs the differential from those two coefficients.  Subsequent
lemmas can therefore calculate the coefficient of a composition without
confusing scalar coefficient transport with the genuine differential law.
-/

noncomputable section

theorem realLinearMap_apply_eq_complexDerivativePart_mul_add_anti
    (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z = complexDerivativePart D * z +
      antiComplexDerivativePart D * (starRingEnd ℂ) z := by
  rw [← Complex.re_add_im z]
  rw [D.map_add]
  change D (z.re : ℂ) + D (z.im • Complex.I) = _
  rw [D.map_smul]
  rw [show (z.re : ℂ) = z.re • (1 : ℂ) by simp, D.map_smul]
  apply Complex.ext <;>
    simp [complexDerivativePart, antiComplexDerivativePart,
      Complex.mul_re, Complex.mul_im] <;>
    ring

theorem realLinearMap_beltrami_norm_upper
    (D : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (hμ : antiComplexDerivativePart D =
      μ * complexDerivativePart D) (z : ℂ) :
    ‖D z‖ ≤ (1 + ‖μ‖) * ‖complexDerivativePart D‖ * ‖z‖ := by
  rw [realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D z, hμ]
  calc
    ‖complexDerivativePart D * z +
        (μ * complexDerivativePart D) * (starRingEnd ℂ) z‖ ≤
      ‖complexDerivativePart D * z‖ +
        ‖(μ * complexDerivativePart D) * (starRingEnd ℂ) z‖ :=
      norm_add_le _ _
    _ = (1 + ‖μ‖) * ‖complexDerivativePart D‖ * ‖z‖ := by
      simp [Complex.norm_conj]
      ring

theorem realLinearMap_beltrami_norm_lower
    (D : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (hμ : antiComplexDerivativePart D =
      μ * complexDerivativePart D) (z : ℂ) :
    (1 - ‖μ‖) * ‖complexDerivativePart D‖ * ‖z‖ ≤ ‖D z‖ := by
  rw [realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D z, hμ]
  have hnorm := norm_sub_norm_le
    (complexDerivativePart D * z)
    (-((μ * complexDerivativePart D) * (starRingEnd ℂ) z))
  calc
    (1 - ‖μ‖) * ‖complexDerivativePart D‖ * ‖z‖ =
        ‖complexDerivativePart D * z‖ -
          ‖(μ * complexDerivativePart D) * (starRingEnd ℂ) z‖ := by
      simp [Complex.norm_conj]
      ring
    _ ≤ ‖complexDerivativePart D * z +
        (μ * complexDerivativePart D) * (starRingEnd ℂ) z‖ := by
      simpa [sub_eq_add_neg, norm_neg] using hnorm

theorem realLinearMap_beltrami_injective
    (D : ℂ →L[ℝ] ℂ) (μ : ℂ)
    (hμ : ‖μ‖ < 1)
    (ha : complexDerivativePart D ≠ 0)
    (hEq : antiComplexDerivativePart D =
      μ * complexDerivativePart D) :
    Function.Injective D := by
  intro x y hxy
  have hlower := realLinearMap_beltrami_norm_lower D μ hEq (x - y)
  have hDxy : D (x - y) = 0 := by
    rw [D.map_sub, hxy, sub_self]
  rw [hDxy, norm_zero] at hlower
  have hcoef : 0 < (1 - ‖μ‖) * ‖complexDerivativePart D‖ := by
    exact mul_pos (sub_pos.mpr hμ) (norm_pos_iff.mpr ha)
  have hz : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem complexDerivativePart_comp
    (D E : ℂ →L[ℝ] ℂ) :
    complexDerivativePart (D.comp E) =
      complexDerivativePart D * complexDerivativePart E +
        antiComplexDerivativePart D *
          (starRingEnd ℂ) (antiComplexDerivativePart E) := by
  have hE1 := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti E 1
  have hEI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti E Complex.I
  have hE1' : E 1 = complexDerivativePart E + antiComplexDerivativePart E := by
    simpa using hE1
  have hEI' : E Complex.I = complexDerivativePart E * Complex.I -
      antiComplexDerivativePart E * Complex.I := by
    simpa [sub_eq_add_neg] using hEI
  change (D (E 1) - Complex.I * D (E Complex.I)) / 2 = _
  rw [hE1', hEI', D.map_add, D.map_sub]
  have hDa := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (complexDerivativePart E)
  have hDb := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (antiComplexDerivativePart E)
  have hDaI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (complexDerivativePart E * Complex.I)
  have hDbI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (antiComplexDerivativePart E * Complex.I)
  rw [hDa, hDb, hDaI, hDbI]
  simp
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ring_nf
  rw [hI2]
  ring

theorem antiComplexDerivativePart_comp
    (D E : ℂ →L[ℝ] ℂ) :
    antiComplexDerivativePart (D.comp E) =
      complexDerivativePart D * antiComplexDerivativePart E +
        antiComplexDerivativePart D *
          (starRingEnd ℂ) (complexDerivativePart E) := by
  have hE1 := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti E 1
  have hEI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti E Complex.I
  have hE1' : E 1 = complexDerivativePart E + antiComplexDerivativePart E := by
    simpa using hE1
  have hEI' : E Complex.I = complexDerivativePart E * Complex.I -
      antiComplexDerivativePart E * Complex.I := by
    simpa [sub_eq_add_neg] using hEI
  change (D (E 1) + Complex.I * D (E Complex.I)) / 2 = _
  rw [hE1', hEI', D.map_add, D.map_sub]
  have hDa := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (complexDerivativePart E)
  have hDb := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (antiComplexDerivativePart E)
  have hDaI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (complexDerivativePart E * Complex.I)
  have hDbI := realLinearMap_apply_eq_complexDerivativePart_mul_add_anti D
    (antiComplexDerivativePart E * Complex.I)
  rw [hDa, hDb, hDaI, hDbI]
  simp
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ring_nf
  rw [hI2]
  ring

/-!
The quotient below is the Beltrami coefficient of a real differential when
its complex-linear part is nonzero.  The definition itself is total in Lean;
the nondegeneracy hypothesis is recorded on the theorems which use the
quotient as a genuine local distortion parameter.
-/

def differentialBeltramiCoefficient (D : ℂ →L[ℝ] ℂ) : ℂ :=
  antiComplexDerivativePart D / complexDerivativePart D

theorem differentialBeltramiCoefficient_eq_zero_iff
    (D : ℂ →L[ℝ] ℂ) (hD : complexDerivativePart D ≠ 0) :
    differentialBeltramiCoefficient D = 0 ↔
      antiComplexDerivativePart D = 0 := by
  unfold differentialBeltramiCoefficient
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hden
    · exact hnum
    · exact (hD hden).elim
  · intro h
    simp [h]

theorem differentialBeltramiCoefficient_comp
    (D E : ℂ →L[ℝ] ℂ) :
    differentialBeltramiCoefficient (D.comp E) =
      (complexDerivativePart D * antiComplexDerivativePart E +
          antiComplexDerivativePart D *
            (starRingEnd ℂ) (complexDerivativePart E)) /
        (complexDerivativePart D * complexDerivativePart E +
          antiComplexDerivativePart D *
            (starRingEnd ℂ) (antiComplexDerivativePart E)) := by
  unfold differentialBeltramiCoefficient
  rw [antiComplexDerivativePart_comp, complexDerivativePart_comp]

/-- The Möbius action of a real-linear coordinate differential on a
Beltrami coefficient.  The formula is written independently of a
representative differential whose coefficient is μ; this is the normalized
form of the composition law. -/
def differentialBeltramiTransform
    (μ : ℂ) (E : ℂ →L[ℝ] ℂ) : ℂ :=
  (antiComplexDerivativePart E +
      μ * (starRingEnd ℂ) (complexDerivativePart E)) /
    (complexDerivativePart E +
      μ * (starRingEnd ℂ) (antiComplexDerivativePart E))

theorem differentialBeltramiCoefficient_comp_eq_transform
    (D E : ℂ →L[ℝ] ℂ)
    (hD : complexDerivativePart D ≠ 0) :
    differentialBeltramiCoefficient (D.comp E) =
      differentialBeltramiTransform
        (differentialBeltramiCoefficient D) E := by
  rw [differentialBeltramiCoefficient_comp]
  unfold differentialBeltramiTransform differentialBeltramiCoefficient
  field_simp [hD]

def fderivBeltramiCoefficient (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  differentialBeltramiCoefficient (fderiv ℝ f z)

theorem fderivBeltramiCoefficient_comp_eq_transform
    (f g : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f (g z))
    (hg : DifferentiableAt ℝ g z)
    (hD : complexDerivativePart (fderiv ℝ f (g z)) ≠ 0) :
    fderivBeltramiCoefficient (f ∘ g) z =
      differentialBeltramiTransform
        (fderivBeltramiCoefficient f (g z))
        (fderiv ℝ g z) := by
  unfold fderivBeltramiCoefficient
  rw [fderiv_comp z hf hg]
  exact differentialBeltramiCoefficient_comp_eq_transform
    (fderiv ℝ f (g z)) (fderiv ℝ g z) hD

end

end Teichmuller
