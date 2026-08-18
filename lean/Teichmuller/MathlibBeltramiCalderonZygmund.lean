import Teichmuller.MathlibBeltramiFourier
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Teichmuller

open Filter MeasureTheory
open scoped BigOperators ENNReal FourierTransform NNReal Pointwise Topology

noncomputable section

/-!
### The Calderón--Zygmund boundary

Mathlib currently gives the exact L² Fourier model in
MathlibBeltramiFourier.lean, but not the full identification of that model
with the principal-value singular integral nor the Beurling Lᵖ theorem.
This file makes those missing analytic inputs explicit data rather than
silently treating them as proved.
-/

/-- The planar Beurling kernel, with an arbitrary value at its singularity. -/
def beurlingKernel (z : ℂ) : ℂ :=
  if z = 0 then 0 else -((Real.pi : ℂ)⁻¹) * z⁻¹ ^ 2

/-- The kernel truncated away from the singularity at scale ε. -/
def beurlingTruncatedKernel (ε : ℝ) (z : ℂ) : ℂ :=
  if ε ≤ ‖z‖ then beurlingKernel z else 0

/-- The formal truncated singular integral associated with beurlingKernel. -/
def beurlingTruncatedIntegral (ε : ℝ) (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ y, beurlingTruncatedKernel ε (x - y) * f y ∂(volume : Measure ℂ)

/-!
The discrete scale sequence below is the one used by the principal-value
interface.  Keeping it as a named object makes the Cauchy criterion below
read as a statement about the actual truncated integrals, rather than about
an unexpanded expression for the scale.
-/

/-- Truncated Beurling integrals along the scales `εₙ = (n + 1)⁻¹`. -/
def beurlingTruncatedIntegralSequence (f : ℂ → ℂ) (x : ℂ) (n : ℕ) : ℂ :=
  beurlingTruncatedIntegral ((n + 1 : ℝ)⁻¹) f x

theorem beurlingKernel_eq_zero_at_origin :
    beurlingKernel 0 = 0 := by
  simp [beurlingKernel]

theorem beurlingKernel_mul_I (z : ℂ) :
    beurlingKernel (Complex.I * z) = -beurlingKernel z := by
  by_cases hz : z = 0
  · simp [beurlingKernel, hz]
  · have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
    rw [beurlingKernel, if_neg hIz, beurlingKernel, if_neg hz]
    rw [mul_inv_rev, Complex.inv_I]
    ring_nf
    simp

theorem beurlingTruncatedKernel_mul_I (ε : ℝ) (z : ℂ) :
    beurlingTruncatedKernel ε (Complex.I * z) =
      -beurlingTruncatedKernel ε z := by
  by_cases h : ε ≤ ‖z‖
  · simp [beurlingTruncatedKernel, h, beurlingKernel_mul_I]
  · simp [beurlingTruncatedKernel, h]

theorem beurlingTruncatedKernel_eq_beurlingKernel
    {ε : ℝ} {z : ℂ} (hz : ε ≤ ‖z‖) :
    beurlingTruncatedKernel ε z = beurlingKernel z := by
  simp [beurlingTruncatedKernel, hz]

theorem beurlingKernel_norm_eq
    {z : ℂ} (hz : z ≠ 0) :
    ‖beurlingKernel z‖ =
      (Real.pi : ℝ)⁻¹ * ‖z‖⁻¹ ^ 2 := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [beurlingKernel, if_neg hz]
  simp [norm_pow, hpi, hz]

theorem beurlingTruncatedKernel_norm_le
    {ε : ℝ} {z : ℂ} (hε : 0 < ε) :
    ‖beurlingTruncatedKernel ε z‖ ≤
      (Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2 := by
  by_cases h : ε ≤ ‖z‖
  · have hz : z ≠ 0 := by
      intro hz0
      subst z
      have hε0 : ε ≤ 0 := by simpa using h
      exact (not_le_of_gt hε) hε0
    rw [beurlingTruncatedKernel_eq_beurlingKernel h,
      beurlingKernel_norm_eq hz]
    have hinv : ‖z‖⁻¹ ≤ ε⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hε h
    have hpow : ‖z‖⁻¹ ^ 2 ≤ ε⁻¹ ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hinv 2
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · simp [beurlingTruncatedKernel, h]
    positivity

theorem beurlingTruncatedKernel_norm_le_of_norm_ge
    {δ ε : ℝ} {z : ℂ} (hδ : 0 < δ) (hz : δ ≤ ‖z‖) :
    ‖beurlingTruncatedKernel ε z‖ ≤
      (Real.pi : ℝ)⁻¹ * δ⁻¹ ^ 2 := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hδ hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  by_cases h : ε ≤ ‖z‖
  · rw [beurlingTruncatedKernel_eq_beurlingKernel h,
      beurlingKernel_norm_eq hz0]
    have hinv : ‖z‖⁻¹ ≤ δ⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hδ hz
    have hpow : ‖z‖⁻¹ ^ 2 ≤ δ⁻¹ ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hinv 2
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · simp [beurlingTruncatedKernel, h]
    positivity

def beurlingAnnulus (ε₁ ε₂ : ℝ) : Set ℂ :=
  {z | ε₁ ≤ ‖z‖ ∧ ‖z‖ < ε₂}

noncomputable def quarterTurnCircle : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

noncomputable def quarterTurnAboutHomeomorph (x : ℂ) : ℂ ≃ₜ ℂ :=
  ((Homeomorph.subRight x).trans
      (rotation quarterTurnCircle).toHomeomorph).trans
    (Homeomorph.addRight x)

theorem quarterTurnAboutHomeomorph_apply (x y : ℂ) :
    quarterTurnAboutHomeomorph x y = x + Complex.I * (y - x) := by
  simp [quarterTurnAboutHomeomorph, quarterTurnCircle, sub_eq_add_neg, add_comm]

theorem quarterTurnAboutHomeomorph_measurePreserving (x : ℂ) :
    MeasurePreserving (quarterTurnAboutHomeomorph x)
      (volume : Measure ℂ) (volume : Measure ℂ) := by
  have h₁ :
      MeasurePreserving (fun y : ℂ => y - x)
        (volume : Measure ℂ) (volume : Measure ℂ) := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.measurePreserving_add_right (volume : Measure ℂ) (-x))
  have h₂ :
      MeasurePreserving (fun y : ℂ => rotation quarterTurnCircle y)
        (volume : Measure ℂ) (volume : Measure ℂ) :=
    LinearIsometryEquiv.measurePreserving (rotation quarterTurnCircle)
  have h₃ :
      MeasurePreserving (fun y : ℂ => y + x)
        (volume : Measure ℂ) (volume : Measure ℂ) :=
    MeasureTheory.measurePreserving_add_right (volume : Measure ℂ) x
  have h₁₂ :
      MeasurePreserving
        (fun y : ℂ => rotation quarterTurnCircle (y - x))
        (volume : Measure ℂ) (volume : Measure ℂ) := by
    simpa only [Function.comp_def] using h₂.comp h₁
  have h₁₂₃ :
      MeasurePreserving
        (fun y : ℂ => rotation quarterTurnCircle (y - x) + x)
        (volume : Measure ℂ) (volume : Measure ℂ) := by
    simpa only [Function.comp_def] using h₃.comp h₁₂
  convert h₁₂₃ using 1

def beurlingClosedBallIndicator (x : ℂ) (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall x R).indicator (fun _ => (1 : ℂ))

theorem quarterTurnAboutHomeomorph_mem_closedBall_iff
    (x y : ℂ) (R : ℝ) :
    quarterTurnAboutHomeomorph x y ∈ Metric.closedBall x R ↔
      y ∈ Metric.closedBall x R := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall]
  rw [dist_eq_norm, dist_eq_norm, quarterTurnAboutHomeomorph_apply]
  rw [show x + Complex.I * (y - x) - x = Complex.I * (y - x) by ring,
    norm_mul]
  simp

/-!
The first genuinely analytic Schwartz estimate is independent of the singular
kernel.  A Schwartz function has a globally bounded real Fréchet derivative,
with the bound controlled by its first Schwartz seminorm.  The mean-value
theorem then turns this into a quantitative estimate along the quarter-turn
orbit used by the cancellation argument.
-/

theorem SchwartzMap.norm_fderiv_le_seminorm_first
    (φ : SchwartzMap ℂ ℂ) (z : ℂ) :
    ‖fderiv ℝ φ z‖ ≤ SchwartzMap.seminorm ℝ 0 1 φ := by
  rw [← norm_iteratedFDeriv_one]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ 1 z

theorem SchwartzMap.norm_sub_quarterTurn_le
    (φ : SchwartzMap ℂ ℂ) (x y : ℂ) :
    ‖φ y - φ (quarterTurnAboutHomeomorph x y)‖ ≤
      (2 * SchwartzMap.seminorm ℝ 0 1 φ) * ‖x - y‖ := by
  have hdiff : ∀ z : ℂ, DifferentiableAt ℝ φ z :=
    fun z => φ.differentiableAt
  have hbound : ∀ z : ℂ, ‖fderiv ℝ φ z‖ ≤
      SchwartzMap.seminorm ℝ 0 1 φ :=
    fun z => SchwartzMap.norm_fderiv_le_seminorm_first φ z
  have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (s := (Set.univ : Set ℂ))
      (fun z _ => hdiff z) (fun z _ => hbound z)
      (x := y) (y := quarterTurnAboutHomeomorph x y) (Set.mem_univ _) (Set.mem_univ _)
  calc
    ‖φ y - φ (quarterTurnAboutHomeomorph x y)‖ =
        ‖φ (quarterTurnAboutHomeomorph x y) - φ y‖ := by
      rw [norm_sub_rev]
    _ ≤ SchwartzMap.seminorm ℝ 0 1 φ *
        ‖quarterTurnAboutHomeomorph x y - y‖ := hmv
    _ ≤ SchwartzMap.seminorm ℝ 0 1 φ * (2 * ‖x - y‖) := by
      gcongr
      rw [quarterTurnAboutHomeomorph_apply]
      calc
        ‖x + Complex.I * (y - x) - y‖ =
            ‖(x - y) + Complex.I * (y - x)‖ := by
              congr 1
              ring
        _ ≤ ‖x - y‖ + ‖Complex.I * (y - x)‖ := norm_add_le _ _
        _ = 2 * ‖x - y‖ := by
          rw [norm_mul]
          simp [norm_sub_rev]
          ring
    _ = (2 * SchwartzMap.seminorm ℝ 0 1 φ) * ‖x - y‖ := by ring

theorem beurlingClosedBallIndicator_quarterTurn_invariant
    (x : ℂ) (R : ℝ) (y : ℂ) :
    beurlingClosedBallIndicator x R (quarterTurnAboutHomeomorph x y) =
      beurlingClosedBallIndicator x R y := by
  by_cases hy : y ∈ Metric.closedBall x R
  · have hqy : quarterTurnAboutHomeomorph x y ∈ Metric.closedBall x R :=
      (quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).2 hy
    simp [beurlingClosedBallIndicator, hy, hqy]
  · have hqy : quarterTurnAboutHomeomorph x y ∉ Metric.closedBall x R := by
      intro h
      exact hy ((quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).1 h)
    simp [beurlingClosedBallIndicator, hy, hqy]

theorem beurlingClosedBallIndicator_apply_center
    {x : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    beurlingClosedBallIndicator x R x = 1 := by
  simp [beurlingClosedBallIndicator, hR]

theorem integrable_beurlingClosedBallIndicator
    (x : ℂ) (R : ℝ) :
    Integrable (beurlingClosedBallIndicator x R) volume := by
  have hball : volume (Metric.closedBall x R) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  unfold beurlingClosedBallIndicator
  exact
    (integrableOn_const hball).integrable_indicator measurableSet_closedBall

/-!
The next class is the first finite-dimensional enlargement of a single disk.
The finite set records a complex coefficient and a radius for each term.  The
common center keeps the exact quarter-turn symmetry, while the coefficients and
radii are allowed to vary from term to term.
-/

def beurlingClosedBallSimple
    (x : ℂ) (s : Finset (ℂ × ℝ)) : ℂ → ℂ :=
  fun y => ∑ t ∈ s, t.1 * beurlingClosedBallIndicator x t.2 y

theorem beurlingClosedBallSimple_quarterTurn_invariant
    (x : ℂ) (s : Finset (ℂ × ℝ)) (y : ℂ) :
    beurlingClosedBallSimple x s (quarterTurnAboutHomeomorph x y) =
      beurlingClosedBallSimple x s y := by
  unfold beurlingClosedBallSimple
  apply Finset.sum_congr rfl
  intro t ht
  rw [beurlingClosedBallIndicator_quarterTurn_invariant]

theorem integrable_beurlingClosedBallSimple
    (x : ℂ) (s : Finset (ℂ × ℝ)) :
    Integrable (beurlingClosedBallSimple x s) volume := by
  unfold beurlingClosedBallSimple
  apply integrable_finsetSum
  intro t ht
  exact (integrable_beurlingClosedBallIndicator x t.2).const_mul t.1

theorem beurlingClosedBallSimple_apply_center
    {x : ℂ} {s : Finset (ℂ × ℝ)}
    (hR : ∀ t ∈ s, 0 ≤ t.2) :
    beurlingClosedBallSimple x s x = ∑ t ∈ s, t.1 := by
  unfold beurlingClosedBallSimple
  apply Finset.sum_congr rfl
  intro t ht
  rw [beurlingClosedBallIndicator_apply_center (hR t ht)]
  simp

/-!
The quadratic disk is the first deliberately non-invariant test function.  Its
quadratic vanishing at the center compensates for the order-two singularity of
the Beurling kernel after quarter-turn pairing.
-/

def beurlingQuadraticClosedBall (x : ℂ) (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall x R).indicator (fun y => (y - x) ^ 2)

theorem beurlingQuadraticClosedBall_quarterTurn_neg
    (x : ℂ) (R : ℝ) (y : ℂ) :
    beurlingQuadraticClosedBall x R (quarterTurnAboutHomeomorph x y) =
      -beurlingQuadraticClosedBall x R y := by
  by_cases hy : y ∈ Metric.closedBall x R
  · have hqy : quarterTurnAboutHomeomorph x y ∈ Metric.closedBall x R :=
      (quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).2 hy
    simp only [beurlingQuadraticClosedBall, Set.indicator_of_mem hqy,
      Set.indicator_of_mem hy]
    rw [quarterTurnAboutHomeomorph_apply]
    calc
      (x + Complex.I * (y - x) - x) ^ 2 =
          (Complex.I * (y - x)) ^ 2 := by ring
      _ = -(y - x) ^ 2 := by
        rw [mul_pow]
        simp [Complex.I_mul_I]
  · have hqy : quarterTurnAboutHomeomorph x y ∉ Metric.closedBall x R := by
      intro h
      exact hy ((quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).1 h)
    simp [beurlingQuadraticClosedBall, hy, hqy]

theorem norm_beurlingQuadraticClosedBall_le
    (x : ℂ) (R : ℝ) (y : ℂ) :
    ‖beurlingQuadraticClosedBall x R y‖ ≤ ‖x - y‖ ^ 2 := by
  by_cases hy : y ∈ Metric.closedBall x R
  · simp [beurlingQuadraticClosedBall, hy, norm_pow, norm_sub_rev]
  · simp [beurlingQuadraticClosedBall, hy]

theorem integrable_beurlingQuadraticClosedBall
    (x : ℂ) (R : ℝ) :
    Integrable (beurlingQuadraticClosedBall x R) volume := by
  have hball : IsCompact (Metric.closedBall x R) := isCompact_closedBall x R
  have hconst :
      IntegrableOn (fun _ : ℂ => (1 : ℂ)) (Metric.closedBall x R) volume := by
    exact integrableOn_const (measure_closedBall_lt_top.ne)
  have hpoly : ContinuousOn (fun y : ℂ => (y - x) ^ 2)
      (Metric.closedBall x R) := by
    fun_prop
  have hprod :
      IntegrableOn
        (fun y : ℂ => (1 : ℂ) * (y - x) ^ 2)
        (Metric.closedBall x R) volume :=
    hconst.mul_continuousOn hpoly hball
  simpa only [one_mul, beurlingQuadraticClosedBall] using
    hprod.integrable_indicator measurableSet_closedBall

def beurlingQuadraticClosedBallMajorant
    (x : ℂ) (m : ℕ) : ℂ → ℝ :=
  (Metric.closedBall x ((m + 1 : ℝ)⁻¹)).indicator
    (fun _ => (Real.pi : ℝ)⁻¹)

theorem integrable_beurlingQuadraticClosedBallMajorant
    (x : ℂ) (m : ℕ) :
    Integrable (beurlingQuadraticClosedBallMajorant x m) volume := by
  unfold beurlingQuadraticClosedBallMajorant
  exact
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
      measurableSet_closedBall

theorem integral_beurlingQuadraticClosedBallMajorant
    (x : ℂ) (m : ℕ) :
    ∫ y, beurlingQuadraticClosedBallMajorant x m y ∂volume =
      (volume (Metric.closedBall x ((m + 1 : ℝ)⁻¹))).toReal *
        (Real.pi : ℝ)⁻¹ := by
  unfold beurlingQuadraticClosedBallMajorant
  rw [integral_indicator_const _ measurableSet_closedBall]
  simp [Measure.real, smul_eq_mul]

theorem tendsto_integral_beurlingQuadraticClosedBallMajorant
    (x : ℂ) :
    Tendsto
      (fun m : ℕ => ∫ y, beurlingQuadraticClosedBallMajorant x m y ∂volume)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => ((m + 1 : ℝ)⁻¹) ^ 2)
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun m : ℕ => (m + 1 : ℝ)⁻¹)
        atTop (𝓝 0) := by
      apply Tendsto.inv_tendsto_atTop
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using hinv.pow 2
  have hform :
      (fun m : ℕ => ∫ y, beurlingQuadraticClosedBallMajorant x m y ∂volume) =
        (fun m : ℕ =>
          (volume (Metric.closedBall x ((m + 1 : ℝ)⁻¹))).toReal *
            (Real.pi : ℝ)⁻¹) := by
    funext m
    exact integral_beurlingQuadraticClosedBallMajorant x m
  rw [hform]
  simp_rw [Complex.volume_closedBall]
  simp [Measure.real, ENNReal.toReal_mul, Real.pi_pos.le]
  have hnonneg : ∀ m : ℕ, 0 ≤ (m + 1 : ℝ)⁻¹ := by
    intro m
    positivity
  have hreal :
      (fun m : ℕ => (ENNReal.ofReal ((m + 1 : ℝ)⁻¹)).toReal ^ 2) =
        (fun m : ℕ => ((m + 1 : ℝ)⁻¹) ^ 2) := by
    funext m
    rw [ENNReal.toReal_ofReal (hnonneg m)]
  rw [hreal]
  exact hlim

theorem norm_beurlingQuadraticClosedBall_pairing_le
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) (m : ℕ)
    (x : ℂ) (R : ℝ) (y : ℂ) :
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y) *
          (beurlingQuadraticClosedBall x R y -
            beurlingQuadraticClosedBall x R
              (quarterTurnAboutHomeomorph x y)))‖ ≤
      beurlingQuadraticClosedBallMajorant x m y := by
  by_cases hz : x - y ∈ beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)
  · have hnormpos : 0 < ‖x - y‖ := lt_of_lt_of_le hε₁ hz.1
    have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hnormpos
    have hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹) := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm, norm_sub_rev] using hz.2.le
    have hdiff :
        beurlingQuadraticClosedBall x R y -
            beurlingQuadraticClosedBall x R
              (quarterTurnAboutHomeomorph x y) =
          2 * beurlingQuadraticClosedBall x R y := by
      rw [beurlingQuadraticClosedBall_quarterTurn_neg]
      ring
    have hA :
        ‖(beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y)‖ =
          (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 := by
      rw [Set.indicator_of_mem hz, beurlingKernel_norm_eq hxy0]
    have hcancel :
        ‖x - y‖⁻¹ ^ 2 *
            ‖beurlingQuadraticClosedBall x R y‖ ≤ 1 := by
      calc
        ‖x - y‖⁻¹ ^ 2 *
              ‖beurlingQuadraticClosedBall x R y‖ ≤
            ‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (norm_beurlingQuadraticClosedBall_le x R y) (by positivity)
        _ = 1 := by field_simp [hxy0]
    unfold beurlingQuadraticClosedBallMajorant
    rw [Set.indicator_of_mem hball]
    calc
      ‖(1 / 2 : ℂ) *
          ((beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y) *
            (beurlingQuadraticClosedBall x R y -
              beurlingQuadraticClosedBall x R
              (quarterTurnAboutHomeomorph x y)))‖ =
          ‖(beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y)‖ *
            ‖beurlingQuadraticClosedBall x R y‖ := by
        rw [hdiff]
        simp only [norm_mul]
        rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num,
          show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        ring
      _ = ((Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2) *
            ‖beurlingQuadraticClosedBall x R y‖ := by rw [hA]
      _ ≤ (Real.pi : ℝ)⁻¹ * 1 := by
        calc
          ((Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2) *
                ‖beurlingQuadraticClosedBall x R y‖ =
              (Real.pi : ℝ)⁻¹ *
                (‖x - y‖⁻¹ ^ 2 *
                  ‖beurlingQuadraticClosedBall x R y‖) := by ring
          _ ≤ (Real.pi : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ = (Real.pi : ℝ)⁻¹ := by ring
  · unfold beurlingQuadraticClosedBallMajorant
    by_cases hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹)
    · simp only [Set.indicator_of_notMem hz, norm_zero, zero_mul,
        Set.indicator_of_mem hball]
      simpa using (show (0 : ℝ) ≤ Real.pi⁻¹ by positivity)
    · simp only [Set.indicator_of_notMem hz, norm_zero, zero_mul,
        Set.indicator_of_notMem hball]
      norm_num

theorem beurlingAnnulus_indicator_kernel_mul_I
    {ε₁ ε₂ : ℝ} (z : ℂ) :
    (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (Complex.I * z) =
      -(beurlingAnnulus ε₁ ε₂).indicator beurlingKernel z := by
  by_cases hz : z ∈ beurlingAnnulus ε₁ ε₂
  · have hIz : Complex.I * z ∈ beurlingAnnulus ε₁ ε₂ := by
      simpa [beurlingAnnulus, norm_mul] using hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hIz]
    rw [beurlingKernel_mul_I]
  · have hIz : Complex.I * z ∉ beurlingAnnulus ε₁ ε₂ := by
      intro h
      apply hz
      simpa [beurlingAnnulus, norm_mul] using h
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hIz, neg_zero]

theorem beurlingAnnulus_indicator_kernel_centered_quarter_turn
    {ε₁ ε₂ : ℝ} (x y : ℂ) :
    (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel
        (x - (x + Complex.I * (y - x))) =
      -(beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) := by
  rw [show x - (x + Complex.I * (y - x)) = Complex.I * (x - y) by ring]
  exact beurlingAnnulus_indicator_kernel_mul_I (x - y)

theorem beurlingTruncatedKernel_centered_quarter_turn
    (ε : ℝ) (x y : ℂ) :
    beurlingTruncatedKernel ε
        (x - (x + Complex.I * (y - x))) =
      -beurlingTruncatedKernel ε (x - y) := by
  rw [show x - (x + Complex.I * (y - x)) = Complex.I * (x - y) by ring]
  exact beurlingTruncatedKernel_mul_I ε (x - y)

theorem beurlingTruncatedKernel_sub_eq_annulus_indicator
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (z : ℂ) :
    beurlingTruncatedKernel ε₁ z -
        beurlingTruncatedKernel ε₂ z =
      (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel z := by
  by_cases h₁ : ε₁ ≤ ‖z‖
  · by_cases h₂ : ε₂ ≤ ‖z‖
    · simp [beurlingAnnulus, beurlingTruncatedKernel, h₁, h₂]
    · have hz₂ : ‖z‖ < ε₂ := lt_of_not_ge h₂
      simp [beurlingAnnulus, beurlingTruncatedKernel, h₁, h₂, hz₂]
  · have hz₁ : ‖z‖ < ε₁ := lt_of_not_ge h₁
    have hz₂ : ‖z‖ < ε₂ := lt_of_lt_of_le hz₁ hε
    simp [beurlingAnnulus, beurlingTruncatedKernel, h₁, hz₂]

theorem beurlingTruncatedKernel_sub_norm_le
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (z : ℂ) :
    ‖beurlingTruncatedKernel ε₁ z -
        beurlingTruncatedKernel ε₂ z‖ ≤
      (Real.pi : ℝ)⁻¹ * ε₁⁻¹ ^ 2 := by
  rw [beurlingTruncatedKernel_sub_eq_annulus_indicator hε]
  by_cases hz : z ∈ beurlingAnnulus ε₁ ε₂
  · simp only [Set.indicator_of_mem hz]
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hε₁ hz.1
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
    rw [beurlingKernel_norm_eq hz0]
    have hinv : ‖z‖⁻¹ ≤ ε₁⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hε₁ hz.1
    have hpow : ‖z‖⁻¹ ^ 2 ≤ ε₁⁻¹ ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hinv 2
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · simp only [Set.indicator_of_notMem hz, norm_zero]
    positivity

theorem measurable_beurlingKernel :
    Measurable beurlingKernel := by
  unfold beurlingKernel
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

theorem measurable_beurlingTruncatedKernel (ε : ℝ) :
    Measurable (beurlingTruncatedKernel ε) := by
  unfold beurlingTruncatedKernel
  refine Measurable.ite ?_ measurable_beurlingKernel measurable_const
  exact measurableSet_le measurable_const measurable_id.norm

theorem aestronglyMeasurable_beurlingTruncatedIntegrand
    {ε : ℝ} {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) (x : ℂ) :
    AEStronglyMeasurable
      (fun y => beurlingTruncatedKernel ε (x - y) * f y) volume := by
  exact
    ((measurable_beurlingTruncatedKernel ε).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hf

theorem integrable_beurlingTruncatedIntegrand
    {ε : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hε : 0 < ε) (hf : Integrable f volume) :
    Integrable
      (fun y => beurlingTruncatedKernel ε (x - y) * f y) volume := by
  apply Integrable.bdd_mul hf
    ((measurable_beurlingTruncatedKernel ε).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  filter_upwards [] with y
  exact beurlingTruncatedKernel_norm_le hε

theorem SchwartzMap.integrable_beurlingTruncatedIntegrand
    (φ : SchwartzMap ℂ ℂ) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Integrable
      (fun y => beurlingTruncatedKernel ε (x - y) * φ y)
      volume := by
  apply Integrable.bdd_mul
    (memLp_one_iff_integrable.mp (φ.memLp 1 (volume : Measure ℂ)))
    ((measurable_beurlingTruncatedKernel ε).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  filter_upwards [] with y
  exact beurlingTruncatedKernel_norm_le hε

def beurlingLocalInverseMajorant (z : ℂ) : ℝ :=
  (Metric.ball 0 1).indicator (fun w => ‖w‖ ^ (-1 : ℝ)) z

theorem integrable_beurlingLocalInverseMajorant :
    Integrable beurlingLocalInverseMajorant volume := by
  unfold beurlingLocalInverseMajorant
  refine
    (integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ) (μ := volume)
      (f := fun w : ℂ => ‖w‖ ^ (-1 : ℝ)) (C := 1) (α := 1) (r := 1)
      (by norm_num : 1 ≤ Module.finrank ℝ ℂ)
      (by norm_num : (1 : ℝ) < Module.finrank ℝ ℂ) ?_ ?_).integrable_indicator
      measurableSet_ball
  · exact Eventually.of_forall (fun z => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _),
        one_mul]
      exact le_rfl)
  · exact (measurable_id.norm.pow_const (-1 : ℝ)).aestronglyMeasurable

theorem beurlingLocalInverseMajorant_centered_integrable (x : ℂ) :
    Integrable (fun y => beurlingLocalInverseMajorant (x - y)) volume := by
  let q : ℂ → ℂ := fun y => x - y
  have hneg : MeasurePreserving (fun z : ℂ => -z) volume volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun z : ℂ => z + x) volume volume :=
    measurePreserving_add_right volume x
  have hqmp : MeasurePreserving q volume volume := by
    convert hadd.comp hneg using 1
    · funext z
      simp [q, sub_eq_add_neg, add_comm]
  have hcomp := MeasurePreserving.integrable_comp_of_integrable hqmp
    (g := beurlingLocalInverseMajorant) integrable_beurlingLocalInverseMajorant
  simpa [q, Function.comp_def] using hcomp

def beurlingLocalInverseMajorantOnBall (x : ℂ) (m : ℕ) : ℂ → ℝ :=
  (Metric.ball x ((m + 1 : ℝ)⁻¹)).indicator
    (fun y => beurlingLocalInverseMajorant (x - y))

theorem integrable_beurlingLocalInverseMajorantOnBall
    (x : ℂ) (m : ℕ) :
    Integrable (beurlingLocalInverseMajorantOnBall x m) volume := by
  unfold beurlingLocalInverseMajorantOnBall
  exact
    (beurlingLocalInverseMajorant_centered_integrable x).integrableOn.integrable_indicator
      measurableSet_ball

theorem integral_beurlingLocalInverseMajorantOnBall_eq
    (x : ℂ) (m : ℕ) :
    ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume =
      ∫ y in Metric.ball x ((m + 1 : ℝ)⁻¹),
        beurlingLocalInverseMajorant (x - y) ∂volume := by
  unfold beurlingLocalInverseMajorantOnBall
  rw [integral_indicator measurableSet_ball]

theorem tendsto_integral_beurlingLocalInverseMajorantOnBall
    (x : ℂ) :
    Tendsto
      (fun m : ℕ => ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ => (m + 1 : ℝ)⁻¹)
      atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun m : ℕ => ((m + 1 : ℝ)⁻¹) ^ 2)
      atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hmeasure : Tendsto
      (fun m : ℕ => volume (Metric.ball x ((m + 1 : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    have hform : (fun m : ℕ => volume (Metric.ball x ((m + 1 : ℝ)⁻¹))) =
        (fun m : ℕ => ENNReal.ofReal ((m + 1 : ℝ)⁻¹) ^ 2 *
          (NNReal.pi : ℝ≥0∞)) := by
      funext m
      exact Complex.volume_ball x ((m + 1 : ℝ)⁻¹)
    rw [hform]
    have hpow : Tendsto
        (fun m : ℕ => ENNReal.ofReal ((m + 1 : ℝ)⁻¹) ^ 2)
        atTop (𝓝 0) := by
      have hpow' : Tendsto
          (fun m : ℕ => ENNReal.ofReal (((m + 1 : ℝ)⁻¹) ^ 2))
          atTop (𝓝 (ENNReal.ofReal 0)) := ENNReal.tendsto_ofReal hlim
      convert hpow' using 1
      · funext m
        rw [ENNReal.ofReal_pow (by positivity)]
      · simp
    simpa using ENNReal.Tendsto.mul_const hpow
      (by simp : (0 : ℝ≥0∞) ≠ 0 ∨ (NNReal.pi : ℝ≥0∞) ≠ ∞)
  have hfi : Integrable (fun y => beurlingLocalInverseMajorant (x - y)) volume :=
    beurlingLocalInverseMajorant_centered_integrable x
  rw [show (fun m : ℕ =>
      ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume) =
      (fun m : ℕ => ∫ y in Metric.ball x ((m + 1 : ℝ)⁻¹),
        beurlingLocalInverseMajorant (x - y) ∂volume) by
    funext m
    exact integral_beurlingLocalInverseMajorantOnBall_eq x m]
  exact hfi.tendsto_setIntegral_nhds_zero hmeasure

/-!
The preceding dominated-convergence statement is enough for existence of a
vanishing modulus, but the radial singularity actually gives a linear rate.
We record that rate in a form that does not depend on evaluating the unit-ball
constant.  The proof is the two-dimensional scaling law for `‖z‖⁻¹`, together
with the affine reflection `y ↦ x - y`.
-/

theorem integral_beurlingLocalInverseMajorant_on_ball_eq_linear
    (x : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫ y in Metric.ball x r, beurlingLocalInverseMajorant (x - y) ∂volume =
      r * ∫ z, beurlingLocalInverseMajorant z ∂volume := by
  let q : ℂ → ℂ := fun y => x - y
  have hneg : MeasurePreserving (fun z : ℂ => -z) volume volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun z : ℂ => z + x) volume volume :=
    measurePreserving_add_right volume x
  have hqmp : MeasurePreserving q volume volume := by
    convert hadd.comp hneg using 1
    · funext z
      simp [q, sub_eq_add_neg, add_comm]
  have hqemb : MeasurableEmbedding q := by
    change MeasurableEmbedding (fun y : ℂ => x - y)
    exact (Homeomorph.subLeft x).measurableEmbedding
  have hcenter :
      ∫ y in Metric.ball x r, beurlingLocalInverseMajorant (x - y) ∂volume =
        ∫ z in Metric.ball 0 r, beurlingLocalInverseMajorant z ∂volume := by
    have hpre := hqmp.setIntegral_preimage_emb hqemb
      beurlingLocalInverseMajorant (Metric.ball 0 r)
    have hpreimage : q ⁻¹' Metric.ball 0 r = Metric.ball x r := by
      ext y
      simp [q, dist_eq_norm, norm_sub_rev]
    rw [← hpreimage]
    simpa [q, Function.comp_def] using hpre
  let I : ℝ := ∫ z, beurlingLocalInverseMajorant z ∂volume
  have hunit :
      ∫ z in Metric.ball 0 1, beurlingLocalInverseMajorant z ∂volume = I := by
    change ∫ z in Metric.ball 0 1,
        (Metric.ball 0 1).indicator (fun w : ℂ => ‖w‖ ^ (-1 : ℝ)) z ∂volume =
        ∫ z, (Metric.ball 0 1).indicator (fun w : ℂ => ‖w‖ ^ (-1 : ℝ)) z ∂volume
    rw [setIntegral_indicator measurableSet_ball, Set.inter_self,
      integral_indicator measurableSet_ball]
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (E := ℂ) (F := ℝ) (μ := (volume : Measure ℂ))
    (R := r) beurlingLocalInverseMajorant
    (Metric.ball (0 : ℂ) 1) hr
  have hball_smul :
      (r : ℝ) • (Metric.ball (0 : ℂ) 1 : Set ℂ) = Metric.ball (0 : ℂ) r := by
    rw [_root_.smul_ball (ne_of_gt hr) (0 : ℂ) 1]
    simp [Real.norm_eq_abs, abs_of_pos hr]
  have hlocal_smul : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      beurlingLocalInverseMajorant (r • w) =
        r⁻¹ * beurlingLocalInverseMajorant w := by
    intro w hw
    have hw_norm : ‖w‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hw
    have hrw_norm : ‖r • w‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc
        r * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
        _ < 1 := by simpa using hw_norm
    have hw_mem : w ∈ Metric.ball (0 : ℂ) 1 := hw
    have hrw_mem : r • w ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hrw_norm
    rw [beurlingLocalInverseMajorant, Set.indicator_of_mem hrw_mem,
      beurlingLocalInverseMajorant, Set.indicator_of_mem hw_mem,
      Real.rpow_neg_one, Real.rpow_neg_one, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev]
    ring
  have hleft :
      ∫ w in Metric.ball (0 : ℂ) 1,
          beurlingLocalInverseMajorant (r • w) ∂volume = r⁻¹ * I := by
    calc
      ∫ w in Metric.ball (0 : ℂ) 1,
          beurlingLocalInverseMajorant (r • w) ∂volume =
          ∫ w in Metric.ball (0 : ℂ) 1,
            r⁻¹ * beurlingLocalInverseMajorant w ∂volume := by
              apply setIntegral_congr_fun measurableSet_ball
              intro w hw
              exact hlocal_smul w hw
      _ = r⁻¹ * ∫ w in Metric.ball (0 : ℂ) 1,
            beurlingLocalInverseMajorant w ∂volume := by
              rw [integral_const_mul]
      _ = r⁻¹ * I := by rw [hunit]
  have hscale' : r⁻¹ * I = (r ^ 2)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) r,
        beurlingLocalInverseMajorant z ∂volume) := by
    simpa [hball_smul, Complex.finrank_real_complex, smul_eq_mul] using hleft.symm.trans hscale
  have hball :
      ∫ z in Metric.ball (0 : ℂ) r, beurlingLocalInverseMajorant z ∂volume = r * I := by
    field_simp [ne_of_gt hr] at hscale'
    exact hscale'.symm
  rw [hcenter, hball]

theorem integral_beurlingLocalInverseMajorantOnBall_eq_linear
    (x : ℂ) (m : ℕ) :
    ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume =
      ((m + 1 : ℝ)⁻¹) * ∫ z, beurlingLocalInverseMajorant z ∂volume := by
  rw [integral_beurlingLocalInverseMajorantOnBall_eq]
  apply integral_beurlingLocalInverseMajorant_on_ball_eq_linear
  · exact inv_pos.mpr (by positivity)
  · have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    exact inv_le_one_of_one_le₀ hbase

theorem integral_beurlingLocalInverseMajorant_eq_two_mul_pi :
    ∫ z, beurlingLocalInverseMajorant z ∂volume = 2 * Real.pi := by
  have hpolar := Complex.integral_comp_polarCoord_symm
    (f := beurlingLocalInverseMajorant)
  have hpoint : ∀ p ∈ Complex.polarCoord.target,
      p.1 • beurlingLocalInverseMajorant (Complex.polarCoord.symm p) =
        (Set.Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.1 := by
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      simpa [abs_of_pos hp0] using Complex.norm_polarCoord_symm p
    by_cases hp1 : p.1 < 1
    · have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact hp1
      rw [beurlingLocalInverseMajorant, Set.indicator_of_mem hmem,
        Real.rpow_neg_one, hnorm,
        Set.indicator_of_mem (show p.1 ∈ Set.Ioo (0 : ℝ) 1 from ⟨hp0, hp1⟩)]
      simp [smul_eq_mul, hp0.ne']
    · have hmem : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) 1 := by
        intro hz
        have hz' : ‖Complex.polarCoord.symm p‖ < 1 := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        have hz'' : p.1 < 1 := by
          simpa [hnorm, abs_of_pos hp0] using hz'
        exact hp1 hz''
      have hpnot : p.1 ∉ Set.Ioo (0 : ℝ) 1 := by
        intro hp'
        exact hp1 hp'.2
      rw [beurlingLocalInverseMajorant, Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem hpnot]
      simp
  have hpolar_ball :
      ∫ p in Complex.polarCoord.target,
          p.1 • beurlingLocalInverseMajorant (Complex.polarCoord.symm p) ∂volume =
        ∫ p in (Set.Ioo (0 : ℝ) 1) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ) ∂volume := by
    rw [Complex.polarCoord_target]
    calc
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 • beurlingLocalInverseMajorant (Complex.polarCoord.symm p) ∂volume =
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            (Set.Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.1 ∂volume := by
              apply setIntegral_congr_fun
                (measurableSet_Ioi.prod measurableSet_Ioo)
              intro p hp
              exact hpoint p ⟨hp.1, hp.2⟩
      _ = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ) ∂volume := by
            rw [Measure.volume_eq_prod ℝ ℝ]
            calc
              ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
                  (Set.Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.1 ∂volume.prod volume =
                  (∫ u in Set.Ioi (0 : ℝ),
                    (Set.Ioo (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) u ∂volume) *
                    ∫ v in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) ∂volume := by
                      simpa using setIntegral_prod_mul
                        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
                        (fun u : ℝ => (Set.Ioo (0 : ℝ) 1).indicator
                          (fun _ => (1 : ℝ)) u)
                        (fun _ : ℝ => (1 : ℝ)) (Set.Ioi (0 : ℝ))
                        (Set.Ioo (-Real.pi) Real.pi)
              _ = (∫ u in Set.Ioo (0 : ℝ) 1, (1 : ℝ) ∂volume) *
                    ∫ v in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) ∂volume := by
                      rw [setIntegral_indicator measurableSet_Ioo]
                      rw [Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
              _ = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
                    (1 : ℝ) ∂volume.prod volume := by
                      symm
                      simpa using setIntegral_prod_mul
                        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
                        (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ))
                        (Set.Ioo (0 : ℝ) 1) (Set.Ioo (-Real.pi) Real.pi)
  have hpolar_ball_value :
      ∫ p in (Set.Ioo (0 : ℝ) 1) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ) ∂volume = 2 * Real.pi := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    calc
      ∫ p in (Set.Ioo (0 : ℝ) 1) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ) ∂volume =
          (∫ x in Set.Ioo (0 : ℝ) 1, (1 : ℝ) ∂volume) *
            ∫ y in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) ∂volume := by
              simpa only [one_mul, Measure.volume_eq_prod ℝ ℝ] using setIntegral_prod_mul
                (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
                (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ))
                (Set.Ioo (0 : ℝ) 1) (Set.Ioo (-Real.pi) Real.pi)
      _ = 2 * Real.pi := by
        simp only [setIntegral_const, smul_eq_mul, mul_one]
        rw [Real.volume_real_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1),
          Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos.le])]
        ring
  calc
    ∫ z, beurlingLocalInverseMajorant z ∂volume =
        ∫ p in Complex.polarCoord.target,
          p.1 • beurlingLocalInverseMajorant (Complex.polarCoord.symm p) ∂volume :=
      hpolar.symm
    _ = 2 * Real.pi := by rw [hpolar_ball, hpolar_ball_value]

/-!
The first physical-side change of variables.  The affine reflection
`y ↦ x - y` preserves Lebesgue measure, so the truncated singular integral
can be written with the kernel centered at the origin.  This is the form in
which the later Fourier calculation and the principal-value cancellation
meet.
-/

theorem beurlingTruncatedIntegral_centered_eq
    {ε : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hε : 0 < ε) (hf : Integrable f volume) :
    beurlingTruncatedIntegral ε f x =
      ∫ z, beurlingTruncatedKernel ε z * f (x - z) ∂volume := by
  let q : ℂ → ℂ := fun y => x - y
  let F : ℂ → ℂ := fun z => beurlingTruncatedKernel ε z * f (x - z)
  have hneg : MeasurePreserving (fun z : ℂ => -z) volume volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun z : ℂ => z + x) volume volume :=
    measurePreserving_add_right volume x
  have hqmp : MeasurePreserving q volume volume := by
    convert hadd.comp hneg using 1
    · funext z
      simp [q, sub_eq_add_neg, add_comm]
  have hqemb : MeasurableEmbedding q := by
    change MeasurableEmbedding (fun y : ℂ => x - y)
    exact (Homeomorph.subLeft x).measurableEmbedding
  have hbase : Integrable (fun y =>
      beurlingTruncatedKernel ε (x - y) * f y) volume :=
    integrable_beurlingTruncatedIntegrand hε hf
  have hFcomp : Integrable (F ∘ q) volume := by
    simpa [F, q, Function.comp_def] using hbase
  have hF : Integrable F volume := by
    have htwice : Integrable ((F ∘ q) ∘ q) volume :=
      hqmp.integrable_comp_of_integrable hFcomp
    convert htwice using 1
    funext z
    simp [F, q, Function.comp_def, sub_sub_cancel]
  calc
    beurlingTruncatedIntegral ε f x = ∫ y, F (q y) ∂volume := by
      unfold beurlingTruncatedIntegral
      congr 1
      funext y
      simp [F, q, sub_sub_cancel]
    _ = ∫ z, F z ∂volume := hqmp.integral_comp hqemb F
    _ = ∫ z, beurlingTruncatedKernel ε z * f (x - z) ∂volume := by
      rfl

theorem norm_beurlingTruncatedIntegral_le
    {ε : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hε : 0 < ε) (hf : Integrable f volume) :
    ‖beurlingTruncatedIntegral ε f x‖ ≤
      ((Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2) * ∫ y, ‖f y‖ ∂volume := by
  have hbound :
      ∀ᵐ y ∂volume,
        ‖beurlingTruncatedKernel ε (x - y) * f y‖ ≤
          ((Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2) * ‖f y‖ := by
    filter_upwards [] with y
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_right
        (beurlingTruncatedKernel_norm_le hε) (norm_nonneg _)
  calc
    ‖beurlingTruncatedIntegral ε f x‖ ≤
        ∫ y, ((Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2) * ‖f y‖ ∂volume := by
      unfold beurlingTruncatedIntegral
      exact
        norm_integral_le_of_norm_le
          (hf.norm.const_mul ((Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2)) hbound
    _ = ((Real.pi : ℝ)⁻¹ * ε⁻¹ ^ 2) * ∫ y, ‖f y‖ ∂volume := by
      rw [integral_const_mul]

theorem tendsto_beurlingTruncatedKernel_nat
    {z : ℂ} (hz : z ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) z)
      atTop
      (𝓝 (beurlingKernel z)) := by
  have hlim :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply tendsto_const_nhds.congr'
  filter_upwards [hlim.eventually (eventually_lt_nhds hnorm)] with n hn
  exact (beurlingTruncatedKernel_eq_beurlingKernel hn.le).symm

theorem tendsto_beurlingTruncatedIntegral_nat_of_away_from_singularity
    {δ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hδ : 0 < δ) (hf : Integrable f volume)
    (haway :
      ∀ᵐ y ∂volume, f y = 0 ∨ δ ≤ ‖x - y‖) :
    Tendsto
      (fun n : ℕ =>
        beurlingTruncatedIntegral ((n + 1 : ℝ)⁻¹) f x)
      atTop
      (𝓝 (∫ y, beurlingKernel (x - y) * f y ∂volume)) := by
  let C : ℝ := (Real.pi : ℝ)⁻¹ * δ⁻¹ ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound_integrable : Integrable (fun y => C * ‖f y‖) volume := by
    exact hf.norm.const_mul C
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun y =>
            beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y)
          volume := by
    intro n
    exact aestronglyMeasurable_beurlingTruncatedIntegrand
      hf.aestronglyMeasurable x
  have hF_bound :
      ∀ n : ℕ, ∀ᵐ y ∂volume,
        ‖beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y‖ ≤
          C * ‖f y‖ := by
    intro n
    filter_upwards [haway] with y hy
    by_cases hfy : f y = 0
    · simp [hfy]
    · have hdist : δ ≤ ‖x - y‖ := hy.resolve_left hfy
      rw [norm_mul]
      exact
        mul_le_mul_of_nonneg_right
          (by
            simpa [C] using
              beurlingTruncatedKernel_norm_le_of_norm_ge hδ hdist)
          (norm_nonneg _)
  have hF_lim :
      ∀ᵐ y ∂volume, Tendsto
        (fun n : ℕ =>
          beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y)
        atTop
        (𝓝 (beurlingKernel (x - y) * f y)) := by
    filter_upwards [haway] with y hy
    by_cases hfy : f y = 0
    · simp [hfy]
    · have hdist : δ ≤ ‖x - y‖ := hy.resolve_left hfy
      have hxy : x - y ≠ 0 := by
        apply norm_pos_iff.mp
        exact lt_of_lt_of_le hδ hdist
      simpa only using
        (tendsto_beurlingTruncatedKernel_nat hxy).mul_const (f y)
  have hresult := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ))
    (F := fun n y =>
      beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y)
    (f := fun y => beurlingKernel (x - y) * f y)
    (fun y => C * ‖f y‖)
    hF_meas hbound_integrable hF_bound hF_lim
  simpa only [beurlingTruncatedIntegral] using hresult

def beurlingQuadraticClosedBallGlobalMajorant
    (x : ℂ) (R : ℝ) : ℂ → ℝ :=
  (Metric.closedBall x R).indicator (fun _ => (Real.pi : ℝ)⁻¹)

theorem integrable_beurlingQuadraticClosedBallGlobalMajorant
    (x : ℂ) (R : ℝ) :
    Integrable (beurlingQuadraticClosedBallGlobalMajorant x R) volume := by
  unfold beurlingQuadraticClosedBallGlobalMajorant
  exact
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
      measurableSet_closedBall

theorem norm_beurlingQuadraticClosedBall_truncatedIntegrand_le
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) (R : ℝ) (y : ℂ) :
    ‖beurlingTruncatedKernel ε (x - y) *
        beurlingQuadraticClosedBall x R y‖ ≤
      beurlingQuadraticClosedBallGlobalMajorant x R y := by
  by_cases hy : y ∈ Metric.closedBall x R
  · unfold beurlingQuadraticClosedBallGlobalMajorant
    rw [Set.indicator_of_mem hy]
    by_cases hε' : ε ≤ ‖x - y‖
    · have hxy0 : x - y ≠ 0 := by
        apply norm_pos_iff.mp
        exact lt_of_lt_of_le hε hε'
      rw [beurlingTruncatedKernel_eq_beurlingKernel hε',
        norm_mul, beurlingKernel_norm_eq hxy0]
      simp only [beurlingQuadraticClosedBall, Set.indicator_of_mem hy, norm_pow]
      have hnorm : ‖y - x‖ = ‖x - y‖ := by
        rw [norm_sub_rev]
      rw [hnorm]
      have hcancel : ‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ 2 = 1 := by
        field_simp [hxy0]
      calc
        (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ 2 =
            (Real.pi : ℝ)⁻¹ *
              (‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ 2) := by ring
        _ = (Real.pi : ℝ)⁻¹ * 1 := by rw [hcancel]
        _ ≤ (Real.pi : ℝ)⁻¹ := by simp
    · simp [beurlingTruncatedKernel, hε']
      positivity
  · simp [beurlingQuadraticClosedBall,
      beurlingQuadraticClosedBallGlobalMajorant, hy]

theorem beurlingQuadraticClosedBall_principalValue_tendsto_kernelIntegral
    (x : ℂ) (R : ℝ) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingQuadraticClosedBall x R) x)
      atTop
      (𝓝 (∫ y,
        beurlingKernel (x - y) * beurlingQuadraticClosedBall x R y
        ∂volume)) := by
  have hf : Integrable (beurlingQuadraticClosedBall x R) volume :=
    integrable_beurlingQuadraticClosedBall x R
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun y =>
            beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) *
              beurlingQuadraticClosedBall x R y)
          volume := by
    intro n
    exact aestronglyMeasurable_beurlingTruncatedIntegrand
      hf.aestronglyMeasurable x
  have hbound_integrable :
      Integrable (beurlingQuadraticClosedBallGlobalMajorant x R) volume :=
    integrable_beurlingQuadraticClosedBallGlobalMajorant x R
  have hF_bound :
      ∀ n : ℕ, ∀ᵐ y ∂volume,
        ‖beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) *
            beurlingQuadraticClosedBall x R y‖ ≤
          beurlingQuadraticClosedBallGlobalMajorant x R y := by
    intro n
    filter_upwards [] with y
    exact norm_beurlingQuadraticClosedBall_truncatedIntegrand_le
      (by positivity) x R y
  have hF_lim :
      ∀ᵐ y ∂volume, Tendsto
        (fun n : ℕ =>
          beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) *
            beurlingQuadraticClosedBall x R y)
        atTop
        (𝓝 (beurlingKernel (x - y) *
          beurlingQuadraticClosedBall x R y)) := by
    filter_upwards [show ∀ᵐ y ∂volume, y ≠ x by
      simp [ae_iff, measure_singleton]] with y hy
    have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    simpa only using
      (tendsto_beurlingTruncatedKernel_nat hxy0).mul_const
        (beurlingQuadraticClosedBall x R y)
  have hresult := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ))
    (F := fun n y =>
      beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) *
        beurlingQuadraticClosedBall x R y)
    (f := fun y =>
      beurlingKernel (x - y) * beurlingQuadraticClosedBall x R y)
    (beurlingQuadraticClosedBallGlobalMajorant x R)
    hF_meas hbound_integrable hF_bound hF_lim
  change
    Tendsto
      (fun n : ℕ => ∫ y,
        beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) *
          beurlingQuadraticClosedBall x R y ∂volume)
      atTop
      (𝓝 (∫ y,
        beurlingKernel (x - y) * beurlingQuadraticClosedBall x R y
        ∂volume))
  exact hresult

theorem beurlingQuadraticClosedBall_kernel_integrand_ae
    {x : ℂ} {R : ℝ} :
    ∀ᵐ y ∂volume,
      beurlingKernel (x - y) * beurlingQuadraticClosedBall x R y =
        (Metric.closedBall x R).indicator
          (fun _ => -((Real.pi : ℂ)⁻¹)) y := by
  filter_upwards [show ∀ᵐ y ∂volume, y ≠ x by
    simp [ae_iff, measure_singleton]] with y hy
  by_cases hball : y ∈ Metric.closedBall x R
  · have hxy : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
    simp only [beurlingQuadraticClosedBall, Set.indicator_of_mem hball]
    rw [beurlingKernel, if_neg hxy]
    field_simp [hxy]
    ring
  · simp [beurlingQuadraticClosedBall, hball]

theorem integral_beurlingQuadraticClosedBall_kernel
    {x : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    ∫ y, beurlingKernel (x - y) * beurlingQuadraticClosedBall x R y ∂volume =
      -((R : ℂ) ^ 2) := by
  have hconst :
      ∫ y,
          (Metric.closedBall x R).indicator
            (fun _ => -((Real.pi : ℂ)⁻¹)) y ∂volume =
        -((R : ℂ) ^ 2) := by
    rw [integral_indicator_const _ measurableSet_closedBall]
    simp [Complex.volume_closedBall, Measure.real, smul_eq_mul, hR,
      ENNReal.toReal_ofReal, Real.pi_pos.le]
  rw [integral_congr_ae beurlingQuadraticClosedBall_kernel_integrand_ae]
  exact hconst

theorem beurlingQuadraticClosedBall_principalValue_tendsto
    {x : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingQuadraticClosedBall x R) x)
      atTop (𝓝 (-((R : ℂ) ^ 2))) := by
  have hlim :=
    beurlingQuadraticClosedBall_principalValue_tendsto_kernelIntegral x R
  rw [integral_beurlingQuadraticClosedBall_kernel hR] at hlim
  exact hlim

theorem beurlingTruncatedIntegralSequence_tendsto_of_away_from_singularity
    {δ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hδ : 0 < δ) (hf : Integrable f volume)
    (haway :
      ∀ᵐ y ∂volume, f y = 0 ∨ δ ≤ ‖x - y‖) :
    Tendsto
      (beurlingTruncatedIntegralSequence f x)
      atTop
      (𝓝 (∫ y, beurlingKernel (x - y) * f y ∂volume)) := by
  change
    Tendsto
      (fun n : ℕ =>
        beurlingTruncatedIntegral ((n + 1 : ℝ)⁻¹) f x)
      atTop
      (𝓝 (∫ y, beurlingKernel (x - y) * f y ∂volume))
  exact tendsto_beurlingTruncatedIntegral_nat_of_away_from_singularity
    hδ hf haway

theorem beurlingTruncatedIntegralSequence_cauchySeq_of_away_from_singularity
    {δ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hδ : 0 < δ) (hf : Integrable f volume)
    (haway :
      ∀ᵐ y ∂volume, f y = 0 ∨ δ ≤ ‖x - y‖) :
    CauchySeq (beurlingTruncatedIntegralSequence f x) := by
  exact
    (beurlingTruncatedIntegralSequence_tendsto_of_away_from_singularity
      hδ hf haway).cauchySeq

theorem beurlingTruncatedIntegral_congr_ae
    {ε : ℝ} {f g : ℂ → ℂ} {x : ℂ}
    (hfg : f =ᵐ[volume] g) :
    beurlingTruncatedIntegral ε f x = beurlingTruncatedIntegral ε g x := by
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  simp [hy]

theorem beurlingTruncatedIntegral_zero
    (ε : ℝ) (x : ℂ) :
    beurlingTruncatedIntegral ε (fun _ : ℂ => 0) x = 0 := by
  simp [beurlingTruncatedIntegral]

theorem beurlingTruncatedIntegral_eq_zero_of_quarterTurnInvariant
    {ε : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hintegrable :
      Integrable
        (fun y => beurlingTruncatedKernel ε (x - y) * f y)
        volume)
    (hinvariant : ∀ᵐ y ∂volume,
      f (quarterTurnAboutHomeomorph x y) = f y) :
    beurlingTruncatedIntegral ε f x = 0 := by
  let q : ℂ → ℂ := quarterTurnAboutHomeomorph x
  let F : ℂ → ℂ :=
    fun y => beurlingTruncatedKernel ε (x - y) * f y
  have hF : Integrable F volume := by
    simpa only [F] using hintegrable
  have hqmp : MeasurePreserving q (volume : Measure ℂ) (volume : Measure ℂ) := by
    simpa only [q] using quarterTurnAboutHomeomorph_measurePreserving x
  have hqemb : MeasurableEmbedding q := by
    simpa only [q] using (quarterTurnAboutHomeomorph x).measurableEmbedding
  have hchange :
      ∫ y, F (q y) ∂volume = ∫ y, F y ∂volume :=
    MeasureTheory.MeasurePreserving.integral_comp hqmp hqemb F
  have hanti : ∫ y, F (q y) ∂volume = ∫ y, -F y ∂volume := by
    apply integral_congr_ae
    filter_upwards [hinvariant] with y hy
    dsimp [F, q]
    rw [hy, quarterTurnAboutHomeomorph_apply,
      beurlingTruncatedKernel_centered_quarter_turn]
    ring
  have hneg : ∫ y, -F y ∂volume = -(∫ y, F y ∂volume) := by
    rw [integral_neg]
  have hzero : (∫ y, F y ∂volume) = -(∫ y, F y ∂volume) :=
    hchange.symm.trans (hanti.trans hneg)
  have hdouble : (2 : ℂ) * (∫ y, F y ∂volume) = 0 := by
    calc
      (2 : ℂ) * (∫ y, F y ∂volume) =
          (∫ y, F y ∂volume) + (∫ y, F y ∂volume) := by ring
      _ = 0 := eq_neg_iff_add_eq_zero.mp hzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hFzero : (∫ y, F y ∂volume) = 0 :=
    (mul_eq_zero.mp hdouble).resolve_left htwo
  simpa only [beurlingTruncatedIntegral, F] using hFzero

theorem beurlingTruncatedIntegral_add
    {ε : ℝ} {f g : ℂ → ℂ} {x : ℂ}
    (hf :
      Integrable
        (fun y => beurlingTruncatedKernel ε (x - y) * f y) volume)
    (hg :
      Integrable
        (fun y => beurlingTruncatedKernel ε (x - y) * g y) volume) :
    beurlingTruncatedIntegral ε (fun y => f y + g y) x =
      beurlingTruncatedIntegral ε f x +
        beurlingTruncatedIntegral ε g x := by
  unfold beurlingTruncatedIntegral
  have hfun :
      (fun y => beurlingTruncatedKernel ε (x - y) * (f y + g y)) =
        (fun y => beurlingTruncatedKernel ε (x - y) * f y) +
          (fun y => beurlingTruncatedKernel ε (x - y) * g y) := by
    funext y
    rw [Pi.add_apply, mul_add]
  rw [hfun]
  change
    (∫ y,
      beurlingTruncatedKernel ε (x - y) * f y +
        beurlingTruncatedKernel ε (x - y) * g y ∂volume) =
      (∫ y, beurlingTruncatedKernel ε (x - y) * f y ∂volume) +
        ∫ y, beurlingTruncatedKernel ε (x - y) * g y ∂volume
  rw [integral_add hf hg]

theorem beurlingTruncatedIntegral_sub_eq_integral
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (h₁ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₁ (x - y) * f y) volume)
    (h₂ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₂ (x - y) * f y) volume) :
    beurlingTruncatedIntegral ε₁ f x -
        beurlingTruncatedIntegral ε₂ f x =
      ∫ y,
        (beurlingTruncatedKernel ε₁ (x - y) -
            beurlingTruncatedKernel ε₂ (x - y)) * f y ∂volume := by
  unfold beurlingTruncatedIntegral
  rw [← integral_sub h₁ h₂]
  congr 1
  funext y
  ring

theorem beurlingTruncatedIntegral_sub_eq_annulus_integral
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {f : ℂ → ℂ} {x : ℂ}
    (h₁ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₁ (x - y) * f y) volume)
    (h₂ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₂ (x - y) * f y) volume) :
    beurlingTruncatedIntegral ε₁ f x -
        beurlingTruncatedIntegral ε₂ f x =
      ∫ y,
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
          f y ∂volume := by
  rw [beurlingTruncatedIntegral_sub_eq_integral h₁ h₂]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [beurlingTruncatedKernel_sub_eq_annulus_indicator hε]

/-- Data for an actual measure-preserving antisymmetry of an annular integral. -/
structure BeurlingAnnularAntisymmetryData
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ} where
  symmetry : ℂ → ℂ
  symmetry_measurePreserving :
    MeasurePreserving symmetry (volume : Measure ℂ) (volume : Measure ℂ)
  symmetry_embedding : MeasurableEmbedding symmetry
  integrable :
    Integrable
      (fun y =>
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)
      volume
  integrand_antisymmetric :
    ∀ᵐ y ∂volume,
      (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel
          (x - symmetry y) * f (symmetry y) =
        -((beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)

theorem BeurlingAnnularAntisymmetryData.integral_eq_zero
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingAnnularAntisymmetryData (ε₁ := ε₁) (ε₂ := ε₂) (f := f) (x := x)) :
    ∫ y,
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
      ∂volume = 0 := by
  let F : ℂ → ℂ :=
    fun y => (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
  have hchange :
      ∫ y, F (D.symmetry y) ∂volume = ∫ y, F y ∂volume :=
    MeasureTheory.MeasurePreserving.integral_comp
      D.symmetry_measurePreserving D.symmetry_embedding F
  have hanti : ∫ y, F (D.symmetry y) ∂volume = ∫ y, -F y ∂volume := by
    apply integral_congr_ae
    exact D.integrand_antisymmetric
  have hneg : ∫ y, -F y ∂volume = -(∫ y, F y ∂volume) := by
    rw [integral_neg]
  have hzero : (∫ y, F y ∂volume) = -(∫ y, F y ∂volume) :=
    hchange.symm.trans (hanti.trans hneg)
  have hdouble : (2 : ℂ) * (∫ y, F y ∂volume) = 0 := by
    calc
      (2 : ℂ) * (∫ y, F y ∂volume) =
          (∫ y, F y ∂volume) + (∫ y, F y ∂volume) := by ring
      _ = 0 := eq_neg_iff_add_eq_zero.mp hzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hFzero : (∫ y, F y ∂volume) = 0 :=
    (mul_eq_zero.mp hdouble).resolve_left htwo
  simpa only [F] using hFzero

/--
If the input is invariant under the quarter-turn about `x`, the concrete
annular Beurling contribution cancels exactly.  This is the first direct
specialization of the abstract antisymmetry interface.
-/
theorem beurlingAnnularIntegral_eq_zero_of_quarterTurnInvariant
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hintegrable :
      Integrable
        (fun y =>
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)
        volume)
    (hinvariant : ∀ᵐ y ∂volume,
      f (quarterTurnAboutHomeomorph x y) = f y) :
    ∫ y,
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
      ∂volume = 0 := by
  apply BeurlingAnnularAntisymmetryData.integral_eq_zero
  refine
    { symmetry := quarterTurnAboutHomeomorph x
      symmetry_measurePreserving := quarterTurnAboutHomeomorph_measurePreserving x
      symmetry_embedding := (quarterTurnAboutHomeomorph x).measurableEmbedding
      integrable := hintegrable
      integrand_antisymmetric := ?_ }
  filter_upwards [hinvariant] with y hy
  rw [hy, quarterTurnAboutHomeomorph_apply,
    beurlingAnnulus_indicator_kernel_centered_quarter_turn]
  ring

/--
The quarter-turn also gives a pairing identity for a general input.  It
rewrites the annular integral as the half-integral of the quarter-turn
difference of `f`; this is the quantitative entry point for replacing exact
invariance by an oscillation estimate.
-/
theorem beurlingAnnularIntegral_eq_half_quarterTurn_difference
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hintegrable :
      Integrable
        (fun y =>
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)
        volume) :
    ∫ y,
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
      ∂volume =
      (1 / 2 : ℂ) *
        ∫ y,
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
            (f y - f (quarterTurnAboutHomeomorph x y))
        ∂volume := by
  let q : ℂ → ℂ := quarterTurnAboutHomeomorph x
  let F : ℂ → ℂ :=
    fun y => (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
  let G : ℂ → ℂ :=
    fun y =>
      (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
        (f y - f (q y))
  have hF : Integrable F volume := by
    simpa only [F] using hintegrable
  have hqmp : MeasurePreserving q (volume : Measure ℂ) (volume : Measure ℂ) := by
    simpa only [q] using quarterTurnAboutHomeomorph_measurePreserving x
  have hqemb : MeasurableEmbedding q := by
    simpa only [q] using (quarterTurnAboutHomeomorph x).measurableEmbedding
  have hFq : Integrable (fun y => F (q y)) volume := by
    have h := hqmp.integrable_comp_of_integrable hF
    simpa only [Function.comp_def] using h
  have hkernel (y : ℂ) :
      (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - q y) =
        -(beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) := by
    dsimp [q]
    rw [quarterTurnAboutHomeomorph_apply]
    exact beurlingAnnulus_indicator_kernel_centered_quarter_turn
      (ε₁ := ε₁) (ε₂ := ε₂) x y
  have hpoint (y : ℂ) : F y + F (q y) = G y := by
    change
      (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y +
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - q y) * f (q y) =
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
          (f y - f (q y))
    rw [hkernel]
    ring
  have hchange :
      ∫ y, F (q y) ∂volume = ∫ y, F y ∂volume :=
    MeasureTheory.MeasurePreserving.integral_comp hqmp hqemb F
  have hsum :
      ∫ y, F y + F (q y) ∂volume = ∫ y, G y ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact hpoint y
  have hresult :
      (∫ y, F y ∂volume) =
        (1 / 2 : ℂ) * ∫ y, G y ∂volume := by
    calc
      (∫ y, F y ∂volume) =
          (1 / 2 : ℂ) *
            ((∫ y, F y ∂volume) + ∫ y, F (q y) ∂volume) := by
        rw [hchange]
        ring
      _ = (1 / 2 : ℂ) * ∫ y, F y + F (q y) ∂volume := by
        rw [integral_add hF hFq]
      _ = (1 / 2 : ℂ) * ∫ y, G y ∂volume := by
        rw [hsum]
  simpa only [F, G, q] using hresult

/--
An oscillation majorant for the quarter-turn pairing controls the norm of the
annular Beurling contribution.
-/
theorem norm_beurlingAnnularIntegral_le_of_quarterTurn_majorant
    {ε₁ ε₂ : ℝ} {f : ℂ → ℂ} {x : ℂ} {g : ℂ → ℝ}
    (hintegrable :
      Integrable
        (fun y =>
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)
        volume)
    (hg : Integrable g volume)
    (hmajorant : ∀ᵐ y ∂volume,
      ‖(1 / 2 : ℂ) *
          ((beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
            (f y - f (quarterTurnAboutHomeomorph x y)))‖ ≤
        g y) :
    ‖∫ y,
        (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y
      ∂volume‖ ≤ ∫ y, g y ∂volume := by
  rw [beurlingAnnularIntegral_eq_half_quarterTurn_difference hintegrable]
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le hg hmajorant

/--
The quarter-turn oscillation estimate controls the distance between two
truncations.  The annular integrability needed by the pairing identity is
derived from the two truncated integrability hypotheses.
-/
theorem dist_beurlingTruncatedIntegral_sub_le_of_quarterTurn_majorant
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {f : ℂ → ℂ} {x : ℂ} {g : ℂ → ℝ}
    (h₁ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₁ (x - y) * f y)
        volume)
    (h₂ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₂ (x - y) * f y)
        volume)
    (hg : Integrable g volume)
    (hmajorant : ∀ᵐ y ∂volume,
      ‖(1 / 2 : ℂ) *
          ((beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) *
            (f y - f (quarterTurnAboutHomeomorph x y)))‖ ≤
        g y) :
    dist
        (beurlingTruncatedIntegral ε₁ f x)
        (beurlingTruncatedIntegral ε₂ f x) ≤
      ∫ y, g y ∂volume := by
  have hdiff :
      Integrable
        (fun y =>
          (beurlingTruncatedKernel ε₁ (x - y) -
              beurlingTruncatedKernel ε₂ (x - y)) * f y)
        volume := by
    have hsub := h₁.sub h₂
    convert hsub using 1
    funext y
    simp
    ring
  have hannular :
      Integrable
        (fun y =>
          (beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y)
        volume := by
    apply hdiff.congr
    filter_upwards [] with y
    rw [beurlingTruncatedKernel_sub_eq_annulus_indicator hε]
  rw [dist_eq_norm,
    beurlingTruncatedIntegral_sub_eq_annulus_integral hε h₁ h₂]
  exact
    norm_beurlingAnnularIntegral_le_of_quarterTurn_majorant hannular hg hmajorant

theorem norm_beurlingTruncatedIntegral_sub_le_of_annular_majorant
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {f : ℂ → ℂ} {x : ℂ} {g : ℂ → ℝ}
    (h₁ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₁ (x - y) * f y) volume)
    (h₂ :
      Integrable
        (fun y => beurlingTruncatedKernel ε₂ (x - y) * f y) volume)
    (hg : Integrable g volume)
    (hmajorant :
      ∀ᵐ y ∂volume,
        ‖(beurlingAnnulus ε₁ ε₂).indicator beurlingKernel (x - y) * f y‖ ≤
          g y) :
    dist
        (beurlingTruncatedIntegral ε₁ f x)
        (beurlingTruncatedIntegral ε₂ f x) ≤
      ∫ y, g y ∂volume := by
  rw [dist_eq_norm, beurlingTruncatedIntegral_sub_eq_annulus_integral hε h₁ h₂]
  exact norm_integral_le_of_norm_le hg hmajorant

/-!
The analytic heart of the principal-value problem is now isolated as an
annular Cauchy estimate: the contribution of every outer annulus must become
small uniformly in the second truncation scale.  The next structure records
exactly that input for one function and one evaluation point.
-/

/-- Quantitative annular cancellation data at one input and one point. -/
structure BeurlingAnnularCauchyData (f : ℂ → ℂ) (x : ℂ) where
  modulus : ℕ → ℝ
  modulus_tendsto_zero : Tendsto modulus atTop (𝓝 0)
  dist_le : ∀ m n, m ≤ n →
    dist
        (beurlingTruncatedIntegralSequence f x m)
        (beurlingTruncatedIntegralSequence f x n) ≤
      modulus m

theorem BeurlingAnnularCauchyData.cauchySeq
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingAnnularCauchyData f x) :
    CauchySeq (beurlingTruncatedIntegralSequence f x) := by
  exact cauchySeq_of_le_tendsto_0' D.modulus D.dist_le D.modulus_tendsto_zero

theorem BeurlingAnnularCauchyData.exists_principalValue
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingAnnularCauchyData f x) :
    ∃ L : ℂ,
      Tendsto (beurlingTruncatedIntegralSequence f x) atTop (𝓝 L) := by
  exact cauchySeq_tendsto_of_complete D.cauchySeq

/--
Concrete data from which the abstract annular Cauchy modulus is obtained by
quarter-turn pairing.  The majorant is allowed to depend on the initial
scale, while its integral is required to be bounded by a scalar modulus that
tends to zero.
-/
structure BeurlingQuarterTurnCauchyData (f : ℂ → ℂ) (x : ℂ) where
  modulus : ℕ → ℝ
  modulus_tendsto_zero : Tendsto modulus atTop (𝓝 0)
  majorant : ℕ → ℂ → ℝ
  majorant_integrable : ∀ m : ℕ, Integrable (majorant m) volume
  majorant_integral_le : ∀ m : ℕ, ∫ y, majorant m y ∂volume ≤ modulus m
  truncated_integrable : ∀ n : ℕ,
    Integrable
      (fun y =>
        beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y)
      volume
  oscillation_majorant : ∀ m n : ℕ, m ≤ n → ∀ᵐ y ∂volume,
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
          beurlingKernel (x - y) *
          (f y - f (quarterTurnAboutHomeomorph x y)))‖ ≤
      majorant m y

def SchwartzMap.beurlingLocalOscillationMajorant
    (φ : SchwartzMap ℂ ℂ) (x : ℂ) (m : ℕ) : ℂ → ℝ :=
  fun y =>
    (SchwartzMap.seminorm ℝ 0 1 φ) * (Real.pi : ℝ)⁻¹ *
      beurlingLocalInverseMajorantOnBall x m y

theorem SchwartzMap.norm_beurling_quarterTurn_pairing_le_localOscillationMajorant
    (φ : SchwartzMap ℂ ℂ) (m n : ℕ) (hmn : m ≤ n) (x y : ℂ) :
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
          beurlingKernel (x - y) *
          (φ y - φ (quarterTurnAboutHomeomorph x y)))‖ ≤
      SchwartzMap.beurlingLocalOscillationMajorant φ x m y := by
  by_cases hz : x - y ∈
      beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)
  · have hnormpos : 0 < ‖x - y‖ :=
      lt_of_lt_of_le (by positivity) hz.1
    have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hnormpos
    have hball : y ∈ Metric.ball x ((m + 1 : ℝ)⁻¹) := by
      rw [Metric.mem_ball]
      simpa [dist_eq_norm, norm_sub_rev] using hz.2
    have hbase : (1 : ℝ) ≤ (m + 1 : ℝ) := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hR : (m + 1 : ℝ)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hbase
    have hunit : x - y ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hz.2.trans_le hR
    have hlocal : beurlingLocalInverseMajorant (x - y) = ‖x - y‖⁻¹ := by
      rw [beurlingLocalInverseMajorant, Set.indicator_of_mem hunit,
        Real.rpow_neg_one]
    have hA :
        ‖(beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y)‖ =
          (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 := by
      rw [Set.indicator_of_mem hz, beurlingKernel_norm_eq hxy0]
    unfold SchwartzMap.beurlingLocalOscillationMajorant
    rw [beurlingLocalInverseMajorantOnBall, Set.indicator_of_mem hball,
      hlocal]
    calc
      ‖(1 / 2 : ℂ) *
          ((beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y) *
            (φ y - φ (quarterTurnAboutHomeomorph x y)))‖ =
          (1 / 2 : ℝ) *
            ((Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2) *
            ‖φ y - φ (quarterTurnAboutHomeomorph x y)‖ := by
        rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num,
          hA]
        ring
      _ ≤ (1 / 2 : ℝ) *
            ((Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2) *
            ((2 * SchwartzMap.seminorm ℝ 0 1 φ) * ‖x - y‖) := by
        exact mul_le_mul_of_nonneg_left
          (SchwartzMap.norm_sub_quarterTurn_le φ x y) (by positivity)
      _ = SchwartzMap.seminorm ℝ 0 1 φ * (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ := by
        field_simp [hxy0, ne_of_gt Real.pi_pos]
  · unfold SchwartzMap.beurlingLocalOscillationMajorant
    by_cases hball : y ∈ Metric.ball x ((m + 1 : ℝ)⁻¹)
    · rw [beurlingLocalInverseMajorantOnBall, Set.indicator_of_mem hball]
      simp only [Set.indicator_of_notMem hz, norm_zero, zero_mul]
      have hlocalnonneg : 0 ≤ beurlingLocalInverseMajorant (x - y) := by
        unfold beurlingLocalInverseMajorant
        by_cases hunit : x - y ∈ Metric.ball 0 1
        · rw [Set.indicator_of_mem hunit]
          exact Real.rpow_nonneg (norm_nonneg _) _
        · rw [Set.indicator_of_notMem hunit]
      simp only [mul_zero, norm_zero]
      exact mul_nonneg
        (mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℝ 0 1) φ)
          (inv_nonneg.mpr Real.pi_pos.le))
        hlocalnonneg
    · simp [beurlingLocalInverseMajorantOnBall, hz, hball]

noncomputable def SchwartzMap.beurlingQuarterTurnCauchyData
    (φ : SchwartzMap ℂ ℂ) (x : ℂ) :
    BeurlingQuarterTurnCauchyData (φ : ℂ → ℂ) x := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 1 φ * (Real.pi : ℝ)⁻¹
  refine
    { modulus := fun m => C *
        ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume
      modulus_tendsto_zero := by
        simpa [C] using
          (tendsto_const_nhds.mul
            (tendsto_integral_beurlingLocalInverseMajorantOnBall x))
      majorant := fun m => SchwartzMap.beurlingLocalOscillationMajorant φ x m
      majorant_integrable := by
        intro m
        exact
          (integrable_beurlingLocalInverseMajorantOnBall x m).const_mul C
      majorant_integral_le := by
        intro m
        change
          ∫ y, C * beurlingLocalInverseMajorantOnBall x m y ∂volume ≤
            C * ∫ y, beurlingLocalInverseMajorantOnBall x m y ∂volume
        rw [integral_const_mul]
      truncated_integrable := by
        intro n
        exact SchwartzMap.integrable_beurlingTruncatedIntegrand φ (by positivity) x
      oscillation_majorant := by
        intro m n hmn
        exact Eventually.of_forall (fun y =>
          SchwartzMap.norm_beurling_quarterTurn_pairing_le_localOscillationMajorant
            φ m n hmn x y) }

/-!
The integer family above is only a discrete model for the regularity input
used in the Calderón--Zygmund proof.  The next structure keeps the real
Hölder exponent visible.  The `holder_bound` field is the local analytic
estimate, while `oscillation_majorant` and `majorant_integral_le` record the
separate kernel-integration estimate.  This separation is intentional: the
first is a regularity statement about the input, and the second is the
singular-integral estimate that still has to be proved for a concrete class.
-/

structure BeurlingHolderQuarterTurnWitness (f : ℂ → ℂ) (x : ℂ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  majorant : ℕ → ℂ → ℝ
  majorant_integrable : ∀ m : ℕ, Integrable (majorant m) volume
  majorant_integral_le : ∀ m : ℕ,
    ∫ y, majorant m y ∂volume ≤
      constant * ((m + 1 : ℝ)⁻¹) ^ exponent
  truncated_integrable : ∀ n : ℕ,
    Integrable
      (fun y =>
        beurlingTruncatedKernel ((n + 1 : ℝ)⁻¹) (x - y) * f y)
      volume
  holder_bound : ∀ᵐ y ∂volume,
    ‖f y - f (quarterTurnAboutHomeomorph x y)‖ ≤
      constant * ‖x - y‖ ^ exponent
  kernel_holder_majorant : ∀ m n : ℕ, m ≤ n → ∀ᵐ y ∂volume,
    ‖(1 / 2 : ℂ) *
        (beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
          beurlingKernel (x - y)‖ *
        (constant * ‖x - y‖ ^ exponent) ≤
      majorant m y

theorem tendsto_holderModulus_zero
    {C α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun m : ℕ => C * ((m + 1 : ℝ)⁻¹) ^ α)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun m : ℕ => (m + 1 : ℝ)⁻¹)
      atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul (hinv.rpow_const_nhds_zero hα)).congr'
      (Eventually.of_forall fun _ => by ring)

theorem BeurlingHolderQuarterTurnWitness.oscillation_majorant
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingHolderQuarterTurnWitness f x)
    (m n : ℕ) (hmn : m ≤ n) : ∀ᵐ y ∂volume,
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
          beurlingKernel (x - y) *
          (f y - f (quarterTurnAboutHomeomorph x y)))‖ ≤
      D.majorant m y := by
  filter_upwards [D.holder_bound, D.kernel_holder_majorant m n hmn] with y hy hmajorant
  calc
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
          beurlingKernel (x - y) *
          (f y - f (quarterTurnAboutHomeomorph x y)))‖ =
        ‖(1 / 2 : ℂ) *
          (beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y)‖ *
          ‖f y - f (quarterTurnAboutHomeomorph x y)‖ := by
      simp only [norm_mul]
      ring
    _ ≤ ‖(1 / 2 : ℂ) *
          (beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y)‖ *
          (D.constant * ‖x - y‖ ^ D.exponent) := by
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ ≤ D.majorant m y := hmajorant

noncomputable def BeurlingHolderQuarterTurnWitness.toQuarterTurnCauchyData
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingHolderQuarterTurnWitness f x) :
    BeurlingQuarterTurnCauchyData f x := by
  refine
    { modulus := fun m => D.constant * ((m + 1 : ℝ)⁻¹) ^ D.exponent
      modulus_tendsto_zero :=
        tendsto_holderModulus_zero D.exponent_pos
      majorant := D.majorant
      majorant_integrable := D.majorant_integrable
      majorant_integral_le := by
        intro m
        exact D.majorant_integral_le m
      truncated_integrable := D.truncated_integrable
      oscillation_majorant := D.oscillation_majorant }

/-!
For Schwartz data the abstract Holder interface is now inhabited with the
natural exponent one.  The factor `2` comes from the quarter-turn difference;
the factor `2 * π` in the local inverse-norm integral cancels the kernel's
normalization `π⁻¹` exactly.
-/

noncomputable def SchwartzMap.beurlingHolderQuarterTurnWitness
    (φ : SchwartzMap ℂ ℂ) (x : ℂ) :
    BeurlingHolderQuarterTurnWitness (φ : ℂ → ℂ) x := by
  let S : ℝ := SchwartzMap.seminorm ℝ 0 1 φ
  let C : ℝ := 2 * S
  refine
    { exponent := 1
      exponent_pos := by norm_num
      constant := C
      constant_nonneg := by
        dsimp [C, S]
        positivity
      majorant := fun m => SchwartzMap.beurlingLocalOscillationMajorant φ x m
      majorant_integrable := by
        intro m
        change Integrable (fun y => S * (Real.pi : ℝ)⁻¹ *
          beurlingLocalInverseMajorantOnBall x m y) volume
        exact (integrable_beurlingLocalInverseMajorantOnBall x m).const_mul _
      majorant_integral_le := by
        intro m
        dsimp [SchwartzMap.beurlingLocalOscillationMajorant, C, S]
        rw [integral_const_mul,
          integral_beurlingLocalInverseMajorantOnBall_eq_linear,
          integral_beurlingLocalInverseMajorant_eq_two_mul_pi]
        have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
        rw [Real.rpow_one]
        have hm1 : (1 + (m : ℝ)) ≠ 0 := by positivity
        field_simp [hpi, hm1]
        exact le_rfl
      truncated_integrable := by
        intro n
        exact SchwartzMap.integrable_beurlingTruncatedIntegrand φ (by positivity) x
      holder_bound := by
        filter_upwards [] with y
        simpa [C, S, Real.rpow_one] using SchwartzMap.norm_sub_quarterTurn_le φ x y
      kernel_holder_majorant := by
        intro m n hmn
        filter_upwards [] with y
        by_cases hz : x - y ∈
            beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)
        · have hnormpos : 0 < ‖x - y‖ :=
            lt_of_lt_of_le (by positivity) hz.1
          have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hnormpos
          have hball : y ∈ Metric.ball x ((m + 1 : ℝ)⁻¹) := by
            rw [Metric.mem_ball]
            simpa [dist_eq_norm, norm_sub_rev] using hz.2
          have hunit : x - y ∈ Metric.ball 0 1 := by
            rw [Metric.mem_ball, dist_zero_right]
            have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
            have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
            exact hz.2.trans_le (inv_le_one_of_one_le₀ hbase)
          have hlocal : beurlingLocalInverseMajorant (x - y) = ‖x - y‖⁻¹ := by
            rw [beurlingLocalInverseMajorant, Set.indicator_of_mem hunit,
              Real.rpow_neg_one]
          unfold SchwartzMap.beurlingLocalOscillationMajorant
          rw [beurlingLocalInverseMajorantOnBall, Set.indicator_of_mem hball,
            hlocal, Set.indicator_of_mem hz, norm_mul,
            show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num,
            beurlingKernel_norm_eq hxy0]
          dsimp [C, S]
          have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
          rw [Real.rpow_one]
          field_simp [hpi, hxy0]
          exact le_rfl
        · unfold SchwartzMap.beurlingLocalOscillationMajorant
          rw [Set.indicator_of_notMem hz]
          have hnonneg :
              0 ≤ SchwartzMap.seminorm ℝ 0 1 φ * (Real.pi : ℝ)⁻¹ := by
            positivity
          have hlocalnonneg : 0 ≤ beurlingLocalInverseMajorantOnBall x m y := by
            unfold beurlingLocalInverseMajorantOnBall
            by_cases hball : y ∈ Metric.ball x ((m + 1 : ℝ)⁻¹)
            · rw [Set.indicator_of_mem hball]
              unfold beurlingLocalInverseMajorant
              by_cases hunit : x - y ∈ Metric.ball 0 1
              · rw [Set.indicator_of_mem hunit]
                positivity
              · rw [Set.indicator_of_notMem hunit]
            · rw [Set.indicator_of_notMem hball]
          have hmajor : 0 ≤ SchwartzMap.beurlingLocalOscillationMajorant φ x m y :=
            mul_nonneg hnonneg hlocalnonneg
          calc
            ‖(1 / 2 : ℂ) * 0‖ *
                (C * ‖x - y‖ ^ (1 : ℝ)) = 0 := by
                  simp
            _ ≤ SchwartzMap.beurlingLocalOscillationMajorant φ x m y := hmajor }

/--
Quarter-turn Cauchy data is stable under addition.  This is the first
function-space closure principle beyond the individual disk examples: local
oscillation majorants add, and so do their scalar moduli.
-/
noncomputable def BeurlingQuarterTurnCauchyData.add
    {f g : ℂ → ℂ} {x : ℂ}
    (Df : BeurlingQuarterTurnCauchyData f x)
    (Dg : BeurlingQuarterTurnCauchyData g x) :
    BeurlingQuarterTurnCauchyData (fun y => f y + g y) x := by
  refine
    { modulus := fun m => Df.modulus m + Dg.modulus m
      modulus_tendsto_zero := by
        simpa only [add_zero] using
          Df.modulus_tendsto_zero.add Dg.modulus_tendsto_zero
      majorant := fun m y => Df.majorant m y + Dg.majorant m y
      majorant_integrable := by
        intro m
        exact (Df.majorant_integrable m).add (Dg.majorant_integrable m)
      majorant_integral_le := by
        intro m
        calc
          ∫ y, Df.majorant m y + Dg.majorant m y ∂volume =
              (∫ y, Df.majorant m y ∂volume) +
                ∫ y, Dg.majorant m y ∂volume := by
            exact integral_add (Df.majorant_integrable m) (Dg.majorant_integrable m)
          _ ≤ Df.modulus m + Dg.modulus m :=
            add_le_add (Df.majorant_integral_le m) (Dg.majorant_integral_le m)
      truncated_integrable := by
        intro n
        have hsum :=
          (Df.truncated_integrable n).add (Dg.truncated_integrable n)
        convert hsum using 1
        funext y
        simp only [Pi.add_apply, mul_add]
      oscillation_majorant := by
        intro m n hmn
        filter_upwards [Df.oscillation_majorant m n hmn,
          Dg.oscillation_majorant m n hmn] with y hyf hyg
        let K : ℂ :=
          (beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y)
        have hnorm :
            ‖(1 / 2 : ℂ) * (K *
                ((f y + g y) -
                  (f (quarterTurnAboutHomeomorph x y) +
                    g (quarterTurnAboutHomeomorph x y))))‖ ≤
              Df.majorant m y + Dg.majorant m y := by
          calc
            ‖(1 / 2 : ℂ) * (K *
                ((f y + g y) -
                  (f (quarterTurnAboutHomeomorph x y) +
                    g (quarterTurnAboutHomeomorph x y))))‖ =
                ‖(1 / 2 : ℂ) * (K *
                    (f y - f (quarterTurnAboutHomeomorph x y))) +
                  (1 / 2 : ℂ) * (K *
                    (g y - g (quarterTurnAboutHomeomorph x y)))‖ := by
              congr 1
              ring
            _ ≤ ‖(1 / 2 : ℂ) * (K *
                    (f y - f (quarterTurnAboutHomeomorph x y)))‖ +
                  ‖(1 / 2 : ℂ) * (K *
                    (g y - g (quarterTurnAboutHomeomorph x y)))‖ :=
              norm_add_le _ _
            _ ≤ Df.majorant m y + Dg.majorant m y :=
              add_le_add (by simpa [K] using hyf) (by simpa [K] using hyg)
        simpa [K] using hnorm }

noncomputable def BeurlingQuarterTurnCauchyData.toAnnularCauchyData
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingQuarterTurnCauchyData f x) :
    BeurlingAnnularCauchyData f x := by
  refine
    { modulus := D.modulus
      modulus_tendsto_zero := D.modulus_tendsto_zero
      dist_le := ?_ }
  intro m n hmn
  have hscale :
      (n + 1 : ℝ)⁻¹ ≤ (m + 1 : ℝ)⁻¹ := by
    have hmn' : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < (m + 1 : ℝ)) hmn'
  calc
    dist
        (beurlingTruncatedIntegralSequence f x m)
        (beurlingTruncatedIntegralSequence f x n) =
        dist
          (beurlingTruncatedIntegralSequence f x n)
          (beurlingTruncatedIntegralSequence f x m) :=
      dist_comm _ _
    _ ≤ ∫ y, D.majorant m y ∂volume := by
      simpa only [beurlingTruncatedIntegralSequence] using
        (dist_beurlingTruncatedIntegral_sub_le_of_quarterTurn_majorant
          (ε₁ := (n + 1 : ℝ)⁻¹) (ε₂ := (m + 1 : ℝ)⁻¹) hscale
          (D.truncated_integrable n) (D.truncated_integrable m)
          (D.majorant_integrable m) (D.oscillation_majorant m n hmn))
    _ ≤ D.modulus m := D.majorant_integral_le m

theorem SchwartzMap.principalValue_exists
    (φ : SchwartzMap ℂ ℂ) (x : ℂ) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence (φ : ℂ → ℂ) x)
        atTop (𝓝 L) := by
  exact
    (SchwartzMap.beurlingQuarterTurnCauchyData φ x).toAnnularCauchyData
      |> BeurlingAnnularCauchyData.exists_principalValue

theorem BeurlingHolderQuarterTurnWitness.principalValue_exists
    {f : ℂ → ℂ} {x : ℂ}
    (D : BeurlingHolderQuarterTurnWitness f x) :
    ∃ L : ℂ,
      Tendsto (beurlingTruncatedIntegralSequence f x) atTop (𝓝 L) := by
  exact
    (D.toQuarterTurnCauchyData.toAnnularCauchyData).exists_principalValue

theorem SchwartzMap.principalValue_exists_via_holder
    (φ : SchwartzMap ℂ ℂ) (x : ℂ) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence (φ : ℂ → ℂ) x)
        atTop (𝓝 L) := by
  exact
    (SchwartzMap.beurlingHolderQuarterTurnWitness φ x).principalValue_exists

/--
The indicator of a finite closed disk centered at `x` is a concrete
nonzero example.  Its exact quarter-turn invariance gives the zero modulus,
while finite measure of the disk supplies integrability of all truncations.
-/
noncomputable def beurlingClosedBallIndicator_quarterTurnCauchyData
    (x : ℂ) (R : ℝ) :
    BeurlingQuarterTurnCauchyData (beurlingClosedBallIndicator x R) x := by
  refine
    { modulus := fun _ => 0
      modulus_tendsto_zero := tendsto_const_nhds
      majorant := fun _ _ => 0
      majorant_integrable := by
        intro m
        exact integrable_zero ℂ ℝ volume
      majorant_integral_le := by
        intro m
        simp
      truncated_integrable := by
        intro n
        apply integrable_beurlingTruncatedIntegrand
        · positivity
        · exact integrable_beurlingClosedBallIndicator x R
      oscillation_majorant := by
        intro m n hmn
        filter_upwards [] with y
        rw [beurlingClosedBallIndicator_quarterTurn_invariant]
        simp }

theorem beurlingClosedBallIndicator_principalValue_exists
    (x : ℂ) (R : ℝ) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence
          (beurlingClosedBallIndicator x R) x)
        atTop (𝓝 L) := by
  exact
    (BeurlingQuarterTurnCauchyData.toAnnularCauchyData
      (beurlingClosedBallIndicator_quarterTurnCauchyData x R)).exists_principalValue

noncomputable def beurlingQuadraticClosedBall_quarterTurnCauchyData
    (x : ℂ) (R : ℝ) :
    BeurlingQuarterTurnCauchyData (beurlingQuadraticClosedBall x R) x := by
  refine
    { modulus := fun m =>
        ∫ y, beurlingQuadraticClosedBallMajorant x m y ∂volume
      modulus_tendsto_zero :=
        tendsto_integral_beurlingQuadraticClosedBallMajorant x
      majorant := beurlingQuadraticClosedBallMajorant x
      majorant_integrable := by
        intro m
        exact integrable_beurlingQuadraticClosedBallMajorant x m
      majorant_integral_le := by
        intro m
        exact le_rfl
      truncated_integrable := by
        intro n
        apply integrable_beurlingTruncatedIntegrand
        · positivity
        · exact integrable_beurlingQuadraticClosedBall x R
      oscillation_majorant := by
        intro m n hmn
        filter_upwards [] with y
        exact
          norm_beurlingQuadraticClosedBall_pairing_le
            (by positivity : 0 < (n + 1 : ℝ)⁻¹) m x R y }

theorem beurlingQuadraticClosedBall_principalValue_exists
    (x : ℂ) (R : ℝ) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence
          (beurlingQuadraticClosedBall x R) x)
        atTop (𝓝 L) := by
  exact
    (BeurlingQuarterTurnCauchyData.toAnnularCauchyData
    (beurlingQuadraticClosedBall_quarterTurnCauchyData x R)).exists_principalValue

/--
The integer vanishing-order family.  The parameter j adds j powers of
vanishing to the quadratic model, so the Beurling singularity leaves a
remainder of order j after pairing.
-/
def beurlingVanishingClosedBall (j : ℕ) (x : ℂ) (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall x R).indicator (fun y => (y - x) ^ (j + 2))

theorem beurlingVanishingClosedBall_zero_eq_quadratic
    (x : ℂ) (R : ℝ) :
    beurlingVanishingClosedBall 0 x R =
      beurlingQuadraticClosedBall x R := by
  funext y
  simp [beurlingVanishingClosedBall, beurlingQuadraticClosedBall]

theorem integrable_beurlingVanishingClosedBall
    (j : ℕ) (x : ℂ) (R : ℝ) :
    Integrable (beurlingVanishingClosedBall j x R) volume := by
  have hball : IsCompact (Metric.closedBall x R) := isCompact_closedBall x R
  have hconst :
      IntegrableOn (fun _ : ℂ => (1 : ℂ)) (Metric.closedBall x R) volume := by
    exact integrableOn_const (measure_closedBall_lt_top.ne)
  have hpoly : ContinuousOn (fun y : ℂ => (y - x) ^ (j + 2))
      (Metric.closedBall x R) := by
    fun_prop
  have hprod :
      IntegrableOn
        (fun y : ℂ => (1 : ℂ) * (y - x) ^ (j + 2))
        (Metric.closedBall x R) volume :=
    hconst.mul_continuousOn hpoly hball
  simpa only [one_mul, beurlingVanishingClosedBall] using
    hprod.integrable_indicator measurableSet_closedBall

def beurlingVanishingClosedBallMajorant
    (j : ℕ) (x : ℂ) (m : ℕ) : ℂ → ℝ :=
  (Metric.closedBall x ((m + 1 : ℝ)⁻¹)).indicator
    (fun _ => (Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j)

theorem integrable_beurlingVanishingClosedBallMajorant
    (j : ℕ) (x : ℂ) (m : ℕ) :
    Integrable (beurlingVanishingClosedBallMajorant j x m) volume := by
  unfold beurlingVanishingClosedBallMajorant
  exact
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
      measurableSet_closedBall

theorem integral_beurlingVanishingClosedBallMajorant
    (j : ℕ) (x : ℂ) (m : ℕ) :
    ∫ y, beurlingVanishingClosedBallMajorant j x m y ∂volume =
      ((m + 1 : ℝ)⁻¹) ^ (j + 2) := by
  have hRm : 0 ≤ (m + 1 : ℝ)⁻¹ := by positivity
  unfold beurlingVanishingClosedBallMajorant
  rw [integral_indicator_const _ measurableSet_closedBall]
  simp [Complex.volume_closedBall, Measure.real, smul_eq_mul, hRm,
    ENNReal.toReal_ofReal, Real.pi_pos.le]
  field_simp
  rw [pow_add]
  ring

theorem tendsto_integral_beurlingVanishingClosedBallMajorant
    (j : ℕ) (x : ℂ) :
    Tendsto
      (fun m : ℕ => ∫ y, beurlingVanishingClosedBallMajorant j x m y ∂volume)
      atTop (𝓝 0) := by
  rw [show (fun m : ℕ =>
      ∫ y, beurlingVanishingClosedBallMajorant j x m y ∂volume) =
      (fun m : ℕ => ((m + 1 : ℝ)⁻¹) ^ (j + 2)) by
    funext m
    exact integral_beurlingVanishingClosedBallMajorant j x m]
  have hinv : Tendsto (fun m : ℕ => (m + 1 : ℝ)⁻¹)
      atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa using hinv.pow (j + 2)

theorem norm_beurlingVanishingClosedBall_pairing_le
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) (j : ℕ) (m : ℕ)
    (x : ℂ) (R : ℝ) (y : ℂ) :
    ‖(1 / 2 : ℂ) *
        ((beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y) *
          (beurlingVanishingClosedBall j x R y -
            beurlingVanishingClosedBall j x R
              (quarterTurnAboutHomeomorph x y)))‖ ≤
      beurlingVanishingClosedBallMajorant j x m y := by
  by_cases hz : x - y ∈ beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)
  · have hnormpos : 0 < ‖x - y‖ := lt_of_lt_of_le hε₁ hz.1
    have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hnormpos
    have hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹) := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm, norm_sub_rev] using hz.2.le
    have hK :
        ‖(beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator
            beurlingKernel (x - y)‖ =
          (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 := by
      rw [Set.indicator_of_mem hz, beurlingKernel_norm_eq hxy0]
    have hfy :
        ‖beurlingVanishingClosedBall j x R y‖ ≤ ‖x - y‖ ^ (j + 2) := by
      by_cases hyR : y ∈ Metric.closedBall x R
      · simp [beurlingVanishingClosedBall, hyR, norm_pow, norm_sub_rev]
      · simp [beurlingVanishingClosedBall, hyR]
    have hq :
        ‖beurlingVanishingClosedBall j x R
            (quarterTurnAboutHomeomorph x y)‖ ≤ ‖x - y‖ ^ (j + 2) := by
      by_cases hqR :
          quarterTurnAboutHomeomorph x y ∈ Metric.closedBall x R
      · simp only [beurlingVanishingClosedBall, Set.indicator_of_mem hqR,
          norm_pow]
        rw [quarterTurnAboutHomeomorph_apply]
        simp [dist_eq_norm, norm_sub_rev, norm_mul]
      · simp [beurlingVanishingClosedBall, hqR]
    have hpow :
        ‖x - y‖ ^ (j + 2) =
          ‖x - y‖ ^ j * ‖x - y‖ ^ 2 := by
      rw [pow_add]
    have hcancel :
        ‖x - y‖⁻¹ ^ 2 *
            (‖x - y‖ ^ j * ‖x - y‖ ^ 2) = ‖x - y‖ ^ j := by
      field_simp [hxy0]
    have hpow_le :
        ‖x - y‖ ^ j ≤ ((m + 1 : ℝ)⁻¹) ^ j := by
      exact pow_le_pow_left₀ (by positivity) hz.2.le j
    unfold beurlingVanishingClosedBallMajorant
    rw [Set.indicator_of_mem hball]
    calc
      ‖(1 / 2 : ℂ) *
          ((beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel (x - y) *
            (beurlingVanishingClosedBall j x R y -
              beurlingVanishingClosedBall j x R
                (quarterTurnAboutHomeomorph x y)))‖ ≤
          (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 *
            (‖beurlingVanishingClosedBall j x R y‖ +
              ‖beurlingVanishingClosedBall j x R
                (quarterTurnAboutHomeomorph x y)‖) / 2 := by
        calc
          ‖(1 / 2 : ℂ) *
              ((beurlingAnnulus ε₁ ((m + 1 : ℝ)⁻¹)).indicator beurlingKernel
                (x - y) *
                (beurlingVanishingClosedBall j x R y -
                  beurlingVanishingClosedBall j x R
                    (quarterTurnAboutHomeomorph x y)))‖ =
              (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 *
                ‖beurlingVanishingClosedBall j x R y -
                  beurlingVanishingClosedBall j x R
                    (quarterTurnAboutHomeomorph x y)‖ / 2 := by
            rw [norm_mul, norm_mul, hK]
            norm_num
            ring
          _ ≤ (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 *
              (‖beurlingVanishingClosedBall j x R y‖ +
                ‖beurlingVanishingClosedBall j x R
                  (quarterTurnAboutHomeomorph x y)‖) / 2 := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left
                (norm_sub_le _ _) (by positivity)
            · norm_num
      _ ≤ (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 *
            (‖x - y‖ ^ (j + 2) + ‖x - y‖ ^ (j + 2)) / 2 := by
        gcongr
      _ = (Real.pi : ℝ)⁻¹ * ‖x - y‖ ^ j := by
        rw [hpow]
        calc
          (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 *
              (‖x - y‖ ^ j * ‖x - y‖ ^ 2 +
                ‖x - y‖ ^ j * ‖x - y‖ ^ 2) / 2 =
              (Real.pi : ℝ)⁻¹ *
                (‖x - y‖⁻¹ ^ 2 *
                  (‖x - y‖ ^ j * ‖x - y‖ ^ 2)) := by ring
          _ = (Real.pi : ℝ)⁻¹ * ‖x - y‖ ^ j := by rw [hcancel]
      _ ≤ (Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j := by
        exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  · unfold beurlingVanishingClosedBallMajorant
    by_cases hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹)
    · have hnonneg :
          0 ≤ (Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j := by
        positivity
      simpa [Set.indicator_of_notMem hz, Set.indicator_of_mem hball] using hnonneg
    · simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hball]

noncomputable def beurlingVanishingClosedBall_quarterTurnCauchyData
    (j : ℕ) (x : ℂ) (R : ℝ) :
    BeurlingQuarterTurnCauchyData (beurlingVanishingClosedBall j x R) x := by
  refine
    { modulus := fun m =>
        ∫ y, beurlingVanishingClosedBallMajorant j x m y ∂volume
      modulus_tendsto_zero :=
        tendsto_integral_beurlingVanishingClosedBallMajorant j x
      majorant := beurlingVanishingClosedBallMajorant j x
      majorant_integrable := by
        intro m
        exact integrable_beurlingVanishingClosedBallMajorant j x m
      majorant_integral_le := by
        intro m
        exact le_rfl
      truncated_integrable := by
        intro n
        apply integrable_beurlingTruncatedIntegrand
        · positivity
        · exact integrable_beurlingVanishingClosedBall j x R
      oscillation_majorant := by
        intro m n hmn
        filter_upwards [] with y
        exact
          norm_beurlingVanishingClosedBall_pairing_le
            (by positivity : 0 < (n + 1 : ℝ)⁻¹) j m x R y }

theorem beurlingVanishingClosedBall_principalValue_exists
    (j : ℕ) (x : ℂ) (R : ℝ) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence
          (beurlingVanishingClosedBall j x R) x)
        atTop (𝓝 L) := by
  exact
    (BeurlingQuarterTurnCauchyData.toAnnularCauchyData
      (beurlingVanishingClosedBall_quarterTurnCauchyData j x R)).exists_principalValue

/-!
The discrete vanishing family now enters the real Holder interface.  The
sharp disk cutoff is not globally Holder with respect to arbitrary pairs of
points, but it is Holder along the quarter-turn orbit used by the pairing:
the cutoff is invariant and the polynomial difference has size at most twice
the vanishing power.  This is exactly the directional regularity needed by
the principal-value argument.
-/
noncomputable def beurlingVanishingClosedBall_holderWitness
    (j : ℕ) (x : ℂ) (R : ℝ) :
    BeurlingHolderQuarterTurnWitness
      (beurlingVanishingClosedBall j x R) x := by
  refine
    { exponent := (j + 2 : ℝ)
      exponent_pos := by positivity
      constant := 2
      constant_nonneg := by norm_num
      majorant := fun m y =>
        2 * beurlingVanishingClosedBallMajorant j x m y
      majorant_integrable := by
        intro m
        exact (integrable_beurlingVanishingClosedBallMajorant j x m).const_mul 2
      majorant_integral_le := by
        intro m
        change (∫ y, 2 * beurlingVanishingClosedBallMajorant j x m y ∂volume) ≤ _
        rw [integral_const_mul, integral_beurlingVanishingClosedBallMajorant]
        have hpow : ((m + 1 : ℝ)⁻¹) ^ (j + 2) =
            ((m + 1 : ℝ)⁻¹) ^ (j + 2 : ℝ) := by
          rw [show (j + 2 : ℝ) = ((j + 2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [hpow]
      truncated_integrable := by
        intro n
        apply integrable_beurlingTruncatedIntegrand
        · positivity
        · exact integrable_beurlingVanishingClosedBall j x R
      holder_bound := by
        filter_upwards [] with y
        by_cases hy : y ∈ Metric.closedBall x R
        · have hqy : quarterTurnAboutHomeomorph x y ∈ Metric.closedBall x R :=
            (quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).2 hy
          simp only [beurlingVanishingClosedBall,
            Set.indicator_of_mem hy, Set.indicator_of_mem hqy]
          rw [quarterTurnAboutHomeomorph_apply]
          calc
            ‖(y - x) ^ (j + 2) -
                ((x + Complex.I * (y - x)) - x) ^ (j + 2)‖ ≤
                ‖(y - x) ^ (j + 2)‖ +
                  ‖((x + Complex.I * (y - x)) - x) ^ (j + 2)‖ :=
              norm_sub_le _ _
            _ = 2 * ‖x - y‖ ^ (j + 2 : ℝ) := by
              rw [show x + Complex.I * (y - x) - x = Complex.I * (y - x) by ring]
              have hexp : (↑j + 2 : ℝ) = ((j + 2 : ℕ) : ℝ) := by
                norm_num
              rw [hexp, Real.rpow_natCast]
              simp [norm_pow, norm_sub_rev]
              ring
        · have hqy : quarterTurnAboutHomeomorph x y ∉ Metric.closedBall x R := by
            intro h
            exact hy ((quarterTurnAboutHomeomorph_mem_closedBall_iff x y R).1 h)
          simp [beurlingVanishingClosedBall, hy, hqy]
          exact Real.rpow_nonneg (norm_nonneg _) _
      kernel_holder_majorant := by
        intro m n hmn
        filter_upwards [] with y
        by_cases hz : x - y ∈ beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)
        · have hnormpos : 0 < ‖x - y‖ := lt_of_lt_of_le (by positivity) hz.1
          have hxy0 : x - y ≠ 0 := norm_pos_iff.mp hnormpos
          have hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹) := by
            rw [Metric.mem_closedBall]
            simpa [dist_eq_norm, norm_sub_rev] using hz.2.le
          rw [Set.indicator_of_mem hz]
          simp only [beurlingVanishingClosedBallMajorant,
            Set.indicator_of_mem hball]
          have hkernel :
              ‖(1 / 2 : ℂ) * beurlingKernel (x - y)‖ =
                (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 / 2 := by
            rw [norm_mul,
              show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num,
              beurlingKernel_norm_eq hxy0]
            ring
          have hpow_le :
              ‖x - y‖ ^ j ≤ ((m + 1 : ℝ)⁻¹) ^ j := by
            exact pow_le_pow_left₀ (by positivity) hz.2.le j
          have hpow_exp : ‖x - y‖ ^ (j + 2 : ℝ) =
              ‖x - y‖ ^ (j + 2) := by
            rw [show (j + 2 : ℝ) = ((j + 2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
          have hcancel :
              ‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ (j + 2) =
                ‖x - y‖ ^ j := by
            rw [pow_add]
            field_simp [hxy0]
          calc
            ‖(1 / 2 : ℂ) * beurlingKernel (x - y)‖ *
                (2 * ‖x - y‖ ^ (j + 2 : ℝ)) =
                (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 / 2 *
                  (2 * ‖x - y‖ ^ (j + 2)) := by
              rw [hkernel, hpow_exp]
            _ = (Real.pi : ℝ)⁻¹ * ‖x - y‖ ^ j := by
              calc
                (Real.pi : ℝ)⁻¹ * ‖x - y‖⁻¹ ^ 2 / 2 *
                    (2 * ‖x - y‖ ^ (j + 2)) =
                    (Real.pi : ℝ)⁻¹ *
                      (‖x - y‖⁻¹ ^ 2 * ‖x - y‖ ^ (j + 2)) := by ring
                _ = (Real.pi : ℝ)⁻¹ * ‖x - y‖ ^ j := by rw [hcancel]
            _ ≤ (Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j := by
              exact mul_le_mul_of_nonneg_left hpow_le
                (by positivity)
            _ ≤ 2 * ((Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j) := by
              have hnonneg :
                  0 ≤ (Real.pi : ℝ)⁻¹ * ((m + 1 : ℝ)⁻¹) ^ j := by
                positivity
              nlinarith
        · have hindicator :
              (beurlingAnnulus ((n + 1 : ℝ)⁻¹) ((m + 1 : ℝ)⁻¹)).indicator
                  beurlingKernel (x - y) = 0 :=
            Set.indicator_of_notMem hz beurlingKernel
          rw [hindicator]
          have hmajorant :
              0 ≤ 2 * beurlingVanishingClosedBallMajorant j x m y := by
            unfold beurlingVanishingClosedBallMajorant
            by_cases hball : y ∈ Metric.closedBall x ((m + 1 : ℝ)⁻¹)
            · rw [Set.indicator_of_mem hball]
              positivity
            · rw [Set.indicator_of_notMem hball]
              norm_num
          simpa only [norm_zero, mul_zero, zero_mul] using hmajorant }

theorem beurlingVanishingClosedBall_zero_principalValue_tendsto
    {x : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingVanishingClosedBall 0 x R) x)
      atTop (𝓝 (-((R : ℂ) ^ 2))) := by
  simpa only [beurlingVanishingClosedBall_zero_eq_quadratic] using
    (beurlingQuadraticClosedBall_principalValue_tendsto (x := x) hR)

/-- A finite two-term sum in the first non-invariant concrete class. -/
def beurlingQuadraticClosedBallAdd (x : ℂ) (R S : ℝ) : ℂ → ℂ :=
  fun y => beurlingQuadraticClosedBall x R y +
    beurlingQuadraticClosedBall x S y

noncomputable def beurlingQuadraticClosedBallAdd_quarterTurnCauchyData
    (x : ℂ) (R S : ℝ) :
    BeurlingQuarterTurnCauchyData
      (beurlingQuadraticClosedBallAdd x R S) x := by
  exact
    (beurlingQuadraticClosedBall_quarterTurnCauchyData x R).add
      (beurlingQuadraticClosedBall_quarterTurnCauchyData x S)

theorem beurlingQuadraticClosedBallAdd_principalValue_tendsto
    {x : ℂ} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingQuadraticClosedBallAdd x R S) x)
      atTop
      (𝓝 (-((R : ℂ) ^ 2) + -((S : ℂ) ^ 2))) := by
  have hsum : ∀ n : ℕ,
      beurlingTruncatedIntegralSequence
          (beurlingQuadraticClosedBallAdd x R S) x n =
        beurlingTruncatedIntegralSequence
            (beurlingQuadraticClosedBall x R) x n +
          beurlingTruncatedIntegralSequence
            (beurlingQuadraticClosedBall x S) x n := by
    intro n
    exact beurlingTruncatedIntegral_add
      ((beurlingQuadraticClosedBall_quarterTurnCauchyData x R).truncated_integrable n)
      ((beurlingQuadraticClosedBall_quarterTurnCauchyData x S).truncated_integrable n)
  have hRlim :=
    beurlingQuadraticClosedBall_principalValue_tendsto (x := x) hR
  have hSlim :=
    beurlingQuadraticClosedBall_principalValue_tendsto (x := x) hS
  rw [show beurlingTruncatedIntegralSequence
        (beurlingQuadraticClosedBallAdd x R S) x =
      fun n => beurlingTruncatedIntegralSequence
          (beurlingQuadraticClosedBall x R) x n +
        beurlingTruncatedIntegralSequence
          (beurlingQuadraticClosedBall x S) x n by
    funext n
    exact hsum n]
  simpa only using hRlim.add hSlim

/-!
The same exact-cancellation mechanism applies to the finite simple class.  A
zero majorant is enough because every term is invariant under the centered
quarter-turn, even though the coefficients and radii vary across the finite
sum.
-/

noncomputable def beurlingClosedBallSimple_quarterTurnCauchyData
    (x : ℂ) (s : Finset (ℂ × ℝ)) :
    BeurlingQuarterTurnCauchyData (beurlingClosedBallSimple x s) x := by
  refine
    { modulus := fun _ => 0
      modulus_tendsto_zero := tendsto_const_nhds
      majorant := fun _ _ => 0
      majorant_integrable := by
        intro m
        exact integrable_zero ℂ ℝ volume
      majorant_integral_le := by
        intro m
        simp
      truncated_integrable := by
        intro n
        apply integrable_beurlingTruncatedIntegrand
        · positivity
        · exact integrable_beurlingClosedBallSimple x s
      oscillation_majorant := by
        intro m n hmn
        filter_upwards [] with y
        rw [beurlingClosedBallSimple_quarterTurn_invariant]
        simp }

theorem beurlingClosedBallSimple_truncatedIntegral_eq_zero
    (x : ℂ) (s : Finset (ℂ × ℝ)) {ε : ℝ} (hε : 0 < ε) :
    beurlingTruncatedIntegral ε (beurlingClosedBallSimple x s) x = 0 := by
  apply beurlingTruncatedIntegral_eq_zero_of_quarterTurnInvariant
  · exact
      integrable_beurlingTruncatedIntegrand hε
        (integrable_beurlingClosedBallSimple x s)
  · filter_upwards [] with y
    exact beurlingClosedBallSimple_quarterTurn_invariant x s y

theorem beurlingClosedBallSimple_principalValue_tendsto_zero
    (x : ℂ) (s : Finset (ℂ × ℝ)) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingClosedBallSimple x s) x)
      atTop (𝓝 0) := by
  have hzero : ∀ n : ℕ,
      beurlingTruncatedIntegralSequence
        (beurlingClosedBallSimple x s) x n = 0 := by
    intro n
    unfold beurlingTruncatedIntegralSequence
    exact
      beurlingClosedBallSimple_truncatedIntegral_eq_zero x s
        (by positivity)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [] with n
  exact (hzero n).symm

theorem beurlingClosedBallSimple_principalValue_exists
    (x : ℂ) (s : Finset (ℂ × ℝ)) :
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence
          (beurlingClosedBallSimple x s) x)
        atTop (𝓝 L) := by
  exact
    (BeurlingQuarterTurnCauchyData.toAnnularCauchyData
      (beurlingClosedBallSimple_quarterTurnCauchyData x s)).exists_principalValue

theorem beurlingClosedBallIndicator_principalValue_away_from_center
    {x z : ℂ} {R δ : ℝ} (hδ : 0 < δ)
    (hseparated : R + δ ≤ ‖x - z‖) :
    Tendsto
      (beurlingTruncatedIntegralSequence
        (beurlingClosedBallIndicator z R) x)
      atTop
      (𝓝 (∫ y,
        beurlingKernel (x - y) * beurlingClosedBallIndicator z R y
        ∂volume)) := by
  apply beurlingTruncatedIntegralSequence_tendsto_of_away_from_singularity
    hδ (integrable_beurlingClosedBallIndicator z R)
  filter_upwards [] with y
  by_cases hy : y ∈ Metric.closedBall z R
  · right
    have hyz : ‖y - z‖ ≤ R := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hy)
    have htriangle : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
      simpa [dist_eq_norm] using (dist_triangle x y z)
    linarith
  · left
    simp [beurlingClosedBallIndicator, hy]

/-- An actual bounded Lp operator supplied by an analytic theorem. -/
structure BeurlingLpOperatorWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] where
  operator :
    Lp (α := ℂ) ℂ p (volume : Measure ℂ) →L[ℂ]
      Lp (α := ℂ) ℂ p (volume : Measure ℂ)
  norm_bound : ℝ≥0
  norm_le : ‖operator‖ ≤ norm_bound

namespace BeurlingLpOperatorWitness

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Insert a supplied bounded Beurling operator into the coefficient equation. -/
noncomputable def neumannProblem
    (W : BeurlingLpOperatorWitness p)
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ p (volume : Measure ℂ))
    (hcontract : (c.bound : ℝ) * (W.norm_bound : ℝ) < 1) :
    LpNeumannBeltramiProblem (volume : Measure ℂ) p where
  coefficient := c
  singularOperator := W.operator
  forcing := g
  coefficient_operator_norm_lt_one := by
    calc
      (c.bound : ℝ) * ‖W.operator‖ ≤
          (c.bound : ℝ) * (W.norm_bound : ℝ) := by
        exact mul_le_mul_of_nonneg_left W.norm_le c.bound.coe_nonneg
      _ < 1 := hcontract

theorem neumannProblem_kernel_norm_lt_one
    (W : BeurlingLpOperatorWitness p)
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ p (volume : Measure ℂ))
    (hcontract : (c.bound : ℝ) * (W.norm_bound : ℝ) < 1) :
    ‖(W.neumannProblem c g hcontract).kernel‖ < 1 :=
  (W.neumannProblem c g hcontract).kernel_norm_lt_one

theorem neumannProblem_exists_solution
    (W : BeurlingLpOperatorWitness p)
    (c : BoundedScalarCoefficient ℂ (volume : Measure ℂ))
    (g : Lp (α := ℂ) ℂ p (volume : Measure ℂ))
    (hcontract : (c.bound : ℝ) * (W.norm_bound : ℝ) < 1) :
    ∃ u : Lp (α := ℂ) ℂ p (volume : Measure ℂ),
      u = g + (W.neumannProblem c g hcontract).kernel u :=
  (W.neumannProblem c g hcontract).exists_solution

end BeurlingLpOperatorWitness

/-!
The most economical analytic input for identifying the principal-value
operator is often a uniform tail estimate.  The structure below records such
an estimate separately: once an operator and a modulus `ω` are supplied, the
principal-value convergence itself is a short metric argument.  This keeps
the genuinely Calderón--Zygmund part (proving the estimate) visible.
-/

structure BeurlingUniformPrincipalValueTailWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingLpOperatorWitness p where
  modulus : ℕ → ℝ
  modulus_nonneg : ∀ n, 0 ≤ modulus n
  modulus_tendsto_zero : Tendsto modulus atTop (𝓝 0)
  tail_bound :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ), ∀ n : ℕ,
      dist
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x n)
          (toBeurlingLpOperatorWitness.operator f x) ≤
        modulus n * ‖f‖

namespace BeurlingUniformPrincipalValueTailWitness

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem principalValue_ae
    (W : BeurlingUniformPrincipalValueTailWitness p)
    (f : Lp (α := ℂ) ℂ p (volume : Measure ℂ)) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      Tendsto
        (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
        atTop
        (𝓝 (W.toBeurlingLpOperatorWitness.operator f x)) := by
  have hmodulus :
      Tendsto (fun n : ℕ => W.modulus n * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      W.modulus_tendsto_zero.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => ‖f‖) atTop (𝓝 ‖f‖))
  filter_upwards [W.tail_bound f] with x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases eventually_atTop.1 (hmodulus.eventually (gt_mem_nhds hε)) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  exact (hx n).trans_lt (hN n hn)

end BeurlingUniformPrincipalValueTailWitness

/--
An analytic annular-cancellation input for the principal-value problem.

This witness deliberately separates existence of a pointwise principal-value
limit from the later theorem identifying that limit with the supplied bounded
`Lp` operator.  The separation prevents a Cauchy estimate from silently
becoming the full Calderón--Zygmund kernel-identification theorem.
-/
structure BeurlingAnnularCancellationWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingLpOperatorWitness p where
  cancellation_ae :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ),
      Nonempty (BeurlingAnnularCauchyData (f : ℂ → ℂ) x)

theorem BeurlingAnnularCancellationWitness.principalValue_exists_ae
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingAnnularCancellationWitness p)
    (f : Lp (α := ℂ) ℂ p (volume : Measure ℂ)) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      ∃ L : ℂ,
        Tendsto
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
          atTop
          (𝓝 L) := by
  filter_upwards [W.cancellation_ae f] with x hx
  exact (Classical.choice hx).exists_principalValue

/-!
The local Holder layer can now be lifted to the a.e. `Lp` boundary without
identifying its limit with an operator value.  This is the precise bridge
between local regularity and the existing annular-cancellation witness.
-/
structure BeurlingHolderAnnularCancellationWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingLpOperatorWitness p where
  holder_ae :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ),
      Nonempty (BeurlingHolderQuarterTurnWitness (f : ℂ → ℂ) x)

theorem BeurlingHolderAnnularCancellationWitness.principalValue_exists_ae
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingHolderAnnularCancellationWitness p)
    (f : Lp (α := ℂ) ℂ p (volume : Measure ℂ)) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      ∃ L : ℂ,
        Tendsto
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
          atTop
          (𝓝 L) := by
  filter_upwards [W.holder_ae f] with x hx
  exact (Classical.choice hx).principalValue_exists

noncomputable def BeurlingHolderAnnularCancellationWitness.toBeurlingAnnularCancellationWitness
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingHolderAnnularCancellationWitness p) :
    BeurlingAnnularCancellationWitness p := by
  refine
    { toBeurlingLpOperatorWitness := W.toBeurlingLpOperatorWitness
      cancellation_ae := ?_ }
  intro f
  filter_upwards [W.holder_ae f] with x hx
  exact
    ⟨(Classical.choice hx).toQuarterTurnCauchyData.toAnnularCauchyData⟩

/-- The exact L² spectral operator as a reusable operator-bound witness. -/
noncomputable def beurlingL2OperatorWitness :
    BeurlingLpOperatorWitness 2 where
  operator := beurlingL2Operator
  norm_bound := 1
  norm_le := by
    simpa using norm_beurlingL2Operator_le

theorem beurlingL2OperatorWitness_operator :
    beurlingL2OperatorWitness.operator = beurlingL2Operator :=
  rfl

theorem beurlingL2OperatorWitness_norm_bound :
    (beurlingL2OperatorWitness.norm_bound : ℝ) = 1 :=
  rfl

/-- A genuine principal-value witness packages the missing convergence theorem. -/
structure BeurlingCalderonZygmundWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingLpOperatorWitness p where
  principalValue_ae :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ),
      Tendsto
        (fun n : ℕ =>
          beurlingTruncatedIntegral ((n + 1 : ℝ)⁻¹) (f : ℂ → ℂ) x)
        atTop
        (𝓝 (toBeurlingLpOperatorWitness.operator f x))

/-!
The exact Fourier-side `L²` operator is the canonical candidate for the
physical Beurling principal value.  The proposition below records precisely
the missing identification target at the layer where both objects are
available.  It is an interface, not an assumed theorem.
-/

def BeurlingL2PrincipalValueIdentificationGoal : Prop :=
  ∀ f : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ),
    Tendsto
      (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
      atTop
      (𝓝 (beurlingL2Operator f x))

noncomputable def beurlingL2CalderonZygmundWitness_of_goal
    (hgoal : BeurlingL2PrincipalValueIdentificationGoal) :
    BeurlingCalderonZygmundWitness 2 := by
  refine
    { toBeurlingLpOperatorWitness := beurlingL2OperatorWitness
      principalValue_ae := ?_ }
  intro f
  change ∀ᵐ x ∂(volume : Measure ℂ),
    Tendsto
      (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
      atTop
      (𝓝 (beurlingL2Operator f x))
  exact hgoal f

theorem BeurlingCalderonZygmundWitness.operator_norm_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingCalderonZygmundWitness p) :
    ‖W.toBeurlingLpOperatorWitness.operator‖ ≤ W.norm_bound :=
  W.norm_le

theorem BeurlingCalderonZygmundWitness.operator_eq_of_principalValue
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {W₁ W₂ : BeurlingCalderonZygmundWitness p} :
    W₁.toBeurlingLpOperatorWitness.operator =
      W₂.toBeurlingLpOperatorWitness.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [W₁.principalValue_ae f, W₂.principalValue_ae f] with x h₁ h₂
  exact tendsto_nhds_unique h₁ h₂

theorem continuousLinearMap_eq_of_eq_on_schwartz
    {A B : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) →L[ℂ]
      Lp (α := ℂ) ℂ 2 (volume : Measure ℂ)}
    (hA : ∀ φ : SchwartzMap ℂ ℂ,
      A (φ.toLp 2 (volume : Measure ℂ)) = B (φ.toLp 2 (volume : Measure ℂ))) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro f
  apply DenseRange.induction_on
    (p := fun g : Lp (α := ℂ) ℂ 2 (volume : Measure ℂ) => A g = B g)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq A.continuous B.continuous
  · intro φ
    exact hA φ

def BeurlingL2SchwartzCalibration
    (W : BeurlingCalderonZygmundWitness 2) : Prop :=
  ∀ φ : SchwartzMap ℂ ℂ,
    W.toBeurlingLpOperatorWitness.operator (φ.toLp 2 (volume : Measure ℂ)) =
      beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ))

def BeurlingL2SchwartzFourierCalibration
    (W : BeurlingCalderonZygmundWitness 2) : Prop :=
  ∀ φ : SchwartzMap ℂ ℂ,
    complexL2Fourier
        (W.toBeurlingLpOperatorWitness.operator (φ.toLp 2 (volume : Measure ℂ))) =
      beurlingSymbolCoefficient.mulLp ((𝓕 φ).toLp 2 (volume : Measure ℂ))

theorem BeurlingCalderonZygmundWitness.schwartzCalibration_of_schwartzFourierCalibration
    (W : BeurlingCalderonZygmundWitness 2)
    (hcal : BeurlingL2SchwartzFourierCalibration W) :
    BeurlingL2SchwartzCalibration W := by
  intro φ
  apply (Lp.fourierTransformₗᵢ ℂ ℂ).injective
  change complexL2Fourier
      (W.toBeurlingLpOperatorWitness.operator (φ.toLp 2 (volume : Measure ℂ))) =
    complexL2Fourier (beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ)))
  rw [hcal φ, beurlingL2Operator_fourier_eq_on_schwartz φ]

def BeurlingL2SchwartzPrincipalValueGoal : Prop :=
  ∀ φ : SchwartzMap ℂ ℂ, ∀ᵐ x ∂(volume : Measure ℂ),
    Tendsto
      (beurlingTruncatedIntegralSequence (φ.toLp 2 (volume : Measure ℂ) : ℂ → ℂ) x)
      atTop
      (𝓝 (beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ)) x))

/-!
The Schwartz test-domain argument has two genuinely different analytic inputs.
First, local Holder control plus annular cancellation gives existence of a
principal-value limit.  Second, the limit has to be identified with the
Fourier-defined `L²` operator.  The structures below keep these inputs
separate, so that a future kernel calculation can discharge them one at a
time without turning the first implication into the second by definition.
-/

def BeurlingL2SchwartzPrincipalValueExistenceGoal : Prop :=
  ∀ φ : SchwartzMap ℂ ℂ, ∀ᵐ x ∂(volume : Measure ℂ),
    ∃ L : ℂ,
      Tendsto
        (beurlingTruncatedIntegralSequence (φ.toLp 2 (volume : Measure ℂ) : ℂ → ℂ) x)
        atTop (𝓝 L)

structure BeurlingL2SchwartzHolderWitness : Prop where
  holder_ae :
    ∀ φ : SchwartzMap ℂ ℂ, ∀ᵐ x ∂(volume : Measure ℂ),
      Nonempty (BeurlingHolderQuarterTurnWitness
        (φ.toLp 2 (volume : Measure ℂ) : ℂ → ℂ) x)

noncomputable def BeurlingHolderAnnularCancellationWitness.toL2SchwartzHolderWitness
    (W : BeurlingHolderAnnularCancellationWitness 2) :
    BeurlingL2SchwartzHolderWitness where
  holder_ae := by
    intro φ
    exact W.holder_ae (φ.toLp 2 (volume : Measure ℂ))

theorem BeurlingL2SchwartzHolderWitness.principalValue_exists
    (W : BeurlingL2SchwartzHolderWitness) :
    BeurlingL2SchwartzPrincipalValueExistenceGoal := by
  intro φ
  filter_upwards [W.holder_ae φ] with x hx
  exact (Classical.choice hx).principalValue_exists

structure BeurlingL2SchwartzPrincipalValueIdentificationWitness
    : Prop extends BeurlingL2SchwartzHolderWitness where
  operator_identifies_ae :
    ∀ φ : SchwartzMap ℂ ℂ, ∀ᵐ x ∂(volume : Measure ℂ), ∀ L : ℂ,
      Tendsto
          (beurlingTruncatedIntegralSequence (φ.toLp 2 (volume : Measure ℂ) : ℂ → ℂ) x)
          atTop (𝓝 L) →
        L = beurlingL2Operator (φ.toLp 2 (volume : Measure ℂ)) x

theorem BeurlingL2SchwartzPrincipalValueIdentificationWitness.principalValue_goal
    (W : BeurlingL2SchwartzPrincipalValueIdentificationWitness) :
    BeurlingL2SchwartzPrincipalValueGoal := by
  intro φ
  filter_upwards [W.holder_ae φ, W.operator_identifies_ae φ] with x hx hidentify
  obtain ⟨L, hL⟩ := (Classical.choice hx).principalValue_exists
  have hL' := hidentify L hL
  simpa [hL'] using hL

theorem BeurlingL2SchwartzPrincipalValueIdentificationWitness.existence
    (W : BeurlingL2SchwartzPrincipalValueIdentificationWitness) :
    BeurlingL2SchwartzPrincipalValueExistenceGoal :=
  W.toBeurlingL2SchwartzHolderWitness.principalValue_exists

theorem BeurlingL2PrincipalValueIdentificationGoal.schwartz
    (hgoal : BeurlingL2PrincipalValueIdentificationGoal) :
    BeurlingL2SchwartzPrincipalValueGoal := by
  intro φ
  exact hgoal (φ.toLp 2 (volume : Measure ℂ))

theorem BeurlingCalderonZygmundWitness.schwartzCalibration_of_schwartzPrincipalValueGoal
    (W : BeurlingCalderonZygmundWitness 2)
    (hgoal : BeurlingL2SchwartzPrincipalValueGoal) :
    BeurlingL2SchwartzCalibration W := by
  intro φ
  apply Lp.ext
  filter_upwards [W.principalValue_ae (φ.toLp 2 (volume : Measure ℂ)), hgoal φ] with x hW hF
  exact tendsto_nhds_unique hW hF

theorem BeurlingCalderonZygmundWitness.operator_eq_beurlingL2_of_schwartzCalibration
    (W : BeurlingCalderonZygmundWitness 2)
    (hcal : BeurlingL2SchwartzCalibration W) :
    W.toBeurlingLpOperatorWitness.operator = beurlingL2Operator := by
  exact continuousLinearMap_eq_of_eq_on_schwartz hcal

theorem BeurlingCalderonZygmundWitness.operator_eq_beurlingL2_of_schwartzFourierCalibration
    (W : BeurlingCalderonZygmundWitness 2)
    (hcal : BeurlingL2SchwartzFourierCalibration W) :
    W.toBeurlingLpOperatorWitness.operator = beurlingL2Operator := by
  exact W.operator_eq_beurlingL2_of_schwartzCalibration
    (W.schwartzCalibration_of_schwartzFourierCalibration hcal)

theorem BeurlingCalderonZygmundWitness.schwartzPrincipalValueGoal_of_schwartzFourierCalibration
    (W : BeurlingCalderonZygmundWitness 2)
    (hcal : BeurlingL2SchwartzFourierCalibration W) :
    BeurlingL2SchwartzPrincipalValueGoal := by
  have hop := W.operator_eq_beurlingL2_of_schwartzFourierCalibration hcal
  intro φ
  rw [← hop]
  exact W.principalValue_ae (φ.toLp 2 (volume : Measure ℂ))

theorem BeurlingCalderonZygmundWitness.operator_eq_beurlingL2_of_schwartzPrincipalValueGoal
    (W : BeurlingCalderonZygmundWitness 2)
    (hgoal : BeurlingL2SchwartzPrincipalValueGoal) :
    W.toBeurlingLpOperatorWitness.operator = beurlingL2Operator := by
  exact W.operator_eq_beurlingL2_of_schwartzCalibration
    (W.schwartzCalibration_of_schwartzPrincipalValueGoal hgoal)

theorem BeurlingCalderonZygmundWitness.operator_eq_beurlingL2_of_schwartzIdentificationWitness
    (W : BeurlingCalderonZygmundWitness 2)
    (H : BeurlingL2SchwartzPrincipalValueIdentificationWitness) :
    W.toBeurlingLpOperatorWitness.operator = beurlingL2Operator := by
  exact W.operator_eq_beurlingL2_of_schwartzPrincipalValueGoal H.principalValue_goal

theorem BeurlingCalderonZygmundWitness.operator_eq_beurlingL2_of_goal
    (hgoal : BeurlingL2PrincipalValueIdentificationGoal)
    (W : BeurlingCalderonZygmundWitness 2) :
    W.toBeurlingLpOperatorWitness.operator = beurlingL2Operator := by
  calc
    W.toBeurlingLpOperatorWitness.operator =
        (beurlingL2CalderonZygmundWitness_of_goal hgoal).toBeurlingLpOperatorWitness.operator :=
      BeurlingCalderonZygmundWitness.operator_eq_of_principalValue
        (W₁ := W) (W₂ := beurlingL2CalderonZygmundWitness_of_goal hgoal)
    _ = beurlingL2Operator := by
      rfl

noncomputable def BeurlingUniformPrincipalValueTailWitness.toBeurlingCalderonZygmundWitness
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingUniformPrincipalValueTailWitness p) :
    BeurlingCalderonZygmundWitness p := by
  refine
    { toBeurlingLpOperatorWitness := W.toBeurlingLpOperatorWitness
      principalValue_ae := ?_ }
  intro f
  change ∀ᵐ x ∂(volume : Measure ℂ),
    Tendsto
      (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
      atTop
      (𝓝 (W.toBeurlingLpOperatorWitness.operator f x))
  exact W.principalValue_ae f

/--
The second half of the principal-value theorem: once annular cancellation has
produced a limit, this input identifies that limit with the supplied bounded
Lp operator.  It is kept separate from cancellation so that the analytic
kernel-identification argument can be developed independently.
-/
structure BeurlingPrincipalValueIdentificationWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingAnnularCancellationWitness p where
  operator_identifies_ae :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ), ∀ L : ℂ,
      Tendsto
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
          atTop
          (𝓝 L) →
        L =
          toBeurlingAnnularCancellationWitness.toBeurlingLpOperatorWitness.operator f x

/-- Combine annular cancellation and operator identification into the full PV witness. -/
noncomputable def BeurlingPrincipalValueIdentificationWitness.toBeurlingCalderonZygmundWitness
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingPrincipalValueIdentificationWitness p) :
    BeurlingCalderonZygmundWitness p := by
  refine
    { toBeurlingLpOperatorWitness :=
        W.toBeurlingAnnularCancellationWitness.toBeurlingLpOperatorWitness
      principalValue_ae := ?_ }
  intro f
  change
    ∀ᵐ x ∂(volume : Measure ℂ),
      Tendsto
        (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
        atTop
        (𝓝 (W.toBeurlingAnnularCancellationWitness.toBeurlingLpOperatorWitness.operator f x))
  filter_upwards [W.cancellation_ae f, W.operator_identifies_ae f] with x hx hidentify
  obtain ⟨L, hL⟩ := (Classical.choice hx).exists_principalValue
  have hL' :=
    hidentify L hL
  simpa [hL'] using hL

/-!
This is the Holder-specific version of the final analytic boundary.  It
keeps the local regularity input and the kernel-identification input in one
record, but the latter remains an explicit field: no operator identity is
smuggled in by the conversion from Holder data.
-/
structure BeurlingHolderPrincipalValueIdentificationWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingHolderAnnularCancellationWitness p where
  operator_identifies_ae :
    ∀ f : Lp (α := ℂ) ℂ p (volume : Measure ℂ), ∀ᵐ x ∂(volume : Measure ℂ), ∀ L : ℂ,
      Tendsto
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
          atTop
          (𝓝 L) →
        L =
          toBeurlingHolderAnnularCancellationWitness.toBeurlingLpOperatorWitness.operator f x

noncomputable def BeurlingHolderPrincipalValueIdentificationWitness.toBeurlingPrincipalValueIdentificationWitness
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingHolderPrincipalValueIdentificationWitness p) :
    BeurlingPrincipalValueIdentificationWitness p := by
  refine
    { toBeurlingAnnularCancellationWitness :=
        W.toBeurlingHolderAnnularCancellationWitness.toBeurlingAnnularCancellationWitness
      operator_identifies_ae := ?_ }
  intro f
  change ∀ᵐ x ∂(volume : Measure ℂ), ∀ L : ℂ,
    Tendsto
        (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x)
        atTop (𝓝 L) →
      L = W.toBeurlingHolderAnnularCancellationWitness.toBeurlingLpOperatorWitness.operator f x
  exact W.operator_identifies_ae f

noncomputable def BeurlingHolderPrincipalValueIdentificationWitness.toBeurlingCalderonZygmundWitness
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (W : BeurlingHolderPrincipalValueIdentificationWitness p) :
    BeurlingCalderonZygmundWitness p :=
  W.toBeurlingPrincipalValueIdentificationWitness.toBeurlingCalderonZygmundWitness

/-!
The uniform tail estimate becomes an annular Cauchy estimate once its modulus
is chosen antitone.  This is the natural quantitative hypothesis in the
Calderón--Zygmund proof: the two tails at scales `m ≤ n` are each controlled by
the outer scale `m`.  The conversion below makes the factor `2` explicit and
then uses uniqueness of limits to recover operator identification.
-/

structure BeurlingMonotonePrincipalValueTailWitness (p : ℝ≥0∞)
    [Fact (1 ≤ p)] extends BeurlingUniformPrincipalValueTailWitness p where
  modulus_antitone : Antitone modulus

namespace BeurlingMonotonePrincipalValueTailWitness

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

noncomputable def toBeurlingAnnularCancellationWitness
    (W : BeurlingMonotonePrincipalValueTailWitness p) :
    BeurlingAnnularCancellationWitness p := by
  refine
    { toBeurlingLpOperatorWitness := W.toBeurlingLpOperatorWitness
      cancellation_ae := ?_ }
  intro f
  filter_upwards [W.tail_bound f] with x hx
  refine ⟨{
      modulus := fun m => 2 * (W.modulus m * ‖f‖)
      modulus_tendsto_zero := ?_
      dist_le := ?_ }⟩
  · have hconst :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hnorm :
        Tendsto (fun _ : ℕ => ‖f‖) atTop (𝓝 ‖f‖) := tendsto_const_nhds
    simpa only [mul_assoc, mul_zero, zero_mul] using
      ((hconst.mul W.modulus_tendsto_zero).mul hnorm)
  · intro m n hmn
    calc
      dist
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x m)
          (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x n) ≤
          dist
              (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x m)
              (W.toBeurlingLpOperatorWitness.operator f x) +
            dist
              (W.toBeurlingLpOperatorWitness.operator f x)
              (beurlingTruncatedIntegralSequence (f : ℂ → ℂ) x n) :=
        dist_triangle _ _ _
      _ ≤ W.modulus m * ‖f‖ + W.modulus n * ‖f‖ := by
        exact add_le_add (hx m) ((by simpa [dist_comm] using hx n))
      _ ≤ W.modulus m * ‖f‖ + W.modulus m * ‖f‖ := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (W.modulus_antitone hmn) (norm_nonneg _))
      _ = 2 * (W.modulus m * ‖f‖) := by ring

noncomputable def principalValueIdentificationWitness
    (W : BeurlingMonotonePrincipalValueTailWitness p) :
    BeurlingPrincipalValueIdentificationWitness p := by
  refine
    { toBeurlingAnnularCancellationWitness :=
        W.toBeurlingAnnularCancellationWitness
      operator_identifies_ae := ?_ }
  intro f
  filter_upwards [W.principalValue_ae f] with x hx
  intro L hL
  exact tendsto_nhds_unique hL hx

noncomputable def toBeurlingCalderonZygmundWitness
    (W : BeurlingMonotonePrincipalValueTailWitness p) :
    BeurlingCalderonZygmundWitness p :=
  W.principalValueIdentificationWitness.toBeurlingCalderonZygmundWitness

end BeurlingMonotonePrincipalValueTailWitness

end

end Teichmuller
