import Teichmuller.MathlibBeltramiNeumann
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace Teichmuller

open Filter Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
### The coefficient-multiplier layer

The Neumann layer only needs a bounded operator `K`.  The next structural
step is to expose the classical factorisation

`K = M_μ ∘ B`,

where `M_μ` is multiplication by a measurable, essentially bounded complex
coefficient and `B` is the still-to-be-supplied singular operator.  This file
constructs `M_μ` on `L^p` for `1 ≤ p`; it does not identify `B` with the
Beurling transform.
-/

/-- A measurable complex coefficient together with an a.e. pointwise bound. -/
structure BoundedScalarCoefficient (α : Type*) [MeasurableSpace α]
    (m : Measure α) where
  toFun : α → ℂ
  aestronglyMeasurable : AEStronglyMeasurable toFun m
  bound : ℝ≥0
  bound_ae : ∀ᵐ x ∂m, ‖toFun x‖₊ ≤ bound

instance {α : Type*} [MeasurableSpace α] {m : Measure α} :
    CoeFun (BoundedScalarCoefficient α m) (fun _ => α → ℂ) :=
  ⟨BoundedScalarCoefficient.toFun⟩

namespace BoundedScalarCoefficient

variable {α : Type*} [MeasurableSpace α] {m : Measure α}

/-- The coefficient as an almost-everywhere equivalence class. -/
def toAEEqFun (c : BoundedScalarCoefficient α m) : α →ₘ[m] ℂ :=
  AEEqFun.mk c.toFun c.aestronglyMeasurable

theorem toAEEqFun_bound_ae (c : BoundedScalarCoefficient α m) :
    ∀ᵐ x ∂m, ‖c.toAEEqFun x‖₊ ≤ c.bound := by
  filter_upwards [c.bound_ae, AEEqFun.coeFn_mk c.toFun c.aestronglyMeasurable] with x hx hmk
  simpa only [toAEEqFun, hmk] using hx

theorem bound_ae_nnnorm (c : BoundedScalarCoefficient α m) :
    ∀ᵐ x ∂m, ‖c x‖₊ ≤ c.bound := by
  filter_upwards [c.bound_ae] with x hx
  rw [← NNReal.coe_le_coe]
  exact_mod_cast hx

/-- Multiplication by `c` on `L^p`. -/
def mulLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) : Lp ℂ p m → Lp ℂ p m :=
  fun f =>
    ⟨c.toAEEqFun * (f : α →ₘ[m] ℂ), by
      apply Lp.mem_Lp_of_nnnorm_ae_le_mul (f := c.toAEEqFun * (f : α →ₘ[m] ℂ)) (g := f)
      filter_upwards [c.toAEEqFun_bound_ae,
        AEEqFun.coeFn_mul c.toAEEqFun (f : α →ₘ[m] ℂ)] with x hbound hmul
      rw [hmul, Pi.mul_apply, nnnorm_mul]
      exact mul_le_mul_of_nonneg_right hbound (by positivity)
    ⟩

theorem coeFn_mulLp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) (f : Lp ℂ p m) :
    c.mulLp f =ᵐ[m] fun x => c x * f x := by
  filter_upwards [AEEqFun.coeFn_mul c.toAEEqFun (f : α →ₘ[m] ℂ),
    AEEqFun.coeFn_mk c.toFun c.aestronglyMeasurable] with x hmul hcoeff
  exact hmul.trans (congrArg (fun z => z * f x) hcoeff)

theorem nnnorm_mulLp_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) (f : Lp ℂ p m) :
    ‖c.mulLp f‖₊ ≤ c.bound * ‖f‖₊ := by
  apply Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul
  filter_upwards [c.coeFn_mulLp f, c.bound_ae_nnnorm] with x hmul hbound
  rw [hmul, nnnorm_mul]
  exact mul_le_mul_of_nonneg_right hbound (by positivity)

theorem norm_mulLp_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) (f : Lp ℂ p m) :
    ‖c.mulLp f‖ ≤ (c.bound : ℝ) * ‖f‖ := by
  exact_mod_cast c.nnnorm_mulLp_le f

/-- The coefficient multiplier as a continuous complex-linear operator. -/
def multiplier {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) : Lp ℂ p m →L[ℂ] Lp ℂ p m :=
  LinearMap.mkContinuous
    { toFun := c.mulLp
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [c.coeFn_mulLp (f + g), c.coeFn_mulLp f, c.coeFn_mulLp g,
          Lp.coeFn_add f g, Lp.coeFn_add (c.mulLp f) (c.mulLp g)] with
          x hmul_sum hmul_f hmul_g hfg hresult
        calc
          c.mulLp (f + g) x = c.toFun x * (f + g) x := hmul_sum
          _ = c.toFun x * f x + c.toFun x * g x := by
            rw [hfg]
            simp [mul_add]
          _ = c.mulLp f x + c.mulLp g x := by rw [hmul_f, hmul_g]
          _ = (c.mulLp f + c.mulLp g) x := hresult.symm
      map_smul' := by
        intro a f
        apply Lp.ext
        filter_upwards [c.coeFn_mulLp (a • f), c.coeFn_mulLp f,
          Lp.coeFn_smul a f, Lp.coeFn_smul a (c.mulLp f)] with
          x hmul hbase hsmul hresult
        calc
          c.mulLp (a • f) x = c.toFun x * (a • f) x := hmul
          _ = a * (c.toFun x * f x) := by
            rw [hsmul]
            simp [smul_eq_mul]
            ring
          _ = a * c.mulLp f x := by rw [hbase]
          _ = (a • c.mulLp f) x := by
            simpa only [Pi.smul_apply, smul_eq_mul] using hresult.symm
    }
    c.bound
    (fun f => c.norm_mulLp_le f)

theorem multiplier_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) (f : Lp ℂ p m) :
    c.multiplier f = c.mulLp f :=
  rfl

theorem norm_multiplier_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m) :
    ‖c.multiplier (p := p)‖ ≤ c.bound := by
  exact c.multiplier.opNorm_le_bound c.bound.coe_nonneg fun f => by
    exact c.norm_mulLp_le f

/-- Compose the coefficient multiplier with a candidate singular operator. -/
def kernel {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m)
    (B : Lp ℂ p m →L[ℂ] Lp ℂ p m) : Lp ℂ p m →L[ℂ] Lp ℂ p m :=
  c.multiplier.comp B

theorem norm_kernel_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : BoundedScalarCoefficient α m)
    (B : Lp ℂ p m →L[ℂ] Lp ℂ p m) :
    ‖c.kernel B‖ ≤ c.bound * ‖B‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (c.norm_multiplier_le (p := p)) (norm_nonneg _))

end BoundedScalarCoefficient

/-- An `L^p` Neumann problem with the coefficient/operator factor exposed. -/
structure LpNeumannBeltramiProblem {α : Type*} [MeasurableSpace α]
    (m : Measure α) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  coefficient : BoundedScalarCoefficient α m
  singularOperator : Lp ℂ p m →L[ℂ] Lp ℂ p m
  forcing : Lp ℂ p m
  coefficient_operator_norm_lt_one :
    (coefficient.bound : ℝ) * ‖singularOperator‖ < 1

namespace LpNeumannBeltramiProblem

variable {α : Type*} [MeasurableSpace α] {m : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def kernel (P : LpNeumannBeltramiProblem m p) : Lp ℂ p m →L[ℂ] Lp ℂ p m :=
  P.coefficient.kernel P.singularOperator

theorem kernel_norm_lt_one (P : LpNeumannBeltramiProblem m p) :
    ‖P.kernel‖ < 1 :=
  (P.coefficient.norm_kernel_le P.singularOperator).trans_lt
    P.coefficient_operator_norm_lt_one

def toNeumannProblem (P : LpNeumannBeltramiProblem m p) :
    NeumannBeltramiProblem (Lp ℂ p m) where
  forcing := P.forcing
  kernel := P.kernel
  kernel_norm_lt_one := by
    exact_mod_cast P.kernel_norm_lt_one

theorem fixedPoint_equation (P : LpNeumannBeltramiProblem m p) :
    P.toNeumannProblem.fixedPoint = P.forcing + P.kernel P.toNeumannProblem.fixedPoint :=
  P.toNeumannProblem.fixedPoint_equation

theorem fixedPoint_unique (P : LpNeumannBeltramiProblem m p) (u : Lp ℂ p m)
    (hu : u = P.forcing + P.kernel u) :
    u = P.toNeumannProblem.fixedPoint :=
  P.toNeumannProblem.fixedPoint_unique u hu

theorem exists_solution (P : LpNeumannBeltramiProblem m p) :
    ∃ u : Lp ℂ p m, u = P.forcing + P.kernel u :=
  P.toNeumannProblem.exists_solution

end LpNeumannBeltramiProblem

/-- Turn the existing measurable Beltrami coefficient into the multiplier input.

The `max k 0` step is intentional: on a null measure a real essential bound
may be negative, while an `ℝ≥0` operator bound cannot be.  The strict bound
`k < 1` is preserved by this harmless normalization.
-/
noncomputable def BeltramiCoefficient.toBoundedScalarCoefficient
    {m : Measure ℂ} (μ : BeltramiCoefficient m) :
    BoundedScalarCoefficient ℂ m := by
  let k : ℝ := Classical.choose μ.essential_bound
  have hk : k < 1 := (Classical.choose_spec μ.essential_bound).1
  have hbound : ∀ᵐ z ∂m, ‖μ z‖ ≤ k := (Classical.choose_spec μ.essential_bound).2
  let C : ℝ≥0 := (max k 0).toNNReal
  have hC : (C : ℝ) = max k 0 := by
    change ((max k 0).toNNReal : ℝ) = max k 0
    exact Real.coe_toNNReal (max k 0) (le_max_right k 0)
  refine
    { toFun := μ
      aestronglyMeasurable := μ.measurable.aestronglyMeasurable
      bound := C
      bound_ae := ?_ }
  filter_upwards [hbound] with z hz
  rw [← NNReal.coe_le_coe]
  simpa only [coe_nnnorm, hC] using hz.trans (le_max_left k 0)

theorem BeltramiCoefficient.toBoundedScalarCoefficient_apply
    {m : Measure ℂ} (μ : BeltramiCoefficient m) (z : ℂ) :
    μ.toBoundedScalarCoefficient z = μ z :=
  by
    change μ.toFun z = μ.toFun z
    rfl

theorem BeltramiCoefficient.toBoundedScalarCoefficient_bound_lt_one
    {m : Measure ℂ} (μ : BeltramiCoefficient m) :
    (μ.toBoundedScalarCoefficient.bound : ℝ) < 1 := by
  have hmax :
      max (Classical.choose μ.essential_bound) 0 < 1 :=
    max_lt (Classical.choose_spec μ.essential_bound).1 (by norm_num)
  simp only [BeltramiCoefficient.toBoundedScalarCoefficient]
  exact Eq.mpr
    (congrArg (fun r : ℝ => r < 1)
      (Real.coe_toNNReal (max (Classical.choose μ.essential_bound) 0)
        (le_max_right _ _))) hmax

end

end Teichmuller
