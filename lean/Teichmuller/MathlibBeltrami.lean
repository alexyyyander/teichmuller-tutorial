import Mathlib.Analysis.Complex.Conformal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

namespace Teichmuller

open MeasureTheory

/-!
### A first concrete Beltrami layer

The full measurable Riemann mapping theorem is deliberately not asserted here.
This file records the analytic data which that theorem consumes: a measurable
coefficient with an essential bound strictly below one, the real differential
split into its complex-linear and anti-linear parts, and the pointwise
Beltrami equation.  The zero coefficient case is proved to reduce to ordinary
complex differentiability.
-/

noncomputable section

/-- A Beltrami coefficient relative to an explicitly supplied chart measure.

Keeping the measure as a parameter is intentional: a later surface-level
construction can transport the measure through a chart instead of silently
assuming a preferred global volume form. -/
structure BeltramiCoefficient (m : Measure ℂ) where
  toFun : ℂ → ℂ
  measurable : Measurable toFun
  essential_bound : ∃ k : ℝ, k < 1 ∧
    ∀ᵐ z ∂m, ‖toFun z‖ ≤ k

instance {m : Measure ℂ} : CoeFun (BeltramiCoefficient m) (fun _ => ℂ → ℂ) :=
  ⟨BeltramiCoefficient.toFun⟩

theorem BeltramiCoefficient.measurable_toFun
    {m : Measure ℂ} (μ : BeltramiCoefficient m) : Measurable μ :=
  μ.measurable

@[ext] theorem BeltramiCoefficient.ext
    {m : Measure ℂ} {μ ν : BeltramiCoefficient m}
    (h : ∀ z, μ z = ν z) : μ = ν := by
  cases μ with
  | mk f hf hb =>
    cases ν with
    | mk g hg hb' =>
      have hfg : f = g := funext h
      subst g
      rfl

theorem BeltramiCoefficient.exists_essential_bound
    {m : Measure ℂ} (μ : BeltramiCoefficient m) :
    ∃ k : ℝ, k < 1 ∧
      ∀ᵐ z ∂m, ‖μ z‖ ≤ k :=
  μ.essential_bound

theorem BeltramiCoefficient.integrable
    {m : Measure ℂ} [IsFiniteMeasure m]
    (μ : BeltramiCoefficient m) :
    Integrable μ m := by
  rcases μ.exists_essential_bound with ⟨k, hk, hbound⟩
  exact Integrable.of_bound μ.measurable.aestronglyMeasurable k hbound

theorem BeltramiCoefficient.integrable_of_majorant
    {m : Measure ℂ} (μ : BeltramiCoefficient m)
    {g : ℂ → ℝ} (hg : Integrable g m)
    (hbound : ∀ᵐ z ∂m, ‖μ z‖ ≤ g z) :
    Integrable μ m := by
  exact hg.mono' μ.measurable.aestronglyMeasurable hbound

theorem BeltramiCoefficient.integrable_restrict
    {m : Measure ℂ} [IsFiniteMeasure m]
    (μ : BeltramiCoefficient m) (s : Set ℂ) :
    Integrable μ (m.restrict s) := by
  exact μ.integrable.integrableOn

/-- Pull a coefficient back along a measurable coordinate map.

The absolute-continuity hypothesis is the measure-theoretic part of the
coordinate-change rule: the transported chart measure must see every
m-null set as null after applying φ. -/
noncomputable def BeltramiCoefficient.pullback
    {m m' : Measure ℂ} (μ : BeltramiCoefficient m) (φ : ℂ → ℂ)
    (hφ : Measurable φ) (hmap : Measure.map φ m' ≪ m) :
    BeltramiCoefficient m' where
  toFun := fun z => μ (φ z)
  measurable := μ.measurable.comp hφ
  essential_bound := by
    rcases μ.essential_bound with ⟨k, hk, hbound⟩
    refine ⟨k, hk, ?_⟩
    exact ae_of_ae_map (μ := m') hφ.aemeasurable (hmap.ae_le hbound)

@[simp] theorem BeltramiCoefficient.pullback_apply
    {m m' : Measure ℂ} (μ : BeltramiCoefficient m) (φ : ℂ → ℂ)
    (hφ : Measurable φ) (hmap : Measure.map φ m' ≪ m) (z : ℂ) :
    μ.pullback φ hφ hmap z = μ (φ z) :=
  rfl

theorem BeltramiCoefficient.pullback_id
    {m : Measure ℂ} (μ : BeltramiCoefficient m) :
    μ.pullback id measurable_id
        (by simpa using (Measure.AbsolutelyContinuous.rfl : m ≪ m)) = μ := by
  apply BeltramiCoefficient.ext
  intro z
  rfl

/-- Pullback is functorial under composition of measurable coordinate maps.

The absolute-continuity hypotheses compose by first mapping the second
measure along the inner map and then along the outer map.  This is the
measure-theoretic core of the cocycle law for changing Beltrami coordinates. -/
theorem BeltramiCoefficient.pullback_comp
    {m₀ m₁ m₂ : Measure ℂ} (μ : BeltramiCoefficient m₀)
    (φ ψ : ℂ → ℂ)
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφmap : Measure.map φ m₁ ≪ m₀)
    (hψmap : Measure.map ψ m₂ ≪ m₁) :
    (μ.pullback φ hφ hφmap).pullback ψ hψ hψmap =
      μ.pullback (φ ∘ ψ) (hφ.comp hψ) (by
        rw [← Measure.map_map hφ hψ]
        exact (hψmap.map hφ).trans hφmap) := by
  apply BeltramiCoefficient.ext
  intro z
  rfl

noncomputable def zeroBeltramiCoefficient (m : Measure ℂ) : BeltramiCoefficient m where
  toFun := 0
  measurable := measurable_const
  essential_bound := by
    refine ⟨0, by norm_num, ?_⟩
    filter_upwards [] with z
    simp

@[simp] theorem zeroBeltramiCoefficient_apply (m : Measure ℂ) (z : ℂ) :
    zeroBeltramiCoefficient m z = 0 :=
  rfl

/-- The complex-linear coefficient of a real differential `D`. -/
def complexDerivativePart (D : ℂ →L[ℝ] ℂ) : ℂ :=
  (D 1 - Complex.I * D Complex.I) / 2

/-- The anti-linear coefficient of a real differential `D`. -/
def antiComplexDerivativePart (D : ℂ →L[ℝ] ℂ) : ℂ :=
  (D 1 + Complex.I * D Complex.I) / 2

theorem antiComplexDerivativePart_eq_zero_iff
    (D : ℂ →L[ℝ] ℂ) :
    antiComplexDerivativePart D = 0 ↔
      D Complex.I = Complex.I * D 1 := by
  unfold antiComplexDerivativePart
  constructor
  · intro h
    have h' : D 1 + Complex.I * D Complex.I = 0 := by
      exact (div_eq_zero_iff).mp h |>.resolve_right (by norm_num)
    have hmul : Complex.I * (D 1 + Complex.I * D Complex.I) = 0 := by
      rw [h']
      simp
    have hmul' : Complex.I * D 1 - D Complex.I = 0 := by
      calc
        Complex.I * D 1 - D Complex.I =
            Complex.I * D 1 + (Complex.I * Complex.I) * D Complex.I := by
          rw [Complex.I_mul_I]
          ring
        _ = Complex.I * (D 1 + Complex.I * D Complex.I) := by ring
        _ = 0 := hmul
    exact (sub_eq_zero.mp hmul').symm
  · intro h
    rw [h]
    have hzero : D 1 + Complex.I * (Complex.I * D 1) = 0 := by
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    rw [hzero]
    simp

theorem complexDerivativePart_add_antiComplexDerivativePart
    (D : ℂ →L[ℝ] ℂ) :
    complexDerivativePart D + antiComplexDerivativePart D = D 1 := by
  unfold complexDerivativePart antiComplexDerivativePart
  ring

theorem complexDerivativePart_sub_antiComplexDerivativePart
    (D : ℂ →L[ℝ] ℂ) :
    complexDerivativePart D - antiComplexDerivativePart D =
      -Complex.I * D Complex.I := by
  unfold complexDerivativePart antiComplexDerivativePart
  ring_nf

/-- The pointwise Beltrami equation on a set.  The equation is stated only at
points where the real differential exists; no measurable Riemann mapping
theorem is smuggled into this definition. -/
def BeltramiEquationOn {m : Measure ℂ} (μ : BeltramiCoefficient m) (f : ℂ → ℂ)
    (U : Set ℂ) : Prop :=
  ∀ z ∈ U, DifferentiableAt ℝ f z ∧
    antiComplexDerivativePart (fderiv ℝ f z) =
      μ z * complexDerivativePart (fderiv ℝ f z)

/-- The almost-everywhere form of the Beltrami equation used by a global
measurable solution interface.  This is deliberately weaker than
`BeltramiEquationOn`: it asks only for real differentiability and the
equation almost everywhere with respect to the supplied chart measure. -/
def BeltramiEquationAE {m : Measure ℂ} (μ : BeltramiCoefficient m) (f : ℂ → ℂ) : Prop :=
  ∀ᵐ z ∂m, DifferentiableAt ℝ f z ∧
    antiComplexDerivativePart (fderiv ℝ f z) =
      μ z * complexDerivativePart (fderiv ℝ f z)

theorem beltramiEquationOn_univ_toAE
    {m : Measure ℂ} {μ : BeltramiCoefficient m} {f : ℂ → ℂ}
    (h : BeltramiEquationOn μ f Set.univ) :
    BeltramiEquationAE μ f := by
  exact ae_of_all _ (fun z => h z (Set.mem_univ z))

theorem beltramiEquationOn_zero_iff
    (m : Measure ℂ) (f : ℂ → ℂ) (U : Set ℂ) :
    BeltramiEquationOn (zeroBeltramiCoefficient m) f U ↔
      ∀ z ∈ U, DifferentiableAt ℝ f z ∧
        antiComplexDerivativePart (fderiv ℝ f z) = 0 := by
  constructor
  · intro h z hz
    have h' := h z hz
    exact ⟨h'.1, by simpa using h'.2⟩
  · intro h z hz
    have h' := h z hz
    exact ⟨h'.1, by simpa using h'.2⟩

theorem differentiableOn_complex_of_beltramiEquationOn_zero
    {m : Measure ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (h : BeltramiEquationOn (zeroBeltramiCoefficient m) f U) :
    DifferentiableOn ℂ f U := by
  intro z hz
  have hreal : DifferentiableAt ℝ f z := (h z hz).1
  have hanti : antiComplexDerivativePart (fderiv ℝ f z) = 0 := by
    simpa using (h z hz).2
  have hcr : fderiv ℝ f z Complex.I =
      Complex.I • fderiv ℝ f z 1 := by
    have hiff := antiComplexDerivativePart_eq_zero_iff (fderiv ℝ f z)
    have hmul := hiff.mp hanti
    simpa [smul_eq_mul] using hmul
  exact (differentiableAt_complex_iff_differentiableAt_real.mpr
    ⟨hreal, hcr⟩).differentiableWithinAt

theorem beltramiEquationOn_zero_iff_differentiableOn_complex
    {m : Measure ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) :
    BeltramiEquationOn (zeroBeltramiCoefficient m) f U ↔
      DifferentiableOn ℂ f U := by
  constructor
  · exact differentiableOn_complex_of_beltramiEquationOn_zero
  · intro h z hz
    have hcomplex : DifferentiableAt ℂ f z :=
      (h z hz).differentiableAt (hU.mem_nhds hz)
    have hreal_cr := differentiableAt_complex_iff_differentiableAt_real.mp hcomplex
    have hanti : antiComplexDerivativePart (fderiv ℝ f z) = 0 :=
      (antiComplexDerivativePart_eq_zero_iff (fderiv ℝ f z)).2 (by
        simpa [smul_eq_mul] using hreal_cr.2)
    refine ⟨hreal_cr.1, ?_⟩
    simp [hanti]

/-- A local coordinate-domain witness for a Beltrami deformation.

This is the first bridge from the coefficient layer to the chart layer: it
records an open coordinate domain, a map on that domain, and the equation it
satisfies.  It intentionally does not assert existence or uniqueness of a
solution for a prescribed coefficient. -/
structure BeltramiChartDeformation (m : Measure ℂ) where
  coefficient : BeltramiCoefficient m
  domain : Set ℂ
  domain_open : IsOpen domain
  map : ℂ → ℂ
  equation : BeltramiEquationOn coefficient map domain

/-- A global normalized homeomorphic solution witness for a measurable
coefficient.  The extension to `OnePoint ℂ` makes the usual point at infinity
explicit, while the finite normalizations fix `0` and `1`.  This is a data
interface for the measurable Riemann mapping theorem, not the theorem itself:
no constructor from an arbitrary coefficient is provided here. -/
structure NormalizedBeltramiHomeomorph
    {m : Measure ℂ} (μ : BeltramiCoefficient m) where
  map : Homeomorph ℂ ℂ
  mapAtInfinity : Homeomorph (OnePoint ℂ) (OnePoint ℂ)
  mapAtInfinity_coe : ∀ z : ℂ,
    mapAtInfinity (z : OnePoint ℂ) = (map z : OnePoint ℂ)
  mapAtInfinity_infty : mapAtInfinity OnePoint.infty = OnePoint.infty
  equation_ae : BeltramiEquationAE μ map
  map_zero : map 0 = 0
  map_one : map 1 = 1

/-- A stronger, pointwise solution witness.  It can be lowered to the
existing open-domain deformation interface, whereas the a.e. witness above
is the appropriate target for a measurable Riemann mapping theorem. -/
structure PointwiseNormalizedBeltramiHomeomorph
    {m : Measure ℂ} (μ : BeltramiCoefficient m)
    extends NormalizedBeltramiHomeomorph μ where
  equation : BeltramiEquationOn μ map Set.univ

def PointwiseNormalizedBeltramiHomeomorph.toChartDeformation
    {m : Measure ℂ} {μ : BeltramiCoefficient m}
    (S : PointwiseNormalizedBeltramiHomeomorph μ) :
    BeltramiChartDeformation m where
  coefficient := μ
  domain := Set.univ
  domain_open := isOpen_univ
  map := S.map
  equation := S.equation

theorem PointwiseNormalizedBeltramiHomeomorph.equation_ae_of_equation
    {m : Measure ℂ} {μ : BeltramiCoefficient m}
    (S : PointwiseNormalizedBeltramiHomeomorph μ) :
    BeltramiEquationAE μ S.map :=
  beltramiEquationOn_univ_toAE S.equation

/-- A conditional existence-and-uniqueness witness for the normalized
measurable solution problem.  The actual measurable Riemann mapping theorem
must eventually construct this structure from analytic hypotheses; keeping
it explicit prevents the current development from treating existence as a
definition or as an accidental consequence of integrability. -/
structure NormalizedBeltramiMappingWitness
    {m : Measure ℂ} (μ : BeltramiCoefficient m) where
  solution : NormalizedBeltramiHomeomorph μ
  unique : ∀ T : NormalizedBeltramiHomeomorph μ, T.map = solution.map

theorem NormalizedBeltramiMappingWitness.unique_map
    {m : Measure ℂ} {μ : BeltramiCoefficient m}
    (W : NormalizedBeltramiMappingWitness μ)
    (T : NormalizedBeltramiHomeomorph μ) :
    T.map = W.solution.map :=
  W.unique T

/-- Fiberwise Beltrami data over a topological parameter space.

The structure records exactly the first family-level compatibility needed by
the program: open varying coordinate domains, a Beltrami equation in each
fiber, and continuity of the joint map on the total coordinate domain. It
does not assert that the coefficients themselves vary continuously, nor that
the family is universal. -/
structure BeltramiFamilyData (B : Type*) [TopologicalSpace B]
    (m : Measure ℂ) where
  domain : B → Set ℂ
  domain_open : ∀ b, IsOpen (domain b)
  coefficient : B → BeltramiCoefficient m
  map : B → ℂ → ℂ
  equation : ∀ b, BeltramiEquationOn (coefficient b) (map b) (domain b)
  totalDomain : Set (B × ℂ)
  totalDomain_eq : totalDomain = {p | p.2 ∈ domain p.1}
  totalMap : B × ℂ → ℂ
  totalMap_eq : ∀ b z, totalMap (b, z) = map b z
  totalMap_continuousOn : ContinuousOn totalMap totalDomain

/-! A parameter-regularity layer deliberately separate from coordinate
regularity: the coefficient is still only required to be measurable in its
coordinate, while its value at each fixed coordinate varies continuously with
the parameter. -/

structure ParameterContinuousBeltramiFamilyData
    (B : Type*) [TopologicalSpace B] (m : Measure ℂ)
    extends BeltramiFamilyData B m where
  coefficient_parameter_continuous :
    ∀ z : ℂ, Continuous (fun b => coefficient b z)

theorem ParameterContinuousBeltramiFamilyData.coefficient_continuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : ParameterContinuousBeltramiFamilyData B m) (z : ℂ) :
    Continuous (fun b => F.coefficient b z) :=
  F.coefficient_parameter_continuous z

/-- A family of pointwise normalized solution witnesses.

The coefficient field is continuous at each fixed coordinate and the solution
maps are jointly continuous in the parameter and coordinate.  The pointwise
equation is intentionally stronger than the a.e. equation in
NormalizedBeltramiHomeomorph; it is the bridge needed to reuse the existing
BeltramiFamilyData interface.  Existence of such a family is not inferred
from these regularity hypotheses. -/
structure PointwiseNormalizedBeltramiFamilyWitness
    (B : Type*) [TopologicalSpace B] (m : Measure ℂ) where
  coefficient : B → BeltramiCoefficient m
  coefficient_parameter_continuous :
    ∀ z : ℂ, Continuous (fun b => coefficient b z)
  solution : ∀ b, PointwiseNormalizedBeltramiHomeomorph (coefficient b)
  solution_totalMap_continuous :
    Continuous (fun p : B × ℂ => (solution p.1).map p.2)

def PointwiseNormalizedBeltramiFamilyWitness.toBeltramiFamilyData
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : PointwiseNormalizedBeltramiFamilyWitness B m) :
    BeltramiFamilyData B m where
  domain := fun _ => Set.univ
  domain_open := fun _ => isOpen_univ
  coefficient := F.coefficient
  map := fun b => (F.solution b).map
  equation := fun b => (F.solution b).equation
  totalDomain := Set.univ
  totalDomain_eq := by
    ext p
    simp
  totalMap := fun p => (F.solution p.1).map p.2
  totalMap_eq := by
    intro b z
    rfl
  totalMap_continuousOn := F.solution_totalMap_continuous.continuousOn

def PointwiseNormalizedBeltramiFamilyWitness.toParameterContinuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : PointwiseNormalizedBeltramiFamilyWitness B m) :
    ParameterContinuousBeltramiFamilyData B m where
  toBeltramiFamilyData := F.toBeltramiFamilyData
  coefficient_parameter_continuous := F.coefficient_parameter_continuous

theorem PointwiseNormalizedBeltramiFamilyWitness.coefficient_continuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : PointwiseNormalizedBeltramiFamilyWitness B m) (z : ℂ) :
    Continuous (fun b => F.coefficient b z) :=
  F.coefficient_parameter_continuous z

/-- The a.e. family analogue of BeltramiFamilyData.

This separates the measurable-solution output from the stronger pointwise
family interface.  Its equation field is deliberately a.e. with respect to
the explicit chart measure. -/
structure AEBeltramiFamilyData
    (B : Type*) [TopologicalSpace B] (m : Measure ℂ) where
  domain : B → Set ℂ
  domain_open : ∀ b, IsOpen (domain b)
  coefficient : B → BeltramiCoefficient m
  map : B → ℂ → ℂ
  equation_ae : ∀ b, BeltramiEquationAE (coefficient b) (map b)
  totalDomain : Set (B × ℂ)
  totalDomain_eq : totalDomain = {p | p.2 ∈ domain p.1}
  totalMap : B × ℂ → ℂ
  totalMap_eq : ∀ b z, totalMap (b, z) = map b z
  totalMap_continuousOn : ContinuousOn totalMap totalDomain

/-- A parameterized family of global normalized a.e. solution witnesses.

Unlike the pointwise family witness, this is the exact regularity level
compatible with the measurable Riemann mapping theorem interface. -/
structure AENormalizedBeltramiFamilyWitness
    (B : Type*) [TopologicalSpace B] (m : Measure ℂ) where
  coefficient : B → BeltramiCoefficient m
  coefficient_parameter_continuous :
    ∀ z : ℂ, Continuous (fun b => coefficient b z)
  solution : ∀ b, NormalizedBeltramiHomeomorph (coefficient b)
  solution_totalMap_continuous :
    Continuous (fun p : B × ℂ => (solution p.1).map p.2)

def PointwiseNormalizedBeltramiFamilyWitness.toAENormalizedBeltramiFamilyWitness
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : PointwiseNormalizedBeltramiFamilyWitness B m) :
    AENormalizedBeltramiFamilyWitness B m where
  coefficient := F.coefficient
  coefficient_parameter_continuous := F.coefficient_parameter_continuous
  solution := fun b => (F.solution b).toNormalizedBeltramiHomeomorph
  solution_totalMap_continuous := by
    simpa using F.solution_totalMap_continuous

def AENormalizedBeltramiFamilyWitness.toAEBeltramiFamilyData
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : AENormalizedBeltramiFamilyWitness B m) :
    AEBeltramiFamilyData B m where
  domain := fun _ => Set.univ
  domain_open := fun _ => isOpen_univ
  coefficient := F.coefficient
  map := fun b => (F.solution b).map
  equation_ae := fun b => (F.solution b).equation_ae
  totalDomain := Set.univ
  totalDomain_eq := by
    ext p
    simp
  totalMap := fun p => (F.solution p.1).map p.2
  totalMap_eq := by
    intro b z
    rfl
  totalMap_continuousOn := F.solution_totalMap_continuous.continuousOn

theorem AENormalizedBeltramiFamilyWitness.coefficient_continuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : AENormalizedBeltramiFamilyWitness B m) (z : ℂ) :
    Continuous (fun b => F.coefficient b z) :=
  F.coefficient_parameter_continuous z

theorem BeltramiFamilyData.mem_totalDomain_iff
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ}
    (F : BeltramiFamilyData B m) (b : B) (z : ℂ) :
    (b, z) ∈ F.totalDomain ↔ z ∈ F.domain b := by
  simp [F.totalDomain_eq]

theorem BeltramiChartDeformation.zero_isComplexOn
    {m : Measure ℂ} (D : BeltramiChartDeformation m)
  (hzero : D.coefficient = zeroBeltramiCoefficient m) :
    DifferentiableOn ℂ D.map D.domain := by
  have heq := D.equation
  rw [hzero] at heq
  exact differentiableOn_complex_of_beltramiEquationOn_zero heq

noncomputable def zeroBeltramiChartDeformation
    (m : Measure ℂ) (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) : BeltramiChartDeformation m where
  coefficient := zeroBeltramiCoefficient m
  domain := U
  domain_open := hU
  map := f
  equation := beltramiEquationOn_zero_iff_differentiableOn_complex hU |>.mpr hf

theorem beltramiEquationOn_zero_id (m : Measure ℂ) (U : Set ℂ) :
    BeltramiEquationOn (zeroBeltramiCoefficient m) id U := by
  intro z hz
  have hderiv : fderiv ℝ (id : ℂ → ℂ) z =
      ContinuousLinearMap.id ℝ ℂ := by
    exact fderiv_id
  refine ⟨differentiableAt_id, ?_⟩
  rw [hderiv]
  simp [antiComplexDerivativePart, complexDerivativePart]

/-- The constant coefficient model with strict distortion bound. -/
noncomputable def constantBeltramiCoefficient
    (m : Measure ℂ) (μ : ℂ) (hμ : ‖μ‖ < 1) :
    BeltramiCoefficient m where
  toFun := fun _ => μ
  measurable := measurable_const
  essential_bound := by
    refine ⟨‖μ‖, hμ, ?_⟩
    filter_upwards [] with z
    rfl

@[simp] theorem constantBeltramiCoefficient_apply
    (m : Measure ℂ) (μ : ℂ) (hμ : ‖μ‖ < 1) (z : ℂ) :
    constantBeltramiCoefficient m μ hμ z = μ :=
  rfl

def constantBeltramiAffineMap (μ : ℂ) (z : ℂ) : ℂ :=
  (1 + μ)⁻¹ * (z + μ * (starRingEnd ℂ) z)

def constantBeltramiAffineInverse (μ : ℂ) (z : ℂ) : ℂ :=
  (1 - (Complex.normSq μ : ℂ))⁻¹ *
    ((1 + μ) * z - μ * (starRingEnd ℂ) ((1 + μ) * z))

theorem constantBeltrami_denominator_ne_zero
    {μ : ℂ} (hμ : ‖μ‖ < 1) :
    1 - (Complex.normSq μ : ℂ) ≠ 0 := by
  have hsq : ‖μ‖ ^ 2 < (1 : ℝ) := by
    nlinarith [norm_nonneg μ]
  have hnormSq : Complex.normSq μ < (1 : ℝ) := by
    rw [← Complex.sq_norm μ]
    exact hsq
  intro h
  have hreal : (1 : ℝ) - Complex.normSq μ = 0 := by
    exact_mod_cast congrArg Complex.re h
  exact (ne_of_gt (sub_pos.mpr hnormSq)) hreal

theorem constantBeltrami_one_add_ne_zero
    {μ : ℂ} (hμ : ‖μ‖ < 1) :
    1 + μ ≠ 0 := by
  intro h
  have hneg : μ = -1 := eq_neg_of_add_eq_zero_right h
  rw [hneg] at hμ
  norm_num at hμ

theorem constantBeltramiAffineMap_left_inv
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    constantBeltramiAffineInverse μ
        (constantBeltramiAffineMap μ z) = z := by
  have h₁ := constantBeltrami_one_add_ne_zero hμ
  have h₂ := constantBeltrami_denominator_ne_zero hμ
  have h₁' : 1 + (starRingEnd ℂ) μ ≠ 0 := by
    intro h
    apply h₁
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  simp [constantBeltramiAffineInverse, constantBeltramiAffineMap,
    map_add, map_mul, map_sub, map_inv₀, Complex.mul_conj]
  field_simp [h₁, h₁', h₂]
  ring_nf
  have hμnorm : μ * (starRingEnd ℂ) μ = (Complex.normSq μ : ℂ) :=
    Complex.mul_conj μ
  linear_combination -z * hμnorm

theorem constantBeltramiAffineMap_right_inv
    {μ : ℂ} (hμ : ‖μ‖ < 1) (z : ℂ) :
    constantBeltramiAffineMap μ
        (constantBeltramiAffineInverse μ z) = z := by
  have h₁ := constantBeltrami_one_add_ne_zero hμ
  have h₂ := constantBeltrami_denominator_ne_zero hμ
  have h₁' : 1 + (starRingEnd ℂ) μ ≠ 0 := by
    intro h
    apply h₁
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  simp [constantBeltramiAffineInverse, constantBeltramiAffineMap,
    map_add, map_mul, map_sub, map_inv₀, Complex.mul_conj]
  field_simp [h₁, h₁', h₂]
  ring_nf
  have hμnorm : μ * (starRingEnd ℂ) μ = (Complex.normSq μ : ℂ) :=
    Complex.mul_conj μ
  linear_combination -z * (1 + μ) * hμnorm

theorem constantBeltramiAffineMap_continuous
    (μ : ℂ) (hμ : ‖μ‖ < 1) :
    Continuous (constantBeltramiAffineMap μ) := by
  unfold constantBeltramiAffineMap
  fun_prop

theorem constantBeltramiAffineInverse_continuous
    (μ : ℂ) :
    Continuous (constantBeltramiAffineInverse μ) := by
  unfold constantBeltramiAffineInverse
  fun_prop

noncomputable def constantBeltramiAffineHomeomorph
    (μ : ℂ) (hμ : ‖μ‖ < 1) : Homeomorph ℂ ℂ where
  toFun := constantBeltramiAffineMap μ
  invFun := constantBeltramiAffineInverse μ
  left_inv := constantBeltramiAffineMap_left_inv hμ
  right_inv := constantBeltramiAffineMap_right_inv hμ
  continuous_toFun := constantBeltramiAffineMap_continuous μ hμ
  continuous_invFun := constantBeltramiAffineInverse_continuous μ

noncomputable def zeroPointwiseNormalizedBeltramiHomeomorph
    (m : Measure ℂ) :
    PointwiseNormalizedBeltramiHomeomorph
      (zeroBeltramiCoefficient m) where
  map := Homeomorph.refl ℂ
  mapAtInfinity := Homeomorph.refl (OnePoint ℂ)
  mapAtInfinity_coe := by
    intro z
    rfl
  mapAtInfinity_infty := by
    rfl
  equation_ae := beltramiEquationOn_univ_toAE
    (beltramiEquationOn_zero_id m Set.univ)
  map_zero := by
    simp
  map_one := by
    simp
  equation := beltramiEquationOn_zero_id m Set.univ

noncomputable def zeroPointwiseNormalizedBeltramiFamilyWitness
    {B : Type*} [TopologicalSpace B] (m : Measure ℂ) :
    PointwiseNormalizedBeltramiFamilyWitness B m where
  coefficient := fun _ => zeroBeltramiCoefficient m
  coefficient_parameter_continuous := by
    intro z
    simpa using (continuous_const : Continuous (fun _ : B => (0 : ℂ)))
  solution := fun _ => zeroPointwiseNormalizedBeltramiHomeomorph m
  solution_totalMap_continuous := by
    simpa [zeroPointwiseNormalizedBeltramiHomeomorph] using
      (continuous_snd : Continuous (fun p : B × ℂ => p.2))

noncomputable def zeroAENormalizedBeltramiFamilyWitness
    {B : Type*} [TopologicalSpace B] (m : Measure ℂ) :
    AENormalizedBeltramiFamilyWitness B m where
  coefficient := fun _ => zeroBeltramiCoefficient m
  coefficient_parameter_continuous := by
    intro z
    simpa using (continuous_const : Continuous (fun _ : B => (0 : ℂ)))
  solution := fun _ =>
    (zeroPointwiseNormalizedBeltramiHomeomorph m).toNormalizedBeltramiHomeomorph
  solution_totalMap_continuous := by
    simpa [zeroPointwiseNormalizedBeltramiHomeomorph] using
      (continuous_snd : Continuous (fun p : B × ℂ => p.2))

noncomputable def zeroParameterContinuousBeltramiFamilyData
    {B : Type*} [TopologicalSpace B] (m : Measure ℂ) :
    ParameterContinuousBeltramiFamilyData B m where
  toBeltramiFamilyData := {
    domain := fun _ => Set.univ
    domain_open := fun _ => isOpen_univ
    coefficient := fun _ => zeroBeltramiCoefficient m
    map := fun _ => id
    equation := fun _ => beltramiEquationOn_zero_id m Set.univ
    totalDomain := Set.univ
    totalDomain_eq := by
      ext p
      simp
    totalMap := fun p => p.2
    totalMap_eq := by
      intro b z
      rfl
    totalMap_continuousOn := continuous_snd.continuousOn
  }
  coefficient_parameter_continuous := by
    intro z
    simpa using (continuous_const : Continuous (fun _ : B => (0 : ℂ)))

@[simp] theorem zeroParameterContinuousBeltramiFamilyData_coefficient
    {B : Type*} [TopologicalSpace B] (m : Measure ℂ) (b : B) :
    (zeroParameterContinuousBeltramiFamilyData m).coefficient b =
      zeroBeltramiCoefficient m :=
  rfl

end

end Teichmuller
