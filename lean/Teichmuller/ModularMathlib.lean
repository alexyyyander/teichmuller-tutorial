import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Teichmuller.Modular

/-!
The first bridge from the self-contained modular interface to Mathlib's actual
complex model.

The previous `Modular.lean` file deliberately kept the matrix and action
interfaces small.  Mathlib already contains the corresponding mathematical
objects: `SL(2, ℤ)`, the upper half-plane `ℍ`, its Möbius action, and the
standard fundamental-domain theorems.  This file records that bridge without
silently identifying the two representations.
-/

namespace Teichmuller

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Modular

/-- Mathlib's concrete modular group. -/
abbrev MathlibSL2Z := SL(2, ℤ)

/-- Mathlib's concrete complex upper half-plane. -/
abbrev MathlibUpperHalfPlane := UpperHalfPlane

/-- The concrete monoid structure used by the abstract modular interface. -/
def mathlibSL2ZMonoidSpec : MonoidSpec MathlibSL2Z where
  one := 1
  mul := (· * ·)
  one_mul := by intro g; simp
  mul_one := by intro g; simp
  mul_assoc := by intro g h k; simp [mul_assoc]

/-- The actual Möbius action of `SL(2, ℤ)` on `ℍ`, viewed as an action spec. -/
noncomputable def mathlibUpperHalfPlaneActionSpec :
    ActionSpec MathlibSL2Z MathlibUpperHalfPlane mathlibSL2ZMonoidSpec where
  act := (· • ·)
  one_act := by
    intro z
    simp [mathlibSL2ZMonoidSpec]
  mul_act := by
    intro g h z
    simpa [mathlibSL2ZMonoidSpec] using (mul_smul g h z)

/-- A modular function with the genuine Mathlib action, not an abstract action parameter. -/
structure MathlibModularFunction (Y : Type*) where
  toFun : MathlibUpperHalfPlane → Y
  invariant : ∀ (γ : MathlibSL2Z) (τ : MathlibUpperHalfPlane),
    toFun (γ • τ) = toFun τ

/-- The carrier of the complex upper half-plane, viewed as a subset of `ℂ`. -/
def upperHalfPlaneSet : Set ℂ := {z | 0 < z.im}

@[simp]
theorem mem_upperHalfPlaneSet (z : ℂ) : z ∈ upperHalfPlaneSet ↔ 0 < z.im :=
  Iff.rfl

/-- A genuinely analytic complex modular function on the upper half-plane. -/
structure HolomorphicModularFunction where
  toFun : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ toFun upperHalfPlaneSet
  invariant : ∀ (γ : MathlibSL2Z) (τ : MathlibUpperHalfPlane),
    toFun ((γ • τ : MathlibUpperHalfPlane) : ℂ) = toFun (τ : ℂ)

/-- Forget analyticity and retain the underlying Mathlib modular function. -/
def HolomorphicModularFunction.toMathlib
    (f : HolomorphicModularFunction) : MathlibModularFunction ℂ where
  toFun := fun τ => f.toFun (τ : ℂ)
  invariant := f.invariant

/-- Constant functions give a first concrete family of analytic modular functions. -/
def constantHolomorphicModularFunction (c : ℂ) : HolomorphicModularFunction where
  toFun := fun _ => c
  holomorphic := differentiableOn_const c
  invariant := by
    intro γ τ
    rfl

/-- Mathlib's level-one modular forms, indexed by their integral weight. -/
abbrev MathlibLevelOneModularForm (k : ℤ) := ModularForm 𝒮ℒ k

/-- Mathlib's level-one cusp forms, indexed by their integral weight. -/
abbrev MathlibLevelOneCuspForm (k : ℤ) := CuspForm 𝒮ℒ k

/-- The normalized level-one Eisenstein series of weights four and six. -/
noncomputable def mathlibEisensteinE4 : MathlibLevelOneModularForm 4 := ModularForm.E₄

noncomputable def mathlibEisensteinE6 : MathlibLevelOneModularForm 6 := ModularForm.E₆

/-- The non-constant level-one modular discriminant. -/
noncomputable def mathlibDiscriminant : MathlibLevelOneCuspForm 12 := CuspForm.discriminant

theorem mathlibDiscriminant_ne_zero (τ : MathlibUpperHalfPlane) :
    mathlibDiscriminant τ ≠ 0 := by
  simpa [mathlibDiscriminant] using ModularForm.discriminant_ne_zero τ

/-- A formal non-constancy certificate: the first q-expansion coefficient is one. -/
theorem mathlibDiscriminant_qExpansion_coeff_one :
    (qExpansion 1 (mathlibDiscriminant : MathlibUpperHalfPlane → ℂ)).coeff 1 = 1 := by
  simpa [mathlibDiscriminant] using ModularForm.discriminant_qExpansion_coeff_one

/-- The concrete level-one relation that removes the modular weights. -/
theorem mathlibDiscriminant_E4_E6_identity (τ : MathlibUpperHalfPlane) :
    mathlibDiscriminant τ =
      (mathlibEisensteinE4 τ ^ 3 - mathlibEisensteinE6 τ ^ 2) / 1728 := by
  simpa [mathlibDiscriminant, mathlibEisensteinE4, mathlibEisensteinE6] using
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ

/-- The first weight-zero quotient built from the level-one forms.

The denominator is nonzero on `ℍ`, so this is a genuine function on the
upper half-plane.  It is the usual `j`-type normalization; the meromorphic
extension across the compactified cusp is deliberately left for the next
layer.
-/
noncomputable def mathlibJType (τ : MathlibUpperHalfPlane) : ℂ :=
  1728 * mathlibEisensteinE4 τ ^ 3 / mathlibDiscriminant τ

theorem mathlibJType_denominator_ne_zero (τ : MathlibUpperHalfPlane) :
    mathlibDiscriminant τ ≠ 0 :=
  mathlibDiscriminant_ne_zero τ

theorem mathlibJType_invariant (γ : MathlibSL2Z) (τ : MathlibUpperHalfPlane) :
    mathlibJType (γ • τ) = mathlibJType τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE4 := SlashInvariantForm.slash_action_eqn'' mathlibEisensteinE4 hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' mathlibDiscriminant hγ τ
  have haction : (γ • τ : MathlibUpperHalfPlane) =
      ((γ : GL (Fin 2) ℝ) • τ : MathlibUpperHalfPlane) := by
    apply UpperHalfPlane.ext_iff.mpr
    simp [UpperHalfPlane.coe_smul]
  rw [mathlibJType, mathlibJType, haction, hE4, hΔ]
  have hdenom : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hdiscriminant := mathlibDiscriminant_ne_zero τ
  field_simp [hdenom, hdiscriminant]

/-- Package the quotient as the concrete invariant-function interface. -/
noncomputable def mathlibJTypeModularFunction : MathlibModularFunction ℂ where
  toFun := mathlibJType
  invariant := mathlibJType_invariant

/-- Forget the concrete action down to the earlier reusable invariant-function interface. -/
noncomputable def MathlibModularFunction.toAbstract {Y : Type*}
    (f : MathlibModularFunction Y) :
    ModularFunction MathlibSL2Z MathlibUpperHalfPlane Y
      mathlibSL2ZMonoidSpec mathlibUpperHalfPlaneActionSpec where
  toFun := f.toFun
  invariant := by
    intro γ τ
    simpa [mathlibUpperHalfPlaneActionSpec] using f.invariant γ τ

/-- The same `j`-type quotient after forgetting to the reusable abstract layer. -/
noncomputable def mathlibJTypeAbstract :
    ModularFunction MathlibSL2Z MathlibUpperHalfPlane ℂ
      mathlibSL2ZMonoidSpec mathlibUpperHalfPlaneActionSpec :=
  MathlibModularFunction.toAbstract mathlibJTypeModularFunction

/-- Convert the explicit four-entry matrix representation into Mathlib's `SL(2, ℤ)`. -/
def SL2ZMatrix.toMathlib (A : SL2ZMatrix) : MathlibSL2Z :=
  ⟨!![A.a, A.b; A.c, A.d], by
    rw [Matrix.det_fin_two]
    simpa [SL2ZMatrix.det] using A.determinantOne⟩

@[simp]
theorem SL2ZMatrix.toMathlib_apply (A : SL2ZMatrix) :
    (A.toMathlib : Matrix (Fin 2) (Fin 2) ℤ) = !![A.a, A.b; A.c, A.d] :=
  rfl

theorem SL2ZMatrix.toMathlib_injective :
    Function.Injective SL2ZMatrix.toMathlib := by
  intro A B h
  apply SL2ZMatrix.ext
  · have h' := congrArg (fun g : MathlibSL2Z =>
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simpa [SL2ZMatrix.toMathlib] using h'
  · have h' := congrArg (fun g : MathlibSL2Z =>
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    simpa [SL2ZMatrix.toMathlib] using h'
  · have h' := congrArg (fun g : MathlibSL2Z =>
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h
    simpa [SL2ZMatrix.toMathlib] using h'
  · have h' := congrArg (fun g : MathlibSL2Z =>
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
    simpa [SL2ZMatrix.toMathlib] using h'

/-- Every upper-half-plane point has a representative in the standard fundamental domain. -/
theorem exists_fundamental_domain_representative (τ : MathlibUpperHalfPlane) :
    ∃ γ : MathlibSL2Z, γ • τ ∈ ModularGroup.fd :=
  ModularGroup.exists_smul_mem_fd τ

/-- The open fundamental domain has unique representatives up to the central sign. -/
theorem open_fundamental_domain_unique
    (τ : MathlibUpperHalfPlane) (γ : MathlibSL2Z)
    (hτ : τ ∈ ModularGroup.fdo) (hγ : γ • τ ∈ ModularGroup.fdo) :
    τ = γ • τ :=
  ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hτ hγ

@[simp]
theorem translation_generator (τ : MathlibUpperHalfPlane) :
    ModularGroup.T • τ = (1 : ℝ) +ᵥ τ :=
  UpperHalfPlane.modular_T_smul τ

@[simp]
theorem inversion_generator (τ : MathlibUpperHalfPlane) :
    ModularGroup.S • τ = ⟨(-τ : ℂ)⁻¹, UpperHalfPlane.im_inv_neg_coe_pos τ⟩ := by
  exact UpperHalfPlane.modular_S_smul τ

end Teichmuller
