import Teichmuller.MathlibBeltramiDifferential

namespace Teichmuller

open MeasureTheory

universe u

/-!
### Pointwise differential transport cocycles

This is the first honest interface above the scalar coefficient cocycle.  A
transition has both an underlying coordinate map and a pointwise real
derivative.  The derivative satisfies the chain rule on triples, while the
coefficient compatibility uses the Möbius transformation law from
MathlibBeltramiDifferential.

The structure intentionally does not claim that the derivative field is
actually fderiv of the transition map, nor that the transformed
coefficients are measurable and essentially bounded.  Those are analytic
compatibility theorems for a later chart-level construction.
-/

structure BeltramiDifferentialTransportCocycle (I : Type u) where
  measure : I → Measure ℂ
  transition : I → I → ℂ → ℂ
  transition_measurable : ∀ i j, Measurable (transition i j)
  transition_absolutelyContinuous : ∀ i j,
    Measure.map (transition i j) (measure j) ≪ measure i
  coefficient : ∀ i, BeltramiCoefficient (measure i)
  differential : I → I → ℂ → ℂ →L[ℝ] ℂ
  coefficient_compatible : ∀ i j z,
    coefficient j z =
      differentialBeltramiTransform
        (coefficient i (transition i j z))
        (differential i j z)
  transition_self : ∀ i, transition i i = id
  transition_comp : ∀ i j k,
    transition i k = transition i j ∘ transition j k
  differential_self : ∀ i z,
    differential i i z = ContinuousLinearMap.id ℝ ℂ
  differential_comp : ∀ i j k z,
    differential i k z =
      (differential i j (transition j k z)).comp
        (differential j k z)

namespace BeltramiDifferentialTransportCocycle

theorem coefficient_compatible_apply
    {I : Type u} (C : BeltramiDifferentialTransportCocycle I)
    (i j : I) (z : ℂ) :
    C.coefficient j z =
      differentialBeltramiTransform
        (C.coefficient i (C.transition i j z))
        (C.differential i j z) :=
  C.coefficient_compatible i j z

theorem transition_self_apply
    {I : Type u} (C : BeltramiDifferentialTransportCocycle I)
    (i : I) (z : ℂ) :
    C.transition i i z = z := by
  rw [C.transition_self i]
  rfl

theorem transition_comp_apply
    {I : Type u} (C : BeltramiDifferentialTransportCocycle I)
    (i j k : I) (z : ℂ) :
    C.transition i k z =
      C.transition i j (C.transition j k z) := by
  rw [C.transition_comp i j k]
  rfl

theorem differential_self_apply
    {I : Type u} (C : BeltramiDifferentialTransportCocycle I)
    (i : I) (z : ℂ) :
    C.differential i i z = ContinuousLinearMap.id ℝ ℂ :=
  C.differential_self i z

theorem differential_comp_apply
    {I : Type u} (C : BeltramiDifferentialTransportCocycle I)
    (i j k : I) (z w : ℂ) :
    C.differential i k z w =
      C.differential i j (C.transition j k z)
        (C.differential j k z w) := by
  rw [C.differential_comp i j k z]
  rfl

end BeltramiDifferentialTransportCocycle

/-!
The previous structure records a pointwise differential field.  The following
extension is the first bridge to actual analysis: it requires the field to be
the real Fréchet derivative of the transition map.  The chain rule is then a
theorem, rather than another independent cocycle field.
-/

structure RealDifferentiableBeltramiDifferentialTransportCocycle
    (I : Type u) extends BeltramiDifferentialTransportCocycle I where
  transition_differentiable : ∀ i j z,
    DifferentiableAt ℝ (transition i j) z
  differential_eq_fderiv : ∀ i j z,
    differential i j z = fderiv ℝ (transition i j) z

namespace RealDifferentiableBeltramiDifferentialTransportCocycle

theorem differential_comp_from_fderiv
    {I : Type u}
    (C : RealDifferentiableBeltramiDifferentialTransportCocycle I)
    (i j k : I) (z : ℂ) :
    C.differential i k z =
      (C.differential i j (C.transition j k z)).comp
        (C.differential j k z) := by
  rw [C.differential_eq_fderiv, C.differential_eq_fderiv,
    C.differential_eq_fderiv, C.transition_comp i j k]
  exact fderiv_comp z
    (C.transition_differentiable i j (C.transition j k z))
    (C.transition_differentiable j k z)

theorem differential_comp_agrees_with_recorded
    {I : Type u}
    (C : RealDifferentiableBeltramiDifferentialTransportCocycle I)
    (i j k : I) (z : ℂ) :
    C.toBeltramiDifferentialTransportCocycle.differential i k z =
      (C.toBeltramiDifferentialTransportCocycle.differential i j
        (C.transition j k z)).comp
        (C.toBeltramiDifferentialTransportCocycle.differential j k z) :=
  C.differential_comp_from_fderiv i j k z

end RealDifferentiableBeltramiDifferentialTransportCocycle

noncomputable def trivialBeltramiDifferentialTransportCocycle
    (I : Type u) (m : Measure ℂ) :
    BeltramiDifferentialTransportCocycle I where
  measure := fun _ => m
  transition := fun _ _ => id
  transition_measurable := by
    intro i j
    exact measurable_id
  transition_absolutelyContinuous := by
    intro i j
    simpa using (Measure.AbsolutelyContinuous.rfl : m ≪ m)
  coefficient := fun _ => zeroBeltramiCoefficient m
  differential := fun _ _ _ => ContinuousLinearMap.id ℝ ℂ
  coefficient_compatible := by
    intro i j z
    simp [differentialBeltramiTransform, complexDerivativePart,
      antiComplexDerivativePart]
  transition_self := by
    intro i
    rfl
  transition_comp := by
    intro i j k
    funext z
    rfl
  differential_self := by
    intro i z
    rfl
  differential_comp := by
    intro i j k z
    rw [ContinuousLinearMap.id_comp]

noncomputable def trivialRealDifferentiableBeltramiDifferentialTransportCocycle
    (I : Type u) (m : Measure ℂ) :
    RealDifferentiableBeltramiDifferentialTransportCocycle I where
  toBeltramiDifferentialTransportCocycle :=
    trivialBeltramiDifferentialTransportCocycle I m
  transition_differentiable := by
    intro i j z
    change DifferentiableAt ℝ id z
    exact differentiableAt_id
  differential_eq_fderiv := by
    intro i j z
    change (ContinuousLinearMap.id ℝ ℂ) = fderiv ℝ id z
    symm
    exact fderiv_id

@[simp] theorem trivialRealDifferentiableBeltramiDifferentialTransportCocycle_transition
    (I : Type u) (m : Measure ℂ) (i j : I) :
    (trivialRealDifferentiableBeltramiDifferentialTransportCocycle I m).transition i j = id :=
  rfl

end Teichmuller
