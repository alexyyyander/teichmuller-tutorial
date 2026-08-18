import Teichmuller.MathlibBeltramiDifferentialCocycle
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace Teichmuller

open MeasureTheory

universe u

/-!
### Almost-everywhere differential transport

The pointwise differential cocycle is useful for exact calculations, but a
chartwise Beltrami construction is naturally measured only almost everywhere.
This file records that next interface without adding an unproved regularity
theorem.  In particular, the a.e. compatibility and chain laws are fields of
the structure: an analytic construction must supply them, rather than obtain
them for free from notation.
-/

structure AEBeltramiDifferentialTransportCocycle (I : Type u) where
  measure : I → Measure ℂ
  transition : I → I → ℂ → ℂ
  transition_measurable : ∀ i j, Measurable (transition i j)
  transition_absolutelyContinuous : ∀ i j,
    Measure.map (transition i j) (measure j) ≪ measure i
  coefficient : ∀ i, BeltramiCoefficient (measure i)
  differential : I → I → ℂ → ℂ →L[ℝ] ℂ
  differential_aestronglyMeasurable : ∀ i j,
    AEStronglyMeasurable (differential i j) (measure j)
  coefficient_compatible_ae : ∀ i j,
    ∀ᵐ z ∂measure j,
      coefficient j z =
        differentialBeltramiTransform
          (coefficient i (transition i j z))
          (differential i j z)
  transition_self : ∀ i, transition i i = id
  transition_comp : ∀ i j k,
    transition i k = transition i j ∘ transition j k
  differential_self_ae : ∀ i,
    ∀ᵐ z ∂measure i,
      differential i i z = ContinuousLinearMap.id ℝ ℂ
  differential_comp_ae : ∀ i j k,
    ∀ᵐ z ∂measure k,
      differential i k z =
        (differential i j (transition j k z)).comp
          (differential j k z)

namespace AEBeltramiDifferentialTransportCocycle

theorem coefficient_compatible_ae_apply
    {I : Type u} (C : AEBeltramiDifferentialTransportCocycle I)
    (i j : I) :
    ∀ᵐ z ∂C.measure j,
      C.coefficient j z =
        differentialBeltramiTransform
          (C.coefficient i (C.transition i j z))
          (C.differential i j z) :=
  C.coefficient_compatible_ae i j

theorem differential_self_ae_apply
    {I : Type u} (C : AEBeltramiDifferentialTransportCocycle I)
    (i : I) :
    ∀ᵐ z ∂C.measure i,
      C.differential i i z = ContinuousLinearMap.id ℝ ℂ :=
  C.differential_self_ae i

theorem differential_comp_ae_apply
    {I : Type u} (C : AEBeltramiDifferentialTransportCocycle I)
    (i j k : I) (w : ℂ) :
    ∀ᵐ z ∂C.measure k,
      C.differential i k z w =
        C.differential i j (C.transition j k z)
          (C.differential j k z w) := by
  filter_upwards [C.differential_comp_ae i j k] with z hz
  rw [hz]
  rfl

/-!
An exact pointwise cocycle can be viewed as an a.e. cocycle once the
differential field has been supplied with the required measurable envelope.
The hypothesis is explicit because arbitrary pointwise derivatives are not
silently promoted to measurable fields here.
-/

noncomputable def ofPointwise
    {I : Type u}
    (C : BeltramiDifferentialTransportCocycle I)
    (hmeas : ∀ i j,
      AEStronglyMeasurable (C.differential i j) (C.measure j)) :
    AEBeltramiDifferentialTransportCocycle I where
  measure := C.measure
  transition := C.transition
  transition_measurable := C.transition_measurable
  transition_absolutelyContinuous := C.transition_absolutelyContinuous
  coefficient := C.coefficient
  differential := C.differential
  differential_aestronglyMeasurable := hmeas
  coefficient_compatible_ae := by
    intro i j
    exact Filter.Eventually.of_forall (C.coefficient_compatible i j)
  transition_self := C.transition_self
  transition_comp := C.transition_comp
  differential_self_ae := by
    intro i
    exact Filter.Eventually.of_forall (C.differential_self i)
  differential_comp_ae := by
    intro i j k
    exact Filter.Eventually.of_forall (C.differential_comp i j k)

end AEBeltramiDifferentialTransportCocycle

/-!
This extension names the a.e. statement that the recorded differential is
the actual Fréchet derivative of the transition.  It is intentionally weaker
than the everywhere-differentiable structure from the preceding file.
-/

structure RealDifferentiableAEBeltramiDifferentialTransportCocycle
    (I : Type u) extends AEBeltramiDifferentialTransportCocycle I where
  transition_differentiable_ae : ∀ i j,
    ∀ᵐ z ∂measure j, DifferentiableAt ℝ (transition i j) z
  differential_eq_fderiv_ae : ∀ i j,
    ∀ᵐ z ∂measure j,
      differential i j z = fderiv ℝ (transition i j) z

namespace RealDifferentiableAEBeltramiDifferentialTransportCocycle

theorem coefficient_compatible_ae_with_fderiv
    {I : Type u}
    (C : RealDifferentiableAEBeltramiDifferentialTransportCocycle I)
    (i j : I) :
    ∀ᵐ z ∂C.measure j,
      C.coefficient j z =
        differentialBeltramiTransform
          (C.coefficient i (C.transition i j z))
          (fderiv ℝ (C.transition i j) z) := by
  filter_upwards [C.coefficient_compatible_ae i j,
    C.differential_eq_fderiv_ae i j] with z hz hderiv
  rw [← hderiv]
  exact hz

/-!
The everywhere-differentiable structure embeds into this a.e. layer after
the user supplies measurability of its differential field.  This is a
conversion theorem, not a claim that differentiability alone implies the
needed chartwise measurable regularity in the generality of this project.
-/

noncomputable def ofEverywhereDifferentiable
    {I : Type u}
    (C : RealDifferentiableBeltramiDifferentialTransportCocycle I)
    (hmeas : ∀ i j,
      AEStronglyMeasurable (C.differential i j) (C.measure j)) :
    RealDifferentiableAEBeltramiDifferentialTransportCocycle I where
  toAEBeltramiDifferentialTransportCocycle :=
    AEBeltramiDifferentialTransportCocycle.ofPointwise
      C.toBeltramiDifferentialTransportCocycle hmeas
  transition_differentiable_ae := by
    intro i j
    exact Filter.Eventually.of_forall (C.transition_differentiable i j)
  differential_eq_fderiv_ae := by
    intro i j
    exact Filter.Eventually.of_forall (C.differential_eq_fderiv i j)

end RealDifferentiableAEBeltramiDifferentialTransportCocycle

noncomputable def trivialAEBeltramiDifferentialTransportCocycle
    (I : Type u) (m : Measure ℂ) :
    AEBeltramiDifferentialTransportCocycle I :=
  AEBeltramiDifferentialTransportCocycle.ofPointwise
    (trivialBeltramiDifferentialTransportCocycle I m)
    (by
      intro i j
      exact aestronglyMeasurable_const)

end Teichmuller
