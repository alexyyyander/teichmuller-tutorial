import Teichmuller.MathlibBeltrami

namespace Teichmuller

open MeasureTheory

universe u

/-!
### A first chart-cocycle layer for coefficient transport

The structure below is deliberately a scalar transport cocycle: it records
composition of coordinate maps, absolute continuity of the transported chart
measures, and compatibility of the coefficient functions under composition.
It is not yet the full Beltrami differential transformation law, which must
also use the derivative of a coordinate change.  Keeping this distinction
explicit prevents a measurable-composition lemma from being mistaken for the
measurable Riemann mapping theorem.
-/

structure BeltramiCoefficientTransportCocycle (I : Type u) where
  measure : I → Measure ℂ
  transition : I → I → ℂ → ℂ
  transition_measurable : ∀ i j, Measurable (transition i j)
  transition_absolutelyContinuous : ∀ i j,
    Measure.map (transition i j) (measure j) ≪ measure i
  coefficient : ∀ i, BeltramiCoefficient (measure i)
  coefficient_compatible : ∀ i j,
    (coefficient i).pullback (transition i j)
      (transition_measurable i j)
      (transition_absolutelyContinuous i j) = coefficient j
  transition_self : ∀ i, transition i i = id
  transition_comp : ∀ i j k,
    transition i k = transition i j ∘ transition j k

namespace BeltramiCoefficientTransportCocycle

theorem coefficient_compatible_apply
    {I : Type u} (C : BeltramiCoefficientTransportCocycle I)
    (i j : I) (z : ℂ) :
    C.coefficient i (C.transition i j z) = C.coefficient j z := by
  have h := congrArg (fun μ => μ z) (C.coefficient_compatible i j)
  simpa using h

theorem transition_self_apply
    {I : Type u} (C : BeltramiCoefficientTransportCocycle I)
    (i : I) (z : ℂ) : C.transition i i z = z := by
  rw [C.transition_self i]
  rfl

theorem transition_comp_apply
    {I : Type u} (C : BeltramiCoefficientTransportCocycle I)
    (i j k : I) (z : ℂ) :
    C.transition i k z = C.transition i j (C.transition j k z) := by
  rw [C.transition_comp i j k]
  rfl

theorem coefficient_pullback_self
    {I : Type u} (C : BeltramiCoefficientTransportCocycle I)
    (i : I) :
    (C.coefficient i).pullback (C.transition i i)
      (C.transition_measurable i i)
      (C.transition_absolutelyContinuous i i) = C.coefficient i := by
  exact C.coefficient_compatible i i

/-- Compatibility transported twice agrees with the direct third transition.

This theorem is the first explicit cocycle consequence of the measure
transport law: the inner and outer pullbacks combine by `pullback_comp`, and
the transition cocycle identifies their composite with the direct map. -/
theorem coefficient_pullback_pullback
    {I : Type u} (C : BeltramiCoefficientTransportCocycle I)
    (i j k : I) :
    ((C.coefficient i).pullback (C.transition i j)
      (C.transition_measurable i j)
      (C.transition_absolutelyContinuous i j)).pullback
        (C.transition j k)
        (C.transition_measurable j k)
        (C.transition_absolutelyContinuous j k) = C.coefficient k := by
  calc
    ((C.coefficient i).pullback (C.transition i j)
        (C.transition_measurable i j)
        (C.transition_absolutelyContinuous i j)).pullback
        (C.transition j k)
        (C.transition_measurable j k)
        (C.transition_absolutelyContinuous j k) =
      (C.coefficient i).pullback
        (C.transition i j ∘ C.transition j k)
        ((C.transition_measurable i j).comp (C.transition_measurable j k))
        (by
          rw [← Measure.map_map (C.transition_measurable i j)
            (C.transition_measurable j k)]
          exact (C.transition_absolutelyContinuous j k).map
            (C.transition_measurable i j) |>.trans
            (C.transition_absolutelyContinuous i j)) := by
      exact BeltramiCoefficient.pullback_comp
        (C.coefficient i) (C.transition i j) (C.transition j k)
        (C.transition_measurable i j) (C.transition_measurable j k)
        (C.transition_absolutelyContinuous i j)
        (C.transition_absolutelyContinuous j k)
    _ = (C.coefficient i).pullback (C.transition i k)
        (C.transition_measurable i k)
        (C.transition_absolutelyContinuous i k) := by
      apply BeltramiCoefficient.ext
      intro z
      simp only [BeltramiCoefficient.pullback_apply]
      rw [C.transition_comp i j k]
    _ = C.coefficient k := C.coefficient_compatible i k

end BeltramiCoefficientTransportCocycle

noncomputable def trivialBeltramiCoefficientTransportCocycle
    (I : Type u) (m : Measure ℂ) :
    BeltramiCoefficientTransportCocycle I where
  measure := fun _ => m
  transition := fun _ _ => id
  transition_measurable := by
    intro i j
    exact measurable_id
  transition_absolutelyContinuous := by
    intro i j
    simpa using (Measure.AbsolutelyContinuous.rfl : m ≪ m)
  coefficient := fun _ => zeroBeltramiCoefficient m
  coefficient_compatible := by
    intro i j
    apply BeltramiCoefficient.ext
    intro z
    rfl
  transition_self := by
    intro i
    rfl
  transition_comp := by
    intro i j k
    funext z
    rfl

@[simp] theorem trivialBeltramiCoefficientTransportCocycle_coefficient
    (I : Type u) (m : Measure ℂ) (i : I) :
    (trivialBeltramiCoefficientTransportCocycle I m).coefficient i =
      zeroBeltramiCoefficient m :=
  rfl

end Teichmuller
