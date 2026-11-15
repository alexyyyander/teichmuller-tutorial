import Teichmuller.MathlibBeltramiNeumannOperatorFamily
import Teichmuller.MathlibBeltramiFamily

namespace Teichmuller

open MeasureTheory
open Filter Function
open scoped NNReal Topology

noncomputable section

/-!
### From a continuous Neumann state to a Beltrami family

NeumannOperatorFamily.continuous_solution controls the fixed-point state in
the complete normed space E.  It does not, by itself, say how a state is
decoded into a map on ℂ.  The two structures below isolate that remaining
analytic input instead of silently identifying a Banach state with a
homeomorphism.

The forward bridge assumes a continuous evaluation map
E × ℂ → ℂ and proves the joint continuity field required by
PointwiseNormalizedBeltramiFamilyWitness.  The inverse bridge is the exact
same construction for the inverse-coordinate evaluation and produces the
NormalizedBeltramiInverseContinuityWitness needed by the local total-space
chart constructor.

Neither structure identifies the evaluation map with the Beurling transform,
nor proves the measurable Riemann mapping theorem.  Those identifications
remain separate analytic inputs.
-/

structure NeumannBeltramiEvaluationBridge
    {B E : Type*}
    [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : NeumannOperatorFamily B E) (m : Measure ℂ) where
  coefficient : B → BeltramiCoefficient m
  coefficient_parameter_continuous :
    ∀ z : ℂ, Continuous (fun b => coefficient b z)
  solution : ∀ b, PointwiseNormalizedBeltramiHomeomorph (coefficient b)
  evaluation : E → ℂ → ℂ
  evaluation_continuous :
    Continuous (fun p : E × ℂ => evaluation p.1 p.2)
  solution_map_eq :
    ∀ b z, (solution b).map z = evaluation (F.solution b) z

namespace NeumannBeltramiEvaluationBridge

variable {B E : Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : NeumannOperatorFamily B E} {m : Measure ℂ}

noncomputable def toPointwiseNormalizedBeltramiFamilyWitness
    (W : NeumannBeltramiEvaluationBridge F m) :
    PointwiseNormalizedBeltramiFamilyWitness B m where
  coefficient := W.coefficient
  coefficient_parameter_continuous := W.coefficient_parameter_continuous
  solution := W.solution
  solution_totalMap_continuous := by
    have hstate :
        Continuous (fun p : B × ℂ => (F.solution p.1, p.2)) :=
      (F.continuous_solution.comp continuous_fst).prodMk continuous_snd
    have hevaluation :
        Continuous (fun p : B × ℂ => W.evaluation (F.solution p.1) p.2) := by
      exact W.evaluation_continuous.comp hstate
    apply hevaluation.congr
    intro p
    exact (W.solution_map_eq p.1 p.2).symm

theorem toPointwiseNormalizedBeltramiFamilyWitness_solution_totalMap_continuous
    (W : NeumannBeltramiEvaluationBridge F m) :
    Continuous (fun p : B × ℂ =>
      (W.toPointwiseNormalizedBeltramiFamilyWitness.solution p.1).map p.2) :=
  W.toPointwiseNormalizedBeltramiFamilyWitness.solution_totalMap_continuous

noncomputable def toAENormalizedBeltramiFamilyWitness
    (W : NeumannBeltramiEvaluationBridge F m) :
    AENormalizedBeltramiFamilyWitness B m :=
  W.toPointwiseNormalizedBeltramiFamilyWitness
    |>.toAENormalizedBeltramiFamilyWitness

end NeumannBeltramiEvaluationBridge

structure NeumannBeltramiInverseEvaluationBridge
    {B E : Type*}
    [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {m : Measure ℂ} {anchor : ℂ}
  (M : NormalizedBeltramiParameterModel B m anchor)
    (F : NeumannOperatorFamily B E) where
  inverseEvaluation : E → ℂ → ℂ
  inverseEvaluation_continuous :
    Continuous (fun p : E × ℂ => inverseEvaluation p.1 p.2)
  solution_inverse_eq :
    ∀ b z, (M.solution b).map.symm z =
      inverseEvaluation (F.solution b) z

namespace NeumannBeltramiInverseEvaluationBridge

variable {B E : Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {m : Measure ℂ} {anchor : ℂ}
  {M : NormalizedBeltramiParameterModel B m anchor}
  {F : NeumannOperatorFamily B E}

noncomputable def toInverseContinuityWitness
  (W : NeumannBeltramiInverseEvaluationBridge M F) :
    MathlibFormal.NormalizedBeltramiInverseContinuityWitness M where
  solution_inverse_totalMap_continuous := by
    have hstate :
        Continuous (fun p : B × ℂ => (F.solution p.1, p.2)) :=
      (F.continuous_solution.comp continuous_fst).prodMk continuous_snd
    have hevaluation :
        Continuous (fun p : B × ℂ =>
          W.inverseEvaluation (F.solution p.1) p.2) := by
      exact W.inverseEvaluation_continuous.comp hstate
    apply hevaluation.congr
    intro p
    exact (W.solution_inverse_eq p.1 p.2).symm

theorem toInverseContinuityWitness_solution_inverse_totalMap_continuous
    (W : NeumannBeltramiInverseEvaluationBridge M F) :
    Continuous (fun p : B × ℂ => (M.solution p.1).map.symm p.2) :=
  W.toInverseContinuityWitness.solution_inverse_totalMap_continuous

end NeumannBeltramiInverseEvaluationBridge

end

end Teichmuller
