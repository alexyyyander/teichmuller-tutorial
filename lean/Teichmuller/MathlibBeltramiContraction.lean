import Teichmuller.MathlibBeltrami
import Mathlib.Topology.MetricSpace.Contracting

namespace Teichmuller

open MeasureTheory
open Function
open Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-!
### A conditional contraction scheme for the measurable solution problem

The general measurable Riemann mapping theorem is not reduced to Banach's
fixed-point theorem without an analytic operator construction.  This file
isolates the exact conditional layer that Banach's theorem can discharge once
such an operator has been supplied: a complete state space, a contraction,
and a sound/complete encoding of normalized solutions as fixed points.

The `encode`/`decode` fields are deliberately explicit.  They are the place
where a future Ahlfors--Beurling or other analytic construction must enter;
the existence, convergence, and uniqueness conclusions below are proved from
the contraction hypotheses rather than being hidden in a solution structure.
-/

structure ContractiveBeltramiSolutionScheme
    (m : Measure ℂ) (E : Type*)
    [EMetricSpace E] [CompleteSpace E] where
  coefficient : BeltramiCoefficient m
  operator : E → E
  factor : ℝ≥0
  contraction : ContractingWith factor operator
  seed : E
  seed_finite : edist seed (operator seed) ≠ ∞
  decode : {x : E // IsFixedPt operator x} →
    NormalizedBeltramiHomeomorph coefficient
  encode : NormalizedBeltramiHomeomorph coefficient → E
  encode_fixedPoint : ∀ T, IsFixedPt operator (encode T)
  encode_seed_finite : ∀ T, edist seed (encode T) ≠ ∞
  decode_encode : ∀ T,
    decode ⟨encode T, encode_fixedPoint T⟩ = T

noncomputable def ContractiveBeltramiSolutionScheme.fixedPoint
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) : E :=
  ContractingWith.efixedPoint S.operator S.contraction S.seed S.seed_finite

theorem ContractiveBeltramiSolutionScheme.fixedPoint_isFixedPt
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) :
    IsFixedPt S.operator S.fixedPoint := by
  simpa [ContractiveBeltramiSolutionScheme.fixedPoint] using
    (ContractingWith.efixedPoint_isFixedPt
      S.contraction S.seed_finite)

theorem ContractiveBeltramiSolutionScheme.fixedPoint_iterates_tendsto
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) :
    Tendsto (fun n => S.operator^[n] S.seed) atTop
      (𝓝 S.fixedPoint) := by
  simpa [ContractiveBeltramiSolutionScheme.fixedPoint] using
    (ContractingWith.tendsto_iterate_efixedPoint
      S.contraction S.seed_finite)

theorem ContractiveBeltramiSolutionScheme.fixedPoint_iteration_bound
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) (n : ℕ) :
    edist (S.operator^[n] S.seed) S.fixedPoint ≤
      edist S.seed (S.operator S.seed) * (S.factor : ℝ≥0∞) ^ n /
        (1 - S.factor) := by
  simpa [ContractiveBeltramiSolutionScheme.fixedPoint] using
    (ContractingWith.apriori_edist_iterate_efixedPoint_le
      S.contraction S.seed_finite n)

theorem ContractiveBeltramiSolutionScheme.fixedPoint_eq_encoded
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E)
    (T : NormalizedBeltramiHomeomorph S.coefficient) :
    S.fixedPoint = S.encode T := by
  have hfixed_finite : edist S.fixedPoint S.seed ≠ ∞ := by
    have hlt : edist S.seed S.fixedPoint < ∞ :=
      S.contraction.edist_efixedPoint_lt_top S.seed_finite
    exact ne_of_lt (by simpa [edist_comm] using hlt)
  have hencoded_finite : edist S.fixedPoint (S.encode T) ≠ ∞ := by
    apply ne_of_lt
    calc
      edist S.fixedPoint (S.encode T) ≤
          edist S.fixedPoint S.seed + edist S.seed (S.encode T) :=
        edist_triangle _ _ _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨
        lt_top_iff_ne_top.mpr hfixed_finite,
        lt_top_iff_ne_top.mpr (S.encode_seed_finite T)⟩
  rcases S.contraction.eq_or_edist_eq_top_of_fixedPoints
      S.fixedPoint_isFixedPt (S.encode_fixedPoint T) with h | h
  · exact h
  · exact (hencoded_finite h).elim

noncomputable def ContractiveBeltramiSolutionScheme.normalizedSolution
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) :
    NormalizedBeltramiHomeomorph S.coefficient :=
  S.decode ⟨S.fixedPoint, S.fixedPoint_isFixedPt⟩

theorem ContractiveBeltramiSolutionScheme.normalizedSolution_unique
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E)
    (T : NormalizedBeltramiHomeomorph S.coefficient) :
    T.map = S.normalizedSolution.map := by
  have hdecode :
      S.decode ⟨S.fixedPoint, S.fixedPoint_isFixedPt⟩ = T := by
    have hsub :
        (⟨S.fixedPoint, S.fixedPoint_isFixedPt⟩ :
          {x : E // IsFixedPt S.operator x}) =
        ⟨S.encode T, S.encode_fixedPoint T⟩ := by
      exact Subtype.ext (S.fixedPoint_eq_encoded T)
    rw [hsub, S.decode_encode]
  simpa [ContractiveBeltramiSolutionScheme.normalizedSolution] using
    (congrArg (fun R : NormalizedBeltramiHomeomorph S.coefficient => R.map)
      hdecode).symm

noncomputable def ContractiveBeltramiSolutionScheme.mappingWitness
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) :
    NormalizedBeltramiMappingWitness S.coefficient where
  solution := S.normalizedSolution
  unique := S.normalizedSolution_unique

theorem ContractiveBeltramiSolutionScheme.exists_normalizedSolution
    {m : Measure ℂ} {E : Type*}
    [EMetricSpace E] [CompleteSpace E]
    (S : ContractiveBeltramiSolutionScheme m E) :
    Nonempty (NormalizedBeltramiHomeomorph S.coefficient) :=
  ⟨S.normalizedSolution⟩

end

end Teichmuller
