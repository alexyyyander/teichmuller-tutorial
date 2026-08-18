import Teichmuller.MathlibBeltrami
import Teichmuller.MathlibFamily

namespace Teichmuller

open MeasureTheory

namespace MathlibFormal

universe u w

/-!
### Beltrami data over an actual Mathlib surface family

ParameterContinuousBeltramiFamilyData describes local coordinate data over a
parameter space and adds pointwise parameter-continuity of the coefficient.
The structure below is the first explicit bridge to the existing
ComplexSurfaceFamily.Family: its coordinate domain is embedded as an open
subspace of the family's total space, and the embedding commutes with the
family projection. A later atlas-level structure can strengthen this to a
specified complex chart and impose the full transition cocycle.
-/

structure BeltramiCompatibleFamily
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    (F : ComplexSurfaceFamily.Family S B) (m : Measure ℂ) where
  data : ParameterContinuousBeltramiFamilyData B m
  chartToTotal :
    {p : B × ℂ // p ∈ data.totalDomain} →
      ComplexSurfaceFamily.Total F
  chartToTotal_isOpenEmbedding :
    @Topology.IsOpenEmbedding
      {p : B × ℂ // p ∈ data.totalDomain}
      (ComplexSurfaceFamily.Total F)
      inferInstance F.totalTopology chartToTotal
  projection_commutes :
    ∀ p, ComplexSurfaceFamily.projection F (chartToTotal p) = p.1.1

namespace BeltramiCompatibleFamily

theorem chartToTotal_injective
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : ComplexSurfaceFamily.Family S B} {m : Measure ℂ}
    (G : BeltramiCompatibleFamily F m) :
    Function.Injective G.chartToTotal := by
  letI : TopologicalSpace (ComplexSurfaceFamily.Total F) := F.totalTopology
  exact G.chartToTotal_isOpenEmbedding.injective

theorem projection_commutes'
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : ComplexSurfaceFamily.Family S B} {m : Measure ℂ}
    (G : BeltramiCompatibleFamily F m)
    (p : {q : B × ℂ // q ∈ G.data.totalDomain}) :
    ComplexSurfaceFamily.projection F (G.chartToTotal p) = p.1.1 :=
  G.projection_commutes p

theorem range_isOpen
    {S : Type u} {B : Type w}
    [TopologicalSpace S] [TopologicalSpace B]
    {F : ComplexSurfaceFamily.Family S B} {m : Measure ℂ}
    (G : BeltramiCompatibleFamily F m) :
    @IsOpen
      (ComplexSurfaceFamily.Total F) F.totalTopology
      (Set.range G.chartToTotal) := by
  letI : TopologicalSpace (ComplexSurfaceFamily.Total F) := F.totalTopology
  exact G.chartToTotal_isOpenEmbedding.isOpen_range

end BeltramiCompatibleFamily

end MathlibFormal

end Teichmuller
