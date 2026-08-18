import Teichmuller.Core

namespace Teichmuller

/-!
This file contains only consequences of the structural core.  It is useful
as a boundary marker: the quotient construction is formalized, while the
analytic existence theorems remain explicit research targets.
-/

theorem marking_relation_is_equivalence (S : Type) [MarkingRelation S] :
    Equivalence (MarkingRelation.related : MarkedRiemannSurface S →
      MarkedRiemannSurface S → Prop) := by
  constructor
  · exact MarkingRelation.refl
  · intro X Y h
    exact MarkingRelation.symm h
  · intro X Y Z hXY hYZ
    exact MarkingRelation.trans hXY hYZ

theorem quotient_respects_marking (S : Type) [MarkingRelation S]
    (X Y : MarkedRiemannSurface S)
    (h : MarkingRelation.related X Y) :
    teichmullerPoint X = teichmullerPoint Y :=
  teichmullerPoint_eq_of_related X Y h

/-!
Research targets, stated rather than asserted:

1. define the analytic predicate in `AnalyticFamily` using holomorphic charts;
2. define the marking relation using biholomorphisms and isotopies;
3. construct a universal family and prove its pullback property;
4. construct turning-piece coordinates and compare them with period and
   Fenchel--Nielsen coordinates.
-/

def researchTargets : List String :=
  [ "holomorphic charts and the measurable Riemann mapping theorem"
  , "isotopy-compatible conformal equivalence"
  , "universal Teichmuller family and its pullback property"
  , "turning-piece coordinates versus period coordinates"
  , "comparison with Fenchel-Nielsen coordinates"
  ]

end Teichmuller
