import Teichmuller.MathlibBeltrami
import Teichmuller.MathlibBeltramiDifferential
import Teichmuller.MathlibFamily
import Teichmuller.MathlibFiberBundle

namespace Teichmuller

open MeasureTheory

/-!
### A parameter-model interface for normalized Beltrami solutions

`PointwiseNormalizedBeltramiFamilyWitness` records a family of solutions and
their parameter continuity.  The structure below adds the two pieces needed
before such a family can serve as a genuine local parameter model: the
coefficient recovered from the real differential is the original coefficient,
and evaluation at one anchor coordinate separates parameters.  The latter is
kept as an explicit field because it is geometric input, not a consequence of
continuity alone.
-/

structure NormalizedBeltramiParameterModel
    (B : Type*) [TopologicalSpace B] (m : Measure ℂ) (anchor : ℂ)
    extends PointwiseNormalizedBeltramiFamilyWitness B m where
  recovered_coefficient :
    ∀ b z, fderivBeltramiCoefficient (solution b).map z = coefficient b z
  coefficient_parameter_injective :
    Function.Injective (fun b => coefficient b anchor)

namespace NormalizedBeltramiParameterModel

def parameterMap
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) : B → ℂ :=
  fun b => M.coefficient b anchor

noncomputable def toParameterContinuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    ParameterContinuousBeltramiFamilyData B m :=
  M.toPointwiseNormalizedBeltramiFamilyWitness.toParameterContinuous

@[simp] theorem parameterMap_apply
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) :
    M.parameterMap b = M.coefficient b anchor :=
  rfl

theorem parameterMap_continuous
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    Continuous M.parameterMap := by
  exact M.coefficient_parameter_continuous anchor

theorem parameterMap_injective
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    Function.Injective M.parameterMap := by
  exact M.coefficient_parameter_injective

theorem recovered_coefficient_at
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) (z : ℂ) :
    fderivBeltramiCoefficient (M.solution b).map z = M.coefficient b z :=
  M.recovered_coefficient b z

/-! The anchored equality relation is the first quotient one can form from a
    parameter model.  Because `parameterMap` is required to be injective, this
    quotient is provably harmless: it is equivalent to the original parameter
    space.  Keeping the quotient explicit records the distinction between this
    coefficient-level identification and the later marking quotient in
    Teichmuller theory. -/

def parameterSetoid
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) : Setoid B where
  r := fun b₁ b₂ => M.parameterMap b₁ = M.parameterMap b₂
  iseqv := {
    refl := fun b => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

def parameterQuotient
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) : Type _ :=
  Quotient M.parameterSetoid

noncomputable def parameterQuotientMap
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    M.parameterQuotient → ℂ :=
  Quotient.lift M.parameterMap (by
    intro b₁ b₂ h
    exact h)

@[simp] theorem parameterQuotientMap_mk
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) :
    M.parameterQuotientMap (Quotient.mk'' b) = M.parameterMap b :=
  rfl

theorem parameterQuotientMap_injective
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    Function.Injective M.parameterQuotientMap := by
  intro q₁ q₂ h
  refine Quotient.inductionOn q₁ ?_ q₂ h
  intro b₁ q₂ h
  refine Quotient.inductionOn q₂ ?_ h
  intro b₂ h
  apply Quotient.sound
  exact h

noncomputable def parameterQuotientEquiv
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    B ≃ M.parameterQuotient where
  toFun := Quotient.mk''
  invFun := Quotient.lift id (by
    intro b₁ b₂ h
    exact M.parameterMap_injective h)
  left_inv := by
    intro b
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro b
    rfl

theorem parameterSetoid_eq_iff
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b₁ b₂ : B) :
    @Setoid.r B M.parameterSetoid b₁ b₂ ↔ b₁ = b₂ := by
  constructor
  · intro h
    exact M.parameterMap_injective h
  · intro h
    cases h
    rfl

/-! Reparametrization preserves the full pointwise solution data when the new
    parameter map is continuous and injective.  The injectivity hypothesis is
    essential: without it, the result is a family but not a parameter model in
    the sense fixed above. -/

def reparametrize
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor)
    (g : C → B) (hg : Continuous g) (hgi : Function.Injective g) :
    NormalizedBeltramiParameterModel C m anchor where
  toPointwiseNormalizedBeltramiFamilyWitness := {
    coefficient := fun c => M.coefficient (g c)
    coefficient_parameter_continuous := by
      intro z
      exact (M.coefficient_parameter_continuous z).comp hg
    solution := fun c => M.solution (g c)
    solution_totalMap_continuous := by
      have hpair : Continuous (fun p : C × ℂ => (g p.1, p.2)) :=
        (hg.comp continuous_fst).prodMk continuous_snd
      exact M.solution_totalMap_continuous.comp hpair }
  recovered_coefficient := by
    intro c z
    exact M.recovered_coefficient (g c) z
  coefficient_parameter_injective := by
    intro c₁ c₂ h
    apply hgi
    apply M.parameterMap_injective
    exact h

end NormalizedBeltramiParameterModel

/-! A coefficient-level classification witness.  Its map goes from the test
    parameter space into the proposed universal parameter space and requires
    equality of the complete coefficient functions, not merely equality at the
    anchor.  The anchor injectivity then proves uniqueness of the classifying
    map.  This is deliberately weaker than a holomorphic family classification:
    no fibrewise biholomorphism or joint holomorphic variation is inferred here.
-/

structure NormalizedBeltramiParameterClassification
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {m : Measure ℂ} {anchor : ℂ}
    (U : NormalizedBeltramiParameterModel B m anchor)
    (F : NormalizedBeltramiParameterModel C m anchor) where
  map : C → B
  map_continuous : Continuous map
  coefficient_compat :
    ∀ c z, F.coefficient c z = U.coefficient (map c) z

namespace NormalizedBeltramiParameterClassification

def refl
    {B : Type*} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (U : NormalizedBeltramiParameterModel B m anchor) :
    NormalizedBeltramiParameterClassification U U where
  map := id
  map_continuous := continuous_id
  coefficient_compat := by
    intro b z
    rfl

def trans
    {B C D : Type*}
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    {m : Measure ℂ} {anchor : ℂ}
    {U : NormalizedBeltramiParameterModel B m anchor}
    {F : NormalizedBeltramiParameterModel C m anchor}
    {G : NormalizedBeltramiParameterModel D m anchor}
    (c₁ : NormalizedBeltramiParameterClassification U F)
    (c₂ : NormalizedBeltramiParameterClassification F G) :
    NormalizedBeltramiParameterClassification U G where
  map := fun d => c₁.map (c₂.map d)
  map_continuous := c₁.map_continuous.comp c₂.map_continuous
  coefficient_compat := by
    intro d z
    rw [c₂.coefficient_compat d z, c₁.coefficient_compat (c₂.map d) z]

@[simp] theorem trans_map
    {B C D : Type*}
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    {m : Measure ℂ} {anchor : ℂ}
    {U : NormalizedBeltramiParameterModel B m anchor}
    {F : NormalizedBeltramiParameterModel C m anchor}
    {G : NormalizedBeltramiParameterModel D m anchor}
    (c₁ : NormalizedBeltramiParameterClassification U F)
    (c₂ : NormalizedBeltramiParameterClassification F G) :
    (c₁.trans c₂).map = fun d => c₁.map (c₂.map d) :=
  rfl

theorem map_unique
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {m : Measure ℂ} {anchor : ℂ}
    {U : NormalizedBeltramiParameterModel B m anchor}
    {F : NormalizedBeltramiParameterModel C m anchor}
    (c₁ c₂ : NormalizedBeltramiParameterClassification U F) :
    c₁.map = c₂.map := by
  funext c
  apply U.parameterMap_injective
  calc
    U.parameterMap (c₁.map c) = U.coefficient (c₁.map c) anchor := rfl
    _ = F.coefficient c anchor := (c₁.coefficient_compat c anchor).symm
    _ = U.coefficient (c₂.map c) anchor := c₂.coefficient_compat c anchor
    _ = U.parameterMap (c₂.map c) := rfl

end NormalizedBeltramiParameterClassification

def NormalizedBeltramiParameterModel.reparametrizeClassification
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor)
    (g : C → B) (hg : Continuous g) (hgi : Function.Injective g) :
    NormalizedBeltramiParameterClassification M
      (M.reparametrize g hg hgi) where
  map := g
  map_continuous := hg
  coefficient_compat := by
    intro c z
    rfl

namespace MathlibFormal

/-! A solution map can be made holomorphic by transporting the one-chart
    complex structure along its inverse.  The marking is the solution itself,
    so the resulting marked surface remembers the original normalized map. -/

noncomputable def beltramiSolutionChart (e : ℂ ≃ₜ ℂ) : ComplexChart ℂ where
  domain := Set.univ
  range := Set.univ
  domain_open := isOpen_univ
  range_open := isOpen_univ
  toComplex := e.symm
  fromComplex := e
  maps_into := by
    intro z _
    trivial
  inverse_into := by
    intro z _
    trivial
  left_inv := by
    intro z _
    simpa using e.symm_apply_apply z
  right_inv := by
    intro z _
    simpa using e.apply_symm_apply z
  continuous_toComplex := e.symm.continuous.continuousOn
  continuous_fromComplex := e.continuous.continuousOn

noncomputable def beltramiSolutionAtlas (e : ℂ ≃ₜ ℂ) : ComplexAtlas ℂ where
  index := PUnit
  chart := fun _ => beltramiSolutionChart e
  covers := by
    intro z
    exact ⟨PUnit.unit, Set.mem_univ z⟩
  transition_holomorphic := by
    intro i j
    cases i
    cases j
    have hfun :
        ComplexChart.transitionMap (beltramiSolutionChart e)
          (beltramiSolutionChart e) = id := by
      funext z
      simp [ComplexChart.transitionMap, beltramiSolutionChart]
    have hset :
        ComplexChart.overlap (beltramiSolutionChart e)
          (beltramiSolutionChart e) = (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexChart.overlap, beltramiSolutionChart]
    rw [hfun, hset]
    exact differentiableOn_id

theorem beltramiSolutionAtlas_holomorphic (e : ℂ ≃ₜ ℂ) :
    @AtlasHolomorphicEquiv ℂ ℂ inferInstance inferInstance
      complexPlaneAtlas (beltramiSolutionAtlas e) e := by
  refine { forward := ?_, inverse := ?_ }
  · refine ⟨?_⟩
    intro i j
    cases i
    cases j
    have hfun :
        ComplexAtlas.chartMap complexPlaneAtlas
            (beltramiSolutionAtlas e) e PUnit.unit PUnit.unit = id := by
      funext z
      simp [ComplexAtlas.chartMap, beltramiSolutionAtlas,
        beltramiSolutionChart, complexPlaneAtlas, complexPlaneChart]
    have hset :
        ComplexAtlas.chartMapDomain complexPlaneAtlas
            (beltramiSolutionAtlas e) e PUnit.unit PUnit.unit =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexAtlas.chartMapDomain, beltramiSolutionAtlas,
        beltramiSolutionChart, complexPlaneAtlas, complexPlaneChart]
    rw [hfun, hset]
    exact differentiableOn_id
  · refine ⟨?_⟩
    intro i j
    cases i
    cases j
    have hfun :
        ComplexAtlas.chartMap (beltramiSolutionAtlas e)
            complexPlaneAtlas e.symm PUnit.unit PUnit.unit = id := by
      funext z
      simp [ComplexAtlas.chartMap, beltramiSolutionAtlas,
        beltramiSolutionChart, complexPlaneAtlas, complexPlaneChart]
    have hset :
        ComplexAtlas.chartMapDomain (beltramiSolutionAtlas e)
            complexPlaneAtlas e.symm PUnit.unit PUnit.unit =
          (Set.univ : Set ℂ) := by
      ext z
      simp [ComplexAtlas.chartMapDomain, beltramiSolutionAtlas,
        beltramiSolutionChart, complexPlaneAtlas, complexPlaneChart]
    rw [hfun, hset]
    exact differentiableOn_id

noncomputable def normalizedBeltramiMarkedSurface
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) :
    MarkedComplexRiemannSurface ℂ where
  carrier := ℂ
  topology := inferInstance
  surface := { atlas := beltramiSolutionAtlas (M.solution b).map }
  marking := (M.solution b).map

universe u w

/-! The fibrewise transport above assembles into the existing family interface.
    Its total topology is deliberately the constant-plane topology: this makes
    the projection continuous, while `analyticVariation` remains an explicit
    proposition rather than an unproved claim of joint holomorphicity. -/

noncomputable def NormalizedBeltramiParameterModel.toMarkedSurfaceFamily
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    ComplexSurfaceFamily.Family ℂ B where
  fiber := normalizedBeltramiMarkedSurface M
  totalTopology :=
    (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology
  projection_continuous := by
    change @Continuous
      (Sigma fun _ : B => ℂ) B
      (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology
      inferInstance (fun z => z.1)
    exact (ComplexSurfaceFamily.constantComplexPlaneFamily B).projection_continuous
  analyticVariation := True

@[simp] theorem NormalizedBeltramiParameterModel.toMarkedSurfaceFamily_fiber
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) :
    (NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b =
      normalizedBeltramiMarkedSurface M b :=
  rfl

/-! The solution itself is now a fibrewise biholomorphism from the constant
    marked plane to the transported marked surface family. -/

noncomputable def NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyEquiv
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    HolomorphicFiberwiseEquiv
      (ComplexSurfaceFamily.constantComplexPlaneFamily B)
      (NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M) where
  map := fun b => (M.solution b).map
  holomorphic := by
    intro b
    exact beltramiSolutionAtlas_holomorphic (M.solution b).map
  marking_commutes := by
    intro b s
    rfl

@[simp] theorem NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyEquiv_map
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) (b : B) :
    (NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyEquiv M).map b =
      (M.solution b).map :=
  rfl

/-! Since the family already carries the transported fibres over `B`, the
    induced classification over the constant plane has the identity base map.
    This is the first formal point where coefficient data reaches the marked
    family interface; the missing joint two-dimensional atlas is intentionally
    not hidden in this definition. -/

noncomputable def NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyClassification
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    HolomorphicFamilyClassification
      (NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M)
      (ComplexSurfaceFamily.constantComplexPlaneFamily B) where
  map := id
  map_continuous := continuous_id
  realization := {
    map := fun b => (M.solution b).map
    holomorphic := by
      intro b
      exact beltramiSolutionAtlas_holomorphic (M.solution b).map
    marking_commutes := by
      intro b s
      rfl }

@[simp] theorem NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyClassification_map
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    (NormalizedBeltramiParameterModel.toMarkedSurfaceFamilyClassification M).map = id :=
  rfl

/-! The constant-plane topology already supplies a genuine topological bundle
    witness.  This upgrades the legacy `Family` placeholder to the
    data-carrying `AnalyticFamily` interface: the fibre maps are the original
    normalized solutions and their chartwise holomorphicity is proved above. -/

noncomputable def NormalizedBeltramiParameterModel.toAnalyticFamily
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    ComplexSurfaceFamily.AnalyticFamily ℂ B where
  family := NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M
  variation := {
    topology := {
      model := ℂ
      modelTopology := inferInstance
      modelNonempty := ⟨0⟩
      modelHomeomorph := fun b => (M.solution b).map
      bundleTopology :=
        @Bundle.Trivial.topologicalSpace B ℂ inferInstance inferInstance
      totalSpaceHomeomorph := by
        exact ComplexSurfaceFamily.constantComplexPlaneTotalHomeomorph B
      bundle := by
        exact Bundle.Trivial.fiberBundle B ℂ }
    modelSurface := complexPlane
    fiberHolomorphic := by
      intro b
      exact beltramiSolutionAtlas_holomorphic (M.solution b).map }

/-! Over an arbitrary topological base, any chosen complex base chart now gets
    a local jointly holomorphic coordinate.  In the transported fibre chart
    the solution and its inverse cancel, so the joint coordinate is simply the
    second coordinate.  The stronger total-space chart witness remains a
    separate step because it also needs continuity of the inverse solution
    family. -/

noncomputable def NormalizedBeltramiParameterModel.toLocalJointlyHolomorphicFamily
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor)
    (C : ComplexSurfaceFamily.ComplexBaseChart B) :
    ComplexSurfaceFamily.LocalJointlyHolomorphicFamily ℂ
      (NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M) C where
  fiberEquiv := fun b _ => (M.solution b).map
  chartIndex := fun b hb => by
    letI : TopologicalSpace
        ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).carrier :=
      ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).topology
    exact PUnit.unit
  jointCoordinate := fun p => p.2
  jointCoordinate_eq_chart := by
    intro b hb z
    letI : TopologicalSpace
        ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).carrier :=
      ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).topology
    change z = (M.solution b).map.symm ((M.solution b).map z)
    simp
  jointlyHolomorphic := by
    simpa using
      (differentiable_snd : Differentiable ℂ (fun p : ℂ × ℂ => p.2))

/-! When the parameter space itself is `ℂ`, the local statement packages into
    the global base-coordinate interface.  The coordinate is still the second
    projection; the parameter dependence is carried by the transported fibre
    atlas and the separate topological bundle witness. -/

noncomputable def NormalizedBeltramiParameterModel.toJointlyHolomorphicFamily
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel ℂ m anchor) :
    ComplexSurfaceFamily.JointlyHolomorphicFamily ℂ
      (NormalizedBeltramiParameterModel.toAnalyticFamily M) where
  fiberEquiv := fun b => (M.solution b).map
  chartIndex := fun b => by
    letI : TopologicalSpace
        ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).carrier :=
      ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).topology
    exact PUnit.unit
  jointCoordinate := fun p => p.2
  jointCoordinate_eq_chart := by
    intro b z
    letI : TopologicalSpace
        ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).carrier :=
      ((NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M).fiber b).topology
    change z = (M.solution b).map.symm ((M.solution b).map z)
    simp
  jointlyHolomorphic := by
    simpa using
      (differentiable_snd : Differentiable ℂ (fun p : ℂ × ℂ => p.2))

/-! The missing topological ingredient for a genuine two-dimensional chart is
    now isolated as a named hypothesis: joint continuity of the inverse
    normalized solutions.  This is weaker than asserting any new analytic
    theorem, but strong enough to construct the local total-space
    homeomorphism required by `LocalJointlyHolomorphicChartWitness`. -/

structure NormalizedBeltramiInverseContinuityWitness
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) where
  solution_inverse_totalMap_continuous :
    Continuous (fun p : B × ℂ => (M.solution p.1).map.symm p.2)

noncomputable def NormalizedBeltramiParameterModel.toLocalJointlyHolomorphicChartWitness
    {B : Type*} [TopologicalSpace B]
    {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor)
    (W : NormalizedBeltramiInverseContinuityWitness M)
    (C : ComplexSurfaceFamily.ComplexBaseChart B) :
    ComplexSurfaceFamily.LocalJointlyHolomorphicChartWitness
      (NormalizedBeltramiParameterModel.toLocalJointlyHolomorphicFamily M C) := by
  let F := NormalizedBeltramiParameterModel.toMarkedSurfaceFamily M
  let J := NormalizedBeltramiParameterModel.toLocalJointlyHolomorphicFamily M C
  let localTrivialization :
      @Homeomorph
        (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
        (ComplexSurfaceFamily.LocalBaseTotal F C)
        inferInstance
        (ComplexSurfaceFamily.localBaseTotalTopology F C) := by
    letI : TopologicalSpace
        (ComplexSurfaceFamily.LocalBaseTotal F C) :=
      ComplexSurfaceFamily.localBaseTotalTopology F C
    let H0 := ComplexSurfaceFamily.constantComplexPlaneTotalHomeomorph B
    let K := Bundle.Trivial.homeomorphProd B ℂ
    have htopology : F.totalTopology =
        TopologicalSpace.induced
          (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
          (@Bundle.Trivial.topologicalSpace B
            complexPlaneMarkedSurface.carrier inferInstance
            complexPlaneMarkedSurface.topology) := by
      rfl
    refine
      { toFun := fun p =>
          ⟨p.1, (M.solution p.1.1).map p.2⟩
        invFun := fun x =>
          (x.1, (M.solution x.1.1).map.symm x.2)
        left_inv := by
          intro p
          apply Prod.ext
          · rfl
          · simp
        right_inv := by
          intro x
          cases x with
          | mk b z =>
            apply Sigma.ext
            · rfl
            · simp
        continuous_toFun := by
          apply continuous_induced_rng.mpr
          have hbase : Continuous
              (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                (p.1.1 : B)) :=
            continuous_subtype_val.comp continuous_fst
          have hsolution : Continuous
              (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                (M.solution p.1.1).map p.2) := by
            simpa [Function.comp_def] using
              M.solution_totalMap_continuous.comp
                (hbase.prodMk continuous_snd)
          have hproduct : Continuous
              (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                ((p.1.1 : B), (M.solution p.1.1).map p.2)) :=
            hbase.prodMk hsolution
          have hKinv : @Continuous
              (B × ℂ)
              (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
              inferInstance
              (@Bundle.Trivial.topologicalSpace B
                complexPlaneMarkedSurface.carrier inferInstance
                complexPlaneMarkedSurface.topology)
              K.invFun := by
            exact K.continuous_invFun
          have hH0inv : @Continuous
              (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
              (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
              (@Bundle.Trivial.topologicalSpace B
                complexPlaneMarkedSurface.carrier inferInstance
                complexPlaneMarkedSurface.topology)
              (TopologicalSpace.induced
                (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology))
              H0.invFun := by
            letI : TopologicalSpace
                (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) :=
              TopologicalSpace.induced
                (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
            letI : TopologicalSpace
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier)) :=
              @Bundle.Trivial.topologicalSpace B
                complexPlaneMarkedSurface.carrier inferInstance
                complexPlaneMarkedSurface.topology
            exact H0.continuous_invFun
          have hglobal : @Continuous
              (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
              (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
              inferInstance
              (TopologicalSpace.induced
                (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology))
              (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                H0.invFun (K.invFun
                  ((p.1.1 : B), (M.solution p.1.1).map p.2))) :=
            by
              have hinner : @Continuous
                  (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
                  (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                    (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                  inferInstance
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology)
                  (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                    K.invFun ((p.1.1 : B), (M.solution p.1.1).map p.2)) := by
                exact @Continuous.comp
                  (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
                  (B × ℂ)
                  (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                    (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                  inferInstance inferInstance
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology)
                  (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                    ((p.1.1 : B), (M.solution p.1.1).map p.2))
                  K.invFun hKinv hproduct
              exact @Continuous.comp
                (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
                inferInstance
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
                (TopologicalSpace.induced
                  (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology))
                (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                  K.invFun ((p.1.1 : B), (M.solution p.1.1).map p.2))
                H0.invFun hH0inv hinner
          rw [htopology]
          change @Continuous
              (ComplexSurfaceFamily.BaseChartDomain C × ℂ)
              (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
              inferInstance
              (TopologicalSpace.induced
                (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology))
              (fun p : ComplexSurfaceFamily.BaseChartDomain C × ℂ =>
                ComplexSurfaceFamily.localBaseTotalMap F C
                  ⟨p.1, (M.solution p.1.1).map p.2⟩)
          convert hglobal using 1
        continuous_invFun := by
          have hlocal : @Continuous
              (ComplexSurfaceFamily.LocalBaseTotal F C)
              (ComplexSurfaceFamily.Total F)
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              F.totalTopology
              (ComplexSurfaceFamily.localBaseTotalMap F C) :=
            continuous_induced_dom
          have hglobal : @Continuous
              (ComplexSurfaceFamily.LocalBaseTotal F C)
              (B × ℂ)
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              inferInstance
              (fun x => K.toFun (H0.toFun
                (ComplexSurfaceFamily.localBaseTotalMap F C x))) := by
            have hH0to : @Continuous
                (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                (TopologicalSpace.induced
                  (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology))
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
                H0.toFun := by
              letI : TopologicalSpace
                  (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) :=
                TopologicalSpace.induced
                  (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology)
              letI : TopologicalSpace
                  (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                    (Bundle.Trivial B complexPlaneMarkedSurface.carrier)) :=
                @Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology
              exact H0.continuous_toFun
            have hKto : @Continuous
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                (B × ℂ)
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
                inferInstance K.toFun := by
              exact K.continuous_toFun
            have hlocal' : @Continuous
                (ComplexSurfaceFamily.LocalBaseTotal F C)
                (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
                (ComplexSurfaceFamily.localBaseTotalTopology F C)
                (TopologicalSpace.induced
                  (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology))
                (ComplexSurfaceFamily.localBaseTotalMap F C) := by
              rw [← htopology]
              exact hlocal
            have hinner : @Continuous
                (ComplexSurfaceFamily.LocalBaseTotal F C)
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                (ComplexSurfaceFamily.localBaseTotalTopology F C)
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
                (fun x => H0.toFun
                  (ComplexSurfaceFamily.localBaseTotalMap F C x)) := by
              exact @Continuous.comp
                (ComplexSurfaceFamily.LocalBaseTotal F C)
                (Sigma fun _ : B => complexPlaneMarkedSurface.carrier)
                (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                  (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
                (ComplexSurfaceFamily.localBaseTotalTopology F C)
                (TopologicalSpace.induced
                  (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
                  (@Bundle.Trivial.topologicalSpace B
                    complexPlaneMarkedSurface.carrier inferInstance
                    complexPlaneMarkedSurface.topology))
                (@Bundle.Trivial.topologicalSpace B
                  complexPlaneMarkedSurface.carrier inferInstance
                  complexPlaneMarkedSurface.topology)
                (ComplexSurfaceFamily.localBaseTotalMap F C)
                H0.toFun hH0to hlocal'
            exact @Continuous.comp
              (ComplexSurfaceFamily.LocalBaseTotal F C)
              (Bundle.TotalSpace complexPlaneMarkedSurface.carrier
                (Bundle.Trivial B complexPlaneMarkedSurface.carrier))
              (B × ℂ)
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              (@Bundle.Trivial.topologicalSpace B
                complexPlaneMarkedSurface.carrier inferInstance
                complexPlaneMarkedSurface.topology)
              inferInstance
              (fun x => H0.toFun
                (ComplexSurfaceFamily.localBaseTotalMap F C x))
              K.toFun hKto hinner
          have hbase : @Continuous
              (ComplexSurfaceFamily.LocalBaseTotal F C) B
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              inferInstance
              (fun x => (x.1.1 : B)) := by
            convert hglobal.fst using 1
          have hcoordinate : @Continuous
              (ComplexSurfaceFamily.LocalBaseTotal F C) ℂ
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              inferInstance
              (fun x => x.2) := by
            convert hglobal.snd using 1
          have hback : Continuous
              (fun x : ComplexSurfaceFamily.LocalBaseTotal F C =>
                (M.solution x.1.1).map.symm x.2) := by
            have hpair : Continuous
                (fun x : ComplexSurfaceFamily.LocalBaseTotal F C =>
                  ((x.1.1 : B), x.2)) :=
              hbase.prodMk hcoordinate
            exact W.solution_inverse_totalMap_continuous.comp hpair
          have hbase' : @Continuous
              (ComplexSurfaceFamily.LocalBaseTotal F C)
              (ComplexSurfaceFamily.BaseChartDomain C)
              (ComplexSurfaceFamily.localBaseTotalTopology F C)
              inferInstance
              (fun x => x.1) := by
            apply Continuous.subtype_mk
            exact hbase
          exact hbase'.prodMk hback }
  let hprod :
      {p : ℂ × ℂ // p ∈ C.range ×ˢ (Set.univ : Set ℂ)} ≃ₜ
        ComplexSurfaceFamily.BaseChartDomain C × ℂ :=
    (Homeomorph.Set.prod C.range (Set.univ : Set ℂ)).trans
      (C.chart.symm.prodCongr (Homeomorph.Set.univ ℂ))
  refine
    { localTrivialization := localTrivialization
      localTrivialization_apply := by
        intro p
        rfl
      range := C.range ×ˢ (Set.univ : Set ℂ)
      range_open := C.range_open.prod isOpen_univ
      jointChart := hprod.symm
      jointChart_apply := by
        intro p
        change (C.coordinateOn p.1, p.2) =
          (C.coordinateOn p.1,
            J.jointCoordinate (C.coordinateOn p.1, p.2))
        rfl }

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

/-!
The constant plane gives a fully explicit total-space target for a parameter
model.  The source is the subtype of the product chart domain; the
homeomorphism below makes the identification with the dependent-sum total
space visible rather than relying on a definitional equality of topologies.
-/

noncomputable def constantPlaneParameterChartHomeomorph
    (B : Type w) [TopologicalSpace B] :
    @Homeomorph
      {p : B × ℂ // p ∈ Set.univ}
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.constantComplexPlaneFamily B))
      inferInstance
      (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology := by
  let e₁ : @Homeomorph
      {p : B × ℂ // p ∈ Set.univ} (B × ℂ)
      inferInstance inferInstance :=
    Homeomorph.Set.univ (B × ℂ)
  letI : TopologicalSpace
      (Sigma fun _ : B => complexPlaneMarkedSurface.carrier) :=
    TopologicalSpace.induced
      (ComplexSurfaceFamily.constantComplexPlaneTotalEquiv B).toFun
      (@Bundle.Trivial.topologicalSpace B
        complexPlaneMarkedSurface.carrier inferInstance
        complexPlaneMarkedSurface.topology)
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.constantComplexPlaneFamily B)) :=
    (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology
  let h := ComplexSurfaceFamily.constantComplexPlaneTotalHomeomorph B
  let g := Bundle.Trivial.homeomorphProd B ℂ
  let e₂ : @Homeomorph
      (B × ℂ)
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.constantComplexPlaneFamily B))
      inferInstance
      (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology := by
    refine
      { toFun := fun p => h.invFun (g.invFun p)
        invFun := fun z => g.toFun (h.toFun z)
        left_inv := ?_
        right_inv := ?_
        continuous_toFun := ?_
        continuous_invFun := ?_ }
    · intro p
      simp [h, g]
    · intro z
      change h.invFun (g.invFun (g.toFun (h.toFun z))) = z
      rw [g.left_inv]
      exact h.left_inv z
    · exact h.continuous_invFun.comp g.continuous_invFun
    · exact g.continuous_toFun.comp h.continuous_toFun
  exact e₁.trans e₂

@[simp] theorem constantPlaneParameterChartHomeomorph_apply
    (B : Type w) [TopologicalSpace B]
    (p : {q : B × ℂ // q ∈ Set.univ}) :
    constantPlaneParameterChartHomeomorph B p =
      (⟨p.1.1, p.1.2⟩ :
        ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.constantComplexPlaneFamily B)) := by
  rfl

noncomputable def NormalizedBeltramiParameterModel.toConstantPlaneCompatibleFamily
    {B : Type w} [TopologicalSpace B] {m : Measure ℂ} {anchor : ℂ}
    (M : NormalizedBeltramiParameterModel B m anchor) :
    BeltramiCompatibleFamily
      (ComplexSurfaceFamily.constantComplexPlaneFamily B) m where
  data := M.toParameterContinuous
  chartToTotal := constantPlaneParameterChartHomeomorph B
  chartToTotal_isOpenEmbedding := by
    letI : TopologicalSpace
        (ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.constantComplexPlaneFamily B)) :=
      (ComplexSurfaceFamily.constantComplexPlaneFamily B).totalTopology
    exact (constantPlaneParameterChartHomeomorph B).isOpenEmbedding
  projection_commutes := by
    intro p
    change (constantPlaneParameterChartHomeomorph B p).1 = p.1.1
    simp [constantPlaneParameterChartHomeomorph,
      ComplexSurfaceFamily.constantComplexPlaneTotalHomeomorph,
      ComplexSurfaceFamily.constantComplexPlaneTotalEquiv,
      Bundle.Trivial.homeomorphProd, Bundle.TotalSpace.toProd]
    rfl

end MathlibFormal

end Teichmuller
