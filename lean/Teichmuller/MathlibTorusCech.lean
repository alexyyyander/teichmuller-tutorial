import Teichmuller.MathlibTorus
import Teichmuller.MathlibCechConcrete

namespace Teichmuller
namespace MathlibFormal

open HolomorphicCechDescentData

/-!
  A compact-fibre Cech adapter for the concrete genus-one family.

  The generic LocalJointlyHolomorphicFamily interface uses a global model
  fibre ℂ, which is appropriate for the translated-plane regression model
  but impossible for an entire compact torus.  The first compact-fibre
  adapter therefore works one level higher: it uses the already constructed
  GlobalHolomorphicMarkedFamily of quotient tori, covers its test base by
  small parameter balls, and feeds the resulting restrictions into the
  general Cech quotient/atlas machinery.

  The fibre transition on an overlap is the identity on the common quotient
  torus.  The nontrivial analytic information is retained in the local
  surface charts of the restricted global family; their unquotiented
  transition sheets are the parameter-dependent deck maps constructed in
  MathlibTorus.lean.
-/

universe u w v t

/-! Equality transport for a family atlas is harmless at the level of its
    global bookkeeping fields.  These small lemmas keep dependent transports
    explicit instead of asking `simp` to guess a motive involving a Sigma
    total space. -/

theorem ComplexSurfaceFamilyAtlas.cast_cover_univ
    {S : Type u} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace C]
    {F G : ComplexSurfaceFamily.Family S C}
    (h : F = G)
    (A : @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total F) C inferInstance)
    (hA : A.coverSet = Set.univ) :
    (h ▸ A).coverSet = Set.univ := by
  cases h
  exact hA

theorem ComplexSurfaceFamilyAtlas.cast_topology_eq
    {S : Type u} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace C]
    {F G : ComplexSurfaceFamily.Family S C}
    (h : F = G)
    (A : @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total F) C inferInstance)
    (hA : A.toComplexSurfaceAtlas.topology = F.totalTopology) :
    (h ▸ A).toComplexSurfaceAtlas.topology = G.totalTopology := by
  cases h
  exact hA

theorem ComplexSurfaceFamilyAtlas.cast_projection_eq
    {S : Type u} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace C]
    {F G : ComplexSurfaceFamily.Family S C}
    (h : F = G)
    (A : @ComplexSurfaceFamilyAtlas
      (ComplexSurfaceFamily.Total F) C inferInstance)
    (hA : ∀ x,
      A.projection x = ComplexSurfaceFamily.projection F x) :
    ∀ x, (h ▸ A).projection x = ComplexSurfaceFamily.projection G x := by
  cases h
  exact hA

/-!
  The ordinary holomorphic Cech data already permits an arbitrary marked
  fibre type S.  The following refinement makes compactness of each actual
  local fibre an explicit reusable field.  It is intentionally a property of
  the fibre topology stored by the family, not an assumption that the
  reference type S itself is compact.
-/

structure CompactFiberHolomorphicCechDescentData
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    extends HolomorphicCechDescentData.{u, w, v, t} S B I where
  compact_fiber : ∀ (i : I) (b : toHolomorphicCechDescentData.cover i),
    @CompactSpace
      ((toHolomorphicCechDescentData.localFamily i).family.fiber b).carrier
      ((toHolomorphicCechDescentData.localFamily i).family.fiber b).topology

namespace CompactFiberHolomorphicCechDescentData

theorem compact_fiber_at
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : CompactFiberHolomorphicCechDescentData (S := S) (B := B) (I := I))
    (i : I) (b : D.toHolomorphicCechDescentData.cover i) :
    @CompactSpace
      ((D.toHolomorphicCechDescentData.localFamily i).family.fiber b).carrier
      ((D.toHolomorphicCechDescentData.localFamily i).family.fiber b).topology :=
  D.compact_fiber i b

end CompactFiberHolomorphicCechDescentData

/-!
  Compactness of the descended fibre is stronger than compactness of each
  local fibre: the quotient topology must be compared with one chosen local
  fibre.  This witness records exactly that comparison as an actual
  homeomorphism.  It is the geometric input still needed before a descended
  compact fibre can be claimed.
-/

@[reducible] instance instDescendedFiberTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I) (b : B) :
    TopologicalSpace (DescendedFiber D b) := by
  exact @instTopologicalSpaceSubtype
    (DescendedTotal D)
    (fun q => descendedProjection D q = b)
    (instDescendedTotalTopology D)

/-!
  Before handling the pulled-back test base, isolate the fixed-parameter
  fibre of the original varying-torus total space.  The key point is that the
  total quotient map is open and preserves the parameter exactly; therefore
  its restriction to a parameter fibre is again an open quotient map.
-/

abbrev ComplexTorusTotalFiberSlice (τ : ComplexTorusParameter) :=
  {x : Sigma ComplexTorus // x.1 = τ}

abbrev ComplexTorusLiftFiberSlice (τ : ComplexTorusParameter) :=
  {p : ComplexTorusParameter × ℂ // p.1 = τ}

@[reducible] noncomputable instance instComplexTorusTotalFiberSliceTopology
    (τ : ComplexTorusParameter) :
    TopologicalSpace (ComplexTorusTotalFiberSlice τ) :=
  @instTopologicalSpaceSubtype
    (Sigma ComplexTorus)
    (fun x => x.1 = τ)
    complexTorusTotalTopology

@[reducible] noncomputable instance instComplexTorusLiftFiberSliceTopology
    (τ : ComplexTorusParameter) :
    TopologicalSpace (ComplexTorusLiftFiberSlice τ) :=
  @instTopologicalSpaceSubtype
    (ComplexTorusParameter × ℂ)
    (fun p => p.1 = τ)
    inferInstance

theorem complexTorusTotalMk_isOpenMap :
    @IsOpenMap
      (ComplexTorusParameter × ℂ) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology complexTorusTotalMk := by
  intro V hV
  exact complexTorusTotalMk_image_isOpen hV

noncomputable def complexTorusTotalMkFiberSlice
    (τ : ComplexTorusParameter) :
    ComplexTorusLiftFiberSlice τ → ComplexTorusTotalFiberSlice τ :=
  fun p =>
    ⟨complexTorusTotalMk p.1, by
      change p.1.1 = τ
      exact p.2⟩

theorem complexTorusTotalMkFiberSlice_continuous
    (τ : ComplexTorusParameter) :
    @Continuous
      (ComplexTorusLiftFiberSlice τ)
      (ComplexTorusTotalFiberSlice τ)
      (instComplexTorusLiftFiberSliceTopology τ)
      (instComplexTorusTotalFiberSliceTopology τ)
      (complexTorusTotalMkFiberSlice τ) := by
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  apply Continuous.subtype_mk
  exact complexTorusTotalMk_continuous.comp continuous_subtype_val

theorem complexTorusTotalMkFiberSlice_surjective
    (τ : ComplexTorusParameter) :
    Function.Surjective (complexTorusTotalMkFiberSlice τ) := by
  intro y
  obtain ⟨p, hp⟩ := complexTorusTotalMk_surjective y.1
  have hpτ : p.1 = τ := by
    apply UpperHalfPlane.ext
    calc
      (p.1 : ℂ) = (complexTorusTotalMk p).1 := by rfl
      _ = (y.1.1 : ℂ) := congrArg (fun q : ComplexTorusParameter => (q : ℂ))
        (congrArg Sigma.fst hp)
      _ = (τ : ℂ) := congrArg (fun q : ComplexTorusParameter => (q : ℂ)) y.2
  refine ⟨⟨p, hpτ⟩, ?_⟩
  apply Subtype.ext
  exact hp

theorem complexTorusTotalMkFiberSlice_isOpenMap
    (τ : ComplexTorusParameter) :
    @IsOpenMap
      (ComplexTorusLiftFiberSlice τ)
      (ComplexTorusTotalFiberSlice τ)
      (instComplexTorusLiftFiberSliceTopology τ)
      (instComplexTorusTotalFiberSliceTopology τ)
      (complexTorusTotalMkFiberSlice τ) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have himage : @IsOpen (Sigma ComplexTorus) complexTorusTotalTopology
      (complexTorusTotalMk '' V) :=
    complexTorusTotalMk_image_isOpen hV
  have himage_eq :
      complexTorusTotalMkFiberSlice τ '' U =
        (Subtype.val : ComplexTorusTotalFiberSlice τ → Sigma ComplexTorus) ⁻¹'
          (complexTorusTotalMk '' V) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpV : p.1 ∈ V := by
        change p ∈ Subtype.val ⁻¹' V
        rw [hVU]
        exact hp
      exact ⟨p.1, hpV, rfl⟩
    · intro hy
      rcases hy with ⟨p, hp, hpy⟩
      have hpτ : p.1 = τ := by
        apply UpperHalfPlane.ext
        calc
          (p.1 : ℂ) = (complexTorusTotalMk p).1 := by rfl
          _ = (y.1.1 : ℂ) := congrArg (fun q : ComplexTorusParameter => (q : ℂ))
            (congrArg Sigma.fst hpy)
          _ = (τ : ℂ) := congrArg (fun q : ComplexTorusParameter => (q : ℂ)) y.2
      refine ⟨⟨p, hpτ⟩, ?_, ?_⟩
      · rw [← hVU]
        exact hp
      · apply Subtype.ext
        exact hpy
  rw [himage_eq]
  change @IsOpen
    (ComplexTorusTotalFiberSlice τ)
    (TopologicalSpace.induced Subtype.val complexTorusTotalTopology)
    ((Subtype.val : ComplexTorusTotalFiberSlice τ → Sigma ComplexTorus) ⁻¹'
      (complexTorusTotalMk '' V))
  exact @isOpen_induced
    (ComplexTorusTotalFiberSlice τ) (Sigma ComplexTorus)
    complexTorusTotalTopology
    Subtype.val (complexTorusTotalMk '' V) himage

theorem complexTorusTotalMkFiberSlice_isQuotientMap
    (τ : ComplexTorusParameter) :
    @Topology.IsQuotientMap
      (ComplexTorusLiftFiberSlice τ)
      (ComplexTorusTotalFiberSlice τ)
      (instComplexTorusLiftFiberSliceTopology τ)
      (instComplexTorusTotalFiberSliceTopology τ)
      (complexTorusTotalMkFiberSlice τ) :=
  IsOpenMap.isQuotientMap
    (complexTorusTotalMkFiberSlice_isOpenMap τ)
    (complexTorusTotalMkFiberSlice_continuous τ)
    (complexTorusTotalMkFiberSlice_surjective τ)

noncomputable def complexTorusTotalFiberSliceHomeomorph
    (τ : ComplexTorusParameter) :
    @Homeomorph
      (ComplexTorus τ) (ComplexTorusTotalFiberSlice τ)
      inferInstance (instComplexTorusTotalFiberSliceTopology τ) := by
  let toFun : ComplexTorus τ → ComplexTorusTotalFiberSlice τ :=
    fun x => ⟨⟨τ, x⟩, rfl⟩
  let invFun : ComplexTorusTotalFiberSlice τ → ComplexTorus τ :=
    fun y => Eq.mp (congrArg ComplexTorus y.2) y.1.2
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    rfl
  have hright : Function.RightInverse invFun toFun := by
    intro y
    rcases y with ⟨⟨τ', x⟩, hτ⟩
    cases hτ
    rfl
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
    apply Continuous.subtype_mk
    change @Continuous (ComplexTorus τ) (Sigma ComplexTorus)
      inferInstance complexTorusTotalTopology
      (fun x => (⟨τ, x⟩ : Sigma ComplexTorus))
    apply (complexTorusMk_isQuotientCoveringMap τ).toIsQuotientMap.continuous_iff.mpr
    change Continuous (fun z : ℂ =>
      complexTorusTotalMk (τ, z))
    exact complexTorusTotalMk_continuous.comp
      (continuous_const.prodMk continuous_id)
  · let q := complexTorusTotalMkFiberSlice τ
    have hq := complexTorusTotalMkFiberSlice_isQuotientMap τ
    apply hq.continuous_iff.mpr
    change Continuous (fun p : ComplexTorusLiftFiberSlice τ =>
      invFun (q p))
    have hcomp :
        (fun p : ComplexTorusLiftFiberSlice τ => invFun (q p)) =
          (fun p : ComplexTorusLiftFiberSlice τ =>
            complexTorusMk τ p.1.2) := by
      funext p
      rcases p with ⟨⟨τ', z⟩, hτ⟩
      cases hτ
      rfl
    rw [hcomp]
    exact complexTorusMk_continuous τ |>.comp
      (continuous_snd.comp continuous_subtype_val)

/-!
  The fixed-parameter homeomorphisms now assemble into one continuous family.
  The target is a dependent sum of the fibre slices; its topology is the
  topology transported from the original quotient total space by the inverse
  identification.  This makes the parameter dependence an actual topological
  statement rather than a collection of unrelated fibrewise witnesses.
-/

abbrev ComplexTorusFiberSliceTotal :=
  Sigma (fun τ : ComplexTorusParameter => ComplexTorusTotalFiberSlice τ)

noncomputable def complexTorusFiberSliceTotalToSlice :
    Sigma ComplexTorus → ComplexTorusFiberSliceTotal :=
  fun z => ⟨z.1, ⟨z, rfl⟩⟩

noncomputable def complexTorusFiberSliceTotalFromSlice :
    ComplexTorusFiberSliceTotal → Sigma ComplexTorus :=
  fun z =>
    ⟨z.1, Eq.mp (congrArg ComplexTorus z.2.2) z.2.1.2⟩

@[reducible] noncomputable def instComplexTorusFiberSliceTotalTopology :
    TopologicalSpace ComplexTorusFiberSliceTotal :=
  TopologicalSpace.induced complexTorusFiberSliceTotalFromSlice
    complexTorusTotalTopology

noncomputable def complexTorusFiberSliceTotalHomeomorph :
    @Homeomorph
      (Sigma ComplexTorus)
      ComplexTorusFiberSliceTotal
      complexTorusTotalTopology
      instComplexTorusFiberSliceTotalTopology := by
  let toFun := complexTorusFiberSliceTotalToSlice
  let invFun := complexTorusFiberSliceTotalFromSlice
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  letI : TopologicalSpace ComplexTorusFiberSliceTotal :=
    instComplexTorusFiberSliceTotalTopology
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    rfl
  · intro z
    rcases z with ⟨τ, ⟨⟨τ', x⟩, hτ⟩⟩
    cases hτ
    rfl
  · apply continuous_induced_rng.mpr
    change Continuous (fun z : Sigma ComplexTorus =>
      complexTorusFiberSliceTotalFromSlice
        (complexTorusFiberSliceTotalToSlice z))
    change Continuous (fun z : Sigma ComplexTorus => z)
    exact continuous_id
  · change @Continuous
      ComplexTorusFiberSliceTotal (Sigma ComplexTorus)
      instComplexTorusFiberSliceTotalTopology complexTorusTotalTopology
      complexTorusFiberSliceTotalFromSlice
    exact continuous_induced_dom

@[simp] theorem complexTorusFiberSliceTotalHomeomorph_base
    (z : Sigma ComplexTorus) :
    (complexTorusFiberSliceTotalHomeomorph z).1 = z.1 := by
  rfl

@[simp] theorem complexTorusFiberSliceTotalHomeomorph_fiber
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    (complexTorusFiberSliceTotalHomeomorph ⟨τ, x⟩).2.1 =
      (⟨τ, x⟩ : Sigma ComplexTorus) := by
  rfl

theorem complexTorusFiberSliceTotalHomeomorph_fiber_homeomorph_apply
    (τ : ComplexTorusParameter) (x : ComplexTorus τ) :
    (complexTorusFiberSliceTotalHomeomorph ⟨τ, x⟩).2 =
      complexTorusTotalFiberSliceHomeomorph τ x := by
  simp [complexTorusFiberSliceTotalHomeomorph,
    complexTorusFiberSliceTotalToSlice,
    complexTorusTotalFiberSliceHomeomorph]

/-!
  Pulling this assembled family back along a holomorphic test base gives the
  uniform topological comparison used by the concrete Čech construction.
  The final continuity theorem below goes back to the original quotient
  total space, so the transported slice topology is tied to the actual
  parameterized torus family rather than being an isolated fibrewise choice.
-/

abbrev ComplexTorusLocalHolomorphicParameterBase
    (F : ComplexTorusLocalHolomorphicParameterMap) :=
  {b : ℂ // b ∈ F.domain}

abbrev ComplexTorusLocalFiberSliceTotal
    (F : ComplexTorusLocalHolomorphicParameterMap) :=
  Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
    ComplexTorusTotalFiberSlice
      (F.toComplexTorusHolomorphicParameterMap.parameterPoint b))

noncomputable def complexTorusLocalFiberSliceTotalToSlice
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
      ComplexTorus
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint b)) →
      ComplexTorusLocalFiberSliceTotal F :=
  fun z =>
    ⟨z.1,
      ⟨⟨F.toComplexTorusHolomorphicParameterMap.parameterPoint z.1, z.2⟩,
        rfl⟩⟩

noncomputable def complexTorusLocalFiberSliceTotalFromSlice
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusLocalFiberSliceTotal F →
      Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus
          (F.toComplexTorusHolomorphicParameterMap.parameterPoint b)) :=
  fun z =>
    ⟨z.1,
      Eq.mp (congrArg ComplexTorus z.2.2) z.2.1.2⟩

@[reducible] noncomputable def instComplexTorusLocalFiberSliceTotalTopology
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    TopologicalSpace (ComplexTorusLocalFiberSliceTotal F) :=
  TopologicalSpace.induced (complexTorusLocalFiberSliceTotalFromSlice F)
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology

noncomputable def complexTorusLocalFiberSliceTotalHomeomorph
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    @Homeomorph
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus
          (F.toComplexTorusHolomorphicParameterMap.parameterPoint b)))
      (ComplexTorusLocalFiberSliceTotal F)
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
      (instComplexTorusLocalFiberSliceTotalTopology F) := by
  let toFun := complexTorusLocalFiberSliceTotalToSlice F
  let invFun := complexTorusLocalFiberSliceTotalFromSlice F
  let sourceTopology :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  letI : TopologicalSpace
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus
          (F.toComplexTorusHolomorphicParameterMap.parameterPoint b))) :=
    sourceTopology
  letI : TopologicalSpace (ComplexTorusLocalFiberSliceTotal F) :=
    instComplexTorusLocalFiberSliceTotalTopology F
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    rfl
  · intro z
    rcases z with ⟨b, ⟨⟨τ, x⟩, hτ⟩⟩
    cases hτ
    rfl
  · apply continuous_induced_rng.mpr
    change Continuous (fun z =>
      complexTorusLocalFiberSliceTotalFromSlice F
        (complexTorusLocalFiberSliceTotalToSlice F z))
    change Continuous (fun z => z)
    exact continuous_id
  · change @Continuous
      (ComplexTorusLocalFiberSliceTotal F)
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus
          (F.toComplexTorusHolomorphicParameterMap.parameterPoint b)))
      (instComplexTorusLocalFiberSliceTotalTopology F)
      sourceTopology
      (complexTorusLocalFiberSliceTotalFromSlice F)
    exact continuous_induced_dom

@[simp] theorem complexTorusLocalFiberSliceTotalHomeomorph_base
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (z : Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
      ComplexTorus
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint b))) :
    (complexTorusLocalFiberSliceTotalHomeomorph F z).1 = z.1 := by
  rfl

@[simp] theorem complexTorusLocalFiberSliceTotalHomeomorph_fiber
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (b : ComplexTorusLocalHolomorphicParameterBase F)
    (x : ComplexTorus
      (F.toComplexTorusHolomorphicParameterMap.parameterPoint b)) :
    (complexTorusLocalFiberSliceTotalHomeomorph F ⟨b, x⟩).2.1 =
      (⟨F.toComplexTorusHolomorphicParameterMap.parameterPoint b, x⟩ :
        Sigma ComplexTorus) := by
  rfl

theorem complexTorusLocalFiberSliceTotalHomeomorph_toOriginal_continuous
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    @Continuous
      (ComplexTorusLocalFiberSliceTotal F)
      (Sigma ComplexTorus)
      (instComplexTorusLocalFiberSliceTotalTopology F)
      complexTorusTotalTopology
      (fun z =>
        (complexTorusHolomorphicParameterPullback_toTotal
          F.toComplexTorusHolomorphicParameterMap)
          ((complexTorusLocalFiberSliceTotalHomeomorph F).invFun z)) := by
  let F₀ := F.toComplexTorusHolomorphicParameterMap
  letI : TopologicalSpace
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus (F₀.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback F₀).family.totalTopology
  letI : TopologicalSpace (ComplexTorusLocalFiberSliceTotal F) :=
    instComplexTorusLocalFiberSliceTotalTopology F
  letI : TopologicalSpace (Sigma ComplexTorus) := complexTorusTotalTopology
  have hlocal :
      @Continuous
        (ComplexTorusLocalFiberSliceTotal F)
        (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
          ComplexTorus (F₀.parameterPoint b)))
        (instComplexTorusLocalFiberSliceTotalTopology F)
        (complexTorusHolomorphicParameterPullback F₀).family.totalTopology
        (complexTorusLocalFiberSliceTotalHomeomorph F).invFun := by
    exact (complexTorusLocalFiberSliceTotalHomeomorph F).continuous_invFun
  exact
    (complexTorusHolomorphicParameterPullback_toTotal_continuous F₀).comp hlocal

/-!
  The same fixed-base comparison is useful for arbitrary dependent-sum
  pullbacks.  A fibre slice of a pullback family is homeomorphic to the
  corresponding fibre slice of the original family; this is the precise
  topological form of “base change does not alter the fibre topology”.
-/

noncomputable def canonicalPullbackFiberSliceHomeomorph
    {S : Type u} {B : Type w} {C : Type w}
    [TopologicalSpace S] [TopologicalSpace B] [TopologicalSpace C]
    (F : ComplexSurfaceFamily.Family S B)
    (e : C → B) (he : Continuous e) (c : C) :
    @Homeomorph
      {z : ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback F e he) // z.1 = c}
      {x : ComplexSurfaceFamily.Total F //
        ComplexSurfaceFamily.projection F x = e c}
      (@instTopologicalSpaceSubtype
        (ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback F e he))
        (fun z => z.1 = c)
        (ComplexSurfaceFamily.pullbackTopology F e))
      (@instTopologicalSpaceSubtype
        (ComplexSurfaceFamily.Total F)
        (fun x => ComplexSurfaceFamily.projection F x = e c)
        F.totalTopology) := by
  let P := ComplexSurfaceFamily.canonicalPullback F e he
  let toFun :
      {z : ComplexSurfaceFamily.Total P // z.1 = c} →
        {x : ComplexSurfaceFamily.Total F //
          ComplexSurfaceFamily.projection F x = e c} :=
    fun z =>
      ⟨⟨e z.1.1, z.1.2⟩, by
        change e z.1.1 = e c
        exact congrArg e z.2⟩
  let invFun :
      {x : ComplexSurfaceFamily.Total F //
          ComplexSurfaceFamily.projection F x = e c} →
        {z : ComplexSurfaceFamily.Total P // z.1 = c} :=
    fun x =>
      ⟨⟨c,
          Eq.mp
            (congrArg (fun b => (F.fiber b).carrier) x.2)
            x.1.2⟩, rfl⟩
  letI : TopologicalSpace (ComplexSurfaceFamily.Total F) := F.totalTopology
  letI : TopologicalSpace (ComplexSurfaceFamily.Total P) := P.totalTopology
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    rcases z with ⟨⟨c', x⟩, hzc⟩
    change c' = c at hzc
    cases hzc
    rfl
  · intro x
    rcases x with ⟨⟨b, x⟩, hxb⟩
    change b = e c at hxb
    cases hxb
    rfl
  · apply Continuous.subtype_mk
    have hmap :
        @Continuous
          (ComplexSurfaceFamily.Total P)
          (C × ComplexSurfaceFamily.Total F)
          P.totalTopology inferInstance
          (ComplexSurfaceFamily.pullbackMap F e) :=
      continuous_induced_dom
    have hsecond :=
      (@continuous_snd C (ComplexSurfaceFamily.Total F)
        inferInstance inferInstance).comp hmap
    have hsecond' :
        @Continuous
          {z : ComplexSurfaceFamily.Total P // z.1 = c}
          (ComplexSurfaceFamily.Total F)
          (@instTopologicalSpaceSubtype
            (ComplexSurfaceFamily.Total P)
            (fun z => z.1 = c)
            P.totalTopology)
          F.totalTopology
          (fun z =>
            (ComplexSurfaceFamily.pullbackMap F e z.1).2) := by
      exact hsecond.comp continuous_subtype_val
    change @Continuous
      {z : ComplexSurfaceFamily.Total P // z.1 = c}
      (ComplexSurfaceFamily.Total F)
      _ F.totalTopology
      (fun z => ⟨e z.1.1, z.1.2⟩)
    simpa [P, ComplexSurfaceFamily.pullbackMap] using hsecond'
  · apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    have hpair :
        @Continuous
          {x : ComplexSurfaceFamily.Total F //
            ComplexSurfaceFamily.projection F x = e c}
          (C × ComplexSurfaceFamily.Total F)
          _ inferInstance
          (fun x => (c, x.1)) :=
      continuous_const.prodMk continuous_subtype_val
    change @Continuous
      {x : ComplexSurfaceFamily.Total F //
        ComplexSurfaceFamily.projection F x = e c}
      (C × ComplexSurfaceFamily.Total F)
      _ inferInstance
      (fun x =>
        ComplexSurfaceFamily.pullbackMap F e
          ⟨c,
            Eq.mp
              (congrArg (fun b => (F.fiber b).carrier) x.2)
              x.1.2⟩)
    convert hpair using 1
    funext x
    rcases x with ⟨⟨b, y⟩, hxb⟩
    change b = e c at hxb
    cases hxb
    rfl

/-!
  A useful intermediate object is the fibre of one local total space, with
  the topology induced from that total space.  This is not definitionally the
  same as the fibre topology stored in `Family`: the latter is deliberately
  an independent field.  Keeping the two carriers separate lets us prove the
  genuine quotient statement before asking for the remaining fibre/subspace
  comparison.
-/

abbrev CechLocalFiberSlice
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i) :=
  {z : ComplexSurfaceFamily.Total (D.localFamily i).family // z.1 = b}

@[reducible] instance instCechLocalFiberSliceTopology
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i) :
    TopologicalSpace (CechLocalFiberSlice D i b) := by
  exact @instTopologicalSpaceSubtype
    (ComplexSurfaceFamily.Total (D.localFamily i).family)
    (fun z => z.1 = b)
    (D.localFamily i).family.totalTopology

noncomputable def cechLocalFiberSliceMap
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i) :
    CechLocalFiberSlice D i b → DescendedFiber D (b : B) :=
  fun z =>
    ⟨localQuotient D i z.1, by
      rw [localQuotient_projection]
      exact congrArg Subtype.val z.2⟩

theorem cechLocalFiberSliceMap_isEmbedding
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @Topology.IsEmbedding
      (CechLocalFiberSlice D i b) (DescendedFiber D (b : B))
      (instCechLocalFiberSliceTopology D i b)
      (instDescendedFiberTopology D (b : B))
      (cechLocalFiberSliceMap D i b) := by
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total (D.localFamily i).family) :=
    (D.localFamily i).family.totalTopology
  have hlocal :=
    (isOpenEmbedding_localQuotient_of_isOpenMap_quotientMk D i hquot).isEmbedding
  let hmaps :
      ({z : ComplexSurfaceFamily.Total (D.localFamily i).family |
          z.1 = b}).MapsTo (localQuotient D i)
        {q : DescendedTotal D | descendedProjection D q = (b : B)} := by
    intro z hz
    change descendedProjection D (localQuotient D i z) = (b : B)
    rw [localQuotient_projection]
    exact congrArg Subtype.val hz
  change @Topology.IsEmbedding
    {z : ComplexSurfaceFamily.Total (D.localFamily i).family // z.1 = b}
    {q : DescendedTotal D // descendedProjection D q = (b : B)}
    (TopologicalSpace.induced Subtype.val
      (D.localFamily i).family.totalTopology)
    (TopologicalSpace.induced Subtype.val
      (instDescendedTotalTopology D))
    (cechLocalFiberSliceMap D i b)
  exact hlocal.restrict hmaps

theorem cechLocalFiberSliceMap_surjective
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i) :
    Function.Surjective (cechLocalFiberSliceMap D i b) := by
  intro y
  rcases y with ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases x with ⟨j, z⟩
  have hzbase : (z.1 : B) = (b : B) := by
    simpa [descendedProjection, localBase,
      ComplexSurfaceFamily.projection] using hq
  let p : CechOverlap D.cover j i :=
    ⟨(z.1 : B), ⟨z.1.property, by
      rw [hzbase]
      exact b.property⟩⟩
  let zi : ComplexSurfaceFamily.Total (D.localFamily i).family :=
    ⟨CechOverlap.rightPoint D.cover j i p,
      D.transition j i p z.2⟩
  have hzi : zi.1 = b := by
    apply Subtype.ext
    exact hzbase
  let zs : CechLocalFiberSlice D i b := ⟨zi, hzi⟩
  refine ⟨zs, ?_⟩
  apply Subtype.ext
  have htransition := localQuotient_transition D p z.2
  have hleft : CechOverlap.leftPoint D.cover j i p = z.1 := by
    apply Subtype.ext
    rfl
  calc
    localQuotient D i zi =
        localQuotient D j
          ⟨CechOverlap.leftPoint D.cover j i p, z.2⟩ := by
      exact htransition.symm
    _ = quotientMk D ⟨j, z⟩ := by
      change quotientMk D
        ⟨j, ⟨CechOverlap.leftPoint D.cover j i p, z.2⟩⟩ =
        quotientMk D ⟨j, z⟩
      cases hleft
      rfl

noncomputable def cechLocalFiberSliceHomeomorph
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i)
    (hquot : @IsOpenMap
      (LocalTotal D) (DescendedTotal D)
      (localTotalTopology D) inferInstance (quotientMk D)) :
    @Homeomorph
      (CechLocalFiberSlice D i b) (DescendedFiber D (b : B))
      (instCechLocalFiberSliceTopology D i b)
      (instDescendedFiberTopology D (b : B)) := by
  exact
    (cechLocalFiberSliceMap_isEmbedding D i b hquot).toHomeomorphOfSurjective
      (cechLocalFiberSliceMap_surjective D i b)

structure DescendedFiberCompactnessWitness
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I) (b : B) where
  index : I
  base_mem : b ∈ D.cover index
  fiberHomeomorph :
    @Homeomorph
      ((D.localFamily index).family.fiber
        ⟨b, base_mem⟩).carrier
      (DescendedFiber D b)
      ((D.localFamily index).family.fiber
        ⟨b, base_mem⟩).topology
      inferInstance

/-!
  The remaining comparison is now isolated in a single homeomorphism: the
  stored fibre topology of a local `Family` versus the subspace topology of
  its total-space slice.  Once this comparison is supplied, the previous
  slice homeomorphism automatically produces the compactness witness for the
  descended fibre.
-/

structure CechLocalFiberTopologyComparison
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : HolomorphicCechDescentData.{u, w, v, t} S B I)
    (i : I) (b : D.cover i) where
  fiberHomeomorph :
    @Homeomorph
      ((D.localFamily i).family.fiber b).carrier
      (CechLocalFiberSlice D i b)
      ((D.localFamily i).family.fiber b).topology
      (instCechLocalFiberSliceTopology D i b)

namespace DescendedFiberCompactnessWitness

noncomputable def of_localFiberTopologyComparison
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : CompactFiberHolomorphicCechDescentData
      (S := S) (B := B) (I := I))
    (i : I)
    (b : D.toHolomorphicCechDescentData.cover i)
    (hquot : @IsOpenMap
      (LocalTotal D.toHolomorphicCechDescentData)
      (DescendedTotal D.toHolomorphicCechDescentData)
      (localTotalTopology D.toHolomorphicCechDescentData)
      inferInstance
      (quotientMk D.toHolomorphicCechDescentData))
    (H : CechLocalFiberTopologyComparison
      D.toHolomorphicCechDescentData i b) :
    DescendedFiberCompactnessWitness
      D.toHolomorphicCechDescentData (b : B) := by
  letI : TopologicalSpace
      ((D.toHolomorphicCechDescentData.localFamily i).family.fiber b).carrier :=
    (D.toHolomorphicCechDescentData.localFamily i).family.fiber b |>.topology
  exact
    { index := i
      base_mem := b.property
      fiberHomeomorph := H.fiberHomeomorph.trans
        (cechLocalFiberSliceHomeomorph
          D.toHolomorphicCechDescentData i b hquot) }

@[reducible] noncomputable def compactSpace_of_local
    {S : Type u} {B : Type w} {I : Type v}
    [TopologicalSpace S] [TopologicalSpace B]
    (D : CompactFiberHolomorphicCechDescentData
      (S := S) (B := B) (I := I))
    (b : B)
    (W : DescendedFiberCompactnessWitness
      D.toHolomorphicCechDescentData b) :
    CompactSpace (DescendedFiber D.toHolomorphicCechDescentData b) := by
  letI : TopologicalSpace
      ((D.toHolomorphicCechDescentData.localFamily W.index).family.fiber
        ⟨b, W.base_mem⟩).carrier :=
    (D.toHolomorphicCechDescentData.localFamily W.index).family.fiber
      ⟨b, W.base_mem⟩ |>.topology
  letI : @CompactSpace
      ((D.toHolomorphicCechDescentData.localFamily W.index).family.fiber
        ⟨b, W.base_mem⟩).carrier
      ((D.toHolomorphicCechDescentData.localFamily W.index).family.fiber
        ⟨b, W.base_mem⟩).topology :=
    D.compact_fiber W.index ⟨b, W.base_mem⟩
  exact W.fiberHomeomorph.compactSpace

end DescendedFiberCompactnessWitness

def complexTorusLocalHolomorphicParameterCechCover
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    Set (ComplexTorusLocalHolomorphicParameterBase F) :=
  {b | dist (b : ℂ) c < (1 : ℝ) / 4}

theorem complexTorusLocalHolomorphicParameterCechCover_isOpen
    (F : ComplexTorusLocalHolomorphicParameterMap) (c : ℂ) :
    IsOpen (complexTorusLocalHolomorphicParameterCechCover F c) := by
  change IsOpen {b : ComplexTorusLocalHolomorphicParameterBase F |
    dist (b : ℂ) c < (1 : ℝ) / 4}
  exact isOpen_lt
    (continuous_subtype_val.dist continuous_const)
    continuous_const

theorem complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (⋃ c : ℂ, complexTorusLocalHolomorphicParameterCechCover F c) =
      (Set.univ :
        Set (ComplexTorusLocalHolomorphicParameterBase F)) := by
  ext b
  constructor
  · intro _
    trivial
  · intro _
    refine Set.mem_iUnion.mpr ⟨(b : ℂ), ?_⟩
    change dist (b : ℂ) (b : ℂ) < (1 : ℝ) / 4
    norm_num

noncomputable def complexTorusLocalHolomorphicParameterCechData
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    HolomorphicCechDescentData
      (ComplexTorus complexTorusBaseParameter)
      (ComplexTorusLocalHolomorphicParameterBase F)
      ℂ :=
  multiPatchCechDescentData
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)

@[simp] theorem complexTorusLocalHolomorphicParameterCechData_cover
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalHolomorphicParameterCechData F).cover =
      complexTorusLocalHolomorphicParameterCechCover F := by
  rfl

/-!
  For the concrete torus family, the local Čech fibre slice can now be
  compared with the original quotient torus.  The proof factors through
  pullback associativity: an open-patch restriction is an iterated pullback,
  while the fixed-base slice of the direct pullback is handled by the generic
  comparison above.
-/

noncomputable def complexTorusCechLocalFiberSliceHomeomorph
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : ℂ)
    (b : (complexTorusLocalHolomorphicParameterCechData F).cover c) :
    @Homeomorph
      (CechLocalFiberSlice
        (complexTorusLocalHolomorphicParameterCechData F) c b)
      (ComplexTorusTotalFiberSlice
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint (b :
          ComplexTorusLocalHolomorphicParameterBase F)))
      (instCechLocalFiberSliceTopology
        (complexTorusLocalHolomorphicParameterCechData F) c b)
      (instComplexTorusTotalFiberSliceTopology
        (F.toComplexTorusHolomorphicParameterMap.parameterPoint (b :
          ComplexTorusLocalHolomorphicParameterBase F))) := by
  let D := complexTorusLocalHolomorphicParameterCechData F
  let F₀ := F.toComplexTorusHolomorphicParameterMap
  let V := complexTorusLocalHolomorphicParameterCechCover F c
  let e : ComplexTorusLocalHolomorphicParameterBase F →
      ComplexTorusParameter := F₀.parameterPoint
  let g : V → ComplexTorusLocalHolomorphicParameterBase F :=
    fun v => (v : ComplexTorusLocalHolomorphicParameterBase F)
  have he : Continuous e := F₀.parameterPoint_continuous
  have hg : Continuous g := continuous_subtype_val
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily e he) g hg)) :=
    ComplexSurfaceFamily.pullbackTopology
      (ComplexSurfaceFamily.canonicalPullback
        complexTorusMarkedSurfaceFamily e he) g
  letI : TopologicalSpace
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback
          complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
            (he.comp hg))) :=
    ComplexSurfaceFamily.pullbackTopology
      complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
  let hiter :=
    ComplexSurfaceFamily.canonicalPullback_iterated_homeomorph
      complexTorusMarkedSurfaceFamily e g he hg
  let hdirect :=
    canonicalPullbackFiberSliceHomeomorph
      complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
      (he.comp hg) b
  have hslice :
      @Homeomorph
        (CechLocalFiberSlice D c b)
        {z : ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
              (he.comp hg)) // z.1 = b}
        (instCechLocalFiberSliceTopology D c b)
        (@instTopologicalSpaceSubtype
          (ComplexSurfaceFamily.Total
            (ComplexSurfaceFamily.canonicalPullback
              complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
                (he.comp hg)))
          (fun z => z.1 = b)
          (ComplexSurfaceFamily.pullbackTopology
            complexTorusMarkedSurfaceFamily (fun v : V => e (g v)))) := by
    change @Homeomorph
      {z : ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback
            (ComplexSurfaceFamily.canonicalPullback
              complexTorusMarkedSurfaceFamily e he) g hg) // z.1 = b}
      {z : ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
              (he.comp hg)) // z.1 = b}
      (@instTopologicalSpaceSubtype
        (ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback
            (ComplexSurfaceFamily.canonicalPullback
              complexTorusMarkedSurfaceFamily e he) g hg))
        (fun z => z.1 = b)
        (ComplexSurfaceFamily.pullbackTopology
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily e he) g))
      (@instTopologicalSpaceSubtype
        (ComplexSurfaceFamily.Total
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily (fun v : V => e (g v))
              (he.comp hg)))
        (fun z => z.1 = b)
        (ComplexSurfaceFamily.pullbackTopology
          complexTorusMarkedSurfaceFamily (fun v : V => e (g v))))
    exact hiter.subtype (fun z => Iff.rfl)
  change @Homeomorph
    {z : ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily e he) g hg) // z.1 = b}
    (ComplexTorusTotalFiberSlice (e (g b)))
    (@instTopologicalSpaceSubtype
      (ComplexSurfaceFamily.Total
        (ComplexSurfaceFamily.canonicalPullback
          (ComplexSurfaceFamily.canonicalPullback
            complexTorusMarkedSurfaceFamily e he) g hg))
      (fun z => z.1 = b)
      (ComplexSurfaceFamily.pullbackTopology
        (ComplexSurfaceFamily.canonicalPullback
          complexTorusMarkedSurfaceFamily e he) g))
    (instComplexTorusTotalFiberSliceTopology (e (g b)))
  exact hslice.trans hdirect

noncomputable def complexTorusCechLocalFiberTopologyComparison
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : ℂ)
    (b : (complexTorusLocalHolomorphicParameterCechData F).cover c) :
    CechLocalFiberTopologyComparison
      (complexTorusLocalHolomorphicParameterCechData F) c b := by
  let τ :=
    F.toComplexTorusHolomorphicParameterMap.parameterPoint (b :
      ComplexTorusLocalHolomorphicParameterBase F)
  refine { fiberHomeomorph := ?_ }
  change @Homeomorph
      (ComplexTorus τ)
      (CechLocalFiberSlice
        (complexTorusLocalHolomorphicParameterCechData F) c b)
      inferInstance
      (instCechLocalFiberSliceTopology
        (complexTorusLocalHolomorphicParameterCechData F) c b)
  exact
    (complexTorusTotalFiberSliceHomeomorph τ).trans
      (complexTorusCechLocalFiberSliceHomeomorph F c b).symm

theorem complexTorusLocalHolomorphicParameterGlobalFamily_fiber_compact
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (b : ComplexTorusLocalHolomorphicParameterBase F) :
    @CompactSpace
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).carrier
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).topology := by
  change @CompactSpace
    (ComplexTorus (F.parameterPoint b)) inferInstance
  exact complexTorus_isCompact (F.parameterPoint b)

/-! The local fine-moduli witness can now be lifted one level, from the
    family-only classification interface to the global-family interface.
    The extra fields are not axioms: the concrete pulled-back atlas already
    constructed above supplies them.  This remains restricted to the
    explicit torus test objects `F`; it is not a global universal-family
    theorem. -/

noncomputable def complexTorusLocalHolomorphicParameterGlobalClassification
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily F) := by
  have hP :
      (complexTorusLocalHolomorphicParameterGlobalFamily F).family =
        MathlibFormal.ComplexSurfaceFamily.canonicalPullback
          W.globalFamily.family
          F.toComplexTorusHolomorphicParameterMap.parameterPoint
          F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous := by
    change (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).toFamily = _
    rw [W.family_eq]
    exact (complexTorusMarkedSurfaceFamily_canonicalPullback_eq
      F.toComplexTorusHolomorphicParameterMap).symm
  have hsource :
      MathlibFormal.ComplexSurfaceFamily.canonicalPullback
          complexTorusMarkedSurfaceFamily
          (complexTorusLocalHolomorphicParameterClassification F).map
          (complexTorusLocalHolomorphicParameterClassification F).map_continuous =
        MathlibFormal.ComplexSurfaceFamily.canonicalPullback
          W.globalFamily.family
          F.toComplexTorusHolomorphicParameterMap.parameterPoint
          F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous := by
    simp [complexTorusLocalHolomorphicParameterClassification,
      W.family_eq, complexTorusMarkedSurfaceFamily_canonicalPullback_eq]
  let A_local := complexTorusLocalHolomorphicParameterComplexSurfaceFamilyAtlas F
  let A_global :
      @ComplexSurfaceFamilyAtlas
        (ComplexSurfaceFamily.Total
          (MathlibFormal.ComplexSurfaceFamily.canonicalPullback
            W.globalFamily.family
            F.toComplexTorusHolomorphicParameterMap.parameterPoint
            F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous))
        {b : ℂ // b ∈ F.domain} inferInstance :=
    hP ▸ A_local
  have hcover_local : A_local.coverSet = Set.univ := by
    dsimp [A_local]
    rfl
  have htop_local :
      A_local.toComplexSurfaceAtlas.topology =
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family.totalTopology := by
    dsimp [A_local]
    rfl
  have hprojection_local : ∀ x,
      A_local.projection x =
        MathlibFormal.ComplexSurfaceFamily.projection
          (complexTorusLocalHolomorphicParameterGlobalFamily F).family x := by
    intro x
    rfl
  refine
    { map := F.toComplexTorusHolomorphicParameterMap.parameterPoint
      map_continuous :=
        F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous
      realization := ?_
      pullback_atlas := ?_
      pullback_cover_univ := ?_
      pullback_topology_eq := ?_
      pullback_projection_eq := ?_ }
  · simpa [complexTorusLocalHolomorphicParameterGlobalFamily] using
      (hsource ▸ (complexTorusLocalHolomorphicParameterClassification F).realization)
  · exact A_global
  · dsimp [A_global]
    exact ComplexSurfaceFamilyAtlas.cast_cover_univ hP A_local hcover_local
  · dsimp [A_global]
    exact ComplexSurfaceFamilyAtlas.cast_topology_eq hP A_local htop_local
  · intro x
    dsimp [A_global]
    exact (ComplexSurfaceFamilyAtlas.cast_projection_eq hP A_local
      hprojection_local) x

@[simp] theorem complexTorusLocalHolomorphicParameterGlobalClassification_map
  (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
  (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalHolomorphicParameterGlobalClassification W F).map =
      F.toComplexTorusHolomorphicParameterMap.parameterPoint :=
  by
    simp [complexTorusLocalHolomorphicParameterGlobalClassification] <;> rfl

theorem complexTorusLocalHolomorphicParameterGlobalClassification_toLocal
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalHolomorphicParameterGlobalClassification W F).toHolomorphicFamilyClassification.map =
      (complexTorusLocalHolomorphicParameterClassification F).map :=
  by
    simp [complexTorusLocalHolomorphicParameterGlobalClassification,
      complexTorusLocalHolomorphicParameterClassification] <;> rfl

/-! The upper half-plane is represented by a subtype, so its complex analytic
    classifying map is recorded in the ambient coordinate.  This is the global
    counterpart of `ComplexTorusLocalHolomorphicClassificationWitness`: the
    fibrewise realization and the global pullback atlas now live in the same
    witness, while `DifferentiableOn` remains a certificate for the ambient
    map `ℂ → ℂ`. -/

structure ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  classification :
    MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily F)
  ambientClassifyingMap : ℂ → ℂ
  ambientClassifyingMap_eq : ∀ (c : ℂ) (hc : c ∈ F.domain),
    ambientClassifyingMap c =
      (classification.map ⟨c, hc⟩ : ℂ)
  ambientClassifyingMap_differentiableOn :
    DifferentiableOn ℂ ambientClassifyingMap F.domain

noncomputable def complexTorusLocalHolomorphicParameterGlobalClassificationWitness
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness W F where
  classification := complexTorusLocalHolomorphicParameterGlobalClassification W F
  ambientClassifyingMap := F.toComplexTorusHolomorphicParameterMap.map
  ambientClassifyingMap_eq := by
    intro c hc
    rw [complexTorusLocalHolomorphicParameterGlobalClassification_map W F]
    rfl
  ambientClassifyingMap_differentiableOn :=
    F.toComplexTorusHolomorphicParameterMap.map_differentiableOn

theorem ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.map_eq_parameterPoint
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalHolomorphicParameterGlobalClassificationWitness W F).classification.map =
      F.toComplexTorusHolomorphicParameterMap.parameterPoint :=
  complexTorusLocalHolomorphicParameterGlobalClassification_map W F

/-! Base change preserves the ambient analytic certificate by the chain rule.
    The global classification component is the already proved global
    classification for the precomposed test family, while the ambient map is
    the literal composite of the two holomorphic parameter maps. -/

noncomputable def ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness W
      (F.precompose G hG) where
  classification :=
    complexTorusLocalHolomorphicParameterGlobalClassification W
      (F.precompose G hG)
  ambientClassifyingMap := fun c => F.map (G.map c)
  ambientClassifyingMap_eq := by
    intro c hc
    rfl
  ambientClassifyingMap_differentiableOn :=
    F.precompose_map_differentiableOn G hG

@[simp] theorem ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose_ambientClassifyingMap
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
      W F G hG).ambientClassifyingMap =
      fun c => F.map (G.map c) := by
  rfl

theorem complexTorusLocalHolomorphicParameterGlobalClassificationWitness_ambient_eq_precompose
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
      W F G hG).ambientClassifyingMap =
      fun c => F.map (G.map c) :=
  ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose_ambientClassifyingMap
    W F G hG

theorem complexTorusLocalHolomorphicParameterGlobalClassificationWitness_precompose_precompose_ambient
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G H : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (hH : Set.MapsTo H.map H.domain G.domain) :
    (ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
      W (F.precompose G hG) H hH).ambientClassifyingMap =
      fun c => F.map (G.map (H.map c)) := by
  rfl

theorem complexTorusLocalHolomorphicParameterGlobalClassificationWitness_precompose_compose_ambient
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G H : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (hH : Set.MapsTo H.map H.domain G.domain)
    (hGH : Set.MapsTo (G.compose H hH).map
      (G.compose H hH).domain F.domain) :
    (ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
      W F (G.compose H hH) hGH).ambientClassifyingMap =
      (ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness.precompose
        W (F.precompose G hG) H hH).ambientClassifyingMap := by
  funext c
  rfl

/-! Quantifying the preceding global classifier over all local torus test
    maps gives the Čech-compatible restricted universal object.  Its test
    family is exactly the global family from which
    `complexTorusLocalHolomorphicParameterCechData` is built.  Thus the
    classifier is available before descent, while the generic descended
    universal-property witness below remains conditional on an additional
    classification theorem for arbitrary global test families. -/

structure ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness) where
  classify : ∀ (F : ComplexTorusLocalHolomorphicParameterMap),
    MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily F)
  classify_map_eq_parameterPoint :
    ∀ (F : ComplexTorusLocalHolomorphicParameterMap)
      (C : MathlibFormal.GlobalHolomorphicFamilyClassification
        W.globalFamily
        (complexTorusLocalHolomorphicParameterGlobalFamily F)),
      C.map =
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
  classify_map_unique :
    ∀ (F : ComplexTorusLocalHolomorphicParameterMap)
      (C₁ C₂ : MathlibFormal.GlobalHolomorphicFamilyClassification
        W.globalFamily
        (complexTorusLocalHolomorphicParameterGlobalFamily F)),
      C₁.map = C₂.map

namespace ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily

noncomputable def fromLocalRestricted
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (U : ComplexTorusLocalRestrictedFineHolomorphicUniversalMarkedFamily) :
    ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W where
  classify := complexTorusLocalHolomorphicParameterGlobalClassification W
  classify_map_eq_parameterPoint := by
    intro F C
    let C' : MathlibFormal.HolomorphicFamilyClassification
        complexTorusMarkedSurfaceFamily (ComplexTorusLocalTestFamily F) :=
      { map := C.map
        map_continuous := C.map_continuous
        realization := by
          simpa [complexTorusLocalHolomorphicParameterGlobalFamily,
            ComplexTorusLocalTestFamily, W.family_eq,
            complexTorusMarkedSurfaceFamily_canonicalPullback_eq] using C.realization }
    have h := U.classify_map_eq_parameterPoint
      F C'
    exact h
  classify_map_unique := by
    intro F C₁ C₂
    let C₁' : MathlibFormal.HolomorphicFamilyClassification
        complexTorusMarkedSurfaceFamily (ComplexTorusLocalTestFamily F) :=
      { map := C₁.map
        map_continuous := C₁.map_continuous
        realization := by
          simpa [complexTorusLocalHolomorphicParameterGlobalFamily,
            ComplexTorusLocalTestFamily, W.family_eq,
            complexTorusMarkedSurfaceFamily_canonicalPullback_eq] using C₁.realization }
    let C₂' : MathlibFormal.HolomorphicFamilyClassification
        complexTorusMarkedSurfaceFamily (ComplexTorusLocalTestFamily F) :=
      { map := C₂.map
        map_continuous := C₂.map_continuous
        realization := by
          simpa [complexTorusLocalHolomorphicParameterGlobalFamily,
            ComplexTorusLocalTestFamily, W.family_eq,
            complexTorusMarkedSurfaceFamily_canonicalPullback_eq] using C₂.realization }
    exact U.classify_maps_unique F
      C₁' C₂'

theorem classify_map_eq_parameterPoint'
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (U : ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (C : MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily F)) :
    C.map = F.toComplexTorusHolomorphicParameterMap.parameterPoint :=
  U.classify_map_eq_parameterPoint F C

theorem classify_maps_unique
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (U : ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (C₁ C₂ : MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily F)) :
    C₁.map = C₂.map :=
  U.classify_map_unique F C₁ C₂

end ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily

noncomputable def complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily :
    ∀ W : ComplexTorusGlobalMarkedSurfaceFamilyWitness,
    ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W :=
  fun W =>
  ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.fromLocalRestricted W
    ComplexTorusLocalRestrictedFineHolomorphicUniversalMarkedFamily.fromLocalWitnesses

/-! The generic global fine-moduli interface has a strictly larger test
    category than the explicit torus maps used here.  Its safe specialization
    direction is nevertheless constructive: a generic universal object can be
    restricted to the torus test families, while the converse remains a real
    existence problem. -/

noncomputable def ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.ofGlobalFine
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (V : MathlibFormal.GlobalFineHolomorphicUniversalMarkedFamily W.globalFamily) :
    ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W where
  classify := fun F => V.universal (complexTorusLocalHolomorphicParameterGlobalFamily F)
  classify_map_eq_parameterPoint := by
    intro F C
    let C' : MathlibFormal.HolomorphicFamilyClassification
        complexTorusMarkedSurfaceFamily (ComplexTorusLocalTestFamily F) :=
      { map := C.map
        map_continuous := C.map_continuous
        realization := by
          simpa [complexTorusLocalHolomorphicParameterGlobalFamily,
            ComplexTorusLocalTestFamily, W.family_eq,
            complexTorusMarkedSurfaceFamily_canonicalPullback_eq] using C.realization }
    exact complexTorusLocalHolomorphicParameterClassification_map_eq_parameterPoint F C'
  classify_map_unique := by
    intro F C₁ C₂
    exact V.classify_unique (complexTorusLocalHolomorphicParameterGlobalFamily F) C₁ C₂

/-! The preceding restricted universal object records global classification
    maps and their uniqueness.  The next refinement quantifies the stronger
    ambient analytic witness as well.  It is still conditional on `W`, but it
    now matches the original Teichmüller arrow on the restricted test category:
    every test family has a global pullback realization, a unique classifying
    map, and an ambient `DifferentiableOn` certificate. -/

structure ComplexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness) where
  classify : ∀ (F : ComplexTorusLocalHolomorphicParameterMap),
    ComplexTorusLocalHolomorphicParameterGlobalClassificationWitness W F
  classify_map_eq_parameterPoint :
    ∀ (F : ComplexTorusLocalHolomorphicParameterMap),
      (classify F).classification.map =
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
  classify_map_unique :
    ∀ (F : ComplexTorusLocalHolomorphicParameterMap)
      (C₁ C₂ : MathlibFormal.GlobalHolomorphicFamilyClassification
        W.globalFamily
        (complexTorusLocalHolomorphicParameterGlobalFamily F)),
      C₁.map = C₂.map

noncomputable def complexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily :
    ∀ W : ComplexTorusGlobalMarkedSurfaceFamilyWitness,
    ComplexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily W :=
  fun W =>
    { classify := complexTorusLocalHolomorphicParameterGlobalClassificationWitness W
      classify_map_eq_parameterPoint := by
        intro F
        exact complexTorusLocalHolomorphicParameterGlobalClassification_map W F
      classify_map_unique := by
        intro F C₁ C₂
        exact ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.classify_maps_unique
          W (complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W)
          F C₁ C₂ }

theorem complexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily_classify_ambient_eq_precompose
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (complexTorusLocalRestrictedGlobalAnalyticFineUniversalMarkedFamily W |>.classify
      (F.precompose G hG)).ambientClassifyingMap =
      fun c => F.map (G.map c) := by
  rfl

theorem complexTorusLocalHolomorphicParameterCechClassification_map_eq_parameterPoint
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W |>.classify F).map =
      F.toComplexTorusHolomorphicParameterMap.parameterPoint := by
  exact ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.classify_map_eq_parameterPoint'
    W (complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W) F
    (complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W |>.classify F)

/-! The restricted global classifier is functorial under a holomorphic change of
    test base.  This is the global-atlas analogue of the family-only
    composition theorem in `MathlibTorus.lean`; it shows that the classifying
    map of any global witness is the actual composite parameter map. -/

theorem complexTorusLocalHolomorphicParameterGlobalClassification_map_eq_precompose
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (C : MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily
        (F.precompose G hG))) :
    C.map =
      (fun c : {c : ℂ // c ∈ G.domain} =>
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
          ⟨G.map (c : ℂ), hG c.2⟩) := by
  rw [ComplexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily.classify_map_eq_parameterPoint'
    W (complexTorusLocalRestrictedGlobalFineHolomorphicUniversalMarkedFamily W)
    (F.precompose G hG) C]
  funext c
  exact ComplexTorusLocalHolomorphicParameterMap.precompose_parameterPoint
    F G hG c

theorem complexTorusLocalHolomorphicParameterGlobalClassification_map_eq_precompose_precompose
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G H : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain)
    (hH : Set.MapsTo H.map H.domain G.domain)
    (C : MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      (complexTorusLocalHolomorphicParameterGlobalFamily
        ((F.precompose G hG).precompose H hH))) :
    C.map =
      (fun c : {c : ℂ // c ∈ H.domain} =>
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
          ⟨G.map (H.map (c : ℂ)), hG (hH c.2)⟩) := by
  rw [complexTorusLocalHolomorphicParameterGlobalClassification_map_eq_precompose
    W (F.precompose G hG) H hH C]
  funext c
  exact ComplexTorusLocalHolomorphicParameterMap.precompose_parameterPoint
    F G hG ⟨H.map c, hH c.2⟩

/-! The map-composition theorem can be backed by an actual global pullback
    atlas.  The only geometric input is the associativity homeomorphism for
    canonical pullbacks: it transports the already constructed direct atlas
    of `F.precompose G hG` to the iterated pullback of the `F`-family. -/

noncomputable def complexTorusLocalHolomorphicParameterGlobalPullbackWitness
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    (complexTorusLocalHolomorphicParameterGlobalFamily F).PullbackWitness
      (fun c : {c : ℂ // c ∈ G.domain} =>
        ⟨G.map (c : ℂ), hG c.2⟩)
      (by
        exact Continuous.subtype_mk
          (G.map_continuous.comp continuous_subtype_val)
          (fun c => hG c.2)) := by
  let f := F.toComplexTorusHolomorphicParameterMap.parameterPoint
  let g : {c : ℂ // c ∈ G.domain} →
      {b : ℂ // b ∈ F.domain} := fun c =>
    ⟨G.map (c : ℂ), hG c.2⟩
  have hf : Continuous f :=
    F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous
  have hg : Continuous g := by
    exact Continuous.subtype_mk
      (G.map_continuous.comp continuous_subtype_val)
      (fun c => hG c.2)
  let hassoc := ComplexSurfaceFamily.canonicalPullback_iterated_homeomorph
    complexTorusMarkedSurfaceFamily f g hf hg
  let A := complexTorusLocalHolomorphicParameterComplexSurfaceFamilyAtlas
    (F.precompose G hG)
  let Aiter := ComplexSurfaceAtlas.transport
    A.toComplexSurfaceAtlas hassoc
  refine
    { atlas :=
        { toComplexSurfaceAtlas := Aiter
          projection := fun x => x.1
          parameterCoordinate := fun c : {c : ℂ // c ∈ G.domain} => (c : ℂ)
          projection_continuous := by
            exact ComplexSurfaceFamily.pullback_projection_continuous
              (complexTorusLocalHolomorphicParameterGlobalFamily F).family g
          chart_base_coordinate := by
            intro i x hx
            have hxA : hassoc x ∈ (A.chart i).domain := by
              exact hx
            have hcoord := A.chart_base_coordinate i hxA
            have htransport := ComplexSurfaceChart.transport_chart_val
              (e := hassoc) (A := A.chart i) (x := x) (hx := hx)
            change
              ((ComplexSurfaceChart.transport hassoc (A.chart i)).chart
                ⟨x, hx⟩).1.1 = (x.1 : ℂ)
            calc
              ((ComplexSurfaceChart.transport hassoc (A.chart i)).chart
                  ⟨x, hx⟩).1.1 =
                  ((A.chart i).chart ⟨hassoc x, hxA⟩).1.1 := by
                exact congrArg Prod.fst htransport
              _ = (hassoc x).1.1 := hcoord
              _ = (x.1 : ℂ) := by
                rfl }
      cover_univ := by
        rw [ComplexSurfaceAtlas.transport_coverSet]
        change A.toComplexSurfaceAtlas.coverSet = Set.univ
        rfl
      topology_eq := by
        rfl
      projection_eq := by
        intro x
        rfl }

noncomputable def complexTorusLocalHolomorphicParameterGlobalSourcePullbackWitness
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    W.globalFamily.PullbackWitness
      (fun c : {c : ℂ // c ∈ G.domain} =>
        F.toComplexTorusHolomorphicParameterMap.parameterPoint
          ⟨G.map (c : ℂ), hG c.2⟩)
      (by
        have hF :=
          F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous
        have hG' : Continuous
            (fun c : {c : ℂ // c ∈ G.domain} =>
              (⟨G.map (c : ℂ), hG c.2⟩ : {b : ℂ // b ∈ F.domain})) := by
          exact Continuous.subtype_mk
            (G.map_continuous.comp continuous_subtype_val)
            (fun c => hG c.2)
        exact hF.comp hG') := by
  let f := F.toComplexTorusHolomorphicParameterMap.parameterPoint
  let g : {c : ℂ // c ∈ G.domain} →
      {b : ℂ // b ∈ F.domain} := fun c =>
    ⟨G.map (c : ℂ), hG c.2⟩
  have hf : Continuous f :=
    F.toComplexTorusHolomorphicParameterMap.parameterPoint_continuous
  have hg : Continuous g := by
    exact Continuous.subtype_mk
      (G.map_continuous.comp continuous_subtype_val)
      (fun c => hG c.2)
  have hfg : Continuous (fun c => f (g c)) := hf.comp hg
  have hPcomp :
      (complexTorusLocalHolomorphicParameterGlobalFamily
        (F.precompose G hG)).family =
        MathlibFormal.ComplexSurfaceFamily.canonicalPullback
          W.globalFamily.family (fun c => f (g c)) hfg := by
    change (complexTorusHolomorphicParameterPullback
      (F.precompose G hG).toComplexTorusHolomorphicParameterMap).toFamily = _
    rw [W.family_eq]
    exact (complexTorusMarkedSurfaceFamily_canonicalPullback_eq
      (F.precompose G hG).toComplexTorusHolomorphicParameterMap).symm
  let A := complexTorusLocalHolomorphicParameterComplexSurfaceFamilyAtlas
    (F.precompose G hG)
  let A_direct :
      @ComplexSurfaceFamilyAtlas
        (ComplexSurfaceFamily.Total
          (complexTorusLocalHolomorphicParameterGlobalFamily
            (F.precompose G hG)).family)
        {c : ℂ // c ∈ G.domain} inferInstance :=
    { toComplexSurfaceAtlas := A.toComplexSurfaceAtlas
      projection := fun x => x.1
      parameterCoordinate := fun c : {c : ℂ // c ∈ G.domain} => (c : ℂ)
      projection_continuous := by
        exact (complexTorusLocalHolomorphicParameterGlobalFamily
          (F.precompose G hG)).family.projection_continuous
      chart_base_coordinate := by
        intro i x hx
        exact A.chart_base_coordinate i hx }
  let A' :
      @ComplexSurfaceFamilyAtlas
        (ComplexSurfaceFamily.Total
          (MathlibFormal.ComplexSurfaceFamily.canonicalPullback
            W.globalFamily.family (fun c => f (g c)) hfg))
        {c : ℂ // c ∈ G.domain} inferInstance :=
    hPcomp ▸ A_direct
  have hcover_direct : A_direct.coverSet = Set.univ := by
    dsimp [A_direct]
    change A.toComplexSurfaceAtlas.coverSet = Set.univ
    rfl
  have htop_direct :
      A_direct.toComplexSurfaceAtlas.topology =
        (complexTorusLocalHolomorphicParameterGlobalFamily
          (F.precompose G hG)).family.totalTopology := by
    dsimp [A_direct]
    rfl
  have hprojection_direct : ∀ x,
      A_direct.projection x =
        MathlibFormal.ComplexSurfaceFamily.projection
          (complexTorusLocalHolomorphicParameterGlobalFamily
            (F.precompose G hG)).family x := by
    intro x
    rfl
  refine
    { atlas := A'
      cover_univ := ?_
      topology_eq := ?_
      projection_eq := ?_ }
  · dsimp [A']
    exact ComplexSurfaceFamilyAtlas.cast_cover_univ hPcomp A_direct hcover_direct
  · dsimp [A']
    exact ComplexSurfaceFamilyAtlas.cast_topology_eq hPcomp A_direct htop_direct
  · intro x
    dsimp [A']
    exact (ComplexSurfaceFamilyAtlas.cast_projection_eq hPcomp A_direct
      hprojection_direct) x

noncomputable def complexTorusLocalHolomorphicParameterGlobalClassification_pullbackWithWitness
    (W : ComplexTorusGlobalMarkedSurfaceFamilyWitness)
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (G : ComplexTorusHolomorphicParameterMap)
    (hG : Set.MapsTo G.map G.domain F.domain) :
    MathlibFormal.GlobalHolomorphicFamilyClassification
      W.globalFamily
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).pullbackOf
        (fun c : {c : ℂ // c ∈ G.domain} =>
          ⟨G.map (c : ℂ), hG c.2⟩)
        (by
          exact Continuous.subtype_mk
            (G.map_continuous.comp continuous_subtype_val)
            (fun c => hG c.2))
        (complexTorusLocalHolomorphicParameterGlobalPullbackWitness F G hG)) := by
  let g : {c : ℂ // c ∈ G.domain} →
      {b : ℂ // b ∈ F.domain} := fun c =>
    ⟨G.map (c : ℂ), hG c.2⟩
  have hg : Continuous g := by
    exact Continuous.subtype_mk
      (G.map_continuous.comp continuous_subtype_val)
      (fun c => hG c.2)
  let W_F := complexTorusLocalHolomorphicParameterGlobalPullbackWitness F G hG
  let W_U := complexTorusLocalHolomorphicParameterGlobalSourcePullbackWitness W F G hG
  have hmap :
      (complexTorusLocalHolomorphicParameterGlobalClassification W F).map =
        F.toComplexTorusHolomorphicParameterMap.parameterPoint := by
    exact complexTorusLocalHolomorphicParameterGlobalClassification_map W F
  let W_U' :
      W.globalFamily.PullbackWitness
        (fun d => (complexTorusLocalHolomorphicParameterGlobalClassification W F).map (g d))
        ((complexTorusLocalHolomorphicParameterGlobalClassification W F).map_continuous.comp hg) := by
    simpa [hmap] using W_U
  simpa [hmap] using
    (complexTorusLocalHolomorphicParameterGlobalClassification W F).pullbackWithWitness
      g hg W_F W_U'

theorem complexTorusLocalHolomorphicParameterGlobalFamily_fiber_no_global_plane
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (b : ComplexTorusLocalHolomorphicParameterBase F)
    (e : @Homeomorph ℂ
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).carrier
      inferInstance
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).topology) :
    False := by
  change ℂ ≃ₜ ComplexTorus (F.parameterPoint b) at e
  exact complexTorus_has_no_global_complex_plane_homeomorph
    (F.parameterPoint b) e

noncomputable def complexTorusLocalHolomorphicParameterCompactCechData
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    CompactFiberHolomorphicCechDescentData
      (S := ComplexTorus complexTorusBaseParameter)
      (B := ComplexTorusLocalHolomorphicParameterBase F)
      (I := ℂ) := by
  refine
    { toHolomorphicCechDescentData :=
        complexTorusLocalHolomorphicParameterCechData F
      compact_fiber := ?_ }
  intro c b
  exact complexTorusLocalHolomorphicParameterGlobalFamily_fiber_compact
    F b

noncomputable def complexTorusLocalHolomorphicParameterCechDescendedFiberCompactnessWitness
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : ℂ)
    (b : (complexTorusLocalHolomorphicParameterCechData F).cover c) :
    DescendedFiberCompactnessWitness
      (complexTorusLocalHolomorphicParameterCechData F)
      (b : ComplexTorusLocalHolomorphicParameterBase F) := by
  let D := complexTorusLocalHolomorphicParameterCompactCechData F
  let hquot :=
    isOpenMap_quotientMk_of_openGluing
      (complexTorusLocalHolomorphicParameterCechData F)
      (multiPatchOpenGluingWitness
        (complexTorusLocalHolomorphicParameterGlobalFamily F)
        (complexTorusLocalHolomorphicParameterCechCover F)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
        (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F))
  exact
    DescendedFiberCompactnessWitness.of_localFiberTopologyComparison
      D c b hquot
      (complexTorusCechLocalFiberTopologyComparison F c b)

@[reducible] noncomputable def complexTorusLocalHolomorphicParameterCechDescendedFiberCompact
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (c : ℂ)
    (b : (complexTorusLocalHolomorphicParameterCechData F).cover c) :
    @CompactSpace
      (DescendedFiber
        (complexTorusLocalHolomorphicParameterCechData F)
        (b : ComplexTorusLocalHolomorphicParameterBase F))
      (instDescendedFiberTopology
        (complexTorusLocalHolomorphicParameterCechData F)
        (b : ComplexTorusLocalHolomorphicParameterBase F)) := by
  let D := complexTorusLocalHolomorphicParameterCompactCechData F
  let W :=
    complexTorusLocalHolomorphicParameterCechDescendedFiberCompactnessWitness
      F c b
  exact
    DescendedFiberCompactnessWitness.compactSpace_of_local D
      (b : ComplexTorusLocalHolomorphicParameterBase F) W

@[reducible] noncomputable def complexTorusLocalHolomorphicParameterCechDescendedFiberCompactAt
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (b : ComplexTorusLocalHolomorphicParameterBase F) :
    @CompactSpace
      (DescendedFiber
        (complexTorusLocalHolomorphicParameterCechData F) b)
      (instDescendedFiberTopology
        (complexTorusLocalHolomorphicParameterCechData F) b) := by
  let bc : (complexTorusLocalHolomorphicParameterCechData F).cover (b : ℂ) :=
    ⟨b, by
      change dist (b : ℂ) (b : ℂ) < (1 : ℝ) / 4
      norm_num⟩
  exact complexTorusLocalHolomorphicParameterCechDescendedFiberCompact F
    (b : ℂ) bc

noncomputable def complexTorusLocalHolomorphicParameterCechTransition
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    JointlyHolomorphicTransitionData
      (complexTorusLocalHolomorphicParameterCechData F) :=
  multiPatchJointlyHolomorphicTransition
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)

theorem complexTorusLocalHolomorphicParameterCechTransition_comp_apply
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j k : ℂ)
    (x : CechTripleOverlap
      (complexTorusLocalHolomorphicParameterCechData F).cover i j k)
    (z : (((complexTorusLocalHolomorphicParameterCechData F).localFamily i).family.fiber
      (CechOverlap.leftPoint
        (complexTorusLocalHolomorphicParameterCechData F).cover i j
        (CechTripleOverlap.toIJ
          (complexTorusLocalHolomorphicParameterCechData F).cover i j k x))).carrier) :
    (complexTorusLocalHolomorphicParameterCechTransition F).toFun i k
        ⟨CechTripleOverlap.toIK
          (complexTorusLocalHolomorphicParameterCechData F).cover i j k x, z⟩ =
      ⟨CechTripleOverlap.toIK
          (complexTorusLocalHolomorphicParameterCechData F).cover i j k x,
        (complexTorusLocalHolomorphicParameterCechData F).transition j k
          (CechTripleOverlap.toJK
            (complexTorusLocalHolomorphicParameterCechData F).cover i j k x)
          ((complexTorusLocalHolomorphicParameterCechData F).transition i j
            (CechTripleOverlap.toIJ
              (complexTorusLocalHolomorphicParameterCechData F).cover i j k x) z)⟩ := by
  exact JointlyContinuousTransitionData.toFun_comp_apply
    (complexTorusLocalHolomorphicParameterCechTransition F).toContinuous
    i j k x z

/-!
  A compact torus cannot be represented by one global coordinate with target
  `ℂ`.  The correct local analytic certificate therefore lives on the lifted
  two-dimensional charts and records the deck descent explicitly.  This
  structure is the compact-fibre replacement for the overly strong
  `LocalJointlyHolomorphicFamily` interface: it asks for a genuine joint
  holomorphic lift and holomorphic transition sheets, but only locally in the
  fibre direction.
-/

structure ComplexTorusLocalJointlyHolomorphicLiftWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  localChart : ∀ _ : ℂ,
    @MathlibFormal.ComplexSurfaceChart
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus (F.parameterPoint b)))
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  localChart_cover : ∀ x,
    ∃ c : ℂ, x ∈ (localChart c).domain
  localChart_base_coordinate : ∀ (c : ℂ) {x}
      (hx : x ∈ (localChart c).domain),
    ((localChart c).chart ⟨x, hx⟩).1.1 = (x.1 : ℂ)
  localChart_transition_differentiableOn : ∀ c₁ c₂ : ℂ,
    DifferentiableOn ℂ
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (localChart c₁) (localChart c₂))
      (MathlibFormal.ComplexSurfaceChart.overlap
        (localChart c₁) (localChart c₂))
  liftCoordinate : ℂ × ℂ → ℂ
  liftCoordinate_eq_snd : ∀ (τ z : ℂ),
    liftCoordinate (τ, z) = z
  liftCoordinate_differentiable : Differentiable ℂ liftCoordinate
  deckHomeomorph : ℤ × ℤ → (ℂ × ℂ) ≃ₜ (ℂ × ℂ)
  deckHomeomorph_apply : ∀ (mn : ℤ × ℤ) (p : ℂ × ℂ),
    deckHomeomorph mn p =
      (p.1, p.2 + (mn.1 : ℂ) + (mn.2 : ℂ) * F.map p.1)
  deckHomeomorph_differentiableOn : ∀ c₁ c₂ : ℂ, ∀ m n : ℤ,
    DifferentiableOn ℂ (deckHomeomorph (m, n))
      (complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n)
  deckHomeomorph_cocycle : ∀ (mn pq : ℤ × ℤ) (p : ℂ × ℂ),
    deckHomeomorph (mn.1 + pq.1, mn.2 + pq.2) p =
      deckHomeomorph mn (deckHomeomorph pq p)
  deckHomeomorph_descends : ∀ (mn : ℤ × ℤ)
      (p : ComplexTorusLocalHolomorphicParameterBase F × ℂ),
    complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap
        ⟨p.1,
          complexTorusMk (F.parameterPoint p.1)
            ((deckHomeomorph mn (p.1, p.2)).2)⟩ =
      complexTorusHolomorphicParameterPullback_toTotal
        F.toComplexTorusHolomorphicParameterMap
        ⟨p.1, complexTorusMk (F.parameterPoint p.1) p.2⟩

noncomputable def complexTorusLocalJointlyHolomorphicLiftWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusLocalJointlyHolomorphicLiftWitness F where
  localChart := complexTorusLocalHolomorphicParameterSurfaceChart F
  localChart_cover := by
    intro x
    have hx : x ∈ ⋃ c : ℂ,
        complexTorusHolomorphicParameterPullbackLocalImageAt F c := by
      rw [complexTorusHolomorphicParameterPullbackLocalImageAt_union F]
      trivial
    rcases Set.mem_iUnion.mp hx with ⟨c, hxc⟩
    exact ⟨c, hxc⟩
  localChart_base_coordinate := by
    intro c x hx
    exact complexTorusLocalHolomorphicParameterSurfaceChart_chart_base_coordinate
      F c hx
  localChart_transition_differentiableOn := by
    intro c₁ c₂
    exact complexTorusLocalHolomorphicParameterSurfaceChart_transition_differentiableOn
      F c₁ c₂
  liftCoordinate := complexTorusAmbientLiftCoordinate
  liftCoordinate_eq_snd := by
    intro τ z
    rfl
  liftCoordinate_differentiable := complexTorusAmbientLiftCoordinate_differentiable
  deckHomeomorph := fun mn =>
    complexTorusLocalHolomorphicParameterDeckHomeomorph F mn.1 mn.2
  deckHomeomorph_apply := by
    intro mn p
    exact complexTorusLocalHolomorphicParameterDeckHomeomorph_apply
      F mn.1 mn.2 p
  deckHomeomorph_differentiableOn := by
    intro c₁ c₂ m n
    exact (complexTorusLocalHolomorphicParameterDeckTransitionSheet
      F c₁ c₂ m n).differentiableOn
  deckHomeomorph_cocycle := by
    intro mn pq p
    exact complexTorusLocalHolomorphicParameterDeckHomeomorph_add_apply
      F mn pq p
  deckHomeomorph_descends := by
    intro mn p
    simpa [complexTorusLocalHolomorphicParameterDeckHomeomorph_apply] using
      complexTorusLocalHolomorphicParameterDeckAddAction_invariant
        F mn p

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toComplexSurfaceAtlas
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F) :
    MathlibFormal.ComplexSurfaceAtlas
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus (F.parameterPoint b))) :=
  { toComplexSurfaceChartFamily :=
      { topology :=
          (complexTorusHolomorphicParameterPullback
            F.toComplexTorusHolomorphicParameterMap).family.totalTopology
        index := ℂ
        chart := W.localChart
        coverSet := Set.univ
        covers := by
          intro x _
          rcases W.localChart_cover x with ⟨c, hc⟩
          exact ⟨c, hc⟩ }
    transition_differentiableOn := W.localChart_transition_differentiableOn }

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toComplexSurfaceFamilyAtlas
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F) :
    @MathlibFormal.ComplexSurfaceFamilyAtlas
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus (F.parameterPoint b)))
      (ComplexTorusLocalHolomorphicParameterBase F) inferInstance where
  toComplexSurfaceAtlas := W.toComplexSurfaceAtlas
  projection := fun x => x.1
  parameterCoordinate := fun b => (b : ℂ)
  projection_continuous := by
    exact (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.projection_continuous
  chart_base_coordinate := W.localChart_base_coordinate

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toGlobalFamily
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F) :
    @MathlibFormal.ComplexSurfaceFamily.GlobalHolomorphicMarkedFamily
      (ComplexTorus complexTorusBaseParameter)
      (ComplexTorusLocalHolomorphicParameterBase F)
      inferInstance inferInstance where
  family := (complexTorusLocalHolomorphicParameterGlobalFamily F).family
  atlas := W.toComplexSurfaceFamilyAtlas
  cover_univ := by
    rfl
  topology_eq := by
    change W.toComplexSurfaceAtlas.topology =
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
    rfl
  projection_eq := by
    intro x
    rfl

theorem ComplexTorusLocalJointlyHolomorphicLiftWitness.toGlobalFamily_eq_named
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalJointlyHolomorphicLiftWitness F).toGlobalFamily =
      complexTorusLocalHolomorphicParameterGlobalFamily F := by
  rfl

/-! The preceding conversion is now consumed by the generic Čech pipeline.
    These wrappers are intentionally thin: they do not postulate a second
    cocycle or a second descent theorem, but expose that the concrete torus
    lift/deck certificate is an admissible input to the already proved
    restriction, overlap, gluing, and descended-atlas constructions. -/

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechData
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F)
    {I : Type*} (cover : I → Set (ComplexTorusLocalHolomorphicParameterBase F))
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    HolomorphicCechDescentData
      (ComplexTorus complexTorusBaseParameter)
      (ComplexTorusLocalHolomorphicParameterBase F) I :=
  multiPatchCechDescentData W.toGlobalFamily cover cover_open cover_univ

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechTransition
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F)
    {I : Type*} (cover : I → Set (ComplexTorusLocalHolomorphicParameterBase F))
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    JointlyHolomorphicTransitionData
      (W.toCechData cover cover_open cover_univ) :=
  multiPatchJointlyHolomorphicTransition
    W.toGlobalFamily cover cover_open cover_univ

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechOpenGluing
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F)
    {I : Type*} (cover : I → Set (ComplexTorusLocalHolomorphicParameterBase F))
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    OpenGluingWitness (W.toCechData cover cover_open cover_univ) :=
  multiPatchOpenGluingWitness
    W.toGlobalFamily cover cover_open cover_univ

noncomputable def ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechDescendedAtlas
    (W : ComplexTorusLocalJointlyHolomorphicLiftWitness F)
    {I : Type*} (cover : I → Set (ComplexTorusLocalHolomorphicParameterBase F))
    (cover_open : ∀ i, IsOpen (cover i))
    (cover_univ : ⋃ i, cover i = Set.univ) :
    DescendedAtlasHolomorphicWitness
      (W.toCechData cover cover_open cover_univ)
      (isOpenMap_quotientMk_of_openGluing
        (W.toCechData cover cover_open cover_univ)
        (W.toCechOpenGluing cover cover_open cover_univ)) :=
  multiPatchDescendedAtlasHolomorphicWitness
    W.toGlobalFamily cover cover_open cover_univ

theorem complexTorusLocalJointlyHolomorphicLiftWitness.transition_is_holomorphic
    (F : ComplexTorusLocalHolomorphicParameterMap) (c₁ c₂ : ℂ) :
    DifferentiableOn ℂ
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        ((complexTorusLocalJointlyHolomorphicLiftWitness F).localChart c₁)
        ((complexTorusLocalJointlyHolomorphicLiftWitness F).localChart c₂))
      (MathlibFormal.ComplexSurfaceChart.overlap
        ((complexTorusLocalJointlyHolomorphicLiftWitness F).localChart c₁)
        ((complexTorusLocalJointlyHolomorphicLiftWitness F).localChart c₂)) :=
  (complexTorusLocalJointlyHolomorphicLiftWitness F).localChart_transition_differentiableOn
    c₁ c₂

noncomputable def complexTorusLocalHolomorphicParameterCechDescendedAtlas
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    DescendedAtlasHolomorphicWitness
      (complexTorusLocalHolomorphicParameterCechData F)
      (isOpenMap_quotientMk_of_openGluing
        (complexTorusLocalHolomorphicParameterCechData F)
        (multiPatchOpenGluingWitness
          (complexTorusLocalHolomorphicParameterGlobalFamily F)
          (complexTorusLocalHolomorphicParameterCechCover F)
          (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
          (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F))) :=
  multiPatchDescendedAtlasHolomorphicWitness
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)

noncomputable def complexTorusLocalHolomorphicParameterCechDescendedFamilyAtlas
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    @ComplexSurfaceFamilyAtlas
      (DescendedTotal (complexTorusLocalHolomorphicParameterCechData F))
      (ComplexTorusLocalHolomorphicParameterBase F) inferInstance :=
  multiPatchDescendedFamilyAtlas
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)

noncomputable def complexTorusLocalHolomorphicParameterCechDescendedMarkedAtlas
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    DescendedMarkedAtlas
      (complexTorusLocalHolomorphicParameterCechData F) :=
  multiPatchDescendedMarkedAtlas
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)

theorem ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechData_eq_named
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalJointlyHolomorphicLiftWitness F).toCechData
        (complexTorusLocalHolomorphicParameterCechCover F)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
        (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F) =
      complexTorusLocalHolomorphicParameterCechData F := by
  rfl

theorem ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechTransition_eq_named
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalJointlyHolomorphicLiftWitness F).toCechTransition
        (complexTorusLocalHolomorphicParameterCechCover F)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
        (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F) =
      complexTorusLocalHolomorphicParameterCechTransition F := by
  rfl

theorem ComplexTorusLocalJointlyHolomorphicLiftWitness.toCechDescendedAtlas_eq_named
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    (complexTorusLocalJointlyHolomorphicLiftWitness F).toCechDescendedAtlas
        (complexTorusLocalHolomorphicParameterCechCover F)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
        (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F) =
      complexTorusLocalHolomorphicParameterCechDescendedAtlas F := by
  rfl

/-! The generic local-comparison interface cannot be instantiated for the
    compact torus family: its predecessor
    `CechJointlyHolomorphicVariationWitness` contains a homeomorphism from the
    global model fibre `ℂ` to every local fibre.  The following theorem makes
    that type-level obstruction executable on the identity test family. -/

theorem complexTorusLocalCechVariation_no_global_plane_model
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (b : ComplexTorusLocalHolomorphicParameterBase F) :
    ¬ Nonempty
      (CechJointlyHolomorphicVariationWitness
        (complexTorusLocalHolomorphicParameterCechData F)) := by
  rintro ⟨W⟩
  let D := complexTorusLocalHolomorphicParameterCechData F
  let c : ℂ := (b : ℂ)
  have hb : b ∈ complexTorusLocalHolomorphicParameterCechCover F c := by
    change dist (b : ℂ) c < (1 : ℝ) / 4
    simp [c]
  let i : ℂ := c
  let b' : D.cover i := ⟨b, hb⟩
  have hchart := W.baseChart_covers i b'
  let e := (W.localVariation i).fiberEquiv b' hchart
  rw [W.localFamily_eq i] at e
  change @Homeomorph ℂ
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).carrier
      inferInstance
      ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber b).topology at e
  exact complexTorusLocalHolomorphicParameterGlobalFamily_fiber_no_global_plane F b e

theorem complexTorusIdentityCechVariation_no_global_plane_model :
    ¬ Nonempty
      (CechJointlyHolomorphicVariationWitness
        (complexTorusLocalHolomorphicParameterCechData
          complexTorusIdentityLocalHolomorphicParameterMap)) := by
  exact complexTorusLocalCechVariation_no_global_plane_model
    complexTorusIdentityLocalHolomorphicParameterMap
    ⟨Complex.I, complexTorusLocalParameterNeighborhood_contains_base⟩

/-! The generic multi-patch construction already produces genuine source and
    target overlap atlases on the compact-fibre quotient.  The following
    torus-specialized lemmas expose that construction at the same named
    boundary as the lifted/deck witness.  In particular, they do not replace
    the compact fibre by a global plane: the atlases remain charts on the
    actual overlap total spaces. -/

theorem complexTorusLocalCechOverlapAtlas_targetTransport
    (F : ComplexTorusLocalHolomorphicParameterMap) (i j : ℂ) :
    overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j =
      ComplexSurfaceAtlas.transport
        (overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j)
        (multiPatchJointlyTransitionHomeomorphInv
          (complexTorusLocalHolomorphicParameterGlobalFamily F)
          (complexTorusLocalHolomorphicParameterCechCover F)
          (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
          (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
          i j) := by
  exact multiPatchOverlapAtlas_eq_targetTransport
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
    i j

theorem complexTorusLocalCechOverlapAtlas_source_transition_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap) (i j : ℂ)
    (c d :
      (overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d)) :=
  overlapSourceAtlas_transition_differentiableOn
    (complexTorusLocalHolomorphicParameterCechData F) i j c d

theorem complexTorusLocalCechOverlapAtlas_target_transition_differentiableOn
    (F : ComplexTorusLocalHolomorphicParameterMap) (i j : ℂ)
    (c d :
      (overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).index) :
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d)) :=
  overlapTargetAtlas_transition_differentiableOn
    (complexTorusLocalHolomorphicParameterCechData F) i j c d

theorem complexTorusLocalCechOverlapAtlas_local_coordinate_agreement
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j : ℂ)
    (k :
      (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (p : CechOverlap
      (complexTorusLocalHolomorphicParameterCechCover F) i j)
    (y : ((complexTorusLocalHolomorphicParameterGlobalFamily F).family.fiber
      ((CechOverlap.rightPoint
        (complexTorusLocalHolomorphicParameterCechCover F) i j p :
          (complexTorusLocalHolomorphicParameterCechCover F) j) :
        ComplexTorusLocalHolomorphicParameterBase F)).carrier)
    (ht : overlapTargetFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j ⟨p, y⟩ ∈
      (((complexTorusLocalHolomorphicParameterGlobalFamily F).restrictBaseOpen
        (complexTorusLocalHolomorphicParameterCechCover F j)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F j)).atlas.chart
          k).domain)
    (hs : overlapSourceFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j ⟨p, y⟩ ∈
      (((complexTorusLocalHolomorphicParameterGlobalFamily F).restrictBaseOpen
        (complexTorusLocalHolomorphicParameterCechCover F i)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F i)).atlas.chart
          k).domain) :
    ((((complexTorusLocalHolomorphicParameterGlobalFamily F).restrictBaseOpen
        (complexTorusLocalHolomorphicParameterCechCover F j)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F j)).atlas.chart
          k).chart
      ⟨overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j ⟨p, y⟩, ht⟩).1 =
    ((((complexTorusLocalHolomorphicParameterGlobalFamily F).restrictBaseOpen
        (complexTorusLocalHolomorphicParameterCechCover F i)
        (complexTorusLocalHolomorphicParameterCechCover_isOpen F i)).atlas.chart
          k).chart
      ⟨overlapSourceFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j ⟨p, y⟩, hs⟩).1 := by
  exact multiPatchOverlap_local_coord
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
    i j k p y ht hs

/-! For the torus family the generic source-overlap comparison lands in the
    already constructed lifted surface chart.  This is the first pointwise
    commuting square between the quotient overlap atlas and a chosen lift;
    the remaining sheet index is supplied by the deck-sheet theorem below. -/

theorem complexTorusLocalCechOverlapAtlas_source_chart_eq_lift_chart
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j : ℂ)
    (c : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (z : CechOverlapSourceTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j)
    (hz : z ∈
      ((overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).domain)
    (hx : overlapSourceFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
      (((complexTorusLocalHolomorphicParameterCechData F).localFamily i).atlas.chart c).domain)
    (hxo :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family
        (complexTorusLocalHolomorphicParameterCechCover F i)
        (overlapSourceFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
        ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c).domain) ) :
    (((overlapSourceAtlas
      (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).chart
      ⟨z, hz⟩).1 =
      ((complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
        ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
            (complexTorusLocalHolomorphicParameterGlobalFamily F).family
            (complexTorusLocalHolomorphicParameterCechCover F i)
            (overlapSourceFibreMap
              (complexTorusLocalHolomorphicParameterCechData F) i j z)).1,
          hxo⟩).1 := by
  exact multiPatchOverlapSourceChart_apply_val_eq_global
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
    i j c z hz hx hxo

theorem complexTorusLocalCechOverlapAtlas_target_chart_eq_lift_chart
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j : ℂ)
    (c : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (z : CechOverlapTargetTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j)
    (hz : z ∈
      ((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).domain)
    (hx : overlapTargetFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
      (((complexTorusLocalHolomorphicParameterCechData F).localFamily j).atlas.chart c).domain)
    (hxo :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family
        (complexTorusLocalHolomorphicParameterCechCover F j)
        (overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
        ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c).domain) ) :
    (((overlapTargetAtlas
      (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).chart
      ⟨z, hz⟩).1 =
      ((complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
        ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
            (complexTorusLocalHolomorphicParameterGlobalFamily F).family
            (complexTorusLocalHolomorphicParameterCechCover F j)
            (overlapTargetFibreMap
              (complexTorusLocalHolomorphicParameterCechData F) i j z)).1,
          hxo⟩).1 := by
  exact multiPatchOverlapTargetChart_apply_val_eq_global
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
    i j c z hz hx hxo

structure ComplexTorusCompactFiberCechLiftCoordinateWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  source_chart_eq_lift_chart : ∀
    (i j : ℂ)
    (c : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (z : CechOverlapSourceTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j),
    ∀ (hz : z ∈
      ((overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).domain)
      (hx : overlapSourceFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
        (((complexTorusLocalHolomorphicParameterCechData F).localFamily i).atlas.chart c).domain)
      (hxo :
        ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
          (complexTorusLocalHolomorphicParameterGlobalFamily F).family
          (complexTorusLocalHolomorphicParameterCechCover F i)
          (overlapSourceFibreMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
          ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c).domain) ),
      (((overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).chart
        ⟨z, hz⟩).1 =
        ((complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
          ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
              (complexTorusLocalHolomorphicParameterGlobalFamily F).family
              (complexTorusLocalHolomorphicParameterCechCover F i)
              (overlapSourceFibreMap
                (complexTorusLocalHolomorphicParameterCechData F) i j z)).1,
            hxo⟩).1
  target_chart_eq_lift_chart : ∀
    (i j : ℂ)
    (c : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (z : CechOverlapTargetTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j),
    ∀ (hz : z ∈
      ((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).domain)
      (hx : overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
        (((complexTorusLocalHolomorphicParameterCechData F).localFamily j).atlas.chart c).domain)
      (hxo :
        ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
          (complexTorusLocalHolomorphicParameterGlobalFamily F).family
          (complexTorusLocalHolomorphicParameterCechCover F j)
          (overlapTargetFibreMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
          ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c).domain) ),
      (((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c).chart
        ⟨z, hz⟩).1 =
        ((complexTorusLocalHolomorphicParameterSurfaceChart F c).chart
          ⟨(ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
              (complexTorusLocalHolomorphicParameterGlobalFamily F).family
              (complexTorusLocalHolomorphicParameterCechCover F j)
              (overlapTargetFibreMap
                (complexTorusLocalHolomorphicParameterCechData F) i j z)).1,
            hxo⟩).1

noncomputable def complexTorusCompactFiberCechLiftCoordinateWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusCompactFiberCechLiftCoordinateWitness F where
  source_chart_eq_lift_chart := by
    intro i j c z hz hx hxo
    exact complexTorusLocalCechOverlapAtlas_source_chart_eq_lift_chart
      F i j c z hz hx hxo
  target_chart_eq_lift_chart := by
    intro i j c z hz hx hxo
    exact complexTorusLocalCechOverlapAtlas_target_chart_eq_lift_chart
      F i j c z hz hx hxo

/-! In the concrete multi-patch torus datum, the source point and its
    Čech-transported target point represent the same point of the global
    pullback total space.  This is the equality needed before invoking the
    lifted surface-chart overlap. -/

theorem complexTorusLocalCechOverlap_sourceGlobalPoint_eq_targetGlobalPoint
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j : ℂ)
    (z : CechOverlapSourceTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j) :
    (ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
      (complexTorusLocalHolomorphicParameterGlobalFamily F).family
      (complexTorusLocalHolomorphicParameterCechCover F i)
      (overlapSourceFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 =
      (ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family
        (complexTorusLocalHolomorphicParameterCechCover F j)
        (overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j
          (overlapTransitionMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z))).1 := by
  rcases z with ⟨p, y⟩
  rfl

/-! The preceding ingredients now compose into the desired quotient-side
    statement: on every common pair of source/target overlap charts, the
    target quotient coordinate is one explicit deck transform of the source
    quotient coordinate.  The sheet index is not postulated; it is obtained
    from the lifted chart-overlap cover. -/

theorem complexTorusLocalCechOverlapAtlas_transition_eq_deck_at
    (F : ComplexTorusLocalHolomorphicParameterMap)
    (i j : ℂ)
    (c₁ c₂ : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
    (z : CechOverlapSourceTotal
      (complexTorusLocalHolomorphicParameterCechData F) i j)
    (hz : z ∈
      ((overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).domain)
    (hzt : overlapTransitionMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
      ((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).domain)
    (hxs : overlapSourceFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
      (((complexTorusLocalHolomorphicParameterCechData F).localFamily i).atlas.chart c₁).domain)
    (hxt : overlapTargetFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j
        (overlapTransitionMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z) ∈
      (((complexTorusLocalHolomorphicParameterCechData F).localFamily j).atlas.chart c₂).domain)
    (hxo₁ :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family
        (complexTorusLocalHolomorphicParameterCechCover F i)
        (overlapSourceFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
        ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c₁).domain) )
    (hxo₂ :
      ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
        (complexTorusLocalHolomorphicParameterGlobalFamily F).family
        (complexTorusLocalHolomorphicParameterCechCover F j)
        (overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j
          (overlapTransitionMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z))).1 ∈
        ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c₂).domain) ) :
    ∃ mn : ℤ × ℤ,
      (((overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
          ⟨z, hz⟩).1 ∈
        complexTorusLocalHolomorphicParameterDeckOverlap
          F c₁ c₂ mn.1 mn.2 ∧
      (((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
          ⟨overlapTransitionMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z, hzt⟩).1 =
        complexTorusLocalHolomorphicParameterDeckHomeomorph F mn.1 mn.2
          (((overlapSourceAtlas
            (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
            ⟨z, hz⟩).1 := by
  let x₁ :=
    (ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
      (complexTorusLocalHolomorphicParameterGlobalFamily F).family
      (complexTorusLocalHolomorphicParameterCechCover F i)
      (overlapSourceFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z)).1
  let z₂ := overlapTransitionMap
    (complexTorusLocalHolomorphicParameterCechData F) i j z
  let x₂ :=
    (ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
      (complexTorusLocalHolomorphicParameterGlobalFamily F).family
      (complexTorusLocalHolomorphicParameterCechCover F j)
      (overlapTargetFibreMap
        (complexTorusLocalHolomorphicParameterCechData F) i j z₂)).1
  have hxEq : x₁ = x₂ := by
    exact complexTorusLocalCechOverlap_sourceGlobalPoint_eq_targetGlobalPoint
      F i j z
  have hsLift :=
    complexTorusLocalCechOverlapAtlas_source_chart_eq_lift_chart
      F i j c₁ z hz hxs hxo₁
  have htLift :=
    complexTorusLocalCechOverlapAtlas_target_chart_eq_lift_chart
      F i j c₂ z₂ hzt hxt hxo₂
  have hxo₂' : x₁ ∈
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₂).domain := by
    rw [hxEq]
    exact hxo₂
  have htLift' :
      (((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
          ⟨z₂, hzt⟩).1 =
        ((complexTorusLocalHolomorphicParameterSurfaceChart F c₂).chart
          ⟨x₁, hxo₂'⟩).1 := by
    calc
      (((overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
          ⟨z₂, hzt⟩).1 =
          ((complexTorusLocalHolomorphicParameterSurfaceChart F c₂).chart
            ⟨x₂, hxo₂⟩).1 := htLift
      _ = ((complexTorusLocalHolomorphicParameterSurfaceChart F c₂).chart
            ⟨x₁, hxo₂'⟩).1 := by
        have hsub :
            (⟨x₂, hxo₂⟩ :
              {x // x ∈
                (complexTorusLocalHolomorphicParameterSurfaceChart F c₂).domain}) =
            ⟨x₁, hxo₂'⟩ := by
          apply Subtype.ext
          exact hxEq.symm
        exact congrArg
          (fun q =>
            ((complexTorusLocalHolomorphicParameterSurfaceChart F c₂).chart q).1)
          hsub
  letI : TopologicalSpace
      (Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b))) :=
    (complexTorusHolomorphicParameterPullback
      F.toComplexTorusHolomorphicParameterMap).family.totalTopology
  let W : CompactFiberLiftToCechComparisonWitness
      (P := PUnit)
      (X := Sigma (fun b : {b : ℂ // b ∈ F.domain} =>
        ComplexTorus (F.parameterPoint b)))
      (M := ℤ × ℤ)
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) :=
    { liftPoint := fun _ => x₁
      sourceDomain := by
        intro _
        exact hxo₁
      targetDomain := by
        intro _
        exact hxo₂'
      sourceCoordinate := fun _ =>
        (((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
            ⟨z, hz⟩).1
      targetCoordinate := fun _ =>
        (((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
            ⟨z₂, hzt⟩).1
      sourceCoordinate_eq_lift := by
        intro _
        exact hsLift
      targetCoordinate_eq_lift := by
        intro _
        exact htLift'
      deckCover := complexTorusLocalHolomorphicParameterDeckTransitionCover
        F c₁ c₂ }
  let q : {p : ℂ × ℂ // p ∈
      MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂)} :=
    ⟨W.sourceCoordinate PUnit.unit,
      W.sourceCoordinate_mem_overlap PUnit.unit⟩
  let mn := W.deckCover.sheetSelector q
  have hmn : W.sourceCoordinate PUnit.unit ∈
      (W.deckCover.sheet mn).source := by
    exact W.deckCover.sheetSelector_mem q
  have hdeck := W.targetCoordinate_eq_selectedDeckMap
    (complexTorusLocalHolomorphicParameterDeckOverlap_pairwise_disjoint F c₁ c₂)
    PUnit.unit
  refine ⟨mn, hmn, ?_⟩
  change (((overlapTargetAtlas
      (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
        ⟨z₂, hzt⟩).1 =
      complexTorusLocalHolomorphicParameterDeckHomeomorph F mn.1 mn.2
        (((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
            ⟨z, hz⟩).1
  exact hdeck

structure ComplexTorusCompactFiberCechDeckComparisonWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  transition_eq_deck_at :
    ∀ (i j : ℂ)
      (c₁ c₂ : (complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.index)
      (z : CechOverlapSourceTotal
        (complexTorusLocalHolomorphicParameterCechData F) i j),
      (hz : z ∈
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).domain) →
      (hzt : overlapTransitionMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).domain) →
      (hxs : overlapSourceFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j z ∈
        (((complexTorusLocalHolomorphicParameterCechData F).localFamily i).atlas.chart c₁).domain) →
      (hxt : overlapTargetFibreMap
          (complexTorusLocalHolomorphicParameterCechData F) i j
          (overlapTransitionMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z) ∈
        (((complexTorusLocalHolomorphicParameterCechData F).localFamily j).atlas.chart c₂).domain) →
      (hxo₁ :
        ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
          (complexTorusLocalHolomorphicParameterGlobalFamily F).family
          (complexTorusLocalHolomorphicParameterCechCover F i)
          (overlapSourceFibreMap
            (complexTorusLocalHolomorphicParameterCechData F) i j z)).1 ∈
              ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c₁).domain) ) →
      (hxo₂ :
        ((ComplexSurfaceFamily.canonicalPullback_subtype_homeomorph
          (complexTorusLocalHolomorphicParameterGlobalFamily F).family
          (complexTorusLocalHolomorphicParameterCechCover F j)
          (overlapTargetFibreMap
            (complexTorusLocalHolomorphicParameterCechData F) i j
            (overlapTransitionMap
              (complexTorusLocalHolomorphicParameterCechData F) i j z))).1 ∈
              ((complexTorusLocalHolomorphicParameterGlobalFamily F).atlas.chart c₂).domain) ) →
      ∃ mn : ℤ × ℤ,
        (((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
            ⟨z, hz⟩).1 ∈
          complexTorusLocalHolomorphicParameterDeckOverlap
            F c₁ c₂ mn.1 mn.2 ∧
        (((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₂).chart
            ⟨overlapTransitionMap
              (complexTorusLocalHolomorphicParameterCechData F) i j z, hzt⟩).1 =
          complexTorusLocalHolomorphicParameterDeckHomeomorph F mn.1 mn.2
            (((overlapSourceAtlas
              (complexTorusLocalHolomorphicParameterCechData F) i j).chart c₁).chart
              ⟨z, hz⟩).1

noncomputable def complexTorusCompactFiberCechDeckComparisonWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusCompactFiberCechDeckComparisonWitness F where
  transition_eq_deck_at := by
    intro i j c₁ c₂ z hz hzt hxs hxt hxo₁ hxo₂
    exact complexTorusLocalCechOverlapAtlas_transition_eq_deck_at
      F i j c₁ c₂ z hz hzt hxs hxt hxo₁ hxo₂

structure ComplexTorusCompactFiberCechOverlapAtlasWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  targetTransport : ∀ i j : ℂ,
    overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j =
      ComplexSurfaceAtlas.transport
        (overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j)
        (multiPatchJointlyTransitionHomeomorphInv
          (complexTorusLocalHolomorphicParameterGlobalFamily F)
          (complexTorusLocalHolomorphicParameterCechCover F)
          (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
          (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
          i j)
  sourceTransition_differentiableOn : ∀ i j : ℂ,
    ∀ c d :
      (overlapSourceAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).index,
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapSourceAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))
  targetTransition_differentiableOn : ∀ i j : ℂ,
    ∀ c d :
      (overlapTargetAtlas
        (complexTorusLocalHolomorphicParameterCechData F) i j).index,
    DifferentiableOn ℂ
      (ComplexSurfaceChart.transitionMap
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))
      (ComplexSurfaceChart.overlap
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart c)
        ((overlapTargetAtlas
          (complexTorusLocalHolomorphicParameterCechData F) i j).chart d))

noncomputable def complexTorusCompactFiberCechOverlapAtlasWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusCompactFiberCechOverlapAtlasWitness F where
  targetTransport := complexTorusLocalCechOverlapAtlas_targetTransport F
  sourceTransition_differentiableOn :=
    complexTorusLocalCechOverlapAtlas_source_transition_differentiableOn F
  targetTransition_differentiableOn :=
    complexTorusLocalCechOverlapAtlas_target_transition_differentiableOn F

/-! The lift-side chart calculation is stronger than a bare differentiability
    statement.  It identifies the overlap of any two local surface charts as
    a union of explicit `(ℤ × ℤ)` sheets, and on each sheet identifies the
    chart transition with the corresponding deck homeomorphism.  This is the
    precise local analytic datum that must eventually be compared with the
    quotient overlap atlas above. -/

structure ComplexTorusCompactFiberLiftChartSheetWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  transitionCover : ∀ c₁ c₂ : ℂ,
    @MathlibFormal.ComplexSurfaceChartTransitionCover
      (Sigma (fun b : ComplexTorusLocalHolomorphicParameterBase F =>
        ComplexTorus (F.parameterPoint b)))
      (complexTorusHolomorphicParameterPullback
        F.toComplexTorusHolomorphicParameterMap).family.totalTopology
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
      (complexTorusLocalHolomorphicParameterSurfaceChart F c₂)
  overlap_eq_iUnion_deckSheets : ∀ c₁ c₂ : ℂ,
    MathlibFormal.ComplexSurfaceChart.overlap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂) =
      ⋃ mn : ℤ × ℤ,
        complexTorusLocalHolomorphicParameterDeckOverlap
          F c₁ c₂ mn.1 mn.2
  transitionMap_eq_deck_on_sheet : ∀ c₁ c₂ : ℂ, ∀ m n : ℤ,
    Set.EqOn
      (MathlibFormal.ComplexSurfaceChart.transitionMap
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₁)
        (complexTorusLocalHolomorphicParameterSurfaceChart F c₂))
      (complexTorusLocalHolomorphicParameterDeckHomeomorph F m n)
      (complexTorusLocalHolomorphicParameterDeckOverlap F c₁ c₂ m n)

noncomputable def complexTorusCompactFiberLiftChartSheetWitness
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusCompactFiberLiftChartSheetWitness F where
  transitionCover := complexTorusLocalHolomorphicParameterChartTransitionCover F
  overlap_eq_iUnion_deckSheets :=
    complexTorusLocalHolomorphicParameterSurfaceChartOverlap_eq_iUnion_deckSheets F
  transitionMap_eq_deck_on_sheet :=
    complexTorusLocalHolomorphicParameterChartTransitionMap_eq_deck_on_sheet F

/-! Since the old local-model route is obstructed, the compact-fibre route is
    bundled at the level that is actually available: a lifted analytic/deck
    witness, the common-mother Čech atlas, the joint holomorphic transition,
    and the descended holomorphic atlas.  This is the replacement bridge for
    compact fibres; it does not smuggle a global plane coordinate into the
    local fibres. -/

structure ComplexTorusCompactFiberCechLiftBridge
    (F : ComplexTorusLocalHolomorphicParameterMap) where
  liftWitness : ComplexTorusLocalJointlyHolomorphicLiftWitness F
  liftSheets : ComplexTorusCompactFiberLiftChartSheetWitness F
  coordinateComparison : ComplexTorusCompactFiberCechLiftCoordinateWitness F
  deckComparison : ComplexTorusCompactFiberCechDeckComparisonWitness F
  overlapAtlas : ComplexTorusCompactFiberCechOverlapAtlasWitness F
  commonMother :
    CommonMotherAtlasTransitionWitness
      (complexTorusLocalHolomorphicParameterCechData F)
  jointlyHolomorphic :
    JointlyHolomorphicTransitionData
      (complexTorusLocalHolomorphicParameterCechData F)
  descendedAtlas :
    DescendedAtlasHolomorphicWitness
      (complexTorusLocalHolomorphicParameterCechData F)
      (isOpenMap_quotientMk_of_openGluing
        (complexTorusLocalHolomorphicParameterCechData F)
        (multiPatchOpenGluingWitness
          (complexTorusLocalHolomorphicParameterGlobalFamily F)
          (complexTorusLocalHolomorphicParameterCechCover F)
          (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
          (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)))

noncomputable def complexTorusCompactFiberCechLiftBridge
    (F : ComplexTorusLocalHolomorphicParameterMap) :
    ComplexTorusCompactFiberCechLiftBridge F where
  liftWitness := complexTorusLocalJointlyHolomorphicLiftWitness F
  liftSheets := complexTorusCompactFiberLiftChartSheetWitness F
  coordinateComparison := complexTorusCompactFiberCechLiftCoordinateWitness F
  deckComparison := complexTorusCompactFiberCechDeckComparisonWitness F
  overlapAtlas := complexTorusCompactFiberCechOverlapAtlasWitness F
  commonMother := multiPatchCommonMotherAtlasWitness
    (complexTorusLocalHolomorphicParameterGlobalFamily F)
    (complexTorusLocalHolomorphicParameterCechCover F)
    (complexTorusLocalHolomorphicParameterCechCover_isOpen F)
    (complexTorusLocalHolomorphicParameterCechCover_iUnion_eq_univ F)
  jointlyHolomorphic := complexTorusLocalHolomorphicParameterCechTransition F
  descendedAtlas := complexTorusLocalHolomorphicParameterCechDescendedAtlas F

end MathlibFormal
end Teichmuller
