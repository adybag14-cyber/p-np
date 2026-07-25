import ResearchFiftySeventh

namespace PIsNPOrNot.ResearchFiftyEighth

/-! ## 841 - A targeted test isolates a set when exactly one element survives -/
namespace A841_TargetedIsolation

variable {U : Type} [DecidableEq U]

def Isolates (test subset : Finset U) : Prop :=
  (subset ∩ test).card = 1

end A841_TargetedIsolation

/-! ## 842 - A family is universal when it isolates every nonempty subset -/
namespace A842_UniversalIsolation

open A841_TargetedIsolation

variable {U : Type} [DecidableEq U]

def UniversalOn (domainSet : Finset U) (family : Finset (Finset U)) : Prop :=
  ∀ subset, subset ⊆ domainSet -> subset.Nonempty ->
    ∃ test ∈ family, Isolates test subset

end A842_UniversalIsolation

/-! ## 843 - Isolation of the whole domainSet exposes one distinguished element -/
namespace A843_WholeSetSingleton

open A841_TargetedIsolation A842_UniversalIsolation

variable {U : Type} [DecidableEq U]

theorem exists_singleton_intersection
    {domainSet : Finset U} {family : Finset (Finset U)}
    (universal : UniversalOn domainSet family)
    (nonempty : domainSet.Nonempty) :
    ∃ test ∈ family, ∃ point, domainSet ∩ test = {point} := by
  obtain ⟨test, member, isolated⟩ :=
    universal domainSet (Finset.Subset.rfl) nonempty
  obtain ⟨point, singleton⟩ := Finset.card_eq_one.mp isolated
  exact ⟨test, member, point, singleton⟩

end A843_WholeSetSingleton

/-! ## 844 - Removing an isolated point and its test preserves universality -/
namespace A844_DeleteIsolated

open A841_TargetedIsolation A842_UniversalIsolation

variable {U : Type} [DecidableEq U]

theorem universal_after_delete
    {domainSet : Finset U} {family : Finset (Finset U)}
    (universal : UniversalOn domainSet family)
    {test : Finset U} (testMember : test ∈ family)
    {point : U} (singleton : domainSet ∩ test = {point}) :
    UniversalOn (domainSet.erase point) (family.erase test) := by
  intro subset subsetOf nonempty
  have subsetUniverse : subset ⊆ domainSet :=
    subsetOf.trans (Finset.erase_subset point domainSet)
  obtain ⟨nextTest, nextMember, nextIsolates⟩ :=
    universal subset subsetUniverse nonempty
  refine ⟨nextTest, ?_, nextIsolates⟩
  apply Finset.mem_erase.mpr
  refine ⟨?_, nextMember⟩
  intro same
  subst nextTest
  have pointNotSubset : point ∉ subset := by
    intro pointMember
    have impossible : point ∈ domainSet.erase point := subsetOf pointMember
    exact (domainSet.notMem_erase point) impossible
  have emptyIntersection : subset ∩ test = ∅ := by
    ext value
    constructor
    · intro valueMember
      have valueSubset : value ∈ subset := (Finset.mem_inter.mp valueMember).1
      have valueTest : value ∈ test := (Finset.mem_inter.mp valueMember).2
      have valueWhole : value ∈ domainSet ∩ test :=
        Finset.mem_inter.mpr ⟨subsetUniverse valueSubset, valueTest⟩
      have valueEq : value = point := by
        simpa [singleton] using valueWhole
      exact False.elim (pointNotSubset (valueEq ▸ valueSubset))
    · intro valueEmpty
      simp at valueEmpty
  unfold A841_TargetedIsolation.Isolates at nextIsolates
  rw [emptyIntersection] at nextIsolates
  simp at nextIsolates

end A844_DeleteIsolated

/-! ## 845 - Every universal targeted isolation family has at least |U| tests -/
namespace A845_UniversalFamilyLowerBound

open A842_UniversalIsolation

variable {U : Type} [DecidableEq U]

theorem family_card_ge_domainSet_card
    (domainSet : Finset U) (family : Finset (Finset U))
    (universal : UniversalOn domainSet family) :
    domainSet.card ≤ family.card := by
  classical
  induction hsize : domainSet.card using Nat.strong_induction_on generalizing domainSet family with
  | h size ih =>
      by_cases nonempty : domainSet.Nonempty
      · obtain ⟨test, testMember, point, singleton⟩ :=
          A843_WholeSetSingleton.exists_singleton_intersection universal nonempty
        have pointMember : point ∈ domainSet := by
          have : point ∈ domainSet ∩ test := by simp [singleton]
          exact (Finset.mem_inter.mp this).1
        have smaller : (domainSet.erase point).card < domainSet.card :=
          Finset.card_erase_lt_of_mem pointMember
        have reducedUniversal :
            UniversalOn (domainSet.erase point) (family.erase test) :=
          A844_DeleteIsolated.universal_after_delete
            universal testMember singleton
        have smallerSize : (domainSet.erase point).card < size := by
          simpa [hsize] using smaller
        have reducedBound :
            (domainSet.erase point).card ≤ (family.erase test).card :=
          ih (domainSet.erase point).card smallerSize
            (domainSet.erase point) (family.erase test) reducedUniversal rfl
        calc
          size = domainSet.card := hsize.symm
          _ = (domainSet.erase point).card + 1 :=
            (Finset.card_erase_add_one pointMember).symm
          _ ≤ (family.erase test).card + 1 := Nat.add_le_add_right reducedBound 1
          _ = family.card := Finset.card_erase_add_one testMember
      · have empty : domainSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
        have sizeZero : size = 0 := by simpa [empty] using hsize.symm
        simp [sizeZero]

end A845_UniversalFamilyLowerBound

/-! ## 846 - The Boolean n-cube contains exactly 2^n possible witnesses -/
namespace A846_BooleanUniverseCardinality

variable (n : Nat)

theorem bit_domainSet_card :
    (Finset.univ : Finset (Fin n -> Bool)).card = 2 ^ n := by
  simp [Fintype.card_fun]

end A846_BooleanUniverseCardinality

/-! ## 847 - Indexed tests induce a finite family of targeted subsets -/
namespace A847_IndexedTestFamily

variable {Index U : Type} [Fintype Index] [DecidableEq U]

noncomputable def family (test : Index -> Finset U) : Finset (Finset U) := by
  classical
  exact (Finset.univ : Finset Index).image test

theorem family_card_le (test : Index -> Finset U) :
    (family test).card ≤ Fintype.card Index := by
  classical
  calc
    (family test).card ≤ (Finset.univ : Finset Index).card := Finset.card_image_le
    _ = Fintype.card Index := Finset.card_univ

end A847_IndexedTestFamily

/-! ## 848 - Any indexed universal isolation system needs at least |U| indices -/
namespace A848_IndexedIsolationLowerBound

open A841_TargetedIsolation A842_UniversalIsolation A847_IndexedTestFamily

variable {Index U : Type} [Fintype Index] [Fintype U]
variable [DecidableEq U]

def IndexedUniversal (test : Index -> Finset U) : Prop :=
  ∀ subset : Finset U, subset.Nonempty ->
    ∃ index, Isolates (test index) subset

 theorem index_card_ge_domainSet_card
    (test : Index -> Finset U) (universal : IndexedUniversal test) :
    Fintype.card U ≤ Fintype.card Index := by
  classical
  have familyUniversal : UniversalOn (Finset.univ : Finset U) (family test) := by
    intro subset _subsetOf nonempty
    obtain ⟨index, isolated⟩ := universal subset nonempty
    exact ⟨test index, Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩, isolated⟩
  calc
    Fintype.card U = (Finset.univ : Finset U).card := Finset.card_univ.symm
    _ ≤ (family test).card :=
      A845_UniversalFamilyLowerBound.family_card_ge_domainSet_card
        (Finset.univ : Finset U) (family test) familyUniversal
    _ ≤ Fintype.card Index := family_card_le test

end A848_IndexedIsolationLowerBound

/-! ## 849 - A hash-target pair denotes one targeted fiber -/
namespace A849_HashFiber

variable {U Hash Bucket : Type}
variable [Fintype U] [DecidableEq U] [DecidableEq Bucket]

noncomputable def fiber (hash : Hash -> U -> Bucket)
    (candidate : Hash × Bucket) : Finset U := by
  classical
  exact (Finset.univ : Finset U).filter
    (fun value => hash candidate.1 value = candidate.2)

end A849_HashFiber

/-! ## 850 - Universal hash isolation obeys a hashes-times-buckets lower bound -/
namespace A850_HashBucketProductLowerBound

open A848_IndexedIsolationLowerBound A849_HashFiber

variable {U Hash Bucket : Type}
variable [Fintype U] [Fintype Hash] [Fintype Bucket]
variable [DecidableEq U] [DecidableEq Bucket]

 theorem hash_mul_bucket_ge_domainSet
    (hash : Hash -> U -> Bucket)
    (universal : IndexedUniversal (fiber hash)) :
    Fintype.card U ≤ Fintype.card Hash * Fintype.card Bucket := by
  simpa [Fintype.card_prod] using
    (index_card_ge_domainSet_card (test := fiber hash) universal)

end A850_HashBucketProductLowerBound

/-! ## 851 - Fixed-target deterministic isolation on n bits needs 2^n hashes -/
namespace A851_FixedTargetExponential

open A848_IndexedIsolationLowerBound

variable {n : Nat} {Hash : Type} [Fintype Hash]

 theorem fixed_target_hashes_ge_pow_two
    (test : Hash -> Finset (Fin n -> Bool))
    (universal : IndexedUniversal test) :
    2 ^ n ≤ Fintype.card Hash := by
  simpa [Fintype.card_fun] using
    (index_card_ge_domainSet_card (test := test) universal)

end A851_FixedTargetExponential

/-! ## 852 - Inspecting every bucket pays the full targeted-test product -/
namespace A852_EnumerationWork

structure Work where
  hashes : Nat
  bucketsPerHash : Nat
  checkCost : Nat

def total (work : Work) : Nat :=
  work.hashes * work.bucketsPerHash * work.checkCost

theorem total_ge_targeted
    (work : Work) (positive : 1 ≤ work.checkCost) :
    work.hashes * work.bucketsPerHash ≤ total work := by
  exact Nat.le_mul_of_pos_right (work.hashes * work.bucketsPerHash) positive

end A852_EnumerationWork

/-! ## 853 - A uniquely occupied targeted test contains a concrete witness -/
namespace A853_IsolatedWitnessRecovery

variable {U : Type} [DecidableEq U]

 theorem recover
    (accepted test : Finset U)
    (unique : (accepted ∩ test).card = 1) :
    ∃ witness, witness ∈ accepted ∧ witness ∈ test := by
  obtain ⟨witness, singleton⟩ := Finset.card_eq_one.mp unique
  have member : witness ∈ accepted ∩ test := by simp [singleton]
  exact ⟨witness, (Finset.mem_inter.mp member).1, (Finset.mem_inter.mp member).2⟩

end A853_IsolatedWitnessRecovery

/-! ## 854 - A universal fixed-target black-box isolation proof cannot be polynomial-size -/
namespace A854_BlackBoxIsolationObstruction

variable (n : Nat)

structure Attempt where
  Hash : Type
  finiteHash : Fintype Hash
  test : Hash -> Finset (Fin n -> Bool)
  universal :
    A848_IndexedIsolationLowerBound.IndexedUniversal test

attribute [instance] Attempt.finiteHash

theorem required_hashes (attempt : Attempt n) :
    2 ^ n ≤ Fintype.card attempt.Hash :=
  A851_FixedTargetExponential.fixed_target_hashes_ge_pow_two
    attempt.test attempt.universal

end A854_BlackBoxIsolationObstruction

/-! ## 855 - The genuine isolation route still requires formula-dependent discovery -/
namespace A855_FormulaDependentIsolationCriterion

structure Compiler where
  inputSize : Nat
  familySize : Nat
  bucketCount : Nat
  constructionCost : Nat
  selectionCost : Nat
  residualSolveCost : Nat

 def totalCost (compiler : Compiler) : Nat :=
  compiler.constructionCost + compiler.selectionCost +
    compiler.familySize * compiler.bucketCount * compiler.residualSolveCost

theorem black_box_product_obstruction
    (compiler : Compiler)
    (domainSetLowerBound : 2 ^ compiler.inputSize ≤
      compiler.familySize * compiler.bucketCount) :
    2 ^ compiler.inputSize * compiler.residualSolveCost ≤
      compiler.familySize * compiler.bucketCount * compiler.residualSolveCost := by
  exact Nat.mul_le_mul_right compiler.residualSolveCost domainSetLowerBound

end A855_FormulaDependentIsolationCriterion

end PIsNPOrNot.ResearchFiftyEighth
