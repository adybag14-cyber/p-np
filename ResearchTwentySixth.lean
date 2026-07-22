import ResearchTwentyFifth

namespace PIsNPOrNot
namespace ResearchTwentySixth

/-! ## 361 - Opposite-label witness pairs are the exact collision obligations -/
namespace A361_OppositePairs

variable {Witness : Type}

def Opposite (relation : Witness -> Bool) (pair : Witness × Witness) : Prop :=
  relation pair.1 ≠ relation pair.2

end A361_OppositePairs

/-! ## 362 - One observable separates a pair when its values differ -/
namespace A362_FeatureSeparation

variable {Witness : Type}

def Separates (feature : Witness -> Bool) (pair : Witness × Witness) : Prop :=
  feature pair.1 ≠ feature pair.2

end A362_FeatureSeparation

/-! ## 363 - A finite observable family induces a joint list signature -/
namespace A363_ListSignature

variable {Witness : Type}

def signature (features : List (Witness -> Bool)) (witness : Witness) : List Bool :=
  features.map (fun feature => feature witness)

end A363_ListSignature

/-! ## 364 - Covering every opposite pair makes simultaneous feature collisions safe -/
namespace A364_SeparationImpliesFiberSafety

open A361_OppositePairs A362_FeatureSeparation

variable {Witness : Type}

 theorem same_features_same_label
    (relation : Witness -> Bool)
    (features : List (Witness -> Bool))
    (covers : forall pair,
      Opposite relation pair ->
        exists feature, feature ∈ features /\ Separates feature pair)
    {left right : Witness}
    (sameAll : forall feature, feature ∈ features ->
      feature left = feature right) :
    relation left = relation right := by
  by_contra different
  have opposite : Opposite relation (left, right) := different
  rcases covers (left, right) opposite with ⟨feature, member, separates⟩
  exact separates (sameAll feature member)

end A364_SeparationImpliesFiberSafety

/-! ## 365 - Fiber safety forces every opposite pair to be separated -/
namespace A365_FiberSafetyEquivalence

variable {Witness Feature : Type}

 theorem safe_implies_separates_opposites
    (relation : Witness -> Bool) (feature : Witness -> Feature)
    (safe : forall left right,
      feature left = feature right -> relation left = relation right)
    {left right : Witness}
    (opposite : relation left ≠ relation right) :
    feature left ≠ feature right := by
  intro same
  exact opposite (safe left right same)

end A365_FiberSafetyEquivalence

/-! ## 366 - Opposite-pair universes are finite and explicitly checkable -/
namespace A366_FiniteOppositeUniverse

variable {Witness : Type} [Fintype Witness] [DecidableEq Witness]

def oppositePairs (relation : Witness -> Bool) : Finset (Witness × Witness) :=
  (Finset.univ : Finset (Witness × Witness)).filter
    (fun pair => relation pair.1 ≠ relation pair.2)

theorem mem_oppositePairs
    (relation : Witness -> Bool) (pair : Witness × Witness) :
    pair ∈ oppositePairs relation <->
      A361_OppositePairs.Opposite relation pair := by
  simp [oppositePairs, A361_OppositePairs.Opposite]

end A366_FiniteOppositeUniverse

/-! ## 367 - A feature covers exactly the opposite pairs that it separates -/
namespace A367_FeatureCover

open A366_FiniteOppositeUniverse

variable {Witness : Type} [Fintype Witness] [DecidableEq Witness]

def coveredPairs
    (relation : Witness -> Bool) (feature : Witness -> Bool) :
    Finset (Witness × Witness) :=
  (oppositePairs relation).filter (fun pair => feature pair.1 ≠ feature pair.2)

theorem covered_subset_opposites
    (relation : Witness -> Bool) (feature : Witness -> Bool) :
    coveredPairs relation feature ⊆ oppositePairs relation := by
  intro pair member
  exact (Finset.mem_filter.1 member).1

end A367_FeatureCover

/-! ## 368 - A complete pair cover certifies exact quotient safety -/
namespace A368_CompleteCoverSafety

variable {Witness : Type}

 theorem complete_cover_safe
    (relation : Witness -> Bool)
    (features : List (Witness -> Bool))
    (complete : forall left right,
      relation left ≠ relation right ->
        exists feature, feature ∈ features /\ feature left ≠ feature right)
    {left right : Witness}
    (sameAll : forall feature, feature ∈ features ->
      feature left = feature right) :
    relation left = relation right := by
  by_contra opposite
  rcases complete left right opposite with ⟨feature, member, separates⟩
  exact separates (sameAll feature member)

end A368_CompleteCoverSafety

/-! ## 369 - Adding observables preserves complete pair coverage -/
namespace A369_CoverMonotonicity

variable {Witness : Type}

 theorem append_preserves_cover
    (relation : Witness -> Bool)
    (oldFeatures newFeatures : List (Witness -> Bool))
    (oldComplete : forall left right,
      relation left ≠ relation right ->
        exists feature, feature ∈ oldFeatures /\ feature left ≠ feature right) :
    forall left right,
      relation left ≠ relation right ->
        exists feature,
          feature ∈ oldFeatures ++ newFeatures /\
          feature left ≠ feature right := by
  intro left right opposite
  rcases oldComplete left right opposite with ⟨feature, member, separates⟩
  exact ⟨feature, List.mem_append_left newFeatures member, separates⟩

end A369_CoverMonotonicity

/-! ## 370 - Unioning per-feature pair covers is bounded by their total sizes -/
namespace A370_CoverUnionBound

variable {Pair : Type} [DecidableEq Pair]

 theorem union_card_le_sum (covers : List (Finset Pair)) :
    (ResearchThirteenth.A174_PortfolioUnion.unionAll covers).card <=
      (covers.map Finset.card).sum :=
  ResearchThirteenth.A175_PortfolioUnionBound.card_unionAll_le_sum covers

end A370_CoverUnionBound

/-! ## 371 - The opposite-pair universe has at most the square of witness count -/
namespace A371_PairUniverseBound

open A366_FiniteOppositeUniverse

variable {Witness : Type} [Fintype Witness] [DecidableEq Witness]

 theorem opposite_pair_card_le_square (relation : Witness -> Bool) :
    (oppositePairs relation).card <= Fintype.card Witness ^ 2 := by
  calc
    (oppositePairs relation).card <= Fintype.card (Witness × Witness) :=
      Finset.card_le_univ _
    _ = Fintype.card Witness ^ 2 := by simp [pow_two]

end A371_PairUniverseBound

/-! ## 372 - Explicit collision checking has pair-count times feature-count work -/
namespace A372_CollisionCheckCost

 theorem collision_check_bound
    (pairCount featureCount input pairExp featureExp : Nat)
    (pairBound : pairCount <= input ^ pairExp)
    (featureBound : featureCount <= input ^ featureExp) :
    pairCount * featureCount <= input ^ (pairExp + featureExp) := by
  calc
    pairCount * featureCount <=
        input ^ pairExp * input ^ featureExp :=
      Nat.mul_le_mul pairBound featureBound
    _ = input ^ (pairExp + featureExp) := by rw [pow_add]

end A372_CollisionCheckCost

/-! ## 373 - Exhaustive pair checking over n-bit witnesses is exponential -/
namespace A373_BitPairBarrier

 theorem bit_pair_space_card (n : Nat) :
    Fintype.card ((Fin n -> Bool) × (Fin n -> Bool)) = 2 ^ (2 * n) := by
  calc
    Fintype.card ((Fin n -> Bool) × (Fin n -> Bool)) =
        (2 ^ n) * (2 ^ n) := by simp
    _ = 2 ^ (n + n) := by rw [← pow_add]
    _ = 2 ^ (2 * n) := by congr 1 <;> omega

end A373_BitPairBarrier

/-! ## 374 - Structural proof certificates can replace exhaustive pair enumeration -/
namespace A374_StructuralSeparationCertificate

variable {Instance : Type}

structure Certificate (specification : Instance -> Prop) where
  verify : Instance -> Bool
  sound : forall input, verify input = true -> specification input

theorem verified_certificate_sound
    (specification : Instance -> Prop)
    (certificate : Certificate specification)
    (input : Instance) (accepted : certificate.verify input = true) :
    specification input :=
  certificate.sound input accepted

end A374_StructuralSeparationCertificate

/-! ## 375 - Uniform polynomial separating-feature covers yield P = NP -/
namespace A375_FeatureCoverCollapse

variable {Language : Type}

structure UniformFeatureCover
    (PClass NPClass : Set Language) where
  hasPolynomialCover : Language -> Prop
  allNPHaveCover : forall language,
    language ∈ NPClass -> hasPolynomialCover language
  coverGivesP : forall language,
    hasPolynomialCover language -> language ∈ PClass

theorem p_eq_np_of_uniform_separating_features
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (cover : UniformFeatureCover PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language languageNP
  exact cover.coverGivesP language
    (cover.allNPHaveCover language languageNP)

end A375_FeatureCoverCollapse

end ResearchTwentySixth
end PIsNPOrNot
