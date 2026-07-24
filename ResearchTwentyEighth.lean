import Mathlib
import ResearchTwentyFifth
import ResearchTwentySeventh

namespace PIsNPOrNot.ResearchTwentyEighth

/-! ## 391 - Reachable feature images are explicit finite objects -/
namespace A391_ReachableFeatureImage

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

def reachableImage (feature : Witness -> Feature) : Finset Feature :=
  (Finset.univ : Finset Witness).image feature

theorem mem_reachableImage_iff
    (feature : Witness -> Feature) (value : Feature) :
    value ∈ reachableImage feature <-> exists witness, feature witness = value := by
  classical
  simp [reachableImage]

end A391_ReachableFeatureImage

/-! ## 392 - A reachable-image enumerator must be complete and sound -/
namespace A392_ReachableEnumerator

open A391_ReachableFeatureImage

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

structure Enumerator (feature : Witness -> Feature) where
  values : List Feature
  complete : forall witness, feature witness ∈ values
  sound : forall value, value ∈ values -> exists witness, feature witness = value

theorem values_toFinset_eq_image
    (feature : Witness -> Feature) (enumerator : Enumerator feature) :
    enumerator.values.toFinset = reachableImage feature := by
  classical
  ext value
  constructor
  · intro member
    rcases enumerator.sound value (by simpa using member) with ⟨witness, rfl⟩
    exact Finset.mem_image.2 ⟨witness, Finset.mem_univ witness, rfl⟩
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, rfl⟩
    simpa using enumerator.complete witness

end A392_ReachableEnumerator

/-! ## 393 - Exact decision follows from factorization plus reachable enumeration -/
namespace A393_EnumeratedQuotientDecision

open ResearchTwentyFifth.A347_NonlinearFactorization
open A392_ReachableEnumerator

variable {Witness Feature : Type}

 theorem exists_accepting_iff_enumerated
    (relation : Witness -> Bool) (feature : Witness -> Feature)
    (acceptFeature : Feature -> Bool)
    (factors : forall witness, relation witness = acceptFeature (feature witness))
    (enumerator : Enumerator feature) :
    (exists witness, relation witness = true) <->
      exists value, value ∈ enumerator.values /\ acceptFeature value = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨feature witness, enumerator.complete witness, ?_⟩
    simpa [factors witness] using accepted
  · rintro ⟨value, member, accepted⟩
    rcases enumerator.sound value member with ⟨witness, rfl⟩
    refine ⟨witness, ?_⟩
    simpa [factors witness] using accepted

end A393_EnumeratedQuotientDecision

/-! ## 394 - Representative tables certify reachability constructively -/
namespace A394_RepresentativeTable

variable {Witness Feature : Type}

structure Table (feature : Witness -> Feature) where
  values : List Feature
  representative : Feature -> Witness
  complete : forall witness, feature witness ∈ values
  exactRepresentative : forall value, value ∈ values ->
    feature (representative value) = value

theorem listed_value_reachable
    (feature : Witness -> Feature) (table : Table feature)
    {value : Feature} (member : value ∈ table.values) :
    exists witness, feature witness = value := by
  exact ⟨table.representative value, table.exactRepresentative value member⟩

end A394_RepresentativeTable

/-! ## 395 - Any complete list is at least as large as the reachable image -/
namespace A395_EnumeratorLowerBound

open A391_ReachableFeatureImage A392_ReachableEnumerator

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

 theorem image_card_le_list_length
    (feature : Witness -> Feature) (enumerator : Enumerator feature) :
    (reachableImage feature).card <= enumerator.values.length := by
  rw [← A392_ReachableEnumerator.values_toFinset_eq_image feature enumerator]
  exact List.toFinset_card_le enumerator.values

end A395_EnumeratorLowerBound

/-! ## 396 - The verifier output itself is a one-bit feature -/
namespace A396_OutputFeature

variable {Witness : Type}

def outputFeature (relation : Witness -> Bool) : Witness -> Bool := relation

theorem output_factors
    (relation : Witness -> Bool) (witness : Witness) :
    relation witness = outputFeature relation witness := rfl

end A396_OutputFeature

/-! ## 397 - The output feature always has at most two reachable values -/
namespace A397_OutputImageBound

open A391_ReachableFeatureImage A396_OutputFeature

variable {Witness : Type} [Fintype Witness]

 theorem output_image_le_two (relation : Witness -> Bool) :
    (reachableImage (outputFeature relation)).card <= 2 := by
  classical
  calc
    (reachableImage (outputFeature relation)).card <= Fintype.card Bool :=
      Finset.card_le_univ _
    _ = 2 := Fintype.card_bool

end A397_OutputImageBound

/-! ## 398 - Reaching true in the output image is exactly the original search problem -/
namespace A398_OutputReachabilityCircularity

open A391_ReachableFeatureImage A396_OutputFeature

variable {Witness : Type} [Fintype Witness]

 theorem true_mem_output_image_iff
    (relation : Witness -> Bool) :
    true ∈ reachableImage (outputFeature relation) <->
      exists witness, relation witness = true := by
  classical
  simp [reachableImage, outputFeature]

end A398_OutputReachabilityCircularity

/-! ## 399 - Any exact output-image oracle is already an existential decider -/
namespace A399_OutputOracleEquivalence

open A391_ReachableFeatureImage A396_OutputFeature

variable {Witness : Type} [Fintype Witness]

structure ReachabilityOracle (relation : Witness -> Bool) where
  decideTrueReachable : Bool
  exact : decideTrueReachable = true <->
    true ∈ reachableImage (outputFeature relation)

theorem oracle_decides_existence
    (relation : Witness -> Bool) (oracle : ReachabilityOracle relation) :
    oracle.decideTrueReachable = true <->
      exists witness, relation witness = true := by
  rw [oracle.exact]
  exact A398_OutputReachabilityCircularity.true_mem_output_image_iff relation

end A399_OutputOracleEquivalence

/-! ## 400 - The ambient Boolean signature cube has size two to the k -/
namespace A400_AmbientSignatureCube

 theorem signature_cube_card (k : Nat) :
    Fintype.card (Fin k -> Bool) = 2 ^ k := by
  simp [Fintype.card_fun]

end A400_AmbientSignatureCube

/-! ## 401 - Enumerating every ambient signature costs two to the k candidates -/
namespace A401_AmbientEnumerationCost

 theorem full_signature_list_length (k : Nat) :
    (Finset.univ : Finset (Fin k -> Bool)).card = 2 ^ k := by
  simp [Fintype.card_fun]

end A401_AmbientEnumerationCost

/-! ## 402 - Quotient decision cost must include reachable-image generation -/
namespace A402_QuotientCostAccounting

 theorem total_cost_bound
    (construction enumeration evaluation imageSize : Nat)
    (enumerationPerValue : Nat) :
    construction + enumeration + imageSize * evaluation <=
      construction + enumeration + imageSize * evaluation + enumerationPerValue := by
  omega

end A402_QuotientCostAccounting

/-! ## 403 - Polynomial image size and polynomial per-value work compose -/
namespace A403_EnumerationWorkBudget

 theorem image_times_evaluation
    (imageSize evaluation input imageExp evalExp : Nat)
    (imageBound : imageSize <= input ^ imageExp)
    (evalBound : evaluation <= input ^ evalExp) :
    imageSize * evaluation <= input ^ imageExp * input ^ evalExp := by
  exact Nat.mul_le_mul imageBound evalBound

end A403_EnumerationWorkBudget

/-! ## 404 - A corrected nonlinear compiler carries enumeration cost explicitly -/
namespace A404_ReachabilityAwareCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  constructionCost : Input -> Nat
  enumerationCost : Input -> Nat
  evaluationCost : Input -> Nat
  reachableValues : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  constructionBound : forall input,
    constructionCost input <= inputSize input ^ exponent
  enumerationBound : forall input,
    enumerationCost input <= inputSize input ^ exponent
  evaluationBound : forall input,
    evaluationCost input <= inputSize input ^ exponent
  reachableBound : forall input,
    reachableValues input <= inputSize input ^ exponent

theorem compiler_exact
    (specification : Input -> Prop) (compiler : Compiler specification)
    (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A404_ReachabilityAwareCompiler

/-! ## 405 - A uniform reachability-aware compiler cover yields the class collapse -/
namespace A405_ReachabilityAwareCollapse

variable {Language : Type}

structure UniformCover (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language,
    hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_reachable_quotients
    (PClass NPClass : Set Language)
    (cover : UniformCover PClass NPClass)
    (pSubsetNP : PClass ⊆ NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language member
  exact cover.compilerGivesP language
    (cover.allNPHaveCompiler language member)

end A405_ReachabilityAwareCollapse

end PIsNPOrNot.ResearchTwentyEighth
