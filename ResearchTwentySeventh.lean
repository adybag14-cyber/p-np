import ResearchTwentySixth

namespace PIsNPOrNot
namespace ResearchTwentySeventh

/-! ## 376 - Bijective preprocessing preserves opposite-label pairs -/
namespace A376_OppositePairTransport

open ResearchEighteenth.A241_BijectiveTransform

variable {Witness : Type}

 theorem opposite_iff_after_encode
    (relation : Witness -> Bool)
    (transform : Transform (Witness := Witness))
    (left right : Witness) :
    relation left ≠ relation right <->
      relation (transform.decode (transform.encode left)) ≠
        relation (transform.decode (transform.encode right)) := by
  rw [transform.decodeEncode left, transform.decodeEncode right]

end A376_OppositePairTransport

/-! ## 377 - Observables on transformed coordinates pull back to original witnesses -/
namespace A377_PullbackObservable

open ResearchEighteenth.A241_BijectiveTransform

variable {Witness Feature : Type}

def pullback (transform : Transform (Witness := Witness))
    (observable : Witness -> Feature) : Witness -> Feature :=
  fun witness => observable (transform.encode witness)

end A377_PullbackObservable

/-! ## 378 - Fiber safety in transformed coordinates implies pullback safety -/
namespace A378_PullbackSafety

open ResearchEighteenth.A241_BijectiveTransform
open A377_PullbackObservable

variable {Witness Feature : Type}

 theorem pullback_fiber_safe
    (relation : Witness -> Bool)
    (transform : Transform (Witness := Witness))
    (feature : Witness -> Feature)
    (safe : forall left right,
      feature left = feature right ->
        relation (transform.decode left) = relation (transform.decode right))
    {left right : Witness}
    (same : feature (transform.encode left) = feature (transform.encode right)) :
    relation left = relation right := by
  have transformed := safe (transform.encode left) (transform.encode right) same
  simpa [transform.decodeEncode] using transformed

end A378_PullbackSafety

/-! ## 379 - Bijective preprocessing preserves the reachable feature image exactly -/
namespace A379_FeatureImageTransport

open ResearchEighteenth.A241_BijectiveTransform
open A377_PullbackObservable

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

 theorem pullback_image_eq
    (transform : Transform (Witness := Witness))
    (feature : Witness -> Feature) :
    (Finset.univ : Finset Witness).image (pullback transform feature) =
      (Finset.univ : Finset Witness).image feature := by
  classical
  ext value
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, rfl⟩
    exact Finset.mem_image.2
      ⟨transform.encode witness, Finset.mem_univ _, rfl⟩
  · intro member
    rcases Finset.mem_image.1 member with ⟨encoded, _, rfl⟩
    refine Finset.mem_image.2
      ⟨transform.decode encoded, Finset.mem_univ _, ?_⟩
    simp [pullback, transform.encodeDecode]

end A379_FeatureImageTransport

/-! ## 380 - Pullback feature images have identical cardinality -/
namespace A380_FeatureImageCardinality

open ResearchEighteenth.A241_BijectiveTransform
open A377_PullbackObservable A379_FeatureImageTransport

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

 theorem pullback_image_card_eq
    (transform : Transform (Witness := Witness))
    (feature : Witness -> Feature) :
    ((Finset.univ : Finset Witness).image (pullback transform feature)).card =
      ((Finset.univ : Finset Witness).image feature).card := by
  rw [pullback_image_eq transform feature]

end A380_FeatureImageCardinality

/-! ## 381 - Keeping original and transformed quotients can never worsen image size -/
namespace A381_PortfolioMinimum

 theorem portfolio_min_le_original (original transformed : Nat) :
    min original transformed <= original :=
  Nat.min_le_left _ _

theorem portfolio_min_le_transformed (original transformed : Nat) :
    min original transformed <= transformed :=
  Nat.min_le_right _ _

end A381_PortfolioMinimum

/-! ## 382 - A baseline-safe quotient portfolio preserves exactness -/
namespace A382_ExactQuotientPortfolio

variable {Input : Type}

structure Candidate (specification : Input -> Prop) where
  decide : Input -> Bool
  imageSize : Nat
  exact : forall input, decide input = true <-> specification input

structure Portfolio (specification : Input -> Prop) where
  original : Candidate specification
  transformed : Candidate specification
  chosen : Candidate specification
  chosenBound : chosen.imageSize <= min original.imageSize transformed.imageSize

theorem chosen_exact
    (specification : Input -> Prop)
    (portfolio : Portfolio specification) (input : Input) :
    portfolio.chosen.decide input = true <-> specification input :=
  portfolio.chosen.exact input

end A382_ExactQuotientPortfolio

/-! ## 383 - Network and observable evaluation costs compose additively -/
namespace A383_TransformFeatureCost

 theorem combined_cost_bound
    (networkCost featureCost input networkExp featureExp : Nat)
    (networkBound : networkCost <= input ^ networkExp)
    (featureBound : featureCost <= input ^ featureExp) :
    networkCost + featureCost <=
      input ^ networkExp + input ^ featureExp :=
  Nat.add_le_add networkBound featureBound

end A383_TransformFeatureCost

/-! ## 384 - Polynomially many transform-feature candidates remain polynomial -/
namespace A384_TransformFeaturePortfolioCost

 theorem portfolio_cost_bound
    (candidateCount perCandidate input countExp candidateExp : Nat)
    (countBound : candidateCount <= input ^ countExp)
    (candidateBound : perCandidate <= input ^ candidateExp) :
    candidateCount * perCandidate <= input ^ (countExp + candidateExp) := by
  calc
    candidateCount * perCandidate <=
        input ^ countExp * input ^ candidateExp :=
      Nat.mul_le_mul countBound candidateBound
    _ = input ^ (countExp + candidateExp) := by rw [pow_add]

end A384_TransformFeaturePortfolioCost

/-! ## 385 - Exact transform replay plus exact fiber checking composes -/
namespace A385_ComposedCertificate

variable {Input : Type}

structure Certificate (specification : Input -> Prop) where
  transformValid : Input -> Prop
  featureValid : Input -> Prop
  decide : Input -> Bool
  exactWhenValid : forall input,
    transformValid input -> featureValid input ->
      (decide input = true <-> specification input)

theorem replayed_exact
    (specification : Input -> Prop)
    (certificate : Certificate specification)
    (input : Input)
    (transformProof : certificate.transformValid input)
    (featureProof : certificate.featureValid input) :
    certificate.decide input = true <-> specification input :=
  certificate.exactWhenValid input transformProof featureProof

end A385_ComposedCertificate

/-! ## 386 - Separating features transport through a bijection -/
namespace A386_SeparationPullback

open ResearchEighteenth.A241_BijectiveTransform
open A377_PullbackObservable

variable {Witness : Type}

 theorem transformed_cover_gives_original_cover
    (relation : Witness -> Bool)
    (transform : Transform (Witness := Witness))
    (features : List (Witness -> Bool))
    (cover : forall left right,
      relation (transform.decode left) ≠ relation (transform.decode right) ->
        exists feature,
          feature ∈ features /\ feature left ≠ feature right) :
    forall left right,
      relation left ≠ relation right ->
        exists feature,
          feature ∈ features /\
          pullback transform feature left ≠ pullback transform feature right := by
  intro left right opposite
  have transformedOpposite :
      relation (transform.decode (transform.encode left)) ≠
        relation (transform.decode (transform.encode right)) := by
    simpa [transform.decodeEncode] using opposite
  rcases cover (transform.encode left) (transform.encode right) transformedOpposite with
    ⟨feature, member, separates⟩
  exact ⟨feature, member, separates⟩

end A386_SeparationPullback

/-! ## 387 - Original-or-transformed selection is exact under either certificate -/
namespace A387_SafeSelector

variable {Input : Type}

 theorem choose_exact
    (specification : Input -> Prop)
    (original transformed : Input -> Bool)
    (originalExact : forall input,
      original input = true <-> specification input)
    (transformedExact : forall input,
      transformed input = true <-> specification input)
    (chooseTransformed : Bool) (input : Input) :
    (if chooseTransformed then transformed input else original input) = true <->
      specification input := by
  cases chooseTransformed <;> simp [originalExact input, transformedExact input]

end A387_SafeSelector

/-! ## 388 - Selecting by certified image size preserves the baseline bound -/
namespace A388_ImageBoundSelector

 theorem selected_image_le_baseline
    (original transformed selected : Nat)
    (selectedBound : selected <= min original transformed) :
    selected <= original :=
  le_trans selectedBound (Nat.min_le_left _ _)

end A388_ImageBoundSelector

/-! ## 389 - A combined transform-observable compiler exposes all costs -/
namespace A389_CombinedCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  transformCost : Input -> Nat
  featureCost : Input -> Nat
  imageSize : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  transformBound : forall input,
    transformCost input <= inputSize input ^ exponent
  featureBound : forall input,
    featureCost input <= inputSize input ^ exponent
  imageBound : forall input,
    imageSize input <= inputSize input ^ exponent

theorem compiler_exact
    (specification : Input -> Prop)
    (compiler : Compiler specification) (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A389_CombinedCompiler

/-! ## 390 - Uniform combined compilers yield P = NP -/
namespace A390_CombinedCollapse

variable {Language : Type}

structure UniformCombinedCover
    (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPCompiled : forall language,
    language ∈ NPClass -> hasCompiler language
  compiledInP : forall language,
    hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_transform_feature_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (cover : UniformCombinedCover PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language languageNP
  exact cover.compiledInP language
    (cover.allNPCompiled language languageNP)

end A390_CombinedCollapse

end ResearchTwentySeventh
end PIsNPOrNot
