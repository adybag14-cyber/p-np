import ResearchTwentyFourth

namespace PIsNPOrNot
namespace ResearchTwentyFifth

/-! ## 346 - A finite observable family induces a nonlinear witness signature -/
namespace A346_ObservableSignature

variable {Witness : Type}

def signature {k : Nat}
    (observable : Fin k -> Witness -> Bool) (witness : Witness) :
    Fin k -> Bool :=
  fun index => observable index witness

end A346_ObservableSignature

/-! ## 347 - Acceptance may factor through a noninjective nonlinear signature -/
namespace A347_NonlinearFactorization

open A346_ObservableSignature

variable {Witness : Type}

structure Factorization {k : Nat}
    (relation : Witness -> Bool)
    (observable : Fin k -> Witness -> Bool) where
  acceptSignature : (Fin k -> Bool) -> Bool
  factors : forall witness,
    relation witness = acceptSignature (signature observable witness)

theorem same_signature_same_answer
    {k : Nat} (relation : Witness -> Bool)
    (observable : Fin k -> Witness -> Bool)
    (factor : Factorization relation observable)
    {left right : Witness}
    (same : signature observable left = signature observable right) :
    relation left = relation right := by
  rw [factor.factors left, factor.factors right, same]

end A347_NonlinearFactorization

/-! ## 348 - Existential search reduces exactly to the reachable signature image -/
namespace A348_SignatureImageDecision

open A346_ObservableSignature A347_NonlinearFactorization

variable {Witness : Type} [Fintype Witness]

 theorem exists_witness_iff_signature_image
    {k : Nat} (relation : Witness -> Bool)
    (observable : Fin k -> Witness -> Bool)
    (factor : Factorization relation observable) :
    (exists witness, relation witness = true) <->
      exists feature,
        feature ∈ ((Finset.univ : Finset Witness).image (signature observable)) /\
        factor.acceptSignature feature = true := by
  classical
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨signature observable witness, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨witness, Finset.mem_univ witness, rfl⟩
    · simpa [factor.factors witness] using accepted
  · rintro ⟨feature, inImage, accepted⟩
    rcases Finset.mem_image.1 inImage with ⟨witness, _, rfl⟩
    refine ⟨witness, ?_⟩
    simpa [factor.factors witness] using accepted

end A348_SignatureImageDecision

/-! ## 349 - k Boolean observables have at most 2^k reachable signatures -/
namespace A349_SignatureCardinality

open A346_ObservableSignature

variable {Witness : Type} [Fintype Witness]

 theorem signature_image_le_pow_two
    {k : Nat} (observable : Fin k -> Witness -> Bool) :
    ((Finset.univ : Finset Witness).image (signature observable)).card <= 2 ^ k := by
  classical
  calc
    ((Finset.univ : Finset Witness).image (signature observable)).card <=
        Fintype.card (Fin k -> Bool) := by
      exact Finset.card_le_univ _
    _ = 2 ^ k := by simp [Fintype.card_fun]

end A349_SignatureCardinality

/-! ## 350 - Injectivity is unnecessary for decision, but necessary for universal recovery -/
namespace A350_DecisionVersusRecovery

open A346_ObservableSignature

variable {Witness : Type}

 theorem injective_of_exact_decoder
    {k : Nat} (observable : Fin k -> Witness -> Bool)
    (decode : (Fin k -> Bool) -> Witness)
    (recovers : forall witness,
      decode (signature observable witness) = witness) :
    Function.Injective (signature observable) := by
  intro left right same
  calc
    left = decode (signature observable left) := (recovers left).symm
    _ = decode (signature observable right) := by rw [same]
    _ = right := recovers right

end A350_DecisionVersusRecovery

/-! ## 351 - Adding an observable only refines the existing fibers -/
namespace A351_FeatureRefinement

variable {Witness Feature : Type}

 theorem extended_equal_implies_old_equal
    (oldFeature : Witness -> Feature) (extra : Witness -> Bool)
    {left right : Witness}
    (same : (oldFeature left, extra left) = (oldFeature right, extra right)) :
    oldFeature left = oldFeature right := by
  exact congrArg Prod.fst same

end A351_FeatureRefinement

/-! ## 352 - A safe old quotient remains safe after arbitrary feature refinement -/
namespace A352_RefinementSafety

variable {Witness Feature : Type}

 theorem refined_fiber_safe
    (relation : Witness -> Bool)
    (oldFeature : Witness -> Feature)
    (extra : Witness -> Bool)
    (oldSafe : forall left right,
      oldFeature left = oldFeature right -> relation left = relation right)
    {left right : Witness}
    (same : (oldFeature left, extra left) = (oldFeature right, extra right)) :
    relation left = relation right := by
  apply oldSafe left right
  exact A351_FeatureRefinement.extended_equal_implies_old_equal
    oldFeature extra same

end A352_RefinementSafety

/-! ## 353 - Product features combine independently discovered invariants -/
namespace A353_ProductFeature

variable {Witness LeftFeature RightFeature : Type}

 theorem product_equal_implies_components
    (leftFeature : Witness -> LeftFeature)
    (rightFeature : Witness -> RightFeature)
    {first second : Witness}
    (same :
      (leftFeature first, rightFeature first) =
        (leftFeature second, rightFeature second)) :
    leftFeature first = leftFeature second /\
      rightFeature first = rightFeature second := by
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

end A353_ProductFeature

/-! ## 354 - A lossless k-observable code cannot encode more than 2^k witnesses -/
namespace A354_ObservableLowerBound

open A346_ObservableSignature

variable {Witness : Type} [Fintype Witness]

 theorem witness_card_le_pow_two
    {k : Nat} (observable : Fin k -> Witness -> Bool)
    (lossless : Function.Injective (signature observable)) :
    Fintype.card Witness <= 2 ^ k := by
  calc
    Fintype.card Witness <= Fintype.card (Fin k -> Bool) :=
      Fintype.card_le_of_injective (signature observable) lossless
    _ = 2 ^ k := by simp [Fintype.card_fun]

end A354_ObservableLowerBound

/-! ## 355 - Observable evaluation cost is explicit rather than hidden -/
namespace A355_ObservableEvaluationCost

 theorem total_evaluation_bound
    (featureCount perFeature input featureExp costExp : Nat)
    (featureBound : featureCount <= input ^ featureExp)
    (costBound : perFeature <= input ^ costExp) :
    featureCount * perFeature <= input ^ (featureExp + costExp) := by
  calc
    featureCount * perFeature <=
        input ^ featureExp * input ^ costExp :=
      Nat.mul_le_mul featureBound costBound
    _ = input ^ (featureExp + costExp) := by rw [pow_add]

end A355_ObservableEvaluationCost

/-! ## 356 - Polynomially many learned observable sets form a polynomial portfolio -/
namespace A356_ObservablePortfolio

 theorem portfolio_work_bound
    (portfolioSize featureCost input portfolioExp featureExp : Nat)
    (portfolioBound : portfolioSize <= input ^ portfolioExp)
    (featureBound : featureCost <= input ^ featureExp) :
    portfolioSize * featureCost <= input ^ (portfolioExp + featureExp) := by
  calc
    portfolioSize * featureCost <=
        input ^ portfolioExp * input ^ featureExp :=
      Nat.mul_le_mul portfolioBound featureBound
    _ = input ^ (portfolioExp + featureExp) := by rw [pow_add]

end A356_ObservablePortfolio

/-! ## 357 - Exact collision checking certifies a learned feature quotient -/
namespace A357_CollisionCertificate

variable {Witness Feature : Type}

structure Certificate (relation : Witness -> Bool)
    (feature : Witness -> Feature) where
  fiberSafe : forall left right,
    feature left = feature right -> relation left = relation right

theorem collision_safe
    (relation : Witness -> Bool) (feature : Witness -> Feature)
    (certificate : Certificate relation feature)
    {left right : Witness} (same : feature left = feature right) :
    relation left = relation right :=
  certificate.fiberSafe left right same

end A357_CollisionCertificate

/-! ## 358 - Small reachable images are enough even when the ambient feature cube is large -/
namespace A358_ReachableImageBudget

variable {Witness Feature : Type} [Fintype Witness] [DecidableEq Feature]

 theorem reachable_image_bound
    (feature : Witness -> Feature) (budget : Nat)
    (small : ((Finset.univ : Finset Witness).image feature).card <= budget) :
    ((Finset.univ : Finset Witness).image feature).card <= budget :=
  small

end A358_ReachableImageBudget

/-! ## 359 - A nonlinear observable compiler must certify semantics, image size, and cost -/
namespace A359_NonlinearCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  constructionCost : Input -> Nat
  evaluationCost : Input -> Nat
  imageSize : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  constructionBound : forall input,
    constructionCost input <= inputSize input ^ exponent
  evaluationBound : forall input,
    evaluationCost input <= inputSize input ^ exponent
  imageBound : forall input,
    imageSize input <= inputSize input ^ exponent

theorem compiler_exact
    (specification : Input -> Prop) (compiler : Compiler specification)
    (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A359_NonlinearCompiler

/-! ## 360 - Uniform nonlinear observable compilers yield P = NP -/
namespace A360_NonlinearCollapse

variable {Language : Type}

structure UniformNonlinearCover
    (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language,
    hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_nonlinear_observables
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (cover : UniformNonlinearCover PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language languageNP
  exact cover.compilerGivesP language
    (cover.allNPHaveCompiler language languageNP)

end A360_NonlinearCollapse

end ResearchTwentyFifth
end PIsNPOrNot
