import ResearchFiftyEighth

namespace PIsNPOrNot.ResearchFiftyNinth

/-! ## 856 - Boolean translations form the witness-space action -/
namespace A856_BooleanTranslation

abbrev Bits (n : Nat) := Fin n -> Bool

def translate {n : Nat} (anchor mask : Bits n) : Bits n :=
  fun index => Bool.xor (anchor index) (mask index)

end A856_BooleanTranslation

/-! ## 857 - Every target is one translation away from every anchor -/
namespace A857_TranslationTransitive

open A856_BooleanTranslation

variable {n : Nat}

def maskTo (anchor target : Bits n) : Bits n :=
  fun index => Bool.xor (anchor index) (target index)

theorem translate_maskTo (anchor target : Bits n) :
    translate anchor (maskTo anchor target) = target := by
  funext index
  change Bool.xor (anchor index)
      (Bool.xor (anchor index) (target index)) = target index
  cases anchor index <;> cases target index <;> rfl

end A857_TranslationTransitive

/-! ## 858 - Orbit-OR symmetrisation asks whether any translate accepts -/
namespace A858_OrbitOr

open A856_BooleanTranslation

variable {n : Nat}

def Symmetrized (verifier : Bits n -> Bool) (anchor : Bits n) : Prop :=
  Exists fun mask => verifier (translate anchor mask) = true

end A858_OrbitOr

/-! ## 859 - Translation symmetrisation is exactly witness existence -/
namespace A859_SymmetrizedExistence

open A856_BooleanTranslation A857_TranslationTransitive A858_OrbitOr

variable {n : Nat}

theorem symmetrized_iff_exists
    (verifier : Bits n -> Bool) (anchor : Bits n) :
    Symmetrized verifier anchor ↔
      Exists fun witness => verifier witness = true := by
  constructor
  · rintro ⟨mask, accepted⟩
    exact ⟨translate anchor mask, accepted⟩
  · rintro ⟨witness, accepted⟩
    refine ⟨maskTo anchor witness, ?_⟩
    rw [translate_maskTo]
    exact accepted

end A859_SymmetrizedExistence

/-! ## 860 - The symmetrised existential answer is independent of the anchor -/
namespace A860_AnchorIndependence

open A856_BooleanTranslation A858_OrbitOr

variable {n : Nat}

theorem anchor_independent
    (verifier : Bits n -> Bool) (left right : Bits n) :
    Symmetrized verifier left ↔ Symmetrized verifier right := by
  rw [A859_SymmetrizedExistence.symmetrized_iff_exists,
    A859_SymmetrizedExistence.symmetrized_iff_exists]

end A860_AnchorIndependence

/-! ## 861 - Executing orbit-OR by finite decision is exact -/
namespace A861_ExecutableOrbitOr

open A856_BooleanTranslation

variable {n : Nat}

def decideOrbit (verifier : Bits n -> Bool) (anchor : Bits n) : Bool :=
  decide
    (Exists fun mask : Bits n =>
      verifier (translate anchor mask) = true)

theorem decide_eq_true_iff
    (verifier : Bits n -> Bool) (anchor : Bits n) :
    decideOrbit verifier anchor = true ↔
      Exists fun witness => verifier witness = true := by
  rw [← A859_SymmetrizedExistence.symmetrized_iff_exists verifier anchor]
  simp [decideOrbit, A858_OrbitOr.Symmetrized]

end A861_ExecutableOrbitOr

/-! ## 862 - Full translation symmetrisation enumerates exactly 2^n masks -/
namespace A862_OrbitSize

open A856_BooleanTranslation

variable (n : Nat)

theorem mask_count : Fintype.card (Bits n) = 2 ^ n := by
  simp

end A862_OrbitSize

/-! ## 863 - Orbit-OR collapses every verifier to a constant semantic answer -/
namespace A863_ConstantSymmetrizedAnswer

open A856_BooleanTranslation A858_OrbitOr

variable {n : Nat}

def answer (verifier : Bits n -> Bool) : Bool :=
  decide
    (Exists fun witness : Bits n => verifier witness = true)

theorem symmetrized_eq_answer
    (verifier : Bits n -> Bool) (anchor : Bits n) :
    Symmetrized verifier anchor ↔ answer verifier = true := by
  rw [A859_SymmetrizedExistence.symmetrized_iff_exists]
  simp [answer]

end A863_ConstantSymmetrizedAnswer

/-! ## 864 - A one-state representation can hide the complete SAT answer -/
namespace A864_OneStateCircularity

open A856_BooleanTranslation A858_OrbitOr

variable {n : Nat}

structure OneStateRepresentation (verifier : Bits n -> Bool) where
  state : Unit
  value : Bool
  exact : ∀ anchor, Symmetrized verifier anchor ↔ value = true

noncomputable def representation
    (verifier : Bits n -> Bool) : OneStateRepresentation verifier where
  state := ()
  value := decide
    (Exists fun witness : Bits n => verifier witness = true)
  exact := by
    intro anchor
    rw [A859_SymmetrizedExistence.symmetrized_iff_exists]
    simp

theorem value_true_iff_witness
    (verifier : Bits n -> Bool) :
    (representation verifier).value = true ↔
      Exists fun witness => verifier witness = true := by
  simp [representation]

end A864_OneStateCircularity

/-! ## 865 - Constructing the one-state value already decides witness existence -/
namespace A865_SymmetrizerCircularity

open A856_BooleanTranslation A858_OrbitOr

variable {n : Nat}

theorem evaluator_decides_existence
    (evaluate : (Bits n -> Bool) -> Bits n -> Bool)
    (correct : ∀ verifier anchor,
      evaluate verifier anchor = true ↔ Symmetrized verifier anchor)
    (verifier : Bits n -> Bool) (anchor : Bits n) :
    evaluate verifier anchor = true ↔
      Exists fun witness => verifier witness = true := by
  rw [correct, A859_SymmetrizedExistence.symmetrized_iff_exists]

end A865_SymmetrizerCircularity

/-! ## 866 - The algebraic reject product is zero exactly when a witness exists -/
namespace A866_RejectionProduct

open A856_BooleanTranslation

variable {n : Nat}

def rejectFactor (verifier : Bits n -> Bool) (anchor mask : Bits n) : Nat :=
  if verifier (translate anchor mask) = true then 0 else 1

def rejectionProduct (verifier : Bits n -> Bool) (anchor : Bits n) : Nat :=
  (Finset.univ : Finset (Bits n)).prod
    (fun mask => rejectFactor verifier anchor mask)

theorem product_eq_zero_iff
    (verifier : Bits n -> Bool) (anchor : Bits n) :
    rejectionProduct verifier anchor = 0 ↔
      Exists fun witness => verifier witness = true := by
  rw [← A859_SymmetrizedExistence.symmetrized_iff_exists verifier anchor]
  constructor
  case mp =>
    intro productZero
    unfold rejectionProduct at productZero
    have zeroFactor := Finset.prod_eq_zero_iff.mp productZero
    let mask := zeroFactor.choose
    have factorZero : rejectFactor verifier anchor mask = 0 := by
      simpa [mask] using zeroFactor.choose_spec.2
    refine Exists.intro mask ?_
    by_cases accepted : verifier (translate anchor mask) = true
    case pos => exact accepted
    case neg =>
      have contradiction := factorZero
      simp [rejectFactor, accepted] at contradiction
  case mpr =>
    intro symmetrized
    let mask := symmetrized.choose
    have accepted : verifier (translate anchor mask) = true := by
      simpa [mask] using symmetrized.choose_spec
    unfold rejectionProduct
    apply Finset.prod_eq_zero (Finset.mem_univ mask)
    simp [rejectFactor, accepted]

end A866_RejectionProduct

/-! ## 867 - The direct algebraic product contains 2^n verifier factors -/
namespace A867_ProductFactorCount

structure ProductPlan where
  inputBits : Nat
  factors : Nat
  verifierCost : Nat

def direct (n verifierCost : Nat) : ProductPlan where
  inputBits := n
  factors := 2 ^ n
  verifierCost := verifierCost

def work (plan : ProductPlan) : Nat :=
  plan.factors * plan.verifierCost

theorem direct_work (n verifierCost : Nat) :
    work (direct n verifierCost) = 2 ^ n * verifierCost := rfl

end A867_ProductFactorCount

/-! ## 868 - A compact semantic orbit does not imply compact orbit aggregation -/
namespace A868_SemanticAggregationGap

structure Profile where
  semanticAnswers : Nat
  orbitElements : Nat
  aggregationWork : Nat

def translationProfile (n verifierCost : Nat) : Profile where
  semanticAnswers := 1
  orbitElements := 2 ^ n
  aggregationWork := 2 ^ n * verifierCost

theorem one_answer_exponential_orbit (n verifierCost : Nat) :
    (translationProfile n verifierCost).semanticAnswers = 1 ∧
    (translationProfile n verifierCost).orbitElements = 2 ^ n := by
  exact ⟨rfl, rfl⟩

end A868_SemanticAggregationGap

/-! ## 869 - Any exact fast orbit aggregator would be a SAT algorithm -/
namespace A869_OrbitAggregatorCriterion

open A856_BooleanTranslation

structure Aggregator (n : Nat) where
  evaluate : (Bits n -> Bool) -> Bool
  exact : ∀ verifier,
    evaluate verifier = true ↔
      Exists fun witness => verifier witness = true
  constructionCost : Nat
  evaluationCost : Nat

theorem decides {n : Nat}
    (aggregator : Aggregator n) (verifier : Bits n -> Bool) :
    aggregator.evaluate verifier = true ↔
      Exists fun witness => verifier witness = true :=
  aggregator.exact verifier

end A869_OrbitAggregatorCriterion

/-! ## 870 - Translation symmetry moves the hard step into exact aggregation -/
namespace A870_TranslationProofAttempt

structure Attempt where
  inputBits : Nat
  semanticStates : Nat
  groupElements : Nat
  exactAggregationCost : Nat

def translationAttempt (n aggregationCost : Nat) : Attempt where
  inputBits := n
  semanticStates := 1
  groupElements := 2 ^ n
  exactAggregationCost := aggregationCost

theorem semantic_collapse_does_not_bound_work
    (n aggregationCost : Nat) :
    (translationAttempt n aggregationCost).semanticStates = 1 ∧
    (translationAttempt n aggregationCost).groupElements = 2 ^ n := by
  exact ⟨rfl, rfl⟩

end A870_TranslationProofAttempt

end PIsNPOrNot.ResearchFiftyNinth

