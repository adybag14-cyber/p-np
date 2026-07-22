import ResearchEighteenth

namespace PIsNPOrNot
namespace ResearchNineteenth

/-! ## 256 - The unrestricted ordered linear-form search space is quadratic-exponential -/
namespace A256_LinearBasisSearchSpace

theorem ordered_form_ceiling (n : Nat) :
    (2 ^ n) ^ n = 2 ^ (n * n) := by
  rw [← pow_mul]

end A256_LinearBasisSearchSpace

/-! ## 257 - All ordered n-tuples of Boolean linear-form masks have size 2^(n^2) -/
namespace A257_AllMaskFamilies

theorem all_mask_family_card (n : Nat) :
    Fintype.card (Fin n -> (Fin n -> Bool)) = 2 ^ (n * n) := by
  rw [Fintype.card_fun]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul]

end A257_AllMaskFamilies

/-! ## 258 - Any one-bit feature has at most two reachable feature states -/
namespace A258_OneBitImage

variable {Input : Type} [Fintype Input]

theorem boolean_feature_image_le_two (feature : Input -> Bool) :
    ((Finset.univ : Finset Input).image feature).card <= 2 := by
  have subset : ((Finset.univ : Finset Input).image feature) ⊆
      (Finset.univ : Finset Bool) := Finset.subset_univ _
  simpa using Finset.card_le_card subset

end A258_OneBitImage

/-! ## 259 - A k-bit sketch has at most 2^k reachable states -/
namespace A259_KBitSketchImage

variable {Input : Type} [Fintype Input]

theorem sketch_image_le_pow_two
    (k : Nat) (sketch : Input -> (Fin k -> Bool)) :
    ((Finset.univ : Finset Input).image sketch).card <= 2 ^ k := by
  have subset : ((Finset.univ : Finset Input).image sketch) ⊆
      (Finset.univ : Finset (Fin k -> Bool)) := Finset.subset_univ _
  have cardBound := Finset.card_le_card subset
  simpa using cardBound

end A259_KBitSketchImage

/-! ## 260 - Concrete parity is a one-bit witness feature -/
namespace A260_ParityFeature

def xorAll {n : Nat} (bits : Fin n -> Bool) : Bool :=
  (List.ofFn bits).foldl Bool.xor false

def parityRelation {n : Nat} (bits : Fin n -> Bool) : Bool := xorAll bits

theorem parity_factors_through_one_bit {n : Nat} (bits : Fin n -> Bool) :
    parityRelation bits = xorAll bits := rfl

end A260_ParityFeature

/-! ## 261 - Parity therefore has at most two semantic feature states -/
namespace A261_ParityStateBound

open A260_ParityFeature

theorem parity_image_le_two (n : Nat) :
    ((Finset.univ : Finset (Fin n -> Bool)).image xorAll).card <= 2 := by
  exact A258_OneBitImage.boolean_feature_image_le_two xorAll

end A261_ParityStateBound

/-! ## 262 - Bijective basis changes preserve satisfiability before feature compression -/
namespace A262_BasisThenFeature

open ResearchEighteenth.A241_BijectiveTransform
open ResearchSeventeenth.A226_FeatureQuotient

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

theorem transformed_feature_decision
    (relation : Witness -> Bool)
    (transform : Transform (Witness := Witness))
    (quotient : Quotient (Feature := Feature)
      (fun encoded => relation (transform.decode encoded))) :
    (exists witness : Witness, relation witness = true) <->
      exists feature : Feature,
        feature ∈ ((Finset.univ : Finset Witness).image quotient.feature) /\
        quotient.acceptFeature feature = true := by
  rw [ResearchEighteenth.A241_BijectiveTransform.exists_after_decode_iff relation transform]
  exact ResearchSeventeenth.A226_FeatureQuotient.exists_witness_iff_feature_image
    (fun encoded => relation (transform.decode encoded)) quotient

end A262_BasisThenFeature

/-! ## 263 - A listed candidate family succeeds whenever it contains a good transform -/
namespace A263_CandidateBasisCompleteness

variable {Transform : Type}

 theorem family_contains_good_transform
    (family : List Transform) (good : Transform -> Prop)
    (candidate : Transform)
    (member : candidate ∈ family)
    (works : good candidate) :
    exists transform : Transform, transform ∈ family /\ good transform := by
  exact ⟨candidate, member, works⟩

end A263_CandidateBasisCompleteness

/-! ## 264 - Polynomial transform families with polynomial compilation remain polynomial -/
namespace A264_TransformFamilyBudget

theorem transform_search_bound
    (transformCount perTransform input countExponent workExponent : Nat)
    (countBound : transformCount <= input ^ countExponent)
    (workBound : perTransform <= input ^ workExponent) :
    transformCount * perTransform <= input ^ (countExponent + workExponent) := by
  calc
    transformCount * perTransform <=
        (input ^ countExponent) * (input ^ workExponent) :=
      Nat.mul_le_mul countBound workBound
    _ = input ^ (countExponent + workExponent) := by rw [pow_add]

end A264_TransformFamilyBudget

/-! ## 265 - Independent linear equations reduce search to their syndrome image -/
namespace A265_SyndromeImage

variable {Input : Type} [Fintype Input]

theorem syndrome_image_bound
    (equationCount : Nat)
    (syndrome : Input -> (Fin equationCount -> Bool)) :
    ((Finset.univ : Finset Input).image syndrome).card <= 2 ^ equationCount := by
  exact A259_KBitSketchImage.sketch_image_le_pow_two equationCount syndrome

end A265_SyndromeImage

/-! ## 266 - A relation depending only on a syndrome is safely quotientable -/
namespace A266_SyndromeFactorization

variable {Input : Type}

structure SyndromeModel (relation : Input -> Bool) (k : Nat) where
  syndrome : Input -> (Fin k -> Bool)
  decideSyndrome : (Fin k -> Bool) -> Bool
  factors : forall input,
    relation input = decideSyndrome (syndrome input)

theorem equal_syndrome_equal_answer
    (relation : Input -> Bool) (k : Nat)
    (model : SyndromeModel relation k)
    (left right : Input)
    (same : model.syndrome left = model.syndrome right) :
    relation left = relation right := by
  rw [model.factors left, model.factors right, same]

end A266_SyndromeFactorization

/-! ## 267 - A known parity coordinate gives a constant-size decision representation -/
namespace A267_KnownParityCoordinate

open A260_ParityFeature

structure OneCoordinateMachine (n : Nat) where
  coordinate : (Fin n -> Bool) -> Bool
  decide : Bool -> Bool
  exact : forall bits, decide (coordinate bits) = parityRelation bits

def parityMachine (n : Nat) : OneCoordinateMachine n where
  coordinate := xorAll
  decide := fun bit => bit
  exact := by intro bits; rfl

theorem parity_machine_exact (n : Nat) (bits : Fin n -> Bool) :
    (parityMachine n).decide ((parityMachine n).coordinate bits) =
      parityRelation bits := by
  exact (parityMachine n).exact bits

end A267_KnownParityCoordinate

/-! ## 268 - Linear preprocessing cost plus bounded-state traversal composes additively -/
namespace A268_PreprocessTraversalBudget

theorem total_work_bound
    (preprocess traversal preprocessBound traversalBound : Nat)
    (hPreprocess : preprocess <= preprocessBound)
    (hTraversal : traversal <= traversalBound) :
    preprocess + traversal <= preprocessBound + traversalBound := by
  exact Nat.add_le_add hPreprocess hTraversal

end A268_PreprocessTraversalBudget

/-! ## 269 - Exponential full-basis enumeration localizes the construction obstruction -/
namespace A269_BasisEnumerationObstruction

theorem excessive_basis_search_localizes
    (actual polynomialBudget : Nat)
    (tooLarge : polynomialBudget < actual) :
    Not (actual <= polynomialBudget) := by
  omega

end A269_BasisEnumerationObstruction

/-! ## 270 - Uniform polynomial linear-basis sketches would collapse P and NP -/
namespace A270_LinearBasisCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_linear_sketches
    (InP InNP HasPolynomialLinearSketch : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (sketchImpliesP : forall language,
      HasPolynomialLinearSketch language -> InP language)
    (uniform : forall language,
      InNP language -> HasPolynomialLinearSketch language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact sketchImpliesP language (uniform language hNP)

end A270_LinearBasisCollapse

end ResearchNineteenth
end PIsNPOrNot
