import ResearchThird

/-!
# Approaches 48-55: affine recognition and proof-carrying structural dispatch

This layer formalizes the Boolean core behind canonical 3-XOR recognition and
Gaussian row operations.  It then states the exact composition principle for a
proof-carrying structural recognizer with a residual fallback.
-/

namespace PIsNPOrNot
namespace ResearchFourth

/-! ## 48 - A canonical four-clause 3-XOR encoding is exact -/
namespace A48_XorEncoding

def xor3 (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c

def clause3 (a b c : Bool) : Bool := a || b || c

def xor3CNF (rhs a b c : Bool) : Bool :=
  if rhs then
    clause3 a b c &&
    clause3 a (!b) (!c) &&
    clause3 (!a) b (!c) &&
    clause3 (!a) (!b) c
  else
    clause3 a b (!c) &&
    clause3 a (!b) c &&
    clause3 (!a) b c &&
    clause3 (!a) (!b) (!c)

theorem xor3CNF_correct (rhs a b c : Bool) :
    xor3CNF rhs a b c = true <-> xor3 a b c = rhs := by
  cases rhs <;> cases a <;> cases b <;> cases c <;>
    decide

theorem opposite_parities_incompatible (a b c : Bool) :
    (xor3CNF false a b c && xor3CNF true a b c) = false := by
  cases a <;> cases b <;> cases c <;> decide

end A48_XorEncoding

/-! ## 49 - Adding one Boolean linear equation to another preserves solutions -/
namespace A49_RowAddition

theorem xor_row_reversible (left right leftRhs rightRhs : Bool)
    (hleft : left = leftRhs) :
    (right = rightRhs <->
      Bool.xor left right = Bool.xor leftRhs rightRhs) := by
  cases left <;> cases right <;> cases leftRhs <;> cases rightRhs <;>
    simp_all

theorem replace_second_row (left right leftRhs rightRhs : Bool) :
    (left = leftRhs /\ right = rightRhs) <->
      (left = leftRhs /\
        Bool.xor left right = Bool.xor leftRhs rightRhs) := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · exact hleft
    · simp [hleft, hright]
  · rintro ⟨hleft, hcombined⟩
    constructor
    · exact hleft
    · exact (xor_row_reversible left right leftRhs rightRhs hleft).mpr hcombined

end A49_RowAddition

/-! ## 50 - A zero row with right-hand side one certifies inconsistency -/
namespace A50_ZeroRowContradiction

theorem zero_equals_one_impossible (h : false = true) : False := by
  cases h

theorem contradictory_equation_has_no_solution
    (lhs : Unit -> Bool) (hlhs : lhs () = false) :
    Not (lhs () = true) := by
  intro htrue
  have : false = true := hlhs.symm.trans htrue
  exact zero_equals_one_impossible this

end A50_ZeroRowContradiction

/-! ## 51 - A proof-carrying recognizer cannot silently misclassify an input -/
namespace A51_ProofCarryingRecognition

variable {I Reduced : Type}

structure Recognized (Yes : I -> Prop) (YesReduced : Reduced -> Prop)
    (input : I) where
  reduced : Reduced
  semantics : YesReduced reduced <-> Yes input

def recognizeResult (Yes : I -> Prop) (YesReduced : Reduced -> Prop)
    (input : I) := Option (Recognized Yes YesReduced input)

theorem recognized_transport
    (Yes : I -> Prop) (YesReduced : Reduced -> Prop)
    {input : I} (certificate : Recognized Yes YesReduced input) :
    YesReduced certificate.reduced <-> Yes input :=
  certificate.semantics

end A51_ProofCarryingRecognition

/-! ## 52 - A proof-carrying affine solver composes with any exact fallback -/
namespace A52_AffineDispatch

open A51_ProofCarryingRecognition

variable {I Affine : Type}

def dispatch
    (Yes : I -> Prop) (YesAffine : Affine -> Prop)
    (recognize : forall input, recognizeResult Yes YesAffine input)
    (affineSolve : Affine -> Bool)
    (fallback : I -> Bool)
    (input : I) : Bool :=
  match recognize input with
  | some certificate => affineSolve certificate.reduced
  | none => fallback input

theorem dispatch_correct
    (Yes : I -> Prop) (YesAffine : Affine -> Prop)
    (recognize : forall input, recognizeResult Yes YesAffine input)
    (affineSolve : Affine -> Bool)
    (fallback : I -> Bool)
    (affineCorrect : forall reduced,
      affineSolve reduced = true <-> YesAffine reduced)
    (fallbackCorrect : forall input,
      fallback input = true <-> Yes input)
    (input : I) :
    dispatch Yes YesAffine recognize affineSolve fallback input = true <-> Yes input := by
  cases hrec : recognize input with
  | none =>
      simpa [dispatch, hrec] using fallbackCorrect input
  | some certificate =>
      calc
        dispatch Yes YesAffine recognize affineSolve fallback input = true <->
            affineSolve certificate.reduced = true := by simp [dispatch, hrec]
        _ <-> YesAffine certificate.reduced := affineCorrect certificate.reduced
        _ <-> Yes input := certificate.semantics

end A52_AffineDispatch

/-! ## 53 - A structural solver only needs a polynomial accounting certificate -/
namespace A53_StructuralCostCertificate

structure PolynomialCost where
  inputSize : Nat
  exponent : Nat
  actualCost : Nat
  bounded : actualCost <= inputSize ^ exponent

theorem compose_costs (left right : PolynomialCost)
    (sameSize : left.inputSize = right.inputSize) :
    left.actualCost + right.actualCost <=
      left.inputSize ^ left.exponent + left.inputSize ^ right.exponent := by
  calc
    left.actualCost + right.actualCost <=
        left.inputSize ^ left.exponent + right.inputSize ^ right.exponent :=
      Nat.add_le_add left.bounded right.bounded
    _ = left.inputSize ^ left.exponent + left.inputSize ^ right.exponent := by
      rw [sameSize]

end A53_StructuralCostCertificate

/-! ## 54 - A finite union of exact structural families remains exact -/
namespace A54_TractableUnion

variable {I : Type}

structure FamilySolver (Yes : I -> Prop) where
  recognizes : I -> Bool
  solve : I -> Bool
  correctWhenRecognized : forall input,
    recognizes input = true -> (solve input = true <-> Yes input)

def coveredBy {Yes : I -> Prop} (families : List (FamilySolver Yes))
    (input : I) : Prop :=
  exists family, family ∈ families /\ family.recognizes input = true

theorem covered_family_sound {Yes : I -> Prop}
    (families : List (FamilySolver Yes)) (input : I)
    (hcover : coveredBy families input) :
    exists family, family ∈ families /\
      (family.solve input = true <-> Yes input) := by
  rcases hcover with ⟨family, hmem, hrec⟩
  exact ⟨family, hmem, family.correctWhenRecognized input hrec⟩

end A54_TractableUnion

/-! ## 55 - Abstract collapse criterion for a polynomial certified cover -/
namespace A55_CertifiedCoverCriterion

variable {Instance : Type}

abbrev Language := Instance -> Prop

structure PolyDecider (Accepts : Language (Instance := Instance)) where
  run : Instance -> Bool
  correct : forall input, run input = true <-> Accepts input
  cost : Instance -> Nat
  size : Instance -> Nat
  exponent : Nat
  polynomial : forall input, cost input <= size input ^ exponent

structure UniformCertifiedCover
    (InNP : Language (Instance := Instance) -> Prop) where
  compile : forall L, InNP L -> PolyDecider L

theorem np_subset_p_of_uniform_certified_cover
    (InNP InP : Language (Instance := Instance) -> Prop)
    (cover : UniformCertifiedCover InNP)
    (polyDeciderInP : forall L, Nonempty (PolyDecider L) -> InP L) :
    forall L, InNP L -> InP L := by
  intro L hNP
  exact polyDeciderInP L ⟨cover.compile L hNP⟩

end A55_CertifiedCoverCriterion

end ResearchFourth
end PIsNPOrNot
