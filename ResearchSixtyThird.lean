import ResearchSixtySecond

namespace PIsNPOrNot.ResearchSixtyThird

open ResearchSixtySecond.A901_BooleanFunctionUniverse
open ResearchSixtySecond.A904_DescriptionEvaluator

/-! ## 916 - All n-bit Boolean functions form an explicit finite set -/
namespace A916_AllFunctions

noncomputable def allFunctions (n : Nat) : Finset (BoolFn n) := by
  classical
  exact Finset.univ

end A916_AllFunctions

/-! ## 917 - Hard candidates are the functions outside the circuit-code image -/
namespace A917_HardCandidateSet

noncomputable def hardCandidates {n b : Nat}
    (evaluate : Code b -> BoolFn n) : Finset (BoolFn n) := by
  classical
  exact (A916_AllFunctions.allFunctions n).filter
    (fun function => Not (Membership.mem (image evaluate) function))

end A917_HardCandidateSet

/-! ## 918 - Membership in the hard-candidate set is exactly non-representability -/
namespace A918_HardCandidateMembership

 theorem hard_mem_iff {n b : Nat} (evaluate : Code b -> BoolFn n)
    (function : BoolFn n) :
    Membership.mem (A917_HardCandidateSet.hardCandidates evaluate) function <->
      Not (Membership.mem (image evaluate) function) := by
  classical
  simp [A917_HardCandidateSet.hardCandidates, A916_AllFunctions.allFunctions]

end A918_HardCandidateMembership

/-! ## 919 - The hard-candidate set is nonempty under the counting gap -/
namespace A919_HardCandidateNonempty

 theorem nonempty {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) :
    (A917_HardCandidateSet.hardCandidates evaluate).Nonempty := by
  classical
  obtain ⟨hard, outside⟩ :=
    ResearchSixtySecond.A909_HardFunctionExistence.exists_outside_image evaluate small
  refine Exists.intro hard ?_
  apply (A918_HardCandidateMembership.hard_mem_iff evaluate hard).mpr
  intro represented
  rcases Finset.mem_image.mp represented with ⟨code, _member, equality⟩
  exact outside code equality

end A919_HardCandidateNonempty

/-! ## 920 - Exhaustive selection chooses one hard truth table -/
namespace A920_ExhaustiveHardSelection

noncomputable def selected {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) : BoolFn n :=
  (A919_HardCandidateNonempty.nonempty evaluate small).choose

end A920_ExhaustiveHardSelection

/-! ## 921 - The exhaustively selected truth table is not represented -/
namespace A921_ExhaustiveSelectionHard

 theorem selected_outside {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) :
    Not (Membership.mem (image evaluate)
      (A920_ExhaustiveHardSelection.selected evaluate small)) := by
  exact (A918_HardCandidateMembership.hard_mem_iff evaluate
    (A920_ExhaustiveHardSelection.selected evaluate small)).mp
      (A919_HardCandidateNonempty.nonempty evaluate small).choose_spec

end A921_ExhaustiveSelectionHard

/-! ## 922 - Exhaustive selection ranges over 2^(2^n) candidate truth tables -/
namespace A922_CandidateCount

 theorem candidate_count (n : Nat) :
    (A916_AllFunctions.allFunctions n).card = 2 ^ (2 ^ n) := by
  classical
  simp [A916_AllFunctions.allFunctions,
    ResearchSixtySecond.A903_FunctionCardinality.function_card]

end A922_CandidateCount

/-! ## 923 - Every candidate may be compared with all 2^b circuit descriptions -/
namespace A923_ComparisonProfile

structure Profile where
  inputBits : Nat
  codeBits : Nat
  candidates : Nat
  descriptions : Nat
  truthTableBits : Nat

 def exhaustive (n b : Nat) : Profile where
  inputBits := n
  codeBits := b
  candidates := 2 ^ (2 ^ n)
  descriptions := 2 ^ b
  truthTableBits := 2 ^ n

end A923_ComparisonProfile

/-! ## 924 - Naive exhaustive construction multiplies candidate and code counts -/
namespace A924_ExhaustiveWork

open A923_ComparisonProfile

def comparisons (profile : Profile) : Nat :=
  profile.candidates * profile.descriptions

 theorem exhaustive_formula (n b : Nat) :
    comparisons (exhaustive n b) = 2 ^ (2 ^ n) * 2 ^ b := rfl

end A924_ExhaustiveWork

/-! ## 925 - The naive comparison count is at least the full function count -/
namespace A925_ExhaustiveLowerBound

 theorem candidates_le_comparisons (n b : Nat) :
    2 ^ (2 ^ n) <= A924_ExhaustiveWork.comparisons
      (A923_ComparisonProfile.exhaustive n b) := by
  rw [A924_ExhaustiveWork.exhaustive_formula]
  exact Nat.le_mul_of_pos_right _ (pow_pos (by decide) b)

end A925_ExhaustiveLowerBound

/-! ## 926 - Evaluating a stored truth table is easy only after exponential storage -/
namespace A926_TableLookup

structure StoredTable (n : Nat) where
  table : BoolFn n
  storedBits : Nat
  exactStorage : storedBits = 2 ^ n

 def evaluate {n : Nat} (stored : StoredTable n) : BoolFn n := stored.table

end A926_TableLookup

/-! ## 927 - The direct stored representation requires one bit per input assignment -/
namespace A927_StoredTableCost

 theorem storage_formula {n : Nat} (stored : A926_TableLookup.StoredTable n) :
    stored.storedBits = 2 ^ n := stored.exactStorage

end A927_StoredTableCost

/-! ## 928 - Counting hardness and efficient per-input evaluation are distinct fields -/
namespace A928_ExplicitHardPackage

structure Package (n b : Nat) (evaluateCode : Code b -> BoolFn n) where
  function : BoolFn n
  outside : forall code, Not (evaluateCode code = function)
  constructionCost : Nat
  evaluationCost : Nat
  representationBits : Nat

end A928_ExplicitHardPackage

/-! ## 929 - A truth-table package exposes its exponential representation cost -/
namespace A929_TablePackage

noncomputable def package {n b : Nat} (evaluateCode : Code b -> BoolFn n)
    (small : b < 2 ^ n) :
    A928_ExplicitHardPackage.Package n b evaluateCode where
  function := A920_ExhaustiveHardSelection.selected evaluateCode small
  outside := by
    intro code equality
    apply A921_ExhaustiveSelectionHard.selected_outside evaluateCode small
    apply Finset.mem_image.mpr
    exact ⟨code, Finset.mem_univ code, equality⟩
  constructionCost := 2 ^ (2 ^ n) * 2 ^ b
  evaluationCost := 1
  representationBits := 2 ^ n

 theorem representation_formula {n b : Nat} (evaluateCode : Code b -> BoolFn n)
    (small : b < 2 ^ n) :
    (package evaluateCode small).representationBits = 2 ^ n := rfl

end A929_TablePackage

/-! ## 930 - A P-versus-NP separation needs uniform explicitness, not a hard table alone -/
namespace A930_UniformExplicitnessCriterion

structure UniformCandidate where
  descriptionAt : Nat -> Nat
  evaluationAt : Nat -> Nat
  constructionAt : Nat -> Nat
  hardAgainst : Nat -> Nat

 def totalAt (candidate : UniformCandidate) (n : Nat) : Nat :=
  candidate.descriptionAt n + candidate.evaluationAt n +
    candidate.constructionAt n

 theorem total_charges_construction (candidate : UniformCandidate) (n : Nat) :
    candidate.constructionAt n <= totalAt candidate n := by
  unfold totalAt
  omega

end A930_UniformExplicitnessCriterion

end PIsNPOrNot.ResearchSixtyThird
