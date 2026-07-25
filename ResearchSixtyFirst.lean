import ResearchSixtieth

namespace PIsNPOrNot.ResearchSixtyFirst

/-! ## 886 - A Boolean branch splits a finite candidate set -/
namespace A886_BooleanSplit

variable {U : Type} [DecidableEq U]

def left (candidates : Finset U) (branch : U -> Bool) : Finset U :=
  candidates.filter (fun value => branch value = true)

def right (candidates : Finset U) (branch : U -> Bool) : Finset U :=
  candidates.filter (fun value => branch value = false)

end A886_BooleanSplit

/-! ## 887 - Child cardinalities add to the parent cardinality -/
namespace A887_SplitCardinality

open A886_BooleanSplit

variable {U : Type} [DecidableEq U]

theorem card_left_add_right
    (candidates : Finset U) (branch : U -> Bool) :
    (left candidates branch).card + (right candidates branch).card =
      candidates.card := by
  unfold left right
  have rightEq :
      candidates.filter (fun value => branch value = false) =
        candidates.filter (fun value => Not (branch value = true)) := by
    ext value
    by_cases h : branch value = true
    case pos => simp [h]
    case neg =>
      have hf : branch value = false := Bool.eq_false_iff.mpr h
      simp [h, hf]
  rw [rightEq]
  exact Finset.card_filter_add_card_filter_not
    (s := candidates) (fun value => branch value = true)

end A887_SplitCardinality

/-! ## 888 - A nonempty parent has a nonempty child -/
namespace A888_NonemptyChild

open A886_BooleanSplit

variable {U : Type} [DecidableEq U]

theorem left_or_right_nonempty
    {candidates : Finset U} {branch : U -> Bool}
    (nonempty : candidates.Nonempty) :
    (left candidates branch).Nonempty ∨
      (right candidates branch).Nonempty := by
  let value := nonempty.choose
  have member : Membership.mem candidates value := nonempty.choose_spec
  by_cases h : branch value = true
  case pos =>
    left
    exact Exists.intro value (by simp [left, member, h])
  case neg =>
    right
    have hf : branch value = false := Bool.eq_false_iff.mpr h
    exact Exists.intro value (by simp [right, member, hf])

end A888_NonemptyChild

/-! ## 889 - A nonemptiness oracle answers exact residual-existence queries -/
namespace A889_NonemptyOracle

variable {U : Type} [DecidableEq U]

structure Oracle where
  query : Finset U -> Bool
  exact : forall candidates,
    query candidates = true ↔ candidates.Nonempty

end A889_NonemptyOracle

/-! ## 890 - An exact oracle chooses one residual child -/
namespace A890_OracleChildChoice

open A886_BooleanSplit A889_NonemptyOracle

variable {U : Type} [DecidableEq U]

def chooseChild (oracle : Oracle (U := U)) (candidates : Finset U)
    (branch : U -> Bool) : Finset U :=
  if oracle.query (left candidates branch) = true then
    left candidates branch
  else
    right candidates branch

end A890_OracleChildChoice

/-! ## 891 - Oracle-guided descent preserves a surviving candidate -/
namespace A891_OracleChoiceSound

open A886_BooleanSplit A888_NonemptyChild
open A889_NonemptyOracle A890_OracleChildChoice

variable {U : Type} [DecidableEq U]

theorem chosen_nonempty
    (oracle : Oracle) {candidates : Finset U} {branch : U -> Bool}
    (nonempty : candidates.Nonempty) :
    (chooseChild oracle candidates branch).Nonempty := by
  unfold chooseChild
  split
  next yes =>
    exact (oracle.exact (left candidates branch)).mp yes
  next no =>
    have leftEmpty : ¬(left candidates branch).Nonempty := by
      intro leftNonempty
      exact no ((oracle.exact (left candidates branch)).mpr leftNonempty)
    rcases left_or_right_nonempty nonempty with leftNonempty | rightNonempty
    · exact False.elim (leftEmpty leftNonempty)
    · exact rightNonempty

end A891_OracleChoiceSound

/-! ## 892 - One oracle query is already a residual SAT question -/
namespace A892_ResidualQueryMeaning

open A889_NonemptyOracle

variable {U : Type} [DecidableEq U]

theorem query_true_iff_exists
    (oracle : Oracle) (candidates : Finset U) :
    oracle.query candidates = true ↔
      Exists fun value => value ∈ candidates := by
  rw [oracle.exact]
  rfl

end A892_ResidualQueryMeaning

/-! ## 893 - A complete binary descent plan records one query per level -/
namespace A893_DescentAccounting

structure Plan where
  levels : Nat
  queriesPerLevel : Nat
  queryCost : Nat

def totalWork (plan : Plan) : Nat :=
  plan.levels * plan.queriesPerLevel * plan.queryCost

def oneQueryPerBit (n queryCost : Nat) : Plan where
  levels := n
  queriesPerLevel := 1
  queryCost := queryCost

theorem work_formula (n queryCost : Nat) :
    totalWork (oneQueryPerBit n queryCost) = n * queryCost := by
  simp [totalWork, oneQueryPerBit]

end A893_DescentAccounting

/-! ## 894 - An exact root nonemptiness oracle decides satisfiability -/
namespace A894_RootOracleCircularity

open A889_NonemptyOracle
open ResearchSixtieth.A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

theorem root_query_iff_witness
    (oracle : Oracle) (verifier : U -> Bool) :
    oracle.query (acceptedSet verifier) = true ↔
      Exists fun witness => verifier witness = true := by
  rw [oracle.exact]
  exact ResearchSixtieth.A872_AcceptedNonempty.nonempty_iff_exists verifier

end A894_RootOracleCircularity

/-! ## 895 - A count oracle returns exact finite completion counts -/
namespace A895_CountOracle

variable {U : Type} [DecidableEq U]

structure Oracle where
  count : Finset U -> Nat
  exact : forall candidates, count candidates = candidates.card

end A895_CountOracle

/-! ## 896 - Exact counts satisfy the binary branch recurrence -/
namespace A896_CountRecurrence

open A886_BooleanSplit A895_CountOracle

variable {U : Type} [DecidableEq U]

theorem parent_eq_children
    (oracle : Oracle) (candidates : Finset U) (branch : U -> Bool) :
    oracle.count candidates =
      oracle.count (left candidates branch) +
        oracle.count (right candidates branch) := by
  rw [oracle.exact, oracle.exact, oracle.exact]
  exact (A887_SplitCardinality.card_left_add_right candidates branch).symm

end A896_CountRecurrence

/-! ## 897 - The heavier exact-count child is nonempty when the parent is -/
namespace A897_HeavierChild

open A886_BooleanSplit

variable {U : Type} [DecidableEq U]

def choose (candidates : Finset U) (branch : U -> Bool) : Finset U :=
  if (left candidates branch).card ≤ (right candidates branch).card then
    right candidates branch
  else
    left candidates branch

theorem chosen_nonempty
    {candidates : Finset U} {branch : U -> Bool}
    (nonempty : candidates.Nonempty) :
    (choose candidates branch).Nonempty := by
  unfold choose
  split
  next hle =>
    apply Finset.card_pos.mp
    have parentPositive : 0 < candidates.card := Finset.card_pos.mpr nonempty
    have recurrence := A887_SplitCardinality.card_left_add_right candidates branch
    omega
  next hnot =>
    apply Finset.card_pos.mp
    have parentPositive : 0 < candidates.card := Finset.card_pos.mpr nonempty
    have recurrence := A887_SplitCardinality.card_left_add_right candidates branch
    omega

end A897_HeavierChild

/-! ## 898 - A positive count can vanish modulo its modulus -/
namespace A898_ModularFalseZero

theorem positive_zero_residue (modulus : Nat) (positive : 0 < modulus) :
    modulus % modulus = 0 ∧ 0 < modulus := by
  exact ⟨Nat.mod_self modulus, positive⟩

end A898_ModularFalseZero

/-! ## 899 - A modulus larger than the count makes a zero residue exact -/
namespace A899_LargeModulusExactness

theorem count_eq_zero_of_residue
    {count modulus : Nat}
    (residueZero : count % modulus = 0)
    (below : count < modulus) :
    count = 0 := by
  exact Nat.eq_zero_of_dvd_of_lt
    (Nat.dvd_of_mod_eq_zero residueZero) below

end A899_LargeModulusExactness

/-! ## 900 - A polynomial exact residue compiler would decide witness existence -/
namespace A900_ResidueCompilerCriterion

open ResearchSixtieth.A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

structure Compiler (U : Type) [Fintype U] [DecidableEq U] where
  modulus : Nat
  positiveModulus : 0 < modulus
  largerThanUniverse : Fintype.card U < modulus
  residue : (U -> Bool) -> Nat
  exact : forall verifier,
    residue verifier = (acceptedSet verifier).card % modulus
  constructionCost : Nat
  evaluationCost : Nat

def decideWitness (compiler : Compiler U) (verifier : U -> Bool) : Bool :=
  decide (compiler.residue verifier ≠ 0)

theorem decideWitness_eq_true_iff
    (compiler : Compiler U) (verifier : U -> Bool) :
    decideWitness compiler verifier = true ↔
      Exists fun witness => verifier witness = true := by
  rw [show decideWitness compiler verifier = true ↔
      compiler.residue verifier ≠ 0 by simp [decideWitness]]
  rw [compiler.exact]
  constructor
  · intro residueNonzero
    by_contra noWitness
    have empty : acceptedSet verifier = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro nonempty
      apply noWitness
      exact (ResearchSixtieth.A872_AcceptedNonempty.nonempty_iff_exists verifier).mp nonempty
    simp [empty] at residueNonzero
  · intro witnessExists
    intro residueZero
    have countBound : (acceptedSet verifier).card < compiler.modulus :=
      lt_of_le_of_lt (Finset.card_le_univ (acceptedSet verifier))
        compiler.largerThanUniverse
    have countZero : (acceptedSet verifier).card = 0 :=
      A899_LargeModulusExactness.count_eq_zero_of_residue residueZero countBound
    have empty : acceptedSet verifier = ∅ := Finset.card_eq_zero.mp countZero
    have nonempty : (acceptedSet verifier).Nonempty :=
      (ResearchSixtieth.A872_AcceptedNonempty.nonempty_iff_exists verifier).mpr witnessExists
    rw [empty] at nonempty
    exact Finset.not_nonempty_empty nonempty

end A900_ResidueCompilerCriterion

end PIsNPOrNot.ResearchSixtyFirst
