import ResearchTwelfth

namespace PIsNPOrNot
namespace ResearchThirteenth

/-! ## 166 - Exact overlap accounting -/
namespace A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

def overlapCredit (left right : Finset State) : Nat :=
  (left ∩ right).card

theorem union_plus_overlap (left right : Finset State) :
    (left ∪ right).card + overlapCredit left right =
      left.card + right.card := by
  exact Finset.card_union_add_card_inter left right

end A166_OverlapAccounting

/-! ## 167 - Overlap cannot exceed either child -/
namespace A167_OverlapUpperBound

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem overlap_le_left (left right : Finset State) :
    overlapCredit left right <= left.card := by
  apply Finset.card_le_card
  intro state h
  have hh : state ∈ left ∧ state ∈ right := by
    simpa only [Finset.mem_inter] using h
  exact hh.1

theorem overlap_le_right (left right : Finset State) :
    overlapCredit left right <= right.card := by
  apply Finset.card_le_card
  intro state h
  have hh : state ∈ left ∧ state ∈ right := by
    simpa only [Finset.mem_inter] using h
  exact hh.2

end A167_OverlapUpperBound

/-! ## 168 - Enlarging both reachable sets cannot reduce overlap -/
namespace A168_OverlapMonotonicity

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem overlap_mono
    (left right largerLeft largerRight : Finset State)
    (hLeft : left ⊆ largerLeft)
    (hRight : right ⊆ largerRight) :
    overlapCredit left right <= overlapCredit largerLeft largerRight := by
  apply Finset.card_le_card
  intro state h
  have hh : state ∈ left ∧ state ∈ right := by
    simpa only [Finset.mem_inter] using h
  have result : state ∈ largerLeft ∧ state ∈ largerRight :=
    ⟨hLeft hh.1, hRight hh.2⟩
  simpa only [Finset.mem_inter] using result

end A168_OverlapMonotonicity

/-! ## 169 - Any certified common core earns sharing credit -/
namespace A169_CommonCoreCredit

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem common_core_credit
    (core left right : Finset State)
    (hLeft : core ⊆ left)
    (hRight : core ⊆ right) :
    (left ∪ right).card + core.card <= left.card + right.card := by
  have hCore : core.card <= overlapCredit left right := by
    apply Finset.card_le_card
    intro state hState
    have result : state ∈ left ∧ state ∈ right :=
      ⟨hLeft hState, hRight hState⟩
    simpa only [Finset.mem_inter] using result
  have hExact := union_plus_overlap left right
  omega

end A169_CommonCoreCredit

/-! ## 170 - More overlap cannot hurt when child sums are equal -/
namespace A170_EqualSumComparison

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem union_nonincreasing_of_overlap
    (leftA rightA leftB rightB : Finset State)
    (sameSum : leftA.card + rightA.card = leftB.card + rightB.card)
    (moreOverlap : overlapCredit leftA rightA <= overlapCredit leftB rightB) :
    (leftB ∪ rightB).card <= (leftA ∪ rightA).card := by
  have hA := union_plus_overlap leftA rightA
  have hB := union_plus_overlap leftB rightB
  omega

end A170_EqualSumComparison

/-! ## 171 - Strictly more overlap gives a strict global saving -/
namespace A171_StrictOverlapSaving

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem union_strictly_smaller_of_overlap
    (leftA rightA leftB rightB : Finset State)
    (sameSum : leftA.card + rightA.card = leftB.card + rightB.card)
    (moreOverlap : overlapCredit leftA rightA < overlapCredit leftB rightB) :
    (leftB ∪ rightB).card < (leftA ∪ rightA).card := by
  have hA := union_plus_overlap leftA rightA
  have hB := union_plus_overlap leftB rightB
  omega

end A171_StrictOverlapSaving

/-! ## 172 - A fully reused candidate adds no states -/
namespace A172_FullReuse

variable {State : Type} [DecidableEq State]

theorem union_eq_existing_of_subset
    (existing candidate : Finset State)
    (reused : candidate ⊆ existing) :
    existing ∪ candidate = existing := by
  ext state
  constructor
  · intro h
    have hh : state ∈ existing ∨ state ∈ candidate := by
      simpa only [Finset.mem_union] using h
    rcases hh with hExisting | hCandidate
    · exact hExisting
    · exact reused hCandidate
  · intro h
    have result : state ∈ existing ∨ state ∈ candidate := Or.inl h
    simpa only [Finset.mem_union] using result

theorem reused_candidate_adds_zero
    (existing candidate : Finset State)
    (reused : candidate ⊆ existing) :
    (existing ∪ candidate).card = existing.card := by
  rw [union_eq_existing_of_subset existing candidate reused]

end A172_FullReuse

/-! ## 173 - Zero overlap means no sharing discount -/
namespace A173_ZeroOverlapAccounting

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

theorem union_card_eq_sum_of_zero_overlap
    (left right : Finset State)
    (noOverlap : overlapCredit left right = 0) :
    (left ∪ right).card = left.card + right.card := by
  have h := union_plus_overlap left right
  omega

end A173_ZeroOverlapAccounting

/-! ## 174 - Union of an entire policy portfolio -/
namespace A174_PortfolioUnion

variable {State : Type} [DecidableEq State]

def unionAll : List (Finset State) -> Finset State
  | [] => ∅
  | states :: rest => states ∪ unionAll rest

theorem mem_unionAll
    (state : State) (portfolio : List (Finset State)) :
    state ∈ unionAll portfolio <->
      exists states, states ∈ portfolio /\ state ∈ states := by
  induction portfolio with
  | nil => simp [unionAll]
  | cons head tail ih =>
      simp [unionAll, ih]

end A174_PortfolioUnion

/-! ## 175 - Portfolio union is bounded by the sum of individual sizes -/
namespace A175_PortfolioUnionBound

open A174_PortfolioUnion
open PIsNPOrNot.ResearchTwelfth.A158_SharingUpperBound

variable {State : Type} [DecidableEq State]

theorem card_unionAll_le_sum (portfolio : List (Finset State)) :
    (unionAll portfolio).card <= (portfolio.map Finset.card).sum := by
  induction portfolio with
  | nil => simp [unionAll]
  | cons head tail ih =>
      simp only [unionAll, List.map_cons, List.sum_cons]
      have hUnion := union_card_le_sum head (unionAll tail)
      omega

end A175_PortfolioUnionBound

/-! ## 176 - Bounded policy count and bounded policy size compose -/
namespace A176_PolynomialPortfolioStates

open A174_PortfolioUnion A175_PortfolioUnionBound

variable {State : Type} [DecidableEq State]

theorem sum_card_le_length_mul
    (portfolio : List (Finset State)) (width : Nat)
    (hWidth : forall states, states ∈ portfolio -> states.card <= width) :
    (portfolio.map Finset.card).sum <= portfolio.length * width := by
  induction portfolio with
  | nil => simp
  | cons head tail ih =>
      have hHead : head.card <= width := hWidth head (by simp)
      have hTail : forall states, states ∈ tail -> states.card <= width := by
        intro states hMem
        exact hWidth states (by simp [hMem])
      have hRec := ih hTail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        head.card + (tail.map Finset.card).sum <=
            width + tail.length * width := Nat.add_le_add hHead hRec
        _ = (tail.length + 1) * width := by
          rw [Nat.add_mul, one_mul]
          omega

theorem portfolio_state_bound
    (portfolio : List (Finset State)) (count width : Nat)
    (hCount : portfolio.length <= count)
    (hWidth : forall states, states ∈ portfolio -> states.card <= width) :
    (unionAll portfolio).card <= count * width := by
  have hUnion := card_unionAll_le_sum portfolio
  have hSum := sum_card_le_length_mul portfolio width hWidth
  have hMul : portfolio.length * width <= count * width :=
    Nat.mul_le_mul_right width hCount
  exact le_trans hUnion (le_trans hSum hMul)

end A176_PolynomialPortfolioStates

/-! ## 177 - Separator assignments times residual width -/
namespace A177_SeparatorCrossProduct

theorem separator_cross_product_bound
    (assignments width input assignmentExponent widthExponent : Nat)
    (hAssignments : assignments <= input ^ assignmentExponent)
    (hWidth : width <= input ^ widthExponent) :
    assignments * width <=
      (input ^ assignmentExponent) * (input ^ widthExponent) := by
  exact Nat.mul_le_mul hAssignments hWidth

end A177_SeparatorCrossProduct

/-! ## 178 - A branch certificate records exact shared cost -/
namespace A178_BranchPotentialCertificate

open A166_OverlapAccounting

variable {State : Type} [DecidableEq State]

structure Certificate where
  left : Finset State
  right : Finset State
  sharedCost : Nat
  exact : sharedCost + overlapCredit left right = left.card + right.card

def makeCertificate (left right : Finset State) : Certificate (State := State) where
  left := left
  right := right
  sharedCost := (left ∪ right).card
  exact := union_plus_overlap left right

theorem certificate_cost (left right : Finset State) :
    (makeCertificate left right).sharedCost = (left ∪ right).card := rfl

end A178_BranchPotentialCertificate

/-! ## 179 - Monotone globally measured policy replacement -/
namespace A179_MonotonePotentialSearch

structure Candidate where
  answer : Bool
  cost : Nat

inductive Improves : Candidate -> Candidate -> Prop
  | step (old new : Candidate)
      (sameAnswer : new.answer = old.answer)
      (nonworse : new.cost <= old.cost) :
      Improves old new

theorem replacement_preserves_answer
    {old new : Candidate} (improves : Improves old new) :
    new.answer = old.answer := by
  cases improves with
  | step sameAnswer nonworse => exact sameAnswer

theorem replacement_nonworse
    {old new : Candidate} (improves : Improves old new) :
    new.cost <= old.cost := by
  cases improves with
  | step sameAnswer nonworse => exact nonworse

end A179_MonotonePotentialSearch

/-! ## 180 - Uniform polynomial overlap-aware policies imply collapse -/
namespace A180_OverlapPolicyCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_overlap_policies
    (InP InNP : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (hasOverlapPolicy : Language -> Prop)
    (policyImpliesP : forall language,
      hasOverlapPolicy language -> InP language)
    (uniform : forall language,
      InNP language -> hasOverlapPolicy language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact policyImpliesP language (uniform language hNP)

end A180_OverlapPolicyCollapse

end ResearchThirteenth
end PIsNPOrNot
