import ResearchFifteenth

namespace PIsNPOrNot
namespace ResearchSixteenth

/-! ## 211 - Policy candidates carry a closure and coherent choices -/
namespace A211_PolicyCandidate

open PIsNPOrNot.ResearchFifteenth.A196_TransitionSystem

structure Candidate
    (State Choice : Type)
    [DecidableEq State] where
  states : Finset State
  policy : Policy State Choice

end A211_PolicyCandidate

/-! ## 212 - Candidate compatibility on shared states -/
namespace A212_CandidateCompatibility

open PIsNPOrNot.ResearchFifteenth.A196_TransitionSystem
open A211_PolicyCandidate

variable {State Choice : Type} [DecidableEq State]

def Compatible
    (left right : Candidate State Choice) : Prop :=
  forall state,
    state ∈ left.states ->
    state ∈ right.states ->
    left.policy state = right.policy state

end A212_CandidateCompatibility

/-! ## 213 - Dominance means fewer states with identical retained choices -/
namespace A213_CandidateDominance

open PIsNPOrNot.ResearchFifteenth.A196_TransitionSystem
open A211_PolicyCandidate

variable {State Choice : Type} [DecidableEq State]

def Dominates
    (left right : Candidate State Choice) : Prop :=
  left.states ⊆ right.states /\
    forall state, state ∈ left.states ->
      left.policy state = right.policy state

end A213_CandidateDominance

/-! ## 214 - Candidate dominance is reflexive -/
namespace A214_DominanceReflexive

open A211_PolicyCandidate A213_CandidateDominance

variable {State Choice : Type} [DecidableEq State]

theorem dominates_refl (candidate : Candidate State Choice) :
    Dominates candidate candidate := by
  constructor
  · exact Finset.Subset.rfl
  · intro state hState
    rfl

end A214_DominanceReflexive

/-! ## 215 - Candidate dominance is transitive -/
namespace A215_DominanceTransitive

open A211_PolicyCandidate A213_CandidateDominance

variable {State Choice : Type} [DecidableEq State]

theorem dominates_trans
    {first second third : Candidate State Choice}
    (hFirst : Dominates first second)
    (hSecond : Dominates second third) :
    Dominates first third := by
  constructor
  · exact fun state hState => hSecond.1 (hFirst.1 hState)
  · intro state hState
    calc
      first.policy state = second.policy state := hFirst.2 state hState
      _ = third.policy state := hSecond.2 state (hFirst.1 hState)

end A215_DominanceTransitive

/-! ## 216 - A dominating candidate preserves compatibility with any extension -/
namespace A216_CompatibilityTransfer

open A211_PolicyCandidate A212_CandidateCompatibility
open A213_CandidateDominance

variable {State Choice : Type} [DecidableEq State]

theorem compatible_of_dominates
    {smaller larger external : Candidate State Choice}
    (dominates : Dominates smaller larger)
    (compatible : Compatible larger external) :
    Compatible smaller external := by
  intro state hSmall hExternal
  calc
    smaller.policy state = larger.policy state := dominates.2 state hSmall
    _ = external.policy state :=
      compatible state (dominates.1 hSmall) hExternal

end A216_CompatibilityTransfer

/-! ## 217 - Candidate composition uses the union of reachable states -/
namespace A217_CandidateUnion

open A211_PolicyCandidate

variable {State Choice : Type} [DecidableEq State]

def unionStates
    (left right : Candidate State Choice) : Finset State :=
  left.states ∪ right.states

end A217_CandidateUnion

/-! ## 218 - Dominance transfers through union with an external candidate -/
namespace A218_UnionDominance

open A211_PolicyCandidate A213_CandidateDominance A217_CandidateUnion

variable {State Choice : Type} [DecidableEq State]

theorem union_subset_union
    {smaller larger external : Candidate State Choice}
    (dominates : Dominates smaller larger) :
    unionStates smaller external ⊆ unionStates larger external := by
  intro state hState
  have h : state ∈ smaller.states ∨ state ∈ external.states := by
    simpa only [unionStates, Finset.mem_union] using hState
  have result : state ∈ larger.states ∨ state ∈ external.states := by
    rcases h with hSmall | hExternal
    · exact Or.inl (dominates.1 hSmall)
    · exact Or.inr hExternal
  simpa only [unionStates, Finset.mem_union] using result

end A218_UnionDominance

/-! ## 219 - Dominance never increases composed state cost -/
namespace A219_UnionCostNonworsening

open A211_PolicyCandidate A213_CandidateDominance A217_CandidateUnion
open A218_UnionDominance

variable {State Choice : Type} [DecidableEq State]

theorem union_card_le
    {smaller larger external : Candidate State Choice}
    (dominates : Dominates smaller larger) :
    (unionStates smaller external).card <=
      (unionStates larger external).card := by
  exact Finset.card_le_card (union_subset_union dominates)

end A219_UnionCostNonworsening

/-! ## 220 - Proper composed inclusion gives a strict pruning advantage -/
namespace A220_UnionCostStrict

open A211_PolicyCandidate A213_CandidateDominance A217_CandidateUnion
open A218_UnionDominance

variable {State Choice : Type} [DecidableEq State]

theorem union_card_lt
    {smaller larger external : Candidate State Choice}
    (dominates : Dominates smaller larger)
    (different : unionStates smaller external ≠
      unionStates larger external) :
    (unionStates smaller external).card <
      (unionStates larger external).card := by
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_subset_ne).2
    ⟨union_subset_union dominates, different⟩

end A220_UnionCostStrict

/-! ## 221 - Safe pruning preserves both compatibility and cost -/
namespace A221_SafePruning

open A211_PolicyCandidate A212_CandidateCompatibility
open A213_CandidateDominance A216_CompatibilityTransfer
open A217_CandidateUnion A219_UnionCostNonworsening

variable {State Choice : Type} [DecidableEq State]

theorem prune_dominated
    {smaller larger external : Candidate State Choice}
    (dominates : Dominates smaller larger)
    (compatible : Compatible larger external) :
    Compatible smaller external /\
      (unionStates smaller external).card <=
        (unionStates larger external).card := by
  exact ⟨compatible_of_dominates dominates compatible,
    union_card_le dominates⟩

end A221_SafePruning

/-! ## 222 - An undominated frontier contains no safely removable pair -/
namespace A222_UndominatedFrontier

open A211_PolicyCandidate A213_CandidateDominance

variable {State Choice : Type} [DecidableEq State]

def Undominated
    (frontier : Finset (Candidate State Choice)) : Prop :=
  forall left, left ∈ frontier ->
    forall right, right ∈ frontier ->
      Dominates left right -> left = right

end A222_UndominatedFrontier

/-! ## 223 - A candidate dominated by a frontier member may be discarded -/
namespace A223_FrontierPruningCertificate

open A211_PolicyCandidate A213_CandidateDominance
open A222_UndominatedFrontier

variable {State Choice : Type} [DecidableEq State]

structure PruningCertificate
    (frontier : Finset (Candidate State Choice))
    (discarded : Candidate State Choice) where
  witness : Candidate State Choice
  witness_mem : witness ∈ frontier
  dominates : Dominates witness discarded

theorem has_replacement
    {frontier : Finset (Candidate State Choice)}
    {discarded : Candidate State Choice}
    (certificate : PruningCertificate frontier discarded) :
    exists witness, witness ∈ frontier /\ Dominates witness discarded := by
  exact ⟨certificate.witness,
    certificate.witness_mem, certificate.dominates⟩

end A223_FrontierPruningCertificate

/-! ## 224 - Pairwise frontier combination has a product bound -/
namespace A224_FrontierProductBudget

theorem pair_count_bound
    (leftCount rightCount input leftExponent rightExponent : Nat)
    (hLeft : leftCount <= input ^ leftExponent)
    (hRight : rightCount <= input ^ rightExponent) :
    leftCount * rightCount <=
      (input ^ leftExponent) * (input ^ rightExponent) := by
  exact Nat.mul_le_mul hLeft hRight

end A224_FrontierProductBudget

/-! ## 225 - Uniform polynomial undominated frontiers imply collapse -/
namespace A225_FrontierCollapseCriterion

variable {Language : Type}

theorem p_eq_np_of_uniform_polynomial_frontiers
    (InP InNP : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (hasPolynomialFrontier : Language -> Prop)
    (frontierImpliesP : forall language,
      hasPolynomialFrontier language -> InP language)
    (uniform : forall language,
      InNP language -> hasPolynomialFrontier language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact frontierImpliesP language (uniform language hNP)

end A225_FrontierCollapseCriterion

end ResearchSixteenth
end PIsNPOrNot
