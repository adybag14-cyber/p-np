import ResearchEleventh

/-!
# Global adaptive-policy accounting

Approaches 151-165 formalize the distinction exposed by the experiments:
an adaptive model contains every fixed-order policy, but a local tree score need
not minimize the globally shared DAG. Safe search must retain an exact baseline
and accept only globally measured improvements.
-/

namespace PIsNPOrNot
namespace ResearchTwelfth

/-! ## 151 - A finite policy result -/
namespace A151_PolicyResult

structure PolicyResult (State : Type) [DecidableEq State] where
  reachable : Finset State
  answer : Bool

def PolicyResult.cost {State : Type} [DecidableEq State]
    (result : PolicyResult State) : Nat :=
  result.reachable.card

end A151_PolicyResult

/-! ## 152 - Reachable-state inclusion implies a cost bound -/
namespace A152_StateDominance

open A151_PolicyResult

variable {State : Type} [DecidableEq State]

def Dominates (left right : PolicyResult State) : Prop :=
  left.reachable ⊆ right.reachable

theorem cost_le_of_dominates (left right : PolicyResult State)
    (dominates : Dominates left right) :
    left.cost <= right.cost := by
  unfold PolicyResult.cost
  exact Finset.card_le_card dominates

end A152_StateDominance

/-! ## 153 - Choosing the globally smaller exact result is safe -/
namespace A153_SafeGlobalChoice

open A151_PolicyResult

variable {State Instance : Type} [DecidableEq State]

def Exact (Yes : Instance -> Prop) (input : Instance)
    (result : PolicyResult State) : Prop :=
  result.answer = true <-> Yes input

def chooseBetter (baseline candidate : PolicyResult State) : PolicyResult State :=
  if candidate.cost <= baseline.cost then candidate else baseline

theorem chooseBetter_cost_le (baseline candidate : PolicyResult State) :
    (chooseBetter baseline candidate).cost <= baseline.cost := by
  unfold chooseBetter
  split
  case isTrue h => simpa using h
  case isFalse h => simp

theorem chooseBetter_exact
    (Yes : Instance -> Prop) (input : Instance)
    (baseline candidate : PolicyResult State)
    (baselineExact : Exact Yes input baseline)
    (candidateExact : Exact Yes input candidate) :
    Exact Yes input (chooseBetter baseline candidate) := by
  unfold chooseBetter
  split
  case isTrue h => exact candidateExact
  case isFalse h => exact baselineExact

end A153_SafeGlobalChoice

/-! ## 154 - An adaptive model may embed every ordered model -/
namespace A154_OrderedEmbedding

structure Embedding (Ordered Adaptive : Type) where
  embed : Ordered -> Adaptive
  orderedCost : Ordered -> Nat
  adaptiveCost : Adaptive -> Nat
  preservesCost : forall ordered,
    adaptiveCost (embed ordered) = orderedCost ordered

end A154_OrderedEmbedding

/-! ## 155 - The optimal adaptive candidate cannot be worse than an ordered baseline -/
namespace A155_AdaptiveBaseline

open A154_OrderedEmbedding

variable {Ordered Adaptive : Type}

theorem adaptive_best_le_ordered
    (embedding : Embedding Ordered Adaptive)
    (best : Adaptive)
    (optimal : forall candidate,
      embedding.adaptiveCost best <= embedding.adaptiveCost candidate)
    (ordered : Ordered) :
    embedding.adaptiveCost best <= embedding.orderedCost ordered := by
  rw [← embedding.preservesCost ordered]
  exact optimal (embedding.embed ordered)

end A155_AdaptiveBaseline

/-! ## 156 - A smaller local recurrence can still have a larger shared DAG -/
namespace A156_LocalGlobalMismatch

theorem concrete_mismatch :
    9 < 10 /\ 10 < 13 := by
  decide

theorem local_order_does_not_determine_global_order :
    exists localA localB globalA globalB : Nat,
      localA < localB /\ globalB < globalA := by
  exact ⟨9, 10, 13, 10, by decide, by decide⟩

end A156_LocalGlobalMismatch

/-! ## 157 - Shared-node accounting is controlled by set union -/
namespace A157_SharedUnion

variable {State : Type} [DecidableEq State]

theorem union_inter_identity (left right : Finset State) :
    (left ∪ right).card + (left ∩ right).card =
      left.card + right.card := by
  exact Finset.card_union_add_card_inter left right

end A157_SharedUnion

/-! ## 158 - Sharing never costs more than separate expansion -/
namespace A158_SharingUpperBound

open A157_SharedUnion

variable {State : Type} [DecidableEq State]

theorem union_card_le_sum (left right : Finset State) :
    (left ∪ right).card <= left.card + right.card := by
  have identity := union_inter_identity left right
  omega

theorem shared_node_cost_le_tree_cost (left right : Finset State) :
    1 + (left ∪ right).card <= 1 + left.card + right.card := by
  have h := union_card_le_sum left right
  omega

end A158_SharingUpperBound

/-! ## 159 - Nonempty overlap gives a strict sharing benefit -/
namespace A159_StrictSharing

open A157_SharedUnion

variable {State : Type} [DecidableEq State]

theorem union_card_lt_sum_of_intersection
    (left right : Finset State)
    (overlap : 0 < (left ∩ right).card) :
    (left ∪ right).card < left.card + right.card := by
  have identity := union_inter_identity left right
  omega

end A159_StrictSharing

/-! ## 160 - A chain of accepted improvements never exceeds its initial cost -/
namespace A160_ImprovementChain

inductive CostChain : Nat -> Nat -> Prop
  | done (cost : Nat) : CostChain cost cost
  | step {initial next final : Nat}
      (improves : next <= initial)
      (tail : CostChain next final) :
      CostChain initial final

theorem final_le_initial {initial final : Nat}
    (chain : CostChain initial final) :
    final <= initial := by
  induction chain with
  | done cost => exact le_rfl
  | step improves tail ih => exact le_trans ih improves

end A160_ImprovementChain

/-! ## 161 - Exactness is invariant along accepted policy moves -/
namespace A161_SearchInvariant

structure SearchState where
  cost : Nat
  exact : Prop

structure AcceptedMove (old next : SearchState) : Prop where
  costImproves : next.cost <= old.cost
  exactPreserved : next.exact <-> old.exact

theorem accepted_move_preserves_exact
    (old next : SearchState) (move : AcceptedMove old next) :
    next.exact <-> old.exact :=
  move.exactPreserved

end A161_SearchInvariant

/-! ## 162 - Folding safe choices preserves exactness -/
namespace A162_ExactPortfolio

open A151_PolicyResult A153_SafeGlobalChoice

variable {State Instance : Type} [DecidableEq State]

def choosePortfolio
    (seed : PolicyResult State) : List (PolicyResult State) -> PolicyResult State
  | [] => seed
  | candidate :: rest =>
      choosePortfolio (chooseBetter seed candidate) rest

theorem choosePortfolio_exact
    (Yes : Instance -> Prop) (input : Instance)
    (seed : PolicyResult State) (candidates : List (PolicyResult State))
    (seedExact : Exact Yes input seed)
    (allExact : forall candidate,
      List.Mem candidate candidates -> Exact Yes input candidate) :
    Exact Yes input (choosePortfolio seed candidates) := by
  induction candidates generalizing seed with
  | nil => simpa [choosePortfolio] using seedExact
  | cons candidate rest ih =>
      have candidateExact : Exact Yes input candidate :=
        allExact candidate (List.Mem.head rest)
      have chosenExact : Exact Yes input (chooseBetter seed candidate) :=
        chooseBetter_exact Yes input seed candidate seedExact candidateExact
      apply ih (seed := chooseBetter seed candidate) chosenExact
      intro later hmem
      exact allExact later (List.Mem.tail candidate hmem)

end A162_ExactPortfolio

/-! ## 163 - The portfolio result is never worse than its seed baseline -/
namespace A163_PortfolioBaseline

open A151_PolicyResult A153_SafeGlobalChoice A162_ExactPortfolio

variable {State : Type} [DecidableEq State]

theorem choosePortfolio_cost_le_seed
    (seed : PolicyResult State) (candidates : List (PolicyResult State)) :
    (choosePortfolio seed candidates).cost <= seed.cost := by
  induction candidates generalizing seed with
  | nil => simp [choosePortfolio]
  | cons candidate rest ih =>
      have first := chooseBetter_cost_le seed candidate
      have tail := ih (seed := chooseBetter seed candidate)
      exact le_trans tail first

end A163_PortfolioBaseline

/-! ## 164 - Polynomially many polynomial-cost policies remain polynomial -/
namespace A164_PolynomialPortfolio

theorem portfolio_work_bound
    (input count perPolicy countExponent policyExponent : Nat)
    (countBound : count <= input ^ countExponent)
    (policyBound : perPolicy <= input ^ policyExponent) :
    count * perPolicy <= input ^ (countExponent + policyExponent) := by
  calc
    count * perPolicy <=
        (input ^ countExponent) * (input ^ policyExponent) :=
      Nat.mul_le_mul countBound policyBound
    _ = input ^ (countExponent + policyExponent) := by
      rw [pow_add]

end A164_PolynomialPortfolio

/-! ## 165 - A uniform polynomial adaptive-policy portfolio yields class collapse -/
namespace A165_PolicyCollapseCriterion

variable {Language : Type}

theorem p_eq_np_of_uniform_policy_portfolios
    (InP InNP : Language -> Prop)
    (pSubsetNP : forall language, InP language -> InNP language)
    (HasPortfolio : Language -> Prop)
    (portfolioImpliesP : forall language,
      HasPortfolio language -> InP language)
    (uniform : forall language,
      InNP language -> HasPortfolio language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  case mp =>
    intro hP
    exact pSubsetNP language hP
  case mpr =>
    intro hNP
    exact portfolioImpliesP language (uniform language hNP)

end A165_PolicyCollapseCriterion

end ResearchTwelfth
end PIsNPOrNot
