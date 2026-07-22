import ResearchFourteenth

namespace PIsNPOrNot
namespace ResearchFifteenth

/-! ## 196 - Residual transition systems and global policies -/
namespace A196_TransitionSystem

structure System (State Choice : Type) [DecidableEq State] where
  children : State -> Choice -> Finset State

abbrev Policy (State Choice : Type) := State -> Choice

end A196_TransitionSystem

/-! ## 197 - Policy-closed reachable state sets -/
namespace A197_PolicyClosed

open A196_TransitionSystem

variable {State Choice : Type} [DecidableEq State]

def Closed
    (system : System State Choice)
    (policy : Policy State Choice)
    (states : Finset State) : Prop :=
  forall state, state ∈ states ->
    system.children state (policy state) ⊆ states

def Rooted (root : State) (states : Finset State) : Prop :=
  root ∈ states

end A197_PolicyClosed

/-! ## 198 - Least reachable closure certificates -/
namespace A198_ClosureCertificate

open A196_TransitionSystem A197_PolicyClosed

variable {State Choice : Type} [DecidableEq State]

structure Certificate
    (system : System State Choice)
    (policy : Policy State Choice)
    (root : State) where
  reachable : Finset State
  root_mem : Rooted root reachable
  closed : Closed system policy reachable
  minimal : forall candidate : Finset State,
    Rooted root candidate ->
    Closed system policy candidate ->
    reachable ⊆ candidate

end A198_ClosureCertificate

/-! ## 199 - Least reachable closures are unique -/
namespace A199_ClosureUniqueness

open A196_TransitionSystem A198_ClosureCertificate

variable {State Choice : Type} [DecidableEq State]

theorem reachable_unique
    (system : System State Choice)
    (policy : Policy State Choice)
    (root : State)
    (left right : Certificate system policy root) :
    left.reachable = right.reachable := by
  apply Finset.Subset.antisymm
  · exact left.minimal right.reachable right.root_mem right.closed
  · exact right.minimal left.reachable left.root_mem left.closed

end A199_ClosureUniqueness

/-! ## 200 - Least closure has minimum cardinality among closed rooted sets -/
namespace A200_ClosureCardinalityMinimality

open A196_TransitionSystem A197_PolicyClosed A198_ClosureCertificate

variable {State Choice : Type} [DecidableEq State]

theorem reachable_card_le
    (system : System State Choice)
    (policy : Policy State Choice)
    (root : State)
    (certificate : Certificate system policy root)
    (candidate : Finset State)
    (rooted : Rooted root candidate)
    (closed : Closed system policy candidate) :
    certificate.reachable.card <= candidate.card := by
  exact Finset.card_le_card
    (certificate.minimal candidate rooted closed)

end A200_ClosureCardinalityMinimality

/-! ## 201 - Policies that agree on a state set preserve closure -/
namespace A201_PolicyAgreement

open A196_TransitionSystem A197_PolicyClosed

variable {State Choice : Type} [DecidableEq State]

def AgreeOn
    (states : Finset State)
    (left right : Policy State Choice) : Prop :=
  forall state, state ∈ states -> left state = right state

theorem closed_transfer
    (system : System State Choice)
    (states : Finset State)
    (left right : Policy State Choice)
    (closed : Closed system left states)
    (agree : AgreeOn states left right) :
    Closed system right states := by
  intro state hState
  rw [← agree state hState]
  exact closed state hState

end A201_PolicyAgreement

/-! ## 202 - Merging policies by a finite domain -/
namespace A202_MergePolicy

open A196_TransitionSystem

variable {State Choice : Type} [DecidableEq State]

def mergePolicy
    (leftDomain : Finset State)
    (left right : Policy State Choice) : Policy State Choice :=
  fun state => if state ∈ leftDomain then left state else right state

end A202_MergePolicy

/-! ## 203 - The merged policy agrees with the left policy on its domain -/
namespace A203_MergeLeftAgreement

open A196_TransitionSystem A201_PolicyAgreement A202_MergePolicy

variable {State Choice : Type} [DecidableEq State]

theorem merge_agrees_left
    (leftDomain : Finset State)
    (left right : Policy State Choice) :
    AgreeOn leftDomain (mergePolicy leftDomain left right) left := by
  intro state hState
  simp [mergePolicy, hState]

end A203_MergeLeftAgreement

/-! ## 204 - Compatibility means equal choices on shared states -/
namespace A204_PolicyCompatibility

open A196_TransitionSystem

variable {State Choice : Type} [DecidableEq State]

def CompatibleOn
    (states : Finset State)
    (left right : Policy State Choice) : Prop :=
  forall state, state ∈ states -> left state = right state

end A204_PolicyCompatibility

/-! ## 205 - A compatible merge agrees with the right policy on the right domain -/
namespace A205_MergeRightAgreement

open A196_TransitionSystem A201_PolicyAgreement
open A202_MergePolicy A204_PolicyCompatibility

variable {State Choice : Type} [DecidableEq State]

theorem merge_agrees_right
    (leftDomain rightDomain : Finset State)
    (left right : Policy State Choice)
    (compatible : CompatibleOn (leftDomain ∩ rightDomain) left right) :
    AgreeOn rightDomain (mergePolicy leftDomain left right) right := by
  intro state hRight
  by_cases hLeft : state ∈ leftDomain
  · have hInter : state ∈ leftDomain ∩ rightDomain := by
      simpa only [Finset.mem_inter] using And.intro hLeft hRight
    simp [mergePolicy, hLeft, compatible state hInter]
  · simp [mergePolicy, hLeft]

end A205_MergeRightAgreement

/-! ## 206 - Compatible closed child policies compose on their union -/
namespace A206_CoherentUnionClosure

open A196_TransitionSystem A197_PolicyClosed A201_PolicyAgreement
open A202_MergePolicy A203_MergeLeftAgreement A204_PolicyCompatibility
open A205_MergeRightAgreement

variable {State Choice : Type} [DecidableEq State]

theorem union_closed
    (system : System State Choice)
    (leftStates rightStates : Finset State)
    (leftPolicy rightPolicy : Policy State Choice)
    (leftClosed : Closed system leftPolicy leftStates)
    (rightClosed : Closed system rightPolicy rightStates)
    (compatible : CompatibleOn (leftStates ∩ rightStates)
      leftPolicy rightPolicy) :
    Closed system
      (mergePolicy leftStates leftPolicy rightPolicy)
      (leftStates ∪ rightStates) := by
  intro state hState
  have hUnion : state ∈ leftStates ∨ state ∈ rightStates := by
    simpa only [Finset.mem_union] using hState
  rcases hUnion with hLeft | hRight
  · have hChoice := merge_agrees_left leftStates leftPolicy rightPolicy state hLeft
    rw [hChoice]
    intro child hChild
    have childLeft := leftClosed state hLeft hChild
    have result : child ∈ leftStates ∨ child ∈ rightStates := Or.inl childLeft
    simpa only [Finset.mem_union] using result
  · have hChoice := merge_agrees_right leftStates rightStates
      leftPolicy rightPolicy compatible state hRight
    rw [hChoice]
    intro child hChild
    have childRight := rightClosed state hRight hChild
    have result : child ∈ leftStates ∨ child ∈ rightStates := Or.inr childRight
    simpa only [Finset.mem_union] using result

end A206_CoherentUnionClosure

/-! ## 207 - Either rooted child makes the coherent union rooted -/
namespace A207_CoherentUnionRoot

open A197_PolicyClosed

variable {State : Type} [DecidableEq State]

theorem union_rooted_left
    (root : State) (left right : Finset State)
    (rooted : Rooted root left) :
    Rooted root (left ∪ right) := by
  have result : root ∈ left ∨ root ∈ right := Or.inl rooted
  simpa only [Rooted, Finset.mem_union] using result

theorem union_rooted_right
    (root : State) (left right : Finset State)
    (rooted : Rooted root right) :
    Rooted root (left ∪ right) := by
  have result : root ∈ left ∨ root ∈ right := Or.inr rooted
  simpa only [Rooted, Finset.mem_union] using result

end A207_CoherentUnionRoot

/-! ## 208 - A proof-carrying coherent policy composition -/
namespace A208_CoherentComposition

open A196_TransitionSystem A197_PolicyClosed A202_MergePolicy
open A204_PolicyCompatibility A206_CoherentUnionClosure

variable {State Choice : Type} [DecidableEq State]

structure Composition (system : System State Choice) where
  leftStates : Finset State
  rightStates : Finset State
  leftPolicy : Policy State Choice
  rightPolicy : Policy State Choice
  leftClosed : Closed system leftPolicy leftStates
  rightClosed : Closed system rightPolicy rightStates
  compatible : CompatibleOn (leftStates ∩ rightStates)
    leftPolicy rightPolicy

def Composition.policy
    {system : System State Choice}
    (composition : Composition system) : Policy State Choice :=
  mergePolicy composition.leftStates
    composition.leftPolicy composition.rightPolicy

def Composition.states
    {system : System State Choice}
    (composition : Composition system) : Finset State :=
  composition.leftStates ∪ composition.rightStates

theorem Composition.closed
    {system : System State Choice}
    (composition : Composition system) :
    Closed system composition.policy composition.states := by
  exact union_closed system
    composition.leftStates composition.rightStates
    composition.leftPolicy composition.rightPolicy
    composition.leftClosed composition.rightClosed composition.compatible

end A208_CoherentComposition

/-! ## 209 - Coherent composition receives the exact overlap discount -/
namespace A209_CoherentCompositionCost

open A208_CoherentComposition
open PIsNPOrNot.ResearchThirteenth.A166_OverlapAccounting

variable {State Choice : Type} [DecidableEq State]

theorem composition_cost_identity
    {system : A196_TransitionSystem.System State Choice}
    (composition : Composition system) :
    composition.states.card +
        overlapCredit composition.leftStates composition.rightStates =
      composition.leftStates.card + composition.rightStates.card := by
  exact union_plus_overlap composition.leftStates composition.rightStates

end A209_CoherentCompositionCost

/-! ## 210 - Uniform polynomial coherent closures imply P = NP -/
namespace A210_CoherentPolicyCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_coherent_policies
    (InP InNP : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (hasCoherentPolicy : Language -> Prop)
    (policyImpliesP : forall language,
      hasCoherentPolicy language -> InP language)
    (uniform : forall language,
      InNP language -> hasCoherentPolicy language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact policyImpliesP language (uniform language hNP)

end A210_CoherentPolicyCollapse

end ResearchFifteenth
end PIsNPOrNot
