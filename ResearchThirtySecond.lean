import ResearchThirtieth

namespace PIsNPOrNot.ResearchThirtySecond

/-! ## 451 - Exact boundary messages enumerate every reachable output -/
namespace A451_ExactBoundaryMessage

variable {Boundary Payload Output : Type}
variable [DecidableEq Output]

structure Message (feature : Boundary -> Payload -> Output) where
  rows : Boundary -> Finset Output
  exact : forall boundary output,
    output ∈ rows boundary <-> exists payload, feature boundary payload = output

end A451_ExactBoundaryMessage

/-! ## 452 - Message membership is both complete and sound -/
namespace A452_MessageMembership

open A451_ExactBoundaryMessage

variable {Boundary Payload Output : Type}
variable [DecidableEq Output]

 theorem complete
    (feature : Boundary -> Payload -> Output)
    (message : Message feature)
    (boundary : Boundary) (payload : Payload) :
    feature boundary payload ∈ message.rows boundary := by
  exact (message.exact boundary (feature boundary payload)).2 ⟨payload, rfl⟩

 theorem sound
    (feature : Boundary -> Payload -> Output)
    (message : Message feature)
    (boundary : Boundary) (output : Output)
    (member : output ∈ message.rows boundary) :
    exists payload, feature boundary payload = output :=
  (message.exact boundary output).1 member

end A452_MessageMembership

/-! ## 453 - Output maps transport exact messages -/
namespace A453_MapMessage

open A451_ExactBoundaryMessage

variable {Boundary Payload Output Projected : Type}
variable [DecidableEq Output] [DecidableEq Projected]

 def mapMessage
    (feature : Boundary -> Payload -> Output)
    (project : Output -> Projected)
    (message : Message feature) :
    Message (fun boundary payload => project (feature boundary payload)) where
  rows boundary := (message.rows boundary).image project
  exact boundary projected := by
    constructor
    · intro member
      rcases Finset.mem_image.1 member with ⟨output, outputMember, rfl⟩
      rcases (message.exact boundary output).1 outputMember with ⟨payload, valueEq⟩
      exact ⟨payload, by simp [valueEq]⟩
    · rintro ⟨payload, rfl⟩
      exact Finset.mem_image.2 ⟨feature boundary payload,
        (message.exact boundary _).2 ⟨payload, rfl⟩, rfl⟩

end A453_MapMessage

/-! ## 454 - Independent children join exactly over a shared boundary -/
namespace A454_JoinMessage

open A451_ExactBoundaryMessage

variable {Boundary LeftPayload RightPayload LeftOutput RightOutput : Type}
variable [DecidableEq LeftOutput] [DecidableEq RightOutput]

 def joinMessage
    (leftFeature : Boundary -> LeftPayload -> LeftOutput)
    (rightFeature : Boundary -> RightPayload -> RightOutput)
    (left : Message leftFeature)
    (right : Message rightFeature) :
    Message (fun boundary (payload : LeftPayload × RightPayload) =>
      (leftFeature boundary payload.1, rightFeature boundary payload.2)) where
  rows boundary := (left.rows boundary).product (right.rows boundary)
  exact boundary output := by
    constructor
    · intro member
      rcases Finset.mem_product.1 member with ⟨leftMember, rightMember⟩
      rcases (left.exact boundary output.1).1 leftMember with ⟨leftPayload, leftEq⟩
      rcases (right.exact boundary output.2).1 rightMember with ⟨rightPayload, rightEq⟩
      exact ⟨(leftPayload, rightPayload), Prod.ext leftEq rightEq⟩
    · rintro ⟨⟨leftPayload, rightPayload⟩, rfl⟩
      exact Finset.mem_product.2 ⟨
        (left.exact boundary _).2 ⟨leftPayload, rfl⟩,
        (right.exact boundary _).2 ⟨rightPayload, rfl⟩⟩

end A454_JoinMessage

/-! ## 455 - Alternative branches combine by exact union -/
namespace A455_BranchMessage

open A451_ExactBoundaryMessage

variable {Boundary LeftPayload RightPayload Output : Type}
variable [DecidableEq Output]

 def branchMessage
    (leftFeature : Boundary -> LeftPayload -> Output)
    (rightFeature : Boundary -> RightPayload -> Output)
    (left : Message leftFeature)
    (right : Message rightFeature) :
    Message (fun boundary (payload : Sum LeftPayload RightPayload) =>
      match payload with
      | Sum.inl value => leftFeature boundary value
      | Sum.inr value => rightFeature boundary value) where
  rows boundary := left.rows boundary ∪ right.rows boundary
  exact boundary output := by
    constructor
    · intro member
      rcases Finset.mem_union.1 member with leftMember | rightMember
      · rcases (left.exact boundary output).1 leftMember with ⟨payload, valueEq⟩
        exact ⟨Sum.inl payload, valueEq⟩
      · rcases (right.exact boundary output).1 rightMember with ⟨payload, valueEq⟩
        exact ⟨Sum.inr payload, valueEq⟩
    · rintro ⟨payload, valueEq⟩
      cases payload with
      | inl leftPayload =>
          exact Finset.mem_union_left _ ((left.exact boundary output).2 ⟨leftPayload, valueEq⟩)
      | inr rightPayload =>
          exact Finset.mem_union_right _ ((right.exact boundary output).2 ⟨rightPayload, valueEq⟩)

end A455_BranchMessage

/-! ## 456 - Hidden separator values are eliminated by finite union -/
namespace A456_HideSeparator

open A451_ExactBoundaryMessage

variable {Parent Hidden Payload Output : Type}
variable [Fintype Hidden] [DecidableEq Output]

 def hideSeparator
    (feature : Parent -> Hidden -> Payload -> Output)
    (child : Message (fun boundary : Parent × Hidden =>
      feature boundary.1 boundary.2)) :
    Message (fun parent (payload : Hidden × Payload) =>
      feature parent payload.1 payload.2) where
  rows parent := (Finset.univ : Finset Hidden).biUnion
    (fun hidden => child.rows (parent, hidden))
  exact parent output := by
    constructor
    · intro member
      rcases Finset.mem_biUnion.1 member with ⟨hidden, _, childMember⟩
      rcases (child.exact (parent, hidden) output).1 childMember with ⟨payload, valueEq⟩
      exact ⟨(hidden, payload), valueEq⟩
    · rintro ⟨⟨hidden, payload⟩, valueEq⟩
      exact Finset.mem_biUnion.2 ⟨hidden, Finset.mem_univ hidden,
        (child.exact (parent, hidden) output).2 ⟨payload, valueEq⟩⟩

end A456_HideSeparator

/-! ## 457 - A unit-boundary message is an exact root image table -/
namespace A457_RootImage

open A451_ExactBoundaryMessage
open ResearchThirtieth.A421_ExactImageTable

variable {Witness Output : Type}
variable [DecidableEq Output]

 def rootTable
    (feature : Witness -> Output)
    (message : Message (fun _ : Unit => feature)) :
    Table feature where
  rows := message.rows ()
  complete witness := (message.exact () _).2 ⟨witness, rfl⟩
  sound output member := (message.exact () output).1 member

end A457_RootImage

/-! ## 458 - Root acceptance is equivalent to a concrete witness -/
namespace A458_RootAcceptance

open A451_ExactBoundaryMessage

variable {Witness : Type}

 theorem true_mem_iff
    (relation : Witness -> Bool)
    (message : Message (fun _ : Unit => relation)) :
    true ∈ message.rows () <-> exists witness, relation witness = true :=
  message.exact () true

end A458_RootAcceptance

/-! ## 459 - Mapping a message cannot increase row count -/
namespace A459_MapWidth

open A451_ExactBoundaryMessage A453_MapMessage

variable {Boundary Payload Output Projected : Type}
variable [DecidableEq Output] [DecidableEq Projected]

 theorem mapped_card_le
    (feature : Boundary -> Payload -> Output)
    (project : Output -> Projected)
    (message : Message feature)
    (boundary : Boundary) :
    ((mapMessage feature project message).rows boundary).card <=
      (message.rows boundary).card := by
  exact Finset.card_image_le

end A459_MapWidth

/-! ## 460 - Independent join width multiplies exactly -/
namespace A460_JoinWidth

open A451_ExactBoundaryMessage A454_JoinMessage

variable {Boundary LeftPayload RightPayload LeftOutput RightOutput : Type}
variable [DecidableEq LeftOutput] [DecidableEq RightOutput]

 theorem joined_card
    (leftFeature : Boundary -> LeftPayload -> LeftOutput)
    (rightFeature : Boundary -> RightPayload -> RightOutput)
    (left : Message leftFeature)
    (right : Message rightFeature)
    (boundary : Boundary) :
    ((joinMessage leftFeature rightFeature left right).rows boundary).card =
      (left.rows boundary).card * (right.rows boundary).card := by
  simp [joinMessage]

end A460_JoinWidth

/-! ## 461 - Branch union width is at most the child-width sum -/
namespace A461_BranchWidth

open A451_ExactBoundaryMessage A455_BranchMessage

variable {Boundary LeftPayload RightPayload Output : Type}
variable [DecidableEq Output]

 theorem branch_card_le
    (leftFeature : Boundary -> LeftPayload -> Output)
    (rightFeature : Boundary -> RightPayload -> Output)
    (left : Message leftFeature)
    (right : Message rightFeature)
    (boundary : Boundary) :
    ((branchMessage leftFeature rightFeature left right).rows boundary).card <=
      (left.rows boundary).card + (right.rows boundary).card := by
  exact Finset.card_union_le _ _

end A461_BranchWidth

/-! ## 462 - Hiding a finite separator costs at most assignments times width -/
namespace A462_HiddenSeparatorWidth

open A451_ExactBoundaryMessage A456_HideSeparator

variable {Parent Hidden Payload Output : Type}
variable [Fintype Hidden] [DecidableEq Output]

 theorem hidden_card_le
    (feature : Parent -> Hidden -> Payload -> Output)
    (child : Message (fun boundary : Parent × Hidden =>
      feature boundary.1 boundary.2))
    (parent : Parent) (width : Nat)
    (bounded : forall hidden, (child.rows (parent, hidden)).card <= width) :
    ((hideSeparator feature child).rows parent).card <=
      Fintype.card Hidden * width := by
  classical
  calc
    ((hideSeparator feature child).rows parent).card <=
        ((Finset.univ : Finset Hidden).biUnion
          (fun hidden => child.rows (parent, hidden))).card := le_rfl
    _ <= ∑ hidden : Hidden, (child.rows (parent, hidden)).card :=
      Finset.card_biUnion_le
    _ <= ∑ _hidden : Hidden, width := by
      exact Finset.sum_le_sum (fun hidden _ => bounded hidden)
    _ = Fintype.card Hidden * width := by simp

end A462_HiddenSeparatorWidth

/-! ## 463 - Logarithmic hidden interfaces keep table width polynomial -/
namespace A463_LogarithmicHiddenInterface

 theorem hidden_interface_budget
    (hiddenAssignments width input hiddenExponent widthExponent : Nat)
    (hiddenBound : hiddenAssignments <= input ^ hiddenExponent)
    (widthBound : width <= input ^ widthExponent) :
    hiddenAssignments * width <=
      input ^ (hiddenExponent + widthExponent) := by
  calc
    hiddenAssignments * width <=
        input ^ hiddenExponent * input ^ widthExponent :=
      Nat.mul_le_mul hiddenBound widthBound
    _ = input ^ (hiddenExponent + widthExponent) := by rw [pow_add]

end A463_LogarithmicHiddenInterface

/-! ## 464 - Polynomially many bounded messages have polynomial materialization cost -/
namespace A464_MessagePlanBudget

 theorem message_plan_bound
    (messageCount width scanCost input countExp widthExp scanExp : Nat)
    (countBound : messageCount <= input ^ countExp)
    (widthBound : width <= input ^ widthExp)
    (scanBound : scanCost <= input ^ scanExp) :
    messageCount * width + scanCost <=
      input ^ countExp * input ^ widthExp + input ^ scanExp := by
  exact Nat.add_le_add (Nat.mul_le_mul countBound widthBound) scanBound

end A464_MessagePlanBudget

/-! ## 465 - Uniform polynomial exact-message plans imply the class collapse -/
namespace A465_MessagePlanCollapse

variable {Language : Type}

structure UniformMessagePlans
    (PClass NPClass : Set Language) where
  hasPlan : Language -> Prop
  allNPHavePlan : forall language,
    language ∈ NPClass -> hasPlan language
  planGivesP : forall language,
    hasPlan language -> language ∈ PClass

 theorem p_eq_np_of_uniform_message_plans
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (plans : UniformMessagePlans PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact plans.planGivesP language (plans.allNPHavePlan language inNP)

end A465_MessagePlanCollapse

end PIsNPOrNot.ResearchThirtySecond
