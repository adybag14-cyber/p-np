import ResearchFiftyFifth

namespace PIsNPOrNot.ResearchFiftySixth

/-! ## 811 - A lawful finite group action supplies identity and composition -/
namespace A811_FiniteGroupAction

structure Action (G Residual : Type) [Group G] [Fintype G] where
  act : G -> Residual -> Residual
  identity : forall value, act 1 value = value
  compose : forall left right value,
    act (left * right) value = act left (act right value)

end A811_FiniteGroupAction

/-! ## 812 - Inverse edge labels recover the original residual value -/
namespace A812_GroupInverseRecovery

open A811_FiniteGroupAction

variable {G Residual : Type} [Group G] [Fintype G]

theorem inverse_recovers (action : Action G Residual)
    (label : G) (value : Residual) :
    action.act label⁻¹ (action.act label value) = value := by
  rw [← action.compose]
  simp [action.identity]

end A812_GroupInverseRecovery

/-! ## 813 - Two nested group labels normalize to one product label -/
namespace A813_GroupLabelNormalization

open A811_FiniteGroupAction

variable {G Residual : Type} [Group G] [Fintype G]

theorem normalize (action : Action G Residual)
    (left right : G) (value : Residual) :
    action.act left (action.act right value) =
      action.act (left * right) value := by
  symm
  exact action.compose left right value

end A813_GroupLabelNormalization

/-! ## 814 - Belonging to the same action orbit is reflexive -/
namespace A814_OrbitReflexive

open A811_FiniteGroupAction

variable {G Residual : Type} [Group G] [Fintype G]

def SameOrbit (action : Action G Residual) (left right : Residual) : Prop :=
  exists label, right = action.act label left

theorem refl (action : Action G Residual) (value : Residual) :
    SameOrbit action value value := by
  exact ⟨1, (action.identity value).symm⟩

end A814_OrbitReflexive

/-! ## 815 - Action-orbit membership is symmetric -/
namespace A815_OrbitSymmetric

open A811_FiniteGroupAction
open A814_OrbitReflexive

variable {G Residual : Type} [Group G] [Fintype G]

theorem symm (action : Action G Residual) {left right : Residual}
    (same : SameOrbit action left right) : SameOrbit action right left := by
  rcases same with ⟨label, rfl⟩
  exact ⟨label⁻¹, (A812_GroupInverseRecovery.inverse_recovers action label left).symm⟩

end A815_OrbitSymmetric

/-! ## 816 - Action-orbit membership is transitive -/
namespace A816_OrbitTransitive

open A811_FiniteGroupAction
open A814_OrbitReflexive

variable {G Residual : Type} [Group G] [Fintype G]

theorem trans (action : Action G Residual) {left middle right : Residual}
    (first : SameOrbit action left middle)
    (second : SameOrbit action middle right) :
    SameOrbit action left right := by
  rcases first with ⟨firstLabel, rfl⟩
  rcases second with ⟨secondLabel, rfl⟩
  exact ⟨secondLabel * firstLabel, (action.compose secondLabel firstLabel left).symm⟩

end A816_OrbitTransitive

/-! ## 817 - A finite group orbit has at most the group cardinality -/
namespace A817_GroupOrbitCardinality

open A811_FiniteGroupAction

variable {G Residual : Type} [Group G] [Fintype G] [DecidableEq Residual]

noncomputable def orbit (action : Action G Residual) (base : Residual) :
    Finset Residual := by
  classical
  exact (Finset.univ : Finset G).image (fun label => action.act label base)

theorem orbit_card_le (action : Action G Residual) (base : Residual) :
    (orbit action base).card <= Fintype.card G := by
  exact Finset.card_image_le

end A817_GroupOrbitCardinality

/-! ## 818 - Product group labels act independently on product residuals -/
namespace A818_ProductGroupAction

open A811_FiniteGroupAction

variable {G H X Y : Type}
variable [Group G] [Fintype G]
variable [Group H] [Fintype H]

def productAction
    (leftAction : Action G X)
    (rightAction : Action H Y) :
    Action (G × H) (X × Y) where
  act := fun label value =>
    (leftAction.act label.1 value.1, rightAction.act label.2 value.2)
  identity := by
    intro value
    apply Prod.ext
    · exact leftAction.identity value.1
    · exact rightAction.identity value.2
  compose := by
    intro left right value
    apply Prod.ext
    · exact leftAction.compose left.1 right.1 value.1
    · exact rightAction.compose left.2 right.2 value.2

end A818_ProductGroupAction

/-! ## 819 - Product label cardinality multiplies independent action capacity -/
namespace A819_ProductLabelCardinality

variable {G H : Type}
variable [Fintype G] [Fintype H]

theorem product_card :
    Fintype.card (G × H) = Fintype.card G * Fintype.card H :=
  Fintype.card_prod _ _

end A819_ProductLabelCardinality

/-! ## 820 - A finite bit encoding bounds the number of available edge labels -/
namespace A820_LabelBitCapacity

structure BitEncoding (Label : Type) [Fintype Label] (bits : Nat) where
  encode : Label -> (Fin bits -> Bool)
  injective : Function.Injective encode

variable {Label : Type} [Fintype Label]

theorem label_card_le_pow_two {bits : Nat} (encoding : BitEncoding Label bits) :
    Fintype.card Label <= 2 ^ bits := by
  calc
    Fintype.card Label <= Fintype.card (Fin bits -> Bool) :=
      Fintype.card_le_of_injective encoding.encode encoding.injective
    _ = 2 ^ bits :=
      ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card bits

end A820_LabelBitCapacity

/-! ## 821 - Semantic capacity is bounded by bases times encoded label space -/
namespace A821_EncodedActionCapacity

open ResearchFiftySecond.A752_ActionEncoding
open A820_LabelBitCapacity

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem state_card_le_base_mul_pow_two {bits : Nat}
    (encoding : Encoding State Base Label Residual)
    (meaningInjective : Function.Injective encoding.meaning)
    (labelEncoding : BitEncoding Label bits) :
    Fintype.card State <= Fintype.card Base * 2 ^ bits := by
  apply le_trans
    (ResearchFiftySecond.A755_ActionCardinalityBound.state_card_le_base_mul_label
      encoding meaningInjective)
  exact Nat.mul_le_mul_left (Fintype.card Base)
    (A820_LabelBitCapacity.label_card_le_pow_two labelEncoding)

end A821_EncodedActionCapacity

/-! ## 822 - Physical storage includes nodes, edges, and label bits -/
namespace A822_EdgeLabelStorage

structure Storage where
  physicalNodes : Nat
  physicalEdges : Nat
  labelBits : Nat
  nodeWords : Nat
  arithmeticWork : Nat

def labelStorage (storage : Storage) : Nat :=
  storage.physicalEdges * storage.labelBits

def totalStorage (storage : Storage) : Nat :=
  storage.nodeWords + labelStorage storage

def totalWork (storage : Storage) : Nat :=
  totalStorage storage + storage.arithmeticWork

end A822_EdgeLabelStorage

/-! ## 823 - Linear node count does not by itself bound edge-label work -/
namespace A823_LabelCostObstruction

open A822_EdgeLabelStorage

theorem one_node_can_have_large_label_cost :
    exists storage : Storage,
      storage.physicalNodes = 1 ∧
      labelStorage storage > storage.physicalNodes := by
  refine ⟨⟨1, 2, 10, 1, 0⟩, rfl, ?_⟩
  decide

end A823_LabelCostObstruction

/-! ## 824 - Too few encoded labels obstruct an injective exact action representation -/
namespace A824_InsufficientLabelCapacity

open ResearchFiftySecond.A752_ActionEncoding
open A820_LabelBitCapacity

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem no_encoding_when_capacity_too_small {bits : Nat}
    (encoding : Encoding State Base Label Residual)
    (meaningInjective : Function.Injective encoding.meaning)
    (labelEncoding : BitEncoding Label bits)
    (tooSmall : Fintype.card Base * 2 ^ bits < Fintype.card State) : False := by
  exact Nat.not_le_of_lt tooSmall
    (A821_EncodedActionCapacity.state_card_le_base_mul_pow_two
      encoding meaningInjective labelEncoding)

end A824_InsufficientLabelCapacity

/-! ## 825 - Uniform polynomial encoded-action compilers would imply P = NP -/
namespace A825_EncodedActionCollapse

variable {Language : Type}

structure UniformEncodedActionCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_encoded_action_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformEncodedActionCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A825_EncodedActionCollapse

end PIsNPOrNot.ResearchFiftySixth
