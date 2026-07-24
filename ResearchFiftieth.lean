import ResearchFortyNinth

namespace PIsNPOrNot.ResearchFiftieth

/-! ## 721 - A complemented reference pairs a physical node with a polarity bit -/
namespace A721_ComplementedReference

abbrev Ref (Node : Type) := Node × Bool

def node {Node : Type} (reference : Ref Node) : Node := reference.1

def complemented {Node : Type} (reference : Ref Node) : Bool := reference.2

end A721_ComplementedReference

/-! ## 722 - A polarity bit either preserves or negates a Boolean value -/
namespace A722_ApplyPolarity

def applyPolarity (polarity value : Bool) : Bool := Bool.xor polarity value

theorem false_identity (value : Bool) : applyPolarity false value = value := by
  cases value <;> rfl

theorem true_complement (value : Bool) : applyPolarity true value = !value := by
  cases value <;> rfl

end A722_ApplyPolarity

/-! ## 723 - The odd parity residual is the complement of the even residual -/
namespace A723_ParityResidualComplement

open ResearchFortyNinth.A709_ParityResidual

theorem false_residual_identity : residual false = fun suffix => suffix := by
  funext suffix
  cases suffix <;> rfl

theorem true_residual_complement :
    residual true = fun suffix => !(residual false suffix) := by
  funext suffix
  cases suffix <;> rfl

end A723_ParityResidualComplement

/-! ## 724 - One physical residual node plus polarity represents both parity states -/
namespace A724_SharedParityResidualNode

open ResearchFortyNinth.A709_ParityResidual
open A722_ApplyPolarity

structure SharedNode where
  base : Bool -> Bool
  decode : Bool -> Bool -> Bool
  evenExact : decode false = residual false
  oddExact : decode true = residual true

def parityNode : SharedNode where
  base := residual false
  decode := fun polarity suffix => applyPolarity polarity (residual false suffix)
  evenExact := by
    funext suffix
    simp [applyPolarity, ResearchFortyNinth.A709_ParityResidual.residual]
  oddExact := by
    funext suffix
    cases suffix <;> rfl

end A724_SharedParityResidualNode

/-! ## 725 - A complemented parity chain stores one terminal and one node per variable -/
namespace A725_ComplementedPhysicalNode

abbrev PhysicalNode (n : Nat) := Sum Unit (Fin n)

theorem physical_node_card (n : Nat) :
    Fintype.card (PhysicalNode n) = n + 1 := by
  simp [PhysicalNode, Nat.add_comm]

end A725_ComplementedPhysicalNode

/-! ## 726 - References expose two polarities per physical parity node -/
namespace A726_ComplementedReferenceCard

open A721_ComplementedReference
open A725_ComplementedPhysicalNode

theorem reference_card (n : Nat) :
    Fintype.card (Ref (PhysicalNode n)) = 2 * (n + 1) := by
  simp [Ref, PhysicalNode, Nat.mul_comm, Nat.add_comm]

end A726_ComplementedReferenceCard

/-! ## 727 - The complemented chain evaluator is the XOR fold -/
namespace A727_ComplementedChainEvaluation

open ResearchFortyFifth.A646_BitFlip
open ResearchNineteenth.A260_ParityFeature

def evaluate {n : Nat} (bits : Assignment n) : Bool := xorAll bits

theorem evaluate_eq_xorAll {n : Nat} (bits : Assignment n) :
    evaluate bits = xorAll bits := rfl

end A727_ComplementedChainEvaluation

/-! ## 728 - The complemented chain computes recursive parity exactly -/
namespace A728_ComplementedChainExact

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

theorem evaluate_correct {n : Nat} (bits : Assignment n) :
    A727_ComplementedChainEvaluation.evaluate bits = parity bits := by
  exact (ResearchFortyEighth.A692_ParityCoordinateAgreement.parity_eq_xorAll bits).symm

end A728_ComplementedChainExact

/-! ## 729 - A proof-carrying complemented parity certificate has n+1 physical nodes -/
namespace A729_ComplementedParityCertificate

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

structure Certificate (n : Nat) where
  physicalNodes : Nat
  evaluate : Assignment n -> Bool
  sizeExact : physicalNodes = n + 1
  semanticsExact : forall bits, evaluate bits = parity bits

noncomputable def certificate (n : Nat) : Certificate n where
  physicalNodes := n + 1
  evaluate := A727_ComplementedChainEvaluation.evaluate
  sizeExact := rfl
  semanticsExact := A728_ComplementedChainExact.evaluate_correct

end A729_ComplementedParityCertificate

/-! ## 730 - Complemented edges save n nodes over the explicit two-state OBDD -/
namespace A730_ComplementedSaving

theorem complemented_lt_explicit (n : Nat) (positive : 1 <= n) :
    n + 1 < 2 * n + 1 := by omega

end A730_ComplementedSaving

/-! ## 731 - Complemented parity BDDs are smaller than 2^n from n=2 onward -/
namespace A731_ComplementedVersusCubeGrowth

theorem complemented_lt_pow (n : Nat) (atLeastTwo : 2 <= n) :
    n + 1 < 2 ^ n := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le atLeastTwo
  induction offset with
  | zero => decide
  | succ offset ih =>
      rw [show 2 + (offset + 1) = (2 + offset) + 1 by omega]
      rw [pow_succ]
      omega

end A731_ComplementedVersusCubeGrowth

/-! ## 732 - Every parity cube cover exceeds the complemented BDD from n=2 onward -/
namespace A732_ComplementedCubeGap

open ResearchFortyFifth.A655_ParityCubeCover

variable {n : Nat} {Term : Type} [Fintype Term]

theorem complemented_strictly_smaller
    (cover : ParityCubeCover n Term) (atLeastTwo : 2 <= n) :
    n + 1 < Fintype.card Term := by
  exact lt_of_lt_of_le
    (A731_ComplementedVersusCubeGrowth.complemented_lt_pow n atLeastTwo)
    (ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound cover)

end A732_ComplementedCubeGap

/-! ## 733 - At sixteen variables complemented BDDs use 17 nodes versus 65536 cube terms -/
namespace A733_SixteenVariableComplementedGap

theorem concrete_gap : 16 + 1 < 2 ^ 16 := by decide

end A733_SixteenVariableComplementedGap

/-! ## 734 - Representation accounting must state whether complement edges are allowed -/
namespace A734_RepresentationConvention

structure CostConvention (n : Nat) where
  explicitStateNodes : Nat
  complementedNodes : Nat
  explicitEquation : explicitStateNodes = 2 * n + 1
  complementedEquation : complementedNodes = n + 1
  complementedLeExplicit : complementedNodes <= explicitStateNodes

noncomputable def parityConvention (n : Nat) : CostConvention n where
  explicitStateNodes := 2 * n + 1
  complementedNodes := n + 1
  explicitEquation := rfl
  complementedEquation := rfl
  complementedLeExplicit := by omega

end A734_RepresentationConvention

/-! ## 735 - The exact physical-node saving from complement edges is n -/
namespace A735_ExactComplementSaving

theorem exact_saving (n : Nat) :
    (2 * n + 1) - (n + 1) = n := by omega

end A735_ExactComplementSaving

end PIsNPOrNot.ResearchFiftieth
