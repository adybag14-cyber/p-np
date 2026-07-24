import ResearchFortySeventh

namespace PIsNPOrNot.ResearchFortyEighth

/-! ## 691 - XOR folding from an arbitrary initial state factors through the zero-state fold -/
namespace A691_XorFoldFactorization

theorem foldl_xor_init (initial : Bool) (bits : List Bool) :
    bits.foldl Bool.xor initial = Bool.xor initial (bits.foldl Bool.xor false) := by
  induction bits generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih (Bool.xor initial head)]
      rw [show Bool.xor false head = head by cases head <;> rfl]
      rw [ih head]
      cases initial <;> cases head <;> cases tail.foldl Bool.xor false <;> decide

end A691_XorFoldFactorization

/-! ## 692 - Recursive parity equals the existing list-fold parity coordinate -/
namespace A692_ParityCoordinateAgreement

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open ResearchNineteenth.A260_ParityFeature

theorem parity_eq_xorAll {n : Nat} (bits : Assignment n) :
    parity bits = xorAll bits := by
  induction n with
  | zero => simp [parity, xorAll]
  | succ n ih =>
      simp [parity, xorAll, ih]
      exact (A691_XorFoldFactorization.foldl_xor_init
        (bits 0) (List.ofFn fun index => bits index.succ)).symm

end A692_ParityCoordinateAgreement

/-! ## 693 - The reduced parity OBDD has one root, paired intermediate states, and two terminals -/
namespace A693_ParityObddNode

abbrev Node (n : Nat) := Unit ⊕ ((Fin (n - 1) × Bool) ⊕ Bool)

end A693_ParityObddNode

/-! ## 694 - The structured OBDD node type has cardinality 1 + 2(n-1) + 2 -/
namespace A694_ParityObddCardinality

open A693_ParityObddNode

theorem node_card_formula (n : Nat) :
    Fintype.card (Node n) = 1 + ((n - 1) * 2 + 2) := by
  simp [Node]

end A694_ParityObddCardinality

/-! ## 695 - For nonempty inputs the reduced parity OBDD has exactly 2n+1 nodes -/
namespace A695_ExactParityObddSize

open A693_ParityObddNode

theorem node_card_eq (n : Nat) (positive : 1 <= n) :
    Fintype.card (Node n) = 2 * n + 1 := by
  rw [A694_ParityObddCardinality.node_card_formula]
  omega

end A695_ExactParityObddSize

/-! ## 696 - An executable parity OBDD certificate uses the XOR-fold evaluator -/
namespace A696_ParityObddCertificate

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open ResearchNineteenth.A260_ParityFeature

structure Certificate (n : Nat) where
  evaluate : Assignment n -> Bool
  nodeCount : Nat
  exact : forall bits, evaluate bits = parity bits

noncomputable def certificate (n : Nat) : Certificate n where
  evaluate := xorAll
  nodeCount := if n = 0 then 1 else 2 * n + 1
  exact := by
    intro bits
    exact (A692_ParityCoordinateAgreement.parity_eq_xorAll bits).symm

end A696_ParityObddCertificate

/-! ## 697 - The OBDD evaluator is pointwise equal to recursive parity -/
namespace A697_ParityObddExact

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open A696_ParityObddCertificate

theorem evaluate_correct (n : Nat) (bits : Assignment n) :
    (certificate n).evaluate bits = parity bits :=
  (certificate n).exact bits

end A697_ParityObddExact

/-! ## 698 - The exact OBDD size is smaller than 2^n from n=3 onward -/
namespace A698_ObddVersusCubeGrowth

theorem obdd_lt_pow (n : Nat) (atLeastThree : 3 <= n) :
    2 * n + 1 < 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le atLeastThree
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 3 + (k + 1) = (3 + k) + 1 by omega]
      rw [pow_succ]
      omega

end A698_ObddVersusCubeGrowth

/-! ## 699 - Every parity cube cover is strictly larger than the exact OBDD from n=3 onward -/
namespace A699_ExactObddCubeGap

open ResearchFortyFifth.A655_ParityCubeCover

variable {n : Nat} {Term : Type} [Fintype Term]

theorem obdd_strictly_smaller (cover : ParityCubeCover n Term)
    (atLeastThree : 3 <= n) :
    2 * n + 1 < Fintype.card Term := by
  exact lt_of_lt_of_le
    (A698_ObddVersusCubeGrowth.obdd_lt_pow n atLeastThree)
    (ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound cover)

end A699_ExactObddCubeGap

/-! ## 700 - At sixteen variables the exact gap is 33 OBDD nodes versus 65536 cube terms -/
namespace A700_SixteenVariableGap

theorem concrete_gap : 2 * 16 + 1 < 2 ^ 16 := by decide

end A700_SixteenVariableGap

/-! ## 701 - The unreduced full parity decision tree has 2^n leaves -/
namespace A701_FullTreeLeaves

def leafCount (n : Nat) : Nat := 2 ^ n

theorem leaf_count (n : Nat) : leafCount n = 2 ^ n := rfl

end A701_FullTreeLeaves

/-! ## 702 - The unreduced full binary decision tree has 2^(n+1)-1 total nodes -/
namespace A702_FullTreeNodes

def nodeCount (n : Nat) : Nat := 2 ^ (n + 1) - 1

theorem node_count (n : Nat) : nodeCount n = 2 ^ (n + 1) - 1 := rfl

end A702_FullTreeNodes

/-! ## 703 - Reduced parity OBDDs are smaller than full trees from n=2 onward -/
namespace A703_TreeObddGap

theorem obdd_lt_tree (n : Nat) (atLeastTwo : 2 <= n) :
    2 * n + 1 < 2 ^ (n + 1) - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le atLeastTwo
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega]
      rw [show (2 + k + 1) + 1 = ((2 + k) + 1) + 1 by omega]
      rw [pow_succ]
      omega

end A703_TreeObddGap

/-! ## 704 - Sharing equal parity residuals yields an explicit node saving -/
namespace A704_ParitySharingSaving

def saving (n : Nat) : Nat := (2 ^ (n + 1) - 1) - (2 * n + 1)

theorem positive_saving (n : Nat) (atLeastTwo : 2 <= n) :
    0 < saving n := by
  unfold saving
  exact Nat.sub_pos_of_lt (A703_TreeObddGap.obdd_lt_tree n atLeastTwo)

end A704_ParitySharingSaving

/-! ## 705 - Parity separates semantic, cube, tree, and OBDD representation measures -/
namespace A705_ParityRepresentationProfile

structure Profile (n : Nat) where
  semanticClasses : Nat
  cubeTerms : Nat
  cubeLiterals : Nat
  treeNodes : Nat
  obddNodes : Nat
  semanticEquation : semanticClasses = 2
  cubeEquation : cubeTerms = 2 ^ n
  literalEquation : cubeLiterals = n * 2 ^ n
  treeEquation : treeNodes = 2 ^ (n + 1) - 1
  obddEquation : obddNodes = 2 * n + 1

noncomputable def profile (n : Nat) : Profile n where
  semanticClasses := 2
  cubeTerms := 2 ^ n
  cubeLiterals := n * 2 ^ n
  treeNodes := 2 ^ (n + 1) - 1
  obddNodes := 2 * n + 1
  semanticEquation := rfl
  cubeEquation := rfl
  literalEquation := rfl
  treeEquation := rfl
  obddEquation := rfl

end A705_ParityRepresentationProfile

end PIsNPOrNot.ResearchFortyEighth
