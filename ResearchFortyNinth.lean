import ResearchFortyEighth

namespace PIsNPOrNot.ResearchFortyNinth

/-! ## 706 - The all-false assignment has even parity -/
namespace A706_AllFalseParity

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

theorem parity_all_false (n : Nat) :
    parity (fun _index : Fin n => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parity, ih]

end A706_AllFalseParity

/-! ## 707 - A first-bit-only assignment has odd parity -/
namespace A707_FirstTrueParity

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

def firstTrue (n : Nat) : Assignment (n + 1) :=
  Fin.cases true (fun _ => false)

theorem parity_first_true (n : Nat) : parity (firstTrue n) = true := by
  simp [firstTrue, parity, A706_AllFalseParity.parity_all_false]

end A707_FirstTrueParity

/-! ## 708 - Nonempty parity has exactly two semantic classes -/
namespace A708_ExactParityClasses

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

theorem parity_image_eq_two (n : Nat) :
    ((Finset.univ : Finset (Assignment (n + 1))).image parity).card = 2 := by
  classical
  have falseMember : false ∈
      (Finset.univ : Finset (Assignment (n + 1))).image parity := by
    apply Finset.mem_image.2
    refine ⟨(fun _index : Fin (n + 1) => false), Finset.mem_univ _, ?_⟩
    exact A706_AllFalseParity.parity_all_false (n + 1)
  have trueMember : true ∈
      (Finset.univ : Finset (Assignment (n + 1))).image parity := by
    apply Finset.mem_image.2
    refine ⟨A707_FirstTrueParity.firstTrue n, Finset.mem_univ _, ?_⟩
    exact A707_FirstTrueParity.parity_first_true n
  have universeSubset : (Finset.univ : Finset Bool) ⊆
      (Finset.univ : Finset (Assignment (n + 1))).image parity := by
    intro value _member
    cases value
    · exact falseMember
    · exact trueMember
  have lower : 2 <=
      ((Finset.univ : Finset (Assignment (n + 1))).image parity).card := by
    simpa using Finset.card_le_card universeSubset
  have upper := ResearchFortySixth.A663_ParitySemanticClasses.parity_image_le_two (n + 1)
  exact Nat.le_antisymm upper lower

end A708_ExactParityClasses

/-! ## 709 - A parity prefix state determines its residual action on suffix parity -/
namespace A709_ParityResidual

def residual (prefixParity suffixParity : Bool) : Bool :=
  Bool.xor prefixParity suffixParity

theorem equal_state_equal_residual {left right : Bool} (equal : left = right) :
    residual left = residual right := by
  subst right
  rfl

end A709_ParityResidual

/-! ## 710 - The two parity residual functions are distinct -/
namespace A710_DistinctParityResiduals

open A709_ParityResidual

theorem residuals_distinct : Not (residual false = residual true) := by
  intro equal
  have point : false = true := by
    simpa [A709_ParityResidual.residual] using congrFun equal false
  cases point

end A710_DistinctParityResiduals

/-! ## 711 - Every prefix layer has at most two residual functions -/
namespace A711_PrefixResidualBound

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open A709_ParityResidual

noncomputable def residualImage (k : Nat) : Finset (Bool -> Bool) := by
  classical
  exact ((Finset.univ : Finset (Assignment k)).image parity).image residual

theorem residual_image_le_two (k : Nat) :
    (residualImage k).card <= 2 := by
  classical
  calc
    (residualImage k).card <=
        ((Finset.univ : Finset (Assignment k)).image parity).card := by
      unfold residualImage
      exact Finset.card_image_le
    _ <= 2 := ResearchFortySixth.A663_ParitySemanticClasses.parity_image_le_two k

end A711_PrefixResidualBound

/-! ## 712 - A raw prefix layer contains exactly 2^k assignments -/
namespace A712_RawPrefixCount

open ResearchFortyFifth.A646_BitFlip

theorem raw_prefix_count (k : Nat) :
    Fintype.card (Assignment k) = 2 ^ k :=
  ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card k

end A712_RawPrefixCount

/-! ## 713 - The parity quotient compresses 2^k raw prefixes to at most two states -/
namespace A713_LayerCompression

structure Compression (k : Nat) where
  rawPrefixes : Nat
  quotientStates : Nat
  rawEquation : rawPrefixes = 2 ^ k
  quotientBound : quotientStates <= 2

noncomputable def parityCompression (k : Nat) : Compression k where
  rawPrefixes := 2 ^ k
  quotientStates :=
    ((Finset.univ : Finset (ResearchFortyFifth.A646_BitFlip.Assignment k)).image
      ResearchFortyFifth.A647_RecursiveParity.parity).card
  rawEquation := rfl
  quotientBound :=
    ResearchFortySixth.A663_ParitySemanticClasses.parity_image_le_two k

end A713_LayerCompression

/-! ## 714 - From depth two onward the raw layer is strictly larger than the parity quotient -/
namespace A714_StrictLayerCompression

theorem two_lt_pow (k : Nat) (atLeastTwo : 2 <= k) : 2 < 2 ^ k := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le atLeastTwo
  induction offset with
  | zero => decide
  | succ offset ih =>
      rw [show 2 + (offset + 1) = (2 + offset) + 1 by omega]
      rw [pow_succ]
      omega

end A714_StrictLayerCompression

/-! ## 715 - Prefixes are equivalent exactly when their accumulated parity states agree -/
namespace A715_PrefixEquivalence

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open A709_ParityResidual

def Equivalent {k : Nat} (left right : Assignment k) : Prop :=
  A709_ParityResidual.residual (parity left) =
    A709_ParityResidual.residual (parity right)

theorem equivalent_iff_same_parity {k : Nat} (left right : Assignment k) :
    Equivalent left right <-> parity left = parity right := by
  constructor
  case mp =>
    intro equalResidual
    cases leftParity : parity left <;> cases rightParity : parity right
    case false.false => rfl
    case false.true =>
      exfalso
      apply A710_DistinctParityResiduals.residuals_distinct
      simpa [Equivalent, leftParity, rightParity] using equalResidual
    case true.false =>
      exfalso
      apply A710_DistinctParityResiduals.residuals_distinct
      symm
      simpa [Equivalent, leftParity, rightParity] using equalResidual
    case true.true => rfl
  case mpr =>
    intro equalParity
    exact A709_ParityResidual.equal_state_equal_residual equalParity

end A715_PrefixEquivalence

/-! ## 716 - The full tree stores every prefix separately -/
namespace A716_FullTreePrefixNodes

def prefixNodesThrough (n : Nat) : Nat := 2 ^ (n + 1) - 1

theorem prefix_node_formula (n : Nat) :
    prefixNodesThrough n = 2 ^ (n + 1) - 1 := rfl

end A716_FullTreePrefixNodes

/-! ## 717 - The reduced parity OBDD stores one root and two states per later layer -/
namespace A717_ReducedPrefixNodes

def reducedNodes (n : Nat) : Nat := 2 * n + 1

theorem reduced_node_formula (n : Nat) : reducedNodes n = 2 * n + 1 := rfl

end A717_ReducedPrefixNodes

/-! ## 718 - Prefix quotienting gives positive sharing savings from n=2 onward -/
namespace A718_PrefixSharingSaving

def saving (n : Nat) : Nat :=
  A716_FullTreePrefixNodes.prefixNodesThrough n - A717_ReducedPrefixNodes.reducedNodes n

theorem saving_positive (n : Nat) (atLeastTwo : 2 <= n) : 0 < saving n := by
  unfold saving A716_FullTreePrefixNodes.prefixNodesThrough A717_ReducedPrefixNodes.reducedNodes
  exact Nat.sub_pos_of_lt
    (ResearchFortyEighth.A703_TreeObddGap.obdd_lt_tree n atLeastTwo)

end A718_PrefixSharingSaving

/-! ## 719 - Any exact decoder for the two parity residuals needs at least two states -/
namespace A719_ParityResidualMinimality

open A709_ParityResidual

structure ExactEncoding (State : Type) [Fintype State] where
  encode : Bool -> State
  decode : State -> (Bool -> Bool)
  exact : forall prefixState, decode (encode prefixState) = residual prefixState

variable {State : Type} [Fintype State]

theorem encode_injective (encoding : ExactEncoding State) :
    Function.Injective encoding.encode := by
  intro left right same
  cases left <;> cases right
  · rfl
  · exfalso
    apply A710_DistinctParityResiduals.residuals_distinct
    rw [← encoding.exact false, ← encoding.exact true, same]
  · exfalso
    apply A710_DistinctParityResiduals.residuals_distinct
    symm
    rw [← encoding.exact false, ← encoding.exact true, same]
  · rfl

theorem state_card_lower_bound (encoding : ExactEncoding State) :
    2 <= Fintype.card State := by
  calc
    2 = Fintype.card Bool := by simp
    _ <= Fintype.card State :=
      Fintype.card_le_of_injective encoding.encode (encode_injective encoding)

end A719_ParityResidualMinimality

/-! ## 720 - The Boolean parity quotient is an exact minimal residual encoding -/
namespace A720_ExactMinimalParityQuotient

open A709_ParityResidual
open A719_ParityResidualMinimality

def booleanEncoding : ExactEncoding Bool where
  encode := fun state => state
  decode := residual
  exact := by intro state; rfl

theorem exact_two_states : Fintype.card Bool = 2 := by simp

theorem minimal (State : Type) [Fintype State] (encoding : ExactEncoding State) :
    Fintype.card Bool <= Fintype.card State := by
  simpa using state_card_lower_bound encoding

end A720_ExactMinimalParityQuotient

end PIsNPOrNot.ResearchFortyNinth
