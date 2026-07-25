import ResearchSixtyFirst

namespace PIsNPOrNot.ResearchSixtySecond

/-! ## 901 - Boolean functions on n input bits form a finite universe -/
namespace A901_BooleanFunctionUniverse

abbrev Bits (n : Nat) := Fin n -> Bool
abbrev BoolFn (n : Nat) := Bits n -> Bool

end A901_BooleanFunctionUniverse

/-! ## 902 - The n-bit input space has cardinality 2^n -/
namespace A902_InputCardinality

open A901_BooleanFunctionUniverse

theorem input_card (n : Nat) : Fintype.card (Bits n) = 2 ^ n := by
  simp

end A902_InputCardinality

/-! ## 903 - The Boolean-function universe has cardinality 2^(2^n) -/
namespace A903_FunctionCardinality

open A901_BooleanFunctionUniverse

theorem function_card (n : Nat) : Fintype.card (BoolFn n) = 2 ^ (2 ^ n) := by
  simp

end A903_FunctionCardinality

/-! ## 904 - A b-bit circuit description denotes at most one Boolean function -/
namespace A904_DescriptionEvaluator

open A901_BooleanFunctionUniverse

abbrev Code (b : Nat) := Fin b -> Bool

def image {n b : Nat} (evaluate : Code b -> BoolFn n) : Finset (BoolFn n) := by
  classical
  exact (Finset.univ : Finset (Code b)).image evaluate

end A904_DescriptionEvaluator

/-! ## 905 - Description images contain at most as many functions as descriptions -/
namespace A905_ImageCardinality

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem image_card_le {n b : Nat} (evaluate : Code b -> BoolFn n) :
    (image evaluate).card <= Fintype.card (Code b) := by
  classical
  calc
    (image evaluate).card <= (Finset.univ : Finset (Code b)).card :=
      Finset.card_image_le
    _ = Fintype.card (Code b) := Finset.card_univ

end A905_ImageCardinality

/-! ## 906 - A b-bit description space has exactly 2^b descriptions -/
namespace A906_CodeCardinality

open A904_DescriptionEvaluator

theorem code_card (b : Nat) : Fintype.card (Code b) = 2 ^ b := by
  simp

end A906_CodeCardinality

/-! ## 907 - Fewer than 2^n description bits cannot cover all n-bit functions -/
namespace A907_CountingGap

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem code_space_lt_function_space {n b : Nat} (small : b < 2 ^ n) :
    Fintype.card (Code b) < Fintype.card (BoolFn n) := by
  rw [A906_CodeCardinality.code_card, A903_FunctionCardinality.function_card]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) small

end A907_CountingGap

/-! ## 908 - A short-description evaluator is not surjective -/
namespace A908_NonSurjective

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem not_surjective {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) : Not (Function.Surjective evaluate) := by
  intro surjective
  have cardLe : Fintype.card (BoolFn n) <= Fintype.card (Code b) :=
    Fintype.card_le_of_surjective evaluate surjective
  exact (Nat.not_le_of_gt (A907_CountingGap.code_space_lt_function_space small)) cardLe

end A908_NonSurjective

/-! ## 909 - Counting produces a Boolean function outside every short code image -/
namespace A909_HardFunctionExistence

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem exists_outside_image {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) :
    Exists fun hard : BoolFn n => forall code, Not (evaluate code = hard) := by
  by_contra noHard
  apply A908_NonSurjective.not_surjective evaluate small
  intro hard
  by_contra noCode
  apply noHard
  refine Exists.intro hard ?_
  intro code equality
  apply noCode
  exact Exists.intro code equality

end A909_HardFunctionExistence

/-! ## 910 - A noncomputable hard function can be selected from the counting proof -/
namespace A910_SelectedHardFunction

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

noncomputable def hardFunction {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) : BoolFn n :=
  (A909_HardFunctionExistence.exists_outside_image evaluate small).choose

end A910_SelectedHardFunction

/-! ## 911 - The selected function is outside the represented circuit family -/
namespace A911_SelectedHardness

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator A910_SelectedHardFunction

theorem hardFunction_not_computed {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) (code : Code b) :
    Not (evaluate code = hardFunction evaluate small) := by
  exact (A909_HardFunctionExistence.exists_outside_image evaluate small).choose_spec code

end A911_SelectedHardness

/-! ## 912 - An explicit truth table for an n-bit function contains 2^n output bits -/
namespace A912_TruthTableLength

theorem truth_table_length (n : Nat) : Fintype.card (Fin n -> Bool) = 2 ^ n := by
  simp

end A912_TruthTableLength

/-! ## 913 - Listing a hard truth table is exponential in the original input length -/
namespace A913_TableStorage

def tableBits (n : Nat) : Nat := 2 ^ n

theorem table_bits_formula (n : Nat) : tableBits n = 2 ^ n := rfl

theorem table_bits_double (n : Nat) : tableBits (n + 1) = 2 * tableBits n := by
  simp [tableBits, pow_succ, Nat.mul_comm]

end A913_TableStorage

/-! ## 914 - Counting alone cannot force membership in an arbitrary target class -/
namespace A914_PropertySelectionGap

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem represented_property_has_no_hard_member {n b : Nat}
    (evaluate : Code b -> BoolFn n) :
    Not (Exists fun function =>
      And (Membership.mem (image evaluate) function)
        (forall code, Not (evaluate code = function))) := by
  rintro ⟨function, represented, hard⟩
  rcases Finset.mem_image.mp represented with ⟨code, _member, equality⟩
  exact hard code equality

end A914_PropertySelectionGap

/-! ## 915 - Counting separates a target slice only after that slice is proved large -/
namespace A915_TargetSliceCriterion

open A901_BooleanFunctionUniverse A904_DescriptionEvaluator

theorem exists_target_outside {n b : Nat}
    (evaluate : Code b -> BoolFn n)
    (target : Finset (BoolFn n))
    (larger : (image evaluate).card < target.card) :
    Exists fun function =>
      And (Membership.mem target function)
        (Not (Membership.mem (image evaluate) function)) := by
  by_contra noneOutside
  have subset : target ⊆ image evaluate := by
    intro function member
    by_contra outside
    apply noneOutside
    exact Exists.intro function (And.intro member outside)
  have cardLe := Finset.card_le_card subset
  exact (Nat.not_le_of_gt larger) cardLe

end A915_TargetSliceCriterion

end PIsNPOrNot.ResearchSixtySecond
