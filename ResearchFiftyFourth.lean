import ResearchFiftyThird

namespace PIsNPOrNot.ResearchFiftyFourth

/-! ## 781 - Boolean bits embed as zero or one in a nontrivial cyclic group -/
namespace A781_ModularBitValue

def bitValue {m : Nat} (bit : Bool) : ZMod (m + 2) :=
  if bit then 1 else 0

end A781_ModularBitValue

/-! ## 782 - Modular population sum is a finite cyclic output function -/
namespace A782_ModularSum

open ResearchFortyFifth.A646_BitFlip
open A781_ModularBitValue

def modSum {m n : Nat} (bits : Assignment n) : ZMod (m + 2) :=
  ∑ index, bitValue (m := m) (bits index)

end A782_ModularSum

/-! ## 783 - One is nonzero modulo every modulus m+2 -/
namespace A783_OneNonzero

theorem one_ne_zero_mod {m : Nat} : (1 : ZMod (m + 2)) ≠ 0 := by
  intro equal
  have divisible : m + 2 ∣ 1 :=
    (ZMod.natCast_eq_zero_iff 1 (m + 2)).1 (by simpa using equal)
  have impossible : m + 2 = 1 := Nat.dvd_one.mp divisible
  omega

end A783_OneNonzero

/-! ## 784 - Flipping one bit replaces exactly one modular summand -/
namespace A784_ModularFlipFormula

open ResearchFortyFifth.A646_BitFlip
open A781_ModularBitValue
open A782_ModularSum

theorem flip_formula {m n : Nat} (bits : Assignment n) (index : Fin n) :
    modSum (m := m) (flipAt bits index) =
      modSum (m := m) bits - bitValue (m := m) (bits index) +
        bitValue (m := m) (!(bits index)) := by
  classical
  unfold modSum
  let f : Fin n -> ZMod (m + 2) := fun i => bitValue (m := m) (bits i)
  have updated :
      (fun i => bitValue (m := m) (flipAt bits index i)) =
        Function.update f index (bitValue (m := m) (!(bits index))) := by
    funext i
    by_cases same : i = index
    · subst i
      simp [flipAt, f]
    · simp [flipAt, Function.update, same, f]
  rw [updated, Finset.sum_update_of_mem (Finset.mem_univ index)]
  rw [Finset.sdiff_singleton_eq_erase]
  have original :=
    Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ index)
  dsimp [f] at original ⊢
  rw [← original]
  abel

end A784_ModularFlipFormula

/-! ## 785 - Adding or subtracting one changes every modular value -/
namespace A785_ModularUnitChange

open A783_OneNonzero

lemma add_one_ne_self {m : Nat} (value : ZMod (m + 2)) :
    value + 1 ≠ value := by
  intro equal
  have oneEqZero : (1 : ZMod (m + 2)) = 0 := by
    apply add_left_cancel (a := value)
    simpa using equal
  exact one_ne_zero_mod oneEqZero

lemma sub_one_ne_self {m : Nat} (value : ZMod (m + 2)) :
    value - 1 ≠ value := by
  intro equal
  have negOneEqZero : (-1 : ZMod (m + 2)) = 0 := by
    apply add_left_cancel (a := value)
    simpa [sub_eq_add_neg] using equal
  have oneEqZero : (1 : ZMod (m + 2)) = 0 := by
    have negated := congrArg Neg.neg negOneEqZero
    simpa using negated
  exact one_ne_zero_mod oneEqZero

end A785_ModularUnitChange

/-! ## 786 - Flipping any coordinate changes the modular population sum -/
namespace A786_ModularFlipSensitive

open ResearchFortyFifth.A646_BitFlip
open A781_ModularBitValue
open A782_ModularSum

theorem flip_ne {m n : Nat} (bits : Assignment n) (index : Fin n) :
    modSum (m := m) (flipAt bits index) ≠ modSum (m := m) bits := by
  rw [A784_ModularFlipFormula.flip_formula]
  cases old : bits index
  · simpa [bitValue, old, sub_zero] using
      A785_ModularUnitChange.add_one_ne_self (m := m) (modSum (m := m) bits)
  · simpa [bitValue, old, add_zero] using
      A785_ModularUnitChange.sub_one_ne_self (m := m) (modSum (m := m) bits)

end A786_ModularFlipSensitive

/-! ## 787 - Full sensitivity extends to arbitrary finite output types -/
namespace A787_GeneralFullSensitivity

open ResearchFortyFifth.A646_BitFlip

def FullySensitive {n : Nat} {Output : Type}
    (label : Assignment n -> Output) : Prop :=
  forall bits index, label (flipAt bits index) ≠ label bits

end A787_GeneralFullSensitivity

/-! ## 788 - Modular population sum is fully sensitive at every input -/
namespace A788_ModularFullSensitivity

open ResearchFortyFifth.A646_BitFlip
open A782_ModularSum
open A787_GeneralFullSensitivity

theorem fully_sensitive (m n : Nat) :
    FullySensitive (@modSum m n) := by
  intro bits index
  exact A786_ModularFlipSensitive.flip_ne bits index

end A788_ModularFullSensitivity

/-! ## 789 - A safe cube for any fully sensitive output has no free coordinate -/
namespace A789_GeneralNoFreeCoordinate

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open A787_GeneralFullSensitivity

variable {n : Nat} {Output : Type}

theorem no_free_coordinate (label : Assignment n -> Output)
    (sensitive : FullySensitive label) (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> label bits = label representative) :
    forall index, Not (cube index = none) := by
  intro index free
  have flippedExtends :=
    ResearchFortyFifth.A650_FreeFlipExtends.flip_extends_of_free
      cube representative index representativeExtends free
  have equal := safe (flipAt representative index) flippedExtends
  exact sensitive representative index equal

end A789_GeneralNoFreeCoordinate

/-! ## 790 - Every modular-sum-safe cube is fully specified -/
namespace A790_ModularCubeFullySpecified

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open ResearchFortyFifth.A652_FullySpecifiedCube
open A782_ModularSum

 theorem fully_specified {m n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube ->
      modSum (m := m) bits = modSum (m := m) representative) :
    FullySpecified cube := by
  apply fullySpecified_of_no_free
  exact A789_GeneralNoFreeCoordinate.no_free_coordinate (@modSum m n)
    (A788_ModularFullSensitivity.fully_sensitive m n) cube representative
    representativeExtends safe

end A790_ModularCubeFullySpecified

/-! ## 791 - Every modular-sum-safe cube has a unique total extension -/
namespace A791_ModularCubeUnique

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open A782_ModularSum

 theorem unique_extension {m n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube ->
      modSum (m := m) bits = modSum (m := m) representative)
    (bits : Assignment n) (bitsExtend : Extends bits cube) :
    bits = representative := by
  exact ResearchFortyFifth.A653_UniqueExtension.extensions_equal cube
    (A790_ModularCubeFullySpecified.fully_specified cube representative
      representativeExtends safe)
    bits representative bitsExtend representativeExtends

end A791_ModularCubeUnique

/-! ## 792 - A modular cube cover assigns every input to a safe term -/
namespace A792_ModularCubeCover

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open A782_ModularSum

structure ModularCubeCover (m n : Nat) (Term : Type) [Fintype Term] where
  cube : Term -> Cube n
  representative : Term -> Assignment n
  representativeExtends : forall term, Extends (representative term) (cube term)
  safe : forall term bits, Extends bits (cube term) ->
    modSum (m := m) bits = modSum (m := m) (representative term)
  complete : forall bits, exists term, Extends bits (cube term)

noncomputable def owner {m n : Nat} {Term : Type} [Fintype Term]
    (cover : ModularCubeCover m n Term) (bits : Assignment n) : Term :=
  Classical.choose (cover.complete bits)

theorem owner_covers {m n : Nat} {Term : Type} [Fintype Term]
    (cover : ModularCubeCover m n Term) (bits : Assignment n) :
    Extends bits (cover.cube (owner cover bits)) :=
  Classical.choose_spec (cover.complete bits)

end A792_ModularCubeCover

/-! ## 793 - The owner map of a modular cube cover is injective -/
namespace A793_ModularOwnerInjective

open ResearchFortyFifth.A646_BitFlip
open A792_ModularCubeCover

variable {m n : Nat} {Term : Type} [Fintype Term]

theorem owner_injective (cover : ModularCubeCover m n Term) :
    Function.Injective (owner cover) := by
  intro left right sameOwner
  have leftCovered := owner_covers cover left
  have rightCovered := owner_covers cover right
  rw [sameOwner] at leftCovered
  exact ResearchFortyFifth.A653_UniqueExtension.extensions_equal
    (cover.cube (owner cover right))
    (A790_ModularCubeFullySpecified.fully_specified
      (cover.cube (owner cover right))
      (cover.representative (owner cover right))
      (cover.representativeExtends (owner cover right))
      (cover.safe (owner cover right)))
    left right leftCovered rightCovered

end A793_ModularOwnerInjective

/-! ## 794 - Every modular-sum cube cover has at least 2^n terms -/
namespace A794_ModularTermLowerBound

open ResearchFortyFifth.A646_BitFlip
open A792_ModularCubeCover

variable {m n : Nat} {Term : Type} [Fintype Term]

theorem term_card_lower_bound (cover : ModularCubeCover m n Term) :
    2 ^ n <= Fintype.card Term := by
  calc
    2 ^ n = Fintype.card (Assignment n) := by
      symm
      exact ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card n
    _ <= Fintype.card Term :=
      Fintype.card_le_of_injective (owner cover)
        (A793_ModularOwnerInjective.owner_injective cover)

end A794_ModularTermLowerBound

/-! ## 795 - Uniform polynomial modular-sum cube compilers would imply P = NP -/
namespace A795_ModularCubeCollapse

variable {Language : Type}

structure UniformModularCubeCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_modular_cube_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformModularCubeCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A795_ModularCubeCollapse

end PIsNPOrNot.ResearchFiftyFourth
