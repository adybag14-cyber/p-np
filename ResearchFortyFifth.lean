import ResearchFortyFourth

namespace PIsNPOrNot.ResearchFortyFifth

/-! ## 646 - Boolean assignments admit a one-coordinate flip operation -/
namespace A646_BitFlip

abbrev Assignment (n : Nat) := Fin n -> Bool

def flipAt {n : Nat} (bits : Assignment n) (index : Fin n) : Assignment n :=
  Function.update bits index (!(bits index))

theorem flipAt_changed {n : Nat} (bits : Assignment n) (index : Fin n) :
    flipAt bits index index = !(bits index) := by
  simp [flipAt]

theorem flipAt_unchanged {n : Nat} (bits : Assignment n)
    (changed other : Fin n) (different : Not (other = changed)) :
    flipAt bits changed other = bits other := by
  simp [flipAt, Function.update, different]

end A646_BitFlip

/-! ## 647 - Recursive parity is an explicit Boolean function -/
namespace A647_RecursiveParity

open A646_BitFlip

def parity : {n : Nat} -> Assignment n -> Bool
  | 0, _ => false
  | n + 1, bits => Bool.xor (bits 0) (parity (fun index => bits index.succ))

theorem parity_zero (bits : Assignment 0) : parity bits = false := rfl

end A647_RecursiveParity

/-! ## 648 - Flipping any coordinate flips parity -/
namespace A648_ParityFlip

open A646_BitFlip
open A647_RecursiveParity

theorem parity_flip {n : Nat} (bits : Assignment n) (index : Fin n) :
    parity (flipAt bits index) = !(parity bits) := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simp [parity, flipAt]
      · have htail :
          (fun j => Function.update bits tailIndex.succ (!(bits tailIndex.succ)) j.succ) =
            Function.update (fun j => bits j.succ) tailIndex (!(bits tailIndex.succ)) := by
            funext j
            simp [Function.update]
        simp only [parity, flipAt]
        have hne : Not ((0 : Fin (n + 1)) = tailIndex.succ) := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        rw [show Function.update bits tailIndex.succ (!(bits tailIndex.succ)) 0 = bits 0 by
          simp [Function.update, hne]]
        rw [htail]
        have hih := ih (fun j => bits j.succ) tailIndex
        rw [show parity (Function.update (fun j => bits j.succ) tailIndex (!(bits tailIndex.succ))) =
            !(parity (fun j => bits j.succ)) by
          simpa [flipAt] using hih]
        cases bits 0 <;> cases parity (fun j => bits j.succ) <;> decide

theorem parity_flip_ne {n : Nat} (bits : Assignment n) (index : Fin n) :
    Not (parity (flipAt bits index) = parity bits) := by
  rw [parity_flip]
  cases parity bits <;> decide

end A648_ParityFlip

/-! ## 649 - Full coordinate sensitivity abstracts the parity property -/
namespace A649_FullSensitivity

open A646_BitFlip

def FullySensitive {n : Nat} (label : Assignment n -> Bool) : Prop :=
  forall bits index, Not (label (flipAt bits index) = label bits)

theorem parity_fully_sensitive (n : Nat) :
    FullySensitive (@A647_RecursiveParity.parity n) := by
  intro bits index
  exact A648_ParityFlip.parity_flip_ne bits index

end A649_FullSensitivity

/-! ## 650 - Flipping a coordinate omitted by a cube preserves extension -/
namespace A650_FreeFlipExtends

open A646_BitFlip
open ResearchFortyFirst.A586_Cube

theorem flip_extends_of_free {n : Nat} (cube : Cube n)
    (bits : Assignment n) (index : Fin n)
    (bitsExtend : Extends bits cube) (free : cube index = none) :
    Extends (flipAt bits index) cube := by
  intro other bit fixed
  by_cases same : other = index
  · subst other
    rw [free] at fixed
    contradiction
  · rw [flipAt_unchanged bits index other same]
    exact bitsExtend other bit fixed

end A650_FreeFlipExtends

/-! ## 651 - A monochromatic cube for a fully sensitive label has no free coordinate -/
namespace A651_NoFreeCoordinate

open A646_BitFlip
open A649_FullSensitivity
open ResearchFortyFirst.A586_Cube

theorem no_free_coordinate {n : Nat} (label : Assignment n -> Bool)
    (sensitive : FullySensitive label) (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (monochromatic : forall bits, Extends bits cube -> label bits = label representative) :
    forall index, Not (cube index = none) := by
  intro index free
  have flippedExtends :=
    A650_FreeFlipExtends.flip_extends_of_free cube representative index representativeExtends free
  have equal := monochromatic (flipAt representative index) flippedExtends
  exact sensitive representative index equal

end A651_NoFreeCoordinate

/-! ## 652 - A cube without free coordinates fixes every bit -/
namespace A652_FullySpecifiedCube

open ResearchFortyFirst.A586_Cube

def FullySpecified {n : Nat} (cube : Cube n) : Prop :=
  forall index, exists bit, cube index = some bit

theorem fullySpecified_of_no_free {n : Nat} (cube : Cube n)
    (noFree : forall index, Not (cube index = none)) :
    FullySpecified cube := by
  intro index
  exact Option.ne_none_iff_exists'.1 (noFree index)

end A652_FullySpecifiedCube

/-! ## 653 - A fully specified cube has at most one total extension -/
namespace A653_UniqueExtension

open ResearchFortyFirst.A586_Cube
open A652_FullySpecifiedCube

theorem extensions_equal {n : Nat} (cube : Cube n) (fullySpecified : FullySpecified cube)
    (left right : Fin n -> Bool) (leftExtends : Extends left cube)
    (rightExtends : Extends right cube) :
    left = right := by
  funext index
  rcases fullySpecified index with ⟨bit, fixed⟩
  calc
    left index = bit := leftExtends index bit fixed
    _ = right index := (rightExtends index bit fixed).symm

end A653_UniqueExtension

/-! ## 654 - Every parity-safe cube is a singleton region -/
namespace A654_ParityCubeSingleton

open A646_BitFlip
open A647_RecursiveParity
open ResearchFortyFirst.A586_Cube
open A652_FullySpecifiedCube

theorem parity_safe_fully_specified {n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> parity bits = parity representative) :
    FullySpecified cube := by
  apply fullySpecified_of_no_free
  exact A651_NoFreeCoordinate.no_free_coordinate parity
    (A649_FullSensitivity.parity_fully_sensitive n) cube representative
    representativeExtends safe

theorem parity_safe_unique {n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> parity bits = parity representative)
    (bits : Assignment n) (bitsExtends : Extends bits cube) :
    bits = representative := by
  exact A653_UniqueExtension.extensions_equal cube
    (parity_safe_fully_specified cube representative representativeExtends safe)
    bits representative bitsExtends representativeExtends

end A654_ParityCubeSingleton

/-! ## 655 - A parity cube cover assigns every input to a safe term -/
namespace A655_ParityCubeCover

open A646_BitFlip
open A647_RecursiveParity
open ResearchFortyFirst.A586_Cube

structure ParityCubeCover (n : Nat) (Term : Type) [Fintype Term] where
  cube : Term -> Cube n
  representative : Term -> Assignment n
  representativeExtends : forall term, Extends (representative term) (cube term)
  safe : forall term bits, Extends bits (cube term) ->
    parity bits = parity (representative term)
  complete : forall bits, exists term, Extends bits (cube term)

noncomputable def owner {n : Nat} {Term : Type} [Fintype Term]
    (cover : ParityCubeCover n Term) (bits : Assignment n) : Term :=
  Classical.choose (cover.complete bits)

theorem owner_covers {n : Nat} {Term : Type} [Fintype Term]
    (cover : ParityCubeCover n Term) (bits : Assignment n) :
    Extends bits (cover.cube (owner cover bits)) :=
  Classical.choose_spec (cover.complete bits)

end A655_ParityCubeCover

/-! ## 656 - The owner map of a parity cube cover is injective -/
namespace A656_OwnerInjective

open A646_BitFlip
open A655_ParityCubeCover

variable {n : Nat} {Term : Type} [Fintype Term]

theorem owner_injective (cover : ParityCubeCover n Term) :
    Function.Injective (owner cover) := by
  intro left right sameOwner
  have leftCovered := owner_covers cover left
  have rightCovered := owner_covers cover right
  rw [sameOwner] at leftCovered
  exact A653_UniqueExtension.extensions_equal
    (cover.cube (owner cover right))
    (A654_ParityCubeSingleton.parity_safe_fully_specified
      (cover.cube (owner cover right))
      (cover.representative (owner cover right))
      (cover.representativeExtends (owner cover right))
      (cover.safe (owner cover right)))
    left right leftCovered rightCovered

end A656_OwnerInjective

/-! ## 657 - Every parity cube cover has at least 2^n terms -/
namespace A657_ParityTermLowerBound

open A646_BitFlip
open A655_ParityCubeCover

variable {n : Nat} {Term : Type} [Fintype Term]

theorem term_card_lower_bound (cover : ParityCubeCover n Term) :
    2 ^ n <= Fintype.card Term := by
  calc
    2 ^ n = Fintype.card (Assignment n) := by
      symm
      exact ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card n
    _ <= Fintype.card Term :=
      Fintype.card_le_of_injective (owner cover) (A656_OwnerInjective.owner_injective cover)

end A657_ParityTermLowerBound

/-! ## 658 - Singleton cubes attain the parity lower bound -/
namespace A658_SingletonParityCover

open A646_BitFlip
open A647_RecursiveParity
open A655_ParityCubeCover
open ResearchFortyFirst.A586_Cube
open ResearchFortyFirst.A596_SingletonCube

noncomputable def singletonCover (n : Nat) : ParityCubeCover n (Assignment n) where
  cube := singleton
  representative := fun bits => bits
  representativeExtends := by
    intro bits
    exact (extends_singleton_iff bits bits).2 rfl
  safe := by
    intro representative bits bitsExtend
    have equal := (extends_singleton_iff bits representative).1 bitsExtend
    subst bits
    rfl
  complete := by
    intro bits
    exact ⟨bits, (extends_singleton_iff bits bits).2 rfl⟩

theorem singleton_term_card (n : Nat) :
    Fintype.card (Assignment n) = 2 ^ n :=
  ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card n

end A658_SingletonParityCover

/-! ## 659 - The exact minimum safe cube-cover cardinality for parity is 2^n -/
namespace A659_ExactParityCubeComplexity

open A646_BitFlip
open A655_ParityCubeCover

structure ExactMinimum (n : Nat) where
  lower : forall (Term : Type) [Fintype Term], ParityCubeCover n Term ->
    2 ^ n <= Fintype.card Term
  witness : ParityCubeCover n (Assignment n)
  witnessCard : Fintype.card (Assignment n) = 2 ^ n

noncomputable def exactMinimum (n : Nat) : ExactMinimum n where
  lower := by
    intro Term inst cover
    exact A657_ParityTermLowerBound.term_card_lower_bound cover
  witness := A658_SingletonParityCover.singletonCover n
  witnessCard := A658_SingletonParityCover.singleton_term_card n

end A659_ExactParityCubeComplexity

/-! ## 660 - Two semantic labels can coexist with exponentially many safe cubes -/
namespace A660_SemanticCubeSeparation

structure Separation (n : Nat) where
  semanticLabels : Nat
  cubeTerms : Nat
  semanticBound : semanticLabels <= 2
  cubeLowerBound : 2 ^ n <= cubeTerms

variable {n : Nat} {Term : Type} [Fintype Term]

noncomputable def fromCover
    (cover : A655_ParityCubeCover.ParityCubeCover n Term) : Separation n where
  semanticLabels := 2
  cubeTerms := Fintype.card Term
  semanticBound := le_rfl
  cubeLowerBound := A657_ParityTermLowerBound.term_card_lower_bound cover

end A660_SemanticCubeSeparation

end PIsNPOrNot.ResearchFortyFifth
