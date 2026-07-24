import ResearchFortySixth

namespace PIsNPOrNot.ResearchFortySeventh

/-! ## 676 - Coordinate sensitivity is defined by one-bit flips -/
namespace A676_SensitiveAt

open ResearchFortyFifth.A646_BitFlip

def SensitiveAt {n : Nat} (label : Assignment n -> Bool)
    (bits : Assignment n) (index : Fin n) : Prop :=
  Not (label (flipAt bits index) = label bits)

end A676_SensitiveAt

/-! ## 677 - The sensitive coordinates form a finite set -/
namespace A677_SensitiveSet

open ResearchFortyFifth.A646_BitFlip
open A676_SensitiveAt

noncomputable def sensitiveSet {n : Nat} (label : Assignment n -> Bool)
    (bits : Assignment n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (SensitiveAt label bits)

noncomputable def sensitivity {n : Nat} (label : Assignment n -> Bool)
    (bits : Assignment n) : Nat :=
  (sensitiveSet label bits).card

end A677_SensitiveSet

/-! ## 678 - Point sensitivity is always at most the number of coordinates -/
namespace A678_SensitivityBound

open ResearchFortyFifth.A646_BitFlip
open A677_SensitiveSet

theorem sensitivity_le_n {n : Nat} (label : Assignment n -> Bool)
    (bits : Assignment n) :
    sensitivity label bits <= n := by
  classical
  unfold sensitivity
  calc
    (sensitiveSet label bits).card <= (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp

end A678_SensitivityBound

/-! ## 679 - A free coordinate of a safe cube cannot be sensitive at its representative -/
namespace A679_FreeCoordinateInsensitive

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open A676_SensitiveAt

theorem not_sensitive_of_free {n : Nat} (label : Assignment n -> Bool)
    (cube : Cube n) (representative : Assignment n)
    (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> label bits = label representative)
    (index : Fin n) (free : cube index = none) :
    Not (SensitiveAt label representative index) := by
  intro sensitive
  have flippedExtends :=
    ResearchFortyFifth.A650_FreeFlipExtends.flip_extends_of_free
      cube representative index representativeExtends free
  exact sensitive (safe (flipAt representative index) flippedExtends)

end A679_FreeCoordinateInsensitive

/-! ## 680 - Every sensitive coordinate must occur in the support of a safe cube -/
namespace A680_SensitiveSubsetSupport

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open ResearchFortyFourth.A636_CubeSupport
open A676_SensitiveAt
open A677_SensitiveSet

theorem sensitive_subset_support {n : Nat} (label : Assignment n -> Bool)
    (cube : Cube n) (representative : Assignment n)
    (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> label bits = label representative) :
    sensitiveSet label representative ⊆ support cube := by
  classical
  intro index sensitiveMember
  have sensitive : SensitiveAt label representative index :=
    (Finset.mem_filter.1 sensitiveMember).2
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ index, ?_⟩
  intro free
  exact (A679_FreeCoordinateInsensitive.not_sensitive_of_free
    label cube representative representativeExtends safe index free) sensitive

end A680_SensitiveSubsetSupport

/-! ## 681 - Sensitivity lower-bounds the width of every safe cube containing the point -/
namespace A681_SensitivityWidthLowerBound

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFirst.A586_Cube
open ResearchFortyFourth.A636_CubeSupport
open A677_SensitiveSet

theorem sensitivity_le_support {n : Nat} (label : Assignment n -> Bool)
    (cube : Cube n) (representative : Assignment n)
    (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> label bits = label representative) :
    sensitivity label representative <= (support cube).card := by
  unfold sensitivity
  exact Finset.card_le_card
    (A680_SensitiveSubsetSupport.sensitive_subset_support
      label cube representative representativeExtends safe)

end A681_SensitivityWidthLowerBound

/-! ## 682 - Every parity coordinate is sensitive -/
namespace A682_ParitySensitiveSet

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open ResearchFortyFifth.A648_ParityFlip
open A676_SensitiveAt
open A677_SensitiveSet

theorem parity_sensitive_set {n : Nat} (bits : Assignment n) :
    sensitiveSet parity bits = Finset.univ := by
  classical
  ext index
  simp [sensitiveSet, SensitiveAt, parity_flip_ne]

end A682_ParitySensitiveSet

/-! ## 683 - Parity has maximum point sensitivity n -/
namespace A683_ParitySensitivity

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open A677_SensitiveSet

theorem parity_sensitivity {n : Nat} (bits : Assignment n) :
    sensitivity parity bits = n := by
  unfold sensitivity
  rw [A682_ParitySensitiveSet.parity_sensitive_set]
  simp

end A683_ParitySensitivity

/-! ## 684 - Every parity-safe cube has full support -/
namespace A684_ParityFullSupport

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open ResearchFortyFirst.A586_Cube
open ResearchFortyFourth.A636_CubeSupport

theorem support_eq_univ {n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> parity bits = parity representative) :
    support cube = Finset.univ := by
  classical
  ext index
  constructor
  · intro _
    exact Finset.mem_univ index
  · intro _
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ index, ?_⟩
    exact ResearchFortyFifth.A651_NoFreeCoordinate.no_free_coordinate parity
      (ResearchFortyFifth.A649_FullSensitivity.parity_fully_sensitive n)
      cube representative representativeExtends safe index

end A684_ParityFullSupport

/-! ## 685 - Every parity-safe term has width exactly n -/
namespace A685_ParityTermWidth

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open ResearchFortyFirst.A586_Cube
open ResearchFortyFourth.A636_CubeSupport

theorem support_card_eq_n {n : Nat} (cube : Cube n)
    (representative : Assignment n) (representativeExtends : Extends representative cube)
    (safe : forall bits, Extends bits cube -> parity bits = parity representative) :
    (support cube).card = n := by
  rw [A684_ParityFullSupport.support_eq_univ
    cube representative representativeExtends safe]
  simp

end A685_ParityTermWidth

/-! ## 686 - Literal work sums cube supports over all terms -/
namespace A686_ParityLiteralWork

open ResearchFortyFifth.A655_ParityCubeCover
open ResearchFortyFourth.A636_CubeSupport

variable {n : Nat} {Term : Type} [Fintype Term] [DecidableEq Term]

noncomputable def literalWork (cover : ParityCubeCover n Term) : Nat :=
  ∑ term : Term, (support (cover.cube term)).card

theorem literal_work_eq (cover : ParityCubeCover n Term) :
    literalWork cover = Fintype.card Term * n := by
  classical
  unfold literalWork
  calc
    (∑ term : Term, (support (cover.cube term)).card) =
        ∑ _term : Term, n := by
      apply Finset.sum_congr rfl
      intro term _member
      exact A685_ParityTermWidth.support_card_eq_n
        (cover.cube term) (cover.representative term)
        (cover.representativeExtends term) (cover.safe term)
    _ = Fintype.card Term * n := by simp

end A686_ParityLiteralWork

/-! ## 687 - Every parity cube cover has at least n*2^n total literals -/
namespace A687_ParityLiteralLowerBound

open ResearchFortyFifth.A655_ParityCubeCover
open A686_ParityLiteralWork

variable {n : Nat} {Term : Type} [Fintype Term] [DecidableEq Term]

theorem literal_work_lower_bound (cover : ParityCubeCover n Term) :
    n * 2 ^ n <= literalWork cover := by
  rw [literal_work_eq cover]
  have termLower :=
    ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound cover
  have scaled := Nat.mul_le_mul_left n termLower
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using scaled

end A687_ParityLiteralLowerBound

/-! ## 688 - Fully sensitive labels admit only singleton safe cubes -/
namespace A688_GeneralSensitiveCover

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A649_FullSensitivity
open ResearchFortyFirst.A586_Cube

structure SensitiveCubeCover (n : Nat) (Term : Type) [Fintype Term]
    (label : Assignment n -> Bool) where
  cube : Term -> Cube n
  representative : Term -> Assignment n
  representativeExtends : forall term, Extends (representative term) (cube term)
  safe : forall term bits, Extends bits (cube term) ->
    label bits = label (representative term)
  complete : forall bits, exists term, Extends bits (cube term)
  fullySensitive : FullySensitive label

noncomputable def owner {n : Nat} {Term : Type} [Fintype Term]
    {label : Assignment n -> Bool}
    (cover : SensitiveCubeCover n Term label) (bits : Assignment n) : Term :=
  Classical.choose (cover.complete bits)

theorem owner_covers {n : Nat} {Term : Type} [Fintype Term]
    {label : Assignment n -> Bool}
    (cover : SensitiveCubeCover n Term label) (bits : Assignment n) :
    Extends bits (cover.cube (owner cover bits)) :=
  Classical.choose_spec (cover.complete bits)

end A688_GeneralSensitiveCover

/-! ## 689 - Every fully sensitive safe cube cover has at least 2^n terms -/
namespace A689_GeneralSensitiveLowerBound

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A652_FullySpecifiedCube
open ResearchFortyFirst.A586_Cube
open A688_GeneralSensitiveCover

variable {n : Nat} {Term : Type} [Fintype Term]
variable {label : Assignment n -> Bool}

theorem owner_injective (cover : SensitiveCubeCover n Term label) :
    Function.Injective (owner cover) := by
  intro left right sameOwner
  have leftCovered := owner_covers cover left
  have rightCovered := owner_covers cover right
  rw [sameOwner] at leftCovered
  have full : FullySpecified (cover.cube (owner cover right)) :=
    fullySpecified_of_no_free (cover.cube (owner cover right))
      (ResearchFortyFifth.A651_NoFreeCoordinate.no_free_coordinate label
        cover.fullySensitive (cover.cube (owner cover right))
        (cover.representative (owner cover right))
        (cover.representativeExtends (owner cover right))
        (cover.safe (owner cover right)))
  exact ResearchFortyFifth.A653_UniqueExtension.extensions_equal
    (cover.cube (owner cover right)) full left right leftCovered rightCovered

theorem term_card_lower_bound (cover : SensitiveCubeCover n Term label) :
    2 ^ n <= Fintype.card Term := by
  calc
    2 ^ n = Fintype.card (Assignment n) := by
      symm
      exact ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card n
    _ <= Fintype.card Term :=
      Fintype.card_le_of_injective (owner cover) (owner_injective cover)

end A689_GeneralSensitiveLowerBound

/-! ## 690 - Sensitivity exposes a general cube-only representation obstruction -/
namespace A690_SensitivityObstruction

structure Obstruction (n : Nat) where
  sensitivity : Nat
  minimumTerms : Nat
  fullSensitivity : sensitivity = n
  exponentialTerms : 2 ^ n <= minimumTerms
  literalLowerBound : n * 2 ^ n <= n * minimumTerms

def parityObstruction (n : Nat) : Obstruction n where
  sensitivity := n
  minimumTerms := 2 ^ n
  fullSensitivity := rfl
  exponentialTerms := le_rfl
  literalLowerBound := Nat.mul_le_mul_left n le_rfl

end A690_SensitivityObstruction

end PIsNPOrNot.ResearchFortySeventh
