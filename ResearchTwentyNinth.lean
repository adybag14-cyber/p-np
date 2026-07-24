import Mathlib
import ResearchTwentyEighth
import ResearchEighteenth

namespace PIsNPOrNot.ResearchTwentyNinth

/-! ## 406 - Independent features combine as a product feature -/
namespace A406_ProductFeature

variable {Left Right LeftFeature RightFeature : Type}

def productFeature
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature) :
    Left × Right -> LeftFeature × RightFeature :=
  fun witness => (leftFeature witness.1, rightFeature witness.2)

end A406_ProductFeature

/-! ## 407 - The reachable image of an independent product is exactly the image product -/
namespace A407_ProductImage

open ResearchTwentyEighth.A391_ReachableFeatureImage
open A406_ProductFeature

variable {Left Right LeftFeature RightFeature : Type}
variable [Fintype Left] [Fintype Right]
variable [DecidableEq LeftFeature] [DecidableEq RightFeature]

 theorem reachable_product_eq
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature) :
    reachableImage (productFeature leftFeature rightFeature) =
      (reachableImage leftFeature).product (reachableImage rightFeature) := by
  classical
  ext value
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, rfl⟩
    exact Finset.mem_product.2 ⟨
      Finset.mem_image.2 ⟨witness.1, Finset.mem_univ witness.1, rfl⟩,
      Finset.mem_image.2 ⟨witness.2, Finset.mem_univ witness.2, rfl⟩⟩
  · intro member
    rcases Finset.mem_product.1 member with ⟨leftMember, rightMember⟩
    rcases Finset.mem_image.1 leftMember with ⟨leftWitness, _, leftEq⟩
    rcases Finset.mem_image.1 rightMember with ⟨rightWitness, _, rightEq⟩
    refine Finset.mem_image.2 ⟨(leftWitness, rightWitness),
      Finset.mem_univ _, ?_⟩
    exact Prod.ext leftEq rightEq

end A407_ProductImage

/-! ## 408 - Product-image cardinality multiplies exactly -/
namespace A408_ProductImageCardinality

open ResearchTwentyEighth.A391_ReachableFeatureImage
open A406_ProductFeature A407_ProductImage

variable {Left Right LeftFeature RightFeature : Type}
variable [Fintype Left] [Fintype Right]
variable [DecidableEq LeftFeature] [DecidableEq RightFeature]

 theorem reachable_product_card
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature) :
    (reachableImage (productFeature leftFeature rightFeature)).card =
      (reachableImage leftFeature).card * (reachableImage rightFeature).card := by
  rw [reachable_product_eq]
  exact Finset.card_product _ _

end A408_ProductImageCardinality

/-! ## 409 - Product quotient decision searches only reachable feature pairs -/
namespace A409_ProductQuotientDecision

open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Left Right LeftFeature RightFeature : Type}
variable [Fintype Left] [Fintype Right]
variable [DecidableEq LeftFeature] [DecidableEq RightFeature]

 theorem exists_pair_iff_reachable_features
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature)
    (combine : LeftFeature -> RightFeature -> Bool)
    (relation : Left × Right -> Bool)
    (factors : forall witness,
      relation witness = combine (leftFeature witness.1) (rightFeature witness.2)) :
    (exists witness, relation witness = true) <->
      exists leftValue rightValue,
        leftValue ∈ reachableImage leftFeature /\
        rightValue ∈ reachableImage rightFeature /\
        combine leftValue rightValue = true := by
  classical
  constructor
  · rintro ⟨⟨leftWitness, rightWitness⟩, accepted⟩
    refine ⟨leftFeature leftWitness, rightFeature rightWitness, ?_, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨leftWitness, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.2 ⟨rightWitness, Finset.mem_univ _, rfl⟩
    · simpa [factors (leftWitness, rightWitness)] using accepted
  · rintro ⟨leftValue, rightValue, leftMember, rightMember, accepted⟩
    rcases Finset.mem_image.1 leftMember with ⟨leftWitness, _, rfl⟩
    rcases Finset.mem_image.1 rightMember with ⟨rightWitness, _, rfl⟩
    refine ⟨(leftWitness, rightWitness), ?_⟩
    simpa [factors (leftWitness, rightWitness)] using accepted

end A409_ProductQuotientDecision

/-! ## 410 - Branch-local feature images combine by union -/
namespace A410_BranchFeatureImage

open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Left Right Feature : Type}
variable [Fintype Left] [Fintype Right] [DecidableEq Feature]

def branchFeature
    (leftFeature : Left -> Feature)
    (rightFeature : Right -> Feature) : Sum Left Right -> Feature
  | Sum.inl left => leftFeature left
  | Sum.inr right => rightFeature right

 theorem reachable_branch_eq_union
    (leftFeature : Left -> Feature)
    (rightFeature : Right -> Feature) :
    reachableImage (branchFeature leftFeature rightFeature) =
      reachableImage leftFeature ∪ reachableImage rightFeature := by
  classical
  ext value
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, valueEq⟩
    cases witness with
    | inl left =>
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨left, Finset.mem_univ left, valueEq⟩
    | inr right =>
        apply Finset.mem_union_right
        exact Finset.mem_image.2 ⟨right, Finset.mem_univ right, valueEq⟩
  · intro member
    rcases Finset.mem_union.1 member with leftMember | rightMember
    · rcases Finset.mem_image.1 leftMember with ⟨left, _, valueEq⟩
      exact Finset.mem_image.2 ⟨Sum.inl left, Finset.mem_univ _, valueEq⟩
    · rcases Finset.mem_image.1 rightMember with ⟨right, _, valueEq⟩
      exact Finset.mem_image.2 ⟨Sum.inr right, Finset.mem_univ _, valueEq⟩

end A410_BranchFeatureImage

/-! ## 411 - Branch-image cardinality is at most the sum of branch cardinalities -/
namespace A411_BranchImageBound

open ResearchTwentyEighth.A391_ReachableFeatureImage
open A410_BranchFeatureImage

variable {Left Right Feature : Type}
variable [Fintype Left] [Fintype Right] [DecidableEq Feature]

 theorem reachable_branch_card_le
    (leftFeature : Left -> Feature)
    (rightFeature : Right -> Feature) :
    (reachableImage (branchFeature leftFeature rightFeature)).card <=
      (reachableImage leftFeature).card + (reachableImage rightFeature).card := by
  rw [reachable_branch_eq_union]
  exact Finset.card_union_le _ _

end A411_BranchImageBound

/-! ## 412 - Separator-conditioned images are unions of finite buckets -/
namespace A412_SeparatorBuckets

open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Separator Local Feature : Type}
variable [Fintype Separator] [Fintype Local]
variable [DecidableEq Separator] [DecidableEq Feature]

def bucketImage (feature : Separator -> Local -> Feature)
    (separator : Separator) : Finset Feature :=
  reachableImage (feature separator)

def allBuckets (feature : Separator -> Local -> Feature) : Finset Feature :=
  (Finset.univ : Finset Separator).biUnion (bucketImage feature)

end A412_SeparatorBuckets

/-! ## 413 - Separator bucket union equals the global reachable image -/
namespace A413_SeparatorImageExact

open ResearchTwentyEighth.A391_ReachableFeatureImage
open A412_SeparatorBuckets

variable {Separator Local Feature : Type}
variable [Fintype Separator] [Fintype Local]
variable [DecidableEq Separator] [DecidableEq Feature]

 theorem allBuckets_eq_global_image
    (feature : Separator -> Local -> Feature) :
    allBuckets feature =
      reachableImage (fun witness : Separator × Local => feature witness.1 witness.2) := by
  classical
  ext value
  constructor
  · intro member
    rcases Finset.mem_biUnion.1 member with ⟨separator, _, bucketMember⟩
    rcases Finset.mem_image.1 bucketMember with ⟨localWitness, _, valueEq⟩
    exact Finset.mem_image.2 ⟨(separator, localWitness), Finset.mem_univ _, valueEq⟩
  · intro member
    rcases Finset.mem_image.1 member with ⟨⟨separator, localWitness⟩, _, valueEq⟩
    apply Finset.mem_biUnion.2
    refine ⟨separator, Finset.mem_univ separator, ?_⟩
    exact Finset.mem_image.2 ⟨localWitness, Finset.mem_univ localWitness, valueEq⟩

end A413_SeparatorImageExact

/-! ## 414 - Polynomially many bounded buckets have a product cardinality bound -/
namespace A414_SeparatorBucketBound

open A412_SeparatorBuckets

variable {Separator Local Feature : Type}
variable [Fintype Separator] [Fintype Local]
variable [DecidableEq Separator] [DecidableEq Feature]

 theorem allBuckets_card_le
    (feature : Separator -> Local -> Feature) (width : Nat)
    (bounded : forall separator,
      (bucketImage feature separator).card <= width) :
    (allBuckets feature).card <= Fintype.card Separator * width := by
  classical
  unfold allBuckets
  have h := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset Separator) (bucketImage feature) width
    (by
      intro separator _
      exact bounded separator)
  simpa using h

end A414_SeparatorBucketBound

/-! ## 415 - Bijective preprocessing transports an enumerator without changing its values -/
namespace A415_TransformEnumeratorTransport

open ResearchEighteenth.A241_BijectiveTransform
open ResearchTwentyEighth.A392_ReachableEnumerator

variable {Witness Feature : Type}

 def transport_enumerator
    (transform : Transform (Witness := Witness))
    (feature : Witness -> Feature)
    (enumerator : Enumerator feature) :
    Enumerator (fun witness => feature (transform.encode witness)) := by
  refine {
    values := enumerator.values
    complete := ?_
    sound := ?_
  }
  · intro witness
    exact enumerator.complete (transform.encode witness)
  · intro value member
    rcases enumerator.sound value member with ⟨encoded, valueEq⟩
    refine ⟨transform.decode encoded, ?_⟩
    simpa [transform.encodeDecode] using valueEq

end A415_TransformEnumeratorTransport

/-! ## 416 - Finite Boolean words drive exact layered state machines -/
namespace A416_FiniteWordRun

variable {State : Type}

def runFin (step : State -> Bool -> State) (start : State) :
    {n : Nat} -> (Fin n -> Bool) -> State
  | 0, _ => start
  | n + 1, word =>
      step (runFin step start (fun index : Fin n => word index.castSucc))
        (word (Fin.last n))

end A416_FiniteWordRun

/-! ## 417 - A layer is the exact image of all words of one length -/
namespace A417_LayerImage

open A416_FiniteWordRun

variable {State : Type} [DecidableEq State]

def layer (step : State -> Bool -> State) (start : State) (n : Nat) : Finset State :=
  (Finset.univ : Finset (Fin n -> Bool)).image (runFin step start)

end A417_LayerImage

/-! ## 418 - Layer membership is equivalent to a concrete word reaching the state -/
namespace A418_LayerMembership

open A416_FiniteWordRun A417_LayerImage

variable {State : Type} [DecidableEq State]

 theorem mem_layer_iff
    (step : State -> Bool -> State) (start state : State) (n : Nat) :
    state ∈ layer step start n <->
      exists word : Fin n -> Bool, runFin step start word = state := by
  classical
  simp [layer]

end A418_LayerMembership

/-! ## 419 - Every n-step layer has at most two to the n states -/
namespace A419_LayerCardinality

open A417_LayerImage

variable {State : Type} [DecidableEq State]

 theorem layer_card_le_pow_two
    (step : State -> Bool -> State) (start : State) (n : Nat) :
    (layer step start n).card <= 2 ^ n := by
  classical
  calc
    (layer step start n).card <= Fintype.card (Fin n -> Bool) :=
      Finset.card_image_le
    _ = 2 ^ n := by simp [Fintype.card_fun]

end A419_LayerCardinality

/-! ## 420 - Uniform structural image generators yield the corrected collapse criterion -/
namespace A420_StructuralImageCollapse

variable {Language : Type}

structure UniformStructuralGenerators
    (PClass NPClass : Set Language) where
  hasGenerator : Language -> Prop
  allNPHaveGenerator : forall language,
    language ∈ NPClass -> hasGenerator language
  generatorGivesP : forall language,
    hasGenerator language -> language ∈ PClass

theorem p_eq_np_of_uniform_structural_image_generators
    (PClass NPClass : Set Language)
    (cover : UniformStructuralGenerators PClass NPClass)
    (pSubsetNP : PClass ⊆ NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language member
  exact cover.generatorGivesP language
    (cover.allNPHaveGenerator language member)

end A420_StructuralImageCollapse

end PIsNPOrNot.ResearchTwentyNinth
