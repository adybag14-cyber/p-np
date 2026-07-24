import Mathlib
import ResearchTwentyEighth
import ResearchTwentyNinth

namespace PIsNPOrNot.ResearchThirtieth

/-! ## 421 - Exact image tables carry both completeness and witness soundness -/
namespace A421_ExactImageTable

open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

structure Table (feature : Witness -> Feature) where
  rows : Finset Feature
  complete : forall witness, feature witness ∈ rows
  sound : forall value, value ∈ rows -> exists witness, feature witness = value

theorem rows_eq_reachableImage
    (feature : Witness -> Feature) (table : Table feature) :
    table.rows = reachableImage feature := by
  classical
  ext value
  constructor
  · intro member
    rcases table.sound value member with ⟨witness, rfl⟩
    exact Finset.mem_image.2 ⟨witness, Finset.mem_univ _, rfl⟩
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, rfl⟩
    exact table.complete witness

end A421_ExactImageTable

/-! ## 422 - Mapping an exact table gives an exact projected image table -/
namespace A422_MapImageTable

open A421_ExactImageTable

variable {Witness Feature Projected : Type}
variable [Fintype Witness] [DecidableEq Feature] [DecidableEq Projected]

def mapTable
    (feature : Witness -> Feature) (project : Feature -> Projected)
    (table : Table feature) : Table (fun witness => project (feature witness)) where
  rows := table.rows.image project
  complete := by
    intro witness
    exact Finset.mem_image.2 ⟨feature witness, table.complete witness, rfl⟩
  sound := by
    intro value member
    rcases Finset.mem_image.1 member with ⟨source, sourceMember, rfl⟩
    rcases table.sound source sourceMember with ⟨witness, rfl⟩
    exact ⟨witness, rfl⟩

theorem mapped_card_le
    (feature : Witness -> Feature) (project : Feature -> Projected)
    (table : Table feature) :
    (mapTable feature project table).rows.card <= table.rows.card := by
  exact Finset.card_image_le

end A422_MapImageTable

/-! ## 423 - Independent exact image tables compose by Cartesian product -/
namespace A423_ProductImageTable

open A421_ExactImageTable
open ResearchTwentyNinth.A406_ProductFeature

variable {Left Right LeftFeature RightFeature : Type}
variable [Fintype Left] [Fintype Right]
variable [DecidableEq LeftFeature] [DecidableEq RightFeature]

def productTable
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature)
    (leftTable : Table leftFeature)
    (rightTable : Table rightFeature) :
    Table (productFeature leftFeature rightFeature) where
  rows := leftTable.rows.product rightTable.rows
  complete := by
    intro witness
    exact Finset.mem_product.2 ⟨
      leftTable.complete witness.1,
      rightTable.complete witness.2⟩
  sound := by
    intro value member
    rcases Finset.mem_product.1 member with ⟨leftMember, rightMember⟩
    rcases leftTable.sound value.1 leftMember with ⟨leftWitness, leftEq⟩
    rcases rightTable.sound value.2 rightMember with ⟨rightWitness, rightEq⟩
    refine ⟨(leftWitness, rightWitness), ?_⟩
    exact Prod.ext leftEq rightEq

end A423_ProductImageTable

/-! ## 424 - Branch-local exact tables compose by union -/
namespace A424_BranchImageTable

open A421_ExactImageTable
open ResearchTwentyNinth.A410_BranchFeatureImage

variable {Left Right Feature : Type}
variable [Fintype Left] [Fintype Right] [DecidableEq Feature]

def branchTable
    (leftFeature : Left -> Feature)
    (rightFeature : Right -> Feature)
    (leftTable : Table leftFeature)
    (rightTable : Table rightFeature) :
    Table (branchFeature leftFeature rightFeature) where
  rows := leftTable.rows ∪ rightTable.rows
  complete := by
    intro witness
    cases witness with
    | inl left => exact Finset.mem_union_left _ (leftTable.complete left)
    | inr right => exact Finset.mem_union_right _ (rightTable.complete right)
  sound := by
    intro value member
    rcases Finset.mem_union.1 member with leftMember | rightMember
    · rcases leftTable.sound value leftMember with ⟨left, valueEq⟩
      exact ⟨Sum.inl left, valueEq⟩
    · rcases rightTable.sound value rightMember with ⟨right, valueEq⟩
      exact ⟨Sum.inr right, valueEq⟩

end A424_BranchImageTable

/-! ## 425 - Separator-indexed exact tables compose by finite bucket union -/
namespace A425_SeparatorImageTable

open A421_ExactImageTable

variable {Separator Local Feature : Type}
variable [Fintype Separator] [Fintype Local]
variable [DecidableEq Separator] [DecidableEq Feature]

def separatorTable
    (feature : Separator -> Local -> Feature)
    (tables : forall separator, Table (feature separator)) :
    Table (fun witness : Separator × Local => feature witness.1 witness.2) where
  rows := (Finset.univ : Finset Separator).biUnion
    (fun separator => (tables separator).rows)
  complete := by
    intro witness
    apply Finset.mem_biUnion.2
    exact ⟨witness.1, Finset.mem_univ _, (tables witness.1).complete witness.2⟩
  sound := by
    intro value member
    rcases Finset.mem_biUnion.1 member with ⟨separator, _, rowMember⟩
    rcases (tables separator).sound value rowMember with ⟨localWitness, valueEq⟩
    exact ⟨(separator, localWitness), valueEq⟩

end A425_SeparatorImageTable

/-! ## 426 - Product table size multiplies exactly -/
namespace A426_ProductTableCardinality

open A421_ExactImageTable A423_ProductImageTable

variable {Left Right LeftFeature RightFeature : Type}
variable [Fintype Left] [Fintype Right]
variable [DecidableEq LeftFeature] [DecidableEq RightFeature]

 theorem product_table_card
    (leftFeature : Left -> LeftFeature)
    (rightFeature : Right -> RightFeature)
    (leftTable : Table leftFeature)
    (rightTable : Table rightFeature) :
    (productTable leftFeature rightFeature leftTable rightTable).rows.card =
      leftTable.rows.card * rightTable.rows.card := by
  exact Finset.card_product _ _

end A426_ProductTableCardinality

/-! ## 427 - Branch table size is bounded by the branch-size sum -/
namespace A427_BranchTableBound

open A421_ExactImageTable A424_BranchImageTable

variable {Left Right Feature : Type}
variable [Fintype Left] [Fintype Right] [DecidableEq Feature]

 theorem branch_table_card_le
    (leftFeature : Left -> Feature)
    (rightFeature : Right -> Feature)
    (leftTable : Table leftFeature)
    (rightTable : Table rightFeature) :
    (branchTable leftFeature rightFeature leftTable rightTable).rows.card <=
      leftTable.rows.card + rightTable.rows.card := by
  exact Finset.card_union_le _ _

end A427_BranchTableBound

/-! ## 428 - Separator tables are bounded by separator count times bucket width -/
namespace A428_SeparatorTableBound

open A421_ExactImageTable A425_SeparatorImageTable

variable {Separator Local Feature : Type}
variable [Fintype Separator] [Fintype Local]
variable [DecidableEq Separator] [DecidableEq Feature]

 theorem separator_table_card_le
    (feature : Separator -> Local -> Feature)
    (tables : forall separator, Table (feature separator))
    (width : Nat)
    (bounded : forall separator, (tables separator).rows.card <= width) :
    (separatorTable feature tables).rows.card <=
      Fintype.card Separator * width := by
  classical
  unfold separatorTable
  simpa using Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset Separator)
    (fun separator => (tables separator).rows)
    width
    (by
      intro separator _
      exact bounded separator)

end A428_SeparatorTableBound

/-! ## 429 - Projection can only reduce an exact table -/
namespace A429_ProjectionMonotonicity

open A421_ExactImageTable A422_MapImageTable

variable {Witness Feature Projected : Type}
variable [Fintype Witness] [DecidableEq Feature] [DecidableEq Projected]

 theorem projection_never_increases
    (feature : Witness -> Feature) (project : Feature -> Projected)
    (table : Table feature) :
    (mapTable feature project table).rows.card <= table.rows.card :=
  mapped_card_le feature project table

end A429_ProjectionMonotonicity

/-! ## 430 - Bijective preprocessing transports exact image tables -/
namespace A430_TransformImageTable

open A421_ExactImageTable
open ResearchEighteenth.A241_BijectiveTransform

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

def transportTable
    (transform : Transform (Witness := Witness))
    (feature : Witness -> Feature)
    (table : Table feature) :
    Table (fun witness => feature (transform.encode witness)) where
  rows := table.rows
  complete := by
    intro witness
    exact table.complete (transform.encode witness)
  sound := by
    intro value member
    rcases table.sound value member with ⟨encoded, valueEq⟩
    refine ⟨transform.decode encoded, ?_⟩
    simpa [transform.encodeDecode] using valueEq

end A430_TransformImageTable

/-! ## 431 - A factored relation is decidable by scanning an exact image table -/
namespace A431_TableDecision

open A421_ExactImageTable

variable {Witness Feature : Type}

 theorem exists_accepting_iff_table
    (relation : Witness -> Bool)
    (feature : Witness -> Feature)
    (acceptFeature : Feature -> Bool)
    (factors : forall witness,
      relation witness = acceptFeature (feature witness))
    (table : Table feature) :
    (exists witness, relation witness = true) <->
      exists value, value ∈ table.rows /\ acceptFeature value = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨feature witness, table.complete witness, ?_⟩
    simpa [factors witness] using accepted
  · rintro ⟨value, member, accepted⟩
    rcases table.sound value member with ⟨witness, rfl⟩
    refine ⟨witness, ?_⟩
    simpa [factors witness] using accepted

end A431_TableDecision

/-! ## 432 - An exact output-feature table contains true exactly when a witness exists -/
namespace A432_OutputTableCircularity

open A421_ExactImageTable
open ResearchTwentyEighth.A396_OutputFeature

variable {Witness : Type} [Fintype Witness]

 theorem true_mem_output_table_iff
    (relation : Witness -> Bool)
    (table : Table (outputFeature relation)) :
    true ∈ table.rows <-> exists witness, relation witness = true := by
  constructor
  · intro member
    rcases table.sound true member with ⟨witness, valueEq⟩
    exact ⟨witness, valueEq⟩
  · rintro ⟨witness, accepted⟩
    have member := table.complete witness
    simpa [outputFeature, accepted] using member

end A432_OutputTableCircularity

/-! ## 433 - A table plan must account for materialized intermediate rows -/
namespace A433_MaterializationCost

 theorem materialization_cost_bound
    (tables : List Nat) (count width : Nat)
    (countBound : tables.length <= count)
    (widthBound : forall rows, rows ∈ tables -> rows <= width) :
    tables.sum <= count * width := by
  have localLemma : forall xs : List Nat,
      (forall rows, rows ∈ xs -> rows <= width) ->
        xs.sum <= xs.length * width := by
    intro xs bounded
    induction xs with
    | nil => simp
    | cons head tail ih =>
        have headBound : head <= width := bounded head (by simp)
        have tailBound : forall rows, rows ∈ tail -> rows <= width := by
          intro rows member
          exact bounded rows (by simp [member])
        have recBound := ih tailBound
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum <= width + tail.length * width :=
            Nat.add_le_add headBound recBound
          _ = (tail.length + 1) * width := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have localBound := localLemma tables widthBound
  exact le_trans localBound (Nat.mul_le_mul_right width countBound)

end A433_MaterializationCost

/-! ## 434 - A structural image plan exposes construction, materialization and scan costs -/
namespace A434_StructuralImagePlan

variable {Input : Type}

structure Plan (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  constructionCost : Input -> Nat
  materializationCost : Input -> Nat
  scanCost : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  constructionBound : forall input,
    constructionCost input <= inputSize input ^ exponent
  materializationBound : forall input,
    materializationCost input <= inputSize input ^ exponent
  scanBound : forall input,
    scanCost input <= inputSize input ^ exponent

theorem plan_exact
    (specification : Input -> Prop) (plan : Plan specification)
    (input : Input) :
    plan.decide input = true <-> specification input :=
  plan.exact input

end A434_StructuralImagePlan

/-! ## 435 - Uniform polynomial structural image plans yield the corrected collapse -/
namespace A435_StructuralPlanCollapse

variable {Language : Type}

structure UniformPlans (PClass NPClass : Set Language) where
  hasPlan : Language -> Prop
  allNPHavePlan : forall language,
    language ∈ NPClass -> hasPlan language
  planGivesP : forall language,
    hasPlan language -> language ∈ PClass

theorem p_eq_np_of_uniform_structural_plans
    (PClass NPClass : Set Language)
    (plans : UniformPlans PClass NPClass)
    (pSubsetNP : PClass ⊆ NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language member
  exact plans.planGivesP language (plans.allNPHavePlan language member)

end A435_StructuralPlanCollapse

end PIsNPOrNot.ResearchThirtieth
