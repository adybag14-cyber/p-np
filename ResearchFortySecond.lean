import ResearchFortyFirst

namespace PIsNPOrNot.ResearchFortySecond

/-! ## 601 - Membership in a two-region cover is disjunctive -/
namespace A601_UnionMembership

variable {α : Type} [DecidableEq α]

theorem mem_union_iff (left right : Finset α) (value : α) :
    value ∈ left ∪ right ↔ value ∈ left ∨ value ∈ right := by
  simp

end A601_UnionMembership

/-! ## 602 - Overlapping regions are harmless for existential SAT -/
namespace A602_OverlappingExistence

variable {α : Type} [DecidableEq α]

theorem exists_in_union_iff
    (left right : Finset α) (accept : α -> Prop) :
    (exists value, value ∈ left ∪ right ∧ accept value) ↔
      (exists value, value ∈ left ∧ accept value) ∨
      (exists value, value ∈ right ∧ accept value) := by
  constructor
  · rintro ⟨value, member, accepted⟩
    rcases Finset.mem_union.1 member with inLeft | inRight
    · exact Or.inl ⟨value, inLeft, accepted⟩
    · exact Or.inr ⟨value, inRight, accepted⟩
  · rintro (⟨value, member, accepted⟩ | ⟨value, member, accepted⟩)
    · exact ⟨value, Finset.mem_union_left _ member, accepted⟩
    · exact ⟨value, Finset.mem_union_right _ member, accepted⟩

end A602_OverlappingExistence

/-! ## 603 - Naive addition over an overlapping cover can overcount -/
namespace A603_DuplicateOvercount

theorem duplicate_singleton_overcounts :
    ({true} : Finset Bool).card + ({true} : Finset Bool).card >
      (({true} : Finset Bool) ∪ ({true} : Finset Bool)).card := by
  decide

end A603_DuplicateOvercount

/-! ## 604 - Disjoint union cardinalities add exactly -/
namespace A604_DisjointUnionCount

variable {α : Type} [DecidableEq α]

theorem card_union
    (left right : Finset α) (disjoint : Disjoint left right) :
    (left ∪ right).card = left.card + right.card := by
  exact Finset.card_union_of_disjoint disjoint

end A604_DisjointUnionCount

/-! ## 605 - Partitioned OR packages the condition needed for addition -/
namespace A605_PartitionedOr

variable {α : Type} [DecidableEq α]

structure PartitionedOr (left right : Finset α) : Prop where
  disjoint : Disjoint left right

theorem count
    (left right : Finset α) (partition : PartitionedOr left right) :
    (left ∪ right).card = left.card + right.card :=
  A604_DisjointUnionCount.card_union left right partition.disjoint

end A605_PartitionedOr

/-! ## 606 - Independent Cartesian products multiply cardinalities -/
namespace A606_DecomposableProduct

variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem product_card (left : Finset α) (right : Finset β) :
    (left ×ˢ right).card = left.card * right.card := by
  simp

end A606_DecomposableProduct

/-! ## 607 - Decomposable AND is represented by an exact Cartesian product -/
namespace A607_DecomposableAnd

variable {α β : Type} [DecidableEq α] [DecidableEq β]

structure DecomposableAnd (pairs : Finset (α × β))
    (left : Finset α) (right : Finset β) : Prop where
  exactProduct : pairs = left ×ˢ right

theorem count
    (pairs : Finset (α × β)) (left : Finset α) (right : Finset β)
    (decomposition : DecomposableAnd pairs left right) :
    pairs.card = left.card * right.card := by
  rw [decomposition.exactProduct]
  exact A606_DecomposableProduct.product_card left right

end A607_DecomposableAnd

/-! ## 608 - General overlap requires an explicit intersection correction -/
namespace A608_OverlapCorrection

variable {α : Type} [DecidableEq α]

theorem union_plus_intersection
    (left right : Finset α) :
    (left ∪ right).card + (left ∩ right).card = left.card + right.card :=
  ResearchThirteenth.A166_OverlapAccounting.union_plus_overlap left right

end A608_OverlapCorrection

/-! ## 609 - Subtracting previous coverage preserves the total union -/
namespace A609_FreshRegion

variable {α : Type} [DecidableEq α]

def fresh (previous current : Finset α) : Finset α :=
  current \ previous

theorem union_fresh_eq_union
    (previous current : Finset α) :
    previous ∪ fresh previous current = previous ∪ current := by
  ext value
  simp [fresh]

end A609_FreshRegion

/-! ## 610 - A fresh region is disjoint from all previous coverage -/
namespace A610_FreshDisjoint

variable {α : Type} [DecidableEq α]

theorem disjoint_fresh (previous current : Finset α) :
    Disjoint previous (A609_FreshRegion.fresh previous current) := by
  rw [Finset.disjoint_left]
  intro value inPrevious inFresh
  have notPrevious := (Finset.mem_sdiff.1 inFresh).2
  exact notPrevious inPrevious

end A610_FreshDisjoint

/-! ## 611 - Disjointisation yields an exact count decomposition -/
namespace A611_DisjointizedCount

variable {α : Type} [DecidableEq α]

theorem card_union_as_fresh_sum (previous current : Finset α) :
    (previous ∪ current).card =
      previous.card + (A609_FreshRegion.fresh previous current).card := by
  rw [← A609_FreshRegion.union_fresh_eq_union previous current]
  exact A604_DisjointUnionCount.card_union previous
    (A609_FreshRegion.fresh previous current)
    (A610_FreshDisjoint.disjoint_fresh previous current)

end A611_DisjointizedCount

/-! ## 612 - A finite list of regions has an exact union membership theorem -/
namespace A612_UnionAll

variable {α : Type} [DecidableEq α]

def unionAll : List (Finset α) -> Finset α
  | [] => ∅
  | region :: rest => region ∪ unionAll rest

theorem mem_unionAll_iff
    (regions : List (Finset α)) (value : α) :
    value ∈ unionAll regions ↔
      exists region, region ∈ regions ∧ value ∈ region := by
  induction regions with
  | nil => simp [unionAll]
  | cons head tail inductionHypothesis =>
      simp [unionAll, inductionHypothesis]

end A612_UnionAll

/-! ## 613 - SAT over a region family needs coverage but not disjointness -/
namespace A613_FamilyExistence

variable {α : Type} [DecidableEq α]

theorem exists_unionAll_iff
    (regions : List (Finset α)) (accept : α -> Prop) :
    (exists value, value ∈ A612_UnionAll.unionAll regions ∧ accept value) ↔
      exists region, region ∈ regions ∧
        exists value, value ∈ region ∧ accept value := by
  constructor
  · rintro ⟨value, member, accepted⟩
    rcases (A612_UnionAll.mem_unionAll_iff regions value).1 member with
      ⟨region, inFamily, inRegion⟩
    exact ⟨region, inFamily, value, inRegion, accepted⟩
  · rintro ⟨region, inFamily, value, inRegion, accepted⟩
    exact ⟨value,
      (A612_UnionAll.mem_unionAll_iff regions value).2
        ⟨region, inFamily, inRegion⟩,
      accepted⟩

end A613_FamilyExistence

/-! ## 614 - Cover checking and representative solving have additive work -/
namespace A614_CoverWork

structure Work where
  construction : Nat
  coverageCheck : Nat
  representativeSolving : Nat

def total (work : Work) : Nat :=
  work.construction + work.coverageCheck + work.representativeSolving

theorem total_bound
    (work : Work) (constructionBound coverageBound solvingBound budget : Nat)
    (construction : work.construction <= constructionBound)
    (coverage : work.coverageCheck <= coverageBound)
    (solving : work.representativeSolving <= solvingBound)
    (sumBound : constructionBound + coverageBound + solvingBound <= budget) :
    total work <= budget := by
  unfold total
  omega

end A614_CoverWork

/-! ## 615 - Uniform polynomial partition-aware covers imply P = NP -/
namespace A615_PartitionAwareCollapse

variable {Language : Type}

structure UniformPartitionAwareCovers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_partition_aware_covers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (covers : UniformPartitionAwareCovers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact covers.compilerGivesP language
    (covers.allNPHaveCompiler language inNP)

end A615_PartitionAwareCollapse

end PIsNPOrNot.ResearchFortySecond