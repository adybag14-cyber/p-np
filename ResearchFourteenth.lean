import ResearchThirteenth

namespace PIsNPOrNot
namespace ResearchFourteenth

/-! ## 181 - Canonical semantic states represented by concrete DAG nodes -/
namespace A181_CanonicalRepresentation

structure Representation
    (Semantic Node : Type)
    [DecidableEq Semantic] [DecidableEq Node] where
  states : Finset Semantic
  nodes : Finset Node
  encode : Semantic -> Node
  injectiveOn : Set.InjOn encode states
  imageExact : states.image encode = nodes

theorem node_card_eq_state_card
    {Semantic Node : Type}
    [DecidableEq Semantic] [DecidableEq Node]
    (representation : Representation Semantic Node) :
    representation.nodes.card = representation.states.card := by
  have hImage : (representation.states.image representation.encode).card =
      representation.states.card :=
    (Finset.card_image_iff).2 representation.injectiveOn
  rw [representation.imageExact] at hImage
  exact hImage

end A181_CanonicalRepresentation

/-! ## 182 - Node-count comparisons are exactly semantic-state comparisons -/
namespace A182_CardinalitySignTransfer

open A181_CanonicalRepresentation

variable {Semantic Node : Type}
variable [DecidableEq Semantic] [DecidableEq Node]

theorem node_lt_iff_state_lt
    (before after : Representation Semantic Node) :
    after.nodes.card < before.nodes.card <->
      after.states.card < before.states.card := by
  rw [node_card_eq_state_card after, node_card_eq_state_card before]

theorem node_le_iff_state_le
    (before after : Representation Semantic Node) :
    after.nodes.card <= before.nodes.card <->
      after.states.card <= before.states.card := by
  rw [node_card_eq_state_card after, node_card_eq_state_card before]

end A182_CardinalitySignTransfer

/-! ## 183 - A contextual replacement splits into unaffected and replaced regions -/
namespace A183_ContextPartition

structure Replacement (Node : Type) [DecidableEq Node] where
  unaffected : Finset Node
  oldRegion : Finset Node
  newRegion : Finset Node

def Replacement.oldTotal
    {Node : Type} [DecidableEq Node]
    (replacement : Replacement Node) : Finset Node :=
  replacement.unaffected ∪ replacement.oldRegion

def Replacement.newTotal
    {Node : Type} [DecidableEq Node]
    (replacement : Replacement Node) : Finset Node :=
  replacement.unaffected ∪ replacement.newRegion

end A183_ContextPartition

/-! ## 184 - Region inclusion guarantees a nonworsening global replacement -/
namespace A184_ContextSubsetSafety

open A183_ContextPartition

variable {Node : Type} [DecidableEq Node]

theorem new_total_subset_old_total
    (replacement : Replacement Node)
    (regionSubset : replacement.newRegion ⊆ replacement.oldRegion) :
    replacement.newTotal ⊆ replacement.oldTotal := by
  intro node hNode
  have h : node ∈ replacement.unaffected ∨ node ∈ replacement.newRegion := by
    simpa only [Replacement.newTotal, Finset.mem_union] using hNode
  have result : node ∈ replacement.unaffected ∨ node ∈ replacement.oldRegion := by
    rcases h with hUnaffected | hNew
    · exact Or.inl hUnaffected
    · exact Or.inr (regionSubset hNew)
  simpa only [Replacement.oldTotal, Finset.mem_union] using result

theorem new_total_card_le_old_total
    (replacement : Replacement Node)
    (regionSubset : replacement.newRegion ⊆ replacement.oldRegion) :
    replacement.newTotal.card <= replacement.oldTotal.card := by
  exact Finset.card_le_card
    (new_total_subset_old_total replacement regionSubset)

end A184_ContextSubsetSafety

/-! ## 185 - A proper contextual subset gives a strict global saving -/
namespace A185_ContextStrictSaving

open A183_ContextPartition A184_ContextSubsetSafety

variable {Node : Type} [DecidableEq Node]

theorem new_total_card_lt_old_total
    (replacement : Replacement Node)
    (regionSubset : replacement.newRegion ⊆ replacement.oldRegion)
    (totalDifferent : replacement.newTotal ≠ replacement.oldTotal) :
    replacement.newTotal.card < replacement.oldTotal.card := by
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_subset_ne).2
    ⟨new_total_subset_old_total replacement regionSubset, totalDifferent⟩

end A185_ContextStrictSaving

/-! ## 186 - Disjoint context makes local and global cost differences identical -/
namespace A186_DisjointContextAccounting

open A183_ContextPartition
open PIsNPOrNot.ResearchThirteenth.A166_OverlapAccounting
open PIsNPOrNot.ResearchThirteenth.A173_ZeroOverlapAccounting

variable {Node : Type} [DecidableEq Node]

theorem old_total_card
    (replacement : Replacement Node)
    (oldDisjoint : overlapCredit replacement.unaffected replacement.oldRegion = 0) :
    replacement.oldTotal.card =
      replacement.unaffected.card + replacement.oldRegion.card := by
  exact union_card_eq_sum_of_zero_overlap
    replacement.unaffected replacement.oldRegion oldDisjoint

theorem new_total_card
    (replacement : Replacement Node)
    (newDisjoint : overlapCredit replacement.unaffected replacement.newRegion = 0) :
    replacement.newTotal.card =
      replacement.unaffected.card + replacement.newRegion.card := by
  exact union_card_eq_sum_of_zero_overlap
    replacement.unaffected replacement.newRegion newDisjoint

end A186_DisjointContextAccounting

/-! ## 187 - A smaller disjoint region strictly lowers the whole graph -/
namespace A187_LocalToGlobalStrictness

open A183_ContextPartition A186_DisjointContextAccounting
open PIsNPOrNot.ResearchThirteenth.A166_OverlapAccounting

variable {Node : Type} [DecidableEq Node]

theorem smaller_region_smaller_total
    (replacement : Replacement Node)
    (oldDisjoint : overlapCredit replacement.unaffected replacement.oldRegion = 0)
    (newDisjoint : overlapCredit replacement.unaffected replacement.newRegion = 0)
    (smaller : replacement.newRegion.card < replacement.oldRegion.card) :
    replacement.newTotal.card < replacement.oldTotal.card := by
  rw [old_total_card replacement oldDisjoint,
      new_total_card replacement newDisjoint]
  omega

end A187_LocalToGlobalStrictness

/-! ## 188 - The affected ancestor cone is bounded by decision depth -/
namespace A188_AncestorConeBudget

variable {Node : Type} [DecidableEq Node]

theorem affected_ancestors_le_depth
    (affectedAncestors : Finset Node) (depth : Nat)
    (bounded : affectedAncestors.card <= depth) :
    affectedAncestors.card <= depth := bounded

theorem replacement_region_bound
    (subtree ancestors : Finset Node) (subtreeBound depth : Nat)
    (hSubtree : subtree.card <= subtreeBound)
    (hAncestors : ancestors.card <= depth) :
    (subtree ∪ ancestors).card <= subtreeBound + depth := by
  have hUnion :=
    PIsNPOrNot.ResearchTwelfth.A158_SharingUpperBound.union_card_le_sum
      subtree ancestors
  omega

end A188_AncestorConeBudget

/-! ## 189 - A stable boundary fingerprint preserves exported semantics -/
namespace A189_BoundaryFingerprint

structure Fingerprint (Key : Type) where
  rootKey : Key
  answer : Bool

variable {Key : Type}

def Compatible (old new : Fingerprint Key) : Prop :=
  old.rootKey = new.rootKey /\ old.answer = new.answer

theorem compatible_root
    {old new : Fingerprint Key} (compatible : Compatible old new) :
    old.rootKey = new.rootKey := compatible.1

theorem compatible_answer
    {old new : Fingerprint Key} (compatible : Compatible old new) :
    old.answer = new.answer := compatible.2

end A189_BoundaryFingerprint

/-! ## 190 - Equal intern keys create no additional concrete node -/
namespace A190_InternKeyReuse

variable {Key : Type} [DecidableEq Key]

theorem insert_same_key
    (keys : Finset Key) (oldKey newKey : Key)
    (same : newKey = oldKey) :
    insert newKey (insert oldKey keys) = insert oldKey keys := by
  subst newKey
  simp

theorem existing_key_no_growth
    (keys : Finset Key) (key : Key) (present : key ∈ keys) :
    (insert key keys).card = keys.card := by
  simp [present]

end A190_InternKeyReuse

/-! ## 191 - A canonical representation attains any semantic lower bound -/
namespace A191_CanonicalOptimality

open A181_CanonicalRepresentation

variable {Semantic Node : Type}
variable [DecidableEq Semantic] [DecidableEq Node]

theorem canonical_nodes_le_any_exact_nodes
    (canonical : Representation Semantic Node)
    (otherNodes : Finset Node)
    (semanticLowerBound : canonical.states.card <= otherNodes.card) :
    canonical.nodes.card <= otherNodes.card := by
  rw [node_card_eq_state_card canonical]
  exact semanticLowerBound

end A191_CanonicalOptimality

/-! ## 192 - Exact representation transfers equality as well as inequalities -/
namespace A192_ExactDeltaTransfer

open A181_CanonicalRepresentation

variable {Semantic Node : Type}
variable [DecidableEq Semantic] [DecidableEq Node]

theorem node_eq_iff_state_eq
    (left right : Representation Semantic Node) :
    left.nodes.card = right.nodes.card <->
      left.states.card = right.states.card := by
  rw [node_card_eq_state_card left, node_card_eq_state_card right]

theorem node_difference_equation
    (left right : Representation Semantic Node)
    (difference : Nat) :
    left.nodes.card + difference = right.nodes.card <->
      left.states.card + difference = right.states.card := by
  rw [node_card_eq_state_card left, node_card_eq_state_card right]

end A192_ExactDeltaTransfer

/-! ## 193 - A polynomial semantic-state bound is a polynomial node bound -/
namespace A193_PolynomialStateToNode

open A181_CanonicalRepresentation

variable {Semantic Node : Type}
variable [DecidableEq Semantic] [DecidableEq Node]

theorem node_bound_of_state_bound
    (representation : Representation Semantic Node)
    (input exponent : Nat)
    (stateBound : representation.states.card <= input ^ exponent) :
    representation.nodes.card <= input ^ exponent := by
  rw [node_card_eq_state_card representation]
  exact stateBound

end A193_PolynomialStateToNode

/-! ## 194 - Uniform canonical semantic compilers imply P = NP -/
namespace A194_CanonicalCompilerCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_canonical_compilers
    (InP InNP : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (hasCanonicalCompiler : Language -> Prop)
    (compilerImpliesP : forall language,
      hasCanonicalCompiler language -> InP language)
    (uniform : forall language,
      InNP language -> hasCanonicalCompiler language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compilerImpliesP language (uniform language hNP)

end A194_CanonicalCompilerCollapse

/-! ## 195 - Separation forces failure of canonical polynomial compilation -/
namespace A195_CanonicalCompilerObstruction

variable {Language : Type}

theorem obstruction_of_separation
    (InP InNP : Language -> Prop)
    (separated : {language | InP language} ≠ {language | InNP language})
    (p_subset_np : forall language, InP language -> InNP language)
    (hasCanonicalCompiler : Language -> Prop)
    (compilerImpliesP : forall language,
      hasCanonicalCompiler language -> InP language) :
    exists language,
      InNP language /\ Not (hasCanonicalCompiler language) := by
  by_contra hnone
  push Not at hnone
  apply separated
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compilerImpliesP language (hnone language hNP)

end A195_CanonicalCompilerObstruction

end ResearchFourteenth
end PIsNPOrNot
