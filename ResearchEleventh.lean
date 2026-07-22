import ResearchTenth
import CNFCore

/-!
# Adaptive semantic-width paradigm

Approaches 136-150 replace a single global variable order with residual-dependent
branch choices. Every branch is checked against pa-assignment semantics, and
the remaining-variable count is a certified decreasing rank.
-/

namespace PIsNPOrNot
namespace ResearchEleventh

open CNFCore

/-! ## 136 - Partial assignments and residual acceptance -/
namespace A136_PartialResidual

abbrev Partial (n : Nat) := Fin n -> Option Bool

def Extends {n : Nat} (assignment : Bits n) (pa : Partial n) : Prop :=
  forall x bit, pa x = some bit -> assignment x = bit

def ResidualAccept {n : Nat}
    (verifier : Bits n -> Bool) (pa : Partial n) : Prop :=
  exists assignment : Bits n,
    Extends assignment pa /\ verifier assignment = true

end A136_PartialResidual

/-! ## 137 - Assigning one previously unset variable -/
namespace A137_AssignPartial

open A136_PartialResidual

def assign {n : Nat} (pa : Partial n) (x : Fin n) (bit : Bool) : Partial n :=
  Function.update pa x (some bit)

theorem assign_at {n : Nat} (pa : Partial n) (x : Fin n) (bit : Bool) :
    assign pa x bit x = some bit := by
  simp [assign]

theorem assign_other {n : Nat} (pa : Partial n) (x y : Fin n)
    (bit : Bool) (hne : Not (y = x)) :
    assign pa x bit y = pa y := by
  simp [assign, hne]

end A137_AssignPartial

/-! ## 138 - Extension through an adaptive assignment -/
namespace A138_ExtensionCharacterization

open A136_PartialResidual A137_AssignPartial

theorem extends_assign_iff {n : Nat}
    (assignment : Bits n) (pa : Partial n) (x : Fin n) (bit : Bool)
    (unset : pa x = none) :
    Extends assignment (assign pa x bit) <->
      Extends assignment pa /\ assignment x = bit := by
  constructor
  · intro h
    constructor
    · intro y value hy
      by_cases hxy : y = x
      · subst y
        rw [unset] at hy
        contradiction
      · exact h y value (by simpa [assign, hxy] using hy)
    · exact h x bit (by simp [assign])
  · rintro ⟨hExtends, hx⟩ y value hy
    by_cases hxy : y = x
    · subst y
      have : bit = value := by
        simpa [assign] using hy
      simpa [this] using hx
    · exact hExtends y value (by simpa [assign, hxy] using hy)

end A138_ExtensionCharacterization

/-! ## 139 - Adaptive Shannon branching -/
namespace A139_AdaptiveShannon

open A136_PartialResidual A137_AssignPartial A138_ExtensionCharacterization

theorem residual_branch {n : Nat}
    (verifier : Bits n -> Bool) (pa : Partial n) (x : Fin n)
    (unset : pa x = none) :
    ResidualAccept verifier pa <->
      ResidualAccept verifier (assign pa x false) \/
      ResidualAccept verifier (assign pa x true) := by
  constructor
  · rintro ⟨assignment, hExtends, hAccept⟩
    cases hx : assignment x with
    | false =>
        left
        exact ⟨assignment,
          (extends_assign_iff assignment pa x false unset).2 ⟨hExtends, hx⟩,
          hAccept⟩
    | true =>
        right
        exact ⟨assignment,
          (extends_assign_iff assignment pa x true unset).2 ⟨hExtends, hx⟩,
          hAccept⟩
  · intro h
    rcases h with hFalse | hTrue
    · rcases hFalse with ⟨assignment, hExtends, hAccept⟩
      exact ⟨assignment,
        ((extends_assign_iff assignment pa x false unset).1 hExtends).1,
        hAccept⟩
    · rcases hTrue with ⟨assignment, hExtends, hAccept⟩
      exact ⟨assignment,
        ((extends_assign_iff assignment pa x true unset).1 hExtends).1,
        hAccept⟩

end A139_AdaptiveShannon

/-! ## 140 - The set of unassigned variables -/
namespace A140_UnassignedSet

open A136_PartialResidual A137_AssignPartial

noncomputable def unassigned {n : Nat} (pa : Partial n) : Finset (Fin n) :=
  Finset.univ.filter fun x => pa x = none

theorem mem_unassigned {n : Nat} (pa : Partial n) (x : Fin n) :
    x ∈ unassigned pa <-> pa x = none := by
  simp [unassigned]

theorem unassigned_assign {n : Nat}
    (pa : Partial n) (x : Fin n) (bit : Bool)
    (unset : pa x = none) :
    unassigned (assign pa x bit) = (unassigned pa).erase x := by
  ext y
  by_cases hyx : y = x
  · subst y
    simp [unassigned, assign]
  · simp [unassigned, assign, hyx]

end A140_UnassignedSet

/-! ## 141 - Every valid adaptive branch decreases rank by one -/
namespace A141_RankDecrease

open A136_PartialResidual A137_AssignPartial A140_UnassignedSet

noncomputable def rank {n : Nat} (pa : Partial n) : Nat :=
  (unassigned pa).card

theorem rank_assign_add_one {n : Nat}
    (pa : Partial n) (x : Fin n) (bit : Bool)
    (unset : pa x = none) :
    rank (assign pa x bit) + 1 = rank pa := by
  rw [rank, rank, unassigned_assign pa x bit unset]
  exact Finset.card_erase_add_one (by
    rw [mem_unassigned]
    exact unset)

theorem rank_assign_lt {n : Nat}
    (pa : Partial n) (x : Fin n) (bit : Bool)
    (unset : pa x = none) :
    rank (assign pa x bit) < rank pa := by
  have h := rank_assign_add_one pa x bit unset
  omega

end A141_RankDecrease

/-! ## 142 - Adaptive residual search trees -/
namespace A142_AdaptiveTree

open A136_PartialResidual

inductive Tree (n : Nat) where
  | leaf (pa : Partial n)
  | branch (pa : Partial n) (x : Fin n) (left right : Tree n)

def Tree.root {n : Nat} : Tree n -> Partial n
  | .leaf pa => pa
  | .branch pa _ _ _ => pa

def Tree.eval {n : Nat} (leafSolver : Partial n -> Bool) : Tree n -> Bool
  | .leaf pa => leafSolver pa
  | .branch _ _ left right => left.eval leafSolver || right.eval leafSolver

def Tree.depth {n : Nat} : Tree n -> Nat
  | .leaf _ => 0
  | .branch _ _ left right => 1 + max left.depth right.depth

def Tree.nodeCount {n : Nat} : Tree n -> Nat
  | .leaf _ => 1
  | .branch _ _ left right => 1 + left.nodeCount + right.nodeCount

end A142_AdaptiveTree

/-! ## 143 - Local certificates imply global adaptive-tree correctness -/
namespace A143_AdaptiveValidity

open A136_PartialResidual A137_AssignPartial A139_AdaptiveShannon A142_AdaptiveTree

inductive Valid {n : Nat}
    (verifier : Bits n -> Bool) (leafSolver : Partial n -> Bool) : Tree n -> Prop
  | leaf (pa : Partial n)
      (correct : leafSolver pa = true <-> ResidualAccept verifier pa) :
      Valid verifier leafSolver (.leaf pa)
  | branch (pa : Partial n) (x : Fin n) (left right : Tree n)
      (unset : pa x = none)
      (leftRoot : left.root = assign pa x false)
      (rightRoot : right.root = assign pa x true)
      (leftValid : Valid verifier leafSolver left)
      (rightValid : Valid verifier leafSolver right) :
      Valid verifier leafSolver (.branch pa x left right)

theorem eval_correct {n : Nat}
    {verifier : Bits n -> Bool} {leafSolver : Partial n -> Bool}
    {tree : Tree n} (valid : Valid verifier leafSolver tree) :
    tree.eval leafSolver = true <-> ResidualAccept verifier tree.root := by
  induction valid with
  | leaf pa correct => simpa [Tree.eval, Tree.root] using correct
  | branch pa x left right unset leftRoot rightRoot leftValid rightValid ihLeft ihRight =>
      rw [Tree.eval, Bool.or_eq_true, ihLeft, ihRight]
      change
        (ResidualAccept verifier left.root \/ ResidualAccept verifier right.root) <->
          ResidualAccept verifier pa
      rw [leftRoot, rightRoot]
      exact (residual_branch verifier pa x unset).symm

end A143_AdaptiveValidity

/-! ## 144 - Certified adaptive depth is bounded by remaining variables -/
namespace A144_AdaptiveDepth

open A136_PartialResidual A137_AssignPartial A141_RankDecrease
open A142_AdaptiveTree A143_AdaptiveValidity

theorem height_le_rank {n : Nat}
    {verifier : Bits n -> Bool} {leafSolver : Partial n -> Bool}
    {tree : Tree n} (valid : Valid verifier leafSolver tree) :
    tree.depth <= rank tree.root := by
  induction valid with
  | leaf pa correct =>
      change 0 <= rank pa
      exact Nat.zero_le _
  | branch pa x left right unset leftRoot rightRoot leftValid rightValid ihLeft ihRight =>
      have hFalse : rank left.root + 1 = rank pa := by
        rw [leftRoot]
        exact rank_assign_add_one pa x false unset
      have hTrue : rank right.root + 1 = rank pa := by
        rw [rightRoot]
        exact rank_assign_add_one pa x true unset
      change 1 + max left.depth right.depth <= rank pa
      have hLeft : left.depth + 1 <= rank pa := by omega
      have hRight : right.depth + 1 <= rank pa := by omega
      omega

end A144_AdaptiveDepth

/-! ## 145 - Any binary adaptive tree has the expected exponential ceiling -/
namespace A145_TreeCeiling

open A142_AdaptiveTree

theorem nodeCount_add_one_le_pow_height {n : Nat} (tree : Tree n) :
    tree.nodeCount + 1 <= 2 ^ (tree.depth + 1) := by
  induction tree with
  | leaf pa => simp [Tree.nodeCount, Tree.depth]
  | branch pa x left right ihLeft ihRight =>
      simp only [Tree.nodeCount, Tree.depth]
      have hMaxLeft : left.depth <= max left.depth right.depth := Nat.le_max_left _ _
      have hMaxRight : right.depth <= max left.depth right.depth := Nat.le_max_right _ _
      have hPowLeft : 2 ^ (left.depth + 1) <= 2 ^ (max left.depth right.depth + 1) :=
        Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hMaxLeft 1)
      have hPowRight : 2 ^ (right.depth + 1) <= 2 ^ (max left.depth right.depth + 1) :=
        Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hMaxRight 1)
      calc
        1 + left.nodeCount + right.nodeCount + 1 =
            (left.nodeCount + 1) + (right.nodeCount + 1) := by omega
        _ <= 2 ^ (left.depth + 1) + 2 ^ (right.depth + 1) :=
          Nat.add_le_add ihLeft ihRight
        _ <= 2 ^ (max left.depth right.depth + 1) +
            2 ^ (max left.depth right.depth + 1) :=
          Nat.add_le_add hPowLeft hPowRight
        _ = 2 ^ (1 + max left.depth right.depth + 1) := by
          rw [show 1 + max left.depth right.depth + 1 =
            (max left.depth right.depth + 1) + 1 by omega, pow_succ]
          omega

end A145_TreeCeiling

/-! ## 146 - Completion-set equality is a verifier-independent merge certificate -/
namespace A146_CompletionEquivalence

open A136_PartialResidual

def SameCompletions {n : Nat} (left right : Partial n) : Prop :=
  forall assignment : Bits n,
    Extends assignment left <-> Extends assignment right

theorem residual_equivalent_of_same_completions {n : Nat}
    (verifier : Bits n -> Bool) (left right : Partial n)
    (same : SameCompletions left right) :
    ResidualAccept verifier left <-> ResidualAccept verifier right := by
  constructor
  · rintro ⟨assignment, hExtends, hAccept⟩
    exact ⟨assignment, (same assignment).1 hExtends, hAccept⟩
  · rintro ⟨assignment, hExtends, hAccept⟩
    exact ⟨assignment, (same assignment).2 hExtends, hAccept⟩

end A146_CompletionEquivalence

/-! ## 147 - Verifier-specific residual equivalence is enough for memoization -/
namespace A147_SemanticAlias

open A136_PartialResidual

def SameResidual {n : Nat}
    (verifier : Bits n -> Bool) (left right : Partial n) : Prop :=
  ResidualAccept verifier left <-> ResidualAccept verifier right

theorem alias_sound {n : Nat}
    (verifier : Bits n -> Bool) (left right : Partial n)
    (same : SameResidual verifier left right) :
    ResidualAccept verifier left <-> ResidualAccept verifier right := same

end A147_SemanticAlias

/-! ## 148 - Polynomial-width adaptive DAG accounting -/
namespace A148_AdaptiveDagBudget


def dagNodes (widths : List Nat) : Nat := widths.sum

theorem dagNodes_le_depth_mul_width
    (widths : List Nat) (width : Nat)
    (bounded : forall value, List.Mem value widths -> value <= width) :
    dagNodes widths <= widths.length * width := by
  unfold dagNodes
  induction widths with
  | nil => simp
  | cons head tail ih =>
      have hHead : head <= width := bounded head (List.Mem.head tail)
      have hTail : forall value, List.Mem value tail -> value <= width := by
        intro value hmem
        exact bounded value (List.Mem.tail head hmem)
      have hRec := ih hTail
      simp only [List.sum_cons, List.length_cons]
      calc
        head + tail.sum <= width + tail.length * width := Nat.add_le_add hHead hRec
        _ = (tail.length + 1) * width := by
          rw [Nat.add_mul, Nat.one_mul]
          omega

end A148_AdaptiveDagBudget

/-! ## 149 - An adaptive compiler packages exactness and explicit budgets -/
namespace A149_AdaptiveCompiler

open A136_PartialResidual A142_AdaptiveTree A143_AdaptiveValidity

structure Compiler {n : Nat} (verifier : Bits n -> Bool) where
  leafSolver : Partial n -> Bool
  compile : Partial n -> Tree n
  root_correct : forall pa, (compile pa).root = pa
  valid : forall pa, Valid verifier leafSolver (compile pa)
  inputSize : Partial n -> Nat
  exponent : Nat
  node_bound : forall pa,
    (compile pa).nodeCount <= inputSize pa ^ exponent

noncomputable def Compiler.decide {n : Nat} {verifier : Bits n -> Bool}
    (compiler : Compiler verifier) (pa : Partial n) : Bool :=
  (compiler.compile pa).eval compiler.leafSolver

theorem Compiler.decide_correct {n : Nat} {verifier : Bits n -> Bool}
    (compiler : Compiler verifier) (pa : Partial n) :
    compiler.decide pa = true <-> ResidualAccept verifier pa := by
  unfold Compiler.decide
  rw [eval_correct (compiler.valid pa)]
  rw [compiler.root_correct pa]

end A149_AdaptiveCompiler

/-! ## 150 - The adaptive paradigm localizes the remaining global theorem -/
namespace A150_AdaptiveCollapseCriterion

open A149_AdaptiveCompiler

variable {Language Instance : Type}

theorem p_eq_np_of_uniform_adaptive_compilers
    (InP InNP : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (hasCompiler : Language -> Prop)
    (compilerImpliesP : forall language,
      hasCompiler language -> InP language)
    (uniform : forall language, InNP language -> hasCompiler language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compilerImpliesP language (uniform language hNP)

end A150_AdaptiveCollapseCriterion

end ResearchEleventh
end PIsNPOrNot