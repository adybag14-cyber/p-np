import ResearchSixth
import CNFCore

/-!
# Approaches 76-90: proof-carrying AND/OR decision structures

This layer packages the operations developed earlier into a locally justified
AND/OR search object.  The important distinction is between correctness, which
composes from local certificates, and compactness, which requires a polynomial
bound on the number of distinct residual nodes.
-/

namespace PIsNPOrNot
namespace ResearchSeventh

/-! ## 76 - AND/OR decision trees -/
namespace A76_AndOrTree

inductive DecisionTree (I : Type) where
  | leaf (input : I)
  | orNode (input : I) (left right : DecisionTree I)
  | andNode (input : I) (left right : DecisionTree I)

def DecisionTree.root {I : Type} : DecisionTree I -> I
  | .leaf input => input
  | .orNode input _ _ => input
  | .andNode input _ _ => input

def DecisionTree.eval {I : Type} (leafSolver : I -> Bool) : DecisionTree I -> Bool
  | .leaf input => leafSolver input
  | .orNode _ left right => left.eval leafSolver || right.eval leafSolver
  | .andNode _ left right => left.eval leafSolver && right.eval leafSolver

end A76_AndOrTree

/-! ## 77 - Local semantic certificates imply global correctness -/
namespace A77_LocalValidity

open A76_AndOrTree

inductive Valid {I : Type} (Yes : I -> Prop) (leafSolver : I -> Bool) :
    DecisionTree I -> Prop
  | leaf (input : I)
      (correct : leafSolver input = true <-> Yes input) :
      Valid Yes leafSolver (.leaf input)
  | orNode (input : I) (left right : DecisionTree I)
      (splitCorrect : Yes input <-> Yes left.root \/ Yes right.root)
      (leftValid : Valid Yes leafSolver left)
      (rightValid : Valid Yes leafSolver right) :
      Valid Yes leafSolver (.orNode input left right)
  | andNode (input : I) (left right : DecisionTree I)
      (decomposeCorrect : Yes input <-> Yes left.root /\ Yes right.root)
      (leftValid : Valid Yes leafSolver left)
      (rightValid : Valid Yes leafSolver right) :
      Valid Yes leafSolver (.andNode input left right)

theorem eval_correct {I : Type} {Yes : I -> Prop} {leafSolver : I -> Bool}
    {tree : DecisionTree I} (valid : Valid Yes leafSolver tree) :
    tree.eval leafSolver = true <-> Yes tree.root := by
  induction valid with
  | leaf input correct => simpa [DecisionTree.eval, DecisionTree.root] using correct
  | orNode input left right splitCorrect leftValid rightValid ihLeft ihRight =>
      rw [DecisionTree.eval, Bool.or_eq_true, ihLeft, ihRight]
      simpa [DecisionTree.root] using splitCorrect.symm
  | andNode input left right decomposeCorrect leftValid rightValid ihLeft ihRight =>
      rw [DecisionTree.eval, Bool.and_eq_true, ihLeft, ihRight]
      simpa [DecisionTree.root] using decomposeCorrect.symm

end A77_LocalValidity

/-! ## 78 - Tree node accounting -/
namespace A78_NodeAccounting

open A76_AndOrTree

def nodeCount {I : Type} : DecisionTree I -> Nat
  | .leaf _ => 1
  | .orNode _ left right => 1 + nodeCount left + nodeCount right
  | .andNode _ left right => 1 + nodeCount left + nodeCount right

def leafCount {I : Type} : DecisionTree I -> Nat
  | .leaf _ => 1
  | .orNode _ left right => leafCount left + leafCount right
  | .andNode _ left right => leafCount left + leafCount right

theorem leafCount_le_nodeCount {I : Type} (tree : DecisionTree I) :
    leafCount tree <= nodeCount tree := by
  induction tree with
  | leaf input => simp [leafCount, nodeCount]
  | orNode input left right ihLeft ihRight =>
      simp only [leafCount, nodeCount]
      omega
  | andNode input left right ihLeft ihRight =>
      simp only [leafCount, nodeCount]
      omega

end A78_NodeAccounting

/-! ## 79 - A compiled tree decides its root instance -/
namespace A79_CertifiedCompiler

open A76_AndOrTree A77_LocalValidity

structure Compiler {I : Type} (Yes : I -> Prop) where
  leafSolver : I -> Bool
  compile : I -> DecisionTree I
  root_preserved : forall input, (compile input).root = input
  valid : forall input, Valid Yes leafSolver (compile input)

def Compiler.decide {I : Type} {Yes : I -> Prop}
    (compiler : Compiler Yes) (input : I) : Bool :=
  (compiler.compile input).eval compiler.leafSolver

theorem Compiler.decide_correct {I : Type} {Yes : I -> Prop}
    (compiler : Compiler Yes) (input : I) :
    compiler.decide input = true <-> Yes input := by
  rw [Compiler.decide, eval_correct (compiler.valid input), compiler.root_preserved]

end A79_CertifiedCompiler

/-! ## 80 - Polynomial tree size is an explicit sufficient condition -/
namespace A80_PolynomialTreeCompiler

open A76_AndOrTree A78_NodeAccounting A79_CertifiedCompiler

structure PolyCompiler {I : Type} (Yes : I -> Prop) extends Compiler Yes where
  inputSize : I -> Nat
  exponent : Nat
  node_bound : forall input, nodeCount (compile input) <= inputSize input ^ exponent

theorem decision_structure_polynomially_bounded {I : Type} {Yes : I -> Prop}
    (compiler : PolyCompiler Yes) (input : I) :
    nodeCount (compiler.compile input) <= compiler.inputSize input ^ compiler.exponent :=
  compiler.node_bound input

end A80_PolynomialTreeCompiler

/-! ## 81 - Semantic memo keys are safe -/
namespace A81_SemanticMemoKey

structure SemanticKey {I K : Type} (Yes : I -> Prop) where
  key : I -> K
  factors : forall left right, key left = key right -> (Yes left <-> Yes right)

theorem reuse_exact_answer {I K : Type} {Yes : I -> Prop}
    (memo : SemanticKey (I := I) (K := K) Yes)
    (solve : I -> Bool)
    (correct : forall input, solve input = true <-> Yes input)
    {left right : I} (same : memo.key left = memo.key right) :
    solve left = true <-> solve right = true := by
  rw [correct left, correct right]
  exact memo.factors left right same

end A81_SemanticMemoKey

/-! ## 82 - A finite key space bounds distinct residual answers -/
namespace A82_KeySpaceBound

variable {I K : Type} [Fintype I] [Fintype K] [DecidableEq K]

def keyImage (key : I -> K) : Finset K :=
  Finset.univ.image key

theorem keyImage_card_le (key : I -> K) :
    (keyImage key).card <= Fintype.card K := by
  exact Finset.card_le_univ _

end A82_KeySpaceBound

/-! ## 83 - Certified OR branching -/
namespace A83_OrBranch

def branchAnswer (left right : Bool) : Bool := left || right

theorem branchAnswer_correct
    (Root Left Right : Prop) (left right : Bool)
    (split : Root <-> Left \/ Right)
    (leftCorrect : left = true <-> Left)
    (rightCorrect : right = true <-> Right) :
    branchAnswer left right = true <-> Root := by
  rw [branchAnswer, Bool.or_eq_true, leftCorrect, rightCorrect]
  exact split.symm

end A83_OrBranch

/-! ## 84 - Certified AND decomposition -/
namespace A84_AndDecomposition

def decompositionAnswer (left right : Bool) : Bool := left && right

theorem decompositionAnswer_correct
    (Root Left Right : Prop) (left right : Bool)
    (decompose : Root <-> Left /\ Right)
    (leftCorrect : left = true <-> Left)
    (rightCorrect : right = true <-> Right) :
    decompositionAnswer left right = true <-> Root := by
  rw [decompositionAnswer, Bool.and_eq_true, leftCorrect, rightCorrect]
  exact decompose.symm

end A84_AndDecomposition

/-! ## 85 - Sharing can only reduce evaluation work -/
namespace A85_DagSharing

variable {Node : Type} [Fintype Node]

def dagWork (cost : Node -> Nat) : Nat :=
  Finset.univ.sum cost

theorem dagWork_le_card_mul
    (cost : Node -> Nat) (perNode : Nat)
    (bounded : forall node, cost node <= perNode) :
    dagWork cost <= Fintype.card Node * perNode := by
  unfold dagWork
  calc
    Finset.univ.sum cost <= Finset.univ.sum (fun _ : Node => perNode) :=
      Finset.sum_le_sum fun node _ => bounded node
    _ = Fintype.card Node * perNode := by simp

end A85_DagSharing

/-! ## 86 - Full unresolved branching remains exponential -/
namespace A86_FullBranching

def fullTreeNodes : Nat -> Nat
  | 0 => 1
  | depth + 1 => 1 + 2 * fullTreeNodes depth

theorem fullTreeNodes_plus_one (depth : Nat) :
    fullTreeNodes depth + 1 = 2 ^ (depth + 1) := by
  induction depth with
  | zero => simp [fullTreeNodes]
  | succ depth ih =>
      simp [fullTreeNodes, pow_succ]
      omega

theorem fullTreeNodes_closed (depth : Nat) :
    fullTreeNodes depth = 2 ^ (depth + 1) - 1 := by
  have h := fullTreeNodes_plus_one depth
  omega

end A86_FullBranching

/-! ## 87 - Width times depth bounds layered DAG size -/
namespace A87_LayeredWidth

def layeredNodes (widths : List Nat) : Nat := widths.sum

theorem layeredNodes_le_length_mul
    (widths : List Nat) (width : Nat)
    (bounded : forall value, List.Mem value widths -> value <= width) :
    layeredNodes widths <= widths.length * width := by
  unfold layeredNodes
  induction widths with
  | nil => simp
  | cons head tail ih =>
      have hHead : head <= width := bounded head (List.Mem.head tail)
      have hTail : forall value, List.Mem value tail -> value <= width := by
        intro value hmem
        exact bounded value (List.Mem.tail head hmem)
      simp only [List.sum_cons, List.length_cons]
      have hRec := ih hTail
      calc
        head + tail.sum <= width + tail.length * width := Nat.add_le_add hHead hRec
        _ = (tail.length + 1) * width := by
          simp [Nat.add_mul, Nat.add_comm]

end A87_LayeredWidth

/-! ## 88 - Logarithmic depth plus polynomial width remains polynomial -/
namespace A88_WidthDepthBudget

theorem width_depth_cost
    (input width depth exponent : Nat)
    (hWidth : width <= input ^ exponent)
    (hDepth : depth <= input) :
    depth * width <= input ^ (exponent + 1) := by
  calc
    depth * width <= input * (input ^ exponent) := Nat.mul_le_mul hDepth hWidth
    _ = (input ^ exponent) * input := Nat.mul_comm _ _
    _ = input ^ (exponent + 1) := (pow_succ input exponent).symm

end A88_WidthDepthBudget

/-! ## 89 - A proof-carrying DAG compiler yields an exact decider -/
namespace A89_ProofCarryingDagCompiler

structure DagCompiler {I : Type} (Yes : I -> Prop) where
  State : Type
  stateCount : I -> Nat
  compileAnswer : I -> Bool
  correct : forall input, compileAnswer input = true <-> Yes input
  inputSize : I -> Nat
  exponent : Nat
  state_bound : forall input, stateCount input <= inputSize input ^ exponent

def DagCompiler.decide {I : Type} {Yes : I -> Prop}
    (compiler : DagCompiler Yes) : I -> Bool := compiler.compileAnswer

theorem DagCompiler.decide_correct {I : Type} {Yes : I -> Prop}
    (compiler : DagCompiler Yes) (input : I) :
    compiler.decide input = true <-> Yes input :=
  compiler.correct input

end A89_ProofCarryingDagCompiler

/-! ## 90 - Exact class-level DAG criterion -/
namespace A90_DagCollapseCriterion

open A89_ProofCarryingDagCompiler

variable {Language Instance : Type}

structure UniformDagCover (InNP : Language -> Prop)
    (Accepts : Language -> Instance -> Prop) where
  compile : forall language, InNP language -> DagCompiler (Accepts language)

theorem np_subset_p_of_uniform_dag_cover
    (InNP InP : Language -> Prop)
    (Accepts : Language -> Instance -> Prop)
    (cover : UniformDagCover (Instance := Instance) InNP Accepts)
    (dagImpliesP : forall language,
      DagCompiler (Accepts language) -> InP language) :
    forall language, InNP language -> InP language := by
  intro language hNP
  exact dagImpliesP language (cover.compile language hNP)

end A90_DagCollapseCriterion

end ResearchSeventh
end PIsNPOrNot
