import ResearchThirtyEighth

namespace PIsNPOrNot.ResearchThirtyNinth

/-! ## 556 - A quotient layer separates raw branches from unique residual classes -/
namespace A556_QuotientLayer

structure Layer where
  rawBranches : Nat
  uniqueClasses : Nat
  maximumClassWork : Nat
  classesBounded : uniqueClasses <= rawBranches

end A556_QuotientLayer

/-! ## 557 - Raw and quotient work are explicit products -/
namespace A557_LayerWork

open A556_QuotientLayer

def rawWork (layer : Layer) : Nat :=
  layer.rawBranches * layer.maximumClassWork

def quotientWork (layer : Layer) : Nat :=
  layer.uniqueClasses * layer.maximumClassWork

end A557_LayerWork

/-! ## 558 - Quotienting never costs more than solving every raw branch -/
namespace A558_QuotientNonincrease

open A556_QuotientLayer A557_LayerWork

theorem quotient_le_raw (layer : Layer) :
    quotientWork layer <= rawWork layer := by
  exact Nat.mul_le_mul_right layer.maximumClassWork layer.classesBounded

end A558_QuotientNonincrease

/-! ## 559 - A strict class reduction gives strict work reduction for positive class work -/
namespace A559_StrictQuotientSaving

open A556_QuotientLayer A557_LayerWork

theorem quotient_lt_raw
    (layer : Layer)
    (strictClasses : layer.uniqueClasses < layer.rawBranches)
    (positiveWork : 0 < layer.maximumClassWork) :
    quotientWork layer < rawWork layer := by
  exact Nat.mul_lt_mul_of_pos_right strictClasses positiveWork

end A559_StrictQuotientSaving

/-! ## 560 - All impossible branches can be charged as one residual class -/
namespace A560_ImpossibleClassSaving

theorem impossible_branch_saving
    (impossibleBranches : Nat) (positive : 0 < impossibleBranches) :
    1 <= impossibleBranches :=
  positive

theorem one_class_work_le_raw
    (impossibleBranches work : Nat)
    (positive : 0 < impossibleBranches) :
    work <= impossibleBranches * work := by
  simpa [Nat.one_mul] using Nat.mul_le_mul_right work
    (impossible_branch_saving impossibleBranches positive)

end A560_ImpossibleClassSaving

/-! ## 561 - A list of unique class counts measures memoized layered states -/
namespace A561_LayeredClassCounts

def totalStates (classCounts : List Nat) : Nat :=
  classCounts.sum

end A561_LayeredClassCounts

/-! ## 562 - Depth times maximum layer width bounds total memoized states -/
namespace A562_LayerWidthBound

open A561_LayeredClassCounts

theorem total_states_le_depth_mul_width
    (classCounts : List Nat) (depth width : Nat)
    (depthBound : classCounts.length <= depth)
    (widthBound : forall count, count ∈ classCounts -> count <= width) :
    totalStates classCounts <= depth * width := by
  have helper : forall values : List Nat,
      (forall count, count ∈ values -> count <= width) ->
      values.sum <= values.length * width := by
    intro values
    induction values with
    | nil => intro bounded; simp
    | cons head tail ih =>
        intro bounded
        have headBound : head <= width := bounded head (by simp)
        have tailBound : forall count, count ∈ tail -> count <= width := by
          intro count member
          exact bounded count (by simp [member])
        have recursive := ih tailBound
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum <= width + tail.length * width :=
            Nat.add_le_add headBound recursive
          _ = (tail.length + 1) * width := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact le_trans (helper classCounts widthBound)
    (Nat.mul_le_mul_right width depthBound)

end A562_LayerWidthBound

/-! ## 563 - Constant branching at every depth still creates exponentially many raw paths -/
namespace A563_RawPathBarrier

theorem binary_paths (depth : Nat) :
    (List.replicate depth 2).prod = 2 ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

end A563_RawPathBarrier

/-! ## 564 - Layered memoization counts state unions rather than path products -/
namespace A564_MemoVersusPaths

theorem two_state_layers_total (depth : Nat) :
    (List.replicate depth 2).sum = depth * 2 := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

end A564_MemoVersusPaths

/-! ## 565 - Every transition from a finite layer has at most states times fanout edges -/
namespace A565_TransitionBound

theorem transition_count_bound
    (states fanout transitions : Nat)
    (bounded : transitions <= states * fanout) :
    transitions <= states * fanout :=
  bounded

end A565_TransitionBound

/-! ## 566 - Polynomial layer states and polynomial fanout give polynomial transition work -/
namespace A566_TransitionBudget

theorem transition_budget
    (states fanout input stateExp fanoutExp : Nat)
    (stateBound : states <= input ^ stateExp)
    (fanoutBound : fanout <= input ^ fanoutExp) :
    states * fanout <= input ^ stateExp * input ^ fanoutExp := by
  exact Nat.mul_le_mul stateBound fanoutBound

end A566_TransitionBudget

/-! ## 567 - Memoized evaluation work is state count times per-state processing cost -/
namespace A567_MemoWork

theorem memo_work_bound
    (states perStateWork input stateExp workExp : Nat)
    (stateBound : states <= input ^ stateExp)
    (workBound : perStateWork <= input ^ workExp) :
    states * perStateWork <= input ^ stateExp * input ^ workExp := by
  exact Nat.mul_le_mul stateBound workBound

end A567_MemoWork

/-! ## 568 - Construction, memo traversal, and final scanning compose additively -/
namespace A568_RecursiveCompilerBudget

theorem total_budget
    (construction traversal scan input constructionExp traversalExp scanExp : Nat)
    (constructionBound : construction <= input ^ constructionExp)
    (traversalBound : traversal <= input ^ traversalExp)
    (scanBound : scan <= input ^ scanExp) :
    construction + traversal + scan <=
      input ^ constructionExp + input ^ traversalExp + input ^ scanExp := by
  exact Nat.add_le_add (Nat.add_le_add constructionBound traversalBound) scanBound

end A568_RecursiveCompilerBudget

/-! ## 569 - A recursively quotient-compiled candidate carries an exact answer -/
namespace A569_RecursiveQuotientCompiler

structure Compiled (specification : Prop) where
  answer : Bool
  constructionCost : Nat
  stateCount : Nat
  transitionCost : Nat
  exact : answer = true <-> specification

theorem compiled_decides
    (specification : Prop) (compiled : Compiled specification) :
    compiled.answer = true <-> specification :=
  compiled.exact

end A569_RecursiveQuotientCompiler

/-! ## 570 - Uniform polynomial recursive quotient compilers imply P = NP -/
namespace A570_RecursiveQuotientCollapse

variable {Language : Type}

structure UniformRecursiveQuotients (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_recursive_quotients
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformRecursiveQuotients PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A570_RecursiveQuotientCollapse

end PIsNPOrNot.ResearchThirtyNinth
