import ResearchAgenda
import CNFCore

/-!
# Approaches 59-68: concrete SAT reductions and polynomial accounting

This layer formalizes exact transformations used by structural SAT solvers.
The logical reductions are complete; the unresolved issue is proving a uniformly
small separator, backdoor, elimination width, or uncovered residual family for
every NP-complete instance.
-/

namespace PIsNPOrNot
namespace ResearchFifth

/-! ## 59 - Conditioning on a separator decomposes existential search -/
namespace A59_SeparatorConditioning

variable {A B S : Type}

theorem separator_exists
    (left : A -> S -> Prop) (right : B -> S -> Prop) :
    (exists a b s, left a s /\ right b s) <->
      exists s, (exists a, left a s) /\ (exists b, right b s) := by
  constructor
  · rintro ⟨a, b, s, hleft, hright⟩
    exact ⟨s, ⟨a, hleft⟩, ⟨b, hright⟩⟩
  · rintro ⟨s, ⟨a, hleft⟩, ⟨b, hright⟩⟩
    exact ⟨a, b, s, hleft, hright⟩

end A59_SeparatorConditioning

/-! ## 60 - A certified pure positive variable removes one branch -/
namespace A60_PureLiteral

variable {W : Type}

theorem pure_positive
    (R : Bool -> W -> Prop)
    (monotone : forall w, R false w -> R true w) :
    (exists bit w, R bit w) <-> exists w, R true w := by
  constructor
  · rintro ⟨bit, w, hw⟩
    cases bit with
    | false => exact ⟨w, monotone w hw⟩
    | true => exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨true, w, hw⟩

end A60_PureLiteral

/-! ## 61 - A logically subsumed constraint can be removed -/
namespace A61_Subsumption

theorem remove_subsumed
    (strong weak rest : Prop) (subsumes : strong -> weak) :
    (strong /\ weak /\ rest) <-> strong /\ rest := by
  constructor
  · rintro ⟨hstrong, _hweak, hrest⟩
    exact ⟨hstrong, hrest⟩
  · rintro ⟨hstrong, hrest⟩
    exact ⟨hstrong, subsumes hstrong, hrest⟩

end A61_Subsumption

/-! ## 62 - An autarky removes every clause it touches -/
namespace A62_Autarky

variable {Clause Completion : Type}

theorem remove_autarkic_region
    (clauses : List Clause)
    (touched : Clause -> Prop)
    (eval : Completion -> Clause -> Prop)
    (completion : Completion)
    (satisfiesTouched : forall clause,
      clause ∈ clauses -> touched clause -> eval completion clause) :
    (forall clause, clause ∈ clauses -> eval completion clause) <->
      forall clause, clause ∈ clauses -> Not (touched clause) ->
        eval completion clause := by
  constructor
  · intro hall clause hmem _hnt
    exact hall clause hmem
  · intro huntouched clause hmem
    by_cases ht : touched clause
    · exact satisfiesTouched clause hmem ht
    · exact huntouched clause hmem ht

end A62_Autarky

/-! ## 63 - Davis-Putnam variable elimination is equisatisfiable -/
namespace A63_DavisPutnam

/--
`positive` represents clauses `p OR x`; `negative` represents clauses
`n OR NOT x`. Eliminating `x` creates every resolvent `p OR n`.
-/
theorem eliminate_one_variable
    (positive negative : List Prop) (rest : Prop) :
    (exists x : Prop,
      (forall p, p ∈ positive -> p \/ x) /\
      (forall n, n ∈ negative -> n \/ Not x) /\ rest) <->
    ((forall p, p ∈ positive -> forall n, n ∈ negative -> p \/ n) /\ rest) := by
  classical
  constructor
  · rintro ⟨x, hpositive, hnegative, hrest⟩
    refine ⟨?_, hrest⟩
    intro p hp n hn
    have hpClause := hpositive p hp
    have hnClause := hnegative n hn
    by_cases hx : x
    · exact Or.inr (hnClause.resolve_right (not_not_intro hx))
    · exact Or.inl (hpClause.resolve_right hx)
  · rintro ⟨hresolvents, hrest⟩
    by_cases hallPositive : forall p, p ∈ positive -> p
    · refine ⟨False, ?_, ?_, hrest⟩
      · intro p hp
        exact Or.inl (hallPositive p hp)
      · intro n hn
        exact Or.inr (by simp)
    · have hexFalse : exists p, p ∈ positive /\ Not p := by
        push Not at hallPositive
        exact hallPositive
      rcases hexFalse with ⟨p0, hp0, hnotp0⟩
      have hallNegative : forall n, n ∈ negative -> n := by
        intro n hn
        exact (hresolvents p0 hp0 n hn).resolve_left hnotp0
      refine ⟨True, ?_, ?_, hrest⟩
      · intro p hp
        exact Or.inr trivial
      · intro n hn
        exact Or.inl (hallNegative n hn)

end A63_DavisPutnam

/-! ## 64 - One elimination step creates a product of clause counts -/
namespace A64_EliminationWidth

def resolventCount (positive negative : Nat) : Nat := positive * negative

theorem bounded_resolvent_count
    {positive negative width : Nat}
    (hpositive : positive <= width)
    (hnegative : negative <= width) :
    resolventCount positive negative <= width ^ 2 := by
  unfold resolventCount
  simpa [pow_two] using Nat.mul_le_mul hpositive hnegative

end A64_EliminationWidth

/-! ## 65 - A bounded elimination schedule has polynomial local work -/
namespace A65_BoundedEliminationSchedule

structure ElimStep where
  positive : Nat
  negative : Nat

def work : List ElimStep -> Nat
  | [] => 0
  | step :: rest => step.positive * step.negative + work rest

def BoundedBy (width : Nat) (steps : List ElimStep) : Prop :=
  forall step, step ∈ steps ->
    step.positive <= width /\ step.negative <= width

theorem work_le_length_mul_square
    (width : Nat) (steps : List ElimStep)
    (bounded : BoundedBy width steps) :
    work steps <= steps.length * (width ^ 2) := by
  induction steps with
  | nil => simp [work]
  | cons step rest ih =>
      have hstep := bounded step (by simp)
      have hrest : BoundedBy width rest := by
        intro candidate hmem
        exact bounded candidate (by simp [hmem])
      have hproduct : step.positive * step.negative <= width ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hstep.1 hstep.2
      calc
        work (step :: rest) =
            step.positive * step.negative + work rest := rfl
        _ <= width ^ 2 + rest.length * (width ^ 2) :=
          Nat.add_le_add hproduct (ih hrest)
        _ = (step :: rest).length * (width ^ 2) := by
          simp [Nat.succ_mul, Nat.add_comm]

end A65_BoundedEliminationSchedule

/-! ## 66 - Polynomial preprocessing, leaf count, and leaf cost compose -/
namespace A66_ThreeBudgetComposition

structure HybridBudget (inputSize : Nat) where
  preprocessCost : Nat
  leafCount : Nat
  maxLeafCost : Nat
  preprocessExponent : Nat
  leafCountExponent : Nat
  leafCostExponent : Nat
  preprocessBound : preprocessCost <= inputSize ^ preprocessExponent
  leafCountBound : leafCount <= inputSize ^ leafCountExponent
  leafCostBound : maxLeafCost <= inputSize ^ leafCostExponent

def HybridBudget.totalCost {inputSize : Nat}
    (budget : HybridBudget inputSize) : Nat :=
  budget.preprocessCost + budget.leafCount * budget.maxLeafCost

theorem total_cost_polynomial {inputSize : Nat}
    (budget : HybridBudget inputSize) :
    budget.totalCost <=
      inputSize ^ budget.preprocessExponent +
        inputSize ^ (budget.leafCountExponent + budget.leafCostExponent) := by
  calc
    budget.totalCost =
        budget.preprocessCost + budget.leafCount * budget.maxLeafCost := rfl
    _ <= inputSize ^ budget.preprocessExponent +
        (inputSize ^ budget.leafCountExponent) *
          (inputSize ^ budget.leafCostExponent) :=
      Nat.add_le_add budget.preprocessBound
        (Nat.mul_le_mul budget.leafCountBound budget.leafCostBound)
    _ = inputSize ^ budget.preprocessExponent +
        inputSize ^ (budget.leafCountExponent + budget.leafCostExponent) := by
      rw [pow_add]

end A66_ThreeBudgetComposition

/-! ## 67 - Superpolynomial total work localizes to an expensive leaf -/
namespace A67_CostObstruction

theorem expensive_leaf_of_total_exceeds
    (inputSize preprocess leaves maxLeaf a b c : Nat)
    (hpreprocess : preprocess <= inputSize ^ c)
    (hleaves : leaves <= inputSize ^ a)
    (hexceeds :
      inputSize ^ c + inputSize ^ (a + b) <
        preprocess + leaves * maxLeaf) :
    inputSize ^ b < maxLeaf := by
  by_contra hnot
  have hleaf : maxLeaf <= inputSize ^ b := Nat.le_of_not_gt hnot
  have hbound :
      preprocess + leaves * maxLeaf <=
        inputSize ^ c + inputSize ^ (a + b) := by
    calc
      preprocess + leaves * maxLeaf <=
          inputSize ^ c + (inputSize ^ a) * (inputSize ^ b) :=
        Nat.add_le_add hpreprocess (Nat.mul_le_mul hleaves hleaf)
      _ = inputSize ^ c + inputSize ^ (a + b) := by rw [pow_add]
  exact (Nat.not_lt_of_ge hbound) hexceeds

end A67_CostObstruction

/-! ## 68 - A logarithmic interface permits polynomial enumeration -/
namespace A68_LogarithmicInterface

structure InterfaceBudget (inputSize interfaceBits exponent : Nat) where
  assignmentsBound : 2 ^ interfaceBits <= inputSize ^ exponent

theorem enumeration_times_polynomial
    (inputSize interfaceBits interfaceExponent leafExponent : Nat)
    (budget : InterfaceBudget inputSize interfaceBits interfaceExponent)
    (leafCost : Nat)
    (hleaf : leafCost <= inputSize ^ leafExponent) :
    2 ^ interfaceBits * leafCost <=
      inputSize ^ (interfaceExponent + leafExponent) := by
  calc
    2 ^ interfaceBits * leafCost <=
        (inputSize ^ interfaceExponent) * (inputSize ^ leafExponent) :=
      Nat.mul_le_mul budget.assignmentsBound hleaf
    _ = inputSize ^ (interfaceExponent + leafExponent) := by rw [pow_add]

end A68_LogarithmicInterface

end ResearchFifth
end PIsNPOrNot
