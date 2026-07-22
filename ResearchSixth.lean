import ResearchFifth

/-!
# Approaches 69-75: private-variable peeling and residual cores

The elimination-width experiment found that some sparse constraint systems are
not merely low-width: variables occurring in one locally solvable constraint can
be peeled without producing any residual constraint.  This file formalizes the
logic of that route and localizes all remaining difficulty to the unpeeled core.
-/

namespace PIsNPOrNot
namespace ResearchSixth

/-! ## 69 - A private locally solvable variable erases its constraint -/
namespace A69_PrivateVariable

variable {R : Type}

theorem eliminate_private_variable
    (constraint : Bool -> R -> Prop) (rest : R -> Prop)
    (locallySolvable : forall residual, rest residual ->
      exists bit, constraint bit residual) :
    (exists bit residual, constraint bit residual /\ rest residual) <->
      exists residual, rest residual := by
  constructor
  · rintro ⟨bit, residual, _hlocal, hrest⟩
    exact ⟨residual, hrest⟩
  · rintro ⟨residual, hrest⟩
    rcases locallySolvable residual hrest with ⟨bit, hlocal⟩
    exact ⟨bit, residual, hlocal, hrest⟩

end A69_PrivateVariable

/-! ## 70 - A three-variable XOR equation is solvable for any one variable -/
namespace A70_XorLeaf

open ResearchFourth.A48_XorEncoding

theorem xor3_solvable_for_first (rhs a b : Bool) :
    exists x, xor3 x a b = rhs := by
  cases rhs <;> cases a <;> cases b <;> decide

theorem xor3_solvable_for_second (rhs a b : Bool) :
    exists x, xor3 a x b = rhs := by
  cases rhs <;> cases a <;> cases b <;> decide

theorem xor3_solvable_for_third (rhs a b : Bool) :
    exists x, xor3 a b x = rhs := by
  cases rhs <;> cases a <;> cases b <;> decide

end A70_XorLeaf

/-! ## 71 - A private XOR leaf constraint can be removed exactly -/
namespace A71_PeelXorLeaf

open ResearchFourth.A48_XorEncoding
open A70_XorLeaf

theorem peel_first_xor_variable
    (rhs a b : Bool) (rest : Prop) :
    (exists x, xor3 x a b = rhs /\ rest) <-> rest := by
  constructor
  · rintro ⟨_x, _hx, hrest⟩
    exact hrest
  · intro hrest
    rcases xor3_solvable_for_first rhs a b with ⟨x, hx⟩
    exact ⟨x, hx, hrest⟩

end A71_PeelXorLeaf

/-! ## 72 - Equisatisfiable peeling steps compose transitively -/
namespace A72_PeelChain

inductive PeelChain : Prop -> Prop -> Prop
  | refl (problem : Prop) : PeelChain problem problem
  | step {before middle after : Prop}
      (head : before <-> middle)
      (tail : PeelChain middle after) :
      PeelChain before after

theorem PeelChain.correct {before after : Prop}
    (chain : PeelChain before after) : before <-> after := by
  induction chain with
  | refl problem => rfl
  | step head tail ih => exact head.trans ih

end A72_PeelChain

/-! ## 73 - All post-peeling hardness is localized to the residual core -/
namespace A73_CoreLocalization

open A72_PeelChain

theorem original_iff_core {original core : Prop}
    (peeling : PeelChain original core) :
    original <-> core :=
  peeling.correct

theorem original_unsat_of_core_unsat {original core : Prop}
    (peeling : PeelChain original core)
    (coreUnsat : Not core) : Not original := by
  intro horiginal
  exact coreUnsat (peeling.correct.mp horiginal)

theorem original_sat_of_core_sat {original core : Prop}
    (peeling : PeelChain original core)
    (coreSat : core) : original :=
  peeling.correct.mpr coreSat

end A73_CoreLocalization

/-! ## 74 - Polynomial peeling plus a small core gives polynomial total work -/
namespace A74_SmallCoreBudget

structure CoreBudget
    (inputSize coreBits peelExponent coreExponent : Nat) where
  peelCost : Nat
  coreCheckCost : Nat
  peelBound : peelCost <= inputSize ^ peelExponent
  assignmentsBound : 2 ^ coreBits <= inputSize ^ coreExponent

def CoreBudget.totalCost
    {inputSize coreBits peelExponent coreExponent : Nat}
    (budget : CoreBudget inputSize coreBits peelExponent coreExponent) : Nat :=
  budget.peelCost + 2 ^ coreBits * budget.coreCheckCost

theorem total_cost_bound
    (inputSize coreBits peelExponent coreExponent checkExponent : Nat)
    (budget : CoreBudget inputSize coreBits peelExponent coreExponent)
    (hcheck : budget.coreCheckCost <= inputSize ^ checkExponent) :
    budget.totalCost <=
      inputSize ^ peelExponent +
        inputSize ^ (coreExponent + checkExponent) := by
  calc
    budget.totalCost =
        budget.peelCost + 2 ^ coreBits * budget.coreCheckCost := rfl
    _ <= inputSize ^ peelExponent +
        (inputSize ^ coreExponent) * (inputSize ^ checkExponent) :=
      Nat.add_le_add budget.peelBound
        (Nat.mul_le_mul budget.assignmentsBound hcheck)
    _ = inputSize ^ peelExponent +
        inputSize ^ (coreExponent + checkExponent) := by rw [pow_add]

end A74_SmallCoreBudget

/-! ## 75 - If peeling is cheap, superpolynomial work must remain in the core -/
namespace A75_CoreObstruction

theorem expensive_core_of_total_exceeds
    (inputSize peelCost coreCost peelExponent coreExponent : Nat)
    (hpeel : peelCost <= inputSize ^ peelExponent)
    (hexceeds :
      inputSize ^ peelExponent + inputSize ^ coreExponent <
        peelCost + coreCost) :
    inputSize ^ coreExponent < coreCost := by
  by_contra hnot
  have hcore : coreCost <= inputSize ^ coreExponent := Nat.le_of_not_gt hnot
  have hbound :
      peelCost + coreCost <=
        inputSize ^ peelExponent + inputSize ^ coreExponent :=
    Nat.add_le_add hpeel hcore
  exact (Nat.not_lt_of_ge hbound) hexceeds

end A75_CoreObstruction

end ResearchSixth
end PIsNPOrNot
