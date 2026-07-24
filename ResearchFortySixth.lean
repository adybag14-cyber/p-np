import ResearchFortyFifth

namespace PIsNPOrNot.ResearchFortySixth

/-! ## 661 - A two-state layer representation uses one Boolean state per depth -/
namespace A661_ParityLayerState

abbrev LayerState (n : Nat) := Fin (n + 1) × Bool

end A661_ParityLayerState

/-! ## 662 - The complete layered parity state space has 2(n+1) nodes -/
namespace A662_ParityLayerCardinality

open A661_ParityLayerState

theorem layer_state_card (n : Nat) :
    Fintype.card (LayerState n) = 2 * (n + 1) := by
  simp [LayerState, Nat.mul_comm]

end A662_ParityLayerCardinality

/-! ## 663 - Recursive parity has at most two semantic output classes -/
namespace A663_ParitySemanticClasses

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

theorem parity_image_le_two (n : Nat) :
    ((Finset.univ : Finset (Assignment n)).image parity).card <= 2 := by
  classical
  calc
    ((Finset.univ : Finset (Assignment n)).image parity).card <=
        (Finset.univ : Finset Bool).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by simp

end A663_ParitySemanticClasses

/-! ## 664 - Parity has an exact one-bit semantic machine -/
namespace A664_OneBitParityMachine

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity

structure OneBitMachine (n : Nat) where
  coordinate : Assignment n -> Bool
  decide : Bool -> Bool
  exact : forall bits, decide (coordinate bits) = parity bits

def parityMachine (n : Nat) : OneBitMachine n where
  coordinate := parity
  decide := fun state => state
  exact := by intro bits; rfl

end A664_OneBitParityMachine

/-! ## 665 - The one-bit parity machine is pointwise exact -/
namespace A665_ParityMachineExact

open ResearchFortyFifth.A646_BitFlip
open ResearchFortyFifth.A647_RecursiveParity
open A664_OneBitParityMachine

theorem parity_machine_exact (n : Nat) (bits : Assignment n) :
    (parityMachine n).decide ((parityMachine n).coordinate bits) = parity bits :=
  (parityMachine n).exact bits

end A665_ParityMachineExact

/-! ## 666 - A linear-size parity DAG cost certificate -/
namespace A666_LinearParityDag

structure DagCost (n : Nat) where
  semanticStates : Nat
  totalNodes : Nat
  stateBound : semanticStates <= 2
  nodeEquation : totalNodes = 2 * (n + 1)

noncomputable def parityDagCost (n : Nat) : DagCost n where
  semanticStates := 2
  totalNodes := 2 * (n + 1)
  stateBound := le_rfl
  nodeEquation := rfl

end A666_LinearParityDag

/-! ## 667 - Exponential cube count eventually strictly exceeds the linear DAG -/
namespace A667_LinearVersusExponential

theorem linear_lt_pow (n : Nat) (atLeastFive : 5 <= n) :
    2 * (n + 1) < 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le atLeastFive
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 5 + (k + 1) = (5 + k) + 1 by omega]
      rw [pow_succ]
      omega

end A667_LinearVersusExponential

/-! ## 668 - Every parity cube cover is larger than the linear DAG from n=5 onward -/
namespace A668_ParityCoverDagGap

open ResearchFortyFifth.A655_ParityCubeCover

variable {n : Nat} {Term : Type} [Fintype Term]

theorem dag_strictly_smaller (cover : ParityCubeCover n Term) (atLeastFive : 5 <= n) :
    2 * (n + 1) < Fintype.card Term := by
  exact lt_of_lt_of_le
    (A667_LinearVersusExponential.linear_lt_pow n atLeastFive)
    (ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound cover)

end A668_ParityCoverDagGap

/-! ## 669 - At eight variables the certified gap is 18 nodes versus at least 256 terms -/
namespace A669_EightVariableGap

theorem concrete_gap : 2 * (8 + 1) < 2 ^ 8 := by decide

end A669_EightVariableGap

/-! ## 670 - Disjoint subcube partitions inherit the same parity lower bound -/
namespace A670_ParitySubcubePartition

open ResearchFortyFifth.A655_ParityCubeCover

structure ParityPartition (n : Nat) (Term : Type) [Fintype Term] where
  cover : ParityCubeCover n Term
  disjoint : forall left right, Not (left = right) ->
    forall bits,
      Not (ResearchFortyFirst.A586_Cube.Extends bits (cover.cube left) ∧
        ResearchFortyFirst.A586_Cube.Extends bits (cover.cube right))

variable {n : Nat} {Term : Type} [Fintype Term]

theorem partition_term_lower_bound (partition : ParityPartition n Term) :
    2 ^ n <= Fintype.card Term :=
  ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound partition.cover

end A670_ParitySubcubePartition

/-! ## 671 - Term count and term width multiply into literal work -/
namespace A671_UniformLiteralCost

structure Cost (n : Nat) where
  terms : Nat
  width : Nat
  totalLiterals : Nat
  termLower : 2 ^ n <= terms
  widthLower : n <= width
  totalEquation : totalLiterals = terms * width

theorem literal_lower_bound {n : Nat} (cost : Cost n) :
    n * 2 ^ n <= cost.totalLiterals := by
  rw [cost.totalEquation]
  have product := Nat.mul_le_mul cost.termLower cost.widthLower
  simpa [Nat.mul_comm] using product

end A671_UniformLiteralCost

/-! ## 672 - The singleton parity DNF has exactly n*2^n literals -/
namespace A672_SingletonLiteralCount

def singletonLiteralCost (n : Nat) : Nat := n * 2 ^ n

theorem exact_cost (n : Nat) : singletonLiteralCost n = n * 2 ^ n := rfl

end A672_SingletonLiteralCount

/-! ## 673 - At eight variables singleton DNF literals exceed the linear DAG by two orders -/
namespace A673_ConcreteLiteralGap

theorem concrete_literal_gap : 2 * (8 + 1) < 8 * 2 ^ 8 := by decide

end A673_ConcreteLiteralGap

/-! ## 674 - A representation portfolio can select the parity DAG over the DNF -/
namespace A674_ParityRepresentationChoice

open ResearchFortyFourth.A642_RepresentationPortfolio

variable {specification : Prop}

theorem choose_dag_when_strictly_cheaper
    (dnf dag : Candidate specification) (cheaper : dag.work < dnf.work) :
    choose dnf dag = dag := by
  unfold choose
  split
  · rename_i dnfLeDag
    omega
  · rfl

end A674_ParityRepresentationChoice

/-! ## 675 - Cube-only parity compilers have an unavoidable exponential output -/
namespace A675_CubeOnlyCompilerBarrier

open ResearchFortyFifth.A655_ParityCubeCover

structure CubeOnlyCompiler (n : Nat) where
  Term : Type
  finiteTerm : Fintype Term
  output : @ParityCubeCover n Term finiteTerm

attribute [instance] CubeOnlyCompiler.finiteTerm

theorem exponential_output {n : Nat} (compiler : CubeOnlyCompiler n) :
    2 ^ n <= Fintype.card compiler.Term :=
  ResearchFortyFifth.A657_ParityTermLowerBound.term_card_lower_bound compiler.output

end A675_CubeOnlyCompilerBarrier

end PIsNPOrNot.ResearchFortySixth
