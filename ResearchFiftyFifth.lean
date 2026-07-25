import ResearchFiftyFourth

namespace PIsNPOrNot.ResearchFiftyFifth

/-! ## 796 - A modular stream step adds the current Boolean edge value -/
namespace A796_ModularStep

open ResearchFiftyFourth.A781_ModularBitValue

def step {m : Nat} (state : ZMod (m + 2)) (bit : Bool) : ZMod (m + 2) :=
  state + bitValue (m := m) bit

end A796_ModularStep

/-! ## 797 - Modular stream execution threads one cyclic state through a bit list -/
namespace A797_ModularRun

open A796_ModularStep

def run {m : Nat} : ZMod (m + 2) -> List Bool -> ZMod (m + 2)
  | state, [] => state
  | state, bit :: tail => run (step state bit) tail

end A797_ModularRun

/-! ## 798 - Stream execution equals the initial state plus the list sum -/
namespace A798_RunAsSum

open ResearchFiftyFourth.A781_ModularBitValue
open A796_ModularStep
open A797_ModularRun

theorem run_eq_state_add_sum {m : Nat}
    (state : ZMod (m + 2)) (bits : List Bool) :
    run state bits = state + (bits.map (bitValue (m := m))).sum := by
  induction bits generalizing state with
  | nil => simp [run]
  | cons bit tail ih =>
      rw [run, ih]
      simp [step]
      abel

end A798_RunAsSum

/-! ## 799 - Running from zero computes the mapped list sum exactly -/
namespace A799_RunFromZero

open ResearchFiftyFourth.A781_ModularBitValue
open A797_ModularRun

theorem run_zero_eq_sum {m : Nat} (bits : List Bool) :
    run (0 : ZMod (m + 2)) bits =
      (bits.map (ResearchFiftyFourth.A781_ModularBitValue.bitValue (m := m))).sum := by
  simpa using A798_RunAsSum.run_eq_state_add_sum (m := m) 0 bits

end A799_RunFromZero

/-! ## 800 - Finite-vector streaming agrees with the modular population sum -/
namespace A800_StreamSumExact

open ResearchFortyFifth.A646_BitFlip
open ResearchFiftyFourth.A781_ModularBitValue
open ResearchFiftyFourth.A782_ModularSum
open A797_ModularRun

def streamSum {m n : Nat} (bits : Assignment n) : ZMod (m + 2) :=
  run 0 (List.ofFn bits)

theorem stream_eq_modSum {m n : Nat} (bits : Assignment n) :
    streamSum (m := m) bits = modSum (m := m) bits := by
  unfold streamSum
  rw [A799_RunFromZero.run_zero_eq_sum]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

end A800_StreamSumExact

/-! ## 801 - The modular stream maintains exactly one edge label as its state -/
namespace A801_OneLabelState

structure StateProfile (m : Nat) where
  stateCard : Nat
  stateEquation : stateCard = m + 2

noncomputable def profile (m : Nat) : StateProfile m where
  stateCard := m + 2
  stateEquation := rfl

end A801_OneLabelState

/-! ## 802 - One physical decision node per variable plus one terminal is linear -/
namespace A802_EdgeLabelledNodeCount

def physicalNodes (n : Nat) : Nat := n + 1

theorem physical_node_formula (n : Nat) : physicalNodes n = n + 1 := rfl

end A802_EdgeLabelledNodeCount

/-! ## 803 - An explicit-state layered diagram stores every modular state per layer -/
namespace A803_ExplicitStateNodeCount

def explicitNodes (m n : Nat) : Nat := (m + 2) * n + 1

theorem explicit_node_formula (m n : Nat) :
    explicitNodes m n = (m + 2) * n + 1 := rfl

end A803_ExplicitStateNodeCount

/-! ## 804 - Edge labels save (m+1)n physical nodes over explicit states -/
namespace A804_EdgeLabelSaving

def saving (m n : Nat) : Nat :=
  A803_ExplicitStateNodeCount.explicitNodes m n -
    A802_EdgeLabelledNodeCount.physicalNodes n

theorem saving_eq (m n : Nat) : saving m n = (m + 1) * n := by
  unfold saving A803_ExplicitStateNodeCount.explicitNodes
    A802_EdgeLabelledNodeCount.physicalNodes
  rw [show (m + 2) * n + 1 = (m + 1) * n + (n + 1) by ring]
  exact Nat.add_sub_cancel_right ((m + 1) * n) (n + 1)

end A804_EdgeLabelSaving

/-! ## 805 - The edge-labelled modular stream has n+1 physical nodes -/
namespace A805_ModularStreamCertificate

open ResearchFortyFifth.A646_BitFlip
open ResearchFiftyFourth.A782_ModularSum

structure Certificate (m n : Nat) where
  evaluate : Assignment n -> ZMod (m + 2)
  physicalNodes : Nat
  exact : forall bits, evaluate bits = modSum (m := m) bits
  nodeEquation : physicalNodes = n + 1

noncomputable def certificate (m n : Nat) : Certificate m n where
  evaluate := A800_StreamSumExact.streamSum
  physicalNodes := n + 1
  exact := A800_StreamSumExact.stream_eq_modSum
  nodeEquation := rfl

end A805_ModularStreamCertificate

/-! ## 806 - Linear edge-labelled size beats the exponential cube lower bound -/
namespace A806_ModularStreamCubeGap

open ResearchFiftyFourth.A792_ModularCubeCover

variable {m n : Nat} {Term : Type} [Fintype Term]

theorem physical_nodes_lt_terms
    (atLeastTwo : 2 <= n) (cover : ModularCubeCover m n Term) :
    A802_EdgeLabelledNodeCount.physicalNodes n < Fintype.card Term := by
  apply lt_of_lt_of_le
    (ResearchFiftieth.A731_ComplementedVersusCubeGrowth.complemented_lt_pow
      n atLeastTwo)
  exact ResearchFiftyFourth.A794_ModularTermLowerBound.term_card_lower_bound cover

end A806_ModularStreamCubeGap

/-! ## 807 - The modular output state set has exactly m+2 labels -/
namespace A807_ModularLabelCardinality

theorem label_card (m : Nat) : Fintype.card (ZMod (m + 2)) = m + 2 := by
  exact ZMod.card (m + 2)

end A807_ModularLabelCardinality

/-! ## 808 - Semantic states factor as one physical base times m+2 labels -/
namespace A808_ModularFactorization

theorem exact_factorization (m : Nat) :
    Fintype.card (ZMod (m + 2)) =
      Fintype.card Unit * Fintype.card (ZMod (m + 2)) := by
  simp

end A808_ModularFactorization

/-! ## 809 - Modular representation profiles separate semantic, physical, and cube costs -/
namespace A809_ModularRepresentationProfile

structure Profile where
  inputBits : Nat
  modulus : Nat
  semanticStates : Nat
  physicalNodes : Nat
  cubeLowerBound : Nat
  semanticEquation : semanticStates = modulus
  physicalEquation : physicalNodes = inputBits + 1
  cubeEquation : cubeLowerBound = 2 ^ inputBits

noncomputable def profile (m n : Nat) : Profile where
  inputBits := n
  modulus := m + 2
  semanticStates := m + 2
  physicalNodes := n + 1
  cubeLowerBound := 2 ^ n
  semanticEquation := rfl
  physicalEquation := rfl
  cubeEquation := rfl

end A809_ModularRepresentationProfile

/-! ## 810 - Uniform polynomial edge-labelled stream compilers would imply P = NP -/
namespace A810_EdgeLabelledStreamCollapse

variable {Language : Type}

structure UniformStreamCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_stream_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformStreamCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A810_EdgeLabelledStreamCollapse

end PIsNPOrNot.ResearchFiftyFifth
