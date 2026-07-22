import ResearchNinth

/-!
# Approaches 121-135: an acceptable ordered-residual proof skeleton

A successful proof through this route must provide a uniform compiler producing
an exact deterministic witness machine, polynomial witness length, polynomially
many states, and polynomial construction cost.  None of the structures below
contains a field merely asserting that the target language is already in P.
-/

namespace PIsNPOrNot
namespace ResearchTenth

open A15_ResidualAutomaton
open Synthesis_ResidualCompression

/-! ## 121 - Exact ordered witness machines -/
namespace A121_OrderedMachine

structure OrderedMachine (relation : List Bool -> Bool) (witnessLength : Nat) where
  State : Type
  decEqState : DecidableEq State
  finiteState : Fintype State
  start : State
  step : State -> Bool -> State
  accept : State -> Bool
  exact : forall witness,
    witness.length = witnessLength ->
      relation witness = accept (runR step start witness)

noncomputable def stateCount
    {relation : List Bool -> Bool} {witnessLength : Nat}
    (machine : OrderedMachine relation witnessLength) : Nat := by
  letI : Fintype machine.State := machine.finiteState
  exact Fintype.card machine.State

end A121_OrderedMachine

/-! ## 122 - Every fixed witness is evaluated exactly -/
namespace A122_PathCorrectness

open A121_OrderedMachine

theorem evaluate_witness
    {relation : List Bool -> Bool} {witnessLength : Nat}
    (machine : OrderedMachine relation witnessLength)
    (witness : List Bool) (hLength : witness.length = witnessLength) :
    relation witness =
      machine.accept (runR machine.step machine.start witness) :=
  machine.exact witness hLength

end A122_PathCorrectness

/-! ## 123 - Ordered machines induce residual models -/
namespace A123_ToResidualModel

open A121_OrderedMachine

noncomputable def toResidualModel
    {relation : List Bool -> Bool} {witnessLength : Nat}
    (machine : OrderedMachine relation witnessLength) :
    ResidualModel relation witnessLength := by
  letI : Fintype machine.State := machine.finiteState
  exact {
    State := machine.State
    decEqState := machine.decEqState
    finiteState := machine.finiteState
    step := machine.step
    start := machine.start
    accept := machine.accept
    stateBudget := Fintype.card machine.State
    card_le_budget := le_rfl
    correct := machine.exact
  }

end A123_ToResidualModel

/-! ## 124 - The machine decides existential witness acceptance -/
namespace A124_ExistentialDecision

open A121_OrderedMachine A123_ToResidualModel

noncomputable def decide
    {relation : List Bool -> Bool} {witnessLength : Nat}
    (machine : OrderedMachine relation witnessLength) : Bool :=
  (toResidualModel machine).decide

theorem decide_correct
    {relation : List Bool -> Bool} {witnessLength : Nat}
    (machine : OrderedMachine relation witnessLength) :
    decide machine = true <->
      exists witness : List Bool,
        witness.length = witnessLength /\ relation witness = true := by
  exact ResidualModel.decide_correct (toResidualModel machine)

end A124_ExistentialDecision

/-! ## 125 - Every reachable layer is bounded by the state type -/
namespace A125_LayerWidth

open A121_OrderedMachine

theorem reachable_layer_bound
    {relation : List Bool -> Bool} {witnessLength layer : Nat}
    (machine : OrderedMachine relation witnessLength) :
    letI : DecidableEq machine.State := machine.decEqState
    (reachable machine.step machine.start layer).card <=
      stateCount machine := by
  letI : DecidableEq machine.State := machine.decEqState
  letI : Fintype machine.State := machine.finiteState
  unfold stateCount
  exact reachable_state_bound machine.step machine.start layer

end A125_LayerWidth

/-! ## 126 - Layer-by-layer work accounting -/
namespace A126_LayerWork

def layerWork (depth stateCount : Nat) : Nat :=
  (depth + 1) * stateCount

theorem layerWork_zero (stateCount : Nat) :
    layerWork 0 stateCount = stateCount := by
  simp [layerWork]

theorem layerWork_mono
    {depthA depthB statesA statesB : Nat}
    (hDepth : depthA <= depthB) (hStates : statesA <= statesB) :
    layerWork depthA statesA <= layerWork depthB statesB := by
  unfold layerWork
  exact Nat.mul_le_mul (Nat.add_le_add_right hDepth 1) hStates

end A126_LayerWork

/-! ## 127 - Polynomial depth and width give a polynomial work expression -/
namespace A127_PolynomialLayerBudget

open A126_LayerWork

theorem polynomial_layer_bound
    (depth stateCount inputSize exponent : Nat)
    (hDepth : depth <= inputSize)
    (hStates : stateCount <= inputSize ^ exponent) :
    layerWork depth stateCount <=
      (inputSize + 1) * (inputSize ^ exponent) := by
  exact layerWork_mono hDepth hStates

end A127_PolynomialLayerBudget

/-! ## 128 - Uniform compiled witness families -/
namespace A128_CompiledFamily

open A121_OrderedMachine

structure CompiledFamily (Instance : Type) where
  relation : Instance -> List Bool -> Bool
  witnessLength : Instance -> Nat
  machine : forall input,
    OrderedMachine (relation input) (witnessLength input)
  inputSize : Instance -> Nat
  stateExponent : Nat
  constructionExponent : Nat
  witness_length_bound : forall input,
    witnessLength input <= inputSize input
  state_bound : forall input,
    stateCount (machine input) <= inputSize input ^ stateExponent
  constructionCost : Instance -> Nat
  construction_bound : forall input,
    constructionCost input <= inputSize input ^ constructionExponent

end A128_CompiledFamily

/-! ## 129 - The compiled family defines its language without circularity -/
namespace A129_CompiledLanguage

open A128_CompiledFamily

def CompiledAccepts {Instance : Type}
    (compiler : CompiledFamily Instance) (input : Instance) : Prop :=
  exists witness : List Bool,
    witness.length = compiler.witnessLength input /\
      compiler.relation input witness = true

end A129_CompiledLanguage

/-! ## 130 - The compiled family has an exact decider -/
namespace A130_CompiledDecision

open A124_ExistentialDecision A128_CompiledFamily A129_CompiledLanguage

noncomputable def compiledDecide
    {Instance : Type} (compiler : CompiledFamily Instance)
    (input : Instance) : Bool :=
  decide (compiler.machine input)

theorem compiledDecide_correct
    {Instance : Type} (compiler : CompiledFamily Instance)
    (input : Instance) :
    compiledDecide compiler input = true <->
      CompiledAccepts compiler input := by
  exact decide_correct (compiler.machine input)

end A130_CompiledDecision

/-! ## 131 - The reachable-state work has an explicit polynomial bound -/
namespace A131_CompiledWorkBound

open A121_OrderedMachine A126_LayerWork
open A127_PolynomialLayerBudget A128_CompiledFamily

theorem compiled_layer_work_bound
    {Instance : Type} (compiler : CompiledFamily Instance)
    (input : Instance) :
    layerWork
        (compiler.witnessLength input)
        (stateCount (compiler.machine input)) <=
      (compiler.inputSize input + 1) *
        (compiler.inputSize input ^ compiler.stateExponent) := by
  exact polynomial_layer_bound
    (compiler.witnessLength input)
    (stateCount (compiler.machine input))
    (compiler.inputSize input)
    compiler.stateExponent
    (compiler.witness_length_bound input)
    (compiler.state_bound input)

end A131_CompiledWorkBound

/-! ## 132 - Construction and traversal costs remain separately visible -/
namespace A132_TotalCertifiedCost

open A121_OrderedMachine A126_LayerWork A128_CompiledFamily

noncomputable def totalCertifiedCost {Instance : Type}
    (compiler : CompiledFamily Instance) (input : Instance) : Nat :=
  compiler.constructionCost input +
    layerWork
      (compiler.witnessLength input)
      (stateCount (compiler.machine input))

theorem total_cost_bound
    {Instance : Type} (compiler : CompiledFamily Instance)
    (input : Instance) :
    totalCertifiedCost compiler input <=
      compiler.inputSize input ^ compiler.constructionExponent +
      (compiler.inputSize input + 1) *
        (compiler.inputSize input ^ compiler.stateExponent) := by
  unfold totalCertifiedCost
  exact Nat.add_le_add
    (compiler.construction_bound input)
    (A131_CompiledWorkBound.compiled_layer_work_bound compiler input)

end A132_TotalCertifiedCost

/-! ## 133 - A machine-model bridge turns the compiler into membership in P -/
namespace A133_MachineBridge

open A128_CompiledFamily A129_CompiledLanguage

variable {Language Instance : Type}

structure LanguageCompiler
    (Encodes : Language -> Instance -> Prop) where
  compiler : Language -> CompiledFamily Instance
  agrees : forall language input,
    Encodes language input <-> CompiledAccepts (compiler language) input

theorem languages_in_p_of_compiler_bridge
    (InP : Language -> Prop) (Encodes : Language -> Instance -> Prop)
    (family : LanguageCompiler (Instance := Instance) Encodes)
    (compiledImpliesP : forall language (compiler : CompiledFamily Instance),
      (forall input,
        Encodes language input <-> CompiledAccepts compiler input) ->
      InP language) :
    forall language, InP language := by
  intro language
  exact compiledImpliesP language (family.compiler language)
    (family.agrees language)

end A133_MachineBridge

/-! ## 134 - A uniform compiler for NP languages yields P = NP -/
namespace A134_CollapseCriterion

open A128_CompiledFamily A129_CompiledLanguage

variable {Language Instance : Type}

structure UniformNPCompiler
    (InNP : Language -> Prop)
    (Encodes : Language -> Instance -> Prop) where
  compile : forall language, InNP language -> CompiledFamily Instance
  agrees : forall language (hNP : InNP language) input,
    Encodes language input <->
      CompiledAccepts (compile language hNP) input

theorem p_eq_np_of_uniform_compiler
    (InP InNP : Language -> Prop)
    (Encodes : Language -> Instance -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (family : UniformNPCompiler (Instance := Instance) InNP Encodes)
    (compiledImpliesP : forall language (compiler : CompiledFamily Instance),
      (forall input,
        Encodes language input <-> CompiledAccepts compiler input) ->
      InP language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compiledImpliesP language (family.compile language hNP)
      (family.agrees language hNP)

end A134_CollapseCriterion

/-! ## 135 - Failure of the collapse localizes to a compiler obligation -/
namespace A135_CompilerObstruction

open A128_CompiledFamily A129_CompiledLanguage

variable {Language Instance : Type}

theorem compiler_obstruction_of_separation
    (InP InNP : Language -> Prop)
    (Encodes : Language -> Instance -> Prop)
    (separated : Not ({language | InP language} = {language | InNP language}))
    (p_subset_np : forall language, InP language -> InNP language)
    (compiledImpliesP : forall language (compiler : CompiledFamily Instance),
      (forall input,
        Encodes language input <-> CompiledAccepts compiler input) ->
      InP language) :
    exists language,
      InNP language /\
      forall compiler : CompiledFamily Instance,
        Not (forall input,
          Encodes language input <-> CompiledAccepts compiler input) := by
  by_contra hnone
  push Not at hnone
  have np_subset_p : forall language, InNP language -> InP language := by
    intro language hNP
    rcases hnone language hNP with ⟨compiler, agrees⟩
    exact compiledImpliesP language compiler agrees
  apply separated
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact np_subset_p language hNP

end A135_CompilerObstruction

end ResearchTenth
end PIsNPOrNot
