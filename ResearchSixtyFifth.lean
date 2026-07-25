import ResearchSixtyFourth

namespace PIsNPOrNot.ResearchSixtyFifth

/-! ## 946 - Polynomial machine stages are indexed by their time exponent -/
namespace A946_PolynomialStage

def cost (inputSize exponent : Nat) : Nat := inputSize ^ exponent

end A946_PolynomialStage

/-! ## 947 - At base two, increasing the exponent strictly increases cost -/
namespace A947_ExponentGrowth

theorem strict_step (k : Nat) : 2 ^ k < 2 ^ (k + 1) := by
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k)

end A947_ExponentGrowth

/-! ## 948 - No fixed exponent bounds every polynomial exponent even at input size two -/
namespace A948_NoUniformExponent

theorem no_fixed_exponent (k : Nat) :
    Not (forall exponent, 2 ^ exponent <= 2 ^ k) := by
  intro uniform
  have impossible := uniform (k + 1)
  exact (Nat.not_le_of_gt (A947_ExponentGrowth.strict_step k)) impossible

end A948_NoUniformExponent

/-! ## 949 - A diagonal simulation inherits the exponent of the machine it attacks -/
namespace A949_DiagonalSimulation

structure Stage where
  machineIndex : Nat
  machineExponent : Nat
  inputSize : Nat

def simulationCost (stage : Stage) : Nat :=
  stage.inputSize ^ stage.machineExponent

end A949_DiagonalSimulation

/-! ## 950 - Simulating machine i for n^i steps has a variable exponent -/
namespace A950_IndexAsExponent

open A949_DiagonalSimulation

def stage (machineIndex inputSize : Nat) : Stage where
  machineIndex := machineIndex
  machineExponent := machineIndex
  inputSize := inputSize

theorem cost_formula (machineIndex inputSize : Nat) :
    simulationCost (stage machineIndex inputSize) =
      inputSize ^ machineIndex := rfl

end A950_IndexAsExponent

/-! ## 951 - The indexed diagonal simulator has no single polynomial exponent -/
namespace A951_DiagonalExponentObstruction

theorem no_uniform_bound (k : Nat) :
    Not (forall machineIndex,
      A949_DiagonalSimulation.simulationCost
        (A950_IndexAsExponent.stage machineIndex 2) <= 2 ^ k) := by
  simpa [A949_DiagonalSimulation.simulationCost,
    A950_IndexAsExponent.stage] using A948_NoUniformExponent.no_fixed_exponent k

end A951_DiagonalExponentObstruction

/-! ## 952 - Capping the simulated exponent yields a uniform polynomial verifier -/
namespace A952_CappedDiagonal

structure Plan where
  exponentCap : Nat
  verifierExponent : Nat
  coveredMachineExponent : Nat -> Prop

def capped (cap : Nat) : Plan where
  exponentCap := cap
  verifierExponent := cap
  coveredMachineExponent := fun exponent => exponent <= cap

end A952_CappedDiagonal

/-! ## 953 - A finite exponent cap misses the next polynomial-time stage -/
namespace A953_CapMissesNextStage

theorem next_not_covered (cap : Nat) :
    Not ((A952_CappedDiagonal.capped cap).coveredMachineExponent (cap + 1)) := by
  simp [A952_CappedDiagonal.capped]

end A953_CapMissesNextStage

/-! ## 954 - Covering every polynomial exponent forces an unbounded verifier exponent -/
namespace A954_UniversalCoverageObstruction

structure Coverage where
  verifierExponent : Nat
  covers : Nat -> Prop
  sound : forall exponent, covers exponent -> exponent <= verifierExponent

theorem cannot_cover_all (coverage : Coverage) :
    Not (forall exponent, coverage.covers exponent) := by
  intro allCovered
  have nextCovered := allCovered (coverage.verifierExponent + 1)
  have impossible := coverage.sound _ nextCovered
  omega

end A954_UniversalCoverageObstruction

/-! ## 955 - Encoding the machine exponent in the input does not make it constant -/
namespace A955_EncodedExponent

structure EncodedInstance where
  dataLength : Nat
  machineExponent : Nat

def universalSimulationCost (encoded : EncodedInstance) : Nat :=
  encoded.dataLength ^ encoded.machineExponent

theorem exponent_remains_input_dependent (length exponent : Nat) :
    universalSimulationCost {
      dataLength := length
      machineExponent := exponent } = length ^ exponent := rfl

end A955_EncodedExponent

/-! ## 956 - Variable-exponent universal simulation is not bounded by any fixed power -/
namespace A956_UniversalVerifierFailure

theorem no_fixed_power (k : Nat) :
    Not (forall exponent,
      A955_EncodedExponent.universalSimulationCost {
        dataLength := 2
        machineExponent := exponent } <= 2 ^ k) := by
  simpa [A955_EncodedExponent.universalSimulationCost] using
    A948_NoUniformExponent.no_fixed_exponent k

end A956_UniversalVerifierFailure

/-! ## 957 - Padding each stage by its simulation cost makes that stage linear -/
namespace A957_StageSpecificPadding

structure PaddedStage where
  originalInputSize : Nat
  machineExponent : Nat
  paddedLength : Nat
  simulationCost : Nat

def padToRuntime (inputSize exponent : Nat) : PaddedStage where
  originalInputSize := inputSize
  machineExponent := exponent
  paddedLength := inputSize ^ exponent
  simulationCost := inputSize ^ exponent

theorem simulation_linear_in_padding (inputSize exponent : Nat) :
    (padToRuntime inputSize exponent).simulationCost =
      (padToRuntime inputSize exponent).paddedLength := rfl

end A957_StageSpecificPadding

/-! ## 958 - Stage-specific padding therefore erases the intended deterministic lower bound -/
namespace A958_DiagonalPaddingTrap

theorem padded_simulation_degree_one (inputSize exponent : Nat) :
    (A957_StageSpecificPadding.padToRuntime inputSize exponent).simulationCost <=
      (A957_StageSpecificPadding.padToRuntime inputSize exponent).paddedLength ^ 1 := by
  simp [A957_StageSpecificPadding.padToRuntime]

end A958_DiagonalPaddingTrap

/-! ## 959 - Direct diagonalisation faces an exponent-or-padding dilemma -/
namespace A959_DiagonalDilemma

structure Attempt where
  fixedVerifierExponent : Option Nat
  coversEveryPolynomialExponent : Bool
  paddingAbsorbsSimulation : Bool

def unpaddedUniversal : Attempt where
  fixedVerifierExponent := none
  coversEveryPolynomialExponent := true
  paddingAbsorbsSimulation := false

def paddedUniversal (exponent : Nat) : Attempt where
  fixedVerifierExponent := some exponent
  coversEveryPolynomialExponent := true
  paddingAbsorbsSimulation := true

theorem unpadded_has_no_fixed_exponent :
    unpaddedUniversal.fixedVerifierExponent = none := rfl

theorem padded_absorbs (exponent : Nat) :
    (paddedUniversal exponent).paddingAbsorbsSimulation = true := rfl

end A959_DiagonalDilemma

/-! ## 960 - A successful NP diagonal language needs fixed verification and universal disagreement -/
namespace A960_SeparationDiagonalCriterion

structure Criterion where
  verifierExponent : Nat
  disagreesWithExponent : Nat -> Prop
  universalDisagreement : forall exponent, disagreesWithExponent exponent
  verificationBound : Nat -> Nat
  fixedBound : forall inputSize,
    verificationBound inputSize <= inputSize ^ verifierExponent

theorem next_stage_must_also_disagree (criterion : Criterion) :
    criterion.disagreesWithExponent (criterion.verifierExponent + 1) :=
  criterion.universalDisagreement _

end A960_SeparationDiagonalCriterion

end PIsNPOrNot.ResearchSixtyFifth
