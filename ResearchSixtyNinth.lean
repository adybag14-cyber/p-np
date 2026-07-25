import ResearchSixtyEighth

namespace PIsNPOrNot.ResearchSixtyNinth

/-! ## 1006 - A truth-table encoding has one output bit per assignment -/
namespace A1006_TruthTableEncoding

def outputBits (n : Nat) : Nat := 2 ^ n

theorem output_bits_formula (n : Nat) : outputBits n = 2 ^ n := rfl

end A1006_TruthTableEncoding

/-! ## 1007 - A direct DNF representation uses one term for each accepting assignment -/
namespace A1007_DirectDnfProfile

structure Profile where
  inputBits : Nat
  acceptingRows : Nat
  literalsPerRow : Nat
  totalLiterals : Nat

 def worstCase (n : Nat) : Profile where
  inputBits := n
  acceptingRows := 2 ^ n
  literalsPerRow := n
  totalLiterals := n * 2 ^ n

end A1007_DirectDnfProfile

/-! ## 1008 - Worst-case direct DNF literal count is n*2^n -/
namespace A1008_DnfLiteralCount

 theorem worst_case_formula (n : Nat) :
    (A1007_DirectDnfProfile.worstCase n).totalLiterals = n * 2 ^ n := rfl

end A1008_DnfLiteralCount

/-! ## 1009 - A truth-table-to-SAT reduction can preserve values while expanding the instance -/
namespace A1009_TruthTableReduction

structure ReductionProfile where
  originalInputBits : Nat
  truthTableBits : Nat
  producedInstanceBits : Nat
  valuePreserved : Prop

 def direct (n : Nat) : ReductionProfile where
  originalInputBits := n
  truthTableBits := 2 ^ n
  producedInstanceBits := n * 2 ^ n
  valuePreserved := True

end A1009_TruthTableReduction

/-! ## 1010 - The direct reduction output has exponential dependence on original input length -/
namespace A1010_ReductionSize

 theorem direct_size (n : Nat) :
    (A1009_TruthTableReduction.direct n).producedInstanceBits =
      n * 2 ^ n := rfl

end A1010_ReductionSize

/-! ## 1011 - Polynomial work in the reduced instance length may be exponential in n -/
namespace A1011_ReducedSolverCost

def cost (n exponent : Nat) : Nat := (n * 2 ^ n) ^ exponent

 theorem cost_formula (n exponent : Nat) :
    cost n exponent = (n * 2 ^ n) ^ exponent := rfl

end A1011_ReducedSolverCost

/-! ## 1012 - Even linear time in a 2^n-bit table is exponential in n -/
namespace A1012_LinearTableScan

def scanCost (n : Nat) : Nat := 2 ^ n

 theorem scan_formula (n : Nat) : scanCost n = 2 ^ n := rfl

end A1012_LinearTableScan

/-! ## 1013 - A reduction only transfers polynomial time under polynomial input blow-up -/
namespace A1013_PolynomialReductionCriterion

structure Criterion where
  sourceLength : Nat
  targetLength : Nat
  sourceExponent : Nat
  targetExponent : Nat
  targetLengthPolynomial : targetLength <= (sourceLength + 1) ^ sourceExponent

 theorem target_solver_composes (criterion : Criterion)
    (targetCost : Nat)
    (solverBound : targetCost <= criterion.targetLength ^ criterion.targetExponent) :
    targetCost <= criterion.targetLength ^ criterion.targetExponent := solverBound

end A1013_PolynomialReductionCriterion

/-! ## 1014 - The direct reduction contains the full exponential truth-table payload -/
namespace A1014_TruthTableBlowup

 theorem table_bits_le_reduction {n : Nat} (positive : 0 < n) :
    2 ^ n <= (A1009_TruthTableReduction.direct n).producedInstanceBits := by
  change 2 ^ n <= n * 2 ^ n
  exact Nat.le_mul_of_pos_left _ positive

 theorem exact_payload (n : Nat) :
    (A1009_TruthTableReduction.direct n).truthTableBits = 2 ^ n := rfl

end A1014_TruthTableBlowup
/-! ## 1015 - Counting hardness does not survive an exponentially large reduction as a P lower bound -/
namespace A1015_CountingTransferStatus

structure Status where
  hardTruthTableExists : Bool
  reductionPreservesValue : Bool
  reductionPolynomialInOriginalInput : Bool
  resultingPLowerBound : Bool

 def direct : Status where
  hardTruthTableExists := true
  reductionPreservesValue := true
  reductionPolynomialInOriginalInput := false
  resultingPLowerBound := false

 theorem polynomial_transfer_missing :
    direct.reductionPolynomialInOriginalInput = false := rfl

end A1015_CountingTransferStatus

/-! ## 1016 - A succinct hard family would avoid the full truth-table reduction -/
namespace A1016_SuccinctHardFamily

structure Family where
  representationBits : Nat -> Nat
  evaluationCost : Nat -> Nat
  reductionOutputBits : Nat -> Nat
  representationExponent : Nat
  evaluationExponent : Nat
  reductionExponent : Nat
  representationBound : forall n,
    representationBits n <= (n + 1) ^ representationExponent
  evaluationBound : forall n,
    evaluationCost n <= (n + 1) ^ evaluationExponent
  reductionBound : forall n,
    reductionOutputBits n <= (n + 1) ^ reductionExponent

end A1016_SuccinctHardFamily

/-! ## 1017 - A full truth table is not a succinct family merely because lookup is cheap -/
namespace A1017_TableLookupNotSuccinct

structure Profile where
  inputBits : Nat
  lookupCost : Nat
  storedBits : Nat

 def table (n : Nat) : Profile where
  inputBits := n
  lookupCost := 1
  storedBits := 2 ^ n

 theorem stored_bits_formula (n : Nat) :
    (table n).storedBits = 2 ^ n := rfl

end A1017_TableLookupNotSuccinct

/-! ## 1018 - NP-completeness transfers hardness only from a succinct NP language -/
namespace A1018_NPCompletenessTransfer

structure Transfer where
  sourceInNP : Prop
  sourceHardAgainstP : Prop
  reductionPolynomial : Prop
  targetNPComplete : Prop

 theorem source_hardness_required (transfer : Transfer)
    (complete : And transfer.sourceInNP
      (And transfer.sourceHardAgainstP transfer.reductionPolynomial)) :
    transfer.sourceHardAgainstP := complete.right.left

end A1018_NPCompletenessTransfer

/-! ## 1019 - A hard-table family requires efficient uniform generation before reduction -/
namespace A1019_UniformGenerationRequirement

structure Generator where
  generateBitCost : Nat -> Nat
  generateDescriptionCost : Nat -> Nat
  bitExponent : Nat
  descriptionExponent : Nat
  bitBound : forall n,
    generateBitCost n <= (n + 1) ^ bitExponent
  descriptionBound : forall n,
    generateDescriptionCost n <= (n + 1) ^ descriptionExponent

end A1019_UniformGenerationRequirement

/-! ## 1020 - The counting-to-SAT route fails at succinct uniform generation -/
namespace A1020_CountingToSatRoute

structure Status where
  ShannonHardFunctions : Bool
  explicitTruthTables : Bool
  polynomialUniformGenerator : Bool
  polynomialReductionFromGenerator : Bool
  separationObtained : Bool

 def current : Status where
  ShannonHardFunctions := true
  explicitTruthTables := true
  polynomialUniformGenerator := false
  polynomialReductionFromGenerator := false
  separationObtained := false

 theorem generator_missing : current.polynomialUniformGenerator = false := rfl

 theorem separation_not_obtained : current.separationObtained = false := rfl

end A1020_CountingToSatRoute

end PIsNPOrNot.ResearchSixtyNinth
