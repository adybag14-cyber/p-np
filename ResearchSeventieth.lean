import ResearchSixtyNinth

namespace PIsNPOrNot.ResearchSeventieth

/-! ## 1021 - A proof system has a checker, proof lengths, and checking costs -/
namespace A1021_ProofSystem

structure System (Statement Proof : Type) where
  check : Statement -> Proof -> Bool
  proofBits : Proof -> Nat
  checkCost : Statement -> Proof -> Nat

end A1021_ProofSystem

/-! ## 1022 - Soundness means every accepted proof establishes a true statement -/
namespace A1022_ProofSoundness

def Sound {Statement Proof : Type}
    (truth : Statement -> Prop)
    (system : A1021_ProofSystem.System Statement Proof) : Prop :=
  forall statement proof,
    system.check statement proof = true -> truth statement

end A1022_ProofSoundness

/-! ## 1023 - Completeness means every true statement has an accepted proof -/
namespace A1023_ProofCompleteness

def Complete {Statement Proof : Type}
    (truth : Statement -> Prop)
    (system : A1021_ProofSystem.System Statement Proof) : Prop :=
  forall statement, truth statement ->
    Exists fun proof => system.check statement proof = true

end A1023_ProofCompleteness

/-! ## 1024 - Polynomial boundedness charges both proof length and verification time -/
namespace A1024_PolynomiallyBounded

structure Certificate {Statement Proof : Type}
    (truth : Statement -> Prop)
    (system : A1021_ProofSystem.System Statement Proof)
    (statementBits : Statement -> Nat) where
  proofExponent : Nat
  checkExponent : Nat
  complete : forall statement, truth statement ->
    Exists fun proof =>
      And (system.check statement proof = true)
        (And (system.proofBits proof <=
          (statementBits statement + 1) ^ proofExponent)
          (system.checkCost statement proof <=
            (statementBits statement + 1) ^ checkExponent))

end A1024_PolynomiallyBounded

/-! ## 1025 - A lower bound for one proof system quantifies only over its accepted proofs -/
namespace A1025_SystemSpecificLowerBound

def RequiresMoreThan {Statement Proof : Type}
    (system : A1021_ProofSystem.System Statement Proof)
    (statement : Statement) (bound : Nat) : Prop :=
  forall proof, system.check statement proof = true ->
    bound < system.proofBits proof

end A1025_SystemSpecificLowerBound

/-! ## 1026 - A system-specific lower bound immediately excludes short proofs in that system -/
namespace A1026_NoShortRestrictedProof

 theorem no_short_proof {Statement Proof : Type}
    (system : A1021_ProofSystem.System Statement Proof)
    (statement : Statement) (bound : Nat)
    (lower : A1025_SystemSpecificLowerBound.RequiresMoreThan
      system statement bound)
    (proof : Proof) (accepted : system.check statement proof = true) :
    Not (system.proofBits proof <= bound) := by
  exact Nat.not_le_of_gt (lower proof accepted)

end A1026_NoShortRestrictedProof

/-! ## 1027 - Another proof system may assign a different proof length to the same statement -/
namespace A1027_SystemDependence

structure Comparison where
  statementBits : Nat
  restrictedProofBits : Nat
  alternativeProofBits : Nat

 def profile (n : Nat) : Comparison where
  statementBits := n
  restrictedProofBits := 2 ^ n
  alternativeProofBits := n

 theorem alternative_shorter (n : Nat) :
    (profile n).alternativeProofBits < (profile n).restrictedProofBits := by
  simpa [profile] using (Nat.lt_pow_self Nat.one_lt_two : n < 2 ^ n)

end A1027_SystemDependence

/-! ## 1028 - Transferring lower bounds requires a proof simulation between systems -/
namespace A1028_ProofSimulation

structure Simulation {Statement RestrictedProof GeneralProof : Type}
    (restricted : A1021_ProofSystem.System Statement RestrictedProof)
    (general : A1021_ProofSystem.System Statement GeneralProof) where
  translate : Statement -> GeneralProof -> RestrictedProof
  acceptance : forall statement proof,
    general.check statement proof = true ->
      restricted.check statement (translate statement proof) = true
  overhead : Nat
  sizeBound : forall statement proof,
    restricted.proofBits (translate statement proof) <=
      general.proofBits proof + overhead

end A1028_ProofSimulation

/-! ## 1029 - A simulation transports accepted general proofs into the restricted system -/
namespace A1029_SimulationSoundness

 theorem accepted_translation {Statement RestrictedProof GeneralProof : Type}
    {restricted : A1021_ProofSystem.System Statement RestrictedProof}
    {general : A1021_ProofSystem.System Statement GeneralProof}
    (simulation : A1028_ProofSimulation.Simulation restricted general)
    (statement : Statement) (proof : GeneralProof)
    (accepted : general.check statement proof = true) :
    restricted.check statement (simulation.translate statement proof) = true :=
  simulation.acceptance statement proof accepted

end A1029_SimulationSoundness

/-! ## 1030 - A restricted lower bound transfers only through the simulation overhead -/
namespace A1030_SimulatedLowerBound

 theorem general_proof_lower_bound {Statement RestrictedProof GeneralProof : Type}
    {restricted : A1021_ProofSystem.System Statement RestrictedProof}
    {general : A1021_ProofSystem.System Statement GeneralProof}
    (simulation : A1028_ProofSimulation.Simulation restricted general)
    (statement : Statement) (bound : Nat)
    (lower : A1025_SystemSpecificLowerBound.RequiresMoreThan
      restricted statement bound)
    (proof : GeneralProof) (accepted : general.check statement proof = true) :
    bound < general.proofBits proof + simulation.overhead := by
  have translatedAccepted := simulation.acceptance statement proof accepted
  have translatedLarge := lower (simulation.translate statement proof) translatedAccepted
  exact lt_of_lt_of_le translatedLarge (simulation.sizeBound statement proof)

end A1030_SimulatedLowerBound

/-! ## 1031 - A resolution lower bound alone supplies no simulation from arbitrary systems -/
namespace A1031_ResolutionTransferGap

structure Status where
  resolutionLowerBound : Bool
  arbitrarySystemSimulation : Bool
  allSystemLowerBound : Bool

 def current : Status where
  resolutionLowerBound := true
  arbitrarySystemSimulation := false
  allSystemLowerBound := false

 theorem restricted_result_available : current.resolutionLowerBound = true := rfl

 theorem universal_transfer_missing : current.arbitrarySystemSimulation = false := rfl

end A1031_ResolutionTransferGap

/-! ## 1032 - Excluding polynomial proofs requires quantifying over every sound complete checker -/
namespace A1032_AllSystemsQuantifier

structure UniversalLowerBound where
  systemIndex : Nat -> Nat
  hardStatementAt : Nat -> Nat
  excluded : Nat -> Prop
  excludesSystem : forall index : Nat, excluded index

 theorem every_index_required (lower : UniversalLowerBound) (index : Nat) :
    lower.excluded index := lower.excludesSystem index

end A1032_AllSystemsQuantifier

/-! ## 1033 - A short proof with an expensive checker is not an NP certificate -/
namespace A1033_CheckerCostObstruction

structure Profile where
  statementBits : Nat
  proofBits : Nat
  checkCost : Nat
  allowedExponent : Nat

 def acceptable (profile : Profile) : Prop :=
  And (profile.proofBits <= (profile.statementBits + 1) ^ profile.allowedExponent)
    (profile.checkCost <= (profile.statementBits + 1) ^ profile.allowedExponent)

 theorem expensive_checker_rejected (profile : Profile)
    (tooExpensive : (profile.statementBits + 1) ^ profile.allowedExponent <
      profile.checkCost) :
    Not (acceptable profile) := by
  intro accepted
  exact (Nat.not_le_of_gt tooExpensive) accepted.right

end A1033_CheckerCostObstruction

/-! ## 1034 - A proof-complexity separation package must rule out every polynomial checker -/
namespace A1034_ProofSeparationPackage

structure Package where
  statementFamily : Nat -> Nat
  truthInCoNP : Prop
  systemExcluded : Nat -> Prop
  excludesEveryPolynomialSystem : forall systemIndex,
    systemExcluded systemIndex
  lowerBoundCertificateCost : Nat -> Nat

 theorem excludes_selected_system (package : Package) (systemIndex : Nat) :
    package.systemExcluded systemIndex :=
  package.excludesEveryPolynomialSystem systemIndex

end A1034_ProofSeparationPackage

/-! ## 1035 - Current proof lower bounds do not exclude every polynomial proof system -/
namespace A1035_ProofComplexityStatus

structure Status where
  restrictedLowerBounds : Bool
  polynomialCheckerAccounting : Bool
  universalProofSystemLowerBound : Bool
  NPneqCoNP : Bool
  PneqNP : Bool

 def current : Status where
  restrictedLowerBounds := true
  polynomialCheckerAccounting := true
  universalProofSystemLowerBound := false
  NPneqCoNP := false
  PneqNP := false

 theorem universal_lower_bound_missing :
    current.universalProofSystemLowerBound = false := rfl

 theorem separation_not_obtained : current.PneqNP = false := rfl

end A1035_ProofComplexityStatus

end PIsNPOrNot.ResearchSeventieth
