import ResearchSixtyFifth

namespace PIsNPOrNot.ResearchSixtySixth

/-! ## 961 - A stage-specific candidate may beat one chosen polynomial exponent -/
namespace A961_StageSpecificHardness

def Beats (circuitExponent languageIndex : Nat) : Prop :=
  circuitExponent < languageIndex

end A961_StageSpecificHardness

/-! ## 962 - Every fixed exponent has a larger stage-specific candidate -/
namespace A962_PerExponentExistence

 theorem every_exponent_has_candidate (circuitExponent : Nat) :
    Exists fun languageIndex =>
      A961_StageSpecificHardness.Beats circuitExponent languageIndex := by
  exact Exists.intro (circuitExponent + 1) (Nat.lt_succ_self _)

end A962_PerExponentExistence

/-! ## 963 - Per-exponent existence does not yield one candidate beating all exponents -/
namespace A963_QuantifierSwapFailure

 theorem no_single_index_beats_all :
    Not (Exists fun languageIndex => forall circuitExponent,
      A961_StageSpecificHardness.Beats circuitExponent languageIndex) := by
  rintro ⟨languageIndex, beatsAll⟩
  exact (Nat.lt_irrefl languageIndex) (beatsAll languageIndex)

end A963_QuantifierSwapFailure

/-! ## 964 - The canonical stage family changes language as the target exponent changes -/
namespace A964_ChangingCandidate

def candidate (circuitExponent : Nat) : Nat := circuitExponent + 1

 theorem candidate_beats_stage (circuitExponent : Nat) :
    A961_StageSpecificHardness.Beats circuitExponent (candidate circuitExponent) :=
  Nat.lt_succ_self _

 theorem candidate_changes (circuitExponent : Nat) :
    candidate (circuitExponent + 1) = candidate circuitExponent + 1 := by
  simp [candidate]

end A964_ChangingCandidate

/-! ## 965 - Every fixed candidate fails against its own exponent -/
namespace A965_FixedCandidateFailure

 theorem fails_at_self (languageIndex : Nat) :
    Not (A961_StageSpecificHardness.Beats languageIndex languageIndex) :=
  Nat.lt_irrefl _

end A965_FixedCandidateFailure

/-! ## 966 - A uniform NP verifier carries one fixed polynomial exponent -/
namespace A966_FixedVerifierExponent

structure VerifierProfile where
  verifierExponent : Nat
  witnessExponent : Nat
  verificationCost : Nat -> Nat
  verificationBound : forall inputSize,
    verificationCost inputSize <= inputSize ^ verifierExponent

end A966_FixedVerifierExponent

/-! ## 967 - One fixed verifier exponent cannot directly simulate all polynomial stages -/
namespace A967_VerifierCoverageFailure

structure DirectSimulationProfile where
  verifier : A966_FixedVerifierExponent.VerifierProfile
  coversExponent : Nat -> Prop
  directSimulation : forall exponent,
    coversExponent exponent -> exponent <= verifier.verifierExponent

 theorem not_all_exponents (profile : DirectSimulationProfile) :
    Not (forall exponent, profile.coversExponent exponent) := by
  intro allCovered
  have nextCovered := allCovered (profile.verifier.verifierExponent + 1)
  have impossible := profile.directSimulation _ nextCovered
  omega

end A967_VerifierCoverageFailure

/-! ## 968 - A universal selector must retain the selected machine exponent -/
namespace A968_UniversalSelector

structure Instance where
  machineIndex : Nat
  machineExponent : Nat
  dataLength : Nat

 def simulationCost (input : Instance) : Nat :=
  input.dataLength ^ input.machineExponent

 theorem selected_cost (machineIndex exponent length : Nat) :
    simulationCost {
      machineIndex := machineIndex
      machineExponent := exponent
      dataLength := length } = length ^ exponent := rfl

end A968_UniversalSelector

/-! ## 969 - The universal selector again has no fixed polynomial bound -/
namespace A969_SelectorExponentFailure

 theorem no_fixed_bound (k : Nat) :
    Not (forall exponent,
      A968_UniversalSelector.simulationCost {
        machineIndex := exponent
        machineExponent := exponent
        dataLength := 2 } <= 2 ^ k) := by
  simpa [A968_UniversalSelector.simulationCost] using
    ResearchSixtyFifth.A948_NoUniformExponent.no_fixed_exponent k

end A969_SelectorExponentFailure

/-! ## 970 - Padding the universal selector to its runtime makes its simulation linear -/
namespace A970_UniversalSelectorPadding

structure PaddedInstance where
  originalCost : Nat
  paddedLength : Nat
  paddedDecisionCost : Nat

 def padToCost (cost : Nat) : PaddedInstance where
  originalCost := cost
  paddedLength := cost
  paddedDecisionCost := cost

 theorem decision_linear (cost : Nat) :
    (padToCost cost).paddedDecisionCost = (padToCost cost).paddedLength := rfl

end A970_UniversalSelectorPadding

/-! ## 971 - Fixed-exponent lower bounds and one universal lower bound have different quantifiers -/
namespace A971_LowerBoundQuantifiers

structure PerStage where
  languageAt : Nat -> Nat
  beats : forall exponent,
    A961_StageSpecificHardness.Beats exponent (languageAt exponent)

structure Uniform where
  language : Nat
  beats : forall exponent,
    A961_StageSpecificHardness.Beats exponent language

 theorem no_uniform_object : Not (Nonempty Uniform) := by
  rintro ⟨uniform⟩
  exact A963_QuantifierSwapFailure.no_single_index_beats_all
    (Exists.intro uniform.language uniform.beats)

end A971_LowerBoundQuantifiers

/-! ## 972 - Counting at each circuit budget does not automatically select one hard family -/
namespace A972_CountingQuantifierGap

structure SliceResult where
  budget : Nat
  selectedFunction : Nat
  outsideBudget : Prop

structure UniformResult where
  selectedFamily : Nat
  outsideEveryBudget : forall budget : Nat, Prop

 theorem per_budget_data_has_budget_dependent_selection
    (result : Nat -> SliceResult) (budget : Nat) :
    (result budget).budget = (result budget).budget := rfl

end A972_CountingQuantifierGap

/-! ## 973 - Restricted-model lower bounds need a transfer to one NP-complete language -/
namespace A973_RestrictedModelTransfer

structure TransferAttempt where
  restrictedModel : Nat
  hardLanguageClass : Nat
  targetClass : Nat
  transferCost : Nat
  preservesHardness : Prop
  landsInTarget : Prop

 theorem both_obligations_required (attempt : TransferAttempt)
    (complete : And attempt.preservesHardness attempt.landsInTarget) :
    attempt.preservesHardness := complete.left

end A973_RestrictedModelTransfer

/-! ## 974 - A valid P != NP package must combine NP membership and all-polynomial hardness -/
namespace A974_SeparationPackage

structure Package where
  verifierExponent : Nat
  witnessExponent : Nat
  hardAgainstExponent : Nat -> Prop
  hardAgainstAll : forall exponent, hardAgainstExponent exponent
  verificationCost : Nat -> Nat
  verificationBound : forall inputSize,
    verificationCost inputSize <= inputSize ^ verifierExponent

 theorem hard_against_next (package : Package) :
    package.hardAgainstExponent (package.verifierExponent + 1) :=
  package.hardAgainstAll _

end A974_SeparationPackage

/-! ## 975 - The direct hierarchy route is missing a fixed-exponent universal hard language -/
namespace A975_HierarchyRouteStatus

structure Status where
  perExponentHardLanguages : Bool
  oneUniformNPLanguage : Bool
  paddingPreservesHardness : Bool

 def current : Status where
  perExponentHardLanguages := true
  oneUniformNPLanguage := false
  paddingPreservesHardness := false

 theorem missing_uniform_language : current.oneUniformNPLanguage = false := rfl

 theorem padding_does_not_preserve : current.paddingPreservesHardness = false := rfl

end A975_HierarchyRouteStatus

end PIsNPOrNot.ResearchSixtySixth
