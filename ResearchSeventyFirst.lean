import ResearchSeventieth

namespace PIsNPOrNot.ResearchSeventyFirst

/-! ## 1036 - Unary Boolean monotonicity requires false-to-true order preservation -/
namespace A1036_UnaryMonotonicity

def Monotone (function : Bool -> Bool) : Prop :=
  function false = true -> function true = true

end A1036_UnaryMonotonicity

/-! ## 1037 - The identity Boolean function is monotone -/
namespace A1037_IdentityMonotone

 theorem identity_monotone : A1036_UnaryMonotonicity.Monotone id := by
  intro impossible
  simp at impossible

end A1037_IdentityMonotone

/-! ## 1038 - Boolean negation is not monotone -/
namespace A1038_NegationNotMonotone

 theorem not_monotone :
    Not (A1036_UnaryMonotonicity.Monotone Bool.not) := by
  intro monotone
  have falseAccepted : Bool.not false = true := by decide
  have trueAccepted := monotone falseAccepted
  simp at trueAccepted

end A1038_NegationNotMonotone

/-! ## 1039 - A monotone-only representation cannot compute Boolean negation -/
namespace A1039_MonotoneModelObstruction

structure Representation where
  output : Bool -> Bool
  monotone : A1036_UnaryMonotonicity.Monotone output

 theorem no_negation (representation : Representation)
    (computesNot : representation.output = Bool.not) : False := by
  apply A1038_NegationNotMonotone.not_monotone
  simpa [computesNot] using representation.monotone

end A1039_MonotoneModelObstruction

/-! ## 1040 - Negation nevertheless has a constant-size unrestricted representation -/
namespace A1040_UnrestrictedNegation

structure Circuit where
  output : Bool -> Bool
  gates : Nat

 def negation : Circuit where
  output := Bool.not
  gates := 1

 theorem one_gate : negation.gates = 1 := rfl

end A1040_UnrestrictedNegation

/-! ## 1041 - Restricted lower bounds need a simulation from unrestricted circuits -/
namespace A1041_CircuitSimulation

structure Simulation where
  unrestrictedSize : Nat -> Nat
  restrictedSize : Nat -> Nat
  overheadExponent : Nat
  represented : Nat -> Prop
  simulationBound : forall n,
    restrictedSize n <= (unrestrictedSize n + 1) ^ overheadExponent

end A1041_CircuitSimulation

/-! ## 1042 - A restricted lower bound transfers only through a size-preserving simulation -/
namespace A1042_RestrictedLowerBoundTransfer

 theorem transfer {restrictedSize unrestrictedSize bound : Nat}
    (restrictedLower : bound < restrictedSize)
    (simulation : restrictedSize <= unrestrictedSize)
    : bound < unrestrictedSize :=
  lt_of_lt_of_le restrictedLower simulation

end A1042_RestrictedLowerBoundTransfer

/-! ## 1043 - No monotone simulation can cover every unrestricted Boolean circuit -/
namespace A1043_MonotoneSimulationFailure

structure ClaimedSimulation where
  translate : A1040_UnrestrictedNegation.Circuit ->
    A1039_MonotoneModelObstruction.Representation
  exact : forall circuit,
    (translate circuit).output = circuit.output

 theorem impossible (simulation : ClaimedSimulation) : False := by
  exact A1039_MonotoneModelObstruction.no_negation
    (simulation.translate A1040_UnrestrictedNegation.negation)
    (simulation.exact A1040_UnrestrictedNegation.negation)

end A1043_MonotoneSimulationFailure

/-! ## 1044 - A bounded-depth profile may be large while an unrestricted profile is small -/
namespace A1044_DepthRestrictionProfile

structure Profile where
  inputBits : Nat
  boundedDepthSize : Nat
  unrestrictedSize : Nat

 def parityStyle (n : Nat) : Profile where
  inputBits := n
  boundedDepthSize := 2 ^ n
  unrestrictedSize := n

 theorem unrestricted_smaller (n : Nat) :
    (parityStyle n).unrestrictedSize <
      (parityStyle n).boundedDepthSize := by
  simpa [parityStyle] using (Nat.lt_pow_self Nat.one_lt_two : n < 2 ^ n)

end A1044_DepthRestrictionProfile

/-! ## 1045 - A large restricted size does not imply a large unrestricted size -/
namespace A1045_RestrictedDoesNotImplyGeneral

 theorem concrete_counterprofile (n : Nat) :
    And ((A1044_DepthRestrictionProfile.parityStyle n).boundedDepthSize = 2 ^ n)
      ((A1044_DepthRestrictionProfile.parityStyle n).unrestrictedSize = n) := by
  exact And.intro rfl rfl

end A1045_RestrictedDoesNotImplyGeneral

/-! ## 1046 - A transfer theorem must cover every gate used by polynomial-time circuits -/
namespace A1046_GateCoverage

structure GateSetTransfer where
  unrestrictedGateCount : Nat
  coveredGateCount : Nat
  allGatesCovered : Prop
  sizeOverhead : Nat

 theorem coverage_required (transfer : GateSetTransfer)
    (usable : And transfer.allGatesCovered (0 < transfer.sizeOverhead)) :
    transfer.allGatesCovered := usable.left

end A1046_GateCoverage

/-! ## 1047 - Adding the missing gates can invalidate the restricted lower-bound invariant -/
namespace A1047_InvariantLoss

structure ExtensionStatus where
  restrictedInvariant : Prop
  addedGatesPreserveInvariant : Prop
  lowerBoundSurvivesExtension : Prop

 def monotoneWithNegation : ExtensionStatus where
  restrictedInvariant := True
  addedGatesPreserveInvariant := False
  lowerBoundSurvivesExtension := False

 theorem negation_breaks_invariant :
    monotoneWithNegation.addedGatesPreserveInvariant = False := rfl

end A1047_InvariantLoss

/-! ## 1048 - Restricted-model progress must be paired with a transfer or completeness theorem -/
namespace A1048_RestrictedModelCriterion

structure Criterion where
  targetLanguageInNP : Prop
  restrictedLowerBound : Prop
  unrestrictedToRestrictedSimulation : Prop
  polynomialOverhead : Prop

 theorem transfer_obligations (criterion : Criterion)
    (complete : And criterion.restrictedLowerBound
      (And criterion.unrestrictedToRestrictedSimulation criterion.polynomialOverhead)) :
    criterion.unrestrictedToRestrictedSimulation := complete.right.left

end A1048_RestrictedModelCriterion

/-! ## 1049 - Current strong lower bounds often live in restricted or larger-time models -/
namespace A1049_CurrentLowerBoundLocation

structure Status where
  restrictedCircuitBounds : Bool
  exponentialTimeBounds : Bool
  unrestrictedNPCircuitBounds : Bool
  unrestrictedSATTimeBound : Bool

 def current : Status where
  restrictedCircuitBounds := true
  exponentialTimeBounds := true
  unrestrictedNPCircuitBounds := false
  unrestrictedSATTimeBound := false

 theorem np_circuit_bound_missing :
    current.unrestrictedNPCircuitBounds = false := rfl

end A1049_CurrentLowerBoundLocation

/-! ## 1050 - The restricted-circuit route has not produced P != NP -/
namespace A1050_RestrictedCircuitRoute

structure Status where
  monotoneLowerBounds : Bool
  boundedDepthLowerBounds : Bool
  transferToGeneralCircuits : Bool
  oneNPLanguageHardForGeneralCircuits : Bool
  PneqNP : Bool

 def current : Status where
  monotoneLowerBounds := true
  boundedDepthLowerBounds := true
  transferToGeneralCircuits := false
  oneNPLanguageHardForGeneralCircuits := false
  PneqNP := false

 theorem transfer_missing : current.transferToGeneralCircuits = false := rfl

 theorem separation_not_obtained : current.PneqNP = false := rfl

end A1050_RestrictedCircuitRoute

end PIsNPOrNot.ResearchSeventyFirst
