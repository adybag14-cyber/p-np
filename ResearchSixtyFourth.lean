import ResearchSixtyThird

namespace PIsNPOrNot.ResearchSixtyFourth

/-! ## 931 - A padding plan records original time and padded input length -/
namespace A931_PaddingPlan

structure Plan where
  originalLength : Nat
  originalTime : Nat
  paddedLength : Nat
  polynomialExponent : Nat

end A931_PaddingPlan

/-! ## 932 - Padding absorbs a computation when its time is polynomial in padded length -/
namespace A932_AbsorbedComputation

open A931_PaddingPlan

def Absorbed (plan : Plan) : Prop :=
  plan.originalTime <= plan.paddedLength ^ plan.polynomialExponent

end A932_AbsorbedComputation

/-! ## 933 - Direct deterministic simulation costs the original running time -/
namespace A933_DirectSimulation

open A931_PaddingPlan

def simulationCost (plan : Plan) : Nat := plan.originalTime

end A933_DirectSimulation

/-! ## 934 - Any padding that absorbs a deterministic history also absorbs simulation -/
namespace A934_AbsorptionMakesSimulationPolynomial

open A931_PaddingPlan A932_AbsorbedComputation A933_DirectSimulation

theorem simulation_bounded (plan : Plan) (absorbed : Absorbed plan) :
    simulationCost plan <= plan.paddedLength ^ plan.polynomialExponent :=
  absorbed

end A934_AbsorptionMakesSimulationPolynomial

/-! ## 935 - A full deterministic computation history has the same step scale -/
namespace A935_HistoryLength

open A931_PaddingPlan

def historyLength (plan : Plan) : Nat := plan.originalTime

 theorem history_equals_simulation (plan : Plan) :
    historyLength plan = A933_DirectSimulation.simulationCost plan := rfl

end A935_HistoryLength

/-! ## 936 - Making the full history polynomial also makes direct decision polynomial -/
namespace A936_HistoryPaddingTrap

open A931_PaddingPlan A932_AbsorbedComputation

theorem history_bound_implies_simulation_bound (plan : Plan)
    (historyBound : A935_HistoryLength.historyLength plan <=
      plan.paddedLength ^ plan.polynomialExponent) :
    A933_DirectSimulation.simulationCost plan <=
      plan.paddedLength ^ plan.polynomialExponent := by
  simpa [A935_HistoryLength.historyLength,
    A933_DirectSimulation.simulationCost] using historyBound

end A936_HistoryPaddingTrap

/-! ## 937 - Exponential padding makes an exponential computation linear in padded length -/
namespace A937_ExponentialPadding

open A931_PaddingPlan

def plan (n : Nat) : Plan where
  originalLength := n
  originalTime := 2 ^ n
  paddedLength := 2 ^ n
  polynomialExponent := 1

end A937_ExponentialPadding

/-! ## 938 - The exponentially padded simulation cost equals padded length -/
namespace A938_ExponentialPaddingCollapse

 theorem simulation_eq_padded_length (n : Nat) :
    A933_DirectSimulation.simulationCost (A937_ExponentialPadding.plan n) =
      (A937_ExponentialPadding.plan n).paddedLength := rfl

 theorem absorbed (n : Nat) :
    A932_AbsorbedComputation.Absorbed (A937_ExponentialPadding.plan n) := by
  simp [A932_AbsorbedComputation.Absorbed, A937_ExponentialPadding.plan]

end A938_ExponentialPaddingCollapse

/-! ## 939 - Polynomial history verification does not separate deterministic simulation -/
namespace A939_HistoryCertificateCollapse

structure HistoryCertificate where
  paddedLength : Nat
  historyLength : Nat
  exponent : Nat
  verificationCost : Nat
  verificationEqualsHistory : verificationCost = historyLength
  historyPolynomial : historyLength <= paddedLength ^ exponent

 theorem deterministic_cost_polynomial (certificate : HistoryCertificate) :
    certificate.verificationCost <=
      certificate.paddedLength ^ certificate.exponent := by
  rw [certificate.verificationEqualsHistory]
  exact certificate.historyPolynomial

end A939_HistoryCertificateCollapse

/-! ## 940 - Underpadding fails to absorb a longer computation at the same exponent -/
namespace A940_Underpadding

 theorem not_absorbed_degree_one {time padded : Nat} (tooShort : padded < time) :
    Not (time <= padded ^ 1) := by
  simpa using Nat.not_le_of_gt tooShort

end A940_Underpadding

/-! ## 941 - Every padding plan falls on one side of the absorption dilemma -/
namespace A941_PaddingDilemma

open A931_PaddingPlan

theorem absorbed_or_too_short (plan : Plan) :
    plan.originalTime <= plan.paddedLength ^ plan.polynomialExponent \/
      plan.paddedLength ^ plan.polynomialExponent < plan.originalTime :=
  le_or_gt _ _

end A941_PaddingDilemma

/-! ## 942 - The absorbed side yields a deterministic polynomial bound -/
namespace A942_AbsorbedSide

open A931_PaddingPlan

theorem simulation_polynomial_if_absorbed (plan : Plan)
    (absorbed : plan.originalTime <=
      plan.paddedLength ^ plan.polynomialExponent) :
    A933_DirectSimulation.simulationCost plan <=
      plan.paddedLength ^ plan.polynomialExponent := absorbed

end A942_AbsorbedSide

/-! ## 943 - The unabsorbed side cannot verify the full history within that bound -/
namespace A943_UnabsorbedSide

open A931_PaddingPlan

theorem full_history_not_polynomial (plan : Plan)
    (tooShort : plan.paddedLength ^ plan.polynomialExponent <
      plan.originalTime) :
    Not (A935_HistoryLength.historyLength plan <=
      plan.paddedLength ^ plan.polynomialExponent) := by
  simpa [A935_HistoryLength.historyLength] using Nat.not_le_of_gt tooShort

end A943_UnabsorbedSide

/-! ## 944 - A useful NP certificate must be shorter than deterministic recomputation -/
namespace A944_ShortCertificateRequirement

structure Profile where
  deterministicTime : Nat
  certificateLength : Nat
  verificationTime : Nat
  paddedLength : Nat
  exponent : Nat

 def genuinelyShort (profile : Profile) : Prop :=
  profile.certificateLength < profile.deterministicTime

 theorem full_history_not_short (time : Nat) :
    Not (genuinelyShort {
      deterministicTime := time
      certificateLength := time
      verificationTime := time
      paddedLength := time
      exponent := 1 }) := by
  simp [genuinelyShort]

end A944_ShortCertificateRequirement

/-! ## 945 - Padding a deterministic hierarchy language by its full runtime cannot prove P != NP -/
namespace A945_PaddingSeparationCriterion

structure Attempt where
  originalTime : Nat
  paddedLength : Nat
  exponent : Nat
  verifierTime : Nat
  deterministicPaddedTime : Nat

 def fullHistoryAttempt (time : Nat) : Attempt where
  originalTime := time
  paddedLength := time
  exponent := 1
  verifierTime := time
  deterministicPaddedTime := time

 theorem deterministic_matches_verifier (time : Nat) :
    (fullHistoryAttempt time).deterministicPaddedTime =
      (fullHistoryAttempt time).verifierTime := rfl

end A945_PaddingSeparationCriterion

end PIsNPOrNot.ResearchSixtyFourth
