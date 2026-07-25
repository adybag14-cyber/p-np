import ResearchSixtySeventh

namespace PIsNPOrNot.ResearchSixtyEighth

open ResearchSixtySecond.A901_BooleanFunctionUniverse
open ResearchSixtySecond.A904_DescriptionEvaluator

/-! ## 991 - Range nonmembership is a universal statement over all circuit codes -/
namespace A991_RangeNonmembership

def NonImage {n b : Nat} (evaluate : Code b -> BoolFn n)
    (hard : BoolFn n) : Prop :=
  forall code, Not (evaluate code = hard)

end A991_RangeNonmembership

/-! ## 992 - Range nonmembership is equivalent to a distinguishing input for every code -/
namespace A992_PointwiseNonmembership

 theorem nonimage_iff {n b : Nat} (evaluate : Code b -> BoolFn n)
    (hard : BoolFn n) :
    A991_RangeNonmembership.NonImage evaluate hard <->
      forall code, Exists fun input =>
        Not (evaluate code input = hard input) := by
  constructor
  · intro outside code
    exact Function.ne_iff.mp (outside code)
  · intro pointwise code equality
    obtain ⟨input, differs⟩ := pointwise code
    exact differs (congrFun equality input)

end A992_PointwiseNonmembership

/-! ## 993 - A full distinguishing-input certificate proves range nonmembership -/
namespace A993_CertificateSoundness

 theorem certificate_sound {n b : Nat} {evaluate : Code b -> BoolFn n}
    {hard : BoolFn n}
    (certificate : ResearchSixtySeventh.A986_NonImageCertificate.Certificate
      evaluate hard) :
    A991_RangeNonmembership.NonImage evaluate hard := by
  intro code equality
  exact certificate.differs code
    (congrFun equality (certificate.distinguishingInput code))

end A993_CertificateSoundness

/-! ## 994 - The raw certificate contains exactly one input entry per code -/
namespace A994_CertificateEntryCount

def entries (b : Nat) : Nat := 2 ^ b

 theorem entries_eq_code_count (b : Nat) :
    entries b = Fintype.card (Code b) := by
  simp [entries]

end A994_CertificateEntryCount

/-! ## 995 - Explicitly checking every code has exponential work in code length -/
namespace A995_UniversalCheckWork

def work (b perCodeCost : Nat) : Nat := 2 ^ b * perCodeCost

 theorem work_formula (b perCodeCost : Nat) :
    work b perCodeCost = 2 ^ b * perCodeCost := rfl

 theorem entries_le_work (b perCodeCost : Nat) (positive : 0 < perCodeCost) :
    2 ^ b <= work b perCodeCost := by
  unfold work
  exact Nat.le_mul_of_pos_right _ positive

end A995_UniversalCheckWork

/-! ## 996 - Once a hard table is supplied, one output bit is a direct lookup -/
namespace A996_SuppliedTableLookup

structure Table (n : Nat) where
  function : BoolFn n
  storedBits : Nat
  exactBits : storedBits = 2 ^ n

def lookup {n : Nat} (table : Table n) (input : Bits n) : Bool :=
  table.function input

end A996_SuppliedTableLookup

/-! ## 997 - Direct lookup does not charge the construction of the hard table -/
namespace A997_LookupConstructionGap

structure Profile where
  lookupCost : Nat
  tableConstructionCost : Nat
  storedBits : Nat

 theorem construction_is_separate (profile : Profile) :
    profile.tableConstructionCost <=
      profile.lookupCost + profile.tableConstructionCost + profile.storedBits := by
  omega

end A997_LookupConstructionGap

/-! ## 998 - A locally explicit Boolean family computes one bit without storing all tables -/
namespace A998_LocalBooleanFamily

structure Family where
  output : forall n, BoolFn n
  evaluationCost : Nat -> Nat
  evaluationExponent : Nat
  evaluationBound : forall n,
    evaluationCost n <= (n + 1) ^ evaluationExponent

end A998_LocalBooleanFamily

/-! ## 999 - A code family assigns one description budget and evaluator at every length -/
namespace A999_CodeFamily

structure Family where
  codeBits : Nat -> Nat
  evaluate : forall n, Code (codeBits n) -> BoolFn n

end A999_CodeFamily

/-! ## 1000 - A local family is hard for a code family when every length avoids its range -/
namespace A1000_LocalRangeHardness

def HardAt (family : A998_LocalBooleanFamily.Family)
    (codes : A999_CodeFamily.Family) (n : Nat) : Prop :=
  forall code, Not (codes.evaluate n code = family.output n)

def HardEverywhere (family : A998_LocalBooleanFamily.Family)
    (codes : A999_CodeFamily.Family) : Prop :=
  forall n, HardAt family codes n

end A1000_LocalRangeHardness

/-! ## 1001 - Hardness immediately excludes any code computing the local output -/
namespace A1001_CodeContradiction

 theorem no_representing_code
    (family : A998_LocalBooleanFamily.Family)
    (codes : A999_CodeFamily.Family)
    (hard : A1000_LocalRangeHardness.HardEverywhere family codes)
    (n : Nat) (code : Code (codes.codeBits n)) :
    Not (codes.evaluate n code = family.output n) :=
  hard n code

end A1001_CodeContradiction

/-! ## 1002 - NP-style membership uses one fixed witness and verification exponent -/
namespace A1002_NPVerifierFamily

structure Verifier (family : A998_LocalBooleanFamily.Family) where
  witnessBits : Nat -> Nat
  verifier : forall n, Bits n -> Bits (witnessBits n) -> Bool
  verifierCost : Nat -> Nat
  verifierExponent : Nat
  witnessExponent : Nat
  verifierBound : forall n,
    verifierCost n <= (n + 1) ^ verifierExponent
  witnessBound : forall n,
    witnessBits n <= (n + 1) ^ witnessExponent
  exact : forall n input,
    family.output n input = true <->
      Exists fun witness => verifier n input witness = true

end A1002_NPVerifierFamily

/-! ## 1003 - Polynomial circuit budgets form an exponent-indexed family of code lengths -/
namespace A1003_PolynomialCodeBudgets

def budget (exponent n : Nat) : Nat := (n + 1) ^ exponent

 theorem next_exponent_larger_at_two (exponent : Nat) :
    budget exponent 1 < budget (exponent + 1) 1 := by
  unfold budget
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self exponent)

end A1003_PolynomialCodeBudgets

/-! ## 1004 - A separation package requires one NP family hard for every polynomial exponent -/
namespace A1004_SeparationRangePackage

structure Package where
  family : A998_LocalBooleanFamily.Family
  membership : A1002_NPVerifierFamily.Verifier family
  codeFamilyAt : Nat -> A999_CodeFamily.Family
  codeBudgetExact : forall exponent n,
    (codeFamilyAt exponent).codeBits n =
      A1003_PolynomialCodeBudgets.budget exponent n
  hardAgainstEveryExponent : forall exponent,
    A1000_LocalRangeHardness.HardEverywhere family (codeFamilyAt exponent)

 theorem hard_against_next_verifier_exponent (package : Package) :
    A1000_LocalRangeHardness.HardEverywhere package.family
      (package.codeFamilyAt (package.membership.verifierExponent + 1)) :=
  package.hardAgainstEveryExponent _

end A1004_SeparationRangePackage

/-! ## 1005 - Current range avoidance gives nonimage outputs but not this uniform NP package -/
namespace A1005_RangeAvoidanceStatus

structure Status where
  countingNonimage : Bool
  locallyExplicitFamily : Bool
  fixedNPVerifier : Bool
  hardAgainstAllPolynomialBudgets : Bool
  succinctNonimageProof : Bool

 def current : Status where
  countingNonimage := true
  locallyExplicitFamily := false
  fixedNPVerifier := false
  hardAgainstAllPolynomialBudgets := false
  succinctNonimageProof := false

 theorem counting_available : current.countingNonimage = true := rfl

 theorem local_family_missing : current.locallyExplicitFamily = false := rfl

 theorem all_budget_hardness_missing :
    current.hardAgainstAllPolynomialBudgets = false := rfl

end A1005_RangeAvoidanceStatus

end PIsNPOrNot.ResearchSixtyEighth
