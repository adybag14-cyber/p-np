import ResearchSixtySixth

namespace PIsNPOrNot.ResearchSixtySeventh

open ResearchSixtySecond.A901_BooleanFunctionUniverse
open ResearchSixtySecond.A904_DescriptionEvaluator

/-! ## 976 - A range avoider outputs one function outside a circuit-code image -/
namespace A976_RangeAvoider

structure Avoider {n b : Nat} (evaluate : Code b -> BoolFn n) where
  output : BoolFn n
  outside : forall code, Not (evaluate code = output)

end A976_RangeAvoider

/-! ## 977 - Counting gives a noncomputable range avoider under the description gap -/
namespace A977_CountingAvoider

noncomputable def avoider {n b : Nat} (evaluate : Code b -> BoolFn n)
    (small : b < 2 ^ n) : A976_RangeAvoider.Avoider evaluate where
  output := ResearchSixtySecond.A910_SelectedHardFunction.hardFunction evaluate small
  outside := by
    intro code
    exact ResearchSixtySecond.A911_SelectedHardness.hardFunction_not_computed
      evaluate small code

end A977_CountingAvoider

/-! ## 978 - Local evaluation asks for one bit of the avoided truth table -/
namespace A978_LocalBitEvaluation

def bit {n b : Nat} {evaluate : Code b -> BoolFn n}
    (avoider : A976_RangeAvoider.Avoider evaluate)
    (input : Bits n) : Bool := avoider.output input

end A978_LocalBitEvaluation

/-! ## 979 - No represented circuit computes every locally evaluated output bit -/
namespace A979_LocalHardness

theorem differs_somewhere {n b : Nat} {evaluate : Code b -> BoolFn n}
    (avoider : A976_RangeAvoider.Avoider evaluate) (code : Code b) :
    Exists fun input =>
      Not (evaluate code input = A978_LocalBitEvaluation.bit avoider input) := by
  exact Function.ne_iff.mp (avoider.outside code)

end A979_LocalHardness

/-! ## 980 - The complete avoided output contains one bit for every n-bit input -/
namespace A980_OutputLength

def outputBits (n : Nat) : Nat := 2 ^ n

theorem output_bits_formula (n : Nat) : outputBits n = 2 ^ n := rfl

end A980_OutputLength

/-! ## 981 - Range-avoidance accounting separates local and global output costs -/
namespace A981_AvoidanceProfile

structure Profile where
  inputBits : Nat
  codeBits : Nat
  globalOutputBits : Nat
  localEvaluationCost : Nat
  constructionCost : Nat

end A981_AvoidanceProfile

/-! ## 982 - Polynomial work in truth-table length can remain exponential in input length -/
namespace A982_OutputLengthScaling

def workInOutputLength (n exponent : Nat) : Nat :=
  (2 ^ n) ^ exponent

theorem work_formula (n exponent : Nat) :
    workInOutputLength n exponent = 2 ^ (n * exponent) := by
  exact (pow_mul 2 n exponent).symm

end A982_OutputLengthScaling

/-! ## 983 - A locally explicit avoider must construct and evaluate its hard family uniformly -/
namespace A983_LocalExplicitnessPackage

structure Package (n b : Nat) (evaluateCode : Code b -> BoolFn n) where
  avoider : A976_RangeAvoider.Avoider evaluateCode
  constructAt : Nat -> Nat
  evaluateAt : Bits n -> Nat
  representationBits : Nat
  constructionBound : Nat
  evaluationBound : Nat
  constructPolynomial : forall index, constructAt index <= constructionBound
  evaluatePolynomial : forall input, evaluateAt input <= evaluationBound

end A983_LocalExplicitnessPackage

/-! ## 984 - Any locally explicit avoider is an explicit hard function for that code family -/
namespace A984_ExplicitAvoiderHardness

theorem no_code_computes_output {n b : Nat} {evaluate : Code b -> BoolFn n}
    (package : A983_LocalExplicitnessPackage.Package n b evaluate)
    (code : Code b) :
    Not (evaluate code = package.avoider.output) :=
  package.avoider.outside code

end A984_ExplicitAvoiderHardness

/-! ## 985 - If the local evaluator is itself in the avoided family, contradiction follows -/
namespace A985_SelfRepresentationObstruction

theorem no_self_code {n b : Nat} {evaluate : Code b -> BoolFn n}
    (avoider : A976_RangeAvoider.Avoider evaluate)
    (code : Code b)
    (self : evaluate code = avoider.output) : False :=
  avoider.outside code self

end A985_SelfRepresentationObstruction

/-! ## 986 - A nonimage certificate supplies one distinguishing input per code -/
namespace A986_NonImageCertificate

structure Certificate {n b : Nat} (evaluate : Code b -> BoolFn n)
    (hard : BoolFn n) where
  distinguishingInput : Code b -> Bits n
  differs : forall code,
    Not (evaluate code (distinguishingInput code) =
      hard (distinguishingInput code))

end A986_NonImageCertificate

/-! ## 987 - Every extensional range avoider has a noncomputable difference certificate -/
namespace A987_CertificateFromAvoider

noncomputable def certificate {n b : Nat} {evaluate : Code b -> BoolFn n}
    (avoider : A976_RangeAvoider.Avoider evaluate) :
    A986_NonImageCertificate.Certificate evaluate avoider.output where
  distinguishingInput := fun code =>
    (Function.ne_iff.mp (avoider.outside code)).choose
  differs := by
    intro code
    exact (Function.ne_iff.mp (avoider.outside code)).choose_spec

end A987_CertificateFromAvoider

/-! ## 988 - A raw nonimage certificate has one entry per circuit description -/
namespace A988_CertificateEntries

def entries (b : Nat) : Nat := 2 ^ b

theorem entry_formula (b : Nat) :
    Fintype.card (Code b) = entries b := by
  simp [entries]

end A988_CertificateEntries

/-! ## 989 - Storing n-bit distinguishing inputs for all b-bit codes costs n*2^b bits -/
namespace A989_RawCertificateBits

def bits (n b : Nat) : Nat := n * 2 ^ b

theorem bits_formula (n b : Nat) : bits n b = n * 2 ^ b := rfl

theorem square_code_budget (n : Nat) :
    bits n (n * n) = n * 2 ^ (n * n) := rfl

end A989_RawCertificateBits

/-! ## 990 - A separation-grade range avoider needs local explicitness and succinct soundness -/
namespace A990_RangeAvoidanceCriterion

structure Criterion where
  inputBits : Nat
  codeBits : Nat
  localConstructionCost : Nat
  localEvaluationCost : Nat
  nonimageProofBits : Nat
  nonimageCheckCost : Nat
  outputOutsideRange : Prop
  locallyExplicit : Prop
  proofSound : Prop

 theorem all_obligations (criterion : Criterion)
    (complete : And criterion.outputOutsideRange
      (And criterion.locallyExplicit criterion.proofSound)) :
    criterion.outputOutsideRange := complete.left

end A990_RangeAvoidanceCriterion

end PIsNPOrNot.ResearchSixtySeventh
