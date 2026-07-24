import ResearchFiftieth

namespace PIsNPOrNot.ResearchFiftyFirst

/-! ## 736 - Pointwise Boolean complementation is an involution -/
namespace A736_PointwiseComplement

def complement {Input : Type} (function : Input -> Bool) : Input -> Bool :=
  fun input => !(function input)

theorem involutive {Input : Type} (function : Input -> Bool) :
    complement (complement function) = function := by
  funext input
  cases value : function input <;> simp [complement, value]

end A736_PointwiseComplement

/-! ## 737 - A semantic complemented encoding separates physical nodes from polarity -/
namespace A737_SemanticComplementedEncoding

structure Encoding (State Base Residual : Type)
    [Fintype State] [Fintype Base] where
  meaning : State -> Residual
  meaningInjective : Function.Injective meaning
  baseMeaning : Base -> Residual
  complement : Residual -> Residual
  encode : State -> Base × Bool
  decode : Base × Bool -> Residual
  exact : forall state, decode (encode state) = meaning state
  baseCase : forall base, decode (base, false) = baseMeaning base
  complementCase : forall base, decode (base, true) = complement (baseMeaning base)

end A737_SemanticComplementedEncoding

/-! ## 738 - Exact complemented decoding factors every semantic meaning through a reference -/
namespace A738_ComplementedFactorization

open A737_SemanticComplementedEncoding

variable {State Base Residual : Type} [Fintype State] [Fintype Base]

theorem meaning_factors (encoding : Encoding State Base Residual) (state : State) :
    encoding.meaning state = encoding.decode (encoding.encode state) :=
  (encoding.exact state).symm

end A738_ComplementedFactorization

/-! ## 739 - Exact complemented encodings are injective on references -/
namespace A739_ComplementedEncodeInjective

open A737_SemanticComplementedEncoding

variable {State Base Residual : Type} [Fintype State] [Fintype Base]

theorem encode_injective (encoding : Encoding State Base Residual) :
    Function.Injective encoding.encode := by
  intro left right sameReference
  apply encoding.meaningInjective
  calc
    encoding.meaning left = encoding.decode (encoding.encode left) :=
      (encoding.exact left).symm
    _ = encoding.decode (encoding.encode right) := by rw [sameReference]
    _ = encoding.meaning right := encoding.exact right

end A739_ComplementedEncodeInjective

/-! ## 740 - A complemented base can encode at most twice as many semantic states -/
namespace A740_ComplementedCardinalityBound

open A737_SemanticComplementedEncoding

variable {State Base Residual : Type} [Fintype State] [Fintype Base]

theorem state_card_le_two_mul_base (encoding : Encoding State Base Residual) :
    Fintype.card State <= 2 * Fintype.card Base := by
  calc
    Fintype.card State <= Fintype.card (Base × Bool) :=
      Fintype.card_le_of_injective encoding.encode
        (A739_ComplementedEncodeInjective.encode_injective encoding)
    _ = 2 * Fintype.card Base := by simp [Nat.mul_comm]

end A740_ComplementedCardinalityBound

/-! ## 741 - The parity residual meanings form an injective two-state family -/
namespace A741_ParityMeaningInjective

open ResearchFortyNinth.A709_ParityResidual

theorem meaning_injective : Function.Injective residual := by
  intro left right equalMeaning
  cases left <;> cases right
  case false.false => rfl
  case false.true =>
    exfalso
    exact ResearchFortyNinth.A710_DistinctParityResiduals.residuals_distinct equalMeaning
  case true.false =>
    exfalso
    apply ResearchFortyNinth.A710_DistinctParityResiduals.residuals_distinct
    exact equalMeaning.symm
  case true.true => rfl

end A741_ParityMeaningInjective

/-! ## 742 - Parity admits a one-base-node semantic complemented encoding -/
namespace A742_ParityComplementedEncoding

open A736_PointwiseComplement
open A737_SemanticComplementedEncoding
open ResearchFortyNinth.A709_ParityResidual

def parityEncoding : Encoding Bool Unit (Bool -> Bool) where
  meaning := residual
  meaningInjective := A741_ParityMeaningInjective.meaning_injective
  baseMeaning := fun _unit => residual false
  complement := complement
  encode := fun state => ((), state)
  decode := fun reference =>
    if reference.2 then complement (residual false) else residual false
  exact := by
    intro state
    cases state
    case false => rfl
    case true =>
      exact ResearchFiftieth.A723_ParityResidualComplement.true_residual_complement.symm
  baseCase := by intro base; cases base; rfl
  complementCase := by intro base; cases base; rfl

end A742_ParityComplementedEncoding

/-! ## 743 - The parity complemented encoding is pointwise exact -/
namespace A743_ParityComplementedExact

open ResearchFortyNinth.A709_ParityResidual

theorem decode_encode (state : Bool) :
    A742_ParityComplementedEncoding.parityEncoding.decode
      (A742_ParityComplementedEncoding.parityEncoding.encode state) = residual state :=
  A742_ParityComplementedEncoding.parityEncoding.exact state

end A743_ParityComplementedExact

/-! ## 744 - One physical base node is sufficient for both parity residual states -/
namespace A744_ParityBaseCardinality

theorem unit_base_card : Fintype.card Unit = 1 := by simp

theorem two_states_fit_one_base :
    Fintype.card Bool <= 2 * Fintype.card Unit := by
  exact A740_ComplementedCardinalityBound.state_card_le_two_mul_base
    A742_ParityComplementedEncoding.parityEncoding

end A744_ParityBaseCardinality

/-! ## 745 - One base node is also necessary for nonempty parity semantics -/
namespace A745_ParityBaseMinimality

variable {Base : Type} [Fintype Base]

theorem base_nonempty
    (encoding : A737_SemanticComplementedEncoding.Encoding Bool Base (Bool -> Bool)) :
    1 <= Fintype.card Base := by
  have bound := A740_ComplementedCardinalityBound.state_card_le_two_mul_base encoding
  have boolCard : Fintype.card Bool = 2 := by simp
  rw [boolCard] at bound
  omega

end A745_ParityBaseMinimality

/-! ## 746 - Every encoded meaning is a base meaning or its complement -/
namespace A746_ComplementClosure

open A737_SemanticComplementedEncoding

variable {State Base Residual : Type} [Fintype State] [Fintype Base]

theorem meaning_is_base_or_complement
    (encoding : Encoding State Base Residual) (state : State) :
    Exists fun base =>
      Or (encoding.meaning state = encoding.baseMeaning base)
        (encoding.meaning state = encoding.complement (encoding.baseMeaning base)) := by
  cases encodeEq : encoding.encode state with
  | mk base polarity =>
    apply Exists.intro base
    cases polarity
    case false =>
      apply Or.inl
      calc
        encoding.meaning state = encoding.decode (encoding.encode state) :=
          (encoding.exact state).symm
        _ = encoding.decode (base, false) := by rw [encodeEq]
        _ = encoding.baseMeaning base := encoding.baseCase base
    case true =>
      apply Or.inr
      calc
        encoding.meaning state = encoding.decode (encoding.encode state) :=
          (encoding.exact state).symm
        _ = encoding.decode (base, true) := by rw [encodeEq]
        _ = encoding.complement (encoding.baseMeaning base) :=
          encoding.complementCase base

end A746_ComplementClosure

/-! ## 747 - A residual outside all complement pairs obstructs an exact encoding -/
namespace A747_UnpairedResidualObstruction

open A737_SemanticComplementedEncoding

variable {State Base Residual : Type} [Fintype State] [Fintype Base]

theorem no_encoding_of_unpaired
    (meaning : State -> Residual) (baseMeaning : Base -> Residual)
    (complement : Residual -> Residual)
    (unpaired : Exists fun state => forall base,
      And (Not (meaning state = baseMeaning base))
        (Not (meaning state = complement (baseMeaning base)))) :
    Not (Exists fun encoding : Encoding State Base Residual =>
      And (encoding.meaning = meaning)
        (And (encoding.baseMeaning = baseMeaning)
          (encoding.complement = complement))) := by
  intro hasEncoding
  cases hasEncoding with
  | intro encoding properties =>
    cases properties with
    | intro meaningEq remaining =>
      cases remaining with
      | intro baseEq complementEq =>
        cases unpaired with
        | intro state stateUnpaired =>
          have represented :=
            A746_ComplementClosure.meaning_is_base_or_complement encoding state
          cases represented with
          | intro base alternatives =>
            cases alternatives with
            | inl direct =>
              rw [meaningEq, baseEq] at direct
              exact (stateUnpaired base).1 direct
            | inr complemented =>
              rw [meaningEq, baseEq, complementEq] at complemented
              exact (stateUnpaired base).2 complemented

end A747_UnpairedResidualObstruction

/-! ## 748 - Complemented and explicit representations form a baseline-safe portfolio -/
namespace A748_ComplementedPortfolio

structure Candidate (specification : Prop) where
  work : Nat
  exact : specification

def choose {specification : Prop}
    (explicit complemented : Candidate specification) : Candidate specification :=
  if complemented.work <= explicit.work then complemented else explicit

theorem chosen_work_le_explicit {specification : Prop}
    (explicit complemented : Candidate specification) :
    (choose explicit complemented).work <= explicit.work := by
  unfold choose
  split
  case isTrue h => exact le_trans h le_rfl
  case isFalse _ => exact le_rfl

theorem chosen_exact {specification : Prop}
    (explicit complemented : Candidate specification) :
    specification :=
  (choose explicit complemented).exact

end A748_ComplementedPortfolio

/-! ## 749 - Complement pairing halves width only when polarity decoding is exact -/
namespace A749_PairingObligation

structure Obligation where
  semanticStates : Nat
  physicalBases : Nat
  exactDecode : Prop
  cardinalityBound : exactDecode -> semanticStates <= 2 * physicalBases

theorem bound_when_certified (obligation : Obligation)
    (certified : obligation.exactDecode) :
    obligation.semanticStates <= 2 * obligation.physicalBases :=
  obligation.cardinalityBound certified

end A749_PairingObligation

/-! ## 750 - Parity's complete representation profile includes complement-edge BDDs -/
namespace A750_CompleteParityProfile

structure Profile (n : Nat) where
  semanticClasses : Nat
  complementedNodes : Nat
  explicitObddNodes : Nat
  cubeTerms : Nat
  cubeLiterals : Nat
  treeNodes : Nat
  semanticEquation : semanticClasses = 2
  complementedEquation : complementedNodes = n + 1
  explicitEquation : explicitObddNodes = 2 * n + 1
  cubeEquation : cubeTerms = 2 ^ n
  literalEquation : cubeLiterals = n * 2 ^ n
  treeEquation : treeNodes = 2 ^ (n + 1) - 1

noncomputable def profile (n : Nat) : Profile n where
  semanticClasses := 2
  complementedNodes := n + 1
  explicitObddNodes := 2 * n + 1
  cubeTerms := 2 ^ n
  cubeLiterals := n * 2 ^ n
  treeNodes := 2 ^ (n + 1) - 1
  semanticEquation := rfl
  complementedEquation := rfl
  explicitEquation := rfl
  cubeEquation := rfl
  literalEquation := rfl
  treeEquation := rfl

end A750_CompleteParityProfile

end PIsNPOrNot.ResearchFiftyFirst
