import ResearchEighth

/-!
# Approaches 106-120: minimal semantic residual state spaces

An exact memo key may merge two partial computations only when every possible
completion gives the same answer.  The residual Boolean function is therefore
the canonical exact state.  This file proves both sufficiency and minimality.
-/

namespace PIsNPOrNot
namespace ResearchNinth

/-! ## 106 - Residual functions -/
namespace A106_ResidualFunction

variable {Prefix Suffix : Type}

def residual (relation : Prefix -> Suffix -> Bool) (pfx : Prefix) :
    Suffix -> Bool := relation pfx

def Equivalent (relation : Prefix -> Suffix -> Bool)
    (left right : Prefix) : Prop :=
  forall suffix, relation left suffix = relation right suffix

end A106_ResidualFunction

/-! ## 107 - Semantic residual equivalence is an equivalence relation -/
namespace A107_ResidualEquivalence

open A106_ResidualFunction

variable {Prefix Suffix : Type}

theorem equivalent_refl (relation : Prefix -> Suffix -> Bool) (pfx : Prefix) :
    Equivalent relation pfx pfx := by
  intro suffix
  rfl

theorem equivalent_symm (relation : Prefix -> Suffix -> Bool)
    {left right : Prefix} (h : Equivalent relation left right) :
    Equivalent relation right left := by
  intro suffix
  exact (h suffix).symm

theorem equivalent_trans (relation : Prefix -> Suffix -> Bool)
    {first second third : Prefix}
    (h12 : Equivalent relation first second)
    (h23 : Equivalent relation second third) :
    Equivalent relation first third := by
  intro suffix
  exact (h12 suffix).trans (h23 suffix)

end A107_ResidualEquivalence

/-! ## 108 - Exact state factorizations -/
namespace A108_ExactState

variable {Prefix Suffix : Type}

structure ExactState (relation : Prefix -> Suffix -> Bool) where
  State : Type
  key : Prefix -> State
  decode : State -> Suffix -> Bool
  factors : forall pfx suffix,
    relation pfx suffix = decode (key pfx) suffix

end A108_ExactState

/-! ## 109 - Equal exact states imply equal residual functions -/
namespace A109_StateCollisionSafety

open A106_ResidualFunction A108_ExactState

variable {Prefix Suffix : Type}

theorem same_state_equivalent
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    {left right : Prefix}
    (same : machine.key left = machine.key right) :
    Equivalent relation left right := by
  intro suffix
  calc
    relation left suffix = machine.decode (machine.key left) suffix :=
      machine.factors left suffix
    _ = machine.decode (machine.key right) suffix := by rw [same]
    _ = relation right suffix := (machine.factors right suffix).symm

end A109_StateCollisionSafety

/-! ## 110 - The residual function itself is an exact state -/
namespace A110_CanonicalResidualState

open A106_ResidualFunction A108_ExactState

variable {Prefix Suffix : Type}

def canonical (relation : Prefix -> Suffix -> Bool) : ExactState relation where
  State := Suffix -> Bool
  key := residual relation
  decode := fun state => state
  factors := by
    intro pfx suffix
    rfl

theorem canonical_key_eq_iff
    (relation : Prefix -> Suffix -> Bool) (left right : Prefix) :
    (canonical relation).key left = (canonical relation).key right <->
      Equivalent relation left right := by
  constructor
  · intro same suffix
    exact congrFun same suffix
  · intro equivalent
    funext suffix
    exact equivalent suffix

end A110_CanonicalResidualState

/-! ## 111 - Residual image and state image -/
namespace A111_ResidualImages

variable {Prefix Suffix State : Type}

def residualImage [Fintype Prefix] [DecidableEq (Suffix -> Bool)]
    (relation : Prefix -> Suffix -> Bool) : Finset (Suffix -> Bool) :=
  Finset.univ.image relation

def stateImage [Fintype Prefix] [DecidableEq State]
    (key : Prefix -> State) : Finset State :=
  Finset.univ.image key

end A111_ResidualImages

/-! ## 112 - Every exact state space is at least as large as the residual image -/
namespace A112_ResidualLowerBound

open A108_ExactState A111_ResidualImages

variable {Prefix Suffix : Type} [Fintype Prefix]

theorem residual_image_card_le_state_card
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    [Fintype machine.State] [DecidableEq machine.State]
    [DecidableEq (Suffix -> Bool)] :
    (residualImage relation).card <= Fintype.card machine.State := by
  have hsubset : residualImage relation <=
      Finset.univ.image machine.decode := by
    intro residualFunction hmem
    rcases Finset.mem_image.mp hmem with ⟨pfx, _, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨machine.key pfx, Finset.mem_univ _, ?_⟩
    funext suffix
    exact (machine.factors pfx suffix).symm
  calc
    (residualImage relation).card <=
        (Finset.univ.image machine.decode).card :=
      Finset.card_le_card hsubset
    _ <= Finset.univ.card := Finset.card_image_le
    _ = Fintype.card machine.State := Finset.card_univ

end A112_ResidualLowerBound

/-! ## 113 - The canonical residual state achieves exactly the residual image -/
namespace A113_CanonicalOptimality

open A106_ResidualFunction A110_CanonicalResidualState A111_ResidualImages

variable {Prefix Suffix : Type} [Fintype Prefix]
    [DecidableEq (Suffix -> Bool)]

theorem canonical_image_eq (relation : Prefix -> Suffix -> Bool) :
    stateImage (State := Suffix -> Bool) (canonical relation).key =
      residualImage relation := by
  rfl

end A113_CanonicalOptimality

/-! ## 114 - Decoder states can only add unreachable redundancy -/
namespace A114_ReachableStateBound

open A108_ExactState A111_ResidualImages

variable {Prefix Suffix : Type} [Fintype Prefix]

theorem reachable_states_le_all_states
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    [Fintype machine.State] [DecidableEq machine.State] :
    (stateImage machine.key).card <= Fintype.card machine.State := by
  exact Finset.card_le_univ _

end A114_ReachableStateBound

/-! ## 115 - Residual transitions make canonical states executable -/
namespace A115_ResidualTransition

open A106_ResidualFunction

variable {Prefix Suffix : Type}

structure ResidualTransition
    (relation : Prefix -> Suffix -> Bool)
    (extend : Prefix -> Bool -> Prefix) where
  step : (Suffix -> Bool) -> Bool -> (Suffix -> Bool)
  correct : forall pfx bit,
    residual relation (extend pfx bit) =
      step (residual relation pfx) bit

theorem transition_preserves_residual
    (relation : Prefix -> Suffix -> Bool)
    (extend : Prefix -> Bool -> Prefix)
    (transition : ResidualTransition relation extend)
    (pfx : Prefix) (bit : Bool) :
    residual relation (extend pfx bit) =
      transition.step (residual relation pfx) bit :=
  transition.correct pfx bit

end A115_ResidualTransition

/-! ## 116 - Layer width is bounded below by distinct residuals -/
namespace A116_LayerWidthLowerBound

open A108_ExactState A111_ResidualImages A112_ResidualLowerBound

variable {Prefix Suffix : Type} [Fintype Prefix]

theorem exact_layer_width_lower_bound
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    [Fintype machine.State] [DecidableEq machine.State]
    [DecidableEq (Suffix -> Bool)]
    (claimedWidth : Nat)
    (stateBound : Fintype.card machine.State <= claimedWidth) :
    (residualImage relation).card <= claimedWidth := by
  exact (residual_image_card_le_state_card machine).trans stateBound

end A116_LayerWidthLowerBound

/-! ## 117 - A super-polynomial residual image defeats every small exact state space -/
namespace A117_ResidualObstruction

open A108_ExactState A111_ResidualImages A112_ResidualLowerBound

variable {Prefix Suffix : Type} [Fintype Prefix]

theorem state_space_exceeds_budget
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    [Fintype machine.State] [DecidableEq machine.State]
    [DecidableEq (Suffix -> Bool)]
    (budget : Nat)
    (tooManyResiduals : budget < (residualImage relation).card) :
    budget < Fintype.card machine.State := by
  exact lt_of_lt_of_le tooManyResiduals
    (residual_image_card_le_state_card machine)

end A117_ResidualObstruction

/-! ## 118 - Polynomial residual images are necessary for polynomial exact DAGs -/
namespace A118_PolynomialResidualNecessity

open A108_ExactState A111_ResidualImages A112_ResidualLowerBound

variable {Prefix Suffix : Type} [Fintype Prefix]

theorem residuals_polynomial_if_states_polynomial
    {relation : Prefix -> Suffix -> Bool}
    (machine : ExactState relation)
    [Fintype machine.State] [DecidableEq machine.State]
    [DecidableEq (Suffix -> Bool)]
    (inputSize exponent : Nat)
    (statePolynomial : Fintype.card machine.State <= inputSize ^ exponent) :
    (residualImage relation).card <= inputSize ^ exponent := by
  exact (residual_image_card_le_state_card machine).trans statePolynomial

end A118_PolynomialResidualNecessity

/-! ## 119 - Polynomial canonical residuals are also sufficient once transitions are computable -/
namespace A119_PolynomialResidualSufficiency

structure ResidualCompiler (Instance : Type) where
  decide : Instance -> Bool
  correct : Instance -> Prop
  decisionCorrect : forall input, decide input = true <-> correct input
  residualStates : Instance -> Nat
  inputSize : Instance -> Nat
  exponent : Nat
  residualBound : forall input,
    residualStates input <= inputSize input ^ exponent

theorem compiled_decider_exact {Instance : Type}
    (compiler : ResidualCompiler Instance) (input : Instance) :
    compiler.decide input = true <-> compiler.correct input :=
  compiler.decisionCorrect input

end A119_PolynomialResidualSufficiency

/-! ## 120 - Exact residual criterion for a language-class collapse -/
namespace A120_ResidualCollapseCriterion

open A119_PolynomialResidualSufficiency

variable {Language Instance : Type}

structure UniformResidualCover (InNP : Language -> Prop)
    (Accepts : Language -> Instance -> Prop) where
  compile : forall language, InNP language -> ResidualCompiler Instance
  agrees : forall language (hNP : InNP language) input,
    (compile language hNP).correct input <-> Accepts language input

theorem np_subset_p_of_uniform_residual_cover
    (InNP InP : Language -> Prop)
    (Accepts : Language -> Instance -> Prop)
    (cover : UniformResidualCover (Instance := Instance) InNP Accepts)
    (compilerImpliesP : forall language (compiler : ResidualCompiler Instance),
      (forall input, compiler.correct input <-> Accepts language input) ->
      InP language) :
    forall language, InNP language -> InP language := by
  intro language hNP
  exact compilerImpliesP language (cover.compile language hNP)
    (cover.agrees language hNP)

end A120_ResidualCollapseCriterion

end ResearchNinth
end PIsNPOrNot
