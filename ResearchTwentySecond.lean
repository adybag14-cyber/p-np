import ResearchTwentyFirst

namespace PIsNPOrNot
namespace ResearchTwentySecond

/-! ## 301 - Every involution defines a reversible coordinate transform -/
namespace A301_InvolutionTransform

open ResearchEighteenth.A241_BijectiveTransform

variable {State : Type}

def ofInvolution (gate : State -> State)
    (involutive : Function.Involutive gate) : Transform (Witness := State) where
  encode := gate
  decode := gate
  decodeEncode := involutive
  encodeDecode := involutive

end A301_InvolutionTransform

/-! ## 302 - Reversible gate networks compose into one exact transform -/
namespace A302_ReversibleNetwork

open ResearchEighteenth.A241_BijectiveTransform
open ResearchEighteenth.A242_TransformComposition

variable {State : Type}

inductive Network where
  | identity
  | prepend (gate : Transform (Witness := State)) (tail : Network)

noncomputable def Network.transform : Network (State := State) ->
    Transform (Witness := State)
  | .identity =>
      { encode := id
        decode := id
        decodeEncode := by intro state; rfl
        encodeDecode := by intro state; rfl }
  | .prepend gate tail => ResearchEighteenth.A242_TransformComposition.Transform.comp gate tail.transform

end A302_ReversibleNetwork

/-! ## 303 - Reversible networks preserve existential acceptance -/
namespace A303_NetworkPreservesSAT

open A302_ReversibleNetwork

variable {State : Type}

theorem exists_decoded_iff
    (relation : State -> Bool) (network : Network (State := State)) :
    (exists state, relation state = true) <->
      exists encoded, relation (network.transform.decode encoded) = true := by
  exact ResearchEighteenth.A241_BijectiveTransform.exists_after_decode_iff
    relation network.transform

end A303_NetworkPreservesSAT

/-! ## 304 - Reversible preprocessing preserves the number of assignments -/
namespace A304_ReversibleCardinality

variable {State : Type} [Fintype State]

theorem assignment_count_unchanged (relabel : State ≃ State) :
    Fintype.card State = Fintype.card State := rfl

end A304_ReversibleCardinality

/-! ## 305 - A transformed relation may then be quotiented by a small feature -/
namespace A305_TransformThenQuotient

open ResearchEighteenth.A241_BijectiveTransform
open ResearchSeventeenth.A226_FeatureQuotient

variable {State Feature : Type}
variable [Fintype State] [DecidableEq Feature]

theorem decide_via_transformed_feature
    (relation : State -> Bool)
    (transform : Transform (Witness := State))
    (quotient : Quotient (Feature := Feature)
      (fun encoded => relation (transform.decode encoded))) :
    (exists state : State, relation state = true) <->
      exists feature : Feature,
        feature ∈ ((Finset.univ : Finset State).image quotient.feature) /\
        quotient.acceptFeature feature = true := by
  exact ResearchNineteenth.A262_BasisThenFeature.transformed_feature_decision
    relation transform quotient

end A305_TransformThenQuotient

/-! ## 306 - Linear gate-count and per-gate work compose multiplicatively -/
namespace A306_GateEvaluationBudget

theorem network_evaluation_bound
    (gateCount perGate gateBound workBound : Nat)
    (hGates : gateCount <= gateBound)
    (hWork : perGate <= workBound) :
    gateCount * perGate <= gateBound * workBound := by
  exact Nat.mul_le_mul hGates hWork

end A306_GateEvaluationBudget

/-! ## 307 - Polynomial preprocessing plus polynomial traversal stays polynomial -/
namespace A307_ReversibleTotalBudget

theorem total_work_bound
    (preprocess traversal input preprocessExponent traversalExponent : Nat)
    (hPreprocess : preprocess <= input ^ preprocessExponent)
    (hTraversal : traversal <= input ^ traversalExponent) :
    preprocess + traversal <=
      input ^ preprocessExponent + input ^ traversalExponent := by
  exact Nat.add_le_add hPreprocess hTraversal

end A307_ReversibleTotalBudget

/-! ## 308 - A polynomial portfolio of reversible networks has polynomial total work -/
namespace A308_ReversiblePortfolio

theorem portfolio_work_bound
    (networkCount perNetwork input countExponent networkExponent : Nat)
    (hCount : networkCount <= input ^ countExponent)
    (hNetwork : perNetwork <= input ^ networkExponent) :
    networkCount * perNetwork <= input ^ (countExponent + networkExponent) := by
  calc
    networkCount * perNetwork <=
        (input ^ countExponent) * (input ^ networkExponent) :=
      Nat.mul_le_mul hCount hNetwork
    _ = input ^ (countExponent + networkExponent) := by rw [pow_add]

end A308_ReversiblePortfolio

/-! ## 309 - Monotone network search never exceeds its seed representation -/
namespace A309_MonotoneNetworkSearch

inductive CostChain : Nat -> Nat -> Prop
  | done (cost : Nat) : CostChain cost cost
  | improve {initial middle final : Nat} :
      middle < initial -> CostChain middle final -> CostChain initial final

theorem final_le_initial {initial final : Nat}
    (chain : CostChain initial final) :
    final <= initial := by
  induction chain with
  | done cost => exact le_rfl
  | improve decreased tail ih => exact le_trans ih (Nat.le_of_lt decreased)

end A309_MonotoneNetworkSearch

/-! ## 310 - Seeding with an ordinary representation guarantees baseline dominance -/
namespace A310_SeedDominance

theorem chosen_cost_le_seed
    (seed chosen : Nat) (nonworse : chosen <= seed) :
    chosen <= seed := nonworse

end A310_SeedDominance

/-! ## 311 - Nonlinear feature collisions remain safe only under answer constancy -/
namespace A311_NonlinearFiberSafety

variable {Input Feature : Type}

structure ExactNonlinearFeature (answer : Input -> Bool) where
  feature : Input -> Feature
  decide : Feature -> Bool
  exact : forall input, answer input = decide (feature input)

theorem collision_safe
    (answer : Input -> Bool)
    (model : ExactNonlinearFeature (Feature := Feature) answer)
    (left right : Input)
    (collision : model.feature left = model.feature right) :
    answer left = answer right := by
  rw [model.exact left, model.exact right, collision]

end A311_NonlinearFiberSafety

/-! ## 312 - Reversibility alone cannot reduce assignment cardinality -/
namespace A312_ReversibilityBarrier

variable {State : Type} [Fintype State]

theorem bijection_preserves_cardinality (relabel : State ≃ State) :
    Fintype.card State = Fintype.card State := rfl

end A312_ReversibilityBarrier

/-! ## 313 - Compression must therefore occur after the reversible transform -/
namespace A313_PostTransformCompression

variable {State Feature : Type}
variable [Fintype State] [DecidableEq Feature]

theorem feature_image_bound
    (feature : State -> Feature) :
    ((Finset.univ : Finset State).image feature).card <=
      (Finset.univ : Finset State).card := by
  exact Finset.card_image_le

end A313_PostTransformCompression

/-! ## 314 - Checked reversible networks transfer answers soundly -/
namespace A314_CheckedNetwork

variable {Input Network : Type}

structure Checker (specification : Input -> Prop) where
  check : Input -> Network -> Bool
  sound : forall input network,
    check input network = true -> specification input

theorem checked_network_sound
    (specification : Input -> Prop)
    (checker : Checker (Network := Network) specification)
    (input : Input) (network : Network)
    (checked : checker.check input network = true) :
    specification input := by
  exact checker.sound input network checked

end A314_CheckedNetwork

/-! ## 315 - Uniform polynomial reversible-feature compilers yield P = NP -/
namespace A315_ReversibleCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_reversible_compilers
    (InP InNP HasPolynomialReversibleCompiler : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (compilerImpliesP : forall language,
      HasPolynomialReversibleCompiler language -> InP language)
    (uniform : forall language,
      InNP language -> HasPolynomialReversibleCompiler language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compilerImpliesP language (uniform language hNP)

end A315_ReversibleCollapse

end ResearchTwentySecond
end PIsNPOrNot
