import ResearchNineteenth

namespace PIsNPOrNot
namespace ResearchTwentieth

/-! ## 271 - Canonicalization induces an equivalence relation -/
namespace A271_CanonicalEquivalence

variable {State Canon : Type}

def Equivalent (canon : State -> Canon) (left right : State) : Prop :=
  canon left = canon right

theorem equivalent_refl (canon : State -> Canon) (state : State) :
    Equivalent canon state state := rfl

theorem equivalent_symm (canon : State -> Canon) {left right : State}
    (same : Equivalent canon left right) :
    Equivalent canon right left := same.symm

theorem equivalent_trans (canon : State -> Canon) {left middle right : State}
    (first : Equivalent canon left middle)
    (second : Equivalent canon middle right) :
    Equivalent canon left right := first.trans second

end A271_CanonicalEquivalence

/-! ## 272 - Canonical images never exceed the raw residual set -/
namespace A272_QuotientCardinality

variable {State Canon : Type} [DecidableEq Canon]

theorem canonical_image_card_le
    (states : Finset State) (canon : State -> Canon) :
    (states.image canon).card <= states.card := by
  exact Finset.card_image_le

end A272_QuotientCardinality

/-! ## 273 - A genuine canonical collision gives strict compression -/
namespace A273_StrictCanonicalCompression

variable {State Canon : Type} [DecidableEq State] [DecidableEq Canon]

theorem canonical_image_card_lt
    (states : Finset State) (canon : State -> Canon)
    (left right : State)
    (leftMem : left ∈ states) (rightMem : right ∈ states)
    (different : Not (left = right))
    (collision : canon left = canon right) :
    (states.image canon).card < states.card := by
  have notInjective : Not (Set.InjOn canon (states : Set State)) := by
    intro injective
    exact different (injective leftMem rightMem collision)
  have notEqual : Not ((states.image canon).card = states.card) := by
    intro equalCards
    exact notInjective ((Finset.card_image_iff).1 equalCards)
  have lessOrEqual : (states.image canon).card <= states.card :=
    Finset.card_image_le
  omega

end A273_StrictCanonicalCompression

/-! ## 274 - Invariant answers factor through canonical states -/
namespace A274_InvariantFactorization

variable {State Canon : Type}

structure InvariantModel (answer : State -> Bool) where
  canon : State -> Canon
  answerCanon : Canon -> Bool
  factors : forall state, answer state = answerCanon (canon state)

theorem same_canon_same_answer
    (answer : State -> Bool)
    (model : InvariantModel (Canon := Canon) answer)
    (left right : State)
    (same : model.canon left = model.canon right) :
    answer left = answer right := by
  rw [model.factors left, model.factors right, same]

end A274_InvariantFactorization

/-! ## 275 - The full variable-renaming family has n! elements -/
namespace A275_PermutationSearchSpace

theorem permutation_family_card (n : Nat) :
    Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
  rw [Fintype.card_perm, Fintype.card_fin]

end A275_PermutationSearchSpace

/-! ## 276 - A polynomial generator family avoids factorial enumeration -/
namespace A276_SymmetryGeneratorBudget

theorem generator_search_bound
    (generatorCount perGenerator input generatorExponent workExponent : Nat)
    (generatorBound : generatorCount <= input ^ generatorExponent)
    (workBound : perGenerator <= input ^ workExponent) :
    generatorCount * perGenerator <= input ^ (generatorExponent + workExponent) := by
  calc
    generatorCount * perGenerator <=
        (input ^ generatorExponent) * (input ^ workExponent) :=
      Nat.mul_le_mul generatorBound workBound
    _ = input ^ (generatorExponent + workExponent) := by rw [pow_add]

end A276_SymmetryGeneratorBudget

/-! ## 277 - Relabeling by an equivalence preserves existential acceptance -/
namespace A277_RelabelingPreservesExistence

variable {State : Type}

theorem exists_comp_equiv_iff
    (relation : State -> Bool) (relabel : State ≃ State) :
    (exists state, relation state = true) <->
      exists state, relation (relabel state) = true := by
  constructor
  · rintro ⟨state, accepted⟩
    refine ⟨relabel.symm state, ?_⟩
    simpa using accepted
  · rintro ⟨state, accepted⟩
    exact ⟨relabel state, accepted⟩

end A277_RelabelingPreservesExistence

/-! ## 278 - Automorphism orbits safely merge invariant residuals -/
namespace A278_AutomorphismOrbit

variable {State Automorphism : Type}

structure OrbitModel (answer : State -> Bool) where
  act : Automorphism -> State -> State
  invariant : forall automorphism state,
    answer (act automorphism state) = answer state

theorem orbit_member_same_answer
    (answer : State -> Bool)
    (model : OrbitModel (Automorphism := Automorphism) answer)
    (automorphism : Automorphism) (state : State) :
    answer (model.act automorphism state) = answer state := by
  exact model.invariant automorphism state

end A278_AutomorphismOrbit

/-! ## 279 - A checked canonicalizer transfers answers soundly -/
namespace A279_CheckedCanonicalizer

variable {State Canon : Type}

structure Checker (answer : State -> Bool) where
  canon : State -> Canon
  representative : Canon -> State
  check : forall state,
    answer (representative (canon state)) = answer state

theorem representative_sound
    (answer : State -> Bool)
    (checker : Checker (Canon := Canon) answer)
    (state : State) :
    answer (checker.representative (checker.canon state)) = answer state := by
  exact checker.check state

end A279_CheckedCanonicalizer

/-! ## 280 - Polynomially many symmetry quotients have a polynomial union bound -/
namespace A280_SymmetryPortfolioBudget

theorem symmetry_portfolio_bound
    (quotientCount statesPerQuotient input countExponent stateExponent : Nat)
    (countBound : quotientCount <= input ^ countExponent)
    (stateBound : statesPerQuotient <= input ^ stateExponent) :
    quotientCount * statesPerQuotient <=
      input ^ (countExponent + stateExponent) := by
  calc
    quotientCount * statesPerQuotient <=
        (input ^ countExponent) * (input ^ stateExponent) :=
      Nat.mul_le_mul countBound stateBound
    _ = input ^ (countExponent + stateExponent) := by rw [pow_add]

end A280_SymmetryPortfolioBudget

/-! ## 281 - Linear and symmetry features compose into product features -/
namespace A281_ProductFeature

variable {Input LinearFeature SymmetryFeature : Type}

structure ProductModel (answer : Input -> Bool) where
  linear : Input -> LinearFeature
  symmetry : Input -> SymmetryFeature
  decide : LinearFeature × SymmetryFeature -> Bool
  factors : forall input,
    answer input = decide (linear input, symmetry input)

theorem equal_product_feature_equal_answer
    (answer : Input -> Bool)
    (model : ProductModel
      (LinearFeature := LinearFeature) (SymmetryFeature := SymmetryFeature) answer)
    (left right : Input)
    (sameLinear : model.linear left = model.linear right)
    (sameSymmetry : model.symmetry left = model.symmetry right) :
    answer left = answer right := by
  rw [model.factors left, model.factors right, sameLinear, sameSymmetry]

end A281_ProductFeature

/-! ## 282 - Product feature state counts multiply -/
namespace A282_ProductStateBudget

theorem product_state_bound
    (linearStates symmetryStates linearBound symmetryBound : Nat)
    (hLinear : linearStates <= linearBound)
    (hSymmetry : symmetryStates <= symmetryBound) :
    linearStates * symmetryStates <= linearBound * symmetryBound := by
  exact Nat.mul_le_mul hLinear hSymmetry

end A282_ProductStateBudget

/-! ## 283 - Polynomial canonicalization and traversal costs compose -/
namespace A283_CanonicalTraversalBudget

theorem canonical_total_bound
    (canonicalization traversal canonicalBound traversalBound : Nat)
    (hCanonical : canonicalization <= canonicalBound)
    (hTraversal : traversal <= traversalBound) :
    canonicalization + traversal <= canonicalBound + traversalBound := by
  exact Nat.add_le_add hCanonical hTraversal

end A283_CanonicalTraversalBudget

/-! ## 284 - A finite radical portfolio is complete when one member covers each input -/
namespace A284_RadicalPortfolioCoverage

variable {Input Solver : Type}

structure Portfolio where
  solves : Solver -> Input -> Prop
  family : List Solver
  cover : forall input, exists solver, solver ∈ family /\ solves solver input

theorem every_input_has_solver
    (portfolio : Portfolio (Input := Input) (Solver := Solver))
    (input : Input) :
    exists solver, solver ∈ portfolio.family /\ portfolio.solves solver input := by
  exact portfolio.cover input

end A284_RadicalPortfolioCoverage

/-! ## 285 - Uniform polynomial symmetry-linear portfolios yield P = NP -/
namespace A285_SymmetryLinearCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_symmetry_linear_portfolio
    (InP InNP HasPortfolio : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (portfolioImpliesP : forall language, HasPortfolio language -> InP language)
    (uniform : forall language, InNP language -> HasPortfolio language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact portfolioImpliesP language (uniform language hNP)

end A285_SymmetryLinearCollapse

end ResearchTwentieth
end PIsNPOrNot
