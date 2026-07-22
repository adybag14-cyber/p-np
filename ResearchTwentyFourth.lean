import ResearchTwentyThird

namespace PIsNPOrNot
namespace ResearchTwentyFourth

/-! ## 331 - Exact compiled candidates carry their own semantic proof -/
namespace A331_ExactCandidate

variable {Input : Type}

structure Candidate (specification : Input -> Prop) where
  decide : Input -> Bool
  cost : Nat
  exact : forall input, decide input = true <-> specification input

theorem accepted_iff_specification
    (specification : Input -> Prop)
    (candidate : Candidate specification) (input : Input) :
    candidate.decide input = true <-> specification input :=
  candidate.exact input

end A331_ExactCandidate

/-! ## 332 - The identity or baseline candidate makes every search total -/
namespace A332_BaselineCandidate

open A331_ExactCandidate

variable {Input : Type}

structure SearchSeed (specification : Input -> Prop) where
  baseline : Candidate specification

theorem seed_has_exact_candidate
    (specification : Input -> Prop) (seed : SearchSeed specification) :
    exists candidate : Candidate specification,
      candidate.cost <= seed.baseline.cost := by
  exact ⟨seed.baseline, Nat.le_refl _⟩

end A332_BaselineCandidate

/-! ## 333 - A globally measured improving step preserves exactness -/
namespace A333_ImprovingStep

open A331_ExactCandidate

variable {Input : Type}

structure Step (specification : Input -> Prop) where
  before : Candidate specification
  after : Candidate specification
  improves : after.cost <= before.cost

theorem after_is_exact
    (specification : Input -> Prop) (step : Step specification)
    (input : Input) :
    step.after.decide input = true <-> specification input :=
  step.after.exact input

end A333_ImprovingStep

/-! ## 334 - Chains of accepted improvements never exceed their seed -/
namespace A334_ImprovementChain

inductive Chain : Nat -> Nat -> Prop
  | done (cost : Nat) : Chain cost cost
  | step {start middle finish : Nat} :
      middle <= start -> Chain middle finish -> Chain start finish

theorem final_le_initial {initial final : Nat} (chain : Chain initial final) :
    final <= initial := by
  induction chain with
  | done cost => exact Nat.le_refl cost
  | step improvement rest ih => exact le_trans ih improvement

end A334_ImprovementChain

/-! ## 335 - Beam retention can explicitly preserve a certified baseline -/
namespace A335_BeamBaseline

open A331_ExactCandidate

variable {Input : Type}

structure BeamResult (specification : Input -> Prop) where
  baseline : Candidate specification
  chosen : Candidate specification
  retainedBound : chosen.cost <= baseline.cost

theorem chosen_exact_and_bounded
    (specification : Input -> Prop) (result : BeamResult specification)
    (input : Input) :
    (result.chosen.decide input = true <-> specification input) /\
      result.chosen.cost <= result.baseline.cost := by
  exact ⟨result.chosen.exact input, result.retainedBound⟩

end A335_BeamBaseline

/-! ## 336 - Fixed-depth gate networks have an exact finite search-space size -/
namespace A336_GateNetworkCount

theorem network_space_card
    (Gate : Type) [Fintype Gate] (depth : Nat) :
    Fintype.card (Fin depth -> Gate) = Fintype.card Gate ^ depth := by
  simpa using (Fintype.card_fun :
    Fintype.card (Fin depth -> Gate) =
      Fintype.card Gate ^ Fintype.card (Fin depth))

end A336_GateNetworkCount

/-! ## 337 - Enumerating a bounded network family has multiplicative work -/
namespace A337_EnumerationWork

theorem enumeration_work_bound
    (candidateCount perCandidate input countExp workExp : Nat)
    (countBound : candidateCount <= input ^ countExp)
    (workBound : perCandidate <= input ^ workExp) :
    candidateCount * perCandidate <= input ^ (countExp + workExp) := by
  calc
    candidateCount * perCandidate <=
        input ^ countExp * input ^ workExp :=
      Nat.mul_le_mul countBound workBound
    _ = input ^ (countExp + workExp) := by
      rw [pow_add]

end A337_EnumerationWork

/-! ## 338 - A polynomial candidate subfamily is enough if it contains a good network -/
namespace A338_CandidateSubfamily

variable {Network : Type}

theorem contained_good_network
    (family : List Network) (good : Network -> Prop)
    (network : Network) (member : network ∈ family) (works : good network) :
    exists candidate, candidate ∈ family /\ good candidate := by
  exact ⟨network, member, works⟩

end A338_CandidateSubfamily

/-! ## 339 - Exact replay checks remove trust from the network-search heuristic -/
namespace A339_ReplayChecker

variable {Input Network : Type}

structure Checker (specification : Input -> Prop) where
  check : Input -> Network -> Bool
  sound : forall input network,
    check input network = true -> specification input

theorem accepted_network_sound
    (specification : Input -> Prop) (checker : Checker specification)
    (input : Input) (network : Network)
    (accepted : checker.check input network = true) :
    specification input :=
  checker.sound input network accepted

end A339_ReplayChecker

/-! ## 340 - Exhaustive semantic agreement upgrades a heuristic candidate to exactness -/
namespace A340_ExhaustiveValidation

variable {Input : Type}

structure Validation (specification : Input -> Prop) where
  decide : Input -> Bool
  agrees : forall input, decide input = true <-> specification input

theorem validated_exact
    (specification : Input -> Prop) (validation : Validation specification)
    (input : Input) :
    validation.decide input = true <-> specification input :=
  validation.agrees input

end A340_ExhaustiveValidation

/-! ## 341 - Network construction plus diagram evaluation has additive cost -/
namespace A341_CompiledCost

theorem total_cost_bound
    (construction evaluation input constructionExp evaluationExp : Nat)
    (constructionBound : construction <= input ^ constructionExp)
    (evaluationBound : evaluation <= input ^ evaluationExp) :
    construction + evaluation <=
      input ^ constructionExp + input ^ evaluationExp :=
  Nat.add_le_add constructionBound evaluationBound

end A341_CompiledCost

/-! ## 342 - Short certificates remain polynomial when replay is polynomial -/
namespace A342_CertificateReplayBudget

theorem replay_work_bound
    (certificateLength perStep input lengthExp stepExp : Nat)
    (lengthBound : certificateLength <= input ^ lengthExp)
    (stepBound : perStep <= input ^ stepExp) :
    certificateLength * perStep <= input ^ (lengthExp + stepExp) := by
  calc
    certificateLength * perStep <=
        input ^ lengthExp * input ^ stepExp :=
      Nat.mul_le_mul lengthBound stepBound
    _ = input ^ (lengthExp + stepExp) := by
      rw [pow_add]

end A342_CertificateReplayBudget

/-! ## 343 - An exact portfolio selector may use any heuristic score -/
namespace A343_ExactPortfolio

open A331_ExactCandidate

variable {Input : Type}

structure Portfolio (specification : Input -> Prop) where
  candidates : List (Candidate specification)
  chosen : Candidate specification
  chosenMember : chosen ∈ candidates

theorem chosen_is_exact
    (specification : Input -> Prop) (portfolio : Portfolio specification)
    (input : Input) :
    portfolio.chosen.decide input = true <-> specification input :=
  portfolio.chosen.exact input

end A343_ExactPortfolio

/-! ## 344 - A learned reversible compiler is acceptable only with exact semantics and cost -/
namespace A344_LearnedCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  constructionCost : Input -> Nat
  evaluationCost : Input -> Nat
  inputSize : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  costBound : forall input,
    constructionCost input + evaluationCost input <=
      inputSize input ^ exponent

theorem compiler_decides_exactly
    (specification : Input -> Prop) (compiler : Compiler specification)
    (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A344_LearnedCompiler

/-! ## 345 - Uniform learned reversible compilers yield the class collapse -/
namespace A345_LearnedCollapse

variable {Language : Type}

structure UniformCompilerCover
    (PClass NPClass : Set Language) where
  compiled : Language -> Prop
  allNPCompiled : forall language, language ∈ NPClass -> compiled language
  compiledInP : forall language, compiled language -> language ∈ PClass

theorem p_eq_np_of_uniform_learned_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (cover : UniformCompilerCover PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language languageNP
  exact cover.compiledInP language
    (cover.allNPCompiled language languageNP)

end A345_LearnedCollapse

end ResearchTwentyFourth
end PIsNPOrNot
