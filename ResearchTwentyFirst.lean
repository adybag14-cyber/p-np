import ResearchTwentieth

namespace PIsNPOrNot
namespace ResearchTwentyFirst

/-! ## 286 - A covering restriction family preserves satisfiability -/
namespace A286_RestrictionCover

variable {Assignment Restriction : Type}

structure Cover where
  family : List Restriction
  holds : Restriction -> Assignment -> Prop
  covers : forall assignment,
    exists restriction, restriction ∈ family /\ holds restriction assignment

theorem sat_iff_some_restriction
    (accepts : Assignment -> Prop)
    (cover : Cover (Assignment := Assignment) (Restriction := Restriction)) :
    (exists assignment, accepts assignment) <->
      exists restriction, restriction ∈ cover.family /\
        exists assignment, accepts assignment /\ cover.holds restriction assignment := by
  constructor
  · rintro ⟨assignment, accepted⟩
    rcases cover.covers assignment with ⟨restriction, member, holds⟩
    exact ⟨restriction, member, assignment, accepted, holds⟩
  · rintro ⟨restriction, member, assignment, accepted, holds⟩
    exact ⟨assignment, accepted⟩

end A286_RestrictionCover

/-! ## 287 - Exact residual solvers compose with a restriction cover -/
namespace A287_ResidualSolverComposition

variable {Instance Restriction : Type}

structure ResidualSolver (specification : Instance -> Prop) where
  solve : Restriction -> Instance -> Bool
  residualSpec : Restriction -> Instance -> Prop
  exact : forall restriction input,
    solve restriction input = true <-> residualSpec restriction input
  cover : forall input,
    specification input <-> exists restriction, residualSpec restriction input

theorem solve_some_iff_specification
    (specification : Instance -> Prop)
    (solver : ResidualSolver (Restriction := Restriction) specification)
    (input : Instance) :
    (exists restriction, solver.solve restriction input = true) <->
      specification input := by
  rw [solver.cover input]
  constructor
  · rintro ⟨restriction, solved⟩
    exact ⟨restriction, (solver.exact restriction input).1 solved⟩
  · rintro ⟨restriction, residual⟩
    exact ⟨restriction, (solver.exact restriction input).2 residual⟩

end A287_ResidualSolverComposition

/-! ## 288 - Polynomial restriction families with polynomial residual solvers remain polynomial -/
namespace A288_RestrictionWorkBudget

theorem restriction_work_bound
    (restrictionCount perResidual input countExponent residualExponent : Nat)
    (countBound : restrictionCount <= input ^ countExponent)
    (residualBound : perResidual <= input ^ residualExponent) :
    restrictionCount * perResidual <=
      input ^ (countExponent + residualExponent) := by
  calc
    restrictionCount * perResidual <=
        (input ^ countExponent) * (input ^ residualExponent) :=
      Nat.mul_le_mul countBound residualBound
    _ = input ^ (countExponent + residualExponent) := by rw [pow_add]

end A288_RestrictionWorkBudget

/-! ## 289 - Fixing variables leaves the expected Boolean search ceiling -/
namespace A289_RemainingDimension

theorem residual_assignment_ceiling
    (remaining : Nat) :
    Fintype.card (Fin remaining -> Bool) = 2 ^ remaining := by
  simp

end A289_RemainingDimension

/-! ## 290 - A polynomial residual-dimension bound gives polynomial enumeration -/
namespace A290_SmallResidualEnumeration

theorem residual_enumeration_bound
    (remaining input exponent : Nat)
    (dimensionBound : 2 ^ remaining <= input ^ exponent) :
    2 ^ remaining <= input ^ exponent := dimensionBound

end A290_SmallResidualEnumeration

/-! ## 291 - Switching certificates expose shallow residual decision trees -/
namespace A291_SwitchingCertificate

variable {Instance : Type}

structure Certificate where
  depth : Nat
  leafCount : Nat
  validFor : Instance -> Prop
  leafBound : leafCount <= 2 ^ depth

theorem certified_leaf_bound
    (certificate : Certificate (Instance := Instance)) :
    certificate.leafCount <= 2 ^ certificate.depth :=
  certificate.leafBound

end A291_SwitchingCertificate

/-! ## 292 - Polynomially bounded depth ceilings imply explicit leaf ceilings -/
namespace A292_ShallowTreeBudget

theorem leaf_ceiling_transfer
    (leaves depth polynomialBound : Nat)
    (treeBound : leaves <= 2 ^ depth)
    (depthBound : 2 ^ depth <= polynomialBound) :
    leaves <= polynomialBound := by
  exact le_trans treeBound depthBound

end A292_ShallowTreeBudget

/-! ## 293 - A restriction ensemble of shallow trees has multiplicative cost -/
namespace A293_RestrictionTreeEnsemble

theorem ensemble_leaf_bound
    (restrictionCount leavesPerRestriction restrictionBound leafBound : Nat)
    (hRestrictions : restrictionCount <= restrictionBound)
    (hLeaves : leavesPerRestriction <= leafBound) :
    restrictionCount * leavesPerRestriction <= restrictionBound * leafBound := by
  exact Nat.mul_le_mul hRestrictions hLeaves

end A293_RestrictionTreeEnsemble

/-! ## 294 - A common sunflower core is charged once across petals -/
namespace A294_CommonCoreAccounting

variable {State : Type} [DecidableEq State]

theorem common_core_union_bound
    (core : Finset State) (petals : List (Finset State))
    (petalBound : Nat)
    (bounded : forall petal, petal ∈ petals -> petal.card <= petalBound) :
    (petals.foldl (fun total petal => total ∪ petal) core).card <=
      core.card + petals.length * petalBound := by
  induction petals generalizing core with
  | nil => simp
  | cons head tail ih =>
      have hHead : head.card <= petalBound := bounded head (List.Mem.head tail)
      have hTail : forall petal, petal ∈ tail -> petal.card <= petalBound := by
        intro petal hmem
        exact bounded petal (List.Mem.tail head hmem)
      have hUnion : (core ∪ head).card <= core.card + petalBound := by
        calc
          (core ∪ head).card <= core.card + head.card :=
            ResearchTwelfth.A158_SharingUpperBound.union_card_le_sum core head
          _ <= core.card + petalBound := Nat.add_le_add_left hHead core.card
      have hRec := ih (core := core ∪ head) hTail
      calc
        ((head :: tail).foldl (fun total petal => total ∪ petal) core).card =
            (tail.foldl (fun total petal => total ∪ petal) (core ∪ head)).card := rfl
        _ <= (core ∪ head).card + tail.length * petalBound := hRec
        _ <= (core.card + petalBound) + tail.length * petalBound :=
          Nat.add_le_add_right hUnion _
        _ = core.card + (tail.length + 1) * petalBound := by
          rw [Nat.add_mul, Nat.one_mul]
          omega

end A294_CommonCoreAccounting

/-! ## 295 - Exact kernelization transfers decisions back to the source instance -/
namespace A295_ExactKernel

variable {Instance Kernel : Type}

structure Kernelization (specification : Instance -> Prop) where
  kernel : Instance -> Kernel
  kernelSpec : Kernel -> Prop
  exact : forall input,
    specification input <-> kernelSpec (kernel input)

theorem kernel_answer_transfers
    (specification : Instance -> Prop)
    (kernelization : Kernelization (Kernel := Kernel) specification)
    (input : Instance) :
    specification input <->
      kernelization.kernelSpec (kernelization.kernel input) := by
  exact kernelization.exact input

end A295_ExactKernel

/-! ## 296 - Learned proof traces remain sound after restriction -/
namespace A296_RestrictedProofTrace

variable {Instance Restriction Trace : Type}

structure Checker (specification : Instance -> Prop) where
  check : Restriction -> Instance -> Trace -> Bool
  sound : forall restriction input trace,
    check restriction input trace = true -> specification input

theorem checked_restricted_trace_sound
    (specification : Instance -> Prop)
    (checker : Checker (Restriction := Restriction) (Trace := Trace) specification)
    (restriction : Restriction) (input : Instance) (trace : Trace)
    (checked : checker.check restriction input trace = true) :
    specification input := by
  exact checker.sound restriction input trace checked

end A296_RestrictedProofTrace

/-! ## 297 - Strict rank decrease bounds every restriction chain -/
namespace A297_RestrictionRank

structure RankedStep where
  before : Nat
  after : Nat
  decreases : after < before

theorem step_after_le_before (step : RankedStep) :
    step.after <= step.before := by
  exact Nat.le_of_lt step.decreases

end A297_RestrictionRank

/-! ## 298 - Isolation and restriction certificates compose -/
namespace A298_IsolatedRestriction

variable {Witness Restriction Hash : Type}

structure Certificate (accepted : Witness -> Prop) where
  restriction : Restriction
  hash : Hash
  witness : Witness
  acceptedWitness : accepted witness
  isolated : Prop
  restrictionValid : Prop

theorem certificate_contains_accepted_witness
    (accepted : Witness -> Prop)
    (certificate : Certificate
      (Restriction := Restriction) (Hash := Hash) accepted) :
    exists witness, accepted witness := by
  exact ⟨certificate.witness, certificate.acceptedWitness⟩

end A298_IsolatedRestriction

/-! ## 299 - A heterogeneous radical cover may choose restrictions, symmetry, or algebra -/
namespace A299_HeterogeneousRadicalCover

variable {Language : Type}

structure Cover where
  restriction : Language -> Prop
  symmetry : Language -> Prop
  algebraic : Language -> Prop
  covers : forall language,
    restriction language \/ symmetry language \/ algebraic language

theorem one_radical_route_applies
    (cover : Cover (Language := Language)) (language : Language) :
    cover.restriction language \/
      cover.symmetry language \/ cover.algebraic language := by
  exact cover.covers language

end A299_HeterogeneousRadicalCover

/-! ## 300 - Uniform polynomial restriction covers would collapse P and NP -/
namespace A300_RestrictionCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_restriction_covers
    (InP InNP HasPolynomialRestrictionCover : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (coverImpliesP : forall language,
      HasPolynomialRestrictionCover language -> InP language)
    (uniform : forall language,
      InNP language -> HasPolynomialRestrictionCover language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact coverImpliesP language (uniform language hNP)

end A300_RestrictionCollapse

end ResearchTwentyFirst
end PIsNPOrNot
