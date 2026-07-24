import ResearchThirtyFifth

namespace PIsNPOrNot.ResearchThirtySixth

/-! ## 511 - Conditioning substitutes a Boolean cut coordinate immediately -/
namespace A511_SubstitutedResidual

variable {Payload Output : Type}

 def residual
    (feature : Bool -> Payload -> Output)
    (cut : Bool) : Payload -> Output :=
  feature cut

 theorem residual_apply
    (feature : Bool -> Payload -> Output)
    (cut : Bool) (payload : Payload) :
    residual feature cut payload = feature cut payload :=
  rfl

end A511_SubstitutedResidual

/-! ## 512 - Global existence is the exact union of substituted residuals -/
namespace A512_SubstitutionShannon

variable {Payload : Type}

 theorem exists_iff_residual_disjunction
    (relation : Bool -> Payload -> Prop) :
    (exists cut payload, relation cut payload) <->
      (exists payload, relation false payload) \/
      (exists payload, relation true payload) := by
  constructor
  · rintro ⟨cut, payload, holds⟩
    cases cut
    · exact Or.inl ⟨payload, holds⟩
    · exact Or.inr ⟨payload, holds⟩
  · intro branch
    rcases branch with ⟨payload, holds⟩ | ⟨payload, holds⟩
    · exact ⟨false, payload, holds⟩
    · exact ⟨true, payload, holds⟩

end A512_SubstitutionShannon

/-! ## 513 - Output images are exactly the union of substituted branch images -/
namespace A513_SubstitutedImageUnion

open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Payload Output : Type}
variable [Fintype Payload] [DecidableEq Output]

 theorem image_eq_branch_union
    (feature : Bool -> Payload -> Output) :
    reachableImage (fun witness : Bool × Payload =>
      feature witness.1 witness.2) =
      reachableImage (feature false) ∪ reachableImage (feature true) := by
  classical
  ext output
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨⟨cut, payload⟩, _, valueEq⟩
    cases cut
    · exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨payload, Finset.mem_univ payload, valueEq⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨payload, Finset.mem_univ payload, valueEq⟩)
  · intro member
    rcases Finset.mem_union.1 member with falseMember | trueMember
    · rcases Finset.mem_image.1 falseMember with ⟨payload, _, valueEq⟩
      exact Finset.mem_image.2 ⟨(false, payload), Finset.mem_univ _, valueEq⟩
    · rcases Finset.mem_image.1 trueMember with ⟨payload, _, valueEq⟩
      exact Finset.mem_image.2 ⟨(true, payload), Finset.mem_univ _, valueEq⟩

end A513_SubstitutedImageUnion

/-! ## 514 - Exact substituted tables reconstruct the original image table -/
namespace A514_SubstitutedTables

open ResearchThirtieth.A421_ExactImageTable
open ResearchThirtieth.A424_BranchImageTable

variable {Payload Output : Type}
variable [DecidableEq Output]

 def combine
    (feature : Bool -> Payload -> Output)
    (falseTable : Table (feature false))
    (trueTable : Table (feature true)) :
    Table (ResearchTwentyNinth.A410_BranchFeatureImage.branchFeature
      (feature false) (feature true)) :=
  branchTable (feature false) (feature true) falseTable trueTable

end A514_SubstitutedTables

/-! ## 515 - Empty impossible branches contribute no output rows -/
namespace A515_ImpossibleBranch

variable {Output : Type}
variable [DecidableEq Output]

 theorem empty_union (rows : Finset Output) :
    (∅ : Finset Output) ∪ rows = rows := by
  simp

 theorem union_empty (rows : Finset Output) :
    rows ∪ (∅ : Finset Output) = rows := by
  simp

end A515_ImpossibleBranch

/-! ## 516 - A k-bit internal cutset still has exactly 2^k assignments -/
namespace A516_InternalCutsetCount

 theorem internal_cutset_card (k : Nat) :
    Fintype.card (Fin k -> Bool) = 2 ^ k := by
  simp

end A516_InternalCutsetCount

/-! ## 517 - Exact internal-wire conditioning is independent of wire meaning -/
namespace A517_ArbitraryWireConditioning

variable {WireAssignment Payload : Type}

structure Decomposition where
  cutValue : WireAssignment -> Bool
  residualPayload : WireAssignment -> Payload
  rebuild : Bool -> Payload -> WireAssignment
  rebuildExact : forall assignment,
    rebuild (cutValue assignment) (residualPayload assignment) = assignment

 theorem exists_transport
    (decomposition : Decomposition
      (WireAssignment := WireAssignment) (Payload := Payload))
    (relation : WireAssignment -> Prop) :
    (exists assignment, relation assignment) <->
      exists cut payload, relation (decomposition.rebuild cut payload) := by
  constructor
  · rintro ⟨assignment, holds⟩
    exact ⟨decomposition.cutValue assignment,
      decomposition.residualPayload assignment, by
        simpa [decomposition.rebuildExact assignment] using holds⟩
  · rintro ⟨cut, payload, holds⟩
    exact ⟨decomposition.rebuild cut payload, holds⟩

end A517_ArbitraryWireConditioning

/-! ## 518 - Branching cost must include every substituted residual -/
namespace A518_SubstitutedWork

 theorem total_work_bound
    (branchWork : List Nat) (branches maxWork : Nat)
    (branchBound : branchWork.length <= branches)
    (workBound : forall work, work ∈ branchWork -> work <= maxWork) :
    branchWork.sum <= branches * maxWork := by
  have helper : forall values : List Nat,
      (forall work, work ∈ values -> work <= maxWork) ->
        values.sum <= values.length * maxWork := by
    intro values
    induction values with
    | nil => intro bounded; simp
    | cons head tail ih =>
        intro bounded
        have headBound : head <= maxWork := bounded head (by simp)
        have tailBound : forall work, work ∈ tail -> work <= maxWork := by
          intro work member
          exact bounded work (by simp [member])
        have recursive := ih tailBound
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum <= maxWork + tail.length * maxWork :=
            Nat.add_le_add headBound recursive
          _ = (tail.length + 1) * maxWork := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact le_trans (helper branchWork workBound)
    (Nat.mul_le_mul_right maxWork branchBound)

end A518_SubstitutedWork

/-! ## 519 - Halving residual work only offsets one additional branch bit -/
namespace A519_BranchWidthTradeoff

 theorem doubling_branches_doubling_width_identity
    (branches residualWork : Nat) :
    (2 * branches) * residualWork =
      branches * (2 * residualWork) := by
  simp [Nat.mul_left_comm, Nat.mul_comm]

 theorem half_saving_can_break_even
    (branches reduced original : Nat)
    (half : original = 2 * reduced) :
    (2 * branches) * reduced = branches * original := by
  subst original
  simp [Nat.mul_left_comm, Nat.mul_comm]

end A519_BranchWidthTradeoff

/-! ## 520 - The correct cutset score is total branch work, not peak width alone -/
namespace A520_TotalCutsetScore

structure Score where
  branches : Nat
  peakResidualWork : Nat

deriving DecidableEq

 def total (score : Score) : Nat :=
  score.branches * score.peakResidualWork

 theorem lower_peak_not_enough
    (old new : Score)
    (_lowerPeak : new.peakResidualWork < old.peakResidualWork)
    (notBetter : total old <= total new) :
    ¬ (total new < total old) := by
  exact Nat.not_lt_of_ge notBetter

end A520_TotalCutsetScore

/-! ## 521 - Certified cutset candidates carry exact answers and measured work -/
namespace A521_CutsetCandidate

structure Candidate (specification : Prop) where
  answer : Bool
  totalWork : Nat
  exact : answer = true <-> specification

 theorem candidate_exact
    (specification : Prop) (candidate : Candidate specification) :
    candidate.answer = true <-> specification :=
  candidate.exact

end A521_CutsetCandidate

/-! ## 522 - Selecting a lower-work exact cutset preserves the baseline -/
namespace A522_BaselineSafeCutsetChoice

open A521_CutsetCandidate

 def choose
    {specification : Prop}
    (baseline candidate : Candidate specification) :
    Candidate specification :=
  if candidate.totalWork < baseline.totalWork then candidate else baseline

 theorem chosen_exact
    {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).answer = true <-> specification := by
  unfold choose
  split
  · exact candidate.exact
  · exact baseline.exact

 theorem chosen_work_le_baseline
    {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).totalWork <= baseline.totalWork := by
  unfold choose
  split
  · omega
  · exact le_rfl

end A522_BaselineSafeCutsetChoice

/-! ## 523 - A monotone cutset-improvement chain never exceeds its seed -/
namespace A523_CutsetImprovementChain

structure Candidate where
  answer : Bool
  work : Nat

inductive Improves : Candidate -> Candidate -> Prop
  | step (old new : Candidate)
      (sameAnswer : new.answer = old.answer)
      (workDrops : new.work <= old.work) : Improves old new

inductive Chain : Candidate -> Candidate -> Prop
  | refl (candidate : Candidate) : Chain candidate candidate
  | tail {start middle finish : Candidate}
      (prior : Chain start middle)
      (step : Improves middle finish) : Chain start finish

 theorem final_work_le_initial
    {start finish : Candidate}
    (chain : Chain start finish) :
    finish.work <= start.work := by
  induction chain with
  | refl => exact le_rfl
  | tail prior improvement ih =>
      cases improvement with
      | step sameAnswer workDrops =>
          exact le_trans workDrops ih

end A523_CutsetImprovementChain

/-! ## 524 - Graph-width proxies are not themselves semantic work guarantees -/
namespace A524_ProxyScoreBarrier

 theorem proxy_and_work_can_disagree :
    exists proxyA proxyB workA workB : Nat,
      proxyA < proxyB /\ workB < workA := by
  exact ⟨0, 1, 2, 1, by omega, by omega⟩

end A524_ProxyScoreBarrier

/-! ## 525 - Uniform polynomial internal-cutset compilers imply P = NP -/
namespace A525_InternalCutsetCollapse

variable {Language : Type}

structure UniformInternalCutsets
    (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language,
    hasCompiler language -> language ∈ PClass

 theorem p_eq_np_of_uniform_internal_cutsets
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformInternalCutsets PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A525_InternalCutsetCollapse

end PIsNPOrNot.ResearchThirtySixth
