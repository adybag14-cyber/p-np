import ResearchThirtyFourth

namespace PIsNPOrNot.ResearchThirtyFifth

/-! ## 496 - Conditioning fixes a cutset and exposes a residual output image -/
namespace A496_ConditionedImage

variable {Cutset Payload Output : Type}
variable [Fintype Payload] [DecidableEq Output]

 def imageAt
    (feature : Cutset -> Payload -> Output)
    (cut : Cutset) : Finset Output :=
  (Finset.univ : Finset Payload).image (feature cut)

 theorem mem_imageAt
    (feature : Cutset -> Payload -> Output)
    (cut : Cutset) (output : Output) :
    output ∈ imageAt feature cut <->
      exists payload, feature cut payload = output := by
  simp [imageAt]

end A496_ConditionedImage

/-! ## 497 - The global image is the union of every conditioned image -/
namespace A497_CutsetUnionExact

open A496_ConditionedImage
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Cutset Payload Output : Type}
variable [Fintype Cutset] [Fintype Payload] [DecidableEq Output]

 def allImages (feature : Cutset -> Payload -> Output) : Finset Output :=
  (Finset.univ : Finset Cutset).biUnion (imageAt feature)

 theorem allImages_eq_reachable
    (feature : Cutset -> Payload -> Output) :
    allImages feature =
      reachableImage (fun witness : Cutset × Payload =>
        feature witness.1 witness.2) := by
  classical
  ext output
  constructor
  · intro member
    rcases Finset.mem_biUnion.1 member with ⟨cut, _, imageMember⟩
    rcases (mem_imageAt feature cut output).1 imageMember with ⟨payload, valueEq⟩
    exact Finset.mem_image.2 ⟨(cut, payload), Finset.mem_univ _, valueEq⟩
  · intro member
    rcases Finset.mem_image.1 member with ⟨⟨cut, payload⟩, _, valueEq⟩
    exact Finset.mem_biUnion.2 ⟨cut, Finset.mem_univ cut,
      (mem_imageAt feature cut output).2 ⟨payload, valueEq⟩⟩

end A497_CutsetUnionExact

/-! ## 498 - Acceptance after conditioning is an exact finite disjunction -/
namespace A498_ConditionedAcceptance

open A496_ConditionedImage A497_CutsetUnionExact

variable {Cutset Payload : Type}
variable [Fintype Cutset] [Fintype Payload]

 theorem true_mem_iff_some_cut
    (relation : Cutset -> Payload -> Bool) :
    true ∈ allImages relation <->
      exists cut payload, relation cut payload = true := by
  constructor
  · intro member
    rcases Finset.mem_biUnion.1 member with ⟨cut, _, imageMember⟩
    rcases (mem_imageAt relation cut true).1 imageMember with ⟨payload, accepted⟩
    exact ⟨cut, payload, accepted⟩
  · rintro ⟨cut, payload, accepted⟩
    exact Finset.mem_biUnion.2 ⟨cut, Finset.mem_univ cut,
      (mem_imageAt relation cut true).2 ⟨payload, accepted⟩⟩

end A498_ConditionedAcceptance

/-! ## 499 - Cutset union size is at most assignments times residual width -/
namespace A499_CutsetImageBound

open A496_ConditionedImage A497_CutsetUnionExact

variable {Cutset Payload Output : Type}
variable [Fintype Cutset] [Fintype Payload] [DecidableEq Output]

 theorem allImages_card_le
    (feature : Cutset -> Payload -> Output)
    (width : Nat)
    (bounded : forall cut, (imageAt feature cut).card <= width) :
    (allImages feature).card <= Fintype.card Cutset * width := by
  classical
  calc
    (allImages feature).card <=
        ∑ cut : Cutset, (imageAt feature cut).card :=
      Finset.card_biUnion_le
    _ <= ∑ _cut : Cutset, width := by
      exact Finset.sum_le_sum (fun cut _ => bounded cut)
    _ = Fintype.card Cutset * width := by simp

end A499_CutsetImageBound

/-! ## 500 - Exact per-cut tables combine into an exact global table -/
namespace A500_CutsetTable

open ResearchThirtieth.A421_ExactImageTable
open ResearchThirtieth.A425_SeparatorImageTable

variable {Cutset Payload Output : Type}
variable [Fintype Cutset] [DecidableEq Output]

 def cutsetTable
    (feature : Cutset -> Payload -> Output)
    (tables : forall cut, Table (feature cut)) :
    Table (fun witness : Cutset × Payload =>
      feature witness.1 witness.2) :=
  separatorTable feature tables

end A500_CutsetTable

/-! ## 501 - Cutset branching work is assignments times residual work -/
namespace A501_CutsetWork

 theorem cutset_work_bound
    (assignments residualWork input cutExp residualExp : Nat)
    (assignmentBound : assignments <= input ^ cutExp)
    (residualBound : residualWork <= input ^ residualExp) :
    assignments * residualWork <=
      input ^ (cutExp + residualExp) := by
  calc
    assignments * residualWork <=
        input ^ cutExp * input ^ residualExp :=
      Nat.mul_le_mul assignmentBound residualBound
    _ = input ^ (cutExp + residualExp) := by rw [pow_add]

end A501_CutsetWork

/-! ## 502 - Conditioning one Boolean variable is exact Shannon disjunction -/
namespace A502_OneBitConditioning

variable {Payload : Type}

 theorem condition_bool
    (relation : Bool -> Payload -> Prop) :
    (exists witness : Bool × Payload,
      relation witness.1 witness.2) <->
      (exists payload, relation false payload) \/
      (exists payload, relation true payload) := by
  constructor
  · rintro ⟨⟨cut, payload⟩, holds⟩
    cases cut
    · exact Or.inl ⟨payload, holds⟩
    · exact Or.inr ⟨payload, holds⟩
  · intro branch
    rcases branch with ⟨payload, holds⟩ | ⟨payload, holds⟩
    · exact ⟨(false, payload), holds⟩
    · exact ⟨(true, payload), holds⟩

end A502_OneBitConditioning

/-! ## 503 - A k-bit cutset has exactly 2^k branches -/
namespace A503_CutsetBranchCount

 theorem cutset_card (k : Nat) :
    Fintype.card (Fin k -> Bool) = 2 ^ k := by
  simp

end A503_CutsetBranchCount

/-! ## 504 - Adding one cut bit doubles the ambient branch count -/
namespace A504_OneMoreCutBit

 theorem one_more_bit (k : Nat) :
    2 ^ (k + 1) = 2 ^ k * 2 := by
  rw [pow_succ]

end A504_OneMoreCutBit

/-! ## 505 - A certified cutset records exact residual solvers for every branch -/
namespace A505_CertifiedCutset

variable {Cutset Input : Type}

structure Certificate (specification : Input -> Prop) where
  branchAnswer : Input -> Cutset -> Bool
  decide : Input -> Bool
  branchExact : forall input cut,
    branchAnswer input cut = true -> specification input
  covered : forall input,
    specification input -> exists cut, branchAnswer input cut = true
  decideExact : forall input,
    decide input = true <-> exists cut, branchAnswer input cut = true

 theorem decide_correct
    (specification : Input -> Prop)
    (certificate : Certificate (Cutset := Cutset) specification)
    (input : Input) :
    certificate.decide input = true <-> specification input := by
  constructor
  · intro accepted
    rcases (certificate.decideExact input).1 accepted with ⟨cut, branchAccepted⟩
    exact certificate.branchExact input cut branchAccepted
  · intro holds
    rcases certificate.covered input holds with ⟨cut, branchAccepted⟩
    exact (certificate.decideExact input).2 ⟨cut, branchAccepted⟩

end A505_CertifiedCutset

/-! ## 506 - A cutset certificate must expose its residual table width -/
namespace A506_ResidualWidthCertificate

structure WidthCertificate where
  branches : Nat
  residualWidth : Nat
  residualWork : Nat
  totalWork : Nat
  workBound : totalWork <= branches * residualWork

 theorem certified_work_le
    (certificate : WidthCertificate) :
    certificate.totalWork <=
      certificate.branches * certificate.residualWork :=
  certificate.workBound

end A506_ResidualWidthCertificate

/-! ## 507 - Polynomial cutset branches and residual work compose -/
namespace A507_CutsetPolynomialBudget

 theorem total_polynomial
    (branches residualWork total input branchExp residualExp : Nat)
    (totalBound : total <= branches * residualWork)
    (branchBound : branches <= input ^ branchExp)
    (residualBound : residualWork <= input ^ residualExp) :
    total <= input ^ (branchExp + residualExp) := by
  exact le_trans totalBound (A501_CutsetWork.cutset_work_bound
    branches residualWork input branchExp residualExp branchBound residualBound)

end A507_CutsetPolynomialBudget

/-! ## 508 - Excess total work localizes to branch count or residual work -/
namespace A508_CutsetObstruction

 theorem branch_or_residual_exceeds
    (branches residualWork input branchExp residualExp : Nat)
    (tooLarge : input ^ (branchExp + residualExp) <
      branches * residualWork) :
    input ^ branchExp < branches \/
      input ^ residualExp < residualWork := by
  by_contra neither
  push Not at neither
  have productBound := Nat.mul_le_mul neither.1 neither.2
  rw [← pow_add] at productBound
  omega

end A508_CutsetObstruction

/-! ## 509 - A cutset portfolio may safely retain an exact fallback -/
namespace A509_CutsetFallback

 def choose
    (cutset fallback : Bool)
    (recognized : Bool) : Bool :=
  if recognized then cutset else fallback

 theorem choose_exact
    (specification : Prop)
    (cutset fallback recognized : Bool)
    (cutsetExact : cutset = true <-> specification)
    (fallbackExact : fallback = true <-> specification) :
    choose cutset fallback recognized = true <-> specification := by
  unfold choose
  split <;> assumption

end A509_CutsetFallback

/-! ## 510 - Uniform polynomial cutset compilers imply P = NP -/
namespace A510_CutsetCollapse

variable {Language : Type}

structure UniformCutsets
    (PClass NPClass : Set Language) where
  hasCutsetCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCutsetCompiler language
  compilerGivesP : forall language,
    hasCutsetCompiler language -> language ∈ PClass

 theorem p_eq_np_of_uniform_cutsets
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (cutsets : UniformCutsets PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact cutsets.compilerGivesP language
    (cutsets.allNPHaveCompiler language inNP)

end A510_CutsetCollapse

end PIsNPOrNot.ResearchThirtyFifth
