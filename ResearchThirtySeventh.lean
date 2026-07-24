import ResearchThirtySixth

namespace PIsNPOrNot.ResearchThirtySeventh

/-! ## 526 - A cut assignment is represented by its complete residual behaviour -/
namespace A526_ResidualSignature

variable {Cut Payload Output : Type}

def signature (feature : Cut -> Payload -> Output) (cut : Cut) : Payload -> Output :=
  feature cut

theorem signature_apply
    (feature : Cut -> Payload -> Output) (cut : Cut) (payload : Payload) :
    signature feature cut payload = feature cut payload :=
  rfl

end A526_ResidualSignature

/-! ## 527 - Equality of residual signatures is an equivalence relation -/
namespace A527_SignatureEquivalence

open A526_ResidualSignature

variable {Cut Payload Output : Type}

abbrev Equivalent (feature : Cut -> Payload -> Output) (left right : Cut) : Prop :=
  signature feature left = signature feature right

theorem refl (feature : Cut -> Payload -> Output) (cut : Cut) :
    Equivalent feature cut cut :=
  rfl

theorem symm
    (feature : Cut -> Payload -> Output) {left right : Cut}
    (same : Equivalent feature left right) :
    Equivalent feature right left :=
  same.symm

theorem trans
    (feature : Cut -> Payload -> Output) {first second third : Cut}
    (firstSecond : Equivalent feature first second)
    (secondThird : Equivalent feature second third) :
    Equivalent feature first third :=
  firstSecond.trans secondThird

end A527_SignatureEquivalence

/-! ## 528 - Equivalent cut assignments agree on every residual payload -/
namespace A528_SignatureSafety

open A526_ResidualSignature A527_SignatureEquivalence

variable {Cut Payload Output : Type}

theorem equal_output
    (feature : Cut -> Payload -> Output) {left right : Cut}
    (same : Equivalent feature left right) (payload : Payload) :
    feature left payload = feature right payload := by
  exact congrFun same payload

end A528_SignatureSafety

/-! ## 529 - Equivalent cuts have exactly the same reachable output image -/
namespace A529_SignatureImageSafety

open A526_ResidualSignature A527_SignatureEquivalence
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Cut Payload Output : Type}
variable [Fintype Payload] [DecidableEq Output]

theorem equal_reachable_images
    (feature : Cut -> Payload -> Output) {left right : Cut}
    (same : Equivalent feature left right) :
    reachableImage (feature left) = reachableImage (feature right) := by
  change feature left = feature right at same
  rw [same]

end A529_SignatureImageSafety

/-! ## 530 - The semantic quotient is the finite image of the signature map -/
namespace A530_SignatureImage

open A526_ResidualSignature

variable {Cut Payload Output : Type}
variable [Fintype Cut]

noncomputable def signatures (feature : Cut -> Payload -> Output) :
    Finset (Payload -> Output) := by
  classical
  exact (Finset.univ : Finset Cut).image (signature feature)

theorem signature_mem
    (feature : Cut -> Payload -> Output) (cut : Cut) :
    signature feature cut ∈ signatures feature := by
  classical
  exact Finset.mem_image.2 ⟨cut, Finset.mem_univ cut, rfl⟩

end A530_SignatureImage

/-! ## 531 - Semantic quotient size never exceeds the raw cut-assignment count -/
namespace A531_SignatureCardinality

open A526_ResidualSignature A530_SignatureImage

variable {Cut Payload Output : Type}
variable [Fintype Cut]

theorem signature_card_le_raw
    (feature : Cut -> Payload -> Output) :
    (signatures feature).card <= Fintype.card Cut := by
  classical
  simpa [signatures] using
    (Finset.card_image_le :
      ((Finset.univ : Finset Cut).image (signature feature)).card <=
        (Finset.univ : Finset Cut).card)

end A531_SignatureCardinality

/-! ## 532 - A representative cover keeps one cut for every residual signature -/
namespace A532_RepresentativeCover

open A526_ResidualSignature

variable {Cut Payload Output : Type}

structure Cover (feature : Cut -> Payload -> Output) where
  representatives : Finset Cut
  covers : forall cut, exists representative,
    representative ∈ representatives /\
      signature feature representative = signature feature cut

end A532_RepresentativeCover

/-! ## 533 - Every cut has a pointwise-equivalent representative -/
namespace A533_RepresentativeSafety

open A526_ResidualSignature A528_SignatureSafety A532_RepresentativeCover

variable {Cut Payload Output : Type}

theorem represented_output
    (feature : Cut -> Payload -> Output)
    (cover : Cover feature) (cut : Cut) (payload : Payload) :
    exists representative,
      representative ∈ cover.representatives /\
      feature representative payload = feature cut payload := by
  rcases cover.covers cut with ⟨representative, member, same⟩
  exact ⟨representative, member, equal_output feature same payload⟩

end A533_RepresentativeSafety

/-! ## 534 - Searching one representative per signature preserves existence exactly -/
namespace A534_RepresentativeExistence

open A526_ResidualSignature A532_RepresentativeCover

variable {Cut Payload Output : Type}

theorem exists_over_representatives
    (feature : Cut -> Payload -> Output)
    (accept : Output -> Prop)
    (cover : Cover feature) :
    (exists cut payload, accept (feature cut payload)) <->
      exists representative,
        representative ∈ cover.representatives /\
        exists payload, accept (feature representative payload) := by
  constructor
  · rintro ⟨cut, payload, accepted⟩
    rcases cover.covers cut with ⟨representative, member, same⟩
    refine ⟨representative, member, payload, ?_⟩
    change feature representative = feature cut at same
    have outputSame := congrFun same payload
    rw [outputSame]
    exact accepted
  · rintro ⟨representative, _member, payload, accepted⟩
    exact ⟨representative, payload, accepted⟩

end A534_RepresentativeExistence

/-! ## 535 - Representative output tables reconstruct the complete global image -/
namespace A535_RepresentativeImageUnion

open A526_ResidualSignature A532_RepresentativeCover
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Cut Payload Output : Type}
variable [Fintype Cut] [Fintype Payload] [DecidableEq Output]

noncomputable def allOutputs (feature : Cut -> Payload -> Output) : Finset Output := by
  classical
  exact (Finset.univ : Finset Cut).biUnion (fun cut => reachableImage (feature cut))

noncomputable def representativeOutputs
    (feature : Cut -> Payload -> Output) (cover : Cover feature) : Finset Output := by
  classical
  exact cover.representatives.biUnion (fun cut => reachableImage (feature cut))

theorem representative_outputs_exact
    (feature : Cut -> Payload -> Output) (cover : Cover feature) :
    representativeOutputs feature cover = allOutputs feature := by
  classical
  ext output
  constructor
  · intro member
    rcases Finset.mem_biUnion.1 member with ⟨cut, _cutMember, outputMember⟩
    exact Finset.mem_biUnion.2 ⟨cut, Finset.mem_univ cut, outputMember⟩
  · intro member
    rcases Finset.mem_biUnion.1 member with ⟨cut, _cutMember, outputMember⟩
    rcases cover.covers cut with ⟨representative, representativeMember, same⟩
    have imageSame : reachableImage (feature representative) =
        reachableImage (feature cut) := by
      change feature representative = feature cut at same
      rw [same]
    exact Finset.mem_biUnion.2
      ⟨representative, representativeMember, by
        rw [imageSame]
        exact outputMember⟩

end A535_RepresentativeImageUnion

/-! ## 536 - Representative count is bounded by the raw finite cut space -/
namespace A536_RepresentativeCardinality

open A532_RepresentativeCover

variable {Cut Payload Output : Type}
variable [Fintype Cut]

theorem representative_card_le_raw
    (feature : Cut -> Payload -> Output) (cover : Cover feature) :
    cover.representatives.card <= Fintype.card Cut := by
  simpa using Finset.card_le_univ cover.representatives

end A536_RepresentativeCardinality

/-! ## 537 - All impossible branches share the same empty residual relation -/
namespace A537_ImpossibleSignature

variable {Cut Payload : Type}

abbrev Relation := Cut -> Payload -> Prop

abbrev Impossible (relation : Relation (Cut := Cut) (Payload := Payload))
    (cut : Cut) : Prop :=
  forall payload, Not (relation cut payload)

theorem impossible_signatures_equal
    (relation : Relation (Cut := Cut) (Payload := Payload))
    {left right : Cut}
    (leftImpossible : Impossible relation left)
    (rightImpossible : Impossible relation right) :
    relation left = relation right := by
  funext payload
  apply propext
  constructor
  · intro holds
    exact False.elim (leftImpossible payload holds)
  · intro holds
    exact False.elim (rightImpossible payload holds)

end A537_ImpossibleSignature

/-! ## 538 - Solving one representative per class has class-count times width cost -/
namespace A538_RepresentativeWork

open A532_RepresentativeCover

variable {Cut Payload Output : Type}

theorem total_work_bound
    (feature : Cut -> Payload -> Output)
    (cover : Cover feature)
    (work : Cut -> Nat) (maximum : Nat)
    (bounded : forall representative,
      representative ∈ cover.representatives -> work representative <= maximum) :
    (cover.representatives.sum work) <= cover.representatives.card * maximum := by
  calc
    cover.representatives.sum work <= cover.representatives.sum (fun _ => maximum) := by
      exact Finset.sum_le_sum (fun representative member => bounded representative member)
    _ = cover.representatives.card * maximum := by simp

end A538_RepresentativeWork

/-! ## 539 - Quotient work never exceeds raw branching when representatives are no more expensive -/
namespace A539_QuotientDominance

open A532_RepresentativeCover

variable {Cut Payload Output : Type}
variable [Fintype Cut]

theorem quotient_work_le_raw
    (feature : Cut -> Payload -> Output)
    (cover : Cover feature) (maximum : Nat) :
    cover.representatives.card * maximum <= Fintype.card Cut * maximum := by
  exact Nat.mul_le_mul_right maximum
    (ResearchThirtySeventh.A536_RepresentativeCardinality.representative_card_le_raw
      feature cover)

end A539_QuotientDominance

/-! ## 540 - Uniform polynomial semantic-quotient compilers imply P = NP -/
namespace A540_SemanticQuotientCollapse

variable {Language : Type}

structure UniformSemanticQuotients (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_semantic_quotients
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformSemanticQuotients PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A540_SemanticQuotientCollapse

end PIsNPOrNot.ResearchThirtySeventh
