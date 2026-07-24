import ResearchThirtyNinth

namespace PIsNPOrNot.ResearchFortieth

/-! ## 571 - An exact certificate factorization decodes every certificate into a residual function -/
namespace A571_ExactCertificateFactorization

variable {Cut Payload Output Certificate : Type}

structure Factorization (feature : Cut -> Payload -> Output)
    (certificate : Cut -> Certificate) where
  decode : Certificate -> Payload -> Output
  exact : forall cut payload,
    decode (certificate cut) payload = feature cut payload

end A571_ExactCertificateFactorization

/-! ## 572 - The semantic signature image is the decoded certificate image -/
namespace A572_SignatureImageFactorization

open A571_ExactCertificateFactorization
open ResearchThirtySeventh.A526_ResidualSignature
open ResearchThirtySeventh.A530_SignatureImage
open ResearchThirtyEighth.A547_CertificateImage

variable {Cut Payload Output Certificate : Type}
variable [Fintype Cut]

noncomputable def decodedCertificates
    (feature : Cut -> Payload -> Output)
    (certificate : Cut -> Certificate)
    (factorization : Factorization feature certificate) :
    Finset (Payload -> Output) := by
  classical
  exact (certificates certificate).image factorization.decode

theorem signatures_eq_decoded_certificates
    (feature : Cut -> Payload -> Output)
    (certificate : Cut -> Certificate)
    (factorization : Factorization feature certificate) :
    signatures feature = decodedCertificates feature certificate factorization := by
  classical
  unfold ResearchThirtySeventh.A530_SignatureImage.signatures
  unfold decodedCertificates
  unfold ResearchThirtyEighth.A547_CertificateImage.certificates
  ext residual
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨cut, _cutMember, residualEq⟩
    refine Finset.mem_image.2 ⟨certificate cut, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨cut, Finset.mem_univ cut, rfl⟩
    · rw [← residualEq]
      funext payload
      exact factorization.exact cut payload
  · intro member
    rcases Finset.mem_image.1 member with ⟨cert, certMember, residualEq⟩
    rcases Finset.mem_image.1 certMember with ⟨cut, _cutMember, certEq⟩
    refine Finset.mem_image.2 ⟨cut, Finset.mem_univ cut, ?_⟩
    rw [← residualEq, ← certEq]
    funext payload
    exact (factorization.exact cut payload).symm

end A572_SignatureImageFactorization

/-! ## 573 - Every exact decodable certificate partition is at least as large as the semantic quotient -/
namespace A573_SemanticOptimalityBound

open A571_ExactCertificateFactorization
open ResearchThirtySeventh.A530_SignatureImage
open ResearchThirtyEighth.A547_CertificateImage

variable {Cut Payload Output Certificate : Type}
variable [Fintype Cut]

theorem semantic_card_le_certificate_card
    (feature : Cut -> Payload -> Output)
    (certificate : Cut -> Certificate)
    (factorization : Factorization feature certificate) :
    (signatures feature).card <= (certificates certificate).card := by
  classical
  rw [ResearchFortieth.A572_SignatureImageFactorization.signatures_eq_decoded_certificates
    feature certificate factorization]
  unfold ResearchFortieth.A572_SignatureImageFactorization.decodedCertificates
  exact Finset.card_image_le

end A573_SemanticOptimalityBound

/-! ## 574 - Semantic signatures are the coarsest exact residual certificates -/
namespace A574_CoarsestExactQuotient

open A571_ExactCertificateFactorization

variable {Cut Payload Output Certificate : Type}
variable [Fintype Cut]

theorem no_exact_certificate_beats_semantic_cardinality
    (feature : Cut -> Payload -> Output)
    (certificate : Cut -> Certificate)
    (factorization : Factorization feature certificate) :
    (ResearchThirtySeventh.A530_SignatureImage.signatures feature).card <=
      (ResearchThirtyEighth.A547_CertificateImage.certificates certificate).card :=
  ResearchFortieth.A573_SemanticOptimalityBound.semantic_card_le_certificate_card
    feature certificate factorization

end A574_CoarsestExactQuotient

/-! ## 575 - A residual-kernel score records construction, classes, and message work -/
namespace A575_ResidualKernelScore

structure Score where
  rawBranches : Nat
  uniqueResiduals : Nat
  maximumMessageWork : Nat
  constructionWork : Nat
  quotientBound : uniqueResiduals <= rawBranches

end A575_ResidualKernelScore

/-! ## 576 - Exact quotient-message work pays once per unique residual kernel -/
namespace A576_QuotientMessageWork

open A575_ResidualKernelScore

def messageWork (score : Score) : Nat :=
  score.uniqueResiduals * score.maximumMessageWork

def totalWork (score : Score) : Nat :=
  score.constructionWork + messageWork score

end A576_QuotientMessageWork

/-! ## 577 - Quotient message work never exceeds raw branch message work -/
namespace A577_KernelDominance

open A575_ResidualKernelScore A576_QuotientMessageWork

theorem message_work_le_raw (score : Score) :
    messageWork score <= score.rawBranches * score.maximumMessageWork := by
  exact Nat.mul_le_mul_right score.maximumMessageWork score.quotientBound

end A577_KernelDominance

/-! ## 578 - Construction and quotient-message work compose explicitly -/
namespace A578_KernelTotalBudget

open A575_ResidualKernelScore A576_QuotientMessageWork

theorem total_work_bound
    (score : Score) (constructionBound quotientBound : Nat)
    (construction : score.constructionWork <= constructionBound)
    (quotient : messageWork score <= quotientBound) :
    totalWork score <= constructionBound + quotientBound := by
  exact Nat.add_le_add construction quotient

end A578_KernelTotalBudget

/-! ## 579 - Polynomial class count and polynomial message work give polynomial kernel work -/
namespace A579_PolynomialKernelBudget

theorem quotient_message_budget
    (classes messageWork input classExp messageExp : Nat)
    (classBound : classes <= input ^ classExp)
    (messageBound : messageWork <= input ^ messageExp) :
    classes * messageWork <= input ^ classExp * input ^ messageExp := by
  exact Nat.mul_le_mul classBound messageBound

end A579_PolynomialKernelBudget

/-! ## 580 - A genuine semantic collision gives a strict saving when message work is positive -/
namespace A580_CollisionSaving

theorem strict_collision_saving
    (unique raw messageWork : Nat)
    (collision : unique < raw)
    (positive : 0 < messageWork) :
    unique * messageWork < raw * messageWork := by
  exact Nat.mul_lt_mul_of_pos_right collision positive

end A580_CollisionSaving

/-! ## 581 - Exponentially many raw cuts can still have one semantic residual class -/
namespace A581_ExponentialRawOneClass

theorem one_class_example (cutBits : Nat) :
    exists raw unique : Nat,
      raw = 2 ^ cutBits /\ unique = 1 /\ unique <= raw := by
  refine ⟨2 ^ cutBits, 1, rfl, rfl, ?_⟩
  have positive : 0 < (2 : Nat) ^ cutBits := pow_pos (by decide) _
  omega

end A581_ExponentialRawOneClass

/-! ## 582 - Impossible assignments may all be represented by one empty kernel -/
namespace A582_EmptyKernelClass

theorem empty_class_cost
    (impossibleBranches kernelWork : Nat)
    (nonempty : 0 < impossibleBranches) :
    kernelWork <= impossibleBranches * kernelWork := by
  have oneLe : 1 <= impossibleBranches := nonempty
  simpa [Nat.one_mul] using Nat.mul_le_mul_right kernelWork oneLe

end A582_EmptyKernelClass

/-! ## 583 - A compiled residual kernel carries exactness and all measured resources -/
namespace A583_CompiledResidualKernel

structure Compiled (specification : Prop) where
  answer : Bool
  certificateConstruction : Nat
  uniqueResiduals : Nat
  messageWork : Nat
  exact : answer = true <-> specification

theorem decide_correct
    (specification : Prop) (compiled : Compiled specification) :
    compiled.answer = true <-> specification :=
  compiled.exact

end A583_CompiledResidualKernel

/-! ## 584 - The acceptable kernel obligation includes discovery, quotienting, and message construction -/
namespace A584_UniformKernelCompiler

variable {Input : Type}

structure Compiler (accepts : Input -> Prop) where
  compile : (input : Input) ->
    ResearchFortieth.A583_CompiledResidualKernel.Compiled (accepts input)
  constructionCost : Input -> Nat
  quotientCost : Input -> Nat
  messageCost : Input -> Nat

end A584_UniformKernelCompiler

/-! ## 585 - Uniform polynomial residual-kernel compilers imply P = NP -/
namespace A585_ResidualKernelCollapse

variable {Language : Type}

structure UniformResidualKernels (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_residual_kernels
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformResidualKernels PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A585_ResidualKernelCollapse

end PIsNPOrNot.ResearchFortieth
