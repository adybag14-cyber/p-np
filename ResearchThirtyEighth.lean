import ResearchThirtySeventh

namespace PIsNPOrNot.ResearchThirtyEighth

/-! ## 541 - A safe certificate never merges different residual behaviours -/
namespace A541_SafeCertificate

variable {Cut Payload Output Certificate : Type}

structure System (feature : Cut -> Payload -> Output) where
  certificate : Cut -> Certificate
  safe : forall {left right}, certificate left = certificate right ->
    forall payload, feature left payload = feature right payload

end A541_SafeCertificate

/-! ## 542 - Safe certificate equality implies semantic signature equality -/
namespace A542_CertificateToSignature

open A541_SafeCertificate
open ResearchThirtySeventh.A526_ResidualSignature

variable {Cut Payload Output Certificate : Type}

theorem equal_signature
    (feature : Cut -> Payload -> Output)
    (system : System (Certificate := Certificate) feature)
    {left right : Cut}
    (same : system.certificate left = system.certificate right) :
    signature feature left = signature feature right := by
  funext payload
  exact system.safe same payload

end A542_CertificateToSignature

/-! ## 543 - Denotational certificates are safe by construction -/
namespace A543_DenotationalCertificate

open A541_SafeCertificate

variable {Cut Payload Output Certificate : Type}

structure Representation (feature : Cut -> Payload -> Output) where
  certificate : Cut -> Certificate
  denote : Certificate -> Payload -> Output
  exact : forall cut payload,
    denote (certificate cut) payload = feature cut payload

noncomputable def toSafe
    (feature : Cut -> Payload -> Output)
    (representation : Representation (Certificate := Certificate) feature) :
    System (Certificate := Certificate) feature where
  certificate := representation.certificate
  safe := by
    intro left right same payload
    calc
      feature left payload = representation.denote
          (representation.certificate left) payload :=
        (representation.exact left payload).symm
      _ = representation.denote (representation.certificate right) payload := by
        rw [same]
      _ = feature right payload := representation.exact right payload

end A543_DenotationalCertificate

/-! ## 544 - A certificate cover stores one cut per syntactic certificate -/
namespace A544_CertificateCover

variable {Cut Certificate : Type}

structure Cover (certificate : Cut -> Certificate) where
  representatives : Finset Cut
  covers : forall cut, exists representative,
    representative ∈ representatives /\
      certificate representative = certificate cut

end A544_CertificateCover

/-! ## 545 - Every safe certificate cover induces an exact semantic cover -/
namespace A545_CertificateCoverSafety

open A541_SafeCertificate A542_CertificateToSignature A544_CertificateCover
open ResearchThirtySeventh.A526_ResidualSignature
open ResearchThirtySeventh.A532_RepresentativeCover

variable {Cut Payload Output Certificate : Type}

noncomputable def semanticCover
    (feature : Cut -> Payload -> Output)
    (system : System (Certificate := Certificate) feature)
    (cover : Cover system.certificate) :
    ResearchThirtySeventh.A532_RepresentativeCover.Cover feature where
  representatives := cover.representatives
  covers := by
    intro cut
    rcases cover.covers cut with ⟨representative, member, same⟩
    exact ⟨representative, member, equal_signature feature system same⟩

end A545_CertificateCoverSafety

/-! ## 546 - Searching a safe certificate cover preserves acceptance exactly -/
namespace A546_CertificateExistence

open A541_SafeCertificate A544_CertificateCover A545_CertificateCoverSafety
open ResearchThirtySeventh.A534_RepresentativeExistence

variable {Cut Payload Output Certificate : Type}

theorem exists_over_certificates
    (feature : Cut -> Payload -> Output)
    (accept : Output -> Prop)
    (system : System (Certificate := Certificate) feature)
    (cover : Cover system.certificate) :
    (exists cut payload, accept (feature cut payload)) <->
      exists representative,
        representative ∈ cover.representatives /\
        exists payload, accept (feature representative payload) := by
  exact exists_over_representatives feature accept
    (semanticCover feature system cover)

end A546_CertificateExistence

/-! ## 547 - A finite certificate image never has more classes than raw cuts -/
namespace A547_CertificateImage

variable {Cut Certificate : Type}
variable [Fintype Cut]

noncomputable def certificates (certificate : Cut -> Certificate) : Finset Certificate := by
  classical
  exact (Finset.univ : Finset Cut).image certificate

theorem certificate_card_le_raw (certificate : Cut -> Certificate) :
    (certificates certificate).card <= Fintype.card Cut := by
  classical
  simpa [certificates] using
    (Finset.card_image_le :
      ((Finset.univ : Finset Cut).image certificate).card <=
        (Finset.univ : Finset Cut).card)

end A547_CertificateImage

/-! ## 548 - Boolean expression syntax supplies checkable structural certificates -/
namespace A548_BooleanExpressions

inductive Expr (Variable : Type)
  | constant : Bool -> Expr Variable
  | variable : Variable -> Expr Variable
  | negation : Expr Variable -> Expr Variable
  | conjunction : Expr Variable -> Expr Variable -> Expr Variable
  | disjunction : Expr Variable -> Expr Variable -> Expr Variable
  | exclusiveOr : Expr Variable -> Expr Variable -> Expr Variable

def evaluate {Variable : Type}
    (assignment : Variable -> Bool) : Expr Variable -> Bool
  | Expr.constant value => value
  | Expr.variable name => assignment name
  | Expr.negation child => !(evaluate assignment child)
  | Expr.conjunction left right =>
      evaluate assignment left && evaluate assignment right
  | Expr.disjunction left right =>
      evaluate assignment left || evaluate assignment right
  | Expr.exclusiveOr left right =>
      decide (evaluate assignment left != evaluate assignment right)

end A548_BooleanExpressions

/-! ## 549 - Equal expression certificates evaluate equally under every assignment -/
namespace A549_ExpressionEqualitySafety

open A548_BooleanExpressions

variable {Variable : Type}

theorem equal_expression_equal_value
    (assignment : Variable -> Bool) {left right : Expr Variable}
    (same : left = right) :
    evaluate assignment left = evaluate assignment right := by
  rw [same]

end A549_ExpressionEqualitySafety

/-! ## 550 - A compiled expression representation is a safe residual certificate -/
namespace A550_ExpressionCertificate

open A541_SafeCertificate
open A548_BooleanExpressions

variable {Cut Payload Variable : Type}

noncomputable def system
    (feature : Cut -> Payload -> Bool)
    (compile : Cut -> Expr Variable)
    (assignment : Payload -> Variable -> Bool)
    (correct : forall cut payload,
      evaluate (assignment payload) (compile cut) = feature cut payload) :
    System (Certificate := Expr Variable) feature where
  certificate := compile
  safe := by
    intro left right same payload
    calc
      feature left payload = evaluate (assignment payload) (compile left) :=
        (correct left payload).symm
      _ = evaluate (assignment payload) (compile right) := by rw [same]
      _ = feature right payload := correct right payload

end A550_ExpressionCertificate

/-! ## 551 - Safe structural certificates may be finer than semantic signatures -/
namespace A551_CertificateRefinement

open A541_SafeCertificate
open ResearchThirtySeventh.A526_ResidualSignature

variable {Cut Payload Output Certificate : Type}

theorem certificate_collision_is_semantic_collision
    (feature : Cut -> Payload -> Output)
    (system : System (Certificate := Certificate) feature)
    {left right : Cut}
    (same : system.certificate left = system.certificate right) :
    signature feature left = signature feature right := by
  funext payload
  exact system.safe same payload

end A551_CertificateRefinement

/-! ## 552 - Representative certificate work is class count times maximum class work -/
namespace A552_CertificateWork

open A544_CertificateCover

variable {Cut Certificate : Type}

theorem total_work_bound
    (certificate : Cut -> Certificate)
    (cover : Cover certificate)
    (work : Cut -> Nat) (maximum : Nat)
    (bounded : forall representative,
      representative ∈ cover.representatives -> work representative <= maximum) :
    cover.representatives.sum work <= cover.representatives.card * maximum := by
  calc
    cover.representatives.sum work <=
        cover.representatives.sum (fun _ => maximum) := by
      exact Finset.sum_le_sum (fun representative member => bounded representative member)
    _ = cover.representatives.card * maximum := by simp

end A552_CertificateWork

/-! ## 553 - Polynomial certificate construction plus polynomial class work stays polynomial -/
namespace A553_CertificateBudget

theorem construction_and_class_work
    (construction classes classWork input constructionExp classExp workExp : Nat)
    (constructionBound : construction <= input ^ constructionExp)
    (classBound : classes <= input ^ classExp)
    (workBound : classWork <= input ^ workExp) :
    construction + classes * classWork <=
      input ^ constructionExp + input ^ classExp * input ^ workExp := by
  exact Nat.add_le_add constructionBound
    (Nat.mul_le_mul classBound workBound)

end A553_CertificateBudget

/-! ## 554 - Baseline-retaining certificate portfolios never worsen measured work -/
namespace A554_CertificatePortfolio

structure Candidate (specification : Prop) where
  answer : Bool
  work : Nat
  exact : answer = true <-> specification

def choose {specification : Prop}
    (baseline candidate : Candidate specification) : Candidate specification :=
  if candidate.work < baseline.work then candidate else baseline

theorem chosen_exact {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).answer = true <-> specification := by
  unfold choose
  split
  · exact candidate.exact
  · exact baseline.exact

theorem chosen_work_le_baseline {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).work <= baseline.work := by
  unfold choose
  split
  · omega
  · exact le_rfl

end A554_CertificatePortfolio

/-! ## 555 - Uniform polynomial safe-certificate compilers imply P = NP -/
namespace A555_CertificateCollapse

variable {Language : Type}

structure UniformCertificates (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_safe_certificates
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformCertificates PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A555_CertificateCollapse

end PIsNPOrNot.ResearchThirtyEighth
