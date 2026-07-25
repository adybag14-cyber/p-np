import ResearchFiftySixth

namespace PIsNPOrNot.ResearchFiftySeventh

/-! ## 826 - An action invariant is unchanged by every edge label -/
namespace A826_ActionInvariant

structure Invariant (Label Residual Class : Type)
    (action : Label -> Residual -> Residual) where
  classify : Residual -> Class
  preserved : forall label value,
    classify (action label value) = classify value

end A826_ActionInvariant

/-! ## 827 - Exact action encodings transport invariant classes to physical bases -/
namespace A827_InvariantTransport

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant

variable {State Base Label Residual Class : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem class_eq_base_class
    (encoding : Encoding State Base Label Residual)
    (invariant : Invariant Label Residual Class encoding.action)
    (state : State) :
    invariant.classify (encoding.meaning state) =
      invariant.classify
        (encoding.baseMeaning (encoding.encode state).1) := by
  rw [← encoding.exact state]
  exact invariant.preserved (encoding.encode state).2
    (encoding.baseMeaning (encoding.encode state).1)

end A827_InvariantTransport

/-! ## 828 - Semantic and physical invariant-class images are finite -/
namespace A828_InvariantImages

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant

variable {State Base Label Residual Class : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]
variable [DecidableEq Class]

noncomputable def semanticClasses
    (encoding : Encoding State Base Label Residual)
    (invariant : Invariant Label Residual Class encoding.action) :
    Finset Class := by
  classical
  exact (Finset.univ : Finset State).image
    (fun state => invariant.classify (encoding.meaning state))

noncomputable def baseClasses
    (encoding : Encoding State Base Label Residual)
    (invariant : Invariant Label Residual Class encoding.action) :
    Finset Class := by
  classical
  exact (Finset.univ : Finset Base).image
    (fun base => invariant.classify (encoding.baseMeaning base))

end A828_InvariantImages

/-! ## 829 - Every semantic invariant class appears among physical base classes -/
namespace A829_SemanticClassCoverage

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant
open A828_InvariantImages

variable {State Base Label Residual Class : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]
variable [DecidableEq Class]

theorem semantic_subset_base
    (encoding : Encoding State Base Label Residual)
    (invariant : Invariant Label Residual Class encoding.action) :
    semanticClasses encoding invariant ⊆ baseClasses encoding invariant := by
  classical
  intro classValue member
  rcases Finset.mem_image.1 member with ⟨state, _inUniverse, classEq⟩
  apply Finset.mem_image.2
  refine ⟨(encoding.encode state).1, Finset.mem_univ _, ?_⟩
  rw [← A827_InvariantTransport.class_eq_base_class encoding invariant state]
  exact classEq

end A829_SemanticClassCoverage

/-! ## 830 - Distinct invariant classes lower-bound physical base count -/
namespace A830_OrbitClassBaseLowerBound

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant
open A828_InvariantImages

variable {State Base Label Residual Class : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]
variable [DecidableEq Class]

theorem semantic_class_card_le_base_card
    (encoding : Encoding State Base Label Residual)
    (invariant : Invariant Label Residual Class encoding.action) :
    (semanticClasses encoding invariant).card <= Fintype.card Base := by
  classical
  calc
    (semanticClasses encoding invariant).card <=
        (baseClasses encoding invariant).card :=
      Finset.card_le_card
        (A829_SemanticClassCoverage.semantic_subset_base encoding invariant)
    _ <= (Finset.univ : Finset Base).card := Finset.card_image_le
    _ = Fintype.card Base := Finset.card_univ

end A830_OrbitClassBaseLowerBound

/-! ## 831 - One physical base can cover at most one invariant class -/
namespace A831_OneBaseInvariantBound

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant
open A828_InvariantImages

variable {State Label Residual Class : Type}
variable [Fintype State] [Fintype Label] [DecidableEq Class]

theorem semantic_class_card_le_one
    (encoding : Encoding State Unit Label Residual)
    (invariant : Invariant Label Residual Class encoding.action) :
    (semanticClasses encoding invariant).card <= 1 := by
  simpa using
    (A830_OrbitClassBaseLowerBound.semantic_class_card_le_base_card
      encoding invariant)

end A831_OneBaseInvariantBound

/-! ## 832 - Two invariant-separated meanings obstruct every one-base encoding -/
namespace A832_TwoClassObstruction

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant

variable {State Label Residual Class : Type}
variable [Fintype State] [Fintype Label]

theorem no_one_base_when_classes_differ
    (encoding : Encoding State Unit Label Residual)
    (invariant : Invariant Label Residual Class encoding.action)
    {left right : State}
    (different :
      invariant.classify (encoding.meaning left) ≠
        invariant.classify (encoding.meaning right)) : False := by
  apply different
  calc
    invariant.classify (encoding.meaning left) =
        invariant.classify (encoding.baseMeaning ()) :=
      A827_InvariantTransport.class_eq_base_class encoding invariant left
    _ = invariant.classify (encoding.meaning right) :=
      (A827_InvariantTransport.class_eq_base_class
        encoding invariant right).symm

end A832_TwoClassObstruction

/-! ## 833 - Product invariants classify independent residual products -/
namespace A833_ProductInvariant

open A826_ActionInvariant

variable {LeftLabel RightLabel LeftResidual RightResidual LeftClass RightClass : Type}

def product
    (leftAction : LeftLabel -> LeftResidual -> LeftResidual)
    (rightAction : RightLabel -> RightResidual -> RightResidual)
    (leftInvariant : Invariant LeftLabel LeftResidual LeftClass leftAction)
    (rightInvariant : Invariant RightLabel RightResidual RightClass rightAction) :
    Invariant (LeftLabel × RightLabel)
      (LeftResidual × RightResidual) (LeftClass × RightClass)
      (fun label value =>
        (leftAction label.1 value.1, rightAction label.2 value.2)) where
  classify := fun value =>
    (leftInvariant.classify value.1, rightInvariant.classify value.2)
  preserved := by
    intro label value
    apply Prod.ext
    · exact leftInvariant.preserved label.1 value.1
    · exact rightInvariant.preserved label.2 value.2

end A833_ProductInvariant

/-! ## 834 - Product invariant-class universes multiply -/
namespace A834_ProductInvariantCapacity

variable {LeftClass RightClass : Type}
variable [Fintype LeftClass] [Fintype RightClass]

theorem class_universe_card :
    Fintype.card (LeftClass × RightClass) =
      Fintype.card LeftClass * Fintype.card RightClass :=
  Fintype.card_prod _ _

end A834_ProductInvariantCapacity

/-! ## 835 - An orbit lower-bound certificate packages a checkable invariant -/
namespace A835_OrbitLowerBoundCertificate

open ResearchFiftySecond.A752_ActionEncoding
open A826_ActionInvariant
open A828_InvariantImages

structure Certificate
    (State Base Label Residual Class : Type)
    [Fintype State] [Fintype Base] [Fintype Label]
    [DecidableEq Class]
    (encoding : Encoding State Base Label Residual) where
  invariant : Invariant Label Residual Class encoding.action
  claimedClasses : Nat
  classEquation :
    claimedClasses = (semanticClasses encoding invariant).card

end A835_OrbitLowerBoundCertificate

/-! ## 836 - Every orbit lower-bound certificate is sound for base count -/
namespace A836_OrbitCertificateSoundness

open ResearchFiftySecond.A752_ActionEncoding
open A835_OrbitLowerBoundCertificate

variable {State Base Label Residual Class : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]
variable [DecidableEq Class]

theorem claimed_classes_le_bases
    (encoding : Encoding State Base Label Residual)
    (certificate : Certificate State Base Label Residual Class encoding) :
    certificate.claimedClasses <= Fintype.card Base := by
  rw [certificate.classEquation]
  exact A830_OrbitClassBaseLowerBound.semantic_class_card_le_base_card
    encoding certificate.invariant

end A836_OrbitCertificateSoundness

/-! ## 837 - A normalizer preserves decoded meaning and is idempotent -/
namespace A837_ReferenceNormalizer

structure Normalizer (Reference Residual : Type) where
  decode : Reference -> Residual
  normalize : Reference -> Reference
  preserves : forall reference,
    decode (normalize reference) = decode reference
  idempotent : forall reference,
    normalize (normalize reference) = normalize reference

end A837_ReferenceNormalizer

/-! ## 838 - Equal normalized references have equal decoded semantics -/
namespace A838_NormalizedReferenceSafety

open A837_ReferenceNormalizer

variable {Reference Residual : Type}

theorem equal_normal_forms_equal_meaning
    (normalizer : Normalizer Reference Residual)
    {left right : Reference}
    (equal : normalizer.normalize left = normalizer.normalize right) :
    normalizer.decode left = normalizer.decode right := by
  rw [← normalizer.preserves left, ← normalizer.preserves right, equal]

end A838_NormalizedReferenceSafety

/-! ## 839 - Normalized-image size never exceeds raw reference count -/
namespace A839_NormalizedImageBound

open A837_ReferenceNormalizer

variable {Reference Residual : Type}
variable [Fintype Reference] [DecidableEq Reference]

theorem normalized_card_le
    (normalizer : Normalizer Reference Residual) :
    ((Finset.univ : Finset Reference).image normalizer.normalize).card <=
      Fintype.card Reference := by
  calc
    ((Finset.univ : Finset Reference).image normalizer.normalize).card <=
        (Finset.univ : Finset Reference).card := Finset.card_image_le
    _ = Fintype.card Reference := Finset.card_univ

end A839_NormalizedImageBound

/-! ## 840 - Uniform polynomial normalized-action compilers would imply P = NP -/
namespace A840_NormalizedActionCollapse

variable {Language : Type}

structure UniformNormalizedActionCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_normalized_action_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformNormalizedActionCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A840_NormalizedActionCollapse

end PIsNPOrNot.ResearchFiftySeventh
