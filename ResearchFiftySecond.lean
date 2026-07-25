import ResearchFiftyFirst

namespace PIsNPOrNot.ResearchFiftySecond

/-! ## 751 - Edge-labelled references separate physical bases from semantic labels -/
namespace A751_EdgeReference

abbrev Reference (Base Label : Type) := Base × Label

end A751_EdgeReference

/-! ## 752 - An exact action-labelled encoding decodes every semantic state -/
namespace A752_ActionEncoding

structure Encoding (State Base Label Residual : Type)
    [Fintype State] [Fintype Base] [Fintype Label] where
  meaning : State -> Residual
  baseMeaning : Base -> Residual
  action : Label -> Residual -> Residual
  encode : State -> Base × Label
  exact : forall state,
    action (encode state).2 (baseMeaning (encode state).1) = meaning state

def decode {State Base Label Residual : Type}
    [Fintype State] [Fintype Base] [Fintype Label]
    (encoding : Encoding State Base Label Residual)
    (reference : Base × Label) : Residual :=
  encoding.action reference.2 (encoding.baseMeaning reference.1)

end A752_ActionEncoding

/-! ## 753 - Equal references transport equal semantic meanings -/
namespace A753_ReferenceTransport

open A752_ActionEncoding

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem equal_reference_equal_meaning
    (encoding : Encoding State Base Label Residual)
    {left right : State} (equal : encoding.encode left = encoding.encode right) :
    encoding.meaning left = encoding.meaning right := by
  rw [← encoding.exact left, ← encoding.exact right, equal]

end A753_ReferenceTransport

/-! ## 754 - Distinguishable meanings force injective edge references -/
namespace A754_ReferenceInjective

open A752_ActionEncoding

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem encode_injective
    (encoding : Encoding State Base Label Residual)
    (meaningInjective : Function.Injective encoding.meaning) :
    Function.Injective encoding.encode := by
  intro left right equal
  apply meaningInjective
  exact A753_ReferenceTransport.equal_reference_equal_meaning encoding equal

end A754_ReferenceInjective

/-! ## 755 - Semantic state count is bounded by physical bases times labels -/
namespace A755_ActionCardinalityBound

open A752_ActionEncoding

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem state_card_le_base_mul_label
    (encoding : Encoding State Base Label Residual)
    (meaningInjective : Function.Injective encoding.meaning) :
    Fintype.card State <= Fintype.card Base * Fintype.card Label := by
  calc
    Fintype.card State <= Fintype.card (Base × Label) :=
      Fintype.card_le_of_injective encoding.encode
        (A754_ReferenceInjective.encode_injective encoding meaningInjective)
    _ = Fintype.card Base * Fintype.card Label := Fintype.card_prod _ _

end A755_ActionCardinalityBound

/-! ## 756 - Every represented meaning lies in a labelled orbit of a physical base -/
namespace A756_ActionClosure

open A752_ActionEncoding

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem meaning_is_action_of_base
    (encoding : Encoding State Base Label Residual) (state : State) :
    exists base label,
      encoding.meaning state = encoding.action label (encoding.baseMeaning base) := by
  rcases referenceEq : encoding.encode state with ⟨base, label⟩
  exact ⟨base, label, by
    have represented := (encoding.exact state).symm
    simpa [referenceEq] using represented⟩

end A756_ActionClosure

/-! ## 757 - One physical base can represent at most one full label orbit -/
namespace A757_OneBaseBound

open A752_ActionEncoding

variable {State Label Residual : Type}
variable [Fintype State] [Fintype Label]

theorem state_card_le_label_card
    (encoding : Encoding State Unit Label Residual)
    (meaningInjective : Function.Injective encoding.meaning) :
    Fintype.card State <= Fintype.card Label := by
  simpa using
    (A755_ActionCardinalityBound.state_card_le_base_mul_label encoding meaningInjective)

end A757_OneBaseBound

/-! ## 758 - Lawful labelled actions expose identity and composition rules -/
namespace A758_LawfulAction

structure Laws (Label Residual : Type) [Monoid Label] where
  action : Label -> Residual -> Residual
  identity : forall value, action 1 value = value
  compose : forall left right value,
    action (left * right) value = action left (action right value)

end A758_LawfulAction

/-! ## 759 - Nested edge labels normalize to one composed label -/
namespace A759_LabelNormalization

open A758_LawfulAction

variable {Label Residual : Type} [Monoid Label]

theorem normalize (laws : Laws Label Residual)
    (left right : Label) (value : Residual) :
    laws.action left (laws.action right value) =
      laws.action (left * right) value := by
  symm
  exact laws.compose left right value

end A759_LabelNormalization

/-! ## 760 - The identity label preserves every physical base meaning -/
namespace A760_IdentityReference

open A758_LawfulAction

variable {Label Residual : Type} [Monoid Label]

theorem identity_reference (laws : Laws Label Residual) (value : Residual) :
    laws.action 1 value = value := laws.identity value

end A760_IdentityReference

/-! ## 761 - A finite orbit model is an explicit one-base semantic family -/
namespace A761_OrbitModel

structure OrbitModel (Label Residual : Type) [Fintype Label] where
  base : Residual
  action : Label -> Residual -> Residual

def orbitMeaning {Label Residual : Type} [Fintype Label]
    (model : OrbitModel Label Residual) (label : Label) : Residual :=
  model.action label model.base

end A761_OrbitModel

/-! ## 762 - Every finite orbit has an exact one-base labelled encoding -/
namespace A762_OrbitEncoding

open A752_ActionEncoding
open A761_OrbitModel

variable {Label Residual : Type} [Fintype Label]

def encoding (model : OrbitModel Label Residual) :
    Encoding Label Unit Label Residual where
  meaning := orbitMeaning model
  baseMeaning := fun _ => model.base
  action := model.action
  encode := fun label => ((), label)
  exact := by
    intro label
    rfl

end A762_OrbitEncoding

/-! ## 763 - An injective orbit uses exactly one semantic slot per label -/
namespace A763_OrbitCapacity

open A761_OrbitModel

variable {Label Residual : Type} [Fintype Label] [DecidableEq Residual]

theorem orbit_card_le_label_card (model : OrbitModel Label Residual) :
    ((Finset.univ : Finset Label).image (orbitMeaning model)).card <=
      Fintype.card Label := by
  exact Finset.card_image_le

end A763_OrbitCapacity

/-! ## 764 - A meaning outside every labelled base orbit obstructs exact encoding -/
namespace A764_UnpairedActionObstruction

open A752_ActionEncoding

variable {State Base Label Residual : Type}
variable [Fintype State] [Fintype Base] [Fintype Label]

theorem no_encoding_of_outside_orbits
    (meaning : State -> Residual)
    (baseMeaning : Base -> Residual)
    (action : Label -> Residual -> Residual)
    (outside : exists state, forall base label,
      Not (meaning state = action label (baseMeaning base))) :
    Not (exists encoding : Encoding State Base Label Residual,
      encoding.meaning = meaning ∧
      encoding.baseMeaning = baseMeaning ∧
      encoding.action = action) := by
  rintro ⟨encoding, meaningEq, baseEq, actionEq⟩
  rcases outside with ⟨state, stateOutside⟩
  rcases A756_ActionClosure.meaning_is_action_of_base encoding state with
    ⟨base, label, represented⟩
  exact stateOutside base label (by
    simpa [meaningEq, baseEq, actionEq] using represented)

end A764_UnpairedActionObstruction

/-! ## 765 - Uniform polynomial action-labelled compilers would imply P = NP -/
namespace A765_ActionLabelledCollapse

variable {Language : Type}

structure UniformActionCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_action_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformActionCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A765_ActionLabelledCollapse

end PIsNPOrNot.ResearchFiftySecond
