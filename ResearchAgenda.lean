import ResearchFourth

/-!
# Approaches 56-58: exact set-level frontier

This file states the strongest current formulation as a conditional equality of
complexity classes and proves the corresponding equivalence under explicit
bridges between class membership and polynomial deciders.
-/

namespace PIsNPOrNot
namespace ResearchAgenda

open ResearchFourth.A55_CertifiedCoverCriterion

abbrev Lang (Instance : Type) := Language (Instance := Instance)

def ClassSet {Instance : Type} (C : Lang Instance -> Prop) : Set (Lang Instance) :=
  {L | C L}

/-! ## 56 - A uniform certified cover plus P subset NP yields class equality -/
namespace A56_SetLevelCollapse

variable {Instance : Type}

theorem p_eq_np_of_uniform_certified_cover
    (InP InNP : Lang Instance -> Prop)
    (pSubsetNP : forall L, InP L -> InNP L)
    (cover : UniformCertifiedCover (Instance := Instance) InNP)
    (polyDeciderInP : forall L,
      Nonempty (PolyDecider (Instance := Instance) L) -> InP L) :
    ClassSet InP = ClassSet InNP := by
  apply Set.ext
  intro L
  constructor
  · intro hP
    exact pSubsetNP L hP
  · intro hNP
    exact polyDeciderInP L ⟨cover.compile L hNP⟩

end A56_SetLevelCollapse

/-! ## 57 - Equality is equivalent to uniform polynomial deciders -/
namespace A57_ExactCriterion

variable {Instance : Type}

theorem p_eq_np_iff_uniform_poly_deciders
    (InP InNP : Lang Instance -> Prop)
    (pSubsetNP : forall L, InP L -> InNP L)
    (pHasDecider : forall L, InP L ->
      Nonempty (PolyDecider (Instance := Instance) L))
    (polyDeciderInP : forall L,
      Nonempty (PolyDecider (Instance := Instance) L) -> InP L) :
    ClassSet InP = ClassSet InNP <->
      forall L, InNP L ->
        Nonempty (PolyDecider (Instance := Instance) L) := by
  constructor
  · intro hclasses L hNP
    have hP : InP L := by
      have hmemNP : L ∈ ClassSet InNP := hNP
      rw [← hclasses] at hmemNP
      exact hmemNP
    exact pHasDecider L hP
  · intro hall
    apply Set.ext
    intro L
    constructor
    · intro hP
      exact pSubsetNP L hP
    · intro hNP
      exact polyDeciderInP L (hall L hNP)

end A57_ExactCriterion

/-! ## 58 - If the classes differ, some NP language escapes every certified decider -/
namespace A58_ObstructionLocalization

variable {Instance : Type}

theorem exists_np_without_poly_decider_of_ne
    (InP InNP : Lang Instance -> Prop)
    (pSubsetNP : forall L, InP L -> InNP L)
    (polyDeciderInP : forall L,
      Nonempty (PolyDecider (Instance := Instance) L) -> InP L)
    (hne : ClassSet InP ≠ ClassSet InNP) :
    exists L, InNP L /\
      Not (Nonempty (PolyDecider (Instance := Instance) L)) := by
  by_contra hnone
  push Not at hnone
  apply hne
  apply Set.ext
  intro L
  constructor
  · intro hP
    exact pSubsetNP L hP
  · intro hNP
    exact polyDeciderInP L (hnone L hNP)

end A58_ObstructionLocalization

end ResearchAgenda
end PIsNPOrNot
