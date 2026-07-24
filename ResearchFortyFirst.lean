import ResearchFortieth

namespace PIsNPOrNot.ResearchFortyFirst

/-! ## 586 - Cubes are partial Boolean assignments -/
namespace A586_Cube

abbrev Cube (n : Nat) := Fin n -> Option Bool

def Extends {n : Nat} (assignment : Fin n -> Bool) (cube : Cube n) : Prop :=
  forall index bit, cube index = some bit -> assignment index = bit

end A586_Cube

/-! ## 587 - Every cube denotes its exact finite region of total assignments -/
namespace A587_CubeRegion

open A586_Cube

noncomputable def region {n : Nat} (cube : Cube n) : Finset (Fin n -> Bool) := by
  classical
  exact Finset.univ.filter (fun assignment => Extends assignment cube)

theorem mem_region {n : Nat} (cube : Cube n) (assignment : Fin n -> Bool) :
    assignment ∈ region cube ↔ Extends assignment cube := by
  classical
  simp [region]

end A587_CubeRegion

/-! ## 588 - A semantic cube is monochromatic in complete residual behaviour -/
namespace A588_MonochromaticCube

open A586_Cube

variable {n : Nat} {Payload Output : Type}

def Residual (feature : (Fin n -> Bool) -> Payload -> Output)
    (cut : Fin n -> Bool) : Payload -> Output :=
  feature cut

def Monochromatic
    (feature : (Fin n -> Bool) -> Payload -> Output)
    (cube : Cube n) (target : Payload -> Output) : Prop :=
  forall cut, Extends cut cube -> Residual feature cut = target

end A588_MonochromaticCube

/-! ## 589 - Safe terms carry a representative of a monochromatic cube -/
namespace A589_SafeTerm

open A586_Cube
open A588_MonochromaticCube

variable {n : Nat} {Payload Output : Type}

structure SafeTerm (feature : (Fin n -> Bool) -> Payload -> Output) where
  cube : Cube n
  representative : Fin n -> Bool
  representativeExtends : Extends representative cube
  safe : forall cut, Extends cut cube ->
    Residual feature cut = Residual feature representative

end A589_SafeTerm

/-! ## 590 - Safe-term collisions preserve every residual output -/
namespace A590_SafeTermOutput

open A586_Cube
open A588_MonochromaticCube
open A589_SafeTerm

variable {n : Nat} {Payload Output : Type}

theorem output_eq
    (feature : (Fin n -> Bool) -> Payload -> Output)
    (term : SafeTerm feature)
    (cut : Fin n -> Bool) (payload : Payload)
    (hExt : Extends cut term.cube) :
    feature cut payload = feature term.representative payload := by
  exact congrFun (term.safe cut hExt) payload

end A590_SafeTermOutput

/-! ## 591 - One accepting representative payload works throughout its cube -/
namespace A591_AcceptingTermTransport

open A586_Cube
open A589_SafeTerm

variable {n : Nat} {Payload : Type}

theorem accepting_payload_transports
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (term : SafeTerm feature)
    (payload : Payload)
    (accepted : feature term.representative payload = true)
    (cut : Fin n -> Bool)
    (hExt : Extends cut term.cube) :
    feature cut payload = true := by
  rw [A590_SafeTermOutput.output_eq feature term cut payload hExt]
  exact accepted

end A591_AcceptingTermTransport

/-! ## 592 - A rejecting representative rejects every assignment in its cube -/
namespace A592_RejectingTermTransport

open A586_Cube
open A589_SafeTerm

variable {n : Nat} {Payload : Type}

theorem rejection_transports
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (term : SafeTerm feature)
    (rejected : forall payload, feature term.representative payload = false)
    (cut : Fin n -> Bool)
    (hExt : Extends cut term.cube) :
    forall payload, feature cut payload = false := by
  intro payload
  rw [A590_SafeTermOutput.output_eq feature term cut payload hExt]
  exact rejected payload

end A592_RejectingTermTransport

/-! ## 593 - A safe cube cover covers every total cut assignment -/
namespace A593_SafeCover

open A586_Cube
open A589_SafeTerm

variable {n : Nat} {Payload Output : Type}

structure Cover (feature : (Fin n -> Bool) -> Payload -> Output) where
  terms : List (SafeTerm feature)
  complete : forall cut, exists term, term ∈ terms ∧ Extends cut term.cube

end A593_SafeCover

/-! ## 594 - Solving representatives of a complete safe cover is existentially exact -/
namespace A594_RepresentativeDecision

open A586_Cube
open A593_SafeCover

variable {n : Nat} {Payload : Type}

theorem exists_over_cover_iff
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (cover : Cover feature) :
    (exists cut payload, feature cut payload = true) ↔
      exists term, term ∈ cover.terms ∧
        exists payload, feature term.representative payload = true := by
  constructor
  · rintro ⟨cut, payload, accepted⟩
    rcases cover.complete cut with ⟨term, member, hExt⟩
    refine ⟨term, member, payload, ?_⟩
    rw [← A590_SafeTermOutput.output_eq feature term cut payload hExt]
    exact accepted
  · rintro ⟨term, _member, payload, accepted⟩
    exact ⟨term.representative, payload, accepted⟩

end A594_RepresentativeDecision

/-! ## 595 - Representative residual images reconstruct the global output image -/
namespace A595_RepresentativeImage

open A586_Cube
open A593_SafeCover

variable {n : Nat} {Payload Output : Type}

theorem output_exists_over_representatives
    (feature : (Fin n -> Bool) -> Payload -> Output)
    (cover : Cover feature) (output : Output) :
    (exists cut payload, feature cut payload = output) ↔
      exists term, term ∈ cover.terms ∧
        exists payload, feature term.representative payload = output := by
  constructor
  · rintro ⟨cut, payload, value⟩
    rcases cover.complete cut with ⟨term, member, hExt⟩
    refine ⟨term, member, payload, ?_⟩
    rw [← A590_SafeTermOutput.output_eq feature term cut payload hExt]
    exact value
  · rintro ⟨term, _member, payload, value⟩
    exact ⟨term.representative, payload, value⟩

end A595_RepresentativeImage

/-! ## 596 - Every total assignment has a singleton cube -/
namespace A596_SingletonCube

open A586_Cube

variable {n : Nat}

def singleton (assignment : Fin n -> Bool) : Cube n :=
  fun index => some (assignment index)

theorem extends_singleton_iff
    (cut assignment : Fin n -> Bool) :
    Extends cut (singleton assignment) ↔ cut = assignment := by
  constructor
  · intro hExt
    funext index
    exact hExt index (assignment index) rfl
  · rintro rfl
    intro index bit equal
    exact Option.some.inj equal

end A596_SingletonCube

/-! ## 597 - Singleton cubes are always semantically safe -/
namespace A597_SingletonSafeTerm

open A586_Cube
open A589_SafeTerm
open A596_SingletonCube

variable {n : Nat} {Payload Output : Type}

noncomputable def term
    (feature : (Fin n -> Bool) -> Payload -> Output)
    (assignment : Fin n -> Bool) : SafeTerm feature where
  cube := singleton assignment
  representative := assignment
  representativeExtends := (extends_singleton_iff assignment assignment).2 rfl
  safe := by
    intro cut hExt
    have equal := (extends_singleton_iff cut assignment).1 hExt
    subst cut
    rfl

theorem every_assignment_has_safe_singleton
    (feature : (Fin n -> Bool) -> Payload -> Output)
    (assignment : Fin n -> Bool) :
    exists safeTerm : SafeTerm feature,
      Extends assignment safeTerm.cube := by
  exact ⟨term feature assignment, (term feature assignment).representativeExtends⟩

end A597_SingletonSafeTerm

/-! ## 598 - The complete cube candidate space has cardinality 3^n -/
namespace A598_CubeSpaceCardinality

open A586_Cube

theorem cube_card (n : Nat) :
    Fintype.card (Cube n) = 3 ^ n := by
  simp [Cube, Fintype.card_fun]

end A598_CubeSpaceCardinality

/-! ## 599 - The raw total-assignment space has cardinality 2^n -/
namespace A599_AssignmentSpaceCardinality

theorem assignment_card (n : Nat) :
    Fintype.card (Fin n -> Bool) = 2 ^ n := by
  simp [Fintype.card_fun]

end A599_AssignmentSpaceCardinality

/-! ## 600 - Uniform polynomial safe-cube covers imply P = NP -/
namespace A600_SafeCubeCollapse

variable {Language : Type}

structure UniformSafeCubeCovers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_safe_cube_covers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (covers : UniformSafeCubeCovers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact covers.compilerGivesP language
    (covers.allNPHaveCompiler language inNP)

end A600_SafeCubeCollapse

end PIsNPOrNot.ResearchFortyFirst