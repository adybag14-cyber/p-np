import ResearchFortyThird

namespace PIsNPOrNot.ResearchFortyFourth

namespace A631_LabelledCover

structure LabelledCover
    (Assignment Class Term : Type)
    [Fintype Assignment] [DecidableEq Assignment]
    [DecidableEq Class] [DecidableEq Term]
    (residualClass : Assignment -> Class) where
  terms : Finset Term
  label : Term -> Class
  covers : Term -> Assignment -> Prop
  complete : forall assignment, exists term, term ∈ terms ∧ covers term assignment
  safe : forall term assignment, covers term assignment ->
    residualClass assignment = label term

noncomputable def semanticClasses
    (Assignment Class : Type)
    [Fintype Assignment] [DecidableEq Assignment] [DecidableEq Class]
    (residualClass : Assignment -> Class) : Finset Class := by
  classical
  exact Finset.univ.image residualClass

noncomputable def termClasses
    (Assignment Class Term : Type)
    [Fintype Assignment] [DecidableEq Assignment]
    [DecidableEq Class] [DecidableEq Term]
    {residualClass : Assignment -> Class}
    (cover : LabelledCover Assignment Class Term residualClass) : Finset Class := by
  classical
  exact cover.terms.image cover.label

end A631_LabelledCover

namespace A632_ClassCoverage
open A631_LabelledCover

variable {Assignment Class Term : Type}
variable [Fintype Assignment] [DecidableEq Assignment]
variable [DecidableEq Class] [DecidableEq Term]

theorem semantic_subset_term_classes
    (residualClass : Assignment -> Class)
    (cover : LabelledCover Assignment Class Term residualClass) :
    semanticClasses Assignment Class residualClass ⊆
      termClasses Assignment Class Term cover := by
  classical
  intro classValue classMember
  rcases Finset.mem_image.1 classMember with ⟨assignment, _inUniverse, classEq⟩
  rcases cover.complete assignment with ⟨term, termMember, covered⟩
  apply Finset.mem_image.2
  refine ⟨term, termMember, ?_⟩
  rw [← cover.safe term assignment covered]
  exact classEq

end A632_ClassCoverage

namespace A633_TermLowerBound
open A631_LabelledCover

variable {Assignment Class Term : Type}
variable [Fintype Assignment] [DecidableEq Assignment]
variable [DecidableEq Class] [DecidableEq Term]

theorem semantic_card_le_terms
    (residualClass : Assignment -> Class)
    (cover : LabelledCover Assignment Class Term residualClass) :
    (semanticClasses Assignment Class residualClass).card <= cover.terms.card := by
  classical
  calc
    (semanticClasses Assignment Class residualClass).card <=
        (termClasses Assignment Class Term cover).card :=
      Finset.card_le_card
        (A632_ClassCoverage.semantic_subset_term_classes residualClass cover)
    _ <= cover.terms.card := Finset.card_image_le

end A633_TermLowerBound

namespace A634_SingletonTermUpperBound

theorem singleton_term_count (n : Nat) :
    Fintype.card (Fin n -> Bool) = 2 ^ n :=
  ResearchFortyFirst.A599_AssignmentSpaceCardinality.assignment_card n

end A634_SingletonTermUpperBound

namespace A635_CubeCandidateBarrier

theorem candidate_count (n : Nat) :
    Fintype.card (ResearchFortyFirst.A586_Cube.Cube n) = 3 ^ n :=
  ResearchFortyFirst.A598_CubeSpaceCardinality.cube_card n

end A635_CubeCandidateBarrier

namespace A636_CubeSupport
open ResearchFortyFirst.A586_Cube

noncomputable def support {n : Nat} (cube : Cube n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun index => cube index ≠ none)

theorem support_card_le {n : Nat} (cube : Cube n) :
    (support cube).card <= n := by
  classical
  calc
    (support cube).card <= (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp

end A636_CubeSupport

namespace A637_CubeRegionBound
open ResearchFortyFirst.A586_Cube

variable {n : Nat}

theorem region_card_le (cube : Cube n) :
    (ResearchFortyFirst.A587_CubeRegion.region cube).card <= 2 ^ n := by
  classical
  calc
    (ResearchFortyFirst.A587_CubeRegion.region cube).card <=
        (Finset.univ : Finset (Fin n -> Bool)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ n := by simp

end A637_CubeRegionBound

namespace A638_DagTerminalLowerBound

structure SemanticDagCost where
  semanticClasses : Nat
  terminals : Nat
  totalNodes : Nat
  classesLeTerminals : semanticClasses <= terminals
  terminalsLeNodes : terminals <= totalNodes

theorem classes_le_nodes (cost : SemanticDagCost) :
    cost.semanticClasses <= cost.totalNodes :=
  le_trans cost.classesLeTerminals cost.terminalsLeNodes

end A638_DagTerminalLowerBound

namespace A639_QuotientDnfGap

theorem possible_gap :
    exists semanticClasses dnfTerms : Nat,
      semanticClasses = 2 ∧ dnfTerms = 35 ∧ semanticClasses < dnfTerms := by
  exact ⟨2, 35, rfl, rfl, by decide⟩

end A639_QuotientDnfGap

namespace A640_QuotientDagGap

theorem possible_gap :
    exists semanticClasses dagNodes : Nat,
      semanticClasses = 16 ∧ dagNodes = 70 ∧ semanticClasses < dagNodes := by
  exact ⟨16, 70, rfl, rfl, by decide⟩

end A640_QuotientDagGap

namespace A641_RepresentationIncomparability

theorem dnf_can_be_smaller : exists dnf dag : Nat, dnf < dag :=
  ⟨35, 70, by decide⟩

theorem dag_can_be_smaller : exists dnf dag : Nat, dag < dnf :=
  ⟨70, 35, by decide⟩

end A641_RepresentationIncomparability

namespace A642_RepresentationPortfolio

structure Candidate (specification : Prop) where
  answer : Bool
  work : Nat
  exact : answer = true ↔ specification

def choose {specification : Prop}
    (dnf dag : Candidate specification) : Candidate specification :=
  if dnf.work <= dag.work then dnf else dag

theorem chosen_exact {specification : Prop}
    (dnf dag : Candidate specification) :
    (choose dnf dag).answer = true ↔ specification := by
  unfold choose
  split
  · exact dnf.exact
  · exact dag.exact

theorem chosen_work_le_dnf {specification : Prop}
    (dnf dag : Candidate specification) :
    (choose dnf dag).work <= dnf.work := by
  unfold choose
  split
  · exact le_rfl
  · rename_i h
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem chosen_work_le_dag {specification : Prop}
    (dnf dag : Candidate specification) :
    (choose dnf dag).work <= dag.work := by
  unfold choose
  split
  · rename_i h
    exact h
  · exact le_rfl

end A642_RepresentationPortfolio

namespace A643_BackdoorDNF

structure BackdoorDNF (Input Term : Type) where
  terms : List Term
  covers : Term -> Input -> Prop
  safe : Term -> Prop
  tractable : Term -> Prop
  complete : forall item, exists term, term ∈ terms ∧ covers term item
  allSafe : forall term, term ∈ terms -> safe term
  allTractable : forall term, term ∈ terms -> tractable term

end A643_BackdoorDNF

namespace A644_ConstructionObligation

structure Budget where
  termCount : Nat
  construction : Nat
  verification : Nat
  residualSolving : Nat

def total (budget : Budget) : Nat :=
  budget.construction + budget.verification + budget.residualSolving

theorem small_terms_do_not_bound_total :
    exists budget : Budget,
      budget.termCount = 1 ∧ total budget > budget.termCount := by
  refine ⟨⟨1, 2, 0, 0⟩, rfl, ?_⟩
  decide

end A644_ConstructionObligation

namespace A645_MultiRepresentationCollapse

variable {Language : Type}

structure UniformMultiRepresentationCompilers (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_multi_representation_compilers
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformMultiRepresentationCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A645_MultiRepresentationCollapse

end PIsNPOrNot.ResearchFortyFourth