import ResearchFortySecond

namespace PIsNPOrNot.ResearchFortyThird

namespace A616_AcceptedTerm
open ResearchFortyFirst.A589_SafeTerm
variable {n : Nat} {Payload : Type}
structure AcceptedTerm (feature : (Fin n -> Bool) -> Payload -> Bool) where
  base : SafeTerm feature
  payload : Payload
  accepted : feature base.representative payload = true
end A616_AcceptedTerm

namespace A617_AcceptedTermTransport
open ResearchFortyFirst.A586_Cube
open A616_AcceptedTerm
variable {n : Nat} {Payload : Type}
theorem witness_for_extension
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (term : AcceptedTerm feature) (cut : Fin n -> Bool)
    (hExt : Extends cut term.base.cube) :
    exists payload, feature cut payload = true := by
  exact ⟨term.payload,
    ResearchFortyFirst.A591_AcceptingTermTransport.accepting_payload_transports
      feature term.base term.payload term.accepted cut hExt⟩
end A617_AcceptedTermTransport

namespace A618_RejectedTerm
open ResearchFortyFirst.A589_SafeTerm
variable {n : Nat} {Payload : Type}
structure RejectedTerm (feature : (Fin n -> Bool) -> Payload -> Bool) where
  base : SafeTerm feature
  rejected : forall payload, feature base.representative payload = false
end A618_RejectedTerm

namespace A619_RejectedTermTransport
open ResearchFortyFirst.A586_Cube
open A618_RejectedTerm
variable {n : Nat} {Payload : Type}
theorem rejects_extension
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (term : RejectedTerm feature) (cut : Fin n -> Bool)
    (hExt : Extends cut term.base.cube) :
    forall payload, feature cut payload = false :=
  ResearchFortyFirst.A592_RejectingTermTransport.rejection_transports
    feature term.base term.rejected cut hExt
end A619_RejectedTermTransport

namespace A620_ClassifiedTerm
open ResearchFortyFirst.A589_SafeTerm
variable {n : Nat} {Payload : Type}
structure ClassifiedTerm (feature : (Fin n -> Bool) -> Payload -> Bool) where
  base : SafeTerm feature
  answer : Bool
  exact : answer = true ↔ exists payload, feature base.representative payload = true
end A620_ClassifiedTerm

namespace A621_ClassifiedTransport
open ResearchFortyFirst.A586_Cube
open A620_ClassifiedTerm
variable {n : Nat} {Payload : Type}
theorem answer_exact_for_extension
    (feature : (Fin n -> Bool) -> Payload -> Bool)
    (term : ClassifiedTerm feature) (cut : Fin n -> Bool)
    (hExt : Extends cut term.base.cube) :
    term.answer = true ↔ exists payload, feature cut payload = true := by
  constructor
  · intro answerTrue
    rcases term.exact.1 answerTrue with ⟨payload, accepted⟩
    exact ⟨payload,
      ResearchFortyFirst.A591_AcceptingTermTransport.accepting_payload_transports
        feature term.base payload accepted cut hExt⟩
  · rintro ⟨payload, accepted⟩
    apply term.exact.2
    refine ⟨payload, ?_⟩
    rw [← ResearchFortyFirst.A590_SafeTermOutput.output_eq
      feature term.base cut payload hExt]
    exact accepted
end A621_ClassifiedTransport

namespace A622_ClassifiedPlan
open ResearchFortyFirst.A586_Cube
open A620_ClassifiedTerm
variable {n : Nat} {Payload : Type}
structure Plan (feature : (Fin n -> Bool) -> Payload -> Bool) where
  terms : List (ClassifiedTerm feature)
  complete : forall cut, exists term, term ∈ terms ∧ Extends cut term.base.cube
end A622_ClassifiedPlan

namespace A623_AnyAnswer
variable {Term : Type}
def anyAnswer (answer : Term -> Bool) : List Term -> Bool
  | [] => false
  | term :: rest => answer term || anyAnswer answer rest

theorem anyAnswer_eq_true_iff (answer : Term -> Bool) (terms : List Term) :
    anyAnswer answer terms = true ↔
      exists term, term ∈ terms ∧ answer term = true := by
  induction terms with
  | nil => simp [anyAnswer]
  | cons head tail ih => simp [anyAnswer, ih]
end A623_AnyAnswer

namespace A624_PlanDecision
open A620_ClassifiedTerm
open A622_ClassifiedPlan
variable {n : Nat} {Payload : Type}
def decide {feature : (Fin n -> Bool) -> Payload -> Bool}
    (plan : Plan feature) : Bool :=
  A623_AnyAnswer.anyAnswer (fun term => term.answer) plan.terms

theorem decide_correct
    (feature : (Fin n -> Bool) -> Payload -> Bool) (plan : Plan feature) :
    decide plan = true ↔ exists cut payload, feature cut payload = true := by
  constructor
  · intro accepted
    rcases (A623_AnyAnswer.anyAnswer_eq_true_iff
      (fun term : ClassifiedTerm feature => term.answer) plan.terms).1 accepted with
      ⟨term, _member, termTrue⟩
    rcases term.exact.1 termTrue with ⟨payload, payloadAccepted⟩
    exact ⟨term.base.representative, payload, payloadAccepted⟩
  · rintro ⟨cut, payload, payloadAccepted⟩
    rcases plan.complete cut with ⟨term, member, hExt⟩
    apply (A623_AnyAnswer.anyAnswer_eq_true_iff
      (fun term : ClassifiedTerm feature => term.answer) plan.terms).2
    refine ⟨term, member, ?_⟩
    exact (A621_ClassifiedTransport.answer_exact_for_extension
      feature term cut hExt).2 ⟨payload, payloadAccepted⟩
end A624_PlanDecision

namespace A625_PlanWitnessRecovery
open A622_ClassifiedPlan
variable {n : Nat} {Payload : Type}
theorem recover
    (feature : (Fin n -> Bool) -> Payload -> Bool) (plan : Plan feature)
    (accepted : A624_PlanDecision.decide plan = true) :
    exists cut payload, feature cut payload = true :=
  (A624_PlanDecision.decide_correct feature plan).1 accepted
end A625_PlanWitnessRecovery

namespace A626_PlanRejection
open A622_ClassifiedPlan
variable {n : Nat} {Payload : Type}
theorem no_witness_of_false
    (feature : (Fin n -> Bool) -> Payload -> Bool) (plan : Plan feature)
    (rejected : A624_PlanDecision.decide plan = false) :
    ¬ (exists cut payload, feature cut payload = true) := by
  intro witness
  have trueAnswer := (A624_PlanDecision.decide_correct feature plan).2 witness
  rw [rejected] at trueAnswer
  contradiction
end A626_PlanRejection

namespace A627_CoverageCertificate
structure Coverage (Cut Term : Type) where
  covers : Term -> Cut -> Prop
  terms : List Term
  complete : forall cut, exists term, term ∈ terms ∧ covers term cut

theorem covers_every_cut {Cut Term : Type}
    (certificate : Coverage Cut Term) (cut : Cut) :
    exists term, term ∈ certificate.terms ∧ certificate.covers term cut :=
  certificate.complete cut
end A627_CoverageCertificate

namespace A628_CertifiedPlanWork
structure Work where
  termConstruction : Nat
  safetyChecking : Nat
  coverageChecking : Nat
  representativeSolving : Nat

def total (work : Work) : Nat :=
  work.termConstruction + work.safetyChecking +
    work.coverageChecking + work.representativeSolving

theorem total_le
    (work : Work) (a b c d budget : Nat)
    (ha : work.termConstruction <= a) (hb : work.safetyChecking <= b)
    (hc : work.coverageChecking <= c) (hd : work.representativeSolving <= d)
    (sumBound : a + b + c + d <= budget) : total work <= budget := by
  unfold total
  omega
end A628_CertifiedPlanWork

namespace A629_BaselineSafePlanChoice
structure Candidate (specification : Prop) where
  answer : Bool
  work : Nat
  exact : answer = true ↔ specification

def choose {specification : Prop}
    (baseline candidate : Candidate specification) : Candidate specification :=
  if candidate.work < baseline.work then candidate else baseline

theorem chosen_exact {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).answer = true ↔ specification := by
  unfold choose
  split
  · exact candidate.exact
  · exact baseline.exact

theorem chosen_work_le_baseline {specification : Prop}
    (baseline candidate : Candidate specification) :
    (choose baseline candidate).work <= baseline.work := by
  unfold choose
  split
  · rename_i h
    exact Nat.le_of_lt h
  · exact le_rfl
end A629_BaselineSafePlanChoice

namespace A630_ProofCarryingCubeCollapse
variable {Language : Type}
structure UniformProofCarryingPlans (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language, language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language, hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_proof_carrying_cube_plans
    (PClass NPClass : Set Language) (pSubsetNP : PClass ⊆ NPClass)
    (plans : UniformProofCarryingPlans PClass NPClass) : PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact plans.compilerGivesP language (plans.allNPHaveCompiler language inNP)
end A630_ProofCarryingCubeCollapse

end PIsNPOrNot.ResearchFortyThird