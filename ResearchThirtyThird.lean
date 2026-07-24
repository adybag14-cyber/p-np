import ResearchThirtySecond

namespace PIsNPOrNot.ResearchThirtyThird

/-! ## 466 - Read-once Boolean computation trees -/
namespace A466_ReadOnceFormula

inductive Formula where
  | free : Formula
  | const : Bool -> Formula
  | unary : (Bool -> Bool) -> Formula -> Formula
  | binary : (Bool -> Bool -> Bool) -> Formula -> Formula -> Formula

end A466_ReadOnceFormula

/-! ## 467 - Every formula carries its own independent witness type -/
namespace A467_DependentWitness

open A466_ReadOnceFormula

 def Witness : Formula -> Type
  | Formula.free => Bool
  | Formula.const _ => Unit
  | Formula.unary _ child => Witness child
  | Formula.binary _ left right => Witness left × Witness right

 def evaluate : (formula : Formula) -> Witness formula -> Bool
  | Formula.free, value => value
  | Formula.const value, _ => value
  | Formula.unary operation child, witness =>
      operation (evaluate child witness)
  | Formula.binary operation left right, witness =>
      operation (evaluate left witness.1) (evaluate right witness.2)

end A467_DependentWitness

/-! ## 468 - Possible outputs are computed bottom-up -/
namespace A468_PossibleOutputs

open A466_ReadOnceFormula

 def possible : Formula -> Finset Bool
  | Formula.free => Finset.univ
  | Formula.const value => {value}
  | Formula.unary operation child =>
      (possible child).image operation
  | Formula.binary operation left right =>
      ((possible left).product (possible right)).image
        (fun values => operation values.1 values.2)

end A468_PossibleOutputs

/-! ## 469 - Bottom-up possible outputs are exact -/
namespace A469_PossibleOutputsExact

open A466_ReadOnceFormula A467_DependentWitness A468_PossibleOutputs

 theorem possible_exact (formula : Formula) (output : Bool) :
    output ∈ possible formula <->
      exists witness : Witness formula, evaluate formula witness = output := by
  induction formula generalizing output with
  | free =>
      simp [possible, Witness, evaluate]
  | const value =>
      constructor
      · intro member
        have outputEq : output = value := by simpa [possible] using member
        exact ⟨(), by simpa [Witness, evaluate, outputEq]⟩
      · rintro ⟨witness, valueEq⟩
        simpa [possible, Witness, evaluate] using valueEq.symm
  | unary operation child ih =>
      constructor
      · intro member
        rcases Finset.mem_image.1 member with ⟨childOutput, childMember, outputEq⟩
        rcases (ih childOutput).1 childMember with ⟨witness, witnessEq⟩
        exact ⟨witness, by simpa [Witness, evaluate, witnessEq] using outputEq⟩
      · rintro ⟨witness, valueEq⟩
        apply Finset.mem_image.2
        refine ⟨evaluate child witness, ?_, ?_⟩
        · exact (ih _).2 ⟨witness, rfl⟩
        · simpa [Witness, evaluate] using valueEq
  | binary operation left right leftIH rightIH =>
      constructor
      · intro member
        rcases Finset.mem_image.1 member with ⟨values, pairMember, outputEq⟩
        rcases Finset.mem_product.1 pairMember with ⟨leftMember, rightMember⟩
        rcases (leftIH values.1).1 leftMember with ⟨leftWitness, leftEq⟩
        rcases (rightIH values.2).1 rightMember with ⟨rightWitness, rightEq⟩
        exact ⟨(leftWitness, rightWitness), by
          simpa [Witness, evaluate, leftEq, rightEq] using outputEq⟩
      · rintro ⟨⟨leftWitness, rightWitness⟩, valueEq⟩
        apply Finset.mem_image.2
        refine ⟨(evaluate left leftWitness, evaluate right rightWitness), ?_, ?_⟩
        · exact Finset.mem_product.2 ⟨
            (leftIH _).2 ⟨leftWitness, rfl⟩,
            (rightIH _).2 ⟨rightWitness, rfl⟩⟩
        · simpa [Witness, evaluate] using valueEq

end A469_PossibleOutputsExact

/-! ## 470 - Every read-once subtree has at most two output states -/
namespace A470_TwoStateWidth

open A466_ReadOnceFormula A468_PossibleOutputs

 theorem possible_card_le_two (formula : Formula) :
    (possible formula).card <= 2 := by
  calc
    (possible formula).card <= (Finset.univ : Finset Bool).card :=
      Finset.card_le_univ _
    _ = 2 := by decide

end A470_TwoStateWidth

/-! ## 471 - Formula size counts one unit per gate or free input -/
namespace A471_FormulaSize

open A466_ReadOnceFormula

 def nodeCount : Formula -> Nat
  | Formula.free => 1
  | Formula.const _ => 1
  | Formula.unary _ child => nodeCount child + 1
  | Formula.binary _ left right => nodeCount left + nodeCount right + 1

end A471_FormulaSize

/-! ## 472 - Constant-width message passing has linear work on formula trees -/
namespace A472_LinearFormulaWork

open A466_ReadOnceFormula A471_FormulaSize

 def work : Formula -> Nat
  | Formula.free => 1
  | Formula.const _ => 1
  | Formula.unary _ child => work child + 2
  | Formula.binary _ left right => work left + work right + 4

 theorem work_le_four_mul_nodes (formula : Formula) :
    work formula <= 4 * nodeCount formula := by
  induction formula with
  | free => simp [work, nodeCount]
  | const value => simp [work, nodeCount]
  | unary operation child ih =>
      simp only [work, nodeCount]
      omega
  | binary operation left right leftIH rightIH =>
      simp only [work, nodeCount]
      omega

end A472_LinearFormulaWork

/-! ## 473 - Formula satisfiability is exactly membership of true -/
namespace A473_ReadOnceSAT

open A466_ReadOnceFormula A467_DependentWitness A468_PossibleOutputs
open A469_PossibleOutputsExact

 theorem true_mem_iff_satisfiable (formula : Formula) :
    true ∈ possible formula <->
      exists witness : Witness formula, evaluate formula witness = true :=
  possible_exact formula true

end A473_ReadOnceSAT

/-! ## 474 - The executable read-once solver is exact -/
namespace A474_ReadOnceSolver

open A466_ReadOnceFormula A467_DependentWitness A468_PossibleOutputs
open A469_PossibleOutputsExact

 def solve (formula : Formula) : Bool :=
  decide (true ∈ possible formula)

 theorem solve_correct (formula : Formula) :
    solve formula = true <->
      exists witness : Witness formula, evaluate formula witness = true := by
  simp [solve, possible_exact]

end A474_ReadOnceSolver

/-! ## 475 - Duplicating a shared input as independent leaves is unsound -/
namespace A475_ReconvergenceCounterexample

open A466_ReadOnceFormula A467_DependentWitness A468_PossibleOutputs
open A469_PossibleOutputsExact

 def relaxedContradiction : Formula :=
  Formula.binary (fun left right => left && right)
    Formula.free
    (Formula.unary (fun value => !value) Formula.free)

 theorem relaxed_accepts : true ∈ possible relaxedContradiction := by
  apply (possible_exact relaxedContradiction true).2
  exact ⟨(true, false), rfl⟩

 def sharedContradiction (value : Bool) : Bool :=
  value && !value

 theorem shared_rejects (value : Bool) :
    sharedContradiction value = false := by
  cases value <;> rfl

 theorem no_shared_witness :
    ¬ (exists value, sharedContradiction value = true) := by
  rintro ⟨value, accepted⟩
  rw [shared_rejects value] at accepted
  contradiction

end A475_ReconvergenceCounterexample

/-! ## 476 - Equality coupling restores exact shared-input semantics -/
namespace A476_EqualityCoupling

variable {Shared : Type}

 theorem coupled_iff_shared
    (left right : Shared -> Prop) :
    (exists value, left value /\ right value) <->
      exists leftValue rightValue,
        leftValue = rightValue /\ left leftValue /\ right rightValue := by
  constructor
  · rintro ⟨value, leftHolds, rightHolds⟩
    exact ⟨value, value, rfl, leftHolds, rightHolds⟩
  · rintro ⟨leftValue, rightValue, same, leftHolds, rightHolds⟩
    subst same
    exact ⟨leftValue, leftHolds, rightHolds⟩

end A476_EqualityCoupling

/-! ## 477 - k shared Boolean identities have exactly 2^k assignments -/
namespace A477_SharedAssignmentCount

 theorem shared_assignment_card (k : Nat) :
    Fintype.card (Fin k -> Bool) = 2 ^ k := by
  simp

end A477_SharedAssignmentCount

/-! ## 478 - Polynomially bounded shared assignments preserve polynomial work -/
namespace A478_SharedInterfaceBudget

 theorem shared_interface_budget
    (sharedAssignments localWork input sharedExp localExp : Nat)
    (sharedBound : sharedAssignments <= input ^ sharedExp)
    (localBound : localWork <= input ^ localExp) :
    sharedAssignments * localWork <=
      input ^ (sharedExp + localExp) := by
  calc
    sharedAssignments * localWork <=
        input ^ sharedExp * input ^ localExp :=
      Nat.mul_le_mul sharedBound localBound
    _ = input ^ (sharedExp + localExp) := by rw [pow_add]

end A478_SharedInterfaceBudget

/-! ## 479 - A circuit compiler must bound both tree work and shared interfaces -/
namespace A479_CircuitMessageCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  formulaNodes : Input -> Nat
  sharedAssignments : Input -> Nat
  localWork : Input -> Nat
  totalWork : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  nodeBound : forall input,
    formulaNodes input <= inputSize input ^ exponent
  sharedBound : forall input,
    sharedAssignments input <= inputSize input ^ exponent
  localBound : forall input,
    localWork input <= inputSize input ^ exponent
  workBound : forall input,
    totalWork input <=
      formulaNodes input * localWork input +
        sharedAssignments input * localWork input

 theorem compiler_exact
    (specification : Input -> Prop)
    (compiler : Compiler specification) (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A479_CircuitMessageCompiler

/-! ## 480 - Uniform polynomial circuit-message compilers imply P = NP -/
namespace A480_CircuitMessageCollapse

variable {Language : Type}

structure UniformCircuitCompilers
    (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language,
    hasCompiler language -> language ∈ PClass

 theorem p_eq_np_of_uniform_circuit_messages
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (compilers : UniformCircuitCompilers PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language inNP)

end A480_CircuitMessageCollapse

end PIsNPOrNot.ResearchThirtyThird
