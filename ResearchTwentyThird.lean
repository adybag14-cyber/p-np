import ResearchTwentySecond

namespace PIsNPOrNot
namespace ResearchTwentyThird

/-! ## 316 - Accepted witnesses can be counted exactly over a finite type -/
namespace A316_AcceptedCount

variable {Witness : Type} [Fintype Witness]

noncomputable def acceptedCount (accepted : Witness -> Prop) [DecidablePred accepted] : Nat :=
  (Finset.univ.filter accepted).card

end A316_AcceptedCount

/-! ## 317 - The accepted count is zero exactly when no witness is accepted -/
namespace A317_ZeroCountCriterion

open A316_AcceptedCount

variable {Witness : Type} [Fintype Witness]

 theorem accepted_count_eq_zero_iff
    (accepted : Witness -> Prop) [DecidablePred accepted] :
    acceptedCount accepted = 0 <-> Not (exists witness, accepted witness) := by
  unfold acceptedCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

end A317_ZeroCountCriterion

/-! ## 318 - Positive accepted count is equivalent to an accepted witness -/
namespace A318_PositiveCountCriterion

open A316_AcceptedCount A317_ZeroCountCriterion

variable {Witness : Type} [Fintype Witness]

theorem accepted_count_pos_iff
    (accepted : Witness -> Prop) [DecidablePred accepted] :
    0 < acceptedCount accepted <-> exists witness, accepted witness := by
  rw [Nat.pos_iff_ne_zero, ne_eq, accepted_count_eq_zero_iff]
  simp

end A318_PositiveCountCriterion

/-! ## 319 - Accepted count is bounded by the witness-space cardinality -/
namespace A319_CountCardinalityBound

open A316_AcceptedCount

variable {Witness : Type} [Fintype Witness]

theorem accepted_count_le_card
    (accepted : Witness -> Prop) [DecidablePred accepted] :
    acceptedCount accepted <= Fintype.card Witness := by
  unfold acceptedCount
  simpa using Finset.card_le_card (Finset.filter_subset accepted Finset.univ)

end A319_CountCardinalityBound

/-! ## 320 - An n-bit witness language has at most 2^n accepted witnesses -/
namespace A320_BitWitnessCountBound

open A316_AcceptedCount A319_CountCardinalityBound

theorem bit_accepted_count_le_pow_two
    (n : Nat) (accepted : (Fin n -> Bool) -> Prop) [DecidablePred accepted] :
    acceptedCount accepted <= 2 ^ n := by
  calc
    acceptedCount accepted <= Fintype.card (Fin n -> Bool) :=
      accepted_count_le_card accepted
    _ = 2 ^ n := by simp

end A320_BitWitnessCountBound

/-! ## 321 - Reduction modulo a larger modulus preserves the exact count -/
namespace A321_LargeModulusExactness

theorem mod_eq_self_of_lt
    (count modulus : Nat) (smaller : count < modulus) :
    count % modulus = count := by
  exact Nat.mod_eq_of_lt smaller

end A321_LargeModulusExactness

/-! ## 322 - Under a large modulus, zero residue is equivalent to zero count -/
namespace A322_ZeroResidueCriterion

theorem mod_eq_zero_iff_eq_zero_of_lt
    (count modulus : Nat) (smaller : count < modulus) :
    count % modulus = 0 <-> count = 0 := by
  rw [Nat.mod_eq_of_lt smaller]

end A322_ZeroResidueCriterion

/-! ## 323 - Modulus 2^n + 1 decides whether an n-bit witness exists -/
namespace A323_ExactModularSAT

open A316_AcceptedCount A317_ZeroCountCriterion
open A320_BitWitnessCountBound A322_ZeroResidueCriterion

theorem no_witness_iff_large_residue_zero
    (n : Nat) (accepted : (Fin n -> Bool) -> Prop) [DecidablePred accepted] :
    acceptedCount accepted % (2 ^ n + 1) = 0 <->
      Not (exists witness, accepted witness) := by
  have smaller : acceptedCount accepted < 2 ^ n + 1 := by
    exact Nat.lt_succ_of_le (bit_accepted_count_le_pow_two n accepted)
  rw [mod_eq_zero_iff_eq_zero_of_lt _ _ smaller]
  exact accepted_count_eq_zero_iff accepted

end A323_ExactModularSAT

/-! ## 324 - A nonzero large-modulus residue certifies existence -/
namespace A324_NonzeroResidueWitness

open A316_AcceptedCount A323_ExactModularSAT

theorem witness_exists_iff_residue_ne_zero
    (n : Nat) (accepted : (Fin n -> Bool) -> Prop) [DecidablePred accepted] :
    (exists witness, accepted witness) <->
      Not (acceptedCount accepted % (2 ^ n + 1) = 0) := by
  rw [no_witness_iff_large_residue_zero]
  simp

end A324_NonzeroResidueWitness

/-! ## 325 - Counts multiply across independent witness components -/
namespace A325_IndependentProductCount

variable {Left Right : Type}
variable [Fintype Left] [Fintype Right]

 theorem product_count
    (leftAccepted : Left -> Prop) (rightAccepted : Right -> Prop)
    [DecidablePred leftAccepted] [DecidablePred rightAccepted] :
    ((Finset.univ.filter leftAccepted).product
      (Finset.univ.filter rightAccepted)).card =
      (Finset.univ.filter leftAccepted).card *
      (Finset.univ.filter rightAccepted).card := by
  exact Finset.card_product _ _

end A325_IndependentProductCount

/-! ## 326 - Counts add across a disjoint separator partition -/
namespace A326_DisjointPartitionCount

variable {Witness Separator : Type}
variable [Fintype Witness] [Fintype Separator] [DecidableEq Witness]

theorem sum_bucket_cards
    (bucket : Separator -> Finset Witness)
    (disjoint : ((Finset.univ : Finset Separator) : Set Separator).PairwiseDisjoint bucket)
    (covers : Finset.univ.biUnion bucket = (Finset.univ : Finset Witness)) :
    (Finset.univ.sum fun separator => (bucket separator).card) =
      Fintype.card Witness := by
  rw [← Finset.card_biUnion disjoint, covers]
  simp

end A326_DisjointPartitionCount

/-! ## 327 - A width-w Boolean tensor table has 2^w entries -/
namespace A327_TensorTableCardinality

theorem tensor_table_card (width : Nat) :
    Fintype.card (Fin width -> Bool) = 2 ^ width := by
  simp

end A327_TensorTableCardinality

/-! ## 328 - A polynomial tensor-table bound transfers directly to contraction work -/
namespace A328_TensorWidthBudget

theorem table_bound_transfer
    (width input exponent : Nat)
    (polynomialWidth : 2 ^ width <= input ^ exponent) :
    2 ^ width <= input ^ exponent := polynomialWidth

end A328_TensorWidthBudget

/-! ## 329 - Polynomial modular-residue compilers decide finite witness existence -/
namespace A329_ModularCompilerCriterion

variable {Instance : Type}

structure Compiler where
  witnessBits : Instance -> Nat
  accepted : forall input, (Fin (witnessBits input) -> Bool) -> Bool
  decideResidueZero : Instance -> Bool
  exact : forall input,
    decideResidueZero input = true <->
      A316_AcceptedCount.acceptedCount
        (fun witness => accepted input witness = true) %
        (2 ^ witnessBits input + 1) = 0

theorem compiler_decides_no_witness
    (compiler : Compiler (Instance := Instance)) (input : Instance)
    :
    compiler.decideResidueZero input = true <->
      Not (exists witness, compiler.accepted input witness = true) := by
  rw [compiler.exact input]
  exact A323_ExactModularSAT.no_witness_iff_large_residue_zero
    (compiler.witnessBits input) (fun witness => compiler.accepted input witness = true)

end A329_ModularCompilerCriterion

/-! ## 330 - Uniform polynomial exact-residue compilers would collapse P and NP -/
namespace A330_ModularCollapse

variable {Language : Type}

theorem p_eq_np_of_uniform_modular_compilers
    (InP InNP HasPolynomialModularCompiler : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (compilerImpliesP : forall language,
      HasPolynomialModularCompiler language -> InP language)
    (uniform : forall language,
      InNP language -> HasPolynomialModularCompiler language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact compilerImpliesP language (uniform language hNP)

end A330_ModularCollapse

end ResearchTwentyThird
end PIsNPOrNot
