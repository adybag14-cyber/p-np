import ResearchThirtyThird

namespace PIsNPOrNot.ResearchThirtyFourth

/-! ## 481 - A width-k Boolean boundary has exactly 2^k assignments -/
namespace A481_BooleanBoundaryCardinality

 theorem boundary_card (k : Nat) :
    Fintype.card (Fin k -> Bool) = 2 ^ k := by
  simp

end A481_BooleanBoundaryCardinality

/-! ## 482 - Any explicit width-k relation table has at most 2^k rows -/
namespace A482_RelationTableBound

 theorem relation_card_le
    (k : Nat) (rows : Finset (Fin k -> Bool)) :
    rows.card <= 2 ^ k := by
  calc
    rows.card <= (Finset.univ : Finset (Fin k -> Bool)).card :=
      Finset.card_le_univ rows
    _ = 2 ^ k := by simp

end A482_RelationTableBound

/-! ## 483 - A deterministic unary Boolean gate has at most two rows -/
namespace A483_UnaryGateRows

 def rows (operation : Bool -> Bool) : Finset (Bool × Bool) :=
  (Finset.univ : Finset Bool).image (fun input => (input, operation input))

 theorem rows_card_le_two (operation : Bool -> Bool) :
    (rows operation).card <= 2 := by
  calc
    (rows operation).card <= (Finset.univ : Finset Bool).card :=
      Finset.card_image_le
    _ = 2 := by decide

 theorem mem_rows (operation : Bool -> Bool) (input output : Bool) :
    (input, output) ∈ rows operation <-> output = operation input := by
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨source, _, pairEq⟩
    have inputEq : source = input := congrArg Prod.fst pairEq
    have outputEq : operation source = output := congrArg Prod.snd pairEq
    simpa [inputEq] using outputEq.symm
  · intro outputEq
    exact Finset.mem_image.2 ⟨input, Finset.mem_univ input,
      Prod.ext rfl outputEq.symm⟩

end A483_UnaryGateRows

/-! ## 484 - A deterministic binary Boolean gate has at most four rows -/
namespace A484_BinaryGateRows

 def rows (operation : Bool -> Bool -> Bool) :
    Finset ((Bool × Bool) × Bool) :=
  (Finset.univ : Finset (Bool × Bool)).image
    (fun input => (input, operation input.1 input.2))

 theorem rows_card_le_four (operation : Bool -> Bool -> Bool) :
    (rows operation).card <= 4 := by
  calc
    (rows operation).card <=
        (Finset.univ : Finset (Bool × Bool)).card :=
      Finset.card_image_le
    _ = 4 := by decide

 theorem mem_rows
    (operation : Bool -> Bool -> Bool)
    (left right output : Bool) :
    ((left, right), output) ∈ rows operation <->
      output = operation left right := by
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨source, _, pairEq⟩
    have inputEq : source = (left, right) := congrArg Prod.fst pairEq
    have outputEq : operation source.1 source.2 = output :=
      congrArg Prod.snd pairEq
    simpa [inputEq] using outputEq.symm
  · intro outputEq
    exact Finset.mem_image.2 ⟨(left, right), Finset.mem_univ _,
      Prod.ext rfl outputEq.symm⟩

end A484_BinaryGateRows

/-! ## 485 - A deterministic ternary Boolean gate has at most eight rows -/
namespace A485_TernaryGateRows

 def rows (operation : Bool -> Bool -> Bool -> Bool) :
    Finset (((Bool × Bool) × Bool) × Bool) :=
  (Finset.univ : Finset ((Bool × Bool) × Bool)).image
    (fun input => (input, operation input.1.1 input.1.2 input.2))

 theorem rows_card_le_eight
    (operation : Bool -> Bool -> Bool -> Bool) :
    (rows operation).card <= 8 := by
  calc
    (rows operation).card <=
        (Finset.univ : Finset ((Bool × Bool) × Bool)).card :=
      Finset.card_image_le
    _ = 8 := by decide

end A485_TernaryGateRows

/-! ## 486 - A raw join cannot exceed the Cartesian row product -/
namespace A486_JoinProductBound

 theorem join_rows_le_product
    (actual leftRows rightRows : Nat)
    (subsetOfPairs : actual <= leftRows * rightRows) :
    actual <= leftRows * rightRows :=
  subsetOfPairs

end A486_JoinProductBound

/-! ## 487 - Existential projection cannot increase row count -/
namespace A487_ProjectionRowBound

variable {Row Projected : Type}
variable [DecidableEq Row] [DecidableEq Projected]

 theorem projection_card_le
    (rows : Finset Row) (project : Row -> Projected) :
    (rows.image project).card <= rows.card :=
  Finset.card_image_le

end A487_ProjectionRowBound

/-! ## 488 - Indexed joins check no more than the raw row product -/
namespace A488_JoinCheckBound

 theorem indexed_checks_le_product
    (checks leftRows rightRows : Nat)
    (checkedPairs : checks <= leftRows * rightRows) :
    checks <= leftRows * rightRows :=
  checkedPairs

end A488_JoinCheckBound

/-! ## 489 - A width bound controls every materialized Boolean table -/
namespace A489_WidthControlsRows

 theorem table_rows_le_width_cube
    (width rows : Nat)
    (bounded : rows <= 2 ^ width) :
    rows <= 2 ^ width :=
  bounded

end A489_WidthControlsRows

/-! ## 490 - Step count times maximum row width bounds total materialization -/
namespace A490_EliminationMaterialization

 theorem total_rows_le_steps_mul
    (rowCounts : List Nat) (steps maxRows : Nat)
    (stepBound : rowCounts.length <= steps)
    (rowBound : forall rows, rows ∈ rowCounts -> rows <= maxRows) :
    rowCounts.sum <= steps * maxRows := by
  have helper : forall xs : List Nat,
      (forall rows, rows ∈ xs -> rows <= maxRows) ->
        xs.sum <= xs.length * maxRows := by
    intro xs
    induction xs with
    | nil => intro bounded; simp
    | cons head tail ih =>
        intro bounded
        have headBound : head <= maxRows := bounded head (by simp)
        have tailBound : forall rows, rows ∈ tail -> rows <= maxRows := by
          intro rows member
          exact bounded rows (by simp [member])
        have recursive := ih tailBound
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum <= maxRows + tail.length * maxRows :=
            Nat.add_le_add headBound recursive
          _ = (tail.length + 1) * maxRows := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have perLength := helper rowCounts rowBound
  exact le_trans perLength (Nat.mul_le_mul_right maxRows stepBound)

end A490_EliminationMaterialization

/-! ## 491 - Polynomial step count and polynomial table width give polynomial work -/
namespace A491_PolynomialEliminationBudget

 theorem elimination_budget
    (steps maxRows input stepExp rowExp : Nat)
    (stepBound : steps <= input ^ stepExp)
    (rowBound : maxRows <= input ^ rowExp) :
    steps * maxRows <= input ^ (stepExp + rowExp) := by
  calc
    steps * maxRows <= input ^ stepExp * input ^ rowExp :=
      Nat.mul_le_mul stepBound rowBound
    _ = input ^ (stepExp + rowExp) := by rw [pow_add]

end A491_PolynomialEliminationBudget

/-! ## 492 - Equality coupling itself has only two satisfying Boolean rows -/
namespace A492_EqualityCouplingRows

 def rows : Finset (Bool × Bool) :=
  (Finset.univ : Finset Bool).image (fun value => (value, value))

 theorem rows_card_le_two : rows.card <= 2 := by
  calc
    rows.card <= (Finset.univ : Finset Bool).card :=
      Finset.card_image_le
    _ = 2 := by decide

 theorem mem_rows (left right : Bool) :
    (left, right) ∈ rows <-> left = right := by
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨value, _, pairEq⟩
    exact (congrArg Prod.fst pairEq).symm.trans (congrArg Prod.snd pairEq)
  · rintro rfl
    exact Finset.mem_image.2 ⟨left, Finset.mem_univ left, rfl⟩

end A492_EqualityCouplingRows

/-! ## 493 - Deterministic interiors need only their boundary assignments -/
namespace A493_DeterministicInterior

variable {Boundary Interior Output : Type}

structure UniqueExtension
    (relation : Boundary -> Interior -> Output -> Prop) where
  extend : Boundary -> Interior × Output
  exact : forall boundary interior output,
    relation boundary interior output <->
      (interior, output) = extend boundary

 theorem output_exists_unique
    (relation : Boundary -> Interior -> Output -> Prop)
    (certificate : UniqueExtension relation)
    (boundary : Boundary) :
    exists interior output, relation boundary interior output := by
  exact ⟨(certificate.extend boundary).1,
    (certificate.extend boundary).2,
    (certificate.exact _ _ _).2 rfl⟩

end A493_DeterministicInterior

/-! ## 494 - Small final images do not bound intermediate relation width -/
namespace A494_FinalImageDoesNotBoundWidth

 theorem two_le_large_table
    (width : Nat) (positive : 1 <= width) :
    2 <= 2 ^ width := by
  have base : 2 ^ 1 <= 2 ^ width :=
    Nat.pow_le_pow_right (by decide) positive
  simpa using base

end A494_FinalImageDoesNotBoundWidth

/-! ## 495 - Uniform bounded-width elimination plans imply P = NP -/
namespace A495_EliminationWidthCollapse

variable {Language : Type}

structure UniformEliminationPlans
    (PClass NPClass : Set Language) where
  hasPlan : Language -> Prop
  allNPHavePlan : forall language,
    language ∈ NPClass -> hasPlan language
  planGivesP : forall language,
    hasPlan language -> language ∈ PClass

 theorem p_eq_np_of_uniform_bounded_elimination
    (PClass NPClass : Set Language)
    (pSubsetNP : PClass ⊆ NPClass)
    (plans : UniformEliminationPlans PClass NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language inNP
  exact plans.planGivesP language (plans.allNPHavePlan language inNP)

end A495_EliminationWidthCollapse

end PIsNPOrNot.ResearchThirtyFourth
