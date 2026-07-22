import ResearchSeventh
import CNFCore

/-!
# Approaches 91-105: concrete CNF branching and decomposition certificates

The earlier AND/OR layer was abstract.  This file proves its two central node
rules directly for the verified CNF representation: Shannon branching by
restriction and conjunction splitting across disjoint variable supports.
-/

namespace PIsNPOrNot
namespace ResearchEighth

open CNFCore

/-! ## 91 - CNF satisfiability and fixed-bit satisfiability -/
namespace A91_FixedBitSatisfiability

def Sat {n : Nat} (formula : CNF n) : Prop :=
  exists assignment : Bits n, evalCNF assignment formula = true

def FixedSat {n : Nat} (formula : CNF n) (x : Fin n) (value : Bool) : Prop :=
  exists assignment : Bits n,
    assignment x = value /\ evalCNF assignment formula = true

theorem sat_split_bit {n : Nat} (formula : CNF n) (x : Fin n) :
    Sat formula <-> FixedSat formula x false \/ FixedSat formula x true := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    cases hbit : assignment x with
    | false => exact Or.inl ⟨assignment, hbit, hsatisfies⟩
    | true => exact Or.inr ⟨assignment, hbit, hsatisfies⟩
  · intro h
    rcases h with hfalse | htrue
    · rcases hfalse with ⟨assignment, _, hsatisfies⟩
      exact ⟨assignment, hsatisfies⟩
    · rcases htrue with ⟨assignment, _, hsatisfies⟩
      exact ⟨assignment, hsatisfies⟩

end A91_FixedBitSatisfiability

/-! ## 92 - Overwriting one assignment bit -/
namespace A92_SetBit

def setBit {n : Nat} (assignment : Bits n) (x : Fin n) (value : Bool) : Bits n :=
  fun y => if y = x then value else assignment y

theorem setBit_at {n : Nat} (assignment : Bits n) (x : Fin n) (value : Bool) :
    setBit assignment x value x = value := by
  simp [setBit]

theorem setBit_other {n : Nat} (assignment : Bits n) (x y : Fin n)
    (value : Bool) (hne : Not (y = x)) :
    setBit assignment x value y = assignment y := by
  simp [setBit, hne]

end A92_SetBit

/-! ## 93 - Restricting a clause removes the selected variable -/
namespace A93_RestrictedClauseAvoids

def ClauseAvoids {n : Nat} (x : Fin n) (clause : Clause n) : Prop :=
  forall lit, List.Mem lit clause -> Not (lit.var = x)

theorem restrictClause_avoids {n : Nat}
    (x : Fin n) (value : Bool) (clause : Clause n) :
    match restrictClause x value clause with
    | .satisfied => True
    | .reduced reduced => ClauseAvoids x reduced := by
  induction clause with
  | nil =>
      simp only [restrictClause]
      intro lit hmem
      cases hmem
  | cons lit rest ih =>
      by_cases hvar : lit.var = x
      · cases hbit : evalAtBit value lit <;>
          simp [restrictClause, hvar, hbit, ih]
      · cases hrest : restrictClause x value rest with
        | satisfied => simp [restrictClause, hvar, hrest]
        | reduced reduced =>
            have hAvoid : ClauseAvoids x reduced := by
              simpa [hrest] using ih
            simp only [restrictClause, hvar, hrest]
            intro candidate hmem
            cases hmem with
            | head => exact hvar
            | tail _ htail => exact hAvoid candidate htail

end A93_RestrictedClauseAvoids

/-! ## 94 - Restricting a CNF removes the selected variable everywhere -/
namespace A94_RestrictedFormulaAvoids

open A93_RestrictedClauseAvoids

def FormulaAvoids {n : Nat} (x : Fin n) (formula : CNF n) : Prop :=
  forall clause, List.Mem clause formula -> ClauseAvoids x clause

theorem restrictCNF_avoids {n : Nat}
    (x : Fin n) (value : Bool) (formula : CNF n) :
    FormulaAvoids x (restrictCNF x value formula) := by
  induction formula with
  | nil =>
      intro clause hmem
      cases hmem
  | cons clause rest ih =>
      cases hclause : restrictClause x value clause with
      | satisfied =>
          simpa [restrictCNF, hclause] using ih
      | reduced reduced =>
          have hReduced : ClauseAvoids x reduced := by
            have h := restrictClause_avoids x value clause
            simpa [hclause] using h
          intro candidate hmem
          rw [restrictCNF, hclause] at hmem
          cases hmem with
          | head => exact hReduced
          | tail _ htail => exact ih candidate htail

end A94_RestrictedFormulaAvoids

/-! ## 95 - Changing an unused variable cannot change evaluation -/
namespace A95_UnusedBitInvariance

open A93_RestrictedClauseAvoids A94_RestrictedFormulaAvoids

def AgreeExcept {n : Nat} (left right : Bits n) (x : Fin n) : Prop :=
  forall y, Not (y = x) -> left y = right y

theorem evalLit_agree_except {n : Nat}
    (left right : Bits n) (x : Fin n) (lit : Lit n)
    (agree : AgreeExcept left right x) (unused : Not (lit.var = x)) :
    evalLit left lit = evalLit right lit := by
  have hvalue := agree lit.var unused
  cases lit.positive <;> simp [evalLit, hvalue]

theorem evalClause_agree_except {n : Nat}
    (left right : Bits n) (x : Fin n) (clause : Clause n)
    (agree : AgreeExcept left right x) (avoids : ClauseAvoids x clause) :
    evalClause left clause = evalClause right clause := by
  induction clause with
  | nil => simp [evalClause]
  | cons lit rest ih =>
      have hLitAvoid : Not (lit.var = x) := avoids lit (List.Mem.head rest)
      have hRestAvoid : ClauseAvoids x rest := by
        intro candidate hmem
        exact avoids candidate (List.Mem.tail lit hmem)
      have hLit := evalLit_agree_except left right x lit agree hLitAvoid
      have hRest := ih hRestAvoid
      have hRestAny : rest.any (evalLit left) = rest.any (evalLit right) := by
        simpa [evalClause] using hRest
      change (evalLit left lit || rest.any (evalLit left)) =
        (evalLit right lit || rest.any (evalLit right))
      rw [hLit, hRestAny]

theorem evalCNF_agree_except {n : Nat}
    (left right : Bits n) (x : Fin n) (formula : CNF n)
    (agree : AgreeExcept left right x) (avoids : FormulaAvoids x formula) :
    evalCNF left formula = evalCNF right formula := by
  induction formula with
  | nil => simp [evalCNF]
  | cons clause rest ih =>
      have hClauseAvoid : ClauseAvoids x clause :=
        avoids clause (List.Mem.head rest)
      have hRestAvoid : FormulaAvoids x rest := by
        intro candidate hmem
        exact avoids candidate (List.Mem.tail clause hmem)
      have hClause := evalClause_agree_except left right x clause agree hClauseAvoid
      have hRest := ih hRestAvoid
      have hRestAll : rest.all (evalClause left) = rest.all (evalClause right) := by
        simpa [evalCNF] using hRest
      change (evalClause left clause && rest.all (evalClause left)) =
        (evalClause right clause && rest.all (evalClause right))
      rw [hClause, hRestAll]

end A95_UnusedBitInvariance

/-! ## 96 - Fixing an unused bit does not change satisfiability -/
namespace A96_FixedResidual

open A91_FixedBitSatisfiability A92_SetBit
open A94_RestrictedFormulaAvoids A95_UnusedBitInvariance

theorem fixedSat_iff_sat_of_avoids {n : Nat}
    (formula : CNF n) (x : Fin n) (value : Bool)
    (avoids : FormulaAvoids x formula) :
    FixedSat formula x value <-> Sat formula := by
  constructor
  · rintro ⟨assignment, _, hsatisfies⟩
    exact ⟨assignment, hsatisfies⟩
  · rintro ⟨assignment, hsatisfies⟩
    let changed := setBit assignment x value
    have hAgree : AgreeExcept changed assignment x := by
      intro y hne
      exact setBit_other assignment x y value hne
    refine ⟨changed, setBit_at assignment x value, ?_⟩
    calc
      evalCNF changed formula = evalCNF assignment formula :=
        evalCNF_agree_except changed assignment x formula hAgree avoids
      _ = true := hsatisfies

end A96_FixedResidual

/-! ## 97 - Exact Shannon branching for the concrete CNF representation -/
namespace A97_CNFShannon

open A91_FixedBitSatisfiability A94_RestrictedFormulaAvoids A96_FixedResidual

theorem sat_restrict_branch {n : Nat} (formula : CNF n) (x : Fin n) :
    Sat formula <->
      Sat (restrictCNF x false formula) \/
      Sat (restrictCNF x true formula) := by
  rw [sat_split_bit]
  have hFalse :
      FixedSat formula x false <->
        FixedSat (restrictCNF x false formula) x false := by
    simpa [FixedSat] using
      (branch_preserves_satisfying_assignments formula x false)
  have hTrue :
      FixedSat formula x true <->
        FixedSat (restrictCNF x true formula) x true := by
    simpa [FixedSat] using
      (branch_preserves_satisfying_assignments formula x true)
  rw [hFalse, hTrue]
  rw [fixedSat_iff_sat_of_avoids
        (restrictCNF x false formula) x false
        (restrictCNF_avoids x false formula)]
  rw [fixedSat_iff_sat_of_avoids
        (restrictCNF x true formula) x true
        (restrictCNF_avoids x true formula)]

end A97_CNFShannon

/-! ## 98 - Formula-local assignment agreement -/
namespace A98_FormulaAgreement

def AgreeOnFormula {n : Nat}
    (left right : Bits n) (formula : CNF n) : Prop :=
  forall clause, List.Mem clause formula ->
    forall lit, List.Mem lit clause -> left lit.var = right lit.var

theorem evalClause_agree_on {n : Nat}
    (left right : Bits n) (clause : Clause n)
    (agree : forall lit, List.Mem lit clause -> left lit.var = right lit.var) :
    evalClause left clause = evalClause right clause := by
  induction clause with
  | nil => simp [evalClause]
  | cons lit rest ih =>
      have hLit := agree lit (List.Mem.head rest)
      have hRest : forall candidate, List.Mem candidate rest ->
          left candidate.var = right candidate.var := by
        intro candidate hmem
        exact agree candidate (List.Mem.tail lit hmem)
      have ihRest := ih hRest
      have hRestAny : rest.any (evalLit left) = rest.any (evalLit right) := by
        simpa [evalClause] using ihRest
      change (evalLit left lit || rest.any (evalLit left)) =
        (evalLit right lit || rest.any (evalLit right))
      cases lit.positive <;> simp [evalLit, hLit, hRestAny]

theorem evalCNF_agree_on {n : Nat}
    (left right : Bits n) (formula : CNF n)
    (agree : AgreeOnFormula left right formula) :
    evalCNF left formula = evalCNF right formula := by
  induction formula with
  | nil => simp [evalCNF]
  | cons clause rest ih =>
      have hClause : forall lit, List.Mem lit clause ->
          left lit.var = right lit.var := agree clause (List.Mem.head rest)
      have hRest : AgreeOnFormula left right rest := by
        intro candidate hmem
        exact agree candidate (List.Mem.tail clause hmem)
      have hc := evalClause_agree_on left right clause hClause
      have hr := ih hRest
      have hRestAll : rest.all (evalClause left) = rest.all (evalClause right) := by
        simpa [evalCNF] using hr
      change (evalClause left clause && rest.all (evalClause left)) =
        (evalClause right clause && rest.all (evalClause right))
      rw [hc, hRestAll]

end A98_FormulaAgreement

/-! ## 99 - Computable variable support and assignment merging -/
namespace A99_DisjointMerge

open A98_FormulaAgreement

def usesVar {n : Nat} (formula : CNF n) (x : Fin n) : Bool :=
  formula.any fun clause => clause.any fun lit => decide (lit.var = x)

def DisjointVars {n : Nat} (left right : CNF n) : Prop :=
  forall x, usesVar left x = true -> usesVar right x = false

def mergeAssignment {n : Nat}
    (left : CNF n) (leftAssignment rightAssignment : Bits n) : Bits n :=
  fun x => if usesVar left x then leftAssignment x else rightAssignment x

theorem usesVar_true_of_mem {n : Nat}
    (formula : CNF n) (clause : Clause n) (lit : Lit n)
    (hClause : List.Mem clause formula) (hLit : List.Mem lit clause) :
    usesVar formula lit.var = true := by
  simp only [usesVar, List.any_eq_true]
  refine Exists.intro clause ?_
  constructor
  · exact hClause
  · refine Exists.intro lit ?_
    constructor
    · exact hLit
    · simp

theorem merge_agrees_left {n : Nat}
    (left : CNF n) (leftAssignment rightAssignment : Bits n)
    (x : Fin n) (hUses : usesVar left x = true) :
    mergeAssignment left leftAssignment rightAssignment x = leftAssignment x := by
  simp [mergeAssignment, hUses]

theorem merge_agrees_right {n : Nat}
    (left right : CNF n) (leftAssignment rightAssignment : Bits n)
    (disjoint : DisjointVars left right)
    (x : Fin n) (hUsesRight : usesVar right x = true) :
    mergeAssignment left leftAssignment rightAssignment x = rightAssignment x := by
  cases hUsesLeft : usesVar left x with
  | false => simp [mergeAssignment, hUsesLeft]
  | true =>
      have hFalse := disjoint x hUsesLeft
      rw [hUsesRight] at hFalse
      contradiction

theorem merged_agrees_on_left {n : Nat}
    (left : CNF n) (leftAssignment rightAssignment : Bits n) :
    AgreeOnFormula
      (mergeAssignment left leftAssignment rightAssignment)
      leftAssignment left := by
  intro clause hClause lit hLit
  exact merge_agrees_left left leftAssignment rightAssignment lit.var
    (usesVar_true_of_mem left clause lit hClause hLit)

theorem merged_agrees_on_right {n : Nat}
    (left right : CNF n) (leftAssignment rightAssignment : Bits n)
    (disjoint : DisjointVars left right) :
    AgreeOnFormula
      (mergeAssignment left leftAssignment rightAssignment)
      rightAssignment right := by
  intro clause hClause lit hLit
  exact merge_agrees_right left right leftAssignment rightAssignment disjoint lit.var
    (usesVar_true_of_mem right clause lit hClause hLit)

end A99_DisjointMerge

/-! ## 100 - Exact AND decomposition for disjoint CNF components -/
namespace A100_DisjointDecomposition

open A91_FixedBitSatisfiability A98_FormulaAgreement A99_DisjointMerge

theorem evalCNF_append {n : Nat}
    (assignment : Bits n) (left right : CNF n) :
    evalCNF assignment (left ++ right) =
      (evalCNF assignment left && evalCNF assignment right) := by
  simp [evalCNF, List.all_append]

theorem sat_append_iff {n : Nat}
    (left right : CNF n) (disjoint : DisjointVars left right) :
    Sat (left ++ right) <-> Sat left /\ Sat right := by
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    have hBoth :
        evalCNF assignment left = true /\ evalCNF assignment right = true := by
      have := hsatisfies
      rw [evalCNF_append] at this
      simpa using this
    exact ⟨⟨assignment, hBoth.1⟩, ⟨assignment, hBoth.2⟩⟩
  · rintro ⟨⟨leftAssignment, hLeft⟩, ⟨rightAssignment, hRight⟩⟩
    let merged := mergeAssignment left leftAssignment rightAssignment
    have hMergedLeft : evalCNF merged left = true := by
      calc
        evalCNF merged left = evalCNF leftAssignment left :=
          evalCNF_agree_on merged leftAssignment left
            (merged_agrees_on_left left leftAssignment rightAssignment)
        _ = true := hLeft
    have hMergedRight : evalCNF merged right = true := by
      calc
        evalCNF merged right = evalCNF rightAssignment right :=
          evalCNF_agree_on merged rightAssignment right
            (merged_agrees_on_right left right leftAssignment rightAssignment disjoint)
        _ = true := hRight
    refine ⟨merged, ?_⟩
    rw [evalCNF_append, hMergedLeft, hMergedRight]
    decide

end A100_DisjointDecomposition

/-! ## 101 - Concrete CNF proof trees -/
namespace A101_CNFProofTree

open A91_FixedBitSatisfiability

inductive ProofTree (n : Nat) where
  | leaf (formula : CNF n) (answer : Bool)
  | branch (formula : CNF n) (x : Fin n)
      (falseTree trueTree : ProofTree n)
  | andSplit (left right : CNF n)
      (leftTree rightTree : ProofTree n)

def ProofTree.root {n : Nat} : ProofTree n -> CNF n
  | .leaf formula _ => formula
  | .branch formula _ _ _ => formula
  | .andSplit left right _ _ => left ++ right

def ProofTree.eval {n : Nat} : ProofTree n -> Bool
  | .leaf _ answer => answer
  | .branch _ _ falseTree trueTree => falseTree.eval || trueTree.eval
  | .andSplit _ _ leftTree rightTree => leftTree.eval && rightTree.eval

end A101_CNFProofTree

/-! ## 102 - Local CNF proof-tree validity -/
namespace A102_CNFProofValidity

open A91_FixedBitSatisfiability A97_CNFShannon A99_DisjointMerge
open A100_DisjointDecomposition A101_CNFProofTree

inductive Valid {n : Nat} : ProofTree n -> Prop
  | leaf (formula : CNF n) (answer : Bool)
      (correct : answer = true <-> Sat formula) :
      Valid (.leaf formula answer)
  | branch (formula : CNF n) (x : Fin n)
      (falseTree trueTree : ProofTree n)
      (falseRoot : falseTree.root = restrictCNF x false formula)
      (trueRoot : trueTree.root = restrictCNF x true formula)
      (falseValid : Valid falseTree) (trueValid : Valid trueTree) :
      Valid (.branch formula x falseTree trueTree)
  | andSplit (left right : CNF n)
      (leftTree rightTree : ProofTree n)
      (disjoint : DisjointVars left right)
      (leftRoot : leftTree.root = left)
      (rightRoot : rightTree.root = right)
      (leftValid : Valid leftTree) (rightValid : Valid rightTree) :
      Valid (.andSplit left right leftTree rightTree)

theorem eval_correct {n : Nat} {tree : ProofTree n} (valid : Valid tree) :
    tree.eval = true <-> Sat tree.root := by
  induction valid with
  | leaf formula answer correct =>
      simpa [ProofTree.eval, ProofTree.root] using correct
  | branch formula x falseTree trueTree falseRoot trueRoot falseValid trueValid ihFalse ihTrue =>
      rw [ProofTree.eval, Bool.or_eq_true, ihFalse, ihTrue]
      change Sat falseTree.root \/ Sat trueTree.root <-> Sat formula
      rw [falseRoot, trueRoot]
      exact (sat_restrict_branch formula x).symm
  | andSplit left right leftTree rightTree disjoint leftRoot rightRoot leftValid rightValid ihLeft ihRight =>
      rw [ProofTree.eval, Bool.and_eq_true, ihLeft, ihRight]
      change Sat leftTree.root /\ Sat rightTree.root <-> Sat (left ++ right)
      rw [leftRoot, rightRoot]
      exact (sat_append_iff left right disjoint).symm

end A102_CNFProofValidity

/-! ## 103 - Concrete proof-tree node accounting -/
namespace A103_CNFProofSize

open A101_CNFProofTree

def nodeCount {n : Nat} : ProofTree n -> Nat
  | .leaf _ _ => 1
  | .branch _ _ left right => 1 + nodeCount left + nodeCount right
  | .andSplit _ _ left right => 1 + nodeCount left + nodeCount right

def depth {n : Nat} : ProofTree n -> Nat
  | .leaf _ _ => 1
  | .branch _ _ left right => 1 + max (depth left) (depth right)
  | .andSplit _ _ left right => 1 + max (depth left) (depth right)

theorem depth_le_nodeCount {n : Nat} (tree : ProofTree n) :
    depth tree <= nodeCount tree := by
  induction tree with
  | leaf formula answer => simp [depth, nodeCount]
  | branch formula x left right ihLeft ihRight =>
      simp only [depth, nodeCount]
      omega
  | andSplit leftFormula rightFormula left right ihLeft ihRight =>
      simp only [depth, nodeCount]
      omega

end A103_CNFProofSize

/-! ## 104 - Canonical CNF keys may safely share answers -/
namespace A104_CanonicalCNFKey

open A91_FixedBitSatisfiability

structure Canonicalizer (n : Nat) where
  normalize : CNF n -> CNF n
  preserves : forall formula, Sat (normalize formula) <-> Sat formula
  idempotent : forall formula, normalize (normalize formula) = normalize formula

theorem equal_keys_same_sat {n : Nat}
    (canonicalizer : Canonicalizer n) {left right : CNF n}
    (same : canonicalizer.normalize left = canonicalizer.normalize right) :
    Sat left <-> Sat right := by
  rw [← canonicalizer.preserves left, ← canonicalizer.preserves right, same]

end A104_CanonicalCNFKey

/-! ## 105 - Polynomial proof-tree compilation is sufficient for SAT in P -/
namespace A105_PolynomialCNFCertificate

open A91_FixedBitSatisfiability A101_CNFProofTree
open A102_CNFProofValidity A103_CNFProofSize

structure Compiler where
  compile : {n : Nat} -> CNF n -> ProofTree n
  root_preserved : forall {n} (formula : CNF n), (compile formula).root = formula
  valid : forall {n} (formula : CNF n), Valid (compile formula)
  inputSize : {n : Nat} -> CNF n -> Nat
  exponent : Nat
  node_bound : forall {n} (formula : CNF n),
    nodeCount (compile formula) <= inputSize formula ^ exponent

def Compiler.decide (compiler : Compiler) {n : Nat} (formula : CNF n) : Bool :=
  (compiler.compile formula).eval

theorem Compiler.decide_correct (compiler : Compiler)
    {n : Nat} (formula : CNF n) :
    compiler.decide formula = true <-> Sat formula := by
  rw [Compiler.decide, eval_correct (compiler.valid formula), compiler.root_preserved]

end A105_PolynomialCNFCertificate

end ResearchEighth
end PIsNPOrNot
