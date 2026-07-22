import PIsNPOrNot

/-!
# A small verified CNF restriction core

The Python experiments use the same operation at scale: assign one variable,
drop satisfied clauses, and delete falsified occurrences.  This file proves that
operation preserves Boolean evaluation for assignments agreeing with the chosen
bit.
-/

namespace PIsNPOrNot
namespace CNFCore

structure Lit (n : Nat) where
  var : Fin n
  positive : Bool
deriving DecidableEq, Repr

abbrev Clause (n : Nat) := List (Lit n)
abbrev CNF (n : Nat) := List (Clause n)

def evalLit {n : Nat} (assignment : Bits n) (lit : Lit n) : Bool :=
  if lit.positive then assignment lit.var else !(assignment lit.var)

def evalAtBit {n : Nat} (value : Bool) (lit : Lit n) : Bool :=
  if lit.positive then value else !value

def evalClause {n : Nat} (assignment : Bits n) (clause : Clause n) : Bool :=
  clause.any (evalLit assignment)

def evalCNF {n : Nat} (assignment : Bits n) (formula : CNF n) : Bool :=
  formula.all (evalClause assignment)

inductive ClauseResidual (n : Nat) where
  | satisfied
  | reduced (clause : Clause n)
deriving Repr

def restrictClause {n : Nat} (x : Fin n) (value : Bool) :
    Clause n -> ClauseResidual n
  | [] => .reduced []
  | lit :: rest =>
      if hvar : lit.var = x then
        if evalAtBit value lit then
          .satisfied
        else
          restrictClause x value rest
      else
        match restrictClause x value rest with
        | .satisfied => .satisfied
        | .reduced reduced => .reduced (lit :: reduced)

def restrictCNF {n : Nat} (x : Fin n) (value : Bool) : CNF n -> CNF n
  | [] => []
  | clause :: rest =>
      match restrictClause x value clause with
      | .satisfied => restrictCNF x value rest
      | .reduced reduced => reduced :: restrictCNF x value rest

theorem evalLit_eq_evalAtBit_of_var_eq {n : Nat}
    (assignment : Bits n) (x : Fin n) (value : Bool) (lit : Lit n)
    (hassignment : assignment x = value) (hvar : lit.var = x) :
    evalLit assignment lit = evalAtBit value lit := by
  simp [evalLit, evalAtBit, hvar, hassignment]

theorem evalClause_restrict {n : Nat}
    (assignment : Bits n) (x : Fin n) (value : Bool)
    (hassignment : assignment x = value) (clause : Clause n) :
    evalClause assignment clause =
      match restrictClause x value clause with
      | .satisfied => true
      | .reduced reduced => evalClause assignment reduced := by
  induction clause with
  | nil =>
      simp [evalClause, restrictClause]
  | cons lit rest ih =>
      by_cases hvar : lit.var = x
      · have hlit := evalLit_eq_evalAtBit_of_var_eq assignment x value lit
          hassignment hvar
        cases hbit : evalAtBit value lit with
        | false =>
            have hlitFalse : evalLit assignment lit = false := hlit.trans hbit
            simp [evalClause, restrictClause, hvar, hbit, hlitFalse]
            simpa [evalClause] using ih
        | true =>
            have hlitTrue : evalLit assignment lit = true := hlit.trans hbit
            simp [evalClause, restrictClause, hvar, hbit, hlitTrue]
      · cases hrest : restrictClause x value rest with
        | satisfied =>
            have ihTrue : evalClause assignment rest = true := by
              simpa [hrest] using ih
            have ihAnyTrue : rest.any (evalLit assignment) = true := by
              simpa [evalClause] using ihTrue
            rw [show restrictClause x value (lit :: rest) = .satisfied by
              simp [restrictClause, hvar, hrest]]
            change (evalLit assignment lit || rest.any (evalLit assignment)) = true
            rw [ihAnyTrue]
            simp
        | reduced reduced =>
            have ihReduced :
                evalClause assignment rest = evalClause assignment reduced := by
              simpa [hrest] using ih
            have ihAny :
                rest.any (evalLit assignment) =
                  reduced.any (evalLit assignment) := by
              simpa [evalClause] using ihReduced
            rw [show restrictClause x value (lit :: rest) = .reduced (lit :: reduced) by
              simp [restrictClause, hvar, hrest]]
            change (evalLit assignment lit || rest.any (evalLit assignment)) =
              (evalLit assignment lit || reduced.any (evalLit assignment))
            rw [ihAny]

theorem evalCNF_restrict {n : Nat}
    (assignment : Bits n) (x : Fin n) (value : Bool)
    (hassignment : assignment x = value) (formula : CNF n) :
    evalCNF assignment formula = evalCNF assignment (restrictCNF x value formula) := by
  induction formula with
  | nil => simp [evalCNF, restrictCNF]
  | cons clause rest ih =>
      have ihAll :
          rest.all (evalClause assignment) =
            (restrictCNF x value rest).all (evalClause assignment) := by
        simpa [evalCNF] using ih
      cases hclause : restrictClause x value clause with
      | satisfied =>
          have hcTrue : evalClause assignment clause = true := by
            have hc := evalClause_restrict assignment x value hassignment clause
            simpa [hclause] using hc
          simp [evalCNF, restrictCNF, hclause, hcTrue, ihAll]
      | reduced reduced =>
          have hcReduced :
              evalClause assignment clause = evalClause assignment reduced := by
            have hc := evalClause_restrict assignment x value hassignment clause
            simpa [hclause] using hc
          simp [evalCNF, restrictCNF, hclause, hcReduced, ihAll]

theorem branch_preserves_satisfying_assignments {n : Nat}
    (formula : CNF n) (x : Fin n) (value : Bool) :
    (Exists fun assignment : Bits n =>
      assignment x = value /\ evalCNF assignment formula = true) <->
    (Exists fun assignment : Bits n =>
      assignment x = value /\
        evalCNF assignment (restrictCNF x value formula) = true) := by
  constructor
  · rintro ⟨assignment, hx, hsatisfies⟩
    refine ⟨assignment, hx, ?_⟩
    rw [← evalCNF_restrict assignment x value hx formula]
    exact hsatisfies
  · rintro ⟨assignment, hx, hsatisfies⟩
    refine ⟨assignment, hx, ?_⟩
    rw [evalCNF_restrict assignment x value hx formula]
    exact hsatisfies

end CNFCore
end PIsNPOrNot
