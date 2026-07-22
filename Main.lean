import PIsNPOrNot

open PIsNPOrNot
open PIsNPOrNot.A15_ResidualAutomaton

def parityStep (q b : Bool) : Bool := Bool.xor q b

def cappedCountStep (cap : Nat) (q : Nat) (b : Bool) : Nat :=
  if b then min cap (q + 1) else q

def identityStep (q : List Bool) (b : Bool) : List Bool :=
  b :: q

def pow2 (n : Nat) : Nat := 2 ^ n

def reportResidualWidths : IO Unit := do
  IO.println "Residual-state experiment"
  IO.println "n | witnesses | parity states | capped-count states | identity states"
  IO.println "--+-----------+---------------+---------------------+----------------"
  for n in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] do
    let parityStates := (reachable parityStep false n).card
    let countStates := (reachable (cappedCountStep 8) 0 n).card
    let identityStates := (reachable identityStep [] n).card
    IO.println s!"{n} | {pow2 n} | {parityStates} | {countStates} | {identityStates}"

def reportWitnessExplosion : IO Unit := do
  IO.println ""
  IO.println "Witness-space growth"
  for m in [8, 16, 24, 32, 40, 48, 56, 64] do
    IO.println s!"m={m}: 2^m = {pow2 m} candidate witnesses"

def main : IO Unit := do
  IO.println "P versus NP: fifteen checked attacks, finite experiments"
  IO.println "Lean proves the reductions and barriers; it does not assume a collapse."
  IO.println ""
  reportResidualWidths
  reportWitnessExplosion
