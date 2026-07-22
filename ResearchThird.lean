import ResearchNext
import CNFCore

/-!
# Approaches 33-47: certified decomposition and canonical residual search

These theorems do not assert P = NP.  They isolate a second possible route:
turn an input into a polynomial number of certified pieces, normalize equivalent
residuals, prune dominated pieces, and solve each surviving piece by a verified
specialized method.
-/

namespace PIsNPOrNot
namespace ResearchThird

/-! ## 33 - A covered certified portfolio is a total exact decider -/
namespace A33_CertifiedCoverage

variable {I : Type}

structure CertifiedPartial (Yes : I -> Prop) where
  run : I -> Option Bool
  sound : forall input result,
    run input = some result -> (result = true <-> Yes input)

def firstAnswer {Yes : I -> Prop}
    (solvers : List (CertifiedPartial Yes)) (input : I) : Option Bool :=
  solvers.findSome? (fun solver => solver.run input)

def Covers {Yes : I -> Prop}
    (solvers : List (CertifiedPartial Yes)) : Prop :=
  forall input, exists solver, solver ∈ solvers /\ exists result, solver.run input = some result

theorem firstAnswer_sound {Yes : I -> Prop}
    (solvers : List (CertifiedPartial Yes)) (input : I) (result : Bool)
    (h : firstAnswer solvers input = some result) :
    result = true <-> Yes input := by
  unfold firstAnswer at h
  rw [List.findSome?_eq_some_iff] at h
  rcases h with ⟨before, solver, after, hlist, hrun, _⟩
  have hs : solver ∈ solvers := by
    rw [hlist]
    simp
  exact solver.sound input result hrun

theorem firstAnswer_total {Yes : I -> Prop}
    (solvers : List (CertifiedPartial Yes)) (cover : Covers solvers)
    (input : I) : exists result, firstAnswer solvers input = some result := by
  rcases cover input with ⟨solver, hmem, result, hrun⟩
  cases hfirst : firstAnswer solvers input with
  | some answer => exact ⟨answer, rfl⟩
  | none =>
      have hall : forall candidate, candidate ∈ solvers ->
          candidate.run input = none := by
        unfold firstAnswer at hfirst
        exact List.findSome?_eq_none_iff.mp hfirst
      have hnone := hall solver hmem
      rw [hrun] at hnone
      simp at hnone

end A33_CertifiedCoverage

/-! ## 34 - Exact disjunctive decomposition turns one search into two -/
namespace A34_DisjunctiveDecomposition

variable {W : Type}

theorem exists_or_decompose (R left right : W -> Bool)
    (factor : forall w, R w = (left w || right w)) :
    (exists w, R w = true) <->
      (exists w, left w = true) \/ (exists w, right w = true) := by
  constructor
  · rintro ⟨w, hw⟩
    have hor : left w = true \/ right w = true := by
      have : left w || right w = true := by simpa [factor w] using hw
      simpa [Bool.or_eq_true] using this
    rcases hor with hl | hr
    · exact Or.inl ⟨w, hl⟩
    · exact Or.inr ⟨w, hr⟩
  · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
    · exact ⟨w, by simp [factor w, hw]⟩
    · exact ⟨w, by simp [factor w, hw]⟩

end A34_DisjunctiveDecomposition

/-! ## 35 - Independent conjunctive components can be solved separately -/
namespace A35_IndependentConjunction

variable {A B : Type}

theorem independent_product (left : A -> Bool) (right : B -> Bool) :
    (exists a b, left a && right b = true) <->
      (exists a, left a = true) /\ (exists b, right b = true) := by
  constructor
  · rintro ⟨a, b, h⟩
    have hparts : left a = true /\ right b = true := by
      simpa [Bool.and_eq_true] using h
    exact ⟨⟨a, hparts.1⟩, ⟨b, hparts.2⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, by simp [ha, hb]⟩

end A35_IndependentConjunction

/-! ## 36 - A dominated residual may be deleted -/
namespace A36_DominancePruning

variable {W : Type}

def Dominates (strong weak : W -> Prop) : Prop :=
  forall w, strong w -> weak w

theorem prune_dominated (strong weak : W -> Prop)
    (hdom : Dominates strong weak) :
    (exists w, strong w \/ weak w) <-> exists w, weak w := by
  constructor
  · rintro ⟨w, hs | hw⟩
    · exact ⟨w, hdom w hs⟩
    · exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Or.inr hw⟩

end A36_DominancePruning

/-! ## 37 - Semantic normalization preserves existential acceptance -/
namespace A37_SemanticNormalization

variable {I : Type}

theorem normalize_exists (R : I -> Bool) (normalize : I -> I)
    (preserves : forall input, R (normalize input) = R input) :
    (exists input, R (normalize input) = true) <->
      (exists input, R input = true) := by
  constructor
  · rintro ⟨input, h⟩
    exact ⟨input, by simpa [preserves input] using h⟩
  · rintro ⟨input, h⟩
    exact ⟨input, by simpa [preserves input] using h⟩

end A37_SemanticNormalization

/-! ## 38 - Equal canonical keys imply mergeable residuals -/
namespace A38_CanonicalMemoization

variable {I K : Type}

theorem equal_key_equal_answer (key : I -> K) (answer : I -> Bool)
    (factors : exists decode : K -> Bool, forall input, answer input = decode (key input))
    {a b : I} (hkey : key a = key b) : answer a = answer b := by
  rcases factors with ⟨decode, hdecode⟩
  calc
    answer a = decode (key a) := hdecode a
    _ = decode (key b) := by rw [hkey]
    _ = answer b := (hdecode b).symm

theorem idempotent_key_stable (normalize : I -> I)
    (hidempotent : forall input, normalize (normalize input) = normalize input)
    (input : I) : normalize (normalize input) = normalize input :=
  hidempotent input

end A38_CanonicalMemoization

/-! ## 39 - Backdoor enumeration is exact -/
namespace A39_BackdoorSearch

variable {B W : Type}

theorem backdoor_exact (R : W -> Bool) (residual : B -> W -> Bool)
    (cover : forall w, R w = true <-> exists b, residual b w = true) :
    (exists w, R w = true) <-> exists b w, residual b w = true := by
  constructor
  · rintro ⟨w, hw⟩
    rcases (cover w).mp hw with ⟨b, hb⟩
    exact ⟨b, w, hb⟩
  · rintro ⟨b, w, hb⟩
    exact ⟨w, (cover w).mpr ⟨b, hb⟩⟩

end A39_BackdoorSearch

/-! ## 40 - The exact numerical burden of a small backdoor -/
namespace A40_PolynomialBackdoorBudget

structure BackdoorBudget where
  inputSize : Nat
  backdoorBits : Nat
  exponent : Nat
  polynomialBound : 2 ^ backdoorBits <= inputSize ^ exponent

theorem assignments_fit_polynomial (B : BackdoorBudget) :
    2 ^ B.backdoorBits <= B.inputSize ^ B.exponent :=
  B.polynomialBound

theorem combine_branch_cost (B : BackdoorBudget) (costPerBranch : Nat)
    (hcost : costPerBranch <= B.inputSize ^ B.exponent) :
    2 ^ B.backdoorBits * costPerBranch <=
      (B.inputSize ^ B.exponent) * (B.inputSize ^ B.exponent) := by
  exact Nat.mul_le_mul B.polynomialBound hcost

end A40_PolynomialBackdoorBudget

/-! ## 41 - Adding an entailed learned constraint preserves solutions -/
namespace A41_EntailedLearning

variable {A : Type}

def Entails (formula learned : A -> Bool) : Prop :=
  forall assignment, formula assignment = true -> learned assignment = true

theorem add_entailed_preserves (formula learned : A -> Bool)
    (hentails : Entails formula learned) (assignment : A) :
    (formula assignment && learned assignment = true) <->
      formula assignment = true := by
  constructor
  · intro h
    have hp : formula assignment = true /\ learned assignment = true := by
      simpa [Bool.and_eq_true] using h
    exact hp.1
  · intro hf
    have hl := hentails assignment hf
    simp [hf, hl]

theorem add_entailed_preserves_sat (formula learned : A -> Bool)
    (hentails : Entails formula learned) :
    (exists assignment, formula assignment && learned assignment = true) <->
      exists assignment, formula assignment = true := by
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, (add_entailed_preserves formula learned hentails assignment).mp h⟩
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, (add_entailed_preserves formula learned hentails assignment).mpr h⟩

end A41_EntailedLearning

/-! ## 42 - One Boolean resolution step is sound -/
namespace A42_ResolutionStep

theorem resolution_sound (a b pivot : Bool)
    (h : (a || pivot) && (b || !pivot) = true) :
    a || b = true := by
  cases a <;> cases b <;> cases pivot <;> simp at h ⊢

end A42_ResolutionStep

/-! ## 43 - A pipeline of semantics-preserving preprocessors is semantics-preserving -/
namespace A43_PreprocessPipeline

variable {I : Type}

def applyPipeline : List (I -> I) -> I -> I
  | [], input => input
  | transform :: rest, input => applyPipeline rest (transform input)

theorem pipeline_preserves (Yes : I -> Prop) (steps : List (I -> I))
    (preserves : forall transform, transform ∈ steps ->
      forall input, Yes (transform input) <-> Yes input)
    (input : I) : Yes (applyPipeline steps input) <-> Yes input := by
  induction steps generalizing input with
  | nil => simp [applyPipeline]
  | cons head tail ih =>
      have hhead : forall x, Yes (head x) <-> Yes x := by
        intro x
        exact preserves head (by simp) x
      have htail : forall transform, transform ∈ tail ->
          forall x, Yes (transform x) <-> Yes x := by
        intro transform hmem x
        exact preserves transform (by simp [hmem]) x
      calc
        Yes (applyPipeline (head :: tail) input) <->
            Yes (applyPipeline tail (head input)) := by rfl
        _ <-> Yes (head input) := ih htail (head input)
        _ <-> Yes input := hhead input

end A43_PreprocessPipeline

/-! ## 44 - Forced simplification gives linear rather than binary-tree work -/
namespace A44_ForcedDescent

def forcedWork (perLevel : Nat) : Nat -> Nat
  | 0 => 1
  | depth + 1 => forcedWork perLevel depth + perLevel

theorem forcedWork_closed (perLevel depth : Nat) :
    forcedWork perLevel depth = 1 + depth * perLevel := by
  induction depth with
  | zero => simp [forcedWork]
  | succ depth ih =>
      simp [forcedWork, ih, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]

def fullBranchLeaves : Nat -> Nat
  | 0 => 1
  | depth + 1 => 2 * fullBranchLeaves depth

theorem fullBranchLeaves_closed (depth : Nat) :
    fullBranchLeaves depth = 2 ^ depth := by
  induction depth with
  | zero => simp [fullBranchLeaves]
  | succ depth ih =>
      simp [fullBranchLeaves, ih, pow_succ, Nat.mul_comm]

end A44_ForcedDescent

/-! ## 45 - Representative families preserve existence -/
namespace A45_RepresentativeFamilies

variable {W : Type}

theorem representative_cover (all representatives : Set W) (Good : W -> Prop)
    (representatives_subset : representatives ⊆ all)
    (covers_good : forall w, w ∈ all -> Good w ->
      exists r, r ∈ representatives /\ Good r) :
    (exists w, w ∈ all /\ Good w) <->
      exists r, r ∈ representatives /\ Good r := by
  constructor
  · rintro ⟨w, hw, hgood⟩
    exact covers_good w hw hgood
  · rintro ⟨r, hr, hgood⟩
    exact ⟨r, representatives_subset hr, hgood⟩

end A45_RepresentativeFamilies

/-! ## 46 - A decomposition tree is exactly the OR of its leaves -/
namespace A46_DecompositionTree

inductive SearchTree (I : Type) where
  | leaf (input : I)
  | split (left right : SearchTree I)

def SearchTree.solve {I : Type} (solver : I -> Bool) : SearchTree I -> Bool
  | .leaf input => solver input
  | .split left right => left.solve solver || right.solve solver

def SearchTree.leaves {I : Type} : SearchTree I -> List I
  | .leaf input => [input]
  | .split left right => left.leaves ++ right.leaves

theorem solve_true_iff_leaf {I : Type} (solver : I -> Bool)
    (tree : SearchTree I) :
    tree.solve solver = true <-> exists input, input ∈ tree.leaves /\ solver input = true := by
  induction tree with
  | leaf input => simp [SearchTree.solve, SearchTree.leaves]
  | split left right ihLeft ihRight =>
      constructor
      · intro h
        have hor : left.solve solver = true \/ right.solve solver = true := by
          simpa [SearchTree.solve, Bool.or_eq_true] using h
        rcases hor with hl | hr
        · rcases ihLeft.mp hl with ⟨input, hmem, hs⟩
          exact ⟨input, by simp [SearchTree.leaves, hmem], hs⟩
        · rcases ihRight.mp hr with ⟨input, hmem, hs⟩
          exact ⟨input, by simp [SearchTree.leaves, hmem], hs⟩
      · rintro ⟨input, hmem, hs⟩
        have hside : input ∈ left.leaves \/ input ∈ right.leaves := by
          simpa [SearchTree.leaves] using hmem
        rcases hside with hl | hr
        · have hleft : left.solve solver = true := ihLeft.mpr ⟨input, hl, hs⟩
          simp [SearchTree.solve, hleft]
        · have hright : right.solve solver = true := ihRight.mpr ⟨input, hr, hs⟩
          simp [SearchTree.solve, hright]

end A46_DecompositionTree

/-! ## 47 - Structural recognition and residual fallback can coexist exactly -/
namespace A47_UniversalHybrid

variable {I Structural Residual : Type}

def hybrid
    (recognize : I -> Option Structural)
    (fast : Structural -> Bool)
    (compileResidual : I -> Residual)
    (residualSolve : Residual -> Bool)
    (input : I) : Bool :=
  match recognize input with
  | some structured => fast structured
  | none => residualSolve (compileResidual input)

theorem hybrid_correct
    (Yes : I -> Prop) (YesStructural : Structural -> Prop)
    (YesResidual : Residual -> Prop)
    (recognize : I -> Option Structural)
    (fast : Structural -> Bool)
    (compileResidual : I -> Residual)
    (residualSolve : Residual -> Bool)
    (recognition_correct : forall input structured,
      recognize input = some structured ->
        (YesStructural structured <-> Yes input))
    (fast_correct : forall structured,
      fast structured = true <-> YesStructural structured)
    (compile_correct : forall input,
      YesResidual (compileResidual input) <-> Yes input)
    (residual_correct : forall residual,
      residualSolve residual = true <-> YesResidual residual)
    (input : I) :
    hybrid recognize fast compileResidual residualSolve input = true <-> Yes input := by
  cases hrec : recognize input with
  | none =>
      calc
        hybrid recognize fast compileResidual residualSolve input = true <->
            residualSolve (compileResidual input) = true := by simp [hybrid, hrec]
        _ <-> YesResidual (compileResidual input) := residual_correct _
        _ <-> Yes input := compile_correct input
  | some structured =>
      calc
        hybrid recognize fast compileResidual residualSolve input = true <->
            fast structured = true := by simp [hybrid, hrec]
        _ <-> YesStructural structured := fast_correct structured
        _ <-> Yes input := recognition_correct input structured hrec

end A47_UniversalHybrid

/-!
## Synthesis target

A route to P = NP would follow if every NP verifier could be transformed in
polynomial time into a polynomial-size decomposition tree whose leaves are all
covered by certified polynomial-time structural solvers or by polynomial-state
canonical residual models.  The theorems above verify the logical composition;
the missing theorem is the uniform polynomial bound and construction.
-/

end ResearchThird
end PIsNPOrNot
