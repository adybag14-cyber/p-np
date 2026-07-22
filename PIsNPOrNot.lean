import Mathlib

/-!
# Fifteen mechanically checked attacks on P versus NP

This project does not assume `P = NP` or `P ≠ NP`.  Each namespace isolates a
real algorithmic route, proves its finite/logical core, and leaves the genuine
complexity bottleneck visible.
-/

namespace PIsNPOrNot

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Verifier (n m : ℕ) := Bits n → Bits m → Bool

def Accepts {n m : ℕ} (V : Verifier n m) (x : Bits n) : Prop :=
  ∃ w, V x w = true

def bruteAcceptSpec {n m : ℕ} (V : Verifier n m) (x : Bits n) : Prop :=
  Accepts V x

theorem bruteAcceptSpec_correct {n m : ℕ} (V : Verifier n m) (x : Bits n) :
    bruteAcceptSpec V x ↔ Accepts V x := by
  rfl
/-! ## 01 — Exhaustive witness search -/
namespace A01_Exhaustive

theorem witness_space_size (m : ℕ) :
    Fintype.card (Bits m) = 2 ^ m := by
  simp [Bits]

end A01_Exhaustive

/-! ## 02 — Prefix self-reduction -/
namespace A02_SelfReduction

def descend (Good : List Bool → Prop) [DecidablePred Good] :
    ℕ → List Bool → List Bool
  | 0, p => p
  | n + 1, p =>
      if Good (p ++ [false]) then
        descend Good n (p ++ [false])
      else
        descend Good n (p ++ [true])

theorem descend_preserves_good
    (Good : List Bool → Prop) [DecidablePred Good]
    (split : ∀ p, Good p → Good (p ++ [false]) ∨ Good (p ++ [true]))
    (n : ℕ) (p : List Bool) (hp : Good p) :
    Good (descend Good n p) := by
  induction n generalizing p with
  | zero => simpa [descend]
  | succ n ih =>
      by_cases h0 : Good (p ++ [false])
      · simp [descend, h0]
        exact ih (p ++ [false]) h0
      · have h1 : Good (p ++ [true]) := (split p hp).resolve_left h0
        simp [descend, h0]
        exact ih (p ++ [true]) h1

end A02_SelfReduction

/-! ## 03 — Random sampling and witness density -/
namespace A03_RandomSampling

variable {W : Type} [Fintype W]

theorem sample_space_count (t : ℕ) :
    Fintype.card (Fin t → W) = (Fintype.card W) ^ t := by
  simp

theorem all_bad_sample_count (R : W → Prop) [DecidablePred R] (t : ℕ) :
    Fintype.card (Fin t → {w : W // ¬ R w}) =
      (Fintype.card {w : W // ¬ R w}) ^ t := by
  simp

theorem witness_exists_of_positive_count
    (R : W → Prop) [DecidablePred R]
    (h : 0 < ((Finset.univ : Finset W).filter R).card) :
    ∃ w, R w := by
  have hn : ((Finset.univ : Finset W).filter R).Nonempty := Finset.card_pos.mp h
  rcases hn with ⟨w, hw⟩
  exact ⟨w, (Finset.mem_filter.mp hw).2⟩

end A03_RandomSampling

/-! ## 04 — Isolation by hashing -/
namespace A04_Isolation

variable {W B : Type}

def IsolatedBy (hash : W → B) (R : W → Prop) (bucket : B) : Prop :=
  ∃! w, R w ∧ hash w = bucket

theorem injective_on_witnesses_isolates
    (hash : W → B) (R : W → Prop)
    (hinj : ∀ a b, R a → R b → hash a = hash b → a = b)
    (w : W) (hw : R w) :
    IsolatedBy hash R (hash w) := by
  refine ⟨w, ⟨hw, rfl⟩, ?_⟩
  intro y hy
  exact hinj y w hy.1 hw hy.2

theorem isolated_bucket_yields_witness
    (hash : W → B) (R : W → Prop) (bucket : B)
    (h : IsolatedBy hash R bucket) :
    ∃ w, R w := by
  rcases h with ⟨w, hw, _⟩
  exact ⟨w, hw.1⟩

end A04_Isolation

/-! ## 05 — Meet in the middle for separable verifiers -/
namespace A05_MeetInMiddle

variable {A B : Type}

theorem separable_search (L : A → Prop) (R : B → Prop) :
    (∃ p : A × B, L p.1 ∧ R p.2) ↔
      (∃ a, L a) ∧ (∃ b, R b) := by
  constructor
  · rintro ⟨⟨a, b⟩, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), ha, hb⟩

end A05_MeetInMiddle

/-! ## 06 — Dynamic programming through a small separator -/
namespace A06_SeparatorDP

variable {A B S T : Type}

theorem separator_factorization
    (leftSig : A → S) (rightSig : B → T)
    (compatible : S → T → Prop) (R : A → B → Prop)
    (factor : ∀ a b, R a b ↔ compatible (leftSig a) (rightSig b)) :
    (∃ a b, R a b) ↔
      ∃ s ∈ Set.range leftSig, ∃ t ∈ Set.range rightSig, compatible s t := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨leftSig a, ⟨a, rfl⟩, rightSig b, ⟨b, rfl⟩,
      (factor a b).mp hab⟩
  · rintro ⟨s, ⟨a, rfl⟩, t, ⟨b, rfl⟩, hst⟩
    exact ⟨a, b, (factor a b).mpr hst⟩

end A06_SeparatorDP

/-! ## 07 — Symmetry quotienting -/
namespace A07_Symmetry

variable {W : Type}

theorem representative_search
    (rep : W → W) (R : W → Prop)
    (invariant : ∀ w, R (rep w) ↔ R w) :
    (∃ w, R w) ↔ ∃ r ∈ Set.range rep, R r := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨rep w, ⟨w, rfl⟩, (invariant w).mpr hw⟩
  · rintro ⟨r, ⟨w, rfl⟩, hr⟩
    exact ⟨w, (invariant w).mp hr⟩

end A07_Symmetry

/-! ## 08 — Behavioural trace quotienting -/
namespace A08_TraceQuotient

variable {W T : Type}

theorem factor_through_trace
    (trace : W → T) (acceptTrace : T → Prop) (R : W → Prop)
    (factor : ∀ w, R w ↔ acceptTrace (trace w)) :
    (∃ w, R w) ↔ ∃ t ∈ Set.range trace, acceptTrace t := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨trace w, ⟨w, rfl⟩, (factor w).mp hw⟩
  · rintro ⟨t, ⟨w, rfl⟩, ht⟩
    exact ⟨w, (factor w).mpr ht⟩

end A08_TraceQuotient

/-! ## 09 — Memoization and state merging -/
namespace A09_StateMerging

variable {W S : Type} [Fintype W] [Fintype S] [DecidableEq S]

theorem distinct_trace_bound (trace : W → S) :
    ((Finset.univ : Finset W).image trace).card ≤ Fintype.card S := by
  simpa using
    (Finset.card_le_card (Finset.subset_univ ((Finset.univ : Finset W).image trace)))

end A09_StateMerging

/-! ## 10 — Arithmetizing the giant OR -/
namespace A10_Arithmetization

def complementNat : Bool → ℕ
  | false => 1
  | true => 0

def noHitProduct (xs : List Bool) : ℕ :=
  (xs.map complementNat).prod

theorem noHitProduct_eq_zero_iff_any (xs : List Bool) :
    noHitProduct xs = 0 ↔ xs.any id = true := by
  induction xs with
  | nil => simp [noHitProduct]
  | cons b bs =>
      cases b <;> simp [noHitProduct, complementNat, *]

end A10_Arithmetization

/-! ## 11 — Monotonicity: SAT collapses to the all-true assignment -/
namespace A11_Monotone

def LeBits {m : ℕ} (x y : Bits m) : Prop :=
  ∀ i, x i = true → y i = true

def Monotone {m : ℕ} (f : Bits m → Bool) : Prop :=
  ∀ x y, LeBits x y → f x = true → f y = true

def topBits (m : ℕ) : Bits m := fun _ => true

theorem monotone_sat_at_top {m : ℕ} (f : Bits m → Bool)
    (hf : Monotone f) :
    (∃ x, f x = true) ↔ f (topBits m) = true := by
  constructor
  · rintro ⟨x, hx⟩
    apply hf x (topBits m)
    · intro i hi
      rfl
    · exact hx
  · intro h
    exact ⟨topBits m, h⟩

end A11_Monotone

/-! ## 12 — Low Boolean-rank feature aggregation -/
namespace A12_LowRank

variable {W : Type} [Fintype W]

def dotOrAnd {k : ℕ} (a b : Fin k → Bool) : Bool :=
  decide (∃ i, a i = true ∧ b i = true)

def aggregateFeatures {k : ℕ} (B : W → Fin k → Bool) : Fin k → Bool :=
  fun i => decide (∃ w, B w i = true)

theorem aggregate_features_correct {k : ℕ}
    (a : Fin k → Bool) (B : W → Fin k → Bool) :
    (∃ w, dotOrAnd a (B w) = true) ↔
      dotOrAnd a (aggregateFeatures B) = true := by
  simp [dotOrAnd, aggregateFeatures]
  aesop

end A12_LowRank

/-! ## 13 — Kernelization -/
namespace A13_Kernelization

variable {I K : Type}

def kernelDecide (kernel : I → K) (yesK : K → Prop)
    [DecidablePred yesK] (x : I) : Bool :=
  decide (yesK (kernel x))

theorem kernelDecide_correct
    (kernel : I → K) (yesI : I → Prop) (yesK : K → Prop)
    [DecidablePred yesK]
    (preserves : ∀ x, yesI x ↔ yesK (kernel x)) (x : I) :
    kernelDecide kernel yesK x = true ↔ yesI x := by
  simp [kernelDecide, ← preserves x]

end A13_Kernelization

/-! ## 14 — Polynomial candidate generators / bounded proof search -/
namespace A14_CandidateGenerator

variable {W : Type}

def generatedAccept {k : ℕ} (gen : Fin k → W) (R : W → Prop)
    [DecidablePred R] : Bool :=
  decide (∃ i, R (gen i))

theorem generatedAccept_correct {k : ℕ}
    (gen : Fin k → W) (R : W → Prop) [DecidablePred R]
    (coverage : (∃ w, R w) → ∃ i, R (gen i)) :
    generatedAccept gen R = true ↔ ∃ w, R w := by
  constructor
  · intro h
    simp [generatedAccept] at h
    rcases h with ⟨i, hi⟩
    exact ⟨gen i, hi⟩
  · intro h
    simp [generatedAccept]
    exact coverage h

end A14_CandidateGenerator

/-! ## 15 — Residual-state automata / adaptive OBDD frontier -/
namespace A15_ResidualAutomaton

variable {S : Type} [DecidableEq S]

def runR (step : S → Bool → S) : S → List Bool → S
  | q, [] => q
  | q, b :: bs => step (runR step q bs) b

def nextStates (step : S → Bool → S) (Q : Finset S) : Finset S :=
  Q.image (fun q => step q false) ∪ Q.image (fun q => step q true)

def reachable (step : S → Bool → S) (start : S) : ℕ → Finset S
  | 0 => {start}
  | n + 1 => nextStates step (reachable step start n)

theorem mem_reachable_iff
    (step : S → Bool → S) (start q : S) (n : ℕ) :
    q ∈ reachable step start n ↔
      ∃ w : List Bool, w.length = n ∧ runR step start w = q := by
  induction n generalizing q with
  | zero => simp [reachable, runR, eq_comm]
  | succ n ih =>
      constructor
      · intro h
        rw [reachable, nextStates] at h
        rcases Finset.mem_union.mp h with h0 | h1
        · rcases Finset.mem_image.mp h0 with ⟨r, hr, hrq⟩
          rcases (ih r).mp hr with ⟨w, hwlen, hwr⟩
          refine ⟨false :: w, by simp [hwlen], ?_⟩
          simpa [runR, hwr] using hrq
        · rcases Finset.mem_image.mp h1 with ⟨r, hr, hrq⟩
          rcases (ih r).mp hr with ⟨w, hwlen, hwr⟩
          refine ⟨true :: w, by simp [hwlen], ?_⟩
          simpa [runR, hwr] using hrq
      · rintro ⟨w, hwlen, hwr⟩
        cases w with
        | nil => simp at hwlen
        | cons b bs =>
            have hlen : bs.length = n := by simpa using hwlen
            have hrs : runR step start bs ∈ reachable step start n :=
              (ih (runR step start bs)).mpr ⟨bs, hlen, rfl⟩
            rw [reachable, nextStates]
            cases b with
            | false =>
                apply Finset.mem_union_left
                apply Finset.mem_image.mpr
                refine ⟨runR step start bs, hrs, ?_⟩
                simpa [runR] using hwr
            | true =>
                apply Finset.mem_union_right
                apply Finset.mem_image.mpr
                refine ⟨runR step start bs, hrs, ?_⟩
                simpa [runR] using hwr

noncomputable def dpAccept (step : S → Bool → S) (start : S)
    (accept : S → Bool) (n : ℕ) : Bool :=
  if ∃ q ∈ reachable step start n, accept q = true then true else false

theorem dpAccept_correct
    (step : S → Bool → S) (start : S)
    (accept : S → Bool) (n : ℕ) :
    dpAccept step start accept n = true ↔
      ∃ w : List Bool,
        w.length = n ∧ accept (runR step start w) = true := by
  classical
  constructor
  · intro h
    have hex : ∃ q ∈ reachable step start n, accept q = true := by
      simpa [dpAccept] using h
    rcases hex with ⟨q, hq, ha⟩
    rcases (mem_reachable_iff step start q n).mp hq with ⟨w, hwlen, hrun⟩
    exact ⟨w, hwlen, by simpa [hrun] using ha⟩
  · rintro ⟨w, hwlen, ha⟩
    have hq : runR step start w ∈ reachable step start n :=
      (mem_reachable_iff step start (runR step start w) n).mpr
        ⟨w, hwlen, rfl⟩
    have hex : ∃ q ∈ reachable step start n, accept q = true :=
      ⟨runR step start w, hq, ha⟩
    simpa [dpAccept] using hex
theorem reachable_state_bound [Fintype S]
    (step : S → Bool → S) (start : S) (n : ℕ) :
    (reachable step start n).card ≤ Fintype.card S := by
  simpa using Finset.card_le_card (Finset.subset_univ (reachable step start n))

end A15_ResidualAutomaton

/-! ## Synthesis — the residual-compression research target

A uniform polynomial-time construction of these models, with polynomial
`stateBudget`, would turn the residual-state idea into a route to `P = NP`.
The theorem below verifies the exact finite decision core without assuming that
such compact models always exist.
-/
namespace Synthesis_ResidualCompression

open A15_ResidualAutomaton

structure ResidualModel (R : List Bool → Bool) (m : ℕ) where
  State : Type
  decEqState : DecidableEq State
  finiteState : Fintype State
  step : State → Bool → State
  start : State
  accept : State → Bool
  stateBudget : ℕ
  card_le_budget : Fintype.card State ≤ stateBudget
  correct : ∀ w, w.length = m →
    R w = accept (runR step start w)

noncomputable def ResidualModel.decide
    {R : List Bool → Bool} {m : ℕ} (M : ResidualModel R m) : Bool :=
  letI : DecidableEq M.State := M.decEqState
  dpAccept M.step M.start M.accept m

theorem ResidualModel.decide_correct
    {R : List Bool → Bool} {m : ℕ} (M : ResidualModel R m) :
    M.decide = true ↔
      ∃ w : List Bool, w.length = m ∧ R w = true := by
  letI : DecidableEq M.State := M.decEqState
  rw [ResidualModel.decide, dpAccept_correct]
  constructor
  · rintro ⟨w, hwlen, ha⟩
    refine ⟨w, hwlen, ?_⟩
    calc
      R w = M.accept (runR M.step M.start w) := M.correct w hwlen
      _ = true := ha
  · rintro ⟨w, hwlen, hr⟩
    refine ⟨w, hwlen, ?_⟩
    calc
      M.accept (runR M.step M.start w) = R w := (M.correct w hwlen).symm
      _ = true := hr

theorem ResidualModel.reachable_le_budget
    {R : List Bool → Bool} {m : ℕ} (M : ResidualModel R m) :
    letI : DecidableEq M.State := M.decEqState
    (reachable M.step M.start m).card ≤ M.stateBudget := by
  letI : DecidableEq M.State := M.decEqState
  letI : Fintype M.State := M.finiteState
  exact (reachable_state_bound M.step M.start m).trans M.card_le_budget

end Synthesis_ResidualCompression
end PIsNPOrNot
