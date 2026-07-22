import PIsNPOrNot

/-!
# Second research pass

This file sharpens the first fifteen approaches.  In particular, it separates
mere existence of a small quotient from a compositional residual machine that
can actually be constructed without already deciding the verifier.
-/

namespace PIsNPOrNot
namespace ResearchNext

/-! ## 16 - The acceptance-bit quotient is always tiny, hence vacuous -/
namespace A16_TrivialAcceptanceQuotient

variable {W : Type}

def trace (R : W -> Bool) : W -> Bool := R

def decode : Bool -> Bool := id

theorem factors (R : W -> Bool) (w : W) :
    decode (trace R w) = R w := by
  rfl

theorem existential_factors (R : W -> Bool) :
    (Exists fun w => R w = true) <->
      (Exists fun b : Bool => (Exists fun w => trace R w = b) /\ decode b = true) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨true, ⟨w, hw⟩, rfl⟩
  · rintro ⟨b, ⟨w, hw⟩, hb⟩
    have hwb : R w = b := by simpa [trace] using hw
    have hbt : b = true := by simpa [decode] using hb
    exact ⟨w, hwb.trans hbt⟩

end A16_TrivialAcceptanceQuotient

/-! ## 17 - Exact one-way compression of equality needs one state per row -/
namespace A17_EqualityRowLowerBound

variable {W S : Type} [Fintype W] [Fintype S] [DecidableEq W]

def eqRel (a b : W) : Bool := decide (a = b)

theorem encoding_injective
    (encode : W -> S) (decode : S -> W -> Bool)
    (correct : forall a b, decode (encode a) b = eqRel a b) :
    Function.Injective encode := by
  intro a b hab
  by_contra hne
  have hba : b ≠ a := Ne.symm hne
  have hs : eqRel a a = eqRel b a := by
    calc
      eqRel a a = decode (encode a) a := (correct a a).symm
      _ = decode (encode b) a := by rw [hab]
      _ = eqRel b a := correct b a
  simpa [eqRel, hne, hba] using hs

theorem state_lower_bound
    (encode : W -> S) (decode : S -> W -> Bool)
    (correct : forall a b, decode (encode a) b = eqRel a b) :
    Fintype.card W <= Fintype.card S := by
  exact Fintype.card_le_of_injective encode
    (encoding_injective encode decode correct)

theorem bit_state_lower_bound (k : Nat)
    (encode : Bits k -> S) (decode : S -> Bits k -> Bool)
    (correct : forall a b, decode (encode a) b = eqRel a b) :
    2 ^ k <= Fintype.card S := by
  calc
    2 ^ k = Fintype.card (Bits k) := by simp [Bits]
    _ <= Fintype.card S := state_lower_bound encode decode correct

end A17_EqualityRowLowerBound

/-! ## 18 - Pairwise distinguishable residuals force distinct states -/
namespace A18_DistinguishableResiduals

variable {I S : Type} [Fintype I] [Fintype S]

def PairwiseSeparated
    (R : List Bool -> Bool) (pref : I -> List Bool) : Prop :=
  forall i j, i ≠ j ->
    Exists fun suffix => R (pref i ++ suffix) ≠ R (pref j ++ suffix)

theorem state_injective
    (R : List Bool -> Bool) (pref : I -> List Bool)
    (state : I -> S) (decode : S -> List Bool -> Bool)
    (correct : forall i suffix,
      decode (state i) suffix = R (pref i ++ suffix))
    (separated : PairwiseSeparated R pref) :
    Function.Injective state := by
  intro i j hij
  by_contra hne
  rcases separated i j hne with ⟨suffix, hsuffix⟩
  apply hsuffix
  calc
    R (pref i ++ suffix) = decode (state i) suffix :=
      (correct i suffix).symm
    _ = decode (state j) suffix := by rw [hij]
    _ = R (pref j ++ suffix) := correct j suffix

theorem state_card_lower_bound
    (R : List Bool -> Bool) (pref : I -> List Bool)
    (state : I -> S) (decode : S -> List Bool -> Bool)
    (correct : forall i suffix,
      decode (state i) suffix = R (pref i ++ suffix))
    (separated : PairwiseSeparated R pref) :
    Fintype.card I <= Fintype.card S := by
  exact Fintype.card_le_of_injective state
    (state_injective R pref state decode correct separated)

end A18_DistinguishableResiduals

/-! ## 19 - A universal black-box hitting set must contain every witness -/
namespace A19_HittingSetBarrier

variable {W : Type} [Fintype W] [DecidableEq W]

def HitsEverySingleton (H : Finset W) : Prop :=
  forall w : W, w ∈ H

theorem hitting_set_eq_univ (H : Finset W)
    (hits : HitsEverySingleton H) :
    H = Finset.univ := by
  exact Finset.eq_univ_iff_forall.mpr hits

theorem hitting_set_card (H : Finset W)
    (hits : HitsEverySingleton H) :
    H.card = Fintype.card W := by
  rw [hitting_set_eq_univ H hits, Finset.card_univ]

theorem bit_hitting_set_card (m : Nat) (H : Finset (Bits m))
    (hits : HitsEverySingleton H) :
    H.card = 2 ^ m := by
  rw [hitting_set_card H hits]
  simp [Bits]

end A19_HittingSetBarrier

/-! ## 20 - A trace that retains the witness cannot compress it -/
namespace A20_TraceRecoveryBarrier

variable {W T : Type} [Fintype W] [Fintype T]

theorem trace_injective_of_recoverable
    (trace : W -> T) (recover : T -> W)
    (leftInverse : forall w, recover (trace w) = w) :
    Function.Injective trace := by
  intro a b hab
  calc
    a = recover (trace a) := (leftInverse a).symm
    _ = recover (trace b) := by rw [hab]
    _ = b := leftInverse b

theorem trace_card_lower_bound
    (trace : W -> T) (recover : T -> W)
    (leftInverse : forall w, recover (trace w) = w) :
    Fintype.card W <= Fintype.card T := by
  exact Fintype.card_le_of_injective trace
    (trace_injective_of_recoverable trace recover leftInverse)

end A20_TraceRecoveryBarrier

/-! ## 21 - Independent blocks really do decompose -/
namespace A21_IndependentBlocks

variable {k : Nat} {W : Fin k -> Type}

theorem independent_block_search
    (R : forall i, W i -> Prop) :
    (Exists fun witness : forall i, W i => forall i, R i (witness i)) <->
      (forall i, Exists fun wi => R i wi) := by
  constructor
  · rintro ⟨witness, hwitness⟩ i
    exact ⟨witness i, hwitness i⟩
  · intro h
    classical
    choose witness hwitness using h
    exact ⟨witness, hwitness⟩

end A21_IndependentBlocks

/-! ## 22 - Counting all Boolean truth tables quantifies nonuniform advice -/
namespace A22_TruthTableAdvice

theorem boolean_function_count (n : Nat) :
    Fintype.card (Bits n -> Bool) = 2 ^ (2 ^ n) := by
  simp [Bits]

variable {I A : Type} [Fintype I] [Fintype A]

theorem advice_lower_bound
    (encode : I -> A) (injective : Function.Injective encode) :
    Fintype.card I <= Fintype.card A := by
  exact Fintype.card_le_of_injective encode injective

end A22_TruthTableAdvice

/-! ## 23 - Any omitted black-box query can hide the sole witness -/
namespace A23_BlackBoxSpike

variable {W : Type} [Fintype W] [DecidableEq W]

def allFalse : W -> Bool := fun _ => false

def spike (hidden : W) : W -> Bool := fun w => decide (w = hidden)

theorem agree_on_queries
    (Q : Finset W) (hidden : W) (hhidden : hidden ∉ Q) :
    forall q, q ∈ Q -> allFalse q = spike hidden q := by
  intro q hq
  have hne : q ≠ hidden := by
    intro h
    apply hhidden
    simpa [h] using hq
  simp [allFalse, spike, hne]

theorem existential_answers_differ (hidden : W) :
    (¬ Exists fun w : W => allFalse w = true) /\
      (Exists fun w : W => spike hidden w = true) := by
  constructor
  · simp [allFalse]
  · exact ⟨hidden, by simp [spike]⟩

end A23_BlackBoxSpike

/-! ## 24 - Explicit work accounting for bounded residual propagation -/
namespace A24_ResidualWork

def work (levels states : Nat) : Nat :=
  2 * levels * states

theorem work_zero (states : Nat) : work 0 states = 0 := by
  simp [work]

theorem work_succ (levels states : Nat) :
    work (levels + 1) states = work levels states + 2 * states := by
  simp [work, Nat.add_mul, Nat.mul_add]

theorem work_mono_states {levels a b : Nat} (h : a <= b) :
    work levels a <= work levels b := by
  exact Nat.mul_le_mul_left (2 * levels) h

end A24_ResidualWork

/-! ## 25 - Refined target: local compositionality, not arbitrary factorization -/
namespace A25_CompositionalTarget

open A15_ResidualAutomaton

structure LocalResidualModel (R : List Bool -> Bool) (m : Nat) where
  State : Type
  decEqState : DecidableEq State
  finiteState : Fintype State
  start : State
  step : State -> Bool -> State
  accept : State -> Bool
  exact : forall w, w.length = m ->
    accept (runR step start w) = R w

noncomputable def LocalResidualModel.decide
    {R : List Bool -> Bool} {m : Nat} (M : LocalResidualModel R m) : Bool :=
  letI : DecidableEq M.State := M.decEqState
  dpAccept M.step M.start M.accept m

theorem LocalResidualModel.decide_correct
    {R : List Bool -> Bool} {m : Nat} (M : LocalResidualModel R m) :
    M.decide = true <->
      Exists fun w : List Bool => w.length = m /\ R w = true := by
  letI : DecidableEq M.State := M.decEqState
  rw [LocalResidualModel.decide, dpAccept_correct]
  constructor
  · rintro ⟨w, hwlen, ha⟩
    exact ⟨w, hwlen, by simpa [M.exact w hwlen] using ha⟩
  · rintro ⟨w, hwlen, hr⟩
    refine ⟨w, hwlen, ?_⟩
    simpa [M.exact w hwlen] using hr

end A25_CompositionalTarget

end ResearchNext
end PIsNPOrNot


namespace PIsNPOrNot
namespace ResearchNext

/-! ## 26 - Equality changes from exponential one-way rows to a two-state pair aggregate -/
namespace A26_OrderSensitivity

open A17_EqualityRowLowerBound

def pairedEq {k : Nat} (a b : Bits k) : Bool :=
  (List.finRange k).all (fun i => decide (a i = b i))

theorem pairedEq_true_iff {k : Nat} (a b : Bits k) :
    pairedEq a b = true <-> a = b := by
  simp [pairedEq, funext_iff]

theorem paired_aggregate_state_count : Fintype.card Bool = 2 := by
  decide

/-- The same equality relation has an exponential one-way row lower bound,
    while pairwise processing only needs a Boolean running aggregate. -/
theorem order_sensitive_summary {S : Type} [Fintype S]
    (k : Nat) (encode : Bits k -> S)
    (decode : S -> Bits k -> Bool)
    (correct : forall a b, decode (encode a) b = eqRel a b) :
    2 ^ k <= Fintype.card S := by
  exact bit_state_lower_bound k encode decode correct

end A26_OrderSensitivity

/-! ## 27 - Bounded frontier signatures bound exact residual width -/
namespace A27_FrontierSignatures

variable {P : Type} [Fintype P]

def signatureImage {f : Nat} (signature : P -> Bits f) : Finset (Bits f) :=
  (Finset.univ : Finset P).image signature

theorem signature_count_bound {f : Nat} (signature : P -> Bits f) :
    (signatureImage signature).card <= 2 ^ f := by
  calc
    (signatureImage signature).card <= Fintype.card (Bits f) := by
      simpa [signatureImage] using
        Finset.card_le_card (Finset.subset_univ (signatureImage signature))
    _ = 2 ^ f := by simp [Bits]

def ResidualFactorsThrough {f : Nat}
    (R : List Bool -> Bool) (pref : P -> List Bool)
    (signature : P -> Bits f) : Prop :=
  Exists fun decode : Bits f -> List Bool -> Bool =>
    forall p suffix, decode (signature p) suffix = R (pref p ++ suffix)

theorem equal_signature_equal_residual {f : Nat}
    (R : List Bool -> Bool) (pref : P -> List Bool)
    (signature : P -> Bits f)
    (factor : ResidualFactorsThrough R pref signature)
    {p q : P} (hsig : signature p = signature q) :
    forall suffix, R (pref p ++ suffix) = R (pref q ++ suffix) := by
  rcases factor with ⟨decode, hdecode⟩
  intro suffix
  calc
    R (pref p ++ suffix) = decode (signature p) suffix :=
      (hdecode p suffix).symm
    _ = decode (signature q) suffix := by rw [hsig]
    _ = R (pref q ++ suffix) := hdecode q suffix

end A27_FrontierSignatures

end ResearchNext
end PIsNPOrNot


namespace PIsNPOrNot
namespace ResearchNext

/-! ## 28 - Exact Shannon branching on one witness bit -/
namespace A28_ShannonBranching


def setBit {n : Nat} (a : Bits n) (x : Fin n) (b : Bool) : Bits n :=
  fun i => if i = x then b else a i

theorem setBit_current {n : Nat} (a : Bits n) (x : Fin n) :
    setBit a x (a x) = a := by
  funext i
  by_cases h : i = x
  · subst i
    simp [setBit]
  · simp [setBit, h]

theorem shannon_exists {n : Nat} (R : Bits n -> Bool) (x : Fin n) :
    (Exists fun a => R a = true) <->
      (Exists fun a => R (setBit a x false) = true) \/
      (Exists fun a => R (setBit a x true) = true) := by
  constructor
  · rintro ⟨a, ha⟩
    cases hx : a x with
    | false =>
        left
        refine ⟨a, ?_⟩
        have hset : setBit a x false = a := by
          simpa [hx] using setBit_current a x
        simpa [hset] using ha
    | true =>
        right
        refine ⟨a, ?_⟩
        have hset : setBit a x true = a := by
          simpa [hx] using setBit_current a x
        simpa [hset] using ha
  · rintro (h | h)
    · rcases h with ⟨a, ha⟩
      exact ⟨setBit a x false, ha⟩
    · rcases h with ⟨a, ha⟩
      exact ⟨setBit a x true, ha⟩

end A28_ShannonBranching

/-! ## 29 - A genuinely forced literal removes one branch exactly -/
namespace A29_ForcedLiteral

open A28_ShannonBranching

theorem restrict_to_forced_bit {n : Nat}
    (R : Bits n -> Bool) (x : Fin n) (b : Bool)
    (forced : forall a, R a = true -> a x = b) :
    (Exists fun a => R a = true) <->
      (Exists fun a => R (setBit a x b) = true) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hset : setBit a x b = a := by
      have hx := forced a ha
      simpa [hx] using setBit_current a x
    simpa [hset] using ha
  · rintro ⟨a, ha⟩
    exact ⟨setBit a x b, ha⟩

end A29_ForcedLiteral

/-! ## 30 - Exact variable/witness renaming preserves satisfiability -/
namespace A30_SymmetryIsomorphism

variable {A B : Type}

theorem exists_under_equiv (rename : A ≃ B) (R : B -> Bool) :
    (Exists fun a : A => R (rename a) = true) <->
      (Exists fun b : B => R b = true) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨rename a, ha⟩
  · rintro ⟨b, hb⟩
    exact ⟨rename.symm b, by simpa using hb⟩

theorem merge_isomorphic_predicates
    (rename : A ≃ B) (left : A -> Bool) (right : B -> Bool)
    (preserves : forall a, left a = right (rename a)) :
    (Exists fun a => left a = true) <->
      (Exists fun b => right b = true) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨rename a, by simpa [preserves a] using ha⟩
  · rintro ⟨b, hb⟩
    refine ⟨rename.symm b, ?_⟩
    calc
      left (rename.symm b) = right (rename (rename.symm b)) := preserves _
      _ = right b := by simp
      _ = true := hb

end A30_SymmetryIsomorphism

end ResearchNext
end PIsNPOrNot


namespace PIsNPOrNot
namespace ResearchNext

/-! ## 31 - Certified structural dispatch preserves the original decision problem -/
namespace A31_CertifiedDispatch

variable {Instance Reduced : Type}

def dispatch
    (recognize : Instance -> Option Reduced)
    (fast : Reduced -> Bool)
    (fallback : Instance -> Bool)
    (input : Instance) : Bool :=
  match recognize input with
  | some reduced => fast reduced
  | none => fallback input

theorem dispatch_correct
    (YesInstance : Instance -> Prop) (YesReduced : Reduced -> Prop)
    (recognize : Instance -> Option Reduced)
    (fast : Reduced -> Bool) (fallback : Instance -> Bool)
    (reduction_sound : forall input reduced,
      recognize input = some reduced ->
        (YesReduced reduced <-> YesInstance input))
    (fast_correct : forall reduced, fast reduced = true <-> YesReduced reduced)
    (fallback_correct : forall input, fallback input = true <-> YesInstance input)
    (input : Instance) :
    dispatch recognize fast fallback input = true <-> YesInstance input := by
  cases hrecognize : recognize input with
  | none =>
      simpa [dispatch, hrecognize] using fallback_correct input
  | some reduced =>
      calc
        dispatch recognize fast fallback input = true <->
            fast reduced = true := by simp [dispatch, hrecognize]
        _ <-> YesReduced reduced := fast_correct reduced
        _ <-> YesInstance input := reduction_sound input reduced hrecognize

end A31_CertifiedDispatch

/-! ## 32 - A finite portfolio remains exact when every branch is certified -/
namespace A32_CertifiedPortfolio

variable {I : Type}

def chooseFirst (solvers : List (I -> Option Bool)) (input : I) : Option Bool :=
  solvers.findSome? (fun solver => solver input)

theorem chosen_result_sound
    (Yes : I -> Prop) (solvers : List (I -> Option Bool))
    (sound : forall solver, solver ∈ solvers -> forall input result,
      solver input = some result -> (result = true <-> Yes input))
    (input : I) (result : Bool)
    (hchosen : chooseFirst solvers input = some result) :
    result = true <-> Yes input := by
  unfold chooseFirst at hchosen
  rw [List.findSome?_eq_some_iff] at hchosen
  rcases hchosen with ⟨before, solver, after, hlist, hrun, _⟩
  have hsolver : solver ∈ solvers := by
    rw [hlist]
    simp
  exact sound solver hsolver input result hrun

end A32_CertifiedPortfolio

end ResearchNext
end PIsNPOrNot
