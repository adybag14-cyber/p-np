import ResearchSeventeenth

namespace PIsNPOrNot
namespace ResearchEighteenth

/-! ## 241 - Bijective coordinate changes preserve existential acceptance -/
namespace A241_BijectiveTransform

variable {Witness : Type}

structure Transform where
  encode : Witness -> Witness
  decode : Witness -> Witness
  decodeEncode : forall witness, decode (encode witness) = witness
  encodeDecode : forall witness, encode (decode witness) = witness

theorem exists_after_decode_iff
    (relation : Witness -> Bool) (transform : Transform) :
    (exists witness, relation witness = true) <->
      exists encoded, relation (transform.decode encoded) = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨transform.encode witness, ?_⟩
    rw [transform.decodeEncode]
    exact accepted
  · rintro ⟨encoded, accepted⟩
    exact ⟨transform.decode encoded, accepted⟩

end A241_BijectiveTransform

/-! ## 242 - Coordinate transformations compose -/
namespace A242_TransformComposition

open A241_BijectiveTransform

variable {Witness : Type}

def Transform.comp (outer inner : Transform (Witness := Witness)) :
    Transform (Witness := Witness) where
  encode := fun witness => outer.encode (inner.encode witness)
  decode := fun witness => inner.decode (outer.decode witness)
  decodeEncode := by
    intro witness
    rw [outer.decodeEncode, inner.decodeEncode]
  encodeDecode := by
    intro witness
    rw [inner.encodeDecode, outer.encodeDecode]

end A242_TransformComposition

/-! ## 243 - A feature quotient is constant on every feature fiber -/
namespace A243_FiberConstancy

open ResearchSeventeenth.A226_FeatureQuotient

variable {Witness Feature : Type}

 theorem relation_equal_on_feature_fiber
    (relation : Witness -> Bool)
    (quotient : Quotient (Feature := Feature) relation)
    (left right : Witness)
    (sameFeature : quotient.feature left = quotient.feature right) :
    relation left = relation right := by
  rw [quotient.factors left, quotient.factors right, sameFeature]

end A243_FiberConstancy

/-! ## 244 - Distinguishable witnesses must receive different exact feature codes -/
namespace A244_DistinguishabilityInjection

open ResearchSeventeenth.A226_FeatureQuotient

variable {Witness Feature : Type}

 theorem feature_ne_of_relation_ne
    (relation : Witness -> Bool)
    (quotient : Quotient (Feature := Feature) relation)
    (left right : Witness)
    (different : Not (relation left = relation right)) :
    Not (quotient.feature left = quotient.feature right) := by
  intro sameFeature
  exact different (ResearchEighteenth.A243_FiberConstancy.relation_equal_on_feature_fiber
    relation quotient left right sameFeature)

end A244_DistinguishabilityInjection

/-! ## 245 - Exact transformed machines decide the original relation -/
namespace A245_TransformedMachine

open A241_BijectiveTransform

variable {Witness State : Type}

structure Machine (relation : Witness -> Bool) where
  transform : Transform (Witness := Witness)
  run : Witness -> State
  accept : State -> Bool
  exact : forall encoded,
    accept (run encoded) = relation (transform.decode encoded)

theorem accepted_encoded_state_gives_original_witness
    (relation : Witness -> Bool)
    (machine : Machine (State := State) relation)
    (encoded : Witness)
    (accepted : machine.accept (machine.run encoded) = true) :
    relation (machine.transform.decode encoded) = true := by
  rw [← machine.exact encoded]
  exact accepted

end A245_TransformedMachine

/-! ## 246 - Finite transformed state budgets bound reachable images -/
namespace A246_TransformedStateBudget

variable {Witness State : Type}
variable [Fintype Witness] [Fintype State] [DecidableEq State]

 theorem run_image_card_le_state_card (run : Witness -> State) :
    ((Finset.univ : Finset Witness).image run).card <= Fintype.card State := by
  have subset : ((Finset.univ : Finset Witness).image run) ⊆
      (Finset.univ : Finset State) := Finset.subset_univ _
  simpa using Finset.card_le_card subset

end A246_TransformedStateBudget

/-! ## 247 - Polynomially bounded affine coset counts remain polynomial -/
namespace A247_AffineCosetBudget

 theorem coset_enumeration_bound
    (cosets codimension input exponent : Nat)
    (cosetBound : cosets <= 2 ^ codimension)
    (codimensionBound : 2 ^ codimension <= input ^ exponent) :
    cosets <= input ^ exponent := by
  exact le_trans cosetBound codimensionBound

end A247_AffineCosetBudget

/-! ## 248 - Sparse algebraic normal forms have sparse evaluation cost -/
namespace A248_SparsePolynomialEvaluation

 theorem evaluation_work_bound
    (termCosts : List Nat) (termCount perTerm : Nat)
    (lengthBound : termCosts.length <= termCount)
    (costBound : forall cost, cost ∈ termCosts -> cost <= perTerm) :
    termCosts.sum <= termCount * perTerm := by
  have sumBound : termCosts.sum <= termCosts.length * perTerm := by
    clear termCount lengthBound
    induction termCosts with
    | nil => simp
    | cons head tail ih =>
        have hHead : head <= perTerm := costBound head (List.Mem.head tail)
        have hTail : forall cost, cost ∈ tail -> cost <= perTerm := by
          intro cost hmem
          exact costBound cost (List.Mem.tail head hmem)
        have hRec := ih hTail
        simp only [List.sum_cons, List.length_cons]
        calc
          head + tail.sum <= perTerm + tail.length * perTerm :=
            Nat.add_le_add hHead hRec
          _ = (tail.length + 1) * perTerm := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact le_trans sumBound (Nat.mul_le_mul_right perTerm lengthBound)

end A248_SparsePolynomialEvaluation

/-! ## 249 - Sparse spectral features need only their support image -/
namespace A249_SpectralSupport

variable {Input Frequency : Type}
variable [Fintype Input] [DecidableEq Frequency]

structure SparseSpectrum (relation : Input -> Bool) where
  active : Input -> Frequency
  evaluate : Frequency -> Bool
  factors : forall input, relation input = evaluate (active input)

theorem existential_reduces_to_active_frequencies
    (relation : Input -> Bool)
    (spectrum : SparseSpectrum (Frequency := Frequency) relation) :
    (exists input : Input, relation input = true) <->
      exists frequency : Frequency,
        frequency ∈ ((Finset.univ : Finset Input).image spectrum.active) /\
        spectrum.evaluate frequency = true := by
  constructor
  · rintro ⟨input, accepted⟩
    refine ⟨spectrum.active input, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨input, Finset.mem_univ input, rfl⟩
    · rw [← spectrum.factors input]
      exact accepted
  · rintro ⟨frequency, inImage, accepted⟩
    rcases Finset.mem_image.1 inImage with ⟨input, _, rfl⟩
    refine ⟨input, ?_⟩
    rw [spectrum.factors input]
    exact accepted

end A249_SpectralSupport

/-! ## 250 - Exact linear sketches may collide only on equal answers -/
namespace A250_LinearSketchSafety

variable {Input Sketch : Type}

structure ExactSketch (relation : Input -> Bool) where
  sketch : Input -> Sketch
  answer : Sketch -> Bool
  exact : forall input, relation input = answer (sketch input)

theorem collision_safe
    (relation : Input -> Bool)
    (exactSketch : ExactSketch (Sketch := Sketch) relation)
    (left right : Input)
    (collision : exactSketch.sketch left = exactSketch.sketch right) :
    relation left = relation right := by
  rw [exactSketch.exact left, exactSketch.exact right, collision]

end A250_LinearSketchSafety

/-! ## 251 - A finite family of exact sketches has a union state bound -/
namespace A251_SketchPortfolio

variable {State : Type} [DecidableEq State]

 theorem union_state_bound
    (families : List (Finset State)) (perFamily count : Nat)
    (lengthBound : families.length <= count)
    (familyBound : forall family, family ∈ families -> family.card <= perFamily) :
    (families.foldl (fun total family => total ∪ family) ∅).card <=
      count * perFamily := by
  have foldGeneral : forall start : Finset State,
      (families.foldl (fun total family => total ∪ family) start).card <=
        start.card + families.length * perFamily := by
    intro start
    clear count lengthBound
    induction families generalizing start with
    | nil => simp
    | cons head tail ih =>
        have hHead : head.card <= perFamily :=
          familyBound head (List.Mem.head tail)
        have hTail : forall family, family ∈ tail -> family.card <= perFamily := by
          intro family hmem
          exact familyBound family (List.Mem.tail head hmem)
        have hUnion : (start ∪ head).card <= start.card + perFamily := by
          calc
            (start ∪ head).card <= start.card + head.card :=
              ResearchTwelfth.A158_SharingUpperBound.union_card_le_sum start head
            _ <= start.card + perFamily := Nat.add_le_add_left hHead start.card
        have hRec := ih (start := start ∪ head) hTail
        calc
          ((head :: tail).foldl (fun total family => total ∪ family) start).card =
              (tail.foldl (fun total family => total ∪ family) (start ∪ head)).card := rfl
          _ <= (start ∪ head).card + tail.length * perFamily := hRec
          _ <= (start.card + perFamily) + tail.length * perFamily :=
            Nat.add_le_add_right hUnion _
          _ = start.card + (tail.length + 1) * perFamily := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
  have foldBound :
      (families.foldl (fun total family => total ∪ family) ∅).card <=
        families.length * perFamily := by
    simpa using foldGeneral (∅ : Finset State)
  exact le_trans foldBound (Nat.mul_le_mul_right perFamily lengthBound)

end A251_SketchPortfolio

/-! ## 252 - Proof-carrying radical certificates need only checker soundness -/
namespace A252_RadicalCertificate

variable {Instance Certificate : Type}

structure CertificateChecker (specification : Instance -> Prop) where
  check : Instance -> Certificate -> Bool
  sound : forall input certificate,
    check input certificate = true -> specification input

theorem checked_certificate_sound
    (specification : Instance -> Prop)
    (checker : CertificateChecker (Certificate := Certificate) specification)
    (input : Instance) (certificate : Certificate)
    (checked : checker.check input certificate = true) :
    specification input := by
  exact checker.sound input certificate checked

end A252_RadicalCertificate

/-! ## 253 - Polynomial hash families with polynomial checks remain polynomial -/
namespace A253_HashFamilyBudget

 theorem hash_search_work_bound
    (hashCount perHash input hashExponent checkExponent : Nat)
    (hashBound : hashCount <= input ^ hashExponent)
    (checkBound : perHash <= input ^ checkExponent) :
    hashCount * perHash <= input ^ (hashExponent + checkExponent) := by
  calc
    hashCount * perHash <=
        (input ^ hashExponent) * (input ^ checkExponent) :=
      Nat.mul_le_mul hashBound checkBound
    _ = input ^ (hashExponent + checkExponent) := by rw [pow_add]

end A253_HashFamilyBudget

/-! ## 254 - A radical portfolio may dispatch to any exact polynomial representation -/
namespace A254_RadicalDispatch

variable {Instance : Type}

structure Solver where
  solve : Instance -> Bool
  specification : Instance -> Prop
  exact : forall input, solve input = true <-> specification input

 theorem chosen_solver_exact
    (solvers : List (Solver (Instance := Instance)))
    (chosen : Solver (Instance := Instance))
    (member : chosen ∈ solvers)
    (input : Instance) :
    chosen.solve input = true <-> chosen.specification input := by
  exact chosen.exact input

end A254_RadicalDispatch

/-! ## 255 - Uniform transformed or sketched deciders yield P = NP -/
namespace A255_TransformSketchCollapse

variable {Language : Type}

 theorem p_eq_np_of_uniform_transform_sketch_cover
    (InP InNP HasTransformSketch : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (coverImpliesP : forall language, HasTransformSketch language -> InP language)
    (uniform : forall language, InNP language -> HasTransformSketch language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact coverImpliesP language (uniform language hNP)

end A255_TransformSketchCollapse

end ResearchEighteenth
end PIsNPOrNot
