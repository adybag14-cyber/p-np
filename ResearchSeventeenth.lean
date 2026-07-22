import ResearchSixteenth

namespace PIsNPOrNot
namespace ResearchSeventeenth

/-! ## 226 - Feature quotients preserve existential acceptance -/
namespace A226_FeatureQuotient

variable {Witness Feature : Type}
variable [Fintype Witness] [DecidableEq Feature]

structure Quotient (relation : Witness -> Bool) where
  feature : Witness -> Feature
  acceptFeature : Feature -> Bool
  factors : forall witness,
    relation witness = acceptFeature (feature witness)

theorem exists_witness_iff_feature_image
    (relation : Witness -> Bool)
    (quotient : Quotient (Feature := Feature) relation) :
    (exists witness : Witness, relation witness = true) <->
      exists feature : Feature,
        feature ∈ ((Finset.univ : Finset Witness).image quotient.feature) /\
        quotient.acceptFeature feature = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨quotient.feature witness, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨witness, Finset.mem_univ witness, rfl⟩
    · rw [← quotient.factors witness]
      exact accepted
  · rintro ⟨feature, inImage, accepted⟩
    rcases Finset.mem_image.1 inImage with ⟨witness, _, rfl⟩
    refine ⟨witness, ?_⟩
    rw [quotient.factors witness]
    exact accepted

end A226_FeatureQuotient

/-! ## 227 - Universally lossless feature maps cannot reduce cardinality -/
namespace A227_InjectiveFeatureBarrier

variable {Witness Feature : Type}
variable [Fintype Witness] [Fintype Feature]

theorem card_le_of_injective_feature
    (feature : Witness -> Feature) (injective : Function.Injective feature) :
    Fintype.card Witness <= Fintype.card Feature := by
  exact Fintype.card_le_of_injective feature injective

end A227_InjectiveFeatureBarrier

/-! ## 228 - Accepted features recover witnesses when fibers have representatives -/
namespace A228_FiberRecovery

variable {Witness Feature : Type}

structure FiberRepresentative (feature : Witness -> Feature) where
  representative : Feature -> Witness
  rightInverse : forall value, feature (representative value) = value

theorem recover_accepted_witness
    (relation : Witness -> Bool)
    (feature : Witness -> Feature)
    (acceptFeature : Feature -> Bool)
    (factors : forall witness, relation witness = acceptFeature (feature witness))
    (fiber : FiberRepresentative feature)
    (value : Feature)
    (accepted : acceptFeature value = true) :
    relation (fiber.representative value) = true := by
  rw [factors, fiber.rightInverse]
  exact accepted

end A228_FiberRecovery

/-! ## 229 - Sparse feature descriptions have linear total support cost -/
namespace A229_SparseSupportAccounting

theorem support_sum_bound
    (supports : List (Finset Nat)) (sparsity : Nat)
    (bounded : forall support, support ∈ supports -> support.card <= sparsity) :
    (supports.map Finset.card).sum <= supports.length * sparsity := by
  induction supports with
  | nil => simp
  | cons head tail ih =>
      have hHead : head.card <= sparsity := bounded head (List.Mem.head tail)
      have hTail : forall support, support ∈ tail -> support.card <= sparsity := by
        intro support hmem
        exact bounded support (List.Mem.tail head hmem)
      have hRec : (tail.map Finset.card).sum <= tail.length * sparsity := ih hTail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        head.card + (tail.map Finset.card).sum <=
            sparsity + tail.length * sparsity := Nat.add_le_add hHead hRec
        _ = (tail.length + 1) * sparsity := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end A229_SparseSupportAccounting

/-! ## 230 - Polynomially many features with polynomial evaluation remain polynomial -/
namespace A230_FeatureEnumerationBudget

theorem feature_work_bound
    (featureCount perFeature input featureExponent workExponent : Nat)
    (countBound : featureCount <= input ^ featureExponent)
    (workBound : perFeature <= input ^ workExponent) :
    featureCount * perFeature <= input ^ (featureExponent + workExponent) := by
  calc
    featureCount * perFeature <=
        (input ^ featureExponent) * (input ^ workExponent) :=
      Nat.mul_le_mul countBound workBound
    _ = input ^ (featureExponent + workExponent) := by
      rw [pow_add]

end A230_FeatureEnumerationBudget

/-! ## 231 - Canonical orbit representatives preserve invariant predicates -/
namespace A231_OrbitCanonicalization

variable {Witness Orbit : Type}

structure Canonicalizer (relation : Witness -> Bool) where
  canon : Witness -> Orbit
  representative : Orbit -> Witness
  representativeCanon : forall witness,
    canon (representative (canon witness)) = canon witness
  invariant : forall left right,
    canon left = canon right -> relation left = relation right

theorem representative_preserves
    (relation : Witness -> Bool)
    (canonical : Canonicalizer (Orbit := Orbit) relation)
    (witness : Witness) :
    relation (canonical.representative (canonical.canon witness)) =
      relation witness := by
  exact canonical.invariant _ _ (canonical.representativeCanon witness)

end A231_OrbitCanonicalization

/-! ## 232 - Orbit representatives decide existential acceptance -/
namespace A232_OrbitDecision

open A231_OrbitCanonicalization

variable {Witness Orbit : Type}
variable [Fintype Witness] [DecidableEq Orbit]

theorem exists_witness_iff_representative_image
    (relation : Witness -> Bool)
    (canonical : Canonicalizer (Orbit := Orbit) relation) :
    (exists witness : Witness, relation witness = true) <->
      exists orbit : Orbit,
        orbit ∈ ((Finset.univ : Finset Witness).image canonical.canon) /\
        relation (canonical.representative orbit) = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    refine ⟨canonical.canon witness, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨witness, Finset.mem_univ witness, rfl⟩
    · rw [A231_OrbitCanonicalization.representative_preserves relation canonical witness]
      exact accepted
  · rintro ⟨orbit, inImage, accepted⟩
    rcases Finset.mem_image.1 inImage with ⟨witness, _, rfl⟩
    refine ⟨witness, ?_⟩
    rw [← A231_OrbitCanonicalization.representative_preserves relation canonical witness]
    exact accepted

end A232_OrbitDecision

/-! ## 233 - Orbit images are bounded by the orbit type -/
namespace A233_OrbitCardinality

variable {Witness Orbit : Type}
variable [Fintype Witness] [Fintype Orbit] [DecidableEq Orbit]

theorem orbit_image_card_le
    (canon : Witness -> Orbit) :
    ((Finset.univ : Finset Witness).image canon).card <= Fintype.card Orbit := by
  have subset : ((Finset.univ : Finset Witness).image canon) ⊆
      (Finset.univ : Finset Orbit) := Finset.subset_univ _
  simpa using Finset.card_le_card subset

end A233_OrbitCardinality

/-! ## 234 - Separator tensor products have explicit state cost -/
namespace A234_TensorSeparatorBudget

theorem tensor_state_bound
    (leftStates rightStates separatorAssignments : Nat)
    (leftBound rightBound separatorBound : Nat)
    (hLeft : leftStates <= leftBound)
    (hRight : rightStates <= rightBound)
    (hSeparator : separatorAssignments <= separatorBound) :
    leftStates * rightStates * separatorAssignments <=
      leftBound * rightBound * separatorBound := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hLeft hRight) hSeparator

end A234_TensorSeparatorBudget

/-! ## 235 - Low-rank feature factorizations reduce existential search to feature pairs -/
namespace A235_LowRankFactorization

variable {Witness LeftFeature RightFeature : Type}

structure Factorization (relation : Witness -> Bool) where
  left : Witness -> LeftFeature
  right : Witness -> RightFeature
  combine : LeftFeature -> RightFeature -> Bool
  factors : forall witness,
    relation witness = combine (left witness) (right witness)

theorem accepted_witness_gives_accepted_pair
    (relation : Witness -> Bool)
    (factor : Factorization
      (LeftFeature := LeftFeature) (RightFeature := RightFeature) relation)
    (witness : Witness) (accepted : relation witness = true) :
    factor.combine (factor.left witness) (factor.right witness) = true := by
  rw [← factor.factors witness]
  exact accepted

end A235_LowRankFactorization

/-! ## 236 - Deterministic isolation families cover all accepted witnesses -/
namespace A236_IsolationFamily

variable {Witness Hash : Type}

structure IsolationCover (accepted : Witness -> Prop) where
  isolates : Hash -> Witness -> Prop
  cover : forall witness, accepted witness -> exists hash, isolates hash witness

theorem accepted_implies_isolated
    (accepted : Witness -> Prop)
    (cover : IsolationCover (Hash := Hash) accepted) :
    (exists witness : Witness, accepted witness) ->
      exists hash : Hash, exists witness : Witness,
        accepted witness /\ cover.isolates hash witness := by
  rintro ⟨witness, hAccepted⟩
  rcases cover.cover witness hAccepted with ⟨hash, hIsolates⟩
  exact ⟨hash, witness, hAccepted, hIsolates⟩

end A236_IsolationFamily

/-! ## 237 - Unique isolation makes witness recovery unambiguous -/
namespace A237_UniqueIsolation

variable {Witness Hash : Type}

structure UniqueIsolator (accepted : Witness -> Prop) where
  isolates : Hash -> Witness -> Prop
  unique : forall hash left right,
    accepted left -> accepted right ->
    isolates hash left -> isolates hash right -> left = right

theorem isolated_witness_unique
    (accepted : Witness -> Prop)
    (isolation : UniqueIsolator (Hash := Hash) accepted)
    (hash : Hash) (left right : Witness)
    (hLeft : accepted left) (hRight : accepted right)
    (iLeft : isolation.isolates hash left)
    (iRight : isolation.isolates hash right) :
    left = right := by
  exact isolation.unique hash left right hLeft hRight iLeft iRight

end A237_UniqueIsolation

/-! ## 238 - Entailed learned constraints preserve the model set -/
namespace A238_EntailedLearning

variable {Assignment : Type}

theorem add_entailed_preserves_models
    (base learned : Assignment -> Prop)
    (entailed : forall assignment, base assignment -> learned assignment) :
    (fun assignment => base assignment /\ learned assignment) = base := by
  funext assignment
  apply propext
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, entailed assignment h⟩

end A238_EntailedLearning

/-! ## 239 - Proof-trace checkers transfer correctness to compiled answers -/
namespace A239_ProofTraceReplay

variable {Instance Trace : Type}

structure Checker (specification : Instance -> Prop) where
  check : Instance -> Trace -> Bool
  sound : forall input trace,
    check input trace = true -> specification input

theorem accepted_trace_sound
    (specification : Instance -> Prop)
    (checker : Checker (Trace := Trace) specification)
    (input : Instance) (trace : Trace)
    (accepted : checker.check input trace = true) :
    specification input := by
  exact checker.sound input trace accepted

end A239_ProofTraceReplay

/-! ## 240 - A uniform radical representation cover yields class collapse -/
namespace A240_RadicalCoverCriterion

variable {Language : Type}

theorem p_eq_np_of_radical_cover
    (InP InNP HasRadicalRepresentation : Language -> Prop)
    (p_subset_np : forall language, InP language -> InNP language)
    (representationImpliesP : forall language,
      HasRadicalRepresentation language -> InP language)
    (uniform : forall language,
      InNP language -> HasRadicalRepresentation language) :
    {language | InP language} = {language | InNP language} := by
  apply Set.ext
  intro language
  constructor
  · intro hP
    exact p_subset_np language hP
  · intro hNP
    exact representationImpliesP language (uniform language hNP)

end A240_RadicalCoverCriterion

end ResearchSeventeenth
end PIsNPOrNot
