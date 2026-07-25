import ResearchFiftyNinth

namespace PIsNPOrNot.ResearchSixtieth

/-! ## 871 - The accepted witness set is the exact finite verifier image -/
namespace A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

def acceptedSet (verifier : U -> Bool) : Finset U :=
  (Finset.univ : Finset U).filter (fun value => verifier value = true)

@[simp] theorem mem_acceptedSet
    (verifier : U -> Bool) (value : U) :
    value ∈ acceptedSet verifier ↔ verifier value = true := by
  simp [acceptedSet]

end A871_AcceptedSet

/-! ## 872 - Satisfiability is nonemptiness of the accepted set -/
namespace A872_AcceptedNonempty

open A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

 theorem nonempty_iff_exists
    (verifier : U -> Bool) :
    (acceptedSet verifier).Nonempty ↔
      Exists fun witness => verifier witness = true := by
  constructor
  · rintro ⟨witness, member⟩
    exact ⟨witness, (mem_acceptedSet verifier witness).mp member⟩
  · rintro ⟨witness, accepted⟩
    exact ⟨witness, (mem_acceptedSet verifier witness).mpr accepted⟩

end A872_AcceptedNonempty

/-! ## 873 - A known witness gives a one-test formula-dependent isolator -/
namespace A873_WitnessTailoredTest

open ResearchFiftyEighth.A841_TargetedIsolation
open A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

 theorem singleton_isolates
    (verifier : U -> Bool) {witness : U}
    (accepted : verifier witness = true) :
    Isolates ({witness} : Finset U) (acceptedSet verifier) := by
  unfold Isolates
  have member : witness ∈ acceptedSet verifier :=
    (mem_acceptedSet verifier witness).mpr accepted
  simp [member]

end A873_WitnessTailoredTest

/-! ## 874 - One tailored test always exists, but its construction chooses a witness -/
namespace A874_OneTestExistence

open ResearchFiftyEighth.A841_TargetedIsolation
open A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

 theorem exists_one_test
    (verifier : U -> Bool)
    (satisfiable : Exists fun witness => verifier witness = true) :
    Exists fun test : Finset U =>
      Isolates test (acceptedSet verifier) := by
  let witness := satisfiable.choose
  exact Exists.intro ({witness} : Finset U)
    (A873_WitnessTailoredTest.singleton_isolates
      verifier satisfiable.choose_spec)

end A874_OneTestExistence

/-! ## 875 - A proof-carrying targeted test exposes its unique accepted witness -/
namespace A875_TargetedCertificate

open ResearchFiftyEighth.A841_TargetedIsolation
open A871_AcceptedSet

variable {U : Type} [Fintype U] [DecidableEq U]

structure Certificate (verifier : U -> Bool) where
  test : Finset U
  isolated : Isolates test (acceptedSet verifier)

noncomputable def chosenWitness
    {verifier : U -> Bool} (certificate : Certificate verifier) : U :=
  (Finset.card_eq_one_iff_existsUnique.mp certificate.isolated).choose

theorem chosenWitness_accepted
    {verifier : U -> Bool} (certificate : Certificate verifier) :
    verifier (chosenWitness certificate) = true := by
  have member :=
    (Finset.card_eq_one_iff_existsUnique.mp certificate.isolated).choose_spec.1
  exact (A871_AcceptedSet.mem_acceptedSet verifier (chosenWitness certificate)).mp
    (Finset.mem_inter.mp member).1

end A875_TargetedCertificate

/-! ## 876 - Constructing a targeted certificate is already a witness-search algorithm -/
namespace A876_CertificateCompilerCircularity

open A871_AcceptedSet A875_TargetedCertificate

variable {U : Type} [Fintype U] [DecidableEq U]

structure Compiler (U : Type) [Fintype U] [DecidableEq U] where
  compile : (verifier : U -> Bool) ->
    (acceptedSet verifier).Nonempty -> Certificate verifier

noncomputable def findWitness
    (compiler : Compiler U) (verifier : U -> Bool)
    (satisfiable : Exists fun witness => verifier witness = true) : U :=
  let nonempty := (A872_AcceptedNonempty.nonempty_iff_exists verifier).mpr satisfiable
  A875_TargetedCertificate.chosenWitness
    (compiler.compile verifier nonempty)

theorem findWitness_accepted
    (compiler : Compiler U) (verifier : U -> Bool)
    (satisfiable : Exists fun witness => verifier witness = true) :
    verifier (findWitness compiler verifier satisfiable) = true := by
  unfold findWitness
  exact A875_TargetedCertificate.chosenWitness_accepted _

end A876_CertificateCompilerCircularity

/-! ## 877 - A hash bucket is one targeted subset of the witness universe -/
namespace A877_HashBucket

variable {U Bucket : Type}
variable [Fintype U] [DecidableEq U] [DecidableEq Bucket]

def bucket (hash : U -> Bucket) (target : Bucket) : Finset U :=
  (Finset.univ : Finset U).filter (fun value => hash value = target)

@[simp] theorem mem_bucket
    (hash : U -> Bucket) (target : Bucket) (value : U) :
    value ∈ bucket hash target ↔ hash value = target := by
  simp [bucket]

end A877_HashBucket

/-! ## 878 - Bucket occupancy is the exact number of accepted witnesses in the fiber -/
namespace A878_BucketCount

open A871_AcceptedSet A877_HashBucket

variable {U Bucket : Type}
variable [Fintype U] [DecidableEq U] [DecidableEq Bucket]

def bucketCount (verifier : U -> Bool)
    (hash : U -> Bucket) (target : Bucket) : Nat :=
  ((acceptedSet verifier) ∩ bucket hash target).card

 theorem count_eq_one_iff_isolates
    (verifier : U -> Bool) (hash : U -> Bucket) (target : Bucket) :
    bucketCount verifier hash target = 1 ↔
      ResearchFiftyEighth.A841_TargetedIsolation.Isolates
        (bucket hash target) (acceptedSet verifier) := by
  rfl

end A878_BucketCount

/-! ## 879 - A unique target packages the affine-hash isolation objective -/
namespace A879_UniqueTarget

open A878_BucketCount

variable {U Bucket : Type}
variable [Fintype U] [DecidableEq U] [DecidableEq Bucket]

structure UniqueTarget (verifier : U -> Bool) (hash : U -> Bucket) where
  target : Bucket
  unique : bucketCount verifier hash target = 1

end A879_UniqueTarget

/-! ## 880 - A unique target recovers one accepted witness -/
namespace A880_UniqueTargetRecovery

open A871_AcceptedSet A877_HashBucket A878_BucketCount A879_UniqueTarget

variable {U Bucket : Type}
variable [Fintype U] [DecidableEq U] [DecidableEq Bucket]

noncomputable def chosenWitness
    {verifier : U -> Bool} {hash : U -> Bucket}
    (target : UniqueTarget verifier hash) : U :=
  (Finset.card_eq_one_iff_existsUnique.mp target.unique).choose

theorem chosenWitness_accepted
    {verifier : U -> Bool} {hash : U -> Bucket}
    (target : UniqueTarget verifier hash) :
    verifier (chosenWitness target) = true := by
  have member :=
    (Finset.card_eq_one_iff_existsUnique.mp target.unique).choose_spec.1
  exact (A871_AcceptedSet.mem_acceptedSet verifier (chosenWitness target)).mp
    (Finset.mem_inter.mp member).1

end A880_UniqueTargetRecovery

/-! ## 881 - Identity hashing makes every bucket a singleton -/
namespace A881_IdentityBuckets

open A877_HashBucket

variable {U : Type} [Fintype U] [DecidableEq U]

 theorem identity_bucket (target : U) :
    bucket (fun value : U => value) target = {target} := by
  ext value
  simp [bucket]

end A881_IdentityBuckets

/-! ## 882 - An identity bucket is occupied exactly when its target is a witness -/
namespace A882_IdentityOccupancyCircularity

open A871_AcceptedSet A877_HashBucket A878_BucketCount

variable {U : Type} [Fintype U] [DecidableEq U]

 theorem identity_count_eq_one_iff
    (verifier : U -> Bool) (target : U) :
    bucketCount verifier (fun value : U => value) target = 1 ↔
      verifier target = true := by
  rw [bucketCount, A881_IdentityBuckets.identity_bucket]
  by_cases accepted : verifier target = true
  · have member : target ∈ acceptedSet verifier :=
      (mem_acceptedSet verifier target).mpr accepted
    simp [member, accepted]
  · have notMember : target ∉ acceptedSet verifier := by
      simpa [mem_acceptedSet] using accepted
    simp [notMember, accepted]

end A882_IdentityOccupancyCircularity

/-! ## 883 - Selecting an occupied identity target is exactly witness search -/
namespace A883_IdentityTargetSelector

structure Selector (U : Type) where
  select : (verifier : U -> Bool) ->
    (Exists fun witness => verifier witness = true) -> U
  occupied : forall (verifier : U -> Bool)
      (satisfiable : Exists fun witness => verifier witness = true),
    verifier (select verifier satisfiable) = true

theorem selected_is_witness {U : Type}
    (selector : Selector U) (verifier : U -> Bool)
    (satisfiable : Exists fun witness => verifier witness = true) :
    verifier (selector.select verifier satisfiable) = true :=
  selector.occupied verifier satisfiable

end A883_IdentityTargetSelector

/-! ## 884 - Low-rank isolator existence and polynomial discovery are separate claims -/
namespace A884_IsolationDiscoveryAccounting

structure Profile where
  inputBits : Nat
  hashRank : Nat
  candidateMaps : Nat
  verifierEvaluations : Nat
  histogramEntries : Nat

 def exhaustiveProfile (n rank maps : Nat) : Profile where
  inputBits := n
  hashRank := rank
  candidateMaps := maps
  verifierEvaluations := 2 ^ n
  histogramEntries := 2 ^ rank

 theorem exhaustive_evaluations
    (n rank maps : Nat) :
    (exhaustiveProfile n rank maps).verifierEvaluations = 2 ^ n := rfl

end A884_IsolationDiscoveryAccounting

/-! ## 885 - A uniform fast formula-dependent isolator would settle witness search -/
namespace A885_FormulaDependentIsolationCriterion

open A871_AcceptedSet A875_TargetedCertificate

variable {U : Type} [Fintype U] [DecidableEq U]

structure FastCompiler (U : Type) [Fintype U] [DecidableEq U] where
  compile : (verifier : U -> Bool) -> Option (Certificate verifier)
  exact : forall verifier,
    (Exists fun witness => verifier witness = true) <->
      Exists fun certificate => compile verifier = some certificate
  constructionCost : Nat
  certificateCheckCost : Nat

theorem successful_compile_gives_witness
    (compiler : FastCompiler U) (verifier : U -> Bool)
    {certificate : Certificate verifier}
    (_success : compiler.compile verifier = some certificate) :
    verifier (A875_TargetedCertificate.chosenWitness certificate) = true := by
  exact A875_TargetedCertificate.chosenWitness_accepted certificate

end A885_FormulaDependentIsolationCriterion

end PIsNPOrNot.ResearchSixtieth
