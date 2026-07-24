import Mathlib
import ResearchTwentyEighth
import ResearchThirtieth
import ResearchEighteenth

namespace PIsNPOrNot.ResearchThirtyFirst

/-! ## 436 - A syndrome generator parameterizes every reachable signature -/
namespace A436_SyndromeGenerator

variable {Witness : Type}

structure Generator {rank outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool)) where
  encode : (Fin rank -> Bool) -> (Fin outputWidth -> Bool)
  representative : (Fin rank -> Bool) -> Witness
  complete : forall witness,
    exists coordinates, feature witness = encode coordinates
  exactRepresentative : forall coordinates,
    feature (representative coordinates) = encode coordinates

end A436_SyndromeGenerator

/-! ## 437 - A syndrome generator gives the exact reachable image -/
namespace A437_SyndromeImageExact

open A436_SyndromeGenerator
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Witness : Type} [Fintype Witness]

 theorem reachable_eq_coordinate_image
    {rank outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := rank) feature) :
    reachableImage feature =
      (Finset.univ : Finset (Fin rank -> Bool)).image generator.encode := by
  classical
  ext value
  constructor
  · intro member
    rcases Finset.mem_image.1 member with ⟨witness, _, valueEq⟩
    rcases generator.complete witness with ⟨coordinates, featureEq⟩
    apply Finset.mem_image.2
    refine ⟨coordinates, Finset.mem_univ _, ?_⟩
    exact featureEq.symm.trans valueEq
  · intro member
    rcases Finset.mem_image.1 member with ⟨coordinates, _, valueEq⟩
    apply Finset.mem_image.2
    refine ⟨generator.representative coordinates, Finset.mem_univ _, ?_⟩
    exact generator.exactRepresentative coordinates |>.trans valueEq

end A437_SyndromeImageExact

/-! ## 438 - Rank r gives at most two to the r reachable signatures -/
namespace A438_SyndromeCardinality

open A436_SyndromeGenerator A437_SyndromeImageExact
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Witness : Type} [Fintype Witness]

 theorem reachable_card_le_pow_two
    {rank outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := rank) feature) :
    (reachableImage feature).card <= 2 ^ rank := by
  classical
  rw [reachable_eq_coordinate_image feature generator]
  calc
    ((Finset.univ : Finset (Fin rank -> Bool)).image generator.encode).card <=
        (Finset.univ : Finset (Fin rank -> Bool)).card := Finset.card_image_le
    _ = 2 ^ rank := by simp

end A438_SyndromeCardinality

/-! ## 439 - Coordinates give a concrete complete and sound image table -/
namespace A439_SyndromeTable

open A436_SyndromeGenerator
open ResearchThirtieth.A421_ExactImageTable

variable {Witness : Type} [Fintype Witness]

 def syndromeTable
    {rank outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := rank) feature) :
    Table feature where
  rows := (Finset.univ : Finset (Fin rank -> Bool)).image generator.encode
  complete := by
    intro witness
    rcases generator.complete witness with ⟨coordinates, featureEq⟩
    exact Finset.mem_image.2 ⟨coordinates, Finset.mem_univ _, featureEq.symm⟩
  sound := by
    intro value member
    rcases Finset.mem_image.1 member with ⟨coordinates, _, valueEq⟩
    refine ⟨generator.representative coordinates, ?_⟩
    exact generator.exactRepresentative coordinates |>.trans valueEq

end A439_SyndromeTable

/-! ## 440 - Acceptance reduces exactly to coordinate enumeration -/
namespace A440_SyndromeDecision

open A436_SyndromeGenerator

variable {Witness : Type}

 theorem exists_accepting_iff_coordinates
    {rank outputWidth : Nat}
    (relation : Witness -> Bool)
    (feature : Witness -> (Fin outputWidth -> Bool))
    (acceptSignature : (Fin outputWidth -> Bool) -> Bool)
    (factors : forall witness,
      relation witness = acceptSignature (feature witness))
    (generator : Generator (rank := rank) feature) :
    (exists witness, relation witness = true) <->
      exists coordinates : Fin rank -> Bool,
        acceptSignature (generator.encode coordinates) = true := by
  constructor
  · rintro ⟨witness, accepted⟩
    rcases generator.complete witness with ⟨coordinates, featureEq⟩
    refine ⟨coordinates, ?_⟩
    rw [factors witness, featureEq] at accepted
    exact accepted
  · rintro ⟨coordinates, accepted⟩
    refine ⟨generator.representative coordinates, ?_⟩
    rw [factors, generator.exactRepresentative]
    exact accepted

end A440_SyndromeDecision

/-! ## 441 - Accepted coordinates recover an explicit accepting witness -/
namespace A441_SyndromeWitnessRecovery

open A436_SyndromeGenerator

variable {Witness : Type}

 theorem recover_accepting_witness
    {rank outputWidth : Nat}
    (relation : Witness -> Bool)
    (feature : Witness -> (Fin outputWidth -> Bool))
    (acceptSignature : (Fin outputWidth -> Bool) -> Bool)
    (factors : forall witness,
      relation witness = acceptSignature (feature witness))
    (generator : Generator (rank := rank) feature)
    (coordinates : Fin rank -> Bool)
    (accepted : acceptSignature (generator.encode coordinates) = true) :
    relation (generator.representative coordinates) = true := by
  rw [factors, generator.exactRepresentative]
  exact accepted

end A441_SyndromeWitnessRecovery

/-! ## 442 - Injective coordinate encodings realize exactly two to the rank signatures -/
namespace A442_InjectiveSyndromeCardinality

open A436_SyndromeGenerator A437_SyndromeImageExact
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Witness : Type} [Fintype Witness]

 theorem reachable_card_eq_pow_two_of_injective
    {rank outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := rank) feature)
    (injective : Function.Injective generator.encode) :
    (reachableImage feature).card = 2 ^ rank := by
  classical
  rw [reachable_eq_coordinate_image feature generator]
  rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin rank -> Bool)) injective]
  simp

end A442_InjectiveSyndromeCardinality

/-! ## 443 - Rank one has at most two reachable signatures -/
namespace A443_RankOneBound

open A436_SyndromeGenerator A438_SyndromeCardinality
open ResearchTwentyEighth.A391_ReachableFeatureImage

variable {Witness : Type} [Fintype Witness]

 theorem rank_one_image_le_two
    {outputWidth : Nat}
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := 1) feature) :
    (reachableImage feature).card <= 2 := by
  simpa using reachable_card_le_pow_two feature generator

end A443_RankOneBound

/-! ## 444 - Independent syndrome generators multiply their image bounds -/
namespace A444_ProductSyndromeBound

open A436_SyndromeGenerator A438_SyndromeCardinality
open ResearchTwentyEighth.A391_ReachableFeatureImage
open ResearchTwentyNinth.A406_ProductFeature
open ResearchTwentyNinth.A408_ProductImageCardinality

variable {Left Right : Type} [Fintype Left] [Fintype Right]

 theorem product_image_le_rank_product
    {leftRank rightRank leftWidth rightWidth : Nat}
    (leftFeature : Left -> (Fin leftWidth -> Bool))
    (rightFeature : Right -> (Fin rightWidth -> Bool))
    (leftGenerator : Generator (rank := leftRank) leftFeature)
    (rightGenerator : Generator (rank := rightRank) rightFeature) :
    (reachableImage (productFeature leftFeature rightFeature)).card <=
      (2 ^ leftRank) * (2 ^ rightRank) := by
  rw [reachable_product_card]
  exact Nat.mul_le_mul
    (reachable_card_le_pow_two leftFeature leftGenerator)
    (reachable_card_le_pow_two rightFeature rightGenerator)

end A444_ProductSyndromeBound

/-! ## 445 - Bijective preprocessing transports syndrome generators -/
namespace A445_TransformSyndromeGenerator

open A436_SyndromeGenerator
open ResearchEighteenth.A241_BijectiveTransform

variable {Witness : Type}

 def transportGenerator
    {rank outputWidth : Nat}
    (transform : Transform (Witness := Witness))
    (feature : Witness -> (Fin outputWidth -> Bool))
    (generator : Generator (rank := rank) feature) :
    Generator (rank := rank) (fun witness => feature (transform.encode witness)) where
  encode := generator.encode
  representative := fun coordinates =>
    transform.decode (generator.representative coordinates)
  complete := by
    intro witness
    exact generator.complete (transform.encode witness)
  exactRepresentative := by
    intro coordinates
    simpa [transform.encodeDecode] using generator.exactRepresentative coordinates

end A445_TransformSyndromeGenerator

/-! ## 446 - Full coordinate enumeration contains exactly two to the rank candidates -/
namespace A446_CoordinateEnumerationCost

 theorem coordinate_cube_card (rank : Nat) :
    (Finset.univ : Finset (Fin rank -> Bool)).card = 2 ^ rank := by
  simp

end A446_CoordinateEnumerationCost

/-! ## 447 - Polynomial coordinate count and polynomial signature evaluation compose -/
namespace A447_SyndromeWorkBudget

 theorem enumeration_scan_bound
    (coordinateCount evaluation input coordinateExp evalExp : Nat)
    (coordinateBound : coordinateCount <= input ^ coordinateExp)
    (evaluationBound : evaluation <= input ^ evalExp) :
    coordinateCount * evaluation <=
      input ^ coordinateExp * input ^ evalExp := by
  exact Nat.mul_le_mul coordinateBound evaluationBound

end A447_SyndromeWorkBudget

/-! ## 448 - A rank-one generator for the output feature already supplies SAT witnesses -/
namespace A448_OutputSyndromeCircularity

open A436_SyndromeGenerator
open ResearchTwentyEighth.A396_OutputFeature

variable {Witness : Type}

 theorem true_coordinate_gives_witness
    (relation : Witness -> Bool)
    (generator : Generator (rank := 1)
      (fun witness (_ : Fin 1) => relation witness))
    (coordinates : Fin 1 -> Bool)
    (encodedTrue : generator.encode coordinates = fun _ => true) :
    relation (generator.representative coordinates) = true := by
  have exactFeature := generator.exactRepresentative coordinates
  have atZero := congrFun (exactFeature.trans encodedTrue) 0
  simpa using atZero

end A448_OutputSyndromeCircularity

/-! ## 449 - A syndrome compiler must account for coordinate generation and scan -/
namespace A449_SyndromeCompiler

variable {Input : Type}

structure Compiler (specification : Input -> Prop) where
  decide : Input -> Bool
  inputSize : Input -> Nat
  constructionCost : Input -> Nat
  coordinateCount : Input -> Nat
  scanCost : Input -> Nat
  exponent : Nat
  exact : forall input, decide input = true <-> specification input
  constructionBound : forall input,
    constructionCost input <= inputSize input ^ exponent
  coordinateBound : forall input,
    coordinateCount input <= inputSize input ^ exponent
  scanBound : forall input,
    scanCost input <= inputSize input ^ exponent

theorem compiler_exact
    (specification : Input -> Prop) (compiler : Compiler specification)
    (input : Input) :
    compiler.decide input = true <-> specification input :=
  compiler.exact input

end A449_SyndromeCompiler

/-! ## 450 - Uniform polynomial syndrome compilers yield the corrected class collapse -/
namespace A450_SyndromeCollapse

variable {Language : Type}

structure UniformSyndromeCompilers
    (PClass NPClass : Set Language) where
  hasCompiler : Language -> Prop
  allNPHaveCompiler : forall language,
    language ∈ NPClass -> hasCompiler language
  compilerGivesP : forall language,
    hasCompiler language -> language ∈ PClass

theorem p_eq_np_of_uniform_syndrome_compilers
    (PClass NPClass : Set Language)
    (compilers : UniformSyndromeCompilers PClass NPClass)
    (pSubsetNP : PClass ⊆ NPClass) :
    PClass = NPClass := by
  apply Set.Subset.antisymm pSubsetNP
  intro language member
  exact compilers.compilerGivesP language
    (compilers.allNPHaveCompiler language member)

end A450_SyndromeCollapse

end PIsNPOrNot.ResearchThirtyFirst
