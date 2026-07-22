import PIsNPOrNot
import ResearchNext
import ResearchThird
import ResearchFourth
import ResearchAgenda
import ResearchFifth
import ResearchSixth
import ResearchSeventh
import ResearchEighth
import ResearchNinth
import ResearchTenth
import CNFCore

-- Original residual and decomposition core
#print axioms PIsNPOrNot.A06_SeparatorDP.separator_factorization
#print axioms PIsNPOrNot.A15_ResidualAutomaton.dpAccept_correct
#print axioms PIsNPOrNot.Synthesis_ResidualCompression.ResidualModel.decide_correct

-- Lower bounds and structural barriers
#print axioms PIsNPOrNot.ResearchNext.A17_EqualityRowLowerBound.bit_state_lower_bound
#print axioms PIsNPOrNot.ResearchNext.A18_DistinguishableResiduals.state_card_lower_bound
#print axioms PIsNPOrNot.ResearchNext.A19_HittingSetBarrier.bit_hitting_set_card
#print axioms PIsNPOrNot.ResearchNext.A23_BlackBoxSpike.existential_answers_differ

-- CNF restriction and certified dispatch
#print axioms PIsNPOrNot.CNFCore.evalCNF_restrict
#print axioms PIsNPOrNot.CNFCore.branch_preserves_satisfying_assignments
#print axioms PIsNPOrNot.ResearchNext.A31_CertifiedDispatch.dispatch_correct
#print axioms PIsNPOrNot.ResearchNext.A32_CertifiedPortfolio.chosen_result_sound

-- Approaches 33-47
#print axioms PIsNPOrNot.ResearchThird.A33_CertifiedCoverage.firstAnswer_total
#print axioms PIsNPOrNot.ResearchThird.A41_EntailedLearning.add_entailed_preserves_sat
#print axioms PIsNPOrNot.ResearchThird.A42_ResolutionStep.resolution_sound
#print axioms PIsNPOrNot.ResearchThird.A46_DecompositionTree.solve_true_iff_leaf
#print axioms PIsNPOrNot.ResearchThird.A47_UniversalHybrid.hybrid_correct

-- Approaches 48-55
#print axioms PIsNPOrNot.ResearchFourth.A48_XorEncoding.xor3CNF_correct
#print axioms PIsNPOrNot.ResearchFourth.A49_RowAddition.replace_second_row
#print axioms PIsNPOrNot.ResearchFourth.A52_AffineDispatch.dispatch_correct
#print axioms PIsNPOrNot.ResearchFourth.A55_CertifiedCoverCriterion.np_subset_p_of_uniform_certified_cover

-- Approaches 56-58: set-level frontier
#print axioms PIsNPOrNot.ResearchAgenda.A56_SetLevelCollapse.p_eq_np_of_uniform_certified_cover
#print axioms PIsNPOrNot.ResearchAgenda.A57_ExactCriterion.p_eq_np_iff_uniform_poly_deciders
#print axioms PIsNPOrNot.ResearchAgenda.A58_ObstructionLocalization.exists_np_without_poly_decider_of_ne

-- Approaches 59-68: concrete SAT reductions and accounting
#print axioms PIsNPOrNot.ResearchFifth.A59_SeparatorConditioning.separator_exists
#print axioms PIsNPOrNot.ResearchFifth.A63_DavisPutnam.eliminate_one_variable
#print axioms PIsNPOrNot.ResearchFifth.A65_BoundedEliminationSchedule.work_le_length_mul_square
#print axioms PIsNPOrNot.ResearchFifth.A66_ThreeBudgetComposition.total_cost_polynomial
#print axioms PIsNPOrNot.ResearchFifth.A67_CostObstruction.expensive_leaf_of_total_exceeds
#print axioms PIsNPOrNot.ResearchFifth.A68_LogarithmicInterface.enumeration_times_polynomial

-- Approaches 69-75: private-variable peeling and cores
#print axioms PIsNPOrNot.ResearchSixth.A69_PrivateVariable.eliminate_private_variable
#print axioms PIsNPOrNot.ResearchSixth.A70_XorLeaf.xor3_solvable_for_first
#print axioms PIsNPOrNot.ResearchSixth.A72_PeelChain.PeelChain.correct
#print axioms PIsNPOrNot.ResearchSixth.A73_CoreLocalization.original_iff_core
#print axioms PIsNPOrNot.ResearchSixth.A74_SmallCoreBudget.total_cost_bound
#print axioms PIsNPOrNot.ResearchSixth.A75_CoreObstruction.expensive_core_of_total_exceeds

-- Approaches 76-90: proof-carrying AND/OR DAGs
#print axioms PIsNPOrNot.ResearchSeventh.A77_LocalValidity.eval_correct
#print axioms PIsNPOrNot.ResearchSeventh.A87_LayeredWidth.layeredNodes_le_length_mul
#print axioms PIsNPOrNot.ResearchSeventh.A88_WidthDepthBudget.width_depth_cost
#print axioms PIsNPOrNot.ResearchSeventh.A90_DagCollapseCriterion.np_subset_p_of_uniform_dag_cover

-- Approaches 91-105: concrete CNF proof trees
#print axioms PIsNPOrNot.ResearchEighth.A97_CNFShannon.sat_restrict_branch
#print axioms PIsNPOrNot.ResearchEighth.A100_DisjointDecomposition.sat_append_iff
#print axioms PIsNPOrNot.ResearchEighth.A102_CNFProofValidity.eval_correct
#print axioms PIsNPOrNot.ResearchEighth.A105_PolynomialCNFCertificate.Compiler.decide_correct

-- Approaches 106-120: minimal semantic residual states
#print axioms PIsNPOrNot.ResearchNinth.A109_StateCollisionSafety.same_state_equivalent
#print axioms PIsNPOrNot.ResearchNinth.A112_ResidualLowerBound.residual_image_card_le_state_card
#print axioms PIsNPOrNot.ResearchNinth.A113_CanonicalOptimality.canonical_image_eq
#print axioms PIsNPOrNot.ResearchNinth.A117_ResidualObstruction.state_space_exceeds_budget
#print axioms PIsNPOrNot.ResearchNinth.A120_ResidualCollapseCriterion.np_subset_p_of_uniform_residual_cover

-- Approaches 121-135: acceptable ordered-residual compiler skeleton
#print axioms PIsNPOrNot.ResearchTenth.A124_ExistentialDecision.decide_correct
#print axioms PIsNPOrNot.ResearchTenth.A125_LayerWidth.reachable_layer_bound
#print axioms PIsNPOrNot.ResearchTenth.A131_CompiledWorkBound.compiled_layer_work_bound
#print axioms PIsNPOrNot.ResearchTenth.A132_TotalCertifiedCost.total_cost_bound
#print axioms PIsNPOrNot.ResearchTenth.A134_CollapseCriterion.p_eq_np_of_uniform_compiler
#print axioms PIsNPOrNot.ResearchTenth.A135_CompilerObstruction.compiler_obstruction_of_separation
