module

import Approximation

/-!
Exact-message axiom guards for every explicitly named Approximation declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

/-- info: 'STACS2027.sum_map_mul_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_mul_left

/-- info: 'STACS2027.sum_map_mul_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.sum_map_mul_right

/-- info: 'STACS2027.sum_map_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_congr

/-- info: 'STACS2027.sum_map_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_map_eq_zero

/-- info: 'STACS2027.two_mul_le_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_mul_le_sq_add

/-- info: 'STACS2027.four_mul_le_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.four_mul_le_sq_add

/-- info: 'STACS2027.cauchy_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cauchy_schwarz

/-- info: 'STACS2027.quadratic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.quadratic_bound

/-- info: 'STACS2027.le_six_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.le_six_of_quadratic

/-- info: 'STACS2027.two_pairCount_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.two_pairCount_add

/-- info: 'STACS2027.rounded_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.rounded_nil

/-- info: 'STACS2027.rounded_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.rounded_cons

/-- info: 'STACS2027.rounded_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.rounded_congr

/-- info: 'STACS2027.rounded_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounded_add

/-- info: 'STACS2027.rounded_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounded_mul_left

/-- info: 'STACS2027.rounded_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounded_const

/-- info: 'STACS2027.rounded_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounded_sq_eq

/-- info: 'STACS2027.expectedCost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedCost_bound

/-- info: 'STACS2027.chooseMin' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.chooseMin

/-- info: 'STACS2027.greedyFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.greedyFrom

/-- info: 'STACS2027.greedy' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.greedy

/-- info: 'STACS2027.GreedyRun' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.GreedyRun

/-- info: 'STACS2027.chooseMin_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.chooseMin_mem

/-- info: 'STACS2027.chooseMin_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.chooseMin_le

/-- info: 'STACS2027.greedyFrom_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedyFrom_run

/-- info: 'STACS2027.greedy_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_run

/-- info: 'STACS2027.GreedyRun.valid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.GreedyRun.valid

/-- info: 'STACS2027.GreedyRun.cost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.GreedyRun.cost_le

/-- info: 'STACS2027.cycleOptions_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleOptions_nonempty

/-- info: 'STACS2027.greedy_cycles_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_cycles_run

/-- info: 'STACS2027.load_le_sq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.load_le_sq

/-- info: 'STACS2027.greedy_sq_load_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_sq_load_bound

/-- info: 'STACS2027.greedy_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_cost_bound

/-- info: 'STACS2027.greedy_cost_integer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_cost_integer_bound

/-- info: 'STACS2027.pathLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.pathLoad

/-- info: 'STACS2027.pathLoad_eq_overlap_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.pathLoad_eq_overlap_sum

/-- info: 'STACS2027.cost_snoc_pathLoad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cost_snoc_pathLoad

/-- info: 'STACS2027.load_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.load_append

/-- info: 'STACS2027.load_le_load_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.load_le_load_append

/-- info: 'STACS2027.pathLoad_le_pathLoad_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.pathLoad_le_pathLoad_append

/-- info: 'STACS2027.sum_pathLoad_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_pathLoad_eq

/-- info: 'STACS2027.sum_load_eq_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_load_eq_length

/-- info: 'STACS2027.total_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.total_load

/-- info: 'STACS2027.sum_sq_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_sq_load

/-- info: 'STACS2027.sum_sq_load_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_sq_load_assignment

/-- info: 'STACS2027.Paper.cost_increase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cost_increase

/-- info: 'STACS2027.Paper.algorithm1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.algorithm1

/-- info: 'STACS2027.Paper.algorithm1_assignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.algorithm1_assignment

/-- info: 'STACS2027.Paper.total_load_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.total_load_eq

/-- info: 'STACS2027.Paper.sum_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.sum_sq_eq

/-- info: 'STACS2027.Paper.greedy_cost_le_product' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.greedy_cost_le_product

/-- info: 'STACS2027.Paper.cauchy_schwarz_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.cauchy_schwarz_loads

/-- info: 'STACS2027.Paper.greedy_load_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.greedy_load_norm

/-- info: 'STACS2027.Paper.greedy_load_norm_integer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.greedy_load_norm_integer

/-- info: 'STACS2027.Paper.greedy_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.greedy_guarantee

/-- info: 'STACS2027.Paper.greedy_guarantee_integer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.greedy_guarantee_integer

/-- info: 'STACS2027.Paper.fractional_solution_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.fractional_solution_iff

/-- info: 'STACS2027.Paper.fractional_load_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.Paper.fractional_load_eq

/-- info: 'STACS2027.Paper.relaxation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.relaxation_lower_bound

/-- info: 'STACS2027.Paper.rounding_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.rounding_guarantee

/-- info: 'STACS2027.Paper.conditional_expectation_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.conditional_expectation_average

/-- info: 'STACS2027.Paper.fixing_a_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.fixing_a_path

/-- info: 'STACS2027.Paper.algorithm2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.algorithm2

/-- info: 'STACS2027.Paper.algorithm2_assignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.algorithm2_assignment

/-- info: 'STACS2027.Paper.derandomized_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.Paper.derandomized_guarantee

/-- info: 'STACS2027.optionLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.optionLoad

/-- info: 'STACS2027.fractionalLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.fractionalLoad

/-- info: 'STACS2027.meanLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.meanLoad

/-- info: 'STACS2027.meanLoadSum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.meanLoadSum

/-- info: 'STACS2027.varianceLoad' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.varianceLoad

/-- info: 'STACS2027.expectedSquares' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.expectedSquares

/-- info: 'STACS2027.roundFrom' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.roundFrom

/-- info: 'STACS2027.conditionalRounding' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.conditionalRounding

/-- info: 'STACS2027.RoundingRun' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RoundingRun

/-- info: 'STACS2027.rounded' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.rounded

/-- info: 'STACS2027.expectedCost' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.expectedCost

/-- info: 'STACS2027.FractionalSolution' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.FractionalSolution

/-- info: 'STACS2027.relaxationObjective' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.relaxationObjective

/-- info: 'STACS2027.OptimalFractional' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OptimalFractional

/-- info: 'STACS2027.integralSolution' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.integralSolution

/-- info: 'STACS2027.CycleInstance' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CycleInstance

/-- info: 'STACS2027.CycleInstance.optionsIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.CycleInstance.optionsIn

/-- info: 'STACS2027.CycleInstance.tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.CycleInstance.tail

/-- info: 'STACS2027.indicator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.indicator

/-- info: 'STACS2027.sum_indicator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_indicator_le

/-- info: 'STACS2027.variance_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variance_bound

/-- info: 'STACS2027.variance_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.variance_sum_bound

/-- info: 'STACS2027.sum_fractionalLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_fractionalLoad

/-- info: 'STACS2027.int_sum_map_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.int_sum_map_sub

/-- info: 'STACS2027.int_sum_map_mul_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.int_sum_map_mul_left

/-- info: 'STACS2027.int_natCast_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.int_natCast_sum

/-- info: 'STACS2027.relaxationObjective_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.relaxationObjective_eq

/-- info: 'STACS2027.integralSolution_fst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.integralSolution_fst

/-- info: 'STACS2027.integralSolution_fractional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.integralSolution_fractional

/-- info: 'STACS2027.integralSolution_load' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.integralSolution_load

/-- info: 'STACS2027.fractional_le_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fractional_le_integral

/-- info: 'STACS2027.OptionsIn.choices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.OptionsIn.choices

/-- info: 'STACS2027.roundingRun_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.roundingRun_cost_bound

/-- info: 'STACS2027.OptionsIn' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.OptionsIn

/-- info: 'STACS2027.OptionsIn.tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OptionsIn.tail

/-- info: 'STACS2027.OptionsIn.head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.OptionsIn.head

/-- info: 'STACS2027.FractionalSolution.tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.FractionalSolution.tail

/-- info: 'STACS2027.FractionalSolution.head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.FractionalSolution.head

/-- info: 'STACS2027.count_le_one_of_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.count_le_one_of_nodup

/-- info: 'STACS2027.count_sq_of_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.count_sq_of_nodup

/-- info: 'STACS2027.optionLoad_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.optionLoad_le_sum

/-- info: 'STACS2027.optionLoad_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.optionLoad_eq_zero

/-- info: 'STACS2027.sum_optionLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.sum_optionLoad

/-- info: 'STACS2027.fractionalLoad_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.fractionalLoad_cons

/-- info: 'STACS2027.varianceLoad_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.varianceLoad_cons

/-- info: 'STACS2027.meanLoad_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.meanLoad_snoc

/-- info: 'STACS2027.meanLoad_cons_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.meanLoad_cons_mem

/-- info: 'STACS2027.average_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.average_identity

/-- info: 'STACS2027.expectedSquares_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedSquares_snoc

/-- info: 'STACS2027.expectedSquares_le_of_meanLoadSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedSquares_le_of_meanLoadSum_le

/-- info: 'STACS2027.average_identity_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.average_identity_sum

/-- info: 'STACS2027.expectedSquares_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedSquares_step

/-- info: 'STACS2027.RoundingRun.expectedSquares_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RoundingRun.expectedSquares_le

/-- info: 'STACS2027.RoundingRun.valid' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.RoundingRun.valid

/-- info: 'STACS2027.roundFrom_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.roundFrom_run

/-- info: 'STACS2027.conditionalRounding_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.conditionalRounding_run

/-- info: 'STACS2027.expectedSquares_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedSquares_nil

/-- info: 'STACS2027.expectedSquares_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.expectedSquares_start

/-- info: 'STACS2027.cycleEdges_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleEdges_length

/-- info: 'STACS2027.cycleInstance_of_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycleInstance_of_cycles

/-- info: 'STACS2027.rounding_options_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounding_options_nonempty

/-- info: 'STACS2027.fractional_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.fractional_length

/-- info: 'STACS2027.cycles_k_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.cycles_k_ge

/-- info: 'STACS2027.conditional_rounding_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.conditional_rounding_cost_bound

/-- info: 'STACS2027.randomized_rounding_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.randomized_rounding_cost_bound

/-- info: 'STACS2027.conditionalRounding_cycles_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.conditionalRounding_cycles_run

/-- info: 'STACS2027.RoundingRun.valid_cycles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.RoundingRun.valid_cycles

/-- info: 'STACS2027.greedy_is_assignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.greedy_is_assignment

/-- info: 'STACS2027.rounding_is_assignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.rounding_is_assignment

/-- info: 'STACS2027.weightedSum' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.weightedSum

/-- info: 'STACS2027.unitWeights' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.unitWeights

/-- info: 'STACS2027.weightedSum_nil_left' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.weightedSum_nil_left

/-- info: 'STACS2027.weightedSum_nil_right' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.weightedSum_nil_right

/-- info: 'STACS2027.weightedSum_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms STACS2027.weightedSum_cons

/-- info: 'STACS2027.weightedSum_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_congr

/-- info: 'STACS2027.weightedSum_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_add

/-- info: 'STACS2027.weightedSum_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_mul_left

/-- info: 'STACS2027.weightedSum_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_const

/-- info: 'STACS2027.weightedSum_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_le

/-- info: 'STACS2027.weightedSum_sum_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_sum_swap

/-- info: 'STACS2027.weightedSum_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_ge_min

/-- info: 'STACS2027.unitWeights_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.unitWeights_length

/-- info: 'STACS2027.unitWeights_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.unitWeights_sum

/-- info: 'STACS2027.weightedSum_zeros' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_zeros

/-- info: 'STACS2027.weightedSum_unitWeights' depends on axioms: [propext] -/
#guard_msgs in
#print axioms STACS2027.weightedSum_unitWeights
