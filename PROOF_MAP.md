> Historical declaration map, retained for the earlier proof chain. For the
> 14 October review additions and current Theorems 1–2 coverage, see
> [THEOREM1_STATUS.md](THEOREM1_STATUS.md).

# Proof map: PS theorems → Lean

The formalization contains reusable concentration lemmas and an unconditional
final theorem on the explicit uniform preference-profile sample.

This map covers the earlier one-copy asymptotic results and the finite expectation results for
all positive integer quotas, and the matching asymptotic lower bound for each
fixed positive integer quota. It does not cover all clauses of the updated Theorem 1. See [THEOREM1_STATUS.md](THEOREM1_STATUS.md) for the current
manuscript and [the finite-rank audit](audit/2026-09-28/Finite_PS_Rank_Audit.md)
for the historical baseline. The finite and lower-bound proof chains are listed below.

## Unconditional concentration code

| Mathematical step | Lean declaration |
| --- | --- |
| Finite-tree Ville inequality | `AdaptiveBernoulli.threshold_mul_hitProbability_le` |
| Upper adaptive choice deviation | `AdaptiveBernoulli.upper_deviation` |
| Lower adaptive choice deviation and positivity of `c_*` | `AdaptiveBernoulli.lower_deviation`, `AdaptiveBernoulli.lowerRate_pos` |
| Uniform finite-product MGF factorization | `UniformProduct.exp_sum_expect_eq_pow` |
| Chernoff bound | `UniformProduct.chernoff_sum` |
| Simultaneous finite-family union bound | `UniformProduct.simultaneous_chernoff` |
| Final `2^n` exponent calculation | `UniformProduct.uniform_active_rank_exponential` |
| Exact active-rank hypergeometric count | `UniformSubsetRank.firstRank_tail_probability` |
| `choose` ratio exponential estimate | `UniformSubsetRank.choose_ratio_le_exp` |
| One-agent exponential rank tail | `UniformSubsetRank.firstRank_tail_le_exp` |
| Tail-to-MGF calculation | `UniformRank.mgf_scaled_rank_le_one_add_exp` |
| Fixed-active-set product concentration | `UniformSubsetRank.fixed_active_set_sum_tail` |
| Equal-cardinality permutation orbit argument | `UniformPermutation.perm_preimage_expect_eq_powerset_expect` |
| Permutation active positions have the subset law | `UniformPermutation.activePositions_expect_eq_rankSample` |
| Exact rank tail for a uniform strict preference | `UniformPermutation.activeRank_tail_probability` |
| One common uniform permutation-profile sample | `UniformPermutation.preferenceProfileSample` |
| Simultaneous active-rank exponential bound on that profile | `UniformPermutation.uniform_active_rank_exponential_profile` |
| Event-driven continuous PS construction | `PSProcess.run`, `PSProcess.runFrom` |
| At least one exhaustion per phase | `PSProcess.activeGoods_step_ssubset` |
| At most `n` phases | `PSProcess.run_phases_length_le` |
| Total eating time is one | `PSProcess.run_totalDuration` |
| Every good is fully consumed | `PSProcess.run_consumedByGood` |
| Allocation row and column sums | `PSProcess.run_allocation_agent_sum`, `PSProcess.run_allocation_good_sum` |
| Dynamic-rank identity | `PSProcess.averageRank_eq_dynamicRank` |
| Step 3 event on the concrete process | `PSProcess.uniformRankGood_failure_probability_le` |
| Equation `rank-reduction` for the concrete process | `PSProcess.run_rankReduction` |
| Concrete deterministic `Rank(PS) ≤ n` | `PSProcess.run_averageRank_le_marketSize` |
| Preference relabelling preserves earlier reveals | `SequentialRevelation.swapProfileAt_compatible` |
| Equal conditional count for every available answer | `SequentialRevelation.answerFiber_card_eq` |
| Exact sequential-revelation probability | `SequentialRevelation.sequential_revelation_probability` |
| Valid Bernoulli entry parameter | `SequentialRevelation.entryParameter_valid` |
| Joint independence for successive displaced choices | `SequentialRevelation.sequential_revelation_joint_count` |
| Concrete PS active sets are strictly nested | `SequentialRevelation.run_phases_pairwise` |
| Conditional uniformity for a concrete PS phase | `SequentialRevelation.phase_choice_conditional_uniform` |
| Ville inequalities with full labelled history | `AdaptiveCategorical.upper_deviation`, `AdaptiveCategorical.lower_deviation` |
| Labelled transition equals permutation-profile conditional law | `StoppedChoices.sequential_revelation_matches_labelled_law` |
| Agents displaced at an exhaustion | `StoppedChoices.displacedAgents` |
| Stopped actual entry count `N_B` | `StoppedChoices.recordedEntryCountFrom` |
| Predictable volume `V_B` | `StoppedChoices.predictableVolumeFrom` |
| Event potential `H` | `StoppedChoices.displacementPotentialFrom` |
| First identity `N_B=L_B` | `StoppedChoices.recordedEntryCountFrom_eq_phaseLoad` |
| Second identity `V_B=|B|(1+H)` | `StoppedChoices.predictableVolumeFrom_eq_card_mul_one_add_potential` |
| Both `load-mean` identities on an actual PS prefix | `StoppedChoices.run_prefix_load_mean` |
| Stopped upper/lower deviation bounds | `StoppedChoices.stoppedChoice_upper_deviation`, `StoppedChoices.stoppedChoice_lower_deviation` |
| Finite union bound on a labelled adaptive tree | `LoadBound.hitProbability_finiteUnion_le_card_mul` |
| Step 1: union over all `2^n` fixed active sets | `LoadBound.allSet_potential_exponential_bound` |
| Concrete constants and `I(etaZero) > log 2` | `LoadBound.rateFunction_etaZero_gt_log_two`, `LoadBound.alphaZero_pos` |
| Existence of the paper's absolute `lambdaZero` | `LoadBound.exists_absolute_lambdaZero` |
| Entropy estimate `choose n b ≤ (e n/b)^b` | `LoadBound.choose_le_exp_mul_div_pow` |
| Pay for `choose n b` while retaining half the exponent | `LoadBound.candidate_union_exponent` |
| Ceiling case split `b lambda ≥ log n/alpha` | `LoadBound.candidateSize_mul_lambda_ge_log_div` |
| Fixed-cardinality `n⁻⁴` underload bound | `LoadBound.candidateSize_underload_le_inv_fourth` |
| Sum over active cardinalities and combined load failure | `LoadBound.candidateSize_underload_all_cardinalities`, `LoadBound.load_bound_tree_failure` |
| Fewer than `b` underloaded goods iff no bad candidate `b`-set | `LoadBound.no_bad_candidate_iff_few_underloaded` |
| Step 4 demand conclusion | `LoadBound.paper_demand_bound` |
| Supply consumed by a survivor block is at most its cardinality | `PhaseIntegral.blockConsumption_le_card` |
| One phase-block integral is at most `8/eta` | `PhaseIntegral.oneBlock_integral_le` |
| Initial interval contributes at most `lambdaZero` | `PhaseIntegral.initialBlock_integral_le` |
| Two-good tail duration and integral bounds | `PhaseIntegral.terminalBlock_duration_le`, `PhaseIntegral.terminalBlock_integral_le_of_carrier` |
| Ceiling loss and `lambdaNext ≥ exp(alpha*lambda)/4` | `PhaseIntegral.candidateSize_cast_le_two_mul_base`, `PhaseIntegral.nextLambda_ge_exp_div_four` |
| Rescaled recurrence `uNext ≥ exp u` | `PhaseIntegral.rescaledLambda_next_ge_exp`, `PhaseIntegral.activeSize_recurrence_gives_exp_scale` |
| Logarithmic threshold forces the terminal case | `PhaseIntegral.candidateBase_le_one_of_log_threshold` |
| Concrete exponential-iteration/log-star height | `PhaseIntegral.exponentialHeight` |
| Number of nonterminal blocks is at most that height | `PhaseIntegral.chain_length_le_exponentialHeight` |
| Certified deterministic eating-integral bound | `PhaseIntegral.eatingIntegral_le_of_phaseCertificate` |
| One absolute threshold for load and phase inequalities | `PhaseAdapter.exists_phaseLambdaZero`, `PhaseAdapter.phaseLambdaZero_spec` |
| Concrete simultaneous underload event and demand implication | `PhaseAdapter.ConcretePhaseLoadGood`, `PhaseAdapter.concretePhaseLoadGood_demand` |
| Initial-prefix and post-initial split | `PhaseAdapter.initial_append_postInitial`, `PhaseAdapter.postInitialPhases_ratio_gt` |
| Terminating greedy grouping and exact decomposition | `PhaseAdapter.greedyRawBlocks`, `PhaseAdapter.greedyRawBlocks_decomposition` |
| Survivor certification of every raw block | `PhaseAdapter.exists_survivorBlock_of_raw` |
| Recurrence across consecutive concrete blocks | `PhaseAdapter.rawBlockScales_chain`, `PhaseAdapter.rawBlockScales_below_chain` |
| Construct the concrete phase certificate | `PhaseAdapter.exists_phaseCertificate_of_concreteLoadGood` |
| Concrete `C(1+logStar n)` eating-integral bound | `PhaseAdapter.concrete_eatingIntegral_le_logStar` |
| Geometric lower bound for repeated exponentiation | `AsymptoticClosure.pow_two_mul_le_iteratedExp` |
| Ordinary-log upper bound on the exponential hitting time | `AsymptoticClosure.exponentialHeight_lt_log_bound` |
| Concrete `1 + psLogStar n = o(log n)` | `AsymptoticClosure.psLogStar_small_relative_to_log` |
| Harmonic numbers are asymptotic to `log n` | `AsymptoticClosure.harmonic_isEquivalent_log` |
| Knuth's exact RP formula is asymptotic to `log n` | `AsymptoticClosure.rpExpectation_isEquivalent_log` |
| History-indexed PS machine agrees with the concrete trajectory | `PSChoiceMachine.profile_machine_correspondence` |
| Genuine fresh-reveal trace is admissible | `PSChoiceMachine.profileRevealHistory_admissible` |
| Exact profile-path fiber count and weight bound | `PSChoiceMachine.pathFiber_probability_le_pathWeight` |
| Concrete path-hit probability is dominated by the labelled tree | `PSChoiceMachine.profile_hit_probability_le_hitProbability` |
| Every bad concrete phase produces a tree failure by depth `n^2` | `PSChoiceMachine.treeFailure_of_phase_bad` |
| Concrete simultaneous phase-load probability bound | `PSChoiceMachine.concrete_load_transfer` |

## Final theorem assembly

The final paragraph of the paper's proof is expanded into these checked steps.

| Mathematical step | Lean declaration |
| --- | --- |
| Define a common absolute constant | `theoremConstant` and `theoremConstant_pos` |
| Combine rank reduction with the phase integral bound | `rank_le_on_good_intersection` |
| Union-bound the two exceptional events | `good_intersection_failure` |
| Obtain equation `main-tail` | `theorem_one_tail` |
| Split the integral over a good set and its complement | `integral_le_good_plus_bad` |
| Use `Rank(PS) ≤ n` on the failure event | `theorem_one_expectation_bound` |
| Prove the failure contribution is `o(1)` | `tailError_cost_tendsto_zero` |
| Obtain equation `main-expectation` | `theorem_one_expectation_bigO` |
| Combine PS big-O, `logStar = o(log)`, and Knuth's RP asymptotic | `theorem_one_ratio` |
| Package all three conclusions with common constants | `theorem_one` |
| Concrete finite-profile good-event rank bound | `ConcreteTheoremOne.rank_le_on_concrete_good` |
| Concrete finite-profile tail from the load law transfer | `ConcreteTheoremOne.concrete_tail_of_load_transfer` |
| Concrete finite-profile expectation big-O | `ConcreteTheoremOne.expectedPS_isBigO_of_load_transfer` |
| Concrete PS/RP expected-rank ratio | `ConcreteTheoremOne.expectedPS_div_RP_tendsto_zero_of_load_transfer` |
| Package the three concrete conclusions | `ConcreteTheoremOne.concrete_theorem_one_of_load_transfer` |
| Discharge the concrete load-transfer premise | `ConcreteTheoremOne.concrete_load_transfer` |
| Expose the unconditional finite expectation estimate | `ConcreteTheoremOne.expectedPS_le_phase_bound` |
| Average the elementary rank bound | `ConcreteTheoremOne.expectedPS_le_marketSize` |
| Finite expectation bound using literal `log*` | `PaperTheoremOne.expectedPS_le_paperLogStar` |
| Minimum of that bound and market size | `PaperTheoremOne.expectedPS_le_finite_min` |
| Package all concrete conclusions without extra hypotheses | `ConcreteTheoremOne.concrete_theorem_one` |
| Define the manuscript's literal repeated-natural-log `log*` | `StandardLogStar.logStar`, `StandardLogStar.logStar_least_characterization` |
| Compare the phase counter with literal `log*` | `StandardLogStar.psLogStar_le_logStar_add_one` |
| Define random priority as serial dictatorship | `RandomPriority.randomPriorityRank`, `RandomPriority.rpExpectedRank` |
| Derive Knuth's harmonic expectation from that mechanism | `RandomPriority.rpExpectedRank_eq_knuth_formula` |
| State all conclusions with literal `log*` and actual RP | `PaperTheoremOne.paper_theorem_one` |
| Compress the finite error to `C/n^3 + exp(-c*n)` | `PaperTheoremOne.failureError_le_paper_tail_eventually`, `PaperTheoremOne.paper_theorem_one_as_stated` |

## Statement choices

- The abstract measure-theoretic assembly uses probabilities of type `ℝ≥0∞`
  and Bochner integrals. The final concrete profile assembly instead uses
  real-valued finite probabilities and `Finset` expectations.
- The market-size statement starts at `n ≥ 1`, as a market with zero agents and
  goods is outside the paper's model.
- `C n⁻³` is written `C / n^3`.
- Mathlib's standard filter notation is used for `O`, `o`, asymptotic
  equivalence, and convergence at infinity.

## End-to-end status

For the **September 3 one-copy theorem**, the labelled-tree path law is transferred to the actual ordered
initial/displaced-agent revelation trace by finite path-fiber counting. Every
violation of `ConcretePhaseLoadGood` is mapped to the combined tree-failure
event, so the former `loadTransfer` interface is discharged by
`PSChoiceMachine.concrete_load_transfer`. Therefore
`ConcreteTheoremOne.concrete_theorem_one` is end to end and has no
paper-specific hypothesis.

## Updated finite theorem: implemented proof components

| Paper step | Lean declarations |
| --- | --- |
| Predictable weighted exponential process | `AdaptiveCategorical.weightedArrivalProcess_supermartingale` |
| Finite-horizon expectation at most one | `AdaptiveCategorical.weightedArrivalProcess_expectation_le_one` |
| Nonnegative terminal-statistic transfer to actual one-copy PS profiles | `PSChoiceMachine.profile_terminal_expectation_le_sequence_sum`, `profile_weightedArrivalProcess_expectation_le_one` |
| Replica PS mechanism and capacity constraints | `ReplicaPS.favorite_type`, `allocation_agent_sum`, `allocation_type_sum`, `expectedPS_bounds` |
| Replica conditional type-choice law | `ReplicaRevelation.sequential_revelation_probability`, `sequential_revelation_joint_count` |
| Exact three-case exposure maximum | `FiniteExposure.objective_le_phi`, `phi_attained` |
| Uniformity of the normalized bound over quotas | `FiniteExposure.phi_div_antitone`, `phi_quota_reduction` |
| Logarithm of total exponential mass | `FiniteExposure.expect_log_le_zero`, `expect_le_of_log_envelope` |
| Exponential remainder comparison | `FinitePhaseConstants.remainder_half_ratio` |
| Fixed phase-growth inequalities | `FinitePhaseConstants.tower_multiplier_ge_one`, `initial_parameter_gt_one` |
| Initial interval and envelope `<2.108` | `FinitePhaseConstants.initialTime_bounds`, `initial_envelope_lt` |
| Excess scalar `<2.291` | `FinitePhaseConstants.excess_scalar_lt` |
| Remove eventual-size restriction in the one-copy tail | `PaperTheoremOne.paper_tail_all_positive` |

This second table is a component map, not an end-to-end proof of the updated
Theorem 1. The remaining quota-uniform tail and replica RP obligations are
listed in `THEOREM1_STATUS.md`; the replica finite bridge is mapped below. The phase summation is now proved on every
finite prefix by `FinitePhaseSum.phase_excess_sum_lt`; no infinite-sum exchange
is needed. See the following additional integration points.

| New step | Lean declarations |
| --- | --- |
| Concrete exponential phase growth and stopping count | `FinitePhaseGrowth.x_ge_tower`, `stopping_phase_count` |
| Finite excess sum and additive constant | `FinitePhaseSum.phase_excess_sum_lt`, `phase_assembly` |
| Derive phase inequalities from a finite exposure representation | `FiniteAtomicExposure.increment_le`, `initial_envelope`, `logarithmic_bound` |
| Survivor Jensen and endpoint expectation closure | `FiniteSurvivor.survivor_log_envelope`, `expected_compensator_le`, `expected_endpoint_compensator_le` |
| Replica rank concentration and actual eating identity | `ReplicaRank.uniform_active_rank`, `averageRank_eq_phase_sum`, `run_rankReduction` |
| Distinguish type changes from internal copy changes | `ReplicaTrace.choice_changes_iff_type_exhausted`, `retained_type_not_fresh` |
| Actual replica RP mechanism and elementary expectations | `ReplicaRP.serialTypeRankSum`, `expectedRP_bounds` |
| Quota error conversion and critical-root separation | `ReplicaAsymptoticConstants.polynomial_failure_le_agents_cube`, `critical_root_separation` |
| Positive finite certificate soundness | `FiniteArrivalCertificate.grid_domination`, `value_le_certificate` |
| Exact 21-test below-five calculation | `FiniteFiveCertificate.value_lt_five` |
| Explicit PS integration obligations | `PaperReplicaInterface.expectedPS_lt_logStar_add_of_arrival_bounds`, `expectedPS_lt_five_of_arrival_bounds` |

The last two general PS interfaces have hypotheses. They must not be cited as
a full formalization of updated Theorem 1 or its corollary.

## Unconditional one-copy finite expectation

The process hypotheses above are now discharged for the original one-copy
model. The added declarations are in namespace `PSChoiceMachine`, except
for the first and last rows below. The exact checked source is in
`VERIFICATION.md`; the full argument is described in
`audit/2026-09-28/One_Copy_Finite_Bound.md`.

| Step | Declarations |
| --- | --- |
| Conditional permutation rank jump | `PSRankIncrement.expected_rank_jump_le` |
| Exact actual history fibers | `pathFiber_eq_compatibleProfiles`, `expected_rank_jump_at_slot_le` |
| Predictable elapsed time and conservation | `roundTime_succ`, `roundSupply_conservation` |
| Partial consumption and last survivor | `sum_residual`, `residual_pos_implies_active`, `exists_last_survivor` |
| Weighted process identities | `weightedSuccesses_eq_consumption`, `weightedCompensator_eq_exposure` |
| Actual arrival estimates | `expected_profileExposureCost_le`, `expected_profileExposureCost_endpoint_le` |
| Finite atomic representation | `actualExposure_value`, `actualExposure_cost` |
| Allocation-rank summation | `averageRank_eq_weighted_jumps` |
| Unconditional expectation bridge | `expectedPS_le_expected_exposure` |
| Public finite conclusions | `PaperTheoremOne.expectedPS_le_logStar_add_three_point_four`, `expectedPS_lt_five` |

The finite arbitrary-quota extension is described next. The quota-uniform tail
and RP threshold remain open as described in `THEOREM1_STATUS.md`.

## Unconditional finite expectation for arbitrary positive quotas

Tasks 1 and 2 are complete. The public results below use
`ReplicaPS.expectedPS m q` with only positivity and the stated finite range.
The declarations are in `ReplicaChoiceMachine` unless otherwise qualified.

| Step | Declarations |
| --- | --- |
| Fresh type observations on the actual copy run | `history`, `queryTypes`, `stochasticRecording`, `revealHistory` |
| Chosen type determines its surviving copy | `favorite_eq_representative`, `answer_eq_representative` |
| Both directions of replay | `compatible_of_history_eq`, `history_eq_of_compatible` |
| Exact actual profile fibers | `pathFiber_eq_compatibleProfiles` |
| Admissibility at each fresh query | `fresh_query_admissible` |
| Exact conditional law on copy histories | `machineWeight_expectation`, `machineWeight_valid` |
| Uniform fresh type probability | `fresh_answer_probability`, `entry_successProbability` |
| Weighted process on actual replica profiles | `profile_weightedArrivalProcess_expectation_le_one` |
| Conditional type-rank increment | `ReplicaRankIncrement.expected_rank_jump_le`, `expected_rank_jump_at_slot_le` |
| Type capacity and final survivor | `residual_eq`, `sum_residual`, `residual_pos_implies_active`, `exists_last_survivor` |
| Actual weighted consumption and compensator | `weightedSuccesses_eq_consumption`, `weightedCompensator_eq_exposure` |
| Quota-uniform normalized arrival envelopes | `actualExposure_cost_le`, `actualExposure_cost_endpoint_le` |
| Actual allocation expectation bridge | `averageRank_eq_weighted_jumps`, `expectedPS_le_expected_exposure`, `expectedPS_le_actualExposure` |
| Public `log* m + 3.4` bound | `PaperReplicaInterface.expectedPS_le_logStar_add_three_point_four` |
| Public below-five corollary, every positive quota | `PaperReplicaInterface.expectedPS_lt_five` |

The existing conditional `...of_arrival_bounds` interfaces are now
instantiated by a concrete finite ramp measure from the replica trace.
Its weight at profile/round/agent `(p,r,i)` is the fresh-choice probability
`1/a` (or zero at a nonfresh query), divided by `q * |profileSample|`;
its time is the actual phase start. No process or numerical hypotheses
remain in the public finite declarations.

See [Replica_Finite_Bound.md](audit/2026-09-28/Replica_Finite_Bound.md) for the
full dependency explanation and [VERIFICATION.md](VERIFICATION.md) for exact
checked sources. The quota-uniform tail and RP equivalence remain tasks 3–5.

## Fixed-quota lower bound

| Mathematical step | Lean declaration |
| --- | --- |
| Exact mean of independent coupon unseen count | `CouponLowerBound.expected_unseenCount` |
| Nonpositive covariance and variance bound | `CouponLowerBound.unseen_pair_nonpositive_covariance`, `unseen_variance_le_mean` |
| Coupon lower tail | `CouponLowerBound.unseen_lower_tail` |
| Exact mean best available rank | `UniformLowerRank.expected_firstRank`, `expected_scaledActiveRank` |
| Uniform second moment and lower MGF | `UniformLowerRank.scaledActiveRank_second_moment_le`, `scaledActiveRank_lower_mgf` |
| Fixed-set lower concentration | `UniformLowerRank.fixed_set_lower_tail` |
| Simultaneous concentration on the actual profile sample | `ReplicaLowerRank.uniformLowerRankGood_failure_probability` |
| Pathwise lower reduction for the actual PS allocation | `ReplicaLowerRank.run_rank_lower_reduction` |
| Expected lower reduction with exceptional-event cost | `ReplicaLowerRank.expectedPS_ge_band_sub_failure` |
| Exponential bands counted by literal log-star up to a constant | `LowerBoundBands.bandIndex_le_logStar`, `logStar_le_bandIndex_add_constant` |
| Divergence of literal log-star | `LowerBoundBands.logStar_tendsto_atTop` |
| Exact raw-label coupling to the original profile law | `ReplicaRawProcess.raw_prefix_profile_marginal` |
| Uniform iid prefixes and independent restart | `UniformRawPrefixes.probability_prefix`, `ReplicaRawProcess.expected_restart` |
| Survivor raw counts bounded by agent count | `ReplicaSurvivorEntries.raw_count_survivor_le_agents` |
| Untouched types retain full quota | `ReplicaUntouched.untouched_residual_eq_quota` |
| Predictable weighted-hit averaging | `ReplicaRawProcess.expected_hits_per_type` |
| Actual capacity supplies the band-cost lower bound | `ReplicaConsumptionLower.expected_bandCost_lower` |
| Residual-capacity bound | `RawSurvivorBound.expected_residual_le` |
| Summed finite band lower bound | `ReplicaBandLower.expected_cost_ge_band_sum` |
| Raw cost as an actual PS phase sum | `ReplicaRawRankBridge.rawBandCost_eq_round_counts` |
| Simultaneous raw-prefix counts | `RawPrefixGood.countsGood_failure_probability` |
| Raw cost to original expected rank, with exceptions | `ReplicaRawCostRank.expectedPS_lower_from_rawCost` |
| Complete finite lower inequality | `FiniteLowerBound.expectedPS_ge_explicit_bands` |
| Small-set entropy and vanishing exceptions | `LowerBoundEntropy.small_family_card_le_rate`, `LowerBoundErrors.polynomial_error_tendsto` |
| Rounded bands have asymptotically full quota cost | `LowerBoundBandErrors.bandLowerValue_ge`, `bandError_tendsto` |
| Band count and polynomial horizon | `LowerBoundSchedule.logStar_le_completedBands_add`, `rawCutoff_le_horizon` |
| Eventual cutoff and error estimates | `LowerBoundMarket.eventually_market_conditions`, `weighted_exceptionalBound_le` |
| Parameters for arbitrary coefficient loss | `FixedQuotaParameters.parameters_exist` |
| Eventual leading coefficient approaching one | `FixedQuotaLowerBound.eventually_lower_with_loss` |
| Matching ratio limit for every fixed positive quota | `FixedQuotaLowerBound.expectedPS_div_logStar_tendsto_one` |
| Eventual `(1−ε) logStar m` lower bound | `FixedQuotaLowerBound.eventually_expectedPS_ge` |

The final statements use the unchanged `ReplicaPS.expectedPS` and standard
`logStar`. They require only a fixed positive integer quota (and a positive
error tolerance for the lower-bound form). See
[LOWER_BOUND_STATUS.md](LOWER_BOUND_STATUS.md) for the proof scope and
[VERIFICATION.md](VERIFICATION.md) for the checked source and audit.
