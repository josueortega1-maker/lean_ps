# Finite replica PS expectation: tasks 1 and 2

The full repository build, placeholder scan and 195-declaration audit passed
at `a7141baf36e6cf1889d26af917ebf72b80d1b663` in
[workflow run 36439363780](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36439363780).
All audited dependencies are among `propext`, `Classical.choice`, and `Quot.sound`.

The public target is the existing `ReplicaPS.expectedPS m q`, on independent
uniform permutations of `m` types for `m*q` agents. A type has capacity `q`.
The deterministic model is the existing `ReplicaPS.liftedProfile`: `q`
ordered unit copies per type, grouped back into the actual type allocation.
Neither that mechanism nor the preference sample is redefined.

The exact verification status and checked source hashes are recorded in
[`VERIFICATION.md`](../../VERIFICATION.md). This proof map describes the
declarations and their mathematical roles; compilation evidence is separate.

## Task 1: actual histories, exact fibers, weighted law

All names below are in `ProbabilisticSerial.ReplicaChoiceMachine`, except
where another namespace is explicit.

| File | Declarations | Role |
| --- | --- | --- |
| `ReplicaChoiceMachine` | `history`, `queryTypes`, `previousType`, `stochasticRecording` | Observe the existing copy-level PS machine; record a fresh type query only initially or after the previous type disappears. |
| `ReplicaChoiceMachine` | `copy_rank_le_iff`, `favorite_eq_representative`, `answer_eq_representative` | A chosen type determines its preferred surviving copy, independently of its position in the type ranking. |
| `ReplicaChoiceMachine` | `revealHistory_compatible`, `compatible_of_history_eq`, `history_eq_of_compatible` | Both directions of exact replay from the fresh type observations. |
| `ReplicaChoiceMachine` | `pathFiber_eq_compatibleProfiles` | The actual finite preference fiber equals the compatible-profile set; this is an equality. |
| `ReplicaHistory` | `fresh_query_admissible` | Every new type query is nested below and excludes the earlier answers of that agent. |
| `ReplicaLaw` | `machineWeight`, `machineWeight_valid`, `machineWeight_expectation` | The transition law is the finite conditional distribution of the next actual copy answer on the exact history fiber. Unreachable histories have a deterministic extension. |
| `ReplicaLaw` | `fresh_answer_probability`, `entry_successProbability` | Apply `ReplicaRevelation.answerFiber_card_mul_available` to derive probability `1/a` for each of the `a` available types at a fresh query. |
| `ReplicaLaw` | `profile_supermartingale_expectation_le`, `profile_weightedArrivalProcess_expectation_le_one` | Transfer any tree supermartingale, including the weighted exponential arrival process, to actual replica profiles at every finite depth. |

No uniform law on permutations of the copies is used. The copy preferences
are dependent blocks, exactly as in `ReplicaPS`. Internal copy switches
have zero fresh-type arrival weight.

## Task 2: allocation rank, capacity, exposure and constants

| File | Declarations | Role |
| --- | --- | --- |
| `ReplicaRankIncrement` | `expected_rank_jump_le` | Finite swap injections give conditional expected type-rank increment at most `m/(a+1)`. The agents range over `Fin (m*q)` and preferences over `PreferenceOrder m`. |
| `ReplicaHistory` | `expected_rank_jump_at_slot_le` | Apply that rank increment bound to the exact actual path fibers. |
| `ReplicaCapacity` | `residual_eq`, `sum_residual`, `residual_pos_implies_active`, `exists_last_survivor` | Group the existing per-copy identities: residual capacity is at most `q` per type and totals `m*q*(1-t)`. |
| `ReplicaWeightedExposure` | `weightedSuccesses_eq_consumption`, `weightedCompensator_eq_exposure` | Weighted fresh type arrivals equal consumed type capacity while the type survives; the compensator is the common exposure cost. |
| `ReplicaExposureBound` | `expected_profileExposureCost_le`, `expected_profileExposureCost_endpoint_le` | Survivor averaging gives raw bounds `Phi(q*theta,1-t)` and `q*theta + log m`. |
| `ReplicaExposureBound` | `actualExposure_value`, `actualExposure_cost_le`, `actualExposure_cost_endpoint_le` | Divide the positive finite ramp measure by `q`; `FiniteExposure.phi_quota_reduction` gives quota-uniform interior and endpoint bounds. |
| `ReplicaRankAllocation` | `averageRank_eq_weighted_jumps` | Summation by parts for the actual grouped allocation rank. |
| `ReplicaExpectedRank` | `expectedPS_le_expected_exposure`, `expectedPS_le_actualExposure` | Average rank increments over exact fibers. The rank numerator `m` divided by `m*q` agents gives the required factor `1/q`. |
| `PaperReplicaInterface` | `expectedPS_lt_logStar_add_three_point_four`, `expectedPS_le_logStar_add_three_point_four` | Apply the existing finite analytic theorem to the actual normalized exposure. |
| `PaperReplicaInterface` | `expectedPS_lt_five` | Apply the existing exact 21-test certificate for every `1 <= m <= 10^80` and every positive integer `q`. |

The finite public declarations have only positivity and the displayed size
restriction. They have no rank, exposure, arrival, independence, or numerical
certificate hypotheses. `17/5` is exactly 3.4; `logStar` retains its existing
repeated-natural-log definition. The strict bound also implies the paper's
weak inequality and the earlier requested `+3.7` inequality.

The below-five result uses the exact positive 21-test cost
`124982139465456527 / 25000000000000000 = 4.99928557861826108`.
It does not identify that certificate with the manuscript's different
1920-step recursion or prove its sharper approximately 4.921241 result.

## Remaining full-Theorem-1 tasks

Tasks 3–5 remain separate: the quota-uniform tail and quota-sensitive PS
expectation, the replica RP clock representation and bounds, and the critical
regime/subsequence argument for the absolute-gap threshold equivalence.
The earlier one-copy PS/RP ratio limit is not that equivalence.
