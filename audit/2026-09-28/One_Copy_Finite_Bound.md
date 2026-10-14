# The finite one-copy expectation bridge

This extends the original `ConcreteTheoremOne.expectedPS n`, which averages
actual PS allocations over independent uniform permutations of `Fin n`.
It neither redefines the expectation nor assumes the desired bound.
The exact verification commit and job are recorded in `VERIFICATION.md`.

## Public conclusions

In namespace `ProbabilisticSerial.PaperTheoremOne`:

```lean
expectedPS_lt_logStar_add_three_point_four (n : ℕ) (hn : 0 < n) :
  ConcreteTheoremOne.expectedPS n < (StandardLogStar.logStar n : ℝ) + 17 / 5

expectedPS_le_logStar_add_three_point_four (n : ℕ) (hn : 0 < n) :
  ConcreteTheoremOne.expectedPS n ≤ (StandardLogStar.logStar n : ℝ) + 17 / 5

expectedPS_lt_five (n : ℕ) (hn : 0 < n) (hmax : n ≤ 10 ^ 80) :
  ConcreteTheoremOne.expectedPS n < 5
```

The first theorem is slightly stronger than the requested weak inequality.
`17/5` is the exact real rational 3.4. The logarithm convention is the
existing natural-log iterated logarithm in `StandardLogStar`.

## Proof chain

All process declarations below are in `ProbabilisticSerial.PSChoiceMachine`,
unless another namespace is shown.

| Step | File and principal declaration | Substance |
| --- | --- | --- |
| Conditional rank increment | `PSRankIncrement.expected_rank_jump_le` | On compatible finite preference profiles, the mean jump to a favorite among `a` survivors is at most `n/(a+1)`. |
| Actual conditioning | `PSRankHistory.pathFiber_eq_compatibleProfiles`, `expected_rank_jump_at_slot_le` | Compatible fresh reveals generate exactly the same machine path; the rank bound applies to its exact conditional fiber. |
| Predictable clock | `PSFiniteClock.roundTime_succ`, `roundSupply_conservation` | Time is `1 - totalSupply/n`; each phase advances it by the actual eating duration. All supply is consumed by padded phase `n`. |
| Capacity | `PSFiniteCapacity.sum_residual`, `residual_pos_implies_active`, `exists_last_survivor` | Partial consumption leaves residuals in `[0,1]`, summing to `n(1-t)`. A positive residual implies survival at all earlier queries. |
| Weighted process | `PSWeightedExposure.weightedSuccesses_eq_consumption`, `weightedCompensator_eq_exposure` | For a surviving good, weighted entries equal consumed mass and the compensator equals the common exposure cost. |
| Exponential envelope | `PSExposureBound.expected_profileExposureCost_le`, `expected_profileExposureCost_endpoint_le` | The existing supermartingale and survivor Jensen lemmas give the actual interior and endpoint cost bounds. |
| Finite ramps | `PSExposureBound.actualExposure_value`, `actualExposure_cost` | Expected exposure is a positive finite ramp sum indexed by profiles, rounds and agents. |
| Rank telescoping | `PSRankAllocation.averageRank_eq_weighted_jumps` | The actual allocation rank equals the normalized sum of rank increments weighted by remaining time. |
| Expectation transfer | `PSExpectedRank.expectedPS_le_expected_exposure` | Finite fiber averaging combines the conditional rank bound and telescoping identity. |
| Analytic closure | `FiniteAtomicExposure.logarithmic_bound` | The already proved phase argument yields `logStar n + 17/5`; sizes 1 and 2 use the elementary market-size bound. |
| Finite range | `FiniteFiveCertificate.value_lt_five` | The existing exact 21-test certificate yields the below-five corollary, using `log n ≤ 80 log 10`. |

The skipped-good count in `PSRankIncrement` avoids an unproved independence
claim about endogenous available sets. For a removed good strictly between
the previous and next favorite, swapping it with any member of its union
with the survivor set gives injections into disjoint answer fibers.
Thus each skipped good has conditional probability at most `1/(a+1)`.
There are at most `n-a-1` candidates, giving
`1 + (n-a-1)/(a+1) = n/(a+1)`.

The rank bridge uses the weaker `n/a` after this count. Multiplication by the
allocation normalization `1/n` leaves the exposure weight `1/a`. Initial
choices have rank one and total exposure weight one. All later increments
are weighted by their remaining time. Terminal dummy queries have weight zero.

For the exponential estimate, the weights are predictable functions of the
existing labelled history, `max(t - queryTime, 0)`. No random survivor is
conditioned upon. The positive exponential processes are averaged over all
goods and all profiles using `FiniteSurvivor`.

## Scope still open

These declarations prove the main finite claims for the original one-copy
model. They do not prove the full updated replica theorem for `m` types,
`q` copies and `mq` agents. The replica development still requires:

1. A fresh-type history and exact replay/fiber theorem for the actual grouped
   copy process. Within-type copy switches must carry no fresh type query.
2. The corresponding rank-increment and weighted-capacity identities on
   `ReplicaPS.profileSample`, with capacity `q` and exposure normalized by `q`.
3. Quota-uniform tail estimates and the RP quota-threshold equivalence.

The one-copy uniform permutation law cannot be applied to lifted replica
copy preferences, whose ranks within a type are dependent. The existing
`PaperReplicaInterface` general-quota results retain their hypotheses.
The 4.99928557861826108 certificate also remains distinct from the paper's
sharper numerical 1920-step recursion and its approximately 4.921241 bound.
