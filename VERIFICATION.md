# Verification evidence

The 14 October local review passed its final verification; evidence is in
`audit/2026-10-14/verification.json` and companion logs. The full build,
23 gate regression tests and all 318 audited declarations passed. Use its exact input hashes to identify checked
sources. The new `scripts/verify.py` command enforces all gates and records
failures as well as successes. No GitHub workflow run is claimed for this
local review.

The records below are historical and retain their original commit, manuscript
and statement scope. They do not certify later source changes.

---

# Verification record

## October 7 fixed-quota lower bound

Commit `8d6a16c47773fc0aa1e3800422739c88c110529f` passed the complete
[workflow run 37557488459](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/37557488459),
job `112586971232`, on 2026-10-07. The unchanged repository workflow completed
`lake build`, the source-placeholder rejection, and `lake env lean AxiomAudit.lean`.

All **302 audited declarations** have no dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`. In particular, the three declarations
in `FixedQuotaLowerBound` report exactly those standard principles:

- `eventually_lower_with_loss`;
- `expectedPS_div_logStar_tendsto_one`;
- `eventually_expectedPS_ge`.

The ratio theorem proves
`ReplicaPS.expectedPS m q / (StandardLogStar.logStar m : ℝ) → 1` as `m → ∞`,
for every fixed positive integer `q`. The lower-bound form gives
`(1−ε) logStar m ≤ ReplicaPS.expectedPS m q` eventually, for each `ε>0`.
These conclusions use the original PS expectation and have no additional
process, independence, or lower-bound hypotheses.

The proof constructs a uniform raw-label process preserving the original
profile law, applies actual capacity identities to exponential bands, and
converts the resulting cost into the actual allocation rank. All cutoff,
entropy, rounding, and exceptional-event estimates are discharged before the
fixed-quota limit. The existing finite upper bound completes the ratio limit.

Evidence:

- [Complete job log](audit/2026-10-07/fixed-quota-lower-verification.log).
- [All 302 footprints and exact source blobs](audit/2026-10-07/fixed-quota-lower-verification.json).
- [SHA-256 source manifest](audit/2026-10-07/fixed-quota-lower-sources.sha256).
- [Proof scope and chain](LOWER_BOUND_STATUS.md), with declarations in [PROOF_MAP.md](PROOF_MAP.md).

All **86 Lean and configuration files** were compared with the checked GitHub
tree and matched exactly. The publishing tree changes only documentation and
evidence relative to that checked tree; its Lean sources, toolchain,
dependency manifest, and workflow are identical. The manuscript remains at
SHA-256 `aaa3035ecad55a3c38de8bf88339553d668ac3ba20dd194990f01e4b7dc0f96c`.

Verification ran in GitHub Actions with Lean 4.19.0 and the pinned mathlib
4.19.0 revision. No successful local Lean run is claimed.

**The fixed-quota lower bound is complete. The full updated Theorem 1 is
still incomplete:** the quota-uniform tail and PS–RP absolute-gap threshold
equivalence remain open. This limit fixes `q` before taking `m → ∞` and does
not establish uniformity for growing quotas.


## October 7 manuscript synchronization

The manuscript now includes the October 6 draft's matching lower bound for
fixed positive integer quotas and its appendix proof. At the synchronization
commit, this was a manuscript result, not yet a Lean-verified theorem. That
commit changed no Lean source, configuration, workflow, or historical audit
record. The later fixed-quota formalization is recorded above.
[THEOREM1_STATUS.md](THEOREM1_STATUS.md) records the current manuscript hash
and coverage; the September 28 checks below retain their original scope.

## Unconditional replica +3.4 theorem and below-five corollary: tasks 1 and 2

Commit `a7141baf36e6cf1889d26af917ebf72b80d1b663` passed the complete
[workflow run 36439363780](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36439363780), job `108985529275`, on 2026-09-28.
The unchanged repository workflow completed `lake build`, its source
placeholder rejection, and `lake env lean AxiomAudit.lean`.

All **195 audited declarations** have no dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`. This includes the 30 new
audit targets and the three public declarations in `PaperReplicaInterface`:

- `expectedPS_lt_logStar_add_three_point_four`;
- `expectedPS_le_logStar_add_three_point_four`;
- `expectedPS_lt_five`.

The first two apply to every positive integer `m,q`, with exact constant
`17/5 = 3.4`. The third applies to every `1≤m≤10^80` and every positive
integer quota. Their left-hand side is the existing `ReplicaPS.expectedPS m q`,
computed from actual grouped-copy PS allocations on `m*q` independent
uniform type rankings. Their statements have no process, exposure, arrival,
independence, or numerical-certificate hypotheses.

The checked chain establishes fresh type histories, exact replay and fibers,
conditional uniformity, weighted law transfer, finite conditional rank
increments, type capacities and consumption, normalized exposure envelopes,
and the actual allocation expectation bridge. The existing analytic phase
proof and exact 21-test certificate then apply.

Evidence:

- [Full job log](audit/2026-09-28/replica-finite-proof-verification.log).
- [All 195 footprints and exact source blobs](audit/2026-09-28/replica-finite-proof-verification.json).
- [SHA-256 source manifest](audit/2026-09-28/replica-finite-proof-sources.sha256).
- [Declaration-level proof chain](audit/2026-09-28/Replica_Finite_Bound.md).

All **58 Lean and configuration files** were compared with the checked GitHub
tree and matched exactly. The publishing commit changes only documentation
and evidence relative to the checked tree: its Lean files, toolchain,
dependency manifest, and workflow are identical. At that publishing commit,
the manuscript's SHA-256 was
`8892247e32aa87c1de23cff12e6bf69f2e3ec9a409d552c28789f9a8be9e1222`.
The repository remains private.

Verification ran in GitHub Actions with Lean 4.19.0 and the pinned mathlib
4.19.0 revision. No successful local Lean run is claimed.

**The main finite expectation claim is complete for all positive integer
quotas. The full updated Theorem 1 remains incomplete:** tasks 3–5 cover the
quota-uniform tail, quota-sensitive estimates, replica RP bounds, and the
absolute-gap threshold equivalence. At this September 28 check, the later
fixed-quota lower bound was also unformalized; its October 7 check is recorded
above. The below-five result uses the exact
21-test certificate; it does not verify the manuscript's separate 1920-step
recursion or its sharper approximately 4.921241 value.

## Unconditional one-copy +3.4 theorem and below-five corollary

Commit `965abf4c2553336ade7d29ee752115ff38e71d5b` passed the complete
[workflow run 36431355568](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36431355568),
job `108958064159`, on 2026-09-28. The unchanged workflow completed
`lake build`, its placeholder rejection, and `lake env lean AxiomAudit.lean`.
All **165 declarations** printed in the audit have no dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`.

In particular, this checks the unconditional declarations

- `PaperTheoremOne.expectedPS_lt_logStar_add_three_point_four`;
- `PaperTheoremOne.expectedPS_le_logStar_add_three_point_four`;
- `PaperTheoremOne.expectedPS_lt_five`.

The first two concern every positive one-copy size `n`, with exact constant
`17/5 = 3.4`. The third concerns every `1≤n≤10^80`. Their left-hand side is
the existing `ConcreteTheoremOne.expectedPS n`, computed from actual PS
allocations and uniform preference profiles. Their statements contain no
rank, arrival or exposure hypotheses.

This completes the one-copy bridge through finite conditional permutation
counts, exact path fibers, predictable time, partial consumption, weighted
arrivals, survivor averaging, finite atomic exposure, and rank telescoping.
The public statements compose those proofs with the already checked
analytic phase bound and exact 21-test below-five certificate.

Evidence:

- [Full job log](audit/2026-09-28/one-copy-finite-proof-verification.log).
- [All 165 footprints and exact source blobs](audit/2026-09-28/one-copy-finite-proof-verification.json).
- [SHA-256 source manifest](audit/2026-09-28/one-copy-finite-proof-sources.sha256).
- [Declaration-level proof chain](audit/2026-09-28/One_Copy_Finite_Bound.md).

All **49 Lean and configuration blobs** were compared with the checked
GitHub tree and matched. The subsequent publishing commit changes only
documentation and evidence. Its proof sources, toolchain, dependency
manifest and workflow are identical to this checked commit. The repository
remains private. Verification ran in GitHub Actions; no successful local
Lean run is claimed.

At this earlier one-copy commit, the replica process/rank bridge,
quota-uniform tail and RP quota-threshold equivalence remained open.
The replica finite bridge is completed in the newer record above; current
remaining coverage is in `THEOREM1_STATUS.md`. The 21-test certificate is also
separate from the manuscript's sharper 1920-step numerical recursion.

## Earlier component check, including survivor averaging

Commit `a4537e0bc0fd4c19447295ab58b939acedce35e0` passed the full
[workflow run 36424267331](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36424267331),
job `108934251757`, on 2026-09-28. `lake build`, the unchanged placeholder
rejection step and `lake env lean AxiomAudit.lean` all succeeded.
The audit prints 145 declarations, with no dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`.

This includes every component in the following record and the additional
`FiniteSurvivor` proofs: survivor Jensen averaging, the pointwise logarithmic
envelope, and the interior and endpoint expectation closures. These lemmas
retain explicit residual-capacity and exponential-process identities that
still need to be established for the actual replica PS trace.

Evidence:

- [Full job log](audit/2026-09-28/completion-proof-verification.log).
- [Declarations and exact source blobs](audit/2026-09-28/completion-proof-verification.json).
- [SHA-256 source manifest](audit/2026-09-28/completion-proof-sources.sha256).

All 41 local Lean and configuration blobs were compared with the checked
GitHub tree and matched. The publishing commit only changes documentation
and evidence; its proof sources, toolchain, dependency manifest and workflow
are identical to this checked commit. The repository remains private.

The complete updated Theorem 1 was still open at this component commit. This verification did not
discharge the process/rank hypotheses in `PaperReplicaInterface`, extend the
load bound to arbitrary quotas, or prove the RP quota-threshold equivalence.

## September 28 analytic phase, replica interfaces and finite certificate

Commit `43c4713ac9305bb38647cf948bb006063093263d` passed
[workflow run 36423067645](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36423067645),
job `108930280494`, on 2026-09-28. The unchanged workflow completed
`lake build`, its source-placeholder rejection and
`lake env lean AxiomAudit.lean`. All 141 audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

This verifies the concrete analytic phase recurrence, stopping count and
+3.4 expectation-bound implication in `FiniteAtomicExposure`; replica static
rank concentration and dynamic reduction; type-choice persistence; the actual
replica RP definition and elementary bounds; quota scalar inequalities; the
new positive 21-test certificate; and the explicit `PaperReplicaInterface`
implications. The certificate gives the exact rational upper cost
`124982139465456527 / 25000000000000000 = 4.99928557861826108 < 5`.
It uses exact rational arithmetic and Taylor enclosures checked in Lean,
without a trusted numerical evaluator. It is separate from the manuscript's
1920-step recursion and does not verify that recursion's sharper 4.921241
value.

The complete job output is retained in
[certificate-proof-verification.log](audit/2026-09-28/certificate-proof-verification.log),
and the 141 extracted declaration footprints are in
[certificate-proof-verification.json](audit/2026-09-28/certificate-proof-verification.json).

**These are checked components, not a full formalization of updated Theorem
1.** The general finite PS conclusions still have explicit rank and arrival
hypotheses. The replica process/rank bridge, quota-uniform tail and PS–RP
threshold remain open; see `THEOREM1_STATUS.md`. Verification ran in GitHub
Actions, not in the local runtime, where Lean could not launch.

## September 28 updated-theorem component verification

The complete Lean source at commit
`27a75a9cc7ec4d0861788245b740e3fc7571b427` passed
[workflow run 36412362011](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36412362011),
job `108895323780`, on 2026-09-28:

1. `lake build` completed successfully with Lean 4.19.0.
2. The unchanged source-placeholder rejection step passed.
3. `lake env lean AxiomAudit.lean` completed successfully.
4. All 27 newly audited declarations reported exactly
   `[propext, Classical.choice, Quot.sound]`. The complete audit printed 105
   declarations with no dependency outside these three standard principles.

This covers `WeightedArrival.lean`, `ReplicaPS.lean`,
`ReplicaRevelation.lean`, `FiniteExposure.lean`, `FinitePhaseConstants.lean`,
and `PaperTheoremOne.paper_tail_all_positive`, together with the existing
development. All new modules are build roots, and their principal statements
are included in `AxiomAudit.lean`.

The actual full job log is retained in
[`updated-proof-verification.log`](audit/2026-09-28/updated-proof-verification.log).
The source/toolchain hashes are in
[`updated-proof-sources.sha256`](audit/2026-09-28/updated-proof-sources.sha256),
and the extracted new-declaration audit is in
[`updated-proof-verification.json`](audit/2026-09-28/updated-proof-verification.json).
All 29 local source and configuration blobs were also compared against the
checked GitHub tree, with no differences. Subsequent changes in the publishing
commit only add this evidence and refine coverage documentation.

These are **verified components, not a complete proof of the updated Theorem
1**. At that historical commit, the unconditional PS `+3.4` expectation,
uniform replica tail, quota threshold equivalence and below-five PS corollary
were not proved. Current coverage is listed in `THEOREM1_STATUS.md`. This earlier component check covered scalar inequalities; the later record
above covers the completed analytic phase argument with its explicit arrival
hypotheses.

Verification ran in GitHub Actions. The local Lean executable could not start
(`failed to locate application`); no successful local kernel run is claimed.

## September 28 finite-interface verification

The exact Lean source changes at commit
`b8a592ce27189dddf04cc8b11693285a541b5e65` passed the unchanged repository
[workflow run 36406816379](https://github.com/josueortega1-maker/ProbabilisticSerial/actions/runs/36406816379),
job `108877431883`, on 2026-09-28. The observed checks were:

1. `lake build`: successful with Lean 4.19.0.
2. Source placeholder scan: successful.
3. `lake env lean AxiomAudit.lean`: successful.
4. Each new declaration below reports exactly
   `[propext, Classical.choice, Quot.sound]`:
   - `ConcreteTheoremOne.expectedPS_le_phase_bound`;
   - `ConcreteTheoremOne.expectedPS_le_marketSize`;
   - `PaperTheoremOne.expectedPS_le_paperLogStar`;
   - `PaperTheoremOne.expectedPS_le_finite_min`.

The actual job output is retained in
`audit/2026-09-28/github-verification.log`. This is CI verification, not a
successful local build: the local runtime could not launch Lean. These
declarations expose the older argument's finite bounds; they do not establish
the updated +3.4 expectation theorem, quota threshold, or below-five corollary.
See `THEOREM1_STATUS.md` for semantic coverage.

## Historical September 3 record

Verified on 2026-09-03 (UTC).

## Environment

- Lean: `4.19.0`, commit `6caaee842e94`
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`
- project version: `1.1.0`

## Checks completed

1. `lake build` exited with status 0. Full output: `BUILD_OUTPUT.txt`.
2. `lake env lean AxiomAudit.lean` exited with status 0. Full output:
   `AXIOM_AUDIT.txt`.
3. The source placeholder scan exited with status 0. Output:
   `PLACEHOLDER_SCAN.txt`.
4. The final theorem
   `ProbabilisticSerial.PaperTheoremOne.paper_theorem_one_as_stated` has axiom
   footprint `[propext, Classical.choice, Quot.sound]`.
5. The literal-log-star bridge and the derivation of Knuth's formula from the
   explicit RP mechanism have the same standard axiom footprint.

The warnings in `BUILD_OUTPUT.txt` are style-linter suggestions in older proof
modules; they are not errors and do not affect kernel checking.

## SHA-256 checksums

```text
9b44ccc56aba9d22fbdda5ba9e080a8c2f9f0dc7a9931591e877abe9256e6cb8  PaperTheoremOne.lean
41d72ab35df567adf62abca8178046038f3ff5ae1cbcb32aafac01a99a23c044  RandomPriority.lean
c05df30708bce2ca380978ece5a2063b985eef005c0f9693e10c3b12244d2c6a  StandardLogStar.lean
2771f07d6758e6557fed0b18c6bd8d1a1a83594d779333a04e4a1856e0029c1f  BUILD_OUTPUT.txt
2801a2a680f278d6e70f875fed2768e8cd62c14ca9103d7bd11dfadc098fcd3b  AXIOM_AUDIT.txt
bdbc1106be51b7f0a40375f2eb2560ac200df64ce1e5434cbe6e912734e73c46  PLACEHOLDER_SCAN.txt
```

These checksums cover the three new theorem-interface files and the captured
verification outputs. Run `sha256sum -c` against this list after extracting the
archive if transport integrity matters.
