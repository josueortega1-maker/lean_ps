# Lean improvement checkpoints — 14 October 2026

Work on an isolated local repository. Do not push until the final verification
gate is satisfied. The source snapshot is byte-for-byte equal to GitHub
`josueortega1-maker/ProbabilisticSerial` at
`8926a649fba448075de751ca0014c5dd29eaf7d5` (7 October 2026), including all 130 files.
The local baseline is `863bc38`; it is a snapshot commit, not upstream ancestry.
There are no repository-specific AGENTS.md instructions in that snapshot.

## Evaluation

The all-positive-integer-quota +3.4 expectation bound and fixed-positive-quota
log-star limit are connected to actual grouped-copy PS allocations and the
original independent uniform type-ranking law. The lower proof retains its
exceptional-event errors before taking limits. No missing process premise was
found in the public statements. The original source snapshot passed a fresh full build and all 302 audited
declarations; all 86 recorded source/config hashes and all 9 pinned dependency
revisions match. See `audit/2026-10-14/baseline-verification.json`.

The important gaps are the quota-uniform tail, the sharper quota-sensitive PS
bound in the current paper, the replica RP clock/bounds, and both general
Theorem 2 equivalences. Those are not established merely by the existing
one-copy ratio theorem. The plan below closes useful portions without labeling
the whole revised paper as formalized.

## Twelve steps

1. **Complete:** preserve and hash-check the isolated source snapshot; establish
   local commits, a checkpoint script, and recovery instructions.
2. **Complete:** reproduce Lean 4.19.0 / pinned mathlib baseline build;
   record the actual environment and any compatibility adaptation.
3. **Complete:** make source-placeholder and module-build coverage checks fail
   closed, with regression cases for missing tools/files and omitted modules.
4. **Complete:** enforce the foundational-axiom allowlist and exact public
   theorem contracts, rather than merely printing dependencies.
5. **Complete:** retain the normalized endpoint term `log(m)/q`.
6. **Complete:** prove a reusable terminal exposure inequality from endpoint
   exponential cost, including the optimized elementary envelope.
7. **Complete:** derive the unconditional finite bound
   `expectedPS ≤ 1 + sqrt(2 log(m)/q) + log(m)/q`.
8. **Complete:** prove PS expected rank tends to one whenever `log(m)/q → 0`,
   and expose the growing-market high-quota form.
9. **Complete:** retain the finite-market factor in the affine rank/exposure
   bridge, keeping the old weaker interface for compatibility.
10. **Complete:** derive uniform log-star convergence over bounded positive
    quotas, allowing quotas to vary with market size.
11. **Complete:** align current coverage and checking documentation with the
    14 October revised manuscript, distinguishing remaining obligations and
    historical records.
12. **Complete:** run the final complete build and enforced audits; independently
    review statement scope; export a source archive, diff, and full git bundle.

Each completed step gets a local commit and a numbered bundle under the sibling
`lean-checkpoints` directory. Uncompiled candidates are not completed steps.
Use `python scripts/checkpoint.py NN` after committing a completed step.

## Resume

Read this file, `git log --oneline`, and `git status --short` first. Check the
sibling `lean-checkpoints/LATEST.json`; restore a numbered bundle with
`git clone STEP.bundle restored-review`. Keep the pinned manifest. Read the
latest recorded verification result before asserting that a source revision
has compiled. Do not use historical output as proof of a changed revision.

The revised manuscript used for comparison was the supplied
`Paper_JPE_revised(1).tex`. Outdated manuscript copies are omitted from the
public edition; the README links to the paper on the author's webpage.

## Checkpoint ordering

Independent pieces were developed in parallel and committed after their own
checks passed. Step numbers identify work packages, not commit chronology.
The final combined build and axiom audit is required even though each new
mathematical module has already passed a direct Lean check.

## Final verification

The combined build, exact statement contracts, source-coverage/placeholder
checks, 23 gate regression tests and all 318 axiom footprints passed on the
clean source revision recorded in `audit/2026-10-14/verification.json`.
The final evidence/checkpoint commit changes only documentation and retained
logs; its Lean/configuration/script inputs match that verified receipt.
Independent semantic review found no material mismatch or overclaim.
A checkpoint bundle was cloned and checked with `git fsck --full`.
All 12 steps were complete within the documented scope before publication.
No remote had been pushed at this checkpoint.
