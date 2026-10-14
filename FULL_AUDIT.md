# Full follow-up audit

The independent mathematical reviews found no incorrect theorem, hidden
process assumption, or mismatch in the existing expected-rank model. They
covered the actual PS/RP mechanisms and probability laws, the finite upper
chain and certificate, the fixed-quota lower chain and parameter choices,
the legacy one-copy tail, and every new result from the 12-step review.
Declaration-level findings are in `audit/2026-10-14-full/full-audit-*.txt`.

The audit did find and repair verification gaps:

1. The actual Lean version and dependency checkouts are now checked against
   the pins before and after verification.
2. The source guard rejects Lake settings that can silently omit declared
   proof roots from a default build.
3. `AllDeclarationsAudit.lean` checks every safe project declaration, including
   unused definitions and private helpers, rather than only selected public
   theorems. All proof roots must be explicitly imported. Unsafe compiler
   implementation artifacts are excluded as roots only; transitive dependencies
   are never filtered. The allowed dependencies remain exactly `propext`,
   `Classical.choice`, and `Quot.sound`.
4. Final source checks detect newly introduced untracked Lean files, and
   `.gitignore` is included in the recorded verification inputs.
5. Verification atomically invalidates an earlier success receipt before
   starting, so an abrupt interruption cannot leave stale success evidence.
6. Clean verification now checks that the project build directory was removed,
   disables cache downloads, rejects replayed project roots, and requires fresh
   output timestamps for every root. An initial run had unexpectedly restored
   old outputs; that run is not accepted as fresh compilation evidence.

A small mathematical interface improvement defines
`ReplicaRP.profileAverageRank`, which averages priorities at a fixed profile,
and proves its expectation equals the existing `expectedRP`. This makes the
paper's random-variable convention explicit; the original expectation was
already correct. Existing theorem statements and definitions are preserved.

The reviewers independently recomputed the below-five certificate with exact
rational arithmetic: 462 kernel inequalities and 22 endpoint checks give
4.99928557861826108 < 5. Independent exact small-market enumeration checked
20,107 anonymous profiles representing 10,457,710 labeled profiles; the affine
rank bound passed. These are corroborating checks, not substitutes for Lean.

## Final verification

The accepted run checked source commit `63ba84063429830d0d1034d4ca890df3484eb3fb`
with a clean working tree. It passed all ten stages:

- All 86 proof/contract roots compiled freshly. Every root's output timestamp
  is recorded, and no project root was replayed.
- All 2,893 safe project declarations passed the whole-project dependency audit.
- All 319 selected public declarations passed the exact-footprint audit.
- All 42 verification regression tests and the literal statement contracts passed.
- The actual Lean version and all nine clean dependency revisions matched the pins.
- Final source and environment rechecks passed; all 105 recorded verification
  inputs retained their exact hashes.

`audit/2026-10-14-full/verification.json` and its companion logs contain the
complete evidence. The final evidence commit changes reports and logs only;
its proof/configuration/script hashes remain those of the verified revision.
`FINAL_ENVIRONMENT.txt` documents the separate initial cleanup used to avoid
this session's artifact-restoration behavior. No failed or replayed run is
being represented as fresh compilation.

## Scope that remains open

This is an audit of the current formalization, not a claim that the entire
revised manuscript has been formalized. The quota-uniform tail, sharper quota
bound, replica RP asymptotics, and both general Theorem 2 equivalences remain
open. The fixed-quota lower proof establishes the same asymptotic using
some different intermediate constants and cutoffs; it is not verbatim
certification of the manuscript's finite estimates. Quotas are positive
integers. The numerical certificate differs from the paper's sharper recursion.

At audit completion, the review was isolated and no changes had been pushed.
The source archive, full git bundle, and patch preserve recovery. The public
edition preserves the verified proof files and evidence; publication changes
only the accompanying documentation and omits outdated manuscript copies.
