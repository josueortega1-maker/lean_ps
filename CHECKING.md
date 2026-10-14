# Checking the formalization

## One verification command

Install the pinned Lean toolchain through `elan` and use Python 3.11 or newer.
Keep `lean-toolchain` and `lake-manifest.json` unchanged unless deliberately
upgrading the entire checked dependency set.

```bash
lake exe cache get
python3 scripts/verify.py --clean
```

The command must exit zero. It checks the actual Lean version and clean
dependency revisions, runs the source gate and its regression suite, removes
only this project's build outputs, rebuilds all proofs, and runs both
`AllDeclarationsAudit.lean` and `AxiomAudit.lean` with enforced dependency
policies. It checks that the build directory is absent before building, rejects
replayed project roots, and records fresh output timestamps for every root.
Dependency caches are retained. Omit `--clean` for incremental checks.
`TheoremContracts.lean` is a build root, so the
literal public statements and their quantifiers are checked too.

The result is `verification-output/verification.json`, with command exit codes,
source hashes, toolchain, source commit, and working-tree status. Companion
logs retain the complete output. Each run atomically writes `success: false`
before starting; an earlier successful receipt cannot survive a failed or
interrupted new check. Sources and the environment are checked again at the
end. The CI workflow runs the same verification gates and retains
its evidence as an artifact. Linter suggestions in older proofs are not
logical errors; no change is made merely to silence those suggestions.

## What each gate establishes

* The build checks the Lean statements that actually occur in the sources.
  Every tracked Lean file must be an explicit library root or the separately
  executed audit files; all libraries must be default build targets with
  build globs and facets that include every root.
  Untracked Lean files make local verification fail.
* The lexical source scan rejects visible placeholders, declared axioms, native decision
  shortcuts, unsafe code and partial definitions. It handles nested comments,
  strings, character literals and quoted identifiers; scanner and Git errors
  are failures. This lexical check supplements kernel dependency checking.
* The full Lean audit visits every safe declaration originating in all library
  roots, including private helpers and unused definitions. It catches hidden
  placeholders that a lexical scan can miss. Compiler-generated unsafe
  implementation constants are excluded only as roots; all transitive
  dependencies of safe declarations are checked without exclusions.
* The selected-public axiom gate requires exactly one footprint for every audited declaration,
  including the mandatory names in `audit/public-declarations.txt`. Only
  `propext`, `Classical.choice` and `Quot.sound` are allowed. Missing output,
  extra output, duplicates and unexpected axioms fail.
* The statement contracts reject replacing a public result by a weaker
  implication with an extra process premise. They also preserve fixed-quota
  and varying-quota quantifier distinctions. They are regression checks,
  not new mathematical claims.

Neither a clean axiom audit nor a successful build proves a theorem that is
absent from the project. Compare [THEOREM1_STATUS.md](THEOREM1_STATUS.md) with
the manuscript when assessing coverage. In particular, the one-copy ratio
limit does not establish either general Theorem 2 equivalence.

## Adding a result

1. Put its module in `lakefile.toml` and add its explicit import to
   `AllDeclarationsAudit.lean`, retaining every existing root.
2. Add the main declaration to `AxiomAudit.lean`. Add headline results to
   `audit/public-declarations.txt` and literal statement contracts to
   `TheoremContracts.lean`.
3. Run `python3 scripts/verify.py`. Associate the evidence with the exact
   checked hashes, including toolchain, manifest, configuration and scripts.
4. Update coverage only after the concrete mechanism's hypotheses have been
   discharged. Keep reusable conditional lemmas clearly distinguished.

The existing numerical `<5` certificate and the paper's sharper numerical
recursion are different. Do not describe the latter as kernel-verified.
The formal replica model currently uses integer quotas, not real capacities.

## Checkpoint and resume

After committing a completed review step:

```bash
python3 scripts/checkpoint.py 6
```

Use the appropriate step number, 1–12. The script creates and verifies a full
local git bundle and records its SHA-256 and commit. Concurrent unfinished
files are explicitly listed as excluded from that committed bundle. The
review also preserves a separate archive of unfinished work when needed.
Recover a completed step with `git clone STEP.bundle restored-review`.

The review repository begins from a verified snapshot commit, so its history
has no upstream ancestry. The final patch is relative to the exact upstream
snapshot and can be applied to an ordinary checkout. No verification or
checkpoint command pushes to a remote. Publication remains a separate action.

## Historical evidence

`VERIFICATION.md`, the dated audit folders, and the old root
`BUILD_OUTPUT.txt` / `AXIOM_AUDIT.txt` are historical records. Their scope is
limited to the source hashes they record. The root text files are the early
one-copy baseline, not the result of the current review.
