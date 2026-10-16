# Erdős 662: corrected global threshold conjecture

This project disproves the following explicitly corrected formulation of the
ambiguous printed problem: for each radius at least 1, all sufficiently large
one-separated planar sets have average short-distance degree at most the
triangular lattice's number of neighbors within that radius.

The counterexample and substantive proof are adapted from Colin Snyder /
Star Fleet. A rational oblique lattice has 128 neighbors within radius 6,
whereas the triangular lattice has 126. Exact boundary counting produces a
finite patch exceeding the proposed global bound. Separated copies produce
counterexamples above every cutoff, refuting the entire chosen conjecture.
See [NOTICE](NOTICE) for source and permission provenance.

`Challenge.lean` states the conjecture independently using only Mathlib.
Its deliberate proof hole is the standard Comparator challenge surface.
`Statement.lean` repeats those exact definitions without any theorem hole.
`Solution.lean` proves `Erdos662.not_globalThresholdConjecture` from the complete
proof in `Research/`. The proof development has no placeholders or custom
mathematical axioms. `comparator.json` compares the theorem and recursively checks all five fixed
statement definitions, with independent NanoDa replay enabled.

The Palomar project pins Lean 4.35.0-rc2 and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The same mathematical statement and
proof were first checked locally under Lean 4.33.1 before this submission port.

```sh
lake exe cache get
lake --wfail build
lake env lean AxiomAudit.lean
lake comparator --config comparator.json
```

The printed #662 statement lacks a consistent local/global normalization and
contains erroneous sample counts. This repository documents a reconstruction;
it does not claim to recover a unique historical statement. It does not
formalize the separate smallest-distance-multiplicity theorem or the other
local and strict-threshold readings.
