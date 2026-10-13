# Morley's trisector theorem in Metamath

A verified complex-plane proof of Morley's trisector theorem for `set.mm`,
following Alain Connes' rotation argument. The theorem is `morleyR2` in
[morley.mm](morley.mm): given a positively oriented triangle and its adjacent
interior trisector intersections, the three pairwise distances between those
intersections are equal.

The extension also contains a law of sines and supporting complex algebra,
reflection, and signed-angle lemmas. Every theorem in this release has a proof;
the extension adds no axioms. Verification checks both the extension and the
base database it reads through `$[ set.mm $]`.

## Read the result

- [Statement and hypotheses](docs/statement.md): the exact frame, orientation,
  and definedness conditions.
- [Proof](docs/proof.md): rotations, the explicit algebraic cofactor, and the
  equilateral conclusion.
- [Worksheets](mmp/README.md): readable derivations corresponding to the
  compressed proofs in `morley.mm`.
- [References](references.md): mathematical sources and verifier documentation.

This is a theorem about supplied complex points satisfying signed trisection
equations. It does not construct trisectors or their intersections, and it does
not formalize Morley for arbitrary Tarski geometry structures. Its formal
conclusion is equal distances; a separate existence or noncollapse conclusion
is not asserted. Completed helpers for a trigonometric argument are included,
but a second full proof is not part of this release.

The pinned `set.mm` already contains an unfinished Morley development for
Tarski geometry, in Thierry Arnoux's mathbox (`morleylemrneab` and its
helpers). This release is independent of it and uses none of its statements.

## Verify

Use Python 3 and metamath-knife 0.3.9. With Rust and Cargo installed, build the
pinned verifier from its public source:

```sh
cargo install --git https://github.com/metamath/metamath-knife \
  --rev 5268bcfccbbea251e9b24568938c184ee17fb604 --locked
```

From this repository, run:

```sh
python3 scripts/verify.py --fetch
```

The script downloads `set.mm` from the public revision recorded in
[set-mm-version.txt](set-mm-version.txt), checks its SHA-256, and runs:

```sh
metamath-knife --verify --jobs 4 --time morley.mm
```

Success means exit status zero and `0 diagnostics issued.` There should be no
incomplete-proof warning. Subsequent runs can omit `--fetch`. An existing base
file with the wrong hash is rejected rather than overwritten. If the verifier
is not on `PATH`, pass `--verifier /path/to/metamath-knife`.

The base database is a downloaded dependency, not part of this repository. To
work offline, supply a copy matching the recorded hash and run the script
without `--fetch`. The script checks the dependency hash; metamath-knife checks
the proofs. Worksheet files are reading aids, not inputs to this verification.

For an independent check, after supplying the pinned base, use the reference
[Metamath executable](https://github.com/metamath/metamath-exe):

```sh
metamath 'read morley.mm' 'verify proof *' 'exit'
```

Inspect the output for a successful load and `All proofs in the database were
verified`; the reference executable's exit status alone is not sufficient.
The release has been checked with Metamath 0.199.pre (29-Jan-2022) and
metamath-knife 0.3.9. Comments in `morley.mm` use ASCII so the reference
reader can load the file directly.

## Relation to upstream `set.mm`

This standalone release is not an accepted contribution to `set.mm`. The file
is formatted, compressed, and markup-checked with the reference executable, as
the [upstream contribution instructions](https://github.com/metamath/set.mm/blob/develop/CONTRIBUTING.md)
and [AI contribution guidance](https://github.com/metamath/set.mm/wiki/Contributing-guidelines-for-AI)
require. The proofs are not shortened; the worksheets show the same
derivations. Some cited theorems live in other contributors' mathboxes, so an
upstream submission still needs a review of those dependencies and of
placement.

## License and sources

Original proofs, worksheets, documentation, and the verification entry point 
licensed  under [CC0 1.0 Universal](LICENSE). 
The separately retrieved `set.mm` is distributed under its upstream CC0 license. 
Mathematical attribution is recorded in [references.md](references.md); external f
ormalizations are linked rather than bundled.

## Authorship and AI assistance

This project was prepared with AI assistance from **Claude and Codex**. The 
contributor remains responsible for the material; proof validity is checked by
the Metamath verifiers described above.

The contribution dates in `morley.mm` record preparation of this publication
on 13-Oct-2026, not the dates on which the original proofs were developed.
