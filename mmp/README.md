# Readable proof worksheets

Each `.mmp` file has the same name as its theorem label in
[morley.mm](../morley.mm). The files use the mmj2 proof-worksheet notation:
hypothesis rows begin with `h`, derived rows name their cited statements, and
`qed` gives the conclusion. Local hypotheses, disjoint-variable conditions,
and useful proof annotations are retained. `morley.mm` contains the same
derivations, with proof representation compressed and formatted separately.

Start with [morleyR2.mmp](morleyR2.mmp), the final assembly. Its main ingredients
are [morlemj.mmp](morlemj.mmp), [morlemlin.mmp](morlemlin.mmp), and
[morlemeqi.mmp](morlemeqi.mmp). The algebra inside `morlemlin` is developed in
[morlemlinalg.mmp](morlemlinalg.mmp).

`morley.mm` is authoritative. The release verification command checks its
proofs against the pinned base database; it does not verify these worksheet
files separately.
