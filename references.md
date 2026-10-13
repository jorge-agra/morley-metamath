# References

## Mathematics

- **Alain Connes**, *A new proof of Morley's theorem* (1998), pp. 43-46,
  in *Les relations entre les mathematiques et la physique theorique*.
  The affine-rotation argument followed here.
  [Author's copy](https://alainconnes.org/wp-content/uploads/morley.pdf).
- **John Harrison**, HOL Light `100/morley.ml`, especially
  `REFLECT2D_COMPOSE`, `REFLECT_ACROSS_COMPOSE_ANGLE`, `ALGEBRAIC_LEMMA`,
  `EQUILATERAL_TRIANGLE_ALGEBRAIC`, and `MORLEY`.
  The formalization used as the statement and proof-route reference. HOL Light
  uses unsigned angles and a convex-hull hypothesis; the present frame uses
  signed angles and positive orientation.
  [Source](https://github.com/jrh13/hol-light/blob/master/100/morley.ml).
- **Roland Coghetto**, *Morley's Trisector Theorem*, Mizar article `EUCLID11`
  (2015), particularly Theorems 12, 13, and 23. A reference for the completed
  trigonometric helpers. Those helpers are not a second completed target proof.
  [Article](https://mizar.uwb.edu.pl/version/current/html/euclid11.html).
- **Thierry Arnoux and SS**, the unfinished "Morley's Miracle" section of
  Thierry Arnoux's mathbox in `set.mm` (`morleylemrneab` and its helpers).
  It states the theorem for Tarski geometry structures with congruent-angle
  hypotheses. The present proof is independent of it and uses none of its
  statements.


## Formal library and verification

- **Metamath `set.mm`** supplies the logic, set theory, complex analysis, and
  angle infrastructure. The exact dependency is pinned in
  [set-mm-version.txt](set-mm-version.txt).
  [Repository](https://github.com/metamath/set.mm),
  [upstream license](https://github.com/metamath/set.mm/blob/develop/LICENSE).
- **Metamath-knife** is the verifier used by the release script.
  The tested source revision is `5268bcfccbbea251e9b24568938c184ee17fb604`
  (version 0.3.9).
  [Pinned source](https://github.com/metamath/metamath-knife/tree/5268bcfccbbea251e9b24568938c184ee17fb604).
- **The reference Metamath executable** provides an independent verifier.
  [Source and build instructions](https://github.com/metamath/metamath-exe).
- **mmj2** documents the readable proof-worksheet format used in `mmp/`.
  The release's proof verification uses `morley.mm` rather than these
  worksheets.
  [Project](https://github.com/digama0/mmj2).

External papers, programs, and formalizations are linked, not included in this
publication. Their licenses remain their own. Original publication material
is dedicated under [CC0 1.0](LICENSE).
