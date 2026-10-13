# The rotation proof

The argument follows Connes' affine-rotation proof, as formalized by Harrison
in HOL Light. The present implementation uses explicit complex expressions
and Metamath proofs over `set.mm`. Sources are listed in
[references.md](../references.md); the precise hypotheses are in
[statement.md](statement.md).

Write the positively oriented vertex angles as `3X`, `3Y`, and `3Z`.
`ang180pos` proves their positivity and triangle angle sum, giving

```text
X + Y + Z = pi / 3.
```

Let `E = exp(2iX)`, `D = exp(2iY)`, and `G = exp(2iZ)`. Define the rotations
by their expressions:

```text
g_A(z) = A + E(z - A)
g_B(z) = B + D(z - B)
g_C(z) = C + G(z - C).
```

No new function definitions or axioms are added to the database. The notation
here abbreviates the complex expressions appearing in the formal statements.

## Reflections give the fixed points

For distinct complex points `a` and `w`, reflection in their line is expressed
as

```text
s_(a,w)(z) = a + ((w - a) / conjugate(w - a)) conjugate(z - a).
```

`cnrflinv` proves that this expression is an involution; `cnrflfix` proves
that it fixes its defining points; `cnrflsw` shows that swapping those points
does not change the expression. `cnrfl2` and `ang2exp` identify the composition
of two such reflections with the corresponding rotation.

The trisection equations express `g_A` and `g_B` as reflections whose middle
factors cancel. The remaining reflections both fix `R`. `morlemfix` proves
`g_A(g_B(R)) = R`; `morlemfix3` supplies this fact and its cyclic partners:

```text
g_A(g_B(R)) = R
g_B(g_C(P)) = P
g_C(g_A(Q)) = Q.
```

The cubed rotations have twice the full vertex angles. Their reflection
expressions telescope, giving `g_A^3 o g_B^3 o g_C^3 = identity` pointwise
in `morlemid`. Composition order matters: the rightmost map is applied first.

## The composite coefficient is primitive

Set `J = EDG`. The angle sum gives

```text
J = exp(2pi i / 3),    J^3 = 1,    J != 1.
```

These are the conclusions of `morlemj`. In particular,
`J^2 + J + 1 = 0`. The primitive-root condition is essential to the algebra
below; `J^3 = 1` alone is insufficient.

## An explicit cofactor gives the linear relation

The affine offsets and denominator factors are

```text
b1 = (1 - E)A     b2 = (1 - D)B     b3 = (1 - G)C
d1 = 1 - DG       d2 = 1 - GE       d3 = 1 - ED.
```

`morlemclr` reads the fixed-point equations without dividing:

```text
P d1 = b2 + D b3
Q d2 = b3 + G b1
R d3 = b1 + E b2.
```

The desired relation is `T = P + JQ + J^2 R = 0`. Clearing its factors with
these equations gives

```text
N = (b2 + D b3)d2 d3
  + J(b3 + G b1)d1 d3
  + J^2(b1 + E b2)d1 d2
  = T d1 d2 d3.
```

Evaluating the telescoping identity `morlemid` at zero gives the offset
identity

```text
M = (1 - E^3)A + E^3(1 - D^3)B + E^3 D^3(1 - G^3)C = 0.
```

Under `J = EDG`, `J^3 = 1`, and **`J != 1`**, the explicit cofactor is

```text
(E^2 D) N = -M.
```

The formal argument groups terms by vertex rather than performing a general
polynomial elimination. `morlemka`, `morlemkb`, and `morlemkc` prove the
coefficient identities, using `morlemcyc`:

```text
(1 - S)(S - J)(J^2 - S) = S^3 - 1.
```

`morlemlinalg` assembles the cofactor identity from these lemmas. The rotation
coefficients are nonzero because they are exponentials. Positivity and the
angle sum give nonzero `d1`, `d2`, and `d3` through `morlemdne0`. Cancelling
the nonzero multiplier yields `T = 0`. `morlemlin` discharges the algebraic
lemma's hypotheses from the geometric frame.

This argument never solves for `P`, `Q`, or `R`. It does not require the
additional condition `1 - E^3 != 0`, and its algebraic core does not assume
unit absolute values for `E`, `D`, or `G`.

## The relation forces equal distances

`morlemeqi` uses `J^3 = 1`, `J != 1`, and the linear relation to derive

```text
Q - R = J(P - Q)
P - Q = J(R - P).
```

`morlemabs1` proves `abs(J) = 1`. Taking absolute values in these equations
gives the equalities of distances required by the theorem. `morleyR2` is the
final assembly of the closure facts, `morlemj`, `morlemlin`, and `morlemeqi`.

For the detailed derivations, read [morleyR2.mmp](../mmp/morleyR2.mmp), then
[morlemlin.mmp](../mmp/morlemlin.mmp),
[morlemlinalg.mmp](../mmp/morlemlinalg.mmp), and
[morlemeqi.mmp](../mmp/morlemeqi.mmp). The complete proof bodies and their
frames are in [morley.mm](../morley.mm).

## Other completed results

`morley.mm` also proves a multiplicative law of sines (`lawsin`) through
the imaginary part of a conjugate product and its cyclic signed-area identity.
Further results include the sine triple-angle product (`sin3tprod`),
angle/exponential transport (`angexp`, `angexpadd`, `angeqd`), and the
trigonometric segment formulas (`morlemside`, `morlemsym`). These results are
included with their proofs, but this release does not claim a second complete
proof of Morley's theorem.
