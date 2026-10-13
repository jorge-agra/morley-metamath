# Statement and hypotheses

The headline theorem is `morleyR2` in [morley.mm](../morley.mm). It concerns
complex points `A`, `B`, and `C`, and supplied trisector intersections `P`,
`Q`, and `R`. The conclusion is

```text
|- ( ph -> ( ( abs ` ( R - P ) ) = ( abs ` ( P - Q ) )
                       /\ ( abs ` ( Q - R ) ) = ( abs ` ( P - Q ) ) ) )
```

## Exact hypotheses

The following block reproduces the hypotheses and disjoint-variable
conditions from `morley.mm`. The conclusion above is proved under this frame.

```metamath
${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d C x $.  $d C y $.  $d P x $.
    $d P y $.  $d Q x $.  $d Q y $.  $d R x $.  $d R y $.  $d x y $.
    morleyR2.f $e |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |->
                      ( Im ` ( log ` ( y / x ) ) ) ) $.
    morleyR2.x $e |- X = ( ( ( B - A ) F ( C - A ) ) / 3 ) $.
    morleyR2.y $e |- Y = ( ( ( C - B ) F ( A - B ) ) / 3 ) $.
    morleyR2.z $e |- Z = ( ( ( A - C ) F ( B - C ) ) / 3 ) $.
    morleyR2.a $e |- ( ph -> A e. CC ) $.
    morleyR2.b $e |- ( ph -> B e. CC ) $.
    morleyR2.c $e |- ( ph -> C e. CC ) $.
    morleyR2.p $e |- ( ph -> P e. CC ) $.
    morleyR2.q $e |- ( ph -> Q e. CC ) $.
    morleyR2.r $e |- ( ph -> R e. CC ) $.
    morleyR2.ab $e |- ( ph -> A =/= B ) $.
    morleyR2.bc $e |- ( ph -> B =/= C ) $.
    morleyR2.ca $e |- ( ph -> C =/= A ) $.
    morleyR2.ra $e |- ( ph -> R =/= A ) $.
    morleyR2.rb $e |- ( ph -> R =/= B ) $.
    morleyR2.pb $e |- ( ph -> P =/= B ) $.
    morleyR2.pc $e |- ( ph -> P =/= C ) $.
    morleyR2.qc $e |- ( ph -> Q =/= C ) $.
    morleyR2.qa $e |- ( ph -> Q =/= A ) $.
    morleyR2.o $e |- ( ph -> ( ( B - A ) F ( C - A ) ) e. ( 0 (,) _pi ) ) $.
    morleyR2.1 $e |- ( ph -> ( ( B - A ) F ( R - A ) ) = X ) $.
    morleyR2.2 $e |- ( ph -> ( ( Q - A ) F ( C - A ) ) = X ) $.
    morleyR2.3 $e |- ( ph -> ( ( C - B ) F ( P - B ) ) = Y ) $.
    morleyR2.4 $e |- ( ph -> ( ( R - B ) F ( A - B ) ) = Y ) $.
    morleyR2.5 $e |- ( ph -> ( ( A - C ) F ( Q - C ) ) = Z ) $.
    morleyR2.6 $e |- ( ph -> ( ( P - C ) F ( B - C ) ) = Z ) $.
  $}
```

## How to read the frame

`ph` is an arbitrary proposition. Deduction-form hypotheses say that the
point-closure, inequalities, orientation, and trisection equations hold under
`ph`; the conclusion holds under the same proposition.

`F` is the library's signed angle function. For nonzero complex vectors `U`
and `V`, its value is `Im(log(V / U))`, in the principal interval
`(-pi, pi]`. The vertex convention is cyclic:

```text
3X = angle(B - A, C - A)
3Y = angle(C - B, A - B)
3Z = angle(A - C, B - C).
```

The orientation condition `morleyR2.o` places the angle at `A` in `(0, pi)`.
Together with the point conditions, `ang180pos` gives positive cyclic vertex
angles whose sum is `pi`. Thus the trisected angles are positive and sum to
`pi / 3`.

The signed trisection equations put `R` on the adjacent inner rays from `A`
and `B`, `P` on those from `B` and `C`, and `Q` on those from `C` and `A`.
Using signed angles distinguishes a ray from its reflection. This is why the
frame does not add a separate unsigned-angle or convex-hull hypothesis.

The inequalities keep the vectors used by the angle function nonzero: the
outer vertices are distinct, and each auxiliary point differs from the
endpoints whose rays define it. These are explicit definedness assumptions,
not conditions silently supplied by a total angle operation.

The `$d` declarations keep the bound variables `x` and `y` distinct from
one another and from the point expressions substituted into the angle
function. They are part of the formal theorem's frame.

## Scope of the result

The conclusion is equality of the three pairwise distances, represented by
`abs` of complex differences. It does not separately assert that the
intersections exist or that these distances are positive. The intersection
points are already supplied by the hypotheses.

The displayed frame fixes positive orientation. Clockwise configurations
must be relabelled into that convention; a separate orientation-free corollary
is not included. The ambient space is the complex plane, not an arbitrary
Tarski geometry structure. No theorem connecting those two formulations is
asserted here.

The [proof explanation](proof.md) follows this exact frame. The full proof
body and all supporting theorem frames are in `morley.mm`; readable rows
for the target are in [morleyR2.mmp](../mmp/morleyR2.mmp).
