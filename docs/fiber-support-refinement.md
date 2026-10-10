# Fiber-Guided Support Refinement and Type Negation

The rendered English and Chinese documents are generated from
`fiber-support-refinement.tex` and `fiber-support-refinement-zh.tex`.

## Support padding

For a qualifier `phi` and finite set `X`, support padding `X.{phi}` satisfies

\[
\mathsf{FV}(X.\{\phi\})=X\cup\mathsf{FV}(\phi),\qquad
\sigma\models X.\{\phi\}
\Longleftrightarrow
(\sigma|_{\mathsf{FV}(\phi)})\models\phi.
\]

Padding changes the observed support, not the predicate after projection.

## Right-facing fiber composition

The low-level fiber connective fixes `X` and checks the substituted formula in
each `X`-fiber:

\[
r\models X\mathbin{|>}P
\Longleftrightarrow
\forall\sigma_X\in r|_X.\;
\mathsf{Fiber}(r,X,\sigma_X)\models\sigma_X(P).
\]

At formula level define

\[
P\blacktriangleright Q
\triangleq
P\land(\mathsf{FV}(P)\mathbin{|>}Q).
\]

## Relationship with separating conjunction

Separating conjunction entails both directional fiber compositions:

\[
P*Q\models P\blacktriangleright Q,
\qquad
P*Q\models Q\blacktriangleright P.
\]

For disjoint, inhabited atomic Under bindings

\[
P=x:[b_1\mid\phi],\qquad Q=y:[b_2\mid\psi],
\]

Under forces the complete canonical rectangle, so

\[
P*Q
\Longleftrightarrow
P\blacktriangleright Q
\Longleftrightarrow
Q\blacktriangleright P.
\]

In general the reverse implication fails. Let

\[
P=x:\{\mathsf{Bool}\mid\top\},\qquad
Q=y:[\mathsf{Bool}\mid\top]
\]

and let `r_diag = {(false,false),(true,true)}`. Then

\[
r_{\mathrm{diag}}\models Q\blacktriangleright P,
\qquad
r_{\mathrm{diag}}\not\models P*Q.
\]

The Under formula covers both `y` values, while each `y`-fiber contains one
safe `x`, which is enough for Over. Any Cartesian product contains an
off-diagonal point.

## Dependent type negation

Consider a function whose parameters and result are all Over base types:

\[
x:\{\mathsf{Nat}\mid\top\}\to
y:\{\mathsf{Nat}\mid x<\nu\}\to
\{\mathsf{Bool}\mid\psi(x,y,\nu)\}.
\]

The traditional translation turns each Over parameter into a disjoint Under
parameter and complements the result qualifier:

\[
x:[\mathsf{Nat}\mid\top]-*
y:[\mathsf{Nat}\mid x<\nu]-*
[\mathsf{Bool}\mid\neg\psi(x,y,\nu)].
\]

This cannot retain the dependency of `y` on `x`. Fiber refinement keeps
ordinary arrows and grows the observation set:

\[
x:[\mathsf{Nat}\mid\top]\to
y:[\mathsf{Nat}\mid\{x\}.\{x<\nu\}]\to
[\mathsf{Bool}\mid\{x,y\}.\{\neg\psi(x,y,\nu)\}].
\]

A later parameter depending on `x,y` similarly receives support padding by
`{x,y}`. Thus negation changes the Over parameters into Under coverage and the
Over result into the Under complement, while preserving dependencies by
accumulating fiber variables rather than imposing disjointness.
