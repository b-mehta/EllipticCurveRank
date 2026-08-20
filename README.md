# ECCompute

Certified lower bounds on the Mordell-Weil rank of elliptic curves over `ℚ`, in Lean 4 on top of
mathlib.

For a Weierstrass curve `E/ℚ`, ECCompute produces a proof of `rank E(ℚ) ≥ ρ - t` that the Lean
kernel checks directly: every computational obligation reduces in the kernel via
`Lean.reflBoolTrue`.

## How it works

The bound works inside the finitely generated subgroup that the given points span, so it needs no
Mordell-Weil theorem. Given `ρ` rational points, Cremona's descent character `λ_{p,θ}` maps the
subgroup they generate to `𝔽₂^ρ`. If the resulting `ρ × ρ` matrix is invertible over `𝔽₂`, the
points are independent modulo `2·E(ℚ)`, which gives `rank ≥ ρ - t`, where `t = dim_{𝔽₂} E(ℚ)[2]`
is the rational 2-torsion dimension.

A certificate lists the `ρ` points, the `ρ` descent labels `(p, θ)`, the character matrix and its
inverse over `𝔽₂`, and a witness bounding `t`. The `certify_curve` tactic reads the points and
labels from two data files, recomputes the matrix, and discharges the referee obligations of
`hasRankGE_of_certificate`, each a kernel-reducible `Bool` check.

## Layout

* `Theory/` - the descent character and the rank-bound argument.
* `Check/` - the `Bool`-valued checkers the kernel reduces (points on the curve, label legitimacy,
  matrix inverse over `𝔽₂`, primality, 2-torsion), together with the generic kernel-reducible
  primitives they are built from, so `Fold.lean` and `F2Invert.lean` hold list and `𝔽₂` combinators
  rather than anything about curves.
* `Certificate.lean` - the certificate record the referee audits.
* `MainTheorem.lean` - `HasRankGE`, and `hasRankGE_of_certificate`, the theorem `certify_curve`
  closes.
* `Tactic/` - the `certify_curve` and `quickRfl` tactics.
* `ForMathlib/` - lemmas destined for mathlib.
* `Curves/` - certified curves, with rank records at `20`-`24` and `28`-`30` (Nagao, Nagao-Kouya,
  Fermigier, Martin-McMillen, Elkies, Elkies-Klagsbrun) and two small worked examples.
* `data/` - the points and labels each certificate reads; see `data/README.md` for the format and
  the sources.

## Building

The project uses a pinned mathlib. After cloning, fetch the cache once, then build:

```
lake exe cache get
lake build
```
