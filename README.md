# ECCompute

Certified lower bounds on the Mordell-Weil rank of elliptic curves over `ℚ`, in Lean 4 on top of
mathlib.

For a Weierstrass curve `E/ℚ` and an integer `ρ`, ECCompute produces a proof of
`rank E(ℚ) ≥ ρ` that the Lean kernel checks directly. No `native_decide` is used: every
computational obligation reduces in the kernel via `Lean.reflBoolTrue`.

## How it works

The bound avoids Mordell-Weil (which mathlib does not have) by working inside a finitely generated
subgroup. Given `ρ` rational points, Cremona's descent character `λ_{p,θ}` maps the subgroup they
generate to `𝔽₂^ρ`. If the resulting `ρ × ρ` matrix is invertible over `𝔽₂`, the points are
independent modulo `2·E(ℚ)`, which gives `rank ≥ ρ - t` where `t = dim_{𝔽₂} E(ℚ)[2]` is the
rational 2-torsion dimension.

A certificate lists the `ρ` points, the `ρ` descent labels `(p, θ)`, the character matrix and its
inverse over `𝔽₂`, and a witness bounding `t`. The `certify_curve` tactic reads the points and
labels from two data files, recomputes the matrix, and discharges the referee obligations of
`hasRankGE_of_certificate`, each a kernel-reducible `Bool` check.

## Layout

* `Theory/` - the descent character and the rank-bound argument.
* `Check/` - the `Bool`-valued checkers the kernel reduces (matrix inverse over `𝔽₂`, primality,
  2-torsion, points on the curve).
* `Certify/` and `Certify.lean` - the certificate type and the `certify_curve` tactic.
* `Curves/` - certified curves, named by their id on the
  [ICARM Elliptic Curve Rank Leaderboard](https://elliptic-rank.icarm.cloud/): rank records from
  `20` to `30` (Nagao, Fermigier, Martin-McMillen, Elkies, Elkies-Klagsbrun, and curve `273` at
  rank `30`) and two small worked examples.
* `data/` - the points and labels each certificate reads.

## Building

The project uses a pinned mathlib. After cloning, fetch the cache once, then build:

```
lake exe cache get
lake build
```
