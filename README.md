# ECCompute

Certified lower bounds on the Mordell-Weil rank of elliptic curves over `ℚ`, in Lean 4 on top of
mathlib.

For a Weierstrass curve `E/ℚ` and an integer `ρ`, ECCompute produces a term of `HasRankGE E ρ`:
`E(ℚ)` contains a finitely generated subgroup of rank at least `ρ`. Every check reduces in the Lean
kernel via `Lean.reflBoolTrue`.

The headline result is
[curve 302](https://elliptic-rank.icarm.cloud/curve/302) of the ICARM Elliptic Curve Rank
Leaderboard, at rank at least `31`:

```lean
def curve302 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1284727764113567728281797636015784768866707681415849262157224232063,
    560368321454261339256859338901915312332769858684945406858043869199456710681989058863306170127006181⟩

theorem curve302_hasRankGE_31 : HasRankGE curve302 31 := by
  unfold curve302
  certify_curve torsion 31 "data/curve302.txt" "data/curve302-labels.txt"
```

The points and labels are read from `data/`. `torsion 31` concedes a bound on the 2-torsion
dimension `t`; `fullTorsion` certifies `t` instead.

## How it works

mathlib has no Mordell-Weil theorem, so rather than compute the rank, we show that `ρ` given points
are independent. Cremona's descent turns each point into a short bit-vector; when those vectors are
independent, so are the points, and the rank is at least `ρ` (minus a small 2-torsion correction).
Independence of the vectors is one invertible matrix over the two-element field, which a computer
can check.

A certificate is that precomputed data: the points, the matrix and its inverse, and the torsion
bound. `certify_curve` rechecks it inside the Lean kernel, so nothing outside Lean's core is
trusted.

## Layout

* `Theory/` - the descent character and the rank-bound argument.
* `Check/` - the `Bool`-valued checkers the kernel reduces (matrix inverse over `𝔽₂`, primality,
  2-torsion, points on the curve).
* `Certify/`, `Certify.lean`, `MainTheorem.lean` - the certificate type, the assembled rank bound
  `hasRankGE_of_certificate`, and the `certify_curve` tactic.
* `Curves/` - certified curves, named by their id on the
  [ICARM Elliptic Curve Rank Leaderboard](https://elliptic-rank.icarm.cloud/): high-rank curves
  spanning rank `20` to `31` (Nagao, Fermigier, Martin-McMillen, Elkies, Elkies-Klagsbrun, and
  curve `302` at rank `31`).
* `ForMathlib/` - lemmas destined upstream (2-torsion, `padicValInt`, rational denominators).
* `data/` - the points and labels each certificate reads.

## Building

The project uses a pinned mathlib. After cloning, fetch the cache once, then build:

```
lake exe cache get
lake build
```

## Acknowledgements

The descent method is Section 2 of J. E. Cremona, *On the computation of Mordell-Weil and 2-Selmer
groups of elliptic curves*, [filter.pdf](https://johncremona.github.io/papers/filter.pdf).

Much of this work was done at the [Lean for the LMFDB](https://multramate.github.io/lean-lmfdb/)
workshop, funded by [Scalable Theorem Proving via Mathematical Databases](https://www.renaissancephilanthropy.org/scalable-theorem-proving)
through the AI for Math Fund (Renaissance Philanthropy, founding donor XTX Markets).
