# ECCompute

Certified lower bounds on the Mordell-Weil rank of elliptic curves over `ℚ`, in Lean 4 on top of
mathlib.

For a Weierstrass curve `E/ℚ` and an integer `ρ`, ECCompute produces a term of `HasRankGE E ρ`,
the statement that `E(ℚ)` contains a finitely generated subgroup of rank at least `ρ`. Every
computational obligation reduces in the Lean kernel via `Lean.reflBoolTrue`, so each certificate is
trusted at the level of Lean's own type theory.

The headline result is
[curve 273](https://elliptic-rank.icarm.cloud/curve/273) of the ICARM Elliptic Curve Rank
Leaderboard, certified at rank at least `30`:

```lean
def curve273 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -201769035260418549083594900060734240952308696994802735114305555,
    1151107939141058565733479426024323225135665982951300586808823640527729578307228357301072889377⟩

theorem curve273_hasRankGE_30 : HasRankGE curve273 30 := by
  unfold curve273
  certify_curve torsion 23 points "data/curve273.txt" labels "data/curve273-labels.txt"
```

The 30 witness points from the leaderboard, transported to the integral short model, live in
`data/curve273.txt`; their descent labels in `data/curve273-labels.txt`. `torsion 23` concedes an
upper bound on the 2-torsion dimension `t`; `certify_curve fullTorsion` is the form that certifies
`t` in full.

## How it works

mathlib has no Mordell-Weil theorem, so the argument stays inside the finitely generated subgroup
the given points span. Given `ρ` rational points, Cremona's descent character `λ_{p,θ}` maps that
subgroup to `𝔽₂^ρ`. When the resulting `ρ × ρ` matrix is invertible over `𝔽₂`, the points are
independent modulo `2·E(ℚ)`, giving `rank ≥ ρ - t` where `t = dim_{𝔽₂} E(ℚ)[2]` is the rational
2-torsion dimension.

A certificate lists the `ρ` points, the `ρ` descent labels `(p, θ)`, the character matrix and its
inverse over `𝔽₂`, and a witness bounding `t`. The `certify_curve` tactic reads the points and
labels from two data files, recomputes the matrix, and discharges the referee obligations of
`hasRankGE_of_certificate`, each a kernel-reducible `Bool` check.

## Layout

* `Theory/` - the descent character and the rank-bound argument.
* `Check/` - the `Bool`-valued checkers the kernel reduces (matrix inverse over `𝔽₂`, primality,
  2-torsion, points on the curve).
* `Certify/`, `Certify.lean`, `MainTheorem.lean` - the certificate type, the assembled rank bound
  `hasRankGE_of_certificate`, and the `certify_curve` tactic.
* `Curves/` - certified curves, named by their id on the
  [ICARM Elliptic Curve Rank Leaderboard](https://elliptic-rank.icarm.cloud/): rank records from
  `20` to `30` (Nagao, Fermigier, Martin-McMillen, Elkies, Elkies-Klagsbrun, and curve `273` at
  rank `30`) and two small worked examples.
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
groups of elliptic curves*, [johncremona.github.io/papers/filter.pdf](https://johncremona.github.io/papers/filter.pdf).

Much of this work was done at the
[Lean for the LMFDB](https://multramate.github.io/lean-lmfdb/) workshop, funded through the project
[Scalable Theorem Proving via Mathematical Databases](https://www.renaissancephilanthropy.org/scalable-theorem-proving),
supported by the AI for Math Fund managed by Renaissance Philanthropy in partnership with founding
donor XTX Markets.
