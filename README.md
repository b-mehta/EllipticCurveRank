# ECCompute

Certified lower bounds on the Mordell-Weil rank of elliptic curves over `ℚ`, in Lean 4 on top of
mathlib.

For a Weierstrass curve `E/ℚ` and an integer `ρ`, ECCompute produces a term of `HasRankGE E ρ`:
`E(ℚ)` contains a finitely generated subgroup of rank at least `ρ`. Every check reduces in the Lean
kernel via `Lean.reflBoolTrue`.

The headline result is
[curve 273](https://elliptic-rank.icarm.cloud/curve/273) of the ICARM Elliptic Curve Rank
Leaderboard, at rank at least `30`:

```lean
def curve273 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -201769035260418549083594900060734240952308696994802735114305555,
    1151107939141058565733479426024323225135665982951300586808823640527729578307228357301072889377⟩

theorem curve273_hasRankGE_30 : HasRankGE curve273 30 := by
  unfold curve273
  certify_curve torsion 23 points "data/curve273.txt" labels "data/curve273-labels.txt"
```

The points and labels are read from `data/`. `torsion 23` concedes a bound on the 2-torsion
dimension `t`; `fullTorsion` certifies `t` instead.

## How it works

mathlib has no Mordell-Weil theorem, so the argument stays inside the finitely generated subgroup
the given points span. Cremona's descent character `λ_{p,θ}` maps that subgroup to `𝔽₂^ρ`; when the
`ρ × ρ` matrix is invertible, the points are independent modulo `2·E(ℚ)`, giving `rank ≥ ρ - t` for
`t = dim_{𝔽₂} E(ℚ)[2]`.

A certificate supplies the points, the labels `(p, θ)`, the matrix and its `𝔽₂`-inverse, and a
bound on `t`. `certify_curve` recomputes the matrix and discharges the referee obligations of
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
groups of elliptic curves*, [filter.pdf](https://johncremona.github.io/papers/filter.pdf).

Much of this work was done at the [Lean for the LMFDB](https://multramate.github.io/lean-lmfdb/)
workshop, funded by [Scalable Theorem Proving via Mathematical Databases](https://www.renaissancephilanthropy.org/scalable-theorem-proving)
through the AI for Math Fund (Renaissance Philanthropy, founding donor XTX Markets).
