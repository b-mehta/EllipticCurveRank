# Certificate data

Each certified curve in `ECCompute/Curves/` reads two files from this directory: `<curve>.txt`
holding its generating points, and `<curve>-labels.txt` holding its descent labels. The
`certify_curve` tactic parses both and rebuilds the certificate from them.

## Format

`<curve>.txt` has one point per line, `x y`, in **short-model coordinates**: the point lies on
`y² = x³ + a₂x² + a₄x + a₆`, the model `certify_curve` obtains from the curve's general Weierstrass
model by completing the square and scaling to integer coefficients. Each coordinate is either an
integer or a reduced fraction `a/b`.

`<curve>-labels.txt` has one descent label per line, `p θ`: a prime `p` and an integer `θ` that is a
root of the 2-division cubic mod `p`. The certificate needs as many labels as points.

Both files carry exactly `ρ` lines, where `ρ` is the certified rank plus the 2-torsion dimension `t`.

## The curves

| files | curve | certified rank |
|---|---|---|
| `cm82` | `y² = x³ - 82x`, complex multiplication by `ℤ[i]` | 3 |
| `wiman4` | a curve of Wiman, 1945, with full rational 2-torsion | 4 |
| `nagao20` | Nagao's curve, the 1993 rank record | 20 |
| `nagaoKouya21` | the Nagao-Kouya curve, the 1994 rank record | 21 |
| `fermigier22` | Fermigier's curve, the 1997 rank record | 22 |
| `martinMcMillen23` | a Martin-McMillen curve | 23 |
| `martinMcMillen24` | the Martin-McMillen curve, the 2000 rank record | 24 |
| `elkies28` | Elkies' curve, the 2006 rank record | 28 |
| `elkiesKlagsbrun29` | the Elkies-Klagsbrun curve | 29 |
| `curve273` | curve 273 of the ICARM Elliptic Curve Rank Leaderboard | 30 |

## Provenance

`curve273.txt` holds the witness points from
[the ICARM leaderboard entry](https://elliptic-rank.icarm.cloud/curve/273), transported to the
integral short model. `martinMcMillen23-labels.txt` uses the primes `7` to `163` of §2.3 of
Cremona's *On the computation of Mordell-Weil and 2-Selmer groups*.
`elkiesKlagsbrun29-labels.txt` uses the primes `19` to `179`.

The coefficients of each curve are recorded in the module docstring of the corresponding file in
`ECCompute/Curves/`, together with the attribution above. For the remaining files, the source of the
individual point coordinates is not recorded here; the module docstrings name the curve, and the
certificate is checked from the coordinates themselves, so the points stand or fall on the kernel
check rather than on their source.
