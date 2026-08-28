#!/usr/bin/env python3
"""Generate an ECCompute rank certificate for an ICARM leaderboard curve.

Given a curve id (fetched from elliptic-rank.icarm.cloud) or a local JSON file,
this emits everything `certify_curve` needs:
  - data/curve<id>.txt         witness points on the integral short model
  - data/curve<id>-labels.txt  descent labels (an F2-independent column set)
  - Curves/Curve<id>.lean      the theorem, ready to import

It mirrors the Lean referee exactly (the `certify_curve` tactic and the integral
short-model change of variables), so the kernel is the final judge: any wrong
generated line fails `lake build`.

Model (ModelChange.intShort*):
    A2 = a1^2 + 4 a2      A4 = 16 a4 + 8 a1 a3      A6 = 64 a6 + 16 a3^2
    short model  Y^2 = X^3 + A2 X^2 + A4 X + A6
    point map    X = 4 x,  Y = 8 y + 4 a1 x + 4 a3   (general (x,y) -> short)
Descent character (CertifyEval.lambdaEval): lambda = 1 iff jacobi_symbol(a,p) != 1,
where a = alpha = x.num - theta*x.den mod p, or f'(theta)=3θ²+2A2θ+A4 if alpha≡0.
Torsion (certTorsionBound_zero): t=0 witnessed by a prime ℓ where the 2-division
cubic has no root; f(4x)-scaling makes that equivalent to f having no root mod ℓ.

Requires sympy (number theory). Usage:
    uv run --with sympy tools/gen_curve.py 273 --repo /path/to/ECCompute
    uv run --with sympy tools/gen_curve.py --json curve273.json --repo /path/to/ECCompute
    uv run --with sympy tools/gen_curve.py 273 --dry-run    # print summary, write nothing
"""
import argparse
import json
import sys
import urllib.request
from fractions import Fraction
from math import isqrt
from pathlib import Path
from sympy import Poly, QQ, Rational, Symbol, ZZ, jacobi_symbol, primerange

_X = Symbol("X")


# ---------- curve model ----------
class Curve:
    def __init__(self, ainvs, points):
        self.a1, self.a2, self.a3, self.a4, self.a6 = ainvs
        self.A2 = self.a1 * self.a1 + 4 * self.a2
        self.A4 = 16 * self.a4 + 8 * self.a1 * self.a3
        self.A6 = 64 * self.a6 + 16 * self.a3 * self.a3
        b, c, d = self.A2, self.A4, self.A6
        self.disc = 18 * b * c * d - 4 * b**3 * d + b * b * c * c - 4 * c**3 - 27 * d * d
        if self.disc == 0:
            raise SystemExit("gen_curve: short model is singular (disc = 0)")
        self.short = []  # (xnum, xden, ynum, yden)
        for (x, y) in points:
            if (y * y + self.a1 * x * y + self.a3 * y
                    != x**3 + self.a2 * x * x + self.a4 * x + self.a6):
                raise SystemExit("gen_curve: a witness point is not on the general curve")
            X = 4 * x
            Y = 8 * y + 4 * self.a1 * x + 4 * self.a3
            if Y * Y != X**3 + self.A2 * X * X + self.A4 * X + self.A6:
                raise SystemExit("gen_curve: short-model transform failed (internal bug)")
            if X.denominator != isqrt(X.denominator) ** 2:
                raise SystemExit("gen_curve: x-denominator is not a perfect square")
            self.short.append((X.numerator, X.denominator, Y.numerator, Y.denominator))

    def f(self, t):
        return t**3 + self.A2 * t * t + self.A4 * t + self.A6

    def roots_mod(self, p):
        return [t for t in range(p) if self.f(t) % p == 0]

    def lam(self, p, theta, xnum, xden):
        """The descent character λ_{p,θ} at the point x = xnum/xden: 0 when the relevant residue
        is a square mod p (Jacobi symbol 1), else 1. Mirrors CertifyEval.lambdaEval."""
        if xden % p == 0:
            return 0
        alpha = (xnum - theta * xden) % p
        a = (3 * theta * theta + 2 * self.A2 * theta + self.A4) if alpha == 0 else alpha
        return 0 if jacobi_symbol(a, p) == 1 else 1


def col_bits(curve, p, theta):
    """The (p, θ) descent column as a bitmask: bit i is set iff λ_{p,θ} is 1 on witness point i."""
    v = 0
    for i, (xn, xd, _, _) in enumerate(curve.short):
        if curve.lam(p, theta, xn, xd):
            v |= (1 << i)
    return v


def padd(P, Q, A2, A4):
    """Group law on the short model Y^2 = X^3 + A2 X^2 + A4 X + A6; points are Fraction
    pairs, the identity is None."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and y1 + y2 == 0:
        return None
    lam = (3 * x1 * x1 + 2 * A2 * x1 + A4) / (2 * y1) if P == Q else (y2 - y1) / (x2 - x1)
    x3 = lam * lam - A2 - x1 - x2
    return (x3, lam * (x1 - x3) - y1)


def f2_kernel(curve, prime_cap):
    """Basis of the F2-relations among the witness points that every descent column up to
    `prime_cap` misses, together with the image dimension (image rank = number of pivots)."""
    n = len(curve.short)
    basis = []                          # (pivot_bit, mask) in reduced row-echelon form
    for p in primerange(5, prime_cap):
        if curve.disc % p == 0:
            continue
        for th in curve.roots_mod(p):
            r = col_bits(curve, p, th)
            for pb, m in basis:
                if (r >> pb) & 1:
                    r ^= m
            if r:
                pb = r.bit_length() - 1
                basis = [(q, (mm ^ r) if (mm >> pb) & 1 else mm) for q, mm in basis]
                basis.append((pb, r))
    pivots = {pb for pb, _ in basis}
    kernel = []
    for fb in (i for i in range(n) if i not in pivots):
        v = 1 << fb
        for pb, m in basis:
            if bin((m & ~(1 << pb)) & v).count("1") & 1:
                v |= 1 << pb
        kernel.append(v)
    return len(basis), kernel


def rational_sqrt(q):
    """Exact rational square root of a nonnegative Fraction, or None if it is not a square."""
    if q < 0:
        return None
    sn, sd = isqrt(q.numerator), isqrt(q.denominator)
    if sn * sn == q.numerator and sd * sd == q.denominator:
        return Fraction(sn, sd)
    return None


def halve(Q, A2, A4, A6):
    """A rational point R with 2R = Q, or None if Q is not in 2E(Q). The X-coordinates of
    such R are the rational roots of the halving quartic."""
    if Q is None:
        return None
    xQ = Rational(Q[0].numerator, Q[0].denominator)
    A2r, A4r, A6r = (Rational(v) for v in (A2, A4, A6))
    fX = _X**3 + A2r * _X**2 + A4r * _X + A6r
    g = (3 * _X**2 + 2 * A2r * _X + A4r)**2 - 4 * fX * (2 * _X + A2r + xQ)
    for root in Poly(g, _X, domain=QQ).ground_roots():
        xR = Fraction(int(root.p), int(root.q))
        yR = rational_sqrt(xR**3 + A2 * xR**2 + A4 * xR + A6)
        if yR is None:
            continue
        for R in ((xR, yR), (xR, -yR)):
            if padd(R, R, A2, A4) == Q:
                return R
    return None


def saturate(curve, prime_cap=15000, max_cap=200000, max_rounds=60):
    """2-saturate the witness points in place: while some F2-combination of the points is in
    2E(Q) (so no descent character separates it), replace one summand by the half. Starts at
    a small prime cap and escalates only when a relation is not yet resolved, so the common
    case stays fast. Returns True once the descent images reach full F2 rank."""
    A2, A4, A6 = curve.A2, curve.A4, curve.A6
    cap = prime_cap
    for _ in range(max_rounds):
        _, kernel = f2_kernel(curve, cap)
        if not kernel:
            return True
        mask = min(kernel, key=lambda m: bin(m).count("1"))
        idxs = [i for i in range(len(curve.short)) if (mask >> i) & 1]
        Q = None
        for i in idxs:
            xn, xd, yn, yd = curve.short[i]
            Q = padd(Q, (Fraction(xn, xd), Fraction(yn, yd)), A2, A4)
        R = halve(Q, A2, A4, A6)
        if R is None:                       # relation not in 2E at this cap: scan further
            if cap >= max_cap:
                return False
            cap = min(cap * 3, max_cap)
            continue
        curve.short[idxs[0]] = (R[0].numerator, R[0].denominator, R[1].numerator, R[1].denominator)
    return False


def select_labels(curve, prime_cap=100000):
    """Greedy F2-independent column set, scanning primes ascending, roots ascending.
    Matches the ordering the committed data files were built with."""
    n = len(curve.short)
    basis, chosen = [], []
    for p in primerange(5, prime_cap):
        if len(chosen) >= n:
            break
        if curve.disc % p == 0:
            continue
        for th in curve.roots_mod(p):
            red = col_bits(curve, p, th)
            for b in basis:
                red = min(red, red ^ b)      # reduce mod the running F2 basis
            if red != 0:
                basis.append(red)
                basis.sort(reverse=True)
                chosen.append((p, th))
    return chosen


def first_prime(curve, cap, pred):
    """The least prime `q < cap` of good reduction (`disc % q != 0`) satisfying `pred(q)`."""
    return next((q for q in primerange(5, cap) if curve.disc % q != 0 and pred(q)), None)


def torsion_prime(curve, cap=1000):
    # For t=0 the 2-division cubic is irreducible over ℚ, so a positive density of primes have no
    # root; a witness turns up well under 1000. None here means the curve likely has t>0.
    return first_prime(curve, cap, lambda q: not curve.roots_mod(q))


def find_integer_root(A2, A4, A6):
    """One integer root of the monic cubic X^3+A2 X^2+A4 X+A6, or None. Monic, so every
    rational root is an integer; polynomial factorization over ℤ finds it regardless of the
    size of A6."""
    if A6 == 0:
        return 0
    roots = Poly(_X ** 3 + A2 * _X ** 2 + A4 * _X + A6, _X, domain=ZZ).ground_roots()
    return int(next(iter(roots))) if roots else None


def two_torsion(A2, A4, A6):
    """Rational 2-torsion of the short model Y^2 = X^3+A2 X^2+A4 X+A6. Returns (t, roots):
    t = dim_F2 E(Q)[2] in {0,1,2}; roots = short-model x-coordinates of the nonzero rational
    2-torsion (0, 1, or 3 of them). A monic cubic has 0, 1, or 3 rational roots, never 2."""
    R0 = find_integer_root(A2, A4, A6)
    if R0 is None:
        return 0, []
    b = A2 + R0
    c = A4 + R0 * b                          # cofactor  X^2 + b X + c
    D = b * b - 4 * c
    if D < 0:
        return 1, [R0]
    s = isqrt(D)
    if s * s == D:                           # cofactor splits -> full 2-torsion
        return 2, sorted([R0, (-b + s) // 2, (-b - s) // 2])
    return 1, [R0]


def cofactor_witness_prime(b, c, curve, cap=10000):
    """Prime ℓ where the cofactor quadratic X^2+bX+c has no root (its discriminant is a
    non-residue), witnessing that the other two 2-torsion points are irrational (t=1)."""
    D = b * b - 4 * c
    return first_prime(curve, cap, lambda q: jacobi_symbol(D, q) == -1)


# ---------- io ----------
def frac(n, den):
    return str(n) if den == 1 else f"{n}/{den}"


def j_invariant(a1, a2, a3, a4, a6):
    """The j-invariant c₄³/Δ of the general model ⟨a₁,…,a₆⟩, as a reduced Fraction."""
    a1, a2, a3, a4, a6 = map(Fraction, (a1, a2, a3, a4, a6))
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    disc = -b2 * b2 * b8 - 8 * b4**3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    return c4**3 / disc


def j_lit(j):
    """The j-invariant as a Lean ℚ literal: an integer, or `num / den`."""
    return str(j.numerator) if j.denominator == 1 else f"{j.numerator} / {j.denominator}"


def gate(decl):
    """A declaration (its docstring and body), prefixed with `set_option linter.style.longLine
    false in` when any line exceeds 100 columns — an unbreakable numeral in a def, a tactic line,
    or a theorem statement."""
    if any(len(line) > 100 for line in decl.splitlines()):
        return f"set_option linter.style.longLine false in\n{decl}"
    return decl


def j_theorem(cid, jinv):
    """The `j`-invariant theorem. Short statements stay on one line; longer ones move the
    proof to its own line, and only a statement whose numeral overflows keeps the longLine
    suppression."""
    doc = f"/-- The `j`-invariant of curve {cid}. -/\n"
    head = f"public theorem curve{cid}_j : curve{cid}.j = {jinv} :="
    proof = "j_eq_iff.mpr (by decide +kernel)"
    if len(f"{head} {proof}") <= 100:
        return doc + f"{head} {proof}"
    return gate(doc + f"{head}\n  {proof}")


def lean_int(n):
    """A Lean integer literal that parses at `term:max`: negatives need parentheses."""
    return f"({n})" if n < 0 else str(n)


def load(args):
    if args.json:
        with open(args.json) as fh:
            return json.load(fh)
    url = f"https://elliptic-rank.icarm.cloud/curve/{args.id}.json"
    with urllib.request.urlopen(url, timeout=30) as resp:
        return json.load(resp)


def weier_eq(a1, a2, a3):
    """A human-readable Weierstrass equation string (`y² + a₁xy + a₃y = x³ + a₂x² + a₄·x + a₆`,
    with zero terms dropped) for the generated module docstring."""
    def term(coef, mono):
        if coef == 0:
            return ""
        sign = " + " if coef > 0 else " - "
        mag = "" if abs(coef) == 1 else str(abs(coef))
        return f"{sign}{mag}{mono}"
    lhs = "y²" + term(a1, "xy") + term(a3, "y")
    rhs = "x³" + term(a2, "x²") + " + a₄·x + a₆"
    return f"{lhs} = {rhs}"


def def_block(cid, a):
    """The inlined `def curve<id>` matching the curve-abbrev design: one line if it fits
    under 100 columns, else break after `:=`, else split `a₆` onto its own line."""
    tup = f"⟨{a[0]}, {a[1]}, {a[2]}, {a[3]}, {a[4]}⟩"
    head = f"@[expose] public def curve{cid} : WeierstrassCurve ℚ :="
    if len(f"{head} {tup}") <= 100:
        return f"{head} {tup}"
    if len(f"  {tup}") <= 100:
        return f"{head}\n  {tup}"
    return f"{head}\n  ⟨{a[0]}, {a[1]}, {a[2]}, {a[3]},\n    {a[4]}⟩"


def coeff_block(a4, a6, width=76):
    """Docstring lines for the two big coefficients, wrapped under 100 columns like
    the committed curve files (continuation lines aligned under the digits)."""
    def wrap(name, val, suffix=""):
        s = str(val)
        head, rest = s[:width], s[width:]
        lines = [f"  `{name} = {head}`"]
        pad = " " * (len(name) + 3)  # align under the char after "name = "
        while rest:
            lines.append(f"  `{pad}{rest[:width]}`")
            rest = rest[width:]
        lines[-1] += suffix
        return lines
    return "\n".join(wrap("a₄", a4, "   and") + wrap("a₆", a6))


def main():
    ap = argparse.ArgumentParser(description="Generate an ECCompute rank certificate for a curve.")
    ap.add_argument("id", nargs="?", help="ICARM leaderboard curve id")
    ap.add_argument("--json", help="read the curve from a local JSON file")
    ap.add_argument("--repo", default=".", help="repo root to write into (default .)")
    ap.add_argument("--dry-run", action="store_true", help="print summary, write no files")
    args = ap.parse_args()
    if not args.id and not args.json:
        ap.error("give a curve id or --json")

    data = load(args)
    cid = args.id or str(data.get("id"))
    ainvs = [int(a) for a in data["ainvs"]]
    if len(ainvs) != 5:
        raise SystemExit("gen_curve: expected 5 a-invariants")
    points = [(Fraction(p[0]), Fraction(p[1])) for p in data["points"]]
    claimed = data.get("rank_lower_bound")

    curve = Curve(ainvs, points)
    ngen = len(curve.short)
    t, roots = two_torsion(curve.A2, curve.A4, curve.A6)

    # The certificate carries rho = rank + t points: the generators plus the rational
    # 2-torsion points (root, 0), whose descent images are F2-independent of the rest.
    if t == 1:
        tors_pts = [roots[0]]
    elif t == 2:
        tors_pts = sorted(roots)[-2:]        # any two of the three are independent in E[2]
    else:
        tors_pts = []
    for r in tors_pts:
        curve.short.append((r, 1, 0, 1))

    # Leaderboard generators can span an index-2^k subgroup; saturate so the descent sees
    # the full rank rather than rank - k.
    saturate(curve)

    labels = select_labels(curve)
    rho = len(curve.short)
    # select_labels only keeps F2-independent columns, so the matrix rank is exactly their count.
    achieved = len(labels)
    rank_goal = achieved - t

    data_args = f'"data/curve{cid}.txt" "data/curve{cid}-labels.txt"'
    ell0 = ellq = None
    if t == 0:
        ell0 = torsion_prime(curve)
        tactic = f'certify_curve torsion {ell0} {data_args}'
    elif t == 1:
        R0 = roots[0]
        b, c = curve.A2 + R0, curve.A4 + R0 * (curve.A2 + R0)
        ellq = cofactor_witness_prime(b, c, curve)
        tactic = f'certify_curve oneTorsion {lean_int(R0)} {ellq} {data_args}'
    else:
        tactic = f'certify_curve fullTorsion {data_args}'

    tdesc = {0: "trivial", 1: "one rational point", 2: "full (ℤ/2)²"}[t]
    print(f"curve {cid}: {ngen} generators + {len(tors_pts)} torsion = "
          f"{rho} points, claimed rank {claimed}")
    print(f"  2-torsion t = {t} ({tdesc}); short-model roots {roots}")
    print(f"  labels selected: {len(labels)} (primes to {labels[-1][0] if labels else '-'})")
    print(f"  F2 rank of the {rho}x{rho} matrix: {achieved}  ->  certified rank >= {rank_goal}")
    if t == 0:
        print(f"  torsion witness prime (f irreducible mod ℓ): {ell0}")
    elif t == 1:
        print(f"  oneTorsion root R = {roots[0]}, cofactor no-root prime ℓ = {ellq}")

    problems = []
    if achieved != rho:
        problems.append(f"only {achieved} of {rho} points are F2-independent; "
                        f"the certified bound would be {rank_goal}")
    if t == 0 and ell0 is None:
        problems.append("t=0 but no torsion witness prime under the cap; raise it in torsion_prime")
    if t == 1 and ellq is None:
        problems.append("t=1 but no cofactor witness prime under the cap; raise it")
    if claimed is not None and rank_goal != claimed:
        problems.append(f"certified rank {rank_goal} != claimed rank_lower_bound {claimed}")
    fatal = achieved != rho or (t == 0 and ell0 is None) or (t == 1 and ellq is None)
    if problems:
        print("\n!! attention:")
        for p in problems:
            print("   - " + p)
        if fatal:
            sys.exit(1)

    if args.dry_run:
        print("\n(dry run: no files written)")
        return

    repo = args.repo.rstrip("/")
    with open(f"{repo}/data/curve{cid}.txt", "w") as fh:
        for (xn, xd, yn, yd) in curve.short:
            fh.write(f"{frac(xn, xd)} {frac(yn, yd)}\n")
    with open(f"{repo}/data/curve{cid}-labels.txt", "w") as fh:
        for (p, th) in sorted(labels):
            fh.write(f"{p} {th}\n")
    jinv = j_lit(j_invariant(*ainvs))
    defblock = gate(f"/-- ICARM leaderboard curve {cid} over `ℚ`. -/\n{def_block(cid, ainvs)}")
    rankblock = gate(
        f"/-- ICARM leaderboard curve {cid} has Mordell-Weil rank at least `{rank_goal}`. -/\n"
        f"public theorem curve{cid}_hasRankGE_{rank_goal} : HasRankGE curve{cid} {rank_goal} := by\n"
        f"  unfold curve{cid}\n  {tactic}")
    ellblock = gate(
        f"/-- Curve {cid} is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/\n"
        f"public instance : curve{cid}.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)")
    jblock = j_theorem(cid, jinv)
    template = (Path(__file__).parent / "curve_template.lean").read_text()
    lean = template.format(id=cid, rank=rank_goal, eq=weier_eq(*ainvs[:3]),
                           coeffs=coeff_block(ainvs[3], ainvs[4]),
                           defblock=defblock, rankblock=rankblock, ellblock=ellblock, jblock=jblock)
    with open(f"{repo}/Curves/Curve{cid}.lean", "w") as fh:
        fh.write(lean)

    print(f"\nwrote data/curve{cid}.txt, data/curve{cid}-labels.txt, "
          f"Curves/Curve{cid}.lean")
    print(f"add to Curves.lean:  import Curves.Curve{cid}")


if __name__ == "__main__":
    main()
