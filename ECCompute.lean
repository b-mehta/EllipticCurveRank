-- Foundations
import ECCompute.Kernel
import ECCompute.ForLean
import ECCompute.Check.IntResNat
import ECCompute.Certificate

-- Pure mathematics
import ECCompute.Theory.Descent
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.Descent.ReducedArith
import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.Theory.Descent.Collinearity
import ECCompute.Theory.Descent.PsiBase
import ECCompute.Check.LambdaCompute
import ECCompute.Theory.RankDeduction
import ECCompute.Theory.IntegralScaling
import ECCompute.Theory.CompleteSquare

-- Certification checkers
import ECCompute.Check.DescentMatrix
import ECCompute.Check.Primes
import ECCompute.Check.Labels
import ECCompute.Check.RootMod
import ECCompute.Check.Torsion
import ECCompute.Check.Points
import ECCompute.Check.JInvariant

-- Soundness of the checkers
import ECCompute.Soundness.Fold
import ECCompute.Soundness.F2Invert
import ECCompute.Soundness.Points

-- Main theory
import ECCompute.MainTheorem

-- Certificate tactic
import ECCompute.Tactic.CertifyEval
import ECCompute.Tactic.CertifyCurve

-- Certified curves
import ECCompute.Curves.Curve7
import ECCompute.Curves.Curve8
import ECCompute.Curves.Curve9
import ECCompute.Curves.Curve10
import ECCompute.Curves.Curve11
import ECCompute.Curves.Curve12
import ECCompute.Curves.Curve13
import ECCompute.Curves.Curve14
import ECCompute.Curves.Curve74
import ECCompute.Curves.Curve273

-- Upstream candidates
import ECCompute.ForMathlib.ModuleTorsionQuotient
import ECCompute.ForMathlib.PadicValInt
import ECCompute.ForMathlib.RatDenom
import ECCompute.ForMathlib.TwoTorsion
import ECCompute.ForMathlib.WeierstrassCurveAffine
import ECCompute.ForMathlib.WeierstrassCurveProjective
