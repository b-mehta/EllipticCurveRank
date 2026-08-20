-- Upstream candidates
import ECCompute.ForMathlib.ListGetD
import ECCompute.ForMathlib.ModuleTorsionQuotient
import ECCompute.ForMathlib.PadicValInt
import ECCompute.ForMathlib.RatDenom
import ECCompute.ForMathlib.TwoTorsion
import ECCompute.ForMathlib.WeierstrassCurveAffine
import ECCompute.ForMathlib.WeierstrassCurveProjective

-- Pure mathematics
import ECCompute.Theory.CompleteSquare
import ECCompute.Theory.Descent
import ECCompute.Theory.Descent.Collinearity
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.Theory.Descent.PsiBase
import ECCompute.Theory.Descent.ReducedArith
import ECCompute.Theory.Descent.Reduction.EpsFinite
import ECCompute.Theory.Descent.Reduction.Hom
import ECCompute.Theory.Descent.Reduction.IntModel
import ECCompute.Theory.Descent.Reduction.KernelClosure
import ECCompute.Theory.Descent.Reduction.RedP
import ECCompute.Theory.Descent.Reduction.ReducedSlope
import ECCompute.Theory.Descent.Reduction.Repr
import ECCompute.Theory.IntegralScaling
import ECCompute.Theory.RankDeduction

-- Certification checkers
import ECCompute.Check.DescentMatrix
import ECCompute.Check.F2Invert
import ECCompute.Check.Fold
import ECCompute.Check.IntResNat
import ECCompute.Check.JInvariant
import ECCompute.Check.Labels
import ECCompute.Check.LambdaCompute
import ECCompute.Check.Points
import ECCompute.Check.Primes
import ECCompute.Check.RootMod
import ECCompute.Check.Torsion

-- The certificate and the soundness theorem
import ECCompute.Certificate
import ECCompute.MainTheorem

-- Tactics
import ECCompute.Tactic.CertifyCurve
import ECCompute.Tactic.CertifyEval
import ECCompute.Tactic.QuickRfl

-- Certified curves
import ECCompute.Curves.CM82
import ECCompute.Curves.Curve273
import ECCompute.Curves.Elkies28
import ECCompute.Curves.ElkiesKlagsbrun29
import ECCompute.Curves.Fermigier22
import ECCompute.Curves.MartinMcMillen23
import ECCompute.Curves.MartinMcMillen24
import ECCompute.Curves.Nagao20
import ECCompute.Curves.NagaoKouya21
import ECCompute.Curves.Wiman4
