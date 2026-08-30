import UnitTangentIterates.PaperMainTheoremUnconditional

/-!
# Current status of Theorem 1.1

This is the canonical audit boundary for the paper's main theorem.  The
repository now proves the full paper-facing conclusion without hypotheses via
`PaperMainTheoremUnconditional.mainConclusion`.

Historical conditional assembly layers remain available in their own modules,
but they are not part of this canonical theorem boundary.
-/

noncomputable section

namespace Theorem11Status

/-- The exact conclusion of Theorem 1.1, including smoothness, embeddedness,
genuine geometric noncircularity, and the infinite forward unit-tangent orbit. -/
abbrev MainConclusion : Prop :=
  PaperMainTheoremGenuineNoncircularStatement.MainConclusion

/-- The canonical, closed statement of Theorem 1.1.  All construction inputs
are produced by `PaperMainTheoremUnconditional.mainConclusion`. -/
theorem mainConclusion : MainConclusion :=
  PaperMainTheoremUnconditional.mainConclusion

end Theorem11Status
