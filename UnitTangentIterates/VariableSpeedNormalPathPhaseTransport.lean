import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.MarkedShift

noncomputable section

open Function

namespace NormalPathC2IncrementVariableSpeed

open PathMetric PathMetric.NormalPath

/-- A constant cyclic change of the spatial parameter preserves every field
of the variable-speed normal-path certificate. -/
theorem isVariableSpeedNormalPath_shift
    {P0 P1 khat G1 Cg b : ℝ} {p r : MarkedSpace.Data}
    (G : NormalPath p r) (hG : IsVariableSpeedNormalPath P0 P1 khat G1 Cg G) :
    IsVariableSpeedNormalPath P0 P1 khat G1 Cg (MarkedShift.shiftPath b G) := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := hG
  refine ⟨(fun t u => g t (u + b)), (fun t u => gu t (u + b)),
    (fun t u => gt t (u + b)), (fun t u => gut t (u + b)),
    (fun t u => theta t (u + b)), (fun t u => kappa t (u + b)),
    (fun t u => etas t (u + b)), (fun t u => kt t (u + b)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun t u => hgnn t (u + b)
  · exact fun t u => hgub t (u + b)
  · exact fun t u => hguB t (u + b)
  · exact fun t u => hkap t (u + b)
  · intro t u
    have hi : HasDerivAt (fun x : ℝ => x + b) 1 u := by
      simpa using (hasDerivAt_id u).add_const b
    simpa [MarkedShift.shiftPath, MarkedShift.shiftPathOf, Function.comp_def] using
      (hXu t (u + b)).scomp u hi
  · intro t u
    simpa [Function.comp_def] using
      (hgud t (u + b)).comp u ((hasDerivAt_id u).add_const b)
  · intro t u
    simpa [Function.comp_def] using
      (hthetau t (u + b)).comp u ((hasDerivAt_id u).add_const b)
  · exact fun t u => hgt t (u + b)
  · exact fun u => hgtc (u + b)
  · exact fun t u => hgtbd t (u + b)
  · exact fun t u => hgut t (u + b)
  · exact fun u => hgutc (u + b)
  · exact fun t u => hgutbd t (u + b)
  · exact fun t u => hthetat t (u + b)
  · exact fun u => hetasc (u + b)
  · exact fun t u => hetas t (u + b)
  · exact fun t u => hkappat t (u + b)
  · exact fun u => hktc (u + b)
  · exact fun t u => hkt t (u + b)

end NormalPathC2IncrementVariableSpeed
