import UnitTangentIterates.TerminalMarkingCompactness
import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminal
import UnitTangentIterates.ClosingArgument
import UnitTangentIterates.CurveDistance

/-!
# Paper-facing output from variable terminal markings

The variable triangular limit is first equipped with oriented arclength
representatives.  Only then do we choose ordinary oval curves.  This retains
the oriented unit-tangent image and keeps physical total length separate from
the basepoint speed stored by `MarkedSpace.perim` on a nonaffine marking.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric

namespace PaperFacingVariableTerminalOutput

open VariableMarkedTube TriangularMarkedPathSchemeVariableTerminal

/-- The row-zero shadow size appearing in the variable-terminal limit. -/
def shadowSize
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (_O : LimitOutput Q P e P0 P1 khat G1 Cg C c dlt) : ℝ :=
  rowC P0 P1 khat G1 Cg 0 * ShadowingTails.tail (e 0) 0

/-- Ordinary oval representatives together with the exact paper orbit and
the honest row-zero closing estimates. -/
structure Output
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (O : LimitOutput Q P e P0 P1 khat G1 Cg C c dlt)
    (direction : ℂ) (modelWidth H : ℝ) where
  Gamma : ℕ → ℝ → ℂ
  oval : ∀ n, MainTheoremConditional.IsOval (Gamma n)
  range_eq_variable : ∀ n, range (Gamma n) = range (⇑(O.X n).1)
  range_orbit : ∀ n,
    range (Gamma (n + 1)) =
      range (UnitTangent.unitTangentMap (Gamma n))
  shadow_hausdorff :
    Metric.hausdorffDist (range (Gamma 0)) (range (⇑(Q 0).1)) ≤ shadowSize O
  shadow_width :
    Width.width (range (Gamma 0)) direction ≤
      modelWidth + 2 * shadowSize O
  physical_length_error :
    |MarkedReparam.totalLength (fun u => (O.X 0).2.1 u) -
        MarkedReparam.totalLength (fun u => (Q 0).2.1 u)| ≤ shadowSize O
  physical_length_lower :
    2 * H - shadowSize O ≤
      MarkedReparam.totalLength (fun u => (O.X 0).2.1 u)
  physical_length_pos :
    0 < MarkedReparam.totalLength (fun u => (O.X 0).2.1 u)
  physical_periodic :
    Periodic (Gamma 0)
      (MarkedReparam.totalLength (fun u => (O.X 0).2.1 u))
  noncircle :
    ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0))
      (MarkedReparam.totalLength (fun u => (O.X 0).2.1 u))

/-- Choose paper-facing ordinary ovals from oriented representatives of the
variable-terminal limit.  The explicit gap is exactly the closing argument,
with physical total length controlled by marked velocity distance.

`hQbounded` is deliberately geometric.  It is immediate from periodicity of
the constructed model front, but is not stored by `LimitOutput` itself. -/
def output_of_orientedRepresentatives
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (O : LimitOutput Q P e P0 P1 khat G1 Cg C c dlt)
    (R : ∀ n, OrientedArclengthRepresentative (O.X n))
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : modelWidth + 2 * shadowSize O <
      (2 * H - shadowSize O) / Real.pi) :
    Output O direction modelWidth H := by
  let Hrep : ∀ n, ArclengthHarnackCertificate (O.X n) :=
    fun n => (R n).toArclengthHarnackCertificate
  let Gamma : ℕ → ℝ → ℂ := fun n => ev (Hrep n).q
  have hoval : ∀ n, MainTheoremConditional.IsOval (Gamma n) := by
    intro n
    exact UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH
      (Hrep n).c_pos (Hrep n).dlt_pos (Hrep n).tube (Hrep n).strictness
  have hrange : ∀ n, range (Gamma n) = range (⇑(O.X n).1) := by
    intro n
    change range (ev (Hrep n).q) = range (⇑(O.X n).1)
    rw [MarkedSpace.range_ev (Hrep n).c_pos (Hrep n).tube,
      (Hrep n).same_range]
  have horbit : ∀ n, range (Gamma (n + 1)) =
      range (UnitTangent.unitTangentMap (Gamma n)) := by
    intro n
    calc
      range (Gamma (n + 1)) = range (⇑(O.X (n + 1)).1) := hrange (n + 1)
      _ = range (VariableMarkedTube.geometricUnitTangent (O.X n)) :=
        O.range_orbit n
      _ = range (UnitTangent.unitTangentMap (Gamma n)) := by
        symm
        exact (R n).unitTangent_range
  have hhaus : Metric.hausdorffDist (range (Gamma 0))
      (range (⇑(Q 0).1)) ≤ shadowSize O := by
    rw [hrange 0]
    exact O.shadow_range 0
  have hGammaBounded : Bornology.IsBounded (range (Gamma 0)) := by
    obtain ⟨L, hL, hperiodic⟩ := (hoval 0).exists_period
    exact CurveDistance.isBounded_range_of_periodic
      (hoval 0).continuous hperiodic hL
  have hwidth : Width.width (range (Gamma 0)) direction ≤
      modelWidth + 2 * shadowSize O := by
    have habs := Width.abs_width_sub_le
      (range_nonempty (Gamma 0)) (range_nonempty (⇑(Q 0).1))
      hGammaBounded hQbounded (le_of_eq hdirection) hhaus
    linarith [(abs_le.mp habs).2, hQwidth]
  have hlength :
      |MarkedReparam.totalLength (fun u => (O.X 0).2.1 u) -
          MarkedReparam.totalLength (fun u => (Q 0).2.1 u)| ≤ shadowSize O := by
    exact (VariableMarkedPhysicalLength.abs_totalLength_sub_le_dist
      (O.X 0) (Q 0)).trans (by
        simpa [dist_comm, shadowSize] using O.shadow_dist 0)
  have hlengthLower : 2 * H - shadowSize O ≤
      MarkedReparam.totalLength (fun u => (O.X 0).2.1 u) := by
    rw [abs_sub_le_iff] at hlength
    linarith
  have hphysicalPos : 0 <
      MarkedReparam.totalLength (fun u => (O.X 0).2.1 u) := by
    rw [(R 0).physical_length]
    exact MarkedSpace.perim_pos (Hrep 0).c_pos (Hrep 0).tube
  have hphysicalPeriodic : Periodic (Gamma 0)
      (MarkedReparam.totalLength (fun u => (O.X 0).2.1 u)) := by
    have hp := MarkedSpace.periodic_ev (Hrep 0).c_pos (Hrep 0).tube
    rw [(R 0).physical_length]
    exact hp
  have hnoncircle : ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0))
      (MarkedReparam.totalLength (fun u => (O.X 0).2.1 u)) :=
    ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le
      (range_nonempty (Gamma 0)) (range_nonempty (⇑(Q 0).1))
      hGammaBounded hQbounded hdirection hhaus hQwidth hlengthLower hgap
  exact
    { Gamma := Gamma
      oval := hoval
      range_eq_variable := hrange
      range_orbit := horbit
      shadow_hausdorff := hhaus
      shadow_width := hwidth
      physical_length_error := hlength
      physical_length_lower := hlengthLower
      physical_length_pos := hphysicalPos
      physical_periodic := hphysicalPeriodic
      noncircle := hnoncircle }

end PaperFacingVariableTerminalOutput
