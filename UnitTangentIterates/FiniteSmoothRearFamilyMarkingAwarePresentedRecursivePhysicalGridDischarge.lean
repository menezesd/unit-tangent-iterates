import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.TubeMemberFloorFree
import UnitTangentIterates.ChordArc

/-! # Discharging retained physical-grid hypotheses

This companion to the range-aligned presented physical grid records the
hypotheses that are already available from the recursive construction.  A
variable tube gives the nonzero marked perimeter needed to compare raw and
arclength ranges, retained terminal inputs give edgewise rear tubes, and a
`PhysicalRowBounds` package gives the uniform rear tube used by the limiting
Harnack argument.

Ordinary tube membership of the independently marked physical fronts remains
explicit.  It does not follow from equality of images or from rear
kinematics, since `IsTubeMember` includes marking-dependent speed data.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  RichFamilyPhysicalMarkingIntegration

open FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource

/-- The canonical normalized unit-tangent front has a genuine ordinary tube
certificate once its geometric injectivity is known.  All jet, speed, and
convexity fields are intrinsic consequences of the exact source; injectivity
is precisely what supplies the positive chord constant. -/
theorem exists_unitTangentData_tube
    {a b : Data} {Gamma : NormalPath a b} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s)
    (hinj : InjOn (normalizedFront A) (Ico 0 1)) :
    ∃ d : ℝ, 0 < d ∧ IsTubeMember (A.P Gamma.T) 0 d
      (unitTangentData A) := by
  have hnorm : ∀ u, ‖normalizedFrontVelocity A u‖ = A.P Gamma.T := by
    intro u
    simp [normalizedFrontVelocity, Complex.norm_exp,
      abs_of_pos (A.period_pos Gamma.T)]
  have hVcont : Continuous (normalizedFrontVelocity A) :=
    Differentiable.continuous fun u =>
      (normalizedFrontVelocity_deriv A u).differentiableAt
  obtain ⟨d, hd, hchord⟩ := ChordArc.exists_chord_arc
    (A.period_pos Gamma.T) (normalizedFront_deriv A) hVcont
    (normalizedFrontVelocity_periodic A) (normalizedFront_periodic A)
    (fun u => (hnorm u).ge) hinj
  refine ⟨d, hd, MarkedSpace.isTubeMember_zero_of_convex_and_chord
    ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro u
    simpa only [unitTangentData_curve, unitTangentData_velocity] using
      normalizedFront_deriv A u
  · intro u
    simpa [unitTangentData] using normalizedFrontVelocity_deriv A u
  · simpa only [unitTangentData_curve] using normalizedFront_periodic A
  · intro u v
    simp only [unitTangentData_velocity, hnorm]
  · intro u
    rw [unitTangentData_velocity, hnorm]
  · intro u
    change 0 ≤ ((starRingEnd ℂ) (normalizedFrontVelocity A u) *
      normalizedFrontAcceleration A u).im
    let z : ℂ := Complex.exp
      (Complex.I * (A.Theta Gamma.T (A.P Gamma.T * u) : ℂ))
    have hz : (starRingEnd ℂ) z * z = 1 := by
      dsimp [z]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    have heq : (starRingEnd ℂ) (normalizedFrontVelocity A u) *
        normalizedFrontAcceleration A u =
        (((A.P Gamma.T) ^ 3 * A.K Gamma.T (A.P Gamma.T * u) : ℝ) : ℂ) *
          Complex.I := by
      simp only [normalizedFrontVelocity, normalizedFrontAcceleration]
      rw [map_mul, Complex.conj_ofReal]
      change (A.P Gamma.T : ℂ) * (starRingEnd ℂ) z *
        ((A.P Gamma.T : ℂ) ^ 2 *
          (Complex.I * (A.K Gamma.T (A.P Gamma.T * u) : ℂ) * z)) = _
      push_cast
      linear_combination
        ((A.P Gamma.T : ℂ) ^ 3 *
          (A.K Gamma.T (A.P Gamma.T * u) : ℂ) * Complex.I) * hz
    rw [heq]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg (A.period_pos Gamma.T).le 3) (hK0 _)
  · intro u hu v hv
    simpa only [unitTangentData_curve] using hchord u hu v hv

/-- Terminal geometry identifies its canonical front with `unitTangentData`,
so the preceding intrinsic theorem applies without any range transport. -/
theorem PresentedTerminalGeometry.exists_frontData_tube
    {a b : Data} {Gamma : NormalPath a b} {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A}
    (G : PresentedTerminalGeometry A E)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s)
    (hinj : InjOn (normalizedFront A) (Ico 0 1)) :
    ∃ d : ℝ, 0 < d ∧ IsTubeMember (A.P Gamma.T) 0 d G.frontData := by
  rw [G.frontData_eq]
  exact exists_unitTangentData_tube A hK0 hinj

/-- If the retained physical-front certificate is the actual canonical
marking (as it is for `Certificate.ofSame`), the canonical tube transfers by
equality.  The abstract `Certificate` interface intentionally does not retain
this equality. -/
theorem PresentedTerminalGeometry.exists_physicalFront_tube_of_eq
    {a b : Data} {Gamma : NormalPath a b} {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A}
    (G : PresentedTerminalGeometry A E)
    (hphysical : G.physicalFront.physicalFront = G.frontData)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s)
    (hinj : InjOn (normalizedFront A) (Ico 0 1)) :
    ∃ d : ℝ, 0 < d ∧ IsTubeMember (A.P Gamma.T) 0 d
      G.physicalFront.physicalFront := by
  rw [hphysical]
  exact exists_frontData_tube G hK0 hinj

/-- A positive lower speed in a variable tube makes the marked perimeter
positive. -/
theorem perim_pos_of_variableTube
    {c C kmin dlt : ℝ} {p : Data} (hc : 0 < c)
    (hp : VariableMarkedTube.IsVariableTubeMember c C kmin dlt p) :
    0 < perim p := by
  rw [perim]
  exact hc.trans_le (hp.speed_lb 0)

/-- Nonvanishing form used by arclength range conversion. -/
theorem perim_ne_of_variableTube
    {c C kmin dlt : ℝ} {p : Data} (hc : 0 < c)
    (hp : VariableMarkedTube.IsVariableTubeMember c C kmin dlt p) :
    perim p ≠ 0 :=
  ne_of_gt (perim_pos_of_variableTube hc hp)

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The recursive marked grid has nonzero perimeter as soon as its actual
variable-tube certificate is supplied (for example by a `CapFamily`). -/
theorem markedGrid_perim_ne_of_variableTube
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (hc : 0 < c)
    (htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k)) :
    ∀ n k, perim (markedGrid F n k) ≠ 0 :=
  fun n k => perim_ne_of_variableTube hc (htube n k)

/-- Remove both auxiliary inputs of `rangeKinematics` when the steering cap
is the configured constant `sourceKh`: constancy is definitional, and marked
perimeters follow from the actual recursive variable tube. -/
noncomputable def sourceKhRangeKinematics
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal (fun _ => sourceKh) Qmax a MA NA K0 K1 K2)
    (hc : 0 < c)
    (htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k)) :
    FinitePullbackPhysicalRearRangeKinematics sourceKh
      (rearGrid F) (markedGrid F) :=
  rangeKinematics F sourceKh (fun _ => rfl)
    (markedGrid_perim_ne_of_variableTube F hc htube)

/-- Every positive-depth rear representative carries its own ordinary tube
certificate from the exact presented terminal input.  The constants are
edge-dependent here; uniform constants are supplied by `PhysicalRowBounds`
below. -/
def rearGrid_succ_tube
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    IsTubeMember
      ((rowFamilyAt F k).row n).terminalInput.physical.cq 0
      ((rowFamilyAt F k).row n).terminalInput.physical.dlt
      (rearGrid F n (k + 1)) := by
  simpa [rearGrid, successorAt, PresentedRowFamily.successor,
    successorOfPresentedRows] using
      ((rowFamilyAt F k).row n).terminalInput.zero_floor_tube

/-- Existing row bounds discharge the uniform ordinary rear-tube hypothesis
of the range-aligned limiting closure. -/
theorem rearGrid_tube_of_physicalRowBounds
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {cb db : ℝ}
    (R : PhysicalRowBounds (rearGrid F) (markedGrid F) cb db) :
    ∀ n k, IsTubeMember cb 0 db (rearGrid F n k) :=
  R.physical_tube

/-- Configured constant-cap closure with every retained recursive input
discharged.  The sole geometric input not stored by the recursive presented
state is an ordinary tube for its independently marked physical fronts. -/
def sourceKhLimitStrictnessDataH
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal (fun _ => sourceKh) Qmax a MA NA K0 K1 K2)
    (hc : 0 < c)
    (htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k))
    {cb db cp dp : ℝ}
    (R : PhysicalRowBounds (rearGrid F) (markedGrid F) cb db)
    (hcb : 0 < cb) (hcp : 0 < cp)
    (hfront : ∀ n k, IsTubeMember cp 0 dp (physicalFrontGrid F n k))
    (X : ℕ → Data) (hX : ∀ n, Tendsto (rearGrid F n) atTop (nhds (X n)))
    (n : ℕ) : UnconditionalAssembly.LimitStrictnessDataH (X n) :=
  limitStrictnessDataH_of_finitePullbackPhysicalRearRangeKinematics
    sourceKh_nonnegative sourceKh_lt_one hcb hcp R.physical_tube
    (sourceKhRangeKinematics F hc htube) hfront X hX n

end FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge
