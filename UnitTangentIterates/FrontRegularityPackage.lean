import UnitTangentIterates.FrontDataRegularity
import UnitTangentIterates.SteeringPackage

/-!
# The front-side regularity hypotheses of the rear-family constructor
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function FrontFromPath

namespace FrontDataRegularity

/-- **The front and its tangent angle are jointly `C¹`.**

`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
asks for `hFC : ContDiff ℝ 1 (uncurry F)` and `hΘC : ContDiff ℝ 1 (uncurry Θ)`
where `F` and `Θ` are the front family and its tangent-angle family.  Both are
already available: `contDiff_frontOfPath` from the regularity of the moving
curve and of the speed, and `contDiff_angleOfPath` from the regularity of the
curvature and of the tangent argument at the marked point.

Note the asymmetry in the second: `contDiff_angleOfPath` concludes at order
`n + 1` from hypotheses at order `n + 1`, so `n = 0` already gives the `C¹`
statement — the angle is one order better than the raw integrand because it is
an integral of the curvature. -/
theorem front_and_angle_contDiff_one {X V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}
    (hX : ContDiff ℝ (1 : ℕ) (uncurry X)) (hP : ContDiff ℝ (1 : ℕ) P)
    (hPne : ∀ t, P t ≠ 0)
    (hcurv : ContDiff ℝ ((0 : ℕ) + 1) (uncurry (curvOfPath V A P)))
    (harg : ContDiff ℝ ((0 : ℕ) + 1) fun t => (tangentOfPath V P t 0).arg) :
    ContDiff ℝ (1 : ℕ) (uncurry (frontOfPath X P)) ∧
      ContDiff ℝ ((0 : ℕ) + 1) (uncurry (angleOfPath V A P)) :=
  ⟨contDiff_frontOfPath hX hP hPne, contDiff_angleOfPath hcurv harg⟩

/-- The same at the higher order the defect estimates use. -/
theorem front_and_angle_contDiff_four {X V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}
    (hX : ContDiff ℝ (4 : ℕ) (uncurry X)) (hP : ContDiff ℝ (4 : ℕ) P)
    (hPne : ∀ t, P t ≠ 0)
    (hcurv : ContDiff ℝ ((3 : ℕ) + 1) (uncurry (curvOfPath V A P)))
    (harg : ContDiff ℝ ((3 : ℕ) + 1) fun t => (tangentOfPath V P t 0).arg) :
    ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath X P)) ∧
      ContDiff ℝ ((3 : ℕ) + 1) (uncurry (angleOfPath V A P)) :=
  ⟨contDiff_frontOfPath hX hP hPne, contDiff_angleOfPath hcurv harg⟩

end FrontDataRegularity
