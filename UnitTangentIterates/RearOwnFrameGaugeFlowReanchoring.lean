import UnitTangentIterates.GlobalODEGrowth
import UnitTangentIterates.GaugeFlowDerivCost
import UnitTangentIterates.RearOwnFrameDriftReanchoring
import UnitTangentIterates.RearOwnMotion

/-!
# Genuine gauge-flow reanchoring of a rear frame

The moving phase is the global solution of `q' = -xi(t,q)`.  Translating a
rear curve by `x ↦ x + q(t)` adds `q'` times its unit tangent to its time
velocity.  Consequently the translated tangential component is
`xi(t,x+q(t)) + q'(t)`, and therefore vanishes at the new origin.
-/

noncomputable section

open Function

namespace RearOwnFrameGaugeFlowReanchoring

open RearFamilyFrame

/-- A globally defined `C¹` integral curve of the negative tangential field,
started at the selected rear origin. -/
structure Gauge (xi : ℝ → ℝ → ℝ) where
  q : ℝ → ℝ
  initial : q 0 = 0
  ode : ∀ t, HasDerivAt q (-xi t (q t)) t
  contDiff : ContDiff ℝ 1 q

/-- A jointly continuous spatial frame with a uniform first-derivative bound
has a genuine global rear gauge. -/
theorem exists_gauge {xi : ℝ → ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 xi) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ t x, |S.xi1 t x| ≤ L) : Nonempty (Gauge xi) := by
  have hlip : ∀ t, LipschitzWith (Real.toNNReal L) (fun x ↦ -xi t x) := by
    intro t
    exact GaugeFlowDerivCost.lipschitzWith_of_deriv_bound hL
      (fun s x ↦ (S.deriv1 s x).neg)
      (fun s x ↦ by simpa using hbound s x) t
  have htime : ∀ x, Continuous (fun t ↦ -xi t x) := by
    intro x
    simpa [uncurry] using S.continuous0.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ ↦ x))) |>.neg
  obtain ⟨q, hq0, hq⟩ :=
    GlobalODEGrowth.exists_global_solution_real_of_lipschitz hlip htime 0 0
  have hdiff : Differentiable ℝ q := fun t ↦ (hq t).differentiableAt
  have hrate : Continuous (fun t ↦ -xi t (q t)) := by
    simpa [uncurry] using S.continuous0.comp
      (continuous_id.prodMk hdiff.continuous) |>.neg
  have hqC : ContDiff ℝ 1 q := by
    refine contDiff_one_iff_deriv.2 ⟨hdiff, ?_⟩
    convert hrate using 1
    funext t
    exact (hq t).deriv
  exact ⟨⟨q, hq0, hq, hqC⟩⟩

def shiftedPsi (psi : ℝ → ℝ → ℝ) (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  TimeDependentSpatialReanchoring.shift psi q

/-- The actual time velocity of the translated rear curve. -/
def shiftedYdot (Ydot : ℝ → ℝ → ℂ) (psi xi : ℝ → ℝ → ℝ)
    (q : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t x ↦ TimeDependentSpatialReanchoring.shift Ydot q t x +
    ((-xi t (q t) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (shiftedPsi psi q t x : ℂ))

private theorem frameTangential_add_tangential (z : ℂ) (c psi : ℝ) :
    ((z + (c : ℂ) * Complex.exp (Complex.I * (psi : ℂ))) *
        (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))).re =
      (z * (starRingEnd ℂ)
        (Complex.exp (Complex.I * (psi : ℂ)))).re + c := by
  have hEE : Complex.exp (Complex.I * (psi : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ))) = 1 :=
    RearSmoothDependence.exp_mul_conj psi
  rw [add_mul, mul_assoc, hEE, mul_one]
  simp

theorem frameTangential_shiftedYdot
    (Ydot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t x : ℝ) :
    frameTangential
        (shiftedYdot Ydot psi (frameTangential Ydot psi) q)
        (shiftedPsi psi q) t x =
      RearOwnFrameDrift.SpatialC2.tangentialReanchor
        (frameTangential Ydot psi) q t x := by
  rw [show frameTangential
        (shiftedYdot Ydot psi (frameTangential Ydot psi) q)
        (shiftedPsi psi q) t x =
      frameTangential Ydot psi t (x + q t) -
        frameTangential Ydot psi t (q t) by
    unfold frameTangential shiftedYdot shiftedPsi
      TimeDependentSpatialReanchoring.shift
    rw [frameTangential_add_tangential]
    ring]
  rfl

theorem frameNormal_shiftedYdot
    (Ydot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t x : ℝ) :
    frameNormal
        (shiftedYdot Ydot psi (frameTangential Ydot psi) q)
        (shiftedPsi psi q) t x =
      TimeDependentSpatialReanchoring.shift
        (frameNormal Ydot psi) q t x := by
  unfold frameNormal shiftedYdot shiftedPsi
    TimeDependentSpatialReanchoring.shift
  exact RearOwnMotion.frameNormal_add_tangential _ _ _

@[simp] theorem frameTangential_shiftedYdot_zero
    (Ydot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t : ℝ) :
    frameTangential
        (shiftedYdot Ydot psi (frameTangential Ydot psi) q)
        (shiftedPsi psi q) t 0 = 0 := by
  rw [frameTangential_shiftedYdot]
  exact RearOwnFrameDrift.SpatialC2.tangentialReanchor_zero _ _ _

/-- The constant marked origin satisfies the residual gauge-flow equation for
the genuinely shifted velocity. -/
theorem zero_anchor_flow
    (Ydot : ℝ → ℝ → ℂ) (psi : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (t : ℝ) :
    HasDerivAt (fun _ : ℝ ↦ (0 : ℝ))
      (-frameTangential
        (shiftedYdot Ydot psi (frameTangential Ydot psi) q)
        (shiftedPsi psi q) t 0) t := by
  simpa using (hasDerivAt_const t (0 : ℝ))

end RearOwnFrameGaugeFlowReanchoring
