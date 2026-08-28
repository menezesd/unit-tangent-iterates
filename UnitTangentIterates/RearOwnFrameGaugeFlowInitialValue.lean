import UnitTangentIterates.RearOwnFrameGaugeFlowReanchoring

/-!
# Rear gauge flow with prescribed initial marking

The zero-origin gauge is insufficient after a normalized phase change.  The
correct transported origin is the solution of the same gauge ODE with the
corresponding rear-arclength coordinate as its initial value.
-/

noncomputable section

open Function

namespace RearOwnFrameGaugeFlowInitialValue

/-- A globally defined `C1` integral curve of the negative tangential field
with a prescribed initial rear-arclength coordinate. -/
structure GaugeAt (xi : ℝ → ℝ → ℝ) (q0 : ℝ) where
  q : ℝ → ℝ
  initial : q 0 = q0
  ode : ∀ t, HasDerivAt q (-xi t (q t)) t
  contDiff : ContDiff ℝ 1 q

/-- Existentially initialled gauge, convenient for constructions whose initial
coordinate is part of the retained presentation data. -/
structure Gauge (xi : ℝ → ℝ → ℝ) where
  q0 : ℝ
  q : ℝ → ℝ
  initial : q 0 = q0
  ode : ∀ t, HasDerivAt q (-xi t (q t)) t
  contDiff : ContDiff ℝ 1 q

/-- Joint spatial `C2` regularity and a uniform first derivative bound give a
global gauge through every prescribed initial coordinate. -/
theorem exists_gaugeAt {xi : ℝ → ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 xi) {L q0 : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ t x, |S.xi1 t x| ≤ L) : Nonempty (GaugeAt xi q0) := by
  have hlip : ∀ t, LipschitzWith (Real.toNNReal L) (fun x ↦ -xi t x) := by
    intro t
    exact GaugeFlowDerivCost.lipschitzWith_of_deriv_bound hL
      (fun s x ↦ (S.deriv1 s x).neg)
      (fun s x ↦ by simpa using hbound s x) t
  have htime : ∀ x, Continuous (fun t ↦ -xi t x) := by
    intro x
    simpa [uncurry] using S.continuous0.comp
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : ℝ ↦ x))) |>.neg
  obtain ⟨q, hq0, hq⟩ :=
    GlobalODEGrowth.exists_global_solution_real_of_lipschitz hlip htime 0 q0
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

def GaugeAt.toGauge {xi : ℝ → ℝ → ℝ} {q0 : ℝ}
    (G : GaugeAt xi q0) : Gauge xi where
  q0 := q0
  q := G.q
  initial := G.initial
  ode := G.ode
  contDiff := G.contDiff

theorem exists_gauge {xi : ℝ → ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 xi) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ t x, |S.xi1 t x| ≤ L) (q0 : ℝ) :
    Nonempty (Gauge xi) := by
  obtain ⟨G⟩ := exists_gaugeAt S hL hbound (q0 := q0)
  exact ⟨G.toGauge⟩

/-- The old zero-origin gauge embeds in the prescribed-initial-value API. -/
def GaugeAt.ofZero {xi : ℝ → ℝ → ℝ}
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge xi) : GaugeAt xi 0 where
  q := G.q
  initial := G.initial
  ode := G.ode
  contDiff := G.contDiff

/-- Conversely, the zero-initial-value specialization is definitionally the
legacy gauge certificate. -/
def GaugeAt.toZero {xi : ℝ → ℝ → ℝ}
    (G : GaugeAt xi 0) : RearOwnFrameGaugeFlowReanchoring.Gauge xi where
  q := G.q
  initial := G.initial
  ode := G.ode
  contDiff := G.contDiff

end RearOwnFrameGaugeFlowInitialValue
