import Mathlib
import UnitTangentIterates.GaugeTangentialFundamental
import UnitTangentIterates.GaugeMarkedDataOfRearFamily
import UnitTangentIterates.GaugeClosingRelations
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# The comparison path of the family of selected rears, with the bounds on one period

`GaugeMarkedDataOfRearFamily.exists_variableSpeed_normalPath_of_rearFamily`
produces the comparison path of the family of selected rears of a normal path of
fronts, asking for a bound `|ξ| ≤ R_b` on the tangential component of the motion
*globally in the arclength*.  For a family of closed curves whose rear arclength
period `Q t` moves that bound cannot hold: the closing relations force
`ξ(t, x + Q t) = ξ(t, x) − Q'(t)`, so a globally bounded `ξ` means a stationary
period.

This file is the fundamental-domain form of that assembly.  The closing of the
slices is taken as the geometric input — `rearOwn(t, x + Q t) = rearOwn(t, x)`
and the tangent angle increasing by `2π` over one period — and the two drift
relations are then *derived* from it (`GaugeClosingRelations.closing_relations`):
the normal component is `Q t`-periodic and the tangential one drifts by `−Q'(t)`.
The bound on the tangential component is asked only on the fundamental domain
`[0, Q t]`, which is exactly what the one-period drift estimate
`RearOwnDriftFundamental.abs_frameTangential_le_cost_on_period` provides.
Nothing is assumed about the motion of the period.

Main result: `exists_variableSpeed_normalPath_of_rearFamily_fundamental`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeRearFamilyFundamental

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeTangentialFundamental
  NormalPathC2IncrementVariableSpeed RearFamilyFrame RearOwnArclength RearOwnTangential
  RearOwnTangentialCost RearOwnTangentialCostC2 UniformFrameBounds
  GaugeMarkedDataOfRearFamily GaugeFlowFundamentalDomain

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf etaF alphaT kT gS : ℝ → ℝ → ℝ}
  {m : ℝ → ℝ} {Q Q' P Kx Rb Dd : ℝ → ℝ} {P0 khat d r kx kh : ℝ}

/-- The tangent of a family of slices whose tangent angle increases by `2π` over
one period is periodic. -/
theorem periodic_rearOwnTangent (hQ : ∀ t x,
    rearOwnAngle Θ δ sf t (x + Q t) = rearOwnAngle Θ δ sf t x + 2 * Real.pi) (t : ℝ) :
    Function.Periodic
      (fun x => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))) (Q t) := by
  intro x
  simp only
  have hsplit : Complex.I * ((rearOwnAngle Θ δ sf t (x + Q t) : ℝ) : ℂ)
      = Complex.I * ((rearOwnAngle Θ δ sf t x : ℝ) : ℂ) + 2 * Real.pi * Complex.I := by
    rw [hQ t x]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **The exact gauge-field certificate used by the selected-rear flow.**

For `R = -xi`, where `xi` is the tangential component of the selected-rear
motion, the first two spatial derivatives are `-partialX xi` and
`-partialX (partialX xi)`.  Their bounds are the sharp coefficients
`rearKappa1 kh` and `rearKappa2 kh` times the front cost density.  This theorem
exports the estimates which were previously available only inside the proof
of `exists_variableSpeed_normalPath_of_rearFamily_fundamental`. -/
theorem selectedRear_gaugeField_certificate {p q : Data} (Gamma : NormalPath p q)
    {Q P : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s)
    (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t)
      (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt
      (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic
      (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t)
    (hlink : ∀ t u, Gamma.eta t u = etaF t (P t * u)) :
    let xi := frameTangential Ydot (rearOwnAngle Θ δ sf)
    let R : ℝ → ℝ → ℝ := fun t x => -xi t x
    let Rx : ℝ → ℝ → ℝ := fun t x => -partialX xi t x
    let Rxx : ℝ → ℝ → ℝ := fun t x => -partialX (partialX xi) t x
    ContDiff ℝ 2 (uncurry xi) ∧
      Continuous (uncurry R) ∧ Continuous (uncurry Rx) ∧ Continuous (uncurry Rxx) ∧
      (∀ t x, HasDerivAt (R t) (Rx t x) x) ∧
      (∀ t x, HasDerivAt (Rx t) (Rxx t x) x) ∧
      (∀ t x, |Rx t x| ≤ rearKappa1 kh * Gamma.m t) ∧
      (∀ t x, |Rxx t x| ≤ rearKappa2 kh * Gamma.m t) := by
  dsimp only
  have hxiC : ContDiff ℝ (2 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnTangential.contDiff_frameTangential hYdotC hangC
  have hpxC : ContDiff ℝ (1 : ℕ)
      (uncurry (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)))) :=
    contDiff_partialX (n := 1) hxiC
  have hpxxC : Continuous
      (uncurry (partialX (partialX
        (frameTangential Ydot (rearOwnAngle Θ δ sf))))) :=
    (contDiff_partialX (n := 0) hpxC).continuous
  refine ⟨hxiC, hxiC.continuous.neg, hpxC.continuous.neg,
    hpxxC.neg, ?_, ?_, ?_, ?_⟩
  · intro t x
    simpa using (hasDerivAt_partialX (hxiC.of_le (by norm_num)) t x).neg
  · intro t x
    simpa using (hasDerivAt_partialX hpxC t x).neg
  · intro t x
    simpa only [abs_neg] using
      (abs_partialX_frameTangential_le_rearKappa1 (K := K) (Q := Q)
        (etaF := etaF) (P := P) Gamma hkh0 hkh1 hstrip0 hstrip1 hF hTheta
        hsteer hsf hcos hYt (hYdotC.of_le (by norm_num))
        (hangC.of_le (by norm_num)) hQpos hper hjac hPpos hlink t x)
  · intro t x
    simpa only [abs_neg] using
      (abs_partialX_partialX_frameTangential_le_cost_density (K := K) (Q := Q)
        (etaF := etaF) (P := P) Gamma hkh0 hkh1 hstrip0 hstrip1 hK hF hTheta
        hsteer hsf hcos hYt hYdotC hangC hQpos hper hjac hPpos hlink t x)

/-- A stopped normal-path density turns the sharp time-dependent gauge-field
bounds into the global constants required by the flow existence and terminal
marking-defect theorems. -/
theorem selectedRear_gaugeField_global_bounds {p q : Data} (Gamma : NormalPath p q)
    {R Rx Rxx : ℝ → ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hRx : ∀ t x, HasDerivAt (R t) (Rx t x) x)
    (hRxbd : ∀ t x, |Rx t x| ≤ rearKappa1 kh * Gamma.m t)
    (hRxxbd : ∀ t x, |Rxx t x| ≤ rearKappa2 kh * Gamma.m t) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t, Gamma.m t ≤ B) ∧
      (∀ t, LipschitzWith (Real.toNNReal (rearKappa1 kh * B)) (R t)) ∧
      ∀ t x, |Rxx t x| ≤ rearKappa2 kh * B := by
  obtain ⟨B, hB0, hB⟩ := GaugeFlowDerivCost.exists_bound_of_stop
    Gamma.cont_m Gamma.m_nonneg Gamma.m_stop Gamma.T_pos
  have hk1 : 0 ≤ rearKappa1 kh := rearKappa1_nonneg hkh0 hkh1
  have hk2 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg hkh0 hkh1
  have hRxB : ∀ t x, |Rx t x| ≤ rearKappa1 kh * B := by
    intro t x
    exact (hRxbd t x).trans (mul_le_mul_of_nonneg_left (hB t) hk1)
  refine ⟨B, hB0, hB, ?_, ?_⟩
  · intro t
    exact GaugeFlowDerivCost.lipschitzWith_of_deriv_bound
      (mul_nonneg hk1 hB0) hRx hRxB t
  · intro t x
    exact (hRxxbd t x).trans (mul_le_mul_of_nonneg_left (hB t) hk2)

/-- The gauge frame and all identities needed by the terminal marking-defect
estimate, retained before the long rear-family construction erases them. -/
structure RetainedGaugeFrame
    (Phi : ℝ → ℝ → ℝ) (Q Q' m : ℝ → ℝ) (xi : ℝ → ℝ → ℝ)
    (kappa kappa2 : ℝ) where
  frame : GaugeFrameData
  v_eq_one : ∀ t x, frame.v t x = 1
  xi_eq : ∀ t x, frame.xi t x = xi t x
  period_deriv : ∀ t, HasDerivAt Q (Q' t) t
  v_periodic : ∀ t, Function.Periodic (frame.v t) (Q t)
  xi_quasiPeriodic : ∀ t x,
    frame.xi t (x + Q t) = frame.xi t x - Q' t * frame.v t x
  flow : ∀ u t, HasDerivAt (fun s => Phi s u)
    (GaugeRate.gaugeRate frame.xi frame.v t (Phi t u)) t
  initial : ∀ u, Phi 0 u = Q 0 * u
  xi_zero : ∀ t, frame.xi t 0 = 0
  rate1_bound : ∀ t x,
    |GaugeRate.gaugeRate1 frame.xi frame.xi1 frame.v frame.v1 t x| ≤
      kappa * m t
  rate2_bound : ∀ t x,
    |GaugeRate.gaugeRate2 frame.xi frame.xi1 frame.xi2
      frame.v frame.v1 frame.v2 t x| ≤ kappa2 * m t

/-- **The comparison path of the family of selected rears, with the bound on the
tangential component asked on one period only.**

Along a normal path `Γ` of fronts, the family of selected rears carried in its
own arclength closes up with the moving arclength period `Q`, its tangent angle
increasing by `2π` over one period.  It then admits a gauge marking `Φ` — the
flow of minus its tangential component, which fixes the base point and carries
the unit parameter interval onto one period `[0, Q t]` — under which it is a
normal path of the path metric whose slices form a variable-speed family, with
the explicit constants built from the cost `M = ∫₀^{T} m`.

Only the fundamental domain is used: the bound `R_b` on the tangential component
is asked for `x ∈ [0, Q t]`, and no constraint is placed on the motion of `Q`. -/
theorem exists_variableSpeed_normalPath_of_rearFamily_fundamental_with_eta_spatialC2_of_intrinsic_bound
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (Sxi : RearOwnFrameDrift.SpatialC2
      (frameTangential Ydot (rearOwnAngle Θ δ sf)))
    (hencont : Continuous
      (uncurry (frameNormal Ydot (rearOwnAngle Θ δ sf))))
    (hCbd : ∀ t x, |Sxi.xi1 t x| ≤ rearKappa1 kh * m t)
    (hC2bd : ∀ t x, |Sxi.xi2 t x| ≤ rearKappa2 kh * m t)
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    -- the closing of the slices, with a period free to move
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hclose : ∀ t x, rearOwn F Θ δ sf t (x + Q t) = rearOwn F Θ δ sf t x)
    (hangper : ∀ t x,
      rearOwnAngle Θ δ sf t (x + Q t) = rearOwnAngle Θ δ sf t x + 2 * Real.pi)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    -- the inverse Jacobi ODE of the rear normal rate
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hetaFbd : ∀ t s, |etaF t s| ≤ Γ.m t)
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    -- the bound on the tangential component, on one period only
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hr : 0 ≤ r)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      (∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧
          (∀ t u, Γ'.eta t u = frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) ∧
          (∀ t u, Phi t (u + 1) = Phi t u + Q t) ∧
          (∃ phi1 phi2 : ℝ → ℝ → ℝ,
            (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
            (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
            (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t)) ∧
            (∀ t u, phi1 t u ≤ costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) ∧
            (∀ t u, |phi2 t u| ≤
              costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))) ∧
          Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh * costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ') ∧
      Nonempty (RetainedGaugeFrame Phi Q Q' m
        (frameTangential Ydot (rearOwnAngle Θ δ sf))
        (rearKappa1 kh) (rearKappa2 kh)) := by
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hangC1 : ContDiff ℝ 1 (uncurry (rearOwnAngle Θ δ sf)) :=
    RearOwnHigherRegularity.contDiff_rearOwnAngle hΘC hδC hsfC
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  -- each slice is carried in its own arclength
  have hYspace : ∀ t s, HasDerivAt (rearOwn F Θ δ sf t)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t s : ℂ))) s := by
    intro t s
    simpa [rearOwnTangent] using
      hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos t s
  -- the motion splits in the moving frame
  have hYtime : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) t := by
    intro t x
    have h := frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    refine (hYt t x).congr_deriv ?_
    simp only [frameTangential, frameNormal]
    conv_lhs => rw [← h]
    ring
  -- the closing relations of the family: the drift of the tangential component
  -- and the periodicity of the normal one
  have hclosing := fun t x =>
    GaugeClosingRelations.closing_relations (X := rearOwn F Θ δ sf)
      (tau := fun t' x' => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t' x' : ℂ)))
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (eta := frameNormal Ydot (rearOwnAngle Θ δ sf)) (Q := Q) (Q' := Q')
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (fun _ _ => Complex.exp_ne_zero _) (periodic_rearOwnTangent hangper) hclose hQd t x
  have hxiqp : ∀ t x, frameTangential Ydot (rearOwnAngle Θ δ sf) t (x + Q t)
      = frameTangential Ydot (rearOwnAngle Θ δ sf) t x - Q' t := fun t x =>
    (hclosing t x).1
  have hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t) :=
    fun t x => (hclosing t x).2
  -- the pointwise bounds carried by the maximum principle
  have hen : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ m t := fun t x =>
    le_trans (abs_frameNormal_le_slice (Q := Q) (EF := Γ.m) hkh0 hkh1
      hstrip0 hstrip1 hQpos hper hjac hetaFbd t x) (hmge t)
  -- the curvature of the slices is dominated by `κ̂`
  have hkbd : ∀ t x, |Real.tan (δ t (sf t x))| ≤ khat := fun t x =>
    le_trans (abs_tan_le_rearKappa1 hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
      hkappa1
  -- the second arclength derivative of the normal rate, read off the ODE
  have henSS : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)) x := fun t x =>
    (hgSd t x).sub (hjac t x)
  have hgbd : ∀ t x, |etaF t (sf t x) / Real.cos (δ t (sf t x))|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
      (hetaFbd t (sf t x))
  have henbd : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_slice (Q := Q) (EF := Γ.m) hkh0 hkh1 hstrip0 hstrip1
      hQpos hper hjac hetaFbd t x
  have hS0m : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ 1 * m t := by
    intro t
    rw [one_mul]
    exact hmge t
  -- the curvature is periodic, being the arclength derivative of the tangent angle
  have hkper : ∀ t, Function.Periodic (fun x => Real.tan (δ t (sf t x))) (Q t) :=
    fun t => periodic_deriv_of_quasiPeriodic (Q' := fun _ => 2 * Real.pi)
      (f := rearOwnAngle Θ δ sf) (fx := fun t' x => Real.tan (δ t' (sf t' x)))
      (fun a x => hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf a x) hangper t
  obtain ⟨Phi, hPhi0, hbase, hflow, hmain, hframe⟩ :=
    exists_variableSpeed_normalPath_of_tangential_fundamental_with_eta_c2flow
      (C := fun t => rearKappa1 kh * m t) (C2 := fun t => rearKappa2 kh * m t)
      (Y := rearOwn F Θ δ sf) (alpha := rearOwnAngle Θ δ sf)
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (en := frameNormal Ydot (rearOwnAngle Θ δ sf))
      (k := fun t x => Real.tan (δ t (sf t x)))
      (kX := fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
        / Real.cos (δ t (sf t x)) ^ 3)
      (enS := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)
      (enSS := fun t x => gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x))
      (g := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))) (gS := gS)
      (S0 := fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)) (Dd := Dd) (Rb := Rb) (Kx := Kx)
      (m := m) (T := Γ.T) (khat := khat) (kappa2 := rearKappa2 kh)
      (alphaT := alphaT) (kT := kT) (c := 1) (d := d) (r := r) (kx := kx) (P0 := P0)
      (Q := Q) (Q' := Q') (turn := 2 * Real.pi)
      Sxi
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf)
      (rearKappa2_nonneg hkh0 hkh1)
      (continuous_const.mul hmc) (continuous_const.mul hmc)
      (fun t => mul_le_mul_of_nonneg_right hkappa1 (hm0 t)) (fun _ => le_rfl)
      hangC1 hkC1 halphaT hkT
      (hasDerivAt_rearCurv_space (K := K) hsteer hsf hcos)
      halphaTc hkTc hkXc hkC1.continuous hKxnn hjac henSS halphaTS hmixed hgSd hjac
      hQpos hQd hxiqp hkper hangper hxi0
      (fun t x _ => hkbd t x) (fun t x _ => hCbd t x) (fun t x _ => hC2bd t x)
      (fun t x _ => hKxbd t x) hRbd (fun t x _ => hgbd t x) (fun t x _ => henbd t x)
      (fun t x _ => hgSbd t x) hS0m hDm hRbm hKxm hr hm0
      (by simp only [mul_one]; linarith [hnumA])
      (by simp only [mul_one]; linarith [hnumK]) Γ.T_pos
      hencont hmc hmstop
  obtain ⟨D, hDv, hDxi⟩ := hframe
  have hDv1 : ∀ t x, D.v1 t x = 0 := by
    intro t x
    have hfun : D.v t = fun _ => (1 : ℝ) := funext (hDv t)
    have hder := D.hv t x
    rw [hfun] at hder
    exact hder.unique (hasDerivAt_const x (1 : ℝ))
  have hDv2 : ∀ t x, D.v2 t x = 0 := by
    intro t x
    have hfun : D.v1 t = fun _ => (0 : ℝ) := funext (hDv1 t)
    have hder := D.hv1 t x
    rw [hfun] at hder
    exact hder.unique (hasDerivAt_const x (0 : ℝ))
  have hDxi1 : ∀ t x, D.xi1 t x = Sxi.xi1 t x := by
    intro t x
    have hfun : D.xi t =
        frameTangential Ydot (rearOwnAngle Θ δ sf) t := funext (hDxi t)
    have hder := D.hxi t x
    rw [hfun] at hder
    exact hder.unique (Sxi.deriv1 t x)
  have hDxi2 : ∀ t x, D.xi2 t x = Sxi.xi2 t x := by
    intro t x
    have hfun : D.xi1 t = Sxi.xi1 t := funext (hDxi1 t)
    have hder := D.hxi1 t x
    rw [hfun] at hder
    exact hder.unique (Sxi.deriv2 t x)
  let retained : RetainedGaugeFrame Phi Q Q' m
      (frameTangential Ydot (rearOwnAngle Θ δ sf))
      (rearKappa1 kh) (rearKappa2 kh) :=
    { frame := D
      v_eq_one := hDv
      xi_eq := hDxi
      period_deriv := hQd
      v_periodic := by
        intro t x
        rw [hDv t (x + Q t), hDv t x]
      xi_quasiPeriodic := by
        intro t x
        rw [hDxi t (x + Q t), hDxi t x, hDv t x, mul_one]
        exact hxiqp t x
      flow := by
        intro u t
        have hf := hflow u t
        convert hf using 1
        simp [GaugeRate.gaugeRate, hDv t (Phi t u), hDxi t (Phi t u)]
      initial := hPhi0
      xi_zero := by
        intro t
        rw [hDxi t 0]
        exact hxi0 t
      rate1_bound := by
        intro t x
        simp [GaugeRate.gaugeRate1, hDv, hDxi, hDxi1, hDv1]
        exact hCbd t x
      rate2_bound := by
        intro t x
        simp [GaugeRate.gaugeRate2, hDv, hDxi, hDxi1, hDxi2, hDv1, hDv2]
        exact hC2bd t x }
  exact ⟨Phi, hPhi0, hbase, hflow, (fun a b ha hb hsup =>
    hmain a b ha hb (fun t u => hen t (Phi t u)) hsup), ⟨retained⟩⟩

/-- Compatibility wrapper: joint `C²` data supplies the exact spatial
certificate required by the stopped-clock core theorem. -/
theorem exists_variableSpeed_normalPath_of_rearFamily_fundamental_with_eta_c2flow_of_intrinsic_bound
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hclose : ∀ t x, rearOwn F Θ δ sf t (x + Q t) = rearOwn F Θ δ sf t x)
    (hangper : ∀ t x,
      rearOwnAngle Θ δ sf t (x + Q t) = rearOwnAngle Θ δ sf t x + 2 * Real.pi)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hetaFbd : ∀ t s, |etaF t s| ≤ Γ.m t)
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hr : 0 ≤ r)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      (∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧
          (∀ t u, Γ'.eta t u = frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) ∧
          (∀ t u, Phi t (u + 1) = Phi t u + Q t) ∧
          (∃ phi1 phi2 : ℝ → ℝ → ℝ,
            (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
            (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
            (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t)) ∧
            (∀ t u, phi1 t u ≤ costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) ∧
            (∀ t u, |phi2 t u| ≤
              costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))) ∧
          Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh * costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ') ∧
      Nonempty (RetainedGaugeFrame Phi Q Q' m
        (frameTangential Ydot (rearOwnAngle Θ δ sf))
        (rearKappa1 kh) (rearKappa2 kh)) := by
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  have hYspace : ∀ t s, HasDerivAt (rearOwn F Θ δ sf t)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t s : ℂ))) s := by
    intro t s
    simpa [rearOwnTangent] using
      hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos t s
  have hYtime : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) t := by
    intro t x
    have h := frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    refine (hYt t x).congr_deriv ?_
    simp only [frameTangential, frameNormal]
    conv_lhs => rw [← h]
    ring
  have hclosing := fun t x =>
    GaugeClosingRelations.closing_relations (X := rearOwn F Θ δ sf)
      (tau := fun t' x' => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t' x' : ℂ)))
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (eta := frameNormal Ydot (rearOwnAngle Θ δ sf)) (Q := Q) (Q' := Q')
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (fun _ _ => Complex.exp_ne_zero _) (periodic_rearOwnTangent hangper) hclose hQd t x
  have hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t) :=
    fun t x => (hclosing t x).2
  let Sxi := RearOwnFrameDrift.SpatialC2.ofContDiff
    (contDiff_frameTangential hYdotC hangC)
  have hCbd : ∀ t x, |Sxi.xi1 t x| ≤ rearKappa1 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_front (K := K) (Q := Q)
      (etaF := etaF) (EF := Γ.m) hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt
      hYdotC1 hangC1 hQpos hper hjac hetaFbd t x) ?_
    rw [rearKappa1, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa1_nonneg hkh0 hkh1)
  have hC2bd : ∀ t x, |Sxi.xi2 t x| ≤ rearKappa2 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_partialX_frameTangential_le_front (K := K)
      (Q := Q) (etaF := etaF) (EF := Γ.m) hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf
      hcos hYt hYdotC hangC hQpos hper hjac hetaFbd t x) ?_
    rw [rearKappa2]
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa2_nonneg hkh0 hkh1)
  apply exists_variableSpeed_normalPath_of_rearFamily_fundamental_with_eta_spatialC2_of_intrinsic_bound
    (Γ := Γ) (Sxi := Sxi)
    (hencont := (contDiff_frameNormal hYdotC1 hangC1).continuous)
    (hCbd := hCbd) (hC2bd := hC2bd) <;> assumption



theorem exists_variableSpeed_normalPath_of_rearFamily_fundamental_with_eta
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    -- the closing of the slices, with a period free to move
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hclose : ∀ t x, rearOwn F Θ δ sf t (x + Q t) = rearOwn F Θ δ sf t x)
    (hangper : ∀ t x,
      rearOwnAngle Θ δ sf t (x + Q t) = rearOwnAngle Θ δ sf t x + 2 * Real.pi)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    -- the inverse Jacobi ODE of the rear normal rate
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    -- the bound on the tangential component, on one period only
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hr : 0 ≤ r)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧
          (∀ t u, Γ'.eta t u = frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) ∧
          Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh * costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' := by
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hYdotC2 : ContDiff ℝ (2 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hangC2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  -- each slice is carried in its own arclength
  have hYspace : ∀ t s, HasDerivAt (rearOwn F Θ δ sf t)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t s : ℂ))) s := by
    intro t s
    simpa [rearOwnTangent] using
      hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos t s
  -- the motion splits in the moving frame
  have hYtime : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) t := by
    intro t x
    have h := frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    refine (hYt t x).congr_deriv ?_
    simp only [frameTangential, frameNormal]
    conv_lhs => rw [← h]
    ring
  -- the closing relations of the family: the drift of the tangential component
  -- and the periodicity of the normal one
  have hclosing := fun t x =>
    GaugeClosingRelations.closing_relations (X := rearOwn F Θ δ sf)
      (tau := fun t' x' => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t' x' : ℂ)))
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (eta := frameNormal Ydot (rearOwnAngle Θ δ sf)) (Q := Q) (Q' := Q')
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (fun _ _ => Complex.exp_ne_zero _) (periodic_rearOwnTangent hangper) hclose hQd t x
  have hxiqp : ∀ t x, frameTangential Ydot (rearOwnAngle Θ δ sf) t (x + Q t)
      = frameTangential Ydot (rearOwnAngle Θ δ sf) t x - Q' t := fun t x =>
    (hclosing t x).1
  have hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t) :=
    fun t x => (hclosing t x).2
  -- the pointwise bounds carried by the maximum principle
  have hen : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ m t := fun t x =>
    le_trans (abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1
      hstrip0 hstrip1 hQpos hper hjac hPpos hlink t x) (hmge t)
  -- the curvature of the slices is dominated by `κ̂`
  have hkbd : ∀ t x, |Real.tan (δ t (sf t x))| ≤ khat := fun t x =>
    le_trans (abs_tan_le_rearKappa1 hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
      hkappa1
  -- the two tangential estimates
  have hCbd : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ rearKappa1 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_rearKappa1 (K := K) (Q := Q)
      (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt
      hYdotC1 hangC1 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa1_nonneg hkh0 hkh1)
  have hC2bd : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
        ≤ rearKappa2 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_partialX_frameTangential_le_cost_density (K := K)
      (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf
      hcos hYt hYdotC2 hangC2 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa2_nonneg hkh0 hkh1)
  -- the second arclength derivative of the normal rate, read off the ODE
  have henSS : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)) x := fun t x =>
    (hgSd t x).sub (hjac t x)
  have hgbd : ∀ t x, |etaF t (sf t x) / Real.cos (δ t (sf t x))|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_jacobiSource_le_cost (etaF := etaF) (P := P) (sf := sf) Γ hkh0 hkh1 hstrip0
      hstrip1 hPpos hlink t x
  have henbd : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1
      hQpos hper hjac hPpos hlink t x
  have hS0m : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ 1 * m t := by
    intro t
    rw [one_mul]
    exact hmge t
  -- the curvature is periodic, being the arclength derivative of the tangent angle
  have hkper : ∀ t, Function.Periodic (fun x => Real.tan (δ t (sf t x))) (Q t) :=
    fun t => periodic_deriv_of_quasiPeriodic (Q' := fun _ => 2 * Real.pi)
      (f := rearOwnAngle Θ δ sf) (fx := fun t' x => Real.tan (δ t' (sf t' x)))
      (fun a x => hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf a x) hangper t
  obtain ⟨Phi, hPhi0, hbase, hflow, hmain⟩ :=
    exists_variableSpeed_normalPath_of_tangential_fundamental_with_eta
      (C := fun t => rearKappa1 kh * m t) (C2 := fun t => rearKappa2 kh * m t)
      (Y := rearOwn F Θ δ sf) (alpha := rearOwnAngle Θ δ sf)
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (en := frameNormal Ydot (rearOwnAngle Θ δ sf))
      (k := fun t x => Real.tan (δ t (sf t x)))
      (kX := fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
        / Real.cos (δ t (sf t x)) ^ 3)
      (enS := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)
      (enSS := fun t x => gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x))
      (g := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))) (gS := gS)
      (S0 := fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)) (Dd := Dd) (Rb := Rb) (Kx := Kx)
      (m := m) (T := Γ.T) (khat := khat) (kappa2 := rearKappa2 kh)
      (alphaT := alphaT) (kT := kT) (c := 1) (d := d) (r := r) (kx := kx) (P0 := P0)
      (Q := Q) (Q' := Q') (turn := 2 * Real.pi)
      (contDiff_frameTangential hYdotC hangC)
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf)
      (rearKappa2_nonneg hkh0 hkh1)
      (continuous_const.mul hmc) (continuous_const.mul hmc)
      (fun t => mul_le_mul_of_nonneg_right hkappa1 (hm0 t)) (fun _ => le_rfl)
      hangC1 hkC1 halphaT hkT
      (hasDerivAt_rearCurv_space (K := K) hsteer hsf hcos)
      halphaTc hkTc hkXc hkC1.continuous hKxnn hjac henSS halphaTS hmixed hgSd hjac
      hQpos hQd hxiqp hkper hangper hxi0
      (fun t x _ => hkbd t x) (fun t x _ => hCbd t x) (fun t x _ => hC2bd t x)
      (fun t x _ => hKxbd t x) hRbd (fun t x _ => hgbd t x) (fun t x _ => henbd t x)
      (fun t x _ => hgSbd t x) hS0m hDm hRbm hKxm hr hm0
      (by simp only [mul_one]; linarith [hnumA])
      (by simp only [mul_one]; linarith [hnumK]) Γ.T_pos
      (contDiff_frameNormal hYdotC1 hangC1).continuous hmc hmstop
  exact ⟨Phi, hPhi0, hbase, hflow, fun a b ha hb hsup =>
    hmain a b ha hb (fun t u => hen t (Phi t u)) hsup⟩


/-- Compatibility form retaining the historical result shape. -/
theorem exists_variableSpeed_normalPath_of_rearFamily_fundamental
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    -- the closing of the slices, with a period free to move
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hclose : ∀ t x, rearOwn F Θ δ sf t (x + Q t) = rearOwn F Θ δ sf t x)
    (hangper : ∀ t x,
      rearOwnAngle Θ δ sf t (x + Q t) = rearOwnAngle Θ δ sf t x + 2 * Real.pi)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    -- the inverse Jacobi ODE of the rear normal rate
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    -- the bound on the tangential component, on one period only
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hr : 0 ≤ r)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧ Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (Q 0) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh * costP1 (Q 0) khat (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' := by
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hYdotC2 : ContDiff ℝ (2 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hangC2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  -- each slice is carried in its own arclength
  have hYspace : ∀ t s, HasDerivAt (rearOwn F Θ δ sf t)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t s : ℂ))) s := by
    intro t s
    simpa [rearOwnTangent] using
      hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos t s
  -- the motion splits in the moving frame
  have hYtime : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) t := by
    intro t x
    have h := frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    refine (hYt t x).congr_deriv ?_
    simp only [frameTangential, frameNormal]
    conv_lhs => rw [← h]
    ring
  -- the closing relations of the family: the drift of the tangential component
  -- and the periodicity of the normal one
  have hclosing := fun t x =>
    GaugeClosingRelations.closing_relations (X := rearOwn F Θ δ sf)
      (tau := fun t' x' => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t' x' : ℂ)))
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (eta := frameNormal Ydot (rearOwnAngle Θ δ sf)) (Q := Q) (Q' := Q')
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (fun _ _ => Complex.exp_ne_zero _) (periodic_rearOwnTangent hangper) hclose hQd t x
  have hxiqp : ∀ t x, frameTangential Ydot (rearOwnAngle Θ δ sf) t (x + Q t)
      = frameTangential Ydot (rearOwnAngle Θ δ sf) t x - Q' t := fun t x =>
    (hclosing t x).1
  have hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t) :=
    fun t x => (hclosing t x).2
  -- the pointwise bounds carried by the maximum principle
  have hen : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ m t := fun t x =>
    le_trans (abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1
      hstrip0 hstrip1 hQpos hper hjac hPpos hlink t x) (hmge t)
  -- the curvature of the slices is dominated by `κ̂`
  have hkbd : ∀ t x, |Real.tan (δ t (sf t x))| ≤ khat := fun t x =>
    le_trans (abs_tan_le_rearKappa1 hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
      hkappa1
  -- the two tangential estimates
  have hCbd : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ rearKappa1 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_rearKappa1 (K := K) (Q := Q)
      (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt
      hYdotC1 hangC1 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa1_nonneg hkh0 hkh1)
  have hC2bd : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
        ≤ rearKappa2 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_partialX_frameTangential_le_cost_density (K := K)
      (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf
      hcos hYt hYdotC2 hangC2 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa2_nonneg hkh0 hkh1)
  -- the second arclength derivative of the normal rate, read off the ODE
  have henSS : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)) x := fun t x =>
    (hgSd t x).sub (hjac t x)
  have hgbd : ∀ t x, |etaF t (sf t x) / Real.cos (δ t (sf t x))|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_jacobiSource_le_cost (etaF := etaF) (P := P) (sf := sf) Γ hkh0 hkh1 hstrip0
      hstrip1 hPpos hlink t x
  have henbd : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1
      hQpos hper hjac hPpos hlink t x
  have hS0m : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ 1 * m t := by
    intro t
    rw [one_mul]
    exact hmge t
  -- the curvature is periodic, being the arclength derivative of the tangent angle
  have hkper : ∀ t, Function.Periodic (fun x => Real.tan (δ t (sf t x))) (Q t) :=
    fun t => periodic_deriv_of_quasiPeriodic (Q' := fun _ => 2 * Real.pi)
      (f := rearOwnAngle Θ δ sf) (fx := fun t' x => Real.tan (δ t' (sf t' x)))
      (fun a x => hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf a x) hangper t
  obtain ⟨Phi, hPhi0, hbase, hflow, hmain⟩ :=
    exists_variableSpeed_normalPath_of_tangential_const_fundamental
      (Y := rearOwn F Θ δ sf) (alpha := rearOwnAngle Θ δ sf)
      (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
      (en := frameNormal Ydot (rearOwnAngle Θ δ sf))
      (k := fun t x => Real.tan (δ t (sf t x)))
      (kX := fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
        / Real.cos (δ t (sf t x)) ^ 3)
      (enS := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)
      (enSS := fun t x => gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x))
      (g := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))) (gS := gS)
      (S0 := fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)) (Dd := Dd) (Rb := Rb) (Kx := Kx)
      (m := m) (T := Γ.T) (kappa1 := rearKappa1 kh) (kappa2 := rearKappa2 kh)
      (alphaT := alphaT) (kT := kT) (c := 1) (d := d) (r := r) (kx := kx) (P0 := P0)
      (Q := Q) (Q' := Q') (turn := 2 * Real.pi)
      (contDiff_frameTangential hYdotC hangC)
      (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
      (hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf)
      (rearKappa2_nonneg hkh0 hkh1) hkappa1
      hangC1 hkC1 halphaT hkT
      (hasDerivAt_rearCurv_space (K := K) hsteer hsf hcos)
      halphaTc hkTc hkXc hkC1.continuous hKxnn hjac henSS halphaTS hmixed hgSd hjac
      hQpos hQd hxiqp hkper hangper hxi0
      (fun t x _ => hkbd t x) (fun t x _ => hCbd t x) (fun t x _ => hC2bd t x)
      (fun t x _ => hKxbd t x) hRbd (fun t x _ => hgbd t x) (fun t x _ => henbd t x)
      (fun t x _ => hgSbd t x) hS0m hDm hRbm hKxm hr hm0
      (by simp only [mul_one]; linarith [hnumA])
      (by simp only [mul_one]; linarith [hnumK]) Γ.T_pos
      (contDiff_frameNormal hYdotC1 hangC1).continuous hmc hmstop
  exact ⟨Phi, hPhi0, hbase, hflow, fun a b ha hb hsup =>
    hmain a b ha hb (fun t u => hen t (Phi t u)) hsup⟩

end GaugeRearFamilyFundamental
