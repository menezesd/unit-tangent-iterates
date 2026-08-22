import Mathlib
import UnitTangentIterates.GaugeDensities
import UnitTangentIterates.PathMetricJacobi

/-!
# A normal path in the gauge parameter, from estimates in arclength

`PathMetricJacobi.exists_normalPath_of_jacobi` turns the four estimates of the
paper's lemma *Inverse Jacobi estimates* into a normal path, but it wants them
in the **normalized parameter** of `PathMetric.lean`.  What the geometry
supplies is the same four estimates in **arclength**, for a family of curves
which does not move normally in its arclength parameter: it must first be put
in the normal gauge.

This file joins the two.  If the moving family is read in the gauge parameter
`u ↦ Φ(t, u)` of a closed family — so that each slice has period one
(`GaugeFlowPeriodic.lean`) — then `GaugeDensities.lean` bounds its four
normalized densities by the arclength ones, at the price of the distortion
factors of the gauge flow.  Over the compact time interval of the path those
factors are bounded by their value at the final time, so the arclength
estimates with constants `C_W, C₀, C₁, C₂` become normalized estimates with

`C_W' = C_W e^{LT}/Q`, `C₀' = C₀`, `C₁' = C₁Qe^{LT}`,
`C₂' = C₂(Qe^{LT})² + C₁ R₂Q²T e^{2LT}`,

`L` and `R₂` being the Lipschitz constant and the second-derivative bound of the
tangential rate.

Main result: `exists_normalPath_of_gauge_jacobi`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace GaugeNormalPath

open UniformFrameBounds GaugeDensities GaugeFlowPeriodic PathMetricJacobi

/-- The constants of the normalized estimates, produced from the arclength ones
by the distortion of the gauge flow over the time interval `[0, T]`. -/
def gaugeCW (CW L T Q : ℝ) : ℝ := CW * (Real.exp (L * T) / Q)

/-- The sup-norm constant is unchanged: the gauge flow does not move the values
of the normal velocity, only the parameter. -/
def gaugeC0 (C0 : ℝ) : ℝ := C0

/-- The first-derivative constant, distorted by the derivative of the gauge
flow. -/
def gaugeC1 (C1 L T Q : ℝ) : ℝ := C1 * (Q * Real.exp (L * T))

/-- The second-derivative constant: the square of the distortion, plus the
second derivative of the gauge flow acting on the first derivative. -/
def gaugeC2 (C1 C2 L R2 T Q : ℝ) : ℝ :=
  C2 * (Q * Real.exp (L * T)) ^ 2 + C1 * (R2 * Q ^ 2 * T * Real.exp (2 * L * T))

/-- **From arclength estimates to a normal path in the gauge parameter.**

`Γ` is a normal path of fronts and `XR` a family of curves joining `p'` to `q'`
over the same time interval, moving with the normal velocity `η_t(Φ(t,u)) ν`,
where `η_t` is the normal velocity in the arclength of the reference slice and
`Φ` is the gauge flow of the closed family described by the bundle `D`.  If the
arclength densities of `η_t` obey the four estimates of the paper's lemma
*Inverse Jacobi estimates* against the densities of `Γ` at every time of the
interval, and the family is at rest outside it, then `XR` is a normal path
whose cost is the constant `jacobiConst` of the distorted constants times the
cost of `Γ`. -/
theorem exists_normalPath_of_gauge_jacobi {p q p' q' : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hxiper : ∀ a, Function.Periodic (D.xi a) Q) (hvper : ∀ a, Function.Periodic (D.v a) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    {XR nuR : ℝ → ℝ → ℂ} {etaR : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Function.Periodic (etaR t) Q)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0)
    {CW C0 C1 C2 : ℝ} (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hW : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..Q, |etaR t x|) ≤ CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS0 : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      supNorm (etaR t) ≤ C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS1 : ∀ t ∈ Ioo (0:ℝ) Γ.T, supNorm (deriv (etaR t))
      ≤ C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)))
    (hS2 : ∀ t ∈ Ioo (0:ℝ) Γ.T, supNorm (deriv (deriv (etaR t)))
      ≤ C2 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
        + supNorm (iteratedDeriv 1 (Γ.eta t)))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst (gaugeCW CW D.rateLip Γ.T Q) (gaugeC0 C0)
        (gaugeC1 C1 D.rateLip Γ.T Q)
        (gaugeC2 C1 C2 D.rateLip D.rateBound2 Γ.T Q) * cost Γ := by
  set L := D.rateLip with hL
  set R2 := D.rateBound2 with hR2
  set T := Γ.T with hT
  have hLnn : 0 ≤ L := D.rateLip_nonneg
  have hR2nn : 0 ≤ R2 := D.rateBound2_nonneg
  have hTpos : 0 < T := Γ.T_pos
  have hE : (0:ℝ) < Real.exp (L * T) := Real.exp_pos _
  -- the flowed normal velocity
  set etaF : ℝ → ℝ → ℝ := fun t u => etaR t (Phi t u) with hetaF
  -- the distortion factors at time `t` are bounded by those at the final time
  have hexp_le : ∀ t ∈ Ioo (0:ℝ) T, Real.exp (L * |t|) ≤ Real.exp (L * T) := by
    intro t ht
    have : L * |t| ≤ L * T := by
      have habs : |t| ≤ T := by rw [abs_of_pos ht.1]; exact ht.2.le
      exact mul_le_mul_of_nonneg_left habs hLnn
    exact Real.exp_le_exp.mpr this
  have hexp2_le : ∀ t ∈ Ioo (0:ℝ) T,
      R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|) ≤ R2 * Q ^ 2 * T * Real.exp (2 * L * T) := by
    intro t ht
    have habs : |t| ≤ T := by rw [abs_of_pos ht.1]; exact ht.2.le
    have h2 : Real.exp (2 * L * |t|) ≤ Real.exp (2 * L * T) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_left habs (by positivity)
    have hnn : (0:ℝ) ≤ R2 * Q ^ 2 := by positivity
    have hnnT : (0:ℝ) ≤ T := hTpos.le
    have hstep : R2 * Q ^ 2 * |t| ≤ R2 * Q ^ 2 * T := mul_le_mul_of_nonneg_left habs hnn
    have hnn2 : (0:ℝ) ≤ R2 * Q ^ 2 * T := by positivity
    calc R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|)
        ≤ R2 * Q ^ 2 * T * Real.exp (2 * L * |t|) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ ≤ R2 * Q ^ 2 * T * Real.exp (2 * L * T) := mul_le_mul_of_nonneg_left h2 hnn2
  -- the front densities are nonnegative
  have hWFnn : ∀ t, (0:ℝ) ≤ ∫ u in (0:ℝ)..1, |Γ.eta t u| :=
    fun t => intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _)
  -- the four densities of the flowed slice
  have hdens := fun t => gauge_densities_le D hQ hxiper hvper hPhid hPhi0
    (hetaC2 t) (hetaper t) t
  -- the flowed slice vanishes when the family is at rest
  have hzero : ∀ t ∉ Ioo (0:ℝ) T, etaF t = fun _ => 0 := by
    intro t ht
    funext u
    simp [hetaF, hrest t ht]
  have hsupzero : ∀ t ∉ Ioo (0:ℝ) T, supNorm (etaF t) = 0 := by
    intro t ht
    rw [hzero t ht]
    simp [supNorm]
  have hsupzero1 : ∀ t ∉ Ioo (0:ℝ) T, supNorm (iteratedDeriv 1 (etaF t)) = 0 := by
    intro t ht
    rw [hzero t ht, iteratedDeriv_zero_fun]
    simp [supNorm]
  have hsupzero2 : ∀ t ∉ Ioo (0:ℝ) T, supNorm (iteratedDeriv 2 (etaF t)) = 0 := by
    intro t ht
    rw [hzero t ht, iteratedDeriv_zero_fun]
    simp [supNorm]
  have hintzero : ∀ t ∉ Ioo (0:ℝ) T, (∫ u in (0:ℝ)..1, |etaF t u|) = 0 := by
    intro t ht
    rw [hzero t ht]
    simp
  -- the flowed slice is bounded, so the sup norm is an upper bound for its values
  have hbdd : ∀ t u, |etaF t u| ≤ supNorm (etaF t) := by
    intro t u
    refine le_supNorm ?_ u
    obtain ⟨M, _, hM⟩ := UniformFrameBounds.exists_bound_of_periodic (t0 := (0:ℝ)) (t1 := 0)
      (f := fun _ x => etaR t x) hQ
      (by
        have : Continuous (etaR t) := (hetaC2 t).continuous
        exact this.comp continuous_snd)
      (fun _ => hetaper t)
    exact ⟨M, by
      rintro y ⟨u', rfl⟩
      exact hM 0 (by simp) (Phi t u')⟩
  refine exists_normalPath_of_jacobi (p' := p') (q' := q') Γ ?_ ?_ ?_ ?_
    (XR := XR) (nuR := nuR) (etaR := etaF)
    hstart hfinish hderiv hcont hnu hbdd ?_ ?_ ?_ ?_
  · exact mul_nonneg hCW (by positivity)
  · exact hC0
  · exact mul_nonneg hC1 (by positivity)
  · have h1 : (0:ℝ) ≤ C2 * (Q * Real.exp (L * T)) ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ C1 * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by positivity
    simpa [gaugeC2] using add_nonneg h1 h2
  · -- the `L¹` density
    intro t
    by_cases ht : t ∈ Ioo (0:ℝ) T
    · calc (∫ u in (0:ℝ)..1, |etaF t u|)
          ≤ (Real.exp (L * |t|) / Q) * ∫ x in (0:ℝ)..Q, |etaR t x| := (hdens t).2.2.2
        _ ≤ (Real.exp (L * T) / Q) * (CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|) := by
            have hnn : (0:ℝ) ≤ ∫ x in (0:ℝ)..Q, |etaR t x| :=
              intervalIntegral.integral_nonneg hQ.le (fun u _ => abs_nonneg _)
            have hle1 : Real.exp (L * |t|) / Q ≤ Real.exp (L * T) / Q := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (hexp_le t ht) (inv_nonneg.mpr hQ.le)
            have hle2 := hW t ht
            have hpos : (0:ℝ) < Real.exp (L * T) / Q := by positivity
            calc (Real.exp (L * |t|) / Q) * ∫ x in (0:ℝ)..Q, |etaR t x|
                ≤ (Real.exp (L * T) / Q) * ∫ x in (0:ℝ)..Q, |etaR t x| := by
                  exact mul_le_mul_of_nonneg_right hle1 hnn
              _ ≤ (Real.exp (L * T) / Q) * (CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|) :=
                  mul_le_mul_of_nonneg_left hle2 hpos.le
        _ = gaugeCW CW L T Q * ∫ u in (0:ℝ)..1, |Γ.eta t u| := by
            rw [gaugeCW]; ring
    · rw [hintzero t ht]
      have : (0:ℝ) ≤ gaugeCW CW L T Q := mul_nonneg hCW (by positivity)
      exact mul_nonneg this (hWFnn t)
  · -- the sup norm
    intro t
    by_cases ht : t ∈ Ioo (0:ℝ) T
    · calc supNorm (etaF t) ≤ supNorm (etaR t) := (hdens t).1
        _ ≤ C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u| := hS0 t ht
        _ = gaugeC0 C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u| := by rw [gaugeC0]
    · rw [hsupzero t ht]
      exact mul_nonneg hC0 (hWFnn t)
  · -- the first derivative
    intro t
    by_cases ht : t ∈ Ioo (0:ℝ) T
    · have hbr : (0:ℝ) ≤ (∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t) :=
        add_nonneg (hWFnn t) (supNorm_nonneg _)
      calc supNorm (iteratedDeriv 1 (etaF t))
          ≤ supNorm (deriv (etaR t)) * (Q * Real.exp (L * |t|)) := (hdens t).2.1
        _ ≤ (C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)))
              * (Q * Real.exp (L * T)) := by
            have hfac : Q * Real.exp (L * |t|) ≤ Q * Real.exp (L * T) :=
              mul_le_mul_of_nonneg_left (hexp_le t ht) hQ.le
            have hnn : (0:ℝ) ≤ supNorm (deriv (etaR t)) := supNorm_nonneg _
            have hrhs : (0:ℝ) ≤ C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)) :=
              mul_nonneg hC1 hbr
            calc supNorm (deriv (etaR t)) * (Q * Real.exp (L * |t|))
                ≤ supNorm (deriv (etaR t)) * (Q * Real.exp (L * T)) :=
                  mul_le_mul_of_nonneg_left hfac hnn
              _ ≤ (C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)))
                    * (Q * Real.exp (L * T)) := by
                  refine mul_le_mul_of_nonneg_right (hS1 t ht) ?_
                  positivity
        _ = gaugeC1 C1 L T Q * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)) := by
            rw [gaugeC1]; ring
    · rw [hsupzero1 t ht]
      have hbr : (0:ℝ) ≤ (∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t) :=
        add_nonneg (hWFnn t) (supNorm_nonneg _)
      exact mul_nonneg (mul_nonneg hC1 (by positivity)) hbr
  · -- the second derivative
    intro t
    set BR : ℝ := (∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
      + supNorm (iteratedDeriv 1 (Γ.eta t)) with hBR
    have hBRnn : 0 ≤ BR := by
      have := hWFnn t
      have h1 := supNorm_nonneg (Γ.eta t)
      have h2 := supNorm_nonneg (iteratedDeriv 1 (Γ.eta t))
      simp only [hBR]
      linarith
    by_cases ht : t ∈ Ioo (0:ℝ) T
    · have hS1' : supNorm (deriv (etaR t)) ≤ C1 * BR := by
        refine le_trans (hS1 t ht) ?_
        have h2 := supNorm_nonneg (iteratedDeriv 1 (Γ.eta t))
        have : (∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t) ≤ BR := by
          simp only [hBR]; linarith
        exact mul_le_mul_of_nonneg_left this hC1
      have hS2' : supNorm (deriv (deriv (etaR t))) ≤ C2 * BR := hS2 t ht
      calc supNorm (iteratedDeriv 2 (etaF t))
          ≤ supNorm (deriv (deriv (etaR t))) * (Q * Real.exp (L * |t|)) ^ 2
              + supNorm (deriv (etaR t)) * (R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|)) :=
            (hdens t).2.2.1
        _ ≤ (C2 * BR) * (Q * Real.exp (L * T)) ^ 2
              + (C1 * BR) * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by
            have hfac : (Q * Real.exp (L * |t|)) ^ 2 ≤ (Q * Real.exp (L * T)) ^ 2 := by
              have h1 : Q * Real.exp (L * |t|) ≤ Q * Real.exp (L * T) :=
                mul_le_mul_of_nonneg_left (hexp_le t ht) hQ.le
              have h0 : (0:ℝ) ≤ Q * Real.exp (L * |t|) := by positivity
              nlinarith
            have hnn2 : (0:ℝ) ≤ supNorm (deriv (deriv (etaR t))) := supNorm_nonneg _
            have hnn1 : (0:ℝ) ≤ supNorm (deriv (etaR t)) := supNorm_nonneg _
            have hA : supNorm (deriv (deriv (etaR t))) * (Q * Real.exp (L * |t|)) ^ 2
                ≤ (C2 * BR) * (Q * Real.exp (L * T)) ^ 2 := by
              calc supNorm (deriv (deriv (etaR t))) * (Q * Real.exp (L * |t|)) ^ 2
                  ≤ supNorm (deriv (deriv (etaR t))) * (Q * Real.exp (L * T)) ^ 2 :=
                    mul_le_mul_of_nonneg_left hfac hnn2
                _ ≤ (C2 * BR) * (Q * Real.exp (L * T)) ^ 2 := by
                    refine mul_le_mul_of_nonneg_right hS2' ?_
                    positivity
            have hB : supNorm (deriv (etaR t)) * (R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|))
                ≤ (C1 * BR) * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by
              calc supNorm (deriv (etaR t)) * (R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|))
                  ≤ supNorm (deriv (etaR t)) * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) :=
                    mul_le_mul_of_nonneg_left (hexp2_le t ht) hnn1
                _ ≤ (C1 * BR) * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by
                    refine mul_le_mul_of_nonneg_right hS1' ?_
                    positivity
            linarith
        _ = gaugeC2 C1 C2 L R2 T Q * BR := by rw [gaugeC2]; ring
    · rw [hsupzero2 t ht]
      have h1 : (0:ℝ) ≤ C2 * (Q * Real.exp (L * T)) ^ 2 := by positivity
      have h2 : (0:ℝ) ≤ C1 * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by positivity
      have : (0:ℝ) ≤ gaugeC2 C1 C2 L R2 T Q := by
        simpa [gaugeC2] using add_nonneg h1 h2
      exact mul_nonneg this hBRnn

/-- A bundle of frame data with vanishing tangential component and unit speed:
the family already moves normally, and its gauge flow is the identity. -/
def trivialFrame : GaugeFrameData where
  xi := fun _ _ => 0
  xi1 := fun _ _ => 0
  xi2 := fun _ _ => 0
  v := fun _ _ => 1
  v1 := fun _ _ => 0
  v2 := fun _ _ => 0
  rateLip := 0
  rateBound2 := 0
  hxi := fun _ x => hasDerivAt_const x 0
  hxi1 := fun _ x => hasDerivAt_const x 0
  hv := fun _ x => hasDerivAt_const x 1
  hv1 := fun _ x => hasDerivAt_const x 0
  hvne := fun _ _ => one_ne_zero
  hxic := continuous_const
  hxi1c := continuous_const
  hxi2c := continuous_const
  hvc := continuous_const
  hv1c := continuous_const
  hv2c := continuous_const
  hrate1 := fun _ _ => by simp [GaugeRate.gaugeRate1]
  hrate2 := fun _ _ => by simp [GaugeRate.gaugeRate2]

/-- **The hypotheses are consistent.**  The constant path of any marked curve,
with the trivial frame data — vanishing tangential component, unit speed, so
that the gauge flow is the dilation `Φ(t,u) = Qu` — and a rear family at rest,
satisfies all of them, with all four constants zero. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = jacobiConst (gaugeCW 0 trivialFrame.rateLip (NormalPath.const p).T 1)
        (gaugeC0 0) (gaugeC1 0 trivialFrame.rateLip (NormalPath.const p).T 1)
        (gaugeC2 0 0 trivialFrame.rateLip trivialFrame.rateBound2
          (NormalPath.const p).T 1) * cost (NormalPath.const p) := by
  have hrate : GaugeRate.gaugeRate trivialFrame.xi trivialFrame.v = fun _ _ => (0:ℝ) := by
    funext t x
    simp [GaugeRate.gaugeRate, trivialFrame]
  refine exists_normalPath_of_gauge_jacobi (Γ := NormalPath.const p) (D := trivialFrame)
    (Phi := fun _ u => 1 * u) (Q := 1) one_pos (fun _ _ => rfl) (fun _ _ => rfl)
    ?_ (fun _ => rfl) (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    (etaR := fun _ _ => 0) (fun _ => contDiff_const) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
    le_rfl le_rfl le_rfl le_rfl ?_ ?_ ?_ ?_
  · intro u t
    rw [hrate]
    simpa using hasDerivAt_const t (1 * u)
  · intro t u
    simpa using hasDerivAt_const t (p'.1 u)
  · intro u
    simpa using continuous_const
  · intro t _; simp
  · intro t _; simp [supNorm]
  · intro t _
    have hz : deriv (fun _ : ℝ => (0:ℝ)) = fun _ => 0 := by funext x; simp
    rw [hz]
    simp [supNorm]
  · intro t _
    have hz : deriv (fun _ : ℝ => (0:ℝ)) = fun _ => 0 := by funext x; simp
    rw [hz, hz]
    simp [supNorm]

end GaugeNormalPath
