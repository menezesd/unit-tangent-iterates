import Mathlib
import UnitTangentIterates.GaugeNormalPath
import UnitTangentIterates.GaugeDensitiesVariable

/-!
# A normal path in the gauge parameter, for a family whose slices change length

`GaugeNormalPath.exists_normalPath_of_gauge_jacobi` turns the four estimates of
the paper's lemma *Inverse Jacobi estimates*, held in the arclength of each
slice, into a normal path in the gauge parameter — under the standing
assumption that all the slices have the *same* arclength period `Q`.

This file removes that assumption.  The arclength period of the slice at time
`t` is now a differentiable function `Q t`; the frame data of the family obeys
the closing relations of such a family (`hvper`, `hxiqp`, the relations obtained
by differentiating `X(t, x + Q t) = X(t, x)` in `t`), the normal velocity of the
slice at time `t` is `Q t`-periodic, and the `L¹` estimate is taken over one
period of the *current* slice.  The gauge flow still translates by the current
period (`GaugeFlowVariablePeriod.flow_translation_var`), so the flowed parameter
is normalized at every time, and the distortion constants are those of the
reference length `Q 0`.

Main result: `exists_normalPath_of_gauge_jacobi_var`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace GaugeNormalPathVariable

open UniformFrameBounds GaugeDensities GaugeNormalPath PathMetricJacobi

/-- **From arclength estimates to a normal path in the gauge parameter, with a
changing period.**

`Γ` is a normal path of fronts and `XR` a family of curves joining `p'` to `q'`
over the same time interval, moving with the normal velocity `η_t(Φ(t,u)) ν`,
where `η_t` is the normal velocity in the arclength of the slice at time `t` —
of period `Qf t` — and `Φ` is the gauge flow of the closed family described by
the bundle `D`.  If the arclength densities of `η_t` obey the four estimates of
the paper's lemma *Inverse Jacobi estimates* against the densities of `Γ` at
every time of the interval, and the family is at rest outside it, then `XR` is a
normal path whose cost is the constant `jacobiConst` of the constants distorted
by the reference length `Qf 0` times the cost of `Γ`. -/
theorem exists_normalPath_of_gauge_jacobi_var {p q p' q' : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hQpos : ∀ t, 0 < Qf t) (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    {XR nuR : ℝ → ℝ → ℂ} {etaR : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0)
    {CW C0 C1 C2 : ℝ} (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hW : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..(Qf t), |etaR t x|) ≤ CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS0 : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      supNorm (etaR t) ≤ C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS1 : ∀ t ∈ Ioo (0:ℝ) Γ.T, supNorm (deriv (etaR t))
      ≤ C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)))
    (hS2 : ∀ t ∈ Ioo (0:ℝ) Γ.T, supNorm (deriv (deriv (etaR t)))
      ≤ C2 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
        + supNorm (iteratedDeriv 1 (Γ.eta t)))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst (gaugeCW CW D.rateLip Γ.T (Qf 0)) (gaugeC0 C0)
        (gaugeC1 C1 D.rateLip Γ.T (Qf 0))
        (gaugeC2 C1 C2 D.rateLip D.rateBound2 Γ.T (Qf 0)) * cost Γ := by
  set Q : ℝ := Qf 0 with hQdef
  have hQ : 0 < Q := hQpos 0
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
  have hdens := fun t => GaugeDensitiesVariable.gauge_densities_le_var D hQpos hQd hvper
    hxiqp hPhid hPhi0 t (hetaC2 t) (hetaper t)
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
      (f := fun _ x => etaR t x) (hQpos t)
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
          ≤ (Real.exp (L * |t|) / Q) * ∫ x in (0:ℝ)..Qf t, |etaR t x| := (hdens t).2.2.2
        _ ≤ (Real.exp (L * T) / Q) * (CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|) := by
            have hnn : (0:ℝ) ≤ ∫ x in (0:ℝ)..Qf t, |etaR t x| :=
              intervalIntegral.integral_nonneg (hQpos t).le (fun u _ => abs_nonneg _)
            have hle1 : Real.exp (L * |t|) / Q ≤ Real.exp (L * T) / Q := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (hexp_le t ht) (inv_nonneg.mpr hQ.le)
            have hle2 := hW t ht
            have hpos : (0:ℝ) < Real.exp (L * T) / Q := by positivity
            calc (Real.exp (L * |t|) / Q) * ∫ x in (0:ℝ)..Qf t, |etaR t x|
                ≤ (Real.exp (L * T) / Q) * ∫ x in (0:ℝ)..Qf t, |etaR t x| := by
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

end GaugeNormalPathVariable
