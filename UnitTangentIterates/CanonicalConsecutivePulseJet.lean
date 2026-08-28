import UnitTangentIterates.CanonicalConsecutivePulsePair

/-! # Finite pulse jet from the quantitative hairpin data -/


open ShiftedCurvatureJetMajorant

namespace PaperHairpinQuantitativeData.ConsecutiveData

/-- The all-orders smoothness and relative estimates stored in `Data` provide
the exact finite jet consumed by periodization.  The first derivative is
identified with the named witness `yp` by uniqueness of derivatives. -/
theorem exists_pulseJet4_relative
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hzero : ∀ s, 0 ≤ currentPulse f theta x s) :
    ∃ y2 y3 y4 : ℝ → ℝ,
      PulseJet4 (currentPulse f theta x) yp y2 y3 y4 ∧
      PulseJetRelative (currentPulse f theta x) yp y2 y3 y4
        (c.quantitative.relativeConst 0) (c.quantitative.relativeConst 1)
        (c.quantitative.relativeConst 2) (c.quantitative.relativeConst 3)
        (c.quantitative.relativeConst 4) := by
  let y0 := currentPulse f theta x
  let z1 := iteratedDeriv 1 y0
  let z2 := iteratedDeriv 2 y0
  let z3 := iteratedDeriv 3 y0
  let z4 := iteratedDeriv 4 y0
  have hc0 : ContDiff ℝ 4 y0 := c.quantitative.smooth_pulse 4
  have hc1 : ContDiff ℝ 3 (deriv y0) := (contDiff_succ_iff_deriv.mp hc0).2.2
  have hc2 : ContDiff ℝ 2 (deriv (deriv y0)) :=
    (contDiff_succ_iff_deriv.mp hc1).2.2
  have hc3 : ContDiff ℝ 1 (deriv (deriv (deriv y0))) :=
    (contDiff_succ_iff_deriv.mp hc2).2.2
  have hc4 : ContDiff ℝ 0 (deriv (deriv (deriv (deriv y0)))) :=
    (contDiff_succ_iff_deriv.mp hc3).2.2
  have h01 : ∀ s, HasDerivAt y0 (z1 s) s := by
    intro s
    simpa [z1, iteratedDeriv_one] using
      ((hc0.differentiable (by norm_num)) s).hasDerivAt
  have h12 : ∀ s, HasDerivAt z1 (z2 s) s := by
    intro s
    simpa [z1, z2, iteratedDeriv_one, iteratedDeriv_succ] using
      ((hc1.differentiable (by norm_num)) s).hasDerivAt
  have h23 : ∀ s, HasDerivAt z2 (z3 s) s := by
    intro s
    simpa [z2, z3, iteratedDeriv_one, iteratedDeriv_succ] using
      ((hc2.differentiable (by norm_num)) s).hasDerivAt
  have h34 : ∀ s, HasDerivAt z3 (z4 s) s := by
    intro s
    simpa [z3, z4, iteratedDeriv_one, iteratedDeriv_succ] using
      ((hc3.differentiable (by norm_num)) s).hasDerivAt
  have hz3c : Continuous z3 := by
    simpa [z3, iteratedDeriv_one, iteratedDeriv_succ] using hc3.continuous
  have hz4c : Continuous z4 := by
    simpa [z4, iteratedDeriv_one, iteratedDeriv_succ] using hc4.continuous
  have hyp : yp = z1 := by
    funext s
    exact (c.pulse_deriv s).unique (by simpa [y0] using h01 s)
  subst hyp
  refine ⟨z2, z3, z4, ?_, ?_⟩
  · exact ⟨by simpa [y0] using h01, h12, h23, h34, hz3c, hz4c⟩
  · refine ⟨hzero, c.quantitative.relativeConst_nonneg 0,
      c.quantitative.relativeConst_nonneg 1, c.quantitative.relativeConst_nonneg 2,
      c.quantitative.relativeConst_nonneg 3, c.quantitative.relativeConst_nonneg 4,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      simpa [y0, currentPulse] using c.quantitative.relative 0 (by norm_num) s
    · intro s
      simpa [y0, z1, currentPulse] using c.quantitative.relative 1 (by norm_num) s
    · intro s
      simpa [y0, z2, currentPulse] using c.quantitative.relative 2 (by norm_num) s
    · intro s
      simpa [y0, z3, currentPulse] using c.quantitative.relative 3 (by norm_num) s
    · intro s
      simpa [y0, z4, currentPulse] using c.quantitative.relative 4 (by norm_num) s

/-- Consequently the canonical same-profile pair supplies the analytic Config
record once the paper's chosen common exponential and strip constants dominate
the quantitative ones. -/
theorem pulsePairAnalyticData_of_quantitative
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha C CU D DU DU2 au P : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta Cq Ht Pfun Pp)
    (hzero : ∀ s, 0 ≤ currentPulse f theta x s) (halpha : 0 ≤ alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    (hstrip : ∀ u, (∑' m : ℤ,
      shift (phase f theta g) (currentPulse f theta x) (u - m * P)) ≤ au) :
    ∃ y2 : ℝ → ℝ, PaperHairpinConfig.PulsePairAnalyticData
      (alpha := alpha) (au := au) (C := C) (CU := CU)
      (DU := DU) (DU2 := DU2) (D := D) (P := P)
      (currentPulse f theta x) yp (previousPulse f theta x g)
      (previousPulseDeriv f theta g yp) (shift (phase f theta g) y2) := by
  obtain ⟨y2, y3, y4, hjet, hrel⟩ := c.exists_pulseJet4_relative hzero
  exact ⟨y2, c.pulsePairAnalyticData_of_pulseJet hjet hrel halpha hdec0 hdec1
    hCU hD hDU hDU2 hstrip⟩

end PaperHairpinQuantitativeData.ConsecutiveData

