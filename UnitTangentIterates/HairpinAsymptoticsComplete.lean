import Mathlib
import UnitTangentIterates.FrontPeriodization
import UnitTangentIterates.HairpinArclength
import UnitTangentIterates.HairpinRelativeDerivatives
import UnitTangentIterates.HairpinPulseDecay
import UnitTangentIterates.HairpinPulseMass
import UnitTangentIterates.HairpinDefect
import UnitTangentIterates.PerimeterAsymptoticsProduced
import UnitTangentIterates.PerimeterDerivativeProduced
import UnitTangentIterates.PerimeterLeibnizProduced
import UnitTangentIterates.PerimeterHairpinPulse
import UnitTangentIterates.PeriodizationSup
import UnitTangentIterates.LargeSeparation

/-!
# Tail-local synchronization for the paper's own hairpin

This file instantiates the analytic core of Sections 4–5 of *A Noncircular Oval
with Convex Unit-Tangent Iterates* on **the paper's own translating-hairpin
profile**, closing the previously-declared gap that the large-separation
threshold consumed the two-cap perimeter asymptotics as bare hypotheses.

Main results:

* `theta_unique` : uniqueness of the rear-arclength parametrization — the glue
  showing that every producer of a hairpin parametrization produces *the same*
  canonical pair `(theta, x)`;
* `exists_hairpin_pulse_package` : ONE canonical arclength parametrization
  produces the steering pulse with exponential decay of `y` and `y'`,
  steering mass `∫ y = π`, and defect positivity `Δ = ∫ Φ(y) > 0`
  (paper Lemma *Hairpin pulse estimates*, fully instantiated);
* `hairpin_perimeter_tail_asymptotics`: for the periodization of THAT pulse,
  the half-perimeter functional satisfies `P(H) = H - Δ + O(e^{-βH})`, is
  differentiable at every large `H`, and `P'(H) = 1 + O(e^{-βH})`
  (the asymptotic clauses of Proposition *Exact two-cap pairs*, produced
  rather than assumed);
* `synchronization_tail_of_perimeter_asymptotics` : the large-separation
  threshold (paper Lemma *Large-separation threshold*) assembled from
  asymptotics that are only required above an explicit threshold — hence
  applicable verbatim to the produced `P`, `P'` of the hairpin.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

open scoped ContDiff

namespace HairpinAsymptoticsComplete

set_option maxHeartbeats 1000000

open HairpinRelative HairpinArclength PerimeterAsymptotics FrontPeriodization
  FrontPeriodizationIntegral PerimeterHairpinPulse LargeSeparation MainThresholds

variable {f : ℝ → ℝ}

/-! ### Uniqueness of the parametrizations -/

/-- Any two arclength-parametrized inverses of the rear-arclength map agree:
the hairpin has exactly ONE canonical tangent parametrization. -/
theorem theta_unique (hcontf : ContinuousOn f (Ioo 0 π)) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) {t₁ t₂ : ℝ → ℝ}
    (hv₁ : ∀ u, Hairpin.hairpinArclength f (π / 2) (t₁ u) = u)
    (hv₂ : ∀ u, Hairpin.hairpinArclength f (π / 2) (t₂ u) = u)
    (m₁ : ∀ u, t₁ u ∈ Ioo (0:ℝ) π) (m₂ : ∀ u, t₂ u ∈ Ioo (0:ℝ) π) :
    t₁ = t₂ := by
  have hmono := strictMonoOn_arclength hcontf hm hlow
  funext u
  exact hmono.injOn (m₁ u) (m₂ u) (by rw [hv₁ u, hv₂ u])

/-! ### The canonical hairpin pulse package -/

/-- **The hairpin pulse package.**  For a smooth positive profile there are ONE
canonical rear parametrization `theta` and ONE canonical front parametrization
`x` such that the steering pulse `y(s) = sin δ(s)` along them decays
exponentially together with all its derivatives, carries total mass `π`, and
its defect integral `Δ = ∫_ℝ Φ(y)` is strictly positive. -/
theorem exists_hairpin_pulse_package (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (M Δ : ℝ),
      0 < M ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
        |iteratedDeriv j (fun u => curvField f (theta u)) u| ≤ C * Real.exp (-|u| / M)) ∧
      (∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
        |iteratedDeriv j (fun s => pulseField f (theta (x s))) s| ≤ D * Real.exp (-|s| / M)) ∧
      Integrable (fun s : ℝ => pulseField f (theta (x s))) ∧
      (∫ s : ℝ, pulseField f (theta (x s)) = π) ∧
      (Δ = ∫ s : ℝ, Phi (pulseField f (theta (x s)))) ∧
      0 < Δ := by
  -- the richest producer fixes the canonical pair
  obtain ⟨M, theta, x, hM, hmem, hval, hderivθ, hxinv, hxderiv, hKdec, hydec⟩ :=
    hairpin_pulse_exponential_decay hf hfpos
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.2 fun p =>
      DifferentiableAt.continuousAt ((hderivθ p).differentiableAt)
  -- injectivity of the front arclength along `theta`
  have hsigderiv : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + curvField f (theta u) ^ 2)) u :=
    fun u => hasDerivAt_frontArclength hf hfpos hthetac u
  have hge : ∀ u, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta u) ^ 2) := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta u) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta u))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (1 + curvField f (theta u) ^ 2) := Real.sqrt_le_sqrt h1
  have hFmono : StrictMono (frontArclength f theta) :=
    ArclengthInverse.strictMono_of_deriv_ge (c := 1) one_pos hsigderiv hge
  have hxinj : Function.Injective (frontArclength f theta) := hFmono.injective
  -- transport the mass identity onto the canonical pair
  obtain ⟨θ₂, x₂, hm₂, hv₂, hxv₂, _hint, hintπ⟩ := hairpin_pulse_mass hf hfpos
  -- lower bound of the profile for the uniqueness argument
  have hcontf : ContinuousOn f (Ioo 0 π) := hf.continuous.continuousOn
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hf.continuous.continuousOn
  have hm' : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hθ₂ : theta = θ₂ := theta_unique hcontf hm' hlow hval hv₂ hmem hm₂
  subst hθ₂
  have hx₂eq : ∀ s, x s = x₂ s := fun s => hxinj (by rw [hxinv s, hxv₂ s])
  have hx₂ : x = x₂ := funext hx₂eq
  subst hx₂
  -- transport the defect positivity onto the canonical pair
  obtain ⟨θ₃, x₃, hm₃, hv₃, hxv₃, hintD, hposD⟩ := hairpin_defect hf hfpos
  have hθ₃ : theta = θ₃ := theta_unique hcontf hm' hlow hval hv₃ hmem hm₃
  subst hθ₃
  have hx₃eq : ∀ s, x s = x₃ s := fun s => hxinj (by rw [hxinv s, hxv₃ s])
  have hx₃ : x = x₃ := funext hx₃eq
  subst hx₃
  -- `Φ(y) = defect` pointwise, so `Δ = ∫ Φ(y)` is positive
  have hPhi : ∀ s : ℝ,
      Phi (pulseField f (theta (x s))) = defectField f (theta (x s)) := by
    intro s
    show 1 - Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)
        = 1 - 1 / Real.sqrt (1 + curvField f (theta (x s)) ^ 2)
    have hp : 0 < 1 + curvField f (theta (x s)) ^ 2 := by positivity
    have hrw : 1 - pulseField f (theta (x s)) ^ 2
        = 1 / (1 + curvField f (theta (x s)) ^ 2) := by
      show 1 - (curvField f (theta (x s))
          / Real.sqrt (1 + curvField f (theta (x s)) ^ 2)) ^ 2 = _
      rw [div_pow, Real.sq_sqrt hp.le]
      field_simp
      ring
    rw [hrw, Real.sqrt_div']
    · norm_num
    · positivity
  have hycont : Continuous (fun s : ℝ => pulseField f (theta (x s))) := by
    have hw : Continuous (fun s => theta (x s)) :=
      continuous_iff_continuousAt.2 fun s =>
        DifferentiableAt.continuousAt ((hxderiv s).differentiableAt)
    exact ((contDiff_pulseField hf hfpos).continuous).comp hw
  have hy0 : ∀ s : ℝ, 0 ≤ pulseField f (theta (x s)) := fun s =>
    pulseField_nonneg hfpos ⟨(hmem (x s)).1.le, (hmem (x s)).2.le⟩
  obtain ⟨Cy, hCy0, hCy⟩ := hydec 0
  have hybound : ∀ s : ℝ,
      pulseField f (theta (x s)) ≤ Cy * Real.exp (-|s| / M) := by
    intro s
    have := hCy s
    simpa [abs_of_nonneg (hy0 s)] using this
  have hyint : Integrable (fun s : ℝ => pulseField f (theta (x s))) :=
    HairpinRelative.integrable_of_exp_bound hycont hy0 hybound hM
  refine ⟨theta, x, M, ∫ s : ℝ, Phi (pulseField f (theta (x s))), hM, hmem, hval,
    hderivθ, hxinv, hxderiv, hKdec, hydec, hyint, hintπ, rfl, ?_⟩
  simp only [hPhi]
  exact hposD

/-! ### The perimeter tail asymptotics of the hairpin -/

/-- `Φ` is continuous. -/
private theorem continuous_Phi : Continuous Phi := by
  show Continuous fun z => (1:ℝ) - Real.sqrt ((1:ℝ) - z ^ 2)
  fun_prop

/-- On any interval of length `H`, an `H`-periodic function integrates the same:
`[-H/2, H/2]` vs `[0, H]`. -/
private theorem integral_center_eq_forward {g : ℝ → ℝ} {H : ℝ}
    (hper : Function.Periodic g H) (hH : 0 < H) :
    ∫ u in (-(H / 2))..(H / 2), g u = ∫ s in (0:ℝ)..H, g s := by
  have h := hper.intervalIntegral_add_eq_of_pos hH (-(H / 2)) 0
  rw [show -(H / 2) + H = H / 2 from by ring, show (0:ℝ) + H = H from by ring] at h
  exact h

/-- **The perimeter tail asymptotics for the paper's own hairpin.**  Feeding the
constructed hairpin data in: for the periodization of the canonical steering
pulse, the rear half-perimeter functional
`P(H) = H - ∫_{-H/2}^{H/2} Φ(Y_H)` satisfies, past an explicit threshold,

`|P(H) - (H - Δ)| ≤ C e^{-βH}`,   `P'(H) = 1 + O(e^{-βH})`,

with `Δ = ∫_ℝ Φ(y) > 0` the hairpin defect.  This is the asymptotic pair of
Proposition *Exact two-cap pairs*, PRODUCED from the constructed hairpin
rather than assumed. -/
theorem hairpin_perimeter_tail_asymptotics (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ),
      0 < M ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
        |iteratedDeriv j (fun s => pulseField f (theta (x s))) s| ≤ D * Real.exp (-|s| / M)) ∧
      0 < Delta ∧ Delta = ∫ s : ℝ, Phi (pulseField f (theta (x s))) ∧
      0 < beta ∧ 0 ≤ C ∧ 0 < Ht ∧
      (∀ H, Ht ≤ H → |P H - (H - Delta)| ≤ C * Real.exp (-beta * H)) ∧
      (∀ H, Ht ≤ H → HasDerivAt P (Pp H) H) ∧
      (∀ H, Ht ≤ H → |Pp H - 1| ≤ C * Real.exp (-beta * H)) := by
  obtain ⟨theta, x, M, Δ, hM, hmem, hval, hderivθ, hxinv, hxderiv, hKdec, hydec, _hyint, hmass,
    hΔdef, hΔpos⟩ := exists_hairpin_pulse_package hf hfpos
  set y : ℝ → ℝ := fun s => pulseField f (theta (x s)) with hydef
  -- regularity of the pulse
  have hw : Continuous (fun s => theta (x s)) :=
    continuous_iff_continuousAt.2 fun s =>
      DifferentiableAt.continuousAt ((hxderiv s).differentiableAt)
  have hycont : Continuous y :=
    ((contDiff_pulseField hf hfpos).continuous).comp hw
  have hy0n : ∀ s, 0 ≤ y s := fun s =>
    pulseField_nonneg hfpos ⟨(hmem (x s)).1.le, (hmem (x s)).2.le⟩
  -- profile lower bound and sup bound `b`
  have hcontf : ContinuousOn f (Ioo 0 π) := hf.continuous.continuousOn
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hf.continuous.continuousOn
  have hm' : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  set b : ℝ := 1 / Real.sqrt (1 + f t₀ ^ 2) with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := inv_sqrt_one_add_sq_lt_one hm'
  have hlowC : ∀ t ∈ Icc (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ht
  have hsup : ∀ s, y s ≤ b := fun s =>
    pulseField_le_of_lower_bound hm' hfpos hlowC ⟨(hmem (x s)).1.le, (hmem (x s)).2.le⟩
  -- exponential decay of `y` and `y'`
  obtain ⟨C₀, hC₀0, hC₀b⟩ := hydec 0
  obtain ⟨D₁, hD₁0, hD₁b⟩ := hydec 1
  rw [iteratedDeriv_zero] at hC₀b
  set α : ℝ := 1 / M with hαdef
  have hαpos : 0 < α := by positivity
  -- derivative of `y`
  have hpdiff : Differentiable ℝ (pulseField f) :=
    (contDiff_pulseField hf hfpos).differentiable (by simp)
  set yp : ℝ → ℝ := fun s => deriv (pulseField f) (theta (x s)) * y s with hypdef
  have hyd : ∀ s, HasDerivAt y (yp s) s := by
    intro s
    have h1 : HasDerivAt (pulseField f) (deriv (pulseField f) (theta (x s)))
        (theta (x s)) := (hpdiff (theta (x s))).hasDerivAt
    simpa [hydef, hypdef, mul_comm] using h1.comp s (hxderiv s)
  have hypc : Continuous yp := by
    have hdc : Continuous (deriv (pulseField f)) :=
      (contDiff_pulseField hf hfpos).continuous_deriv (by simp)
    exact (hdc.comp hw).mul hycont
  -- one common exponential constant
  set C : ℝ := max C₀ D₁ with hCdef
  have hyb' : ∀ s, y s ≤ C * Real.exp (-|s| / M) := by
    intro s
    refine le_trans (le_abs_self _) ?_
    exact le_trans (hC₀b s)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  have hypb' : ∀ s, |yp s| ≤ C * Real.exp (-|s| / M) := by
    intro s
    have h1 : deriv y s = yp s := (hyd s).deriv
    calc |yp s| = |deriv y s| := by rw [h1]
      _ = |iteratedDeriv 1 y s| := by rw [iteratedDeriv_one]
      _ ≤ D₁ * Real.exp (-|s| / M) := hD₁b s
      _ ≤ C * Real.exp (-|s| / M) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  have hrewexp : ∀ s : ℝ, -|s| / M = -α * |s| := by
    intro s
    rw [hαdef]
    field_simp
  have hyb : ∀ s, y s ≤ C * Real.exp (-α * |s|) := fun s => by
    rw [← hrewexp s]; exact hyb' s
  have hyab : ∀ s, |y s| ≤ C * Real.exp (-α * |s|) := fun s => by
    rw [abs_of_nonneg (hy0n s)]; exact hyb s
  have hypb : ∀ s, |yp s| ≤ C * Real.exp (-α * |s|) := fun s => by
    rw [← hrewexp s]; exact hypb' s
  -- the periodization and the perimeter functional
  set β : ℝ := α / 4 with hβdef
  have hβlt : β < α / 2 := by linarith
  have hβpos : 0 < β := by positivity
  set T₀ : ℝ := threshold α C b with hT₀def
  have hCpos : 0 ≤ C := le_trans hC₀0 (le_max_left _ _)
  have hT₀pos : 0 < T₀ := threshold_pos hαpos hCpos hb1
  set YH : ℝ → ℝ → ℝ := fun H u => ∑' m : ℤ, y (u - m * H) with hYHdef
  set P : ℝ → ℝ := fun H => H - ∫ u in (-(H / 2))..(H / 2), Phi (YH H u) with hPdef
  -- periodicity and integrability of `Φ ∘ Y_H`
  have hYper : ∀ H : ℝ, Function.Periodic (fun u => Phi (YH H u)) H := by
    intro H u
    show Phi (∑' m : ℤ, y (u + H - m * H)) = Phi (∑' m : ℤ, y (u - m * H))
    congr 1
    exact periodic_tsum_translates y H u
  have hYcont : ∀ H : ℝ, 0 < H → Continuous (YH H) := fun H hH =>
    continuous_tsum_translates hαpos hH hycont hyab
  have hPhiYcont : ∀ H : ℝ, 0 < H → Continuous (fun u => Phi (YH H u)) := fun H hH =>
    continuous_Phi.comp (hYcont H hH)
  have hPhiYint : ∀ H : ℝ, 0 < H →
      IntervalIntegrable (fun u => Phi (YH H u)) volume (-(H / 2)) (H / 2) := by
    intro H hH
    exact ((hPhiYcont H hH).intervalIntegrable _ _)
  -- the centered cell integral equals the forward cell integral
  have hJcW : ∀ H : ℝ, 0 < H →
      ∫ u in (-(H / 2))..(H / 2), Phi (YH H u) = ∫ s in (0:ℝ)..H, Phi (YH H s) :=
    fun H hH => integral_center_eq_forward (hYper H) hH
  -- value clause translated onto `P`
  set Bval : ℝ := ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (4 * C)
      / ((α / 2 - β) * Real.exp 1) + 2 * C ^ 2 / α) with hBvaldef
  have hval' : ∀ H : ℝ, T₀ ≤ H → |P H - (H - Δ)| ≤ Bval * Real.exp (-β * H) := by
    intro H hH
    have hv := defect_value_clause_of_sup (y := y) (C := C) (alpha := α) (b := b)
      hαpos hb0 hb1 hycont hy0n hyb hsup hH hβlt
    rw [← hΔdef] at hv
    have hHpos : 0 < H := lt_of_lt_of_le hT₀pos hH
    have hintid : ∫ s in (0:ℝ)..H, Real.sqrt (1 - YH H s ^ 2)
        = H - ∫ s in (0:ℝ)..H, Phi (YH H s) := by
      have hpt : ∀ s : ℝ,
          Real.sqrt (1 - YH H s ^ 2) = (1:ℝ) - Phi (YH H s) := fun s => by
        show Real.sqrt (1 - YH H s ^ 2)
            = 1 - (1 - Real.sqrt (1 - YH H s ^ 2))
        ring
      have hc1 : IntervalIntegrable (fun _ => (1:ℝ)) volume (0:ℝ) H :=
        continuous_const.intervalIntegrable _ _
      have hc2 : IntervalIntegrable (fun s => Phi (YH H s)) volume (0:ℝ) H :=
        (hPhiYcont H hHpos).intervalIntegrable _ _
      rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x _ => hpt x),
        intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const]
      simp
    have hW : (H - ∫ s in (0:ℝ)..H, Real.sqrt (1 - YH H s ^ 2))
        = ∫ u in (-(H / 2))..(H / 2), Phi (YH H u) := by
      rw [hintid, hJcW H (lt_of_lt_of_le hT₀pos hH)]
      ring
    have heq : P H - (H - Δ)
        = -((H - ∫ s in (0:ℝ)..H, Real.sqrt (1 - YH H s ^ 2)) - Δ) := by
      rw [hPdef, hW]
      ring
    rw [heq, abs_neg]
    exact hv
  -- derivative clause
  have hid : ∀ H : ℝ, H - P H = ∫ u in (-(H / 2))..(H / 2), Phi (YH H u) := by
    intro H
    show H - (H - _) = _
    ring
  set Bder : ℝ := 25 * C ^ 2 + (1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2)
      * (8 * C) / ((α / 2 - β) * Real.exp 1) with hBderdef
  have hex : ∀ H : ℝ, 2 * T₀ ≤ H → ∃ p : ℝ, HasDerivAt P p H ∧
      |p - 1| ≤ Bder * Real.exp (-β * H) := by
    intro H hH
    exact perimeter_derivative_clause_of_sup (y := y) (yp := yp) (C := C) (alpha := α)
      (b := b) (P := P) (H0 := H) (beta' := β)
      hαpos hb1 hyd hypc hy0n hyb hypb hsup hH hβlt hid
  choose! pp hpp using hex
  have hab : 0 ≤ (1 + b) / 2 := by linarith
  have hden : 0 < Real.sqrt (1 - ((1 + b) / 2) ^ 2) := by
    have hq : (0:ℝ) < 1 - ((1 + b) / 2) ^ 2 := by nlinarith
    exact Real.sqrt_pos.mpr hq
  have h4C : 0 ≤ 4 * C := by linarith
  have h8C : 0 ≤ 8 * C := by linarith
  have hden2 : 0 ≤ (α / 2 - β) * Real.exp 1 :=
    mul_nonneg (by linarith) (Real.exp_nonneg 1)
  have hpiece : 0 ≤ (1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (4 * C)
      / ((α / 2 - β) * Real.exp 1) :=
    div_nonneg (mul_nonneg (div_nonneg hab hden.le) h4C) hden2
  have hBvpos : 0 ≤ Bval := by
    rw [hBvaldef]
    exact add_nonneg hpiece (div_nonneg (by linarith [sq_nonneg C]) hαpos.le)
  have hBdpos : 0 ≤ Bder := by
    rw [hBderdef]
    refine add_nonneg (by nlinarith [hCpos, sq_nonneg C]) ?_
    exact div_nonneg (mul_nonneg (div_nonneg hab hden.le) h8C) (by positivity)
  have hCnonneg : 0 ≤ max Bval Bder := hBvpos.trans (le_max_left Bval Bder)
  refine ⟨theta, x, M, Δ, β, max Bval Bder, 2 * T₀, P, pp, hM, hmem, hval, hderivθ,
    hxinv, hxderiv, hydec, hΔpos, hΔdef, hβpos, hCnonneg, by linarith, ?_,
    fun H hH => (hpp H hH).1, ?_⟩
  · intro H hH
    calc |P H - (H - Δ)| ≤ Bval * Real.exp (-β * H) := hval' H (by linarith)
      _ ≤ max Bval Bder * Real.exp (-β * H) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · intro H hH
    calc |pp H - 1| ≤ Bder * Real.exp (-β * H) := (hpp H hH).2
      _ ≤ max Bval Bder * Real.exp (-β * H) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-! ### The large-separation threshold from localized asymptotics

The produced perimeter asymptotics hold past an explicit threshold rather than
globally; this section mirrors the recursion/tail assembly of
`MainThresholds.lean` and `LargeSeparation.lean` under hypotheses localized
above a threshold. -/

section Synchronization

variable {P Pp : ℝ → ℝ} {Delta beta C : ℝ}

/-- Localized version of `MainThresholds.strictMonoOn_of_deriv_ge_half`. -/
theorem strictMonoOn_of_deriv_ge_half_loc {Hstar : ℝ}
    (hP : ∀ x, Hstar ≤ x → HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) :
    StrictMonoOn P (Ici Hstar) := by
  have hcont : ContinuousOn P (Ici Hstar) := fun x hx =>
    ((((hP x hx).differentiableAt).continuousAt).continuousWithinAt)
  apply strictMonoOn_of_deriv_pos (convex_Ici Hstar) hcont
  intro x hx
  rw [interior_Ici] at hx
  rw [(hP x (le_of_lt hx)).deriv]
  linarith [hPp x (le_of_lt hx)]

/-- Localized version of `MainThresholds.le_of_deriv_ge_half`. -/
theorem le_of_deriv_ge_half_loc {Hstar : ℝ}
    (hP : ∀ x, Hstar ≤ x → HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) {x : ℝ} (hx : Hstar ≤ x) :
    P Hstar + (x - Hstar) / 2 ≤ P x := by
  have hc : ContinuousOn P (Ici Hstar) := fun t ht =>
    ((((hP t ht).differentiableAt).continuousAt).continuousWithinAt)
  have hcont : ContinuousOn (fun t => P t - t / 2) (Ici Hstar) :=
    hc.sub (continuous_id.div_const 2).continuousOn
  have hmono : MonotoneOn (fun t => P t - t / 2) (Ici Hstar) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici Hstar) hcont
    · intro t ht
      rw [interior_Ici] at ht
      exact ((((hP t (le_of_lt ht)).differentiableAt).sub
        (((hasDerivAt_id t).div_const 2).differentiableAt)).differentiableWithinAt).mono
          (subset_univ _)
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun r => P r - r / 2) (Pp t - 1 / 2) t := by
        simpa using ((hP t (le_of_lt ht)).sub ((hasDerivAt_id t).div_const 2))
      rw [hd.deriv]
      linarith [hPp t (le_of_lt ht)]
  have h := hmono (Set.self_mem_Ici) (mem_Ici.mpr hx) hx
  simp only at h
  linarith

/-- Localized version of `MainThresholds.existsUnique_recursion_step`. -/
theorem existsUnique_recursion_step_loc {Hstar : ℝ}
    (hP : ∀ x, Hstar ≤ x → HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) {t : ℝ} (ht : P Hstar ≤ t) :
    ∃! x, Hstar ≤ x ∧ P x = t := by
  set b : ℝ := Hstar + 2 * (t - P Hstar) with hb
  have hbge : Hstar ≤ b := by simp only [hb]; linarith
  have hPb : t ≤ P b := by
    have h := le_of_deriv_ge_half_loc hP hPp hbge
    simp only [hb] at h ⊢
    linarith
  have hcI : ContinuousOn P (Ici Hstar) := fun x hx =>
    ((((hP x hx).differentiableAt).continuousAt).continuousWithinAt)
  have hc : ContinuousOn P (Icc Hstar b) := hcI.mono Icc_subset_Ici_self
  have hsub : Icc (P Hstar) (P b) ⊆ P '' Icc Hstar b :=
    intermediate_value_Icc hbge hc
  obtain ⟨x, hx, hxt⟩ := hsub ⟨ht, hPb⟩
  refine ⟨x, ⟨hx.1, hxt⟩, ?_⟩
  rintro y ⟨hy, hyt⟩
  have hmono := strictMonoOn_of_deriv_ge_half_loc hP hPp
  exact hmono.injOn (mem_Ici.mpr hy) (mem_Ici.mpr hx.1) (by rw [hyt, hxt])

/-- Localized version of `LargeSeparation.exists_cap_sequence`. -/
theorem exists_cap_sequence_loc {Hs H0 : ℝ} (hDelta : 0 < Delta)
    (hd : ∀ H, Hs ≤ H → HasDerivAt P (Pp H) H)
    (hPp : ∀ H, Hs ≤ H → 1 / 2 ≤ Pp H)
    (hPle : ∀ H, Hs ≤ H → P H ≤ H - Delta / 2)
    (hH0 : Hs ≤ H0) :
    ∃ H : ℕ → ℝ, H 0 = H0 ∧ (∀ n, Hs ≤ H n) ∧ (∀ n, P (H (n + 1)) = H n) ∧
      (∀ n : ℕ, H0 + Delta / 2 * n ≤ H n) := by
  have step : ∀ t : ℝ, ∃ x : ℝ, Hs ≤ t → (Hs ≤ x ∧ P x = t) := by
    intro t
    by_cases ht : Hs ≤ t
    · have hPHs : P Hs ≤ t := by
        have h := hPle Hs le_rfl
        linarith
      obtain ⟨x, hx, -⟩ := existsUnique_recursion_step_loc hd hPp hPHs
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose G hG using step
  set H : ℕ → ℝ := fun n => Nat.rec H0 (fun _ x => G x) n with hHdef
  have hstep : ∀ n, H (n + 1) = G (H n) := fun n => rfl
  have hmem : ∀ n, Hs ≤ H n := by
    intro n
    induction n with
    | zero => exact hH0
    | succ k ih =>
      rw [hstep k]
      exact (hG (H k) ih).1
  have hrec : ∀ n, P (H (n + 1)) = H n := by
    intro n
    rw [hstep n]
    exact (hG (H n) (hmem n)).2
  refine ⟨H, rfl, hmem, hrec, ?_⟩
  intro n
  have h := MainThresholds.recursion_growth (P := P) (Hstar := Hs) (Delta := Delta)
    hPle hmem hrec n
  simpa using h

/-- Clause (i) of the large-separation threshold under asymptotics localized
above `Ht`. -/
theorem exists_threshold_asymptotics_loc {Ht : ℝ}
    (hDelta : 0 < Delta) (hbeta : 0 < beta)
    (hd : ∀ H, Ht ≤ H → HasDerivAt P (Pp H) H)
    (hP : ∀ H, Ht ≤ H → |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, Ht ≤ H → |Pp H - 1| ≤ C * Real.exp (-beta * H)) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ Ht ≤ Hs ∧
      (∀ H, Hs ≤ H → 1 / 2 ≤ Pp H) ∧
      (∀ H, Hs ≤ H → P H ≤ H - Delta / 2) ∧ StrictMonoOn P (Ici Hs) := by
  obtain ⟨A, hA0, hA⟩ := exists_exp_threshold (C := C) hbeta
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨B, hB0, hB⟩ := exists_exp_threshold (C := C) hbeta
    (by linarith : (0:ℝ) < Delta / 2)
  have hAHs : ∀ H', max (max A B) Ht ≤ H' → A ≤ H' := fun H' hH' =>
    le_trans (le_trans (le_max_left A B) (le_max_left (max A B) Ht)) hH'
  have hBHs : ∀ H', max (max A B) Ht ≤ H' → B ≤ H' := fun H' hH' =>
    le_trans (le_trans (le_max_right A B) (le_max_left (max A B) Ht)) hH'
  have hTHs : ∀ H', max (max A B) Ht ≤ H' → Ht ≤ H' := fun H' hH' =>
    le_trans (le_max_right (max A B) Ht) hH'
  refine ⟨max (max A B) Ht,
    le_trans hA0 (le_trans (le_max_left A B) (le_max_left (max A B) Ht)),
    le_max_right (max A B) Ht, ?_, ?_, ?_⟩
  · intro H hH
    have h1 := hA H (hAHs H hH)
    have h2 := (abs_le.mp (hPp H (hTHs H hH))).1
    linarith
  · intro H hH
    have h1 := hB H (hBHs H hH)
    have h2 := (abs_le.mp (hP H (hTHs H hH))).2
    linarith
  · refine strictMonoOn_of_deriv_ge_half_loc (fun x hx => hd x (hTHs x hx)) ?_
    intro H hH
    have h1 := hA H (hAHs H hH)
    have h2 := (abs_le.mp (hPp H (hTHs H hH))).1
    linarith

/-- **The synchronized tail of the cap sequence, from the perimeter
asymptotics.**  Localized version of
`LargeSeparation.exists_large_separation_threshold`: the asymptotics
`P(H) = H - Δ + O(e^{-βH})`, `P'(H) = 1 + O(e^{-βH})` are required only above
an explicit threshold `Ht`, matching what `hairpin_perimeter_tail_asymptotics`
produces. -/
theorem synchronization_tail_of_perimeter_asymptotics
    {Cr eta Cw Csh beta' Ht : ℝ}
    (hDelta : 0 < Delta) (hbeta : 0 < beta) (hbeta' : 0 < beta') (heta : 0 < eta)
    (hd : ∀ H, Ht ≤ H → HasDerivAt P (Pp H) H)
    (hP : ∀ H, Ht ≤ H → |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, Ht ≤ H → |Pp H - 1| ≤ C * Real.exp (-beta * H)) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ H0, Hs ≤ H0 →
      ((∀ H, H0 ≤ H → 1 / 2 ≤ Pp H ∧ P H ≤ H - Delta / 2) ∧
        StrictMonoOn P (Ici H0) ∧
        ∃ H : ℕ → ℝ, H 0 = H0 ∧ (∀ n, H0 ≤ H n) ∧ (∀ n, P (H (n + 1)) = H n) ∧
          (∀ n : ℕ, H0 + Delta / 2 * n ≤ H n)) ∧
      Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)) ≤ eta ∧
      Cw + 2 * Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))
        < (2 * H0 - Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))) / Real.pi := by
  obtain ⟨S, hS0, hSHt, hA1, hA2, hmono⟩ :=
    exists_threshold_asymptotics_loc hDelta hbeta hd hP hPp
  set r : ℝ → ℝ := fun x => Cr * ((1 + x) ^ 2 * Real.exp (-beta' * x)) with hr
  have hrzero : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_tail_zero (beta := beta') hbeta').const_mul Cr
    simpa [hr] using h
  have hsmall : ∀ᶠ x in atTop, r x ≤ eta := by
    have h := hrzero.eventually (gt_mem_nhds heta)
    filter_upwards [h] with x hx using hx.le
  have hgap : ∀ᶠ x in atTop, Cw + 2 * Csh * r x < (2 * x - Csh * r x) / Real.pi :=
    eventually_width_gap (Cw := Cw) (Csh := Csh) hrzero
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp (hsmall.and hgap)
  refine ⟨max S (max B 0),
    le_trans (le_max_right B 0) (le_max_right S _), ?_⟩
  intro H0 hH0
  have hSH0 : S ≤ H0 := le_trans (le_max_left S (max B 0)) hH0
  have hBH0 : B ≤ H0 := le_trans (le_trans (le_max_left B 0) (le_max_right S _)) hH0
  obtain ⟨hsm, hgp⟩ := hB H0 hBH0
  refine ⟨⟨fun H hH => ⟨hA1 H (le_trans hSH0 hH), hA2 H (le_trans hSH0 hH)⟩, ?_, ?_⟩,
    hsm, hgp⟩
  · refine strictMonoOn_of_deriv_ge_half_loc
      (fun x hx => hd x (le_trans hSHt (le_trans hSH0 hx))) ?_
    intro H hH
    exact hA1 H (le_trans hSH0 hH)
  · exact exists_cap_sequence_loc hDelta
      (fun x hx => hd x (le_trans hSHt (le_trans hSH0 hx)))
      (fun H hH => hA1 H (le_trans hSH0 hH))
      (fun H hH => hA2 H (le_trans hSH0 hH)) le_rfl

end Synchronization

end HairpinAsymptoticsComplete
