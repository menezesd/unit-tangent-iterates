import Mathlib
import UnitTangentIterates.ModelConfigInstance
import UnitTangentIterates.ModelPeriodContinuity
import UnitTangentIterates.ModelPeriodGrowth

/-!
# The model pseudo-orbit: a whole family of matching configurations

`ModelConfigInstance.lean` produces one matching configuration for every
separation `H` beyond an explicit threshold, all of them with the *same*
constants, from one pulse of the isolated pair.  The defect estimate along the
model pseudo-orbit (`ModelOrbitDefect.pathDistRigid_selInv_model_orbit`) asks
for more: a *sequence* of configurations tied by the recursion
`P(H_{n+1}) = H_n` of the lemma *Large-separation threshold*, the rear period of
the `(n+1)`-st being the front period of the `n`-th.

`ModelPeriodContinuity.lean` solves that recursion — the rear period is
continuous in the separation and lies between `H/2` and `H` — so the recursion
can be run from any admissible `H₀`.

Main results:

* `exists_config_family` — a sequence of separations, increasing from `H₀`, and
  a matching configuration of separation `H_{n+1}` whose rear period is exactly
  `H_n`, all with the same constants;
* `exists_pathDistRigid_model_orbit` — hence the defect estimate along the model
  pseudo-orbit is not vacuous;
* `nonempty_config_family` — a concrete family, with `λ = 1/100` and
  `H₀ = 3200`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace ModelConfigFamily

open ModelOrbitDefect ModelConfigInstance ModelPeriodContinuity ModelPeriodGrowth SechHairpin
open MarkedSpace PathMetric CurvatureInterpolation RearTrack TwoCapPairsAssembly
open InterpolationPathDistSummable MarkedRigid

variable {lam : ℝ}

/-- **A family of matching configurations along the orbit recursion.**  All the
configurations share the constants of the estimate; the rear period of the
configuration of separation `H_{n+1}` is exactly the separation `H_n` of the
previous one. -/
theorem exists_config_family (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (theta0 : ℝ)
    {H0 : ℝ} (hH0 : 0 < H0) (hthr : Real.exp (-(lam / 8) * H0) ≤ 1 / 8) :
    ∃ (alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd Delta : ℝ) (Hs : ℕ → ℝ),
      0 < Delta ∧ Hs 0 = H0 ∧ (∀ n, H0 + n * Delta ≤ Hs n) ∧
      (∀ n, Hs n + Delta ≤ Hs (n + 1)) ∧
      ∀ n, Nonempty (Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd
        (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * Hs (n + 1))))
        (Hs (n + 1)) (Hs n)) := by
  have hA0 : 0 < amp lam := amp_pos hlam
  have hA50 : amp lam ≤ 1 / 50 := amp_le hlam hlam'
  obtain ⟨y, yd, x, hx0, hy0, hyKm, hyc, hydc, hyderiv, hyb, hydb, hrelD, hxint, hidx,
      hyint, hymass⟩ :=
    PulseFromCurvature.exists_pulse_of_curvature (K := curv lam) (K' := curvD lam)
      (Km := 2 * amp lam) (alpha := 2 * lam) (CK := 8 * amp lam)
      (CK1 := 12 * lam * amp lam) (DK := 6 * lam)
      (continuous_curv hlam hlam') (continuous_curvD hlam hlam')
      (fun u => hasDerivAt_curv hlam hlam' u) (fun u => curv_nonneg hlam hlam' u)
      (fun u => curv_le hlam hlam' u) (by positivity) (by positivity)
      (fun u => curv_le_exp hlam hlam' u) (by positivity)
      (fun u => abs_curvD_le_exp hlam hlam' u) (by positivity)
      (fun u => abs_curvD_le_curv hlam hlam' u) (integrable_curv hlam hlam')
  have hratedef : 2 * lam / Real.sqrt (1 + (2 * amp lam) ^ 2) = rate lam := rfl
  rw [hratedef] at hyb hydb
  have ha : 0 < rate lam := rate_pos hlam hlam'
  -- the two decay bounds, with a common constant
  have hzb : ∀ s, |y s| ≤ 8 * amp lam * Real.exp (-rate lam * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hz'b : ∀ s, |yd s| ≤ 8 * amp lam * Real.exp (-rate lam * |s|) := fun s => by
    refine le_trans (hydb s) ?_
    have h1 : 12 * lam * amp lam ≤ 8 * amp lam := by nlinarith
    have h2 : (0:ℝ) < Real.exp (-rate lam * |s|) := Real.exp_pos _
    nlinarith
  -- the configurations, with constants uniform in the separation
  obtain ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, hcfg⟩ :=
    exists_config_of_pulse hlam hlam' theta0 y yd x hy0 hyKm hyc hydc hyderiv hyb hydb
      hrelD hxint hidx hyint hymass
  -- the threshold is inherited by every larger separation
  have hthrH : ∀ H : ℝ, H0 ≤ H → Real.exp (-(lam / 8) * H) ≤ 1 / 8 := by
    intro H hH
    refine le_trans (Real.exp_le_exp.mpr ?_) hthr
    nlinarith [hlam.le]
  -- one step of the recursion
  have step : ∀ t : ℝ, ∃ H, H0 ≤ t → (t ≤ H ∧ rearPeriod y H = t) := by
    intro t
    by_cases ht : H0 ≤ t
    · have ht0 : 0 < t := lt_of_lt_of_le hH0 ht
      have h2 : t ≤ rearPeriod y (2 * t) := by
        have h := (hcfg (2 * t) (by linarith) (hthrH _ (by linarith))).2.1
        have : rearPeriod y (2 * t) = modelRearArclength (periodizedPulse y (2 * t)) (2 * t) :=
          rfl
        rw [this]
        linarith
      obtain ⟨H, h1, -, h3⟩ :=
        exists_rearPeriod_eq (y' := yd) ha hyc hyderiv hzb hz'b h2 ht0
      exact ⟨H, fun _ => ⟨h1, h3⟩⟩
    · exact ⟨H0, fun h => absurd h ht⟩
  choose g hg using step
  -- the perimeter defect of one period, bounded below
  have hsqint : Integrable fun s => y s ^ 2 := by
    have hmaj : Integrable fun s : ℝ =>
        (2 * amp lam * (8 * amp lam)) * Real.exp (-rate lam * |s|) :=
      (SechPulse.integrable_exp_neg_abs ha).const_mul _
    refine Integrable.mono' hmaj ((hyc.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hy0 s
    have h2 := hyKm s
    have h3 : y s ≤ 8 * amp lam * Real.exp (-rate lam * |s|) := hyb s
    nlinarith [Real.exp_pos (-rate lam * |s|), hA0]
  have hy0pos : 0 < y 0 := by
    have hcurv0 : curv lam 0 = amp lam := by
      simp [curv, pul, pulD, SechPulse.pulse, SechPulse.pulseD]
    have hx00 : x 0 = 0 := hx0
    have hid0 := hidx 0
    rw [hx00, hcurv0] at hid0
    rcases (hy0 0).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hid0
      simp at hid0
      linarith [hA0, hid0]
  have hDelta : 0 < (∫ s, y s ^ 2) / 2 := by
    have hpos : 0 < ∫ s, y s ^ 2 := by
      rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun s => sq_nonneg _) hsqint]
      have hopen : IsOpen (Function.support fun s => y s ^ 2) := (hyc.pow 2).isOpen_support
      refine hopen.measure_pos volume ⟨0, ?_⟩
      simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
        not_false_eq_true]
      exact ne_of_gt hy0pos
    linarith
  have hgrow : ∀ H : ℝ, H0 ≤ H → rearPeriod y H ≤ H - (∫ s, y s ^ 2) / 2 := by
    intro H hH
    have hHpos : 0 < H := lt_of_lt_of_le hH0 hH
    have hYle := (hcfg H hHpos (hthrH _ hH)).1
    refine rearPeriod_le_sub (alpha := rate lam) (C := 8 * amp lam) (Km := 2 * amp lam)
      ha hyc hy0 hyKm hzb hsqint hHpos (fun s => le_trans (hYle s) (by norm_num))
  -- the sequence of separations
  have hn : ∀ n, H0 ≤ g^[n] H0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans ih (hg _ ih).1
  have hstep : ∀ n, g^[n] H0 + (∫ s, y s ^ 2) / 2 ≤ g^[n + 1] H0 := fun n => by
    have hper : rearPeriod y (g^[n + 1] H0) = g^[n] H0 := by
      rw [Function.iterate_succ_apply']
      exact (hg _ (hn n)).2
    have hn1 : H0 ≤ g^[n + 1] H0 := by
      rw [Function.iterate_succ_apply']
      exact le_trans (hn n) (hg _ (hn n)).1
    have := hgrow (g^[n + 1] H0) hn1
    rw [hper] at this
    linarith
  have hlin : ∀ n : ℕ, H0 + n * ((∫ s, y s ^ 2) / 2) ≤ g^[n] H0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have := hstep n
        push_cast
        push_cast at ih
        nlinarith
  refine ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd,
    (∫ s, y s ^ 2) / 2, fun n => g^[n] H0, hDelta, by simp, hlin, hstep, fun n => ?_⟩
  have hn1 : H0 ≤ g^[n + 1] H0 := by
    rw [Function.iterate_succ_apply']
    exact le_trans (hn n) (hg _ (hn n)).1
  have hc := (hcfg (g^[n + 1] H0) (lt_of_lt_of_le hH0 hn1) (hthrH _ hn1)).2.2
  have hper : rearPeriod y (g^[n + 1] H0) = g^[n] H0 := by
    rw [Function.iterate_succ_apply']
    exact (hg _ (hn n)).2
  have heq : modelRearArclength (periodizedPulse y (g^[n + 1] H0)) (g^[n + 1] H0)
      = g^[n] H0 := hper
  rwa [heq] at hc

/-- **The defect estimate along the model pseudo-orbit is not vacuous.**  For a
whole sequence of configurations tied by the orbit recursion, the marked
selected inverse of the `(n+1)`-st model front and the `n`-th model are within
the interpolation cost of the matching bound. -/
theorem exists_pathDistRigid_model_orbit (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100)
    (theta0 : ℝ) {H0 : ℝ} (hH0 : 0 < H0) (hthr : Real.exp (-(lam / 8) * H0) ≤ 1 / 8) :
    ∃ (alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd Delta : ℝ) (Hs : ℕ → ℝ)
      (cfg : ∀ n, Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd
        (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * Hs (n + 1))))
        (Hs (n + 1)) (Hs n)),
      0 < Delta ∧ Hs 0 = H0 ∧ (∀ n, H0 + n * Delta ≤ Hs n) ∧
      ∀ n, ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * Hs n) ∧
        ∀ p' q' : Data,
          (∀ u, p'.1 u = rearTrack ((cfg n).frontCurve (theta0 := theta0))
            ((cfg n).frontTangentAngle (theta0 := theta0)) (modelSteering (cfg n).Y)
            ((cfg n).sf (2 * Hs n * u))) →
          (∀ u, q'.1 u = interpCurve (modelCurvature (cfg n).yu (cfg n).yu' (Hs n))
            theta0 (Hs n) (psi u)) →
          pathDistRigid p' q' ≤ interpCostL1 kstar kd (Hs n)
            (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * Hs (n + 1))))
            (matchConst a C CK CU DU Km Kd au alpha beta B
              * Real.exp (-(beta * Hs (n + 1)))) := by
  obtain ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, Delta, Hs,
    hDelta, h0, hge, -, hcfg⟩ := exists_config_family hlam hlam' theta0 hH0 hthr
  refine ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, Delta, Hs,
    fun n => Classical.choice (hcfg n), hDelta, h0, hge, ?_⟩
  intro n
  exact pathDistRigid_selInv_model_orbit
    (eps0 := fun n => matchConst a C CK CU DU Km Kd au alpha beta B
      * Real.exp (-(beta * Hs (n + 1))))
    (fun n => Classical.choice (hcfg n)) n

/-- **A concrete family**, with `λ = 1/100` and first separation `H₀ = 3200`. -/
theorem nonempty_config_family (theta0 : ℝ) :
    ∃ (alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd Delta : ℝ) (Hs : ℕ → ℝ),
      0 < Delta ∧ Hs 0 = 3200 ∧ (∀ n, 3200 + n * Delta ≤ Hs n) ∧
      (∀ n, Hs n + Delta ≤ Hs (n + 1)) ∧
      ∀ n, Nonempty (Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd
        (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * Hs (n + 1))))
        (Hs (n + 1)) (Hs n)) :=
  exists_config_family (lam := 1 / 100) (by norm_num) (by norm_num) theta0 (by norm_num)
    (by
      have h : Real.exp (-(1 / 100 / 8) * 3200) = Real.exp (-4) := by norm_num
      rw [h]; exact exp_neg_four_le)

end ModelConfigFamily
