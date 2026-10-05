module

public import UnitTangentIterates.Shadowing
public import UnitTangentIterates.Pulse
public import UnitTangentIterates.ModelDefects
public import UnitTangentIterates.CurvatureBound
public import UnitTangentIterates.WidthBound
public import UnitTangentIterates.PulseAux

/-!
# Section 7: assembling the closed models into a chain for Theorem 6.4

From the pulse of the translating hairpin (Lemma 3.5, `pulse_exists`) we build the closed
pairs `𝒯 R_H = F_H` (Proposition 4.3), choose the period sequence `P(H_{n+1}) = H_n`, and
check that the fronts `Q_n = F_{H_n}` and rears `A_n = R_{H_{n+1}}` form a model chain
(`Ovals.ModelChain`) with curvatures at most `1/10`, defects summing to at most `C e^{-βH₀}`
(estimate (7.2)), and widths bounded independently of `n` (Lemma 4.4).  Theorem 6.4
(`backward_shadowing`) then yields a thin orbit of ovals.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology MeasureTheory

/-- The curvature of the closed rear as a function of its own arclength.  If `0 < Y < 1` is
continuous and `H`-periodic, then `x(s) = x₀ + ∫₀ˢ √(1 - Y²)` is a bijection, and the function
`k` with `k(x(s)) = Y(s) / √(1 - Y(s)²)` is continuous, periodic with period
`P = ∫₀ᴴ √(1 - Y²)`, and `∫₀ᴾ k = ∫₀ᴴ Y`. -/
theorem rear_curvature_function {Y : ℝ → ℝ} {H : ℝ} (hH : 0 < H) (hYc : Continuous Y)
    (hYp : Function.Periodic Y H) (hY01 : ∀ s, 0 < Y s ∧ Y s < 1) (x₀ : ℝ) :
    ∃ k : ℝ → ℝ, Continuous k ∧
      Function.Periodic k (∫ s in (0 : ℝ)..H, √(1 - Y s ^ 2)) ∧
      (∫ x in (0 : ℝ)..(∫ s in (0 : ℝ)..H, √(1 - Y s ^ 2)), k x) = ∫ s in (0 : ℝ)..H, Y s ∧
      (∀ x, ∃ s, k x = Y s / √(1 - Y s ^ 2)) ∧
      ∀ s, k (x₀ + ∫ r in (0 : ℝ)..s, √(1 - Y r ^ 2)) = Y s / √(1 - Y s ^ 2) := by
  set c : ℝ → ℝ := fun s => √(1 - Y s ^ 2) with hcdef
  have hcc : Continuous c := by fun_prop
  have hcp : Function.Periodic c H := fun s => by simp only [hcdef, hYp s]
  -- a positive lower bound for `c`
  obtain ⟨t₀, ht₀⟩ := exists_max_of_periodic hH hYc hYp
  set c₀ : ℝ := √(1 - Y t₀ ^ 2) with hc₀
  have hc₀pos : 0 < c₀ := Real.sqrt_pos.2 (by nlinarith [hY01 t₀])
  have hcge : ∀ s, c₀ ≤ c s := fun s => by
    apply Real.sqrt_le_sqrt
    nlinarith [hY01 s, ht₀ s, hY01 t₀]
  set xf : ℝ → ℝ := fun s => x₀ + ∫ r in (0 : ℝ)..s, c r with hxf
  have hxd : ∀ s, HasDerivAt xf (c s) s := fun s =>
    ((hcc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add x₀
  obtain ⟨Xi, hxXi, hXix, hXid⟩ := exists_inverse_of_deriv_ge hc₀pos hxd hcge
  have hXic : Continuous Xi := continuous_iff_continuousAt.2 fun x => (hXid x).continuousAt
  set P : ℝ := ∫ s in (0 : ℝ)..H, c s with hP
  have hxper : ∀ s, xf (s + H) = xf s + P := fun s => by
    simp only [hxf]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hcc.intervalIntegrable _ _)
      (hcc.intervalIntegrable _ _), hcp.intervalIntegral_add_eq s 0, zero_add]
    ring
  set k : ℝ → ℝ := fun x => Y (Xi x) / c (Xi x) with hkdef
  have hkx : ∀ s, k (xf s) = Y s / c s := fun s => by simp only [hkdef, hXix]
  have hkc : Continuous k :=
    (hYc.comp hXic).div (hcc.comp hXic) fun x => (lt_of_lt_of_le hc₀pos (hcge _)).ne'
  have hkp : Function.Periodic k P := fun x => by
    have e : x + P = xf (Xi x + H) := by rw [hxper, hxXi]
    rw [e, hkx, ← hxXi x, hkx, hXix, hYp, hcp]
  refine ⟨k, hkc, hkp, ?_, fun x => ⟨Xi x, rfl⟩, hkx⟩
  -- the mass identity, by the change of variables `x = xf s`
  have h1 : ∫ x in (0 : ℝ)..P, k x = ∫ x in xf 0..xf 0 + P, k x := by
    rw [hkp.intervalIntegral_add_eq (xf 0) 0, zero_add]
  have h2 : xf 0 + P = xf H := by rw [← hxper, zero_add]
  have h3 : ∫ x in xf 0..xf H, k x = ∫ s in (0 : ℝ)..H, (k ∘ xf) s * c s :=
    (intervalIntegral.integral_comp_mul_deriv (fun s _ => hxd s) (hcc.continuousOn)
      hkc).symm
  rw [h1, h2, h3]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Function.comp, hkx]
  have : 0 < c s := lt_of_lt_of_le hc₀pos (hcge s)
  field_simp

/-- **A thin orbit of ovals** (Section 7).  The closed models built from the translating
hairpin form a model chain with small total defect and uniformly bounded widths, so Theorem 6.4
yields an orbit of ovals of `𝒯`, up to reparametrization, all lying in strips of one common
width. -/
theorem exists_ovalOrbit_bounded_width :
    ∃ (X : ℕ → ℝ → ℂ) (p : ℕ → ℝ) (ψ : ℕ → ℝ → ℝ) (W : ℝ), IsOvalOrbit X p ψ ∧
      ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ t t', coord v (X n t - X n t') ≤ W := by
  obtain ⟨y, y', y'', A, a, D, b, b₀, x₀, hy, hy', hypos, hyA, ha, hyD, hyD2, hyb, hb, hmass,
    hb₀, hK, hKx, hKF, hKR⟩ := pulse_exists
  have hy0 : ∀ t, 0 ≤ y t := fun t => (hypos t).le
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hexp : ∀ {u : ℝ → ℝ}, (∀ t, |u t| ≤ D * y t) →
      ∀ t, |u t| ≤ (|D| * A) * exp (-(a * |t|)) := fun {u} hu t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hu t]
  have hy'A := hexp hyD
  have hy''A := hexp hyD2
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  obtain ⟨H₁, hcurv⟩ := periodized_curvature_le hy hy0 hyA ha hyD hyb hb
    (show (1 / 20 : ℝ) < 1 / 10 by norm_num) hKF hKR
  obtain ⟨H₂, hpair⟩ :=
    periodized_closed_pair 0 hy hy' hypos hyA ha hyD hyD2 hyb hb hmass hb₀ hK
  obtain ⟨Cw, H₃, hwidth⟩ :=
    periodized_width_bounded 0 hy hy' hypos hyA ha hyD hyD2 hyb hb hmass hb₀ hK
  obtain ⟨Cd, β, H₄, hβ, hdef⟩ :=
    model_defects_small hy hy' hy0 hyA ha hyD hyD2 hyb hb x₀ hKx (hypos 0)
  obtain ⟨η, hη, hshadow⟩ := backward_shadowing (κ₀ := 1 / 10) (by norm_num) (by norm_num)
  have hev : ∀ᶠ H in atTop, Cd * exp (-(β * H)) ≤ η := by
    have ht : Tendsto (fun H : ℝ => Cd * exp (-(β * H))) atTop (𝓝 (Cd * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hβ)).const_mul _
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds hη)
  obtain ⟨H₅, hH₅⟩ := eventually_atTop.1 hev
  set H₀ : ℝ := max (max (max H₁ H₂) (max H₃ H₄)) (max H₅ (2 / a)) with hH₀def
  have hH₀1 : H₁ ≤ H₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hH₀2 : H₂ ≤ H₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hH₀3 : H₃ ≤ H₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hH₀4 : H₄ ≤ H₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hH₀5 : H₅ ≤ H₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hH₀a : 2 / a ≤ H₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hH₀pos : 0 < H₀ := lt_of_lt_of_le (by positivity) hH₀a
  obtain ⟨Hs, -, hrec, hdefs⟩ := hdef H₀ hH₀4
  have hΔ : 0 ≤ steeringDefect y := integral_nonneg fun t => by
    have : √(1 - y t ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (y t)])
    simp only [Pi.zero_apply]; linarith
  have hHs : ∀ n, H₀ ≤ Hs n := fun n => by
    have : (0 : ℝ) ≤ steeringDefect y / 2 * n := by positivity
    linarith [(hrec n).2]
  have hper : ∀ (g : ℝ → ℝ) (H : ℝ), Function.Periodic (periodize g H) H := fun g H s => by
    have := periodize_sub_int_mul g H (s + H) 1
    simp only [Int.cast_one, one_mul, add_sub_cancel_right] at this
    exact this.symm
  -- facts about the closed pair of period `H ≥ H₀`
  have front : ∀ H, H₀ ≤ H →
      Continuous (frontCurv (periodize y H)) ∧ Function.Periodic (frontCurv (periodize y H)) H ∧
      (∫ s in (0 : ℝ)..H, frontCurv (periodize y H) s) = π ∧
      (∀ s, 0 < frontCurv (periodize y H) s ∧ frontCurv (periodize y H) s ≤ 1 / 10) ∧
      (∀ s, 0 < periodize y H s ∧ periodize y H s < 1) ∧
      (∀ s, periodize y H s / √(1 - periodize y H s ^ 2) ≤ 1 / 10) ∧
      Continuous (periodize y H) ∧
      (∀ s, HasDerivAt (periodizedAngle y H)
        (frontCurv (periodize y H) s - Real.sin (periodizedAngle y H s)) s) ∧
      (∀ s, periodizedAngle y H s ∈ Set.Ioo 0 (π / 2)) ∧
      Function.Periodic (periodizedAngle y H) H ∧
      (∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (frontCurv (periodize y H)) H s -
        curveOfCurvature 0 (frontCurv (periodize y H)) H s') ≤ Cw) := by
    intro H hH
    have hH0 : 0 < H := hH₀pos.trans_le hH
    set Y := periodize y H with hYdef
    have hYp : Function.Periodic Y H := hper y H
    have hYd : ∀ s, HasDerivAt Y (periodize y' H s) s :=
      hasDerivAt_periodize hy hyA' hy'A ha hH0
    have hY'd : ∀ s, HasDerivAt (periodize y' H) (periodize y'' H s) s :=
      hasDerivAt_periodize hy' hy'A hy''A ha hH0
    have hYc : Continuous Y := continuous_iff_continuousAt.2 fun s => (hYd s).continuousAt
    have hY'c : Continuous (periodize y' H) :=
      continuous_iff_continuousAt.2 fun s => (hY'd s).continuousAt
    obtain ⟨hY01, -, -, -, hF, -⟩ := hpair H (hH₀2.trans hH)
    have hsq : ∀ s, 0 < 1 - Y s ^ 2 := fun s => by nlinarith [(hY01 s).1, (hY01 s).2]
    have hKeq : frontCurv Y = fun s => Y s + periodize y' H s / √(1 - Y s ^ 2) :=
      funext fun s => by rw [frontCurv, (hYd s).deriv]
    have hKc : Continuous (frontCurv Y) := by
      rw [hKeq]
      exact hYc.add (hY'c.div (by fun_prop) fun s => (Real.sqrt_pos.2 (hsq s)).ne')
    have hKp : Function.Periodic (frontCurv Y) H := fun s => by
      rw [hKeq]; simp only [hYp s, hper y' H s]
    have hsin : ∀ s, Real.sin (periodizedAngle y H s) = Y s := fun s =>
      Real.sin_arcsin (by linarith [(hY01 s).1]) (hY01 s).2.le
    have hδ : ∀ s, HasDerivAt (periodizedAngle y H) (periodizedAngleDeriv y y' H s) s := by
      intro s
      have h := (Real.hasDerivAt_arcsin (by linarith [(hY01 s).1]) (hY01 s).2.ne).comp s (hYd s)
      unfold periodizedAngle periodizedAngleDeriv
      convert h using 1
      rw [← hYdef]; ring
    have hδ'c : Continuous (periodizedAngleDeriv y y' H) := by
      unfold periodizedAngleDeriv
      exact hY'c.div (Real.continuous_sqrt.comp (continuous_const.sub (hYc.pow 2)))
        (fun s => (Real.sqrt_pos.2 (hsq s)).ne')
    have hδp : Function.Periodic (periodizedAngle y H) H := fun s => by
      unfold periodizedAngle; rw [← hYdef, hYp s]
    have hpc : frontCurv Y = pairCurvature (periodizedAngle y H) (periodizedAngleDeriv y y' H) :=
      funext fun s => by
        rw [hKeq]; simp only [pairCurvature, hsin, periodizedAngleDeriv]; rw [← hYdef]; ring
    have hYint : ∫ s in (0 : ℝ)..H, Y s = π := by
      rw [hYdef, integral_periodize hyc hyA' ha hH0, hmass]
    have hKint : ∫ s in (0 : ℝ)..H, frontCurv Y s = π := by
      rw [hpc, integral_pairCurvature hδ hδ'c hδp]; simp_rw [hsin]; exact hYint
    have hKpos : ∀ s, 0 < frontCurv Y s := fun s => by
      have := (hF s).2.2; rwa [(hF s).2.1] at this
    refine ⟨hKc, hKp, hKint, fun s => ⟨hKpos s, (hcurv H (hH₀1.trans hH) s).1⟩, hY01,
      fun s => (hcurv H (hH₀1.trans hH) s).2, hYc, fun s => ?_, fun s => ?_, hδp, ?_⟩
    · convert hδ s using 1
      rw [hsin, hKeq]; simp only [periodizedAngleDeriv]; rw [← hYdef]; ring
    · refine ⟨Real.arcsin_pos.2 (hY01 s).1, ?_⟩
      unfold periodizedAngle
      exact lt_of_le_of_ne (Real.arcsin_le_pi_div_two _)
        (fun h => (hY01 s).2.ne (by rw [← Real.sin_arcsin (by linarith [(hY01 s).1])
          (hY01 s).2.le, h, Real.sin_pi_div_two]))
    · obtain ⟨-, hw⟩ := hwidth H (hH₀3.trans hH)
      rw [← hpc] at hw
      have hstrip := fun s => curveOfCurvature_strip (θ₀ := 0) hKc (fun s => (hKpos s).le) hKp
        hKint hH0 s
      refine ⟨Complex.I * tau (angleOfCurvature 0 (frontCurv Y) (-H / 2)), ?_, fun s s' => ?_⟩
      · rw [norm_mul, Complex.norm_I, norm_tau, one_mul]
      · rw [coord_sub]; unfold coord; linarith [(hstrip s).2, (hstrip s').1]
  -- the half-perimeter of the rear of period `Hs (n+1)` is `Hs n`
  have hPn : ∀ n, (∫ s in (0 : ℝ)..Hs (n + 1), √(1 - periodize y (Hs (n + 1)) s ^ 2)) = Hs n :=
    fun n => (hrec n).1
  -- the rear curvature functions
  have rear : ∀ n, ∃ k : ℝ → ℝ, Continuous k ∧ Function.Periodic k (Hs n) ∧
      (∫ x in (0 : ℝ)..Hs n, k x) = π ∧ (∀ x, 0 < k x ∧ k x ≤ 1 / 10) ∧
      ∀ s, k (x₀ + ∫ r in (0 : ℝ)..s, √(1 - periodize y (Hs (n + 1)) r ^ 2)) =
        periodize y (Hs (n + 1)) s / √(1 - periodize y (Hs (n + 1)) s ^ 2) := by
    intro n
    obtain ⟨-, -, -, -, hY01, hYR, hYc, -, -, -, -⟩ := front (Hs (n + 1)) (hHs (n + 1))
    have hH0 : 0 < Hs (n + 1) := hH₀pos.trans_le (hHs (n + 1))
    obtain ⟨k, hkc, hkp, hkint, hkval, hkx⟩ :=
      rear_curvature_function hH0 hYc (hper y (Hs (n + 1))) hY01 x₀
    rw [hPn n] at hkp hkint
    refine ⟨k, hkc, hkp, ?_, fun x => ?_, hkx⟩
    · rw [hkint, integral_periodize hyc hyA' ha hH0, hmass]
    · obtain ⟨s, hs⟩ := hkval x
      rw [hs]
      have hsq : 0 < √(1 - periodize y (Hs (n + 1)) s ^ 2) :=
        Real.sqrt_pos.2 (by nlinarith [(hY01 s).1, (hY01 s).2])
      exact ⟨div_pos (hY01 s).1 hsq, hYR s⟩
  choose k hk using rear
  set KQ : ℕ → ℝ → ℝ := fun n => frontCurv (periodize y (Hs n)) with hKQ
  set δs : ℕ → ℝ → ℝ := fun n => periodizedAngle y (Hs (n + 1)) with hδs
  have hcosδ : ∀ n r, Real.cos (δs n r) = √(1 - periodize y (Hs (n + 1)) r ^ 2) := fun n r => by
    simp only [hδs, periodizedAngle, Real.cos_arcsin]
  have hchain : ModelChain (1 / 10) Hs KQ k δs (fun _ => x₀) := by
    refine ⟨fun n => hH₀pos.trans_le (hHs n), fun n => (front _ (hHs n)).1,
      fun n => (front _ (hHs n)).2.1, fun n => (front _ (hHs n)).2.2.1,
      fun n s => ((front _ (hHs n)).2.2.2.1 s).1, fun n s => ((front _ (hHs n)).2.2.2.1 s).2,
      fun n => (hk n).1, fun n => (hk n).2.1, fun n => (hk n).2.2.1,
      fun n x => ((hk n).2.2.2.1 x).1, fun n x => ((hk n).2.2.2.1 x).2,
      fun n s => (front _ (hHs (n + 1))).2.2.2.2.2.2.2.1 s,
      fun n s => (front _ (hHs (n + 1))).2.2.2.2.2.2.2.2.1 s,
      fun n => (front _ (hHs (n + 1))).2.2.2.2.2.2.2.2.2.1, fun n s => ?_, fun n => ?_⟩
    · simp only [hcosδ]
      rw [(hk n).2.2.2.2 s]
      simp only [hδs, periodizedAngle, Real.tan_arcsin]
    · simp only [hcosδ]; exact hPn n
  -- the defects
  obtain ⟨hsum, htsum⟩ := hdefs k (fun n => ⟨(hk n).1, (hk n).2.2.2.2⟩)
  have hdefeq : chainDefect Hs KQ k = fun n => (1 + Hs n) ^ 2 *
      ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2))..
        (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
        |k n u - frontCurv (periodize y (Hs n)) u| := by
    funext n
    unfold chainDefect
    congr 1
    set c : ℝ → ℝ := fun r => √(1 - periodize y (Hs (n + 1)) r ^ 2) with hc
    have hYc := (front _ (hHs (n + 1))).2.2.2.2.2.2.1
    have hcc : Continuous c := by fun_prop
    have hcp : Function.Periodic c (Hs (n + 1)) := fun r => by
      simp only [hc, hper y (Hs (n + 1)) r]
    have hlen : (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), c r) =
        (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2), c r) + Hs n := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := -Hs (n + 1) / 2)
        (hcc.intervalIntegrable _ _) (hcc.intervalIntegrable _ _)]
      have e : Hs (n + 1) / 2 = -Hs (n + 1) / 2 + Hs (n + 1) := by ring
      rw [e, hcp.intervalIntegral_add_eq (-Hs (n + 1) / 2) 0, zero_add, hPn n]
      ring
    rw [hlen]
    have hfp : Function.Periodic (fun u => |k n u - frontCurv (periodize y (Hs n)) u|) (Hs n) :=
      fun u => by simp only [(hk n).2.1 u, (front _ (hHs n)).2.1 u]
    rw [hfp.intervalIntegral_add_eq _ 0, zero_add]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hKQ]
    rw [abs_sub_comm]
  rw [← hdefeq] at hsum htsum
  obtain ⟨X, p, ψ, hX, hXw⟩ := hshadow Hs KQ k δs (fun _ => x₀) Cw hchain hsum
    (htsum.trans (hH₅ H₀ hH₀5)) (fun n => (front _ (hHs n)).2.2.2.2.2.2.2.2.2.2)
  exact ⟨X, p, ψ, Cw, hX, hXw⟩

end Ovals

end
