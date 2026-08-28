import UnitTangentIterates.PaperMainTheoremC2Projection

/-!
# A simple unit-speed circle period is its circumference
-/

noncomputable section

open Function Set

namespace CircleRangeSimplePeriod

open PaperMainTheoremC2Projection

theorem inner_rotate_sq_add (z v : ℂ) :
    (inner ℝ z v) ^ 2 + (inner ℝ z (Complex.I * v)) ^ 2 =
      ‖z‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [real_inner_eq_re_inner, real_inner_eq_re_inner,
    RCLike.inner_apply, RCLike.inner_apply]
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

/-- A unit-speed positively curved oval whose image is a circle has constant
curvature equal to the reciprocal radius. -/
theorem curvature_eq_inv_radius_of_circleRange
    {gamma : ℝ → ℂ} {center : ℂ} {radius : ℝ}
    (hradius : 0 < radius)
    {theta k : ℝ → ℝ}
    (hgamma : ∀ s, HasDerivAt gamma
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (htheta : ∀ s, HasDerivAt theta (k s) s)
    (hk : ∀ s, 0 < k s)
    (hrange : range gamma = Metric.sphere center radius) :
    ∀ s, k s = 1 / radius := by
  let v : ℝ → ℂ := fun s => Complex.exp (Complex.I * (theta s : ℂ))
  have hgammaV : ∀ s, HasDerivAt gamma (v s) s := fun s => by
    simpa [v] using hgamma s
  have hnorm : ∀ s, ‖gamma s - center‖ = radius := by
    intro s
    have hs : gamma s ∈ Metric.sphere center radius := by
      rw [← hrange]
      exact ⟨s, rfl⟩
    simpa [Metric.mem_sphere, Complex.dist_eq] using hs
  have hvnorm : ∀ s, ‖v s‖ = 1 := fun s => by
    simp [v]
  have hvderiv : ∀ s, HasDerivAt v
      (v s * (Complex.I * (k s : ℂ))) s := by
    intro s
    have hi := ((htheta s).ofReal_comp).const_mul Complex.I
    simpa [v, mul_comm] using hi.cexp
  have horth : ∀ s, inner ℝ (gamma s - center) (v s) = 0 := by
    intro s
    have hz := (hgammaV s).sub_const center
    have hn := hz.norm_sq
    have hnzero : HasDerivAt (fun t => ‖gamma t - center‖ ^ 2) 0 s := by
      convert hasDerivAt_const s (radius ^ 2) using 1
      funext t
      rw [hnorm t]
    have heq := hn.unique hnzero
    nlinarith
  intro s
  let z : ℂ := gamma s - center
  let q : ℝ := inner ℝ z (Complex.I * v s)
  have hinnerZero : HasDerivAt (fun t => inner ℝ
      (gamma t - center) (v t)) 0 s := by
    convert hasDerivAt_const s (0 : ℝ) using 1
    funext t
    exact horth t
  have hinnerDeriv := ((hgammaV s).sub_const center).inner ℝ (hvderiv s)
  have hsecond := hinnerDeriv.unique hinnerZero
  have hqeq : k s * q = -1 := by
    change inner ℝ z (v s * (Complex.I * (k s : ℂ))) +
      inner ℝ (v s) (v s) = 0 at hsecond
    rw [real_inner_self_eq_norm_sq, hvnorm] at hsecond
    simp only [one_pow] at hsecond
    have hrotate : v s * (Complex.I * (k s : ℂ)) =
        (k s : ℝ) • (Complex.I * v s) := by
      simp [smul_eq_mul]
      ring
    rw [hrotate, real_inner_smul_right] at hsecond
    change k s * q + 1 = 0 at hsecond
    nlinarith
  have hqsq : q ^ 2 = radius ^ 2 := by
    have hparseval := inner_rotate_sq_add z (v s)
    rw [horth s, hnorm s, hvnorm s] at hparseval
    simpa [q] using hparseval
  have hqneg : q < 0 := by
    by_contra h
    have : 0 ≤ q := le_of_not_gt h
    nlinarith [hk s]
  have hq : q = -radius := by nlinarith
  rw [hq] at hqeq
  field_simp
  nlinarith

/-- The positive simple period of a unit-speed oval parametrizing a circle is
the circle circumference `2πr`. -/
theorem period_eq_two_pi_mul_radius_of_circleRange
    {gamma : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L) (hperiod : Periodic gamma L)
    (hinj : InjOn gamma (Ico 0 L))
    (hoval : MainTheoremConditional.IsOval gamma)
    {center : ℂ} {radius : ℝ} (hradius : 0 < radius)
    (hrange : range gamma = Metric.sphere center radius) :
    L = 2 * Real.pi * radius := by
  obtain ⟨-, -, -, -, theta, hgamma, k, htheta, hk⟩ := hoval
  have hkconst := curvature_eq_inv_radius_of_circleRange hradius
    hgamma htheta hk hrange
  have hthetaLinear : ∀ s, theta s = theta 0 + s / radius := by
    intro s
    let f : ℝ → ℝ := fun t => theta t - t / radius
    have hf : Differentiable ℝ f := fun t =>
      ((htheta t).sub ((hasDerivAt_id t).div_const radius)).differentiableAt
    have hfd : ∀ t, deriv f t = 0 := by
      intro t
      have hd : HasDerivAt f 0 t := by
        change HasDerivAt (fun u => theta u - u / radius) 0 t
        convert (htheta t).sub ((hasDerivAt_id t).div_const radius) using 1
        rw [hkconst t]
        ring
      exact hd.deriv
    have heq := is_const_of_deriv_eq_zero hf hfd s 0
    dsimp [f] at heq
    exact (sub_eq_iff_eq_add).mp (by simpa using heq)
  let v : ℝ → ℂ := fun s => Complex.exp (Complex.I * (theta s : ℂ))
  have hgammaV : ∀ s, HasDerivAt gamma (v s) s := fun s => by
    simpa [v] using hgamma s
  have hvderiv : ∀ s, HasDerivAt v
      (v s * (Complex.I * ((1 / radius : ℝ) : ℂ))) s := by
    intro s
    have hi := ((htheta s).ofReal_comp).const_mul Complex.I
    simpa [v, hkconst s, mul_comm] using hi.cexp
  let F : ℝ → ℂ := fun s => gamma s + Complex.I * radius * v s
  have hFdiff : Differentiable ℝ F := fun s =>
    ((hgamma s).add ((hvderiv s).const_mul (Complex.I * radius))).differentiableAt
  have hFderiv : ∀ s, deriv F s = 0 := by
    intro s
    have hd : HasDerivAt F 0 s := by
      change HasDerivAt (fun u => gamma u + Complex.I * radius * v u) 0 s
      convert (hgamma s).add ((hvderiv s).const_mul
        (Complex.I * radius)) using 1
      dsimp [v]
      push_cast
      field_simp
      simp [Complex.I_sq]
      field_simp [ne_of_gt hradius]
      norm_num
    exact hd.deriv
  have hFconst : ∀ s, F s = F 0 := fun s =>
    is_const_of_deriv_eq_zero hFdiff hFderiv s 0
  let T := 2 * Real.pi * radius
  have hT : 0 < T := by dsimp [T]; positivity
  have hvT : ∀ s, v (s + T) = v s := by
    intro s
    dsimp [v, T]
    rw [hthetaLinear (s + T), hthetaLinear s]
    have harg : ((theta 0 + (s + 2 * Real.pi * radius) / radius : ℝ) : ℂ) =
        ((theta 0 + s / radius : ℝ) : ℂ) + 2 * Real.pi := by
      push_cast
      field_simp [ne_of_gt hradius]
      ring
    rw [harg, mul_add, Complex.exp_add]
    have htwo : Complex.exp (Complex.I * (2 * Real.pi : ℂ)) = 1 := by
      rw [show Complex.I * (2 * (Real.pi : ℂ)) =
        2 * Real.pi * Complex.I by ring]
      exact Complex.exp_two_pi_mul_I
    rw [htwo, mul_one]
  have hTperiod : Periodic gamma T := by
    intro s
    have hs : F (s + T) = F s :=
      (hFconst (s + T)).trans (hFconst s).symm
    dsimp [F] at hs
    rw [hvT] at hs
    exact add_right_cancel hs
  have hLleT : L ≤ T := by
    by_contra h
    have hTL : T < L := lt_of_not_ge h
    have h0mem : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hL⟩
    have hTmem : T ∈ Ico 0 L := ⟨hT.le, hTL⟩
    have heq := hinj h0mem hTmem (by simpa using (hTperiod 0).symm)
    linarith
  have hvL : v L = v 0 := by
    have hgL : HasDerivAt gamma (v L) (0 + L) := by
      simpa using hgammaV L
    have hshift := hgL.comp_add_const 0 L
    rw [show (fun t => gamma (t + L)) = gamma from funext hperiod] at hshift
    exact hshift.unique (hgammaV 0)
  have hexp : Complex.exp (Complex.I * (((L / radius : ℝ)) : ℂ)) = 1 := by
    dsimp [v] at hvL
    rw [hthetaLinear L, hthetaLinear 0] at hvL
    simp only [zero_div, add_zero] at hvL
    have hsplit : Complex.exp (Complex.I *
        (((theta 0 + L / radius : ℝ)) : ℂ)) =
        Complex.exp (Complex.I * ((theta 0 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (((L / radius : ℝ)) : ℂ)) := by
      rw [show Complex.I * (((theta 0 + L / radius : ℝ)) : ℂ) =
        Complex.I * ((theta 0 : ℝ) : ℂ) +
          Complex.I * (((L / radius : ℝ)) : ℂ) by push_cast; ring,
        Complex.exp_add]
    rw [hsplit] at hvL
    exact mul_left_cancel₀
      (Complex.exp_ne_zero (Complex.I * ((theta 0 : ℝ) : ℂ)))
      (by simpa using hvL)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hratio : L / radius = 2 * Real.pi * (n : ℝ) := by
    have hnI := hn
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    apply_fun fun z : ℂ => z / Complex.I at hnI
    have hc : ((L / radius : ℝ) : ℂ) =
        ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
      simpa [mul_assoc, mul_comm, mul_left_comm, hI] using hnI
    exact_mod_cast hc
  have hnpos : 0 < n := by
    have hprod : 0 < 2 * Real.pi * (n : ℝ) := by
      rw [← hratio]
      exact div_pos hL hradius
    have hncast : 0 < (n : ℝ) := by
      rcases (mul_pos_iff.mp hprod) with h | h
      · exact h.2
      · exfalso
        nlinarith [Real.pi_pos]
    exact_mod_cast hncast
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hTleL : T ≤ L := by
    dsimp [T]
    have hEq : L = 2 * Real.pi * radius * (n : ℝ) := by
      field_simp at hratio
      nlinarith
    have hcoef : 0 ≤ 2 * Real.pi * radius := by positivity
    calc
      2 * Real.pi * radius = (2 * Real.pi * radius) * 1 := by ring
      _ ≤ (2 * Real.pi * radius) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn1 hcoef
      _ = L := hEq.symm
  exact le_antisymm hLleT hTleL

/-- Same-L perimeter noncircularity of a simple smooth oval implies genuine,
parameter-independent geometric noncircularity. -/
theorem isNoncircular_of_not_isCircleOfPerimeter
    {gamma : ℝ → ℂ} {L : ℝ}
    (hL : 0 < L) (hperiod : Periodic gamma L)
    (hinj : InjOn gamma (Ico 0 L))
    (hoval : MainTheoremConditional.IsOval gamma)
    (hnoncircle : ¬ ClosingArgument.IsCircleOfPerimeter (range gamma) L) :
    IsNoncircular gamma := by
  intro hcircle
  obtain ⟨center, radius, hradius, hrange⟩ := hcircle
  apply hnoncircle
  refine ⟨center, radius, hradius, ?_, hrange⟩
  exact period_eq_two_pi_mul_radius_of_circleRange
    hL hperiod hinj hoval hradius hrange

end CircleRangeSimplePeriod
