import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.TubePullbackLimit

/-!
# Zero-margin tube invariance of the canonical selected inverse

The canonical map is the marked selected rear whenever that relation is
satisfiable and is the identity otherwise.  In the first branch the
closed-strip relation gives rear curvature `tan delta >= 0`; in the second
branch zero-margin membership is unchanged.  Thus no positive curvature or
chord margin is needed for weak pullback structure.
-/

noncomputable section

open Set Function MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseMap

/-- Every marked selected rear on the closed strip has the zero-margin tube
structure, independently of the auxiliary tube constants in its witness. -/
theorem IsMarkedSelectedInverse.weak_mem
    {kap : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p q : Data} (hq : IsMarkedSelectedInverse kap p q) :
    IsTubeMember 0 0 0 q := by
  obtain ⟨⟨cq, kq, dq, hqmem⟩, Theta, K, delta, sf,
    hfront, hTheta, hdper, hdmem, hode, hsfinv, hperim, hrear⟩ := hq
  have hsqrt : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  have hdeltaC : Continuous delta :=
    Differentiable.continuous fun s => (hode s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s) :=
    fun s => Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  let psi : ℝ → ℝ := fun x => rearAngle Theta delta (sf x)
  have hrearDeriv : ∀ x, HasDerivAt
      (fun y => rearTrack (ev p) Theta delta (sf y))
      (Complex.exp (Complex.I * (psi x : ℂ))) x := by
    intro x
    exact SelectedInverseRearOwn.hasDerivAt_rearOwnCurve
      hsqrt hdeltaC hcos hsfinv hfront hTheta hode x
  have hpsi : ∀ x, HasDerivAt psi (Real.tan (delta (sf x))) x := by
    intro x
    exact SelectedInverseRearOwn.hasDerivAt_rearOwnAngleSf
      hsqrt hdeltaC hcos hsfinv hTheta hode x
  let L : ℝ := perim q
  have hL0 : 0 ≤ L := by dsimp [L, perim]; exact norm_nonneg _
  have hinner : ∀ s : ℝ, HasDerivAt (fun y : ℝ => y / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  let tau : ℝ → ℂ := fun s => q.2.1 (s / L) / L
  have hevRaw : ∀ s, HasDerivAt (ev q) (tau s) s := by
    intro s
    have h := (hqmem.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [ev, L, tau, Function.comp, div_eq_mul_inv, one_div,
      smul_eq_mul, mul_comm] using h
  have hevRear : ∀ s, HasDerivAt (ev q)
      (Complex.exp (Complex.I * (psi s : ℂ))) s := by
    intro s
    have hfun : ev q = fun y => rearTrack (ev p) Theta delta (sf y) :=
      funext hrear
    rw [hfun]
    exact hrearDeriv s
  have htau : ∀ s, tau s = Complex.exp (Complex.I * (psi s : ℂ)) :=
    fun s => (hevRaw s).unique (hevRear s)
  have hLne : L ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm (htau 0)
    simp [tau, hzero, Complex.norm_exp] at hnorm
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLne)
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hLne
  have hvel : ∀ x, q.2.1 x =
      (L : ℂ) * Complex.exp (Complex.I * (psi (L * x) : ℂ)) := by
    intro x
    have h := htau (L * x)
    have harg : L * x / L = x := by field_simp
    rw [show tau (L * x) = q.2.1 x / L by simp [tau, harg]] at h
    have hm := (div_eq_iff hLC).mp h
    simpa [mul_comm] using hm
  have hvelFun : (⇑q.2.1 : ℝ → ℂ) =
      fun x => (L : ℂ) *
        Complex.exp (Complex.I * (psi (L * x) : ℂ)) := funext hvel
  have hacc : ∀ x, q.2.2 x =
      ((L ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (psi (L * x) : ℂ)) *
        (Complex.I * (Real.tan (delta (sf (L * x))) : ℂ)) := by
    intro x
    apply (hqmem.hasDerivAt_vel x).unique
    rw [hvelFun]
    have hlin : HasDerivAt (fun y : ℝ => L * y) L x := by
      simpa using (hasDerivAt_id x).const_mul L
    have hpsiL : HasDerivAt (fun y => psi (L * y))
        (L * Real.tan (delta (sf (L * x)))) x :=
      by convert (hpsi (L * x)).comp x hlin using 1 <;> ring
    have hi := (hpsiL.ofReal_comp).const_mul Complex.I
    have hexp := hi.cexp
    have hscaled := hexp.const_mul (L : ℂ)
    convert hscaled using 1 <;> push_cast <;> ring
  have hconvex : ∀ x,
      0 ≤ ((starRingEnd ℂ) (q.2.1 x) * q.2.2 x).im := by
    intro x
    have htan : 0 ≤ Real.tan (delta (sf (L * x))) :=
      RearTrack.rear_curvature_nonneg hkap1 hkap0
        (hdmem (sf (L * x))).1 (hdmem (sf (L * x))).2
    have hce : (starRingEnd ℂ)
          (Complex.exp (Complex.I * (psi (L * x) : ℂ))) *
        Complex.exp (Complex.I * (psi (L * x) : ℂ)) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    have heq : (starRingEnd ℂ) (q.2.1 x) * q.2.2 x =
        ((L ^ 3 * Real.tan (delta (sf (L * x))) : ℝ) : ℂ) * Complex.I := by
      rw [hvel x, hacc x, map_mul, Complex.conj_ofReal]
      calc
        (L : ℂ) * (starRingEnd ℂ)
              (Complex.exp (Complex.I * (psi (L * x) : ℂ))) *
            (((L ^ 2 : ℝ) : ℂ) *
              Complex.exp (Complex.I * (psi (L * x) : ℂ)) *
                (Complex.I * (Real.tan (delta (sf (L * x))) : ℂ))) =
            ((L : ℂ) * ((L ^ 2 : ℝ) : ℂ)) *
              ((starRingEnd ℂ)
                (Complex.exp (Complex.I * (psi (L * x) : ℂ))) *
                Complex.exp (Complex.I * (psi (L * x) : ℂ))) *
              (Complex.I * (Real.tan (delta (sf (L * x))) : ℂ)) := by ring
        _ = ((L ^ 3 * Real.tan (delta (sf (L * x))) : ℝ) : ℂ) *
              Complex.I := by rw [hce]; push_cast; ring
    rw [heq]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero]
    simpa using mul_nonneg (pow_nonneg hL0 3) htan
  exact
    { hasDerivAt_curve := hqmem.hasDerivAt_curve
      hasDerivAt_vel := hqmem.hasDerivAt_vel
      periodic := hqmem.periodic
      speed_const := hqmem.speed_const
      speed_lb := fun u => norm_nonneg _
      curv_lb := fun u => by simpa using hconvex u
      chord := fun u hu v hv => by simp [norm_nonneg] }

/-- The canonical selected inverse preserves the zero-margin tube.  The
fallback branch is handled definitionally. -/
theorem selInv_weak_mem {kap : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember 0 0 0 p) :
    IsTubeMember 0 0 0 (selInv kap p) := by
  classical
  unfold selInv
  split_ifs with h
  · exact h.choose_spec.weak_mem hkap0 hkap1
  · exact hp

/-- Every diagonal pullback of weak model fronts has weak tube structure. -/
theorem pullback_selInv_weak_mem
    {kap : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {Q : ℕ → Data} (hQ : ∀ n, IsTubeMember 0 0 0 (Q n)) :
    ∀ n k, IsTubeMember 0 0 0
      (TubePullbackLimit.pullback (selInv kap) Q n k) := by
  intro n k
  induction k generalizing n with
  | zero => simpa [TubePullbackLimit.pullback] using hQ n
  | succ k ih =>
      rw [TubePullbackLimit.pullback_succ]
      exact selInv_weak_mem hkap0 hkap1 (ih (n + 1))

end SelectedInverseMap
