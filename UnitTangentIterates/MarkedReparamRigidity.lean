import Mathlib
import UnitTangentIterates.MarkedSpace

/-!
# Rigidity of the marking: a reparametrization of a marked curve is a shift

The space of marked curves of `MarkedSpace.lean` carries its curves in the
**normalized parameter**, in which the speed is constant; the chord-arc bound
of a tube member makes the curve injective over one period, and the curvature
bound `kmin > 0` fixes its orientation.

This file draws the consequence used at the terminal end of the path-distance
bound: if a tube member `q` traces another tube member `R` through a
differentiable change of parameter, `q(u) = R(ψ(u))`, then

```
  ψ(u) = u + ψ(0) ,
```

so the two marked curves differ only by a **shift of the marking**.  Indeed the
constancy of both speeds forces `|ψ'|` to be constant, hence — `ψ'` being
continuous and nowhere zero — `ψ'` itself constant, so `ψ` is affine;
injectivity over a period forces its slope to be `±1`, and the sign of the
curvature forces the slope to be `+1`.

Main results:

* `injOn_curve` — a tube member with positive chord-arc constant is injective
  over one period;
* `int_of_eq_shift` — two parameters carrying the same point differ by an
  integer;
* `exists_shift_of_reparam` — the rigidity statement above.
-/

noncomputable section

open Set Function MarkedSpace

namespace MarkedReparamRigidity

/-- **A tube member is injective over one period.** -/
theorem injOn_curve {c kmin delta : ℝ} (hdelta : 0 < delta) {p : Data}
    (hp : IsTubeMember c kmin delta p) : InjOn (⇑p.1) (Ico (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hchord := hp.chord u (Ico_subset_Icc_self hu) v (Ico_subset_Icc_self hv)
  rw [huv] at hchord
  simp only [sub_self, norm_zero] at hchord
  exact cyc_eq_zero_iff hu hv (by nlinarith [le_max_left |u - v| (1 - |u - v|)])

/-- **Two parameters carrying the same point of a tube member differ by an
integer.** -/
theorem int_of_eq_shift {c kmin delta : ℝ} (hdelta : 0 < delta) {p : Data}
    (hp : IsTubeMember c kmin delta p) {x w : ℝ} (h : p.1 (x + w) = p.1 x) :
    ∃ n : ℤ, w = n := by
  have hfract : ∀ y : ℝ, p.1 (Int.fract y) = p.1 y := by
    intro y
    show p.1 (y - ⌊y⌋) = p.1 y
    simpa using hp.periodic.sub_int_mul_eq (x := y) ⌊y⌋
  have hmem : ∀ y : ℝ, Int.fract y ∈ Ico (0 : ℝ) 1 :=
    fun y => ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  have heq : Int.fract (x + w) = Int.fract x := by
    refine injOn_curve hdelta hp (hmem _) (hmem _) ?_
    rw [hfract, hfract, h]
  refine ⟨⌊x + w⌋ - ⌊x⌋, ?_⟩
  have h1 : x + w - ⌊x + w⌋ = x - ⌊x⌋ := heq
  push_cast
  linarith

variable {R q : Data} {cR kR dR cq kq dq : ℝ}

/-- **Rigidity of the marking.**  If the curve of the tube member `q` is the
curve of the tube member `R` reparametrized by a differentiable change of
parameter `ψ`, then `ψ` is the shift by `ψ 0`: the two marked curves are the
same curve, with markings differing by a constant. -/
theorem exists_shift_of_reparam (hcR : 0 < cR) (hkR : 0 < kR) (hdR : 0 < dR)
    (hcq : 0 < cq) (hkq : 0 < kq) (hdq : 0 < dq)
    (hR : IsTubeMember cR kR dR R) (hq : IsTubeMember cq kq dq q)
    {psi dpsi : ℝ → ℝ} (hpsi : ∀ u, HasDerivAt psi (dpsi u) u)
    (hcomp : ∀ u, q.1 u = R.1 (psi u)) :
    ∀ u, q.1 u = R.1 (u + psi 0) := by
  have hqfun : ⇑q.1 = fun u => R.1 (psi u) := funext hcomp
  have hpsic : Continuous psi :=
    continuous_iff_continuousAt.2 fun u => (hpsi u).continuousAt
  have hPR : 0 < perim R := perim_pos hcR hR
  have hPq : 0 < perim q := perim_pos hcq hq
  -- the chain rule
  have hchain : ∀ u, q.2.1 u = (dpsi u : ℂ) * R.2.1 (psi u) := by
    intro u
    have h1 : HasDerivAt (fun y => R.1 (psi y)) (dpsi u • R.2.1 (psi u)) u :=
      (hR.hasDerivAt_curve (psi u)).scomp u (hpsi u)
    have h2 : HasDerivAt (⇑q.1) (q.2.1 u) u := hq.hasDerivAt_curve u
    rw [hqfun] at h2
    simpa [Complex.real_smul] using h2.unique h1
  -- the two constant speeds force `|ψ'|` to be constant
  have habs : ∀ u, |dpsi u| = perim q / perim R := by
    intro u
    have h := congrArg norm (hchain u)
    rw [norm_vel_eq_perim hq u, norm_mul, norm_vel_eq_perim hR (psi u),
      Complex.norm_real, Real.norm_eq_abs] at h
    rw [h, mul_div_assoc, div_self hPR.ne', mul_one]
  have hpos : 0 < perim q / perim R := div_pos hPq hPR
  have hne : ∀ u, dpsi u ≠ 0 := by
    intro u hu
    have h := habs u
    rw [hu, abs_zero] at h
    exact absurd h.symm hpos.ne'
  -- `ψ'` is continuous
  have hnormR : ∀ u, ‖R.2.1 (psi u)‖ = perim R := fun u => norm_vel_eq_perim hR (psi u)
  have hform : ∀ u, dpsi u
      = ((starRingEnd ℂ) (R.2.1 (psi u)) * q.2.1 u).re / ‖R.2.1 (psi u)‖ ^ 2 := by
    intro u
    have hRne : ‖R.2.1 (psi u)‖ ≠ 0 := by rw [hnormR u]; exact hPR.ne'
    have h1 : (starRingEnd ℂ) (R.2.1 (psi u)) * q.2.1 u
        = ((dpsi u * ‖R.2.1 (psi u)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hchain u]
      have h2 : (starRingEnd ℂ) (R.2.1 (psi u)) * ((dpsi u : ℂ) * R.2.1 (psi u))
          = (dpsi u : ℂ) * ((starRingEnd ℂ) (R.2.1 (psi u)) * R.2.1 (psi u)) := by ring
      rw [h2, Complex.conj_mul']
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
    field_simp
  have hdpsic : Continuous dpsi := by
    have hc1 : Continuous fun u => (starRingEnd ℂ) (R.2.1 (psi u)) :=
      Complex.continuous_conj.comp (R.2.1.continuous.comp hpsic)
    have hc2 : Continuous fun u => ‖R.2.1 (psi u)‖ ^ 2 :=
      (continuous_norm.comp (R.2.1.continuous.comp hpsic)).pow 2
    have hden : ∀ u, ‖R.2.1 (psi u)‖ ^ 2 ≠ 0 := by
      intro u
      rw [hnormR u]
      positivity
    have hcont : Continuous fun u =>
        ((starRingEnd ℂ) (R.2.1 (psi u)) * q.2.1 u).re / ‖R.2.1 (psi u)‖ ^ 2 :=
      (Complex.continuous_re.comp (hc1.mul q.2.1.continuous)).div hc2 hden
    exact hcont.congr fun u => (hform u).symm
  -- hence `ψ'` itself is constant
  have hconst : ∀ u, dpsi u = dpsi 0 := by
    intro u
    by_contra hne'
    have habs2 : |dpsi u| = |dpsi 0| := by rw [habs u, habs 0]
    have hopp : dpsi u = -dpsi 0 := by
      rcases abs_eq_abs.mp habs2 with h | h
      · exact absurd h hne'
      · exact h
    have hzero : (0 : ℝ) ∈ uIcc (dpsi 0) (dpsi u) := by
      rw [hopp, Set.mem_uIcc]
      rcases le_total (dpsi 0) 0 with h | h
      · exact Or.inl ⟨h, by linarith⟩
      · exact Or.inr ⟨by linarith, h⟩
    obtain ⟨y, -, hy⟩ := intermediate_value_uIcc hdpsic.continuousOn hzero
    exact hne y hy
  set k : ℝ := dpsi 0 with hkdef
  have hkne : k ≠ 0 := hne 0
  -- so `ψ` is affine
  have hlin : ∀ u, psi u = psi 0 + k * u := by
    have hdiff : Differentiable ℝ fun y => psi y - k * y := fun y =>
      ((hpsi y).sub ((hasDerivAt_id y).const_mul k)).differentiableAt
    have hderiv : ∀ y : ℝ, deriv (fun y => psi y - k * y) y = 0 := by
      intro y
      have h : HasDerivAt (fun y => psi y - k * y) 0 y := by
        have h1 := (hpsi y).sub ((hasDerivAt_id y).const_mul k)
        simpa [hconst y] using h1
      exact h.deriv
    intro u
    have h := is_const_of_deriv_eq_zero hdiff hderiv u 0
    simp only [mul_zero, sub_zero] at h
    linarith
  -- the slope is an integer
  have hshift : R.1 (psi 0 + k) = R.1 (psi 0) := by
    have h1 : q.1 1 = R.1 (psi 0 + k) := by rw [hcomp 1, hlin 1, mul_one]
    have h2 : q.1 0 = R.1 (psi 0) := hcomp 0
    rw [← h1, ← h2]
    simpa using hq.periodic 0
  obtain ⟨n, hn⟩ := int_of_eq_shift hdR hR hshift
  -- the slope has absolute value one
  have hk1 : |k| = 1 := by
    by_contra hne1
    have hnne : n ≠ 0 := by
      intro h0
      apply hkne
      rw [hn, h0]
      norm_num
    have hnabs : (1 : ℝ) ≤ |k| := by
      rw [hn, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hnne
    have hkgt : 1 < |k| := lt_of_le_of_ne hnabs (Ne.symm hne1)
    have hkabspos : 0 < |k| := by linarith
    have hxmem : 1 / |k| ∈ Ico (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one hkabspos]
      exact hkgt
    have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
    have hval : q.1 (1 / |k|) = q.1 0 := by
      rw [hcomp (1 / |k|), hlin (1 / |k|), hcomp 0]
      rcases abs_cases k with ⟨hka, -⟩ | ⟨hka, -⟩
      · have hone : k * (1 / |k|) = 1 := by rw [hka]; field_simp
        rw [hone]
        simpa using hR.periodic (psi 0)
      · have hone : k * (1 / |k|) = -1 := by
          rw [hka]
          field_simp
        rw [hone, show psi 0 + (-1 : ℝ) = psi 0 - 1 by ring]
        have hp1 := hR.periodic (psi 0 - 1)
        simp only [sub_add_cancel] at hp1
        exact hp1.symm
    have hx0 : (1 : ℝ) / |k| = 0 := injOn_curve hdq hq hxmem h0mem hval
    have : (0 : ℝ) < 1 / |k| := by positivity
    linarith
  -- the orientation fixes the sign
  have hacc : q.2.2 0 = ((k ^ 2 : ℝ) : ℂ) * R.2.2 (psi 0) := by
    have hveq : ⇑q.2.1 = fun y => (k : ℂ) * R.2.1 (psi 0 + k * y) := by
      funext y
      rw [hchain y, hconst y, hlin y]
    have hinner : HasDerivAt (fun y : ℝ => psi 0 + k * y) k 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul k).const_add (psi 0)
    have h1 : HasDerivAt (fun y => (k : ℂ) * R.2.1 (psi 0 + k * y))
        ((k : ℂ) * (k • R.2.2 (psi 0 + k * 0))) 0 := by
      have h := ((hR.hasDerivAt_vel (psi 0 + k * 0)).scomp 0 hinner).const_mul (k : ℂ)
      simpa [Function.comp] using h
    have h2 : HasDerivAt (⇑q.2.1) (q.2.2 0) 0 := hq.hasDerivAt_vel 0
    rw [hveq] at h2
    have h3 := h2.unique h1
    rw [h3]
    push_cast [Complex.real_smul]
    ring_nf
  have hkeq : k = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hk1 with h | h
    · exact h
    · exfalso
      have hq0 : q.2.1 0 = (k : ℂ) * R.2.1 (psi 0) := hchain 0
      have hrel : ((starRingEnd ℂ) (q.2.1 0) * q.2.2 0).im
          = k ^ 3 * ((starRingEnd ℂ) (R.2.1 (psi 0)) * R.2.2 (psi 0)).im := by
        rw [hq0, hacc]
        have hz : (starRingEnd ℂ) ((k : ℂ) * R.2.1 (psi 0)) * (((k ^ 2 : ℝ)) : ℂ)
              * R.2.2 (psi 0)
            = ((k ^ 3 : ℝ) : ℂ) * ((starRingEnd ℂ) (R.2.1 (psi 0)) * R.2.2 (psi 0)) := by
          push_cast [map_mul, Complex.conj_ofReal]
          ring
        rw [← mul_assoc, hz, Complex.im_ofReal_mul]
      have hcurvq := hq.curv_lb 0
      have hcurvR := hR.curv_lb (psi 0)
      rw [norm_vel_eq_perim hq 0] at hcurvq
      rw [norm_vel_eq_perim hR (psi 0)] at hcurvR
      rw [hrel, h] at hcurvq
      nlinarith [pow_pos hPq 3, pow_pos hPR 3]
  intro u
  rw [hcomp u, hlin u, hkeq, one_mul, add_comm]

end MarkedReparamRigidity
