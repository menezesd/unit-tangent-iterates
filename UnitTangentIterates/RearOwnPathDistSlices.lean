import Mathlib
import UnitTangentIterates.RearOwnPathDistIntrinsic

/-!
# The path-distance bound with the path identified as the path of fronts

`RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic` still relates the
normal path `Γ` of the path metric to the family of fronts `F` through two
hypotheses: that the normal speed of `Γ` *is* the front normal velocity read in
the normalized parameter (`hlink`), and that the front normal velocity vanishes
outside the time window (`hFrest`).

Both are consequences of the geometric identification of the path with the
family of fronts:

```
  X(t, u) = F(t, P(t) u) ,      ν(t, u) = i e^{iΘ(t, P(t) u)} ,
```

that is, of the statement that the moving marked curve of the path is the front
family written in the normalized parameter, with the standard unit normal.

* `eta_eq_frontNormalVelocity` — differentiating that identity in the time, the
  reparametrization contributes the *tangential* term `P'(t) u e^{iΘ}`, so the
  normal component is unchanged and `η(t,u) = η_F(t, P(t) u)`.
* `frontNormalVelocity_eq_zero_of_rest` — a normal path is at rest outside its
  time window (`m = 0` there dominates `|η|`), so the front normal velocity
  vanishes there as well.

`pathDist_le_of_front_slices` is the resulting bound: the only hypotheses left
relating `Γ` to the fronts are the two identifications above.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSlices

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The normal speed of the path of fronts is the front normal velocity.**
If the moving marked curve of a normal path is the family of fronts read in the
normalized parameter, with the standard unit normal, then its normal speed is
the normal velocity of the front, whatever the motion of the front period: the
reparametrization contributes a tangential term only. -/
theorem eta_eq_frontNormalVelocity {p q : Data} (Γ : NormalPath p q)
    (hFdiff : Differentiable ℝ (uncurry F))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hPdiff : Differentiable ℝ P)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (t u : ℝ) :
    Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) := by
  -- the two expressions for the time derivative of the moving curve
  have hphi : HasDerivAt (fun r => P r * u) (deriv P t * u) t :=
    ((hPdiff t).hasDerivAt).mul_const u
  have h1 : HasDerivAt (fun r => F r (P r * u))
      (partialTime F t (P t * u) + (deriv P t * u) • partialArc F t (P t * u)) t :=
    hasDerivAt_front_moving hFdiff hphi
  have h2 : HasDerivAt (fun r => F r (P r * u))
      ((Γ.eta t u : ℂ) * Γ.nu t u) t := by
    have hfun : (fun r => F r (P r * u)) = fun r => Γ.X r u := by
      funext r; exact (hX r u).symm
    rw [hfun]
    exact Γ.hasDerivAt_time t u
  have harc : partialArc F t (P t * u) = Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)) :=
    ((hasDerivAt_partialArc hFdiff t (P t * u)).unique (hF t (P t * u)))
  have hkey := h2.unique h1
  rw [harc, hnu t u] at hkey
  set e : ℂ := Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)) with he
  have hconj : e * (starRingEnd ℂ) e = 1 := by
    rw [he, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_I]
  -- take the normal component of both sides
  have hcomp : ((Γ.eta t u : ℂ) * (Complex.I * e) * (starRingEnd ℂ) (Complex.I * e)).re
      = ((partialTime F t (P t * u)
          + ((deriv P t * u : ℝ) : ℂ) * e) * (starRingEnd ℂ) (Complex.I * e)).re := by
    rw [hkey]
    norm_num [Complex.real_smul]
  have hleft : ((Γ.eta t u : ℂ) * (Complex.I * e) * (starRingEnd ℂ) (Complex.I * e)).re
      = Γ.eta t u := by
    have : (Complex.I * e) * (starRingEnd ℂ) (Complex.I * e)
        = Complex.I * (starRingEnd ℂ) Complex.I * (e * (starRingEnd ℂ) e) := by
      rw [map_mul]; ring
    rw [mul_assoc, this, hconj, Complex.conj_I]
    simp
  have hright : ((partialTime F t (P t * u)
        + ((deriv P t * u : ℝ) : ℂ) * e) * (starRingEnd ℂ) (Complex.I * e)).re
      = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) := by
    have hexpand : (partialTime F t (P t * u) + ((deriv P t * u : ℝ) : ℂ) * e)
        * (starRingEnd ℂ) (Complex.I * e)
        = partialTime F t (P t * u) * (starRingEnd ℂ) (Complex.I * e)
          - ((deriv P t * u : ℝ) : ℂ) * Complex.I * (e * (starRingEnd ℂ) e) := by
      rw [map_mul, Complex.conj_I]
      ring
    rw [hexpand, hconj]
    simp only [frontNormalVelocityAt, frontNormalVelocity, rearAngle, sub_add_cancel, ← he]
    simp
  rw [hleft, hright] at hcomp
  exact hcomp

/-- **A path of fronts at rest has a vanishing front normal velocity.**  The
cost density of a normal path vanishes outside its time window and dominates
the normal speed, so the front normal velocity vanishes there too. -/
theorem frontNormalVelocity_eq_zero_of_rest {p q : Data} (Γ : NormalPath p q)
    (hPpos : ∀ t, 0 < P t)
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Γ.T) (s : ℝ) :
    frontNormalVelocityAt (partialTime F) Θ δ t s = 0 := by
  have hm : Γ.m t = 0 := Γ.m_stop t ht
  have habs : |Γ.eta t (s / P t)| ≤ 0 := by
    have := Γ.abs_eta_le t (s / P t)
    rwa [hm] at this
  have hzero : Γ.eta t (s / P t) = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  have hs : P t * (s / P t) = s := by
    rw [mul_comm, div_mul_cancel₀ s (hPpos t).ne']
  rw [hlink t (s / P t), hs] at hzero
  exact hzero

/-- **The path pseudodistance of the selected rears, for the path of fronts
itself.**

Same statement as `RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic`,
with the link between the normal path and the front family, and the vanishing
of the front normal velocity outside the time window, both replaced by the
geometric identification of the moving marked curve with the family of fronts
in the normalized parameter. -/
theorem pathDist_le_of_front_slices {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC3.differentiable (by norm_num)
  have hlink : ∀ t u,
      Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) :=
    fun t u => eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff hX hnu t u
  have hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0 :=
    fun t ht s => frontNormalVelocity_eq_zero_of_rest Γ hPpos hlink ht s
  obtain ⟨EF, hEF0, hEF, Phi, hPhi0, hbase, hPhi⟩ :=
    pathDist_le_of_front_intrinsic Γ p' hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0
      hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4 hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3
      hKdC3 hsfinv hlink hFrest hstart
  refine ⟨EF, hEF0, hEF, Phi, hPhi0, fun h => hbase fun t => ?_, hPhi⟩
  -- the front does not move at the marked point, so the base drift vanishes there
  have hXF : (fun r => Γ.X r 0) = fun r => F r 0 := by
    funext r
    rw [hX r 0, mul_zero]
  have hd := Γ.hasDerivAt_time t 0
  rw [hXF, h t] at hd
  simp only [Complex.ofReal_zero, zero_mul] at hd
  have hFdot : partialTime F t 0 = 0 :=
    (hasDerivAt_partialTime hFdiff t 0).unique hd
  exact RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero hFdot

end RearOwnPathDistSlices
