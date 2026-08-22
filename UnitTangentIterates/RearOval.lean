import Mathlib
import UnitTangentIterates.UnitTangentOval
import UnitTangentIterates.RearTrack

/-!
# The selected rear is an oval

`UnitTangentOval.lean` shows that the unit-tangent transform of an oval,
reparametrized by its own arclength, is again an oval.  The same argument
applies to the **selected rear** of *A Noncircular Oval with Convex
Unit-Tangent Iterates*: it is a closed regular curve of positive curvature, but
in the front's arclength it has speed `cos δ ≠ 1`, so it is an oval only after
reparametrization.

The file first isolates the general statement,

* `isOval_reparam_of_regular` : **a closed regular curve of positive curvature
  is an oval up to reparametrization** — if `g' = v·e^{iψ}` with speed
  `v ≥ c > 0`, tangent angle `ψ` turning at rate `ψ' = k·v` with `k > 0`, `g`
  periodic and injective on one period, then `g` reparametrized by arclength is
  an oval with the same image;

and then applies it to the rear track:

* `isOval_reparam_rearTrack` : the rear track built from a periodic steering
  angle with `cos δ > 0` and `tan δ > 0` — that is, the selected rear of a
  front with `0 < K ≤ κ̂ < 1` — is an oval up to reparametrization.
-/

noncomputable section

open Set Function Filter Topology MeasureTheory intervalIntegral

namespace RearOval

/-- **A closed regular curve of positive curvature is an oval up to
reparametrization.**  Here `v` is the speed, `ψ` the tangent angle and `k` the
curvature with respect to arclength, so that `ψ' = k·v`. -/
theorem isOval_reparam_of_regular {g : ℝ → ℂ} {psi v k : ℝ → ℝ} {p c : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hspeed : ∀ s, c ≤ v s)
    (hvc : Continuous v) (hpsic : Continuous psi)
    (hg : ∀ s, HasDerivAt g ((v s : ℂ) * Complex.exp (Complex.I * (psi s : ℂ))) s)
    (hpsi : ∀ s, HasDerivAt psi (k s * v s) s) (hkpos : ∀ s, 0 < k s)
    (hgper : Periodic g p)
    (hvper : Periodic v p)
    (htanper : ∀ s, Complex.exp (Complex.I * (psi (s + p) : ℂ))
      = Complex.exp (Complex.I * (psi s : ℂ)))
    (hinj : InjOn g (Ico 0 p)) :
    ∃ (Y : ℝ → ℂ) (phi : ℝ → ℝ) (L : ℝ),
      MainTheoremConditional.IsOval Y ∧ range Y = range g ∧
      0 < L ∧ Periodic Y L ∧
      Surjective phi ∧ Continuous phi ∧ (∀ y, phi (y + L) = phi y + p) ∧
      (∀ y, Y y = g (phi y)) ∧
      (∀ y, HasDerivAt Y (Complex.exp (Complex.I * (psi (phi y) : ℂ))) y) ∧
      (∀ y, HasDerivAt (fun z => psi (phi z)) (k (phi y)) y) ∧
      L = ∫ s in (0:ℝ)..p, v s := by
  classical
  set V : ℝ → ℂ := fun s => (v s : ℂ) * Complex.exp (Complex.I * (psi s : ℂ)) with hV
  have hvpos : ∀ s, 0 < v s := fun s => lt_of_lt_of_le hc (hspeed s)
  have hVnorm : ∀ s, ‖V s‖ = v s := by
    intro s
    rw [hV]
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp]
    rw [Real.norm_eq_abs, abs_of_pos (hvpos s)]
    simp
  have hVspeed : ∀ s, c ≤ ‖V s‖ := fun s => by rw [hVnorm s]; exact hspeed s
  have hVc : Continuous V := by
    rw [hV]
    exact (Complex.continuous_ofReal.comp hvc).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp hpsic)).cexp)
  have hVper : Periodic V p := by
    intro s
    simp only [hV, hvper s, htanper s]
  obtain ⟨phi, hphic, hphiright, hphileft, hphideriv, hphiper⟩ :=
    UnitTangentOval.exists_inverse_arcLength_gen hc hVc hVper hVspeed
  set L : ℝ := UnitTangentOval.periodLength V p with hL
  have hLpos : 0 < L := UnitTangentOval.periodLength_pos hc hp hVc hVspeed
  -- the reparametrized curve
  have hphisurj : Surjective phi := fun u => ⟨MarkedReparam.arcLength V u, hphileft u⟩
  have hYderiv : ∀ y, HasDerivAt (fun y => g (phi y))
      (Complex.exp (Complex.I * (psi (phi y) : ℂ))) y := by
    intro y
    have hne : (v (phi y) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hvpos (phi y))
    have h := (hg (phi y)).scomp y (hphideriv y)
    rw [hVnorm (phi y)] at h
    have heq : ((1 / v (phi y) : ℝ) : ℝ) • ((v (phi y) : ℂ)
          * Complex.exp (Complex.I * (psi (phi y) : ℂ)))
        = Complex.exp (Complex.I * (psi (phi y) : ℂ)) := by
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [heq] at h
    exact h
  have hYcurv : ∀ y, HasDerivAt (fun z => psi (phi z)) (k (phi y)) y := by
    intro y
    have h := (hpsi (phi y)).scomp y (hphideriv y)
    rw [hVnorm (phi y)] at h
    have hvne : v (phi y) ≠ 0 := ne_of_gt (hvpos (phi y))
    have heq : (1 / v (phi y)) • (k (phi y) * v (phi y)) = k (phi y) := by
      rw [smul_eq_mul, mul_comm (k (phi y)) (v (phi y)), ← mul_assoc, one_div,
        inv_mul_cancel₀ hvne, one_mul]
    rw [heq] at h
    exact h
  have hYper : Periodic (fun y => g (phi y)) L := by
    intro y
    show g (phi (y + L)) = g (phi y)
    rw [hphiper y, hgper (phi y)]
  refine ⟨fun y => g (phi y), phi, L, ⟨L, hLpos, hYper, ?_, fun y => psi (phi y), hYderiv,
    fun y => k (phi y), hYcurv, fun y => hkpos _⟩, ?_, hLpos, hYper,
    hphisurj, hphic, hphiper, fun y => rfl, hYderiv, hYcurv, ?_⟩
  · -- injectivity on one period
    have hphi0 : phi 0 = 0 := by
      have h := hphileft 0
      simp only [MarkedReparam.arcLength, intervalIntegral.integral_same] at h
      exact h
    have hphiL : phi L = p := by
      have h := hphiper 0
      rw [hphi0] at h
      simpa using h
    have hphimono : StrictMono phi := by
      refine strictMono_of_deriv_pos fun y => ?_
      rw [(hphideriv y).deriv]
      have := hvpos (phi y)
      rw [hVnorm (phi y)]
      positivity
    intro y1 hy1 y2 hy2 hgy
    have hmem : ∀ y ∈ Ico (0:ℝ) L, phi y ∈ Ico (0:ℝ) p := by
      intro y hy
      constructor
      · rw [← hphi0]; exact hphimono.monotone hy.1
      · rw [← hphiL]; exact hphimono hy.2
    exact hphimono.injective (hinj (hmem y1 hy1) (hmem y2 hy2) hgy)
  · -- the image is unchanged
    apply Set.range_comp_subset_range (f := phi) (g := g) |>.antisymm
    rintro _ ⟨u, rfl⟩
    refine ⟨MarkedReparam.arcLength V u, ?_⟩
    show g (phi (MarkedReparam.arcLength V u)) = g u
    rw [hphileft u]
  · -- the period of the reparametrization is the length of one period
    rw [hL, UnitTangentOval.periodLength]
    exact intervalIntegral.integral_congr (fun s _ => hVnorm s)

/-- **The selected rear is an oval up to reparametrization.**  The rear track
of a front, built from a periodic steering angle with `cos δ > 0` and
`tan δ > 0` (the selected rear of a front with `0 < K ≤ κ̂ < 1`), is a closed
regular curve of positive curvature, hence an oval after reparametrization by
its own arclength. -/
theorem isOval_reparam_rearTrack {F : ℝ → ℂ} {Θ delta K : ℝ → ℝ} {p c : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hcos : ∀ s, c ≤ Real.cos (delta s))
    (hdc : Continuous delta) (hΘc : Continuous Θ)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (htan : ∀ s, 0 < Real.tan (delta s))
    (hRper : Periodic (RearTrack.rearTrack F Θ delta) p)
    (hdper : Periodic delta p)
    (htanper : ∀ s, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (s + p) : ℂ))
      = Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)))
    (hinj : InjOn (RearTrack.rearTrack F Θ delta) (Ico 0 p)) :
    ∃ (Y : ℝ → ℂ) (phi : ℝ → ℝ) (L : ℝ),
      MainTheoremConditional.IsOval Y ∧
      range Y = range (RearTrack.rearTrack F Θ delta) ∧
      0 < L ∧ Periodic Y L ∧
      Surjective phi ∧ Continuous phi ∧ (∀ y, phi (y + L) = phi y + p) ∧
      (∀ y, Y y = RearTrack.rearTrack F Θ delta (phi y)) ∧
      (∀ y, HasDerivAt Y
        (Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (phi y) : ℂ))) y) ∧
      (∀ y, HasDerivAt (fun z => RearTrack.rearAngle Θ delta (phi z))
        (Real.tan (delta (phi y))) y) ∧
      L = ∫ s in (0:ℝ)..p, Real.cos (delta s) := by
  have hcospos : ∀ s, 0 < Real.cos (delta s) := fun s => lt_of_lt_of_le hc (hcos s)
  refine isOval_reparam_of_regular (psi := RearTrack.rearAngle Θ delta)
    (v := fun s => Real.cos (delta s)) (k := fun s => Real.tan (delta s))
    hp hc hcos (Real.continuous_cos.comp hdc) (hΘc.sub hdc) ?_ ?_ htan hRper ?_ htanper hinj
  · exact fun s => RearTrack.hasDerivAt_rearTrack (hF s) (hΘ s) (hode s)
  · exact fun s => RearTrack.rear_curvature_eq_tan (hΘ s) (hode s) (ne_of_gt (hcospos s))
  · exact fun s => by simp [hdper s]

/-- **The selected rear is an oval whose unit-tangent transform retraces the
front.**  Under the hypotheses of `isOval_reparam_rearTrack` there is an oval
`Y` (the rear reparametrized by its own arclength) with
`range (𝒯 Y) = range F`: the unit-tangent transform of the rear sweeps out
exactly the front curve.  This is the orbit condition
`range (X (n+1)) = range (𝒯 (X n))` used in the marked-scheme formulation. -/
theorem exists_isOval_rear_unitTangent_range_eq {F : ℝ → ℂ} {Θ delta K : ℝ → ℝ} {p c : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hcos : ∀ s, c ≤ Real.cos (delta s))
    (hdc : Continuous delta) (hΘc : Continuous Θ)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (htan : ∀ s, 0 < Real.tan (delta s))
    (hRper : Periodic (RearTrack.rearTrack F Θ delta) p)
    (hdper : Periodic delta p)
    (htanper : ∀ s, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (s + p) : ℂ))
      = Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)))
    (hinj : InjOn (RearTrack.rearTrack F Θ delta) (Ico 0 p)) :
    ∃ (Y : ℝ → ℂ) (phi : ℝ → ℝ) (L : ℝ),
      MainTheoremConditional.IsOval Y ∧
      range Y = range (RearTrack.rearTrack F Θ delta) ∧
      range (UnitTangent.unitTangentMap Y) = range F ∧
      0 < L ∧ Periodic Y L ∧
      Surjective phi ∧ Continuous phi ∧ (∀ y, phi (y + L) = phi y + p) ∧
      (∀ y, HasDerivAt Y
        (Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (phi y) : ℂ))) y) ∧
      (∀ y, HasDerivAt (fun z => RearTrack.rearAngle Θ delta (phi z))
        (Real.tan (delta (phi y))) y) ∧
      L = ∫ s in (0:ℝ)..p, Real.cos (delta s) := by
  obtain ⟨Y, phi, L, hoval, hrange, hLpos, hYper, hsurj, hphic, hphiper, hYval, hYderiv,
    hYcurv, hLeq⟩ :=
    isOval_reparam_rearTrack hp hc hcos hdc hΘc hF hΘ hode htan hRper hdper htanper hinj
  refine ⟨Y, phi, L, hoval, hrange, ?_, hLpos, hYper, hsurj, hphic, hphiper, hYderiv, hYcurv,
    hLeq⟩
  have hpt : ∀ y, UnitTangent.unitTangentMap Y y = F (phi y) := by
    intro y
    rw [UnitTangent.unitTangentMap, hYval y, (hYderiv y).deriv,
      RearTrack.unitTangentMap_rearTrack]
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨phi y, (hpt y).symm⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj s
    exact ⟨y, hpt y⟩

end RearOval
