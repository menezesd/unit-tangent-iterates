import Mathlib
import UnitTangentIterates.SelectedInverseTube

/-!
# Marked curves with a prescribed chord-arc constant

`SelectedInverseTube.exists_tube_member_of_oval` turns a closed unit-speed
curve with pinched curvature into a member of the tube of marked curves, the
chord-arc constant being *produced* from embeddedness by a compactness argument
(`ChordArc.lean`).  For a whole family of curves that is not enough: the tube
of `MarkedSpace.lean` is cut out by one fixed constant, so a family lives in a
single tube only when the chord-arc bound is uniform.

This file gives the variant in which the constant is prescribed:
`exists_tube_member_of_oval_chord` asks for the quantitative chord-arc bound

`dlt · min(|x−y|, L−|x−y|) ≤ ‖Y x − Y y‖`

in the arclength of the curve, and returns a marked curve with chord-arc
constant `dlt·L` in the normalized parameter.  `IsTubeMember.mono` records that
membership only improves when the speed and the chord-arc constant asked for are
lowered, so a family of curves with a common chord-arc bound and perimeters
bounded below lies in one tube.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-- The cyclic distance of the normalized parameter is nonnegative on `[0,1]`. -/
theorem cyc_nonneg {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ cyc u v := by
  have h1 : |u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [hu.1, hu.2, hv.1, hv.2]; linarith [hu.1, hu.2, hv.1, hv.2]]
  exact le_min (abs_nonneg _) (by linarith)

/-- **Membership in the tube is monotone in its constants**: lowering the speed
bound and the chord-arc constant only weakens the requirement. -/
theorem IsTubeMember.mono {c c' kmin delta delta' : ℝ} {p : Data}
    (hp : IsTubeMember c kmin delta p) (hc : c' ≤ c) (hd : delta' ≤ delta) :
    IsTubeMember c' kmin delta' p where
  hasDerivAt_curve := hp.hasDerivAt_curve
  hasDerivAt_vel := hp.hasDerivAt_vel
  periodic := hp.periodic
  speed_const := hp.speed_const
  speed_lb := fun u => le_trans hc (hp.speed_lb u)
  curv_lb := hp.curv_lb
  chord := by
    intro u hu v hv
    refine le_trans ?_ (hp.chord u hu v hv)
    exact mul_le_mul_of_nonneg_right hd (cyc_nonneg hu hv)

/-- **An oval with a prescribed chord-arc constant is a marked curve.**  A
closed unit-speed curve of period `L` with continuous curvature `k`, satisfying
the quantitative chord-arc bound `dlt·min(|x−y|, L−|x−y|) ≤ ‖Y x − Y y‖` on a
period, is a member of the tube of marked curves with chord-arc constant
`dlt·L`; its arclength parametrization is the curve itself and any pointwise
bound on `k` is reproduced. -/
theorem exists_tube_member_of_oval_chord {Y : ℝ → ℂ} {th k : ℝ → ℝ} {L kmin kmax dlt : ℝ}
    (hLpos : 0 < L) (hYper : Periodic Y L)
    (hY : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th s : ℂ))) s)
    (hth : ∀ s, HasDerivAt th (k s) s) (hkc : Continuous k) (hkper : Periodic k L)
    (hkmin : ∀ s, kmin ≤ k s) (hkmax : ∀ s, k s ≤ kmax)
    (hchord : ∀ x ∈ Icc (0:ℝ) L, ∀ y ∈ Icc (0:ℝ) L,
      dlt * min |x - y| (L - |x - y|) ≤ ‖Y x - Y y‖) :
    ∃ q : Data, IsTubeMember L kmin (dlt * L) q ∧ perim q = L ∧ ev q = Y ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kmax * ‖q.2.1 u‖ ^ 3 := by
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- the tangent field and its periodicity
  set tau : ℝ → ℂ := fun s => Complex.exp (Complex.I * (th s : ℂ)) with htau
  have htauper : ∀ s, tau (s + L) = tau s := by
    intro s
    have h := (hY (s + L)).comp_add_const s L
    rw [hYper.funext] at h
    exact h.unique (hY s)
  have htaunorm : ∀ s, ‖tau s‖ = 1 := by
    intro s
    rw [htau]
    simp [Complex.norm_exp]
  have htauderiv : ∀ s, HasDerivAt tau (Complex.I * (k s : ℂ) * tau s) s := by
    intro s
    have h := (((hth s).ofReal_comp).const_mul Complex.I).cexp
    simpa [htau, mul_comm, mul_assoc, mul_left_comm] using h
  have htaucont : Continuous tau := by
    have : Continuous th := Differentiable.continuous fun s => (hth s).differentiableAt
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp this))
  -- the rescaled data
  set g : ℝ → ℂ := fun u => Y (L * u) with hg
  set W : ℝ → ℂ := fun u => (L : ℂ) * tau (L * u) with hW
  set B : ℝ → ℂ := fun u => ((L : ℂ) ^ 2) * (Complex.I * (k (L * u) : ℂ) * tau (L * u)) with hB
  have hscale : ∀ u : ℝ, HasDerivAt (fun u : ℝ => L * u) L u := by
    intro u
    simpa using (hasDerivAt_id u).const_mul L
  have hgderiv : ∀ u, HasDerivAt g (W u) u := by
    intro u
    have h := (hY (L * u)).scomp u (hscale u)
    simpa [hg, hW, htau, Function.comp, smul_eq_mul, mul_comm] using h
  have hWderiv : ∀ u, HasDerivAt W (B u) u := by
    intro u
    have h := ((htauderiv (L * u)).scomp u (hscale u)).const_mul (L : ℂ)
    simpa [hW, hB, Function.comp, smul_eq_mul, sq, mul_comm, mul_assoc, mul_left_comm] using h
  have hgper : Periodic g 1 := by
    intro u
    simp only [hg, mul_add, mul_one]
    exact hYper (L * u)
  have hWper : Periodic W 1 := by
    intro u
    simp only [hW, mul_add, mul_one]
    rw [htauper (L * u)]
  have hBper : Periodic B 1 := by
    intro u
    simp only [hB, mul_add, mul_one]
    rw [htauper (L * u), hkper (L * u)]
  have hWnorm : ∀ u, ‖W u‖ = L := by
    intro u
    rw [hW]
    simp [htaunorm, abs_of_pos hLpos]
  have hgcont : Continuous g := Differentiable.continuous fun u => (hgderiv u).differentiableAt
  have hWcont : Continuous W := Differentiable.continuous fun u => (hWderiv u).differentiableAt
  have hBcont : Continuous B := by
    have hkcomp : Continuous fun u : ℝ => (k (L * u) : ℂ) :=
      Complex.continuous_ofReal.comp (hkc.comp (continuous_const.mul continuous_id))
    have htaucomp : Continuous fun u : ℝ => tau (L * u) :=
      htaucont.comp (continuous_const.mul continuous_id)
    exact continuous_const.mul ((continuous_const.mul hkcomp).mul htaucomp)
  -- the chord-arc bound in the normalized parameter
  have hd : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, dlt * L * cyc u v ≤ ‖g u - g v‖ := by
    intro u hu v hv
    have hLu : L * u ∈ Icc (0:ℝ) L := by
      constructor
      · exact mul_nonneg hLpos.le hu.1
      · nlinarith [hu.1, hu.2]
    have hLv : L * v ∈ Icc (0:ℝ) L := by
      constructor
      · exact mul_nonneg hLpos.le hv.1
      · nlinarith [hv.1, hv.2]
    have habs : |L * u - L * v| = L * |u - v| := by
      rw [show L * u - L * v = L * (u - v) by ring, abs_mul, abs_of_pos hLpos]
    have hmin : min |L * u - L * v| (L - |L * u - L * v|) = L * cyc u v := by
      rw [habs, cyc, mul_min_of_nonneg _ _ hLpos.le]
      congr 1
      ring
    have h := hchord (L * u) hLu (L * v) hLv
    rw [hmin] at h
    calc dlt * L * cyc u v = dlt * (L * cyc u v) := by ring
      _ ≤ ‖g u - g v‖ := h
  -- the bounded continuous data
  obtain ⟨CY, hCY⟩ := MarkedSpace.exists_bound_of_periodic hgcont hgper
  obtain ⟨CB, hCB⟩ := MarkedSpace.exists_bound_of_periodic hBcont hBper
  have him : ∀ u, ((starRingEnd ℂ) (W u) * B u).im = L ^ 3 * k (L * u) := by
    intro u
    have hconj : (starRingEnd ℂ) (W u) = (L : ℂ) * (starRingEnd ℂ) (tau (L * u)) := by
      rw [hW]; simp
    rw [hconj, hB]
    have hmul : ((L : ℂ) * (starRingEnd ℂ) (tau (L * u)))
        * (((L : ℂ) ^ 2) * (Complex.I * (k (L * u) : ℂ) * tau (L * u)))
        = ((L : ℂ) ^ 3) * ((k (L * u) : ℂ) * Complex.I
          * ((starRingEnd ℂ) (tau (L * u)) * tau (L * u))) := by
      ring
    rw [hmul]
    have hsq : (starRingEnd ℂ) (tau (L * u)) * tau (L * u) = 1 := by
      have h2 := Complex.mul_conj (tau (L * u))
      rw [mul_comm] at h2
      rw [h2, Complex.normSq_eq_norm_sq, htaunorm (L * u)]
      norm_num
    rw [hsq, mul_one]
    simp [Complex.mul_im, ← Complex.ofReal_pow]
  refine ⟨(BoundedContinuousFunction.ofNormedAddCommGroup g hgcont CY hCY,
    BoundedContinuousFunction.ofNormedAddCommGroup W hWcont L (fun u => le_of_eq (hWnorm u)),
    BoundedContinuousFunction.ofNormedAddCommGroup B hBcont CB hCB), ?_, ?_, ?_, ?_⟩
  · refine ⟨hgderiv, hWderiv, hgper, ?_, ?_, ?_, ?_⟩
    · intro u v
      show ‖W u‖ = ‖W v‖
      rw [hWnorm u, hWnorm v]
    · intro u
      show L ≤ ‖W u‖
      rw [hWnorm u]
    · intro u
      show kmin * ‖W u‖ ^ 3 ≤ ((starRingEnd ℂ) (W u) * B u).im
      rw [hWnorm u, him u]
      have hL3 : 0 < L ^ 3 := by positivity
      nlinarith [hkmin (L * u)]
    · intro u hu v hv
      exact hd u hu v hv
  · show ‖W 0‖ = L
    rw [hWnorm 0]
  · have hperim : perim (BoundedContinuousFunction.ofNormedAddCommGroup g hgcont CY hCY,
        BoundedContinuousFunction.ofNormedAddCommGroup W hWcont L (fun u => le_of_eq (hWnorm u)),
        BoundedContinuousFunction.ofNormedAddCommGroup B hBcont CB hCB) = L := by
      show ‖W 0‖ = L
      rw [hWnorm 0]
    funext s
    show g (s / perim _) = Y s
    rw [hperim]
    show Y (L * (s / L)) = Y s
    rw [mul_div_cancel₀ s hLne]
  · intro u
    show ((starRingEnd ℂ) (W u) * B u).im ≤ kmax * ‖W u‖ ^ 3
    rw [him u, hWnorm u]
    have hL3 : 0 < L ^ 3 := by positivity
    nlinarith [hkmax (L * u)]

/-- **The chord-arc bound of a marked curve, in its arclength.**  The chord-arc
condition of the tube, written in the normalized parameter, is the quantitative
chord-arc bound with constant `delta/L` for the arclength parametrization. -/
theorem chord_arclength_of_tube {c kmin dlt : ℝ} (hc : 0 < c) {q : Data}
    (hq : IsTubeMember c kmin dlt q) :
    ∀ x ∈ Icc (0:ℝ) (perim q), ∀ y ∈ Icc (0:ℝ) (perim q),
      (dlt / perim q) * min |x - y| (perim q - |x - y|) ≤ ‖ev q x - ev q y‖ := by
  intro x hx y hy
  have hP : 0 < perim q := perim_pos hc hq
  have hu : x / perim q ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hx.1 hP.le, (div_le_one hP).2 hx.2⟩
  have hv : y / perim q ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hy.1 hP.le, (div_le_one hP).2 hy.2⟩
  have habs : |x / perim q - y / perim q| = |x - y| / perim q := by
    rw [div_sub_div_same, abs_div, abs_of_pos hP]
  have hcyc : cyc (x / perim q) (y / perim q)
      = (1 / perim q) * min |x - y| (perim q - |x - y|) := by
    rw [cyc, habs, mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / perim q)]
    congr 1
    · field_simp
    · field_simp
  have h := hq.chord _ hu _ hv
  rw [hcyc] at h
  calc (dlt / perim q) * min |x - y| (perim q - |x - y|)
      = dlt * ((1 / perim q) * min |x - y| (perim q - |x - y|)) := by ring
    _ ≤ ‖q.1 (x / perim q) - q.1 (y / perim q)‖ := h
    _ = ‖ev q x - ev q y‖ := rfl

end MarkedSpace
