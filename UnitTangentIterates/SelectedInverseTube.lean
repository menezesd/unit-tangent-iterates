import Mathlib
import UnitTangentIterates.ChordArc
import UnitTangentIterates.SelectedInverseOval
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.MarkedSpaceReparam

/-!
# The selected inverse as a map of marked curves

`SelectedInverseOval.lean` produces, from an admissible oval front, an oval
rear whose unit-tangent transform retraces the front, and `MarkedSpace.lean`
constructs the tube of marked curves in which the shadowing scheme of *A
Noncircular Oval with Convex Unit-Tangent Iterates* is run.  This file joins
the two: **the selected inverse takes a marked curve to a marked curve.**

The front data of a marked curve are read off first
(`exists_front_data`: the arclength parametrization of a tube member is a
unit-speed closed curve whose curvature is pinched between the tube's lower
bound and any assumed upper bound), the selected rear is produced by
`SelectedInverseOval.exists_oval_rear_of_oval_front`, and the resulting oval is
put back into the normalized parameter, its chord-arc constant being supplied
by `ChordArc.exists_chord_arc` — so that no chord-arc hypothesis on the rear is
needed.

Main result (`exists_tube_member_rear`): a member `p` of the tube whose
curvature is pinched by `0 < kmin ≤ K ≤ κ̂ < 1` has a **marked selected
inverse**: a member `q` of the tube, of curvature at least
`kmin/√(1−kmin²)` and at most `κ̂/√(1−κ̂²)`, whose arclength parametrization is
an oval with

```
  range (𝒯 (ev q)) = range (ev p) ,
```

that is, whose unit-tangent transform retraces `p`.  Its chord-arc constant is
produced, not assumed.  As everywhere in this project, the global topological
fact that the rear track is embedded is carried as an explicit hypothesis.
-/

noncomputable section

open Set Function

namespace SelectedInverseTube

open MarkedSpace

/-! ### Reading off the front data of a marked curve -/

/-- The velocity of a marked curve is periodic. -/
theorem periodic_vel {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p) :
    Periodic (⇑p.2.1) 1 := by
  intro u
  have h1 : HasDerivAt (⇑p.1) (p.2.1 (u + 1)) u := by
    have h := (hp.hasDerivAt_curve (u + 1)).comp_add_const u 1
    rwa [hp.periodic.funext] at h
  exact h1.unique (hp.hasDerivAt_curve u)

/-- The acceleration of a marked curve is periodic. -/
theorem periodic_acc {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p) :
    Periodic (⇑p.2.2) 1 := by
  intro u
  have h1 : HasDerivAt (⇑p.2.1) (p.2.2 (u + 1)) u := by
    have h := (hp.hasDerivAt_vel (u + 1)).comp_add_const u 1
    rwa [(periodic_vel hp).funext] at h
  exact h1.unique (hp.hasDerivAt_vel u)

/-- **The front data of a marked curve.**  The arclength parametrization of a
member of the tube is a closed unit-speed curve with a tangent angle whose
derivative — the curvature — is continuous, periodic, at least the tube's lower
bound and at most any assumed upper bound. -/
theorem exists_front_data {c kmin delta kap : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin delta p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3) :
    ∃ Θ K : ℝ → ℝ, Continuous K ∧ Periodic K (perim p) ∧
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ (K s) s) ∧ (∀ s, kmin ≤ K s) ∧ (∀ s, K s ≤ kap) := by
  set L : ℝ := perim p with hL
  have hLpos : 0 < L := perim_pos hc hp
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  set tau : ℝ → ℂ := fun s => p.2.1 (s / L) / L with htaudef
  set D : ℝ → ℂ := fun s => p.2.2 (s / L) / (L ^ 2) with hDdef
  have hev : ∀ s, HasDerivAt (ev p) (tau s) s := by
    intro s
    have h := (hp.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [ev, hL, htaudef, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, mul_comm] using h
  have hDderiv : ∀ s, HasDerivAt tau (D s) s := by
    intro s
    have h0 := (hp.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h := h0.div_const L
    simpa [htaudef, hDdef, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, sq, mul_comm,
      mul_assoc, mul_left_comm] using h
  have hnorm : ∀ s, ‖tau s‖ = 1 := by
    intro s
    rw [htaudef]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    rw [norm_vel_eq_perim hp, ← hL]
    field_simp
  have hDcont : Continuous D := by
    have h : Continuous fun s : ℝ => p.2.2 (s / L) :=
      p.2.2.continuous.comp (continuous_id.div_const L)
    exact h.div_const _
  obtain ⟨theta, hthetaderiv, hthetaexp⟩ := exists_angle hnorm hDderiv hDcont
  -- the curvature in arclength
  have hkey : ∀ s, ((starRingEnd ℂ) (tau s) * D s).im
      = ((starRingEnd ℂ) (p.2.1 (s / L)) * p.2.2 (s / L)).im / L ^ 3 := by
    intro s
    have h : (starRingEnd ℂ) (tau s) * D s
        = ((starRingEnd ℂ) (p.2.1 (s / L)) * p.2.2 (s / L)) / ((L ^ 3 : ℝ) : ℂ) := by
      rw [htaudef, hDdef]
      simp only [map_div₀, Complex.conj_ofReal]
      push_cast
      field_simp
    rw [h, Complex.div_ofReal_im]
  refine ⟨theta, fun s => ((starRingEnd ℂ) (tau s) * D s).im, ?_, ?_, ?_, hthetaderiv, ?_, ?_⟩
  · -- continuity
    have hcontTau : Continuous tau := by
      have h : Continuous fun s : ℝ => p.2.1 (s / L) :=
        p.2.1.continuous.comp (continuous_id.div_const L)
      exact h.div_const _
    exact Complex.continuous_im.comp ((Complex.continuous_conj.comp hcontTau).mul hDcont)
  · -- periodicity
    intro s
    have h1 : (s + L) / L = s / L + 1 := by field_simp
    simp only [htaudef, hDdef, h1]
    rw [(periodic_vel hp) (s / L), (periodic_acc hp) (s / L)]
  · -- unit speed
    intro s
    rw [hthetaexp s]
    exact hev s
  · -- lower bound
    intro s
    show kmin ≤ ((starRingEnd ℂ) (tau s) * D s).im
    rw [hkey s]
    have hb := hp.curv_lb (s / L)
    rw [norm_vel_eq_perim hp, ← hL] at hb
    have hL3 : 0 < L ^ 3 := by positivity
    rw [le_div_iff₀ hL3]
    linarith
  · -- upper bound
    intro s
    show ((starRingEnd ℂ) (tau s) * D s).im ≤ kap
    rw [hkey s]
    have hb := hub (s / L)
    rw [norm_vel_eq_perim hp, ← hL] at hb
    have hL3 : 0 < L ^ 3 := by positivity
    rw [div_le_iff₀ hL3]
    linarith

/-! ### Putting an oval back into the normalized parameter -/

/-- **An oval is a marked curve.**  A closed unit-speed curve of period `L` with
continuous curvature `k` bounded below by `kmin > 0`, injective on a period,
becomes, in the normalized parameter `u = s/L`, a member of the tube of marked
curves — with a chord-arc constant produced by `ChordArc.exists_chord_arc`.
Moreover its arclength parametrization is the curve itself, and any pointwise
bound on `k` is reproduced as a bound on the curvature of the marked curve. -/
theorem exists_tube_member_of_oval {Y : ℝ → ℂ} {th k : ℝ → ℝ} {L kmin kmax : ℝ}
    (hLpos : 0 < L) (hYper : Periodic Y L) (hinj : InjOn Y (Ico 0 L))
    (hY : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th s : ℂ))) s)
    (hth : ∀ s, HasDerivAt th (k s) s) (hkc : Continuous k) (hkper : Periodic k L)
    (hkmin : ∀ s, kmin ≤ k s) (hkmax : ∀ s, k s ≤ kmax) :
    ∃ (q : Data) (d : ℝ), 0 < d ∧ IsTubeMember L kmin d q ∧ perim q = L ∧
      ev q = Y ∧
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
    exact (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
      this))))
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
  -- the chord-arc constant
  have hinj1 : InjOn g (Ico 0 1) := by
    intro u hu v hv huv
    have hLu : L * u ∈ Ico (0 : ℝ) L := by
      constructor
      · exact mul_nonneg hLpos.le hu.1
      · nlinarith [hu.2, hu.1]
    have hLv : L * v ∈ Ico (0 : ℝ) L := by
      constructor
      · exact mul_nonneg hLpos.le hv.1
      · nlinarith [hv.2, hv.1]
    have := hinj hLu hLv huv
    exact mul_left_cancel₀ hLne this
  obtain ⟨d, hdpos, hd⟩ :=
    ChordArc.exists_chord_arc hLpos hgderiv hWcont hWper hgper (fun u => le_of_eq (hWnorm u).symm)
      hinj1
  -- the bounded continuous data
  obtain ⟨CY, hCY⟩ := MarkedSpace.exists_bound_of_periodic hgcont hgper
  obtain ⟨CB, hCB⟩ := MarkedSpace.exists_bound_of_periodic hBcont hBper
  refine ⟨(BoundedContinuousFunction.ofNormedAddCommGroup g hgcont CY hCY,
    BoundedContinuousFunction.ofNormedAddCommGroup W hWcont L (fun u => le_of_eq (hWnorm u)),
    BoundedContinuousFunction.ofNormedAddCommGroup B hBcont CB hCB), d, hdpos, ?_, ?_, ?_, ?_⟩
  · refine ⟨hgderiv, hWderiv, hgper, ?_, ?_, ?_, ?_⟩
    · intro u v
      show ‖W u‖ = ‖W v‖
      rw [hWnorm u, hWnorm v]
    · intro u
      show L ≤ ‖W u‖
      rw [hWnorm u]
    · intro u
      show kmin * ‖W u‖ ^ 3 ≤ ((starRingEnd ℂ) (W u) * B u).im
      rw [hWnorm u]
      have him : ((starRingEnd ℂ) (W u) * B u).im = L ^ 3 * k (L * u) := by
        have hconj : (starRingEnd ℂ) (W u) = (L : ℂ) * (starRingEnd ℂ) (tau (L * u)) := by
          rw [hW]
          simp
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
      rw [him]
      have hL3 : 0 < L ^ 3 := by positivity
      nlinarith [hkmin (L * u)]
    · intro u hu v hv
      exact hd u hu v hv
  · show ‖W 0‖ = L
    rw [hWnorm 0]
  · -- the arclength parametrization is `Y` itself
    have hperim : perim (BoundedContinuousFunction.ofNormedAddCommGroup g hgcont CY hCY,
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
    have him : ((starRingEnd ℂ) (W u) * B u).im = L ^ 3 * k (L * u) := by
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
    rw [him, hWnorm u]
    have hL3 : 0 < L ^ 3 := by positivity
    nlinarith [hkmax (L * u)]


/-! ### Identification and periodicity of the curvature -/

/-- Two tangent-angle presentations of the same curve have the same curvature. -/
theorem curvature_unique {Y : ℝ → ℂ} {th1 th2 k1 k2 : ℝ → ℝ}
    (hY1 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th1 s : ℂ))) s)
    (hY2 : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th2 s : ℂ))) s)
    (hth1 : ∀ s, HasDerivAt th1 (k1 s) s) (hth2 : ∀ s, HasDerivAt th2 (k2 s) s) (s : ℝ) :
    k1 s = k2 s := by
  have hexp : ∀ t, Complex.exp (Complex.I * (th1 t : ℂ)) = Complex.exp (Complex.I * (th2 t : ℂ)) :=
    fun t => (hY1 t).unique (hY2 t)
  have hd1 : HasDerivAt (fun t => Complex.exp (Complex.I * (th1 t : ℂ)))
      (Complex.exp (Complex.I * (th1 s : ℂ)) * (Complex.I * (k1 s : ℂ))) s := by
    simpa using (((hth1 s).ofReal_comp).const_mul Complex.I).cexp
  have hd2 : HasDerivAt (fun t => Complex.exp (Complex.I * (th2 t : ℂ)))
      (Complex.exp (Complex.I * (th2 s : ℂ)) * (Complex.I * (k2 s : ℂ))) s := by
    simpa using (((hth2 s).ofReal_comp).const_mul Complex.I).cexp
  have hd1' : HasDerivAt (fun t => Complex.exp (Complex.I * (th2 t : ℂ)))
      (Complex.exp (Complex.I * (th1 s : ℂ)) * (Complex.I * (k1 s : ℂ))) s := by
    have : (fun t => Complex.exp (Complex.I * (th1 t : ℂ)))
        = fun t => Complex.exp (Complex.I * (th2 t : ℂ)) := funext hexp
    rwa [this] at hd1
  have heq := hd1'.unique hd2
  rw [hexp s] at heq
  have hne : Complex.exp (Complex.I * (th2 s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hI : (Complex.I * (k1 s : ℂ)) = (Complex.I * (k2 s : ℂ)) := mul_left_cancel₀ hne heq
  have := mul_left_cancel₀ Complex.I_ne_zero hI
  exact_mod_cast this

/-- The curvature of a closed curve is periodic with the curve's period. -/
theorem curvature_periodic {Y : ℝ → ℂ} {th k : ℝ → ℝ} {L : ℝ}
    (hY : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th s : ℂ))) s)
    (hth : ∀ s, HasDerivAt th (k s) s) (hper : Periodic Y L) : Periodic k L := by
  have htanper : ∀ s, Complex.exp (Complex.I * (th (s + L) : ℂ))
      = Complex.exp (Complex.I * (th s : ℂ)) :=
    SelectedInverseOval.expTangent_periodic hY hper
  intro s
  have hd : HasDerivAt (fun t => Complex.exp (Complex.I * (th t : ℂ)))
      (Complex.exp (Complex.I * (th s : ℂ)) * (Complex.I * (k s : ℂ))) s := by
    simpa using (((hth s).ofReal_comp).const_mul Complex.I).cexp
  have hdshift : HasDerivAt (fun t => Complex.exp (Complex.I * (th (t + L) : ℂ)))
      (Complex.exp (Complex.I * (th (s + L) : ℂ)) * (Complex.I * (k (s + L) : ℂ))) s := by
    have h := (((hth (s + L)).ofReal_comp).const_mul Complex.I).cexp.comp_add_const s L
    simpa using h
  have hfun : (fun t => Complex.exp (Complex.I * (th (t + L) : ℂ)))
      = fun t => Complex.exp (Complex.I * (th t : ℂ)) := funext htanper
  rw [hfun] at hdshift
  have heq := hdshift.unique hd
  rw [htanper s] at heq
  have hne : Complex.exp (Complex.I * (th s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hI : (Complex.I * (k (s + L) : ℂ)) = (Complex.I * (k s : ℂ)) := mul_left_cancel₀ hne heq
  have := mul_left_cancel₀ Complex.I_ne_zero hI
  exact_mod_cast this

/-- **An oval with continuous pinched curvature is a marked curve.**  If `Y` is
an oval and, in some presentation, has unit tangent `e^{i·th}` and continuous
curvature `k` pinched between `kmin > 0` and `kmax`, then `Y` is the arclength
parametrization of a member of the tube — of curvature at least `kmin` and at
most `kmax`, and with a chord-arc constant that is produced, not assumed.  The
period, the injectivity and the positivity of the curvature are taken from
`IsOval`; the curvature of the two presentations is identified by
`curvature_unique`. -/
theorem exists_tube_member_of_oval_data {Y : ℝ → ℂ} {th k : ℝ → ℝ} {kmin kmax : ℝ}
    (hoval : MainTheoremConditional.IsOval Y)
    (hY : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th s : ℂ))) s)
    (hth : ∀ s, HasDerivAt th (k s) s) (hkc : Continuous k)
    (hkmin : ∀ s, kmin ≤ k s) (hkmax : ∀ s, k s ≤ kmax) :
    ∃ (q : Data) (L d : ℝ), 0 < L ∧ 0 < d ∧ IsTubeMember L kmin d q ∧ perim q = L ∧
      ev q = Y ∧ (∀ T, 0 < T → Periodic Y T → L ≤ T) ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kmax * ‖q.2.1 u‖ ^ 3 := by
  obtain ⟨LY, hLYpos, hYperL, hinjY, thY, hYderiv, kYo, hthY, hkYopos⟩ := hoval
  have hkeq : ∀ s, kYo s = k s := fun s => curvature_unique hYderiv hY hthY hth s
  have hkYocont : Continuous kYo := by
    have : kYo = k := funext hkeq
    rw [this]; exact hkc
  have hkYoper : Periodic kYo LY := curvature_periodic hYderiv hthY hYperL
  obtain ⟨q, d, hdpos, hmem, hperimq, hevq, hqub⟩ :=
    exists_tube_member_of_oval hLYpos hYperL hinjY hYderiv hthY hkYocont hkYoper
      (fun s => by rw [hkeq s]; exact hkmin s) (fun s => by rw [hkeq s]; exact hkmax s)
  refine ⟨q, LY, d, hLYpos, hdpos, hmem, hperimq, hevq, ?_, hqub⟩
  -- the period of an oval is its minimal period: any smaller period would
  -- contradict injectivity on `[0, LY)`
  intro T hTpos hTper
  by_contra hlt
  push_neg at hlt
  have hTmem : T ∈ Ico (0 : ℝ) LY := ⟨hTpos.le, hlt⟩
  have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) LY := ⟨le_refl _, hLYpos⟩
  have hYT : Y T = Y 0 := by simpa using hTper 0
  exact absurd (hinjY hTmem h0mem hYT) (ne_of_gt hTpos)

/-- **A closed regular curve of positive curvature is a marked curve.**  If `g`
is a closed curve of period `p`, with speed `v ≥ c > 0`, tangent angle `psi`
turning at rate `psi' = k·v` with the curvature `k` continuous and pinched
between `kmin > 0` and `kmax`, and `g` is injective on one period, then `g` is,
after reparametrization by arclength, a member of the tube of marked curves
with the same image — the chord-arc constant being produced, not assumed. -/
theorem exists_tube_member_of_regular {g : ℝ → ℂ} {psi v k : ℝ → ℝ} {p c kmin kmax : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hkminpos : 0 < kmin) (hspeed : ∀ s, c ≤ v s)
    (hvc : Continuous v) (hpsic : Continuous psi)
    (hg : ∀ s, HasDerivAt g ((v s : ℂ) * Complex.exp (Complex.I * (psi s : ℂ))) s)
    (hpsi : ∀ s, HasDerivAt psi (k s * v s) s) (hkc : Continuous k)
    (hkmin : ∀ s, kmin ≤ k s) (hkmax : ∀ s, k s ≤ kmax)
    (hgper : Periodic g p) (hvper : Periodic v p)
    (htanper : ∀ s, Complex.exp (Complex.I * (psi (s + p) : ℂ))
      = Complex.exp (Complex.I * (psi s : ℂ)))
    (hinj : InjOn g (Ico 0 p)) :
    ∃ (q : Data) (L d : ℝ), 0 < L ∧ 0 < d ∧ IsTubeMember L kmin d q ∧ perim q = L ∧
      MainTheoremConditional.IsOval (ev q) ∧ range (ev q) = range g ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kmax * ‖q.2.1 u‖ ^ 3 := by
  obtain ⟨Y, phi, LY, hoval, hrange, -, -, -, hphic, -, -, hYderiv, hYcurv, -⟩ :=
    RearOval.isOval_reparam_of_regular hp hc hspeed hvc hpsic hg hpsi
      (fun s => lt_of_lt_of_le hkminpos (hkmin s)) hgper hvper htanper hinj
  obtain ⟨q, L, d, hLpos, hdpos, hmem, hperimq, hevq, -, hqub⟩ :=
    exists_tube_member_of_oval_data hoval hYderiv hYcurv (hkc.comp hphic)
      (fun y => hkmin (phi y)) (fun y => hkmax (phi y))
  refine ⟨q, L, d, hLpos, hdpos, hmem, hperimq, ?_, ?_, hqub⟩
  · rw [hevq]; exact hoval
  · rw [hevq]; exact hrange

/-! ### The selected inverse of a marked curve -/

/-- **The selected inverse takes a marked curve to a marked curve.**  Let `p` be
a member of the tube of marked curves whose curvature, in arclength, is pinched
by `0 < kmin ≤ K ≤ κ̂ < 1`.  Then there is a member `q` of the tube — of
curvature at least `kmin/√(1−kmin²)` and at most `κ̂/√(1−κ̂²)`, with a chord-arc
constant that is produced rather than assumed — whose arclength parametrization
is an oval whose unit-tangent transform retraces `p`:

```
  range (𝒯 (ev q)) = range (ev p) .
```

As everywhere in this project, the global topological fact that the rear track
is embedded is carried as an explicit hypothesis. -/
theorem exists_tube_member_rear {c kmin delta kap : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkap1 : kap < 1) {p : Data} (hp : IsTubeMember c kmin delta p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    ∃ (q : Data) (LR dR : ℝ), 0 < LR ∧ 0 < dR ∧
      IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR q ∧
      perim q = LR ∧ perim q ≤ perim p ∧
      MainTheoremConditional.IsOval (ev q) ∧
      (∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) * ‖q.2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev p) := by
  have hLpos : 0 < perim p := perim_pos hc hp
  obtain ⟨Θ, K, hKc, hKper, hX, hΘ, hKlow, hKhigh⟩ := exists_front_data hc hp hub
  obtain ⟨Y, th, kY, qper, hoval, hrange, hqpos, hYper, hkYc, -, hY, hth, hpinch, hqle⟩ :=
    SelectedInverseOval.exists_oval_rear_of_oval_front hLpos hkmin hkap1 hKc hKper hX hΘ
      (periodic_ev hc hp) hKlow hKhigh (fun dl hdlper hdlmem hdlode =>
        hinjR Θ K dl hX hΘ hdlper hdlmem hdlode)
  obtain ⟨q, LR, dR, hLRpos, hdRpos, hmem, hperimq, hevq, hmin, hqub⟩ :=
    exists_tube_member_of_oval_data hoval hY hth hkYc
      (fun s => (hpinch s).1) (fun s => (hpinch s).2)
  refine ⟨q, LR, dR, hLRpos, hdRpos, hmem, hperimq, ?_, ?_, hqub, ?_⟩
  · -- the rear is not longer than the front
    rw [hperimq]
    exact le_trans (hmin qper hqpos (hevq ▸ hYper)) hqle
  · rw [hevq]; exact hoval
  · rw [hevq]; exact hrange

end SelectedInverseTube
