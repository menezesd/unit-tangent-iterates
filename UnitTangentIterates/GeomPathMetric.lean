import Mathlib
import UnitTangentIterates.GeomPathDist

/-!
# The geometric path pseudodistance is a pseudometric

`GeomPathDist.geomPathDist` restricts the infimum defining `PathMetric.pathDist`
to the normal paths whose slices are constant-speed closed curves with the tube
bounds, so that the increment bound `NormalPathC2Increment.dist_le_cost` passes
to the infimum.  For that restricted infimum to be a *pseudodistance* one has to
know that the restricted class of paths is closed under the three structural
operations of `PathMetric`: the constant path, the reversal and the
concatenation.  This file proves exactly that, for the slightly strengthened
predicate

* `IsGeomNormalPath P₀ P₁ κ̂ Γ` — the hypothesis bundle of
  `NormalPathC2Increment.IsConstantSpeedNormalPath` with the *two-sided* bound
  `P₀ ≤ P t ≤ P₁` on the perimeter of the slices (the constant `P₀` already
  occurs in the bundle, in the estimates for the time derivatives, but only the
  upper bound on `P` was recorded there),

and the corresponding notion for a single curve,

* `IsGeomCurve P₀ P₁ κ̂ p` — the marked curve `p` is a constant-speed closed
  curve of perimeter in `[P₀, P₁]` and curvature bounded by `κ̂`, which
  `isGeomCurve_of_tubeMember` produces from membership in the tube together with
  an upper curvature bound.

The three closure properties are `isGeomNormalPath_const`,
`IsGeomNormalPath.reverse` and `IsGeomNormalPath.concat`; the last one is where
the geometry enters, since the two families of geometric data have to be
identified at the seam: the two perimeters agree because both compute the speed
of the common slice, the two tangent angles differ by a constant with
`e^{ic} = 1`, and therefore the two curvatures agree.

The resulting pseudodistance is `geomDist P₀ P₁ κ̂`, with

* `geomDist_self`, `geomDist_comm`, `geomDist_triangle` — the pseudometric
  axioms;
* `geomPathDist_le_geomDist` and `dist_le_c2Const_mul_geomDist` — it dominates
  the pseudodistance of `GeomPathDist` and, through it, the metric of the space
  of marked curves.
-/

noncomputable section

open Set Filter Topology MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace GeomPathMetric

variable {p q r : Data}

/-! ### Gluing derivatives -/

/-- Gluing two derivatives at a point where both velocities vanish; the
real-valued counterpart of `PathMetric.hasDerivAt_glue`. -/
theorem hasDerivAt_glue_real {f g vf vg : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, HasDerivAt f (vf t) t) (hg : ∀ t, HasDerivAt g (vg t) t)
    (hval : f a = g a) (hva : vf a = 0) (hvb : vg a = 0) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ a then f s else g s) (if t ≤ a then vf t else vg t) t := by
  rcases lt_trichotomy t a with h | h | h
  · have hmem : Iio a ∈ nhds t := Iio_mem_nhds h
    have heq : (fun s => if s ≤ a then f s else g s) =ᶠ[nhds t] f :=
      Filter.eventuallyEq_of_mem hmem (fun s hs => if_pos (le_of_lt hs))
    rw [if_pos h.le]
    exact (hf t).congr_of_eventuallyEq heq
  · subst h
    rw [if_pos le_rfl, hva]
    have h1 : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) 0 (Iic t) t := by
      refine HasDerivWithinAt.congr ?_ (fun s hs => if_pos hs) (if_pos le_rfl)
      simpa [hva] using (hf t).hasDerivWithinAt (s := Iic t)
    have h2 : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) 0 (Ici t) t := by
      refine HasDerivWithinAt.congr ?_ (fun s hs => ?_) (by rw [if_pos le_rfl, hval])
      · simpa [hvb] using (hg t).hasDerivWithinAt (s := Ici t)
      · rcases eq_or_lt_of_le (mem_Ici.1 hs) with rfl | hlt
        · rw [if_pos le_rfl, hval]
        · rw [if_neg (not_le.mpr hlt)]
    have := h1.union h2
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · have hmem : Ioi a ∈ nhds t := Ioi_mem_nhds h
    have heq : (fun s => if s ≤ a then f s else g s) =ᶠ[nhds t] g :=
      Filter.eventuallyEq_of_mem hmem (fun s hs => if_neg (not_le.mpr hs))
    rw [if_neg (not_le.mpr h)]
    exact (hg t).congr_of_eventuallyEq heq

/-! ### Geometric curves and geometric normal paths -/

/-- A **geometric marked curve**: a closed curve of constant speed `P ∈ [P₀,P₁]`
in the normalized parameter whose tangent angle `θ` turns at the rate `Pκ` with
`|κ| ≤ κ̂`. -/
def IsGeomCurve (P0 P1 khat : ℝ) (p : Data) : Prop :=
  ∃ P : ℝ, ∃ theta kappa : ℝ → ℝ,
    P0 ≤ P ∧ P ≤ P1 ∧ (∀ u, |kappa u| ≤ khat) ∧
    (∀ u, HasDerivAt (⇑p.1) ((P : ℂ) * Complex.exp (Complex.I * (theta u : ℂ))) u) ∧
    (∀ u, HasDerivAt theta (P * kappa u) u)

/-- A **geometric normal path**: the hypothesis bundle of
`NormalPathC2Increment.IsConstantSpeedNormalPath`, with the perimeter of the
slices bounded below by `P₀` as well as above by `P₁`. -/
def IsGeomNormalPath (P0 P1 khat : ℝ) {p q : Data} (Γ : NormalPath p q) : Prop :=
  ∃ P Pd : ℝ → ℝ, ∃ theta kappa etas kt : ℝ → ℝ → ℝ,
    (∀ t, P0 ≤ P t) ∧ (∀ t, P t ≤ P1) ∧ (∀ t u, |kappa t u| ≤ khat) ∧
    (∀ t u, HasDerivAt (Γ.X t) ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u) ∧
    (∀ t u, HasDerivAt (theta t) (P t * kappa t u) u) ∧
    (∀ t, HasDerivAt P (Pd t) t) ∧ Continuous Pd ∧
    (∀ t, |Pd t| ≤ khat * P1 * Γ.m t) ∧
    (∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t) ∧
    (∀ u, Continuous fun t => etas t u) ∧
    (∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t) ∧
    (∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t) ∧
    (∀ u, Continuous fun t => kt t u) ∧
    (∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t)

/-- A geometric normal path is in particular a constant-speed normal path, so
the increment bound applies to it. -/
theorem IsGeomNormalPath.isConstantSpeed {P0 P1 khat : ℝ} {Γ : NormalPath p q}
    (hP0 : 0 ≤ P0) (h : IsGeomNormalPath P0 P1 khat Γ) :
    IsConstantSpeedNormalPath P0 P1 khat Γ := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0', hP1, hka, hX, hth, hPd, hPdc, hPdb,
    htht, hetc, het, hkat, hktc, hkt⟩ := h
  exact ⟨P, Pd, theta, kappa, etas, kt, fun t => le_trans hP0 (hP0' t), hP1, hka, hX, hth,
    hPd, hPdc, hPdb, htht, hetc, het, hkat, hktc, hkt⟩

/-- Membership in the tube, together with an upper bound for the curvature and
two-sided bounds for the perimeter, makes a marked curve geometric. -/
theorem isGeomCurve_of_tubeMember {c kmin dlt P0 P1 khat : ℝ} (hc : 0 < c)
    (hp : IsTubeMember c kmin dlt p) (hP0 : P0 ≤ perim p) (hP1 : perim p ≤ P1)
    (hk : ∀ u, |((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im| ≤ khat * perim p ^ 3) :
    IsGeomCurve P0 P1 khat p := by
  set L : ℝ := perim p with hL
  have hLpos : 0 < L := perim_pos hc hp
  set tau : ℝ → ℂ := fun u => (L : ℂ)⁻¹ * p.2.1 u with htau
  set D : ℝ → ℂ := fun u => (L : ℂ)⁻¹ * p.2.2 u with hD
  have hLne : (L : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hLpos)
  have hnorm : ∀ u, ‖tau u‖ = 1 := by
    intro u
    rw [htau]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    rw [norm_vel_eq_perim hp u, ← hL]
    field_simp
  have hderiv : ∀ u, HasDerivAt tau (D u) u := by
    intro u
    exact ((hp.hasDerivAt_vel u).const_mul ((L : ℂ)⁻¹))
  have hcontD : Continuous D := by
    have : Continuous fun u => p.2.2 u := (map_continuous p.2.2)
    exact continuous_const.mul this
  obtain ⟨theta, hth, hexp⟩ := exists_angle hnorm hderiv hcontD
  refine ⟨L, theta, fun u => ((starRingEnd ℂ) (tau u) * D u).im / L, hP0, hP1, ?_, ?_, ?_⟩
  · intro u
    have hconj : (starRingEnd ℂ) ((L : ℂ)⁻¹) = (L : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    have hprod : (starRingEnd ℂ) (p.2.1 u) * p.2.2 u
        = ((L ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (tau u) * D u) := by
      simp only [htau, hD, map_mul, hconj]
      push_cast
      field_simp
    have hkey : ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im
        = L ^ 2 * ((starRingEnd ℂ) (tau u) * D u).im := by
      rw [hprod, Complex.im_ofReal_mul]
    show |((starRingEnd ℂ) (tau u) * D u).im / L| ≤ khat
    rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
    have hL2 : (0:ℝ) < L ^ 2 := by positivity
    have h1 := hk u
    rw [hkey, abs_mul, abs_of_pos hL2] at h1
    have h2 : L ^ 2 * |((starRingEnd ℂ) (tau u) * D u).im| ≤ L ^ 2 * (khat * L) := by
      rw [show L ^ 2 * (khat * L) = khat * L ^ 3 from by ring]
      exact h1
    exact le_of_mul_le_mul_left h2 hL2
  · intro u
    have h1 : HasDerivAt (⇑p.1) (p.2.1 u) u := hp.hasDerivAt_curve u
    have h2 : ((L : ℂ) * Complex.exp (Complex.I * (theta u : ℂ))) = p.2.1 u := by
      rw [hexp u, htau]
      field_simp
    rw [h2]
    exact h1
  · intro u
    have := hth u
    have hLne' : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    convert this using 1
    field_simp

/-! ### The constant path -/

/-- The constant path at a geometric curve is a geometric normal path. -/
theorem isGeomNormalPath_const {P0 P1 khat : ℝ} (h : IsGeomCurve P0 P1 khat p) :
    IsGeomNormalPath P0 P1 khat (NormalPath.const p) := by
  obtain ⟨P, theta, kappa, hP0, hP1, hka, hX, hth⟩ := h
  refine ⟨fun _ => P, fun _ => 0, fun _ u => theta u, fun _ u => kappa u, fun _ _ => 0,
    fun _ _ => 0, fun _ => hP0, fun _ => hP1, fun _ u => hka u, ?_, fun t u => hth u,
    fun t => hasDerivAt_const t P, continuous_const, ?_, fun t u => hasDerivAt_const t (theta u),
    fun u => continuous_const, ?_, fun t u => hasDerivAt_const t (kappa u),
    fun u => continuous_const, ?_⟩
  · intro t u
    exact hX u
  · intro t; simp [NormalPath.const]
  · intro t u; simp [NormalPath.const]
  · intro t u; simp [NormalPath.const]

/-! ### Reversal -/

/-- The reversal of a geometric normal path is a geometric normal path. -/
theorem IsGeomNormalPath.reverse {P0 P1 khat : ℝ} {Γ : NormalPath p q}
    (h : IsGeomNormalPath P0 P1 khat Γ) :
    IsGeomNormalPath P0 P1 khat (NormalPath.reverse Γ) := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hka, hX, hth, hPd, hPdc, hPdb,
    htht, hetc, het, hkat, hktc, hkt⟩ := h
  have hsub : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Γ.T - s) (-1) t := by
    intro t
    simpa using (hasDerivAt_id t).const_sub Γ.T
  have hcsub : Continuous fun t : ℝ => Γ.T - t := continuous_const.sub continuous_id
  refine ⟨fun t => P (Γ.T - t), fun t => -Pd (Γ.T - t), fun t u => theta (Γ.T - t) u,
    fun t u => kappa (Γ.T - t) u, fun t u => -etas (Γ.T - t) u, fun t u => -kt (Γ.T - t) u,
    fun t => hP0 _, fun t => hP1 _, fun t u => hka _ u, ?_, fun t u => hth _ u, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u; exact hX (Γ.T - t) u
  · intro t
    have := (hPd (Γ.T - t)).scomp t (hsub t)
    simpa using this
  · exact (hPdc.comp hcsub).neg
  · intro t; simpa using hPdb (Γ.T - t)
  · intro t u
    have := (htht (Γ.T - t) u).scomp t (hsub t)
    simpa using this
  · intro u; exact ((hetc u).comp hcsub).neg
  · intro t u; simpa using het (Γ.T - t) u
  · intro t u
    have := (hkat (Γ.T - t) u).scomp t (hsub t)
    simpa using this
  · intro u; exact ((hktc u).comp hcsub).neg
  · intro t u; simpa using hkt (Γ.T - t) u

/-! ### Concatenation -/

/-- The concatenation of two geometric normal paths is a geometric normal path.
The two families of geometric data are identified at the seam: the perimeters
agree because both compute the speed of the common slice, the tangent angles
differ by a constant `c` with `e^{ic} = 1`, and hence the curvatures agree. -/
theorem IsGeomNormalPath.concat {P0 P1 khat : ℝ} (hP0pos : 0 < P0)
    {Γ : NormalPath p q} {Δ : NormalPath q r}
    (hΓ : IsGeomNormalPath P0 P1 khat Γ) (hΔ : IsGeomNormalPath P0 P1 khat Δ) :
    IsGeomNormalPath P0 P1 khat (NormalPath.concat Γ Δ) := by
  obtain ⟨PA, PdA, thA, kaA, etA, ktA, hPA0, hPA1, hkaA, hXA, hthA, hPdA, hPdAc, hPdAb,
    hthtA, hetAc, hetA, hkatA, hktAc, hktA⟩ := hΓ
  obtain ⟨PB, PdB, thB, kaB, etB, ktB, hPB0, hPB1, hkaB, hXB, hthB, hPdB, hPdBc, hPdBb,
    hthtB, hetBc, hetB, hkatB, hktBc, hktB⟩ := hΔ
  -- the two cost densities vanish at the seam
  have hmA : Γ.m Γ.T = 0 := Γ.m_stop Γ.T (by simp)
  have hmB : Δ.m 0 = 0 := Δ.m_stop 0 (by simp)
  have hPdA0 : PdA Γ.T = 0 := by
    have h := hPdAb Γ.T
    rw [hmA, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hPdB0 : PdB 0 = 0 := by
    have h := hPdBb 0
    rw [hmB, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hetA0 : ∀ u, etA Γ.T u = 0 := by
    intro u
    have h := hetA Γ.T u
    rw [hmA, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hetB0 : ∀ u, etB 0 u = 0 := by
    intro u
    have h := hetB 0 u
    rw [hmB, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hktA0 : ∀ u, ktA Γ.T u = 0 := by
    intro u
    have h := hktA Γ.T u
    rw [hmA, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hktB0 : ∀ u, ktB 0 u = 0 := by
    intro u
    have h := hktB 0 u
    rw [hmB, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  -- the two slices at the seam are the same curve
  have hXT : Γ.X Γ.T = ⇑q.1 := funext Γ.finish
  have hX0 : Δ.X 0 = ⇑q.1 := funext Δ.start
  have hE : ∀ u, ((PA Γ.T : ℂ) * Complex.exp (Complex.I * (thA Γ.T u : ℂ)))
      = ((PB 0 : ℂ) * Complex.exp (Complex.I * (thB 0 u : ℂ))) := by
    intro u
    have h1 : HasDerivAt (⇑q.1) ((PA Γ.T : ℂ) * Complex.exp (Complex.I * (thA Γ.T u : ℂ))) u := by
      rw [← hXT]; exact hXA Γ.T u
    have h2 : HasDerivAt (⇑q.1) ((PB 0 : ℂ) * Complex.exp (Complex.I * (thB 0 u : ℂ))) u := by
      rw [← hX0]; exact hXB 0 u
    exact h1.unique h2
  have hnexp : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  have hPApos : 0 < PA Γ.T := lt_of_lt_of_le hP0pos (hPA0 Γ.T)
  have hPBpos : 0 < PB 0 := lt_of_lt_of_le hP0pos (hPB0 0)
  have hPeq : PA Γ.T = PB 0 := by
    have h := congrArg norm (hE 0)
    rw [norm_mul, norm_mul, hnexp, hnexp] at h
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPApos, abs_of_pos hPBpos] using h
  have hexpeq : ∀ u, Complex.exp (Complex.I * (thA Γ.T u : ℂ))
      = Complex.exp (Complex.I * (thB 0 u : ℂ)) := by
    intro u
    have h := hE u
    rw [hPeq] at h
    have hne : (PB 0 : ℂ) ≠ 0 := by
      simpa using ne_of_gt hPBpos
    exact mul_left_cancel₀ hne h
  -- the two tangent angles differ by a constant, and the two curvatures agree
  set d : ℝ → ℝ := fun u => thA Γ.T u - thB 0 u with hd
  have hdderiv : ∀ u, HasDerivAt d (PA Γ.T * kaA Γ.T u - PB 0 * kaB 0 u) u := fun u =>
    (hthA Γ.T u).sub (hthB 0 u)
  have hdconst : ∀ u, Complex.exp (Complex.I * (d u : ℂ)) = 1 := by
    intro u
    have h : Complex.exp (Complex.I * (d u : ℂ))
        = Complex.exp (Complex.I * (thA Γ.T u : ℂ)) / Complex.exp (Complex.I * (thB 0 u : ℂ)) := by
      rw [← Complex.exp_sub, hd]
      push_cast
      ring_nf
    rw [h, hexpeq u]
    exact div_self (Complex.exp_ne_zero _)
  have hdzero : ∀ u, PA Γ.T * kaA Γ.T u - PB 0 * kaB 0 u = 0 := by
    intro u
    have hfun : (fun u => Complex.exp (Complex.I * (d u : ℂ))) = fun _ : ℝ => (1 : ℂ) := by
      funext v; exact hdconst v
    have hderiv : HasDerivAt (fun u => Complex.exp (Complex.I * (d u : ℂ)))
        (Complex.exp (Complex.I * (d u : ℂ)) *
          (Complex.I * ((PA Γ.T * kaA Γ.T u - PB 0 * kaB 0 u : ℝ) : ℂ))) u :=
      (((hdderiv u).ofReal_comp).const_mul Complex.I).cexp
    rw [hfun] at hderiv
    have hzero : Complex.exp (Complex.I * (d u : ℂ)) *
        (Complex.I * ((PA Γ.T * kaA Γ.T u - PB 0 * kaB 0 u : ℝ) : ℂ)) = 0 :=
      hderiv.unique (hasDerivAt_const u (1 : ℂ))
    rw [hdconst u, one_mul] at hzero
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have := (mul_eq_zero.mp hzero).resolve_left hI
    exact_mod_cast this
  have hkaeq : ∀ u, kaA Γ.T u = kaB 0 u := by
    intro u
    have h := hdzero u
    rw [hPeq] at h
    have hne : PB 0 ≠ 0 := ne_of_gt hPBpos
    have h2 : PB 0 * kaA Γ.T u = PB 0 * kaB 0 u := by linarith
    exact mul_left_cancel₀ hne h2
  have hdderiv0 : ∀ u, HasDerivAt d 0 u := by
    intro u
    have := hdderiv u
    rwa [hdzero u] at this
  set c : ℝ := d 0 with hc
  have hdeq : ∀ u, d u = c := by
    intro u
    have hdiff : Differentiable ℝ d := fun x => (hdderiv0 x).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun x => (hdderiv0 x).deriv) u 0
  have hthAeq : ∀ u, thA Γ.T u = thB 0 u + c := by
    intro u
    have := hdeq u
    rw [hd] at this
    linarith [this]
  have hexpc : Complex.exp (Complex.I * (c : ℂ)) = 1 := by
    rw [hc]; exact hdconst 0
  have hshift : ∀ x : ℝ, Complex.exp (Complex.I * ((x + c : ℝ) : ℂ))
      = Complex.exp (Complex.I * (x : ℂ)) := by
    intro x
    push_cast
    rw [mul_add, Complex.exp_add, hexpc, mul_one]
  -- the glued data
  refine ⟨fun t => if t ≤ Γ.T then PA t else PB (t - Γ.T),
    fun t => if t ≤ Γ.T then PdA t else PdB (t - Γ.T),
    fun t u => if t ≤ Γ.T then thA t u else thB (t - Γ.T) u + c,
    fun t u => if t ≤ Γ.T then kaA t u else kaB (t - Γ.T) u,
    fun t u => if t ≤ Γ.T then etA t u else etB (t - Γ.T) u,
    fun t u => if t ≤ Γ.T then ktA t u else ktB (t - Γ.T) u,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; dsimp only; split_ifs with h; exacts [hPA0 t, hPB0 _]
  · intro t; dsimp only; split_ifs with h; exacts [hPA1 t, hPB1 _]
  · intro t u; dsimp only; split_ifs with h; exacts [hkaA t u, hkaB _ u]
  · intro t u
    by_cases h : t ≤ Γ.T
    · simp only [if_pos h]
      have hfun : (NormalPath.concat Γ Δ).X t = Γ.X t := by
        funext v
        show (if t ≤ Γ.T then Γ.X t v else Δ.X (t - Γ.T) v) = Γ.X t v
        rw [if_pos h]
      rw [hfun]
      exact hXA t u
    · simp only [if_neg h]
      have hfun : (NormalPath.concat Γ Δ).X t = Δ.X (t - Γ.T) := by
        funext v
        show (if t ≤ Γ.T then Γ.X t v else Δ.X (t - Γ.T) v) = Δ.X (t - Γ.T) v
        rw [if_neg h]
      rw [hfun, hshift]
      exact hXB (t - Γ.T) u
  · intro t u
    by_cases h : t ≤ Γ.T
    · simp only [if_pos h]
      exact hthA t u
    · simp only [if_neg h]
      exact (hthB (t - Γ.T) u).add_const c
  · intro t
    have h := hasDerivAt_glue_real (f := PA) (g := fun s => PB (s - Γ.T))
      (vf := PdA) (vg := fun s => PdB (s - Γ.T)) (a := Γ.T) hPdA
      (fun s => by simpa using (hPdB (s - Γ.T)).comp s ((hasDerivAt_id s).sub_const Γ.T))
      (by simpa using hPeq) hPdA0 (by simpa using hPdB0) t
    exact h
  · refine Continuous.if_le hPdAc (hPdBc.comp (continuous_id.sub continuous_const))
      continuous_id continuous_const (fun x hx => ?_)
    subst hx
    simp [hPdA0, hPdB0]
  · intro t
    show |if t ≤ Γ.T then PdA t else PdB (t - Γ.T)| ≤
      khat * P1 * (if t ≤ Γ.T then Γ.m t else Δ.m (t - Γ.T))
    split_ifs with h
    · exact hPdAb t
    · exact hPdBb _
  · intro t u
    have h := hasDerivAt_glue_real (f := fun s => thA s u) (g := fun s => thB (s - Γ.T) u + c)
      (vf := fun s => etA s u) (vg := fun s => etB (s - Γ.T) u) (a := Γ.T)
      (fun s => hthtA s u)
      (fun s => by
        simpa using ((hthtB (s - Γ.T) u).comp s ((hasDerivAt_id s).sub_const Γ.T)).add_const c)
      (by simpa using hthAeq u) (hetA0 u) (by simpa using hetB0 u) t
    exact h
  · intro u
    refine Continuous.if_le (hetAc u)
      (((hetBc u).comp (continuous_id.sub continuous_const))) continuous_id continuous_const
      (fun x hx => ?_)
    subst hx
    simp [hetA0 u, hetB0 u]
  · intro t u
    show |if t ≤ Γ.T then etA t u else etB (t - Γ.T) u| ≤
      1 / P0 * (if t ≤ Γ.T then Γ.m t else Δ.m (t - Γ.T))
    split_ifs with h
    · exact hetA t u
    · exact hetB _ u
  · intro t u
    have h := hasDerivAt_glue_real (f := fun s => kaA s u) (g := fun s => kaB (s - Γ.T) u)
      (vf := fun s => ktA s u) (vg := fun s => ktB (s - Γ.T) u) (a := Γ.T)
      (fun s => hkatA s u)
      (fun s => by
        simpa using (hkatB (s - Γ.T) u).comp s ((hasDerivAt_id s).sub_const Γ.T))
      (by simpa using hkaeq u) (hktA0 u) (by simpa using hktB0 u) t
    exact h
  · intro u
    refine Continuous.if_le (hktAc u)
      (((hktBc u).comp (continuous_id.sub continuous_const))) continuous_id continuous_const
      (fun x hx => ?_)
    subst hx
    simp [hktA0 u, hktB0 u]
  · intro t u
    show |if t ≤ Γ.T then ktA t u else ktB (t - Γ.T) u| ≤
      (1 / P0 ^ 2 + khat ^ 2) * (if t ≤ Γ.T then Γ.m t else Δ.m (t - Γ.T))
    split_ifs with h
    · exact hktA t u
    · exact hktB _ u

/-! ### The ends of a geometric normal path -/

/-- The initial curve of a geometric normal path is a geometric curve. -/
theorem IsGeomNormalPath.isGeomCurve_start {P0 P1 khat : ℝ} {Γ : NormalPath p q}
    (h : IsGeomNormalPath P0 P1 khat Γ) : IsGeomCurve P0 P1 khat p := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hka, hX, hth, -⟩ := h
  refine ⟨P 0, theta 0, kappa 0, hP0 0, hP1 0, fun u => hka 0 u, ?_, fun u => hth 0 u⟩
  intro u
  have hfun : ⇑p.1 = Γ.X 0 := (funext Γ.start).symm
  rw [hfun]
  exact hX 0 u

/-- The terminal curve of a geometric normal path is a geometric curve. -/
theorem IsGeomNormalPath.isGeomCurve_finish {P0 P1 khat : ℝ} {Γ : NormalPath p q}
    (h : IsGeomNormalPath P0 P1 khat Γ) : IsGeomCurve P0 P1 khat q := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hP0, hP1, hka, hX, hth, -⟩ := h
  refine ⟨P Γ.T, theta Γ.T, kappa Γ.T, hP0 Γ.T, hP1 Γ.T, fun u => hka Γ.T u, ?_,
    fun u => hth Γ.T u⟩
  intro u
  have hfun : ⇑q.1 = Γ.X Γ.T := (funext Γ.finish).symm
  rw [hfun]
  exact hX Γ.T u

/-! ### The pseudodistance -/

/-- The set of costs of the *geometric* normal paths from `p` to `q`. -/
def geomSet (P0 P1 khat : ℝ) (p q : Data) : Set ℝ :=
  {x | ∃ Γ : NormalPath p q, IsGeomNormalPath P0 P1 khat Γ ∧ cost Γ = x}

theorem bddBelow_geomSet (P0 P1 khat : ℝ) (p q : Data) : BddBelow (geomSet P0 P1 khat p q) := by
  refine ⟨0, ?_⟩
  rintro x ⟨Γ, -, rfl⟩
  exact Γ.cost_nonneg

/-- **The geometric path pseudodistance**, for the two-sided perimeter bounds. -/
def geomDist (P0 P1 khat : ℝ) (p q : Data) : ℝ := sInf (geomSet P0 P1 khat p q)

theorem geomDist_nonneg (P0 P1 khat : ℝ) (p q : Data) : 0 ≤ geomDist P0 P1 khat p q := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨Γ, -, rfl⟩
  exact Γ.cost_nonneg

theorem geomDist_le_cost {P0 P1 khat : ℝ} (Γ : NormalPath p q)
    (hΓ : IsGeomNormalPath P0 P1 khat Γ) : geomDist P0 P1 khat p q ≤ cost Γ :=
  csInf_le (bddBelow_geomSet P0 P1 khat p q) ⟨Γ, hΓ, rfl⟩

theorem geomSet_subset_geomCostSet {P0 P1 khat : ℝ} (hP0 : 0 ≤ P0) (p q : Data) :
    geomSet P0 P1 khat p q ⊆ GeomPathDist.geomCostSet P0 P1 khat p q := by
  rintro x ⟨Γ, hΓ, rfl⟩
  exact ⟨Γ, hΓ.isConstantSpeed hP0, rfl⟩

/-- The pseudodistance of this file dominates the one of `GeomPathDist`, the
infimum being taken over fewer paths. -/
theorem geomPathDist_le_geomDist {P0 P1 khat : ℝ} (hP0 : 0 ≤ P0)
    (hne : (geomSet P0 P1 khat p q).Nonempty) :
    GeomPathDist.geomPathDist P0 P1 khat p q ≤ geomDist P0 P1 khat p q :=
  csInf_le_csInf (GeomPathDist.bddBelow_geomCostSet P0 P1 khat p q) hne
    (geomSet_subset_geomCostSet hP0 p q)

/-- **The geometric path pseudodistance dominates the metric of the space of
marked curves.** -/
theorem dist_le_c2Const_mul_geomDist {c kmin dlt cq kminq dltq P0 P1 khat : ℝ} (hP0 : 0 ≤ P0)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hne : (geomSet P0 P1 khat p q).Nonempty) :
    dist p q ≤ c2Const P0 P1 khat * geomDist P0 P1 khat p q := by
  have hc2 : (0:ℝ) < c2Const P0 P1 khat := lt_of_lt_of_le one_pos (one_le_c2Const P0 P1 khat)
  have hne' : (GeomPathDist.geomCostSet P0 P1 khat p q).Nonempty :=
    hne.mono (geomSet_subset_geomCostSet hP0 p q)
  refine le_trans (GeomPathDist.dist_le_c2Const_mul_geomPathDist hp hq hne') ?_
  exact mul_le_mul_of_nonneg_left (geomPathDist_le_geomDist hP0 hne) hc2.le

/-! ### The pseudometric axioms -/

/-- A geometric curve is at geometric distance zero from itself. -/
theorem geomDist_self {P0 P1 khat : ℝ} (h : IsGeomCurve P0 P1 khat p) :
    geomDist P0 P1 khat p p = 0 :=
  le_antisymm
    (by simpa using geomDist_le_cost (NormalPath.const p) (isGeomNormalPath_const h))
    (geomDist_nonneg P0 P1 khat p p)

/-- Any curve joined to another by a geometric normal path is at geometric
distance zero from itself. -/
theorem geomDist_self_of_nonempty {P0 P1 khat : ℝ} (hne : (geomSet P0 P1 khat p q).Nonempty) :
    geomDist P0 P1 khat p p = 0 := by
  obtain ⟨x, Γ, hΓ, -⟩ := hne
  exact geomDist_self hΓ.isGeomCurve_start

theorem geomSet_comm (P0 P1 khat : ℝ) (p q : Data) :
    geomSet P0 P1 khat p q = geomSet P0 P1 khat q p := by
  have key : ∀ a b : Data, geomSet P0 P1 khat a b ⊆ geomSet P0 P1 khat b a := by
    rintro a b x ⟨Γ, hΓ, rfl⟩
    exact ⟨NormalPath.reverse Γ, hΓ.reverse, cost_reverse Γ⟩
  exact Subset.antisymm (key p q) (key q p)

theorem geomDist_comm (P0 P1 khat : ℝ) (p q : Data) :
    geomDist P0 P1 khat p q = geomDist P0 P1 khat q p := by
  rw [geomDist, geomDist, geomSet_comm]

/-- **The triangle inequality** for the geometric path pseudodistance. -/
theorem geomDist_triangle {P0 P1 khat : ℝ} (hP0 : 0 < P0) {p q r : Data}
    (hpq : (geomSet P0 P1 khat p q).Nonempty) (hqr : (geomSet P0 P1 khat q r).Nonempty) :
    geomDist P0 P1 khat p r ≤ geomDist P0 P1 khat p q + geomDist P0 P1 khat q r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, hx, hxlt⟩ := Real.lt_sInf_add_pos hpq (half_pos hε)
  obtain ⟨y, hy, hylt⟩ := Real.lt_sInf_add_pos hqr (half_pos hε)
  obtain ⟨Γ, hΓ, rfl⟩ := hx
  obtain ⟨Δ, hΔ, rfl⟩ := hy
  have hle : geomDist P0 P1 khat p r ≤ cost Γ + cost Δ := by
    have := geomDist_le_cost (NormalPath.concat Γ Δ) (hΓ.concat hP0 hΔ)
    rwa [cost_concat] at this
  have : cost Γ + cost Δ
      < (geomDist P0 P1 khat p q + geomDist P0 P1 khat q r) + ε := by
    have h1 : cost Γ < geomDist P0 P1 khat p q + ε / 2 := hxlt
    have h2 : cost Δ < geomDist P0 P1 khat q r + ε / 2 := hylt
    linarith
  linarith

end GeomPathMetric
