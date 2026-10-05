module

public import UnitTangentIterates.ShadowRegularity

/-!
# Continuity of the selected inverse

The selected inverse `(L, f) ↦ (rearL L f, rearF L f)` is continuous on admissible normalized
ovals, for convergence of `L` and uniform convergence of `f`; we get convergence of `rearL` and
pointwise convergence of `rearF` (`Ovals.rear_tendsto`).  The proof is quantitative: the
periodic steering angles depend Lipschitz-continuously on the data (maximum principle,
`Ovals.weightedSteering_diff_le`), and so do the normalized rear arclengths and their inverses.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- A function with derivative at least `c > 0` expands distances by at least `c`. -/
lemma abs_sub_le_of_deriv_ge {N N' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hN : ∀ u, HasDerivAt N (N' u) u) (hN' : ∀ u, c ≤ N' u) (u v : ℝ) :
    |u - v| ≤ |N u - N v| / c := by
  have hd : ∀ s, HasDerivAt (fun s => N s - c * s) (N' s - c) s := fun s => by
    simpa using (hN s).sub ((hasDerivAt_id s).const_mul c)
  have hmono : Monotone fun s => N s - c * s :=
    monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s => by
      rw [(hd s).deriv]; linarith [hN' s]
  rw [le_div_iff₀ hc]
  rcases le_total u v with h | h
  · have := hmono h; simp only at this
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]; nlinarith
  · have := hmono h; simp only at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]; nlinarith

/-- Linear bounds give convergence. -/
lemma tendsto_of_lin_bound {ι : Type*} {F : Filter ι} {a : ι → ℝ} {b C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε > 0, ε ≤ ε₀ → ∀ᶠ j in F, |a j - b| ≤ C * ε) : Tendsto a F (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hC : 0 < |C| + 1 := by positivity
  set ε := min ε₀ (e / (2 * (|C| + 1)))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  filter_upwards [h ε hε (min_le_left _ _)] with j hj
  rw [Real.dist_eq]
  calc |a j - b| ≤ C * ε := hj
    _ ≤ |C| * ε := by gcongr; exact le_abs_self C
    _ ≤ (|C| + 1) * (e / (2 * (|C| + 1))) := by
        gcongr
        · linarith
        · exact min_le_right _ _
    _ = e / 2 := by field_simp
    _ < e := by linarith

section

variable {κ L L' : ℝ} {f f' : ℝ → ℝ}

lemma AdmOval.abs_le_one (hA : AdmOval κ L f) (hκ1 : κ < 1) (σ : ℝ) : |f σ| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [(hA.2.2.2.1 σ).1, (hA.2.2.2.1 σ).2]

lemma cos_arcsin_pos' (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) : 0 < Real.cos (Real.arcsin κ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.arcsin_nonneg.2 hκ0, Real.pi_pos],
    arcsin_lt_pi_div_two hκ1⟩

/-- **Lipschitz dependence of the steering angle.** -/
lemma rδ_diff_le (hA : AdmOval κ L f) (hA' : AdmOval κ L' f') (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {ε : ℝ} (hεL : ε ≤ L / 2) (hL : |L' - L| ≤ ε) (hf : ∀ σ, |f' σ - f σ| ≤ ε) (σ : ℝ) :
    |rδ L' f' σ - rδ L f σ| ≤ 2 * (2 + L) / (L * Real.cos (Real.arcsin κ)) * ε := by
  obtain ⟨h1p, h1d, h1b⟩ := rδ_spec hA' hκ0 hκ1
  obtain ⟨h2p, h2d, h2b⟩ := rδ_spec hA hκ0 hκ1
  have hL0 := hA.1
  have hL' : L / 2 ≤ L' := by linarith [(abs_le.1 hL).1]
  have hcA := cos_arcsin_pos' hκ0 hκ1
  have := weightedSteering_diff_le (p := 1) (A := Real.arcsin κ) (m := L / 2)
    (a₁ := fun σ => L' * f' σ) (a₂ := fun σ => L * f σ) (b₁ := fun _ => L') (b₂ := fun _ => L)
    (α := (1 + L) * ε) (β := ε) one_pos (arcsin_lt_pi_div_two hκ1) (by positivity) h1d h2d
    h1p h2p h1b h2b (fun _ => hL') (fun _ => by linarith) (fun u => ?_) (fun _ => hL) σ
  · calc |rδ L' f' σ - rδ L f σ| ≤ ((1 + L) * ε + ε) / (L / 2 * Real.cos (Real.arcsin κ)) :=
          this
      _ = 2 * (2 + L) / (L * Real.cos (Real.arcsin κ)) * ε := by field_simp; ring
  · show |L' * f' u - L * f u| ≤ (1 + L) * ε
    rw [show L' * f' u - L * f u = (L' - L) * f' u + L * (f' u - f u) by ring]
    have h1 := hA'.abs_le_one hκ1 u
    calc |(L' - L) * f' u + L * (f' u - f u)| ≤ |L' - L| * |f' u| + L * |f' u - f u| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hL0]
      _ ≤ ε * 1 + L * ε := add_le_add (mul_le_mul hL h1 (abs_nonneg _)
          ((abs_nonneg _).trans hL)) (mul_le_mul_of_nonneg_left (hf u) hL0.le)
      _ = (1 + L) * ε := by ring

/-- **Lipschitz dependence of the rear half-perimeter.** -/
lemma rearL_diff_le (hA : AdmOval κ L f) (hA' : AdmOval κ L' f') (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {ε : ℝ} (hεL : ε ≤ L / 2) (hL : |L' - L| ≤ ε) (hf : ∀ σ, |f' σ - f σ| ≤ ε) :
    (∀ σ, |L' * Real.cos (rδ L' f' σ) - L * Real.cos (rδ L f σ)| ≤
      (1 + L * (2 * (2 + L) / (L * Real.cos (Real.arcsin κ)))) * ε) ∧
    |rearL L' f' - rearL L f| ≤ (1 + L * (2 * (2 + L) / (L * Real.cos (Real.arcsin κ)))) * ε := by
  have hpt : ∀ σ, |L' * Real.cos (rδ L' f' σ) - L * Real.cos (rδ L f σ)| ≤
      (1 + L * (2 * (2 + L) / (L * Real.cos (Real.arcsin κ)))) * ε := fun σ => by
    rw [show L' * Real.cos (rδ L' f' σ) - L * Real.cos (rδ L f σ) =
      (L' - L) * Real.cos (rδ L' f' σ) + L * (Real.cos (rδ L' f' σ) - Real.cos (rδ L f σ))
      by ring]
    have h1 := Real.abs_cos_le_one (rδ L' f' σ)
    have h2 := (Real.abs_cos_sub_cos_le (rδ L' f' σ) (rδ L f σ)).trans
      (rδ_diff_le hA hA' hκ0 hκ1 hεL hL hf σ)
    calc _ ≤ |L' - L| * |Real.cos (rδ L' f' σ)| +
          L * |Real.cos (rδ L' f' σ) - Real.cos (rδ L f σ)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hA.1]
      _ ≤ ε * 1 + L * (2 * (2 + L) / (L * Real.cos (Real.arcsin κ)) * ε) :=
          add_le_add (mul_le_mul hL h1 (abs_nonneg _) ((abs_nonneg _).trans hL))
            (mul_le_mul_of_nonneg_left h2 hA.1.le)
      _ = _ := by ring
  refine ⟨hpt, ?_⟩
  obtain ⟨-, h1d, -⟩ := rδ_spec hA' hκ0 hκ1
  obtain ⟨-, h2d, -⟩ := rδ_spec hA hκ0 hκ1
  have hc1 : Continuous (rδ L' f') := continuous_iff_continuousAt.2 fun σ => (h1d σ).continuousAt
  have hc2 : Continuous (rδ L f) := continuous_iff_continuousAt.2 fun σ => (h2d σ).continuousAt
  unfold rearL
  rw [← intervalIntegral.integral_sub (f := fun σ => L' * Real.cos (rδ L' f' σ))
    (g := fun σ => L * Real.cos (rδ L f σ))
    ((continuous_const.mul (Real.continuous_cos.comp hc1)).intervalIntegrable _ _)
    ((continuous_const.mul (Real.continuous_cos.comp hc2)).intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun σ => L' * Real.cos (rδ L' f' σ) - L * Real.cos (rδ L f σ))
    (fun σ _ => by rw [Real.norm_eq_abs]; exact hpt σ)
  simpa using this

/-- Facts about the normalized rear arclength. -/
lemma normArc_rear_facts (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    let g := fun σ => L * Real.cos (rδ L f σ)
    (∀ u, HasDerivAt (normArc 1 g) (g u / rearL L f) u) ∧
      (∀ u, Real.cos (Real.arcsin κ) ≤ g u / rearL L f) ∧ normArc 1 g 0 = 0 ∧
      (∀ u, rearF L f (normArc 1 g u) = Real.tan (rδ L f u)) ∧ Continuous g ∧
      (∀ u, |g u| ≤ L) ∧ (∀ u v, |rδ L f u - rδ L f v| ≤ L * |u - v|) := by
  intro g
  obtain ⟨hδp, hδd, hδb⟩ := rδ_spec hA hκ0 hκ1
  obtain ⟨hRL, hRle, -⟩ := rear_facts hA hκ0 hκ1
  have hL := hA.1
  have hcA := cos_arcsin_pos' hκ0 hκ1
  have hA2 := arcsin_lt_pi_div_two hκ1
  have hδc : Continuous (rδ L f) := continuous_iff_continuousAt.2 fun σ => (hδd σ).continuousAt
  have hcos : ∀ s, Real.cos (Real.arcsin κ) ≤ Real.cos (rδ L f s) := fun s =>
    Real.cos_le_cos_of_nonneg_of_le_pi (hδb s).1 (by linarith [Real.pi_pos]) (hδb s).2
  have hcpos : ∀ s, 0 < Real.cos (rδ L f s) := fun s => hcA.trans_le (hcos s)
  have hgc : Continuous g := continuous_const.mul (Real.continuous_cos.comp hδc)
  refine ⟨fun u => hasDerivAt_normArc hgc u, fun u => ?_, by simp [normArc], fun u => ?_, hgc,
    fun u => ?_, fun u v => ?_⟩
  · rw [le_div_iff₀ hRL]
    calc Real.cos (Real.arcsin κ) * rearL L f ≤ Real.cos (Real.arcsin κ) * L := by gcongr
      _ ≤ g u := by simp only [g]; rw [mul_comm]; gcongr; exact hcos u
  · have := invFun_normArc one_pos (g := fun σ => L * Real.cos (rδ L f σ)) hgc
      (fun σ => mul_pos hL (hcpos σ)) u
    simp only [rearF, normF, g, this]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hL.ne']
  · simp only [g]
    rw [abs_mul, abs_of_pos hL]
    exact mul_le_of_le_one_right hL.le (Real.abs_cos_le_one _)
  · have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := rδ L f) (C := L)
      (fun x _ => (hδd x).hasDerivWithinAt) (fun r _ => ?_) (Set.mem_univ v) (Set.mem_univ u)
    · simpa [Real.norm_eq_abs] using this
    · have h1 := hA.2.2.2.1 r
      have h2 : 0 ≤ Real.sin (rδ L f r) := Real.sin_nonneg_of_nonneg_of_le_pi (hδb r).1
        (by linarith [(hδb r).2, Real.pi_pos])
      have h3 := Real.sin_le_one (rδ L f r)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [h1.1, h1.2]

/-- **Lipschitz dependence of the rear curvature at a point.** -/
lemma rearF_diff_le (hA : AdmOval κ L f) (hκ0 : 0 < κ) (hκ1 : κ < 1) (y : ℝ) :
    ∃ C, ∀ (L' : ℝ) (f' : ℝ → ℝ) (ε : ℝ), AdmOval κ L' f' → 0 ≤ ε → ε ≤ L / 2 →
      |L' - L| ≤ ε → (∀ σ, |f' σ - f σ| ≤ ε) → |rearF L' f' y - rearF L f y| ≤ C * ε := by
  set c := Real.cos (Real.arcsin κ)
  have hcA : 0 < c := cos_arcsin_pos' hκ0.le hκ1
  have hA2 := arcsin_lt_pi_div_two hκ1
  set ρ := π / Real.tan (Real.arcsin κ)
  have hρ : 0 < ρ := div_pos Real.pi_pos (PathData.tan_arcsin_pos hκ0 hκ1)
  have hL := hA.1
  set C1 := 2 * (2 + L) / (L * c)
  set C2 := 1 + L * C1
  set K := |y| / c * (1 / ρ + 3 * L / 2 / ρ ^ 2)
  refine ⟨(C1 + L * (C2 * K / c)) / c ^ 2, fun L' f' ε hA' hε0 hεL hLε hfε => ?_⟩
  have hC1 : 0 ≤ C1 := by positivity
  have hK : 0 ≤ K := by positivity
  obtain ⟨hNd, hNc, hN0, hNF, hgc, hgL, hδL⟩ := normArc_rear_facts hA hκ0.le hκ1
  obtain ⟨hNd', hNc', hN0', hNF', hgc', hgL', -⟩ := normArc_rear_facts hA' hκ0.le hκ1
  obtain ⟨hRL, -, hRρ, -⟩ := rear_facts hA hκ0.le hκ1
  obtain ⟨hRL', hRle', hRρ', -⟩ := rear_facts hA' hκ0.le hκ1
  obtain ⟨-, -, hδb⟩ := rδ_spec hA hκ0.le hκ1
  obtain ⟨-, -, hδb'⟩ := rδ_spec hA' hκ0.le hκ1
  have hL' : L' ≤ 3 * L / 2 := by linarith [(abs_le.1 hLε).2]
  set g := fun σ => L * Real.cos (rδ L f σ)
  set g' := fun σ => L' * Real.cos (rδ L' f' σ)
  obtain ⟨hgg, hRR⟩ := rearL_diff_le hA hA' hκ0.le hκ1 hεL hLε hfε
  -- preimages of `y`
  obtain ⟨G, hG, -, -⟩ := exists_inverse_of_deriv_ge hcA hNd hNc
  obtain ⟨G', hG', -, -⟩ := exists_inverse_of_deriv_ge hcA hNd' hNc'
  set u := G y
  set u' := G' y
  have hu' : |u'| ≤ |y| / c := by
    have := abs_sub_le_of_deriv_ge hcA hNd' hNc' u' 0
    rwa [sub_zero, hG', hN0', sub_zero] at this
  -- comparison of the normalized arclengths at `u'`
  set I := ∫ t in (0 : ℝ)..u', g t
  set I' := ∫ t in (0 : ℝ)..u', g' t
  have e1 : |I - I'| ≤ C2 * ε * |u'| := by
    simp only [I, I']
    rw [← intervalIntegral.integral_sub (hgc.intervalIntegrable _ _)
      (hgc'.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u')
      (f := fun t => g t - g' t) (C := C2 * ε) (fun t _ => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hgg t)
    simpa using this
  have e2 : |I'| ≤ 3 * L / 2 * |u'| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u')
      (f := g') (C := 3 * L / 2) (fun t _ => by
        rw [Real.norm_eq_abs]; exact (hgL' t).trans hL')
    simpa using this
  have hRρ1 : ρ ≤ rearL L f := hRρ
  have hRρ2 : ρ ≤ rearL L' f' := hRρ'
  have e3 : |normArc 1 g u' - normArc 1 g' u'| ≤ C2 * ε * K := by
    have hsplit : normArc 1 g u' - normArc 1 g' u' =
        (I - I') / rearL L f + I' * (rearL L' f' - rearL L f) / (rearL L f * rearL L' f') := by
      simp only [normArc, I, I', g, g']
      rw [show (∫ v in (0 : ℝ)..1, L * Real.cos (rδ L f v)) = rearL L f from rfl,
        show (∫ v in (0 : ℝ)..1, L' * Real.cos (rδ L' f' v)) = rearL L' f' from rfl]
      field_simp
      ring
    rw [hsplit]
    calc |(I - I') / rearL L f + I' * (rearL L' f' - rearL L f) / (rearL L f * rearL L' f')|
        ≤ |I - I'| / rearL L f + |I'| * |rearL L' f' - rearL L f| /
            (rearL L f * rearL L' f') := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_div, abs_mul, abs_of_pos hRL, abs_of_pos (mul_pos hRL hRL')]
      _ ≤ C2 * ε * |u'| / ρ + 3 * L / 2 * |u'| * (C2 * ε) / (ρ * ρ) := by
          gcongr
      _ ≤ C2 * ε * (|y| / c) / ρ + 3 * L / 2 * (|y| / c) * (C2 * ε) / (ρ * ρ) := by
          gcongr
      _ = C2 * ε * K := by simp only [K]; field_simp
  have e4 : |u - u'| ≤ C2 * ε * K / c := by
    have := abs_sub_le_of_deriv_ge hcA hNd hNc u u'
    rw [hG] at this
    calc |u - u'| ≤ |y - normArc 1 g u'| / c := this
      _ = |normArc 1 g' u' - normArc 1 g u'| / c := by rw [hG']
      _ ≤ C2 * ε * K / c := by rw [abs_sub_comm]; gcongr
  -- the curvatures
  have hy : rearF L f y = Real.tan (rδ L f u) := by rw [← hNF u, hG]
  have hy' : rearF L' f' y = Real.tan (rδ L' f' u') := by rw [← hNF' u', hG']
  rw [hy, hy']
  have e5 : |rδ L' f' u' - rδ L f u| ≤ (C1 + L * (C2 * K / c)) * ε := by
    have h1 := rδ_diff_le hA hA' hκ0.le hκ1 hεL hLε hfε u'
    have h2 := hδL u' u
    rw [abs_sub_comm u' u] at h2
    calc |rδ L' f' u' - rδ L f u| ≤ |rδ L' f' u' - rδ L f u'| + |rδ L f u' - rδ L f u| := by
          rw [show rδ L' f' u' - rδ L f u = (rδ L' f' u' - rδ L f u') + (rδ L f u' - rδ L f u)
            by ring]
          exact abs_add_le _ _
      _ ≤ C1 * ε + L * (C2 * ε * K / c) :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left e4 hL.le))
      _ = (C1 + L * (C2 * K / c)) * ε := by ring
  calc |Real.tan (rδ L' f' u') - Real.tan (rδ L f u)|
      ≤ |rδ L' f' u' - rδ L f u| / c ^ 2 := abs_tan_sub_le hA2 (hδb' u') (hδb u)
    _ ≤ (C1 + L * (C2 * K / c)) * ε / c ^ 2 := by gcongr
    _ = (C1 + L * (C2 * K / c)) / c ^ 2 * ε := by ring

/-- **Continuity of the selected inverse.**  If admissible `(L_j, f_j)` converge to an
admissible `(L, f)` (with `f_j → f` uniformly), then `rearL L_j f_j → rearL L f` and
`rearF L_j f_j → rearF L f` pointwise. -/
theorem rear_tendsto {ι : Type*} {F : Filter ι} {Lj : ι → ℝ} {fj : ι → ℝ → ℝ}
    (hA : AdmOval κ L f) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hAj : ∀ᶠ j in F, AdmOval κ (Lj j) (fj j)) (hL : Tendsto Lj F (𝓝 L))
    (hf : ∀ ε > 0, ∀ᶠ j in F, ∀ σ, |fj j σ - f σ| ≤ ε) :
    Tendsto (fun j => rearL (Lj j) (fj j)) F (𝓝 (rearL L f)) ∧
      ∀ y, Tendsto (fun j => rearF (Lj j) (fj j) y) F (𝓝 (rearF L f y)) := by
  have hclose : ∀ ε > 0, ∀ᶠ j in F, AdmOval κ (Lj j) (fj j) ∧ |Lj j - L| ≤ ε ∧
      ∀ σ, |fj j σ - f σ| ≤ ε := fun ε hε => by
    have h1 := (Metric.tendsto_nhds.1 hL) ε hε
    filter_upwards [hAj, h1, hf ε hε] with j h1 h2 h3
    exact ⟨h1, by rw [← Real.dist_eq]; exact h2.le, h3⟩
  have hL2 : 0 < L / 2 := by linarith [hA.1]
  refine ⟨tendsto_of_lin_bound (C := 1 + L * (2 * (2 + L) / (L * Real.cos (Real.arcsin κ))))
    hL2 fun ε hε hεL => ?_, fun y => ?_⟩
  · filter_upwards [hclose ε hε] with j ⟨h1, h2, h3⟩
    exact (rearL_diff_le hA h1 hκ0.le hκ1 hεL h2 h3).2
  · obtain ⟨C, hC⟩ := rearF_diff_le hA hκ0 hκ1 y
    refine tendsto_of_lin_bound (C := C) hL2 fun ε hε hεL => ?_
    filter_upwards [hclose ε hε] with j ⟨h1, h2, h3⟩
    exact hC _ _ ε h1 hε.le hεL h2 h3

end

end Ovals

end
