module

public import UnitTangentIterates.ShadowNodes

/-!
# The limiting orbit of normalized ovals

Along a nonprincipal ultrafilter `U` on `ℕ`, the backward iterates `node N n = 𝓑^{N-n} A_N`
converge (as `N → U`) to normalized ovals `X n = (LX n, fX n)`: the half-perimeters converge since
they stay in a compact interval, the curvatures converge pointwise since they are bounded, and
uniformly since they are equi-Lipschitz.  By continuity of the selected inverse, `X n = 𝓑 X_{n+1}`
(`Ovals.limit_orbit_data`).  Widths pass to the limit.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- The limiting half-perimeters. -/
noncomputable def LX (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) (n : ℕ) : ℝ :=
  limUnder (Filter.hyperfilter ℕ : Filter ℕ) fun N => (node L KA x₀ N n).1

/-- The limiting normalized curvatures. -/
noncomputable def fX (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  limUnder (Filter.hyperfilter ℕ : Filter ℕ) fun N => (node L KA x₀ N n).2 σ

lemma eventually_gt_hyper (m : ℕ) : ∀ᶠ N in (Filter.hyperfilter ℕ : Filter ℕ), m < N :=
  Filter.Eventually.filter_mono (Filter.hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop)
    (Filter.eventually_gt_atTop m)

lemma coord_continuous : Continuous fun p : ℂ × ℂ => coord p.1 p.2 := by
  unfold coord
  exact Complex.continuous_re.comp (continuous_snd.mul (Complex.continuous_conj.comp continuous_fst))

section chain

variable {κ₀ : ℝ} {L : ℕ → ℝ} {KQ KA δ : ℕ → ℝ → ℝ} {x₀ : ℕ → ℝ}
  (hM : ModelChain κ₀ L KQ KA δ x₀) (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1)
  (hs : Summable (chainDefect L KQ KA)) (hη : ∑' n, chainDefect L KQ KA n ≤ etaC κ₀)
include hM hκ₀ hκ₀1 hs hη

local notation "U" => (Filter.hyperfilter ℕ : Filter ℕ)

lemma LX_spec (n : ℕ) :
    Tendsto (fun N => (node L KA x₀ N n).1) U (𝓝 (LX L KA x₀ n)) ∧
      LX L KA x₀ n ∈ Set.Icc (π / Real.tan (Real.arcsin (khat κ₀))) (L n + devB κ₀) := by
  refine limUnder_spec (Filter.hyperfilter ℕ) isCompact_Icc ?_
  filter_upwards [eventually_gt_hyper n] with N hN
  exact ⟨node_lower hM hκ₀ hκ₀1 hs hη hN,
    by linarith [(abs_le.1 (node_L hM hκ₀ hκ₀1 hs hη hN.le)).2]⟩

lemma fX_spec (n : ℕ) (σ : ℝ) :
    Tendsto (fun N => (node L KA x₀ N n).2 σ) U (𝓝 (fX L KA x₀ n σ)) ∧
      fX L KA x₀ n σ ∈ Set.Icc 0 (khat κ₀) := by
  refine limUnder_spec (Filter.hyperfilter ℕ) isCompact_Icc ?_
  filter_upwards [eventually_gt_hyper n] with N hN
  exact (node_adm hM hκ₀ hκ₀1 hs hη hN.le).2.2.2.1 σ

lemma LX_pos (n : ℕ) : 0 < LX L KA x₀ n :=
  (div_pos Real.pi_pos (PathData.tan_arcsin_pos (khat_pos hκ₀) (khat_lt_one hκ₀1))).trans_le
    (LX_spec hM hκ₀ hκ₀1 hs hη n).2.1

lemma fX_lip (n : ℕ) (σ σ' : ℝ) :
    |fX L KA x₀ n σ - fX L KA x₀ n σ'| ≤
      (L (n + 1) + devB κ₀) / Real.cos (Real.arcsin (khat κ₀)) ^ 3 * |σ - σ'| := by
  have ht := ((fX_spec hM hκ₀ hκ₀1 hs hη n σ).1.sub (fX_spec hM hκ₀ hκ₀1 hs hη n σ').1).abs
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_gt_hyper n] with N hN
  exact node_lip hM hκ₀ hκ₀1 hs hη hN σ σ'

lemma fX_periodic (n : ℕ) : Function.Periodic (fX L KA x₀ n) 1 := fun σ => by
  have h1 := (fX_spec hM hκ₀ hκ₀1 hs hη n (σ + 1)).1
  have h2 := (fX_spec hM hκ₀ hκ₀1 hs hη n σ).1
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [eventually_gt_hyper n] with N hN
  exact (node_adm hM hκ₀ hκ₀1 hs hη hN.le).2.2.1 σ

lemma fX_unif (n : ℕ) : ∀ ε > 0, ∀ᶠ N in U, ∀ σ, |(node L KA x₀ N n).2 σ - fX L KA x₀ n σ| ≤ ε := by
  have hc := cos_arcsin_pos' (khat_pos hκ₀).le (khat_lt_one hκ₀1)
  have hB : 0 ≤ L (n + 1) + devB κ₀ := by
    have := hM.L_pos (n + 1)
    have : 0 ≤ devB κ₀ := by
      unfold devB
      exact mul_nonneg (mul_nonneg (khat_pos hκ₀).le K1c_pos.le) (etaC_pos hκ₀ hκ₀1).le
    linarith
  refine unif_of_pointwise (by positivity) ?_ (fX_lip hM hκ₀ hκ₀1 hs hη n) ?_
    (fX_periodic hM hκ₀ hκ₀1 hs hη n) fun σ => (fX_spec hM hκ₀ hκ₀1 hs hη n σ).1
  · filter_upwards [eventually_gt_hyper n] with N hN
    exact node_lip hM hκ₀ hκ₀1 hs hη hN
  · filter_upwards [eventually_gt_hyper n] with N hN
    exact (node_adm hM hκ₀ hκ₀1 hs hη hN.le).2.2.1

lemma fX_continuous (n : ℕ) : Continuous (fX L KA x₀ n) := by
  set C := (L (n + 1) + devB κ₀) / Real.cos (Real.arcsin (khat κ₀)) ^ 3
  refine Metric.continuous_iff.2 fun σ ε hε => ⟨ε / (|C| + 1), by positivity, fun σ' h => ?_⟩
  rw [Real.dist_eq] at h ⊢
  calc |fX L KA x₀ n σ' - fX L KA x₀ n σ| ≤ C * |σ' - σ| := fX_lip hM hκ₀ hκ₀1 hs hη n σ' σ
    _ ≤ |C| * |σ' - σ| := by gcongr; exact le_abs_self C
    _ ≤ |C| * (ε / (|C| + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg C]

lemma X_adm (n : ℕ) : AdmOval (khat κ₀) (LX L KA x₀ n) (fX L KA x₀ n) := by
  have hL := LX_pos hM hκ₀ hκ₀1 hs hη n
  have hfc := fX_continuous hM hκ₀ hκ₀1 hs hη n
  refine ⟨hL, hfc, fX_periodic hM hκ₀ hκ₀1 hs hη n,
    fun σ => (fX_spec hM hκ₀ hκ₀1 hs hη n σ).2, ?_⟩
  -- the integrals converge
  have ht : Tendsto (fun N => ∫ σ in (0 : ℝ)..1, (node L KA x₀ N n).1 * (node L KA x₀ N n).2 σ)
      U (𝓝 (∫ σ in (0 : ℝ)..1, LX L KA x₀ n * fX L KA x₀ n σ)) := by
    refine tendsto_of_lin_bound (C := 1 + LX L KA x₀ n) one_pos fun ε hε _ => ?_
    have hLt := (Metric.tendsto_nhds.1 (LX_spec hM hκ₀ hκ₀1 hs hη n).1) ε hε
    filter_upwards [eventually_gt_hyper n, hLt, fX_unif hM hκ₀ hκ₀1 hs hη n ε hε]
      with N hN hLN hfN
    have hA := node_adm hM hκ₀ hκ₀1 hs hη hN.le
    rw [Real.dist_eq] at hLN
    rw [← intervalIntegral.integral_sub
      (f := fun σ => (node L KA x₀ N n).1 * (node L KA x₀ N n).2 σ)
      (g := fun σ => LX L KA x₀ n * fX L KA x₀ n σ)
      ((continuous_const.mul hA.2.1).intervalIntegrable _ _)
      ((continuous_const.mul hfc).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun σ => (node L KA x₀ N n).1 * (node L KA x₀ N n).2 σ -
        LX L KA x₀ n * fX L KA x₀ n σ) (C := (1 + LX L KA x₀ n) * ε) (fun σ _ => by
        simp only [Real.norm_eq_abs]
        rw [show (node L KA x₀ N n).1 * (node L KA x₀ N n).2 σ -
          LX L KA x₀ n * fX L KA x₀ n σ = ((node L KA x₀ N n).1 - LX L KA x₀ n) *
          (node L KA x₀ N n).2 σ + LX L KA x₀ n * ((node L KA x₀ N n).2 σ - fX L KA x₀ n σ)
          by ring]
        have h1 := hA.abs_le_one (khat_lt_one hκ₀1) σ
        calc _ ≤ |(node L KA x₀ N n).1 - LX L KA x₀ n| * |(node L KA x₀ N n).2 σ| +
              LX L KA x₀ n * |(node L KA x₀ N n).2 σ - fX L KA x₀ n σ| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_pos hL]
          _ ≤ ε * 1 + LX L KA x₀ n * ε := add_le_add (mul_le_mul hLN.le h1 (abs_nonneg _)
              hε.le) (mul_le_mul_of_nonneg_left (hfN σ) hL.le)
          _ = (1 + LX L KA x₀ n) * ε := by ring)
    simpa using this
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_hyper n] with N hN
  exact ((node_adm hM hκ₀ hκ₀1 hs hη hN.le).2.2.2.2).symm

lemma X_step (n : ℕ) :
    (LX L KA x₀ n, fX L KA x₀ n) = rearOv (LX L KA x₀ (n + 1), fX L KA x₀ (n + 1)) := by
  have hA := X_adm hM hκ₀ hκ₀1 hs hη (n + 1)
  obtain ⟨hRL, hRF⟩ := rear_tendsto (Lj := fun N => (node L KA x₀ N (n + 1)).1)
    (fj := fun N => (node L KA x₀ N (n + 1)).2) hA (khat_pos hκ₀) (khat_lt_one hκ₀1)
    (by filter_upwards [eventually_gt_hyper (n + 1)] with N hN
        exact node_adm hM hκ₀ hκ₀1 hs hη hN.le)
    (LX_spec hM hκ₀ hκ₀1 hs hη (n + 1)).1 (fX_unif hM hκ₀ hκ₀1 hs hη (n + 1))
  have hev : ∀ᶠ N in U, node L KA x₀ N n = rearOv (node L KA x₀ N (n + 1)) := by
    filter_upwards [eventually_gt_hyper n] with N hN
    exact node_succ L KA x₀ hN
  refine Prod.ext ?_ (funext fun σ => ?_)
  · refine tendsto_nhds_unique (LX_spec hM hκ₀ hκ₀1 hs hη n).1 (hRL.congr' ?_)
    filter_upwards [hev] with N hN
    rw [hN]; rfl
  · refine tendsto_nhds_unique (fX_spec hM hκ₀ hκ₀1 hs hη n σ).1 ((hRF σ).congr' ?_)
    filter_upwards [hev] with N hN
    rw [hN]; rfl

lemma X_width {W : ℝ}
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
      curveOfCurvature 0 (KQ n) (L n) s') ≤ W) (n : ℕ) :
    WidthLe W (LX L KA x₀ n, fX L KA x₀ n) := by
  have hex : ∀ N, ∃ v : ℂ, v ∈ Metric.sphere (0 : ℂ) 1 ∧ (n ≤ N → ∀ s s',
      coord v (curveOfCurvature 0 (fun s => (node L KA x₀ N n).2 (s / (node L KA x₀ N n).1))
        (node L KA x₀ N n).1 s - curveOfCurvature 0
        (fun s => (node L KA x₀ N n).2 (s / (node L KA x₀ N n).1)) (node L KA x₀ N n).1 s')
        ≤ W) := fun N => by
    by_cases h : n ≤ N
    · obtain ⟨v, hv, hvW⟩ := node_width hM hκ₀ hκ₀1 hs hη hW h
      exact ⟨v, by simpa using hv, fun _ => hvW⟩
    · exact ⟨1, by simp, fun h' => absurd h' h⟩
  choose v hv hvW using hex
  obtain ⟨hvt, hvs⟩ := limUnder_spec (Filter.hyperfilter ℕ) (isCompact_sphere (0 : ℂ) 1)
    (Filter.Eventually.of_forall hv)
  refine ⟨limUnder U v, by simpa using hvs, fun s s' => ?_⟩
  have hL := LX_pos hM hκ₀ hκ₀1 hs hη n
  have hLt := (LX_spec hM hκ₀ hκ₀1 hs hη n).1
  have hfc := fX_continuous hM hκ₀ hκ₀1 hs hη n
  set C := (L (n + 1) + devB κ₀) / Real.cos (Real.arcsin (khat κ₀)) ^ 3
  have hinv : Tendsto (fun N => ((node L KA x₀ N n).1)⁻¹) U (𝓝 (LX L KA x₀ n)⁻¹) :=
    hLt.inv₀ hL.ne'
  have hcurve : ∀ t, Tendsto (fun N => curveOfCurvature 0
      (fun s => (node L KA x₀ N n).2 (s / (node L KA x₀ N n).1)) (node L KA x₀ N n).1 t) U
      (𝓝 (curveOfCurvature 0 (fun s => fX L KA x₀ n (s / LX L KA x₀ n)) (LX L KA x₀ n) t)) :=
    fun t => by
    refine curve_tendsto (hfc.comp (continuous_id.div_const _)) ?_ (fun R ε hε => ?_) hLt 0 t
    · filter_upwards [eventually_gt_hyper n] with N hN
      exact (node_adm hM hκ₀ hκ₀1 hs hη hN.le).2.1.comp (continuous_id.div_const _)
    · have hR : 0 < |C| * |R| + 1 := by positivity
      have h1 := (Metric.tendsto_nhds.1 hinv) (ε / 2 / (|C| * |R| + 1)) (by positivity)
      filter_upwards [h1, fX_unif hM hκ₀ hκ₀1 hs hη n (ε / 2) (by positivity)] with N hN hfN
      intro r hr
      rw [Real.dist_eq] at hN
      have e1 := hfN (r / (node L KA x₀ N n).1)
      have e2 := fX_lip hM hκ₀ hκ₀1 hs hη n (r / (node L KA x₀ N n).1) (r / LX L KA x₀ n)
      have e3 : |r / (node L KA x₀ N n).1 - r / LX L KA x₀ n| ≤
          |R| * (ε / 2 / (|C| * |R| + 1)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
        exact mul_le_mul (hr.trans (le_abs_self R)) hN.le (abs_nonneg _) (abs_nonneg _)
      calc |(node L KA x₀ N n).2 (r / (node L KA x₀ N n).1) - fX L KA x₀ n (r / LX L KA x₀ n)|
          ≤ |(node L KA x₀ N n).2 (r / (node L KA x₀ N n).1) -
              fX L KA x₀ n (r / (node L KA x₀ N n).1)| +
            |fX L KA x₀ n (r / (node L KA x₀ N n).1) - fX L KA x₀ n (r / LX L KA x₀ n)| :=
            abs_sub_le _ _ _
        _ ≤ ε / 2 + |C| * (|R| * (ε / 2 / (|C| * |R| + 1))) := by
            refine add_le_add e1 (e2.trans ?_)
            exact mul_le_mul (le_abs_self C) e3 (abs_nonneg _) (abs_nonneg _)
        _ ≤ ε / 2 + ε / 2 := by
            gcongr
            rw [← mul_assoc, mul_div_assoc', div_le_iff₀ hR]
            nlinarith [abs_nonneg C, abs_nonneg R]
        _ = ε := by ring
  have ht := (coord_continuous.tendsto _).comp (hvt.prodMk_nhds ((hcurve s).sub (hcurve s')))
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_gt_hyper n] with N hN
  exact hvW N hN.le s s'

/-- **The limiting orbit.**  The limits `X n = (LX n, fX n)` are admissible normalized ovals with
`X n = 𝓑 X_{n+1}`, lying in strips of width `W` if all fronts of the chain do. -/
theorem limit_orbit_data {W : ℝ}
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
      curveOfCurvature 0 (KQ n) (L n) s') ≤ W) :
    ∃ (LX' : ℕ → ℝ) (fX' : ℕ → ℝ → ℝ), ∀ n, AdmOval (khat κ₀) (LX' n) (fX' n) ∧
      (LX' n, fX' n) = rearOv (LX' (n + 1), fX' (n + 1)) ∧ WidthLe W (LX' n, fX' n) :=
  ⟨LX L KA x₀, fX L KA x₀, fun n => ⟨X_adm hM hκ₀ hκ₀1 hs hη n, X_step hM hκ₀ hκ₀1 hs hη n,
    X_width hM hκ₀ hκ₀1 hs hη hW n⟩⟩

end chain

end Ovals

end
