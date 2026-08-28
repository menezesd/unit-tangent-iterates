import UnitTangentIterates.ConstructedNoFloor

/-!
# The exact form of the curvature-floor obstruction

§47 showed the main theorem's uniform floor `0 < kmin` cannot be met by the
construction.  This file pins down what *can* be: a floor at each level is not
forbidden, but it is bounded by `π/Hₙ`.

* `levelwise_floor_le` : `kmins n ≤ π/Hₙ`, for any level-wise floor;
* `levelwise_floor_tendsto_zero` : hence for the constructed sequence, every
  level-wise floor gets below any positive constant.

So the repair to `unit_tangent_iterates_main_theorem` is not to weaken `kmin`
slightly — no positive constant works.  Either the floor must be indexed by `n`
and allowed to decay like `π/Hₙ` (with the chord-arc constant of
`ModelChordArc.modelChordConst` re-derived accordingly), or the chord-arc bound
must come from the two-cap geometry rather than from a curvature floor.  The
first route is the one `CurvatureFloorFreeFamily` prepares.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Filter Topology MeasureTheory

/-- **Any curvature floor decays like `π/Hₙ`.**  This is the exact form of the
obstruction: a floor at level `n` is not forbidden, but it is bounded by
`π/Hₙ`, so no floor uniform in `n` survives once the separations grow. -/
theorem levelwise_floor_le {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {kmins : ℕ → ℝ}
    (hH : ∀ n, 0 < Hs n) (hk : ∀ n, Continuous (kappas n))
    (hkmin : ∀ n s, kmins n ≤ kappas n s)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) (n : ℕ) :
    kmins n ≤ Real.pi / Hs n := by
  have hmono := intervalIntegral.integral_mono_on (hH n).le
    (intervalIntegrable_const (μ := volume) (c := kmins n) (a := (0:ℝ))
      (b := Hs n))
    ((hk n).intervalIntegrable _ _) (fun s _ => hkmin n s)
  rw [htotal n, intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  rw [le_div_iff₀ (hH n)]
  linarith

/-- Hence the floors tend to zero for the constructed sequence. -/
theorem levelwise_floor_tendsto_zero {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ),
      (∀ n, 0 < Hs n) ∧
      (∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) ∧
      ∀ (kmins : ℕ → ℝ), (∀ n s, kmins n ≤ kappas n s) →
        ∀ c : ℝ, 0 < c → ∃ n, kmins n < c := by
  obtain ⟨kappas, Hs, Delta, hDelta, hHpos, hcont, htotal, hgrow, -⟩ :=
    no_positive_floor_of_eps heps heps10
  refine ⟨kappas, Hs, hHpos, htotal, ?_⟩
  intro kmins hkmin c hc
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / c - Hs 0) / Delta)
  refine ⟨n, ?_⟩
  have hbdd := levelwise_floor_le hHpos hcont hkmin htotal n
  have hgn := hgrow n
  have hmul := (div_lt_iff₀ hDelta).mp hn
  have hHn : Real.pi / c < Hs n := by nlinarith [hgn, hmul]
  by_contra hcon
  push_neg at hcon
  have h1 : Real.pi / Hs n < c := by
    rw [div_lt_iff₀ (hHpos n)]
    rw [div_lt_iff₀ hc] at hHn
    linarith
  linarith [hbdd, hcon, h1]
