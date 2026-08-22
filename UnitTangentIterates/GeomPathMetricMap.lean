import Mathlib
import UnitTangentIterates.GeomPathMetric
import UnitTangentIterates.SummableNormalPathLimit

/-!
# Maps of marked curves in the geometric pseudometric

`PathMetric.pathDist_le_of_maps_paths` reduces non-expansiveness of a map of
marked curves for the path pseudodistance to the statement that it takes normal
paths to normal paths of no greater cost.  Since the estimates of the paper's
lemma *Inverse Jacobi estimates* are available only for paths whose slices are
constant-speed closed curves with the tube bounds, the same reduction is needed
for the restricted class of geometric normal paths of `GeomPathMetric.lean`.
This file provides it:

* `geomDist_le_of_maps_geomPaths` — the non-expansiveness criterion;
* `geomDist_le_mul_of_maps_geomPaths` — the Lipschitz criterion;
* `dist_le_mul_geomDist_of_maps_geomPaths` — the resulting bound for the metric
  of the space of marked curves;
* `tendsto_of_geomDist_tendsto_zero` — convergence in the geometric
  pseudodistance implies convergence in the marked geometric topology;
* `geomSet_nonempty_chain`, `geomDist_le_sum_range` — the chain form of the
  triangle inequality along a sequence;
* `exists_limit_of_summable_geomDist` — a sequence of tube members with
  summable consecutive geometric pseudodistances converges to a marked curve of
  the same tube.
-/

noncomputable section

open Set Filter Topology MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace GeomPathMetric

variable {p q : Data}

/-- **A criterion for non-expansiveness in the geometric pseudometric.**  A map
of marked curves which takes every geometric normal path from `p` to `q` to a
geometric normal path of no greater cost does not increase `geomDist`. -/
theorem geomDist_le_of_maps_geomPaths {P0 P1 khat : ℝ} {F : Data → Data}
    (h : ∀ Γ : NormalPath p q, IsGeomNormalPath P0 P1 khat Γ →
      ∃ Γ' : NormalPath (F p) (F q), IsGeomNormalPath P0 P1 khat Γ' ∧ cost Γ' ≤ cost Γ)
    (hne : (geomSet P0 P1 khat p q).Nonempty) :
    geomDist P0 P1 khat (F p) (F q) ≤ geomDist P0 P1 khat p q := by
  refine le_csInf hne ?_
  rintro x ⟨Γ, hΓ, rfl⟩
  obtain ⟨Γ', hΓ', hcost⟩ := h Γ hΓ
  exact le_trans (geomDist_le_cost Γ' hΓ') hcost

/-- **A Lipschitz criterion in the geometric pseudometric.**  A map of marked
curves which takes every geometric normal path from `p` to `q` to a geometric
normal path of cost at most `C` times as large is `C`-Lipschitz for
`geomDist`. -/
theorem geomDist_le_mul_of_maps_geomPaths {P0 P1 khat C : ℝ} {F : Data → Data} (hC : 0 ≤ C)
    (h : ∀ Γ : NormalPath p q, IsGeomNormalPath P0 P1 khat Γ →
      ∃ Γ' : NormalPath (F p) (F q), IsGeomNormalPath P0 P1 khat Γ' ∧ cost Γ' ≤ C * cost Γ)
    (hne : (geomSet P0 P1 khat p q).Nonempty) :
    geomDist P0 P1 khat (F p) (F q) ≤ C * geomDist P0 P1 khat p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  have hεpos : 0 < ε / (C + 1) := by positivity
  obtain ⟨x, ⟨Γ, hΓ, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne
    (show geomDist P0 P1 khat p q < geomDist P0 P1 khat p q + ε / (C + 1) by linarith)
  obtain ⟨Γ', hΓ', hcost⟩ := h Γ hΓ
  have h1 : geomDist P0 P1 khat (F p) (F q) ≤ C * cost Γ :=
    le_trans (geomDist_le_cost Γ' hΓ') hcost
  have h2 : C * cost Γ ≤ C * (geomDist P0 P1 khat p q + ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hx.le hC
  have h3 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hCpos]
    nlinarith
  nlinarith [h1, h2, h3]

/-- The Lipschitz criterion, read in the metric of the space of marked
curves. -/
theorem dist_le_mul_geomDist_of_maps_geomPaths {c kmin dlt cq kminq dltq P0 P1 khat C : ℝ}
    {F : Data → Data} (hP0 : 0 ≤ P0) (hC : 0 ≤ C)
    (hFp : IsTubeMember c kmin dlt (F p)) (hFq : IsTubeMember cq kminq dltq (F q))
    (h : ∀ Γ : NormalPath p q, IsGeomNormalPath P0 P1 khat Γ →
      ∃ Γ' : NormalPath (F p) (F q), IsGeomNormalPath P0 P1 khat Γ' ∧ cost Γ' ≤ C * cost Γ)
    (hne : (geomSet P0 P1 khat p q).Nonempty) :
    dist (F p) (F q) ≤ c2Const P0 P1 khat * C * geomDist P0 P1 khat p q := by
  have hc2 : (0:ℝ) < c2Const P0 P1 khat := lt_of_lt_of_le one_pos (one_le_c2Const P0 P1 khat)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨Γ, hΓ, rfl⟩ := hx
  obtain ⟨Γ', hΓ', -⟩ := h Γ hΓ
  have hneF : (geomSet P0 P1 khat (F p) (F q)).Nonempty := ⟨cost Γ', Γ', hΓ', rfl⟩
  have h1 : dist (F p) (F q) ≤ c2Const P0 P1 khat * geomDist P0 P1 khat (F p) (F q) :=
    dist_le_c2Const_mul_geomDist hP0 hFp hFq hneF
  have h2 : geomDist P0 P1 khat (F p) (F q) ≤ C * geomDist P0 P1 khat p q :=
    geomDist_le_mul_of_maps_geomPaths hC h ⟨cost Γ, Γ, hΓ, rfl⟩
  calc dist (F p) (F q) ≤ c2Const P0 P1 khat * geomDist P0 P1 khat (F p) (F q) := h1
    _ ≤ c2Const P0 P1 khat * (C * geomDist P0 P1 khat p q) :=
        mul_le_mul_of_nonneg_left h2 hc2.le
    _ = c2Const P0 P1 khat * C * geomDist P0 P1 khat p q := by ring

/-- **Convergence in the geometric pseudodistance implies convergence in the
marked geometric topology.** -/
theorem tendsto_of_geomDist_tendsto_zero {c kmin dlt cq kminq dltq P0 P1 khat : ℝ}
    {P : ℕ → Data} {q : Data} (hP0 : 0 ≤ P0)
    (hmem : ∀ n, IsTubeMember c kmin dlt (P n)) (hq : IsTubeMember cq kminq dltq q)
    (hne : ∀ n, (geomSet P0 P1 khat (P n) q).Nonempty)
    (h : Tendsto (fun n => geomDist P0 P1 khat (P n) q) atTop (𝓝 0)) :
    Tendsto P atTop (𝓝 q) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg)
    (fun n => dist_le_c2Const_mul_geomDist hP0 (hmem n) hq (hne n)) ?_
  simpa using h.const_mul (c2Const P0 P1 khat)

/-! ### Chains -/

/-- Two geometric normal paths in succession give one, so the geometric cost
sets compose. -/
theorem geomSet_nonempty_trans {P0 P1 khat : ℝ} (hP0 : 0 < P0) {p q r : Data}
    (h1 : (geomSet P0 P1 khat p q).Nonempty) (h2 : (geomSet P0 P1 khat q r).Nonempty) :
    (geomSet P0 P1 khat p r).Nonempty := by
  obtain ⟨x, Γ, hΓ, -⟩ := h1
  obtain ⟨y, Δ, hΔ, -⟩ := h2
  exact ⟨cost (NormalPath.concat Γ Δ), NormalPath.concat Γ Δ, hΓ.concat hP0 hΔ, rfl⟩

/-- Along a sequence whose consecutive terms are joined by geometric normal
paths, any two terms are joined by one. -/
theorem geomSet_nonempty_chain {P0 P1 khat : ℝ} (hP0 : 0 < P0) {P : ℕ → Data}
    (hne : ∀ n, (geomSet P0 P1 khat (P n) (P (n + 1))).Nonempty) (m N : ℕ) :
    (geomSet P0 P1 khat (P m) (P (m + N))).Nonempty := by
  induction N with
  | zero =>
    obtain ⟨x, Γ, hΓ, -⟩ := hne m
    exact ⟨cost (NormalPath.const (P m)), NormalPath.const (P m),
      isGeomNormalPath_const hΓ.isGeomCurve_start, rfl⟩
  | succ N ih =>
    have h := geomSet_nonempty_trans hP0 ih (hne (m + N))
    simpa [← add_assoc] using h

/-- **The chain form of the triangle inequality.** -/
theorem geomDist_le_sum_range {P0 P1 khat : ℝ} (hP0 : 0 < P0) {P : ℕ → Data}
    (hne : ∀ n, (geomSet P0 P1 khat (P n) (P (n + 1))).Nonempty) (m N : ℕ) :
    geomDist P0 P1 khat (P m) (P (m + N))
      ≤ ∑ k ∈ Finset.range N, geomDist P0 P1 khat (P (m + k)) (P (m + k + 1)) := by
  induction N with
  | zero =>
    simpa using (geomDist_self_of_nonempty (hne m)).le
  | succ N ih =>
    have htri := geomDist_triangle (P0 := P0) (P1 := P1) (khat := khat) hP0
      (geomSet_nonempty_chain hP0 hne m N) (hne (m + N))
    have hstep : geomDist P0 P1 khat (P m) (P (m + (N + 1)))
        ≤ geomDist P0 P1 khat (P m) (P (m + N))
          + geomDist P0 P1 khat (P (m + N)) (P (m + N + 1)) := by
      simpa [← add_assoc] using htri
    rw [Finset.sum_range_succ]
    linarith

/-- **Summable geometric pseudodistances give a limit in the tube.** -/
theorem exists_limit_of_summable_geomDist {c kmin dlt P0 P1 khat : ℝ} {P : ℕ → Data}
    (hP0 : 0 ≤ P0) (hmem : ∀ n, IsTubeMember c kmin dlt (P n))
    (hne : ∀ n, (geomSet P0 P1 khat (P n) (P (n + 1))).Nonempty)
    (hsum : Summable fun n => geomDist P0 P1 khat (P n) (P (n + 1))) :
    ∃ plim : Data, IsTubeMember c kmin dlt plim ∧ Tendsto P atTop (𝓝 plim) := by
  refine SummableNormalPathLimit.exists_limit_of_summable_dist hmem
    (hsum.mul_left (c2Const P0 P1 khat)) (fun n => ?_)
  exact dist_le_c2Const_mul_geomDist hP0 (hmem n) (hmem (n + 1)) (hne n)

end GeomPathMetric
