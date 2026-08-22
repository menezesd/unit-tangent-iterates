import Mathlib
import UnitTangentIterates.TubeInvariance
import UnitTangentIterates.SummableNormalPathLimit

/-!
# The terminal pullbacks converge to an exact inverse orbit

`UnitTangentIterates/TubeInvariance.lean` shows that the terminal pullbacks

```
  Zₙ^{(n+k)} = B^k (Q_{n+k})
```

of a model pseudo-orbit stay in the tubes `𝒟ₙ` of the theorem *Regularizing
backward shadowing* of *A Noncircular Oval with Convex Unit-Tangent Iterates*.
This file runs the rest of the scheme **in the concrete space of marked
curves**: consecutive pullbacks are joined by normal paths whose costs are
dominated by `Kᵏ dₙ₊ₖ`, hence summable, so the lemma *Completeness of summable
normal paths* (`SummableNormalPathLimit.exists_limit_of_summable_costs`)
produces limits `Xₙ` in the same tube; they form an **exact inverse orbit**
`Xₙ = B X_{n+1}` and they shadow the model, `‖Xₙ − Qₙ‖ ≤ rₙ` pointwise, where
`rₙ = ∑_{m ≥ n} d_m`.

Main results:

* `exists_path_iterate` — the `k`-th image of a normal path under `B` is a
  normal path of cost at most `Kᵏ` times as large;
* `exists_step_path` — consequently consecutive pullbacks are joined by a path
  of cost at most `Kᵏ d_{n+k}`;
* `exists_shadowing_limit_of_radii` — the limits `Xₙ`, their membership of the
  tube, the exact orbit relation `Xₙ = B X_{n+1}`, the membership of every
  pullback in the tube of radius `aₙ` around the model, the pointwise shadowing
  bound, the shadowing bound in the marked metric and the perimeter clause, for
  any radii dominating the partial sums of `∑ₖ Kᵏ d_{n+k}`;
* `exists_shadowing_limit` — the case `K ≤ 1` of summable defects, with the
  radii the tails `rₙ = ∑_{m ≥ n} d_m`;
* `exists_shadowing_limit_geom` — the case of an inverse step that may expand,
  `Kθ < 1` against geometric defects `dₙ ≤ Dθⁿ`, with the radii `Dθⁿ/(1 − Kθ)`.

As in `TubeInvariance.lean`, what is assumed and not proved is that the
selected inverse takes normal paths to normal paths of controlled cost (the
paper's lemmas *Smooth dependence of the selected rear* and *Inverse Jacobi
estimates*) and that the pullbacks remain members of the tube.
-/

noncomputable section

open Set Filter Topology MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace TubePullbackLimit

/-- The terminal pullback `Zₙ^{(n+k)} = B^k (Q_{n+k})`. -/
def pullback (B : Data → Data) (Q : ℕ → Data) (n k : ℕ) : Data := B^[k] (Q (n + k))

@[simp] theorem pullback_zero (B : Data → Data) (Q : ℕ → Data) (n : ℕ) :
    pullback B Q n 0 = Q n := by simp [pullback]

/-- The pullbacks of consecutive levels are related by one application of the
map: `Zₙ^{(n+k+1)} = B Z_{n+1}^{(n+1+k)}`. -/
theorem pullback_succ (B : Data → Data) (Q : ℕ → Data) (n k : ℕ) :
    pullback B Q n (k + 1) = B (pullback B Q (n + 1) k) := by
  have hidx : n + (k + 1) = (n + 1) + k := by omega
  simp [pullback, hidx, Function.iterate_succ_apply']

/-- **The iterated image of a normal path.**  If `B` takes a constant-speed
normal path to a constant-speed normal path of cost at most `K` times as large,
then `B^k` multiplies the cost by at most `Kᵏ`. -/
theorem exists_path_iterate {B : Data → Data} {K P0 P1 khat : ℝ} (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (k : ℕ) {p q : Data} (Γ : NormalPath p q) (hΓ : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    ∃ Δ : NormalPath (B^[k] p) (B^[k] q),
      cost Δ ≤ K ^ k * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  induction k with
  | zero => exact ⟨Γ, by simp, hΓ⟩
  | succ k ih =>
      obtain ⟨Δ, hΔ, hΔgeom⟩ := ih
      obtain ⟨Δ', hΔ', hΔ'geom⟩ := hmap _ _ Δ hΔgeom
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨Δ', ?_, hΔ'geom⟩
      calc cost Δ' ≤ K * cost Δ := hΔ'
        _ ≤ K * (K ^ k * cost Γ) := mul_le_mul_of_nonneg_left hΔ hK
        _ = K ^ (k + 1) * cost Γ := by ring

/-- **Consecutive pullbacks are close.**  The defect path from `Q_{n+k}` to
`B Q_{n+k+1}`, pushed forward `k` times, joins `Zₙ^{(n+k)} to `Zₙ^{(n+k+1)}` at
cost at most `Kᵏ d_{n+k}`. -/
theorem exists_step_path {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ} {K P0 P1 khat : ℝ}
    (hK : 0 ≤ K)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (n k : ℕ) :
    ∃ Δ : NormalPath (pullback B Q n k) (pullback B Q n (k + 1)),
      cost Δ ≤ K ^ k * d (n + k) ∧ IsConstantSpeedNormalPath P0 P1 khat Δ := by
  obtain ⟨Λ, hΛ, hΛgeom⟩ := hdefect (n + k)
  obtain ⟨Δ, hΔ, hΔgeom⟩ := exists_path_iterate hK hmap k Λ hΛgeom
  have hidx : n + (k + 1) = (n + k) + 1 := by omega
  have htarget : pullback B Q n (k + 1) = B^[k] (B (Q ((n + k) + 1))) := by
    simp [pullback, hidx, Function.iterate_succ_apply]
  rw [htarget]
  refine ⟨Δ, ?_, hΔgeom⟩
  exact hΔ.trans (mul_le_mul_of_nonneg_left hΛ (pow_nonneg hK k))

/-- **The shadowing limits, with abstract radii.**  Let `B` take constant-speed
normal paths to constant-speed normal paths of cost at most `K` times as large,
let the models `Qₙ` be joined to `B Q_{n+1}` by defect paths of cost `dₙ`, let
the weighted series `∑ₖ Kᵏ d_{n+k}` converge with partial sums at most `aₙ`, let
every pullback be a member of the tube, and let `B` be continuous.  Then the
terminal pullbacks converge to marked curves `Xₙ` of the same tube which form an
exact inverse orbit `Xₙ = B X_{n+1}` and shadow the model within `aₙ`:
pointwise, in the marked metric up to `c2Const`, and in perimeter. -/
theorem exists_shadowing_limit_of_radii {B : Data → Data} {Q : ℕ → Data} {d a : ℕ → ℝ}
    {K c kmin dlt P0 P1 khat : ℝ}
    (hK : 0 ≤ K)
    (hsum : ∀ n, Summable fun k => K ^ k * d (n + k))
    (ha : ∀ n k, ∑ j ∈ Finset.range k, K ^ j * d (n + j) ≤ a n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c kmin dlt (X n)) ∧
      (∀ n, Tendsto (pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n k, pullback B Q n k ∈ TubeInvariance.tube (Q n) (a n)) ∧
      (∀ n u, ‖(X n).1 u - (Q n).1 u‖ ≤ a n) ∧
      (∀ n, dist (Q n) (X n) ≤ c2Const P0 P1 khat * a n) ∧
      (∀ n, |perim (X n) - perim (Q n)| ≤ c2Const P0 P1 khat * a n) := by
  -- the paths joining consecutive pullbacks, and their summable costs
  choose Γ hΓcost hΓgeom using fun n k =>
    exists_step_path (Q := Q) (d := d) hK hmap hdefect n k
  have hsummable : ∀ n, Summable fun k => cost (Γ n k) := by
    intro n
    exact Summable.of_nonneg_of_le (fun k => cost_nonneg _) (fun k => hΓcost n k) (hsum n)
  -- the limits
  have hlimit : ∀ n, ∃ plim : Data,
      IsTubeMember c kmin dlt plim ∧ Tendsto (pullback B Q n) atTop (𝓝 plim) := by
    intro n
    exact SummableNormalPathLimit.exists_limit_of_summable_costs (Γ n) (hmem n)
      (hΓgeom n) (hsummable n)
  choose X hXmem hXlim using hlimit
  -- the costs of the steps are dominated by the weighted defects
  have hpartial : ∀ n k : ℕ, ∑ j ∈ Finset.range k, cost (Γ n j) ≤ a n := by
    intro n k
    have h1 : ∑ j ∈ Finset.range k, cost (Γ n j)
        ≤ ∑ j ∈ Finset.range k, K ^ j * d (n + j) :=
      Finset.sum_le_sum fun j _ => hΓcost n j
    exact h1.trans (ha n k)
  -- every pullback lies in the tube of radius `aₙ` around the model
  have htube : ∀ n k, pullback B Q n k ∈ TubeInvariance.tube (Q n) (a n) := by
    intro n k
    have hchain : ∀ k : ℕ, ∃ Δ : NormalPath (Q n) (pullback B Q n k),
        cost Δ ≤ ∑ j ∈ Finset.range k, cost (Γ n j) := by
      intro k
      induction k with
      | zero =>
          rw [pullback_zero]
          exact ⟨NormalPath.const (Q n), by simp⟩
      | succ k ih =>
          obtain ⟨Δ, hΔ⟩ := ih
          refine ⟨Δ.concat (Γ n k), ?_⟩
          rw [cost_concat, Finset.sum_range_succ]
          gcongr
    obtain ⟨Δ, hΔ⟩ := hchain k
    exact ⟨Δ, hΔ.trans (hpartial n k)⟩
  -- the pullbacks stay close to the model in the marked metric as well
  have hdistk : ∀ n k, dist (Q n) (pullback B Q n k)
      ≤ c2Const P0 P1 khat * ∑ j ∈ Finset.range k, cost (Γ n j) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : dist (pullback B Q n k) (pullback B Q n (k + 1))
            ≤ c2Const P0 P1 khat * cost (Γ n k) :=
          NormalPathC2Increment.dist_le_cost (Γ n k) (hmem n k) (hmem n (k + 1)) (hΓgeom n k)
        have htri := dist_triangle (Q n) (pullback B Q n k) (pullback B Q n (k + 1))
        rw [Finset.sum_range_succ, mul_add]
        linarith
  have hdistlim : ∀ n, dist (Q n) (X n) ≤ c2Const P0 P1 khat * a n := by
    intro n
    have hlim : Tendsto (fun k => dist (Q n) (pullback B Q n k)) atTop (𝓝 (dist (Q n) (X n))) :=
      tendsto_const_nhds.dist (hXlim n)
    refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    exact (hdistk n k).trans
      (mul_le_mul_of_nonneg_left (hpartial n k) (c2Const_nonneg P0 P1 khat))
  refine ⟨X, hXmem, hXlim, ?_, htube, ?_, hdistlim, fun n => ?_⟩
  · -- the exact orbit relation
    intro n
    have hshift : Tendsto (fun k => pullback B Q n (k + 1)) atTop (𝓝 (X n)) :=
      (hXlim n).comp (tendsto_add_atTop_nat 1)
    have hB : Tendsto (fun k => B (pullback B Q (n + 1) k)) atTop (𝓝 (B (X (n + 1)))) :=
      (hBcont.tendsto _).comp (hXlim (n + 1))
    have : (fun k => pullback B Q n (k + 1)) = fun k => B (pullback B Q (n + 1) k) :=
      funext fun k => pullback_succ B Q n k
    rw [this] at hshift
    exact tendsto_nhds_unique hshift hB
  · -- the shadowing bound
    intro n u
    have hbound : ∀ k, ‖(pullback B Q n k).1 u - (Q n).1 u‖ ≤ a n :=
      fun k => TubeInvariance.norm_sub_le_of_mem_tube (htube n k) u
    have hpt : Tendsto (fun k => (pullback B Q n k).1 u) atTop (𝓝 ((X n).1 u)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (g := fun k => dist (pullback B Q n k) (X n)) (fun k => dist_nonneg)
        (fun k => ?_) ?_
      · simpa [dist_eq_norm] using MarkedSpace.dist_apply_le (pullback B Q n k) (X n) u
      · simpa using (tendsto_iff_dist_tendsto_zero.1 (hXlim n))
    have hnorm : Tendsto (fun k => ‖(pullback B Q n k).1 u - (Q n).1 u‖) atTop
        (𝓝 ‖(X n).1 u - (Q n).1 u‖) :=
      (hpt.sub tendsto_const_nhds).norm
    exact le_of_tendsto hnorm (Eventually.of_forall hbound)
  · -- the perimeters of the limit and of the model are close
    calc |perim (X n) - perim (Q n)| ≤ dist (X n) (Q n) := MarkedSpace.abs_perim_sub_le_dist _ _
      _ = dist (Q n) (X n) := dist_comm _ _
      _ ≤ c2Const P0 P1 khat * a n := hdistlim n

/-- **The shadowing limits for a non-expanding map.**  When `K ≤ 1` and the
defects are summable, the radii may be taken to be the tails
`rₙ = ∑_{m ≥ n} d_m` of the defect sequence. -/
theorem exists_shadowing_limit {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K c kmin dlt P0 P1 khat : ℝ}
    (hK : 0 ≤ K) (hK1 : K ≤ 1) (hd : ∀ n, 0 ≤ d n) (hs : Summable d)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c kmin dlt (X n)) ∧
      (∀ n, Tendsto (pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n k, pullback B Q n k ∈ TubeInvariance.tube (Q n) (ShadowingTails.tail d n)) ∧
      (∀ n u, ‖(X n).1 u - (Q n).1 u‖ ≤ ShadowingTails.tail d n) ∧
      (∀ n, dist (Q n) (X n) ≤ c2Const P0 P1 khat * ShadowingTails.tail d n) ∧
      (∀ n, |perim (X n) - perim (Q n)| ≤ c2Const P0 P1 khat * ShadowingTails.tail d n) := by
  have hterm : ∀ n k : ℕ, K ^ k * d (n + k) ≤ d (n + k) := by
    intro n k
    have hpow : K ^ k ≤ 1 := pow_le_one₀ hK hK1
    nlinarith [hd (n + k), pow_nonneg hK k]
  have hsum : ∀ n, Summable fun k => K ^ k * d (n + k) := by
    intro n
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg hK k) (hd _)) (hterm n)
      (ShadowingTails.summable_shift hs n)
  have ha : ∀ n k, ∑ j ∈ Finset.range k, K ^ j * d (n + j) ≤ ShadowingTails.tail d n := by
    intro n k
    have h1 : ∑ j ∈ Finset.range k, K ^ j * d (n + j) ≤ ∑ j ∈ Finset.range k, d (n + j) :=
      Finset.sum_le_sum fun j _ => hterm n j
    have h2 : ∑ j ∈ Finset.range k, d (n + j) ≤ ∑' m, d (n + m) :=
      Summable.sum_le_tsum _ (fun j _ => hd _) (ShadowingTails.summable_shift hs n)
    exact h1.trans h2
  exact exists_shadowing_limit_of_radii hK hsum ha hmap hdefect hmem hBcont

/-- **The shadowing limits for a map that may expand, against geometric
defects.**  If the cost factor of one inverse step is `K` and the defects decay
geometrically, `dₙ ≤ Dθⁿ` with `Kθ < 1`, the scheme still converges: the radii
may be taken to be `Dθⁿ/(1 − Kθ)`.  This is the form the model pseudo-orbit
of the paper meets, its defects decaying exponentially in the separation. -/
theorem exists_shadowing_limit_geom {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K D th c kmin dlt P0 P1 khat : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hth : 0 ≤ th) (hKth : K * th < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * th ^ n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember c kmin dlt (X n)) ∧
      (∀ n, Tendsto (pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n k, pullback B Q n k ∈
        TubeInvariance.tube (Q n) (D * th ^ n * (1 - K * th)⁻¹)) ∧
      (∀ n u, ‖(X n).1 u - (Q n).1 u‖ ≤ D * th ^ n * (1 - K * th)⁻¹) ∧
      (∀ n, dist (Q n) (X n) ≤ c2Const P0 P1 khat * (D * th ^ n * (1 - K * th)⁻¹)) ∧
      (∀ n, |perim (X n) - perim (Q n)|
        ≤ c2Const P0 P1 khat * (D * th ^ n * (1 - K * th)⁻¹)) := by
  have hKth0 : 0 ≤ K * th := mul_nonneg hK hth
  have hgeomsum : Summable fun k : ℕ => (K * th) ^ k :=
    summable_geometric_of_lt_one hKth0 hKth
  have hterm : ∀ n k : ℕ, K ^ k * d (n + k) ≤ D * th ^ n * (K * th) ^ k := by
    intro n k
    have h1 : d (n + k) ≤ D * th ^ (n + k) := hdgeo (n + k)
    have h2 : K ^ k * d (n + k) ≤ K ^ k * (D * th ^ (n + k)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hK k)
    calc K ^ k * d (n + k) ≤ K ^ k * (D * th ^ (n + k)) := h2
      _ = D * th ^ n * (K * th) ^ k := by rw [pow_add, mul_pow]; ring
  have hsum : ∀ n, Summable fun k => K ^ k * d (n + k) := by
    intro n
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg hK k) (hd _)) (hterm n)
      (hgeomsum.mul_left (D * th ^ n))
  have ha : ∀ n k, ∑ j ∈ Finset.range k, K ^ j * d (n + j)
      ≤ D * th ^ n * (1 - K * th)⁻¹ := by
    intro n k
    have hpref : 0 ≤ D * th ^ n := mul_nonneg hD (pow_nonneg hth n)
    have h1 : ∑ j ∈ Finset.range k, K ^ j * d (n + j)
        ≤ ∑ j ∈ Finset.range k, D * th ^ n * (K * th) ^ j :=
      Finset.sum_le_sum fun j _ => hterm n j
    have h2 : ∑ j ∈ Finset.range k, (K * th) ^ j ≤ (1 - K * th)⁻¹ := by
      have := hgeomsum.sum_le_tsum (Finset.range k) (fun j _ => by positivity)
      rwa [tsum_geometric_of_lt_one hKth0 hKth] at this
    calc ∑ j ∈ Finset.range k, K ^ j * d (n + j)
        ≤ ∑ j ∈ Finset.range k, D * th ^ n * (K * th) ^ j := h1
      _ = D * th ^ n * ∑ j ∈ Finset.range k, (K * th) ^ j := by rw [Finset.mul_sum]
      _ ≤ D * th ^ n * (1 - K * th)⁻¹ := mul_le_mul_of_nonneg_left h2 hpref
  exact exists_shadowing_limit_of_radii hK hsum ha hmap hdefect hmem hBcont

/-- **The exact inverse orbit is an orbit of the forward map.**  If the map `T`
undoes `B` — as the unit-tangent transform undoes the selected inverse — then
the orbit `Xₙ = B X_{n+1}` produced by the scheme satisfies `T Xₙ = X_{n+1}`. -/
theorem forward_orbit_of_inverse_orbit {B T : Data → Data} {X : ℕ → Data}
    (hTB : ∀ p, T (B p) = p) (hX : ∀ n, X n = B (X (n + 1))) (n : ℕ) :
    T (X n) = X (n + 1) := by
  rw [hX n, hTB]

end TubePullbackLimit
