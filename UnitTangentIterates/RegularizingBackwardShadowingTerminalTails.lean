import UnitTangentIterates.PathMetricRescale
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.TubePullbackLimit

/-!
# Terminal tail paths for regularizing backward shadowing

The completeness argument naturally supplies a sequence of normal paths
between consecutive terminal pullbacks.  This file records the strongest
path-valued conclusion available without an additional infinite-concatenation
construction: every finite terminal tail has an explicit concatenated path,
its endpoint tends to the shadowing limit, and its paper functionals satisfy
the required uniform tail estimates.

The endpoint of `path N k` is `p (N+k)`, not the limiting curve itself.  Thus
this module deliberately does not claim the stronger TeX assertion that the
countable concatenation extends to a `NormalPath` ending at the limit.
-/

noncomputable section

open Filter Topology
open MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace RegularizingBackwardShadowingTerminalTails

variable {p : ℕ → MarkedSpace.Data}

/-- Existence of the first `k` concatenated links, with exact additive cost. -/
theorem exists_finiteConcat
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    ∃ A : NormalPath (p N) (p (N + k)),
      cost A = ∑ j ∈ Finset.range k, cost (step (N + j)) := by
  induction k with
  | zero =>
      exact ⟨NormalPath.const (p N), by simp⟩
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      have hcost : cost (A.concat (step (N + k))) =
          ∑ j ∈ Finset.range (k + 1), cost (step (N + j)) := by
        rw [cost_concat, hA, Finset.sum_range_succ]
      simpa [Nat.add_assoc] using ⟨A.concat (step (N + k)), hcost⟩

/-- A chosen concatenation of the first `k` links beginning at `p N`. -/
noncomputable def finiteConcat
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    NormalPath (p N) (p (N + k)) :=
  Classical.choose (exists_finiteConcat step N k)

@[simp] theorem cost_finiteConcat
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    cost (finiteConcat step N k) =
      ∑ j ∈ Finset.range k, cost (step (N + j)) :=
  Classical.choose_spec (exists_finiteConcat step N k)

/-- The finite concatenation, rerun on `[0,1]` without changing its cost. -/
noncomputable def unitFiniteConcat
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    NormalPath (p N) (p (N + k)) :=
  (finiteConcat step N k).rescale (finiteConcat step N k).T_pos

@[simp] theorem unitFiniteConcat_time
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    (unitFiniteConcat step N k).T = 1 := by
  simp [unitFiniteConcat, NormalPath.T_rescale,
    div_self (ne_of_gt (finiteConcat step N k).T_pos)]

@[simp] theorem cost_unitFiniteConcat
    (step : ∀ j, NormalPath (p j) (p (j + 1))) (N k : ℕ) :
    cost (unitFiniteConcat step N k) =
      ∑ j ∈ Finset.range k, cost (step (N + j)) := by
  rw [unitFiniteConcat, NormalPath.cost_rescale, cost_finiteConcat]

/-- A completed terminal tail is represented by all of its finite normal-path
concatenations together with convergence of their terminal endpoints. -/
structure CompletedTail
    (step : ∀ j, NormalPath (p j) (p (j + 1)))
    (limit : MarkedSpace.Data) (major : ℕ → ℝ) where
  endpoint_tendsto : Tendsto p atTop (nhds limit)
  cost_le : ∀ N k, ∑ j ∈ Finset.range k, cost (step (N + j)) ≤ major N

namespace CompletedTail

variable {step : ∀ j, NormalPath (p j) (p (j + 1))}
  {limit : MarkedSpace.Data} {major : ℕ → ℝ}

/-- The explicit finite concatenated terminal path. -/
noncomputable def path (H : CompletedTail step limit major) (N k : ℕ) :
    NormalPath (p N) (p (N + k)) :=
  unitFiniteConcat step N k

@[simp] theorem path_time (H : CompletedTail step limit major) (N k : ℕ) :
    (H.path N k).T = 1 :=
  unitFiniteConcat_time step N k

theorem path_cost_le (H : CompletedTail step limit major) (N k : ℕ) :
    cost (H.path N k) ≤ major N := by
  rw [path, cost_unitFiniteConcat]
  exact H.cost_le N k

/-- The terminal endpoints of the finite concatenations converge to the
shadowing limit. -/
theorem path_endpoint_tendsto (H : CompletedTail step limit major) (N : ℕ) :
    Tendsto (fun k => p (N + k)) atTop (nhds limit) := by
  simpa [Nat.add_comm] using
    H.endpoint_tendsto.comp (Filter.tendsto_add_atTop_nat N)

/-- Paper clause `eq:shadow-terminal-tail-low`, with the sharp factor `2`
coming from bounding `S₀` and `S₁` separately by the path cost. -/
theorem terminal_tail_low (H : CompletedTail step limit major) (N k : ℕ) :
    S 0 (H.path N k).eta + S 1 (H.path N k).eta ≤ 2 * major N := by
  have h0 := (H.path N k).S_le_cost (H.path_time N k) (j := 0) (by omega)
  have h1 := (H.path N k).S_le_cost (H.path_time N k) (j := 1) (by omega)
  have hc := H.path_cost_le N k
  linarith

/-- Paper clause `eq:shadow-terminal-tail` for every finite terminal tail. -/
theorem terminal_tail_two (H : CompletedTail step limit major) (N k : ℕ) :
    S 2 (H.path N k).eta ≤ major N :=
  ((H.path N k).S_le_cost (H.path_time N k) (j := 2) (by omega)).trans
    (H.path_cost_le N k)

end CompletedTail

/-- Build the completed finite-tail system from a summable pointwise cost
majorant. -/
theorem completedTail_of_summable
    (step : ∀ j, NormalPath (p j) (p (j + 1)))
    (limit : MarkedSpace.Data) (b : ℕ → ℝ)
    (hlim : Tendsto p atTop (nhds limit))
    (hcost : ∀ j, cost (step j) ≤ b j)
    (hb0 : ∀ j, 0 ≤ b j) (hbsum : Summable b) :
    CompletedTail step limit (ShadowingTails.tail b) := by
  refine ⟨hlim, fun N k => ?_⟩
  calc
    ∑ j ∈ Finset.range k, cost (step (N + j))
        ≤ ∑ j ∈ Finset.range k, b (N + j) :=
          Finset.sum_le_sum fun j _ => hcost (N + j)
    _ ≤ ShadowingTails.tail b N := by
      simpa [ShadowingTails.tail, Nat.add_comm] using
        (ShadowingTails.summable_shift hbsum N).sum_le_tsum
          (Finset.range k) (fun j _ => hb0 (N + j))

/-! ### Terminal tails for the pullback shadowing construction -/

open NormalPathC2Increment TubePullbackLimit

/-- The pullback shadowing theorem with its propagated paths retained.

For each fixed row `n`, `step n k` joins consecutive terminal pullbacks and
`tails n` supplies all unit-time finite concatenations beginning at an
arbitrary terminal depth `N`.  Their endpoints tend to `X n`, and
`CompletedTail.terminal_tail_low` / `terminal_tail_two` give the two terminal
tail inequalities. -/
theorem exists_shadowing_with_completedTails
    {B : MarkedSpace.Data → MarkedSpace.Data}
    {Q : ℕ → MarkedSpace.Data} {d a : ℕ → ℝ}
    {K c kmin dlt P0 P1 khat : ℝ}
    (hK : 0 ≤ K)
    (hsum : ∀ n, Summable fun k => K ^ k * d (n + k))
    (ha : ∀ n k, ∑ j ∈ Finset.range k, K ^ j * d (n + j) ≤ a n)
    (hmap : ∀ (p q : MarkedSpace.Data) (Gamma : NormalPath p q),
      IsConstantSpeedNormalPath P0 P1 khat Gamma →
      ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma ∧
        IsConstantSpeedNormalPath P0 P1 khat Delta)
    (hdefect : ∀ n, ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
      cost Lambda ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Lambda)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, IsTubeMember c kmin dlt (X n)) ∧
      (∀ n, Tendsto (pullback B Q n) atTop (nhds (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      ∃ step : ∀ n k,
          NormalPath (pullback B Q n k) (pullback B Q n (k + 1)),
        (∀ n k, cost (step n k) ≤ K ^ k * d (n + k)) ∧
        (∀ n k, IsConstantSpeedNormalPath P0 P1 khat (step n k)) ∧
        (∀ n, CompletedTail (step n) (X n)
          (ShadowingTails.tail fun k => K ^ k * d (n + k))) := by
  obtain ⟨X, hXmem, hXlim, hXinv, -, -, -, -⟩ :=
    TubePullbackLimit.exists_shadowing_limit_of_radii
      hK hsum ha hmap hdefect hmem hBcont
  choose step hstepCost hstepGeom using fun n k =>
    TubePullbackLimit.exists_step_path
      (Q := Q) (d := d) hK hmap hdefect n k
  refine ⟨X, hXmem, hXlim, hXinv, step, hstepCost, hstepGeom, fun n => ?_⟩
  exact completedTail_of_summable (step n) (X n)
    (fun k => K ^ k * d (n + k)) (hXlim n) (hstepCost n)
    (fun k => (step n k).cost_nonneg.trans (hstepCost n k)) (hsum n)

end RegularizingBackwardShadowingTerminalTails
