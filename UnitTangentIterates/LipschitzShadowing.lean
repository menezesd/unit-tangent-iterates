import Mathlib
import UnitTangentIterates.ShadowingTails

/-!
# Backward shadowing for a Lipschitz selected inverse

`MarkedSpace.exists_canonical_marked_orbit` (and its wrapper
`SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`) proves
backward shadowing under the hypothesis

```
  ∀ p q, dist (𝔅 p) (𝔅 q) ≤ dist p q,
```

non-expansiveness in the marked `C²` metric.  **The paper does not prove that.**
Its lemma *Inverse Jacobi estimates* proves `W(𝔅Γ) ≤ W(Γ)` — non-expansiveness of
the `L¹` functional alone — together with *gains* for `S₀, S₁, S₂`; the marked
distance is an infimum of costs controlling all of `W, S₀, S₁, S₂`, so
non-expansiveness of the metric does not follow.  What the Lean development does
prove for the marked metric is a Lipschitz bound with an explicit but large
constant (`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist`).

That is enough.  The defects of the paper's pseudo-orbit decay *exponentially*:
`eₙ ≤ C(1+Hₙ)²e^{-βH_{n+1}}` with `Hₙ ≥ H₀ + (Δ/2)n` (lemma *Large-separation
threshold*), so `∑ Lⁿeₙ` converges for any fixed `L` once `H₀` is large.  This
file proves backward shadowing under exactly that pair of hypotheses, replacing
an assumption the paper does not establish by two that it does.

Taking `L = 1` recovers the non-expansive statement, so nothing is lost.

Main results: `dist_iterate_le`, `exists_shadowing_orbit_of_lipschitz`.
-/

noncomputable section

open Filter Topology

namespace LipschitzShadowing

variable {M : Type*} [MetricSpace M]

/-- A Lipschitz map iterates with the powers of its constant. -/
theorem dist_iterate_le {B : M → M} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ p q, dist (B p) (B q) ≤ L * dist p q) :
    ∀ (N : ℕ) (p q : M), dist ((B^[N]) p) ((B^[N]) q) ≤ L ^ N * dist p q := by
  intro N
  induction N with
  | zero => intro p q; simp
  | succ N ih =>
      intro p q
      have hstep : dist ((B^[N]) (B p)) ((B^[N]) (B q))
          ≤ L ^ N * dist (B p) (B q) := ih (B p) (B q)
      have h2 : L ^ N * dist (B p) (B q) ≤ L ^ N * (L * dist p q) :=
        mul_le_mul_of_nonneg_left (hlip p q) (by positivity)
      have hcomm : (B^[N + 1]) p = (B^[N]) (B p) := by
        rw [Function.iterate_succ_apply]
      have hcomm' : (B^[N + 1]) q = (B^[N]) (B q) := by
        rw [Function.iterate_succ_apply]
      rw [hcomm, hcomm']
      calc dist ((B^[N]) (B p)) ((B^[N]) (B q)) ≤ L ^ N * dist (B p) (B q) := hstep
        _ ≤ L ^ N * (L * dist p q) := h2
        _ = L ^ (N + 1) * dist p q := by ring

variable [CompleteSpace M]

/-- **Backward shadowing for a Lipschitz selected inverse.**  If `𝔅` is
`L`-Lipschitz with a left inverse `T`, and the defects of the pseudo-orbit
satisfy `∑ Lⁿeₙ < ∞`, then the terminal pullbacks converge to an exact orbit of
`T`, with the tail estimate.

With `L = 1` this is the non-expansive statement; the point of the generality is
that the paper proves a Lipschitz bound and exponentially decaying defects, but
not non-expansiveness. -/
theorem exists_shadowing_orbit_of_lipschitz (T B : M → M) {L : ℝ} (hL : 0 < L)
    (hTB : ∀ q, T (B q) = q)
    (hlip : ∀ p q, dist (B p) (B q) ≤ L * dist p q)
    (Q : ℕ → M) (e : ℕ → ℝ)
    (hsum : Summable fun m => L ^ m * e m)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M, (∀ n, X (n + 1) = T (X n)) ∧
      ∀ n, Tendsto (fun N => (B^[N]) (Q (n + N))) atTop (𝓝 (X n)) := by
  have hBcont : Continuous B := by
    refine Metric.continuous_iff.2 fun p ε hε => ?_
    refine ⟨ε / L, by positivity, fun q hq => ?_⟩
    calc dist (B q) (B p) ≤ L * dist q p := hlip q p
      _ < L * (ε / L) := by exact mul_lt_mul_of_pos_left hq hL
      _ = ε := by field_simp
  have hstep : ∀ n N,
      dist ((B^[N]) (Q (n + N))) ((B^[N + 1]) (Q (n + (N + 1))))
        ≤ L ^ N * e (n + N) := by
    intro n N
    have hiter : (B^[N + 1]) (Q (n + (N + 1)))
        = (B^[N]) (B (Q (n + (N + 1)))) := Function.iterate_succ_apply B N _
    rw [hiter]
    refine le_trans (dist_iterate_le hL.le hlip N _ _) ?_
    exact mul_le_mul_of_nonneg_left (hdef (n + N)) (by positivity)
  have hsummable : ∀ n, Summable fun N => L ^ N * e (n + N) := by
    intro n
    have h : Summable fun N => L ^ (N + n) * e (N + n) :=
      (summable_nat_add_iff n).mpr hsum
    have h' : Summable fun N => (L ^ n)⁻¹ * (L ^ (N + n) * e (N + n)) :=
      h.mul_left _
    refine h'.congr fun N => ?_
    have hne : (L : ℝ) ^ n ≠ 0 := by positivity
    rw [pow_add, Nat.add_comm N n]
    field_simp
  have hcauchy : ∀ n, CauchySeq fun N => (B^[N]) (Q (n + N)) := by
    intro n
    refine cauchySeq_of_summable_dist ?_
    exact Summable.of_nonneg_of_le (fun _ => dist_nonneg) (fun N => hstep n N)
      (hsummable n)
  choose X hX using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  refine ⟨X, fun n => ?_, hX⟩
  have hshift : Tendsto (fun N => (B^[N + 1]) (Q (n + (N + 1)))) atTop (𝓝 (X n)) :=
    (hX n).comp (tendsto_add_atTop_nat 1)
  have hBX : Tendsto (fun N => B ((B^[N]) (Q (n + 1 + N)))) atTop
      (𝓝 (B (X (n + 1)))) :=
    (hBcont.tendsto (X (n + 1))).comp (hX (n + 1))
  have heq : (fun N => B ((B^[N]) (Q (n + 1 + N))))
      = fun N => (B^[N + 1]) (Q (n + (N + 1))) := by
    funext N
    have hidx : n + 1 + N = n + (N + 1) := by omega
    rw [hidx, Function.iterate_succ_apply']
  rw [heq] at hBX
  have hBXn : B (X (n + 1)) = X n := tendsto_nhds_unique hBX hshift
  rw [← hBXn, hTB]

/-- **The non-expansive statement is the case `L = 1`.**  So nothing is lost by
working with the Lipschitz hypothesis: it strictly generalizes
`SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`, while
being satisfiable from what the paper actually proves. -/
theorem exists_shadowing_orbit_of_nonexpansive (T B : M → M)
    (hTB : ∀ q, T (B q) = q)
    (hne : ∀ p q, dist (B p) (B q) ≤ dist p q)
    (Q : ℕ → M) (e : ℕ → ℝ) (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n) :
    ∃ X : ℕ → M, (∀ n, X (n + 1) = T (X n)) ∧
      ∀ n, Tendsto (fun N => (B^[N]) (Q (n + N))) atTop (𝓝 (X n)) := by
  refine exists_shadowing_orbit_of_lipschitz T B one_pos hTB ?_ Q e ?_ hdef
  · intro p q
    simpa using hne p q
  · simpa using hsum

end LipschitzShadowing
