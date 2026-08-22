import Mathlib
import UnitTangentIterates.MainThresholds

/-!
# The large-separation threshold

The lemma *Large-separation threshold* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* fixes one threshold `H_*` past which every ingredient of
the proof of the main theorem is available at every level of the cap sequence:

i.   `P` is strictly increasing, `P(H) ≤ H - Δ/2`, and the recursion
     `P(H_{n+1}) = H_n` has a unique solution, with `H_n ≥ H_0 + (Δ/2)n`;
iii. the synchronized tail satisfies `r_0 ≤ C(1+H_0)²e^{-βH_0} → 0`, so that
     `r_0 ≤ η_*` after increasing `H_*`;
iv.  `(2H_0 - C_sh r_0)/π > C_W + 2C_sh r_0`.

`UnitTangentIterates/MainThresholds.lean` contains the individual steps.  This file
assembles them into single statements, and adds the construction of the cap
sequence itself: from the asymptotics
`P(H) = H - Δ + O(e^{-βH})`, `P'(H) = 1 + O(e^{-βH})` of the proposition
*Exact two-cap pairs* (`UnitTangentIterates/PerimeterAsymptotics.lean`) it produces
a threshold `H_*` and, above it, the whole sequence `H_n`.

Main results:

* `exists_exp_threshold` : an exponentially small quantity is eventually below
  any positive level;
* `exists_threshold_asymptotics` : clause (i) — thresholds for `P' ≥ 1/2` and
  `P(H) ≤ H - Δ/2`, hence strict monotonicity;
* `exists_cap_sequence` : the recursion `P(H_{n+1}) = H_n` really defines a
  sequence, and it grows at least linearly;
* `antitoneOn_poly_exp`, `summable_poly_exp_shift`, `tail_estimate` : clause
  (iii) — the synchronized tail bound `∑ eₙ ≤ C(1+H_0)²e^{-βH_0}·C_tail`;
* `exists_large_separation_threshold` : the three clauses in one statement.
-/

noncomputable section

open Filter Real Set Topology

namespace LargeSeparation

/-! ### An exponentially small quantity is eventually small -/

/-- For every level `ε > 0` there is a threshold past which
`C e^{-βH} ≤ ε`. -/
theorem exists_exp_threshold {C beta eps : ℝ} (hbeta : 0 < beta) (heps : 0 < eps) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ H, Hs ≤ H → C * Real.exp (-beta * H) ≤ eps := by
  have h1 : Tendsto (fun H : ℝ => -beta * H) atTop atBot :=
    (tendsto_neg_atBot_iff.mpr (Filter.tendsto_id.const_mul_atTop hbeta)).congr
      (fun x => by simp [neg_mul])
  have h2 : Tendsto (fun H : ℝ => C * Real.exp (-beta * H)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp h1).const_mul C
    simpa using this
  have h3 := h2.eventually (gt_mem_nhds heps)
  rw [Filter.eventually_atTop] at h3
  obtain ⟨a, ha⟩ := h3
  exact ⟨max 0 a, le_max_left _ _, fun H hH => (ha H (le_trans (le_max_right _ _) hH)).le⟩

/-! ### Clause (i): the thresholds coming from the asymptotics -/

variable {P Pp : ℝ → ℝ} {Delta beta C : ℝ}

/-- **Clause (i) of the large-separation threshold.**  From the asymptotics
`P(H) = H - Δ + O(e^{-βH})` and `P'(H) = 1 + O(e^{-βH})` there is a threshold
`H_*` past which `P' ≥ 1/2` and `P(H) ≤ H - Δ/2`; in particular `P` is strictly
increasing on `[H_*, ∞)`. -/
theorem exists_threshold_asymptotics (hDelta : 0 < Delta) (hbeta : 0 < beta)
    (hd : ∀ H, HasDerivAt P (Pp H) H)
    (hP : ∀ H, |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, |Pp H - 1| ≤ C * Real.exp (-beta * H)) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ (∀ H, Hs ≤ H → 1 / 2 ≤ Pp H) ∧
      (∀ H, Hs ≤ H → P H ≤ H - Delta / 2) ∧ StrictMonoOn P (Ici Hs) := by
  obtain ⟨A, hA0, hA⟩ := exists_exp_threshold (C := C) hbeta (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨B, hB0, hB⟩ := exists_exp_threshold (C := C) hbeta (by linarith : (0:ℝ) < Delta / 2)
  refine ⟨max A B, le_trans hA0 (le_max_left _ _), ?_, ?_, ?_⟩
  · intro H hH
    have h1 := hA H (le_trans (le_max_left _ _) hH)
    have h2 := (abs_le.mp (hPp H)).1
    linarith
  · intro H hH
    have h1 := hB H (le_trans (le_max_right _ _) hH)
    have h2 := (abs_le.mp (hP H)).2
    linarith
  · refine MainThresholds.strictMonoOn_of_deriv_ge_half hd ?_
    intro H hH
    have h1 := hA H (le_trans (le_max_left _ _) hH)
    have h2 := (abs_le.mp (hPp H)).1
    linarith

/-! ### The cap sequence -/

/-- **Construction of the cap sequence.**  If `P' ≥ 1/2` and `P(H) ≤ H - Δ/2`
above `H_*`, then for every initial separation `H₀ ≥ H_*` the recursion
`P(H_{n+1}) = H_n` defines a sequence, which stays above `H_*` and grows at
least at rate `Δ/2`. -/
theorem exists_cap_sequence {Hs H0 : ℝ} (hDelta : 0 < Delta)
    (hd : ∀ H, HasDerivAt P (Pp H) H)
    (hPp : ∀ H, Hs ≤ H → 1 / 2 ≤ Pp H)
    (hPle : ∀ H, Hs ≤ H → P H ≤ H - Delta / 2)
    (hH0 : Hs ≤ H0) :
    ∃ H : ℕ → ℝ, H 0 = H0 ∧ (∀ n, Hs ≤ H n) ∧ (∀ n, P (H (n + 1)) = H n) ∧
      (∀ n : ℕ, H0 + Delta / 2 * n ≤ H n) := by
  -- one step of the recursion
  have step : ∀ t : ℝ, ∃ x : ℝ, Hs ≤ t → (Hs ≤ x ∧ P x = t) := by
    intro t
    by_cases ht : Hs ≤ t
    · have hPHs : P Hs ≤ t := by
        have := hPle Hs le_rfl
        linarith
      obtain ⟨x, hx, -⟩ := MainThresholds.existsUnique_recursion_step hd hPp hPHs
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose G hG using step
  set H : ℕ → ℝ := fun n => Nat.rec H0 (fun _ x => G x) n with hHdef
  have hstep : ∀ n, H (n + 1) = G (H n) := fun n => rfl
  have hmem : ∀ n, Hs ≤ H n := by
    intro n
    induction n with
    | zero => exact hH0
    | succ k ih =>
      rw [hstep k]
      exact (hG (H k) ih).1
  have hrec : ∀ n, P (H (n + 1)) = H n := by
    intro n
    rw [hstep n]
    exact (hG (H n) (hmem n)).2
  refine ⟨H, rfl, hmem, hrec, ?_⟩
  intro n
  have := MainThresholds.recursion_growth (P := P) (Hstar := Hs) (Delta := Delta)
    hPle hmem hrec n
  simpa using this

/-! ### Clause (iii): the synchronized tail -/

/-- The weight `x ↦ (1+x)²e^{-βx}` is decreasing once `β(1+x) ≥ 2`. -/
theorem antitoneOn_poly_exp (hbeta : 0 < beta) :
    AntitoneOn (fun x : ℝ => (1 + x) ^ 2 * Real.exp (-beta * x)) (Ici (2 / beta)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 + x) ^ 2 * Real.exp (-beta * x))
      ((2 * (1 + x) - beta * (1 + x) ^ 2) * Real.exp (-beta * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add (1:ℝ)).pow 2
      simpa using this
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-beta * x)) (-beta * Real.exp (-beta * x)) x := by
      have := ((hasDerivAt_id x).const_mul (-beta)).exp
      simpa [mul_comm] using this
    have := h1.mul h2
    convert this using 1
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (Continuous.continuousOn (by fun_prop))
  · intro x _
    exact ((hderiv x).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    have hx' : 2 / beta < x := hx
    have h2 : 2 < beta * x := by
      rw [div_lt_iff₀ hbeta] at hx'
      linarith
    have hxpos : 0 < x := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hfac : 2 * (1 + x) - beta * (1 + x) ^ 2 ≤ 0 := by nlinarith
    have hexp : 0 < Real.exp (-beta * x) := Real.exp_pos _
    exact mul_nonpos_of_nonpos_of_nonneg hfac hexp.le

/-- The shifted weights `(1+H₀+dn)²e^{-β(H₀+dn)}` are summable. -/
theorem summable_poly_exp_shift {d H0 : ℝ} (hd : 0 < d) (hbeta : 0 < beta) (hH0 : 0 ≤ H0) :
    Summable (fun n : ℕ => (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))) := by
  have hmaj : Summable (fun n : ℕ => (1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) :=
    MainThresholds.summable_weighted_geometric hd hbeta
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hmaj.mul_left
    ((1 + H0) ^ 2 * Real.exp (-beta * H0)))
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpoly : (1 + H0 + d * n) ^ 2 ≤ (1 + H0) ^ 2 * (1 + d * n) ^ 2 := by
    have hbase : 1 + H0 + d * n ≤ (1 + H0) * (1 + d * n) := by
      nlinarith [mul_nonneg (mul_nonneg hH0 hd.le) hn]
    have h0 : 0 ≤ 1 + H0 + d * n := by positivity
    calc (1 + H0 + d * n) ^ 2 ≤ ((1 + H0) * (1 + d * n)) ^ 2 := pow_le_pow_left₀ h0 hbase 2
      _ = (1 + H0) ^ 2 * (1 + d * n) ^ 2 := by rw [mul_pow]
  have hexp : Real.exp (-beta * (H0 + d * n))
      = Real.exp (-beta * H0) * Real.exp (-(beta * d) * n) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have hE : (0:ℝ) < Real.exp (-beta * H0) * Real.exp (-(beta * d) * n) := by positivity
  calc (1 + H0 + d * n) ^ 2 * (Real.exp (-beta * H0) * Real.exp (-(beta * d) * n))
      ≤ ((1 + H0) ^ 2 * (1 + d * n) ^ 2)
          * (Real.exp (-beta * H0) * Real.exp (-(beta * d) * n)) :=
        mul_le_mul_of_nonneg_right hpoly hE.le
    _ = (1 + H0) ^ 2 * Real.exp (-beta * H0) * ((1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) := by
        ring

/-- **Clause (iii): the synchronized tail estimate.**  If the defects satisfy
`0 ≤ eₙ ≤ C(1+Hₙ)²e^{-βHₙ}` along a sequence growing at least at rate `d` from
`H₀ ≥ 2/β`, then

`r₀ = ∑ₙ eₙ ≤ C(1+H₀)²e^{-βH₀}·C_tail(d, β)`. -/
theorem tail_estimate {e Hn : ℕ → ℝ} {d H0 : ℝ} (hd : 0 < d) (hbeta : 0 < beta)
    (hC : 0 ≤ C) (hstart : 2 / beta ≤ H0) (hH0 : 0 ≤ H0)
    (hgrow : ∀ n : ℕ, H0 + d * n ≤ Hn n)
    (he0 : ∀ n, 0 ≤ e n)
    (he : ∀ n, e n ≤ C * ((1 + Hn n) ^ 2 * Real.exp (-beta * Hn n))) :
    ∑' n, e n ≤ C * ((1 + H0) ^ 2 * Real.exp (-beta * H0)) * MainThresholds.tailConst d beta := by
  have hanti := antitoneOn_poly_exp (beta := beta) hbeta
  have hpoint : ∀ n : ℕ,
      e n ≤ C * ((1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))) := by
    intro n
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : H0 + d * n ∈ Ici (2 / beta) := by
      have : 0 ≤ d * n := by positivity
      exact mem_Ici.mpr (by linarith)
    have hy : Hn n ∈ Ici (2 / beta) := mem_Ici.mpr (le_trans hx (hgrow n))
    have := hanti hx hy (hgrow n)
    have hmul := mul_le_mul_of_nonneg_left this hC
    have : C * ((1 + (H0 + d * n)) ^ 2 * Real.exp (-beta * (H0 + d * n)))
        = C * ((1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))) := by ring_nf
    rw [← this]
    exact le_trans (he n) (by simpa using hmul)
  have hmajsum : Summable (fun n : ℕ =>
      C * ((1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n)))) :=
    (summable_poly_exp_shift hd hbeta hH0).mul_left C
  have hsum : Summable e := Summable.of_nonneg_of_le he0 hpoint hmajsum
  calc ∑' n, e n ≤ ∑' n : ℕ, C * ((1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))) :=
        hsum.tsum_le_tsum hpoint hmajsum
    _ = C * ∑' n : ℕ, (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n)) := by
        rw [tsum_mul_left]
    _ ≤ C * ((1 + H0) ^ 2 * Real.exp (-beta * H0) * MainThresholds.tailConst d beta) :=
        mul_le_mul_of_nonneg_left (MainThresholds.tail_bound hd hbeta hH0) hC
    _ = C * ((1 + H0) ^ 2 * Real.exp (-beta * H0)) * MainThresholds.tailConst d beta := by ring

/-! ### The three clauses in one statement -/

/-- **The large-separation threshold.**  Assume the asymptotics
`P(H) = H - Δ + O(e^{-βH})`, `P'(H) = 1 + O(e^{-βH})` of *Exact two-cap pairs*,
a level `η_* > 0` below which the shadowing theorem applies, and constants
`C_W`, `C_sh` of *Uniform transverse width* and of the shadowing estimate,
where the tail is measured by `r(H₀) = C_r(1+H₀)²e^{-β'H₀}`.  Then there is a
threshold `H_*` such that every initial separation `H₀ ≥ H_*` satisfies:

i.   `P' ≥ 1/2` and `P(H) ≤ H - Δ/2` above `H₀`, `P` is strictly increasing
     there, and the recursion `P(H_{n+1}) = H_n` defines a sequence with
     `H_n ≥ H₀ + (Δ/2)n`;
iii. `r(H₀) ≤ η_*`;
iv.  `(2H₀ - C_sh r(H₀))/π > C_W + 2C_sh r(H₀)`. -/
theorem exists_large_separation_threshold {Cr beta' eta Cw Csh : ℝ}
    (hDelta : 0 < Delta) (hbeta : 0 < beta) (hbeta' : 0 < beta') (heta : 0 < eta)
    (hd : ∀ H, HasDerivAt P (Pp H) H)
    (hP : ∀ H, |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, |Pp H - 1| ≤ C * Real.exp (-beta * H)) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ H0, Hs ≤ H0 →
      ((∀ H, H0 ≤ H → 1 / 2 ≤ Pp H ∧ P H ≤ H - Delta / 2) ∧
        StrictMonoOn P (Ici H0) ∧
        ∃ H : ℕ → ℝ, H 0 = H0 ∧ (∀ n, H0 ≤ H n) ∧ (∀ n, P (H (n + 1)) = H n) ∧
          (∀ n : ℕ, H0 + Delta / 2 * n ≤ H n)) ∧
      Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)) ≤ eta ∧
      Cw + 2 * Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))
        < (2 * H0 - Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))) / Real.pi := by
  obtain ⟨A, hA0, hA1, hA2, -⟩ := exists_threshold_asymptotics hDelta hbeta hd hP hPp
  -- the tail is eventually below `η_*` and eventually gives the width gap
  set r : ℝ → ℝ := fun x => Cr * ((1 + x) ^ 2 * Real.exp (-beta' * x)) with hr
  have hrzero : Tendsto r atTop (𝓝 0) := by
    have := (MainThresholds.tendsto_tail_zero (beta := beta') hbeta').const_mul Cr
    simpa [hr] using this
  have hsmall : ∀ᶠ x in atTop, r x ≤ eta := by
    have := hrzero.eventually (gt_mem_nhds heta)
    filter_upwards [this] with x hx using hx.le
  have hgap : ∀ᶠ x in atTop, Cw + 2 * Csh * r x < (2 * x - Csh * r x) / Real.pi :=
    MainThresholds.eventually_width_gap (Cw := Cw) (Csh := Csh) hrzero
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp (hsmall.and hgap)
  refine ⟨max A (max B 0), le_trans (le_max_right B 0) (le_max_right A _), ?_⟩
  intro H0 hH0
  have hAH0 : A ≤ H0 := le_trans (le_max_left _ _) hH0
  have hBH0 : B ≤ H0 := le_trans (le_trans (le_max_left B 0) (le_max_right A _)) hH0
  obtain ⟨hsm, hgp⟩ := hB H0 hBH0
  refine ⟨⟨fun H hH => ⟨hA1 H (le_trans hAH0 hH), hA2 H (le_trans hAH0 hH)⟩, ?_, ?_⟩, hsm, hgp⟩
  · refine MainThresholds.strictMonoOn_of_deriv_ge_half hd ?_
    intro H hH
    exact hA1 H (le_trans hAH0 hH)
  · exact exists_cap_sequence hDelta hd (fun H hH => hA1 H (le_trans hAH0 hH))
      (fun H hH => hA2 H (le_trans hAH0 hH)) le_rfl

end LargeSeparation
