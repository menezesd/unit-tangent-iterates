import Mathlib

/-!
# Exponential periodization

This file formalizes the basic case of Lemma 4.1 (*Exponential periodization*)
of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

If `z ≥ 0` decays exponentially, `z(s) ≤ C e^{-a|s|}`, and
`Z_H(s) = ∑_{m ∈ ℤ} z(s - mH)` is its `H`-periodization, then on the
fundamental interval `|s| ≤ H/2` the periodization differs from `z` itself by
at most `4C e^{-aH/2}`.

Main results:

* `summable_periodization` : the periodized series converges;
* `periodization_error_le` : the exponential bound
  `|Z_H(s) - z(s)| ≤ 4 C e^{-(a/2) H}` on the fundamental interval.
-/

noncomputable section

open Real

namespace Periodization

variable {z : ℝ → ℝ} {C a H s : ℝ}

/-- The constant in an exponential majorant is nonnegative. -/
lemma const_nonneg (hz : ∀ s, 0 ≤ z s) (hzb : ∀ s, z s ≤ C * Real.exp (-a * |s|)) :
    0 ≤ C := by
  have h := hzb 0
  have h0 := hz 0
  simp at h
  linarith

/-- Off the central term, the translates of an exponentially decaying pulse are
geometrically small on the fundamental interval. -/
lemma term_le (ha : 0 < a) (hz : ∀ s, 0 ≤ z s)
    (hzb : ∀ s, z s ≤ C * Real.exp (-a * |s|))
    (hH : 0 < H) (hs : |s| ≤ H / 2) (m : ℤ) :
    z (s - m * H) ≤ (C * Real.exp (a * H / 2)) * (Real.exp (-a * H)) ^ (m.natAbs) := by
  have hC : 0 ≤ C := const_nonneg hz hzb
  have habs : ((m.natAbs : ℝ)) * H - H / 2 ≤ |s - m * H| := by
    have h1 : |(m : ℝ) * H| - |s| ≤ |(m : ℝ) * H - s| := abs_sub_abs_le_abs_sub _ _
    have h2 : |(m : ℝ) * H - s| = |s - (m : ℝ) * H| := abs_sub_comm _ _
    have h3 : |(m : ℝ) * H| = (m.natAbs : ℝ) * H := by
      rw [abs_mul, abs_of_pos hH]
      congr 1
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [h2, h3] at h1
    linarith
  calc z (s - m * H) ≤ C * Real.exp (-a * |s - m * H|) := hzb _
    _ ≤ C * Real.exp (-a * ((m.natAbs : ℝ) * H - H / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = (C * Real.exp (a * H / 2)) * (Real.exp (-a * H)) ^ (m.natAbs) := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        ring_nf

/-- The geometric majorant of the translates. -/
noncomputable def majorant (C a H : ℝ) (m : ℤ) : ℝ :=
  (C * Real.exp (a * H / 2)) * (Real.exp (-a * H)) ^ (m.natAbs)

lemma summable_majorant (ha : 0 < a) (hH : 0 < H) : Summable (majorant C a H) := by
  have hq0 : (0:ℝ) ≤ Real.exp (-a * H) := (Real.exp_pos _).le
  have hq1 : Real.exp (-a * H) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have hgeo : Summable (fun n : ℕ => Real.exp (-a * H) ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa [majorant] using hgeo.mul_left (C * Real.exp (a * H / 2))
  · have hsum : Summable (fun n : ℕ => (C * Real.exp (a * H / 2)) * Real.exp (-a * H) ^ (n + 1)) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using
        (hgeo.mul_left ((C * Real.exp (a * H / 2)) * Real.exp (-a * H)))
    have hfun : (fun n : ℕ => majorant C a H (-((n : ℤ) + 1)))
        = fun n : ℕ => (C * Real.exp (a * H / 2)) * Real.exp (-a * H) ^ (n + 1) := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [majorant, hn]
    rw [hfun]
    exact hsum

/-- The periodized series converges. -/
theorem summable_periodization (ha : 0 < a) (hz : ∀ s, 0 ≤ z s)
    (hzb : ∀ s, z s ≤ C * Real.exp (-a * |s|))
    (hH : 0 < H) (hs : |s| ≤ H / 2) :
    Summable (fun m : ℤ => z (s - m * H)) :=
  Summable.of_nonneg_of_le (fun _ => hz _) (fun m => term_le ha hz hzb hH hs m)
    (summable_majorant ha hH)

/-! ### The two-sided geometric tail -/

/-- Summability of the punctured geometric series over `ℕ`. -/
lemma summable_ite_geom_nat {C' q : ℝ} (hC' : 0 ≤ C') (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => if n = 0 then (0:ℝ) else C' * q ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C')
  · split_ifs with h
    · exact le_refl 0
    · positivity
  · split_ifs with h
    · positivity
    · exact le_refl _

/-- Value of the punctured geometric series over `ℕ`. -/
lemma tsum_ite_geom_nat {C' q : ℝ} (hC' : 0 ≤ C') (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, (if n = 0 then (0:ℝ) else C' * q ^ n) = C' * q * (1 - q)⁻¹ := by
  rw [(summable_ite_geom_nat hC' hq0 hq1).tsum_eq_zero_add]
  have h : (fun b : ℕ => if b + 1 = 0 then (0:ℝ) else C' * q ^ (b + 1))
      = fun b : ℕ => (C' * q) * q ^ b := by
    funext b
    rw [if_neg (Nat.succ_ne_zero b)]
    ring
  rw [h, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  simp

lemma ite_geom_nat_shape (C' q : ℝ) :
    (fun n : ℕ => if (n : ℤ) = 0 then (0:ℝ) else C' * q ^ ((n : ℤ)).natAbs)
      = fun n : ℕ => if n = 0 then (0:ℝ) else C' * q ^ n := by
  funext n
  cases n with
  | zero => simp
  | succ k =>
    have h1 : ((k + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    rw [if_neg h1, if_neg (Nat.succ_ne_zero k)]
    congr 1

lemma ite_geom_neg_shape (C' q : ℝ) :
    (fun n : ℕ => if (-((n : ℤ) + 1)) = 0 then (0:ℝ)
        else C' * q ^ ((-((n : ℤ) + 1))).natAbs)
      = fun n : ℕ => (C' * q) * q ^ n := by
  funext n
  have hne : (-((n : ℤ) + 1)) ≠ 0 := by omega
  have hna : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [if_neg hne, hna]
  ring

/-- Summability of the two-sided punctured geometric series over `ℤ`. -/
lemma summable_ite_geom_int {C' q : ℝ} (hC' : 0 ≤ C') (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => if m = 0 then (0:ℝ) else C' * q ^ m.natAbs) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · rw [ite_geom_nat_shape]
    exact summable_ite_geom_nat hC' hq0 hq1
  · rw [ite_geom_neg_shape]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _

/-- Value of the two-sided punctured geometric series over `ℤ`. -/
lemma tsum_ite_geom_int {C' q : ℝ} (hC' : 0 ≤ C') (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' m : ℤ, (if m = 0 then (0:ℝ) else C' * q ^ m.natAbs) = 2 * (C' * q * (1 - q)⁻¹) := by
  rw [tsum_of_nat_of_neg_add_one
    (f := fun m : ℤ => if m = 0 then (0:ℝ) else C' * q ^ m.natAbs)
    (by rw [ite_geom_nat_shape]; exact summable_ite_geom_nat hC' hq0 hq1)
    (by rw [ite_geom_neg_shape]; exact (summable_geometric_of_lt_one hq0 hq1).mul_left _)]
  rw [ite_geom_nat_shape, ite_geom_neg_shape, tsum_ite_geom_nat hC' hq0 hq1,
    tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  ring

/-- **Exponential periodization.**  On the fundamental interval `|s| ≤ H/2`,
the periodization `Z_H` differs from the isolated pulse `z` by at most
`4C e^{-(a/2)H}`, provided `e^{-aH} ≤ 1/2`. -/
theorem periodization_error_le (ha : 0 < a) (hz : ∀ s, 0 ≤ z s)
    (hzb : ∀ s, z s ≤ C * Real.exp (-a * |s|))
    (hH : 0 < H) (hq : Real.exp (-a * H) ≤ 1 / 2) (hs : |s| ≤ H / 2) :
    |(∑' m : ℤ, z (s - m * H)) - z s| ≤ 4 * C * Real.exp (-(a / 2) * H) := by
  have hC : 0 ≤ C := const_nonneg hz hzb
  set C' : ℝ := C * Real.exp (a * H / 2) with hC'
  set q : ℝ := Real.exp (-a * H) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hC'0 : 0 ≤ C' := by positivity
  have hsum : Summable (fun m : ℤ => z (s - m * H)) := summable_periodization ha hz hzb hH hs
  -- split off the central term
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : ℤ)
  have hz0 : z (s - ((0 : ℤ) : ℝ) * H) = z s := by norm_num
  rw [hz0] at hsplit
  have hdiff : (∑' m : ℤ, z (s - m * H)) - z s
      = ∑' m : ℤ, (if m = 0 then 0 else z (s - m * H)) := by
    rw [hsplit]; ring
  -- the tail is dominated by a two-sided geometric series
  have hwnn : ∀ m : ℤ, 0 ≤ (if m = 0 then 0 else z (s - m * H)) := by
    intro m
    split_ifs with h
    · exact le_refl 0
    · exact hz _
  have hwle : ∀ m : ℤ, (if m = 0 then 0 else z (s - m * H))
      ≤ (if m = 0 then 0 else C' * q ^ m.natAbs) := by
    intro m
    split_ifs with h
    · exact le_refl 0
    · exact term_le ha hz hzb hH hs m
  have hmajsum : Summable (fun m : ℤ => (if m = 0 then 0 else C' * q ^ m.natAbs)) :=
    summable_ite_geom_int hC'0 hq0 hq1
  have hwsum : Summable (fun m : ℤ => (if m = 0 then 0 else z (s - m * H))) :=
    Summable.of_nonneg_of_le hwnn hwle hmajsum
  have hle : (∑' m : ℤ, (if m = 0 then 0 else z (s - m * H)))
      ≤ ∑' m : ℤ, (if m = 0 then 0 else C' * q ^ m.natAbs) :=
    hwsum.tsum_le_tsum hwle hmajsum
  rw [hdiff, abs_of_nonneg (tsum_nonneg hwnn)]
  refine hle.trans ?_
  rw [tsum_ite_geom_int hC'0 hq0 hq1]
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hC'q : C' * q = C * Real.exp (-(a / 2) * H) := by
    rw [hC', hqdef, mul_assoc, ← Real.exp_add]
    ring_nf
  have hexp : 0 ≤ C * Real.exp (-(a / 2) * H) := by positivity
  calc 2 * (C' * q * (1 - q)⁻¹) = 2 * ((C' * q) * (1 - q)⁻¹) := by ring
    _ ≤ 2 * ((C' * q) * 2) := by
        have hstep : (C' * q) * (1 - q)⁻¹ ≤ (C' * q) * 2 := by
          apply mul_le_mul_of_nonneg_left hinv
          rw [hC'q]; exact hexp
        linarith
    _ = 4 * C * Real.exp (-(a / 2) * H) := by rw [hC'q]; ring

end Periodization
