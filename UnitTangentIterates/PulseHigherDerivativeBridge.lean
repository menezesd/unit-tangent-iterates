import Mathlib
import UnitTangentIterates.ShiftedCurvatureJetMajorant
import UnitTangentIterates.PulseFourthTermBounds

/-!
# Canonical/expanded higher pulse derivative bridge

This module keeps the analytic chain-rule hypotheses separate from the scalar
majorant calculation.  In particular, the inverse front-arclength coordinate
is required to have derivative `1 / sqrt (1 + K²)`.
-/

noncomputable section

namespace PulseHigherDerivativeBridge

open ShiftedCurvatureJetMajorant

private theorem abs_div_pow_le_abs {a q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    |a / q ^ n| ≤ |a| := by
  rw [abs_div, abs_pow, abs_of_nonneg (le_trans zero_le_one hq)]
  have hpow : 1 ≤ q ^ n := one_le_pow₀ hq
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow)]
  nlinarith [abs_nonneg a]

/-- The explicit third pulse formula has the paper's relative bound directly
from a nonnegative curvature ceiling and relative bounds for its first three
rear-arclength derivatives. -/
theorem rel_pulseDDDExpanded
    {K K1 K2 K3 x : ℝ → ℝ} {B D1 D2 D3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hK1 : RelMajorant K K1 D1)
    (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3) :
    RelMajorant (fun s => K (x s)) (pulseDDDExpanded K K1 K2 K3 x)
      (pulseThirdConstant B D1 D2 D3) := by
  intro s
  have hgoal : pulseDDDExpanded K K1 K2 K3 x s
      = K3 (x s) / (1 + K (x s) ^ 2) ^ 3
        - (13 * K (x s) * K1 (x s) * K2 (x s) + 4 * K1 (x s) ^ 3)
            / (1 + K (x s) ^ 2) ^ 4
        + 28 * K (x s) ^ 2 * K1 (x s) ^ 3 / (1 + K (x s) ^ 2) ^ 5 := rfl
  rw [hgoal]
  set k := K (x s) with hkdef
  set k1 := K1 (x s) with hk1def
  set k2 := K2 (x s) with hk2def
  set k3 := K3 (x s) with hk3def
  have hk0 : 0 ≤ k := hK0 (x s)
  have hkB : k ≤ B := hKB (x s)
  have h1 : |k1| ≤ D1 * k := hK1 (x s)
  have h2 : |k2| ≤ D2 * k := hK2 (x s)
  have h3 : |k3| ≤ D3 * k := hK3 (x s)
  have hkabs : |k| = k := abs_of_nonneg hk0
  have hq : (1 : ℝ) ≤ 1 + k ^ 2 := by nlinarith [sq_nonneg k]
  have hkk : k * k ≤ B * B := mul_le_mul hkB hkB hk0 (hk0.trans hkB)
  have hk4 : k ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hk0 hkB 4
  have ht0 : |k3 / (1 + k ^ 2) ^ 3| ≤ D3 * k :=
    (abs_div_pow_le_abs hq 3).trans h3
  have hn12 : |13 * k * k1 * k2| ≤ 13 * B ^ 2 * D1 * D2 * k := by
    have e1 : |13 * k * k1 * k2| = 13 * k * |k1| * |k2| := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13), hkabs]
    rw [e1]
    have hA : (0 : ℝ) ≤ 13 * k := by linarith
    have hA2 : (0 : ℝ) ≤ 13 * k * (D1 * k) := by positivity
    have s1 : 13 * k * |k1| * |k2| ≤ 13 * k * (D1 * k) * (D2 * k) :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA)
        (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 hA2)
    refine s1.trans ?_
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hD1 hD2) hk0)
      (sub_nonneg.2 hkk)]
  have hn13 : |4 * k1 ^ 3| ≤ 4 * B ^ 2 * D1 ^ 3 * k := by
    have e1 : |4 * k1 ^ 3| = 4 * |k1| ^ 3 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_pow]
    rw [e1]
    have hcube : |k1| ^ 3 ≤ (D1 * k) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 3
    nlinarith [hcube, mul_nonneg (mul_nonneg (pow_nonneg hD1 3) hk0)
      (sub_nonneg.2 hkk)]
  have hn1 : |13 * k * k1 * k2 + 4 * k1 ^ 3| ≤
      (13 * B ^ 2 * D1 * D2 + 4 * B ^ 2 * D1 ^ 3) * k := by
    have htri := abs_add_le (13 * k * k1 * k2) (4 * k1 ^ 3)
    nlinarith [hn12, hn13, htri]
  have ht1 : |(13 * k * k1 * k2 + 4 * k1 ^ 3) / (1 + k ^ 2) ^ 4| ≤
      (13 * B ^ 2 * D1 * D2 + 4 * B ^ 2 * D1 ^ 3) * k :=
    (abs_div_pow_le_abs hq 4).trans hn1
  have hn2 : |28 * k ^ 2 * k1 ^ 3| ≤ 28 * B ^ 4 * D1 ^ 3 * k := by
    have e1 : |28 * k ^ 2 * k1 ^ 3| = 28 * k ^ 2 * |k1| ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 28),
        abs_pow, abs_pow, hkabs]
    rw [e1]
    have hcube : |k1| ^ 3 ≤ (D1 * k) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 3
    nlinarith [mul_nonneg (pow_nonneg hk0 2) (sub_nonneg.2 hcube),
      mul_nonneg (mul_nonneg (pow_nonneg hD1 3) hk0) (sub_nonneg.2 hk4)]
  have ht2 : |28 * k ^ 2 * k1 ^ 3 / (1 + k ^ 2) ^ 5| ≤
      28 * B ^ 4 * D1 ^ 3 * k :=
    (abs_div_pow_le_abs hq 5).trans hn2
  have tri1 := abs_sub (k3 / (1 + k ^ 2) ^ 3)
    ((13 * k * k1 * k2 + 4 * k1 ^ 3) / (1 + k ^ 2) ^ 4)
  have tri2 := abs_add_le
    (k3 / (1 + k ^ 2) ^ 3
      - (13 * k * k1 * k2 + 4 * k1 ^ 3) / (1 + k ^ 2) ^ 4)
    (28 * k ^ 2 * k1 ^ 3 / (1 + k ^ 2) ^ 5)
  have hconst : pulseThirdConstant B D1 D2 D3 * k
      = D3 * k + (13 * B ^ 2 * D1 * D2 + 4 * B ^ 2 * D1 ^ 3) * k
        + 28 * B ^ 4 * D1 ^ 3 * k := by
    dsimp [pulseThirdConstant]; ring
  rw [hconst]
  linarith [ht0, ht1, ht2, tri1, tri2]

/-- The expanded third pulse formula is the canonical derivative of
`PulseFromCurvature.pulseDD`. -/
theorem pulseDDDExpanded_eq_pulseDDD
    {K K1 K2 K3 x : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s) :
    pulseDDDExpanded K K1 K2 K3 x = pulseDDD K K1 K2 x := by
  funext s
  have hcanonical := hasDerivAt_pulseDD_pulseDDD hK hK1 hK2 hx s
  have hexpanded : HasDerivAt (PulseFromCurvature.pulseDD K K1 K2 x)
      (pulseDDDExpanded K K1 K2 K3 x s) s := by
    have hqpos : (0 : ℝ) < 1 + K (x s) ^ 2 := by positivity
    have hsqne : Real.sqrt (1 + K (x s) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hqpos).ne'
    have hxs := hx s
    have hkx : HasDerivAt (fun t => K (x t))
        (K1 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK (x s)).comp s hxs
    have hk1x : HasDerivAt (fun t => K1 (x t))
        (K2 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK1 (x s)).comp s hxs
    have hk2x : HasDerivAt (fun t => K2 (x t))
        (K3 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK2 (x s)).comp s hxs
    have hqd : HasDerivAt (fun t => 1 + K (x t) ^ 2) _ s :=
      (hasDerivAt_const s (1 : ℝ)).add (hkx.pow 2)
    have hsqrtK : HasDerivAt (fun u : ℝ => Real.sqrt (1 + u ^ 2))
        (K (x s) / Real.sqrt (1 + K (x s) ^ 2)) (K (x s)) := by
      have h1 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * K (x s)) (K (x s)) := by
        refine ((hasDerivAt_const (K (x s)) (1 : ℝ)).add
          ((hasDerivAt_id (K (x s))).pow 2)).congr_deriv ?_
        norm_num
      refine ((Real.hasDerivAt_sqrt hqpos.ne').comp (K (x s)) h1).congr_deriv ?_
      field_simp
    have hsqrt := hsqrtK.comp s hkx
    have hD2ne : Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 2 ≠ 0 := by
      positivity
    have hD3ne : Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 3 ≠ 0 := by
      positivity
    have hA := hk2x.div (hsqrt.mul (hqd.pow 2)) hD2ne
    have hB := (((hasDerivAt_const s (4 : ℝ)).mul hkx).mul (hk1x.pow 2)).div
      (hsqrt.mul (hqd.pow 3)) hD3ne
    refine (hA.sub hB).congr_deriv ?_
    dsimp [pulseDDDExpanded]
    set r := Real.sqrt (1 + K (x s) ^ 2) with hrdef
    have hr2 : r ^ 2 = 1 + K (x s) ^ 2 := by rw [hrdef]; exact Real.sq_sqrt hqpos.le
    have hrne : r ≠ 0 := by rw [hrdef]; exact hsqne
    rw [← hr2]
    field_simp
    ring
  exact hexpanded.unique hcanonical

/-- Relative estimate for the canonical third pulse derivative, transferred
from any relative estimate for its explicit expansion. -/
theorem rel_pulseDDD_of_expanded
    {K K1 K2 K3 x : ℝ → ℝ} {C : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hrel : RelMajorant (fun s => K (x s))
      (pulseDDDExpanded K K1 K2 K3 x) C) :
    RelMajorant (fun s => K (x s)) (pulseDDD K K1 K2 x) C := by
  rw [← pulseDDDExpanded_eq_pulseDDD hK hK1 hK2 hx]
  exact hrel

/-- Fully instantiated relative bound for the canonical third pulse
derivative. -/
theorem rel_pulseDDD
    {K K1 K2 K3 x : ℝ → ℝ} {B D1 D2 D3 : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1d : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2d : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hK1 : RelMajorant K K1 D1)
    (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3) :
    RelMajorant (fun s => K (x s)) (pulseDDD K K1 K2 x)
      (pulseThirdConstant B D1 D2 D3) :=
  rel_pulseDDD_of_expanded hK hK1d hK2d hx
    (rel_pulseDDDExpanded hK0 hKB hB hD1 hD2 hD3 hK1 hK2 hK3)

/-- The explicit fourth front-arclength derivative of `pulseDDDExpanded`. -/
def pulseDDDDExpanded (K K1 K2 K3 K4 x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  let k := K (x s); let k1 := K1 (x s); let k2 := K2 (x s)
  let k3 := K3 (x s); let k4 := K4 (x s); let q := 1 + k ^ 2
  k4 / (Real.sqrt q * q ^ 3)
    - 6 * k * k1 * k3 / (Real.sqrt q * q ^ 4)
    - (25 * k1 ^ 2 * k2 + 13 * k * k2 ^ 2 + 13 * k * k1 * k3) /
        (Real.sqrt q * q ^ 4)
    + 8 * k * k1 * (13 * k * k1 * k2 + 4 * k1 ^ 3) /
        (Real.sqrt q * q ^ 5)
    + (56 * k * k1 ^ 4 + 84 * k ^ 2 * k1 ^ 2 * k2) /
        (Real.sqrt q * q ^ 5)
    - 280 * k ^ 3 * k1 ^ 4 / (Real.sqrt q * q ^ 6)

/-- Explicit relative constant for the fourth pulse derivative. -/
def pulseFourthConstant (B D1 D2 D3 D4 : ℝ) : ℝ :=
  D4 + 6 * B ^ 2 * D1 * D3
    + (25 * B ^ 2 * D1 ^ 2 * D2 + 13 * B ^ 2 * D2 ^ 2
      + 13 * B ^ 2 * D1 * D3)
    + (104 * B ^ 4 * D1 ^ 2 * D2 + 32 * B ^ 4 * D1 ^ 4)
    + (56 * B ^ 4 * D1 ^ 4 + 84 * B ^ 4 * D1 ^ 2 * D2)
    + 280 * B ^ 6 * D1 ^ 4

/-- Differentiating the displayed third formula gives the displayed fourth
formula. -/
theorem hasDerivAt_pulseDDDExpanded
    {K K1 K2 K3 K4 x : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s) (s : ℝ) :
    HasDerivAt (pulseDDDExpanded K K1 K2 K3 x)
      (pulseDDDDExpanded K K1 K2 K3 K4 x s) s := by
  have hqpos : (0 : ℝ) < 1 + K (x s) ^ 2 := by positivity
  have hsqne : Real.sqrt (1 + K (x s) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hqpos).ne'
  have hxs := hx s
  have hkx : HasDerivAt (fun t => K (x t))
      (K1 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK (x s)).comp s hxs
  have hk1x : HasDerivAt (fun t => K1 (x t))
      (K2 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK1 (x s)).comp s hxs
  have hk2x : HasDerivAt (fun t => K2 (x t))
      (K3 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK2 (x s)).comp s hxs
  have hk3x : HasDerivAt (fun t => K3 (x t))
      (K4 (x s) * (1 / Real.sqrt (1 + K (x s) ^ 2))) s := (hK3 (x s)).comp s hxs
  have hqd : HasDerivAt (fun t => 1 + K (x t) ^ 2) _ s :=
    (hasDerivAt_const s (1 : ℝ)).add (hkx.pow 2)
  have hq3ne : (1 + K (x s) ^ 2) ^ 3 ≠ 0 := by positivity
  have hq4ne : (1 + K (x s) ^ 2) ^ 4 ≠ 0 := by positivity
  have hq5ne : (1 + K (x s) ^ 2) ^ 5 ≠ 0 := by positivity
  have hT1 := hk3x.div (hqd.pow 3) hq3ne
  have hT2 := ((((hasDerivAt_const s (13 : ℝ)).mul hkx).mul hk1x).mul hk2x).add
    ((hasDerivAt_const s (4 : ℝ)).mul (hk1x.pow 3)) |>.div (hqd.pow 4) hq4ne
  have hT3 := (((hasDerivAt_const s (28 : ℝ)).mul (hkx.pow 2)).mul
    (hk1x.pow 3)).div (hqd.pow 5) hq5ne
  refine ((hT1.sub hT2).add hT3).congr_deriv ?_
  dsimp [pulseDDDDExpanded]
  set r := Real.sqrt (1 + K (x s) ^ 2) with hrdef
  have hr2 : r ^ 2 = 1 + K (x s) ^ 2 := by rw [hrdef]; exact Real.sq_sqrt hqpos.le
  have hrne : r ≠ 0 := by rw [hrdef]; exact hsqne
  rw [← hr2]
  field_simp
  ring

/-- The explicit fourth formula agrees with the canonical fourth derivative. -/
theorem pulseDDDDExpanded_eq_pulseDDDD
    {K K1 K2 K3 K4 x : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s) :
    pulseDDDDExpanded K K1 K2 K3 K4 x = pulseDDDD K K1 K2 x := by
  funext s
  have he := hasDerivAt_pulseDDDExpanded hK hK1 hK2 hK3 hx s
  rw [pulseDDDExpanded_eq_pulseDDD hK hK1 hK2 hx] at he
  exact he.deriv.symm

/-- Termwise relative estimate for the explicit fourth pulse derivative. -/
theorem rel_pulseDDDDExpanded
    {K K1 K2 K3 K4 x : ℝ → ℝ} {B D1 D2 D3 D4 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3) (hK4 : RelMajorant K K4 D4) :
    RelMajorant (fun s => K (x s)) (pulseDDDDExpanded K K1 K2 K3 K4 x)
      (pulseFourthConstant B D1 D2 D3 D4) := by
  intro s
  have hk0 := hK0 (x s); have hkB := hKB (x s)
  have h1 := hK1 (x s); have h2 := hK2 (x s)
  have h3 := hK3 (x s); have h4 := hK4 (x s)
  dsimp [pulseDDDDExpanded, pulseFourthConstant]
  have hq : 1 ≤ 1 + K (x s) ^ 2 := by nlinarith [sq_nonneg (K (x s))]
  obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩ :=
    PulseFourthTermBounds.pulseFourth_numerator_bounds hk0 hkB hB
      hD1 hD2 hD3 hD4 h1 h2 h3 h4
  have hd0 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := K4 (x s)) hq 3
  have hd1 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := 6 * K (x s) * K1 (x s) * K3 (x s)) hq 4
  have hd2 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := 25 * K1 (x s) ^ 2 * K2 (x s) + 13 * K (x s) * K2 (x s) ^ 2
      + 13 * K (x s) * K1 (x s) * K3 (x s)) hq 4
  have hd3 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := 8 * K (x s) * K1 (x s) *
      (13 * K (x s) * K1 (x s) * K2 (x s) + 4 * K1 (x s) ^ 3)) hq 5
  have hd4 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := 56 * K (x s) * K1 (x s) ^ 4
      + 84 * K (x s) ^ 2 * K1 (x s) ^ 2 * K2 (x s)) hq 5
  have hd5 := PulseFourthTermBounds.abs_div_sqrt_mul_pow_le_abs
    (z := 280 * K (x s) ^ 3 * K1 (x s) ^ 4) hq 6
  have key : ∀ a b c d e f : ℝ,
      |a - b - c + d + e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
    intro a b c d e f
    have s1 := abs_sub (a - b - c + d + e) f
    have s2 := abs_add_le (a - b - c + d) e
    have s3 := abs_add_le (a - b - c) d
    have s4 := abs_sub (a - b) c
    have s5 := abs_sub a b
    linarith
  refine (key _ _ _ _ _ _).trans ?_
  linarith [hd0.trans ht0, hd1.trans ht1, hd2.trans ht2, hd3.trans ht3,
    hd4.trans ht4, hd5.trans ht5]

/-- Canonical fourth pulse derivative bound through the fourth curvature jet. -/
theorem rel_pulseDDDD
    {K K1 K2 K3 K4 x : ℝ → ℝ} {B D1 D2 D3 D4 : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1d : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2d : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3d : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3) (hK4 : RelMajorant K K4 D4) :
    RelMajorant (fun s => K (x s)) (pulseDDDD K K1 K2 x)
      (pulseFourthConstant B D1 D2 D3 D4) := by
  rw [← pulseDDDDExpanded_eq_pulseDDDD hK hK1d hK2d hK3d hx]
  exact rel_pulseDDDDExpanded hK0 hKB hB hD1 hD2 hD3 hD4 hK1 hK2 hK3 hK4

/-- Conditional fourth pulse expansion: differentiating the explicit third
formula gives the canonical fourth derivative.  The `K4` hypothesis is made
explicit because it is exactly the additional curvature-jet input needed by
the chain rule. -/
theorem pulseDDDD_eq_deriv_expanded
    {K K1 K2 K3 K4 x : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s) :
    pulseDDDD K K1 K2 x = fun s =>
      deriv (pulseDDDExpanded K K1 K2 K3 x) s := by
  have h := pulseDDDExpanded_eq_pulseDDD (K3 := K3) hK hK1 hK2 hx
  funext s
  show deriv (pulseDDD K K1 K2 x) s = deriv (pulseDDDExpanded K K1 K2 K3 x) s
  rw [h]

/-- A relative fourth-order bound transfers directly from the differentiated
expanded formula to the canonical fourth pulse derivative.  The derivative
jet through `K4` records the hypotheses used to establish that supplied
expanded bound. -/
theorem rel_pulseDDDD_of_expanded
    {K K1 K2 K3 K4 x : ℝ → ℝ} {C : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK4 : ∃ D4 ≥ 0, RelMajorant K K4 D4)
    (hrel : RelMajorant (fun s => K (x s))
      (fun s => deriv (pulseDDDExpanded K K1 K2 K3 x) s) C) :
    RelMajorant (fun s => K (x s)) (pulseDDDD K K1 K2 x) C := by
  obtain ⟨D4, hD4, hK4rel⟩ := hK4
  rw [pulseDDDD_eq_deriv_expanded hK hK1 hK2 hK3 hx]
  exact hrel

end PulseHigherDerivativeBridge
