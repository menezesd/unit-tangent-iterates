import Mathlib
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.HairpinMass
import UnitTangentIterates.SechPulse

/-!
# The steering pulse of an isolated pair from its rear curvature

The matching configurations of *A Noncircular Oval with Convex Unit-Tangent
Iterates* are built from a *steering pulse* `y = sin δ` of an isolated pair,
read in the **front** arclength `t`, whose rear curvature `K` is read in the
**rear** arclength `u`.  The two are tied by the steering identity

```
  y(t) = √(1 - y(t)²)·K(x(t)),        x'(t) = √(1 - y(t)²),  x(0) = 0,
```

which says that `tan δ = K ∘ x` with `x` the rear arclength of the pair.

This file *constructs* the pulse from the curvature: given a nonnegative `C¹`
curvature `K` on the line with an exponential majorant and a relative derivative
bound, the front arclength `σ(u) = ∫₀ᵘ √(1+K²)` is an increasing bijection, and
the pulse

```
  y(t) = K(x(t))/√(1 + K(x(t))²),      x = σ⁻¹,
```

satisfies the steering identity, is nonnegative, decays exponentially (at the
rate `α/√(1+Km²)`, the front arclength being longer than the rear one by at most
that factor), has a continuous derivative dominated both by the same exponential
and by `D·y`, and carries the same mass as the curvature, `∫_ℝ y = ∫_ℝ K`.

Main result: `exists_pulse_of_curvature`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PulseFromCurvature

/-- The front arclength of the rear track of curvature `K`: `σ(u) = ∫₀ᵘ √(1+K²)`. -/
def frontLen (K : ℝ → ℝ) : ℝ → ℝ := fun u => ∫ v in (0:ℝ)..u, Real.sqrt (1 + K v ^ 2)

/-- The steering pulse `y = K∘x/√(1+(K∘x)²)` attached to a rear arclength
inverse `x`. -/
def pulse (K x : ℝ → ℝ) : ℝ → ℝ := fun s => K (x s) / Real.sqrt (1 + K (x s) ^ 2)

/-- Its derivative, `y' = (K'∘x)/(1+(K∘x)²)²`. -/
def pulseD (K K' x : ℝ → ℝ) : ℝ → ℝ := fun s => K' (x s) / (1 + K (x s) ^ 2) ^ 2

/-- The second front-arclength derivative of the pulse, written only in terms
of the first two rear-arclength curvature derivatives. -/
def pulseDD (K K' K'' x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  K'' (x s) / (Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 2)
    - 4 * K (x s) * K' (x s) ^ 2 /
      (Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 3)

variable {K K' x : ℝ → ℝ} {alpha CK CK1 DK Km : ℝ}

/-! ### The front arclength -/

theorem one_le_sqrt (u : ℝ) : (1:ℝ) ≤ Real.sqrt (1 + K u ^ 2) := by
  have h : (1:ℝ) ≤ 1 + K u ^ 2 := by nlinarith [sq_nonneg (K u)]
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt h

theorem sqrt_le_of_le (hKm : ∀ u, K u ≤ Km) (hK0 : ∀ u, 0 ≤ K u) (u : ℝ) :
    Real.sqrt (1 + K u ^ 2) ≤ Real.sqrt (1 + Km ^ 2) := by
  refine Real.sqrt_le_sqrt ?_
  nlinarith [hKm u, hK0 u]

theorem hasDerivAt_frontLen (hKc : Continuous K) (u : ℝ) :
    HasDerivAt (frontLen K) (Real.sqrt (1 + K u ^ 2)) u := by
  have hc : Continuous fun v => Real.sqrt (1 + K v ^ 2) := by fun_prop
  simpa [frontLen] using (hc.integral_hasStrictDerivAt (0:ℝ) u).hasDerivAt

theorem frontLen_zero : frontLen K 0 = 0 := by simp [frontLen]

theorem strictMono_frontLen (hKc : Continuous K) : StrictMono (frontLen K) :=
  ArclengthInverse.strictMono_of_deriv_ge (c := 1) one_pos (hasDerivAt_frontLen hKc)
    (fun u => one_le_sqrt u)

/-- An upper bound for a function whose derivative is at most `c`, above `0`. -/
theorem le_of_deriv_le {f g : ℝ → ℝ} {c : ℝ} (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, g s ≤ c) {s : ℝ} (hs : 0 ≤ s) : f s ≤ f 0 + c * s := by
  have h := ArclengthInverse.le_of_deriv_ge (f := fun z => -f z) (g := fun z => -g z)
    (c := -c) (fun z => (hf z).neg) (fun z => by linarith [hg z]) hs
  simp only [neg_mul] at h
  linarith

/-- The symmetric bound below `0`. -/
theorem ge_of_deriv_le {f g : ℝ → ℝ} {c : ℝ} (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, g s ≤ c) {s : ℝ} (hs : s ≤ 0) : f 0 + c * s ≤ f s := by
  have h := ArclengthInverse.ge_of_deriv_ge (f := fun z => -f z) (g := fun z => -g z)
    (c := -c) (fun z => (hf z).neg) (fun z => by linarith [hg z]) hs
  simp only [neg_mul] at h
  linarith

/-- The front arclength stretches by at most `√(1+Km²)`. -/
theorem abs_frontLen_le (hKc : Continuous K) (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km)
    (u : ℝ) : |frontLen K u| ≤ Real.sqrt (1 + Km ^ 2) * |u| := by
  rcases le_total 0 u with hu | hu
  · have h1 : frontLen K u ≤ Real.sqrt (1 + Km ^ 2) * u := by
      have := le_of_deriv_le (hasDerivAt_frontLen hKc) (sqrt_le_of_le hKm hK0) hu
      rwa [frontLen_zero, zero_add] at this
    have h2 : 0 ≤ frontLen K u := by
      have := ArclengthInverse.le_of_deriv_ge (c := 1) (hasDerivAt_frontLen hKc)
        (fun v => one_le_sqrt v) hu
      rw [frontLen_zero, zero_add] at this
      linarith
    rw [abs_of_nonneg h2, abs_of_nonneg hu]
    exact h1
  · have hu' : u ≤ 0 := hu
    have h1 : Real.sqrt (1 + Km ^ 2) * u ≤ frontLen K u := by
      have := ge_of_deriv_le (hasDerivAt_frontLen hKc) (sqrt_le_of_le hKm hK0) hu'
      rwa [frontLen_zero, zero_add] at this
    have h2 : frontLen K u ≤ 0 := by
      have := ArclengthInverse.ge_of_deriv_ge (c := 1) (hasDerivAt_frontLen hKc)
        (fun v => one_le_sqrt v) hu'
      rw [frontLen_zero, zero_add] at this
      linarith
    rw [abs_of_nonpos h2, abs_of_nonpos hu']
    linarith

/-! ### The pulse -/

section Pulse

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

theorem x_zero : x 0 = 0 := by
  refine (strictMono_frontLen hKc).injective ?_
  rw [hxinv 0, frontLen_zero]

theorem leftInverse_x (u : ℝ) : x (frontLen K u) = u :=
  ArclengthInverse.leftInverse_of_rightInverse (strictMono_frontLen hKc).injective hxinv u

theorem continuous_x : Continuous x :=
  ArclengthInverse.continuous_of_rightInverse (c := 1) one_pos (hasDerivAt_frontLen hKc)
    (fun u => one_le_sqrt u) hxinv

theorem hasDerivAt_x (s : ℝ) : HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s :=
  ArclengthInverse.hasDerivAt_of_rightInverse (c := 1) one_pos (hasDerivAt_frontLen hKc)
    (fun u => one_le_sqrt u) hxinv s

/-- `|s| ≤ √(1+Km²)·|x s|`: the rear arclength is shorter than the front one by
at most the factor `√(1+Km²)`. -/
theorem abs_le_abs_x (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km) (s : ℝ) :
    |s| ≤ Real.sqrt (1 + Km ^ 2) * |x s| := by
  have h := abs_frontLen_le (K := K) (Km := Km) hKc hK0 hKm (x s)
  rwa [hxinv s] at h

end Pulse

/-! ### The pointwise algebra of the pulse -/

theorem sqrt_pos_one_add (u : ℝ) : 0 < Real.sqrt (1 + K u ^ 2) :=
  lt_of_lt_of_le one_pos (one_le_sqrt u)

theorem pulse_nonneg (hK0 : ∀ u, 0 ≤ K u) (s : ℝ) : 0 ≤ pulse K x s :=
  div_nonneg (hK0 _) (Real.sqrt_nonneg _)

theorem pulse_le_curv (hK0 : ∀ u, 0 ≤ K u) (s : ℝ) : pulse K x s ≤ K (x s) := by
  rw [pulse]
  exact div_le_self (hK0 _) (one_le_sqrt _)

theorem one_sub_pulse_sq (s : ℝ) :
    1 - pulse K x s ^ 2 = 1 / (1 + K (x s) ^ 2) := by
  have hpos : (0:ℝ) < 1 + K (x s) ^ 2 := by positivity
  have hsq : Real.sqrt (1 + K (x s) ^ 2) ^ 2 = 1 + K (x s) ^ 2 :=
    Real.sq_sqrt hpos.le
  rw [pulse, div_pow, hsq]
  field_simp
  ring

theorem sqrt_one_sub_pulse_sq (s : ℝ) :
    Real.sqrt (1 - pulse K x s ^ 2) = 1 / Real.sqrt (1 + K (x s) ^ 2) := by
  rw [one_sub_pulse_sq, one_div, one_div, ← Real.sqrt_inv]

/-- **The steering identity**: `y = √(1-y²)·K∘x`. -/
theorem pulse_eq_speed_mul_curv (s : ℝ) :
    pulse K x s = Real.sqrt (1 - pulse K x s ^ 2) * K (x s) := by
  rw [sqrt_one_sub_pulse_sq, pulse]
  ring

/-! ### The derivative of the pulse -/

/-- The derivative of `u ↦ K u/√(1+K u²)`. -/
theorem hasDerivAt_curvPulse (hKd : ∀ u, HasDerivAt K (K' u) u) (u : ℝ) :
    HasDerivAt (fun v => K v / Real.sqrt (1 + K v ^ 2))
      (K' u / ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2))) u := by
  have hpos : (0:ℝ) < 1 + K u ^ 2 := by positivity
  have hsq : HasDerivAt (fun v => 1 + K v ^ 2) (2 * K u * K' u) u := by
    have := (hKd u).pow 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this.const_add 1
  have hsqrt : HasDerivAt (fun v => Real.sqrt (1 + K v ^ 2))
      (1 / (2 * Real.sqrt (1 + K u ^ 2)) * (2 * K u * K' u)) u :=
    (Real.hasDerivAt_sqrt hpos.ne').comp u hsq
  have hne : Real.sqrt (1 + K u ^ 2) ≠ 0 := (sqrt_pos_one_add u).ne'
  have h := (hKd u).div hsqrt hne
  convert h using 1
  have hs2 : Real.sqrt (1 + K u ^ 2) ^ 2 = 1 + K u ^ 2 := Real.sq_sqrt hpos.le
  have hspos : (0:ℝ) < Real.sqrt (1 + K u ^ 2) := sqrt_pos_one_add u
  field_simp
  rw [hs2]
  ring

section Deriv

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

/-- The derivative of the pulse. -/
theorem hasDerivAt_pulse (hKd : ∀ u, HasDerivAt K (K' u) u) (s : ℝ) :
    HasDerivAt (pulse K x) (pulseD K K' x s) s := by
  have h := (hasDerivAt_curvPulse hKd (x s)).comp s (hasDerivAt_x hKc hxinv s)
  have hpos : (0:ℝ) < 1 + K (x s) ^ 2 := by positivity
  have hspos : (0:ℝ) < Real.sqrt (1 + K (x s) ^ 2) := sqrt_pos_one_add _
  have hs2 : Real.sqrt (1 + K (x s) ^ 2) ^ 2 = 1 + K (x s) ^ 2 := Real.sq_sqrt hpos.le
  have hval : K' (x s) / ((1 + K (x s) ^ 2) * Real.sqrt (1 + K (x s) ^ 2))
      * (1 / Real.sqrt (1 + K (x s) ^ 2)) = pulseD K K' x s := by
    rw [pulseD]
    field_simp
    rw [hs2]
  rw [← hval]
  exact h

/-- The exact second derivative after changing from rear to front arclength. -/
theorem hasDerivAt_pulseD (hKd : ∀ u, HasDerivAt K (K' u) u)
    {K'' : ℝ → ℝ} (hKdd : ∀ u, HasDerivAt K' (K'' u) u) (s : ℝ) :
    HasDerivAt (pulseD K K' x) (pulseDD K K' K'' x s) s := by
  let q : ℝ := 1 + K (x s) ^ 2
  let r : ℝ := Real.sqrt q
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by exact Real.sqrt_pos.2 hq
  have hx := hasDerivAt_x hKc hxinv s
  have hn : HasDerivAt (fun t => K' (x t)) (K'' (x s) * (1 / r)) s := by
    simpa [r, q] using (hKdd (x s)).comp s hx
  have hkx : HasDerivAt (fun t => K (x t)) (K' (x s) * (1 / r)) s := by
    simpa [r, q] using (hKd (x s)).comp s hx
  have hden : HasDerivAt (fun t => (1 + K (x t) ^ 2) ^ 2)
      (4 * K (x s) * K' (x s) * (1 / r) * q) s := by
    convert ((hasDerivAt_const s (1 : ℝ)).add (hkx.pow 2)).pow 2 using 1 <;>
      simp [q] <;> ring
  have h := hn.div hden (by positivity : q ^ 2 ≠ 0)
  convert h using 1
  dsimp [pulseDD, pulseD, q, r]
  have hrsq : Real.sqrt (1 + K (x s) ^ 2) ^ 2 = 1 + K (x s) ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp

theorem continuous_pulse : Continuous (pulse K x) := by
  have hx : Continuous x := continuous_x hKc hxinv
  have : Continuous fun s => K (x s) := hKc.comp hx
  exact this.div (by fun_prop) fun s => (sqrt_pos_one_add (K := K) (x s)).ne'

theorem continuous_pulseD (hK'c : Continuous K') : Continuous (pulseD K K' x) := by
  have hx : Continuous x := continuous_x hKc hxinv
  have h1 : Continuous fun s => K' (x s) := hK'c.comp hx
  have h2 : Continuous fun s => (1 + K (x s) ^ 2) ^ 2 := by
    have : Continuous fun s => K (x s) := hKc.comp hx
    fun_prop
  exact h1.div h2 fun s => by positivity

end Deriv

/-! ### The bounds -/

theorem abs_pulseD_le_abs_curvD (s : ℝ) : |pulseD K K' x s| ≤ |K' (x s)| := by
  have hpos : (0:ℝ) < 1 + K (x s) ^ 2 := by positivity
  have h1 : (1:ℝ) ≤ (1 + K (x s) ^ 2) ^ 2 := by nlinarith [sq_nonneg (K (x s))]
  rw [pulseD, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + K (x s) ^ 2) ^ 2)]
  exact div_le_self (abs_nonneg _) h1

/-- The relative derivative bound is inherited by the pulse. -/
theorem abs_pulseD_le_mul_pulse (hK0 : ∀ u, 0 ≤ K u) (hDK : 0 ≤ DK)
    (hrel : ∀ u, |K' u| ≤ DK * K u) (s : ℝ) :
    |pulseD K K' x s| ≤ DK * pulse K x s := by
  have hpos : (0:ℝ) < 1 + K (x s) ^ 2 := by positivity
  have hspos : (0:ℝ) < Real.sqrt (1 + K (x s) ^ 2) := sqrt_pos_one_add _
  have hs2 : Real.sqrt (1 + K (x s) ^ 2) ^ 2 = 1 + K (x s) ^ 2 := Real.sq_sqrt hpos.le
  have hcmp : Real.sqrt (1 + K (x s) ^ 2) ≤ (1 + K (x s) ^ 2) ^ 2 := by
    nlinarith [hs2, hspos, one_le_sqrt (K := K) (x s)]
  calc |pulseD K K' x s| ≤ |K' (x s)| / (1 + K (x s) ^ 2) ^ 2 := by
        rw [pulseD, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + K (x s) ^ 2) ^ 2)]
    _ ≤ (DK * K (x s)) / (1 + K (x s) ^ 2) ^ 2 := by
        gcongr
        exact hrel _
    _ ≤ (DK * K (x s)) / Real.sqrt (1 + K (x s) ^ 2) := by
        gcongr
        · exact mul_nonneg hDK (hK0 _)
    _ = DK * pulse K x s := by rw [pulse]; ring

/-! ### Exponential decay of the pulse and of its derivative -/

section Decay

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

/-- Transporting an exponential majorant from the rear to the front arclength:
the front arclength is at most `√(1+Km²)` times the rear one. -/
theorem exp_comp_le (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km) (halpha : 0 ≤ alpha) (s : ℝ) :
    Real.exp (-alpha * |x s|)
      ≤ Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|) := by
  have hMpos : (0:ℝ) < Real.sqrt (1 + Km ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith [sq_nonneg Km]
  have h := abs_le_abs_x hKc hxinv hK0 hKm s
  refine Real.exp_le_exp.mpr ?_
  rw [neg_mul, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff₀ hMpos]
  calc alpha * |s| ≤ alpha * (Real.sqrt (1 + Km ^ 2) * |x s|) := by
        exact mul_le_mul_of_nonneg_left h halpha
    _ = alpha * |x s| * Real.sqrt (1 + Km ^ 2) := by ring

/-- **Exponential decay of the pulse.** -/
theorem pulse_le_exp (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km) (halpha : 0 ≤ alpha)
    (hCK : 0 ≤ CK) (hKb : ∀ u, K u ≤ CK * Real.exp (-alpha * |u|)) (s : ℝ) :
    pulse K x s ≤ CK * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|) := by
  calc pulse K x s ≤ K (x s) := pulse_le_curv hK0 s
    _ ≤ CK * Real.exp (-alpha * |x s|) := hKb _
    _ ≤ CK * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|) :=
        mul_le_mul_of_nonneg_left (exp_comp_le hKc hxinv hK0 hKm halpha s) hCK

/-- **Exponential decay of the derivative of the pulse.** -/
theorem abs_pulseD_le_exp (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km) (halpha : 0 ≤ alpha)
    (hCK1 : 0 ≤ CK1) (hK1b : ∀ u, |K' u| ≤ CK1 * Real.exp (-alpha * |u|)) (s : ℝ) :
    |pulseD K K' x s| ≤ CK1 * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|) := by
  calc |pulseD K K' x s| ≤ |K' (x s)| := abs_pulseD_le_abs_curvD s
    _ ≤ CK1 * Real.exp (-alpha * |x s|) := hK1b _
    _ ≤ CK1 * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|) :=
        mul_le_mul_of_nonneg_left (exp_comp_le hKc hxinv hK0 hKm halpha s) hCK1

end Decay

/-! ### The rear arclength of the pulse -/

section RearArclength

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

/-- **The rear arclength of the pulse is the inverse of the front arclength**:
`∫₀ᵗ √(1-y²) = x(t)`, both sides having derivative `√(1-y²)` and vanishing at
`0`. -/
theorem integral_sqrt_one_sub_pulse_sq (t : ℝ) :
    (∫ u in (0:ℝ)..t, Real.sqrt (1 - pulse K x u ^ 2)) = x t := by
  have hyc : Continuous (pulse K x) := continuous_pulse hKc hxinv
  have hspeed : Continuous fun u => Real.sqrt (1 - pulse K x u ^ 2) := by fun_prop
  have hg : ∀ t : ℝ, HasDerivAt (fun t => ∫ u in (0:ℝ)..t, Real.sqrt (1 - pulse K x u ^ 2))
      (Real.sqrt (1 - pulse K x t ^ 2)) t := fun t => by
    simpa using (hspeed.integral_hasStrictDerivAt (0:ℝ) t).hasDerivAt
  have hxd : ∀ t : ℝ, HasDerivAt x (Real.sqrt (1 - pulse K x t ^ 2)) t := fun t => by
    have h := hasDerivAt_x hKc hxinv t
    rwa [← sqrt_one_sub_pulse_sq (K := K) (x := x) t] at h
  set F : ℝ → ℝ := fun t => (∫ u in (0:ℝ)..t, Real.sqrt (1 - pulse K x u ^ 2)) - x t with hF
  have hFd : ∀ t : ℝ, HasDerivAt F 0 t := fun t => by
    simpa using (hg t).sub (hxd t)
  have hconst : ∀ t : ℝ, F t = F 0 :=
    fun t => is_const_of_deriv_eq_zero (fun z => (hFd z).differentiableAt)
      (fun z => (hFd z).deriv) t 0
  have h0 : F 0 = 0 := by
    simp [hF, x_zero hKc hxinv]
  have := hconst t
  rw [h0] at this
  simp only [hF] at this
  linarith [this]

end RearArclength

/-! ### The mass of the pulse -/

section Mass

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

/-- The pulse is integrable. -/
theorem integrable_pulse (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km) (halpha : 0 < alpha)
    (hCK : 0 ≤ CK) (hKb : ∀ u, K u ≤ CK * Real.exp (-alpha * |u|)) :
    Integrable (pulse K x) := by
  set beta : ℝ := alpha / Real.sqrt (1 + Km ^ 2) with hbeta
  have hMpos : (0:ℝ) < Real.sqrt (1 + Km ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith [sq_nonneg Km]
  have hbpos : 0 < beta := by positivity
  have hmaj : Integrable (fun s : ℝ => CK * Real.exp (-beta * |s|)) :=
    (SechPulse.integrable_exp_neg_abs hbpos).const_mul CK
  refine Integrable.mono' hmaj (continuous_pulse hKc hxinv).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pulse_nonneg hK0 s)]
  exact pulse_le_exp hKc hxinv hK0 hKm halpha.le hCK hKb s

/-- **The mass identity**: the pulse carries the same mass as the curvature. -/
theorem integral_pulse_eq_integral_curv (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km)
    (halpha : 0 < alpha) (hCK : 0 ≤ CK) (hKb : ∀ u, K u ≤ CK * Real.exp (-alpha * |u|))
    (hKint : Integrable K) :
    (∫ s, pulse K x s) = ∫ u, K u := by
  have hyc : Continuous (pulse K x) := continuous_pulse hKc hxinv
  have hyint : Integrable (pulse K x) :=
    integrable_pulse (Km := Km) (alpha := alpha) (CK := CK) hKc hxinv hK0 hKm halpha hCK hKb
  have hsigderiv : ∀ u, HasDerivAt (frontLen K) (Real.sqrt (1 + K u ^ 2)) u :=
    hasDerivAt_frontLen hKc
  have hmass : ∀ a b : ℝ,
      (∫ s in (frontLen K a)..(frontLen K b), pulse K x s) = ∫ u in a..b, K u := by
    intro a b
    refine HairpinMass.mass_identity (fun u _ => hsigderiv u) hKc hyc ?_
    intro u
    rw [pulse, leftInverse_x hKc hxinv u]
  have hsigTop : Filter.Tendsto (frontLen K) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    have := ArclengthInverse.le_of_deriv_ge (c := 1) hsigderiv (fun v => one_le_sqrt v) hu
    rw [frontLen_zero] at this
    simpa using this
  have hsigBot : Filter.Tendsto (fun t : ℝ => frontLen K (-t)) atTop atBot := by
    have h : Filter.Tendsto (frontLen K) atBot atBot := by
      refine tendsto_atBot_mono' atBot ?_ (tendsto_id (α := ℝ))
      filter_upwards [eventually_le_atBot (0:ℝ)] with u hu
      have := ArclengthInverse.ge_of_deriv_ge (c := 1) hsigderiv (fun v => one_le_sqrt v) hu
      rw [frontLen_zero] at this
      simpa using this
    exact h.comp tendsto_neg_atTop_atBot
  have h1 : Filter.Tendsto
      (fun t : ℝ => ∫ s in (frontLen K (-t))..(frontLen K t), pulse K x s)
      atTop (nhds (∫ s, pulse K x s)) :=
    intervalIntegral_tendsto_integral hyint hsigBot hsigTop
  have h2 : Filter.Tendsto (fun t : ℝ => ∫ u in (-t)..t, K u) atTop (nhds (∫ u, K u)) :=
    intervalIntegral_tendsto_integral hKint tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have heq : (fun t : ℝ => ∫ s in (frontLen K (-t))..(frontLen K t), pulse K x s)
      = fun t : ℝ => ∫ u in (-t)..t, K u := funext fun t => hmass (-t) t
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Mass

/-! ### The pulse of a curvature -/

/-- **The steering pulse of an isolated pair from its rear curvature.**  A
nonnegative `C¹` curvature `K` on the line with exponential majorants `CK`,
`CK1` at the rate `alpha`, a relative derivative bound `DK` and a sup bound `Km`
carries a steering pulse `y`: with `x` the rear arclength of the pair (the
inverse of the front arclength `σ = ∫√(1+K²)`), the pulse
`y = K∘x/√(1+(K∘x)²)` obeys the steering identity of a matching configuration,
decays at the rate `alpha/√(1+Km²)` together with its derivative, inherits the
relative derivative bound, and has the same mass as `K`. -/
theorem exists_pulse_of_curvature (hKc : Continuous K) (hK'c : Continuous K')
    (hKd : ∀ u, HasDerivAt K (K' u) u) (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km)
    (halpha : 0 < alpha) (hCK : 0 ≤ CK) (hKb : ∀ u, K u ≤ CK * Real.exp (-alpha * |u|))
    (hCK1 : 0 ≤ CK1) (hK1b : ∀ u, |K' u| ≤ CK1 * Real.exp (-alpha * |u|))
    (hDK : 0 ≤ DK) (hrel : ∀ u, |K' u| ≤ DK * K u) (hKint : Integrable K) :
    ∃ y yd x : ℝ → ℝ,
      x 0 = 0 ∧
      (∀ s, 0 ≤ y s) ∧ (∀ s, y s ≤ Km) ∧
      Continuous y ∧ Continuous yd ∧
      (∀ s, HasDerivAt y (yd s) s) ∧
      (∀ s, y s ≤ CK * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|)) ∧
      (∀ s, |yd s| ≤ CK1 * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|)) ∧
      (∀ s, |yd s| ≤ DK * y s) ∧
      (∀ t, (∫ u in (0:ℝ)..t, Real.sqrt (1 - y u ^ 2)) = x t) ∧
      (∀ t, y t = Real.sqrt (1 - y t ^ 2) * K (x t)) ∧
      Integrable y ∧ (∫ s, y s) = ∫ u, K u := by
  obtain ⟨x, hxinv⟩ := ArclengthInverse.exists_rightInverse (c := 1) one_pos
    (hasDerivAt_frontLen hKc) (fun u => one_le_sqrt u)
  refine ⟨pulse K x, pulseD K K' x, x, x_zero hKc hxinv, fun s => pulse_nonneg hK0 s,
    fun s => le_trans (pulse_le_curv hK0 s) (hKm _),
    continuous_pulse hKc hxinv, continuous_pulseD hKc hxinv hK'c,
    fun s => hasDerivAt_pulse hKc hxinv hKd s,
    fun s => pulse_le_exp hKc hxinv hK0 hKm halpha.le hCK hKb s,
    fun s => abs_pulseD_le_exp hKc hxinv hK0 hKm halpha.le hCK1 hK1b s,
    fun s => abs_pulseD_le_mul_pulse hK0 hDK hrel s,
    fun t => integral_sqrt_one_sub_pulse_sq hKc hxinv t,
    fun t => pulse_eq_speed_mul_curv t,
    integrable_pulse (Km := Km) (alpha := alpha) (CK := CK) hKc hxinv hK0 hKm halpha hCK hKb,
    integral_pulse_eq_integral_curv (Km := Km) hKc hxinv hK0 hKm halpha hCK hKb hKint⟩

end PulseFromCurvature
