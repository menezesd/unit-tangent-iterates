import UnitTangentIterates.MarkingDeviationC2
import UnitTangentIterates.RearOwnTangential

/-!
# Oriented curvature of a gauge-marked selected rear

Positive reparametrization preserves the sign of oriented curvature.  The
second derivative of the marking contributes only tangential acceleration;
the normal term is multiplied by the cube of the first derivative.
-/

noncomputable section

open Set Function Complex MarkedSpace

namespace GaugeRearEndpointCurvature

open RearOwnArclength RearOwnTangential

/-- Exact oriented-curvature transformation for a `C2` marking of a
unit-speed Frenet curve. -/
theorem orientedCurvature_eq_cube
    {Y : ℝ → ℂ} {α k phi phi1 phi2 : ℝ → ℝ} {rear : Data}
    (hY : ∀ s, HasDerivAt Y
      (Complex.exp (Complex.I * (α s : ℂ))) s)
    (hα : ∀ s, HasDerivAt α (k s) s)
    (hposition : ∀ u, rear.1 u = Y (phi u))
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u) (u : ℝ) :
    ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im =
      phi1 u ^ 3 * k (phi u) := by
  let a := phi1 u
  let b := k (phi u)
  let z := Complex.exp (Complex.I * (α (phi u) : ℂ))
  have hv : rear.2.1 u = (a : ℂ) * z := by
    have hcomp := (hY (phi u)).scomp u (hphi u)
    change HasDerivAt (fun t : ℝ => Y (phi t))
      (phi1 u • Complex.exp (Complex.I * (α (phi u) : ℂ))) u at hcomp
    have heq : (fun t : ℝ => Y (phi t)) = ⇑rear.1 :=
      funext fun t => (hposition t).symm
    rw [heq] at hcomp
    have hu := (hcurve u).unique hcomp
    simpa [a, z, Complex.real_smul] using hu
  have ha : rear.2.2 u =
      (((phi2 u : ℝ) : ℂ) + Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) * z := by
    have hveq : ⇑rear.2.1 = fun t : ℝ =>
        ((phi1 t : ℝ) : ℂ) *
          Complex.exp (Complex.I * (α (phi t) : ℂ)) := by
      funext t
      have hcomp := (hY (phi t)).scomp t (hphi t)
      change HasDerivAt (fun x : ℝ => Y (phi x))
        (phi1 t • Complex.exp (Complex.I * (α (phi t) : ℂ))) t at hcomp
      have heq : (fun x : ℝ => Y (phi x)) = ⇑rear.1 :=
        funext fun x => (hposition x).symm
      rw [heq] at hcomp
      have ht := (hcurve t).unique hcomp
      simpa [Complex.real_smul] using ht
    have hang := (MarkingDeviationC2.hasDerivAt_exp_angle hα (phi u)).scomp u
      (hphi u)
    have hcast : HasDerivAt (fun t : ℝ => ((phi1 t : ℝ) : ℂ))
        ((phi2 u : ℝ) : ℂ) u :=
      (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt u (hphi1 u)
    have hprod := hcast.mul hang
    rw [hveq] at hvel
    have hu := (hvel u).unique hprod
    rw [hu]
    dsimp [a, b, z]
    push_cast
    ring
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp
  have hzsq : Complex.normSq z = 1 := by
    calc
      Complex.normSq z = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
      _ = 1 := by rw [hzNorm]; norm_num
  have hzconj : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hzsq]
    norm_num
  rw [hv, ha, map_mul, Complex.conj_ofReal]
  have hreassoc :
      ((a : ℂ) * (starRingEnd ℂ) z) *
          ((((phi2 u : ℝ) : ℂ) +
            Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) * z) =
        (a : ℂ) *
          (((phi2 u : ℝ) : ℂ) +
            Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) *
          ((starRingEnd ℂ) z * z) := by ring
  rw [hreassoc, hzconj]
  simp [Complex.mul_im]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  dsimp [a, b]
  ring

/-- Nonnegative Frenet curvature and an orientation-preserving marking imply
nonnegative oriented curvature of the marked endpoint. -/
theorem orientedCurvature_nonnegative
    {Y : ℝ → ℂ} {α k phi phi1 phi2 : ℝ → ℝ} {rear : Data}
    (hY : ∀ s, HasDerivAt Y
      (Complex.exp (Complex.I * (α s : ℂ))) s)
    (hα : ∀ s, HasDerivAt α (k s) s)
    (hposition : ∀ u, rear.1 u = Y (phi u))
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1_nonnegative : ∀ u, 0 ≤ phi1 u)
    (hk : ∀ s, 0 ≤ k s) :
    ∀ u, 0 ≤ ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im := by
  intro u
  rw [orientedCurvature_eq_cube hY hα hposition hcurve hvel hphi hphi1 u]
  exact mul_nonneg (pow_nonneg (hphi1_nonnegative u) 3) (hk (phi u))

/-- Selected-rear specialization.  The rear-own Frenet curvature is
`tan delta`; the selected strip makes it nonnegative, and the terminal gauge
flow supplies the positive marking derivative. -/
theorem rearOwn_terminal_orientedCurvature_nonnegative
    {F : ℝ → ℝ → ℂ} {Θ delta K sf : ℝ → ℝ → ℝ}
    {phi phi1 phi2 : ℝ → ℝ} {rear : Data} {T kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ s, 0 ≤ delta T s)
    (hstrip1 : ∀ s, delta T s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (hposition : ∀ u, rear.1 u = rearOwn F Θ delta sf T (phi u))
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1_nonnegative : ∀ u, 0 ≤ phi1 u) :
    ∀ u, 0 ≤ ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im := by
  have harc : Real.arcsin kh < Real.pi / 2 := by
    rw [show Real.pi / 2 = Real.arcsin 1 by simp [Real.arcsin_one]]
    exact Real.arcsin_lt_arcsin (by linarith) hkh1 (le_refl 1)
  have htan : ∀ x, 0 ≤ Real.tan (delta T (sf T x)) := by
    intro x
    rcases eq_or_lt_of_le (hstrip0 (sf T x)) with hzero | hpos
    · rw [← hzero]
      simp
    · exact (Real.tan_pos_of_pos_of_lt_pi_div_two hpos
        (lt_of_le_of_lt (hstrip1 (sf T x)) harc)).le
  exact orientedCurvature_nonnegative
    (Y := rearOwn F Θ delta sf T)
    (α := rearOwnAngle Θ delta sf T)
    (k := fun x => Real.tan (delta T (sf T x)))
    (hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos T)
    (hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf T)
    hposition hcurve hvel hphi hphi1 hphi1_nonnegative htan

end GaugeRearEndpointCurvature
