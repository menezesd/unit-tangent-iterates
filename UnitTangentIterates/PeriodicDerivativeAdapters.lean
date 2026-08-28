import Mathlib

/-!
# Periodicity of derivatives from translation laws

These elementary adapters are independent of the interpolation constructor.
They are intended for the moving-period closing stage, where a gauge slice is
known to commute with translation and its spatial derivative witnesses are
supplied separately.
-/

open Function

namespace PeriodicDerivativeAdapters

/-- Differentiating `f (u + Q) = f u + C` removes the additive drift and makes
the derivative `Q`-periodic. -/
theorem periodic_derivative_of_additive_translation
    {f f1 : ℝ → ℝ} {Q C : ℝ}
    (htrans : ∀ u, f (u + Q) = f u + C)
    (hderiv : ∀ u, HasDerivAt f (f1 u) u) :
    Periodic f1 Q := by
  intro u
  have hleft : HasDerivAt (fun x => f (x + Q)) (f1 (u + Q)) u :=
    by simpa only [Function.comp_def, id_eq, mul_one] using
      (hderiv (u + Q)).comp u ((hasDerivAt_id u).add_const Q)
  have hright : HasDerivAt (fun x => f x + C) (f1 u) u :=
    (hderiv u).add_const C
  have heq : (fun x => f (x + Q)) = fun x => f x + C :=
    funext htrans
  calc
    f1 (u + Q) = deriv (fun x => f (x + Q)) u := hleft.deriv.symm
    _ = deriv (fun x => f x + C) u := by rw [heq]
    _ = f1 u := hright.deriv

/-- The zero-drift specialization for an ordinary periodic function. -/
theorem periodic_derivative_of_periodic
    {f f1 : ℝ → ℝ} {Q : ℝ}
    (hper : Periodic f Q)
    (hderiv : ∀ u, HasDerivAt f (f1 u) u) :
    Periodic f1 Q := by
  exact periodic_derivative_of_additive_translation
    (Q := Q) (C := 0) (fun u => by simpa using hper u) hderiv

/-- First and second derivative periodicity obtained from one periodic
function and two explicit derivative witnesses. -/
theorem periodic_first_second_derivatives
    {f f1 f2 : ℝ → ℝ} {Q : ℝ}
    (hper : Periodic f Q)
    (hderiv : ∀ u, HasDerivAt f (f1 u) u)
    (hderiv1 : ∀ u, HasDerivAt f1 (f2 u) u) :
    Periodic f1 Q ∧ Periodic f2 Q := by
  have hper1 := periodic_derivative_of_periodic hper hderiv
  exact ⟨hper1, periodic_derivative_of_periodic hper1 hderiv1⟩

/-- A quasi-periodic gauge slice has periodic first and second spatial
derivatives.  The translation amount and the parameter period may vary with
the time slice. -/
theorem phi_derivatives_periodic
    {Phi phi1 phi2 : ℝ → ℝ → ℝ} {period drift : ℝ → ℝ}
    (htrans : ∀ t u, Phi t (u + period t) = Phi t u + drift t)
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) :
    (∀ t, Periodic (phi1 t) (period t)) ∧
      (∀ t, Periodic (phi2 t) (period t)) := by
  constructor
  · intro t
    exact periodic_derivative_of_additive_translation (htrans t) (hphi1 t)
  · intro t
    have hper1 : Periodic (phi1 t) (period t) :=
      periodic_derivative_of_additive_translation (htrans t) (hphi1 t)
    exact periodic_derivative_of_periodic hper1 (hphi2 t)

/-- Spatial derivatives of a periodic normal-rate family are periodic.  This
is the periodicity component needed for `C2NormalPathData` once the two
spatial derivative witnesses for `pathEta` are available. -/
theorem eta_derivatives_periodic
    {eta eta1 eta2 : ℝ → ℝ → ℝ} {period : ℝ → ℝ}
    (heta : ∀ t, Periodic (eta t) (period t))
    (heta1 : ∀ t u, HasDerivAt (eta t) (eta1 t u) u)
    (heta2 : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u) :
    (∀ t, Periodic (eta1 t) (period t)) ∧
      (∀ t, Periodic (eta2 t) (period t)) := by
  constructor
  · intro t
    exact periodic_derivative_of_periodic (heta t) (heta1 t)
  · intro t
    have hper1 : Periodic (eta1 t) (period t) :=
      periodic_derivative_of_periodic (heta t) (heta1 t)
    exact periodic_derivative_of_periodic hper1 (heta2 t)

end PeriodicDerivativeAdapters
