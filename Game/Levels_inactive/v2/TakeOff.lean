import Game.Metadata
import Mathlib


open Real Polynomial

noncomputable
def f : ℝ → ℝ := fun x =>  if x ≤ 0 then 0 else Real.exp (- 1 / x)

/-- `f` is exactly Mathlib's `expNegInvGlue`. -/
theorem f_eq_expNegInvGlue : f = expNegInvGlue := by
  funext x
  simp [f, expNegInvGlue, neg_div, one_div]

/-- The polynomials `P n` such that the `n`-th derivative of `expNegInvGlue` is
`x ↦ (P n).eval x⁻¹ * expNegInvGlue x`. -/
noncomputable
def P : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (P n - derivative (P n))

/-- On all of `ℝ`, the `n`-th derivative of `expNegInvGlue` is `(P n)(x⁻¹) * expNegInvGlue x`. -/
theorem iteratedDeriv_expNegInvGlue (n : ℕ) :
    iteratedDeriv n expNegInvGlue = fun x => (P n).eval x⁻¹ * expNegInvGlue x := by
  induction n with
  | zero =>
    funext x
    rw [iteratedDeriv_zero, P, eval_one, one_mul]
  | succ n ih =>
    funext x
    rw [iteratedDeriv_succ, ih, P]
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (P n) x).deriv

/-- All iterated derivatives of `f` vanish at `0`: `f` is infinitely flat at `0`. -/
theorem iteratedDeriv_f_zero (n : ℕ) : iteratedDeriv n f 0 = 0 := by
  rw [f_eq_expNegInvGlue, iteratedDeriv_expNegInvGlue]
  simp [expNegInvGlue.zero]
