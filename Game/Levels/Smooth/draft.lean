import Game.Metadata
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition


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

section

open expNegInvGlue

lemma hasDerivAt_polynomial_eval_inv_mul' (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * expNegInvGlue x)
      ((X ^ 2 * (p - derivative (R := ℝ) p)).eval x⁻¹ * expNegInvGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le, mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
    simp_log [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
    convert! this.congr_of_eventuallyEq _ using 1
    · simp_log [expNegInvGlue, hx.not_ge]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp_log [expNegInvGlue, hy.not_ge]

end
