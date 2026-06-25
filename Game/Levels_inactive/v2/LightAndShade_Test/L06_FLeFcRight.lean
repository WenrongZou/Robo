import Game.Levels_inactive.v2.LightAndShade_Test.L05_FcLeFsSup

World "LightAndShade"
Level 6

Title "Nothing Higher to the Right"

Introduction "Intro LightAndShade L06: control of `f` just to the right of the supremum.

Let `d = sSup (shadeSet f c b)`.  For any `x` strictly between `d` and `b`, the point `x` lies
beyond the supremum, hence cannot be in `shadeSet f c b`.  Since `x` *is* in `Ioo c b`, the only way
it can fail to be in the set is `f x ≤ f c`.  Thus `f x ≤ f c` for every `x ∈ Ioo d b`.
"

open Set

/-- To the right of the supremum (but below `b`), `f` never exceeds `f c`. -/
TheoremDoc f_le_fc_right as "f_le_fc_right" in "Shade"

Statement f_le_fc_right {f : ℝ → ℝ} {b c : ℝ}
    (hne : (shadeSet f c b).Nonempty) :
    ∀ x ∈ Set.Ioo (sSup (shadeSet f c b)) b, f x ≤ f c := by
  Hint "Abbreviate the supremum with `set d := sSup (shadeSet f c b) with hd_def`."
  set d := sSup (shadeSet f c b) with hd_def
  have hd : BddAbove (shadeSet f c b) := shadeSet_bddAbove f c b
  Hint "First note `c < d`: pick any element `x0` of the (nonempty) set, then
  `c < x0 ≤ sSup = d`."
  have hcd : c < d := by
    obtain ⟨x0, hx0⟩ := hne
    obtain h := (le_csSup hd hx0)
    simp [shadeSet] at hx0
    grind
    -- exact lt_of_lt_of_le hx0.1.1 (le_csSup hd hx0)
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  Hint "Since `d < x`, `x` is past the supremum, so `x ∉ shadeSet f c b`. Use
  `notMem_of_csSup_lt hx1 hd`."
  have not_mem : x ∉ shadeSet f c b := notMem_of_csSup_lt hx1 hd
  Hint "Suppose `f x > f c`. Together with `c < x < b` this would put `x` back into the set,
  contradicting `not_mem`."
  by_contra hcon
  exact not_mem ⟨⟨lt_trans hcd hx1, hx2⟩, not_le.mp hcon⟩

Conclusion "Conclusion LightAndShade L06: saved as `f_le_fc_right`."

TheoremTab "Shade"
