import Game.Levels_inactive.v2.LightAndShade_Test.L03_ShadeSetNonempty

World "LightAndShade"
Level 4

Title "Bounded Above"

Introduction "Intro LightAndShade L04: a quick boundedness fact.

To take the supremum `sSup (shadeSet f c b)`, we also need the set to be bounded above.  This is
immediate: every element of `shadeSet f c b` lies in `Ioo c b`, hence is below `b`.
"

open Set

/-- The set `shadeSet f c b` is bounded above (by `b`). -/
TheoremDoc shadeSet_bddAbove as "shadeSet_bddAbove" in "Shade"

Statement shadeSet_bddAbove (f : ℝ → ℝ) (c b : ℝ) : BddAbove (shadeSet f c b) := by
  Hint "Provide `b` as an explicit upper bound. For any `y` in the set, its membership gives
  `y < b`, so `y ≤ b`. The whole proof is the term `⟨b, fun y hy => hy.1.2.le⟩`."
  use b
  intro y hy
  simp [shadeSet] at hy
  grind

Conclusion "Conclusion LightAndShade L04: saved as `shadeSet_bddAbove`."

TheoremTab "Shade"
