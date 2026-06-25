import Game.Levels_inactive.v2.LightAndShade_Test.L01_NotMemShade

World "LightAndShade"
Level 2

Title "Finding a High Point"

Introduction "Intro LightAndShade L02: the intermediate value step.

Suppose `f` is continuous, `a < b`, and `f a > f b`.  Then somewhere strictly between `a` and `b`
the function still takes a value above `f b`.  This is a direct consequence of the intermediate
value theorem applied on the open interval `Ioo a b`.
"

open Set

/-- If `f` is continuous on `[a,b]` with `f a > f b`, then there is a point `s ∈ Ioo a b`
with `f s > f b`. -/
TheoremDoc exist_gt as "exist_gt" in "Shade"

Statement exist_gt {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b) (h : f a > f b) :
    ∃ s ∈ Set.Ioo a b, f s > f b := by
  Hint "The intermediate value theorem `intermediate_value_Ioo'` tells you that the interval
  `Ioo (f b) (f a)` is contained in the image `f '' Ioo a b`. Establish that inclusion first."
  have as2 : Set.Ioo (f b) (f a) ⊆ f '' Set.Ioo a b := by
    apply intermediate_value_Ioo'
    linarith
    exact hf.continuousOn
  Hint "The interval `Ioo (f b) (f a)` is nonempty: its midpoint works."
  have set_not_empty : (Set.Ioo (f b) (f a)).Nonempty := by
    use (f b + f a) / 2
    constructor
    linarith
    linarith
  obtain ⟨z, hz⟩ := set_not_empty
  have hz' := hz
  apply as2 at hz
  simp at hz
  choose zz hzz using hz
  use zz
  constructor
  simp [hzz]
  obtain ⟨h1, h2⟩ := hzz
  simp at hz'
  obtain ⟨hh1, hh2⟩ := hz'
  simp
  rw [← h2] at hh1
  assumption

Conclusion "Conclusion LightAndShade L02: saved as `exist_gt`."

TheoremTab "Shade"
