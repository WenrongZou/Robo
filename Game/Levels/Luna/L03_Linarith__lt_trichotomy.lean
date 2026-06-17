import Game.Metadata


open Nat

World "Luna"
Level 3

Title ""

/-
Introduction
"
**Lina**: Probierts doch mal hiermit!
"
-/
Introduction "Intro Luna L03"

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"


Statement lt_trichotomy: ∀ a b : ℝ, a < b ∨ a = b ∨ b < a := by
  grind

TheoremTab "≤"

/-
Conclusion "
  **Lina**:  Ihr hättet übrigens auch einfach `apply lt_trichotomy` sagen können.
"
-/
Conclusion "Conclusion Luna L03: Alternatively `apply lt_trichotomy` could have been used."
