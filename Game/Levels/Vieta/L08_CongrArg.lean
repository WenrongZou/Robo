import Game.Metadata


World "Vieta"
Level 8

Title "" -- "congrArg"

/-
Introduction
"Die Kampfgeräusche kommen näher. Vieta gibt euch zwei weitere Blätter."
-/
Introduction "Intro Vieta L08"

open Function

Statement {x : ℤ} (f : ℤ → ℤ) :
    let g : ℤ → ℤ := fun x ↦ x + 3;
    f (g 0) = f 3 := by
  /-
  Hint "**Robo**: Oh, das ist ein Fall für `congrArg`.  Wenn du schon weiß, dass `x = y`, erhälst du
 `f x = f y` mit `apply congrArg`."
  -/
  Hint "Try `congrArg`. If `x = y`, then `f x = f y` when using `apply congrArg`"
  apply congrArg
  rfl

/---/
TheoremDoc congrArg as "congrArg" in "Function"

OnlyTactic apply rfl
NewTheorem congrArg -- tactic `congr` would have same effect
TheoremTab "Function"

Conclusion ""
