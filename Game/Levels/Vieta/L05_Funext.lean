import Game.Metadata


World "Vieta"
Level 5

Title "" -- "funext"

/-
Introduction
"
Vieta sieht sich vorsichtig um, bleibt dann aber doch stehen.
Er reicht euch ruhig das nächste Blatt.
"
-/
Introduction "Intro Vieta L05"

open Function

Statement {n : ℕ} (h : Even n) :
    let f := fun (x : ℤ) ↦ x ^ n;
    let g := fun x ↦ f (-x);
    f = g := by
    /-
  Hint"**Du**: Per Definition sind doch zwei Abbildungen gleich, wenn sie angewendet auf
jedes Element den gleichen Wert haben …

**Robo**: Zu dem Prinzip hätte ich die Taktik `funext` auf Lager.
Mit `funext x` wählst du ein beliebiges `x` und änderst das Beweisziel von `f = g` zu `f x = g x`."
-/
  Hint "Try `funext`. Explain `funext x` as taking arbitrary `x` and changing goal from `f = g` to `f x = g x`"
  /- here we could use `grind -ext`. `grind -ext` will not closed the goal before `funext`. -/
  -- Here: `grind` will not closed the goal. See `GameMeta/Tactics/Grind.lean`.
  funext x
  unfold g f
  rw [Even.neg_pow]
  assumption

  -- -- Hint (hidden := true) "**Robo**: Zur Erinnerung, `ring` sieht durch lokale Definition hindurch."
  -- Hint (hidden := true) "Remind: `ring` sees through local definitions"
  -- ring

OnlyTactic funext
NewTactic funext
TheoremTab "Function"

Conclusion ""
