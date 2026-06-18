import Game.Metadata

World "Babylon"
Level 6

Title ""

/-
Introduction
"
  Auf der nächsten Bodenplatte sind viele Steine in einer Reihe eingraviert.
  Bis auf einen einzigen tragen sie alle den Wert $0$ — nur der $k$-te trägt den Wert $a$.
  Die Inschrift behauptet, dass die Summe über die ganze Reihe einfach $a$ ergibt.
"
-/
Introduction "Intro Babylon L06"

open Finset

Statement (n k : ℕ) (hk : k < n) (a : ℤ) :
    ∑ i ∈ range n, (if i = k then a else 0) = a := by
  /-
  Hint "**Du**:  In dieser Summe verschwinden alle Summanden bis auf den einen bei `i = {k}`.
  Wie sammle ich den einen heraus?

  **Robo**:  Dafür gibt es `sum_eq_single`:  Ist `{k}` der einzige Index, an dem der Summand
  nicht verschwindet, so ist die ganze Summe gleich dem Wert an dieser Stelle.
  Probier `rw [sum_eq_single {k}]`."
  -/
  Hint "Every term vanishes except the one at `i = {k}`. Use `sum_eq_single`: if `{k}` is the only index
  where the term does not vanish, the whole sum equals the term there. Try `rw [sum_eq_single {k}]`"
  rw [sum_eq_single k]
  -- Hauptziel: der Summand bei `{k}` ist `a`.
  -- Hint (hidden := true) "**Robo**:  `if {k} = {k}` ist natürlich wahr — `simp` räumt das weg."
  · Hint (hidden := true) "`if k = k` is true, so `simp` closes this"
    simp
  -- Nebenziel: für alle `b ≠ {k}` verschwindet der Summand.
  · -- Hint (hidden := true) "**Robo**:  Hier ist `b ≠ {k}`, also `if b = {k}` falsch.  `simp [...]`."
    Hint (hidden := true) "Here `b ≠ k`, so the condition is false. Try `intro b _ hbk` and then `simp [hbk]`"
    intro b _ hbk
    simp [hbk]
  -- Nebenziel: `{k}` liegt in `range {n}`, also tritt dieser Fall nicht ein.
  · -- Hint (hidden := true) "**Robo**:  `{k} ∉ range {n}` widerspricht `{k} < {n}`.  `simp` und `omega`."
    Hint (hidden := true) "`k ∉ range n` contradicts `k < n`. Try `intro h`, `simp [mem_range] at h` and `omega`"
    intro h
    simp [mem_range] at h
    omega

/---/
TheoremDoc Finset.sum_eq_single as "sum_eq_single" in "∑ Π"
NewTheorem Finset.sum_eq_single

TheoremTab "∑ Π"

/-
Conclusion "
  **Babylonier**:  Ein einzelner Stein trägt den ganzen Turm — fast wie bei uns!
"
-/
Conclusion "Conclusion Babylon L06"
