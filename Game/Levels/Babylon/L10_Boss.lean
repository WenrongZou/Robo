import Game.Metadata

import Game.Levels.Babylon.L09_Induction3_sub_insert3

World "Babylon"
Level 10
Title ""

/-
Introduction
"
Ihr seid noch nicht weit gegangen, da kommt hinter einem Turm plötzlich ein besonders großer Babylonier hervor,
stellt sich euch in den Weg, schaut euch finster an und fordert in tiefer Stimme einen Beweis der
folgenden Gleichung.
"
-/
Introduction "Intro Babylon L09"

open Finset

-- open BigOperators


Statement (m : ℕ) : (∑ i ∈ Icc 0 m, (i : ℚ) ^3) = (∑ i ∈  Icc 0 m, i : ℚ)^2 := by
  /- Hint "**Du**: Naja. Das wird schon klappen … " -/
  Hint "this should work"
  induction m with n n_ih
  · simp
  · rw [← insert_Icc_right_eq_Icc_add_one]
    ·
      -- here we could use `grind [arithmetic_sum]`.
      rw [sum_insert]
      · simp
        rw [n_ih]
        /-
        Hint (hidden := true) "
          **Robo**:  Denk daran, dass wir schon `arithmetic_sum` bewiesen hatten.
        "
        -/
        Hint (hidden := true) "Use `arithmetic_sum` as its already proven"
        rw [arithmetic_sum]
        grind

        -- simp
        -- ring
      · simp
    · grind

TheoremTab "∑ Π"

/-
Conclusion "Der Babylonier denkt ganz lange nach, und ihr bekommt das Gefühl, dass er gar nie
aggressiv war, sondern nur eine sehr tiefe Stimme hat.

Mit einem kleinen Erdbeben setzt er sich hin und winkt euch dankend zu."
-/
Conclusion "Conclusion Babylon L09"
