import Game.Metadata

World "Piazza"
Level 10

Title ""

/-
Introduction "
**Ritha** (*zu Lina*):  Bitte, lass mich doch auch noch eine Frage stellen …

**Lina**:  Okay, eine einzige …  Aber nicht wieder zu `omega`!

Ritha macht große Augen und sieht Lina flehend an.

**Lina**:  Wenns *unbedingt* sein muss.  Aber mach schnell! Wir haben jetzt wirklich keine Zeit mehr!
"
-/
Introduction "Intro Luna L10: Use `omega` again"

/---/
TheoremDoc Finset.Icc_subset_Icc_iff as "Icc_subset_Icc_iff" in "≤"
-- Note that mathlib's theorem is more general; here we restrict to ℕ

namespace Finset

Statement Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ) :
a₁ ≤ b₁ →  (Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂) := by
  -- unfold Icc -- optional
  /-
  Hint (hidden := true) "
    **Robo**: Vielleicht hilft hier mal wieder `subset_iff`.  Und wenn gar nichts geht, probier mal `simp`.
    "
  -/
  Hint "Try using `subset_iff` and if nothing else helps, `simp`"
  rw [subset_iff]
  simp
  grind

NewTheorem Set.subset_iff

NewDefinition Finset.Icc

Conclusion ""
