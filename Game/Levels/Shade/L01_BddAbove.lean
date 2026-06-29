import Game.MetaData

World "Shade"
Level 1

open Set

Statement {a b : ℝ} {p : ℝ → Prop} :
    BddAbove {x ∈ Ioo a b | p x} := by
  Hint "[Hint bdad] `rw` theorem `bddAbove_def` to translate the problem. "
  rw [bddAbove_def]
  use b
  grind

/-- -/
DefinitionDoc BddAbove as "BddAbove" in "Set"
NewDefinition BddAbove

/-- -/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def
