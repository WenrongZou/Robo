import Game.MetaData

World "Shade"
Level 1

open Set

Statement {a b : ℝ} {p : ℝ → Prop} :
    BddAbove {x ∈ Ioo a b | p x} := by
  apply bddAbove_def.mp
  use b
  simp [upperBounds]
  grind

/-- -/
DefinitionDoc BddAbove as "BddAbove" in "Set"
NewDefinition BddAbove

/-- -/
TheoremDoc bddAbove_def as "bddAbove_def" in "Set"
NewTheorem bddAbove_def
