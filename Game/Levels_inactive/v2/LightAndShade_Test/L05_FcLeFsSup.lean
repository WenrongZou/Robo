import Game.Levels_inactive.v2.LightAndShade_Test.L04_ShadeSetBddAbove

World "LightAndShade"
Level 5

Title "The Sup Stays High"

Introduction "Intro LightAndShade L05: the value at the supremum is not below `f c`.

Let `d = sSup (shadeSet f c b)`.  Although `d` itself need not belong to the set, it lies in its
*closure*.  The condition `f c ≤ f x` defines a **closed** set (continuity of `f`), and it holds on
all of `shadeSet f c b`; therefore it persists at `d`.  Conclusion: `f c ≤ f d`.
"

open Set

/-- The value of `f` at the supremum of `shadeSet f c b` is at least `f c`. -/
TheoremDoc fc_le_fsSup as "fc_le_fsSup" in "Shade"

Statement fc_le_fsSup {f : ℝ → ℝ} {b c : ℝ} (hf : Continuous f)
    (hne : (shadeSet f c b).Nonempty) :
    f c ≤ f (sSup (shadeSet f c b)) := by
  -- Hint "Recall the set is bounded above by the previous level: `shadeSet_bddAbove f c b`."
  -- have hd : BddAbove (shadeSet f c b) := shadeSet_bddAbove f c b
  -- Hint "The supremum lies in the closure of the set. `(isLUB_csSup hne hd).mem_closure hne`
  -- gives exactly `sSup (shadeSet f c b) ∈ closure (shadeSet f c b)`."
  -- have hd_closure : sSup (shadeSet f c b) ∈ closure (shadeSet f c b) :=
  --   (isLUB_csSup hne hd).mem_closure hne
  -- Hint "The set of points where `f c ≤ f x` is closed because `f` is continuous (`isClosed_le`),
  -- and `shadeSet f c b` is contained in it. Conclude with `closure_minimal`."
  -- have hclosed : IsClosed {x : ℝ | f c ≤ f x} := isClosed_le continuous_const hf
  have hsub : shadeSet f c b ⊆ {x | f c ≤ f x} := fun x hx => le_of_lt hx.2
  apply closure_minimal hsub
  · apply isClosed_le
    apply continuous_const
    assumption
  · apply csSup_mem_closure hne ?_
    apply shadeSet_bddAbove f c b

Conclusion "Conclusion LightAndShade L05: saved as `fc_le_fsSup`."

TheoremTab "Shade"
