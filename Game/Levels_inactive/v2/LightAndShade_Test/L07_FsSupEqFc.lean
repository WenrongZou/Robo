import Game.Levels_inactive.v2.LightAndShade_Test.L06_FLeFcRight

World "LightAndShade"
Level 7

Title "Equality at the Sup"

Introduction "Intro LightAndShade L07: pin down the value at the supremum.

Combine the previous two levels.  From level 5 we have `f c ≤ f d`.  We also know `d < b` (otherwise
`f d = f b < f c ≤ f d`).  By level 6, `f ≤ f c` on `Ioo d b`, and `d` lies in the closure of that
interval, so `f d ≤ f c`.  The two inequalities give `f d = f c`.
"

open Set

/-- The value of `f` at the supremum equals `f c`. -/
TheoremDoc fsSup_eq_fc as "fsSup_eq_fc" in "Shade"

Statement fsSup_eq_fc {f : ℝ → ℝ} {b c : ℝ} (hf : Continuous f)
    (hbc : f b < f c) (hne : (shadeSet f c b).Nonempty) :
    f (sSup (shadeSet f c b)) = f c := by
  set d := sSup (shadeSet f c b) with hd_def
  Hint "Level 5 gives `f c ≤ f d` directly: `fc_le_fsSup hf hne`."
  have hfc_le_fd : f c ≤ f d := fc_le_fsSup hf hne
  Hint "The supremum is at most `b`, since every element of the set is below `b`:
  `csSup_le hne (fun x hx => hx.1.2.le)`."
  have hdb : d ≤ b := csSup_le hne (fun x hx => hx.1.2.le)
  Hint "Upgrade to the strict bound `d < b`: if `d = b` then `f d = f b < f c ≤ f d`, impossible."
  have hdb_lt : d < b := by
    rcases lt_or_eq_of_le hdb with h' | h'
    · exact h'
    · exfalso; rw [h'] at hfc_le_fd; linarith
  Hint "Level 6 controls `f` to the right of `d`: `f_le_fc_right hne`."
  have h_lt : ∀ x ∈ Set.Ioo d b, f x ≤ f c := f_le_fc_right hne
  Hint "It remains to show `f d ≤ f c`; combined with `hfc_le_fd` use `le_antisymm`."
  refine le_antisymm ?_ hfc_le_fd
  have hclosed : IsClosed {x : ℝ | f x ≤ f c} := isClosed_le hf continuous_const
  have hsub : Set.Ioo d b ⊆ {x : ℝ | f x ≤ f c} := h_lt
  Hint "`d` lies in the closure of `Ioo d b` (use `closure_Ioo` with `d ≠ b`), so the bound
  `f ≤ f c` extends to `d` via `closure_minimal`."
  have hd_cl : d ∈ closure (Set.Ioo d b) := by
    rw [closure_Ioo (ne_of_lt hdb_lt)]
    exact ⟨le_refl d, hdb_lt.le⟩
  exact closure_minimal hsub hclosed hd_cl

Conclusion "Conclusion LightAndShade L07: saved as `fsSup_eq_fc`."

TheoremTab "Shade"
