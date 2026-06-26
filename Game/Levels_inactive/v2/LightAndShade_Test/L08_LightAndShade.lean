import Game.Levels_inactive.v2.LightAndShade_Test.L07_Lt_sSup_shadeSet

World "LightAndShade"
Level 8

Title "Light and Shade"

Introduction "Intro LightAndShade L08 (BOSS): the full theorem.

This is the final challenge of the planet.  Let `f` be continuous and `a < b`.  Suppose neither `a`
nor `b` is a shadow point, yet **every** point strictly between them is.  Then `f a = f b`.

You have built all the pieces:

* `exist_gt` — finds a high point `c` (level 2),
* `shadeSet_nonempty` / `shadeSet_bddAbove` — make `d = sSup (shadeSet f c b)` available (levels 3–4),
* `fsSup_eq_fc` — gives `f d = f c` (level 7),
* `f_le_fc_right` and `not_mem_shade` — show `d` is *not* a shadow point (levels 6, 1).

The contradiction: `d` lies strictly between `a` and `b`, so by assumption it *must* be a shadow
point.  Assemble the argument.
"

open Set

/-- **Light and Shade.** If `f` is continuous, `a < b`, neither `a` nor `b` is a shadow point, but
every point strictly between `a` and `b` is a shadow point, then `f a = f b`. -/
TheoremDoc light_and_shade as "light_and_shade" in "Shade"

Statement light_and_shade {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b)
    (ha : a ∉ Shade f) (hb : b ∉ Shade f)
    (h₀ : ∀ k ∈ Set.Ioo a b, k ∈ Shade f) : f a = f b := by
  Hint "Compare `f a` and `f b` by trichotomy: `obtain h | h | h := lt_trichotomy (f a) (f b)`."
  obtain h | h | h := lt_trichotomy (f a) (f b)
  · Hint "If `f a < f b`, then `b` witnesses that `a` is a shadow point, contradicting `ha`."
    have a_mem : a ∈ Shade f := by
      use b
    contradiction
  · exact h
  · /- Hint: Level 2, use lemma exist_gt. -/
    obtain ⟨c, hc_mem, hc_gt⟩ := exist_gt hf hab h
    /- Hint: by assumption h₀, we have that `c ∈ Shade f`. -/
    have hc_shade : c ∈ Shade f := h₀ c hc_mem
    /- Hint: Level 3, shadeSet is non empty. -/
    have hne : (shadeSet f c b).Nonempty := shadeSet_nonempty hb hc_gt hc_shade
    Hint "Name the supremum: `set d := sSup (shadeSet f c b) with hd_def`."
    set d := sSup (shadeSet f c b) with hd_def
    /- Hint: Level 4, shadeSet is bounded above. -/
    have hbd : BddAbove (shadeSet f c b) := shadeSet_bddAbove f c b
    /- Make this as a seperate level to replace level 7. -/
    obtain hcd := lt_sSup_shadeSet hb hc_gt hc_shade
    have hdb : d ≤ b := csSup_le hne (fun x hx => hx.1.2.le)
    /- Level 5. -/
    have fc_le : f c ≤ f d := fc_le_fsSup hf hne
    /- Level 6. -/
    have h_lt : ∀ x ∈ Set.Ioo d b, f x ≤ f c := f_le_fc_right hne
    have d_not_mem : d ∉ Shade f := by
      intro h
      obtain ⟨t, htd, htf⟩ := h
      have htf' : f t > f c := by grind
      obtain htb | htb | htb := lt_trichotomy t b
      · grind
      · grind
      · have := not_mem_shade hb t htb
        grind
    have d_mem : d ∈ Set.Ioo a b := by grind
    obtain d_shade := h₀ _ d_mem
    contradiction
    -- Hint "Level 7 pins the value at the supremum: `fsSup_eq_fc hf hc_gt hne` gives `f d = f c`."
    -- have fd_eq : f d = f c := fsSup_eq_fc hf hc_gt hne
    -- have hdb_lt : d < b := by
    --   rcases lt_or_eq_of_le hdb with h' | h'
    --   · exact h'
    --   · -- grind
    --     exfalso; rw [h'] at fd_eq; linarith
    -- have h_lt : ∀ x ∈ Set.Ioo d b, f x ≤ f c := f_le_fc_right hne
    -- Hint "Show `d` is not a shadow point: any `t > d` with `f t > f d = f c` is impossible. Split on
    -- where `t` sits relative to `b` (use `h_lt`, the `t = b` case, and `not_mem_shade hb`)."
    -- have d_not_mem : d ∉ Shade f := by
    --   rintro ⟨t, htd, htf⟩
    --   rw [fd_eq] at htf
    --   rcases lt_trichotomy t b with htb | htb | htb
    --   · exact absurd (h_lt t ⟨htd, htb⟩) (not_le.mpr htf)
    --   · rw [htb] at htf; linarith
    --   · have := not_mem_shade hb t htb
    --     linarith
    -- Hint "But `d ∈ Ioo a b`, so `h₀ d` forces `d` to be a shadow point — contradiction."
    -- have d_mem : d ∈ Set.Ioo a b := ⟨lt_trans hc_mem.1 hcd, hdb_lt⟩
    -- obtain d_shade := h₀ _ d_mem
    -- contradiction

Conclusion "Conclusion LightAndShade L08: the boss is defeated — `f a = f b`. Planet complete!"

TheoremTab "Shade"
