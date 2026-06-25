import Game.Levels_inactive.v2.LightAndShade_Test.L07_FsSupEqFc

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
  · Hint "Now `f b < f a`. Use `exist_gt` to grab `c ∈ Ioo a b` with `f c > f b`."
    obtain ⟨c, hc_mem, hc_gt⟩ := exist_gt hf hab h
    Hint "Since `c` lies between `a` and `b`, the assumption `h₀` makes it a shadow point."
    have hc_shade : c ∈ Shade f := h₀ c hc_mem
    Hint "Feed this to `shadeSet_nonempty` to learn the set `shadeSet f c b` is nonempty."
    have hne : (shadeSet f c b).Nonempty := shadeSet_nonempty hb hc_gt hc_shade
    Hint "Name the supremum: `set d := sSup (shadeSet f c b) with hd_def`."
    set d := sSup (shadeSet f c b) with hd_def
    have hbd : BddAbove (shadeSet f c b) := shadeSet_bddAbove f c b
    Hint "Basic bounds: `c < d` (some set element sits below `d`) and `d ≤ b`."
    have hcd : c < d := by
      obtain ⟨x0, hx0⟩ := hne
      exact lt_of_lt_of_le hx0.1.1 (le_csSup hbd hx0)
    have hdb : d ≤ b := csSup_le hne (fun x hx => hx.1.2.le)
    Hint "Level 7 pins the value at the supremum: `fsSup_eq_fc hf hc_gt hne` gives `f d = f c`."
    have fd_eq : f d = f c := fsSup_eq_fc hf hc_gt hne
    have hdb_lt : d < b := by
      rcases lt_or_eq_of_le hdb with h' | h'
      · exact h'
      · -- grind
        exfalso; rw [h'] at fd_eq; linarith
    have h_lt : ∀ x ∈ Set.Ioo d b, f x ≤ f c := f_le_fc_right hne
    Hint "Show `d` is not a shadow point: any `t > d` with `f t > f d = f c` is impossible. Split on
    where `t` sits relative to `b` (use `h_lt`, the `t = b` case, and `not_mem_shade hb`)."
    have d_not_mem : d ∉ Shade f := by
      rintro ⟨t, htd, htf⟩
      rw [fd_eq] at htf
      rcases lt_trichotomy t b with htb | htb | htb
      · exact absurd (h_lt t ⟨htd, htb⟩) (not_le.mpr htf)
      · rw [htb] at htf; linarith
      · have := not_mem_shade hb t htb
        linarith
    Hint "But `d ∈ Ioo a b`, so `h₀ d` forces `d` to be a shadow point — contradiction."
    have d_mem : d ∈ Set.Ioo a b := ⟨lt_trans hc_mem.1 hcd, hdb_lt⟩
    obtain d_shade := h₀ _ d_mem
    contradiction

Conclusion "Conclusion LightAndShade L08: the boss is defeated — `f a = f b`. Planet complete!"

TheoremTab "Shade"
