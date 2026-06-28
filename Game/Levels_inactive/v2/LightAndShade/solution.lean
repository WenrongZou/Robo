import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic

/-
23. Light and Shadow (Shade?). Let f : ℝ → ℝ be a continuous function. A real number s is called a
    shadow point of f if there exists a real number t with t > s and f(t) > f(s). If a and b with a
    < b are themselves not shadow points, but every s between a and b is a shadow point, then f(a) =
    f(b). (Hint: Assume f(a) > f(b). Then one can find an s between a and b with f(c) > f(b). To
    arrive at a contradiction, one can consider the supremum of {t ∈ ]c, b[ | f(t) > f(c)}.)-/

variable {f : ℝ → ℝ} {a b : ℝ}

open Set

variable (f) in
def Shade : Set ℝ := {s : ℝ | ∃ t > s, f t > f s}

lemma exist_gt (hf : Continuous f) (hab : a < b) (h : f a > f b) :
    ∃ s ∈ Ioo a b, f s > f b := by
  -- old solution.
  have as2: Set.Ioo (f b) (f a) ⊆ f '' Set.Ioo a b := by
    apply intermediate_value_Ioo'
    linarith
    exact Continuous.continuousOn hf
  have set_not_empty : (Set.Ioo (f b) (f a)).Nonempty := by
    use (f b + f a) / 2
    grind
  obtain ⟨z, hz⟩ := set_not_empty
  have hz' := hz
  apply as2 at hz
  choose zz hzz using hz
  use zz
  grind
  -- sorry

lemma not_mem_shade (h : a ∉ Shade f) (x : ℝ) (h_lt : a < x) : f x ≤ f a := by
  by_contra hcon
  /- should we introduce `by_contra!` here. if we do so them we can remove
  `simp at hcon`.  -/
  simp at hcon
  exact h ⟨x, h_lt, hcon⟩

example (hf : Continuous f) (hab : a < b) (ha : a ∉ Shade f) (hb : b ∉ Shade f)
   (h₀ : ∀ k ∈ Set.Ioo a b, k ∈ Shade f) : f a = f b := by
  obtain h | h | h := lt_trichotomy (f a) (f b)
  · have p : a ∈ Shade f := by
      use b
    contradiction
  · assumption
  ·
    obtain ⟨c, hc⟩ := exist_gt hf hab h
    -- `hc.1 : c ∈ Ioo a b`, `hc.2 : f c > f b`.
    let s : Set ℝ := {t ∈ Set.Ioo c b | f c ≤ f t}
    /- `d` is the supremum of `{t ∈ (c, b) | f c ≤ f t}`. -/
    have hd : BddAbove s := by
      refine bddAbove_def.mpr ?_
      use b
      grind
    have hs_nonempty : s.Nonempty := by
      -- `c` lies strictly between `a` and `b`, hence is a shadow point.
      obtain ⟨t₀, ht₀_gt, ht₀_f⟩ := h₀ c hc.1
      -- `ht₀_gt : t₀ > c`, `ht₀_f : f t₀ > f c`. We show `t₀ < b`, so `t₀ ∈ s`.
      have ht₀_lt : t₀ < b := by
        rcases lt_trichotomy t₀ b with hlt | heq | hgt
        · exact hlt
        · -- `t₀ = b` would give `f b > f c`, contradicting `f c > f b`.
          grind
        · -- `t₀ > b` with `f t₀ > f c > f b` makes `b` a shadow point.
          by_contra
          apply hb
          use t₀
          grind
      use t₀
      grind
    let d := sSup s
    -- `b` is not a shadow point, so `f` never exceeds `f b` to the right of `b`.
    have h1 : ∀ x, b < x → f x ≤ f b := not_mem_shade hb
    -- Basic bounds on `d = sSup s`.
    have hcd : c < d := by
      obtain ⟨x, hx⟩ := hs_nonempty
      exact lt_of_lt_of_le hx.1.1 (le_csSup hd hx)
    have hdb : d ≤ b := by
      apply csSup_le hs_nonempty
      intro x hx
      exact le_of_lt hx.1.2
    -- `f c ≤ f d`: `d` lies in the closure of `s`, on which `f c ≤ f`.
    -- have isClosed_s : IsClosed s := isClosed_le continuous_const hf
    have hfc_le_fd : f c ≤ f d := by
      have hsub : s ⊆ {x | f c ≤ f x} := sep_subset_setOf _ _
      apply closure_minimal hsub
      exact isClosed_le continuous_const hf
      exact csSup_mem_closure hs_nonempty hd
      -- have hd_closure : d ∈ closure s :=
      --   (isLUB_csSup hs_nonempty hd).mem_closure hs_nonempty
      -- have hclosed : IsClosed {x : ℝ | f c ≤ f x} := isClosed_le continuous_const hf
      -- have hsub : s ⊆ {x | f c ≤ f x} := fun x hx => mem_of_mem_inter_right hx
      -- exact closure_minimal hsub hclosed hd_closure
    -- Hence `d < b` strictly: otherwise `f d = f b < f c ≤ f d`.
    have hdb_lt : d < b := by
      grind
      -- rcases lt_or_eq_of_le hdb with h' | h'
      -- · exact h'
      -- · grind
    -- Just to the right of `d` (but below `b`), `f` stays `≤ f c`.
    have h_lt : ∀ x ∈ Ioo d b, f x ≤ f c := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have not_mem : x ∉ s := notMem_of_csSup_lt hx1 hd
      by_contra hcon
      have : x ∈ s := by
        grind
      contradiction
      -- exact not_mem ⟨⟨lt_trans hcd hx1, hx2⟩, not_le.mp hcon⟩
    have d_not_mem : d ∉ Shade f := by
      intro h
      obtain ⟨t, htd, htf⟩ := h
      grind
      -- have htf' : f t > f c := by grind
      -- obtain htb | htb | htb := lt_trichotomy t b
      -- · grind
      -- · grind
      -- · have := not_mem_shade hb t htb
      --   grind
    have d_mem : d ∈ Set.Ioo a b := by grind
    obtain d_shade := h₀ _ d_mem
    contradiction


/- Some theorem or definition we need to discuss in this section.

For set: BddAbove, bddAbove_def, sep_subset_setOf

closed set: isClosed_le, closure_minimal, csSup_mem_closure

sSup: le_csSup, csSup_le, csSup_mem_closure
-/
