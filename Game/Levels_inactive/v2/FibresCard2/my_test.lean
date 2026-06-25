import Mathlib

import Mathlib

open Function Set

lemma ncard_eq_two_lt {s : Set ℝ} :
  s.ncard = 2 ↔ (∃ x y, x < y ∧ s = {x, y}) := by
  rw [ncard_eq_two]
  constructor
  · intro ⟨x, y, hx1, hx2⟩
    by_cases h : x < y
    · use x, y
    · use y, x
      grind
  grind

lemma my_not_two_set {S : Set ℝ} [hSf : Finite S] {x₁ x₂ x₃ : ℝ} (h1 : x₁ ∈ S) (h2 : x₂ ∈ S)
    (h3 : x₃ ∈ S) (h12: x₁ < x₂) (h23: x₂ < x₃) : ncard S ≠ 2 := by
  intro hS
  have h_lt : 2 < S.ncard := by
    rw [two_lt_ncard]
    exact ⟨x₁, h1, x₂, h2, x₃, h3, ne_of_lt h12, ne_of_lt (h12.trans h23), ne_of_lt h23⟩
  grind

lemma my_second_element {A : Type} {S : Set A} {a : A} (h : ncard S = 2) (ha : a ∈ S) :
    ∃ b ∈ S, b ≠ a := by
  rw [ncard_eq_two] at h
  obtain ⟨x, y, neq, S_eq⟩ := h
  simp [S_eq]
  grind

lemma getPreimage {f : ℝ → ℝ} (hf1 : Continuous f) :
    ∀ a b, a < b → ∀ y, y ∈ Set.uIcc (f a) (f b) → f a ≠ y → f b ≠ y →
      ∃ c, a < c ∧ c < b ∧ f c = y := by
  intro a b hab y hy fa fb
  obtain ⟨c, hc, hcy⟩ := intermediate_value_uIcc (f := f) hf1.continuousOn hy
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hc
  grind

lemma cross {f : ℝ → ℝ} (hf1 : Continuous f) (a b c : ℝ) (hab : a < b) :
    (f a = 0 ∧ f b = f c) ∨ (f a = f c ∧ f b = 0) →
      ∀ y, 0 < y → y < f c → ∃ c, a < c ∧ c < b ∧ f c = y := by
  intro hval y hy0 hyM
  refine getPreimage hf1 a b hab y ?_ ?_ ?_
  <;> grind [Set.mem_uIcc]

lemma three_preimages {f : ℝ → ℝ} (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {a b c y : ℝ} :
    a < b → b < c → f a = y → f b = y → f c = y → False := by
  intro hab hbc fa fb fc
  have hsub : ({a, b, c} : Set ℝ) ⊆ f ⁻¹' {y} := by grind
  have hfin : (f ⁻¹' {y}).Finite := by
    obtain ⟨p, q, -, hPQ⟩ := Set.ncard_eq_two.mp (hf2 y)
    simp [hPQ]
  have h3 : ({a, b, c} : Set ℝ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩
  have hle := Set.ncard_le_ncard hsub hfin
  rw [h3, hf2 y] at hle
  grind

lemma exist_nonneg {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
    (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≤ 0 := by
  by_contra! hc
  have h_max : ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
    apply IsCompact.exists_isMaxOn isCompact_Icc (nonempty_Icc.mpr (le_of_lt hx_lt))
    exact Continuous.continuousOn hf1
  obtain ⟨xmax, h_max, h_max_at_xmax⟩ := h_max
  rw [isMaxOn_iff] at h_max_at_xmax
  /- `f x₁ = 0` and `f x₂ = 0`. -/
  have fx₁_zero : f x₁ = 0 := by
    have : x₁ ∈ f ⁻¹' {0} := by simp [hx]
    simpa using this
  have fx₂_zero : f x₂ = 0 := by
    have : x₂ ∈ f ⁻¹' {0} := by simp [hx]
    simpa using this
  have hmid_pos : 0 < f ((x₁ + x₂) / 2):= by
    -- Here can be directly proved by `grind`, but I think it is better to do it using apply hc
    apply hc
    grind
  have hMpos : 0 < f xmax := by grind
  have xmax_Ioo : x₁ < xmax ∧ xmax < x₂ := by grind
  have : xmax ∈ f⁻¹' {f xmax} := by rfl
  /- Here: `x₃` is another preimage of `f xmax`. -/
  obtain ⟨x₃, x₃_mem, x₃_neq⟩ := my_second_element (hf2 _) this
  /- Here: `y₀` is a half of the "peak" `f xmax`. -/
  let y₀ := f xmax / 2
  have y₀_pos : 0 < y₀ := by grind
  have y₀_lt : y₀ < f xmax := by grind
  obtain ⟨a, ha₁, ha₂, hfa⟩ := cross hf1 x₁ _ _ xmax_Ioo.1 (Or.inl ⟨fx₁_zero, rfl⟩) y₀ y₀_pos y₀_lt
  obtain ⟨b, hb₁, hb₂, hfb⟩ := cross hf1 _ x₂ _ xmax_Ioo.2 (Or.inr ⟨rfl, fx₂_zero⟩) y₀ y₀_pos y₀_lt
  /- case 1: `x₃ < x₁`. -/
  by_cases h_lt : x₃ < x₁
  · /- a third preimage of `y₀` lies in `(x₃, x₁)`, left of `a`. -/
    obtain ⟨c, hc1, hc2, hfc⟩ := cross hf1 x₃ x₁ _ h_lt (Or.inr ⟨x₃_mem, fx₁_zero⟩) y₀ y₀_pos y₀_lt
    exact three_preimages hf2 (by linarith) (by linarith) hfc hfa hfb
  /- case 1: `x₂ < x₃`. -/
  by_cases h_gt : x₂ < x₃
  · /- a third preimage of `y₀` lies in `(x₂, x₃)`, left of `b`. -/
    obtain ⟨c, hc1, hc2, hfc⟩ := cross hf1 x₂ x₃ _ h_gt (Or.inl ⟨fx₂_zero, x₃_mem⟩) y₀ y₀_pos y₀_lt
    exact three_preimages hf2 (by linarith) (by linarith) hfa hfb hfc
  /- the rest case: `x₃` inside the interval `[x₁, x₂]`. -/
  let t₀ := (x₃ + xmax) / 2
  have t₀_mem : t₀ ∈ Ioo x₁ x₂ := by grind
  have t₀_mem' : x₁ < t₀ ∧ t₀ < x₂ := t₀_mem
  have x₃_mem_Ioo : x₃ ∈ Ioo x₁ x₂ := by grind
  by_cases h_ft₀ : f t₀ = f xmax
  · by_cases x₃_lt : x₃ < xmax
    · refine three_preimages hf2 ?_ ?_  x₃_mem h_ft₀ rfl
      grind
      grind
    refine three_preimages hf2 ?_ ?_  rfl h_ft₀ x₃_mem
    <;> grind
  have ft₀_lt : f t₀ < f xmax := by grind
    -- lt_of_le_of_ne (h_max_at_xmax t₀ t₀_mem) h_ft₀
  have ht₀pos : 0 < f t₀ := hc _ t₀_mem
  by_cases x₃_lt : x₃ < xmax
  · obtain ⟨c, hc1, hc2, hfc⟩ :=
    cross hf1 _ _ _ x₃_mem_Ioo.1 (Or.inl ⟨fx₁_zero, x₃_mem⟩) (f t₀) ht₀pos ft₀_lt
    obtain ⟨d, hd1, hd2, hfd⟩ :=
      cross hf1 _ _ _ xmax_Ioo.2 (Or.inr ⟨rfl, fx₂_zero⟩) (f t₀) ht₀pos ft₀_lt
    refine three_preimages hf2 ?_ ?_ hfc rfl hfd
    grind
    grind
  have x₃_gt : xmax < x₃ := by grind
  obtain ⟨c, hc1, hc2, hfc⟩ :=
    cross hf1 _ _ _ xmax_Ioo.1 (Or.inl ⟨fx₁_zero, rfl⟩) (f t₀) ht₀pos ft₀_lt
  obtain ⟨d, hd1, hd2, hfd⟩ :=
    cross hf1 _ _ _ x₃_mem_Ioo.2 (Or.inr ⟨x₃_mem, fx₂_zero⟩) (f t₀) ht₀pos ft₀_lt
  refine three_preimages hf2 ?_ ?_ hfc rfl hfd
  grind
  grind

lemma exist_nonpos {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
    (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≥ 0 := by
  /- this follows directly from `exist_nonneg` applied to `-f`. -/
  have hf2' : ∀ y, ncard ((-f) ⁻¹' {y}) = 2 := by
    intro y
    have : (-f) ⁻¹' {y} = f ⁻¹' {-y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply, neg_eq_iff_eq_neg]
    simpa [this] using hf2 _
  have hx' : (-f) ⁻¹' {0} = {x₁, x₂} := by
    have : (-f) ⁻¹' {0} = f ⁻¹' {0} := by
      ext x
      simp [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply]
    rw [this]; exact hx
  obtain ⟨x, hx_mem, hx_le⟩ := exist_nonneg (continuous_neg_iff.mpr hf1) hf2' hx_lt hx'
  exact ⟨x, hx_mem, by simpa using hx_le⟩

lemma main_theorem : ¬ ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ y, ncard (f⁻¹' {y}) = 2 := by
  intro ⟨f, hf₁, hf₂⟩
  obtain h₀ := hf₂ 0
  obtain ⟨x₁, x₂, hx, hx_eq⟩ := ncard_eq_two_lt.mp h₀
  have fx₁_zero : f x₁ = 0 := by
    have : x₁ ∈ f ⁻¹' {0} := by simp [hx_eq]
    simpa using this
  have fx₂_zero : f x₂ = 0 := by
    have : x₂ ∈ f ⁻¹' {0} := by simp [hx_eq]
    simpa using this
  /- there is a nonnegative element `c`. -/
  obtain ⟨c, ⟨hc1, hc2⟩, hc_nonneg⟩ := exist_nonneg hf₁ hf₂ hx hx_eq
  by_cases hc₀ : f c = 0
  · exact three_preimages hf₂ hc1 hc2 fx₁_zero hc₀ fx₂_zero
  have fc_neg : f c < 0 := lt_of_le_of_ne hc_nonneg hc₀
  /- there is a nonpositive element `d`. -/
  obtain ⟨d, ⟨hd1, hd2⟩, hc_nonpos⟩ := exist_nonpos hf₁ hf₂ hx hx_eq
  by_cases! hd₀ : f d = 0
  · exact three_preimages hf₂ hd1 hd2 fx₁_zero hd₀ fx₂_zero
  have fd_pos : 0 < f d := lt_of_le_of_ne hc_nonpos hd₀.symm
  /- here use intermediate value lemma to find a element with image zero. -/
  -- `f c < 0 < f d` with `c, d ∈ Ioo x₁ x₂`, so `f` vanishes at some `e` between them,
  -- hence inside `Ioo x₁ x₂`. That makes `e` a third preimage of `0`, contradiction.
  have h0_mem : 0 ∈ Set.uIcc (f c) (f d) :=
    Set.mem_uIcc.mpr (Or.inl ⟨fc_neg.le, fd_pos.le⟩)
  obtain ⟨e, he_mem, he_eq⟩ := intermediate_value_uIcc hf₁.continuousOn h0_mem
  rw [Set.mem_uIcc] at he_mem
  have he_Ioo : x₁ < e ∧ e < x₂ := by grind
  exact three_preimages hf₂ he_Ioo.1 he_Ioo.2 fx₁_zero he_eq fx₂_zero

-- lemma aux {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
--     (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) (h : ∀ x ∈ Ioo x₁ x₂, f x > 0) : False := by
--   -- IsCompact.exists_isMaxOn
--   have h_max : ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
--     apply IsCompact.exists_isMaxOn isCompact_Icc (nonempty_Icc.mpr (le_of_lt hx_lt))
--     exact Continuous.continuousOn hf1
--   obtain ⟨xmax, h_max, h_max_at_xmax⟩ := h_max
--   rw [isMaxOn_iff] at h_max_at_xmax
--   -- No value has three preimages, since every fibre has exactly two points.
--   have three_preimages : ∀ y a b c : ℝ, a < b → b < c →
--       f a = y → f b = y → f c = y → False := by
--     intro y a b c hab hbc fa fb fc
--     have hsub : ({a, b, c} : Set ℝ) ⊆ f ⁻¹' {y} := by grind
--     have hfin : (f ⁻¹' {y}).Finite := by
--       obtain ⟨p, q, -, hPQ⟩ := Set.ncard_eq_two.mp (hf2 y)
--       simp [hPQ]
--     have h3 : ({a, b, c} : Set ℝ).ncard = 3 :=
--       Set.ncard_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩
--     have hle := Set.ncard_le_ncard hsub hfin
--     rw [h3, hf2 y] at hle
--     grind
--   -- A value strictly between `f a` and `f b` is attained strictly inside `(a, b)`.
--   have getpre : ∀ a b : ℝ, a < b → ∀ y, y ∈ Set.uIcc (f a) (f b) → f a ≠ y → f b ≠ y →
--       ∃ c, a < c ∧ c < b ∧ f c = y := by
--     intro a b hab y hy fa fb
--     obtain ⟨c, hc, hcy⟩ := intermediate_value_uIcc (f := f) hf1.continuousOn hy
--     rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hc
--     grind
--   -- The endpoints map to `0`.
--   have hfx1 : f x₁ = 0 := by
--     have : x₁ ∈ f ⁻¹' {0} := by simp [hx]
--     simpa using this
--   have hfx2 : f x₂ = 0 := by
--     have : x₂ ∈ f ⁻¹' {0} := by simp [hx]
--     simpa using this
--   -- The maximum value is positive and attained strictly inside `(x₁, x₂)`.
--   have hmid : (x₁ + x₂) / 2 ∈ Set.Ioo x₁ x₂ := by grind
--   have hMpos : 0 < f xmax := by grind
--   rw [Set.mem_Icc] at h_max
--   have hxmax_Ioo : x₁ < xmax ∧ xmax < x₂ := by
--     grind
--   -- A value `y` strictly between `0` and `f xmax` is hit strictly inside any interval whose
--   -- endpoints take the values `0` and `f xmax` (in either order). This bundles the
--   -- intermediate value theorem with the bookkeeping needed at every use below.
--   have cross : ∀ a b : ℝ, a < b → (f a = 0 ∧ f b = f xmax) ∨ (f a = f xmax ∧ f b = 0) →
--       ∀ y, 0 < y → y < f xmax → ∃ c, a < c ∧ c < b ∧ f c = y := by
--     intro a b hab hval y hy0 hyM
--     refine getpre a b hab y ?_ ?_ ?_
--     <;> grind [Set.mem_uIcc]
--   -- The fibre of `f xmax` has a second point `x₃ ≠ xmax`, also strictly inside `(x₁, x₂)`'s span.
--   obtain ⟨x₃, hx₃ne, hfx₃⟩ : ∃ z, z ≠ xmax ∧ f z = f xmax := by
--     obtain ⟨p, q, hpq, hPQ⟩ := Set.ncard_eq_two.mp (hf2 (f xmax))
--     have hfp : f p = f xmax := by
--       have : p ∈ f ⁻¹' {f xmax} := by rw [hPQ]; simp
--       simpa using this
--     have hfq : f q = f xmax := by
--       have : q ∈ f ⁻¹' {f xmax} := by rw [hPQ]; simp
--       simpa using this
--     have hmem : xmax ∈ ({p, q} : Set ℝ) := by rw [← hPQ]; simp
--     simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
--     grind
--   have hfx3pos : 0 < f x₃ := by grind
--   have hx₃nex1 : x₃ ≠ x₁ := by grind
--   have hx₃nex2 : x₃ ≠ x₂ := by grind
--   -- Two preimages of `y₀ = (f xmax)/2` straddling `xmax`, both inside `(x₁, x₂)`.
--   set y₀ := f xmax / 2 with hy0def
--   have hy0pos : 0 < y₀ := by rw [hy0def]; linarith
--   have hy0lt : y₀ < f xmax := by rw [hy0def]; linarith
--   obtain ⟨a, ha1, ha2, hfa⟩ := cross x₁ xmax hxmax_Ioo.1 (Or.inl ⟨hfx1, rfl⟩) y₀ hy0pos hy0lt
--   obtain ⟨b, hb1, hb2, hfb⟩ := cross xmax x₂ hxmax_Ioo.2 (Or.inr ⟨rfl, hfx2⟩) y₀ hy0pos hy0lt
--   rcases lt_or_ge x₃ x₁ with hL | hL
--   · -- `x₃ < x₁`: a third preimage of `y₀` lies in `(x₃, x₁)`, left of `a`.
--     obtain ⟨c, hc1, hc2, hfc⟩ := cross x₃ x₁ hL (Or.inr ⟨hfx₃, hfx1⟩) y₀ hy0pos hy0lt
--     exact three_preimages y₀ c a b (by linarith) (by linarith) hfc hfa hfb
--   · have hx₁x₃ : x₁ < x₃ := lt_of_le_of_ne hL (Ne.symm hx₃nex1)
--     rcases lt_or_ge x₂ x₃ with hR | hR
--     · -- `x₃ > x₂`: a third preimage of `y₀` lies in `(x₂, x₃)`, right of `b`.
--       obtain ⟨c, hc1, hc2, hfc⟩ := cross x₂ x₃ hR (Or.inl ⟨hfx2, hfx₃⟩) y₀ hy0pos hy0lt
--       exact three_preimages y₀ a b c (by linarith) (by linarith) hfa hfb hfc
--     · -- `x₁ < x₃ < x₂`: a second interior maximizer. Inspect the midpoint `t₀` between them.
--       have hx₃x₂ : x₃ < x₂ := lt_of_le_of_ne hR hx₃nex2
--       have hlohi : min xmax x₃ < max xmax x₃ := by
--         rcases lt_or_gt_of_ne hx₃ne with hlt | hgt
--         · rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact hlt
--         · rw [min_eq_left hgt.le, max_eq_right hgt.le]; exact hgt
--       have flo : f (min xmax x₃) = f xmax := by
--         rcases le_total xmax x₃ with hle | hle
--         · rw [min_eq_left hle]
--         · rw [min_eq_right hle]; exact hfx₃
--       have fhi : f (max xmax x₃) = f xmax := by
--         rcases le_total xmax x₃ with hle | hle
--         · rw [max_eq_right hle]; exact hfx₃
--         · rw [max_eq_left hle]
--       have hlo : x₁ < min xmax x₃ := lt_min hxmax_Ioo.1 hx₁x₃
--       have hhi : max xmax x₃ < x₂ := max_lt hxmax_Ioo.2 hx₃x₂
--       set t₀ := (min xmax x₃ + max xmax x₃) / 2 with ht0def
--       have ht0_lo : min xmax x₃ < t₀ := by rw [ht0def]; linarith
--       have ht0_hi : t₀ < max xmax x₃ := by rw [ht0def]; linarith
--       have ht0_mem : t₀ ∈ Set.Ioo x₁ x₂ := ⟨by linarith, by linarith⟩
--       have ht0_le : f t₀ ≤ f xmax := h_max_at_xmax _ (Set.Ioo_subset_Icc_self ht0_mem)
--       by_cases ht0M : f t₀ = f xmax
--       · -- `min xmax x₃`, `t₀`, `max xmax x₃` are three distinct preimages of `f xmax`.
--         exact three_preimages (f xmax) _ t₀ _ ht0_lo ht0_hi flo ht0M fhi
--       · -- `f t₀ < f xmax`: a preimage of `f t₀` on each flank, with `t₀` strictly between.
--         have ht0lt : f t₀ < f xmax := lt_of_le_of_ne ht0_le ht0M
--         have ht0pos : 0 < f t₀ := h _ ht0_mem
--         obtain ⟨c, hc1, hc2, hfc⟩ :=
--           cross x₁ _ hlo (Or.inl ⟨hfx1, flo⟩) (f t₀) ht0pos ht0lt
--         obtain ⟨d, hd1, hd2, hfd⟩ :=
--           cross _ x₂ hhi (Or.inr ⟨fhi, hfx2⟩) (f t₀) ht0pos ht0lt
--         exact three_preimages (f t₀) c t₀ d (by linarith) (by linarith) hfc rfl hfd

-- lemma aux₁ {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
--     (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) (h : ∀ x ∈ Ioo x₁ x₂, f x < 0) : False := by
--   refine aux (f := -f) (continuous_neg_iff.mpr hf1) ?_ hx_lt ?_ ?_
--   · intro y
--     have : (-f) ⁻¹' {y} = f ⁻¹' {-y} := by
--       ext x
--       simp only [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply, neg_eq_iff_eq_neg]
--     simpa [this] using hf2 _
--   · have : (-f) ⁻¹' {0} = f ⁻¹' {0} := by
--       ext x
--       simp [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply]
--     simpa [this]
--   simpa using h

-- example : ¬ ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ y, ncard (f⁻¹' {y}) = 2 := by
--   intro ⟨f, hf₁, hf₂⟩
--   obtain h₀ := hf₂ 0
--   obtain ⟨x₁, x₂, hx, hx_eq⟩ := ncard_eq_two_lt.mp h₀
--   wlog h : ∃ x ∈ Ioo x₁ x₂, f x > 0 generalizing f x₁ x₂
--   · push Not at h
--     -- `h : ∀ x ∈ Ioo x₁ x₂, f x ≤ 0`. Either `f` is strictly negative on the whole
--     -- interval (apply `aux₁`), or it hits `0` somewhere strictly inside, giving a third
--     -- point in the fibre of `0`.
--     by_cases h' : ∀ x ∈ Ioo x₁ x₂, f x < 0
--     · exact aux₁ hf₁ hf₂ hx hx_eq h'
--     push Not at h'
--     obtain ⟨x, hx_mem, hfx⟩ := h'
--     have hfx0 : f x = 0 := le_antisymm (h x hx_mem) hfx
--     have hmem : x ∈ f ⁻¹' {0} := by
--       rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfx0
--     rw [hx_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
--     rw [Set.mem_Ioo] at hx_mem
--     obtain rfl | rfl := hmem
--     · exact lt_irrefl _ hx_mem.1
--     · exact lt_irrefl _ hx_mem.2
--   by_cases h_pos : ∀ x ∈ Ioo x₁ x₂, f x > 0
--   · exact aux hf₁ hf₂ hx hx_eq h_pos
--   simp only [mem_Ioo, gt_iff_lt, and_imp, not_forall, not_lt] at h_pos
--   obtain ⟨x₃, h_lt₁, h_lt₂, f_le⟩ := h_pos
--   obtain ⟨x₄, x₄_mem, fx₄_pos⟩ := h
--   -- We have `f x₃ ≤ 0 < f x₄` with `x₃, x₄ ∈ Ioo x₁ x₂`, so by the intermediate value
--   -- theorem `f` vanishes at some `c` between `x₃` and `x₄`, hence inside `Ioo x₁ x₂`.
--   rw [Set.mem_Ioo] at x₄_mem
--   have h0_mem : (0 : ℝ) ∈ Set.uIcc (f x₃) (f x₄) :=
--     Set.mem_uIcc.mpr (Or.inl ⟨f_le, le_of_lt fx₄_pos⟩)
--   obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_uIcc hf₁.continuousOn h0_mem
--   -- `c` lies in `Ioo x₁ x₂`, since `uIcc x₃ x₄ ⊆ Ioo x₁ x₂`.
--   rw [Set.mem_uIcc] at hc_mem
--   have hc_Ioo : x₁ < c ∧ c < x₂ := by
--     rcases hc_mem with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
--       exact ⟨by linarith [h_lt₁, x₄_mem.1], by linarith [h_lt₂, x₄_mem.2]⟩
--   have hc_pre : c ∈ f ⁻¹' {0} := by
--     rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hc_eq
--   rw [hx_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hc_pre
--   obtain rfl | rfl := hc_pre
--   · exact lt_irrefl _ hc_Ioo.1
--   · exact lt_irrefl _ hc_Ioo.2

-- open Function Set

-- lemma ncard_eq_two_lt {s : Set ℝ} :
--   s.ncard = 2 ↔ (∃ x y, x < y ∧ s = {x, y}) := by
--   rw [ncard_eq_two]
--   constructor
--   · intro ⟨x, y, hx1, hx2⟩
--     by_cases h : x < y
--     · use x, y
--     · use y, x
--       grind
--   grind

-- lemma aux {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
--     (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) (h : ∀ x ∈ Ioo x₁ x₂, f x > 0) : False := by
--   -- IsCompact.exists_isMaxOn
--   have h_max : ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
--     apply IsCompact.exists_isMaxOn isCompact_Icc (nonempty_Icc.mpr (le_of_lt hx_lt))
--     exact Continuous.continuousOn hf1
--   obtain ⟨xmax, h_max, h_max_at_xmax⟩ := h_max
--   rw [isMaxOn_iff] at h_max_at_xmax

--   sorry

-- lemma aux₁ {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
--     (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) (h : ∀ x ∈ Ioo x₁ x₂, f x < 0) : False := by
--   refine aux (f := -f) (continuous_neg_iff.mpr hf1) ?_ hx_lt ?_ ?_
--   · sorry
--   · sorry
--   simpa using h

-- example : ¬ ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ y, ncard (f⁻¹' {y}) = 2 := by
--   intro ⟨f, hf₁, hf₂⟩
--   obtain h₀ := hf₂ 0
--   obtain ⟨x₁, x₂, hx, hx_eq⟩ := ncard_eq_two_lt.mp h₀
--   wlog h : ∃ x ∈ Ioo x₁ x₂, f x > 0 generalizing f x₁ x₂
--   ·
--     sorry
--   by_cases h_pos : ∀ x ∈ Ioo x₁ x₂, f x > 0
--   · exact aux hf₁ hf₂ hx hx_eq h_pos
--   simp only [mem_Ioo, gt_iff_lt, and_imp, not_forall, not_lt] at h_pos
--   obtain ⟨x₃, h_lt₁, h_lt₂, f_le⟩ := h_pos
--   obtain ⟨x₄, x₄_mem, fx₄_pos⟩ := h
--   #check intermediate_value_uIcc
--   -- intermediate_value_uIcc



--   sorry
