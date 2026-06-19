# `grind` Simplification Candidates (verified)

Goal: find existing proofs that could still be simplified with `grind`, **only in worlds where
`grind` is already available** — i.e. the worlds that already use it plus Samarkand
(Babylon, Robotswana, Ciao, Prado, Euklid, Vieta, Mono, Piazza, Samarkand).

Each candidate below was **actually tested**: the edit was applied to the real level file,
the module was rebuilt with `lake build`, and then reverted. ✅ = build passed, ❌ = `grind` failed.
No files were left modified.

> Method: replace the listed tactics with a single `grind`, build the module, revert via `git checkout`.

---

## ✅ Genuine simplifications (multiple lines → one `grind`)

These collapse a real multi-step tail into a single `grind` and are worth applying.

### 1. Piazza / L02_Simp — `simp` + `decide` → `grind`
[L02_Simp.lean:25](Game/Levels/Piazza/L02_Simp.lean#L25), goal `9 ∈ {n : ℕ | Odd n}`.

```lean
-- before
  simp
  decide
-- after
  grind
```
`grind` alone closes the goal (no `simp`/`decide` needed).

### 2. Piazza / L03_Ext__Set__Union__Inter — `simp` + `tauto` → `grind`
[L03_Ext__Set__Union__Inter.lean:40](Game/Levels/Piazza/L03_Ext__Set__Union__Inter.lean#L40).
After `ext x`, the `simp` step plus the final `tauto` both disappear:

```lean
-- before
  ext x
  simp
  …
  tauto
-- after
  ext x
  grind
```

### 3. Piazza / L06_Ext2__univ2 — `simp` + `tauto` → `grind`
[L06_Ext2__univ2.lean:25](Game/Levels/Piazza/L06_Ext2__univ2.lean#L25). After `ext i`:

```lean
-- before
  ext i
  simp
  tauto
-- after
  ext i
  grind
```

### 4. Piazza / L05_empty__eq_empty_iff_forall_notMem — `rw` + `simp` → `grind`
[L05_empty__eq_empty_iff_forall_notMem.lean:36](Game/Levels/Piazza/L05_empty__eq_empty_iff_forall_notMem.lean#L36).

```lean
-- before
  rw [eq_empty_iff_forall_notMem]
  simp
-- after
  grind
```
⚠️ **Caveat (pedagogy):** this level deliberately introduces `eq_empty_iff_forall_notMem`,
which is reused in Samarkand. Replacing it with `grind` would hide that lemma — apply only
if you don't mind losing the teaching step.

### 5. Piazza / L08_insert_erase — final `by_cases` block → `grind`
[L08_insert_erase.lean:48](Game/Levels/Piazza/L08_insert_erase.lean#L48). The closing case split collapses:

```lean
-- before
  by_cases heq : b = a
  · rw [heq]
    tauto
  · simp [heq]
-- after
  grind
```

### 6. Babylon / L06_sum_eq_single — `simp … at h` + `omega` → `grind`
[L06_sum_eq_single.lean:46](Game/Levels/Babylon/L06_sum_eq_single.lean#L46), last side goal (`k ∈ range n`).

```lean
-- before
    intro h
    simp [mem_range] at h
    omega
-- after
    intro h
    grind
```

---

## ✅ 1:1 replacements (work, but not a real simplification)

`grind` closes these in the same number of lines as the current tactic. Cosmetic only — listed
for completeness; keeping the existing, more readable tactic is usually preferable.

| Location | Current | `grind` works? |
|----------|---------|----------------|
| [Piazza/L01_Mem__Set.lean:28](Game/Levels/Piazza/L01_Mem__Set.lean#L28) | `tauto` | ✅ |
| [Piazza/L07_antisymm_iff.lean:32,37](Game/Levels/Piazza/L07_antisymm_iff.lean#L32) | `tauto` (both branches) | ✅ |
| [Samarkand/L02_ImageMap.lean:64](Game/Levels/Samarkand/L02_ImageMap.lean#L64) | `simp` | ✅ |

---

## ❌ Tested — `grind` does NOT work (keep as-is)

These were tried and failed to build; the existing tactic is required.

| Location | Current | Why `grind` fails |
|----------|---------|-------------------|
| [Mono/L03_NotInjective.lean:60](Game/Levels/Mono/L03_NotInjective.lean#L60) | `decide` | Concrete `Even`/`if` evaluation of `(f+f) 2`, `(f+f) 3` — needs `decide` |
| [Prado/L07_dvd_mul.lean:22](Game/Levels/Prado/L07_dvd_mul.lean#L22) | `rw [Prime.dvd_mul]; decide` | Needs the `Prime.dvd_mul` rewrite + `Prime 5` |
| [Samarkand/L03_SurjectiveRange.lean:74](Game/Levels/Samarkand/L03_SurjectiveRange.lean#L74) | `rw [← mem_range]; rw [h]; tauto` | Needs `mem_range` / `range` unfolding |
| [Samarkand/L06_PreimageNonempty.lean:26](Game/Levels/Samarkand/L06_PreimageNonempty.lean#L26) | `unfold Ne; rw […]; simp` | Needs `eq_empty_iff_forall_notMem`; `grind` can't reach it |
| [Samarkand/L08_Preimage_Injective.lean:51](Game/Levels/Samarkand/L08_Preimage_Injective.lean#L51) | `unfold Ne; rw […]; simp` | same as above |
| [Samarkand/L08_Preimage_Injective.lean:63](Game/Levels/Samarkand/L08_Preimage_Injective.lean#L63) | `rw [← g]; rw [Injective.ne_iff hinj]; simp` | Needs `Injective.ne_iff` + preimage lemmas |

---

## Not tested / not suitable

- **Pure `ring` / `simp; ring` polynomial identities** (Babylon L02/L05/L08, Prado L03,
  Vieta L04/L06, Euklid L02). `grind` is not a ring normalizer; these were not pursued.
- **Domain-specific matrix `simp [E]` / `simp [smul_ebasis]`** throughout Robotswana, and
  local-definition unfolds like `simp [f]` (Vieta, Mono L01/L04). `grind` would need those
  lemmas/definitions explicitly and is not a clean win.

---

## Summary

- **6 genuine simplifications** verified (collapse 2–4 lines into one `grind`):
  Piazza L02, L03, L06, L05, L08 and Babylon L06.
- **3 cosmetic 1:1** spots also work (Piazza L01, L07; Samarkand L02) but aren't improvements.
- **6 spots** were tested and `grind` cannot replace them (Mono L03, Prado L07, Samarkand L03/L06/L08).
- The biggest practical wins are **Piazza L02, L03, L06, L08** and **Babylon L06**.
  Note the pedagogy caveat on **Piazza L05**.
