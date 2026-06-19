# `grind` Usage List

This document collects every place in the game levels where the `grind` tactic is used
(excluding drafts under `Levels_inactive/` and commented-out code).
In many of these spots, `grind` replaces / simplifies longer original proofs such as
`simp` + `ring`, `omega`, or manual `rw` chains.

> `grind` is first introduced as a new tactic at [Piazza/L09_lt_trichotomy2.lean:37](Game/Levels/Piazza/L09_lt_trichotomy2.lean#L37) via `NewTactic grind`.

---

## Babylon (Sums / Induction)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L04_sum_subset.lean:54](Game/Levels/Babylon/L04_sum_subset.lean#L54) | `∑ i ∈ Icc 0 n, (i³-3i²+2i) = ∑ i ∈ Icc 3 n, …` | After `rw [Icc_subset_Icc_iff]`, `grind` closes the inequality |
| [L04_sum_subset.lean:96](Game/Levels/Babylon/L04_sum_subset.lean#L96) | same as above | Proves `i = 0 ∨ i = 1 ∨ i = 2`; originally planned as `simp` + `grind` |
| [L04_sum_subset.lean:105](Game/Levels/Babylon/L04_sum_subset.lean#L105) | same as above | Final step, replacing a manual proof (see comments) |
| [L07_Induction_sum_insert__arithmetic_sum.lean:71-72](Game/Levels/Babylon/L07_Induction_sum_insert__arithmetic_sum.lean#L71) | `∑ i ∈ Icc 0 n, i = ½·n·(n+1)` (arithmetic sum) | **Replaces the commented-out chain `rw [sum_insert] → rw [hd] → simp → ring → simp`** (see comments at L79-L103) |
| [L08_Induction2_sum_insert2.lean:61](Game/Levels/Babylon/L08_Induction2_sum_insert2.lean#L61) | `∑ i ∈ Icc (-n) n, i = 0` | Closes after a `have` inside the induction step |
| [L08_Induction2_sum_insert2.lean:63](Game/Levels/Babylon/L08_Induction2_sum_insert2.lean#L63) | same as above | Closes another branch |
| [L09_Induction3_sub_insert3.lean:36-37](Game/Levels/Babylon/L09_Induction3_sub_insert3.lean#L36) | `∑ i ∈ Icc 0 n, (2i+1) = (n+1)²` | **Replaces the commented-out `rw [sum_insert] → rw [hd] → ring → simp`** (see comments at L39-L43) |
| [L10_Boss.lean:42](Game/Levels/Babylon/L10_Boss.lean#L42) | `∑ i ∈ Icc 0 m, i³ = (∑ i ∈ Icc 0 m, i)²` | **Replaces the commented-out `simp` + `ring`** (see L44-L45); a comment also suggests `grind [arithmetic_sum]` |
| [L10_Boss.lean:47](Game/Levels/Babylon/L10_Boss.lean#L47) | same as above | Closes another branch |

## Euklid (Primes / Infinitude of primes)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L01_prod_pos.lean:29](Game/Levels/Euklid/L01_prod_pos.lean#L29) | `0 < ∏ a ∈ A, a` (product of primes is positive) | Closes the positivity proof |
| [L03_Finite_toFinset__prod_insert2.lean:76](Game/Levels/Euklid/L03_Finite_toFinset__prod_insert2.lean#L76) | Exists a positive integer divisible by all primes | Replaces another manual call to `Finset.prod_pos` (see comments at L69/L78) |
| [L04_Boss_infinitely_many_primes.lean:57,61,87,89](Game/Levels/Euklid/L04_Boss_infinitely_many_primes.lean#L57) | `¬ Set.Finite {p | Prime p}` | Closes several divisibility / contradiction steps |

## Robotswana (Matrices)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L05_EBasisDiagSum.lean:101](Game/Levels/Robotswana/L05_EBasisDiagSum.lean#L101) | `∑ i : Fin n, E i i = 1` | Closes with a "try grind" hint, replacing a manual `simp` simplification (see comment at L112) |

## Mono (Monotonicity / Injectivity)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L02_InjectiveNeIff.lean:25](Game/Levels/Mono/L02_InjectiveNeIff.lean#L25) | Deriving `f a ≠ f b` from injectivity | Closes directly with `grind` |
| [L06_StrictMono.lean:34,39](Game/Levels/Mono/L06_StrictMono.lean#L34) | `StrictMono.injective` | Both branches (including the symmetric one) close with `grind` |

## Piazza (Reals / Intervals)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L09_lt_trichotomy2.lean:35](Game/Levels/Piazza/L09_lt_trichotomy2.lean#L35) | Exists b between a and c | **First place `grind` is introduced as a NewTactic**; closes directly |
| [L10_Icc_subset_Icc_iff.lean:38](Game/Levels/Piazza/L10_Icc_subset_Icc_iff.lean#L38) | `Icc_subset_Icc_iff` | `grind` proves the iff characterization of interval inclusion directly |

## Prado (Divisibility / Primes)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L02_dvd_iff_exists_eq_mul_left.lean:68](Game/Levels/Prado/L02_dvd_iff_exists_eq_mul_left.lean#L68) | `a ∣ b → a ∣ c → a ∣ b+c` | Closes a branch |
| [L05_not_dvd_of_lt_of_lt_mul_succ.lean:40](Game/Levels/Prado/L05_not_dvd_of_lt_of_lt_mul_succ.lean#L40) | `n*k < m < n*(k+1) → ¬ n ∣ m` | Closes directly with `grind` |
| [L06_Prime_Specialize__prime_def.lean:53,64](Game/Levels/Prado/L06_Prime_Specialize__prime_def.lean#L53) | `a ∣ p → a = p` (p prime) | Closes goals; L64 derives a contradiction from `a = 1` and `2 ≤ a` |
| [L09_ExistsUnique.lean:69](Game/Levels/Prado/L09_ExistsUnique.lean#L69) | `∃! m, a*m = b` | Closes the uniqueness branch |

## Vieta (Functions / Polynomials)

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L01_FunctionNotation.lean:30](Game/Levels/Vieta/L01_FunctionNotation.lean#L30) | `f n ≥ 0` (f valued in ℕ) | Closes directly with `grind` (comment notes "oder simp" as an alternative) |
| [L05_Funext.lean:37](Game/Levels/Vieta/L05_Funext.lean#L37) | Function equality (funext) | Closes directly with `grind` plus a hint |
| [L07_Extend.lean:44](Game/Levels/Vieta/L07_Extend.lean#L44) | Function extension | Closes directly with `grind` |
| [L10_Surjective.lean:66](Game/Levels/Vieta/L10_Surjective.lean#L66) | Surjectivity-related | Closes a branch |

## Ciao

| Location | Level goal | What `grind` simplified |
|----------|------------|--------------------------|
| [L01.lean:13](Game/Levels/Ciao/L01.lean#L13) | `∀ n, ∃ m, m > n` | One-line close with `grind` |

---

## Summary

- **Clearest cases of "simplifying the original proof"**: `Babylon/L07`, `Babylon/L09`, `Babylon/L10`, `Robotswana/L05` — these files still keep the old proofs commented out (multi-line chains of `rw [sum_insert]` → `rw [hd]` → `simp` / `ring`), now replaced by a single `grind`.
- **As level closers**: in most other spots, `grind` closes a leftover arithmetic / divisibility / inequality goal in one step, replacing `omega`, `simp` + `ring`, or manual case analysis.
- The "new tactic" introduction point for `grind` is at [Piazza/L09](Game/Levels/Piazza/L09_lt_trichotomy2.lean#L37).
