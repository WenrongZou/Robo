# Quantus Levels — Content Audit

Audit of what each Quantus level introduces: a new tactic (`NewTactic`), a new
definition (`NewDefinition`), or merely proves an existing mathlib lemma
(`NewTheorem` only). Levels ordered by filename.

| Level | NewTactic | NewDefinition | NewTheorem | Role |
|-------|-----------|---------------|------------|------|
| L01 | `use` | `Nonempty` | — | introduces tactic + definition |
| L02 | — | `Exists` | — | introduces definition |
| L03 | — | — | — | practice only (`decide` on `Even 42`) |
| L04 | `unfold` `choose` `let` | `Even` `Odd` | — | introduces tactic + definition |
| **L05** | — | — | `Odd.neg_pow` `Even.neg_pow` | **proves mathlib lemma only** |
| **L06** | — | — | `Nat.not_odd_iff_even` `Nat.not_even_iff_odd` | **proves mathlib lemma only** |
| L07 | — | `Forall` | — | introduces definition |
| L08 | `push` | — | — | introduces tactic |
| **L09** | — | — | `not_exists` `Classical.not_forall` | **proves mathlib lemma only** |
| L10 | — | — | — | practice only (Drinker's Paradox) |
| O04 | — | — | — | practice only (`rw`) |
| O05 | — | — | — | practice only (`ring`) |
| O09 | — | — | — | practice only (`Odd (n^2)`) |

## Decisions
- Delete L03, since only practice `decide`.
- Delete L08 and keep L09, since `tauto` can solve L08 and `grind` can not solve L09
- Delete L06 since `ring` can solves it.

## Findings

**Levels that introduce no new tactic/definition and only prove a mathlib lemma
(`NewTheorem` only):**
- `L05_neg_pow.lean` — `Odd.neg_pow`, `Even.neg_pow`
- `L06_not_even_iff_odd.lean` — `Nat.not_odd_iff_even`, `Nat.not_even_iff_odd`
- `L09_PushNeg.lean` — `not_exists`, `Classical.not_forall`

**Levels that introduce no new content at all (pure practice/application, not even
a `NewTheorem`):**
- `L03_Decide.lean`
- `L10_DrinkersParadox.lean`
- `O04_Rewrite.lean`
- `O05_Ring.lean`
- `O09_Exists.lean`
