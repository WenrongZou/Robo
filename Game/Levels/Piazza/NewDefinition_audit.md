# Piazza Levels — NewDefinition Audit

Overview of the `NewDefinition` declarations across the Piazza levels (ordered by filename / level order).

| Level | NewDefinition |
|-------|---------------|
| L01 | `Mem Set` |
| L02 | `setOf` |
| L03 | `Set.union Set.inter` |
| L04 | `Set.univ` |
| L05 | `Set.empty` |
| L06 | `SDiff` |
| L07 | `Subset` |
| L08 | `Subset` ⚠️ duplicate |
| L09 | `Subset` ⚠️ duplicate |
| **L10** | ❌ none |
| L11 | `Finset.erase` |
| **L12** | ❌ none |
| **L13** | ❌ none |

## Decisions
- Delete L08, L09, L10
- For L11 - L13, only keep L13.

## Findings

**Levels with no NewDefinition:**
- `L10.lean`
- `L12_insert.lean`
- `L13_insert_erase.lean`

**Levels whose NewDefinition already appeared in an earlier level:**
- `L08_subset_iff.lean` — `Subset` already introduced in L07
- `L09_subset_iff2.lean` — `Subset` already introduced in L07

## Other (non-sequential) files

- `O06.lean` — `Set.empty`, already introduced in L05
- `O09.lean` — `Set.compl`, new
