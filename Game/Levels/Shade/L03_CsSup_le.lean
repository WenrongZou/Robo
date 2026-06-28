import Game.Levels.Shade.L02_Le_csSup

World "Shade"
Level 3

Title ""

Introduction
"
In the previous level `le_csSup` told us that `sSup s` is an *upper bound*:
it lies above every element of `s`.

But `sSup s` is the *least* upper bound, so it lies **below** every other
upper bound of `s`.  That direction is

`csSup_le : s.Nonempty → (∀ a ∈ s, a ≤ b) → sSup s ≤ b`

It needs two things: a proof that `s` is nonempty, and a proof that `b` is an
upper bound of `s` (every element is `≤ b`).  Note that `BddAbove` is *not*
required here — once you exhibit a concrete upper bound `b`, the supremum
cannot exceed it.

As in the last level, `csSup_le` is usually one link in a chain.  Here you are
given that every element of `s` is `≤ b`, and that `b ≤ c`.  Conclude that the
supremum `sSup s` is `≤ c`, i.e. read off `sSup s ≤ b ≤ c`.
"

open Set

/-- `csSup_le (hne : s.Nonempty) (H : ∀ a ∈ s, a ≤ b) : sSup s ≤ b` -/
TheoremDoc csSup_le as "csSup_le" in "sSup"

Statement {s : Set ℝ} {b c : ℝ} (hne : s.Nonempty) (H : ∀ x ∈ s, x ≤ b) (hbc : b ≤ c) :
    sSup s ≤ c := by
  Hint "First get `sSup {s} ≤ {b}` from `csSup_le hne H`.
  Then chain it with `{hbc}` using `le_trans`."
  exact le_trans (csSup_le hne H) hbc

Conclusion
"Perfect.  `csSup_le` bounded the supremum from above by `b`, and one
transitivity step pushed it up to `c`."

NewTheorem csSup_le

TheoremTab "sSup"
