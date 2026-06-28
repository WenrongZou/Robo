import Game.Levels.Shade.L01_BddAbove

World "Shade"
Level 2

Title ""

Introduction
"
In the last level we showed that a set can be bounded above (`BddAbove`).
Once a nonempty set of reals is bounded above it has a least upper bound,
its supremum `sSup s`.

The key fact is that the supremum is an *upper bound*: every element of the
set lies below it.  In Mathlib this is

`le_csSup : BddAbove s → a ∈ s → a ≤ sSup s`

(The `c` stands for *conditionally* complete: over `ℝ` we must supply a proof
that `s` is bounded above, otherwise `sSup s` is just a junk value.)

Here is a typical way this lemma gets used.  You are told that the set `s` is
bounded above and that it contains some element `x` which is **strictly bigger
than** a number `c`.  Conclude that `c` is strictly smaller than the whole
supremum `sSup s`.

So `le_csSup` is not the end of the argument — it is one step inside a short
chain of inequalities `c < x ≤ sSup s`.
"

open Set

/-- `le_csSup (hbd : BddAbove s) (hx : a ∈ s) : a ≤ sSup s` -/
TheoremDoc le_csSup as "le_csSup" in "sSup"

Statement {s : Set ℝ} {c x : ℝ} (hbd : BddAbove s) (hx : x ∈ s) (hcx : c < x) :
    c < sSup s := by
  Hint "First get the bound `{x} ≤ sSup {s}` from `le_csSup hbd hx`.
  Then chain it with `{hcx}` using `lt_of_lt_of_le`."
  exact lt_of_lt_of_le hcx (le_csSup hbd hx)

Conclusion
"Nicely done.  `le_csSup` turned membership `x ∈ s` into the bound
`x ≤ sSup s`, and one transitivity step finished the job."

NewTheorem le_csSup

TheoremTab "sSup"
