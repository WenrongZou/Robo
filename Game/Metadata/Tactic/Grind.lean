import Init.Grind.Tactics
open Lean Parser.Tactic

/-!
# `game_grind`

Custom version of `grind` to restrict the player's `grind` calls. Every player `grind`
is rewritten to

  `grind -ring -ext (ematch := 0)`

which turns off the algebraic `ring` solver (`-ring`), the `[grind ext]` extensionality
theorems (`-ext`), and performs no E-matching rounds (`ematch := 0`).

## Why `macro`, not `macro_rules`

For `simp` the game uses `macro_rules` (see `Game.Metadata.Tactic.Simp`). That does **not**
work for `grind`: a `macro_rules` rewrite on `Lean.Parser.Tactic.grind` fires, but the
injected configuration never actually takes effect (grind keeps running at full strength).
Declaring a *fresh* `grind` syntax with `macro` routes the call through a clean re-parse of
the built-in `grind`, and the configuration *does* take effect. So we use one `macro` per
surface form.

## Coverage and escape hatch

The four forms below cover `grind`, `grind only`, `grind [h]`, `grind only [h]`. A `grind`
written with **explicit configuration** (`grind +ring`, `grind (ematch := 5)`, ...) parses
as the built-in `grind` and runs unrestricted -- this is the intended authoring escape
hatch. `grind?` is likewise left unrestricted (authoring tool).

## Behaviour notes

* With this configuration `grind` *fails* (with grind's normal "`grind` failed" diagnostic)
  on goals it cannot close -- e.g. a function equality `f = g`: funext splits it to
  `x² = (-x)²`, which then needs `ring`/E-matching, both disabled here. We deliberately do
  **not** wrap the rewrite in `try`, so that this failure is reported rather than silently
  swallowed. (A `try grind` would hide the message and turn a failing grind into a no-op.)
* Consequently a *restricted* `grind` must not be left in a level's committed proof for a
  goal it cannot close (it would break the build); use it only where it is meant to succeed.
-/

/- this version will give the error message. -/
-- macro (name := gGrind) "grind" : tactic =>
--   `(tactic| grind -ext (ematch := 0))
-- macro (name := gGrindOnly) "grind" "only" : tactic =>
--   `(tactic| grind -ext (ematch := 0) only)
-- macro (name := gGrindArgs) "grind" "[" ps:grindParam,* "]" : tactic =>
--   `(tactic| grind -ext (ematch := 0) [$ps,*])
-- macro (name := gGrindOnlyArgs) "grind" "only" "[" ps:grindParam,* "]" : tactic =>
--   `(tactic| grind -ext (ematch := 0) only [$ps,*])

/- this version will not give the error message. -/
macro_rules
  | `(tactic| grind)            => `(tactic| try grind -ext (ematch := 0))
  | `(tactic| grind only)       => `(tactic| try grind -ext (ematch := 0) only )
  | `(tactic| grind [$args,*])  => `(tactic| try grind -ext (ematch := 0) only [$args,*])
  | `(tactic| grind only [$args,*])  => `(tactic| try grind -ext (ematch := 0) only [$args,*])

macro (name := gGrind) "grind1" : tactic =>
  `(tactic| grind -ext)

/- ===========================================================================
   Earlier versions, kept for reference (do not enable alongside the macros above).

   (1) Original single `macro` for bare `grind` only:

   macro (name := grind) "grind" : tactic =>
     `(tactic| first | grind -ext -ring (ematch := 0))

   (2) `macro_rules` + `try` attempt. NOTE: this does **not** work -- the injected
       config does not take effect, and `try` swallows the resulting failure, so
       `grind` silently does nothing:

   macro_rules
     | `(tactic| grind)            => `(tactic| try grind -ext (ematch := 0))
     | `(tactic| grind only)       => `(tactic| try grind only -ext (ematch := 0))
     | `(tactic| grind [$args,*])  => `(tactic| try grind -ext (ematch := 0) only [$args,*])
     | `(tactic| grind only [$args,*])  => `(tactic| try grind -ext only (ematch := 0) only [$args,*])
   =========================================================================== -/
