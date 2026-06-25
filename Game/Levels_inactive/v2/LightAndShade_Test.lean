import Game.Levels_inactive.v2.LightAndShade_Test.L01_NotMemShade
import Game.Levels_inactive.v2.LightAndShade_Test.L02_ExistGt
import Game.Levels_inactive.v2.LightAndShade_Test.L03_ShadeSetNonempty
import Game.Levels_inactive.v2.LightAndShade_Test.L04_ShadeSetBddAbove
import Game.Levels_inactive.v2.LightAndShade_Test.L05_FcLeFsSup
import Game.Levels_inactive.v2.LightAndShade_Test.L06_FLeFcRight
import Game.Levels_inactive.v2.LightAndShade_Test.L07_FsSupEqFc
import Game.Levels_inactive.v2.LightAndShade_Test.L08_LightAndShade

/-!
The planet `LightAndShade` builds, level by level, the theorem of "Light and Shadow":

A real number `s` is a *shadow point* of a continuous `f : ℝ → ℝ` if there is some `t > s` with
`f t > f s`.  If `a < b` are themselves not shadow points, but every point strictly between them is,
then `f a = f b`.

The boss level (Level 8) assembles the helper lemmas proved in Levels 1–7.
-/

World "LightAndShade"
Title "Light and Shade"

Introduction "Intro LightAndShade: shadow points of a continuous function.

A point `s` is a *shadow point* of `f` if `f` rises above `f s` somewhere to the right of `s`.
Across this world you will prove, piece by piece, that if `a < b` are not shadow points while every
point in between is, then `f a = f b`. The final level is the boss that puts everything together.
"
