import Game.Metadata

World "LightAndShade"
Level 1

Title "Not a Shadow Point"

Introduction "Intro LightAndShade L01: introduce the definition of a shadow point.

A real number `s` is a *shadow point* of `f` if some point further to the right is higher,
i.e. there is `t > s` with `f t > f s`.  We collect all shadow points in the set `Shade f`.

```
Shade f := {s : ℝ | ∃ t > s, f t > f s}
```

In this first level you show: if a point `a` is **not** a shadow point, then `f` never rises
above `f a` anywhere to the right of `a`.
"

open Set

def Shade (f : ℝ → ℝ) : Set ℝ := {s : ℝ | ∃ t > s, f t > f s}

/-- `Shade f` is the set of shadow points of `f`: those `s` for which there exists some
`t > s` with `f t > f s`. -/
DefinitionDoc Shade as "Shade" in "Shade"

/-- If `a` is not a shadow point, then `f x ≤ f a` for every `x > a`. -/
TheoremDoc not_mem_shade as "not_mem_shade" in "Shade"

Statement not_mem_shade {f : ℝ → ℝ} {a : ℝ} (h : a ∉ Shade f) (x : ℝ) (h_lt : a < x) :
    f x ≤ f a := by
  Hint "Argue by contradiction: assume `f x > f a`. Then `x` itself witnesses that `a` is a
  shadow point, contradicting `h`. Start with `by_contra hcon`."
  by_contra hcon
  Hint "Simplify the negated goal with `simp at hcon` to turn it into `f a < f x`."
  simp at hcon
  Hint "Now `x` together with `h_lt` and `hcon` builds the witness `a ∈ Shade f`. Close with
  `exact h ⟨x, h_lt, hcon⟩`."
  exact h ⟨x, h_lt, hcon⟩

Conclusion "Conclusion LightAndShade L01: saved as `not_mem_shade`."

NewDefinition Shade

TheoremTab "Shade"
