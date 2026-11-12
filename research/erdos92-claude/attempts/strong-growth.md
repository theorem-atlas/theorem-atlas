# Claude strong-growth attempt

Source: https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean

Model: claude-opus-5-5[1m]; session: 58ed89b3-8056-4da1-938f-4ccf54344fe2; reported cost: $0.116269. Tools disabled; generated code unverified at generation time.

Prompt: Develop Lean 4 theorem deriving contradiction to eventual f n ≤ n^(c/log(log n)) from arbitrarily large n with n^δ ≤ f n for fixed positive δ, i.e. useful reduction for Formal Conjectures Erdős 92 strong variant. Give exact statement and complete Lean proof if possible; no sorry, admit, unsafe, native_decide or axioms. Explain API uncertainty and status honestly. No tools or local builds.

# Lean 4 reduction: frequent `n^δ ≤ f n` contradicts eventual `f n ≤ n^(c / log log n)`

## Statement and proof

```lean
import Mathlib

open Filter

/-- If `n ^ δ ≤ f n` holds for arbitrarily large `n` (with `δ > 0` fixed), then
`f n ≤ n ^ (c / log (log n))` cannot hold eventually, for any real `c`. -/
theorem not_eventually_le_rpow_div_loglog
    (f : ℕ → ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hfreq : ∃ᶠ n in atTop, (n : ℝ) ^ δ ≤ f n)
    (hev : ∀ᶠ n in atTop, f n ≤ (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))) :
    False := by
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h1 : ∀ᶠ n : ℕ in atTop, max (c / δ) 0 < Real.log (Real.log (n : ℝ)) :=
    hll.eventually_gt_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hbad : ∀ᶠ n : ℕ in atTop, ¬ ((n : ℝ) ^ δ ≤ f n) := by
    filter_upwards [h1, h2, hev] with n hn1 hn2 hn3
    intro hn4
    have hpos : 0 < Real.log (Real.log (n : ℝ)) :=
      lt_of_le_of_lt (le_max_right _ _) hn1
    have hcδ : c / δ < Real.log (Real.log (n : ℝ)) :=
      lt_of_le_of_lt (le_max_left _ _) hn1
    have hexp : c / Real.log (Real.log (n : ℝ)) < δ := by
      rw [div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hδ] at hcδ
      linarith [mul_comm δ (Real.log (Real.log (n : ℝ)))]
    have hn1' : (1 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hlt : (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ))) < (n : ℝ) ^ δ :=
      Real.rpow_lt_rpow_of_exponent_lt hn1' hexp
    linarith
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hbad).exists
  exact hn' hn
```

### Variant matching "arbitrarily large n" phrasing and `ℕ`-valued `f`

```lean
theorem not_eventually_le_rpow_div_loglog_nat
    (f : ℕ → ℕ) {δ c : ℝ} (hδ : 0 < δ)
    (hlarge : ∀ N : ℕ, ∃ n ≥ N, (n : ℝ) ^ δ ≤ (f n : ℝ))
    (hev : ∀ᶠ n in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))) :
    False :=
  not_eventually_le_rpow_div_loglog (fun n => (f n : ℝ)) hδ
    (Filter.frequently_atTop.mpr hlarge) hev
```

## Mathematical idea

Since `log log n → ∞`, eventually `log log n > max(c/δ, 0)`. That gives `c / log log n < δ`, which holds for any sign of `c`. For `n ≥ 2` we have `n > 1`, so `rpow` is strictly increasing in the exponent. That yields `n^(c/log log n) < n^δ`. Combined with `n^δ ≤ f n ≤ n^(c/log log n)` at some large `n`, this is a contradiction.

Junk values of `Real.log` at `n = 0, 1` (and of `log log` for small `n`) don't matter, because everything is restricted to eventually-large `n`.

## Status

**Not compiled.** I wrote this without tools or a local build, as you asked. There are no `sorry`, `admit`, `unsafe`, `native_decide` or custom axioms.

### API names to check if it fails

| Name used | Risk / fallback |
|---|---|
| `tendsto_natCast_atTop_atTop` | Older Mathlib calls it `tendsto_nat_cast_atTop_atTop`. |
| `div_lt_iff₀` (`a / c < b ↔ a < b * c` for `0 < c`) | Older Mathlib uses `div_lt_iff`. If the multiplication order differs, the `mul_comm` hint to `linarith` should still close it. |
| `Real.rpow_lt_rpow_of_exponent_lt` (`1 < x → y < z → x^y < x^z`) | Stable for a long time. A possible future rename is `Real.rpow_lt_rpow_left_of_lt`-style. |
| `Filter.Frequently.and_eventually`, `.exists` | `.exists` needs `NeBot atTop` on `ℕ`, which is found by instance. Fallback: `exact Filter.not_frequently.mpr hbad hfreq`, or simply `exact hfreq hbad`, since `Frequently` unfolds to `¬ ∀ᶠ x, ¬ p x`. |
| `Filter.frequently_atTop` (`(∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b`) | Standard. The `∃ n ≥ N` binder form should match. |
| `filter_upwards [...] with ...` | Standard. |

The most likely failure points are the `div_lt_iff₀` rewrites, where the form or name may have shifted. A robust replacement for `hexp` is:

```lean
    have hexp : c / Real.log (Real.log (n : ℝ)) < δ := by
      have : c < δ * Real.log (Real.log (n : ℝ)) := by
        have := (div_lt_iff₀ hδ).mp hcδ; nlinarith
      exact (div_lt_iff₀ hpos).mpr (by linarith [mul_comm δ (Real.log (Real.log (n : ℝ)))])
```

### Relation to Formal Conjectures Erdős 92

I don't remember the exact form of the strong-variant statement in the Formal Conjectures repo. It may differ in several ways:
- the codomain of `f` (`ℕ` vs `ℝ`);
- whether it uses `Real.log` composed with casts or some other `log`;
- whether the bound is stated with `∀ᶠ`, `∃ N, ∀ n ≥ N`, or `=O[atTop]`;
- whether `c` is existentially quantified.

So you will probably need a small adapter lemma. The two most likely ones:
- **An `∃ c, ∀ᶠ …` hypothesis:** destructure it and apply the theorem.
- **An `IsBigO` formulation:** the multiplicative constant `C` gets absorbed, because `C · n^(c/log log n) < n^δ` still holds eventually. However, that needs an extra argument that the theorem above does not cover.

This lemma is only the easy "growth-rate incompatibility" reduction. It says nothing about whether either hypothesis actually holds for the Erdős 92 function, which is the substantive open part.
