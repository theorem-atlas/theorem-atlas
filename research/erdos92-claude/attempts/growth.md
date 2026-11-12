# Claude growth attempt

Model: claude-opus-5-5[1m]; session: 8f5363fb-fe2f-4e61-a4fc-586a20658965; reported cost: $0.1213538. Tools disabled. Output was not compiled during generation. Source interface: https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean

# Workstream C: candidate proof of the growth-contradiction lemma

This is a **supporting lemma only**. It reduces `erdos_92.variants.weak` to a lower bound of the form "`f n ≥ n^δ` for infinitely many `n`". It does **not** prove Erdős 92. The lower bound is the hard combinatorial input and is not supplied here.

I have not compiled this. It is a candidate for your isolated CI.

```lean
import Mathlib

open Filter

/-- **Supporting lemma (analytic reduction only; not a proof of Erdős 92).**
If `f n ≥ n^δ` for infinitely many `n` (with `δ > 0`), then `f` admits no bound
`f n ≤ n^(o n)` with `o = o(1)`. -/
theorem growth_contradiction (f : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ n ≥ N, (n : ℝ) ^ δ ≤ (f n : ℝ)) :
    ¬ ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ n, (f n : ℝ) ≤ (n : ℝ) ^ (o n) := by
  rintro ⟨o, ho, hbound⟩
  -- Little-o against the constant 1: eventually ‖o n‖ ≤ (δ/2) * ‖1‖.
  have hev : ∀ᶠ n in Filter.atTop, ‖o n‖ ≤ (δ / 2) * ‖(1 : ℕ → ℝ) n‖ :=
    ho.def (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- Force n ≥ 2, so the cases n = 0 and n = 1 never arise.
  obtain ⟨n, hn, hfn⟩ := h (max N 2)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hon : ‖o n‖ ≤ (δ / 2) * ‖(1 : ℕ → ℝ) n‖ := hN n hnN
  simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs] at hon
  have hlt : o n < δ := by
    have := le_abs_self (o n)
    linarith
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  -- For base > 1, rpow is strictly increasing in the exponent.
  have hpow : (n : ℝ) ^ (o n) < (n : ℝ) ^ δ :=
    Real.rpow_lt_rpow_of_exponent_lt hn1 hlt
  have := hbound n
  linarith
```

## How the requested points are handled

- **n = 0 and n = 1:** These cases are avoided, not case-split. Asking for a witness `n ≥ max N 2` guarantees `n ≥ 2`. That gives `1 < (n : ℝ)`, so the degenerate behaviour of `0^x` and `1^x` never appears.
- **Strict monotonicity in the exponent:** This uses `Real.rpow_lt_rpow_of_exponent_lt : 1 < x → y < z → x ^ y < x ^ z`.
- **Little-o API:** This uses `Asymptotics.IsLittleO.def : f =o[l] g → 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`, with `c = δ/2`. It then converts with `Filter.eventually_atTop`. I chose this route over `Asymptotics.isLittleO_one_iff` because that lemma is stated for `fun _ => 1`, while the goal has the Pi constant `(1 : ℕ → ℝ)`. The explicit-`F` argument conventions of that lemma also vary between versions.

## Places that might fail in CI

1. **`Real.rpow_lt_rpow_of_exponent_lt`** may be deprecated or renamed in recent Mathlib. If so, replace it with `(Real.rpow_lt_rpow_left_iff hn1).mpr hlt` or `Real.rpow_lt_rpow_of_exponent_lt` under its new name. A deprecation alone is only a warning.
2. **The `simp only [Pi.one_apply, …] at hon` step** should normalise `‖(1 : ℕ → ℝ) n‖` to `1`. If `Pi.one_apply` does not fire syntactically, use `norm_num at hon`, or `change |o n| ≤ δ / 2 * ‖(1 : ℝ)‖ at hon` followed by `simp at hon`.
3. **`ho.def (by linarith)`** depends on the implicit `c` being unified from the stated type of `hev`. If elaboration fails, write `ho.def (c := δ / 2) (by linarith)`.
4. **File header:** The Formal Conjectures file uses `module` and `public import FormalConjecturesUtil`. My candidate uses plain `import Mathlib` so it stands alone. Adjust the header if you inline it there.

## Remaining gap for the full `erdos_92.variants.weak`

To get the full theorem, someone must instantiate `h` with `f := Erdos92.f` and a concrete `δ > 0`. That means proving `∀ N, ∃ n ≥ N, (n:ℝ)^δ ≤ Erdos92.f n`.

This requires two things:
- a construction of point sets with many equidistant points at every point;
- showing that a construction lies in `possible_f_values n`, and that `le_csSup` applies using `possible_f_values_BddAbove`.

Neither is addressed here. The logical-intelligence source carries nonstandard hypotheses, so it should not be cited as discharging this step unconditionally.
