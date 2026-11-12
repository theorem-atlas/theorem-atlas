import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

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

#print axioms growth_contradiction
