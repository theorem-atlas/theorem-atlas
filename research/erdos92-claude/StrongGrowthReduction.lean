import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter

/-- If `n ^ δ ≤ f n` holds for arbitrarily large `n` (with `δ > 0` fixed), then
`f n ≤ n ^ (c / log (log n))` cannot hold eventually, for any real `c`. -/
theorem not_eventually_le_rpow_div_loglog
    (f : ℕ → ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hfreq : ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ δ ≤ f n)
    (hev : ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))) :
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

theorem not_eventually_le_rpow_div_loglog_nat
    (f : ℕ → ℕ) {δ c : ℝ} (hδ : 0 < δ)
    (hlarge : ∀ N : ℕ, ∃ n ≥ N, (n : ℝ) ^ δ ≤ (f n : ℝ))
    (hev : ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))) :
    False :=
  not_eventually_le_rpow_div_loglog (fun n => (f n : ℝ)) hδ
    (Filter.frequently_atTop.mpr hlarge) hev

#print axioms not_eventually_le_rpow_div_loglog
#print axioms not_eventually_le_rpow_div_loglog_nat
