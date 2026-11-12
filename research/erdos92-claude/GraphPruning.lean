import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Supporting lemma (Workstream A): finite-graph pruning

This is a supporting combinatorial lemma only. It is **not** a proof of
`Erdos92.erdos_92.variants.weak` or `Erdos92.erdos_92.variants.strong`.
-/

open Finset

namespace TheoremAtlas.Erdos92Support

variable {α : Type*} [DecidableEq α]

/-- Degree of `v` inside the vertex set `S`. -/
def degIn (adj : α → α → Prop) [DecidableRel adj] (v : α) (S : Finset α) : ℕ :=
  (S.filter (adj v)).card

/-- Supporting: degree as a sum of indicators. -/
theorem degIn_eq_sum (adj : α → α → Prop) [DecidableRel adj] (v : α) (S : Finset α) :
    degIn adj v S = ∑ w ∈ S, if adj v w then 1 else 0 := by
  unfold degIn
  rw [Finset.card_filter]

/-- Supporting: inserting a fresh vertex `v` into `S` raises the degree sum by twice the
degree of `v` (once for `v`'s own degree, once for the edges counted from the other end). -/
theorem sum_degIn_insert (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : Symmetric adj) (hirr : ∀ v, ¬ adj v v)
    {S : Finset α} {v : α} (hv : v ∉ S) :
    ∑ u ∈ insert v S, degIn adj u (insert v S)
      = ∑ u ∈ S, degIn adj u S + 2 * degIn adj v (insert v S) := by
  simp only [degIn_eq_sum, Finset.sum_insert hv, Finset.sum_add_distrib]
  have h0 : (if adj v v then 1 else 0) = 0 := if_neg (hirr v)
  have hswap : (∑ u ∈ S, if adj u v then 1 else 0) = ∑ u ∈ S, if adj v u then 1 else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : adj v u
    · rw [if_pos (hsymm h), if_pos h]
    · rw [if_neg (fun h' => h (hsymm h')), if_neg h]
  omega

/-- Supporting pruning lemma: if the degree sum exceeds `2 * k * |S|`, some nonempty
`T ⊆ S` has every vertex of degree `> k` inside `T`. -/
theorem exists_subset_forall_lt_degIn (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : Symmetric adj) (hirr : ∀ v, ¬ adj v v) (k : ℕ) (S : Finset α) :
    2 * k * S.card < ∑ v ∈ S, degIn adj v S →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T, k < degIn adj v T := by
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hall : ∀ v ∈ S, k < degIn adj v S
    · refine ⟨S, Finset.Subset.refl S, ?_, hall⟩
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hS
    · push_neg at hall
      obtain ⟨v, hv, hdeg⟩ := hall
      have hsum := sum_degIn_insert adj hsymm hirr (S := S.erase v) (v := v)
        (fun h => (Finset.mem_erase.1 h).1 rfl)
      rw [Finset.insert_erase hv] at hsum
      have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
      have h1 : 2 * k * S.card = 2 * k * (S.erase v).card + 2 * k := by
        rw [← hcard]; ring
      have hS' : 2 * k * (S.erase v).card < ∑ u ∈ S.erase v, degIn adj u (S.erase v) := by
        omega
      obtain ⟨T, hTsub, hTne, hT⟩ := ih (S.erase v) (Finset.erase_ssubset hv) hS'
      exact ⟨T, hTsub.trans (Finset.erase_subset v S), hTne, hT⟩

/-- Supporting: by irreflexivity, `v ∈ T` is not counted in its own degree, so
`degIn adj v T ≤ |T| - 1`. -/
theorem degIn_add_one_le_card (adj : α → α → Prop) [DecidableRel adj]
    (hirr : ∀ v, ¬ adj v v) {v : α} {T : Finset α} (hv : v ∈ T) :
    degIn adj v T + 1 ≤ T.card := by
  unfold degIn
  have hsub : T.filter (adj v) ⊆ T.erase v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_erase]
    exact ⟨fun h => hirr v (by rw [h] at hw; exact hw.2), hw.1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at hle
  have hpos : 0 < T.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

/-- Supporting: a nonempty set in which every vertex has degree `> k` has at least
`k + 2` elements (assumes only irreflexivity). -/
theorem card_ge_of_forall_lt_degIn (adj : α → α → Prop) [DecidableRel adj]
    (hirr : ∀ v, ¬ adj v v) {k : ℕ} {T : Finset α} (hTne : T.Nonempty)
    (hT : ∀ v ∈ T, k < degIn adj v T) : k + 2 ≤ T.card := by
  obtain ⟨v, hv⟩ := hTne
  have h1 := hT v hv
  have h2 := degIn_add_one_le_card adj hirr hv
  omega

/-- Supporting: the degree sum inside a set of minimum degree `> k` is at least
`(k + 1) * |T|`. -/
theorem card_mul_le_sum_degIn_of_forall_lt (adj : α → α → Prop) [DecidableRel adj]
    {k : ℕ} {T : Finset α} (hT : ∀ v ∈ T, k < degIn adj v T) :
    (k + 1) * T.card ≤ ∑ v ∈ T, degIn adj v T :=
  calc (k + 1) * T.card = ∑ _v ∈ T, (k + 1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ v ∈ T, degIn adj v T :=
        Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hT v hv)

/-- Supporting quantitative core: if the degree sum exceeds `2 * k * |S|`, some
`T ⊆ S` with `k + 2 ≤ |T|` has minimum internal degree `> k`, and hence internal
degree sum at least `(k + 1) * |T|`. Assumes symmetry and irreflexivity explicitly.
This is a combinatorial supporting lemma only, not a proof of Erdős 92. -/
theorem exists_core_quantitative (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : Symmetric adj) (hirr : ∀ v, ¬ adj v v) (k : ℕ) (S : Finset α)
    (hS : 2 * k * S.card < ∑ v ∈ S, degIn adj v S) :
    ∃ T ⊆ S, k + 2 ≤ T.card ∧ (∀ v ∈ T, k < degIn adj v T) ∧
      (k + 1) * T.card ≤ ∑ v ∈ T, degIn adj v T := by
  obtain ⟨T, hTS, hTne, hT⟩ := exists_subset_forall_lt_degIn adj hsymm hirr k S hS
  exact ⟨T, hTS, card_ge_of_forall_lt_degIn adj hirr hTne hT, hT,
    card_mul_le_sum_degIn_of_forall_lt adj hT⟩

/-- Supporting corollary: under the same explicit hypotheses, the ambient set itself
has at least `k + 2` elements. -/
theorem card_ge_of_sum_degIn_gt (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : Symmetric adj) (hirr : ∀ v, ¬ adj v v) (k : ℕ) (S : Finset α)
    (hS : 2 * k * S.card < ∑ v ∈ S, degIn adj v S) :
    k + 2 ≤ S.card := by
  obtain ⟨T, hTS, hcard, -, -⟩ := exists_core_quantitative adj hsymm hirr k S hS
  exact hcard.trans (Finset.card_le_card hTS)

end TheoremAtlas.Erdos92Support

#print axioms TheoremAtlas.Erdos92Support.exists_subset_forall_lt_degIn

#print axioms TheoremAtlas.Erdos92Support.exists_core_quantitative
