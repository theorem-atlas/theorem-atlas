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

end TheoremAtlas.Erdos92Support

#print axioms TheoremAtlas.Erdos92Support.exists_subset_forall_lt_degIn
