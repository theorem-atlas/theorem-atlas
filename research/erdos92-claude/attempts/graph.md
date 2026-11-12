# Claude graph pruning attempt

Model: claude-opus-5-5[1m]; session: bfd043d1-dd8f-4124-af25-6a9c89fe81c1; reported cost: $0.3281098. Tools disabled. Output was not compiled during generation. Source interface: https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean

```lean
import Mathlib

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
```

**Status:** This is an unverified candidate. I have not compiled it. It is a supporting lemma only, not a proof of either Erdős 92 statement.

**Imports and names it relies on**
- `import Mathlib`, or more narrowly `Mathlib.Algebra.BigOperators.Basic`, `Mathlib.Tactic.Ring`, and `Mathlib.Tactic.PushNeg`.
- `Finset.card_filter`: `#(s.filter p) = ∑ a ∈ s, if p a then 1 else 0`.
- `Finset.sum_insert`, `Finset.sum_add_distrib`, `Finset.sum_congr`.
- `Finset.insert_erase`, `Finset.mem_erase`, `Finset.card_erase_add_one`, `Finset.erase_ssubset`, `Finset.erase_subset`.
- `Finset.strongInduction`, with case name `H`.
- `Symmetric`, which is `∀ ⦃x y⦄, r x y → r y x`.

**How the proof works**
- The proof uses strong induction on `S`.
- If every vertex has degree greater than `k`, it takes `T = S`. `S` is nonempty, because an empty `S` makes the sum 0, which contradicts `hS`.
- Otherwise it picks `v` with `degIn v S ≤ k` and deletes it.
- `sum_degIn_insert` gives the exact identity `Σ_S = Σ_{S∖v} + 2·deg(v)`, which covers both directions of the symmetric degree sum. Self-loops contribute 0 by irreflexivity. The edges counted from the other end are turned into `v`'s own degree by `hswap`, which uses symmetry.
- From that identity, `2k(|S∖v|+1) < Σ_{S∖v} + 2·deg(v) ≤ Σ_{S∖v} + 2k`. This gives the induction hypothesis for `S.erase v`.
- `omega` treats the sums and `2*k*card` products as atoms. `h1` makes those atoms syntactically consistent.
- `[Fintype α]` is not needed, so the statement is slightly more general than requested.

**Existing Mathlib lemma:** I don't know of a Mathlib lemma with this exact `Finset`/`Prop`-adjacency form. `SimpleGraph.sum_degrees_eq_twice_card_edges` is related, but it is stated for the global `Fintype` degree, not for degrees inside induced subsets. So I proved the lemma directly rather than cite something I can't confirm.

**Most likely failure points, with fallbacks**
1. **`Finset.card_filter`** may have a different form in the pinned Mathlib. Fallback: `simp only [degIn, Finset.sum_boole, Nat.cast_id]`.
2. **`Finset.card_erase_add_one`** may be missing. Fallback: `Finset.card_erase_of_mem hv` together with `Finset.card_pos.2 ⟨v, hv⟩` and `omega`.
3. **The `| H S ih` case name** may not match. Fallback: `refine Finset.strongInduction (fun S ih => ?_) S`.
4. **`omega` atom matching in `sum_degIn_insert`** could fail if the `Decidable` instances inside the `ite` terms don't unify. Fallback: `rw [h0, hswap]` and then `ring`.
