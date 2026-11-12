# Claude quantitative graph core attempt

Source: GraphPruning.lean at eb290ed24f5e86eb2d19945e7b653611ffa5957e.

Model: claude-opus-5-5[1m]; session: 51d98529-3379-4558-b710-ac32e5d76183; reported cost: $0.112645. Tools disabled. Unverified at generation time.

Insert this block just before `end TheoremAtlas.Erdos92Support`. It relies on the file's existing `variable {α : Type*} [DecidableEq α]`, `degIn`, and `exists_subset_forall_lt_degIn`, which it reuses without restating.

```lean
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
```

Optionally, add these after `end`:

```lean
#print axioms TheoremAtlas.Erdos92Support.exists_core_quantitative
#print axioms TheoremAtlas.Erdos92Support.card_ge_of_sum_degIn_gt
```

Notes:
- I have not compiled this, as you asked. The lemma names I relied on are `Finset.card_le_card`, `Finset.card_erase_of_mem`, `Finset.card_pos`, `Finset.sum_const`, and `Finset.sum_le_sum`. These are the current Mathlib names, but if your pinned Mathlib is old, `card_le_card` may still be called `card_le_of_subset`.
- The size bound `card_ge_of_forall_lt_degIn` and the degree-sum bound only need irreflexivity. Symmetry is needed only where the existing pruning theorem is invoked.
- These are supporting combinatorial lemmas. They do not prove Erdős 92.
