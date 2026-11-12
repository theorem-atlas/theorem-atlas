# Claude source interface attempt

Model: claude-opus-5-5[1m]; session: 03681ca2-94c0-4262-9d8f-da13011e7b18; reported cost: $0.16399380000000002. Tools disabled. Output was not compiled during generation. Source interface: https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean

# Workstream B: supporting lemmas for the Erdős 92 source interface (unverified candidate)

These lemmas only connect the source definitions to unit-distance configurations. They do **not** prove `erdos_92.variants.weak` or `erdos_92.variants.strong`, and they don't assume either one. I wrote this without tools: nothing has been compiled or run, so treat it as a candidate for your isolated CI check.

## Which `sSup` the definitions use

Both definitions use **`Set` `sSup`**. Neither uses `Finset.sup` or `Finset.max`.

- **`maxEquidistantPointsAt`**: the argument `distances.image (fun d ↦ …)` is a `Finset ℕ`. It is coerced to `Set ℕ`, and `sSup` comes from the `ConditionallyCompleteLinearOrderBot ℕ` instance. The source's own `possible_f_values_BddAbove` proof confirms this, since it uses `csSup_le'` together with `Finset.mem_coe`.
- **`f n`**: this is `sSup (possible_f_values n)` on `Set ℕ`.

As a result, the lemmas use `le_csSup` together with:
- `Finset.bddAbove`, for the coerced finite set;
- `possible_f_values_BddAbove`, for `f`.

## How `k = 0` and empty distance sets are handled

- **`k = 0`**: this case is closed by `Nat.zero_le` before `sSup` is ever touched. The distance image may be empty here. If it is, the coerced set is `∅`, and `sSup ∅ = 0` in ℕ. The proof never needs that fact.
- **`k > 0`**: the proof derives that a neighbour exists from `0 < k ≤ card (filter …)` via `Finset.card_pos`. Only then does it conclude `1 ∈ distances`.
- **The point `x` itself**: `x` is excluded from the unit-distance filter because `dist x x = 0 ≠ 1`. This is why filtering `A` and filtering `A.erase x` give the same set.

## Code

### Option 1: separate file

```lean
import FormalConjectures.ErdosProblems.«92»

open scoped EuclideanGeometry

namespace Erdos92

/-- Supporting lemma (not a proof of Erdős 92): unit-distance neighbours witness the
equidistant property. -/
theorem hasMinEquidistantProperty_of_unit_neighbors (k : ℕ) (A : Finset ℝ²)
    (hA : A.Nonempty)
    (hk : ∀ x ∈ A, k ≤ (A.filter fun p => dist x p = 1).card) :
    hasMinEquidistantProperty k A := by
  refine ⟨hA, fun x hx => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact Nat.zero_le _
  have hfilter : (A.filter fun p => dist x p = 1) =
      ((A.erase x).filter fun p => dist x p = 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hp, hd⟩
      refine ⟨⟨?_, hp⟩, hd⟩
      rintro rfl
      simp at hd
    · rintro ⟨⟨_, hp⟩, hd⟩
      exact ⟨hp, hd⟩
  have hne : ((A.erase x).filter fun p => dist x p = 1).Nonempty := by
    rw [← Finset.card_pos, ← hfilter]
    exact lt_of_lt_of_le hpos (hk x hx)
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  have h1 : (1 : ℝ) ∈ (A.erase x).image (dist x) :=
    Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩
  have hmem : ((A.erase x).filter fun p => dist x p = 1).card ∈
      ((A.erase x).image (dist x)).image
        (fun d => ((A.erase x).filter fun p => dist x p = d).card) :=
    Finset.mem_image.mpr ⟨1, h1, rfl⟩
  unfold maxEquidistantPointsAt
  calc k ≤ (A.filter fun p => dist x p = 1).card := hk x hx
    _ = ((A.erase x).filter fun p => dist x p = 1).card := by rw [hfilter]
    _ ≤ _ := le_csSup (Finset.bddAbove _) (Finset.mem_coe.mpr hmem)

/-- Supporting lemma (not a proof of Erdős 92): a unit-distance configuration gives a lower
bound on `f`. -/
theorem le_f_card_of_unit_neighbors (k : ℕ) (A : Finset ℝ²)
    (hA : A.Nonempty)
    (hk : ∀ x ∈ A, k ≤ (A.filter fun p => dist x p = 1).card) :
    k ≤ f A.card := by
  unfold f
  refine le_csSup (possible_f_values_BddAbove A.card) ?_
  simp only [possible_f_values, Set.mem_setOf_eq]
  exact ⟨A, rfl, hasMinEquidistantProperty_of_unit_neighbors k A hA hk⟩

end Erdos92
```

### Option 2: append to the source file

Paste the two theorems just before `end Erdos92` in `92.lean`. This needs no new imports.

Caveat on Option 1: the source file is a `module` file. If your CI's test file must also be a module, use `module` / `public import …` instead of the plain `import`.

## Fragile points to check in CI

1. **`unfold maxEquidistantPointsAt` and `letI`**: I expect `letI` to inline the bindings, which the source's own proof relies on. If the goal still shows `let` bindings, add `dsimp only` after the `unfold`.
2. **`simp only [possible_f_values, Set.mem_setOf_eq]`**: I added this because anonymous-constructor elaboration may not unfold the set-builder definition. If `simp only` reports no progress, replace it with `show ∃ points, ∃ _ : points.card = A.card, hasMinEquidistantProperty k points`.
3. **Decidability instances**: the `DecidablePred` instance for `dist x p = 1` and `DecidableEq ℝ²` for `erase` should elaborate to the same instances the source definition uses. If `rw [hfilter]` or `le_csSup` fails with a mismatch, use `convert` or `classical`.
4. **`rintro rfl` followed by `simp at hd`**: this relies on `dist_self` being a simp lemma, which reduces `hd` to `0 = 1`.
5. **API names used**:
   - `Nat.eq_zero_or_pos`
   - `Finset.mem_filter`, `Finset.mem_erase` (form: `a ≠ b ∧ a ∈ s`), `Finset.mem_image`, `Finset.mem_coe`
   - `Finset.card_pos` (form: `0 < s.card ↔ s.Nonempty`)
   - `Finset.bddAbove`
   - `le_csSup`
   - `possible_f_values_BddAbove`
6. **The `ℝ²` notation**: it comes from `FormalConjecturesUtil`, so it should be visible through the import.
