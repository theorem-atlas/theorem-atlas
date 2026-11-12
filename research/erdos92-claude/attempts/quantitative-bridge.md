# Claude quantitative bridge attempt

**Unverified research notes:** The output did not inspect the pinned source and contains speculative claims about unit-distance bounds. It must not be treated as authoritative or as an established proof. Its graph lemma overlaps the already compiled graph-pruning lemma.

Source: https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean

Model: claude-opus-5-5[1m]; session: ecd03303-3f10-4bab-a4f7-87f6ef2595d3; reported cost: $0.393545. Tools disabled.

Prompt: Find a rigorous proof strategy for bridging OpenAI planar unit-distance lower bound to Formal Conjectures Erdős 92 weak variant, preserving logarithmic/exponent quantitative bounds. Identify exact input theorem needed, whether known result is conditional, cardinality growth, constants, and give useful Lean theorem(s) with explicit assumptions. No false unconditional claim, no sorry, admit, unsafe, native_decide or new axioms. Distinguish prose from checked proof. Do not execute tools.

# Bridging a planar unit-distance lower bound to Erdős #92 (weak variant)

**What I could not check.** You asked me not to run tools, so I did not read the Formal Conjectures (FC) file for Erdős 92 or anything in `proofs/`. I also have no reliable knowledge of a specific "OpenAI planar unit-distance lower bound" result. Below, that result appears only as an explicit hypothesis. The Lean code has not been compiled. It contains no `sorry`, `admit`, `unsafe`, `native_decide` or new axioms. Treat it as a candidate until `lake build` passes.

## 1. Which direction can work

Erdős 92 concerns f(n), the largest number such that some n points in ℝ² have, at every point x, at least f(n) other points equidistant from x. Erdős conjectured f(n) ≤ n^{o(1)}, possibly even f(n) ≤ n^{c/log log n}.

- **If the FC "weak variant" is an upper bound** (f(n) ≤ n^{o(1)} or similar), no unit-distance *lower* bound can prove it. A lower bound can only refute it, and only if the input beats n^{o(1)}.
- **If the weak variant is a lower bound or "infinitely often" statement** (sets of unboundedly many sizes m where every point has ≥ m^{c/log log m} equidistant points), the bridge below works and keeps the same constant c.
- **If the weak variant requires every n, or a prescribed n**, this bridge is insufficient (see §4).

## 2. Exact input theorem needed

**(H)** There are constants c > 0 and n₀ such that, for infinitely many n (or for all n ≥ n₀), some set S ⊂ ℝ² with |S| = n has u(S) ≥ n^{1 + c/log log n}. Here u(S) is the number of *unordered* pairs at distance exactly 1.

On whether the input is conditional:
- Erdős's 1946 lattice construction gives (H) unconditionally, for all large n. It uses elementary number theory (counting representations as sums of two squares).
- I cannot confirm whether the OpenAI result is unconditional, or whether it improves c or the exponent form. Check its stated hypotheses. Any number-theoretic assumption it makes must become an explicit hypothesis of the bridge.
- A genuine power bound u(n) ≥ n^{1+δ} would disprove Erdős's unit-distance conjecture. Treat such a claim with suspicion.

## 3. Bridge argument (prose, not checked)

1. **Build the graph.** Let G be the unit-distance graph on S, with v = n vertices and e = u(S) edges.

2. **Extract a high-minimum-degree core.** Fix an integer k with k·n < e.
   - While some vertex has degree < k, delete it.
   - Track 2e − 2k·v, which starts positive. Deleting a vertex of degree d ≤ k − 1 changes it by −2d + 2k ≥ 2, so it stays positive.
   - Hence the process stops at a nonempty T ⊆ S in which every point has ≥ k unit-distance neighbours inside T.
   - This is the standard core argument. In ordered-pair form it reads 2k·|S| < P(S), where P counts ordered pairs, so P = 2u.

3. **Choose k.** Take k = ⌈u/n⌉ − 1, so k·n < u strictly. Then k ≥ n^ε − 1, where ε = c/log log n.

4. **Re-express the bound in terms of m = |T|.**
   - Since unit distance is irreflexive, m ≥ k + 1.
   - The function g(x) = exp(c·log x / log log x) = x^{c/log log x} is increasing for x ≥ e^e ≈ 15.2.
   - Since m ≤ n, we get g(m) ≤ g(n).
   - So every point of T has at least g(m) − 1 = m^{c/log log m} − 1 points at distance 1, and these are equidistant from it.

5. **Quantitative output.**
   - The constant c in the exponent is unchanged.
   - The only loss is an additive −1. If you prefer a clean power, use g(m)/2, or any c′ < c for large m.
   - Cardinality: n^{c/log log n} ≤ m ≤ n, so m → ∞ along the input sequence.

## 4. Cardinality caveat (the real gap)

- The core size m is not controlled. You only know m lies in [n^ε, n].
- The bridge gives good sets for infinitely many sizes m, not for every n.
- f is not obviously monotone. Adding points can break the "every point" condition, so the gaps between sizes cannot be filled for free.
- For an "all n" variant you would need a construction that is regular from the start, such as a torus-like modification of the Erdős lattice. I have not verified such a construction here.

## 5. Lean (candidate, not compiled)

```lean
import Mathlib

namespace UnitDistBridge

open Finset

section Generic

variable {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- Number of `r`-neighbours of `x` inside `s`. -/
def deg (s : Finset α) (x : α) : ℕ := (s.filter (r x)).card

/-- Ordered `r`-pairs inside `s` (twice the edge count for symmetric irreflexive `r`). -/
def P (s : Finset α) : ℕ := ∑ y ∈ s, deg r s y

variable {r}

lemma deg_le_deg_erase (hr : Symmetric r) (s : Finset α) (x y : α) :
    deg r s y ≤ deg r (s.erase x) y + if r x y then 1 else 0 := by
  unfold deg
  split_ifs with hxy
  · calc (s.filter (r y)).card
        ≤ (insert x ((s.erase x).filter (r y))).card := by
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_filter] at hz
          by_cases hzx : z = x
          · simp [hzx]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hzx, hz.1⟩, hz.2⟩)
      _ ≤ _ := Finset.card_insert_le _ _
  · simp only [add_zero]
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨Finset.mem_erase.2 ⟨?_, hz.1⟩, hz.2⟩
    rintro rfl
    exact hxy (hr hz.2)

lemma P_le (hr : Symmetric r) {s : Finset α} {x : α} (hx : x ∈ s) :
    P r s ≤ P r (s.erase x) + 2 * deg r s x := by
  have h0 : deg r s x + ∑ y ∈ s.erase x, deg r s y = P r s :=
    Finset.add_sum_erase s (fun y => deg r s y) hx
  have h1 : ∑ y ∈ s.erase x, deg r s y ≤
      ∑ y ∈ s.erase x, (deg r (s.erase x) y + if r x y then 1 else 0) :=
    Finset.sum_le_sum fun y _ => deg_le_deg_erase hr s x y
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ y ∈ s.erase x, (if r x y then 1 else 0) ≤ deg r s x := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset x s))
  have h3 : P r (s.erase x) = ∑ y ∈ s.erase x, deg r (s.erase x) y := rfl
  omega

/-- Core lemma: `2k|s| < P(s)` yields a nonempty subset with minimum degree `≥ k`. -/
theorem exists_minDeg_subset (hr : Symmetric r) (k : ℕ) :
    ∀ s : Finset α, 2 * k * s.card < P r s →
      ∃ t ⊆ s, t.Nonempty ∧ ∀ x ∈ t, k ≤ deg r t x := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hP
    by_cases hall : ∀ x ∈ s, k ≤ deg r s x
    · refine ⟨s, subset_rfl, ?_, hall⟩
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp [P] at hP
    · push_neg at hall
      obtain ⟨x, hx, hlt⟩ := hall
      have hcard : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
      have hmul : 2 * k * s.card = 2 * k * (s.erase x).card + 2 * k := by
        rw [← hcard]; ring
      have hle := P_le hr hx
      obtain ⟨t, hts, htne, htdeg⟩ :=
        ih (s.erase x) (Finset.erase_ssubset hx) (by omega)
      exact ⟨t, hts.trans (Finset.erase_subset x s), htne, htdeg⟩

end Generic

section Planar

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def unitRel (x y : E2) : Prop := dist x y = 1

noncomputable instance : DecidableRel unitRel := Classical.decRel _

lemma unitRel_symm : Symmetric unitRel := fun x y h => by
  unfold unitRel at *; rw [dist_comm]; exact h

/-- `P unitRel s` = 2 × (number of unit distances in `s`). -/
theorem unitDist_core (s : Finset E2) (k : ℕ) (h : 2 * k * s.card < P unitRel s) :
    ∃ t ⊆ s, t.Nonempty ∧ k ≤ t.card ∧ ∀ x ∈ t, k ≤ deg unitRel t x := by
  obtain ⟨t, hts, ⟨x, hx⟩, hdeg⟩ := exists_minDeg_subset unitRel_symm k s h
  exact ⟨t, hts, ⟨x, hx⟩,
    (hdeg x hx).trans (Finset.card_le_card (Finset.filter_subset _ _)), hdeg⟩

/-- Quantitative bridge with explicit assumptions: a bound `g`, monotone from `N₀`
on, transfers from `|s|` to the core size `|t|`. -/
theorem equidistant_of_unitPairs (g : ℕ → ℝ) (N₀ : ℕ) (hmono : MonotoneOn g (Set.Ici N₀))
    (s : Finset E2) (k : ℕ) (hk : g s.card ≤ k) (hN : N₀ ≤ k)
    (h : 2 * k * s.card < P unitRel s) :
    ∃ t ⊆ s, N₀ ≤ t.card ∧ t.card ≤ s.card ∧
      ∀ x ∈ t, g t.card ≤ (deg unitRel t x : ℝ) := by
  obtain ⟨t, hts, -, hkt, hdeg⟩ := unitDist_core s k h
  have hts' : t.card ≤ s.card := Finset.card_le_card hts
  have hg : g t.card ≤ g s.card :=
    hmono (Set.mem_Ici.2 (hN.trans hkt)) (Set.mem_Ici.2 ((hN.trans hkt).trans hts')) hts'
  exact ⟨t, hts, hN.trans hkt, hts', fun x hx =>
    hg.trans (hk.trans (by exact_mod_cast hdeg x hx))⟩

end Planar

end UnitDistBridge
```

## 6. Checked vs. prose

**Intended as checked proof, once it compiles:**
- the core lemma `exists_minDeg_subset`;
- its planar instance `unitDist_core`;
- the transfer `equidistant_of_unitPairs`.

All of these assume nothing beyond Mathlib.

**Still prose only:**
- (H) itself.
- The choice k = ⌈u/n⌉ − 1.
- Monotonicity of x ↦ x^{c/log log x} on [16, ∞) (needs a short `Real.rpow`/`Real.log` derivative argument).
- Matching `deg unitRel` and `P` to FC's definitions. FC probably states "equidistant" through a sphere or `dist` condition and may use a different point type.

**Likely compile risks:**
- the name `Finset.strongInduction` and its case label `H`;
- whether `omega` treats `2 * k * card` as an atom;
- the exact form of `Finset.card_filter`.

**Next steps, once tools are allowed:**
1. Read FC's `ErdosProblems/92.lean` to fix which case of §1 applies.
2. Read the OpenAI source to settle whether (H) is conditional and what its constants are.
3. Run `lake build`.
