# Claude dense-core attempt

Unverified; edge lower bound is an assumption.

Model: claude-opus-5-5[1m]; session: 6a94c34d-c35f-40a4-bb97-6d63fd9a7b8e; reported cost: $0.6001610000000001. Tools disabled.

Prompt: Develop a complete Lean 4 supporting theorem that connects a finite symmetric irreflexive graph with at least C*n^(1+δ) edges to a nonempty induced subgraph of minimum degree at least k, and proves the subgraph cardinality is at least k+1. Use previously established exists_subset_forall_lt_degIn; focus on rigorous quantitative lower bound sufficient to transfer arbitrarily large polynomial unit-distance edge counts to Erdős 92. State exact assumptions, no axioms, sorry, admit, unsafe, native_decide, no fake proof. Give full Lean code or honestly report gaps. Do not execute tools; CI separately compiles.

I couldn't see the repository, because you asked me not to run tools. So I don't know the exact statement of `exists_subset_forall_lt_degIn`, and calling it with a guessed signature would probably fail in CI. Instead, the file below is self-contained. `exists_nonempty_le_nbrIn` proves the core peeling and extremal step that lemma most likely covers. Adapter notes for switching to your lemma are at the end. The code has not been compiled.

## Exact assumptions

- **Graph:** `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`. Mathlib's `SimpleGraph` is exactly a finite symmetric irreflexive relation once `Fintype V` is given.
- **Induced degree:** `nbrIn G S v := #{w ∈ S | G.Adj v w}`. For `v ∈ S` this is the degree of `v` in `G[S]`. I did not formalize the bridge to `(G.induce S).degree`.
- **Combinatorial core:** if `(2k − 1)·n < Σ_v deg v`, there is a nonempty `S` with `k ≤ nbrIn G S v` for all `v ∈ S`.
- **Edge form:** `k·n ≤ |E|` and `0 < n` give such an `S`, and also `k + 1 ≤ |S|`.
- **Polynomial form:** `k ≤ C·n^δ` and `C·n^(1+δ) ≤ |E|` with `0 < n`. No sign conditions on `C` or `δ` are needed.
- **Uniform transfer:** for `C > 0`, `δ > 0` and any `k`, there is an `N` such that every graph on `n ≥ N` vertices with at least `C·n^(1+δ)` edges contains such an `S` with `|S| ≥ k + 1`.

```lean
import Mathlib

open Finset

namespace TheoremAtlas.Erdos92Support

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of neighbours of `v` inside `S`; for `v ∈ S` this is the degree of `v` in `G[S]`. -/
def nbrIn (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

/-- Number of ordered adjacent pairs inside `S`, i.e. twice the edge count of `G[S]`. -/
def pairCount (S : Finset V) : ℕ := ∑ v ∈ S, nbrIn G S v

lemma nbrIn_erase_self (S : Finset V) (v : V) :
    nbrIn G (S.erase v) v = nbrIn G S v := by
  unfold nbrIn
  congr 1
  ext w
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨-, hw⟩, h⟩
    exact ⟨hw, h⟩
  · rintro ⟨hw, h⟩
    exact ⟨⟨(G.ne_of_adj h).symm, hw⟩, h⟩

lemma nbrIn_split (S : Finset V) {v : V} (hv : v ∈ S) (u : V) :
    nbrIn G S u = nbrIn G (S.erase v) u + if G.Adj u v then 1 else 0 := by
  unfold nbrIn
  rw [card_filter, card_filter]
  exact (sum_erase_add S (fun w => if G.Adj u w then 1 else 0) hv).symm

lemma pairCount_eq (S : Finset V) {v : V} (hv : v ∈ S) :
    pairCount G S = pairCount G (S.erase v) + 2 * nbrIn G S v := by
  have h0 : pairCount G S = ∑ u ∈ S.erase v, nbrIn G S u + nbrIn G S v := by
    unfold pairCount
    exact (sum_erase_add S _ hv).symm
  have h1 : ∑ u ∈ S.erase v, nbrIn G S u
      = pairCount G (S.erase v) + ∑ u ∈ S.erase v, (if G.Adj u v then 1 else 0) := by
    unfold pairCount
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun u _ => nbrIn_split G S hv u)
  have h2 : ∑ u ∈ S.erase v, (if G.Adj u v then 1 else 0) = nbrIn G S v := by
    rw [← nbrIn_erase_self G S v]
    unfold nbrIn
    rw [card_filter]
    refine sum_congr rfl (fun u _ => ?_)
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos h.symm]
    · have h' : ¬ G.Adj v u := fun h' => h h'.symm
      rw [if_neg h, if_neg h']
  rw [h0, h1, h2]
  ring

lemma pairCount_univ : pairCount G univ = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  unfold pairCount nbrIn
  refine sum_congr rfl fun v _ => ?_
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

/-- A nonempty vertex set on which every vertex has at least `k` neighbours
has at least `k + 1` elements (irreflexivity excludes `v` from its own neighbours). -/
lemma card_ge_of_le_nbrIn {S : Finset V} {k : ℕ} (hne : S.Nonempty)
    (h : ∀ v ∈ S, k ≤ nbrIn G S v) : k + 1 ≤ S.card := by
  obtain ⟨v, hv⟩ := hne
  have h1 : nbrIn G S v ≤ (S.erase v).card := by
    rw [← nbrIn_erase_self G S v]
    unfold nbrIn
    exact card_filter_le _ _
  have h2 := card_erase_add_one hv
  have h3 := h v hv
  omega

/-- Core extremal step: maximise `pairCount S - (2k-1)|S|` over all `S`.
Deleting a vertex of inner degree `< k` would strictly increase the potential. -/
theorem exists_nonempty_le_nbrIn (k : ℕ)
    (h : (2 * k - 1 : ℤ) * Fintype.card V < pairCount G univ) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, k ≤ nbrIn G S v := by
  obtain ⟨S, -, hS⟩ := (univ : Finset (Finset V)).exists_max_image
    (fun S => (pairCount G S : ℤ) - (2 * k - 1) * S.card) univ_nonempty
  have hpos : 0 < (pairCount G S : ℤ) - (2 * k - 1) * S.card := by
    have h1 : (pairCount G univ : ℤ) - (2 * k - 1) * (univ : Finset V).card
        ≤ (pairCount G S : ℤ) - (2 * k - 1) * S.card := hS univ (mem_univ _)
    rw [card_univ] at h1
    linarith
  refine ⟨S, ?_, ?_⟩
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [pairCount] at hpos
  · intro v hv
    by_contra hlt
    push_neg at hlt
    have hmax : (pairCount G (S.erase v) : ℤ) - (2 * k - 1) * (S.erase v).card
        ≤ (pairCount G S : ℤ) - (2 * k - 1) * S.card := hS (S.erase v) (mem_univ _)
    have hpc : (pairCount G S : ℤ) = pairCount G (S.erase v) + 2 * nbrIn G S v := by
      exact_mod_cast pairCount_eq G S hv
    have hcard : ((S.erase v).card : ℤ) + 1 = S.card := by
      exact_mod_cast card_erase_add_one hv
    have hlt' : (nbrIn G S v : ℤ) + 1 ≤ k := by omega
    have key : (2 * (k : ℤ) - 1) * S.card
        = (2 * k - 1) * (S.erase v).card + (2 * k - 1) := by
      rw [← hcard]; ring
    linarith

/-- Edge form: `k·n ≤ |E|` yields a nonempty induced subgraph of minimum degree `≥ k`
on at least `k + 1` vertices. -/
theorem exists_induced_minDegree_of_card_edges (k : ℕ)
    (h : k * Fintype.card V ≤ G.edgeFinset.card) (hV : 0 < Fintype.card V) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ v ∈ S, k ≤ nbrIn G S v) ∧ k + 1 ≤ S.card := by
  obtain ⟨S, hne, hdeg⟩ := exists_nonempty_le_nbrIn G k (by
    rw [pairCount_univ]
    push_cast
    have h' : ((k : ℤ) * Fintype.card V) ≤ G.edgeFinset.card := by exact_mod_cast h
    have hV' : (0 : ℤ) < Fintype.card V := by exact_mod_cast hV
    linarith)
  exact ⟨S, hne, hdeg, card_ge_of_le_nbrIn G hne hdeg⟩

/-- Polynomial form: `C·n^(1+δ) ≤ |E|` and `k ≤ C·n^δ` give the same conclusion. -/
theorem exists_dense_core_of_rpow (C δ : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ C * (Fintype.card V : ℝ) ^ δ)
    (hE : C * (Fintype.card V : ℝ) ^ (1 + δ) ≤ G.edgeFinset.card)
    (hV : 0 < Fintype.card V) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ v ∈ S, k ≤ nbrIn G S v) ∧ k + 1 ≤ S.card := by
  refine exists_induced_minDegree_of_card_edges G k ?_ hV
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  have hsplit : (Fintype.card V : ℝ) ^ (1 + δ)
      = Fintype.card V * (Fintype.card V : ℝ) ^ δ := by
    rw [Real.rpow_add hn, Real.rpow_one]
  have hreal : (k : ℝ) * Fintype.card V ≤ G.edgeFinset.card := by
    rw [hsplit] at hE
    nlinarith [mul_le_mul_of_nonneg_left hk hn.le]
  exact_mod_cast hreal

/-- For fixed `C, δ > 0`, the threshold `k ≤ C·n^δ` holds for all large `n`. -/
theorem eventually_le_mul_rpow (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (k : ℝ) ≤ C * (n : ℝ) ^ δ := by
  refine ⟨⌈((k : ℝ) / C) ^ δ⁻¹⌉₊, fun n hn => ?_⟩
  have hkC : 0 ≤ (k : ℝ) / C := div_nonneg (Nat.cast_nonneg k) hC.le
  have h1 : ((k : ℝ) / C) ^ δ⁻¹ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : (k : ℝ) / C ≤ (n : ℝ) ^ δ := by
    calc (k : ℝ) / C = (((k : ℝ) / C) ^ δ⁻¹) ^ δ :=
          (Real.rpow_inv_rpow hkC hδ.ne').symm
      _ ≤ (n : ℝ) ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hkC _) h1 hδ.le
  linarith [(div_le_iff₀ hC).mp h2]

/-- Uniform transfer: graphs with `≥ C·n^(1+δ)` edges (`C, δ > 0`) on enough vertices
contain a nonempty induced subgraph of minimum degree `≥ k` with `≥ k + 1` vertices. -/
theorem dense_core_transfer (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) (k : ℕ) :
    ∃ N : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj],
      N ≤ Fintype.card W →
      C * (Fintype.card W : ℝ) ^ (1 + δ) ≤ H.edgeFinset.card →
      ∃ S : Finset W, S.Nonempty ∧ (∀ v ∈ S, k ≤ nbrIn H S v) ∧ k + 1 ≤ S.card := by
  obtain ⟨N, hN⟩ := eventually_le_mul_rpow C δ hC hδ k
  refine ⟨max N 1, fun W _ _ H _ hW hE => ?_⟩
  exact exists_dense_core_of_rpow H C δ k (hN _ (le_of_max_le_left hW)) hE
    (lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hW))

end TheoremAtlas.Erdos92Support
```

## Proof strategy

- **Extremal step:** choose `S` maximizing `pairCount S − (2k−1)|S|`.
  - Removing a vertex `v` lowers `pairCount` by exactly `2·nbrIn S v` (lemma `pairCount_eq`).
  - If `nbrIn S v ≤ k − 1`, removing `v` would strictly increase the potential, contradicting maximality.
  - The potential of `univ` is positive, so `S` has positive potential and is nonempty.
- **Size bound:** irreflexivity gives `nbrIn S v ≤ |S.erase v| = |S| − 1`, so `|S| ≥ k + 1`.
- **Quantitative transfer:** `n^(1+δ) = n·n^δ`, so `k ≤ C·n^δ` turns the edge bound into `k·n ≤ |E|`. The threshold is `N = max(⌈(k/C)^(1/δ)⌉, 1)`.

## Gaps and risks

1. **Not compiled.** These names are the most likely to break: `Finset.card_filter`, `SimpleGraph.neighborFinset_eq_filter`, `Real.rpow_inv_rpow` and `div_le_iff₀`. If `pairCount_univ` fails, `simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]` is a likely fallback.
2. **Your existing lemma is not used.** To switch to `exists_subset_forall_lt_degIn`, replace the body of `exists_nonempty_le_nbrIn` with a call to it.
   - If your `degIn` is `(S.filter (G.Adj v)).card`, it is definitionally `nbrIn` and `rfl` bridges the two.
   - If your lemma concludes `k < degIn S v`, call it with `k − 1`, or adjust the hypothesis to `2k·n < pairCount`.
3. **No bridge to `G.induce`.** Nothing formally states `nbrIn G S v = (G.induce ↑S).degree ⟨v, hv⟩`. Add it if Erdős 92 needs `SimpleGraph.minDegree` literally.
4. **The unit-distance step is out of scope.** These theorems take the edge lower bound `C·n^(1+δ)` as a hypothesis. They do not prove it for any unit-distance graph.

The file contains no `axiom`, `sorry`, `admit`, `unsafe` or `native_decide`.
