module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Finite

public section

namespace SlaterMatching

open Finset
open scoped BigOperators

/-- Count the edges crossing a vertex cover in both directions. Every outside vertex
contributes at least two crossing edges, and every inside vertex has an additional
neighbor inside the cover. -/
theorem endpoint_sum_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hcover : ∀ {v w}, G.Adj v w → v ∈ S ∨ w ∈ S)
    (hinternal : ∀ v ∈ S, ∃ w ∈ S, G.Adj v w) :
    2 * (Fintype.card V - S.card) + S.card ≤ ∑ v ∈ S, G.degree v := by
  have hout (v : V) (hv : v ∈ Sᶜ) : S.bipartiteAbove G.Adj v = G.neighborFinset v := by
    ext w
    rw [mem_bipartiteAbove, G.mem_neighborFinset]
    exact ⟨And.right, fun h => ⟨(hcover h).resolve_left (mem_compl.mp hv), h⟩⟩
  have hin (v : V) (hv : v ∈ S) :
      (Sᶜ.bipartiteBelow G.Adj v).card + 1 ≤ G.degree v := by
    obtain ⟨w, hw, hvw⟩ := hinternal v hv
    apply Finset.card_lt_card
    have hsub : Sᶜ.bipartiteBelow G.Adj v ⊆ G.neighborFinset v := fun u hu =>
      (G.mem_neighborFinset v u).mpr ((mem_bipartiteBelow G.Adj).mp hu).2.symm
    exact (Finset.ssubset_iff_of_subset hsub).mpr
      ⟨w, (G.mem_neighborFinset v w).mpr hvw, fun h =>
        (mem_compl.mp ((mem_bipartiteBelow G.Adj).mp h).1) hw⟩
  have hcross : 2 * Sᶜ.card ≤ ∑ v ∈ S, (Sᶜ.bipartiteBelow G.Adj v).card := by
    rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      2 * Sᶜ.card = ∑ _ ∈ Sᶜ, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => by rw [hout v hv]; exact hdeg v
  calc
    _ = 2 * Sᶜ.card + S.card := by rw [Finset.card_compl]
    _ ≤ (∑ v ∈ S, (Sᶜ.bipartiteBelow G.Adj v).card) + S.card := Nat.add_le_add_right hcross _
    _ = ∑ v ∈ S, ((Sᶜ.bipartiteBelow G.Adj v).card + 1) := by simp [sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum hin

end SlaterMatching
