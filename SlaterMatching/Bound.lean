module

public import SlaterMatching.Counting
public import SlaterMatching.Matching
public import SlaterMatching.Slater
import Mathlib.Tactic

public section

namespace SlaterMatching

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree sequence gives a lower bound for the size of every maximal matching
whenever every vertex has at least two neighbors. -/
theorem slater_le_card_maximal (hdeg : ∀ v, 2 ≤ G.degree v) (M : G.Subgraph)
    (hm : Maximal (fun N : G.Subgraph => N.IsMatching) M) :
    slaterNumber G ≤ Nat.card M.edgeSet := by
  classical
  let S := M.verts.toFinset
  have memS {v : V} : v ∈ S ↔ v ∈ M.verts := Set.mem_toFinset
  have hcard : S.card = 2 * Nat.card M.edgeSet := by
    rw [← matching_support_card M hm.1]
    exact (Set.ncard_eq_toFinset_card' _).symm
  apply slater_le_of_endpoint_sum G S _ hcard
  apply endpoint_sum_lower G S hdeg
  · intro u v huv
    exact (maximal_hits M hm huv).imp memS.mpr memS.mpr
  · intro v hv
    obtain ⟨w, h, _⟩ := hm.1 (memS.mp hv)
    exact ⟨w, memS.mpr h.snd_mem, M.adj_sub h⟩

/-- The strengthened bound applies to every finite simple graph of minimum degree at least two. -/
theorem slater_le_minMaximalMatching (hdeg : ∀ v, 2 ≤ G.degree v) :
    slaterNumber G ≤ minMaximalMatchingNumber G := by
  obtain ⟨M, hm, hsize⟩ := exists_minimum_matching G
  exact hsize ▸ slater_le_card_maximal G hdeg M hm

/-- The source convention for Eulerian graphs includes connectivity. -/
theorem eulerian_bound (hn : 2 ≤ Fintype.card V)
    (he : G.Connected ∧ ∀ v, G.degree v % 2 = 0) :
    slaterNumber G ≤ minMaximalMatchingNumber G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  apply slater_le_minMaximalMatching
  intro v
  have hpos := he.1.preconnected.degree_pos_of_nontrivial v
  have heven := he.2 v
  omega

/-- Pastorek, AutoGraphForge candidate d7f95ad0 (rank 605 in the author's table). -/
theorem conjecture_d7f95ad0 (hn : 2 ≤ Fintype.card V) (_hK4 : G.CliqueFree 4)
    (he : G.Connected ∧ ∀ v, G.degree v % 2 = 0) :
    slaterNumber G ≤ minMaximalMatchingNumber G :=
  eulerian_bound G hn he

end SlaterMatching

#print axioms SlaterMatching.slater_le_minMaximalMatching
#print axioms SlaterMatching.conjecture_d7f95ad0
