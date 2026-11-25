module

public import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Lattice.Nat

public section

namespace SlaterMatching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The minimum edge count of an inclusion-maximal matching. -/
noncomputable def minMaximalMatchingNumber (G : SimpleGraph V) [Fintype V] : ℕ :=
  sInf {k | ∃ M : G.Subgraph, Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
    Nat.card M.edgeSet = k}

/-- The finite graph has a maximal matching that realizes its minimum. -/
theorem exists_minimum_matching (G : SimpleGraph V) [Fintype V] :
    ∃ M : G.Subgraph, Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
      Nat.card M.edgeSet = minMaximalMatchingNumber G := by
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    exact False.elim hv
  obtain ⟨M, hM⟩ := ({N : G.Subgraph | N.IsMatching}.toFinite).exists_maximal ⟨⊥, hbot⟩
  exact Nat.sInf_mem (s := {k | ∃ N : G.Subgraph,
    Maximal (fun L : G.Subgraph => L.IsMatching) N ∧ Nat.card N.edgeSet = k})
    ⟨Nat.card M.edgeSet, M, hM, rfl⟩

/-- A matching with k edges covers exactly 2k vertices. -/
theorem matching_support_card [Fintype V] (M : G.Subgraph) (hm : M.IsMatching) :
    M.verts.ncard = 2 * Nat.card M.edgeSet := by
  classical
  have he : M.edgeSet.ncard = M.coe.edgeSet.ncard := by
    rw [← M.image_coe_edgeSet_coe, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  change M.verts.ncard = 2 * M.edgeSet.ncard
  rw [he, ← Set.fintypeCard_eq_ncard M.coe.edgeSet, M.coe.card_edgeSet,
    ← M.coe.sum_degrees_eq_twice_card_edges]
  rw [Subgraph.isMatching_iff_forall_degree] at hm
  have hone (v : M.verts) : M.degree v = 1 := by
    convert! hm v v.property using 1
    congr 1
    exact Subsingleton.elim _ _
  simp only [Subgraph.coe_degree, hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Set.fintypeCard_eq_ncard]

/-- Otherwise the edge can be added to the matching. -/
theorem maximal_hits (M : G.Subgraph)
    (hm : Maximal (fun N : G.Subgraph => N.IsMatching) M) {u v : V} (h : G.Adj u v) :
    u ∈ M.verts ∨ v ∈ M.verts := by
  classical
  by_contra! hmiss
  have disj : Disjoint M.support (G.subgraphOfAdj h).support := by
    rw [hm.1.support_eq_verts, support_subgraphOfAdj, Set.disjoint_left]
    intro x hx hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | heq
    · exact hmiss.1 hx
    · exact hmiss.2 ((Set.mem_singleton_iff.mp heq) ▸ hx)
  have hle : M ⊔ G.subgraphOfAdj h ≤ M :=
    hm.2 (hm.1.sup (Subgraph.IsMatching.subgraphOfAdj h) disj) le_sup_left
  have hedge : G.subgraphOfAdj h ≤ M := le_sup_right.trans hle
  exact hmiss.1 (M.edge_vert ((G.subgraphOfAdj_le_iff h M).mp hedge))

/-- A matching meeting every edge is inclusion-maximal. -/
theorem maximal_of_hits (M : G.Subgraph) (hm : M.IsMatching)
    (hits : ∀ ⦃u v⦄, G.Adj u v → u ∈ M.verts ∨ v ∈ M.verts) :
    Maximal (fun N : G.Subgraph => N.IsMatching) M := by
  refine ⟨hm, ?_⟩
  intro N hn hle
  have from_matched {a b : V} (hab : N.Adj a b) (ha : a ∈ M.verts) : M.Adj a b := by
    obtain ⟨c, hc, _⟩ := hm ha
    exact (hn.eq_of_adj_left (hle.2 hc) hab) ▸ hc
  have back {a b : V} (hab : N.Adj a b) : M.Adj a b := by
    rcases hits (N.adj_sub hab) with ha | hb
    · exact from_matched hab ha
    · exact (from_matched hab.symm hb).symm
  refine ⟨?_, fun _ _ => back⟩
  intro v hv
  obtain ⟨w, hw, _⟩ := hn hv
  exact M.edge_vert (back hw)

/-- Any particular maximal matching supplies an upper bound for the minimum. -/
theorem minMaximalMatchingNumber_le [Fintype V] (M : G.Subgraph)
    (hm : Maximal (fun N : G.Subgraph => N.IsMatching) M) :
    minMaximalMatchingNumber G ≤ Nat.card M.edgeSet :=
  Nat.sInf_le (s := {k | ∃ N : G.Subgraph,
    Maximal (fun L : G.Subgraph => L.IsMatching) N ∧ Nat.card N.edgeSet = k})
    ⟨M, hm, rfl⟩

end SlaterMatching
