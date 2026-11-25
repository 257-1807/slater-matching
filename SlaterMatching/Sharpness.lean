module

public import SlaterMatching.Matching
public import SlaterMatching.Slater
public import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

public section

namespace SlaterMatching

open SimpleGraph Finset

private theorem pathFour_degrees :
    ∀ v : Fin 4, 1 ≤ (pathGraph 4).degree v ∧ (pathGraph 4).degree v ≤ 2 := by
  decide

/-- Either endpoint of the four-vertex path attains the minimum degree. -/
theorem pathFour_minDegree : (pathGraph 4).minDegree = 1 := by decide

/-- The degree sequence of the four-vertex path is 2, 2, 1, 1. -/
theorem pathFour_slaterNumber : slaterNumber (pathGraph 4) = 2 := by
  have upper (k : ℕ) : largestDegreeSum (pathGraph 4) k ≤ k * 2 := by
    rw [largestDegreeSum.eq_def]
    apply Finset.sup_le
    intro T hT
    calc
      _ ≤ ∑ _ ∈ T, 2 := Finset.sum_le_sum fun v _ => (pathFour_degrees v).2
      _ = k * 2 := by simp [(Finset.mem_powersetCard.mp hT).2]
  have hlow := slater_spec (pathGraph 4)
  rw [Fintype.card_fin] at hlow
  have hn := upper (slaterNumber (pathGraph 4))
  have pair := degreeSum_le_largestDegreeSum (pathGraph 4) ({1, 2} : Finset (Fin 4))
  have hcard : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hsum : (∑ v ∈ ({1, 2} : Finset (Fin 4)), (pathGraph 4).degree v) = 4 := by decide
  rw [hcard, hsum] at pair
  have hhi : slaterNumber (pathGraph 4) ≤ 2 := by
    rw [slaterNumber.eq_def]
    apply Nat.sInf_le (s := {k : ℕ | Fintype.card (Fin 4) ≤ k + largestDegreeSum (pathGraph 4) k})
    change 4 ≤ 2 + largestDegreeSum (pathGraph 4) 2
    omega
  omega

/-- The middle edge is a maximal matching. The graph has an edge, so every maximal
matching contains at least one edge. -/
theorem pathFour_minMaximalMatchingNumber : minMaximalMatchingNumber (pathGraph 4) = 1 := by
  have h12 : (pathGraph 4).Adj 1 2 := by decide
  let M := (pathGraph 4).subgraphOfAdj h12
  have hM : Maximal (fun N : (pathGraph 4).Subgraph => N.IsMatching) M := by
    apply maximal_of_hits M (Subgraph.IsMatching.subgraphOfAdj h12)
    have h : ∀ u v : Fin 4, (pathGraph 4).Adj u v →
        u ∈ ({1, 2} : Set (Fin 4)) ∨ v ∈ ({1, 2} : Set (Fin 4)) := by decide
    exact fun {u v} huv => h u v huv
  have hupper := minMaximalMatchingNumber_le M hM
  have hcard : Nat.card M.edgeSet = 1 := by
    change ((pathGraph 4).subgraphOfAdj h12).edgeSet.ncard = 1
    rw [edgeSet_subgraphOfAdj, Set.ncard_singleton]
  rw [hcard] at hupper
  obtain ⟨N, hN, hn⟩ := exists_minimum_matching (pathGraph 4)
  have hsup := matching_support_card N hN.1
  rw [hn] at hsup
  have hne : N.verts.Nonempty := by
    rcases maximal_hits N hN h12 with h | h
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hpos : 0 < N.verts.ncard := (Set.ncard_pos).mpr hne
  omega

/-- Minimum degree one does not suffice for the Slater bound. -/
theorem pathFour_sharpness :
    (∀ v : Fin 4, 1 ≤ (pathGraph 4).degree v) ∧
      minMaximalMatchingNumber (pathGraph 4) < slaterNumber (pathGraph 4) := by
  exact ⟨fun v => (pathFour_degrees v).1, by
    rw [pathFour_minMaximalMatchingNumber, pathFour_slaterNumber]
    decide⟩

end SlaterMatching
