module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

public section

namespace SlaterMatching

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sum of the largest `k` degrees, maximized over the subsets of size `k`. -/
@[expose] noncomputable def largestDegreeSum (k : ℕ) : ℕ := by
  classical
  exact (univ.powersetCard k).sup (fun S => ∑ v ∈ S, G.degree v)

/-- The least `k` whose largest `k` degrees, plus `k`, reach the order of the graph. -/
@[expose] noncomputable def slaterNumber : ℕ :=
  sInf {k : ℕ | Fintype.card V ≤ k + largestDegreeSum G k}

theorem slater_spec :
    Fintype.card V ≤ slaterNumber G + largestDegreeSum G (slaterNumber G) := by
  apply Nat.sInf_mem (s := {k : ℕ | Fintype.card V ≤ k + largestDegreeSum G k})
  exact ⟨Fintype.card V, Nat.le_add_right _ _⟩

theorem degreeSum_le_largestDegreeSum (S : Finset V) :
    ∑ v ∈ S, G.degree v ≤ largestDegreeSum G S.card := by
  classical
  apply Finset.le_sup (f := fun T : Finset V => ∑ v ∈ T, G.degree v)
  exact mem_powersetCard.mpr ⟨subset_univ _, rfl⟩

/-- Split the covered vertices into two equally large sets. Each half is bounded
by the maximum degree sum of a set of its size. -/
theorem slater_le_of_endpoint_sum (S : Finset V) (k : ℕ) (hcard : S.card = 2 * k)
    (hsum : 2 * (Fintype.card V - S.card) + S.card ≤ ∑ v ∈ S, G.degree v) :
    slaterNumber G ≤ k := by
  classical
  obtain ⟨A, hAS, hA⟩ := exists_subset_card_eq (show k ≤ S.card by omega)
  have hB : (S \ A).card = k := by rw [card_sdiff_of_subset hAS]; omega
  have h₁ := degreeSum_le_largestDegreeSum G A
  have h₂ := degreeSum_le_largestDegreeSum G (S \ A)
  rw [hA] at h₁
  rw [hB] at h₂
  have hsplit := sum_sdiff hAS (f := fun v => G.degree v)
  have hn := card_le_univ S
  apply Nat.sInf_le (s := {t : ℕ | Fintype.card V ≤ t + largestDegreeSum G t})
  change Fintype.card V ≤ k + largestDegreeSum G k
  omega

end SlaterMatching
