import Mathlib
import ConcreteFiniteGraph
import CapacitatedHall

namespace SparseBigRamsey.C0
open Finset
variable {V : Type*} [LinearOrder V]
namespace FiniteGraph
variable (G : FiniteGraph V)

theorem tail_assignment_outdegree_bound
    {A C : Finset V}
    (hStrong : G.Strong A C) :
    ∃ T : G.TailAssignment A (C \ A),
      ∀ x ∈ C \ A,
        G.downDegree A x +
          (Finset.univ.filter
            (fun e : G.InternalEdge (C \ A) => T.tail e = x)).card
        ≤ 2 := by
  classical
  rcases G.exists_tail_assignment hStrong with ⟨T⟩
  refine ⟨T, ?_⟩
  intro x hx
  have hd := G.downDegree_le_two hStrong hx
  have hc := T.capacity_ok x
  simp only [capacity] at hc
  omega

theorem relative_Hall_Hakimi
    {A C : Finset V}
    (hStrong : G.Strong A C) :
    ∃ T : G.TailAssignment A (C \ A),
      (∀ e, T.tail e = e.1.1 ∨ T.tail e = e.1.2) ∧
      (∀ x ∈ C \ A,
        G.downDegree A x +
          (Finset.univ.filter
            (fun e : G.InternalEdge (C \ A) => T.tail e = x)).card
        ≤ 2) := by
  rcases G.tail_assignment_outdegree_bound hStrong with ⟨T,hT⟩
  exact ⟨T, T.endpoint, hT⟩

end FiniteGraph
end SparseBigRamsey.C0
