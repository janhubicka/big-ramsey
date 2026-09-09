import Mathlib
import ConcreteFiniteGraph

/-!
# Submodularity and closure calculus for the concrete `C₀` predimension
-/

namespace SparseBigRamsey.C0
open Finset
variable {V : Type*} [LinearOrder V]
namespace FiniteGraph
variable (G : FiniteGraph V)

def edgeIndicator (X : Finset V) (e : V × V) : Nat :=
  if e.1 ∈ X ∧ e.2 ∈ X then 1 else 0

theorem card_edgesOn_eq_sum_indicator (X : Finset V) :
    (G.edgesOn X).card = ∑ e ∈ G.edges, G.edgeIndicator X e := by
  classical
  simp [edgesOn, edgeIndicator, Finset.card_filter]

theorem edgeIndicator_supermodular
    (X Y : Finset V) (e : V × V) :
    G.edgeIndicator X e + G.edgeIndicator Y e ≤
      G.edgeIndicator (X ∪ Y) e + G.edgeIndicator (X ∩ Y) e := by
  classical
  rcases e with ⟨u,v⟩
  by_cases huX : u ∈ X <;>
  by_cases hvX : v ∈ X <;>
  by_cases huY : u ∈ Y <;>
  by_cases hvY : v ∈ Y <;>
    simp [edgeIndicator, huX, hvX, huY, hvY]

theorem edgeCount_supermodular (X Y : Finset V) :
    (G.edgesOn X).card + (G.edgesOn Y).card ≤
      (G.edgesOn (X ∪ Y)).card + (G.edgesOn (X ∩ Y)).card := by
  classical
  rw [G.card_edgesOn_eq_sum_indicator X,
      G.card_edgesOn_eq_sum_indicator Y,
      G.card_edgesOn_eq_sum_indicator (X ∪ Y),
      G.card_edgesOn_eq_sum_indicator (X ∩ Y)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e he => G.edgeIndicator_supermodular X Y e)

theorem predim_submodular (X Y : Finset V) :
    G.predim (X ∪ Y) + G.predim (X ∩ Y) ≤
      G.predim X + G.predim Y := by
  classical
  have hv := Finset.card_union_add_card_inter X Y
  have he := G.edgeCount_supermodular X Y
  simp only [predim]
  omega

theorem Strong.trans
    {A B C : Finset V}
    (hAB : G.Strong A B)
    (hBC : G.Strong B C) :
    G.Strong A C := by
  classical
  refine ⟨hAB.1.trans hBC.1, ?_⟩
  intro X hAX hXC
  have hA_B : A ⊆ B := hAB.1
  have hB_C : B ⊆ C := hBC.1
  have hB_union : B ⊆ X ∪ B := Finset.subset_union_right
  have hUnion_C : X ∪ B ⊆ C := Finset.union_subset hXC hB_C
  have hBCineq := hBC.2 (X ∪ B) hB_union hUnion_C
  have hA_inter : A ⊆ X ∩ B := by
    intro a ha
    exact Finset.mem_inter.mpr ⟨hAX ha, hA_B ha⟩
  have hInter_B : X ∩ B ⊆ B := Finset.inter_subset_right
  have hABineq := hAB.2 (X ∩ B) hA_inter hInter_B
  have hsub := G.predim_submodular X B
  omega

theorem strong_inter
    {P Q C : Finset V}
    (hPC : G.Strong P C)
    (hQC : G.Strong Q C) :
    G.Strong (P ∩ Q) C := by
  classical
  refine ⟨?_, ?_⟩
  · exact (Finset.inter_subset_left.trans hPC.1)
  · intro Z hIZ hZC
    have hP_union : P ⊆ P ∪ Z := Finset.subset_union_left
    have hPUnion_C : P ∪ Z ⊆ C := Finset.union_subset hPC.1 hZC
    have hPineq := hPC.2 (P ∪ Z) hP_union hPUnion_C
    have hsubP := G.predim_submodular P Z
    have hZ_ge_interP : G.predim (P ∩ Z) ≤ G.predim Z := by omega
    have hQ_union : Q ⊆ Q ∪ (P ∩ Z) := Finset.subset_union_left
    have hQUnion_C : Q ∪ (P ∩ Z) ⊆ C := by
      apply Finset.union_subset hQC.1
      exact Finset.inter_subset_right.trans hZC
    have hQineq := hQC.2 (Q ∪ (P ∩ Z)) hQ_union hQUnion_C
    have hsubQ := G.predim_submodular Q (P ∩ Z)
    have hIntersection : Q ∩ (P ∩ Z) = P ∩ Q := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxQ,hxPZ⟩
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxPZ).1,hxQ⟩
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxP,hxQ⟩
        have hxZ : x ∈ Z := hIZ (Finset.mem_inter.mpr ⟨hxP,hxQ⟩)
        exact Finset.mem_inter.mpr ⟨hxQ, Finset.mem_inter.mpr ⟨hxP,hxZ⟩⟩
    rw [hIntersection] at hsubQ
    have hPZ_ge_I : G.predim (P ∩ Q) ≤ G.predim (P ∩ Z) := by omega
    exact hPZ_ge_I.trans hZ_ge_interP

end FiniteGraph
end SparseBigRamsey.C0
