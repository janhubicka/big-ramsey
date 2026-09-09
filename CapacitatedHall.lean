import Mathlib
import Formalization.HallMarriage
import ConcreteFiniteGraph

namespace SparseBigRamsey.C0
open Finset
open HallMarriage
variable {V : Type*} [LinearOrder V]
namespace FiniteGraph

def slotSet (cap : V → Nat) (x : V) : Finset (V × Nat) :=
  {x} ×ˢ Finset.range (cap x)

theorem card_slotSet (cap : V → Nat) (x : V) :
    (slotSet cap x).card = cap x := by simp [slotSet]

theorem pairwiseDisjoint_slotSet
    (cap : V → Nat) (X : Finset V) :
    (X : Set V).PairwiseDisjoint (slotSet cap) := by
  classical
  intro x hx y hy hxy
  rw [Finset.disjoint_left]
  intro s hsx hsy
  simp only [slotSet, mem_product, mem_singleton, mem_range] at hsx hsy
  exact hxy (hsx.1.symm.trans hsy.1)

theorem card_slots_over (cap : V → Nat) (X : Finset V) :
    (X.biUnion (slotSet cap)).card = ∑ x ∈ X, cap x := by
  classical
  rw [Finset.card_biUnion (pairwiseDisjoint_slotSet cap X)]
  apply Finset.sum_congr rfl
  intro x hx
  exact card_slotSet cap x

variable (G : FiniteGraph V)

def InternalEdge (B : Finset V) := {e : V × V // e ∈ G.edgesOn B}

instance instDecidableEqInternalEdge (B : Finset V) :
    DecidableEq (G.InternalEdge B) := Classical.decEq _

instance instFintypeInternalEdge (B : Finset V) :
    Fintype (G.InternalEdge B) :=
  Fintype.ofFinset (G.edgesOn B).attach (by intro e; simp)

def endpoints {B : Finset V} (e : G.InternalEdge B) : Finset V :=
  {e.1.1, e.1.2}

def availableSlots {A B : Finset V} (e : G.InternalEdge B) : Finset (V × Nat) :=
  slotSet (G.capacity A) e.1.1 ∪ slotSet (G.capacity A) e.1.2

def endpointSet {B : Finset V} (H : Finset (G.InternalEdge B)) : Finset V :=
  H.biUnion (G.endpoints)

theorem endpointSet_subset {B : Finset V} (H : Finset (G.InternalEdge B)) :
    G.endpointSet H ⊆ B := by
  classical
  intro x hx
  rw [endpointSet, mem_biUnion] at hx
  rcases hx with ⟨e,he,hxe⟩
  have hEdge := e.2
  simp only [edgesOn, mem_filter] at hEdge
  simp only [endpoints, mem_insert, mem_singleton] at hxe
  rcases hxe with rfl | rfl
  · exact hEdge.2.1
  · exact hEdge.2.2

theorem edge_family_subset_edgesOn_endpointSet
    {B : Finset V} (H : Finset (G.InternalEdge B)) :
    H.image Subtype.val ⊆ G.edgesOn (G.endpointSet H) := by
  classical
  intro e he
  rw [mem_image] at he
  rcases he with ⟨ee,hee,rfl⟩
  have hE := ee.2
  simp only [edgesOn, mem_filter] at hE ⊢
  refine ⟨hE.1, ?_, ?_⟩
  · rw [endpointSet, mem_biUnion]
    exact ⟨ee,hee, by simp [endpoints]⟩
  · rw [endpointSet, mem_biUnion]
    exact ⟨ee,hee, by simp [endpoints]⟩

theorem card_edge_family_le_edgesOn_endpointSet
    {B : Finset V} (H : Finset (G.InternalEdge B)) :
    H.card ≤ (G.edgesOn (G.endpointSet H)).card := by
  classical
  have himg := card_le_card (G.edge_family_subset_edgesOn_endpointSet H)
  rw [card_image_of_injective _ Subtype.val_injective] at himg
  exact himg

theorem biUnion_availableSlots {A B : Finset V} (H : Finset (G.InternalEdge B)) :
    H.biUnion (G.availableSlots (A:=A)) =
      (G.endpointSet H).biUnion (slotSet (G.capacity A)) := by
  classical
  ext s
  constructor
  · intro hs
    rw [mem_biUnion] at hs
    rcases hs with ⟨e,he,hse⟩
    simp only [availableSlots, mem_union] at hse
    rw [mem_biUnion]
    rcases hse with hs1 | hs2
    · exact ⟨e.1.1, by rw [endpointSet, mem_biUnion]; exact ⟨e,he, by simp [endpoints]⟩, hs1⟩
    · exact ⟨e.1.2, by rw [endpointSet, mem_biUnion]; exact ⟨e,he, by simp [endpoints]⟩, hs2⟩
  · intro hs
    rw [mem_biUnion] at hs
    rcases hs with ⟨x,hx,hslot⟩
    rw [endpointSet, mem_biUnion] at hx
    rcases hx with ⟨e,he,hxe⟩
    rw [mem_biUnion]
    refine ⟨e,he,?_⟩
    simp only [endpoints, mem_insert, mem_singleton] at hxe
    simp only [availableSlots, mem_union]
    rcases hxe with rfl | rfl
    · exact Or.inl hslot
    · exact Or.inr hslot

theorem hall_condition_internal_edges {A C : Finset V} (hStrong : G.Strong A C) :
    HallCondition (fun e : G.InternalEdge (C \ A) => G.availableSlots (A:=A) e) := by
  classical
  intro H
  let X := G.endpointSet H
  have hXB : X ⊆ C \ A := G.endpointSet_subset H
  have h1 : H.card ≤ (G.edgesOn X).card := G.card_edge_family_le_edgesOn_endpointSet H
  have h2 : (G.edgesOn X).card ≤ ∑ x ∈ X, G.capacity A x :=
    G.relative_vertex_capacity hStrong hXB
  have hslots :
      (H.biUnion (fun e : G.InternalEdge (C \ A) => G.availableSlots (A:=A) e)).card =
      ∑ x ∈ X, G.capacity A x := by
    rw [G.biUnion_availableSlots H]
    exact card_slots_over (G.capacity A) X
  rw [hslots]
  exact h1.trans h2

structure TailAssignment (A B : Finset V) where
  tail : G.InternalEdge B → V
  endpoint : ∀ e, tail e = e.1.1 ∨ tail e = e.1.2
  capacity_ok : ∀ x,
    ((Finset.univ.filter fun e : G.InternalEdge B => tail e = x).card) ≤ G.capacity A x

theorem exists_tail_assignment {A C : Finset V} (hStrong : G.Strong A C) :
    Nonempty (G.TailAssignment A (C \ A)) := by
  classical
  let B := C \ A
  let avail : G.InternalEdge B → Finset (V × Nat) := fun e => G.availableSlots (A:=A) e
  have hHall : HallCondition avail := by
    dsimp [avail, B]
    exact G.hall_condition_internal_edges hStrong
  rcases (hall_marriage_theorem avail).2 hHall with ⟨f,hf⟩
  let tail : G.InternalEdge B → V := fun e => (f e).1
  have hendpoint : ∀ e, tail e = e.1.1 ∨ tail e = e.1.2 := by
    intro e
    have hm := hf.2 e
    simp only [avail, availableSlots, mem_union, slotSet, mem_product, mem_singleton, mem_range] at hm
    rcases hm with hm | hm
    · exact Or.inl hm.1
    · exact Or.inr hm.1
  have hcap : ∀ x,
      (Finset.univ.filter fun e : G.InternalEdge B => tail e = x).card ≤ G.capacity A x := by
    intro x
    let S : Finset (G.InternalEdge B) := Finset.univ.filter fun e => tail e = x
    have himg : (S.image f).card = S.card := by rw [card_image_of_injective _ hf.1]
    have hsub : S.image f ⊆ slotSet (G.capacity A) x := by
      intro s hs
      rw [mem_image] at hs
      rcases hs with ⟨e,he,rfl⟩
      have htailx : tail e = x := (mem_filter.mp he).2
      have htailx' : (f e).1 = x := by simpa [tail] using htailx
      have hm := hf.2 e
      simp only [avail, availableSlots, mem_union] at hm
      rcases hm with hm | hm
      · have hm' : (f e).1 = e.1.1 ∧ (f e).2 < G.capacity A e.1.1 := by simpa [slotSet] using hm
        have heqx : e.1.1 = x := hm'.1.symm.trans htailx'
        simp only [slotSet, mem_product, mem_singleton, mem_range]
        exact ⟨htailx', by simpa [heqx] using hm'.2⟩
      · have hm' : (f e).1 = e.1.2 ∧ (f e).2 < G.capacity A e.1.2 := by simpa [slotSet] using hm
        have heqx : e.1.2 = x := hm'.1.symm.trans htailx'
        simp only [slotSet, mem_product, mem_singleton, mem_range]
        exact ⟨htailx', by simpa [heqx] using hm'.2⟩
    have hc := card_le_card hsub
    rw [G.card_slotSet (G.capacity A) x, himg] at hc
    exact hc
  exact ⟨{ tail := tail, endpoint := hendpoint, capacity_ok := hcap }⟩

end FiniteGraph
end SparseBigRamsey.C0
