import Mathlib

/-!
# Concrete finite graph layer for the `C₀` audit

This file removes the abstract edge-count hypotheses from the previous audit.
A finite simple graph is represented by a finite set of ordered endpoint pairs
`(u,v)` with `u<v`.  This is equivalent to a finite simple graph after choosing
a linear order on the ambient vertex type, and it makes the counting layer
transparent.

No predimension identity is assumed.
-/

namespace SparseBigRamsey.C0

open Finset

variable {V : Type*} [LinearOrder V]

structure FiniteGraph (V : Type*) [LinearOrder V] where
  edges : Finset (V × V)
  ordered : ∀ e ∈ edges, e.1 < e.2

namespace FiniteGraph

variable (G : FiniteGraph V)

def edgesOn (X : Finset V) : Finset (V × V) :=
  G.edges.filter (fun e => e.1 ∈ X ∧ e.2 ∈ X)

def crossEdges (A X : Finset V) : Finset (V × V) :=
  G.edges.filter (fun e =>
    (e.1 ∈ A ∧ e.2 ∈ X) ∨ (e.1 ∈ X ∧ e.2 ∈ A))

def predim (X : Finset V) : Int :=
  2 * (X.card : Int) - ((G.edgesOn X).card : Int)

def Strong (A C : Finset V) : Prop :=
  A ⊆ C ∧
  ∀ X : Finset V, A ⊆ X → X ⊆ C → G.predim A ≤ G.predim X

def downDegree (A : Finset V) (x : V) : Nat :=
  (G.crossEdges A {x}).card

def capacity (A : Finset V) (x : V) : Nat :=
  2 - G.downDegree A x

theorem edgesOn_singleton (x : V) :
    G.edgesOn {x} = ∅ := by
  classical
  ext e
  rcases e with ⟨u,v⟩
  constructor
  · intro he
    simp only [edgesOn, mem_filter, mem_singleton] at he
    rcases he with ⟨hE, rfl, rfl⟩
    exact (lt_irrefl x (G.ordered (x,x) hE)).elim
  · simp

theorem edgesOn_union_partition
    (A X : Finset V) (hAX : Disjoint A X) :
    G.edgesOn (A ∪ X) =
      (G.edgesOn A ∪ G.edgesOn X) ∪ G.crossEdges A X := by
  classical
  ext e
  rcases e with ⟨u,v⟩
  have hd : ∀ {z : V}, z ∈ A → z ∈ X → False := by
    intro z hzA hzX
    exact Finset.disjoint_left.mp hAX hzA hzX
  simp only [edgesOn, crossEdges, mem_filter, mem_union, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hE, (huA | huX), (hvA | hvX)⟩
    · exact Or.inl (Or.inl ⟨hE, huA, hvA⟩)
    · exact Or.inr ⟨hE, Or.inl ⟨huA, hvX⟩⟩
    · exact Or.inr ⟨hE, Or.inr ⟨huX, hvA⟩⟩
    · exact Or.inl (Or.inr ⟨hE, huX, hvX⟩)
  · rintro ((⟨hE,huA,hvA⟩ | ⟨hE,huX,hvX⟩) |
      ⟨hE, (⟨huA,hvX⟩ | ⟨huX,hvA⟩)⟩)
    · exact ⟨hE, Or.inl huA, Or.inl hvA⟩
    · exact ⟨hE, Or.inr huX, Or.inr hvX⟩
    · exact ⟨hE, Or.inl huA, Or.inr hvX⟩
    · exact ⟨hE, Or.inr huX, Or.inl hvA⟩

theorem disjoint_edgesOn
    (A X : Finset V) (hAX : Disjoint A X) :
    Disjoint (G.edgesOn A) (G.edgesOn X) := by
  classical
  rw [Finset.disjoint_left]
  intro e heA heX
  rcases e with ⟨u,v⟩
  simp only [edgesOn, mem_filter, Prod.fst, Prod.snd] at heA heX
  exact Finset.disjoint_left.mp hAX heA.2.1 heX.2.1

theorem disjoint_oldnew_cross
    (A X : Finset V) (hAX : Disjoint A X) :
    Disjoint (G.edgesOn A ∪ G.edgesOn X) (G.crossEdges A X) := by
  classical
  rw [Finset.disjoint_left]
  intro e hleft hcross
  rcases e with ⟨u,v⟩
  simp only [edgesOn, crossEdges, mem_union, mem_filter, Prod.fst, Prod.snd] at hleft hcross
  have hd : ∀ {z : V}, z ∈ A → z ∈ X → False := by
    intro z hzA hzX
    exact Finset.disjoint_left.mp hAX hzA hzX
  rcases hleft with hAA | hXX
  · rcases hcross.2 with hAX' | hXA'
    · exact hd hAA.2.2 hAX'.2
    · exact hd hAA.2.1 hXA'.1
  · rcases hcross.2 with hAX' | hXA'
    · exact hd hAX'.1 hXX.2.1
    · exact hd hXA'.2 hXX.2.2

theorem card_edgesOn_union
    (A X : Finset V) (hAX : Disjoint A X) :
    (G.edgesOn (A ∪ X)).card =
      (G.edgesOn A).card + (G.edgesOn X).card + (G.crossEdges A X).card := by
  classical
  rw [G.edgesOn_union_partition A X hAX]
  rw [Finset.card_union_of_disjoint (G.disjoint_oldnew_cross A X hAX)]
  rw [Finset.card_union_of_disjoint (G.disjoint_edgesOn A X hAX)]

theorem predim_union_increment
    (A X : Finset V) (hAX : Disjoint A X) :
    G.predim (A ∪ X) - G.predim A =
      2 * (X.card : Int) -
      ((G.edgesOn X).card : Int) -
      ((G.crossEdges A X).card : Int) := by
  classical
  have hv := Finset.card_union_of_disjoint hAX
  have he := G.card_edgesOn_union A X hAX
  simp only [predim]
  omega

theorem cross_union_singletons
    (A X : Finset V) (hAX : Disjoint A X) :
    G.crossEdges A X =
      X.biUnion (fun x => G.crossEdges A {x}) := by
  classical
  ext e
  rcases e with ⟨u,v⟩
  have hd : ∀ {z : V}, z ∈ A → z ∈ X → False := by
    intro z hzA hzX
    exact Finset.disjoint_left.mp hAX hzA hzX
  simp only [crossEdges, mem_filter, mem_biUnion, mem_singleton,
    Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hE, h⟩
    rcases h with ⟨huA,hvX⟩ | ⟨huX,hvA⟩
    · exact ⟨v, hvX, hE, Or.inl ⟨huA, rfl⟩⟩
    · exact ⟨u, huX, hE, Or.inr ⟨rfl, hvA⟩⟩
  · rintro ⟨x,hxX,hE,h⟩
    rcases h with ⟨huA,hvx⟩ | ⟨hux,hvA⟩
    · subst x
      exact ⟨hE, Or.inl ⟨huA,hxX⟩⟩
    · subst x
      exact ⟨hE, Or.inr ⟨hxX,hvA⟩⟩

theorem pairwiseDisjoint_cross_singletons
    (A X : Finset V) (hAX : Disjoint A X) :
    (X : Set V).PairwiseDisjoint (fun x => G.crossEdges A {x}) := by
  classical
  intro x hx y hy hxy
  rw [Finset.disjoint_left]
  intro e hex hey
  rcases e with ⟨u,v⟩
  simp only [crossEdges, mem_filter, mem_singleton, Prod.fst, Prod.snd] at hex hey
  have hd : ∀ {z : V}, z ∈ A → z ∈ X → False := by
    intro z hzA hzX
    exact Finset.disjoint_left.mp hAX hzA hzX
  rcases hex.2 with ⟨huA,hvx⟩ | ⟨hux,hvA⟩
  · rcases hey.2 with ⟨huA',hvy⟩ | ⟨huy,hvA'⟩
    · exact hxy (hvx.symm.trans hvy)
    · exact hd hvA' (by simpa [hvx] using hx)
  · rcases hey.2 with ⟨huA',hvy⟩ | ⟨huy,hvA'⟩
    · exact hd huA' (by simpa [hux] using hx)
    · exact hxy (hux.symm.trans huy)

theorem cross_card_eq_sum_downDegree
    (A X : Finset V) (hAX : Disjoint A X) :
    (G.crossEdges A X).card =
      ∑ x ∈ X, G.downDegree A x := by
  classical
  rw [G.cross_union_singletons A X hAX]
  rw [Finset.card_biUnion (G.pairwiseDisjoint_cross_singletons A X hAX)]
  rfl

theorem strong_total_capacity_bound
    {A C X : Finset V}
    (hStrong : G.Strong A C)
    (hXB : X ⊆ C \ A) :
    (G.edgesOn X).card + (G.crossEdges A X).card ≤ 2 * X.card := by
  classical
  have hAX : Disjoint A X := by
    rw [Finset.disjoint_left]
    intro a haA haX
    have := hXB haX
    exact this.2 haA
  have hAC : A ⊆ C := hStrong.1
  have hAuX_C : A ∪ X ⊆ C := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzA | hzX
    · exact hAC hzA
    · exact (hXB hzX).1
  have hδ := hStrong.2 (A ∪ X) Finset.subset_union_left hAuX_C
  have hinc := G.predim_union_increment A X hAX
  omega

theorem downDegree_le_two
    {A C : Finset V} (hStrong : G.Strong A C)
    {x : V} (hx : x ∈ C \ A) :
    G.downDegree A x ≤ 2 := by
  classical
  have h := G.strong_total_capacity_bound hStrong (X := {x}) (by
    intro y hy
    simp only [mem_singleton] at hy
    subst y
    exact hx)
  rw [G.edgesOn_singleton x] at h
  simp at h
  omega


theorem one_point_strong_of_downDegree_eq_two
    {A C : Finset V}
    (hStrong : G.Strong A C)
    {x : V} (hx : x ∈ C \ A)
    (hdeg : G.downDegree A x = 2) :
    G.Strong (insert x A) C := by
  classical
  have hAX : Disjoint A ({x} : Finset V) := by
    rw [Finset.disjoint_left]
    intro a haA hax
    simp only [mem_singleton] at hax
    subst a
    exact hx.2 haA
  have hpred :
      G.predim (insert x A) = G.predim A := by
    have hinc := G.predim_union_increment A {x} hAX
    rw [G.edgesOn_singleton x] at hinc
    have hcross : (G.crossEdges A {x}).card = 2 := hdeg
    simp only [card_empty, Nat.cast_zero, sub_zero, card_singleton, Nat.cast_one] at hinc
    have hUA : A ∪ {x} = insert x A := by
      ext y
      simp [or_comm]
    rw [hUA] at hinc
    omega
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases mem_insert.mp hy with rfl | hyA
    · exact hx.1
    · exact hStrong.1 hyA
  · intro Y hAxY hYC
    have hAY : A ⊆ Y := by
      intro a ha
      exact hAxY (mem_insert_of_mem ha)
    have hbase := hStrong.2 Y hAY hYC
    rw [hpred]
    exact hbase

theorem sum_capacity_plus_cross
    {A C X : Finset V}
    (hStrong : G.Strong A C)
    (hXB : X ⊆ C \ A) :
    (∑ x ∈ X, G.capacity A x) + (G.crossEdges A X).card = 2 * X.card := by
  classical
  have hAX : Disjoint A X := by
    rw [Finset.disjoint_left]
    intro a haA haX
    exact (hXB haX).2 haA
  have hsumdeg := G.cross_card_eq_sum_downDegree A X hAX
  have hpoint : ∀ x ∈ X, G.capacity A x + G.downDegree A x = 2 := by
    intro x hx
    have hd := G.downDegree_le_two hStrong (hXB hx)
    simp only [capacity]
    omega
  have hsum :
      (∑ x ∈ X, G.capacity A x) +
      (∑ x ∈ X, G.downDegree A x) = 2 * X.card := by
    calc
      (∑ x ∈ X, G.capacity A x) +
          (∑ x ∈ X, G.downDegree A x)
          = ∑ x ∈ X, (G.capacity A x + G.downDegree A x) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ X, 2 := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hpoint x hx
      _ = 2 * X.card := by simp [Nat.mul_comm]
  omega

theorem relative_vertex_capacity
    {A C X : Finset V}
    (hStrong : G.Strong A C)
    (hXB : X ⊆ C \ A) :
    (G.edgesOn X).card ≤ ∑ x ∈ X, G.capacity A x := by
  have htot := G.strong_total_capacity_bound hStrong hXB
  have hsum := G.sum_capacity_plus_cross hStrong hXB
  omega

end FiniteGraph
end SparseBigRamsey.C0
