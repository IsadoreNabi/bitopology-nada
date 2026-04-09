/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Bitopological Spaces and the Directed Nada Construction

This file defines bitopological spaces (Kelly, 1963) and proves the central theorem:
the directed Nada construction on any digraph produces a bitopological space.
-/
import BitopologyNada.Directed

namespace BitopologyNada

open Set TopologicalSpace

/-! ## Bitopological spaces -/

/-- A **bitopological space** is a type equipped with two topological space structures.

This is the definition of Kelly (1963): a triple `(X, τ₁, τ₂)` where `τ₁` and `τ₂`
are both topologies on `X`. We bundle this as a structure carrying two
`TopologicalSpace` instances. -/
structure Bitopology (X : Type*) where
  /-- The first topology. -/
  τ₁ : TopologicalSpace X
  /-- The second topology. -/
  τ₂ : TopologicalSpace X

/-- Constructor for a `Bitopology` from two `TopologicalSpace` instances. -/
def Bitopology.mk' {X : Type*} (t₁ t₂ : TopologicalSpace X) : Bitopology X :=
  ⟨t₁, t₂⟩

/-! ## The central theorem -/

/-- **Directed Nada Construction (Central Theorem).**

Let `G` be any directed graph on a type `V`. Then the forward Nada topology `τ⁺`
and the backward Nada topology `τ⁻` are both topologies on `V`, and the triple
`(V, τ⁺, τ⁻)` is a bitopological space.

No symmetry hypothesis on `G` is needed: the Nada procedure depends only on
`TopologicalSpace.generateFrom`, which produces a valid topology from *any*
family of subsets. The proof is therefore structurally trivial — it reduces to
two applications of `generateFrom`, each of which satisfies the topology axioms
by construction (closure under finite intersections and arbitrary unions).

This structural triviality is exactly the point: the universality of the topology
axioms makes the extension from undirected to directed graphs automatic. -/
def nadaBitopology {V : Type*} (G : Digraph V) : Bitopology V :=
  ⟨G.nadaForwardTopology, G.nadaBackwardTopology⟩

/-- The forward topology component of the Nada bitopology is `generateFrom` applied
to the forward subbase. -/
theorem nadaBitopology_τ₁ {V : Type*} (G : Digraph V) :
    (nadaBitopology G).τ₁ = TopologicalSpace.generateFrom G.forwardSubbase :=
  rfl

/-- The backward topology component of the Nada bitopology is `generateFrom` applied
to the backward subbase. -/
theorem nadaBitopology_τ₂ {V : Type*} (G : Digraph V) :
    (nadaBitopology G).τ₂ = TopologicalSpace.generateFrom G.backwardSubbase :=
  rfl

/-- The central theorem, stated as a proposition: the two Nada topologies on a digraph
are both valid topological spaces, and their combination is a bitopological space.

Since `TopologicalSpace.generateFrom` returns a term of type `TopologicalSpace V`
(which is by definition a valid topology), the proof is `⟨_, _⟩` — there is literally
nothing to check beyond the fact that `generateFrom` was applied twice. -/
theorem nadaForwardBackwardIsBitopology
    {V : Type*} (G : Digraph V) :
    ∃ (B : Bitopology V),
      B.τ₁ = G.nadaForwardTopology ∧
      B.τ₂ = G.nadaBackwardTopology :=
  ⟨nadaBitopology G, rfl, rfl⟩

/-- Alternate statement: the Nada forward and backward topologies are well-defined
topological spaces. This is even more directly trivial — `generateFrom` always
produces a `TopologicalSpace`. -/
example {V : Type*} (G : Digraph V) : TopologicalSpace V := G.nadaForwardTopology
example {V : Type*} (G : Digraph V) : TopologicalSpace V := G.nadaBackwardTopology

/-! ## Pairwise separation -/

/-- A set is **pairwise open** in a bitopological space if it is open in either topology. -/
def Bitopology.IsPairwiseOpen {X : Type*} (B : Bitopology X) (s : Set X) : Prop :=
  B.τ₁.IsOpen s ∨ B.τ₂.IsOpen s

/-- A set is **pairwise closed** in a bitopological space if its complement is open in
either topology. -/
def Bitopology.IsPairwiseClosed {X : Type*} (B : Bitopology X) (s : Set X) : Prop :=
  B.τ₁.IsOpen sᶜ ∨ B.τ₂.IsOpen sᶜ

/-- A bitopological space is **pairwise Hausdorff** if for every pair of distinct points,
one can be separated from the other by an open set in `τ₁` and the other by an open
set in `τ₂` (the pairwise T₂ axiom of Kelly). -/
def Bitopology.IsPairwiseHausdorff {X : Type*} (B : Bitopology X) : Prop :=
  ∀ x y : X, x ≠ y →
    ∃ (U W : Set X),
      B.τ₁.IsOpen U ∧ B.τ₂.IsOpen W ∧
      x ∈ U ∧ y ∈ W ∧ Disjoint U W

/-- For a symmetric digraph, the Nada bitopology has equal components. -/
theorem nadaBitopology_symmetric {V : Type*}
    (G : Digraph V) (hsymm : ∀ v w, G.Adj v w → G.Adj w v) :
    (nadaBitopology G).τ₁ = (nadaBitopology G).τ₂ := by
  show G.nadaForwardTopology = G.nadaBackwardTopology
  unfold Digraph.nadaForwardTopology Digraph.nadaBackwardTopology
  congr 1
  unfold Digraph.forwardSubbase Digraph.backwardSubbase
  ext s
  simp only [Set.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv ▸ (G.forwardClosedNhd_eq_backwardClosedNhd_of_symmetric hsymm v).symm⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, hv ▸ G.forwardClosedNhd_eq_backwardClosedNhd_of_symmetric hsymm v⟩

end BitopologyNada
