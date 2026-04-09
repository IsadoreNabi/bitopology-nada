/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Section 3: Extension of Nada's Construction to Directed Graphs

This file formalizes the theorems and propositions of Section 3 of the paper:
"Bitopological Spaces from Directed Graphs: Extending the Nada Construction
to Capture Temporal Irreversibility."
-/
import BitopologyNada.Bitopology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Set TopologicalSpace

/-! ## Theorem 3.1: Validity of the directed extension -/

namespace BitopologyNada

/-- **Theorem 3.1 (combined).** Both the forward and backward Nada topologies
are well-defined topological spaces, obtained by two applications of
`TopologicalSpace.generateFrom` to S⁺ and S⁻ respectively. -/
theorem nadaDirectedExtension_valid {V : Type*} (G : Digraph V) :
    ∃ (t₁ t₂ : TopologicalSpace V),
      t₁ = TopologicalSpace.generateFrom G.forwardSubbase ∧
      t₂ = TopologicalSpace.generateFrom G.backwardSubbase :=
  ⟨G.nadaForwardTopology, G.nadaBackwardTopology, rfl, rfl⟩

end BitopologyNada

/-! ## Proposition 3.2: Self-inclusion guarantees non-degeneracy -/

namespace Digraph

/-- **Proposition 3.2 (forward).** Every forward closed neighborhood is nonempty. -/
theorem forwardClosedNhd_nonempty {V : Type*} (G : Digraph V) (v : V) :
    (G.forwardClosedNhd v).Nonempty :=
  ⟨v, G.mem_forwardClosedNhd_self v⟩

/-- **Proposition 3.2 (backward).** Every backward closed neighborhood is nonempty. -/
theorem backwardClosedNhd_nonempty {V : Type*} (G : Digraph V) (v : V) :
    (G.backwardClosedNhd v).Nonempty :=
  ⟨v, G.mem_backwardClosedNhd_self v⟩

/-- For a source vertex (no in-edges), the backward open neighborhood is empty. -/
theorem openBackwardNhd_empty_of_source {V : Type*} (G : Digraph V) (v : V)
    (hsource : ∀ w, ¬G.Adj w v) :
    {w : V | G.Adj w v} = ∅ := by
  ext w; simp [hsource w]

/-- For a sink vertex (no out-edges), the forward open neighborhood is empty. -/
theorem openForwardNhd_empty_of_sink {V : Type*} (G : Digraph V) (v : V)
    (hsink : ∀ w, ¬G.Adj v w) :
    {w : V | G.Adj v w} = ∅ := by
  ext w; simp [hsink w]

/-- Every element of the forward subbase S⁺ is nonempty. -/
theorem forwardSubbase_nonempty {V : Type*} (G : Digraph V) :
    ∀ s ∈ G.forwardSubbase, s.Nonempty := by
  rintro s ⟨v, rfl⟩
  exact G.forwardClosedNhd_nonempty v

/-- Every element of the backward subbase S⁻ is nonempty. -/
theorem backwardSubbase_nonempty {V : Type*} (G : Digraph V) :
    ∀ s ∈ G.backwardSubbase, s.Nonempty := by
  rintro s ⟨v, rfl⟩
  exact G.backwardClosedNhd_nonempty v

end Digraph

/-! ## Theorem 3.3: Bitopological structure -/

namespace BitopologyNada

/-- **Theorem 3.3.** For any digraph G, the triple (V, τ⁺, τ⁻) is a
bitopological space. No symmetry hypothesis is required. -/
theorem nadaBitopology_directed {V : Type*} (G : Digraph V) :
    ∃ (B : Bitopology V),
      B.τ₁ = G.nadaForwardTopology ∧
      B.τ₂ = G.nadaBackwardTopology :=
  ⟨nadaBitopology G, rfl, rfl⟩

end BitopologyNada

/-! ## Theorem 3.4: Specialization preorder preserves connected components

The full proof requires substantial finite-space machinery (McCord 1966,
Stong 1966). We state the theorem precisely and provide the structural
outline, with sorry for the core step. -/

/-! ### Helper: `Specializes` preserves the connected component

We add a lemma in the global `Specializes` namespace so dot-notation
`h.connectedComponent_eq` works on any `h : x ⤳ y`. The proof uses
`Specializes.joinedIn` from Mathlib to produce a path between `x` and
`y`, then uses the standard fact that the continuous image of the
unit interval is preconnected and is therefore contained in the
connected component of `x`. -/

namespace Specializes

lemma connectedComponent_eq
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x ⤳ y) :
    connectedComponent x = connectedComponent y := by
  have hj : JoinedIn Set.univ x y :=
    h.joinedIn (Set.mem_univ _) (Set.mem_univ _)
  let γ := hj.somePath
  have hrange_pc : IsPreconnected (Set.range γ) :=
    isPreconnected_range γ.continuous_toFun
  have hx_mem : x ∈ Set.range γ := ⟨0, γ.source⟩
  have hy_mem : y ∈ Set.range γ := ⟨1, γ.target⟩
  have hy_in_cc : y ∈ connectedComponent x :=
    (hrange_pc.subset_connectedComponent hx_mem) hy_mem
  exact _root_.connectedComponent_eq hy_in_cc

end Specializes

namespace BitopologyNada

/-- Private helper: a disjunction of specializations still preserves the
connected component. Used in the inductive step of the chain theorem. -/
private lemma specializes_or_cc_eq
    {X : Type*} [TopologicalSpace X] {x y : X}
    (h : Specializes x y ∨ Specializes y x) :
    connectedComponent x = connectedComponent y := by
  rcases h with h | h
  · exact h.connectedComponent_eq
  · exact (h.connectedComponent_eq).symm

/-- Auxiliary form of the chain theorem: induction on the chain length
`k`, using a prefix chain obtained by dropping the last element. -/
private theorem sameComponent_chain_aux {V : Type*} (t : TopologicalSpace V) :
    ∀ (k : ℕ) (chain : Fin (k + 1) → V),
    (∀ (i : Fin k), @Specializes V t (chain i.castSucc) (chain i.succ) ∨
                    @Specializes V t (chain i.succ) (chain i.castSucc)) →
    @connectedComponent V t (chain ⟨0, Nat.zero_lt_succ k⟩) =
    @connectedComponent V t (chain (Fin.last k)) := by
  intro k
  induction k with
  | zero =>
    -- Fin 1 has a single element: ⟨0, _⟩ = Fin.last 0.
    intro _ _
    rfl
  | succ n ih =>
    intro chain hlinks
    -- Apply the IH to the prefix chain `fun i => chain i.castSucc`.
    have h_ih :
        @connectedComponent V t (chain ⟨0, Nat.zero_lt_succ (n + 1)⟩) =
        @connectedComponent V t (chain (Fin.last n).castSucc) := by
      have := ih (fun i => chain i.castSucc) (by
        intro i
        exact hlinks i.castSucc)
      exact this
    -- The final link: from chain (Fin.last n).castSucc to chain (Fin.last (n+1)).
    have h_last := hlinks (Fin.last n)
    have h_step :
        @connectedComponent V t (chain (Fin.last n).castSucc) =
        @connectedComponent V t (chain (Fin.last (n + 1))) := by
      -- `(Fin.last n).succ = Fin.last (n+1)` definitionally.
      have heq : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [← heq]
      exact specializes_or_cc_eq h_last
    exact h_ih.trans h_step

/-- **Theorem 3.4 (easy direction).** If two points are linked by a chain
of specialization-comparable points, they lie in the same connected
component. Proved by reduction to `sameComponent_chain_aux`. -/
theorem sameComponent_of_specialization_chain
    {V : Type*} (t : TopologicalSpace V) (x y : V)
    (h : ∃ (k : ℕ) (chain : Fin (k + 1) → V),
      chain ⟨0, Nat.zero_lt_succ k⟩ = x ∧
      chain (Fin.last k) = y ∧
      ∀ (i : Fin k), @Specializes V t (chain i.castSucc) (chain i.succ) ∨
                      @Specializes V t (chain i.succ) (chain i.castSucc)) :
    @connectedComponent V t x = @connectedComponent V t y := by
  obtain ⟨k, chain, hx, hy, hlinks⟩ := h
  rw [← hx, ← hy]
  exact sameComponent_chain_aux t k chain hlinks

/-- **Axiom (McCord–Stong, finite-space form).** In any finite topological
space, if two points lie in the same connected component, then they are
linked by a chain of specialization-comparable points.

This is the hard direction of the finite-space McCord–Stong theorem (McCord
1966, Stong 1966). It is not yet formalized in `mathlib4` and is declared
here as a named axiom so that its use is fully explicit in any downstream
theorem via `#print axioms`. -/
axiom specialization_chain_of_sameComponent
    {V : Type*} [Finite V] (t : TopologicalSpace V) (x y : V)
    (h : @connectedComponent V t x = @connectedComponent V t y) :
    ∃ (k : ℕ) (chain : Fin (k + 1) → V),
      chain ⟨0, Nat.zero_lt_succ k⟩ = x ∧
      chain (Fin.last k) = y ∧
      ∀ (i : Fin k), @Specializes V t (chain i.castSucc) (chain i.succ) ∨
                      @Specializes V t (chain i.succ) (chain i.castSucc)

/-- **Theorem 3.4 (combined).** In a finite topological space, two points
are in the same connected component iff they are linked by a chain of
specialization-comparable points. The forward direction uses the axiom
`specialization_chain_of_sameComponent` (McCord–Stong finite-space form).
The reverse direction is proved directly. -/
theorem specialization_chain_iff_connectedComponent
    {V : Type*} [Finite V] (t : TopologicalSpace V) (x y : V) :
    @connectedComponent V t x = @connectedComponent V t y ↔
    ∃ (k : ℕ) (chain : Fin (k + 1) → V),
      chain ⟨0, Nat.zero_lt_succ k⟩ = x ∧
      chain (Fin.last k) = y ∧
      ∀ (i : Fin k), @Specializes V t (chain i.castSucc) (chain i.succ) ∨
                      @Specializes V t (chain i.succ) (chain i.castSucc) :=
  ⟨fun h => specialization_chain_of_sameComponent t x y h,
   fun h => sameComponent_of_specialization_chain t x y h⟩

end BitopologyNada

/-! ## Theorem 3.5: Alexandrov topology as subtopology of the directed Nada topology -/

namespace Digraph

/-- The reflexive-transitive closure of a digraph's adjacency relation. -/
@[reducible]
def reachabilityPreorder {V : Type*} (G : Digraph V) : Preorder V where
  le := Relation.ReflTransGen G.Adj
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- The Alexandrov topology on V induced by the reachability preorder of a DAG:
open sets are exactly the upsets of the reflexive-transitive closure of E. -/
@[reducible]
def alexandrovTopology {V : Type*} (G : Digraph V) : TopologicalSpace V :=
  @Topology.upperSet V G.reachabilityPreorder

end Digraph

namespace BitopologyNada

open Digraph

/-- **Theorem 3.5.** For any digraph G, every upset of the reachability preorder
R* is open in the forward Nada topology. That is, τ_A ⊆ τ⁺_Nada as families
of open sets.

Proof: For each upset U and each v ∈ U, the subbase element N⁺[v] satisfies
v ∈ N⁺[v] ⊆ U. Hence U = ⋃_{v ∈ U} N⁺[v] is open in τ⁺. -/
theorem upset_isOpen_nadaForward {V : Type*} (G : Digraph V) (s : Set V)
    (hup : ∀ ⦃a b : V⦄, Relation.ReflTransGen G.Adj a b → a ∈ s → b ∈ s) :
    @IsOpen V G.nadaForwardTopology s := by
  -- Show s = ⋃_{v ∈ s} N⁺[v], each a subbase element.
  have nhd_sub : ∀ v ∈ s, G.forwardClosedNhd v ⊆ s := by
    intro v hv w hw_nhd
    simp only [Digraph.forwardClosedNhd, mem_union, mem_singleton_iff, mem_setOf_eq] at hw_nhd
    rcases hw_nhd with rfl | hadj
    · exact hv
    · exact hup (Relation.ReflTransGen.single hadj) hv
  have heq : s = ⋃₀ {t | ∃ v ∈ s, t = G.forwardClosedNhd v} := by
    ext w
    simp only [mem_sUnion, mem_setOf_eq]
    constructor
    · intro hw
      exact ⟨G.forwardClosedNhd w, ⟨w, hw, rfl⟩, G.mem_forwardClosedNhd_self w⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, hw_nhd⟩
      exact nhd_sub v hv hw_nhd
  rw [heq]
  apply GenerateOpen.sUnion
  rintro t ⟨v, _, rfl⟩
  exact GenerateOpen.basic _ ⟨v, rfl⟩

/-- **Theorem 3.5 (topology ordering form).** τ⁺_Nada refines τ_A.
In Mathlib's ordering on TopologicalSpace (reverse inclusion of open sets),
nadaForwardTopology ≤ alexandrovTopology. -/
theorem alexandrov_le_nadaForward {V : Type*} (G : Digraph V) :
    G.nadaForwardTopology ≤ G.alexandrovTopology := by
  intro s hs
  exact upset_isOpen_nadaForward G s hs

/-! ## Corollary 3.6: Resolution hierarchy -/

/-- **Corollary 3.6.** If the Alexandrov topology τ_A is connected (as a
topological space on all of V) and S is a nontrivial clopen in τ⁺_Nada,
then S is NOT clopen in τ_A.

Proof by contradiction: if S were clopen in τ_A, it would disconnect τ_A
(since S is nonempty and proper), contradicting the hypothesis. -/
theorem resolution_hierarchy {V : Type*} (G : Digraph V)
    (hconn_A : @IsPreconnected V G.alexandrovTopology Set.univ)
    (S : Set V)
    (hS_clopen_nada : @IsClopen V G.nadaForwardTopology S)
    (hS_ne : S.Nonempty)
    (hS_ne_univ : S ≠ Set.univ) :
    ¬(@IsClopen V G.alexandrovTopology S) := by
  intro ⟨hS_closed_A, hS_open_A⟩
  -- S is a nontrivial clopen in τ_A, so τ_A is disconnected.
  have hSc_open_A : @IsOpen V G.alexandrovTopology Sᶜ := hS_closed_A.isOpen_compl
  have hSc_ne : Sᶜ.Nonempty := by rwa [nonempty_compl]
  have hcover : Set.univ ⊆ S ∪ Sᶜ := by simp
  have hU_inter : (Set.univ ∩ S).Nonempty :=
    ⟨hS_ne.some, mem_univ _, hS_ne.some_mem⟩
  have hV_inter : (Set.univ ∩ Sᶜ).Nonempty :=
    ⟨hSc_ne.some, mem_univ _, hSc_ne.some_mem⟩
  have := hconn_A S Sᶜ hS_open_A hSc_open_A hcover hU_inter hV_inter
  obtain ⟨x, ⟨_, ⟨hxS, hxSc⟩⟩⟩ := this
  exact hxSc hxS

/-! ## Proposition 3.7: Irreversibility indices -/

/-- The asymmetry direction Δ(τ⁺, τ⁻) = C⁻ - C⁺ (signed). -/
def asymmetryDirection (c_plus c_minus : ℕ) : ℤ :=
  (c_minus : ℤ) - (c_plus : ℤ)

/-- **Proposition 3.7.** Δ > 0 iff C⁺ < C⁻. -/
theorem asymmetryDirection_pos_iff (c_plus c_minus : ℕ) :
    0 < asymmetryDirection c_plus c_minus ↔ c_plus < c_minus := by
  unfold asymmetryDirection
  omega

/-- Δ = 0 iff C⁺ = C⁻. -/
theorem asymmetryDirection_zero_iff (c_plus c_minus : ℕ) :
    asymmetryDirection c_plus c_minus = 0 ↔ c_plus = c_minus := by
  unfold asymmetryDirection
  omega

/-! ### Rational-valued irreversibility indices I_C and I_B

**Proposition 3.7 (continued).**  The component-count irreversibility index
`I_C = |C⁺ − C⁻| / max(C⁺, C⁻)` and the base-size irreversibility index
`I_B = |B⁺ − B⁻| / max(B⁺, B⁻)` both lie in [0, 1] and equal 0 iff the
two counts coincide.

We define a generic helper `normalizedDiff` over `ℕ → ℕ → ℚ` and instantiate
it for the two indices.
-/

/-- Generic normalized difference `|a − b| / max(a, b)` over natural numbers,
cast into the rationals. Returns `0` when `a = b = 0`. -/
def normalizedDiff (a b : ℕ) : ℚ :=
  if max a b = 0 then 0
  else |(a : ℚ) - (b : ℚ)| / (max a b : ℚ)

/-- Component-count irreversibility index: `I_C(C⁺, C⁻) = |C⁺ − C⁻| / max(C⁺, C⁻)`. -/
def irreversibilityComponents (a b : ℕ) : ℚ := normalizedDiff a b

/-- Base-size irreversibility index: `I_B(B⁺, B⁻) = |B⁺ − B⁻| / max(B⁺, B⁻)`. -/
def irreversibilityBase (a b : ℕ) : ℚ := normalizedDiff a b

/-! #### Lemmas about `normalizedDiff` -/

private theorem max_pos_of_ne_zero {a b : ℕ} (h : ¬max a b = 0) :
    (0 : ℚ) < max (a : ℚ) (b : ℚ) := by
  have hpos : 0 < max a b := Nat.pos_of_ne_zero h
  have hcast : (0 : ℚ) < ((max a b : ℕ) : ℚ) := by exact_mod_cast hpos
  rwa [Nat.cast_max] at hcast

theorem normalizedDiff_nonneg (a b : ℕ) : 0 ≤ normalizedDiff a b := by
  unfold normalizedDiff
  split
  · exact le_refl 0
  · next h =>
    apply div_nonneg
    · exact abs_nonneg _
    · exact le_of_lt (max_pos_of_ne_zero h)

theorem normalizedDiff_le_one (a b : ℕ) : normalizedDiff a b ≤ 1 := by
  unfold normalizedDiff
  split
  · exact zero_le_one
  · next h =>
    have hmax : (0 : ℚ) < max (a : ℚ) (b : ℚ) := max_pos_of_ne_zero h
    have habs : |(a : ℚ) - (b : ℚ)| ≤ max (a : ℚ) (b : ℚ) := by
      rcases le_total (a : ℚ) (b : ℚ) with hab | hab
      · rw [abs_of_nonpos (sub_nonpos.mpr hab), max_eq_right hab]
        linarith [Nat.cast_nonneg (α := ℚ) a]
      · rw [abs_of_nonneg (sub_nonneg.mpr hab), max_eq_left hab]
        linarith [Nat.cast_nonneg (α := ℚ) b]
    rw [div_le_one₀ hmax]
    exact habs

theorem normalizedDiff_eq_zero_iff (a b : ℕ) : normalizedDiff a b = 0 ↔ a = b := by
  unfold normalizedDiff
  constructor
  · intro h
    split at h
    · next h0 =>
      have ha : a ≤ max a b := le_max_left a b
      have hb : b ≤ max a b := le_max_right a b
      omega
    · next hne =>
      have hpos := max_pos_of_ne_zero hne
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have := h
        rw [abs_eq_zero, sub_eq_zero] at this
        exact_mod_cast this
      · linarith
  · intro h
    subst h
    split
    · rfl
    · simp [sub_self, abs_zero, zero_div]

/-! #### Lemmas for `irreversibilityComponents` -/

theorem irreversibilityComponents_nonneg (a b : ℕ) :
    0 ≤ irreversibilityComponents a b :=
  normalizedDiff_nonneg a b

theorem irreversibilityComponents_le_one (a b : ℕ) :
    irreversibilityComponents a b ≤ 1 :=
  normalizedDiff_le_one a b

theorem irreversibilityComponents_eq_zero_iff (a b : ℕ) :
    irreversibilityComponents a b = 0 ↔ a = b :=
  normalizedDiff_eq_zero_iff a b

/-! #### Lemmas for `irreversibilityBase` -/

theorem irreversibilityBase_nonneg (a b : ℕ) :
    0 ≤ irreversibilityBase a b :=
  normalizedDiff_nonneg a b

theorem irreversibilityBase_le_one (a b : ℕ) :
    irreversibilityBase a b ≤ 1 :=
  normalizedDiff_le_one a b

theorem irreversibilityBase_eq_zero_iff (a b : ℕ) :
    irreversibilityBase a b = 0 ↔ a = b :=
  normalizedDiff_eq_zero_iff a b

/-! ## Proposition 3.8: Characterization of pairwise connectedness -/

/-- A bitopological space is **pairwise disconnected** if there exist nonempty
sets U ∈ τ₁ and W ∈ τ₂ that partition V. -/
def Bitopology.IsPairwiseDisconnected {X : Type*} (B : Bitopology X) : Prop :=
  ∃ (U W : Set X),
    B.τ₁.IsOpen U ∧ B.τ₂.IsOpen W ∧
    U.Nonempty ∧ W.Nonempty ∧
    U ∪ W = Set.univ ∧ Disjoint U W

/-- A bitopological space is **pairwise connected** iff it is not pairwise
disconnected. -/
def Bitopology.IsPairwiseConnected {X : Type*} (B : Bitopology X) : Prop :=
  ¬B.IsPairwiseDisconnected

/-- **Proposition 3.8 (first formulation).** Pairwise connected iff there is no
proper nonempty subset A that is simultaneously τ₁-open and τ₂-closed. -/
theorem pairwiseConnected_iff_no_open_closed {X : Type*} (B : Bitopology X) :
    B.IsPairwiseConnected ↔
    ∀ (A : Set X), B.τ₁.IsOpen A → A.Nonempty → A ≠ Set.univ → ¬B.τ₂.IsOpen Aᶜ := by
  unfold Bitopology.IsPairwiseConnected Bitopology.IsPairwiseDisconnected
  constructor
  · -- If pairwise connected, then no such A exists.
    intro hpc A hA_open hA_ne hA_ne_univ hAc_open
    apply hpc
    refine ⟨A, Aᶜ, hA_open, hAc_open, hA_ne, ?_, union_compl_self A, disjoint_compl_right⟩
    rwa [nonempty_compl]
  · -- If no such A exists, then pairwise connected.
    intro hno ⟨U, W, hU_open, hW_open, hU_ne, hW_ne, hcover, hdisj⟩
    -- W = Uᶜ since U ∪ W = univ and U ∩ W = ∅
    have hW_eq : W = Uᶜ := by
      ext x
      constructor
      · intro hx
        exact fun hxU => (hdisj.ne_of_mem hxU hx) rfl
      · intro hx
        have hxUW : x ∈ U ∪ W := by rw [hcover]; exact mem_univ x
        exact hxUW.elim (fun h => absurd h hx) id
    have hU_ne_univ : U ≠ Set.univ := by
      intro heq
      rw [heq, compl_univ] at hW_eq
      rw [hW_eq] at hW_ne
      exact not_nonempty_empty hW_ne
    exact hno U hU_open hU_ne hU_ne_univ (hW_eq ▸ hW_open)

end BitopologyNada
