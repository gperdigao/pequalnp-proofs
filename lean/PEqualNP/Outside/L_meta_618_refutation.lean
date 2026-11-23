import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Outside.L_meta_614

-- Refutes the published existence statement in L-meta-618.
-- Uses the circuit lower bound from L-meta-614 by itay-raveh (pull request 728).

namespace PEqualNP.Outside.Prism618

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]

private def prismAdj (v w : Fin 6) : Prop :=
  (v.val, w.val) ∈ edgeList ∨ (w.val, v.val) ∈ edgeList

local instance : DecidableRel prismAdj := fun v w => by unfold prismAdj; infer_instance

private def prism : SimpleGraph (Fin 6) where
  Adj := prismAdj
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

local instance : DecidableRel prism.Adj := inferInstanceAs (DecidableRel prismAdj)

private theorem incident : ∀ v, ∃ w, prism.Adj v w := by decide

private theorem neighborhoods_different :
    ∀ v w, v ≠ w → ¬ prism.Adj v w → ∃ u, ¬ (prism.Adj v u ↔ prism.Adj w u) := by decide

private theorem adjacent_witness :
    ∀ v w, prism.Adj v w →
      ∃ a b, prism.Adj v a ∧ a ≠ w ∧ prism.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ prism.Adj a b) := by
  decide

private theorem degree_at_least_two (v : Fin 6) : 2 ≤ (prism.neighborSet v).ncard := by
  rw [← prism.coe_neighborFinset v, Set.ncard_coe_finset]
  have h : ∀ w : Fin 6, 2 ≤ (prism.neighborFinset w).card := by decide
  exact h v

private def IsCover (s : Finset (Fin 6)) : Prop :=
  ∀ v w, prism.Adj v w → v ∈ s ∨ w ∈ s

local instance (s : Finset (Fin 6)) : Decidable (IsCover s) := by
  unfold IsCover
  infer_instance

private def cover : Finset (Fin 6) := {1, 2, 3, 5}

private theorem cover_works : IsCover cover := by decide

private theorem cover_count : cover.card = 4 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem cover_minimal : ∀ s, IsCover s → 4 ≤ s.card := by decide

private theorem adjacency_equiv (x : Fin 6 → Bool) :
    (∃ u v : Fin 6, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true) ↔
      ∃ u v : Fin 6, prism.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, Or.inl huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    change prismAdj u v at huv
    rcases huv with huv | hvu
    · exact ⟨u, v, huv, hu, hv⟩
    · exact ⟨v, u, hvu, hv, hu⟩

theorem nonexistence :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
        (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
          (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, heval⟩
  have h := PEqualNP.Outside.L_meta_614 6 4 prism C incident
    (fun v w hvw hn _ _ => neighborhoods_different v w hvw hn)
    (fun v w ha _ _ => adjacent_witness v w ha)
    ⟨cover, fun v w h _ _ => cover_works v w h, cover_count⟩
    (fun s h => cover_minimal s fun v w hvw => h v w hvw (degree_at_least_two v) (degree_at_least_two w))
    hmono (fun x => (heval x).trans (adjacency_equiv x))
  omega

end PEqualNP.Outside.Prism618
