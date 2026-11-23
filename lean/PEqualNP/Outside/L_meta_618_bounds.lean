import PEqualNP.Outside.L_meta_618_refutation
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.Prism618

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit where
  gates :=
    [⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩,
     ⟨.or, [3, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [8, 12]⟩,
     ⟨.or, [7, 13]⟩, ⟨.or, [11, 14]⟩]
  output := 15

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem ten_gate_upper_bound :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 10 ∧
      (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
        (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
          (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  refine ⟨circuit, ?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide

end PEqualNP.Outside.Prism618

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_618_bounds :
    let detectsEdge (C : Circuit) :=
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
        (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
          (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true
    (∀ C : Circuit, Monotone2 C → detectsEdge C → 9 ≤ C.size) ∧
      (∃ C : Circuit, Monotone2 C ∧ C.size = 10 ∧ detectsEdge C) := by
  dsimp only
  constructor
  · intro C hmono hdetect
    by_contra! hsize
    exact PEqualNP.Outside.Prism618.nonexistence ⟨C, hmono, by omega, hdetect⟩
  · exact PEqualNP.Outside.Prism618.ten_gate_upper_bound
