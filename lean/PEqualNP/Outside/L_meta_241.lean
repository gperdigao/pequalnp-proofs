import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.MetaComplexity

theorem L_meta_241 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, Nat.zero_le s, ?_⟩
  intro x
  change (List.ofFn x).getD n false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
  rfl

end PEqualNP.Outside
