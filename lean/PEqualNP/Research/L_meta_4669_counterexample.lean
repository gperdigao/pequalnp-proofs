import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

theorem refutes_L_meta_4669 : ¬ (∀ x1 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)],   have x3 : Fin (24 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : Fin (24 : ℕ)) (x4 : Fin (9 : ℕ)) => ([(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x4;   have x4 : Fin (24 : ℕ) → List Bool := fun (x4 : Fin (24 : ℕ)) => List.ofFn (x3 x4) ++ [!x3 x4 (0 : Fin (9 : ℕ)), x3 x4 (Fin.ofNat (9 : ℕ) (x1 / (10 : ℕ))) || x3 x4 (Fin.ofNat (9 : ℕ) (x1 % (10 : ℕ)))];   have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x4 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true];   ∀ (x6 : List (Fin (24 : ℕ) → Bool)),     x6.length ≤ (13 : ℕ) →       (∀ (x8 : Fin x6.length),           have x9 : List (Fin (24 : ℕ) → Bool) := x5 ++ List.take (↑x8) x6;           (∃ x10 ∈ x9, x6.get x8 = fun (x11 : Fin (24 : ℕ)) => !x10 x11) ∨ ∃ x10 ∈ x9, ∃ x11 ∈ x9, (x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 && x11 x12) ∨ x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 || x11 x12) →         (fun (x9 : Fin (24 : ℕ)) => Decidable.decide (↑x9 < (12 : ℕ))) ∉ x5 ++ x6) := by

  intro claim
  specialize claim 13 (by decide)
  let samples : List ℕ :=
    [3,6,12,24,17,33,66,132,264,160,320,288,42,50,69,104,116,138,201,208,261,276,385,402]
  let input (r : Fin 24) (j : Fin 9) : Bool := (samples.getD r.val 0).testBit j.val
  let col (j : Fin 11) (r : Fin 24) : Bool :=
    (List.ofFn (input r) ++ [!(input r 0), input r 1 || input r 3]).getD j.val false
  let init : List (Fin 24 → Bool) := List.ofFn col ++ [fun _ => false, fun _ => true]
  have col_mem (j : Fin 11) (past : List (Fin 24 → Bool)) : col j ∈ init ++ past := by
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    left
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  let u : Fin 24 → Bool := fun r => col 0 r || col 4 r
  let v : Fin 24 → Bool := fun r => col 2 r || col 7 r
  let a : Fin 24 → Bool := fun r => u r && v r
  let w : Fin 24 → Bool := fun r => col 5 r || col 7 r
  let b : Fin 24 → Bool := fun r => col 10 r && w r
  let both : Fin 24 → Bool := fun r => a r || b r
  let result : Fin 24 → Bool := fun r => !both r
  let trace : List (Fin 24 → Bool) := [u,v,a,w,b,both,result]
  have allowed (j : Fin trace.length) :
      let past := init ++ trace.take j.val
      (∃ s ∈ past, trace.get j = fun r => !s r) ∨
        ∃ s ∈ past, ∃ t ∈ past,
          (trace.get j = fun r => s r && t r) ∨ trace.get j = fun r => s r || t r := by
    fin_cases j
    · exact Or.inr ⟨col 0, col_mem 0 _, col 4, col_mem 4 _, Or.inr rfl⟩
    · exact Or.inr ⟨col 2, col_mem 2 _, col 7, col_mem 7 _, Or.inr rfl⟩
    · refine Or.inr ⟨u, ?_, v, ?_, Or.inl rfl⟩
      all_goals exact List.mem_append.mpr (Or.inr (by simp [trace]))
    · exact Or.inr ⟨col 5, col_mem 5 _, col 7, col_mem 7 _, Or.inr rfl⟩
    · refine Or.inr ⟨col 10, col_mem 10 _, w, ?_, Or.inl rfl⟩
      exact List.mem_append.mpr (Or.inr (by simp [trace]))
    · refine Or.inr ⟨a, ?_, b, ?_, Or.inr rfl⟩
      all_goals exact List.mem_append.mpr (Or.inr (by simp [trace]))
    · refine Or.inl ⟨both, ?_, rfl⟩
      exact List.mem_append.mpr (Or.inr (by simp [trace]))
  have evaluates : result = fun r : Fin 24 => decide (r.val < 12) := by
    funext r
    fin_cases r <;> decide
  apply claim trace (by decide) allowed
  rw [← evaluates]
  exact List.mem_append.mpr (Or.inr (by simp [trace]))

