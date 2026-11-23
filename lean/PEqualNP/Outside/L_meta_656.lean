import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.ShortThread656

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem unchanged_read (x y : List Bool) (n o : ℕ) (a b : Bool)
    (hx : x.length = n) (hy : y.length = n) (ho : o ≠ n)
    (hread : x.getD o false = y.getD o false) :
    (x ++ [a]).getD o false = (y ++ [b]).getD o false := by
  by_cases h : o < n
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa [hx] using h),
      List.getElem?_append_left (by simpa [hy] using h)]
    simpa only [List.getD_eq_getElem?_getD] using hread
  · have hgt : n < o := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp [hx]; omega),
      List.getElem?_eq_none (by simp [hy]; omega)]

private theorem reads_at_most_two (C : Circuit) (n : ℕ) (hsize : C.size ≤ 1)
    (hfan : FanInTwo C) :
    ∃ W : Finset ℕ, W.card ≤ 2 ∧ ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ w ∈ W, x.getD w false = y.getD w false) → C.eval x = C.eval y := by
  cases hg : C.gates with
  | nil =>
      refine ⟨{C.output}, by simp, ?_⟩
      intro x y _ _ hread
      simpa [Circuit.eval, Circuit.wires, hg] using hread C.output (by simp)
  | cons g gs =>
      have hz : gs.length = 0 := by
        simp only [Circuit.size, hg, List.length_cons] at hsize
        omega
      have hone : C.gates = [g] := by simpa [List.length_eq_zero_iff.mp hz] using hg
      by_cases ho : C.output = n
      · have hlen := (hfan g (by simp [hone])).2
        refine ⟨g.inputs.toFinset, (List.toFinset_card_le g.inputs).trans hlen, ?_⟩
        intro x y hx hy hread
        have hmap : g.inputs.map (fun w => x.getD w false) =
            g.inputs.map (fun w => y.getD w false) :=
          List.map_congr_left fun w hw => hread w (by simpa using hw)
        simp only [Circuit.eval, Circuit.wires, hone, List.foldl_cons, List.foldl_nil, ho]
        rw [hmap]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hx, hy]
      · refine ⟨{C.output}, by simp, ?_⟩
        intro x y hx hy hread
        simp only [Circuit.eval, Circuit.wires, hone, List.foldl_cons, List.foldl_nil]
        exact unchanged_read x y n C.output _ _ hx hy ho (hread C.output (by simp))

private def essential {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x y, f x ≠ f y ∧ ∀ j : Fin n, j ≠ i → x j = y j

private theorem not_one_gate {n : ℕ} (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hT : 3 ≤ T.card) (hful : ∀ i ∈ T, essential f i) (s : ℕ) (hs : s ≤ 1) :
    ¬ HasCircuitSize n f s := by
  rintro ⟨C, hfan, hsize, heval⟩
  obtain ⟨W, hW, hread⟩ := reads_at_most_two C n (hsize.trans hs) hfan
  have hg : ∃ i ∈ T, i.val ∉ W := by
    by_contra! hh
    have hsub : T.map ⟨Fin.val, Fin.val_injective⟩ ⊆ W := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      exact hh i hi
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_map] at hcard
    omega
  obtain ⟨i, hi, hiW⟩ := hg
  obtain ⟨x, y, hne, hagree⟩ := hful i hi
  have he := hread (List.ofFn x) (List.ofFn y) List.length_ofFn List.length_ofFn ?_
  · rw [heval, heval] at he
    exact hne he
  · intro w hw
    by_cases h : w < n
    · have hiw : (⟨w, h⟩ : Fin n) ≠ i := fun e => hiW ((congrArg Fin.val e) ▸ hw)
      simp [List.getD_eq_getElem?_getD, h, hagree ⟨w, h⟩ hiw]
    · simp [List.getD_eq_getElem?_getD, h]

private def passenger (x : Fin 3 → Bool) : Bool := x 0 && x 1

private def cycle (x : Fin 5 → Bool) : Bool :=
  passenger (fun i : Fin 3 => x (Fin.castAdd 2 i)) ||
    (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1)

private def star (i : Fin 4) (x : Fin 4 → Bool) : Bool :=
  passenger (fun j : Fin 3 => x j.castSucc) || (x i && x 3)

private def path (x : Fin 5 → Bool) : Bool :=
  passenger (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)

private def cycleCircuit : Circuit where
  gates := [⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [5, 6]⟩]
  output := 7

private theorem cycle_three : HasCircuitSize 5 cycle 3 := by
  refine ⟨cycleCircuit, by simp [cycleCircuit, FanInTwo], by decide, ?_⟩
  decide

private theorem star_not_one (i : Fin 4) (hi : i = 0 ∨ i = 1) (s : ℕ) (hs : s ≤ 1) :
    ¬ HasCircuitSize 4 (star i) s := by
  apply not_one_gate (star i) {0, 1, 3} (by decide) _ s hs
  rcases hi with rfl | rfl <;> unfold essential <;> decide

private theorem path_not_one (s : ℕ) (hs : s ≤ 1) : ¬ HasCircuitSize 5 path s := by
  exact not_one_gate path {0, 1, 3} (by decide) (by unfold essential; decide) s hs

end PEqualNP.Outside.ShortThread656

open PEqualNP.Outside.ShortThread656 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_656 : ¬ (
  ∀ g : (Fin 3 → Bool) → Bool, (∀ x y : Fin 3 → Bool, (∀ i, x i = true → y i = true) → g x = true → g y = true) → g (fun _ : Fin 3 => false) = false →
    (∃ x : Fin 3 → Bool, g x = true) →
    (∃ x : Fin 3 → Bool, x 0 = true ∧ g x = false) →
    (∃ x : Fin 3 → Bool, x 1 = true ∧ g x = false) →
    ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3) || (x 3 && x 1)) s ↔
      ((∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨
       (∃ t : ℕ, 2 + t ≤ s ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) s)) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1)) s ↔
      ((∃ t : ℕ, 5 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨
       (∃ t : ℕ, 3 + t ≤ s ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨
       (∃ t : ℕ, 2 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t))) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 3 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 1)) s ↔
      ((∃ t : ℕ, 6 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨
       (∃ t : ℕ, 5 + t ≤ s ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨
       (∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t)))) := by
  intro h
  have hmono : ∀ x y : Fin 3 → Bool,
      (∀ i, x i = true → y i = true) → passenger x = true → passenger y = true := by decide
  have hn : passenger (fun _ => false) = false := rfl
  have ht : ∃ x, passenger x = true := by decide
  have h₀ : ∃ x, x 0 = true ∧ passenger x = false := by decide
  have h₁ : ∃ x, x 1 = true ∧ passenger x = false := by decide
  have hrow := h passenger hmono hn ht h₀ h₁ 3
  rcases hrow.2.1.mp cycle_three with ⟨t, hb, _⟩ | ⟨t, hb, hleft | hright⟩ | ⟨t, hb, hp⟩
  · omega
  · exact star_not_one 0 (Or.inl rfl) t (by omega) hleft
  · exact star_not_one 1 (Or.inr rfl) t (by omega) hright
  · exact path_not_one t (by omega) hp
