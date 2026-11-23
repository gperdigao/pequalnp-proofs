import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_034

open PEqualNP.CircuitLowerBounds

private theorem read_unaffected (x y : List Bool) (n o : ℕ) (a b : Bool)
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

private theorem one_gate_read (C : Circuit) (n : ℕ) (hsize : C.size ≤ 1)
    (harity : ∀ g ∈ C.gates, g.inputs.length ≤ 1) :
    ∃ w : ℕ, ∀ x y : List Bool, x.length = n → y.length = n →
      x.getD w false = y.getD w false → C.eval x = C.eval y := by
  cases hg : C.gates with
  | nil =>
      refine ⟨C.output, ?_⟩
      intro x y _ _ hread
      simpa only [Circuit.eval, Circuit.wires, hg, List.foldl_nil] using hread
  | cons g rest =>
      have hlen : rest.length = 0 := by
        simp only [Circuit.size, hg, List.length_cons] at hsize
        omega
      have hgate : C.gates = [g] := by simpa [List.length_eq_zero_iff.mp hlen] using hg
      by_cases ho : C.output = n
      · have hi := harity g (by simp [hgate])
        cases hiL : g.inputs with
        | nil =>
            refine ⟨0, ?_⟩
            intro x y hx hy _
            simp only [Circuit.eval, Circuit.wires, hgate, List.foldl_cons, List.foldl_nil,
              hiL, List.map_nil, ho, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hx, hy]
        | cons w ws =>
            have hnil : ws.length = 0 := by
              simp only [hiL, List.length_cons] at hi
              omega
            have hinput : g.inputs = [w] := by simpa [List.length_eq_zero_iff.mp hnil] using hiL
            refine ⟨w, ?_⟩
            intro x y hx hy hread
            simp only [Circuit.eval, Circuit.wires, hgate, List.foldl_cons, List.foldl_nil,
              hinput, List.map_cons, List.map_nil, ho]
            rw [hread]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hx, hy]
      · refine ⟨C.output, ?_⟩
        intro x y hx hy hread
        simp only [Circuit.eval, Circuit.wires, hgate, List.foldl_cons, List.foldl_nil]
        exact read_unaffected x y n C.output _ _ hx hy ho hread

end PEqualNP.Outside.L_clb_034

open PEqualNP.Outside.L_clb_034 in
theorem PEqualNP.Outside.L_clb_034 :
    ∀ (n d : ℕ), 2 ≤ n → ({x : List Bool | x.all id = true} : Language Bool) ∉
      PEqualNP.CircuitLowerBounds.SizeDepth {PEqualNP.CircuitLowerBounds.GateOp.and,
        PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not}
        (fun n' : ℕ => if n' = n then 1 else n' + 2) d := by
  intro n d hn hfamily
  obtain ⟨C, harity, hsize, _, hdec⟩ := hfamily n
  have hsize' : C.size ≤ 1 := by simpa using hsize
  have harity' : ∀ g ∈ C.gates, g.inputs.length ≤ 1 := by
    intro g hg
    simpa using (harity g hg).2
  obtain ⟨w, hdepends⟩ := one_gate_read C n hsize' harity'
  let bad : Fin n := if w = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hbad : bad.val ≠ w := by
    by_cases h : w = 0
    · simp [bad, h]
    · simpa [bad, h] using Ne.symm h
  let yes : List Bool := List.ofFn (fun _ : Fin n => true)
  let no : List Bool := List.ofFn (fun i : Fin n => decide (i ≠ bad))
  have hread : yes.getD w false = no.getD w false := by
    by_cases h : w < n
    · have hne : (⟨w, h⟩ : Fin n) ≠ bad := by
        intro he
        exact hbad ((congrArg Fin.val he).symm)
      simp [yes, no, List.getD_eq_getElem?_getD, h, hne]
    · simp [yes, no, List.getD_eq_getElem?_getD, h]
  have hyes : yes.all id = true := by simp [yes]
  have hwitness : false ∈ no := List.mem_ofFn.mpr ⟨bad, by simp⟩
  have hno : no.all id ≠ true := by
    intro h
    have hf := List.all_eq_true.mp h false hwitness
    simp at hf
  have heval := hdepends yes no (List.length_ofFn) (List.length_ofFn) hread
  have hone := (hdec yes (List.length_ofFn)).mpr hyes
  exact hno ((hdec no (List.length_ofFn)).mp (heval ▸ hone))
