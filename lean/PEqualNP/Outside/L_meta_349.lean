import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_349 :
    ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n))
      (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b))
      (val : Finset (Fin n) → Fin b → Prop),
    (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) →
    (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
        ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) →
    (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
      ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) →
    ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g →
    (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) →
    ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I →
    (∃ w ∈ I, G.Adj u w) → val I H →
    (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  classical
  intro n b G PV RV PG RG OV OG val lp lr evaluate output g H u _ _ noRight occurs I ind _ hasEdge hH
  have noOutput : u ∉ OV := by
    intro hu
    obtain ⟨a, ha, c, hc, hadj⟩ := (output {u}).mp (Or.inl ⟨u, hu, by simp⟩)
    have ha' : a = u := by simpa using ha
    have hc' : c = u := by simpa using hc
    exact G.loopless u (by simpa [ha', hc'] using hadj)
  let J := insert u I
  have noLeft : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
    intro hleft
    have regress : ∀ k : ℕ, ∀ i : Fin b, i.val = k → val J i → val I i := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro i hi h
        by_cases hiH : i = H
        · simpa [hiH] using hH
        obtain ⟨hl, hr⟩ := (evaluate J i).mp h
        refine (evaluate I i).mpr ⟨?_, ?_⟩
        · by_cases hig : i = g
          · simpa [hig] using hleft
          · rcases hl with ⟨v, hv, hvJ⟩ | ⟨j, hj, hjJ⟩
            · rcases Finset.mem_insert.mp hvJ with rfl | hvI
              · exact ((occurs i (Or.inl hv)).elim hig hiH).elim
              · exact Or.inl ⟨v, hv, hvI⟩
            · exact Or.inr ⟨j, hj, ih j.val (by simpa [← hi] using lp i j hj) j rfl hjJ⟩
        · rcases hr with ⟨v, hv, hvJ⟩ | ⟨j, hj, hjJ⟩
          · rcases Finset.mem_insert.mp hvJ with rfl | hvI
            · rcases occurs i (Or.inr hv) with rfl | hiH'
              · exact (noRight hv).elim
              · exact (hiH hiH').elim
            · exact Or.inl ⟨v, hv, hvI⟩
          · exact Or.inr ⟨j, hj, ih j.val (by simpa [← hi] using lr i j hj) j rfl hjJ⟩
    obtain ⟨w, hw, huw⟩ := hasEdge
    have onJ := (output J).mpr ⟨u, by simp [J], w, by simp [J, hw], huw⟩
    have onI : (∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j := by
      rcases onJ with ⟨v, hv, hvJ⟩ | ⟨j, hj, hjJ⟩
      · rcases Finset.mem_insert.mp hvJ with rfl | hvI
        · exact (noOutput hv).elim
        · exact Or.inl ⟨v, hv, hvI⟩
      · exact Or.inr ⟨j, hj, regress j.val j rfl hjJ⟩
    obtain ⟨a, ha, c, hc, h⟩ := (output I).mp onI
    exact ind a ha c hc h
  exact ⟨fun v hv hvI => noLeft (Or.inl ⟨v, hv, hvI⟩),
    fun j hj hjI => noLeft (Or.inr ⟨j, hj, hjI⟩), fun h => noLeft (Or.inr ⟨H, h, hH⟩)⟩
