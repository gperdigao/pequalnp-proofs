import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_988_aux

private def vals (G : List Gate) (w : List Bool) : List Bool :=
  G.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun k => a.getD k false)]) w

private def wire {n : ℕ} (G : List Gate) (x : Fin n → Bool) (k : ℕ) : Bool :=
  (vals G (List.ofFn x)).getD k false

private theorem vals_length (G : List Gate) (w : List Bool) :
    (vals G w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp [vals]
  | cons g G ih =>
    change (vals G (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).length = _
    rw [ih]
    simp
    omega

private theorem wire_snoc {n : ℕ} (G : List Gate) (g : Gate) (x : Fin n → Bool) (k : ℕ) :
    wire (G ++ [g]) x k = if k = n + G.length then
      g.op.eval (g.inputs.map (wire G x)) else wire G x k := by
  let w := vals G (List.ofFn x)
  have hw : w.length = n + G.length := by simp [w, vals_length]
  have hv : vals (G ++ [g]) (List.ofFn x) =
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)] := by
    simp [w, vals, List.foldl_append]
  unfold wire
  rw [hv]
  change (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD k false =
    if k = n + G.length then _ else w.getD k false
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : k < w.length
  · rw [List.getElem?_append_left h, ite_eq_right (by omega)]
  · rw [List.getElem?_append_right (by omega)]
    simp only [List.getElem?_eq_none (by omega : w.length ≤ k), Option.getD_none]
    by_cases e : k = n + G.length
    · simp [e, hw, w]
    · have hsub : k - w.length ≠ 0 := by omega
      simp [e, hsub]

private theorem wire_nil {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    wire [] x k = if h : k < n then x ⟨k, h⟩ else false := by
  by_cases h : k < n <;> simp [wire, vals, List.getD_eq_getElem?_getD, h]

private theorem wire_mono {n : ℕ} {x z : Fin n → Bool} (hx : ∀ v, x v = true → z v = true)
    (G : List Gate) (hG : ∀ g ∈ G, g.op = .and ∨ g.op = .or) :
    ∀ k, wire G x k = true → wire G z k = true := by
  induction G using List.reverseRecOn with
  | nil =>
    intro k hk
    rw [wire_nil] at hk ⊢
    by_cases h : k < n
    · simpa [h] using hx ⟨k, h⟩ (by simpa [h] using hk)
    · simp [h] at hk
  | append_singleton G g ih =>
    have prev := ih (fun a ha => hG a (by simp [ha]))
    have hg := hG g (by simp)
    intro k hk
    rw [wire_snoc] at hk ⊢
    by_cases h : k = n + G.length
    · rcases hg with hAnd | hOr
      · simp only [h, ite_true, hAnd, GateOp.eval, List.all_eq_true, List.mem_map,
          id_eq, forall_exists_index, and_imp] at hk ⊢
        intro _ j hj rfl
        exact prev j (hk _ _ hj rfl)
      · simp only [h, ite_true, hOr, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk ⊢
        obtain ⟨_, ⟨j, hj, rfl⟩, hval⟩ := hk
        exact ⟨_, ⟨j, hj, rfl⟩, prev j hval⟩
    · simp only [ite_eq_right h] at hk ⊢
      exact prev k hk

private def outside {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ S)

private def row {n : ℕ} (Y : Finset (Fin n)) (p v : Fin n) : Bool := decide (v ∈ Y ∨ v = p)

private def Aligned {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin n)
    (P : Fin n → Prop) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, P p → P q → f p = f q

private def Good {n : ℕ} (G : List Gate) (S Y : Finset (Fin n)) (f : Fin n → Fin n) : Prop :=
  ∀ k, wire G (outside S) k = false → Aligned S f (fun p => wire G (row Y p) k = true)

private def Charge {n : ℕ} (G : List Gate) (S Y : Finset (Fin n)) (k : ℕ) : Prop :=
  wire G (outside S) k = false ∧
  ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ wire G (row Y p) k = true ∧ wire G (row Y q) k = true

private noncomputable def cost {n : ℕ} (G : List Gate) (S Y : Finset (Fin n)) (k : ℕ) : ℕ := by
  classical
  exact if Charge G S Y k then 1 else 0

private theorem initial_good {n : ℕ} (S Y : Finset (Fin n)) (h : Disjoint Y S) :
    Good [] S Y id := by
  intro k hm p hp q hq hpv hqv
  by_cases hk : k < n
  · have ha : (⟨k, hk⟩ : Fin n) ∈ S := by
      simpa [wire_nil, hk, outside] using hm
    have hy : (⟨k, hk⟩ : Fin n) ∉ Y := fun hv => Finset.disjoint_left.mp h hv ha
    have ep : (⟨k, hk⟩ : Fin n) = p := by simpa [wire_nil, hk, row, hy] using hpv
    have eq : (⟨k, hk⟩ : Fin n) = q := by simpa [wire_nil, hk, row, hy] using hqv
    exact ep.symm.trans eq
  · simp [wire_nil, hk] at hpv

private theorem join_colour {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin n)
    (P Q : Fin n → Prop) (hP : Aligned S f P) (hQ : Aligned S f Q) :
    ∃ f' : Fin n → Fin n, (∀ p q, f p = f q → f' p = f' q) ∧
      Aligned S f' (fun p => P p ∨ Q p) ∧ (S.image f).card ≤ (S.image f').card + 1 := by
  classical
  by_cases hp : ∃ p ∈ S, P p
  · by_cases hq : ∃ q ∈ S, Q q
    · obtain ⟨a, ha, hap⟩ := hp
      obtain ⟨b, hb, hbq⟩ := hq
      let f' := fun x => if f x = f a then f b else f x
      refine ⟨f', fun p q e => by simp [f', e], ?_, ?_⟩
      · have hr : ∀ p ∈ S, P p ∨ Q p → f' p = f b := by
          intro p hp hv
          rcases hv with h | h
          · simp [f', hP p hp a ha h hap]
          · simp [f', hQ p hp b hb h hbq]
        exact fun p hp q hq ep eq => (hr p hp ep).trans (hr q hq eq).symm
      · calc
          (S.image f).card ≤ (insert (f a) (S.image f')).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
            by_cases h : f p = f a
            · simp [h]
            · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, by simp [f', h]⟩)
          _ ≤ (S.image f').card + 1 := Finset.card_insert_le _ _
    · refine ⟨f, fun _ _ e => e, ?_, by omega⟩
      intro p hp' q hq' ep eq
      exact hP p hp' q hq' (ep.resolve_right fun h => hq ⟨p, hp', h⟩)
        (eq.resolve_right fun h => hq ⟨q, hq', h⟩)
  · refine ⟨f, fun _ _ e => e, ?_, by omega⟩
    intro p hp' q hq' ep eq
    exact hQ p hp' q hq' (ep.resolve_left fun h => hp ⟨p, hp', h⟩)
      (eq.resolve_left fun h => hp ⟨q, hq', h⟩)

private theorem good_step {n : ℕ} (G : List Gate) (g : Gate) (S Y : Finset (Fin n))
    (f : Fin n → Fin n) (hf : Good G S Y f) (hop : g.op = .and ∨ g.op = .or)
    (hLen : g.inputs.length ≤ 2) :
    ∃ f' : Fin n → Fin n, Good (G ++ [g]) S Y f' ∧
      (S.image f).card ≤ (S.image f').card + cost (G ++ [g]) S Y (n + G.length) := by
  classical
  let t := n + G.length
  have hX : ∀ (f' : Fin n → Fin n), (∀ p q, f p = f q → f' p = f' q) →
      (wire (G ++ [g]) (outside S) t = false →
        Aligned S f' (fun p => wire (G ++ [g]) (row Y p) t = true)) →
      Good (G ++ [g]) S Y f' := by
    intro f' hpres ht k hout p hp q hq ep eq
    by_cases hk : k = t
    · subst k
      exact ht hout p hp q hq ep eq
    · have hk' : k ≠ n + G.length := hk
      simp only [wire_snoc, ite_eq_right hk'] at hout ep eq
      exact hpres p q (hf k hout p hp q hq ep eq)
  by_cases hC : Charge (G ++ [g]) S Y (n + G.length)
  · simp only [cost, ite_eq_left hC]
    rcases hop with ha | ho
    · refine ⟨f, hX f (fun _ _ e => e) ?_, by omega⟩
      intro hm p hp q hq ep eq
      have hraw : (g.inputs.map (wire G (outside S))).all id = false := by
        simpa [t, wire_snoc, ha, GateOp.eval] using hm
      obtain ⟨_, hmj, hj⟩ := List.all_eq_false.mp hraw
      obtain ⟨j, hj', rfl⟩ := List.mem_map.mp hmj
      have ev : ∀ v, wire (G ++ [g]) (row Y v) t = true → wire G (row Y v) j = true := by
        intro v hval
        have hrawv : (g.inputs.map (wire G (row Y v))).all id = true := by
          simpa [t, wire_snoc, ha, GateOp.eval] using hval
        exact List.all_eq_true.mp hrawv _ (List.mem_map.mpr ⟨j, hj', rfl⟩)
      exact hf j (by simpa using hj) p hp q hq (ev p ep) (ev q eq)
    · have hm := hC.1
      have mchild : ∀ j ∈ g.inputs, wire G (outside S) j = false := by
        intro j hj
        have hraw : (g.inputs.map (wire G (outside S))).any id = false := by
          simpa [t, wire_snoc, ho, GateOp.eval] using hm
        simpa using List.any_eq_false.mp hraw _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
      cases hs : g.inputs with
      | nil =>
        obtain ⟨_, _, _, _, _, hp, _⟩ := hC.2
        simp [wire_snoc, ho, GateOp.eval, hs] at hp
      | cons a rest =>
        cases rest with
        | nil =>
          refine ⟨f, hX f (fun _ _ e => e) ?_, by omega⟩
          intro _ p hp q hq ep eq
          exact hf a (mchild a (by simp [hs])) p hp q hq
            (by simpa [t, wire_snoc, ho, GateOp.eval, hs] using ep)
            (by simpa [t, wire_snoc, ho, GateOp.eval, hs] using eq)
        | cons b rest =>
          have hr : rest = [] := by
            have hlen' : (a :: b :: rest).length ≤ 2 := hs ▸ hLen
            have ne : rest.length = 0 := by
              simp only [List.length_cons] at hlen'
              omega
            simpa using ne
          subst rest
          obtain ⟨f', hpres, hj, hc⟩ := join_colour S f _ _
            (hf a (mchild a (by simp [hs]))) (hf b (mchild b (by simp [hs])))
          refine ⟨f', hX f' hpres ?_, hc⟩
          intro _ p hp q hq ep eq
          exact hj p hp q hq
            (by simpa [t, wire_snoc, ho, GateOp.eval, hs] using ep)
            (by simpa [t, wire_snoc, ho, GateOp.eval, hs] using eq)
  · simp only [cost, ite_eq_right hC]
    refine ⟨f, hX f (fun _ _ e => e) ?_, by omega⟩
    intro hm p hp q hq ep eq
    by_cases h : p = q
    · simp [h]
    · exact (hC ⟨hm, p, hp, q, hq, h, ep, eq⟩).elim

private theorem sharing {n m : ℕ} (S Y : Fin m → Finset (Fin n))
    (hS : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (G : List Gate) (hG : ∀ g ∈ G, g.op = .and ∨ g.op = .or) (k : ℕ)
    {i j : Fin m} (hi : Charge G (S i) (Y i) k) (hj : Charge G (S j) (Y j) k)
    (hij : i ≠ j) : ¬ Disjoint (Y i) (S j) := by
  classical
  intro disj
  obtain ⟨_, p, hp, q, hq, hne, hpt, hqt⟩ := hi
  have hpoint : ∃ u : Fin n, u ∉ S j ∧ wire G (row (Y i) u) k = true := by
    by_cases hpj : p ∈ S j
    · by_cases hqj : q ∈ S j
      · have hpq : ({p, q} : Finset (Fin n)) ⊆ S i ∩ S j := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp, hpj⟩
          · exact Finset.mem_inter.mpr ⟨hq, hqj⟩
        have h2 := Finset.card_le_card hpq
        have h1 := hS i j hij
        simp [hne] at h2
        omega
      · exact ⟨q, hqj, hqt⟩
    · exact ⟨p, hpj, hpt⟩
  obtain ⟨u, hu, hv⟩ := hpoint
  have hsub : ∀ v, row (Y i) u v = true → outside (S j) v = true := by
    intro v hrv
    have hv' : v ∈ Y i ∨ v = u := by simpa [row] using hrv
    rw [outside, decide_eq_true_eq]
    intro hvs
    rcases hv' with hy | rfl
    · exact Finset.disjoint_left.mp disj hy hvs
    · exact hu hvs
  have ht := wire_mono hsub G hG k hv
  rw [hj.1] at ht
  contradiction

private theorem invariant {n m D : ℕ} (S Y : Fin m → Finset (Fin n))
    (hS : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (hY : ∀ i, Disjoint (Y i) (S i))
    (hShare : ∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (Y i) (S j)) → J.card ≤ D)
    (G : List Gate) (hG : ∀ g ∈ G, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∃ f : Fin m → Fin n → Fin n, (∀ i, Good G (S i) (Y i) (f i)) ∧
      (∑ i : Fin m, (S i).card) ≤ (∑ i : Fin m, ((S i).image (f i)).card) + D * G.length := by
  classical
  induction G using List.reverseRecOn with
  | nil => exact ⟨fun _ => id, fun i => initial_good _ _ (hY i), by simp⟩
  | append_singleton G g ih =>
    obtain ⟨f, hf, hb⟩ := ih (fun a ha => hG a (by simp [ha]))
    have hg := hG g (by simp)
    choose f' hf' hStep using fun i => good_step G g (S i) (Y i) (f i) (hf i) hg.1 hg.2
    let J := Finset.univ.filter fun i : Fin m => Charge (G ++ [g]) (S i) (Y i) (n + G.length)
    have hJ : J.card ≤ D := by
      apply hShare J
      intro i hi j hj hne
      exact sharing S Y hS _ (fun a ha => (hG a ha).1) _
        ((Finset.mem_filter.mp hi).2) ((Finset.mem_filter.mp hj).2) hne
    have hSum : (∑ i : Fin m, cost (G ++ [g]) (S i) (Y i) (n + G.length)) = J.card := by
      unfold cost J
      rw [← Finset.sum_filter]
      simp
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hStep i)
    rw [Finset.sum_add_distrib, hSum] at hs
    refine ⟨f', hf', ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_add, Nat.mul_one]
    omega

end PEqualNP.Outside.L_meta_988_aux

open PEqualNP.Outside.L_meta_988_aux in
theorem PEqualNP.Outside.L_meta_988 :
    ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (o : Fin m → ℕ),
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i : Fin m, Disjoint (y i) (S i)) →
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (i : Fin m) (x : Fin n → Bool),
        (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) →
    (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n =>
        decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) →
    (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) →
    ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hS hy hC hBelow hPoint hShare
  obtain ⟨f, hf, hb⟩ := invariant S y hS hy hShare C.gates hC
  have himg : ∀ i, ((S i).image (f i)).card ≤ 1 := by
    intro i
    have hm : wire C.gates (outside (S i)) (o i) = false := by
      by_contra h
      have ht : wire C.gates (outside (S i)) (o i) = true := by simpa using h
      obtain ⟨p, hp, hpt⟩ := hBelow i (outside (S i)) ht
      simp [outside, hp] at hpt
    apply Finset.card_le_one.mpr
    intro a ha b hb'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb'
    exact hf i (o i) hm p hp q hq (hPoint i p hp) (hPoint i q hq)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => himg i)
  simp at hs
  omega
