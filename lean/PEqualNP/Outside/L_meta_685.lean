import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index

namespace PEqualNP.Outside.LMeta685

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Fintype F] [CharP F p]

private def frobeniusDifference (m : F) : F →+ F where
  toFun x := x ^ p - m * x
  map_zero' := by simp [zero_pow (Fact.out : p.Prime).ne_zero]
  map_add' x y := by rw [add_pow_char, mul_add, add_sub_add_comm]

omit [Fintype F] in
private theorem kernel_bound (m : F) : Nat.card (frobeniusDifference (p := p) m).ker ≤ p := by
  let P : Polynomial F := Polynomial.X ^ p - Polynomial.C m * Polynomial.X
  have hm : (Polynomial.C m * Polynomial.X).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_C_mul_X_pow_le m 1
  have hd : P.natDegree = p := by
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact hm.trans_lt (Fact.out : p.Prime).one_lt
  have hp : P ≠ 0 := by
    intro h
    exact (Fact.out : p.Prime).ne_zero (by simpa [h] using hd.symm)
  have hset : ((frobeniusDifference (p := p) m).ker : Set F) = P.rootSet F := by
    ext x
    rw [Polynomial.mem_rootSet_of_ne hp]
    simp [P, frobeniusDifference, Polynomial.aeval_def]
  change Nat.card ↥((frobeniusDifference (p := p) m).ker : Set F) ≤ p
  rw [hset, Nat.card_coe_set_eq, ← hd]
  exact P.ncard_rootSet_le F

private theorem kernel_card (m : F) :
    Nat.card (frobeniusDifference (p := p) m).ker = 1 ∨
    Nat.card (frobeniusDifference (p := p) m).ker = p := by
  let K := (frobeniusDifference (p := p) m).ker
  by_cases h : ∃ x : K, x ≠ 0
  · obtain ⟨x, hx⟩ := h
    have hp0 : p • x = 0 := by
      apply Subtype.ext
      change p • (x : F) = 0
      rw [nsmul_eq_mul, CharP.cast_eq_zero F p, zero_mul]
    have hd : p ∣ Nat.card K := by
      rw [← addOrderOf_eq_prime hp0 hx]
      exact addOrderOf_dvd_natCard x
    exact Or.inr (le_antisymm (kernel_bound m) (Nat.le_of_dvd Nat.card_pos hd))
  · have hsub : Subsingleton K := ⟨fun x y =>
      (by_contra fun hx => h ⟨x, hx⟩ : x = 0).trans (by_contra fun hy => h ⟨y, hy⟩ : y = 0).symm⟩
    exact Or.inl (Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩)

private theorem count_comap {F : Type} [AddCommGroup F] [Finite F] (f : F →+ F)
    (A : AddSubgroup F) : Nat.card (A.comap f) = Nat.card A * (f.range ⊔ A).index := by
  have h₁ : Nat.card (A.comap f) * A.relIndex f.range = Nat.card F := by
    rw [← A.index_comap f, AddSubgroup.card_mul_index]
  have h₂ : A.relIndex f.range * (f.range ⊔ A).index = A.index := by
    rw [← AddSubgroup.relIndex_sup_right f.range A]
    exact AddSubgroup.relIndex_mul_index le_sup_right
  have h₃ : (Nat.card A * (f.range ⊔ A).index) * A.relIndex f.range = Nat.card F := by
    rw [Nat.mul_right_comm, Nat.mul_assoc, h₂, AddSubgroup.card_mul_index]
  have hpos : 0 < A.relIndex f.range := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h₁.trans h₃.symm)

private theorem affine_card {F : Type} [AddCommGroup F] (f : F →+ F) (A : AddSubgroup F)
    (k t₀ : F) (ht₀ : f t₀ + k ∈ A) :
    Nat.card {x : F // f x + k ∈ A} = Nat.card (A.comap f) := by
  symm
  apply Nat.card_congr
  refine (Equiv.addRight t₀).subtypeEquiv (fun t => ?_)
  change f t ∈ A ↔ f (t + t₀) + k ∈ A
  rw [map_add, add_assoc]
  exact ⟨fun h => A.add_mem h ht₀, fun h => by simpa using A.sub_mem h ht₀⟩

private theorem main (A : AddSubgroup F) (m k : F) :
    Nat.card {x : F // x ^ p - m * x + k ∈ A} = 0 ∨
    Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card A ∨
    Nat.card {x : F // x ^ p - m * x + k ∈ A} = p * Nat.card A := by
  let f := frobeniusDifference (p := p) m
  change Nat.card {x : F // f x + k ∈ A} = 0 ∨
    Nat.card {x : F // f x + k ∈ A} = Nat.card A ∨
    Nat.card {x : F // f x + k ∈ A} = p * Nat.card A
  by_cases hex : ∃ x, f x + k ∈ A
  · obtain ⟨t₀, ht₀⟩ := hex
    rw [affine_card f A k t₀ ht₀, count_comap]
    have hdvd : (f.range ⊔ A).index ∣ f.range.index := AddSubgroup.index_dvd_of_le le_sup_left
    rw [AddSubgroup.index_range] at hdvd
    have hp := Fact.out (p := p.Prime)
    have hi : (f.range ⊔ A).index = 1 ∨ (f.range ⊔ A).index = p := by
      rcases kernel_card (p := p) m with hk | hk
      · rw [show Nat.card f.ker = 1 from hk] at hdvd
        exact Or.inl (Nat.dvd_one.mp hdvd)
      · rw [show Nat.card f.ker = p from hk] at hdvd
        exact (Nat.dvd_prime hp).mp hdvd
    rcases hi with hi | hi
    · exact Or.inr (Or.inl (by rw [hi, mul_one]))
    · exact Or.inr (Or.inr (by rw [hi, Nat.mul_comm]))
  · have hEmpty : IsEmpty {x : F // f x + k ∈ A} := ⟨fun x => hex ⟨x.val, x.property⟩⟩
    exact Or.inl (Nat.card_eq_zero.mpr (Or.inl hEmpty))

end PEqualNP.Outside.LMeta685

theorem PEqualNP.Outside.L_meta_685 :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
      (A : AddSubgroup F),
      (∀ a ∈ A, ∀ c : ZMod p, (ZMod.cast c : F) * a ∈ A) →
      ∀ m k : F,
        Nat.card {x : F // x ^ p - m * x + k ∈ A} = 0 ∨
        Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card A ∨
        Nat.card {x : F // x ^ p - m * x + k ∈ A} = p * Nat.card A := by
  intro p _ F _ _ _ A _ m k
  exact PEqualNP.Outside.LMeta685.main (p := p) A m k
