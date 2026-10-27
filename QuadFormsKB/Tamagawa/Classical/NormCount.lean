/-
# Norms from $\mathbb Z[i]$ and $\mathbb Z[\sqrt2]$ modulo norm-one units

**Layer:** Mathlib only (`Zsqrtd`, `GaussianInt`, `Pell`). The norm-one units $\mathrm{unitary}(\mathbb Z[\sqrt d])$ act on
the elements of norm $m$ by multiplication (`normSet`). For $\mathbb Z[i]$ the four units act freely on the nonzero
elements, so $\#\{z : N(z) = m\} = 4\,\#(\text{orbits})$ (`card_normSet_gaussian`); for $\mathbb Z[\sqrt2]$ the norm-one units
are $\pm(3+2\sqrt2)^k$ (`pell2_units`).
-/
import Mathlib

open MulAction
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Classical

/-- The elements of norm `m` of $\mathbb Z[\sqrt d]$. -/
def normSet (d m : ℤ) : Type := {z : ℤ√d // z.norm = m}

/-- A norm-one unit has norm one. -/
theorem norm_of_mem_unitary {d : ℤ} (u : unitary (ℤ√d)) : (u : ℤ√d).norm = 1 :=
  Zsqrtd.norm_eq_one_iff_mem_unitary.mpr u.2

/-- **Norm-one units act on the elements of norm $m$** by multiplication. -/
instance normSetAction (d m : ℤ) : MulAction (unitary (ℤ√d)) (normSet d m) where
  smul u z := ⟨(u : ℤ√d) * z.1, by
    rw [Zsqrtd.norm_mul, norm_of_mem_unitary u, one_mul]; exact z.2⟩
  one_smul z := Subtype.ext (by
    show ((1 : unitary (ℤ√d)) : ℤ√d) * z.1 = z.1
    simp)
  mul_smul u v z := Subtype.ext (by
    show ((u * v : unitary (ℤ√d)) : ℤ√d) * z.1 = (u : ℤ√d) * ((v : ℤ√d) * z.1)
    exact mul_assoc _ _ _)

theorem normSet_smul_val (d m : ℤ) (u : unitary (ℤ√d)) (z : normSet d m) :
    (u • z).1 = (u : ℤ√d) * z.1 := rfl

/-- For $m \ge 1$ the elements of norm $m$ of $\mathbb Z[i]$ form a finite set. -/
instance finite_normSet_gaussian (m : ℤ) : Finite (normSet (-1) m) := by
  have key : ∀ z : normSet (-1) m, z.1.re ∈ Finset.Icc (-m) m ∧ z.1.im ∈ Finset.Icc (-m) m := by
    intro z
    have h := z.2
    rw [Zsqrtd.norm_def] at h
    have h1 := Int.le_self_sq z.1.re
    have h2 := Int.le_self_sq (-z.1.re)
    have h3 := Int.le_self_sq z.1.im
    have h4 := Int.le_self_sq (-z.1.im)
    simp only [Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg z.1.re, sq_nonneg z.1.im]
  exact Finite.of_injective
    (fun z : normSet (-1) m =>
      ((⟨z.1.re, (key z).1⟩ : Finset.Icc (-m) m), (⟨z.1.im, (key z).2⟩ : Finset.Icc (-m) m)))
    (by
      intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Zsqrtd.ext h.1 h.2))

/-- The elements of norm $m$ of $\mathbb Z[i]$ are the pairs $(x_0, x_1)$ with $x_0^2 + x_1^2 = m$. -/
theorem card_normSet_gaussian_eq (m : ℤ) :
    Nat.card (normSet (-1) m) = Nat.card {x : ℤ × ℤ // x.1 ^ 2 + x.2 ^ 2 = m} := by
  refine Nat.card_congr
    { toFun := fun z => ⟨(z.1.re, z.1.im), ?_⟩
      invFun := fun x => ⟨⟨x.1.1, x.1.2⟩, ?_⟩
      left_inv := fun z => rfl
      right_inv := fun x => rfl }
  · have h := z.2
    rw [Zsqrtd.norm_def] at h
    simp only
    nlinarith
  · have h := x.2
    show (Zsqrtd.norm ⟨x.1.1, x.1.2⟩ : ℤ) = m
    rw [Zsqrtd.norm_def]
    simp only
    nlinarith

/-- `unitary GaussianInt` has four elements. -/
theorem card_unitary_gaussian : Nat.card (unitary (ℤ√(-1))) = 4 := by
  have e : Nat.card (unitary (ℤ√(-1))) = Nat.card (normSet (-1) 1) :=
    Nat.card_congr
      { toFun := fun u => ⟨u.1, norm_of_mem_unitary u⟩
        invFun := fun z => ⟨z.1, Zsqrtd.norm_eq_one_iff_mem_unitary.mp z.2⟩
        left_inv := fun u => rfl
        right_inv := fun z => rfl }
  rw [e, card_normSet_gaussian_eq]
  have : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = 1} =
      ↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      have ha : a ∈ Finset.Icc (-1 : ℤ) 1 := by
        simp only [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg b]
      have hb : b ∈ Finset.Icc (-1 : ℤ) 1 := by
        simp only [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg a]
      simp only [Finset.mem_Icc] at ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      interval_cases a <;> interval_cases b <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  have h2 : Nat.card {x : ℤ × ℤ // x.1 ^ 2 + x.2 ^ 2 = 1} =
      Nat.card (↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        have := Set.ext_iff.mp this x
        simpa using this))
  rw [h2, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

/-- Multiplication by a unit fixing a nonzero element forces the unit to be one. -/
theorem smul_eq_self_gaussian {m : ℤ} (hm : m ≠ 0) (u : unitary (ℤ√(-1))) (z : normSet (-1) m)
    (h : u • z = z) : u = 1 := by
  have hz : z.1 ≠ 0 := by
    intro h0
    apply hm
    rw [← z.2, h0]
    simp
  have h' : (u : ℤ√(-1)) * z.1 = 1 * z.1 := by
    rw [one_mul]; exact congrArg Subtype.val h
  exact Subtype.ext (mul_right_cancel₀ hz h')

/-- **$\#\{z\in\mathbb Z[i] : N(z) = m\} = 4\cdot\#(\text{orbits of the units})$** for $m \ne 0$: the four units act freely. -/
theorem card_normSet_gaussian {m : ℤ} (hm : m ≠ 0) :
    (Nat.card (normSet (-1) m) : ℝ≥0∞) =
      4 * ∑' _ : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m), (1 : ℝ≥0∞) := by
  classical
  have : Fintype (orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m)) :=
    Fintype.ofFinite _
  have horb : ∀ x : normSet (-1) m, Nat.card (orbit (unitary (ℤ√(-1))) x) = 4 := by
    intro x
    rw [← card_unitary_gaussian]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun u => ⟨u • x, u, rfl⟩) ⟨?_, ?_⟩)
    · intro u v h
      have h' : u • x = v • x := congrArg Subtype.val h
      have : (v⁻¹ * u) • x = x := by rw [mul_smul, h', inv_smul_smul]
      have := smul_eq_self_gaussian hm _ _ this
      exact (inv_mul_eq_one.mp this).symm
    · rintro ⟨_, u, rfl⟩
      exact ⟨u, rfl⟩
  have h1 : Nat.card (normSet (-1) m) =
      Nat.card (Σ ω : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m),
        orbit (unitary (ℤ√(-1))) ω.out) :=
    Nat.card_congr (selfEquivSigmaOrbits (unitary (ℤ√(-1))) (normSet (-1) m))
  have : ∀ ω : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m),
      Finite (orbit (unitary (ℤ√(-1))) ω.out) := fun _ => inferInstance
  have : ∀ ω : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m),
      Fintype (orbit (unitary (ℤ√(-1))) ω.out) := fun _ => Fintype.ofFinite _
  rw [h1, Nat.card_sigma]
  have h3 : ∀ ω : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m),
      Nat.card (orbit (unitary (ℤ√(-1))) ω.out) = 4 := fun ω => horb _
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [tsum_fintype]
  simp [mul_comm]

/-- The elements of norm $m$ of $\mathbb Z[\sqrt2]$ are the pairs $(x_0, x_1)$ with $x_0^2 - 2x_1^2 = m$. -/
def normSetEquivPell2 (m : ℤ) : normSet 2 m ≃ {x : Fin 2 → ℤ // x 0 ^ 2 - 2 * x 1 ^ 2 = m} where
  toFun z := ⟨![z.1.re, z.1.im], by
    have h := z.2
    rw [Zsqrtd.norm_def] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith⟩
  invFun x := ⟨⟨x.1 0, x.1 1⟩, by
    have h := x.2
    show (Zsqrtd.norm ⟨x.1 0, x.1 1⟩ : ℤ) = m
    rw [Zsqrtd.norm_def]
    simp only
    nlinarith⟩
  left_inv z := rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

/-- **The fundamental unit** $3 + 2\sqrt2$ of norm one of $\mathbb Z[\sqrt2]$. -/
def pell2Fund : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

theorem pell2Fund_isFundamental : Pell.IsFundamental pell2Fund := by
  refine ⟨by simp [pell2Fund], by simp [pell2Fund], ?_⟩
  intro b hb
  have hx : (pell2Fund).x = 3 := rfl
  rw [hx]
  by_contra hlt
  have h2 : b.x = 2 := by omega
  have hp := b.prop
  rw [h2] at hp
  have : (2 : ℤ) ^ 2 - 2 * b.y ^ 2 = 1 := hp
  have h5 : (2 : ℤ) * b.y ^ 2 = 3 := by linarith
  omega

/-- **The norm-one units of $\mathbb Z[\sqrt2]$ are $\pm(3+2\sqrt2)^k$**, $k\in\mathbb Z$. -/
theorem pell2_units (u : Pell.Solution₁ 2) : ∃ k : ℤ, u = pell2Fund ^ k ∨ u = -pell2Fund ^ k :=
  pell2Fund_isFundamental.eq_zpow_or_neg_zpow u

end QuadFormsKB.Tamagawa.Classical
