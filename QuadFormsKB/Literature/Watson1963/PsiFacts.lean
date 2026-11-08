/-
# Watson (1963): the part with even Hessian of a square-free form at $2$

In the decomposition $F = U \perp \psi$ of `exists_decomp_two` ($U$ even unimodular, $\psi$ with all Hessian entries
even), the square-free condition `SqFree2` of $F$ (Watson's (2.6) at $p = 2$) is a condition on $\psi$ alone,
`SqFreePsi`: **if $4 \mid \psi(c)$ and $c'^{\mathsf T}H_\psi c \equiv 0 \pmod 4$ for every $c'$ with
$2 \mid \psi(c')$, then $c \equiv 0 \pmod 2$** (`sqFreePsi_of_decomp`). In terms of $\mathbb F_2$: on
$W = \{\psi \text{ even}\}$ the quadratic form $q = \psi/2 \bmod 2$ (with polar form $c'^{\mathsf T}H_\psi c/2$) has
trivial radical.
-/
import QuadFormsKB.Literature.Watson1963.Rep2

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n m : ℕ}

/-- **Square-free at $2$, for a form with even Hessian** (see the module docstring). Argument: the form `ψ` over
$\mathbb Z_2$. -/
def SqFreePsi (ψ : QuadForm ℤ_[2] m) : Prop :=
  ∀ c, (4 : ℤ_[2]) ∣ ψ.eval c → (∀ c', (2 : ℤ_[2]) ∣ ψ.eval c' → (4 : ℤ_[2]) ∣ c' ⬝ᵥ (ψ.hessian *ᵥ c)) →
    ∀ i, (2 : ℤ_[2]) ∣ c i

/-- Helper: pairings of vectors of the complement, computed in $\psi = F \circ K$. -/
theorem dot_compMat (F : QuadForm ℤ_[2] n) (K : Matrix (Fin n) (Fin m) ℤ_[2]) (c c' : Fin m → ℤ_[2]) :
    (K *ᵥ c') ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) = c' ⬝ᵥ ((F.compMat K).hessian *ᵥ c) := by
  rw [QuadForm.hessian_compMat, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec c' Kᵀ, vecMul_transpose]

theorem dot_symm (F : QuadForm ℤ_[2] n) (v w : Fin n → ℤ_[2]) :
    v ⬝ᵥ (F.hessian *ᵥ w) = w ⬝ᵥ (F.hessian *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hessian_isSymm', dotProduct_comm]

/-- Helper: with complement data, $K\vec c \equiv 0 \pmod 2$ forces $\vec c \equiv 0 \pmod 2$. -/
theorem two_dvd_of_two_dvd_mulVec {v : ℕ} (H : Matrix (Fin n) (Fin v) ℤ_[2]) (K : Matrix (Fin n) (Fin m) ℤ_[2])
    (hspan : ∀ z, ∃ y c, z = H *ᵥ y + K *ᵥ c) (huniq : ∀ y c, H *ᵥ y + K *ᵥ c = 0 → y = 0 ∧ c = 0)
    (c : Fin m → ℤ_[2]) (h : ∀ r, (2 : ℤ_[2]) ∣ (K *ᵥ c) r) : ∀ a, (2 : ℤ_[2]) ∣ c a := by
  choose w hw using h
  have hKw : K *ᵥ c = (2 : ℤ_[2]) • w := funext fun r => by rw [hw r]; rfl
  obtain ⟨y, c', hwc⟩ := hspan w
  have hz : H *ᵥ ((-2 : ℤ_[2]) • y) + K *ᵥ (c - (2 : ℤ_[2]) • c') = 0 := by
    rw [mulVec_smul, mulVec_sub, mulVec_smul, hKw, hwc]
    ext r
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    ring
  obtain ⟨-, hc0⟩ := huniq _ _ hz
  intro a
  have := congrFun hc0 a
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact ⟨c' a, by linear_combination this⟩

/-- **Square-freeness passes to $\psi$** (Watson 1963, §3: the 2-modular component of a square-free form). With the
data of `exists_decomp_two` ($H^{\mathsf T}H_F H$ invertible, $K$ an orthogonal complement), `SqFree2 F` implies
`SqFreePsi (F ∘ K)`. *Proof:* for $z = H\vec a + K\vec b \in \Lambda_2(F)$ the pairing with the columns of $H$ forces
$\vec a \equiv 0$, so $F(z) \equiv \psi(\vec b) \pmod 4$; apply `SqFree2` to $K\vec c$. -/
theorem sqFreePsi_of_decomp {v : ℕ} (F : QuadForm ℤ_[2] n) (hSF : SqFree2 F) (H : Matrix (Fin n) (Fin v) ℤ_[2])
    (K : Matrix (Fin n) (Fin m) ℤ_[2]) (hH : IsUnit (Hᵀ * F.hessian * H).det)
    (horth : ∀ y c, (H *ᵥ y) ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) = 0)
    (hspan : ∀ z, ∃ y c, z = H *ᵥ y + K *ᵥ c) (huniq : ∀ y c, H *ᵥ y + K *ᵥ c = 0 → y = 0 ∧ c = 0)
    (hpsi : ∀ i j, (2 : ℤ_[2]) ∣ (F.compMat K).hessian i j) : SqFreePsi (F.compMat K) := by
  set ψ := F.compMat K
  have hψ : ∀ c, F.eval (K *ᵥ c) = ψ.eval c := fun c => (QuadForm.eval_compMat F K c).symm
  have hdot2 : ∀ c c' : Fin m → ℤ_[2], (2 : ℤ_[2]) ∣ c' ⬝ᵥ (ψ.hessian *ᵥ c) := fun c c' => by
    simp only [dotProduct, mulVec]
    exact Finset.dvd_sum fun a _ => Dvd.dvd.mul_left (Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hpsi a b) _) _
  -- pairing of an arbitrary vector with K c
  have hpair : ∀ (c : Fin m → ℤ_[2]) (y : Fin v → ℤ_[2]) (b : Fin m → ℤ_[2]),
      (H *ᵥ y + K *ᵥ b) ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) = b ⬝ᵥ (ψ.hessian *ᵥ c) := fun c y b => by
    rw [add_dotProduct, horth, zero_add, dot_compMat]
  intro c h4 hz i
  have hL : InLam2 F (K *ᵥ c) := by
    refine ⟨by rw [hψ]; exact dvd_trans ⟨2, by norm_num⟩ h4, fun w => ?_⟩
    obtain ⟨y, b, rfl⟩ := hspan w
    rw [hpair]; exact hdot2 c b
  have hz' : ∀ z, InLam2 F z → (4 : ℤ_[2]) ∣ z ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c)) := by
    intro z hzL
    obtain ⟨a, b, rfl⟩ := hspan z
    rw [hpair]
    refine hz b ?_
    -- the H-part of z is even
    set G := Hᵀ * F.hessian * H
    have hGa : ∀ j, (2 : ℤ_[2]) ∣ (G *ᵥ a) j := fun j => by
      have h := hzL.2 (H *ᵥ Pi.single j 1)
      rw [mulVec_add, dotProduct_add, horth, add_zero] at h
      have e : (H *ᵥ Pi.single j 1) ⬝ᵥ (F.hessian *ᵥ (H *ᵥ a)) = (G *ᵥ a) j := by
        rw [dot_compMat, QuadForm.hessian_compMat, single_one_dotProduct]
      rw [← e]; exact h
    choose g hg using hGa
    have ha : a = (2 : ℤ_[2]) • (G⁻¹ *ᵥ g) := by
      have : G *ᵥ a = (2 : ℤ_[2]) • g := funext fun j => by rw [hg j]; rfl
      calc a = G⁻¹ *ᵥ (G *ᵥ a) := by rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hH, one_mulVec]
        _ = G⁻¹ *ᵥ ((2 : ℤ_[2]) • g) := by rw [this]
        _ = _ := mulVec_smul _ _ _
    have hFz : F.eval (H *ᵥ a + K *ᵥ b) = F.eval (H *ᵥ a) + ψ.eval b := by
      have hp := QuadForm.eval_polar F (H *ᵥ a) (K *ᵥ b)
      rw [horth, hψ] at hp
      linear_combination hp
    have hUa : (4 : ℤ_[2]) ∣ F.eval (H *ᵥ a) := by
      rw [ha, mulVec_smul, eval_smul_sq]
      exact ⟨_, by ring⟩
    have := hzL.1
    rw [hFz] at this
    have h2 : (2 : ℤ_[2]) ∣ F.eval (H *ᵥ a) := dvd_trans ⟨2, by norm_num⟩ hUa
    exact (dvd_add_right h2).1 this
  have hKc := hSF (K *ᵥ c) hL (by rw [hψ]; exact h4) hz'
  exact two_dvd_of_two_dvd_mulVec H K hspan huniq c hKc i

end QuadFormsKB.Watson1963
