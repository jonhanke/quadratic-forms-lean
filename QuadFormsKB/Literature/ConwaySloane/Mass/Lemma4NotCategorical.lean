/-
# Conway–Sloane 1988, §11: Lemma 4 is not categorical

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, pp. 280–281: "lemma 2 has a categorical character not shared by lemma 4. In lemma 4
there need not be a 2-adically integral equivalence between $L$ and $M$ that induces the given isomorphism between
their dual quotients $L^*/L$ and $M^*/M$."

**Counterexample** (`lemma4_not_categorical`). Take $L = M = A_1^4$, Gram matrix $A = 2I_4$ (positive definite, even).
Then $L^*/L = \mathbb Z^4/2\mathbb Z^4$ (a class $[y]$ stands for the dual vector $A^{-1}y = y/2$, of norm
$y\cdot y/2$). The unimodular integer matrix $M_0$ sending $e_0 \mapsto e_0 + e_1 + e_2$ and fixing $e_1, e_2, e_3$
induces an automorphism $\varphi$ of $L^*/L$ that preserves norms modulo $1$ (`discIso_one`), so it is an isomorphism
as in Lemma 4. But $\varphi[e_0 + e_3] = [e_0 + e_1 + e_2 + e_3]$, with norms $1$ and $2$, which differ by an odd
integer; an isomorphism induced by an equivalence over $\mathbb Z_2$ preserves norms modulo $2\mathbb Z_2$ (the lattice
is even), so no $g \in M_4(\mathbb Z_2)$ with $g^{\mathsf T}Ag = A$ induces $\varphi$.

**Conventions.** A $2$-adic integral map $x \mapsto gx$, $g \in M_n(\mathbb Z_2)$, from $L \otimes \mathbb Z_2$ to
$M \otimes \mathbb Z_2$ is isometric iff $g^{\mathsf T}Bg = A$. It *induces* $\varphi : L^*/L \to M^*/M$
(`InducedBy`) iff whenever $\varphi[y] = [z]$ the dual vectors $B^{-1}z$ and $g A^{-1}y$ differ by a vector of
$\mathbb Z_2^n$ (both read in $\mathbb Q_2^n$). Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmas

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity

namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-- **An isomorphism of dual quotients induced by a $2$-adic integral map** $x \mapsto gx$ ($g \in M_n(\mathbb Z_2)$):
whenever $\varphi[y] = [z]$, the dual vectors $B^{-1}z$ and $gA^{-1}y$ differ by a vector with entries in
$\mathbb Z_2$. -/
def InducedBy (A B : Matrix (Fin n) (Fin n) ℤ) (g : Matrix (Fin n) (Fin n) ℤ_[2])
    (φ : DiscGroup A ≃+ DiscGroup B) : Prop :=
  ∀ y z : Fin n → ℤ, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk z →
    ∃ w : Fin n → ℤ_[2], (B.map (Int.castRingHom ℚ_[2]))⁻¹ *ᵥ (fun i => (z i : ℚ_[2])) =
      g.map PadicInt.Coe.ringHom *ᵥ ((A.map (Int.castRingHom ℚ_[2]))⁻¹ *ᵥ (fun i => (y i : ℚ_[2]))) +
        fun i => (w i : ℚ_[2])

/-- $A_1^4$: the Gram matrix $2I_4$. -/
def a1Four : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal fun _ => 2

/-- The unimodular matrix $e_0 \mapsto e_0 + e_1 + e_2$, $e_i \mapsto e_i$ ($i = 1, 2, 3$). -/
def twistMat : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 1, 1, 0, 0; 1, 0, 1, 0; 0, 0, 0, 1]

/-- Its inverse. -/
def twistInv : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; -1, 1, 0, 0; -1, 0, 1, 0; 0, 0, 0, 1]

theorem twistInv_mul : twistInv * twistMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [twistInv, twistMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem twist_mul : twistMat * twistInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [twistInv, twistMat, Matrix.mul_apply, Fin.sum_univ_four]

/-- $y \mapsto M_0 y$ as an additive automorphism of $\mathbb Z^4$. -/
def twistEquiv : (Fin 4 → ℤ) ≃+ (Fin 4 → ℤ) where
  toFun v := twistMat *ᵥ v
  invFun v := twistInv *ᵥ v
  left_inv v := by simp [mulVec_mulVec, twistInv_mul]
  right_inv v := by simp [mulVec_mulVec, twist_mul]
  map_add' v w := mulVec_add _ _ _

theorem mem_gramLat_a1Four {v : Fin 4 → ℤ} : v ∈ gramLat a1Four ↔ ∃ u : Fin 4 → ℤ, v = 2 • u := by
  rw [mem_gramLat]
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z, by ext i; simp [a1Four, mulVec_diagonal]⟩
  · rintro ⟨u, rfl⟩; exact ⟨u, by ext i; simp [a1Four, mulVec_diagonal]⟩

theorem map_gramLat_twist : (gramLat a1Four).map twistEquiv.toAddMonoidHom = gramLat a1Four := by
  ext v
  simp only [AddSubgroup.mem_map, mem_gramLat_a1Four]
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨twistMat *ᵥ u, by
      show twistMat *ᵥ (2 • u) = 2 • (twistMat *ᵥ u)
      rw [mulVec_smul]⟩
  · rintro ⟨u, rfl⟩
    refine ⟨2 • (twistInv *ᵥ u), ⟨_, rfl⟩, ?_⟩
    show twistMat *ᵥ (2 • (twistInv *ᵥ u)) = 2 • u
    rw [mulVec_smul, mulVec_mulVec, twist_mul, one_mulVec]

/-- **The automorphism $\varphi$ of $L^*/L$** induced by $M_0$. -/
noncomputable def twistDisc : DiscGroup a1Four ≃+ DiscGroup a1Four :=
  QuotientAddGroup.congr (gramLat a1Four) (gramLat a1Four) twistEquiv map_gramLat_twist

theorem twistDisc_mk (y : Fin 4 → ℤ) :
    twistDisc (QuotientAddGroup.mk y) = QuotientAddGroup.mk (twistMat *ᵥ y) := rfl

theorem gramQ_a1Four_inv : (gramQ a1Four)⁻¹ = Matrix.diagonal fun _ => (1 / 2 : ℚ) := by
  have h : gramQ a1Four = Matrix.diagonal fun _ => (2 : ℚ) := by
    ext i j; by_cases hij : i = j <;> simp [gramQ, a1Four, diagonal, hij]
  rw [h]
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]; norm_num

/-- The norm of the dual vector $y/2$: $y \cdot y / 2$. -/
theorem dualNorm_a1Four (y : Fin 4 → ℤ) : dualNorm a1Four y = ((∑ i, y i ^ 2 : ℤ) : ℚ) / 2 := by
  rw [dualNorm, gramQ_a1Four_inv]
  simp [dotProduct, mulVec_diagonal, Finset.sum_div, sq]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem posDefGram_a1Four : PosDefGram a1Four := by
  refine ⟨by simp [a1Four], fun x hx => ?_⟩
  have h : gramQ a1Four = Matrix.diagonal fun _ => (2 : ℚ) := by
    ext i j; by_cases hij : i = j <;> simp [gramQ, a1Four, diagonal, hij]
  rw [h]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_pos' (fun j _ => by nlinarith [sq_nonneg (x j)]) ⟨i, Finset.mem_univ _, ?_⟩
  have := pow_pos (abs_pos.2 hi) 2
  rw [sq_abs] at this
  nlinarith

/-- **$\varphi$ preserves norms modulo $1$**: it is an isomorphism of the kind in Lemma 4. -/
theorem twistDisc_preserves_one (y z : Fin 4 → ℤ)
    (h : twistDisc (QuotientAddGroup.mk y) = QuotientAddGroup.mk z) :
    ∃ k : ℤ, dualNorm a1Four z = dualNorm a1Four y + (1 : ℕ) * k := by
  rw [twistDisc_mk] at h
  obtain ⟨k, hk⟩ := dualNorm_congr_one posDefGram_a1Four.1 posDefGram_a1Four.det_ne h
  refine ⟨k + (y 0 ^ 2 + y 0 * y 1 + y 0 * y 2), ?_⟩
  rw [hk, dualNorm_a1Four, dualNorm_a1Four]
  simp [twistMat, Fin.sum_univ_four, mulVec, dotProduct]
  push_cast
  ring

theorem discIso_one_a1Four : DiscIso 1 a1Four a1Four := ⟨twistDisc, twistDisc_preserves_one⟩

theorem a1Four_map_inv : (a1Four.map (Int.castRingHom ℚ_[2]))⁻¹ = Matrix.diagonal fun _ => (1 / 2 : ℚ_[2]) := by
  have h : a1Four.map (Int.castRingHom ℚ_[2]) = Matrix.diagonal fun _ => (2 : ℚ_[2]) := by
    ext i j; by_cases hij : i = j <;> simp [a1Four, diagonal, hij]
  rw [h]
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]; norm_num

/-- **No $2$-adic integral automorphism induces $\varphi$.** -/
theorem not_inducedBy_twistDisc (g : Matrix (Fin 4) (Fin 4) ℤ_[2])
    (hg : gᵀ * a1Four.map (Int.castRingHom ℤ_[2]) * g = a1Four.map (Int.castRingHom ℤ_[2])) :
    ¬ InducedBy a1Four a1Four g twistDisc := by
  intro hI
  -- $g^{\mathsf T} g = 1$
  have hA2 : a1Four.map (Int.castRingHom ℤ_[2]) = (2 : ℤ_[2]) • (1 : Matrix (Fin 4) (Fin 4) ℤ_[2]) := by
    ext i j; by_cases hij : i = j <;> simp [a1Four, diagonal, hij]
  have hgg : gᵀ * g = 1 := by
    rw [hA2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hg i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ two_ne_zero this
  set y : Fin 4 → ℤ := ![1, 0, 0, 1] with hy
  set z : Fin 4 → ℤ := ![1, 1, 1, 1] with hz
  have hφ : twistDisc (QuotientAddGroup.mk y) = QuotientAddGroup.mk z := by
    rw [twistDisc_mk]; congr 1; ext i; fin_cases i <;> simp [twistMat, hy, hz, mulVec, dotProduct, Fin.sum_univ_four]
  obtain ⟨w, hw⟩ := hI y z hφ
  have hdiag : ∀ v : Fin 4 → ℚ_[2], (diagonal fun _ => (1 / 2 : ℚ_[2])) *ᵥ v = (1 / 2 : ℚ_[2]) • v := by
    intro v; funext i; simp [mulVec_diagonal]
  rw [a1Four_map_inv, hdiag, hdiag, mulVec_smul] at hw
  -- in $\mathbb Z_2$: $z = g y + 2 w$
  set yp : Fin 4 → ℤ_[2] := fun i => (y i : ℤ_[2])
  set zp : Fin 4 → ℤ_[2] := fun i => (z i : ℤ_[2])
  have hzp : zp = g *ᵥ yp + (2 : ℤ_[2]) • w := by
    funext i
    have hi := congrFun hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have e1 : (((g *ᵥ yp) i : ℤ_[2]) : ℚ_[2]) = (g.map PadicInt.Coe.ringHom *ᵥ fun j => (y j : ℚ_[2])) i := by
      have := RingHom.map_mulVec PadicInt.Coe.ringHom g yp i
      refine this.trans ?_
      congr 1
    apply PadicInt.ext
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_add, PadicInt.coe_mul, e1]
    simp only [zp, PadicInt.coe_intCast]
    have h2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by
      first | rfl | norm_cast | exact PadicInt.coe_natCast 2
    linear_combination 2 * hi - (w i : ℚ_[2]) * h2
  -- norms: $z \cdot z = y \cdot y + 4(\ldots)$
  have hnorm : zp ⬝ᵥ zp = yp ⬝ᵥ yp + 4 * (w ⬝ᵥ (g *ᵥ yp) + w ⬝ᵥ w) := by
    have hgy : (g *ᵥ yp) ⬝ᵥ (g *ᵥ yp) = yp ⬝ᵥ yp := by
      rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, hgg, transpose_one, one_mulVec]
    rw [hzp, add_dotProduct, dotProduct_add, dotProduct_add, hgy, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, dotProduct_comm (g *ᵥ yp) w]
    simp only [smul_eq_mul]; ring
  have hz2 : zp ⬝ᵥ zp = 4 := by simp [zp, hz, dotProduct, Fin.sum_univ_four]; norm_num
  have hy2 : yp ⬝ᵥ yp = 2 := by simp [yp, hy, dotProduct, Fin.sum_univ_four]; norm_num
  rw [hz2, hy2] at hnorm
  -- $2 = 4c$ in $\mathbb Z_2$ forces $1 = 2c$, impossible modulo $2$
  have h1 : (1 : ℤ_[2]) = 2 * (w ⬝ᵥ (g *ᵥ yp) + w ⬝ᵥ w) := by
    have h2 : (2 : ℤ_[2]) * 1 = 2 * (2 * (w ⬝ᵥ (g *ᵥ yp) + w ⬝ᵥ w)) := by linear_combination hnorm
    exact mul_left_cancel₀ two_ne_zero h2
  have h3 := congrArg (PadicInt.toZMod (p := 2)) h1
  rw [map_one, map_mul, map_ofNat] at h3
  have h0 : (2 : ZMod 2) = 0 := rfl
  rw [h0, zero_mul] at h3
  exact one_ne_zero h3

/-- **Conway–Sloane 1988, §11 (pp. 280–281): Lemma 4 is not categorical.** For the even lattice $L = A_1^4$
(Gram matrix $2I_4$) there is an automorphism $\varphi$ of $L^*/L$ preserving norms modulo $1$ (the data of Lemma 4
for $M = L$) that is not induced by any $2$-adically integral equivalence $x \mapsto gx$ of $L$ with itself
($g \in M_4(\mathbb Z_2)$, $g^{\mathsf T}Ag = A$). -/
@[kb "conwaysloane1988" "§11, remark 2, pp. 280–281"]
theorem lemma4_not_categorical :
    PosDefGram a1Four ∧ ∃ φ : DiscGroup a1Four ≃+ DiscGroup a1Four,
      (∀ y z : Fin 4 → ℤ, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk z →
        ∃ k : ℤ, dualNorm a1Four z = dualNorm a1Four y + (1 : ℕ) * k) ∧
      ∀ g : Matrix (Fin 4) (Fin 4) ℤ_[2],
        gᵀ * a1Four.map (Int.castRingHom ℤ_[2]) * g = a1Four.map (Int.castRingHom ℤ_[2]) →
        ¬ InducedBy a1Four a1Four g φ :=
  ⟨posDefGram_a1Four, twistDisc, twistDisc_preserves_one, not_inducedBy_twistDisc⟩

end QuadFormsKB.ConwaySloane.Mass
