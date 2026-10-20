/-
# Conjugation on the pure quaternions in an arbitrary coordinate system

**Layer:** a field $K$ with $2 \ne 0$, $D = (a,b)_K$, and an invertible matrix $P \in GL_3(K)$ whose columns are the
coordinates (in $i, j, k$) of a basis $e_0, e_1, e_2$ of the pure quaternions $D^0$.

`QuaternionSO3.lean` identifies $D^\times/K^\times$ with $SO(\langle -a,-b,ab\rangle)(K)$ in the coordinates $i, j, k$.
For the ternary lattice $\mathcal O^0$ of a maximal order the natural coordinates are those of an $\mathcal O_F$-basis of
$\mathcal O^0$, so we transport: $\psi_P(y) = \sum_l y_le_l = $ `pure (P *ᵥ y)`, the form $Q_P = \langle -a,-b,ab\rangle\circ P$
(`(pureForm a b).compMat P`), and
$$c_P(\alpha) = P^{-1}\,\mathrm{conj}(\alpha)\,P,\qquad \psi_P(c_P(\alpha)\,y) = \alpha\,\psi_P(y)\,\alpha^{-1}$$
(`cvHom`, `psi_cvHom`). It lands in $\{g : g^{\mathsf T}H_{Q_P}g = H_{Q_P},\ \det g = 1\}$, every such $g$ is a $c_P(\alpha)$, and
$c_P(\alpha) = 1$ iff $\alpha \in K^\times$.

Source: Weil 1982, §3.7(a), p. 63.
-/
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.LocalDensity.FormDensitySelf

open Matrix Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Quat

variable {K : Type*} [Field K] {a b : K}

/-- The coordinate map $\psi_P : K^3 \to D^0$, $y \mapsto \sum_l y_l e_l$, where the columns of $P$ are the $i,j,k$-coordinates
of the $e_l$. -/
def psiP (P : Matrix (Fin 3) (Fin 3) K) (y : Fin 3 → K) : ℍ[K,a,b] := pure (P *ᵥ y)

theorem psiP_add (P : Matrix (Fin 3) (Fin 3) K) (y z : Fin 3 → K) :
    (psiP P (y + z) : ℍ[K,a,b]) = psiP P y + psiP P z := by
  rw [psiP, mulVec_add, pure_add]; rfl

theorem psiP_smul (P : Matrix (Fin 3) (Fin 3) K) (c : K) (y : Fin 3 → K) :
    (psiP P (c • y) : ℍ[K,a,b]) = c • psiP P y := by
  rw [psiP, mulVec_smul, pure_smul]; rfl

theorem psiP_injective {P : Matrix (Fin 3) (Fin 3) K} (hP : IsUnit P.det) :
    Function.Injective (psiP P : (Fin 3 → K) → ℍ[K,a,b]) := by
  intro y z h
  have h1 : P *ᵥ y = P *ᵥ z := by
    have := congrArg imv h
    simpa [psiP] using this
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hP
  have := congrArg (fun w => P⁻¹ *ᵥ w) h1
  simpa [mulVec_mulVec, Matrix.nonsing_inv_mul _ hP] using this

theorem nrd_psiP (P : Matrix (Fin 3) (Fin 3) K) (y : Fin 3 → K) :
    nrd (psiP P y : ℍ[K,a,b]) = ((pureForm a b).compMat P).eval y := by
  rw [psiP, nrd_pure, QuadForm.eval_compMat]

/-- **Conjugation in the coordinates $P$:** $c_P(\alpha) = P^{-1}\,\mathrm{conj}(\alpha)\,P$, a homomorphism $D^\times \to GL_3(K)$. -/
def cvHom (P : GL (Fin 3) K) : (ℍ[K,a,b])ˣ →* GL (Fin 3) K :=
  (MulAut.conj P⁻¹).toMonoidHom.comp ((SO (pureForm a b)).subtype.comp conjSO)

theorem cvHom_apply (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) : cvHom P α = P⁻¹ * conjGL α * P := by
  simp [cvHom]; rfl

theorem cvHom_val (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) :
    ((cvHom P α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * LinearMap.toMatrix' (conjLin α) * P.val := by
  rw [cvHom_apply]; rfl

/-- **$\psi_P(c_P(\alpha)y) = \alpha\,\psi_P(y)\,\alpha^{-1}$.** -/
theorem psiP_cvHom (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) (y : Fin 3 → K) :
    psiP (P : Matrix (Fin 3) (Fin 3) K) ((cvHom P α : GL (Fin 3) K).val *ᵥ y) =
      (α : ℍ[K,a,b]) * psiP (P : Matrix (Fin 3) (Fin 3) K) y * ((α⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) := by
  rw [psiP, psiP, cvHom_val, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mul, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec, pure_conjLin]

theorem det_cvHom (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) : (cvHom P α).val.det = 1 := by
  rw [cvHom_val, det_mul, det_mul, det_conjLin, mul_one, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    det_one]

/-- **$c_P(\alpha)$ is an isometry of $Q_P$:** $c_P(\alpha)^{\mathsf T}H_{Q_P}c_P(\alpha) = H_{Q_P}$ ($2 \ne 0$). -/
theorem cvHom_hessian (h2 : (2 : K) ≠ 0) (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) :
    (cvHom P α).valᵀ * ((pureForm a b).compMat P.val).hessian *
      (cvHom P α).val = ((pureForm a b).compMat P.val).hessian := by
  have hC := ((mem_SO_iff_hessian h2).1 (conjGL_mem α)).2
  rw [QuadForm.hessian_compMat, cvHom_val]
  set C := LinearMap.toMatrix' (conjLin α)
  set Pm := (P : Matrix (Fin 3) (Fin 3) K)
  set Pi := ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hPP : Pm * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  change (Pi * C * Pm)ᵀ * (Pmᵀ * (pureForm a b).hessian * Pm) * (Pi * C * Pm) = _
  have hC' : Cᵀ * (pureForm a b).hessian * C = (pureForm a b).hessian := hC
  calc (Pi * C * Pm)ᵀ * (Pmᵀ * (pureForm a b).hessian * Pm) * (Pi * C * Pm)
      = Pmᵀ * Cᵀ * ((Pm * Pi)ᵀ * (pureForm a b).hessian * (Pm * Pi)) * C * Pm := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Pmᵀ * (Cᵀ * (pureForm a b).hessian * C) * Pm := by
        rw [hPP, transpose_one, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC']

/-- **Every rotation of $Q_P$ is a $c_P(\alpha)$** ($2 \ne 0$, $a, b \ne 0$). -/
theorem exists_cvHom_eq (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (P : GL (Fin 3) K) (g : GL (Fin 3) K)
    (hg : g.valᵀ * ((pureForm a b).compMat P.val).hessian * g =
      ((pureForm a b).compMat P.val).hessian) (hdet : g.val.det = 1) :
    ∃ α : (ℍ[K,a,b])ˣ, cvHom P α = g := by
  set Pm := (P : Matrix (Fin 3) (Fin 3) K)
  set Pi := ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hPP : Pm * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : Pi * Pm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set h : GL (Fin 3) K := P * g * P⁻¹
  have hmem : h ∈ SO (pureForm a b) := by
    rw [mem_SO_iff_hessian h2]
    refine ⟨?_, ?_⟩
    · change (Pm * g.val * Pi).det = 1
      rw [det_mul, det_mul, hdet, mul_one, ← det_mul, hPP, det_one]
    · change (Pm * g.val * Pi)ᵀ * (pureForm a b).hessian * (Pm * g.val * Pi) = _
      rw [QuadForm.hessian_compMat] at hg
      calc (Pm * g.val * Pi)ᵀ * (pureForm a b).hessian * (Pm * g.val * Pi)
          = Piᵀ * (g.valᵀ * (Pmᵀ * (pureForm a b).hessian * Pm) * g.val) * Pi := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = Piᵀ * (Pmᵀ * (pureForm a b).hessian * Pm) * Pi := by rw [hg]
        _ = (Pm * Pi)ᵀ * (pureForm a b).hessian * (Pm * Pi) := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hPP, transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨α, hα⟩ := conjSO_surjective h2 ha hb ⟨h, hmem⟩
  refine ⟨α, ?_⟩
  rw [cvHom_apply]
  have : conjGL α = h := congrArg Subtype.val hα
  rw [this]
  simp only [h]
  group

/-- **The kernel of $c_P$ is $K^\times$:** $c_P(\alpha) = 1$ iff $\alpha$ is a scalar ($2 \ne 0$, $a \ne 0$). -/
theorem cvHom_eq_one_iff (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (P : GL (Fin 3) K) (α : (ℍ[K,a,b])ˣ) :
    cvHom P α = 1 ↔ ∃ r : K, (α : ℍ[K,a,b]) = algebraMap K ℍ[K,a,b] r := by
  simp only [QuaternionAlgebra.coe_algebraMap]
  rw [← mem_centerUnits, ← ker_conjSO h2 ha, MonoidHom.mem_ker, cvHom_apply]
  constructor
  · intro h
    have h1 : conjGL α = 1 := by
      have := congrArg (fun g => P * g * P⁻¹) h
      simpa [mul_assoc] using this
    exact Subtype.ext h1
  · intro h
    have h1 : conjGL α = 1 := congrArg Subtype.val h
    rw [h1]; group

theorem cvHom_eq_iff (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (P : GL (Fin 3) K) (α β : (ℍ[K,a,b])ˣ) :
    cvHom P α = cvHom P β ↔ ∃ r : K, (α : ℍ[K,a,b]) = algebraMap K ℍ[K,a,b] r * β := by
  have : cvHom P α = cvHom P β ↔ cvHom P (α * β⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [this, cvHom_eq_one_iff h2 ha]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have := congrArg (· * (β : ℍ[K,a,b])) hr
    simpa [mul_assoc] using this
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [Units.val_mul, hr, mul_assoc, Units.mul_inv, mul_one]

end QuadFormsKB.Quat
