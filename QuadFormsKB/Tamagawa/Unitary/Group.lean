import QuadFormsKB.Tamagawa.Unitary.UnitaryOne

/-!
# Unitary groups of hermitian spaces: $U(V)$, $SU(V)$ and $\det : U(V)\to U(1)$

**Layer:** a field $K$ of characteristic $0$ containing the number field $F$ (the $k$ of the unitary-group literature;
$K = F$, a completion $F_v$, $\mathbb R$ or $\mathbb C$), $E = F(\omega)$ with $\omega^2 = -D$, $D\in\mathcal O_F$, $D\ne0$, as in
`UnitaryOne.lean`, and $E\otimes_FK = K[\omega]$ (`QuadK D K`) with its conjugation $z\mapsto\bar z$ (`star`). A hermitian
space of dimension $m$ is $(E\otimes K)^m$ with a hermitian matrix $H$ ($H^* = H$, `Matrix.IsHermitian`), and the
hermitian form $h(x,y) = y^*Hx$ (linear in $x$, conjugate-linear in $y$). $\det H$ is fixed by the conjugation, hence lies
in $K$ (`det_eq_algebraMap_re`); $V$ is nondegenerate iff $\det H\ne0$. Indices are $0$-based (`Fin m`).

*Comparison with Gan–Hanke–Yu's convention.* Gan–Hanke–Yu 2001, §§3–4 write $\langle x,y\rangle = \sum_{i,j}x_iH_{ij}\bar y_j = x^{\mathsf T}H\bar y$
(`GanHankeYu2001.herm`); this is $h(x,y)$ for the matrix $H^{\mathsf T}$ (also hermitian). The groups agree:
$g^{\mathsf T}H\bar g = H\iff g^*H^{\mathsf T}g = H^{\mathsf T}$ (conjugate the first identity).

**Defines**
* `unitaryH D K H` $= U(V)(K) = \{g\in GL_m(E\otimes K) : g^*Hg = H\}$;
* `specialUnitaryH D K H` $= SU(V)(K) = \{g\in U(V)(K) : \det g = 1\}$;
* `detU D K hH hdet` : $U(V)(K)\to U(1)(K)$, $g\mapsto\det g$ (for hermitian nondegenerate $H$).

**Proves**
* `ker_detU`: $\ker(\det) = SU(V)(K)$;
* `exists_anisotropic`: a nonzero hermitian $H$ has a vector $e$ with $h(e,e) = c\in K^\times$ (no assumption that $E\otimes K$
  is a field: it may split);
* `unitaryTransvection`: for such $e$ and $t\in U(1)(K)$, $g_t(x) = x + (t-1)\,c^{-1}h(x,e)\,e$ is unitary with
  $\det g_t = t$ (`det_unitaryTransvection`, `unitaryTransvection_mem`);
* **`detU_surjective`**: $\det : U(V)(K)\to U(1)(K)$ is surjective for every nondegenerate hermitian space of dimension
  $m\ge1$, so $1\to SU(V)\to U(V)\xrightarrow{\det}U(1)\to1$ is exact on $K$-points. This is the algebraic input of
  Ono's reduction $\tau(U(V)) = \tau(U(1))\,\tau(SU(V))$.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] (D : NumberField.RingOfIntegers F)
variable (K : Type*) [Field K] [Algebra F K] [CharZero K] {m : ℕ}

/-! ### Scalars of $E\otimes K$ -/

/-- $\bar z = z$ iff $z\in K$. -/
theorem star_eq_self_iff (z : QuadK D K) : star z = z ↔ z = algebraMap K (QuadK D K) z.re := by
  constructor
  · intro h
    have him : z.im = 0 := by
      have := congrArg QuadraticAlgebra.im h
      simp only [QuadraticAlgebra.im_star] at this
      have h2 : (2 : K) * z.im = 0 := by linear_combination -this
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    ext <;> simp [him]
  · intro h
    rw [h]
    ext <;> simp

theorem star_algebraMap_quadK (r : K) : star (algebraMap K (QuadK D K) r) = algebraMap K (QuadK D K) r := by
  ext <;> simp

/-- $z + \bar z = 2\,\mathrm{Re}\,z$. -/
theorem add_star_quadK (z : QuadK D K) : z + star z = algebraMap K (QuadK D K) (2 * z.re) := by
  ext <;> simp; ring

variable {D K}

/-- **The determinant of a hermitian matrix lies in $K$**: $\det H = \mathrm{Re}(\det H)$. -/
theorem det_eq_algebraMap_re {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) :
    H.det = algebraMap K (QuadK D K) H.det.re := by
  rw [← star_eq_self_iff, ← det_conjTranspose, hH.eq]

/-! ### The groups -/

variable (D K)

/-- **The unitary group** $U(V)(K) = \{g\in GL_m(E\otimes_FK) : g^*Hg = H\}$ of the hermitian space $((E\otimes K)^m, H)$
(Gan–Hanke–Yu 2001, §3, p. 105 and §4, p. 109: "$G$ the corresponding unitary group"). -/
@[kb "ganhankeyu2001" "§3, p. 105; §4, p. 109 (G = U(V), the unitary group)"]
def unitaryH (H : Matrix (Fin m) (Fin m) (QuadK D K)) : Subgroup (GL (Fin m) (QuadK D K)) where
  carrier := {g | g.valᴴ * H * g.val = H}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, conjTranspose_mul] at ha hb ⊢
    calc b.valᴴ * a.valᴴ * H * (a.val * b.val) = b.valᴴ * (a.valᴴ * H * a.val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : (a⁻¹).valᴴ * a.valᴴ = 1 := by
      rw [← conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, conjTranspose_one]
    have h2 : a.val * (a⁻¹).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (a⁻¹).valᴴ * H * (a⁻¹).val = (a⁻¹).valᴴ * (a.valᴴ * H * a.val) * (a⁻¹).val := by rw [ha]
      _ = ((a⁻¹).valᴴ * a.valᴴ) * H * (a.val * (a⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem mem_unitaryH {H : Matrix (Fin m) (Fin m) (QuadK D K)} {g : GL (Fin m) (QuadK D K)} :
    g ∈ unitaryH D K H ↔ g.valᴴ * H * g.val = H := Iff.rfl

/-- **The special unitary group** $SU(V)(K) = \{g\in U(V)(K) : \det g = 1\}$. -/
@[kb "ganhankeyu2001" "§4, p. 109 (G = U(V); SU(V) its derived group, simply connected) [running text]"]
def specialUnitaryH (H : Matrix (Fin m) (Fin m) (QuadK D K)) : Subgroup (GL (Fin m) (QuadK D K)) :=
  unitaryH D K H ⊓ (Matrix.GeneralLinearGroup.det).ker

theorem mem_specialUnitaryH {H : Matrix (Fin m) (Fin m) (QuadK D K)} {g : GL (Fin m) (QuadK D K)} :
    g ∈ specialUnitaryH D K H ↔ g ∈ unitaryH D K H ∧ (g : Matrix (Fin m) (Fin m) (QuadK D K)).det = 1 := by
  rw [specialUnitaryH, Subgroup.mem_inf, MonoidHom.mem_ker, Units.ext_iff]
  rfl

variable {D K}

/-- For $g\in U(V)(K)$ and nondegenerate hermitian $H$: $N(\det g) = \overline{\det g}\det g = 1$. -/
theorem det_mem_unitary {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hdet : H.det ≠ 0)
    {g : GL (Fin m) (QuadK D K)} (hg : g ∈ unitaryH D K H) :
    (g : Matrix (Fin m) (Fin m) (QuadK D K)).det ∈ unitary (QuadK D K) := by
  rw [← QuadraticAlgebra.norm_eq_one_iff_mem_unitary]
  have h := congrArg Matrix.det ((mem_unitaryH D K).1 hg)
  rw [det_mul, det_mul, det_conjTranspose] at h
  set c := H.det.re
  have hc : H.det = algebraMap K (QuadK D K) c := det_eq_algebraMap_re hH
  have hc0 : c ≠ 0 := by
    intro h0; apply hdet; rw [hc, h0, map_zero]
  set z := (g : Matrix (Fin m) (Fin m) (QuadK D K)).det
  have hz : algebraMap K (QuadK D K) (z.norm * c) = algebraMap K (QuadK D K) c := by
    rw [map_mul, QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← hc]
    linear_combination h
  have := (algebraMap K (QuadK D K)).injective hz
  exact mul_right_cancel₀ hc0 (this.trans (one_mul c).symm)

/-- **$\det : U(V)(K)\to U(1)(K)$** for a nondegenerate hermitian space. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (det : U(V) → U(1), Ono's route to τ(G) = 2)"]
def detU {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hdet : H.det ≠ 0) :
    unitaryH D K H →* U1 D K where
  toFun g := ⟨((g : GL (Fin m) (QuadK D K)) : Matrix (Fin m) (Fin m) (QuadK D K)).det, det_mem_unitary hH hdet g.2⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [det_mul]

@[simp] theorem coe_detU {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hdet : H.det ≠ 0)
    (g : unitaryH D K H) :
    ((detU hH hdet g : U1 D K) : QuadK D K) = ((g : GL (Fin m) (QuadK D K)) : Matrix (Fin m) (Fin m) _).det := rfl

/-- **$\ker(\det) = SU(V)(K)$.** -/
theorem ker_detU {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hdet : H.det ≠ 0)
    (g : unitaryH D K H) : g ∈ (detU hH hdet).ker ↔ (g : GL (Fin m) (QuadK D K)) ∈ specialUnitaryH D K H := by
  rw [MonoidHom.mem_ker, mem_specialUnitaryH, Subtype.ext_iff]
  simp [g.2]

/-! ### Anisotropic vectors and unitary transvections -/

/-- **A nonzero hermitian form has an anisotropic vector**: $h(e,e) = e^*He = c\in K^\times$. $E\otimes K$ need not be a
field. If some $H_{ii}\ne0$ take $e = e_i$; otherwise $H_{ij}\ne0$ for some $i\ne j$ and $e = e_i + \lambda e_j$ with
$\lambda\in\{1,\omega\}$ gives $h(e,e) = 2\,\mathrm{Re}(\lambda H_{ij})\ne0$. -/
theorem exists_anisotropic (hD : D ≠ 0) {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hne : H ≠ 0) :
    ∃ (e : Fin m → QuadK D K) (c : K), c ≠ 0 ∧ star e ⬝ᵥ (H *ᵥ e) = algebraMap K (QuadK D K) c := by
  classical
  have hdiag : ∀ i, H i i = algebraMap K (QuadK D K) (H i i).re := fun i =>
    (star_eq_self_iff D K _).1 (hH.apply i i)
  by_cases h : ∃ i, H i i ≠ 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨Pi.single i 1, (H i i).re, ?_, ?_⟩
    · intro h0; apply hi; rw [hdiag i, h0, map_zero]
    · rw [← hdiag i]
      simp [Pi.star_single, mulVec_single, single_dotProduct]
  · push_neg at h
    obtain ⟨i, j, hij⟩ : ∃ i j, H i j ≠ 0 := by
      by_contra h'
      push_neg at h'
      exact hne (Matrix.ext h')
    have hji : H j i = star (H i j) := (hH.apply j i).symm
    -- the value of h(e_i + λ e_j, e_i + λ e_j)
    have key : ∀ l : QuadK D K, star (Pi.single i 1 + Pi.single j l) ⬝ᵥ (H *ᵥ (Pi.single i 1 + Pi.single j l)) =
        algebraMap K (QuadK D K) (2 * (H i j * l).re) := by
      intro l
      rw [← add_star_quadK]
      rw [star_add, Pi.star_single, Pi.star_single, star_one, mulVec_add, add_dotProduct, dotProduct_add,
        dotProduct_add]
      simp only [mulVec_single, single_dotProduct, Matrix.col_apply, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, Pi.smul_apply, smul_eq_mul, h i, h j, one_mul, mul_one, mul_zero, zero_mul, add_zero,
        zero_add, hji, star_mul, star_star]
    have hd0 : algebraMap F K (dD D) ≠ 0 := by
      rw [dD_algebraMap]; exact neg_ne_zero.2 (dIn_ne_zero D hD K)
    by_cases hre : (H i j).re = 0
    · have him : (H i j).im ≠ 0 := by
        intro h0; apply hij; ext <;> simp [hre, h0]
      refine ⟨Pi.single i 1 + Pi.single j ⟨0, 1⟩, 2 * (H i j * ⟨0, 1⟩).re, ?_, key _⟩
      simp only [QuadraticAlgebra.re_mul, hre]
      simpa using And.intro hd0 him
    · refine ⟨Pi.single i 1 + Pi.single j 1, 2 * (H i j * 1).re, ?_, key _⟩
      simpa using hre

variable (D K)

/-- **The unitary transvection** $g_t = 1 + (t-1)c^{-1}\,e\,(e^*H)$, i.e. $g_t(x) = x + (t-1)c^{-1}h(x,e)\,e$, for
$h(e,e) = c\in K^\times$: it is $t$ on $(E\otimes K)e$ and the identity on $e^\perp$. -/
def transvMat (H : Matrix (Fin m) (Fin m) (QuadK D K)) (e : Fin m → QuadK D K) (c : K) (t : QuadK D K) :
    Matrix (Fin m) (Fin m) (QuadK D K) :=
  1 + ((t - 1) * algebraMap K (QuadK D K) c⁻¹) • vecMulVec e (star e ᵥ* H)

variable {D K}

theorem det_transvMat {H : Matrix (Fin m) (Fin m) (QuadK D K)} {e : Fin m → QuadK D K} {c : K} (hc : c ≠ 0)
    (he : star e ⬝ᵥ (H *ᵥ e) = algebraMap K (QuadK D K) c) (t : QuadK D K) :
    (transvMat D K H e c t).det = t := by
  rw [transvMat, ← vecMulVec_smul, vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    ← dotProduct_mulVec, he, smul_eq_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  ring

theorem transvMat_unitary {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) {e : Fin m → QuadK D K}
    {c : K} (hc : c ≠ 0) (he : star e ⬝ᵥ (H *ᵥ e) = algebraMap K (QuadK D K) c) {t : QuadK D K}
    (ht : t ∈ unitary (QuadK D K)) :
    (transvMat D K H e c t)ᴴ * H * transvMat D K H e c t = H := by
  set u := H *ᵥ e
  set ι := algebraMap K (QuadK D K) c⁻¹
  set γ := algebraMap K (QuadK D K) c
  set s := (t - 1) * ι
  have hw : star e ᵥ* H = star u := by
    rw [star_mulVec, hH.eq]
  have hstar_s : star s = (star t - 1) * ι := by
    rw [star_mul, star_sub, star_one, star_algebraMap_quadK, mul_comm]
  have hιγ : ι * γ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  have htt : star t * t = 1 := Unitary.star_mul_self_of_mem ht
  have hue : star u ⬝ᵥ e = γ := by rw [← hw, ← dotProduct_mulVec, he]
  have h1 : H * vecMulVec e (star u) = vecMulVec u (star u) := by rw [mul_vecMulVec]
  have h2 : vecMulVec u (star e) * H = vecMulVec u (star u) := by rw [vecMulVec_mul, hw]
  have h3 : vecMulVec u (star u) * vecMulVec e (star u) = γ • vecMulVec u (star u) := by
    rw [vecMulVec_mul_vecMulVec, hue, vecMulVec_smul]
  have hT : transvMat D K H e c t = 1 + s • vecMulVec e (star u) := by rw [transvMat, hw]
  have hTc : (transvMat D K H e c t)ᴴ = 1 + star s • vecMulVec u (star e) := by
    rw [hT, conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec, star_star]
  have hcoef : s + star s + star s * s * γ = 0 := by
    rw [hstar_s]
    simp only [s]
    linear_combination ι * htt + (star t - 1) * (t - 1) * ι * hιγ
  rw [hTc, hT]
  calc (1 + star s • vecMulVec u (star e)) * H * (1 + s • vecMulVec e (star u))
      = H + s • (H * vecMulVec e (star u)) + star s • (vecMulVec u (star e) * H) +
          (star s * s) • (vecMulVec u (star e) * H * vecMulVec e (star u)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        rw [smul_add, smul_smul, mul_comm s (star s)]
        abel
    _ = H + (s + star s + star s * s * γ) • vecMulVec u (star u) := by
        rw [h1, h2, h3, smul_smul]
        module
    _ = H := by rw [hcoef, zero_smul, add_zero]

/-- **The unitary transvection as an element of $U(V)(K)$** ($t\in U(1)(K)$). -/
def unitaryTransvection {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) {e : Fin m → QuadK D K} {c : K}
    (hc : c ≠ 0) (he : star e ⬝ᵥ (H *ᵥ e) = algebraMap K (QuadK D K) c) (t : U1 D K) : unitaryH D K H :=
  ⟨((Matrix.isUnit_iff_isUnit_det (transvMat D K H e c t)).2 (by
      rw [det_transvMat hc he]; exact (Unitary.toUnits t).isUnit)).unit,
    transvMat_unitary hH hc he t.2⟩

theorem det_unitaryTransvection {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) {e : Fin m → QuadK D K}
    {c : K} (hc : c ≠ 0) (he : star e ⬝ᵥ (H *ᵥ e) = algebraMap K (QuadK D K) c) (t : U1 D K) :
    (((unitaryTransvection hH hc he t : unitaryH D K H) : GL (Fin m) (QuadK D K)) :
      Matrix (Fin m) (Fin m) (QuadK D K)).det = t :=
  det_transvMat hc he t

/-- **$\det : U(V)(K)\to U(1)(K)$ is surjective** for every nondegenerate hermitian space of dimension $m\ge1$ (every
field $K\supseteq F$ of characteristic $0$, $E\otimes K$ split or not): $t = \det g_t$ for the unitary transvection $g_t$
along an anisotropic vector. Hence $1\to SU(V)(K)\to U(V)(K)\to U(1)(K)\to1$ is exact. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (det : U(V) → U(1) surjective; Ono's route)"]
theorem detU_surjective (hD : D ≠ 0) (hm : m ≠ 0) {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian)
    (hdet : H.det ≠ 0) : Function.Surjective (detU hH hdet) := by
  have hne : H ≠ 0 := by
    rintro rfl
    apply hdet
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  obtain ⟨e, c, hc, he⟩ := exists_anisotropic hD hH hne
  intro t
  exact ⟨unitaryTransvection hH hc he t, Subtype.ext (det_unitaryTransvection hH hc he t)⟩

end QuadFormsKB.Tamagawa.Unitary
