import QuadFormsKB.Tamagawa.Unitary.Realify

/-!
# The integral trace form and $U(V)$ as the commutant of $\omega$ in $O(V_F, q)$

**Layer:** $F$ a number field, $D\in\mathcal O_F$, $E = F(\omega)$, $\omega^2 = -D$ (as in `Group.lean`). The *integral* hermitian
data are a matrix $H_0$ over the order $\mathcal O_F[\omega]$ = `QuadO D` (Mathlib's `QuadraticAlgebra (𝓞 F) (-D) 0`), hermitian
($H_0^* = H_0$). Its image $H$ = `HK D K H₀` over $E\otimes_FK = K[\omega]$ (`QuadK D K`) is the matrix of the hermitian space
$V_K = ((E\otimes K)^m, h)$, $h(x, y) = y^*Hx$, of `Group.lean`, and $\Lambda = \mathcal O_F[\omega]^m$ is the lattice of $H_0$.

**Defines**
* `toQuadK D K` : $\mathcal O_F[\omega]\to K[\omega]$, the base change (a ring hom); `HK D K H₀` $= H_0$ over $K[\omega]$;
* `blkO D z` $=\begin{pmatrix}x&-Dy\\Dy&Dx\end{pmatrix}$ for $z = x+y\omega$ (the matrix of $(w, z')\mapsto\mathrm{Re}(\bar w z z')$ in the
  basis $(1,\omega)$), and `traceS D H₀` $=(\mathrm{blkO}(H_{0,ab}))_{a,b}$ over $\mathcal O_F$, indexed by `Fin m × Fin 2`;
* **`traceQF D H₀`**: the **trace form** $q(x) = h(x, x) = x^{\mathsf T}S x$ as a quadratic form over $\mathcal O_F$ in $2m$
  variables (the library's `QuadForm (𝓞 F) (m * 2)`; coordinates reindexed by Mathlib's `finProdFinEquiv`). The lattice
  $\mathcal O_F^{2m}$ of `traceQF` is $\Lambda$ in the coordinates $(a, i)$ = coefficient of $\omega^i$ in $x_a$;
* `omegaO D m`: the matrix of multiplication by $\omega$ on $\mathcal O_F[\omega]^m$ (block diagonal
  $\begin{pmatrix}0&-D\\1&0\end{pmatrix}$), and `omegaR D m R` its image over an $F$-algebra $R$;
* **`unitaryOrth D H₀ R`** $=\{g\in O(V_F, q)(R) : g\,\omega = \omega\,g\}$, the unitary group $U(V)(R)$ for **every**
  commutative $F$-algebra $R$ (e.g. $F_v$, $\mathbb R$, $\mathbb C$, the adeles), as a subgroup of the library's `orthGroup`.

**Proves**
* `traceS_map`: $S$ over $K$ is `Realify.traceGram` of $H$; `traceS_transpose` ($S$ is symmetric for hermitian $H_0$);
  `hessian_traceQF`: the Hessian of $q$ is $S + S^{\mathsf T}$ (reindexed).

For a field $K\supseteq F$ of characteristic $0$ the comparison $U(V)(K) = $ `unitaryH D K (HK D K H₀)` $\cong$
`unitaryOrth D H₀ K` is `UnitaryOrth.lean`.

*Why this presentation.* It makes $U(V)$ a closed subgroup of the library's orthogonal groups at every place
($O(V)(F_v)$ with its topology, `Measure/LocalSO.lean`; the restricted product `OAf`; $SO(V)(\mathbb A)$ = `SOAdele`), so the
topology, the compact open lattice stabilizers and Haar measures of the orthogonal case apply to $U(V)$ without a second construction.
For $m = 1$, $H_0 = (1)$ the trace form is $x_0^2 + Dx_1^2$ = `diagForm1 D`, the form through which `UnitaryOne.lean`
realizes $U(1)$.
-/

open Matrix
open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Tamagawa.Measure.Weil NumberField QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)
variable (K : Type*) [Field K] [Algebra F K] [CharZero K] {m : ℕ}

/-- **The order $\mathcal O_F[\omega]$**, $\omega^2 = -D$ (Mathlib's `QuadraticAlgebra (𝓞 F) (-D) 0`, with its conjugation
$\omega\mapsto-\omega$ as `star`). For $-D$ not a square it is an order of $E = F(\omega)$, maximal when $-D$ generates the
relative discriminant. -/
abbrev QuadO : Type := QuadraticAlgebra (𝓞 F) (-D) 0

local notation "ι" => fun x : 𝓞 F => algebraMap F K (algebraMap (𝓞 F) F x)

/-- **Base change** $\mathcal O_F[\omega]\to K[\omega] = E\otimes_FK$, $x + y\omega\mapsto x + y\omega$. -/
def toQuadK : QuadO D →+* QuadK D K where
  toFun z := ⟨ι z.re, ι z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp [dD] <;> ring
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem toQuadK_re (z : QuadO D) : (toQuadK D K z).re = ι z.re := rfl
@[simp] theorem toQuadK_im (z : QuadO D) : (toQuadK D K z).im = ι z.im := rfl

theorem toQuadK_star (z : QuadO D) : toQuadK D K (star z) = star (toQuadK D K z) := by
  ext <;> simp

/-- **The hermitian matrix over $E\otimes_FK$** of the integral hermitian matrix $H_0$. -/
def HK (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) : Matrix (Fin m) (Fin m) (QuadK D K) := H₀.map (toQuadK D K)

theorem HK_isHermitian {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) : (HK D K H₀).IsHermitian := by
  refine Matrix.ext fun a b => ?_
  simp only [HK, conjTranspose_apply, map_apply, ← toQuadK_star]
  rw [← conjTranspose_apply, hH.eq]

/-- **The $2\times2$ block of the trace form**: for $z = x + y\omega$, $\mathrm{Re}(\bar w\,z\,z') = w^{\mathsf T}\,\mathrm{blkO}(z)\,z'$ in the
coordinates $(\mathrm{re}, \mathrm{im})$: $\mathrm{blkO}(z) = \mathrm{diag}(1, D)\,\mathrm{rot}(z) =
\begin{pmatrix}x&-Dy\\Dy&Dx\end{pmatrix}$. -/
def blkO (z : QuadO D) : Matrix (Fin 2) (Fin 2) (𝓞 F) := !![z.re, -D * z.im; D * z.im, D * z.re]

/-- **The Gram matrix of the trace form** $q(x) = h(x,x)$ over $\mathcal O_F$, in the coordinates `Fin m × Fin 2`. -/
def traceS (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) (𝓞 F) :=
  Matrix.of fun p q => blkO D (H₀ p.1 q.1) p.2 q.2

/-- $S$ over $K$ is the Gram matrix `traceGram` of `Realify.lean`. -/
theorem traceS_map (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) :
    (traceS D H₀).map ι = traceGram D K (HK D K H₀) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [traceGram, map_apply, mul_apply, Fintype.sum_prod_type, gramBlk_apply, realify_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  fin_cases i <;> fin_cases j <;>
    simp [traceS, blkO, rot_apply, gram2, Fin.sum_univ_two, HK, dD]

/-- **$S$ is symmetric** for hermitian $H_0$. -/
theorem traceS_transpose {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    (traceS D H₀)ᵀ = traceS D H₀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  have h := congrFun (congrFun hH.eq a) b
  rw [conjTranspose_apply] at h
  simp only [transpose_apply, traceS, of_apply]
  rw [← h]
  fin_cases i <;> fin_cases j <;> simp [blkO] <;> ring

/-- The reindexing `Fin m × Fin 2 ≃ Fin (m * 2)` (Mathlib's `finProdFinEquiv`). -/
abbrev eCoord (m : ℕ) : Fin m × Fin 2 ≃ Fin (m * 2) := finProdFinEquiv

/-- **The trace form** $q(x) = h(x,x) = x^{\mathsf T}Sx$ as a quadratic form over $\mathcal O_F$ in $2m$ variables:
coefficients $c_{ii} = S_{ii}$, $c_{ij} = S_{ij} + S_{ji}$ ($i<j$), after reindexing by `eCoord`. -/
@[kb "ganhankeyu2001" "§3, p. 105 (the hermitian space V); weil1982 §2.3 (restriction of scalars) [unverified]"]
def traceQF (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) : QuadForm (𝓞 F) (m * 2) :=
  QuadForm.ofUpper fun i j =>
    if i = j then reindex (eCoord m) (eCoord m) (traceS D H₀) i i
    else reindex (eCoord m) (eCoord m) (traceS D H₀) i j + reindex (eCoord m) (eCoord m) (traceS D H₀) j i

/-- The Hessian of the trace form is $S + S^{\mathsf T}$ (reindexed). -/
theorem hessian_traceQF (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) :
    (traceQF D H₀).hessian =
      reindex (eCoord m) (eCoord m) (traceS D H₀) + (reindex (eCoord m) (eCoord m) (traceS D H₀))ᵀ := by
  ext i j
  simp only [traceQF, QuadForm.ofUpper, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.mpr h, h.ne]
  · simp
  · simp [h.le, not_le.mpr h, h.ne, h.ne', add_comm]

/-- **Multiplication by $\omega$** on $\mathcal O_F[\omega]^m$ in the coordinates `Fin m × Fin 2`: block diagonal
$\begin{pmatrix}0&-D\\1&0\end{pmatrix}$ ($\omega\cdot(x + y\omega) = -Dy + x\omega$). -/
def omegaO (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) (𝓞 F) :=
  Matrix.of fun p q => if p.1 = q.1 then !![0, -D; 1, 0] p.2 q.2 else 0

/-- `omegaO` over an $F$-algebra $R$, reindexed to `Fin (m * 2)`. -/
def omegaR (m : ℕ) (R : Type*) [CommRing R] [Algebra F R] : Matrix (Fin (m * 2)) (Fin (m * 2)) R :=
  (reindex (eCoord m) (eCoord m) (omegaO D m)).map fun x => algebraMap F R (algebraMap (𝓞 F) F x)

/-- The trace form over $F$. -/
abbrev traceQFF (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) : QuadForm F (m * 2) :=
  (traceQF D H₀).map (algebraMap (𝓞 F) F)

/-- **The unitary group $U(V)(R)$** of the hermitian space $(E^m, H_0)$ over a commutative $F$-algebra $R$, realized inside
the orthogonal group of the trace form: $\{g\in O(V_F, q)(R) : g\,\omega = \omega\,g\}$ ($E\otimes_FR$-linear isometries of
$q$; for a field $R = K$ this is `unitaryH D K (HK D K H₀)`, `UnitaryOrth.lean`). -/
@[kb "ganhankeyu2001" "§3, p. 105; §4, p. 109 (G = U(V), the unitary group)"]
def unitaryOrth (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (R : Type*) [CommRing R] [Algebra F R] :
    Subgroup (orthGroup (traceQFF D H₀) R) where
  carrier := {g | (g : GL (Fin (m * 2)) R).val * omegaR D m R = omegaR D m R * (g : GL (Fin (m * 2)) R).val}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul] at ha hb ⊢
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
    set g : GL (Fin (m * 2)) R := (a : GL (Fin (m * 2)) R)
    calc (g⁻¹ : GL (Fin (m * 2)) R).val * omegaR D m R
        = (g⁻¹ : GL _ R).val * (omegaR D m R * g.val) * (g⁻¹ : GL _ R).val := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (g⁻¹ : GL _ R).val * (g.val * omegaR D m R) * (g⁻¹ : GL _ R).val := by rw [ha]
      _ = omegaR D m R * (g⁻¹ : GL _ R).val := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem mem_unitaryOrth {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} {R : Type*} [CommRing R] [Algebra F R]
    {g : orthGroup (traceQFF D H₀) R} :
    g ∈ unitaryOrth D H₀ R ↔
      (g : GL (Fin (m * 2)) R).val * omegaR D m R = omegaR D m R * (g : GL (Fin (m * 2)) R).val := Iff.rfl

end QuadFormsKB.Tamagawa.Unitary
