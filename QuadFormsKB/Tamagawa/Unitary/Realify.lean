import QuadFormsKB.Tamagawa.Unitary.Group

/-!
# Realification: $U(V)\subseteq SO(V_F)$ for the trace form

**Layer:** as in `Group.lean`: $K\supseteq F$ a field of characteristic $0$, $E\otimes_FK = K[\omega]$, $\omega^2 = d = -D$.

The $m$-dimensional hermitian space $((E\otimes K)^m, h)$, $h(x,y) = y^*Hx$, is a $2m$-dimensional $K$-space, and
$q(x) = h(x,x)\in K$ is a quadratic form on it (the *trace form*, $\mathrm{Tr}_{E/F}h(x,y) = 2\,\mathrm{Re}\,h(x,y)$ its
polar form). A unitary $g$ is $K$-linear, commutes with multiplication by $\omega$ and preserves $q$. This file makes the
coordinates explicit (`Fin m × Fin 2`, the pair $(a, i)$ = coordinate $i$ of $x_a$ in the basis $(1,\omega)$).

**Defines**
* `rot D K z` $=\begin{pmatrix}x&dy\\y&x\end{pmatrix}$, the matrix of multiplication by $z = x + y\omega$ (a ring hom);
* `realify D K M` $\in M_{m\times2}(K)$: the block matrix $(\mathrm{rot}\,M_{ab})_{a,b}$ (Mathlib's `Matrix.comp`), a ring hom;
* `gramBlk D K` = the block diagonal matrix $\mathrm{diag}(G,\dots,G)$, $G = \mathrm{diag}(1, D)$: $\mathrm{Re}(\bar wz) = w^{\mathsf T}Gz$
  in coordinates;
* `traceGram D K H` $= G_{\mathrm{blk}}\,\mathrm{realify}(H)$, the Gram matrix of $q$ (symmetric for hermitian $H$).

**Proves**
* `det_rot`: $\det\mathrm{rot}(z) = N(z)$; `det_realify`: $\det\mathrm{realify}(M) = N(\det M)$ (Mathlib's `Matrix.det_det`);
* `rot_star`: $\mathrm{rot}(z)^{\mathsf T}G = G\,\mathrm{rot}(\bar z)$; `realify_conjTranspose`:
  $\mathrm{realify}(M)^{\mathsf T}G_{\mathrm{blk}} = G_{\mathrm{blk}}\,\mathrm{realify}(M^*)$;
* `realify_isometry`: for $g\in U(V)(K)$, $\mathrm{realify}(g)^{\mathsf T}\,S\,\mathrm{realify}(g) = S$ ($S$ = `traceGram`) and
  `det_realify_unitary`: $\det\mathrm{realify}(g) = 1$. So $U(V)(K)\subseteq SO(V_K, q)$.
-/

open Matrix
open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] (D : NumberField.RingOfIntegers F)
variable (K : Type*) [Field K] [Algebra F K] [CharZero K] {m : ℕ}

local notation "dK" => algebraMap F K (dD D)

/-- **The regular representation** $z = x + y\omega\mapsto\begin{pmatrix}x&dy\\y&x\end{pmatrix}$ of $K[\omega]$ on the basis
$(1,\omega)$. -/
def rot : QuadK D K →+* Matrix (Fin 2) (Fin 2) K where
  toFun z := !![z.re, dK * z.im; z.im, z.re]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' z w := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem rot_apply (z : QuadK D K) : rot D K z = !![z.re, dK * z.im; z.im, z.re] := rfl

theorem det_rot (z : QuadK D K) : (rot D K z).det = z.norm := by
  rw [rot_apply, det_fin_two_of, QuadraticAlgebra.norm_def]; ring

/-- $G = \mathrm{diag}(1, -d) = \mathrm{diag}(1, D)$: $\mathrm{Re}(\bar wz) = w^{\mathsf T}Gz$ in the coordinates $(\mathrm{re},\mathrm{im})$. -/
def gram2 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -dK]

/-- $\mathrm{rot}(z)^{\mathsf T}G = G\,\mathrm{rot}(\bar z)$. -/
theorem rot_transpose_mul_gram2 (z : QuadK D K) : (rot D K z)ᵀ * gram2 D K = gram2 D K * rot D K (star z) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot_apply, gram2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Realification** of an $m\times m$ matrix over $K[\omega]$: the $(m\times2)$-block matrix $(\mathrm{rot}\,M_{ab})$. -/
def realify : Matrix (Fin m) (Fin m) (QuadK D K) →+* Matrix (Fin m × Fin 2) (Fin m × Fin 2) K :=
  (Matrix.compRingEquiv (Fin m) (Fin 2) K).toRingHom.comp (rot D K).mapMatrix

theorem realify_apply (M : Matrix (Fin m) (Fin m) (QuadK D K)) (a b : Fin m) (i j : Fin 2) :
    realify D K M (a, i) (b, j) = rot D K (M a b) i j := rfl

/-- **$\det\mathrm{realify}(M) = N(\det M)$** (Mathlib's `Matrix.det_det`: blocks in the commutative ring $\mathrm{rot}(K[\omega])$). -/
theorem det_realify (M : Matrix (Fin m) (Fin m) (QuadK D K)) : (realify D K M).det = (M.det).norm := by
  rw [← det_rot, Matrix.det_det]
  rfl

/-- The block-diagonal Gram matrix $G_{\mathrm{blk}} = (\delta_{ab}G)_{a,b}$ of $\mathrm{Re}(y^*x)$. -/
def gramBlk : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K :=
  Matrix.comp (Fin m) (Fin m) (Fin 2) (Fin 2) K (Matrix.diagonal fun _ => gram2 D K)

theorem gramBlk_apply (a b : Fin m) (i j : Fin 2) :
    gramBlk D K (a, i) (b, j) = if a = b then gram2 D K i j else 0 := by
  simp only [gramBlk, Matrix.comp_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- **$\mathrm{realify}(M)^{\mathsf T}G_{\mathrm{blk}} = G_{\mathrm{blk}}\,\mathrm{realify}(M^*)$**: the realification of the
conjugate transpose is the adjoint for $\mathrm{Re}(y^*x)$. -/
theorem realify_transpose_mul_gramBlk (M : Matrix (Fin m) (Fin m) (QuadK D K)) :
    (realify D K M)ᵀ * gramBlk D K = gramBlk D K * realify D K Mᴴ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, gramBlk_apply, realify_apply,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply]
  have := congrFun (congrFun (rot_transpose_mul_gram2 D K (M b a)) i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using this

/-- **The Gram matrix of the trace form** $q(x) = h(x,x) = \mathrm{Re}(x^*Hx)$: $S = G_{\mathrm{blk}}\,\mathrm{realify}(H)$, so
$q(x) = x^{\mathsf T}Sx$ in the coordinates `Fin m × Fin 2`. -/
def traceGram (H : Matrix (Fin m) (Fin m) (QuadK D K)) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K :=
  gramBlk D K * realify D K H

/-- **Unitary matrices are isometries of the trace form**: $\mathrm{realify}(g)^{\mathsf T}S\,\mathrm{realify}(g) = S$. -/
theorem realify_isometry {H : Matrix (Fin m) (Fin m) (QuadK D K)} {g : GL (Fin m) (QuadK D K)}
    (hg : g ∈ unitaryH D K H) :
    (realify D K (g : Matrix (Fin m) (Fin m) (QuadK D K)))ᵀ * traceGram D K H * realify D K g = traceGram D K H := by
  rw [traceGram, ← Matrix.mul_assoc, realify_transpose_mul_gramBlk, Matrix.mul_assoc, Matrix.mul_assoc, ← map_mul,
    ← map_mul, ← Matrix.mul_assoc, (mem_unitaryH D K).1 hg]

/-- **Unitary matrices have determinant $1$ as $K$-linear maps**: $\det\mathrm{realify}(g) = N(\det g) = 1$. -/
theorem det_realify_unitary {H : Matrix (Fin m) (Fin m) (QuadK D K)} (hH : H.IsHermitian) (hdet : H.det ≠ 0)
    {g : GL (Fin m) (QuadK D K)} (hg : g ∈ unitaryH D K H) :
    (realify D K (g : Matrix (Fin m) (Fin m) (QuadK D K))).det = 1 := by
  rw [det_realify]
  exact QuadraticAlgebra.norm_eq_one (det_mem_unitary hH hdet hg)

end QuadFormsKB.Tamagawa.Unitary
