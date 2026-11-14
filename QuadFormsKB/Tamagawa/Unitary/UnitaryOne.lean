import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTauTwoUncond

/-!
# The unitary group in one variable: $U(1)\cong SO(E, N_{E/k})$ and $\tau(U(1)) = 2$

**Layer:** number fields. $F$ is any number field (the $k$ of the unitary-group literature), $D\in\mathcal O_F$ with
$-D$ not a square in $F$, and $E = F(\omega)$, $\omega^2 = -D$, a quadratic extension of $F$ given with the basis
$b = (1,\omega)$ (`hb0 : b 0 = 1`, `hb1 : b 1 * b 1 = -D`, the conventions of the binary torus files). Nothing is assumed
about the real places: $E/F$ may be a CM extension (Gan–Hanke–Yu's case, $F$ totally real and $D$ totally positive) or any other
quadratic extension.

**The group.** For a field $K\supseteq F$ of characteristic $0$, $E\otimes_FK = K[\omega]$ (`QuadK D K`, Mathlib's
`QuadraticAlgebra K (-D) 0`) with the conjugation $\overline{x+y\omega} = x - y\omega$ (Mathlib's `star`), and
$$U(1)(K) = \{t\in E\otimes_FK : t\bar t = 1\}$$
is Mathlib's `unitary (QuadK D K)` (`U1 D K`). This is the unitary group of every one-dimensional hermitian space
$\langle a\rangle$, $a\in F^\times$: $\bar t\,a\,t = a\iff t\bar t = 1$ (`mem_unitary_herm_one_iff`).

**Defines**
* `u1Mat D K t` $=\begin{pmatrix}x&-Dy\\y&x\end{pmatrix}$ for $t = x + y\omega$: the matrix of multiplication by $t$ on
  $E\otimes K = K\cdot1\oplus K\cdot\omega$;
* `u1ToSO D K` : $U(1)(K)\to SO(\langle1,D\rangle)(K)$, $t\mapsto$ `u1Mat D K t`, and the isomorphism `u1EquivSO D hD K`;
* `diagU1 D hD` : $U(1)(F)\to SO(\langle1,D\rangle)(\mathbb A)$ and `GammaU1 D hD`, its image;
* `muTamU1 D hD E` $=$ `muTamBin (diagForm1 D) _ E`: Weil's Tamagawa measure of $U(1)$, with the convergence factors
  $L_v(1,\chi_{E/F})$ and the global factor $L(1,\chi_{E/F})^{-1}$;
* `tauU1 D hD E`: the Tamagawa number $\mathrm{vol}(U(1)(F)\backslash U(1)(\mathbb A))$.

**Proves**
* `u1EquivSO`: the norm-one torus $U(1) = R^1_{E/F}\mathbb G_m$ and the special orthogonal group of the norm form
  $N_{E/F}(x + y\omega) = x^2 + Dy^2$ of $E$ are isomorphic on $K$-points for every field $K\supseteq F$ of characteristic
  $0$ (in particular at every place of $F$), by $t\mapsto$ (multiplication by $t$); the inverse is $g\mapsto g_{00} + g_{10}\omega$;
* `range_diagU1`: $U(1)(F)$ is the diagonal subgroup `GammaSOAdele` of $SO(\langle1,D\rangle)(\mathbb A)$;
* **`tauU1_eq_two`**: $\tau(U(1)) = 2$ for every quadratic extension $E = F(\sqrt{-D})$ of every number field $F$
  (unconditional; from `tauTwoBinaryAll_uncond`). This is Ono's value $\tau(R^1_{E/F}\mathbb G_m) = 2$ used by Gan–Hanke–Yu (4.3).

**Why $SO(\langle 1, D\rangle)(\mathbb A)$ is the adelic group of $U(1)$.** The adelic points of an affine algebraic group are
functorial in the group, and `u1EquivSO` is an isomorphism of algebraic groups over $F$ given by polynomials in both
directions ($t = x + y\omega\mapsto\begin{pmatrix}x&-Dy\\y&x\end{pmatrix}$, $g\mapsto g_{00} + g_{10}\omega$), integral over
$\mathcal O_F$. So $U(1)(F_v)\cong SO(\langle1,D\rangle)(F_v)$ at every place (`u1EquivSO` with $K = F_v$) and $U(1)(\mathbb A)$ is
the restricted product of these. An isomorphism of algebraic groups carries an invariant gauge form to an invariant gauge
form (up to a factor in $F^\times$, which does not change the Tamagawa measure by the product formula), so Weil's Tamagawa
measure of $U(1)$ with the convergence factors $L_v(1,\chi_{E/F})$ is `muTamBin`. Weil's measure and Ono's: Weil 1982,
§2.3, p. 21 and Ono 1963 (the measure $L(1,\chi)^{-1}\prod_vL_v(1,\chi)\,|\omega|_v$ for the norm-one torus) [both unverified].
-/

open MeasureTheory Matrix NumberField

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.HilbertModular QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

section Points

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- **The unitary group in one variable** $U(1)(K) = \{t\in E\otimes_FK : t\bar t = 1\}$, $E = F(\omega)$,
$\omega^2 = -D$ (Mathlib's `unitary` of the star ring $K[\omega]$, conjugation $\omega\mapsto-\omega$). It is the norm-one
torus $R^1_{E/F}\mathbb G_m$ and the unitary group of every one-dimensional hermitian space (`mem_unitary_herm_one_iff`). -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (U(1), the norm-one torus of L/k, via τ(U(V)) = 2)"]
abbrev U1 : Type _ := unitary (QuadK D K)

/-- $N(x + y\omega) = x^2 + Dy^2$. -/
theorem norm_quadK (t : QuadK D K) : t.norm = t.re ^ 2 + dIn D K * t.im ^ 2 := by
  have hd := dD_algebraMap D K
  rw [QuadraticAlgebra.norm_def]
  linear_combination (-(t.im * t.im)) * hd

/-- For $t\in U(1)(K)$, $x^2 + Dy^2 = 1$. -/
theorem re_sq_add (t : U1 D K) : (t : QuadK D K).re ^ 2 + dIn D K * (t : QuadK D K).im ^ 2 = 1 := by
  rw [← norm_quadK]; exact QuadraticAlgebra.norm_eq_one t.2

/-- **$U(\langle a\rangle) = U(1)$**: for $a\ne0$ in $K$ (e.g. $a\in F^\times$), $\bar t\,a\,t = a$ iff $t\in U(1)(K)$, i.e. the
unitary group of the one-dimensional hermitian space $\langle a\rangle$ does not depend on $a$. -/
theorem mem_unitary_herm_one_iff {a : K} (ha : a ≠ 0) (t : QuadK D K) :
    star t * algebraMap K (QuadK D K) a * t = algebraMap K (QuadK D K) a ↔ t ∈ unitary (QuadK D K) := by
  rw [← QuadraticAlgebra.norm_eq_one_iff_mem_unitary]
  have hc : star t * algebraMap K (QuadK D K) a * t = algebraMap K (QuadK D K) (a * t.norm) := by
    rw [map_mul, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    ring
  rw [hc, (algebraMap K (QuadK D K)).injective.eq_iff]
  constructor
  · intro h; exact mul_left_cancel₀ ha (h.trans (mul_one a).symm)
  · intro h; rw [h, mul_one]

/-- **The matrix of multiplication by $t = x + y\omega$** on $K[\omega] = K\oplus K\omega$:
$\begin{pmatrix}x&-Dy\\y&x\end{pmatrix}$ (the library's `rotMat` with determinant sign $1$), invertible for $t\in U(1)(K)$. -/
def u1Mat (t : U1 D K) : GL (Fin 2) K :=
  ⟨rotMat (dIn D K) (t : QuadK D K).re (t : QuadK D K).im 1,
    rotMatInv (dIn D K) (t : QuadK D K).re (t : QuadK D K).im 1,
    rotMat_mul_rotMatInv (re_sq_add D K t) (one_pow 2), rotMatInv_mul_rotMat (re_sq_add D K t) (one_pow 2)⟩

@[simp] theorem u1Mat_val (t : U1 D K) :
    (u1Mat D K t).val = rotMat (dIn D K) (t : QuadK D K).re (t : QuadK D K).im 1 := rfl

/-- **$U(1)\to SO(E, N_{E/F})$**: $t\mapsto$ multiplication by $t$, a rotation of the norm form $\langle1,D\rangle$. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (U(1) ≅ SO of the norm form of L/k)"]
def u1ToSO : U1 D K →* soSub (formF (diagForm1 D)) K where
  toFun t := ⟨⟨u1Mat D K t, (mem_orthGroup_diag_iff D).2 (rotMat_isometry (re_sq_add D K t) (one_pow 2))⟩,
    det_rotMat (re_sq_add D K t)⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    show rotMat (dIn D K) (1 : QuadK D K).re (1 : QuadK D K).im 1 = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' s t := by
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    show rotMat (dIn D K) ((s : QuadK D K) * t).re ((s : QuadK D K) * t).im 1 =
      rotMat (dIn D K) (s : QuadK D K).re (s : QuadK D K).im 1 * rotMat (dIn D K) (t : QuadK D K).re (t : QuadK D K).im 1
    have hd := dD_algebraMap D K
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hd] <;> ring

theorem u1ToSO_val (t : U1 D K) :
    (((u1ToSO D K t : soSub (formF (diagForm1 D)) K) : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val =
      rotMat (dIn D K) (t : QuadK D K).re (t : QuadK D K).im 1 := rfl

theorem u1ToSO_injective : Function.Injective (u1ToSO D K) := by
  intro s t h
  have h' := congrArg (fun g : soSub (formF (diagForm1 D)) K =>
    ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val) h
  simp only [u1ToSO_val] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 0
  simp [rotMat] at h0 h1
  exact Subtype.ext (QuadraticAlgebra.ext h0 h1)


/-- **Every rotation of $\langle1,D\rangle$ is multiplication by a norm-one element** ($D\ne0$): $g = $ `u1Mat` of
$g_{00} + g_{10}\omega$. -/
theorem u1ToSO_surjective {D : 𝓞 F} (hD : D ≠ 0) : Function.Surjective (u1ToSO D K) := by
  intro g
  have hg := (mem_orthGroup_diag_iff D).1 (g : orthGroup (formF (diagForm1 D)) K).2
  have hdet := mem_soSub.1 g.2
  obtain ⟨e1, e2, -⟩ := orth_eq_rotMat (two_ne_zero : (2 : K) ≠ 0) (dIn_ne_zero D hD K) hg
  set M := ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val
  let t : QuadK D K := ⟨M 0 0, M 1 0⟩
  have ht : t ∈ unitary (QuadK D K) := by
    rw [← QuadraticAlgebra.norm_eq_one_iff_mem_unitary, norm_quadK]; exact e2
  refine ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
  rw [u1ToSO_val]
  change rotMat (dIn D K) (M 0 0) (M 1 0) 1 = M
  rw [hdet] at e1
  exact e1.symm

/-- **$U(1)\cong SO(E, N_{E/F})$ on $K$-points** for every field $K\supseteq F$ of characteristic $0$ (every completion
$F_v$, $\mathbb R$, $\mathbb C$ and $F$ itself), $D\ne0$: the norm-one torus of $E/F$ acting on $E\otimes K$ by
multiplication is the special orthogonal group of the norm form $x^2 + Dy^2$. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (U(1) ≅ SO(L, N_{L/k}))"]
def u1EquivSO {D : 𝓞 F} (hD : D ≠ 0) : U1 D K ≃* soSub (formF (diagForm1 D)) K :=
  MulEquiv.ofBijective (u1ToSO D K) ⟨u1ToSO_injective D K, u1ToSO_surjective K hD⟩

@[simp] theorem u1EquivSO_apply {D : 𝓞 F} (hD : D ≠ 0) (t : U1 D K) : u1EquivSO K hD t = u1ToSO D K t := rfl

end Points

/-! ### The adelic group, the Tamagawa measure and $\tau(U(1)) = 2$ -/

section Adelic

variable {D}

/-- **$U(1)(F)$ in $U(1)(\mathbb A) = SO(\langle1,D\rangle)(\mathbb A)$**, diagonally: $t\mapsto$ (multiplication by $t$ at every
place). -/
def diagU1 (hD : D ≠ 0) : U1 D F →* SOAdele (diagForm1 D) :=
  (diagSOAdele (diagForm1 D)).comp (u1EquivSO F hD).toMonoidHom

/-- **$U(1)(F)$ as a subgroup of $U(1)(\mathbb A)$** (Weil 1982, §2.4: $G_k\subset G_{\mathbb A}$). -/
@[kb "weil1982" "§2.4, p. 23 (G_k ⊂ G_𝔸) [unverified]"]
def GammaU1 (hD : D ≠ 0) : Subgroup (SOAdele (diagForm1 D)) := (diagU1 hD).range

/-- $U(1)(F)$ is the diagonal $SO(\langle1,D\rangle)(F)$: `GammaU1 = GammaSOAdele`. -/
theorem range_diagU1 (hD : D ≠ 0) : GammaU1 hD = GammaSOAdele (diagForm1 D) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨t, rfl⟩ := (u1EquivSO F hD).surjective g
    exact ⟨t, rfl⟩

/-- **Weil's Tamagawa measure on $U(1)(\mathbb A)$** for $E/F$: `muTamBin` $= L(1,\chi_{E/F})^{-1}\,c_F\,\mu_\infty\times
\prod_v L_v(1,\chi_{E/F})\,\mu_v$ (the local measures of the norm form, the convergence factors
$\lambda_v^{-1} = L_v(1,\chi_{E/F})$ of the character group of $U(1)$, on which $\mathrm{Gal}(E/F)$ acts by $-1$). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure with convergence factors) [unverified]; ono1963 [unverified]"]
def muTamU1 (hD : D ≠ 0) (E : Type) [Field E] [NumberField E] [Algebra F E] : Measure (SOAdele (diagForm1 D)) :=
  muTamBin (diagForm1 D) (nondegenerate_diagForm1 hD) E

/-- **The Tamagawa number of $U(1)$**: $\tau(U(1)) = \mathrm{vol}(U(1)(F)\backslash U(1)(\mathbb A))$ for `muTamU1`. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)) [unverified]"]
def tauU1 (hD : D ≠ 0) (E : Type) [Field E] [NumberField E] [Algebra F E] : ENNReal :=
  covolume (GammaU1 hD) (SOAdele (diagForm1 D)) (muTamU1 hD E)

/-- **$\tau(U(1)) = 2$** for every quadratic extension $E = F(\omega)$, $\omega^2 = -D$, of every number field $F$
(complex places and every signature allowed): Ono's value for the norm-one torus $R^1_{E/F}\mathbb G_m$, one of the two
inputs of Gan–Hanke–Yu (4.3) on Ono's route ($\tau(U(V)) = \tau(U(1))\,\tau(SU(V))$). Unconditional, from
`tauTwoBinaryAll_uncond` through the isomorphism `u1EquivSO`. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (τ(U(1)) = 2, via Ono [O, p. 128])"]
theorem tauU1_eq_two (hD : D ≠ 0) (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) (E : Type) [Field E] [NumberField E]
    [Algebra F E] {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1) (hb1 : b 1 * b 1 = algebraMap F E (dD D)) :
    tauU1 hD E = 2 := by
  rw [tauU1, range_diagU1, muTamU1]
  exact tauTwoBinaryAll_uncond F (diagForm1 D) (nondegenerate_diagForm1 hD)
    ((anisotropicF_diagForm1_iff D).mpr hsq) E (isDiscField_of_basis hb0 hb1)

end Adelic

end QuadFormsKB.Tamagawa.Unitary
