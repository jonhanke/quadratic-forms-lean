import QuadFormsKB.Tamagawa.BinaryNormOne
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusBase
import QuadFormsKB.Tamagawa.Measure.Weil.PDLocal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO

/-!
# The norm-one torus of a binary form, locally: Hilbert 90 and integral lifts
**Layer:** number fields. $F$ is a number field, $D\in\mathcal O_F$, $Q_0 = \langle1,D\rangle = x_0^2 + Dx_1^2$ = `diagForm1 D`,
$d = -D$ = `dD D`, and $K$ is a field (of characteristic $0$) with a ring homomorphism $\rho : F\to K$: $K$ is $\mathbb R$ or
$\mathbb C$ with an embedding $\rho$ of $F$ (archimedean places), or the completion $F_v$ (finite places). The
quadratic algebra is $K[\omega] = K\oplus K\omega$ with $\omega^2 = \rho(d)$ (`QuadraticAlgebra K (ρ d) 0`; coordinates
`re` $=$ coefficient of $\omega^0$, `im` $=$ coefficient of $\omega^1$, i.e. the basis $(1,\omega) = (b_0,b_1)$).

**The mathematics.** For a unit $z = x + y\omega$ of $K[\omega]$ with norm $N(z) = z\bar z = x^2 - \rho(d)y^2 = x^2 + \rho(D)y^2$ put
$$u(z) = z/\bar z = z^2N(z)^{-1} = p(z) + q(z)\omega,\quad p(z) = \frac{x^2 + \rho(d)y^2}{N(z)},\quad q(z) = \frac{2xy}{N(z)},$$
an element of norm $1$: $p^2 + \rho(D)q^2 = 1$. The matrix of multiplication by $u(z)$ in the basis $(1,\omega)$ is
$\begin{pmatrix}p&-\rho(D)q\\q&p\end{pmatrix}$, an element of $SO(\langle1,D\rangle)(K)$ (`BinaryNormOne.rotMat`).

**Defines**
* generic algebra over a field $K$ and $d, D_K\in K$ with $d = -D_K$: `torP`, `torQ`, `normOneG` ($u$), `torGLK`,
  `torGLHom` ($z\mapsto$ the matrix of $u(z)$, a homomorphism $K[\omega]^\times\to\mathrm{GL}_2(K)$);
* over an $F$-algebra field $K$: `normOneOf` ($u(z)$), `torOrthK`, **`torSOK`** $: K[\omega]^\times\to SO(\langle1,D\rangle)(K)$;
* over a real or complex embedding $\rho$ of $F$: **`torSOReal`** into `soReal`, **`torSOC`** into `soC` (the groups of the
  archimedean factors `ArchSO`, `ArchSOC` of `GInfSO`).

**Proves**
* `normOneOf_norm` ($N(u(z)) = 1$) and `normOneOf_eq_one_iff` ($u(z) = 1\iff\mathrm{im}\,z = 0$);
* **`torSOK_surjective`**, `torSOReal_surjective`, `torSOC_surjective` (Hilbert 90: $K[\omega]^\times\to SO(\langle1,D\rangle)(K)$
  is onto; the lift of $u = p + q\omega$ is $z = 1 + u$ if $1 + p\ne0$, else $z = \omega(1-u)$, `exists_unit_torP_torQ`);
* **`torSOK_eq_one_iff`** (and the real and complex versions): the kernel is $K^\times$, i.e. $\mathrm{im}\,z = 0$;
* **`exists_integral_lift`**: at a finite place $v$ with $|2|_v = |D|_v = 1$, every $g\in SO(\langle1,D\rangle)(F_v)$ that
  stabilizes $\mathfrak o_v^2$ is $\mathrm{tor}(z)$ with $z$ and $z^{-1}$ having integral coordinates (one of $1\pm p$ is a unit
  because $(1+p) + (1-p) = 2$ is); conversely **`torOrthK_mem_stdStab`**: such a $z$ gives an element of $O(\mathfrak o_v^2)$.

Source: Weil 1982, §2.4 (the group $G = R_{E/F}\mathbb G_m/\mathbb G_m\cong SO_2$, Hilbert 90) [unverified locator]; Ono 1963
(Tamagawa numbers of tori) [unverified].
-/

open NumberField Matrix IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

section Generic

variable {K : Type*} [Field K] {d : K}

/-- $p(z) = \mathrm{re}\,u(z) = (x^2 + dy^2)/N(z)$ for $z = x + y\omega$ ($x$ = `re`, $y$ = `im`, $N(z) = x^2 - dy^2$,
$\omega^2 = d$). -/
def torP (z : QuadraticAlgebra K d 0) : K := (z.re * z.re + d * z.im * z.im) / z.norm

/-- $q(z) = \mathrm{im}\,u(z) = 2xy/N(z)$ for $z = x + y\omega$. -/
def torQ (z : QuadraticAlgebra K d 0) : K := 2 * z.re * z.im / z.norm

/-- $u(z) = z/\bar z = p(z) + q(z)\omega = N(z)^{-1}z^2$ (`normOneG_eq`), the norm-one element attached to $z$
(an unconditional definition: $N(z)^{-1} = 0$ if $N(z) = 0$). -/
def normOneG (z : QuadraticAlgebra K d 0) : QuadraticAlgebra K d 0 := ⟨torP z, torQ z⟩

theorem norm_eq (z : QuadraticAlgebra K d 0) : z.norm = z.re * z.re - d * z.im * z.im := by
  simp [QuadraticAlgebra.norm_def]

theorem normOneG_eq (z : QuadraticAlgebra K d 0) : normOneG z = z.norm⁻¹ • (z * z) := by
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [normOneG, torP, QuadraticAlgebra.re_smul, QuadraticAlgebra.re_mul, smul_eq_mul, div_eq_inv_mul]
  · simp only [normOneG, torQ, QuadraticAlgebra.im_smul, QuadraticAlgebra.im_mul, smul_eq_mul, div_eq_inv_mul]
    ring

theorem normOneG_mul (z w : QuadraticAlgebra K d 0) : normOneG (z * w) = normOneG z * normOneG w := by
  simp only [normOneG_eq, map_mul, mul_inv]
  rw [smul_mul_smul_comm]
  congr 1
  ring

theorem torP_mul (z w : QuadraticAlgebra K d 0) : torP (z * w) = torP z * torP w + d * torQ z * torQ w := by
  have := congrArg QuadraticAlgebra.re (normOneG_mul z w)
  simpa [normOneG] using this

theorem torQ_mul (z w : QuadraticAlgebra K d 0) : torQ (z * w) = torP z * torQ w + torQ z * torP w := by
  have := congrArg QuadraticAlgebra.im (normOneG_mul z w)
  simpa [normOneG] using this

@[simp] theorem torP_one : torP (1 : QuadraticAlgebra K d 0) = 1 := by
  simp [torP, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[simp] theorem torQ_one : torQ (1 : QuadraticAlgebra K d 0) = 0 := by
  simp [torQ, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem torP_sq_sub {z : QuadraticAlgebra K d 0} (hz : z.norm ≠ 0) : torP z ^ 2 - d * torQ z ^ 2 = 1 := by
  rw [torP, torQ, div_pow, div_pow, mul_div_assoc', ← sub_div, div_eq_one_iff_eq (pow_ne_zero 2 hz), sq (z.norm),
    norm_eq]
  ring

theorem torP_sq_add {Dk : K} (hd : d = -Dk) {z : QuadraticAlgebra K d 0} (hz : z.norm ≠ 0) :
    torP z ^ 2 + Dk * torQ z ^ 2 = 1 := by
  have := torP_sq_sub hz
  linear_combination this + (torQ z ^ 2) * hd

theorem norm_normOneG {z : QuadraticAlgebra K d 0} (hz : z.norm ≠ 0) : (normOneG z).norm = 1 := by
  have := torP_sq_sub hz
  rw [norm_eq]
  show torP z * torP z - d * torQ z * torQ z = 1
  linear_combination this

theorem norm_ne_zero_of_unit (z : (QuadraticAlgebra K d 0)ˣ) : (z : QuadraticAlgebra K d 0).norm ≠ 0 :=
  (QuadraticAlgebra.isUnit_iff_norm_isUnit.1 z.isUnit).ne_zero

theorem coe_inv_unit (z : (QuadraticAlgebra K d 0)ˣ) :
    ((z⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0) = (z : QuadraticAlgebra K d 0).norm⁻¹ • star (z : QuadraticAlgebra K d 0) := by
  have hz := norm_ne_zero_of_unit z
  rw [norm_eq] at hz
  refine Units.inv_eq_of_mul_eq_one_right ?_
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, smul_eq_mul, norm_eq, QuadraticAlgebra.re_one]
    linear_combination (inv_mul_cancel₀ hz)
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, smul_eq_mul, norm_eq, QuadraticAlgebra.im_one]
    ring

theorem norm_coe_inv (z : (QuadraticAlgebra K d 0)ˣ) :
    ((z⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).norm = (z : QuadraticAlgebra K d 0).norm⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]

/-- $p(z) = (x^2 + dy^2)\,N(z^{-1})$: a polynomial in the coordinates of $z$ and $z^{-1}$ (used for continuity). -/
theorem torP_eq_mul_norm_inv (z : (QuadraticAlgebra K d 0)ˣ) :
    torP (z : QuadraticAlgebra K d 0) =
      ((z : QuadraticAlgebra K d 0).re * (z : QuadraticAlgebra K d 0).re +
        d * (z : QuadraticAlgebra K d 0).im * (z : QuadraticAlgebra K d 0).im) *
        ((z⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).norm := by
  rw [norm_coe_inv, torP, div_eq_mul_inv]

/-- $q(z) = 2xy\,N(z^{-1})$. -/
theorem torQ_eq_mul_norm_inv (z : (QuadraticAlgebra K d 0)ˣ) :
    torQ (z : QuadraticAlgebra K d 0) =
      2 * (z : QuadraticAlgebra K d 0).re * (z : QuadraticAlgebra K d 0).im *
        ((z⁻¹ : (QuadraticAlgebra K d 0)ˣ) : QuadraticAlgebra K d 0).norm := by
  rw [norm_coe_inv, torQ, div_eq_mul_inv]

/-- $p$ commutes with ring homomorphisms. -/
theorem torP_map {L : Type*} [Field L] (f : K →+* L) {d' : L} (h : f d = d') (z : QuadraticAlgebra K d 0)
    (z' : QuadraticAlgebra L d' 0) (hx : z'.re = f z.re) (hy : z'.im = f z.im) : torP z' = f (torP z) := by
  rw [torP, torP, map_div₀, norm_eq, norm_eq, hx, hy, ← h]
  simp

/-- $q$ commutes with ring homomorphisms. -/
theorem torQ_map {L : Type*} [Field L] (f : K →+* L) {d' : L} (h : f d = d') (z : QuadraticAlgebra K d 0)
    (z' : QuadraticAlgebra L d' 0) (hx : z'.re = f z.re) (hy : z'.im = f z.im) : torQ z' = f (torQ z) := by
  rw [torQ, torQ, map_div₀, norm_eq, norm_eq, hx, hy, ← h]
  simp
  rw [map_ofNat]

end Generic

section GLPart

variable {K : Type*} [Field K] {d Dk : K} (hd : d = -Dk)

include hd in
theorem torPQ (z : (QuadraticAlgebra K d 0)ˣ) :
    torP (z : QuadraticAlgebra K d 0) ^ 2 + Dk * torQ (z : QuadraticAlgebra K d 0) ^ 2 = 1 :=
  torP_sq_add hd (norm_ne_zero_of_unit z)

/-- The matrix of multiplication by $u(z) = z/\bar z$ in the basis $(1, \omega)$, as an element of $\mathrm{GL}_2$. -/
def torGLK (z : (QuadraticAlgebra K d 0)ˣ) : GL (Fin 2) K :=
  ⟨rotMat Dk (torP (z : QuadraticAlgebra K d 0)) (torQ (z : QuadraticAlgebra K d 0)) 1,
    rotMatInv Dk (torP (z : QuadraticAlgebra K d 0)) (torQ (z : QuadraticAlgebra K d 0)) 1,
    rotMat_mul_rotMatInv (torPQ hd z) (one_pow 2), rotMatInv_mul_rotMat (torPQ hd z) (one_pow 2)⟩

@[simp] theorem torGLK_val (z : (QuadraticAlgebra K d 0)ˣ) :
    (torGLK hd z).val = rotMat Dk (torP (z : QuadraticAlgebra K d 0)) (torQ (z : QuadraticAlgebra K d 0)) 1 := rfl

@[simp] theorem torGLK_inv_val (z : (QuadraticAlgebra K d 0)ˣ) :
    (torGLK hd z)⁻¹.val = rotMatInv Dk (torP (z : QuadraticAlgebra K d 0)) (torQ (z : QuadraticAlgebra K d 0)) 1 := rfl

/-- $z\mapsto$ the matrix of $u(z)$: a homomorphism. -/
def torGLHom : (QuadraticAlgebra K d 0)ˣ →* GL (Fin 2) K where
  toFun := torGLK hd
  map_one' := by
    refine Units.ext ?_
    show rotMat Dk (torP (1 : QuadraticAlgebra K d 0)) (torQ (1 : QuadraticAlgebra K d 0)) 1 = 1
    rw [torP_one, torQ_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
  map_mul' z w := by
    refine Units.ext ?_
    show rotMat Dk (torP ((z : QuadraticAlgebra K d 0) * (w : QuadraticAlgebra K d 0))) (torQ ((z : QuadraticAlgebra K d 0) * (w : QuadraticAlgebra K d 0))) 1 = _
    rw [torP_mul, torQ_mul]
    subst hd
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem torGLHom_apply (z : (QuadraticAlgebra K d 0)ˣ) : torGLHom hd z = torGLK hd z := rfl

theorem torGLK_isometry (z : (QuadraticAlgebra K d 0)ˣ) :
    (torGLK hd z).valᵀ * hessD Dk * (torGLK hd z).val = hessD Dk :=
  rotMat_isometry (torPQ hd z) (one_pow 2)

theorem det_torGLK (z : (QuadraticAlgebra K d 0)ˣ) : (torGLK hd z).val.det = 1 :=
  det_rotMat (torPQ hd z)

variable [CharZero K]

/-- $p(z) = 1$ and $q(z) = 0$ iff $z$ is a scalar ($\mathrm{im}\,z = 0$). -/
theorem torP_eq_one_torQ_eq_zero_iff {z : QuadraticAlgebra K d 0} (hz : z.norm ≠ 0) :
    (torP z = 1 ∧ torQ z = 0) ↔ z.im = 0 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  constructor
  · rintro ⟨hp, hq⟩
    rw [torP, div_eq_one_iff_eq hz, norm_eq] at hp
    rw [torQ, div_eq_zero_iff] at hq
    by_contra hy
    rcases hq with hq | hq
    · have hxy : z.re = 0 := by
        rcases mul_eq_zero.1 hq with h1 | h1
        · rcases mul_eq_zero.1 h1 with h3 | h3
          · exact absurd h3 h2
          · exact h3
        · exact absurd h1 hy
      have hd0 : d = 0 := by
        have : d * z.im ^ 2 = 0 := by
          rw [hxy] at hp
          linear_combination (1 / 2 : K) * hp
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h1
        · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.1 h1) hy
      apply hz
      rw [norm_eq, hxy]
      linear_combination (-(z.im * z.im)) * hd0
    · exact hz hq
  · intro hy
    have hz' := hz
    rw [norm_eq, hy] at hz'
    refine ⟨?_, ?_⟩
    · rw [torP, hy, div_eq_one_iff_eq hz, norm_eq, hy]; ring
    · rw [torQ, hy]; simp

theorem normOneG_eq_one_iff {z : QuadraticAlgebra K d 0} (hz : z.norm ≠ 0) : normOneG z = 1 ↔ z.im = 0 := by
  rw [← torP_eq_one_torQ_eq_zero_iff hz]
  constructor
  · intro h
    exact ⟨congrArg QuadraticAlgebra.re h, congrArg QuadraticAlgebra.im h⟩
  · rintro ⟨h1, h2⟩
    exact QuadraticAlgebra.ext h1 h2

theorem torGLK_eq_one_iff (z : (QuadraticAlgebra K d 0)ˣ) : torGLK hd z = 1 ↔ (z : QuadraticAlgebra K d 0).im = 0 := by
  rw [← torP_eq_one_torQ_eq_zero_iff (norm_ne_zero_of_unit z)]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (fun g : GL (Fin 2) K => g.val 0 0) h
      simpa [rotMat] using this
    · have := congrArg (fun g : GL (Fin 2) K => g.val 1 0) h
      simpa [rotMat] using this
  · rintro ⟨hp, hq⟩
    refine Units.ext ?_
    show rotMat Dk (torP (z : QuadraticAlgebra K d 0)) (torQ (z : QuadraticAlgebra K d 0)) 1 = 1
    rw [hp, hq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]

/-- The unit with given coordinates and nonzero norm. -/
def unitOfNorm (z : QuadraticAlgebra K d 0) (hz : z.norm ≠ 0) : (QuadraticAlgebra K d 0)ˣ :=
  (QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (Ne.isUnit hz)).unit

@[simp] theorem coe_unitOfNorm (z : QuadraticAlgebra K d 0) (hz : z.norm ≠ 0) :
    (unitOfNorm z hz : QuadraticAlgebra K d 0) = z := rfl

include hd in
/-- $N(1 + u) = 2(1 + a)$ for $u = a + b\omega$ of norm one. -/
theorem norm_one_add {a b : K} (h : a ^ 2 + Dk * b ^ 2 = 1) :
    (⟨1 + a, b⟩ : QuadraticAlgebra K d 0).norm = 2 * (1 + a) := by
  rw [norm_eq]
  show (1 + a) * (1 + a) - d * b * b = _
  linear_combination h + (-(b ^ 2)) * hd

include hd in
/-- $z = 1 + u$ has $u(z) = u$ when $1 + a\ne0$. -/
theorem torP_torQ_one_add {a b : K} (h : a ^ 2 + Dk * b ^ 2 = 1) (h1 : 1 + a ≠ 0) :
    torP (⟨1 + a, b⟩ : QuadraticAlgebra K d 0) = a ∧ torQ (⟨1 + a, b⟩ : QuadraticAlgebra K d 0) = b := by
  have hn := norm_one_add hd h
  have hn0 : (⟨1 + a, b⟩ : QuadraticAlgebra K d 0).norm ≠ 0 := by
    rw [hn]; exact mul_ne_zero two_ne_zero h1
  refine ⟨?_, ?_⟩
  · rw [torP, div_eq_iff hn0, hn]
    show (1 + a) * (1 + a) + d * b * b = a * (2 * (1 + a))
    linear_combination (-1 : K) * h + b ^ 2 * hd
  · rw [torQ, div_eq_iff hn0, hn]
    show 2 * (1 + a) * b = b * (2 * (1 + a))
    ring

include hd in
/-- $N(\omega(1-u)) = -2d(1-a)$ for $u = a + b\omega$ of norm one; $\omega(1-u) = -db + (1-a)\omega$. -/
theorem norm_omega_one_sub {a b : K} (h : a ^ 2 + Dk * b ^ 2 = 1) :
    (⟨-d * b, 1 - a⟩ : QuadraticAlgebra K d 0).norm = -(2 * d * (1 - a)) := by
  rw [norm_eq]
  show (-d * b) * (-d * b) - d * (1 - a) * (1 - a) = _
  linear_combination (-d) * h + (d * b ^ 2) * hd

include hd in
/-- $z = \omega(1 - u)$ has $u(z) = u$ when $1 - a\ne0$, $D \ne 0$. -/
theorem torP_torQ_omega_one_sub (hDk : Dk ≠ 0) {a b : K} (h : a ^ 2 + Dk * b ^ 2 = 1) (h1 : 1 - a ≠ 0) :
    torP (⟨-d * b, 1 - a⟩ : QuadraticAlgebra K d 0) = a ∧ torQ (⟨-d * b, 1 - a⟩ : QuadraticAlgebra K d 0) = b := by
  have hd0 : d ≠ 0 := by rw [hd]; exact neg_ne_zero.2 hDk
  have hn := norm_omega_one_sub hd h
  have hn0 : (⟨-d * b, 1 - a⟩ : QuadraticAlgebra K d 0).norm ≠ 0 := by
    rw [hn]; exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero hd0) h1)
  refine ⟨?_, ?_⟩
  · rw [torP, div_eq_iff hn0, hn]
    show (-d * b) * (-d * b) + d * (1 - a) * (1 - a) = a * -(2 * d * (1 - a))
    linear_combination (-d) * h + (d * b ^ 2) * hd
  · rw [torQ, div_eq_iff hn0, hn]
    show 2 * (-d * b) * (1 - a) = b * -(2 * d * (1 - a))
    ring

include hd in
/-- **Hilbert 90 for the pairs $(a,b)$ with $a^2 + Db^2 = 1$** ($D\ne0$): $(a,b) = (p(z), q(z))$ for a unit $z$;
$z = 1 + u$ if $1 + a\ne0$, else $z = \omega(1 - u)$. -/
theorem exists_unit_torP_torQ (hDk : Dk ≠ 0) {a b : K} (h : a ^ 2 + Dk * b ^ 2 = 1) :
    ∃ z : (QuadraticAlgebra K d 0)ˣ, torP (z : QuadraticAlgebra K d 0) = a ∧ torQ (z : QuadraticAlgebra K d 0) = b := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  by_cases ha : 1 + a = 0
  · have h1 : 1 - a ≠ 0 := fun h0 => h2 (by linear_combination ha + h0)
    have hd0 : d ≠ 0 := by rw [hd]; exact neg_ne_zero.2 hDk
    have hn0 : (⟨-d * b, 1 - a⟩ : QuadraticAlgebra K d 0).norm ≠ 0 := by
      rw [norm_omega_one_sub hd h]; exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h2 hd0) h1)
    exact ⟨unitOfNorm _ hn0, torP_torQ_omega_one_sub hd hDk h h1⟩
  · have hn0 : (⟨1 + a, b⟩ : QuadraticAlgebra K d 0).norm ≠ 0 := by
      rw [norm_one_add hd h]; exact mul_ne_zero h2 ha
    exact ⟨unitOfNorm _ hn0, torP_torQ_one_add hd h ha⟩

include hd in
/-- **Surjectivity of $z\mapsto$ the matrix of $u(z)$** onto the rotations of $\langle1,D\rangle$ ($D\ne0$). -/
theorem torGLHom_surjective_aux (hDk : Dk ≠ 0) {g : GL (Fin 2) K}
    (hg : g.valᵀ * hessD Dk * g.val = hessD Dk) (hdet : g.val.det = 1) : ∃ z, torGLK hd z = g := by
  obtain ⟨e1, e2, e3⟩ := orth_eq_rotMat (two_ne_zero : (2 : K) ≠ 0) hDk hg
  rw [hdet] at e1
  obtain ⟨z, hzp, hzq⟩ := exists_unit_torP_torQ hd hDk e2
  refine ⟨z, Units.ext ?_⟩
  rw [torGLK_val, hzp, hzq]
  exact e1.symm

end GLPart

/-! ### Specialization to the form $\langle1,D\rangle$ -/

section Spec

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

theorem dD_map {K : Type*} [Field K] (ρ : F →+* K) : ρ (dD D) = -(ρ (algebraMap (𝓞 F) F D)) := by
  simp [dD]

theorem hessian_formF_diag_map {K : Type*} [Field K] (ρ : F →+* K) :
    ((formF (diagForm1 D)).map ρ).hessian = hessD (ρ (algebraMap (𝓞 F) F D)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hessD, formF, QuadForm.map, QuadForm.hessian, diagForm1, QuadForm.diag, Matrix.diagonal] <;> ring

theorem dIn_ne_zero (hD : D ≠ 0) (K : Type*) [Field K] [Algebra F K] [CharZero K] : dIn D K ≠ 0 := by
  simp only [dIn]
  exact (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD)

theorem ringHom_D_ne_zero (hD : D ≠ 0) {K : Type*} [Field K] (ρ : F →+* K) : ρ (algebraMap (𝓞 F) F D) ≠ 0 :=
  (map_ne_zero ρ).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD)

section FieldK

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- $E\otimes_FK = K[\omega]$, $\omega^2 = d = -D$. -/
abbrev QuadK : Type _ := QuadraticAlgebra K (algebraMap F K (dD D)) 0

theorem dD_algebraMap : algebraMap F K (dD D) = -(dIn D K) := by
  simp [dD, dIn]

/-- **$u(z) = z/\bar z = z^2N(z)^{-1}$**, the norm-one element attached to a unit $z$ of $K[\omega]$. -/
def normOneOf (z : (QuadK D K)ˣ) : QuadK D K := normOneG (z : QuadK D K)

/-- $N(u(z)) = 1$. -/
theorem normOneOf_norm (z : (QuadK D K)ˣ) : (normOneOf D K z).norm = 1 :=
  norm_normOneG (norm_ne_zero_of_unit z)

/-- $u(z) = 1$ iff $z\in K^\times$ (`im z = 0`). -/
theorem normOneOf_eq_one_iff (z : (QuadK D K)ˣ) : normOneOf D K z = 1 ↔ (z : QuadK D K).im = 0 :=
  normOneG_eq_one_iff (norm_ne_zero_of_unit z)

/-- $z\mapsto$ the isometry of $\langle1,D\rangle$ over $K$ given by multiplication by $u(z)$ in the basis $(1,\omega)$. -/
def torOrthK : (QuadK D K)ˣ →* orthGroup (formF (diagForm1 D)) K :=
  (torGLHom (dD_algebraMap D K)).codRestrict _ fun z =>
    (mem_orthGroup_diag_iff D).2 (torGLK_isometry (dD_algebraMap D K) z)

/-- **The torus map over $K$** $K[\omega]^\times\to SO(\langle1,D\rangle)(K)$, $z\mapsto$ the matrix
$\begin{pmatrix}p&-Dq\\q&p\end{pmatrix}$ of multiplication by $u(z) = p + q\omega$ in the basis $(1,\omega)$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torSOK : (QuadK D K)ˣ →* soSub (formF (diagForm1 D)) K :=
  (torOrthK D K).codRestrict _ fun z => det_torGLK (dD_algebraMap D K) z

theorem torSOK_val (z : (QuadK D K)ˣ) :
    (((torSOK D K z : soSub (formF (diagForm1 D)) K) : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val =
      rotMat (dIn D K) (normOneOf D K z).re (normOneOf D K z).im 1 := rfl

theorem torSOK_coe (z : (QuadK D K)ˣ) :
    (((torSOK D K z : soSub (formF (diagForm1 D)) K) : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K) =
      torGLK (dD_algebraMap D K) z := rfl

/-- **Hilbert 90 (surjectivity of the torus map)**: every element of $SO(\langle1,D\rangle)(K)$ is $\mathrm{tor}(z)$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torSOK_surjective (hD : D ≠ 0) : Function.Surjective (torSOK D K) := by
  intro g
  have hg := (mem_orthGroup_diag_iff D).1 (g : orthGroup (formF (diagForm1 D)) K).2
  have hdet := mem_soSub.1 g.2
  obtain ⟨z, hz⟩ := torGLHom_surjective_aux (dD_algebraMap D K) (dIn_ne_zero D hD K) hg hdet
  exact ⟨z, Subtype.ext (Subtype.ext hz)⟩

/-- **The kernel of the torus map is $K^\times$** (`im z = 0`). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem torSOK_eq_one_iff (z : (QuadK D K)ˣ) : torSOK D K z = 1 ↔ (z : QuadK D K).im = 0 := by
  rw [← torGLK_eq_one_iff (dD_algebraMap D K) z]
  constructor
  · intro h
    exact congrArg (fun g : soSub (formF (diagForm1 D)) K => ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K)) h
  · intro h
    exact Subtype.ext (Subtype.ext h)

/-- The torus map is determined by the two coordinates $p(z), q(z)$ of $u(z)$. -/
theorem torSOK_eq_of_torP_torQ (hD : D ≠ 0) (z : (QuadK D K)ˣ) (g : soSub (formF (diagForm1 D)) K)
    (hP : (normOneOf D K z).re = ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val 0 0)
    (hQ : (normOneOf D K z).im = ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val 1 0) :
    torSOK D K z = g := by
  obtain ⟨e1, -, -, -⟩ := orth_diag D hD (g : orthGroup (formF (diagForm1 D)) K).2
  have hdet := mem_soSub.1 g.2
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  rw [torSOK_val, e1, hdet]
  have hP' : (normOneOf D K z).re = ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val 0 0 := hP
  have hQ' : (normOneOf D K z).im = ((g : orthGroup (formF (diagForm1 D)) K) : GL (Fin 2) K).val 1 0 := hQ
  rw [hP', hQ']

end FieldK

/-! ### Archimedean places: ring homomorphisms $\rho : F\to\mathbb R,\mathbb C$ -/

section RingHomVersions

/-- **The torus map at a real embedding** $\rho : F\to\mathbb R$:
$\mathbb R[\omega]^\times\to SO(\langle1,\rho D\rangle)(\mathbb R)$ (the real form $Q^\rho$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torSOReal (ρ : F →+* ℝ) :
    (QuadraticAlgebra ℝ (ρ (dD D)) 0)ˣ →* soReal ((formF (diagForm1 D)).map ρ) :=
  (torGLHom (dD_map D ρ)).codRestrict _ fun z => by
    rw [mem_soReal_iff, hessian_formF_diag_map]
    exact ⟨torGLK_isometry (dD_map D ρ) z, det_torGLK (dD_map D ρ) z⟩

theorem torSOReal_coe (ρ : F →+* ℝ) (z : (QuadraticAlgebra ℝ (ρ (dD D)) 0)ˣ) :
    ((torSOReal D ρ z : soReal ((formF (diagForm1 D)).map ρ)) : GL (Fin 2) ℝ) = torGLK (dD_map D ρ) z := rfl

theorem torSOReal_surjective (hD : D ≠ 0) (ρ : F →+* ℝ) : Function.Surjective (torSOReal D ρ) := by
  intro g
  have hg := (mem_soReal_iff _ _).1 g.2
  rw [hessian_formF_diag_map] at hg
  obtain ⟨z, hz⟩ := torGLHom_surjective_aux (dD_map D ρ) (ringHom_D_ne_zero D hD ρ) hg.1 hg.2
  exact ⟨z, Subtype.ext hz⟩

theorem torSOReal_eq_one_iff (ρ : F →+* ℝ) (z : (QuadraticAlgebra ℝ (ρ (dD D)) 0)ˣ) :
    torSOReal D ρ z = 1 ↔ (z : QuadraticAlgebra ℝ (ρ (dD D)) 0).im = 0 := by
  rw [← torGLK_eq_one_iff (dD_map D ρ) z]
  constructor
  · intro h
    exact congrArg (fun g : soReal ((formF (diagForm1 D)).map ρ) => (g : GL (Fin 2) ℝ)) h
  · intro h
    exact Subtype.ext h

/-- **The torus map at a complex embedding** $\rho : F\to\mathbb C$:
$\mathbb C[\omega]^\times\to SO(\langle1,\rho D\rangle)(\mathbb C)$. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torSOC (ρ : F →+* ℂ) :
    (QuadraticAlgebra ℂ (ρ (dD D)) 0)ˣ →* soC ((formF (diagForm1 D)).map ρ) :=
  (torGLHom (dD_map D ρ)).codRestrict _ fun z => by
    rw [mem_soC_iff, gramC, hessian_formF_diag_map]
    refine ⟨?_, det_torGLK (dD_map D ρ) z⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (fun M => (1 / 2 : ℂ) • M) (torGLK_isometry (dD_map D ρ) z)

theorem torSOC_coe (ρ : F →+* ℂ) (z : (QuadraticAlgebra ℂ (ρ (dD D)) 0)ˣ) :
    ((torSOC D ρ z : soC ((formF (diagForm1 D)).map ρ)) : GL (Fin 2) ℂ) = torGLK (dD_map D ρ) z := rfl

theorem torSOC_surjective (hD : D ≠ 0) (ρ : F →+* ℂ) : Function.Surjective (torSOC D ρ) := by
  intro g
  have hg := (mem_soC_iff _ _).1 g.2
  rw [gramC, hessian_formF_diag_map] at hg
  have h1 : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * hessD (ρ (algebraMap (𝓞 F) F D)) *
      (g : GL (Fin 2) ℂ) = hessD (ρ (algebraMap (𝓞 F) F D)) := by
    have := congrArg ((2 : ℂ) • ·) hg.1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at this
    norm_num at this
    exact this
  obtain ⟨z, hz⟩ := torGLHom_surjective_aux (dD_map D ρ) (ringHom_D_ne_zero D hD ρ) h1 hg.2
  exact ⟨z, Subtype.ext hz⟩

theorem torSOC_eq_one_iff (ρ : F →+* ℂ) (z : (QuadraticAlgebra ℂ (ρ (dD D)) 0)ˣ) :
    torSOC D ρ z = 1 ↔ (z : QuadraticAlgebra ℂ (ρ (dD D)) 0).im = 0 := by
  rw [← torGLK_eq_one_iff (dD_map D ρ) z]
  constructor
  · intro h
    exact congrArg (fun g : soC ((formF (diagForm1 D)).map ρ) => (g : GL (Fin 2) ℂ)) h
  · intro h
    exact Subtype.ext h

end RingHomVersions

/-! ### Finite places: integral lifts -/

section Place

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem mem_std_iff_fin {n : ℕ} (y : Fin n → Fv) : y ∈ std v ↔ ∀ i, y i ∈ (v.adicCompletionIntegers F).toSubring := by
  refine forall_congr' fun i => ?_
  rw [neg_zero, WithZero.exp_zero, mem_O_iff]

theorem valued_two_le_one : Valued.v (2 : Fv) ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact (Valuation.map_add _ _ _).trans (max_le (by simp) (by simp))

theorem valued_dD_le_one : Valued.v (algebraMap F Fv (dD D)) ≤ 1 := by
  rw [dD_algebraMap, Valuation.map_neg]
  exact valued_dIn_le_one D v

theorem valued_norm_le_one {z : QuadK D Fv} (hx : Valued.v z.re ≤ 1) (hy : Valued.v z.im ≤ 1) :
    Valued.v z.norm ≤ 1 := by
  have hd := valued_dD_le_one D v
  rw [norm_eq]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' hx hx
  · rw [map_mul, map_mul]; exact mul_le_one' (mul_le_one' hd hy) hy

/-- If $z$ and $z^{-1}$ are integral, then $N(z)$ is a unit of $\mathfrak o_v$. -/
theorem valued_norm_eq_one {z : (QuadK D Fv)ˣ} (hx : Valued.v (z : QuadK D Fv).re ≤ 1)
    (hy : Valued.v (z : QuadK D Fv).im ≤ 1) (hx' : Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).re ≤ 1)
    (hy' : Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).im ≤ 1) : Valued.v (z : QuadK D Fv).norm = 1 := by
  have h1 := valued_norm_le_one D v hx hy
  have h2 := valued_norm_le_one D v hx' hy'
  have hprod : (z : QuadK D Fv).norm * ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).norm = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  by_contra hne
  have hlt : Valued.v (z : QuadK D Fv).norm < 1 := lt_of_le_of_ne h1 hne
  have := mul_lt_one_of_lt_of_le hlt h2
  rw [← map_mul, hprod, map_one] at this
  exact lt_irrefl _ this

/-- The inverse of a unit with norm of valuation $1$ and integral coordinates has integral coordinates. -/
theorem valued_inv_coords {z : (QuadK D Fv)ˣ} (hN : Valued.v (z : QuadK D Fv).norm = 1)
    (hx : Valued.v (z : QuadK D Fv).re ≤ 1) (hy : Valued.v (z : QuadK D Fv).im ≤ 1) :
    Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).re ≤ 1 ∧ Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).im ≤ 1 := by
  rw [coe_inv_unit]
  refine ⟨?_, ?_⟩
  · simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.re_star, smul_eq_mul, zero_mul, add_zero, map_mul, map_inv₀,
      hN, inv_one, one_mul]
    exact hx
  · simp only [QuadraticAlgebra.im_smul, QuadraticAlgebra.im_star, smul_eq_mul, map_mul, map_inv₀, hN, inv_one,
      one_mul, Valuation.map_neg]
    exact hy

/-- **Integral elements of the torus map land in $O(\mathfrak o_v^2)$:** if $z$ and $z^{-1}$ have integral coordinates,
then $\mathrm{tor}(z)$ and its inverse have integral entries, so $\mathrm{tor}(z)$ stabilizes $\mathfrak o_v^2$. -/
theorem torOrthK_mem_stdStab {z : (QuadK D Fv)ˣ} (hx : Valued.v (z : QuadK D Fv).re ≤ 1)
    (hy : Valued.v (z : QuadK D Fv).im ≤ 1) (hx' : Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).re ≤ 1)
    (hy' : Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).im ≤ 1) :
    torOrthK D Fv z ∈ stdStab (formF (diagForm1 D)) v := by
  have hN := valued_norm_eq_one D v hx hy hx' hy'
  have hd := valued_dD_le_one D v
  have hp : Valued.v (torP (z : QuadK D Fv)) ≤ 1 := by
    rw [torP, map_div₀, hN, div_one]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_one' hx hx
    · rw [map_mul, map_mul]; exact mul_le_one' (mul_le_one' hd hy) hy
  have hq : Valued.v (torQ (z : QuadK D Fv)) ≤ 1 := by
    rw [torQ, map_div₀, hN, div_one, map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (valued_two_le_one v) hx) hy
  have h1 : Valued.v (1 : Fv) ≤ 1 := by simp
  have hent : ∀ i j, Valued.v (rotMat (dIn D Fv) (torP (z : QuadK D Fv)) (torQ (z : QuadK D Fv)) 1 i j) ≤ 1 :=
    valued_rotMat_le_one D v hp hq h1
  have hent' : ∀ i j, Valued.v (rotMatInv (dIn D Fv) (torP (z : QuadK D Fv)) (torQ (z : QuadK D Fv)) 1 i j) ≤ 1 :=
    valued_rotMatInv_le_one D v hp hq h1
  exact mem_stdStab_of_mulVec v _ (fun y hy => mulVec_mem_std v hent hy) (fun y hy => mulVec_mem_std v hent' hy)

/-- **Integral Hilbert 90 at a good place.** Let $|2|_v = |D|_v = 1$. If $g\in SO(\langle1,D\rangle)(F_v)$ stabilizes
$\mathfrak o_v^2$, then $g = \mathrm{tor}(z)$ with $z$ and $z^{-1}$ in $\mathfrak o_v[\omega]$ (integral coordinates).

*Proof.* $g$ is the rotation with first column $(a,b)$, integral, $a^2 + Db^2 = 1$. Since $(1+a) + (1-a) = 2$ is a unit,
one of $1\pm a$ is a unit. Take $z = 1 + u$ if $1 + a$ is a unit ($N(z) = 2(1+a)$), else $z = \omega(1-u)$
($N(z) = -2d(1-a)$); in both cases $N(z)\in\mathfrak o_v^\times$, so $z^{-1} = N(z)^{-1}\bar z$ is integral too. -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem exists_integral_lift (h2 : Valued.v (2 : Fv) = 1) (hDv : Valued.v (dIn D Fv) = 1)
    (g : soSub (formF (diagForm1 D)) Fv)
    (hg : (g : orthGroup (formF (diagForm1 D)) Fv) ∈ stdStab (formF (diagForm1 D)) v) :
    ∃ z : (QuadK D Fv)ˣ, torSOK D Fv z = g ∧ Valued.v (z : QuadK D Fv).re ≤ 1 ∧
      Valued.v (z : QuadK D Fv).im ≤ 1 ∧ Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).re ≤ 1 ∧
      Valued.v ((z⁻¹ : (QuadK D Fv)ˣ) : QuadK D Fv).im ≤ 1 := by
  have hD : D ≠ 0 := fun h0 => by
    rw [h0] at hDv
    simp [dIn] at hDv
  obtain ⟨-, -, e3, -⟩ := orth_diag D hD (g : orthGroup (formF (diagForm1 D)) Fv).2
  have ha : Valued.v (((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 0 0) ≤ 1 :=
    entry_le_one_of_mem_stdStab v hg 0 0
  have hb : Valued.v (((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 1 0) ≤ 1 :=
    entry_le_one_of_mem_stdStab v hg 1 0
  set a := ((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 0 0 with ha_def
  set b := ((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 1 0 with hb_def
  have hd := dD_algebraMap D Fv
  have hab : a ^ 2 + dIn D Fv * b ^ 2 = 1 := e3
  have hp1 : Valued.v (1 + a) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le (by simp) ha)
  have hm1 : Valued.v (1 - a) ≤ 1 := (Valuation.map_sub _ _ _).trans (max_le (by simp) ha)
  by_cases h1 : Valued.v (1 + a) = 1
  · have h1' : 1 + a ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
    have hn := norm_one_add hd hab
    have hnv : Valued.v (⟨1 + a, b⟩ : QuadK D Fv).norm = 1 := by
      rw [hn, map_mul, h2, h1, one_mul]
    have hn0 : (⟨1 + a, b⟩ : QuadK D Fv).norm ≠ 0 := fun h0 => by rw [h0, map_zero] at hnv; exact zero_ne_one hnv
    have hz := torP_torQ_one_add hd hab h1'
    refine ⟨unitOfNorm _ hn0, torSOK_eq_of_torP_torQ D Fv hD _ g hz.1 hz.2, hp1, hb, ?_⟩
    exact valued_inv_coords D v (z := unitOfNorm _ hn0) hnv hp1 hb
  · have hlt : Valued.v (1 + a) < 1 := lt_of_le_of_ne hp1 h1
    have h3 : Valued.v (1 - a) = 1 := by
      by_contra hne
      have hlt' : Valued.v (1 - a) < 1 := lt_of_le_of_ne hm1 hne
      have : Valued.v (2 : Fv) < 1 := by
        rw [show (2 : Fv) = (1 + a) + (1 - a) by ring]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt hlt')
      rw [h2] at this
      exact lt_irrefl _ this
    have h3' : 1 - a ≠ 0 := fun h0 => by rw [h0, map_zero] at h3; exact zero_ne_one h3
    have hdv : Valued.v (algebraMap F Fv (dD D)) = 1 := by
      rw [hd, Valuation.map_neg, hDv]
    have hn := norm_omega_one_sub hd hab
    have hnv : Valued.v (⟨-(algebraMap F Fv (dD D)) * b, 1 - a⟩ : QuadK D Fv).norm = 1 := by
      rw [hn, Valuation.map_neg, map_mul, map_mul, h2, hdv, h3, one_mul, one_mul]
    have hn0 : (⟨-(algebraMap F Fv (dD D)) * b, 1 - a⟩ : QuadK D Fv).norm ≠ 0 :=
      fun h0 => by rw [h0, map_zero] at hnv; exact zero_ne_one hnv
    have hz := torP_torQ_omega_one_sub hd (dIn_ne_zero D hD Fv) hab h3'
    have hx : Valued.v (-(algebraMap F Fv (dD D)) * b) ≤ 1 := by
      rw [map_mul, Valuation.map_neg, hdv, one_mul]; exact hb
    refine ⟨unitOfNorm _ hn0, torSOK_eq_of_torP_torQ D Fv hD _ g hz.1 hz.2, hx, hm1, ?_⟩
    exact valued_inv_coords D v (z := unitOfNorm _ hn0) hnv hx hm1

end Place

end Spec

end QuadFormsKB.Tamagawa.Measure.Weil
