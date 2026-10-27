/-
# O'Meara §57: quaternion algebras (57:2–57:6, 57:12)

**Setting.** $F$ is a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`, as throughout Chapter V).
O'Meara's quaternion algebra $\left(\frac{\alpha,\beta}{F}\right) = (\alpha,\beta)$ (§57A, p. 142) is
Mathlib's `ℍ[F,α,β]` $=$ `QuaternionAlgebra F α 0 β`: the $F$-algebra with basis $1, i, j, k$ and
$$i^2 = \alpha, \qquad j^2 = \beta, \qquad k = ij = -ji,$$
which is O'Meara's multiplication table with $x_1 = i$, $x_2 = j$, $x_3 = x_1x_2 = k$ (so $k^2 = -\alpha\beta$).
O'Meara's defining base $1, x_1, x_2, x_3$ is therefore `1, i, j, k`, and his coordinates
$\xi_0, \dots, \xi_3$ are `re, imI, imJ, imK` (0-based here). O'Meara implicitly assumes
$\alpha, \beta \ne 0$ (so that his norm form is regular); this is a hypothesis wherever a statement needs it.
Conjugate, norm and trace are the library's definitions: the conjugate is Mathlib's `star`
($\bar x = \xi_0 - \xi_1 i - \xi_2 j - \xi_3 k$), the norm is `QuadFormsKB.Quat.nrd`
($Nx = x\bar x = \xi_0^2 - \alpha\xi_1^2 - \beta\xi_2^2 + \alpha\beta\xi_3^2$, a scalar identified with an element
of $F$; `Quat.mul_star_eq_nrd`), and the trace is $Tx = x + \bar x = 2\xi_0$ (`QuaternionAlgebra.self_add_star'`).

**Already in the library** (not re-proved here):
* 57:1 ($x$ invertible iff $Nx \ne 0$, $x^{-1} = (Nx)^{-1}\bar x$): `Quat.isUnit_iff_nrd_ne_zero` and `Quat.inv_eq`;
* the quadratic space $(\alpha,\beta)$ of §57B, $(\alpha,\beta) \cong \langle 1\rangle \perp \langle -\alpha\rangle \perp
  \langle -\beta\rangle \perp \langle \alpha\beta\rangle$: `Quat.nrdForm` with `Quat.evalIn_nrdForm` and
  `Quat.toQuadraticForm_nrdForm_apply`; here `nrdQuadraticForm` is the same form on the algebra itself;
* 57:12 in coordinates on $F^3$: `Quat.conjLin_pureUnit` ($\mathrm{conj}(u) = -s_u$);
* 57:9 (in Hilbert-symbol form): `Quat.nonempty_algEquiv_matrix_iff`,
  `Quat.hilbertSymbol_eq_neg_one_iff_division`.

**Proves**
* `isCentral` and `isSimpleRing` (**57:2**): $(\alpha,\beta)$ is central simple;
* `liftHom_injective`, `range_liftHom_eq_span`, `nonempty_algEquiv_range_liftHom` (**57:3**): elements $y, z$ of an
  $F$-algebra with $y^2 = \alpha$, $z^2 = \beta$, $yz = -zy$ span a subalgebra $F1 + Fy + Fz + Fyz$ isomorphic to
  $(\alpha,\beta)$;
* `nonempty_algEquiv_matrix_one_neg_one` (**57:4**): $(1,-1) \cong M_2(F)$;
* `cliffordQuaternionQ_apply`, `exists_cliffordAlgebra_algEquiv` (**57:5**): the Clifford algebra of
  $\langle\alpha\rangle \perp \langle\beta\rangle$ is $(\alpha,\beta)$;
* `algEquiv_re_eq_zero`, `algEquiv_star`, `algEquiv_re`, `algEquiv_nrd` (**57:6**): algebra isomorphisms between
  quaternion algebras preserve pure quaternions, conjugation, trace and norm;
* `symmetry_pure_apply` (**57:12**): $\tau_u x = -u x u^{-1}$ on the space of pure quaternions.
-/
import QuadFormsKB.Tamagawa.QuaternionSO3
import QuadFormsKB.Literature.OMeara.Sec91

open Quaternion QuadFormsKB.Quat

set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Quaternions57

variable {F : Type*} [Field F] [Invertible (2 : F)] {α β : F}

theorem two_ne_zero' : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero

theorem four_ne_zero' : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero two_ne_zero' two_ne_zero'

/-! ### 57:2 The quaternion algebra is central simple -/

/-- **57:2, central** (O'Meara 1963, §57A, p. 143): for $\alpha, \beta \in F^\times$ (characteristic $\ne 2$) the
center of $(\alpha,\beta)$ is $F1$. (If $x = \xi_0 + \xi_1 i + \xi_2 j + \xi_3 k$ commutes with $i$ and $j$ then
$\xi_1 = \xi_2 = \xi_3 = 0$.) -/
@[kb "omeara1963" "§57A, 57:2, p. 143"]
theorem isCentral (hα : α ≠ 0) (_hβ : β ≠ 0) : Algebra.IsCentral F ℍ[F,α,β] where
  out := by
    intro x hx
    rw [Subalgebra.mem_center_iff] at hx
    have hi := hx ⟨0, 1, 0, 0⟩
    have hj := hx ⟨0, 0, 1, 0⟩
    have e1 := congrArg QuaternionAlgebra.imJ hi
    have e2 := congrArg QuaternionAlgebra.imK hi
    have e3 := congrArg QuaternionAlgebra.imK hj
    simp at e1 e2 e3
    have hu : x.imK = 0 := by
      have : (2 * α) * x.imK = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero' hα)
    have ht : x.imJ = 0 := by
      have : 2 * x.imJ = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero'
    have hs : x.imI = 0 := by
      have : 2 * x.imI = 0 := by linear_combination -e3
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero'
    rw [Algebra.mem_bot]
    refine ⟨x.re, ?_⟩
    ext <;> simp [hs, ht, hu]

/-- A nonzero two-sided ideal of $(\alpha,\beta)$ contains a nonzero scalar. (O'Meara's argument in 57:2, part 2,
isolates one coordinate; here we combine $x$ with $ixi$, $jxj$, $kxk$: for suitable signs
$\alpha\beta x \pm \beta\, ixi \pm \alpha\, jxj \pm kxk = 4\alpha\beta\,\xi_c\, e_c$, $e_c \in \{1, i, j, k\}$,
and multiplying by $e_c$ gives a scalar.) -/
theorem exists_scalar_mem (hα : α ≠ 0) (hβ : β ≠ 0) (I : TwoSidedIdeal ℍ[F,α,β]) {x : ℍ[F,α,β]}
    (hx : x ∈ I) (hx0 : x ≠ 0) : ∃ s : F, s ≠ 0 ∧ (s : ℍ[F,α,β]) ∈ I := by
  have hab : α * β ≠ 0 := mul_ne_zero hα hβ
  have hcomb : ∀ p q r s : F, ((p : ℍ[F,α,β]) * x + (q : ℍ[F,α,β]) * (⟨0, 1, 0, 0⟩ * x * ⟨0, 1, 0, 0⟩)
      + (r : ℍ[F,α,β]) * (⟨0, 0, 1, 0⟩ * x * ⟨0, 0, 1, 0⟩)
      + (s : ℍ[F,α,β]) * (⟨0, 0, 0, 1⟩ * x * ⟨0, 0, 0, 1⟩)) ∈ I := by
    intro p q r s
    exact I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ _ hx)
      (I.mul_mem_left _ _ (I.mul_mem_right _ _ (I.mul_mem_left _ _ hx))))
      (I.mul_mem_left _ _ (I.mul_mem_right _ _ (I.mul_mem_left _ _ hx))))
      (I.mul_mem_left _ _ (I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)))
  obtain ⟨c, hc4⟩ : ∃ c : F, c = 4 := ⟨_, rfl⟩
  have P0 : ((c * α * β * x.re : F) : ℍ[F,α,β]) ∈ I := by
    have h := hcomb (α * β) β α (-1)
    convert h using 1
    ext <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> (subst hc4; first | ring1 | (ring_nf; simp))
  have P1 : ((c * α * β * x.imI * α : F) : ℍ[F,α,β]) ∈ I := by
    have h := I.mul_mem_right _ (⟨0, 1, 0, 0⟩ : ℍ[F,α,β]) (hcomb (α * β) β (-α) 1)
    convert h using 1
    ext <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> (subst hc4; first | ring1 | (ring_nf; simp))
  have P2 : ((c * α * β * x.imJ * β : F) : ℍ[F,α,β]) ∈ I := by
    have h := I.mul_mem_right _ (⟨0, 0, 1, 0⟩ : ℍ[F,α,β]) (hcomb (α * β) (-β) α 1)
    convert h using 1
    ext <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> (subst hc4; first | ring1 | (ring_nf; simp))
  have P3 : ((c * α * β * x.imK * (-(α * β)) : F) : ℍ[F,α,β]) ∈ I := by
    have h := I.mul_mem_right _ (⟨0, 0, 0, 1⟩ : ℍ[F,α,β]) (hcomb (α * β) (-β) (-α) (-1))
    convert h using 1
    ext <;> simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> (subst hc4; first | ring1 | (ring_nf; simp))
  by_contra hno
  have key : ∀ s : F, (s : ℍ[F,α,β]) ∈ I → s = 0 := fun s hs => by
    by_contra h
    exact hno ⟨s, h, hs⟩
  have h4 : c * α * β ≠ 0 := by
    rw [hc4]; exact mul_ne_zero (mul_ne_zero four_ne_zero' hα) hβ
  have r0 : x.re = 0 := (mul_eq_zero.1 (key _ P0)).resolve_left h4
  have r1 : x.imI = 0 := by
    have := key _ P1
    rw [mul_comm (c * α * β * x.imI) α] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hα
    · exact (mul_eq_zero.1 h).resolve_left h4
  have r2 : x.imJ = 0 := by
    have := key _ P2
    rw [mul_comm (c * α * β * x.imJ) β] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ
    · exact (mul_eq_zero.1 h).resolve_left h4
  have r3 : x.imK = 0 := by
    have := key _ P3
    rcases mul_eq_zero.1 this with h | h
    · exact (mul_eq_zero.1 h).resolve_left h4
    · exact absurd (neg_eq_zero.1 h) hab
  exact hx0 (by ext <;> simp [r0, r1, r2, r3])

/-- **57:2, simple** (O'Meara 1963, §57A, p. 143): for $\alpha, \beta \in F^\times$ (characteristic $\ne 2$) the
quaternion algebra $(\alpha,\beta)$ is a simple ring: its only two-sided ideals are $0$ and $(\alpha,\beta)$. -/
@[kb "omeara1963" "§57A, 57:2, p. 143"]
theorem isSimpleRing (hα : α ≠ 0) (hβ : β ≠ 0) : IsSimpleRing ℍ[F,α,β] := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases h : ∀ x ∈ I, x = 0
  · left
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩
  · right
    push Not at h
    obtain ⟨x, hx, hx0⟩ := h
    obtain ⟨s, hs, hsI⟩ := exists_scalar_mem hα hβ I hx hx0
    apply TwoSidedIdeal.eq_top
    have := I.mul_mem_left ((s⁻¹ : F) : ℍ[F,α,β]) _ hsI
    rwa [← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hs, QuaternionAlgebra.coe_one] at this

/-! ### 57:3 Subalgebras generated by anticommuting square roots -/

section Embedding

variable {A : Type*} [Ring A] [Algebra F A]

/-- The quaternion basis of $A$ given by $i \mapsto y$, $j \mapsto z$, $k \mapsto yz$ for elements with
$y^2 = \alpha$, $z^2 = \beta$, $yz = -zy$ (the hypotheses of O'Meara's 57:3). -/
def basisOfAnticomm (y z : A) (hy : y * y = α • (1 : A)) (hz : z * z = β • (1 : A))
    (hyz : y * z = -(z * y)) : QuaternionAlgebra.Basis A α 0 β where
  i := y
  j := z
  k := y * z
  i_mul_i := by rw [hy, zero_smul, add_zero]
  j_mul_j := hz
  i_mul_j := rfl
  j_mul_i := by rw [zero_smul, zero_sub, hyz, neg_neg]

/-- **57:3, injectivity** (O'Meara 1963, §57A, p. 144): for $\alpha, \beta \in F^\times$ and a nontrivial
$F$-algebra $A$ with $y, z \in A$, $y^2 = \alpha 1$, $z^2 = \beta 1$, $yz = -zy$, the algebra homomorphism
$(\alpha,\beta) \to A$ with $i \mapsto y$, $j \mapsto z$ (Mathlib's `QuaternionAlgebra.Basis.liftHom`, which
sends $k$ to $yz$) is injective. (O'Meara: its kernel is a two-sided ideal, hence $0$ by 57:2.)
*Update:* O'Meara's "arbitrary algebra $A$" must be nontrivial (otherwise the kernel is everything), and
$\alpha, \beta \ne 0$ is needed for 57:2. -/
@[kb "omeara1963" "§57A, 57:3, p. 144"]
theorem liftHom_injective (hα : α ≠ 0) (hβ : β ≠ 0) [Nontrivial A] (y z : A)
    (hy : y * y = α • (1 : A)) (hz : z * z = β • (1 : A)) (hyz : y * z = -(z * y)) :
    Function.Injective (basisOfAnticomm y z hy hz hyz).liftHom := by
  have := isSimpleRing hα hβ
  exact RingHom.injective (basisOfAnticomm y z hy hz hyz).liftHom.toRingHom

/-- **57:3, the image** (O'Meara 1963, §57A, p. 144): the image of that homomorphism, as a subspace of $A$, is
$F1 + Fy + Fz + Fyz$. -/
@[kb "omeara1963" "§57A, 57:3, p. 144"]
theorem range_liftHom_eq_span (y z : A)
    (hy : y * y = α • (1 : A)) (hz : z * z = β • (1 : A)) (hyz : y * z = -(z * y)) :
    Subalgebra.toSubmodule (basisOfAnticomm y z hy hz hyz).liftHom.range =
      Submodule.span F {1, y, z, y * z} := by
  apply le_antisymm
  · intro a ha
    rw [Subalgebra.mem_toSubmodule] at ha
    obtain ⟨q, rfl⟩ := ha
    change algebraMap F A q.re + q.imI • y + q.imJ • z + q.imK • (y * z) ∈ _
    rw [Algebra.algebraMap_eq_smul_one]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      refine Submodule.smul_mem (Submodule.span F {1, y, z, y * z}) _ (Submodule.subset_span ?_) <;> simp
  · rw [Submodule.span_le]
    have hmem : ∀ q : ℍ[F,α,β], (basisOfAnticomm y z hy hz hyz).liftHom q ∈
        Subalgebra.toSubmodule (basisOfAnticomm y z hy hz hyz).liftHom.range :=
      fun q => ⟨q, rfl⟩
    rintro _ (rfl | rfl | rfl | rfl)
    · simp
    · simpa [QuaternionAlgebra.Basis.lift, basisOfAnticomm] using hmem ⟨0, 1, 0, 0⟩
    · simpa [QuaternionAlgebra.Basis.lift, basisOfAnticomm] using hmem ⟨0, 0, 1, 0⟩
    · simpa [QuaternionAlgebra.Basis.lift, basisOfAnticomm] using hmem ⟨0, 0, 0, 1⟩

/-- **57:3** (O'Meara 1963, §57A, p. 144): under the hypotheses of `liftHom_injective`, the subalgebra
$F1 + Fy + Fz + Fyz$ of $A$ (the range of the homomorphism, `range_liftHom_eq_span`) is isomorphic as an
$F$-algebra to $(\alpha,\beta)$, by $i \mapsto y$, $j \mapsto z$. -/
@[kb "omeara1963" "§57A, 57:3, p. 144"]
theorem nonempty_algEquiv_range_liftHom (hα : α ≠ 0) (hβ : β ≠ 0) [Nontrivial A] (y z : A)
    (hy : y * y = α • (1 : A)) (hz : z * z = β • (1 : A)) (hyz : y * z = -(z * y)) :
    Nonempty (ℍ[F,α,β] ≃ₐ[F] (basisOfAnticomm y z hy hz hyz).liftHom.range) :=
  ⟨AlgEquiv.ofInjective _ (liftHom_injective hα hβ y z hy hz hyz)⟩

end Embedding

/-! ### 57:4 $(1,-1) \cong M_2(F)$ -/

/-- **57:4** (O'Meara 1963, §57A, p. 145): $(1,-1) \cong M_2(F)$ as $F$-algebras. Following the book, take
$y = e_{12} + e_{21}$ and $z = e_{12} - e_{21}$ (so $y^2 = 1$, $z^2 = -1$, $yz = -zy$); by 57:3 the map
$i \mapsto y$, $j \mapsto z$ is injective, and it is onto since both sides have dimension $4$ over $F$.
(The indices of $y$ and $z$ are lost in the machine-read text; they are reconstructed from the stated relations
$y^2 = 1$, $z^2 = -1$, $yz = -zy$.) -/
@[kb "omeara1963" "§57A, 57:4, p. 145"]
theorem nonempty_algEquiv_matrix_one_neg_one :
    Nonempty (ℍ[F,1,-1] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  let y : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]
  let z : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
  have hy : y * y = (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [y, Matrix.mul_apply, Fin.sum_univ_two]
  have hz : z * z = (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [z, Matrix.mul_apply, Fin.sum_univ_two]
  have hyz : y * z = -(z * y) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [y, z, Matrix.mul_apply, Fin.sum_univ_two]
  have hinj := liftHom_injective (one_ne_zero (α := F)) (neg_ne_zero.2 (one_ne_zero (α := F))) y z hy hz hyz
  set φ := (basisOfAnticomm y z hy hz hyz).liftHom
  have hrank : Module.finrank F ℍ[F,1,-1] = Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]; simp
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-! ### 57:5 The Clifford algebra of $\langle\alpha\rangle \perp \langle\beta\rangle$ -/

/-- Mathlib's quadratic form `CliffordAlgebraQuaternion.Q α β` on $F \times F$ is
$(v_1, v_2) \mapsto \alpha v_1^2 + \beta v_2^2$, i.e. (with O'Meara's $Q(x) = B(x,x)$) the quadratic space
$\langle\alpha\rangle \perp \langle\beta\rangle$ with orthogonal basis $(1,0), (0,1)$. -/
theorem cliffordQuaternionQ_apply (v : F × F) :
    CliffordAlgebraQuaternion.Q α β v = α * v.1 ^ 2 + β * v.2 ^ 2 := by
  simp [CliffordAlgebraQuaternion.Q, sq]

/-- **57:5** (O'Meara 1963, §57A, p. 145): the Clifford algebra of the quadratic space
$\langle\alpha\rangle \perp \langle\beta\rangle$ (`CliffordAlgebraQuaternion.Q α β`, `cliffordQuaternionQ_apply`)
is isomorphic to the quaternion algebra $(\alpha,\beta)$: Mathlib's `CliffordAlgebraQuaternion.equiv`, an
$F$-algebra isomorphism sending $\iota(1,0) \mapsto i$ and $\iota(0,1) \mapsto j$. -/
@[kb "omeara1963" "§57A, 57:5, p. 145"]
theorem exists_cliffordAlgebra_algEquiv :
    ∃ φ : CliffordAlgebra (CliffordAlgebraQuaternion.Q α β) ≃ₐ[F] ℍ[F,α,β],
      φ (CliffordAlgebra.ι _ (1, 0)) = ⟨0, 1, 0, 0⟩ ∧ φ (CliffordAlgebra.ι _ (0, 1)) = ⟨0, 0, 1, 0⟩ := by
  refine ⟨CliffordAlgebraQuaternion.equiv (c₁ := α) (c₂ := β), ?_, ?_⟩ <;> simp

/-! ### 57:6 Isomorphisms of quaternion algebras -/

section Iso

variable {γ δ : F}

theorem algEquiv_coe (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) (r : F) : φ (r : ℍ[F,α,β]) = (r : ℍ[F,γ,δ]) := by
  rw [← QuaternionAlgebra.coe_algebraMap]
  exact φ.commutes r

/-- A quaternion whose square is a scalar and which is not itself a scalar is pure. (Characteristic $\ne 2$.) -/
theorem re_eq_zero_of_mul_self_scalar {y : ℍ[F,γ,δ]} (h : ∃ r : F, y * y = (r : ℍ[F,γ,δ]))
    (hn : ¬ ∃ s : F, y = (s : ℍ[F,γ,δ])) : y.re = 0 := by
  obtain ⟨r, hr⟩ := h
  by_contra hre
  apply hn
  have e1 := congrArg QuaternionAlgebra.imI hr
  have e2 := congrArg QuaternionAlgebra.imJ hr
  have e3 := congrArg QuaternionAlgebra.imK hr
  simp at e1 e2 e3
  have hc : ∀ t : F, 2 * y.re * t = 0 → t = 0 := fun t ht =>
    (mul_eq_zero.1 ht).resolve_left (mul_ne_zero two_ne_zero' hre)
  refine ⟨y.re, ?_⟩
  ext <;> simp
  · exact hc _ (by linear_combination e1)
  · exact hc _ (by linear_combination e2)
  · exact hc _ (by linear_combination e3)

/-- **57:6, pure quaternions** (O'Meara 1963, §57A, p. 145): an algebra isomorphism of quaternion algebras sends
pure quaternions (`re = 0`) to pure quaternions. (O'Meara's argument: a nonzero $x$ is pure iff $x^2$ is a scalar
and $x$ is not; stated here without the hypotheses $\alpha, \beta, \gamma, \delta \ne 0$ that the book assumes
implicitly, which are not needed.) -/
@[kb "omeara1963" "§57A, 57:6, p. 145"]
theorem algEquiv_re_eq_zero (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) {x : ℍ[F,α,β]} (hx : x.re = 0) :
    (φ x).re = 0 := by
  by_cases hs : ∃ s : F, φ x = (s : ℍ[F,γ,δ])
  · obtain ⟨s, hs⟩ := hs
    have : x = (s : ℍ[F,α,β]) := φ.injective (by rw [hs, algEquiv_coe])
    have hs0 : s = 0 := by rw [this] at hx; simpa using hx
    rw [hs, hs0]; rfl
  · refine re_eq_zero_of_mul_self_scalar ⟨-nrd x, ?_⟩ hs
    have hxx : x * x = ((-nrd x : F) : ℍ[F,α,β]) := by
      have h1 : star x = -x := by ext <;> simp [hx]
      have := mul_star_eq_nrd x
      rw [h1, mul_neg] at this
      rw [QuaternionAlgebra.coe_neg, ← this, neg_neg]
    rw [← map_mul, hxx, algEquiv_coe]

/-- **57:6, trace** (O'Meara 1963, §57A, p. 145): an algebra isomorphism of quaternion algebras preserves the
scalar part, hence the trace $T x = 2\,\mathrm{re}(x)$. -/
@[kb "omeara1963" "§57A, 57:6, p. 145"]
theorem algEquiv_re (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) (x : ℍ[F,α,β]) : (φ x).re = x.re := by
  have h := algEquiv_re_eq_zero φ (x := x.im) (by simp)
  have hx : x = (x.re : ℍ[F,α,β]) + x.im := (QuaternionAlgebra.re_add_im x).symm
  conv_lhs => rw [hx, map_add, algEquiv_coe]
  simp [h]

/-- **57:6, conjugation** (O'Meara 1963, §57A, p. 145): $\varphi \bar x = \overline{\varphi x}$. -/
@[kb "omeara1963" "§57A, 57:6, p. 145"]
theorem algEquiv_star (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) (x : ℍ[F,α,β]) : φ (star x) = star (φ x) := by
  rw [QuaternionAlgebra.star_eq_two_re_sub, QuaternionAlgebra.star_eq_two_re_sub, map_sub, algEquiv_coe,
    algEquiv_re]
  simp

/-- **57:6, norm** (O'Meara 1963, §57A, p. 145): $N(\varphi x) = N x$ (norms are the scalars `Quat.nrd`). -/
@[kb "omeara1963" "§57A, 57:6, p. 145"]
theorem algEquiv_nrd (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) (x : ℍ[F,α,β]) : nrd (φ x) = nrd x := by
  apply QuaternionAlgebra.coe_injective
  rw [← mul_star_eq_nrd, ← algEquiv_star, ← map_mul, mul_star_eq_nrd, algEquiv_coe]

end Iso

/-! ### 57:12 The symmetry of the pure quaternions -/

section Symmetry

/-- The quadratic space $(\alpha,\beta)$ of §57B (p. 145): the algebra with $Q(x) = Nx$, i.e. the form
$\langle 1, -\alpha, -\beta, \alpha\beta\rangle$ (Mathlib quadratic form obtained from `Quat.nrdForm`). -/
def nrdQuadraticForm (α β : F) : QuadraticForm F ℍ[F,α,β] :=
  (Quat.nrdForm α β).toQuadraticForm.comp (QuaternionAlgebra.linearEquivTuple α 0 β).toLinearMap

theorem nrdQuadraticForm_apply (x : ℍ[F,α,β]) : nrdQuadraticForm α β x = nrd x := by
  have := toQuadraticForm_nrdForm_apply α β (QuaternionAlgebra.equivTuple α 0 β x)
  rw [Equiv.symm_apply_apply] at this
  exact this

/-- The pure quaternions $(\alpha,\beta)^\circ = F x_1 + F x_2 + F x_3$ (§57A, p. 142), as a subspace. -/
def pureSubmodule (α β : F) : Submodule F ℍ[F,α,β] where
  carrier := {x | x.re = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := rfl
  smul_mem' := by intro c x hx; simp_all

theorem mem_pureSubmodule {x : ℍ[F,α,β]} : x ∈ pureSubmodule α β ↔ x.re = 0 := Iff.rfl

/-- **The quadratic space of pure quaternions** $(\alpha,\beta)^\circ$ with $Q(x) = Nx$ (§57B, p. 146), i.e.
$\langle -\alpha\rangle \perp \langle -\beta\rangle \perp \langle\alpha\beta\rangle$. -/
def pureQuadraticForm (α β : F) : QuadraticForm F (pureSubmodule α β) :=
  (nrdQuadraticForm α β).comp (pureSubmodule α β).subtype

theorem pureQuadraticForm_apply (x : pureSubmodule α β) :
    pureQuadraticForm α β x = nrd (x : ℍ[F,α,β]) := nrdQuadraticForm_apply _

theorem two_mul_bil {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (x y : V) :
    2 * bil Q x y = Q (x + y) - Q x - Q y := by
  rw [← bil_self Q (x + y), bil_add_left, bil_add_right, bil_add_right, bil_comm Q y x, bil_self, bil_self]
  ring

/-- **57:12** (O'Meara 1963, §57C, p. 148): let $u$ be an anisotropic pure quaternion in $(\alpha,\beta)$,
$Nu \ne 0$, with $\tau_u$ the symmetry (`OMeara.symmetry`) of the quadratic space $(\alpha,\beta)^\circ$ of pure
quaternions ($Q(x) = Nx$). Then $u$ is invertible (57:1) and $\tau_u x = -u x u^{-1}$ for all pure $x$.
Here the inverse is the inverse of a unit $w$ of $(\alpha,\beta)$ with $w = u$ (it exists by 57:1:
`Quat.isUnit_iff_nrd_ne_zero`). -/
@[kb "omeara1963" "§57C, 57:12, p. 148"]
theorem symmetry_pure_apply {u : pureSubmodule α β} (hu : pureQuadraticForm α β u ≠ 0)
    (w : (ℍ[F,α,β])ˣ) (hw : (w : ℍ[F,α,β]) = u) (x : pureSubmodule α β) :
    ((symmetry (pureQuadraticForm α β) u hu x : pureSubmodule α β) : ℍ[F,α,β]) =
      -((u : ℍ[F,α,β]) * x * ((w⁻¹ : (ℍ[F,α,β])ˣ) : ℍ[F,α,β])) := by
  have hn : nrd (u : ℍ[F,α,β]) ≠ 0 := by rwa [pureQuadraticForm_apply] at hu
  have hb := two_mul_bil (pureQuadraticForm α β) x u
  rw [pureQuadraticForm_apply, pureQuadraticForm_apply, pureQuadraticForm_apply] at hb
  rw [symmetry_apply, Quat.inv_eq, hw, pureQuadraticForm_apply]
  obtain ⟨x, hx⟩ := x
  obtain ⟨u, hu0⟩ := u
  simp only [mem_pureSubmodule] at hx hu0
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add] at hb ⊢
  have hkey : u * x * star u =
      (-nrd u) • x + (nrd (x + u) - nrd x - nrd u) • u := by
    ext <;> simp [nrd, hx, hu0] <;> ring
  change nrd u ≠ 0 at hn
  rw [hb, mul_smul_comm, hkey]
  generalize nrd (x + u) - nrd x - nrd u = T
  generalize nrd u = n at hn ⊢
  ext <;> simp <;> field_simp <;> ring

end Symmetry

end Quaternions57

end QuadFormsKB.OMeara