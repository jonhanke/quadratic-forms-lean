import Mathlib
import QuadFormsKB.Citation

open QuadraticAlgebra NumberField Polynomial

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

/-- **$D$ is the discriminant of a quadratic field**: a fundamental discriminant
(Mathlib's `Int.IsFundamentalDiscr`: $D \equiv 0, 1 \pmod 4$ and $D$ is not $f^2 D_0$ with $f > 1$ and
$D_0 \equiv 0, 1 \pmod 4$) with $D \ne 1$. Fields: `fund`, `ne_one`. -/
class IsQuadDisc (D : ℤ) : Prop where
  /-- $D$ is a fundamental discriminant. -/
  fund : Int.IsFundamentalDiscr D
  /-- $D \neq 1$ (the only square fundamental discriminant). -/
  ne_one : D ≠ 1

variable (D : ℤ)

/-- The coefficient $a_D = \lfloor D/4 \rfloor$, so that $\omega^2 = a_D + b_D\,\omega$. -/
abbrev qa : ℤ := D / 4
/-- The coefficient $b_D = D \bmod 4 \in \{0, 1\}$, so that $\omega^2 = a_D + b_D\,\omega$. -/
abbrev qb : ℤ := D % 4

/-- **The quadratic field $K_D = \mathbb{Q}(\sqrt D)$**, realized as the quadratic algebra
$\mathbb{Q}[\omega]/(\omega^2 - b_D\omega - a_D)$ with $a_D = \lfloor D/4\rfloor$, $b_D = D \bmod 4$, so that
$\omega = (b_D + \sqrt D)/2$ (Mathlib's `QuadraticAlgebra ℚ a b`, with $\omega^2 = a + b\omega$). -/
abbrev QField : Type := QuadraticAlgebra ℚ (qa D : ℚ) (qb D : ℚ)

/-- **The order $\mathbb{Z}[\omega] = \mathbb{Z}\left[\tfrac{b_D + \sqrt D}{2}\right]$** (`QuadraticAlgebra ℤ a b`); for a
fundamental $D$ it is the ring of integers of $K_D$ (`isIntegralClosure`). -/
abbrev QOrder : Type := QuadraticAlgebra ℤ (qa D) (qb D)

variable {D}

theorem qb_eq (hD : D % 4 = 0 ∨ D % 4 = 1) : qb D = 0 ∨ qb D = 1 := hD

/-- $b_D^2 + 4a_D = D$. -/
theorem discr_qa_qb (hD : D % 4 = 0 ∨ D % 4 = 1) : discr (qa D) (qb D) = D :=
  discr_ediv_emod hD

/-- A fundamental discriminant $D \ne 1$ is not a square. -/
theorem not_isSquare_of_isQuadDisc [h : IsQuadDisc D] : ¬ IsSquare D := by
  rintro ⟨k, hk⟩
  rcases Int.isFundamentalDiscr_iff_squarefree.mp h.fund with ⟨h1, hsq⟩ | ⟨h0, hsq, hm⟩
  · have hu : IsUnit k := hsq k (hk ▸ dvd_refl _)
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at hk <;> exact h.ne_one hk
  · -- D = 4m, m squarefree, so k = 2j and m = j², j a unit, m = 1: but m ≡ 2,3 mod 4.
    have h4 : D = 4 * (D / 4) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h0)).symm
    have hk2 : (2 : ℤ) ∣ k := by
      have : (2 : ℤ) ∣ k * k := ⟨2 * (D / 4), by rw [← hk]; omega⟩
      rcases Int.Prime.dvd_mul' (by norm_num) this with h | h <;> exact h
    obtain ⟨j, rfl⟩ := hk2
    have hD' : D = 4 * (j * j) := by rw [hk]; ring
    have hm' : D / 4 = j * j := by omega
    have hu : IsUnit j := hsq j (hm' ▸ dvd_refl _)
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp at hm' <;> omega

instance [IsQuadDisc D] : Fact (¬ IsSquare (discr (qa D : ℚ) (qb D : ℚ))) := by
  refine ⟨?_⟩
  rw [discr_intCast, discr_qa_qb (IsQuadDisc.fund (D := D)).1, Rat.isSquare_intCast_iff]
  exact not_isSquare_of_isQuadDisc

instance [IsQuadDisc D] : Fact (¬ IsSquare (discr (qa D) (qb D))) := by
  refine ⟨?_⟩
  rw [discr_qa_qb (IsQuadDisc.fund (D := D)).1]
  exact not_isSquare_of_isQuadDisc

instance [IsQuadDisc D] : NumberField (QField D) := {}

/-! ### The ring of integers -/

private theorem zmod4_cases (e : ℤ) : (e % 4 = 0 → (e : ZMod 4) = 0) ∧ (e % 4 = 1 → (e : ZMod 4) = 1) ∧
    (e % 4 = 2 → (e : ZMod 4) = 2) ∧ (e % 4 = 3 → (e : ZMod 4) = 3) := by
  have h := ZMod.intCast_mod e 4
  push_cast at h
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> rw [← h, h'] <;> rfl

private theorem emod_four_of_zmod {e : ℤ} (h : (e : ZMod 4) = 0 ∨ (e : ZMod 4) = 1) :
    e % 4 = 0 ∨ e % 4 = 1 := by
  have : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases this with h' | h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · rw [(zmod4_cases e).2.2.1 h'] at h; exact absurd h (by decide)
  · rw [(zmod4_cases e).2.2.2 h'] at h; exact absurd h (by decide)

private theorem zmod_of_emod {e : ℤ} (h : e % 4 = 0 ∨ e % 4 = 1) : (e : ZMod 4) = 0 ∨ (e : ZMod 4) = 1 := by
  rcases h with h | h
  · exact Or.inl ((zmod4_cases e).1 h)
  · exact Or.inr ((zmod4_cases e).2.1 h)

private theorem zmod_of_odd {r : ℤ} (hr : Odd r) : (r : ZMod 4) = 1 ∨ (r : ZMod 4) = 3 := by
  have h := Int.odd_iff.mp hr
  have : r % 4 = 1 ∨ r % 4 = 3 := by omega
  rcases this with h' | h'
  · exact Or.inl ((zmod4_cases r).2.1 h')
  · exact Or.inr ((zmod4_cases r).2.2.2 h')

/-- If $D$ is a fundamental discriminant and $D v^2 = t^2 - 4n$ with $t, n \in \mathbb{Z}$, then $v \in \mathbb{Z}$. -/
theorem den_eq_one_of_fund {D : ℤ} (hD : Int.IsFundamentalDiscr D) {v : ℚ} {t n : ℤ}
    (h : (D : ℚ) * v ^ 2 = t ^ 2 - 4 * n) : v.den = 1 := by
  by_contra hs
  set r := v.num
  set s : ℕ := v.den
  have hs0 : (s : ℚ) ≠ 0 := by positivity
  have hv : v = r / s := (Rat.num_div_den v).symm
  have hZ : D * r ^ 2 = (t ^ 2 - 4 * n) * (s : ℤ) ^ 2 := by
    have : (D : ℚ) * r ^ 2 = (t ^ 2 - 4 * n) * (s : ℚ) ^ 2 := by
      rw [← h, hv]; field_simp
    exact_mod_cast this
  set p := s.minFac
  have hp : p.Prime := Nat.minFac_prime hs
  obtain ⟨s1, hs1⟩ : p ∣ s := Nat.minFac_dvd s
  have hcop : Nat.Coprime p r.natAbs :=
    (Nat.Coprime.coprime_dvd_right (Nat.minFac_dvd s) v.reduced).symm
  have hgcd : Int.gcd (p : ℤ) r = 1 := hcop
  have hpr : ¬ (p : ℤ) ∣ r := by
    intro hd
    have := Int.dvd_gcd (dvd_refl (p : ℤ)) hd
    rw [hgcd] at this
    have h1 : p ≤ 1 := Nat.le_of_dvd one_pos (by exact_mod_cast this)
    have h2 := hp.two_le
    omega
  -- p² ∣ D
  have hpD : (p : ℤ) ^ 2 ∣ D := by
    have h1 : (p : ℤ) ^ 2 ∣ D * r ^ 2 := by
      rw [hZ, hs1]; push_cast; exact ⟨(t ^ 2 - 4 * n) * s1 ^ 2, by ring⟩
    have hcop2 : IsCoprime ((p : ℤ) ^ 2) (r ^ 2) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr hgcd).pow
    exact hcop2.dvd_of_dvd_mul_right h1
  obtain ⟨e, he⟩ := hpD
  have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
  have hE : e * r ^ 2 = (t ^ 2 - 4 * n) * (s1 : ℤ) ^ 2 := by
    apply mul_left_cancel₀ hp0
    have := hZ
    rw [he, hs1] at this; push_cast at this; linear_combination this
  refine (Int.isFundamentalDiscr_iff_forall_prime.mp hD).2 p hp ⟨e, he, emod_four_of_zmod ?_⟩
  rcases Int.even_or_odd r with hre | hro
  · -- r even, so p is odd, and D ≡ e (mod 4)
    have hpo : Odd (p : ℤ) := by
      rcases Int.even_or_odd (p : ℤ) with hpe | hpo
      · exfalso
        have h22 : p = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (by exact_mod_cast hpe.two_dvd)).symm
        exact hpr (h22 ▸ hre.two_dvd)
      · exact hpo
    have hD4 := zmod_of_emod hD.1
    have hp4 := zmod_of_odd hpo
    rw [he] at hD4; push_cast at hD4 hp4
    generalize (e : ZMod 4) = E at hD4 ⊢
    generalize ((p : ℕ) : ZMod 4) = P at hp4 hD4
    revert E P; decide
  · have hr4 := zmod_of_odd hro
    have hE4 : ((e * r ^ 2 : ℤ) : ZMod 4) = (((t ^ 2 - 4 * n) * (s1 : ℤ) ^ 2 : ℤ) : ZMod 4) := by rw [hE]
    push_cast at hE4
    rw [show (4 : ZMod 4) = 0 from rfl, zero_mul, sub_zero] at hE4
    generalize (e : ZMod 4) = E at hE4 ⊢
    generalize (r : ZMod 4) = R at hr4 hE4
    generalize (t : ZMod 4) = T at hE4
    generalize ((s1 : ℕ) : ZMod 4) = S at hE4
    revert E R T S; decide

/-- **The ring of integers of $K_D$ is $\mathbb{Z}[\omega]$**, $\omega = (b_D + \sqrt D)/2$: an element
$x = u + v\omega \in K_D$ is integral over $\mathbb{Z}$ iff $u, v \in \mathbb{Z}$. *Proof:* if $x$ is integral, so is its
conjugate, hence $t = \operatorname{Tr} x = 2u + b_D v$ and $n = N x = u^2 + b_D uv - a_D v^2$ are rational integers;
then $D v^2 = t^2 - 4n$ forces $v \in \mathbb{Z}$ (`den_eq_one_of_fund`, using that $D$ is fundamental) and
$(2u)^2 = 4n - 2b_D(2u)v + 4a_D v^2$ is even, so $u \in \mathbb{Z}$. Source: Marcus, *Number Fields*, Ch. 2, Cor. 2 to
Thm. 1; Cohen, *A Course in Computational Algebraic Number Theory*, §5.1.1. -/
@[kb "marcus1977" "Ch. 2, Thm. 1 Cor. 2"]
theorem isIntegral_iff [IsQuadDisc D] {x : QField D} :
    IsIntegral ℤ x ↔ ∃ y : QOrder D, algebraMap (QOrder D) (QField D) y = x := by
  constructor
  · intro hx
    have hstar : IsIntegral ℤ (star x) := hx.map (starRingEnd (QField D)).toIntAlgHom
    have htr : IsIntegral ℤ (trace x) := by
      have : IsIntegral ℤ (algebraMap ℚ (QField D) (trace x)) := by
        rw [algebraMap_trace_eq_add_star]; exact hx.add hstar
      exact isIntegral_algebraMap_iff.mp this
    have hnm : IsIntegral ℤ (norm x) := by
      have : IsIntegral ℤ (algebraMap ℚ (QField D) (norm x)) := by
        rw [algebraMap_norm_eq_mul_star]; exact hx.mul hstar
      exact isIntegral_algebraMap_iff.mp this
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnm
    rw [trace_def] at ht
    rw [norm_def] at hn
    simp only [algebraMap_int_eq, eq_intCast] at ht hn
    have hdisc : ((qb D : ℚ) ^ 2 + 4 * (qa D : ℚ)) = D := by
      have := discr_qa_qb (IsQuadDisc.fund (D := D)).1
      rw [discr_def] at this; exact_mod_cast this
    have hv : (D : ℚ) * x.im ^ 2 = t ^ 2 - 4 * n := by
      rw [← hdisc, ht, hn]; ring
    have hden := den_eq_one_of_fund (IsQuadDisc.fund (D := D)) hv
    set r := x.im.num
    have hr : (r : ℚ) = x.im := (Rat.den_eq_one_iff _).mp hden
    -- w = 2u is an integer, and it is even
    have hw : ((t - qb D * r : ℤ) : ℚ) = 2 * x.re := by push_cast; rw [hr, ht]; ring
    have hw2 : (t - qb D * r) ^ 2 = 4 * n - 2 * qb D * (t - qb D * r) * r + 4 * qa D * r ^ 2 := by
      have : (((t - qb D * r) ^ 2 : ℤ) : ℚ) =
          ((4 * n - 2 * qb D * (t - qb D * r) * r + 4 * qa D * r ^ 2 : ℤ) : ℚ) := by
        push_cast
        rw [show ((t : ℚ) - qb D * r) = t - qb D * r from rfl]
        have hw' : (t : ℚ) - qb D * r = 2 * x.re := by exact_mod_cast hw
        rw [hw', hr, hn]; ring
      exact_mod_cast this
    obtain ⟨k, hk⟩ : Even (t - qb D * r) := by
      have h2 : Even ((t - qb D * r) ^ 2) := by
        rw [hw2]; exact ⟨2 * n - qb D * (t - qb D * r) * r + 2 * qa D * r ^ 2, by ring⟩
      exact (Int.even_pow.mp h2).1
    refine ⟨⟨k, r⟩, ?_⟩
    ext
    · simp only [Int.re_algebraMap]
      have : ((t - qb D * r : ℤ) : ℚ) = 2 * k := by rw [hk]; push_cast; ring
      linarith
    · simp only [Int.im_algebraMap]; exact hr
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral y).algebraMap

instance isIntegralClosure [IsQuadDisc D] : IsIntegralClosure (QOrder D) ℤ (QField D) :=
  IsIntegralClosure.mk (FaithfulSMul.algebraMap_injective _ _) isIntegral_iff

/-! ### Trace and discriminant of a quadratic algebra -/
section
variable {R : Type*} [CommRing R] {a b : R}

/-- **The algebra trace** of the free $R$-algebra `QuadraticAlgebra R a b` (basis $1, \omega$) is Mathlib's
`QuadraticAlgebra.trace`: $\operatorname{Tr}(x + y\omega) = 2x + by$. -/
theorem algTrace_eq (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (basis a b) z, Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp [basis_repr_apply, trace_def, basis_apply_zero, basis_apply_one]
  ring

/-- **The discriminant of the basis $\{1, \omega\}$** of `QuadraticAlgebra R a b` is $b^2 + 4a$
(Mathlib's `QuadraticAlgebra.discr a b`). -/
theorem algDiscr_basis : Algebra.discr R (basis a b) = discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis_apply_zero, basis_apply_one,
    algTrace_eq]
  simp [trace_def, discr_def, omega_mul_omega_eq_mk]
  ring
end

variable [IsQuadDisc D]

/-- The ring isomorphism $\mathbb{Z}[\omega] \cong \mathcal O_{K_D}$ (over $\mathbb{Z}$). -/
noncomputable def orderEquiv (D : ℤ) [IsQuadDisc D] : QOrder D ≃ₐ[ℤ] 𝓞 (QField D) :=
  IsIntegralClosure.equiv ℤ (QOrder D) (QField D) (𝓞 (QField D))

/-- **The generator $\theta = \omega = (b_D + \sqrt D)/2 \in \mathcal O_{K_D}$.** -/
noncomputable def theta (D : ℤ) [IsQuadDisc D] : 𝓞 (QField D) := orderEquiv D ω

/-- $\theta = \omega$ in $K_D$. -/
theorem coe_theta : ((theta D : 𝓞 (QField D)) : QField D) = ω := by
  have := IsIntegralClosure.algebraMap_equiv ℤ (QOrder D) (QField D) (𝓞 (QField D)) ω
  exact this.trans (by ext <;> simp)

/-- **$\mathcal O_{K_D} = \mathbb{Z}[\theta]$** (monogenic), so Dedekind–Kummer applies at every prime, including $p = 2$. -/
theorem adjoin_theta : Algebra.adjoin ℤ {theta D} = ⊤ := by
  have := Algebra.adjoin_image ℤ (orderEquiv D).toAlgHom {ω}
  rw [Set.image_singleton, adjoin_omega_eq_top] at this
  rw [theta, show (orderEquiv D) ω = (orderEquiv D).toAlgHom ω from rfl, this, Algebra.map_top]
  exact eq_top_iff.mpr fun x _ => ⟨(orderEquiv D).symm x, by simp⟩

/-- **The defining polynomial** $f_D(X) = X^2 - b_D X - a_D \in \mathbb{Z}[X]$ of $\omega$, of discriminant $D$. -/
noncomputable def qpoly (D : ℤ) : ℤ[X] := X ^ 2 - C (qb D) * X - C (qa D)

omit [IsQuadDisc D] in
/-- $f_D$ is monic. -/
theorem qpoly_monic : (qpoly D).Monic := by
  unfold qpoly
  rw [sub_sub]
  exact (monic_X_pow 2).sub_of_left (by
    rw [degree_X_pow]; refine (degree_add_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ((degree_C_le).trans_lt (by norm_num)))

omit [IsQuadDisc D] in
/-- $f_D$ has degree $2$. -/
theorem qpoly_natDegree : (qpoly D).natDegree = 2 := by
  unfold qpoly; compute_degree!

omit [IsQuadDisc D] in
/-- $f_D(\omega) = 0$ in $\mathbb{Z}[\omega]$. -/
theorem aeval_omega : aeval (ω : QOrder D) (qpoly D) = 0 := by
  simp only [qpoly, map_sub, map_pow, aeval_X, map_mul, eq_intCast]
  ext <;> simp [sq, omega_mul_omega_eq_mk]

/-- $f_D(\theta) = 0$ in $\mathcal O_{K_D}$. -/
theorem aeval_theta : aeval (theta D) (qpoly D) = 0 := by
  rw [theta, ← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, aeval_omega, map_zero]

/-- **The minimal polynomial of $\theta$ over $\mathbb{Z}$ is $f_D = X^2 - b_D X - a_D$** ($\theta \notin \mathbb{Z}$, so
the minimal polynomial, a monic divisor of $f_D$, has degree $2$). -/
@[kb "cohen1993" "§5.1.1"]
theorem minpoly_theta : minpoly ℤ (theta D) = qpoly D := by
  have hint : IsIntegral ℤ (theta D) := (theta D).isIntegral
  have hdvd := minpoly.isIntegrallyClosed_dvd hint aeval_theta
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) qpoly_monic hdvd ?_).symm
  rw [qpoly_natDegree]
  have hle : (minpoly ℤ (theta D)).natDegree ≤ 2 :=
    qpoly_natDegree (D := D) ▸ natDegree_le_of_dvd hdvd qpoly_monic.ne_zero
  have hpos := minpoly.natDegree_pos hint
  by_contra hlt
  have h1 : (minpoly ℤ (theta D)).natDegree = 1 := by omega
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1
  have := congrArg (fun x : 𝓞 (QField D) => ((orderEquiv D).symm x).im) hc
  simp [theta] at this

/-- **The discriminant of $K_D$ is $D$**: $\{1, \omega\}$ is an integral basis
(`isIntegralClosure`), with trace matrix $\begin{pmatrix} 2 & b_D \\ b_D & b_D^2 + 2a_D\end{pmatrix}$ of
determinant $b_D^2 + 4a_D = D$. -/
@[kb "cohen1993" "§5.1.1, Prop. 5.1.2"]
theorem discr_eq : NumberField.discr (QField D) = D := by
  classical
  rw [← NumberField.discr_eq_discr _ ((basis (qa D) (qb D)).map (orderEquiv D).toLinearEquiv),
    Module.Basis.coe_map, show ⇑(orderEquiv D).toLinearEquiv = ⇑(orderEquiv D) from rfl,
    ← Algebra.discr_eq_discr_of_algEquiv, algDiscr_basis, discr_qa_qb (IsQuadDisc.fund (D := D)).1]

/-- $[K_D : \mathbb{Q}] = 2$. -/
theorem finrank_eq : Module.finrank ℚ (QField D) = 2 := by
  rw [Module.finrank_eq_card_basis (basis (qa D : ℚ) (qb D : ℚ)), Fintype.card_fin]

/-- Under any embedding $\varphi : K_D \to \mathbb{C}$, $(2\varphi(\omega) - b_D)^2 = D$. -/
theorem embedding_sq (φ : QField D →+* ℂ) : (2 * φ ω - qb D) ^ 2 = (D : ℂ) := by
  have h1 : φ ω * φ ω = (qa D : ℂ) + (qb D : ℂ) * φ ω := by
    rw [← map_mul, omega_mul_omega_eq_mk]
    have : (⟨(qa D : ℚ), (qb D : ℚ)⟩ : QField D) = ((qa D : ℚ) : QField D) + ((qb D : ℚ) : QField D) * ω := by
      ext <;> simp
    rw [this, map_add, map_mul, map_ratCast, map_ratCast]; push_cast; ring
  have h2 : ((qb D : ℂ)) ^ 2 + 4 * (qa D : ℂ) = D := by
    have := discr_qa_qb (IsQuadDisc.fund (D := D)).1
    rw [discr_def] at this; exact_mod_cast this
  linear_combination 4 * h1 + h2

open NumberField.InfinitePlace in
/-- For $D < 0$, no embedding $K_D \to \mathbb{C}$ is real: $(2\varphi(\omega) - b_D)^2 = D < 0$. -/
theorem not_isReal_of_neg (hD : D < 0) (φ : QField D →+* ℂ) : ¬ ComplexEmbedding.IsReal φ := by
  intro hφ
  have hz : (φ ω).im = 0 := by
    have := congrArg (fun f : QField D →+* ℂ => f ω) (ComplexEmbedding.isReal_iff.mp hφ)
    simp only [ComplexEmbedding.conjugate_coe_eq] at this
    exact Complex.conj_eq_iff_im.mp this
  have h := congrArg Complex.re (embedding_sq φ)
  simp [sq, hz] at h
  have hD' : (D : ℝ) < 0 := by exact_mod_cast hD
  nlinarith [mul_self_nonneg (2 * (φ ω).re - (qb D : ℝ))]

open NumberField.InfinitePlace in
/-- For $D > 0$, every embedding $K_D \to \mathbb{C}$ is real: $(2\varphi(\omega) - b_D)^2 = D > 0$ forces
$\varphi(\omega) \in \mathbb{R}$. -/
theorem isReal_of_pos (hD : 0 < D) (φ : QField D →+* ℂ) : ComplexEmbedding.IsReal φ := by
  have hw := embedding_sq φ
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  generalize hW : 2 * φ ω - (qb D : ℂ) = w at hre him
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at hre him
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hwim : w.im = 0 := by
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rw [h] at hre; nlinarith [mul_self_nonneg w.im]
    · exact h
  have hz : (φ ω).im = 0 := by
    have := congrArg Complex.im hW
    simp at this; linarith
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← re_smul_add_im_smul x]
  simp only [Algebra.smul_def, mul_one, eq_ratCast, map_add, map_mul, map_ratCast]
  apply Complex.ext <;> simp [hz]

open NumberField.InfinitePlace

/-- **An imaginary quadratic field has no real place**, $r_1 = 0$. -/
@[kb "marcus1977" "Ch. 5"]
theorem nrRealPlaces_of_neg (hD : D < 0) : nrRealPlaces (QField D) = 0 := by
  classical
  rw [nrRealPlaces, Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨w, hw⟩ => not_isReal_of_neg hD _ (isReal_iff.mp hw)⟩

/-- **An imaginary quadratic field has one complex place**, $r_2 = 1$. -/
@[kb "marcus1977" "Ch. 5"]
theorem nrComplexPlaces_of_neg (hD : D < 0) : nrComplexPlaces (QField D) = 1 := by
  have := card_add_two_mul_card_eq_rank (QField D)
  rw [nrRealPlaces_of_neg hD, finrank_eq] at this
  omega

/-- **A real quadratic field has no complex place**, $r_2 = 0$. -/
@[kb "marcus1977" "Ch. 5"]
theorem nrComplexPlaces_of_pos (hD : 0 < D) : nrComplexPlaces (QField D) = 0 := by
  classical
  rw [nrComplexPlaces, Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨w, hw⟩ => (not_isReal_iff_isComplex.mpr hw) (isReal_iff.mpr (isReal_of_pos hD _))⟩

/-- **A real quadratic field has two real places**, $r_1 = 2$. -/
@[kb "marcus1977" "Ch. 5"]
theorem nrRealPlaces_of_pos (hD : 0 < D) : nrRealPlaces (QField D) = 2 := by
  have := card_add_two_mul_card_eq_rank (QField D)
  rw [nrComplexPlaces_of_pos hD, finrank_eq] at this
  omega

open NumberField.Units in
set_option backward.isDefEq.respectTransparency false in
/-- **The roots of unity of a real quadratic field are $\pm 1$**, $w = 2$ (it has a real place, so no root of unity
of order $> 2$; the argument of Mathlib's `torsionOrder_eq_two_of_odd_finrank`). -/
@[kb "marcus1977" "Ch. 5"]
theorem torsionOrder_of_pos (hD : 0 < D) : torsionOrder (QField D) = 2 := by
  classical
  have hr : 0 < nrRealPlaces (QField D) := by rw [nrRealPlaces_of_pos hD]; norm_num
  have key : ∀ x : torsion (QField D), (x : (𝓞 (QField D))ˣ) = 1 ∨ (x : (𝓞 (QField D))ˣ) = -1 := by
    intro x
    by_cases! hc : 2 < orderOf (x : (𝓞 (QField D))ˣ)
    · rw [← orderOf_units, ← orderOf_submonoid] at hc
      linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
        (IsPrimitiveRoot.orderOf (x.1 : QField D))]
    · interval_cases hi : orderOf (x : (𝓞 (QField D))ˣ)
      · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
      · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
      · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
        simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]
  let := Fintype.ofFinite (torsion (QField D))
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact key x

open NumberField.Units in
/-- **The regulator of an imaginary quadratic field is $1$** (the unit rank is $r_1 + r_2 - 1 = 0$, and the
regulator is the determinant of an empty matrix). -/
@[kb "marcus1977" "Ch. 5"]
theorem regulator_of_neg (hD : D < 0) : regulator (QField D) = 1 := by
  classical
  have hrank : rank (QField D) = 0 := by
    rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_neg hD, nrComplexPlaces_of_neg hD]
  have : IsEmpty (Fin (rank (QField D))) := by rw [hrank]; infer_instance
  have hcard : Fintype.card (InfinitePlace (QField D)) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_neg hD, nrComplexPlaces_of_neg hD]
  have hs : ∀ a b : InfinitePlace (QField D), a = b := Fintype.card_le_one_iff.mp hcard.le
  have : IsEmpty {w : InfinitePlace (QField D) // w ≠ dirichletUnitTheorem.w₀} :=
    ⟨fun ⟨w, hw⟩ => hw (hs _ _)⟩
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

open NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **The regulator of a real quadratic field is $\log\varepsilon$**: for the fundamental unit $\varepsilon$
(`fundSystem`, unit rank $1$) and *either* real place $w$, $R = |\log w(\varepsilon)|$ (the two values $\log w(\varepsilon)$
are opposite, as $\sum_w \log w(\varepsilon) = \log|N\varepsilon| = 0$). With $\varepsilon > 1$ under a real embedding this
is $R = \log\varepsilon$. -/
@[kb "marcus1977" "Ch. 5"]
theorem regulator_of_pos (hD : 0 < D) (i : Fin (rank (QField D))) (w : InfinitePlace (QField D)) :
    regulator (QField D) = |Real.log (w (fundSystem (QField D) i : QField D))| := by
  classical
  set K := QField D
  have hreal : ∀ v : InfinitePlace K, IsReal v := fun v => isReal_iff.mpr (isReal_of_pos hD _)
  have hmult : ∀ v : InfinitePlace K, mult v = 1 := fun v => (hreal v).mult_eq_one
  have hcard : Fintype.card (InfinitePlace K) = 2 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_pos hD, nrComplexPlaces_of_pos hD]
  have hrank : rank K = 1 := by rw [rank, hcard]
  -- the place other than w₀
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : InfinitePlace K, w₁ ≠ w₀ := by
    by_contra! h
    have : Fintype.card (InfinitePlace K) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
    omega
  have hall : ∀ v : InfinitePlace K, v = w₀ ∨ v = w₁ := by
    intro v
    by_contra! h
    have : ({w₀, w₁, v} : Finset (InfinitePlace K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hw₁.symm, h.1.symm]),
      Finset.card_pair (Ne.symm h.2)] at this
    omega
  have huniq : Unique {v : InfinitePlace K // v ≠ w₀} :=
    { default := ⟨w₁, hw₁⟩
      uniq := fun ⟨v, hv⟩ => Subtype.ext ((hall v).resolve_left hv) }
  have hrank' : rank (QField D) = 1 := hrank
  have hi : ∀ j : Fin (rank K), j = i := fun j => Fin.ext (by
    have h1 := j.2; have h2 := i.2; omega)
  set ε := fundSystem K i
  -- log w₀ ε = - log w₁ ε
  have hsum := sum_mult_mul_log ε
  have hsplit : ∑ v : InfinitePlace K, (mult v : ℝ) * Real.log (v (ε : K)) =
      Real.log (w₀ (ε : K)) + Real.log (w₁ (ε : K)) := by
    rw [show (Finset.univ : Finset (InfinitePlace K)) = {w₀, w₁} from
      (Finset.eq_univ_of_forall (s := ({w₀, w₁} : Finset (InfinitePlace K)))
        fun v => by rcases hall v with h | h <;> simp [h]).symm,
      Finset.sum_pair (Ne.symm hw₁), hmult, hmult]
    simp
  have hreg : regulator K = |Real.log (w₁ (ε : K))| := by
    rw [regulator_eq_det', Matrix.det_unique]
    simp only [Matrix.of_apply, logEmbedding_component]
    rw [show (default : {v : InfinitePlace K // v ≠ w₀}) = ⟨w₁, hw₁⟩ from (huniq.uniq _).symm, hmult, hi ((equivFinRank K).symm _)]
    simp only [Nat.cast_one, one_mul]
    rfl
  rcases hall w with rfl | rfl
  · rw [hreg]
    have : Real.log (w₀ (ε : K)) = - Real.log (w₁ (ε : K)) := by linarith
    rw [this, abs_neg]
  · exact hreg

end QuadFormsKB.Binary
