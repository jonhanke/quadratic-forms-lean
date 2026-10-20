import QuadFormsKB.HilbertModular.ThetaReciprocity
import QuadFormsKB.HilbertModular.GaussSumO

/-!
# Theta series over a totally real field VII: the character $\chi_Q$ and $\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$

Notation of `ThetaGamma0.lean`, `ThetaReciprocity.lean`, `GaussSumO.lean`. Let $Q$ be a totally positive definite form over
$\mathcal{O}_F$ of even rank $n = 2k$, $H$ its Hessian, $\mathfrak N \ne 0$ a level, and $D = (-1)^k\det H$.

**Good elements.** $a \in \mathcal{O}_F$ is *good* (`IsGoodF`) if $a$ is prime to $2\det H$ and to the different $\mathfrak d$.

**Evaluation** (`thetaMultG_eq_psiF`): for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ with $c \ne 0$ and $a$ good,
$$m_Q(\gamma) = \Psi(a) = \operatorname{sgn}\big(N_{F/\mathbb{Q}}(a)\big)^k\Big(\frac{D}{(a)}\Big)\qquad(\texttt{psiF}),$$
a sign times the Jacobi symbol of $\mathcal{O}_F$. *Proof:* reciprocity $M_Q(a, c) = N(a)^{-k}G^\#(-c, a)$ (`thetaMultF_reciprocity`), and the
dual Gauss sum modulo the good element $a$ is $(\frac{D}{(a)})N((a))^k$ (`gsQ_eval` for $S = \operatorname{adj}H$, the character
$x \mapsto e(\operatorname{Tr}(\beta x/a))$, which is primitive because $a$ is prime to $\mathfrak d$).

**Independence of the representative** (`thetaMultG_congr`): $m_Q(\gamma)$ depends only on $a \bmod \mathfrak N$. *Proof* (no Dirichlet
or Hecke theorem on primes in progressions is needed): left multiplication by $T(t)$ and $L(s) = \begin{pmatrix}1&0\\s&1\end{pmatrix}$,
$s \in \mathfrak N$, does not change $m_Q$ (`thetaMultG_transl_mul`, `thetaMultG_lowerU`), and moves $a$ within $a + c\mathcal{O}_F$
to a good element (`exists_add_mem_sup_eq_top`, a Chinese remainder argument). For good $x \equiv x' \pmod{\mathfrak N}$ which
are coprime, the column $(x, x' - x)$ completes to $\gamma_1 \in \Gamma_0(\mathfrak N)$, and $T(1)\gamma_1$ has first column $(x', x' - x)$,
so $\Psi(x) = m_Q(\gamma_1) = m_Q(T(1)\gamma_1) = \Psi(x')$; a third good element coprime to both links any two. This is
quadratic reciprocity over $F$, obtained from the theta function (as in Hecke's proof).

**The character** (`thetaCharF`): $\chi_Q(d \bmod \mathfrak N) = m_Q(\gamma)$ for any $\gamma \in \Gamma_0(\mathfrak N)$ with lower right entry $d$; a
quadratic character of $(\mathcal{O}_F/\mathfrak N)^\times$ (`thetaCharF_isQuadratic`) with
$$\chi_Q(d \bmod \mathfrak N) = \operatorname{sgn}\big(N(d')\big)^k\Big(\frac{(-1)^k\det H}{(d')}\Big)\quad\text{for every good } d' \equiv d \pmod{\mathfrak N}
\qquad(\texttt{thetaCharF\_eq\_jacobi}),$$
i.e. $\chi_Q$ is the Hecke character of $F(\sqrt D)/F$ (with signature $\operatorname{sgn}^k$ at the real places), see the docs.

**Main results:** `thetaQ_slash_gamma0_char`: $\theta_Q\,|_k\,\gamma = \chi_Q(d)\,\theta_Q$ for all $\gamma \in \Gamma_0(\mathfrak N)$;
`thetaQ_mem_modularFormChar`: $\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$ for $[F:\mathbb{Q}] \ge 2$ (Koecher).
-/

open Matrix NumberField NumberField.InfinitePlace Complex Filter Topology
open scoped Real nonZeroDivisors MatrixGroups ModularForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### The additive character $x \mapsto e(\operatorname{Tr}(x/a))$ of $\mathcal{O}_F/a$ -/

lemma finite_quot_of_ne_bot : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → Finite (𝓞 F ⧸ I) :=
  fun I hI => Ideal.finiteQuotientOfFreeOfNeBot I hI

lemma algebraMap_div_mem_one {a y : 𝓞 F} (ha : a ≠ 0) (h : y ∈ Ideal.span {a}) :
    algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F a ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp h
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h0 => ha (FaithfulSMul.algebraMap_injective (𝓞 F) F
    (by rw [map_zero]; exact h0))
  rw [map_mul, mul_div_assoc, div_self haF, mul_one]
  exact algebraMap_mem_one t

/-- **The additive character** $\psi_a(x) = e(\operatorname{Tr}_{F/\mathbb{Q}}(x/a))$ of $\mathcal{O}_F/a$. -/
def addCharMod (a : 𝓞 F) (ha : a ≠ 0) : AddChar (𝓞 F ⧸ Ideal.span {a}) ℂ where
  toFun r := cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
    (algebraMap (𝓞 F) F (qlift r) / algebraMap (𝓞 F) F a) : ℚ) : ℂ))
  map_zero_eq_one' := by
    refine cexp_trace_eq_one (mem_invDifferent_of_mem_one (algebraMap_div_mem_one ha ?_))
    rw [← Ideal.Quotient.eq_zero_iff_mem, mk_qlift]
  map_add_eq_mul' r r' := by
    obtain ⟨t, ht⟩ := exists_eq_add_mul_of_mk_eq (show Ideal.Quotient.mk (Ideal.span {a})
      (qlift (r + r')) = Ideal.Quotient.mk _ (qlift r + qlift r') by
        rw [mk_qlift, map_add, mk_qlift, mk_qlift])
    rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← map_add, ← add_div, ← map_add, ht,
      map_add, add_div, cexp_trace_add_of_mem]
    refine mem_invDifferent_of_mem_one (algebraMap_div_mem_one ha ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)

lemma addCharMod_mk {a : 𝓞 F} (ha : a ≠ 0) (y : 𝓞 F) :
    addCharMod a ha (Ideal.Quotient.mk _ y) = cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
      (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F a) : ℚ) : ℂ)) := by
  show cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
    (algebraMap (𝓞 F) F (qlift (Ideal.Quotient.mk _ y)) / algebraMap (𝓞 F) F a) : ℚ) : ℂ)) = _
  obtain ⟨t, ht⟩ := exists_eq_add_mul_of_mk_eq (show Ideal.Quotient.mk (Ideal.span {a})
    (qlift (Ideal.Quotient.mk (Ideal.span {a}) y)) = Ideal.Quotient.mk (Ideal.span {a}) y from
      mk_qlift _)
  rw [ht, map_add, add_div, cexp_trace_add_of_mem]
  exact mem_invDifferent_of_mem_one (algebraMap_div_mem_one ha
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)))

/-- $\psi_a$ is primitive when $a$ is prime to the different. -/
theorem addCharMod_isPrimitive {a : 𝓞 F} (ha : a ≠ 0)
    (had : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) : (addCharMod a ha).IsPrimitive := by
  intro r hr h
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  apply hr
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h0 => ha (FaithfulSMul.algebraMap_injective (𝓞 F) F
    (by rw [map_zero]; exact h0))
  -- `y / a ∈ 𝔡⁻¹`
  have hδ : algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F a ∈ invDifferent F := by
    rw [invDifferent, FractionalIdeal.mem_dual (one_ne_zero)]
    intro z hz
    obtain ⟨z', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
    have h1 := congrArg (fun χ : AddChar (𝓞 F ⧸ Ideal.span {a}) ℂ => χ (Ideal.Quotient.mk _ z')) h
    simp only [AddChar.mulShift_apply, AddChar.one_apply, ← map_mul, addCharMod_mk] at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    have h2 : ((Algebra.trace ℚ F (algebraMap (𝓞 F) F (y * z') / algebraMap (𝓞 F) F a) : ℚ) : ℂ) =
        m := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hpi
      rw [hm]; ring
    simp only [Algebra.traceForm_apply, eq_intCast]
    have h3 : algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F z' =
        algebraMap (𝓞 F) F (y * z') / algebraMap (𝓞 F) F a := by rw [map_mul]; ring
    rw [h3]
    exact_mod_cast h2.symm
  have h1 := mem_one_of_mul_mem had hδ (by
    rw [mul_div_cancel₀ _ haF]; exact algebraMap_mem_one y)
  obtain ⟨t, ht⟩ := (FractionalIdeal.mem_one_iff _).mp h1
  have : y = a * t := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ht, mul_div_cancel₀ _ haF]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)

/-! ### The dual Gauss sum as a Gauss sum of $\operatorname{adj}H$ modulo $a$ -/

lemma quadQ_mk (I : Ideal (𝓞 F)) (S : Matrix (Fin n) (Fin n) (𝓞 F)) (x : Fin n → 𝓞 F) :
    quadQ I S (fun i => Ideal.Quotient.mk I (x i)) = Ideal.Quotient.mk I (x ⬝ᵥ S *ᵥ x) := by
  simp [quadQ, dotProduct, mulVec, map_sum, map_mul]

lemma hessian_adjugate_transpose (Q : QuadForm (𝓞 F) n) : (Q.hessian.adjugate)ᵀ = Q.hessian.adjugate := by
  rw [adjugate_transpose, QuadForm.hessian, transpose_add, transpose_transpose, add_comm]

/-- $Q^\#(x) = \dfrac{x^{\mathsf T}(\operatorname{adj}H)x}{2\det H}$ for $x \in \mathcal{O}_F^n$. -/
lemma qDual_vecO_eq {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (x : Fin n → 𝓞 F) :
    qDual Q (vecO x) = algebraMap (𝓞 F) F (x ⬝ᵥ Q.hessian.adjugate *ᵥ x) /
      (2 * algebraMap (𝓞 F) F Q.hessian.det) := by
  have hdet : (hessF Q).det = algebraMap (𝓞 F) F Q.hessian.det :=
    (RingHom.map_det (algebraMap (𝓞 F) F) Q.hessian).symm
  have hadj : (hessF Q).adjugate = Q.hessian.adjugate.map (algebraMap (𝓞 F) F) :=
    ((algebraMap (𝓞 F) F).map_adjugate Q.hessian).symm
  have hd0 : algebraMap (𝓞 F) F Q.hessian.det ≠ 0 := by rw [← hdet]; exact hessF_det_ne_zero hQ
  rw [qDual_eq hQ, Matrix.inv_def, Ring.inverse_eq_inv, hdet, hadj, smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  have : vecO x ⬝ᵥ Q.hessian.adjugate.map (algebraMap (𝓞 F) F) *ᵥ vecO x =
      algebraMap (𝓞 F) F (x ⬝ᵥ Q.hessian.adjugate *ᵥ x) := by
    simp [vecO, dotProduct, mulVec, map_sum, map_mul]
  rw [this]
  field_simp

/-- **The dual Gauss sum is a Gauss sum of $\operatorname{adj}H$**: if $s\cdot2\det H = 1 + am$ then
$G^\#(-c, a) = \sum_{r\in(\mathcal{O}_F/a)^n}\psi_a\big(-cs\cdot r^{\mathsf T}(\operatorname{adj}H)r\big)$. -/
theorem gaussSumDualF_eq_gsQ {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {𝔑 : Ideal (𝓞 F)}
    (hlev : IsThetaLevelF Q 𝔑) {a c : 𝓞 F} (ha0 : a ≠ 0) (hc : c ∈ 𝔑) {s m : 𝓞 F}
    (hs : s * (2 * Q.hessian.det) = 1 + a * m) [Fintype (𝓞 F ⧸ Ideal.span {a})] :
    gaussSumDualF Q (-c) a = gsQ (Ideal.span {a}) Q.hessian.adjugate
      (AddChar.mulShift (addCharMod a ha0) (Ideal.Quotient.mk _ (-c * s))) := by
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h0 => ha0 (FaithfulSMul.algebraMap_injective (𝓞 F) F
    (by rw [map_zero]; exact h0))
  have hdet : (hessF Q).det = algebraMap (𝓞 F) F Q.hessian.det :=
    (RingHom.map_det (algebraMap (𝓞 F) F) Q.hessian).symm
  have hd0 : algebraMap (𝓞 F) F Q.hessian.det ≠ 0 := by rw [← hdet]; exact hessF_det_ne_zero hQ
  rw [gaussSumDualF, finsum_eq_sum_of_fintype, gsQ]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : r = fun i => Ideal.Quotient.mk (Ideal.span {a}) (qlift (r i)) := by
    funext i; rw [mk_qlift]
  conv_rhs => rw [hr]
  rw [quadQ_mk, AddChar.mulShift_apply, ← map_mul, addCharMod_mk]
  set x : Fin n → 𝓞 F := fun i => qlift (r i)
  have hsF := congrArg (algebraMap (𝓞 F) F) hs
  simp only [map_mul, map_add, map_one, map_ofNat] at hsF
  have key : algebraMap (𝓞 F) F (-c) * qDual Q (vecO x) / algebraMap (𝓞 F) F a =
      algebraMap (𝓞 F) F (-c * s * (x ⬝ᵥ Q.hessian.adjugate *ᵥ x)) / algebraMap (𝓞 F) F a +
        algebraMap (𝓞 F) F m * (algebraMap (𝓞 F) F c * qDual Q (vecO x)) := by
    rw [qDual_vecO_eq hQ x]
    simp only [map_mul, map_neg]
    field_simp
    linear_combination (algebraMap (𝓞 F) F c * algebraMap (𝓞 F) F
      (x ⬝ᵥ Q.hessian.adjugate *ᵥ x)) * hsF
  rw [key, cexp_trace_add_of_mem]
  exact algebraMap_mul_mem_invDifferent _ (hlev c hc _ fun i => algebraMap_mem_invDifferent _)

/-! ### Evaluation of the dual Gauss sum at a good modulus -/

lemma legendreO_mul_sq {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) (D : 𝓞 F) {u : 𝓞 F}
    (hu : u ∉ 𝔭) : legendreO (D * u ^ 2) 𝔭 = legendreO D 𝔭 := by
  classical
  letI : Fintype (𝓞 F ⧸ 𝔭) := @Fintype.ofFinite _ (finite_quot_of_ne_bot 𝔭 h0)
  letI := Ideal.Quotient.field 𝔭
  rw [← quadraticChar_mk_eq_legendreO, ← quadraticChar_mk_eq_legendreO, map_mul, map_mul, map_pow,
    quadraticChar_sq_one' (fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)), mul_one]

lemma jacobiO_mul_sq (D : 𝓞 F) {a u : 𝓞 F}
    (hu : Ideal.span {a} ⊔ Ideal.span {u} = ⊤) :
    jacobiO (D * u ^ 2) (Ideal.span {a}) = jacobiO D (Ideal.span {a}) := by
  unfold jacobiO
  congr 1
  refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 h𝔭
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔭
  have hle : Ideal.span {a} ≤ 𝔭 := Ideal.dvd_iff_le.mp hdvd
  have h0 : 𝔭 ≠ ⊥ := hp.ne_zero
  haveI : 𝔭.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal h0
  refine legendreO_mul_sq h0 D fun hu𝔭 => ?_
  have : Ideal.span {a} ⊔ Ideal.span {u} ≤ 𝔭 :=
    sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hu𝔭)
  rw [hu] at this
  exact (Ideal.isPrime_of_prime hp).ne_top (top_le_iff.mp this)

lemma isCoprime_of_sup_span {a b : 𝓞 F} (h : Ideal.span {a} ⊔ Ideal.span {b} = ⊤) : IsCoprime a b :=
  (Ideal.isCoprime_span_singleton_iff a b).mp ((Ideal.isCoprime_iff_sup_eq).mpr h)

lemma sup_span_of_isCoprime {a b : 𝓞 F} (h : IsCoprime a b) : Ideal.span {a} ⊔ Ideal.span {b} = ⊤ :=
  (Ideal.isCoprime_iff_sup_eq).mp ((Ideal.isCoprime_span_singleton_iff a b).mpr h)

/-- **The dual Gauss sum at a good modulus**: for $a \ne 0$ prime to $2\det H$ and $\mathfrak d$, $c \in \mathfrak N$ prime to $a$,
$G^\#(-c, a) = (\frac{(-1)^k\det H}{(a)})\,N((a))^k$, independent of $c$. -/
theorem gaussSumDualF_eval {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {a c : 𝓞 F} (ha0 : a ≠ 0)
    (had : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤)
    (ha2 : Ideal.span {a} ⊔ Ideal.span {2 * Q.hessian.det} = ⊤) (hc : c ∈ 𝔑)
    (hac : Ideal.span {a} ⊔ Ideal.span {c} = ⊤) :
    gaussSumDualF Q (-c) a = (jacobiO ((-1) ^ k * Q.hessian.det) (Ideal.span {a}) : ℂ) *
      (Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℂ) ^ k := by
  classical
  letI : Fintype (𝓞 F ⧸ Ideal.span {a}) :=
    @Fintype.ofFinite _ (finite_quot_of_ne_bot _ (by simpa using ha0))
  -- `s · 2 det H ≡ 1 (mod a)`
  obtain ⟨u, s, hus⟩ := isCoprime_of_sup_span ha2
  have hs : s * (2 * Q.hessian.det) = 1 + a * (-u) := by linear_combination hus
  rw [gaussSumDualF_eq_gsQ hQ hlev ha0 hc hs]
  have hcopa : IsCoprime a (2 * Q.hessian.det) := isCoprime_of_sup_span ha2
  have hcop' : Ideal.span {a} ⊔ Ideal.span {2 * Q.hessian.adjugate.det} = ⊤ := by
    refine sup_span_of_isCoprime ?_
    rw [det_adjugate]
    exact IsCoprime.mul_right hcopa.of_mul_right_left (hcopa.of_mul_right_right.pow_right)
  -- the character is primitive
  have hβ : IsUnit (Ideal.Quotient.mk (Ideal.span {a}) (-c * s)) := by
    have h1 : IsCoprime a (-c * s) := by
      refine IsCoprime.mul_right (IsCoprime.neg_right (isCoprime_of_sup_span hac)) ?_
      exact ⟨u, 2 * Q.hessian.det, by linear_combination hus⟩
    obtain ⟨x, y, hxy⟩ := h1
    refine IsUnit.of_mul_eq_one (b := Ideal.Quotient.mk _ y) ?_
    rw [← map_mul, mul_comm, show y * (-c * s) = 1 - x * a by linear_combination hxy, map_sub,
      map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ _
        (Ideal.mem_span_singleton_self a)), sub_zero]
  have hψ : (AddChar.mulShift (addCharMod a ha0) (Ideal.Quotient.mk _ (-c * s))).IsPrimitive := by
    intro r hr
    rw [AddChar.mulShift_mulShift]
    exact addCharMod_isPrimitive ha0 had (by
      intro h; exact hr ((hβ.mul_right_eq_zero).mp h))
  rw [gsQ_eval finite_quot_of_ne_bot (hessian_adjugate_transpose Q) hn (Ideal.span {a})
    (by simpa using ha0) hcop' _ hψ]
  congr 2
  -- `(-1)^k det(adj H) = (-1)^k det H · (det H^(k-1))^2`
  rw [det_adjugate, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hn0 : n = 0 := by omega
    subst hn0
    simp [Matrix.det_isEmpty]
  · have : (-1) ^ k * Q.hessian.det ^ (n - 1) =
        (-1) ^ k * Q.hessian.det * (Q.hessian.det ^ (k - 1)) ^ 2 := by
      rw [← pow_mul, mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [this, jacobiO_mul_sq _ (sup_span_of_isCoprime hcopa.of_mul_right_right.pow_right)]

/-! ### Moving an element off finitely many primes (Chinese remainder theorem) -/

/-- **Avoidance**: if $(x) + I = 1$ and $\mathfrak c \ne 0$, there is $s \in I$ with $(x + s) + \mathfrak c = 1$. -/
theorem exists_add_mem_sup_eq_top {x : 𝓞 F} {I 𝔠 : Ideal (𝓞 F)} (hxI : Ideal.span {x} ⊔ I = ⊤)
    (h𝔠 : 𝔠 ≠ ⊥) : ∃ s ∈ I, Ideal.span {x + s} ⊔ 𝔠 = ⊤ := by
  classical
  set P := (UniqueFactorizationMonoid.normalizedFactors 𝔠).toFinset with hP
  have hprime : ∀ 𝔭 ∈ P, Prime 𝔭 := fun 𝔭 h𝔭 =>
    UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 (Multiset.mem_toFinset.mp h𝔭)
  -- local choices
  have hloc : ∀ 𝔭 : P, ∃ t ∈ I, x + t ∉ (𝔭 : Ideal (𝓞 F)) := by
    rintro ⟨𝔭, h𝔭⟩
    have hp := Ideal.isPrime_of_prime (hprime 𝔭 h𝔭)
    by_cases hx : x ∈ 𝔭
    · have hI : ¬ I ≤ 𝔭 := by
        intro hI
        have : Ideal.span {x} ⊔ I ≤ 𝔭 := sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hx) hI
        rw [hxI] at this
        exact hp.ne_top (top_le_iff.mp this)
      obtain ⟨t, htI, ht𝔭⟩ := Set.not_subset.mp hI
      refine ⟨t, htI, fun h => ht𝔭 ?_⟩
      have := Ideal.sub_mem _ h hx
      simpa using this
    · exact ⟨0, I.zero_mem, by simpa using hx⟩
  choose t htI ht using hloc
  -- idempotents
  have heps : ∀ 𝔭 : P, ∃ ε : 𝓞 F, ∀ (𝔮 : Ideal (𝓞 F)) (h𝔮 : 𝔮 ∈ P),
      ε - (if 𝔮 = 𝔭 then 1 else 0) ∈ 𝔮 ^ 1 := by
    intro 𝔭
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := P) id (fun _ => 1)
      (fun i hi => hprime i hi) (fun i _ j _ hij => hij) (fun 𝔮 => if (𝔮 : Ideal (𝓞 F)) = 𝔭 then 1 else 0)
    exact ⟨y, fun 𝔮 h𝔮 => hy 𝔮 h𝔮⟩
  choose ε hε using heps
  set s : 𝓞 F := ∑ 𝔭 : P, t 𝔭 * ε 𝔭 with hs
  refine ⟨s, Submodule.sum_mem _ fun 𝔭 _ => Ideal.mul_mem_right _ _ (htI 𝔭), ?_⟩
  -- `x + s ∉ 𝔮` for every prime factor `𝔮` of `𝔠`
  have hnot : ∀ 𝔮 : P, x + s ∉ (𝔮 : Ideal (𝓞 F)) := by
    intro 𝔮 h
    apply ht 𝔮
    have hdiff : s - t 𝔮 ∈ (𝔮 : Ideal (𝓞 F)) := by
      have : s - t 𝔮 = ∑ 𝔭 : P, t 𝔭 * (ε 𝔭 - if (𝔮 : Ideal (𝓞 F)) = 𝔭 then 1 else 0) := by
        rw [hs]
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
        congr 1
        simp only [← Subtype.ext_iff, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [this]
      refine Submodule.sum_mem _ fun 𝔭 _ => Ideal.mul_mem_left _ _ ?_
      have := hε 𝔭 𝔮 𝔮.2
      rw [pow_one] at this
      convert this using 2
    have := Ideal.sub_mem _ h hdiff
    rwa [show x + s - (s - t 𝔮) = x + t 𝔮 by ring] at this
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hM0 : M ≠ ⊥ := fun h => h𝔠 (le_bot_iff.mp (h ▸ le_sup_right.trans hle))
  have hMP : M ∈ P := by
    rw [hP, Multiset.mem_toFinset, UniqueFactorizationMonoid.mem_normalizedFactors_iff h𝔠]
    exact ⟨Ideal.prime_of_isPrime hM0 hM.isPrime, Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)⟩
  exact hnot ⟨M, hMP⟩ (le_sup_left.trans hle (Ideal.mem_span_singleton_self _))

/-! ### Good elements and the evaluation of the multiplier -/

/-- The ideal $(2\det H)\,\mathfrak d$ of bad primes ($\mathfrak d$ = `differentIdeal ℤ (𝓞 F)`). -/
@[kb "hecke1923" "§§54–58 [unverified]"]
def goodIdealF (Q : QuadForm (𝓞 F) n) : Ideal (𝓞 F) :=
  Ideal.span {2 * Q.hessian.det} * differentIdeal ℤ (𝓞 F)

/-- **Good elements**: $a \in \mathcal{O}_F$ prime to $2\det H$ and to the different $\mathfrak d$ (`goodIdealF`). -/
@[kb "hecke1923" "§§54–58 (moduli prime to 2 and the discriminant) [unverified]"]
def IsGoodF (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) : Prop := Ideal.span {a} ⊔ goodIdealF Q = ⊤

lemma IsGoodF.different {Q : QuadForm (𝓞 F) n} {a : 𝓞 F} (h : IsGoodF Q a) :
    Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤ :=
  top_le_iff.mp (h ▸ sup_le_sup_left (Ideal.mul_le_left (I := differentIdeal ℤ (𝓞 F))
    (J := Ideal.span {2 * Q.hessian.det}) |>.trans_eq' (mul_comm _ _)) _)

lemma IsGoodF.two_det {Q : QuadForm (𝓞 F) n} {a : 𝓞 F} (h : IsGoodF Q a) :
    Ideal.span {a} ⊔ Ideal.span {2 * Q.hessian.det} = ⊤ :=
  top_le_iff.mp (h ▸ sup_le_sup_left (Ideal.mul_le_left (I := Ideal.span {2 * Q.hessian.det})
    (J := differentIdeal ℤ (𝓞 F))) _)

lemma span_two_ne_top : Ideal.span {(2 : 𝓞 F)} ≠ ⊤ := by
  intro h
  have h1 := congrArg Ideal.absNorm h
  rw [Ideal.absNorm_top, Ideal.absNorm_span_singleton,
    show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have : (2 : ℤ) ^ Module.finrank ℤ (𝓞 F) ≠ 1 ∧ (2 : ℤ) ^ Module.finrank ℤ (𝓞 F) ≠ -1 := by
    constructor
    · exact (one_lt_pow₀ (by norm_num) hd.ne').ne'
    · have : (0 : ℤ) < 2 ^ Module.finrank ℤ (𝓞 F) := by positivity
      omega
  rcases Int.natAbs_eq_iff.mp h1 with h2 | h2 <;> simp_all

lemma IsGoodF.ne_zero {Q : QuadForm (𝓞 F) n} {a : 𝓞 F} (h : IsGoodF Q a) : a ≠ 0 := by
  rintro rfl
  have h1 : goodIdealF Q ≤ Ideal.span {(2 : 𝓞 F)} := by
    refine (Ideal.mul_le_right (I := differentIdeal ℤ (𝓞 F)) (J := Ideal.span {2 * Q.hessian.det})
      |>.trans_eq' (mul_comm _ _)).trans ?_
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2))
  rw [IsGoodF, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq] at h
  exact span_two_ne_top (top_le_iff.mp (h ▸ h1))

lemma hessian_det_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) : Q.hessian.det ≠ 0 := by
  intro h
  apply hessF_det_ne_zero hQ
  rw [show (hessF Q).det = algebraMap (𝓞 F) F Q.hessian.det from
    (RingHom.map_det (algebraMap (𝓞 F) F) Q.hessian).symm, h, map_zero]

lemma goodIdealF_ne_bot {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) : goodIdealF Q ≠ ⊥ := by
  rw [goodIdealF]
  refine mul_ne_zero ?_ differentIdeal_ne_bot
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero two_ne_zero (hessian_det_ne_zero hQ)

/-- **The value of the multiplier at a good $a$**: $\Psi(a) = N(a)^{-k}\big(\frac{(-1)^k\det H}{(a)}\big)N((a))^k$,
$N(a) = \prod_v\varphi_v(a)$, $N((a)) = |\mathcal{O}_F/a|$. It equals $\operatorname{sgn}(N(a))^k(\frac{D}{(a)}) \in \{\pm1\}$ (`psiF_sq`). -/
@[kb "hecke1923" "§§54–58, values of the theta multiplier [unverified]"]
def psiF (Q : QuadForm (𝓞 F) n) (k : ℕ) (a : 𝓞 F) : ℂ :=
  ((∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ k)⁻¹ *
    (jacobiO ((-1) ^ k * Q.hessian.det) (Ideal.span {a}) : ℂ) *
      (Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℂ) ^ k

lemma sl2O_col_coprime (γ : SL(2, 𝓞 F)) : Ideal.span {γ 0 0} ⊔ Ideal.span {γ 1 0} = ⊤ :=
  sup_span_of_isCoprime ⟨γ 1 1, -γ 0 1, by linear_combination sl2O_det γ⟩

/-- **Evaluation of the multiplier** at a good upper-left entry: for $\gamma \in \Gamma_0(\mathfrak N)$ with $c \ne 0$ and $a$ good,
$m_Q(\gamma) = \Psi(a)$. -/
theorem thetaMultG_eq_psiF {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) (hc : γ 1 0 ≠ 0) (hgood : IsGoodF Q (γ 0 0)) :
    thetaMultG Q k γ = psiF Q k (γ 0 0) := by
  simp only [thetaMultG, hc, ↓reduceIte]
  rw [thetaMultF_reciprocity hQ hn hlev h𝔑 hgood.ne_zero hgood.different hc hγ,
    gaussSumDualF_eval hQ hn hlev hgood.ne_zero hgood.different hgood.two_det hγ
      (sl2O_col_coprime γ), psiF]
  ring

/-! ### $m_Q$ depends only on $a \bmod \mathfrak N$ -/

/-- The translation $T(t)$ as an element of $\mathrm{SL}_2(\mathcal{O}_F)$. -/
def translO (t : 𝓞 F) : SL(2, 𝓞 F) := ⟨!![1, t; 0, 1], by simp [det_fin_two_of]⟩

lemma translO_mul_00 (t : 𝓞 F) (γ : SL(2, 𝓞 F)) : (translO t * γ) 0 0 = γ 0 0 + t * γ 1 0 := by
  rw [sl2_mul_apply]; simp [translO]
lemma translO_mul_10 (t : 𝓞 F) (γ : SL(2, 𝓞 F)) : (translO t * γ) 1 0 = γ 1 0 := by
  rw [sl2_mul_apply]; simp [translO]
lemma lowerU_mul_00 (s : 𝓞 F) (γ : SL(2, 𝓞 F)) : (lowerU s * γ) 0 0 = γ 0 0 := by
  rw [sl2_mul_apply]; simp [lowerU]
lemma lowerU_mul_10 (s : 𝓞 F) (γ : SL(2, 𝓞 F)) : (lowerU s * γ) 1 0 = s * γ 0 0 + γ 1 0 := by
  rw [sl2_mul_apply]; simp [lowerU]

lemma translO_mem (𝔑 : Ideal (𝓞 F)) (t : 𝓞 F) : translO t ∈ Gamma0R 𝔑 := by
  show (translO t) 1 0 ∈ 𝔑; simp [translO]

lemma lowerU_mem {𝔑 : Ideal (𝓞 F)} {s : 𝓞 F} (hs : s ∈ 𝔑) : lowerU s ∈ Gamma0R 𝔑 := hs

/-- $m_Q(L(s)) = 1$ for $s \in \mathfrak N$ (reciprocity with $a = 1$). -/
theorem thetaMultG_lowerU {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {s : 𝓞 F}
    (hs : s ∈ 𝔑) : thetaMultG Q k (lowerU s) = 1 := by
  by_cases hs0 : s = 0
  · subst hs0
    have : lowerU (0 : 𝓞 F) = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [lowerU]
    rw [this]; simp [thetaMultG]
  · have hl : (lowerU s) 1 0 = s := rfl
    simp only [thetaMultG, hl, hs0, ↓reduceIte]
    rw [show (lowerU s) 0 0 = 1 from rfl, thetaMultF_reciprocity hQ hn hlev h𝔑 one_ne_zero
      (by rw [Ideal.span_singleton_one, top_sup_eq]) hs0 hs, gaussSumDualF_one hlev (𝔑.neg_mem hs)]
    simp

/-- $m_Q(T(t)\gamma) = m_Q(\gamma)$ and $m_Q(L(s)\gamma) = m_Q(\gamma)$. -/
lemma thetaMultG_translO_mul {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) (t : 𝓞 F) : thetaMultG Q k (translO t * γ) = thetaMultG Q k γ :=
  thetaMultG_transl_mul hQ hn hlev hγ t

lemma thetaMultG_lowerU_mul {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) {s : 𝓞 F} (hs : s ∈ 𝔑) :
    thetaMultG Q k (lowerU s * γ) = thetaMultG Q k γ := by
  rw [thetaMultG_mul hQ hn hlev (lowerU_mem hs) hγ, thetaMultG_lowerU hQ hn hlev h𝔑 hs, one_mul]

/-- A column $(x, y)$ with $(x) + (y) = 1$, $y \in \mathfrak N$, is the first column of some $\gamma \in \Gamma_0(\mathfrak N)$. -/
lemma exists_gamma0_col {𝔑 : Ideal (𝓞 F)} {x y : 𝓞 F} (hxy : Ideal.span {x} ⊔ Ideal.span {y} = ⊤)
    (hy : y ∈ 𝔑) : ∃ γ : SL(2, 𝓞 F), γ ∈ Gamma0R 𝔑 ∧ γ 0 0 = x ∧ γ 1 0 = y := by
  obtain ⟨u, w, huw⟩ := isCoprime_of_sup_span hxy
  refine ⟨⟨!![x, -w; y, u], by simp [det_fin_two_of]; linear_combination huw⟩, hy, rfl, rfl⟩

lemma gamma0_a_coprime {𝔑 : Ideal (𝓞 F)} {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    Ideal.span {γ 0 0} ⊔ 𝔑 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := sl2O_det γ
  have : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 ∈ Ideal.span {γ 0 0} ⊔ 𝔑 :=
    Submodule.sub_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_right _ _
      (Ideal.mem_span_singleton_self _))) (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ hγ))
  rwa [h1] at this

/-- **Every $\gamma \in \Gamma_0(\mathfrak N)$ has a good representative**: some good $a_1 \equiv \gamma_{00} \pmod{\mathfrak N}$ with
$m_Q(\gamma) = \Psi(a_1)$. -/
theorem exists_good_rep {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    ∃ a₁ : 𝓞 F, IsGoodF Q a₁ ∧ a₁ - γ 0 0 ∈ 𝔑 ∧ Ideal.span {a₁} ⊔ 𝔑 = ⊤ ∧
      thetaMultG Q k γ = psiF Q k a₁ := by
  -- first make `c ≠ 0`
  obtain ⟨γ', hγ', ha', hc', hm'⟩ : ∃ γ' : SL(2, 𝓞 F), γ' ∈ Gamma0R 𝔑 ∧ γ' 0 0 = γ 0 0 ∧
      γ' 1 0 ≠ 0 ∧ thetaMultG Q k γ' = thetaMultG Q k γ := by
    by_cases hc : γ 1 0 = 0
    · obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔑
      have ha0 : γ 0 0 ≠ 0 := by
        intro h; have := sl2O_det γ; rw [h, hc] at this; simp at this
      refine ⟨lowerU s * γ, Subgroup.mul_mem _ (lowerU_mem hs) hγ, lowerU_mul_00 s γ, ?_,
        thetaMultG_lowerU_mul hQ hn hlev h𝔑 hγ hs⟩
      rw [lowerU_mul_10, hc, add_zero]; exact mul_ne_zero hs0 ha0
    · exact ⟨γ, hγ, rfl, hc, rfl⟩
  -- then move `a` to a good element
  have hcop : Ideal.span {γ' 0 0} ⊔ Ideal.span {γ' 1 0} = ⊤ := sl2O_col_coprime γ'
  obtain ⟨s, hs, hgood⟩ := exists_add_mem_sup_eq_top hcop (goodIdealF_ne_bot hQ)
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  have hγ'' : translO t * γ' ∈ Gamma0R 𝔑 := Subgroup.mul_mem _ (translO_mem 𝔑 t) hγ'
  have hgood' : IsGoodF Q ((translO t * γ') 0 0) := by
    rw [translO_mul_00]; exact hgood
  refine ⟨(translO t * γ') 0 0, hgood', ?_, gamma0_a_coprime hγ'', ?_⟩
  · rw [translO_mul_00, ha']
    simp only [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ hγ'
  · rw [← hm', ← thetaMultG_translO_mul hQ hn hlev hγ' t]
    exact thetaMultG_eq_psiF hQ hn hlev h𝔑 hγ'' (by rw [translO_mul_10]; exact hc') hgood'

/-- One step: for good coprime $x \ne z$ with $z - x \in \mathfrak N$, $\Psi(x) = \Psi(z)$. -/
lemma psiF_step {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {x z : 𝓞 F}
    (hx : IsGoodF Q x) (hz : IsGoodF Q z) (hxz : z - x ∈ 𝔑)
    (hcop : Ideal.span {x} ⊔ Ideal.span {z} = ⊤) : psiF Q k x = psiF Q k z := by
  by_cases he : z = x
  · rw [he]
  have hc0 : z - x ≠ 0 := sub_ne_zero.mpr he
  have hcop' : Ideal.span {x} ⊔ Ideal.span {z - x} = ⊤ := by
    obtain ⟨u, w, huw⟩ := isCoprime_of_sup_span hcop
    exact sup_span_of_isCoprime ⟨u + w, w, by linear_combination huw⟩
  obtain ⟨γ, hγ, hγa, hγc⟩ := exists_gamma0_col hcop' hxz
  have h1 := thetaMultG_eq_psiF hQ hn hlev h𝔑 hγ (by rw [hγc]; exact hc0) (by rw [hγa]; exact hx)
  have hT : translO (1 : 𝓞 F) * γ ∈ Gamma0R 𝔑 := Subgroup.mul_mem _ (translO_mem 𝔑 1) hγ
  have hTa : (translO (1 : 𝓞 F) * γ : SL(2, 𝓞 F)) 0 0 = z := by
    rw [translO_mul_00, hγa, hγc]; ring
  have h2 := thetaMultG_eq_psiF hQ hn hlev h𝔑 hT (by rw [translO_mul_10, hγc]; exact hc0)
    (by rw [hTa]; exact hz)
  rw [thetaMultG_translO_mul hQ hn hlev hγ, hTa] at h2
  rw [hγa] at h1
  rw [← h1, h2]

/-- **$\Psi$ is constant on good elements of a class modulo $\mathfrak N$.** -/
theorem psiF_congr {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {x x' : 𝓞 F}
    (hx : IsGoodF Q x) (hx' : IsGoodF Q x') (hxN : Ideal.span {x} ⊔ 𝔑 = ⊤) (hxx : x' - x ∈ 𝔑) :
    psiF Q k x = psiF Q k x' := by
  have h𝔠 : Ideal.span {x * x'} * goodIdealF Q ≠ ⊥ := by
    refine mul_ne_zero ?_ (goodIdealF_ne_bot hQ)
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hx.ne_zero hx'.ne_zero
  obtain ⟨s, hs, hcop⟩ := exists_add_mem_sup_eq_top hxN h𝔠
  have hgood : IsGoodF Q (x + s) := top_le_iff.mp (hcop ▸ sup_le_sup_left
    (Ideal.mul_le_left (I := goodIdealF Q) (J := Ideal.span {x * x'}) |>.trans_eq' (mul_comm _ _)) _)
  have hspan : Ideal.span {x + s} ⊔ Ideal.span {x * x'} = ⊤ := top_le_iff.mp (hcop ▸ sup_le_sup_left
    (Ideal.mul_le_left (I := Ideal.span {x * x'}) (J := goodIdealF Q)) _)
  obtain ⟨u, w, huw⟩ := isCoprime_of_sup_span hspan
  have hc1 : Ideal.span {x} ⊔ Ideal.span {x + s} = ⊤ :=
    sup_span_of_isCoprime ⟨w * x', u, by linear_combination huw⟩
  have hc2 : Ideal.span {x'} ⊔ Ideal.span {x + s} = ⊤ :=
    sup_span_of_isCoprime ⟨w * x, u, by linear_combination huw⟩
  rw [psiF_step hQ hn hlev h𝔑 hx hgood (by simpa using hs) hc1,
    psiF_step hQ hn hlev h𝔑 hx' hgood (by
      rw [show x + s - x' = s - (x' - x) by ring]; exact Submodule.sub_mem _ hs hxx) hc2]

/-- **The multiplier depends only on $a \bmod \mathfrak N$** (equivalently on $d \bmod \mathfrak N$). -/
theorem thetaMultG_congr {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ γ' : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) (hγ' : γ' ∈ Gamma0R 𝔑) (h : γ' 0 0 - γ 0 0 ∈ 𝔑) :
    thetaMultG Q k γ = thetaMultG Q k γ' := by
  obtain ⟨a, ha, haγ, haN, hma⟩ := exists_good_rep hQ hn hlev h𝔑 hγ
  obtain ⟨a', ha', haγ', -, hma'⟩ := exists_good_rep hQ hn hlev h𝔑 hγ'
  rw [hma, hma']
  refine psiF_congr hQ hn hlev h𝔑 ha ha' haN ?_
  rw [show a' - a = (a' - γ' 0 0) + (γ' 0 0 - γ 0 0) - (a - γ 0 0) by ring]
  exact Submodule.sub_mem _ (Submodule.add_mem _ haγ' h) haγ

/-! ### The character $\chi_Q$ -/

lemma gamma0_ad_mod {𝔑 : Ideal (𝓞 F)} {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    Ideal.Quotient.mk 𝔑 (γ 0 0) * Ideal.Quotient.mk 𝔑 (γ 1 1) = 1 := by
  have := congrArg (Ideal.Quotient.mk 𝔑) (sl2O_det γ)
  rwa [map_sub, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hγ, mul_zero, sub_zero,
    map_one] at this

lemma exists_gamma0_d {𝔑 : Ideal (𝓞 F)} (u : (𝓞 F ⧸ 𝔑)ˣ) :
    ∃ γ : SL(2, 𝓞 F), γ ∈ Gamma0R 𝔑 ∧ Ideal.Quotient.mk 𝔑 (γ 1 1) = u := by
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 F ⧸ 𝔑)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (𝓞 F ⧸ 𝔑)ˣ) : 𝓞 F ⧸ 𝔑)
  have h1 : a * d - 1 ∈ 𝔑 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hd, map_one, Units.inv_mul, sub_self]
  exact ⟨⟨!![a, 1; a * d - 1, d], by simp [det_fin_two_of]⟩, h1, hd⟩

lemma thetaMultG_congr_d {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ γ' : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) (hγ' : γ' ∈ Gamma0R 𝔑)
    (h : Ideal.Quotient.mk 𝔑 (γ 1 1) = Ideal.Quotient.mk 𝔑 (γ' 1 1)) :
    thetaMultG Q k γ = thetaMultG Q k γ' := by
  refine thetaMultG_congr hQ hn hlev h𝔑 hγ hγ' ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have h1 := gamma0_ad_mod hγ
  have h2 := gamma0_ad_mod hγ'
  calc Ideal.Quotient.mk 𝔑 (γ' 0 0)
      = Ideal.Quotient.mk 𝔑 (γ' 0 0) * (Ideal.Quotient.mk 𝔑 (γ 0 0) * Ideal.Quotient.mk 𝔑 (γ 1 1)) := by
        rw [h1, mul_one]
    _ = Ideal.Quotient.mk 𝔑 (γ 0 0) * (Ideal.Quotient.mk 𝔑 (γ' 0 0) * Ideal.Quotient.mk 𝔑 (γ' 1 1)) := by
        rw [h]; ring
    _ = Ideal.Quotient.mk 𝔑 (γ 0 0) := by rw [h2, mul_one]

lemma gamma0_mul_11_mod {𝔑 : Ideal (𝓞 F)} {γ δ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    Ideal.Quotient.mk 𝔑 ((γ * δ) 1 1) = Ideal.Quotient.mk 𝔑 (γ 1 1) * Ideal.Quotient.mk 𝔑 (δ 1 1) := by
  rw [sl2_mul_apply, map_add, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hγ, zero_mul,
    zero_add]

/-- The multiplier as a homomorphism $(\mathcal{O}_F/\mathfrak N)^\times \to \mathbb{C}^\times$, $d \mapsto m_Q(\gamma_d)$. -/
def thetaCharHom {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ} (hn : n = 2 * k)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) : (𝓞 F ⧸ 𝔑)ˣ →* ℂˣ where
  toFun u := Units.mk0 (thetaMultG Q k (exists_gamma0_d u).choose)
    (thetaMultG_ne_zero hQ hn hlev (exists_gamma0_d u).choose_spec.1)
  map_one' := by
    ext
    simp only [Units.val_mk0, Units.val_one]
    have h1 : (1 : SL(2, 𝓞 F)) ∈ Gamma0R 𝔑 := Subgroup.one_mem _
    rw [thetaMultG_congr_d hQ hn hlev h𝔑 (exists_gamma0_d (1 : (𝓞 F ⧸ 𝔑)ˣ)).choose_spec.1 h1
      (by rw [(exists_gamma0_d (1 : (𝓞 F ⧸ 𝔑)ˣ)).choose_spec.2]; simp)]
    simp [thetaMultG]
  map_mul' u v := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    have hu := (exists_gamma0_d u).choose_spec
    have hv := (exists_gamma0_d v).choose_spec
    have huv := (exists_gamma0_d (u * v)).choose_spec
    rw [← thetaMultG_mul hQ hn hlev hu.1 hv.1]
    refine thetaMultG_congr_d hQ hn hlev h𝔑 huv.1 (Subgroup.mul_mem _ hu.1 hv.1) ?_
    rw [huv.2, gamma0_mul_11_mod hu.1, hu.2, hv.2, Units.val_mul]

/-- **The theta character** $\chi_Q$ on $\mathcal{O}_F/\mathfrak N$: $\chi_Q(d \bmod \mathfrak N) = m_Q(\gamma)$ for any
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ (`thetaCharF_apply`), $0$ on non-units. It is quadratic
(`thetaCharF_isQuadratic`) and equals $\operatorname{sgn}(N(a))^k(\frac{(-1)^k\det H}{(a)})$ at every good $a$ prime to $\mathfrak N$
(`thetaCharF_eq_psiF`): the quadratic Hecke character of $F(\sqrt{(-1)^k\det H})/F$ with signature $\operatorname{sgn}^k$.

Parameters: the form `Q` with `hQ` (totally positive definite), `hn` ($n = 2k$), `hlev` ($\mathfrak N$ a level), `h𝔑`
($\mathfrak N \ne 0$). -/
@[kb "shimura1973" "§2, the character of θ [unverified]"]
def thetaCharF {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ} (hn : n = 2 * k)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) : MulChar (𝓞 F ⧸ 𝔑) ℂ :=
  MulChar.ofUnitHom (thetaCharHom hQ hn hlev h𝔑)

theorem thetaCharF_apply {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 (γ 1 1)) = thetaMultG Q k γ := by
  have hu : IsUnit (Ideal.Quotient.mk 𝔑 (γ 1 1)) :=
    IsUnit.of_mul_eq_one (b := Ideal.Quotient.mk 𝔑 (γ 0 0)) (by rw [mul_comm]; exact gamma0_ad_mod hγ)
  rw [← hu.unit_spec, thetaCharF, MulChar.ofUnitHom_coe]
  simp only [thetaCharHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0]
  refine thetaMultG_congr_d hQ hn hlev h𝔑 (exists_gamma0_d hu.unit).choose_spec.1 hγ ?_
  rw [(exists_gamma0_d hu.unit).choose_spec.2, hu.unit_spec]

/-! ### The transformation law, quadraticity, and the values of $\chi_Q$ -/

/-- **The $\Gamma_0(\mathfrak N)$ transformation law of $\theta_Q$ with character.** Let $F$ be totally real, $Q$ a totally positive
definite form over $\mathcal{O}_F$ in $n = 2k$ variables (`IsTotPosGram (gramF Q)`), and $\mathfrak N \ne 0$ a level of $Q$
(`IsThetaLevelF`). For every $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ ($d = \gamma_{11}$, 0-based):
$$\theta_Q\,|_k\,\gamma = \chi_Q(d \bmod \mathfrak N)\,\theta_Q,$$
with the quadratic character $\chi_Q$ = `thetaCharF` (the Hecke character of $F(\sqrt{(-1)^k\det H})/F$, `thetaCharF_eq_psiF`).
For $F = \mathbb{Q}$ this is `QuadFormsKB.Siegel.theta_gamma0_chi`; here no theorem on primes in progressions is used. -/
@[kb "shimura1973" "§2, Prop. 2.1 (theta transformation, integral weight case) [unverified]"]
theorem thetaQ_slash_gamma0_char {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Gamma0R 𝔑) :
    thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) (toF F γ) =
      thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 (γ 1 1)) • thetaQ Q := by
  rw [thetaCharF_apply hQ hn hlev h𝔑 hγ, thetaQ_slash_eq_thetaMultG hQ hn hlev hγ]

/-- $|\mathcal{O}_F/a| = |N_{F/\mathbb{Q}}(a)| = |\prod_v\varphi_v(a)|$. -/
lemma natCard_quot_span_eq (a : 𝓞 F) :
    (Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℝ) = |∏ v, realEmb F v (algebraMap (𝓞 F) F a)| := by
  have h1 : Nat.card (𝓞 F ⧸ Ideal.span {a}) = Ideal.absNorm (Ideal.span {a}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Finset.abs_prod]
  have h2 := InfinitePlace.prod_eq_abs_norm (K := F) (algebraMap (𝓞 F) F a)
  simp only [(IsTotallyReal.isReal _).mult_eq_one, pow_one] at h2
  simp_rw [abs_realEmb]
  rw [h2, ← Algebra.coe_norm_int]
  push_cast
  rfl

lemma jacobiO_sq_eq_one {D a : 𝓞 F} (hD : Ideal.span {a} ⊔ Ideal.span {D} = ⊤) :
    jacobiO D (Ideal.span {a}) ^ 2 = 1 := by
  unfold jacobiO
  rw [← Multiset.prod_map_pow]
  refine Multiset.prod_eq_one fun x hx => ?_
  obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hx
  refine legendreO_sq_eq_one fun hD𝔭 => ?_
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 h𝔭
  have hle : Ideal.span {a} ≤ 𝔭 :=
    Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔭)
  have : Ideal.span {a} ⊔ Ideal.span {D} ≤ 𝔭 :=
    sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hD𝔭)
  rw [hD] at this
  exact (Ideal.isPrime_of_prime hp).ne_top (top_le_iff.mp this)

/-- $\Psi(a) = \pm1$ for good $a$. -/
theorem psiF_sq {Q : QuadForm (𝓞 F) n} (k : ℕ) {a : 𝓞 F}
    (ha : IsGoodF Q a) : psiF Q k a ^ 2 = 1 := by
  have ha0 := ha.ne_zero
  have hD : Ideal.span {a} ⊔ Ideal.span {(-1) ^ k * Q.hessian.det} = ⊤ := by
    have h1 := isCoprime_of_sup_span ha.two_det
    exact sup_span_of_isCoprime (IsCoprime.mul_right (isCoprime_one_right.neg_right.pow_right)
      h1.of_mul_right_right)
  have hJ := jacobiO_sq_eq_one hD
  have hN : ((Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℂ)) ^ 2 =
      (∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ 2 := by
    have := natCard_quot_span_eq a
    have h2 : ((Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℝ)) ^ 2 =
        (∏ v, realEmb F v (algebraMap (𝓞 F) F a)) ^ 2 := by rw [this, sq_abs]
    exact_mod_cast h2
  have hP0 : (∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => realEmb_algebraMap_ne_zero ha0 v
  have hJc : ((jacobiO ((-1) ^ k * Q.hessian.det) (Ideal.span {a}) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast hJ
  have hNk : ((Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℂ) ^ k) ^ 2 =
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm, pow_mul, hN, ← pow_mul]
  rw [psiF, mul_pow, mul_pow, hJc, mul_one, hNk, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hP0))]

/-- **$\chi_Q$ is a quadratic character**: its values are $0$ (non-units) and $\pm1$. -/
@[kb "shimura1973" "§2, the character of θ [unverified]"]
theorem thetaCharF_isQuadratic {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    (thetaCharF hQ hn hlev h𝔑).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · right
    obtain ⟨γ, hγ, hd⟩ := exists_gamma0_d hx.unit
    rw [← hx.unit_spec, ← hd, thetaCharF_apply hQ hn hlev h𝔑 hγ]
    obtain ⟨a, ha, -, -, hma⟩ := exists_good_rep hQ hn hlev h𝔑 hγ
    rw [hma]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact psiF_sq k ha)
  · left; exact MulChar.map_nonunit _ hx

/-- **The values of $\chi_Q$: the Hecke character of $F(\sqrt D)/F$.** For good $a$ (prime to $2\det H$ and $\mathfrak d$) with
$(a) + \mathfrak N = 1$:
$$\chi_Q(a \bmod \mathfrak N) = \Psi(a) = N(a)^{-k}\Big(\frac{(-1)^k\det H}{(a)}\Big)N((a))^k
  = \operatorname{sgn}\big(N_{F/\mathbb{Q}}(a)\big)^k\Big(\frac{(-1)^k\det H}{(a)}\Big).$$
Every class of $(\mathcal{O}_F/\mathfrak N)^\times$ contains good elements (`exists_add_mem_sup_eq_top`), so this determines $\chi_Q$. -/
@[kb "neukirch1999" "Ch. VI §6, quadratic Hecke characters [unverified]"]
theorem thetaCharF_eq_psiF {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {a : 𝓞 F}
    (ha : IsGoodF Q a) (haN : Ideal.span {a} ⊔ 𝔑 = ⊤) :
    thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 a) = psiF Q k a := by
  -- a matrix with upper left entry `a`
  have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔑 := by rw [haN]; trivial
  obtain ⟨x, hx, m, hm, hxm⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  set γ : SL(2, 𝓞 F) := ⟨!![a, -1; m, u], by simp [det_fin_two_of]; linear_combination hxm⟩
  have hγ : γ ∈ Gamma0R 𝔑 := hm
  have hγa : γ 0 0 = a := rfl
  -- `m_Q(γ) = Ψ(a)`
  obtain ⟨a₁, ha₁, haa₁, -, hma⟩ := exists_good_rep hQ hn hlev h𝔑 hγ
  rw [hγa] at haa₁
  have hm' : thetaMultG Q k γ = psiF Q k a := by
    rw [hma, ← psiF_congr hQ hn hlev h𝔑 ha ha₁ haN haa₁]
  have hχd := thetaCharF_apply hQ hn hlev h𝔑 hγ
  rw [hm'] at hχd
  have hprod : thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 a) *
      thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 (γ 1 1)) = 1 := by
    rw [← map_mul, ← hγa, gamma0_ad_mod hγ, MulChar.map_one]
  rw [hχd] at hprod
  have hsq := psiF_sq k ha
  have hne : psiF Q k a ≠ 0 := fun h => by rw [h] at hsq; simp at hsq
  calc thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 a)
      = thetaCharF hQ hn hlev h𝔑 (Ideal.Quotient.mk 𝔑 a) * (psiF Q k a * psiF Q k a) := by
        rw [← sq, hsq, mul_one]
    _ = psiF Q k a := by rw [← mul_assoc, hprod, one_mul]

/-- $\Psi(a) = \operatorname{sgn}(N(a))^k(\frac{D}{(a)})$, $N(a) = \prod_v\varphi_v(a)$. -/
theorem psiF_eq_sign {Q : QuadForm (𝓞 F) n} (k : ℕ) {a : 𝓞 F} (ha0 : a ≠ 0) :
    psiF Q k a = ((SignType.sign (∏ v, realEmb F v (algebraMap (𝓞 F) F a)) : ℝ) : ℂ) ^ k *
      (jacobiO ((-1) ^ k * Q.hessian.det) (Ideal.span {a}) : ℂ) := by
  set P : ℝ := ∏ v, realEmb F v (algebraMap (𝓞 F) F a) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => by
    have := realEmb_algebraMap_ne_zero ha0 v; exact_mod_cast this
  have hcard := natCard_quot_span_eq a
  rw [← hP] at hcard
  rw [psiF]
  have hPc : (∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) = (P : ℂ) := by rw [hP]; push_cast; rfl
  rw [hPc]
  have hcardc : (Nat.card (𝓞 F ⧸ Ideal.span {a}) : ℂ) = ((|P| : ℝ) : ℂ) := by
    rw [← hcard]; push_cast; rfl
  rw [hcardc]
  have hs : (|P| : ℝ) = (SignType.sign P : ℝ) * P := by
    rcases lt_or_gt_of_ne hP0 with h | h
    · rw [abs_of_neg h, sign_neg h]; simp
    · rw [abs_of_pos h, sign_pos h]; simp
  rw [hs]
  have hPc0 : (P : ℂ) ≠ 0 := by exact_mod_cast hP0
  push_cast
  field_simp
  ring

/-! ### $\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$ -/

/-- **$\theta_Q$ is a Hilbert modular form with character.** For $F$ totally real of degree $d = [F:\mathbb{Q}] \ge 2$, $Q$ a
totally positive definite form over $\mathcal{O}_F$ in $n = 2k$ variables and $\mathfrak N \ne 0$ a level of $Q$:
$$\theta_Q \in M_k(\Gamma_0(\mathfrak N), \chi_Q)$$
(`modularFormChar`: $\theta_Q \in M_k(\Gamma_1(\mathfrak N))$ and $\theta_Q\,|_k\,\gamma = \chi_Q(d)\theta_Q$ on $\Gamma_0(\mathfrak N)$). The cusp
condition comes from the Koecher principle (`mem_modularFormSpace_of_GammaFull_le`). For $d = 1$ ($F = \mathbb{Q}$) the transformation
law `thetaQ_slash_gamma0_char` still holds; boundedness at the cusps is then not automatic, and the $\mathbb{Q}$ result is
`QuadFormsKB.Siegel.thetaMFGamma1` / `QuadFormsKB.Siegel.theta_gamma0_chi`. -/
@[kb "shimura1973" "§2, Prop. 2.1 (theta series as modular forms with character) [unverified]"]
theorem thetaQ_mem_modularFormChar (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ} (hn : n = 2 * k)
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    thetaQ Q ∈ modularFormChar 𝔑 (thetaCharF hQ hn hlev h𝔑) k := by
  refine ⟨mem_modularFormSpace_of_GammaFull_le hd 𝔑 h𝔑 (GammaFull_le_Gamma1 𝔑) ?_
    (isHolomorphic_thetaQ hQ), fun γ hγ => thetaQ_slash_gamma0_char hQ hn hlev h𝔑 hγ⟩
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨hγ0, hγ1⟩ := (mem_Gamma1R 𝔑).mp hγ
  rw [thetaQ_slash_gamma0_char hQ hn hlev h𝔑 hγ0, hγ1, MulChar.map_one, one_smul]

end

end QuadFormsKB.HilbertModular
