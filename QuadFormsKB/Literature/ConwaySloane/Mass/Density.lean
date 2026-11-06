/-
# Conway–Sloane, "Low-dimensional lattices IV: the mass formula", §12 and formula (2)

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`). Their form $f$ has an integral symmetric Gram matrix $A$ (`A : Matrix (Fin n) (Fin n) ℤ`),
$f(x) = x A x^{\mathsf T}$ and $\det f = \det A$. The repository's `QuadForm ℤ n` stores the quadratic form, so the form
with Gram matrix $A$ is `LocalDensity.ofMatrixZ A`, whose Hessian is $A + A^{\mathsf T} = 2A$ (`hessian_ofMatrixZ`).

**Definitions (§12, p. 281).**
* `countN p r A` $= N(p^r)$, (18): the number of $X \in M_n(\mathbb Z/p^r)$ with $X^{\mathsf T} A X \equiv A \pmod{p^r}$;
* `alphaP p A` $= \alpha_p(f) = \lim_r N(p^r)\,p^{-r\,n(n-1)/2}$ (Lean's `limUnder`; the limit exists, see below);
* `pMassDensity p A` $= m_p(f) = p^{s(n+1)/2}/\alpha_p(f)$, where $p^s \,\|\, \det A$.

**Proves.**
* the bridge to the library's local densities over the completion $\mathbb Q_p$: `countN_eq_shimuraCount`
  (the count over $\mathbb Z/p^r$ is Hanke's Shimura count over $\mathbb Z_p/p^r$), `alphaP_eq_shimuraE`,
  `hankeBeta_eq_half_alphaP` ($\beta_p = \tfrac12\alpha_p$);
* the stabilization claim of p. 281: `alphaP_stabilizes` (for $A$ symmetric with $\det A \ne 0$ the ratio
  $N(p^r)p^{-r n(n-1)/2}$ is constant, equal to $\alpha_p(A)$, for all large $r$), and `alphaP_pos`;
* **formula (2)**, p. 263 (`mass_formula_two`), for $n \ge 3$ and $A$ symmetric positive definite:
  $$m(f) = 2\,\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p 2\,m_p(f),$$
  the product over all primes (convergent: `Multipliable`, with positive value), with `Siegel.mass` as $m(f)$. It is
  `Hanke2011Structure.cor_6_3_genus` for $F = \mathbb Q$, generalizing `cor_6_3_rat` from $n = 3$ to all $n \ge 3$
  (`mass_eq_invBeta`), then rewritten with $\det_H = 2^n\det A$, $V(n)$, $\beta_p = \tfrac12\alpha_p$ and
  $(\det A)^{(n+1)/2} = \prod_p p^{s_p(n+1)/2}$ (`hasProd_pow_det`);
* scaling (§12, p. 282): `alphaP_smul_prime` ($\alpha_p(pA) = p^{n(n+1)/2}\alpha_p(A)$) and
  `pMassDensity_smul_prime` ($m_p(pA) = m_p(A)$, "the $p$-mass, unlike the $p$-adic density, is invariant under
  changing the scale of the form") for the scale factor $p$.

**Open.** The scale invariance for an arbitrary integer $c \ne 0$ (only $c = p$ is proved; general $c = p^k u$ would also
need invariance under a $p$-adic unit). Dimension 2 (the product in (2) converges only conditionally) is proved in
`FormulaDimTwo.lean` (`mass_formula_two_dimTwo`, `mass_formula_two_dimTwo_natural`).

*Convention note.* Indices are 0-based; the exponent $n(n-1)/2$ is natural-number division, as in `Hanke2005.shimuraE`.
-/
import QuadFormsKB.Literature.Hanke2011Structure.RationalTernary
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal
import QuadFormsKB.Literature.Hanke2005.TheoremTwoOne
import QuadFormsKB.LocalDensity.JordanForm

open QuadFormsKB IsDedekindDomain NumberField Filter Matrix

noncomputable section
namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-- **$N(p^r)$** (Conway–Sloane (18), p. 281): the number of matrices $X \in M_n(\mathbb Z/p^r\mathbb Z)$ with
$X^{\mathsf T} A X \equiv A \pmod{p^r}$, for the integral Gram matrix $A$. -/
@[kb "conwaysloane1988" "(18), p. 281"]
def countN (p r : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin n) (ZMod (p ^ r)) //
    Xᵀ * A.map (Int.castRingHom (ZMod (p ^ r))) * X = A.map (Int.castRingHom (ZMod (p ^ r)))}

/-- **The $p$-adic density** $\alpha_p(f) = \lim_{r\to\infty} N(p^r)\,p^{-r\,n(n-1)/2}$ of the form with Gram matrix $A$
(§12, p. 281). The limit exists and is attained for large $r$ when $A$ is symmetric with $\det A \ne 0$
(`alphaP_stabilizes`). -/
@[kb "conwaysloane1988" "§12, p. 281"]
def alphaP (p : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  limUnder atTop fun r : ℕ => (countN p r A : ℝ) / (p : ℝ) ^ (r * (n * (n - 1) / 2))

/-- **The $p$-mass** $m_p(f) = p^{s(n+1)/2}/\alpha_p(f)$, $p^s \,\|\, \det f$ (§12, p. 281; $s$ is `padicValInt p A.det`). -/
@[kb "conwaysloane1988" "§12, p. 281"]
def pMassDensity (p : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  (p : ℝ) ^ (((padicValInt p A.det : ℝ) * ((n : ℝ) + 1)) / 2) / alphaP p A

section Bridge

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The rational prime $p$ of the place $v$ of $\mathbb Q$. -/
abbrev pv : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)

instance : Fact (pv v).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The ring isomorphism $\mathbb Z_p \cong \mathfrak o_v$ (Mathlib's `padicIntEquiv`). -/
def eInt : ℤ_[pv v] ≃+* 𝔬 :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv

theorem eInt_irreducible : Irreducible (eInt v (pv v : ℤ_[pv v])) :=
  (MulEquiv.irreducible_iff (eInt v).toMulEquiv).mpr PadicInt.irreducible_p

theorem eInt_assoc : Associated (eInt v (pv v : ℤ_[pv v])) (LocalDensity.NF.π v) :=
  IsDiscreteValuationRing.associated_of_irreducible _ (eInt_irreducible v)
    (LocalDensity.NF.irreducible_π v)

def redPsi (r : ℕ) : 𝔬 →+* ZMod (pv v ^ r) :=
  (PadicInt.toZModPow r).comp (eInt v).symm.toRingHom

theorem redPsi_surjective (r : ℕ) : Function.Surjective (redPsi v r) := by
  intro a
  refine ⟨eInt v ((a.val : ℕ) : ℤ_[pv v]), ?_⟩
  simp [redPsi]

theorem ker_redPsi (r : ℕ) : RingHom.ker (redPsi v r) = Ideal.span {LocalDensity.NF.π v ^ r} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have h1 : redPsi v r x = 0 ↔ (pv v : ℤ_[pv v]) ^ r ∣ (eInt v).symm x := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    rfl
  rw [h1, ← ((eInt_assoc v).pow_pow (n := r)).dvd_iff_dvd_left, ← map_pow]
  have := map_dvd_iff (eInt v) (a := (pv v : ℤ_[pv v]) ^ r) (b := (eInt v).symm x)
  simpa using this.symm

def eQuot (r : ℕ) : 𝔬 ⧸ Ideal.span {LocalDensity.NF.π v ^ r} ≃+* ZMod (pv v ^ r) :=
  (Ideal.quotEquivOfEq (ker_redPsi v r).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redPsi_surjective v r))

theorem eQuot_mk (r : ℕ) (x : 𝔬) : eQuot v r (Ideal.Quotient.mk _ x) = redPsi v r x := rfl

/-- **Bridge to Hanke's Shimura count**: $N(p^r)$ is `Hanke2005.shimuraCount` at the place of $p$, the count of
$X \in M_n(\mathfrak o_v/\pi^r)$ with $X^{\mathsf T}AX = A$ ($\mathfrak o_v \cong \mathbb Z_p$, $\mathfrak o_v/\pi^r \cong
\mathbb Z/p^r$). -/
@[kb "conwaysloane1988" "(18), p. 281 (bridge to the p-adic count)"]
theorem countN_eq_shimuraCount {A : Matrix (Fin n) (Fin n) ℤ} (r : ℕ) :
    countN (pv v) r A = Hanke2005.shimuraCount v (A.map (algebraMap ℤ 𝔬)) r := by
  unfold countN Hanke2005.shimuraCount
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (eQuot v r).mapMatrix.toEquiv fun X => ?_)
  have hA : (((A.map (algebraMap ℤ 𝔬)).map (Ideal.Quotient.mk _)).map (eQuot v r) :
      Matrix (Fin n) (Fin n) (ZMod (pv v ^ r))) =
      A.map (Int.castRingHom (ZMod (pv v ^ r))) := by
    ext i j
    simp
  have key : ∀ (Y Z : Matrix (Fin n) (Fin n) (𝔬 ⧸ Ideal.span {LocalDensity.NF.π v ^ r})),
      Y = Z ↔ (eQuot v r).mapMatrix Y = (eQuot v r).mapMatrix Z := fun Y Z =>
    ((eQuot v r).mapMatrix.injective.eq_iff).symm
  rw [key]
  simp only [map_mul, RingEquiv.mapMatrix_apply, Matrix.transpose_map]
  rw [hA]
  rfl

/-- The residue field of $\mathfrak o_v$ has $p$ elements. -/
theorem q_eq : LocalDensity.DVR.q 𝔬 = pv v := by
  unfold LocalDensity.DVR.q
  rw [← Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (eInt v)).toEquiv]
  rw [Nat.card_congr (PadicInt.residueField (p := pv v)).toEquiv]
  simp

/-- **$\alpha_p(A) = e_p(A)$**: Conway–Sloane's $p$-adic density is Shimura's local factor `Hanke2005.shimuraE`. -/
@[kb "conwaysloane1988" "§12, p. 281 (bridge to Shimura's e_p)"]
theorem alphaP_eq_shimuraE (A : Matrix (Fin n) (Fin n) ℤ) :
    alphaP (pv v) A = Hanke2005.shimuraE v (A.map (algebraMap ℤ 𝔬)) := by
  unfold alphaP Hanke2005.shimuraE
  congr 1
  funext r
  rw [countN_eq_shimuraCount, q_eq]

theorem det_map_ne_zero {A : Matrix (Fin n) (Fin n) ℤ} (hdet : A.det ≠ 0) :
    (A.map (algebraMap ℤ 𝔬)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (algebraMap ℤ 𝔬).injective_int).mpr hdet

/-- **$\beta_p = \tfrac12\alpha_p$**: Hanke's local density of the Gram matrix $A$ is half the $p$-adic density. -/
@[kb "conwaysloane1988" "§12, p. 281 (bridge: Hanke's beta = half alpha_p)"]
theorem hankeBeta_eq_half_alphaP {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    Hanke2005.hankeBeta v (Lattices.std v) ((A.map (algebraMap ℤ 𝔬)).map
      (algebraMap 𝔬 (v.adicCompletion ℚ))) = (1 / 2 : ℝ) * alphaP (pv v) A := by
  rw [Hanke2005.hankeBeta_std_eq_half_shimuraE v _ (det_map_ne_zero v hdet), alphaP_eq_shimuraE]
  rw [← Matrix.transpose_map, hA.eq]

/-- Stabilization at the place $v$ (see `alphaP_stabilizes`). -/
@[kb "conwaysloane1988" "§12, p. 281 (independence of r)"]
theorem alphaP_stabilizes'{A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ∀ᶠ r in atTop, (countN (pv v) r A : ℝ) / (pv v : ℝ) ^ (r * (n * (n - 1) / 2)) =
      alphaP (pv v) A := by
  set φ := A.map (algebraMap ℤ 𝔬) with hφ
  have hdet' : φ.det ≠ 0 := det_map_ne_zero v hdet
  have hπ := LocalDensity.NF.irreducible_π v
  obtain ⟨d, hd, hd'⟩ := LocalDensity.DVR.exists_pow_dvd_not_dvd (LocalDensity.NF.π v) hπ hdet'
  have hsym : (φ.map (algebraMap 𝔬 (v.adicCompletion ℚ)))ᵀ = φ.map (algebraMap 𝔬 (v.adicCompletion ℚ)) := by
    have hφT : φᵀ = φ := by rw [hφ, ← Matrix.transpose_map, hA.eq]
    rw [← Matrix.transpose_map, hφT]
  have hdetF : (φ.map (algebraMap 𝔬 (v.adicCompletion ℚ))).det ≠ 0 := by
    have : (φ.map (algebraMap 𝔬 (v.adicCompletion ℚ))).det = algebraMap 𝔬 _ φ.det :=
      (RingHom.map_det _ φ).symm
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 (v.adicCompletion ℚ))).mpr hdet'
  have h1 := Hanke2005.gramRatio_std_eventually_eq v hsym hdetF
  have hb := hankeBeta_eq_half_alphaP v hA hdet
  filter_upwards [h1, eventually_gt_atTop d] with i hi hdi
  rw [countN_eq_shimuraCount, show ((pv v : ℕ) : ℝ) = ((LocalDensity.DVR.q 𝔬 : ℕ) : ℝ) by rw [q_eq],
    ← Hanke2005.f3_gramRatio_eq v φ hd hd' hdi, hi, hb]
  ring

end Bridge

/-- **Stabilization** (§12, p. 281: "for all sufficiently large $r$ the $p$-adic density is independent of $r$"): for
a prime $p$ and a symmetric integral $A$ with $\det A \ne 0$ there is $r_0$ such that
$N(p^r)\,p^{-r\,n(n-1)/2} = \alpha_p(A)$ for all $r \ge r_0$. -/
@[kb "conwaysloane1988" "§12, p. 281 (independence of r)"]
theorem alphaP_stabilizes {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, (countN p r A : ℝ) / (p : ℝ) ^ (r * (n * (n - 1) / 2)) = alphaP p A := by
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), pv v = p :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (⟨p, hp⟩ : Nat.Primes))⟩
  exact eventually_atTop.mp (alphaP_stabilizes' v hA hdet)

/-- The identity matrix is a solution, so $N(p^r) \ge 1$. -/
@[kb "conwaysloane1988" "(18), p. 281"]
theorem countN_pos {p : ℕ} (hp : p.Prime) (r : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : 0 < countN p r A := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  unfold countN
  exact Nat.card_pos_iff.mpr ⟨⟨⟨1, by simp⟩⟩, inferInstance⟩

/-- **$\alpha_p(A) > 0$** for $A$ symmetric with $\det A \ne 0$ (it equals a positive term of the stabilized sequence). -/
@[kb "conwaysloane1988" "§12, p. 281"]
theorem alphaP_pos {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) : 0 < alphaP p A := by
  obtain ⟨r₀, h⟩ := alphaP_stabilizes hp hA hdet
  rw [← h r₀ le_rfl]
  have := countN_pos hp r₀ A
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  positivity

/-! ### Formula (2) -/

open Real Hanke2011Structure Tamagawa.RatBridge

/-- **Corollary 6.3 over $\mathbb Z$ for all $n \ge 3$** (generalizing `Hanke2011Structure.cor_6_3_rat`, $n = 3$):
$\mathrm{Mass}(Q) = V(n)^{-1}\,(\det_HQ)^{(n+1)/2}\,2^{-n(n+1)/2}\prod_p\beta_p^{-1}$ with $\prod_p\beta_p^{-1} > 0$. -/
@[kb "conwaysloane1988" "(2), p. 263 (via Siegel's formula in Hanke's normalization)"]
theorem mass_eq_invBeta {Q : QuadForm ℤ n} (hn : 3 ≤ n) (hQ : IntQF.PosDef Q) :
    Siegel.mass Q = (volV n)⁻¹ * (Q.hessian.det : ℝ) ^ (((n : ℝ) + 1) / 2) /
        (2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2) * (∏' v, localBeta v (up Q))⁻¹ ∧
      0 < (∏' v, localBeta v (up Q))⁻¹ := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (up Q).Nondegenerate := by
    have h := Siegel.det_hessian_pos hQ
    unfold QuadForm.Nondegenerate
    rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 ℚ)).injective_int).mpr h.ne'
  obtain ⟨h, hP⟩ := cor_6_3_genus (F := ℚ) hn (up Q) hnd hpd
  refine ⟨?_, hP⟩
  have hD : (0 : ℝ) < Q.hessian.det := by exact_mod_cast Siegel.det_hessian_pos hQ
  rw [mass_rat Q hQ, h, hessian_det_formF_up, Algebra.norm_self, MonoidHom.id_apply, Rat.cast_intCast,
    NumberField.discr_rat, Module.finrank_self, abs_of_pos hD, Int.cast_one, abs_one, Real.one_rpow,
    pow_one, pow_one]
  ring

/-- Hanke's `localBeta` at the place $v$ of the form with Gram matrix $A$ is $\tfrac12\alpha_p(A)$. -/
@[kb "conwaysloane1988" "§12, p. 281 (bridge: localBeta = half alpha_p)"]
theorem localBeta_ofMatrixZ (v : HeightOneSpectrum (𝓞 ℚ)) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    localBeta v (up (LocalDensity.ofMatrixZ A)) = (1 / 2 : ℝ) * alphaP (pv v) A := by
  unfold localBeta
  rw [← hankeBeta_eq_half_alphaP v hA hdet]
  congr 1
  have hH : (LocalDensity.NF.Qp v (up (LocalDensity.ofMatrixZ A))).hessian =
      (A + A).map (algebraMap ℤ (v.adicCompletionIntegers ℚ)) := by
    show (QuadForm.map (LocalDensity.NF.ι v) (QuadForm.map Lattices.toOQ (LocalDensity.ofMatrixZ A))).hessian = _
    rw [QuadForm.hessian_map', QuadForm.hessian_map', LocalDensity.hessian_ofMatrixZ, hA.eq,
      Matrix.map_map]
    ext i j
    simp [eq_intCast]
  unfold Hanke2005.gramOf
  rw [hH]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, map_add, smul_eq_mul]
  ring

/-- $\det H = 2^n\det A$ for the form with symmetric Gram matrix $A$. -/
@[kb "conwaysloane1988" "§1, p. 259 (det f = det A)"]
theorem hessian_det_ofMatrixZ {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) :
    (LocalDensity.ofMatrixZ A).hessian.det = 2 ^ n * A.det := by
  rw [LocalDensity.hessian_ofMatrixZ, hA.eq, ← two_smul ℤ A, Matrix.det_smul]
  simp

/-- A positive definite integral symmetric Gram matrix has positive determinant. -/
@[kb "conwaysloane1988" "§1, p. 259 (det f = det A)"]
theorem det_pos_of_posDef {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A)) : 0 < A.det := by
  have h := Siegel.det_hessian_pos hQ
  rw [hessian_det_ofMatrixZ hA] at h
  exact (mul_pos_iff_of_pos_left (by positivity)).mp h

/-- The finite product $\prod_q q^{v_q(d)c} = |d|^c$ over all $q \in \mathbb N$ (factorization exponents). -/
@[kb "conwaysloane1988" "(2), p. 263 (det f = product of p^s)"]
theorem hasProd_pow_det_nat (d : ℤ) (hd : d ≠ 0) (c : ℝ) :
    HasProd (fun q : ℕ => (q : ℝ) ^ ((d.natAbs.factorization q : ℝ) * c))
      ((d.natAbs : ℝ) ^ c) := by
  have hd' : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have h1 : HasProd (fun q : ℕ => (q : ℝ) ^ ((d.natAbs.factorization q : ℝ) * c))
      (∏ q ∈ d.natAbs.primeFactors, (q : ℝ) ^ ((d.natAbs.factorization q : ℝ) * c)) := by
    refine hasProd_prod_of_ne_finset_one fun q hq => ?_
    have : d.natAbs.factorization q = 0 := by
      by_contra h
      exact hq (by rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact h)
    simp [this]
  convert h1 using 1
  have h2 : ((d.natAbs : ℕ) : ℝ) = ∏ q ∈ d.natAbs.primeFactors, (q : ℝ) ^ (d.natAbs.factorization q) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd']
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [h2, ← Real.finsetProd_rpow _ _ (fun q _ => by positivity)]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

/-- $\prod_p p^{s_p c} = d^c$ over the primes, $p^{s_p} \,\|\, d$ (so $c = (n+1)/2$ gives $(\det A)^{(n+1)/2}$). -/
@[kb "conwaysloane1988" "(2), p. 263 (det f = product of p^s)"]
theorem hasProd_pow_det {d : ℤ} (hd : 0 < d) (c : ℝ) :
    HasProd (fun p : Nat.Primes => (p : ℝ) ^ ((padicValInt p d : ℝ) * c)) ((d : ℝ) ^ c) := by
  have h := hasProd_pow_det_nat d hd.ne' c
  have hdn : ((d.natAbs : ℕ) : ℝ) = (d : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos]; exact_mod_cast hd
  rw [hdn] at h
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  rw [← hinj.hasProd_iff] at h
  · convert h using 2 with p
    have : padicValInt p d = d.natAbs.factorization p := by
      rw [Nat.factorization_def _ p.2]; rfl
    simp [this]
  · intro q hq
    have : d.natAbs.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_prime
      intro hqp
      exact hq ⟨⟨q, hqp⟩, rfl⟩
    simp [this]

/-- The inverse local densities of the form with Gram matrix $A$ ($n \ge 3$, positive definite) multiply to the
inverse of the product of the densities. -/
@[kb "conwaysloane1988" "(2), p. 263"]
theorem hasProd_inv_localBeta_ofMatrixZ (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A)) :
    HasProd (fun v => (localBeta v (up (LocalDensity.ofMatrixZ A)))⁻¹)
      (∏' v, localBeta v (up (LocalDensity.ofMatrixZ A)))⁻¹ := by
  set Q := LocalDensity.ofMatrixZ A
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (up Q).Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  have hgram : ∀ v, localBeta v (up Q) =
      ‖(2 : v.adicCompletion ℚ)‖ ^ (n * (n - 1) / 2) * LocalDensity.NF.siegelDensity v (up Q) (up Q) :=
    fun v => Hanke2005.hankeBeta_gramV v (up Q) hnd
  have hm2 : Multipliable fun v : HeightOneSpectrum (𝓞 ℚ) => ‖(2 : v.adicCompletion ℚ)‖ ^ (n * (n - 1) / 2) :=
    multipliable_of_hasFiniteMulSupport (Hanke2005.hasFiniteMulSupport_norm_two.pow _)
  have hms := Tamagawa.multipliable_siegelDensity (by omega) (by omega) (up Q) hnd
  have hm : Multipliable fun v => localBeta v (up Q) := by
    simp_rw [hgram]; exact hm2.mul hms
  have hne : ∏' v, localBeta v (up Q) ≠ 0 := by
    have := (mass_eq_invBeta hn hQ).2
    intro h0
    rw [h0, _root_.inv_zero] at this
    exact lt_irrefl _ this
  exact hm.hasProd.inv₀ hne

/-- $\lVert p\rVert_p = p^{-1}$ in the completion at the place of $p$. -/
theorem norm_prime_completion (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖((pv v : ℕ) : v.adicCompletion ℚ)‖ = ((pv v : ℝ))⁻¹ := by
  have h := Tamagawa.norm_coe_of_pow_dvd v (x := eInt v (pv v : ℤ_[pv v])) (e := 1)
    (by rw [pow_one]; exact (eInt_assoc v).symm.dvd) (by
      rw [pow_succ, pow_one]
      intro hd
      have h1 : LocalDensity.NF.π v * LocalDensity.NF.π v ∣ LocalDensity.NF.π v * 1 := by
        rw [mul_one]; exact hd.trans (eInt_assoc v).dvd
      have h2 := (mul_dvd_mul_iff_left (LocalDensity.NF.irreducible_π v).ne_zero).mp h1
      exact (LocalDensity.NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h2))
  rw [q_eq, pow_one] at h
  rw [← h]
  congr 1
  rw [map_natCast (eInt v)]
  simp

/-- **Scaling the density** (§12, p. 282): $\alpha_p(pA) = p^{n(n+1)/2}\,\alpha_p(A)$ (Hanke's Lemma 3.1 with $c = p$;
equivalently $N(p^r)$ for $pA$ is $p^{n^2}N(p^{r-1})$ for $A$). -/
@[kb "conwaysloane1988" "§12, p. 282 (scale change)"]
theorem alphaP_smul_prime {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) :
    alphaP p ((p : ℤ) • A) = (p : ℝ) ^ (n * (n + 1) / 2) * alphaP p A := by
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), pv v = p :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, congrArg Subtype.val
      (Equiv.apply_symm_apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (⟨p, hp⟩ : Nat.Primes))⟩
  have hp0 : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsA : ((pv v : ℤ) • A).IsSymm := by
    unfold Matrix.IsSymm; rw [Matrix.transpose_smul, hA.eq]
  have hdA : ((pv v : ℤ) • A).det ≠ 0 := by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hp0) hdet
  have hsym : ((A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)))ᵀ =
      (A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) := by
    rw [← Matrix.transpose_map, ← Matrix.transpose_map, hA.eq]
  have hdetF : ((A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))).det ≠ 0 := by
    have : ((A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))).det =
        algebraMap _ _ (A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).det :=
      (RingHom.map_det _ _).symm
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))).mpr
      (det_map_ne_zero v hdet)
  have hc : ((pv v : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have h1 := Hanke2005.hankeBeta_std_smul v hsym hdetF hc
  have hsm : ((pv v : ℕ) : v.adicCompletion ℚ) • ((A.map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))) =
      (((pv v : ℤ) • A).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp
  rw [hsm, hankeBeta_eq_half_alphaP v hA hdet, hankeBeta_eq_half_alphaP v hsA hdA,
    norm_prime_completion] at h1
  have hpR : (0 : ℝ) < pv v := by exact_mod_cast hp.pos
  have : alphaP (pv v) A = ((pv v : ℝ))⁻¹ ^ (n * (n + 1) / 2) * alphaP (pv v) ((pv v : ℤ) • A) := by
    linarith
  rw [this, inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- $p^s \,\|\, \det A$ implies $p^{s+n} \,\|\, \det(pA)$. -/
theorem padicValInt_smul_det {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ} (hdet : A.det ≠ 0) :
    padicValInt p (((p : ℤ) • A).det) = n + padicValInt p A.det := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Matrix.det_smul, Fintype.card_fin, padicValInt.mul (pow_ne_zero _ hp0) hdet]
  congr 1
  unfold padicValInt
  simp [padicValNat.prime_pow]

/-- the exponent identity `n(n+1)/2` -/
theorem cast_half (n : ℕ) : ((n * (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  have := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h : (2 : ℝ) * ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) := by exact_mod_cast this
  linarith

/-- **The $p$-mass is invariant under scaling by $p$** (§12, p. 282: "the $p$-mass, unlike the $p$-adic density, is
invariant under changing the scale of the form"): $m_p(pA) = m_p(A)$. -/
@[kb "conwaysloane1988" "§12, p. 282 (scale invariance of the p-mass)"]
theorem pMassDensity_smul_prime {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hdet : A.det ≠ 0) : pMassDensity p ((p : ℤ) • A) = pMassDensity p A := by
  unfold pMassDensity
  rw [alphaP_smul_prime hp hA hdet, padicValInt_smul_det hp hdet]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hα := (alphaP_pos hp hA hdet).ne'
  rw [← Real.rpow_natCast, cast_half]
  have : (p : ℝ) ^ ((((n + padicValInt p A.det : ℕ) : ℝ) * ((n : ℝ) + 1)) / 2) =
      (p : ℝ) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) *
        (p : ℝ) ^ (((padicValInt p A.det : ℝ) * ((n : ℝ) + 1)) / 2) := by
    rw [← Real.rpow_add hpR]; congr 1; push_cast; ring
  rw [this]
  have : (0 : ℝ) < (p : ℝ) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) := by positivity
  field_simp

/-- **Formula (2)** (Conway–Sloane, p. 263), $n \ge 3$: for a symmetric positive definite integral Gram matrix $A$,
$$m(f) = 2\,\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p 2\,m_p(f),$$
where $m(f)$ is `Siegel.mass` of the form $f$ with Gram matrix $A$ (`LocalDensity.ofMatrixZ A`, Hessian $2A$) and the
product runs over all primes ($m_p$ = `pMassDensity`). The product is multipliable with positive value. Unconditional:
it rests on `Hanke2011Structure.cor_6_3_genus` (itself proved from Hanke 2005's Theorem 2.1) and the bridge above. -/
@[kb "conwaysloane1988" "(2), p. 263"]
theorem mass_formula_two (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm)
    (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A)) :
    Multipliable (fun p : Nat.Primes => 2 * pMassDensity p A) ∧
    0 < ∏' p : Nat.Primes, 2 * pMassDensity p A ∧
    Siegel.mass (LocalDensity.ofMatrixZ A) =
      2 * π ^ (-((n : ℝ) * (n + 1) / 4)) * (∏ j ∈ Finset.Icc 1 n, Gamma ((j : ℝ) / 2)) *
        ∏' p : Nat.Primes, 2 * pMassDensity p A := by
  set Q := LocalDensity.ofMatrixZ A with hQdef
  have hdpos : 0 < A.det := det_pos_of_posDef hA hQ
  have hdne : A.det ≠ 0 := hdpos.ne'
  obtain ⟨hm, hP⟩ := mass_eq_invBeta hn hQ
  have hinv := hasProd_inv_localBeta_ofMatrixZ hn hA hQ
  -- the inverse densities as a product over primes
  have hg : HasProd (fun p : Nat.Primes => 2 / alphaP p A) (∏' v, localBeta v (up Q))⁻¹ := by
    have h : HasProd ((fun p : Nat.Primes => 2 / alphaP p A) ∘ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)))
        (∏' v, localBeta v (up Q))⁻¹ := by
      convert hinv using 1
      funext v
      simp only [Function.comp, localBeta_ofMatrixZ v hA hdne]
      have : alphaP (pv v) A ≠ 0 := (alphaP_pos (Rat.HeightOneSpectrum.primesEquiv v).2 hA hdne).ne'
      change 2 / alphaP (pv v) A = _
      field_simp
    exact (Equiv.hasProd_iff _).mp h
  have hD := hasProd_pow_det hdpos (((n : ℝ) + 1) / 2)
  have hprod : HasProd (fun p : Nat.Primes => 2 * pMassDensity p A)
      ((A.det : ℝ) ^ (((n : ℝ) + 1) / 2) * (∏' v, localBeta v (up Q))⁻¹) := by
    convert hD.mul hg using 1
    funext p
    unfold pMassDensity
    have : (p : ℝ) ^ (((padicValInt p A.det : ℝ) * ((n : ℝ) + 1)) / 2) =
        (p : ℝ) ^ ((padicValInt p A.det : ℝ) * (((n : ℝ) + 1) / 2)) := by
      congr 1; ring
    rw [this]
    show 2 * ((p : ℝ) ^ ((padicValInt p A.det : ℝ) * (((n : ℝ) + 1) / 2)) / alphaP p A) =
      (p : ℝ) ^ ((padicValInt p A.det : ℝ) * (((n : ℝ) + 1) / 2)) * (2 / alphaP p A)
    ring
  have hdetpos : (0 : ℝ) < A.det := by exact_mod_cast hdpos
  refine ⟨hprod.multipliable, ?_, ?_⟩
  · rw [hprod.tprod_eq]; positivity
  · rw [hprod.tprod_eq, hm, hessian_det_ofMatrixZ hA]
    have hV : (volV n)⁻¹ = 2 * π ^ (-((n : ℝ) * (n + 1) / 4)) * ∏ i ∈ Finset.Icc 1 n, Gamma ((i : ℝ) / 2) := by
      unfold volV
      rw [show -((n : ℝ) * (n + 1) / 4) = -((n : ℝ) * (n + 1) / 4) from rfl, Real.rpow_neg pi_pos.le,
        mul_inv, mul_inv, Finset.prod_inv_distrib, inv_inv, one_div, inv_inv, inv_eq_one_div]
    have h2 : (((2 ^ n * A.det : ℤ)) : ℝ) ^ (((n : ℝ) + 1) / 2) =
        (2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2) * (A.det : ℝ) ^ (((n : ℝ) + 1) / 2) := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Real.mul_rpow (by positivity) hdetpos.le, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 2; ring
    rw [hV, h2]
    have : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
    field_simp

end QuadFormsKB.ConwaySloane.Mass
