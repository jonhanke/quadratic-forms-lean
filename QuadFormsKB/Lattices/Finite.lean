/-
# Lattices over $\mathcal O_F$: finiteness of the class number of a totally definite genus

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/Genus.lean`).

**Defines** total positive definiteness (`IsTotallyPosDef`: $\sigma(Q(x)) > 0$ for every embedding
$\sigma : F \to \mathbb C$ and every $x \ne 0$; this forces $F$ to be totally real when $n \ge 1$), the isometry classes of
lattices (`LatClass`), the classes in the genus of $L$ (`genusClasses`), and the trace form
$x \mapsto \mathrm{Tr}_{F/\mathbb Q} B(x, x)$ on a lattice viewed as a $\mathbb Z$-lattice of rank $n[F:\mathbb Q]$.

**Proves** (O'Meara 1963, 103:4 [unverified]; for $F = \mathbb Q$, `Siegel.genusFinite`):
* `genusClasses_finite`: **the genus of an integral lattice in a totally positive definite space contains only
  finitely many classes.**
* `finite_autLat`: $O(L)$ is finite (for every lattice $L$).

*Proof (generalizing Hermite reduction).* View a lattice $M$ in the genus as a $\mathbb Z$-lattice of rank
$N = n[F:\mathbb Q]$ with the positive definite integral Gram matrix $G = (\mathrm{Tr}\,B(m_i, m_j))$ of a $\mathbb Z$-basis $m$.
1. *Bounded determinant* (`det_gram_le`): a constant $c \in \mathbb Z$ depending only on $L$ has $c\,M^\sharp \subseteq M$
   for the trace dual $M^\sharp$ of every $M$ in the genus (`smul_mem_of_dual`; local duality at every $\mathfrak p$
   through $M_\mathfrak p = g_\mathfrak p L_\mathfrak p$, and the bound $\delta\,\mathfrak d^{-1} \subseteq \mathcal O_F$ for the
   inverse different, `exists_dual_bound`). Hence $c\,G^{-1}$ is integral and $1 \le \det G \le c^N$.
2. *Reduction:* by Hermite (`Hermite.exists_reduced`) $M$ has a basis whose Gram matrix has entries bounded in terms of
   $N$ and $\det G$; the matrices of multiplication by a $\mathbb Z$-basis $\omega_l$ of $\mathcal O_F$ then have columns $y$ with
   $y^{\mathsf T} G y = \mathrm{Tr}(\omega_l^2 \cdot 2Q(m_j)) \le C_l G_{jj}$ (`trace_mul_sq_le`), so they lie in a finite set.
3. *Rigidity* (`isIsometric_of_data_eq`): two lattices with bases having the same Gram matrix and the same
   multiplication matrices are isometric: the $\mathbb Q$-linear map $m_i \mapsto m'_i$ is $F$-linear and preserves
   $\mathrm{Tr}(a\,B(x, y))$ for all $a \in \mathcal O_F$, hence $B$ (`eq_zero_of_trace_mul`).
-/
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Siegel.GenusFinite

open NumberField IsDedekindDomain WithZero Matrix Module
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-! ### Traces and integers in $F$ -/

section Scalars

/-- **Integer multiples of a nonzero integer:** for $d \ne 0$ in $\mathcal O_F$, some nonzero rational integer $k$ is a
multiple of $d$ (take $k = N(d\mathcal O_F)$, `Ideal.absNorm_mem`). -/
theorem exists_int_dvd {d : 𝓞 F} (hd : d ≠ 0) : ∃ k : ℤ, k ≠ 0 ∧ d ∣ (k : 𝓞 F) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · rw [Nat.cast_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd
  · rw [← Ideal.mem_span_singleton]
    exact_mod_cast Ideal.absNorm_mem (Ideal.span {d})

/-- **Common integer denominators:** finitely many $x_j \in F$ have $k x_j \in \mathcal O_F$ for one nonzero $k \in \mathbb Z$. -/
theorem exists_int_mul_mem (s : Finset F) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ x ∈ s, (k : F) * x ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) s
  obtain ⟨k, hk, r, hr⟩ := exists_int_dvd (nonZeroDivisors.coe_ne_zero b)
  refine ⟨k, hk, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hb x hx
  refine ⟨r * a, ?_⟩
  have e : (k : F) = algebraMap (𝓞 F) F ((b : 𝓞 F) * r) := by rw [← hr]; simp
  rw [e, map_mul, map_mul, ha, Algebra.smul_def]; ring

/-- The trace $\mathrm{Tr}_{F/\mathbb Q}(a)$ of an algebraic integer is a rational integer. -/
theorem trace_int (a : 𝓞 F) :
    Algebra.trace ℚ F (algebraMap (𝓞 F) F a) = (Algebra.intTrace ℤ (𝓞 F) a : ℚ) :=
  (Algebra.algebraMap_intTrace (A := ℤ) (B := 𝓞 F) a).symm

/-- **The trace pairing on $F$ is nondegenerate against $\mathcal O_F$:** if $\mathrm{Tr}(a z) = 0$ for every
$a \in \mathcal O_F$ then $z = 0$. (Take $a = k z^{-1}$ with $k \in \mathbb Z \setminus 0$; then $\mathrm{Tr}(a z) = k[F:\mathbb Q]$.) -/
theorem eq_zero_of_trace_mul {z : F}
    (h : ∀ a : 𝓞 F, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * z) = 0) : z = 0 := by
  by_contra hz
  obtain ⟨k, hk, hks⟩ := exists_int_mul_mem {z⁻¹}
  obtain ⟨a, ha⟩ := hks z⁻¹ (Finset.mem_singleton_self _)
  have := h a
  rw [ha, mul_assoc, inv_mul_cancel₀ hz, mul_one, show (k : F) = algebraMap ℚ F (k : ℚ) by simp,
    Algebra.trace_algebraMap, nsmul_eq_mul] at this
  have hd : (finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  exact hk (by exact_mod_cast (mul_eq_zero.mp this).resolve_left hd)

/-- **The inverse different is bounded:** for some nonzero $\delta \in \mathbb Z$ (the discriminant of $F$), every
$z \in F$ with $\mathrm{Tr}(a z) \in \mathbb Z$ for all $a \in \mathcal O_F$ has $\delta z \in \mathcal O_F$. -/
theorem exists_dual_bound :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : F, (∀ a : 𝓞 F, ∃ t : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * z) = t) →
      (δ : F) * z ∈ (algebraMap (𝓞 F) F).range := by
  classical
  set ω := RingOfIntegers.basis F
  set b := integralBasis F
  set T : Matrix (Free.ChooseBasisIndex ℤ (𝓞 F)) (Free.ChooseBasisIndex ℤ (𝓞 F)) ℤ :=
    Matrix.of fun i j => Algebra.intTrace ℤ (𝓞 F) (ω i * ω j)
  have hT : T.map (Int.castRingHom ℚ) = Algebra.traceMatrix ℚ b := by
    ext i j
    simp only [T, Matrix.map_apply, Matrix.of_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, b, integralBasis_apply, eq_intCast, ← map_mul, trace_int]
    rfl
  refine ⟨T.det, ?_, fun z hz => ?_⟩
  · intro h0
    have : (Algebra.traceMatrix ℚ b).det = 0 := by
      rw [← hT]
      have := RingHom.map_det (Int.castRingHom ℚ) T
      rw [h0, map_zero] at this
      exact this.symm
    exact Algebra.discr_not_zero_of_basis ℚ b (by rw [Algebra.discr_def]; exact this)
  · choose t ht using hz
    -- coordinates of `z` in the integral basis
    set c := b.repr z
    have hz' : z = ∑ j, c j • b j := (b.sum_repr z).symm
    have hTc : ∀ i, ∑ j, Algebra.traceMatrix ℚ b i j * c j = (t (ω i) : ℚ) := by
      intro i
      rw [← ht (ω i)]
      conv_rhs => rw [hz']
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show algebraMap (𝓞 F) F (ω i) = b i from (integralBasis_apply F i).symm, mul_smul_comm,
        map_smul, smul_eq_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]
    -- `δ c = adj(T) t` is integral
    have hc : ∀ j, (T.det : ℚ) * c j = ((T.adjugate *ᵥ fun i => t (ω i)) j : ℤ) := by
      intro j
      have h1 : (T.map (Int.castRingHom ℚ)).adjugate * T.map (Int.castRingHom ℚ) =
          (T.map (Int.castRingHom ℚ)).det • 1 := Matrix.adjugate_mul _
      have h2 := congrArg (fun A => (A *ᵥ c) j) h1
      rw [← mulVec_mulVec, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : T.map (Int.castRingHom ℚ) *ᵥ c = fun i => (t (ω i) : ℚ) := by
        funext i; rw [hT, mulVec, dotProduct]; exact hTc i
      have e1 : (T.map (Int.castRingHom ℚ)).det = (T.det : ℚ) :=
        (RingHom.map_det (Int.castRingHom ℚ) T).symm
      have e2 : (T.map (Int.castRingHom ℚ)).adjugate = T.adjugate.map (Int.castRingHom ℚ) :=
        (RingHom.map_adjugate (Int.castRingHom ℚ) T).symm
      rw [h3, e1, e2] at h2
      rw [← h2]
      exact (RingHom.map_mulVec (Int.castRingHom ℚ) T.adjugate (fun i => t (ω i)) j).symm
    refine ⟨∑ j, ((T.adjugate *ᵥ fun i => t (ω i)) j) • ω j, ?_⟩
    rw [hz', Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul, show b j = algebraMap (𝓞 F) F (ω j) from integralBasis_apply F j,
      Algebra.smul_def, ← mul_assoc]
    congr 1
    rw [show (T.det : F) = algebraMap ℚ F (T.det : ℚ) by simp, ← map_mul, hc j]
    simp

end Scalars

/-! ### Total positivity -/

section Positivity

/-- **Totally positive element:** $\sigma(a) > 0$ (a positive real number) for every embedding
$\sigma : F \to \mathbb C$. -/
def IsTotallyPos (a : F) : Prop := ∀ σ : F →ₐ[ℚ] ℂ, 0 < σ a

/-- **Totally positive definite form** on $F^n$: $Q(x)$ is totally positive for every $x \ne 0$. For $n \ge 1$ this
forces $F$ to be totally real, and it says that $\sigma(Q)$ is positive definite at every real place. -/
@[kb "omeara1963" "§101 (totally positive definite) [unverified]"]
def IsTotallyPosDef (Q : QuadForm F n) : Prop := ∀ x : Fin n → F, x ≠ 0 → IsTotallyPos (Q.eval x)

theorem trace_complex (a : F) : ((Algebra.trace ℚ F a : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ a := by
  rw [← trace_eq_sum_embeddings ℂ (K := ℚ)]; simp

theorem card_embeddings_pos : 0 < Fintype.card (F →ₐ[ℚ] ℂ) := by
  rw [AlgHom.card ℚ F ℂ]; exact Module.finrank_pos

/-- **The trace of a totally positive element is positive.** -/
theorem trace_pos {a : F} (ha : IsTotallyPos a) : 0 < Algebra.trace ℚ F a := by
  have h := congrArg Complex.re (trace_complex a)
  rw [Complex.ratCast_re, Complex.re_sum] at h
  have : (0 : ℝ) < Algebra.trace ℚ F a := by
    rw [h]
    refine Finset.sum_pos (fun σ _ => (Complex.lt_def.mp (ha σ)).1) ?_
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp card_embeddings_pos)
  exact_mod_cast this

/-- The constant $C(a) = \sum_\sigma |\sigma(a)|^2$. -/
def sqBound (a : F) : ℝ := ∑ σ : F →ₐ[ℚ] ℂ, ‖σ a‖ ^ 2

/-- **$\mathrm{Tr}(a^2 b) \le C(a)\,\mathrm{Tr}(b)$ for totally positive $b$** (or $b = 0$). -/
theorem trace_mul_sq_le (a : F) {b : F} (hb : IsTotallyPos b ∨ b = 0) :
    (Algebra.trace ℚ F (a ^ 2 * b) : ℝ) ≤ sqBound a * Algebra.trace ℚ F b := by
  rcases hb with hb | rfl
  swap; · simp
  have h1 := congrArg Complex.re (trace_complex (a ^ 2 * b))
  have h2 := congrArg Complex.re (trace_complex b)
  rw [Complex.ratCast_re, Complex.re_sum] at h1 h2
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hbσ := Complex.lt_def.mp (hb σ)
  have hnorm : ‖σ b‖ = (σ b).re := by
    rw [← Complex.re_add_im (σ b), ← hbσ.2]
    simp only [Complex.zero_im, Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real,
      Complex.ofReal_re, Real.norm_eq_abs]
    exact abs_of_pos (by simpa using hbσ.1)
  calc (σ (a ^ 2 * b)).re ≤ ‖σ (a ^ 2 * b)‖ := Complex.re_le_norm _
    _ = ‖σ a‖ ^ 2 * (σ b).re := by rw [map_mul, map_pow, norm_mul, norm_pow, hnorm]
    _ ≤ sqBound a * (σ b).re := by
      refine mul_le_mul_of_nonneg_right ?_ (by simpa using hbσ.1.le)
      exact Finset.single_le_sum (f := fun τ : F →ₐ[ℚ] ℂ => ‖τ a‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ σ)

end Positivity

/-! ### Duality: a uniform bound $c\,M^\# \subseteq M$ over the genus -/

section Duality

variable (Q : QuadForm F n)

/-- **The polar bilinear form** $B(x, y) = x^{\mathsf T} H y = Q(x+y) - Q(x) - Q(y)$ on $F^n$ (`QuadForm.polar_eq_hessian`). -/
def bil (x y : Fin n → F) : F := x ⬝ᵥ (Q.hessian *ᵥ y)

/-- The polar form over an $F$-algebra $R$: $B_R(x, y) = x^{\mathsf T} H y$. -/
def bilR (R : Type*) [CommRing R] [Algebra F R] (x y : Fin n → R) : R :=
  x ⬝ᵥ (Q.hessian.map (algebraMap F R) *ᵥ y)

theorem bilR_isometry {R : Type*} [CommRing R] [Algebra F R] {g : GL (Fin n) R}
    (hg : g ∈ orthGroup Q R) (x y : Fin n → R) : bilR Q R (g.val *ᵥ x) (g.val *ᵥ y) = bilR Q R x y := by
  rw [bilR, bilR]
  conv_rhs => rw [← (mem_orthGroup Q).mp hg, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

theorem bilR_locVec (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → F) :
    bilR Q (v.adicCompletion F) (locVec v x) (locVec v y) =
      algebraMap F (v.adicCompletion F) (bil Q x y) := by
  rw [bilR, bil, RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec (algebraMap F (v.adicCompletion F)) Q.hessian y i).symm

/-- **Localizing the dual:** if $B(x, M) \subseteq \mathcal O_F$ then $B(x, M_\mathfrak p) \subseteq \mathfrak o_\mathfrak p$. -/
theorem valued_bilR_le_one (v : HeightOneSpectrum (𝓞 F)) {M : Submodule (𝓞 F) (Fin n → F)}
    {x : Fin n → F} (hx : ∀ m ∈ M, bil Q x m ∈ (algebraMap (𝓞 F) F).range)
    {m : Fin n → v.adicCompletion F} (hm : m ∈ loc v M) :
    Valued.v (bilR Q (v.adicCompletion F) (locVec v x) m) ≤ 1 := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨m', hm', rfl⟩ := hm
    obtain ⟨a, ha⟩ := hx m' hm'
    rw [bilR_locVec, ← ha, ← IsScalarTower.algebraMap_apply]
    exact valued_int_le_one v a
  | zero => simp [bilR]
  | add a b _ _ ha hb =>
    rw [bilR, mulVec_add, dotProduct_add]
    exact Valuation.map_add_le _ ha hb
  | smul c m _ hm =>
    have e : bilR Q (v.adicCompletion F) (locVec v x) (c • m) =
        (c : v.adicCompletion F) * bilR Q (v.adicCompletion F) (locVec v x) m := by
      rw [bilR, bilR, mulVec_smul, dotProduct_smul]; rfl
    rw [e, map_mul]
    exact mul_le_one' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2) hm

section LocalDual

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Local duality bound:** if $k\,\mathcal O_F^n \subseteq L$ and $e H^{-1}$ is integral ($k, e \in \mathbb Z$), then every
$y \in F_\mathfrak p^n$ with $B(y, L_\mathfrak p) \subseteq \mathfrak o_\mathfrak p$ has $k^2 e\, y \in L_\mathfrak p$. -/
theorem zsmul_mem_loc_of_dual (hQ : Q.Nondegenerate)
    {L : Submodule (𝓞 F) (Fin n → F)} {k e : ℤ} (hk0 : k ≠ 0)
    (hk : ∀ x ∈ intVec, (k : 𝓞 F) • x ∈ L)
    (he : ∀ i j, (e : F) * Q.hessian⁻¹ i j ∈ (algebraMap (𝓞 F) F).range)
    {y : Fin n → Fv} (hy : ∀ l ∈ loc v L, Valued.v (bilR Q Fv y l) ≤ 1) :
    (k * (e * k)) • y ∈ loc v L := by
  have hsym : ∀ a b, Q.hessian.map (algebraMap F Fv) a b = Q.hessian.map (algebraMap F Fv) b a := by
    intro a b
    simp only [Matrix.map_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, add_comm]
  -- (1) `k (H y)_i` is integral
  have hw : ∀ i, Valued.v ((k : Fv) * (Q.hessian.map (algebraMap F Fv) *ᵥ y) i) ≤ 1 := by
    intro i
    have hl : locVec v ((k : 𝓞 F) • (Pi.single i (1 : F) : Fin n → F)) ∈ loc v L :=
      locVec_mem_loc v (hk _ (single_one_mem_intVec i))
    have := hy _ hl
    have e1 : locVec v ((k : 𝓞 F) • (Pi.single i (1 : F) : Fin n → F)) = Pi.single i (k : Fv) := by
      rw [locVec_smul_int, locVec_single, map_one, ← Pi.single_smul']; congr 1
      change ((algebraMap (𝓞 F) Fv) k) * 1 = _; simp
    have e2 : bilR Q Fv y (Pi.single i (k : Fv)) =
        (k : Fv) * (Q.hessian.map (algebraMap F Fv) *ᵥ y) i := by
      simp only [bilR, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsym j i]; ring
    rwa [e1, e2] at this
  -- (2) `e k y = (e H⁻¹) (k H y)` is in `𝔬^n`
  have hdet : IsUnit Q.hessian.det := isUnit_iff_ne_zero.mpr hQ
  have hinv : Q.hessian⁻¹.map (algebraMap F Fv) * Q.hessian.map (algebraMap F Fv) = 1 := by
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hE : ∀ i j, Valued.v ((e : Fv) * Q.hessian⁻¹.map (algebraMap F Fv) i j) ≤ 1 := by
    intro i j
    obtain ⟨a, ha⟩ := he i j
    have : (e : Fv) * Q.hessian⁻¹.map (algebraMap F Fv) i j = algebraMap (𝓞 F) Fv a := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv, ha, map_mul, map_intCast, Matrix.map_apply]
    rw [this]; exact valued_int_le_one v a
  have hEk : ∀ i, (((e * k : ℤ) : Fv) • y) i =
      ∑ j, ((e : Fv) * Q.hessian⁻¹.map (algebraMap F Fv) i j) *
        ((k : Fv) * (Q.hessian.map (algebraMap F Fv) *ᵥ y) j) := by
    intro i
    have h1 : y = Q.hessian⁻¹.map (algebraMap F Fv) *ᵥ (Q.hessian.map (algebraMap F Fv) *ᵥ y) := by
      rw [mulVec_mulVec, hinv, one_mulVec]
    conv_lhs => rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring_nf
  have hstd : ((e * k : ℤ) : Fv) • y ∈ std v := by
    intro i
    rw [hEk, neg_zero, exp_zero]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_one' (hE i j) (hw j)
  -- (3) `k 𝔬^n ⊆ L_𝔭`
  obtain ⟨k₀, hk₀⟩ := exists_valued_int_eq v (d := (k : 𝓞 F)) (by exact_mod_cast hk0)
  have hball := ball_le_loc v hk hk₀
  have hmem : (algebraMap (𝓞 F) Fv (k : 𝓞 F)) • (((e * k : ℤ) : Fv) • y) ∈ ball v k₀ := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hk₀]
    have := hstd i
    rw [neg_zero, exp_zero] at this
    calc exp (-(k₀ : ℤ)) * Valued.v ((((e * k : ℤ) : Fv) • y) i) ≤ exp (-(k₀ : ℤ)) * 1 :=
          mul_le_mul_right this _
      _ = exp (-(k₀ : ℤ)) := mul_one _
  have := hball hmem
  convert this using 1
  rw [smul_smul, ← Int.cast_smul_eq_zsmul Fv, map_intCast]
  congr 1; simp

end LocalDual

/-- **Integer global bounds:** $k\,\mathcal O_F^n \subseteq L$ and $k L \subseteq \mathcal O_F^n$ for some nonzero
$k \in \mathbb Z$. -/
theorem exists_int_global_bounds {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    ∃ k : ℤ, k ≠ 0 ∧ (∀ x ∈ intVec, (k : 𝓞 F) • x ∈ L) ∧ (∀ x ∈ L, (k : 𝓞 F) • x ∈ intVec) := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  obtain ⟨k, hk, r, hr⟩ := exists_int_dvd hd
  refine ⟨k, hk, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hr, mul_smul]; exact h1 _ (intVec.smul_mem _ hx)
  · rw [hr, mul_smul]; exact h2 _ (L.smul_mem _ hx)

/-- **A uniform dual bound over the genus:** for a nondegenerate $Q$ and a lattice $L$ there is a nonzero $c \in \mathbb Z$
such that for every lattice $M$ in the genus of $L$, every $x$ with $B(x, M) \subseteq \mathcal O_F$ has $c\,x \in M$
($c\,M^\# \subseteq M$). Local at every $\mathfrak p$: $M_\mathfrak p = g_\mathfrak p L_\mathfrak p$ with $g_\mathfrak p$ an isometry. -/
theorem exists_dual_zsmul_mem (hQ : Q.Nondegenerate) {L : Submodule (𝓞 F) (Fin n → F)}
    (hL : L.IsLattice F) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F → SameGenus Q L M →
      ∀ x, (∀ m ∈ M, bil Q x m ∈ (algebraMap (𝓞 F) F).range) → c • x ∈ M := by
  classical
  obtain ⟨k, hk0, hk, -⟩ := exists_int_global_bounds hL
  obtain ⟨e, he0, he⟩ := exists_int_mul_mem
    (Finset.univ.image fun ij : Fin n × Fin n => Q.hessian⁻¹ ij.1 ij.2)
  refine ⟨k * (e * k), mul_ne_zero hk0 (mul_ne_zero he0 hk0), fun M hM hgen x hx => ?_⟩
  rw [mem_iff_forall_loc hM]
  intro v
  obtain ⟨g, hg, hgL⟩ := hgen v
  have hy : ∀ l ∈ loc v L, Valued.v (bilR Q (v.adicCompletion F) (g⁻¹.val *ᵥ locVec v x) l) ≤ 1 := by
    intro l hl
    have hgl : g.val *ᵥ l ∈ loc v M := hgL ▸ ⟨l, hl, rfl⟩
    rw [← bilR_isometry Q hg, mulVec_inv_mulVec]
    exact valued_bilR_le_one Q v hx hgl
  have hmem := zsmul_mem_loc_of_dual Q v hQ hk0 hk
    (fun i j => he _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) hy
  have h2 : locVec v ((k * (e * k)) • x) = g.val *ᵥ ((k * (e * k)) • (g⁻¹.val *ᵥ locVec v x)) := by
    rw [map_zsmul, mulVec_smul, mulVec_inv_mulVec]
  rw [h2, ← hgL]
  exact ⟨_, hmem, rfl⟩

end Duality

/-! ### The underlying $\mathbb Z$-lattice and the trace form -/

section ZStructure

variable (Q : QuadForm F n)

/-- **The underlying $\mathbb Z$-module** of an $\mathcal O_F$-submodule $M \subseteq F^n$. -/
abbrev zLat (M : Submodule (𝓞 F) (Fin n → F)) : Submodule ℤ (Fin n → F) := M.restrictScalars ℤ

omit [NumberField F] in
theorem qsmul_eq (q : ℚ) (y : Fin n → F) [CharZero F] : q • y = (q : F) • y := by
  rw [← algebraMap_smul F q y, eq_ratCast]

/-- **A lattice over $\mathcal O_F$ is a $\mathbb Z$-lattice** in the $\mathbb Q$-vector space $F^n$ (of dimension
$n[F:\mathbb Q]$). -/
theorem zLat_isLattice {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F) :
    (zLat M).IsLattice ℚ where
  fg := by
    have : Module.Finite (𝓞 F) M := Module.Finite.iff_fg.mpr hM.fg
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 F) M
    exact Module.Finite.iff_fg.mp this
  span_eq_top := by
    classical
    obtain ⟨k, hk0, hk, -⟩ := exists_int_global_bounds hM
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm0, hm⟩ := exists_int_mul_mem {x i}
    obtain ⟨a, ha⟩ := hm (x i) (Finset.mem_singleton_self _)
    have hmem : (k : 𝓞 F) • (Pi.single i (algebraMap (𝓞 F) F a) : Fin n → F) ∈ M := by
      refine hk _ fun j => ?_
      by_cases hj : j = i
      · subst hj; exact ⟨a, by simp⟩
      · exact ⟨0, by simp [hj]⟩
    have e : (Pi.single i (x i) : Fin n → F) =
        ((1 : ℚ) / (k * m)) • ((k : 𝓞 F) • (Pi.single i (algebraMap (𝓞 F) F a) : Fin n → F)) := by
      rw [qsmul_eq, ← algebraMap_smul F (k : 𝓞 F), smul_smul, ← Pi.single_smul', smul_eq_mul, ha]
      congr 1
      have hk' : (k : F) ≠ 0 := by exact_mod_cast hk0
      have hm' : (m : F) ≠ 0 := by exact_mod_cast hm0
      push_cast
      field_simp
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- The rank $N = n[F:\mathbb Q] = \dim_{\mathbb Q} F^n$ of the underlying $\mathbb Z$-lattices. -/
abbrev zrank (F : Type*) [Field F] [NumberField F] (n : ℕ) : ℕ := finrank ℚ (Fin n → F)

theorem finrank_zLat {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F) :
    finrank ℤ (zLat M) = zrank F n := by
  have := zLat_isLattice hM
  exact Module.finrank_eq_of_rank_eq ((Submodule.IsLattice.rank' ℚ (zLat M)).trans
    (Module.finrank_eq_rank ℚ (Fin n → F)).symm)

/-- **A $\mathbb Z$-frame** of $M$: a $\mathbb Z$-basis of the underlying $\mathbb Z$-lattice, indexed by `Fin N`. -/
abbrev Frame (M : Submodule (𝓞 F) (Fin n → F)) : Type _ := Basis (Fin (zrank F n)) ℤ (zLat M)

/-- Some $\mathbb Z$-frame of a lattice (it is a free $\mathbb Z$-module of rank $N$). -/
def frame {M : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F) : Frame M :=
  have := zLat_isLattice hM
  Module.finBasisOfFinrankEq ℤ (zLat M) (finrank_zLat hM)

/-- Expansion in a frame: $m = \sum_i c_i m_i$ with $c_i \in \mathbb Z$. -/
theorem coe_eq_sum {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) (m : zLat M) :
    (m : Fin n → F) = ∑ i, b.repr m i • (b i : Fin n → F) := by
  conv_lhs => rw [← b.sum_repr m]
  rw [Submodule.coe_sum]
  rfl

/-- $\mathrm{Tr}_{F/\mathbb Q}$ of an element of $F$ as an integer (when it is one; $0$ otherwise). -/
def trZ (z : F) : ℤ := Classical.epsilon fun t : ℤ => Algebra.trace ℚ F z = t

theorem trZ_eq {z : F} (hz : z ∈ (algebraMap (𝓞 F) F).range) : (trZ z : ℚ) = Algebra.trace ℚ F z := by
  obtain ⟨a, rfl⟩ := hz
  have h : ∃ t : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a) = t := ⟨_, trace_int a⟩
  exact (Classical.epsilon_spec h).symm

/-- For an integral lattice, $B(x, y) \in \mathcal O_F$ for $x, y \in M$. -/
theorem bil_mem {M : Submodule (𝓞 F) (Fin n → F)} (hMi : IsIntegral Q M) {x y : Fin n → F}
    (hx : x ∈ M) (hy : y ∈ M) : bil Q x y ∈ (algebraMap (𝓞 F) F).range := by
  have h := QuadForm.polar_eq_hessian F Q x y
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [e] at h
  rw [bil, ← h]
  exact sub_mem (sub_mem (hMi _ (M.add_mem hx hy)) (hMi _ hx)) (hMi _ hy)

theorem bil_self (x : Fin n → F) : bil Q x x = 2 * Q.eval x := by
  have := two_mul_evalIn Q (R := F) x
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [e] at this
  rw [bil, ← this]

theorem bil_smul_left (a : F) (x y : Fin n → F) : bil Q (a • x) y = a * bil Q x y := by
  rw [bil, bil, smul_dotProduct, smul_eq_mul]

theorem bil_smul_right (a : F) (x y : Fin n → F) : bil Q x (a • y) = a * bil Q x y := by
  rw [bil, bil, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- **The trace form** $(x, y) \mapsto \mathrm{Tr}_{F/\mathbb Q} B(x, y)$, a $\mathbb Q$-bilinear form on $F^n$. -/
def trForm : LinearMap.BilinForm ℚ (Fin n → F) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ F (bil Q x y))
    (fun x x' y => by rw [bil, bil, bil, add_dotProduct, map_add])
    (fun c x y => by
      rw [qsmul_eq, bil_smul_left, show (c : F) * bil Q x y = c • bil Q x y by
        rw [Algebra.smul_def, eq_ratCast], map_smul])
    (fun x y y' => by rw [bil, bil, bil, mulVec_add, dotProduct_add, map_add])
    (fun c x y => by
      rw [qsmul_eq, bil_smul_right, show (c : F) * bil Q x y = c • bil Q x y by
        rw [Algebra.smul_def, eq_ratCast], map_smul])

@[simp] theorem trForm_apply (x y : Fin n → F) :
    trForm Q x y = Algebra.trace ℚ F (bil Q x y) := rfl

/-- **The Gram matrix of the trace form** in a frame: $G_{ij} = \mathrm{Tr}\,B(m_i, m_j) \in \mathbb Z$. -/
def gram {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) : Matrix (Fin (zrank F n)) (Fin (zrank F n)) ℤ :=
  Matrix.of fun i j => trZ (bil Q (b i) (b j))

theorem gram_cast {M : Submodule (𝓞 F) (Fin n → F)} (hMi : IsIntegral Q M) (b : Frame M) (i j) :
    (gram Q b i j : ℚ) = trForm Q (b i) (b j) :=
  trZ_eq (bil_mem Q hMi (b i).2 (b j).2)

/-- The index set of the $\mathbb Z$-basis $\omega$ of $\mathcal O_F$. -/
abbrev OIdx (F : Type*) [Field F] [NumberField F] : Type _ := Free.ChooseBasisIndex ℤ (𝓞 F)

/-- **The matrices of multiplication by $\omega_l$** in a frame: $\omega_l m_j = \sum_i A^{(l)}_{ij} m_i$. -/
def mulMat {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) (l : OIdx F) :
    Matrix (Fin (zrank F n)) (Fin (zrank F n)) ℤ :=
  Matrix.of fun i j =>
    b.repr ⟨RingOfIntegers.basis F l • (b j : Fin n → F), M.smul_mem _ (b j).2⟩ i

theorem omega_smul_eq {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) (l : OIdx F) (j) :
    RingOfIntegers.basis F l • (b j : Fin n → F) = ∑ i, mulMat b l i j • (b i : Fin n → F) :=
  coe_eq_sum b ⟨_, M.smul_mem _ (b j).2⟩

end ZStructure

/-! ### Rigidity: equal frame data gives isometric lattices -/

section Rigidity

variable (Q : QuadForm F n)

/-- Multiplication by $a \in F$, as a $\mathbb Q$-linear map of $F^n$. -/
def smulQ (a : F) : (Fin n → F) →ₗ[ℚ] (Fin n → F) where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [qsmul_eq, qsmul_eq, smul_smul, smul_smul, mul_comm]

theorem single_dotProduct_mulVec_single (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Pi.single i (1 : F) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
  simp

/-- **Rigidity:** two integral lattices with frames having the same Gram matrix and the same multiplication matrices
are isometric. The $\mathbb Q$-linear map $\varphi : m_i \mapsto m'_i$ commutes with each $\omega_l$, hence is $F$-linear;
it preserves the trace form, hence $\mathrm{Tr}(a\,B(\varphi x, \varphi y)) = \mathrm{Tr}(a\,B(x, y))$ for all
$a \in \mathcal O_F$, hence $B$ (`eq_zero_of_trace_mul`); and it maps $M$ onto $M'$. -/
theorem isIsometric_of_data_eq {M M' : Submodule (𝓞 F) (Fin n → F)} (hM : M.IsLattice F)
    (hM' : M'.IsLattice F) (hMi : IsIntegral Q M) (hM'i : IsIntegral Q M') (b : Frame M)
    (b' : Frame M') (hG : gram Q b = gram Q b') (hA : ∀ l, mulMat b l = mulMat b' l) :
    IsIsometric Q M M' := by
  classical
  have := zLat_isLattice hM
  have := zLat_isLattice hM'
  set bt := b.extendOfIsLattice ℚ
  set bt' := b'.extendOfIsLattice ℚ
  set φ := bt.equiv bt' (Equiv.refl _)
  have hφb : ∀ j, φ (b j : Fin n → F) = (b' j : Fin n → F) := by
    intro j
    have := bt.equiv_apply j bt' (Equiv.refl _)
    simpa [bt, bt'] using this
  have hφsum : ∀ c : Fin (zrank F n) → ℤ,
      φ (∑ i, c i • (b i : Fin n → F)) = ∑ i, c i • (b' i : Fin n → F) := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, hφb]
  -- (1) `φ` commutes with the `ω_l`
  have hR1 : ∀ l (x : Fin n → F),
      φ (RingOfIntegers.basis F l • x) = RingOfIntegers.basis F l • φ x := by
    intro l x
    have h : (φ.toLinearMap ∘ₗ smulQ (algebraMap (𝓞 F) F (RingOfIntegers.basis F l))) =
        (smulQ (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) ∘ₗ φ.toLinearMap) := by
      refine bt.ext fun j => ?_
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, smulQ,
        LinearMap.coe_mk, AddHom.coe_mk, bt, Basis.extendOfIsLattice_apply]
      rw [algebraMap_smul, omega_smul_eq, hφsum, hφb, algebraMap_smul, omega_smul_eq, hA]
    have := LinearMap.congr_fun h x
    simpa [smulQ, algebraMap_smul] using this
  -- (2) `φ` is `𝓞_F`-linear
  have hR2 : ∀ (a : 𝓞 F) (x : Fin n → F), φ (a • x) = a • φ x := by
    intro a x
    rw [← (RingOfIntegers.basis F).sum_repr a, Finset.sum_smul, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_assoc, smul_assoc, map_zsmul, hR1]
  -- (3) `φ` is `F`-linear
  have hR3 : ∀ (f : F) (x : Fin n → F), φ (f • x) = f • φ x := by
    intro f x
    obtain ⟨m, hm0, hm⟩ := exists_int_mul_mem {f}
    obtain ⟨a, ha⟩ := hm f (Finset.mem_singleton_self _)
    have hm' : (m : F) ≠ 0 := by exact_mod_cast hm0
    have e : ∀ y : Fin n → F, f • y = ((1 : ℚ) / m) • (a • y) := by
      intro y
      rw [qsmul_eq, ← algebraMap_smul F a y, ha, smul_smul]
      congr 1; push_cast; field_simp
    rw [e, e, map_smul, hR2]
  -- (4) `φ` preserves the trace form
  have hR4 : ∀ x y, trForm Q (φ x) (φ y) = trForm Q x y := by
    have h : (trForm Q).compl₁₂ φ.toLinearMap φ.toLinearMap = trForm Q := by
      refine LinearMap.ext_basis bt bt fun i j => ?_
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, bt, Basis.extendOfIsLattice_apply, hφb]
      rw [← gram_cast Q hM'i, ← gram_cast Q hMi, hG]
    intro x y; exact LinearMap.congr_fun₂ h x y
  -- (5) `φ` preserves `B`
  have hR5 : ∀ x y, bil Q (φ x) (φ y) = bil Q x y := by
    intro x y
    rw [← sub_eq_zero]
    apply eq_zero_of_trace_mul
    intro a
    rw [mul_sub, map_sub, ← bil_smul_left, ← bil_smul_left, algebraMap_smul, algebraMap_smul, ← hR2]
    have := hR4 (a • x) y
    simp only [trForm_apply] at this
    rw [this, sub_self]
  -- (6) the matrix of `φ`
  let φF : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := φ, map_add' := map_add φ, map_smul' := hR3 }
  let ψF : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := φ.symm, map_add' := map_add φ.symm
      map_smul' := fun f x => by
        apply φ.injective
        simp only [RingHom.id_apply, LinearEquiv.apply_symm_apply, hR3] }
  have hφψ : φF ∘ₗ ψF = LinearMap.id :=
    LinearMap.ext fun x => φ.apply_symm_apply x
  have hψφ : ψF ∘ₗ φF = LinearMap.id :=
    LinearMap.ext fun x => φ.symm_apply_apply x
  let γ : GL (Fin n) F := ⟨LinearMap.toMatrix' φF, LinearMap.toMatrix' ψF,
    by rw [← LinearMap.toMatrix'_comp, hφψ, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hψφ, LinearMap.toMatrix'_id]⟩
  have hγ : ∀ x, γ.val *ᵥ x = φ x := fun x => LinearMap.toMatrix'_mulVec φF x
  -- (7) `γ` is an isometry
  have hγO : γ ∈ orthGroup Q F := by
    rw [mem_orthGroup]
    have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
    rw [e]
    ext i j
    have h := hR5 (Pi.single i 1) (Pi.single j 1)
    rw [← hγ, ← hγ] at h
    rw [← single_dotProduct_mulVec_single (γ.valᵀ * Q.hessian * γ.val) i j,
      ← single_dotProduct_mulVec_single Q.hessian i j, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose]
    exact h
  -- (8) `γ M = M'`
  refine ⟨γ, hγO, ?_⟩
  ext y
  rw [mem_glImage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hγ, show x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Fin n → F) from coe_eq_sum b ⟨x, hx⟩, hφsum]
    exact (zLat M').sum_mem fun i _ => (zLat M').smul_mem _ (b' i).2
  · intro hy
    refine ⟨∑ i, b'.repr ⟨y, hy⟩ i • (b i : Fin n → F),
      (zLat M).sum_mem fun i _ => (zLat M).smul_mem _ (b i).2, ?_⟩
    rw [hγ, hφsum]
    exact (coe_eq_sum b' ⟨y, hy⟩).symm

end Rigidity

/-! ### Integrality and definiteness in the genus -/

section GenusIntegral

variable (Q : QuadForm F n)

theorem evalIn_smul' {R : Type*} [CommRing R] [Algebra F R] (c : R) (y : Fin n → R) :
    Q.evalIn R (c • y) = c ^ 2 * Q.evalIn R y := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem evalIn_locVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → F) :
    Q.evalIn (v.adicCompletion F) (locVec v x) = algebraMap F (v.adicCompletion F) (Q.eval x) := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.eval, QuadForm.evalIn_eq_dotProduct,
    RingHom.map_dotProduct]
  congr 1
  funext i
  have := (RingHom.map_mulVec (algebraMap F (v.adicCompletion F))
    (Q.coeff.map (algebraMap F F)) x i).symm
  simp only [Matrix.map_map, Algebra.algebraMap_self] at this
  exact this

theorem bilR_comm {R : Type*} [CommRing R] [Algebra F R] (x y : Fin n → R) :
    bilR Q R x y = bilR Q R y x := by
  have hsym : (Q.hessian.map (algebraMap F R))ᵀ = Q.hessian.map (algebraMap F R) := by
    rw [← Matrix.transpose_map]; congr 1
    simp only [QuadForm.hessian, transpose_add, transpose_transpose, add_comm]
  rw [bilR, bilR, dotProduct_comm, ← vecMul_transpose, hsym, ← dotProduct_mulVec]

/-- For an integral lattice, $B(L_\mathfrak p, L_\mathfrak p) \subseteq \mathfrak o_\mathfrak p$. -/
theorem valued_bilR_loc_le_one (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 F) (Fin n → F)}
    (hLi : IsIntegral Q L) {y y' : Fin n → v.adicCompletion F} (hy : y ∈ loc v L)
    (hy' : y' ∈ loc v L) : Valued.v (bilR Q (v.adicCompletion F) y y') ≤ 1 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact valued_bilR_le_one Q v (fun m hm => bil_mem Q hLi hl hm) hy'
  | zero => simp [bilR]
  | add a b _ _ ha hb =>
    rw [bilR, add_dotProduct]
    exact Valuation.map_add_le _ ha hb
  | smul c m _ hm =>
    rw [bilR, smul_dotProduct]
    change Valued.v ((c : v.adicCompletion F) * _) ≤ 1
    rw [map_mul]
    exact mul_le_one' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2) hm

/-- For an integral lattice, $Q(L_\mathfrak p) \subseteq \mathfrak o_\mathfrak p$. -/
theorem valued_evalIn_loc_le_one (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 F) (Fin n → F)}
    (hLi : IsIntegral Q L) {y : Fin n → v.adicCompletion F} (hy : y ∈ loc v L) :
    Valued.v (Q.evalIn (v.adicCompletion F) y) ≤ 1 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hLi l hl
    rw [evalIn_locVec, show Q.eval l = algebraMap (𝓞 F) F a from ha.symm,
      ← IsScalarTower.algebraMap_apply]
    exact valued_int_le_one v a
  | zero =>
    rw [show (0 : Fin n → v.adicCompletion F) = (0 : v.adicCompletion F) • (0 : Fin n → _) by simp,
      evalIn_smul']
    simp
  | add a b ha' hb' ha hb =>
    have h := QuadForm.polar_eq_hessian (v.adicCompletion F) Q a b
    have e : Q.evalIn (v.adicCompletion F) (a + b) = Q.evalIn (v.adicCompletion F) a +
        Q.evalIn (v.adicCompletion F) b + bilR Q (v.adicCompletion F) a b := by
      rw [bilR, ← h]; ring
    rw [e]
    exact Valuation.map_add_le _ (Valuation.map_add_le _ ha hb)
      (valued_bilR_loc_le_one Q v hLi ha' hb')
  | smul c m _ hm =>
    change Valued.v (Q.evalIn _ ((c : v.adicCompletion F) • m)) ≤ 1
    rw [evalIn_smul', map_mul, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2)) hm

/-- **Integrality is a genus invariant:** a lattice in the genus of an integral lattice is integral. -/
@[kb "omeara1963" "§102 [unverified]"]
theorem SameGenus.isIntegral {L M : Submodule (𝓞 F) (Fin n → F)} (hLi : IsIntegral Q L)
    (h : SameGenus Q L M) : IsIntegral Q M := by
  intro x hx
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one F
  intro v
  obtain ⟨g, hg, he⟩ := h v
  have hmem : locVec v x ∈ loc v M := locVec_mem_loc v hx
  rw [← he] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyx' : g.val *ᵥ y = locVec v x := hyx
  have := valued_evalIn_loc_le_one Q v hLi hy
  rw [← evalIn_mulVec_of_mem Q hg, hyx', evalIn_locVec, valued_algebraMap] at this
  exact this

/-- **A totally positive definite form is nondegenerate.** -/
theorem IsTotallyPosDef.nondegenerate {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) : Q.Nondegenerate := by
  intro h0
  obtain ⟨x, hx, hHx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := bil_self Q x
  rw [bil, hHx, dotProduct_zero] at h
  have h2 : Q.eval x = 0 := by
    have : (2 : F) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp h.symm).resolve_left this
  have := trace_pos (hQ x hx)
  rw [h2, map_zero] at this
  exact lt_irrefl _ this

end GenusIntegral

/-! ### The Gram matrix of a frame: positivity and bounded determinant -/

section GramBounds

variable (Q : QuadForm F n)

theorem bil_comm (x y : Fin n → F) : bil Q x y = bil Q y x := by
  have := bilR_comm Q (R := F) x y
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  simp only [bilR, e] at this
  exact this

theorem trForm_comm (x y : Fin n → F) : trForm Q x y = trForm Q y x := by
  simp only [trForm_apply, bil_comm Q x y]

/-- $\mathrm{Tr}\,B(\sum_i x_i m_i, \sum_j y_j m_j) = \sum_{i,j} x_i y_j\,\mathrm{Tr}\,B(m_i, m_j)$ for integer coefficients. -/
theorem trForm_sum {N : ℕ} (m : Fin N → Fin n → F) (x y : Fin N → ℤ) :
    trForm Q (∑ i, x i • m i) (∑ j, y j • m j) = ∑ i, ∑ j, (x i * y j : ℚ) * trForm Q (m i) (m j) := by
  rw [LinearMap.map_sum₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℚ (x i), ← Int.cast_smul_eq_zsmul ℚ (y j), LinearMap.map_smul₂, map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The trace form is positive definite** for totally positive definite $Q$:
$\mathrm{Tr}\,B(x, x) = 2\,\mathrm{Tr}\,Q(x) > 0$ for $x \ne 0$. -/
theorem trForm_self_pos {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {x : Fin n → F} (hx : x ≠ 0) :
    0 < trForm Q x x := by
  rw [trForm_apply, bil_self, show (2 : F) * Q.eval x = (2 : ℚ) • Q.eval x by
    rw [Algebra.smul_def]; simp, map_smul, smul_eq_mul]
  exact mul_pos two_pos (trace_pos (hQ x hx))

/-- The rational Gram entries: $G_{ij} = \mathrm{Tr}\,B(m_i, m_j)$. -/
theorem dotProduct_gram {M : Submodule (𝓞 F) (Fin n → F)} (hMi : IsIntegral Q M) (b : Frame M)
    (x : Fin (zrank F n) → ℤ) :
    ((x ⬝ᵥ (gram Q b *ᵥ x) : ℤ) : ℚ) =
      trForm Q (∑ i, x i • (b i : Fin n → F)) (∑ i, x i • (b i : Fin n → F)) := by
  rw [trForm_sum]
  simp only [dotProduct, mulVec, Int.cast_sum, Int.cast_mul, gram_cast Q hMi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_ne_zero_of_ne_zero {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M)
    {x : Fin (zrank F n) → ℤ} (hx : x ≠ 0) : ∑ i, x i • (b i : Fin n → F) ≠ 0 := by
  intro h0
  apply hx
  funext i
  have h : ∑ i, x i • b i = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simpa using h0
  exact Fintype.linearIndependent_iff.mp b.linearIndependent x h i

/-- **The Gram matrix of a frame is a positive definite integral symmetric matrix.** -/
theorem gram_isPosDefInt {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hMi : IsIntegral Q M) (b : Frame M) : Siegel.Hermite.IsPosDefInt (gram Q b) := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [gram, Matrix.transpose_apply, Matrix.of_apply, bil_comm Q (b i : Fin n → F)]
  · have h := dotProduct_gram Q hMi b x
    have hpos := trForm_self_pos hQ (sum_ne_zero_of_ne_zero b hx)
    rw [← h] at hpos
    exact_mod_cast hpos

/-- **Bounded determinant over the genus:** for totally positive definite $Q$ and an integral lattice $L$, there is
$B \in \mathbb N$ with $|\det G| \le B$ for the Gram matrix $G$ of every frame of every lattice in the genus of $L$. -/
theorem exists_det_gram_le {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {L : Submodule (𝓞 F) (Fin n → F)}
    (hL : L.IsLattice F) (hLi : IsIntegral Q L) :
    ∃ B : ℕ, ∀ M : Submodule (𝓞 F) (Fin n → F), M.IsLattice F → SameGenus Q L M →
      ∀ b : Frame M, |(gram Q b).det| ≤ B := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_dual_zsmul_mem Q hQ.nondegenerate hL
  obtain ⟨δ, hδ0, hδ⟩ := exists_dual_bound (F := F)
  refine ⟨(c * δ).natAbs ^ zrank F n, fun M hM hgen b => ?_⟩
  have hMi := hgen.isIntegral Q hLi
  have := zLat_isLattice hM
  set N := zrank F n
  set G := gram Q b
  set GQ : Matrix (Fin N) (Fin N) ℚ := G.map (Int.castRingHom ℚ)
  have hGQ : ∀ i j, GQ i j = trForm Q (b i) (b j) := fun i j => gram_cast Q hMi b i j
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hGx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := (gram_isPosDefInt hQ hMi b).2 x hx
    rw [hGx, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hdetQ : GQ.det ≠ 0 := by
    rw [show GQ.det = (G.det : ℚ) from (RingHom.map_det (Int.castRingHom ℚ) G).symm]
    exact_mod_cast hdet
  have hunit : IsUnit GQ.det := isUnit_iff_ne_zero.mpr hdetQ
  -- the dual vectors `d_j = ∑_k (G⁻¹)_{kj} m_k`
  set d : Fin N → Fin n → F := fun j => ∑ k, GQ⁻¹ k j • (b k : Fin n → F)
  have hdual : ∀ j i, trForm Q (d j) (b i) = if j = i then 1 else 0 := by
    intro j i
    simp only [d, map_sum, LinearMap.sum_apply, LinearMap.map_smul₂, smul_eq_mul]
    have : ∑ k, GQ⁻¹ k j * trForm Q (b k) (b i) = (GQ * GQ⁻¹) i j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hGQ, show GQ k i = GQ i k by
        rw [hGQ, hGQ, trForm_comm]]; ring
    rw [this, mul_nonsing_inv _ hunit, Matrix.one_apply]
    simp only [eq_comm]
  have hdualZ : ∀ j (m : Fin n → F), m ∈ M → ∃ t : ℤ, trForm Q (d j) m = t := by
    intro j m hm
    have hm' : m = ∑ i, b.repr ⟨m, hm⟩ i • (b i : Fin n → F) := coe_eq_sum b ⟨m, hm⟩
    refine ⟨b.repr ⟨m, hm⟩ j, ?_⟩
    conv_lhs => rw [hm']
    rw [map_sum]
    simp only [map_zsmul, hdual, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp
  -- `c δ d_j ∈ M`
  have hmem : ∀ j, ((c * δ : ℤ) : 𝓞 F) • d j ∈ M := by
    intro j
    have h1 : ∀ m ∈ M, bil Q ((δ : F) • d j) m ∈ (algebraMap (𝓞 F) F).range := by
      intro m hm
      rw [bil_smul_left]
      refine hδ _ fun a => ?_
      rw [← bil_smul_right, algebraMap_smul]
      exact hdualZ j _ (M.smul_mem a hm)
    have h2 := hc M hM hgen _ h1
    have e : ((c * δ : ℤ) : 𝓞 F) • d j = c • ((δ : F) • d j) := by
      rw [← algebraMap_smul F, map_intCast, ← Int.cast_smul_eq_zsmul F c, smul_smul]
      congr 1; push_cast; ring
    rw [e]; exact h2
  -- hence `c δ G⁻¹` is integral
  set bt := b.extendOfIsLattice ℚ
  set A : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun k j => b.repr ⟨_, hmem j⟩ k
  have hA : A.map (Int.castRingHom ℚ) = ((c * δ : ℤ) : ℚ) • GQ⁻¹ := by
    ext k j
    simp only [A, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
    have h1 : ((((c * δ : ℤ) : 𝓞 F) • d j : Fin n → F)) =
        ∑ k', (((c * δ : ℤ) : ℚ) * GQ⁻¹ k' j) • bt k' := by
      simp only [d, Finset.smul_sum, bt, Basis.extendOfIsLattice_apply]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [← algebraMap_smul F, map_intCast, qsmul_eq, qsmul_eq, smul_smul]
      congr 1; push_cast; ring
    have h2 : ((((c * δ : ℤ) : 𝓞 F) • d j : Fin n → F)) =
        ∑ i, b.repr ⟨_, hmem j⟩ i • (b i : Fin n → F) := coe_eq_sum b ⟨_, hmem j⟩
    have h3 : ((((c * δ : ℤ) : 𝓞 F) • d j : Fin n → F)) =
        ∑ k', ((b.repr ⟨_, hmem j⟩ k' : ℤ) : ℚ) • bt k' := by
      conv_lhs => rw [h2]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [show bt k' = (b k' : Fin n → F) from Basis.extendOfIsLattice_apply ℚ b k']
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    have := congrArg (fun z => bt.repr z k) (h1.symm.trans h3)
    have e1 := congrFun (bt.repr_sum_self (fun k' => ((c * δ : ℤ) : ℚ) * GQ⁻¹ k' j)) k
    have e2 := congrFun (bt.repr_sum_self (fun k' => ((b.repr ⟨_, hmem j⟩ k' : ℤ) : ℚ))) k
    exact (e2.symm.trans (this.symm.trans e1))
  have hprod : G.det * A.det = (c * δ) ^ N := by
    have h1 : GQ * A.map (Int.castRingHom ℚ) = ((c * δ : ℤ) : ℚ) • 1 := by
      rw [hA, Matrix.mul_smul, mul_nonsing_inv _ hunit]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h2
    have e1 : GQ.det = (G.det : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) G).symm
    have e2 : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) A).symm
    rw [e1, e2] at h2
    exact_mod_cast h2
  have hA0 : A.det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ (mul_ne_zero hc0 hδ0) hprod.symm
  have : |G.det| ≤ |G.det| * |A.det| := le_mul_of_one_le_right (abs_nonneg _)
    (Int.one_le_abs hA0)
  rw [← abs_mul, hprod, abs_pow] at this
  calc |G.det| ≤ |c * δ| ^ N := this
    _ = (((c * δ).natAbs ^ N : ℕ) : ℤ) := by push_cast; rw [Int.abs_eq_natAbs]

end GramBounds

/-! ### Hermite reduction of frames and finitely many frame data -/

section Reduction

variable (Q : QuadForm F n)

/-- **Change of frame** by $g \in \mathrm{GL}_N(\mathbb Z)$: $m'_j = \sum_i g_{ij} m_i$. -/
def reframe {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) (g : GL (Fin (zrank F n)) ℤ) : Frame M :=
  b.map (Matrix.GeneralLinearGroup.toLin' b g).toLinearEquiv

theorem reframe_apply {M : Submodule (𝓞 F) (Fin n → F)} (b : Frame M) (g : GL (Fin (zrank F n)) ℤ)
    (j : Fin (zrank F n)) : (reframe b g j : Fin n → F) = ∑ i, g.val i j • (b i : Fin n → F) := by
  rw [reframe, Basis.map_apply, Matrix.GeneralLinearGroup.toLin'_apply, Basis.repr_self,
    Fintype.linearCombination_apply]
  rw [Submodule.coe_sum (zLat M)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul]
  congr 1
  simp [mulVec, dotProduct, Finsupp.single_apply]

/-- The Gram matrix changes by congruence: $G' = g^{\mathsf T} G g$. -/
theorem gram_reframe {M : Submodule (𝓞 F) (Fin n → F)} (hMi : IsIntegral Q M) (b : Frame M)
    (g : GL (Fin (zrank F n)) ℤ) : gram Q (reframe b g) = g.valᵀ * gram Q b * g.val := by
  ext i j
  have h : ((gram Q (reframe b g) i j : ℤ) : ℚ) = ((g.valᵀ * gram Q b * g.val) i j : ℤ) := by
    rw [gram_cast Q hMi, reframe_apply, reframe_apply, trForm_sum, Siegel.Hermite.conj_apply]
    simp only [dotProduct, mulVec, Int.cast_sum, Int.cast_mul, Finset.mul_sum, gram_cast Q hMi]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact_mod_cast h

/-- **Hermite reduction of frames:** every frame can be changed to one whose Gram matrix has entries bounded by
$E_N(\det G)$ (`Siegel.Hermite.entryBound`), with the same determinant. -/
theorem exists_reduced_frame {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hMi : IsIntegral Q M) (b : Frame M) :
    ∃ b' : Frame M, (gram Q b').det = (gram Q b).det ∧
      ∀ i j, |gram Q b' i j| ≤ Siegel.Hermite.entryBound (zrank F n) (gram Q b).det := by
  obtain ⟨g, -, hg⟩ := Siegel.Hermite.exists_reduced (zrank F n) (gram Q b) (gram_isPosDefInt hQ hMi b)
  refine ⟨reframe b g, ?_, fun i j => ?_⟩
  · rw [gram_reframe Q hMi]; exact Siegel.Hermite.det_conj _ g
  · rw [gram_reframe Q hMi]; exact hg i j

/-- **Finitely many bounded integer matrices.** -/
theorem finite_bounded_matrices (N : ℕ) (B : ℤ) :
    {G : Matrix (Fin N) (Fin N) ℤ | ∀ i j, |G i j| ≤ B}.Finite := by
  have hM : {M : Fin N → Fin N → ℤ | ∀ i, M i ∈ {r : Fin N → ℤ | ∀ j, r j ∈ Set.Icc (-B) B}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  refine hM.subset fun G hG i j => ?_
  exact abs_le.mp (hG i j)

/-- **Finitely many short vectors:** for a positive definite integral $G$, $\{y \in \mathbb Z^N : y^{\mathsf T} G y \le T\}$ is
finite (via the integral form with Hessian $2G$, `IntQF.PosDef.finite_setOf_eval_le`). -/
theorem finite_short_vectors {N : ℕ} {G : Matrix (Fin N) (Fin N) ℤ} (hG : Siegel.Hermite.IsPosDefInt G)
    (T : ℤ) : {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ T}.Finite := by
  obtain ⟨QG, hQG⟩ := Siegel.exists_hessian_eq ((2 : ℤ) • G)
    (by
      unfold Matrix.IsSymm
      rw [Matrix.transpose_smul, hG.1.eq])
    (fun i => ⟨G i i, by simp [two_mul]⟩)
  have hev : ∀ y, QG.eval y = y ⬝ᵥ (G *ᵥ y) := by
    intro y
    have := LocalDensity.two_mul_eval_eq_hessian QG y
    rw [hQG, smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    linarith
  have hpos : IntQF.PosDef QG := fun y hy => by rw [hev]; exact hG.2 y hy
  refine (IntQF.PosDef.finite_setOf_eval_le hpos T).subset fun y hy => ?_
  simp only [Set.mem_ofPred_eq, hev]; exact hy

/-- $B(a x, a y) = a^2 B(x, y)$ and $\mathrm{Tr}\,B(\omega x, \omega x) = \mathrm{Tr}(\omega^2 \cdot 2Q(x))$. -/
theorem trForm_smul_self (a : F) (x : Fin n → F) :
    trForm Q (a • x) (a • x) = Algebra.trace ℚ F (a ^ 2 * (2 * Q.eval x)) := by
  rw [trForm_apply, bil_smul_left, bil_smul_right, bil_self]; ring_nf

/-- **The multiplication matrices have short columns:** the $j$-th column $y$ of $A^{(l)}$ has
$y^{\mathsf T} G y = \mathrm{Tr}(\omega_l^2 \cdot 2Q(m_j)) \le C(\omega_l)\,G_{jj}$. -/
theorem mulMat_col_le {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hMi : IsIntegral Q M) (b : Frame M) (l : OIdx F) (j : Fin (zrank F n)) :
    ((((fun i => mulMat b l i j) ⬝ᵥ (gram Q b *ᵥ fun i => mulMat b l i j)) : ℤ) : ℝ) ≤
      sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) * gram Q b j j := by
  have h1 := dotProduct_gram Q hMi b (fun i => mulMat b l i j)
  rw [← omega_smul_eq, ← algebraMap_smul F, trForm_smul_self] at h1
  have h2 : ((gram Q b j j : ℤ) : ℚ) = Algebra.trace ℚ F (2 * Q.eval (b j : Fin n → F)) := by
    rw [gram_cast Q hMi, trForm_apply, bil_self]
  have hb : IsTotallyPos (2 * Q.eval (b j : Fin n → F)) ∨ 2 * Q.eval (b j : Fin n → F) = 0 := by
    by_cases h0 : (b j : Fin n → F) = 0
    · right; rw [h0]; simp [QuadForm.evalIn]
    · left
      intro σ
      rw [map_mul, map_ofNat]
      exact mul_pos two_pos (hQ _ h0 σ)
  have h3 := trace_mul_sq_le (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) hb
  have e1 : ((((fun i => mulMat b l i j) ⬝ᵥ (gram Q b *ᵥ fun i => mulMat b l i j)) : ℤ) : ℝ) =
      ((Algebra.trace ℚ F ((algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) ^ 2 *
        (2 * Q.eval (b j : Fin n → F))) : ℚ) : ℝ) := by
    rw [← h1]; push_cast; rfl
  have e2 : ((gram Q b j j : ℤ) : ℝ) = ((Algebra.trace ℚ F (2 * Q.eval (b j : Fin n → F)) : ℚ) : ℝ) := by
    rw [← h2]; push_cast; rfl
  rw [e1, e2]; exact h3

end Reduction

/-! ### The class number is finite -/

section ClassNumber

variable (Q : QuadForm F n)

/-- **Isometry of lattices** in $(F^n, Q)$ as a setoid on `Lat F n`. -/
def latSetoid : Setoid (Lat F n) where
  r L M := IsIsometric Q L.1 M.1
  iseqv := ⟨fun L => IsIsometric.refl Q L.1, fun h => IsIsometric.symm Q h,
    fun h h' => IsIsometric.trans Q h h'⟩

/-- **Classes of lattices** in $(F^n, Q)$: lattices up to isometry by $O(V)(F)$. -/
abbrev LatClass : Type _ := Quotient (latSetoid Q)

/-- **The classes in the genus** of $L$: $\{\mathrm{cls}(M) : M \in \mathrm{gen}(L)\}$. -/
@[kb "omeara1963" "§102 (classes in a genus) [unverified]"]
def genusClasses (L : Lat F n) : Set (LatClass Q) :=
  {c | ∃ M : Lat F n, Quotient.mk _ M = c ∧ SameGenus Q L.1 M.1}

/-- **Finiteness of the class number** (O'Meara 1963, 103:4 [unverified]; for $F = \mathbb Q$, `Siegel.genusFinite`):
for a totally positive definite $Q$ over the number field $F$ (so $F$ is totally real) and an integral lattice
$L \subseteq F^n$, the genus of $L$ contains only finitely many classes. Proof by Hermite reduction of the trace form
of the underlying $\mathbb Z$-lattices of rank $n[F:\mathbb Q]$ (module docstring). -/
@[kb "omeara1963" "103:4 [unverified]"]
theorem genusClasses_finite {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n)
    (hLi : IsIntegral Q L.1) : (genusClasses Q L).Finite := by
  classical
  set N := zrank F n
  obtain ⟨B, hB⟩ := exists_det_gram_le hQ L.2 hLi
  set Bnd : ℕ := (Finset.Icc (-(B : ℤ)) B).sup fun D => Siegel.Hermite.entryBound N D
  set C : ℝ := ∑ l : OIdx F, sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l))
  have hC : ∀ l, sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) ≤ C := fun l =>
    Finset.single_le_sum (f := fun l : OIdx F => sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)))
      (fun l _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ l)
  set T : ℤ := ⌈C * Bnd⌉
  set Sg := {G : Matrix (Fin N) (Fin N) ℤ | Siegel.Hermite.IsPosDefInt G ∧ ∀ i j, |G i j| ≤ Bnd}
  set Aset : Matrix (Fin N) (Fin N) ℤ → Set (OIdx F → Matrix (Fin N) (Fin N) ℤ) := fun G =>
    {A | ∀ l j, (fun i => A l i j) ∈ {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ T}}
  set S : Set (Matrix (Fin N) (Fin N) ℤ × (OIdx F → Matrix (Fin N) (Fin N) ℤ)) :=
    ⋃ G ∈ Sg, ({G} : Set _) ×ˢ Aset G
  have hSg : Sg.Finite := (finite_bounded_matrices N Bnd).subset fun G hG => hG.2
  have hAset : ∀ G ∈ Sg, (Aset G).Finite := by
    intro G hG
    have hY := finite_short_vectors hG.1 T
    have hY' : (Set.pi Set.univ fun _ : Fin N => {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ T}).Finite :=
      Set.Finite.pi fun _ => hY
    have hYY : (Set.pi Set.univ fun _ : OIdx F => Set.pi Set.univ fun _ : Fin N =>
        {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ T}).Finite := Set.Finite.pi fun _ => hY'
    refine (hYY.image (fun f l => Matrix.of fun i j => f l j i)).subset ?_
    intro A hA
    exact ⟨fun l j i => A l i j, fun l _ j _ => hA l j, by ext l i j; rfl⟩
  have hS : S.Finite := hSg.biUnion fun G hG => (Set.finite_singleton G).prod (hAset G hG)
  -- every class in the genus has a reduced frame with data in `S`
  let P : LatClass Q → (Matrix (Fin N) (Fin N) ℤ × (OIdx F → Matrix (Fin N) (Fin N) ℤ)) → Prop :=
    fun c d => ∃ M : Lat F n, Quotient.mk _ M = c ∧ SameGenus Q L.1 M.1 ∧
      ∃ b : Frame M.1, gram Q b = d.1 ∧ mulMat b = d.2
  have key : ∀ c ∈ genusClasses Q L, ∃ d ∈ S, P c d := by
    rintro c ⟨M, rfl, hgen⟩
    have hMi := hgen.isIntegral Q hLi
    obtain ⟨b, hdet, hb⟩ := exists_reduced_frame hQ hMi (frame M.2)
    have hdB : (gram Q (frame M.2)).det ∈ Finset.Icc (-(B : ℤ)) B :=
      Finset.mem_Icc.mpr (abs_le.mp (hB M.1 M.2 hgen _))
    have hb' : ∀ i j, |gram Q b i j| ≤ Bnd := fun i j => (hb i j).trans (by
      exact_mod_cast Finset.le_sup (f := fun D => Siegel.Hermite.entryBound N D) hdB)
    refine ⟨(gram Q b, mulMat b), ?_, M, rfl, hgen, b, rfl, rfl⟩
    refine Set.mem_biUnion (x := gram Q b) ⟨gram_isPosDefInt hQ hMi b, hb'⟩ ?_
    refine ⟨rfl, fun l j => ?_⟩
    have h1 := mulMat_col_le hQ hMi b l j
    have h2 : (gram Q b j j : ℝ) ≤ Bnd := by
      have := (abs_le.mp (hb' j j)).2; exact_mod_cast this
    have h3 : sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) * gram Q b j j ≤ C * Bnd := by
      have hC0 : 0 ≤ sqBound (algebraMap (𝓞 F) F (RingOfIntegers.basis F l)) :=
        Finset.sum_nonneg fun _ _ => by positivity
      have hG0 : (0 : ℝ) ≤ gram Q b j j := by
        have := (gram_isPosDefInt hQ hMi b).nonneg (Pi.single j 1)
        simp only [mulVec_single_one, dotProduct] at this
        have h : (0 : ℤ) ≤ gram Q b j j := by simpa [Pi.single_apply] using this
        exact_mod_cast h
      calc _ ≤ C * gram Q b j j := mul_le_mul_of_nonneg_right (hC l) hG0
        _ ≤ C * Bnd := mul_le_mul_of_nonneg_left h2 (le_trans hC0 (hC l))
    have : (((fun i => mulMat b l i j) ⬝ᵥ (gram Q b *ᵥ fun i => mulMat b l i j) : ℤ) : ℝ) ≤ T :=
      (h1.trans h3).trans (Int.le_ceil _)
    exact_mod_cast this
  choose! f hfS hfP using key
  refine Set.Finite.of_injOn (f := f) (t := S) (fun c hc => hfS c hc) ?_ hS
  intro c₁ hc₁ c₂ hc₂ he
  obtain ⟨M₁, rfl, hg₁, b₁, hG₁, hA₁⟩ := hfP c₁ hc₁
  obtain ⟨M₂, rfl, hg₂, b₂, hG₂, hA₂⟩ := hfP c₂ hc₂
  apply Quotient.sound
  refine isIsometric_of_data_eq Q M₁.2 M₂.2 (hg₁.isIntegral Q hLi) (hg₂.isIntegral Q hLi) b₁ b₂
    ?_ fun l => ?_
  · rw [hG₁, hG₂, he]
  · rw [show mulMat b₁ = (f (Quotient.mk _ M₁)).2 from hA₁, show mulMat b₂ = (f (Quotient.mk _ M₂)).2 from hA₂, he]

end ClassNumber

/-! ### Finiteness of $O(L)$ and the mass -/

section Mass

variable (Q : QuadForm F n)

theorem bil_isometry {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) (x y : Fin n → F) :
    bil Q (γ.val *ᵥ x) (γ.val *ᵥ y) = bil Q x y := by
  have := bilR_isometry Q hγ x y
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  simp only [bilR, e] at this
  exact this

/-- **$O(L)$ is finite** for an integral lattice $L$ in a totally positive definite space (O'Meara 1963, 104:5
[unverified]): an automorphism is determined by the images of a $\mathbb Z$-frame, which lie among the finitely many
vectors $y$ with $y^{\mathsf T} G y = G_{jj}$. -/
@[kb "omeara1963" "104:5 [unverified]"]
theorem finite_autLat {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hM : M.IsLattice F) (hMi : IsIntegral Q M) : Finite (autLat Q M) := by
  classical
  have := zLat_isLattice hM
  set b := frame hM
  set N := zrank F n
  set G := gram Q b
  have hmem : ∀ γ : autLat Q M, ∀ j, ((γ : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) ∈ M :=
    fun γ j => by
      have h := mulVec_mem_glImage (γ := ((γ : orthGroup Q F) : GL (Fin n) F)) (b j).2
      rwa [(mem_autLat Q).mp γ.2] at h
  let f : autLat Q M → (Fin N → Fin N → ℤ) := fun γ j => b.repr ⟨_, hmem γ j⟩
  have hf : ∀ γ j, ((f γ j : Fin N → ℤ) : Fin N → ℤ) ⬝ᵥ (G *ᵥ f γ j) = G j j := by
    intro γ j
    have h1 := dotProduct_gram Q hMi b (f γ j)
    have h2 : ∑ i, f γ j i • (b i : Fin n → F) = ((γ : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) :=
      (coe_eq_sum b ⟨_, hmem γ j⟩).symm
    rw [h2, trForm_apply, bil_isometry Q (γ : orthGroup Q F).2, ← trForm_apply, ← gram_cast Q hMi] at h1
    exact_mod_cast h1
  set S := Set.pi Set.univ fun j : Fin N => {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ G j j}
  have hS : S.Finite := Set.Finite.pi fun j =>
    finite_short_vectors (gram_isPosDefInt hQ hMi b) (G j j)
  have := hS.to_subtype
  refine Finite.of_injective (fun γ => (⟨f γ, fun j _ => (hf γ j).le⟩ : S)) ?_
  intro γ γ' he
  have he' : f γ = f γ' := congrArg Subtype.val he
  have hb : ∀ j, ((γ : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) =
      ((γ' : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) := by
    intro j
    have e1 : ((γ : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) =
        ∑ i, f γ j i • (b i : Fin n → F) := coe_eq_sum b ⟨_, hmem γ j⟩
    have e2 : ((γ' : orthGroup Q F) : GL (Fin n) F).val *ᵥ (b j : Fin n → F) =
        ∑ i, f γ' j i • (b i : Fin n → F) := coe_eq_sum b ⟨_, hmem γ' j⟩
    rw [e1, e2, he']
  have hlin : (Matrix.mulVecLin ((γ : orthGroup Q F) : GL (Fin n) F).val).restrictScalars ℚ =
      (Matrix.mulVecLin ((γ' : orthGroup Q F) : GL (Fin n) F).val).restrictScalars ℚ := by
    refine (b.extendOfIsLattice ℚ).ext fun j => ?_
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Basis.extendOfIsLattice_apply]
    exact hb j
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  ext i j
  have := congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
  simpa using this

/-- Conjugation $\delta \mapsto \gamma\delta\gamma^{-1}$ carries $O(L)$ onto $O(\gamma L)$. -/
theorem card_autLat_eq_of_isIsometric {M M' : Submodule (𝓞 F) (Fin n → F)} (h : IsIsometric Q M M') :
    Nat.card (autLat Q M) = Nat.card (autLat Q M') := by
  obtain ⟨γ, hγ, rfl⟩ := h
  set g : orthGroup Q F := ⟨γ, hγ⟩
  have hinv : ∀ N : Submodule (𝓞 F) (Fin n → F), glImage γ⁻¹ (glImage γ N) = N := fun N => by
    rw [← glImage_mul, inv_mul_cancel, glImage_one]
  have hinv' : ∀ N : Submodule (𝓞 F) (Fin n → F), glImage γ (glImage γ⁻¹ N) = N := fun N => by
    rw [← glImage_mul, mul_inv_cancel, glImage_one]
  refine Nat.card_congr
    { toFun := fun δ => ⟨g * δ * g⁻¹, ?_⟩
      invFun := fun δ => ⟨g⁻¹ * δ * g, ?_⟩
      left_inv := fun δ => by apply Subtype.ext; simp only; group
      right_inv := fun δ => by apply Subtype.ext; simp only; group }
  · rw [mem_autLat]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, glImage_mul]
    change glImage γ (glImage _ (glImage γ⁻¹ (glImage γ M))) = glImage γ M
    rw [hinv, (mem_autLat Q).mp δ.2]
  · rw [mem_autLat]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, glImage_mul]
    change glImage γ⁻¹ (glImage _ (glImage γ M)) = M
    rw [(mem_autLat Q).mp δ.2, hinv]

/-- **$|O(M)|$ of a class** (well defined by `card_autLat_eq_of_isIsometric`). -/
def LatClass.autCard (c : LatClass Q) : ℕ :=
  Quotient.lift (fun M : Lat F n => Nat.card (autLat Q M.1))
    (fun _ _ h => card_autLat_eq_of_isIsometric Q h) c

/-- **The mass of the genus of $L$** over $F$:
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M) \subseteq \mathrm{gen}(L)} \frac{1}{|O(M)|},$$
a `finsum` over the classes in the genus (finite for totally positive definite $Q$, `genusClasses_finite`), with
$O(M)$ including improper isometries (for $F = \mathbb Q$: `Siegel.mass`). -/
@[kb "omeara1963" "§102 (mass of a genus) [unverified]"]
def mass (L : Lat F n) : ℝ := ∑ᶠ c ∈ genusClasses Q L, ((LatClass.autCard Q c : ℝ))⁻¹

theorem mass_eq_sum {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    mass Q L = ∑ c ∈ (genusClasses_finite hQ L hLi).toFinset, ((LatClass.autCard Q c : ℝ))⁻¹ :=
  finsum_mem_eq_finite_toFinset_sum _ (genusClasses_finite hQ L hLi)

/-- **The mass is positive** for an integral lattice in a totally positive definite space: the class of $L$
contributes $1/|O(L)| > 0$ ($O(L)$ finite, `finite_autLat`) and all terms are $\ge 0$. -/
@[kb "omeara1963" "§102 [unverified]"]
theorem mass_pos {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    0 < mass Q L := by
  rw [mass_eq_sum hQ L hLi]
  have hmem : Quotient.mk (latSetoid Q) L ∈ (genusClasses_finite hQ L hLi).toFinset :=
    (Set.Finite.mem_toFinset _).mpr ⟨L, rfl, SameGenus.refl Q L.1⟩
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun c _ => by positivity) hmem)
  have := finite_autLat hQ L.2 hLi
  have hpos : 0 < Nat.card (autLat Q L.1) := Nat.card_pos
  change (0 : ℝ) < ((Nat.card (autLat Q L.1) : ℕ) : ℝ)⁻¹
  positivity

end Mass

end QuadFormsKB.Lattices
