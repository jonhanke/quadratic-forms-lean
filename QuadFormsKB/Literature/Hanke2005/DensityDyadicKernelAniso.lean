/-
# Hanke 2005, (3.3) at dyadic places: the anisotropic kernels of dimension 2, 3, 4

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), (3.3);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), §3.2, Lemma 3.8, Prop. 3.9;
W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.5), (6.10).

The named input `DyadicKernelDensityLow` (Shimura's density of $\mathbb H^k\perp N$ at a dyadic place, $N$ anisotropic
maximal of dimension $r\in\{2,3,4\}$) is reduced here to two smaller named inputs:

* `DyadicQuaternaryDensity`: $\beta(\pi T'\perp T) = 4q(q+1)^2$ for unimodular binary $T, T'$ with anisotropic residue
  forms (the self-density of the maximal order of the quaternion division algebra);
* `DyadicRamifiedBinaryDensity`: $\beta(N) = 4|\det H_N|^{-1}$ for an anisotropic maximal binary $N$ whose residue zero
  space has dimension $1$ (the ring of integers of a ramified quadratic extension, scaled norm form, every depth).

Everything else is proved, purely locally, from the norm filtration of `DyadicAnisoKernel.lean` and the shapes of
`DyadicAnisoShape.lean`:

* the residue zero count of $N$ is $q^s$, $s = \dim\overline W$, and $r - 2 \le s \le 2$;
* $r = 4$: $s = 2$, $N \simeq \pi T'\perp T$;
* $r = 3$: Shimura's hypothesis forces $s = 2$ (for $s = 1$, $N\simeq\langle\pi c\rangle\perp T$ has $\det$ of odd valuation
  relative to $8$), and $N\simeq\langle u\rangle\perp\pi S$, whose density is `localDensityForm_ram_dyadic`;
* $r = 2$: $s = 0$ is unimodular (excluded by $[\widetilde\Lambda:\Lambda]\ne1$), $s = 2$ gives $N = \pi S$ with $\delta$
  unramified and density $q^3\cdot2(q+1)/q$; $s = 1$ is the ramified case (named input for the density).
-/
import QuadFormsKB.Literature.Hanke2005.DyadicAnisoShape
import QuadFormsKB.Tamagawa.QuaternaryRamDyadic

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadFormsKB.Lattices QuadForm

/-! ### Residue counts over the residue field -/

section Bridge

theorem zeroCount_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {n : ℕ} (P : QuadForm A n) :
    zeroCount (P.map e.toRingHom) = zeroCount P := by
  unfold zeroCount
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => e.toEquiv) fun x => ?_)
  have h : (P.map e.toRingHom).eval (fun i => e.toRingHom (x i)) = e.toRingHom (P.eval x) := by
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [map_mul]
  simp only [Equiv.piCongrRight_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv] at h ⊢
  change P.eval x = 0 ↔ (P.map e.toRingHom).eval (fun i => e.toRingHom (x i)) = 0
  rw [h]
  simp

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem resZero_eq_zeroCount_res {π : R} (hπ : Irreducible π) {m : ℕ} (L : QuadForm R m) :
    resZero π L = zeroCount (L.map (IsLocalRing.residue R)) := by
  have hI : Ideal.span {π ^ 1} = IsLocalRing.maximalIdeal R := by rw [pow_one, hπ.maximalIdeal_eq]
  unfold resZero
  rw [← zeroCount_map_ringEquiv (Ideal.quotEquivOfEq hI)]
  congr 1

/-- **The self-density of a unimodular binary form with anisotropic residue form at a dyadic prime:**
$\beta(S,S) = |O(\bar S)|/q = 2(q+1)/q$. -/
theorem localDensityForm_self_binary_aniso [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (h2π : π ∣ 2) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm T T π = 2 * ((q R : ℝ) + 1) / q R := by
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT le_rfl]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have hfin := finite_quot_pow π hπ 1
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have hmk0 : ∀ x : R, mk x = 0 ↔ π ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  have h2 : (2 : R ⧸ Ideal.span {π ^ 1}) = 0 := by rw [← map_ofNat mk 2, hmk0]; exact h2π
  have hanisoK : ∀ x : Fin 2 → R ⧸ Ideal.span {π ^ 1}, (T.map mk).eval x = 0 → x = 0 := by
    intro x hx
    choose f hf using fun i => Ideal.Quotient.mk_surjective (x i)
    have hxf : x = fun i => mk (f i) := funext fun i => (hf i).symm
    subst hxf
    have : mk (T.eval f) = 0 := by rw [← hx, eval_map_comp']
    have hd := haniso f ((hmk0 _).1 this)
    funext i; exact (hmk0 _).2 (hd i)
  have hb : (T.map mk).coeff 0 1 ≠ 0 := by
    intro h0
    have hdet : (T.map mk).hessian.det = mk T.hessian.det := by
      rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu := hT.map mk
    rw [← hdet] at hu
    have h10 : (T.map mk).coeff 1 0 = 0 := (T.map mk).upper (show (0 : Fin 2) < 1 by decide)
    have : (T.map mk).hessian.det = 0 := by
      simp only [hessian, det_fin_two, Matrix.add_apply, Matrix.transpose_apply, h0, h10]
      rw [show (T.map mk).coeff 0 0 + (T.map mk).coeff 0 0 = 2 * (T.map mk).coeff 0 0 by ring, h2]; ring
    rw [this] at hu; exact not_isUnit_zero hu
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  unfold repCountForm
  rw [card_orth_binary_char2 h2 _ hanisoK hb, hcard]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  push_cast
  ring

end Bridge

/-! ### Maximality at a place -/

section Max

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem pi_dvd_two_of_not_isUnit (h2 : ¬ IsUnit (2 : 𝔬)) : NF.π v ∣ (2 : 𝔬) := by
  by_contra h
  exact h2 (dvr_isUnit_of_not_dvd (NF.irreducible_π v) h)

theorem two_ne_zero_O : (2 : 𝔬) ≠ 0 := by
  intro h
  have := congrArg (algebraMap 𝔬 Fv) h
  simp at this

/-- **Maximality gives $\pi^2\mid N(x)\Rightarrow\pi\mid x$** for an anisotropic $N$ at a dyadic place: $y = x/\pi$ has
$N(y)$ integral, and $H_Ny = H_Nx/\pi$ is integral because $\pi\mid N(x)$ forces $\pi\mid B(x,e_j)$ (norm inequality); so `MaxProp`
makes $y$ integral. -/
theorem hmax_of_maxProp (h2 : ¬ IsUnit (2 : 𝔬)) {r : ℕ} (N : QuadForm 𝔬 r)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv))) (han : ∀ x : Fin r → 𝔬, N.eval x = 0 → x = 0) :
    ∀ x : Fin r → 𝔬, NF.π v ^ 2 ∣ N.eval x → ∀ i, NF.π v ∣ x i := by
  intro x hx i
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  obtain ⟨wq, hwq⟩ := hx
  have hdiv : ∀ j, ∃ c, (N.hessian *ᵥ x) j = NF.π v * c := fun j => by
    have := pi_dvd_polar_of_aniso hπ h2π h20 N han ⟨NF.π v * wq, by rw [hwq]; ring⟩ (Pi.single j 1)
    rw [Hanke2005.dot_hessian_comm, single_dotProduct_one] at this
    exact this
  choose w hw using hdiv
  set π' : Fv := algebraMap 𝔬 Fv (NF.π v) with hπ'
  have hπ0 : π' ≠ 0 := pi_ne_zero_Fv v
  set y : Fin r → Fv := π'⁻¹ • fun i => algebraMap 𝔬 Fv (x i) with hy
  have h1 : Valued.v ((N.map (algebraMap 𝔬 Fv)).eval y) ≤ 1 := by
    have e : (N.map (algebraMap 𝔬 Fv)).eval y = algebraMap 𝔬 Fv wq := by
      rw [hy, eval_smul_sq, eval_map_comp' (algebraMap 𝔬 Fv) N x, hwq, map_mul, map_pow, ← hπ']
      field_simp
    rw [e]
    exact valued_le_one_of_mem v _
  have h2' : ((N.map (algebraMap 𝔬 Fv)).hessian *ᵥ y) ∈ std v := by
    refine mem_std_of_le_one v fun j => ?_
    have e : ((N.map (algebraMap 𝔬 Fv)).hessian *ᵥ y) j = algebraMap 𝔬 Fv (w j) := by
      rw [hessian_map_eq, hy, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have := RingHom.map_mulVec (algebraMap 𝔬 Fv) N.hessian x j
      have e2 : (N.hessian.map (algebraMap 𝔬 Fv) *ᵥ fun i => algebraMap 𝔬 Fv (x i)) j =
          algebraMap 𝔬 Fv ((N.hessian *ᵥ x) j) := this.symm
      rw [e2, hw j, map_mul, ← hπ']
      field_simp
    rw [e]; exact valued_le_one_of_mem v _
  have h3 := v_le_one_of_mem_std v (hmax y h1 h2') i
  refine ⟨toO v (y i) h3, ?_⟩
  apply IsFractionRing.injective 𝔬 Fv
  rw [map_mul]
  change algebraMap 𝔬 Fv (x i) = π' * y i
  rw [hy, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- $\|(\pi^a u)\| = q^{-a}$ for a unit $u$. -/
theorem norm_pi_pow_mul_unit (a : ℕ) {u : 𝔬} (hu : IsUnit u) :
    ‖((NF.π v ^ a * u : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ a)⁻¹ := by
  refine Tamagawa.norm_coe_of_pow_dvd v (dvd_mul_right _ _) fun h => ?_
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ (NF.irreducible_π v).ne_zero)] at h
  exact (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit h hu)

/-- $\|\det H\|$ is invariant under $\mathrm{GL}_n(\mathfrak o)$. -/
theorem norm_det_of_isGLEquiv {n : ℕ} {Q Q' : QuadForm 𝔬 n} (h : DVR.IsGLEquiv Q Q') :
    ‖((Q.hessian.det : 𝔬) : Fv)‖ = ‖((Q'.hessian.det : 𝔬) : Fv)‖ := by
  obtain ⟨u, hu, e⟩ := h.det_hessian
  rw [e]
  have hu1 : ‖((u : 𝔬) : Fv)‖ = 1 := by
    have := norm_pi_pow_mul_unit v 0 hu
    simpa using this
  push_cast
  rw [norm_mul, norm_pow, hu1, one_pow, one_mul]

theorem localDensityForm_of_isGLEquiv {n : ℕ} {Q Q' : QuadForm 𝔬 n} (h : DVR.IsGLEquiv Q Q') :
    localDensityForm Q Q (NF.π v) = localDensityForm Q' Q' (NF.π v) := by
  have hi := Siegel.Kneser.isometricGL_of_isGLEquiv h
  rw [localDensityForm_congr_left hi, localDensityForm_congr_right _ hi]

end Max

/-! ### The named inputs -/

section Inputs

variable (F : Type) [Field F] [NumberField F]

/-- **The self-density of the maximal order of the quaternion division algebra at a dyadic place** (a **named input**;
Shimura 1999, Lemma 3.7(2) and Prop. 3.9, $t = 4$): for unimodular binary forms $T, T'$ over $\mathfrak o_\mathfrak p$ whose
residue forms are anisotropic, $\beta(\pi T'\perp T) = 4q(q+1)^2$ (`localDensityForm` normalization, twice Siegel's $\alpha$).
Field: `density`. Not the conclusion of (3.3): a single explicit local density, below Shimura's level $n\ge3$ only by its
shape. -/
@[kb "shimura1999" "Lemma 3.7(2), Prop. 3.9, p. 18 (t = 4: the maximal order of the quaternion division algebra)"]
structure DyadicQuaternaryDensity : Prop where
  /-- $\beta(\pi T'\perp T) = 4q(q+1)^2$. -/
  density : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ T T' : QuadForm (v.adicCompletionIntegers F) 2, IsUnit T.hessian.det → IsUnit T'.hessian.det →
      (∀ x : Fin 2 → v.adicCompletionIntegers F, NF.π v ∣ T.eval x → ∀ i, NF.π v ∣ x i) →
      (∀ x : Fin 2 → v.adicCompletionIntegers F, NF.π v ∣ T'.eval x → ∀ i, NF.π v ∣ x i) →
      DVR.localDensityForm (orthSum (NF.π v • T') T) (orthSum (NF.π v • T') T) (NF.π v) =
        4 * (normQ v) * (normQ v + 1) ^ 2

/-- **The ramified anisotropic binary kernel at a dyadic place** (a **named input**; Shimura 1999, §3.2 ($t = 2$,
$\mathfrak d\ne\mathfrak r$), Lemma 3.7(2), Prop. 3.9): for an anisotropic binary form $N$ over $\mathfrak o_\mathfrak p$ with
the extension property (`MaxProp`), not unimodular, and not all of whose values lie in $\mathfrak p$ (equivalently its
residue zero space has dimension $1$), $\mathfrak p$ is ramified in $F_\mathfrak p(\sqrt\delta)$, $\delta = -\det H_N/4$, and
$\beta(N,N) = 4\,|\det H_N|^{-1}$. Fields: `ram`, `density`. Checked by brute force over $\mathbb Z_2$ on
$\langle1,2\rangle,\langle1,6\rangle,\langle3,2\rangle$ ($\beta = 32$) and $x^2+2xy+2y^2$, $\langle1,1\rangle$ ($\beta = 16$). -/
@[kb "shimura1999" "§3.2 (t = 2, d ≠ r), Lemma 3.7(2), Prop. 3.9, p. 18 (ramified binary kernel)"]
structure DyadicRamifiedBinaryDensity : Prop where
  /-- $\mathfrak p$ ramifies in $F_\mathfrak p(\sqrt{-\det H_N/4})$. -/
  ram : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ N : QuadForm (v.adicCompletionIntegers F) 2, N.Nondegenerate →
      MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) →
      (∀ y : Fin 2 → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) →
      ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 →
      (¬ ∀ y, NF.π v ∣ N.eval y) →
      ¬ IsUnramSqrt v ((-1) ^ (2 / 2) * (((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ 2))
  /-- $\beta(N,N) = 4|\det H_N|^{-1}$. -/
  density : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ N : QuadForm (v.adicCompletionIntegers F) 2, N.Nondegenerate →
      MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) →
      (∀ y : Fin 2 → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) →
      ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 →
      (¬ ∀ y, NF.π v ∣ N.eval y) →
      DVR.localDensityForm N N (NF.π v) = 4 * ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹

/-- **`DyadicQuaternaryDensity` is proved** (`localDensityForm_quaternary_dyadic`: frame of the $\pi T'$ block, Hensel
transitivity on frames, stabilizer $\cong$ ($\pi$-torsion) $\times O(T)$). -/
@[kb "shimura1999" "Lemma 3.7(2), Prop. 3.9, p. 18 (t = 4)"]
theorem dyadicQuaternaryDensity : DyadicQuaternaryDensity F := by
  refine ⟨fun v h2 T T' hT hT' han han' => ?_⟩
  have h2π : NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    by_contra h
    exact h2 (dvr_isUnit_of_not_dvd (NF.irreducible_π v) h)
  have h20 : (2 : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    have := congrArg (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) h
    simp at this
  rw [Tamagawa.localDensityForm_quaternary_dyadic (NF.irreducible_π v) h20 h2π T T' hT hT' han han',
    DensitySD.q_eq v]

end Inputs

/-! ### Small algebraic facts -/

section Alg

variable {A : Type*} [CommRing A]

theorem orthSum_unary_eq_splitForm (c : A) (S : QuadForm A 2) :
    (orthSum (DVR.unary c) S : QuadForm A 3) = splitForm c S := by
  refine eq_of_eval_eq fun x => ?_
  rw [← Fin.cons_self_tail x, eval_splitForm_cons, QuadForm.eval, evalIn_orthSum]
  simp only [QuadForm.eval]
  congr 1
  simp [DVR.unary, QuadForm.diag, QuadForm.evalIn]

theorem hessian_smul_det_two (c : A) (S : QuadForm A 2) : (c • S).hessian.det = c ^ 2 * S.hessian.det := by
  have : (c • S).hessian = c • S.hessian := by ext i j; simp [QuadForm.hessian]; ring
  rw [this, Matrix.det_smul, Fintype.card_fin]

theorem hessian_unary_det (c : A) : (DVR.unary c).hessian.det = 2 * c := by
  simp [QuadForm.hessian, DVR.unary, QuadForm.diag, Matrix.det_unique]; ring

end Alg

/-! ### The kernel at level $0$ -/

section Base

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- An element of $F_\mathfrak p^\times$ has $\|c\|^2 = q^{2z}$, never an odd power of $q$. -/
theorem norm_sq_ne_odd_pow {c : Fv} (hc : c ≠ 0) {k : ℤ} (hk : Odd k) :
    ‖c‖ ^ 2 ≠ (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  intro h
  have hQ1 : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← NF.q_completion, DensitySD.q_eq v]; exact one_lt_normQ v
  have hQ0 : 0 < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hQ1
  rw [LocalZeta.norm_eq_absNorm_pow v hc, ← zpow_natCast, ← _root_.zpow_mul] at h
  have := zpow_right_injective₀ hQ0 hQ1.ne' h
  obtain ⟨j, hj⟩ := hk
  push_cast at this
  omega

open Classical in
/-- **The anisotropic kernel at level $0$** ($2\le r\le4$): its residue zero count is Shimura's $Z^*$ and its self-density is
$2|D|^{-1}\xi(r)$, from the named inputs `DyadicQuaternaryDensity` ($r = 4$) and `DyadicRamifiedBinaryDensity` ($r = 2$,
residue zero space of dimension $1$); proved for $r = 3$ and $r = 2$ otherwise. -/
theorem kernel_base (I4 : DyadicQuaternaryDensity F) (I2 : DyadicRamifiedBinaryDensity F)
    (h2 : ¬ IsUnit (2 : 𝔬)) {r : ℕ} (hr2 : 2 ≤ r) (N : QuadForm 𝔬 r) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin r → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖dN v N‖⁻¹ ≠ 1)
    (hdet : Odd r → ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ r * c ^ 2‖ = 1) :
    (resZero (NF.π v) N : ℝ) = zStar (normQ v) r (¬ IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r))) ∧
    DVR.localDensityForm N N (NF.π v) =
      2 * ‖dN v N‖⁻¹ * xiShimura (normQ v) r r (¬ IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r))) False := by
  have hr4 : r ≤ 4 := rank_le_four_of_aniso v _ han
  obtain rfl | rfl | rfl : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  all_goals (
    have hπ := NF.irreducible_π v
    have h2π := pi_dvd_two_of_not_isUnit v h2
    have h20 := two_ne_zero_O v
    have han' := aniso_integral v N han
    have hmax' := hmax_of_maxProp v h2 N hmax han'
    set W := resZeroSub hπ h2π h20 N han' with hW
    set s := Module.finrank (IsLocalRing.ResidueField 𝔬) W with hs
    have hq := DensitySD.q_eq v
    have hZ : (resZero (NF.π v) N : ℝ) = (normQ v) ^ s := by
      rw [resZero_eq_zeroCount_res hπ, zeroCount_eq_pow_finrank hπ h2π h20 N han', ← hq]
      push_cast
      rfl
    have hlo := le_finrank_resZeroSub_add_two hπ h2π h20 N han'
    have hhi := finrank_resZeroSub_le_two hπ h2π h20 N han' hmax'
    rw [← hW, ← hs] at hlo hhi
    have hq1 : 1 < normQ v := one_lt_normQ v
    have hq0 : 0 < normQ v := lt_trans zero_lt_one hq1
    obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
    have hn2 : ‖((2 : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := Tamagawa.norm_coe_of_pow_dvd v he he')
  · -- `r = 2`
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
    · -- unimodular: excluded
      exfalso
      apply hD
      have hNan : ∀ y : Fin 2 → 𝔬, NF.π v ∣ N.eval y → ∀ i, NF.π v ∣ y i := by
        intro y hy i
        have hW0 : W = ⊥ := Submodule.finrank_eq_zero.mp (hs.symm.trans hs0)
        have hmem : (fun j => IsLocalRing.residue 𝔬 (y j)) ∈ W := by
          rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ]; exact hy
        rw [hW0, Submodule.mem_bot] at hmem
        exact (res_eq_zero_iff' hπ _).1 (congrFun hmem i)
      have hu := isUnit_det_of_aniso hπ h2π N hNan
      have := norm_pi_pow_mul_unit v 0 hu
      simp only [pow_zero, one_mul, inv_one] at this
      rw [dN, this, inv_one]
    · -- ramified: the named input
      have hnot : ¬ ∀ y, NF.π v ∣ N.eval y := by
        intro hall
        have htop : W = ⊤ := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨x', rfl⟩ := res_surj_vec x
          rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ]
          exact hall x'
        have : s = 2 := by rw [hs, htop, finrank_top, Module.finrank_fin_fun]
        omega
      have hram := I2.ram v h2 N hN hmax han hD hnot
      have hβ := I2.density v h2 N hN hmax han hD hnot
      refine ⟨?_, ?_⟩
      · rw [hZ, hs1, pow_one, zStar, if_neg (by decide), if_pos ⟨rfl, hram⟩]
      · rw [hβ]
        simp only [xiShimura]
        rw [if_pos hram]
        simp [ppow]
        ring
    · -- `N = π S`, unramified
      have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [← hs, hs2, Module.finrank_fin_fun])
      have hall : ∀ y, NF.π v ∣ N.eval y := by
        intro y
        have : (fun j => IsLocalRing.residue 𝔬 (y j)) ∈ W := by rw [htop]; trivial
        rwa [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ] at this
      obtain ⟨S, hS⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero N hall
      have hSan : ∀ y : Fin 2 → 𝔬, NF.π v ∣ S.eval y → ∀ i, NF.π v ∣ y i := fun y hy i =>
        hmax' y (by rw [hS, eval_smul_form, pow_two]; exact mul_dvd_mul_left _ hy) i
      have hSu := isUnit_det_of_aniso hπ h2π S hSan
      have hb := not_dvd_coeff01_of_aniso hπ h2π S hSan
      have hbu : IsUnit (S.coeff 0 1) := dvr_isUnit_of_not_dvd hπ hb
      have hdetN : N.hessian.det = NF.π v ^ 2 * S.hessian.det := by rw [hS, hessian_smul_det_two]
      have hnD : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by rw [dN, hdetN, norm_pi_pow_mul_unit v 2 hSu]
      -- `δ` is unramified
      have hunram : IsUnramSqrt v ((-1) ^ (2 / 2) * (dN v N / 2 ^ 2)) := by
        obtain ⟨binv, hbinv⟩ := hbu.exists_right_inv
        have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := pi_ne_zero_Fv v
        have hb0 : ((S.coeff 0 1 : 𝔬) : Fv) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hbu.ne_zero
        have hbinv' : ((binv : 𝔬) : Fv) = ((S.coeff 0 1 : 𝔬) : Fv)⁻¹ := by
          refine eq_inv_of_mul_eq_one_left ?_
          have := congrArg (fun z : 𝔬 => (z : Fv)) hbinv
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
          rw [mul_comm]; exact this
        refine ⟨2 / (((NF.π v : 𝔬) : Fv) * ((S.coeff 0 1 : 𝔬) : Fv)), div_ne_zero two_ne_zero (mul_ne_zero hπ0 hb0), -(S.coeff 0 0 * S.coeff 1 1 * binv ^ 2), ?_, ?_⟩
        · refine dvr_isUnit_of_not_dvd hπ fun h => hπ.not_isUnit (isUnit_of_dvd_one ?_)
          have h4 : NF.π v ∣ 4 * -(S.coeff 0 0 * S.coeff 1 1 * binv ^ 2) :=
            dvd_mul_of_dvd_left (h2π.trans ⟨2, by norm_num⟩) _
          have := dvd_sub h h4
          simpa using this
        · rw [dN, hdetN, det_hessian_binary]
          push_cast
          rw [hbinv']
          field_simp
          push_cast
          rw [show ((4 : 𝔬) : Fv) = 4 from map_ofNat (algebraMap 𝔬 Fv) 4]
          ring
      have hram : ¬ ¬ IsUnramSqrt v ((-1) ^ (2 / 2) * (dN v N / 2 ^ 2)) := not_not.mpr hunram
      refine ⟨?_, ?_⟩
      · rw [hZ, hs2, zStar, if_neg (by decide), if_neg (fun h => hram h.2)]
      · rw [show N = NF.π v • S from hS] at hN ⊢
        have hSnd : S.Nondegenerate := hSu.ne_zero
        rw [Tamagawa.localDensityForm_smul S hSnd hπ (o := 1) (by simp)
            (fun h => hπ.not_isUnit (isUnit_of_dvd_one (by
              rw [pow_two] at h; exact (mul_dvd_mul_iff_left hπ.ne_zero).mp (by simpa using h)))),
          localDensityForm_self_binary_aniso hπ h2π S hSu hSan]
        rw [← hS, hnD, hq]
        simp only [xiShimura]
        rw [if_neg hram, if_neg not_false]
        norm_num [ppow]
        field_simp
        ring
  · -- `r = 3`
    rcases (show s = 1 ∨ s = 2 by omega) with hs1 | hs2
    · -- `s = 1` contradicts Shimura's determinant hypothesis
      exfalso
      obtain ⟨M, T, hTu, hTan, hMd, hM⟩ := exists_shape_top (m := 1) hπ h2π h20 N han' hs1
      have hMc : M = DVR.unary (M.coeff 0 0) := diag_of_rank_one M
      have hc : NF.π v ∣ M.coeff 0 0 := by
        have := hMd (Pi.single 0 1); rwa [Tamagawa.eval_single_rd] at this
      obtain ⟨c', hc'⟩ := hc
      have hmax2 := hmax_of_isGLEquiv hM hmax'
      have hc'u : IsUnit c' := by
        refine dvr_isUnit_of_not_dvd hπ fun h => ?_
        have h1 := hmax2 (Fin.append (Pi.single 0 1) 0) ?_ (Fin.castAdd 2 0)
        · simp at h1; exact hπ.not_isUnit (isUnit_of_dvd_one h1)
        · rw [eval_orthSum_append, Tamagawa.eval_single_rd, hc']
          obtain ⟨d, hd⟩ := h
          refine ⟨d, ?_⟩
          rw [hd]; simp [QuadForm.eval, QuadForm.evalIn]; ring
      have hdetN : ‖dN v N‖ = ‖((2 : 𝔬) : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ := by
        rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hMc, hessian_unary_det, hc',
          show (2 : 𝔬) * (NF.π v * c') * T.hessian.det = 2 * (NF.π v ^ 1 * (c' * T.hessian.det)) by ring]
        push_cast
        rw [norm_mul]
        congr 1
        exact_mod_cast norm_pi_pow_mul_unit v 1 (hc'u.mul hTu)
      obtain ⟨c, hc0, hcn⟩ := hdet (by decide)
      apply norm_sq_ne_odd_pow v hc0 (k := 1 - 2 * (e : ℤ)) ⟨-(e : ℤ), by ring⟩
      rw [norm_mul, norm_div, norm_pow, norm_pow, hdetN] at hcn
      have h2c : ‖(2 : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by rw [← hn2, ← map_ofNat (algebraMap 𝔬 Fv) 2]; rfl
      rw [hn2, h2c, NF.q_completion] at hcn
      have hQ0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
        rw [← NF.q_completion, hq]; exact hq0
      rw [show (1 : ℤ) - 2 * (e : ℤ) = 1 - ((2 * e : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ hQ0.ne', zpow_one,
        zpow_natCast]
      field_simp at hcn ⊢
      linear_combination hcn
    · -- `s = 2`: `N ≃ ⟨u⟩ ⊥ π S`
      obtain ⟨M, S, hSu, hSan, hM⟩ := exists_shape_bottom (m := 1) hπ h2π h20 N han' hmax' hs2
      have hMc : M = DVR.unary (M.coeff 0 0) := diag_of_rank_one M
      set u := M.coeff 0 0 with hu
      have hmax2 := hmax_of_isGLEquiv hM hmax'
      have han2 := aniso_of_isGLEquiv hM han'
      have huu : IsUnit u := by
        refine dvr_isUnit_of_not_dvd hπ fun hc => ?_
        have htop : resZeroSub hπ h2π h20 _ han2 = ⊤ := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨x', rfl⟩ := res_surj_vec x
          rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ, QuadForm.eval, evalIn_orthSum]
          refine dvd_add ?_ ?_
          · rw [hMc]
            simp [DVR.unary, QuadForm.diag, QuadForm.evalIn]
            exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hc _) _
          · change NF.π v ∣ (NF.π v • S).eval _
            rw [eval_smul_form]; exact dvd_mul_right _ _
        have := finrank_resZeroSub_le_two hπ h2π h20 _ han2 hmax2
        rw [htop, finrank_top, Module.finrank_fin_fun] at this
        omega
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0; exact absurd (by simpa using h2π) he'
        · exact h0
      have hβ := localDensityForm_ram_dyadic hπ h20 ⟨he, he'⟩ he1 huu S hSu hSan
      have hdetN : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ (e + 2))⁻¹ := by
        rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hMc, hessian_unary_det,
          hessian_smul_det_two]
        obtain ⟨w, hw⟩ := he
        have hwu : IsUnit w := dvr_isUnit_of_not_dvd hπ fun h => he' (by
          rw [hw, pow_succ]; exact mul_dvd_mul_left _ h)
        rw [hw, show NF.π v ^ e * w * u * (NF.π v ^ 2 * S.hessian.det) =
          NF.π v ^ (e + 2) * (w * u * S.hessian.det) by ring]
        exact norm_pi_pow_mul_unit v (e + 2) ((hwu.mul huu).mul hSu)
      refine ⟨?_, ?_⟩
      · rw [hZ, hs2]; simp [zStar]
      · rw [localDensityForm_of_isGLEquiv v hM, hMc, orthSum_unary_eq_splitForm, hβ, hdetN, hq]
        simp only [xiShimura]; norm_num [ppow]
        ring
  · -- `r = 4`: `N ≃ π T' ⊥ T`
    have hs2 : s = 2 := by omega
    obtain ⟨M, T, hTu, hTan, hMd, hM⟩ := exists_shape_top (m := 2) hπ h2π h20 N han' hs2
    obtain ⟨T', hT'⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero M hMd
    rw [hT'] at hM
    have hmax2 := hmax_of_isGLEquiv hM hmax'
    have hT'an : ∀ y : Fin 2 → 𝔬, NF.π v ∣ T'.eval y → ∀ i, NF.π v ∣ y i := by
      intro y hy i
      have h := hmax2 (Fin.append y 0) (by
        rw [eval_orthSum_append, eval_smul_form, pow_two]
        have h0 : T.eval (0 : Fin 2 → 𝔬) = 0 := by simp [QuadForm.eval, QuadForm.evalIn]
        rw [h0, add_zero]
        exact mul_dvd_mul_left _ hy) (Fin.castAdd 2 i)
      simpa using h
    have hT'u := isUnit_det_of_aniso hπ h2π T' hT'an
    have hβ := I4.density v h2 T T' hTu hT'u hTan hT'an
    have hnD : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
      rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hessian_smul_det_two,
        mul_assoc]
      exact norm_pi_pow_mul_unit v 2 (hT'u.mul hTu)
    refine ⟨?_, ?_⟩
    · rw [hZ, hs2]; simp [zStar]
    · rw [localDensityForm_of_isGLEquiv v hM, hβ, hnD, hq]
      simp only [xiShimura]
      norm_num [ppow]
      have hq' : normQ v - 1 ≠ 0 := (sub_pos.mpr hq1).ne'
      simp only [Real.rpow_neg_one]
      field_simp
      ring

end Base

/-! ### The reduction -/

section Reduction

variable {F : Type} [Field F] [NumberField F]

/-- **`DyadicKernelDensityLow` from the two small inputs** (purely local; see the module docstring): the kernel data at
level $0$ (`kernel_base`) propagate along the recursion `localDensityForm_hypSum_succ` / `xiShimura_succ`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N, r = 2, 3, 4; quoting Shimura 1999, Thm 8.6(3), Prop. 3.9)"]
theorem dyadicKernelDensityLow_of_inputs (I4 : DyadicQuaternaryDensity F) (I2 : DyadicRamifiedBinaryDensity F) :
    DyadicKernelDensityLow F := by
  classical
  refine ⟨fun v h2 {k r} _ _ hr2 N hN hmax han hD hdet => ?_⟩
  set D := dN v N with hDdef
  set ram0 : Prop := ¬ IsUnramSqrt v ((-1) ^ (r / 2) * (D / 2 ^ r)) with hram0
  have hD0 : ‖D‖⁻¹ ≠ 1 := by rw [← norm_det_hypSum v N k]; exact hD
  have hdet0 : Odd r → ∃ c : v.adicCompletion F, c ≠ 0 ∧ ‖D / 2 ^ r * c ^ 2‖ = 1 := fun hodd =>
    (detHyp_hypSum v N k).1 (hdet (by rw [Nat.odd_iff] at hodd ⊢; omega))
  obtain ⟨hZ, hβ0⟩ := kernel_base v I4 I2 h2 hr2 N hN hmax han hD0 hdet0
  rw [norm_det_hypSum, ram_hypSum, ← hDdef, ← hram0, eq_false hD0]
  set β : ℕ → ℝ := fun j => DVR.localDensityForm (hypSum N j) (hypSum N j) (NF.π v) with hβdef
  set S : ℕ → ℝ := fun j => 2 * ‖D‖⁻¹ * xiShimura (normQ v) (r + 2 * j) r ram0 False with hSdef
  show β k = S k
  have hq : ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) = normQ v := DensitySD.q_eq v
  have hrec : ∀ j, β (j + 1) = rho (normQ v) r (zStar (normQ v) r ram0) j * β j := by
    intro j
    simp only [hβdef]
    rw [localDensityForm_hypSum_succ (NF.irreducible_π v) N hN (aniso_integral v N han) j, hq, hZ]
  have hSrec : ∀ j, S (j + 1) = rho (normQ v) r (zStar (normQ v) r ram0) j * S j := by
    intro j
    simp only [hSdef]
    rw [xiShimura_succ (one_lt_normQ v) (by omega) (rank_le_four_of_aniso v _ han) ram0 j]
    ring
  have h0 : β 0 = S 0 := hβ0
  exact eq_of_rec 0 hrec hSrec h0 k (Nat.zero_le _)

/-- **`ShimuraMaximalDensityRest` (hence (3.3) at every place) from the two small inputs.** -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places; dyadic kernels from the quaternary and ramified binary densities)"]
theorem shimuraMaximalDensityRest_of_inputs (I4 : DyadicQuaternaryDensity F) (I2 : DyadicRamifiedBinaryDensity F) :
    ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_low (dyadicKernelDensityLow_of_inputs I4 I2)

end Reduction

end QuadFormsKB.Hanke2005
