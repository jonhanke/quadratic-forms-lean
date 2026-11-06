/-
# Hanke 2005, (3.3) at odd places: the Jordan shape of a maximal lattice

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

This file proves `OddMaximalJordan` (`oddMaximalJordan`) (the Jordan shape $\langle u\rangle\perp\pi W$ of a maximal lattice at a non-dyadic place).
The maximality of $\mathfrak o_\mathfrak p^n$ for the form $Q_\mathfrak p$ (`isMaximal_loc`) is turned into the extension property
`MaxProp`: if $y\in F_\mathfrak p^n$ has $Q(y)\in\mathfrak o_\mathfrak p$ and $Hy\in\mathfrak o_\mathfrak p^n$, then $y\in\mathfrak o_\mathfrak p^n$ (otherwise
$\mathfrak o_\mathfrak p^n+\mathfrak o_\mathfrak p y$ is a larger lattice of integral norm).
-/
import QuadFormsKB.Literature.Hanke2005.DensityOddShape
import QuadFormsKB.Literature.Hanke2005.MaximalLocal
import QuadFormsKB.Literature.Hanke2005.TheoremSixThree
import QuadFormsKB.Siegel.KneserConnectedProof

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section SortPerm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **A permutation of the variables is a $\mathrm{GL}$-equivalence of diagonal forms.** -/
theorem isGLEquiv_diag_perm {m : ℕ} (d : Fin m → R) (σ : Equiv.Perm (Fin m)) :
    DVR.IsGLEquiv (QuadForm.diag d) (QuadForm.diag (d ∘ σ)) := by
  refine ⟨(1 : Matrix (Fin m) (Fin m) R).submatrix σ.symm id, ?_, fun x => ?_⟩
  · rw [Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hx : ((1 : Matrix (Fin m) (Fin m) R).submatrix σ.symm id) *ᵥ x = x ∘ σ.symm := by
      have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin m) (Fin m) R) x σ.symm (Equiv.refl _)
      simpa using this
    rw [hx, Siegel.Kneser.eval_diag, Siegel.Kneser.eval_diag]
    simp only [Function.comp]
    exact (Finset.sum_congr rfl fun i _ => by simp).trans (Equiv.sum_comp σ (fun j => d j * (x (σ.symm j)) ^ 2))

theorem diag_succ_gen {a : ℕ} (u : Fin (a + 1) → R) :
    QuadForm.diag u = splitForm (u 0) (QuadForm.diag (Fin.tail u)) := by
  refine QuadForm.ext ?_
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [QuadForm.diag, splitForm_coeff, Matrix.diagonal_apply, Fin.succ_ne_zero, Fin.tail,
      (Fin.succ_ne_zero _).symm, Fin.succ_inj]

/-- The coefficient sequence of $\langle u\rangle\perp\langle t\rangle$: $u$ first, then $t$. -/
def cseq {b : ℕ} (t : Fin b → R) : (a : ℕ) → (Fin a → R) → Fin (b + a) → R
  | 0, _ => t
  | a + 1, u => Fin.cons (u 0) (cseq t a (Fin.tail u))

theorem unitSum_diag {b : ℕ} (t : Fin b → R) :
    ∀ (a : ℕ) (u : Fin a → R), unitSum (QuadForm.diag t) a u = QuadForm.diag (cseq t a u)
  | 0, u => rfl
  | a + 1, u => by
    show splitForm (u 0) (unitSum (QuadForm.diag t) a (Fin.tail u)) = _
    rw [unitSum_diag t a (Fin.tail u)]
    rw [diag_succ_gen (cseq t (a + 1) u)]
    simp [cseq]

theorem cseq_lt {b : ℕ} (t : Fin b → R) :
    ∀ (a : ℕ) (u : Fin a → R) (i : Fin (b + a)) (h : i.val < a), cseq t a u i = u ⟨i.val, h⟩
  | 0, u, i, h => absurd h (Nat.not_lt_zero _)
  | a + 1, u, i, h => by
    refine Fin.cases ?_ (fun j => ?_) i h
    · intro h; simp [cseq]
    · intro h
      simp only [cseq, Fin.cons_succ]
      rw [cseq_lt t a (Fin.tail u) j (by simpa using h)]
      rfl

theorem cseq_ge {b : ℕ} (t : Fin b → R) :
    ∀ (a : ℕ) (u : Fin a → R) (i : Fin (b + a)) (h : a ≤ i.val), cseq t a u i = t ⟨i.val - a, by omega⟩
  | 0, u, i, h => by simp [cseq]
  | a + 1, u, i, h => by
    refine Fin.cases ?_ (fun j => ?_) i h
    · intro h; simp at h
    · intro h
      simp only [cseq, Fin.cons_succ]
      rw [cseq_ge t a (Fin.tail u) j (by simpa using h)]
      simp

/-- **Sorting the exponents:** a diagonal form $\langle\pi^{\nu_i}u_i\rangle$ with $\nu_i\in\{0,1\}$ and unit $u_i$ is $\mathrm{GL}$-equivalent to
$\langle u'\rangle\perp\langle\pi w\rangle$ (`unitSum`) with unit $u'_i$, $w_j$ (units first). -/
theorem exists_shape_of_nu (π : R) {n : ℕ} (ν : Fin n → ℕ) (hν : ∀ i, ν i ≤ 1) (u : Fin n → R)
    (hu : ∀ i, IsUnit (u i)) :
    ∃ (a b : ℕ) (h : b + a = n) (u' : Fin a → R) (w : Fin b → R), (∀ i, IsUnit (u' i)) ∧ (∀ j, IsUnit (w j)) ∧
      DVR.IsGLEquiv (QuadForm.diag fun i => π ^ ν i * u i)
        (h ▸ unitSum (QuadForm.diag fun j => π * w j) a u') := by
  classical
  set σ := Tuple.sort ν with hσ
  have hmono : Monotone (ν ∘ σ) := Tuple.monotone_sort ν
  have hperm := isGLEquiv_diag_perm (fun i => π ^ ν i * u i) σ
  -- the number of zero exponents
  obtain ⟨a, ha, hzero⟩ : ∃ a, a ≤ n ∧ ∀ i : Fin n, (ν (σ i) = 0 ↔ i.val < a) := by
    by_cases hex : ∃ i, ν (σ i) ≠ 0
    · have hne : (Finset.univ.filter fun i => ν (σ i) ≠ 0).Nonempty := by
        obtain ⟨i, hi⟩ := hex; exact ⟨i, by simpa using hi⟩
      set i₀ := (Finset.univ.filter fun i => ν (σ i) ≠ 0).min' hne with hi₀
      have hi₀ne : ν (σ i₀) ≠ 0 := by
        have := Finset.min'_mem _ hne; simpa [hi₀] using this
      refine ⟨i₀.val, i₀.2.le, fun i => ⟨fun h0 => ?_, fun hlt => ?_⟩⟩
      · by_contra hge
        push Not at hge
        have : i₀ ≤ i := hge
        have := hmono this
        simp only [Function.comp] at this
        omega
      · by_contra hne0
        have hmem : i ∈ Finset.univ.filter fun i => ν (σ i) ≠ 0 := by simpa using hne0
        have := Finset.min'_le _ i hmem
        have : i₀ ≤ i := this
        have : i₀.val ≤ i.val := this
        omega
    · push Not at hex
      exact ⟨n, le_rfl, fun i => ⟨fun _ => i.2, fun _ => hex i⟩⟩
  obtain ⟨b, h⟩ : ∃ b, b + a = n := ⟨n - a, by omega⟩
  subst h
  have hge : ∀ i : Fin (b + a), a ≤ i.val → ν (σ i) = 1 := fun i hi => by
    have h1 := hν (σ i)
    have h2 : ν (σ i) ≠ 0 := fun h0 => by have := (hzero i).1 h0; omega
    omega
  refine ⟨a, b, rfl, fun i => u (σ ⟨i.val, by omega⟩), fun j => u (σ ⟨a + j.val, by omega⟩),
    fun i => hu _, fun j => hu _, ?_⟩
  have hd : (fun i => π ^ ν i * u i) ∘ σ =
      cseq (fun j : Fin b => π * u (σ ⟨a + j.val, by omega⟩)) a (fun i : Fin a => u (σ ⟨i.val, by omega⟩)) := by
    funext i
    by_cases hi : i.val < a
    · rw [cseq_lt _ a _ i hi]
      simp only [Function.comp, (hzero i).2 hi, pow_zero, one_mul]
    · push Not at hi
      rw [cseq_ge _ a _ i hi]
      simp only [Function.comp, hge i hi, pow_one]
      congr 3
      ext; simp; omega
  rw [unitSum_diag, ← hd]
  exact hperm

end SortPerm

section Max

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The extension property** of a form over $\mathfrak o_\mathfrak p$: a vector $y\in F_\mathfrak p^n$ with $Q(y)$ and $Hy$ integral is integral. -/
def MaxProp (Q : QuadForm Fv n) : Prop :=
  ∀ y : Fin n → Fv, Valued.v (Q.eval y) ≤ 1 → (Q.hessian *ᵥ y) ∈ std v → y ∈ std v

theorem v_le_one_of_mem_std {y : Fin n → Fv} (hy : y ∈ std v) (i : Fin n) : Valued.v (y i) ≤ 1 := by
  have := (mem_ball v).mp hy i
  simpa using this

theorem mem_std_of_le_one {y : Fin n → Fv} (hy : ∀ i, Valued.v (y i) ≤ 1) : y ∈ std v :=
  (mem_ball v).mpr fun i => by simpa using hy i

theorem v_dotProduct_le_one {a b : Fin n → Fv} (ha : a ∈ std v) (hb : b ∈ std v) : Valued.v (a ⬝ᵥ b) ≤ 1 := by
  unfold dotProduct
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact mul_le_one' (v_le_one_of_mem_std v ha i) (v_le_one_of_mem_std v hb i)

/-- A form with coefficients in $\mathfrak o_\mathfrak p$ takes integral values on $\mathfrak o_\mathfrak p^n$. -/
theorem v_eval_le_one (Q : QuadForm 𝔬 n) {y : Fin n → Fv} (hy : y ∈ std v) :
    Valued.v ((Q.map (algebraMap 𝔬 Fv)).eval y) ≤ 1 := by
  have hy' : y = fun i => algebraMap 𝔬 Fv (toO v (y i) (v_le_one_of_mem_std v hy i)) := rfl
  rw [hy', eval_map_comp']
  exact valued_le_one_of_mem v _

theorem mulVec_mem_std (A : Matrix (Fin n) (Fin n) 𝔬) {y : Fin n → Fv} (hy : y ∈ std v) :
    (A.map (algebraMap 𝔬 Fv)) *ᵥ y ∈ std v := by
  refine mem_std_of_le_one v fun i => ?_
  simp only [mulVec, dotProduct, Matrix.map_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (valued_le_one_of_mem v _) (v_le_one_of_mem_std v hy j)

/-- **The extension property is invariant under $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalence.** -/
theorem maxProp_of_isGLEquiv {Q Q' : QuadForm 𝔬 n} (h : IsGLEquiv Q Q') (hQ : MaxProp v (Q.map (algebraMap 𝔬 Fv))) :
    MaxProp v (Q'.map (algebraMap 𝔬 Fv)) := by
  obtain ⟨U, hU, hUe⟩ := h
  have hH := DVR.hessian_eq_of_eval hUe
  set ι := algebraMap 𝔬 Fv with hι
  have hmapH : ∀ P : QuadForm 𝔬 n, (P.map ι).hessian = P.hessian.map ι := by
    intro P; ext i j; simp [QuadForm.hessian, QuadForm.map]
  have hHK : (Q'.map ι).hessian = (U.map ι)ᵀ * (Q.map ι).hessian * U.map ι := by
    rw [hmapH, hmapH, hH]
    simp [Matrix.map_mul, Matrix.transpose_map]
  have heval : ∀ x : Fin n → Fv, (Q.map ι).eval ((U.map ι) *ᵥ x) = (Q'.map ι).eval x := by
    intro x
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    rw [two_mul_eval_gen, two_mul_eval_gen, hHK, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec x (U.map ι)ᵀ, vecMul_transpose]
  have hVU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul _ hU
  have hWU : (Uᵀ)⁻¹ * Uᵀ = 1 := Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose])
  intro y h1 h2
  have hz1 : Valued.v ((Q.map ι).eval ((U.map ι) *ᵥ y)) ≤ 1 := by rw [heval]; exact h1
  have hz2 : ((Q.map ι).hessian *ᵥ ((U.map ι) *ᵥ y)) ∈ std v := by
    have e : (Q.map ι).hessian *ᵥ ((U.map ι) *ᵥ y) =
        ((Uᵀ)⁻¹).map ι *ᵥ ((Q'.map ι).hessian *ᵥ y) := by
      have hWUK : ((Uᵀ)⁻¹).map ι * (U.map ι)ᵀ = 1 := by
        rw [← Matrix.transpose_map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one ι (map_zero ι) (map_one ι)
      rw [hHK, mulVec_mulVec, mulVec_mulVec]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWUK, Matrix.one_mul]
    rw [e]; exact mulVec_mem_std v _ h2
  have hz := hQ _ hz1 hz2
  have e : y = (U⁻¹).map ι *ᵥ ((U.map ι) *ᵥ y) := by
    rw [mulVec_mulVec, ← Matrix.map_mul, hVU]; simp
  rw [e]; exact mulVec_mem_std v _ hz

section Diag

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Diagonalization at a non-dyadic prime** (Hanke 2004, Lemma 2.1, `exists_jordanForm_isGLEquiv`): a nondegenerate form over $R$ with
$\pi\nmid2$ is $\mathrm{GL}_n(R)$-equivalent to $\langle\pi^{\nu_0}u_0,\dots,\pi^{\nu_{n-1}}u_{n-1}\rangle$ with units $u_i$. -/
theorem exists_diag_pi {n : ℕ} (Q : QuadForm R n) (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    ∃ (ν : Fin n → ℕ) (u : Fin n → R), (∀ i, IsUnit (u i)) ∧
      DVR.IsGLEquiv Q (QuadForm.diag fun i => π ^ ν i * u i) := by
  have h2' : ¬ π ^ 2 ∣ 2 := fun h => h2 ((dvd_pow_self π two_ne_zero).trans h)
  obtain ⟨Q', P, ν, hJ, hP, hE⟩ := DVR.exists_jordanForm_isGLEquiv Q hQ π hπ h2'
  have hP0 := hP h2
  subst hP0
  have hpair : ∀ i, ¬ IsPaired (∅ : Finset (Fin n × Fin n)) i := fun i ⟨e, he, _⟩ => by simp at he
  choose u hu hunit using fun i => hJ.2.2.2.2.2 i (hpair i)
  refine ⟨ν, u, hunit, ?_⟩
  have hQ'a : Q' = QuadForm.diag fun i => π ^ ν i * u i := by
    ext i j
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne]; exact hJ.2.2.2.1 i j h (by simp)
    · simp [hu]
    · rw [if_neg h.ne']; exact Q'.upper (show id j < id i from h)
  rw [hQ'a] at hE
  exact hE

end Diag

/-- $Q(x+y)=Q(x)+Q(y)+x^{\mathsf T}Hy$ over a commutative ring. -/
theorem eval_add_hessian {K : Type*} [CommRing K] {m : ℕ} (Q : QuadForm K m) (x y : Fin m → K) :
    Q.eval (x + y) = Q.eval x + Q.eval y + x ⬝ᵥ (Q.hessian *ᵥ y) := by
  have h := QuadForm.polar_eq_hessian K Q x y
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  unfold QuadForm.eval
  linear_combination h

theorem eval_smul_sq {K : Type*} [CommRing K] {m : ℕ} (Q : QuadForm K m) (t : K) (y : Fin m → K) :
    Q.eval (t • y) = t ^ 2 * Q.eval y := by
  unfold QuadForm.eval QuadForm.evalIn
  simp only [Algebra.algebraMap_self, RingHom.coe_id, id, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Maximality gives the extension property for $Q_\mathfrak p$** (O'Meara 82:?, `isMaximal_loc`): $y\in F_\mathfrak p^n$ with
$Q(y)\in\mathfrak o_\mathfrak p$ and $Hy\in\mathfrak o_\mathfrak p^n$ lies in $\mathfrak o_\mathfrak p^n$, since otherwise $\mathfrak o_\mathfrak p^n+\mathfrak o_\mathfrak p y$
is a strictly larger lattice of integral norm. -/
@[kb "omeara1963" "§82H, p. 234 (maximal lattices; extension by a vector of integral norm)"]
theorem maxProp_Qp (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    MaxProp v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) := by
  intro y h1 h2
  have hM := isMaximal_loc v Q₀ hQ ⊤ top_ne_bot (stdLat F n) (by rw [span_image_top]; exact hmax)
  rw [ordIdeal_top] at hM
  obtain ⟨hlat, hnorm, hmaxK⟩ := hM
  have hloc : loc v (stdLat F n).1 = std v := loc_intVec v
  rw [hloc] at hlat hnorm hmaxK
  have hqf : (NF.Qp v Q₀).map (algebraMap 𝔬 Fv) = Qf v Q₀ := Tamagawa.map_Qp_eq v Q₀
  rw [hqf] at h1 h2
  have hHes : (Qf v Q₀).hessian = hessV v Q₀ := hessian_Qf v Q₀
  rw [hHes] at h2
  set K : Submodule 𝔬 (Fin n → Fv) := std v ⊔ Submodule.span 𝔬 {y} with hK
  haveI := hlat
  have hKlat : K.IsLattice Fv :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg Fv (le_sup_left : std v ≤ K)
      (Submodule.IsLattice.fg.sup (Submodule.fg_span_singleton y))
  have hKn : OMeara.normIdeal (qv v Q₀) K ≤ pPow v 0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ℓ, hℓ, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    show _ ∈ pPow v 0
    rw [mem_pPow_iff]
    have hq : ∀ x, qv v Q₀ x = (Qf v Q₀).eval x := qv_apply v Q₀
    have hts : t • y = (t : Fv) • y := rfl
    have hEl : Valued.v ((Qf v Q₀).eval ℓ) ≤ 1 := by
      rw [← hqf]; exact v_eval_le_one v _ hℓ
    have ht1 : Valued.v (t : Fv) ≤ 1 := valued_le_one_of_mem v t
    rw [hq, eval_add_hessian, hts, eval_smul_sq, hHes, mulVec_smul, dotProduct_smul]
    have hc : Valued.v (ℓ ⬝ᵥ (hessV v Q₀ *ᵥ y)) ≤ 1 := v_dotProduct_le_one v hℓ h2
    have e1 : Valued.v ((t : Fv) ^ 2 * (Qf v Q₀).eval y) ≤ 1 := by
      rw [map_mul, map_pow]; exact mul_le_one' (pow_le_one' ht1 2) h1
    have e2 : Valued.v ((t : Fv) • (ℓ ⬝ᵥ (hessV v Q₀ *ᵥ y))) ≤ 1 := by
      rw [smul_eq_mul, map_mul]; exact mul_le_one' ht1 hc
    simp only [Int.reduceNeg, WithZero.exp_zero, neg_zero] at *
    exact (Valuation.map_add_le _ (Valuation.map_add_le _ hEl e1) e2)
  have hEq := hmaxK K hKlat le_sup_left hKn
  have : y ∈ K := Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  rw [hEq] at this
  exact this

theorem hessian_diag_gen {K : Type*} [CommRing K] {m : ℕ} (a : Fin m → K) :
    (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  ext i j
  by_cases h : i = j
  · subst h; simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_apply]; ring
  · simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_apply, h, Ne.symm h]

theorem aux_sq {K : Type*} [Field K] (p x : K) (hp : p ≠ 0) (k : ℕ) :
    p ^ (k + 2) * x * p⁻¹ ^ 2 = p ^ k * x := by
  field_simp
  ring

theorem aux_lin {K : Type*} [Field K] (p x : K) (hp : p ≠ 0) (k : ℕ) :
    2 * (p ^ (k + 2) * x) * p⁻¹ = 2 * (p ^ (k + 1) * x) := by
  field_simp
  ring

/-- **Maximality bounds the exponents:** if $\langle\pi^{\nu_i}u_i\rangle$ has the extension property then every $\nu_i\le1$ (else
$y=\pi^{-1}e_i$ has $Q(y)=\pi^{\nu_i-2}u_i$ and $Hy=2\pi^{\nu_i-1}u_ie_i$ integral but $y\notin\mathfrak o_\mathfrak p^n$). -/
theorem nu_le_one (ν : Fin n → ℕ) (u : Fin n → 𝔬)
    (h : MaxProp v ((QuadForm.diag fun i => NF.π v ^ ν i * u i).map (algebraMap 𝔬 Fv))) : ∀ i, ν i ≤ 1 := by
  intro i
  by_contra hi
  push Not at hi
  obtain ⟨π', hπ'⟩ : ∃ π' : Fv, π' = algebraMap 𝔬 Fv (NF.π v) := ⟨_, rfl⟩
  have hπ0 : π' ≠ 0 := by
    rw [hπ']; exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr (NF.irreducible_π v).ne_zero
  have hvπ : Valued.v π' = WithZero.exp (-1 : ℤ) := by rw [hπ']; exact NF.valued_π v
  obtain ⟨k, hk⟩ : ∃ k, ν i = k + 2 := ⟨ν i - 2, by omega⟩
  set y : Fin n → Fv := Pi.single i π'⁻¹ with hy
  rw [DVR.map_diag] at h
  have hey : (QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v ^ ν j * u j)).eval y =
      algebraMap 𝔬 Fv (NF.π v ^ k * u i) := by
    rw [Siegel.Kneser.eval_diag]
    rw [Finset.sum_eq_single i]
    · simp only [hy, Pi.single_eq_same, hk]
      simp only [map_mul, map_pow, ← hπ']
      exact aux_sq π' _ hπ0 k
    · intro j _ hj; simp [hy, Pi.single_apply, hj]
    · simp
  have hHy : (QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v ^ ν j * u j)).hessian *ᵥ y =
      Pi.single i (algebraMap 𝔬 Fv (2 * (NF.π v ^ (k + 1) * u i))) := by
    rw [hessian_diag_gen]
    funext j
    rw [mulVec_diagonal]
    by_cases hj : j = i
    · subst hj
      simp only [hy, Pi.single_eq_same, hk]
      simp only [map_mul, map_pow, map_ofNat, ← hπ']
      exact aux_lin π' _ hπ0 k
    · simp [hy, Pi.single_apply, hj]
  have h1 : Valued.v ((QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v ^ ν j * u j)).eval y) ≤ 1 := by
    rw [hey]; exact valued_le_one_of_mem v (NF.π v ^ k * u i)
  have h2 : ((QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v ^ ν j * u j)).hessian *ᵥ y) ∈ std v := by
    rw [hHy]
    refine mem_std_of_le_one v fun j => ?_
    by_cases hj : j = i
    · subst hj; simp only [Pi.single_eq_same]; exact valued_le_one_of_mem v (2 * (NF.π v ^ (k + 1) * u j))
    · simp [hj]
  have := v_le_one_of_mem_std v (h y h1 h2) i
  rw [hy, Pi.single_eq_same, map_inv₀, hvπ] at this
  have h3 : (1 : WithZero (Multiplicative ℤ)) < (WithZero.exp (-1 : ℤ))⁻¹ := by
    rw [← WithZero.exp_neg]
    have : (WithZero.exp (1 : ℤ)) > WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by norm_num)
    simpa using this
  exact absurd this (not_le.mpr h3)

/-- **Peeling off a coordinate:** the extension property of $\langle c\rangle\perp Q'$ gives that of $Q'$. -/
theorem maxProp_of_splitForm {m : ℕ} (c : 𝔬) (Q' : QuadForm 𝔬 m)
    (h : MaxProp v ((splitForm c Q').map (algebraMap 𝔬 Fv))) : MaxProp v (Q'.map (algebraMap 𝔬 Fv)) := by
  rw [map_splitForm] at h
  intro y' h1 h2
  have h1' : Valued.v ((splitForm (algebraMap 𝔬 Fv c) (Q'.map (algebraMap 𝔬 Fv))).eval
      (Fin.cons 0 y' : Fin (m + 1) → Fv)) ≤ 1 := by
    unfold QuadForm.eval
    rw [evalIn_splitForm]
    simpa using h1
  have h2' : ((splitForm (algebraMap 𝔬 Fv c) (Q'.map (algebraMap 𝔬 Fv))).hessian *ᵥ
      (Fin.cons 0 y' : Fin (m + 1) → Fv)) ∈ std v := by
    rw [hessian_splitForm, cornerMat_mulVec]
    refine mem_std_of_le_one v fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using v_le_one_of_mem_std v h2 j
  have := h _ h1' h2'
  exact mem_std_of_le_one v fun i => by simpa using v_le_one_of_mem_std v this i.succ

/-- **Peeling off all unit coordinates:** the extension property of $\langle u\rangle\perp T$ gives that of $T$. -/
theorem maxProp_of_unitSum {b : ℕ} (T : QuadForm 𝔬 b) :
    ∀ (a : ℕ) (u : Fin a → 𝔬), MaxProp v ((unitSum T a u).map (algebraMap 𝔬 Fv)) →
      MaxProp v (T.map (algebraMap 𝔬 Fv))
  | 0, u, h => h
  | a + 1, u, h =>
    maxProp_of_unitSum T a (Fin.tail u) (maxProp_of_splitForm v (u 0) _ h)

/-- **The residue form of the $\pi$-modular part is anisotropic:** if $\langle\pi w_0,\dots,\pi w_{b-1}\rangle$ has the extension property, then
$\sum_jw_jx_j^2\equiv0\bmod\pi$ with $x_j\in\mathfrak o_\mathfrak p$ forces every $x_j\equiv0\bmod\pi$ (else $y=\pi^{-1}x$ has
$Q(y)=\pi^{-1}\sum w_jx_j^2$ and $Hy=2(w_jx_j)_j$ integral, but $y\notin\mathfrak o_\mathfrak p^b$). -/
theorem aniso_of_maxProp {b : ℕ} (w : Fin b → 𝔬)
    (h : MaxProp v ((QuadForm.diag fun j => NF.π v * w j).map (algebraMap 𝔬 Fv))) (x : Fin b → 𝔬)
    (hdiv : NF.π v ∣ ∑ j, w j * x j ^ 2) : ∀ j, NF.π v ∣ x j := by
  rw [DVR.map_diag] at h
  obtain ⟨s, hs⟩ := hdiv
  obtain ⟨π', hπ'⟩ : ∃ π' : Fv, π' = algebraMap 𝔬 Fv (NF.π v) := ⟨_, rfl⟩
  have hπ0 : π' ≠ 0 := by
    rw [hπ']; exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr (NF.irreducible_π v).ne_zero
  set y : Fin b → Fv := fun j => π'⁻¹ * algebraMap 𝔬 Fv (x j) with hy
  have hey : (QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v * w j)).eval y = algebraMap 𝔬 Fv s := by
    rw [Siegel.Kneser.eval_diag]
    have hsum : ∑ j, algebraMap 𝔬 Fv (NF.π v * w j) * y j ^ 2 =
        π'⁻¹ * algebraMap 𝔬 Fv (∑ j, w j * x j ^ 2) := by
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hy, map_mul, map_pow, ← hπ']
      field_simp
    rw [hsum, hs, map_mul, ← hπ']
    field_simp
  have hHy : (QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v * w j)).hessian *ᵥ y =
      fun j => algebraMap 𝔬 Fv (2 * (w j * x j)) := by
    rw [hessian_diag_gen]
    funext j
    rw [mulVec_diagonal]
    simp only [hy, map_mul, map_ofNat, ← hπ']
    field_simp
  have h1 : Valued.v ((QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v * w j)).eval y) ≤ 1 := by
    rw [hey]; exact valued_le_one_of_mem v s
  have h2 : ((QuadForm.diag fun j => algebraMap 𝔬 Fv (NF.π v * w j)).hessian *ᵥ y) ∈ std v := by
    rw [hHy]
    exact mem_std_of_le_one v fun j => valued_le_one_of_mem v (2 * (w j * x j))
  intro j
  have hj := v_le_one_of_mem_std v (h y h1 h2) j
  simp only [hy] at hj
  refine ⟨toO v _ hj, ?_⟩
  apply (IsFractionRing.injective 𝔬 Fv)
  change algebraMap 𝔬 Fv (x j) = algebraMap 𝔬 Fv (NF.π v * toO v _ hj)
  rw [map_mul, ← hπ']
  change _ = π' * (π'⁻¹ * algebraMap 𝔬 Fv (x j))
  field_simp

/-- **The residue form has at most two variables:** an anisotropic diagonal form $\langle\bar w_j\rangle$ over the finite residue field has
$b\le2$ (Chevalley–Warning). -/
theorem rank_le_two {b : ℕ} (w : Fin b → 𝔬) (A : ∀ x : Fin b → 𝔬, NF.π v ∣ ∑ j, w j * x j ^ 2 → ∀ j, NF.π v ∣ x j) :
    b ≤ 2 := by
  by_contra hb
  push Not at hb
  have hπ := NF.irreducible_π v
  obtain ⟨z, hz0, hz⟩ := Siegel.Kneser.exists_isotropic_of_three_le (K := IsLocalRing.ResidueField 𝔬) (n := b) hb
    (QuadForm.diag fun j => IsLocalRing.residue 𝔬 (w j))
  choose x hx using fun j => IsLocalRing.residue_surjective (z j)
  rw [Siegel.Kneser.eval_diag] at hz
  have hsum : IsLocalRing.residue 𝔬 (∑ j, w j * x j ^ 2) = 0 := by
    rw [map_sum]
    simpa [hx] using hz
  have hd := (DVR.residue_eq_zero_iff_dvd hπ _).1 hsum
  apply hz0
  funext j
  have := (DVR.residue_eq_zero_iff_dvd hπ _).2 (A x hd j)
  simpa [hx] using this

/-- **A binary anisotropic residue form has $\chi(-\det)=-1$.** -/
theorem chiDisc_diag_two (h2 : IsUnit (2 : 𝔬)) (w : Fin 2 → 𝔬) (hw : ∀ j, IsUnit (w j))
    (A : ∀ x : Fin 2 → 𝔬, NF.π v ∣ ∑ j, w j * x j ^ 2 → ∀ j, NF.π v ∣ x j) :
    chiDisc (QuadForm.diag w) = -1 := by
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have hdet : ¬ NF.π v ∣ (QuadForm.diag w).hessian.det := by
    rw [det_hessian_diag]
    exact DVR.dvr_not_dvd_of_isUnit hπ ((h2.pow 2).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hw i)))
  rcases chiDisc_pm hπ hπ2 _ hdet with h1 | h1
  swap
  · exact h1
  exfalso
  have h2F : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have := DVR.res_ne_zero hπ hπ2
    rwa [map_ofNat] at this
  have hr0 : IsLocalRing.residue 𝔬 (w 0) ≠ 0 := DVR.res_ne_zero hπ (DVR.dvr_not_dvd_of_isUnit hπ (hw 0))
  have hr1 : IsLocalRing.residue 𝔬 (w 1) ≠ 0 := DVR.res_ne_zero hπ (DVR.dvr_not_dvd_of_isUnit hπ (hw 1))
  have hc : (-1 : IsLocalRing.ResidueField 𝔬) ^ (2 / 2) * resGramDet (QuadForm.diag w) =
      -(IsLocalRing.residue 𝔬 (w 0) * IsLocalRing.residue 𝔬 (w 1)) := by
    unfold resGramDet
    rw [det_hessian_diag, map_mul, map_pow, map_ofNat, Fin.prod_univ_two, map_mul]
    field_simp
    norm_num
  unfold chiDisc at h1
  rw [hc] at h1
  obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare (neg_ne_zero.2 (mul_ne_zero hr0 hr1))).1 h1
  obtain ⟨x0, hx0⟩ := IsLocalRing.residue_surjective s
  have hsum : IsLocalRing.residue 𝔬 (∑ j, w j * (![x0, w 0] : Fin 2 → 𝔬) j ^ 2) = 0 := by
    simp only [Fin.sum_univ_two, map_add, map_mul, map_pow, Matrix.cons_val_zero, Matrix.cons_val_one, hx0]
    linear_combination (-(IsLocalRing.residue 𝔬 (w 0))) * hs
  have hd := (DVR.residue_eq_zero_iff_dvd hπ _).1 hsum
  have := A _ hd 1
  exact (DVR.dvr_not_dvd_of_isUnit hπ (hw 0)) (by simpa using this)

end Max

variable (F) in
/-- **The Jordan shape of a maximal lattice at an odd place** (O'Meara 91:2, §92; proved): `OddMaximalJordan F` holds. -/
@[kb "omeara1963" "91:2, §92 (Jordan shape U ⊥ πW of a maximal lattice at an odd place; proved from isMaximal_loc)"]
theorem oddMaximalJordan : OddMaximalJordan F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v h2 h1 => ?_⟩
  have hπ := NF.irreducible_π v
  have hπ2 := DensitySD.not_dvd_two v h2
  have hQp := NF.nondegenerate_Qp v hQ
  have MP0 := maxProp_Qp v Q₀ hQ hmax
  obtain ⟨ν, u, hu, hE⟩ := exists_diag_pi (NF.Qp v Q₀) hQp hπ hπ2
  have MP1 := maxProp_of_isGLEquiv v hE MP0
  have hν := nu_le_one v ν u MP1
  obtain ⟨a, b, h, u', w, hu', hw, hE2⟩ := exists_shape_of_nu (NF.π v) ν hν u hu
  have hEq := hE.trans hE2
  subst h
  have MP2 := maxProp_of_isGLEquiv v hEq MP0
  have MP3 := maxProp_of_unitSum v (QuadForm.diag fun j => NF.π v * w j) a u' MP2
  have A := aniso_of_maxProp v w MP3
  have hb2 := rank_le_two v w A
  have hWdet : IsUnit (QuadForm.diag w).hessian.det := by
    rw [DVR.det_hessian_diag]
    exact (h2.pow b).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hw i))
  have hT : ∀ i j, (QuadForm.diag fun j => NF.π v * w j).coeff i j = NF.π v * (QuadForm.diag w).coeff i j := by
    intro i j
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hb1 : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    obtain ⟨w0, hw0, hD⟩ := det_shape v h2 u' hu' (QuadForm.diag w) (QuadForm.diag fun j => NF.π v * w j)
      hWdet hT (NF.Qp v Q₀) hEq
    rw [show NF.π v ^ b = 1 by rw [hb0', pow_zero], one_mul] at hD
    apply h1
    unfold dualIndexAt
    rw [hD, norm_coe_unit v hw0, inv_one]
  refine ⟨a, b, rfl, u', QuadForm.diag w, QuadForm.diag fun j => NF.π v * w j, hu', hWdet, hT, by omega,
    fun hb => ?_, ⟨w, rfl, rfl⟩, hEq⟩
  subst hb
  exact chiDisc_diag_two v h2 w hw A


/-- **(3.3) at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, from the Witt type alone:** the Jordan shape is
proved (`oddMaximalJordan`), so `ShimuraDensityOddRamified F` follows from `OddWittType F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p; from the Witt type)"]
theorem shimuraDensityOddRamified_of_wittType (I : OddWittType F) : ShimuraDensityOddRamified F :=
  shimuraDensityOddRamified_of_shape (oddMaximalShape_of_split (oddMaximalJordan F) I)

end QuadFormsKB.Hanke2005
