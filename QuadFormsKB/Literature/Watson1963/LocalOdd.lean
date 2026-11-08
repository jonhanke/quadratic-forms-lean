/-
# Watson (1963), §2: a Watson-minimal form is $p$-adically square-free at an odd prime

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §2, proof of
Theorem 2, p. 551, and Watson 1962, Theorems 3, 4. If $f$ is a Watson-minimal positive definite integral form and
$p$ is an odd prime, then over $\mathbb Z_p$
$$ f \cong \langle u_0, \dots, u_{r-1}, p\,u_r, \dots, p\,u_{n-1}\rangle, \qquad r = r_p(f),\ u_i \in \mathbb Z_p^\times.$$
*Proof outline.* Diagonalize $f \cong \langle p^{\nu_i} u_i\rangle$ over $\mathbb Z_p$ (Jordan decomposition, $p$ odd).
Let $g$ be derived from $f$ at $p$ (basis matrix $B$ of $\Lambda_p$) and $h$ derived from $g$ at $p$. Both steps
multiply $|\det H|$ by $p^{2 r_p - n}$ (`det_sq_mul_det_hessian`), so minimality gives $n \le r_p(f) + r_p(g)$. Locally
$r_p(f) = \#\{\nu_i = 0\}$ and $r_p(g) \le \#\{\nu_i = 1\}$ (the lattice $B\mathbb Z_p^n$ is
$\{y : y_i \in p\mathbb Z_p \text{ if } \nu_i = 0\}$ in the diagonal basis), so no $\nu_i \ge 2$ occurs.
-/
import QuadFormsKB.Literature.Watson1963.Primitive
import QuadFormsKB.LocalDensity.DVRUnimodular

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

variable {n : ℕ} (p : ℕ) [Fact p.Prime]

/-! ### Elementary facts on $\mathbb Z_p \to \mathbb F_p$ -/

/-- An element of $\mathbb Z_p$ reduces to $0$ in $\mathbb F_p$ iff it is divisible by $p$. -/
theorem toZMod_eq_zero_iff_dvd (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

theorem toZMod_natCast_self : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
  rw [toZMod_eq_zero_iff_dvd]

theorem toZMod_ne_zero_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) : PadicInt.toZMod x ≠ 0 :=
  (hx.map PadicInt.toZMod).ne_zero

theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-! ### Diagonal forms over $\mathbb F_p$ -/

/-- **Rank bound for a form that is diagonal over $\mathbb F_p$:** if $\bar F(T\vec y) = \sum_i e_i y_i^2$ over
$\mathbb F_p$ for an invertible $T$ (`T * T' = 1`), then $r_p(F) \le \#\{i : e_i \ne 0\}$. *Proof:* the vectors
$T\vec y$ with $y_i = 0$ whenever $e_i \ne 0$ lie in the radical $R_p(F)$. -/
theorem rankModP_le_card_of_diag (F : QuadForm ℤ n) (T T' : Matrix (Fin n) (Fin n) (ZMod p)) (hTT : T * T' = 1)
    (e : Fin n → ZMod p) (h : ∀ y, F.evalIn (ZMod p) (T *ᵥ y) = ∑ i, e i * y i ^ 2) :
    rankModP p F ≤ (Finset.univ.filter fun i => e i ≠ 0).card := by
  classical
  have hTT' : T' * T = 1 := mul_eq_one_comm.mp hTT
  let S := {i // e i = 0}
  let ι : (S → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
    { toFun := fun y i => if h : e i = 0 then y ⟨i, h⟩ else 0
      map_add' := by
        intro y z; funext i; by_cases hi : e i = 0 <;> simp [hi]
      map_smul' := by
        intro c y; funext i; by_cases hi : e i = 0 <;> simp [hi] }
  have hι : ∀ y i, e i ≠ 0 → ι y i = 0 := fun y i hi => by simp [ι, hi]
  have hιinj : Function.Injective ι := by
    intro y z hyz
    funext ⟨i, hi⟩
    have := congrFun hyz i
    simpa [ι, hi] using this
  let L : (S → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) := T.mulVecLin ∘ₗ ι
  have hLinj : Function.Injective L := by
    intro y z hyz
    apply hιinj
    have := congrArg (fun v => T' *ᵥ v) hyz
    simpa [L, mulVec_mulVec, hTT'] using this
  have hrange : LinearMap.range L ≤ radModP p F := by
    rintro _ ⟨y, rfl⟩
    rw [mem_radModP_iff]
    intro z
    have hz : z = T *ᵥ (T' *ᵥ z) := by rw [mulVec_mulVec, hTT, one_mulVec]
    set w := T' *ᵥ z
    have hLy : L y = T *ᵥ (ι y) := rfl
    rw [hLy, hz, ← mulVec_add, h, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : e i = 0
    · simp [hi]
    · simp [hι y i hi]
  have h1 : Module.finrank (ZMod p) (S → ZMod p) ≤ Module.finrank (ZMod p) (radModP p F) := by
    rw [← LinearMap.finrank_range_of_inj hLinj]
    exact Submodule.finrank_mono hrange
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Fintype.card S = (Finset.univ.filter fun i => e i = 0).card := by
    rw [Fintype.card_subtype]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => e i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  have h4 := rankModP_add_finrank p F
  have h5 : (Finset.univ.filter fun i => ¬ e i = 0) = (Finset.univ.filter fun i => e i ≠ 0) := rfl
  rw [h5] at h3
  omega

/-- **Support of a radical vector:** with $p$ odd, if $\bar F(T\vec y) = \sum_i e_i y_i^2$ and $\vec x \in R_p(F)$, then
$(T^{-1}\vec x)_j = 0$ for every $j$ with $e_j \ne 0$. -/
theorem rad_support_of_diag (hp : p ≠ 2) (F : QuadForm ℤ n) (T T' : Matrix (Fin n) (Fin n) (ZMod p))
    (hTT : T * T' = 1) (e : Fin n → ZMod p)
    (h : ∀ y, F.evalIn (ZMod p) (T *ᵥ y) = ∑ i, e i * y i ^ 2) {x : Fin n → ZMod p}
    (hx : x ∈ radModP p F) (j : Fin n) (hj : e j ≠ 0) : (T' *ᵥ x) j = 0 := by
  classical
  rw [mem_radModP_iff] at hx
  set a := T' *ᵥ x with ha
  have hxa : x = T *ᵥ a := by rw [ha, mulVec_mulVec, hTT, one_mulVec]
  have key : ∀ w : Fin n → ZMod p, ∑ i, e i * (a i + w i) ^ 2 = ∑ i, e i * w i ^ 2 := by
    intro w
    have := hx (T *ᵥ w)
    rw [hxa, ← mulVec_add, h, h] at this
    exact this
  have k0 := key 0
  have k1 := key (Pi.single j 1)
  simp only [Pi.zero_apply, add_zero, zero_pow two_ne_zero, mul_zero, Finset.sum_const_zero] at k0
  have e1 : ∑ i, e i * (a i + (Pi.single j (1 : ZMod p) : Fin n → ZMod p) i) ^ 2 =
      ∑ i, e i * a i ^ 2 + 2 * (e j * a j) + e j := by
    have : ∀ i, e i * (a i + (Pi.single j (1 : ZMod p) : Fin n → ZMod p) i) ^ 2 =
        e i * a i ^ 2 + (if i = j then 2 * (e j * a j) + e j else 0) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
    simp [add_assoc]
  have e2 : ∑ i, e i * ((Pi.single j (1 : ZMod p) : Fin n → ZMod p) i) ^ 2 = e j := by
    have : ∀ i, e i * ((Pi.single j (1 : ZMod p) : Fin n → ZMod p) i) ^ 2 = if i = j then e j else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp
  rw [e1, e2, k0] at k1
  have h2 : (2 : ZMod p) * (e j * a j) = 0 := by linear_combination k1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (two_ne_zero_zmod p hp)
  · exact (mul_eq_zero.mp h).resolve_left hj

/-! ### From $\mathbb Z_p$ to $\mathbb F_p$, and the derived form over $\mathbb Z_p$ -/

/-- **A diagonalization over $\mathbb Z_p$ reduces to one over $\mathbb F_p$.** -/
theorem toZMod_diag (F : QuadForm ℤ n) (T : Matrix (Fin n) (Fin n) ℤ_[p]) (e : Fin n → ℤ_[p])
    (h : ∀ y, F.evalIn ℤ_[p] (T *ᵥ y) = ∑ i, e i * y i ^ 2) (y : Fin n → ZMod p) :
    F.evalIn (ZMod p) ((T.map PadicInt.toZMod) *ᵥ y) = ∑ i, PadicInt.toZMod (e i) * y i ^ 2 := by
  obtain ⟨y', hy'⟩ : ∃ y' : Fin n → ℤ_[p], ∀ i, PadicInt.toZMod (y' i) = y i := by
    choose y' hy' using fun i => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (y i)
    exact ⟨y', hy'⟩
  have e1 := map_evalIn_hom (PadicInt.toZMod (p := p)) F (T *ᵥ y')
  rw [h] at e1
  have hv : (fun i => PadicInt.toZMod ((T *ᵥ y') i)) = (T.map PadicInt.toZMod) *ᵥ y := by
    funext i
    simp [mulVec, dotProduct, map_sum, hy']
  rw [hv] at e1
  rw [← e1]
  simp [map_sum, hy']

/-- **Helper:** $2 Q(\vec x) = \vec x^{\mathsf T} H \vec x$ over any commutative ring. -/
theorem two_mul_evalIn' {S : Type*} [CommRing S] (Q : QuadForm ℤ n) (x : Fin n → S) :
    2 * Q.evalIn S x = x ⬝ᵥ (Q.hessian.map (algebraMap ℤ S) *ᵥ x) := by
  rw [QuadForm.hessian, Matrix.map_add _ (map_add _), Matrix.add_mulVec, dotProduct_add, Matrix.transpose_map,
    mulVec_transpose, dotProduct_comm x (x ᵥ* _), ← dotProduct_mulVec, QuadForm.evalIn_eq_dotProduct]
  ring

/-- **The identity $Q(B\vec x) = c\,Q'(\vec x)$ holds over $\mathbb Z_p$:** if it holds on $\mathbb Z^n$ then it holds
for all $\vec y \in \mathbb Z_p^n$ (with $B$ mapped into $\mathbb Z_p$). *Proof:* it is equivalent to
$B^{\mathsf T} H_Q B = c\,H_{Q'}$, and $2Q(\vec x) = \vec x^{\mathsf T} H \vec x$; cancel $2 \ne 0$. -/
theorem evalIn_map_mulVec_of_eval (Q Q' : QuadForm ℤ n) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℤ)
    (hQ : ∀ x, Q.eval (B *ᵥ x) = c * Q'.eval x) (y : Fin n → ℤ_[p]) :
    Q.evalIn ℤ_[p] ((B.map (algebraMap ℤ ℤ_[p])) *ᵥ y) = (c : ℤ_[p]) * Q'.evalIn ℤ_[p] y := by
  have h1 : ∀ x, Q.eval (B *ᵥ x) = (c • Q').eval x := fun x => by rw [hQ, Kneser.eval_smul_form]
  have h2 := (eval_mulVec_eq_iff_hessian Q (c • Q') B).1 h1
  rw [hessian_smul] at h2
  have h3 := congrArg (fun M => M.map (algebraMap ℤ ℤ_[p])) h2
  simp only [Matrix.map_mul, Matrix.transpose_map] at h3
  have h4 : ((c • Q'.hessian).map (algebraMap ℤ ℤ_[p])) = (c : ℤ_[p]) • Q'.hessian.map (algebraMap ℤ ℤ_[p]) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul,
      map_mul]
    simp
  rw [h4] at h3
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[p]) ≠ 0)
  rw [two_mul_evalIn', mul_left_comm, two_mul_evalIn']
  set Bp := B.map (algebraMap ℤ ℤ_[p])
  have h5 : (Bp *ᵥ y) ⬝ᵥ (Q.hessian.map (algebraMap ℤ ℤ_[p]) *ᵥ (Bp *ᵥ y)) =
      y ⬝ᵥ ((Bpᵀ * Q.hessian.map (algebraMap ℤ ℤ_[p]) * Bp) *ᵥ y) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm y, ← dotProduct_mulVec,
      dotProduct_comm]
  rw [h5, h3, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Existence of the derived form with the index of $\Lambda_p$ as determinant:** for every integral form $Q$ and
prime $p$ there are a basis matrix $B$ of $\Lambda_p(Q)$ (`watsonSub`) with $|\det B| = p^{r_p(Q)}$
(`index_watsonSub`) and an integral form $R$ with $Q(B\vec x) = p\,R(\vec x)$; so $R$ is derived from $Q$ at $p$
(`IsWatsonDerived`). (The construction of `IsWatsonMinimal.le_two_mul_rankModP`.) -/
theorem exists_derived_form (Q : QuadForm ℤ n) :
    ∃ (B : Matrix (Fin n) (Fin n) ℤ) (R : QuadForm ℤ n), B.det.natAbs = p ^ rankModP p Q ∧
      Set.range B.mulVec = (watsonSub Q (p : ℤ) : Set (Fin n → ℤ)) ∧
      ∀ x, Q.eval (B *ᵥ x) = (p : ℤ) * R.eval x := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set K := watsonSub Q (p : ℤ) with hK
  obtain ⟨B, hB⟩ := wm_exists_matrix_of_submodule hp0 K (smul_mem_watsonSub Q (p : ℤ))
  obtain ⟨X, hBX⟩ := wm_exists_mul_eq (M := B) (N := (p : ℤ) • 1) fun j => by
    rw [smul_mulVec, one_mulVec]; exact (hB _).mp (smul_mem_watsonSub Q (p : ℤ) _)
  have hdetB : B.det ≠ 0 := (wm_det_ne_zero_of_mul_eq hBX hp0).1
  have hrange : Set.range B.mulVec = (K : Set (Fin n → ℤ)) := by
    ext z; exact ((hB z).symm)
  have hinj : Function.Injective (B.mulVecLin) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hdetB hx
  let f : (Fin n → ℤ) →+ K := (B.mulVecLin.toAddMonoidHom).codRestrict K.toAddSubgroup (fun x => (hB _).mpr ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := (hB z).mp hz
      exact ⟨x, Subtype.ext hx⟩
  let e : (Fin n → ℤ) ≃+ K := AddEquiv.ofBijective f hf
  have hdet := Submodule.natAbs_det_equiv K e
  have hlin : K.subtype ∘ₗ AddMonoidHom.toIntLinearMap ((e : (Fin n → ℤ) ≃+ K) : (Fin n → ℤ) →+ K) =
      Matrix.toLin' B := by
    ext x : 1
    rfl
  rw [hlin, LinearMap.det_toLin'] at hdet
  have hidx : Nat.card ((Fin n → ℤ) ⧸ K) = p ^ rankModP p Q := by
    rw [← index_watsonSub p Q]; rfl
  rw [hidx] at hdet
  have hdvd : ∀ v, (p : ℤ) ∣ (Q.compMat B).eval v := fun v => by
    rw [QuadForm.eval_compMat]
    exact dvd_eval_of_mem_watsonSub ((hB _).mpr ⟨v, rfl⟩)
  obtain ⟨R, hR⟩ := wm_exists_eq_smul_of_dvd hp0 hdvd
  have hg : ∀ x, Q.eval (B *ᵥ x) = (p : ℤ) * R.eval x := fun x => by
    rw [← QuadForm.eval_compMat, hR, Kneser.eval_smul_form]
  exact ⟨B, R, hdet, hrange, hg⟩

/-! ### The local computation -/

/-- $p^k u$ with $u$ a unit reduces to a non-zero element of $\mathbb F_p$ iff $k = 0$. -/
theorem toZMod_pow_mul_ne_zero {k : ℕ} {u : ℤ_[p]} (hu : IsUnit u) :
    PadicInt.toZMod ((p : ℤ_[p]) ^ k * u) ≠ 0 ↔ k = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [toZMod_ne_zero_of_isUnit p hu]
  · have : PadicInt.toZMod ((p : ℤ_[p]) ^ k * u) = 0 := by
      rw [map_mul, map_pow, toZMod_natCast_self, zero_pow hk.ne', zero_mul]
    simp [this, hk.ne']

/-- **The local computation** (Watson 1963, §2, p. 551; $p$ odd). Let $f \cong \langle p^{\nu_i} u_i\rangle$ over
$\mathbb Z_p$ ($u_i$ units; `T`, `T'` mutually inverse), and let $g$ be derived from $f$ at $p$ with basis matrix $B$
of $\Lambda_p(f)$ of determinant $\pm p^{r_p(f)}$. Then $r_p(f) = \#\{\nu_i = 0\}$ and
$r_p(g) \le \#\{\nu_i = 1\}$. *Proof:* in the diagonal basis $B\mathbb Z_p^n = D W \mathbb Z_p^n$ with
$D = \mathrm{diag}(p \text{ if } \nu_i = 0, \text{ else } 1)$ (a vector of $\Lambda_p$ has $p \mid y_i$ where $\nu_i = 0$,
`rad_support_of_diag`) and $W \in \mathrm{GL}_n(\mathbb Z_p)$ by comparing determinants with
$r_p(f) \le \#\{\nu_i = 0\}$ (`rankModP_le_card_of_diag`); then $g \cong \langle p^{\varepsilon_i} u_i\rangle$ with
$\varepsilon_i = 1$ if $\nu_i = 0$ and $\nu_i - 1$ otherwise. -/
theorem local_analysis (hp : p ≠ 2) (f g : QuadForm ℤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hdetB : B.det.natAbs = p ^ rankModP p f)
    (hrange : Set.range B.mulVec = (watsonSub f (p : ℤ) : Set (Fin n → ℤ)))
    (hg : ∀ x, f.eval (B *ᵥ x) = (p : ℤ) * g.eval x)
    (T T' : Matrix (Fin n) (Fin n) ℤ_[p]) (hTT : T * T' = 1) (ν : Fin n → ℕ) (u : Fin n → ℤ_[p])
    (hu : ∀ i, IsUnit (u i))
    (hT : ∀ y, f.evalIn ℤ_[p] (T *ᵥ y) = ∑ i, ((p : ℤ_[p]) ^ ν i * u i) * y i ^ 2) :
    rankModP p f = (Finset.univ.filter fun i => ν i = 0).card ∧
      rankModP p g ≤ (Finset.univ.filter fun i => ν i = 1).card := by
  classical
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hTT' : T' * T = 1 := mul_eq_one_comm.mp hTT
  set Bp : Matrix (Fin n) (Fin n) ℤ_[p] := B.map (algebraMap ℤ ℤ_[p]) with hBp
  -- reduction mod p
  have hred : ∀ (X Y : Matrix (Fin n) (Fin n) ℤ_[p]), X * Y = 1 →
      X.map PadicInt.toZMod * Y.map PadicInt.toZMod = 1 := by
    intro X Y h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hT1 := toZMod_diag p f T (fun i => (p : ℤ_[p]) ^ ν i * u i) hT
  have he0 : ∀ i, PadicInt.toZMod ((p : ℤ_[p]) ^ ν i * u i) ≠ 0 ↔ ν i = 0 := fun i =>
    toZMod_pow_mul_ne_zero p (hu i)
  have hfilt : (Finset.univ.filter fun i => PadicInt.toZMod ((p : ℤ_[p]) ^ ν i * u i) ≠ 0) =
      Finset.univ.filter fun i => ν i = 0 := Finset.filter_congr fun i _ => he0 i
  have hrf : rankModP p f ≤ (Finset.univ.filter fun i => ν i = 0).card := by
    have := rankModP_le_card_of_diag p f _ _ (hred T T' hTT) _ hT1
    rwa [hfilt] at this
  -- the columns of B
  set M : Matrix (Fin n) (Fin n) ℤ_[p] := T' * Bp with hM
  have hMdvd : ∀ j k, ν j = 0 → (p : ℤ_[p]) ∣ M j k := by
    intro j k hj
    have hmem : (fun l => B l k) ∈ watsonSub f (p : ℤ) := by
      have : (fun l => B l k) ∈ Set.range B.mulVec := ⟨Pi.single k 1, by
        funext l; simp [mulVec, dotProduct, Pi.single_apply]⟩
      rw [hrange] at this
      exact this
    have hrad := (mem_watsonSub_iff_redVec_mem p).1 hmem
    have := rad_support_of_diag p hp f _ _ (hred T T' hTT) _ hT1 hrad j ((he0 j).2 hj)
    rw [← toZMod_eq_zero_iff_dvd]
    rw [← this]
    simp [hM, hBp, Matrix.mul_apply, mulVec, dotProduct, map_sum, redVec_apply]
  -- the matrix W
  let D : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.diagonal fun j => if ν j = 0 then (p : ℤ_[p]) else 1
  have hexW : ∀ j k, ∃ w : ℤ_[p], M j k = (if ν j = 0 then (p : ℤ_[p]) else 1) * w := by
    intro j k
    by_cases hj : ν j = 0
    · obtain ⟨w, hw⟩ := hMdvd j k hj
      exact ⟨w, by simp [hj, hw]⟩
    · exact ⟨M j k, by simp [hj]⟩
  choose Wf hWf using hexW
  set W : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of Wf with hW
  have hMDW : M = D * W := by
    ext j k
    simp [D, hW, Matrix.diagonal_mul, hWf j k]
  -- determinants
  have hdetD : D.det = (p : ℤ_[p]) ^ (Finset.univ.filter fun i => ν i = 0).card := by
    simp [D, Matrix.det_diagonal, Finset.prod_ite]
  have hdetT' : IsUnit T'.det := Matrix.isUnit_det_of_left_inverse hTT
  have hdetBp : Bp.det = (B.det : ℤ_[p]) := by
    have := RingHom.map_det (algebraMap ℤ ℤ_[p]) B
    rw [hBp]; exact this.symm
  obtain ⟨s, hs, hsB⟩ : ∃ s : ℤ_[p], IsUnit s ∧ (B.det : ℤ_[p]) = s * (p : ℤ_[p]) ^ rankModP p f := by
    rcases Int.natAbs_eq B.det with h | h
    · refine ⟨1, isUnit_one, ?_⟩
      rw [h, hdetB]; push_cast; ring
    · refine ⟨-1, isUnit_one.neg, ?_⟩
      rw [h, hdetB]; push_cast; ring
  have hdetEq : T'.det * (s * (p : ℤ_[p]) ^ rankModP p f) = (p : ℤ_[p]) ^ (Finset.univ.filter fun i => ν i = 0).card * W.det := by
    rw [← hsB, ← hdetBp, ← hdetD, ← Matrix.det_mul, ← Matrix.det_mul, ← hMDW, hM]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrf
  rw [hk, pow_add] at hdetEq
  have hcancel : T'.det * s = (p : ℤ_[p]) ^ k * W.det := by
    have hpr : (p : ℤ_[p]) ^ rankModP p f ≠ 0 := pow_ne_zero _ hp0
    apply mul_right_cancel₀ hpr
    linear_combination hdetEq
  have hk0 : k = 0 := by
    by_contra hk0
    have hdv : (p : ℤ_[p]) ∣ T'.det * s := by
      rw [hcancel]
      exact Dvd.dvd.mul_right (dvd_pow_self _ hk0) _
    exact (PadicInt.irreducible_p (p := p)).not_isUnit (isUnit_of_dvd_unit hdv (hdetT'.mul hs))
  subst hk0
  have hrfeq : rankModP p f = (Finset.univ.filter fun i => ν i = 0).card := by omega
  have hdetW : IsUnit W.det := by
    have : W.det = T'.det * s := by rw [hcancel]; simp
    rw [this]; exact hdetT'.mul hs
  refine ⟨hrfeq, ?_⟩
  -- the form g in the basis W⁻¹
  set W' := W⁻¹ with hW'
  have hWW' : W * W' = 1 := Matrix.mul_nonsing_inv _ hdetW
  have hW'W : W' * W = 1 := Matrix.nonsing_inv_mul _ hdetW
  have hBpe : Bp = T * D * W := by
    calc Bp = (T * T') * Bp := by rw [hTT, one_mul]
      _ = T * M := by rw [hM, Matrix.mul_assoc]
      _ = T * D * W := by rw [hMDW, Matrix.mul_assoc]
  let ε : Fin n → ℕ := fun i => if ν i = 0 then 1 else ν i - 1
  let e : Fin n → ℤ_[p] := fun i => (p : ℤ_[p]) ^ ε i * u i
  have hgW : ∀ y, g.evalIn ℤ_[p] (W' *ᵥ y) = ∑ i, e i * y i ^ 2 := by
    intro y
    have h1 := evalIn_map_mulVec_of_eval p f g B (p : ℤ) hg (W' *ᵥ y)
    have h2 : Bp *ᵥ (W' *ᵥ y) = T *ᵥ (D *ᵥ y) := by
      rw [hBpe, mulVec_mulVec, Matrix.mul_assoc (T * D) W W', hWW', Matrix.mul_one, mulVec_mulVec]
    rw [← hBp, h2, hT] at h1
    apply mul_left_cancel₀ hp0
    rw [show ((p : ℤ) : ℤ_[p]) = (p : ℤ_[p]) by simp] at h1
    rw [← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [D, mulVec_diagonal, e, ε]
    rcases Nat.eq_zero_or_pos (ν i) with h0 | h0
    · simp [h0]; ring
    · have : ν i = (ν i - 1) + 1 := by omega
      simp only [h0.ne', ite_false, one_mul]
      rw [this]
      simp [pow_succ]
      ring
  have hg1 := toZMod_diag p g W' e hgW
  have hrg := rankModP_le_card_of_diag p g _ _ (hred W' W hW'W) _ hg1
  refine hrg.trans (Finset.card_le_card fun i hi => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have := (toZMod_pow_mul_ne_zero p (hu i)).1 hi
  simp only [ε] at this
  split_ifs at this
  omega

/-! ### Jordan decomposition over $\mathbb Z_p$ ($p$ odd) -/

/-- The value of a diagonal form: $\langle a_0, \dots, a_{n-1}\rangle(\vec z) = \sum_i a_i z_i^2$. -/
theorem eval_diag' {R : Type*} [CommRing R] (a : Fin n → R) (z : Fin n → R) :
    (QuadForm.diag a).eval z = ∑ i, a i * z i ^ 2 := by
  simp only [QuadForm.diag, QuadForm.evalIn, diagonal_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp; ring

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR in
/-- **Diagonalization over $\mathbb Z_p$, $p$ odd** (Jordan decomposition, Watson 1962, §2): a nondegenerate
integral form $f$ is $\mathrm{GL}_n(\mathbb Z_p)$-equivalent to a diagonal form $\langle p^{\nu_i} u_i \rangle$ with
$u_i \in \mathbb Z_p^\times$: there are mutually inverse matrices `T`, `T'` over $\mathbb Z_p$ with
$f(T\vec y) = \sum_i p^{\nu_i} u_i y_i^2$. (`exists_jordanForm_isGLEquiv` with the block set $P = \emptyset$ for
$p \nmid 2$.) -/
theorem exists_diag_padic (hp : p ≠ 2) (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0) :
    ∃ (T T' : Matrix (Fin n) (Fin n) ℤ_[p]) (ν : Fin n → ℕ) (u : Fin n → ℤ_[p]),
      T * T' = 1 ∧ (∀ i, IsUnit (u i)) ∧
      ∀ y, f.evalIn ℤ_[p] (T *ᵥ y) = ∑ i, ((p : ℤ_[p]) ^ ν i * u i) * y i ^ 2 := by
  classical
  have hpirr : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have h2 : ¬ (p : ℤ_[p]) ∣ 2 := by
    intro h
    have h' : PadicInt.toZMod (2 : ℤ_[p]) = 0 := (toZMod_eq_zero_iff_dvd p _).2 h
    rw [map_ofNat] at h'
    exact two_ne_zero_zmod p hp h'
  have h2' : ¬ (p : ℤ_[p]) ^ 2 ∣ 2 := fun h => h2 ((dvd_pow_self _ two_ne_zero).trans h)
  set fp : QuadForm ℤ_[p] n := f.map (Int.castRingHom ℤ_[p]) with hfp
  have hnd : fp.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have : fp.hessian = f.hessian.map (Int.castRingHom ℤ_[p]) := by
      simp [QuadForm.hessian, hfp, QuadForm.map, Matrix.map_add, Matrix.transpose_map]
    have hd : (f.hessian.map (Int.castRingHom ℤ_[p])).det = ((f.hessian.det : ℤ) : ℤ_[p]) :=
      (RingHom.map_det (Int.castRingHom ℤ_[p]) f.hessian).symm
    rw [this, hd]
    exact fun h => hf (by exact_mod_cast h)
  obtain ⟨Q', P, ν, hJ, hP, U, hU, hE⟩ := exists_jordanForm_isGLEquiv fp hnd (p : ℤ_[p]) hpirr h2'
  have hP0 := hP h2
  subst hP0
  set a : Fin n → ℤ_[p] := fun i => Q'.coeff i i
  have hQ'a : Q' = QuadForm.diag a := by
    refine QuadForm.ext (Matrix.ext fun i j => ?_)
    simp only [QuadForm.diag, Matrix.diagonal_apply, a]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h.ne)]; exact hJ.2.2.2.1 i j h (by simp)
    · simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h.ne')]; exact Q'.upper (show id j < id i from h)
  have hu : ∀ i, ∃ u, a i = (p : ℤ_[p]) ^ ν i * u ∧ IsUnit u := fun i =>
    hJ.2.2.2.2.2 i (by simp [IsPaired])
  choose u hau huu using hu
  have hUinv : IsUnit U.det := hU
  refine ⟨U, U⁻¹, ν, u, Matrix.mul_nonsing_inv _ hUinv, huu, fun y => ?_⟩
  have := hE y
  rw [hQ'a, eval_diag'] at this
  have e : fp.eval (U *ᵥ y) = f.evalIn ℤ_[p] (U *ᵥ y) := by
    simp [QuadForm.evalIn, hfp, QuadForm.map]
  rw [← e, ← this]
  exact Finset.sum_congr rfl fun i _ => by rw [hau i]

/-! ### Minimality: $n \le r_p(f) + r_p(g)$ -/

/-- **What minimality gives at $p$ after two steps** (Watson 1963, §2, p. 551): for a Watson-minimal positive definite
$f$, a prime $p$, and the derived form $g$ of `exists_derived_form` (basis matrix $B$ of $\Lambda_p(f)$,
$|\det B| = p^{r_p(f)}$), we have $n \le r_p(f) + r_p(g)$. *Proof:* take $h$ derived from $g$ at $p$ (basis matrix
$C$, $|\det C| = p^{r_p(g)}$); $h$ is reachable from $f$, and $(\det B)^2(\det C)^2 \det H_f = p^{2n} \det H_h$
(`det_sq_mul_det_hessian` twice), so minimality $|\det H_f| \le |\det H_h|$ gives $p^{2n} \le p^{2 r_p(f) + 2 r_p(g)}$. -/
theorem IsWatsonMinimal.exists_derived_rank_ge {f : QuadForm ℤ n} (hf : IntQF.PosDef f)
    (hmin : IsWatsonMinimal f) :
    ∃ (B : Matrix (Fin n) (Fin n) ℤ) (g : QuadForm ℤ n), B.det.natAbs = p ^ rankModP p f ∧
      Set.range B.mulVec = (watsonSub f (p : ℤ) : Set (Fin n → ℤ)) ∧
      (∀ x, f.eval (B *ᵥ x) = (p : ℤ) * g.eval x) ∧ n ≤ rankModP p f + rankModP p g := by
  have hpp : p.Prime := Fact.out
  obtain ⟨B, g, hdetB, hrange, hg⟩ := exists_derived_form p f
  refine ⟨B, g, hdetB, hrange, hg, ?_⟩
  obtain ⟨C, h, hdetC, hrangeC, hh⟩ := exists_derived_form p g
  have hBne : B.det ≠ 0 := by
    intro h0; rw [h0] at hdetB; simp at hdetB; exact (pow_pos hpp.pos _).ne' hdetB.symm
  have hCne : C.det ≠ 0 := by
    intro h0; rw [h0] at hdetC; simp at hdetC; exact (pow_pos hpp.pos _).ne' hdetC.symm
  have d1 : IsWatsonDerived f p g := ⟨hpp, B, hBne, hrange, hg⟩
  have d2 : IsWatsonDerived g p h := ⟨hpp, C, hCne, hrangeC, hh⟩
  have hle := hmin h ((Relation.ReflTransGen.single ⟨p, d1⟩).tail ⟨p, d2⟩)
  have e1 := congrArg Int.natAbs (det_sq_mul_det_hessian B hg)
  have e2 := congrArg Int.natAbs (det_sq_mul_det_hessian C hh)
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, hdetB, hdetC] at e1 e2
  have ha : 0 < f.hessian.det.natAbs := Int.natAbs_pos.mpr hf.nondegenerate
  have key : p ^ n * p ^ n * f.hessian.det.natAbs ≤
      (p ^ rankModP p g) ^ 2 * (p ^ rankModP p f) ^ 2 * f.hessian.det.natAbs := by
    calc p ^ n * p ^ n * f.hessian.det.natAbs ≤ p ^ n * p ^ n * h.hessian.det.natAbs :=
          Nat.mul_le_mul_left _ hle
      _ = p ^ n * (p ^ n * h.hessian.det.natAbs) := by ring
      _ = p ^ n * ((p ^ rankModP p g) ^ 2 * g.hessian.det.natAbs) := by rw [e2]
      _ = (p ^ rankModP p g) ^ 2 * (p ^ n * g.hessian.det.natAbs) := by ring
      _ = (p ^ rankModP p g) ^ 2 * ((p ^ rankModP p f) ^ 2 * f.hessian.det.natAbs) := by rw [e1]
      _ = _ := by ring
  have h1 := Nat.le_of_mul_le_mul_right key ha
  rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add] at h1
  have := (Nat.pow_le_pow_iff_right hpp.one_lt).mp h1
  omega

/-! ### Reordering the diagonal -/

/-- **Sorting a predicate to the front:** if exactly $r$ indices of $\{0, \dots, n-1\}$ satisfy `P`, there is a
permutation $\sigma$ with $P(\sigma(k)) \iff k < r$. -/
theorem exists_perm_of_card {r : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : (Finset.univ.filter P).card = r) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : Fin n, (k : ℕ) < r ↔ P (σ k) := by
  classical
  have hr : r ≤ n := by
    rw [← h]; exact (Finset.card_le_univ _).trans (by simp)
  have c1 : Fintype.card {i // P i} = r := by rw [Fintype.card_subtype]; exact h
  have c2 : Fintype.card {i // ¬ P i} = n - r := by
    rw [Fintype.card_subtype_compl, c1]; simp
  let e1 : {i // P i} ≃ Fin r := Fintype.equivFinOfCardEq c1
  let e2 : {i // ¬ P i} ≃ Fin (n - r) := Fintype.equivFinOfCardEq c2
  let E : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  let σ' : Fin r ⊕ Fin (n - r) ≃ Fin n := (Equiv.sumCongr e1.symm e2.symm).trans (Equiv.sumCompl P)
  refine ⟨E.symm.trans σ', fun k => ?_⟩
  have hEl : ∀ a, (E (Sum.inl a) : ℕ) = a := by intro a; simp [E]
  have hEr : ∀ b, (E (Sum.inr b) : ℕ) = r + b := by intro b; simp [E]
  suffices H : ∀ s, ((E s : ℕ) < r ↔ P ((E.symm.trans σ') (E s))) by
    obtain ⟨s, hs⟩ := E.surjective k
    rw [← hs]; exact H s
  intro s
  show (E s : ℕ) < r ↔ P (σ' (E.symm (E s)))
  rw [Equiv.symm_apply_apply]
  rcases s with a | b
  · rw [hEl]
    simp only [σ', Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ⟨fun _ => (e1.symm a).2, fun _ => a.2⟩
  · rw [hEr]
    simp only [σ', Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ⟨fun h => by omega, fun h => absurd h (e2.symm b).2⟩

/-- **Permuting a diagonal form:** $\langle a_0, \dots, a_{n-1}\rangle \cong \langle a_{\sigma(0)}, \dots,
a_{\sigma(n-1)}\rangle$ over any commutative ring (a permutation matrix). -/
theorem isometricGL_diag_perm {K : Type*} [CommRing K] (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    IsometricGL (QuadForm.diag a) (QuadForm.diag fun k => a (σ k)) := by
  rw [isometricGL_iff_isometricIn]
  refine ⟨(1 : Matrix (Fin n) (Fin n) K).submatrix σ.symm id, ?_, fun x => ?_⟩
  · rw [Matrix.det_permute, Matrix.det_one, mul_one]
    simpa using (Units.isUnit (Equiv.Perm.sign σ.symm)).map (Int.castRingHom K)
  · have hv : ((1 : Matrix (Fin n) (Fin n) K).submatrix σ.symm id) *ᵥ x = fun i => x (σ.symm i) := by
      funext i
      simp [mulVec, dotProduct, Matrix.one_apply]
    show (QuadForm.diag a).eval _ = (QuadForm.diag _).eval x
    rw [hv, eval_diag', eval_diag']
    have := Equiv.sum_comp σ (fun i => a i * x (σ.symm i) ^ 2)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm

/-! ### The theorem -/

/-- **Watson-minimal forms are $p$-adically square-free at odd primes** (Watson 1963, §2, proof of Theorem 2, p. 551;
Watson 1962, Theorems 3, 4): if $f$ is a Watson-minimal positive definite integral form in $n$ variables and $p$ is an
odd prime, then over $\mathbb Z_p$
$$ f \cong \langle u_0, \dots, u_{r-1}, p\,u_r, \dots, p\,u_{n-1}\rangle, \qquad r = r_p(f) \ (\texttt{rankModP}),\
   u_i \in \mathbb Z_p^\times,$$
i.e. the Jordan decomposition of $f$ at $p$ has only the scales $1$ and $p$, the unimodular part having rank $r_p(f)$.
(Indices are 0-based: Watson's $u_1, \dots, u_r$ are `u 0`, …, `u (r-1)` here.)
*Proof:* diagonalize $f \cong \langle p^{\nu_i} u_i \rangle$ (`exists_diag_padic`); for $g$ derived from $f$ at $p$
minimality gives $n \le r_p(f) + r_p(g)$ (`IsWatsonMinimal.exists_derived_rank_ge`), while locally
$r_p(f) = \#\{\nu_i = 0\}$ and $r_p(g) \le \#\{\nu_i = 1\}$ (`local_analysis`), so no $\nu_i \ge 2$ occurs;
finally the $\nu_i = 0$ coordinates are moved to the front (`exists_perm_of_card`, `isometricGL_diag_perm`).
Arguments: `hf` positive definiteness, `hmin` Watson-minimality, the odd prime `p`. -/
@[kb "watson1963" "§2, proof of Theorem 2, p. 551 (minimal forms are square-free; odd p)"]
theorem exists_diag_of_minimal_odd {n : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ u : Fin n → ℤ_[p], (∀ i, IsUnit (u i)) ∧
      IsometricGL (f.map (Int.castRingHom ℤ_[p]))
        (QuadForm.diag fun i => if (i : ℕ) < rankModP p f then u i else (p : ℤ_[p]) * u i) := by
  classical
  obtain ⟨T, T', ν, w, hTT, hw, hT⟩ := exists_diag_padic p hp f hf.nondegenerate
  obtain ⟨B, g, hdetB, hrange, hg, hn⟩ := IsWatsonMinimal.exists_derived_rank_ge p hf hmin
  obtain ⟨h1, h2⟩ := local_analysis p hp f g B hdetB hrange hg T T' hTT ν w hw hT
  have hcount : (Finset.univ.filter fun i => ν i = 0).card + (Finset.univ.filter fun i => ν i = 1).card +
      (Finset.univ.filter fun i => 2 ≤ ν i).card = n := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : ∀ i, ((if ν i = 0 then 1 else 0) + (if ν i = 1 then 1 else 0) + (if 2 ≤ ν i then 1 else 0) : ℕ) = 1 :=
      fun i => by split_ifs <;> omega
    simp [this]
  have hc2 : (Finset.univ.filter fun i => 2 ≤ ν i).card = 0 := by omega
  have hν : ∀ i, ν i ≤ 1 := fun i => by
    have := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hc2) (Finset.mem_univ i)
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (fun i => ν i = 0) h1.symm
  refine ⟨fun k => w (σ k), fun k => hw _, ?_⟩
  set a : Fin n → ℤ_[p] := fun i => (p : ℤ_[p]) ^ ν i * w i with ha
  have step1 : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.diag a) := by
    rw [isometricGL_iff_isometricIn]
    refine ⟨T, Matrix.isUnit_det_of_right_inverse hTT, fun x => ?_⟩
    show (f.map (Int.castRingHom ℤ_[p])).eval (T *ᵥ x) = (QuadForm.diag a).eval x
    rw [eval_diag']
    have e : (f.map (Int.castRingHom ℤ_[p])).eval (T *ᵥ x) = f.evalIn ℤ_[p] (T *ᵥ x) := by
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e, hT]
  have step2 := isometricGL_diag_perm a σ
  have hdiag : (QuadForm.diag fun k => a (σ k)) = QuadForm.diag
      (fun k : Fin n => if (k : ℕ) < rankModP p f then w (σ k) else (p : ℤ_[p]) * w (σ k)) := by
    congr 1
    funext k
    have hk := hσ k
    simp only [ha]
    by_cases hlt : (k : ℕ) < rankModP p f
    · have : ν (σ k) = 0 := hk.1 hlt
      simp [hlt, this]
    · have h0 : ν (σ k) ≠ 0 := fun h0 => hlt (hk.2 h0)
      have : ν (σ k) = 1 := by have := hν (σ k); omega
      simp [hlt, this]
  rw [hdiag] at step2
  exact step1.trans step2

end QuadFormsKB.Watson1963
