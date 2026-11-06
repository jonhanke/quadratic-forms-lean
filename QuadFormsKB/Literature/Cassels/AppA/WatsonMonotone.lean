/-
# Cassels, Appendix A, §3: Watson's operation does not increase the number of classes

Cassels, *Rational Quadratic Forms* (1978), Appendix A, §3, p. 365. **Proves** the named statement
`WatsonOperationMonotone` of `Watson.lean` (`watsonOperationMonotone_holds`), in the stronger form
`encard_genusClasses_le_of_isWatsonDerived` (no definiteness needed): if $Q'$ is derived from $Q$ at a prime $p$
(`IsWatsonDerived`), the genus of $Q'$ has at most as many classes as the genus of $Q$.

**Route (purely local).**
* The derived class is determined by the class (`intEquiv_of_isWatsonDerived`): an equivalence maps $\Lambda_p$ onto
  $\Lambda_p$, and two bases of one lattice differ by $\mathrm{GL}_n(\mathbb Z)$.
* Every form $Q''$ in the genus of $Q'$ is derived from a form $R$ in the genus of $Q$
  (`exists_watsonDerived_of_sameGenus`; Cassels' footnote: the lattice $\Lambda' \supseteq \Lambda'_p$). The
  overlattice is built at $p$ alone (`wm_exists_basis_change`: approximate modulo $p$, take a basis of
  $B_0\mathbb Z^n + p\mathbb Z^n$); at the other primes and over $\mathbb R$, $p$ is a unit
  (`wm_isometricGL_of_unit`). Membership in $\Lambda_p$ is transferred to $\mathbb Z_p$ (`PadicWatsonCond`,
  `wm_mem_watsonSub_iff`, `wm_padicWatsonCond_iff`).
* Choosing such an $R$ for each class gives an injection of classes.

Variables are $x_0, \dots, x_{n-1}$.
-/
import QuadFormsKB.Literature.Cassels.AppA.Remaining
import QuadFormsKB.Binary.GenusLocal

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.DefiniteForms

open Siegel

variable {n : ℕ}

/-! ### Matrix helpers -/

/-- Helper: left cancellation by a square matrix $M$ with $\det M \ne 0$ over an integral domain: $MA = MB$ implies
$A = B$. Arguments: `hM` the non-vanishing of $\det M$, `h` the equation $MA = MB$. -/
theorem wm_cancel_left {R : Type*} [CommRing R] [IsDomain R] {M A B : Matrix (Fin n) (Fin n) R}
    (hM : M.det ≠ 0) (h : M * A = M * B) : A = B := by
  have h2 : M.adjugate * (M * A) = M.adjugate * (M * B) := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.one_mul] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hM this

/-- Helper: if every column $N e_j$ of $N$ lies in the image of $M$, then $N = MV$ for a matrix $V$. Arguments:
`h` gives, for each column index $j$, a preimage of $N e_j$. -/
theorem wm_exists_mul_eq {R : Type*} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (h : ∀ j, ∃ x, M *ᵥ x = N *ᵥ Pi.single j 1) : ∃ V, M * V = N := by
  choose x hx using h
  refine ⟨Matrix.of fun i j => x j i, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- Helper: two integer $n \times n$ matrices $M_1$, $M_2$ with $\det M_1 \ne 0$ and the same image
$M_1\mathbb Z^n = M_2\mathbb Z^n$ differ by a unimodular matrix: $M_2 = M_1 V$ with $V \in \mathrm{GL}_n(\mathbb Z)$.
Arguments: `h1` the non-vanishing of $\det M_1$, `h` the equality of the images. -/
theorem wm_exists_gl_of_range_eq {M₁ M₂ : Matrix (Fin n) (Fin n) ℤ} (h1 : M₁.det ≠ 0)
    (h : Set.range M₁.mulVec = Set.range M₂.mulVec) : ∃ V : GL (Fin n) ℤ, M₂ = M₁ * V.val := by
  obtain ⟨V, hV⟩ := wm_exists_mul_eq (M := M₁) (N := M₂) fun j => by
    have : M₂ *ᵥ Pi.single j 1 ∈ Set.range M₁.mulVec := h ▸ ⟨_, rfl⟩
    exact this
  obtain ⟨V', hV'⟩ := wm_exists_mul_eq (M := M₂) (N := M₁) fun j => by
    have : M₁ *ᵥ Pi.single j 1 ∈ Set.range M₂.mulVec := h ▸ ⟨_, rfl⟩
    exact this
  have hVV : V * V' = 1 := wm_cancel_left h1 (by rw [← Matrix.mul_assoc, hV, hV', Matrix.mul_one])
  exact ⟨⟨V, V', hVV, mul_eq_one_comm.mp hVV⟩, hV.symm⟩

/-- Helper: the image of the scalar matrix $c \cdot 1$ under a ring homomorphism $f$ is $f(c) \cdot 1$. Arguments:
`f` the ring homomorphism, `c` the scalar. -/
theorem wm_map_smul_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    ((c • (1 : Matrix (Fin n) (Fin n) R)).map f) = f c • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

/-- Helper: a submodule $K$ of $\mathbb Z^n$ containing $c\,\mathbb Z^n$ ($c \ne 0$) is the image $B\mathbb Z^n$ of
a square integer matrix $B$ (a basis of $K$ has exactly $n$ elements). Arguments: `hc` the non-vanishing of `c`,
`K` the submodule, `hK` the inclusion $c\,\mathbb Z^n \subseteq K$. -/
theorem wm_exists_matrix_of_submodule {c : ℤ} (hc : c ≠ 0) (K : Submodule ℤ (Fin n → ℤ))
    (hK : ∀ y : Fin n → ℤ, c • y ∈ K) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ, ∀ z, z ∈ K ↔ ∃ x, B *ᵥ x = z := by
  obtain ⟨m, bK⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) K
  have : Module.Finite ℤ K := Module.Finite.of_basis bK
  have hm1 : m ≤ n := by
    have hli : LinearIndependent ℤ (K.subtype ∘ bK) :=
      bK.linearIndependent.map' _ (Submodule.ker_subtype K)
    have := hli.fintype_card_le_finrank
    simpa using this
  have hm2 : n ≤ m := by
    let v : Fin n → K := fun i => ⟨c • Pi.single i 1, hK _⟩
    have hli : LinearIndependent ℤ v := by
      apply LinearIndependent.of_comp K.subtype
      rw [Fintype.linearIndependent_iff]
      intro a ha i
      have := congrFun ha i
      simp only [v, Function.comp_apply, Submodule.subtype_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
      simp only [ite_true] at this
      exact (mul_eq_zero.mp this).resolve_right hc
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bK, Fintype.card_fin] at this
  have hm : m = n := le_antisymm hm1 hm2
  let b : Module.Basis (Fin n) ℤ K := bK.reindex (finCongr hm)
  refine ⟨Matrix.of fun i j => (b j : Fin n → ℤ) i, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine ⟨fun j => b.repr ⟨z, hz⟩ j, ?_⟩
    have := congrArg (fun y : K => (y : Fin n → ℤ)) (b.sum_repr ⟨z, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    conv_rhs => rw [← this]
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  · rintro ⟨x, rfl⟩
    have : (Matrix.of fun i j => (b j : Fin n → ℤ) i) *ᵥ x = ∑ j, x j • (b j : Fin n → ℤ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact K.sum_mem fun j _ => K.smul_mem _ (b j).2

/-! ### The derived class is determined by the class -/

/-- **Derived forms of equivalent forms are equivalent** (Cassels, App. A, §3, p. 365: isomorphic lattices produce
isomorphic $\Lambda_p$). If $S_1$ is derived from $R_1$ and $S_2$ from $R_2$ at the same prime $p$, and $R_1$, $R_2$
are $\mathrm{GL}_n(\mathbb Z)$-equivalent, then so are $S_1$ and $S_2$: an equivalence $u$ maps $\Lambda_p(R_2)$ onto
$\Lambda_p(R_1)$, and two bases of the same lattice differ by a unimodular matrix. Arguments: `h₁`, `h₂` the two
derived-form relations, `hR` the equivalence of $R_1$ and $R_2$. -/
theorem intEquiv_of_isWatsonDerived {R₁ R₂ S₁ S₂ : QuadForm ℤ n} {p : ℕ} (h₁ : IsWatsonDerived R₁ p S₁)
    (h₂ : IsWatsonDerived R₂ p S₂) (hR : IntEquiv R₁ R₂) : IntEquiv S₁ S₂ := by
  obtain ⟨hp, g₁, hg₁, hr₁, hQ₁⟩ := h₁
  obtain ⟨-, g₂, -, hr₂, hQ₂⟩ := h₂
  obtain ⟨u, hu⟩ := hR
  have huu : ∀ y : Fin n → ℤ, u.val *ᵥ ((u⁻¹).val *ᵥ y) = y := fun y => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hrange : Set.range g₁.mulVec = Set.range (u.val * g₂).mulVec := by
    rw [hr₁]
    ext y
    constructor
    · intro hy
      have : (u⁻¹).val *ᵥ y ∈ watsonSub R₂ (p : ℤ) := by
        rw [← mem_watsonSub_iff_of_isometry (p : ℤ) u hu, huu]
        exact hy
      rw [← SetLike.mem_coe, ← hr₂] at this
      obtain ⟨x, hx⟩ := this
      refine ⟨x, ?_⟩
      rw [← mulVec_mulVec, hx, huu]
    · rintro ⟨x, rfl⟩
      rw [← mulVec_mulVec]
      exact (mem_watsonSub_iff_of_isometry (p : ℤ) u hu _).mpr
        (by rw [← SetLike.mem_coe, ← hr₂]; exact ⟨x, rfl⟩)
  obtain ⟨V, hV⟩ := wm_exists_gl_of_range_eq hg₁ hrange
  refine ⟨V, fun x => ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hp0
  rw [← hQ₁, ← hQ₂, ← hu, mulVec_mulVec, mulVec_mulVec, hV]

/-! ### $p$-adic transfer of Watson's condition -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper: every $z \in \mathbb Z_p$ is $a + p e$ with $a \in \mathbb Z$ and $e \in \mathbb Z_p$. Argument: `z`. -/
theorem wm_exists_int_approx (z : ℤ_[p]) : ∃ (a : ℤ) (e : ℤ_[p]), z = a + p * e := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec 1 z)
  refine ⟨(z.appr 1 : ℤ), t, ?_⟩
  push_cast
  rw [pow_one] at ht
  linear_combination ht

/-- Helper: every $\vec v \in \mathbb Z_p^n$ is $\vec v_0 + p\vec v_1$ with $\vec v_0 \in \mathbb Z^n$ and
$\vec v_1 \in \mathbb Z_p^n$. Argument: `v`. -/
theorem wm_exists_vec_approx (v : Fin n → ℤ_[p]) :
    ∃ (v₀ : Fin n → ℤ) (v₁ : Fin n → ℤ_[p]), v = (fun i => (v₀ i : ℤ_[p])) + (p : ℤ_[p]) • v₁ := by
  choose a e h using fun i => wm_exists_int_approx (v i)
  exact ⟨a, e, funext fun i => by simp [h i]⟩

/-- Helper: every matrix $M$ over $\mathbb Z_p$ is $M_0 + pE$ with $M_0$ an integer matrix and $E$ over
$\mathbb Z_p$. Argument: `M`. -/
theorem wm_exists_mat_approx (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    ∃ (M₀ : Matrix (Fin n) (Fin n) ℤ) (E : Matrix (Fin n) (Fin n) ℤ_[p]),
      M = M₀.map (Int.castRingHom ℤ_[p]) + (p : ℤ_[p]) • E := by
  choose a e h using fun i j => wm_exists_int_approx (M i j)
  exact ⟨Matrix.of a, Matrix.of e, by ext i j; simp [h i j]⟩

/-- Helper: the value of the base change of an integral form at an integer vector is the image of the integer value.
Arguments: `Q` the form, `x` the integer vector. -/
theorem wm_eval_map_cast {K : Type*} [CommRing K] (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    (Q.map (Int.castRingHom K)).eval (fun i => (x i : K)) = (Q.eval x : K) := by
  have := AWS.evalIn_map Q (Int.castRingHom K) x
  simp only [eq_intCast] at this
  rw [this]
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
    RingHom.id_apply, eq_intCast, Function.comp_apply]

/-- Helper: casting commutes with matrix-vector multiplication. Arguments: `M` the integer matrix, `x` the integer
vector. -/
theorem wm_cast_mulVec {K : Type*} [CommRing K] (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (fun i => ((M *ᵥ x) i : K)) = M.map (Int.castRingHom K) *ᵥ (fun i => (x i : K)) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- **Watson's condition over $\mathbb Z_p$:** for an integral form $Q$ and $\vec v \in \mathbb Z_p^n$,
$Q(\vec b + \vec v) \equiv Q(\vec b) \pmod{p\mathbb Z_p}$ for every $\vec b \in \mathbb Z_p^n$. On integer vectors this
is membership in $\Lambda_p$ = `watsonSub Q p` (`wm_mem_watsonSub_iff`). Arguments: `Q` the form, `p` the prime,
`v` the vector. -/
def PadicWatsonCond (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ_[p]) : Prop :=
  ∀ b : Fin n → ℤ_[p], (p : ℤ_[p]) ∣
    (Q.map (Int.castRingHom ℤ_[p])).eval (b + v) - (Q.map (Int.castRingHom ℤ_[p])).eval b

/-- Helper: Watson's condition over $\mathbb Z_p$ is closed under addition. Arguments: `hv`, `hw` the conditions for
$\vec v$ and $\vec w$. -/
theorem PadicWatsonCond.add {Q : QuadForm ℤ n} {v w : Fin n → ℤ_[p]} (hv : PadicWatsonCond Q p v)
    (hw : PadicWatsonCond Q p w) : PadicWatsonCond Q p (v + w) := by
  intro b
  have := dvd_add (hw (b + v)) (hv b)
  rw [← add_assoc]
  convert this using 1
  ring

/-- Helper: every vector $p\vec u$, $\vec u \in \mathbb Z_p^n$, satisfies Watson's condition over $\mathbb Z_p$
($Q(\vec b + p\vec u) - Q(\vec b) = p\,\vec b^{\mathsf T} H \vec u + p^2 Q(\vec u)$). Arguments: `Q` the form, `u` the
vector. -/
theorem wm_padicWatsonCond_smul (Q : QuadForm ℤ n) (u : Fin n → ℤ_[p]) :
    PadicWatsonCond Q p ((p : ℤ_[p]) • u) := by
  intro b
  have h := (Q.map (Int.castRingHom ℤ_[p])).polar_eq_hessian ℤ_[p] b ((p : ℤ_[p]) • u)
  have h2 := Kneser.eval_smul_gen (Q.map (Int.castRingHom ℤ_[p])) u (p : ℤ_[p])
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul] at h
  refine ⟨b ⬝ᵥ ((Q.map (Int.castRingHom ℤ_[p])).hessian.map (algebraMap ℤ_[p] ℤ_[p]) *ᵥ u) +
    p * (Q.map (Int.castRingHom ℤ_[p])).eval u, ?_⟩
  linear_combination h + h2

/-- Helper: an integer vector satisfies Watson's condition over $\mathbb Z_p$ if and only if it lies in
$\Lambda_p$ = `watsonSub Q p` (approximate $\vec b \in \mathbb Z_p^n$ by an integer vector modulo $p$). Arguments: `Q`
the form, `c` the integer vector. -/
theorem wm_mem_watsonSub_iff (Q : QuadForm ℤ n) (c : Fin n → ℤ) :
    c ∈ watsonSub Q (p : ℤ) ↔ PadicWatsonCond Q p (fun i => (c i : ℤ_[p])) := by
  have hcast : ∀ x y : Fin n → ℤ, (fun i => (x i : ℤ_[p])) + (fun i => (y i : ℤ_[p])) =
      (fun i => ((x + y) i : ℤ_[p])) := fun x y => by ext i; simp
  constructor
  · intro hc b
    obtain ⟨b₀, b₁, rfl⟩ := wm_exists_vec_approx b
    have h1 := wm_padicWatsonCond_smul Q b₁ ((fun i => (b₀ i : ℤ_[p])) + fun i => (c i : ℤ_[p]))
    have h2 := wm_padicWatsonCond_smul Q b₁ (fun i => (b₀ i : ℤ_[p]))
    have h3 : (p : ℤ_[p]) ∣ (Q.map (Int.castRingHom ℤ_[p])).eval
        ((fun i => (b₀ i : ℤ_[p])) + fun i => (c i : ℤ_[p])) -
          (Q.map (Int.castRingHom ℤ_[p])).eval (fun i => (b₀ i : ℤ_[p])) := by
      rw [hcast, wm_eval_map_cast, wm_eval_map_cast, ← Int.cast_sub]
      obtain ⟨k, hk⟩ := hc b₀
      exact ⟨k, by rw [hk]; push_cast; ring⟩
    have e : (fun i => (b₀ i : ℤ_[p])) + (p : ℤ_[p]) • b₁ + (fun i => (c i : ℤ_[p])) =
        ((fun i => (b₀ i : ℤ_[p])) + fun i => (c i : ℤ_[p])) + (p : ℤ_[p]) • b₁ := by abel
    rw [e]
    have := dvd_add (dvd_sub h1 h2) h3
    convert this using 1
    ring
  · intro h b
    apply Binary.int_dvd_of_padic_dvd (p := p)
    have := h (fun i => (b i : ℤ_[p]))
    rwa [hcast, wm_eval_map_cast, wm_eval_map_cast, ← Int.cast_sub] at this

/-- Helper: Watson's condition over $\mathbb Z_p$ is transported by $\mathbb Z_p$-isometries: if
$Q(U\vec x) = R(\vec x)$ with $U \in \mathrm{GL}_n(\mathbb Z_p)$, then $\vec v$ satisfies it for $R$ if and only if
$U\vec v$ satisfies it for $Q$. Arguments: `U` the isometry, `hU` the isometry identity, `v` the vector. -/
theorem wm_padicWatsonCond_iff_of_isometry {Q R : QuadForm ℤ n} (U : GL (Fin n) ℤ_[p])
    (hU : ∀ x, (Q.map (Int.castRingHom ℤ_[p])).eval (U.val *ᵥ x) = (R.map (Int.castRingHom ℤ_[p])).eval x)
    (v : Fin n → ℤ_[p]) : PadicWatsonCond R p v ↔ PadicWatsonCond Q p (U.val *ᵥ v) := by
  have hUU : ∀ y : Fin n → ℤ_[p], U.val *ᵥ ((U⁻¹).val *ᵥ y) = y := fun y => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  constructor
  · intro h b
    have := h ((U⁻¹).val *ᵥ b)
    rwa [← hU, ← hU, mulVec_add, hUU] at this
  · intro h b
    have := h (U.val *ᵥ b)
    rwa [← mulVec_add, hU, hU] at this

/-- Helper: if $g\mathbb Z^n = \Lambda_p$ and $gG = p\cdot 1$ with $G$ an integer matrix, then the vectors of
$\mathbb Z_p^n$ satisfying Watson's condition over $\mathbb Z_p$ are exactly those of $g\mathbb Z_p^n$. Arguments:
`hrange` the equality $g\mathbb Z^n = \Lambda_p$, `hgG` the identity $gG = p \cdot 1$, `v` the vector. -/
theorem wm_padicWatsonCond_iff {Q : QuadForm ℤ n} {g G : Matrix (Fin n) (Fin n) ℤ}
    (hrange : Set.range g.mulVec = (watsonSub Q (p : ℤ) : Set (Fin n → ℤ)))
    (hgG : g * G = (p : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) (v : Fin n → ℤ_[p]) :
    PadicWatsonCond Q p v ↔ ∃ w, v = g.map (Int.castRingHom ℤ_[p]) *ᵥ w := by
  have hgGp : g.map (Int.castRingHom ℤ_[p]) * G.map (Int.castRingHom ℤ_[p]) = (p : ℤ_[p]) • 1 := by
    rw [← Matrix.map_mul, hgG, wm_map_smul_one]
    simp
  have hint : ∀ c : Fin n → ℤ, c ∈ watsonSub Q (p : ℤ) →
      ∃ x : Fin n → ℤ, (fun i => (c i : ℤ_[p])) = g.map (Int.castRingHom ℤ_[p]) *ᵥ (fun i => (x i : ℤ_[p])) := by
    intro c hc
    rw [← SetLike.mem_coe, ← hrange] at hc
    obtain ⟨x, rfl⟩ := hc
    exact ⟨x, wm_cast_mulVec g x⟩
  constructor
  · intro h
    obtain ⟨v₀, v₁, rfl⟩ := wm_exists_vec_approx v
    have h0 : PadicWatsonCond Q p (fun i => (v₀ i : ℤ_[p])) := by
      have := h.add (wm_padicWatsonCond_smul Q (-v₁))
      convert this using 1
      rw [smul_neg]; abel
    obtain ⟨x, hx⟩ := hint v₀ ((wm_mem_watsonSub_iff Q v₀).mpr h0)
    refine ⟨(fun i => (x i : ℤ_[p])) + G.map (Int.castRingHom ℤ_[p]) *ᵥ v₁, ?_⟩
    rw [mulVec_add, mulVec_mulVec, hgGp, hx, smul_mulVec, one_mulVec]
  · rintro ⟨w, rfl⟩
    obtain ⟨w₀, w₁, rfl⟩ := wm_exists_vec_approx w
    rw [mulVec_add, mulVec_smul]
    refine PadicWatsonCond.add ?_ (wm_padicWatsonCond_smul Q _)
    rw [← wm_cast_mulVec]
    refine (wm_mem_watsonSub_iff Q _).mp ?_
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨w₀, rfl⟩

end Padic

/-! ### Forms: pull-backs, scaling, base change -/

/-- Helper: if $BX = c \cdot 1$ for square matrices over an integral domain and $c \ne 0$, then $\det B \ne 0$ and
$\det X \ne 0$. Arguments: `hBX` the identity $BX = c \cdot 1$, `hc` the non-vanishing of `c`. -/
theorem wm_det_ne_zero_of_mul_eq {R : Type*} [CommRing R] [IsDomain R] {B X : Matrix (Fin n) (Fin n) R} {c : R}
    (hBX : B * X = c • 1) (hc : c ≠ 0) : B.det ≠ 0 ∧ X.det ≠ 0 := by
  have h := congrArg Matrix.det hBX
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
  exact mul_ne_zero_iff.mp (h ▸ pow_ne_zero _ hc)

/-- Helper: if $BX = c \cdot 1$ with $\det B \ne 0$ over an integral domain, then also $XB = c \cdot 1$. Arguments:
`hB` the non-vanishing of $\det B$, `hBX` the identity $BX = c \cdot 1$. -/
theorem wm_mul_comm_of_mul_eq {R : Type*} [CommRing R] [IsDomain R] {B X : Matrix (Fin n) (Fin n) R} {c : R}
    (hB : B.det ≠ 0) (hBX : B * X = c • 1) : X * B = c • 1 :=
  wm_cancel_left hB (by rw [← Matrix.mul_assoc, hBX, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one])

/-- Helper: cancellation of a non-zero scalar on matrices over an integral domain. Arguments: `hc` the
non-vanishing of `c`, `h` the identity $cA = cB$. -/
theorem wm_smul_cancel {R : Type*} [CommRing R] [IsDomain R] {A B : Matrix (Fin n) (Fin n) R} {c : R}
    (hc : c ≠ 0) (h : c • A = c • B) : A = B := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

/-- Helper: the pull-back $\vec y \mapsto Q(B\vec y)$ of an integral form along an integer matrix $B$ is an integral
form. Arguments: `Q` the form, `B` the matrix. -/
theorem wm_exists_pullback (Q : QuadForm ℤ n) (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P : QuadForm ℤ n, ∀ y, P.eval y = Q.eval (B *ᵥ y) := by
  set A := Bᵀ * Q.coeff * B with hA
  refine ⟨QuadForm.ofUpper fun i j => if i = j then A i i else A i j + A j i,
    fun y => ((eval_mulVec_eq_iff Q _ B).mpr ?_ y).symm⟩
  ext i j
  simp only [defect, ← hA, QuadForm.ofUpper, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.zero_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij.le, not_le.mpr hij, hij.ne]
  · simp
  · simp only [not_le.mpr hij, hij.ne, hij.le, ite_true, ite_false]
    ring

/-- Helper: an integral form all of whose values are divisible by $c \ne 0$ is $c$ times an integral form.
Arguments: `hc` the non-vanishing of `c`, `h` the divisibility of all values. -/
theorem wm_exists_eq_smul_of_dvd {P : QuadForm ℤ n} {c : ℤ} (hc : c ≠ 0) (h : ∀ v, c ∣ P.eval v) :
    ∃ R : QuadForm ℤ n, P = c • R := by
  have hd : ∀ i j, c ∣ P.coeff i j := dvd_coeff_of_dvd_eval h
  choose d hd' using hd
  refine ⟨⟨Matrix.of d, fun i j hij => ?_⟩, ?_⟩
  · have h0 := P.upper hij
    have := hd' i j
    rw [h0] at this
    simp only [Matrix.of_apply]
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  · ext i j
    simp [hd' i j]

/-- Helper: an identity $Q_1(M\vec x) = c\,Q_2(\vec x)$ on $\mathbb Z^n$ holds after any base change
$f : \mathbb Z \to K$, for all $\vec x \in K^n$. Arguments: `f` the base change, `c` the scalar, `h` the integral
identity, `x` the vector over $K$. -/
theorem wm_eval_map_of_eq_smul {K : Type*} [CommRing K] (f : ℤ →+* K) {Q₁ Q₂ : QuadForm ℤ n}
    {M : Matrix (Fin n) (Fin n) ℤ} (c : ℤ) (h : ∀ x, Q₁.eval (M *ᵥ x) = c * Q₂.eval x) (x : Fin n → K) :
    (Q₁.map f).eval (M.map f *ᵥ x) = f c * (Q₂.map f).eval x := by
  have := eval_mulVec_map f (Q' := c • Q₂) (g := M) (fun y => by rw [h, Kneser.eval_smul_form]) x
  rwa [Kneser.map_smul_form, Kneser.eval_smul_form] at this

/-- Helper (the places where $p$ is a unit): let $gG = p \cdot 1$ and $BX = p \cdot 1$ for integer matrices, let
$Q(g\vec x) = p\,Q'(\vec x)$ and $Q''(B\vec x) = p\,R(\vec x)$ on $\mathbb Z^n$, and let $f : \mathbb Z \to K$ be a ring
homomorphism with $f(p)$ a unit. If $Q'$ and $Q''$ are $\mathrm{GL}_n(K)$-equivalent (by $h$), then so are $Q$ and
$R$, by $f(p)^{-1} g h B$. Arguments: `f` the base change, `u` the unit with `hu` : $u = f(p)$, `hgG`, `hBX` the two
matrix identities, `hQg`, `hR` the two form identities, `hiso` the equivalence of $Q'$ and $Q''$ over $K$. -/
theorem wm_isometricGL_of_unit {K : Type*} [CommRing K] (f : ℤ →+* K) {p : ℤ} (u : Kˣ) (hu : (u : K) = f p)
    {Q Q' Q'' R : QuadForm ℤ n} {g G B X : Matrix (Fin n) (Fin n) ℤ}
    (hgG : g * G = p • (1 : Matrix (Fin n) (Fin n) ℤ)) (hBX : B * X = p • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hQg : ∀ x, Q.eval (g *ᵥ x) = p * Q'.eval x) (hR : ∀ x, Q''.eval (B *ᵥ x) = p * R.eval x)
    (hiso : IsometricGL (Q'.map f) (Q''.map f)) : IsometricGL (Q.map f) (R.map f) := by
  obtain ⟨h, hh⟩ := hiso
  set v : K := ((u⁻¹ : Kˣ) : K) with hvdef
  have hv : v * f p = 1 := by rw [← hu, hvdef, Units.inv_mul]
  have e1 : B.map f * X.map f = f p • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.map_mul, hBX, wm_map_smul_one]
  have e2 : g.map f * G.map f = f p • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.map_mul, hgG, wm_map_smul_one]
  have e3 : h.val * (h⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set W := v • (g.map f * h.val * B.map f)
  set W' := v • (X.map f * (h⁻¹).val * G.map f)
  have hWW : W * W' = 1 := by
    have : g.map f * h.val * B.map f * (X.map f * (h⁻¹).val * G.map f) = (f p * f p) • 1 := by
      calc g.map f * h.val * B.map f * (X.map f * (h⁻¹).val * G.map f)
          = g.map f * h.val * (B.map f * X.map f) * (h⁻¹).val * G.map f := by
            simp only [Matrix.mul_assoc]
        _ = f p • (g.map f * (h.val * (h⁻¹).val) * G.map f) := by
            rw [e1]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = (f p * f p) • 1 := by rw [e3, Matrix.mul_one, e2, smul_smul]
    simp only [W, W', Matrix.smul_mul, Matrix.mul_smul, smul_smul, this]
    rw [show v * (v * (f p * f p)) = (v * f p) * (v * f p) by ring, hv, one_mul, one_smul]
  refine ⟨⟨W, W', hWW, mul_eq_one_comm.mp hWW⟩, fun x => ?_⟩
  show (Q.map f).eval (W *ᵥ x) = _
  simp only [W]
  rw [smul_mulVec, Kneser.eval_smul_gen, ← mulVec_mulVec, ← mulVec_mulVec,
    wm_eval_map_of_eq_smul f p hQg, hh, wm_eval_map_of_eq_smul f p hR]
  linear_combination (v * f p + 1) * (R.map f).eval x * hv

/-! ### The overlattice at $p$ -/

section Overlattice

variable {p : ℕ} [hp : Fact p.Prime]

/-- Helper (Cassels' footnote on p. 365: the lattice $\Lambda' \supseteq \Lambda'_p$, in coordinates). Let $g$, $G$ be
integer matrices with $Gg = p \cdot 1$ and $h \in \mathrm{GL}_n(\mathbb Z_p)$. There are integer matrices $B$, $X$
with $BX = XB = p\cdot 1$ and $U \in \mathrm{GL}_n(\mathbb Z_p)$ with $B = h^{-1} G U$ over $\mathbb Z_p$; that is,
$B\mathbb Z_p^n = h^{-1}G\mathbb Z_p^n$ while $B \in \mathrm{GL}_n(\mathbb Z[1/p])$. *Proof:* approximate
$G' = h^{-1}G$ modulo $p$ by an integer matrix $B_0$ and take for $B$ a basis matrix of $B_0\mathbb Z^n + p\mathbb Z^n$.
Arguments: `hGg` the identity $Gg = p \cdot 1$, `h` the $p$-adic matrix. -/
theorem wm_exists_basis_change {g G : Matrix (Fin n) (Fin n) ℤ}
    (hGg : G * g = (p : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) (h : GL (Fin n) ℤ_[p]) :
    ∃ (B X : Matrix (Fin n) (Fin n) ℤ) (U : GL (Fin n) ℤ_[p]),
      B * X = (p : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧ X * B = (p : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
        B.map (Int.castRingHom ℤ_[p]) = (h⁻¹).val * G.map (Int.castRingHom ℤ_[p]) * U.val := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set φ := Int.castRingHom ℤ_[p] with hφ
  have hφp : φ (p : ℤ) = (p : ℤ_[p]) := by simp [hφ]
  have hmap : ∀ M : Matrix (Fin n) (Fin n) ℤ, M = (p : ℤ) • 1 → M.map φ = (p : ℤ_[p]) • 1 := by
    intro M hM; rw [hM, wm_map_smul_one, hφp]
  set G' := (h⁻¹).val * G.map φ with hG'
  set A := g.map φ * h.val with hA
  have hG'A : G' * A = (p : ℤ_[p]) • 1 := by
    have e : G' * A = (h⁻¹).val * (G * g).map φ * h.val := by
      simp only [hG', hA, Matrix.map_mul, Matrix.mul_assoc]
    rw [e, hmap _ hGg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  obtain ⟨B₀, E, hB₀⟩ := wm_exists_mat_approx G'
  set K : Submodule ℤ (Fin n → ℤ) := LinearMap.range (B₀.mulVecLin.coprod ((p : ℤ) • LinearMap.id)) with hK
  have hpK : ∀ y : Fin n → ℤ, (p : ℤ) • y ∈ K := fun y => ⟨(0, y), by simp⟩
  obtain ⟨B, hB⟩ := wm_exists_matrix_of_submodule hp0 K hpK
  obtain ⟨X, hBX⟩ := wm_exists_mul_eq (M := B) (N := (p : ℤ) • 1) fun j => by
    rw [smul_mulVec, one_mulVec]; exact (hB _).mp (hpK _)
  have hdetB : B.det ≠ 0 := (wm_det_ne_zero_of_mul_eq hBX hp0).1
  have hXB := wm_mul_comm_of_mul_eq hdetB hBX
  obtain ⟨Y₁, hY₁⟩ := wm_exists_mul_eq (M := B) (N := B₀) fun j => (hB _).mp ⟨(Pi.single j 1, 0), by simp⟩
  have hcol : ∀ j, ∃ y : (Fin n → ℤ) × (Fin n → ℤ), B₀ *ᵥ y.1 + (p : ℤ) • y.2 = B *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := (hB (B *ᵥ Pi.single j 1)).mpr ⟨_, rfl⟩
    exact ⟨y, by simpa using hy⟩
  choose y hy using hcol
  set Y₂ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (y j).1 i
  set Y₃ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (y j).2 i
  have hBY : B = B₀ * Y₂ + (p : ℤ) • Y₃ := by
    ext i j
    have := congrFun (hy j) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Y₂, Y₃, Matrix.of_apply]
    exact this.symm
  -- over ℤ_p
  have hBp : B.map φ = (G' - (p : ℤ_[p]) • E) * Y₂.map φ + (p : ℤ_[p]) • Y₃.map φ := by
    have e1 : B.map φ = B₀.map φ * Y₂.map φ + (p : ℤ_[p]) • Y₃.map φ := by
      rw [hBY, ← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hφ, Int.coe_castRingHom,
        Int.cast_add, Int.cast_mul, Int.cast_natCast]
    have e2 : B₀.map φ = G' - (p : ℤ_[p]) • E := by rw [hB₀]; abel
    rw [e1, e2]
  set U₀ := Y₂.map φ + A * (Y₃.map φ - E * Y₂.map φ) with hU₀
  have hBU : B.map φ = G' * U₀ := by
    rw [hBp, hU₀]
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hG'A, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul]
    abel
  set V := Y₁.map φ + X.map φ * E with hV
  have hBV : B.map φ * V = G' := by
    rw [hV, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hY₁, hmap _ hBX,
      Matrix.smul_mul, Matrix.one_mul, hB₀]
  have hdetBp : (B.map φ).det ≠ 0 := by
    rw [Kneser.det_map_eq]
    simpa [hφ] using hdetB
  have hVU : V * U₀ = 1 := wm_cancel_left hdetBp (by rw [← Matrix.mul_assoc, hBV, ← hBU, Matrix.mul_one])
  exact ⟨B, X, ⟨U₀, V, mul_eq_one_comm.mp hVU, hVU⟩, hBX, hXB, hBU⟩

end Overlattice

/-! ### Every form in the genus of $Q'$ is derived from a form in the genus of $Q$ -/

/-- **Cassels, App. A, §3, footnote on p. 365 (going up).** Let $Q'$ be derived from $Q$ at the prime $p$, and let
$Q''$ be in the genus of $Q'$. Then there is a form $R$ in the genus of $Q$ from which $Q''$ is derived at $p$.
*Proof:* with $g$ the basis matrix of $\Lambda_p(Q)$ and $h \in \mathrm{GL}_n(\mathbb Z_p)$ an equivalence of $Q'$
and $Q''$, take integer matrices $B$, $X$ with $BX = XB = p \cdot 1$ and $B = h^{-1}GU$ over $\mathbb Z_p$
(`wm_exists_basis_change`), and $R(\vec y) = p^{-1}Q''(B\vec y)$, which is integral. Then $R(\vec y) = Q(U\vec y)$ over
$\mathbb Z_p$, $R \cong Q$ over every ring in which $p$ is a unit (by $p^{-1}ghB$), $R(X\vec x) = p\,Q''(\vec x)$, and
$X\mathbb Z^n = \Lambda_p(R)$ because membership in $\Lambda_p$ is a condition over $\mathbb Z_p$ that $U$ transports
(`wm_mem_watsonSub_iff`, `wm_padicWatsonCond_iff_of_isometry`, `wm_padicWatsonCond_iff`). Arguments: `hd` the
derived-form relation between `Q` and `Q'`, `hg` the genus relation between `Q'` and `Q''`. -/
theorem exists_watsonDerived_of_sameGenus {Q Q' Q'' : QuadForm ℤ n} {p : ℕ} (hd : IsWatsonDerived Q p Q')
    (hg : SameGenus Q' Q'') : ∃ R : QuadForm ℤ n, SameGenus Q R ∧ IsWatsonDerived R p Q'' := by
  obtain ⟨hpp, g, hgdet, hrange, hQg⟩ := hd
  have hfact : Fact p.Prime := ⟨hpp⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hpp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  obtain ⟨G, hgG⟩ := wm_exists_mul_eq (M := g) (N := (p : ℤ) • 1) fun j => by
    have : (p : ℤ) • Pi.single j (1 : ℤ) ∈ (watsonSub Q (p : ℤ) : Set (Fin n → ℤ)) :=
      smul_mem_watsonSub Q _ _
    rw [← hrange] at this
    rw [smul_mulVec, one_mulVec]
    exact this
  have hGg := wm_mul_comm_of_mul_eq hgdet hgG
  obtain ⟨h, hh⟩ := hg.1 p
  obtain ⟨B, X, U, hBX, hXB, hBU⟩ := wm_exists_basis_change hGg h
  have hφp : Int.castRingHom ℤ_[p] (p : ℤ) = (p : ℤ_[p]) := by simp
  have hgGp : g.map (Int.castRingHom ℤ_[p]) * G.map (Int.castRingHom ℤ_[p]) = (p : ℤ_[p]) • 1 := by
    rw [← Matrix.map_mul, hgG, wm_map_smul_one, hφp]
  have hGgp : G.map (Int.castRingHom ℤ_[p]) * g.map (Int.castRingHom ℤ_[p]) = (p : ℤ_[p]) • 1 := by
    rw [← Matrix.map_mul, hGg, wm_map_smul_one, hφp]
  have hAB : g.map (Int.castRingHom ℤ_[p]) * h.val * B.map (Int.castRingHom ℤ_[p]) = (p : ℤ_[p]) • U.val := by
    rw [hBU, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mul_assoc, hgGp, Matrix.smul_mul, Matrix.one_mul]
  have hQgp : ∀ z, (Q.map (Int.castRingHom ℤ_[p])).eval (g.map (Int.castRingHom ℤ_[p]) *ᵥ z) =
      (p : ℤ_[p]) * (Q'.map (Int.castRingHom ℤ_[p])).eval z := fun z => by
    rw [wm_eval_map_of_eq_smul _ (p : ℤ) hQg, hφp]
  have hkey : ∀ x, (Q''.map (Int.castRingHom ℤ_[p])).eval (B.map (Int.castRingHom ℤ_[p]) *ᵥ x) =
      (p : ℤ_[p]) * (Q.map (Int.castRingHom ℤ_[p])).eval (U.val *ᵥ x) := by
    intro x
    apply mul_left_cancel₀ hpp0
    calc (p : ℤ_[p]) * (Q''.map (Int.castRingHom ℤ_[p])).eval (B.map (Int.castRingHom ℤ_[p]) *ᵥ x)
        = p * (Q'.map (Int.castRingHom ℤ_[p])).eval (h.val *ᵥ (B.map (Int.castRingHom ℤ_[p]) *ᵥ x)) := by
          rw [hh]
      _ = (Q.map (Int.castRingHom ℤ_[p])).eval
          (g.map (Int.castRingHom ℤ_[p]) *ᵥ (h.val *ᵥ (B.map (Int.castRingHom ℤ_[p]) *ᵥ x))) := (hQgp _).symm
      _ = (Q.map (Int.castRingHom ℤ_[p])).eval ((p : ℤ_[p]) • (U.val *ᵥ x)) := by
          rw [mulVec_mulVec, mulVec_mulVec, hAB, smul_mulVec]
      _ = p * (p * (Q.map (Int.castRingHom ℤ_[p])).eval (U.val *ᵥ x)) := by
          rw [Kneser.eval_smul_gen]; ring
  obtain ⟨P, hP⟩ := wm_exists_pullback Q'' B
  have hdvd : ∀ y, (p : ℤ) ∣ P.eval y := by
    intro y
    rw [hP]
    apply Binary.int_dvd_of_padic_dvd (p := p)
    rw [← wm_eval_map_cast, wm_cast_mulVec, hkey]
    exact dvd_mul_right _ _
  obtain ⟨R, hPR⟩ := wm_exists_eq_smul_of_dvd hp0 hdvd
  have hR : ∀ y, Q''.eval (B *ᵥ y) = (p : ℤ) * R.eval y := fun y => by
    rw [← hP, hPR, Kneser.eval_smul_form]
  have hUiso : ∀ x, (Q.map (Int.castRingHom ℤ_[p])).eval (U.val *ᵥ x) =
      (R.map (Int.castRingHom ℤ_[p])).eval x := fun x => by
    apply mul_left_cancel₀ hpp0
    rw [← hkey, wm_eval_map_of_eq_smul _ (p : ℤ) hR, hφp]
  refine ⟨R, ⟨fun ℓ _ => ?_, ?_⟩, hpp, X, (wm_det_ne_zero_of_mul_eq hBX hp0).2, ?_, fun x => ?_⟩
  · by_cases hℓ : ℓ = p
    · subst hℓ
      exact ⟨U, hUiso⟩
    · have hnd : ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
        intro hdv
        exact hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).mp (Int.natCast_dvd_natCast.mp hdv))
      have hu := Binary.isUnit_intCast_padic (p := ℓ) hnd
      exact wm_isometricGL_of_unit (Int.castRingHom ℤ_[ℓ]) hu.unit (by simp) hgG hBX hQg hR (hg.1 ℓ)
  · exact wm_isometricGL_of_unit (Int.castRingHom ℝ) (Units.mk0 (p : ℝ) (by exact_mod_cast hpp.ne_zero))
      (by simp) hgG hBX hQg hR hg.2
  · have hUX : U.val * X.map (Int.castRingHom ℤ_[p]) = g.map (Int.castRingHom ℤ_[p]) * h.val := by
      apply wm_smul_cancel hpp0
      rw [← Matrix.smul_mul, ← hAB, Matrix.mul_assoc, ← Matrix.map_mul, hBX, wm_map_smul_one, hφp,
        Matrix.mul_smul, Matrix.mul_one]
    ext c
    rw [SetLike.mem_coe, wm_mem_watsonSub_iff R c, wm_padicWatsonCond_iff_of_isometry U hUiso,
      wm_padicWatsonCond_iff hrange hgG]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨h.val *ᵥ (fun i => (x i : ℤ_[p])), by rw [wm_cast_mulVec, mulVec_mulVec, hUX, mulVec_mulVec]⟩
    · rintro ⟨w, hw⟩
      have hBc : B.map (Int.castRingHom ℤ_[p]) *ᵥ (fun i => (c i : ℤ_[p])) =
          (p : ℤ_[p]) • ((h⁻¹).val *ᵥ w) := by
        rw [hBU, ← mulVec_mulVec, hw, mulVec_mulVec, Matrix.mul_assoc, hGgp, Matrix.mul_smul, Matrix.mul_one,
          smul_mulVec]
      have hdiv : ∀ i, (p : ℤ) ∣ (B *ᵥ c) i := fun i => by
        apply Binary.int_dvd_of_padic_dvd (p := p)
        have := congrFun hBc i
        rw [← wm_cast_mulVec] at this
        rw [show (((B *ᵥ c) i : ℤ) : ℤ_[p]) = _ from this, Pi.smul_apply, smul_eq_mul]
        exact dvd_mul_right _ _
      choose z hz using hdiv
      have hBz : B *ᵥ c = (p : ℤ) • z := funext fun i => by simp [hz i]
      refine ⟨z, smul_right_injective (Fin n → ℤ) hp0 ?_⟩
      show (p : ℤ) • (X *ᵥ z) = (p : ℤ) • c
      rw [← mulVec_smul, ← hBz, mulVec_mulVec, hXB, smul_mulVec, one_mulVec]
  · apply mul_left_cancel₀ hp0
    rw [← hR, mulVec_mulVec, hBX, smul_mulVec, one_mulVec, Kneser.eval_smul_gen]
    ring

/-! ### Watson's operation does not increase the number of classes -/

/-- **Cassels, App. A, §3, p. 365: the genus of a derived form has at most as many classes.** If $Q'$ is derived
from $Q$ at the prime $p$ (`IsWatsonDerived`), then the genus of $Q'$ has at most as many classes as the genus of $Q$.
*Proof:* every class in the genus of $Q'$ is the derived class of a class in the genus of $Q$
(`exists_watsonDerived_of_sameGenus`), and the derived class is determined by the class
(`intEquiv_of_isWatsonDerived`), so choosing such a class gives an injection of the classes of the genus of $Q'$ into
those of the genus of $Q$. No definiteness is needed. Argument: `hd` the derived-form relation. -/
theorem encard_genusClasses_le_of_isWatsonDerived {Q Q' : QuadForm ℤ n} {p : ℕ} (hd : IsWatsonDerived Q p Q') :
    (genusClasses Q').encard ≤ (genusClasses Q).encard := by
  classical
  let F : QClass n → QClass n := fun c =>
    if hc : ∃ R S : QuadForm ℤ n, SameGenus Q R ∧ IsWatsonDerived R p S ∧ classOf S = c then
      classOf hc.choose else c
  have hF : ∀ c ∈ genusClasses Q', ∃ R S : QuadForm ℤ n,
      SameGenus Q R ∧ IsWatsonDerived R p S ∧ classOf S = c ∧ F c = classOf R := by
    intro c hc
    obtain ⟨Q'', hcQ, hgQ⟩ := hc
    have hex : ∃ R S : QuadForm ℤ n, SameGenus Q R ∧ IsWatsonDerived R p S ∧ classOf S = c := by
      obtain ⟨R, hR1, hR2⟩ := exists_watsonDerived_of_sameGenus hd hgQ
      exact ⟨R, Q'', hR1, hR2, hcQ⟩
    obtain ⟨S, h1, h2, h3⟩ := hex.choose_spec
    exact ⟨hex.choose, S, h1, h2, h3, dite_eq_left_of_eq_true (eq_true hex)⟩
  refine Set.encard_le_encard_of_injOn (f := F) ?_ ?_
  · intro c hc
    obtain ⟨R, S, h1, -, -, hFc⟩ := hF c hc
    rw [hFc]
    exact classOf_mem_genusClasses_iff.mpr h1
  · intro c₁ hc₁ c₂ hc₂ heq
    obtain ⟨R₁, S₁, -, h₁, rfl, hF₁⟩ := hF c₁ hc₁
    obtain ⟨R₂, S₂, -, h₂, rfl, hF₂⟩ := hF c₂ hc₂
    rw [hF₁, hF₂] at heq
    exact classOf_eq_classOf_iff.mpr (intEquiv_of_isWatsonDerived h₁ h₂ (classOf_eq_classOf_iff.mp heq))

/-- **Cassels, App. A, §3, p. 365: Watson's operation does not increase the number of classes** (proved; the named
statement `WatsonOperationMonotone` of `Watson.lean`). For every positive definite $Q$ in $n$ variables, every prime
$p$ and every form $Q'$ derived from $Q$ at $p$, the genus of $Q'$ has at most as many classes as the genus of $Q$
(`encard_genusClasses_le_of_isWatsonDerived`, which does not use definiteness). -/
@[kb "cassels1978" "App. A, §3, p. 365 (Watson's operation does not increase the number of classes)"]
theorem watsonOperationMonotone_holds : WatsonOperationMonotone :=
  ⟨fun _ _ _ _ _ hd => encard_genusClasses_le_of_isWatsonDerived hd⟩

/-- **Cassels, App. A, Theorem 3.1 ($c(n) \to \infty$), conditional on the local study only:** with Watson's
monotonicity now proved (`watsonOperationMonotone_holds`), the one remaining named input of Cassels' sketch is
`WatsonLocalStudy` (repeated Watson operations reach a genus containing $r\Gamma_8 \perp \Lambda'$ with
$16r \ge n - 6$). Argument: `hB` the named input. -/
@[kb "cassels1978" "App. A, §3, Thm. 3.1, pp. 364-366 (conditional on the local study, Ch. 8, Ex. 8)"]
theorem watson_of_localStudy (hB : WatsonLocalStudy) : WatsonStatement :=
  watson_of_inputs watsonOperationMonotone_holds hB

end QuadFormsKB.DefiniteForms
