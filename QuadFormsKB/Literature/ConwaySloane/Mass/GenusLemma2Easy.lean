/-
# Conway–Sloane 1988, §11, Lemma 2 ("only if"): lattices in the same genus have isomorphic discriminant forms

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11 "Properties of the genus", Lemma 2, p. 280. The paper states Lemma 2 without proof. This file
proves the **"only if" half** unconditionally; the "if" half (Kneser–Puppe) becomes the smaller named statement
`Lemma2IfStatement`, from which `Lemma2Statement` (`GenusLemmas.lean`) and Lemma 4 follow.

**Statement.** Let $A, B \in M_n(\mathbb Z)$ be Gram matrices of lattices $L, M$ (symmetric, $\det \ne 0$; in the headline theorems
positive definite, `PosDefGram`). If `Siegel.SameGenus (ofMatrixZ A) (ofMatrixZ B)` ($x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are
$\mathrm{GL}_n(\mathbb Z_p)$-equivalent for every prime $p$, and over $\mathbb R$), then there is an additive isomorphism
$\varphi : \mathbb Z^n/A\mathbb Z^n \to \mathbb Z^n/B\mathbb Z^n$ (that is, $L^*/L \cong M^*/M$) with
$z^{\mathsf T}B^{-1}z - y^{\mathsf T}A^{-1}y \in T\mathbb Z$ whenever $\varphi[y] = [z]$, where $T \in \{1, 2\}$ is the common type
(`gramType`). This is `DiscIso (gramType A) A B`.

**Proof (elementary: local data plus the Chinese remainder theorem).**
1. *Local to modular.* From $g_p \in \mathrm{GL}_n(\mathbb Z_p)$ with $Q_A(g_p x) = Q_B(x)$ we get, by polarization (valid at
   $p = 2$ too, since $\mathbb Z_p$ is a domain of characteristic $0$), $g_p^{\mathsf T} A g_p = B$ (`gram_of_isometricGL`); reduce
   modulo $p^k$ (`local_mod`).
2. *Chinese remainder.* Let $S$ be the primes dividing $2\det A\det B$ and $k = 2|\det A||\det B|$. Choose entrywise
   (`exists_crt_matrix`) an integer matrix $U$ with $U \equiv g_p \pmod{p^k}$ for all $p \in S$. Then for $p \in S$:
   $p \nmid \det U$ and $U^{\mathsf T}AU - B = p^k E_p$ (`Good`, `exists_good`).
3. *The map.* $\varphi[y] = [U^{\mathsf T}y]$. Everything is a divisibility statement in $\mathbb Z$ checked prime by prime
   (`dvd_of_forall_prime_pow`), using $\operatorname{adj}$ identities (no inverses): well defined (`good_well`, from
   $\det U\cdot\operatorname{adj}(B)U^{\mathsf T}A = \operatorname{adj}(B)(B + p^kE)\operatorname{adj}(U)$), injective (`good_inj`), and
   bijective because the same construction for $(B, A)$ gives an injection back, so the finite groups have equal order.
4. *Norms.* $\det U\cdot\bigl(\det A\,z^{\mathsf T}\operatorname{adj}(B)z - \det B\,y^{\mathsf T}\operatorname{adj}(A)y\bigr)$ equals
   $y^{\mathsf T}U\operatorname{adj}(B)\,p^kE\,\operatorname{adj}(U)\operatorname{adj}(A)y$ for $z = U^{\mathsf T}y$ (`norm_identity`), which gives
   divisibility by $\det A\det B\,T$ (`good_norm`). The remaining freedom $z \mapsto z + Bw$ changes the norm by $T\mathbb Z$
   (`dualNorm_congr_one`, `dualNorm_congr_even`).

**Proves**
* `Lemma2Easy.discIso_of_sameGenus_symm`: the statement above for symmetric $A$, $B$ with $\det \ne 0$ (no definiteness needed;
  $|\det A| = |\det B|$ is *derived*, not assumed).
* `discIso_of_sameGenus`: the "only if" half of Lemma 2 for positive definite lattices, as an isomorphism of discriminant forms
  mod the type $T$.
* `lemma2_only_if`: same genus implies the same type and `DiscIso (gramType A) A B` (with `gramType_eq_of_sameGenus`).

* `Lemma2IfStatement` (**named statement**, the "if" half), `lemma2Statement_of_if`, `lemma4_of_lemma2If`: Lemmas 2 and 4
  conditional on the "if" half only.

**Inputs:** none for the "only if" half (standard axioms only).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmas
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma3

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity

namespace QuadFormsKB.ConwaySloane.Mass

namespace Lemma2Easy

variable {n : ℕ}

/-! ### Divisibility criteria in $\mathbb Z$ -/

/-- **Local-global divisibility criterion**: for $\delta \ne 0$, $\delta \mid x$ as soon as $p^{v_p(\delta)} \mid x$ for every
prime $p$ ($v_p(\delta)$ = `δ.natAbs.factorization p`). -/
theorem dvd_of_forall_prime_pow {δ x : ℤ} (hδ : δ ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ^ (δ.natAbs.factorization p) ∣ x) : δ ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  have hδ' : δ.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hδ
  have hx' : x.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hx
  rw [← Int.natAbs_dvd_natAbs]
  refine (Nat.factorization_le_iff_dvd hδ' hx').1 fun p => ?_
  by_cases hp : p.Prime
  · have h1 := h p hp
    have h2 : p ^ (δ.natAbs.factorization p) ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 h1
      simpa [Int.natAbs_pow] using this
    exact (hp.pow_dvd_iff_le_factorization hx').1 h2
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- $p^{v_p(\delta)} \mid \delta$. -/
theorem pow_fact_dvd (δ : ℤ) (p : ℕ) : (p : ℤ) ^ (δ.natAbs.factorization p) ∣ δ := by
  rw [← Int.natAbs_dvd_natAbs]
  simpa [Int.natAbs_pow] using Nat.ordProj_dvd δ.natAbs p

/-- $v_p(\delta) \le |\delta| \le k$ for $\delta \ne 0$. -/
theorem fact_le {δ : ℤ} (hδ : δ ≠ 0) {k : ℕ} (hk : δ.natAbs ≤ k) (p : ℕ) :
    δ.natAbs.factorization p ≤ k :=
  (Nat.factorization_lt p (Int.natAbs_ne_zero.2 hδ)).le.trans hk

/-! ### The congruence data `Good` -/

/-- **Good approximating matrix.** An integer matrix $U$ is *good* for $(A, B)$ at the exponent $k$ if for every prime
$p \mid 2\det A\det B$: $p \nmid \det U$ and $U^{\mathsf T}AU - B = p^k E$ for some integer matrix $E$ (that is,
$U^{\mathsf T}AU \equiv B \pmod{p^k}$ entrywise). Here $A, B, U \in M_n(\mathbb Z)$ and $k \in \mathbb N$. -/
def Good (A B U : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * (A.det * B.det) →
    ¬ (p : ℤ) ∣ U.det ∧ ∃ E : Matrix (Fin n) (Fin n) ℤ, Uᵀ * A * U - B = ((p : ℤ) ^ k) • E

/-- **Using `Good`**: to show $\delta \mid x$ (with $\delta \mid 2\det A\det B$, $|\delta| \le k$) it suffices to show, for each prime
$p$ and each $E$ with $U^{\mathsf T}AU - B = p^kE$, that $p^{v_p(\delta)} \mid \det U \cdot x$. (For primes not dividing
$2\det A\det B$ the factor $p^{v_p(\delta)}$ is $1$; for the others $p \nmid \det U$ is cancelled.) -/
theorem dvd_of_good {A B U : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} (hG : Good A B U k) {δ x : ℤ}
    (hδ : δ ≠ 0) (hδk : δ.natAbs ≤ k) (hδd : δ ∣ 2 * (A.det * B.det))
    (h : ∀ p : ℕ, p.Prime → ∀ E : Matrix (Fin n) (Fin n) ℤ, Uᵀ * A * U - B = ((p : ℤ) ^ k) • E →
      δ.natAbs.factorization p ≤ k → (p : ℤ) ^ (δ.natAbs.factorization p) ∣ U.det * x) : δ ∣ x := by
  refine dvd_of_forall_prime_pow hδ fun p hp => ?_
  by_cases hd : (p : ℤ) ∣ 2 * (A.det * B.det)
  · obtain ⟨hU, E, hE⟩ := hG p hp hd
    exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left _ hU (h p hp E hE (fact_le hδ hδk p))
  · have hnd : ¬ p ∣ δ.natAbs := fun h' => hd ((Int.natCast_dvd.2 h').trans hδd)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]; simp

/-! ### Matrix identities (adjugates instead of inverses) -/

/-- If $U^{\mathsf T}AU = B + cE$ then $\det U\cdot \operatorname{adj}(B)U^{\mathsf T}A = \det B\cdot\operatorname{adj}(U) +
c\,\operatorname{adj}(B)E\operatorname{adj}(U)$. -/
theorem well_identity {A B U E : Matrix (Fin n) (Fin n) ℤ} {c : ℤ} (hE : Uᵀ * A * U - B = c • E) :
    U.det • (B.adjugate * Uᵀ * A) = B.det • U.adjugate + c • (B.adjugate * E * U.adjugate) := by
  have hB : Uᵀ * A * U = B + c • E := sub_eq_iff_eq_add'.1 hE
  have e : B.adjugate * (Uᵀ * A * U) * U.adjugate = U.det • (B.adjugate * Uᵀ * A) := by
    calc B.adjugate * (Uᵀ * A * U) * U.adjugate
        = B.adjugate * Uᵀ * A * (U * U.adjugate) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [← e, hB, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.adjugate_mul,
    Matrix.smul_mul, Matrix.one_mul]

/-- If $U^{\mathsf T}AU - B = cE$ then $\operatorname{adj}(A)\operatorname{adj}(U)^{\mathsf T}B = \det U\det A\cdot U -
c\,\operatorname{adj}(A)\operatorname{adj}(U)^{\mathsf T}E$. -/
theorem inj_identity {A B U E : Matrix (Fin n) (Fin n) ℤ} {c : ℤ} (hE : Uᵀ * A * U - B = c • E) :
    A.adjugate * (U.adjugateᵀ * B) = (U.det * A.det) • U - c • (A.adjugate * U.adjugateᵀ * E) := by
  have hB : B = Uᵀ * A * U - c • E := by rw [← hE]; abel
  have h1 : U.adjugateᵀ * Uᵀ = U.det • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    rw [← Matrix.transpose_mul, Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one]
  have h2 : U.adjugateᵀ * (Uᵀ * A * U) = U.det • (A * U) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hB, Matrix.mul_sub, h2, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, smul_smul]

/-- **Well definedness of $[y] \mapsto [U^{\mathsf T}y]$**: for good $U$ (with $|\det B| \le k$), $U^{\mathsf T}A\mathbb Z^n
\subseteq B\mathbb Z^n$, i.e. $B^{-1}U^{\mathsf T}Az$ is integral for each $z \in \mathbb Z^n$. -/
theorem good_well {A B U : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} (hG : Good A B U k) (hdB : B.det ≠ 0)
    (hk : B.det.natAbs ≤ k) (z : Fin n → ℤ) : ∃ w, B *ᵥ w = Uᵀ *ᵥ (A *ᵥ z) := by
  have hM : (B.adjugate * Uᵀ * A) *ᵥ z = B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hv : ∀ i, B.det ∣ (B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z))) i := by
    intro i
    refine dvd_of_good hG hdB hk ⟨2 * A.det, by ring⟩ fun p hp E hE hv => ?_
    have hid := congrArg (fun M => (M *ᵥ z) i) (well_identity hE)
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hM] at hid
    rw [hid]
    refine dvd_add (Dvd.dvd.mul_right (pow_fact_dvd _ _) _) ?_
    exact (pow_dvd_pow _ hv).trans (Dvd.intro _ rfl)
  refine ⟨fun i => (B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z))) i / B.det, ?_⟩
  have h1 : B.det • (fun i => (B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z))) i / B.det) = B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hv i)
  have h2 : B.det • (B *ᵥ fun i => (B.adjugate *ᵥ (Uᵀ *ᵥ (A *ᵥ z))) i / B.det) = B.det • (Uᵀ *ᵥ (A *ᵥ z)) := by
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hdB this

/-- **Injectivity of $[y] \mapsto [U^{\mathsf T}y]$**: for good $U$ (with $|\det A| \le k$), if $U^{\mathsf T}y = Bw$ with
$w \in \mathbb Z^n$ then $y \in A\mathbb Z^n$, i.e. $A^{-1}y$ is integral. -/
theorem good_inj {A B U : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} (hG : Good A B U k) (hdA : A.det ≠ 0)
    (hk : A.det.natAbs ≤ k) {y w : Fin n → ℤ} (h : Uᵀ *ᵥ y = B *ᵥ w) : ∃ z, A *ᵥ z = y := by
  have hv : ∀ i, A.det ∣ (A.adjugate *ᵥ y) i := by
    intro i
    refine dvd_of_good hG hdA hk ⟨2 * B.det, by ring⟩ fun p hp E hE hv => ?_
    have h1 : U.det • y = U.adjugateᵀ *ᵥ (B *ᵥ w) := by
      rw [← h, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_adjugate, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : U.det • (A.adjugate *ᵥ y) = (A.adjugate * (U.adjugateᵀ * B)) *ᵥ w := by
      rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [inj_identity hE] at h2
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.smul_mulVec, Pi.sub_apply] at h3
    rw [h3]
    refine dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_fact_dvd _ _) _) _) ?_
    exact (pow_dvd_pow _ hv).trans (Dvd.intro _ rfl)
  refine ⟨fun i => (A.adjugate *ᵥ y) i / A.det, ?_⟩
  have h1 : A.det • (fun i => (A.adjugate *ᵥ y) i / A.det) = A.adjugate *ᵥ y := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hv i)
  have h2 : A.det • (A *ᵥ fun i => (A.adjugate *ᵥ y) i / A.det) = A.det • y := by
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hdA this

/-! ### Norms -/

/-- **The norm via the adjugate**: $y^{\mathsf T}A^{-1}y = y^{\mathsf T}\operatorname{adj}(A)y / \det A$ (`dualNorm`). -/
theorem dualNorm_eq {A : Matrix (Fin n) (Fin n) ℤ} (y : Fin n → ℤ) :
    dualNorm A y = ((y ⬝ᵥ (A.adjugate *ᵥ y) : ℤ) : ℚ) / A.det := by
  have hdet : (gramQ A).det = (A.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) A
    simpa [gramQ] using this.symm
  have hadj : (gramQ A).adjugate = A.adjugate.map (Int.castRingHom ℚ) :=
    (RingHom.map_adjugate (Int.castRingHom ℚ) A).symm
  unfold dualNorm
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, hadj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    div_eq_inv_mul]
  congr 1
  simp [dotProduct, mulVec]

/-- If $U^{\mathsf T}AU - B = cE$ then
$U\operatorname{adj}(B)\,(cE)\,\operatorname{adj}(U)\operatorname{adj}(A) = \det U\det A\cdot U\operatorname{adj}(B)U^{\mathsf T}
- \det B\det U\cdot\operatorname{adj}(A)$. -/
theorem norm_identity {A B U E : Matrix (Fin n) (Fin n) ℤ} {c : ℤ} (hE : Uᵀ * A * U - B = c • E) :
    U * B.adjugate * (c • E) * U.adjugate * A.adjugate
      = (U.det * A.det) • (U * B.adjugate * Uᵀ) - (B.det * U.det) • A.adjugate := by
  have e1 : U * B.adjugate * (Uᵀ * A * U) * U.adjugate * A.adjugate
      = (U.det * A.det) • (U * B.adjugate * Uᵀ) := by
    calc U * B.adjugate * (Uᵀ * A * U) * U.adjugate * A.adjugate
        = U * B.adjugate * Uᵀ * A * (U * U.adjugate) * A.adjugate := by simp only [Matrix.mul_assoc]
      _ = U.det • (U * B.adjugate * Uᵀ * (A * A.adjugate)) := by
        rw [Matrix.mul_adjugate]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_adjugate (A := A), Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have e2 : U * B.adjugate * B * U.adjugate * A.adjugate = (B.det * U.det) • A.adjugate := by
    calc U * B.adjugate * B * U.adjugate * A.adjugate
        = U * (B.adjugate * B) * U.adjugate * A.adjugate := by simp only [Matrix.mul_assoc]
      _ = B.det • (U * U.adjugate) * A.adjugate := by
        rw [Matrix.adjugate_mul]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_adjugate (A := U), Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  rw [← hE, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, e1, e2]

/-- $(U^{\mathsf T}y)^{\mathsf T}M(U^{\mathsf T}y) = y^{\mathsf T}(UMU^{\mathsf T})y$. -/
theorem dot_conj_identity (U M : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) :
    (Uᵀ *ᵥ y) ⬝ᵥ (M *ᵥ (Uᵀ *ᵥ y)) = y ⬝ᵥ ((U * M * Uᵀ) *ᵥ y) := by
  have h : (U * M * Uᵀ) *ᵥ y = U *ᵥ (M *ᵥ (Uᵀ *ᵥ y)) := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [h, Matrix.dotProduct_mulVec y U (M *ᵥ Uᵀ *ᵥ y)]
  simp only [Matrix.mulVec_transpose]

/-- **The map $[y] \mapsto [U^{\mathsf T}y]$ preserves norms mod $T$** ($T \in \{1, 2\}$, $k \ge 2|\det A||\det B|$): there is
$m \in \mathbb Z$ with $(U^{\mathsf T}y)^{\mathsf T}B^{-1}(U^{\mathsf T}y) = y^{\mathsf T}A^{-1}y + Tm$. -/
theorem good_norm {A B U : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} (hG : Good A B U k) (hdA : A.det ≠ 0)
    (hdB : B.det ≠ 0) (hk : A.det.natAbs * B.det.natAbs * 2 ≤ k) {T : ℕ} (hT : T = 1 ∨ T = 2)
    (y : Fin n → ℤ) : ∃ m : ℤ, dualNorm B (Uᵀ *ᵥ y) = dualNorm A y + (T : ℕ) * m := by
  set a : ℤ := (Uᵀ *ᵥ y) ⬝ᵥ (B.adjugate *ᵥ (Uᵀ *ᵥ y)) with ha
  set b : ℤ := y ⬝ᵥ (A.adjugate *ᵥ y) with hb
  have hT0 : (T : ℤ) ≠ 0 := by rcases hT with rfl | rfl <;> norm_num
  have hδ : A.det * B.det * T ≠ 0 := mul_ne_zero (mul_ne_zero hdA hdB) hT0
  have hδk : (A.det * B.det * T).natAbs ≤ k := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    refine le_trans ?_ hk
    rcases hT with rfl | rfl <;> omega
  have hδd : A.det * B.det * T ∣ 2 * (A.det * B.det) := by
    rcases hT with rfl | rfl
    · exact ⟨2, by push_cast; ring⟩
    · exact ⟨1, by push_cast; ring⟩
  have hZ : A.det * B.det * T ∣ A.det * a - B.det * b := by
    refine dvd_of_good hG hδ hδk hδd fun p hp E hE hv => ?_
    have hid := norm_identity hE
    have h1 := congrArg (fun M => y ⬝ᵥ (M *ᵥ y)) hid
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      ← dot_conj_identity] at h1
    have h2 : U.det * (A.det * a - B.det * b)
        = y ⬝ᵥ ((U * B.adjugate * (((p : ℤ) ^ k) • E) * U.adjugate * A.adjugate) *ᵥ y) := by
      rw [h1, ha, hb]; ring
    rw [h2]
    refine (pow_dvd_pow _ hv).trans ?_
    have h3 : U * B.adjugate * (((p : ℤ) ^ k) • E) * U.adjugate * A.adjugate
        = ((p : ℤ) ^ k) • (U * B.adjugate * E * U.adjugate * A.adjugate) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [h3, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact Dvd.intro _ rfl
  obtain ⟨m, hm⟩ := hZ
  refine ⟨m, ?_⟩
  rw [dualNorm_eq, dualNorm_eq]
  have hq : (A.det : ℚ) * a - B.det * b = A.det * B.det * T * m := by exact_mod_cast hm
  have hA' : (A.det : ℚ) ≠ 0 := by exact_mod_cast hdA
  have hB' : (B.det : ℚ) ≠ 0 := by exact_mod_cast hdB
  field_simp
  linear_combination hq

/-! ### Local data and the Chinese remainder theorem -/

/-- The Hessian of $x^{\mathsf T}Ax$ over a ring $R$ (base change along $f : \mathbb Z \to R$) is $A + A$ for symmetric $A$. -/
theorem hessian_map_ofMatrixZ {R : Type*} [CommRing R] (f : ℤ →+* R) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Aᵀ = A) : ((ofMatrixZ A).map f).hessian = A.map f + A.map f := by
  have h1 : ((ofMatrixZ A).map f).hessian = (ofMatrixZ A).hessian.map f := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.map_add _ (map_add f), Matrix.transpose_map]
  rw [h1, hessian_ofMatrixZ, hA, Matrix.map_add _ (map_add f)]

/-- **From equivalence of forms to congruence of Gram matrices** over a domain $R$ of characteristic $0$ (e.g. $\mathbb Z_p$,
including $p = 2$): if $x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ ($A, B$ symmetric integral) are $\mathrm{GL}_n(R)$-equivalent
then $g^{\mathsf T}Ag = B$ for some $g$ with $\det g$ a unit (polarization, then cancel $2$). -/
theorem gram_of_isometricGL {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (f : ℤ →+* R)
    {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : IsometricGL ((ofMatrixZ A).map f) ((ofMatrixZ B).map f)) :
    ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧ gᵀ * A.map f * g = B.map f := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, ?_⟩
  have polar : ∀ (P : QuadForm R n) (x y : Fin n → R),
      P.eval (x + y) - P.eval x - P.eval y = x ⬝ᵥ (P.hessian *ᵥ y) := by
    intro P x y
    have := QuadForm.polar_eq_hessian R P x y
    simpa using this
  have key : ∀ a b : Fin n → R, a ⬝ᵥ (((g.val)ᵀ * (A.map f + A.map f) * g.val) *ᵥ b)
      = a ⬝ᵥ ((B.map f + B.map f) *ᵥ b) := by
    intro a b
    have e1 : a ⬝ᵥ (((g.val)ᵀ * (A.map f + A.map f) * g.val) *ᵥ b)
        = (g.val *ᵥ a) ⬝ᵥ ((A.map f + A.map f) *ᵥ (g.val *ᵥ b)) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec a (g.val)ᵀ, vecMul_transpose]
    rw [e1, ← hessian_map_ofMatrixZ f A hA, ← hessian_map_ofMatrixZ f B hB, ← polar, ← polar]
    have : g.val *ᵥ (a + b) = g.val *ᵥ a + g.val *ᵥ b := mulVec_add _ _ _
    rw [← this]
    simp only [hg]
  have hM : (g.val)ᵀ * (A.map f + A.map f) * g.val = B.map f + B.map f := by
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, dotProduct_single] using this
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  ext i j
  have := congrFun (congrFun hM i) j
  rw [Matrix.mul_add, Matrix.add_mul] at this
  simp only [Matrix.add_apply] at this
  have h3 : (2 : R) * ((g.val)ᵀ * A.map f * g.val) i j = 2 * (B.map f) i j := by
    linear_combination this
  exact mul_left_cancel₀ h2 h3

/-- **The genus condition at $p$, modulo $p^k$**: if $x^{\mathsf T}Ax \sim x^{\mathsf T}Bx$ over $\mathbb Z_p$ then there is
$V \in M_n(\mathbb Z/p^k)$ with $\det V$ a unit and $V^{\mathsf T}AV = B$ in $\mathbb Z/p^k$. -/
theorem local_mod {p : ℕ} [Fact p.Prime] (k : ℕ) {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A)
    (hB : Bᵀ = B)
    (h : IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℤ_[p])) ((ofMatrixZ B).map (Int.castRingHom ℤ_[p]))) :
    ∃ V : Matrix (Fin n) (Fin n) (ZMod (p ^ k)),
      Vᵀ * A.map (Int.castRingHom (ZMod (p ^ k))) * V = B.map (Int.castRingHom (ZMod (p ^ k))) ∧
        IsUnit V.det := by
  obtain ⟨g, hu, hg⟩ := gram_of_isometricGL _ hA hB h
  refine ⟨g.map (PadicInt.toZModPow k), ?_, ?_⟩
  · have := congrArg (RingHom.mapMatrix (PadicInt.toZModPow (p := p) k)) hg
    simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map, Matrix.map_map] at this
    have e : (PadicInt.toZModPow (p := p) k).comp (Int.castRingHom ℤ_[p]) = Int.castRingHom _ :=
      RingHom.ext_int _ _
    have e2 : ∀ M : Matrix (Fin n) (Fin n) ℤ,
        M.map ((PadicInt.toZModPow (p := p) k) ∘ (Int.castRingHom ℤ_[p]))
          = M.map (Int.castRingHom (ZMod (p ^ k))) := by
      intro M
      rw [← e]; rfl
    rw [e2, e2] at this
    exact this
  · have := hu.map (PadicInt.toZModPow (p := p) k)
    rwa [RingHom.map_det] at this

/-- **Chinese remainder theorem for matrices**: given, for each prime $p$ in a finite set $S$, a matrix $V_p$ over $\mathbb Z/p^k$,
there is an integer matrix $U$ with $U \equiv V_p \pmod{p^k}$ for all $p \in S$ (entrywise `Nat.chineseRemainderOfFinset`). -/
theorem exists_crt_matrix (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (V : ∀ p : ℕ, Matrix (Fin n) (Fin n) (ZMod (p ^ k))) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, ∀ p ∈ S, U.map (Int.castRingHom (ZMod (p ^ k))) = V p := by
  have hs : ∀ p ∈ S, p ^ k ≠ 0 := fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  have pp : Set.Pairwise (↑S : Set ℕ) (Function.onFun Nat.Coprime fun p => p ^ k) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow k k ((Nat.coprime_primes (hS p hp) (hS q hq)).2 hpq)
  have ent : ∀ i j : Fin n, ∃ z : ℤ, ∀ p ∈ S, (z : ZMod (p ^ k)) = V p i j := by
    intro i j
    obtain ⟨z, hz⟩ := Nat.chineseRemainderOfFinset (fun p => (V p i j).val) (fun p => p ^ k) S hs pp
    refine ⟨z, fun p hp => ?_⟩
    have : NeZero (p ^ k) := ⟨hs p hp⟩
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hz p hp)
    simpa using this
  choose z hz using ent
  refine ⟨Matrix.of z, fun p hp => ?_⟩
  ext i j
  simpa using hz i j p hp

/-- **A good matrix exists** for lattices in the same genus: if `SameGenus (ofMatrixZ A) (ofMatrixZ B)`, with $A, B$ symmetric
of nonzero determinant and $k \ge 2|\det A||\det B|$, there is an integer matrix $U$ that is `Good A B U k`. -/
theorem exists_good {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B) (hdA : A.det ≠ 0)
    (hdB : B.det ≠ 0) (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) {k : ℕ}
    (hk : A.det.natAbs * B.det.natAbs * 2 ≤ k) : ∃ U : Matrix (Fin n) (Fin n) ℤ, Good A B U k := by
  have hpos : 0 < A.det.natAbs * B.det.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hdA) (Int.natAbs_pos.2 hdB)
  have hk1 : 1 ≤ k := by omega
  have loc : ∀ p : ℕ, ∃ V : Matrix (Fin n) (Fin n) (ZMod (p ^ k)), p.Prime →
      (Vᵀ * A.map (Int.castRingHom (ZMod (p ^ k))) * V = B.map (Int.castRingHom (ZMod (p ^ k))) ∧
        IsUnit V.det) := by
    intro p
    by_cases hp : p.Prime
    · have := Fact.mk hp
      obtain ⟨V, hV⟩ := local_mod k hsA hsB (h.1 p)
      exact ⟨V, fun _ => hV⟩
    · exact ⟨0, fun h' => absurd h' hp⟩
  choose V hV using loc
  have hne : (2 * (A.det * B.det)).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 (mul_ne_zero two_ne_zero (mul_ne_zero hdA hdB))
  obtain ⟨U, hU⟩ := exists_crt_matrix k (2 * (A.det * B.det)).natAbs.primeFactors
    (fun p hp => (Nat.mem_primeFactors.1 hp).1) V
  refine ⟨U, fun p hp hd => ?_⟩
  have hpS : p ∈ (2 * (A.det * B.det)).natAbs.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hd, hne⟩
  have hUp := hU p hpS
  obtain ⟨hEq, hunit⟩ := hV p hp
  have := Fact.mk hp
  have hdet : Int.castRingHom (ZMod (p ^ k)) U.det = (V p).det := by
    rw [RingHom.map_det]
    show (U.map (Int.castRingHom (ZMod (p ^ k)))).det = _
    rw [hUp]
  constructor
  · intro hdv
    have h1 : IsUnit (((U.det : ℤ) : ZMod (p ^ k))) := by
      have : IsUnit (Int.castRingHom (ZMod (p ^ k)) U.det) := hdet ▸ hunit
      simpa using this
    have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have h2 := h1.map (ZMod.castHom hpk (ZMod p))
    rw [map_intCast] at h2
    have h3 : ((U.det : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdv
    rw [h3] at h2
    exact not_isUnit_zero h2
  · set E0 := Uᵀ * A * U - B with hE0
    have h0 : (RingHom.mapMatrix (Int.castRingHom (ZMod (p ^ k)))) E0 = 0 := by
      simp only [hE0, map_sub, map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map, hUp]
      rw [hEq, sub_self]
    have hdvd : ∀ i j, ((p : ℤ) ^ k) ∣ E0 i j := by
      intro i j
      have := congrFun (congrFun h0 i) j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, eq_intCast] at this
      have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).1 this
      simpa using h4
    refine ⟨Matrix.of fun i j => E0 i j / ((p : ℤ) ^ k), ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i j)).symm

/-! ### The map on discriminant groups -/

/-- **The homomorphism $\mathbb Z^n/A\mathbb Z^n \to \mathbb Z^n/B\mathbb Z^n$, $[y] \mapsto [U^{\mathsf T}y]$**, given the proof `hW`
that $U^{\mathsf T}A\mathbb Z^n \subseteq B\mathbb Z^n$. -/
noncomputable def discMap (A B U : Matrix (Fin n) (Fin n) ℤ)
    (hW : ∀ z, ∃ w, B *ᵥ w = Uᵀ *ᵥ (A *ᵥ z)) : DiscGroup A →+ DiscGroup B :=
  QuotientAddGroup.map _ _ (Uᵀ.mulVecLin.toAddMonoidHom) (by
    intro y hy
    obtain ⟨z, rfl⟩ := mem_gramLat.1 hy
    obtain ⟨w, hw⟩ := hW z
    exact mem_gramLat.2 ⟨w, hw⟩)

/-- $\varphi[y] = [U^{\mathsf T}y]$. -/
theorem discMap_mk (A B U : Matrix (Fin n) (Fin n) ℤ) (hW : ∀ z, ∃ w, B *ᵥ w = Uᵀ *ᵥ (A *ᵥ z))
    (y : Fin n → ℤ) : discMap A B U hW (QuotientAddGroup.mk y) = QuotientAddGroup.mk (Uᵀ *ᵥ y) := rfl

/-- The map `discMap` of a good matrix is injective. -/
theorem discMap_injective {A B U : Matrix (Fin n) (Fin n) ℤ} {k : ℕ} (hG : Good A B U k)
    (hdA : A.det ≠ 0) (hdB : B.det ≠ 0) (hkA : A.det.natAbs ≤ k) (hkB : B.det.natAbs ≤ k) :
    Function.Injective (discMap A B U (good_well hG hdB hkB)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using QuotientAddGroup.induction_on with
  | H y =>
    rw [discMap_mk, QuotientAddGroup.eq_zero_iff, mem_gramLat] at hq
    obtain ⟨w, hw⟩ := hq
    obtain ⟨z, hz⟩ := good_inj hG hdA hkA hw.symm
    rw [QuotientAddGroup.eq_zero_iff, mem_gramLat]
    exact ⟨z, hz⟩

/-- $\mathbb Z^n/A\mathbb Z^n$ is finite when $\det A \ne 0$ (`card_discGroup`). -/
theorem finite_discGroup {A : Matrix (Fin n) (Fin n) ℤ} (hd : A.det ≠ 0) : Finite (DiscGroup A) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_discGroup hd]
  exact Int.natAbs_ne_zero.2 hd

/-- **Lemma 2, "only if", for symmetric $A$, $B$ of nonzero determinant**: if $x^{\mathsf T}Ax$ and $x^{\mathsf T}Bx$ are in the
same genus then $L^*/L \cong M^*/M$ by an isomorphism preserving norms mod the type $T$ (`gramType A`). -/
theorem discIso_of_sameGenus_symm {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hdA : A.det ≠ 0) (hdB : B.det ≠ 0) (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) :
    DiscIso (gramType A) A B := by
  have hpos : 0 < A.det.natAbs * B.det.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hdA) (Int.natAbs_pos.2 hdB)
  obtain ⟨k, hk⟩ : ∃ k, k = A.det.natAbs * B.det.natAbs * 2 := ⟨_, rfl⟩
  have hkA : A.det.natAbs ≤ k := by
    have := Int.natAbs_pos.2 hdB
    rw [hk]; nlinarith
  have hkB : B.det.natAbs ≤ k := by
    have := Int.natAbs_pos.2 hdA
    rw [hk]; nlinarith
  obtain ⟨U, hU⟩ := exists_good hsA hsB hdA hdB h hk.symm.le
  obtain ⟨U', hU'⟩ := exists_good hsB hsA hdB hdA h.symm (k := k) (by rw [hk, mul_comm B.det.natAbs])
  have hWA := good_well hU hdB hkB
  have hinj := discMap_injective hU hdA hdB hkA hkB
  have hinj' := discMap_injective hU' hdB hdA hkB hkA
  have := finite_discGroup hdA
  have := finite_discGroup hdB
  have hle : Nat.card (DiscGroup B) ≤ Nat.card (DiscGroup A) :=
    Nat.card_le_card_of_injective _ hinj'
  have hbij : Function.Bijective (discMap A B U hWA) := hinj.bijective_of_nat_card_le hle
  refine ⟨AddEquiv.ofBijective (discMap A B U hWA) hbij, fun y z hyz => ?_⟩
  have h1 : (QuotientAddGroup.mk (Uᵀ *ᵥ y) : DiscGroup B) = QuotientAddGroup.mk z := hyz
  obtain ⟨m, hm⟩ := good_norm hU hdA hdB hk.symm.le (T := gramType A) (gramType_eq_one_or_two A) y
  rcases gramType_eq_one_or_two A with hT | hT
  · obtain ⟨c, hc⟩ := dualNorm_congr_one hsB hdB h1
    refine ⟨m + c, ?_⟩
    rw [hc, hm, hT]; push_cast; ring
  · have hAe : EvenGram A := by
      by_contra hne
      simp [gramType, hne] at hT
    have hBe : EvenGram B := even_of_sameGenus hsA hAe h
    obtain ⟨c, hc⟩ := dualNorm_congr_even hsB hdB hBe h1
    refine ⟨m + c, ?_⟩
    rw [hc, hm, hT]; push_cast; ring

end Lemma2Easy

variable {n : ℕ}

/-- **Conway–Sloane 1988, §11, Lemma 2, "only if"** (p. 280): positive definite lattices $L, M$ with Gram matrices $A$, $B$ in the
same genus have isomorphic discriminant forms: there is an additive isomorphism $\varphi : L^*/L \to M^*/M$
(`DiscGroup A ≃+ DiscGroup B`) such that $z^{\mathsf T}B^{-1}z - y^{\mathsf T}A^{-1}y \in T\mathbb Z$ whenever
$\varphi[y] = [z]$, where $T$ = `gramType A` is the type (1 odd, 2 even; equal for $A$ and $B$ by `gramType_eq_of_sameGenus`).
Unconditional; proved via local congruences and the Chinese remainder theorem (module docstring). -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (only if: same genus gives an isomorphism of discriminant forms)"]
theorem discIso_of_sameGenus {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : DiscIso (gramType A) A B :=
  Lemma2Easy.discIso_of_sameGenus_symm hA.1 hB.1 hA.det_ne hB.det_ne h

/-- **The "only if" half of Conway–Sloane 1988, §11, Lemma 2** (p. 280): positive definite lattices in the same genus (Gram matrices
$A$, $B$) have the same type $T$ and an isomorphism $L^*/L \cong M^*/M$ preserving norms mod $T$. This is the forward direction of
`Lemma2Statement.iff`; it holds unconditionally (the converse is Kneser–Puppe, not proved here). -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (only if: same genus gives same type and an isomorphism of discriminant forms)"]
theorem lemma2_only_if {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : gramType A = gramType B ∧ DiscIso (gramType A) A B :=
  ⟨gramType_eq_of_sameGenus hA.1 hB.1 h, discIso_of_sameGenus hA hB h⟩

/-- **Lemma 2, the "if" half** (§11, p. 280), as a **named statement** (stated without proof in the paper; Kneser–Puppe
1953): positive definite lattices $L$, $M$ of the same dimension and type $T$ with an isomorphism $L^*/L \cong M^*/M$
preserving norms mod $T$ are in the same genus. This is the only unproved part of Lemma 2: the "only if" half is
`lemma2_only_if`. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if: isomorphic discriminant forms give the same genus; stated)"]
structure Lemma2IfStatement : Prop where
  imp : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), PosDefGram A → PosDefGram B →
    gramType A = gramType B → DiscIso (gramType A) A B → SameGenus (ofMatrixZ A) (ofMatrixZ B)

/-- **Lemma 2 from its "if" half** (the "only if" half is proved, `lemma2_only_if`). -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (conditional on the 'if' half)"]
theorem lemma2Statement_of_if (h : Lemma2IfStatement) : Lemma2Statement where
  iff n A B hA hB := ⟨lemma2_only_if hA hB, fun ⟨ht, hi⟩ => h.imp n A B hA hB ht hi⟩

/-- **Lemma 4 from the "if" half of Lemma 2** (with the proved Lemma 3 and the proved "only if" half). -/
@[kb "conwaysloane1988" "§11, Lemma 4, p. 280 (conditional on the 'if' half of Lemma 2)"]
theorem lemma4_of_lemma2If (h : Lemma2IfStatement) : Lemma4Statement :=
  lemma4_of_lemma2 (lemma2Statement_of_if h)

end QuadFormsKB.ConwaySloane.Mass
