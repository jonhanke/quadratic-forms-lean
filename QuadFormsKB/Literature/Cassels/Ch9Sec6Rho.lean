/-
# Cassels, Chapter 9, §6: $\rho$ depends only on the genus of $g$ (6.10), and Lemma 6.2 unconditionally

**Layer:** classically integral forms $f$ in $n = m + 1$ variables and $g$ in $m$ variables (`IsClassicallyIntegral`),
Cassels' matrices $(f_{ij}) = H/2$ (`casselsMat`), the genus `SameGenus` (equivalence over every $\mathbb Z_p$ and over
$\mathbb R$), and the count $\rho(\mathcal F, g)$ of (6.10) (`rhoCount`, `Ch9Sec6Weight.lean`). Indices are 0-based:
the bordered matrix $h(\mathbf c, G)$ (`hMat`) has entries $a$ at $(0,0)$, $c_j$ at $(0, j+1)$ and $(j+1, 0)$, and
$(c_ic_j + G_{ij})/a$ at $(i+1, j+1)$.

**Proves**
* `rhoCount_eq_of_sameGenus` (Cassels (6.10), p. 146): if $g, g'$ are classically integral forms in $m$ variables of one
  genus, then $\rho(\mathcal F, g) = \rho(\mathcal F, g')$ for every $a > 0$ and every $f$;
* `sigmaGenus_eq_rho` (Lemma 6.2, (6.12)): $\sigma(a, \mathcal F, \mathcal G) = \rho(\mathcal F, g)\,W(\mathcal G)$
  with no constancy hypothesis (compare `sigmaGenus_eq`, which assumes it).

*Proof sketch (local; not Cassels' route through Lemma 4.2, Corollary 1 and Lemma 4.3 — Cassels himself remarks that
$\rho$ "can be determined by purely local considerations").* By symmetry of `SameGenus` it suffices to inject the
set counted by $\rho(\mathcal F, g)$ into that for $g'$. For each prime $p$ choose $T_p \in \mathrm{GL}_m(\mathbb Z_p)$
with $T_p^{\mathsf T}GT_p = G'$ ($G = (g_{ij})$, $G' = (g'_{ij})$; `meq_of_isometricGL_casselsMat`) and likewise $T_\infty$
over $\mathbb R$. A bordered-matrix identity (`conj_hMat`): conjugating $h(\mathbf c, G)$ by
$\begin{pmatrix}1 & \mathbf k^{\mathsf T}\\ 0 & T\end{pmatrix}$ gives $h(\mathbf c', G')$ whenever
$\mathbf c' = a\mathbf k + T^{\mathsf T}\mathbf c$ (`meq_hMat`). Given $\mathbf c$ with $h(\mathbf c, G)$ integral in
the genus of $f$, the Chinese remainder theorem (`exists_vec_approx`) produces an integral $\mathbf c'$ with
$\mathbf c' \equiv T_p^{\mathsf T}\mathbf c \pmod{a}$ in $\mathbb Z_p^m$ for every $p$. Then $h(\mathbf c', G')$ is
integral (a local-global divisibility, `int_dvd_of_forall_padic`) and locally equivalent to $h(\mathbf c, G)$ at every
$p$ (by the identity) and at $\infty$ (where $a$ is invertible), hence in the genus of $f$. The class of
$\mathbf c \bmod a$ is sent to that of $\mathbf c'$; this is injective since $T_p$ is invertible over $\mathbb Z_p$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Literature.Cassels.Ch9Sec4Congr

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {m : ℕ}

/-! ### Local-global divisibility and approximation of integers -/

section Arith

variable (p : ℕ) [Fact p.Prime]

/-- For $a > 0$, divisibility by $a$ in $\mathbb Z_p$ is divisibility by the $p$-part $p^{v_p(a)}$. -/
theorem natCast_dvd_iff_ordProj {a : ℕ} (ha : 0 < a) (z : ℤ_[p]) :
    (a : ℤ_[p]) ∣ z ↔ ((p ^ a.factorization p : ℕ) : ℤ_[p]) ∣ z := by
  have hp : p.Prime := Fact.out
  have hu : IsUnit ((a / p ^ a.factorization p : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact Nat.coprime_ordCompl hp ha.ne'
  have h : (a : ℤ_[p]) = ((p ^ a.factorization p : ℕ) : ℤ_[p]) * ((a / p ^ a.factorization p : ℕ) : ℤ_[p]) := by
    rw [← Nat.cast_mul]
    congr 1
    exact (Nat.ordProj_mul_ordCompl_eq_self a p).symm
  rw [h]
  exact hu.mul_right_dvd

/-- Divisibility of an integer by $p^e$ in $\mathbb Z_p$ is divisibility in $\mathbb Z$. -/
theorem intCast_dvd_of_natCast_pow_dvd {e : ℕ} {z : ℤ} (h : ((p ^ e : ℕ) : ℤ_[p]) ∣ (z : ℤ_[p])) :
    ((p ^ e : ℕ) : ℤ) ∣ z := by
  have h1 : (z : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    simpa using h
  rw [RingHom.mem_ker, map_intCast] at h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ e)).mp h1

end Arith

/-- **Local-global divisibility:** an integer divisible by $a$ in every $\mathbb Z_p$ is divisible by $a$. -/
theorem int_dvd_of_forall_padic {a : ℕ} (ha : 0 < a) {z : ℤ}
    (h : ∀ (p : ℕ) [Fact p.Prime], (a : ℤ_[p]) ∣ (z : ℤ_[p])) : (a : ℤ) ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero _
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  rw [← Nat.factorization_le_iff_dvd ha.ne' (Int.natAbs_ne_zero.mpr hz)]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have h1 := (natCast_dvd_iff_ordProj p ha _).mp (h p)
    have h2 := intCast_dvd_of_natCast_pow_dvd p h1
    have h3 : p ^ a.factorization p ∣ z.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h2
      simpa using this
    exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hz)).mp h3
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Approximation:** given $t_p \in \mathbb Z_p$ for each prime $p$, there is an integer $z$ with
$z \equiv t_p \pmod{a}$ in $\mathbb Z_p$ for every $p$. -/
theorem exists_int_approx {a : ℕ} (ha : 0 < a) (t : ∀ (p : ℕ) [Fact p.Prime], ℤ_[p]) :
    ∃ z : ℤ, ∀ (p : ℕ) [Fact p.Prime], ∃ k : ℤ_[p], (z : ℤ_[p]) = t p + a * k := by
  classical
  let S := a.primeFactors
  let I : S → Ideal ℤ := fun p => Ideal.span {((p.1 ^ a.factorization p.1 : ℕ) : ℤ)}
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro p q hpq
    have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hq : q.1.Prime := Nat.prime_of_mem_primeFactors q.2
    have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
    simp only [Function.onFun, I]
    rw [Ideal.isCoprime_span_singleton_iff, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hne)
  let n : S → ℤ := fun p =>
    haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    ((t p.1).appr (a.factorization p.1) : ℤ)
  obtain ⟨z, hz⟩ := Ideal.exists_forall_sub_mem_ideal hI n
  refine ⟨z, fun p _ => ?_⟩
  have hp : p.Prime := Fact.out
  by_cases hpa : p ∈ S
  · have h1 := hz ⟨p, hpa⟩
    simp only [I, Ideal.mem_span_singleton] at h1
    have h2 : ((p ^ a.factorization p : ℕ) : ℤ_[p]) ∣ ((z - n ⟨p, hpa⟩ : ℤ) : ℤ_[p]) := by
      have := map_dvd (Int.castRingHom ℤ_[p]) h1
      simpa using this
    have h3 : ((p ^ a.factorization p : ℕ) : ℤ_[p]) ∣ (t p - ((t p).appr (a.factorization p) : ℤ_[p])) := by
      have := PadicInt.appr_spec (a.factorization p) (t p)
      rw [Ideal.mem_span_singleton] at this
      simpa using this
    have h4 : ((p ^ a.factorization p : ℕ) : ℤ_[p]) ∣ (z : ℤ_[p]) - t p := by
      have h5 := dvd_sub h2 h3
      have e : ((z - n ⟨p, hpa⟩ : ℤ) : ℤ_[p]) - (t p - ((t p).appr (a.factorization p) : ℤ_[p])) =
          (z : ℤ_[p]) - t p := by
        simp [n]
      rwa [e] at h5
    obtain ⟨k, hk⟩ := (natCast_dvd_iff_ordProj p ha _).mpr h4
    exact ⟨k, by rw [← hk]; ring⟩
  · have hu : IsUnit (a : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => hpa ?_
      exact Nat.mem_primeFactors.mpr ⟨hp, hd, ha.ne'⟩
    obtain ⟨u, hu⟩ := hu
    refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((z : ℤ_[p]) - t p), ?_⟩
    rw [← hu]
    calc (z : ℤ_[p]) = t p + (u : ℤ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((z : ℤ_[p]) - t p)) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]; ring
      _ = _ := rfl

/-! ### Bordered matrices over a commutative ring -/

section Bordered

variable {R : Type*} [CommRing R]

/-- The bordered matrix with corner $d$, first row $\mathbf r$, first column $\mathbf s$ and lower right block $Y$
($0$-based: entries $(0,0)$, $(0,j+1)$, $(i+1,0)$, $(i+1,j+1)$). -/
def blkM (d : R) (r s : Fin m → R) (Y : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases d r j) (fun i' => Fin.cases (s i') (fun j' => Y i' j') j) i

/-- Product of two bordered matrices. -/
theorem blkM_mul(d d' : R) (r r' s s' : Fin m → R) (Y Y' : Matrix (Fin m) (Fin m) R) :
    blkM d r s Y * blkM d' r' s' Y' =
      blkM (d * d' + r ⬝ᵥ s') (d • r' + r ᵥ* Y') (d' • s + Y *ᵥ s') (vecMulVec s r' + Y * Y') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blkM, Matrix.mul_apply, Fin.sum_univ_succ, dotProduct, vecMul, mulVec, vecMulVec_apply]
  all_goals ring

/-- Transpose of a bordered matrix swaps the first row and column. -/
theorem blkM_transpose(d : R) (r s : Fin m → R) (Y : Matrix (Fin m) (Fin m) R) :
    (blkM d r s Y)ᵀ = blkM d s r Yᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blkM]

/-- Every square matrix of size $m + 1$ is the bordered matrix of its corner, first row, first column and block. -/
theorem eq_blkM(A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    A = blkM (A 0 0) (fun j => A 0 j.succ) (fun i => A i.succ 0) (A.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blkM]

/-- $\det\begin{pmatrix}1 & \mathbf u^{\mathsf T}\\ 0 & S\end{pmatrix} = \det S$. -/
theorem det_blkM_one(u : Fin m → R) (S : Matrix (Fin m) (Fin m) R) : (blkM 1 u 0 S).det = S.det := by
  have hs : (blkM 1 u 0 S).submatrix Fin.succ Fin.succ = S := by ext i j; simp [blkM]
  have h0 : ∀ i : Fin m, (blkM 1 u 0 S) i.succ 0 = 0 := fun i => by simp [blkM]
  have h00 : (blkM 1 u 0 S) 0 0 = 1 := by simp [blkM]
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [h0, h00, hs, Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- **Change of basis of a bordered matrix** by $\begin{pmatrix}1 & \mathbf u^{\mathsf T}\\ 0 & S\end{pmatrix}$. -/
theorem conj_blkM (α : R) (c : Fin m → R) (X : Matrix (Fin m) (Fin m) R) (u : Fin m → R)
    (S : Matrix (Fin m) (Fin m) R) :
    (blkM 1 u 0 S)ᵀ * blkM α c c X * blkM 1 u 0 S =
      blkM α (α • u + c ᵥ* S) (α • u + c ᵥ* S)
        (vecMulVec (α • u + c ᵥ* S) u + (vecMulVec u c + Sᵀ * X) * S) := by
  rw [blkM_transpose, blkM_mul, blkM_mul]
  have e1 : Sᵀ *ᵥ c = c ᵥ* S := Matrix.mulVec_transpose S c
  simp [e1]

/-- Ring homomorphisms act entrywise on bordered matrices. -/
theorem blkM_map{S : Type*} [CommRing S] (f : R →+* S) (d : R) (r s : Fin m → R)
    (Y : Matrix (Fin m) (Fin m) R) :
    (blkM d r s Y).map f = blkM (f d) (f ∘ r) (f ∘ s) (Y.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blkM]

end Bordered

/-! ### The matrix $h$ of (6.8) as a bordered matrix -/

/-- The lower right block $((c_ic_j + g_{ij})/a)$ of `hMat`. -/
def hBlockX (a : ℤ) (c : Fin m → ℤ) (G : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => (c i * c j + G i j) / a

/-- `hMat` is the bordered matrix with corner $a$, border $\mathbf c$ and block `hBlockX`. -/
theorem hMat_eq_blkM(a : ℤ) (c : Fin m → ℤ) (G : Matrix (Fin m) (Fin m) ℤ) :
    hMat a c G = blkM a c c (hBlockX a c G) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blkM, hBlockX, hMat]

section Conj

variable {R : Type*} [CommRing R]

/-- $a\cdot\bigl((c_ic_j + g_{ij})/a\bigr) = c_ic_j + g_{ij}$ in $R$ when $a \mid c_ic_j + g_{ij}$. -/
theorem smul_hBlockX {a : ℕ} {c : Fin m → ℤ} {G : Matrix (Fin m) (Fin m) ℤ}
    (hc : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) :
    (a : R) • (hBlockX (a : ℤ) c G).map (Int.castRingHom R) =
      vecMulVec (fun i => (c i : R)) (fun i => (c i : R)) + G.map (Int.castRingHom R) := by
  ext i j
  have := Int.mul_ediv_cancel' (hc i j)
  simp only [hBlockX, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply,
    vecMulVec_apply]
  have h2 := congrArg (Int.castRingHom R) this
  simp only [map_mul, map_add, eq_intCast, Int.cast_natCast] at h2 ⊢
  rw [← h2]

/-- **The key identity.** Let $\alpha = a$, $\mathbf c$ with $a \mid c_ic_j + g_{ij}$, and $T$ over $R$ with
$T^{\mathsf T}GT = G'$. If $\mathbf c' = a\mathbf k + T^{\mathsf T}\mathbf c$ then conjugating $h(\mathbf c, G)$ by
$\begin{pmatrix}1 & \mathbf k^{\mathsf T}\\ 0 & T\end{pmatrix}$ gives a bordered matrix with data
$(a, \mathbf c')$ whose lower right block $Y$ satisfies $aY = \mathbf c'\mathbf c'^{\mathsf T} + G'$. -/
theorem conj_hMat {a : ℕ} {c : Fin m → ℤ} {G G' : Matrix (Fin m) (Fin m) ℤ} {c' : Fin m → ℤ}
    (hc : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (T : Matrix (Fin m) (Fin m) R) (k : Fin m → R)
    (hTG : Tᵀ * G.map (Int.castRingHom R) * T = G'.map (Int.castRingHom R))
    (hk : (fun i => (c' i : R)) = (a : R) • k + (fun j => (c j : R)) ᵥ* T) :
    ∃ Y : Matrix (Fin m) (Fin m) R,
      (a : R) • Y = vecMulVec (fun i => (c' i : R)) (fun i => (c' i : R)) + G'.map (Int.castRingHom R) ∧
      (blkM 1 k 0 T)ᵀ * (hMat (a : ℤ) c G).map (Int.castRingHom R) * blkM 1 k 0 T =
        blkM (a : R) (fun i => (c' i : R)) (fun i => (c' i : R)) Y := by
  set φ := Int.castRingHom R with hφ
  set cR : Fin m → R := fun i => (c i : R) with hcR
  set w : Fin m → R := cR ᵥ* T with hw
  have hX : (a : R) • (hBlockX (a : ℤ) c G).map φ = vecMulVec cR cR + G.map φ := smul_hBlockX hc
  rw [hMat_eq_blkM, blkM_map, hk]
  have e1 : (fun i => φ (c i)) = cR := rfl
  have e2 : φ (a : ℤ) = (a : R) := by simp
  have e3 : φ ∘ c = cR := rfl
  rw [e2, e3, conj_blkM, ← hw]
  refine ⟨vecMulVec ((a : R) • k + w) k + (vecMulVec k cR + Tᵀ * (hBlockX (a : ℤ) c G).map φ) * T, ?_, ?_⟩
  · have step : (a : R) • (vecMulVec ((a : R) • k + w) k + (vecMulVec k cR + Tᵀ * (hBlockX (a : ℤ) c G).map φ) * T) =
        (a : R) • vecMulVec ((a : R) • k + w) k + (a : R) • (vecMulVec k cR * T) +
          Tᵀ * ((a : R) • (hBlockX (a : ℤ) c G).map φ) * T := by
      simp only [Matrix.add_mul, smul_add, Matrix.mul_smul, Matrix.smul_mul]
      abel
    rw [step, hX, Matrix.mul_add, Matrix.add_mul, hTG]
    simp only [vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.mulVec_transpose]
    try rw [← hw]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rfl

/-- Under the hypotheses of `conj_hMat`, $a \mid c'_ic'_j + g'_{ij}$ in $R$. -/
theorem dvd_of_conj_hMat {a : ℕ} {c : Fin m → ℤ} {G G' : Matrix (Fin m) (Fin m) ℤ} {c' : Fin m → ℤ}
    (hc : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (T : Matrix (Fin m) (Fin m) R) (k : Fin m → R)
    (hTG : Tᵀ * G.map (Int.castRingHom R) * T = G'.map (Int.castRingHom R))
    (hk : (fun i => (c' i : R)) = (a : R) • k + (fun j => (c j : R)) ᵥ* T) (i j : Fin m) :
    (a : R) ∣ ((c' i * c' j + G' i j : ℤ) : R) := by
  obtain ⟨Y, hY, -⟩ := conj_hMat hc T k hTG hk
  refine ⟨Y i j, ?_⟩
  have := congrFun (congrFun hY i) j
  simpa [vecMulVec_apply] using this.symm

end Conj

section Conj2

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- **Congruence of the matrices $h$** (6.8): if $T^{\mathsf T}GT = G'$ over $R$ with $\det T$ a unit and
$\mathbf c' = a\mathbf k + T^{\mathsf T}\mathbf c$, then $h(\mathbf c, G) \sim h(\mathbf c', G')$ over $R$. -/
theorem meq_hMat {a : ℕ} (ha : 0 < a) {c c' : Fin m → ℤ} {G G' : Matrix (Fin m) (Fin m) ℤ}
    (hc : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (hc' : ∀ i j, (a : ℤ) ∣ c' i * c' j + G' i j)
    (T : Matrix (Fin m) (Fin m) R) (hT : IsUnit T.det) (k : Fin m → R)
    (hTG : Tᵀ * G.map (Int.castRingHom R) * T = G'.map (Int.castRingHom R))
    (hk : (fun i => (c' i : R)) = (a : R) • k + (fun j => (c j : R)) ᵥ* T) :
    CongrLocal.MEq ((hMat (a : ℤ) c G).map (Int.castRingHom R)) ((hMat (a : ℤ) c' G').map (Int.castRingHom R)) := by
  obtain ⟨Y, hY, hY2⟩ := conj_hMat hc T k hTG hk
  refine ⟨blkM 1 k 0 T, by rw [det_blkM_one]; exact hT, ?_⟩
  rw [hY2, hMat_eq_blkM, blkM_map]
  have hX' := smul_hBlockX (R := R) hc'
  have hne : (a : R) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have : Y = (hBlockX (a : ℤ) c' G').map (Int.castRingHom R) :=
    smul_right_injective _ hne (hY.trans hX'.symm)
  have e : Int.castRingHom R (a : ℤ) = (a : R) := by simp
  rw [this, e]
  rfl

end Conj2

/-! ### From equivalence over a ring to congruence of Cassels' matrices -/

/-- The Hessian of the base change of a classically integral form is $2(f_{ij})$. -/
theorem hessian_map_casselsMat {n : ℕ} {R : Type*} [CommRing R] {q : QuadForm ℤ n} (hq : IsClassicallyIntegral q) :
    (q.map (Int.castRingHom R)).hessian = (2 : R) • (casselsMat q).map (Int.castRingHom R) := by
  rw [hessian_map, hessian_eq_two_smul_casselsMat hq]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]

/-- **Equivalence over $R$ gives congruence of Cassels' matrices** (converse of `isometricGL_of_meq_casselsMat'`). -/
theorem meq_of_isometricGL_casselsMat {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {f g : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (hg : IsClassicallyIntegral g)
    (h : IsometricGL (f.map (Int.castRingHom R)) (g.map (Int.castRingHom R))) :
    CongrLocal.MEq ((casselsMat f).map (Int.castRingHom R)) ((casselsMat g).map (Int.castRingHom R)) := by
  obtain ⟨T, hT⟩ := IsometricGL.hessian_eq h
  rw [hessian_map_casselsMat hf, hessian_map_casselsMat hg, Matrix.mul_smul, Matrix.smul_mul] at hT
  refine ⟨T.val, Matrix.isUnits_det_units T, ?_⟩
  exact smul_right_injective _ (two_ne_zero : (2 : R) ≠ 0) hT

/-- The Cassels matrix of `ofGram (hMat ..)` (for symmetric $G$) is `hMat ..`. -/
theorem casselsMat_ofGram_hMat {a : ℤ} {c : Fin m → ℤ} {G : Matrix (Fin m) (Fin m) ℤ} (hG : G.IsSymm) :
    casselsMat (ofGram (hMat a c G)) = hMat a c G :=
  casselsMat_ofGram (hMat_isSymm hG)

/-- **Equivalence of the forms $h$** over $R$ from the data of `meq_hMat`. -/
theorem isometricGL_hMat {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {a : ℕ} (ha : 0 < a)
    {c c' : Fin m → ℤ} {G G' : Matrix (Fin m) (Fin m) ℤ} (hG : G.IsSymm) (hG' : G'.IsSymm)
    (hc : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (hc' : ∀ i j, (a : ℤ) ∣ c' i * c' j + G' i j)
    (T : Matrix (Fin m) (Fin m) R) (hT : IsUnit T.det) (k : Fin m → R)
    (hTG : Tᵀ * G.map (Int.castRingHom R) * T = G'.map (Int.castRingHom R))
    (hk : (fun i => (c' i : R)) = (a : R) • k + (fun j => (c j : R)) ᵥ* T) :
    IsometricGL ((ofGram (hMat (a : ℤ) c G)).map (Int.castRingHom R))
      ((ofGram (hMat (a : ℤ) c' G')).map (Int.castRingHom R)) := by
  refine isometricGL_of_meq_casselsMat' (ci_ofGram (hMat_isSymm hG)) (ci_ofGram (hMat_isSymm hG')) ?_
  rw [casselsMat_ofGram_hMat hG, casselsMat_ofGram_hMat hG']
  exact meq_hMat ha hc hc' T hT k hTG hk

/-! ### (6.10): $\rho$ depends only on the genus -/

/-- **Vector approximation:** given $\mathbf t_p \in \mathbb Z_p^m$ for each prime $p$, there is an integral vector
$\mathbf c'$ with $\mathbf c' = a\mathbf k + \mathbf t_p$ for some $\mathbf k \in \mathbb Z_p^m$, for every $p$. -/
theorem exists_vec_approx {a : ℕ} (ha : 0 < a) (t : ∀ (p : ℕ) [Fact p.Prime], Fin m → ℤ_[p]) :
    ∃ c' : Fin m → ℤ, ∀ (p : ℕ) [Fact p.Prime], ∃ k : Fin m → ℤ_[p],
      (fun i => (c' i : ℤ_[p])) = (a : ℤ_[p]) • k + t p := by
  have h := fun i : Fin m => exists_int_approx ha (fun p _ => t p i)
  choose z hz using h
  refine ⟨z, fun p _ => ?_⟩
  have h2 := fun i : Fin m => hz i p
  choose k hk using h2
  exact ⟨k, funext fun i => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hk i]; ring⟩

/-- If $\mathbf d T = a\mathbf e$ over $\mathbb Z_p$ with $\det T$ a unit, then $a \mid d_i$. -/
theorem dvd_of_vecMul_eq {R : Type*} [CommRing R] (a : R) (T : Matrix (Fin m) (Fin m) R) (hT : IsUnit T.det)
    (d e : Fin m → R) (h : d ᵥ* T = a • e) (i : Fin m) : a ∣ d i := by
  have h1 : d = a • (e ᵥ* T⁻¹) := by
    rw [← smul_vecMul, ← h, vecMul_vecMul, Matrix.mul_nonsing_inv _ hT, vecMul_one]
  exact ⟨(e ᵥ* T⁻¹) i, by rw [h1]; rfl⟩

/-- **Cassels (6.10), one inequality:** $\rho(\mathcal F, g) \le \rho(\mathcal F, g')$ for $g, g'$ in one genus. -/
theorem rhoCount_le_of_sameGenus {f : QuadForm ℤ (m + 1)} {a : ℕ} (ha : 0 < a) {g g' : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) (hg' : IsClassicallyIntegral g') (hs : SameGenus g g') :
    rhoCount f a (casselsMat g) ≤ rhoCount f a (casselsMat g') := by
  classical
  have : NeZero a := ⟨ha.ne'⟩
  have hG : (casselsMat g).IsSymm := casselsMat_isSymm g
  have hG' : (casselsMat g').IsSymm := casselsMat_isSymm g'
  have hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ T : Matrix (Fin m) (Fin m) ℤ_[p], IsUnit T.det ∧
      Tᵀ * (casselsMat g).map (Int.castRingHom ℤ_[p]) * T = (casselsMat g').map (Int.castRingHom ℤ_[p]) :=
    fun p _ => meq_of_isometricGL_casselsMat hg hg' (hs.1 p)
  choose T hT hTG using hloc
  obtain ⟨Tr, hTr, hTrG⟩ := meq_of_isometricGL_casselsMat (R := ℝ) hg hg' hs.2
  -- the key construction
  have key : ∀ v : {v : Fin m → ZMod a // ∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v i) ∧
      (∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) ∧ SameGenus f (ofGram (hMat (a : ℤ) c (casselsMat g)))},
      ∃ c' : Fin m → ℤ, (∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v.1 i) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ k : Fin m → ℤ_[p],
          (fun i => (c' i : ℤ_[p])) = (a : ℤ_[p]) • k + (fun j => (c j : ℤ_[p])) ᵥ* T p) ∧
        (∀ i j, (a : ℤ) ∣ c' i * c' j + casselsMat g' i j) ∧
        SameGenus f (ofGram (hMat (a : ℤ) c' (casselsMat g'))) := by
    rintro ⟨v, c, hcv, hdiv, hgen⟩
    obtain ⟨c', hc'⟩ := exists_vec_approx ha (fun p _ => (fun j => (c j : ℤ_[p])) ᵥ* T p)
    have hdiv' : ∀ i j, (a : ℤ) ∣ c' i * c' j + casselsMat g' i j := fun i j =>
      int_dvd_of_forall_padic ha fun p _ => by
        obtain ⟨k, hk⟩ := hc' p
        exact dvd_of_conj_hMat hdiv (T p) k (hTG p) hk i j
    refine ⟨c', ⟨c, hcv, hc'⟩, hdiv', ?_⟩
    refine hgen.trans ⟨fun p _ => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hc' p
      exact isometricGL_hMat ha hG hG' hdiv hdiv' (T p) (hT p) k (hTG p) hk
    · have hne : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
      refine isometricGL_hMat ha hG hG' hdiv hdiv' Tr hTr
        ((a : ℝ)⁻¹ • (fun i => (c' i : ℝ) - ((fun j => (c j : ℝ)) ᵥ* Tr) i)) hTrG ?_
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  choose c' hc' using key
  let F : {v : Fin m → ZMod a // ∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v i) ∧
      (∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) ∧ SameGenus f (ofGram (hMat (a : ℤ) c (casselsMat g)))} →
      {v : Fin m → ZMod a // ∃ c : Fin m → ℤ, (∀ i, (c i : ZMod a) = v i) ∧
      (∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g' i j) ∧ SameGenus f (ofGram (hMat (a : ℤ) c (casselsMat g')))} :=
    fun v => ⟨fun i => (c' v i : ZMod a), c' v, fun i => rfl, (hc' v).2.1, (hc' v).2.2⟩
  have hF : Function.Injective F := by
    intro v₁ v₂ h
    have h1 : ∀ i, (a : ℤ) ∣ c' v₂ i - c' v₁ i := fun i =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun (congrArg Subtype.val h) i)
    obtain ⟨cc₁, hcc₁, hk₁⟩ := (hc' v₁).1
    obtain ⟨cc₂, hcc₂, hk₂⟩ := (hc' v₂).1
    choose mm hmm using h1
    have h2 : ∀ i, (a : ℤ) ∣ cc₂ i - cc₁ i := fun i => by
      refine int_dvd_of_forall_padic ha fun p _ => ?_
      obtain ⟨k₁, e₁⟩ := hk₁ p
      obtain ⟨k₂, e₂⟩ := hk₂ p
      have y₁ : (fun j => (cc₁ j : ℤ_[p])) ᵥ* T p = fun j => (c' v₁ j : ℤ_[p]) - a * k₁ j := by
        funext j
        have := congrFun e₁ j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        linear_combination (-1 : ℤ_[p]) * this
      have y₂ : (fun j => (cc₂ j : ℤ_[p])) ᵥ* T p = fun j => (c' v₂ j : ℤ_[p]) - a * k₂ j := by
        funext j
        have := congrFun e₂ j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        linear_combination (-1 : ℤ_[p]) * this
      have hv : ((fun j => (cc₂ j : ℤ_[p])) - (fun j => (cc₁ j : ℤ_[p]))) ᵥ* T p =
          (a : ℤ_[p]) • (fun j => (mm j : ℤ_[p]) - k₂ j + k₁ j) := by
        rw [Matrix.sub_vecMul, y₁, y₂]
        funext j
        have x3 : ((c' v₂ j : ℤ) : ℤ_[p]) - (c' v₁ j : ℤ_[p]) = (a : ℤ_[p]) * (mm j : ℤ_[p]) := by
          exact_mod_cast hmm j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination x3
      have := dvd_of_vecMul_eq (a : ℤ_[p]) (T p) (hT p) _ _ hv i
      simpa using this
    refine Subtype.ext (funext fun i => ?_)
    rw [← hcc₁ i, ← hcc₂ i]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h2 i)
  exact Nat.card_le_card_of_injective F hF

/-- **Cassels (6.10)** (Ch. 9, §6, p. 146): *$\rho$ depends only on the genus of $g$.* Hypotheses: $f$ is a form in
$m + 1$ variables (the genus $\mathcal F$ is that of $f$); $a > 0$ is the integer represented (`ha`);
$g, g'$ are forms in $m$ variables, classically integral (`hg`, `hg'`: the matrices $(g_{ij}), (g'_{ij})$ of
`casselsMat` are integral), and in the same genus (`hs`: equivalent over every $\mathbb Z_p$ and over $\mathbb R$).
Conclusion: $\rho(\mathcal F, g) = \rho(\mathcal F, g')$, i.e. the numbers of classes $\mathbf c \bmod a$ in
$(\mathbb Z/a)^m$ (0-based coordinates $c_0, \dots, c_{m-1}$) for which $a \mid c_ic_j + g_{ij}$ and the form
$h$ of (6.8) lies in the genus of $f$ agree. The proof is local (it does not go through Cassels' Lemma 4.2,
Corollary 1 and Lemma 4.3; cf. his remark that $\rho$ "can be determined by purely local considerations"). -/
@[kb "cassels1978" "Ch. 9, §6, (6.10), p. 146 (ρ depends only on the genus of g)"]
theorem rhoCount_eq_of_sameGenus {f : QuadForm ℤ (m + 1)} {a : ℕ} (ha : 0 < a) {g g' : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) (hg' : IsClassicallyIntegral g') (hs : SameGenus g g') :
    rhoCount f a (casselsMat g) = rhoCount f a (casselsMat g') :=
  le_antisymm (rhoCount_le_of_sameGenus ha hg hg' hs) (rhoCount_le_of_sameGenus ha hg' hg hs.symm)

/-- **Cassels, Lemma 6.2** (Ch. 9, p. 146), *without* the constancy hypothesis: with $f$ a positive definite,
classically integral form in $m + 1 \ge 2$ variables (`hm`, `hf`, `hfpd`), $a > 0$ (`ha`), $g$ a positive definite,
classically integral form in $m$ variables (`hg`, `hgpd`) and $\det(g_{ij}) = a^{m-1}\det(f_{ij})$ (`hdet`),
$$\sigma(a, \mathcal F, \mathcal G) = \rho(\mathcal F, g)\,W(\mathcal G) \qquad (6.12),$$
where $\rho(\mathcal F, g)$ is `rhoCount f a (casselsMat g)` and $W(\mathcal G)$ is `pweight g`. The constancy of
$\rho$ on the genus of $g$ (`sigmaGenus_eq`'s hypothesis `hρ`) is now proved (`rhoCount_eq_of_sameGenus`). -/
@[kb "cassels1978" "Ch. 9, Lemma 6.2, (6.12), p. 146"]
theorem sigmaGenus_eq_rho (hm : 1 ≤ m) {f : QuadForm ℤ (m + 1)} (hf : IsClassicallyIntegral f)
    (hfpd : IntQF.PosDef f) {a : ℕ} (ha : 0 < a) {g : QuadForm ℤ m} (hg : IsClassicallyIntegral g)
    (hgpd : IntQF.PosDef g) (hdet : (casselsMat g).det = (a : ℤ) ^ (m - 1) * (casselsMat f).det) :
    sigmaGenus f a g = rhoCount f a (casselsMat g) * pweight g :=
  sigmaGenus_eq hm hf hfpd ha hg hgpd hdet fun _ hs =>
    (rhoCount_eq_of_sameGenus ha hg (hs.isClassicallyIntegral hg) hs).symm

end QuadFormsKB.Siegel
