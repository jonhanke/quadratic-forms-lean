/-
# Cassels, Chapter 9, §6, Lemma 6.6: local classes of the ternary forms

**Layer:** symmetric $3\times 3$ matrices over $\mathbb Z_p$ ($p$ odd), congruence `MEq`
(`Ch9Sec4LocalAlg.lean`) and the unimodular classification `meq_unimod` (`Ch9Sec4LocalPadic.lean`).

**Proves** (`meq_G₀`): let $G_0(a) = \begin{pmatrix} -1 & 0 & 0 \\ 0 & 0 & a \\ 0 & a & 0\end{pmatrix}$ be the matrix
of $-y_0^2 + 2a\,y_1y_2$ (Cassels (6.46), 0-based). If $p \ne 2$, $a \ne 0$, $p^2 \nmid a$, $G$ is a symmetric integral
$3\times3$ matrix with $\det G = a^2$, and (when $p \mid a$) $G \equiv -cc^{\mathsf T} \pmod p$ for some
$c \in \mathbb Z^3$, then $G_0(a)$ and $G$ are congruent over $\mathbb Z_p$ (`meq_G₀`, via `meq_G₀_of_not_dvd`
for $p \nmid a$ and `meq_G₀_of_dvd` for $p \mid a$).

*Proof.* For $p \nmid a$ both matrices are unimodular with the same determinant (`meq_unimod`). For $p \mid a$,
$p^2 \nmid a$: $c \not\equiv 0 \pmod p$ (else $p^3 \mid \det G$), so after a coordinate permutation $G_{00} \equiv -c_0^2$
is a unit. Splitting off the coordinate $0$ by a unipotent congruence gives $\langle G_{00}\rangle \perp A'$ with
$A' \equiv 0 \pmod p$, $A' = pB$, $\det B$ a unit; $\langle G_{00}\rangle \sim \langle -1\rangle$ (as $-G_{00}$ is a
unit square by Hensel) and $B \sim \begin{pmatrix} 0 & a/p \\ a/p & 0\end{pmatrix}$ (`meq_unimod`). Indices are 0-based.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4LocalPadic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel.CongrLocal

/-- **Cassels' matrix (6.46):** $G_0(a) = \begin{pmatrix} -1 & 0 & 0 \\ 0 & 0 & a \\ 0 & a & 0\end{pmatrix}$, the
matrix of $-y_0^2 + 2a\,y_1y_2$ (0-based indices). -/
def G₀ (a : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, 0, a; 0, a, 0]

section Blocks

variable {R : Type*} [CommRing R]

/-- The block diagonal $3\times 3$ matrix $\langle u\rangle \perp B$ with $B$ a $2\times 2$ matrix on the indices
$1, 2$. -/
def blk3 (u : R) (B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

/-- The $2\times 2$ hyperbolic matrix $\begin{pmatrix} 0 & b \\ b & 0\end{pmatrix}$. -/
def hyp (b : R) : Matrix (Fin 2) (Fin 2) R := !![0, b; b, 0]

/-- The determinant of $\langle u\rangle \perp B$ is $u\det B$. -/
theorem det_blk3 (u : R) (B : Matrix (Fin 2) (Fin 2) R) : (blk3 u B).det = u * B.det := by
  simp [blk3, det_fin_three, det_fin_two]; ring

/-- The determinant of the hyperbolic matrix is $-b^2$. -/
theorem det_hyp (b : R) : (hyp b).det = -b ^ 2 := by
  simp [hyp, det_fin_two]; ring

/-- $G_0(a)$ is $\langle -1\rangle \perp \begin{pmatrix} 0 & a \\ a & 0\end{pmatrix}$ (over any ring receiving $\mathbb Z$). -/
theorem G₀_map_eq (a : ℤ) (f : ℤ →+* R) : (G₀ a).map f = blk3 (-1) (hyp (f a)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [G₀, blk3, hyp]

/-- **Orthogonal sums with a $1\times1$ block:** $\langle u\rangle \perp B \sim \langle r^2u\rangle \perp B'$ for
$B \sim B'$ and $r$ a unit. -/
theorem meq_blk3 {u r : R} (hr : IsUnit r) {B B' : Matrix (Fin 2) (Fin 2) R} (h : MEq B B') :
    MEq (blk3 u B) (blk3 (r ^ 2 * u) B') := by
  obtain ⟨T, hT, hTB⟩ := h
  have e : ∀ i j, (Tᵀ * B * T) i j = B' i j := fun i j => by rw [hTB]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e00 e01 e10 e11
  refine ⟨!![r, 0, 0; 0, T 0 0, T 0 1; 0, T 1 0, T 1 1], ?_, ?_⟩
  · have : (!![r, 0, 0; 0, T 0 0, T 0 1; 0, T 1 0, T 1 1] : Matrix (Fin 3) (Fin 3) R).det = r * T.det := by
      simp [det_fin_three, det_fin_two]; ring
    rw [this]; exact hr.mul hT
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination e00 | linear_combination e01 | linear_combination e10 |
        linear_combination e11

/-- **Splitting off the coordinate $0$:** if $v A_{00} = 1$ and $A$ is symmetric, then
$A \sim \langle A_{00}\rangle \perp A'$ with $A'_{ij} = A_{i+1,j+1} - v A_{0,i+1}A_{0,j+1}$. -/
theorem meq_split0 {A : Matrix (Fin 3) (Fin 3) R} (hA : Aᵀ = A) {v : R} (hv : v * A 0 0 = 1) :
    MEq A (blk3 (A 0 0) (Matrix.of fun i j : Fin 2 => A i.succ j.succ - v * A 0 i.succ * A 0 j.succ)) := by
  have hs : ∀ i j, A i j = A j i := fun i j => by rw [← transpose_apply A i j, hA]
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h21 := hs 2 1
  refine ⟨!![1, -v * A 0 1, -v * A 0 2; 0, 1, 0; 0, 0, 1], ?_, ?_⟩
  · simp [det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk3, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21] <;>
      first | linear_combination (-A 0 1) * hv | linear_combination (-A 0 2) * hv |
        linear_combination (v * A 0 1 ^ 2) * hv | linear_combination (v * A 0 1 * A 0 2) * hv |
        linear_combination (v * A 0 2 ^ 2) * hv

/-- **Coordinate permutations are congruences:** $A \sim A_{\sigma\sigma}$ for a permutation $\sigma$. -/
theorem meq_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (σ : Equiv.Perm ι) :
    MEq A (A.submatrix σ σ) := by
  refine ⟨(1 : Matrix ι ι R).submatrix id σ, ?_, ?_⟩
  · rw [det_permute']
    simpa using (Units.isUnit (Equiv.Perm.sign σ)).map (Int.castRingHom R)
  · ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply, mul_ite, ite_mul]

end Blocks

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- For an integer $x$: $p \mid x$ in $\mathbb Z_p$ iff $p \mid x$ in $\mathbb Z$. -/
theorem cast_dvd_iff (x : ℤ) : (p : ℤ_[p]) ∣ (x : ℤ_[p]) ↔ (p : ℤ) ∣ x := by
  rw [dvd_iff_toZMod, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- $G_0(a)$ and its image in $\mathbb Z_p$ are symmetric. -/
theorem G₀_symm (a : ℤ) : ((G₀ a).map (Int.castRingHom ℤ_[p]))ᵀ = (G₀ a).map (Int.castRingHom ℤ_[p]) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [G₀]

/-- The hyperbolic matrix is symmetric. -/
theorem hyp_symm {R : Type*} [CommRing R] (b : R) : (hyp b)ᵀ = hyp b := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hyp]

/-- **The case $p \nmid a$** of Lemma 6.6: both matrices are unimodular of determinant $a^2$. -/
theorem meq_G₀_of_not_dvd (hp2 : p ≠ 2) {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) {G : Matrix (Fin 3) (Fin 3) ℤ}
    (hG : Gᵀ = G) (hdet : G.det = a ^ 2) :
    MEq ((G₀ a).map (Int.castRingHom ℤ_[p])) (G.map (Int.castRingHom ℤ_[p])) := by
  have hB : (G.map (Int.castRingHom ℤ_[p]))ᵀ = G.map (Int.castRingHom ℤ_[p]) := by
    rw [← transpose_map, hG]
  have hdA : ((G₀ a).map (Int.castRingHom ℤ_[p])).det = (a : ℤ_[p]) ^ 2 := by
    rw [G₀_map_eq, det_blk3, det_hyp]; simp
  have hdB : (G.map (Int.castRingHom ℤ_[p])).det = (a : ℤ_[p]) ^ 2 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]; simp
  have hu : IsUnit (a : ℤ_[p]) := by rw [isUnit_iff_not_dvd, cast_dvd_iff]; exact hpa
  exact meq_unimod hp2 (G₀_symm a) hB (by rw [hdA]; exact hu.pow 2) isUnit_one (by rw [hdA, hdB]; ring)

/-- If $\det A = (pa_1)^2$ with $a_1$ a unit and $A \equiv -cc^{\mathsf T} \pmod p$, then some $c_k$ is a unit. -/
theorem exists_unit_c {A : Matrix (Fin 3) (Fin 3) ℤ_[p]} {a₁ : ℤ_[p]} (ha₁ : IsUnit a₁)
    (hdet : A.det = ((p : ℤ_[p]) * a₁) ^ 2) {c : Fin 3 → ℤ_[p]}
    (hc : ∀ i j, (p : ℤ_[p]) ∣ c i * c j + A i j) : ∃ k, IsUnit (c k) := by
  by_contra hne
  push Not at hne
  have hcd : ∀ k, (p : ℤ_[p]) ∣ c k := fun k => by
    have := hne k; rwa [isUnit_iff_not_dvd, not_not] at this
  have hA : ∀ i j, (p : ℤ_[p]) ∣ A i j := fun i j => by
    have := dvd_sub (hc i j) ((hcd i).mul_right (c j))
    simpa using this
  choose g hg using hA
  rw [det_fin_three] at hdet
  simp only [hg] at hdet
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  have key : (p : ℤ_[p]) ^ 2 * a₁ ^ 2 = (p : ℤ_[p]) ^ 2 * (p * (g 0 0 * g 1 1 * g 2 2 - g 0 0 * g 1 2 * g 2 1
      - g 0 1 * g 1 0 * g 2 2 + g 0 1 * g 1 2 * g 2 0 + g 0 2 * g 1 0 * g 2 1 - g 0 2 * g 1 1 * g 2 0)) := by
    linear_combination -hdet
  have key' := mul_left_cancel₀ (pow_ne_zero 2 hp0) key
  have hd : (p : ℤ_[p]) ∣ a₁ ^ 2 := ⟨_, key'⟩
  have hd1 : (p : ℤ_[p]) ∣ a₁ := PadicInt.prime_p.dvd_of_dvd_pow hd
  exact (isUnit_iff_not_dvd a₁).1 ha₁ hd1

/-- **The core, with a unit $c_0$:** if $A \equiv -cc^{\mathsf T} \pmod p$, $\det A = (pa_1)^2$ with $a_1$ a unit
and $c_0$ a unit ($p$ odd), then $\langle -1\rangle \perp \begin{pmatrix} 0 & pa_1 \\ pa_1 & 0\end{pmatrix} \sim A$. -/
theorem meq_core0 (hp2 : p ≠ 2) {A : Matrix (Fin 3) (Fin 3) ℤ_[p]} (hA : Aᵀ = A) {a₁ : ℤ_[p]}
    (ha₁ : IsUnit a₁) (hdet : A.det = ((p : ℤ_[p]) * a₁) ^ 2) {c : Fin 3 → ℤ_[p]}
    (hc : ∀ i j, (p : ℤ_[p]) ∣ c i * c j + A i j) (hc0 : IsUnit (c 0)) :
    MEq (blk3 (-1) (hyp ((p : ℤ_[p]) * a₁))) A := by
  have hs : ∀ i j, A i j = A j i := fun i j => by rw [← transpose_apply A i j, hA]
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  -- reduction mod p
  have hcz : ∀ i j, PadicInt.toZMod (c i) * PadicInt.toZMod (c j) + PadicInt.toZMod (A i j) = 0 := fun i j => by
    have := (dvd_iff_toZMod _).1 (hc i j)
    simpa using this
  have hγ0 : PadicInt.toZMod (c 0) ≠ 0 := by
    intro h; exact (isUnit_iff_not_dvd _).1 hc0 ((dvd_iff_toZMod _).2 h)
  have hA00 : IsUnit (A 0 0) := by
    rw [isUnit_iff_not_dvd, dvd_iff_toZMod]
    intro h
    have := hcz 0 0
    rw [h, add_zero] at this
    exact hγ0 (mul_self_eq_zero.1 this)
  obtain ⟨v, hv⟩ := hA00.exists_left_inv
  have hsplit := meq_split0 hA hv
  set A' : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
    Matrix.of fun i j : Fin 2 => A i.succ j.succ - v * A 0 i.succ * A 0 j.succ with hA'
  -- A' is divisible by p
  have hdiv : ∀ i j, (p : ℤ_[p]) ∣ A' i j := fun i j => by
    have h1 : PadicInt.toZMod (A 0 0 * A' i j) = 0 := by
      have e : A 0 0 * A' i j = A 0 0 * A i.succ j.succ - A 0 i.succ * A 0 j.succ := by
        simp only [hA', Matrix.of_apply]; linear_combination (-(A 0 i.succ * A 0 j.succ)) * hv
      rw [e]
      have h00 := hcz 0 0
      have hxy := hcz i.succ j.succ
      have h0x := hcz 0 i.succ
      have h0y := hcz 0 j.succ
      simp only [map_sub, map_mul]
      linear_combination (PadicInt.toZMod (A i.succ j.succ)) * h00 +
        (-(PadicInt.toZMod (c 0)) ^ 2) * hxy - (PadicInt.toZMod (A 0 j.succ)) * h0x +
        (PadicInt.toZMod (c 0) * PadicInt.toZMod (c i.succ)) * h0y
    have h2 : (p : ℤ_[p]) ∣ A 0 0 * A' i j := (dvd_iff_toZMod _).2 h1
    exact (PadicInt.prime_p.dvd_or_dvd h2).resolve_left ((isUnit_iff_not_dvd _).1 hA00)
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 2) (Fin 2) ℤ_[p], ∀ i j, A' i j = (p : ℤ_[p]) * B i j :=
    ⟨Matrix.of fun i j => (hdiv i j).choose, fun i j => (hdiv i j).choose_spec⟩
  have hA'B : A' = (p : ℤ_[p]) • B := by refine Matrix.ext fun i j => ?_; simp [hB i j]
  have hA's : A'ᵀ = A' := by
    refine Matrix.ext fun i j => ?_
    simp only [transpose_apply, hA', Matrix.of_apply]
    rw [hs j.succ i.succ, hs 0 i.succ, hs 0 j.succ]; ring
  have hBs : Bᵀ = B := by
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hA's i) j
    simp only [transpose_apply] at h1 ⊢
    have h2 : (p : ℤ_[p]) * B j i = (p : ℤ_[p]) * B i j := by rw [← hB, ← hB]; exact h1
    exact mul_left_cancel₀ hp0 h2
  -- determinants
  obtain ⟨r, hr, hrd⟩ := hsplit.det
  rw [det_blk3, hdet, hA'B, det_smul] at hrd
  simp only [Fintype.card_fin] at hrd
  have hrd' : A 0 0 * B.det = r ^ 2 * a₁ ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 hp0) (by linear_combination hrd)
  -- -A 00 is a unit square
  obtain ⟨w, hw⟩ := hc0.exists_left_inv
  have hsq1 : ∃ r1 : ℤ_[p], IsUnit r1 ∧ -A 0 0 = r1 ^ 2 := by
    have hu : (p : ℤ_[p]) ∣ (-A 0 0 * w ^ 2) - 1 := by
      rw [dvd_iff_toZMod]
      have h00 := hcz 0 0
      have hww : PadicInt.toZMod w * PadicInt.toZMod (c 0) = 1 := by
        rw [← map_mul, hw, map_one]
      simp only [map_sub, map_mul, map_neg, map_pow, map_one]
      linear_combination (-(PadicInt.toZMod w) ^ 2) * h00 + (PadicInt.toZMod w * PadicInt.toZMod (c 0) + 1) * hww
    have h2u : IsUnit (2 : ℤ_[p]) := (isUnit_iff_not_dvd 2).2 (Kneser.not_p_dvd_two hp2)
    have h4u : IsUnit (4 : ℤ_[p]) := by
      have : (4 : ℤ_[p]) = 2 * 2 := by norm_num
      rw [this]; exact h2u.mul h2u
    obtain ⟨q, hq⟩ := h4u.exists_left_inv
    obtain ⟨y, hy⟩ := hu
    obtain ⟨r, hr, hre⟩ := exists_sq_of_dvd (p := p) (u := -A 0 0 * w ^ 2)
      ⟨q * y, by linear_combination hy - ((p : ℤ_[p]) * y) * hq⟩
    refine ⟨r * c 0, hr.mul hc0, ?_⟩
    have : -A 0 0 = (-A 0 0 * w ^ 2) * c 0 ^ 2 := by linear_combination (A 0 0 * (w * c 0 + 1)) * hw
    rw [this, hre]; ring
  obtain ⟨r1, hr1, hr1e⟩ := hsq1
  obtain ⟨s1, hs1⟩ := hr1.exists_right_inv
  have hs1u : IsUnit s1 := ⟨⟨s1, r1, by rw [mul_comm]; exact hs1, hs1⟩, rfl⟩
  have hdetB : B.det = (r * s1) ^ 2 * (hyp a₁).det := by
    rw [det_hyp]
    have : r1 ^ 2 * B.det = r ^ 2 * (-a₁ ^ 2) := by linear_combination (-1 : ℤ_[p]) * hrd' - B.det * hr1e
    linear_combination (s1 ^ 2) * this - (B.det * (r1 * s1 + 1)) * hs1
  have hBH : MEq (hyp a₁) B :=
    meq_unimod hp2 (hyp_symm a₁) hBs (by rw [det_hyp]; exact (ha₁.pow 2).neg) (hr.mul hs1u) hdetB
  have hH : (p : ℤ_[p]) • hyp a₁ = hyp ((p : ℤ_[p]) * a₁) := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [hyp]
  have h1 : MEq (hyp ((p : ℤ_[p]) * a₁)) A' := by
    rw [← hH, hA'B]; exact hBH.smul _
  have hmid := meq_blk3 (u := -1) hr1 h1
  have h2 : r1 ^ 2 * (-1 : ℤ_[p]) = A 0 0 := by linear_combination hr1e
  rw [h2] at hmid
  exact hmid.trans hsplit.symm

/-- **The core:** as `meq_core0`, but only requiring some $c_k$ to be a unit (permute the coordinates). -/
theorem meq_core (hp2 : p ≠ 2) {A : Matrix (Fin 3) (Fin 3) ℤ_[p]} (hA : Aᵀ = A) {a₁ : ℤ_[p]}
    (ha₁ : IsUnit a₁) (hdet : A.det = ((p : ℤ_[p]) * a₁) ^ 2) {c : Fin 3 → ℤ_[p]}
    (hc : ∀ i j, (p : ℤ_[p]) ∣ c i * c j + A i j) :
    MEq (blk3 (-1) (hyp ((p : ℤ_[p]) * a₁))) A := by
  obtain ⟨k, hk⟩ := exists_unit_c ha₁ hdet hc
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
  have h := meq_core0 hp2 (submatrix_symm hA σ) ha₁
    (by rw [det_submatrix_equiv_self]; exact hdet) (c := fun i => c (σ i))
    (fun i j => hc (σ i) (σ j)) (by simpa [σ] using hk)
  exact h.trans (meq_perm A σ).symm

/-- **The case $p \mid a$, $p^2 \nmid a$** of Lemma 6.6. -/
theorem meq_G₀_of_dvd (hp2 : p ≠ 2) {a : ℤ} (hpa : (p : ℤ) ∣ a) (hsq : ¬ (p : ℤ) ^ 2 ∣ a)
    {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : Gᵀ = G) (hdet : G.det = a ^ 2)
    (hc : ∃ c : Fin 3 → ℤ, ∀ i j, (p : ℤ) ∣ c i * c j + G i j) :
    MEq ((G₀ a).map (Int.castRingHom ℤ_[p])) (G.map (Int.castRingHom ℤ_[p])) := by
  obtain ⟨a₀, rfl⟩ := hpa
  obtain ⟨c, hc⟩ := hc
  have ha₁ : IsUnit (a₀ : ℤ_[p]) := by
    rw [isUnit_iff_not_dvd, cast_dvd_iff]
    rintro ⟨e, rfl⟩
    exact hsq ⟨e, by ring⟩
  have hB : (G.map (Int.castRingHom ℤ_[p]))ᵀ = G.map (Int.castRingHom ℤ_[p]) := by
    rw [← transpose_map, hG]
  have hdB : (G.map (Int.castRingHom ℤ_[p])).det = ((p : ℤ_[p]) * (a₀ : ℤ_[p])) ^ 2 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]; simp
  have h := meq_core hp2 hB ha₁ hdB (c := fun i => (c i : ℤ_[p])) (fun i j => by
    have := (cast_dvd_iff _).2 (hc i j)
    simpa using this)
  rw [G₀_map_eq]
  simpa using h

/-- **Local classes of the ternary forms of Cassels' Lemma 6.6.** Let $p$ be odd, $a \ne 0$ with $p^2 \nmid a$, and
$G$ a symmetric integral $3\times3$ matrix with $\det G = a^2$ such that, when $p \mid a$, $G \equiv -cc^{\mathsf T}
\pmod p$ for some $c \in \mathbb Z^3$. Then $G_0(a) \sim G$ over $\mathbb Z_p$. -/
theorem meq_G₀ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℤ} (_ha : a ≠ 0) (hsq : ¬ (p : ℤ) ^ 2 ∣ a)
    {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : Gᵀ = G) (hdet : G.det = a ^ 2)
    (hc : ∃ c : Fin 3 → ℤ, ∀ i j, (p : ℤ) ∣ c i * c j + G i j ∨ ¬ (p : ℤ) ∣ a) :
    MEq ((G₀ a).map (Int.castRingHom ℤ_[p])) (G.map (Int.castRingHom ℤ_[p])) := by
  by_cases hpa : (p : ℤ) ∣ a
  · obtain ⟨c, hc⟩ := hc
    exact meq_G₀_of_dvd hp2 hpa hsq hG hdet ⟨c, fun i j => (hc i j).resolve_right (not_not.2 hpa)⟩
  · exact meq_G₀_of_not_dvd hp2 hpa hG hdet

end Padic

end QuadFormsKB.Siegel.CongrLocal
