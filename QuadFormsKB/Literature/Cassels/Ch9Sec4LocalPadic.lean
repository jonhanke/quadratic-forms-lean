/-
# Cassels, Chapter 9, Lemma 4.3: the local statement over $\mathbb Z_p$

**Layer:** symmetric matrices over $\mathbb Z_p$ (Cassels' matrices $f_{ij}$ of classically integral forms), congruence
`MEq` and entrywise divisibility `MDvd` (`Ch9Sec4LocalAlg.lean`).

**Proves** (`meq_of_congr`): if $A, B$ are symmetric over $\mathbb Z_p$, $\det A \ne 0$, $\det A \mid c$,
$B \equiv A \pmod{4c}$ entrywise and $\det B = s^2\det A$ for a unit $s$, then $T^{\mathsf T}AT = B$ for some
$T \in \mathrm{GL}_n(\mathbb Z_p)$. For $c = \det A$ this is the local content of Cassels' Lemma 4.3 (Ch. 9, p. 141).

*Proof.* Induction on $n$. For $p$ odd and $\det A$ a unit: the classification of unimodular forms
(`Lattices.Nbr.isometricGL_of_unimodular_dvr`). Otherwise, if $c$ is not a unit, let $p^\mu$ be the largest power
dividing all entries of $A$; then $p^{\mu+1} \mid c$ (for $n \ge 2$). If a diagonal entry $a = A_{kk}$ has order $\mu$
(after the substitution $e_i \mapsto e_i + e_j$ when $p$ is odd), split it off from $A$ and $B$ (`pivot_reduce`); then
$B_{kk}/a \equiv 1 \pmod{4p}$ is a unit square (Hensel), and the complements are again congruent modulo $4c$. At $p = 2$,
if no diagonal entry has order $\mu$, an entry $A_{ij} = 2^\mu u$ gives an even unimodular binary block $2^{-\mu}A_{\{i,j\}}$,
congruent modulo $4$ to that of $B$, hence equivalent (Hensel for even unimodular forms, via
`Tamagawa.Frames.exists_formF_eq_of_dvd`). If $p = 2$ and $c$ is a unit, $A$ is unimodular with $B \equiv A \pmod 4$: an
even $A$ is handled by the same Hensel lemma; otherwise split off an odd $a = A_{kk}$; if $B_{kk} \not\equiv a \pmod 8$ and
the complement $A'$ has an odd diagonal entry $A'_{ll}$, first replace $e_k$ by $e_k + 2e_l$ in the split form of $B$
(this changes $b$ to $b + 4B'_{ll} \equiv a \pmod 8$ and the complement only modulo $4$); if $A'$ is even its
equivalence to $B'$ forces $B_{kk}/a$ to be a square through the determinants. Indices are 0-based.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4LocalAlg
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.Tamagawa.FrameHensel
import QuadFormsKB.Siegel.ThetaCuspidal

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel.CongrLocal

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Elementary facts on $\mathbb Z_p$ -/

/-- In $\mathbb Z_p$ the units are the elements not divisible by $p$. -/
theorem isUnit_iff_not_dvd (x : ℤ_[p]) : IsUnit x ↔ ¬ (p : ℤ_[p]) ∣ x := by
  rw [PadicInt.isUnit_iff, ← PadicInt.norm_lt_one_iff_dvd]
  constructor
  · intro h; rw [h]; exact lt_irrefl 1
  · intro h; exact le_antisymm (PadicInt.norm_le_one x) (not_lt.1 h)

/-- $p \mid x$ iff $x \equiv 0$ in $\mathbb Z/p$. -/
theorem dvd_iff_toZMod (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- In $\mathbb Z/2$ the sum of two nonzero elements is $0$. -/
theorem zmod2_add : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0 := by decide

/-- In $\mathbb Z_2$ the sum of two odd elements is even. -/
theorem dvd_add_of_not_dvd (hp2 : p = 2) {x y : ℤ_[p]} (hx : ¬ (p : ℤ_[p]) ∣ x) (hy : ¬ (p : ℤ_[p]) ∣ y) :
    (p : ℤ_[p]) ∣ x + y := by
  rw [dvd_iff_toZMod] at hx hy ⊢
  rw [map_add]
  generalize PadicInt.toZMod x = a at hx
  generalize PadicInt.toZMod y = b at hy
  subst hp2
  exact zmod2_add a b hx hy

/-- **Hensel for squares:** a $u \equiv 1 \pmod{4p}$ is the square of a unit. -/
theorem exists_sq_of_dvd {u : ℤ_[p]} (h : 4 * (p : ℤ_[p]) ∣ u - 1) : ∃ r : ℤ_[p], IsUnit r ∧ u = r ^ 2 := by
  obtain ⟨w, hw⟩ := h
  have hu1 : 1 - u = 2 * 2 * (p : ℤ_[p]) * (-w) := by linear_combination -hw
  have h2pos : 0 < ‖(2 : ℤ_[p])‖ := norm_pos_iff.2 two_ne_zero
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hnorm : ‖(1 - u : ℤ_[p])‖ < ‖(2 : ℤ_[p])‖ ^ 2 := by
    rw [hu1, norm_mul, norm_mul, norm_mul, PadicInt.norm_p]
    have hw1 : ‖-w‖ ≤ 1 := PadicInt.norm_le_one _
    have hpp : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.out.pos)
    calc ‖(2 : ℤ_[p])‖ * ‖(2 : ℤ_[p])‖ * (p : ℝ)⁻¹ * ‖-w‖ ≤ ‖(2 : ℤ_[p])‖ * ‖(2 : ℤ_[p])‖ * (p : ℝ)⁻¹ * 1 := by
          gcongr
      _ < ‖(2 : ℤ_[p])‖ * ‖(2 : ℤ_[p])‖ * 1 := by
          rw [mul_one, mul_one]; exact mul_lt_of_lt_one_right (mul_pos h2pos h2pos) hp1
      _ = ‖(2 : ℤ_[p])‖ ^ 2 := by ring
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := p) (R := ℤ_[p]) (F := Polynomial.X ^ 2 - Polynomial.C u) (a := 1)
    (by simpa [Algebra.algebraMap_self, one_add_one_eq_two] using hnorm)
  have hz' : u = z ^ 2 := by simp at hz; linear_combination -hz
  have huu : IsUnit u := by
    rw [isUnit_iff_not_dvd]
    intro hd
    have : (p : ℤ_[p]) ∣ 1 := by
      have h' : (1 : ℤ_[p]) = u - 2 * 2 * p * w := by linear_combination -hw
      rw [h']; exact dvd_sub hd (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one this)
  exact ⟨z, (isUnit_pow_iff two_ne_zero).1 (hz' ▸ huu), hz'⟩

/-! ### Forms with a prescribed Hessian -/

section QOf

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The form with off-diagonal coefficients $M_{ij}$ ($i < j$) and diagonal coefficients $h_i$; its Hessian is $M$
when $M$ is symmetric with $M_{ii} = 2h_i$ (`hessian_qOf`). -/
def qOf (M : Matrix (Fin n) (Fin n) R) (h : Fin n → R) : QuadForm R n :=
  QuadForm.ofUpper fun i j => if i = j then h i else M i j

/-- The Hessian of `qOf M h` is $M$. -/
theorem hessian_qOf {M : Matrix (Fin n) (Fin n) R} (hM : Mᵀ = M) {h : Fin n → R} (hh : ∀ i, M i i = 2 * h i) :
    (qOf M h).hessian = M := by
  ext i j
  simp only [QuadForm.hessian, qOf, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij.le, hij.ne, not_le.2 hij]
  · simp [hh]; ring
  · simp only [not_le.2 hij, hij.le, ite_false, ite_true, hij.ne, hij.ne', zero_add]
    rw [← transpose_apply M i j, hM]

/-- An equivalence of forms gives a congruence of their Hessians. -/
theorem meq_of_isometricGL {Q Q' : QuadForm R n} (h : IsometricGL Q Q') : MEq Q.hessian Q'.hessian := by
  obtain ⟨g, hg⟩ := h.hessian_eq
  exact ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit, hg⟩

end QOf

/-! ### Hensel for even unimodular matrices -/

/-- **Hensel for even unimodular matrices** (Fin version): if $K$ is symmetric with even diagonal and unit
determinant and $K' \equiv K \pmod{2p}$ is symmetric, then $K \sim K'$. -/
theorem meq_even_fin {r : ℕ} {K K' : Matrix (Fin r) (Fin r) ℤ_[p]} (hK : Kᵀ = K) (hK' : K'ᵀ = K')
    (hev : ∀ i, (2 : ℤ_[p]) ∣ K i i) (hu : IsUnit K.det) (hd : MDvd (2 * (p : ℤ_[p])) (K' - K)) : MEq K K' := by
  choose h hh using hev
  choose w hw using fun i => hd i i
  set h' : Fin r → ℤ_[p] := fun i => h i + p * w i
  have hh' : ∀ i, K' i i = 2 * h' i := fun i => by
    have := hw i; rw [Matrix.sub_apply, hh i] at this
    simp only [h']; linear_combination this
  set Q := qOf K' h'
  set T := qOf K h
  have hQ : Q.hessian = K' := hessian_qOf hK' hh'
  have hT : T.hessian = K := hessian_qOf hK hh
  have hTu : ¬ (p : ℤ_[p]) ^ (0 + 1) ∣ T.hessian.det := by
    rw [hT, zero_add, pow_one, ← isUnit_iff_not_dvd]; exact hu
  set x : Fin r × Fin r → ℤ_[p] := fun li => (1 : Matrix (Fin r) (Fin r) ℤ_[p]) li.1 li.2
  have hx1 : LocalDensity.DVR.toMat x = 1 := by ext i j; rfl
  have hcong : ∀ q : LocalDensity.DVR.UpperIdx r,
      (p : ℤ_[p]) ^ 1 ∣ LocalDensity.DVR.formF Q x q - Tamagawa.Frames.tc T q := by
    intro q
    rw [pow_one]
    simp only [LocalDensity.DVR.formF, hx1, QuadForm.compMat_one, Tamagawa.Frames.tc, Q, T, qOf,
      QuadForm.ofUpper, Matrix.of_apply, if_pos q.2]
    by_cases hij : q.1.1 = q.1.2
    · simp only [if_pos hij, h']; ring_nf; exact dvd_mul_right _ _
    · simp only [if_neg hij]
      have := hd q.1.1 q.1.2
      rw [Matrix.sub_apply] at this
      exact (dvd_mul_left _ _).trans this
  obtain ⟨y, hy, -⟩ := Tamagawa.Frames.exists_formF_eq_of_dvd PadicInt.irreducible_p Q T (d := 0) (K := 1)
    (by simp) hTu (by norm_num) x hcong
  rw [Tamagawa.Frames.formF_eq_tc_iff] at hy
  have hH := congrArg QuadForm.hessian hy
  rw [QuadForm.hessian_compMat, hQ, hT] at hH
  set Y := LocalDensity.DVR.toMat y
  have hYu : IsUnit Y.det := by
    have hdet := congrArg Matrix.det hH
    rw [det_mul, det_mul, det_transpose] at hdet
    rw [← hdet] at hu
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
  exact (MEq.symm ⟨Y, hYu, hH⟩)

/-- **Unimodular forms for $p$ odd** (Fin version): symmetric $A, B$ with $\det A$ a unit and
$\det B = s^2\det A$ are congruent. -/
theorem meq_unimod_fin (hp2 : p ≠ 2) {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hu : IsUnit A.det) {s : ℤ_[p]} (hs : IsUnit s) (hdet : B.det = s ^ 2 * A.det) : MEq A B := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofEquiv (ZMod p) PadicInt.residueField.symm.toEquiv
  have h2A : ((2 : ℤ_[p]) • A)ᵀ = (2 : ℤ_[p]) • A := by rw [transpose_smul, hA]
  have h2B : ((2 : ℤ_[p]) • B)ᵀ = (2 : ℤ_[p]) • B := by rw [transpose_smul, hB]
  set Q := qOf ((2 : ℤ_[p]) • A) (fun i => A i i)
  set Q' := qOf ((2 : ℤ_[p]) • B) (fun i => B i i)
  have hQ : Q.hessian = (2 : ℤ_[p]) • A := hessian_qOf h2A (fun i => by simp [two_mul])
  have hQ' : Q'.hessian = (2 : ℤ_[p]) • B := hessian_qOf h2B (fun i => by simp [two_mul])
  have h2u : IsUnit (2 : ℤ_[p]) := (isUnit_iff_not_dvd 2).2 (Kneser.not_p_dvd_two hp2)
  have hiso := Lattices.Nbr.isometricGL_of_unimodular_dvr PadicInt.irreducible_p (Kneser.not_p_dvd_two hp2) Q Q'
    (by rw [hQ, det_smul, ← isUnit_iff_not_dvd]; exact (h2u.pow _).mul hu) hs
    (by rw [hQ, hQ', det_smul, det_smul, hdet]; ring)
  obtain ⟨T, hT, hTe⟩ := meq_of_isometricGL hiso
  rw [hQ, hQ', Matrix.mul_smul, Matrix.smul_mul] at hTe
  refine ⟨T, hT, ?_⟩
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun hTe i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[p]) ≠ 0) this

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Hensel for even unimodular matrices:** if $K$ is symmetric with even diagonal and unit determinant and
$K' \equiv K \pmod{2p}$ is symmetric, then $K \sim K'$. -/
theorem meq_even {K K' : Matrix ι ι ℤ_[p]} (hK : Kᵀ = K) (hK' : K'ᵀ = K')
    (hev : ∀ i, (2 : ℤ_[p]) ∣ K i i) (hu : IsUnit K.det) (hd : MDvd (2 * (p : ℤ_[p])) (K' - K)) : MEq K K' := by
  let e := (Fintype.equivFin ι).symm
  apply MEq.of_submatrix e
  exact meq_even_fin (submatrix_symm hK e) (submatrix_symm hK' e) (fun i => hev (e i))
    (by rw [det_submatrix_equiv_self]; exact hu) (fun i j => hd (e i) (e j))

/-- **Unimodular matrices for $p$ odd:** symmetric $A, B$ with $\det A$ a unit and $\det B = s^2\det A$ are
congruent. -/
theorem meq_unimod (hp2 : p ≠ 2) {A B : Matrix ι ι ℤ_[p]} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hu : IsUnit A.det) {s : ℤ_[p]} (hs : IsUnit s) (hdet : B.det = s ^ 2 * A.det) : MEq A B := by
  let e := (Fintype.equivFin ι).symm
  apply MEq.of_submatrix e
  exact meq_unimod_fin hp2 (submatrix_symm hA e) (submatrix_symm hB e)
    (by rw [det_submatrix_equiv_self]; exact hu) hs (by rw [det_submatrix_equiv_self, det_submatrix_equiv_self, hdet])

end General

/-! ### The induction -/

/-- The local statement for matrices indexed by `ι`: symmetric $A, B$ with $\det A \ne 0$, $\det A \mid c$,
$B \equiv A \pmod{4c}$ and $\det B = s^2 \det A$ ($s$ a unit) are congruent. -/
def Claim (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (A B : Matrix ι ι ℤ_[p]) (c : ℤ_[p]), Aᵀ = A → Bᵀ = B → A.det ≠ 0 → A.det ∣ c →
    MDvd (4 * c) (B - A) → (∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) → MEq A B

/-- The induction hypothesis: `Claim` for all index types of smaller cardinality. -/
def ClaimBelow (p : ℕ) [Fact p.Prime] (N : ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < N → Claim p κ

section Steps

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The $1$-dimensional pivot** at $k$: if $t$ divides all entries, $A_{kk} = tu$ ($u$ a unit), $t \mid c$ and
$B_{kk} = vA_{kk}$ with $v \equiv 1 \pmod{4p}$, then $A \sim B$ (given the claim in smaller dimension). -/
theorem pivot1 (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]} {c : ℤ_[p]} (hA : Aᵀ = A)
    (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c) (hBA : MDvd (4 * c) (B - A))
    (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) (k : ι) {t u : ℤ_[p]} (ht : ∀ i j, t ∣ A i j)
    (htc : t ∣ c) (hk : A k k = t * u) (hu : IsUnit u)
    (hv : ∃ v : ℤ_[p], 4 * (p : ℤ_[p]) ∣ v - 1 ∧ B k k = v * A k k) : MEq A B := by
  let K₀ : Matrix {x // x = k} {x // x = k} ℤ_[p] := u • 1
  have hsub : ∀ i j : {x // x = k}, i = j := fun i j => Subtype.ext (i.2.trans j.2.symm)
  obtain ⟨v, hv1, hvk⟩ := hv
  obtain ⟨r, hr, hvr⟩ := exists_sq_of_dvd hv1
  refine pivot_reduce (· = k) hA hB hA0 hdet (t := t) (m := 4 * c) K₀ (by simp [K₀])
    (by simp only [K₀, det_smul, det_one, mul_one]; exact hu.pow _)
    (fun i j => by obtain rfl := hsub i j; simp only [K₀, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
                   rw [i.2]; exact hk) (fun i j => ht _ _)
    (dvd_mul_of_dvd_right htc 4) hBA ?_ ?_
  · have : (B.submatrix (fun x : {x // x = k} => x.1) (fun x : {x // x = k} => x.1)) =
        r ^ 2 • (A.submatrix (fun x : {x // x = k} => x.1) (fun x : {x // x = k} => x.1)) := by
      refine Matrix.ext fun i j => ?_
      simp only [submatrix_apply, Matrix.smul_apply, smul_eq_mul, i.2, j.2, hvk, hvr]
    rw [this]; convert MEq.smul_sq _ hr
  · intro A' B' hA' hB' hA'0 hdvd hBA' hdet'
    exact IH _ (Fintype.card_subtype_lt (x := k) (by simp)) A' B' c hA' hB' hA'0 (hdvd.trans hc) hBA' hdet'

/-- The determinant of a matrix indexed by the two-element type $\{i, j\}$. -/
theorem det_pair {R : Type*} [CommRing R] {i j : ι} (hij : i ≠ j) [Fintype {x // x = i ∨ x = j}]
    (M : Matrix {x // x = i ∨ x = j} {x // x = i ∨ x = j} R) :
    M.det = M ⟨i, Or.inl rfl⟩ ⟨i, Or.inl rfl⟩ * M ⟨j, Or.inr rfl⟩ ⟨j, Or.inr rfl⟩ -
      M ⟨i, Or.inl rfl⟩ ⟨j, Or.inr rfl⟩ * M ⟨j, Or.inr rfl⟩ ⟨i, Or.inl rfl⟩ := by
  let f : Fin 2 → {x // x = i ∨ x = j} := ![⟨i, Or.inl rfl⟩, ⟨j, Or.inr rfl⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      fin_cases x <;> fin_cases y <;> simp_all [f, Subtype.ext_iff, eq_comm]
    · intro x
      rcases x.2 with h | h
      · exact ⟨0, Subtype.ext (by simp [f, h])⟩
      · exact ⟨1, Subtype.ext (by simp [f, h])⟩
  rw [← det_submatrix_equiv_self (Equiv.ofBijective f hf) M, det_fin_two]
  simp [f]

/-- **The $2$-dimensional pivot** at $p = 2$ on $\{i, j\}$: if $t$ divides all entries, $A_{ij} = tu$ ($u$ a
unit) and $2t \mid A_{ii}, A_{jj}$, $t \mid c$, then $A \sim B$ (given the claim in smaller dimension). -/
theorem pivot2 (hp2 : p = 2) (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]} {c : ℤ_[p]}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c) (hBA : MDvd (4 * c) (B - A))
    (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) {i j : ι} (hij : i ≠ j) {t u : ℤ_[p]} (ht0 : t ≠ 0)
    (ht : ∀ a b, t ∣ A a b) (htc : t ∣ c) (hAij : A i j = t * u) (hu : IsUnit u)
    (hii : t * p ∣ A i i) (hjj : t * p ∣ A j j) : MEq A B := by
  have h2 : ((p : ℕ) : ℤ_[p]) = 2 := by subst hp2; norm_num
  have hsymA : ∀ a b, A a b = A b a := fun a b => by rw [← transpose_apply A a b, hA]
  have hsymB : ∀ a b, B a b = B b a := fun a b => by rw [← transpose_apply B a b, hB]
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Matrix ι ι ℤ_[p], ∀ a b, A a b = t * A₀ a b :=
    ⟨Matrix.of fun a b => (ht a b).choose, fun a b => (ht a b).choose_spec⟩
  obtain ⟨c', rfl⟩ := htc
  have htB : ∀ a b, t ∣ B a b := fun a b => by
    have h1 := hBA a b
    rw [Matrix.sub_apply] at h1
    have h3 : t ∣ 4 * (t * c') := ⟨4 * c', by ring⟩
    simpa using dvd_add (h3.trans h1) (ht a b)
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Matrix ι ι ℤ_[p], ∀ a b, B a b = t * B₀ a b :=
    ⟨Matrix.of fun a b => (htB a b).choose, fun a b => (htB a b).choose_spec⟩
  have hA₀s : ∀ a b, A₀ a b = A₀ b a := fun a b => mul_left_cancel₀ ht0 (by rw [← hA₀, ← hA₀, hsymA])
  have hB₀s : ∀ a b, B₀ a b = B₀ b a := fun a b => mul_left_cancel₀ ht0 (by rw [← hB₀, ← hB₀, hsymB])
  have hd₀ : ∀ a b, 4 * c' ∣ B₀ a b - A₀ a b := fun a b => by
    have h1 := hBA a b
    rw [Matrix.sub_apply, hA₀, hB₀, ← mul_sub, show 4 * (t * c') = t * (4 * c') by ring] at h1
    exact (mul_dvd_mul_iff_left ht0).1 h1
  let P : ι → Prop := fun x => x = i ∨ x = j
  let K₀ : Matrix {x // P x} {x // P x} ℤ_[p] := A₀.submatrix (fun x => x.1) (fun x => x.1)
  let K₀' : Matrix {x // P x} {x // P x} ℤ_[p] := B₀.submatrix (fun x => x.1) (fun x => x.1)
  have hK₀s : K₀ᵀ = K₀ := Matrix.ext fun a b => (hA₀s b.1 a.1)
  have hK₀'s : K₀'ᵀ = K₀' := Matrix.ext fun a b => (hB₀s b.1 a.1)
  have hev : ∀ a : {x // P x}, (p : ℤ_[p]) ∣ K₀ a a := by
    rintro ⟨a, ha | ha⟩ <;> subst ha
    · exact (mul_dvd_mul_iff_left ht0).1 (by show _ ∣ t * A₀ _ _; rw [← hA₀]; exact hii)
    · exact (mul_dvd_mul_iff_left ht0).1 (by show _ ∣ t * A₀ _ _; rw [← hA₀]; exact hjj)
  have hu₀ : A₀ i j = u := mul_left_cancel₀ ht0 (by rw [← hA₀, hAij])
  have hdetK : IsUnit K₀.det := by
    rw [det_pair hij, isUnit_iff_not_dvd]
    intro hd
    have h1 : (p : ℤ_[p]) ∣ K₀ ⟨i, Or.inl rfl⟩ ⟨i, Or.inl rfl⟩ * K₀ ⟨j, Or.inr rfl⟩ ⟨j, Or.inr rfl⟩ :=
      dvd_mul_of_dvd_left (hev _) _
    have h3 := dvd_sub h1 hd
    simp only [sub_sub_cancel, K₀, submatrix_apply] at h3
    rw [hA₀s j i, hu₀] at h3
    exact (isUnit_iff_not_dvd u).1 hu ((PadicInt.prime_p.dvd_or_dvd h3).elim id id)
  refine pivot_reduce P hA hB hA0 hdet (t := t) (m := 4 * (t * c')) K₀ hK₀s hdetK (fun a b => hA₀ _ _)
    (fun a b => ht _ _) ⟨4 * c', by ring⟩ hBA ?_ ?_
  · have e1 : (A.submatrix (fun x : {x // P x} => x.1) (fun x : {x // P x} => x.1)) = t • K₀ :=
      Matrix.ext fun a b => by simp [K₀, hA₀]
    have e2 : (B.submatrix (fun x : {x // P x} => x.1) (fun x : {x // P x} => x.1)) = t • K₀' :=
      Matrix.ext fun a b => by simp [K₀', hB₀]
    rw [e1, e2]
    refine MEq.smul ?_ t
    refine meq_even hK₀s hK₀'s (fun a => by rw [← h2]; exact hev a) hdetK (fun a b => ?_)
    rw [h2, show (2 : ℤ_[p]) * 2 = 4 by norm_num]
    exact (dvd_mul_right 4 c').trans (hd₀ a.1 b.1)
  · intro A' B' hA' hB' hA'0 hdvd hBA' hdet'
    exact IH _ (Fintype.card_subtype_lt (x := i) (by simp [P])) A' B' _ hA' hB' hA'0 (hdvd.trans hc) hBA'
      hdet'

end Steps

/-! ### The induction step: elementary lemmas -/

section Ind

/-- A $\mathbb Z_p$-element congruent mod $p$ to a unit is a unit. -/
theorem isUnit_of_dvd_sub' {a x : ℤ_[p]} (ha : IsUnit a) (h : (p : ℤ_[p]) ∣ x - a) : IsUnit x := by
  rw [isUnit_iff_not_dvd] at ha ⊢
  intro hx
  exact ha (by simpa using dvd_sub hx h)

/-- If $a$ is a unit and $4p \mid b - a$ then $b = va$ with $4p \mid v - 1$. -/
theorem exists_v {a b : ℤ_[p]} (ha : IsUnit a) (h : 4 * (p : ℤ_[p]) ∣ b - a) :
    ∃ v : ℤ_[p], 4 * (p : ℤ_[p]) ∣ v - 1 ∧ b = v * a := by
  obtain ⟨a', ha'⟩ := ha.exists_right_inv
  refine ⟨b * a', ?_, by linear_combination (-b) * ha'⟩
  have : b * a' - 1 = (b - a) * a' := by linear_combination ha'
  rw [this]; exact dvd_mul_of_dvd_left h _

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Pivot on a unit diagonal entry when $p \mid c$.** -/
theorem step_pivot_dvd (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]} {c : ℤ_[p]}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c) (hBA : MDvd (4 * c) (B - A))
    (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) (hpc : (p : ℤ_[p]) ∣ c) (k : ι)
    (hk : IsUnit (A k k)) : MEq A B := by
  refine pivot1 IH hA hB hA0 hc hBA hdet k (t := 1) (u := A k k) (fun _ _ => one_dvd _) (one_dvd _)
    (by simp) hk (exists_v hk ?_)
  have := hBA k k
  rw [Matrix.sub_apply] at this
  exact (mul_dvd_mul_left 4 hpc).trans this

/-- **Pivot on a unit diagonal entry after a transvection** ($p$ odd, $p \mid c$, no unit diagonal entry). -/
theorem step_pivot_odd (hp2 : p ≠ 2) (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]}
    {c : ℤ_[p]} (hA : Aᵀ = A) (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c)
    (hBA : MDvd (4 * c) (B - A)) (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det)
    (hpc : (p : ℤ_[p]) ∣ c) {i j : ι} (hij : IsUnit (A i j)) (hdiag : ∀ k, ¬ IsUnit (A k k)) : MEq A B := by
  have hne : i ≠ j := by
    rintro rfl; exact hdiag _ hij
  set P : Matrix ι ι ℤ_[p] := transvection j i 1 with hPdef
  have hP1 : P.det = 1 := by rw [hPdef, det_transvection_of_ne _ _ hne.symm]
  have hPd : IsUnit P.det := by rw [hP1]; exact isUnit_one
  have hPt : Pᵀ = transvection i j 1 := by
    simp [hPdef, transvection, Matrix.transpose_single]
  have hsymA : ∀ a b, A a b = A b a := fun a b => by rw [← transpose_apply A a b, hA]
  apply MEq.conj_both P hPd
  obtain ⟨s, hs, hsd⟩ := hdet
  have hdA : (Pᵀ * A * P).det = A.det := by
    rw [det_mul, det_mul, det_transpose, hP1]; simp
  have hdB : (Pᵀ * B * P).det = s ^ 2 * A.det := by
    rw [det_mul, det_mul, det_transpose, hP1, ← hsd]; simp
  have hAs : (Pᵀ * A * P)ᵀ = Pᵀ * A * P := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hA, Matrix.mul_assoc]
  have hBs : (Pᵀ * B * P)ᵀ = Pᵀ * B * P := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hB, Matrix.mul_assoc]
  have hdiffs : Pᵀ * B * P - Pᵀ * A * P = Pᵀ * (B - A) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  have hd1 : (Pᵀ * A * P) i i = A i i + 2 * A i j + A j j := by
    rw [hPt, Matrix.mul_assoc]
    simp only [hPdef, transvection_mul_apply_same, mul_transvection_apply_same]
    rw [hsymA j i]; ring
  have hu1 : IsUnit ((Pᵀ * A * P) i i) := by
    rw [isUnit_iff_not_dvd, hd1]
    intro hd
    have h2 : (p : ℤ_[p]) ∣ A i i := by
      have := hdiag i; rwa [isUnit_iff_not_dvd, not_not] at this
    have h3 : (p : ℤ_[p]) ∣ A j j := by
      have := hdiag j; rwa [isUnit_iff_not_dvd, not_not] at this
    have h4 : (p : ℤ_[p]) ∣ 2 * A i j := by
      have := dvd_sub (dvd_sub hd h2) h3
      convert this using 1; ring
    rcases PadicInt.prime_p.dvd_or_dvd h4 with h5 | h5
    · exact Kneser.not_p_dvd_two hp2 h5
    · exact (isUnit_iff_not_dvd _).1 hij h5
  exact step_pivot_dvd IH hAs hBs (by rw [hdA]; exact hA0) (by rw [hdA]; exact hc)
    (by rw [hdiffs]; exact ((hBA.mul_left _).mul_right _)) ⟨s, hs, by rw [hdB, hdA]⟩ hpc i hu1

end Ind

/-! ### The $2$-adic core: a $1\times 1$ block next to a unimodular block -/

section Core

variable {α κ : Type} [Fintype α] [DecidableEq α] [Subsingleton α] [Nonempty α] [Fintype κ] [DecidableEq κ]

/-- The determinant of $a\cdot I$ on a one-point index type is $a$. -/
theorem det_smul_one_unique (a : ℤ_[p]) : ((a • 1 : Matrix α α ℤ_[p])).det = a := by
  rw [det_smul, det_one, mul_one, Fintype.card_eq_one_iff.2 (by
    obtain ⟨x⟩ := ‹Nonempty α›; exact ⟨x, fun y => Subsingleton.elim y x⟩), pow_one]

/-- Two $1\times1$ matrices whose determinants differ by a unit square are congruent. -/
theorem meq_one_of_detRel {a b : ℤ_[p]} (h : DetRel (a • 1 : Matrix α α ℤ_[p]) (b • 1)) :
    MEq (a • 1 : Matrix α α ℤ_[p]) (b • 1) := by
  obtain ⟨q, hq, e⟩ := h
  rw [det_smul_one_unique, det_smul_one_unique] at e
  have := MEq.smul_sq (a • 1 : Matrix α α ℤ_[p]) hq
  rwa [smul_smul, ← e] at this

/-- **The $2$-adic core of Lemma 4.3 (case $p = 2$, $c$ a unit).** An orthogonal sum
$\langle a\rangle \oplus A'$ with $A'$ unimodular is congruent to $\langle b\rangle \oplus B'$ when $B' \equiv A'
\pmod 4$, $b \equiv a + 4 \pmod 8$, the determinants differ by a unit square, and the claim holds for $\kappa$. -/
theorem core_two (hp2 : p = 2) (hC : Claim p κ) {a b : ℤ_[p]} (ha : IsUnit a) (hab : 8 ∣ b - a - 4)
    {A' B' : Matrix κ κ ℤ_[p]} (hA' : A'ᵀ = A') (hB' : B'ᵀ = B') (hu : IsUnit A'.det)
    (h4 : MDvd 4 (B' - A'))
    (hD : DetRel (Matrix.fromBlocks (a • 1 : Matrix α α ℤ_[p]) 0 0 A')
      (Matrix.fromBlocks (b • 1 : Matrix α α ℤ_[p]) 0 0 B')) :
    MEq (Matrix.fromBlocks (a • 1 : Matrix α α ℤ_[p]) 0 0 A')
      (Matrix.fromBlocks (b • 1 : Matrix α α ℤ_[p]) 0 0 B') := by
  have h2 : ((p : ℕ) : ℤ_[p]) = 2 := by subst hp2; norm_num
  have h22 : (2 : ℤ_[p]) * 2 = 4 := by norm_num
  have ha0 : (a • 1 : Matrix α α ℤ_[p]).det ≠ 0 := by
    rw [det_smul_one_unique]; exact ha.ne_zero
  by_cases hev : ∀ l, (p : ℤ_[p]) ∣ A' l l
  · have hAB : MEq A' B' := meq_even hA' hB' (fun l => by rw [← h2]; exact hev l) hu
      (fun i j => by rw [h2, h22]; exact h4 i j) |>.symm.symm
    exact MEq.fromBlocks (meq_one_of_detRel (hD.first hAB.detRel hu.ne_zero)) hAB
  · push_neg at hev
    obtain ⟨l, hl⟩ := hev
    have h4p : (p : ℤ_[p]) ∣ 4 := ⟨2, by rw [h2]; norm_num⟩
    have hBl : ¬ (p : ℤ_[p]) ∣ B' l l := by
      intro h
      apply hl
      have h' := dvd_sub h (h4p.trans (h4 l l))
      simpa using h'
    set b' : ℤ_[p] := b + 4 * B' l l with hb'
    have hp1 : ¬ (p : ℤ_[p]) ∣ 1 := (isUnit_iff_not_dvd 1).1 isUnit_one
    obtain ⟨y, hy⟩ := dvd_add_of_not_dvd hp2 hp1 hBl
    have hb'a : 4 * (p : ℤ_[p]) ∣ b' - a := by
      obtain ⟨z, hz⟩ := hab
      refine ⟨z + y, ?_⟩
      rw [h2]
      have : b' - a = (b - a - 4) + 4 * (1 + B' l l) := by rw [hb']; ring
      rw [this, hz, hy, h2]; ring
    have hb'u : IsUnit b' := isUnit_of_dvd_sub' ha ((dvd_mul_left _ 4).trans hb'a)
    obtain ⟨v, hv, hvb⟩ := exists_v ha hb'a
    obtain ⟨r, hr, hvr⟩ := exists_sq_of_dvd hv
    have hab' : MEq (a • 1 : Matrix α α ℤ_[p]) (b' • 1) :=
      meq_one_of_detRel ⟨r, hr, by rw [det_smul_one_unique, det_smul_one_unique, hvb, hvr]⟩
    -- the twist
    let Y : Matrix κ α ℤ_[p] := Matrix.of fun i _ => if i = l then 2 else 0
    have hYNY : Yᵀ * B' * Y = (4 * B' l l) • (1 : Matrix α α ℤ_[p]) := by
      ext x y
      obtain rfl := Subsingleton.elim x y
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Y, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_const_zero, mul_one, Finset.sum_const, Finset.card_univ,
        one_smul]
      ring
    have hTw := twist_eq ((b • 1 : Matrix α α ℤ_[p])) B' Y
    rw [hYNY, ← add_smul] at hTw
    set K₀ : Matrix α α ℤ_[p] := b' • 1 with hK₀
    have hK₀s : K₀ᵀ = K₀ := by simp [hK₀]
    have hK₀u : IsUnit K₀.det := by rw [hK₀, det_smul_one_unique]; exact hb'u
    set C₀ : Matrix α κ ℤ_[p] := Yᵀ * B' with hC₀
    have hC₀t : C₀ᵀ = B' * Y := by rw [hC₀, transpose_mul, transpose_transpose, hB']
    have hpiv := meq_pivot 1 hK₀s hK₀u C₀ B'
    simp only [one_smul] at hpiv
    have hTw' : MEq (Matrix.fromBlocks (b • 1 : Matrix α α ℤ_[p]) 0 0 B')
        (Matrix.fromBlocks K₀ C₀ C₀ᵀ B') := by
      refine ⟨Matrix.fromBlocks 1 0 Y 1, by rw [det_twist]; exact isUnit_one, ?_⟩
      rw [hTw, hC₀t]
    set B'' : Matrix κ κ ℤ_[p] := B' - C₀ᵀ * K₀⁻¹ * C₀ with hB''
    have hB''s : B''ᵀ = B'' := by
      have := compl_symm hB' hK₀s 1 C₀
      simpa only [one_smul] using this
    have hY2 : MDvd 2 Y := fun i x => by
      simp only [Y, Matrix.of_apply]; split_ifs
      · exact dvd_rfl
      · exact dvd_zero _
    have hC2 : MDvd 2 C₀ := (hY2.transpose).mul_right B'
    have hcomp : MDvd 4 (C₀ᵀ * K₀⁻¹ * C₀) := by
      have := ((hC2.transpose).mul_right K₀⁻¹).mul hC2
      rwa [h22] at this
    have hB''A : MDvd (4 * 1) (B'' - A') := by
      rw [mul_one]
      have : B'' - A' = (B' - A') - C₀ᵀ * K₀⁻¹ * C₀ := by rw [hB'']; abel
      rw [this]; exact h4.sub hcomp
    have hDR : DetRel (Matrix.fromBlocks (a • 1 : Matrix α α ℤ_[p]) 0 0 A')
        (Matrix.fromBlocks K₀ 0 0 B'') := hD.trans (hTw'.trans hpiv).detRel
    have hdr : DetRel A' B'' := hDR.compl hab'.detRel ha0
    have hAB'' : MEq A' B'' :=
      hC A' B'' 1 hA' hB''s hu.ne_zero (by simp [isUnit_iff_dvd_one.1 hu |> fun h => h])
        hB''A (hdr)
    exact (MEq.fromBlocks hab' hAB'').trans (hpiv.symm.trans hTw'.symm)

end Core

section TwoUnit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The case $p = 2$, $c$ a unit, with an odd diagonal entry** $A_{kk}$. -/
theorem step_two_unit (hp2 : p = 2) (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]}
    {c : ℤ_[p]} (hA : Aᵀ = A) (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c)
    (hBA : MDvd (4 * c) (B - A)) (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det)
    (hcu : IsUnit c) (k : ι) (hk : IsUnit (A k k)) : MEq A B := by
  have h2 : ((p : ℕ) : ℤ_[p]) = 2 := by subst hp2; norm_num
  have h4 : MDvd 4 (B - A) := fun i j => (dvd_mul_right 4 c).trans (hBA i j)
  have hba : 4 ∣ B k k - A k k := by simpa using h4 k k
  by_cases h8 : 8 ∣ B k k - A k k
  · refine pivot1 IH hA hB hA0 hc hBA hdet k (t := 1) (u := A k k) (fun _ _ => one_dvd _) (one_dvd _)
      (by simp) hk (exists_v hk ?_)
    rw [h2]; convert h8 using 1; norm_num
  have hp1 : ¬ (p : ℤ_[p]) ∣ -1 := by
    rw [dvd_neg]; exact (isUnit_iff_not_dvd 1).1 isUnit_one
  have hba0 := hba
  have h4p : (p : ℤ_[p]) ∣ 4 := ⟨2, by rw [h2]; norm_num⟩
  have hpba : (p : ℤ_[p]) ∣ B k k - A k k := h4p.trans hba
  obtain ⟨w, hw⟩ := hba
  have hwo : ¬ (p : ℤ_[p]) ∣ w := by
    rintro ⟨w', rfl⟩
    exact h8 ⟨w', by rw [hw, h2]; ring⟩
  obtain ⟨y, hy⟩ := dvd_add_of_not_dvd hp2 hwo hp1
  have hab : 8 ∣ B k k - A k k - 4 := ⟨y, by
    rw [hw, h2] at *
    linear_combination 4 * hy⟩
  obtain ⟨s, hs, hsd⟩ := hdet
  have hAu : IsUnit A.det := isUnit_of_dvd_unit hc hcu
  letI : Fintype {x // x = k} := Subtype.fintype _
  haveI : Subsingleton {x // x = k} := ⟨fun i j => Subtype.ext (i.2.trans j.2.symm)⟩
  haveI : Nonempty {x // x = k} := ⟨⟨k, rfl⟩⟩
  let K₀ : Matrix {x // x = k} {x // x = k} ℤ_[p] := (A k k) • 1
  let K₀' : Matrix {x // x = k} {x // x = k} ℤ_[p] := (B k k) • 1
  let C₀ : Matrix {x // x = k} {x // ¬ x = k} ℤ_[p] := Matrix.of fun i j => A i.1 j.1
  let C₀' : Matrix {x // x = k} {x // ¬ x = k} ℤ_[p] := Matrix.of fun i j => B i.1 j.1
  have hKA : ∀ i j : {x // x = k}, A i j = 1 * K₀ i j := fun i j => by
    obtain rfl := Subsingleton.elim i j
    simp only [K₀, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, one_mul, i.2]
  have hKB : ∀ i j : {x // x = k}, B i j = 1 * K₀' i j := fun i j => by
    obtain rfl := Subsingleton.elim i j
    simp only [K₀', Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, one_mul, i.2]
  have hK₀s : K₀ᵀ = K₀ := by simp [K₀]
  have hK₀s' : K₀'ᵀ = K₀' := by simp [K₀']
  have hdK : IsUnit K₀.det := by simp only [K₀]; rw [det_smul_one_unique]; exact hk
  have hdK' : IsUnit K₀'.det := by
    simp only [K₀']; rw [det_smul_one_unique]
    exact isUnit_of_dvd_sub' hk hpba
  let e := Equiv.sumCompl (fun x : ι => x = k)
  have hCA : ∀ (i : {x // x = k}) (j : {x // ¬ x = k}), A i j = 1 * C₀ i j := fun i j =>
    (one_mul (A i.1 j.1)).symm
  have hCB : ∀ (i : {x // x = k}) (j : {x // ¬ x = k}), B i j = 1 * C₀' i j := fun i j =>
    (one_mul (B i.1 j.1)).symm
  have pA := pivot_split (fun x : ι => x = k) hA 1 hK₀s hdK C₀ hKA hCA
  have pB := pivot_split (fun x : ι => x = k) hB 1 hK₀s' hdK' C₀' hKB hCB
  simp only [one_smul] at pA pB
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix {x // ¬ x = k} {x // ¬ x = k} ℤ_[p],
      A' = A.submatrix (fun x : {x // ¬ x = k} => x.1) (fun x => x.1) - C₀ᵀ * K₀⁻¹ * C₀ := ⟨_, rfl⟩
  obtain ⟨B', hB'def⟩ : ∃ B' : Matrix {x // ¬ x = k} {x // ¬ x = k} ℤ_[p],
      B' = B.submatrix (fun x : {x // ¬ x = k} => x.1) (fun x => x.1) - C₀'ᵀ * K₀'⁻¹ * C₀' := ⟨_, rfl⟩
  rw [← hA'def] at pA
  rw [← hB'def] at pB
  have hA's : A'ᵀ = A' := by
    rw [hA'def]
    have := compl_symm (submatrix_symm hA (fun x : {x // ¬ x = k} => x.1)) hK₀s 1 C₀
    simpa only [one_smul] using this
  have hB's : B'ᵀ = B' := by
    rw [hB'def]
    have := compl_symm (submatrix_symm hB (fun x : {x // ¬ x = k} => x.1)) hK₀s' 1 C₀'
    simpa only [one_smul] using this
  have hd4 : MDvd 4 (B' - A') := by
    rw [hA'def, hB'def]
    have := mdvd_compl (m := 4) (t := 1) hdK hdK' (C₀ := C₀) (C₀' := C₀')
      (N := A.submatrix (fun x : {x // ¬ x = k} => x.1) (fun x => x.1))
      (N' := B.submatrix (fun x : {x // ¬ x = k} => x.1) (fun x => x.1))
      (fun i j => by
        obtain rfl := Subsingleton.elim i j
        simpa [K₀, K₀'] using hba0)
      (fun i j => by simpa [C₀, C₀'] using h4 i.1 j.1)
      (fun i j => by simpa using h4 i.1 j.1)
    simpa only [one_smul] using this
  have hDR : DetRel (Matrix.fromBlocks K₀ 0 0 A') (Matrix.fromBlocks K₀' 0 0 B') :=
    pA.detRel.symm.trans ((DetRel.submatrix ⟨s, hs, hsd⟩ e).trans pB.detRel)
  have hAu' : IsUnit A'.det := by
    obtain ⟨r, hr, er⟩ := pA.det
    rw [det_fromBlocks_zero₂₁, det_submatrix_equiv_self] at er
    exact isUnit_of_mul_isUnit_right (er ▸ (hr.pow 2).mul hAu)
  have hmain := core_two hp2 (IH _ (Fintype.card_subtype_lt (x := k) (by simp))) hk hab hA's hB's hAu' hd4
    hDR
  exact MEq.of_submatrix e (pA.trans (hmain.trans pB.symm))

end TwoUnit

/-! ### The induction step and the theorem -/

section Main

/-- A nonzero element of $\mathbb Z_p$ is not divisible by every power of $p$. -/
theorem exists_not_pow_dvd {x : ℤ_[p]} (hx : x ≠ 0) : ∃ n : ℕ, ¬ (p : ℤ_[p]) ^ n ∣ x :=
  ⟨x.valuation + 1, fun h => by
    have := (PadicInt.mem_span_pow_iff_le_valuation x hx (x.valuation + 1)).1 (Ideal.mem_span_singleton.2 h)
    omega⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Extracting the content:** a nonzero matrix is $p^\mu A_0$ with some entry of $A_0$ a unit. -/
theorem exists_scale {A : Matrix ι ι ℤ_[p]} (hA : A ≠ 0) :
    ∃ (μ : ℕ) (A₀ : Matrix ι ι ℤ_[p]), A = (p : ℤ_[p]) ^ μ • A₀ ∧ ∃ i j, IsUnit (A₀ i j) := by
  have hex : ∃ μ : ℕ, ∃ i j, ¬ (p : ℤ_[p]) ^ (μ + 1) ∣ A i j := by
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hA (Matrix.ext fun i j => h i j)
    obtain ⟨n, hn⟩ := exists_not_pow_dvd hij
    cases n with
    | zero => simp at hn
    | succ μ => exact ⟨μ, i, j, hn⟩
  classical
  have hall : ∀ i j, (p : ℤ_[p]) ^ (Nat.find hex) ∣ A i j := by
    intro i j
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push_neg at h1
      have e : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hpos
      have h2 := h1 i j
      rwa [e] at h2
  choose A₀ hA₀ using hall
  obtain ⟨i, j, hij⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Matrix.of A₀, Matrix.ext fun a b => by simp [hA₀ a b], i, j, ?_⟩
  rw [isUnit_iff_not_dvd]
  intro hd
  apply hij
  rw [hA₀ i j, pow_succ]
  exact mul_dvd_mul_left _ hd

/-- Cancelling a nonzero scalar from a symmetric matrix. -/
theorem symm_of_smul {t : ℤ_[p]} (ht : t ≠ 0) {M : Matrix ι ι ℤ_[p]} (h : (t • M)ᵀ = t • M) : Mᵀ = M := by
  rw [transpose_smul] at h
  exact smul_right_injective (Matrix ι ι ℤ_[p]) ht h

/-- **A unit entry:** the local statement for $A$ having a unit entry (given the claim in lower dimension). -/
theorem step_unit_entry (IH : ClaimBelow p (Fintype.card ι)) {A B : Matrix ι ι ℤ_[p]} {c : ℤ_[p]}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hA0 : A.det ≠ 0) (hc : A.det ∣ c) (hBA : MDvd (4 * c) (B - A))
    (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) {i j : ι} (hij : IsUnit (A i j)) : MEq A B := by
  by_cases hodd : p ≠ 2 ∧ IsUnit A.det
  · obtain ⟨hp2, hu⟩ := hodd
    obtain ⟨s, hs, hsd⟩ := hdet
    exact meq_unimod hp2 hA hB hu hs hsd
  by_cases hdiag : ∃ k, IsUnit (A k k)
  · obtain ⟨k, hk⟩ := hdiag
    by_cases hpc : (p : ℤ_[p]) ∣ c
    · exact step_pivot_dvd IH hA hB hA0 hc hBA hdet hpc k hk
    · have hcu : IsUnit c := (isUnit_iff_not_dvd c).2 hpc
      by_cases hp2 : p = 2
      · exact step_two_unit hp2 IH hA hB hA0 hc hBA hdet hcu k hk
      · exact absurd ⟨hp2, isUnit_of_dvd_unit hc hcu⟩ hodd
  · push_neg at hdiag
    by_cases hp2 : p = 2
    · have hne : i ≠ j := by
        rintro rfl; exact hdiag _ hij
      have hnd : ∀ k, (p : ℤ_[p]) ∣ A k k := fun k => by
        have := hdiag k; rwa [isUnit_iff_not_dvd, not_not] at this
      exact pivot2 hp2 IH hA hB hA0 hc hBA hdet hne one_ne_zero (fun _ _ => one_dvd _) (one_dvd _)
        (one_mul (A i j)).symm hij (by rw [one_mul]; exact hnd i) (by rw [one_mul]; exact hnd j)
    · have hnu : ¬ IsUnit A.det := fun h => hodd ⟨hp2, h⟩
      rw [isUnit_iff_not_dvd, not_not] at hnu
      exact step_pivot_odd hp2 IH hA hB hA0 hc hBA hdet (hnu.trans hc) hij hdiag

/-- **The induction step:** the claim for $\iota$ follows from the claim in lower dimensions. -/
theorem claim_step (IH : ClaimBelow p (Fintype.card ι)) : Claim p ι := by
  intro A B c hA hB hA0 hc hBA hdet
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, by simp, Matrix.ext fun i => isEmptyElim i⟩
  have hA0' : A ≠ 0 := by
    rintro rfl; exact hA0 det_zero
  obtain ⟨μ, A₀, hAeq, i₀, j₀, hij⟩ := exists_scale hA0'
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card ι = M + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_pos.ne'
  obtain ⟨t, ht⟩ : ∃ t : ℤ_[p], t = (p : ℤ_[p]) ^ μ := ⟨_, rfl⟩
  rw [← ht] at hAeq
  have ht0 : t ≠ 0 := by rw [ht]; exact pow_ne_zero _ PadicInt.prime_p.ne_zero
  have hdA : A.det = t ^ (M + 1) * A₀.det := by rw [hAeq, det_smul, hM]
  obtain ⟨e, he⟩ := hc
  obtain ⟨c', hct, hc'd⟩ : ∃ c', c = t * c' ∧ A₀.det ∣ c' :=
    ⟨t ^ M * A₀.det * e, by rw [he, hdA]; ring, ⟨t ^ M * e, by ring⟩⟩
  have hAab : ∀ a b, A a b = t * A₀ a b := fun a b => by rw [hAeq]; simp
  have htB : ∀ a b, t ∣ B a b := fun a b => by
    have h1 := hBA a b
    rw [Matrix.sub_apply] at h1
    have h3 : t ∣ B a b - A a b := (Dvd.intro (4 * c') (by rw [hct]; ring) : t ∣ 4 * c).trans h1
    have h2 : t ∣ A a b := ⟨_, hAab a b⟩
    have := dvd_add h3 h2
    rwa [sub_add_cancel] at this
  choose B₀ hB₀ using htB
  have hBeq : B = t • Matrix.of B₀ := Matrix.ext fun a b => by simp [hB₀ a b]
  have hA₀s : A₀ᵀ = A₀ := symm_of_smul ht0 (by rw [← hAeq]; exact hA)
  have hB₀s : (Matrix.of B₀)ᵀ = Matrix.of B₀ := symm_of_smul ht0 (by rw [← hBeq]; exact hB)
  have htN : t ^ (M + 1) ≠ 0 := pow_ne_zero _ ht0
  have hA₀0 : A₀.det ≠ 0 := fun h => hA0 (by rw [hdA, h, mul_zero])
  have hdB : B.det = t ^ (M + 1) * (Matrix.of B₀).det := by rw [hBeq, det_smul, hM]
  obtain ⟨s, hs, hsd⟩ := hdet
  have hdet' : ∃ s, IsUnit s ∧ (Matrix.of B₀).det = s ^ 2 * A₀.det :=
    ⟨s, hs, mul_left_cancel₀ htN (by rw [← hdB, hsd, hdA]; ring)⟩
  have hBA' : MDvd (4 * c') (Matrix.of B₀ - A₀) := by
    intro a b
    have h1 := hBA a b
    rw [Matrix.sub_apply, hB₀ a b, hAab a b, hct, ← mul_sub, show 4 * (t * c') = t * (4 * c') by ring] at h1
    simpa using (mul_dvd_mul_iff_left ht0).1 h1
  have key := step_unit_entry IH hA₀s hB₀s hA₀0 hc'd hBA' hdet' hij
  rw [hAeq, hBeq]
  exact key.smul t

end Main

/-- **The local statement** (local content of Cassels, Lemma 4.3, Ch. 9, p. 141): symmetric $A, B$ over
$\mathbb Z_p$ with $\det A \ne 0$, $\det A \mid c$, $B \equiv A \pmod{4c}$ and $\det B = s^2\det A$ ($s$ a unit)
are congruent. -/
theorem meq_of_congr (ι : Type) [Fintype ι] [DecidableEq ι] : Claim p ι := by
  have key : ∀ N, ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ = N → Claim p κ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro κ _ _ hκ
      exact claim_step (fun κ' _ _ hlt => ih _ (by omega) κ' rfl)
  exact key _ ι rfl

end QuadFormsKB.Siegel.CongrLocal
