/-
# Change of lattice for the self-density: the local Haar measure does not depend on the lattice

**Layer:** a complete discrete valuation ring $R$ with finite residue field (uniformizer $\pi$, $q = |R/\pi|$, any residue
characteristic, dyadic included), e.g. $\mathfrak o_\mathfrak p$.

The Tamagawa number computation normalizes the Haar measure on $O(V)(F_\mathfrak p)$
by$\mathrm{vol}(O(L_\mathfrak p)) = \beta_\mathfrak p(L, L)$ for the standard
lattice. That this is the gauge-form measure, i.e. does not depend on the lattice used, is the content of this file: for
$Q_1 = c\,(Q\circ D)$ with $D = \mathrm{diag}(c_0, \dots, c_{n-1})$ (the form of the lattice $DL$, rescaled by $c$),
$$\beta(Q_1)\;q^{\,j\,n(n-1)/2} = [A_1 : A_1(j)]\cdot[\mathrm{Sym} : \Phi\,\mathrm{Sym}]\cdot[\mathrm{Sym} : L_Q(M_n(R))]\qquad(j \gg 0),$$
where $A_1$ is the group of integral isometries of $Q_1$, $A_1(j)$ its "box" subgroup $\{Y : DY \equiv D \bmod \pi^jM_n(R)D\}$
(the conjugate of the principal congruence subgroup of level $j$), $\Phi(s)_{ab} = c\,c_ac_b\,s_{ab}$ the effect of
$S \mapsto c\,(S\circ D)$ on coefficients, and $L_Q$ the differential of $X \mapsto Q\circ X$ at $X = 1$ (`formD`).

*Proof.* (1) Hensel (`exists_compMat_eq_of_dvd`): every solution of $Q_1\circ X \equiv Q_1 \bmod \pi^k$ is an exact isometry
times an element of the box, so the solutions mod $\pi^k$ fibre over $A_1/A_1(j)$ with fibres the solutions in the box
(`card_sol_eq`). (2) In the box, $Y = D^{-1}(1 + \pi^jZ)D$ and $Q_1\circ Y = Q_1 + \pi^j\Phi(L_Q Z) + \pi^{2j}(\dots)$, so for
$2j \ge k$ the condition is linear in $Z$ and the count is a lattice index (`card_boxSol`). (3) Index arithmetic
(`index_comap`, `index_map_of_injective`, diagonal lattices).

Indices are 0-based. Sources: Weil 1982, §2.2.1, p. 14 (the local measure of a gauge form is independent of the
coordinates; checked against the printed book); Kitaoka 1993, §5.6 [unverified].
-/
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.Hensel

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open QuadFormsKB.LocalDensity.DVR QuadFormsKB.QuadForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ### Divisibility subgroups and their indices -/

section Index

variable (π : R)

/-- $\{z \in R : \pi^k \mid tz\}$ as an additive subgroup. -/
def dvdSub (k : ℕ) (t : R) : AddSubgroup R where
  carrier := {z | π ^ k ∣ t * z}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, mul_add] at *; exact dvd_add ha hb
  zero_mem' := by simp
  neg_mem' {a} ha := by simp only [Set.mem_ofPred_eq, mul_neg, dvd_neg] at *; exact ha

theorem mem_dvdSub {k : ℕ} {t z : R} : z ∈ dvdSub π k t ↔ π ^ k ∣ t * z := Iff.rfl

variable {π}

theorem index_span_pow [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) (k : ℕ) :
    (Ideal.span {π ^ k} : Ideal R).toAddSubgroup.index = q R ^ k :=
  card_quot_pow π hπ k

/-- In a DVR, $\pi^k \mid \pi^e u z$ ($u$ a unit, $e \le k$) iff $\pi^{k-e} \mid z$. -/
theorem dvdSub_eq (hπ : Irreducible π) {k e : ℕ} {t u : R} (ht : t = π ^ e * u) (hu : IsUnit u) (hek : e ≤ k) :
    dvdSub π k t = (Ideal.span {π ^ (k - e)} : Ideal R).toAddSubgroup := by
  ext z
  rw [mem_dvdSub, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, ht]
  have hk : π ^ k = π ^ e * π ^ (k - e) := by rw [← pow_add]; congr 1; omega
  rw [hk, mul_assoc]
  constructor
  · intro h
    have h1 := (mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)).mp h
    obtain ⟨w, hw⟩ := h1
    refine ⟨↑hu.unit⁻¹ * w, ?_⟩
    calc z = ↑hu.unit⁻¹ * (u * z) := by rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [hw]; ring
  · rintro ⟨w, rfl⟩
    exact ⟨u * w, by ring⟩

theorem index_dvdSub [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) {k e : ℕ} {t u : R}
    (ht : t = π ^ e * u) (hu : IsUnit u) (hek : e ≤ k) : (dvdSub π k t).index = q R ^ (k - e) := by
  rw [dvdSub_eq hπ ht hu hek, index_span_pow hπ]

/-- **Uniqueness of the order:** $\pi^au = \pi^bw$ with units $u, w$ forces $a = b$. -/
theorem eq_of_pow_mul_unit (hπ : Irreducible π) {a b : ℕ} {u w : R} (hu : IsUnit u) (hw : IsUnit w)
    (h : π ^ a * u = π ^ b * w) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · apply dvr_not_pow_succ_dvd hπ hu a
    rw [h]; exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _
  · apply dvr_not_pow_succ_dvd hπ hw b
    rw [← h]; exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _

open Classical in
/-- **The order of a nonzero element**: $t$ is associated to $\pi^{\mathrm{ord}\,t}$ ($0$ for $t = 0$). -/
def ord (hπ : Irreducible π) (t : R) : ℕ :=
  if h : t = 0 then 0 else (IsDiscreteValuationRing.associated_pow_irreducible h hπ).choose

theorem exists_eq_ord (hπ : Irreducible π) {t : R} (ht : t ≠ 0) :
    ∃ u, IsUnit u ∧ t = π ^ ord hπ t * u := by
  classical
  have h := (IsDiscreteValuationRing.associated_pow_irreducible ht hπ).choose_spec
  rw [ord, dif_neg ht]
  obtain ⟨w, hw⟩ := h.symm
  exact ⟨↑w, w.isUnit, hw.symm⟩

theorem ord_pow_mul (hπ : Irreducible π) {u : R} (hu : IsUnit u) (e : ℕ) : ord hπ (π ^ e * u) = e := by
  obtain ⟨w, hw, hew⟩ := exists_eq_ord hπ (mul_ne_zero (pow_ne_zero e hπ.ne_zero) hu.ne_zero)
  exact (eq_of_pow_mul_unit hπ hu hw hew).symm

theorem ord_mul (hπ : Irreducible π) {s t : R} (hs : s ≠ 0) (ht : t ≠ 0) :
    ord hπ (s * t) = ord hπ s + ord hπ t := by
  obtain ⟨u, hu, hsu⟩ := exists_eq_ord hπ hs
  obtain ⟨w, hw, htw⟩ := exists_eq_ord hπ ht
  have : s * t = π ^ (ord hπ s + ord hπ t) * (u * w) := by
    conv_lhs => rw [hsu, htw]
    rw [pow_add]; ring
  rw [this, ord_pow_mul hπ (hu.mul hw)]

theorem ord_unit (hπ : Irreducible π) {u : R} (hu : IsUnit u) : ord hπ u = 0 := by
  simpa using ord_pow_mul hπ hu 0

theorem ord_pow (hπ : Irreducible π) (e : ℕ) : ord hπ (π ^ e) = e := by
  simpa using ord_pow_mul hπ isUnit_one e

theorem pow_ord_dvd (hπ : Irreducible π) (t : R) : π ^ ord hπ t ∣ t := by
  by_cases ht : t = 0
  · rw [ht]; exact dvd_zero _
  · obtain ⟨u, -, hu⟩ := exists_eq_ord hπ ht
    exact ⟨u, hu⟩

/-- $\pi^{\mathrm{ord}\,t} \mid t$ exactly: $\pi^{\mathrm{ord}\,t+1} \nmid t$. -/
theorem not_pow_ord_succ_dvd (hπ : Irreducible π) {t : R} (ht : t ≠ 0) : ¬ π ^ (ord hπ t + 1) ∣ t := by
  obtain ⟨u, hu, htu⟩ := exists_eq_ord hπ ht
  rw [htu, ord_pow_mul hπ hu]; exact dvr_not_pow_succ_dvd hπ hu _

theorem index_dvdSub' [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) {k : ℕ} {t : R} (ht : t ≠ 0)
    (hk : ord hπ t ≤ k) : (dvdSub π k t).index = q R ^ (k - ord hπ t) := by
  obtain ⟨u, hu, htu⟩ := exists_eq_ord hπ ht
  exact index_dvdSub hπ htu hu hk

/-- $\{z : \pi^k \mid z\}$ has index $q^k$. -/
theorem dvdSub_one (k : ℕ) : dvdSub π k 1 = (Ideal.span {π ^ k} : Ideal R).toAddSubgroup := by
  ext z; rw [mem_dvdSub, one_mul, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]

variable (π) in
/-- **A pi of divisibility subgroups** of $R^\iota$: $\{z : \pi^k \mid t_i z_i\ \forall i\}$. -/
def piDvd {ι : Type*} (k : ℕ) (t : ι → R) : AddSubgroup (ι → R) := AddSubgroup.pi Set.univ fun i => dvdSub π k (t i)

theorem mem_piDvd {ι : Type*} {k : ℕ} {t z : ι → R} : z ∈ piDvd π k t ↔ ∀ i, π ^ k ∣ t i * z i := by
  simp [piDvd, AddSubgroup.mem_pi, mem_dvdSub]

theorem index_piDvd [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) {ι : Type*} [Fintype ι] {k : ℕ}
    {t : ι → R} (ht : ∀ i, t i ≠ 0) (hk : ∀ i, ord hπ (t i) ≤ k) :
    (piDvd π k t).index = ∏ i, q R ^ (k - ord hπ (t i)) := by
  rw [piDvd, AddSubgroup.index_pi]
  exact Finset.prod_congr rfl fun i _ => index_dvdSub' hπ (ht i) (hk i)

end Index

/-! ### The form $c\,(Q \circ D)$ for diagonal $D$ -/

section Diag

variable {n : ℕ}

/-- **The weights** $w_{ab} = c\,c_ac_b$ ($a \le b$): $c\,(S\circ D)$ has coefficients $w_{ab}S_{ab}$ for $D = \mathrm{diag}(c_a)$. -/
def wts (c : R) (cv : Fin n → R) : UpperIdx n → R := fun p => c * cv p.1.1 * cv p.1.2

theorem col_diagonal {A : Type*} [CommRing A] (cv : Fin n → A) (i : Fin n) : (fun l => diagonal cv l i) = Pi.single i (cv i) := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [h]

theorem eval_single' {A : Type*} [CommRing A] (S : QuadForm A n) (i : Fin n) (a : A) : S.eval (Pi.single i a) = a ^ 2 * S.coeff i i := by
  simp only [QuadForm.eval, evalIn, Algebra.algebraMap_self, RingHom.id_apply, Pi.single_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => by simp [hb])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ i) h)]
  simp; ring

/-- $(S \circ D)_{ab} = c_ac_bS_{ab}$ for $D = \mathrm{diag}(c_a)$ (all $a, b$; both sides vanish below the diagonal). -/
theorem compMat_diagonal_coeff {A : Type*} [CommRing A] (S : QuadForm A n) (cv : Fin n → A) (a b : Fin n) :
    (S.compMat (diagonal cv)).coeff a b = cv a * cv b * S.coeff a b := by
  rw [compMat_coeff, col_diagonal, col_diagonal]
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    by_cases he : a = b
    · subst he; rw [if_pos rfl, eval_single']; ring
    · rw [if_neg he]
      have hlt : a < b := lt_of_le_of_ne hab he
      rw [single_dotProduct]
      have h0 : S.coeff b a = 0 := S.upper (show id a < id b from hlt)
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hessian, h0]
      ring
  · rw [if_neg hab, S.upper (show id b < id a from not_le.mp hab), mul_zero]

theorem smul_compMat_diagonal_coeff {A : Type*} [CommRing A] (c : A) (S : QuadForm A n) (cv : Fin n → A) (a b : Fin n) :
    (c • S.compMat (diagonal cv)).coeff a b = c * cv a * cv b * S.coeff a b := by
  rw [smul_coeff, Matrix.smul_apply, compMat_diagonal_coeff, smul_eq_mul]; ring

theorem hessian_smul_compMat {A : Type*} [CommRing A] (c : A) (Qo : QuadForm A n) (cv : Fin n → A) :
    (c • Qo.compMat (diagonal cv)).hessian = c • ((diagonal cv)ᵀ * Qo.hessian * diagonal cv) := by
  rw [← hessian_compMat]
  ext a b
  simp [hessian, Matrix.add_apply, Matrix.smul_apply, mul_add]

theorem det_hessian_Q₁ {A : Type*} [CommRing A] (c : A) (Qo : QuadForm A n) (cv : Fin n → A) :
    (c • Qo.compMat (diagonal cv)).hessian.det = c ^ n * (∏ a, cv a) ^ 2 * Qo.hessian.det := by
  rw [hessian_smul_compMat, det_smul, det_mul, det_mul, det_transpose, det_diagonal, Fintype.card_fin]; ring

theorem nondegenerate_Q₁ {A : Type*} [CommRing A] [IsDomain A] {c : A} (hc : c ≠ 0) {Qo : QuadForm A n}
    (hQo : Qo.Nondegenerate) {cv : Fin n → A} (hcv : ∀ a, cv a ≠ 0) : (c • Qo.compMat (diagonal cv)).Nondegenerate := by
  rw [QuadForm.Nondegenerate, det_hessian_Q₁]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun a _ => hcv a))) hQo

end Diag

/-! ### The box $\{P : DP \in \pi^jM_n(R)D\}$ -/

section Box

variable {n : ℕ} (π : R) (cv : Fin n → R) (j : ℕ)

/-- **The box** $V_j = \{P \in M_n(R) : DP = \pi^jZD \text{ for some } Z \in M_n(R)\}$, $D = \mathrm{diag}(c_a)$: the matrices
$P$ with $D(1 + P)D^{-1} \equiv 1 \bmod \pi^j$ (the conjugate of the level-$j$ congruence neighbourhood). -/
def boxV : AddSubgroup (Matrix (Fin n) (Fin n) R) where
  carrier := {P | ∃ Z : Matrix (Fin n) (Fin n) R, diagonal cv * P = π ^ j • Z * diagonal cv}
  add_mem' := by
    rintro P P' ⟨Z, hZ⟩ ⟨Z', hZ'⟩
    exact ⟨Z + Z', by rw [Matrix.mul_add, hZ, hZ', smul_add, Matrix.add_mul]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro P ⟨Z, hZ⟩
    exact ⟨-Z, by rw [Matrix.mul_neg, hZ, smul_neg, Matrix.neg_mul]⟩

variable {π cv j}

theorem mem_boxV {P : Matrix (Fin n) (Fin n) R} :
    P ∈ boxV π cv j ↔ ∃ Z : Matrix (Fin n) (Fin n) R, diagonal cv * P = π ^ j • Z * diagonal cv := Iff.rfl

theorem boxV_mul {P P' : Matrix (Fin n) (Fin n) R} (hP : P ∈ boxV π cv j) (hP' : P' ∈ boxV π cv j) :
    P * P' ∈ boxV π cv j := by
  obtain ⟨Z, hZ⟩ := hP
  obtain ⟨Z', hZ'⟩ := hP'
  refine ⟨π ^ j • (Z * Z'), ?_⟩
  calc diagonal cv * (P * P') = (diagonal cv * P) * P' := (Matrix.mul_assoc _ _ _).symm
    _ = π ^ j • (Z * (diagonal cv * P')) := by rw [hZ]; simp only [Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by rw [hZ']; simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- **Deep matrices lie in the box:** if $c_b \mid \pi^m$ for all $b$, then $\pi^{j+m}M_n(R) \subseteq V_j$. -/
theorem pow_smul_mem_boxV {m : ℕ} (hm : ∀ b, cv b ∣ π ^ m) (E : Matrix (Fin n) (Fin n) R) :
    π ^ (j + m) • E ∈ boxV π cv j := by
  choose f hf using hm
  refine ⟨diagonal cv * E * diagonal f, ?_⟩
  rw [Matrix.smul_mul, Matrix.mul_assoc (diagonal cv * E), diagonal_mul_diagonal]
  have : (fun i => f i * cv i) = fun _ => π ^ m := funext fun i => by rw [mul_comm, ← hf i]
  rw [this, show (diagonal fun _ => π ^ m : Matrix (Fin n) (Fin n) R) = π ^ m • (1 : Matrix (Fin n) (Fin n) R) by
    ext a b; simp [diagonal_apply, Matrix.one_apply]]
  simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul, ← pow_add]

theorem isUnit_det_one_add (hπ : Irreducible π) (hj : 1 ≤ j) (Z : Matrix (Fin n) (Fin n) R) :
    IsUnit (1 + π ^ j • Z).det := by
  apply dvr_isUnit_of_not_dvd hπ
  intro h
  have hmap : (Ideal.Quotient.mk (Ideal.span {π})).mapMatrix (1 + π ^ j • Z) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, map_pow]
    rw [show Ideal.Quotient.mk (Ideal.span {π}) π = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self π), zero_pow (by omega), zero_mul, add_zero]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  have h1 : Ideal.Quotient.mk (Ideal.span {π}) (1 + π ^ j • Z).det = 1 := by
    rw [RingHom.map_det, hmap, det_one]
  have h2 : Ideal.Quotient.mk (Ideal.span {π}) (1 + π ^ j • Z).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  rw [h1] at h2
  have htop := Ideal.Quotient.zero_eq_one_iff.mp h2.symm
  rw [Ideal.span_singleton_eq_top] at htop
  exact hπ.not_isUnit htop

/-- **Inverses stay in the box** (all $c_a \ne 0$). -/
theorem inv_sub_one_mem_boxV (hcv : ∀ a, cv a ≠ 0) {P Y : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ boxV π cv j) (hY : (1 + P) * Y = 1) : Y - 1 ∈ boxV π cv j := by
  obtain ⟨Z, hZ⟩ := hP
  set W : Matrix (Fin n) (Fin n) R := 1 + π ^ j • Z
  have hDW : diagonal cv * (1 + P) = W * diagonal cv := by
    rw [Matrix.mul_add, Matrix.mul_one, hZ, Matrix.add_mul, Matrix.one_mul]
  have hD0 : (diagonal cv).det ≠ 0 := by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hcv a
  have hP1 : IsUnit (1 + P).det := by
    have := congrArg Matrix.det hY
    rw [det_mul, det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hW : IsUnit W.det := by
    have := congrArg Matrix.det hDW
    rw [det_mul, det_mul, mul_comm W.det] at this
    rw [← mul_left_cancel₀ hD0 this]; exact hP1
  have hDY : diagonal cv * Y = W⁻¹ * diagonal cv := by
    have : W * (diagonal cv * Y) = W * (W⁻¹ * diagonal cv) := by
      rw [← Matrix.mul_assoc, ← hDW, Matrix.mul_assoc, hY, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hW, Matrix.one_mul]
    have hl : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul _ hW
    calc diagonal cv * Y = W⁻¹ * (W * (diagonal cv * Y)) := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
      _ = _ := by rw [this, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  refine ⟨-(W⁻¹ * Z), ?_⟩
  have hWi : W⁻¹ - 1 = -(π ^ j • (W⁻¹ * Z)) := by
    have : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul _ hW
    have e : W⁻¹ * W = W⁻¹ + π ^ j • (W⁻¹ * Z) := by
      simp only [W, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [e] at this
    rw [← this]; abel
  calc diagonal cv * (Y - 1) = (W⁻¹ - 1) * diagonal cv := by
        rw [Matrix.mul_sub, Matrix.mul_one, hDY, Matrix.sub_mul, Matrix.one_mul]
    _ = _ := by rw [hWi, smul_neg, Matrix.neg_mul]

variable (cv) in
/-- **The box parametrization** $\psi(Z)_{ab} = e_ac_bZ_{ab}$ ($c_ae_a = \pi^j$): $D\,\psi(Z) = \pi^jZD$. -/
def psi (ev : Fin n → R) (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => ev a * cv b * Z a b

theorem diagonal_mul_psi {ev : Fin n → R} (hev : ∀ a, cv a * ev a = π ^ j) (Z : Matrix (Fin n) (Fin n) R) :
    diagonal cv * psi cv ev Z = π ^ j • Z * diagonal cv := by
  ext a b
  simp only [diagonal_mul, psi, Matrix.of_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  rw [← hev a]; ring

theorem psi_mem_boxV {ev : Fin n → R} (hev : ∀ a, cv a * ev a = π ^ j) (Z : Matrix (Fin n) (Fin n) R) :
    psi cv ev Z ∈ boxV π cv j := ⟨Z, diagonal_mul_psi hev Z⟩

theorem exists_psi_eq (hcv : ∀ a, cv a ≠ 0) {ev : Fin n → R} (hev : ∀ a, cv a * ev a = π ^ j)
    {P : Matrix (Fin n) (Fin n) R} (hP : P ∈ boxV π cv j) : ∃ Z, psi cv ev Z = P := by
  obtain ⟨Z, hZ⟩ := hP
  refine ⟨Z, ?_⟩
  ext a b
  have h := congrFun (congrFun (hZ.trans (diagonal_mul_psi hev Z).symm) a) b
  simp only [diagonal_mul] at h
  exact (mul_left_cancel₀ (hcv a) h).symm

end Box

/-! ### Taylor expansion of $Q_1 \circ (1 + \psi(Z))$ -/

section Taylor

variable {n : ℕ}

theorem eval_smul_form {A : Type*} [CommRing A] (c : A) (S : QuadForm A n) (x : Fin n → A) :
    (c • S).eval x = c * S.eval x := by
  simp only [QuadForm.eval, evalIn, Algebra.algebraMap_self, RingHom.id_apply, smul_coeff, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

theorem smul_compMat {A : Type*} [CommRing A] (c : A) (S : QuadForm A n) (X : Matrix (Fin n) (Fin n) A) :
    (c • S).compMat X = c • S.compMat X :=
  eq_of_eval_eq fun y => by rw [eval_compMat, eval_smul_form, eval_smul_form, eval_compMat]

/-- The identity matrix as a vector indexed by `Fin n × Fin n`. -/
def idv : Fin n × Fin n → R := fun q => (1 : Matrix (Fin n) (Fin n) R) q.1 q.2

/-- A matrix as a vector indexed by `Fin n × Fin n`. -/
def vec (Z : Matrix (Fin n) (Fin n) R) : Fin n × Fin n → R := fun q => Z q.1 q.2

theorem toMat_idv_add (j : ℕ) (π : R) (Z : Matrix (Fin n) (Fin n) R) :
    toMat (idv + π ^ j • vec Z) = 1 + π ^ j • Z := by
  ext a b; rfl

theorem toMat_vec (Z : Matrix (Fin n) (Fin n) R) : toMat (vec Z) = Z := by ext a b; rfl

theorem vec_toMat (z : Fin n × Fin n → R) : vec (toMat z) = z := by funext q; rfl

/-- **The coefficients of $Q_1 = c\,(Q\circ D)$:** $w_pQ_p$. -/
theorem coeff_Q₁ (c : R) (Qo : QuadForm R n) (cv : Fin n → R) (p : UpperIdx n) :
    (c • Qo.compMat (diagonal cv)).coeff p.1.1 p.1.2 = wts c cv p * Qo.coeff p.1.1 p.1.2 := by
  rw [smul_compMat_diagonal_coeff]; rfl

/-- **Taylor expansion in the box:** for $D\psi(Z) = \pi^jZD$,
$Q_1\circ(1 + \psi(Z)) = w\cdot\big(Q + \pi^jL_Q(Z) + \pi^{2j}(Q\circ Z)\big)$ coefficientwise ($L_Q$ = `formD Qo idv`). -/
theorem coeff_compMat_one_add_psi (c : R) (Qo : QuadForm R n) {π : R} {cv ev : Fin n → R} {j : ℕ}
    (hev : ∀ a, cv a * ev a = π ^ j) (Z : Matrix (Fin n) (Fin n) R) (p : UpperIdx n) :
    ((c • Qo.compMat (diagonal cv)).compMat (1 + psi cv ev Z)).coeff p.1.1 p.1.2 =
      wts c cv p * (Qo.coeff p.1.1 p.1.2 + π ^ j * formD Qo idv (vec Z) p + π ^ (2 * j) * formF Qo (vec Z) p) := by
  have hD : diagonal cv * (1 + psi cv ev Z) = (1 + π ^ j • Z) * diagonal cv := by
    rw [Matrix.mul_add, Matrix.mul_one, diagonal_mul_psi hev, Matrix.add_mul, Matrix.one_mul]
  rw [smul_compMat, compMat_mul, hD, ← compMat_mul, smul_compMat_diagonal_coeff]
  have hF := congrFun (formF_add_smul Qo idv (vec Z) (π ^ j)) p
  rw [formF, toMat_idv_add] at hF
  rw [hF]
  have h1 : formF Qo idv p = Qo.coeff p.1.1 p.1.2 := by
    rw [formF, show toMat (idv : Fin n × Fin n → R) = 1 by ext a b; rfl, compMat_one]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, wts]
  ring

end Taylor

/-! ### Counting the solutions in the box -/

section BoxCount

variable {n : ℕ} {π : R}

/-- Reduction mod $\pi^k$. -/
abbrev mk (π : R) (k : ℕ) : R →+* R ⧸ Ideal.span {π ^ k} := Ideal.Quotient.mk _

/-- **Solutions mod $\pi^k$, coefficientwise.** -/
theorem solMod_iff {k : ℕ} (Q : QuadForm R n) (X : Matrix (Fin n) (Fin n) R) :
    (Q.map (mk π k)).compMat (X.map (mk π k)) = Q.map (mk π k) ↔
      ∀ p : UpperIdx n, π ^ k ∣ (Q.compMat X).coeff p.1.1 p.1.2 - Q.coeff p.1.1 p.1.2 := by
  rw [map_compMat]
  constructor
  · intro h p
    have := congrArg (fun S : QuadForm _ n => S.coeff p.1.1 p.1.2) h
    simp only [QuadForm.map] at this
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq.mp this
  · intro h
    apply ext_upper
    intro a b hab
    simp only [QuadForm.map]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h ⟨(a, b), hab⟩))

variable (π) in
/-- **The linear condition** $z \mapsto (w_p\,\pi^j\,L_Q(z)_p)_p$. -/
def fL (c : R) (Qo : QuadForm R n) (cv : Fin n → R) (j : ℕ) : (Fin n × Fin n → R) →+ (UpperIdx n → R) where
  toFun z := fun p => wts c cv p * π ^ j * formD Qo idv z p
  map_zero' := by funext p; simp
  map_add' z z' := by funext p; simp only [map_add, Pi.add_apply]; ring

variable (π) in
/-- $P = \{z : \pi^k \mid w_p\pi^jL_Q(z)_p\ \forall p\}$. -/
def Pset (c : R) (Qo : QuadForm R n) (cv : Fin n → R) (j k : ℕ) : AddSubgroup (Fin n × Fin n → R) :=
  (piDvd π k fun _ : UpperIdx n => (1 : R)).comap (fL π c Qo cv j)

theorem mem_Pset {c : R} {Qo : QuadForm R n} {cv : Fin n → R} {j k : ℕ} {z : Fin n × Fin n → R} :
    z ∈ Pset π c Qo cv j k ↔ ∀ p, π ^ k ∣ wts c cv p * π ^ j * formD Qo idv z p := by
  simp [Pset, AddSubgroup.mem_comap, mem_piDvd, fL]

variable (π) in
/-- $\Lambda = \{z : \pi^k \mid e_ac_bz_{ab}\}$, the $z$ with $\psi(z) \equiv 0 \bmod \pi^k$. -/
def Lam (cv ev : Fin n → R) (k : ℕ) : AddSubgroup (Fin n × Fin n → R) := piDvd π k fun q => ev q.1 * cv q.2

theorem sol_psi_iff {c : R} {Qo : QuadForm R n} {cv ev : Fin n → R} {j k : ℕ} (hev : ∀ a, cv a * ev a = π ^ j)
    (h2j : k ≤ 2 * j) (Z : Matrix (Fin n) (Fin n) R) :
    (∀ p : UpperIdx n, π ^ k ∣ ((c • Qo.compMat (diagonal cv)).compMat (1 + psi cv ev Z)).coeff p.1.1 p.1.2 -
      (c • Qo.compMat (diagonal cv)).coeff p.1.1 p.1.2) ↔ vec Z ∈ Pset π c Qo cv j k := by
  rw [mem_Pset]
  refine forall_congr' fun p => ?_
  rw [coeff_compMat_one_add_psi c Qo hev, coeff_Q₁]
  have hsq : π ^ k ∣ wts c cv p * (π ^ (2 * j) * formF Qo (vec Z) p) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow π h2j) _) _
  rw [show ∀ w a b f : R, w * (a + b + f) - w * a = w * b + w * f from fun _ _ _ _ => by ring,
    dvd_add_left hsq, mul_assoc]

theorem map_one_add_psi_eq_iff {cv ev : Fin n → R} {k : ℕ} (Z Z' : Matrix (Fin n) (Fin n) R) :
    (1 + psi cv ev Z).map (mk π k) = (1 + psi cv ev Z').map (mk π k) ↔ -vec Z + vec Z' ∈ Lam π cv ev k := by
  rw [Lam, mem_piDvd]
  constructor
  · intro h q
    have := congrFun (congrFun h q.1) q.2
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, add_right_inj, psi, Matrix.of_apply] at this
    have h' := Ideal.Quotient.eq.mp this
    rw [Ideal.mem_span_singleton] at h'
    have : ev q.1 * cv q.2 * (-vec Z + vec Z') q = -(ev q.1 * cv q.2 * Z q.1 q.2 - ev q.1 * cv q.2 * Z' q.1 q.2) := by
      simp only [vec, Pi.add_apply, Pi.neg_apply]; ring
    rw [this, dvd_neg]; exact h'
  · intro h
    ext a b
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, add_right_inj, psi, Matrix.of_apply]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.mem_span_singleton]
    have := h (a, b)
    have e : ev a * cv b * Z a b - ev a * cv b * Z' a b = -(ev (a, b).1 * cv (a, b).2 * (-vec Z + vec Z') (a, b)) := by
      simp only [vec, Pi.add_apply, Pi.neg_apply]; ring
    rw [e, dvd_neg]; exact this

variable (π) in
/-- **The solutions mod $\pi^k$ in the box:** $\bar X$ with $\bar Q_1\circ\bar X = \bar Q_1$ and $\bar X = \overline{1 + P}$, $P \in V_j$. -/
def boxSol (c : R) (Qo : QuadForm R n) (cv : Fin n → R) (j k : ℕ) : Type _ :=
  {X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}) //
    ((c • Qo.compMat (diagonal cv)).map (mk π k)).compMat X = (c • Qo.compMat (diagonal cv)).map (mk π k) ∧
      ∃ P ∈ boxV π cv j, (1 + P).map (mk π k) = X}

/-- **The box solutions are $P/\Lambda$** ($2j \ge k$): $|\mathrm{boxSol}| = [P : \Lambda]$. -/
theorem card_boxSol (c : R) (Qo : QuadForm R n) {cv ev : Fin n → R} (hcv : ∀ a, cv a ≠ 0)
    {j k : ℕ} (hev : ∀ a, cv a * ev a = π ^ j) (h2j : k ≤ 2 * j) :
    Nat.card (boxSol π c Qo cv j k) = (Lam π cv ev k).relIndex (Pset π c Qo cv j k) := by
  set P := Pset π c Qo cv j k
  set Λ := Lam π cv ev k
  have hsol : ∀ z : P, ((c • Qo.compMat (diagonal cv)).map (mk π k)).compMat ((1 + psi cv ev (toMat (z : Fin n × Fin n → R))).map (mk π k)) =
      (c • Qo.compMat (diagonal cv)).map (mk π k) := by
    intro z
    rw [solMod_iff, sol_psi_iff hev h2j, vec_toMat]; exact z.2
  let f : P ⧸ Λ.addSubgroupOf P → boxSol π c Qo cv j k :=
    Quotient.lift (fun z : P => ⟨(1 + psi cv ev (toMat (z : Fin n × Fin n → R))).map (mk π k), hsol z,
      ⟨_, psi_mem_boxV hev _, rfl⟩⟩) (fun a b hab => by
        apply Subtype.ext
        simp only
        rw [map_one_add_psi_eq_iff, vec_toMat, vec_toMat]
        have := (QuotientAddGroup.leftRel_apply.mp hab)
        rw [AddSubgroup.mem_addSubgroupOf] at this
        simpa using this)
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn' with | h a => ?_
    induction y using Quotient.inductionOn' with | h b => ?_
    apply Quotient.sound'
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
    have := congrArg Subtype.val hxy
    simp only [f, Quotient.lift_mk] at this
    erw [Quotient.lift_mk, Quotient.lift_mk] at this
    rw [map_one_add_psi_eq_iff, vec_toMat, vec_toMat] at this
    simpa using this
  have hsurj : Function.Surjective f := by
    rintro ⟨X, hX, P₀, hP₀, rfl⟩
    obtain ⟨Z, rfl⟩ := exists_psi_eq hcv hev hP₀
    have hz : vec Z ∈ P := by
      rw [← sol_psi_iff hev h2j, ← solMod_iff]; exact hX
    refine ⟨Quotient.mk'' ⟨vec Z, hz⟩, ?_⟩
    apply Subtype.ext
    show (1 + psi cv ev (toMat (vec Z))).map (mk π k) = _
    rw [toMat_vec]
  rw [AddSubgroup.relIndex, AddSubgroup.index]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

end BoxCount

/-! ### Hensel: the solutions mod $\pi^k$ fibre over $A/A_W$ -/

section Decomp

variable {n : ℕ} {π : R}

theorem dvd_mul_entries {m : ℕ} {M : Matrix (Fin n) (Fin n) R} (hM : ∀ a b, π ^ m ∣ M a b)
    (N : Matrix (Fin n) (Fin n) R) (a b : Fin n) : π ^ m ∣ (N * M) a b := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (hM l b) _

theorem mem_boxV_of_dvd {cv : Fin n → R} {j m t : ℕ} (hm : ∀ b, cv b ∣ π ^ m) (ht : j + m ≤ t)
    {M : Matrix (Fin n) (Fin n) R} (hM : ∀ a b, π ^ t ∣ M a b) : M ∈ boxV π cv j := by
  choose E hE using hM
  have : M = π ^ (j + m) • (π ^ (t - (j + m)) • Matrix.of E) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← mul_assoc, ← pow_add]
    rw [hE a b]; congr 2; omega
  rw [this]; exact pow_smul_mem_boxV hm _

variable (π) in
/-- **The box subgroup** $A_W = \{a \in A : \rho(a) - 1 \in V_j\}$ of a group $A$ acting by integral matrices. -/
def boxSub {A : Type*} [Group A] (ρ : A →* Matrix (Fin n) (Fin n) R) {cv : Fin n → R} (hcv : ∀ a, cv a ≠ 0)
    (j : ℕ) : Subgroup A where
  carrier := {a | ρ a - 1 ∈ boxV π cv j}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at *
    have : ρ a * ρ b - 1 = (ρ a - 1) * (ρ b - 1) + (ρ a - 1) + (ρ b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (boxV_mul ha hb) ha) hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    apply inv_sub_one_mem_boxV hcv ha
    rw [add_sub_cancel, ← map_mul, mul_inv_cancel, map_one]

theorem mem_boxSub {A : Type*} [Group A] {ρ : A →* Matrix (Fin n) (Fin n) R} {cv : Fin n → R}
    {hcv : ∀ a, cv a ≠ 0} {j : ℕ} {a : A} : a ∈ boxSub π ρ hcv j ↔ ρ a - 1 ∈ boxV π cv j := Iff.rfl

variable [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **The decomposition** (Hensel): for a group $A$ acting through $\rho$ exactly by the integral isometries of $Q_1$,
$\pi^d \,\|\, \det H_{Q_1}$, $k \ge 2d + 1$ and the box $V_j$ containing $\pi^{k-d}M_n(R)$,
$$\#\{\bar X \in M_n(R/\pi^k) : \bar Q_1\circ\bar X = \bar Q_1\} = [A : A_W]\cdot\#\mathrm{boxSol}.$$ -/
theorem card_sol_eq (hπ : Irreducible π) (c : R) (Qo : QuadForm R n) {cv : Fin n → R} (hcv : ∀ a, cv a ≠ 0)
    {j k d m : ℕ}
    {A : Type*} [Group A] (ρ : A →* Matrix (Fin n) (Fin n) R)
    (hρ : ∀ a, (c • Qo.compMat (diagonal cv)).compMat (ρ a) = c • Qo.compMat (diagonal cv))
    (hsurj : ∀ X, (c • Qo.compMat (diagonal cv)).compMat X = c • Qo.compMat (diagonal cv) → ∃ a, ρ a = X)
    (hd : π ^ d ∣ (c • Qo.compMat (diagonal cv)).hessian.det)
    (hd' : ¬ π ^ (d + 1) ∣ (c • Qo.compMat (diagonal cv)).hessian.det) (hk : 2 * d + 1 ≤ k)
    (hm : ∀ b, cv b ∣ π ^ m) (hjm : j + m + d ≤ k) :
    Nat.card {X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}) //
        ((c • Qo.compMat (diagonal cv)).map (mk π k)).compMat X = (c • Qo.compMat (diagonal cv)).map (mk π k)} =
      (boxSub π ρ hcv j).index * Nat.card (boxSol π c Qo cv j k) := by
  classical
  set Q₁ := c • Qo.compMat (diagonal cv) with hQ₁
  set S := {X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}) // (Q₁.map (mk π k)).compMat X = Q₁.map (mk π k)}
  set W := boxSub π ρ hcv j
  have hfinR : Finite (R ⧸ Ideal.span {π ^ k}) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_quot_pow π hπ k]
    exact pow_ne_zero _ (Nat.card_pos (α := IsLocalRing.ResidueField R)).ne'
  have hfinS : Finite S := Subtype.finite
  -- lifts
  let lift : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}) → Matrix (Fin n) (Fin n) R :=
    fun X => Matrix.of fun a b => (Ideal.Quotient.mk_surjective (X a b)).choose
  have hlift : ∀ X, (lift X).map (mk π k) = X := fun X => by
    ext a b; exact (Ideal.Quotient.mk_surjective (X a b)).choose_spec
  have hredρ : ∀ a, (Q₁.map (mk π k)).compMat ((ρ a).map (mk π k)) = Q₁.map (mk π k) := fun a => by
    rw [map_compMat, hρ]
  -- the Hensel selection
  have hsel : ∀ X : S, ∃ a : A, ∀ u v, π ^ (k - d) ∣ ρ a u v - lift X.1 u v := by
    intro X
    have h1 : ∀ p : UpperIdx n, π ^ k ∣ (Q₁.compMat (lift X.1)).coeff p.1.1 p.1.2 - Q₁.coeff p.1.1 p.1.2 := by
      rw [← solMod_iff, hlift]; exact X.2
    have h2 : ∀ u v, π ^ k ∣ (Q₁.compMat (lift X.1)).coeff u v - Q₁.coeff u v := by
      intro u v
      by_cases huv : u ≤ v
      · exact h1 ⟨(u, v), huv⟩
      · rw [(Q₁.compMat _).upper (show id v < id u from not_le.mp huv), Q₁.upper (show id v < id u from not_le.mp huv),
          sub_zero]
        exact dvd_zero _
    obtain ⟨Y, hY, hYX⟩ := exists_compMat_eq_of_dvd hπ Q₁ hd hd' hk (lift X.1) h2
    obtain ⟨a, rfl⟩ := hsurj Y hY
    exact ⟨a, hYX⟩
  choose sel hselspec using hsel
  let f : S → A ⧸ W := fun X => QuotientGroup.mk (sel X)
  -- key membership facts
  have hdeep : ∀ M : Matrix (Fin n) (Fin n) R, (∀ u v, π ^ (k - d) ∣ M u v) → M ∈ boxV π cv j :=
    fun M hM => mem_boxV_of_dvd hm (by omega) hM
  have hρinv : ∀ a : A, ρ a⁻¹ * ρ a = 1 := fun a => by rw [← map_mul, inv_mul_cancel, map_one]
  -- the fibre over `mk a₀` is the box
  have hfib : ∀ a₀ : A, Nat.card {X : S // f X = QuotientGroup.mk a₀} = Nat.card (boxSol π c Qo cv j k) := by
    intro a₀
    refine Nat.card_congr
      { toFun := fun X => ⟨(ρ a₀⁻¹).map (mk π k) * X.1.1, ?_, ?_⟩
        invFun := fun Y => ⟨⟨(ρ a₀).map (mk π k) * Y.1, ?_⟩, ?_⟩
        left_inv := fun X => ?_
        right_inv := fun Y => ?_ }
    · rw [← compMat_mul, hredρ, X.1.2]
    · refine ⟨ρ a₀⁻¹ * lift X.1.1 - 1, ?_, ?_⟩
      · have hW : a₀⁻¹ * sel X.1 ∈ W := QuotientGroup.eq.mp X.2.symm
        rw [mem_boxSub, map_mul] at hW
        have : ρ a₀⁻¹ * lift X.1.1 - 1 = (ρ a₀⁻¹ * ρ (sel X.1) - 1) + ρ a₀⁻¹ * (lift X.1.1 - ρ (sel X.1)) := by
          noncomm_ring
        rw [this]
        refine add_mem hW (hdeep _ fun u v => dvd_mul_entries (fun u v => ?_) _ u v)
        rw [Matrix.sub_apply, ← dvd_neg, neg_sub]; exact hselspec X.1 u v
      · rw [add_sub_cancel, Matrix.map_mul, hlift]
    · rw [← compMat_mul, hredρ, Y.2.1]
    · obtain ⟨P, hP, hPY⟩ := Y.2.2
      show QuotientGroup.mk (sel _) = QuotientGroup.mk a₀
      refine (QuotientGroup.eq.mpr ?_).symm
      rw [mem_boxSub, map_mul]
      set X₀ : S := ⟨(ρ a₀).map (mk π k) * Y.1, by rw [← compMat_mul, hredρ, Y.2.1]⟩
      -- `lift X₀ ≡ ρ a₀ (1 + P) mod π^k`
      have hcong : ∀ u v, π ^ k ∣ lift X₀.1 u v - (ρ a₀ * (1 + P)) u v := by
        intro u v
        have : (lift X₀.1).map (mk π k) = (ρ a₀ * (1 + P)).map (mk π k) := by
          rw [hlift, Matrix.map_mul, hPY]
        have := congrFun (congrFun this u) v
        simp only [Matrix.map_apply] at this
        rw [← Ideal.mem_span_singleton]; exact Ideal.Quotient.eq.mp this
      have : ρ a₀⁻¹ * ρ (sel X₀) - 1 =
          ρ a₀⁻¹ * ((ρ (sel X₀) - lift X₀.1) + (lift X₀.1 - ρ a₀ * (1 + P))) + P := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, hρinv, Matrix.one_mul]; abel
      rw [this]
      refine add_mem (hdeep _ fun u v => dvd_mul_entries (fun u v => ?_) _ u v) hP
      rw [Matrix.add_apply]
      exact dvd_add (hselspec X₀ u v) ((pow_dvd_pow π (by omega)).trans (hcong u v))
    · apply Subtype.ext; apply Subtype.ext
      show (ρ a₀).map (mk π k) * ((ρ a₀⁻¹).map (mk π k) * X.1.1) = X.1.1
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · apply Subtype.ext
      show (ρ a₀⁻¹).map (mk π k) * ((ρ a₀).map (mk π k) * Y.1) = Y.1
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hρinv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  -- `f` is surjective, so `A ⧸ W` is finite
  have hfinB : Finite (boxSol π c Qo cv j k) := Subtype.finite
  have hbne : Nonempty (boxSol π c Qo cv j k) :=
    ⟨⟨(1 + (0 : Matrix (Fin n) (Fin n) R)).map (mk π k), by
      rw [add_zero, solMod_iff]; intro p; simp [compMat_one], 0, zero_mem _, rfl⟩⟩
  have hsurjf : Function.Surjective f := by
    intro x
    induction x using QuotientGroup.induction_on with | H a₀ => ?_
    have hpos : 0 < Nat.card {X : S // f X = QuotientGroup.mk a₀} := by
      rw [hfib a₀]; exact Nat.card_pos
    obtain ⟨⟨X, hX⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨X, hX⟩
  have hfinQ : Finite (A ⧸ W) := Finite.of_surjective f hsurjf
  have hFt : Fintype (A ⧸ W) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have : ∀ x : A ⧸ W, Nat.card {X : S // f X = x} = Nat.card (boxSol π c Qo cv j k) := by
    intro x
    induction x using QuotientGroup.induction_on with | H a₀ => exact hfib a₀
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  rfl

end Decomp

/-! ### Index arithmetic and the self-density formula -/

section Formula

variable {π : R} [Finite (IsLocalRing.ResidueField R)]

theorem index_span (hπ : Irreducible π) {t : R} (ht : t ≠ 0) :
    (Ideal.span {t} : Ideal R).toAddSubgroup.index = q R ^ ord hπ t := by
  obtain ⟨u, hu, htu⟩ := exists_eq_ord hπ ht
  have : (Ideal.span {t} : Ideal R) = Ideal.span {π ^ ord hπ t} := by
    conv_lhs => rw [htu]
    rw [Ideal.span_singleton_mul_right_unit hu]
  rw [this]; exact index_span_pow hπ _

/-- Pointwise multiplication by $t$ on $R^\iota$. -/
def scaleHom {ι : Type*} (t : ι → R) : (ι → R) →+ (ι → R) where
  toFun z := fun i => t i * z i
  map_zero' := by funext i; simp
  map_add' z z' := by funext i; simp [mul_add]

theorem scaleHom_injective {ι : Type*} {t : ι → R} (ht : ∀ i, t i ≠ 0) : Function.Injective (scaleHom t) := by
  intro z z' h
  funext i
  exact mul_left_cancel₀ (ht i) (congrFun h i)

theorem range_scaleHom {ι : Type*} (t : ι → R) :
    (scaleHom t).range = AddSubgroup.pi Set.univ fun i => (Ideal.span {t i} : Ideal R).toAddSubgroup := by
  ext s
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
    Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩ i; exact ⟨z i, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext fun i => (hz i).symm⟩

theorem index_range_scaleHom (hπ : Irreducible π) {ι : Type*} [Fintype ι] {t : ι → R} (ht : ∀ i, t i ≠ 0) :
    (scaleHom t).range.index = ∏ i, q R ^ ord hπ (t i) := by
  rw [range_scaleHom, AddSubgroup.index_pi]
  exact Finset.prod_congr rfl fun i _ => index_span hπ (ht i)

variable {n : ℕ}

theorem fL_eq (c : R) (Qo : QuadForm R n) (cv : Fin n → R) (j : ℕ) :
    fL π c Qo cv j = (scaleHom fun p => wts c cv p * π ^ j).comp (formD Qo idv).toAddMonoidHom := by
  ext z p; rfl

/-- **$c_Q = [\mathrm{Sym} : L_Q(M_n(R))]$**, the index of the image of the differential of $X \mapsto Q\circ X$ at $1$. -/
def cQ (Qo : QuadForm R n) : ℕ := ((formD Qo idv).toAddMonoidHom).range.index

theorem formF_idv (Qo : QuadForm R n) (p : UpperIdx n) : formF Qo idv p = Qo.coeff p.1.1 p.1.2 := by
  rw [formF, show toMat (idv : Fin n × Fin n → R) = 1 by ext a b; rfl, compMat_one]

/-- The image of $L_Q$ contains $\pi^{d}\mathrm{Sym}$ ($\pi^d \,\|\, \det H_Q$). -/
theorem exists_formD_eq (hπ : Irreducible π) (Qo : QuadForm R n) {d₀ : ℕ} (hd : π ^ d₀ ∣ Qo.hessian.det)
    (hd' : ¬ π ^ (d₀ + 1) ∣ Qo.hessian.det) (c' : UpperIdx n → R) : ∃ w, formD Qo idv w = π ^ d₀ • c' :=
  formD_surj Qo Qo π hπ d₀ (d₀ + 1) hd hd' (by omega) idv (fun p => by rw [formF_idv, sub_self]; exact dvd_zero _) c'

theorem scale_aux {w u t s' : R} {o j d₀ k : ℕ} (hw : w = π ^ o * u) (hu1 : u * t = 1) (hk : j + d₀ + o ≤ k) :
    w * π ^ j * (π ^ d₀ * (π ^ (k - (j + d₀ + o)) * t * s')) = π ^ k * s' := by
  have e : π ^ k = π ^ o * π ^ j * π ^ d₀ * π ^ (k - (j + d₀ + o)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [e, hw]
  linear_combination (π ^ o * π ^ j * π ^ d₀ * π ^ (k - (j + d₀ + o)) * s') * hu1

theorem le_range_fL (hπ : Irreducible π) {c : R} {Qo : QuadForm R n} {cv : Fin n → R} {d₀ j k : ℕ}
    (hw : ∀ p, wts c cv p ≠ 0) (hd : π ^ d₀ ∣ Qo.hessian.det) (hd' : ¬ π ^ (d₀ + 1) ∣ Qo.hessian.det)
    (hk : ∀ p, j + d₀ + ord hπ (wts c cv p) ≤ k) :
    piDvd π k (fun _ : UpperIdx n => (1 : R)) ≤ (fL π c Qo cv j).range := by
  intro s hs
  rw [mem_piDvd] at hs
  choose s' hs' using fun p => (by simpa using hs p : π ^ k ∣ s p)
  choose u hu hwu using fun p => exists_eq_ord hπ (hw p)
  obtain ⟨w, hw'⟩ := exists_formD_eq hπ Qo hd hd'
    (fun p => π ^ (k - (j + d₀ + ord hπ (wts c cv p))) * ↑(hu p).unit⁻¹ * s' p)
  refine ⟨w, funext fun p => ?_⟩
  show wts c cv p * π ^ j * formD Qo idv w p = s p
  rw [hw', Pi.smul_apply, smul_eq_mul, hs' p]
  exact scale_aux (hwu p) (IsUnit.mul_val_inv (hu p)) (hk p)

theorem Lam_le_Pset (c : R) (Qo : QuadForm R n) {cv ev : Fin n → R} {j k : ℕ} (hev : ∀ a, cv a * ev a = π ^ j)
    (h2j : k ≤ 2 * j) : Lam π cv ev k ≤ Pset π c Qo cv j k := by
  intro z hz
  rw [← vec_toMat z, ← sol_psi_iff hev h2j, ← solMod_iff]
  have : (1 + psi cv ev (toMat z)).map (mk π k) = (1 + psi cv ev 0).map (mk π k) := by
    rw [map_one_add_psi_eq_iff, vec_toMat]
    have : vec (0 : Matrix (Fin n) (Fin n) R) = 0 := rfl
    rw [this, add_zero]
    exact neg_mem hz
  have h0 : psi cv ev (0 : Matrix (Fin n) (Fin n) R) = 0 := by ext a b; simp [psi]
  rw [this, h0, add_zero, Matrix.map_one _ (map_zero _) (map_one _), compMat_one]

theorem exists_mul_eq_pow (hπ : Irreducible π) {t : R} (ht : t ≠ 0) {m : ℕ} (hm : ord hπ t ≤ m) :
    ∃ e, t * e = π ^ m := by
  obtain ⟨u, hu, htu⟩ := exists_eq_ord hπ ht
  generalize ord hπ t = o at htu hm
  subst htu
  refine ⟨↑hu.unit⁻¹ * π ^ (m - o), ?_⟩
  calc π ^ o * u * (↑hu.unit⁻¹ * π ^ (m - o)) = π ^ o * (u * ↑hu.unit⁻¹) * π ^ (m - o) := by ring
    _ = π ^ m := by rw [IsUnit.mul_val_inv, mul_one, ← pow_add]; congr 1; omega

theorem exists_ev (hπ : Irreducible π) {cv : Fin n → R} (hcv : ∀ a, cv a ≠ 0) {j : ℕ} (hj : ∀ a, ord hπ (cv a) ≤ j) :
    ∃ ev : Fin n → R, ∀ a, cv a * ev a = π ^ j := by
  choose ev hev using fun a => exists_mul_eq_pow hπ (hcv a) (hj a)
  exact ⟨ev, hev⟩

/-- $[\,R^{n\times n} : \Lambda\,] = q^{(k-j)n^2}$: the volume of the box is that of $\pi^{k-j}M_n(R)$ (conjugation by $D$
preserves volumes). -/
theorem index_Lam (hπ : Irreducible π) {cv ev : Fin n → R} (hcv : ∀ a, cv a ≠ 0) {j k : ℕ}
    (hev : ∀ a, cv a * ev a = π ^ j) (hjk : ∀ a, ord hπ (cv a) + j ≤ k) :
    ((Lam π cv ev k).index : ℝ) = (q R : ℝ) ^ ((k - j) * (n * n)) := by
  have hev0 : ∀ a, ev a ≠ 0 := fun a h => by
    have := hev a; rw [h, mul_zero] at this; exact pow_ne_zero j hπ.ne_zero this.symm
  have hoe : ∀ a, ord hπ (cv a) + ord hπ (ev a) = j := fun a => by
    rw [← ord_mul hπ (hcv a) (hev0 a), hev a, ord_pow]
  have hord : ∀ q' : Fin n × Fin n, ord hπ (ev q'.1 * cv q'.2) = ord hπ (ev q'.1) + ord hπ (cv q'.2) :=
    fun q' => ord_mul hπ (hev0 _) (hcv _)
  rw [Lam, index_piDvd hπ (fun q' => mul_ne_zero (hev0 _) (hcv _)) (fun q' => by
    rw [hord]; have := hoe q'.1; have := hjk q'.2; omega)]
  push_cast
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  set o : Fin n → ℕ := fun a => ord hπ (cv a)
  have hterm : ∀ q' : Fin n × Fin n, (q R : ℝ) ^ (k - ord hπ (ev q'.1 * cv q'.2)) =
      (q R : ℝ) ^ (k - j) * ((q R : ℝ) ^ o q'.1 / (q R : ℝ) ^ o q'.2) := by
    intro q'
    rw [hord, mul_div_assoc', eq_div_iff (pow_pos hq _).ne', ← pow_add, ← pow_add]
    congr 1
    have := hoe q'.1; have := hjk q'.2; simp only [o]; omega
  rw [Finset.prod_congr rfl fun q' _ => hterm q', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, ← pow_mul, Fintype.prod_prod_type]
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow, div_self (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun a _ => (pow_pos hq _).ne')),
    mul_one]

theorem ord_wts_ne_zero {c : R} (hc : c ≠ 0) {cv : Fin n → R} (hcv : ∀ a, cv a ≠ 0) (p : UpperIdx n) :
    wts c cv p ≠ 0 := mul_ne_zero (mul_ne_zero hc (hcv _)) (hcv _)

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **The self-density in box coordinates** (any residue characteristic): for $Q_1 = c\,(Q\circ D)$, $D = \mathrm{diag}(c_a)$,
$c, c_a \ne 0$, $Q$ nondegenerate, and a group $A$ acting through $\rho$ exactly by the integral isometries of $Q_1$,
$$\beta(Q_1, Q_1)\,q^{\,j\,n(n-1)/2} = [A : A_W(j)]\cdot\prod_{a \le b}q^{\mathrm{ord}(c\,c_ac_b)}\cdot[\mathrm{Sym} : L_Q(M_n(R))]$$
for all large $j$, where $A_W(j) = \{a : D\rho(a)D^{-1} \equiv 1 \bmod \pi^j\}$ (`boxSub`). -/
theorem selfDensity_formula (hπ : Irreducible π) {c : R} (hc : c ≠ 0) {Qo : QuadForm R n} (hQo : Qo.Nondegenerate)
    {cv : Fin n → R} (hcv : ∀ a, cv a ≠ 0) {A : Type*} [Group A] (ρ : A →* Matrix (Fin n) (Fin n) R)
    (hρ : ∀ a, (c • Qo.compMat (diagonal cv)).compMat (ρ a) = c • Qo.compMat (diagonal cv))
    (hsurj : ∀ X, (c • Qo.compMat (diagonal cv)).compMat X = c • Qo.compMat (diagonal cv) → ∃ a, ρ a = X) :
    ∀ᶠ j in Filter.atTop, localDensityForm (c • Qo.compMat (diagonal cv)) (c • Qo.compMat (diagonal cv)) π *
        (q R : ℝ) ^ (j * (n * (n - 1) / 2)) =
      ((boxSub π ρ hcv j).index : ℝ) * (∏ p : UpperIdx n, (q R : ℝ) ^ ord hπ (wts c cv p)) * (cQ Qo : ℝ) := by
  classical
  set Q₁ := c • Qo.compMat (diagonal cv) with hQ₁
  have hdet1 : Q₁.hessian.det ≠ 0 := nondegenerate_Q₁ hc hQo hcv
  set d₀ := ord hπ Qo.hessian.det
  set d₁ := ord hπ Q₁.hessian.det
  set m := Finset.univ.sup fun a => ord hπ (cv a)
  have hom : ∀ a, ord hπ (cv a) ≤ m := fun a => Finset.le_sup (f := fun a => ord hπ (cv a)) (Finset.mem_univ a)
  have hm : ∀ b, cv b ∣ π ^ m := fun b => by
    obtain ⟨e, he⟩ := exists_mul_eq_pow hπ (hcv b) (hom b)
    exact ⟨e, he.symm⟩
  have hw : ∀ p : UpperIdx n, ord hπ (wts c cv p) ≤ ord hπ c + 2 * m := fun p => by
    rw [wts, ord_mul hπ (mul_ne_zero hc (hcv _)) (hcv _), ord_mul hπ hc (hcv _)]
    have := hom p.1.1; have := hom p.1.2; omega
  filter_upwards [Filter.eventually_ge_atTop (d₁ + d₀ + ord hπ c + 2 * m + 1)] with j hj
  set k := 2 * j
  obtain ⟨ev, hev⟩ := exists_ev hπ hcv (j := j) fun a => by have := hom a; omega
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  -- step 1: the density at level `k`
  have hβ := localDensityForm_self_eq Q₁ π hπ d₁ (pow_ord_dvd hπ Q₁.hessian.det) (not_pow_ord_succ_dvd hπ hdet1) k
    (by omega)
  -- step 2: Hensel and the box count
  have hdec := card_sol_eq hπ c Qo hcv (j := j) (k := k) (d := d₁) (m := m) ρ hρ hsurj
    (pow_ord_dvd hπ Q₁.hessian.det) (not_pow_ord_succ_dvd hπ hdet1) (by omega) hm (by omega)
  have hbox := card_boxSol (π := π) c Qo hcv hev (le_refl k)
  have hrep : repCountForm Q₁ Q₁ π k = (boxSub π ρ hcv j).index * (Lam π cv ev k).relIndex (Pset π c Qo cv j k) := by
    rw [← hbox]; exact hdec
  -- step 3: indices
  have hΛP := Lam_le_Pset (π := π) c Qo hev (le_refl k)
  have h1 := AddSubgroup.relIndex_mul_index hΛP
  have hT := le_range_fL hπ (ord_wts_ne_zero hc hcv) (pow_ord_dvd hπ Qo.hessian.det)
    (not_pow_ord_succ_dvd hπ hQo) (d₀ := d₀) (j := j) (k := k) (fun p => by have := hw p; omega)
  have h2 : (Pset π c Qo cv j k).index = (piDvd π k fun _ : UpperIdx n => (1 : R)).relIndex (fL π c Qo cv j).range :=
    AddSubgroup.index_comap _ _
  have h3 := AddSubgroup.relIndex_mul_index hT
  have hw0 : ∀ p, wts c cv p * π ^ j ≠ 0 := fun p => mul_ne_zero (ord_wts_ne_zero hc hcv p) (pow_ne_zero _ hπ.ne_zero)
  have h4 : (fL π c Qo cv j).range.index = cQ Qo * ∏ p : UpperIdx n, q R ^ ord hπ (wts c cv p * π ^ j) := by
    rw [fL_eq, AddMonoidHom.range_comp, AddSubgroup.index_map_of_injective _ (scaleHom_injective hw0),
      index_range_scaleHom hπ hw0]; rfl
  have h5 : (piDvd π k fun _ : UpperIdx n => (1 : R)).index = ∏ _p : UpperIdx n, q R ^ k := by
    rw [index_piDvd hπ (fun _ => one_ne_zero) (fun _ => by rw [ord_unit hπ isUnit_one]; omega)]
    simp [ord_unit hπ isUnit_one]
  have h6 := index_Lam hπ hcv hev (k := k) (fun a => by have := hom a; omega)
  have h7 : ∀ p : UpperIdx n, ord hπ (wts c cv p * π ^ j) = ord hπ (wts c cv p) + j := fun p => by
    rw [ord_mul hπ (ord_wts_ne_zero hc hcv p) (pow_ne_zero _ hπ.ne_zero), ord_pow]
  -- assemble in `ℝ`
  set N := Fintype.card (UpperIdx n)
  have hN : N = n * (n + 1) / 2 := card_upperIdx n
  have hnn : n * n = N + n * (n - 1) / 2 := by
    have := self_exp n
    have hle : n * (n + 1) / 2 ≤ n * n := by
      have : n * (n + 1) / 2 ≤ n * (n + 1) / 2 + n * (n - 1) / 2 := le_self_add
      rcases n with _ | n
      · simp
      · have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (n + 1))
        have h3 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (n + 1))
        simp only [Nat.add_sub_cancel] at h3 ⊢
        nlinarith
    omega
  rw [hβ, hrep]
  push_cast
  have hcQ : cQ Qo ≠ 0 := by
    intro h0
    have := h4; rw [h0, zero_mul] at this
    have h3' := h3; rw [this, mul_zero] at h3'
    rw [h5] at h3'
    exact (Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ q_pos.ne') h3'.symm
  -- `[P : Λ] = [G : Λ] / [G : P]`
  have hPidx : ((Pset π c Qo cv j k).index : ℝ) ≠ 0 := by
    rw [h2]; intro h0
    have h3' := h3; rw [show ((piDvd π k fun _ : UpperIdx n => (1 : R)).relIndex (fL π c Qo cv j).range) = 0 by
      exact_mod_cast h0, zero_mul, h5] at h3'
    exact (Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ q_pos.ne') h3'.symm
  have eX : ((Lam π cv ev k).relIndex (Pset π c Qo cv j k) : ℝ) =
      (q R : ℝ) ^ ((k - j) * (n * n)) / (Pset π c Qo cv j k).index := by
    rw [eq_div_iff hPidx, ← h6]; exact_mod_cast h1
  have eP : ((Pset π c Qo cv j k).index : ℝ) * (cQ Qo * ∏ p : UpperIdx n, (q R : ℝ) ^ (ord hπ (wts c cv p) + j)) =
      (q R : ℝ) ^ (k * N) := by
    rw [h2]
    have := h3; rw [h4, h5] at this
    have e2 : (∏ _p : UpperIdx n, q R ^ k) = q R ^ (k * N) := by
      rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    rw [e2] at this
    simp only [h7] at this
    exact_mod_cast this
  rw [eX]
  have hPpos : (0 : ℝ) < (Pset π c Qo cv j k).index := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hPidx)
  have hprod : ∏ p : UpperIdx n, (q R : ℝ) ^ (ord hπ (wts c cv p) + j) =
      (∏ p : UpperIdx n, (q R : ℝ) ^ ord hπ (wts c cv p)) * (q R : ℝ) ^ (j * N) := by
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]
    rw [mul_comm j N]
  rw [hprod] at eP
  have ePi : ((Pset π c Qo cv j k).index : ℝ)⁻¹ =
      (cQ Qo * ((∏ p : UpperIdx n, (q R : ℝ) ^ ord hπ (wts c cv p)) * (q R : ℝ) ^ (j * N))) / (q R : ℝ) ^ (k * N) := by
    rw [← eP]; field_simp
  rw [div_eq_mul_inv _ ((Pset π c Qo cv j k).index : ℝ), ePi]
  have hk : k = 2 * j := rfl
  have e3 : (q R : ℝ) ^ ((k - j) * (n * n)) = (q R : ℝ) ^ (j * N) * (q R : ℝ) ^ (j * (n * (n - 1) / 2)) := by
    rw [← pow_add]; congr 1; rw [hk, show 2 * j - j = j by omega, hnn]; ring
  have e4 : (q R : ℝ) ^ (k * (n * (n - 1) / 2)) =
      (q R : ℝ) ^ (j * (n * (n - 1) / 2)) * (q R : ℝ) ^ (j * (n * (n - 1) / 2)) := by
    rw [← pow_add]; congr 1; rw [hk]; ring
  have e5 : (q R : ℝ) ^ (k * N) = (q R : ℝ) ^ (j * N) * (q R : ℝ) ^ (j * N) := by
    rw [← pow_add]; congr 1; rw [hk]; ring
  rw [e3, e4, e5]
  have := pow_pos hq (j * N)
  have := pow_pos hq (j * (n * (n - 1) / 2))
  field_simp

end Formula

end QuadFormsKB.Tamagawa.LatChange
