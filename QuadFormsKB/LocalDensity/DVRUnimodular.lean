/-
# Local densities over a DVR: general forms at good primes (non-dyadic reduction; Remark 3.1.1)

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$ and finite residue field $\mathbb{F}$ of size $q$).
The explicit non-dyadic results of `DVRTable2.lean` and `DVRLowerBounds.lean` are stated for unit diagonal forms
$\langle a_0, \dots, a_{n-1}\rangle$. This file makes them hold for a **general** form $Q$ at a prime $\pi \nmid 2\det H$.

**Defines** $\mathrm{GL}_n(R)$-equivalence (`DVR.IsGLEquiv`), "same counts at every level, total and non-Zero type"
(`DVR.SameCounts`), the residue of Hanke's determinant $D_Q = \det(H/2)$ (`DVR.resGramDet`, $H$ the Hessian) and the
intrinsic sign $\Phi_n(\pi)$ (`DVR.phi`, p. 357). **Proves** that counts of every type and all derived quantities
($\beta_\pi$, $C_\pi$, $C'_\pi$, local representability, $\pi$-stability) are $\mathrm{GL}_n(R)$-invariants; the non-dyadic
reduction (`DVR.exists_diag_of_unimodular`: at $\pi \nmid 2\det H$, $Q \cong \langle a_i\rangle$ with $a_i$ units and
$2^n\prod_i a_i = u^2 \det H$, $u$ a unit); and, for general $Q$ at $\pi \nmid 2\det H$: Table 1
(`DVR.card_mod_pi_of_unimodular`), Remark 3.5.1 (`DVR.isLocallyRepresentedAt_of_unimodular`), Table 2
(`DVR.table2_*_of_unimodular`), (5.10), (5.12) (`DVR.eq_5_12_of_unimodular`) and the per-place bounds L10
(`DVR.localDensity_ge_*_of_unimodular`). Also Remark 3.1.1 over a DVR (`DVR.isGoodType_diag_iff_hessian`).
**Depends on** `DVRLowerBounds.lean`.
-/
import QuadFormsKB.LocalDensity.DVRLowerBounds

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix Filter

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-! ### $\mathrm{GL}_n(R)$-equivalence and invariance of counts -/

section GLEquiv

/-- **$\mathrm{GL}_n(R)$-equivalence** of forms over $R$: $Q'(\vec x) = Q(U\vec x)$ for all $\vec x \in R^n$, for some
$n \times n$ matrix $U$ over $R$ with $\det U$ a unit. -/
def IsGLEquiv (Q Q' : QuadForm R n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) R, IsUnit U.det ∧ ∀ x, Q'.eval x = Q.eval (U *ᵥ x)

theorem IsGLEquiv.refl (Q : QuadForm R n) : IsGLEquiv Q Q :=
  ⟨1, by simp, fun x => by rw [Matrix.one_mulVec]⟩

theorem IsGLEquiv.symm {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') : IsGLEquiv Q' Q := by
  obtain ⟨U, hU, hQ⟩ := h
  refine ⟨U⁻¹, ?_, fun x => ?_⟩
  · exact Matrix.isUnit_nonsing_inv_det U hU
  · rw [hQ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]

theorem IsGLEquiv.trans {Q Q' Q'' : QuadForm R n} (h : IsGLEquiv Q Q') (h' : IsGLEquiv Q' Q'') :
    IsGLEquiv Q Q'' := by
  obtain ⟨U, hU, hQ⟩ := h
  obtain ⟨V, hV, hQ'⟩ := h'
  refine ⟨U * V, by rw [Matrix.det_mul]; exact hU.mul hV, fun x => ?_⟩
  rw [hQ', hQ, Matrix.mulVec_mulVec]

/-- **The Hessian transforms by congruence:** if $Q'(\vec x) = Q(U\vec x)$ for all $\vec x$, then
$H' = U^{\mathsf T} H U$. *Proof:* both sides are the matrix of the bilinear form $B'(\vec x, \vec y) = B(U\vec x, U\vec y)$
(`polar_eq_hessian`), evaluated at basis vectors. -/
theorem hessian_eq_of_eval {Q Q' : QuadForm R n} {U : Matrix (Fin n) (Fin n) R}
    (h : ∀ x, Q'.eval x = Q.eval (U *ᵥ x)) : Q'.hessian = Uᵀ * Q.hessian * U := by
  have key : ∀ x y : Fin n → R, x ⬝ᵥ (Q'.hessian *ᵥ y) = x ⬝ᵥ ((Uᵀ * Q.hessian * U) *ᵥ y) := by
    intro x y
    have h1 := polar_eq_hessian R Q' x y
    have h2 := polar_eq_hessian R Q (U *ᵥ x) (U *ᵥ y)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1 h2
    have h' : ∀ z, Q'.evalIn R z = Q.evalIn R (U *ᵥ z) := h
    rw [← h1, h' x, h' y, h' (x + y), Matrix.mulVec_add, h2, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Uᵀ, Matrix.vecMul_transpose]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- **The determinant of the Hessian changes by a unit square** under $\mathrm{GL}_n(R)$-equivalence. -/
theorem IsGLEquiv.det_hessian {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') :
    ∃ u : R, IsUnit u ∧ Q'.hessian.det = u ^ 2 * Q.hessian.det := by
  obtain ⟨U, hU, hQ⟩ := h
  refine ⟨U.det, hU, ?_⟩
  rw [hessian_eq_of_eval hQ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

theorem IsGLEquiv.nondegenerate {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (hQ : Q.Nondegenerate) :
    Q'.Nondegenerate := by
  obtain ⟨u, hu, he⟩ := h.det_hessian
  unfold QuadForm.Nondegenerate; rw [he]
  exact mul_ne_zero (pow_ne_zero _ hu.ne_zero) hQ

/-- Zero type is preserved by any matrix: $\vec x \equiv 0 \pmod \pi \Rightarrow M\vec x \equiv 0 \pmod \pi$. -/
theorem isZeroType_mulVec (π : R) (k : ℕ) (M : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}))
    {x : Fin n → R ⧸ Ideal.span {π ^ k}} (hx : IsZeroType π k x) : IsZeroType π k (M *ᵥ x) :=
  fun i => by
    show _ ∣ ∑ j, M i j * x j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hx j) _

/-- **The change of variables mod $\pi^k$:** for $Q'(\vec x) = Q(U\vec x)$ with $\det U$ a unit, $\vec x \mapsto U\vec x$ is a
bijection of $(R/\pi^k)^n$ carrying $Q'$ to $Q$ and preserving Zero type. -/
theorem exists_vecEquiv {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) (k : ℕ) :
    ∃ e : (Fin n → R ⧸ Ideal.span {π ^ k}) ≃ (Fin n → R ⧸ Ideal.span {π ^ k}),
      ∀ x, Q'.evalIn _ x = Q.evalIn _ (e x) ∧ (IsZeroType π k (e x) ↔ IsZeroType π k x) := by
  obtain ⟨U, hU, hQ'⟩ := h
  set K := R ⧸ Ideal.span {π ^ k}
  let f : R →+* K := Ideal.Quotient.mk _
  have hcast : ∀ (Q₁ : QuadForm R n) (z : Fin n → R),
      Q₁.evalIn K (fun i => f (z i)) = f (Q₁.eval z) := by
    intro Q₁ z
    simp [QuadForm.evalIn, map_sum, apply_ite f, f]
    rfl
  set U' := U.map f
  have hmv : ∀ z : Fin n → R, U' *ᵥ (fun i => f (z i)) = fun i => f ((U *ᵥ z) i) := by
    intro z
    funext i
    simp [U', Matrix.mulVec, dotProduct, map_sum]
  have key : ∀ x : Fin n → K, Q'.evalIn K x = Q.evalIn K (U' *ᵥ x) := by
    intro x
    obtain ⟨z, rfl⟩ : ∃ z : Fin n → R, (fun i => f (z i)) = x :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
        by funext i; exact (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
    rw [hmv, hcast, hcast, hQ']
  have hdet : IsUnit U'.det := by
    rw [show U'.det = f U.det from (RingHom.map_det f U).symm]
    exact hU.map f
  refine ⟨{ toFun := fun x => U' *ᵥ x
            invFun := fun x => U'⁻¹ *ᵥ x
            left_inv := fun x => by
              simp only
              rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
            right_inv := fun x => by
              simp only
              rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] },
    fun x => ⟨key x, ⟨fun hz => ?_, isZeroType_mulVec π k U'⟩⟩⟩
  have := isZeroType_mulVec π k U'⁻¹ hz
  simp only [Equiv.coe_fn_mk] at this
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at this

/-- **Counts of each type are $\mathrm{GL}_n(R)$-invariant:** for $T$ a type predicate that only depends on whether
$\vec x$ is of Zero type (all solutions, Zero type, non-Zero type), $r^T_{\pi^k}(Q', m) = r^T_{\pi^k}(Q, m)$. -/
theorem IsGLEquiv.repCountOf_eq {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) (k : ℕ) (m : R)
    (P : Prop → Prop) :
    repCountOf Q' π k m (fun x => P (IsZeroType π k x)) =
      repCountOf Q π k m (fun x => P (IsZeroType π k x)) := by
  obtain ⟨e, he⟩ := exists_vecEquiv h π k
  unfold repCountOf
  exact Nat.card_congr (Equiv.subtypeEquiv e fun x => by simp only [(he x).1, (he x).2])

theorem IsGLEquiv.repCount_eq {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) (k : ℕ) (m : R) :
    repCount Q' π k m = repCount Q π k m := by
  obtain ⟨e, he⟩ := exists_vecEquiv h π k
  unfold repCount
  exact Nat.card_congr (Equiv.subtypeEquiv e fun x => by rw [(he x).1])

/-- **Same counts at $\pi$**: $Q$ and $Q'$ have the same numbers of solutions mod $\pi^k$ of $Q(\vec x) \equiv m$ in total
and of non-Zero type, for every $k$ and $m$. Every quantity of Hanke's §§3–5 at $\pi$ ($\beta_\pi$, the primitive
density, $C_\pi$, $C'_\pi$, local representability, $\pi$-stability) depends only on these counts. -/
def SameCounts (Q Q' : QuadForm R n) (π : R) : Prop :=
  ∀ k m, repCount Q π k m = repCount Q' π k m ∧
    repCountOf Q π k m (fun x => ¬ IsZeroType π k x) = repCountOf Q' π k m (fun x => ¬ IsZeroType π k x)

theorem IsGLEquiv.sameCounts {Q Q' : QuadForm R n} (h : IsGLEquiv Q Q') (π : R) : SameCounts Q Q' π :=
  fun k m => ⟨(h.repCount_eq π k m).symm, (h.repCountOf_eq π k m Not).symm⟩

theorem SameCounts.symm {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) : SameCounts Q' Q π :=
  fun k m => ⟨(h k m).1.symm, (h k m).2.symm⟩

theorem SameCounts.localDensity_eq {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) (m : R) :
    localDensity Q π m = localDensity Q' π m := by
  simp only [localDensity, (h _ m).1]

theorem SameCounts.localDensityOf_eq {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) (m : R) :
    localDensityOf Q π m (fun k x => ¬ IsZeroType π k x) =
      localDensityOf Q' π m (fun k x => ¬ IsZeroType π k x) := by
  simp only [localDensityOf, (h _ m).2]

theorem SameCounts.localConstC_eq {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) (T : R) :
    localConstC Q π T = localConstC Q' π T := by
  simp only [localConstC, h.localDensity_eq, h.localDensityOf_eq]

theorem SameCounts.localConstC'_eq {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π) (T : R) :
    localConstC' Q π T = localConstC' Q' π T := by
  simp only [localConstC', h.localConstC_eq]

theorem SameCounts.isLocallyRepresentedAt_iff {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π)
    (m : R) : IsLocallyRepresentedAt Q π m ↔ IsLocallyRepresentedAt Q' π m := by
  simp only [IsLocallyRepresentedAt, (h _ m).1]

theorem SameCounts.isPStable_iff {Q Q' : QuadForm R n} {π : R} (h : SameCounts Q Q' π)
    (S₀ S₀' : Finset (Fin n)) (m : R) : IsPStable Q S₀ π m ↔ IsPStable Q' S₀' π m := by
  simp only [IsPStable, h.isLocallyRepresentedAt_iff, (h _ _).2]

end GLEquiv

/-! ### The non-dyadic reduction -/

section Reduction

/-- **Lemma 2.1 with the change of variables kept** (Hanke 2004, Lemma 2.1, p. 355, for $\pi^2 \nmid 2$): as
`exists_jordanForm`, but the normal form $Q'$ is $\mathrm{GL}_n(R)$-equivalent to $Q$ (not only count-equivalent). -/
theorem exists_jordanForm_isGLEquiv (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ^ 2 ∣ 2) :
    ∃ (Q' : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q' π P ν ∧ (¬ π ∣ 2 → P = ∅) ∧ IsGLEquiv Q Q' := by
  classical
  have h20 : (2 : R) ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hJ0 : DvrJInv π (Q.coeff + Q.coeffᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P, ν, hV, hJ⟩ := dvr_jinv_complete_aux hπ h2 _ Q.coeff ∅ ∅ (fun _ => 0) rfl hQ hJ0
  set Q' := dvr_ofMatrix (Vᵀ * Q.coeff * V) with hQ'
  have hH : Q'.hessian = Vᵀ * (Q.coeff + Q.coeffᵀ) * V := by
    rw [hQ', dvr_hessian_ofMatrix]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have heval : ∀ x, Q'.eval x = Q.eval (V *ᵥ x) := by
    intro x
    rw [hQ', dvr_eval_ofMatrix]
    show _ = Q.evalIn R (V *ᵥ x)
    rw [QuadForm.evalIn_eq_dotProduct]
    simp only [Algebra.algebraMap_self, Matrix.map_id]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    rfl
  refine ⟨Q', P, ν, dvr_isJordanForm_of_jinv h20 Q' P ν (hH ▸ hJ), fun h => ?_, V, hV, heval⟩
  by_contra hP
  exact h (hJ.1 (Finset.nonempty_iff_ne_empty.2 hP))

/-- The Hessian of a diagonal form is $\mathrm{diag}(2a_i)$, so $\det H = 2^n \prod_i a_i$. -/
theorem det_hessian_diag (a : Fin n → R) : (QuadForm.diag a).hessian.det = 2 ^ n * ∏ i, a i := by
  unfold QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  rw [Finset.prod_congr rfl fun i _ => (two_mul (a i)).symm, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The non-dyadic reduction** (Hanke 2004, Lemma 2.1, p. 355, case $\mathfrak p \nmid 2$, with the determinant tracked;
DVR analogue of `Siegel.exists_diag_unimodular_same_counts_det`): if $\pi \nmid 2$ and
$\pi \nmid \det H$, then $Q$ is $\mathrm{GL}_n(R)$-equivalent to $\langle a_0, \dots, a_{n-1}\rangle$ with all $a_i$ units and
$2^n \prod_i a_i = u^2 \det H$ for a unit $u$. So $\prod_i a_i$ and Hanke's $D_Q = \det H / 2^n$ have the same square
class, and $Q$ has the counts of every type of a unit diagonal form (`IsGLEquiv.sameCounts`). -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (p ∤ 2, with det)"]
theorem exists_diag_of_unimodular (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) :
    ∃ a : Fin n → R, (∀ i, ¬ π ∣ a i) ∧ IsGLEquiv Q (QuadForm.diag a) ∧
      ∃ u : R, IsUnit u ∧ 2 ^ n * ∏ i, a i = u ^ 2 * Q.hessian.det := by
  classical
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have h2' : ¬ π ^ 2 ∣ 2 := fun h => h2 ((dvd_pow_self π two_ne_zero).trans h)
  obtain ⟨Q', P, ν, hJ, hP, hE⟩ := exists_jordanForm_isGLEquiv Q hQ π hπ h2'
  have hP0 := hP h2
  subst hP0
  set a : Fin n → R := fun i => Q'.coeff i i
  have hQ'a : Q' = QuadForm.diag a := by
    ext i j
    simp only [QuadForm.diag, Matrix.diagonal_apply, a]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne]; exact hJ.2.2.2.1 i j h (by simp)
    · simp
    · rw [if_neg h.ne']; exact Q'.upper (show id j < id i from h)
  rw [hQ'a] at hE
  obtain ⟨u, hu, hdu⟩ := hE.det_hessian
  rw [det_hessian_diag] at hdu
  refine ⟨a, fun i hi => ?_, hE, u, hu, hdu⟩
  have : π ∣ u ^ 2 * Q.hessian.det := hdu ▸ (Finset.dvd_prod_of_mem a (Finset.mem_univ i) |>.trans
    (dvd_mul_left _ _) |> (hi.trans))
  rcases hπ.prime.dvd_or_dvd this with h | h
  · exact dvr_not_dvd_of_isUnit hπ (hu.pow 2) h
  · exact hdet h

end Reduction

/-! ### $\Phi_n(\pi)$ for a general form, and the transfer of the character -/

section Phi

/-- **The residue of Hanke's determinant** $D_Q = \det(Q_\mathfrak p)$ (p. 355; $Q_\mathfrak p$ the Gram matrix $H/2$):
$\overline{D_Q} = \overline{\det H}/2^n \in \mathbb{F} = R/\pi$. Meaningful for $\pi \nmid 2$ (junk $0$ when $2 = 0$ in $\mathbb{F}$). -/
noncomputable def resGramDet (Q : QuadForm R n) : 𝔽 := res Q.hessian.det / 2 ^ n

/-- **$\chi((-1)^{n/2} D)$** (Hanke 2004, $\Phi_n(\mathfrak p)$ for even $n$, p. 357): the quadratic character of the
residue field at $(-1)^{\lfloor n/2 \rfloor}\overline{D_Q}$. -/
noncomputable def chiDisc [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) : ℤ :=
  quadraticChar 𝔽 ((-1) ^ (n / 2) * resGramDet Q)

/-- **$\chi((-1)^{(n-1)/2} D T')$** (Hanke 2004, $\Phi_n(\mathfrak p)$ for odd $n$, p. 357). -/
noncomputable def chiDiscT [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (T : R) : ℤ :=
  quadraticChar 𝔽 ((-1) ^ ((n - 1) / 2) * resGramDet Q * res T)

/-- **$\Phi_n(\pi)$ for a general form** (Hanke 2004, p. 357, at $\pi \nmid 2D$): $\chi((-1)^{n/2} D)$ for $n$ even,
$\chi((-1)^{(n-1)/2} D T')$ for $n$ odd ($\chi$ the quadratic character of $R/\pi$, $D = \det H/2^n$). For a unit
diagonal form equivalent to $Q$ it is `phiN` (`phi_eq_phiN`). -/
@[kb "hanke2004" "Φ_n(𝔭), p. 357"]
noncomputable def phi [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (T : R) : ℤ :=
  if Even n then chiDisc Q else chiDiscT Q T

/-- **Non-dyadic reduction with the character tracked**: at $\pi \nmid 2\det H$, $Q$ has the counts of a unit
diagonal form $\langle a_i\rangle$ whose characters $\chi(\pm\prod_i a_i \cdots)$ are those of $D_Q$. -/
theorem exists_diag_sameCounts [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) :
    ∃ a : Fin n → R, (∀ i, ¬ π ∣ a i) ∧ SameCounts Q (QuadForm.diag a) π ∧
      (∀ s : ℕ, quadraticChar 𝔽 (res ((-1) ^ s * ∏ i, a i)) =
        quadraticChar 𝔽 ((-1) ^ s * resGramDet Q)) ∧
      (∀ (s : ℕ) (T : R), quadraticChar 𝔽 (res ((-1) ^ s * (∏ i, a i) * T)) =
        quadraticChar 𝔽 ((-1) ^ s * resGramDet Q * res T)) := by
  obtain ⟨a, ha, hE, u, hu, hdu⟩ := exists_diag_of_unimodular Q π hπ h2 hdet
  have h2F : (2 : 𝔽) ≠ 0 := by
    rw [← map_ofNat res 2]; exact fun h => h2 ((residue_eq_zero_iff_dvd hπ 2).1 h)
  have hu0 : res u ≠ 0 := (hu.map res).ne_zero
  have hres : res (∏ i, a i) = res u ^ 2 * resGramDet Q := by
    have h := congrArg res hdu
    simp only [map_mul, map_pow, map_ofNat] at h
    unfold resGramDet
    rw [mul_div_assoc', eq_div_iff (pow_ne_zero _ h2F), mul_comm, h]
  have key : ∀ c : 𝔽, quadraticChar 𝔽 (c * res (∏ i, a i)) = quadraticChar 𝔽 (c * resGramDet Q) := by
    intro c
    rw [hres, show c * (res u ^ 2 * resGramDet Q) = c * resGramDet Q * res u ^ 2 by ring, map_mul,
      quadraticChar_sq_one' hu0, mul_one]
  refine ⟨a, ha, hE.sameCounts π, fun s => ?_, fun s T => ?_⟩
  · have : res ((-1) ^ s * ∏ i, a i) = (-1) ^ s * res (∏ i, a i) := by simp
    rw [this, key]
  · have : res ((-1) ^ s * (∏ i, a i) * T) = ((-1) ^ s * res T) * res (∏ i, a i) := by simp; ring
    rw [this, key]; ring_nf

/-- For the diagonal form of `exists_diag_sameCounts`, Hanke's $\Phi_n$ of $Q$ is that of $\langle a_i \rangle$. -/
theorem phi_eq_phiN [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (a : Fin n → R)
    (hE : ∀ s : ℕ, quadraticChar 𝔽 (res ((-1) ^ s * ∏ i, a i)) = quadraticChar 𝔽 ((-1) ^ s * resGramDet Q))
    (hO : ∀ (s : ℕ) (T : R), quadraticChar 𝔽 (res ((-1) ^ s * (∏ i, a i) * T)) =
        quadraticChar 𝔽 ((-1) ^ s * resGramDet Q * res T)) (T : R) :
    phi Q T = phiN a T := by
  unfold phi phiN chiDisc chiDiscT
  split_ifs
  · rw [hE]
  · rw [hO]

end Phi

/-! ### The non-dyadic results for a general form at $\pi \nmid 2\det H$

Each is the unit diagonal result transported along `exists_diag_sameCounts`; the hypotheses $\pi \nmid 2$, $\pi \nmid \det H$
say $\mathfrak p \nmid 2N$ (`DVRLevel.lean`: at $\pi \nmid 2$, $\pi \nmid N \iff \pi \nmid \det H$). -/

section General

/-- **Table 1 for a general form** (Hanke 2004, Table 1, p. 363, for $\mathfrak p \nmid 2N$, all $n \ge 1$): with
$q = \#R/\pi$, $u$ a unit, $\chi_D = \chi((-1)^{n/2}D)$ (`chiDisc`):
- $n$ even: $r_\pi(0) = q^{n-1} + \chi_D (q-1) q^{n/2-1}$, $r_\pi(u) = q^{n-1} - \chi_D q^{n/2-1}$;
- $n$ odd: $r_\pi(0) = q^{n-1}$, $r_\pi(u) = q^{n-1} + \chi((-1)^{(n-1)/2}Du)\, q^{(n-1)/2}$ (`chiDiscT`).
From `card_diag_mod_pi` and the non-dyadic reduction. -/
@[kb "hanke2004" "Table 1, p. 363 (general Q, p ∤ 2N)"]
theorem card_mod_pi_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 1 ≤ n) (u : R) (hu : ¬ π ∣ u) :
    (Even n →
      (repCount Q π 1 0 : ℤ) = (q R : ℤ) ^ (n - 1) + chiDisc Q * ((q R : ℤ) - 1) * (q R : ℤ) ^ (n / 2 - 1) ∧
      (repCount Q π 1 u : ℤ) = (q R : ℤ) ^ (n - 1) - chiDisc Q * (q R : ℤ) ^ (n / 2 - 1)) ∧
    (Odd n →
      repCount Q π 1 0 = q R ^ (n - 1) ∧
      (repCount Q π 1 u : ℤ) = (q R : ℤ) ^ (n - 1) + chiDiscT Q u * (q R : ℤ) ^ ((n - 1) / 2)) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← (hS _ _).1, hE, hO, chiDisc, chiDiscT] using card_diag_mod_pi a π hπ h2 ha hn u hu

/-- **Remark 3.5.1 for a general form** (Hanke 2004, p. 362): for $n \ge 3$ and $\pi \nmid 2\det H$, every $m$ is
locally represented at $\pi$. From `isLocallyRepresentedAt_of_good`. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (general Q)"]
theorem isLocallyRepresentedAt_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hn : 3 ≤ n) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) (m : R) : IsLocallyRepresentedAt Q π m := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  exact (hS.isLocallyRepresentedAt_iff m).2 (isLocallyRepresentedAt_of_good a hn π hπ h2 ha m)

/-- **Every $T$ is $\pi$-stable at $\pi \nmid 2\det H$** ($n \ge 3$). From `isPStable_diag`. -/
theorem isPStable_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (S₀ : Finset (Fin n)) (T : R) : IsPStable Q S₀ π T := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  exact (hS.isPStable_iff S₀ S₀ T).2 (isPStable_diag a π hπ h2 ha hn S₀ T)

/-- **$\beta_\pi(T')$ for a general form, $n$ odd, $\pi \nmid T'$:** $1 + \chi((-1)^{(n-1)/2}DT')\,q^{-(n-1)/2}$. -/
theorem localDensity_odd_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hodd : Odd n) (T : R) (hT : ¬ π ∣ T) :
    localDensity Q π T = 1 + (chiDiscT Q T : ℝ) / (q R : ℝ) ^ ((n - 1) / 2) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← hS.localDensity_eq, hO, chiDiscT] using localDensity_diag_odd_unit a π hπ h2 ha hodd T hT

/-- **$\beta_\pi(T')$ for a general form, $n$ odd, $\mathrm{ord}_\pi T' = 1$:** $1 - q^{-(n-1)}$. -/
theorem localDensity_odd_ord_one_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) (hodd : Odd n) (T : R) (h1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localDensity Q π T = 1 - 1 / (q R : ℝ) ^ (n - 1) := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [hS.localDensity_eq]; exact localDensity_diag_odd_ord_one a π hπ h2 ha hodd T h1 hT2

/-- **$\beta_\pi(T')$ for a general form, $n$ even, $\pi \nmid T'$:** $1 - \chi((-1)^{n/2}D)\,q^{-n/2}$. -/
theorem localDensity_even_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 2 ≤ n) (heven : Even n) (T : R) (hT : ¬ π ∣ T) :
    localDensity Q π T = 1 - (chiDisc Q : ℝ) / (q R : ℝ) ^ (n / 2) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← hS.localDensity_eq, hE, chiDisc] using
    localDensity_diag_even_unit a π hπ h2 ha hn heven T hT

/-- **$\beta_\pi(T')$ for a general form, $n$ even, $\mathrm{ord}_\pi T' = 1$:**
$(1 - \chi_D q^{-n/2})(1 + \chi_D q^{-(n-2)/2})$, $\chi_D = \chi((-1)^{n/2}D)$. -/
theorem localDensity_even_ord_one_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) (hn : 2 ≤ n) (heven : Even n) (T : R) (h1 : π ∣ T)
    (hT2 : ¬ π ^ 2 ∣ T) :
    localDensity Q π T = (1 - (chiDisc Q : ℝ) / (q R : ℝ) ^ (n / 2)) *
      (1 + (chiDisc Q : ℝ) / (q R : ℝ) ^ ((n - 2) / 2)) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← hS.localDensity_eq, hE, chiDisc] using
    localDensity_diag_even_ord_one a π hπ h2 ha hn heven T h1 hT2

/-- **Table 2 for a general form, $n$ odd, $\pi \nmid T'$** (Hanke 2004, Table 2, p. 370, at $\mathfrak p \nmid 2N$):
$C_\pi(T') = \dfrac{q^{n-2} - q^{(n-3)/2}\Phi_n}{q^{n-2} - 1}$, $\Phi_n = \chi((-1)^{(n-1)/2} D T')$. From `table2_odd_unit`. -/
@[kb "hanke2004" "Table 2, p. 370 (general Q, p ∤ 2N)"]
theorem table2_odd_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (hodd : Odd n) (T : R) (hT : ¬ π ∣ T) :
    localConstC Q π T =
      ((q R : ℝ) ^ (n - 2) - (q R : ℝ) ^ ((n - 3) / 2) * chiDiscT Q T) / ((q R : ℝ) ^ (n - 2) - 1) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← hS.localConstC_eq, hO, chiDiscT] using table2_odd_unit a π hπ h2 ha hn hodd T hT

/-- **Table 2 for a general form, $n$ even, $\pi \nmid T'$** (Hanke 2004, Table 2, p. 370, at $\mathfrak p \nmid 2N$):
$C_\pi(T') = \dfrac{q^{(n-2)/2}}{q^{(n-2)/2} - \Phi_n}$, $\Phi_n = \chi((-1)^{n/2} D)$. From `table2_even_unit`. -/
@[kb "hanke2004" "Table 2, p. 370 (general Q, p ∤ 2N)"]
theorem table2_even_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (heven : Even n) (T : R) (hT : ¬ π ∣ T) :
    localConstC Q π T = (q R : ℝ) ^ ((n - 2) / 2) / ((q R : ℝ) ^ ((n - 2) / 2) - chiDisc Q) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  simpa only [← hS.localConstC_eq, hE, chiDisc] using table2_even_unit a π hπ h2 ha hn heven T hT

/-- **Table 2 for a general form, $\mathrm{ord}_\pi T' = 1$** (Hanke 2004, Table 2, p. 370; (5.9)):
$C_\pi(T') = \dfrac{q^{n-2}}{q^{n-2} - 1}$. From `table2_ord_one`. -/
@[kb "hanke2004" "Table 2, p. 370; (5.9) (general Q, p ∤ 2N)"]
theorem table2_ord_one_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (T : R) (hT1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC Q π T = (q R : ℝ) ^ (n - 2) / ((q R : ℝ) ^ (n - 2) - 1) := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [hS.localConstC_eq]; exact table2_ord_one a π hπ h2 ha hn T hT1 hT2

/-- **(5.10) for a general ternary form** (Hanke 2004, p. 371) at $\pi \nmid 2\det H$, with
$\psi = \chi(-DT')$ (`chiDiscT`). From `eq_5_10`. -/
@[kb "hanke2004" "(5.10), p. 371 (general Q)"]
theorem eq_5_10_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R 3) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (T : R) (ν : ℕ) :
    let C := localConstC Q π T
    (¬ π ∣ T → chiDiscT Q T = 1 → C + (1 - C) / (q R : ℝ) ^ ν = 1) ∧
    (¬ π ∣ T → chiDiscT Q T = -1 →
      C + (1 - C) / (q R : ℝ) ^ ν =
        ((q R : ℝ) ^ ν + 2 * ∑ μ ∈ Finset.range ν, (q R : ℝ) ^ μ) / (q R : ℝ) ^ ν) ∧
    (π ∣ T → ¬ π ^ 2 ∣ T →
      C + (1 - C) / (q R : ℝ) ^ ν = (∑ μ ∈ Finset.range (ν + 1), (q R : ℝ) ^ μ) / (q R : ℝ) ^ ν) := by
  intro C
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  have h := eq_5_10 a π hπ h2 ha T ν
  have hψ : quadraticChar 𝔽 (res (-(∏ i, a i) * T)) = chiDiscT Q T := by
    rw [chiDiscT, ← hO]; congr 2; ring
  simp only [hψ] at h
  simpa only [C, hS.localConstC_eq] using h

/-- **$C'_\pi(T') = 1$ for $\mathrm{ord}_\pi T' = 1$**, general form at $\pi \nmid 2\det H$. -/
theorem localConstC'_ord_one_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (T : R) (h1 : π ∣ T) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC' Q π T = 1 := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [hS.localConstC'_eq]; exact localConstC'_diag_ord_one a π hπ h2 ha hn T h1 hT2

/-- **$C'_\pi(T')$, general form, $n$ odd, $\pi \nmid T'$** (Table 2): $1$ if $\Phi_n = -1$, and
$C_\pi(T') = \frac{1 - q^{-(n-1)/2}}{1 - q^{-(n-2)}}$ if $\Phi_n = 1$. -/
theorem localConstC'_odd_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (hodd : Odd n) (T : R) (hT : ¬ π ∣ T) :
    (chiDiscT Q T = -1 → localConstC' Q π T = 1) ∧
    (chiDiscT Q T = 1 → localConstC' Q π T = localConstC Q π T ∧
      localConstC Q π T = (1 - 1 / (q R : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (q R : ℝ) ^ (n - 2))) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  have h := localConstC'_diag_odd_unit a π hπ h2 ha hn hodd T hT
  simp only [hO] at h
  simpa only [chiDiscT, hS.localConstC_eq, hS.localConstC'_eq] using h

/-- **$C'_\pi(T')$, general form, $n$ even, $\pi \nmid T'$** (Table 2): $1$ if $\Phi_n = 1$, $X/(X+1)$ if
$\Phi_n = -1$ ($X = q^{(n-2)/2}$). -/
theorem localConstC'_even_unit_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 4 ≤ n) (heven : Even n) (T : R) (hT : ¬ π ∣ T) :
    (chiDisc Q = 1 → localConstC' Q π T = 1) ∧
    (chiDisc Q = -1 →
      localConstC' Q π T = (q R : ℝ) ^ ((n - 2) / 2) / ((q R : ℝ) ^ ((n - 2) / 2) + 1)) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  have h := localConstC'_diag_even_unit a π hπ h2 ha hn heven T hT
  simp only [hE] at h
  simpa only [chiDisc, hS.localConstC'_eq] using h

/-- **(5.12), corrected, for a general form** (Hanke 2004, p. 371) at non-dyadic $\pi \nmid N$: for $\pi^2 \nmid T'$,
$C'_\pi(T') = 1 \iff n = 3$ or $\pi \mid T'$ or $\Phi_n(\pi) = (-1)^n$, with the intrinsic $\Phi_n$ (`phi`). See the
erratum note at `LocalDensity.eq_5_12`. From `eq_5_12`. -/
@[kb "hanke2004" "(5.12), p. 371 (corrected; general Q)"]
theorem eq_5_12_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (T : R) (hT2 : ¬ π ^ 2 ∣ T) :
    localConstC' Q π T = 1 ↔ n = 3 ∨ π ∣ T ∨ phi Q T = (-1) ^ n := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [hS.localConstC'_eq, phi_eq_phiN Q a hE hO]
  exact eq_5_12 a π hπ h2 ha hn T hT2

/-- **$C'_\pi(T') = 1$ for $n = 3$**, general ternary form at $\pi \nmid 2\det H$ ((5.12); Thm 5.7(a)). -/
@[kb "hanke2004" "(5.12), p. 371 (n = 3, general Q)"]
theorem localConstC'_three_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R 3) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (T : R) (hT2 : ¬ π ^ 2 ∣ T) : localConstC' Q π T = 1 :=
  (eq_5_12_of_unimodular Q π hπ h2 hdet le_rfl T hT2).2 (Or.inl rfl)

open Classical in
/-- **Per-place lower bound L10, $n$ even, general form at non-dyadic $\pi \nmid N$** (proof of Thm 5.7(b),(c),
p. 374): for $m \ne 0$, $\beta_\pi(m) \ge (1 - \chi_D q^{-n/2}) \cdot \frac{X-1}{X+1}$ if $\chi_D = -1$ and $\pi \mid m$, and
$\ge 1 - \chi_D q^{-n/2}$ otherwise ($X = q^{(n-2)/2}$, $\chi_D = \chi((-1)^{n/2}D)$). From `localDensity_ge_even`. -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (local factor at p ∤ 2N, n even, general Q)"]
theorem localDensity_ge_even_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 4 ≤ n) (heven : Even n) (m : R) (hm : m ≠ 0) :
    (1 - (chiDisc Q : ℝ) / (q R : ℝ) ^ (n / 2)) *
        (if chiDisc Q = -1 ∧ π ∣ m then
          ((q R : ℝ) ^ ((n - 2) / 2) - 1) / ((q R : ℝ) ^ ((n - 2) / 2) + 1) else 1) ≤
      localDensity Q π m := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  have h := localDensity_ge_even a π hπ h2 ha hn heven m hm
  simp only [hE] at h
  simp only [chiDisc, hS.localDensity_eq]
  convert h using 2
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

open Classical in
/-- **Per-place lower bound L10, $n$ odd, general form at non-dyadic $\pi \nmid N$** (proof of Thm 5.7(a),(c),
p. 375), with $\Phi = \chi((-1)^{(n-1)/2}DT')$. From `localDensity_ge_odd`. -/
@[kb "hanke2004" "Proof of Thm 5.7(a),(c), p. 375 (local factor at p ∤ 2N, n odd, general Q)"]
theorem localDensity_ge_odd_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (hn : 3 ≤ n) (hodd : Odd n) (T : R) (hT0 : T ≠ 0) (hT2 : ¬ π ^ 2 ∣ T)
    (ν : ℕ) :
    (if π ∣ T then 1 - 1 / (q R : ℝ) ^ (n - 1) else
        1 + (chiDiscT Q T : ℝ) / (q R : ℝ) ^ ((n - 1) / 2)) *
      (if ¬ π ∣ T ∧ chiDiscT Q T = 1 then
        (1 - 1 / (q R : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (q R : ℝ) ^ (n - 2)) else 1) ≤
      localDensity Q π (π ^ (2 * ν) * T) := by
  obtain ⟨a, ha, hS, hE, hO⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  have h := localDensity_ge_odd a π hπ h2 ha hn hodd T hT0 hT2 ν
  simp only [hO] at h
  simp only [chiDiscT, hS.localDensity_eq]
  convert h using 2
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-- **$n = 3$, general form at non-dyadic $\pi \nmid N$:** $\beta_\pi(T'\pi^{2\nu}) \ge \beta_\pi(T')$ (first part of
Thm 5.7(a)). From `localDensity_ge_three`. -/
@[kb "hanke2004" "Thm 5.7(a), p. 374 (p ∤ 2N, n = 3, general Q)"]
theorem localDensity_ge_three_of_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R 3) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q.hessian.det) (T : R) (hT0 : T ≠ 0) (hT2 : ¬ π ^ 2 ∣ T) (ν : ℕ) :
    localDensity Q π T ≤ localDensity Q π (π ^ (2 * ν) * T) := by
  obtain ⟨a, ha, hS, -⟩ := exists_diag_sameCounts Q π hπ h2 hdet
  rw [hS.localDensity_eq, hS.localDensity_eq]
  exact localDensity_ge_three a π hπ h2 ha T hT0 hT2 ν

end General

/-! ### Remark 3.1.1 over a DVR -/

section Remark311

open Classical in
/-- **Remark 3.1.1 over a DVR, $\pi \nmid 2$** (Hanke 2004, p. 358, corrected; DVR analogue of
`LocalDensity.isGoodType_diag_iff_hessian`): for a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ (any $a_i$) with
unimodular coordinates $S_0 = \{i : \pi \nmid a_i\}$ and $k \ge 1$, $\vec x \bmod \pi^k$ is of Good type iff it is not of
Zero type and some entry of $H\vec x$ is $\not\equiv 0 \pmod \pi$, i.e. $\vec x \notin L^{\mathfrak p} =
\{\vec x : B(\vec x, L) \subseteq \mathfrak p\}$. *Update:* the printed
$B(\vec x, L) \subseteq \mathfrak o_\mathfrak p$ should read $\subseteq \mathfrak p$, and the criterion holds only for
$\mathfrak p \nmid 2$. *Proof:* $(H\vec x)_j = 2a_jx_j$ and $2$ is a unit mod $\pi$. -/
@[kb "hanke2004" "Remark 3.1.1, p. 358 (corrected; over a DVR)"]
theorem isGoodType_diag_iff_hessian (a : Fin n → R) (π : R) (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (k : ℕ)
    (hk : 1 ≤ k) (x : Fin n → R ⧸ Ideal.span {π ^ k}) :
    IsGoodType (Finset.univ.filter fun i => ¬ π ∣ a i) π k x ↔
      ¬ IsZeroType π k x ∧ ∃ j, ¬ Ideal.Quotient.mk (Ideal.span {π ^ k}) π ∣
        ((QuadForm.diag a).hessian.map (Ideal.Quotient.mk (Ideal.span {π ^ k})) *ᵥ x) j := by
  set f := Ideal.Quotient.mk (Ideal.span {π ^ k})
  have hent : ∀ j, ((QuadForm.diag a).hessian.map f *ᵥ x) j = f (2 * a j) * x j := by
    intro j
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
    · simp [QuadForm.hessian, QuadForm.diag, two_mul]
    · intro b _ hb
      simp [QuadForm.hessian, QuadForm.diag, Ne.symm hb]
    · simp
  have hprime : ∀ y z : R, f π ∣ f y * f z ↔ π ∣ y ∨ π ∣ z := by
    intro y z
    rw [← map_mul, mk_pi_dvd_iff π k hk]
    exact ⟨fun h => hπ.prime.dvd_or_dvd h, fun h => h.elim (fun h => h.mul_right _) (fun h => h.mul_left _)⟩
  unfold IsGoodType
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, fun h => ?_⟩
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x i)
    rw [hent, ← hz, hprime] at h
    rw [← hz, mk_pi_dvd_iff π k hk] at hx
    rcases h with h | h
    · rcases hπ.prime.dvd_or_dvd h with h | h
      · exact h2 h
      · exact (Finset.mem_filter.1 hi).2 h
    · exact hx h
  · rintro ⟨j, hj⟩
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x j)
    rw [hent, ← hz, hprime, not_or] at hj
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hj.1 (h.mul_left 2)⟩, ?_⟩
    rw [← hz, mk_pi_dvd_iff π k hk]; exact hj.2

end Remark311

end QuadFormsKB.LocalDensity.DVR
