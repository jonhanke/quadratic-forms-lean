/-
# Unimodular forms over a complete non-dyadic DVR: classification by the determinant

**Layer:** $R$ a complete DVR (`IsAdicComplete (maximalIdeal R) R`) with uniformizer $\pi$, $\pi \nmid 2$, finite residue field
$\mathbb F$. (In the application: $R = \mathfrak o_\mathfrak p$, the completion of $\mathcal O_F$ at a prime
$\mathfrak p \nmid 2$, with the instance of `LocalDensity/NFBridge.lean`.)

**Proves** the classification of unimodular forms (O'Meara 1963, 92:1, p. 246, and 92:2, p. 247, there over a non-dyadic local field; Cassels, *Rational Quadratic Forms*, Ch. 8,
Lemma 3.4, p. 115, and Thm. 3.1, Corollary, p. 116, there over $\mathbb{Z}_p$, $p \ne 2$): if $\pi \nmid \det H$ and $\det H' = u^2\det H$ for a unit $u$, then $Q \cong Q'$ over $R$
(`isometricGL_of_unimodular_dvr`). This generalizes `Siegel.Kneser.isometricGL_of_unimodular` ($R = \mathbb Z_p$) with the
same proof:
* a unit whose residue is a nonzero square is a square (Hensel; `LocalDensity.DVR.isSquare_iff_quadraticChar_residue`);
* for units $a, b$ there are $x, y$ with $ax^2 + by^2 = 1$ (`exists_binary_one_dvr`: a solution mod $\pi$ from the binary count of
  Table 1, `LocalDensity.DVR.binary_countF`, lifted by Hensel);
* $\langle a_0, \dots, a_k\rangle \cong \langle 1, \dots, 1, \prod a_i\rangle$ by $2\times2$ rotations (`isometricGL_diag_normal_dvr`), and the
  last coefficient is determined by $\det H$ up to unit squares.
-/
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.LocalDensity.DyadicArf

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Lattices.Nbr

/-- **The Hessian transforms by congruence** (any commutative ring): if $Q'(x) = Q(Ux)$ for all $x$ then $H' = U^{\mathsf T}HU$. -/
theorem hessian_eq_of_eval' {S : Type*} [CommRing S] {n : ℕ} {Q Q' : QuadForm S n}
    {U : Matrix (Fin n) (Fin n) S} (h : ∀ x, Q'.eval x = Q.eval (U *ᵥ x)) :
    Q'.hessian = Uᵀ * Q.hessian * U := by
  have key : ∀ x y : Fin n → S, x ⬝ᵥ (Q'.hessian *ᵥ y) = x ⬝ᵥ ((Uᵀ * Q.hessian * U) *ᵥ y) := by
    intro x y
    have h1 := QuadForm.polar_eq_hessian S Q' x y
    have h2 := QuadForm.polar_eq_hessian S Q (U *ᵥ x) (U *ᵥ y)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1 h2
    have h' : ∀ z, Q'.evalIn S z = Q.evalIn S (U *ᵥ z) := h
    rw [← h1, h' x, h' y, h' (x + y), Matrix.mulVec_add, h2, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Uᵀ, Matrix.vecMul_transpose]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- Evaluation over an algebra is evaluation of the base change. -/
theorem evalIn_eq_eval_map' {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] {n : ℕ} (B : QuadForm A n)
    (z : Fin n → K) : B.evalIn K z = (B.map (algebraMap A K)).eval z := by
  simp [QuadForm.evalIn, QuadForm.map]

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

variable {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
include hπ h2

/-- **Hensel:** an element whose residue is a nonzero square is a square. -/
theorem exists_sq_eq_of_residue (c : R) {s : 𝔽} (hs : s ≠ 0) (hc : res c = s ^ 2) :
    ∃ z : R, z ^ 2 = c := by
  have hcπ : ¬ π ∣ c := fun h => by
    have := (DVR.residue_eq_zero_iff_dvd hπ c).mpr h
    rw [hc] at this; exact hs (pow_eq_zero_iff two_ne_zero |>.mp this)
  have : IsSquare c := (DVR.isSquare_iff_quadraticChar_residue hπ h2 hcπ).mpr (by
    rw [hc]; exact quadraticChar_sq_one' hs)
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by rw [hz, sq]⟩

/-- **Binary unit forms represent $1$** over a complete non-dyadic DVR: for units $a, b$ there are $x, y$ with $ax^2 + by^2 = 1$. -/
theorem exists_binary_one_dvr {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    ∃ x y : R, a * x ^ 2 + b * y ^ 2 = 1 := by
  set A := res a with hAd
  set B := res b with hBd
  have hA : A ≠ 0 := fun h => (ha.map res).ne_zero h
  have hB : B ≠ 0 := fun h => (hb.map res).ne_zero h
  have hF := DVR.ringChar_residueField_ne_two hπ h2
  have hcount := DVR.binary_countF hF A B hA hB 1
  obtain ⟨s, t, hst⟩ : ∃ s t : 𝔽, A * s ^ 2 + B * t ^ 2 = 1 := by
    by_contra h
    push Not at h
    have : (∑ y : 𝔽, ∑ z : 𝔽, (if A * y ^ 2 + B * z ^ 2 = 1 then 1 else 0 : ℤ)) = 0 :=
      Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => if_neg (h y z)
    rw [this, if_neg one_ne_zero, mul_zero, add_zero] at hcount
    have hχ : quadraticChar 𝔽 (-(A * B)) ≤ 1 := by
      rcases quadraticChar_dichotomy (F := 𝔽)
        (neg_ne_zero.mpr (mul_ne_zero hA hB)) with h | h <;> rw [h] <;> norm_num
    have := DVR.three_le_q hπ h2
    have hq : (3 : ℤ) ≤ Fintype.card 𝔽 := by
      have e : DVR.q R = Fintype.card 𝔽 := by rw [DVR.q, Nat.card_eq_fintype_card]
      rw [← e]; exact_mod_cast this
    linarith
  have hinv : ∀ {u : R} (hu : IsUnit u), res (↑hu.unit⁻¹ : R) = (res u)⁻¹ := by
    intro u hu
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  by_cases hs : s = 0
  · subst hs
    have hBt : B * t ^ 2 = 1 := by simpa using hst
    have ht : t ≠ 0 := by rintro rfl; simp at hBt
    obtain ⟨y, hy⟩ := exists_sq_eq_of_residue hπ h2 (↑hb.unit⁻¹ : R) ht (by
      rw [hinv hb, ← hBd]; exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hBt)).symm)
    refine ⟨0, y, ?_⟩
    rw [hy]; simp
  · obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective t
    obtain ⟨x, hx⟩ := exists_sq_eq_of_residue hπ h2 ((1 - b * y ^ 2) * ↑ha.unit⁻¹) hs (by
      rw [map_mul, map_sub, map_one, map_mul, map_pow, hy, hinv ha, ← hAd, ← hBd,
        show 1 - B * t ^ 2 = A * s ^ 2 by linear_combination -hst]
      field_simp)
    refine ⟨x, y, ?_⟩
    rw [hx, mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]; ring

/-- **Normal form of a unit diagonal form** (complete non-dyadic DVR): $\langle a_0, \dots, a_k\rangle \cong \langle 1, \dots, 1, a_0 \cdots a_k\rangle$. -/
theorem isometricGL_diag_normal_dvr {k : ℕ} (a : Fin (k + 1) → R) (ha : ∀ i, IsUnit (a i)) :
    IsometricGL (QuadForm.diag a)
      (QuadForm.diag (Function.update (1 : Fin (k + 1) → R) (Fin.last k) (∏ i, a i))) := by
  classical
  let P : ℕ → R := fun m => ∏ s ∈ Finset.univ.filter (fun s : Fin (k + 1) => s.val < m), a s
  let b : ℕ → Fin (k + 1) → R := fun m r =>
    if r = Fin.last k then a (Fin.last k) * P m else if r.val < m then 1 else a r
  have hP : ∀ m, IsUnit (P m) := fun m => IsUnit.prod_iff.mpr fun s _ => ha s
  have key : ∀ m ≤ k, IsometricGL (QuadForm.diag a) (QuadForm.diag (b m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : b 0 = a := by
        funext r
        by_cases hr : r = Fin.last k
        · subst hr; simp [b, P]
        · simp [b, hr]
      rw [this]; exact IsometricGL.refl _
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      set i : Fin (k + 1) := ⟨m, by omega⟩
      have hi : i ≠ Fin.last k := by
        intro h; have := congrArg Fin.val h; simp [i] at this; omega
      have hbi : b m i = a i := by simp [b, hi, i]
      have hbj : b m (Fin.last k) = a (Fin.last k) * P m := by simp [b]
      have hu : IsUnit (b m (Fin.last k)) := by rw [hbj]; exact (ha _).mul (hP m)
      obtain ⟨x, y, hxy⟩ := exists_binary_one_dvr hπ h2 (ha i) hu
      rw [← hbi] at hxy
      have h2' := isometricGL_diag_rot (b m) hi hxy
      have e : Function.update (Function.update (b m) i 1) (Fin.last k) (b m i * b m (Fin.last k)) =
          b (m + 1) := by
        funext r
        by_cases hr : r = Fin.last k
        · subst hr
          rw [Function.update_self, hbi, hbj]
          simp only [b, if_pos rfl, P]
          have : Finset.univ.filter (fun s : Fin (k + 1) => s.val < m + 1) =
              insert i (Finset.univ.filter (fun s : Fin (k + 1) => s.val < m)) := by
            ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, i,
              Fin.ext_iff]; omega
          rw [this, Finset.prod_insert (by simp [i])]
          ring
        · rw [Function.update_of_ne hr]
          by_cases hri : r = i
          · subst hri; rw [Function.update_self]; simp [b, hi, i]
          · rw [Function.update_of_ne hri]
            have : r.val ≠ m := fun h => hri (Fin.ext h)
            simp only [b, hr, if_false]
            congr 1
            apply propext; omega
      rw [e] at h2'
      exact h1.trans h2'
  have hk := key k le_rfl
  have e : b k = Function.update (1 : Fin (k + 1) → R) (Fin.last k) (∏ i, a i) := by
    funext r
    by_cases hr : r = Fin.last k
    · subst hr
      simp only [b, if_pos rfl, Function.update_self, P]
      have : Finset.univ.filter (fun s : Fin (k + 1) => s.val < k) = Finset.univ.erase (Fin.last k) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
        rw [Fin.ext_iff, Fin.val_last]; have := s.isLt; omega
      rw [this, mul_comm, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
    · have hlt : r.val < k := by
        have := r.isLt; have : r.val ≠ k := fun h => hr (Fin.ext h); omega
      simp [b, hr, hlt]
  rw [e] at hk
  exact hk

/-- **Classification of unimodular forms over a complete non-dyadic DVR with finite residue field** (the ring of integers
of a non-dyadic local field; O'Meara 1963, 92:1, p. 246, and 92:2, p. 247): if $\pi \nmid \det H$
and $\det H' = u^2\det H$ for a unit $u$, then $Q \cong Q'$ over $R$ (`IsometricGL`). -/
@[kb "omeara1963" "§92, 92:1, p. 246; cf. 92:2, p. 247; cassels1978 Ch. 8, Lemma 3.4 and Cor. to Thm. 3.1, pp. 115–116"]
theorem isometricGL_of_unimodular_dvr (Q Q' : QuadForm R n) (hQ : ¬ π ∣ Q.hessian.det) {u : R}
    (hu : IsUnit u) (hdet : Q'.hessian.det = u ^ 2 * Q.hessian.det) : IsometricGL Q Q' := by
  cases n with
  | zero => exact isometricGL_zero Q Q'
  | succ k =>
    have hQ' : ¬ π ∣ Q'.hessian.det := by
      rw [hdet]; intro h; exact hQ ((hu.pow 2).dvd_mul_left.mp h)
    obtain ⟨a, ha, hE, v, hv, hdv⟩ := DVR.exists_diag_of_unimodular Q _ hπ h2 hQ
    obtain ⟨a', ha', hE', v', hv', hdv'⟩ := DVR.exists_diag_of_unimodular Q' _ hπ h2 hQ'
    have haU : ∀ i, IsUnit (a i) := fun i => DVR.isUnit_of_not_dvd _ hπ _ (ha i)
    have haU' : ∀ i, IsUnit (a' i) := fun i => DVR.isUnit_of_not_dvd _ hπ _ (ha' i)
    have hvU : IsUnit v := hv
    have hvU' : IsUnit v' := hv'
    set w : Rˣ := hvU'.unit * hu.unit * hvU.unit⁻¹
    have hw : (w : R) * v = v' * u := by
      simp only [w, Units.val_mul, IsUnit.unit_spec]
      rw [mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hprod : ∏ i, a' i = (w : R) ^ 2 * ∏ i, a i := by
      have h2n : (2 : R) ^ (k + 1) ≠ 0 := pow_ne_zero _ (fun h => h2 (by rw [h]; exact dvd_zero π))
      have hv0 : v ≠ 0 := hvU.ne_zero
      apply mul_left_cancel₀ (mul_ne_zero h2n (pow_ne_zero 2 hv0))
      have e1 : (2 : R) ^ (k + 1) * v ^ 2 * ∏ i, a' i = v ^ 2 * (2 ^ (k + 1) * ∏ i, a' i) := by ring
      rw [e1, hdv', hdet]
      have e2 : (2 : R) ^ (k + 1) * v ^ 2 * ((w : R) ^ 2 * ∏ i, a i) =
          (w : R) ^ 2 * v ^ 2 * (2 ^ (k + 1) * ∏ i, a i) := by ring
      rw [e2, hdv]
      have e3 : (w : R) ^ 2 * v ^ 2 = (v' * u) ^ 2 := by rw [← hw]; ring
      rw [← mul_assoc, e3]; ring
    have e1 := isometricGL_of_isGLEquiv hE
    have e2 := isometricGL_of_isGLEquiv hE'
    have n1 := isometricGL_diag_normal_dvr hπ h2 a haU
    have n2 := isometricGL_diag_normal_dvr hπ h2 a' haU'
    have hsc := isometricGL_diag_scale (Function.update (1 : Fin (k + 1) → R) (Fin.last k) (∏ i, a i))
      (Fin.last k) w
    rw [Function.update_idem, Function.update_self, ← hprod] at hsc
    exact e1.trans (n1.trans (hsc.trans (n2.symm.trans e2.symm)))

/-- **Unimodular forms isometric over the fraction field are isometric over $R$** (complete non-dyadic DVR with finite residue field; O'Meara 1963, 92:2,
p. 247): if $\pi \nmid \det H$, $\pi \nmid \det H'$ and $Q'(x) = Q(gx)$ on $K^n$ for some $g \in \mathrm{GL}_n(K)$, then $Q \cong Q'$ over $R$.
*Proof:* $\det H' = (\det g)^2\det H$, so $(\det g)^2$ is a unit of $R$; $\det g$ is integral over $R$, hence in $R$ and a unit; apply
`isometricGL_of_unimodular_dvr`. -/
@[kb "omeara1963" "§92, 92:2, p. 247 (unimodular case)"]
theorem isometricGL_of_unimodular_of_isometricIn (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q Q' : QuadForm R n) (hQ : ¬ π ∣ Q.hessian.det) (hQ' : ¬ π ∣ Q'.hessian.det) (g : GL (Fin n) K)
    (hg : ∀ x : Fin n → K, Q'.evalIn K x = Q.evalIn K (g.val *ᵥ x)) : IsometricGL Q Q' := by
  -- the Hessians over `K`
  have hH : (Q'.map (algebraMap R K)).hessian = g.valᵀ * (Q.map (algebraMap R K)).hessian * g.val := by
    refine hessian_eq_of_eval' fun x => ?_
    rw [← Nbr.evalIn_eq_eval_map', ← Nbr.evalIn_eq_eval_map', hg]
  have hdetK : algebraMap R K Q'.hessian.det = g.val.det ^ 2 * algebraMap R K Q.hessian.det := by
    have e : ∀ P : QuadForm R n, (P.map (algebraMap R K)).hessian = P.hessian.map (algebraMap R K) := by
      intro P; ext i j; simp [QuadForm.hessian, QuadForm.map]
    have := congrArg Matrix.det hH
    have e2 : ∀ P : QuadForm R n, (P.hessian.map (algebraMap R K)).det = algebraMap R K P.hessian.det :=
      fun P => (RingHom.map_det (algebraMap R K) P.hessian).symm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e, e, e2, e2] at this
    rw [this]; ring
  have hu1 : IsUnit Q.hessian.det := DVR.dvr_isUnit_of_not_dvd hπ hQ
  have hu2 : IsUnit Q'.hessian.det := DVR.dvr_isUnit_of_not_dvd hπ hQ'
  -- `t = det g` satisfies `t² = c` with `c ∈ Rˣ`
  set c : R := Q'.hessian.det * ↑hu1.unit⁻¹ with hc
  have hcU : IsUnit c := hu2.mul (Units.isUnit _)
  have ht : g.val.det ^ 2 = algebraMap R K c := by
    have h0 : algebraMap R K Q.hessian.det ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]; exact hu1.ne_zero
    rw [hc, map_mul, hdetK, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  -- integrality of `det g`
  have hint : IsIntegral R g.val.det :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, by monicity!, by
      simp [Polynomial.eval₂_sub, ht]⟩
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hs2 : s ^ 2 = c := IsFractionRing.injective R K (by rw [map_pow, hs, ht])
  have hsU : IsUnit s := by
    have : IsUnit (s ^ 2) := hs2 ▸ hcU
    exact isUnit_of_mul_isUnit_left (by rwa [sq] at this)
  refine isometricGL_of_unimodular_dvr hπ h2 Q Q' hQ hsU ?_
  rw [hs2, hc, mul_assoc, IsUnit.val_inv_mul, mul_one]

end QuadFormsKB.Lattices.Nbr
