/-
# Unimodular forms over $\mathbb{Z}_p$, $p$ odd: classification by the determinant

**Layer:** forms over $\mathbb{Z}_p$ (`QuadForm ℤ_[p] n`), $p$ an odd prime.

**Proves** the classification of $p$-unimodular forms (O'Meara, *Introduction to Quadratic Forms*, 92:2; Cassels,
*Rational Quadratic Forms*, Ch. 8, Lemma 3.4, p. 115, and Thm. 3.1, Corollary, p. 116, both for $p \ne 2$): if $p \nmid \det H$ and $\det H' = \det H$, then $Q$ and $Q'$
are $\mathrm{GL}_n(\mathbb{Z}_p)$-equivalent (`isometricGL_of_unimodular`). Used to show that Kneser neighbours stay in the genus
at $p$ (`Siegel/NeighborGenus.lean`).

*Proof.* Diagonalize: $Q \cong \langle a_0, \dots, a_{n-1}\rangle$ with units $a_i$ and $2^n\prod a_i = u^2\det H$
(`LocalDensity.DVR.exists_diag_of_unimodular`). For units $a, b$ there are $x, y \in \mathbb{Z}_p$ with $ax^2 + by^2 = 1$
(`exists_binary_one`: a solution mod $p$ by the binary count of Table 1, lifted by Hensel's lemma), and the rotation
$\begin{pmatrix} x & -by \\ y & ax \end{pmatrix}$ (determinant $1$) takes $\langle a, b\rangle$ to $\langle 1, ab\rangle$ (`isometricGL_diag_rot`).
So $\langle a_0, \dots, a_{n-1}\rangle \cong \langle 1, \dots, 1, \prod a_i\rangle$ (`isometricGL_diag_normal`), and the last
coefficient is determined up to unit squares by $\det H$.
-/
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.LocalDensity.DVRUnimodular

open Matrix

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

section General

variable {R : Type*} [CommRing R]

/-- **The value of a diagonal form:** $\langle a_0, \dots, a_{n-1}\rangle(\vec{z}) = \sum_i a_i z_i^2$. -/
theorem eval_diag (a : Fin n → R) (z : Fin n → R) : (QuadForm.diag a).eval z = ∑ i, a i * z i ^ 2 := by
  simp only [QuadForm.diag, QuadForm.evalIn, diagonal_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp; ring

/-- A matrix that is the identity outside the coordinates $i \ne j$, with the $2 \times 2$ block
$\begin{pmatrix} \alpha & \beta \\ \gamma & \delta \end{pmatrix}$ on $\{i, j\}$. -/
def twoBlock (i j : Fin n) (α β γ δ : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r c => (if r = c ∧ r ≠ i ∧ r ≠ j then 1 else 0) + (if r = i ∧ c = i then α else 0) +
    (if r = i ∧ c = j then β else 0) + (if r = j ∧ c = i then γ else 0) + (if r = j ∧ c = j then δ else 0)

theorem twoBlock_mulVec {i j : Fin n} (hij : i ≠ j) (α β γ δ : R) (z : Fin n → R) :
    twoBlock i j α β γ δ *ᵥ z =
      fun r => if r = i then α * z i + β * z j else if r = j then γ * z i + δ * z j else z r := by
  ext r
  simp only [twoBlock, mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, ite_and]
  by_cases hri : r = i
  · subst hri; simp [hij]
  · by_cases hrj : r = j
    · subst hrj; simp [hri, Ne.symm hij]
    · simp [hri, hrj]

theorem twoBlock_mulVec_mulVec {i j : Fin n} (hij : i ≠ j) (α β γ δ α' β' γ' δ' : R) (z : Fin n → R) :
    twoBlock i j α β γ δ *ᵥ (twoBlock i j α' β' γ' δ' *ᵥ z) =
      twoBlock i j (α * α' + β * γ') (α * β' + β * δ') (γ * α' + δ * γ') (γ * β' + δ * δ') *ᵥ z := by
  rw [twoBlock_mulVec hij, twoBlock_mulVec hij, twoBlock_mulVec hij]
  ext r
  by_cases hri : r = i
  · subst hri; simp [hij, hij.symm]; ring
  · by_cases hrj : r = j
    · subst hrj; simp [hri, Ne.symm hri]; ring
    · simp [hri, hrj]

theorem twoBlock_one {i j : Fin n} (hij : i ≠ j) (z : Fin n → R) : twoBlock i j 1 0 0 1 *ᵥ z = z := by
  rw [twoBlock_mulVec hij]
  ext r; by_cases hri : r = i
  · subst hri; simp
  · by_cases hrj : r = j
    · subst hrj; simp [hri]
    · simp [hri, hrj]

/-- If $A(B\vec{z}) = \vec{z}$ for all $\vec{z}$, then $AB = 1$. -/
theorem mul_eq_one_of_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ z, A *ᵥ (B *ᵥ z) = z) : A * B = 1 := by
  ext r c
  have := congrFun (h (Pi.single c 1)) r
  rw [mulVec_mulVec, mulVec_single_one] at this
  simpa [Matrix.col_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this

/-- **The rotation** $\langle \dots, a_i, \dots, a_j, \dots\rangle \cong \langle \dots, 1, \dots, a_ia_j, \dots\rangle$ when
$a_ix^2 + a_jy^2 = 1$ ($i \ne j$; over any commutative ring): $z_i \mapsto xz_i - a_jyz_j$, $z_j \mapsto yz_i + a_ixz_j$. -/
theorem isometricGL_diag_rot (a : Fin n → R) {i j : Fin n} (hij : i ≠ j) {x y : R}
    (h : a i * x ^ 2 + a j * y ^ 2 = 1) :
    IsometricGL (QuadForm.diag a) (QuadForm.diag (Function.update (Function.update a i 1) j (a i * a j))) := by
  set M := twoBlock i j x (-(a j * y)) y (a i * x)
  set N := twoBlock i j (a i * x) (a j * y) (-y) x
  have hMN : ∀ z, M *ᵥ (N *ᵥ z) = z := by
    intro z
    rw [twoBlock_mulVec_mulVec hij]
    convert twoBlock_one (R := R) hij z using 3 <;>
      first | linear_combination h | linear_combination -h | ring
  have hNM : ∀ z, N *ᵥ (M *ᵥ z) = z := by
    intro z
    rw [twoBlock_mulVec_mulVec hij]
    convert twoBlock_one (R := R) hij z using 3 <;>
      first | linear_combination h | linear_combination -h | ring
  refine ⟨⟨M, N, mul_eq_one_of_mulVec hMN, mul_eq_one_of_mulVec hNM⟩, fun z => ?_⟩
  simp only
  rw [eval_diag, eval_diag, twoBlock_mulVec hij, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_eq_add i j hij]
  · simp [hij, Ne.symm hij, Function.update_apply]
    linear_combination (z i ^ 2 + a i * a j * z j ^ 2) * h
  · rintro r ⟨hri, hrj⟩
    simp [hri, hrj, Function.update_apply]

/-- **Scaling the last coefficient by a unit square:** $\langle b_0, \dots, b_{n-1}\rangle \cong \langle b_0, \dots, w^2b_{n-1}\rangle$. -/
theorem isometricGL_diag_scale (b : Fin n → R) (i : Fin n) (w : Rˣ) :
    IsometricGL (QuadForm.diag b) (QuadForm.diag (Function.update b i ((w : R) ^ 2 * b i))) := by
  set D := Matrix.diagonal (Function.update (1 : Fin n → R) i (w : R))
  set D' := Matrix.diagonal (Function.update (1 : Fin n → R) i ((w⁻¹ : Rˣ) : R))
  have h1 : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext r
    by_cases hr : r = i
    · subst hr; simp
    · simp [hr]
  have h2 : D' * D = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext r
    by_cases hr : r = i
    · subst hr; simp
    · simp [hr]
  refine ⟨⟨D, D', h1, h2⟩, fun z => ?_⟩
  simp only
  have hD : D *ᵥ z = fun r => Function.update (1 : Fin n → R) i (w : R) r * z r := by
    ext r; exact mulVec_diagonal _ _ r
  rw [eval_diag, eval_diag, hD]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r = i
  · subst hr; simp; ring
  · simp [hr]

theorem isometricGL_of_isGLEquiv {Q Q' : QuadForm R n} (h : LocalDensity.DVR.IsGLEquiv Q Q') :
    IsometricGL Q Q' := by
  obtain ⟨U, hU, hQ⟩ := h
  rw [isometricGL_iff_isometricIn]
  exact ⟨U, hU, fun x => (hQ x).symm⟩

theorem isometricGL_zero (Q Q' : QuadForm R 0) : IsometricGL Q Q' :=
  ⟨1, fun x => by simp [QuadForm.evalIn]⟩

end General

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem toZMod_two_ne_zero (hp2 : p ≠ 2) : PadicInt.toZMod (2 : ℤ_[p]) ≠ 0 := by
  rw [map_ofNat]
  intro h
  have h' := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h'
  have := hp.out.two_le
  exact hp2 (by omega)

theorem isUnit_of_toZMod_ne_zero {c : ℤ_[p]} (hc : PadicInt.toZMod c ≠ 0) : IsUnit c := by
  by_contra h
  apply hc
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
  exact h

theorem toZMod_ne_zero_of_isUnit {c : ℤ_[p]} (hc : IsUnit c) : PadicInt.toZMod c ≠ 0 := by
  intro h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at h
  exact h hc

/-- **Hensel:** a $p$-adic integer whose residue is a nonzero square is a square ($p$ odd). -/
theorem exists_sq_eq_of_toZMod (hp2 : p ≠ 2) (c : ℤ_[p]) {s : ZMod p} (hs : s ≠ 0)
    (hc : PadicInt.toZMod c = s ^ 2) : ∃ z : ℤ_[p], z ^ 2 = c := by
  set a : ℤ_[p] := (s.val : ℤ_[p])
  have ha : PadicInt.toZMod a = s := by simp [a]
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C c
  have h1 : ‖F.aeval a‖ < 1 := by
    have : F.aeval a ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [RingHom.mem_ker]; simp [F, ha, hc]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have hd : F.derivative.aeval a = 2 * a := by
    simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X]
    simp [two_mul]
  have h2 : ‖F.derivative.aeval a‖ = 1 := by
    rw [← PadicInt.isUnit_iff, hd]
    apply isUnit_of_toZMod_ne_zero
    rw [map_mul, ha]
    exact mul_ne_zero (toZMod_two_ne_zero hp2) hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
  refine ⟨z, ?_⟩
  simpa [F, sub_eq_zero] using hz

/-- **Binary unit forms represent $1$** over $\mathbb{Z}_p$, $p$ odd: for units $a, b$ there are $x, y$ with $ax^2 + by^2 = 1$. -/
theorem exists_binary_one (hp2 : p ≠ 2) {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b) :
    ∃ x y : ℤ_[p], a * x ^ 2 + b * y ^ 2 = 1 := by
  set A := PadicInt.toZMod a with hAd
  set B := PadicInt.toZMod b with hBd
  have hA : A ≠ 0 := toZMod_ne_zero_of_isUnit ha
  have hB : B ≠ 0 := toZMod_ne_zero_of_isUnit hb
  have hcount := LocalDensity.binary_count_modP hp2 A B hA hB 1
  obtain ⟨s, t, hst⟩ : ∃ s t : ZMod p, A * s ^ 2 + B * t ^ 2 = 1 := by
    by_contra h
    push Not at h
    have : (∑ y : ZMod p, ∑ z : ZMod p, (if A * y ^ 2 + B * z ^ 2 = 1 then 1 else 0 : ℤ)) = 0 :=
      Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => if_neg (h y z)
    rw [this, if_neg one_ne_zero, mul_zero, add_zero] at hcount
    have hχ : quadraticChar (ZMod p) (-(A * B)) ≤ 1 := by
      rcases quadraticChar_dichotomy (F := ZMod p)
        (neg_ne_zero.mpr (mul_ne_zero hA hB)) with h | h <;> rw [h] <;> norm_num
    have := hp.out.two_le
    have : (2 : ℤ) ≤ p := by exact_mod_cast this
    linarith
  have hinv : ∀ {u : ℤ_[p]} (hu : IsUnit u), PadicInt.toZMod (↑hu.unit⁻¹ : ℤ_[p]) = (PadicInt.toZMod u)⁻¹ := by
    intro u hu
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  by_cases hs : s = 0
  · subst hs
    have hBt : B * t ^ 2 = 1 := by simpa using hst
    have ht : t ≠ 0 := by rintro rfl; simp at hBt
    obtain ⟨y, hy⟩ := exists_sq_eq_of_toZMod hp2 (↑hb.unit⁻¹ : ℤ_[p]) ht (by
      rw [hinv hb, ← hBd]; exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hBt)).symm)
    refine ⟨0, y, ?_⟩
    rw [hy]; simp
  · -- solve for x with y a lift of t
    set y : ℤ_[p] := (t.val : ℤ_[p])
    have hy : PadicInt.toZMod y = t := by simp [y]
    obtain ⟨x, hx⟩ := exists_sq_eq_of_toZMod hp2 ((1 - b * y ^ 2) * ↑ha.unit⁻¹) hs (by
      rw [map_mul, map_sub, map_one, map_mul, map_pow, hy, hinv ha, ← hAd, ← hBd,
        show 1 - B * t ^ 2 = A * s ^ 2 by linear_combination -hst]
      field_simp)
    refine ⟨x, y, ?_⟩
    rw [hx, mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]; ring

/-- **Normal form of a unit diagonal form** ($p$ odd): $\langle a_0, \dots, a_k\rangle \cong \langle 1, \dots, 1, a_0 \cdots a_k\rangle$
over $\mathbb{Z}_p$ for units $a_i$. -/
theorem isometricGL_diag_normal (hp2 : p ≠ 2) {k : ℕ} (a : Fin (k + 1) → ℤ_[p]) (ha : ∀ i, IsUnit (a i)) :
    IsometricGL (QuadForm.diag a)
      (QuadForm.diag (Function.update (1 : Fin (k + 1) → ℤ_[p]) (Fin.last k) (∏ i, a i))) := by
  classical
  let P : ℕ → ℤ_[p] := fun m => ∏ s ∈ Finset.univ.filter (fun s : Fin (k + 1) => s.val < m), a s
  let b : ℕ → Fin (k + 1) → ℤ_[p] := fun m r =>
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
      obtain ⟨x, y, hxy⟩ := exists_binary_one hp2 (ha i) hu
      rw [← hbi] at hxy
      have h2 := isometricGL_diag_rot (b m) hi hxy
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
      rw [e] at h2
      exact h1.trans h2
  have hk := key k le_rfl
  have e : b k = Function.update (1 : Fin (k + 1) → ℤ_[p]) (Fin.last k) (∏ i, a i) := by
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

theorem toZMod_natCast_self : PadicInt.toZMod (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem not_p_dvd_two (hp2 : p ≠ 2) : ¬ (p : ℤ_[p]) ∣ 2 := by
  rintro ⟨c, hc⟩
  apply toZMod_two_ne_zero (p := p) hp2
  rw [hc, map_mul, toZMod_natCast_self, zero_mul]

/-- **Classification of unimodular forms over $\mathbb{Z}_p$, $p$ odd** (O'Meara 92:1, p. 246, and 92:2, p. 247, special case $F = \mathbb Q_p$): if
$p \nmid \det H$ and $\det H' = \det H$ ($H, H'$ the Hessians), then $Q \cong Q'$ over $\mathbb{Z}_p$. -/
@[kb "omeara1963" "§92, 92:1, p. 246 (unimodular lattices over a non-dyadic local field); cf. 92:2, p. 247; cassels1978 Ch. 8, Lemma 3.4 and Cor. to Thm. 3.1, pp. 115–116"]
theorem isometricGL_of_unimodular (hp2 : p ≠ 2) (Q Q' : QuadForm ℤ_[p] n)
    (hQ : ¬ (p : ℤ_[p]) ∣ Q.hessian.det) (hdet : Q'.hessian.det = Q.hessian.det) : IsometricGL Q Q' := by
  cases n with
  | zero => exact isometricGL_zero Q Q'
  | succ k =>
    have hπ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
    have h2 := not_p_dvd_two (p := p) hp2
    have hQ' : ¬ (p : ℤ_[p]) ∣ Q'.hessian.det := hdet ▸ hQ
    obtain ⟨a, ha, hE, u, hu, hdu⟩ := LocalDensity.DVR.exists_diag_of_unimodular Q _ hπ h2 hQ
    obtain ⟨a', ha', hE', u', hu', hdu'⟩ := LocalDensity.DVR.exists_diag_of_unimodular Q' _ hπ h2 hQ'
    have haU : ∀ i, IsUnit (a i) := fun i => LocalDensity.DVR.isUnit_of_not_dvd _ hπ _ (ha i)
    have haU' : ∀ i, IsUnit (a' i) := fun i => LocalDensity.DVR.isUnit_of_not_dvd _ hπ _ (ha' i)
    set w : ℤ_[p]ˣ := hu'.unit * hu.unit⁻¹
    have hw : (w : ℤ_[p]) * u = u' := by simp [w, mul_assoc]
    have hprod : ∏ i, a' i = (w : ℤ_[p]) ^ 2 * ∏ i, a i := by
      have h2n : (2 : ℤ_[p]) ^ (k + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      have hu0 : u ≠ 0 := hu.ne_zero
      apply mul_left_cancel₀ (mul_ne_zero h2n (pow_ne_zero 2 hu0))
      have : (2 : ℤ_[p]) ^ (k + 1) * u ^ 2 * ∏ i, a' i = u ^ 2 * (2 ^ (k + 1) * ∏ i, a' i) := by ring
      rw [this, hdu', hdet, ← hw]
      have : (2 : ℤ_[p]) ^ (k + 1) * u ^ 2 * ((w : ℤ_[p]) ^ 2 * ∏ i, a i) =
          (w : ℤ_[p]) ^ 2 * u ^ 2 * (2 ^ (k + 1) * ∏ i, a i) := by ring
      rw [this, hdu]; ring
    have e1 := isometricGL_of_isGLEquiv hE
    have e2 := isometricGL_diag_normal hp2 a haU
    have e3 := isometricGL_diag_scale (Function.update (1 : Fin (k + 1) → ℤ_[p]) (Fin.last k) (∏ i, a i))
      (Fin.last k) w
    rw [Function.update_idem, Function.update_self, ← hprod] at e3
    have e4 := (isometricGL_diag_normal hp2 a' haU').symm
    have e5 := (isometricGL_of_isGLEquiv hE').symm
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end Padic

end QuadFormsKB.Siegel.Kneser
