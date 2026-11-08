/-
# Hanke, Arizona Winter School 2009 notes, Ch. 3: quaternion algebras and the Hilbert symbol

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), Chapter 3.

This file proves the statements of Ch. 3 that had no library counterpart in the notes' form:

- Thm 3.1.12 (3), (4), (5) (nondegeneracy, $(a,1-a)_v = 1$, even valuations);
  (2) (bilinearity) is `HilbertLocal.hilbertSymbol_padic_mul_left` / `hilbertSymbol_real_mul_left`.
- Thm 3.1.10, 3.1.11: quaternion algebras over $\mathbb{Q}_p$ and $\mathbb{R}$ are split or division, and
  there is a unique division algebra.
- Lemma 3.3.1 (a): two reflections move $x$ to $y$ when $Q(x) = Q(y) \ne 0$.

Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Literature.Cassels.Ch4.Invariants
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.OMeara.Sec57Iso
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Lattices.CartanDieudonne

open Matrix Quaternion QuadFormsKB.Quat

namespace QuadFormsKB.AWS.Notes

/-! ### §3.1 The Hilbert symbol -/

/-- **Notes, Thm 3.1.12 (4), p. 45:** $(a, 1-a)_K = 1$. Over any field $K$ (so in particular for $K = \mathbb{Q}_p$
and $K = \mathbb{R}$, the notes' $v$), for every $a \in K$: $z^2 = a x^2 + (1-a) y^2$ has the solution
$(x, y, z) = (1, 1, 1)$. (The notes assume $a \ne 0, 1$ so that the symbol is defined; the identity needs no
hypothesis on $a$.) -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.12(4), p. 45"]
theorem hilbertSymbol_one_sub (K : Type*) [Field K] (a : K) : hilbertSymbol K a (1 - a) = 1 := by
  unfold hilbertSymbol
  exact if_pos ⟨1, 1, 1, by simp, by ring⟩

/-- **Notes, Thm 3.1.12 (3), p. 45 (nondegeneracy), $v = p$:** if $a \in \mathbb{Q}_p^\times$ satisfies
$(a, b)_p = 1$ for all $b \in \mathbb{Q}_p^\times$, then $a$ is a square in $\mathbb{Q}_p$. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.12(3), p. 45"]
theorem isSquare_of_hilbertSymbol_padic (p : ℕ) [Fact p.Prime] (a : ℚ_[p]) (ha : a ≠ 0)
    (h : ∀ b : ℚ_[p], b ≠ 0 → hilbertSymbol ℚ_[p] a b = 1) : IsSquare a := by
  by_contra hns
  obtain ⟨x, hx, hx1⟩ := (PadicClass.localHilbertField_padic p).exists_neg_one a ha hns
  have := h x hx
  rw [hx1] at this
  norm_num at this

/-- **Notes, Thm 3.1.12 (3), p. 45 (nondegeneracy), $v = \infty$:** if $a \in \mathbb{R}^\times$ satisfies
$(a, b)_\infty = 1$ for all $b \in \mathbb{R}^\times$, then $a$ is a square in $\mathbb{R}$ (i.e. $a > 0$). -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.12(3), p. 45"]
theorem isSquare_of_hilbertSymbol_real (a : ℝ) (ha : a ≠ 0)
    (h : ∀ b : ℝ, b ≠ 0 → hilbertSymbol ℝ a b = 1) : IsSquare a := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have := (hilbertSymbol_real a (-1) ha (by norm_num)).2 ⟨hneg, by norm_num⟩
    have h1 := h (-1) (by norm_num)
    rw [this] at h1
    norm_num at h1
  · exact ⟨Real.sqrt a, (Real.mul_self_sqrt hpos.le).symm⟩

/-- A nonzero $p$-adic number of even valuation is a unit times a nonzero square. -/
theorem exists_unit_mul_sq_of_even (p : ℕ) [hp : Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0)
    (hev : Even (Padic.valuation x)) : ∃ (u : ℤ_[p]ˣ) (c : ℚ_[p]), c ≠ 0 ∧ x = ((u : ℤ_[p]) : ℚ_[p]) * c ^ 2 := by
  obtain ⟨k, hk⟩ := hev
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set c : ℚ_[p] := (p : ℚ_[p]) ^ k with hc
  have hc0 : c ≠ 0 := zpow_ne_zero _ hp0
  have hnorm : ‖x / c ^ 2‖ = 1 := by
    have hp1 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [norm_div, norm_pow, hc, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, hk]
    rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_sub₀ hp1]
    rw [show -(k + k) - -k * ((2 : ℕ) : ℤ) = 0 by push_cast; ring, zpow_zero]
  have hle : ‖x / c ^ 2‖ ≤ 1 := hnorm.le
  refine ⟨(PadicInt.isUnit_iff.2 (show ‖(⟨x / c ^ 2, hle⟩ : ℤ_[p])‖ = 1 from hnorm)).unit, c, hc0, ?_⟩
  show x = x / c ^ 2 * c ^ 2
  field_simp

/-- **Notes, Thm 3.1.12 (5), p. 45:** for $p$ odd and $a, b \in \mathbb{Q}_p^\times$ with $v_p(a)$ and
$v_p(b)$ both even, $(a, b)_p = 1$. (`Padic.valuation` is the $p$-adic valuation $v_p : \mathbb{Q}_p^\times \to \mathbb{Z}$.) -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.12(5), p. 45"]
theorem hilbertSymbol_padic_even_valuation (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a b : ℚ_[p])
    (ha : a ≠ 0) (hb : b ≠ 0) (hva : Even (Padic.valuation a)) (hvb : Even (Padic.valuation b)) :
    hilbertSymbol ℚ_[p] a b = 1 := by
  obtain ⟨u, c, hc, rfl⟩ := exists_unit_mul_sq_of_even p a ha hva
  obtain ⟨v, d, hd, rfl⟩ := exists_unit_mul_sq_of_even p b hb hvb
  rw [QuadFormsKB.HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm,
    QuadFormsKB.HM3.hilbertSymbol_mul_sq_left _ _ _ _ hd, hilbertSymbol_comm]
  exact HilbertLocal.hilbertSymbol_units hp2 u v

/-! ### §3.1 Quaternion algebras over local fields -/

/-- **Notes, Thm 3.1.10 / 3.1.11, p. 44 (split or division):** for $a, b \in K^\times$ over a field $K$ of
characteristic $\ne 2$, the quaternion algebra $\mathbb{H}[K,a,b]$ is either isomorphic (as a $K$-algebra) to
$M_2(K)$ or a division algebra (every nonzero element is a unit). In particular this holds for
$K = \mathbb{Q}_p$ and $K = \mathbb{R}$; the notes omit the hypothesis $a, b \ne 0$. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.10, 3.1.11, p. 44"]
theorem quat_split_or_division (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Nonempty (ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ∨ ∀ x : ℍ[K,a,b], x ≠ 0 → IsUnit x := by
  by_cases h : hilbertSymbol K a b = 1
  · exact Or.inl ((nonempty_algEquiv_matrix_iff h2 ha hb).2 h)
  · refine Or.inr ((hilbertSymbol_eq_neg_one_iff_division h2 ha hb).1 ?_)
    unfold hilbertSymbol at h ⊢
    split_ifs at h ⊢ with hh
    · exact absurd rfl h
    · rfl

/-- `toQuadraticFormIn` over the base field itself is `toQuadraticForm`. -/
theorem toQuadraticFormIn_self {F : Type*} [Field F] {n : ℕ} (Q : QuadForm F n) :
    Q.toQuadraticFormIn F = Q.toQuadraticForm := by
  ext x
  rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticForm_apply]

/-- **Notes, Thm 3.1.10, p. 44, $v = p$:** any two quaternion division algebras $\mathbb{H}[\mathbb{Q}_p,a,b]$ and
$\mathbb{H}[\mathbb{Q}_p,c,d]$ ($a, b, c, d \ne 0$, every nonzero element a unit in both) are isomorphic as
$\mathbb{Q}_p$-algebras. (Proof: both norm forms $\langle 1,-a,-b,ab\rangle$, $\langle 1,-c,-d,cd\rangle$ are
anisotropic quaternary forms, hence isometric by Cassels Ch. 4, and quaternion algebras are isomorphic iff
their norm forms are, O'Meara 57:8.) -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.10, p. 44"]
theorem quat_division_padic_iso (p : ℕ) [Fact p.Prime] (a b c d : ℚ_[p]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hab : ∀ x : ℍ[ℚ_[p],a,b], x ≠ 0 → IsUnit x)
    (hcd : ∀ x : ℍ[ℚ_[p],c,d], x ≠ 0 → IsUnit x) :
    Nonempty (ℍ[ℚ_[p],a,b] ≃ₐ[ℚ_[p]] ℍ[ℚ_[p],c,d]) := by
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have : Invertible (2 : ℚ_[p]) := invertibleOfNonzero h2
  have h1 := (hilbertSymbol_eq_neg_one_iff_division h2 ha hb).2 hab
  have h1' := (hilbertSymbol_eq_neg_one_iff_division h2 hc hd).2 hcd
  have han := Cassels.anisotropic_norm_form p ha hb h1
  have han' := Cassels.anisotropic_norm_form p hc hd h1'
  have hne : ∀ x y : ℚ_[p], x ≠ 0 → y ≠ 0 → ∀ i : Fin 4, (![1, -x, -y, x * y] : Fin 4 → ℚ_[p]) i ≠ 0 := by
    intro x y hx hy i
    fin_cases i <;> simp [hx, hy]
  have hiso := Cassels.isometric_of_anisotropic_four p (hne a b ha hb) (hne c d hc hd) han han'
  have hiso' := (QuadForm.isometricIn_iff_equivalent (K := ℚ_[p])
    (QuadForm.diag ![1, -a, -b, a * b]) (QuadForm.diag ![1, -c, -d, c * d])).1 hiso
  rw [toQuadraticFormIn_self, toQuadraticFormIn_self] at hiso'
  have e1 := OMeara.QuatIso57.nrdQuadraticForm_equivalent_diag a b
  have e2 := OMeara.QuatIso57.nrdQuadraticForm_equivalent_diag c d
  have hE : (OMeara.Quaternions57.nrdQuadraticForm a b).Equivalent
      (OMeara.Quaternions57.nrdQuadraticForm c d) :=
    (e1.trans hiso'.symm).trans e2.symm
  exact ((OMeara.QuatIso57.tfae_iso (γ := c) (δ := d) ha hb).out 2 1).1 hE

/-- **Notes, Thm 3.1.11, p. 44, $v = \infty$ (the Hamilton quaternions):** for $a, b \in \mathbb{R}^\times$,
$\mathbb{H}[\mathbb{R},a,b]$ is a division algebra iff $a < 0$ and $b < 0$, and then
$\mathbb{H}[\mathbb{R},a,b] \cong \mathbb{H}[\mathbb{R},-1,-1]$ as $\mathbb{R}$-algebras (otherwise it is
$\cong M_2(\mathbb{R})$, `quat_split_or_division`). -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.11, p. 44"]
theorem quat_division_real_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x : ℍ[ℝ,a,b], x ≠ 0 → IsUnit x) ↔ a < 0 ∧ b < 0 := by
  rw [← hilbertSymbol_real a b ha hb]
  exact (hilbertSymbol_eq_neg_one_iff_division two_ne_zero ha hb).symm

/-- **Notes, Thm 3.1.11, p. 44, $v = \infty$:** if $a, b < 0$ then
$\mathbb{H}[\mathbb{R},a,b] \cong \mathbb{H}[\mathbb{R},-1,-1]$ as $\mathbb{R}$-algebras. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.11, p. 44"]
theorem quat_division_real_iso (a b : ℝ) (ha : a < 0) (hb : b < 0) :
    Nonempty (ℍ[ℝ,a,b] ≃ₐ[ℝ] ℍ[ℝ,-1,-1]) := by
  have ha' : (-1 : ℝ) * Real.sqrt (-a) ^ 2 = a := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hb' : (-1 : ℝ) * Real.sqrt (-b) ^ 2 = b := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have := OMeara.QuatIso57.algEquiv_scale (F := ℝ) (α := -1) (β := -1) (by norm_num) (by norm_num)
    (l := Real.sqrt (-a)) (m := Real.sqrt (-b)) (Real.sqrt_pos.2 (by linarith)).ne'
    (Real.sqrt_pos.2 (by linarith)).ne'
  rwa [ha', hb'] at this

/-- **Notes, Thm 3.1.10, p. 44, $v = \infty$:** any two quaternion division algebras $\mathbb{H}[\mathbb{R},a,b]$,
$\mathbb{H}[\mathbb{R},c,d]$ ($a, b, c, d \ne 0$) are isomorphic as $\mathbb{R}$-algebras. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.10, p. 44 (ℝ)"]
theorem quat_division_real_unique (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : ∀ x : ℍ[ℝ,a,b], x ≠ 0 → IsUnit x) (hcd : ∀ x : ℍ[ℝ,c,d], x ≠ 0 → IsUnit x) :
    Nonempty (ℍ[ℝ,a,b] ≃ₐ[ℝ] ℍ[ℝ,c,d]) := by
  obtain ⟨ha', hb'⟩ := (quat_division_real_iff a b ha hb).1 hab
  obtain ⟨hc', hd'⟩ := (quat_division_real_iff c d hc hd).1 hcd
  obtain ⟨e₁⟩ := quat_division_real_iso a b ha' hb'
  obtain ⟨e₂⟩ := quat_division_real_iso c d hc' hd'
  exact ⟨e₁.trans e₂.symm⟩

/-! ### §3.3 Reflections -/

section Reflections

open QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)
  (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- **Notes, Lemma 3.3.1 (a), p. 48:** if $Q(x) = Q(y) \ne 0$, then some product of at most two reflections
$\tau_{v}$ in vectors $v$ with $Q(v) \ne 0$ maps $x$ to $y$. Here $Q$ is a quadratic form over the number field $F$
(the library's reflection API), evaluated over any characteristic-$0$ extension field $K \supseteq F$, and the
product acts on $K^n$ by matrix multiplication. (The proof does not use non-degeneracy of $Q$, only
$Q(x) \ne 0$.) -/
@[kb "hanke2011aws" "§3.3, Lemma 3.3.1(a), p. 48"]
theorem exists_symmProd_le_two (x y : Fin n → K) (hxy : Q.evalIn K x = Q.evalIn K y)
    (hx : Q.evalIn K x ≠ 0) :
    ∃ xs : List (Fin n → K), xs.length ≤ 2 ∧ (∀ v ∈ xs, Q.evalIn K v ≠ 0) ∧
      ((symmProd Q K xs : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = y := by
  have hy : Q.evalIn K y ≠ 0 := hxy ▸ hx
  by_cases h : Q.evalIn K (y - x) ≠ 0
  · refine ⟨[y - x], by simp, by simpa using h, ?_⟩
    have := symm_sub_apply Q K hxy.symm h
    simpa [symmProd] using this
  · push Not at h
    have hsum := evalIn_sub_add_evalIn_add Q K hxy.symm
    have h' : Q.evalIn K (y + x) ≠ 0 := by
      intro h0
      rw [h, h0, add_zero] at hsum
      have h4 : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero two_ne_zero two_ne_zero
      exact (mul_ne_zero h4 hy) hsum.symm
    refine ⟨[y, y + x], by simp, ?_, ?_⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hy
      · exact h'
    · rw [symmProd_mulVec_cons, symmProd_mulVec_cons]
      have e1 : ((symmProd Q K [] : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = x := by
        simp [symmProd]
      have hb : qbil Q K y (-y) = -(2 * Q.evalIn K y) := by
        rw [qbil_comm, qbil_neg_left, qbil_self]
      rw [e1, symm_add_apply Q K hxy.symm h', symm_mulVec_bil Q K hy, hb]
      have : (-(2 * Q.evalIn K y) / Q.evalIn K y) = -2 := by field_simp
      rw [this]
      module

end Reflections

/-! ### §3.1 Central simple algebras: base change and dimension -/

section CSA

open TensorProduct

section Simple

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {A : Type*} [Ring A] [Algebra F A] {ι : Type*} [DecidableEq ι]

/-- The coefficient isomorphism $L \otimes_F A \cong (\iota \to_0 A)$, $z = \sum_i b_i \otimes c_i(z)$, for a basis
$(b_i)$ of $L$ over $F$. -/
private noncomputable def cE (b : Module.Basis ι F L) : L ⊗[F] A ≃ₗ[F] (ι →₀ A) :=
  TensorProduct.equivFinsuppOfBasisLeft b

private theorem cE_tmul_apply (b : Module.Basis ι F L) (l : L) (a : A) (i : ι) :
    cE b (l ⊗ₜ a) i = b.repr l i • a :=
  TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b l a i

private theorem cE_one_tmul_mul (b : Module.Basis ι F L) (x : A) (z : L ⊗[F] A) (i : ι) :
    cE b (((1 : L) ⊗ₜ x) * z) i = x * cE b z i := by
  induction z using TensorProduct.inductionOn with
  | tmul l a => simp [Algebra.TensorProduct.tmul_mul_tmul, cE_tmul_apply]
  | add y z hy hz => simp [mul_add, hy, hz]

private theorem cE_mul_one_tmul (b : Module.Basis ι F L) (x : A) (z : L ⊗[F] A) (i : ι) :
    cE b (z * ((1 : L) ⊗ₜ x)) i = cE b z i * x := by
  induction z using TensorProduct.inductionOn with
  | tmul l a => simp [Algebra.TensorProduct.tmul_mul_tmul, cE_tmul_apply]
  | add y z hy hz => simp [add_mul, hy, hz]

/-- **Base change of a simple central algebra to any extension field is simple** (the minimal-length argument of
O'Meara 52:1, with the basis taken on the field side so that no finiteness of the extension is needed). -/
theorem isSimpleRing_baseChange [IsSimpleRing A] [Algebra.IsCentral F A] : IsSimpleRing (L ⊗[F] A) := by
  classical
  have : Nontrivial (L ⊗[F] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left F L A
      (FaithfulSMul.algebraMap_injective F A)
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  let bL := Module.Basis.ofVectorSpace F L
  have core : ∀ n : ℕ, ∀ z ∈ I, z ≠ 0 → (cE bL z).support.card = n →
      ∃ c : L, c ≠ 0 ∧ ((c ⊗ₜ (1 : A) : L ⊗[F] A)) ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z hz hz0 hn
    obtain ⟨i0, hi0⟩ : ∃ i0, cE bL z i0 ≠ 0 := by
      by_contra h
      push Not at h
      apply hz0
      apply (cE bL).injective
      ext i
      simp [h]
    let J : TwoSidedIdeal A := TwoSidedIdeal.mk'
      {w | ∃ z' ∈ I, (∀ i, cE bL z i = 0 → cE bL z' i = 0) ∧ cE bL z' i0 = w}
      ⟨0, I.zero_mem, fun _ _ => by simp, by simp⟩
      (fun {_ _} h h' => by
        obtain ⟨z1, h1, s1, rfl⟩ := h
        obtain ⟨z2, h2, s2, rfl⟩ := h'
        exact ⟨z1 + z2, I.add_mem h1 h2, fun i hi => by simp [s1 i hi, s2 i hi], by simp⟩)
      (fun {_} h => by
        obtain ⟨z1, h1, s1, rfl⟩ := h
        exact ⟨-z1, I.neg_mem h1, fun i hi => by simp [s1 i hi], by simp⟩)
      (fun {x _} h => by
        obtain ⟨z1, h1, s1, rfl⟩ := h
        exact ⟨((1 : L) ⊗ₜ x) * z1, I.mul_mem_left _ _ h1,
          fun i hi => by rw [cE_one_tmul_mul, s1 i hi, mul_zero],
          cE_one_tmul_mul bL x z1 i0⟩)
      (fun {_ x} h => by
        obtain ⟨z1, h1, s1, rfl⟩ := h
        exact ⟨z1 * ((1 : L) ⊗ₜ x), I.mul_mem_right _ _ h1,
          fun i hi => by rw [cE_mul_one_tmul, s1 i hi, zero_mul],
          cE_mul_one_tmul bL x z1 i0⟩)
    have hJ : (1 : A) ∈ J := by
      refine IsSimpleRing.one_mem_of_ne_zero_mem J hi0 ?_
      rw [TwoSidedIdeal.mem_mk']
      exact ⟨z, hz, fun i hi => hi, rfl⟩
    rw [show J = _ from rfl, TwoSidedIdeal.mem_mk'] at hJ
    obtain ⟨z', hz'I, hsupp, hz'1⟩ := hJ
    by_cases hall : ∀ a : A, (((1 : L) ⊗ₜ a : L ⊗[F] A) * z' - z' * ((1 : L) ⊗ₜ a)) = 0
    · -- all coefficients are central, so `z' = c ⊗ 1`
      have hcen : ∀ i, ∃ f : F, algebraMap F A f = cE bL z' i := by
        intro i
        have hmem : cE bL z' i ∈ Subalgebra.center F A := by
          rw [Subalgebra.mem_center_iff]
          intro a
          have := congrArg (fun w => cE bL w i) (sub_eq_zero.mp (hall a))
          simp only [cE_one_tmul_mul, cE_mul_one_tmul] at this
          exact this
        exact Algebra.mem_bot.mp (Algebra.IsCentral.out hmem)
      choose f hf using hcen
      have hz'eq : z' = (∑ i ∈ (cE bL z').support, f i • bL i) ⊗ₜ (1 : A) := by
        conv_lhs => rw [← (cE bL).symm_apply_apply z']
        unfold cE
        rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hf i
        unfold cE at this
        rw [← this, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      refine ⟨∑ i ∈ (cE bL z').support, f i • bL i, ?_, hz'eq ▸ hz'I⟩
      intro h0
      rw [h0, TensorProduct.zero_tmul] at hz'eq
      rw [hz'eq] at hz'1
      simp at hz'1
    · push Not at hall
      obtain ⟨a, ha⟩ := hall
      set w : L ⊗[F] A := ((1 : L) ⊗ₜ a : L ⊗[F] A) * z' - z' * ((1 : L) ⊗ₜ a) with hw
      have hwI : w ∈ I := I.sub_mem (I.mul_mem_left _ _ hz'I) (I.mul_mem_right _ _ hz'I)
      have hcoef : ∀ i, cE bL w i = a * cE bL z' i - cE bL z' i * a := by
        intro i
        rw [hw, map_sub, Finsupp.sub_apply, cE_one_tmul_mul, cE_mul_one_tmul]
      have hsw : (cE bL w).support ⊆ (cE bL z).support.erase i0 := by
        intro i hi
        rw [Finsupp.mem_support_iff] at hi
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        refine ⟨?_, fun h => hi ?_⟩
        · rintro rfl
          apply hi
          rw [hcoef, hz'1]
          simp
        · rw [hcoef, hsupp i h]
          simp
      have hi0mem : i0 ∈ (cE bL z).support := by simpa [Finsupp.mem_support_iff] using hi0
      have hlt : (cE bL w).support.card < n := by
        calc (cE bL w).support.card ≤ ((cE bL z).support.erase i0).card := Finset.card_le_card hsw
          _ < (cE bL z).support.card := Finset.card_erase_lt_of_mem hi0mem
          _ = n := hn
      exact ih _ hlt w hwI ha rfl
  obtain ⟨z, hzI, hz0 : z ≠ 0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨c, hc0, hcI⟩ := core _ z hzI hz0 rfl
  refine (TwoSidedIdeal.one_mem_iff I).mp ?_
  have := I.mul_mem_left ((c⁻¹ : L) ⊗ₜ (1 : A)) _ hcI
  simpa [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hc0, Algebra.TensorProduct.one_def]
    using this

end Simple

variable (F : Type*) [Field F] (L : Type*) [Field L] [Algebra F L]
  (A : Type*) [Ring A] [Algebra F A]

/-- The centre of $L \otimes_F A$ is $L \cdot 1$ when $A$ is central over $F$: every central element is
$\ell \otimes 1$. -/
theorem isCentral_baseChange [Algebra.IsCentral F A] : Algebra.IsCentral L (L ⊗[F] A) where
  out := by
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    have hcent : z ∈ Subalgebra.centralizer F
        ((Algebra.TensorProduct.includeRight : A →ₐ[F] L ⊗[F] A).range : Set (L ⊗[F] A)) := by
      rintro _ ⟨a, rfl⟩
      exact hz _
    rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at hcent
    obtain ⟨t, rfl⟩ := hcent
    have key : ∀ t : L ⊗[F] (Subalgebra.center F A),
        ∃ l : L, Algebra.TensorProduct.map (AlgHom.id F L) (Subalgebra.center F A).val t =
          algebraMap L (L ⊗[F] A) l := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul l c =>
        obtain ⟨f, hf⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out c.2)
        refine ⟨f • l, ?_⟩
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply]
        simp only [AlgHom.id_apply, Subalgebra.coe_val, ← hf, Algebra.algebraMap_eq_smul_one]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp
      | add x y hx hy =>
        obtain ⟨l₁, h₁⟩ := hx
        obtain ⟨l₂, h₂⟩ := hy
        exact ⟨l₁ + l₂, by rw [map_add, h₁, h₂, map_add]⟩
    obtain ⟨l, hl⟩ := key t
    exact Algebra.mem_bot.mpr ⟨l, hl.symm⟩

/-- **Notes, Thm 3.1.2, p. 41 (base change of a central simple algebra):** if $A$ is a finite-dimensional
central simple algebra over $F$ and $L/F$ is a field extension, then $L \otimes_F A$ is a central simple
$L$-algebra (central: `Algebra.IsCentral L (L ⊗[F] A)`; simple: `IsSimpleRing`) of the same dimension,
$\dim_L(L \otimes_F A) = \dim_F A$. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.2, p. 41"]
theorem baseChange_isCentralSimple [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A] :
    Algebra.IsCentral L (L ⊗[F] A) ∧ IsSimpleRing (L ⊗[F] A) ∧
      Module.finrank L (L ⊗[F] A) = Module.finrank F A := by
  exact ⟨isCentral_baseChange F L A, isSimpleRing_baseChange, Module.finrank_baseChange⟩

/-- **Notes, Cor. 3.1.4, p. 41:** the dimension of a finite-dimensional central simple algebra $A$ over $F$ is a
perfect square: $\dim_F A = n^2$ for some $n \in \mathbb{N}$. (Proof: $\overline F \otimes_F A$ is central simple
over the algebraically closed field $\overline F$ of the same dimension, hence a matrix algebra
$M_n(\overline F)$ by Wedderburn–Artin.) -/
@[kb "hanke2011aws" "§3.1, Cor. 3.1.4, p. 42"]
theorem finrank_centralSimple_isSquare [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A] :
    ∃ n : ℕ, Module.finrank F A = n ^ 2 := by
  obtain ⟨hc, hs, hd⟩ := baseChange_isCentralSimple F (AlgebraicClosure F) A
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure F)
    (AlgebraicClosure F ⊗[F] A)
  refine ⟨n, ?_⟩
  rw [← hd, e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp [sq]

end CSA

end QuadFormsKB.AWS.Notes
