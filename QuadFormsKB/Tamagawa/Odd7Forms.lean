/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.OddProof
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Ternary.OddPrimes
import QuadFormsKB.Tamagawa.Measure.Weil.ThetaPoissonSO

/-!
# Paper 7 at odd primes: forms over $\mathbb Z_p \cong \mathfrak o_v$ and Gram matrices over $\mathbb Q_p$

For a place $v \nmid 2$ of $\mathbb Q$, with $p = p_v$ (`pv v`) and the ring isomorphism $e : \mathbb Z_p \cong \mathfrak o_v$
(`ConwaySloane.Mass.eInt`), this file transports $\mathrm{GL}_n(\mathfrak o_v)$-equivalence of $\mathfrak o_v$-valued
quadratic forms to $\mathbb Z_p$-equivalence (`Cassels.ZpEquiv`) of their Gram matrices $\tfrac12 H_T$ over $\mathbb Q_p$
(`gramQp`), and defines the representatives of the genera of paper 7's Lemma 2.1:

* `isometricGL_iff_zpEquiv_gram`: $T \cong T'$ over $\mathfrak o_v$ iff $\tfrac12H_T \sim_{\mathbb Z_p}\tfrac12H_{T'}$
  ($p$ odd is not needed for this equivalence, only for the integrality of the Gram matrix);
* `gramQp_diag`: the Gram matrix of the diagonal form $\sum_i e(y_i)x_i^2$ is $\operatorname{diag}(y_i)$;
* `rep c e`: the integer representing the unit square class $e = \pm1$ ($1$, or a fixed non-residue $c$);
* `tupleForm`, `tupG`: the form $\langle u_1, p^au_2, p^bu_3\rangle$ of the tuple $(a,b;u_1,u_2,u_3)$ of Lemma 2.1
  and its local genus.

Indices are 0-based: the paper's $u_1,u_2,u_3$ are `e₁ e₂ e₃` (as in `Hanke2011Ternary.IsJordanTuple`), the entries of
`tupleVec` are `0, 1, 2`.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section Generic

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (e : ℤ_[p] ≃+* R) {n : ℕ}

include e

/-- The ring homomorphism `R → ℚ_[p]` (through $R \cong \mathbb Z_p \subset \mathbb Q_p$). -/
def toQp : R →+* ℚ_[p] := PadicInt.Coe.ringHom.comp e.symm.toRingHom

theorem toQp_injective : Function.Injective (toQp e) := by
  intro a b h
  have : (e.symm a : ℚ_[p]) = e.symm b := h
  exact e.symm.injective (Subtype.ext this)

theorem toQp_e (x : ℤ_[p]) : toQp e (e x) = (x : ℚ_[p]) := by
  show PadicInt.Coe.ringHom (e.symm (e x)) = _
  rw [RingEquiv.symm_apply_apply]; rfl

/-- The Hessian of a form over `R`, as a matrix over `ℚ_[p]`. -/
def hessQp (T : QuadForm R n) : Matrix (Fin n) (Fin n) ℚ_[p] := T.hessian.map (toQp e)

/-- The Gram matrix $\tfrac12H_T$ of a form over `R`, as a matrix over `ℚ_[p]`. -/
def gramQp (T : QuadForm R n) : Matrix (Fin n) (Fin n) ℚ_[p] := (1 / 2 : ℚ_[p]) • hessQp e T

theorem two_mul_cancel {a b : R} (h : 2 * a = 2 * b) : a = b := by
  have h' := congrArg e.symm h
  rw [map_mul, map_mul, map_ofNat] at h'
  have h0 : (2 : ℤ_[p]) ≠ 0 := two_ne_zero
  exact e.symm.injective (mul_left_cancel₀ h0 h')

theorem hessian_inj {T T' : QuadForm R n} (h : T.hessian = T'.hessian) : T = T' := by
  have hc : ∀ i j, T.coeff i j = T'.coeff i j := by
    intro i j
    have hij := congrFun (congrFun h i) j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at hij
    rcases lt_trichotomy i j with hl | rfl | hl
    · have h1 : T.coeff j i = 0 := T.upper (show id i < id j from hl)
      have h2 : T'.coeff j i = 0 := T'.upper (show id i < id j from hl)
      simpa [h1, h2] using hij
    · have : 2 * T.coeff i i = 2 * T'.coeff i i := by rw [two_mul, two_mul]; exact hij
      exact two_mul_cancel e this
    · have h1 : T.coeff i j = 0 := T.upper (show id j < id i from hl)
      have h2 : T'.coeff i j = 0 := T'.upper (show id j < id i from hl)
      rw [h1, h2]
  exact QuadForm.ext (Matrix.ext hc)

/-- units transport -/
def glMap (g : GL (Fin n) R) : GL (Fin n) ℤ_[p] :=
  Units.map (RingHom.mapMatrix e.symm.toRingHom).toMonoidHom g

theorem glMap_val (g : GL (Fin n) R) : (glMap e g).val = g.val.map e.symm := rfl

/-- units transport (inverse direction) -/
def glMap' (g : GL (Fin n) ℤ_[p]) : GL (Fin n) R :=
  Units.map (RingHom.mapMatrix e.toRingHom).toMonoidHom g

theorem glMap'_val (g : GL (Fin n) ℤ_[p]) : (glMap' e g).val = g.val.map e := rfl

theorem hessQp_compMat (T : QuadForm R n) (g : Matrix (Fin n) (Fin n) R) :
    hessQp e (T.compMat g) = (g.map (toQp e))ᵀ * hessQp e T * g.map (toQp e) := by
  unfold hessQp
  rw [QuadForm.hessian_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem isometricGL_iff_zpEquiv (T T' : QuadForm R n) :
    IsometricGL T T' ↔ ZpEquiv (hessQp e T) (hessQp e T') := by
  rw [isometricGL_iff_compMat]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨glMap e g, ?_⟩
    rw [hessQp_compMat, glMap_val]
    have : (g.val.map e.symm).map (PadicInt.Coe.ringHom) = g.val.map (toQp e) := by
      rw [Matrix.map_map]; rfl
    rw [this]
  · rintro ⟨T0, hT0⟩
    refine ⟨glMap' e T0, ?_⟩
    have hmap : (T0.val.map e).map (toQp e) = T0.val.map (PadicInt.Coe.ringHom) := by
      rw [Matrix.map_map]; congr 1; ext x; exact toQp_e e x
    apply hessian_inj e
    apply Matrix.ext; intro i j
    apply toQp_injective e
    have := congrFun (congrFun (hessQp_compMat e T (glMap' e T0).val) i) j
    unfold hessQp at this hT0
    show (T'.hessian.map (toQp e)) i j = ((T.compMat (glMap' e T0).val).hessian.map (toQp e)) i j
    rw [this, glMap'_val, hmap]
    exact (congrFun (congrFun hT0 i) j).symm

theorem hessQp_symm (T : QuadForm R n) : (hessQp e T)ᵀ = hessQp e T := by
  unfold hessQp
  rw [← Matrix.transpose_map]
  congr 1
  simp [QuadForm.hessian, add_comm]

theorem hessQp_det (T : QuadForm R n) (h : T.hessian.det ≠ 0) : (hessQp e T).det ≠ 0 := by
  unfold hessQp
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h' => h (toQp_injective e (by simpa using h'))

theorem hessQp_norm (T : QuadForm R n) (i j : Fin n) : ‖hessQp e T i j‖ ≤ 1 :=
  (e.symm (T.hessian i j)).2

omit [CommRing R] e in
/-- Scaling both matrices by a nonzero constant does not change $\mathbb Z_p$-equivalence. -/
theorem zpEquiv_smul_iff {c : ℚ_[p]} (hc : c ≠ 0) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} :
    ZpEquiv (c • F) (c • G) ↔ ZpEquiv F G := by
  unfold ZpEquiv
  refine exists_congr fun T0 => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hc).eq_iff

/-- **$\mathrm{GL}_n(\mathfrak o)$-equivalence of forms is $\mathbb Z_p$-equivalence of their Gram matrices** $\tfrac12H_T$
over $\mathbb Q_p$. -/
theorem isometricGL_iff_zpEquiv_gram (T T' : QuadForm R n) :
    IsometricGL T T' ↔ ZpEquiv (gramQp e T) (gramQp e T') := by
  rw [isometricGL_iff_zpEquiv e, gramQp, gramQp, zpEquiv_smul_iff (p := p) (by norm_num : (1 / 2 : ℚ_[p]) ≠ 0)]

omit [Fact p.Prime] [CommRing R] e in
/-- The Hessian of a diagonal form: $\operatorname{diag}(2a_i)$. -/
theorem hessian_diag_gen {S : Type*} [CommRing S] {m : ℕ} (a : Fin m → S) :
    (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  show Matrix.diagonal a + (Matrix.diagonal a)ᵀ = _
  rw [Matrix.diagonal_transpose, Matrix.diagonal_add]
  congr 1
  funext i
  ring

/-- **The Gram matrix of the diagonal form $\sum_i e(y_i)x_i^2$ is $\operatorname{diag}(y_i)$.** -/
theorem gramQp_diag (y : Fin n → ℤ_[p]) :
    gramQp e (QuadForm.diag (fun i => e (y i))) = Matrix.diagonal (fun i => ((y i : ℤ_[p]) : ℚ_[p])) := by
  unfold gramQp hessQp
  rw [hessian_diag_gen]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, smul_eq_mul, map_mul, map_ofNat,
      toQp_e]
    field_simp
  · simp [Matrix.diagonal_apply_ne _ hij]

end Generic

theorem norm_two_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h := norm_intCast_eq_one (p := p) (z := 2) (by
    intro hd
    have : p ∣ 2 := by exact_mod_cast hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this))
  simpa using h

theorem norm_half_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ‖(1 / 2 : ℚ_[p])‖ = 1 := by
  rw [one_div, norm_inv, norm_two_p hp2, inv_one]

/-- The Gram matrix of a form over $\mathbb Z_p$ (odd $p$) is integral. -/
theorem gramQp_norm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R : Type*} [CommRing R] (e : ℤ_[p] ≃+* R) {n : ℕ}
    (T : QuadForm R n) (i j : Fin n) : ‖gramQp e T i j‖ ≤ 1 := by
  unfold gramQp
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_half_p hp2, one_mul]
  exact hessQp_norm e T i j

theorem gramQp_symm {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (e : ℤ_[p] ≃+* R) {n : ℕ}
    (T : QuadForm R n) : (gramQp e T)ᵀ = gramQp e T := by
  unfold gramQp
  rw [Matrix.transpose_smul, hessQp_symm]

theorem gramQp_det {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (e : ℤ_[p] ≃+* R) {n : ℕ}
    (T : QuadForm R n) (h : T.hessian.det ≠ 0) : (gramQp e T).det ≠ 0 := by
  unfold gramQp
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hessQp_det e T h)

/-! ### At the place $v$ -/

section AtV

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- $v \nmid 2$ means $p_v \ne 2$. -/
theorem pv_ne_two (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) : pv v ≠ 2 := by
  intro h
  apply hv
  have h2 : ((2 : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    refine (RatHeadline3.intCast_mem_iff v 2).mpr ?_
    have h' : Rat.HeightOneSpectrum.natGenerator v = 2 := h
    rw [h']
    norm_num
  exact_mod_cast h2

/-- The diagonal form $\sum_i e(y_i)x_i^2$ over $\mathfrak o_v$ with entries $y_i \in \mathbb Z_p$. -/
def dform (y : Fin 3 → ℤ_[pv v]) : QuadForm 𝔬 3 := QuadForm.diag (fun i => eInt v (y i))

theorem map_diag_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a : Fin n → R) :
    (QuadForm.diag a).map f = QuadForm.diag (fun i => f (a i)) :=
  QuadForm.ext (Matrix.diagonal_map (map_zero f))

/-- **The integer representing the unit square class $e = \pm1$**: $1$ if $e = 1$, and the fixed non-residue $c$ if
$e = -1$. -/
def rep (c : ℤ) (e : ℤˣ) : ℤ := if e = 1 then 1 else c

/-- The diagonal entries of the representative form of the tuple $(a, b; u_1, u_2, u_3)$ of Lemma 2.1:
$(u_1, p^au_2, p^bu_3)$ (0-based: entries $0, 1, 2$), each $u_i$ replaced by `rep c u_i`. -/
def tupleVec (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : Fin 3 → ℤ :=
  ![rep c e₁, (p : ℤ) ^ a * rep c e₂, (p : ℤ) ^ b * rep c e₃]

/-- **The representative form of the tuple $(a, b; u_1, u_2, u_3)$** (Lemma 2.1, p. 4–5):
$u_1x_0^2 + p^au_2x_1^2 + p^bu_3x_2^2$ over $\mathbb Z$, with the unit square classes $u_i = \pm1$ (Legendre symbols
`e₁ e₂ e₃`) represented by $1$ or the non-residue $c$. -/
def tupleForm (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : QuadForm ℤ 3 := QuadForm.diag (tupleVec p c a b e₁ e₂ e₃)

/-- **The local genus of the tuple** $(a, b; u_1, u_2, u_3)$ at $v$ (Lemma 2.1): the class of `tupleForm` over
$\mathfrak o_v$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (genera as tuples)"]
def tupG (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : LocGenus v 3 :=
  LocGenus.mk ((tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬))

theorem tupleForm_map (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬) =
      dform v (fun i => ((tupleVec (pv v) c a b e₁ e₂ e₃ i : ℤ) : ℤ_[pv v])) := by
  unfold tupleForm dform
  rw [map_diag_eq]
  congr 1
  funext i
  rw [map_intCast]
  exact eq_intCast (algebraMap ℤ 𝔬) _

theorem tupG_eq (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    tupG v c a b e₁ e₂ e₃ =
      LocGenus.mk (dform v (fun i => ((tupleVec (pv v) c a b e₁ e₂ e₃ i : ℤ) : ℤ_[pv v]))) := by
  unfold tupG
  rw [tupleForm_map]

end AtV

end

end QuadFormsKB.Odd7
