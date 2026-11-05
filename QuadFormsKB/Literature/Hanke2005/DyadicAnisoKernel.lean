/-
# The anisotropic maximal kernel at a dyadic place: the norm filtration

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), (3.3);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), §3.2, Lemma 3.8;
W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §6.

Let $R$ be a complete discrete valuation ring with uniformizer $\pi \mid 2$, $2 \ne 0$, and let $Q$ be a quadratic form
on $R^n$ which is **anisotropic** ($Q(x) = 0 \Rightarrow x = 0$). Write $B(x,y) = x^{\mathsf T}H_Qy$ for the polar form.

* **The norm inequality** (`pow_dvd_sq_polar_of_aniso`): if $\pi^a \mid Q(x)$ and $\pi^b \mid Q(y)$ then
  $\pi^{a+b} \mid B(x,y)^2$, i.e. $2\,\mathrm{ord}\,B(x,y) \ge \mathrm{ord}\,Q(x) + \mathrm{ord}\,Q(y)$. *Proof:* otherwise
  $Q(x)Q(y) = B^2t$ with $\pi \mid t$; then $1 - 4t = w^2$ (Hensel, `isSquare_one_sub_four_mul_iff`) and
  $z = 2Q(x)\,y + B(w-1)\,x$ satisfies $Q(z) = Q(x)\,(4Q(x)Q(y) + B^2(w^2-1)) = 0$, so $z = 0$, and pairing with $x$ gives
  $2Q(x)Bw = 0$, a contradiction. This is the classical fact behind O'Meara 91:1 (the vectors of integral norm form
  a lattice) for an anisotropic space.

Consequences used for the kernel densities (`DyadicKernelDensity`): the residue zeros
$\overline W = \{\bar x : \bar Q(\bar x) = 0\}$ form a subspace of $\mathbb F^n$ contained in the radical of $\bar B$.
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelLow
import QuadFormsKB.LocalDensity.DyadicArf
import QuadFormsKB.Literature.Hanke2005.DyadicSplitBlock

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadForm

section Ineq

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring, if $\pi^c \nmid y$ and $y \ne 0$ then $y\pi \mid \pi^c$. -/
theorem mul_pi_dvd_pow_of_not_dvd {π : R} (hπ : Irreducible π) {y : R} {c : ℕ} (h : ¬ π ^ c ∣ y) :
    ∃ d, π ^ c = y * (π * d) := by
  obtain ⟨d, hd⟩ := (ValuationRing.dvd_total y (π ^ c)).resolve_right h
  have hd' : ¬ IsUnit d := fun hu => h ⟨((hu.unit⁻¹ : Rˣ) : R), by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  obtain ⟨d', hd''⟩ : π ∣ d := by
    by_contra hπd
    exact hd' (dvr_isUnit_of_not_dvd hπ hπd)
  exact ⟨d', by rw [hd, hd'']⟩

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **The norm inequality on an anisotropic lattice at a dyadic prime:** if $\pi^a \mid Q(x)$ and $\pi^b \mid Q(y)$, then
$\pi^{a+b} \mid B(x,y)^2$ ($B(x,y) = x^{\mathsf T}H_Qy$), for $Q$ anisotropic on $R^n$, $R$ complete, $\pi \mid 2 \ne 0$. -/
@[kb "omeara1963" "§91A, 91:1 (proof: |B(x,y)|² ≤ |Q(x)Q(y)| on an anisotropic space), §63A, 63:3"]
theorem pow_dvd_sq_polar_of_aniso {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {n : ℕ}
    (Q : QuadForm R n) (han : ∀ x, Q.eval x = 0 → x = 0) (x y : Fin n → R) {a b : ℕ}
    (ha : π ^ a ∣ Q.eval x) (hb : π ^ b ∣ Q.eval y) : π ^ (a + b) ∣ (x ⬝ᵥ (Q.hessian *ᵥ y)) ^ 2 := by
  by_contra h
  set A := Q.eval x with hA
  set C := Q.eval y with hC
  set Bv := x ⬝ᵥ (Q.hessian *ᵥ y) with hBv
  have hA0 : A ≠ 0 := by
    intro h0; apply h; rw [hBv, han x h0]; simp
  have hB0 : Bv ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  -- `A C = Bv² t` with `π ∣ t`
  obtain ⟨d, hd⟩ := mul_pi_dvd_pow_of_not_dvd hπ h
  obtain ⟨wa, hwa⟩ := ha
  obtain ⟨wb, hwb⟩ := hb
  set t := π * d * (wa * wb) with ht
  have hAC : A * C = Bv ^ 2 * t := by
    rw [hwa, hwb, ht]
    have : π ^ a * wa * (π ^ b * wb) = π ^ (a + b) * (wa * wb) := by rw [pow_add]; ring
    rw [this, hd]; ring
  have hπt : π ∣ t := ⟨d * (wa * wb), by rw [ht]; ring⟩
  -- `1 - 4 t` is a square
  have hres : IsLocalRing.residue R t = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]; exact hπt
  obtain ⟨w, hw⟩ := (isSquare_one_sub_four_mul_iff hπ h2 h20 t).2 ⟨0, by rw [hres]; ring⟩
  have hw2 : w ^ 2 = 1 - 4 * t := by rw [hw]; ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hw2
    have h4 : π ∣ 4 * t := dvd_mul_of_dvd_right hπt 4
    have : π ∣ 1 := by
      have e : (1 : R) = 4 * t := by linear_combination -hw2
      rw [e]; exact h4
    exact hπ.not_isUnit (isUnit_of_dvd_one this)
  -- the isotropic vector
  set z : Fin n → R := (2 * A) • y + (Bv * (w - 1)) • x with hz
  have hyx : y ⬝ᵥ (Q.hessian *ᵥ x) = Bv := by rw [hBv, Hanke2005.dot_hessian_comm]
  have hQz : Q.eval z = 0 := by
    rw [hz, eval_add_hessian, eval_smul_sq, eval_smul_sq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      hyx, smul_eq_mul, smul_eq_mul, ← hA, ← hC]
    have e : (2 * A) ^ 2 * C + (Bv * (w - 1)) ^ 2 * A + Bv * (w - 1) * (2 * A * Bv) =
        A * (4 * (A * C) + Bv ^ 2 * (w ^ 2 - 1)) := by ring
    rw [e, hAC, hw2]; ring
  have hz0 := han z hQz
  have hxz : x ⬝ᵥ (Q.hessian *ᵥ z) = 2 * A * Bv * w := by
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      dotProduct_smul, ← hBv, dotProduct_hessian_self, ← hA, smul_eq_mul, smul_eq_mul]
    ring
  rw [hz0, Matrix.mulVec_zero, dotProduct_zero] at hxz
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h20 hA0) hB0) hw0 hxz.symm

/-- **Residue zeros lie in the radical:** if $\pi \mid Q(x)$ then $\pi \mid B(x,y)$ for every $y$. -/
theorem pi_dvd_polar_of_aniso {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {n : ℕ}
    (Q : QuadForm R n) (han : ∀ x, Q.eval x = 0 → x = 0) {x : Fin n → R} (hx : π ∣ Q.eval x) (y : Fin n → R) :
    π ∣ x ⬝ᵥ (Q.hessian *ᵥ y) := by
  have := pow_dvd_sq_polar_of_aniso hπ h2 h20 Q han x y (a := 1) (b := 0) (by simpa using hx) (by simp)
  simp only [add_zero, pow_one] at this
  exact hπ.prime.dvd_of_dvd_pow this

/-- If $\pi^2 \mid Q(x)$ and $\pi \mid Q(y)$ then $\pi^2 \mid B(x,y)$. -/
theorem pi_sq_dvd_polar_of_aniso {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {n : ℕ}
    (Q : QuadForm R n) (han : ∀ x, Q.eval x = 0 → x = 0) {x y : Fin n → R} (hx : π ^ 2 ∣ Q.eval x)
    (hy : π ∣ Q.eval y) : π ^ 2 ∣ x ⬝ᵥ (Q.hessian *ᵥ y) := by
  have h3 := pow_dvd_sq_polar_of_aniso hπ h2 h20 Q han x y (a := 2) (b := 1) hx (by simpa using hy)
  by_contra hn
  obtain ⟨d, hd⟩ := mul_pi_dvd_pow_of_not_dvd hπ hn
  -- `B = π^j u` with `j ≤ 1`, so `B² ∣ π²`, contradicting `π³ ∣ B²`
  obtain ⟨c, hc⟩ := h3
  have e : π ^ 4 = π ^ 4 * (π * c * d ^ 2) := by
    linear_combination (π ^ 2 + x ⬝ᵥ (Q.hessian *ᵥ y) * (π * d)) * hd + π ^ 2 * d ^ 2 * hc
  have hu : π * c * d ^ 2 = 1 := by
    have h0 : π ^ 4 ≠ 0 := pow_ne_zero _ hπ.ne_zero
    exact (mul_left_cancel₀ h0 (e.symm.trans (mul_one _).symm))
  exact hπ.not_isUnit (isUnit_of_dvd_one ⟨c * d ^ 2, by rw [← hu]; ring⟩)

end Ineq

/-! ### Dividing a form by a scalar -/

section Divide

variable {A : Type*} [CommRing A] [IsDomain A]

theorem eval_smul_form {n : ℕ} (c : A) (S : QuadForm A n) (x : Fin n → A) : (c • S).eval x = c * S.eval x := by
  simp [QuadForm.eval, QuadForm.evalIn, Finset.mul_sum, mul_assoc]

/-- **A form all of whose values are divisible by $c\ne0$ is $c$ times a form.** -/
theorem exists_eq_smul_of_dvd_eval {c : A} (hc : c ≠ 0) {n : ℕ} (S : QuadForm A n) (h : ∀ x, c ∣ S.eval x) :
    ∃ S' : QuadForm A n, S = c • S' := by
  classical
  have hd : ∀ i j, c ∣ S.coeff i j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have e := eval_add_hessian S (Pi.single i 1) (Pi.single j 1)
      rw [Tamagawa.single_dot_hessian_single, Tamagawa.eval_single_rd, Tamagawa.eval_single_rd] at e
      have hH : S.hessian i j = S.coeff i j := by
        simp [QuadForm.hessian, S.upper hij]
      rw [hH] at e
      have := dvd_sub (dvd_sub (h (Pi.single i 1 + Pi.single j 1)) (h (Pi.single i 1))) (h (Pi.single j 1))
      rw [e, Tamagawa.eval_single_rd, Tamagawa.eval_single_rd] at this
      convert this using 1; ring
    · have := h (Pi.single i 1)
      rwa [Tamagawa.eval_single_rd] at this
    · rw [S.upper hij]; exact dvd_zero c
  choose d hd' using hd
  refine ⟨⟨Matrix.of d, fun i j hij => ?_⟩, ?_⟩
  · have h0 := S.upper hij
    have := hd' i j
    rw [h0] at this
    simp only [Matrix.of_apply]
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  · ext i j
    simp [hd' i j]

end Divide

/-! ### The residue zero space -/

section Residue

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

theorem res_eq_zero_iff' {π : R} (hπ : Irreducible π) (x : R) : res x = 0 ↔ π ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem res_surj_vec {n : ℕ} (x : Fin n → 𝔽) : ∃ x' : Fin n → R, (fun i => res (x' i)) = x := by
  choose f hf using fun i => IsLocalRing.residue_surjective (x i)
  exact ⟨f, funext hf⟩

theorem polar_map_res {n : ℕ} (Q : QuadForm R n) (x y : Fin n → R) :
    (fun i => res (x i)) ⬝ᵥ ((Q.map res).hessian *ᵥ fun i => res (y i)) = res (x ⬝ᵥ (Q.hessian *ᵥ y)) := by
  rw [hessian_map]
  simp only [dotProduct, mulVec, Matrix.map_apply, map_sum, map_mul]

theorem eval_map_res {n : ℕ} (Q : QuadForm R n) (x : Fin n → R) :
    (Q.map res).eval (fun i => res (x i)) = res (Q.eval x) := eval_map_comp' _ Q x

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {n : ℕ} (Q : QuadForm R n)
  (han : ∀ x, Q.eval x = 0 → x = 0)

include hπ h2 h20 han in
/-- A residue zero of an anisotropic form lies in the radical of the residue polar form. -/
theorem resPolar_eq_zero {x : Fin n → 𝔽} (hx : (Q.map res).eval x = 0) (y : Fin n → 𝔽) :
    x ⬝ᵥ ((Q.map res).hessian *ᵥ y) = 0 := by
  obtain ⟨x', rfl⟩ := res_surj_vec x
  obtain ⟨y', rfl⟩ := res_surj_vec y
  rw [polar_map_res, res_eq_zero_iff' hπ]
  rw [eval_map_res, res_eq_zero_iff' hπ] at hx
  exact pi_dvd_polar_of_aniso hπ h2 h20 Q han hx y'

/-- **The residue zero space** $\overline W = \{\bar x\in\mathbb F^n : \bar Q(\bar x) = 0\}$ of an anisotropic form (a subspace,
by the norm inequality). -/
def resZeroSub : Submodule 𝔽 (Fin n → 𝔽) where
  carrier := {x | (Q.map res).eval x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [eval_add_hessian, ha, hb, resPolar_eq_zero hπ h2 h20 Q han ha]
    simp
  zero_mem' := by simp [QuadForm.eval, QuadForm.evalIn]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [eval_smul_sq, hx, mul_zero]

theorem mem_resZeroSub {x : Fin n → 𝔽} : x ∈ resZeroSub hπ h2 h20 Q han ↔ (Q.map res).eval x = 0 := Iff.rfl

/-- **The residue zero count is $q^s$**, $s = \dim\overline W$. -/
theorem zeroCount_eq_pow_finrank [Finite 𝔽] :
    zeroCount (Q.map res) = q R ^ Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) := by
  rw [q, ← Module.natCard_eq_pow_finrank]
  rfl

theorem finrank_resZeroSub_le_n : Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) ≤ n := by
  have := Submodule.finrank_le (resZeroSub hπ h2 h20 Q han)
  simpa using this

/-- The matrix with columns $c_j$. -/
def colMat {K : Type*} [CommRing K] {n k : ℕ} (c : Fin k → Fin n → K) : Matrix (Fin n) (Fin k) K :=
  Matrix.of fun l j => c j l

theorem colMat_mulVec {K : Type*} [CommRing K] {n k : ℕ} (c : Fin k → Fin n → K) (z : Fin k → K) :
    colMat c *ᵥ z = ∑ j, z j • c j := by
  funext l
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

include hπ h2 h20 han in
/-- **The residue form is anisotropic modulo $\overline W$, so $\operatorname{codim}\overline W\le2$** (every ternary form over a
finite field is isotropic, Chevalley–Warning). -/
theorem le_finrank_resZeroSub_add_two [Finite 𝔽] : n ≤ Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) + 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  set W := resZeroSub hπ h2 h20 Q han with hW
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  rw [Module.finrank_fin_fun] at hdim
  have h3 : 3 ≤ Module.finrank 𝔽 C := by omega
  set b := Module.finBasis 𝔽 C with hb
  set c : Fin 3 → Fin n → 𝔽 := fun j => (b ⟨j.val, by omega⟩ : Fin n → 𝔽) with hc
  obtain ⟨z, hz0, hz⟩ := Tamagawa.exists_isotropic_ternary ((Q.map res).compMat (colMat c))
  rw [eval_compMat, colMat_mulVec] at hz
  have hmemC : (∑ j, z j • c j) ∈ C := Submodule.sum_mem _ fun j _ => C.smul_mem _ (b _).2
  have hmemW : (∑ j, z j • c j) ∈ W := hz
  have h0 : (∑ j, z j • c j) = 0 := by
    have := hC.disjoint
    rw [Submodule.disjoint_def] at this
    exact this _ hmemW hmemC
  -- linear independence of the basis vectors
  have hli := b.linearIndependent
  have e : (∑ j : Fin 3, z j • b ⟨j.val, by omega⟩) = 0 := by
    apply Subtype.ext
    simpa [hc] using h0
  apply hz0
  funext j
  have hinj : Function.Injective (fun j : Fin 3 => (⟨j.val, by omega⟩ : Fin (Module.finrank 𝔽 C))) := by
    intro a a' h; simpa [Fin.ext_iff] using h
  have hli3 := hli.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli3
  exact hli3 z e j

include hπ h2 h20 han in
/-- **Maximality bounds the residue zero space: $\dim\overline W\le2$.** If $\pi^2\mid Q(x)\Rightarrow\pi\mid x$ (`hmax`), then three
independent residue zeros $\bar w_0,\bar w_1,\bar w_2$ would give the ternary form $Q(\sum s_iw_i)/\pi$, whose residue form is isotropic
(Chevalley–Warning); a lift of a residue zero is a vector $x\notin\pi R^n$ with $\pi^2\mid Q(x)$. -/
theorem finrank_resZeroSub_le_two [Finite 𝔽] (hmax : ∀ x : Fin n → R, π ^ 2 ∣ Q.eval x → ∀ i, π ∣ x i) :
    Module.finrank 𝔽 (resZeroSub hπ h2 h20 Q han) ≤ 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  set W := resZeroSub hπ h2 h20 Q han with hW
  set b := Module.finBasis 𝔽 W with hb
  set c : Fin 3 → Fin n → 𝔽 := fun j => (b ⟨j.val, by omega⟩ : Fin n → 𝔽) with hc
  have hcW : ∀ j, c j ∈ W := fun j => (b _).2
  choose w hw using fun j => res_surj_vec (c j)
  set X : Matrix (Fin n) (Fin 3) R := colMat w with hX
  set S := Q.compMat X with hS
  -- every value of `S` is divisible by `π`
  have hwQ : ∀ j, π ∣ Q.eval (w j) := by
    intro j
    rw [← res_eq_zero_iff' hπ, ← eval_map_res, hw j]
    exact hcW j
  have hSdvd : ∀ z, π ∣ S.eval z := by
    intro z
    rw [hS, eval_compMat, hX, colMat_mulVec]
    rw [← res_eq_zero_iff' hπ, ← eval_map_res]
    have e : (fun i => res ((∑ j, z j • w j) i)) = ∑ j, res (z j) • c j := by
      funext i
      simp [Finset.sum_apply, ← hw]
    rw [e]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcW j)
  obtain ⟨S', hS'⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero S hSdvd
  obtain ⟨z, hz0, hz⟩ := Tamagawa.exists_isotropic_ternary (S'.map res)
  obtain ⟨z', rfl⟩ := res_surj_vec z
  rw [eval_map_res, res_eq_zero_iff' hπ] at hz
  have h2z : π ^ 2 ∣ Q.eval (X *ᵥ z') := by
    rw [← eval_compMat, ← hS, hS', eval_smul_form, pow_two]
    exact mul_dvd_mul_left π hz
  have hx := hmax _ h2z
  -- the residue of `X z'` is `∑ z_j c_j = 0`
  have e : (∑ j, res (z' j) • c j) = 0 := by
    funext i
    have := (res_eq_zero_iff' hπ _).2 (hx i)
    rw [hX, colMat_mulVec] at this
    simpa [Finset.sum_apply, ← hw] using this
  have hli := b.linearIndependent
  have hinj : Function.Injective (fun j : Fin 3 => (⟨j.val, by omega⟩ : Fin (Module.finrank 𝔽 W))) := by
    intro a a' h; simpa [Fin.ext_iff] using h
  have hli3 := hli.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli3
  apply hz0
  funext j
  refine hli3 (fun j => res (z' j)) ?_ j
  apply Subtype.ext
  simpa [hc] using e

end Residue

end QuadFormsKB.Hanke2005
