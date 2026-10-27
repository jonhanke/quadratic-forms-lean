/-
# Local densities over a DVR: the dyadic Arf sign is the discriminant square class

**Layer:** DVR, at a **dyadic** prime: $R$ a complete DVR (`IsAdicComplete (maximalIdeal R) R`) with uniformizer
$\pi \mid 2$, $2 \ne 0$, finite residue field $\mathbb{F}$ of characteristic $2$.

**Proves** that for an even unimodular $Q$ ($\pi \nmid N$, so $n = 2r$ and $Q \cong$ `pairSumForm A` with all $b_i$ units) the Arf sign $\varepsilon$ = `arfSignQ Q π` (the dyadic $\Phi_n(\mathfrak p)$) is the square class of the
normalized discriminant $\Delta = (-1)^{n/2}\det H$:
$$\varepsilon = +1 \iff \Delta \in (R^\times)^2 \iff \Delta \in (K^\times)^2 \qquad(\texttt{arfSignQ\_eq\_one\_iff},\ \texttt{arfSignQ\_eq\_one\_iff\_isSquare\_frac}),$$
and $\Delta = B^2(1 - 4T)$ with $B$ a unit (`exists_disc_eq_sq_mul_one_sub_four_of_level_zero`), so $K(\sqrt\Delta)/K$ is
unramified and $\varepsilon$ is its Frobenius. **Route:** $(-1)^r\det H = \prod_i(b_i^2 - 4a_ic_i) = (\prod_i b_i)^2\prod_i(1 - 4t_i)$,
$t_i = a_ic_i/b_i^2$ (`det_hessian_pairSumForm`, `pairSum_disc_eq`); $\prod_i(1 - 4t_i) = 1 - 4T$ with $\bar T = \sum_i\bar t_i$
(`prod_one_sub_four_mul`); $1 - 4T$ is a square iff $X^2 - X + T$ has a root iff (Hensel, simple root) $\bar T \in \wp(\mathbb{F})$
(`isSquare_one_sub_four_mul_iff`); and the Artin–Schreier sign `asSign` is an additive character, as $\wp(\mathbb{F})$ has
index $2$ (`asSign_add`, `asSign_sum`), so $\prod_i\varepsilon(\bar a_i, \bar b_i, \bar c_i) = \mathrm{asSign}(\sum_i\bar t_i)$.
Also the non-dyadic Hensel criterion `isSquare_iff_quadraticChar_residue` (a unit is a square iff its residue is).

**Depends on** `DVRLevel.lean`.
-/
import QuadFormsKB.LocalDensity.DVRLevel

set_option linter.unusedSectionVars false

namespace QuadFormsKB.LocalDensity.DVR

section ArtinSchreier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The Artin–Schreier sign** of $d \in \mathbb{F}$ (characteristic $2$): $+1$ if $d \in \wp(\mathbb{F}) = \{z^2 + z\}$,
$-1$ otherwise. `arfSign a b c = asSign (a c / b^2)`. -/
noncomputable def asSign (d : F) : ℤ := if ∃ z : F, z ^ 2 + z = d then 1 else -1

omit [CharP F 2] in
theorem arfSign_eq_asSign (a b c : F) : arfSign a b c = asSign (a * c / b ^ 2) := rfl

theorem as_add {s t : F} (hs : ∃ z : F, z ^ 2 + z = s) (ht : ∃ z : F, z ^ 2 + z = t) :
    ∃ z : F, z ^ 2 + z = s + t := by
  obtain ⟨z, rfl⟩ := hs
  obtain ⟨w, rfl⟩ := ht
  refine ⟨z + w, ?_⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination z * w * h2

theorem as_add_iff_left {s t : F} (hs : ∃ z : F, z ^ 2 + z = s) :
    (∃ z : F, z ^ 2 + z = s + t) ↔ ∃ z : F, z ^ 2 + z = t := by
  refine ⟨fun h => ?_, as_add hs⟩
  have := as_add h hs
  rwa [show s + t + s = t by rw [add_comm s t, add_assoc, CharTwo.add_self_eq_zero, add_zero]] at this

theorem sum_asSign : ∑ d : F, asSign d = 0 := by
  have h1 : ∑ d : F, asCountF d = Fintype.card F := by
    unfold asCountF
    rw [Finset.sum_comm]
    simp
  simp only [asCountF_eq, Finset.sum_add_distrib] at h1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
  unfold asSign
  linarith

/-- **$\wp(\mathbb{F})$ has index $2$:** the sum of two non-Artin–Schreier elements is Artin–Schreier. -/
theorem as_add_of_not {s t : F} (hs : ¬ ∃ z : F, z ^ 2 + z = s) (ht : ¬ ∃ z : F, z ^ 2 + z = t) :
    ∃ z : F, z ^ 2 + z = s + t := by
  classical
  set P : Finset F := Finset.univ.filter fun d => ∃ z : F, z ^ 2 + z = d
  have hsum : (P.card : ℤ) - (Pᶜ).card = 0 := by
    have h := sum_asSign (F := F)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d => ∃ z : F, z ^ 2 + z = d)] at h
    simp only [asSign] at h
    rw [Finset.sum_ite_of_true (fun _ h => (Finset.mem_filter.1 h).2),
      Finset.sum_ite_of_false (fun _ h => (Finset.mem_filter.1 h).2)] at h
    simp only [Finset.sum_const] at h
    rw [Finset.compl_filter]
    simpa [P, sub_eq_add_neg] using h
  -- translation by `s` maps `P` into `Pᶜ`
  have himg : P.image (· + s) = Pᶜ := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_compl]
      intro hP
      have hdP := (Finset.mem_filter.1 hd).2
      exact hs ((as_add_iff_left hdP).1 (Finset.mem_filter.1 hP).2)
    · rw [Finset.card_image_of_injective _ (add_left_injective s)]
      omega
  have htc : t ∈ Pᶜ := by simpa [P] using ht
  rw [← himg] at htc
  obtain ⟨d, hd, hdt⟩ := Finset.mem_image.1 htc
  have : s + t = d := by
    rw [← hdt, add_comm d s, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [this]; exact (Finset.mem_filter.1 hd).2

/-- **The Artin–Schreier sign is an additive character** $\mathbb{F} \to \{\pm 1\}$ (with kernel $\wp(\mathbb{F})$). -/
theorem asSign_add (s t : F) : asSign (s + t) = asSign s * asSign t := by
  unfold asSign
  by_cases hs : ∃ z : F, z ^ 2 + z = s
  · rw [ite_eq_left hs, one_mul]
    simp only [as_add_iff_left hs]
  · rw [ite_eq_right hs]
    by_cases ht : ∃ z : F, z ^ 2 + z = t
    · rw [ite_eq_left ht, add_comm, ite_eq_right (fun h => hs ((as_add_iff_left ht).1 h))]; ring
    · rw [ite_eq_right ht, ite_eq_left (as_add_of_not hs ht)]; ring

theorem asSign_zero : asSign (0 : F) = 1 := ite_eq_left ⟨0, by ring⟩

theorem asSign_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    asSign (∑ i ∈ s, f i) = ∏ i ∈ s, asSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [asSign_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, asSign_add, ih]

end ArtinSchreier

section Hensel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-- **A square root of $1 - 4t$ is $\equiv 1 \pmod 2$** (any DVR): if $y^2 = 1 - 4t$ then
$2 \mid y - 1$. *Proof:* $(y-1)(y+1) = -4t$; if $2 \nmid u := y - 1$ then $2 = uw$ with $w \in \mathfrak m$, so
$u + 2 = u(1 + w)$ with $1 + w$ a unit, and $u^2w^2 = 4 \mid u^2(1 + w)$ forces $w$ to be a unit. -/
theorem two_dvd_sub_one_of_sq_eq {π : R} (hπ : Irreducible π) {t y : R}
    (h : y ^ 2 = 1 - 4 * t) : 2 ∣ y - 1 := by
  by_contra hu
  set u := y - 1 with hu_def
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 2)
  obtain ⟨w, hw⟩ : u ∣ 2 := (ValuationRing.dvd_total u 2).resolve_right hu
  have hwm : ¬ IsUnit w := fun hw' => hu ⟨((hw'.unit⁻¹ : Rˣ) : R), by rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have hπw : π ∣ w := by
    by_contra hπw
    exact hwm (dvr_isUnit_of_not_dvd hπ hπw)
  have h1w : IsUnit (1 + w) := by
    refine dvr_isUnit_of_not_dvd hπ fun h' => hπ.not_isUnit ?_
    have : π ∣ 1 := by simpa using dvd_sub h' hπw
    exact isUnit_of_dvd_one this
  -- u (u + 2) = -4 t, and u + 2 = u (1 + w), 4 = u² w²
  have key : u ^ 2 * (1 + w) = u ^ 2 * (w ^ 2 * (-t)) := by
    have e1 : u * (u + 2) = -(4 * t) := by rw [hu_def]; linear_combination h
    have e2 : (4 : R) = u ^ 2 * w ^ 2 := by rw [show (4 : R) = 2 ^ 2 by norm_num, hw]; ring
    rw [e2] at e1
    linear_combination e1 - u * hw
  have := mul_left_cancel₀ (pow_ne_zero 2 hu0) key
  exact hwm (isUnit_of_mul_isUnit_left (x := w) (y := w * -t) (by rw [← mul_assoc, ← sq, ← this]; exact h1w))

/-- **Hensel–Artin–Schreier criterion** (complete DVR, $\pi \mid 2 \ne 0$): $1 - 4t$ is a square in $R$ iff
$\bar t \in \wp(\mathbb{F}) = \{z^2 + z\}$. *Proof:* $1 - 4t = (1 - 2x)^2 \iff x^2 - x + t = 0$; a root of $X^2 - X + t$ mod $\pi$
is simple (derivative $2x - 1$ a unit) and lifts by Hensel's lemma; conversely every square root of $1 - 4t$ is
$\equiv 1 \pmod 2$ (`two_dvd_sub_one_of_sq_eq`). -/
@[kb "omeara1963" "§63A, 63:1 (proof), 63:3, 63:4, pp. 159–161"]
theorem isSquare_one_sub_four_mul_iff [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R}
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (t : R) :
    IsSquare (1 - 4 * t) ↔ ∃ z : 𝔽, z ^ 2 + z = res t := by
  have hc := charP_residueField_two hπ h2
  have h2F : (2 : 𝔽) = 0 := CharTwo.two_eq_zero
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ := two_dvd_sub_one_of_sq_eq hπ (t := t) (y := y) (by rw [hy]; ring)
    -- y = 1 + 2c, so (with x = -c) x² - x + t = 0
    have h4 : (4 : R) * (c ^ 2 + c + t) = 0 := by
      have : y = 1 + 2 * c := by linear_combination hc
      rw [this] at hy; linear_combination -hy
    have h40 : (4 : R) ≠ 0 := by
      rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
    have hx := (mul_eq_zero.1 h4).resolve_left h40
    refine ⟨res c, ?_⟩
    have := congrArg res hx
    simp only [map_add, map_pow, map_zero] at this
    linear_combination this - res t * h2F
  · rintro ⟨z, hz⟩
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective z
    let f : Polynomial R := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C t
    have hf : f.Monic := by unfold f; monicity!
    have hev : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [f, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, map_add, map_sub, map_pow]
      linear_combination hz - res a₀ * h2F + res t * h2F
    have hder : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.derivative.eval a₀)) := by
      refine IsUnit.map _ ?_
      have : f.derivative.eval a₀ = 2 * a₀ - 1 := by
        simp only [f, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
          Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_zero]
        push_cast; ring
      rw [this]
      refine dvr_isUnit_of_not_dvd hπ fun h' => hπ.not_isUnit (isUnit_of_dvd_one ?_)
      have : π ∣ 2 * a₀ := h2.mul_right _
      simpa using dvd_sub this h'
    obtain ⟨x, hx, -⟩ := HenselianRing.is_henselian f hf a₀ hev hder
    refine ⟨1 - 2 * x, ?_⟩
    have : x ^ 2 - x + t = 0 := by
      simpa [f, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub] using hx
    linear_combination (-4 : R) * this

/-- **Non-dyadic Hensel square criterion** (complete DVR, $\pi \nmid 2$, finite residue field): a unit $x$ is a square in $R$
iff its residue is a square, i.e. $\chi_\pi(\bar x) = 1$ (the quadratic character of $\mathbb{F}$). -/
theorem isSquare_iff_quadraticChar_residue [Fintype 𝔽] [DecidableEq 𝔽]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {x : R}
    (hx : ¬ π ∣ x) : IsSquare x ↔ quadraticChar 𝔽 (res x) = 1 := by
  have hx0 : res x ≠ 0 := fun h => hx ((residue_eq_zero_iff_dvd hπ x).1 h)
  rw [quadraticChar_one_iff_isSquare hx0]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨res y, map_mul _ _ _⟩
  · rintro ⟨s, hs⟩
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective s
    have ha₀ : ¬ π ∣ a₀ := fun h => hx0 (by rw [hs, (residue_eq_zero_iff_dvd hπ a₀).2 h, zero_mul])
    let f : Polynomial R := Polynomial.X ^ 2 - Polynomial.C x
    have hf : f.Monic := by unfold f; monicity!
    have hev : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, map_sub,
        map_pow, hs]
      ring
    have hder : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.derivative.eval a₀)) := by
      refine IsUnit.map _ ?_
      have : f.derivative.eval a₀ = 2 * a₀ := by
        simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_zero]
        push_cast; ring
      rw [this]
      exact (dvr_isUnit_of_not_dvd hπ h2).mul (dvr_isUnit_of_not_dvd hπ ha₀)
    obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian f hf a₀ hev hder
    refine ⟨y, ?_⟩
    have : y ^ 2 - x = 0 := by simpa [f, Polynomial.IsRoot] using hy
    linear_combination -this

/-- **Squares of units in $R$ and in the fraction field agree**: for $x \in R$, $x$ is a square in $K$ iff it is a
square in $R$ ($R$ is integrally closed). -/
theorem isSquare_algebraMap_iff (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : R) :
    IsSquare (algebraMap R K x) ↔ IsSquare x := by
  constructor
  · rintro ⟨y, hy⟩
    have hint : IsIntegral R y := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C x, by monicity!, ?_⟩
      simp [Polynomial.eval₂_sub, hy, sq]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨z, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hz, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap R K y, map_mul _ _ _⟩

end Hensel

section PairSum

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-- **Products of elements $\equiv 1 \pmod 4$:** $\prod_{i \in s}(1 - 4t_i) = 1 - 4T$ with $\bar T = \sum_{i \in s}\bar t_i$ (at
$\pi \mid 2$; $(1 - 4S)(1 - 4t) = 1 - 4(S + t - 4St)$). -/
theorem prod_one_sub_four_mul {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) {ι : Type*} (s : Finset ι) (t : ι → R) :
    ∃ T : R, ∏ i ∈ s, (1 - 4 * t i) = 1 - 4 * T ∧ res T = ∑ i ∈ s, res (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨T, hT, hres⟩ := ih
    refine ⟨t a + T - 4 * t a * T, ?_, ?_⟩
    · rw [Finset.prod_insert ha, hT]; ring
    · have h4 : res 4 = 0 := by
        rw [residue_eq_zero_iff_dvd hπ, show (4 : R) = 2 * 2 by norm_num]; exact h2.mul_right _
      rw [Finset.sum_insert ha, ← hres, map_sub, map_add, map_mul, map_mul, h4]; ring

/-- **The Hessian determinant of a `pairSumForm`**: $\det H = \prod_i (4a_ic_i - b_i^2)$ (block diagonal with blocks
$\begin{pmatrix} 2a_i & b_i \\ b_i & 2c_i \end{pmatrix}$). -/
theorem det_hessian_pairSumForm {S : Type*} [CommRing S] {r : ℕ} (A : Fin r → S × S × S) :
    (pairSumForm A).hessian.det = ∏ i, (4 * (A i).1 * (A i).2.2 - (A i).2.1 ^ 2) := by
  classical
  set e : Fin 2 × Fin r ≃ Fin (r * 2) := (Equiv.prodComm _ _).trans finProdFinEquiv
  set B : Fin r → Matrix (Fin 2) (Fin 2) S := fun i => !![2 * (A i).1, (A i).2.1; (A i).2.1, 2 * (A i).2.2]
  have hM : (pairSumForm A).hessian.submatrix e e = Matrix.blockDiagonal B := by
    ext ⟨j, i⟩ ⟨j', i'⟩
    simp only [Matrix.submatrix_apply, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.blockDiagonal_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, B]
    rw [show finProdFinEquiv (i, j) = pidx i j from rfl, show finProdFinEquiv (i', j') = pidx i' j' from rfl,
      pairSumForm_coeff, pairSumForm_coeff]
    by_cases hii : i = i'
    · subst hii
      fin_cases j <;> fin_cases j' <;> simp <;> ring
    · simp [hii, Ne.symm hii]
  rw [← Matrix.det_submatrix_equiv_self e, hM, Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [B, Matrix.det_fin_two_of]; ring

theorem isSquare_unit_sq_mul_iff {B x : R} (hB : IsUnit B) : IsSquare (B ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨((hB.unit⁻¹ : Rˣ) : R) * y, ?_⟩
    have : x = ((hB.unit⁻¹ : Rˣ) : R) ^ 2 * (B ^ 2 * x) := by
      rw [← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
    rw [this, hy]; ring
  · rintro ⟨y, rfl⟩; exact ⟨B * y, by ring⟩

/-- **The discriminant of an even unimodular `pairSumForm` is $\equiv 1 \pmod 4$ up to unit squares** ($\pi \mid 2$, all $b_i$
units): $(-1)^r\det H = \prod_i(b_i^2 - 4a_ic_i) = (\prod_i b_i)^2(1 - 4T)$ with $\bar T = \sum_i \bar a_i\bar c_i/\bar b_i^2$ (the
Arf invariant). -/
theorem pairSum_disc_eq {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) {r : ℕ} (A : Fin r → R × R × R)
    (hb : ∀ i, ¬ π ∣ (A i).2.1) :
    ∃ T : R, (-1) ^ r * (pairSumForm A).hessian.det = (∏ i, (A i).2.1) ^ 2 * (1 - 4 * T) ∧
      res T = ∑ i, res (A i).1 * res (A i).2.2 / res (A i).2.1 ^ 2 := by
  have hu : ∀ i, IsUnit (A i).2.1 := fun i => dvr_isUnit_of_not_dvd hπ (hb i)
  set t : Fin r → R := fun i => (A i).1 * (A i).2.2 * (((hu i).unit⁻¹ : Rˣ) : R) ^ 2
  obtain ⟨T, hT, hres⟩ := prod_one_sub_four_mul hπ h2 Finset.univ t
  refine ⟨T, ?_, ?_⟩
  · rw [det_hessian_pairSumForm, ← hT, ← Fin.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hinv : (A i).2.1 * (((hu i).unit⁻¹ : Rˣ) : R) = 1 := IsUnit.mul_val_inv _
    simp only [t]
    linear_combination (4 * (A i).1 * (A i).2.2 * ((A i).2.1 * (((hu i).unit⁻¹ : Rˣ) : R) + 1)) * hinv
  · rw [hres]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinv : res (A i).2.1 * res (((hu i).unit⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have hne : res (A i).2.1 ≠ 0 := fun h => by simp [h] at hinv
    simp only [t, map_mul, map_pow]
    field_simp
    linear_combination (res (A i).1 * res (A i).2.2 * (res (A i).2.1 * res (((hu i).unit⁻¹ : Rˣ) : R) + 1))
      * hinv

/-- **The Arf sign of an even unimodular `pairSumForm` is the discriminant square class** (complete DVR, $\pi \mid 2 \ne 0$, all
$b_i$ units): $\varepsilon = \prod_i\varepsilon(\bar a_i, \bar b_i, \bar c_i) = +1 \iff (-1)^r\det H$ is a square in $R$. -/
theorem pairArf_eq_one_iff [Fintype 𝔽] [DecidableEq 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R}
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {r : ℕ} (A : Fin r → R × R × R)
    (hb : ∀ i, ¬ π ∣ (A i).2.1) :
    pairArf A = 1 ↔ IsSquare ((-1) ^ r * (pairSumForm A).hessian.det) := by
  have := charP_residueField_two hπ h2
  obtain ⟨T, hT, hres⟩ := pairSum_disc_eq hπ h2 A hb
  have hB : IsUnit (∏ i, (A i).2.1) :=
    IsUnit.prod_univ_iff.2 fun i => dvr_isUnit_of_not_dvd hπ (hb i)
  rw [hT, isSquare_unit_sq_mul_iff hB, isSquare_one_sub_four_mul_iff hπ h2 h20, hres, pairArf]
  simp only [arfSign_eq_asSign]
  rw [← asSign_sum]
  unfold asSign
  split_ifs with h <;> simp [h]

end PairSum

section General

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R

/-- **The dyadic Arf sign is the discriminant square class** (complete DVR, $\pi \mid 2 \ne 0$, finite residue field;
$Q$ even unimodular, i.e. $\pi \nmid N$, $n = 2r \ge 2$): with $\Delta = (-1)^{n/2}\det H$,
$$\varepsilon(Q \bmod \pi) = +1 \iff \Delta \in (R^\times)^2.$$
Since $\Delta \equiv 1 \pmod 4$ up to unit squares (`exists_disc_eq_sq_mul_one_sub_four_of_level_zero`), $K(\sqrt\Delta)/K$ is
unramified, and $\varepsilon$ is its Frobenius: $+1$ iff it splits (is trivial). -/
@[kb "omeara1963" "§93D, 93:16, p. 259; 93:18, p. 260 (dyadic unimodular lattices)"]
theorem arfSignQ_eq_one_iff [Fintype 𝔽] [DecidableEq 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)
    (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) :
    arfSignQ Q π = 1 ↔ IsSquare ((-1) ^ (n / 2) * Q.hessian.det) := by
  obtain ⟨r, A, h, hb, hE⟩ := exists_pairSum_of_isLocalLevel_zero Q hπ h2 h20 hL
  subst h
  obtain ⟨u, hu, hdet⟩ := hE.det_hessian
  rw [(hE.sameCounts π).arfSign_eq, arfSign_pairSumForm A hπ h2 hb (by omega),
    pairArf_eq_one_iff hπ h2 h20 A hb, hdet, show r * 2 / 2 = r by omega,
    show (-1) ^ r * (u ^ 2 * Q.hessian.det) = u ^ 2 * ((-1) ^ r * Q.hessian.det) by ring,
    isSquare_unit_sq_mul_iff hu]

/-- **Unramifiedness:** at dyadic $\pi \nmid N$, $\Delta = (-1)^{n/2}\det H = B^2(1 - 4T)$ with $B$ a unit, so
$K(\sqrt\Delta) = K(\sqrt{1 - 4T})$ is generated by a root of $X^2 - X + T$ (unramified over $K$). -/
theorem exists_disc_eq_sq_mul_one_sub_four_of_level_zero (Q : QuadForm R n) {π : R} (hπ : Irreducible π)
    (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (hL : IsLocalLevel Q π 0) :
    ∃ B T : R, IsUnit B ∧ (-1) ^ (n / 2) * Q.hessian.det = B ^ 2 * (1 - 4 * T) := by
  obtain ⟨r, A, h, hb, hE⟩ := exists_pairSum_of_isLocalLevel_zero Q hπ h2 h20 hL
  subst h
  obtain ⟨u, hu, hdet⟩ := hE.det_hessian
  obtain ⟨T, hT, -⟩ := pairSum_disc_eq hπ h2 A hb
  have hB : IsUnit (∏ i, (A i).2.1) :=
    IsUnit.prod_univ_iff.2 fun i => dvr_isUnit_of_not_dvd hπ (hb i)
  refine ⟨((hu.unit⁻¹ : Rˣ) : R) * ∏ i, (A i).2.1, T, (Units.isUnit _).mul hB, ?_⟩
  rw [show r * 2 / 2 = r by omega, mul_pow, mul_assoc, ← hT, hdet]
  have : ((hu.unit⁻¹ : Rˣ) : R) ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, IsUnit.val_inv_mul, one_pow]
  linear_combination (-(-1) ^ r * Q.hessian.det) * this

/-- `arfSignQ_eq_one_iff` with squares in the fraction field $K$ ("$\Delta$ is a square in $F_\mathfrak p$"). -/
theorem arfSignQ_eq_one_iff_isSquare_frac [Fintype 𝔽] [DecidableEq 𝔽]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)
    (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) :
    arfSignQ Q π = 1 ↔ IsSquare (algebraMap R K ((-1) ^ (n / 2) * Q.hessian.det)) := by
  rw [isSquare_algebraMap_iff, arfSignQ_eq_one_iff Q hπ h2 h20 hL hn]

theorem arfSignQ_eq_neg_one_iff [Fintype 𝔽] [DecidableEq 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Q : QuadForm R n) {π : R} (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)
    (hL : IsLocalLevel Q π 0) (hn : 1 ≤ n) :
    arfSignQ Q π = -1 ↔ ¬ IsSquare ((-1) ^ (n / 2) * Q.hessian.det) := by
  rw [← arfSignQ_eq_one_iff Q hπ h2 h20 hL hn]
  unfold arfSignQ; split_ifs <;> decide

end General

end QuadFormsKB.LocalDensity.DVR
