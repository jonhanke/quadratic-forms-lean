/-
# The stabilizer of $\mathcal O_v^0$: split and ramified places

**Layer:** as in `TernaryFrame.lean`; $\mathcal O$ a **maximal** order, $v$ a finite place.

**Proves**
* *Split places* ($\varphi : D_v \cong M_2(F_v)$, $\varphi(\mathcal O_v) = M_2(\mathfrak o_v)$): if conjugation by $x$ preserves $\mathcal O_v^0$
  then it preserves $\mathcal O_v$ ($\mathcal O_v^0$ generates $\mathcal O_v$: $e_{11} = e_{12}e_{21}$), and the normalizer of $M_2(\mathfrak o_v)$ in
  $GL_2(F_v)$ is $F_v^\times GL_2(\mathfrak o_v)$ (`exists_scalar_mul_unit_of_conj`); hence
  $SO(\mathfrak o_v^3) = K'_v = c_v(\mathcal O_v^\times)$ (`TZFrame.mem_Kv_of_mem_stdStab_split`).
* *Ramified places* ($D_v$ division, $\mathcal O_v = \{\operatorname{nrd} \in \mathfrak o_v\}$): every $c_v(x)$ stabilizes $\mathfrak o_v^3$
  (`TZFrame.cvv_mem_stdStab_ramified`), and $c_v(x) \in K'_v$ iff $\operatorname{ord}_v\operatorname{nrd}x$ is even
  (`TZFrame.cvv_mem_Kv_iff_even`); an $x$ with $\operatorname{ord}_v\operatorname{nrd}x = 1$ exists.

Source: Voight 2021, Prop. 13.3.4, (13.3.8), Lemma 23.3.? (normalizers of maximal orders, local) [unverified locator], Exercise 23.?;
Weil 1982, §3.7(a).
-/
import QuadFormsKB.Tamagawa.TernaryFrame

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

/-! ### The normalizer of $M_2(\mathfrak o)$ -/

section Normalizer

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem isInteger_iff_le_one (x : Fv) : IsInteger 𝔬 x ↔ Valued.v x ≤ 1 := isInteger_iff_le_one' v x

/-- **The normalizer of $M_2(\mathfrak o_v)$ is $F_v^\times GL_2(\mathfrak o_v)$:** if $XEX^{-1} \in M_2(\mathfrak o_v)$ for every
$E \in M_2(\mathfrak o_v)$, then $X = rY$ with $Y, Y^{-1} \in M_2(\mathfrak o_v)$.

*Proof.* Scale $X$ by an entry of largest absolute value to get $Y$ with integral entries and one entry $Y_{kl} = 1$.
For $E = e_{l,l'}$ ($l' \ne l$) the $(k,k')$ entry of $YE\operatorname{adj}(Y) = \det(Y)\cdot YEY^{-1}$ is $\pm Y_{kl}^2 = \pm1$, so
$\det Y$ is a unit and $Y^{-1} = \det(Y)^{-1}\operatorname{adj}Y$ is integral. -/
theorem exists_scalar_mul_unit_of_conj (X : GL (Fin 2) Fv)
    (h : ∀ E ∈ matOrder 𝔬 Fv, X.val * E * (X⁻¹).val ∈
      matOrder 𝔬 Fv) :
    ∃ r : Fv, r ≠ 0 ∧ r⁻¹ • X.val ∈ matOrder 𝔬 Fv ∧
      r • (X⁻¹).val ∈ matOrder 𝔬 Fv := by
  set M := X.val
  set Mi := (X⁻¹).val
  have hMMi : M * Mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨⟨k, l⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun p => Valued.v (M p.1 p.2)) Finset.univ_nonempty
  set r := M k l
  have hr : r ≠ 0 := by
    intro h0
    have hall : M = 0 := Matrix.ext fun i j => by
      have := hmax (i, j) (Finset.mem_univ _)
      simp only [r, h0, map_zero, le_zero_iff, map_eq_zero] at this
      rw [this]; rfl
    have := congrArg Matrix.det hMMi
    rw [hall, Matrix.zero_mul, det_one] at this
    simp at this
  have hvr : Valued.v r ≠ 0 := (map_ne_zero _).2 hr
  set Y := r⁻¹ • M
  have hYint : ∀ i j, Valued.v (Y i j) ≤ 1 := by
    intro i j
    simp only [Y, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvr), mul_one]
    exact hmax (i, j) (Finset.mem_univ _)
  have hYkl : Y k l = 1 := by simp [Y, r, inv_mul_cancel₀ hr]
  have hYmem : Y ∈ matOrder 𝔬 Fv := (mem_matOrder).2 fun i j => (isInteger_iff_le_one v _).2 (hYint i j)
  set Yi := r • Mi
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, smul_mul_smul_comm, inv_mul_cancel₀ hr, one_smul, hMMi]
  have hconj : ∀ E, Y * E * Yi = M * E * Mi := by
    intro E
    simp only [Y, Yi, smul_mul_assoc, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]
  -- Yi = det(Y)⁻¹ • adj Y
  have hdetY : Y.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hYYi
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hYi : Yi = (Y.det)⁻¹ • Y.adjugate := by
    have h1 : Yi = Y⁻¹ := (Matrix.inv_eq_right_inv hYYi).symm
    rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
  -- the key entry
  set l' : Fin 2 := if l = 0 then 1 else 0
  set k' : Fin 2 := if k = 0 then 1 else 0
  have hE : Matrix.single l l' (1 : Fv) ∈ matOrder 𝔬 Fv := single_mem_matOrder l l'
  have hent := (mem_matOrder).1 (h _ hE) k k'
  rw [← hconj, hYi] at hent
  have hkey : (Y * Matrix.single l l' (1 : Fv) * ((Y.det)⁻¹ • Y.adjugate)) k k' = (Y.det)⁻¹ * (Y k l * Y.adjugate l' k') := by
    rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    congr 1
    fin_cases l <;> simp [l', Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hadj : Y.adjugate l' k' = 1 ∨ Y.adjugate l' k' = -1 := by
    rw [Matrix.adjugate_fin_two]
    fin_cases k <;> fin_cases l <;> simp_all [l', k']
  rw [hkey, hYkl, one_mul] at hent
  rw [isInteger_iff_le_one] at hent
  have hvdet : Valued.v Y.det = 1 := by
    have hle : Valued.v Y.det ≤ 1 := by
      rw [Matrix.det_fin_two]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;>
        rw [map_mul] <;> exact mul_le_one' (hYint _ _) (hYint _ _)
    have hge : 1 ≤ Valued.v Y.det := by
      have hpos : 0 < Valued.v Y.det := zero_lt_iff.2 ((map_ne_zero _).2 hdetY)
      rcases hadj with h1 | h1 <;> rw [h1] at hent <;> simp only [mul_one, mul_neg, Valuation.map_neg,
        map_inv₀] at hent <;> exact (inv_le_one₀ hpos).1 hent
    exact le_antisymm hle hge
  refine ⟨r, hr, hYmem, ?_⟩
  rw [show r • Mi = Yi from rfl, hYi]
  refine (mem_matOrder).2 fun i j => (isInteger_iff_le_one v _).2 ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hvdet, inv_one, one_mul, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hYint]

end Normalizer

/-! ### Split places -/

section Split

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))
  (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
  (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
    (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

include hφ in
theorem mem_localOrder_iff_split (z : QuatV v a b) : z ∈ localOrder (v := v) a b O ↔ φ z ∈ matOrder 𝔬 Fv := by
  rw [← hφ]
  constructor
  · intro hz; exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have : w = z := φ.injective hwz
    rwa [← this]

theorem trd_eq_trace (z : QuatV v a b) : trd z = (φ z).trace := by
  have h1 := det_algEquiv φ (1 + z)
  rw [map_add, map_one] at h1
  have h2 := det_algEquiv φ z
  have h3 : nrd (1 + z) = 1 + trd z + nrd z := by
    simp only [nrd, trd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
      QuaternionAlgebra.imK_one]
    ring
  have h4 : (1 + φ z).det = 1 + (φ z).trace + (φ z).det := by
    rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]; simp; ring
  rw [h3, h4, h2] at h1
  linear_combination h1.symm

theorem re_eq_zero_iff_trace (z : QuatV v a b) : z.re = 0 ↔ (φ z).trace = 0 := by
  rw [← trd_eq_trace v φ, trd]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.1 h).resolve_left two_ne_zero

/-- $E_{12} = \varphi^{-1}(e_{12})$, $E_{21} = \varphi^{-1}(e_{21})$. -/
def E12 : QuatV v a b := φ.symm (Matrix.single 0 1 1)
def E21 : QuatV v a b := φ.symm (Matrix.single 1 0 1)

include hφ in
theorem E12_mem : E12 v φ ∈ fr.Ov0 v := by
  rw [fr.mem_Ov0_iff, mem_localOrder_iff_split v φ hφ, re_eq_zero_iff_trace v φ, E12, AlgEquiv.apply_symm_apply]
  exact ⟨single_mem_matOrder 0 1, by simp [Matrix.trace_fin_two]⟩

include hφ in
theorem E21_mem : E21 v φ ∈ fr.Ov0 v := by
  rw [fr.mem_Ov0_iff, mem_localOrder_iff_split v φ hφ, re_eq_zero_iff_trace v φ, E21, AlgEquiv.apply_symm_apply]
  exact ⟨single_mem_matOrder 1 0, by simp [Matrix.trace_fin_two]⟩

include hφ in
/-- Every element of $\mathcal O_v$ is $c_{00}E_{12}E_{21} + c_{01}E_{12} + c_{10}E_{21} + c_{11}E_{21}E_{12}$ with $c_{ij} \in \mathfrak o_v$. -/
theorem exists_decomp {w : QuatV v a b} (hw : w ∈ localOrder (v := v) a b O) :
    ∃ c : Fin 2 → Fin 2 → 𝔬, w = (c 0 0 : Fv) • (E12 v φ * E21 v φ) + (c 0 1 : Fv) • E12 v φ +
      (c 1 0 : Fv) • E21 v φ + (c 1 1 : Fv) • (E21 v φ * E12 v φ) := by
  have hm := (mem_matOrder).1 ((mem_localOrder_iff_split v φ hφ w).1 hw)
  choose c hc using hm
  refine ⟨c, φ.injective ?_⟩
  simp only [map_add, map_smul, map_mul, E12, E21, AlgEquiv.apply_symm_apply]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_mul_single_same, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, hc,
      Matrix.mul_apply, Fin.sum_univ_two] <;> exact (hc _ _).symm

theorem conj_smul (x : (QuatV v a b)ˣ) (c : Fv) (z : QuatV v a b) :
    (x : QuatV v a b) * (c • z) * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
      c • ((x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) := by
  rw [mul_smul_comm, smul_mul_assoc]

theorem conj_mul (x : (QuatV v a b)ˣ) (y z : QuatV v a b) :
    (x : QuatV v a b) * (y * z) * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
      ((x : QuatV v a b) * y * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) *
        ((x : QuatV v a b) * z * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

include hφ in
/-- **At a split place, preserving $\mathcal O_v^0$ means preserving $\mathcal O_v$.** -/
theorem conj_mem_localOrder_of_conjPres {x : (QuatV v a b)ˣ} (hx : ConjPres v (fr.Ov0 v) x)
    {w : QuatV v a b} (hw : w ∈ localOrder (v := v) a b O) :
    (x : QuatV v a b) * w * ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O := by
  obtain ⟨c, rfl⟩ := exists_decomp v φ hφ hw
  have h12 := fr.Ov0_le v _ (hx _ (E12_mem fr v φ hφ))
  have h21 := fr.Ov0_le v _ (hx _ (E21_mem fr v φ hφ))
  simp only [mul_add, add_mul, conj_smul, conj_mul]
  have hsm : ∀ (d : 𝔬) {z : QuatV v a b}, z ∈ localOrder (v := v) a b O → (d : Fv) • z ∈ localOrder (v := v) a b O :=
    fun d z hz => by
      rw [show (d : Fv) • z = d • z from (algebraMap_smul Fv d z).symm]
      exact Subalgebra.smul_mem _ hz d
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
  · exact hsm _ (Subalgebra.mul_mem _ h12 h21)
  · exact hsm _ h12
  · exact hsm _ h21
  · exact hsm _ (Subalgebra.mul_mem _ h21 h12)

/-- The image of a unit under an algebra isomorphism to $M_2$. -/
def matUnit (x : (QuatV v a b)ˣ) : GL (Fin 2) Fv := Units.map (φ : QuatV v a b →* Matrix (Fin 2) (Fin 2) Fv) x

include hφ in
/-- **At a split place, $SO(\mathfrak o_v^3) \cap c_v(D_v^\times) = c_v(\mathcal O_v^\times)$:** if $c_v(x)$ stabilizes $\mathfrak o_v^3$, then
$c_v(x) \in K'_v$. -/
theorem TZFrame.mem_Kv_of_mem_stdStab_split (ha : a ≠ 0) (x : (QuatV v a b)ˣ) (hx : fr.cvv v x ∈ stdStab fr.QF v) :
    fr.cvv v x ∈ fr.Kv v := by
  have hpres := ((fr.cvv_mem_stdStab_iff v x).1 hx).1
  set X := matUnit v φ x
  have hX : ∀ E ∈ matOrder 𝔬 Fv, X.val * E * (X⁻¹).val ∈
      matOrder 𝔬 Fv := by
    intro E hE
    have hE' : φ.symm E ∈ localOrder (v := v) a b O := by
      rw [mem_localOrder_iff_split v φ hφ, AlgEquiv.apply_symm_apply]; exact hE
    have := conj_mem_localOrder_of_conjPres fr v φ hφ hpres hE'
    rw [mem_localOrder_iff_split v φ hφ, map_mul, map_mul, AlgEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨r, hr, h1, h2⟩ := exists_scalar_mul_unit_of_conj v X hX
  -- u = r⁻¹ x is a unit of O_v
  set u : (QuatV v a b)ˣ := qScalar r⁻¹ (inv_ne_zero hr) * x
  have hu : u ∈ unitsOv (O := O) v := by
    refine ⟨?_, ?_⟩
    · rw [mem_localOrder_iff_split v φ hφ]
      have hu' : (u : QuatV v a b) = algebraMap Fv (QuatV v a b) r⁻¹ * x := by rw [Units.val_mul, coe_qScalar]
      rw [hu', map_mul, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
      exact h1
    · rw [mem_localOrder_iff_split v φ hφ]
      have hXi : (X⁻¹).val = φ ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) := rfl
      have hui : ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
          ((x⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) * algebraMap Fv (QuatV v a b) r := by
        simp only [u, _root_.mul_inv_rev, Units.val_mul, qScalar_inv, coe_qScalar, inv_inv]
      rw [hui, map_mul, AlgEquiv.commutes, ← hXi, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
      exact h2
  rw [fr.cvv_mem_Kv_iff v ha]
  refine ⟨r, u, hu, ?_⟩
  simp only [u, Units.val_mul, coe_qScalar, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]

end Split

/-! ### Ramified places -/

section Ramified

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))
  (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0)
  (heq : localOrder (v := v) a b O = valOrder (R := v.adicCompletionIntegers F) hdiv)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

include heq in
theorem conjPres_ramified (x : (QuatV v a b)ˣ) : ConjPres v (fr.Ov0 v) x := by
  intro z hz
  rw [fr.mem_Ov0_iff, heq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_valOrder, nrd_mul, nrd_mul, mul_comm, ← mul_assoc, ← nrd_mul, Units.inv_mul, nrd_one, one_mul]
    exact hz.1
  · have hz0 : z = pure (imv z) := (pure_imv hz.2).symm
    rw [hz0]; exact re_conj x (imv z)

include heq in
/-- **At a ramified place every $c_v(x)$ stabilizes $\mathfrak o_v^3$** ($\mathcal O_v$ is normalized by all of $D_v^\times$). -/
theorem TZFrame.cvv_mem_stdStab_ramified (x : (QuatV v a b)ˣ) : fr.cvv v x ∈ stdStab fr.QF v :=
  (fr.cvv_mem_stdStab_iff v x).2 ⟨conjPres_ramified fr v hdiv heq x, conjPres_ramified fr v hdiv heq x⁻¹⟩

include heq in
theorem mem_unitsOv_ramified_iff (u : (QuatV v a b)ˣ) :
    u ∈ unitsOv (O := O) v ↔ Valued.v (nrd (u : QuatV v a b)) = 1 := by
  rw [mem_unitsOv, heq, mem_valOrder, mem_valOrder, inv_eq, nrd_smul, nrd_star, isInteger_iff_le_one,
    isInteger_iff_le_one]
  have hn := nrd_units_ne_zero u
  rw [show (nrd (u : QuatV v a b))⁻¹ ^ 2 * nrd (u : QuatV v a b) = (nrd (u : QuatV v a b))⁻¹ by
    field_simp]
  rw [map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < Valued.v (nrd (u : QuatV v a b)) := zero_lt_iff.2 ((map_ne_zero _).2 hn)
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  · intro h; rw [h]; simp

include heq in
/-- **At a ramified place, $c_v(x) \in K'_v$ iff $\operatorname{nrd}x$ has even valuation.** -/
theorem TZFrame.cvv_mem_Kv_iff_even (ha : a ≠ 0) (x : (QuatV v a b)ˣ) (k : ℤ)
    (hk : Valued.v (nrd (x : QuatV v a b)) = exp k) : fr.cvv v x ∈ fr.Kv v ↔ Even k := by
  rw [fr.cvv_mem_Kv_iff v ha]
  constructor
  · rintro ⟨r, u, hu, hx⟩
    have hu1 := (mem_unitsOv_ramified_iff v hdiv heq u).1 hu
    have hr : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [hx, map_zero, zero_mul])
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hr
    rw [hx, nrd_mul, map_mul, hu1] at hk
    have : nrd (algebraMap Fv (QuatV v a b) r) = r ^ 2 := by
      simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
    rw [this, mul_one, map_pow, hm, ← WithZero.exp_nsmul, WithZero.exp_inj] at hk
    exact ⟨m, by rw [← hk]; simp; ring⟩
  · rintro ⟨m, rfl⟩
    -- r = ϖ^{-m}, u = ϖ^m x
    set r : Fv := algebraMap F Fv (unifF v ^ (-m))
    have hr : r ≠ 0 := by
      intro h0
      have := valued_unifF_zpow v (-m)
      rw [show algebraMap F Fv (unifF v ^ (-m)) = r from rfl, h0, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    set u : (QuatV v a b)ˣ := qScalar r⁻¹ (inv_ne_zero hr) * x
    have hu : u ∈ unitsOv (O := O) v := by
      rw [mem_unitsOv_ramified_iff v hdiv heq]
      have : nrd (algebraMap Fv (QuatV v a b) r⁻¹) = r⁻¹ ^ 2 := by
        simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
      simp only [u, Units.val_mul, coe_qScalar, nrd_mul, this, map_mul, map_pow, map_inv₀, hk]
      have hvr : Valued.v r = exp m := by
        rw [valued_unifF_zpow]; simp
      rw [hvr, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
      simp; ring
    refine ⟨r, u, hu, ?_⟩
    simp only [u, Units.val_mul, coe_qScalar, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]

/-- An element of reduced norm of valuation $e^{-1}$ (odd) exists. -/
theorem exists_nrd_odd (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : (QuatV v a b)ˣ, Valued.v (nrd (x : QuatV v a b)) = exp (-1 : ℤ) := by
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  have hc : algebraMap F Fv (unifF v) ≠ 0 := (map_ne_zero _).2 (unifF_ne_zero v)
  obtain ⟨y, hy⟩ := exists_nrd_eq_finite' ha' hb' v hc
  have hy0 : nrd y ≠ 0 := by rw [hy]; exact hc
  refine ⟨((isUnit_iff_nrd_ne_zero y).2 hy0).unit, ?_⟩
  change Valued.v (nrd y) = _
  rw [hy, valued_algebraMap, valuation_unifF]

end Ramified

end QuadFormsKB.QuatOrder
