/-
# Sections of the induced representation from the Weil representation

**Layer:** local. The abstract Weil representation of `Weil/Model.lean` (so every place at once: `weilRepV` at the
finite places, `weilRepInf` at $\infty$), then the finite places $v$ of a number field (dyadic included).

**Conventions** (as in `Weil/Model.lean`, Kudla, *Notes*, §I.1): $n(b) = \begin{pmatrix}1&b\\0&1\end{pmatrix}$,
$m(a) = \begin{pmatrix}a&0\\0&a^{-1}\end{pmatrix}$, $w = \begin{pmatrix}0&1\\-1&0\end{pmatrix}$; $V = \langle a_0,\dots,a_{2m-1}\rangle$,
$n = 2m$ (0-based indices), $\chi_V(t) = (t, (-1)^m\det V)$ (`chiV`), $|t|$ the Haar modulus (`md`). The
Borel subgroup is $B = \{n(b)m(a)\}$, and
$$I(s,\chi_V) = \{f : f(n(b)m(a)g) = \chi_V(a)\,|a|^{s+1}f(g)\},\qquad s_0 = \tfrac n2 - 1 = m - 1.$$

**Results.**
* `sec`, `sec_borel` (**item 1**): for $\Phi \in S(V)$ the function $f_\Phi(g) = (\omega(g)\Phi)(0)$ satisfies
  $f_\Phi(n(b)m(a)g) = \chi_V(a)|a|^{m}f_\Phi(g)$, i.e. $f_\Phi \in I(s_0, \chi_V)$; a two-line local computation
  ($\omega(n(b))$ does not move the value at $0$ since $Q(0) = 0$; $\omega(m(a))$ multiplies it by $\chi_V(a)|a|^m$).
* At a finite place $v$: the **height** $\|g\|_v = \max(|c|_v, |d|_v)$ of the bottom row (`htV`), with
  $\|n(b)m(a)g\|_v = |a|_v^{-1}\|g\|_v$ (`htV_borel`) and $\|gk\|_v = \|g\|_v$ for $k \in \mathrm{SL}_2(\mathcal O_v)$ (`htV_mul_int`);
  so $|a(g)|_v = \|g\|_v^{-1}$ is the Iwasawa $|a|$ without choosing a decomposition.
* **The standard section** (`secS`): $f_\Phi(g, s) = f_\Phi(g)\,\|g\|_v^{-(s - s_0)}$, $s \in \mathbb C$, with
  $f_\Phi(n(b)m(a)g, s) = \chi_V(a)|a|_v^{s+1}f_\Phi(g, s)$ (`secS_borel`) and $f_\Phi(g, s_0) = f_\Phi(g)$ (`secS_s₀`).
* For the lattice function $\varphi_v = \mathbf 1_{L_v}$, $L_v = \mathcal O_v^{2m}$: right $K_0(\mathfrak N_v)$-equivariance
  $f_{\varphi_v}(gk, s) = \chi_v(d_k)f_{\varphi_v}(g, s)$ (`secS_oneS_mul_K0`), from `weilRepV_K0`; $f_{\varphi_v}(1) = 1$.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 and §II.1 (the map $\Phi \mapsto f_\Phi$)
[unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Weil, Acta Math. 113 (1965),
§§ on the Siegel formula [unverified]; Bump (1997), §3.7 (induced representations of $\mathrm{SL}_2$) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.LocalK0
import QuadFormsKB.Weil.ProductFormulas

open IsDedekindDomain NumberField
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

open WeilRep WeilRep.LocalData

/-! ### The abstract section $f_\Phi(g) = (\omega(g)\Phi)(0)$ -/

section Abstract

variable {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} (hD : D.IsModel)
  {k : Type*} [Field k] (ι : k →+* K) {m : ℕ} (a : Fin (2 * m) → Kˣ)

/-- **The section attached to $\Phi \in S(V)$:** $f_\Phi(g) = (\omega(g)\Phi)(0)$ for $g \in \mathrm{SL}_2(k)$, where
$\omega$ = `weilRep` is the Weil representation of $V = \langle a_0, \dots, a_{2m-1}\rangle$ (0-based) in the Schrödinger
model. -/
@[kb "kudla1996" "§II.1 (the map $\\varphi \\mapsto \\lambda(\\varphi)(g) = (\\omega(g)\\varphi)(0)$) [unverified]"]
def sec (Φ : D.Sn (2 * m)) (g : SL(2, k)) : ℂ :=
  ((weilRep hD (a := a) ι g Φ : D.Sn (2 * m)) : (Fin (2 * m) → K) → ℂ) 0

lemma Qform_zero {n : ℕ} (b : Fin n → Kˣ) : Qform b (0 : Fin n → K) = 0 := by simp [Qform]

variable {hD ι a}

/-- $f_\Phi(n(b)g) = f_\Phi(g)$: $\omega(n(b))$ multiplies by $\psi(bQ(x))$, which is $1$ at $x = 0$. -/
theorem sec_nMat_mul (Φ : D.Sn (2 * m)) (b : k) (g : SL(2, k)) :
    sec hD ι a Φ (nMat b * g) = sec hD ι a Φ g := by
  simp only [sec, map_mul, Module.End.mul_apply, weilRep_nMat, opN_apply, opNf, Qform_zero, mul_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

/-- $f_\Phi(m(t)g) = \chi_V(t)|t|^mf_\Phi(g)$. -/
theorem sec_mMat_mul (Φ : D.Sn (2 * m)) (t : kˣ) (g : SL(2, k)) :
    sec hD ι a Φ (mMat t * g) = D.chiV a (ι t) * (D.md (ι t) : ℂ) ^ m * sec hD ι a Φ g := by
  have h0 : (fun i : Fin (2 * m) => ι (t : k) * (0 : Fin (2 * m) → K) i) = 0 := by funext i; simp
  simp only [sec, map_mul, Module.End.mul_apply, weilRep_mMat, opM_apply, opMf, Units.coe_map,
    MonoidHom.coe_ofClass, h0]

/-- **Item 1: $f_\Phi \in I(s_0, \chi_V)$**, $s_0 = n/2 - 1 = m - 1$:
$$f_\Phi(n(b)m(t)g) = \chi_V(t)\,|t|^{s_0+1}\,f_\Phi(g)\qquad(|t|^{s_0+1} = |t|^{m} = |t|^{n/2}).$$
Valid for every model of the local harmonic analysis (`LocalData.IsModel`), so at every finite place (`weilRepV`)
and at $\infty$ (`weilRepInf`). -/
@[kb "kudla1996" "§II.1, (1.2) ($\\lambda(\\varphi) \\in I(s_0, \\chi_V)$, $s_0 = m/2 - 1$ for $\\dim V = m$) [unverified]"]
theorem sec_borel (Φ : D.Sn (2 * m)) (b : k) (t : kˣ) (g : SL(2, k)) :
    sec hD ι a Φ (nMat b * mMat t * g) = D.chiV a (ι t) * (D.md (ι t) : ℂ) ^ m * sec hD ι a Φ g := by
  rw [mul_assoc, sec_nMat_mul, sec_mMat_mul]

/-- $f_\Phi(1) = \Phi(0)$. -/
@[simp] lemma sec_one (Φ : D.Sn (2 * m)) : sec hD ι a Φ 1 = (Φ : (Fin (2 * m) → K) → ℂ) 0 := by
  simp [sec]

/-- $f_\Phi(gh) = f_{\omega(h)\Phi}(g)$ (right translation is the action on $\Phi$). -/
lemma sec_mul (Φ : D.Sn (2 * m)) (g h : SL(2, k)) :
    sec hD ι a Φ (g * h) = sec hD ι a (weilRep hD (a := a) ι h Φ) g := by
  simp [sec, map_mul, Module.End.mul_apply]

/-- $f_\Phi(wn(b)) = \gamma_V\,c_B\int_V\Phi(x)\psi(bQ(x))\,d\mu(x)$, $c_B = \prod_i|2a_i|^{1/2}$ (`cB`): the function whose
Fourier transform in $b$ is the Whittaker integral. -/
theorem sec_wMat_nMat (Φ : D.Sn (2 * m)) (b : k) :
    sec hD ι a Φ (wMat * nMat b) = D.gammaV a * D.cB a *
      ∫ x, (D.ψ (ι b * Qform a x) : ℂ) * (Φ : (Fin (2 * m) → K) → ℂ) x ∂D.muN (2 * m) := by
  simp only [sec, map_mul, Module.End.mul_apply, weilRep_wMat, weilRep_nMat, opW_apply, opWf, opN_apply, opNf]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Bform, Pi.zero_apply, mul_zero, Finset.sum_const_zero, AddChar.map_zero_eq_one, Circle.coe_one,
    mul_one]

end Abstract

/-! ### Finite places: the height and the standard section -/

section Finite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **The height of $g$ at $v$:** $\|g\|_v = \max(|c|_v, |d|_v)$, the norm of the bottom row $(c, d)$ of
$g = \begin{pmatrix}a&b\\c&d\end{pmatrix}$. If $g = n(x)m(t)k$ with $k \in \mathrm{SL}_2(\mathcal O_v)$ then $\|g\|_v = |t|_v^{-1}$. -/
@[kb "bump1997" "§3.7 (the Iwasawa decomposition and $|a(g)|$) [unverified]"]
def htV (g : SL(2, Fv)) : ℝ := max ‖(g : Matrix (Fin 2) (Fin 2) Fv) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) Fv) 1 1‖

lemma htV_pos (g : SL(2, Fv)) : 0 < htV v g := by
  unfold htV
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) Fv) 1 0 = 0
  · exact lt_max_of_lt_right (norm_pos_iff.mpr (d_ne_zero_of_c_eq_zero hc))
  · exact lt_max_of_lt_left (norm_pos_iff.mpr hc)

/-- $\|n(b)m(t)g\|_v = |t|_v^{-1}\|g\|_v$. -/
theorem htV_borel (b : Fv) (t : (Fv)ˣ) (g : SL(2, Fv)) :
    htV v (nMat b * mMat t * g) = ‖(t : Fv)‖⁻¹ * htV v g := by
  have e10 : ((nMat b * mMat t * g : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 0 =
      ((t⁻¹ : (Fv)ˣ) : Fv) * (g : Matrix (Fin 2) (Fin 2) Fv) 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : ((nMat b * mMat t * g : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 1 =
      ((t⁻¹ : (Fv)ˣ) : Fv) * (g : Matrix (Fin 2) (Fin 2) Fv) 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [htV, htV, e10, e11, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
    mul_max_of_nonneg _ _ (inv_nonneg.mpr (norm_nonneg _))]

lemma htV_le_of_mul (g k : SL(2, Fv)) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ 1) :
    htV v (g * k) ≤ htV v g := by
  have key : ∀ j, ‖((g * k : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 j‖ ≤ htV v g := by
    intro j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) Fv) 1 0‖ * 1 := by gcongr; exact hk 0 j
        _ ≤ htV v g := by rw [mul_one]; exact le_max_left _ _
    · rw [norm_mul]
      calc _ ≤ ‖(g : Matrix (Fin 2) (Fin 2) Fv) 1 1‖ * 1 := by gcongr; exact hk 1 j
        _ ≤ htV v g := by rw [mul_one]; exact le_max_right _ _
  exact max_le (key 0) (key 1)

/-- **$\|gk\|_v = \|g\|_v$ for $k \in \mathrm{SL}_2(\mathcal O_v)$** (ultrametric inequality, applied to $k$ and $k^{-1}$). -/
theorem htV_mul_int (g k : SL(2, Fv)) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ 1) :
    htV v (g * k) = htV v g := by
  refine le_antisymm (htV_le_of_mul v g k hk) ?_
  have hk' : ∀ i j, ‖((k⁻¹ : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [hk]
  have := htV_le_of_mul v (g * k) k⁻¹ hk'
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- The section at a finite place, for the local Weil representation `weilRepV`. -/
def secV (Φ : (localDataV v).Sn (2 * m)) (g : SL(2, Fv)) : ℂ :=
  sec (K := Fv) (k := Fv) (isModel_V v) (RingHom.id Fv) a Φ g

/-- **The standard section** at a finite place: $f_\Phi(g, s) = f_\Phi(g)\,\|g\|_v^{-(s - s_0)}$, $s_0 = m - 1$, $s \in \mathbb C$.
It is the unique section of $I(s, \chi_V)$ whose restriction to $\mathrm{SL}_2(\mathcal O_v)$ is that of $f_\Phi$. -/
@[kb "kudla1996" "§II.1 (the standard section $\\Phi(s)$ extending $\\lambda(\\varphi)$) [unverified]"]
def secS (Φ : (localDataV v).Sn (2 * m)) (g : SL(2, Fv)) (s : ℂ) : ℂ :=
  secV v a Φ g * ((htV v g : ℝ) : ℂ) ^ (-(s - ((m : ℂ) - 1)))

lemma md_eq_norm (t : (Fv)ˣ) : (localDataV v).md (t : Fv) = ‖(t : Fv)‖ := modK_eq_norm v t.ne_zero

/-- **$f_\Phi(\cdot, s) \in I(s, \chi_V)$:** $f_\Phi(n(b)m(t)g, s) = \chi_V(t)\,|t|_v^{s+1}f_\Phi(g, s)$. -/
@[kb "kudla1996" "§II.1 [unverified]"]
theorem secS_borel (Φ : (localDataV v).Sn (2 * m)) (b : Fv) (t : (Fv)ˣ) (g : SL(2, Fv)) (s : ℂ) :
    secS v a Φ (nMat b * mMat t * g) s =
      (localDataV v).chiV a t * ((‖(t : Fv)‖ : ℝ) : ℂ) ^ (s + 1) * secS v a Φ g s := by
  have ht : 0 < ‖(t : Fv)‖ := norm_pos_iff.mpr t.ne_zero
  unfold secS secV
  rw [sec_borel, htV_borel]
  simp only [RingHom.id_apply, md_eq_norm]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr ht.le) (htV_pos v g).le,
    Complex.ofReal_inv, Complex.inv_cpow_eq_ite]
  have harg : (((‖(t : Fv)‖ : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne
  rw [ite_eq_right_iff.mpr (fun h => absurd h harg), ← Complex.cpow_neg, neg_neg]
  have hne : (((‖(t : Fv)‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast ht.ne'
  have : ((‖(t : Fv)‖ : ℝ) : ℂ) ^ (s + 1) = ((‖(t : Fv)‖ : ℝ) : ℂ) ^ m * ((‖(t : Fv)‖ : ℝ) : ℂ) ^ (s - ((m : ℂ) - 1)) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]; congr 1; ring
  rw [this]; ring

/-- At $s = s_0 = m - 1$ the standard section is $f_\Phi$. -/
@[simp] theorem secS_s₀ (Φ : (localDataV v).Sn (2 * m)) (g : SL(2, Fv)) :
    secS v a Φ g ((m : ℂ) - 1) = secV v a Φ g := by
  simp [secS]

/-- **Right $K_0(\mathfrak N_v)$-equivariance of the lattice section** (every finite place, dyadic included): for
$k \in \mathrm{SL}_2(\mathcal O_v)$ with lower-left entry in the local level (`LevelV`),
$f_{\varphi_v}(gk, s) = \chi_v(d_k)\,f_{\varphi_v}(g, s)$, $\varphi_v = \mathbf 1_{\mathcal O_v^{2m}}$. From `weilRepV_K0` and `htV_mul_int`. -/
@[kb "kudla1996" "§II.1 and §I.4 [unverified]"]
theorem secS_oneS_mul_K0 (hm : 0 < m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (g k : SL(2, Fv))
    (hint : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1)
    (hlev : LevelV v a ((k : Matrix (Fin 2) (Fin 2) Fv) 1 0)) (s : ℂ) :
    secS v a (oneS v m) (g * k) s = chiLoc v a ((k : Matrix (Fin 2) (Fin 2) Fv) 1 1) * secS v a (oneS v m) g s := by
  have hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ 1 := fun i j =>
    (Valued.toNormedField.norm_le_one_iff).mpr (hint i j)
  unfold secS secV
  rw [htV_mul_int v g k hk, sec_mul, show weilRep (isModel_V v) (a := a) (RingHom.id _) k (oneS v m) =
    weilRepV v a k (oneS v m) from rfl, weilRepV_K0 v a hm ha k hint hlev]
  simp only [sec, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- $f_{\varphi_v}(1, s) = \varphi_v(0) = 1$. -/
@[simp] lemma secS_oneS_one (s : ℂ) : secS v a (oneS v m) 1 s = 1 := by
  simp [secS, secV, htV, oneV, ptensor, Analysis.ballIndV]

end Finite

end QuadFormsKB.SiegelWeil
