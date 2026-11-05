/-
# The Siegel Eisenstein series at a general finite component $g_f \in \mathrm{SL}_2(\mathbb A_f)$
**Layer:** local bounds at each finite place $v$ of a number field $F$ (dyadic places included), then global over a totally
real number field $F$.

**Setting.** $Q = \sum_{i<n}a_ix_i^2$, $n = 2m$ (0-based indices), $a_i \in F^\times$. A *finite datum* is a family
$\Phi = (\Phi_v)_v$ of Schwartz–Bruhat functions $\Phi_v \in S(F_v^n)$ with $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for all but
finitely many $v$, so that $\Phi_f = \bigotimes_v\Phi_v \in S(\mathbb A_f^n)$ is a factorizable function. Examples: the lattice datum
$\mathbf 1_{\mathcal O_v^n}$ (`oneS`) and the transported lattice datum $\mathbf 1_{P^{-1}\mathcal O_v^n}$ (`latS`), which is the datum of a
non-diagonal form $Q_0$ with $Q_0\circ P = \langle a\rangle$. $f_v(g, s)$ is the standard section `secS` of $\Phi_v$ and
$\mathbb A_f$ = Mathlib's `FiniteAdeleRing (𝓞 F) F`; $g_v$ is the $v$-component of $g_f \in \mathrm{SL}_2(\mathbb A_f)$ (`locA`).

**Results (local).**
* `exists_norm_secS_le_Sn` (**the local bound for every Schwartz–Bruhat function**, every finite place, dyadic included): for
  $\Phi_v \in S(F_v^n)$ there is $C_v$ with $|f_v(g, s)| \le C_v\|g\|_v^{-(\operatorname{Re}s+1)}$ for all $g \in \mathrm{SL}_2(F_v)$ and $s$.
  *Proof:* Iwasawa, $g = n(x)m(t)k$ with $k = w^{-1}n(y)$ or $k = \begin{pmatrix}1&0\\y&1\end{pmatrix} = w^{-1}n(-y)w$; then
  $|f_\Phi(w^{-1}n(y))| = |\gamma_Vc_B\int\psi(yQ)\Phi| \le |\gamma_Vc_B|\int|\Phi|$ and the lower unipotent case is the same bound for
  $\omega(w)\Phi$. No compactness argument is needed, and the bound is uniform in $y$.
* `htV_le_mul_entSum`: $\|gk\|_v \le \|g\|_v\cdot\sum_{i,j}|k_{ij}|_v$, so $\|\gamma g\|_v \ge \|\gamma\|_v/M_v(g)$.

**Results (global).**
* `locA`, `finSecA`, `globalSecA`, `eisensteinA`: $E(g, s, \Phi) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma)\,f_f(\gamma g_f, s)$,
  $f_f(\gamma g_f, s) = \prod_vf_v(\gamma_vg_v, s)$, for every $g_f \in \mathrm{SL}_2(\mathbb A_f)$ and every finite datum; left $B(F)$-invariance
  (`globalSecA_borel`), the Bruhat expansion (`eisensteinA_eq_bruhat`). At $g_f = 1$ it is `eisensteinL` for the lattice datum and
  `eisenstein` for $\mathbf 1_{\mathcal O_v^n}$ (`eisensteinA_one_latS`, `eisensteinA_one_oneS`).
* `exists_norm_finSecA_le`: $|f_f(\gamma g_f, s)| \le K\,H_f(\gamma)^{-(\operatorname{Re}s+1)}$.
* **`eisensteinA_archSecS_converges`** (target 1): for $\operatorname{Re}s > 1$, $E((g_z, g_f), s, \Phi)$ converges absolutely over
  $B(F)\backslash\mathrm{SL}_2(F)$ and equals its Bruhat expansion, for every $g_f \in \mathrm{SL}_2(\mathbb A_f)$ and every finite datum.
* **`eisensteinL_archSecS_converges`** (target 2): the lattice series $E^P$ of a non-diagonal $Q_0$ converges absolutely for
  $\operatorname{Re}s > 1$.

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1
[unverified]; Bump (1997), §3.7 [unverified]; Godement (the convergence of Eisenstein series) [unverified].
-/
import QuadFormsKB.SiegelWeil.SiegelWeilLattice

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

/-! ### The local bound for every Schwartz–Bruhat function -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- $|f_\Psi(wn(b))| \le |\gamma_Vc_B|\int|\Psi|$ for every $\Psi \in S(F_v^n)$ and $b \in F_v$. -/
lemma norm_secV_wMat_nMat_le (Ψ : (localDataV v).Sn (2 * m)) (b : Fv) :
    ‖secV v a Ψ (wMat * nMat b)‖ ≤ ‖(localDataV v).gammaV a * (localDataV v).cB a‖ *
      ∫ x, ‖(Ψ : (Fin (2 * m) → Fv) → ℂ) x‖ ∂(localDataV v).muN (2 * m) := by
  unfold secV
  rw [sec_wMat_nMat, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
  congr 1; funext x
  rw [norm_mul, Circle.norm_coe, one_mul]

/-- $|f_\Psi(w^{-1}n(b))| = |f_\Psi(wn(b))|$ ($w^{-1} = m(-1)w$). -/
lemma norm_secV_wInv_nMat (Ψ : (localDataV v).Sn (2 * m)) (b : Fv) :
    ‖secV v a Ψ ((wMat : SL(2, Fv))⁻¹ * nMat b)‖ = ‖secV v a Ψ (wMat * nMat b)‖ := by
  rw [wMat_inv_eq, mul_assoc]
  unfold secV
  rw [sec_mMat_mul, norm_mul, norm_mul]
  simp only [RingHom.id_apply]
  have hmd : (localDataV v).md (((-1 : (Fv)ˣ) : Fv)) = 1 := by
    rw [md_eq_norm v (-1 : (Fv)ˣ)]; simp
  rw [norm_chiV_V, hmd]
  simp

/-- **The section is bounded on the Iwasawa factors, for every Schwartz–Bruhat function** (every finite place, dyadic included):
there is $C$ with $|f_\Phi(k)| \le C$ for $k = \begin{pmatrix}1&0\\y&1\end{pmatrix}$ and $k = w^{-1}n(y)$, for **all** $y \in F_v$. -/
theorem exists_bound_secV_Sn (Φ : (localDataV v).Sn (2 * m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fv,
      ‖secV v a Φ (lowerMat y)‖ ≤ C ∧ ‖secV v a Φ ((wMat : SL(2, Fv))⁻¹ * nMat y)‖ ≤ C := by
  set Ψ := weilRep (isModel_V v) (a := a) (RingHom.id Fv) (wMat : SL(2, Fv)) Φ
  set c := ‖(localDataV v).gammaV a * (localDataV v).cB a‖
  set I₁ := ∫ x, ‖(Φ : (Fin (2 * m) → Fv) → ℂ) x‖ ∂(localDataV v).muN (2 * m)
  set I₂ := ∫ x, ‖(Ψ : (Fin (2 * m) → Fv) → ℂ) x‖ ∂(localDataV v).muN (2 * m)
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ => norm_nonneg _
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨c * I₁ + c * I₂, by positivity, fun y => ⟨?_, ?_⟩⟩
  · have hk : lowerMat y = (wMat : SL(2, Fv))⁻¹ * nMat (-y) * wMat := by
      rw [← lowerMat_mul_wMat_inv, inv_mul_cancel_right]
    rw [hk]
    have e : secV v a Φ ((wMat : SL(2, Fv))⁻¹ * nMat (-y) * wMat) =
        secV v a Ψ ((wMat : SL(2, Fv))⁻¹ * nMat (-y)) := by
      unfold secV; rw [sec_mul]
    rw [e, norm_secV_wInv_nMat]
    exact (norm_secV_wMat_nMat_le v a Ψ (-y)).trans (le_add_of_nonneg_left (by positivity))
  · rw [norm_secV_wInv_nMat]
    exact (norm_secV_wMat_nMat_le v a Φ y).trans (le_add_of_nonneg_right (by positivity))

/-- **The local bound for every Schwartz–Bruhat function** (every finite place, dyadic included; Godement): for
$\Phi_v \in S(F_v^n)$ there is $C_v \ge 0$ with $|f_v(g, s)| \le C_v\,\|g\|_v^{-(\operatorname{Re}s+1)}$ for every $g \in \mathrm{SL}_2(F_v)$ and
$s \in \mathbb C$ ($f_v$ = `secS` of $\Phi_v$; no condition on $a_i$). -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; bump1997 §3.7 [unverified]"]
theorem exists_norm_secS_le_Sn (Φ : (localDataV v).Sn (2 * m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SL(2, Fv)) (s : ℂ), ‖secS v a Φ g s‖ ≤ C * htV v g ^ (-(s.re + 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_secV_Sn v a Φ
  refine ⟨C, hC0, fun g s => ?_⟩
  obtain ⟨x, t, y, hy, h | h⟩ := iwasawa v g
  · have hk := int_lowerMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC y).1 (Real.rpow_nonneg (htV_pos v _).le _)
  · have hk := int_wInv_nMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC y).2 (Real.rpow_nonneg (htV_pos v _).le _)

/-- The entry sum $M(k) = \sum_{i,j}|k_{ij}|_v$ of $k \in \mathrm{SL}_2(F_v)$. -/
def entSum (k : SL(2, Fv)) : ℝ := ∑ i, ∑ j, ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖

lemma entSum_nonneg (k : SL(2, Fv)) : 0 ≤ entSum v k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_le_entSum (k : SL(2, Fv)) (i j : Fin 2) : ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ entSum v k := by
  unfold entSum
  calc ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j‖ ≤ ∑ j', ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖(k : Matrix (Fin 2) (Fin 2) Fv) i j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ‖(k : Matrix (Fin 2) (Fin 2) Fv) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

lemma entSum_pos (k : SL(2, Fv)) : 0 < entSum v k := by
  exact (htV_pos v k).trans_le (max_le (norm_le_entSum v k 1 0) (norm_le_entSum v k 1 1))

/-- **$\|gk\|_v \le \|g\|_v\,M(k)$** (ultrametric inequality). -/
theorem htV_le_mul_entSum (g k : SL(2, Fv)) : htV v (g * k) ≤ htV v g * entSum v k := by
  have key : ∀ j, ‖((g * k : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 j‖ ≤ htV v g * entSum v k := by
    intro j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (le_max_left _ _) (norm_le_entSum v k 0 j) (norm_nonneg _) (htV_pos v g).le
    · rw [norm_mul]
      exact mul_le_mul (le_max_right _ _) (norm_le_entSum v k 1 j) (norm_nonneg _) (htV_pos v g).le
  exact max_le (key 0) (key 1)

/-- **$\|g\|_v \le \|gk\|_v\,M(k^{-1})$**: the height is bounded below along a right translate. -/
theorem htV_le_htV_mul (g k : SL(2, Fv)) : htV v g ≤ htV v (g * k) * entSum v k⁻¹ := by
  have := htV_le_mul_entSum v (g * k) k⁻¹
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

/-- **The local bound along a right translate**: $|f_v(\gamma k, s)| \le C_vM(k^{-1})^{\sigma+1}\|\gamma\|_v^{-(\sigma+1)}$ for $\sigma + 1 \ge 0$. -/
lemma norm_secS_mul_le {C : ℝ} (hC0 : 0 ≤ C) {Φ : (localDataV v).Sn (2 * m)}
    (hC : ∀ (g : SL(2, Fv)) (s : ℂ), ‖secS v a Φ g s‖ ≤ C * htV v g ^ (-(s.re + 1)))
    (γ k : SL(2, Fv)) {s : ℂ} (hs : 0 ≤ s.re + 1) :
    ‖secS v a Φ (γ * k) s‖ ≤ C * entSum v k⁻¹ ^ (s.re + 1) * htV v γ ^ (-(s.re + 1)) := by
  have hM := entSum_pos v k⁻¹
  have hγ := htV_pos v γ
  have hγk := htV_pos v (γ * k)
  have hle : htV v γ / entSum v k⁻¹ ≤ htV v (γ * k) := by
    rw [div_le_iff₀ hM]; exact htV_le_htV_mul v γ k
  have h1 : htV v (γ * k) ^ (-(s.re + 1)) ≤ (htV v γ / entSum v k⁻¹) ^ (-(s.re + 1)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hγ hM) hle (by linarith)
  rw [Real.div_rpow hγ.le hM.le, Real.rpow_neg hM.le, div_inv_eq_mul] at h1
  calc ‖secS v a Φ (γ * k) s‖ ≤ C * htV v (γ * k) ^ (-(s.re + 1)) := hC _ s
    _ ≤ C * (htV v γ ^ (-(s.re + 1)) * entSum v k⁻¹ ^ (s.re + 1)) := mul_le_mul_of_nonneg_left h1 hC0
    _ = _ := by ring

/-- At a good place the unramified section is $1$ on $\mathrm{SL}_2(\mathcal O_v)$, at every $s$. -/
lemma secS_oneS_eq_one_of_good (hg : IsGoodV v a) (k : SL(2, Fv))
    (hint : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1) (s : ℂ) :
    secS v a (oneS v m) k s = 1 := by
  unfold secS secV sec
  rw [show weilRep (isModel_V v) (a := a) (RingHom.id _) k (oneS v m) = weilRepV v a k (oneS v m) from rfl,
    weilRepV_oneS_of_good v a hg _ hint, htV_eq_one_of_int _ hint]
  simp [oneV, ptensor, ballIndV]

end Local

/-! ### The finite adelic component -/

section Adelic

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- The $v$-component $\mathbb A_f \to F_v$ (a ring homomorphism). -/
def evalV (v : HeightOneSpectrum (𝓞 F)) : AF →+* v.adicCompletion F where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The $v$-component** $g_f \mapsto g_v$, $\mathrm{SL}_2(\mathbb A_f) \to \mathrm{SL}_2(F_v)$. -/
abbrev locA (v : HeightOneSpectrum (𝓞 F)) : SL(2, AF) →* SL(2, v.adicCompletion F) :=
  Matrix.SpecialLinearGroup.map (evalV v)

lemma locA_apply (v : HeightOneSpectrum (𝓞 F)) (g : SL(2, AF)) (i j : Fin 2) :
    ((locA v g : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      ((g : Matrix (Fin 2) (Fin 2) AF) i j) v := rfl

/-- **$g_v \in \mathrm{SL}_2(\mathcal O_v)$ for all but finitely many $v$.** -/
lemma finite_not_int_locA (g : SL(2, AF)) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ i j,
      Valued.v (((locA v g : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1}.Finite := by
  have h := Set.finite_iUnion fun i : Fin 2 => Set.finite_iUnion fun j : Fin 2 =>
    FiniteAdeleRing.finite_valued_one_lt ((g : Matrix (Fin 2) (Fin 2) AF) i j)
  refine h.subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq, not_forall, not_le] at hv
  obtain ⟨i, j, hij⟩ := hv
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hij⟩⟩

lemma locA_inv_int {v : HeightOneSpectrum (𝓞 F)} {g : SL(2, AF)}
    (h : ∀ i j, Valued.v (((locA v g : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1) :
    ∀ i j, ‖(((locA v g)⁻¹ : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
  have hn : ∀ i j, ‖((locA v g : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 :=
    fun i j => (Valued.toNormedField.norm_le_one_iff).mpr (h i j)
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> exact h _ _

end Adelic

/-! ### The section and the Eisenstein series at $(g_\infty, g_f)$ -/

section Global

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

variable {m : ℕ} (a : Fin (2 * m) → Fˣ) (Φ : ∀ v : HeightOneSpectrum (𝓞 F), (localDataV v).Sn (2 * m))
  (hΦ : ∀ᶠ v in cofinite, Φ v = oneS v m) (gf : SL(2, FiniteAdeleRing (𝓞 F) F))

/-- **The finite part of the section at $\gamma g_f$**: $f_f(\gamma g_f, s) = \prod_{v<\infty}f_v(\gamma_vg_v, s)$, $f_v$ = `secS` of $\Phi_v$
(a finite product when $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for almost all $v$, `hasFiniteMulSupport_secSA`). -/
@[kb "kudla2008" "§1 (the standard section $\\Phi(s) = \\otimes_v\\Phi_v(s)$ on $G(\\mathbb A)$) [unverified]"]
def finSecA (γ : SL(2, F)) (s : ℂ) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), secS v (aV a v) (Φ v) (locSL v γ * locA v gf) s

/-- The finite set of places outside which $V$ is good, $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ and $g_v \in \mathrm{SL}_2(\mathcal O_v)$. -/
def badA : Set (HeightOneSpectrum (𝓞 F)) :=
  badPlaces a 1 ∪ {v | Φ v ≠ oneS v m} ∪ {v | ¬ ∀ i j,
    Valued.v (((locA v gf : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1}

include hΦ in
lemma badA_finite : (badA a Φ gf).Finite :=
  ((badPlaces_finite a 1).union hΦ).union (finite_not_int_locA gf)

lemma not_badA {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badA a Φ gf) :
    v ∉ badPlaces a 1 ∧ Φ v = oneS v m ∧ ∀ i j,
      Valued.v (((locA v gf : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1 := by
  simp only [badA, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

lemma int_mul {v : HeightOneSpectrum (𝓞 F)} {g k : SL(2, v.adicCompletion F)}
    (hg : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1)
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1) :
    ∀ i j, Valued.v (((g * k : SL(2, v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1 := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hg _ _) (hk _ _)

include hΦ in
lemma hasFiniteMulSupport_secSA (γ : SL(2, F)) (s : ℂ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      secS v (aV a v) (Φ v) (locSL v γ * locA v gf) s :=
  ((badPlaces_finite a γ).union (badA_finite a Φ hΦ gf)).subset fun v hv => by
    by_contra h
    simp only [Set.mem_union, not_or] at h
    obtain ⟨h1, h2, h3⟩ := not_badA a Φ gf h.2
    apply hv
    simp only
    rw [h2]
    exact secS_oneS_eq_one_of_good v _ (isGoodV_of_not_bad a h.1) _
      (int_mul (locSL_int_of_not_bad a h.1) h3) s

include hΦ in
/-- **The Borel law** of the finite section at $\gamma g_f$ (place by place, `secS_borel`). -/
theorem finSecA_borel (β : F) (t : Fˣ) (γ : SL(2, F)) (s : ℂ) :
    finSecA a Φ gf (nMat β * mMat t * γ) s = (∏ᶠ v, borelFactorV a t s v) * finSecA a Φ gf γ s := by
  unfold finSecA
  rw [← finprod_mul_distrib (hasFiniteMulSupport_borelFactorV a t s) (hasFiniteMulSupport_secSA a Φ hΦ gf γ s)]
  congr 1; funext v
  rw [map_mul, map_mul, locSL_nMat, locSL_mMat, mul_assoc, secS_borel]
  rfl

/-- **The global section at $(\gamma g_\infty, \gamma g_f)$**: $f(\gamma, s) = f_\infty(\gamma)\,f_f(\gamma g_f, s)$ ($f_\infty(\gamma)$ stands for
$f_\infty(\gamma g_\infty, s)$). -/
def globalSecA (fInf : SL(2, F) → ℂ) (s : ℂ) (γ : SL(2, F)) : ℂ := fInf γ * finSecA a Φ gf γ s

include hΦ in
/-- **Left $B(F)$-invariance** of the global section at a general $g_f$ (Hilbert reciprocity and the product formula,
`borelFactor_prod_eq_one`). -/
theorem globalSecA_borel {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) {b : SL(2, F)}
    (hb : b ∈ borel F) (γ : SL(2, F)) : globalSecA a Φ gf fInf s (b * γ) = globalSecA a Φ gf fInf s γ := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
  set u : Fˣ := Units.mk0 _ (a_ne_zero_of_c_eq_zero hb')
  set x : F := (b : Matrix (Fin 2) (Fin 2) F) 0 1 / (b : Matrix (Fin 2) (Fin 2) F) 0 0
  have hbe : b = nMat ((u : F) ^ 2 * x) * mMat u := by
    rw [← mMat_nMat]; exact eq_cell_of_c_eq_zero b hb'
  unfold globalSecA
  rw [hbe, hInf, finSecA_borel a Φ hΦ]
  have := borelFactor_prod_eq_one a u s
  linear_combination (fInf γ * finSecA a Φ gf γ s) * this

include hΦ in
/-- **The Siegel Eisenstein series at $g = (g_\infty, g_f)$**, $g_f \in \mathrm{SL}_2(\mathbb A_f)$ arbitrary:
$$E(g, s, \Phi) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma g_\infty, s)\prod_{v<\infty}f_v(\gamma_vg_v, s)$$
(`tsum`; $0$ if the series does not converge), for the finite datum $\Phi_f = \bigotimes_v\Phi_v$. -/
@[kb "kudla2008" "§1 ($E(g, s, \\Phi) = \\sum_{\\gamma\\in P(F)\\backslash G(F)}\\Phi(\\gamma g, s)$, $g \\in G(\\mathbb A)$) [unverified]; weil1965 Ch. II [unverified]"]
def eisensteinA {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) : ℂ :=
  ∑' q : BQuot F, Quotient.lift (globalSecA a Φ gf fInf s) (fun g g' h => by
    have h' : QuotientGroup.rightRel (borel F) g g' := h
    rw [QuotientGroup.rightRel_apply] at h'
    have := globalSecA_borel a Φ hΦ gf hInf h' g
    rw [inv_mul_cancel_right] at this
    exact this.symm) q

lemma finSecA_one_apply (h1 : ∀ v, (Φ v : (Fin (2 * m) → v.adicCompletion F) → ℂ) 0 = 1) (s : ℂ) :
    finSecA a Φ 1 1 s = 1 := by
  unfold finSecA
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  simp only [map_one, mul_one, secS, secV, sec_one, h1 v]
  simp [htV]

/-- **The Bruhat expansion** at a general $g_f$: $E(g, s, \Phi) = f(1, s) + \sum_{\beta\in F}f(wn(\beta), s)$ when the big-cell sum
converges. -/
@[kb "bump1997" "§3.7 [unverified]"]
theorem eisensteinA_eq_bruhat {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s)
    (hsum : Summable fun β : F => globalSecA a Φ gf fInf s (wMat * nMat β)) :
    eisensteinA a Φ hΦ gf hInf = globalSecA a Φ gf fInf s 1 + ∑' β : F, globalSecA a Φ gf fInf s (wMat * nMat β) := by
  unfold eisensteinA
  rw [← (bruhatEquiv (k := F)).tsum_eq]
  have hval : ∀ x : Unit ⊕ F, Quotient.lift (s := QuotientGroup.rightRel (borel F)) (globalSecA a Φ gf fInf s)
      (fun g g' h => by
        have h' : QuotientGroup.rightRel (borel F) g g' := h
        rw [QuotientGroup.rightRel_apply] at h'
        have := globalSecA_borel a Φ hΦ gf hInf h' g
        rw [inv_mul_cancel_right] at this
        exact this.symm) (bruhatEquiv (k := F) x) = globalSecA a Φ gf fInf s (bruhatRep x) := fun x => rfl
  simp only [hval]
  have h1 : HasSum (fun x : Unit ⊕ F => globalSecA a Φ gf fInf s (bruhatRep x))
      (globalSecA a Φ gf fInf s 1 + ∑' β : F, globalSecA a Φ gf fInf s (wMat * nMat β)) := by
    refine HasSum.sum ?_ hsum.hasSum
    have : (fun u : Unit => globalSecA a Φ gf fInf s (bruhatRep (Sum.inl u))) =
        fun _ => globalSecA a Φ gf fInf s 1 := by
      funext u; simp [bruhatRep]
    simp only [Function.comp_def, this]
    simp
  exact h1.tsum_eq

/-- **At $g_f = 1$ the adelic series of the lattice datum is $E^P$** (`eisensteinL`). -/
theorem eisensteinA_one_latS [IsTotallyReal F] (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0)
    (hΦP : ∀ᶠ v in cofinite, latS P hP v = oneS v m) {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) :
    eisensteinA a (latS P hP) hΦP 1 hInf = eisensteinL a P hP hInf := by
  unfold eisensteinA eisensteinL
  congr 1; funext q
  induction q using Quotient.inductionOn with
  | h g => show globalSecA a (latS P hP) 1 fInf s g = globalSecL a P hP fInf s g
           simp [globalSecA, globalSecL, finSecA, finSecL]

/-- The lattice datum is $\mathbf 1_{\mathcal O_v^n}$ outside the places dividing $\det P$. -/
lemma eventually_latS_eq [IsTotallyReal F] (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0) :
    ∀ᶠ v in cofinite, latS P hP v = oneS v m :=
  (detPlaces P hP).finite_toSet.subset fun v hv => by
    by_contra h; exact hv (latS_eq_oneS P hP h)

/-- The unramified datum. -/
lemma eventually_oneS_eq : ∀ᶠ v in cofinite, (fun v : HeightOneSpectrum (𝓞 F) => oneS v m) v = oneS v m :=
  Eventually.of_forall fun _ => rfl

/-- **At $g_f = 1$ the adelic series of $\mathbf 1_{\mathcal O_v^n}$ is `eisenstein`.** -/
theorem eisensteinA_one_oneS {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) :
    eisensteinA a (fun v => oneS v m) eventually_oneS_eq 1 hInf = eisenstein a hInf := by
  unfold eisensteinA eisenstein
  congr 1; funext q
  induction q using Quotient.inductionOn with
  | h g => show globalSecA a (fun v => oneS v m) 1 fInf s g = globalSec a fInf s g
           simp [globalSecA, globalSec, finSecA, finSec]

/-! ### The bound by the height and the convergence -/

lemma hasFiniteMulSupport_htVA (γ : SL(2, F)) (a' : Fin (2 * m) → Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => htV v (locSL v γ) :=
  (badPlaces_finite a' γ).subset fun v hv => by
    by_contra h
    exact hv (htV_eq_one_of_int _ (locSL_int_of_not_bad a' h))

include hΦ in
/-- **The finite part of the section at $\gamma g_f$ is bounded by the height of $\gamma$** (every finite place, dyadic included; any
finite datum, any $g_f$): for $\operatorname{Re}s \ge -1$ there is $K \ge 0$ with
$$|f_f(\gamma g_f, s)| \le K\,H_f(\gamma)^{-(\operatorname{Re}s+1)},\qquad H_f(\gamma) = \prod_{v<\infty}\|\gamma\|_v,$$
for every $\gamma \in \mathrm{SL}_2(F)$. *Proof:* `exists_norm_secS_le_Sn` and $\|\gamma_vg_v\|_v \ge \|\gamma\|_v/M(g_v^{-1})$ at the finitely many
places of `badA`; elsewhere the factor is $\|\gamma\|_v^{-(\operatorname{Re}s+1)}$ (`norm_secS_of_good`, `htV_mul_int`). -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; Weil (1965) [unverified]"]
theorem exists_norm_finSecA_le {s : ℂ} (hs : 0 ≤ s.re + 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ γ : SL(2, F), ‖finSecA a Φ gf γ s‖ ≤ K * (∏ᶠ v, htV v (locSL v γ)) ^ (-(s.re + 1)) := by
  classical
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SL(2, v.adicCompletion F)) (s : ℂ),
      ‖secS v (aV a v) (Φ v) g s‖ ≤ C * htV v g ^ (-(s.re + 1)) :=
    fun v => exists_norm_secS_le_Sn v (aV a v) (Φ v)
  choose C hC0 hC using hC
  set S := badA a Φ gf
  have hS := badA_finite a Φ hΦ gf
  set C' : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if v ∈ S then C v * entSum v (locA v gf)⁻¹ ^ (s.re + 1) else 1 with hC'
  have hC'0 : ∀ v, 0 ≤ C' v := fun v => by
    simp only [hC']; split_ifs
    · exact mul_nonneg (hC0 v) (Real.rpow_nonneg (entSum_nonneg v _) _)
    · exact zero_le_one
  have hC'fin : Function.HasFiniteMulSupport C' :=
    hS.subset fun v hv => by
      by_contra h
      exact hv (show (if v ∈ S then C v * entSum v (locA v gf)⁻¹ ^ (s.re + 1) else 1) = 1 from
        ite_eq_right_iff.mpr fun h' => absurd h' h)
  refine ⟨∏ᶠ v, C' v, finprod_nonneg hC'0, fun γ => ?_⟩
  have hle : ∀ v, ‖secS v (aV a v) (Φ v) (locSL v γ * locA v gf) s‖ ≤
      C' v * htV v (locSL v γ) ^ (-(s.re + 1)) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hC', hv, ite_true]
      exact norm_secS_mul_le v (aV a v) (hC0 v) (hC v) _ _ hs
    · simp only [hC', hv, ite_false, one_mul]
      obtain ⟨h1, h2, h3⟩ := not_badA a Φ gf hv
      rw [h2, norm_secS_of_good v (aV a v) (isGoodV_of_not_bad a (γ := 1) h1),
        htV_mul_int v _ _ fun i j => (Valued.toNormedField.norm_le_one_iff).mpr (h3 i j)]
  have hH := hasFiniteMulSupport_htVA γ a
  have hHr : Function.HasFiniteMulSupport fun v => htV v (locSL v γ) ^ (-(s.re + 1)) :=
    hH.subset fun v hv h => hv (by simp only at h ⊢; rw [h, Real.one_rpow])
  have hsec := hasFiniteMulSupport_secSA a Φ hΦ gf γ s
  have hnsec : Function.HasFiniteMulSupport fun v => ‖secS v (aV a v) (Φ v) (locSL v γ * locA v gf) s‖ :=
    hsec.subset fun v hv h => hv (by simp only at h ⊢; rw [h, norm_one])
  unfold finSecA
  rw [cvNorm_finprod hsec, ← cvFinprod_rpow hH (fun v => (htV_pos v _).le), ← finprod_mul_distrib hC'fin hHr]
  exact cvFinprod_le hnsec (hC'fin.mul hHr) (fun v => norm_nonneg _) hle

end Global

section Convergence

open HilbertModular QuadFormsKB.Lattices NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

variable {m : ℕ}

/-- **The big-cell majorant**: if a function $\varphi$ on $\mathrm{SL}_2(F)$ satisfies $|\varphi(\gamma)| \le K\,H_f(\gamma)^{-(\sigma+1)}$, $\sigma = \operatorname{Re}s > 1$, then
$u \mapsto f_\infty(wn(u)g_z, s)\varphi(wn(u))$ is absolutely summable over $F$ ($f_\infty$ = `archSecS`). This is the argument of
`summable_norm_globalSec_archSecS` (the product formula through the reduced vectors, and the Hilbert Eisenstein majorant
`exists_summable_bound_rpow`), stated for an arbitrary finite part. -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; Kudla (2008), §1 [unverified]"]
theorem summable_norm_archSecS_mul (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re)
    (φ : SL(2, F) → ℂ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ γ : SL(2, F), ‖φ γ‖ ≤ K * (∏ᶠ v, htV v (locSL v γ)) ^ (-(s.re + 1))) :
    Summable fun u : F => ‖archSecS m z s (wMat * nMat u) * φ (wMat * nMat u)‖ := by
  set α := s.re + 1 with hα
  have hα0 : 0 < α := by linarith
  have hrep : ∀ C : ClassGroup (𝓞 F), ∃ e : 𝓞 F, e ∈ repIdeal C ∧ e ≠ 0 :=
    fun C => Submodule.exists_mem_ne_zero_of_ne_bot (repIdeal_ne_bot C)
  choose e he he0 using hrep
  set E : ℝ := ∑ C, normAbs (ιO (e C)) with hE
  have heE : ∀ C, normAbs (ιO (e C)) ≤ E := fun C =>
    Finset.single_le_sum (f := fun C => normAbs (ιO (e C)))
      (fun C _ => Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ C)
  set W : F × F → ℂ := fun x => if IsRedVec x then 1 else 0 with hW
  obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  obtain ⟨h, hsum, hbd⟩ := exists_summable_bound_rpow (eisWeight_redInd (F := F)) (σ := α) (by linarith)
    (∑ v, |(z v).re| + 1) hB
  have hz : ∀ v, z v ∈ UpperHalfPlane.verticalStrip (∑ v, |(z v).re| + 1) B := fun v => ⟨by
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith, (hBv v).le⟩
  set Y := ∏ v, (z v).im ^ (α / 2) with hY
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun v _ => Real.rpow_nonneg (z v).im_pos.le _
  refine ((hsum.comp_injective rho_injective).mul_left (Y * K * E ^ α)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun u => ?_
  set c := redT u with hc
  have hc0 : c ≠ 0 := redT_ne_zero u
  set x : F × F := (c * 1, c * u) with hx
  have hred : IsRedVec x := isRedVec_redT u
  set C := cuspClass x.1 x.2
  have hmem : ιO (e C) ∈ cuspIdeal x.1 x.2 := by
    rw [hred.2]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨e C, he C, rfl⟩
  obtain ⟨r, s', hrs⟩ := mem_cuspIdeal_iff.mp hmem
  have he0' : ιO (e C) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr (he0 C)
  have hlow := div_le_finprod_htV u c (ιO (e C)) hc0 he0' ⟨r, s', by
    rw [hrs, Algebra.smul_def, Algebra.smul_def]; simp [x]⟩
  set H := ∏ᶠ v : HeightOneSpectrum (𝓞 F), htV v (locSL v (wMat * nMat u))
  have hNe : 0 < normAbs (ιO (e C)) := normAbs_pos he0'
  have hNc : 0 < normAbs c := normAbs_pos hc0
  have hE0 : 0 < E := hNe.trans_le (heE C)
  set D := ‖eisDen ((1 : F), u) (fun v => (z v : ℂ))‖
  have hD : 0 < D := norm_pos_iff.mpr (eisDen_one_ne_zero u z)
  have hDx : ‖eisDen (rho u).out (fun v => (z v : ℂ))‖ = D * normAbs c := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε, eisDen_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm, one_mul,
      show x = (c * ((1 : F), u).1, c * ((1 : F), u).2) from rfl, eisDen_smul_scalar, norm_mul, norm_prod, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hWo : ‖W (rho u).out‖ = 1 := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε]
    simp [hW, isRedVec_unit_smul_iff, hred]
  have hho := hbd z hz (rho u)
  rw [hWo, one_mul, hDx] at hho
  have hterm : ‖archSecS m z s (wMat * nMat u) * φ (wMat * nMat u)‖ ≤ Y * K * (D * H) ^ (-α) := by
    rw [norm_mul, norm_archSecS_wMat_nMat, Real.mul_rpow hD.le (le_trans (by positivity) hlow)]
    calc Y * D ^ (-α) * ‖φ (wMat * nMat u)‖ ≤ Y * D ^ (-α) * (K * H ^ (-α)) :=
          mul_le_mul_of_nonneg_left (hK _) (mul_nonneg hY0 (Real.rpow_nonneg hD.le _))
      _ = Y * K * (D ^ (-α) * H ^ (-α)) := by ring
  have hlow' : D * normAbs c / E ≤ D * H := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left hNc.le hNe (heE C)).trans hlow) hD.le
  have hpos : 0 < D * normAbs c / E := by positivity
  have hkey : (D * H) ^ (-α) ≤ E ^ α * (D * normAbs c) ^ (-α) := by
    refine (Real.rpow_le_rpow_of_nonpos hpos hlow' (by linarith)).trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) hE0.le, Real.rpow_neg hE0.le, div_inv_eq_mul, mul_comm]
  calc _ ≤ Y * K * (D * H) ^ (-α) := hterm
    _ ≤ Y * K * (E ^ α * (D * normAbs c) ^ (-α)) := mul_le_mul_of_nonneg_left hkey (mul_nonneg hY0 hK0)
    _ ≤ Y * K * E ^ α * h (rho u) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hho (mul_nonneg (mul_nonneg hY0 hK0) (Real.rpow_nonneg hE0.le _))

/-- Absolute summability over $B(F)\backslash\mathrm{SL}_2(F)$ from the big cell, for any left $B(F)$-invariant $f$. -/
lemma summable_bquot_of_bigCell (f : SL(2, F) → ℂ) (hf : ∀ b ∈ borel F, ∀ γ, f (b * γ) = f γ)
    (hsum : Summable fun u : F => ‖f (wMat * nMat u)‖) : Summable fun q : BQuot F => ‖f q.out‖ := by
  have hInv : ∀ x : Unit ⊕ F, f (bruhatEquiv (k := F) x).out = f (bruhatRep x) := by
    intro x
    have hrel : QuotientGroup.rightRel (borel F) (bruhatEquiv (k := F) x).out (bruhatRep x) :=
      Quotient.exact (Quotient.out_eq (bruhatEquiv (k := F) x))
    rw [QuotientGroup.rightRel_apply] at hrel
    have := hf _ hrel (bruhatEquiv (k := F) x).out
    rw [inv_mul_cancel_right] at this
    exact this.symm
  rw [← (bruhatEquiv (k := F)).summable_iff]
  simp only [Function.comp_def, hInv]
  have h1 : Summable fun u : Unit => ‖f (bruhatRep (Sum.inl u))‖ := (hasSum_fintype _).summable
  exact (HasSum.sum (f := fun x : Unit ⊕ F => ‖f (bruhatRep x)‖) h1.hasSum hsum.hasSum).summable

/-- **Target 1: absolute convergence at a general finite component.** For $F$ totally real, $Q = \sum_{i<n}b_ix_i^2$ totally positive over
$\mathcal O_F$ ($b_i \ne 0$), $n = 2m \ge 2$, any finite datum $\Phi_f = \bigotimes_v\Phi_v$ ($\Phi_v \in S(F_v^n)$, $= \mathbf 1_{\mathcal O_v^n}$ for almost all $v$),
any $g_f \in \mathrm{SL}_2(\mathbb A_f)$, $z \in \mathbb H^d$ and $\operatorname{Re}s > 1$, the Siegel Eisenstein series
$$E((g_z, g_f), s, \Phi) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma g_z, s)\,f_f(\gamma g_f, s)$$
converges absolutely and equals its Bruhat expansion $f(1) + \sum_{u\in F}f(wn(u))$ ($f_\infty$ = `archSecS`, the section of weight $m$). -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; Kudla (2008), §1 [unverified]; Godement [unverified]"]
theorem eisensteinA_archSecS_converges (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 F), (localDataV v).Sn (2 * m)) (hΦ : ∀ᶠ v in cofinite, Φ v = oneS v m)
    (gf : SL(2, FiniteAdeleRing (𝓞 F) F)) (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (Summable fun q : BQuot F => ‖globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s q.out‖) ∧
      eisensteinA (unitsOfInt b hb) Φ hΦ gf (isArchSection_archSecS b hb hbpos z s) =
        globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s 1 +
          ∑' u : F, globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s (wMat * nMat u) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_finSecA_le (unitsOfInt b hb) Φ hΦ gf (s := s) (by linarith)
  have hsum : Summable fun u : F => ‖globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s (wMat * nMat u)‖ :=
    summable_norm_archSecS_mul z hs (fun γ => finSecA (unitsOfInt b hb) Φ gf γ s) hK0 hK
  have hInv : ∀ b' ∈ borel F, ∀ γ, globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s (b' * γ) =
      globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s γ := fun b' hb' γ =>
    globalSecA_borel (unitsOfInt b hb) Φ hΦ gf (isArchSection_archSecS b hb hbpos z s) hb' γ
  exact ⟨summable_bquot_of_bigCell (globalSecA (unitsOfInt b hb) Φ gf (archSecS m z s) s) hInv hsum,
    eisensteinA_eq_bruhat (unitsOfInt b hb) Φ hΦ gf (isArchSection_archSecS b hb hbpos z s) hsum.of_norm⟩

/-- **Target 2: the lattice series $E^P$ of a non-diagonal form converges absolutely for $\operatorname{Re}s > 1$.** For $Q_0\circ P = \langle b\rangle$
($P \in M_n(\mathcal O_F)$, $\det P \ne 0$; e.g. from `exists_diag_global`), $b_i$ totally positive, $n = 2m \ge 2$, $z \in \mathbb H^d$ and
$\operatorname{Re}s > 1$, the series $E^P(g_z, s) = \sum_{B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma g_z, s)\,f_f^P(\gamma, s)$ of
$\Phi_v = \mathbf 1_{P^{-1}\mathcal O_v^n}$ converges absolutely and equals its Bruhat expansion. (At the places dividing $\det P$ the local bound
is `exists_norm_secS_le_Sn`.) -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisensteinL_archSecS_converges (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0)
    (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (Summable fun q : BQuot F => ‖globalSecL (unitsOfInt b hb) P hP (archSecS m z s) s q.out‖) ∧
      eisensteinL (unitsOfInt b hb) P hP (isArchSection_archSecS b hb hbpos z s) =
        archSecS m z s 1 + ∑' u : F, globalSecL (unitsOfInt b hb) P hP (archSecS m z s) s (wMat * nMat u) := by
  have e : ∀ γ, globalSecA (unitsOfInt b hb) (latS P hP) 1 (archSecS m z s) s γ =
      globalSecL (unitsOfInt b hb) P hP (archSecS m z s) s γ := fun γ => by
    simp [globalSecA, globalSecL, finSecA, finSecL]
  obtain ⟨h1, -⟩ := eisensteinA_archSecS_converges b hb hbpos (latS P hP) (eventually_latS_eq P hP) 1 z hs
  simp_rw [e] at h1
  obtain ⟨K, hK0, hK⟩ := exists_norm_finSecA_le (unitsOfInt b hb) (latS P hP) (eventually_latS_eq P hP) 1
    (s := s) (by linarith)
  have hsum : Summable fun u : F => ‖globalSecL (unitsOfInt b hb) P hP (archSecS m z s) s (wMat * nMat u)‖ := by
    have := summable_norm_archSecS_mul (m := m) z hs _ hK0 hK
    simpa [globalSecA, globalSecL, finSecA, finSecL] using this
  exact ⟨h1, eisensteinL_eq_bruhat _ P hP _ hsum.of_norm⟩

end Convergence

end QuadFormsKB.SiegelWeil
