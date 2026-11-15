/-
# Kitaoka 1993, Theorem 1.3.2 in characteristic $2$, and the full theorem

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, Theorem 1.3.2, p. 16, and the second claim of
its proof, pp. 17–18 (printed pages). The statement `Kitaoka.FqCount.Theorem132` is in `Ch1IsometryCount.lean`; the
case of odd $q$ is `theorem132_odd` (`Ch1IsometryCountProof.lean`).

**Proves**
* `isomCount_plane`: $r(A, W) = r'(2, w)$ for a regular plane $A$ (characteristic $2$);
* `theorem132_char2`: `Theorem132` for finite fields of characteristic $2$ (unconditional);
* `theorem132`: `Theorem132` (all finite fields; unconditional).

**Proof** (Kitaoka's induction on $\dim V$, splitting off a regular plane). In characteristic $2$ a regular space
has even dimension, and $V \cong A \perp V_1$ with $A$ a regular plane. By the fibration
(`isomCount_prod_eq`) $r(V, W) = \sum_\tau r(V_1, \tau(A)^\perp)$, and for each isometry $\tau : A \to W$,
$W \cong A \perp W_1$ with $W_1 = \tau(A)^\perp$ regular, $\chi(W_1) = \chi(A)\chi(W)$ and
$\chi(V_1 \perp W_1) = \chi(V \perp W)$ (`chiGen_plane_prod`; $W^{(-1)} = W$ in characteristic $2$). So every
summand is the same $r'(V_1, W_1)$ and $r(V, W) = r(A, W)\,r'(V_1, W_1) = r'(V, W)$ (`rForm_step_plane`). The value
$r(A, W)$ is computed in `Ch1Char2PlaneCount.lean`.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2PlaneCount
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2Algebra

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

/-! ### The three plane identities -/

theorem plane_hyp_identity {q : ℝ} (hq : 0 < q) (k : ℕ) {cW : ℝ} (hW : cW * cW = 1) :
    (zeroVal q (2 * k + 2) cW - 1) * q ^ (2 * k + 2 - 2) = rForm q 2 (2 * k + 2) cW (1 * cW) := by
  rw [rForm_two hq, zeroVal, show 2 * k + 2 - 2 = 2 * k by omega, show (2 * k + 2) / 2 = k + 1 by omega,
    show ((2 * k + 2 : ℕ) : ℤ) - 1 = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring,
    show (((k + 1 : ℕ) : ℤ) - 1) = ((k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
  have h1 : q ^ k ≠ 0 := pow_ne_zero _ hq.ne'
  rcases mul_self_eq_one_iff.mp hW with rfl | rfl <;> field_simp <;> ring

theorem plane_aniso_identity {q : ℝ} (hq : 0 < q) (k : ℕ) {cW : ℝ} (hW : cW * cW = 1) :
    q ^ (((2 * k + 2 : ℕ) : ℤ) - 1) * (1 - cW * q ^ (-(((2 * k + 2) / 2 : ℕ) : ℤ))) *
      (q * (q ^ (((2 * k + 2 - 2 : ℕ) : ℤ) - 1) * (1 - cW * q ^ (-(((2 * k + 2 - 2) / 2 : ℕ) : ℤ))))) =
      rForm q 2 (2 * k + 2) cW (-1 * cW) := by
  rw [rForm_two hq, show 2 * k + 2 - 2 = 2 * k by omega, show (2 * k + 2) / 2 = k + 1 by omega,
    show 2 * k / 2 = k by omega,
    show ((2 * k + 2 : ℕ) : ℤ) - 1 = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring]
  rcases k with _ | k
  · simp only [zpow_natCast, zpow_neg, zpow_one, pow_zero, mul_zero, Nat.cast_zero, zero_add, CharP.cast_eq_zero,
      zero_sub, Int.reduceNeg, zpow_neg_one]
    field_simp
    ring
  · rw [show ((2 * (k + 1) : ℕ) : ℤ) - 1 = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_natCast, zpow_neg]
    have h1 : q ^ (k + 1) ≠ 0 := pow_ne_zero _ hq.ne'
    rcases mul_self_eq_one_iff.mp hW with rfl | rfl <;> field_simp <;> ring

theorem plane_aniso_two_identity {q : ℝ} (hq : 0 < q) :
    q ^ (((2 : ℕ) : ℤ) - 1) * (1 - (-1) * q ^ (-((2 / 2 : ℕ) : ℤ))) * 2 = rForm q 2 (2 * 0 + 2) (-1) (-1 * -1) := by
  rw [rForm_two hq]
  simp only [zpow_neg, zpow_natCast, pow_zero]
  norm_num
  first
  | done
  | (field_simp; ring)

section Gen

variable {F : Type} [Field F] [Finite F] (hF : ringChar F = 2)
include hF

/-- **$r(A, W)$ for a regular plane** $A$ in characteristic $2$: $r(A, W) = r'(2, w)$ with
$\chi(A \perp W) = \chi(A)\chi(W)$. -/
theorem isomCount_plane {U W : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {QA : QuadraticForm F U} (hU : finrank F U = 2)
    (hA : (polarBilin QA).Nondegenerate) {QW : QuadraticForm F W} (hW : (polarBilin QW).Nondegenerate)
    (h2 : 2 ≤ finrank F W) :
    (isomCount QA QW : ℝ) = rForm (Nat.card F) 2 (finrank F W) (chiGen QW) (chiGen QA * chiGen QW) := by
  classical
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  obtain ⟨a, c, hAe⟩ := exists_binForm hF hU hA
  have hb2 : finrank F (F × F) = 2 := by simp
  have hbreg := binForm_nondegenerate hF a c
  rw [isomCount_congr_left QW hAe, chiGen_congr hA hAe]
  obtain ⟨m, hm⟩ := even_finrank_char2 hF QW hW
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hw : finrank F W = 2 * k + 2 := by omega
  have hcW : chiGen QW * chiGen QW = 1 := by
    rw [← _root_.sq]; exact chiGen_sq_of_even QW ⟨k + 1, hm⟩
  have hweven : Even (finrank F W) := ⟨k + 1, hm⟩
  by_cases hK : (binForm a c).Anisotropic
  · have ha : a ≠ 0 := by
      intro h
      have := hK (1, 0) (by simp [h])
      simp at this
    have hchiK : chiGen (binForm a c) = -1 := by rw [chiGen_plane hb2 hbreg, if_pos hK]
    rw [hchiK]
    by_cases hiso : ∃ z : W, z ≠ 0 ∧ QW z = 0
    · rw [isomCount_aniso_of_isotropic hF QW hW hiso hK, valCount_even hW hweven ha, hw]
      exact plane_aniso_identity hq k hcW
    · have hWa : QW.Anisotropic := by
        intro z hz
        by_contra h0
        exact hiso ⟨z, h0, hz⟩
      have hle := Kitaoka.finrank_le_two_of_anisotropic QW hWa
      have hk : k = 0 := by omega
      subst hk
      have hchiW : chiGen QW = -1 := by rw [chiGen_plane hw hW, if_pos hWa]
      rw [isomCount_aniso_aniso hF QW hW hw hWa hK, valCount_even hW hweven ha, hw, hchiW]
      exact plane_aniso_two_identity hq
  · have hiso : ∃ v : F × F, v ≠ 0 ∧ binForm a c v = 0 := by
      simp only [QuadraticMap.Anisotropic, not_forall] at hK
      obtain ⟨v, hv, hv0⟩ := hK
      exact ⟨v, hv0, hv⟩
    have hH1 := Radical.proposition122_plane _ hb2 hbreg hiso
    have hH0 := Radical.proposition122_plane _ hb2 (binForm_nondegenerate hF 0 0) ⟨(1, 0), by simp, by simp⟩
    have hchiK : chiGen (binForm a c) = 1 := by rw [chiGen_plane hb2 hbreg, if_neg hK]
    rw [hchiK, isomCount_congr_left QW (hH1.trans hH0.symm), isomCount_hyp hF QW hW,
      lemma131Gen QW (QuadraticForm.radical_eq_bot_of_nondegenerate QW hW), hw]
    exact plane_hyp_identity hq k hcW

/-- A regular space of positive dimension in characteristic $2$ contains a regular plane: an isometry from some
`binForm a c`. -/
theorem exists_planeIso {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {QV : QuadraticForm F V} (hV : (polarBilin QV).Nondegenerate) (hpos : 0 < finrank F V) :
    ∃ a c : F, Nonempty (IsoT (binForm a c) QV) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  obtain ⟨w, hw⟩ : ∃ w, polar QV v w ≠ 0 := by
    by_contra! h
    exact hv ((QuadraticForm.nondegenerate_polarBilin_iff QV).mp hV v h)
  have hvw : polar QV v ((polar QV v w)⁻¹ • w) = 1 := by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw]
  exact ⟨QV v, QV ((polar QV v w)⁻¹ • w),
    ⟨(isoBinEquiv hF QV _ _).symm ⟨(v, (polar QV v w)⁻¹ • w), rfl, rfl, hvw⟩⟩⟩

/-- **Theorem 1.3.2 in characteristic $2$, general form**, by induction on $\dim V = 2(n + 1)$. -/
theorem theorem132_char2_gen (n : ℕ) : ∀ {V W : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (QV : QuadraticForm F V) (QW : QuadraticForm F W), (polarBilin QV).Nondegenerate →
    (polarBilin QW).Nondegenerate → finrank F V = 2 * (n + 1) → finrank F V ≤ finrank F W →
    (isomCount QV QW : ℝ) =
      rForm (Nat.card F) (2 * (n + 1)) (finrank F W) (chiGen QW) (chiGen (QV.prod (-QW))) := by
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  have hb2 : finrank F (F × F) = 2 := by simp
  induction n with
  | zero =>
    intro V W _ _ _ _ _ _ QV QW hQV hQW hV hvw
    rw [neg_form_char2 hF]
    obtain ⟨a, c, ⟨τ⟩⟩ := exists_planeIso hF hQV (by omega)
    have hbreg := binForm_nondegenerate hF a c
    obtain ⟨he, hd, hreg⟩ := perpRange_split hbreg τ
    have hV1 : Subsingleton (perpRange QV τ.1) := by
      rw [← Module.finrank_zero_iff (R := F)]
      omega
    have : Unique (perpRange QV τ.1) := uniqueOfSubsingleton 0
    have hL : ((binForm a c).prod (QV.comp (perpRange QV τ.1).subtype)).Equivalent (binForm a c) :=
      ⟨{ toLinearEquiv := LinearEquiv.prodUnique, map_app' := fun p => by
          obtain ⟨x, y⟩ := p
          rw [Subsingleton.elim y 0]
          simp [QuadraticMap.prod_apply] }⟩
    have hVb : QV.Equivalent (binForm a c) := he.symm.trans hL
    rw [isomCount_congr_left QW hVb, isomCount_plane hF hb2 hbreg hQW (by omega),
      chiGen_congr (QuadraticForm.nondegenerate_polarBilin_prod hQV hQW) (hVb.prod (QuadraticMap.Equivalent.refl QW)),
      chiGen_plane_prod hF hb2 hbreg hQW]
  | succ n ih =>
    intro V W _ _ _ _ _ _ QV QW hQV hQW hV hvw
    rw [neg_form_char2 hF]
    obtain ⟨a, c, ⟨τ⟩⟩ := exists_planeIso hF hQV (by omega)
    have hbreg := binForm_nondegenerate hF a c
    obtain ⟨he, hd, hreg⟩ := perpRange_split hbreg τ
    set V1 := perpRange QV τ.1
    set QV1 := QV.comp V1.subtype
    have hV1reg : (polarBilin QV1).Nondegenerate := hreg hQV
    have hV1dim : finrank F V1 = 2 * (n + 1) := by rw [hb2] at hd; omega
    have hsq := chiGen_plane_sq hb2 hbreg
    obtain ⟨m, hm⟩ := even_finrank_char2 hF QW hQW
    obtain ⟨k, hk⟩ : ∃ k, finrank F W = 2 * k + 2 := ⟨m - 1, by omega⟩
    have hcW : chiGen QW * chiGen QW = 1 := by
      rw [← _root_.sq]; exact chiGen_sq_of_even QW ⟨m, hm⟩
    -- the common value of the fibres
    have hR : ∀ σ : IsoT (binForm a c) QW, (isomCount QV1 (QW.comp (perpRange QW σ.1).subtype) : ℝ) =
        rForm (Nat.card F) (2 * (n + 1)) (2 * k) (chiGen (binForm a c) * chiGen QW) (chiGen (QV.prod QW)) := by
      intro σ
      obtain ⟨heW, hdW, hregW⟩ := perpRange_split hbreg σ
      have hW1reg := hregW hQW
      rw [hb2] at hdW
      rw [ih QV1 _ hV1reg hW1reg hV1dim (by omega), neg_form_char2 hF,
        show finrank F (perpRange QW σ.1) = 2 * k by omega]
      -- $\chi(W) = \chi(A)\chi(W_1)$
      have hchiW : chiGen QW = chiGen (binForm a c) * chiGen (QW.comp (perpRange QW σ.1).subtype) := by
        rw [← chiGen_congr (QuadraticForm.nondegenerate_polarBilin_prod hbreg hW1reg) heW,
          chiGen_plane_prod hF hb2 hbreg hW1reg]
      have hchiW1 : chiGen (QW.comp (perpRange QW σ.1).subtype) = chiGen (binForm a c) * chiGen QW := by
        rw [hchiW, ← mul_assoc, hsq, one_mul]
      -- $\chi(V \perp W) = \chi(V_1 \perp W_1)$
      have hregV1W1 := QuadraticForm.nondegenerate_polarBilin_prod hV1reg hW1reg
      have e : (QV.prod QW).Equivalent ((binForm a c).prod ((binForm a c).prod
          (QV1.prod (QW.comp (perpRange QW σ.1).subtype)))) :=
        (he.symm.prod heW.symm).trans
          ⟨((QuadraticForm.Witt.prodAssoc _ _ _).trans
            ((QuadraticMap.IsometryEquiv.refl _).prod
              (((QuadraticForm.Witt.prodAssoc _ _ _).symm.trans
                ((QuadraticMap.IsometryEquiv.prodComm _ _).prod (QuadraticMap.IsometryEquiv.refl _))).trans
                (QuadraticForm.Witt.prodAssoc _ _ _))))⟩
      have hchiVW : chiGen (QV.prod QW) = chiGen (QV1.prod (QW.comp (perpRange QW σ.1).subtype)) := by
        rw [chiGen_congr (QuadraticForm.nondegenerate_polarBilin_prod hQV hQW) e,
          chiGen_plane_prod hF hb2 hbreg (QuadraticForm.nondegenerate_polarBilin_prod hbreg hregV1W1),
          chiGen_plane_prod hF hb2 hbreg hregV1W1, ← mul_assoc, hsq, one_mul]
      rw [hchiW1, hchiVW]
    rw [isomCount_congr_left QW he.symm, isomCount_prod_eq hbreg QV1 QW _ hR,
      isomCount_plane hF hb2 hbreg hQW (by omega), hk,
      show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by ring]
    exact rForm_step_plane hq (by omega) (by omega) hsq hcW _

end Gen

/-- **Kitaoka 1993, Theorem 1.3.2** (p. 16) **in characteristic $2$**: for a finite field $K$ of characteristic $2$
with $q$ elements and regular quadratic forms $Q_V$ on $K^v$, $Q_W$ on $K^w$ with $1 \le v \le w$,
$r(V, W) = q^{vw - v(v+1)/2}(1 - \chi(W)q^{-w/2})(1 + \chi(V \perp W^{(-1)})q^{(v-w)/2})
\prod_{w-v+1 \le e \le w-1,\ e \text{ even}}(1 - q^{-e})$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.2, p. 16 (q even)"]
theorem theorem132_char2 (K : Type) [Field K] [Fintype K] (hK : ringChar K = 2) (v w : ℕ)
    (QV : QuadraticForm K (Fin v → K)) (QW : QuadraticForm K (Fin w → K)) (hQV : (polarBilin QV).Nondegenerate)
    (hQW : (polarBilin QW).Nondegenerate) (hv : 0 < v) (hvw : v ≤ w) :
    let q : ℝ := Fintype.card K
    (isomCount QV QW : ℝ) =
      q ^ ((v * w : ℤ) - (v * (v + 1) / 2 : ℕ)) * (1 - chiGen QW * q ^ (-(w : ℝ) / 2)) *
        (1 + chiGen (QV.prod (-QW)) * q ^ (((v : ℝ) - w) / 2)) *
        ∏ e ∈ (Finset.Icc (w - v + 1) (w - 1)).filter Even, (1 - q ^ (-(e : ℤ))) := by
  intro q
  obtain ⟨m, hm⟩ := even_finrank_char2 hK QV hQV
  rw [Module.finrank_fin_fun] at hm
  obtain ⟨n, rfl⟩ : ∃ n, v = 2 * (n + 1) := ⟨m - 1, by omega⟩
  have h := theorem132_char2_gen hK n QV QW hQV hQW (by simp) (by simpa using hvw)
  rw [h, Module.finrank_fin_fun, Nat.card_eq_fintype_card]
  rfl

/-- **Kitaoka 1993, Theorem 1.3.2** (p. 16), for every finite field: the statement `Theorem132` (with $v \ge 1$).
Unconditional: `theorem132_odd` for $q$ odd and `theorem132_char2` for $q$ even. -/
@[kb "kitaoka1993" "§1.3, Thm. 1.3.2, p. 16 (proof)"]
theorem theorem132 : Theorem132 := by
  intro K _ _ v w QV QW hQV hQW hv hvw
  by_cases hK : ringChar K = 2
  · exact theorem132_char2 K hK v w QV QW hQV hQW hv hvw
  · exact theorem132_odd K hK v w QV QW hQV hQW hv hvw

end QuadFormsKB.Kitaoka.FqCount
