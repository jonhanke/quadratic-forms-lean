/-
# $\mu_{\mathrm{Tam}}(K_{SO}(L))$ from arbitrary local bases

**Layer:** a number field $F$ (any class number), $Q_0$ nondegenerate over $\mathcal O_F$ of rank $n \ne 0, 2$, $L$ a lattice on $(F^n, Q_0)$.

Stage 1's `tamagawaKLat_eq_local` computes $\mu_{\mathrm{Tam}}(K_{SO}(L))$ from local bases $L_v = P_v\mathfrak o_v^n$ with $P_v$ **integral**. The
trace-zero lattice of a maximal order is not contained in $\mathcal O_F^3$ in general, so here the local bases are arbitrary
$P_v \in \mathrm{GL}_n(F_v)$ for which the local form $T_v = Q_0\circ P_v$ is integral:

* **`tamagawaKLat_eq_local_gen`**: $\mu(K_{SO}(L)) = |d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_v\tfrac12\beta_v(T_v, T_v)\,\|\det P_v\|^{n+1}$.

*Proof.* With $\varpi^kP_v$ integral, $\varpi^kL_v$ has the same stabilizer as $L_v$ (`stabLat_locAct_scalar`), $Q_0\circ\varpi^kP_v = \varpi^{2k}T_v$, and
$\beta(\varpi^{2k}T) = q^{kn(n+1)}\beta(T)$ (`localDensityForm_smul_pi_pow`) cancels $\|\det\varpi^kP_v\|^{n+1} = q^{-kn(n+1)}\|\det P_v\|^{n+1}$.

Source: Weil 1982, §2.2.1, §2.3; Kitaoka 1993, §5.6 [unverified].
-/
import QuadFormsKB.Tamagawa.LatticeChangeNF
import QuadFormsKB.Tamagawa.TernaryBadDVR
import QuadFormsKB.Tamagawa.TernaryReduction
import QuadFormsKB.Tamagawa.OrderLocalNF

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm WithZero

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$\beta(\varpi^jQ) = q^{jn(n+1)/2}\beta(Q)$.** -/
theorem localDensityForm_smul_pi_pow (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (j : ℕ) :
    DVR.localDensityForm (NF.π v ^ j • Q) (NF.π v ^ j • Q) (NF.π v) =
      ((DVR.q 𝔬 : ℝ) ^ (n * (n + 1) / 2)) ^ j * DVR.localDensityForm Q Q (NF.π v) := by
  have hπ := NF.irreducible_π v
  induction j with
  | zero =>
    have h1 : (NF.π v ^ 0 • Q) = Q := QuadForm.ext (by ext i j; simp [smul_coeff])
    rw [h1, pow_zero, one_mul]
  | succ j ih =>
    have hnd : (NF.π v ^ j • Q).Nondegenerate := by
      rw [QuadForm.Nondegenerate, show (NF.π v ^ j • Q).hessian = NF.π v ^ j • Q.hessian by
        ext a b; simp [hessian, smul_coeff]; ring, det_smul]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)) hQ
    rw [localDensityForm_smul_pi hπ hnd (fun i k => by simp [smul_coeff, pow_succ]; ring), ih, pow_succ]
    ring

theorem scalar_mul_comm (c : Fv) (g : GL (Fin n) Fv) (s : GL (Fin n) Fv) (hs : s.val = c • (1 : Matrix (Fin n) (Fin n) Fv)) :
    g * s = s * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **Scaling a local lattice by a central element does not change its stabilizer.** -/
theorem stabLat_locAct_scalar {G : Type*} [Group G] (ψ : G →* GL (Fin n) Fv) (c : Fv) (s : GL (Fin n) Fv)
    (hs : s.val = c • (1 : Matrix (Fin n) (Fin n) Fv)) (M : Submodule 𝔬 (Fin n → Fv)) :
    stabLat v ψ (locAct v s M) = stabLat v ψ M := by
  ext g
  change locAct v (ψ g) (locAct v s M) = locAct v s M ↔ locAct v (ψ g) M = M
  rw [← locAct_mul, scalar_mul_comm v c (ψ g) s hs, locAct_mul]
  constructor
  · intro h
    have := congrArg (locAct v s⁻¹) h
    rwa [locAct_inv_locAct, locAct_inv_locAct] at this
  · intro h; rw [h]

/-- The integral scaling $\varpi^kP$ of a local basis. -/
theorem exists_pi_pow_integral (P : Matrix (Fin n) (Fin n) Fv) :
    ∃ k : ℕ, ∀ i j, IsLocalization.IsInteger 𝔬 (algebraMap 𝔬 Fv (NF.π v) ^ k * P i j) := by
  classical
  have h := fun (p : Fin n × Fin n) => QuadFormsKB.QuatOrder.exists_pow_mul_isInteger_π (v := v) (P p.1 p.2)
  choose N hN using h
  refine ⟨Finset.univ.sup N, fun i j => ?_⟩
  have hle : N (i, j) ≤ Finset.univ.sup N := Finset.le_sup (f := N) (Finset.mem_univ _)
  obtain ⟨c, hc⟩ := hN (i, j)
  refine ⟨NF.π v ^ (Finset.univ.sup N - N (i, j)) * c, ?_⟩
  rw [map_mul, map_pow, hc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end Local

/-- **$\mu_{\mathrm{Tam}}(K_{SO}(L))$ from arbitrary local bases with integral local forms** (any number field, any lattice $L$, $n \ne 0, 2$):
if $L_v = P_v\mathfrak o_v^n$ with $P_v \in \mathrm{GL}_n(F_v)$ and $T_v$ an integral form with $T_v = Q_0\circ P_v$ over $F_v$, then
$$\mu(K_{SO}(L)) = |d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_v\tfrac12\beta_v(T_v, T_v)\,\|\det P_v\|^{n+1}.$$ -/
@[kb "weil1982" "§2.2.1, p. 14; §2.3, p. 21; §3.4 (μ(O(L_p)) ∝ α_p(L_p)|det L_p|^((n+1)/2)) [unverified]"]
theorem tamagawaKLat_eq_local_gen (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (L : Lat F n) (P : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (T : ∀ v : HeightOneSpectrum (𝓞 F), QuadForm (v.adicCompletionIntegers F) n)
    (hT : ∀ v, (T v).map (algebraMap _ (v.adicCompletion F)) =
      ((NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).compMat (P v).val)
    (hL : ∀ v, loc v L.1 = locAct v (P v) (std v)) :
    tamagawaKLat Q₀ L = (|(discr F : ℝ)|) ^ (-((n : ℝ) * (n - 1) / 4)) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
        ∏' v, (1 / 2 : ℝ) * DVR.localDensityForm (T v) (T v) (NF.π v) * ‖((P v).val.det)‖ ^ (n + 1) := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1)) (stdStab QF v)
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v L.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  have hr1 : ∀ v ∉ S, r v = 1 := fun v hv => by
    simp only [r]; rw [hS v hv, ← stdStab_eq_stabLat, relRatio_self]
  have hR : relRatio (locStab QF L) (locStab QF (stdLat F n)) = ∏ v ∈ S, r v := by
    rw [relRatio_symm', relRatio_locStab_eq_prod QF L S hS, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (relRatio_symm' _ _).symm
  -- the local factors
  have hfac : ∀ v, (1 / 2 : ℝ) * DVR.localDensityForm (T v) (T v) (NF.π v) * ‖((P v).val.det)‖ ^ (n + 1) =
      NF.siegelDensity v Q₀ Q₀ * r v := fun v => by
    have hπ := NF.irreducible_π v
    obtain ⟨k, hk⟩ := exists_pi_pow_integral v (P v).val
    choose c hc using hk
    set P' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := Matrix.of c
    have hP'map : P'.map (algebraMap _ (v.adicCompletion F)) =
        (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ k • (P v).val := by
      ext i j; simp [P', hc]
    have hdetP' : (algebraMap _ (v.adicCompletion F) P'.det) =
        (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ (k * n) * (P v).val.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hP'map, det_smul, Fintype.card_fin, ← pow_mul]
    have hπF : algebraMap _ (v.adicCompletion F) (NF.π v) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero
    have hPd : (P v).val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (P v).isUnit).ne_zero
    have hP'0 : P'.det ≠ 0 := fun h0 => by
      have := hdetP'
      rw [h0, map_zero] at this
      exact (mul_ne_zero (pow_ne_zero _ hπF) hPd) this.symm
    -- the form of `P'`
    have hform : (NF.Qp v Q₀).compMat P' = NF.π v ^ (2 * k) • T v := by
      apply NF.map_injective (IsFractionRing.injective _ (v.adicCompletion F))
      rw [← map_compMat, hP'map, compMat_smul_mat, map_smul_form, ← hT v, ← pow_mul, map_pow, mul_comm]
    have hTnd : (T v).Nondegenerate := by
      intro h0
      have h1 := congrArg (fun S : QuadForm (v.adicCompletion F) n => S.hessian.det) (hT v)
      simp only [hessian_compMat, det_mul, det_transpose] at h1
      rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
      have hQnd : ((NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).hessian.det ≠ 0 := by
        rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, NF.det_hessian_Qp]
        exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (NF.ι_ne_zero v hQ₀)
      exact mul_ne_zero (mul_ne_zero hPd hQnd) hPd h1.symm
    -- the local factor of `P'`
    have hlf := latLocalFactor_eq v Q₀ hQ₀ P' hP'0
    unfold latLocalFactor at hlf
    rw [hform, localDensityForm_smul_pi_pow v (T v) hTnd] at hlf
    -- the stabilizers
    have hsc : ((NF.π v ^ k) • (1 : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))).map
        (algebraMap _ (v.adicCompletion F)) = (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ k • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    have hglOf : glOf v P' hP'0 = glOf v ((NF.π v ^ k) • (1 : Matrix (Fin n) (Fin n) _))
        (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)) * P v := by
      apply Units.ext
      rw [Units.val_mul, glOf_val, glOf_val, hP'map, hsc, Matrix.smul_mul, Matrix.one_mul]
    have hstab : stabLat v (orthGroup QF (v.adicCompletion F)).subtype (locAct v (glOf v P' hP'0) (std v)) =
        stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1) := by
      rw [hglOf, locAct_mul, ← hL v]
      exact stabLat_locAct_scalar v _ _ _ (by rw [glOf_val, hsc]) _
    have hr : r v = relRatio (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))
          (locAct v (glOf v P' hP'0) (std v)))
        (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) (std v)) := by
      simp only [r]; rw [← hstab, relRatio_stab_eq_KL]
    rw [hr, ← hlf]
    -- `‖det P'‖ = q^{-kn} ‖det P‖`
    have hnorm : ‖((P'.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
        ((DVR.q (v.adicCompletionIntegers F) : ℝ)⁻¹) ^ (k * n) * ‖(P v).val.det‖ := by
      rw [show ((P'.det : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap _ (v.adicCompletion F) P'.det from rfl, hdetP', norm_mul, norm_pow]
      congr 2
      have := norm_coe_of_pow_dvd v (x := NF.π v) (e := 1) (by simp)
        (by rw [pow_succ, pow_one]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one
          ((mul_dvd_mul_iff_left hπ.ne_zero).1 (by simpa using h))))
      rw [pow_one] at this; exact this
    rw [hnorm]
    have hq : (0 : ℝ) < DVR.q (v.adicCompletionIntegers F) := by exact_mod_cast DVR.q_pos
    have hexp : n * (n + 1) / 2 * (2 * k) = k * n * (n + 1) := by
      have : n * (n + 1) % 2 = 0 := Nat.even_iff.1 (Nat.even_mul_succ_self n)
      have h2 : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero this)
      calc n * (n + 1) / 2 * (2 * k) = (n * (n + 1) / 2 * 2) * k := by ring
        _ = k * n * (n + 1) := by rw [h2]; ring
    have e1 : ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (n * (n + 1) / 2)) ^ (2 * k) =
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * n * (n + 1)) := by rw [← pow_mul, hexp]
    have e2 : ((((DVR.q (v.adicCompletionIntegers F) : ℝ))⁻¹) ^ (k * n) * ‖(P v).val.det‖) ^ (n + 1) =
        ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * n * (n + 1)))⁻¹ * ‖(P v).val.det‖ ^ (n + 1) := by
      rw [mul_pow, ← pow_mul, inv_pow]
    rw [e1, e2]
    field_simp
  have hrm : Multipliable r := multipliable_of_ne_finset_one hr1
  have hsm := multipliable_siegelDensity hn0 hn2 Q₀ hQ₀
  rw [show (fun v => (1 / 2 : ℝ) * DVR.localDensityForm (T v) (T v) (NF.π v) * ‖((P v).val.det)‖ ^ (n + 1)) =
      fun v => NF.siegelDensity v Q₀ Q₀ * r v from funext hfac, hsm.tprod_mul hrm, tprod_eq_prod hr1]
  unfold tamagawaKLat tamagawaK
  rw [hR]; ring

end QuadFormsKB.Tamagawa.LatChange
