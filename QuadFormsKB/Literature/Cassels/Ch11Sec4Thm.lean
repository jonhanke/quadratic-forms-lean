/-
# Cassels, Chapter 11, Theorem 4.1: $\mathcal S_\Gamma = g(I(\Gamma, \Delta))\,\mathcal S_\Delta$

**Layer:** $\mathbb Z$-lattices `Lat ℚ n` in $V = \mathbb Q^n$ with a regular form $Q$, $n \ge 3$; Cassels' index
$I(\Gamma, \Delta)$ = `casselsI` (`Ch11Sec4Index.lean`); the finite adelic orthogonal group `OAf Q` acting on lattices
(`latSMul`); Cassels' spinor genus = `SameProperSpinorGenus`.

Cassels' set $P^*$ (p. 216): (i) $2 \in P^*$; (ii) for $p \notin P^*$ the form induced on $\Lambda_p$ is integral with
unit determinant; and he takes $P = P^*$ for the group $G = R/ST$ ((4.4); the display is garbled, "$P = P^*$" is read
from the use of $P^*$ in the proof). The action $g\mathcal S_\Gamma$ of $g \in G$ on spinor genera is defined by (3.32)
(Lemma 3.5, Corollary): $g\mathcal S$ is the spinor genus of $\alpha\Gamma'$ for $\Gamma' \in \mathcal S$ with
$\Gamma'_p = \Lambda_p$ ($p \notin P$) and $\alpha_p \in O^+(V_p)$ ($p \in P$), $\alpha_p = 1$ ($p \notin P$), with
$\{\theta(\alpha_p)\}$ representing $g$. For $g = g(c)$ one may take $\theta(\alpha_p) = c\,(\mathbb Q_p^\times)^2$.

**Proves** Cassels' Theorem 4.1 (p. 217; proof pp. 220–221) in this unfolded form
(`sameProperSpinorGenus_latSMul_of_casselsI`): for $\Gamma, \Delta$ in the genus of $\Lambda$ with
$I(\Gamma, \Delta)$ prime to every $p \in P^*$, and $\alpha$ as above with $\theta(\alpha_p) = I(\Gamma, \Delta)$ for
$p \in P^*$, $\Gamma$ is in the spinor genus of $\alpha\Delta$, i.e. $\mathcal S_\Gamma = g(I(\Gamma, \Delta))\,
\mathcal S_\Delta$ (the hypothesis $\Delta_p = \Lambda_p$ off $P^*$ of (3.32) is not needed in this form).
*Proof:* by Lemma 4.4, Corollary, reduce to $I(\Gamma, \Delta) = q$ prime ($q \notin P^*$); the intermediate lattices
are in the genus (Lemma 4.1). Then $\Gamma_q = \beta_q\Delta_q$ with $\theta(\beta_q) = q$ (Lemma 4.5) and
$\Gamma_p = \Delta_p$ for $p \ne q$; conclude with Lemma 1.4 (iv), using $\theta(V) \ni q$ (Lemma 3.2) and
$\theta(\Delta_p) = U_p(\mathbb Q_p^\times)^2$ for $p \notin P^*$ (Lemma 3.3).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec4Chain
import QuadFormsKB.Literature.Cassels.Ch11Sec4Local
import QuadFormsKB.Literature.Cassels.Ch11Sec4
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} (Q : QuadForm ℚ n)

/-! ### Helpers: local indices and unimodularity -/

section IndexHelpers

variable {F : Type} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Two bases of the same local lattice have the same $\|\det\|$. -/
theorem norm_det_eq_of_locAct_std_eq (δ₁ δ₂ : GL (Fin N) Fv) (h : locAct v δ₁ (std v) = locAct v δ₂ (std v)) :
    ‖δ₁.val.det‖ = ‖δ₂.val.det‖ := by
  have hstd : locAct v (δ₁⁻¹ * δ₂) (std v) = std v := by rw [locAct_mul, ← h, locAct_inv_locAct]
  obtain ⟨H, hH⟩ := Tamagawa.exists_GL_o_of_locAct_std v _ hstd
  have e3 : ((H.val.det : 𝔬) : Fv) = (δ₁⁻¹ * δ₂).val.det := by
    rw [← hH, show ((H.val.det : 𝔬) : Fv) = algebraMap 𝔬 Fv H.val.det from rfl, RingHom.map_det]
    rfl
  have hU1 : ‖((H.val.det : 𝔬) : Fv)‖ = 1 := Tamagawa.norm_coe_unit v (H.isUnit.map Matrix.detMonoidHom)
  have hdet : δ₂.val.det = δ₁.val.det * (δ₁⁻¹ * δ₂).val.det := by
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel_left]
  rw [hdet, norm_mul, ← e3, hU1, mul_one]

/-- A lattice $L_v$ is a $\mathrm{GL}_N(F_v)$-translate of the standard lattice. -/
theorem exists_locAct_std_model (L : Lat F N) : ∃ γ : GL (Fin N) Fv, loc v L.1 = locAct v γ (std v) := by
  obtain ⟨A, hA⟩ := exists_isLocModel' v L
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap F Fv) A, ?_⟩
  rw [← hA.2, latOf, loc_glImage, loc_intVec]

/-- $\mathrm{locIndex}_v(L) = \|\det\gamma\|$ for every basis $\gamma$ of $L_v$. -/
theorem locIndex_eq_norm_det {L : Lat F N} {γ : GL (Fin N) Fv} (h : loc v L.1 = locAct v γ (std v)) :
    locIndex v L = ‖γ.val.det‖ := by
  obtain ⟨A, hA⟩ := exists_isLocModel' v L
  rw [locIndex_eq v hA.2]
  have h1 : loc v (latOf A) = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) := by
    rw [latOf, loc_glImage, loc_intVec]
  have := norm_det_eq_of_locAct_std_eq v _ _ (h1.symm.trans (hA.2.trans h))
  rw [← this]
  congr 1
  rw [RingHom.map_det]
  rfl

/-- Equal norms of nonzero elements of $F_v$ give equal valuations. -/
theorem valued_eq_of_norm_eq {x y : Fv} (hx : x ≠ 0) (hy : y ≠ 0) (h : ‖x‖ = ‖y‖) : Valued.v x = Valued.v y := by
  rw [LocalZeta.norm_eq_absNorm_pow v hx, LocalZeta.norm_eq_absNorm_pow v hy] at h
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  have hN1 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 1 := by exact_mod_cast h1
  have := zpow_right_injective₀ hN0 hN1 h
  rw [← WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hx), ← WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hy), this]

/-- Local isometries preserve the local index (for nondegenerate $Q$). -/
theorem locIndex_eq_of_orth (Q : QuadForm F N) (hQ : Q.Nondegenerate) {L M : Lat F N}
    {g : GL (Fin N) Fv} (hg : g ∈ orthGroup Q Fv) (h : locAct v g (loc v L.1) = loc v M.1) :
    locIndex v M = locIndex v L := by
  obtain ⟨γ, hγ⟩ := exists_locAct_std_model v L
  have hM : loc v M.1 = locAct v (g * γ) (std v) := by rw [← h, hγ, locAct_mul]
  rw [locIndex_eq_norm_det v hM, locIndex_eq_norm_det v hγ, Units.val_mul, det_mul, norm_mul]
  have h1 : ‖g.val.det‖ = 1 := by
    rcases Tamagawa.det_eq_one_or_neg_one Q hQ (⟨g, hg⟩ : orthGroup Q Fv) with h | h
    · simp only at h; rw [h, norm_one]
    · simp only at h; rw [h, norm_neg, norm_one]
  rw [h1, one_mul]

/-- If $L, M$ agree away from $v$ and have the same index, they have the same local index at $v$. -/
theorem locIndex_eq_of_loc_eq_ne {L M : Lat F N} (h : latIndex L = latIndex M)
    (hw : ∀ w, w ≠ v → loc w L.1 = loc w M.1) : locIndex v L = locIndex v M := by
  classical
  have hLM : ∀ w, locIndex w M = locIndex w L * (if w = v then locIndex v M / locIndex v L else 1) := by
    intro w
    by_cases hwv : w = v
    · subst hwv
      have e : (if w = w then locIndex w M / locIndex w L else 1) = locIndex w M / locIndex w L := by simp
      rw [e, mul_div_cancel₀ _ (locIndex_pos w L).ne']
    · simp only [hwv, ↓reduceIte, mul_one]
      obtain ⟨γ, hγ⟩ := exists_locAct_std_model w L
      rw [locIndex_eq_norm_det w hγ, locIndex_eq_norm_det w (hw w hwv ▸ hγ)]
  have hsupp : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 F) =>
      if w = v then locIndex v M / locIndex v L else 1).Finite :=
    (Set.finite_singleton v).subset fun w hw => by
      by_contra hne
      exact hw (by simp [Set.mem_singleton_iff.not.mp hne] )
  have key : latIndex M = latIndex L * (locIndex v M / locIndex v L) := by
    have hsingle : (∏ᶠ w : HeightOneSpectrum (𝓞 F), (if w = v then locIndex v M / locIndex v L else 1)) =
        locIndex v M / locIndex v L := by
      rw [finprod_eq_single _ v (fun w hwv => by simp only [hwv, ↓reduceIte])]
      simp
    unfold latIndex
    rw [finprod_congr hLM, finprod_mul_distrib (locIndex_hasFiniteMulSupport L) hsupp, hsingle]
  rw [← h] at key
  have hpos := latIndex_pos L
  have : locIndex v M / locIndex v L = 1 := by
    have := mul_left_cancel₀ hpos.ne' (key.symm.trans (mul_one _).symm)
    exact this
  rw [div_eq_one_iff_eq (locIndex_pos v L).ne'] at this
  exact this.symm

end IndexHelpers

/-- **Lattices in one genus have the same determinant** (`latIndex`), for a nondegenerate form (for $Q = 0$ every two
lattices are in one genus). -/
theorem latIndex_eq_of_sameGenus_of_nondeg (hQ : Q.Nondegenerate) {L M : Lat ℚ n}
    (h : SameGenus Q L.1 M.1) : latIndex L = latIndex M := by
  unfold latIndex
  refine finprod_congr fun v => ?_
  obtain ⟨g, hg, he⟩ := h v
  exact (locIndex_eq_of_orth v Q hQ hg he).symm

/-! ### Helpers: places, adelic elements, and the prime case -/

theorem natGen_injective' {v w : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w) : v = w :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem exists_place_natGen {q : ℕ} (hq : q.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v = q :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩,
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)⟩

/-- A natural number prime to $p_v$ is a unit in $F_v$. -/
theorem valued_natCast_eq_one' {v : HeightOneSpectrum (𝓞 ℚ)} {m : ℕ}
    (h : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ m) : Valued.v ((m : ℚ) : v.adicCompletion ℚ) = 1 := by
  have h1 := valued_algebraMap v (m : ℚ)
  rw [map_natCast] at h1
  rw [Rat.cast_natCast, h1]
  exact chain_val_natCast_eq_one v h

theorem loc_eq_of_ne_prime {X Y : Lat ℚ n} (hlat : latIndex X = latIndex Y) {q : ℕ} (hq : q.Prime)
    (hXY : casselsI X Y = q) {vq : HeightOneSpectrum (𝓞 ℚ)} (hvq : Rat.HeightOneSpectrum.natGenerator vq = q)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ vq) : loc w X.1 = loc w Y.1 := by
  refine (loc_eq_iff_not_dvd_casselsI hlat w).2 fun hd => hw (natGen_injective' ?_)
  rw [hXY] at hd
  rw [hvq]
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).1 hd

/-- Unimodularity transports along a local isometry. -/
theorem local_unimod_of_orth (v : HeightOneSpectrum (𝓞 ℚ)) {X Y : Lat ℚ n}
    {g : GL (Fin n) (v.adicCompletion ℚ)} (hg : g ∈ orthGroup Q (v.adicCompletion ℚ))
    (hXY : locAct v g (loc v X.1) = loc v Y.1)
    (hint : ∀ x ∈ loc v X.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v X.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = 1) :
    (∀ x ∈ loc v Y.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
    ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v Y.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = 1 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [← hXY] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change Valued.v (Q.evalIn (v.adicCompletion ℚ) (g.val *ᵥ y)) ≤ 1
    rw [evalIn_mulVec_of_mem Q hg]
    exact hint y hy
  · obtain ⟨γ, hγ, hd⟩ := hdet
    refine ⟨g * γ, by rw [← hXY, hγ, locAct_mul], ?_⟩
    have : locGram Q v (g * γ) = locGram Q v γ := by
      rw [locGram_mul]
      have hgg : locGram Q v g = Q.hessian.map (algebraMap ℚ (v.adicCompletion ℚ)) := (mem_orthGroup Q).mp hg
      rw [hgg]
      rfl
    rw [this]
    exact hd

/-- The adelic orthogonal element which is $\beta$ at $v_0$ and $1$ elsewhere. -/
def oafSingle (v₀ : HeightOneSpectrum (𝓞 ℚ)) (β : orthGroup Q (v₀.adicCompletion ℚ)) : OAf Q := by
  classical
  exact ⟨Function.update (fun w => (1 : orthGroup Q (w.adicCompletion ℚ))) v₀ β, by
    filter_upwards [Filter.eventually_cofinite_ne v₀] with w hw
    rw [Function.update_of_ne hw]
    exact (stdStab Q w).one_mem⟩

theorem oafSingle_self (v₀ : HeightOneSpectrum (𝓞 ℚ)) (β : orthGroup Q (v₀.adicCompletion ℚ)) :
    oafSingle Q v₀ β v₀ = β := by
  classical
  show Function.update (fun w => (1 : orthGroup Q (w.adicCompletion ℚ))) v₀ β v₀ = β
  exact Function.update_self ..

theorem oafSingle_ne (v₀ : HeightOneSpectrum (𝓞 ℚ)) (β : orthGroup Q (v₀.adicCompletion ℚ))
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₀) : oafSingle Q v₀ β w = 1 := by
  classical
  show Function.update (fun w => (1 : orthGroup Q (w.adicCompletion ℚ))) v₀ β w = 1
  exact Function.update_of_ne hw ..

/-- **The prime case of Theorem 4.1** (Cassels pp. 220–221): if $I(X, Y) = q$ is a prime outside $P$ and $X, Y$ are in
the genus of $L$, then $X$ is in the spinor genus of $\alpha Y$ for every $\alpha$ with $\theta(\alpha_p) = q$ ($p \in P$),
$\alpha_p = 1$ ($p \notin P$). -/
theorem sameProperSpinorGenus_prime_step (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat ℚ n)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P → (∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ Valued.v (locGram Q v γ).det = 1)
    {X Y : Lat ℚ n} (hX : SameGenus Q L.1 X.1) (hY : SameGenus Q L.1 Y.1) (hlat : latIndex X = latIndex Y)
    {q : ℕ} (hq : q.Prime) (hXY : casselsI X Y = q)
    (hqP : ∀ v ∈ P, ¬ Rat.HeightOneSpectrum.natGenerator v ∣ q)
    (α : OAf Q) (hα : ∀ v ∈ P, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
      spinorNorm Q (v.adicCompletion ℚ) (α v) = sqClassOf (((q : ℚ)) : v.adicCompletion ℚ))
    (hα1 : ∀ v, v ∉ P → α v = 1) :
    SameProperSpinorGenus Q X (latSMul Q α Y) := by
  have unimod : ∀ {Z : Lat ℚ n}, SameGenus Q L.1 Z.1 → ∀ v, v ∉ P →
      (∀ x ∈ loc v Z.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v Z.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = 1 := by
    intro Z hZ v hv
    obtain ⟨hLint, hLdet⟩ := hPunim v hv
    obtain ⟨g, hg, he⟩ := hZ v
    exact local_unimod_of_orth Q v hg he hLint hLdet
  obtain ⟨vq, hvq⟩ := exists_place_natGen hq
  have hvqP : vq ∉ P := fun h => hqP vq h (hvq ▸ dvd_rfl)
  have h2 : (2 : 𝓞 ℚ) ∉ vq.asIdeal := fun h => hvqP (hP2 vq h)
  obtain ⟨hYint, hYdet⟩ := unimod hY vq hvqP
  obtain ⟨hXint, -⟩ := unimod hX vq hvqP
  have hYX : casselsI Y X = q := (casselsI_comm hlat.symm).trans hXY
  have hp : Rat.HeightOneSpectrum.natGenerator vq ∣ casselsI Y X := by rw [hYX, hvq]
  have hp2 : ¬ Rat.HeightOneSpectrum.natGenerator vq ^ 2 ∣ casselsI Y X := by
    rw [hYX, hvq]
    intro hd
    have := Nat.le_of_dvd hq.pos hd
    nlinarith [hq.two_le]
  obtain ⟨β, hβrot, hβ, hβθ⟩ := exists_soSub_locAct_eq_of_casselsI Q hQ (by omega) hlat.symm vq h2 hp hp2
    hYint hXint hYdet
  obtain ⟨h, hh1, hh2⟩ : ∃ h : OAf Q, h vq = β ∧ ∀ w, w ≠ vq → h w = 1 :=
    ⟨oafSingle Q vq β, oafSingle_self Q vq β, fun w hw => oafSingle_ne Q vq β hw⟩
  have hrot_h : ∀ w, h w ∈ Tamagawa.soSub Q (w.adicCompletion ℚ) := by
    intro w
    by_cases hw : w = vq
    · subst hw; rw [hh1]; exact hβrot
    · rw [hh2 w hw]; exact (Tamagawa.soSub Q _).one_mem
  have hX_eq : X = latSMul Q h Y := by
    apply Lat.ext
    apply loc_injective X.2 (latSMul Q h Y).2
    intro w
    rw [loc_latSMul]
    by_cases hw : w = vq
    · subst hw; rw [hh1]; exact hβ.symm
    · rw [hh2 w hw]
      change loc w X.1 = locAct w 1 (loc w Y.1)
      rw [locAct_one]
      exact loc_eq_of_ne_prime hlat hq hXY hvq hw
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  obtain ⟨γ, hγrot, hγθ⟩ : ∃ γ ∈ Tamagawa.soSub Q ℚ, spinorNorm Q ℚ γ = sqClassOf (q : ℚ) := by
    have hmem : Units.mk0 (q : ℚ) hq0 ∈ spinorNormGroup Q hQ :=
      (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr (by simpa using hq.pos))
    obtain ⟨σ, hσ, hσθ⟩ := (mem_spinorNormGroup Q hQ).mp hmem
    exact ⟨σ, hσ, by rw [hσθ, sqClassOf_of_ne_zero hq0]⟩
  have hγloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), spinorNorm Q (w.adicCompletion ℚ) (orthMap Q _ γ) =
      sqClassOf ((q : ℚ) : w.adicCompletion ℚ) := by
    intro w
    rw [spinorNorm_orthMap_of hQ w γ hq0 hγθ, map_natCast, Rat.cast_natCast]
  have hone : ∀ K : Type, ∀ [Field K] [Algebra ℚ K] [CharZero K], spinorNorm Q K (1 : orthGroup Q K) = 1 :=
    fun K _ _ _ => map_one (spinorNormHom Q K hQ)
  have hαrot : ∀ w, α w ∈ Tamagawa.soSub Q (w.adicCompletion ℚ) := by
    intro w
    by_cases hw : w ∈ P
    · exact (hα w hw).1
    · rw [hα1 w hw]; exact (Tamagawa.soSub Q _).one_mem
  have hmain := (sameProperSpinorGenus_smul_iff Q hQ Y h α hrot_h hαrot).mpr ⟨γ, hγrot, fun w => ?_⟩
  · rw [← hX_eq] at hmain
    exact hmain
  by_cases hwP : w ∈ P
  · have hwq : w ≠ vq := fun e => hvqP (e ▸ hwP)
    refine ⟨1, ⟨(locStabV Q w Y).one_mem, (Tamagawa.soSub Q _).one_mem⟩, ?_⟩
    rw [(hα w hwP).2, hh2 w hwq, hγloc w, hone, mul_one, SqClass.mul_self]
  · by_cases hwq : w = vq
    · subst hwq
      refine ⟨1, ⟨(locStabV Q w Y).one_mem, (Tamagawa.soSub Q _).one_mem⟩, ?_⟩
      have hc : ((q : ℚ) : w.adicCompletion ℚ) = ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : w.adicCompletion ℚ) := by
        rw [← hvq]; exact Rat.cast_natCast _
      rw [hα1 w hwP, hh1, hβθ, hγloc w, hc, hone, one_mul, SqClass.mul_self]
    · have h2w : (2 : 𝓞 ℚ) ∉ w.asIdeal := fun h => hwP (hP2 w h)
      obtain ⟨hYint', δ, hδ, hδd⟩ := unimod hY w hwP
      have hqw : Valued.v ((q : ℚ) : w.adicCompletion ℚ) = 1 := by
        refine valued_natCast_eq_one' fun hd => hwq (natGen_injective' ?_)
        rw [hvq]
        exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).1 hd
      have hcne : ((q : ℚ) : w.adicCompletion ℚ) ≠ 0 := by
        intro h0; rw [h0, map_zero] at hqw; exact zero_ne_one hqw
      have hmem := (mem_localSpinorNormGroup_iff_of_unimodular Q w hQ h2w (by omega) Y δ hδ hYint' hδd
        (Units.mk0 _ hcne)).mpr ⟨_, hqw, (sqClassOf_of_ne_zero hcne).symm⟩
      obtain ⟨ρ, hρ, hρθ⟩ := (mem_localSpinorNormGroup Q hQ w Y).mp hmem
      refine ⟨ρ, hρ, ?_⟩
      rw [hρθ, hα1 w hwP, hh2 w hwq, hγloc w, hone, one_mul, one_mul, sqClassOf_of_ne_zero hcne]

/-! ### The adelic rotations of Theorem 4.1 and the induction along the chain -/

/-- The adelic rotations in the statement of Theorem 4.1 with $I(\Gamma, \Delta)$ replaced by $c$:
$\alpha_v \in O^+(V_v)$ with $\theta(\alpha_v) = c$ for $v \in P$, and $\alpha_v = 1$ for $v \notin P$. -/
def CasselsGood (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : ℕ) (α : OAf Q) : Prop :=
  (∀ v ∈ P, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
      spinorNorm Q (v.adicCompletion ℚ) (α v) = sqClassOf (((c : ℕ) : ℚ) : v.adicCompletion ℚ)) ∧
    ∀ v, v ∉ P → α v = 1

theorem cast_ne_zero_completion (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℕ} (hc : c ≠ 0) :
    ((c : ℚ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [Rat.cast_natCast]; exact Nat.cast_ne_zero.mpr hc

theorem CasselsGood.mem_spnPlus (hQ : Q.Nondegenerate) {P : Finset (HeightOneSpectrum (𝓞 ℚ))} {α : OAf Q}
    (h : CasselsGood Q P 1 α) : α ∈ spnPlusGroup Q := by
  have : α ∈ spinorKernelAf Q := by
    intro v
    by_cases hv : v ∈ P
    · rw [spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      refine ⟨?_, (soSub_iff_detHom Q _ (α v)).mp (h.1 v hv).1⟩
      rw [spinorNormHom_apply, (h.1 v hv).2]
      simp [sqClassOf_one]
    · rw [h.2 v hv]; exact (spinorKernel Q _).one_mem
  exact Subgroup.mem_sup_right this

theorem CasselsGood.split (hQ : Q.Nondegenerate) {P : Finset (HeightOneSpectrum (𝓞 ℚ))} {c₁ c₂ : ℕ}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) {α β : OAf Q} (hα : CasselsGood Q P (c₁ * c₂) α)
    (hβ : CasselsGood Q P c₂ β) : CasselsGood Q P c₁ (α * β⁻¹) := by
  refine ⟨fun v hv => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · exact (Tamagawa.soSub Q _).mul_mem (hα.1 v hv).1 ((Tamagawa.soSub Q _).inv_mem (hβ.1 v hv).1)
  · have e : (α * β⁻¹) v = α v * (β v)⁻¹ := rfl
    have e2 : spinorNorm Q (v.adicCompletion ℚ) (α v * (β v)⁻¹) =
        spinorNorm Q (v.adicCompletion ℚ) (α v) * (spinorNorm Q (v.adicCompletion ℚ) (β v))⁻¹ := by
      have := map_mul (spinorNormHom Q (v.adicCompletion ℚ) hQ) (α v) (β v)⁻¹
      rwa [map_inv] at this
    rw [e, e2, (hα.1 v hv).2, (hβ.1 v hv).2, SqClass.inv_eq, Nat.cast_mul, Rat.cast_mul,
      sqClassOf_mul (cast_ne_zero_completion v hc₁) (cast_ne_zero_completion v hc₂), mul_assoc,
      SqClass.mul_self, mul_one]
  · have e : (α * β⁻¹) v = α v * (β v)⁻¹ := rfl
    rw [e, hα.2 v hv, hβ.2 v hv]; simp

theorem exists_casselsGood (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {c : ℕ} (hc : c ≠ 0) : ∃ α : OAf Q, CasselsGood Q P c α := by
  classical
  have hex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ σ ∈ Tamagawa.soSub Q (v.adicCompletion ℚ),
      spinorNorm Q (v.adicCompletion ℚ) σ = sqClassOf ((c : ℚ) : v.adicCompletion ℚ) := fun v => by
    obtain ⟨σ, hσ, hσθ⟩ := exists_soSub_spinorNorm_eq_local Q hQ hn v (Units.mk0 _ (cast_ne_zero_completion v hc))
    exact ⟨σ, hσ, by rw [hσθ, sqClassOf_of_ne_zero (cast_ne_zero_completion v hc)]⟩
  choose σ hσ hσθ using hex
  let α : OAf Q := ⟨fun v => if v ∈ P then σ v else 1, by
    filter_upwards [P.finite_toSet.compl_mem_cofinite] with v hv
    have hvP : v ∉ P := by simpa using hv
    show (if v ∈ P then σ v else 1) ∈ stdStab Q v
    simp only [hvP, ↓reduceIte]
    exact (stdStab Q v).one_mem⟩
  have hα : ∀ v, α v = if v ∈ P then σ v else 1 := fun v => rfl
  refine ⟨α, fun v hv => ?_, fun v hv => ?_⟩
  · rw [hα]; simp only [hv, ↓reduceIte]; exact ⟨hσ v, hσθ v⟩
  · rw [hα]; simp only [hv, ↓reduceIte]

/-- The action of $O(V)(\mathbb A_f)$ preserves the spinor genus relation (normality of $O^+(V)J'_V$). -/
theorem sameProperSpinorGenus_smul_left (hQ : Q.Nondegenerate) (a : OAf Q) {X Y : Lat ℚ n}
    (h : SameProperSpinorGenus Q X Y) : SameProperSpinorGenus Q (latSMul Q a X) (latSMul Q a Y) := by
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨a * g * a⁻¹, (spnPlusGroup_normal Q hQ).conj_mem g hg a, ?_⟩
  change (a * g * a⁻¹) • (a • X) = a • (g • X)
  calc (a * g * a⁻¹) • (a • X) = (a * g) • (a⁻¹ • (a • X)) := mul_smul _ _ _
    _ = (a * g) • X := by rw [inv_smul_smul]
    _ = a • (g • X) := mul_smul _ _ _

/-- Classical integrality of a lattice in the genus of $L$ at a prime outside $P$. -/
theorem classical_int_of_genus (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P → (∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ Valued.v (locGram Q v γ).det = 1)
    {Z : Lat ℚ n} (hZ : SameGenus Q L.1 Z.1) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ P) :
    ∀ x ∈ loc v Z.1, ∀ y ∈ loc v Z.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ) := by
  obtain ⟨hLint, hLdet⟩ := hPunim v hv
  obtain ⟨g, hg, he⟩ := hZ v
  obtain ⟨hZint, -⟩ := local_unimod_of_orth Q v hg he hLint hLdet
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hP2 v h)
  intro x hx y hy
  rw [valued_two h2]
  exact qbil_le_one_of_int hZint hx hy

/-- **The genus is preserved along a prime step** (Cassels' Lemma 4.1 at the single prime of $I(X, Y)$). -/
theorem sameGenus_prime_step (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P → (∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ Valued.v (locGram Q v γ).det = 1)
    {X Y : Lat ℚ n} (hX : SameGenus Q L.1 X.1) (hlat : latIndex X = latIndex Y)
    {q : ℕ} (hq : q.Prime) (hXY : casselsI X Y = q)
    (hqP : ∀ v ∈ P, ¬ Rat.HeightOneSpectrum.natGenerator v ∣ q)
    (hYint : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v = q →
      ∀ x ∈ loc v Y.1, ∀ y ∈ loc v Y.1,
        Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) :
    SameGenus Q L.1 Y.1 := by
  obtain ⟨vq, hvq⟩ := exists_place_natGen hq
  refine SameGenus.trans Q hX (sameGenus_of_unimodular_of_loc_ne Q X Y fun w hw => ?_)
  have hwq : w = vq := by
    by_contra hne
    exact hw (loc_eq_of_ne_prime hlat hq hXY hvq hne)
  subst hwq
  have hwP : w ∉ P := fun h => hqP w h (hvq ▸ dvd_rfl)
  have h2 : (2 : 𝓞 ℚ) ∉ w.asIdeal := fun h => hwP (hP2 w h)
  obtain ⟨hLint, hLdet⟩ := hPunim w hwP
  obtain ⟨g, hg, he⟩ := hX w
  obtain ⟨hXint, hXdet⟩ := local_unimod_of_orth Q w hg he hLint hLdet
  have hYint' : ∀ x ∈ loc w Y.1, Valued.v (Q.evalIn (w.adicCompletion ℚ) x) ≤ 1 := by
    intro x hx
    have := hYint w hvq x hx x hx
    rwa [qbil_self, map_mul, valued_two h2, one_mul] at this
  refine ⟨h2, hXint, hYint', hXdet, ?_⟩
  obtain ⟨δ, hδ⟩ := exists_locAct_std_model w Y
  obtain ⟨γ, hγ, hγd⟩ := hXdet
  refine ⟨δ, hδ, ?_⟩
  have hn : ‖δ.val.det‖ = ‖γ.val.det‖ := by
    rw [← locIndex_eq_norm_det w hδ, ← locIndex_eq_norm_det w hγ]
    exact locIndex_eq_of_loc_eq_ne w hlat.symm fun u hu => (loc_eq_of_ne_prime hlat hq hXY hvq hu).symm
  have hv := valued_eq_of_norm_eq w (Matrix.isUnits_det_units δ).ne_zero (Matrix.isUnits_det_units γ).ne_zero hn
  rw [locGram_det, map_mul, map_pow, hv]
  rwa [locGram_det, map_mul, map_pow] at hγd

/-- **Cassels, Theorem 4.1** (Ch. 11, p. 217): *suppose that $n \ge 3$. Let $\Gamma, \Delta$ be in the genus of
$\Lambda$ and suppose that $I(\Gamma, \Delta)$ is not divisible by any $p \in P^*$. Then $\mathcal S_\Gamma =
g_0\mathcal S_\Delta$, where $\mathcal S_\Gamma, \mathcal S_\Delta$ are the spinor genera of $\Gamma, \Delta$ and $g_0
= g(I(\Gamma, \Delta))$ is the image of $I(\Gamma, \Delta)$ under (4.5).* Here $P$ is Cassels' $P^*$ (hypotheses
`hP2`, `hPunim`) and $g_0\mathcal S_\Delta$ is unfolded as in the module docstring: $\Gamma$ is in the spinor genus of
$\alpha\Delta$ for every $\alpha \in O(V)(\mathbb A_f)$ with $\alpha_p \in O^+(V_p)$,
$\theta(\alpha_p) = I(\Gamma, \Delta)\,(\mathbb Q_p^\times)^2$ ($p \in P$) and $\alpha_p = 1$ ($p \notin P$). -/
@[kb "cassels1978" "Ch. 11, Thm. 4.1, p. 217 (g₀𝒮_Δ unfolded via (3.32); P = P*)"]
theorem sameProperSpinorGenus_latSMul_of_casselsI (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat ℚ n)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P → (∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ Valued.v (locGram Q v γ).det = 1)
    {Γ Δ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1) (hΔ : SameGenus Q L.1 Δ.1)
    (hI : ∀ v ∈ P, ¬ Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Γ Δ)
    (α : OAf Q) (hα : ∀ v ∈ P, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
      spinorNorm Q (v.adicCompletion ℚ) (α v) = sqClassOf ((casselsI Γ Δ : ℚ) : v.adicCompletion ℚ))
    (hα1 : ∀ v, v ∉ P → α v = 1) :
    SameProperSpinorGenus Q Γ (latSMul Q α Δ) := by
  classical
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  have hlatΓΔ : latIndex Γ = latIndex Δ :=
    latIndex_eq_of_sameGenus_of_nondeg Q hQ (SameGenus.trans Q (SameGenus.symm Q hΓ) hΔ)
  have hint0 : ∀ {Z : Lat ℚ n}, SameGenus Q L.1 Z.1 → ∀ v ∈ {v : HeightOneSpectrum (𝓞 ℚ) |
      Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Γ Δ}, ∀ x ∈ loc v Z.1, ∀ y ∈ loc v Z.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ) := by
    intro Z hZ v hv
    exact classical_int_of_genus Q L P hP2 hPunim hZ (fun h => hI v h hv)
  obtain ⟨J, Λs, h0, hJ, hlat, hprime, hprod, hint⟩ := exists_casselsI_chain Q hlatΓΔ
    {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Γ Δ} (fun v h => h)
    (hint0 hΓ) (hint0 hΔ)
  have hqdvd : ∀ j : Fin J, casselsI (Λs j.castSucc) (Λs j.succ) ∣ casselsI Γ Δ := fun j => by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem (fun j : Fin J => casselsI (Λs j.castSucc) (Λs j.succ)) (Finset.mem_univ j)
  have hqP : ∀ j : Fin J, ∀ v ∈ P, ¬ Rat.HeightOneSpectrum.natGenerator v ∣
      casselsI (Λs j.castSucc) (Λs j.succ) := fun j v hv hd => hI v hv (hd.trans (hqdvd j))
  have hlatj : ∀ j : Fin J, latIndex (Λs j.castSucc) = latIndex (Λs j.succ) := fun j =>
    (hlat j.castSucc).trans (hlat j.succ).symm
  -- every lattice of the chain is in the genus of `L`
  have hgen : ∀ k (hk : k ≤ J), SameGenus Q L.1 (Λs ⟨k, by omega⟩).1 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have e : Λs ⟨0, by omega⟩ = Γ := h0
      rw [e]; exact hΓ
    | succ k ih =>
      intro hk
      have hkJ : k < J := hk
      let j : Fin J := ⟨k, hkJ⟩
      exact sameGenus_prime_step Q L P hP2 hPunim (X := Λs j.castSucc) (Y := Λs j.succ) (ih hkJ.le)
        (hlatj j) (hprime j) rfl (hqP j) (fun v hv x hx y hy =>
          hint j.succ v (show Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Γ Δ by rw [hv]; exact hqdvd j)
            x hx y hy)
  -- the products of the first `k` primes
  let qf : ℕ → ℕ := fun i => if h : i < J then casselsI (Λs ⟨i, by omega⟩) (Λs ⟨i + 1, by omega⟩) else 1
  have hqf_ne : ∀ i, qf i ≠ 0 := by
    intro i
    by_cases h : i < J
    · have : qf i = casselsI (Λs ⟨i, by omega⟩) (Λs ⟨i + 1, by omega⟩) := by simp only [qf, h, ↓reduceDIte]
      rw [this]
      exact (hprime ⟨i, h⟩).ne_zero
    · have : qf i = 1 := by simp only [qf, h, ↓reduceDIte]
      rw [this]; exact one_ne_zero
  let cf : ℕ → ℕ := fun k => ∏ i ∈ Finset.range k, qf i
  have hcf_ne : ∀ k, cf k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr fun i _ => hqf_ne i
  have hcJ : cf J = casselsI Γ Δ := by
    show ∏ i ∈ Finset.range J, qf i = _
    rw [← hprod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : qf i = casselsI (Λs ⟨i, by omega⟩) (Λs ⟨i + 1, by omega⟩) := by simp only [qf, i.2, ↓reduceDIte]
    rw [this]
    rfl
  have key : ∀ k (hk : k ≤ J) (β : OAf Q), CasselsGood Q P (cf k) β →
      SameProperSpinorGenus Q Γ (latSMul Q β (Λs ⟨k, by omega⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk β hβ
      have e : Λs ⟨0, by omega⟩ = Γ := h0
      have h1 : CasselsGood Q P 1 β := by simpa [cf] using hβ
      exact ⟨β, h1.mem_spnPlus Q hQ, by rw [e]⟩
    | succ k ih =>
      intro hk β hβ
      have hkJ : k < J := hk
      let j : Fin J := ⟨k, hkJ⟩
      have hqk : qf k = casselsI (Λs j.castSucc) (Λs j.succ) := by
        simp only [qf, hkJ, ↓reduceDIte]; rfl
      have hcs : cf (k + 1) = cf k * qf k := Finset.prod_range_succ _ _
      obtain ⟨αk, hαk⟩ := exists_casselsGood Q hQ hn P (hqf_ne k)
      have hβ' : CasselsGood Q P (cf k) (β * αk⁻¹) := by
        rw [hcs] at hβ
        exact hβ.split Q hQ (hcf_ne k) (hqf_ne k) hαk
      have h1 := ih hkJ.le (β * αk⁻¹) hβ'
      rw [hqk] at hαk
      have h2 : SameProperSpinorGenus Q (Λs j.castSucc) (latSMul Q αk (Λs j.succ)) :=
        sameProperSpinorGenus_prime_step Q hQ hn L P hP2 hPunim (hgen k hkJ.le)
          (hgen (k + 1) hk) (hlatj j) (hprime j) rfl (hqP j) αk hαk.1 hαk.2
      have h3 := sameProperSpinorGenus_smul_left Q hQ (β * αk⁻¹) h2
      have e : latSMul Q (β * αk⁻¹) (latSMul Q αk (Λs j.succ)) = latSMul Q β (Λs j.succ) := by
        change (β * αk⁻¹) • (αk • Λs j.succ) = β • Λs j.succ
        rw [← mul_smul, inv_mul_cancel_right]
      rw [e] at h3
      exact SameProperSpinorGenus.trans Q h1 h3
  have hfin := key J le_rfl α (by rw [hcJ]; exact ⟨hα, hα1⟩)
  have e : Λs ⟨J, by omega⟩ = Δ := hJ
  rwa [e] at hfin

end QuadFormsKB.Lattices
