/-
# The $\alpha$ transformation law: changes of basis, cocycle, scalars, the split reduction

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (every residue characteristic,
dyadic included).

**Proves** (for `AlphaLawAt`, the law $r(K(P\mathfrak o^N), K(\mathfrak o^N))\,\beta(Q_o) = \beta(Q_o\circ P)\,\|\det P\|^{N+1}$):
* `alphaLaw_mul_right`, `alphaLaw_conj`: invariance under $P \mapsto PV$ and $(Q_o, P) \mapsto (Q_o\circ U, U^{-1}P)$, $U, V \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$;
* `alphaLaw_mul` (**cocycle**): the law for $P_1$ and for $(Q_o\circ P_1, P_2)$ give the law for $P_1P_2$ (`relRatio_mul`);
* `localDensityForm_smul` (**scaling**): $\beta(sQ, sQ) = q^{\mathrm{ord}(s)N(N+1)/2}\,\beta(Q, Q)$ (counting: the condition at level
  $k + \mathrm{ord}\,s$ depends only on the class mod $\varpi^k$);
* `alphaLaw_scalar`: the law for $P = c\cdot 1$ ($K(c\Lambda) = K(\Lambda)$);
* `alphaLaw_of_split` (**the split reduction**, Hanke-style change of lattice): if $\Lambda_1 = P\mathfrak o^{n+1}$ contains a vector $z$
  that splits $\mathfrak o^{n+1}$ ($2Q(z) \mid B(z, \cdot)$), the law for $(Q_o, P)$ follows from the law in rank $n$ for the complements.

Sources: Weil 1982, §3.4 [unverified]; Hanke 2004, §3, Def. 3.1 and the maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLawSplit

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

section Moves

variable {N : ℕ}

theorem relRatio_KL_conj (Qv : QuadForm Fv N) (g : GL (Fin N) Fv) (Λ₁ Λ₂ : Submodule 𝔬 (Fin N → Fv)) :
    relRatio (KL v (Qv.compMat g.val) Λ₁) (KL v (Qv.compMat g.val) Λ₂) =
      relRatio (KL v Qv (locAct v g Λ₁)) (KL v Qv (locAct v g Λ₂)) := by
  rw [KL_locAct, KL_locAct, relRatio_map (MulAut.conj g).injective]

theorem glOf_mul (P₁ P₂ : Matrix (Fin N) (Fin N) 𝔬) (h₁ : P₁.det ≠ 0) (h₂ : P₂.det ≠ 0) (h₁₂ : (P₁ * P₂).det ≠ 0) :
    glOf v (P₁ * P₂) h₁₂ = glOf v P₁ h₁ * glOf v P₂ h₂ := by
  apply Units.ext
  rw [Units.val_mul, glOf_val, glOf_val, glOf_val, Matrix.map_mul]

theorem glOf_unit (V : Matrix (Fin N) (Fin N) 𝔬) (hV : IsUnit V.det) (hV' : V.det ≠ 0) :
    glOf v V hV' = Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) (Matrix.nonsingInvUnit V hV) := by
  apply Units.ext; rfl

theorem locAct_glOf_unit (V : Matrix (Fin N) (Fin N) 𝔬) (hV : IsUnit V.det) (hV' : V.det ≠ 0) :
    locAct v (glOf v V hV') (std v) = std v := by
  rw [glOf_unit v V hV hV']; exact locAct_map_std v _

theorem isometricGL_compMat (Q : QuadForm 𝔬 N) (V : Matrix (Fin N) (Fin N) 𝔬) (hV : IsUnit V.det) :
    Siegel.IsometricGL Q (Q.compMat V) :=
  ⟨Matrix.nonsingInvUnit V hV, fun x => by rw [eval_compMat]; rfl⟩

theorem norm_det_unit {V : Matrix (Fin N) (Fin N) 𝔬} (hV : IsUnit V.det) : ‖((V.det : 𝔬) : Fv)‖ = 1 :=
  norm_coe_unit v hV

theorem norm_det_mul (P₁ P₂ : Matrix (Fin N) (Fin N) 𝔬) :
    ‖(((P₁ * P₂).det : 𝔬) : Fv)‖ = ‖((P₁.det : 𝔬) : Fv)‖ * ‖((P₂.det : 𝔬) : Fv)‖ := by
  rw [det_mul]; push_cast; exact norm_mul _ _

/-- **Invariance under $P \mapsto PV$**, $V \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$ (same lattice, an equivalent Gram form). -/
theorem alphaLaw_mul_right (Qo : QuadForm 𝔬 N) (P V : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0)
    (hV : IsUnit V.det) (hPV : (P * V).det ≠ 0) : AlphaLawAt v Qo (P * V) hPV ↔ AlphaLawAt v Qo P hP := by
  have hV0 : V.det ≠ 0 := hV.ne_zero
  have hlat : locAct v (glOf v (P * V) hPV) (std v) = locAct v (glOf v P hP) (std v) := by
    rw [glOf_mul v P V hP hV0 hPV, locAct_mul, locAct_glOf_unit v V hV hV0]
  have hβ : localDensityForm (Qo.compMat (P * V)) (Qo.compMat (P * V)) (NF.π v) =
      localDensityForm (Qo.compMat P) (Qo.compMat P) (NF.π v) := by
    rw [← compMat_mul, ← localDensityForm_congr_left (isometricGL_compMat v _ V hV),
      ← localDensityForm_congr_right _ (isometricGL_compMat v _ V hV)]
  unfold AlphaLawAt
  rw [hlat, hβ, norm_det_mul, norm_det_unit v hV, mul_one]

/-- **Invariance under a change of basis of $\mathfrak o_\mathfrak p^N$**: $(Q_o, P) \mapsto (Q_o\circ U, U^{-1}P)$, $U \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$. -/
theorem alphaLaw_conj (Qo : QuadForm 𝔬 N) (U Uinv : Matrix (Fin N) (Fin N) 𝔬) (hU : IsUnit U.det)
    (hUU : U * Uinv = 1) (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0) (hP' : (Uinv * P).det ≠ 0) :
    AlphaLawAt v (Qo.compMat U) (Uinv * P) hP' ↔ AlphaLawAt v Qo P hP := by
  have hU0 : U.det ≠ 0 := hU.ne_zero
  set u := glOf v U hU0
  have hQ : (Qo.compMat U).map (algebraMap 𝔬 Fv) = (Qo.map (algebraMap 𝔬 Fv)).compMat u.val :=
    integralModel_compMat v rfl U hU0
  have hUP : U * (Uinv * P) = P := by rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hlat1 : locAct v u (locAct v (glOf v (Uinv * P) hP') (std v)) = locAct v (glOf v P hP) (std v) := by
    rw [← locAct_mul, ← glOf_mul v U (Uinv * P) hU0 hP' (by rw [hUP]; exact hP)]
    congr 2
  have hlat2 : locAct v u (std v) = std v := locAct_glOf_unit v U hU hU0
  have hβ1 : localDensityForm (Qo.compMat U) (Qo.compMat U) (NF.π v) = localDensityForm Qo Qo (NF.π v) := by
    rw [← localDensityForm_congr_left (isometricGL_compMat v _ U hU),
      ← localDensityForm_congr_right _ (isometricGL_compMat v _ U hU)]
  have hdet : ‖(((Uinv * P).det : 𝔬) : Fv)‖ = ‖((P.det : 𝔬) : Fv)‖ := by
    have hUi : IsUnit Uinv.det := by
      have := congrArg Matrix.det hUU
      rw [det_mul, det_one] at this
      exact ⟨⟨Uinv.det, U.det, by rw [mul_comm]; exact this, this⟩, rfl⟩
    rw [norm_det_mul, norm_det_unit v hUi, one_mul]
  unfold AlphaLawAt
  rw [hQ, relRatio_KL_conj, hlat1, hlat2, hβ1, compMat_mul, hUP, hdet]

/-- **The cocycle:** the law for $P_1$ and for $(Q_o\circ P_1, P_2)$ give the law for $P_1P_2$
($r(K_3, K_1) = r(K_3, K_2)\,r(K_2, K_1)$ for commensurable stabilizers, `relRatio_mul`). -/
theorem alphaLaw_mul (Qo : QuadForm 𝔬 N) (P₁ P₂ : Matrix (Fin N) (Fin N) 𝔬) (h₁ : P₁.det ≠ 0) (h₂ : P₂.det ≠ 0)
    (h₁₂ : (P₁ * P₂).det ≠ 0) (H₁ : AlphaLawAt v Qo P₁ h₁) (H₂ : AlphaLawAt v (Qo.compMat P₁) P₂ h₂) :
    AlphaLawAt v Qo (P₁ * P₂) h₁₂ := by
  set Qv := Qo.map (algebraMap 𝔬 Fv)
  set g₁ := glOf v P₁ h₁
  have hQ : (Qo.compMat P₁).map (algebraMap 𝔬 Fv) = Qv.compMat g₁.val := integralModel_compMat v rfl P₁ h₁
  unfold AlphaLawAt at H₁ H₂ ⊢
  rw [hQ, relRatio_KL_conj, ← locAct_mul, ← glOf_mul v P₁ P₂ h₁ h₂ h₁₂] at H₂
  have hl : ∀ (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0), (locAct v (glOf v P hP) (std v)).IsLattice Fv :=
    fun P hP => locAct_isLattice _ (std_isLattice v)
  rw [← relRatio_mul (commens_KL v Qv (hl _ h₁₂) (hl _ h₁)) (commens_KL v Qv (hl _ h₁) (std_isLattice v))
    (commens_KL v Qv (hl _ h₁₂) (std_isLattice v)), mul_assoc, H₁, ← mul_assoc, H₂, compMat_mul,
    norm_det_mul, mul_pow]
  ring

end Moves

/-! ### Scaling the form -/

section Scaling

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  {N : ℕ}

/-- Counting classes mod $\pi^{a+b}$ of a condition that only depends on the class mod $\pi^a$. -/
theorem card_lift_of_stable {ι : Type*} [Fintype ι] {π : R} (hπ : Irreducible π) {a : ℕ} (P : (ι → R) → Prop)
    (hP : ∀ x y, P x → P (x + π ^ a • y)) (b : ℕ) :
    Nat.card {x : ι → R ⧸ Ideal.span {π ^ (a + b)} // P (liftI π (a + b) x)} =
      Nat.card {x : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a x)} * q R ^ (b * Fintype.card ι) := by
  classical
  have hP' : ∀ x y, P x → P (x + π ^ (a + b) • y) := by
    intro x y hx
    have := hP x (π ^ b • y) hx
    rwa [smul_smul, ← pow_add] at this
  obtain ⟨e⟩ := fiberSigma π hπ.ne_zero a b (a + b) rfl P P hP (fun x h => h) hP'
  have := finite_vec (ι := ι) π hπ a
  have := finite_vec (ι := ι) π hπ b
  have : Finite {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)} := Subtype.finite
  let _ : Fintype {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Nat.card {y : ι → R ⧸ Ideal.span {π ^ b} // P (liftI π a c.1 + π ^ a • liftI π b y)} =
        q R ^ (b * Fintype.card ι) := by
    intro c
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun y => hP _ _ c.2), natCard_vec π hπ b]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

theorem compMat_smul_form (Q : QuadForm R N) (s : R) (X : Matrix (Fin N) (Fin N) R) :
    (s • Q).compMat X = s • Q.compMat X := by
  refine eq_of_eval_eq fun y => ?_
  rw [eval_compMat]
  show (s • Q).evalIn R _ = (s • Q.compMat X).evalIn R y
  simp only [QuadForm.evalIn, smul_coeff, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply]
  have h1 : ∀ (S : QuadForm R N) (z : Fin N → R), (∑ i, ∑ j, if i ≤ j then s * S.coeff i j * z i * z j else 0) =
      s * S.eval z := by
    intro S z
    simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [h1, h1, eval_compMat]

/-- **The scaling of the self-counts**: $A_{\pi^{k+o}}(sQ, sQ) = q^{oN^2}A_{\pi^k}(Q, Q)$ for $\pi^o\,\Vert\,s$. -/
theorem repCountForm_smul_self (Q : QuadForm R N) {π : R} (hπ : Irreducible π) {s : R} {o : ℕ}
    (hs : π ^ o ∣ s) (hs' : ¬ π ^ (o + 1) ∣ s) (k : ℕ) :
    repCountForm (s • Q) (s • Q) π (k + o) = repCountForm Q Q π k * q R ^ (o * (N * N)) := by
  classical
  obtain ⟨u, rfl⟩ := hs
  have hu : IsUnit u := dvr_isUnit_of_not_dvd hπ fun h => hs' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  rw [repCountForm_eq_card_sol, repCountForm_eq_card_sol]
  -- the condition at level `k + o` is the condition at level `k`
  have hcond : ∀ x : Fin N × Fin N → R,
      (∀ p, π ^ (k + o) ∣ formF ((π ^ o * u) • Q) x p - ((π ^ o * u) • Q).coeff p.1.1 p.1.2) ↔
        (∀ p, π ^ k ∣ formF Q x p - Q.coeff p.1.1 p.1.2) := by
    intro x
    refine forall_congr' fun p => ?_
    have : formF ((π ^ o * u) • Q) x p - ((π ^ o * u) • Q).coeff p.1.1 p.1.2 =
        π ^ o * (u * (formF Q x p - Q.coeff p.1.1 p.1.2)) := by
      simp only [formF, compMat_smul_form, smul_coeff, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this, pow_add, mul_comm (π ^ k), mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)]
    exact hu.dvd_mul_left
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => hcond (liftI π (k + o) x))]
  have hstab : ∀ x y : Fin N × Fin N → R, (∀ p, π ^ k ∣ formF Q x p - Q.coeff p.1.1 p.1.2) →
      ∀ p, π ^ k ∣ formF Q (x + π ^ k • y) p - Q.coeff p.1.1 p.1.2 := by
    intro x y hx p
    rw [formF_add_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx p
    have h2 : π ^ k ∣ π ^ k * formD Q x y p + (π ^ k) ^ 2 * formF Q y p :=
      dvd_add (dvd_mul_right _ _) (by rw [pow_two]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
    have := this.add h2
    rwa [show formF Q x p - Q.coeff p.1.1 p.1.2 + (π ^ k * formD Q x y p + (π ^ k) ^ 2 * formF Q y p) =
      formF Q x p + π ^ k * formD Q x y p + (π ^ k) ^ 2 * formF Q y p - Q.coeff p.1.1 p.1.2 by ring] at this
  rw [card_lift_of_stable hπ _ hstab o, Fintype.card_prod, Fintype.card_fin]

theorem eval_smul_form' (Q : QuadForm R N) (s : R) (z : Fin N → R) : (s • Q).eval z = s * Q.eval z := by
  simp only [QuadForm.eval, QuadForm.evalIn, smul_coeff, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem nondegenerate_smul {Q : QuadForm R N} (hQ : Q.Nondegenerate) {s : R} (hs : s ≠ 0) :
    (s • Q).Nondegenerate := by
  have : (s • Q).hessian = s • Q.hessian := by
    simp only [QuadForm.hessian, smul_coeff, Matrix.transpose_smul, smul_add]
  rw [QuadForm.Nondegenerate, this, det_smul]
  exact mul_ne_zero (pow_ne_zero _ hs) hQ

theorem sq_add_tri (N : ℕ) : N * N = N * (N - 1) / 2 + N * (N + 1) / 2 := by
  have h1 := self_exp N
  have h2 : N * (N + 1) / 2 ≤ N * N := by
    rcases N with _ | N
    · simp
    · have : (N + 1) * (N + 1 + 1) / 2 ≤ (N + 1) * (N + 1 + 1) / 2 * 2 / 2 := by omega
      have h3 : (N + 1) * (N + 1 + 1) ≤ 2 * ((N + 1) * (N + 1)) := by nlinarith
      omega
  omega

/-- **Scaling the self-density**: $\beta_\pi(sQ, sQ) = q^{o\,N(N+1)/2}\,\beta_\pi(Q, Q)$ for $\pi^o\,\Vert\,s$ ($Q$ nondegenerate). -/
theorem localDensityForm_smul (Q : QuadForm R N) (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π) {s : R}
    {o : ℕ} (hs : π ^ o ∣ s) (hs' : ¬ π ^ (o + 1) ∣ s) :
    localDensityForm (s • Q) (s • Q) π = (q R : ℝ) ^ (o * (N * (N + 1) / 2)) * localDensityForm Q Q π := by
  have hs0 : s ≠ 0 := fun h => hs' (h ▸ dvd_zero _)
  have e1 := localDensityForm_self_eventually_eq Q hQ π hπ
  have e2 := (Filter.tendsto_add_atTop_nat o).eventually
    (localDensityForm_self_eventually_eq (s • Q) (nondegenerate_smul hQ hs0) π hπ)
  obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
  rw [← hk1, ← hk2, repCountForm_smul_self Q hπ hs hs' k]
  have hq : (0 : ℝ) < q R := Nat.cast_pos.mpr q_pos
  push_cast
  have hE : (q R : ℝ) ^ ((k + o) * (N * (N - 1) / 2)) =
      (q R : ℝ) ^ (k * (N * (N - 1) / 2)) * (q R : ℝ) ^ (o * (N * (N - 1) / 2)) := by
    rw [← pow_add, add_mul]
  have hN : (q R : ℝ) ^ (o * (N * N)) =
      (q R : ℝ) ^ (o * (N * (N - 1) / 2)) * (q R : ℝ) ^ (o * (N * (N + 1) / 2)) := by
    rw [← pow_add, ← mul_add, ← sq_add_tri]
  rw [hE, hN]
  have h1 : (q R : ℝ) ^ (k * (N * (N - 1) / 2)) ≠ 0 := (pow_pos hq _).ne'
  have h2 : (q R : ℝ) ^ (o * (N * (N - 1) / 2)) ≠ 0 := (pow_pos hq _).ne'
  field_simp

end Scaling

/-! ### Scalars and lattices with the same span -/

section Scalar

variable {N : ℕ}

theorem locAct_glOf_smul (c : 𝔬) (hc : ((c • (1 : Matrix (Fin N) (Fin N) 𝔬))).det ≠ 0) :
    locAct v (glOf v (c • (1 : Matrix (Fin N) (Fin N) 𝔬)) hc) (std v) =
      (std v).map ((LinearMap.lsmul Fv (Fin N → Fv) (c : Fv)).restrictScalars 𝔬) := by
  ext x
  simp only [locAct, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    LinearMap.lsmul_apply, glOf_val]
  have : ∀ y : Fin N → Fv, (c • (1 : Matrix (Fin N) (Fin N) 𝔬)).map (algebraMap 𝔬 Fv) *ᵥ y = (c : Fv) • y := by
    intro y
    rw [show (c • (1 : Matrix (Fin N) (Fin N) 𝔬)).map (algebraMap 𝔬 Fv) = (c : Fv) • (1 : Matrix (Fin N) (Fin N) Fv) by
      ext i j; simp [Matrix.one_apply]; split_ifs <;> simp]
    rw [smul_mulVec, one_mulVec]
  simp only [this]

/-- **The law for a scalar matrix** $P = c\cdot 1$: $K(c\Lambda) = K(\Lambda)$, and the scaling of $\beta$ (`localDensityForm_smul`). -/
theorem alphaLaw_scalar (Qo : QuadForm 𝔬 N) (hQo : Qo.Nondegenerate) (c : 𝔬) (hc0 : c ≠ 0)
    (hc : ((c • (1 : Matrix (Fin N) (Fin N) 𝔬))).det ≠ 0) :
    AlphaLawAt v Qo (c • (1 : Matrix (Fin N) (Fin N) 𝔬)) hc := by
  have hπ := NF.irreducible_π v
  obtain ⟨a, ha, ha'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hc0
  unfold AlphaLawAt
  have hcF : (c : Fv) ≠ 0 := fun h => hc0 (Subtype.ext (by simpa using h))
  rw [locAct_glOf_smul, KL_smul v _ _ hcF, relRatio_self, one_mul]
  have hform : Qo.compMat (c • (1 : Matrix (Fin N) (Fin N) 𝔬)) = (c ^ 2) • Qo := by
    refine eq_of_eval_eq fun y => ?_
    rw [eval_compMat, smul_mulVec, one_mulVec, eval_smul_gen, eval_smul_form']
  have ha2 : NF.π v ^ (2 * a) ∣ c ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd ha 2
  have ha2' : ¬ NF.π v ^ (2 * a + 1) ∣ c ^ 2 := by
    intro h
    obtain ⟨u, rfl⟩ := ha
    have hu : IsUnit u := dvr_isUnit_of_not_dvd hπ fun h' => ha' (by rw [pow_succ]; exact mul_dvd_mul_left _ h')
    rw [mul_pow, ← pow_mul, mul_comm a 2, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)] at h
    exact hπ.not_isUnit (isUnit_of_dvd_unit h (hu.pow 2))
  rw [hform, localDensityForm_smul Qo hQo hπ ha2 ha2']
  rw [show (c • (1 : Matrix (Fin N) (Fin N) 𝔬)).det = c ^ N by rw [det_smul, det_one, mul_one, Fintype.card_fin]]
  push_cast
  rw [norm_pow, norm_coe_of_pow_dvd v ha ha']
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  have hT : 2 * a * (N * (N + 1) / 2) = a * N * (N + 1) := by
    obtain ⟨t, ht⟩ := (Nat.even_mul_succ_self N).two_dvd
    rw [ht, Nat.mul_div_cancel_left t two_pos, mul_assoc a N, ht]; ring
  rw [hT, show (q 𝔬 : ℝ) ^ (a * N * (N + 1)) = (((q 𝔬 : ℝ) ^ a) ^ N) ^ (N + 1) by rw [← pow_mul, ← pow_mul, mul_assoc],
    mul_comm _ (localDensityForm Qo Qo (NF.π v)), mul_assoc, ← mul_pow, ← mul_pow,
    mul_inv_cancel₀ (pow_pos hq a).ne', one_pow, one_pow, mul_one]

theorem alphaLaw_congr (Qo : QuadForm 𝔬 N) {P P' : Matrix (Fin N) (Fin N) 𝔬} (h : P = P') (hP : P.det ≠ 0)
    (hP' : P'.det ≠ 0) : AlphaLawAt v Qo P hP ↔ AlphaLawAt v Qo P' hP' := by
  subst h; rfl

theorem exists_mul_eq_of_range_le (P P' : Matrix (Fin N) (Fin N) 𝔬) (h : ∀ y, ∃ y', P' *ᵥ y' = P *ᵥ y) :
    ∃ X, P = P' * X := by
  choose w hw using fun j : Fin N => h (Pi.single j 1)
  refine ⟨Matrix.of fun i j => w j i, Matrix.ext fun i j => ?_⟩
  have := congrFun (hw j) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact this.symm

/-- **Two bases of one lattice**: the law depends only on the lattice $P\,\mathfrak o_\mathfrak p^N$. -/
theorem alphaLaw_of_range_eq (Qo : QuadForm 𝔬 N) (P P' : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0)
    (hP' : P'.det ≠ 0) (h₁ : ∀ y, ∃ y', P' *ᵥ y' = P *ᵥ y) (h₂ : ∀ y, ∃ y', P *ᵥ y' = P' *ᵥ y) :
    AlphaLawAt v Qo P hP ↔ AlphaLawAt v Qo P' hP' := by
  obtain ⟨X, hX⟩ := exists_mul_eq_of_range_le v P P' h₁
  obtain ⟨Y, hY⟩ := exists_mul_eq_of_range_le v P' P h₂
  have hYX : Y * X = 1 := by
    have h1 : P * (Y * X) = P * 1 := by rw [Matrix.mul_one, ← Matrix.mul_assoc, ← hY, ← hX]
    have h2 := congrArg (P.adjugate * ·) h1
    simp only [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h2
    exact smul_right_injective _ hP h2
  have hXu : IsUnit X.det := by
    have := congrArg Matrix.det hYX
    rw [det_mul, det_one] at this
    exact ⟨⟨X.det, Y.det, by rw [mul_comm]; exact this, this⟩, rfl⟩
  rw [alphaLaw_congr v Qo hX hP (by rw [← hX]; exact hP)]
  exact alphaLaw_mul_right v Qo P' X hP' hXu _

end Scalar

/-! ### The split reduction -/

section SplitReduction

variable {n : ℕ}

/-- The transvection $T(u, w) = 1 + u\,w^{\mathsf T}$. -/
theorem transvection_mulVec {R : Type*} [CommRing R] {N : ℕ} (u w x : Fin N → R) :
    (1 + vecMulVec u w) *ᵥ x = x + (w ⬝ᵥ x) • u := by
  rw [add_mulVec, one_mulVec]
  congr 1
  funext i
  simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem det_transvection {R : Type*} [CommRing R] {N : ℕ} (u w : Fin N → R) :
    (1 + vecMulVec u w).det = 1 + w ⬝ᵥ u := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

/-- **A primitive vector is the first column of a matrix in $\mathrm{GL}_{n+1}(R)$** (two transvections). -/
theorem exists_unit_mulVec_e₀ {R : Type*} [CommRing R] (y : Fin (n + 1) → R) (hy : ∃ j, IsUnit (y j)) :
    ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit V.det ∧ V *ᵥ (e₀ : Fin (n + 1) → R) = y := by
  classical
  obtain ⟨j, hj⟩ := hy
  rw [e₀_eq_single]
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨1 + vecMulVec (y - Pi.single 0 1) (Pi.single 0 1), ?_, ?_⟩
    · rw [det_transvection, single_dotProduct]; simpa using hj
    · rw [transvection_mulVec, single_dotProduct]; simp
  · refine ⟨(1 + vecMulVec (y - (Pi.single 0 1 + Pi.single j 1)) (Pi.single j 1)) *
      (1 + vecMulVec (Pi.single j 1) (Pi.single 0 1)), ?_, ?_⟩
    · rw [det_mul, det_transvection, det_transvection, single_dotProduct, single_dotProduct]
      simp [Pi.single_apply, hj0, Ne.symm hj0]
      simpa using hj
    · rw [← mulVec_mulVec, transvection_mulVec, transvection_mulVec, single_dotProduct, single_dotProduct]
      simp [Pi.single_apply, hj0, Ne.symm hj0]

/-- The tail form $Q(0, x_1, \dots, x_n)$. -/
def tailForm {R : Type*} [CommRing R] (Q : QuadForm R (n + 1)) : QuadForm R n :=
  ⟨Q.coeff.submatrix Fin.succ Fin.succ, fun i j h => Q.upper (by simpa using h)⟩

theorem eq_splitForm_of {R : Type*} [CommRing R] (Q : QuadForm R (n + 1)) (h : ∀ j : Fin n, Q.coeff 0 j.succ = 0) :
    Q = splitForm (Q.coeff 0 0) (tailForm Q) := by
  refine QuadForm.ext (Matrix.ext fun i j => ?_)
  rw [splitForm_coeff]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simpa using h j
  · simp only [cornerMat, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero]
    exact Q.upper (by simp [Fin.succ_pos])
  · rfl

theorem eq_cornerMat_of {R : Type*} [CommRing R] (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (h00 : M 0 0 = 1)
    (hc : ∀ i : Fin n, M i.succ 0 = 0) (hr : ∀ j : Fin n, M 0 j.succ = 0) :
    M = cornerMat 1 (M.submatrix Fin.succ Fin.succ) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using h00
  · simpa using hr j
  · simpa using hc i
  · rfl

theorem dotProduct_hessian_comm {R : Type*} [CommRing R] {N : ℕ} (Q : QuadForm R N) (x y : Fin N → R) :
    x ⬝ᵥ (Q.hessian *ᵥ y) = y ⬝ᵥ (Q.hessian *ᵥ x) := by
  have hT : Q.hessianᵀ = Q.hessian := by simp [QuadForm.hessian, add_comm]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

theorem exists_isUnit_of_mulVec_eq_e₀ {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝔬) (y : Fin (N + 1) → 𝔬)
    (hy : M *ᵥ y = e₀) : ∃ j, IsUnit (y j) := by
  by_contra hne
  push_neg at hne
  have hπ := NF.irreducible_π v
  have hd : ∀ j, NF.π v ∣ y j := fun j => by
    by_contra h; exact hne j (dvr_isUnit_of_not_dvd hπ h)
  choose y' hy' using hd
  have : (e₀ : Fin (N + 1) → 𝔬) = NF.π v • (M *ᵥ y') := by
    rw [← hy, ← mulVec_smul]; congr 1; funext j; simp [hy' j]
  have h0 := congrFun this 0
  simp only [Pi.smul_apply, smul_eq_mul] at h0
  exact hπ.not_isUnit ⟨⟨NF.π v, (M *ᵥ y') 0, by rw [← h0]; rfl, by rw [mul_comm, ← h0]; rfl⟩, rfl⟩

/-- **The split reduction** (every prime, dyadic included): if $\Lambda_1 = P\,\mathfrak o_\mathfrak p^{n+1}$ contains a vector $z$ with
$Q(z) \ne 0$ that splits $\mathfrak o_\mathfrak p^{n+1}$ ($2Q(z) \mid B(z, x)$ for all integral $x$), then the law for $(Q_o, P)$ follows from
the law in rank $n$. *Proof:* a basis $U = (z, w_1, \dots, w_n)$ of $\mathfrak o_\mathfrak p^{n+1}$ with $w_i \perp z$ (a primitive-vector
extension and a transvection), so $Q_o\circ U = \langle Q(z)\rangle\perp Q''$; in these coordinates $\Lambda_1 \ni e_0$ has a basis
$\mathrm{diag}(1, P'')$ (two more transvections); then `alphaLaw_split`, `alphaLaw_conj`, `alphaLaw_mul_right`. -/
@[kb "weil1982" "§3.4; Hanke 2004 §3, pp. 358–361 (change of lattice along a split vector)"]
theorem alphaLaw_of_split (Qo : QuadForm 𝔬 (n + 1)) (hQo : Qo.Nondegenerate) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)
    (hP : P.det ≠ 0) (z : Fin (n + 1) → 𝔬) (hzP : ∃ y, P *ᵥ y = z) (hz0 : Qo.eval z ≠ 0)
    (hsplit : ∀ i, 2 * Qo.eval z ∣ (Qo.hessian *ᵥ z) i)
    (IH : ∀ (Q'' : QuadForm 𝔬 n) (P'' : Matrix (Fin n) (Fin n) 𝔬) (hP'' : P''.det ≠ 0), Q''.Nondegenerate →
      AlphaLawAt v Q'' P'' hP'') :
    AlphaLawAt v Qo P hP := by
  classical
  have hπ := NF.irreducible_π v
  have h2 := NF.two_ne_zero' v
  set m := Qo.eval z
  have hdvd : ∀ x : Fin (n + 1) → 𝔬, 2 * m ∣ x ⬝ᵥ (Qo.hessian *ᵥ z) :=
    fun x => Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hsplit i) _
  -- `z` is primitive
  have hzprim : ∃ j, IsUnit (z j) := by
    by_contra hne
    push_neg at hne
    have hd : ∀ j, NF.π v ∣ z j := fun j => by
      by_contra h; exact hne j (dvr_isUnit_of_not_dvd hπ h)
    choose z' hz' using hd
    have hzz : z = NF.π v • z' := funext fun j => by simp [hz' j]
    obtain ⟨t, ht⟩ := hdvd z'
    have e1 : z' ⬝ᵥ (Qo.hessian *ᵥ z) = NF.π v * (2 * Qo.eval z') := by
      rw [hzz, mulVec_smul, dotProduct_smul, smul_eq_mul, dotProduct_hessian_self]
    have e2 : m = NF.π v ^ 2 * Qo.eval z' := by
      show Qo.eval z = _; rw [hzz, eval_smul_gen]
    rw [e1, e2] at ht
    have hz'0 : (2 * Qo.eval z' : 𝔬) ≠ 0 := by
      intro h0; apply hz0; show Qo.eval z = 0; rw [hzz, eval_smul_gen]
      have : Qo.eval z' = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h h2
        · exact h
      rw [this, mul_zero]
    have : (2 * Qo.eval z' * NF.π v) * (NF.π v * t - 1) = 0 := by linear_combination -ht
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hz'0 h'
      · exact hπ.ne_zero h'
    · exact hπ.not_isUnit ⟨⟨NF.π v, t, by linear_combination h, by linear_combination h⟩, rfl⟩
  -- `U₁ e₀ = z`
  obtain ⟨U₁, hU₁, hU₁e⟩ := exists_unit_mulVec_e₀ z hzprim
  -- the transvection making the form split
  choose b hb using fun j : Fin n => hdvd (U₁ *ᵥ Pi.single j.succ 1)
  set t : Fin (n + 1) → 𝔬 := Fin.cons 0 fun j => -b j
  set U₂ := 1 + vecMulVec (e₀ : Fin (n + 1) → 𝔬) t
  have hU₂ : IsUnit U₂.det := by
    rw [det_transvection]; simp [t, e₀_eq_single]
  set U := U₁ * U₂
  have hU : IsUnit U.det := by rw [det_mul]; exact hU₁.mul hU₂
  have hte : t ⬝ᵥ (e₀ : Fin (n + 1) → 𝔬) = 0 := by
    rw [e₀_eq_single, dotProduct_single, mul_one]; rfl
  have hUe : U *ᵥ (e₀ : Fin (n + 1) → 𝔬) = z := by
    rw [← mulVec_mulVec, transvection_mulVec, hte, zero_smul, add_zero, hU₁e]
  set Q₂ := Qo.compMat U
  have hQ₂00 : Q₂.coeff 0 0 = m := by
    rw [compMat_coeff, if_pos le_rfl, if_pos rfl]
    show Qo.eval (fun l => U l 0) = Qo.eval z
    congr 1; rw [← hUe, e₀_eq_single, mulVec_single_one]; rfl
  have hQ₂0j : ∀ j : Fin n, Q₂.coeff 0 j.succ = 0 := by
    intro j
    rw [compMat_coeff, if_pos (Fin.zero_le _), if_neg (Fin.succ_ne_zero j).symm]
    have hcol0 : (fun l => U l 0) = z := by rw [← hUe, e₀_eq_single, mulVec_single_one]; rfl
    have hcolj : (fun l => U l j.succ) = U₁ *ᵥ Pi.single j.succ 1 + t j.succ • z := by
      have : (fun l => U l j.succ) = U *ᵥ Pi.single j.succ 1 := by rw [mulVec_single_one]; rfl
      rw [this, ← mulVec_mulVec, transvection_mulVec, mulVec_add, mulVec_smul, hU₁e]
      congr 2
      simp [t, e₀_eq_single, dotProduct, Pi.single_apply]
    rw [hcol0, dotProduct_hessian_comm, hcolj, add_dotProduct, smul_dotProduct, hb j, dotProduct_hessian_self]
    simp only [t, Fin.cons_succ, smul_eq_mul]
    ring
  have hQ₂ : Q₂ = splitForm m (tailForm Q₂) := by
    conv_lhs => rw [eq_splitForm_of Q₂ hQ₂0j]
    rw [hQ₂00]
  have hQ₂nd : Q₂.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hU.ne_zero hQo) hU.ne_zero
  have hQ''nd : (tailForm Q₂).Nondegenerate := by
    have := hQ₂nd
    rw [hQ₂, QuadForm.Nondegenerate, det_hessian_splitForm] at this
    exact right_ne_zero_of_mul this
  -- pass to the coordinates `U`
  set Uinv := U⁻¹
  have hUU : U * Uinv = 1 := Matrix.mul_nonsing_inv U hU
  have hP' : (Uinv * P).det ≠ 0 := by
    rw [det_mul]; exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det U hU).ne_zero hP
  rw [← alphaLaw_conj v Qo U Uinv hU hUU P hP hP']
  -- `e₀ ∈ U⁻¹ Λ₁`
  obtain ⟨y₀, hy₀⟩ := hzP
  have hPy : (Uinv * P) *ᵥ y₀ = e₀ := by
    rw [← mulVec_mulVec, hy₀, ← hUe, mulVec_mulVec, Matrix.nonsing_inv_mul U hU, one_mulVec]
  obtain ⟨V₁, hV₁, hV₁e⟩ := exists_unit_mulVec_e₀ y₀ (exists_isUnit_of_mulVec_eq_e₀ v _ y₀ hPy)
  set M := Uinv * P * V₁
  have hMe : M *ᵥ (e₀ : Fin (n + 1) → 𝔬) = e₀ := by rw [← mulVec_mulVec, hV₁e, hPy]
  set s' : Fin (n + 1) → 𝔬 := Fin.cons 0 fun j => -M 0 j.succ
  set W := 1 + vecMulVec (e₀ : Fin (n + 1) → 𝔬) s'
  have hW : IsUnit W.det := by
    rw [det_transvection]; simp [s', e₀_eq_single, single_dotProduct]
  have hMW : M * W = cornerMat 1 ((M * W).submatrix Fin.succ Fin.succ) := by
    have hcol : ∀ i, M i 0 = (e₀ : Fin (n + 1) → 𝔬) i := by
      intro i
      have := congrFun hMe i
      rw [e₀_eq_single, mulVec_single_one] at this
      rw [e₀_eq_single]; exact this
    have hMWe : ∀ i j, (M * W) i j = M i j + (e₀ : Fin (n + 1) → 𝔬) i * s' j := by
      intro i j
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
      congr 1
      simp only [Matrix.mul_apply, vecMulVec_apply]
      rw [Finset.sum_eq_single 0]
      · rw [hcol]; simp [e₀_eq_single]
      · intro k _ hk; rw [e₀_eq_single]; simp [Pi.single_apply, hk]
      · simp
    refine eq_cornerMat_of _ ?_ ?_ ?_
    · rw [hMWe, hcol]; simp [s', e₀_eq_single]
    · intro i; rw [hMWe, hcol]; simp [s', e₀_eq_single]
    · intro j; rw [hMWe]; simp [s', e₀_eq_single]
  have hVW : IsUnit (V₁ * W).det := by rw [det_mul]; exact hV₁.mul hW
  have hMW0 : (Uinv * P * (V₁ * W)).det ≠ 0 := by
    rw [det_mul, det_mul]
    exact mul_ne_zero (mul_ne_zero (Matrix.isUnit_nonsing_inv_det U hU).ne_zero hP) hVW.ne_zero
  set P'' := (M * W).submatrix Fin.succ Fin.succ
  have hassoc : Uinv * P * (V₁ * W) = cornerMat 1 P'' := by
    rw [← hMW, ← Matrix.mul_assoc]
  have hP''0 : P''.det ≠ 0 := by
    have := hMW0
    rw [hassoc, det_cornerMat, one_mul] at this
    exact this
  have hc0 : (cornerMat 1 P'').det ≠ 0 := by rw [det_cornerMat, one_mul]; exact hP''0
  rw [← alphaLaw_mul_right v Q₂ (Uinv * P) (V₁ * W) hP' hVW hMW0, alphaLaw_congr v Q₂ hassoc hMW0 hc0, hQ₂]
  exact alphaLaw_split v (tailForm Q₂) hQ''nd hz0 P'' hP''0 hc0 (IH _ _ hP''0 hQ''nd)

end SplitReduction

end QuadFormsKB.Tamagawa
