/-
# Lattices by lattices: consistency checks and the rank-one corollary

**Layer:** as `FrameLatSiegel.lean`: $F$ totally real, any class number; $L$ an arbitrary lattice on $V = (F^N, Q_0)$.

**Proves**
* `siegelFormsAllLat_std_iff` (**free $L$ and $T$**): for $L = \mathcal O_F^N$, $T_\ell = \mathcal O_F^r$ the lattice
  statement is
  `SiegelFormsAll Q₀ T₀` (so `siegelFormsLat_all_ranks` recovers `siegelForms_all_ranks`).
* **The rank-one corollary** $T = \mathfrak a\langle m\rangle$ (`idealLat`, $\mathfrak a$ a nonzero fractional ideal, possibly non-principal):
  `repCountLat_idealLat` ($r(M, \mathfrak a\langle m\rangle) = \#\{x \in F^N : Q(x) = m,\ \mathfrak a x \subseteq M\}$, i.e. $x \in \mathfrak a^{-1}M$),
  **`siegelFormsLat_rankOne`** (Siegel's formula for $\mathfrak a\langle m\rangle$ and the genus of $L$, every $N \ge 1$, unconditional), and
  `siegelFormsAllLat_unary_iff` (for $\mathfrak a = \mathcal O_F$, $N \ge 4$, it is `SiegelFormulaAtLat Q₀ L m`,
  Siegel's formula for the
  number $m$ and the genus of $L$).
* **$T = L$** (`repMassLat_self`, `mass_mul_siegelProductAllLat_self`): the embeddings of $L$ into the lattices of its genus are the
  isometries onto $L$'s class, so the left side is $1$ and the formula is the mass formula $\mathrm{Mass}(L)\cdot S(L, L) = 1$ for the genus of
  an arbitrary lattice.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatSiegel

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices LocalDensity Frames SiegelLat QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-! ### Free lattices -/

/-- **Consistency check (free $L$ and $T$):** for $L = \mathcal O_F^N$ and $T_\ell = \mathcal O_F^r$ the lattice
statement is
`SiegelFormsAll`. -/
@[kb "siegel1935" "Hauptsatz, free lattices (consistency) [unverified]"]
theorem siegelFormsAllLat_std_iff [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r)
    (hrN : r ≤ N) : SiegelFormsAllLat Q₀ (stdLat F N) T₀ (stdLat F r) ↔ SiegelFormsAll Q₀ T₀ := by
  have hsd : (fun v => siegelDensityLat v Q₀ (stdLat F N) T₀ (stdLat F r)) = fun v => NF.siegelDensity v Q₀ T₀ := by
    funext v
    unfold siegelDensityLat NF.siegelDensity epsNR
    rw [latBetaT_of_std v (by omega) hr Q₀ _ (isIntegral_stdLat_map Q₀) T₀ _ (isIntegral_stdLat_map T₀)
      (loc_intVec v) (loc_intVec v)]
    by_cases h : r = N
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hp : siegelProductAllLat Q₀ (stdLat F N) T₀ (stdLat F r) = siegelProductAll Q₀ T₀ := by
    rw [siegelProductAll_eq]; unfold siegelProductAllLat; rw [hsd]
  constructor
  · intro h; exact ⟨by rw [← repMassLat_stdLat, ← hp]; exact h.repMass_eq⟩
  · intro h; exact ⟨by rw [repMassLat_stdLat, hp]; exact h.repMass_eq⟩

/-! ### Rank one: $T = \mathfrak a\langle m\rangle$ -/

theorem mem_steinitzLat_zero {𝔞 : Submodule (𝓞 F) F} {x : Fin 1 → F} :
    x ∈ Steinitz.steinitzLat (m := 0) 𝔞 ↔ x 0 ∈ 𝔞 :=
  ⟨fun h => h.2, fun h => ⟨fun i => i.elim0, h⟩⟩

theorem idealLat_isLattice' (𝔞 : Submodule (𝓞 F) F) (hfg : 𝔞.FG) (hne : 𝔞 ≠ ⊥) :
    (Steinitz.steinitzLat (m := 0) 𝔞).IsLattice F where
  fg := by
    let f : F →ₗ[𝓞 F] (Fin 1 → F) :=
      { toFun := fun a _ => a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have : Steinitz.steinitzLat (m := 0) 𝔞 = 𝔞.map f := by
      ext x
      rw [mem_steinitzLat_zero, Submodule.mem_map]
      constructor
      · intro h; exact ⟨x 0, h, funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ha
    rw [this]; exact hfg.map f
  span_eq_top := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Submodule.eq_top_iff']
    intro y
    have hmem : (fun _ : Fin 1 => a) ∈ Steinitz.steinitzLat (m := 0) 𝔞 := mem_steinitzLat_zero.mpr ha
    have : y = (y 0 / a) • (fun _ : Fin 1 => a) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [ha0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- **The rank-one lattice $\mathfrak a e_0 \subseteq F^1$** of a nonzero fractional ideal $\mathfrak a$ (an $\mathcal O_F$-submodule of $F$,
finitely generated and nonzero; possibly non-principal). With the form $\langle m\rangle$ it is the quadratic lattice $\mathfrak a\langle m\rangle$.
Every lattice on $F^1$ is of this form (`Steinitz.exists_eq_glImage_steinitzLat` with $m = 0$). -/
def idealLat (𝔞 : Submodule (𝓞 F) F) (hfg : 𝔞.FG) (hne : 𝔞 ≠ ⊥) : Lat F 1 :=
  ⟨Steinitz.steinitzLat (m := 0) 𝔞, idealLat_isLattice' 𝔞 hfg hne⟩

/-- **Embeddings of $\mathfrak a\langle m\rangle$** into $M$ are the vectors $x$ with $Q(x) = m$ and $\mathfrak a x \subseteq M$ (i.e. $x \in \mathfrak a^{-1}M$):
the embedding $\mathfrak a e_0 \to M$, $a e_0 \mapsto a x$. -/
theorem repCountLat_idealLat (Q : QuadForm F N) (M : Lat F N) (𝔞 : Submodule (𝓞 F) F) (hfg : 𝔞.FG) (hne : 𝔞 ≠ ⊥)
    (m : F) : repCountLat Q M (idealLat 𝔞 hfg hne) (DVR.unary m) =
      Nat.card {x : Fin N → F // (∀ a ∈ 𝔞, a • x ∈ M.1) ∧ Q.eval x = m} := by
  unfold repCountLat
  refine Nat.card_congr ?_
  let e : Matrix (Fin N) (Fin 1) F ≃ (Fin N → F) :=
    { toFun := fun X l => X l 0
      invFun := fun x => Matrix.of fun l _ => x l
      left_inv := fun X => by ext l i; rw [Fin.fin_one_eq_zero i]; rfl
      right_inv := fun x => rfl }
  refine Equiv.subtypeEquiv e ?_
  intro X
  have hc : Q.compMat X = DVR.unary m ↔ Q.eval (fun l => X l 0) = m := by
    constructor
    · intro h
      have := congrArg (fun T : QuadForm F 1 => T.coeff 0 0) h
      simpa [QuadForm.compMat_coeff, DVR.unary, QuadForm.diag] using this
    · intro h
      apply QuadForm.ext_upper
      intro i j _
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      simpa [QuadForm.compMat_coeff, DVR.unary, QuadForm.diag] using h
  have hmv : ∀ t : Fin 1 → F, X *ᵥ t = t 0 • (fun l => X l 0) := by
    intro t; funext l; simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hc]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h a ha
    have := h (fun _ => a) (mem_steinitzLat_zero.mpr ha)
    rw [hmv] at this
    exact this
  · intro h t ht
    rw [hmv]
    exact h _ (mem_steinitzLat_zero.mp ht)

theorem one_fg' : (1 : Submodule (𝓞 F) F).FG := by
  rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton 1

theorem one_ne_bot' : (1 : Submodule (𝓞 F) F) ≠ ⊥ := by
  intro h
  have h1 : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [h, Submodule.mem_bot] at h1
  exact one_ne_zero h1

/-- For $\mathfrak a = \mathcal O_F$ the lattice $\mathfrak a e_0$ is $\mathcal O_F^1$. -/
theorem idealLat_top : idealLat (1 : Submodule (𝓞 F) F) (one_fg' (F := F)) one_ne_bot' = stdLat F 1 := by
  refine Subtype.ext ?_
  ext x
  show x ∈ Steinitz.steinitzLat (m := 0) (1 : Submodule (𝓞 F) F) ↔ x ∈ (intVec : Submodule (𝓞 F) (Fin 1 → F))
  rw [mem_steinitzLat_zero, Submodule.mem_one, mem_intVec]
  constructor
  · rintro ⟨y, hy⟩ i
    rw [Fin.fin_one_eq_zero i]; exact ⟨y, hy⟩
  · intro h
    obtain ⟨y, hy⟩ := h 0
    exact ⟨y, hy⟩

/-- **Siegel's formula for $\mathfrak a\langle m\rangle$ and the genus of $L$** (rank one, every $N \ge 1$, any class number, unconditional):
for a nonzero fractional ideal $\mathfrak a$ and $m \in \mathcal O_F$ totally positive with $m\mathfrak a^2 \subseteq \mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\#\{x \in \mathfrak a^{-1}M : Q(x) = m\}}{|O(M)|} = \mathrm{Mass}(L)\cdot S(L, \mathfrak a\langle m\rangle).$$ -/
@[kb "siegel1935" "Hauptsatz, r = 1, lattice a<m> (any class number) [unverified]"]
theorem siegelFormsLat_rankOne [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (hN : 1 ≤ N)
    (hpd : IsTotallyPosDef (formF Q₀)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) (𝔞 : Submodule (𝓞 F) F) (hfg : 𝔞.FG)
    (hne : 𝔞 ≠ ⊥) (m : 𝓞 F) (hm : IsTotallyPosDef (formF (DVR.unary m)))
    (hmi : Lattices.IsIntegral (formF (DVR.unary m)) (idealLat 𝔞 hfg hne).1) :
    repMassLat (formF Q₀) L (idealLat 𝔞 hfg hne) (formF (DVR.unary m)) =
      mass (formF Q₀) L * siegelProductAllLat Q₀ L (DVR.unary m) (idealLat 𝔞 hfg hne) :=
  (siegelFormsLat_all_ranks Q₀ L (DVR.unary m) (idealLat 𝔞 hfg hne) le_rfl hN hpd hm hLi hmi).repMass_eq

/-- **For $\mathfrak a = \mathcal O_F$ and $N \ge 4$ the rank-one statement is the Siegel formula for the number $m$
and the genus of $L$**
(`SiegelFormulaAtLat`): $\beta_\mathfrak p(L, \mathcal O_F\langle m\rangle) = \beta_\mathfrak p(L, m)$ and the archimedean factors agree. -/
@[kb "siegel1935" "Hauptsatz, r = 1 (relation to the numbers case, lattices) [unverified]"]
theorem siegelFormsAllLat_unary_iff [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (hN : 4 ≤ N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (m : 𝓞 F) :
    SiegelFormsAllLat Q₀ L (DVR.unary m) (stdLat F 1) ↔ SiegelFormulaAtLat Q₀ L m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hm : formF (DVR.unary m) = DVR.unary (algebraMap (𝓞 F) F m) := by
    ext i j
    simp [formF, QuadForm.map, DVR.unary, QuadForm.diag, Matrix.diagonal_apply]
  have hrep : repMassLat (formF Q₀) L (stdLat F 1) (formF (DVR.unary m)) =
      repMass (formF Q₀) L (algebraMap (𝓞 F) F m) := by
    rw [repMassLat_stdLat, hm, Frames.repMassT_unary]
  have hε : epsNR (n + 1) 1 = 1 := by
    unfold epsNR; rw [if_neg (by omega)]
  have hden : ∀ v : HeightOneSpectrum (𝓞 F),
      siegelDensityLat v Q₀ L (DVR.unary m) (stdLat F 1) = latBeta v Q₀ L m := by
    intro v
    unfold siegelDensityLat
    obtain ⟨A, hA⟩ := exists_isLocModel v L
    have hAi := hA.isIntegral v hLi
    have hB : loc v (Lattices.latOf (1 : GL (Fin 1) F)) = loc v (stdLat F 1).1 := by
      rw [Lattices.latOf, glImage_one]
    rw [hε, one_mul, latBetaT_eq_of_loc v (by omega) le_rfl Q₀ L hLi (DVR.unary m) (stdLat F 1)
      (isIntegral_stdLat_map _) hA.2 hAi hB (isIntegral_latOf_one _), latBeta_eq v Q₀ L hA hAi m,
      gramZ_one, NF.localDensityForm_unary]
    simp
  have hdet : (DVR.unary m).hessian.det = 2 * m := by
    simp [QuadForm.hessian, DVR.unary, QuadForm.diag, Matrix.det_unique, Matrix.diagonal_apply]
    ring
  have hg : ∀ σ : F →ₐ[ℚ] ℂ, detGram (DVR.unary m) σ = ‖σ (algebraMap (𝓞 F) F m)‖ := by
    intro σ
    unfold detGram
    rw [hdet]
    congr 1
    simp only [map_mul, map_ofNat, pow_one]
    rw [mul_div_cancel_left₀ _ (two_ne_zero)]
  have hp : siegelProductAllLat Q₀ L (DVR.unary m) (stdLat F 1) = siegelProductLat Q₀ L m := by
    unfold siegelProductAllLat siegelProductLat preAll prodAll
    have h1 : ¬ (n + 1 = 1) := by omega
    have h2 : ¬ (n + 1 = 2) := by omega
    have h3 : ¬ (n + 1 = 1 + 2) := by omega
    have h4 : ¬ (1 + 1 = n + 1) := by omega
    simp only [h1, h2, h3, if_false]
    rw [show epsCodimOne (n + 1) 1 = 1 from if_neg h4]
    simp only [hden, hg, hε, one_mul, archDensityForm_one]
    congr 2
    push_cast
    ring_nf
  constructor
  · intro h
    exact ⟨by rw [← hrep, ← hp]; exact h.repMass_eq⟩
  · intro h
    exact ⟨by rw [hrep, hp]; exact h.repMass_eq⟩

/-! ### $T = L$: the mass formula for the genus of a lattice -/

/-- An isometry over a field $R \supseteq F$ of a nondegenerate form has $\det^2 = 1$. -/
theorem det_sq_of_orth {R : Type*} [Field R] [Algebra F R] {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate)
    {g : GL (Fin n) R} (hg : g ∈ orthGroup Q R) : g.val.det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det ((mem_orthGroup Q).mp hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have hH : (Q.hessian.map (algebraMap F R)).det ≠ 0 := by
    rw [show (Q.hessian.map (algebraMap F R)).det = algebraMap F R Q.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (_root_.map_ne_zero _).mpr hQ
  have : g.val.det ^ 2 * (Q.hessian.map (algebraMap F R)).det =
      1 * (Q.hessian.map (algebraMap F R)).det := by
    rw [one_mul]; conv_rhs => rw [← h1]
    ring
  exact mul_right_cancel₀ hH this

/-- **A unit-determinant map into $\mathfrak o_\mathfrak p^N$ is onto:** if $k\,\mathfrak o^N \subseteq \mathfrak o^N$ and
$|\det k| = 1$ then $k\,\mathfrak o^N = \mathfrak o^N$. -/
theorem locAct_std_eq_of_le_unit (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (k : GL (Fin N) (v.adicCompletion F))
    (hle : locAct v k (std v) ≤ std v) (hdet : Valued.v k.val.det = 1) : locAct v k (std v) = std v := by
  have hk : ∀ i j, Valued.v (k.val i j) ≤ 1 := by
    intro i j
    have hmem : k.val *ᵥ (Pi.single j (1 : v.adicCompletion F)) ∈ std v :=
      hle (mem_locAct.mpr ⟨_, single_one_mem_std v j, rfl⟩)
    have := hmem i
    rw [neg_zero, WithZero.exp_zero] at this
    simpa [mulVec_single] using this
  have hk' : ∀ i j, Valued.v (k⁻¹.val i j) ≤ 1 := by
    let A : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨k.val i j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hk i j)⟩
    have hA : A.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) = k.val := by
      ext i j; rfl
    have hadj : k.val.adjugate = A.adjugate.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [← hA]; exact ((algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).map_adjugate A).symm
    intro i j
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', hadj, Matrix.smul_apply, smul_eq_mul, map_mul,
      map_inv₀, hdet, inv_one, one_mul, Matrix.map_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (A.adjugate i j).2
  have h2 : locAct v k⁻¹ (std v) ≤ std v := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_locAct.mp hy
    have hx' : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
      have := hx j; rwa [neg_zero, WithZero.exp_zero] at this
    intro i
    show Valued.v ((k⁻¹.val *ᵥ x) i) ≤ WithZero.exp (-(0 : ℤ))
    rw [neg_zero, WithZero.exp_zero]
    simp only [Matrix.mulVec, dotProduct]
    exact Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hk' i j) (hx' j)
  rw [locAct_eq_iff]
  refine le_antisymm ?_ h2
  calc std v = locAct v k⁻¹ (locAct v k (std v)) := (locAct_inv_locAct k (std v)).symm
    _ ≤ locAct v k⁻¹ (std v) := Submodule.map_mono hle

/-- **A unit-determinant map into $L_\mathfrak p$ is onto:** if $h L_\mathfrak p \subseteq L_\mathfrak p$ and $|\det h| = 1$ then $hL_\mathfrak p = L_\mathfrak p$. -/
theorem locAct_loc_eq_of_le_unit (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (L : Lat F N)
    (h : GL (Fin N) (v.adicCompletion F)) (hle : locAct v h (loc v L.1) ≤ loc v L.1)
    (hdet : Valued.v h.val.det = 1) : locAct v h (loc v L.1) = loc v L.1 := by
  obtain ⟨A, hA⟩ := SiegelSpace.exists_isLocModel' v L
  set P := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A with hPdef
  have hP : loc v L.1 = locAct v P (std v) := by
    have := hA.2
    rw [Lattices.latOf, loc_glImage, loc_intVec] at this
    exact this.symm
  rw [hP] at hle ⊢
  have hk : locAct v (P⁻¹ * h * P) (std v) ≤ std v := by
    rw [locAct_mul, locAct_mul]
    calc locAct v P⁻¹ (locAct v h (locAct v P (std v))) ≤ locAct v P⁻¹ (locAct v P (std v)) :=
          Submodule.map_mono hle
      _ = std v := locAct_inv_locAct P (std v)
  have hdk : Valued.v (P⁻¹ * h * P).val.det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hdet, mul_one,
      ← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one]
  have heq := locAct_std_eq_of_le_unit v _ hk hdk
  rw [← locAct_mul, show h * P = P * (P⁻¹ * h * P) by group, locAct_mul, heq]

/-- **An isometry of $V$ mapping $L$ into a lattice $M$ of its genus maps $L$ onto $M$.** -/
theorem glImage_eq_of_le_sameGenus {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) {L M : Lat F n}
    (hg : SameGenus Q L.1 M.1) {X : GL (Fin n) F} (hX : X ∈ orthGroup Q F) (hle : glImage X L.1 ≤ M.1) :
    glImage X L.1 = M.1 := by
  refine loc_injective (glImage_isLattice X L.2) M.2 fun v => ?_
  obtain ⟨g, hgo, hgM⟩ := hg v
  set Xv := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) X with hXv
  have hXL : loc v (glImage X L.1) = locAct v Xv (loc v L.1) := loc_glImage v X L.1
  have hle' : locAct v Xv (loc v L.1) ≤ loc v M.1 := hXL ▸ loc_mono v hle
  have h1 : locAct v (g⁻¹ * Xv) (loc v L.1) ≤ loc v L.1 := by
    rw [locAct_mul]
    calc locAct v g⁻¹ (locAct v Xv (loc v L.1)) ≤ locAct v g⁻¹ (loc v M.1) := Submodule.map_mono hle'
      _ = loc v L.1 := by rw [← hgM, locAct_inv_locAct]
  have hdet : Valued.v (g⁻¹ * Xv).val.det = 1 := by
    have e1 : (g⁻¹.val.det) ^ 2 = 1 := det_sq_of_orth Q hQ ((orthGroup Q _).inv_mem hgo)
    have e2 : (Xv.val.det) ^ 2 = 1 := by
      have h0 := det_sq_of_orth Q hQ hX
      have e : Xv.val.det = algebraMap F (v.adicCompletion F) X.val.det := by
        rw [RingHom.map_det]; rfl
      rw [e, ← map_pow, h0, map_one]
    have h3 : Valued.v (g⁻¹ * Xv).val.det ^ 2 = 1 := by
      rw [← map_pow, show (g⁻¹ * Xv).val.det ^ 2 = (g⁻¹.val.det) ^ 2 * (Xv.val.det) ^ 2 by
        rw [Units.val_mul, Matrix.det_mul, mul_pow], e1, e2, one_mul, map_one]
    exact sq_eq_one.mp h3
  have h2 := locAct_loc_eq_of_le_unit v L _ h1 hdet
  rw [hXL]
  calc locAct v Xv (loc v L.1) = locAct v g (locAct v (g⁻¹ * Xv) (loc v L.1)) := by
        rw [← locAct_mul, mul_inv_cancel_left]
    _ = loc v M.1 := by rw [h2, hgM]

/-- A square matrix with $Q\circ X = Q$ ($Q$ nondegenerate) is an invertible isometry. -/
theorem exists_gl_of_compMat {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) (X : Matrix (Fin n) (Fin n) F)
    (h : Q.compMat X = Q) : ∃ g : GL (Fin n) F, g.val = X ∧ g ∈ orthGroup Q F := by
  have h1 := congrArg QuadForm.hessian h
  rw [QuadForm.hessian_compMat] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  have hX : X.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero] at h2
    exact hQ h2.symm
  have hu : IsUnit X.det := hX.isUnit
  refine ⟨Matrix.nonsingInvUnit X hu, rfl, ?_⟩
  refine mem_orthGroup_of_eval Q fun z => ?_
  show Q.eval (X *ᵥ z) = Q.eval z
  rw [← QuadForm.eval_compMat, h]

/-- Every embedding $X$ of $L$ into a lattice $M$ of its genus is an isometry onto $M$. -/
theorem exists_isometry_of_emb {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) {L M : Lat F n}
    (hg : SameGenus Q L.1 M.1) {X : Matrix (Fin n) (Fin n) F}
    (hX : (∀ t ∈ L.1, X *ᵥ t ∈ M.1) ∧ Q.compMat X = Q) :
    ∃ g : GL (Fin n) F, g ∈ orthGroup Q F ∧ g.val = X ∧ glImage g L.1 = M.1 := by
  obtain ⟨g, rfl, hgo⟩ := exists_gl_of_compMat Q hQ X hX.2
  refine ⟨g, hgo, rfl, glImage_eq_of_le_sameGenus Q hQ hg hgo ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
  exact hX.1 y hy

theorem repCountLat_self_eq_card {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) (L : Lat F n) :
    repCountLat Q L L Q = Nat.card (autLat Q L.1) := by
  unfold repCountLat
  have hmem : ∀ δ : autLat Q L.1, (∀ t ∈ L.1, (δ.1.1 : GL (Fin n) F).val *ᵥ t ∈ L.1) ∧
      Q.compMat (δ.1.1 : GL (Fin n) F).val = Q := by
    intro δ
    refine ⟨fun t ht => ?_, QuadForm.eq_of_eval_eq fun y => ?_⟩
    · have h0 := (mem_autLat Q).mp δ.2
      have h2 := mulVec_mem_glImage (γ := (δ.1.1 : GL (Fin n) F)) ht
      rwa [h0] at h2
    · rw [QuadForm.eval_compMat, eval_mulVec_of_mem Q δ.1.2]
  let f : autLat Q L.1 → {X : Matrix (Fin n) (Fin n) F // (∀ t ∈ L.1, X *ᵥ t ∈ L.1) ∧ Q.compMat X = Q} :=
    fun δ => ⟨(δ.1.1 : GL (Fin n) F).val, hmem δ⟩
  have hf : Function.Bijective f := by
    constructor
    · intro δ δ' h
      exact Subtype.ext (Subtype.ext (Units.ext (congrArg Subtype.val h)))
    · rintro ⟨X, hX⟩
      obtain ⟨g, hgo, hgX, hgL⟩ := exists_isometry_of_emb Q hQ (SameGenus.refl Q L.1) hX
      exact ⟨⟨⟨g, hgo⟩, (mem_autLat Q).mpr hgL⟩, Subtype.ext hgX⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem repCountLat_self_eq_zero {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) {L M : Lat F n}
    (hg : SameGenus Q L.1 M.1) (hnot : ¬ IsIsometric Q L.1 M.1) : repCountLat Q M L Q = 0 := by
  unfold repCountLat
  haveI : IsEmpty {X : Matrix (Fin n) (Fin n) F // (∀ t ∈ L.1, X *ᵥ t ∈ M.1) ∧ Q.compMat X = Q} :=
    ⟨fun ⟨X, hX⟩ => by
      obtain ⟨g, hgo, _, hgL⟩ := exists_isometry_of_emb Q hQ hg hX
      exact hnot ⟨g, hgo, hgL⟩⟩
  exact Nat.card_of_isEmpty

/-- **The embeddings of $L$ into its genus:** $\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L} r(M, L)/|O(M)| = 1$ ($r(M, L) = |O(L)|$ for $M \cong L$, and $0$
otherwise: an isometric embedding of $L$ into a lattice of its genus is onto, the two having the same volume at every prime). -/
theorem repMassLat_self (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) : repMassLat (formF Q₀) L L (formF Q₀) = 1 := by
  have hQ := hpd.nondegenerate
  have hfin := genusClasses_finite hpd L hLi
  haveI := finite_autLat hpd L.2 hLi
  unfold repMassLat
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc0 : Quotient.mk (latSetoid (formF Q₀)) L ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset _).mpr ⟨L, rfl, SameGenus.refl _ L.1⟩
  rw [Finset.sum_eq_single (Quotient.mk (latSetoid (formF Q₀)) L)]
  · show ((repCountLat (formF Q₀) L L (formF Q₀) : ℕ) : ℝ) / ((Nat.card (autLat (formF Q₀) L.1) : ℕ) : ℝ) = 1
    rw [repCountLat_self_eq_card _ hQ]
    exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  · intro b hb hne
    obtain ⟨M', rfl, hg'⟩ := (Set.Finite.mem_toFinset _).mp hb
    show ((repCountLat (formF Q₀) M' L (formF Q₀) : ℕ) : ℝ) / _ = 0
    have hnot : ¬ IsIsometric (formF Q₀) L.1 M'.1 := fun hiso =>
      hne (Quotient.sound (IsIsometric.symm _ hiso))
    rw [repCountLat_self_eq_zero _ hQ hg' hnot, Nat.cast_zero, zero_div]
  · intro h; exact absurd hc0 h

/-- **Consistency check $T = L$: the mass formula for the genus of an arbitrary lattice** (any Steinitz class, every rank $N \ge 1$):
$\mathrm{Mass}(L)\cdot S(L, L) = 1$, with Siegel's $\varepsilon = \tfrac12$ (and the regularization for $N = 2$, the factor $2$ for $N = 1$). -/
@[kb "siegel1935" "Hauptsatz, T = L (mass formula for lattices) [unverified]"]
theorem mass_mul_siegelProductAllLat_self [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (hN : 1 ≤ N)
    (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F N) (hLi : Lattices.IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L * siegelProductAllLat Q₀ L Q₀ L = 1 := by
  rw [← (siegelFormsLat_all_ranks Q₀ L Q₀ L hN le_rfl hpd hpd hLi hLi).repMass_eq, repMassLat_self Q₀ hpd L hLi]

end QuadFormsKB.Tamagawa.FramesLat
