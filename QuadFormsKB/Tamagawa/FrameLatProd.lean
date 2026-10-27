/-
# Siegel's product in every rank, split into an archimedean prefactor and a finite product

**Layer:** $F$ a totally real number field; $Q_0$ over $\mathcal O_F$ of rank $N$, $T_0$ over $\mathcal O_F$ of rank $r$, $1 \le r \le N$.

The `siegelProductAll Q₀ T₀` is `preAll Q₀ T₀ * prodAll Q₀ T₀ (β-function)` with
* `preAll` $= (2\text{ if }N = 1)\cdot\varepsilon'\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\varepsilon\,\beta_\sigma(Q_0,T_0)$ (the archimedean prefactor);
* `prodAll f` the finite product of the case: $\prod_\mathfrak p f(\mathfrak p)$ (`tprod`) for $N \ge 3$, $N - r \ne 2$ and for $N = 1$;
  `regProd (chiForms Q₀ T₀) 1 f` for $N \ge 3$, $N - r = 2$; `regProd (chiP · Q₀) (-1) f` for $N = 2$.

For a frame adapted to $T_0$ with complement $Q'$, the local identity writes Siegel's local factors as $a_\mathfrak p\,u_\mathfrak p$ with
$a$ of finite support and $u_\mathfrak p = \varepsilon_{N,r}\beta_\mathfrak p(Q_0,Q_0)/\beta_\mathfrak p(Q',Q')$ (`baseU`) independent of $T$.

**Proves**
* `siegelProductAll_eq`: the split;
* **`prodMult_baseU`**: `prodAll` is multiplicative on $a\,u$ for $a$ of finite support (`ProdMult`), in every case: the corrected
  product $u\,(1-\chi/N\mathfrak p)^e$ converges ($N, n' \ge 3$: both $\alpha$-products converge; $n' = 2$: the binary factor
  $\alpha_\mathfrak p(Q')(1-\chi'/N\mathfrak p)^{-1}$ has finite support and $\chi' = \chi$ off a finite set; $n' = 1$: rank one has finite support;
  $n' = 0$: $\beta(Q',Q') = 1$; $N \le 2$: finite support);
* `prodAll_scale`: `prodAll` of $u$ is the same for $T_0$ and $c^2T_0$ (the character changes at finitely many primes only);
* `preAll_scale`: $\mathrm{pre}(c^2T_0) = \mathrm{pre}(T_0)\,(\prod_\sigma|\sigma c|)^{r(n'-1)}$;
* `prodAll_eq_zero_of_exists`: a vanishing local factor makes `prodAll` vanish;
* `exists_mul_integral`: a nonzero $c \in \mathcal O_F$ clearing the denominators of a matrix over $F$.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatDefs

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices LocalDensity Frames QuadFormsKB.HilbertModular QuadFormsKB.RegProd NFEuler

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **The archimedean prefactor of Siegel's product in every rank**: $(2$ if $N = 1)\cdot\varepsilon'_{N,r}\,|d_F|^{-r(2N-r-1)/4}
\prod_\sigma\varepsilon_{N,r}\,\beta_\sigma(Q_0,T_0)$. -/
def preAll (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  (if N = 1 then 2 else 1) * (epsCodimOne N r * |(discr F : ℝ)| ^ (-((r : ℝ) * (2 * N - r - 1)) / 4) *
    ∏ σ : F →ₐ[ℚ] ℂ, epsNR N r * archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ))

/-- **The finite product of Siegel's formula in every rank**: plain (`tprod`) for $N = 1$ and for $N \ge 3$, $N - r \ne 2$; regularized
by $L_F(1,\chi)$ for $N - r = 2$ (`chiForms`, exponent $1$) and for $N = 2$ (`chiP · Q₀`, exponent $-1$). -/
def prodAll (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (f : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  if N = 1 then ∏' v, f v
  else if N = 2 then regProd (fun v => chiP v Q₀) (-1) f
  else if N = r + 2 then regProd (chiForms Q₀ T₀) 1 f
  else ∏' v, f v

/-- **The Siegel product is `preAll * prodAll` of the local densities.** -/
theorem siegelProductAll_eq (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) :
    siegelProductAll Q₀ T₀ = preAll Q₀ T₀ * prodAll Q₀ T₀ (fun v => NF.siegelDensity v Q₀ T₀) := by
  unfold siegelProductAll preAll prodAll siegelProductT siegelProductTRegWith siegelProductTReg
  split_ifs <;> ring

/-- **The $T$-independent part of the local factors** for a complement $Q'$: $u_\mathfrak p = \varepsilon_{N,r}\beta_\mathfrak p(Q_0,Q_0)/\beta_\mathfrak p(Q',Q')$. -/
def baseU {n' : ℕ} (Q₀ : QuadForm (𝓞 F) N) (Q' : QuadForm (𝓞 F) n') (r : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  epsNR N r * NF.localDensityForm v Q₀ Q₀ / NF.localDensityForm v Q' Q'

/-- **Multiplicativity of the finite product on $u$**: $\mathrm{prodAll}(a\,u) = \mathrm{prodAll}(u)\prod_\mathfrak p a(\mathfrak p)$ for every $a$ of finite
support. -/
def ProdMult (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (u : HeightOneSpectrum (𝓞 F) → ℝ) : Prop :=
  ∀ a : HeightOneSpectrum (𝓞 F) → ℝ, Function.HasFiniteMulSupport a →
    prodAll Q₀ T₀ (fun v => a v * u v) = prodAll Q₀ T₀ u * ∏ᶠ v, a v

section Helpers

theorem tprod_mul_fin {u a : HeightOneSpectrum (𝓞 F) → ℝ} (hu : Multipliable u) (ha : Function.HasFiniteMulSupport a) :
    ∏' v, a v * u v = (∏' v, u v) * ∏ᶠ v, a v := by
  have ham : Multipliable a := multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) ha
  have h := ham.tprod_mul hu
  have h2 : ∏' v, a v = ∏ᶠ v, a v := tprod_eq_finprod ha
  rw [mul_comm, ← h2]
  exact h

theorem regProd_mul_fin' (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ) {u a : HeightOneSpectrum (𝓞 F) → ℝ}
    (hu : Multipliable fun v => u v * (1 - χ v / (normP v : ℝ)) ^ e) (ha : Function.HasFiniteMulSupport a) :
    regProd χ e (fun v => a v * u v) = regProd χ e u * ∏ᶠ v, a v := by
  have := regProd_mul_fin χ e ha.toFinset (f := u) (g := a) (fun v hv => by
    by_contra h
    exact hv (ha.mem_toFinset.2 h)) hu
  simp only [mul_comm (a _)]
  rw [this, finprod_eq_prod a ha]

theorem baseU_zero {Q₀ : QuadForm (𝓞 F) (r + 0)} (Q' : QuadForm (𝓞 F) 0) (v : HeightOneSpectrum (𝓞 F)) :
    baseU Q₀ Q' r v = NF.siegelDensity v Q₀ Q₀ := by
  unfold baseU NF.siegelDensity
  rw [localDensityForm_rank_zero, if_pos rfl]
  simp [epsNR]

theorem baseU_pos {n' : ℕ} (hn : 1 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n')) (Q' : QuadForm (𝓞 F) n')
    (v : HeightOneSpectrum (𝓞 F)) :
    baseU Q₀ Q' r v = NF.siegelDensity v Q₀ Q₀ / NF.siegelDensity v Q' Q' := by
  unfold baseU NF.siegelDensity
  rw [if_pos rfl, if_pos rfl, epsNR, if_neg (by omega), one_mul, mul_div_mul_left _ _ (by norm_num)]

theorem inv_finite {ι : Type*} {f : ι → ℝ} (h : Function.HasFiniteMulSupport f) :
    Function.HasFiniteMulSupport fun i => (f i)⁻¹ :=
  h.subset fun i hi hf => hi (by simp [hf])

variable [IsTotallyReal F]

theorem nondeg_complement {n' : ℕ} {Q₀ : QuadForm (𝓞 F) (r + n')} {T₀ : QuadForm (𝓞 F) r}
    (hpd : IsTotallyPosDef (formF Q₀)) (fr : AdaptedFrameT (formF Q₀) (formF T₀)) : fr.Q'.Nondegenerate :=
  nondegenerate_of_map (isTotallyPosDef_of_blockForm_right (isTotallyPosDef_blockForm_frame fr hpd)).nondegenerate

/-- Rank one: the local factor is $1$ off finitely many primes. -/
theorem finite_sd_rankOne (Q : QuadForm (𝓞 F) 1) (hQ : Q.Nondegenerate) :
    Function.HasFiniteMulSupport fun v => NF.siegelDensity v Q Q :=
  (finite_badPrimes Q hQ).subset fun v hv => by
    by_contra h
    exact hv (RankOne.siegelDensity_rankOne_good Q hQ v h)

theorem mult_N1 {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (fr : AdaptedFrameT (formF Q₀) (formF T₀))
    (h : r + n' = 1) : Multipliable (baseU Q₀ fr.Q' r) := by
  obtain ⟨rfl, rfl⟩ : r = 1 ∧ n' = 0 := by omega
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have e : baseU Q₀ fr.Q' 1 = fun v => NF.siegelDensity v Q₀ Q₀ := funext fun v => baseU_zero _ v
  rw [e]
  exact multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) (finite_sd_rankOne Q₀ hQ)

theorem mult_N2 {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (fr : AdaptedFrameT (formF Q₀) (formF T₀))
    (h : r + n' = 2) :
    Multipliable fun v => baseU Q₀ fr.Q' r v * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ) := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQ' := nondeg_complement hpd fr
  rcases (by omega : (r = 2 ∧ n' = 0) ∨ (r = 1 ∧ n' = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hfin := hasFiniteMulSupport_siegelDensity_binary_reg (Q' := Q₀) hQ ∅ (χ := fun v => chiP v Q₀)
      (fun _ _ => rfl)
    refine multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) ?_
    simpa only [baseU_zero] using hfin
  · have hfin := hasFiniteMulSupport_siegelDensity_binary_reg (Q' := Q₀) hQ ∅ (χ := fun v => chiP v Q₀)
      (fun _ _ => rfl)
    have h2 := inv_finite (finite_sd_rankOne fr.Q' hQ')
    refine multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) ?_
    have e : (fun v => baseU Q₀ fr.Q' 1 v * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ)) =
        fun v => (NF.siegelDensity v Q₀ Q₀ * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ)) *
          (NF.siegelDensity v fr.Q' fr.Q')⁻¹ := funext fun v => by
      rw [baseU_pos (by norm_num)]; ring
    rw [e]
    exact hfin.mul h2

theorem mult_reg2 (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (fr : AdaptedFrameT (formF Q₀) (formF T₀)) :
    Multipliable fun v => baseU Q₀ fr.Q' r v * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (1 : ℤ) := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQ' := nondeg_complement hpd fr
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiForms Q₀ T₀ hpd hpdT fr
  have hfin := hasFiniteMulSupport_siegelDensity_binary_reg hQ' (χ := chiForms Q₀ T₀) S hS
  have hm : Multipliable fun v => NF.siegelDensity v Q₀ Q₀ :=
    multipliable_siegelDensity (by omega) (by omega) Q₀ hQ
  have e : (fun v => baseU Q₀ fr.Q' r v * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (1 : ℤ)) =
      fun v => NF.siegelDensity v Q₀ Q₀ *
        (NF.siegelDensity v fr.Q' fr.Q' * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ))⁻¹ :=
    funext fun v => by
      rw [baseU_pos (by norm_num)]
      rw [_root_.zpow_one, _root_.zpow_neg_one, mul_inv, inv_inv]
      ring
  rw [e]
  exact hm.mul (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) (inv_finite hfin))

theorem mult_plain {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (fr : AdaptedFrameT (formF Q₀) (formF T₀))
    (h3 : 3 ≤ r + n') (h2 : r + n' ≠ r + 2) : Multipliable (baseU Q₀ fr.Q' r) := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQ' := nondeg_complement hpd fr
  have hm : Multipliable fun v => NF.siegelDensity v Q₀ Q₀ :=
    multipliable_siegelDensity (by omega) (by omega) Q₀ hQ
  rcases Nat.eq_zero_or_pos n' with h0 | h0
  · subst h0
    have e : baseU Q₀ fr.Q' r = fun v => NF.siegelDensity v Q₀ Q₀ := funext fun v => baseU_zero _ v
    rw [e]; exact hm
  · have e : baseU Q₀ fr.Q' r = fun v => NF.siegelDensity v Q₀ Q₀ / NF.siegelDensity v fr.Q' fr.Q' :=
      funext fun v => baseU_pos h0 _ _ v
    rw [e]
    by_cases h1 : n' = 1
    · subst h1
      have h4 := inv_finite (finite_sd_rankOne fr.Q' hQ')
      have := hm.mul (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) h4)
      simpa only [div_eq_mul_inv] using this
    · have hm' : Multipliable fun v => NF.siegelDensity v fr.Q' fr.Q' :=
        multipliable_siegelDensity (by omega) (by omega) fr.Q' hQ'
      have hpos := tprod_siegelDensity_pos (by omega : 3 ≤ n') fr.Q' hQ'
      exact (hm.hasProd.div₀ hm'.hasProd hpos.ne').multipliable

/-- **The character `chiForms` changes at finitely many primes only under $T_0 \mapsto c^2T_0$.** -/
theorem chiForms_scale {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r} (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate) {c : 𝓞 F} (hc : c ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v ∉ S, chiForms Q₀ (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) v = chiForms Q₀ T₀ v := by
  classical
  have hδ : deltaForms Q₀ T₀ ≠ 0 := deltaForms_ne_zero hQ hT
  have hD : deltaForms Q₀ (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) =
      (c ^ r) ^ 2 * deltaForms Q₀ T₀ := by
    unfold deltaForms
    rw [QuadForm.hessian_compMat]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.det_mul, Matrix.det_smul, Matrix.det_one]
    simp
    ring
  have hne : (2 * c * deltaForms Q₀ T₀ : 𝓞 F) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hδ
  refine ⟨(Siegel.finite_mem_asIdeal hne).toFinset, fun v hv => ?_⟩
  have hv' : 2 * c * deltaForms Q₀ T₀ ∉ v.asIdeal := fun hm => hv (by simpa using hm)
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ hm))
  have hc' : c ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ hm))
  have hd : deltaForms Q₀ T₀ ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_left _ hm)
  have hu' : c ^ r ∉ v.asIdeal := fun hm => hc' (v.isPrime.mem_of_pow_mem r hm)
  have hd2 : (c ^ r) ^ 2 * deltaForms Q₀ T₀ ∉ v.asIdeal := by
    intro hm
    rcases v.isPrime.mem_or_mem hm with hm | hm
    · exact hu' (v.isPrime.mem_of_pow_mem 2 hm)
    · exact hd hm
  unfold chiForms
  rw [hD, if_pos ⟨h2, hd2⟩, if_pos ⟨h2, hd⟩]
  congr 1
  unfold Siegel.charNF
  have hres : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v (c ^ r)) ≠ 0 := fun h0 =>
    hu' ((NF.π_dvd_ι_iff v _).1 ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).1 h0))
  have e : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v ((c ^ r) ^ 2 * deltaForms Q₀ T₀)) =
      (IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v (c ^ r))) ^ 2 *
        IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v (deltaForms Q₀ T₀)) := by
    simp only [map_mul, map_pow]
  rw [e, map_mul, quadraticChar_sq_one' hres, one_mul]

end Helpers

/-- **`prodAll` is multiplicative on `baseU`, in every case** (module docstring). -/
theorem prodMult_baseU [IsTotallyReal F] {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (fr : AdaptedFrameT (formF Q₀) (formF T₀)) : ProdMult Q₀ T₀ (baseU Q₀ fr.Q' r) := by
  intro a ha
  unfold prodAll
  split_ifs with h1 h2 h3
  · exact tprod_mul_fin (mult_N1 Q₀ T₀ hr hpd fr h1) ha
  · exact regProd_mul_fin' _ _ (mult_N2 Q₀ T₀ hr hpd fr h2) ha
  · obtain rfl : n' = 2 := by omega
    exact regProd_mul_fin' _ _ (mult_reg2 Q₀ T₀ hr hpd hpdT fr) ha
  · exact tprod_mul_fin (mult_plain Q₀ T₀ hr hpd fr (by omega) h3) ha

/-- **The finite product of $u$ does not see the scaling $T_0 \mapsto c^2T_0$** (only `chiForms` depends on $T_0$, and only at the primes
dividing $c$). -/
theorem prodAll_scale [IsTotallyReal F] {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀))
    (fr : AdaptedFrameT (formF Q₀) (formF T₀)) {c : 𝓞 F} (hc : c ≠ 0) :
    prodAll Q₀ (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) (baseU Q₀ fr.Q' r) =
      prodAll Q₀ T₀ (baseU Q₀ fr.Q' r) := by
  unfold prodAll
  by_cases h1 : r + n' = 1
  · rw [if_pos h1, if_pos h1]
  by_cases h2 : r + n' = 2
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
  by_cases h3 : r + n' = r + 2
  · rw [if_neg h1, if_neg h2, if_pos h3, if_neg h1, if_neg h2, if_pos h3]
    obtain rfl : n' = 2 := by omega
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    obtain ⟨S, hS⟩ := chiForms_scale hQ hT hc
    exact regProd_congr_finite (abs_chiForms_le _ _) (abs_chiForms_le _ _) S hS
      (lOne_chiForms_pos hpd hpdT).2 1 _ (mult_reg2 Q₀ T₀ hr hpd hpdT fr)
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h1, if_neg h2, if_neg h3]

/-- **Scaling of the archimedean prefactor:** $\mathrm{pre}(c^2T_0) = \mathrm{pre}(T_0)\,(\prod_\sigma|\sigma c|)^{r(N-r-1)}$. -/
theorem preAll_scale [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hpd : IsTotallyPosDef (formF Q₀)) (hpdT : IsTotallyPosDef (formF T₀)) {c : 𝓞 F} (hc : c ≠ 0) :
    preAll Q₀ (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) =
      preAll Q₀ T₀ * (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F c)‖) ^ ((r : ℝ) * ((N : ℝ) - r - 1)) := by
  have hDT : ∀ σ : F →ₐ[ℚ] ℂ, detGram (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) σ =
      (‖σ (algebraMap (𝓞 F) F c)‖ ^ r) ^ 2 * detGram T₀ σ := fun σ => by
    rw [LatChange.detGram_compMat]
    simp [map_pow, norm_pow]
  have hnn : ∀ σ : F →ₐ[ℚ] ℂ, 0 ≤ detGram T₀ σ := fun σ => by unfold detGram; exact norm_nonneg _
  have harch : ∀ σ : F →ₐ[ℚ] ℂ, archDensityForm N r (detGram Q₀ σ)
      (detGram (T₀.compMat (c • (1 : Matrix (Fin r) (Fin r) (𝓞 F)))) σ) =
      archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ) *
        ‖σ (algebraMap (𝓞 F) F c)‖ ^ ((r : ℝ) * ((N : ℝ) - r - 1)) := fun σ => by
    unfold archDensityForm
    have key : ∀ (a : ℝ), 0 ≤ a → ∀ x : ℝ, ((a ^ r) ^ 2) ^ x = a ^ ((r : ℝ) * (2 * x)) := fun a ha x => by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul ha]
      push_cast
      ring_nf
    rw [hDT σ, Real.mul_rpow (by positivity) (hnn σ), key _ (norm_nonneg _)]
    have : ((r : ℝ) * (2 * (((N : ℝ) - r - 1) / 2))) = (r : ℝ) * ((N : ℝ) - r - 1) := by ring
    rw [this]
    ring
  unfold preAll
  simp_rw [harch]
  rw [Finset.prod_congr rfl (fun σ _ => (by ring : epsNR N r * (archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ) *
        ‖σ (algebraMap (𝓞 F) F c)‖ ^ ((r : ℝ) * ((N : ℝ) - r - 1))) =
      (epsNR N r * archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ)) *
        ‖σ (algebraMap (𝓞 F) F c)‖ ^ ((r : ℝ) * ((N : ℝ) - r - 1)))),
    Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun σ _ => norm_nonneg _)]
  ring

/-- **A vanishing local factor makes the finite product vanish** (in every case). -/
theorem prodAll_eq_zero_of_exists (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) {f : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : ∃ v, f v = 0) : prodAll Q₀ T₀ f = 0 := by
  obtain ⟨v, hv⟩ := h
  have hz : ∀ (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ),
      (∏' w, f w * (1 - χ w / (normP w : ℝ)) ^ e) = 0 := fun χ e =>
    tprod_of_exists_eq_zero ⟨v, by simp only [hv, zero_mul]⟩
  unfold prodAll
  split_ifs
  · exact tprod_of_exists_eq_zero ⟨v, hv⟩
  · unfold regProd; rw [hz, mul_zero]
  · unfold regProd; rw [hz, mul_zero]
  · exact tprod_of_exists_eq_zero ⟨v, hv⟩

/-- **Clearing denominators:** for $X \in F^{a\times b}$ there is $c \in \mathcal O_F$, $c \ne 0$, with $cX$ integral. -/
theorem exists_mul_integral {a b : ℕ} (X : Matrix (Fin a) (Fin b) F) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i j, ∃ z : 𝓞 F, algebraMap (𝓞 F) F c * X i j = algebraMap (𝓞 F) F z := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image (fun p : Fin a × Fin b => X p.1 p.2))
  refine ⟨(b : 𝓞 F), nonZeroDivisors.coe_ne_zero b, fun i j => ?_⟩
  obtain ⟨z, hz⟩ := hb (X i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  exact ⟨z, by rw [hz, Algebra.smul_def]⟩

end QuadFormsKB.Tamagawa.FramesLat
