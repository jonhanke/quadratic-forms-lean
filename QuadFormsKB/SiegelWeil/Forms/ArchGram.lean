/-
# The rectangular Gram disintegration (Siegel–Weil for forms by forms)

**Layer:** real archimedean place; Lebesgue measure on $r$ vectors in $\mathbb R^N$, $r \le N$.

**Setting.** A tuple of $r$ vectors $X = (X_0, \dots, X_{r-1})$, $X_j \in \mathbb R^N$ (the columns of an $N \times r$ matrix), with Lebesgue
measure $dX$ on $(\mathbb R^N)^r$; its Gram vector $\mathrm{Gram}(X) = (X_i \cdot X_j)_{0 \le i \le j < r}$
(`gramU`), the upper coordinates of $X^{\mathsf T}X$, with Lebesgue measure $dt$ on $\mathbb R^{\{(i,j) : i \le j\}}$
(`UIdx r → ℝ`). Indices are 0-based. This generalizes the square case $r = N$ (`lintegral_gram`,
`Tamagawa/ArchVolume`) and the weighted square case (`lintegral_gramH`, `Literature/Hanke2005/ArchGramAux`).

**Results.**
* `densRect` ($\rho_{N,r}$): the recursive density, $\rho_{N,0} = 1$, $\rho_{0,r+1} = 0$ and
  $\rho_{N+1,r+1}(t) = [s > 0]\,\kappa_{N+1}\,s^{(N-r-1)/2}\,\rho_{N,r}(V - uu^{\mathsf T}/s)$ for
  $t = \begin{pmatrix} s & u^{\mathsf T}\\ u & V\end{pmatrix}$, where $\kappa_N = \pi^{N/2}/\Gamma(N/2)$ (`kap`).
* `lintegral_gramRect` (**unconditional**): for $r \le N$ and measurable $f \ge 0$,
  $$\int_{(\mathbb R^N)^r}f(X^{\mathsf T}X)\,dX = \int f(t)\,\rho_{N,r}(t)\,dt.$$
* `densRect_of_piv`: on positive definite $t$ (more precisely, positive Schur pivots, `piv`),
  $$\rho_{N,r}(t) = \prod_{j<r}\kappa_{N-j}\cdot\det(t)^{(N-r-1)/2}\qquad(\texttt{cprodRect}),$$
  and $\rho_{N,r} = 0$ off that set (`densRect_eq_zero_of_not_piv`): the Wishart density.
* `map_gramRect`: the push-forward of Lebesgue measure under the Gram map is `volume.withDensity (densRect N r)`.
* `lintegral_gramRectH` and `map_gramRectH`: for a positive definite $N \times N$ matrix $H$ and the Gram vector
  $(X_i^{\mathsf T}HX_j)_{i \le j}$ (`gramH`), the same with the extra factor $\det(H)^{-r/2}$.
* `densRect_le`, `densRect_ne_top`: the density is finite and bounded by $\prod_{j<r}\kappa_{N-j}\,|\det t|^{(N-r-1)/2}$.

**Proof.** Induction on $r$ (with $N$ varying): split off the first vector $x \in \mathbb R^{N+1}$, rotate it by a
Householder reflection to $(\|x\|, 0, \dots, 0)$, split each remaining vector into its top entry $w_j$ and the rest
$Z_j \in \mathbb R^N$ (so $s = \|x\|^2$, $u = \|x\|\,w$, $V = ww^{\mathsf T} + Z^{\mathsf T}Z$), integrate $Z$ by induction for $(N, r)$,
translate $V$, rescale $w$ (a factor $s^{-r/2}$) and push $x$ forward to $s = \|x\|^2$ (density $\kappa_{N+1}s^{(N+1)/2-1}$).

**Inputs.** None: everything is proved from Mathlib, unconditionally.

Sources: Siegel, Ann. of Math. 36 (1935), §1 [unverified]; Muirhead, *Aspects of multivariate statistical theory* (1982),
Thm 2.1.14 (the Wishart density) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.ArchVolume
import QuadFormsKB.Literature.Hanke2005.ArchGramAux

open MeasureTheory Matrix Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Hanke2005.ArchReal

/-- **The density of the rectangular Gram map** $X \mapsto X^{\mathsf T}X$ from $(\mathbb R^N)^r$ (recursive form, upper
coordinates): $\rho_{N,0} = 1$, $\rho_{0,r+1} = 0$ and
$\rho_{N+1,r+1}(t) = [s > 0]\,\kappa_{N+1}\,s^{(N-r-1)/2}\,\rho_{N,r}(V - uu^{\mathsf T}/s)$, where $s = t_{00}$, $u = (t_{0,j+1})_j$,
$V = (t_{i+1,j+1})_{i \le j}$ and $\kappa_N = \pi^{N/2}/\Gamma(N/2)$ (`kap`). The exponent is
$(N+1)/2 - 1 - r/2 = (N-r-1)/2$. On positive definite $t$ it is $\prod_{j<r}\kappa_{N-j}\det(t)^{(N-r-1)/2}$
(`densRect_of_piv`). -/
def densRect : (N r : ℕ) → (UIdx r → ℝ) → ℝ≥0∞
  | _, 0, _ => 1
  | 0, _ + 1, _ => 0
  | N + 1, r + 1, t => if 0 < sU t then
      ENNReal.ofReal (kap (N + 1) * sU t ^ ((((N + 1 : ℕ) : ℝ) - 1 - r) / 2 - 1 / 2)) *
        densRect N r (schurU t) else 0

/-- **Measurability of the density** `densRect N r`. -/
theorem measurable_densRect : ∀ N r, Measurable (densRect N r)
  | N, 0 => by
    have : densRect N 0 = fun _ => 1 := by funext t; simp [densRect]
    rw [this]; exact measurable_const
  | 0, r + 1 => by
    have : densRect 0 (r + 1) = fun _ => 0 := by funext t; simp [densRect]
    rw [this]; exact measurable_const
  | N + 1, r + 1 => by
    have : densRect (N + 1) (r + 1) = fun t => if 0 < sU t then
      ENNReal.ofReal (kap (N + 1) * sU t ^ ((((N + 1 : ℕ) : ℝ) - 1 - r) / 2 - 1 / 2)) *
        densRect N r (schurU t) else 0 := by
      funext t; simp [densRect]
    rw [this]
    refine Measurable.ite (measurableSet_lt measurable_const measurable_sU) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_sU.pow_const _))).mul
      ((measurable_densRect N r).comp measurable_schurU)

/-- **The recursion for `densRect` on an assembled vector:** $\rho_{N+1,r+1}(s,u,v) = [s > 0]\,\kappa_{N+1}s^{(N-r-1)/2}
\rho_{N,r}(v - s^{-1}uu^{\mathsf T})$. -/
theorem densRect_succ_asm {N r : ℕ} (s : ℝ) (u : Fin r → ℝ) (v : UIdx r → ℝ) :
    densRect (N + 1) (r + 1) (asm s u v) = if 0 < s then
      ENNReal.ofReal (kap (N + 1) * s ^ (((N : ℝ) - r - 1) / 2)) *
        densRect N r (v - s⁻¹ • outerU u) else 0 := by
  have e : ((((N + 1 : ℕ) : ℝ) - 1 - r) / 2 - 1 / 2) = ((N : ℝ) - r - 1) / 2 := by push_cast; ring
  simp only [densRect, schurU, sU_asm, uU_asm, vU_asm, e]

/-- **The Gram vector after the Householder step, rectangular case:** if the first vector is $(\rho, 0, \dots, 0) \in \mathbb R^{N+1}$
and vector $j+1$ is $(w_j, Z_j)$ with $w_j \in \mathbb R$, $Z_j \in \mathbb R^N$, then $s = \rho^2$, $u = \rho\,w$ and
$V = ww^{\mathsf T} + Z^{\mathsf T}Z$ (here $r$ vectors $w_j, Z_j$ follow the first). -/
theorem gramU_cons_rect {N r : ℕ} (ρ : ℝ) (w : Fin r → ℝ) (Z : Fin r → Fin N → ℝ) :
    gramU (Fin.cons (Fin.cons ρ 0 : Fin (N + 1) → ℝ) (fun j => Fin.cons (w j) (Z j)) :
        Fin (r + 1) → Fin (N + 1) → ℝ) =
      asm (ρ ^ 2) (ρ • w) (outerU w + gramU Z) := by
  funext p
  obtain ⟨q, rfl⟩ := (eU r).surjective p
  rcases q with _ | j | q
  · rw [asm_zero]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ, sq]
  · rw [asm_u]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ]
  · rw [asm_v]; simp [gramU, eU, dotProduct, Fin.sum_univ_succ, outerU]

/-- Splitting each of $r$ vectors in $\mathbb R^{N+1}$ into its top entry $w_j$ and the rest $Z_j \in \mathbb R^N$. -/
theorem lintegral_cols_split_rect {N r : ℕ} {G : (Fin r → Fin (N + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ Y, G Y = ∫⁻ w : Fin r → ℝ, ∫⁻ Z : Fin r → Fin N → ℝ, G (fun j => Fin.cons (w j) (Z j)) := by
  let E : (Fin r → Fin (N + 1) → ℝ) ≃ᵐ (Fin r → ℝ) × (Fin r → Fin N → ℝ) :=
    (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin r))
  have hE : MeasurePreserving E volume volume :=
    (measurePreserving_arrowProdEquivProdArrow ℝ (Fin N → ℝ) (Fin r) (fun _ => volume)
      (fun _ => volume)).comp
      (measurePreserving_pi _ _ (fun _ => volume_preserving_piFinSuccAbove (fun _ => ℝ) 0))
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun w => lintegral_congr fun Z => ?_
  congr 1
  funext j i
  simp [E, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.arrowProdEquivProdArrow]
  rfl

/-- **Rotating the first vector to $(\|x\|, 0, \dots, 0)$, rectangular case:** for fixed $x \in \mathbb R^{N+1}$, applying the
Householder matrix $H_x$ to each of the remaining $r$ vectors preserves Lebesgue measure and the Gram vector of $(x, Y)$. -/
theorem lintegral_cons_hh_rect {N r : ℕ} {f : (UIdx (r + 1) → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (x : Fin (N + 1) → ℝ) :
    ∫⁻ Y : Fin r → Fin (N + 1) → ℝ, f (gramU (Fin.cons x Y : Fin (r + 1) → Fin (N + 1) → ℝ)) =
      ∫⁻ Y : Fin r → Fin (N + 1) → ℝ, f (gramU (Fin.cons (tgt x) Y : Fin (r + 1) → Fin (N + 1) → ℝ)) := by
  have hP : MeasurePreserving (fun (Y : Fin r → Fin (N + 1) → ℝ) j => hh x *ᵥ Y j) volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec _ (abs_det_hh x)
  rw [← hP.lintegral_comp (f := fun Y => f (gramU (Fin.cons (tgt x) Y : Fin (r + 1) → Fin (N + 1) → ℝ)))
    (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)]
  refine lintegral_congr fun Y => ?_
  congr 1
  rw [← gramU_mulVec (hh x) (hh_dot x)]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [hh_mulVec_self]
  · simp

/-- The exponent bookkeeping for the radial step: $\kappa_{N+1}s^{(N+1)/2-1}\cdot(\sqrt s^{\,r})^{-1} = \kappa_{N+1}s^{(N-r-1)/2}$ for $s > 0$. -/
theorem rpow_aux_rect {N r : ℕ} {s : ℝ} (hs : 0 < s) :
    kap (N + 1) * s ^ (((N + 1 : ℕ) : ℝ) / 2 - 1) * (Real.sqrt s ^ r)⁻¹ =
      kap (N + 1) * s ^ (((N : ℝ) - r - 1) / 2) := by
  rw [mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le,
    ← Real.rpow_add hs]
  congr 1; push_cast; ring

/-- The statement of `lintegral_gramRect` with the induction on $r$ made explicit (generalizing $N$). -/
theorem lintegral_gramRect_aux : ∀ (r N : ℕ), r ≤ N → ∀ {f : (UIdx r → ℝ) → ℝ≥0∞}, Measurable f →
    ∫⁻ X : Fin r → Fin N → ℝ, f (gramU X) = ∫⁻ t, densRect N r t * f t
  | 0, N, _, f, hf => by
    have h1 : (volume : Measure (Fin 0 → Fin N → ℝ)) = Measure.dirac 0 := by
      rw [volume_pi]; exact Measure.pi_of_empty _ 0
    have h2 : (volume : Measure (UIdx 0 → ℝ)) = Measure.dirac 0 := by
      rw [volume_pi]; exact Measure.pi_of_empty _ 0
    rw [h1, h2, lintegral_dirac' (f := fun X => f (gramU X)) _ (hf.comp continuous_gramU.measurable),
      lintegral_dirac' (f := fun t => densRect N 0 t * f t) _ ((measurable_densRect N 0).mul hf)]
    simp only [densRect, one_mul]
    exact congrArg f (Subsingleton.elim _ _)
  | r + 1, 0, h, f, hf => absurd h (by omega)
  | r + 1, N + 1, h, f, hf => by
    have hrN : r ≤ N := by omega
    have hfg : Measurable fun X : Fin (r + 1) → Fin (N + 1) → ℝ => f (gramU X) :=
      hf.comp continuous_gramU.measurable
    -- split off the first vector
    have hP := (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => Fin (N + 1) → ℝ) 0).symm
    rw [← hP.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Measure.volume_eq_prod,
      lintegral_prod (f := fun a => f (gramU ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => Fin (N + 1) → ℝ) 0).symm a)))
        (hfg.comp (MeasurableEquiv.measurable _)).aemeasurable]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
      Fin.insertNth_zero']
    rw [lintegral_congr (fun x => lintegral_cons_hh_rect hf x)]
    set Φ : ℝ → ℝ≥0∞ := fun s => ∫⁻ Y : Fin r → Fin (N + 1) → ℝ,
      f (gramU (Fin.cons (Fin.cons (Real.sqrt s) 0 : Fin (N + 1) → ℝ) Y :
        Fin (r + 1) → Fin (N + 1) → ℝ)) with hΦdef
    have hΦ : Measurable Φ :=
      Measurable.lintegral_prod_right' (f := fun p : ℝ × (Fin r → Fin (N + 1) → ℝ) =>
        f (gramU (Fin.cons (Fin.cons (Real.sqrt p.1) 0 : Fin (N + 1) → ℝ) p.2 :
          Fin (r + 1) → Fin (N + 1) → ℝ)))
        (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)
    rw [show (∫⁻ x : Fin (N + 1) → ℝ, ∫⁻ Y : Fin r → Fin (N + 1) → ℝ,
        f (gramU (Fin.cons (tgt x) Y : Fin (r + 1) → Fin (N + 1) → ℝ))) = ∫⁻ x, Φ (x ⬝ᵥ x) from rfl,
      lintegral_dot_self (by omega) hΦ, lintegral_split (F := fun t => densRect (N + 1) (r + 1) t * f t)
        ((measurable_densRect _ _).mul hf)]
    set F : ℝ → (Fin r → ℝ) → (UIdx r → ℝ) → ℝ≥0∞ := fun s u v =>
      ENNReal.ofReal (kap (N + 1) * s ^ (((N : ℝ) - r - 1) / 2)) * densRect N r (v - s⁻¹ • outerU u) *
        f (asm s u v)
    have hR : ∀ s, (∫⁻ u, ∫⁻ v, densRect (N + 1) (r + 1) (asm s u v) * f (asm s u v)) =
        (Ioi 0).indicator (fun s => ∫⁻ u, ∫⁻ v, F s u v) s := by
      intro s
      by_cases hs : 0 < s
      · simp [densRect_succ_asm, hs, F, mul_assoc]
      · simp [densRect_succ_asm, hs]
    rw [lintegral_congr hR, lintegral_indicator measurableSet_Ioi]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) => ?_)
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hr2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have hΦs : Φ s = ENNReal.ofReal ((Real.sqrt s ^ r)⁻¹) *
        ∫⁻ u, ∫⁻ v, densRect N r (v - s⁻¹ • outerU u) * f (asm s u v) := by
      simp only [hΦdef]
      rw [lintegral_cols_split_rect (G := fun Y => f (gramU (Fin.cons (Fin.cons (Real.sqrt s) 0 :
        Fin (N + 1) → ℝ) Y : Fin (r + 1) → Fin (N + 1) → ℝ)))
        (hf.comp (continuous_gramU.comp (by fun_prop)).measurable)]
      simp only [gramU_cons_rect, hr2]
      have h1 : ∀ w : Fin r → ℝ, ∫⁻ Z : Fin r → Fin N → ℝ,
          f (asm s (Real.sqrt s • w) (outerU w + gramU Z)) =
            ∫⁻ v, densRect N r (v - outerU w) * f (asm s (Real.sqrt s • w) v) := by
        intro w
        rw [lintegral_gramRect_aux r N hrN (f := fun u => f (asm s (Real.sqrt s • w) (outerU w + u)))
          (hf.comp (measurable_asm.comp (measurable_const.prodMk (measurable_const.prodMk
            (measurable_const.add measurable_id)))))]
        rw [← lintegral_add_left_eq_self (fun v => densRect N r (v - outerU w) *
          f (asm s (Real.sqrt s • w) v)) (outerU w)]
        simp only [add_sub_cancel_left]
      rw [lintegral_congr h1]
      have h2 := lintegral_comp_smul_pi hr (G := fun u => ∫⁻ v, densRect N r (v - outerU ((Real.sqrt s)⁻¹ • u)) *
        f (asm s u v)) (Measurable.lintegral_prod_right'
          (f := fun p : (Fin r → ℝ) × (UIdx r → ℝ) =>
            densRect N r (p.2 - outerU ((Real.sqrt s)⁻¹ • p.1)) * f (asm s p.1 p.2))
          (Measurable.mul ((measurable_densRect N r).comp (Continuous.measurable
            (f := fun p : (Fin r → ℝ) × (UIdx r → ℝ) => p.2 - outerU ((Real.sqrt s)⁻¹ • p.1))
            (continuous_snd.sub (continuous_outerU.comp ((continuous_const_smul _).comp continuous_fst)))))
            (hf.comp (measurable_asm.comp (measurable_const.prodMk measurable_id)))))
      simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h2
      rw [h2]; simp only [outerU_smul, inv_pow, hr2]
    rw [hΦs, ← mul_assoc, ← ENNReal.ofReal_mul
      (mul_nonneg (kap_pos _ (by omega)).le (Real.rpow_nonneg hs.le _)), rpow_aux_rect hs,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun u => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun v => ?_
    simp only [F, mul_assoc]

/-- **The rectangular Gram disintegration** (Siegel 1935, §1 [unverified locator]; the Wishart integral): for $r \le N$ and
every measurable $f \ge 0$ on the upper coordinates $t = (t_{ij})_{0 \le i \le j < r}$ of symmetric $r \times r$ matrices,
$$\int_{(\mathbb R^N)^r}f\big((X_i \cdot X_j)_{i \le j}\big)\,dX = \int f(t)\,\rho_{N,r}(t)\,dt,\qquad
\rho_{N,r} = \texttt{densRect}\ N\ r,$$
where $X = (X_0, \dots, X_{r-1})$ with $X_j \in \mathbb R^N$. Unconditional. -/
@[kb "siegel1935" "§1 (the Gram map of rectangular matrices) [unverified]"]
theorem lintegral_gramRect : ∀ (N r : ℕ), r ≤ N → ∀ {f : (UIdx r → ℝ) → ℝ≥0∞}, Measurable f →
    ∫⁻ X : Fin r → Fin N → ℝ, f (gramU X) = ∫⁻ t, densRect N r t * f t :=
  fun N r h _ hf => lintegral_gramRect_aux r N h hf

/-- **The product of constants** $\prod_{j<r}\kappa_{N-j}$ in the density of the rectangular Gram map
($\kappa_M = \pi^{M/2}/\Gamma(M/2)$, `kap`; natural subtraction, harmless for $r \le N$). -/
def cprodRect (N r : ℕ) : ℝ := ∏ j ∈ Finset.range r, kap (N - j)

/-- The constant `cprodRect N r` is positive for $r \le N$. -/
theorem cprodRect_pos {N r : ℕ} (h : r ≤ N) : 0 < cprodRect N r :=
  Finset.prod_pos fun j hj => kap_pos _ (by have := Finset.mem_range.1 hj; omega)

/-- **The density is $\prod_{j<r}\kappa_{N-j}\det(t)^{(N-r-1)/2}$ on positive definite matrices:** if $r \le N$ and $t$ has positive
Schur pivots (`piv`) then $\det t > 0$ and $\rho_{N,r}(t) = \prod_{j<r}\kappa_{N-j}\cdot\det(t)^{(N-r-1)/2}$. -/
@[kb "siegel1935" "§1 (the Gram map of rectangular matrices) [unverified]"]
theorem densRect_of_piv : ∀ (N r : ℕ) (t : UIdx r → ℝ), r ≤ N → piv r t →
    0 < (symU t).det ∧
      densRect N r t = ENNReal.ofReal (cprodRect N r * (symU t).det ^ (((N : ℝ) - r - 1) / 2))
  | N, 0, t, _, _ => by simp [densRect, cprodRect, Matrix.det_isEmpty]
  | 0, r + 1, t, h, _ => absurd h (by omega)
  | N + 1, r + 1, t, h, ⟨hs, hp⟩ => by
    obtain ⟨hd, he⟩ := densRect_of_piv N r _ (by omega) hp
    rw [det_symU_succ t hs.ne']
    refine ⟨mul_pos hs hd, ?_⟩
    have e : ((N + 1 : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) - 1 = (N : ℝ) - r - 1 := by push_cast; ring
    have hk : 0 ≤ kap (N + 1) * sU t ^ (((N : ℝ) - r - 1) / 2) :=
      mul_nonneg (kap_pos _ (by omega)).le (Real.rpow_nonneg hs.le _)
    have hc : cprodRect (N + 1) (r + 1) = kap (N + 1) * cprodRect N r := by
      unfold cprodRect
      rw [Finset.prod_range_succ', mul_comm]
      simp [Nat.add_sub_add_right]
    rw [e, densRect, if_pos hs]
    have e2 : ((((N + 1 : ℕ) : ℝ) - 1 - r) / 2 - 1 / 2) = ((N : ℝ) - r - 1) / 2 := by push_cast; ring
    rw [e2, he, ← ENNReal.ofReal_mul hk, Real.mul_rpow hs.le hd.le, hc]
    congr 1; ring

/-- **The density vanishes off the pivot set:** if $t$ does not have positive Schur pivots then $\rho_{N,r}(t) = 0$. -/
theorem densRect_eq_zero_of_not_piv : ∀ (N r : ℕ) (t : UIdx r → ℝ), ¬ piv r t → densRect N r t = 0
  | N, 0, t, h => absurd trivial h
  | 0, r + 1, t, _ => by simp [densRect]
  | N + 1, r + 1, t, h => by
    by_cases hs : 0 < sU t
    · have hp : ¬ piv r (schurU t) := fun hp => h ⟨hs, hp⟩
      rw [densRect, if_pos hs, densRect_eq_zero_of_not_piv N r _ hp, mul_zero]
    · rw [densRect, if_neg hs]

/-- **The density is finite:** $\rho_{N,r}(t) \ne \infty$. -/
theorem densRect_ne_top : ∀ (N r : ℕ) (t : UIdx r → ℝ), densRect N r t ≠ ⊤
  | N, 0, t => by simp [densRect]
  | 0, r + 1, t => by simp [densRect]
  | N + 1, r + 1, t => by
    rw [densRect]
    split_ifs
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (densRect_ne_top N r _)
    · exact ENNReal.zero_ne_top

/-- **Upper bound on the density:** for $r + 1 \le N$, $\rho_{N,r}(t) \le \prod_{j<r}\kappa_{N-j}\,|\det t|^{(N-r-1)/2}$
(as real numbers; equality on positive definite $t$, and $0$ elsewhere). -/
theorem densRect_le (N r : ℕ) (hr : r + 1 ≤ N) (t : UIdx r → ℝ) :
    (densRect N r t).toReal ≤ cprodRect N r * |(symU t).det| ^ (((N : ℝ) - r - 1) / 2) := by
  have hc := cprodRect_pos (show r ≤ N by omega)
  by_cases hp : piv r t
  · obtain ⟨hd, he⟩ := densRect_of_piv N r t (by omega) hp
    rw [he, ENNReal.toReal_ofReal (mul_nonneg hc.le (Real.rpow_nonneg hd.le _)), abs_of_pos hd]
  · rw [densRect_eq_zero_of_not_piv N r t hp, ENNReal.toReal_zero]
    exact mul_nonneg hc.le (Real.rpow_nonneg (abs_nonneg _) _)

/-- **The push-forward of Lebesgue measure under the rectangular Gram map** (measure form of `lintegral_gramRect`):
$\mathrm{Gram}_*(dX) = \rho_{N,r}(t)\,dt$ for $r \le N$. -/
theorem map_gramRect (N r : ℕ) (hr : r ≤ N) :
    Measure.map (gramU : (Fin r → Fin N → ℝ) → UIdx r → ℝ) volume =
      volume.withDensity (densRect N r) := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply continuous_gramU.measurable hA, withDensity_apply _ hA,
    ← lintegral_indicator_one (μ := (volume : Measure (Fin r → Fin N → ℝ)))
      (hA.preimage continuous_gramU.measurable)]
  have h1 : ∀ X : Fin r → Fin N → ℝ,
      (gramU ⁻¹' A).indicator (1 : (Fin r → Fin N → ℝ) → ℝ≥0∞) X = A.indicator 1 (gramU X) := by
    intro X; by_cases h : gramU X ∈ A <;> simp [h]
  simp_rw [h1]
  rw [lintegral_gramRect N r hr (measurable_one.indicator hA), ← lintegral_indicator hA]
  refine lintegral_congr fun t => ?_
  by_cases h : t ∈ A <;> simp [h]

/-- The weighted Gram vector is the plain Gram vector after applying a factor $P$ of $H$ to each vector. -/
theorem gramH_eq_gramU_rect {N r : ℕ} {H P : Matrix (Fin N) (Fin N) ℝ}
    (hP : ∀ x y, x ⬝ᵥ (H *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) (B : Fin r → Fin N → ℝ) :
    gramH H B = gramU (fun j => P *ᵥ B j) := by
  funext p; exact hP _ _

/-- **The weighted rectangular Gram disintegration:** for a positive definite $N \times N$ matrix $H$ and $r \le N$,
$$\int_{(\mathbb R^N)^r}f\big((X_i^{\mathsf T}HX_j)_{i \le j}\big)\,dX = \det(H)^{-r/2}\int f(t)\,\rho_{N,r}(t)\,dt.$$
Unconditional. -/
@[kb "siegel1935" "§1 (the Gram map of rectangular matrices) [unverified]"]
theorem lintegral_gramRectH {N r : ℕ} (hr : r ≤ N) {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.PosDef)
    {f : (UIdx r → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ X : Fin r → Fin N → ℝ, f (gramH H X) =
      ENNReal.ofReal (H.det ^ (-(r : ℝ) / 2)) * ∫⁻ t, densRect N r t * f t := by
  obtain ⟨P, hP, hd, hdP⟩ := exists_factor_posDef hH
  have hP0 : P.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdP; exact (Real.sqrt_pos.2 hd).ne' hdP.symm
  have hfg : Measurable fun Y : Fin r → Fin N → ℝ => f (gramU Y) :=
    hf.comp continuous_gramU.measurable
  have : ∀ B : Fin r → Fin N → ℝ, f (gramH H B) = f (gramU (fun j => P *ᵥ B j)) := fun B => by
    rw [gramH_eq_gramU_rect hP]
  have key : ENNReal.ofReal (|P.det|⁻¹) ^ r = ENNReal.ofReal (H.det ^ (-(r : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [hdP, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hd.le]
    congr 1; ring
  simp_rw [this]
  rw [lintegral_comp_mulVec_rect P hP0 (G := fun Y => f (gramU Y)) hfg, lintegral_gramRect N r hr hf, key]

/-- **The push-forward of Lebesgue measure under the weighted rectangular Gram map** (measure form of
`lintegral_gramRectH`): $\det(H)^{-r/2}\rho_{N,r}(t)\,dt$. -/
theorem map_gramRectH {N r : ℕ} (hr : r ≤ N) {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.PosDef) :
    Measure.map (gramH H : (Fin r → Fin N → ℝ) → UIdx r → ℝ) volume =
      ENNReal.ofReal (H.det ^ (-(r : ℝ) / 2)) • volume.withDensity (densRect N r) := by
  obtain ⟨P, hP, hd, hdP⟩ := exists_factor_posDef hH
  have hgm : Measurable (gramH H : (Fin r → Fin N → ℝ) → UIdx r → ℝ) := by
    have : (gramH H : (Fin r → Fin N → ℝ) → UIdx r → ℝ) = fun B => gramU (fun j => P *ᵥ B j) :=
      funext fun B => gramH_eq_gramU_rect hP B
    rw [this]
    refine continuous_gramU.measurable.comp ?_
    exact measurable_pi_iff.mpr fun j =>
      ((Matrix.toLin' P).continuous_of_finiteDimensional.measurable).comp (measurable_pi_apply j)
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hgm hA, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul,
    ← lintegral_indicator_one (μ := (volume : Measure (Fin r → Fin N → ℝ))) (hgm hA)]
  have h1 : ∀ X : Fin r → Fin N → ℝ,
      (gramH H ⁻¹' A).indicator (1 : (Fin r → Fin N → ℝ) → ℝ≥0∞) X = A.indicator 1 (gramH H X) := by
    intro X; by_cases h : gramH H X ∈ A <;> simp [h]
  simp_rw [h1]
  rw [lintegral_gramRectH hr hH (measurable_one.indicator hA), ← lintegral_indicator hA]
  congr 1
  refine lintegral_congr fun t => ?_
  by_cases h : t ∈ A <;> simp [h]

end QuadFormsKB.SiegelWeil.Forms.ArchR
