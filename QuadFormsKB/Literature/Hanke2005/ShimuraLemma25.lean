/-
# Shimura 1999, Lemma 2.5: units are spinor norms of the stabilizer of a maximal lattice

**Layer:** local spinor norms $\sigma:SO(V)(F_v)\to F_v^\times/F_v^{\times2}$ of `Lattices/SpinorNorm.lean`, for
$Q = Q_0\otimes F$ with $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables whose lattice
$\mathcal O_F^n$ is $\mathcal O_F$-maximal (`StdIsMaximal`), at a finite place $v$ with integers $\mathfrak o_v$.

Shimura (1999, Lemma 2.5, pp. 8–9): for $C_v^+=\{\alpha\in G_v: L_v\alpha=L_v\}$, $G=SO(V)$, one has
$\mathfrak o_v^\times\subseteq\sigma(C_v^+)$ except when $n=2$ and $\varphi_v$ is anisotropic.

**Proves**
* **`shimuraLemma25_isotropic`**: if $n\ge1$ and $Q$ is isotropic over $F_v$, then for every unit $u\in\mathfrak o_v^\times$
  there is $g\in SO(V)(F_v)$ with $g\,\mathfrak o_v^n=\mathfrak o_v^n$ and $\sigma(g)=u\,F_v^{\times2}$;
* **`shimuraLemma25_anisotropic`**: the same for $n\ge3$ when $Q$ is anisotropic over $F_v$ (O'Meara 91:1,
  `OMeara.mem_iff_of_isMaximal`: the maximal lattice is $\{Q\in\mathfrak o_v\}$, preserved by all of $O(V_v)$; then
  `exists_so_spinorNorm_local`);
* **`shimuraLemma25`** (headline, unconditional): for $n\ge3$, every finite place $v$ and unit $u$, the two cases combined.

*Route (isotropic case):* maximality of $\mathfrak o_v^n$ and isotropy give $e,f\in\mathfrak o_v^n$ with $Q(e)=Q(f)=0$, $B(e,f)=1$
(`exists_hyperbolic_pair`); then $x=e-uf$ and $y=e-f$ satisfy $Q(x)=-u$, $Q(y)=-1$, both are unit vectors of
$\mathfrak o_v^n$, so $\tau_x,\tau_y$ stabilize $\mathfrak o_v^n$ (`symm_mem_stdStab`) and $g=\tau_x\tau_y$ is a rotation
with spinor norm $u$.
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelShape
import QuadFormsKB.Literature.Hanke2005.SpinorSurjLocal
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity QuadFormsKB.Hanke2005

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A rotation in $\mathfrak o_v$-stabilizer with spinor norm $u$ at an isotropic place** (Shimura 1999, Lemma 2.5,
isotropic case): let $Q_0$ be nondegenerate over $\mathcal O_F$ with $\mathcal O_F^n$ maximal (`StdIsMaximal`),
$v$ a finite place, $u\in F_v$ with $|u|_v=1$, and suppose $Q=Q_0\otimes F$ has a nonzero isotropic vector
$y\in F_v^n$ ($Q(y)=0$). Then some $g\in SO(V)(F_v)$ stabilizes $\mathfrak o_v^n$ and has $\sigma(g)=u\,F_v^{\times2}$. -/
@[kb "shimura1999" "Lemma 2.5, pp. 8–9 (isotropic case)"]
theorem shimuraLemma25_isotropic (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀)
    {y : Fin n → Fv} (hy : y ≠ 0) (hy0 : (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv y = 0)
    {u : Fv} (hu : Valued.v u = 1) :
    ∃ g ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v ⊓ soSub (Q₀.map (algebraMap (𝓞 F) F)) Fv,
      spinorNorm (Q₀.map (algebraMap (𝓞 F) F)) Fv g = sqClassOf u := by
  set Q := Q₀.map (algebraMap (𝓞 F) F) with hQdef
  have MP := maxProp_Qp v Q₀ hQ hmax
  have hy' : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).eval y = 0 := by
    rw [Tamagawa.map_Qp_eq, ← evalIn_eq_eval_map]; exact hy0
  obtain ⟨e, f, he, hf, hef⟩ := exists_hyperbolic_pair v (NF.Qp v Q₀) MP hy hy'
  set ε : Fin n → Fv := fun i => (e i : Fv) with hε
  set φ : Fin n → Fv := fun i => (f i : Fv) with hφ
  have hεq : Q.evalIn Fv ε = 0 := by rw [hQdef, hε, evalIn_coe_o, he]; simp
  have hφq : Q.evalIn Fv φ = 0 := by rw [hQdef, hφ, evalIn_coe_o, hf]; simp
  have hεφ : qbil Q Fv ε φ = 1 := by
    rw [qbil_eq_polar]
    have h3 : Q.evalIn Fv (fun i => ((e + f) i : Fv)) = (((NF.Qp v Q₀).eval (e + f) : 𝔬) : Fv) :=
      evalIn_coe_o v Q₀ (e + f)
    have : ε + φ = fun i => ((e + f) i : Fv) := by funext i; simp [hε, hφ]
    rw [this, h3, eval_add_hessian, he, hf, hef, hεq, hφq]
    simp
  have hφε : qbil Q Fv φ ε = 1 := by rw [qbil_comm]; exact hεφ
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  have hεs : ε ∈ std v := mem_std_of_le_one v fun i => valued_le_one_of_mem v (e i)
  have hφs : φ ∈ std v := mem_std_of_le_one v fun i => valued_le_one_of_mem v (f i)
  have hu1 : Valued.v u ≤ 1 := hu.le
  -- the vectors
  have hxs : ε - u • φ ∈ std v := by
    refine mem_std_of_le_one v fun i => ?_
    have := v_le_one_of_mem_std v hφs i
    have h' := v_le_one_of_mem_std v hεs i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (Valuation.map_sub _ _ _).trans (max_le h' ?_)
    rw [map_mul]; exact mul_le_one' hu1 this
  have hys : ε - φ ∈ std v := (std v).sub_mem hεs hφs
  have hεε : qbil Q Fv ε ε = 0 := by rw [qbil_self, hεq, mul_zero]
  have hφφ : qbil Q Fv φ φ = 0 := by rw [qbil_self, hφq, mul_zero]
  have hQx : Q.evalIn Fv (ε - u • φ) = -u := by
    have k := qbil_self Q Fv (ε - u • φ)
    simp only [qbil_sub_left, qbil_sub_right, qbil_smul_left, qbil_smul_right, hεε, hφφ, hεφ, hφε] at k
    apply mul_left_cancel₀ h2
    linear_combination -k
  have hQy : Q.evalIn Fv (ε - φ) = -1 := by
    have k := qbil_self Q Fv (ε - φ)
    simp only [qbil_sub_left, qbil_sub_right, hεε, hφφ, hεφ, hφε] at k
    apply mul_left_cancel₀ h2
    linear_combination -k
  have hvx : Valued.v (Q.evalIn Fv (ε - u • φ)) = 1 := by rw [hQx, Valuation.map_neg, hu]
  have hvy : Valued.v (Q.evalIn Fv (ε - φ)) = 1 := by rw [hQy, Valuation.map_neg, map_one]
  have hyne : Q.evalIn Fv (ε - φ) ≠ 0 := by rw [hQy]; norm_num
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hQ' : Q.Nondegenerate := nondegenerate_map Q₀ hQ
  have hs1 := symm_mem_stdStab v Q₀ hxs hvx
  have hs2 := symm_mem_stdStab v Q₀ hys hvy
  have hx0 : Q.evalIn Fv (ε - u • φ) ≠ 0 := by rw [hQx]; simpa using hu0
  refine ⟨symm Q Fv (ε - u • φ) * symm Q Fv (ε - φ), Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hs1 hs2, ?_⟩, ?_⟩
  · rw [mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q Fv hx0, symm_det Q Fv hyne]
    norm_num
  · have := spinorNorm_symmProd Q Fv hQ' [ε - u • φ, ε - φ]
      (by intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl <;> assumption)
    simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at this
    rw [this, hQx, hQy, show -u * -1 = u by ring]


/-- **Anisotropic places** (Shimura 1999, Lemma 2.5, case $\varphi_v$ anisotropic, $n\ge3$): let $Q_0$ be nondegenerate over
$\mathcal O_F$ with $\mathcal O_F^n$ maximal (`StdIsMaximal`), $n\ge3$, $v$ a finite place at which $Q=Q_0\otimes F$ is
anisotropic over $F_v$ ($Q(y)=0\Rightarrow y=0$ for $y\in F_v^n$), and $u\in F_v$ with $|u|_v=1$. Then some
$g\in SO(V)(F_v)$ stabilizes $\mathfrak o_v^n$ and has $\sigma(g)=u\,F_v^{\times2}$.
*Proof:* by O'Meara 91:1 (`OMeara.mem_iff_of_isMaximal`) $\mathfrak o_v^n=\{x:|Q(x)|_v\le1\}$, which every isometry
preserves; so $C_v^+=SO(V)(F_v)$, and $\sigma$ is onto $F_v^\times$ (`exists_so_spinorNorm_local`). -/
@[kb "shimura1999" "Lemma 2.5, pp. 8–9 (anisotropic case, n ≥ 3)"]
theorem shimuraLemma25_anisotropic (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀)
    (han : ∀ y : Fin n → Fv, (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv y = 0 → y = 0)
    {u : Fv} (hu : Valued.v u = 1) :
    ∃ g ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v ⊓ soSub (Q₀.map (algebraMap (𝓞 F) F)) Fv,
      spinorNorm (Q₀.map (algebraMap (𝓞 F) F)) Fv g = sqClassOf u := by
  set Q := Q₀.map (algebraMap (𝓞 F) F) with hQdef
  have hqv : ∀ x, qv v Q₀ x = Q.evalIn Fv x := fun x => by
    rw [qv, QuadForm.toQuadraticForm_apply, ← evalIn_eq_eval_map]
  have hA : (qv v Q₀).Anisotropic := fun x hx => han x (by rw [← hqv]; exact hx)
  have hM := isMaximal_loc v Q₀ hQ ⊤ top_ne_bot (stdLat F n) (by rw [span_image_top]; exact hmax)
  rw [ordIdeal_top, loc_intVec] at hM
  have hmem : ∀ x, x ∈ std v ↔ Valued.v (Q.evalIn Fv x) ≤ 1 := fun x => by
    have := OMeara.mem_iff_of_isMaximal (qv v Q₀) hA hM x
    rw [this, mem_pPow_iff, hqv]; simp
  have hinv : ∀ (g : orthGroup Q Fv) (x : Fin n → Fv),
      Q.evalIn Fv (((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x) = Q.evalIn Fv x := fun g x => by
    have h2 : (2 : Fv) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    rw [two_mul_evalIn_eq, two_mul_evalIn_eq]
    exact qbil_orth Q Fv g x x
  have hstab : ∀ g : orthGroup Q Fv, g ∈ stdStab Q v := fun g => by
    change locAct v (g : GL (Fin n) Fv) (std v) = std v
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hmem] at hx
      show _ ∈ std v
      rw [hmem]
      change Valued.v (Q.evalIn Fv (((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x)) ≤ 1
      rw [hinv]; exact hx
    · intro hy
      refine ⟨((g⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ y, ?_, ?_⟩
      · rw [SetLike.mem_coe]
        rw [hmem] at hy
        rw [hmem, hinv]; exact hy
      · show ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ
          (((g⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ y) = y
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
        simp
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  obtain ⟨g, hg, hgs⟩ := exists_so_spinorNorm_local Q v (nondegenerate_map Q₀ hQ) hn hu0
  exact ⟨g, Subgroup.mem_inf.mpr ⟨hstab g, hg⟩, hgs⟩

/-- **Shimura 1999, Lemma 2.5 ($n\ge3$)**: let $Q_0$ be a nondegenerate quadratic form over $\mathcal O_F$ in $n\ge3$
variables with $\mathcal O_F^n$ $\mathcal O_F$-maximal for $Q=Q_0\otimes F$ (`StdIsMaximal`), $v$ a finite place and
$u\in F_v$ with $|u|_v=1$. Then some $g\in SO(V)(F_v)$ with $g\,\mathfrak o_v^n=\mathfrak o_v^n$ has spinor norm
$\sigma(g)=u\,F_v^{\times2}$; that is, $\mathfrak o_v^\times\subseteq\sigma(C_v^+)$. Unconditional. -/
@[kb "shimura1999" "Lemma 2.5, pp. 8–9"]
theorem shimuraLemma25 (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀)
    {u : Fv} (hu : Valued.v u = 1) :
    ∃ g ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v ⊓ soSub (Q₀.map (algebraMap (𝓞 F) F)) Fv,
      spinorNorm (Q₀.map (algebraMap (𝓞 F) F)) Fv g = sqClassOf u := by
  by_cases hiso : ∃ y : Fin n → Fv, y ≠ 0 ∧ (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv y = 0
  · obtain ⟨y, hy, hy0⟩ := hiso
    exact shimuraLemma25_isotropic v Q₀ hQ hmax hy hy0 hu
  · push Not at hiso
    exact shimuraLemma25_anisotropic v hn Q₀ hQ hmax (fun y hy => by_contra fun h => hiso y h hy) hu

end Local

end QuadFormsKB.Hanke2005.SpinorIdele
