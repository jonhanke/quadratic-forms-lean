/-
# Approximation tools for strong approximation

**Layer:** $V = F^n$ over a number field $F$, its completions $F_\mathfrak p^n$ with the valuation topology, the local
lattices and the action $g \cdot M = gM$ of $\mathrm{GL}_n(F_\mathfrak p)$ (`Lattices/Genus.lean`, `Lattices/Local.lean`).

**Proves** the elementary topological facts used in O'Meara's proof of the strong approximation theorem for rotations
(O'Meara 1973, §104 and Example 101:4 [unverified]), stated with neighbourhoods so that no adelic topology is needed:
* `exists_ball_of_mem_nhds`, `ball_add_mem_nhds`: the balls $x + \mathfrak p^k\mathfrak o_\mathfrak p^n$ (`ball v k`) form a
  neighbourhood basis of $x \in F_\mathfrak p^n$;
* `exists_mem_nhds_locAct_eq` (Example 101:4): **lattice stabilizers are open** — every $\sigma \in \mathrm{GL}_n(F_\mathfrak p)$
  close enough to $h$ has $\sigma M = hM$;
* `exists_vec_approx`: **strong approximation for $F^n$** — given neighbourhoods $U_\mathfrak p$ at finitely many $\mathfrak p \in T$
  there is $y \in F^n$ in every $U_\mathfrak p$ and integral at every $\mathfrak p \notin T$
  (from `Analysis.exists_strong_approx`);
* `continuousAt_symm`: the symmetry $\tau_x$ depends continuously on an anisotropic $x$.
-/
import QuadFormsKB.Lattices.SAEqualPairs
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Analysis.AdelicPoisson

open NumberField IsDedekindDomain Matrix WithZero Topology Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Balls are a neighbourhood basis -/

/-- Every neighbourhood of $x \in F_\mathfrak p$ contains a closed ball $\{y : |y - x| \le \exp(-k)\}$. -/
theorem exists_valued_le_of_mem_nhds {x : Fv} {s : Set Fv} (hs : s ∈ 𝓝 x) :
    ∃ k : ℤ, ∀ y, Valued.v (y - x) ≤ exp (-k) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by
    intro h0
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_inj.mp (by rw [h0, map_zero]))
  refine ⟨1 - log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1), fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ
  rw [Valuation.restrict_lt_iff_lt_embedding, ← exp_log hne]
  refine lt_of_le_of_lt hy ?_
  rw [exp_lt_exp]; omega

/-- The open ball $\{u : |u| < \exp(-k)\}$ is a neighbourhood of $0$. -/
theorem valued_lt_mem_nhds_zero (k : ℤ) : {u : Fv | Valued.v u < exp (-k)} ∈ 𝓝 (0 : Fv) := by
  have h0 : {u : Fv | Valued.v u < 1} ∈ 𝓝 (0 : Fv) := Valued.mem_nhds.mpr ⟨1, by simp⟩
  have hcont : Continuous fun u : Fv => ϖk v (-k) * u := continuous_const.mul continuous_id
  have h1 := hcont.continuousAt (x := 0) (by simpa using h0)
  refine Filter.mem_of_superset h1 fun u hu => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, map_mul, valued_ϖk, neg_neg] at hu ⊢
  have : Valued.v u * exp k < exp (-k) * exp k := by
    rw [← exp_add, neg_add_cancel, exp_zero, mul_comm]; exact hu
  exact lt_of_mul_lt_mul_right' this

theorem valued_le_mem_nhds (x : Fv) (k : ℤ) : {u : Fv | Valued.v (u - x) ≤ exp (-k)} ∈ 𝓝 x := by
  have h := valued_lt_mem_nhds_zero v k
  have hcont : Continuous fun u : Fv => u - x := continuous_id.sub continuous_const
  have h1 := hcont.continuousAt (x := x) (by simpa using h)
  refine Filter.mem_of_superset h1 fun u hu => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hu
  exact le_of_lt hu

/-- **Every neighbourhood of $x \in F_\mathfrak p^n$ contains a ball $x + \mathfrak p^k\mathfrak o_\mathfrak p^n$.** -/
theorem exists_ball_of_mem_nhds {x : Fin n → Fv} {s : Set (Fin n → Fv)} (hs : s ∈ 𝓝 x) :
    ∃ k : ℤ, ∀ y, y - x ∈ ball v k → y ∈ s := by
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, -, t, ht, hIt⟩ := hs
  choose k hk using fun i => exists_valued_le_of_mem_nhds v (ht i)
  refine ⟨∑ i, |k i|, fun y hy => hIt fun i _ => hk i _ ?_⟩
  refine (hy i).trans ?_
  rw [exp_le_exp, neg_le_neg_iff]
  exact (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (k j)) (Finset.mem_univ i))

/-- **The ball $x + \mathfrak p^k\mathfrak o_\mathfrak p^n$ is a neighbourhood of $x$.** -/
theorem ball_add_mem_nhds (x : Fin n → Fv) (k : ℤ) : {y : Fin n → Fv | y - x ∈ ball v k} ∈ 𝓝 x := by
  have : {y : Fin n → Fv | y - x ∈ ball v k} = (Set.univ : Set (Fin n)).pi
      (fun i => {u : Fv | Valued.v (u - x i) ≤ exp (-k)}) := by
    ext y; simp [mem_ball]
  rw [this]
  exact set_pi_mem_nhds Set.finite_univ fun i _ => valued_le_mem_nhds v (x i) k

theorem mball_mem_nhds (A : Matrix (Fin n) (Fin n) Fv) (k : ℤ) :
    {B : Matrix (Fin n) (Fin n) Fv | ∀ i j, Valued.v (B i j - A i j) ≤ exp (-k)} ∈ 𝓝 A := by
  have : ((Set.univ : Set (Fin n)).pi (fun i => {y : Fin n → Fv | y - A i ∈ ball v k}) :
      Set (Fin n → Fin n → Fv)) ∈ 𝓝 (show Fin n → Fin n → Fv from A) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ball_add_mem_nhds v (A i) k
  refine Filter.mem_of_superset this fun B hB i j => ?_
  exact hB i (Set.mem_univ i) j

/-! ### Lattice stabilizers are open -/

/-- An entrywise-small matrix maps balls to smaller balls. -/
theorem mulVec_mem_ball {A : Matrix (Fin n) (Fin n) Fv} {k k' : ℤ} (hA : ∀ i j, Valued.v (A i j) ≤ exp (-k))
    {y : Fin n → Fv} (hy : y ∈ ball v k') : A *ᵥ y ∈ ball v (k + k') := by
  intro i
  rw [mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, neg_add, exp_add]
  exact mul_le_mul' (hA i j) (hy j)

theorem continuousAt_matrix_inv' {A : Matrix (Fin n) (Fin n) Fv} (hA : A.det ≠ 0) :
    ContinuousAt (fun B : Matrix (Fin n) (Fin n) Fv => B⁻¹) A := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hA

/-- **Lattice stabilizers are open** (O'Meara 1973, Example 101:4 [unverified]): for $h \in \mathrm{GL}_n(F_\mathfrak p)$ and a
lattice $M \subseteq F_\mathfrak p^n$, every $\sigma \in \mathrm{GL}_n(F_\mathfrak p)$ in a neighbourhood of $h$ has $\sigma M = hM$. -/
theorem exists_mem_nhds_locAct_eq (h : GL (Fin n) Fv) {M : Submodule 𝔬 (Fin n → Fv)} (hM : M.IsLattice Fv) :
    ∃ U ∈ 𝓝 (h : Matrix (Fin n) (Fin n) Fv), ∀ σ : GL (Fin n) Fv,
      (σ : Matrix (Fin n) (Fin n) Fv) ∈ U → locAct v σ M = locAct v h M := by
  obtain ⟨a, ha1, ha2⟩ := exists_local_bounds v hM
  obtain ⟨b, hb1, hb2⟩ := exists_local_bounds v (locAct_isLattice (v := v) h hM)
  have hdet : (h : Matrix (Fin n) (Fin n) Fv).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  set U₁ := {B : Matrix (Fin n) (Fin n) Fv | ∀ i j, Valued.v (B i j - (h : Matrix (Fin n) (Fin n) Fv) i j) ≤ exp (-((a : ℤ) + b))}
  set U₂ := (fun B : Matrix (Fin n) (Fin n) Fv => B⁻¹) ⁻¹'
    {B | ∀ i j, Valued.v (B i j - ((h : Matrix (Fin n) (Fin n) Fv))⁻¹ i j) ≤ exp (-((a : ℤ) + b))}
  refine ⟨U₁ ∩ U₂, Filter.inter_mem (mball_mem_nhds v _ _)
    ((continuousAt_matrix_inv' v hdet).preimage_mem_nhds (mball_mem_nhds v _ _)), ?_⟩
  rintro σ ⟨h1, h2⟩
  apply le_antisymm
  · -- `σM ⊆ hM`
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ball v (-(a : ℤ)) := ha2 hy
    have hd : ((σ : Matrix (Fin n) (Fin n) Fv) - (h : Matrix (Fin n) (Fin n) Fv)) *ᵥ y ∈ ball v ((a : ℤ) + b + -(a : ℤ)) :=
      mulVec_mem_ball v (fun i j => by simpa using h1 i j) hy'
    have hd' : ((σ : Matrix (Fin n) (Fin n) Fv) - (h : Matrix (Fin n) (Fin n) Fv)) *ᵥ y ∈ locAct v h M := hb1 (by
      rwa [show (a : ℤ) + b + -(a : ℤ) = b by ring] at hd)
    have hhy : (h : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ locAct v h M := ⟨y, hy, rfl⟩
    have : (σ : Matrix (Fin n) (Fin n) Fv) *ᵥ y = (h : Matrix (Fin n) (Fin n) Fv) *ᵥ y + ((σ : Matrix (Fin n) (Fin n) Fv) - (h : Matrix (Fin n) (Fin n) Fv)) *ᵥ y := by
      rw [sub_mulVec]; abel
    change (σ : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ _
    rw [this]; exact Submodule.add_mem _ hhy hd'
  · -- `hM ⊆ σM`, via `σ⁻¹ h M ⊆ M`
    rintro _ ⟨y, hy, rfl⟩
    set x := (h : Matrix (Fin n) (Fin n) Fv) *ᵥ y
    have hx : x ∈ locAct v h M := ⟨y, hy, rfl⟩
    have hx' : x ∈ ball v (-(b : ℤ)) := hb2 hx
    have hinv : ((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ = ((σ⁻¹ : GL (Fin n) Fv) : Matrix _ _ _) := (Matrix.coe_units_inv σ).symm
    have hinvh : ((h : Matrix (Fin n) (Fin n) Fv))⁻¹ = ((h⁻¹ : GL (Fin n) Fv) : Matrix _ _ _) := (Matrix.coe_units_inv h).symm
    have h2' : ∀ i j, Valued.v ((((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ - ((h : Matrix (Fin n) (Fin n) Fv))⁻¹) i j) ≤ exp (-((a : ℤ) + b)) :=
      fun i j => by simpa using h2 i j
    have hd : (((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ - ((h : Matrix (Fin n) (Fin n) Fv))⁻¹) *ᵥ x ∈ ball v ((a : ℤ) + b + -(b : ℤ)) :=
      mulVec_mem_ball v h2' hx'
    have hd' : (((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ - ((h : Matrix (Fin n) (Fin n) Fv))⁻¹) *ᵥ x ∈ M := ha1 (by
      rwa [show (a : ℤ) + b + -(b : ℤ) = a by ring] at hd)
    have hhx : ((h : Matrix (Fin n) (Fin n) Fv))⁻¹ *ᵥ x = y := by
      rw [hinvh, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]; simp
    refine ⟨((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ *ᵥ x, ?_, ?_⟩
    · have : ((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ *ᵥ x = y + (((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ - ((h : Matrix (Fin n) (Fin n) Fv))⁻¹) *ᵥ x := by
        rw [sub_mulVec, hhx]; abel
      rw [this]; exact Submodule.add_mem _ hy hd'
    · change (σ : Matrix (Fin n) (Fin n) Fv) *ᵥ (((σ : Matrix (Fin n) (Fin n) Fv))⁻¹ *ᵥ x) = x
      rw [hinv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]; simp

/-- **$O(\mathfrak o_\mathfrak p^n)$ is open:** isometries close to $1$ stabilize $\mathfrak o_\mathfrak p^n$. -/
theorem exists_mem_nhds_stdStab (Q : QuadForm F n) :
    ∃ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) Fv), ∀ σ : orthGroup Q Fv,
      ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ∈ U → σ ∈ stdStab Q v := by
  obtain ⟨U, hU, hUσ⟩ := exists_mem_nhds_locAct_eq v 1 (isLattice_of_bounds v (le_refl (std v)) (le_refl (std v)))
  refine ⟨U, by simpa using hU, fun σ hσ => ?_⟩
  change locAct v _ (std v) = std v
  rw [hUσ _ hσ, locAct_one]

/-! ### Continuity of $Q$ and of symmetries -/

theorem continuous_evalIn (Q : QuadForm F n) : Continuous fun x : Fin n → Fv => Q.evalIn Fv x := by
  unfold QuadForm.evalIn
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact (continuous_const.mul (continuous_apply i)).mul (continuous_apply j)
  · exact continuous_const

theorem continuous_mulVec (A : Matrix (Fin n) (Fin n) Fv) : Continuous fun x : Fin n → Fv => A *ᵥ x := by
  refine continuous_pi fun i => ?_
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

/-- **The symmetry $\tau_y$ depends continuously on $y$ near an anisotropic $x$.** -/
theorem continuousAt_symm (Q : QuadForm F n) {x : Fin n → Fv} (hx : Q.evalIn Fv x ≠ 0) :
    ContinuousAt (fun y => ((symm Q Fv y : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)) x := by
  have hopen : {y : Fin n → Fv | Q.evalIn Fv y ≠ 0} ∈ 𝓝 x :=
    (continuous_evalIn v Q).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hx)
  have hev : (fun y => QuadForm.reflMat y (symmVec Q Fv y)) =ᶠ[𝓝 x]
      fun y => ((symm Q Fv y : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) := by
    filter_upwards [hopen] with y hy
    exact (symm_val Q Fv hy).symm
  refine ContinuousAt.congr ?_ hev
  have hQ : ContinuousAt (fun y => (Q.evalIn Fv y)⁻¹) x := (continuous_evalIn v Q).continuousAt.inv₀ hx
  have hH := (continuous_mulVec v (Q.hessian.map (algebraMap F Fv))).continuousAt (x := x)
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  simp only [QuadForm.reflMat, symmVec, Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  exact continuousAt_const.sub ((continuous_apply i).continuousAt.mul
    (hQ.mul ((continuous_apply j).continuousAt.comp hH)))

theorem continuous_mulVec_joint :
    Continuous (fun p : Matrix (Fin n) (Fin n) Fv × (Fin n → Fv) => p.1 *ᵥ p.2) := by
  refine continuous_pi fun i => ?_
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => ((continuous_apply j).comp ((continuous_apply i).comp
    continuous_fst)).mul ((continuous_apply j).comp continuous_snd)

theorem continuousAt_mulVec_of {X : Type*} [TopologicalSpace X]
    {M : X → Matrix (Fin n) (Fin n) Fv} {y : X → Fin n → Fv} {x₀ : X}
    (hM : ContinuousAt M x₀) (hy : ContinuousAt y x₀) : ContinuousAt (fun x => M x *ᵥ y x) x₀ := by
  have := (continuous_mulVec_joint v).continuousAt.comp (hM.prodMk hy)
  exact this

theorem continuous_matmul_joint :
    Continuous (fun p : Matrix (Fin n) (Fin n) Fv × Matrix (Fin n) (Fin n) Fv => p.1 * p.2) := by
  refine continuous_matrix fun i j => ?_
  simp only [mul_apply]
  exact continuous_finsetSum _ fun k _ => (continuous_fst.matrix_elem i k).mul (continuous_snd.matrix_elem k j)

theorem continuousAt_matmul_of {X : Type*} [TopologicalSpace X]
    {M N : X → Matrix (Fin n) (Fin n) Fv} {x₀ : X}
    (hM : ContinuousAt M x₀) (hN : ContinuousAt N x₀) : ContinuousAt (fun x => M x * N x) x₀ := by
  have := (continuous_matmul_joint v).continuousAt.comp (hM.prodMk hN)
  exact this

end Local

/-! ### Global approximation -/

theorem locVec_apply' (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → F) (i : Fin n) :
    locVec v y i = algebraMap F (v.adicCompletion F) (y i) := rfl

theorem locVec_eq (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → F) :
    locVec v y = fun i => algebraMap F (v.adicCompletion F) (y i) := rfl

theorem orthMap_symm_locVec (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → F) :
    orthMap Q (v.adicCompletion F) (symm Q F x) = symm Q (v.adicCompletion F) (locVec v x) :=
  orthMap_symm Q v x

/-- **Strong approximation for $F^n$:** for a finite set $T$ of finite primes and neighbourhoods $U_\mathfrak p$ of
$x_\mathfrak p \in F_\mathfrak p^n$ ($\mathfrak p \in T$) there is $y \in F^n$ with $y \in U_\mathfrak p$ for $\mathfrak p \in T$ and
$y \in \mathfrak o_\mathfrak p^n$ for $\mathfrak p \notin T$. -/
theorem exists_vec_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (x : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F)) (hU : ∀ v ∈ T, U v ∈ 𝓝 (x v)) :
    ∃ y : Fin n → F, (∀ v ∈ T, locVec v y ∈ U v) ∧ ∀ v ∉ T, locVec v y ∈ std v := by
  classical
  choose! k hk using fun v (hv : v ∈ T) => exists_ball_of_mem_nhds v (hU v hv)
  have : ∀ i : Fin n, ∃ ξ : F,
      (∀ v ∈ T, Valued.v (algebraMap F (v.adicCompletion F) ξ - x v i) ≤ exp (-k v)) ∧
        ∀ v ∉ T, Valued.v (algebraMap F (v.adicCompletion F) ξ) ≤ 1 :=
    fun i => Analysis.exists_strong_approx T (fun v => x v i) k
  choose y hy1 hy2 using this
  refine ⟨y, fun v hv => hk v hv _ fun i => hy1 i v hv, fun v hv i => ?_⟩
  rw [neg_zero, exp_zero]
  exact hy2 i v hv

/-- **Strong approximation for $F$.** -/
theorem exists_scalar_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hU : ∀ v ∈ T, U v ∈ 𝓝 (c v)) :
    ∃ ξ : F, (∀ v ∈ T, algebraMap F (v.adicCompletion F) ξ ∈ U v) ∧
      ∀ v ∉ T, Valued.v (algebraMap F (v.adicCompletion F) ξ) ≤ 1 := by
  classical
  choose! k hk using fun v (hv : v ∈ T) => exists_valued_le_of_mem_nhds v (hU v hv)
  obtain ⟨ξ, h1, h2⟩ := Analysis.exists_strong_approx T c k
  exact ⟨ξ, fun v hv => hk v hv _ (h1 v hv), h2⟩

end QuadFormsKB.Lattices
