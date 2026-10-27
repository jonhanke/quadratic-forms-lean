/-
# Weil's local orbital identity at the primes $\mathfrak p \mid 2m$, dyadic included

**Layer:** the completions $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime $\mathfrak p$ (`LocalDensity.NF`,
`Lattices/`), with the local types of `LocalOrbital.lean`; the counting is in `OrbitCount.lean`.

Setting as in `LocalOrbital.lean`: $Q = \langle m\rangle\perp Q'$ over $\mathcal O_F$ (`splitForm m₀ Q₀'`), $L = \mathfrak o_\mathfrak p^{n+1}$, $K = O(L)$ (`stdStab`),
$H = O(Q')(F_\mathfrak p)$ acting through $\mathrm{diag}(1, \cdot)$, $Y_\mathfrak p = \{M \in O(V)L : e_0 \in M\}$, $K_0' = O(\mathfrak o_\mathfrak p^n)$,
$w(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$ (`locWeight`), $W_\mathfrak p = \sum_t w(t)$ (`locTypeSum`).

**Proves**
* `intRep` (**$K$ acts by integral isometries**) and `exists_intRep_eq` (every integral isometry of $Q$ is in $K$).
* `exists_inv_e₀`: for $x \in L$ with $Q(x) = m$ there is an involution $\sigma \in O(V)(F_\mathfrak p)$ with $\sigma e_0 = x$
  (a reflection, or $-1$ times one; `exists_refl_e₀` over the field $F_\mathfrak p$).
* `nearCount_mul_relIndex_eq` (**the weight of a type is a ratio of orbit counts**): for $x \in L$, $Q(x) = m$, an involution
  $\sigma$ with $\sigma e_0 = x$ and $M_1 = \sigma L$,
  $$N_{k,r}(Kx) = w(M_1)\cdot N_{k,r}(Ke_0)\qquad(k \gg r \gg 0).$$
  *Proof:* with $J = K \cap \sigma K\sigma$, the finite orbit comparison (`nearCount_mul_relIndex`) at $e_0$ and at $x$, the
  invariance of near counts under $\sigma$ (`nearCount_eq_of_involution`, applied to $Je_0$ and $Jx = \sigma Je_0$), and the
  identification of $[\mathrm{Stab}_K(e_0) : \cdot\cap J]$, $[\mathrm{Stab}_K(x) : \cdot \cap J]$ with $[K_0' : K_0'\cap K_{M_1}]$,
  $[K_{M_1} : K_0'\cap K_{M_1}]$ (conjugation by $\sigma$, `relIndex_stabOf_e₀`, `relIndex_stabOf_x`). Openness and saturation come
  from `exists_openMat`.
* `exists_type_data`, `mem_orbit_of_stdStab`: local types $\leftrightarrow$ $K$-orbits on $\{x \in L : Q(x) = m\}$.
* **`localTypeOrbitCount_of_invariant`**: `LocalTypeOrbitCount` at **every** prime (dyadic included), given that the local
  weights do not depend on the representative of a type (`LocWeightInvariant`, the triviality of the modular function of
  $O(Q')(F_\mathfrak p)$ on the stabilizers of lattices). `LocWeightInvariant` is proved locally in `LocalUnimodular.lean`
  (`locWeightInvariant_local`, Cartan–Dieudonné), which also states the final results (`localTypeOrbitCount_local`,
  `localOrbitalIdentityAt_local`, and the global statements without `hbad`).
* `locWeightInvariant`: an alternative, global proof of `LocWeightInvariant` at $\mathfrak p \mid 2m$, from the finiteness of the
  mass (`compWeight_smul`), for $Q$ totally positive definite.

Sources: Weil 1982, §3.4 [unverified]; Kitaoka 1993, §5.6 and §6.8 [unverified]; O'Meara 1963, §§91–93 [unverified];
Hanke 2004, §3 (local densities by counting) [unverified]. Indices are 0-based ($e_0$ is the first basis vector).
-/
import QuadFormsKB.Tamagawa.OrbitCount
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm

/-! ### $K = O(\mathfrak o_\mathfrak p^N)$ acts by integral isometries -/

section IntRep

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **An integral model** of a form $Q$ over $F$ at $\mathfrak p$: a form $Q_o$ over $\mathfrak o_\mathfrak p$ with the same values on
$\mathfrak o_\mathfrak p^N$. -/
def IsIntModel (Q : QuadForm F N) (Qo : QuadForm 𝔬 N) : Prop :=
  ∀ y : Fin N → 𝔬, Q.evalIn Fv (fun i => (y i : Fv)) = ((Qo.eval y : 𝔬) : Fv)

variable (Q : QuadForm F N)

theorem map_o_injective :
    Function.Injective (fun M : Matrix (Fin N) (Fin N) 𝔬 => M.map (algebraMap 𝔬 Fv)) :=
  fun _ _ h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)

theorem exists_intMat (κ : stdStab Q v) :
    ∃ P : Matrix (Fin N) (Fin N) 𝔬, P.map (algebraMap 𝔬 Fv) = ((κ : orthGroup Q Fv) : GL (Fin N) Fv).val := by
  obtain ⟨P₀, hP₀⟩ := exists_gl_o_of_locAct_eq v κ.2
  exact ⟨P₀.val, congrArg Units.val hP₀⟩

/-- **The integral matrix of $\kappa \in K = O(\mathfrak o_\mathfrak p^N)$.** -/
def intRep : stdStab Q v →* Matrix (Fin N) (Fin N) 𝔬 where
  toFun κ := (exists_intMat v Q κ).choose
  map_one' := map_o_injective v (by
    show (exists_intMat v Q 1).choose.map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [(exists_intMat v Q 1).choose_spec]
    simp [Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a b := map_o_injective v (by
    show (exists_intMat v Q (a * b)).choose.map _ =
      ((exists_intMat v Q a).choose * (exists_intMat v Q b).choose).map _
    rw [(exists_intMat v Q (a * b)).choose_spec, Matrix.map_mul, (exists_intMat v Q a).choose_spec,
      (exists_intMat v Q b).choose_spec]
    rfl)

theorem intRep_map (κ : stdStab Q v) :
    (intRep v Q κ).map (algebraMap 𝔬 Fv) = ((κ : orthGroup Q Fv) : GL (Fin N) Fv).val :=
  (exists_intMat v Q κ).choose_spec

theorem coe_mulVec_o (P : Matrix (Fin N) (Fin N) 𝔬) (y : Fin N → 𝔬) :
    (fun i => ((P *ᵥ y) i : Fv)) = P.map (algebraMap 𝔬 Fv) *ᵥ fun i => (y i : Fv) := by
  funext i
  exact RingHom.map_mulVec (algebraMap 𝔬 Fv) P y i

theorem coe_intRep_mulVec (κ : stdStab Q v) (y : Fin N → 𝔬) :
    (fun i => ((intRep v Q κ *ᵥ y) i : Fv)) =
      ((κ : orthGroup Q Fv) : GL (Fin N) Fv).val *ᵥ fun i => (y i : Fv) := by
  rw [coe_mulVec_o, intRep_map]

theorem coe_o_injective : Function.Injective (fun y : Fin N → 𝔬 => fun i => (y i : Fv)) :=
  fun _ _ h => funext fun i => Subtype.ext (congrFun h i)

variable {Q}

/-- $K$ acts by isometries of the integral model. -/
theorem compMat_intRep {Qo : QuadForm 𝔬 N} (hQo : IsIntModel v Q Qo) (κ : stdStab Q v) : Qo.compMat (intRep v Q κ) = Qo := by
  refine eq_of_eval_eq fun y => ?_
  apply SetLike.coe_eq_coe.mp
  rw [eval_compMat, ← hQo, ← hQo, coe_intRep_mulVec]
  exact evalIn_mulVec_of_mem Q (κ : orthGroup Q Fv).2 _

/-- **Every integral isometry is in $K$** (for a nondegenerate integral model): $X$ with $Q\circ X = Q$ has
$\det X = \pm 1$. -/
theorem exists_intRep_eq {Qo : QuadForm 𝔬 N} (hQo : IsIntModel v Q Qo) (hQ : Qo.Nondegenerate) (X : Matrix (Fin N) (Fin N) 𝔬)
    (hX : Qo.compMat X = Qo) : ∃ κ, intRep v Q κ = X := by
  have hH := congrArg QuadForm.hessian hX
  rw [hessian_compMat] at hH
  have hdet : X.det * X.det * Qo.hessian.det = Qo.hessian.det := by
    have := congrArg Matrix.det hH
    rw [det_mul, det_mul, det_transpose] at this
    linear_combination this
  have hdet1 : X.det * X.det = 1 := by
    have : (X.det * X.det - 1) * Qo.hessian.det = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hQ
  have hu : IsUnit X.det := ⟨⟨X.det, X.det, hdet1, hdet1⟩, rfl⟩
  let P₀ : GL (Fin N) 𝔬 := Matrix.nonsingInvUnit X hu
  let g : GL (Fin N) Fv := Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀
  have hgval : g.val = X.map (algebraMap 𝔬 Fv) := rfl
  have hmem : g ∈ orthGroup Q Fv := by
    refine mem_orthGroup_of_evalIn Q fun z => ?_
    refine evalIn_eq_of_evalIn_o v (A := fun z => Q.evalIn Fv (g.val *ᵥ z)) (B := Q.evalIn Fv)
      (fun c y => by simp only [mulVec_smul]; exact evalIn_smul' _ c _) (fun c y => evalIn_smul' _ c y)
      (fun y => ?_) z
    rw [hgval, ← coe_mulVec_o, hQo, hQo, ← eval_compMat, hX]
  refine ⟨⟨⟨g, hmem⟩, locAct_map_std v P₀⟩, map_o_injective v ?_⟩
  simp only
  rw [intRep_map]
  rfl

end IntRep


/-! ### The involution $\sigma_x$ and its denominators -/

section Inv

open WithZero

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

theorem evalIn_splitForm_eq_eval (z : Fin (n + 1) → Fv) :
    (QS).evalIn Fv z = (splitForm (algebraMap F Fv m) (Q'.map (algebraMap F Fv))).eval z := by
  rw [evalIn_eq_eval_map, map_splitForm]

/-- **An involution moving $e_0$ to $x$** (Witt, explicitly): for $x \in F_\mathfrak p^{n+1}$ with $Q(x) = m \ne 0$ there is
$\sigma \in O(V)(F_\mathfrak p)$ with $\sigma^2 = 1$ and $\sigma e_0 = x$: the reflection in $x - e_0$, or $-1$ times the reflection
in $x + e_0$ (`exists_refl_e₀`, over the field $F_\mathfrak p$; O'Meara 1963, §42 [unverified]). -/
theorem exists_inv_e₀ (hm : m ≠ 0) (x : Fin (n + 1) → Fv) (hx : (QS).evalIn Fv x = algebraMap F Fv m) :
    ∃ σ : orthGroup QS Fv, σ * σ = 1 ∧ (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = x := by
  have h4 : IsUnit (4 * algebraMap F Fv m) :=
    IsUnit.mk0 _ (mul_ne_zero (by norm_num) ((map_ne_zero _).mpr hm))
  rw [evalIn_splitForm_eq_eval] at hx
  obtain ⟨σ, hσQ, hσσ, hσe⟩ := exists_refl_e₀ h4 (Q'.map (algebraMap F Fv)) hx
  let g : GL (Fin (n + 1)) Fv := ⟨σ, σ, hσσ, hσσ⟩
  have hg : g ∈ orthGroup QS Fv := mem_orthGroup_of_evalIn QS fun z => by
    rw [evalIn_splitForm_eq_eval, evalIn_splitForm_eq_eval, ← eval_compMat]
    exact congrArg (fun S => QuadForm.eval S z) hσQ
  exact ⟨⟨g, hg⟩, Subtype.ext (Units.ext hσσ), hσe⟩

/-- **Clearing denominators:** $\varpi^cA$ is integral for some $c$. -/
theorem exists_scale_integral {N : ℕ} (A : Matrix (Fin N) (Fin N) Fv) :
    ∃ (c : ℕ) (A' : Matrix (Fin N) (Fin N) 𝔬),
      A'.map (algebraMap 𝔬 Fv) = ((NF.π v : 𝔬) : Fv) ^ c • A := by
  classical
  choose k hk using fun p : Fin N × Fin N => exists_valued_le v (A p.1 p.2)
  set c := Finset.univ.sup k
  have hv : ∀ i j, Valued.v (((NF.π v : 𝔬) : Fv) ^ c * A i j) ≤ 1 := by
    intro i j
    rw [map_mul, map_pow, NF.valued_π, ← WithZero.exp_nsmul]
    have hkc : k (i, j) ≤ c := Finset.le_sup (f := k) (Finset.mem_univ _)
    calc exp (c • (-1 : ℤ)) * Valued.v (A i j) ≤ exp (c • (-1 : ℤ)) * exp (k (i, j) : ℤ) :=
          mul_le_mul_right (hk (i, j)) _
      _ ≤ 1 := by
        rw [← exp_add, ← exp_zero, exp_le_exp]
        simp only [nsmul_eq_mul, mul_neg, mul_one]
        omega
  refine ⟨c, Matrix.of fun i j => toO v _ (hv i j), ?_⟩
  ext i j
  rfl

end Inv

/-! ### The subgroup $J = K \cap \sigma K \sigma$ -/

section J

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- An isometry with integral matrix and integral inverse lies in $K = O(\mathfrak o_\mathfrak p^N)$. -/
theorem mem_stdStab_of_integral (g : orthGroup Q Fv) (G₀ G₁ : Matrix (Fin N) (Fin N) 𝔬)
    (h₀ : G₀.map (algebraMap 𝔬 Fv) = (g : GL (Fin N) Fv).val)
    (h₁ : G₁.map (algebraMap 𝔬 Fv) = ((g⁻¹ : orthGroup Q Fv) : GL (Fin N) Fv).val) : g ∈ stdStab Q v := by
  have e01 : G₀ * G₁ = 1 := map_o_injective v (by
    show (G₀ * G₁).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, h₀, h₁, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      ← Subgroup.coe_mul, mul_inv_cancel]
    rfl)
  have e10 : G₁ * G₀ = 1 := map_o_injective v (by
    show (G₁ * G₀).map _ = (1 : Matrix (Fin N) (Fin N) 𝔬).map _
    rw [Matrix.map_mul, h₀, h₁, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      ← Subgroup.coe_mul, inv_mul_cancel]
    rfl)
  have := locAct_map_std v (⟨G₀, G₁, e01, e10⟩ : GL (Fin N) 𝔬)
  have hg : Matrix.GeneralLinearGroup.map (algebraMap 𝔬 Fv) (⟨G₀, G₁, e01, e10⟩ : GL (Fin N) 𝔬) =
      (g : GL (Fin N) Fv) := Units.ext h₀
  rw [hg] at this
  exact this

variable (σ : orthGroup Q (v.adicCompletion F))

/-- **$J = K \cap \sigma K \sigma^{-1}$** as a subgroup of $K$: $\kappa \in J$ iff $\sigma\kappa\sigma^{-1} \in K$. -/
def Jsub : Subgroup (stdStab Q v) where
  carrier := {κ | σ * (κ : orthGroup Q Fv) * σ⁻¹ ∈ stdStab Q v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have : σ * ((a * b : stdStab Q v) : orthGroup Q Fv) * σ⁻¹ =
        (σ * (a : orthGroup Q Fv) * σ⁻¹) * (σ * (b : orthGroup Q Fv) * σ⁻¹) := by
      rw [Subgroup.coe_mul]; group
    rw [this]; exact mul_mem ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, mul_one, mul_inv_cancel]
    exact one_mem _
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have : σ * ((a⁻¹ : stdStab Q v) : orthGroup Q Fv) * σ⁻¹ = (σ * (a : orthGroup Q Fv) * σ⁻¹)⁻¹ := by
      rw [InvMemClass.coe_inv]; group
    rw [this]; exact inv_mem ha

theorem mem_Jsub_iff (hσ : σ * σ = 1) (κ : stdStab Q v) :
    κ ∈ Jsub v Q σ ↔ σ * (κ : orthGroup Q Fv) * σ ∈ stdStab Q v := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  show σ * (κ : orthGroup Q Fv) * σ⁻¹ ∈ stdStab Q v ↔ _
  rw [hσi]


/-- Conjugating an element $\equiv 1 \bmod \pi^s$ by $\sigma$ ($\varpi^c\sigma$ integral, $\sigma^2 = 1$) gives an integral matrix
$1 + \pi^{s-2c}\sigma' E\sigma'$ when $s \ge 2c$. -/
theorem conj_val_eq (hσ : σ * σ = 1) {c : ℕ} {σ' : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)}
    (hσ' : σ'.map (algebraMap _ (v.adicCompletion F)) =
      ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c • (σ : GL (Fin N) _).val)
    {s : ℕ} (hs : 2 * c ≤ s) (γ : orthGroup Q (v.adicCompletion F))
    {G E : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)}
    (hγ : G.map (algebraMap _ (v.adicCompletion F)) = (γ : GL (Fin N) _).val) (hG : G = 1 + NF.π v ^ s • E) :
    (1 + NF.π v ^ (s - 2 * c) • (σ' * E * σ')).map (algebraMap _ (v.adicCompletion F)) =
      ((σ * γ * σ : orthGroup Q (v.adicCompletion F)) : GL (Fin N) _).val := by
  set ϖ : v.adicCompletion F := ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F)
  set Sv := (σ : GL (Fin N) (v.adicCompletion F)).val
  have hSS : Sv * Sv = 1 := by
    have := congrArg (fun g : orthGroup Q (v.adicCompletion F) => (g : GL (Fin N) (v.adicCompletion F)).val) hσ
    simpa [Sv] using this
  have hadd : ∀ a₁ a₂ : v.adicCompletionIntegers F, algebraMap _ (v.adicCompletion F) (a₁ + a₂) =
      algebraMap _ (v.adicCompletion F) a₁ + algebraMap _ (v.adicCompletion F) a₂ := fun _ _ => map_add _ _ _
  have hmap : ∀ (A : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)) (t : v.adicCompletionIntegers F),
      (t • A).map (algebraMap _ (v.adicCompletion F)) = (t : v.adicCompletion F) • A.map (algebraMap _ _) := by
    intro A t; ext i j; simp
  set Em := E.map (algebraMap _ (v.adicCompletion F))
  have hγv : (γ : GL (Fin N) _).val = 1 + ϖ ^ s • Em := by
    rw [← hγ, hG, Matrix.map_add _ hadd, Matrix.map_one _ (map_zero _) (map_one _), hmap]
    simp [ϖ, Em]
  rw [Matrix.map_add _ hadd, Matrix.map_one _ (map_zero _) (map_one _), hmap, Matrix.map_mul, Matrix.map_mul, hσ']
  simp only [Subgroup.coe_mul, Units.val_mul, hγv]
  have hpow : ((NF.π v ^ (s - 2 * c) : v.adicCompletionIntegers F) : v.adicCompletion F) * ϖ ^ c * ϖ ^ c =
      ϖ ^ s := by
    simp only [ϖ, SubmonoidClass.coe_pow, ← pow_add]; congr 1; omega
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
  show 1 + (_ * ϖ ^ c * ϖ ^ c) • (Sv * Em * Sv) = Sv * (1 + ϖ ^ s • Em) * Sv
  rw [hpow, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hSS]

/-- **Elements $\equiv 1 \bmod \pi^s$ lie in $J$** when $s \ge 2c$ ($\varpi^c\sigma$ integral). -/
theorem mem_Jsub_of_congr (hσ : σ * σ = 1) {c : ℕ} {σ' : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)}
    (hσ' : σ'.map (algebraMap _ (v.adicCompletion F)) =
      ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c • (σ : GL (Fin N) _).val)
    {s : ℕ} (hs : 2 * c ≤ s) (κ : stdStab Q v)
    (hκ : ∀ i j, NF.π v ^ s ∣ intRep v Q κ i j - (1 : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)) i j) :
    κ ∈ Jsub v Q σ := by
  rw [mem_Jsub_iff v Q σ hσ]
  choose E hE using hκ
  have hG : intRep v Q κ = 1 + NF.π v ^ s • Matrix.of E := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination (hE i j)
  have hG' : intRep v Q κ⁻¹ = 1 + NF.π v ^ s • (-(intRep v Q κ⁻¹ * Matrix.of E)) := by
    have h1 : intRep v Q κ⁻¹ * intRep v Q κ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hG, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h1
    rw [smul_neg, ← h1]; abel
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h0 := conj_val_eq v Q σ hσ hσ' hs _ (intRep_map v Q κ) hG
  have h1 := conj_val_eq v Q σ hσ hσ' hs _ (intRep_map v Q κ⁻¹) hG'
  have hinv : (σ * (κ : orthGroup Q (v.adicCompletion F)) * σ)⁻¹ =
      σ * ((κ⁻¹ : stdStab Q v) : orthGroup Q _) * σ := by
    rw [InvMemClass.coe_inv]; simp only [_root_.mul_inv_rev, hσi, mul_assoc]
  rw [← hinv] at h1
  exact mem_stdStab_of_integral v Q _ _ _ h0 h1


/-- **Openness relative to $J$:** two solutions of $Q = m$ congruent mod $\pi^s$, $s \ge f + 1 + 2c$ ($\pi^f \,\Vert\, 4m$), are
related by an element of $J$ (the integral product of two reflections, `exists_openMat`, is $\equiv 1 \bmod \pi^{s-f}$). -/
theorem exists_Jsub_of_near (hσ : σ * σ = 1) {c : ℕ} {σ' : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)}
    (hσ' : σ'.map (algebraMap _ (v.adicCompletion F)) =
      ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c • (σ : GL (Fin N) _).val)
    {Qo : QuadForm (v.adicCompletionIntegers F) N} (hQo : IsIntModel v Q Qo) (hQ : Qo.Nondegenerate)
    {mo : v.adicCompletionIntegers F} (hmo : mo ≠ 0) {f : ℕ} (hf : NF.π v ^ f ∣ 4 * mo)
    (hf' : ¬ NF.π v ^ (f + 1) ∣ 4 * mo) {s : ℕ} (hs : f + 1 + 2 * c ≤ s)
    {y z : Fin N → v.adicCompletionIntegers F} (hy : Qo.eval y = mo) (hz : Qo.eval z = mo)
    (hyz : ∀ i, NF.π v ^ s ∣ z i - y i) :
    ∃ γ ∈ Jsub v Q σ, intRep v Q γ *ᵥ y = z := by
  obtain ⟨T, hT, hTy, hT1⟩ := exists_openMat (NF.irreducible_π v) Qo hmo hf hf' (s := s) (by omega) hy hz hyz
  obtain ⟨γ, hγ⟩ := exists_intRep_eq v hQo hQ T hT
  refine ⟨γ, mem_Jsub_of_congr v Q σ hσ hσ' (s := s - f) (by omega) γ (by rw [hγ]; exact hT1), by rw [hγ]; exact hTy⟩


/-- **$J$ has finite index in $K$:** it contains the congruence subgroup $\{\kappa : \kappa \equiv 1 \bmod \pi^{2c}\}$, the kernel of the
reduction to the finite ring $M_N(\mathfrak o/\pi^{2c})$. -/
theorem index_Jsub_ne_zero (hσ : σ * σ = 1) {c : ℕ} {σ' : Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F)}
    (hσ' : σ'.map (algebraMap _ (v.adicCompletion F)) =
      ((NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c • (σ : GL (Fin N) _).val) :
    (Jsub v Q σ).index ≠ 0 := by
  set red : stdStab Q v →* Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F ⧸ Ideal.span {NF.π v ^ (2 * c)}) :=
    (RingHom.mapMatrix (Ideal.Quotient.mk (Ideal.span {NF.π v ^ (2 * c)}))).toMonoidHom.comp (intRep v Q)
  have hle : red.ker ≤ Jsub v Q σ := by
    intro κ hκ
    refine mem_Jsub_of_congr v Q σ hσ hσ' le_rfl κ fun i j => ?_
    have := congrFun (congrFun hκ i) j
    simp only [red, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply] at this ⊢
    rw [← DVR.mk_eq_mk_iff]
    split_ifs at this ⊢ <;> simpa using this
  have hfin : Finite (Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F ⧸ Ideal.span {NF.π v ^ (2 * c)})) := by
    have := DVR.finite_quot_pow (NF.π v) (NF.irreducible_π v) (2 * c)
    infer_instance
  have hker : red.ker.index ≠ 0 := by
    have hwd : ∀ a b : stdStab Q v, a⁻¹ * b ∈ red.ker → red a = red b := by
      intro a b hab
      rw [MonoidHom.mem_ker, map_mul] at hab
      calc red a = red a * (red a⁻¹ * red b) := by rw [hab, mul_one]
        _ = red b := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    let φq : stdStab Q v ⧸ red.ker → Matrix (Fin N) (Fin N) (v.adicCompletionIntegers F ⧸ Ideal.span {NF.π v ^ (2 * c)}) :=
      Quotient.lift (fun κ => red κ) (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.mp hab))
    have hinj : Function.Injective φq := by
      intro a b hab
      induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, MonoidHom.mem_ker, map_mul]
      have : red a = red b := hab
      rw [← this, ← map_mul, inv_mul_cancel, map_one]
    have : Finite (stdStab Q v ⧸ red.ker) := Finite.of_injective φq hinj
    exact Subgroup.index_ne_zero_of_finite
  intro h0
  exact hker (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hle))

end J


/-! ### The stabilizers of $e_0$ and $x$ in $K$ and the weight of $\sigma L$ -/

section Stab

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)
  (σ : orthGroup (splitForm m Q') (v.adicCompletion F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

/-- **The lattice $\sigma L$** as an element of $Y_\mathfrak p$, when $\sigma e_0 \in L$ and $\sigma^2 = 1$. -/
def sigmaPt (hσ : σ * σ = 1) (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) ∈ std v) :
    LocCompSet v m Q' :=
  ⟨locAct v (σ : GL (Fin (n + 1)) Fv) (std v), ⟨σ, rfl⟩, by
    refine ⟨_, hx, ?_⟩
    show (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((σ : GL (Fin (n + 1)) Fv).val *ᵥ e₀) = e₀
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, hσ]
    simp⟩

theorem locAct_sigma_sigma (hσ : σ * σ = 1) (M : Submodule 𝔬 (Fin (n + 1) → Fv)) :
    locAct v (σ : GL (Fin (n + 1)) Fv) (locAct v (σ : GL (Fin (n + 1)) Fv) M) = M := by
  rw [← locAct_mul, ← Subgroup.coe_mul, hσ]; exact locAct_one M

/-- $\sigma g \sigma \in K$ iff $g$ stabilizes $\sigma L$. -/
theorem conj_mem_stdStab_iff (hσ : σ * σ = 1) (g : orthGroup QS Fv) :
    σ * g * σ ∈ stdStab QS v ↔
      locAct v (g : GL (Fin (n + 1)) Fv) (locAct v (σ : GL (Fin (n + 1)) Fv) (std v)) =
        locAct v (σ : GL (Fin (n + 1)) Fv) (std v) := by
  show locAct v ((σ * g * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = std v ↔ _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, locAct_mul, locAct_mul]
  constructor
  · intro h
    have := congrArg (locAct v (σ : GL (Fin (n + 1)) Fv)) h
    rwa [locAct_sigma_sigma v m Q' σ hσ] at this
  · intro h
    rw [h, locAct_sigma_sigma v m Q' σ hσ]

variable {m₀ : 𝓞 F} {Q₀' : QuadForm (𝓞 F) n}

theorem coe_intRep_e₀ (κ : stdStab QS v) :
    (fun i => ((intRep v QS κ *ᵥ (e₀ : Fin (n + 1) → 𝔬)) i : Fv)) =
      ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) := by
  rw [coe_intRep_mulVec, coe_e₀_o]

/-- **The stabilizer of $e_0$ in $K$ against $J$:** $[\mathrm{Stab}_K(e_0) : \mathrm{Stab}_K(e_0)\cap J] = [K_0' : K_0'\cap K_{\sigma L}]$. -/
theorem relIndex_stabOf_e₀ (hm : m ≠ 0) (hσ : σ * σ = 1)
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) ∈ std v) :
    (Jsub v QS σ).relIndex (stabOf (intRep v QS) (e₀ : Fin (n + 1) → 𝔬)) =
      (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx)).relIndex (stdStab Q' v) := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  set S₀ := stabOf (intRep v QS) (e₀ : Fin (n + 1) → 𝔬)
  set sub := (stdStab QS v).subtype
  set φ := orthEmb m Q' Fv
  have hsub : Function.Injective sub := Subtype.val_injective
  have hφ : Function.Injective φ := orthEmb_injective m Q' Fv
  have hS₀ : ∀ κ : stdStab QS v, κ ∈ S₀ ↔
      ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    intro κ
    show intRep v QS κ *ᵥ e₀ = e₀ ↔ _
    rw [← coe_intRep_e₀]
    constructor
    · intro h; rw [h, coe_e₀_o]
    · intro h
      apply coe_o_injective v
      show (fun i => ((intRep v QS κ *ᵥ (e₀ : Fin (n + 1) → 𝔬)) i : Fv)) =
        fun i => (((e₀ : Fin (n + 1) → 𝔬) i : 𝔬) : Fv)
      rw [h, coe_e₀_o]
  have hA : S₀.map sub = (stdStab Q' v).map φ := by
    ext g
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 κ ((hS₀ κ).mp hκ)
      refine ⟨h, (mem_stdStab_orthEmb_iff m Q' v h).mp (by rw [hh]; exact κ.2), hh⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨φ h, (mem_stdStab_orthEmb_iff m Q' v h).mpr hh⟩, (hS₀ _).mpr (orthEmb_mulVec_e₀ m Q' Fv h), rfl⟩
  have hB : (Jsub v QS σ ⊓ S₀).map sub =
      (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx) ⊓ stdStab Q' v).map φ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    have key : ∀ h : orthGroup Q' Fv, σ * φ h * σ ∈ stdStab QS v ↔
        h ∈ stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx) := by
      intro h
      rw [conj_mem_stdStab_iff v m Q' σ hσ, mem_stabilizer_iff]
      constructor
      · intro h1; exact Subtype.ext h1
      · intro h1; exact congrArg Subtype.val h1
    constructor
    · rintro ⟨κ, ⟨hJ, hκ⟩, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 κ ((hS₀ κ).mp hκ)
      refine ⟨h, ⟨(key h).mp ?_, (mem_stdStab_orthEmb_iff m Q' v h).mp (by rw [hh]; exact κ.2)⟩, hh⟩
      rw [mem_Jsub_iff v QS σ hσ] at hJ
      rwa [show φ h = (κ : orthGroup QS Fv) from hh]
    · rintro ⟨h, ⟨hst, hh⟩, rfl⟩
      refine ⟨⟨φ h, (mem_stdStab_orthEmb_iff m Q' v h).mpr hh⟩,
        ⟨(mem_Jsub_iff v QS σ hσ _).mpr ((key h).mpr hst), (hS₀ _).mpr (orthEmb_mulVec_e₀ m Q' Fv h)⟩, rfl⟩
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.relIndex_map_map_of_injective _ _ hsub, hA, hB,
    Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.inf_relIndex_right]


/-- **The stabilizer of $x = \sigma e_0$ in $K$ against $J$:** $[\mathrm{Stab}_K(x) : \mathrm{Stab}_K(x)\cap J] = [K_{\sigma L} : K_0'\cap K_{\sigma L}]$
(conjugate by $\sigma$). -/
theorem relIndex_stabOf_x (hm : m ≠ 0) (hσ : σ * σ = 1) (x : Fin (n + 1) → 𝔬)
    (hσx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = fun i => (x i : Fv))
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) ∈ std v) :
    (Jsub v QS σ).relIndex (stabOf (intRep v QS) x) =
      (stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx)) := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  set Sx := stabOf (intRep v QS) x
  set sub := (stdStab QS v).subtype
  set φ := orthEmb m Q' Fv
  set cσ := (MulAut.conj σ).toMonoidHom
  have hsub : Function.Injective sub := Subtype.val_injective
  have hφ : Function.Injective φ := orthEmb_injective m Q' Fv
  have hc : Function.Injective cσ := (MulAut.conj σ).injective
  have hcv : ∀ g, cσ g = σ * g * σ := fun g => by
    show σ * g * σ⁻¹ = _; rw [hσi]
  set Sv := (σ : GL (Fin (n + 1)) Fv).val
  have hSS : Sv * Sv = 1 := by
    have := congrArg (fun g : orthGroup QS Fv => (g : GL (Fin (n + 1)) Fv).val) hσ
    simpa [Sv] using this
  have hσxe : Sv *ᵥ (fun i => (x i : Fv)) = e₀ := by rw [← hσx, mulVec_mulVec, hSS, one_mulVec]
  have hSx : ∀ κ : stdStab QS v, κ ∈ Sx ↔
      ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (x i : Fv)) = fun i => (x i : Fv) := by
    intro κ
    show intRep v QS κ *ᵥ x = x ↔ _
    rw [← coe_intRep_mulVec]
    constructor
    · intro h; rw [h]
    · intro h; exact coe_o_injective v h
  have key2 : ∀ h : orthGroup Q' Fv, σ * φ h * σ ∈ stdStab QS v ↔
      h ∈ stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx) := by
    intro h
    rw [conj_mem_stdStab_iff v m Q' σ hσ, mem_stabilizer_iff]
    constructor
    · intro h1; exact Subtype.ext h1
    · intro h1; exact congrArg Subtype.val h1
  have hfix : ∀ κ : stdStab QS v, κ ∈ Sx →
      ((σ * (κ : orthGroup QS Fv) * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
        (e₀ : Fin (n + 1) → Fv) = e₀ := by
    intro κ hκ
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [show (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = fun i => (x i : Fv) from hσx,
      (hSx κ).mp hκ]
    exact hσxe
  have hback : ∀ h : orthGroup Q' Fv, ((σ * φ h * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
      (fun i => (x i : Fv)) = fun i => (x i : Fv) := by
    intro h
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [show (σ : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (x i : Fv)) = e₀ from hσxe, orthEmb_mulVec_e₀, hσx]
  have hcc : ∀ h : orthGroup Q' Fv, σ * (σ * φ h * σ) * σ = φ h := by
    intro h
    calc σ * (σ * φ h * σ) * σ = (σ * σ) * φ h * (σ * σ) := by group
      _ = φ h := by rw [hσ]; group
  have hC : (Sx.map sub).map cσ = (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx)).map φ := by
    ext g
    simp only [Subgroup.map_map, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ (hfix κ hκ)
      refine ⟨h, (key2 h).mp ?_, by rw [hh, hcv]; rfl⟩
      rw [hh]
      have : σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = κ := by
        calc σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = (σ * σ) * κ * (σ * σ) := by group
          _ = κ := by rw [hσ]; group
      rw [this]; exact κ.2
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨σ * φ h * σ, (key2 h).mpr hh⟩, (hSx _).mpr (hback h), ?_⟩
      show cσ (σ * φ h * σ) = φ h
      rw [hcv, hcc]
  have hD : ((Jsub v QS σ ⊓ Sx).map sub).map cσ =
      (stdStab Q' v ⊓ stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hx)).map φ := by
    ext g
    simp only [Subgroup.map_map, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_inf]
    constructor
    · rintro ⟨κ, ⟨hJ, hκ⟩, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ (hfix κ hκ)
      have hκ' : σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = κ := by
        calc σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = (σ * σ) * κ * (σ * σ) := by group
          _ = κ := by rw [hσ]; group
      refine ⟨h, ⟨?_, (key2 h).mp ?_⟩, by rw [hh, hcv]; rfl⟩
      · rw [mem_Jsub_iff v QS σ hσ] at hJ
        rw [← mem_stdStab_orthEmb_iff m Q' v h, hh]; exact hJ
      · rw [hh, hκ']; exact κ.2
    · rintro ⟨h, ⟨hK, hh⟩, rfl⟩
      refine ⟨⟨σ * φ h * σ, (key2 h).mpr hh⟩, ⟨?_, (hSx _).mpr (hback h)⟩, ?_⟩
      · rw [mem_Jsub_iff v QS σ hσ]
        show σ * (σ * φ h * σ) * σ ∈ stdStab QS v
        rw [hcc]; exact (mem_stdStab_orthEmb_iff m Q' v h).mpr hK
      · show cσ (σ * φ h * σ) = φ h
        rw [hcv, hcc]
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.relIndex_map_map_of_injective _ _ hsub,
    ← Subgroup.relIndex_map_map_of_injective _ _ hc, hC, hD, Subgroup.relIndex_map_map_of_injective _ _ hφ,
    Subgroup.inf_relIndex_right]

end Stab


/-! ### The weight of a type as a ratio of orbit counts -/

section Weight

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)
  (σ : orthGroup (splitForm m Q') (v.adicCompletion F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

/-- **The weight of $\sigma L$ as a ratio of orbit counts** (Weil 1982, §3.4 [unverified]): for an integral model $Q_o$ of
$Q = \langle m\rangle\perp Q'$ with $Q_o(e_0) = m_o$, $x \in \mathfrak o_\mathfrak p^{n+1}$ with $Q_o(x) = m_o$ and an involution $\sigma$ with
$\sigma e_0 = x$ and $\varpi^c\sigma$ integral, for $r \ge f + 1 + 2c$ ($\pi^f \,\Vert\, 4m_o$), $k \ge r + c + e$, $k \ge 2e + 1$
($\pi^e \,\Vert\, 2m_o$):
$$N_{k,r}(Kx)\,[K_{\sigma L} : K_0'\cap K_{\sigma L}] = N_{k,r}(Ke_0)\,[K_0' : K_0' \cap K_{\sigma L}].$$ -/
@[kb "weil1982" "§3.4 (local weights as orbit measures) [unverified]"]
theorem nearCount_mul_relIndex_eq (hm : m ≠ 0) {Qo : QuadForm 𝔬 (n + 1)} (hQo : IsIntModel v QS Qo)
    (hQnd : Qo.Nondegenerate) {mo : 𝔬} (hmo : mo ≠ 0) (he₀ : Qo.eval (e₀ : Fin (n + 1) → 𝔬) = mo)
    (hσ : σ * σ = 1) (x : Fin (n + 1) → 𝔬) (hx : Qo.eval x = mo)
    (hσx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = fun i => (x i : Fv))
    (hxstd : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) ∈ std v)
    {c : ℕ} {σ' : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬}
    (hσ' : σ'.map (algebraMap 𝔬 Fv) = ((NF.π v : 𝔬) : Fv) ^ c • (σ : GL (Fin (n + 1)) Fv).val)
    {e f r k : ℕ} (he : NF.π v ^ e ∣ 2 * mo) (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * mo)
    (hf : NF.π v ^ f ∣ 4 * mo) (hf' : ¬ NF.π v ^ (f + 1) ∣ 4 * mo)
    (hr : f + 1 + 2 * c ≤ r) (hk : r + c + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    nearCount Qo (NF.π v) mo k r (orbitOf (intRep v QS) ⊤ x) *
        (stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hxstd)) =
      nearCount Qo (NF.π v) mo k r (orbitOf (intRep v QS) ⊤ e₀) *
        (stabilizer (orthGroup Q' Fv) (sigmaPt v m Q' σ hσ hxstd)).relIndex (stdStab Q' v) := by
  set ρ := intRep v QS
  set J := Jsub v QS σ
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  have hπ := NF.irreducible_π v
  have hρQ : ∀ κ, Qo.compMat (ρ κ) = Qo := compMat_intRep v hQo
  have hQρ : ∀ κ y, Qo.eval (ρ κ *ᵥ y) = Qo.eval y := fun κ y => by rw [← eval_compMat, hρQ]
  set Sv := (σ : GL (Fin (n + 1)) Fv).val
  have hSS : Sv * Sv = 1 := by
    have := congrArg (fun g : orthGroup QS Fv => (g : GL (Fin (n + 1)) Fv).val) hσ
    simpa [Sv] using this
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hσxe : Sv *ᵥ (fun i => (x i : Fv)) = e₀ := by rw [← hσx, mulVec_mulVec, hSS, one_mulVec]
  -- openness at a point, relative to `J`
  have hopen : ∀ y : Fin (n + 1) → 𝔬, Qo.eval y = mo → ∀ κ ∈ congrSub ρ (NF.π v) r y,
      ∃ γ ∈ J, ρ γ *ᵥ y = ρ κ *ᵥ y := by
    intro y hy κ hκ
    exact exists_Jsub_of_near v QS σ hσ hσ' hQo hQnd hmo hf hf' hr hy (by rw [hQρ, hy]) hκ
  have hJe := nearCount_mul_relIndex ρ Qo hρQ (NF.π v) mo (k := k) (r := r) (by omega) hπ J e₀
    (hopen e₀ he₀)
  have hJx := nearCount_mul_relIndex ρ Qo hρQ (NF.π v) mo (k := k) (r := r) (by omega) hπ J x (hopen x hx)
  -- the involution `σ' = ϖ^c σ`
  have hcoe : ∀ z : Fin (n + 1) → 𝔬, (fun i => ((σ' *ᵥ z) i : Fv)) = ϖ ^ c • (Sv *ᵥ fun i => (z i : Fv)) := by
    intro z; rw [coe_mulVec_o, hσ', smul_mulVec]
  have hσσ : ∀ z, σ' *ᵥ (σ' *ᵥ z) = (NF.π v ^ c) ^ 2 • z := by
    intro z
    apply coe_o_injective v
    show (fun i => ((σ' *ᵥ (σ' *ᵥ z)) i : Fv)) = fun i => ((((NF.π v ^ c) ^ 2 • z) i : 𝔬) : Fv)
    rw [hcoe, hcoe, mulVec_smul, mulVec_mulVec, hSS, one_mulVec, smul_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ϖ]
    push_cast
    ring
  have hσQ : ∀ z, Qo.eval (σ' *ᵥ z) = (NF.π v ^ c) ^ 2 * Qo.eval z := by
    intro z
    apply SetLike.coe_eq_coe.mp
    rw [← hQo, hcoe, evalIn_smul', evalIn_mulVec_of_mem QS σ.2, hQo]
    simp [ϖ]
  -- `σ` exchanges `J e₀` and `J x`
  have hconjJ : ∀ γ ∈ J, ∃ γ' ∈ J, (γ' : orthGroup QS Fv) = σ * (γ : orthGroup QS Fv) * σ := by
    intro γ hγ
    refine ⟨⟨σ * γ * σ, (mem_Jsub_iff v QS σ hσ γ).mp hγ⟩, (mem_Jsub_iff v QS σ hσ _).mpr ?_, rfl⟩
    show σ * (σ * (γ : orthGroup QS Fv) * σ) * σ ∈ stdStab QS v
    have : σ * (σ * (γ : orthGroup QS Fv) * σ) * σ = γ := by
      calc σ * (σ * (γ : orthGroup QS Fv) * σ) * σ = (σ * σ) * γ * (σ * σ) := by group
        _ = γ := by rw [hσ]; group
    rw [this]; exact γ.2
  have hval : ∀ γ' γ : stdStab QS v, (γ' : orthGroup QS Fv) = σ * (γ : orthGroup QS Fv) * σ →
      ((γ' : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val = Sv * ((γ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val * Sv := by
    intro γ' γ h; rw [h]; simp [Sv]
  have hAA' : ∀ (y y' : Fin (n + 1) → 𝔬), Sv *ᵥ (fun i => (y i : Fv)) = (fun i => (y' i : Fv)) →
      ∀ a ∈ orbitOf ρ J y, ∃ a' ∈ orbitOf ρ J y', σ' *ᵥ a = NF.π v ^ c • a' := by
    intro y y' hyy' a ⟨γ, hγ, ha⟩
    obtain ⟨γ', hγ', hγ'v⟩ := hconjJ γ hγ
    refine ⟨ρ γ' *ᵥ y', ⟨γ', hγ', rfl⟩, ?_⟩
    apply coe_o_injective v
    show (fun i => ((σ' *ᵥ a) i : Fv)) = fun i => (((NF.π v ^ c • (ρ γ' *ᵥ y')) i : 𝔬) : Fv)
    rw [hcoe, ← ha, coe_intRep_mulVec]
    have h1 : (fun i => (((NF.π v ^ c • (ρ γ' *ᵥ y')) i : 𝔬) : Fv)) =
        ϖ ^ c • (fun i => ((ρ γ' *ᵥ y') i : Fv)) := by funext i; simp [ϖ]
    rw [h1, coe_intRep_mulVec, hval γ' γ hγ'v, ← hyy', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
      hSS, Matrix.mul_one]
  have hxe : Sv *ᵥ (fun i => ((e₀ : Fin (n + 1) → 𝔬) i : Fv)) = fun i => (x i : Fv) := by
    rw [coe_e₀_o]; exact hσx
  have hex : Sv *ᵥ (fun i => (x i : Fv)) = fun i => ((e₀ : Fin (n + 1) → 𝔬) i : Fv) := by
    rw [coe_e₀_o]; exact hσxe
  -- saturation
  have hsat : ∀ y : Fin (n + 1) → 𝔬, Qo.eval y = mo → ∀ a ∈ orbitOf ρ J y, ∀ z, Qo.eval z = mo →
      (∀ i, NF.π v ^ (f + 1 + 2 * c) ∣ z i - a i) → z ∈ orbitOf ρ J y := by
    intro y hy a ⟨γ, hγ, ha⟩ z hz hza
    obtain ⟨γ₁, hγ₁, h1⟩ := exists_Jsub_of_near v QS σ hσ hσ' hQo hQnd hmo hf hf' le_rfl
      (by rw [← ha, hQρ, hy]) hz hza
    refine ⟨γ₁ * γ, J.mul_mem hγ₁ hγ, ?_⟩
    rw [map_mul, ← mulVec_mulVec, ha, h1]
  have hσl := nearCount_eq_of_involution hπ Qo he he' σ' c hσσ hσQ (hAA' _ _ hxe) (hAA' _ _ hex)
    (hsat _ he₀) (hsat _ hx) hr hk hk2
  rw [relIndex_stabOf_e₀ v m Q' σ hm hσ hxstd] at hJe
  rw [relIndex_stabOf_x v m Q' σ hm hσ x hσx hxstd] at hJx
  rw [hJx, ← hσl, ← hJe]

end Weight


/-! ### Local types and the $K$-orbits on $\{Q = m\}$ -/

section Types

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

theorem integral_of_mem_std {y : Fin (n + 1) → Fv} (hy : y ∈ std v) :
    ∃ x : Fin (n + 1) → 𝔬, (fun i => (x i : Fv)) = y := by
  have hyv : ∀ i, Valued.v (y i) ≤ 1 := by
    intro i; have := hy i; rwa [neg_zero, WithZero.exp_zero] at this
  exact ⟨fun i => toO v _ (hyv i), rfl⟩

theorem coe_mem_std (x : Fin (n + 1) → 𝔬) : (fun i => (x i : Fv)) ∈ std v := by
  intro i
  rw [neg_zero, WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (x i).2

/-- **Data for a lattice of $Y_\mathfrak p$:** for $M \in Y_\mathfrak p$ there are $x \in \mathfrak o_\mathfrak p^{n+1}$ with $Q(x) = m$, an involution
$\sigma$ with $\sigma e_0 = x$, and $h \in H$ with $M = \mathrm{diag}(1, h)\,\sigma L$ (so $M = gL$ with $g = \mathrm{diag}(1,h)\sigma$, $g^{-1}e_0 = x$). -/
theorem exists_type_data (hm : m ≠ 0) {Qo : QuadForm 𝔬 (n + 1)} (hQo : IsIntModel v QS Qo) {mo : 𝔬}
    (hmoF : ((mo : 𝔬) : Fv) = algebraMap F Fv m) (M : LocCompSet v m Q') :
    ∃ (x : Fin (n + 1) → 𝔬) (σ : orthGroup QS Fv) (h : orthGroup Q' Fv), Qo.eval x = mo ∧ σ * σ = 1 ∧
      (σ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = (fun i => (x i : Fv)) ∧
      locAct v ((orthEmb m Q' Fv h * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = M.1 := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  obtain ⟨g, hg⟩ := M.2.1
  have he := M.2.2
  rw [← hg] at he
  obtain ⟨y, hy, hgy⟩ := he
  replace hgy : (g : GL (Fin (n + 1)) Fv).val *ᵥ y = e₀ := hgy
  obtain ⟨x, rfl⟩ := integral_of_mem_std v hy
  have hQx : (QS).evalIn Fv (fun i => (x i : Fv)) = algebraMap F Fv m := by
    rw [← evalIn_mulVec_of_mem QS g.2, hgy, evalIn_splitForm_e₀]
  have hxmo : Qo.eval x = mo := by
    apply SetLike.coe_eq_coe.mp
    rw [← hQo, hQx, hmoF]
  obtain ⟨σ, hσ, hσx⟩ := exists_inv_e₀ v m Q' hm _ hQx
  have hgσ : ((g * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hσx, hgy]
  obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ hgσ
  refine ⟨x, σ, h, hxmo, hσ, hσx, ?_⟩
  rw [hh, mul_assoc, hσ, mul_one, ← hg]

/-- **Points of one $K$-orbit give the same local type:** if $M = gL$, $M' = g'L$ ($g, g' \in O(V)$) and $\kappa \in K$ maps $g^{-1}e_0$ to
$g'^{-1}e_0$, then $M$ and $M'$ are in the same $H$-orbit. -/
theorem mem_orbit_of_stdStab (hm : m ≠ 0) (M M' : LocCompSet v m Q') (g g' : orthGroup QS Fv)
    (hg : locAct v (g : GL (Fin (n + 1)) Fv) (std v) = M.1)
    (hg' : locAct v (g' : GL (Fin (n + 1)) Fv) (std v) = M'.1) (κ : stdStab QS v)
    (hκ : ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ ((g⁻¹ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
      (e₀ : Fin (n + 1) → Fv) = ((g'⁻¹ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ e₀) :
    M' ∈ orbit (orthGroup Q' Fv) M := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  set γ : orthGroup QS Fv := g' * (κ : orthGroup QS Fv) * g⁻¹
  have hγ : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    simp only [γ, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [hκ, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    simp
  obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 γ hγ
  refine ⟨h, Subtype.ext ?_⟩
  rw [LocCompSet.smul_val, hh, ← hg, ← hg', ← locAct_mul]
  have : ((γ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) * (g : GL (Fin (n + 1)) Fv) =
      (g' : GL (Fin (n + 1)) Fv) * ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) := by
    simp only [γ, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [this, locAct_mul, show locAct v ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = std v from κ.2]

end Types


/-! ### The local orbital identity at every prime -/

section Main

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/-- **The local weights do not depend on the representative of a local type** (unimodularity of $O(Q')(F_\mathfrak p)$ on the
stabilizers of the lattices of $Y_\mathfrak p$): $w_\mathfrak p(hM) = w_\mathfrak p(M)$ for $h \in O(Q')(F_\mathfrak p)$, $M \in Y_\mathfrak p$.

Field:
- `smul_eq`: the displayed invariance.

*Meaning.* $K_{hM} = hK_Mh^{-1}$, so this says $[K_0' : K_0'\cap hKh^{-1}] = [hKh^{-1} : K_0' \cap hKh^{-1}]\cdot[K_0' : K_0'\cap K]/[K : K_0'\cap K]$ for
the compact open subgroups $K = K_M$ of $O(Q')(F_\mathfrak p)$: the modular function of $O(Q')(F_\mathfrak p)$ is trivial on these elements.
It is proved locally at every prime for every nondegenerate $Q'$ (`locWeightInvariant_local`, `LocalUnimodular.lean`:
$\Delta$ is multiplicative, trivial on reflections, and reflections generate $O(Q')(F_\mathfrak p)$), and also, at $\mathfrak p \mid 2m$
for totally positive definite $Q$, from the finiteness of the mass (`locWeightInvariant`, `compWeight_smul`).
*Independence:* a statement about one group and one prime; it does not mention densities or counts. -/
@[kb "weil1982" "§3.5 (independence of the representative) [unverified locator]"]
structure LocWeightInvariant (m : F) (Q' : QuadForm F n) : Prop where
  smul_eq : ∀ (h : orthGroup Q' (v.adicCompletion F)) (M : LocCompSet v m Q'),
    locWeight v m Q' (h • M) = locWeight v m Q' M

/-- **Weil's orbit-count identity at every prime** (dyadic primes and primes dividing $m$ included; Weil 1982, §3.4
[unverified]): given the representative independence of the local weights (`LocWeightInvariant`),
$$W_\mathfrak p\cdot|O(Q\bmod\varpi^k)\,e_0| = \#\{x \bmod \varpi^k : Q(x) \equiv m\}\qquad (k \gg 0).$$
*Proof:* the solutions mod $\varpi^k$ split by the $K$-orbit they are close to (`repCount_eq_sum_nearCount`); the $K$-orbits are the
local types ($M = \mathrm{diag}(1,h)\sigma_xL \leftrightarrow Kx$, `exists_type_data`, `mem_orbit_of_stdStab`), finitely many; the orbit of
$x$ has $w(\sigma_xL)$ times as many points as that of $e_0$ (`nearCount_mul_relIndex_eq`); and the points near $Ke_0$ are exactly
the orbit of $e_0$ under $O(Q \bmod \varpi^k)$ (`card_orbitSet_eq_nearCount`). -/
@[kb "weil1982" "§3.4 (orbits of the local fibration, every prime) [unverified]"]
theorem localTypeOrbitCount_of_invariant (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hQ' : Q₀'.Nondegenerate)
    (hinv : LocWeightInvariant v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F))) :
    LocalTypeOrbitCount v Q₀' m₀ := by
  classical
  set mF := algebraMap (𝓞 F) F m₀
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set Qo := NF.Qp v (splitForm m₀ Q₀')
  set mo := NF.ι v m₀
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hsplitF : splitForm mF QF' = (splitForm m₀ Q₀').map (algebraMap (𝓞 F) F) := (map_splitForm _ _ _).symm
  have hQo : IsIntModel v (splitForm mF QF') Qo := fun y => by rw [hsplitF]; exact evalIn_coe_o v _ y
  have hQ : (splitForm m₀ Q₀').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'
  have hQnd : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ
  have hmo : mo ≠ 0 := NF.ι_ne_zero v hm
  have hQosplit : Qo = splitForm mo (NF.Qp v Q₀') := map_splitForm _ _ _
  have he₀ : Qo.eval (e₀ : Fin (n + 1) → v.adicCompletionIntegers F) = mo := by
    rw [hQosplit]; exact eval_splitForm_e₀' _ _
  have hmoF : ((mo : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) mF := by
    have := hQo e₀
    rw [coe_e₀_o, evalIn_splitForm_e₀, he₀] at this
    exact this.symm
  have hπ := NF.irreducible_π v
  have h2 : (2 : v.adicCompletionIntegers F) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : v.adicCompletionIntegers F) ≠ 0 := by
    rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨e, he, he'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h2 hmo)
  obtain ⟨f, hf, hf'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 hmo)
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hQnd
  set ρ := intRep v (splitForm mF QF')
  -- the data of the local types
  choose x σ h hx hσ hσx hloc using fun t : LocTypes v mF QF' =>
    exists_type_data v mF QF' hmF hQo hmoF (locRep v mF QF' t)
  set g : LocTypes v mF QF' → orthGroup (splitForm mF QF') (v.adicCompletion F) :=
    fun t => orthEmb mF QF' (v.adicCompletion F) (h t) * σ t
  have hginv : ∀ t, ((g t)⁻¹ : orthGroup (splitForm mF QF') (v.adicCompletion F)).val.val *ᵥ
      (e₀ : Fin (n + 1) → v.adicCompletion F) = fun i => (x t i : v.adicCompletion F) := by
    intro t
    have hσi : (σ t)⁻¹ = σ t := inv_eq_of_mul_eq_one_right (hσ t)
    simp only [g, _root_.mul_inv_rev, hσi, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← map_inv,
      orthEmb_mulVec_e₀, hσx]
  -- disjointness of the orbits
  have hdisj : ∀ (r : ℕ), f + 1 ≤ r → ∀ t t', ∀ a ∈ orbitOf ρ ⊤ (x t), ∀ a' ∈ orbitOf ρ ⊤ (x t'),
      (∀ i, NF.π v ^ r ∣ a i - a' i) → t = t' := by
    rintro r hr t t' a ⟨κ, -, ha⟩ a' ⟨κ', -, ha'⟩ haa'
    have hQa : Qo.eval a = mo := by rw [← ha, ← eval_compMat, compMat_intRep v hQo, hx t]
    have hQa' : Qo.eval a' = mo := by rw [← ha', ← eval_compMat, compMat_intRep v hQo, hx t']
    obtain ⟨T, hT, hTa, -⟩ := exists_openMat hπ Qo hmo hf hf' (s := r) (by omega) hQa hQa'
      (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
    obtain ⟨τ, hτ⟩ := exists_intRep_eq v hQo hQnd T hT
    have hκ₂ : ρ (κ'⁻¹ * τ * κ) *ᵥ x t = x t' := by
      rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ha, hτ, hTa, ← ha', mulVec_inv_mulVec' ρ κ']
    have hmem := mem_orbit_of_stdStab v mF QF' hmF (locRep v mF QF' t) (locRep v mF QF' t') (g t) (g t')
      (hloc t) (hloc t') (κ'⁻¹ * τ * κ) (by rw [hginv, hginv, ← coe_intRep_mulVec, hκ₂])
    have : (Quotient.mk'' (locRep v mF QF' t') : LocTypes v mF QF') = Quotient.mk'' (locRep v mF QF' t) :=
      Quotient.sound' hmem
    rw [locRep_mk, locRep_mk] at this
    exact this.symm
  -- finitely many types
  have hfinT : Finite (LocTypes v mF QF') := by
    have := DVR.finite_vec (ι := Fin (n + 1)) (NF.π v) hπ (f + 1)
    refine Finite.of_injective (fun t => DVR.redI (NF.π v) (f + 1) (x t)) fun t t' htt => ?_
    refine hdisj (f + 1) le_rfl t t' (x t) ⟨1, Subgroup.mem_top 1, by simp⟩ (x t') ⟨1, Subgroup.mem_top 1, by simp⟩
      ((DVR.redI_eq_iff _ _ _ _).mp htt)
  let _ : Fintype (LocTypes v mF QF') := Fintype.ofFinite _
  -- every solution lies in the orbit of some `x t`
  have hcover : ∀ y, Qo.eval y = mo → ∃ t, y ∈ orbitOf ρ ⊤ (x t) := by
    intro y hy
    have hQy : (splitForm mF QF').evalIn (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) =
        algebraMap F (v.adicCompletion F) mF := by rw [hQo, hy, hmoF]
    obtain ⟨σy, hσy, hσye⟩ := exists_inv_e₀ v mF QF' hmF _ hQy
    have hystd : (σy : GL (Fin (n + 1)) (v.adicCompletion F)).val *ᵥ (e₀ : Fin (n + 1) → v.adicCompletion F) ∈
        std v := by rw [hσye]; exact coe_mem_std v y
    set M := sigmaPt v mF QF' σy hσy hystd
    set t : LocTypes v mF QF' := Quotient.mk'' M
    obtain ⟨h', hh'⟩ : locRep v mF QF' t ∈ orbit (orthGroup QF' (v.adicCompletion F)) M :=
      Quotient.exact' (locRep_mk v mF QF' t)
    set φ := orthEmb mF QF' (v.adicCompletion F)
    set κo : orthGroup (splitForm mF QF') (v.adicCompletion F) := σy * (φ h')⁻¹ * g t
    have hσyσy : locAct v (σy : GL (Fin (n + 1)) (v.adicCompletion F))
        (locAct v (σy : GL (Fin (n + 1)) (v.adicCompletion F)) (std v)) = std v :=
      locAct_sigma_sigma v mF QF' σy hσy _
    have hκK : κo ∈ stdStab (splitForm mF QF') v := by
      show locAct v (κo : GL (Fin (n + 1)) (v.adicCompletion F)) (std v) = std v
      have h1 : locAct v ((g t : orthGroup _ _) : GL (Fin (n + 1)) (v.adicCompletion F)) (std v) =
          locAct v ((φ h' : orthGroup _ _) : GL (Fin (n + 1)) (v.adicCompletion F))
            (locAct v (σy : GL (Fin (n + 1)) (v.adicCompletion F)) (std v)) := by
        rw [hloc t, ← hh']; rfl
      simp only [κo, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
      rw [h1, locAct_inv_locAct, hσyσy]
    refine ⟨t, ⟨⟨κo, hκK⟩, Subgroup.mem_top _, ?_⟩⟩
    apply coe_o_injective v
    show (fun i => ((ρ ⟨κo, hκK⟩ *ᵥ x t) i : v.adicCompletion F)) = fun i => (y i : v.adicCompletion F)
    rw [coe_intRep_mulVec]
    show (κo : GL (Fin (n + 1)) (v.adicCompletion F)).val *ᵥ _ = _
    have hgx : ((g t : orthGroup _ _) : GL (Fin (n + 1)) (v.adicCompletion F)).val *ᵥ
        (fun i => (x t i : v.adicCompletion F)) = e₀ := by
      rw [← hginv t, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
    have hinvfix : (((φ h' : orthGroup _ _) : GL (Fin (n + 1)) (v.adicCompletion F))⁻¹).val *ᵥ
        (e₀ : Fin (n + 1) → v.adicCompletion F) = e₀ := by
      conv_lhs => rw [← orthEmb_mulVec_e₀ mF QF' _ h']
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]; simp
    simp only [κo, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec, hgx]
    rw [hinvfix, hσye]
  -- denominators of the involutions and the radius
  choose c σ' hσ' using fun t => exists_scale_integral v ((σ t : GL (Fin (n + 1)) (v.adicCompletion F)).val)
  set cmax := Finset.univ.sup c
  set r := f + 1 + 2 * cmax
  have hct : ∀ t, c t ≤ cmax := fun t => Finset.le_sup (f := c) (Finset.mem_univ t)
  have hxstd : ∀ t, (σ t : GL (Fin (n + 1)) (v.adicCompletion F)).val *ᵥ (e₀ : Fin (n + 1) → v.adicCompletion F) ∈
      std v := fun t => by rw [hσx]; exact coe_mem_std v _
  -- the weight of a type is that of `σ L`
  have hw : ∀ t, locWeight v mF QF' (locRep v mF QF' t) =
      locWeight v mF QF' (sigmaPt v mF QF' (σ t) (hσ t) (hxstd t)) := by
    intro t
    have : h t • sigmaPt v mF QF' (σ t) (hσ t) (hxstd t) = locRep v mF QF' t := Subtype.ext (by
      rw [LocCompSet.smul_val]
      show locAct v _ (locAct v _ (std v)) = _
      rw [← locAct_mul, ← Subgroup.coe_mul]; exact hloc t)
    rw [← this, hinv.smul_eq]
  have hD : ∀ t, (stdStab QF' v).relIndex
      (stabilizer (orthGroup QF' (v.adicCompletion F)) (sigmaPt v mF QF' (σ t) (hσ t) (hxstd t))) ≠ 0 := by
    intro t h0
    rw [← relIndex_stabOf_x v mF QF' (σ t) hmF (hσ t) (x t) (hσx t) (hxstd t)] at h0
    refine index_Jsub_ne_zero v _ (σ t) (hσ t) (hσ' t) ?_
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_eq_zero_of_le_right le_top h0
  refine ⟨?_⟩
  filter_upwards [Filter.eventually_ge_atTop (r + cmax + 2 * e + 2 * d + 1)] with k hk
  -- the orbit of each type against that of `e₀`
  have hper : ∀ t, (nearCount Qo (NF.π v) mo k r (orbitOf ρ ⊤ (x t)) : ℝ) =
      locWeight v mF QF' (locRep v mF QF' t) * nearCount Qo (NF.π v) mo k r (orbitOf ρ ⊤ e₀) := by
    intro t
    have hid := nearCount_mul_relIndex_eq v mF QF' (σ t) hmF hQo hQnd hmo he₀ (hσ t) (x t) (hx t) (hσx t)
      (hxstd t) (hσ' t) he he' hf hf' (r := r) (k := k) (by have := hct t; omega) (by have := hct t; omega)
      (by omega)
    have hD' : ((stdStab QF' v).relIndex
        (stabilizer (orthGroup QF' (v.adicCompletion F)) (sigmaPt v mF QF' (σ t) (hσ t) (hxstd t))) : ℝ) ≠ 0 := by
      exact_mod_cast hD t
    rw [hw t, locWeight, div_mul_eq_mul_div, eq_div_iff hD']
    have := congrArg (Nat.cast : ℕ → ℝ) hid
    push_cast at this
    linarith
  -- the level set is the union of the orbits
  have hsum := repCount_eq_sum_nearCount hπ Qo he he' (fun t => orbitOf ρ ⊤ (x t)) hcover
    (hdisj r (by omega)) (k := k) (by omega) (by omega)
  -- the orbit of `e₀` mod `π^k`
  have horb : orbitCountE₀ v m₀ Q₀' k = nearCount Qo (NF.π v) mo k r (orbitOf ρ ⊤ e₀) := by
    unfold orbitCountE₀
    have hρQ : ∀ κ, (splitForm mo (NF.Qp v Q₀')).compMat (ρ κ) = splitForm mo (NF.Qp v Q₀') := by
      intro κ; rw [← hQosplit]; exact compMat_intRep v hQo κ
    have hsurj : ∀ X, (splitForm mo (NF.Qp v Q₀')).compMat X = splitForm mo (NF.Qp v Q₀') → ∃ κ, ρ κ = X := by
      intro X hX; rw [← hQosplit] at hX; exact exists_intRep_eq v hQo hQnd X hX
    rw [show NF.Qp v (splitForm m₀ Q₀') = Qo from rfl, hQosplit]
    exact card_orbitSet_eq_nearCount hπ ρ (NF.Qp v Q₀') hρQ hsurj hf hf' (by rw [← hQosplit]; exact hd)
      (by rw [← hQosplit]; exact hd') (by omega) (by omega) (by omega)
  rw [locTypeSum, finsum_eq_sum_of_fintype, horb, Finset.sum_mul]
  show _ = ((DVR.repCount Qo (NF.π v) k mo : ℕ) : ℝ)
  rw [hsum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ => (hper t).symm

end Main


/-! ### The representative independence of the local weights, from the finiteness of the mass -/

section Invariance

open Classical in
/-- **The global weight of a lattice is the product of its local weights at the primes in $S$**, when it is standard
outside $S$ (the computation of `compWeight_glueComp` for any lattice of $Y$). -/
theorem compWeight_eq_prod {F : Type} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : CompSet m Q' (stdLat F (n + 1)))
    (hy : ∀ w ∉ S, locOf m Q' w y = locStdPt w m Q') :
    compWeight m Q' (stdLat F (n + 1)) y = ∏ w ∈ S, locWeight w m Q' (locOf m Q' w y) := by
  set A' : (w : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup Q' (w.adicCompletion F)) :=
    fun w => stabilizer (orthGroup Q' (w.adicCompletion F)) (locOf m Q' w y)
  have hA : ∀ w ∉ S, A' w = stdStab Q' w := by
    intro w hw
    simp only [A']
    rw [hy w hw, stabilizer_locStdPt]
  have hB : ∀ w ∉ S, stdStab Q' w = stdStab Q' w := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf Q') y ↔ ∀ w, h w ∈ A' w := by
    intro h
    rw [stabilizer_compSet, Subgroup.mem_comap]
    show (∀ w, _ = _) ↔ _
    refine forall_congr' fun w => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab Q' (stdLat F n) ↔ ∀ w, h w ∈ stdStab Q' w := mem_locStab_intVec Q'
  have e1 := relIndex_restrictedPi S A' (fun w => stdStab Q' w) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun w => stdStab Q' w) A' hB hA _ _ hBm hAm
  unfold compWeight
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  rfl

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n)

local notation "mF" => algebraMap (𝓞 F) F m₀
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)

open Classical in
/-- **A local weight is the weight of the type's representative** (at a prime $\mathfrak p \mid 2m$), for $Q$ totally positive
definite: the lattice $M$ and `locRep` of its type, glued with $\mathfrak o_\mathfrak q^{n+1}$ at the other primes, are in one
$O(Q')(\mathbb A_f)$-orbit, whose global weight is constant (`compWeight_smul`, i.e. the finiteness of the mass), and the global
weight is the product of the local ones (`compWeight_eq_prod`). -/
theorem locWeight_eq_locRep (hm : m₀ ≠ 0)
    (hpd : IsTotallyPosDef (splitForm mF QF'))
    (hLi : IsIntegral (splitForm mF QF') (stdLat F (n + 1)).1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : 2 * m₀ ∈ v.asIdeal) (M : LocCompSet v mF QF') :
    locWeight v mF QF' M = locWeight v mF QF' (locRep v mF QF' (Quotient.mk'' M)) := by
  have hpd' := isTotallyPosDef_of_splitForm hpd
  have hLi' := isIntegral_of_splitForm hLi
  have hvS : v ∈ badSet m₀ hm := (mem_badSet m₀ hm).mpr hv
  -- the glued lattice with type `[M]` at `v` and the standard type elsewhere
  let f₀ : (w : badSet m₀ hm) → LocTypes w mF QF' := fun w => Quotient.mk'' (locStdPt w mF QF')
  let f : (w : badSet m₀ hm) → LocTypes w mF QF' := Function.update f₀ ⟨v, hvS⟩ (Quotient.mk'' M)
  have hy₁v : locOf mF QF' v (glueComp m₀ Q₀' hm f) = locRep v mF QF' (Quotient.mk'' M) := by
    have := locOf_glueComp m₀ Q₀' hm f ⟨v, hvS⟩
    rw [this]; simp [f]
  -- move the component at `v` to `M`
  obtain ⟨h₀, hh₀⟩ : M ∈ orbit (orthGroup QF' (v.adicCompletion F)) (locRep v mF QF' (Quotient.mk'' M)) :=
    Quotient.exact' (locRep_mk v mF QF' (Quotient.mk'' M)).symm
  let hp : (w : HeightOneSpectrum (𝓞 F)) → orthGroup QF' (w.adicCompletion F) :=
    Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => orthGroup QF' (w.adicCompletion F)) v h₀
  let hA : OAf QF' := ⟨hp, by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    simp only [hp]
    rw [Pi.mulSingle_eq_of_ne (show w ≠ v from hw)]
    exact (stdStab QF' w).one_mem⟩
  have hlocy₂ : ∀ w, w ≠ v → locOf mF QF' w (hA • glueComp m₀ Q₀' hm f) = locOf mF QF' w (glueComp m₀ Q₀' hm f) := by
    intro w hw
    rw [locOf_smul]
    show hp w • _ = _
    simp only [hp]
    rw [Pi.mulSingle_eq_of_ne hw, one_smul]
  have hy₂v : locOf mF QF' v (hA • glueComp m₀ Q₀' hm f) = M := by
    rw [locOf_smul]
    show hp v • _ = _
    simp only [hp]
    rw [Pi.mulSingle_eq_same, hy₁v]; exact hh₀
  have hstd : ∀ w ∉ badSet m₀ hm, locOf mF QF' w (glueComp m₀ Q₀' hm f) = locStdPt w mF QF' := fun w hw =>
    locOf_glueComp_of_not_mem m₀ Q₀' hm f hw
  have hothers : ∀ w ∈ badSet m₀ hm, w ≠ v → locWeight w mF QF' (locOf mF QF' w (glueComp m₀ Q₀' hm f)) = 1 := by
    intro w hw hwv
    have := locOf_glueComp m₀ Q₀' hm f ⟨w, hw⟩
    rw [this]
    have hfw : f ⟨w, hw⟩ = Quotient.mk'' (locStdPt w mF QF') := by
      simp only [f]
      rw [Function.update_of_ne (fun h => hwv (congrArg Subtype.val h))]
    rw [hfw, locRep_std, locWeight_std]
  have e1 := compWeight_eq_prod mF QF' (badSet m₀ hm) _ hstd
  have e2 := compWeight_eq_prod mF QF' (badSet m₀ hm) (hA • glueComp m₀ Q₀' hm f) (fun w hw => by
    rw [hlocy₂ w (fun h => hw (h ▸ hvS)), hstd w hw])
  have e3 := compWeight_smul mF QF' (stdLat F (n + 1)) hpd' hLi' hA (glueComp m₀ Q₀' hm f)
  rw [e1, e2, ← Finset.mul_prod_erase _ _ hvS, ← Finset.mul_prod_erase _ _ hvS, hy₂v, hy₁v] at e3
  have hp1 : ∏ w ∈ (badSet m₀ hm).erase v, locWeight w mF QF' (locOf mF QF' w (hA • glueComp m₀ Q₀' hm f)) = 1 := by
    refine Finset.prod_eq_one fun w hw => ?_
    rw [hlocy₂ w (Finset.ne_of_mem_erase hw), hothers w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)]
  have hp2 : ∏ w ∈ (badSet m₀ hm).erase v, locWeight w mF QF' (locOf mF QF' w (glueComp m₀ Q₀' hm f)) = 1 := by
    refine Finset.prod_eq_one fun w hw => ?_
    rw [hothers w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)]
  rw [hp1, hp2, mul_one, mul_one] at e3
  exact e3

/-- **`LocWeightInvariant` at the primes $\mathfrak p \mid 2m$**, for $Q = \langle m\rangle\perp Q'$ totally positive definite with
$\mathcal O_F^{n+1}$ integral (from `locWeight_eq_locRep`: $hM$ and $M$ have the same type). -/
@[kb "weil1982" "§3.5 (independence of the representative) [unverified locator]"]
theorem locWeightInvariant (hm : m₀ ≠ 0)
    (hpd : IsTotallyPosDef (splitForm mF QF'))
    (hLi : IsIntegral (splitForm mF QF') (stdLat F (n + 1)).1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : 2 * m₀ ∈ v.asIdeal) :
    LocWeightInvariant v mF QF' := by
  refine ⟨fun h M => ?_⟩
  rw [locWeight_eq_locRep m₀ Q₀' hm hpd hLi v hv (h • M), locWeight_eq_locRep m₀ Q₀' hm hpd hLi v hv M]
  congr 2
  exact Quotient.sound' ⟨h, rfl⟩

end Invariance



end QuadFormsKB.Tamagawa
