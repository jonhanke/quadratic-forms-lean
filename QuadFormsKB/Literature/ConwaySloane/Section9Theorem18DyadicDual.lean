/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ through the dual lattice

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction.

**Idea.** The condition of Theorem 18 for $L$ at $\mathfrak p$ (`Theorem18OnlyIf`) only involves the group
$O(L_\mathfrak p)$ (`locStabV`): the spinor norms of its proper elements (`localSpinorNormGroup`) and its reflections
(the root vectors, `IsRootVector`, are the anisotropic $x$ with $\tau_x \in O(L_\mathfrak p)$; they are *not* required
to lie in $L_\mathfrak p$). An isometry preserves a local lattice $M$ if and only if it preserves the dual lattice
$M^\# = \{x : B(x, M) \subseteq \mathfrak o_\mathfrak p\}$. So Theorem 18 holds for $L$ at $\mathfrak p$ as soon as it
holds for some lattice $L'$ with $L'_\mathfrak p = L_\mathfrak p^\#$, and such an $L'$ exists (O'Meara 81:14).

**Layer.** Over a number field $F$ (the Theorem 18 part over $\mathbb Q$), a prime $v$, the form $Q$ on $F_v^n$ with
bilinear form $B$ = `qbil Q Fv` (matrix $H$ = the Hessian of $Q$), local lattices `locAct v γ (std v)` $=
\gamma\mathfrak o_v^n$ with Gram matrix $G$ = `locGram Q v γ` $= \gamma^{\mathsf T}H\gamma$.

**Defines**
* `IsDualLoc Q M M'` (a **condition**): $M' = M^\#$, i.e. $x \in M'$ if and only if $\lvert B(x, y)\rvert \le 1$ for
  every $y \in M$;
* `dualGam Q v γ N hN` (the **dual basis** $\gamma' = \gamma N$ for a matrix $N$ with $GN = 1$).

**Proves**
* `isRootVector_congr`, `rootGroup_congr`, `localSpinorNormGroup_congr`, `theorem18OnlyIf_congr` (everything depends on
  $L$ only through $O(L_\mathfrak p)$);
* `locAct_eq_of_isDualLoc`, `locStabV_eq_of_isDualLoc` ($O(L_\mathfrak p) = O(L_\mathfrak p^\#)$);
* `isDualLoc_of_dualBasis`, `dualGam_dual`, `locGram_dualGam` (dual bases: $\gamma'^{\mathsf T}H\gamma = 1$ gives
  $\gamma'\mathfrak o^n = (\gamma\mathfrak o^n)^\#$; the Gram matrix of $\gamma N$ is $N$);
* `exists_lat_loc_eq` (a global lattice with a prescribed localization at one prime, by gluing, O'Meara 81:14);
* `theorem18OnlyIf_of_dual` (**Theorem 18 passes to $L$ from a lattice with the dual localization**),
  `exists_dual_lat`, `theorem18OnlyIf_of_dual_peelChainTheta`.

The family $K \perp 2\langle a\rangle \perp 8\langle b\rangle$ and the eighth residual statement are in
`Section9Theorem18DyadicResidual8.lean`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual7

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Theorem 18 depends on the lattice only through its local stabilizer -/

section Congr

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {L L' : Lat F n}
  {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F

/-- Root vectors only depend on $O(L_\mathfrak p)$. -/
theorem isRootVector_congr (h : locStabV Q v L = locStabV Q v L') (x : Fin n → Fv) :
    IsRootVector Q L v x ↔ IsRootVector Q L' v x := by
  unfold IsRootVector; rw [h]

/-- The root group only depends on $O(L_\mathfrak p)$. -/
theorem rootGroup_congr (h : locStabV Q v L = locStabV Q v L') : rootGroup Q L v = rootGroup Q L' v := by
  ext c
  simp only [mem_rootGroup, isRootVector_congr h]

/-- $\theta(O^+(L_\mathfrak p))$ only depends on $O(L_\mathfrak p)$. -/
theorem localSpinorNormGroup_congr (hQ : Q.Nondegenerate) (h : locStabV Q v L = locStabV Q v L') :
    localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q hQ v L' := by
  unfold localSpinorNormGroup; rw [h]

/-- **Theorem 18's condition only depends on $O(L_\mathfrak p)$.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (the condition depends on L only through O(L_p))"]
theorem theorem18OnlyIf_congr (hQ : Q.Nondegenerate) (h : locStabV Q v L = locStabV Q v L') :
    Theorem18OnlyIf Q L v hQ ↔ Theorem18OnlyIf Q L' v hQ := by
  rw [theorem18OnlyIf_iff, theorem18OnlyIf_iff, localSpinorNormGroup_congr hQ h, rootGroup_congr h]

end Congr

/-! ### Dual local lattices -/

section Dual

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F

variable (Q) in
/-- **$M'$ is the dual of $M$** (a **condition** on two local lattices): $x \in M'$ if and only if
$\lvert B(x, y)\rvert \le 1$ for every $y \in M$, i.e. $M' = M^\# = \{x : B(x, M) \subseteq \mathfrak o_v\}$. -/
@[kb "omeara1963" "§82F, p. 229 (the dual lattice L^#, locally)"]
def IsDualLoc (M M' : Submodule (v.adicCompletionIntegers F) (Fin n → Fv)) : Prop :=
  ∀ x, x ∈ M' ↔ ∀ y ∈ M, Valued.v (qbil Q Fv x y) ≤ 1

/-- An isometry with $\tau M = M$ maps the dual $M^\#$ into itself. -/
theorem locAct_le_of_isDualLoc {M M' : Submodule (v.adicCompletionIntegers F) (Fin n → Fv)}
    (hd : IsDualLoc Q M M') {τ : orthGroup Q Fv} (hτ : locAct v (τ : GL (Fin n) Fv) M = M) :
    locAct v (τ : GL (Fin n) Fv) M' ≤ M' := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := mem_locAct.mp hw
  have hx' := (hd x).mp hx
  refine (hd _).mpr fun y hy => ?_
  rw [← hτ] at hy
  obtain ⟨z, hz, rfl⟩ := mem_locAct.mp hy
  rw [qbil_orth]
  exact hx' z hz

/-- **An isometry preserving $M$ preserves its dual $M^\#$.** -/
@[kb "omeara1963" "§82F, p. 229 (an isometry of L is an isometry of L^#)"]
theorem locAct_eq_of_isDualLoc {M M' : Submodule (v.adicCompletionIntegers F) (Fin n → Fv)}
    (hd : IsDualLoc Q M M') {σ : orthGroup Q Fv} (hσ : locAct v (σ : GL (Fin n) Fv) M = M) :
    locAct v (σ : GL (Fin n) Fv) M' = M' := by
  have hσi : locAct v ((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv) M = M := by
    have := (locAct_eq_iff.mp hσ).symm
    simpa using this
  refine le_antisymm (locAct_le_of_isDualLoc hd hσ) ?_
  intro x hx
  have hx' : (((σ⁻¹ : orthGroup Q Fv) : GL (Fin n) Fv)).val *ᵥ x ∈ M' :=
    locAct_le_of_isDualLoc hd hσi ⟨x, hx, rfl⟩
  refine ⟨_, hx', ?_⟩
  change (σ : GL (Fin n) Fv).val *ᵥ (((σ : GL (Fin n) Fv)⁻¹).val *ᵥ x) = x
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **$O(L_\mathfrak p) = O(L'_\mathfrak p)$ for mutually dual localizations.** -/
@[kb "omeara1963" "§82F, p. 229 (O(L) = O(L^#), locally)"]
theorem locStabV_eq_of_isDualLoc {L L' : Lat F n} (h₁ : IsDualLoc Q (loc v L.1) (loc v L'.1))
    (h₂ : IsDualLoc Q (loc v L'.1) (loc v L.1)) : locStabV Q v L = locStabV Q v L' := by
  ext σ
  exact ⟨fun hσ => locAct_eq_of_isDualLoc h₁ hσ, fun hσ => locAct_eq_of_isDualLoc h₂ hσ⟩

/-- $B(\gamma' c, \gamma d) = c \cdot d$ when $\gamma'^{\mathsf T}H\gamma = 1$. -/
theorem qbil_dualBasis (γ γ' : GL (Fin n) Fv)
    (h : (γ'.val)ᵀ * Q.hessian.map (algebraMap F Fv) * γ.val = 1) (c d : Fin n → Fv) :
    qbil Q Fv (γ'.val *ᵥ c) (γ.val *ᵥ d) = c ⬝ᵥ d := by
  unfold qbil
  set H := Q.hessian.map (algebraMap F Fv)
  calc (γ'.val *ᵥ c) ⬝ᵥ (H *ᵥ (γ.val *ᵥ d)) = (H *ᵥ (γ.val *ᵥ d)) ⬝ᵥ (γ'.val *ᵥ c) := dotProduct_comm _ _
    _ = ((H *ᵥ (γ.val *ᵥ d)) ᵥ* γ'.val) ⬝ᵥ c := dotProduct_mulVec _ _ _
    _ = ((γ'.val)ᵀ *ᵥ (H *ᵥ (γ.val *ᵥ d))) ⬝ᵥ c := by rw [mulVec_transpose]
    _ = (((γ'.val)ᵀ * H * γ.val) *ᵥ d) ⬝ᵥ c := by simp only [mulVec_mulVec, Matrix.mul_assoc]
    _ = c ⬝ᵥ d := by rw [h, one_mulVec, dotProduct_comm]

/-- **Dual bases give dual lattices**: if $\gamma'^{\mathsf T}H\gamma = 1$ then
$\gamma'\mathfrak o_v^n = (\gamma\mathfrak o_v^n)^\#$. -/
@[kb "omeara1963" "§82F, p. 229 (the dual basis spans the dual lattice)"]
theorem isDualLoc_of_dualBasis (γ γ' : GL (Fin n) Fv)
    (h : (γ'.val)ᵀ * Q.hessian.map (algebraMap F Fv) * γ.val = 1) :
    IsDualLoc Q (locAct v γ (std v)) (locAct v γ' (std v)) := by
  intro x
  have hx : x = γ'.val *ᵥ ((γ'⁻¹ : GL (Fin n) Fv).val *ᵥ x) := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [mem_locAct_std_iff]
  constructor
  · intro hc y hy
    obtain ⟨d, hd, rfl⟩ := mem_locAct.mp hy
    have hd1 := mem_std_iff.mp hd
    rw [hx, qbil_dualBasis γ γ' h]
    simp only [dotProduct]
    exact Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hc j) (hd1 j)
  · intro hB i
    have := hB (γ.val *ᵥ Pi.single i 1) ⟨_, single_mem_std i (by simp), rfl⟩
    rwa [hx, qbil_dualBasis γ γ' h, dotProduct_single, mul_one] at this

/-- The symmetric relation: $\gamma'^{\mathsf T}H\gamma = 1$ implies $\gamma^{\mathsf T}H\gamma' = 1$. -/
theorem dualBasis_symm (γ γ' : GL (Fin n) Fv)
    (h : (γ'.val)ᵀ * Q.hessian.map (algebraMap F Fv) * γ.val = 1) :
    (γ.val)ᵀ * Q.hessian.map (algebraMap F Fv) * γ'.val = 1 := by
  have := congrArg Matrix.transpose h
  simpa [transpose_mul, Matrix.mul_assoc, ← Matrix.transpose_map, QuadForm.hessian_transpose] using this

end Dual

/-! ### A global lattice with a prescribed localization at one prime -/

section Exists

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **A global lattice with a prescribed localization at one prime**: for every prime $v$ and
$\gamma \in GL_n(F_v)$ there is a lattice $L'$ on $F^n$ with $L'_v = \gamma\mathfrak o_v^n$ (glue the family which is
$\gamma\mathfrak o_v^n$ at $v$ and standard elsewhere; O'Meara 81:14, `LocFamily.loc_glue`). -/
@[kb "omeara1963" "§81E, 81:14, p. 218 (a lattice with one prescribed localization)"]
theorem exists_lat_loc_eq (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) (v.adicCompletion F)) :
    ∃ L' : Lat F n, loc v L'.1 = locAct v γ (std v) := by
  classical
  let g : ∀ w : HeightOneSpectrum (𝓞 F), GL (Fin n) (w.adicCompletion F) :=
    Function.update (fun w => (1 : GL (Fin n) (w.adicCompletion F))) v γ
  let M : LocFamily F n :=
    { M := fun w => locAct w (g w) (std w)
      isLattice := fun w => locAct_isLattice _ (isLattice_of_bounds w le_rfl le_rfl)
      eventually_std := by
        filter_upwards [Filter.eventually_cofinite_ne v] with w hw
        simp only [g, Function.update_of_ne hw, locAct_one] }
  refine ⟨⟨M.glue, M.glue_isLattice⟩, ?_⟩
  change loc v M.glue = _
  rw [M.loc_glue v]
  simp only [M, g, Function.update_self]

end Exists

/-! ### Dual bases from an inverse Gram matrix, and the transfer of Theorem 18 -/

section Transfer

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q v) in
/-- **The dual basis** $\gamma' = \gamma N$ of $\gamma$, for a matrix $N$ with $GN = 1$ ($G$ = `locGram Q v γ`). -/
def dualGam (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1) : GL (Fin n) Fv :=
  γ * ⟨N, locGram Q v γ, hN.symm ▸ (mul_eq_one_comm.mp hN), hN⟩

theorem dualGam_val (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1) :
    (dualGam Q v γ N hN).val = γ.val * N := rfl

/-- $\gamma'^{\mathsf T}H\gamma = 1$ for $\gamma' = \gamma N$, $GN = 1$. -/
theorem dualGam_dual (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1) :
    ((dualGam Q v γ N hN).val)ᵀ * Q.hessian.map (algebraMap ℚ Fv) * γ.val = 1 := by
  have hNG : N * locGram Q v γ = 1 := mul_eq_one_comm.mp hN
  have hT : Nᵀ * locGram Q v γ = 1 := by
    have := congrArg Matrix.transpose hN
    rwa [transpose_mul, locGram_transpose, transpose_one] at this
  rw [dualGam_val, transpose_mul, ← hT]
  unfold locGram
  simp only [Matrix.mul_assoc]

/-- **The Gram matrix of the dual basis** $\gamma N$ is $N$ (for $GN = 1$). -/
theorem locGram_dualGam (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1) :
    locGram Q v (dualGam Q v γ N hN) = N := by
  have hT : Nᵀ * locGram Q v γ = 1 := by
    have := congrArg Matrix.transpose hN
    rwa [transpose_mul, locGram_transpose, transpose_one] at this
  unfold dualGam
  rw [locGram_mul]
  change Nᵀ * locGram Q v γ * N = N
  rw [hT, Matrix.one_mul]

/-- **Theorem 18 passes to $L$ from a lattice with the dual localization** (unconditional): if $L'_v = L_v^\#$ and
$L_v = L_v'^\#$, then `Theorem18OnlyIf` for $L'$ gives it for $L$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (the 'only if' condition passes between L_p and its dual)"]
theorem theorem18OnlyIf_of_dual (hQ : Q.Nondegenerate) {L' : Lat ℚ n}
    (h₁ : IsDualLoc Q (loc v L.1) (loc v L'.1)) (h₂ : IsDualLoc Q (loc v L'.1) (loc v L.1))
    (h : Theorem18OnlyIf Q L' v hQ) : Theorem18OnlyIf Q L v hQ :=
  (theorem18OnlyIf_congr hQ (locStabV_eq_of_isDualLoc h₁ h₂)).mpr h

/-- **The dual lattice in a basis**: for a basis $\gamma$ of $L_v$ and $N$ with $GN = 1$ there is a lattice $L'$ with
$L'_v = \gamma N\mathfrak o_v^n$, and $L_v$, $L'_v$ are mutually dual. -/
theorem exists_dual_lat (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) :
    ∃ L' : Lat ℚ n, loc v L'.1 = locAct v (dualGam Q v γ N hN) (std v) ∧
      IsDualLoc Q (loc v L.1) (loc v L'.1) ∧ IsDualLoc Q (loc v L'.1) (loc v L.1) := by
  obtain ⟨L', hL'⟩ := exists_lat_loc_eq v (dualGam Q v γ N hN)
  refine ⟨L', hL', ?_, ?_⟩
  · rw [hγ, hL']
    exact isDualLoc_of_dualBasis γ _ (dualGam_dual γ N hN)
  · rw [hγ, hL']
    exact isDualLoc_of_dualBasis _ γ (dualBasis_symm _ _ (dualGam_dual γ N hN))

/-- **Theorem 18, "only if", from a peeling chain of the dual Gram matrix** (unconditional): if $GN = 1$ and $N$
(the Gram matrix of the dual basis) has a peeling chain with a spinor-norm remainder (`PeelChainTheta`), then
Theorem 18's condition holds for $L$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a peeling chain for the dual lattice)"]
theorem theorem18OnlyIf_of_dual_peelChainTheta (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) (ks : List (Fin n)) (hc : PeelChainTheta N ∅ ks) :
    Theorem18OnlyIf Q L v hQ := by
  obtain ⟨L', hL', h₁, h₂⟩ := exists_dual_lat γ hγ N hN
  refine theorem18OnlyIf_of_dual hQ h₁ h₂ ?_
  refine theorem18OnlyIf_of_peelChainTheta hQ h2 (dualGam Q v γ N hN) hL' ks ?_
  rwa [locGram_dualGam]

end Transfer

end QuadFormsKB.ConwaySloane
