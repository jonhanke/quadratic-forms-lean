/-
# O'Meara §102A: proper classes, proper genera and proper spinor genera

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n`; lattices on $V$ are `Lat F n`,
their localizations `loc 𝔭 L`, the finite adelic orthogonal group `OAf Q` (O'Meara's $J_V$, restricted to the finite
spots) acting on lattices by `latSMul`; rotations are `Tamagawa.soSub` ($O^+$), the spinor kernel is `spinorKernel`
($O'$) and its adelic version `spinorKernelAf` ($J'_V$). The full-orthogonal-group notions are in the library already:
`IsIsometric` (class), `SameGenus` (genus), `SameSpinorGenus` (spinor genus), `genusClasses`.

**Proves** first a local fact used throughout (O'Meara 91:4 in this setting): every lattice $M$ on the regular space
$V_\mathfrak p$ is carried onto itself by a symmetry (`exists_symm_locAct_eq`), so $O(M)$ contains an element of
determinant $-1$; and then (O'Meara 1973, §102A, pp. 297–299):
* the proper class (`IsProperIsometric`), proper genus (`SameProperGenus`) and proper spinor genus
  (`SameProperSpinorGenus`), each an equivalence relation, so that the lattices on $V$ are partitioned into proper
  classes, proper genera and proper spinor genera (102.r4, 102.r5, 102.r14, 102.r15);
* $\operatorname{gen}L = \operatorname{gen}^+L$ (`sameProperGenus_iff_sameGenus`, 102.r7);
* $\operatorname{cls}^+L \subseteq \operatorname{spn}^+L \subseteq \operatorname{gen}^+L$, and
  $\operatorname{spn}^+L \subseteq \operatorname{spn}L$;
* the proper spinor genus through split rotations (`sameProperSpinorGenus_iff`);
* Example 102:1: $\Sigma\operatorname{spn}L = \operatorname{spn}\Sigma L$ and $\Sigma\operatorname{spn}^+L = \operatorname{spn}^+\Sigma L$
  for $\Sigma \in J_V$ (`latSpinorGenus_smul`, `latProperSpinorGenus_smul`);
* the numbers $h(L)$, $h^+(L)$ (`classNumber`, `properClassNumber`, 102.r13, 102.r16) and Example 102:2, first part:
  $h(L) \le h^+(L) \le 2h(L)$ (`classNumber_le_properClassNumber`, `properClassNumber_le_two_mul`).

*Conventions.* As elsewhere in the library, only the finite spots are used (at an infinite spot every two lattices
span the same space, and the local conditions of the genus are empty); `J_V` is `OAf Q`, built from the full local
orthogonal groups rather than from $O^+(V_\mathfrak p)$ (the proper spinor genus only uses elements of $O'(V_\mathfrak p)
\subseteq O^+(V_\mathfrak p)$, so this does not matter). Counting numbers are `Set.ncard`, which is $0$ for an infinite
set; the inequalities of 102:2 hold in that case too.
-/
import QuadFormsKB.Literature.OMeara.Sec101A
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Lattices.SAPerpCoords

open NumberField IsDedekindDomain Matrix WithZero Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### A symmetry in $O(M)$ for every local lattice $M$ -/

section LocalSymmetry

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {v} in
theorem valued_dotProduct_le (x y : Fin n → Fv) : Valued.v (x ⬝ᵥ y) ≤ vecNorm v x * vecNorm v y := by
  rw [dotProduct]
  exact Valuation.map_sum_le _ fun i _ => by rw [map_mul]; exact mul_le_mul' (le_vecNorm x i) (le_vecNorm y i)

variable {v} in
/-- $\lvert Q(x)\rvert \le \lVert x\rVert\,\lVert C\rVert\,\lVert x\rVert$ for the coefficient matrix $C$ of $Q$
(O'Meara 1973, §101A, p. 288: $\lvert Q(x)\rvert \le A\lVert x\rVert^2$). -/
@[kb "omeara1963" "§101A, p. 288 (|Q(x)| ≤ A‖x‖², non-archimedean)"]
theorem valued_evalIn_le (x : Fin n → Fv) :
    Valued.v (Q.evalIn Fv x) ≤ vecNorm v x * (matNorm v (Q.coeff.map (algebraMap F Fv)) * vecNorm v x) := by
  rw [QuadForm.evalIn_eq_dotProduct]
  exact (valued_dotProduct_le _ _).trans (mul_le_mul_right (vecNorm_mulVec_le _ _) _)

/-- A lattice on a regular space $V_\mathfrak p$ ($n \ge 1$) contains an anisotropic vector. -/
theorem exists_mem_evalIn_ne_zero (hQ : Q.Nondegenerate) (hn : 0 < n) {M : Submodule 𝔬 (Fin n → Fv)}
    (hM : M.IsLattice Fv) : ∃ z ∈ M, Q.evalIn Fv z ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := QuadForm.exists_eval_ne_zero Q hQ hn
  obtain ⟨k, hk, -⟩ := exists_local_bounds v hM
  set y := locVec v y₀
  have hy : Q.evalIn Fv y ≠ 0 := by rw [evalIn_locVec]; exact (map_ne_zero _).mpr hy₀
  have hy0 : y ≠ 0 := by rintro h; apply hy; rw [h]; simp [QuadForm.evalIn]
  have hn0 : vecNorm v y ≠ 0 := fun h => hy0 (vecNorm_eq_zero_iff.mp h)
  set j : ℤ := k + log (vecNorm v y)
  refine ⟨ϖk v j • y, hk ((mem_ball v).mpr fun i => ?_), ?_⟩
  · have : Valued.v ((ϖk v j • y) i) ≤ vecNorm v (ϖk v j • y) := le_vecNorm _ i
    refine this.trans ?_
    rw [vecNorm_smul, valued_ϖk, ← exp_log hn0, ← exp_add]
    simp [j]
  · rw [evalIn_smul']
    exact mul_ne_zero (pow_ne_zero _ (ϖk_ne_zero v j)) hy

/-- **Every lattice on a regular space over a local field has a symmetry in $O(M)$** (O'Meara 1973, 91:4, p. 241,
in the coordinate setting: $M \subseteq F_\mathfrak p^n$ an $\mathfrak o_\mathfrak p$-lattice, $Q$ regular, $n \ge 1$,
dyadic $\mathfrak p$ included). Proof: take $x \in M$ with $\lvert Q(x)\rvert$ maximal (the values on $M$ are bounded);
then $\lvert B(x, y)\rvert \le \lvert Q(x)\rvert$ for $y \in M$, so $\tau_x y = y - \frac{B(x,y)}{Q(x)}x \in M$. -/
@[kb "omeara1963" "§91B, 91:4, p. 241 (a symmetry in O(L))"]
theorem exists_symm_locAct_eq (hQ : Q.Nondegenerate) (hn : 0 < n) {M : Submodule 𝔬 (Fin n → Fv)}
    (hM : M.IsLattice Fv) :
    ∃ x ∈ M, Q.evalIn Fv x ≠ 0 ∧ locAct v (symm Q Fv x : GL (Fin n) Fv) M = M := by
  classical
  obtain ⟨k, -, hk⟩ := exists_local_bounds v hM
  set c := matNorm v (Q.coeff.map (algebraMap F Fv))
  have hbd : ∀ z ∈ M, Valued.v (Q.evalIn Fv z) ≤ exp (k : ℤ) * (c * exp (k : ℤ)) := by
    intro z hz
    have hz' : vecNorm v z ≤ exp (k : ℤ) := vecNorm_le_iff.mpr fun i => by
      simpa using (mem_ball v).mp (hk hz) i
    exact (valued_evalIn_le Q z).trans (mul_le_mul' hz' (mul_le_mul_right hz' _))
  obtain ⟨z₀, hz₀M, hz₀⟩ := exists_mem_evalIn_ne_zero Q v hQ hn hM
  set B := exp (k : ℤ) * (c * exp (k : ℤ))
  have hB : B ≠ 0 := by
    intro h
    have := hbd z₀ hz₀M
    rw [h] at this
    exact hz₀ ((Valuation.zero_iff _).mp (le_antisymm this zero_le))
  let P : ℤ → Prop := fun t => ∃ z ∈ M, Q.evalIn Fv z ≠ 0 ∧ Valued.v (Q.evalIn Fv z) = exp t
  have hPb : ∃ b, ∀ t, P t → t ≤ b := ⟨log B, fun t ht => by
    obtain ⟨z, hz, -, he⟩ := ht
    rw [← exp_le_exp, exp_log hB, ← he]; exact hbd z hz⟩
  have hPn : ∃ t, P t := ⟨log (Valued.v (Q.evalIn Fv z₀)), z₀, hz₀M, hz₀,
    (exp_log ((Valuation.ne_zero_iff _).mpr hz₀)).symm⟩
  obtain ⟨t₀, ⟨x, hxM, hx0, hxt⟩, hmax⟩ := Int.exists_greatest_of_bdd hPb hPn
  have hle : ∀ z ∈ M, Valued.v (Q.evalIn Fv z) ≤ Valued.v (Q.evalIn Fv x) := by
    intro z hz
    by_cases hz0 : Q.evalIn Fv z = 0
    · rw [hz0, map_zero]; exact zero_le
    · have hne : Valued.v (Q.evalIn Fv z) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
      rw [hxt, ← exp_log hne, exp_le_exp]
      exact hmax _ ⟨z, hz, hz0, (exp_log hne).symm⟩
  have hQx : Valued.v (Q.evalIn Fv x) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hmaps : ∀ y ∈ M, ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ M := by
    intro y hy
    rw [symm_mulVec_bil Q Fv hx0]
    have hb : Valued.v (qbil Q Fv x y) ≤ Valued.v (Q.evalIn Fv x) := by
      rw [qbil_eq_polar]
      exact Valuation.map_sub_le _ (Valuation.map_sub_le _ (hle _ (M.add_mem hxM hy)) le_rfl) (hle y hy)
    have hc : Valued.v (qbil Q Fv x y / Q.evalIn Fv x) ≤ 1 := by
      rw [map_div₀, div_eq_mul_inv, ← mul_inv_cancel₀ hQx]
      exact mul_le_mul_left hb _
    have hcx : (qbil Q Fv x y / Q.evalIn Fv x) • x ∈ M :=
      M.smul_mem (⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hxM
    exact M.sub_mem hy hcx
  refine ⟨x, hxM, hx0, le_antisymm ?_ fun y hy => ⟨_, hmaps y hy, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmaps y hy
  · show ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ
      (((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, symm_mul_self]
    simp

/-- **An improper local isometry of every lattice** (O'Meara 1973, 91:4, p. 241, and Corollary 91:4a): for $Q$
regular and $n \ge 1$, every lattice $M$ on $V_\mathfrak p$ is carried onto itself by an isometry of determinant
$-1$. -/
@[kb "omeara1963" "§91B, 91:4, p. 241 (O(L) contains a reflexion)"]
theorem exists_det_neg_one_locAct_eq (hQ : Q.Nondegenerate) (hn : 0 < n) {M : Submodule 𝔬 (Fin n → Fv)}
    (hM : M.IsLattice Fv) :
    ∃ g : orthGroup Q Fv, ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det = -1 ∧
      locAct v (g : GL (Fin n) Fv) M = M := by
  obtain ⟨x, -, hx0, hx⟩ := exists_symm_locAct_eq Q v hQ hn hM
  exact ⟨symm Q Fv x, symm_det Q Fv hx0, hx⟩

end LocalSymmetry

/-! ### Proper classes and proper genera -/

section Proper

variable (Q : QuadForm F n)

/-- **Same proper class** (O'Meara 1973, §82C, p. 222; §102A): $M = \sigma L$ for a rotation $\sigma \in O^+(V)$. -/
@[kb "omeara1963" "§82C, p. 222 (cls⁺ L); §102A, p. 298"]
def IsProperIsometric (L M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∃ γ : orthGroup Q F, γ ∈ Tamagawa.soSub Q F ∧ glImage (γ : GL (Fin n) F) L = M

theorem IsProperIsometric.refl (L : Submodule (𝓞 F) (Fin n → F)) : IsProperIsometric Q L L :=
  ⟨1, (Tamagawa.soSub Q F).one_mem, glImage_one L⟩

theorem IsProperIsometric.symm {L M : Submodule (𝓞 F) (Fin n → F)} (h : IsProperIsometric Q L M) :
    IsProperIsometric Q M L := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨γ⁻¹, (Tamagawa.soSub Q F).inv_mem hγ, ?_⟩
  rw [Subgroup.coe_inv, ← glImage_mul, inv_mul_cancel, glImage_one]

theorem IsProperIsometric.trans {L M N : Submodule (𝓞 F) (Fin n → F)} (h : IsProperIsometric Q L M)
    (h' : IsProperIsometric Q M N) : IsProperIsometric Q L N := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨δ, hδ, rfl⟩ := h'
  exact ⟨δ * γ, (Tamagawa.soSub Q F).mul_mem hδ hγ, by rw [Subgroup.coe_mul, glImage_mul]⟩

/-- A proper class lies in the class. -/
theorem IsProperIsometric.isIsometric {L M : Submodule (𝓞 F) (Fin n → F)} (h : IsProperIsometric Q L M) :
    IsIsometric Q L M := by
  obtain ⟨γ, -, he⟩ := h
  exact ⟨γ, γ.2, he⟩

/-- **The proper genus** (O'Meara 1973, §102A, p. 297): $M \in \operatorname{gen}^+L$ if for each spot $\mathfrak p$
there is a rotation $\Sigma_\mathfrak p \in O^+(V_\mathfrak p)$ with $M_\mathfrak p = \Sigma_\mathfrak pL_\mathfrak p$
(equivalently, $\operatorname{cls}^+M_\mathfrak p = \operatorname{cls}^+L_\mathfrak p$ for all $\mathfrak p$, 102.r6). -/
@[kb "omeara1963" "§102A, p. 297 (gen⁺ L)"]
def SameProperGenus (L M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : orthGroup Q (v.adicCompletion F),
    g ∈ Tamagawa.soSub Q (v.adicCompletion F) ∧ locAct v (g : GL (Fin n) _) (loc v L) = loc v M

/-- The lattices on $V$ are partitioned into proper genera (O'Meara 1973, §102A, p. 297). -/
@[kb "omeara1963" "§102A, p. 297 (partition into proper genera)"]
theorem SameProperGenus.refl (L : Submodule (𝓞 F) (Fin n → F)) : SameProperGenus Q L L :=
  fun _ => ⟨1, (Tamagawa.soSub Q _).one_mem, locAct_one _⟩

@[kb "omeara1963" "§102A, p. 297 (partition into proper genera)"]
theorem SameProperGenus.symm {L M : Submodule (𝓞 F) (Fin n → F)} (h : SameProperGenus Q L M) :
    SameProperGenus Q M L := fun v => by
  obtain ⟨g, hg, he⟩ := h v
  exact ⟨g⁻¹, (Tamagawa.soSub Q _).inv_mem hg, by rw [Subgroup.coe_inv, ← he, locAct_inv_locAct]⟩

@[kb "omeara1963" "§102A, p. 297 (partition into proper genera)"]
theorem SameProperGenus.trans {L M N : Submodule (𝓞 F) (Fin n → F)} (h : SameProperGenus Q L M)
    (h' : SameProperGenus Q M N) : SameProperGenus Q L N := fun v => by
  obtain ⟨g, hg, he⟩ := h v
  obtain ⟨g', hg', he'⟩ := h' v
  exact ⟨g' * g, (Tamagawa.soSub Q _).mul_mem hg' hg, by rw [Subgroup.coe_mul, locAct_mul, he, he']⟩

theorem SameProperGenus.sameGenus {L M : Submodule (𝓞 F) (Fin n → F)} (h : SameProperGenus Q L M) :
    SameGenus Q L M := fun v => by
  obtain ⟨g, -, he⟩ := h v
  exact ⟨g, g.2, he⟩

/-- **$\operatorname{gen}L = \operatorname{gen}^+L$** (O'Meara 1973, §102A, p. 298: "the class and the proper class
coincide over local fields"): for a regular $V$, two lattices are in the same genus if and only if they are in the
same proper genus. The local input is `exists_det_neg_one_locAct_eq` (91:4). -/
@[kb "omeara1963" "§102A, p. 298 (gen L = gen⁺ L)"]
theorem sameProperGenus_iff_sameGenus (hQ : Q.Nondegenerate) {L M : Submodule (𝓞 F) (Fin n → F)}
    (hL : L.IsLattice F) : SameProperGenus Q L M ↔ SameGenus Q L M := by
  refine ⟨SameProperGenus.sameGenus Q, fun h v => ?_⟩
  obtain ⟨g, hg, he⟩ := h v
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨g, hg⟩ with h1 | h1
  · exact ⟨⟨g, hg⟩, h1, he⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨⟨g, hg⟩, by simp [Tamagawa.mem_soSub], he⟩
    obtain ⟨τ, hτ, hτL⟩ := exists_det_neg_one_locAct_eq Q v hQ hn (loc_isLattice v hL)
    refine ⟨⟨g, hg⟩ * τ, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
      change g.val.det * _ = 1
      rw [show g.val.det = -1 from h1, hτ]; ring
    · rw [Subgroup.coe_mul, locAct_mul, hτL]; exact he

/-! ### The proper spinor genus -/

/-- **The group $O^+(V)\,J'_V$** (inside $O(V)(\mathbb A_f)$): generated by the principal split rotations
$(\sigma)$, $\sigma \in O^+(V)$, and the adelic spinor kernel. -/
def spnPlusGroup : Subgroup (OAf Q) := (Tamagawa.soSub Q F).map (diagF Q) ⊔ spinorKernelAf Q

theorem mem_spnPlusGroup {g : OAf Q} :
    g ∈ spnPlusGroup Q ↔ ∃ γ ∈ Tamagawa.soSub Q F, ∃ k ∈ spinorKernelAf Q, g = diagF Q γ * k := by
  rw [← SetLike.mem_coe, spnPlusGroup, Subgroup.mul_normal]
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, k, hk, rfl⟩
    exact ⟨γ, hγ, k, hk, rfl⟩
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨_, ⟨γ, hγ, rfl⟩, k, hk, rfl⟩

theorem spnPlusGroup_le_spnGroup : spnPlusGroup Q ≤ spnGroup Q :=
  sup_le_sup (Subgroup.map_le_range _ _) le_rfl

theorem spnPlusGroup_normal (hQ : Q.Nondegenerate) : (spnPlusGroup Q).Normal :=
  normal_of_spinorKernelAf_le Q hQ le_sup_right

/-- **Same proper spinor genus** (O'Meara 1973, §102A, p. 298): $M = \sigma\Sigma L$ for a rotation
$\sigma \in O^+(V)$ and a split rotation $\Sigma \in J'_V$ (`sameProperSpinorGenus_iff`); here stated as
$M = gL$ for $g$ in the group $O^+(V)J'_V$. -/
@[kb "omeara1963" "§102A, p. 298 (spn⁺ L)"]
def SameProperSpinorGenus (L M : Lat F n) : Prop := ∃ g ∈ spnPlusGroup Q, latSMul Q g L = M

/-- **The proper spinor genus through split rotations** (O'Meara 1973, §102A, p. 298): $M \in \operatorname{spn}^+L$
if and only if $M = \sigma\Sigma L$ with $\sigma \in O^+(V)$ and $\Sigma \in J'_V$. -/
@[kb "omeara1963" "§102A, p. 298 (spn⁺ L: K = σΣL, σ ∈ O⁺(V), Σ ∈ J'_V)"]
theorem sameProperSpinorGenus_iff {L M : Lat F n} :
    SameProperSpinorGenus Q L M ↔ ∃ γ ∈ Tamagawa.soSub Q F, ∃ k ∈ spinorKernelAf Q,
      M = latSMul Q (diagF Q γ) (latSMul Q k L) := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨γ, hγ, k, hk, rfl⟩ := (mem_spnPlusGroup Q).mp hg
    exact ⟨γ, hγ, k, hk, mul_smul (diagF Q γ) k L⟩
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨diagF Q γ * k, (mem_spnPlusGroup Q).mpr ⟨γ, hγ, k, hk, rfl⟩, mul_smul (diagF Q γ) k L⟩

/-- The lattices on $V$ are partitioned into proper spinor genera (O'Meara 1973, §102A, pp. 298–299). -/
@[kb "omeara1963" "§102A, pp. 298–299 (partition into proper spinor genera)"]
theorem SameProperSpinorGenus.refl (L : Lat F n) : SameProperSpinorGenus Q L L :=
  ⟨1, (spnPlusGroup Q).one_mem, (latAction Q).one_smul L⟩

@[kb "omeara1963" "§102A, pp. 298–299 (partition into proper spinor genera)"]
theorem SameProperSpinorGenus.symm {L M : Lat F n} (h : SameProperSpinorGenus Q L M) :
    SameProperSpinorGenus Q M L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, (spnPlusGroup Q).inv_mem hg, inv_smul_smul g L⟩

@[kb "omeara1963" "§102A, pp. 298–299 (partition into proper spinor genera)"]
theorem SameProperSpinorGenus.trans {L M N : Lat F n} (h : SameProperSpinorGenus Q L M)
    (h' : SameProperSpinorGenus Q M N) : SameProperSpinorGenus Q L N := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  exact ⟨g' * g, (spnPlusGroup Q).mul_mem hg' hg, mul_smul g' g L⟩

/-- $\operatorname{spn}^+L \subseteq \operatorname{spn}L$. -/
theorem SameProperSpinorGenus.sameSpinorGenus {L M : Lat F n} (h : SameProperSpinorGenus Q L M) :
    SameSpinorGenus Q L M := by
  obtain ⟨g, hg, he⟩ := h
  exact (sameSpinorGenus_iff Q).mpr ⟨g, spnPlusGroup_le_spnGroup Q hg, he⟩

/-- **$\operatorname{cls}^+L \subseteq \operatorname{spn}^+L$** (O'Meara 1973, §102A, p. 299). -/
@[kb "omeara1963" "§102A, p. 299 (cls⁺ L ⊆ spn⁺ L)"]
theorem IsProperIsometric.sameProperSpinorGenus {L M : Lat F n} (h : IsProperIsometric Q L.1 M.1) :
    SameProperSpinorGenus Q L M := by
  obtain ⟨γ, hγ, he⟩ := h
  refine (sameProperSpinorGenus_iff Q).mpr ⟨γ, hγ, 1, (spinorKernelAf Q).one_mem, ?_⟩
  apply Lat.ext
  rw [show latSMul Q 1 L = L from (latAction Q).one_smul L, diagF_smul]
  exact he.symm

/-- Elements of $O'(V_\mathfrak p)$ are rotations. -/
theorem spinorKernel_le_soSub (K : Type*) [Field K] [Algebra F K] [CharZero K] :
    spinorKernel Q K ≤ Tamagawa.soSub Q K := by
  rintro _ ⟨xs, ⟨hxa, hxe, -⟩, rfl⟩
  rw [Tamagawa.mem_soSub, ← detHom_val, detHom_symmProd Q K xs hxa, hxe.neg_one_pow]

/-- **$\operatorname{spn}^+L \subseteq \operatorname{gen}^+L$** (O'Meara 1973, §102A, p. 299). -/
@[kb "omeara1963" "§102A, p. 299 (spn⁺ L ⊆ gen⁺ L)"]
theorem SameProperSpinorGenus.sameProperGenus {L M : Lat F n} (h : SameProperSpinorGenus Q L M) :
    SameProperGenus Q L.1 M.1 := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := (sameProperSpinorGenus_iff Q).mp h
  intro v
  refine ⟨orthMap Q _ γ * k v, (Tamagawa.soSub Q _).mul_mem ?_ (spinorKernel_le_soSub Q _ (hk v)), ?_⟩
  · rw [Tamagawa.mem_soSub, orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hγ, map_one]
  · rw [loc_latSMul, loc_latSMul, Subgroup.coe_mul, locAct_mul]
    rfl

/-- **Example 102:1** (O'Meara 1973, §102A, p. 299): $\Sigma\operatorname{spn}L = \operatorname{spn}\Sigma L$ for every
split rotation $\Sigma$ (here: every $\Sigma \in O(V)(\mathbb A_f)$). -/
@[kb "omeara1963" "§102A, 102:1, p. 299 (Σ spn L = spn ΣL)"]
theorem latSpinorGenus_smul (hQ : Q.Nondegenerate) (g : OAf Q) (L : Lat F n) :
    latSpinorGenus Q (latSMul Q g L) = latSMul Q g '' latSpinorGenus Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hN := spnGroup_normal Q hQ
  ext M
  change SameSpinorGenus Q _ M ↔ M ∈ latSMul Q g '' {M | SameSpinorGenus Q L M}
  simp only [sameSpinorGenus_iff, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨latSMul Q (g⁻¹ * h * g) L, ⟨_, hN.conj_mem' _ hh g, rfl⟩, ?_⟩
    change g • ((g⁻¹ * h * g) • L) = h • g • L
    rw [← mul_smul, ← mul_smul]; congr 1; group
  · intro hM
    obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := hM
    refine ⟨g * h * g⁻¹, hN.conj_mem _ hh g, ?_⟩
    change (g * h * g⁻¹) • g • L = g • h • L
    rw [← mul_smul, ← mul_smul]; congr 1; group

/-- **Example 102:1 for proper spinor genera** (O'Meara 1973, §102A, p. 299): $\Sigma\operatorname{spn}^+L =
\operatorname{spn}^+\Sigma L$. -/
@[kb "omeara1963" "§102A, 102:1, p. 299 (Σ spn⁺ L = spn⁺ ΣL)"]
theorem latProperSpinorGenus_smul (hQ : Q.Nondegenerate) (g : OAf Q) (L : Lat F n) :
    {M | SameProperSpinorGenus Q (latSMul Q g L) M} = latSMul Q g '' {M | SameProperSpinorGenus Q L M} := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hN := spnPlusGroup_normal Q hQ
  ext M
  simp only [SameProperSpinorGenus, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨latSMul Q (g⁻¹ * h * g) L, ⟨_, hN.conj_mem' _ hh g, rfl⟩, ?_⟩
    change g • ((g⁻¹ * h * g) • L) = h • g • L
    rw [← mul_smul, ← mul_smul]; congr 1; group
  · intro hM
    obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := hM
    refine ⟨g * h * g⁻¹, hN.conj_mem _ hh g, ?_⟩
    change (g * h * g⁻¹) • g • L = g • h • L
    rw [← mul_smul, ← mul_smul]; congr 1; group

/-! ### The numbers $h(L)$ and $h^+(L)$ -/

/-- **Proper isometry of lattices** as a setoid on `Lat F n`. -/
def properLatSetoid : Setoid (Lat F n) where
  r L M := IsProperIsometric Q L.1 M.1
  iseqv := ⟨fun L => IsProperIsometric.refl Q L.1, fun h => IsProperIsometric.symm Q h,
    fun h h' => IsProperIsometric.trans Q h h'⟩

/-- **Proper classes of lattices** on $V$. -/
abbrev ProperLatClass : Type _ := Quotient (properLatSetoid Q)

/-- **The proper classes in the genus** of $L$. -/
def properGenusClasses (L : Lat F n) : Set (ProperLatClass Q) :=
  {c | ∃ M : Lat F n, Quotient.mk _ M = c ∧ SameGenus Q L.1 M.1}

/-- **The class number** $h(L)$: the number of classes in $\operatorname{gen}L$ (O'Meara 1973, §102A, p. 298;
`0` if there are infinitely many, which does not happen by 103:4). -/
@[kb "omeara1963" "§102A, p. 298 (h(L))"]
def classNumber (L : Lat F n) : ℕ := (genusClasses Q L).ncard

/-- **The proper class number** $h^+(L)$: the number of proper classes in $\operatorname{gen}L$ (O'Meara 1973,
§102A, p. 299). -/
@[kb "omeara1963" "§102A, p. 299 (h⁺(L))"]
def properClassNumber (L : Lat F n) : ℕ := (properGenusClasses Q L).ncard

/-- The class of a proper class. -/
def ProperLatClass.toClass : ProperLatClass Q → LatClass Q :=
  Quotient.map id fun _ _ h => IsProperIsometric.isIsometric Q h

theorem image_toClass_properGenusClasses (L : Lat F n) :
    ProperLatClass.toClass Q '' properGenusClasses Q L = genusClasses Q L := by
  ext c
  constructor
  · rintro ⟨_, ⟨M, rfl, hM⟩, rfl⟩
    exact ⟨M, rfl, hM⟩
  · rintro ⟨M, rfl, hM⟩
    exact ⟨Quotient.mk _ M, ⟨M, rfl, hM⟩, rfl⟩

/-- Each class contains at most two proper classes: those of $M$ and of $\tau M$, $\tau$ an improper isometry. -/
theorem properGenusClasses_subset (hQ : Q.Nondegenerate) (L : Lat F n) (τ : orthGroup Q F)
    (hτ : ((τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1) :
    properGenusClasses Q L ⊆
      (fun c : LatClass Q => (Quotient.mk _ c.out : ProperLatClass Q)) '' genusClasses Q L ∪
      (fun c : LatClass Q => (Quotient.mk _ (Lat.image (τ : GL (Fin n) F) c.out) : ProperLatClass Q)) ''
        genusClasses Q L := by
  rintro _ ⟨M, rfl, hM⟩
  set c : LatClass Q := Quotient.mk _ M
  have hc : c ∈ genusClasses Q L := ⟨M, rfl, hM⟩
  have hrel : IsIsometric Q c.out.1 M.1 := Quotient.exact (Quotient.out_eq c)
  obtain ⟨γ, hγ, he⟩ := hrel
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨γ, hγ⟩ with h1 | h1
  · refine Or.inl ⟨c, hc, Quotient.sound ⟨⟨γ, hγ⟩, h1, he⟩⟩
  · refine Or.inr ⟨c, hc, Quotient.sound ⟨⟨γ, hγ⟩ * τ⁻¹, ?_, ?_⟩⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
      have hinv : (((τ⁻¹ : orthGroup Q F) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 := by
        have h := congrArg Matrix.det (Units.mul_inv (τ : GL (Fin n) F))
        rw [det_mul, hτ, det_one] at h
        rw [Subgroup.coe_inv]; linear_combination -h
      change ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det * _ = 1
      rw [show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 from h1, hinv]; ring
    · change glImage _ (glImage (τ : GL (Fin n) F) c.out.1) = M.1
      rw [← glImage_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]
      exact he

/-- For $n = 0$ the class and the proper class agree. -/
theorem properGenusClasses_subset_zero (hn : n = 0) (L : Lat F n) :
    properGenusClasses Q L ⊆
      (fun c : LatClass Q => (Quotient.mk _ c.out : ProperLatClass Q)) '' genusClasses Q L := by
  subst hn
  rintro _ ⟨M, rfl, hM⟩
  set c : LatClass Q := Quotient.mk _ M
  obtain ⟨γ, hγ, he⟩ : IsIsometric Q c.out.1 M.1 := Quotient.exact (Quotient.out_eq c)
  exact ⟨c, ⟨M, rfl, hM⟩, Quotient.sound ⟨⟨γ, hγ⟩, by simp [Tamagawa.mem_soSub], he⟩⟩

/-- **Example 102:2, $h(L) \le h^+(L)$** (O'Meara 1973, §102A, p. 299): each class in the genus contains a proper
class. -/
@[kb "omeara1963" "§102A, 102:2, p. 299 (h(L) ≤ h⁺(L))"]
theorem classNumber_le_properClassNumber (hQ : Q.Nondegenerate) (L : Lat F n) :
    classNumber Q L ≤ properClassNumber Q L := by
  unfold classNumber properClassNumber
  by_cases hfin : (properGenusClasses Q L).Finite
  · rw [← image_toClass_properGenusClasses]
    exact Set.ncard_image_le hfin
  · have hinf : ¬ (genusClasses Q L).Finite := by
      intro hG
      apply hfin
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact ((hG.image _)).subset (properGenusClasses_subset_zero Q hn L)
      · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
        exact ((hG.image _).union (hG.image _)).subset (properGenusClasses_subset Q hQ L τ hτ)
    rw [Set.Infinite.ncard hinf]
    exact Nat.zero_le _

/-- **Example 102:2, $h^+(L) \le 2h(L)$** (O'Meara 1973, §102A, p. 299): each class contains either one or two proper
classes. -/
@[kb "omeara1963" "§102A, 102:2, p. 299 (h⁺(L) ≤ 2h(L))"]
theorem properClassNumber_le_two_mul (hQ : Q.Nondegenerate) (L : Lat F n) :
    properClassNumber Q L ≤ 2 * classNumber Q L := by
  unfold classNumber properClassNumber
  by_cases hG : (genusClasses Q L).Finite
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · exact (Set.ncard_le_ncard (properGenusClasses_subset_zero Q hn L) (hG.image _)).trans
        ((Set.ncard_image_le hG).trans (by omega))
    · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
      refine (Set.ncard_le_ncard (properGenusClasses_subset Q hQ L τ hτ)
        ((hG.image _).union (hG.image _))).trans ((Set.ncard_union_le _ _).trans ?_)
      have h1 := Set.ncard_image_le (f := fun c : LatClass Q => (Quotient.mk _ c.out : ProperLatClass Q)) hG
      have h2 := Set.ncard_image_le
        (f := fun c : LatClass Q => (Quotient.mk _ (Lat.image (τ : GL (Fin n) F) c.out) : ProperLatClass Q)) hG
      omega
  · have hinf : ¬ (properGenusClasses Q L).Finite := fun hP => hG (by
      rw [← image_toClass_properGenusClasses]; exact hP.image _)
    rw [Set.Infinite.ncard hinf]
    exact Nat.zero_le _

end Proper

end QuadFormsKB.Lattices
