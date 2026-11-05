/-
# O'Meara §101B–§101D: localization, global spinor norms $D = \theta(O^+(V))$, and $P_D$

**Layer:** $F$ a number field, $V = F^n$ with `Q : QuadForm F n` nondegenerate. $O(V)$ = `orthGroup Q F`,
$O^+(V)$ = `Tamagawa.soSub Q F`, $O'(V)$ = `spinorKernel Q F`, $\Omega(V)$ = `commutator (orthGroup Q F)`, the spinor
norm $\theta$ = `spinorNormHom`, $D = \theta(O^+(V))$ = `spinorNormGroup Q hQ` (`Sec101B.lean`); the localization
$\sigma \mapsto \sigma_\mathfrak p$ is `orthMap Q (v.adicCompletion F)` on isometries and
`RingHom.mapMatrix (algebraMap F (v.adicCompletion F))` on matrices; $J_F$ = `IdeleGroup (𝓞 F) F`, $P_F$ =
`IdeleGroup.principalSubgroup`, $J_F^S$ = `sIdeles S` (`Sec64.lean`; the full idèle group, with its archimedean
components).

**Proves**
* 101.r29: localization $M_n(F) \to M_n(F_\mathfrak p)$ is an injective ring homomorphism preserving determinants
  and scalar multiplication (`localizeMat_spec`);
* 101.r32: $O(V)_\mathfrak p \subseteq O(V_\mathfrak p)$, $O^+(V)_\mathfrak p \subseteq O^+(V_\mathfrak p)$,
  $\Omega(V)_\mathfrak p \subseteq \Omega(V_\mathfrak p)$, $O'(V)_\mathfrak p \subseteq O'(V_\mathfrak p)$
  (`orthGroup_map_le`, `soSub_map_le`, `commutator_map_le`, `spinorKernel_map_le`);
* 101.r33: $O(L)_\mathfrak p \subseteq O(L_\mathfrak p)$, $O^+(L)_\mathfrak p \subseteq O^+(L_\mathfrak p)$
  (`autLat_map_le`, `autLat_inf_soSub_map_le`);
* 101.r34: every $\alpha \in D$ is positive at every real place at which $V_w$ is anisotropic
  (`pos_of_mem_spinorNormGroup`);
* 101:8 (`spinorNormGroup_eq_posAtAnisoReal`): for $n \ge 3$, $D$ is exactly the set of $\alpha \in F^\times$
  positive at all real places where $V_w$ is anisotropic. *Proof:* a variant of `exists_evalIn_eq_mul`
  (`exists_evalIn_eq_mul_of_isSquare`): $Q \perp \langle -a\rangle Q$ of rank $2n \ge 6$ is isotropic at every
  finite place, and at an infinite place $w$ it is isotropic when $V_w$ is, and also when $a$ is a square in $F_w$
  (e.g. $a > 0$ at a real place); Hasse–Minkowski gives $x, y$ with $Q(x) = a\,Q(y)$, $Q(y) \ne 0$, and
  $\theta(\tau_x\tau_y) = a\,F^{\times 2}$. This replaces the book's two-case argument ($n \ge 4$ via 66:3, $n = 3$ via
  63:17 and weak approximation) by one uniform argument for all $n \ge 3$;
* 101.r41 (`spinorNormEquiv`, `nonempty_spinorNormEquiv_posAtAnisoReal`): $O^+(V)/O'(V) \cong D/F^{\times 2}$, and for
  $n \ge 3$ this is (positive-at-anisotropic-real-places)$/F^{\times 2}$;
* 101:13 (`index_spinorNormGroup_ne_zero`, `relIndex_principalSpinorIdeles`,
  `exists_finite_spots_idele_eq_mul`, `exists_finite_spots_sup_eq_top`): for $n \ge 3$, $(F^\times : D) < \infty$, $(P_F : P_D) < \infty$, and there is
  a finite set $T$ of finite spots with $J_F = P_DJ_F^S$ for every set $S$ of finite spots disjoint from $T$.

**Defines**
* `posAtAnisoReal Q` the subgroup of $F^\times$ of elements positive at all real places where $V_w$ is anisotropic;
* `principalSpinorIdeles Q hQ` $= P_D$ (101.r52), the image of $D$ under the principal-idèle embedding.

*Conventions.* "$\alpha$ is positive at the real place $w$" is `0 < InfinitePlace.embedding_of_isReal hw α`.
For 101.r32 the group $O(V)_\mathfrak p$ is the image of $O(V)$ in $\mathrm{GL}_n(F_\mathfrak p)$, the others are
images under `orthMap` (inside `orthGroup Q (v.adicCompletion F)`).
-/
import QuadFormsKB.Literature.OMeara.Sec101B
import QuadFormsKB.Literature.OMeara.Sec101D
import QuadFormsKB.Literature.OMeara.Sec33D
import QuadFormsKB.Lattices.SpinorGlobal

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### 101.r29: localization of linear maps -/

section Localization

variable (v : HeightOneSpectrum (𝓞 F))

/-- **Localization of linear maps** (O'Meara 1973, §101B, p. 289): $\sigma \mapsto \sigma_\mathfrak p$, in the
basis $x_0, \dots, x_{n-1}$ of $V = F^n$ the entrywise map $M_n(F) \to M_n(F_\mathfrak p)$ of a number field $F$
into its completion at the finite spot $\mathfrak p$, is an injective ring homomorphism
(`RingHom.mapMatrix`) with $\det\sigma_\mathfrak p = \det\sigma$ (the image of $\det\sigma$ in $F_\mathfrak p$) and
$(a\sigma)_\mathfrak p = a\,\sigma_\mathfrak p$ for $a \in F$. -/
@[kb "omeara1963" "§101B, p. 289 (localization of linear maps: injective ring homomorphism, det σ_𝔭 = det σ)"]
theorem localizeMat_spec :
    Function.Injective (RingHom.mapMatrix (algebraMap F (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) (v.adicCompletion F)) ∧
    (∀ σ : Matrix (Fin n) (Fin n) F,
      (RingHom.mapMatrix (algebraMap F (v.adicCompletion F)) σ).det = algebraMap F (v.adicCompletion F) σ.det) ∧
    (∀ (a : F) (σ : Matrix (Fin n) (Fin n) F),
      RingHom.mapMatrix (algebraMap F (v.adicCompletion F)) (a • σ) =
        algebraMap F (v.adicCompletion F) a • RingHom.mapMatrix (algebraMap F (v.adicCompletion F)) σ) :=
  ⟨fun _ _ h => Matrix.map_injective (algebraMap F (v.adicCompletion F)).injective h,
    fun σ => (RingHom.map_det _ σ).symm,
    fun a σ => by ext i j; simp⟩

end Localization

/-! ### 101.r32: the groups $O$, $O^+$, $\Omega$, $O'$ localize into their local analogues -/

section LocalGroups

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

/-- **$O(V)_\mathfrak p \subseteq O(V_\mathfrak p)$** (O'Meara 1973, §101B, p. 290): the image of $O(V)$ in
$\mathrm{GL}_n(F_\mathfrak p)$ lies in $O(V_\mathfrak p)$ (`orthMap` has codomain `orthGroup Q (v.adicCompletion F)`). -/
@[kb "omeara1963" "§101B, p. 290 (O(V)_𝔭 ⊆ O(V_𝔭))"]
theorem orthGroup_map_le :
    (orthGroup Q F).map (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))) ≤
      orthGroup Q (v.adicCompletion F) := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact (orthMap Q (v.adicCompletion F) ⟨γ, hγ⟩).2

/-- **$O^+(V)_\mathfrak p \subseteq O^+(V_\mathfrak p)$** (O'Meara 1973, §101B, p. 290): the localization of a
rotation of $V$ is a rotation of $V_\mathfrak p$ ($\det\sigma_\mathfrak p = \det\sigma = 1$). -/
@[kb "omeara1963" "§101B, p. 290 (O⁺(V)_𝔭 ⊆ O⁺(V_𝔭))"]
theorem soSub_map_le :
    (Tamagawa.soSub Q F).map (orthMap Q (v.adicCompletion F)) ≤ Tamagawa.soSub Q (v.adicCompletion F) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [Tamagawa.mem_soSub]
  rw [orthMap_val]
  have h1 : (γ : GL (Fin n) F).val.det = 1 := hγ
  have : ((γ : GL (Fin n) F).val).map (algebraMap F (v.adicCompletion F)) =
      RingHom.mapMatrix (algebraMap F (v.adicCompletion F)) (γ : GL (Fin n) F).val := rfl
  rw [this, ← RingHom.map_det, h1, map_one]

/-- **$\Omega(V)_\mathfrak p \subseteq \Omega(V_\mathfrak p)$** (O'Meara 1973, §101B, p. 290), $\Omega$ the
commutator subgroup of $O(V)$: a homomorphism maps commutator subgroups into commutator subgroups. -/
@[kb "omeara1963" "§101B, p. 290 (Ω(V)_𝔭 ⊆ Ω(V_𝔭))"]
theorem commutator_map_le :
    (commutator (orthGroup Q F)).map (orthMap Q (v.adicCompletion F)) ≤
      commutator (orthGroup Q (v.adicCompletion F)) := by
  rw [commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

/-- **$O'(V)_\mathfrak p \subseteq O'(V_\mathfrak p)$** (O'Meara 1973, §101B, p. 290): the localization of the
spinor kernel lies in the local spinor kernel (a spinor word stays a spinor word). -/
@[kb "omeara1963" "§101B, p. 290 (O'(V)_𝔭 ⊆ O'(V_𝔭))"]
theorem spinorKernel_map_le :
    (spinorKernel Q F).map (orthMap Q (v.adicCompletion F)) ≤ spinorKernel Q (v.adicCompletion F) := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact orthMap_mem_spinorKernel Q v hγ

/-! ### 101.r33: the lattice groups $O(L)$, $O^+(L)$ -/

/-- **$O(L)_\mathfrak p \subseteq O(L_\mathfrak p)$** (O'Meara 1973, §101B, p. 290; stated for the lattice $L$ in
the sense of `Lat F n` and one finite spot $\mathfrak p$, which is the case $S = \{\mathfrak p\}$ of 101:6): the
localization of an isometry of $V$ carrying $L$ onto $L$ carries $L_\mathfrak p$ onto $L_\mathfrak p$, because
$(\sigma L)_\mathfrak p = \sigma_\mathfrak p L_\mathfrak p$ (`loc_glImage`). -/
@[kb "omeara1963" "§101B, p. 290 (O(L)_𝔭 ⊆ O(L_𝔭))"]
theorem autLat_map_le (L : Lat F n) :
    (autLat Q L.1).map (orthMap Q (v.adicCompletion F)) ≤ locStabV Q v L := by
  rintro _ ⟨γ, hγ, rfl⟩
  have h := loc_glImage v (γ : GL (Fin n) F) L.1
  rw [(mem_autLat Q).mp hγ] at h
  exact h.symm

/-- **$O^+(L)_\mathfrak p \subseteq O^+(L_\mathfrak p)$** (O'Meara 1973, §101B, p. 290): as `autLat_map_le`,
intersected with the rotations (`soSub_map_le`). -/
@[kb "omeara1963" "§101B, p. 290 (O⁺(L)_𝔭 ⊆ O⁺(L_𝔭))"]
theorem autLat_inf_soSub_map_le (L : Lat F n) :
    (autLat Q L.1 ⊓ Tamagawa.soSub Q F).map (orthMap Q (v.adicCompletion F)) ≤
      locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F) := by
  refine le_inf ?_ ?_
  · exact (Subgroup.map_mono inf_le_left).trans (autLat_map_le Q v L)
  · exact (Subgroup.map_mono inf_le_right).trans (soSub_map_le Q v)

end LocalGroups

/-! ### Real places and the group $P$ of elements positive at the anisotropic real places -/

section Real

variable (Q : QuadForm F n)

/-- **The elements of $F^\times$ positive at all real places at which $V_w$ is anisotropic** (the right-hand side of
O'Meara 1973, 101:8, p. 291). "$\alpha$ is positive at the real place $w$" is
`0 < InfinitePlace.embedding_of_isReal hw α`. A subgroup of $F^\times$ containing $F^{\times 2}$; for the form $Q$ (the
space $V$) the anisotropy of $V_w$ is `¬ Q.IsotropicIn w.Completion`. -/
@[kb "omeara1963" "§101B, 101:8, p. 291 (the set of elements positive at the real spots where V_𝔭 is anisotropic)"]
def posAtAnisoReal : Subgroup Fˣ where
  carrier := {α | ∀ (w : InfinitePlace F) (hw : w.IsReal), ¬ Q.IsotropicIn w.Completion →
    0 < InfinitePlace.embedding_of_isReal hw (α : F)}
  mul_mem' {a b} ha hb w hw hi := by
    have := mul_pos (ha w hw hi) (hb w hw hi)
    simpa [map_mul] using this
  one_mem' w hw hi := by simp
  inv_mem' {a} ha w hw hi := by
    have := inv_pos.mpr (ha w hw hi)
    simpa [map_inv₀] using this

theorem mem_posAtAnisoReal {α : Fˣ} :
    α ∈ posAtAnisoReal Q ↔ ∀ (w : InfinitePlace F) (hw : w.IsReal), ¬ Q.IsotropicIn w.Completion →
      0 < InfinitePlace.embedding_of_isReal hw (α : F) := Iff.rfl

/-- The identification of the completion at a real place with $\mathbb R$ commutes with $F \to F_w$. -/
theorem ringEquivReal_algebraMap (w : InfinitePlace F) (hw : w.IsReal) (a : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion a) =
      InfinitePlace.embedding_of_isReal hw a := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw (WithAbs.toAbs w.1 a)

/-- For a real place $w$, $a \in F$ is a square in $F_w \cong \mathbb R$ iff its real embedding is $\ge 0$. -/
theorem isSquare_algebraMap_real_iff (w : InfinitePlace F) (hw : w.IsReal) (a : F) :
    IsSquare (algebraMap F w.Completion a) ↔ 0 ≤ InfinitePlace.embedding_of_isReal hw a := by
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [← ringEquivReal_algebraMap w hw a]
  constructor
  · rintro ⟨r, hr⟩
    rw [hr, map_mul]
    exact mul_self_nonneg _
  · intro h
    refine ⟨ψ.symm (Real.sqrt (ψ (algebraMap F w.Completion a))), ψ.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt h]

/-- At a complex place every element of the completion is a square. -/
theorem isSquare_completion_of_isComplex (w : InfinitePlace F) (hw : w.IsComplex) (x : w.Completion) :
    IsSquare x := by
  let ψ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (ψ x)
  exact ⟨ψ.symm z, ψ.injective (by rw [hz, map_mul, RingEquiv.apply_symm_apply])⟩

/-- An element positive at the anisotropic real places is a square in $F_w$ at every place $w$ with $V_w$
anisotropic (real: positive; complex: always). -/
theorem isSquare_of_mem_posAtAnisoReal {α : Fˣ} (hα : α ∈ posAtAnisoReal Q) (w : InfinitePlace F)
    (hw : ¬ Q.IsotropicIn w.Completion) : IsSquare (algebraMap F w.Completion (α : F)) := by
  by_cases hr : w.IsReal
  · exact (isSquare_algebraMap_real_iff w hr _).mpr (hα w hr hw).le
  · exact isSquare_completion_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.mp hr) _

/-- A product of an even number of values $Q(z_i)$ is a square, provided that every product of two nonzero values
is a square. -/
theorem isSquare_valProd_of_even (K : Type*) [Field K] [Algebra F K] [CharZero K]
    (hK : ∀ x y : Fin n → K, Q.evalIn K x ≠ 0 → Q.evalIn K y ≠ 0 → IsSquare (Q.evalIn K x * Q.evalIn K y)) :
    ∀ zs : List (Fin n → K), (∀ z ∈ zs, Q.evalIn K z ≠ 0) → Even zs.length → IsSquare (valProd Q K zs)
  | [], _, _ => ⟨1, by simp [valProd]⟩
  | [_], _, h => absurd h (by simp)
  | z :: z' :: rest, hz, h => by
    have e : valProd Q K (z :: z' :: rest) = (Q.evalIn K z * Q.evalIn K z') * valProd Q K rest := by
      simp [valProd, mul_assoc]
    rw [e]
    refine (hK z z' (hz z (by simp)) (hz z' (by simp))).mul
      (isSquare_valProd_of_even K hK rest (fun w hw => hz w (by simp [hw])) ?_)
    have h' : Even (rest.length + 2) := h
    exact (Nat.even_add.mp h').mpr even_two

theorem valProd_map_algebraMap (K : Type*) [Field K] [Algebra F K] [CharZero K] (xs : List (Fin n → F)) :
    valProd Q K (xs.map fun x i => algebraMap F K (x i)) = algebraMap F K (valProd Q F xs) := by
  rw [valProd, valProd, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => by simpa using evalIn_map_tower Q K (K := F) x

/-- **101.r34: the elements of $D$ are positive at the real places where $V$ is anisotropic** (O'Meara 1973, §101B,
p. 291, first paragraph of the proof of 101:8). Let $Q$ be nondegenerate, $\alpha \in D = \theta(O^+(V))$ and $w$ a
real place with $V_w$ anisotropic (`¬ Q.IsotropicIn w.Completion`). Then $\alpha > 0$ at $w$
(`0 < InfinitePlace.embedding_of_isReal hw α`). Proof: $\alpha F^{\times 2} = \theta(\tau_{y_0}\cdots\tau_{y_{r-1}})$
with $r$ even; an anisotropic $V_w$ is definite, so $Q(y_i)Q(y_j)$ is a square in $F_w$ for all $i, j$
(`isotropicIn_or_isSquare_mul`), hence the product of the $Q(y_i)$ ($r$ even) is a square in $F_w$, and so is
$\alpha$. -/
@[kb "omeara1963" "§101B, 101:8, p. 291 (first paragraph of the proof: θ(O⁺(V)) is positive at anisotropic real spots)"]
theorem pos_of_mem_spinorNormGroup (hQ : Q.Nondegenerate) {α : Fˣ} (hα : α ∈ spinorNormGroup Q hQ)
    (w : InfinitePlace F) (hw : w.IsReal) (hiso : ¬ Q.IsotropicIn w.Completion) :
    0 < InfinitePlace.embedding_of_isReal hw (α : F) := by
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨σ, hσ, hθ⟩ := (mem_spinorNormGroup Q hQ).mp hα
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ σ
  have hev := even_length_of_symmProd_mem_soSub Q hxs hσ
  rw [spinorNorm_symmProd Q F hQ xs hxs] at hθ
  have hP : valProd Q F xs ≠ 0 := valProd_ne_zero Q F hxs
  have hsq : IsSquare (valProd Q F xs * (α : F)) := by
    rw [← sqClassOf_eq_one_iff (mul_ne_zero hP α.ne_zero), sqClassOf_mul hP α.ne_zero, hθ,
      sqClassOf_of_ne_zero α.ne_zero]
    simpa using SqClass.mul_self (SqClass.mk α)
  have hys : ∀ y ∈ xs.map (fun x i => algebraMap F w.Completion (x i)), Q.evalIn w.Completion y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [show Q.evalIn w.Completion (fun i => algebraMap F w.Completion (x i)) =
      algebraMap F w.Completion (Q.evalIn F x) by simpa using evalIn_map_tower Q w.Completion (K := F) x]
    exact (map_ne_zero _).mpr (hxs x hx)
  have hK := (isotropicIn_or_isSquare_mul Q w).resolve_left hiso
  have hPK : IsSquare (valProd Q w.Completion (xs.map fun x i => algebraMap F w.Completion (x i))) :=
    isSquare_valProd_of_even Q w.Completion hK _ hys (by simpa using hev)
  rw [valProd_map_algebraMap] at hPK
  have hPK0 : algebraMap F w.Completion (valProd Q F xs) ≠ 0 := (map_ne_zero _).mpr hP
  have hαK : IsSquare (algebraMap F w.Completion (α : F)) := by
    have h2 := hsq.map (algebraMap F w.Completion)
    rw [map_mul] at h2
    rw [← mul_div_cancel_left₀ (algebraMap F w.Completion (α : F)) hPK0]
    exact h2.div hPK
  have h0 := (isSquare_algebraMap_real_iff w hw _).mp hαK
  exact lt_of_le_of_ne h0 (Ne.symm ((map_ne_zero _).mpr α.ne_zero))

end Real

/-! ### 101:8 -/

section Global8

/-- **Global values with a real-place sign condition** (a variant of `exists_evalIn_eq_mul`, and the engine of
101:8): let $Q$ be nondegenerate in $n \ge 3$ variables and $a \in F^\times$ such that at every infinite place $w$,
either $Q$ is isotropic over $F_w$ or $a$ is a square in $F_w$ (for a real place: $a > 0$; for a complex place this is
automatic). Then there are $x, y \in F^n$ with $Q(y) \ne 0$ and $Q(x) = a\,Q(y)$.
*Proof* (as for `exists_evalIn_eq_mul`): $\langle b\rangle \perp \langle -ab\rangle$ has rank $2n \ge 6$, so is
isotropic at every finite place, and at an infinite place $w$ it is isotropic either because $Q$ is, or, when
$a = s^2$ in $F_w$, at $(s e_0, e_0)$; Hasse–Minkowski applies. -/
@[kb "omeara1963" "§101B, 101:8, p. 291 (and its proof)"]
theorem exists_evalIn_eq_mul_of_isSquare (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {a : F}
    (ha : a ≠ 0)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion ∨ IsSquare (algebraMap F w.Completion a)) :
    ∃ x y : Fin n → F, Q.evalIn F y ≠ 0 ∧ Q.evalIn F x = a * Q.evalIn F y := by
  obtain ⟨b, hb, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  obtain ⟨P, hPu, hP⟩ := hiso
  have hPF : ∀ x : Fin n → F, Q.evalIn F (P *ᵥ x) = ∑ i, b i * x i ^ 2 := fun x => by
    rw [hP, QuadForm.evalIn_diag]; simp
  set c : Fin (n + n) → F := Fin.append b fun i => -a * b i with hcdef
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [c, Fin.append_left]; exact hb j
    · simp only [c, Fin.append_right]; exact mul_ne_zero (neg_ne_zero.mpr ha) (hb j)
  have hD : (QuadForm.diag c).IsotropicIn F := by
    rw [hasseMinkowski_nf _ (QuadForm.nondegenerate_diag hc)]
    intro w
    cases w with
    | infinite w =>
      rcases hinf w with hQw | ⟨s, hs⟩
      · obtain ⟨y, hy0, hy⟩ := (FieldGen.isotropicIn_iff_of_isometricIn _
          (FieldGen.isometricIn_of_base _ ⟨P, hPu, hP⟩)).mp hQw
        refine ⟨Fin.append y 0, fun h => hy0 (funext fun i => ?_), ?_⟩
        · simpa [Fin.append_left] using congrFun h (Fin.castAdd n i)
        · rw [evalIn_diag_append]
          simp only [Fin.append_left, Fin.append_right]
          rw [hy, zero_add, QuadForm.evalIn_diag]
          simp
      · have hn0 : 0 < n := by omega
        set i0 : Fin n := ⟨0, hn0⟩ with hi0
        refine ⟨Fin.append (Pi.single i0 s) (Pi.single i0 1), fun h => ?_, ?_⟩
        · have := congrFun h (Fin.natAdd n i0)
          rw [Fin.append_right] at this
          simp at this
        · rw [evalIn_diag_append]
          simp only [Fin.append_left, Fin.append_right, QuadForm.evalIn_diag]
          simp [Pi.single_apply, map_mul, map_neg, hs]
          ring
    | finite v => exact isotropicIn_diag_finite (by omega) c hc v
  obtain ⟨z, hz0, hz⟩ := hD
  set x' : Fin n → F := fun i => z (Fin.castAdd n i)
  set y' : Fin n → F := fun i => z (Fin.natAdd n i)
  have hxy : Q.evalIn F (P *ᵥ x') = a * Q.evalIn F (P *ᵥ y') := by
    rw [evalIn_diag_append, QuadForm.evalIn_diag, QuadForm.evalIn_diag] at hz
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hz
    rw [hPF, hPF, Finset.mul_sum]
    have : ∑ i, -a * b i * y' i ^ 2 = -∑ i, a * (b i * y' i ^ 2) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this] at hz
    linear_combination hz
  by_cases hy : Q.evalIn F (P *ᵥ y') = 0
  · -- `Q` is isotropic, hence universal
    have hxz : Q.evalIn F (P *ᵥ x') = 0 := by rw [hxy, hy, mul_zero]
    have hiso : (QuadForm.diag b).IsotropicIn F := by
      by_cases hx0 : x' = 0
      · refine ⟨y', fun h => hz0 (funext fun i => ?_), ?_⟩
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · exact congrFun hx0 j
          · exact congrFun h j
        · rw [← hP]; exact hy
      · exact ⟨x', hx0, by rw [← hP]; exact hxz⟩
    have hn0 : 0 < n := by omega
    obtain ⟨x'', hx''⟩ := PadicClass.representsIn_of_isotropic hb hiso (a * b ⟨0, hn0⟩)
    refine ⟨P *ᵥ x'', P *ᵥ Pi.single ⟨0, hn0⟩ 1, ?_, ?_⟩
    · rw [hPF]; simp [Pi.single_apply, hb]
    · rw [hP, hx'', hPF]; simp [Pi.single_apply]
  · exact ⟨P *ᵥ x', P *ᵥ y', hy, hxy⟩

variable (Q : QuadForm F n)

/-- **101:8** (O'Meara 1973, §101B, p. 291). Let $V = F^n$ be a regular quadratic space over the number field $F$
with $n \ge 3$ (`hn`, `hQ`). Then $D = \theta(O^+(V))$ consists exactly of the elements of $F^\times$ which are
positive at all real places $w$ at which $V_w$ is anisotropic (`posAtAnisoReal`). The inclusion $\subseteq$ is
`pos_of_mem_spinorNormGroup`. For $\supseteq$, `exists_evalIn_eq_mul_of_isSquare` gives anisotropic $x, y$ with
$Q(x) = \alpha Q(y)$, and $\theta(\tau_x\tau_y) = \alpha Q(y)^2 F^{\times 2} = \alpha F^{\times 2}$.
*Deviation in the proof:* one uniform argument (Hasse–Minkowski for $Q \perp \langle -\alpha\rangle Q$) for all
$n \ge 3$, instead of the book's separate cases $n \ge 4$ (66:3) and $n = 3$ (63:17 and weak approximation). The
statement is the book's, for number fields (the function-field case 101:8a is not formalized). -/
@[kb "omeara1963" "§101B, 101:8, p. 291"]
theorem spinorNormGroup_eq_posAtAnisoReal (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    spinorNormGroup Q hQ = posAtAnisoReal Q := by
  apply le_antisymm
  · exact fun α hα w hw hi => pos_of_mem_spinorNormGroup Q hQ hα w hw hi
  · intro α hα
    obtain ⟨x, y, hy, hxy⟩ := exists_evalIn_eq_mul_of_isSquare Q hQ hn α.ne_zero (fun w => by
      by_cases hi : Q.IsotropicIn w.Completion
      · exact Or.inl hi
      · exact Or.inr (isSquare_of_mem_posAtAnisoReal Q hα w hi))
    have hx0 : Q.evalIn F x ≠ 0 := by rw [hxy]; exact mul_ne_zero α.ne_zero hy
    rw [mem_spinorNormGroup]
    refine ⟨symm Q F x * symm Q F y, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q F hx0, symm_det Q F hy]
      norm_num
    · have := spinorNorm_symmProd Q F hQ [x, y]
        (by intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
            rcases hz with rfl | rfl <;> assumption)
      simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at this
      have hyy : Q.evalIn F y * Q.evalIn F y ≠ 0 := mul_ne_zero hy hy
      rw [this, hxy, mul_assoc, sqClassOf_mul α.ne_zero hyy, (sqClassOf_eq_one_iff hyy).mpr ⟨_, rfl⟩,
        mul_one, sqClassOf_of_ne_zero α.ne_zero]
      exact congrArg SqClass.mk (Units.ext rfl)

end Global8

/-! ### 101.r41: $O^+(V)/O'(V) \cong D/F^{\times 2}$ -/

section QuotientIso

variable (Q : QuadForm F n)

/-- $O'(V)$ is normal in $O(V)$ (`spinorKernel_normal`), registered as an instance for the quotients below. -/
instance instNormalSpinorKernel : (spinorKernel Q F).Normal := spinorKernel_normal Q F

variable (hQ : Q.Nondegenerate)

/-- The kernel of $\theta$ restricted to the rotations is $O'(V)$ (inside $O^+(V)$). -/
theorem ker_spinorNormHom_restrict_soSub :
    ((spinorNormHom Q F hQ).comp (Tamagawa.soSub Q F).subtype).ker =
      (spinorKernel Q F).subgroupOf (Tamagawa.soSub Q F) := by
  ext ⟨σ, hσ⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, spinorKernel_eq_ker Q F hQ, Subgroup.mem_inf,
    MonoidHom.mem_ker, MonoidHom.mem_ker]
  have hdet : detHom Q F σ = 1 := by
    ext
    rw [detHom_val]
    exact hσ
  simp [hdet]

/-- The image of $\theta$ on the rotations is $D/F^{\times 2}$, the image of $D$ in $F^\times/F^{\times 2}$. -/
theorem range_spinorNormHom_restrict_soSub :
    ((spinorNormHom Q F hQ).comp (Tamagawa.soSub Q F).subtype).range =
      (spinorNormGroup Q hQ).map (sqClassHom F) := by
  have hsurj : Function.Surjective (sqClassHom F) := QuotientGroup.mk'_surjective _
  rw [spinorNormGroup, Subgroup.map_comap_eq_self_of_surjective hsurj]
  ext c
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

theorem range_sqClassHom_restrict :
    ((sqClassHom F).comp (spinorNormGroup Q hQ).subtype).range = (spinorNormGroup Q hQ).map (sqClassHom F) := by
  ext c
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The kernel of $D \to F^\times/F^{\times 2}$ is $F^{\times 2}$ (inside $D$). -/
theorem ker_sqClassHom_restrict :
    ((sqClassHom F).comp (spinorNormGroup Q hQ).subtype).ker =
      ((powMonoidHom 2 : Fˣ →* Fˣ).range).subgroupOf (spinorNormGroup Q hQ) := by
  ext ⟨a, ha⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change sqClassHom F a = 1 ↔ a ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range
  exact QuotientGroup.eq_one_iff (N := (powMonoidHom 2 : Fˣ →* Fˣ).range) a

/-- **101.r41: $O^+(V)/O'(V) \cong D/F^{\times 2}$** (O'Meara 1973, §101C, p. 295, the last paragraph): for the
regular space $V = F^n$ over the number field $F$, the spinor norm $\theta$ induces an isomorphism of the group of
rotations modulo the spinor kernel $O'(V)$ onto $D/F^{\times 2}$, $D = \theta(O^+(V))$ (`spinorNormGroup`),
$F^{\times 2}$ = the subgroup of squares. An abstract isomorphism, built from the first isomorphism theorem for
$\theta|_{O^+(V)}$ (kernel $O'(V)$, `spinorKernel_eq_ker`) and for $D \to F^\times/F^{\times 2}$. -/
@[kb "omeara1963" "§101C, p. 295 (O⁺(V)/O'(V) ≅ D/F²)"]
def spinorNormEquiv :
    Tamagawa.soSub Q F ⧸ (spinorKernel Q F).subgroupOf (Tamagawa.soSub Q F) ≃*
      spinorNormGroup Q hQ ⧸ ((powMonoidHom 2 : Fˣ →* Fˣ).range).subgroupOf (spinorNormGroup Q hQ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_spinorNormHom_restrict_soSub Q hQ).symm).trans <|
    (QuotientGroup.quotientKerEquivRange ((spinorNormHom Q F hQ).comp (Tamagawa.soSub Q F).subtype)).trans <|
      (MulEquiv.subgroupCongr ((range_spinorNormHom_restrict_soSub Q hQ).trans
          (range_sqClassHom_restrict Q hQ).symm)).trans <|
        (QuotientGroup.quotientKerEquivRange ((sqClassHom F).comp (spinorNormGroup Q hQ).subtype)).symm.trans <|
          QuotientGroup.quotientMulEquivOfEq (ker_sqClassHom_restrict Q hQ)

/-- **101.r41 with 101:8** (O'Meara 1973, §101C, p. 295): for $n \ge 3$ the group $O^+(V)/O'(V)$ is isomorphic to the
group of elements of $F^\times$ which are positive at all real places where $V_w$ is anisotropic, modulo $F^{\times 2}$
(`posAtAnisoReal Q`$/F^{\times 2}$). A `Nonempty` statement, from `spinorNormEquiv` and
`spinorNormGroup_eq_posAtAnisoReal`. -/
@[kb "omeara1963" "§101C, p. 295 (O⁺(V)/O'(V): positive at the real anisotropic spots, modulo squares)"]
theorem nonempty_spinorNormEquiv_posAtAnisoReal (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    Nonempty (Tamagawa.soSub Q F ⧸ (spinorKernel Q F).subgroupOf (Tamagawa.soSub Q F) ≃*
      posAtAnisoReal Q ⧸ ((powMonoidHom 2 : Fˣ →* Fˣ).range).subgroupOf (posAtAnisoReal Q)) := by
  have h := spinorNormGroup_eq_posAtAnisoReal Q hQ hn
  rw [← h]
  exact ⟨spinorNormEquiv Q hQ⟩

end QuotientIso

/-! ### 101.r52: the principal spinor idèles $P_D$ -/

section PrincipalD

open QuadFormsKB.OMeara (sIdeles ideleAt ideleAt_mul ideleAt_inv ideleAt_one)

variable (Q : QuadForm F n)

/-- **The group $P_D$ of principal idèles of the form $(\alpha)$ with $\alpha \in D$** (O'Meara 1973, §101D, p. 296;
row 101.r52): the image of $D = \theta(O^+(V))$ (`spinorNormGroup Q hQ`) under the principal-idèle embedding
$F^\times \to J_F$ (`IdeleGroup.unitEmbedding`, whose image is Mathlib's `IdeleGroup.principalSubgroup` $P_F$).
$J_F$ is the full idèle group `IdeleGroup (𝓞 F) F`. -/
@[kb "omeara1963" "§101D, p. 296 (P_D, the principal idèles (α), α ∈ D)"]
def principalSpinorIdeles (hQ : Q.Nondegenerate) : Subgroup (IdeleGroup (𝓞 F) F) :=
  (spinorNormGroup Q hQ).map (IdeleGroup.unitEmbedding (𝓞 F) F)

theorem principalSpinorIdeles_le (hQ : Q.Nondegenerate) :
    principalSpinorIdeles Q hQ ≤ IdeleGroup.principalSubgroup (𝓞 F) F :=
  fun _ ⟨a, _, h⟩ => ⟨a, h⟩

theorem unitEmbedding_injective' : Function.Injective (IdeleGroup.unitEmbedding (𝓞 F) F) :=
  fun a b h => by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    apply Units.ext
    have : algebraMap F w.Completion (a : F) = algebraMap F w.Completion (b : F) :=
      congrArg (fun i => QuadFormsKB.OMeara.ideleAtInf i w) h
    exact (algebraMap F w.Completion).injective this

end PrincipalD

/-! ### 101:13 -/

section Finite13

open QuadFormsKB.OMeara (sIdeles ideleAt ideleAt_mul ideleAt_inv ideleAt_one)

variable (Q : QuadForm F n)

/-- The signs of an element of $F^\times$ at the real places, as a homomorphism to a finite group. -/
def signsAtReal : Fˣ →* ({w : InfinitePlace F // w.IsReal} → SignTypeˣ) :=
  MonoidHom.pi fun w => (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.map (InfinitePlace.embedding_of_isReal w.2).toMonoidHom)

theorem finiteIndex_posAtAnisoReal : (posAtAnisoReal Q).FiniteIndex := by
  have : Finite (signsAtReal (F := F)).range := inferInstance
  have := Subgroup.finiteIndex_ker (signsAtReal (F := F))
  refine Subgroup.finiteIndex_of_le (H := (signsAtReal (F := F)).ker) (fun α hα w hw _ => ?_)
  have h := congrFun (MonoidHom.mem_ker.mp hα) ⟨w, hw⟩
  have h2 : SignType.sign (InfinitePlace.embedding_of_isReal hw (α : F)) = 1 := by
    have := congrArg Units.val h
    simpa [signsAtReal] using this
  exact sign_eq_one_iff.mp h2

/-- **101:13, first claim: $(F^\times : D)$ is finite** (O'Meara 1973, §101D, p. 296), for $n \ge 3$ and $Q$
nondegenerate. By 101:8, $D$ contains the elements positive at the finitely many real places where $V_w$ is
anisotropic, a subgroup of finite index (the kernel of the sign map $F^\times \to \{\pm1\}^{\text{real places}}$). -/
@[kb "omeara1963" "§101D, 101:13, p. 296 ((F^× : D) < ∞)"]
theorem index_spinorNormGroup_ne_zero (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    (spinorNormGroup Q hQ).index ≠ 0 := by
  rw [spinorNormGroup_eq_posAtAnisoReal Q hQ hn]
  have := finiteIndex_posAtAnisoReal Q
  exact Subgroup.FiniteIndex.index_ne_zero

/-- **101:13, second claim: $(P_F : P_D) = (F^\times : D) < \infty$** (O'Meara 1973, §101D, p. 296), for $n \ge 3$ and
$Q$ nondegenerate: the relative index of $P_D$ in the principal idèles $P_F$ equals $(F^\times : D)$ (the principal
embedding is injective), and is finite and nonzero. -/
@[kb "omeara1963" "§101D, 101:13, p. 296 ((P_F : P_D) < ∞)"]
theorem relIndex_principalSpinorIdeles (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    (principalSpinorIdeles Q hQ).relIndex (IdeleGroup.principalSubgroup (𝓞 F) F) =
        (spinorNormGroup Q hQ).index ∧
      (principalSpinorIdeles Q hQ).relIndex (IdeleGroup.principalSubgroup (𝓞 F) F) ≠ 0 := by
  have h : (principalSpinorIdeles Q hQ).relIndex (IdeleGroup.principalSubgroup (𝓞 F) F) =
      (spinorNormGroup Q hQ).index := by
    rw [principalSpinorIdeles, IdeleGroup.principalSubgroup, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ unitEmbedding_injective', Subgroup.relIndex_top_right]
  exact ⟨h, h ▸ index_spinorNormGroup_ne_zero Q hQ hn⟩

/-- A principal idèle $(\alpha)$ is a unit at almost all finite spots: $\lvert\alpha\rvert_\mathfrak p = 1$. -/
theorem eventually_valued_unitEmbedding (α : Fˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v) = 1 := by
  have h1 := (((IdeleGroup.unitEmbedding (𝓞 F) F α : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2).eventually
  have h2 := ((((IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2).eventually
  filter_upwards [h1, h2] with v hv1 hv2
  have ha : Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hv1
  have hb : Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹ v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hv2
  have hmul : Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v) *
      Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹ v) = 1 := by
    rw [← map_mul, ← ideleAt_mul, mul_inv_cancel, ideleAt_one, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v) * 1 := mul_le_mul' le_rfl hb
    _ = _ := mul_one _

/-- **101:13, third claim: $J_F = P_DJ_F^S$ for almost all $S$** (O'Meara 1973, §101D, p. 296), for $n \ge 3$ and $Q$
nondegenerate: there is a finite set $T$ of finite spots such that for every set $S$ of finite spots disjoint from $T$
every idèle $i \in J_F$ factors as $i = p\,j$ with $p \in P_D$ and $j \in J_F^S$ (`sIdeles S`, the idèles of absolute
value $1$ at the spots of $S$). The book's $S_2$ (a Dedekind set of almost all spots, $S \subseteq S_2$) is, as in
`exists_index_sup_sIdeles_eq_one` (33:14a), expressed as: $S$ is disjoint from the finite set $T$ of spots. *Proof* as
in the book: by 33:14a, $J_F = P_FJ_F^S$ for $S$ disjoint from a finite $T_0$; the finite index of $D$ (101:13, first
claim) gives finitely many representatives $\alpha_j$ of $F^\times/D$, each a unit at all spots outside a finite
set; then $P_F = \bigcup_j (\alpha_j)P_D$ and $(\alpha_j) \in J_F^S$ when $S$ avoids these finite sets. -/
@[kb "omeara1963" "§101D, 101:13, p. 296 (J_F = P_D J_F^S for almost all S)"]
theorem exists_finite_spots_idele_eq_mul (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Set (HeightOneSpectrum (𝓞 F)), Disjoint S (T : Set _) →
      ∀ i : IdeleGroup (𝓞 F) F, ∃ p ∈ principalSpinorIdeles Q hQ, ∃ j ∈ sIdeles S, i = p * j := by
  classical
  have hfi : (spinorNormGroup Q hQ).FiniteIndex :=
    ⟨index_spinorNormGroup_ne_zero Q hQ hn⟩
  have : Finite (Fˣ ⧸ spinorNormGroup Q hQ) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨T₀, hT₀⟩ := QuadFormsKB.OMeara.exists_index_sup_sIdeles_eq_one (F := F)
  let rep : Fˣ ⧸ spinorNormGroup Q hQ → Fˣ := Quotient.out
  have hbad : ∀ q, {v : HeightOneSpectrum (𝓞 F) |
      ¬ Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F (rep q)) v) = 1}.Finite :=
    fun q => Filter.eventually_cofinite.mp (eventually_valued_unitEmbedding (rep q))
  have hbadU := Set.finite_iUnion hbad
  refine ⟨T₀ ∪ hbadU.toFinset, fun S hS i => ?_⟩
  have hS0 : Disjoint S (T₀ : Set _) :=
    Set.disjoint_left.mpr fun v hvS hvT => Set.disjoint_left.mp hS hvS (by simp [hvT])
  have htop : IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S = ⊤ :=
    Subgroup.index_eq_one.mp (hT₀ S hS0)
  have hi : i ∈ IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S := by rw [htop]; trivial
  obtain ⟨p, ⟨α, rfl⟩, j, hj, rfl⟩ := Subgroup.mem_sup.mp hi
  -- `α = rep q * d` with `d ∈ D`
  have hd : (rep (α : Fˣ ⧸ spinorNormGroup Q hQ))⁻¹ * α ∈ spinorNormGroup Q hQ := by
    have : ((rep (α : Fˣ ⧸ spinorNormGroup Q hQ) : Fˣ) : Fˣ ⧸ spinorNormGroup Q hQ) =
        (α : Fˣ ⧸ spinorNormGroup Q hQ) := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  set r := rep (α : Fˣ ⧸ spinorNormGroup Q hQ) with hr
  have hrS : IdeleGroup.unitEmbedding (𝓞 F) F r ∈ sIdeles S := by
    intro v hv
    by_contra hne
    have hmem : v ∈ ⋃ q, {v : HeightOneSpectrum (𝓞 F) |
        ¬ Valued.v (ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F (rep q)) v) = 1} :=
      Set.mem_iUnion.mpr ⟨(α : Fˣ ⧸ spinorNormGroup Q hQ), hne⟩
    exact Set.disjoint_left.mp hS hv
      (by simp [hmem])
  refine ⟨IdeleGroup.unitEmbedding (𝓞 F) F (r⁻¹ * α), ⟨_, hd, rfl⟩,
    IdeleGroup.unitEmbedding (𝓞 F) F r * j, (sIdeles S).mul_mem hrS hj, ?_⟩
  rw [map_mul, map_inv]
  symm
  calc (IdeleGroup.unitEmbedding (𝓞 F) F r)⁻¹ * IdeleGroup.unitEmbedding (𝓞 F) F α *
        (IdeleGroup.unitEmbedding (𝓞 F) F r * j)
      = IdeleGroup.unitEmbedding (𝓞 F) F α *
        ((IdeleGroup.unitEmbedding (𝓞 F) F r)⁻¹ * (IdeleGroup.unitEmbedding (𝓞 F) F r * j)) := by
        rw [mul_comm ((IdeleGroup.unitEmbedding (𝓞 F) F r)⁻¹), mul_assoc]
    _ = IdeleGroup.unitEmbedding (𝓞 F) F α * j := by rw [inv_mul_cancel_left]

/-- **101:13, third claim, in the form $J_F = P_DJ_F^S$ of subgroups** (O'Meara 1973, §101D, p. 296): there is a finite
set $T$ of finite spots such that $P_D \sqcup J_F^S = J_F$ for every $S$ disjoint from $T$. -/
@[kb "omeara1963" "§101D, 101:13, p. 296 (J_F = P_D J_F^S for almost all S, as a join of subgroups)"]
theorem exists_finite_spots_sup_eq_top (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Set (HeightOneSpectrum (𝓞 F)), Disjoint S (T : Set _) →
      principalSpinorIdeles Q hQ ⊔ sIdeles S = ⊤ := by
  obtain ⟨T, hT⟩ := exists_finite_spots_idele_eq_mul Q hQ hn
  refine ⟨T, fun S hS => eq_top_iff.mpr fun i _ => ?_⟩
  obtain ⟨p, hp, j, hj, rfl⟩ := hT S hS i
  exact Subgroup.mul_mem_sup hp hj

end Finite13

end QuadFormsKB.Lattices
