import QuadFormsKB.Literature.OMeara.Sec43C

/-!
# O'Meara §43E: the center of the rotation group (43:13a, first part)

**Setting** (as in `Sec43E.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional regular quadratic space of
dimension $n$, $O(V)$ = `orth Q`, $O^+(V)$ = `orthPlus Q`, $\tau_u$ = `symmetry Q u hu`.

**Proves** (O'Meara 1973 printing, Chapter IV, §43E, p. 111):
* `mem_center_orthPlus_iff` (**43:13a**, first part): for $n \ge 3$, a rotation $\sigma$ commutes with every rotation
  iff $\sigma = \pm 1_V$; that is, the center of $O^+_n$ is $O^+_n \cap Z_n$ (with $Z_n = \{\pm 1_V\}$ by 43:12);
* `orthPlus_not_comm_of_three_le` (**43:12b**, second sentence): $O^+_n$ is not commutative for $n \ge 3$.

**Proof notes.** O'Meara deduces 43:13a from 43:13 (the centralizer of $\Omega_n$). Here we argue directly: for an
anisotropic $a$ and anisotropic $b \perp a$, the rotation $\rho = \tau_a\tau_b$ reverses exactly the plane
$Fa + Fb$, and $\rho\sigma = \sigma\rho$ gives $\rho(\sigma a) = -\sigma a$, so $\sigma a \in Fa + Fb$; two such planes
($b_1 \perp b_2$) meet in $Fa$. So $\sigma$ fixes every anisotropic line and 43:11 applies. The second part of 43:13a
(the center of $\Omega_n$) is not formalized.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Center

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- In a regular space of dimension $\ge 3$, two orthogonal anisotropic vectors $a, b$ have an anisotropic vector
orthogonal to both. -/
theorem exists_aniso_orth_two (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hab : bil Q a b = 0) :
    ∃ c, Q c ≠ 0 ∧ bil Q a c = 0 ∧ bil Q b c = 0 := by
  set S := Submodule.span F (Set.range ![a, b])
  set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) S
  have hmemW : ∀ w, w ∈ W ↔ bil Q a w = 0 ∧ bil Q b w = 0 := by
    intro w
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h a (Submodule.subset_span ⟨0, rfl⟩), h b (Submodule.subset_span ⟨1, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ n hn
      refine Submodule.span_induction (p := fun n _ => QuadraticMap.associated Q n w = 0) ?_ ?_ ?_ ?_ hn
      · rintro _ ⟨i, rfl⟩; fin_cases i
        · exact h1
        · exact h2
      · simp
      · intro a b _ _ ha hb; rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
  have hW : 1 ≤ finrank F W := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ S
    have h2 : finrank F S ≤ 2 := by
      have := finrank_range_le_card (R := F) (b := ![a, b])
      exact le_trans this (by simp)
    rw [h1]
    exact Nat.le_sub_of_add_le (by omega)
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    have : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  by_contra hno
  push Not at hno
  have hiso : ∀ z, bil Q a z = 0 → bil Q b z = 0 → Q z = 0 := fun z h1 h2 => by
    by_contra hz; exact hno z hz h1 h2
  apply hw0
  refine hQ.1 w fun v => ?_
  set p := v - (bil Q v a / Q a) • a - (bil Q v b / Q b) • b
  have hpa : bil Q a p = 0 := by
    simp only [p, bil_sub_right, bil_smul_right, bil_self, hab, bil_comm Q a v]; field_simp; ring
  have hpb : bil Q b p = 0 := by
    simp only [p, bil_sub_right, bil_smul_right, bil_self, bil_comm Q b a, hab, bil_comm Q b v]
    field_simp; ring
  obtain ⟨hwa, hwb⟩ := (hmemW w).1 hwW
  have hwp : bil Q w p = 0 := by
    have h := Q_add Q w p
    rw [hiso w hwa hwb, hiso p hpa hpb,
      hiso (w + p) (by rw [bil_add_right, hwa, hpa, add_zero]) (by rw [bil_add_right, hwb, hpb, add_zero])] at h
    have : (2 : F) * bil Q w p = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left iv_two_ne
  have hv : v = p + (bil Q v a / Q a) • a + (bil Q v b / Q b) • b := by simp only [p]; abel
  show bil Q w v = 0
  rw [hv, bil_add_right, bil_add_right, hwp, bil_smul_right, bil_smul_right, bil_comm Q w a, hwa,
    bil_comm Q w b, hwb]; ring

/-- If $\sigma$ commutes with $\tau_a\tau_b$ ($a \perp b$ anisotropic), then $\sigma a \in Fa + Fb$. -/
theorem mem_span_of_comm_symm_mul {σ : V ≃ₗ[F] V} {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hab : bil Q a b = 0) (hc : σ * (symmetry Q a ha * symmetry Q b hb) = symmetry Q a ha * symmetry Q b hb * σ) :
    ∃ p q : F, σ a = p • a + q • b := by
  have h1 := congrArg (fun f : V ≃ₗ[F] V => f a) hc
  have hτb : symmetry Q b hb a = a := by rw [symmetry_apply, hab]; simp
  simp only [LinearEquiv.mul_apply, hτb, iv_symmetry_self_apply, map_neg] at h1
  rw [symmetry_apply Q hb (σ a)] at h1
  refine ⟨bil Q (σ a) a / Q a, bil Q (σ a) b / Q b, ?_⟩
  have h2 : (2 : F) • σ a = (2 : F) • ((bil Q (σ a) a / Q a) • a + (bil Q (σ a) b / Q b) • b) := by
    have e : bil Q (σ a - (2 * bil Q (σ a) b / Q b) • b) a = bil Q (σ a) a := by
      rw [bil_sub_left, bil_smul_left, bil_comm Q b a, hab]; ring
    rw [symmetry_apply, e] at h1
    rw [smul_add, smul_smul, smul_smul, show 2 * (bil Q (σ a) a / Q a) = 2 * bil Q (σ a) a / Q a by ring,
      show 2 * (bil Q (σ a) b / Q b) = 2 * bil Q (σ a) b / Q b by ring]
    linear_combination (norm := module) -h1
  exact smul_right_injective V iv_two_ne h2

/-- **O'Meara 43:13a** (p. 111), first part. If $V$ is regular with $n \ge 3$, a rotation $\sigma$ commutes with every
rotation if and only if $\sigma = \pm 1_V$: the center of $O^+_n$ is $O^+_n \cap Z_n$. -/
@[kb "omeara1963" "§43E, 43:13a, p. 111 (center of O⁺ is O⁺ ∩ Z_n for n ≥ 3)"]
theorem mem_center_orthPlus_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) :
    (∀ ρ ∈ orthPlus Q, σ * ρ = ρ * σ) ↔ (∀ x, σ x = x) ∨ ∀ x, σ x = -x := by
  constructor
  · intro hc
    have hexc : ¬ IsExceptional43 Q := fun h => by have := h.1; omega
    apply eq_one_or_neg_of_forall_aniso_line Q hQ hexc hσ.1
    intro a ha
    have ha0 : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨b, hb, hab⟩ := cd_exists_perp_aniso Q (cd_reg_of_nondeg Q hQ) h3 ha0
    obtain ⟨c, hc', hac, hbc⟩ := exists_aniso_orth_two Q hQ h3 ha hb hab
    have hrot : ∀ {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0),
        symmetry Q u hu * symmetry Q w hw ∈ orthPlus Q := fun hu hw =>
      ⟨(orth Q).mul_mem (symmetry_mem_orth Q hu) (symmetry_mem_orth Q hw),
        MonoidHom.mem_ker.2 (by rw [map_mul, det_symmetry, det_symmetry]; norm_num)⟩
    obtain ⟨p, q, hpq⟩ := mem_span_of_comm_symm_mul Q ha hb hab (hc _ (hrot ha hb))
    obtain ⟨p', q', hpq'⟩ := mem_span_of_comm_symm_mul Q ha hc' hac (hc _ (hrot ha hc'))
    have hli : LinearIndependent F ![a, b, c] := by
      apply linearIndependent_of_det_gram_ne_zero (R := F) Q
      rw [Matrix.det_fin_three]
      simp [gram, hab, hac, hbc, bil_comm Q b a, bil_comm Q c a, bil_comm Q c b, ha, hb, hc']
    have key := (Fintype.linearIndependent_iff.1 hli) ![p - p', q, -q'] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (norm := module) hpq' - hpq)
    have hq : q = 0 := by simpa using key 1
    exact ⟨p, by rw [hpq, hq, zero_smul, add_zero]⟩
  · rintro (h | h) ρ _ <;> ext v <;> simp [h]

/-- **O'Meara 43:12b** (p. 110), second sentence: if $V$ is regular with $n \ge 3$ then $O^+(V)$ is not commutative.
(The scan reads "$n = 3$"; the proof gives $n \ge 3$. Proved here from 43:13a: $\tau_a\tau_b$ with $a \perp b$
anisotropic is a rotation other than $\pm 1_V$.) -/
@[kb "omeara1963" "§43E, 43:12b, p. 110 (O⁺ not commutative for n ≥ 3)"]
theorem orthPlus_not_comm_of_three_le (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank F V) :
    ¬ ∀ σ ∈ orthPlus Q, ∀ ρ ∈ orthPlus Q, σ * ρ = ρ * σ := by
  intro hcomm
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨a, ha⟩ := cd_exists_aniso Q (cd_reg_of_nondeg Q hQ)
  have ha0 : a ≠ 0 := fun h => ha (by simp [h])
  obtain ⟨b, hb, hab⟩ := cd_exists_perp_aniso Q (cd_reg_of_nondeg Q hQ) h3 ha0
  obtain ⟨c, hc, hac, hbc⟩ := exists_aniso_orth_two Q hQ h3 ha hb hab
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hρ : symmetry Q a ha * symmetry Q b hb ∈ orthPlus Q :=
    ⟨(orth Q).mul_mem (symmetry_mem_orth Q ha) (symmetry_mem_orth Q hb),
      MonoidHom.mem_ker.2 (by rw [map_mul, det_symmetry, det_symmetry]; norm_num)⟩
  have hρa : (symmetry Q a ha * symmetry Q b hb) a = -a := by
    rw [LinearEquiv.mul_apply, symmetry_apply Q hb a, hab]
    simp [iv_symmetry_self_apply]
  have hρc : (symmetry Q a ha * symmetry Q b hb) c = c := by
    rw [LinearEquiv.mul_apply, symmetry_apply Q hb c, bil_comm Q c b, hbc]
    simp only [mul_zero, zero_div, zero_smul, sub_zero]
    rw [symmetry_apply Q ha, bil_comm Q c a, hac]; simp
  have h2 : ∀ v : V, -v = v → v = 0 := fun v hv => by
    have : (2 : F) • v = 0 := by rw [two_smul]; nth_rewrite 1 [← hv]; simp
    exact (smul_eq_zero.1 this).resolve_left iv_two_ne
  rcases (mem_center_orthPlus_iff Q hQ h3 hρ).1 (fun ρ hρ' => hcomm _ hρ _ hρ') with h | h
  · exact ha0 (h2 a (by rw [← hρa, h a]))
  · exact hc0 (h2 c (by rw [← h c, hρc]))

end Sec43Center

end QuadFormsKB.OMeara
