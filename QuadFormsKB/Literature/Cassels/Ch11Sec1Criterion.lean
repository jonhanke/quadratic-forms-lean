/-
# Cassels, Chapter 11, Lemma 1.4 (iv): the spinor norm criterion for the spinor genus

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
lattices `Lat F n`; the finite adelic orthogonal group `OAf Q` acting by `latSMul`; rotations `Tamagawa.soSub`, the
spinor norm `spinorNorm`; the proper spinor genus `SameProperSpinorGenus` (Cassels' spinor genus, `Ch11Sec1.lean`).

**Proves** Cassels' Lemma 1.4 (iv) (p. 201; criterion (1.28)): for lattices $\Gamma' = \beta'\Lambda$,
$\Gamma'' = \beta''\Lambda$ of the genus of $\Lambda$ with $\beta'_p, \beta''_p \in O^+(V_p)$ (Cassels (1.8)–(1.9)),
$\Gamma'$ and $\Gamma''$ are in the same spinor genus if and only if there is $\gamma \in O^+(V)$ with
$\theta(\beta''_p)\,\theta(\beta'_p)\,\theta(\gamma) \in \theta(\Lambda_p)$ for all $p$
(`sameProperSpinorGenus_smul_iff`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec1

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

theorem soSub_iff_detHom (K : Type*) [Field K] [Algebra F K] [CharZero K] (g : orthGroup Q K) :
    g ∈ Tamagawa.soSub Q K ↔ detHom Q K g = 1 := by
  rw [Tamagawa.mem_soSub, ← Units.val_inj, detHom_val, Units.val_one]

theorem orthMap_mem_soSub (K : Type*) [Field K] [Algebra F K] [CharZero K] {γ : orthGroup Q F}
    (hγ : γ ∈ Tamagawa.soSub Q F) : orthMap Q K γ ∈ Tamagawa.soSub Q K := by
  rw [Tamagawa.mem_soSub, orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hγ, map_one]

/-- **Cassels, Lemma 1.4 (iv)** (Ch. 11, p. 201, criterion (1.28)): *if $\Gamma'_p = \beta'_p\Lambda_p$ and
$\Gamma''_p = \beta''_p\Lambda_p$ with $\beta'_p, \beta''_p \in O^+(V_p)$ for all $p$, then $S(\Gamma', \Gamma'')$
holds precisely when there exists a $\gamma \in O^+(V)$ such that $\theta(\beta''_p)\theta(\beta'_p)\theta(\gamma)
\in \theta(\Lambda_p)$ for all $p$.* Here $\beta', \beta'' \in O(V)(\mathbb A_f)$ with rotation components,
$\Gamma' = \beta'\Lambda$, $\Gamma'' = \beta''\Lambda$; the condition at $p$ is that the product of the three spinor
norms is the spinor norm of a rotation $\rho \in O^+(\Lambda_p)$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.4 (iv), p. 201 (criterion (1.28))"]
theorem sameProperSpinorGenus_smul_iff (hQ : Q.Nondegenerate) (L : Lat F n) (h' h'' : OAf Q)
    (h'rot : ∀ v, h' v ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (h''rot : ∀ v, h'' v ∈ Tamagawa.soSub Q (v.adicCompletion F)) :
    SameProperSpinorGenus Q (latSMul Q h' L) (latSMul Q h'' L) ↔
      ∃ γ ∈ Tamagawa.soSub Q F, ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ ρ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F),
          spinorNorm Q (v.adicCompletion F) ρ = spinorNorm Q (v.adicCompletion F) (h'' v) *
            spinorNorm Q (v.adicCompletion F) (h' v) *
            spinorNorm Q (v.adicCompletion F) (orthMap Q (v.adicCompletion F) γ) := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  rw [sameProperSpinorGenus_iff]
  have hθ1 : ∀ (K : Type) [Field K] [Algebra F K] [CharZero K] (g : orthGroup Q K), g ∈ spinorKernel Q K ↔
      spinorNorm Q K g = 1 ∧ g ∈ Tamagawa.soSub Q K := by
    intro K _ _ _ g
    rw [spinorKernel_eq_ker Q K hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
      spinorNormHom_apply, soSub_iff_detHom]
  constructor
  · rintro ⟨σ, hσ, k, hk, he⟩
    have hX : ((diagF Q σ * k * h')⁻¹ * h'') • L = L := by
      rw [mul_smul, inv_smul_eq_iff]
      change latSMul Q h'' L = (diagF Q σ * k * h') • L
      rw [he, mul_smul, mul_smul]; rfl
    have hX' : (diagF Q σ * k * h')⁻¹ * h'' ∈ locStab Q L := by
      rw [← stabilizer_eq_locStab, MulAction.mem_stabilizer_iff]; exact hX
    refine ⟨σ, hσ, fun v => ?_⟩
    have e : ((diagF Q σ * k * h')⁻¹ * h'') v =
        (h' v)⁻¹ * (k v)⁻¹ * (orthMap Q (v.adicCompletion F) σ)⁻¹ * h'' v := by
      simp [mul_assoc]; rfl
    have hkv := (hθ1 _ (k v)).mp (hk v)
    refine ⟨((diagF Q σ * k * h')⁻¹ * h'') v, ⟨hX' v, ?_⟩, ?_⟩
    · rw [e]
      exact (Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).mul_mem
        ((Tamagawa.soSub Q _).inv_mem (h'rot v)) ((Tamagawa.soSub Q _).inv_mem hkv.2))
        ((Tamagawa.soSub Q _).inv_mem (orthMap_mem_soSub Q _ hσ))) (h''rot v)
    · rw [e, ← spinorNormHom_apply Q _ hQ]
      simp only [map_mul, map_inv, spinorNormHom_apply, hkv.1, inv_one, mul_one, SqClass.inv_eq]
      ac_rfl
  · rintro ⟨γ, hγ, hρ⟩
    choose ρ hρ1 hρ2 using hρ
    let G : HeightOneSpectrum (𝓞 F) → Prop := fun v => h' v ∈ stdStab Q v ∧ h'' v ∈ stdStab Q v ∧
      orthMap Q (v.adicCompletion F) γ ∈ stdStab Q v ∧ loc v L.1 = std v
    have hG : ∀ᶠ v in Filter.cofinite, G v := by
      filter_upwards [h'.2, h''.2, (diagF Q γ).2, loc_eventually_std L.2] with v a b c d
      exact ⟨a, b, c, d⟩
    let δf : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) := fun v =>
      if G v then 1 else (orthMap Q (v.adicCompletion F) γ)⁻¹ * h'' v * (ρ v)⁻¹ * (h' v)⁻¹
    let δ : OAf Q := ⟨δf, by
      filter_upwards [hG] with v hv
      simp only [δf, if_pos hv]
      exact (stdStab Q v).one_mem⟩
    have hδ : δ ∈ spinorKernelAf Q := by
      intro v
      by_cases hv : G v
      · have : δ v = 1 := if_pos hv
        rw [this]; exact (spinorKernel Q _).one_mem
      · have : δ v = (orthMap Q (v.adicCompletion F) γ)⁻¹ * h'' v * (ρ v)⁻¹ * (h' v)⁻¹ := if_neg hv
        rw [this, hθ1]
        have hr := (hρ1 v).2
        refine ⟨?_, ?_⟩
        · rw [← spinorNormHom_apply Q _ hQ]
          simp only [map_mul, map_inv, spinorNormHom_apply, SqClass.inv_eq, hρ2 v]
          calc _ = (spinorNorm Q _ (orthMap Q (v.adicCompletion F) γ) *
                spinorNorm Q _ (orthMap Q (v.adicCompletion F) γ)) *
                (spinorNorm Q _ (h'' v) * spinorNorm Q _ (h'' v)) *
                (spinorNorm Q _ (h' v) * spinorNorm Q _ (h' v)) := by ac_rfl
            _ = 1 := by simp only [SqClass.mul_self, mul_one]
        · exact (Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).mul_mem
            ((Tamagawa.soSub Q _).inv_mem (orthMap_mem_soSub Q _ hγ)) (h''rot v))
            ((Tamagawa.soSub Q _).inv_mem hr)) ((Tamagawa.soSub Q _).inv_mem (h'rot v))
    obtain ⟨ρ', hρdef⟩ : ∃ ρ' : OAf Q, ρ' = (diagF Q γ * δ * h')⁻¹ * h'' := ⟨_, rfl⟩
    have hρ' : ρ' ∈ locStab Q L := by
      intro v
      have e : ρ' v = (h' v)⁻¹ * (δ v)⁻¹ * (orthMap Q (v.adicCompletion F) γ)⁻¹ * h'' v := by
        rw [hρdef]; simp [mul_assoc]; rfl
      show ρ' v ∈ locStabV Q v L
      by_cases hv : G v
      · have : δ v = 1 := if_pos hv
        rw [e, this, inv_one, mul_one]
        refine (locStabV_eq_stdStab Q v L hv.2.2.2).mpr ?_
        exact (stdStab Q v).mul_mem ((stdStab Q v).mul_mem ((stdStab Q v).inv_mem hv.1)
          ((stdStab Q v).inv_mem hv.2.2.1)) hv.2.1
      · have : δ v = (orthMap Q (v.adicCompletion F) γ)⁻¹ * h'' v * (ρ v)⁻¹ * (h' v)⁻¹ := if_neg hv
        have e2 : ρ' v = ρ v := by rw [e, this]; group
        rw [e2]; exact (hρ1 v).1
    have hid : h'' = diagF Q γ * δ * h' * ρ' := by rw [hρdef]; group
    refine ⟨γ, hγ, δ, hδ, ?_⟩
    change h'' • L = diagF Q γ • (δ • (h' • L))
    have hL' : ρ' • L = L := MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hρ')
    calc h'' • L = (diagF Q γ * δ * h' * ρ') • L := congrArg (· • L) hid
      _ = _ := by rw [mul_smul, mul_smul, mul_smul, hL']

end QuadFormsKB.Lattices
