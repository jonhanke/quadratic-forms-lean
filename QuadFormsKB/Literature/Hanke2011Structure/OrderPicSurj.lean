/-
# The Picard group of an order: $\mathrm{Pic}(R)\to\mathrm{Pic}(\mathcal O)$ is onto (Neukirch I (12.9)–(12.11))

**Setting** as in `OrderPicSetup.lean`: $\mathcal O = \mathcal O_E$, $R\subseteq\mathcal O$ a subalgebra over $\mathcal O_F$,
$\mathfrak m\ne0$ an ideal of $\mathcal O$ with $\mathfrak m\subseteq R$.

**Proves** (unconditional)
* `exists_coprime_rep`: every ideal class of $\mathcal O$ contains an integral ideal $J$ with $J+\mathfrak m = \mathcal O$;
* `mul_inter_eq`: for such $J$, a nonzero $\alpha\in J$ with $\alpha\equiv1\bmod\mathfrak m$ and $J' = \alpha J^{-1}$,
  $(J\cap R)(J'\cap R) = \alpha R$; so $J\cap R$ is an invertible ideal of $R$, and `extendedHom_inter`: $(J\cap R)\mathcal O = J$;
* `psi_surjective`: $\psi:\mathrm{Cl}(R)\to\mathrm{Cl}(\mathcal O)$, $[I]\mapsto[I\mathcal O]$, is surjective.

Source: Neukirch, *Algebraic Number Theory*, Ch. I, §12, (12.9)–(12.11), pp. 78–79 (the proof here is a direct
element computation: with $\mu = 1-\alpha\in\mathfrak m$, $\alpha = \alpha\cdot\alpha^2 + \alpha\cdot2\alpha\mu + \alpha\mu^2$).
-/
import QuadFormsKB.Literature.Hanke2011Structure.OrderPicMaps

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {R : Subalgebra (𝓞 F) (𝓞 E)} {𝔪 : Ideal (𝓞 E)}

local notation "ι" => algebraMap (𝓞 E) E

/-- **Every ideal class of $\mathcal O$ contains an integral ideal $J$ coprime to $\mathfrak m$.** -/
theorem exists_coprime_rep (hm : 𝔪 ≠ ⊥) (c : ClassGroup (𝓞 E)) :
    ∃ J : (Ideal (𝓞 E))⁰, ClassGroup.mk0 J = c ∧ (J : Ideal (𝓞 E)) ⊔ 𝔪 = ⊤ := by
  by_cases htop : 𝔪 = ⊤
  · obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c
    exact ⟨J, hJ, by simp [htop]⟩
  obtain ⟨K, hK⟩ := ClassGroup.mk0_surjective c⁻¹
  have hK0 : (K : Ideal (𝓞 E)) ≠ 0 := nonZeroDivisors.coe_ne_zero K
  have hm0 : 𝔪 ≠ 0 := hm
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx : (K : Ideal (𝓞 E)) * 𝔪 ≤ K)
    (mul_ne_zero hK0 hm0)
  have haK : a ∈ (K : Ideal (𝓞 E)) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨J, hJ⟩ : (K : Ideal (𝓞 E)) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haK)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha
    apply htop
    have : (K : Ideal (𝓞 E)) * 𝔪 = (K : Ideal (𝓞 E)) * ⊤ := by rw [Ideal.mul_top, ha]
    exact mul_left_cancel₀ hK0 this
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha0 hJ
  refine ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩, ?_, ?_⟩
  · have hKJ : (K : Ideal (𝓞 E)) * J ∈ (Ideal (𝓞 E))⁰ := hJ ▸ mem_nonZeroDivisors_of_ne_zero
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
    have h1 : ClassGroup.mk0 (⟨_, hKJ⟩ : (Ideal (𝓞 E))⁰) = 1 :=
      (ClassGroup.mk0_eq_one_iff hKJ).mpr (hJ ▸ ⟨⟨a, rfl⟩⟩)
    have h2 : (⟨_, hKJ⟩ : (Ideal (𝓞 E))⁰) = K * ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩ := rfl
    rw [h2, map_mul, hK] at h1
    exact (inv_mul_eq_one.mp h1).symm
  · have : (K : Ideal (𝓞 E)) * (𝔪 ⊔ J) = (K : Ideal (𝓞 E)) * ⊤ := by
      rw [Ideal.mul_sup, ← hJ, ha, Ideal.mul_top]
    rw [sup_comm]
    exact mul_left_cancel₀ hK0 this

variable [IsFractionRing R E]

/-- $N\cap R$, an $R$-fractional ideal, for an $\mathcal O$-fractional ideal $N$. -/
def inter (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) (N : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal R⁰ E :=
  restr h𝔪 hR N ⊓ 1

theorem mem_inter (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) (N : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    x ∈ inter h𝔪 hR N ↔ x ∈ N ∧ ∃ r : R, algebraMap R E r = x := by
  rw [inter, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_inf, Submodule.mem_inf, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_coe, (FractionalIdeal.mem_one_iff R⁰)]
  exact Iff.rfl

theorem omul_mem (N : FractionalIdeal (𝓞 E)⁰ E) (o : 𝓞 E) {x : E} (hx : x ∈ N) : ι o * x ∈ N := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem (N : Submodule (𝓞 E) E) o hx

/-- For $o\in\mathcal O$ and $\mu\in\mathfrak m$, $o\mu\in\mathfrak m\subseteq R$. -/
theorem mem_R_of_mem_m (hR : ∀ x ∈ 𝔪, x ∈ R) {o μ : 𝓞 E} (hμ : μ ∈ 𝔪) :
    ∃ r : R, algebraMap R E r = ι o * ι μ :=
  ⟨⟨o * μ, hR _ (𝔪.mul_mem_left _ hμ)⟩, by rw [algebraMap_R_E, map_mul]⟩

/-- **$(J\cap R)(J'\cap R) = \alpha R$**, where $J,J'$ are integral $\mathcal O$-fractional ideals, $JJ' = \alpha\mathcal O$,
and $\alpha\in J\cap J'$ with $\alpha - 1\in\mathfrak m$. -/
theorem mul_inter_eq (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) {J J' : FractionalIdeal (𝓞 E)⁰ E} {α : 𝓞 E}
    (hJ1 : J ≤ 1) (hJ'1 : J' ≤ 1) (hJJ' : J * J' = FractionalIdeal.spanSingleton (𝓞 E)⁰ (ι α))
    (hαJ : ι α ∈ J) (hαJ' : ι α ∈ J') (hα1 : α - 1 ∈ 𝔪) :
    inter h𝔪 hR J * inter h𝔪 hR J' = FractionalIdeal.spanSingleton R⁰ (ι α) := by
  have hμ : 1 - α ∈ 𝔪 := by rw [← neg_sub]; exact 𝔪.neg_mem hα1
  have hαR : α ∈ R := by
    have := R.sub_mem (R.one_mem) (hR _ hμ)
    simpa using this
  have hint : ∀ {N : FractionalIdeal (𝓞 E)⁰ E}, N ≤ 1 → ∀ x ∈ N, ∃ o : 𝓞 E, ι o = x := fun hN x hx =>
    (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp (hN hx)
  apply le_antisymm
  · refine FractionalIdeal.mul_le.mpr fun x hx y hy => ?_
    obtain ⟨hxJ, r1, rfl⟩ := (mem_inter h𝔪 hR J _).mp hx
    obtain ⟨hyJ, r2, rfl⟩ := (mem_inter h𝔪 hR J' _).mp hy
    have hxy : algebraMap R E r1 * algebraMap R E r2 ∈ J * J' := FractionalIdeal.mul_mem_mul hxJ hyJ
    rw [hJJ'] at hxy
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 E)⁰).mp hxy
    rw [Algebra.smul_def, algebraMap_R_E, algebraMap_R_E, ← map_mul, ← map_mul] at ho
    have ho' : o * α = (r1 : 𝓞 E) * r2 := IsFractionRing.injective (𝓞 E) E ho
    have hoR : o ∈ R := by
      have e : o = (r1 : 𝓞 E) * r2 + o * (1 - α) := by rw [← ho']; ring
      rw [e]
      exact R.add_mem (R.mul_mem r1.2 r2.2) (hR _ (𝔪.mul_mem_left _ hμ))
    refine (FractionalIdeal.mem_spanSingleton R⁰).mpr ⟨⟨o, hoR⟩, ?_⟩
    rw [Algebra.smul_def, algebraMap_R_E, algebraMap_R_E, algebraMap_R_E, ← map_mul, ← map_mul]
    exact congrArg ι ho'
  · rw [FractionalIdeal.spanSingleton_le_iff_mem]
    set a := ι α
    set μ := ι (1 - α)
    have haR : ∃ r : R, algebraMap R E r = a := ⟨⟨α, hαR⟩, rfl⟩
    have ha_in : a ∈ inter h𝔪 hR J := (mem_inter h𝔪 hR J a).mpr ⟨hαJ, haR⟩
    have h1 : a * a ∈ inter h𝔪 hR J' :=
      (mem_inter h𝔪 hR J' _).mpr ⟨omul_mem J' α hαJ', ⟨⟨α * α, R.mul_mem hαR hαR⟩, by
        show ι (α * α) = _
        rw [map_mul]⟩⟩
    have h2 : 2 * a * μ ∈ inter h𝔪 hR J' := by
      refine (mem_inter h𝔪 hR J' _).mpr ⟨?_, ⟨⟨2 * α * (1 - α), hR _ (𝔪.mul_mem_left _ hμ)⟩, ?_⟩⟩
      · have := omul_mem J' (2 * (1 - α)) hαJ'
        rw [map_mul] at this
        convert this using 1
        simp only [μ, map_ofNat]; ring
      · show ι (2 * α * (1 - α)) = _
        simp only [μ, a, map_mul, map_ofNat]
    have h3 : ∀ z ∈ J.1 * J'.1, z * (μ * μ) ∈ (inter h𝔪 hR J * inter h𝔪 hR J').1 := by
      intro z hz
      refine Submodule.mul_induction_on (C := fun z => z * (μ * μ) ∈ (inter h𝔪 hR J * inter h𝔪 hR J').1) hz
        (fun x hx y hy => ?_) (fun x y hx hy => ?_)
      · have e : x * y * (μ * μ) = (x * μ) * (y * μ) := by ring
        rw [e]
        obtain ⟨ox, rfl⟩ := hint hJ1 x hx
        obtain ⟨oy, rfl⟩ := hint hJ'1 y hy
        refine FractionalIdeal.mul_mem_mul ((mem_inter h𝔪 hR J _).mpr ⟨?_, mem_R_of_mem_m hR hμ⟩)
          ((mem_inter h𝔪 hR J' _).mpr ⟨?_, mem_R_of_mem_m hR hμ⟩)
        · rw [mul_comm]; exact omul_mem J _ hx
        · rw [mul_comm]; exact omul_mem J' _ hy
      · rw [add_mul]; exact Submodule.add_mem _ hx hy
    have ha3 : a * (μ * μ) ∈ (inter h𝔪 hR J * inter h𝔪 hR J').1 := by
      refine h3 a ?_
      have : a ∈ (J * J').1 := by
        rw [hJJ']; exact FractionalIdeal.mem_spanSingleton_self _ _
      exact (FractionalIdeal.coe_mul J J') ▸ this
    have e : a = a * (a * a) + a * (2 * a * μ) + a * (μ * μ) := by
      simp only [μ, map_sub, map_one]; ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (FractionalIdeal.mul_mem_mul ha_in h1)
      (FractionalIdeal.mul_mem_mul ha_in h2)) ha3

/-- **$(J\cap R)\mathcal O = J$** for an integral $\mathcal O$-ideal $J$ containing some $\alpha\equiv1\bmod\mathfrak m$. -/
theorem extendedHom_inter (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) {J : FractionalIdeal (𝓞 E)⁰ E} {α : 𝓞 E}
    (hJ1 : J ≤ 1) (hαJ : ι α ∈ J) (hα1 : α - 1 ∈ 𝔪) :
    FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) (inter h𝔪 hR J) = J := by
  have hμ : 1 - α ∈ 𝔪 := by rw [← neg_sub]; exact 𝔪.neg_mem hα1
  have hαR : α ∈ R := by
    have := R.sub_mem (R.one_mem) (hR _ hμ)
    simpa using this
  rw [← FractionalIdeal.coeToSubmodule_inj, coe_extendedHom]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact ((mem_inter h𝔪 hR J x).mp hx).1
  · intro x hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp (hJ1 hx)
    have e : ι o = o • ι α + (1 : 𝓞 E) • (ι o * ι (1 - α)) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_one, one_mul, ← map_mul, ← map_mul, ← map_add]
      congr 1; ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · exact (mem_inter h𝔪 hR J _).mpr ⟨hαJ, ⟨⟨α, hαR⟩, rfl⟩⟩
    · refine (mem_inter h𝔪 hR J _).mpr ⟨?_, mem_R_of_mem_m hR hμ⟩
      rw [mul_comm]; exact omul_mem J _ hx

/-- **$\mathrm{Pic}(R)\to\mathrm{Pic}(\mathcal O)$ is onto**: each class of $\mathcal O$ is $[J]$ with $J$ integral and
$J+\mathfrak m = \mathcal O$ (`exists_coprime_rep`); $J\cap R$ is invertible (`mul_inter_eq`) and $(J\cap R)\mathcal O = J$
(`extendedHom_inter`). -/
@[kb "neukirch1999" "Ch. I, (12.9)-(12.11), pp. 78-79 (Pic(R) -> Pic(O) surjective)"]
theorem psi_surjective (hm : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) : Function.Surjective (psi R) := by
  intro c
  obtain ⟨J, hJc, hJm⟩ := exists_coprime_rep hm c
  have hJ0 : (J : Ideal (𝓞 E)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have hex : ∃ α ∈ (J : Ideal (𝓞 E)), α ≠ 0 ∧ α - 1 ∈ 𝔪 := by
    have h1 : (1 : 𝓞 E) ∈ (J : Ideal (𝓞 E)) ⊔ 𝔪 := hJm ▸ Submodule.mem_top
    obtain ⟨j, hj, μ, hμ, hjμ⟩ := Submodule.mem_sup.mp h1
    by_cases hj0 : j = 0
    · have h1m : (1 : 𝓞 E) ∈ 𝔪 := by rw [hj0, zero_add] at hjμ; rw [← hjμ]; exact hμ
      obtain ⟨β, hβ, hβ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
      exact ⟨β, hβ, hβ0, ((Ideal.eq_top_iff_one _).mpr h1m).symm ▸ Submodule.mem_top⟩
    · refine ⟨j, hj, hj0, ?_⟩
      have e : j - 1 = -μ := by rw [← hjμ]; ring
      rw [e]; exact 𝔪.neg_mem hμ
  obtain ⟨α, hαJ, hα0, hα1⟩ := hex
  set JF : FractionalIdeal (𝓞 E)⁰ E := ((J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hJF
  have hJF0 : JF ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ0
  have hJF1 : JF ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hαJF : ι α ∈ JF := (FractionalIdeal.mem_coeIdeal (𝓞 E)⁰).mpr ⟨α, hαJ, rfl⟩
  set J' := FractionalIdeal.spanSingleton (𝓞 E)⁰ (ι α) * JF⁻¹ with hJ'
  have hJJ' : JF * J' = FractionalIdeal.spanSingleton (𝓞 E)⁰ (ι α) := by
    rw [hJ', mul_left_comm, mul_inv_cancel₀ hJF0, mul_one]
  have hJ'1 : J' ≤ 1 := by
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (ι α) ≤ JF :=
      (FractionalIdeal.spanSingleton_le_iff_mem).mpr hαJF
    calc J' ≤ JF * JF⁻¹ := mul_le_mul_left hle _
      _ = 1 := mul_inv_cancel₀ hJF0
  have hαJ' : ι α ∈ J' := by
    have h1inv : (1 : E) ∈ JF⁻¹ :=
      (FractionalIdeal.mem_inv_iff hJF0).mpr fun y hy => by rw [one_mul]; exact hJF1 hy
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ (ι α)) h1inv
    rwa [mul_one] at this
  have hprod := mul_inter_eq hm hR hJF1 hJ'1 hJJ' hαJF hαJ' hα1
  have hα0' : ι α ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hα0
  let IU : (FractionalIdeal R⁰ E)ˣ := Units.mkOfMulEqOne (inter hm hR JF)
    (inter hm hR J' * FractionalIdeal.spanSingleton R⁰ (ι α)⁻¹) (by
      rw [← mul_assoc, hprod, ← map_mul, mul_inv_cancel₀ hα0', map_one])
  refine ⟨ClassGroup.mk E IU, ?_⟩
  rw [psi_mk, ← hJc, ← ClassGroup.mk_mk0 E]
  congr 1
  exact Units.ext (by rw [coe_extU]; exact extendedHom_inter hm hR hJF1 hαJF hα1)

end

end QuadFormsKB.Hanke2011Structure.OrderCN

#print axioms QuadFormsKB.Hanke2011Structure.OrderCN.psi_surjective
