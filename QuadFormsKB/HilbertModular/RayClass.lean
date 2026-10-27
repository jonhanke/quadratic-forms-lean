/-
# Ray classes of integral ideals modulo $\mathfrak N$ and their finiteness

$F$ totally real (only the number field structure is used), $\mathfrak N \ne 0$ an integral ideal. For the weight-2 Eisenstein series
with prescribed constant terms we group the nonzero integral ideals $\mathfrak d$ into finitely many classes such that two ideals
$\mathfrak d, \mathfrak d'$ in one class satisfy
$$\mathfrak d = \lambda\mathfrak d', \qquad (\lambda - 1)\,\mathfrak d' \subseteq \mathfrak N \qquad(\lambda \in F^\times)$$
(`exists_scale_of_rayKey_eq`). This is the narrow-free ray class relation modulo $\mathfrak N$, extended to all ideals (including those
not prime to $\mathfrak N$); its classes are those of the "ray class group with $\mathfrak N$-part" used by Hecke for Eisenstein series
of level $\mathfrak N$.

**The key** (`rayKey`). Let $\mathfrak a = \mathfrak b_{[\mathfrak d]^{-1}}$ be the fixed integral ideal of the inverse class (`compIdeal`,
the `repIdeal`), so $\mathfrak d\mathfrak a = (\alpha)$ is principal with $\alpha \in \mathcal{O}_F$ (`rayGen`). The
key of $\mathfrak d$ is
$$\kappa(\mathfrak d) = \big([\mathfrak d],\ \alpha \bmod \mathfrak N\mathfrak a_0\big) \in \mathrm{Cl}_F \times \mathcal{O}_F/\mathfrak N\mathfrak a_0,
  \qquad \mathfrak a_0 = \prod_{C\in\mathrm{Cl}_F}\mathfrak b_C\ (\texttt{repProd}),$$
a **finite** set (`finite_rayKey`: $h_F < \infty$ and $\mathcal{O}_F/\mathfrak N\mathfrak a_0$ finite). If $\kappa(\mathfrak d) = \kappa(\mathfrak d')$ then
$\lambda = \alpha/\alpha'$ works: $\lambda\mathfrak d'\mathfrak a = (\alpha) = \mathfrak d\mathfrak a$, and $(\lambda - 1)\mathfrak d'\mathfrak a = (\alpha - \alpha') \subseteq \mathfrak N\mathfrak a$
($\mathfrak a_0 \subseteq \mathfrak a$); cancel the invertible $\mathfrak a$.

Sources: Hecke, *Vorlesungen über die Theorie der algebraischen Zahlen* (1923), §48 (ideal classes in the narrow sense, ray
classes) [unverified]; Neukirch, *Algebraic Number Theory*, Ch. VI §1 (ray class groups, finiteness) [unverified].
-/
import QuadFormsKB.HilbertModular.CuspFinite

open NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Cancellation in fractional ideals -/

lemma fi_le_of_mul_le {I I' J : FI} (hJ : J ≠ 0) (h : I * J ≤ I' * J) : I ≤ I' := by
  have := mul_le_mul_left h J⁻¹
  rwa [mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_assoc, mul_inv_cancel₀ hJ, mul_one] at this

lemma coeIdeal_ne_zero' {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) : (𝔞 : FI) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

/-! ### The key of an ideal -/

/-- **The product of the class representatives** $\mathfrak a_0 = \prod_{C\in\mathrm{Cl}_F}\mathfrak b_C$ (`repIdeal`). -/
noncomputable def repProd : Ideal (𝓞 F) := ∏ C : ClassGroup (𝓞 F), repIdeal C

lemma repProd_ne_bot : (repProd : Ideal (𝓞 F)) ≠ ⊥ := by
  rw [repProd, ← Ideal.zero_eq_bot, Ne, Finset.prod_eq_zero_iff]
  rintro ⟨C, -, h⟩
  exact repIdeal_ne_bot C (by rw [h, Ideal.zero_eq_bot])

lemma repProd_le (C : ClassGroup (𝓞 F)) : (repProd : Ideal (𝓞 F)) ≤ repIdeal C :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ C))

/-- The class of an integral ideal (junk value $1$ at $0$). -/
noncomputable def idealClass (𝔡 : Ideal (𝓞 F)) : ClassGroup (𝓞 F) := by
  classical exact if h : 𝔡 ∈ (Ideal (𝓞 F))⁰ then ClassGroup.mk0 ⟨𝔡, h⟩ else 1

lemma mem_nzd {𝔡 : Ideal (𝓞 F)} (h : 𝔡 ≠ ⊥) : 𝔡 ∈ (Ideal (𝓞 F))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])

lemma idealClass_eq {𝔡 : Ideal (𝓞 F)} (h : 𝔡 ≠ ⊥) : idealClass 𝔡 = ClassGroup.mk0 ⟨𝔡, mem_nzd h⟩ := by
  classical
  rw [idealClass, dif_pos (mem_nzd h)]

/-- **The complementary ideal** $\mathfrak a = \mathfrak b_{[\mathfrak d]^{-1}}$: the fixed integral ideal of the inverse class. -/
noncomputable def compIdeal (𝔡 : Ideal (𝓞 F)) : Ideal (𝓞 F) := repIdeal (idealClass 𝔡)⁻¹

lemma compIdeal_ne_bot (𝔡 : Ideal (𝓞 F)) : compIdeal 𝔡 ≠ ⊥ := repIdeal_ne_bot _

/-- $\mathfrak d\mathfrak a$ is principal. -/
lemma exists_mul_compIdeal_eq_span {𝔡 : Ideal (𝓞 F)} (h : 𝔡 ≠ ⊥) :
    ∃ α : 𝓞 F, 𝔡 * compIdeal 𝔡 = Ideal.span {α} := by
  have hm : 𝔡 * compIdeal 𝔡 ∈ (Ideal (𝓞 F))⁰ := mem_nzd (mul_ne_zero h (compIdeal_ne_bot 𝔡))
  have h1 : ClassGroup.mk0 ⟨𝔡 * compIdeal 𝔡, hm⟩ = 1 := by
    have e : (⟨𝔡 * compIdeal 𝔡, hm⟩ : (Ideal (𝓞 F))⁰) =
        ⟨𝔡, mem_nzd h⟩ * ⟨repIdeal (idealClass 𝔡)⁻¹, repIdeal_mem _⟩ := rfl
    rw [e, map_mul, ← idealClass_eq h, mk0_repIdeal, mul_inv_cancel]
  obtain ⟨α, hα⟩ := ((ClassGroup.mk0_eq_one_iff hm).mp h1).principal
  exact ⟨α, hα⟩

/-- **The generator** $\alpha$ of $\mathfrak d\mathfrak a = (\alpha)$ (junk value $0$ at $\mathfrak d = 0$). -/
noncomputable def rayGen (𝔡 : Ideal (𝓞 F)) : 𝓞 F := by
  classical exact if h : 𝔡 ≠ ⊥ then (exists_mul_compIdeal_eq_span h).choose else 0

lemma rayGen_spec {𝔡 : Ideal (𝓞 F)} (h : 𝔡 ≠ ⊥) : 𝔡 * compIdeal 𝔡 = Ideal.span {rayGen 𝔡} := by
  classical
  rw [rayGen, dif_pos h]; exact (exists_mul_compIdeal_eq_span h).choose_spec

/-- **The ray-class key** of an integral ideal modulo $\mathfrak N$:
$\kappa(\mathfrak d) = ([\mathfrak d],\ \alpha \bmod \mathfrak N\mathfrak a_0)$ with $\mathfrak d\,\mathfrak b_{[\mathfrak d]^{-1}} = (\alpha)$ (`rayGen`) and
$\mathfrak a_0$ = `repProd`. Parameter: `𝔑` (the modulus). -/
@[kb "hecke1923" "§48, ray classes modulo 𝔑 [unverified]"]
noncomputable def rayKey (𝔑 𝔡 : Ideal (𝓞 F)) : ClassGroup (𝓞 F) × (𝓞 F ⧸ (𝔑 * repProd)) :=
  (idealClass 𝔡, Ideal.Quotient.mk _ (rayGen 𝔡))

/-- **Finitely many ray-class keys** ($\mathfrak N \ne 0$): $h_F < \infty$ and $\mathcal{O}_F/\mathfrak N\mathfrak a_0$ is finite. -/
@[kb "neukirch1999" "Ch. VI §1, finiteness of ray class groups [unverified]"]
theorem finite_rayKey {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) :
    Finite (ClassGroup (𝓞 F) × (𝓞 F ⧸ (𝔑 * repProd))) := by
  have := finite_quot_ideal (mul_ne_zero h𝔑 (repProd_ne_bot (F := F)))
  infer_instance

/-- **Ideals with the same key differ by a scalar $\equiv 1$**: if $\kappa(\mathfrak d) = \kappa(\mathfrak d')$ ($\mathfrak d, \mathfrak d' \ne 0$) then
$\mathfrak d = \lambda\mathfrak d'$ for some $\lambda \in F^\times$ with $(\lambda - 1)\mathfrak d' \subseteq \mathfrak N$. -/
@[kb "hecke1923" "§48, ideals in one ray class [unverified]"]
theorem exists_scale_of_rayKey_eq {𝔑 𝔡 𝔡' : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) (h𝔡' : 𝔡' ≠ ⊥)
    (h : rayKey 𝔑 𝔡 = rayKey 𝔑 𝔡') :
    ∃ l : F, l ≠ 0 ∧ (𝔡 : FI) = FractionalIdeal.spanSingleton (𝓞 F)⁰ l * (𝔡' : FI) ∧
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (l - 1) * (𝔡' : FI) ≤ (𝔑 : FI) := by
  have hC : idealClass 𝔡 = idealClass 𝔡' := (Prod.ext_iff.mp h).1
  have hcomp : compIdeal 𝔡 = compIdeal 𝔡' := by rw [compIdeal, compIdeal, hC]
  set 𝔞 := compIdeal 𝔡'
  have h𝔞 : (𝔞 : FI) ≠ 0 := coeIdeal_ne_zero' (compIdeal_ne_bot 𝔡')
  have e1 : 𝔡 * 𝔞 = Ideal.span {rayGen 𝔡} := by rw [← hcomp]; exact rayGen_spec h𝔡
  have e2 : 𝔡' * 𝔞 = Ideal.span {rayGen 𝔡'} := rayGen_spec h𝔡'
  have hcong : rayGen 𝔡 - rayGen 𝔡' ∈ 𝔑 * 𝔞 :=
    Ideal.mul_mono_right (repProd_le _) (Ideal.Quotient.eq.mp (Prod.ext_iff.mp h).2)
  set a := algebraMap (𝓞 F) F (rayGen 𝔡)
  set a' := algebraMap (𝓞 F) F (rayGen 𝔡')
  have ha' : a' ≠ 0 := by
    intro h0
    have : rayGen 𝔡' = 0 := algebraMap_O_injective (by rw [map_zero]; exact h0)
    rw [this, Ideal.span_singleton_eq_bot.mpr rfl] at e2
    exact mul_ne_zero h𝔡' (compIdeal_ne_bot 𝔡') e2
  have f1 : (𝔡 : FI) * 𝔞 = FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
    rw [← FractionalIdeal.coeIdeal_mul, e1, FractionalIdeal.coeIdeal_span_singleton]
  have f2 : (𝔡' : FI) * 𝔞 = FractionalIdeal.spanSingleton (𝓞 F)⁰ a' := by
    rw [← FractionalIdeal.coeIdeal_mul, e2, FractionalIdeal.coeIdeal_span_singleton]
  refine ⟨a / a', ?_, ?_, ?_⟩
  · intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have : rayGen 𝔡 = 0 := algebraMap_O_injective (by rw [map_zero]; exact h0)
      rw [this, Ideal.span_singleton_eq_bot.mpr rfl] at e1
      exact mul_ne_zero h𝔡 (compIdeal_ne_bot 𝔡') e1
    · exact ha' h0
  · refine mul_right_cancel₀ h𝔞 ?_
    rw [f1, mul_assoc, f2, ← map_mul, div_mul_cancel₀ _ ha']
  · refine fi_le_of_mul_le h𝔞 ?_
    calc FractionalIdeal.spanSingleton (𝓞 F)⁰ (a / a' - 1) * (𝔡' : FI) * 𝔞
        = FractionalIdeal.spanSingleton (𝓞 F)⁰ (a - a') := by
          rw [mul_assoc, f2, ← map_mul]; congr 1; field_simp
      _ ≤ (𝔑 : FI) * 𝔞 := by
          rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_mul]
          refine (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hcong, ?_⟩
          rw [map_sub]

end QuadFormsKB.HilbertModular
