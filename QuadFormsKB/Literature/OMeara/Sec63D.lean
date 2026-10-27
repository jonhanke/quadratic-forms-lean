/-
# O'Meara 63:11b: the quaternion division algebra over a local field

**Setting.** $F$ is a number field, $\mathfrak p$ (`v`) a finite place, $K = F_\mathfrak p$ (`v.adicCompletion F`) with
ring of integers $\mathfrak o$ = `v.adicCompletionIntegers F` (a Henselian discrete valuation ring with finite residue
field, so the results of `Sec63A.lean` and `Sec63B.lean` apply), $\pi$ a prime element and $\Delta$ a unit of quadratic
defect $4\mathfrak o$. Quaternion algebras are Mathlib's `ℍ[K,α,β]`.

**Proves**
* `quatNormEquiv` (any field): $\left(\frac{\alpha,\beta}{K}\right) \cong \left(\frac{\alpha,\beta\,(x^2 - \alpha y^2)}{K}\right)$
  when $x^2 - \alpha y^2 \ne 0$ ($j \mapsto (x + yi)j$), and `quatSwapEquiv`:
  $\left(\frac{\alpha,\beta}{K}\right) \cong \left(\frac{\beta,\alpha}{K}\right)$;
* `quat_equiv_of_hilbertSymbol_eq` (over $K = F_\mathfrak p$): if $(\alpha, \beta)_\mathfrak p = (\alpha, \beta')_\mathfrak p$
  then $\left(\frac{\alpha,\beta}{K}\right) \cong \left(\frac{\alpha,\beta'}{K}\right)$;
* Corollary 63:11b, second part (p. 165): every quaternion division algebra over $F_\mathfrak p$ is isomorphic to
  $\left(\frac{\pi,\Delta}{K}\right)$ (`quat_division_equiv`). O'Meara argues with Hasse algebras (similarity of
  tensor products); the proof here uses only the isomorphisms above and the Hilbert symbols of 63:11a.
-/
import QuadFormsKB.Literature.OMeara.Sec63B
import QuadFormsKB.Literature.OMeara.Sec61B
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Tamagawa.QuatOrderGlobal

open NumberField IsDedekindDomain Submodule
open scoped Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section General

variable {K : Type*} [Field K]

/-- Auxiliary: basis of `ℍ[K,a,b]` with parameters `(a, 0, b * N)`, `j' = (x + y i) j`. -/
def normBasisFwd (a b x y : K) : QuaternionAlgebra.Basis ℍ[K,a,b] a 0 (b * (x ^ 2 - a * y ^ 2)) where
  i := (⟨0, 1, 0, 0⟩ : ℍ[K,a,b])
  j := (⟨0, 0, x, y⟩ : ℍ[K,a,b])
  k := (⟨0, 1, 0, 0⟩ : ℍ[K,a,b]) * ⟨0, 0, x, y⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp <;> ring
  i_mul_j := rfl
  j_mul_i := by ext <;> simp

/-- Auxiliary: basis of `ℍ[K,a,b*N]` with parameters `(a, 0, b)`, `j = (x + y i)⁻¹ j'`. -/
def normBasisInv (a b x y : K) (h : x ^ 2 - a * y ^ 2 ≠ 0) :
    QuaternionAlgebra.Basis ℍ[K,a,b * (x ^ 2 - a * y ^ 2)] a 0 b where
  i := (⟨0, 1, 0, 0⟩ : ℍ[K,a,b * (x ^ 2 - a * y ^ 2)])
  j := (⟨0, 0, x / (x ^ 2 - a * y ^ 2), -y / (x ^ 2 - a * y ^ 2)⟩ : ℍ[K,a,b * (x ^ 2 - a * y ^ 2)])
  k := (⟨0, 1, 0, 0⟩ : ℍ[K,a,b * (x ^ 2 - a * y ^ 2)]) * ⟨0, 0, x / (x ^ 2 - a * y ^ 2), -y / (x ^ 2 - a * y ^ 2)⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp; field_simp; ring
  i_mul_j := rfl
  j_mul_i := by ext <;> simp

/-- Auxiliary: basis of `ℍ[K,a,b]` with parameters `(b, 0, a)`. -/
def swapBasis (a b : K) : QuaternionAlgebra.Basis ℍ[K,a,b] b 0 a where
  i := (⟨0, 0, 1, 0⟩ : ℍ[K,a,b])
  j := (⟨0, 1, 0, 0⟩ : ℍ[K,a,b])
  k := (⟨0, 0, 1, 0⟩ : ℍ[K,a,b]) * ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j_mul_j := by ext <;> simp
  i_mul_j := rfl
  j_mul_i := by ext <;> simp

/-- **Changing $\beta$ by a norm** from $K(\sqrt\alpha)$: $\left(\frac{\alpha,\beta}{K}\right) \cong
\left(\frac{\alpha,\beta\,(x^2 - \alpha y^2)}{K}\right)$ for $x^2 - \alpha y^2 \ne 0$ (new generator $j' = (x + yi)j$,
with $j'^2 = (x^2 - \alpha y^2)\beta$ and $ij' = -j'i$). -/
def quatNormEquiv (a b : K) {x y : K} (h : x ^ 2 - a * y ^ 2 ≠ 0) :
    ℍ[K,a,b] ≃ₐ[K] ℍ[K,a,b * (x ^ 2 - a * y ^ 2)] :=
  AlgEquiv.ofAlgHom (normBasisInv a b x y h).liftHom (normBasisFwd a b x y).liftHom
    (by
      apply QuaternionAlgebra.hom_ext
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [normBasisInv, normBasisFwd, QuaternionAlgebra.Basis.liftHom_apply,
          QuaternionAlgebra.Basis.lift]
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [normBasisInv, normBasisFwd, QuaternionAlgebra.Basis.liftHom_apply,
          QuaternionAlgebra.Basis.lift] <;> field_simp <;> ring)
    (by
      apply QuaternionAlgebra.hom_ext
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [normBasisInv, normBasisFwd, QuaternionAlgebra.Basis.liftHom_apply,
          QuaternionAlgebra.Basis.lift]
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [normBasisInv, normBasisFwd, QuaternionAlgebra.Basis.liftHom_apply,
          QuaternionAlgebra.Basis.lift] <;> field_simp <;> ring)

/-- **Swapping the generators**: $\left(\frac{\alpha,\beta}{K}\right) \cong \left(\frac{\beta,\alpha}{K}\right)$
($i \mapsto j$, $j \mapsto i$, $k \mapsto -k$). -/
def quatSwapEquiv (a b : K) : ℍ[K,a,b] ≃ₐ[K] ℍ[K,b,a] :=
  AlgEquiv.ofAlgHom (swapBasis b a).liftHom (swapBasis a b).liftHom
    (by
      apply QuaternionAlgebra.hom_ext
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [swapBasis, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [swapBasis, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift])
    (by
      apply QuaternionAlgebra.hom_ext
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [swapBasis, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
      · rw [AlgHom.comp_apply, AlgHom.id_apply]
        ext <;> simp [swapBasis, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift])

/-- Auxiliary: if $(\alpha, c) = 1$ and $c \ne 0$ then $c = x^2 - \alpha y^2$. -/
lemma exists_norm_of_hilbertSymbol_eq_one (h2 : (2 : K) ≠ 0) {a c : K} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : hilbertSymbol K a c = 1) : ∃ x y : K, x ^ 2 - a * y ^ 2 = c := by
  obtain ⟨x, y, hxy⟩ := (hilbertSymbol_eq_one_iff_conic K h2 ha hc).1 h
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by rintro rfl; simp at hxy
    refine ⟨(1 + c) / 2, x * (c - 1) / 2, ?_⟩
    have : a = 1 / x ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hx)]; linear_combination hxy
    rw [this]; field_simp; ring
  · refine ⟨1 / y, x / y, ?_⟩
    field_simp
    linear_combination -hxy

end General

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Quaternion algebras with the same Hilbert symbol in the second slot** (over $F_\mathfrak p$): if
$\alpha, \beta, \beta' \ne 0$ and $(\alpha, \beta)_\mathfrak p = (\alpha, \beta')_\mathfrak p$, then
$\left(\frac{\alpha,\beta}{K}\right) \cong \left(\frac{\alpha,\beta'}{K}\right)$ ($\beta\beta'$ is a norm from
$K(\sqrt\alpha)$ by bimultiplicativity and 63:10). -/
theorem quat_equiv_of_hilbertSymbol_eq {a b b' : K} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : hilbertSymbol K a b = hilbertSymbol K a b') : Nonempty (ℍ[K,a,b] ≃ₐ[K] ℍ[K,a,b']) := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hbb : b * b' ≠ 0 := mul_ne_zero hb hb'
  have h1 : hilbertSymbol K a (b * b') = 1 := by
    rw [hK.mul_right ha hb hb', ← h]
    rcases PadicClass.hs_pm a b with h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨x, y, hxy⟩ := exists_norm_of_hilbertSymbol_eq_one h2 ha hbb h1
  have hN : x ^ 2 - a * y ^ 2 ≠ 0 := by rw [hxy]; exact hbb
  have hb2 : b ≠ 0 := hb
  refine ⟨(quatNormEquiv a b hN).trans ((quatCongr (a' := a * 1 ^ 2) (b' := b' * b ^ 2) (by ring)
    (by rw [hxy]; ring)).trans (quatScaleEquiv a b' (s := 1) (t := b) one_ne_zero hb2).symm)⟩

/-- **Corollary 63:11b, second part** (O'Meara 1963, p. 165): every quaternion division algebra over the local field
$F_\mathfrak p$ is isomorphic to $\left(\frac{\pi,\Delta}{F_\mathfrak p}\right)$, where $\pi$ is a prime element and
$\Delta$ a unit of quadratic defect $4\mathfrak o$. -/
@[kb "omeara1963" "§63B, 63:11b, p. 165 (every quaternion division algebra is isomorphic to (π, Δ))"]
theorem quat_division_equiv {π Δ : 𝔬} (hπ : Irreducible π) (hΔ : IsUnit Δ)
    (hΔd : quadDefect 𝔬 (algebraMap 𝔬 K Δ) = span 𝔬 {(4 : K)}) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ q : ℍ[K,a,b], q ≠ 0 → IsUnit q) :
    Nonempty (ℍ[K,a,b] ≃ₐ[K] ℍ[K,algebraMap 𝔬 K π,algebraMap 𝔬 K Δ]) := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h2o : (2 : 𝔬) ≠ 0 := fun h => h2 (by simpa using congrArg (algebraMap 𝔬 K) h)
  have hπ0 : algebraMap 𝔬 K π ≠ 0 := alg_pi_ne_zero hπ
  have hΔ0 : algebraMap 𝔬 K Δ ≠ 0 := alg_ne_zero_of_unit hΔ
  have hb1 : hilbertSymbol K a b = -1 :=
    (Quat.hilbertSymbol_eq_neg_one_iff_division h2 ha hb).2 hdiv
  have hex : ∃ p : 𝔬, Irreducible p ∧ hilbertSymbol K a (algebraMap 𝔬 K p) = -1 := by
    by_contra hno
    push Not at hno
    have hχ : ∀ p : 𝔬, Irreducible p → hilbertSymbol K a (algebraMap 𝔬 K p) = 1 := fun p hp =>
      (PadicClass.hs_pm a _).resolve_right (hno p hp)
    have hu : ∀ ε : 𝔬, IsUnit ε → hilbertSymbol K a (algebraMap 𝔬 K ε) = 1 := by
      intro ε hε
      have h1 := hK.mul_right ha (alg_ne_zero_of_unit hε) hπ0
      rw [← map_mul, hχ _ ((irreducible_isUnit_mul hε).2 hπ), hχ _ hπ, mul_one] at h1
      exact h1.symm
    have hpow : ∀ n : ℕ, hilbertSymbol K a (algebraMap 𝔬 K (π ^ n)) = 1 := by
      intro n
      induction n with
      | zero => simp [hilbertSymbol_one_right]
      | succ n ih =>
        have hne : algebraMap 𝔬 K (π ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero n hπ0
        rw [pow_succ, map_mul, hK.mul_right ha hne hπ0, ih, hχ π hπ]; norm_num
    have hall : ∀ x : 𝔬, x ≠ 0 → hilbertSymbol K a (algebraMap 𝔬 K x) = 1 := by
      intro x hx
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
      have hne : algebraMap 𝔬 K (π ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero n hπ0
      rw [map_mul, hK.mul_right ha (alg_ne_zero_of_unit u.isUnit) hne, hu _ u.isUnit, hpow n]
      norm_num
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝔬) b
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hyK : algebraMap 𝔬 K y ≠ 0 := (map_ne_zero_iff _ alg_inj).2 hy0
    have hxb : algebraMap 𝔬 K x = b * algebraMap 𝔬 K y := by
      rw [← hxy]; field_simp
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxb
      exact hb ((mul_eq_zero.1 hxb.symm).resolve_right hyK)
    have h1 := hK.mul_right ha hb hyK
    rw [← hxb, hall x hx0, hb1, hall y hy0] at h1
    norm_num at h1
  obtain ⟨p, hp, hap⟩ := hex
  have hp0 : algebraMap 𝔬 K p ≠ 0 := alg_pi_ne_zero hp
  have sp := hilbertSymbol_prime_delta (F := K) h2o hΔ hΔd hp
  have sπ := hilbertSymbol_prime_delta (F := K) h2o hΔ hΔd hπ
  obtain ⟨e1⟩ := quat_equiv_of_hilbertSymbol_eq v ha hb hp0 (hb1.trans hap.symm)
  obtain ⟨e3⟩ := quat_equiv_of_hilbertSymbol_eq v (a := algebraMap 𝔬 K p) hp0 ha hΔ0
    (by rw [← hilbertSymbol_comm, hap, sp])
  obtain ⟨e5⟩ := quat_equiv_of_hilbertSymbol_eq v (a := algebraMap 𝔬 K Δ) hΔ0 hp0 hπ0
    (by rw [← hilbertSymbol_comm, sp, hilbertSymbol_comm, sπ])
  exact ⟨e1.trans ((quatSwapEquiv a _).trans (e3.trans ((quatSwapEquiv _ _).trans
    (e5.trans (quatSwapEquiv _ _)))))⟩

end QuadFormsKB.OMeara
