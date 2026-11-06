/-
# O'Meara §95: special subgroups of $O_n(V)$ over a local field

**Setting.** $F$ is a number field, $\mathfrak p$ (`v`) a finite place, $K = F_\mathfrak p$ (`v.adicCompletion F`)
O'Meara's local field (1973 printing, §95, pp. 280–284; every local field of characteristic $0$ is such a completion)
with integers $\mathfrak o_\mathfrak p$ (`v.adicCompletionIntegers F`). $(V, Q)$ is a finite-dimensional quadratic
space over $K$ (Mathlib `QuadraticForm K V`), regular meaning `(QuadraticMap.associated Q).Nondegenerate`;
$n = \dim V$. $O'_n$ is `orthPrime Q` (the kernel of the spinor norm on the rotations), $\Omega_n$ is `omega Q` (the
commutator subgroup of $O_n$), $-1_V$ is `LinearEquiv.neg K`. $K$ is *non-dyadic* when $|2|_\mathfrak p = 1$
(`Valued.v (2 : K) = 1`) and *dyadic* otherwise ($|2|_\mathfrak p < 1$).

**Proves**
* **Proposition 95:1** (pp. 280–283): `omega_eq_orthPrime_local` ($O'_n = \Omega_n$ except when $V$ is an
  anisotropic quaternary space over a non-dyadic field), `relIndex_omega_orthPrime_local` ($(O'_4 : \Omega_4) = 2$ in
  the exceptional case), and both together `omega_orthPrime_local`; the dyadic quaternary anisotropic case
  is `omega_eq_orthPrime_of_dyadic`;
* **Corollary 95:1a** (p. 283): `omega_cosets_local`;
* the remarks of pp. 283–284 on $\Omega_n \cap Z_n$: `neg_mem_omega_iff_local` (outside the exceptional case
  $-1_V \in \Omega_n$ iff $n$ is even and $dV = 1$) and `neg_mem_omega_iff_exceptional` (in the exceptional case
  $-1_V \in \Omega_4$ iff $-1$ is a non-square).

The proofs follow the book: step 1 is 55:5, 55:6a and 63:19; step 2 is `S95.exists_ternary_rep` and
`S95.mem_omega_of_lift`; steps 3 and 4 are `S95.mem_omega_or_of_classes` and `S95.symProd_not_mem_omega`, applied to
$R = \mathfrak o_\mathfrak p$.
-/
import QuadFormsKB.Literature.OMeara.Sec95NonDyadic
import QuadFormsKB.Literature.OMeara.Sec95Local
import QuadFormsKB.LocalDensity.NFBridge

open QuadraticMap Module NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

namespace S95

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- $|2|_\mathfrak p \le 1$. -/
theorem valued_two_le_one : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
  rw [HN.valued_two]
  exact WithZero.exp_le_one_iff.mpr (by omega)

/-- If $|2|_\mathfrak p = 1$ then $2$ is a unit of $\mathfrak o_\mathfrak p$. -/
theorem isUnit_two_of_valued (h2 : Valued.v (2 : v.adicCompletion F) = 1) :
    IsUnit (2 : v.adicCompletionIntegers F) := by
  have h0 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  have hinv : (2 : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  refine ⟨⟨2, ⟨_, hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show (2 : v.adicCompletion F) * 2⁻¹ = 1
    exact mul_inv_cancel₀ h0
  · show (2 : v.adicCompletion F)⁻¹ * 2 = 1
    exact inv_mul_cancel₀ h0

end S95

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Invertible (2 : v.adicCompletion F)]
variable (Q : QuadraticForm (v.adicCompletion F) V)

/-- **Step 2 of the proof of 95:1** (O'Meara 1973, p. 281): for an anisotropic quaternary space over a dyadic
field, $O'_4 = \Omega_4$. A typical $\sigma \in O'_4$ is a product of at most four symmetries
$\tau_{(\alpha_1)}\cdots\tau_{(\alpha_r)}$ (43:3); a regular ternary subspace $U$ represents all $\alpha_i$, and
$O'_3(U) = \Omega_3(U)$ (55:5). -/
@[kb "omeara1963" "§95, proof of 95:1, step 2, p. 281 (O'₄ = Ω₄, anisotropic quaternary, dyadic)"]
theorem omega_eq_orthPrime_of_dyadic (h2 : Valued.v (2 : v.adicCompletion F) < 1) (hQ : Q.Anisotropic)
    (hn : finrank (v.adicCompletion F) V = 4) : omega Q = orthPrime Q := by
  have hQn := S95.nondegenerate_of_anisotropic Q hQ
  refine le_antisymm (omega_le_orthPrime Q hQn) fun σ hσ => ?_
  obtain ⟨l, hl, hσl, hlen⟩ := exists_symmetry_prod_eq_length_le Q hQn hσ.1.1
  rw [attach_prod_eq_symProd Q l hl] at hσl
  obtain ⟨U, hU3, hUn, hrep⟩ := S95.exists_ternary_rep v Q h2 hQ hn (l.map Q)
    (fun α hα => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hα; exact hl u hu)
    (by rw [List.length_map]; omega)
  exact S95.mem_omega_of_lift Q hQn hUn (omega_eq_orthPrime_of_finrank_le_three _ hUn hU3.le) hσ l hl hσl
    fun u hu => hrep _ (List.mem_map_of_mem hu)

/-- **Proposition 95:1, the general case** (O'Meara 1973, pp. 280–281): let $V$ be a regular quadratic space over a
local field. Then $O'_n = \Omega_n$, unless $V$ is an anisotropic quaternary space over a non-dyadic field. -/
@[kb "omeara1963" "§95, 95:1, pp. 280–281 (O'_n = Ω_n outside the exceptional case)"]
theorem omega_eq_orthPrime_local (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hexc : ¬ (finrank (v.adicCompletion F) V = 4 ∧ Q.Anisotropic ∧ Valued.v (2 : v.adicCompletion F) = 1)) :
    omega Q = orthPrime Q := by
  by_cases hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0
  · exact omega_eq_orthPrime_of_isotropic Q hQ hiso
  have han : Q.Anisotropic := fun x hx => by
    by_contra h0; exact hiso ⟨x, h0, hx⟩
  rcases le_or_gt (finrank (v.adicCompletion F) V) 3 with h3 | h4
  · exact omega_eq_orthPrime_of_finrank_le_three Q hQ h3
  rcases le_or_gt (finrank (v.adicCompletion F) V) 4 with h4' | h5
  · have hn : finrank (v.adicCompletion F) V = 4 := by omega
    have h2 : Valued.v (2 : v.adicCompletion F) < 1 :=
      lt_of_le_of_ne (S95.valued_two_le_one v) fun h => hexc ⟨hn, han, h⟩
    exact omega_eq_orthPrime_of_dyadic v Q h2 han hn
  · exact absurd (S95.exists_isotropic_of_five_le v Q hQ h5) hiso

/-- **Proposition 95:1, the exceptional case** (O'Meara 1973, pp. 281–283): for an anisotropic quaternary space
over a non-dyadic local field, $(O'_4 : \Omega_4) = 2$. -/
@[kb "omeara1963" "§95, 95:1, pp. 281–283 ((O'₄ : Ω₄) = 2 in the exceptional case)"]
theorem relIndex_omega_orthPrime_local (hQ : Q.Anisotropic) (hn : finrank (v.adicCompletion F) V = 4)
    (h2 : Valued.v (2 : v.adicCompletion F) = 1) : (omega Q).relIndex (orthPrime Q) = 2 :=
  S95.relIndex_omega_orthPrime_nondyadic (R := v.adicCompletionIntegers F) (S95.isUnit_two_of_valued v h2) hQ hn

/-- **Proposition 95:1** (O'Meara 1973, p. 280): let $V$ be a regular $n$-ary quadratic space over a local field.
Then $O'_n = \Omega_n$ with the following exception: $V$ is a quaternary anisotropic space over a non-dyadic field.
In the exceptional case $(O'_4 : \Omega_4) = 2$. -/
@[kb "omeara1963" "§95, 95:1, p. 280"]
theorem omega_orthPrime_local (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (¬ (finrank (v.adicCompletion F) V = 4 ∧ Q.Anisotropic ∧ Valued.v (2 : v.adicCompletion F) = 1) →
      omega Q = orthPrime Q) ∧
    (finrank (v.adicCompletion F) V = 4 ∧ Q.Anisotropic ∧ Valued.v (2 : v.adicCompletion F) = 1 →
      (omega Q).relIndex (orthPrime Q) = 2) :=
  ⟨omega_eq_orthPrime_local v Q hQ, fun ⟨hn, han, h2⟩ => relIndex_omega_orthPrime_local v Q han hn h2⟩

/-- **Corollary 95:1a** (O'Meara 1973, p. 283): in the exceptional case (anisotropic quaternary $V$, non-dyadic
field), $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}\Omega_4$ and $\Omega_4$ are the two distinct cosets
of $O'_4$ modulo $\Omega_4$, where $\Delta$ can be any non-square unit (and $\pi$ any prime element) of
$\mathfrak o_\mathfrak p$. Stated for any vectors $x, y, u, w$ with $Q(x) = 1$, $Q(y) = \Delta$, $Q(u) = \pi$,
$Q(w) = \pi\Delta$ and $\rho = \tau_x\tau_y\tau_u\tau_w$: $\rho \in O'_4 \setminus \Omega_4$, and every
$\sigma \in O'_4$ lies in $\Omega_4$ or in $\rho\Omega_4$. -/
@[kb "omeara1963" "§95, 95:1a, p. 283"]
theorem omega_cosets_local (hQ : Q.Anisotropic) (hn : finrank (v.adicCompletion F) V = 4)
    (h2 : Valued.v (2 : v.adicCompletion F) = 1) {π Δ : v.adicCompletionIntegers F} (hπ : Irreducible π)
    (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) {x y u w : V} (hx : Q x = 1) (hy : Q y = Δ) (hu : Q u = π)
    (hw : Q w = π * Δ) (h0 : ∀ z ∈ [x, y, u, w], Q z ≠ 0) :
    symProd Q [x, y, u, w] h0 ∈ orthPrime Q ∧ symProd Q [x, y, u, w] h0 ∉ omega Q ∧
      ∀ σ ∈ orthPrime Q, σ ∈ omega Q ∨ σ * (symProd Q [x, y, u, w] h0)⁻¹ ∈ omega Q := by
  have key := S95.omega_cosets_nondyadic (S95.isUnit_two_of_valued v h2) hπ hQ hn hΔ hΔs ![x, y, u, w]
    (fun i => by fin_cases i <;> simp [S95.cls, hx, hy, hu, hw]) (by simpa using h0)
  simpa using key

/-- **$\Omega_n \cap Z_n$ outside the exceptional case** (O'Meara 1973, §95, p. 283): if $V$ is not an anisotropic
quaternary space over a non-dyadic field, then $-1_V \in \Omega_n$ (i.e. $\Omega_n \cap Z_n = \{\pm 1_V\}$) if and
only if $-1_V \in O'_n$, namely $n$ is even and $dV = 1$ ($dV$ the determinant of the Gram matrix of a base $b$,
modulo squares). -/
@[kb "omeara1963" "§95, p. 283 (Ω_n ∩ Z_n = {±1_V} iff dV = 1 with n even, outside the exceptional case)"]
theorem neg_mem_omega_iff_local (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι (v.adicCompletion F) V)
    (hexc : ¬ (finrank (v.adicCompletion F) V = 4 ∧ Q.Anisotropic ∧ Valued.v (2 : v.adicCompletion F) = 1)) :
    LinearEquiv.neg (v.adicCompletion F) ∈ omega Q ↔
      Even (finrank (v.adicCompletion F) V) ∧ IsSquare (gram Q b).det := by
  rw [omega_eq_orthPrime_local v Q hQ hexc]
  exact neg_mem_orthPrime_iff Q hQ b

/-- **$\Omega_4 \cap Z_4$ in the exceptional case** (O'Meara 1973, §95, pp. 283–284): for an anisotropic quaternary
space over a non-dyadic field, $-1_V \in \Omega_4$ (i.e. $\Omega_4 \cap Z_4 = \{\pm 1_V\}$) if and only if $-1$ is a
non-square in $F_\mathfrak p$. -/
@[kb "omeara1963" "§95, pp. 283–284 (Ω₄ ∩ Z₄ = {±1_V} iff −1 is a non-square, the exceptional case)"]
theorem neg_mem_omega_iff_exceptional (hQ : Q.Anisotropic) (hn : finrank (v.adicCompletion F) V = 4)
    (h2 : Valued.v (2 : v.adicCompletion F) = 1) :
    LinearEquiv.neg (v.adicCompletion F) ∈ omega Q ↔ ¬ IsSquare (-1 : v.adicCompletion F) :=
  S95.neg_one_mem_omega_iff_nondyadic (R := v.adicCompletionIntegers F) (S95.isUnit_two_of_valued v h2) hQ hn

end QuadFormsKB.OMeara
