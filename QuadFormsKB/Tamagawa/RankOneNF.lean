/-
# Rank one over $\mathcal O_F$: the genus is one lattice, Mass $= \tfrac12$, and $\tau(SO_1)$

**Layer:** lattices $L \subseteq F^1$ over $\mathcal O_F$ (`Lattices/`: `Lat F 1`, i.e. nonzero finitely generated
$\mathcal O_F$-submodules of $F$, fractional ideals $\mathfrak a$; not necessarily principal) in the quadratic space
$(F, Q)$ with $Q(x_0) = a\,x_0^2$, $a = c_{00} \ne 0$, and the Tamagawa bookkeeping (`Tamagawa/MassFormula.lean`).

**Proves (unconditionally)**
* `mem_orthGroup_rankOne`: $O(V)(R) = \{\pm 1\}$ over every $F$-algebra $R$ that is a domain (so over $F$ and every
  $F_\mathfrak p$);
* `sameGenus_rankOne_iff`: two lattices in $(F, Q)$ are in the same genus iff they are **equal** (a local isometry
  $\pm 1$ fixes every $L_\mathfrak p$, and a lattice is determined by its localizations, `loc_injective`); likewise
  `isIsometric_rankOne_iff`;
* `genusClasses_rankOne`: the genus of $L$ is the single class $\mathrm{cls}(L) = \{L\}$, for **every** number field
  $F$, every $a \ne 0$ and every lattice $L$ (principal or not, integral or not);
* `card_autLat_rankOne`, `mass_rankOne`: $O(L) = \{\pm1\}$ and $\mathrm{Mass}(L) = \tfrac12$;
* the Tamagawa bookkeeping for $Q_0$ over $\mathcal O_F$ of rank $1$ ($L = \mathcal O_F$, $Q_0 \otimes F$ totally positive):
  `dcMass_SO_rankOne` ($SO_1$ is trivial; the $SO$-mass is $1$), `tauSO_rankOne` ($\tau(SO_1) = \mu_{\mathrm{Tam}}(K_{SO})$),
  `archVolSO_one` ($\mathrm{vol}(SO_1(\mathbb R)) = 1/(2d)$ for the gauge form $dX/dQ$), `siegelDensity_rankOne_good`
  ($\alpha_\mathfrak p(L,L) = 1$ for $\mathfrak p \nmid 2a$), `multipliable_siegelDensity_rankOne` (so, unlike
  $\prod_p\beta_p(m)$, the product $\prod_\mathfrak p\alpha_\mathfrak p(L,L)$ converges: it is a finite product), and
  `tamagawaK_rankOne` (the explicit finite form of $\mu_{\mathrm{Tam}}(K_{SO})$).

**The genus over $F$.** In the repo's (and O'Meara's §102) definition the genus of $L$ lives
in the fixed space $(F, a x^2)$, and there it is the single lattice $L$: the class number of a rank-one genus is $1$ over
every number field. The class group and units do **not** enter the class number of a genus; they enter the *set of
genera*: abstract rank-one lattices are pairs $(\mathfrak a, a)$ modulo $(\mathfrak a, a) \sim (\lambda\mathfrak a, \lambda^{-2}a)$
($\lambda \in F^\times$), and those with a fixed discriminant ideal $a\mathfrak a^2$ and a fixed space are parametrized by
$\{x \in F^\times : (x) = \mathfrak b^2\}/F^{\times 2}$, an extension of $\mathrm{Cl}_F[2]$ by $\mathcal O_F^\times/\mathcal O_F^{\times 2}$; each such
lattice is alone in its genus. So no example with more than one class exists, and the bound is $h(\mathrm{gen}) = 1$.

**$\tau(SO_1) = 1$.** $SO_1$ is the trivial group, so its Tamagawa number is $1$ (Weil 1982, §3.7 [unverified]: the
"$\tau = 2$" theorem is for $n \ge 2$). In the terms, `tauSO` $= \mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO}$ with
$\mathrm{mass}_{SO} = 1$ (`dcMass_SO_rankOne`), so $\tau(SO_1) = \mu_{\mathrm{Tam}}(K_{SO})$ = `tamagawaK`, which is
$$\prod_{\sigma}\frac{1}{2 d_\sigma}\cdot\prod_{\mathfrak p \mid 2a}\alpha_\mathfrak p(L, L), \qquad d_\sigma = |\sigma(a)|$$
(`tamagawaK_rankOne`). The value $1$ is the product formula $\prod_{\mathfrak p\mid 2a}\alpha_\mathfrak p = N(2a\mathcal O_F) = \prod_\sigma 2|\sigma(a)|$,
from $\alpha_\mathfrak p(\langle a\rangle, \langle a\rangle) = N\mathfrak p^{v_\mathfrak p(2a)}$ (half the number of square roots of $1$ modulo
$\mathfrak p^{k}$, times $N\mathfrak p^{v_\mathfrak p(a)}$). *Gap:* the bad-prime values $\alpha_\mathfrak p = N\mathfrak p^{v_\mathfrak p(2a)}$ are not formalized
here. Siegel's $\varepsilon = \tfrac12$ for $r = n$ then reads $\mathrm{Mass}(L) = \tfrac12 = \tfrac12\cdot\tau(SO_1)\cdot\mu_{\mathrm{Tam}}(K_{SO})^{-1}$,
i.e. the mass formula `massFormula` holds in rank $1$ with $\tau(SO_1) = 1$ in place of $2$ and the factor $\tfrac12$
of $[O_1 : SO_1] = 2$ uncancelled.
-/
import QuadFormsKB.Tamagawa.MassFormula

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.RankOne

open Lattices

/-! ### The orthogonal group of a rank-one space -/

section Orth

variable {F : Type*} [Field F] [NumberField F] {Q : QuadForm F 1}

theorem hessian_rankOne (Q : QuadForm F 1) : Q.hessian 0 0 = 2 * Q.coeff 0 0 := by
  simp [QuadForm.hessian]; ring

/-- **$O(V)(R) = \{\pm 1\}$ in rank one** ($Q(x_0) = a x_0^2$, $a \ne 0$), over any $F$-algebra $R$ that is a domain:
$g^{\mathsf T}(2a)g = 2a$ forces $g_{00}^2 = 1$ (cf. O'Meara §42E, p. 96, where $\pm 1_V \in O(V)$; the rank-one case is not discussed there). -/
@[kb "omeara1963" "§41A, p. 84 (orthogonal group), rank one"]
theorem mem_orthGroup_rankOne (ha : Q.coeff 0 0 ≠ 0) (R : Type*) [CommRing R] [IsDomain R] [Algebra F R]
    (g : GL (Fin 1) R) : g ∈ orthGroup Q R ↔ g = 1 ∨ g = -1 := by
  rw [mem_orthGroup]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.map_apply] at h00
    have hH : algebraMap F R (Q.hessian 0 0) ≠ 0 := by
      rw [hessian_rankOne, Ne, map_eq_zero_iff _ (algebraMap F R).injective]
      exact mul_ne_zero two_ne_zero ha
    have hsq : g.val 0 0 * g.val 0 0 = 1 := by
      have : (g.val 0 0 * g.val 0 0 - 1) * algebraMap F R (Q.hessian 0 0) = 0 := by
        linear_combination h00
      rcases mul_eq_zero.mp this with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd h1 hH
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left; ext i j; fin_cases i; fin_cases j; simpa using h1
    · right; ext i j; fin_cases i; fin_cases j; simpa using h1
  · rintro (rfl | rfl) <;> simp

/-- $-1$ fixes every $\mathfrak o_\mathfrak p$-submodule: $(-1)M = M$. -/
theorem locAct_neg_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (v.adicCompletionIntegers F)
    (Fin n → v.adicCompletion F)) : locAct v (-1) M = M := by
  ext x
  rw [mem_locAct]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Units.val_neg, neg_mulVec] using M.neg_mem hy
  · intro hx
    exact ⟨-x, M.neg_mem hx, by simp [Units.val_neg, neg_mulVec]⟩

/-- $-1$ fixes every $\mathcal O_F$-submodule: $(-1)L = L$. -/
theorem glImage_neg_one {n : ℕ} (L : Submodule (𝓞 F) (Fin n → F)) : glImage (-1 : GL (Fin n) F) L = L := by
  ext x
  rw [mem_glImage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Units.val_neg, neg_mulVec] using L.neg_mem hy
  · intro hx
    exact ⟨-x, L.neg_mem hx, by simp [Units.val_neg, neg_mulVec]⟩

/-! ### The genus is a single lattice -/

/-- **Same genus in rank one means equal** (cf. O'Meara §102A, p. 297, for the definition of the genus): for lattices $L, M$ in $(F, a x_0^2)$, $a \ne 0$,
$M \in \mathrm{gen}(L)$ iff $M = L$. *Proof:* the local isometries are $\pm 1$ (`mem_orthGroup_rankOne`), which fix
$L_\mathfrak p$; so $L_\mathfrak p = M_\mathfrak p$ for all $\mathfrak p$, and $L = M$ (`loc_injective`). -/
@[kb "omeara1963" "§102A, p. 297"]
theorem sameGenus_rankOne_iff (ha : Q.coeff 0 0 ≠ 0) (L M : Lat F 1) : SameGenus Q L.1 M.1 ↔ L = M := by
  constructor
  · intro h
    refine Subtype.ext (loc_injective L.2 M.2 fun v => ?_)
    obtain ⟨g, hg, he⟩ := h v
    rcases (mem_orthGroup_rankOne ha _ g).mp hg with rfl | rfl
    · rwa [locAct_one] at he
    · rwa [locAct_neg_one] at he
  · rintro rfl; exact SameGenus.refl Q L.1

/-- **Isometric in rank one means equal:** $O(V)(F) = \{\pm 1\}$ fixes every lattice. -/
theorem isIsometric_rankOne_iff (ha : Q.coeff 0 0 ≠ 0) (L M : Lat F 1) : IsIsometric Q L.1 M.1 ↔ L = M := by
  constructor
  · rintro ⟨γ, hγ, he⟩
    refine Subtype.ext ?_
    rcases (mem_orthGroup_rankOne ha F γ).mp hγ with rfl | rfl
    · rwa [glImage_one] at he
    · rwa [glImage_neg_one (F := F)] at he
  · rintro rfl; exact IsIsometric.refl Q L.1

/-- **The genus of a rank-one lattice is one class** (cf. O'Meara §102A, p. 297, for the definition of the genus): for every number field $F$, every
$a \ne 0$ and every lattice $L \subseteq F$ (a fractional ideal, principal or not), the set of classes in
$\mathrm{gen}(L)$ is $\{\mathrm{cls}(L)\}$; in fact $\mathrm{gen}(L) = \mathrm{cls}(L) = \{L\}$. -/
@[kb "omeara1963" "§102A, p. 298 (h(L))"]
theorem genusClasses_rankOne (ha : Q.coeff 0 0 ≠ 0) (L : Lat F 1) :
    genusClasses Q L = {Quotient.mk (latSetoid Q) L} := by
  ext c
  constructor
  · rintro ⟨M, rfl, hM⟩
    rw [(sameGenus_rankOne_iff ha L M).mp hM]; rfl
  · rintro rfl
    exact ⟨L, rfl, SameGenus.refl Q L.1⟩

/-- $|O(V)(F)| = 2$ in rank one. -/
theorem card_orthGroup_rankOne (ha : Q.coeff 0 0 ≠ 0) : Nat.card (orthGroup Q F) = 2 := by
  have hset : ((orthGroup Q F : Set (GL (Fin 1) F))) = {1, -1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact mem_orthGroup_rankOne ha F g
  have hne : (1 : GL (Fin 1) F) ≠ -1 := by
    intro h
    have := congrArg (fun g : GL (Fin 1) F => g.val 0 0) h
    simp only [Units.val_one, Units.val_neg, Matrix.one_apply_eq, Matrix.neg_apply] at this
    norm_num at this
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **$O(L) = O(V)(F) = \{\pm 1\}$ has order $2$** for every lattice $L$ in rank one. -/
@[kb "omeara1963" "§82C, p. 223 (O(L))"]
theorem card_autLat_rankOne (ha : Q.coeff 0 0 ≠ 0) (L : Submodule (𝓞 F) (Fin 1 → F)) :
    Nat.card (autLat Q L) = 2 := by
  have htop : autLat Q L = ⊤ := by
    refine eq_top_iff.mpr fun γ _ => ?_
    rw [mem_autLat]
    rcases (mem_orthGroup_rankOne ha F γ).mp γ.2 with h | h
    · rw [h, glImage_one]
    · rw [h, glImage_neg_one (F := F) L]
  rw [htop, Subgroup.card_top, card_orthGroup_rankOne ha]

/-- **The mass of a rank-one genus is $\tfrac12$** (Siegel 1935, $\varepsilon = \tfrac12$ for $r = n$ [unverified]):
$\mathrm{Mass}(L) = 1/|O(L)| = \tfrac12$ for every lattice $L$ in $(F, a x_0^2)$, $a \ne 0$, over every number field $F$. -/
@[kb "siegel1935" "ε = 1/2 for r = n, rank one over F [unverified]"]
theorem mass_rankOne (ha : Q.coeff 0 0 ≠ 0) (L : Lat F 1) : mass Q L = 1 / 2 := by
  rw [mass, genusClasses_rankOne ha, finsum_mem_singleton]
  change ((Nat.card (autLat Q L.1) : ℕ) : ℝ)⁻¹ = 1 / 2
  rw [card_autLat_rankOne ha]; norm_num

end Orth

/-! ### Tamagawa bookkeeping: $\tau(SO_1)$ -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 1)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem coeff_ne_zero_of_nondegenerate (hQ : Q₀.Nondegenerate) : (QF).coeff 0 0 ≠ 0 := by
  have h : Q₀.hessian.det = 2 * Q₀.coeff 0 0 := by
    rw [Matrix.det_unique]; simp [QuadForm.hessian]; ring
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [h, h0, mul_zero]
  simpa [QuadForm.map] using hc

/-- **$SO_1$ is trivial, so the $SO$-mass is $1$:** $\mathrm{dcMass}(SO(V)(F), SO(\hat L)) = 2\,\mathrm{Mass}(L) = 1$ for
$L = \mathcal O_F$ in rank one (`mass_SO_eq_two_mul_mass` with `mass_rankOne`). -/
theorem dcMass_SO_rankOne (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F 1).1) :
    dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF (stdLat F 1)).subgroupOf (soAf QF)) = 1 := by
  rw [mass_SO_eq_two_mul_mass Q₀ hQ Nat.one_pos hpd hLi,
    mass_rankOne (coeff_ne_zero_of_nondegenerate Q₀ hQ)]
  norm_num

/-- **$\tau(SO_1) = \mu_{\mathrm{Tam}}(K_{SO})$** in the terms (Weil 1982, §3.7 [unverified]): since $SO_1$ is trivial,
the double-coset sum in `tauSO` is $1$ and $\tau(SO_1)$ is the Tamagawa measure `tamagawaK` of the (trivial) compact
group $K_{SO}$. -/
@[kb "weil1982" "§3.7 (rank one) [unverified]"]
theorem tauSO_rankOne (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F 1).1) : tauSO Q₀ = tamagawaK Q₀ := by
  rw [tauSO, dcMass_SO_rankOne Q₀ hQ hpd hLi, mul_one]

/-- **$\mathrm{vol}(SO_1(\mathbb R)) = 1/(2d)$** for the gauge-form normalization (`archVolSO`, $n = 1$): the $j = 0$
factor is $\pi^{1/2}/\Gamma(1/2) = 1$ and $d^{-(n+1)/2} = d^{-1}$. (The two points $\pm 1$ of $O_1(\mathbb R)$ each carry
$1/|d(dx^2)/dx| = 1/(2d)$; $SO_1$ keeps one of them.) Valid for every real $d$ (Lean's $0^{-1} = 0$). -/
theorem archVolSO_one (d : ℝ) : archVolSO 1 d = 1 / (2 * d) := by
  rw [archVolSO]
  norm_num [Finset.prod_range_one, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, Real.rpow_neg_one]
  have : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp

/-- **$\alpha_\mathfrak p(L, L) = 1$ at good primes in rank one** ($\mathfrak p \nmid 2\det H$): the
`siegelDensity_good_odd` with $n = 2\cdot 0 + 1$ (the generic factor is the empty product). Equivalently
$\beta_\mathfrak p(\langle a\rangle, \langle a\rangle) = \#\{\pm 1\} = 2$ and Siegel's $\tfrac12$. -/
theorem siegelDensity_rankOne_good (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ badPrimes Q₀) : LocalDensity.NF.siegelDensity v Q₀ Q₀ = 1 := by
  have := siegelDensity_good_odd 0 Q₀ hQ v hv
  rw [this, genericOdd]; simp

/-- **$\prod_\mathfrak p\alpha_\mathfrak p(L, L)$ converges in rank one** (it is a finite product; contrast
`Siegel.RankOne.not_multipliable_eulerFactor` for $\prod_p\beta_p(m)$). -/
theorem multipliable_siegelDensity_rankOne (hQ : Q₀.Nondegenerate) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
  multipliable_of_ne_finset_one (s := (finite_badPrimes Q₀ hQ).toFinset) fun v hv =>
    siegelDensity_rankOne_good Q₀ hQ v (by simpa using hv)

/-- **The Tamagawa measure of $K_{SO_1}$, explicitly** (the `tamagawaK` at $n = 1$):
$$\mu_{\mathrm{Tam}}(K_{SO}) = \prod_{\sigma : F \to \mathbb C}\frac{1}{2 d_\sigma}\cdot\prod_{\mathfrak p \mid 2\det H}\alpha_\mathfrak p(L, L),
\qquad d_\sigma = |\sigma(\det H/2)| = |\sigma(a)|,$$
a finite product ($|d_F|^{-n(n-1)/4} = 1$ for $n = 1$). By `tauSO_rankOne` this is $\tau(SO_1)$. -/
@[kb "weil1982" "§2.3, §3.7 (rank one) [unverified]"]
theorem tamagawaK_rankOne (hQ : Q₀.Nondegenerate) :
    tamagawaK Q₀ = (∏ σ : F →ₐ[ℚ] ℂ, 1 / (2 * detGram Q₀ σ)) *
      ∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  rw [tamagawaK, tprod_eq_prod (s := (finite_badPrimes Q₀ hQ).toFinset) (fun v hv => siegelDensity_rankOne_good Q₀ hQ v (by simpa using hv))]
  simp only [archVolSO_one]
  norm_num

end Tamagawa

end QuadFormsKB.Tamagawa.RankOne
