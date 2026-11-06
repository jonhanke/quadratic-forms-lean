/-
# Hanke 2005, (3.3) at dyadic places with $\widetilde\Lambda_\mathfrak p=\Lambda_\mathfrak p$: reduction to a group order

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a dyadic place $\mathfrak p$ with $\widetilde\Lambda_\mathfrak p=\Lambda_\mathfrak p$ the lattice is even unimodular
($\det H$ a unit), so (O'Meara 93:15, `exists_pairSum_of_isLocalLevel_zero`) the rank is $n=2m$ and the self-density is
$$\beta_\mathfrak p(Q,Q)=\frac{|O(\bar Q)|}{q^{m(2m-1)}}\qquad(\texttt{localDensityForm\_self\_unimodular}),$$
$\bar Q$ the reduction modulo $\mathfrak p$, a nondegenerate quadratic form in $2m$ variables over the residue field
$\mathbb F_q$ of characteristic $2$. This file replaces the old named statement `ShimuraDensityDyadicSelfDual` (a statement
about the whole local factor (3.3)) by the smaller, purely local named statement `DyadicOrthogonalOrder`:
$$|O(\bar Q)|=2q^{m(m-1)}(q^m-\varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1),\qquad
\varepsilon=\begin{cases}+1&t_\mathfrak p=0\\-1&t_\mathfrak p=2,\end{cases}$$
i.e. the classical order of the orthogonal group $O^\varepsilon_{2m}(\mathbb F_q)$ in characteristic $2$ (Dieudonne), with
the sign $\varepsilon$ given by the Witt type of $Q$ over $F_\mathfrak p$ (Hensel lifting of hyperbolic planes).
*Proved here from it* (`shimuraDensityDyadicSelfDual_of_orderCount`): $n$ is even, $t_\mathfrak p\in\{0,2\}$
(`anisoDim_le_two_of_dualIndexAt_eq_one`, parity), $\mathfrak p$ is unramified in $K$
(`not_isRamifiedAt_of_dualIndexAt_eq_one`), and the algebra from the group order to Shimura's $\xi$ and to $\beta$ of
the thesis' normalization.
-/
import QuadFormsKB.Literature.Hanke2005.DensityOddSplit

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices

/-- **The order of $O(\bar Q)$ gives the unimodular self-density, even rank** (any residue characteristic): if $H_Q$ is
unimodular, $n=2m$, $m\ge1$ and $|O(Q\bmod\pi)|=o_{2m}(q,\varepsilon)=2q^{m(m-1)}(q^m-\varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1)$,
then $\beta_\pi(Q,Q)=2(1-\varepsilon q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$. -/
@[kb "kitaoka1993" "§5.6 (|O_n(F_q)| to the self-density) [unverified]"]
theorem localDensityForm_self_even_of_card {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (m : ℕ) (hm : 1 ≤ m) (Q : QuadForm R (2 * m)) (π : R)
    (hπ : Irreducible π) (hdet : IsUnit Q.hessian.det) (ε : ℤ)
    (h : (Nat.card (DVR.orthMod Q π 1) : ℤ) = DVR.oEven (DVR.q R) m ε) :
    DVR.localDensityForm Q Q π = 2 * (1 - (ε : ℝ) * ((DVR.q R : ℝ) ^ m)⁻¹) *
      ∏ i ∈ Finset.range (m - 1), (1 - ((DVR.q R : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [DVR.localDensityForm_self_unimodular Q π hπ hdet]
  unfold DVR.oEven at h
  have hq : (0 : ℝ) < DVR.q R := by exact_mod_cast DVR.q_pos
  have hR : (Nat.card (DVR.orthMod Q π 1) : ℝ) = 2 * (DVR.q R : ℝ) ^ (m * (m - 1)) * ((DVR.q R : ℝ) ^ m - ε) *
      ∏ i ∈ Finset.range (m - 1), ((DVR.q R : ℝ) ^ (2 * (i + 1)) - 1) := by exact_mod_cast h
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [hR, Nat.add_sub_cancel, DVR.prod_sub_one_eq _ hq.ne',
    show 2 * (l + 1) * (2 * (l + 1) - 1) / 2 = (l + 1) * l + (l + 1) + l * (l + 1) by
      rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega,
        show 2 * (l + 1) * (2 * l + 1) = 2 * ((l + 1) * l + (l + 1) + l * (l + 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos], pow_add, pow_add]
  have : (DVR.q R : ℝ) ^ (l + 1) ≠ 0 := pow_ne_zero _ hq.ne'
  field_simp
  ring

/-- **The order of the orthogonal group of the reduction of an even unimodular lattice** (a **named input**: Dieudonne's
order of $O^\varepsilon_{2m}(\mathbb F_q)$, $q$ even, together with the Hensel lifting that identifies the sign). For a
dyadic place $\mathfrak p$, $n=2m$ with $m\ge1$, $Q_0$ nondegenerate with $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=1$
(so the Gram matrix of $Q_0$ at $\mathfrak p$ is unimodular), the group $O(Q_0\bmod\mathfrak p)$ of invertible matrices over
$\mathcal O/\mathfrak p=\mathbb F_q$ preserving $Q_0\bmod\mathfrak p$ has order
$2q^{m(m-1)}(q^m-\varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1)$, where $\varepsilon=+1$ if the anisotropic kernel of $Q_0$ over
$F_\mathfrak p$ is $0$ and $\varepsilon=-1$ otherwise (then it has dimension $2$). Field: `card_eq`. -/
@[kb "omeara1963" "93:15 (even unimodular lattices); order of O^ε_{2m}(F_q), q even: Dieudonne, La geometrie des groupes classiques, Ch. III [unverified]"]
structure DyadicOrthogonalOrder (F : Type) [Field F] [NumberField F] : Prop where
  /-- $|O(Q_0\bmod\mathfrak p)|=o_{2m}(q,\varepsilon)$ with $\varepsilon=+1$ iff $t_\mathfrak p=0$. -/
  card_eq : ∀ {m : ℕ}, 1 ≤ m → ∀ Q₀ : QuadForm (𝓞 F) (2 * m), Q₀.Nondegenerate →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ = 1 →
      (Nat.card (DVR.orthMod (NF.Qp v Q₀) (NF.π v) 1) : ℤ) =
        DVR.oEven (DVR.q (v.adicCompletionIntegers F)) m (if anisoDim v Q₀ = 0 then 1 else -1)

/-- **The order of the orthogonal group of a nonsingular quadratic form over a finite field of characteristic $2$** (a **named input**:
Dieudonne, *La geometrie des groupes classiques*, Ch. III; Artin, *Geometric Algebra*, Ch. III), in the form used here. For a discrete valuation ring
$R$ with finite residue field $\mathbb F_q$ of characteristic $2$ ($\pi\mid2$), $m\ge1$ and a form $Q$ in $2m$ variables over $R$ with unimodular
Hessian (so the reduction $\bar Q$ is a nonsingular quadratic form over $\mathbb F_q$), the group of invertible matrices over $R/\pi$
preserving $\bar Q$ has order
$$2q^{m(m-1)}(q^m-\varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1),\qquad\varepsilon=\begin{cases}+1&\text{Witt index of }\bar Q\text{ is }m\\-1&\text{otherwise.}\end{cases}$$
Field: `card_eq`. -/
@[kb "omeara1963" "93:15 (even unimodular lattices); order of O^ε_{2m}(F_q), q even: Dieudonne, La geometrie des groupes classiques, Ch. III [unverified]"]
structure EvenOrthogonalOrderChar2 : Prop where
  /-- $|O(\bar Q)|=o_{2m}(q,\varepsilon)$ with $\varepsilon=+1$ iff $\bar Q$ has Witt index $m$. -/
  card_eq : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] {π : R}, Irreducible π → π ∣ 2 → ∀ {m : ℕ}, 1 ≤ m →
      ∀ Q : QuadForm R (2 * m), IsUnit Q.hessian.det →
        (Nat.card (DVR.orthMod Q π 1) : ℤ) =
          DVR.oEven (DVR.q R) m
            (if QuadraticForm.wittIndex (Q.map (IsLocalRing.residue R)).toQuadraticForm = m then 1 else -1)

/-- **The Hensel link for an even unimodular lattice** (a **named input**; O'Meara 93:15 and 93:16--93:18, Artin--Schreier): at a dyadic place $\mathfrak p$ with
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=1$ and $n=2m$, the reduction $\bar Q_0$ over $\mathcal O/\mathfrak p$ has maximal Witt index $m$ if and only if
the anisotropic kernel of $Q_0$ over $F_\mathfrak p$ is $0$ (hyperbolic planes lift by Hensel's lemma; two anisotropic residue planes lift to a hyperbolic
$4$-space). Field: `witt_iff`. -/
@[kb "omeara1963" "93:15, 93:16--93:18 (even unimodular lattices: reduction hyperbolic iff the space is hyperbolic)"]
structure DyadicWittLink (F : Type) [Field F] [NumberField F] : Prop where
  /-- Witt index $m$ of the reduction iff $t_\mathfrak p=0$. -/
  witt_iff : ∀ {m : ℕ}, 1 ≤ m → ∀ Q₀ : QuadForm (𝓞 F) (2 * m), Q₀.Nondegenerate →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → dualIndexAt v Q₀ = 1 →
      (QuadraticForm.wittIndex
          ((NF.Qp v Q₀).map (IsLocalRing.residue (v.adicCompletionIntegers F))).toQuadraticForm = m ↔
        anisoDim v Q₀ = 0)

variable {F : Type} [Field F] [NumberField F]

/-- **`DyadicOrthogonalOrder` from the two classical statements:** the finite-field group order and the Hensel link. -/
@[kb "omeara1963" "93:15, 93:16--93:18 (order of the orthogonal group of the reduction; Hensel link)"]
theorem dyadicOrthogonalOrder_of_split (I₁ : EvenOrthogonalOrderChar2) (I₂ : DyadicWittLink F) :
    DyadicOrthogonalOrder F := by
  refine ⟨fun {m} hm Q₀ hQ v h2 h1 => ?_⟩
  have hπ := NF.irreducible_π v
  have hπ2 : NF.π v ∣ 2 := by
    by_contra hd
    exact h2 (DVR.dvr_isUnit_of_not_dvd hπ hd)
  have hdet := isUnit_det_of_dualIndexAt_eq_one v Q₀ h1
  have h := I₁.card_eq hπ hπ2 hm (NF.Qp v Q₀) hdet
  have hw := I₂.witt_iff hm Q₀ hQ v h2 h1
  rw [h]
  simp only [hw]

open DensitySD in
/-- **Siegel's density at a dyadic self-dual place** from the group order: $\alpha_\mathfrak p=[\widetilde\Lambda_\mathfrak p:
\Lambda_\mathfrak p]\,\xi$ with $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=1$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p = Λ_p; from the group order)"]
theorem siegelDensity_selfDual_dyadic (I : DyadicOrthogonalOrder F) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (h2 : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    (h : dualIndexAt v Q₀ = 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  have hπ := NF.irreducible_π v
  have hdet := isUnit_det_of_dualIndexAt_eq_one v Q₀ h
  have hπ2 : NF.π v ∣ 2 := by
    by_contra hd
    exact h2 (DVR.dvr_isUnit_of_not_dvd hπ hd)
  have hq := q_eq v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  -- the rank is even
  obtain ⟨r, A, hr, -, -⟩ := DVR.exists_pairSum_of_isLocalLevel_zero (NF.Qp v Q₀) hπ hπ2 (NF.two_ne_zero' v)
    (isLocalLevel_zero_of_isUnit_det _ _ hdet)
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨r, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have hle := anisoDim_le_two_of_dualIndexAt_eq_one v Q₀ hQ h
  have hpar := anisoDim_parity v Q₀ hQ
  have hr := not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ (even_two_mul m) h
  have hm' : 2 * m / 2 = m := by omega
  have hcard := I.card_eq (by omega) Q₀ hQ v h2 h
  rw [h, one_mul, NF.siegelDensity, if_pos (rfl : 2 * m = 2 * m), NF.localDensityForm_eq_completion,
    localDensityForm_self_even_of_card m (by omega) _ (NF.π v) hπ hdet _ hcard, hq]
  unfold xiAt
  by_cases ht : anisoDim v Q₀ = 0
  · rw [ht]
    simp only [xiShimura, hm', if_true, hr, ite_false, h, ite_true, rpow_neg_nat (hq0), ppow_eq hq0]
    push_cast
    ring
  · have ht2 : anisoDim v Q₀ = 2 := by omega
    rw [ht2]
    simp only [xiShimura, hm', if_false, hr, ite_false, h, ite_true, rpow_neg_nat (hq0), ppow_eq hq0, ht]
    push_cast
    ring

/-- **(3.3) at a dyadic place with $\widetilde\Lambda_\mathfrak p=\Lambda_\mathfrak p$, from the group order** (Hanke thesis,
(3.3), p. 8): `ShimuraDensityDyadicSelfDual F` follows from `DyadicOrthogonalOrder F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p = Λ_p; from the group order)"]
theorem shimuraDensityDyadicSelfDual_of_orderCount (I : DyadicOrthogonalOrder F) : ShimuraDensityDyadicSelfDual F := by
  refine ⟨fun {n} hn Q₀ hQ _ _ v h2 h1 => ?_⟩
  rw [hankeBeta_gramV v Q₀ hQ, siegelDensity_selfDual_dyadic I v hn Q₀ hQ h2 h1]
  unfold shimuraBetaRHS
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow]
  have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  generalize ‖(2 : v.adicCompletion F)‖ = a at *
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have e : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
    congr 1; ring
  rw [e]; ring

end QuadFormsKB.Hanke2005
