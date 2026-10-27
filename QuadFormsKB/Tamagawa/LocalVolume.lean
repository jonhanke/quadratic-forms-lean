/-
# Local Haar volumes on $O(V)(F_\mathfrak p)$ and $SO(V)(F_\mathfrak p)$

**Layer:** an abstract group with a reference subgroup (the combinatorial Haar measure), then
$G = O(V)(F_\mathfrak p)$ for $V = (F^n, Q_0 \otimes F)$, $Q_0$ an integral form over $\mathcal O_F$, with reference subgroup
$O(L_\mathfrak p) = O(V)(\mathfrak o_\mathfrak p)$ (`Lattices.stdStab`, $L = \mathcal O_F^n$).

## The combinatorial Haar measure
Mathlib's `MeasureTheory.Measure.haar` would need the topology of $O(V)(F_\mathfrak p)$ as a locally compact group and
the identification of the gauge-form measure with a Haar measure; neither is cheap. Every compact open subset of a
totally disconnected group is a finite union of left cosets of a compact open subgroup, and compact open subgroups are
pairwise commensurable. So a left-invariant measure on compact open sets is determined by its value $c$ on one compact
open subgroup $K_0$:
$$\mu(H) = c\,\frac{[H : H\cap K_0]}{[K_0 : H \cap K_0]},\qquad \mu\Big(\bigsqcup_{i=1}^{N} g_iH\Big) = N\,\mu(H).$$
This file defines exactly that (`idxVol`, `cosetVol`, `haarVol`) for **any** group $G$ and subgroup $K_0$, on the
"compact open" sets = finite unions of left cosets of subgroups commensurable with $K_0$ (`IsCosetUnion`), and proves
that it is well defined (independent of the subgroup, `cosetVol_eq_of_commensurable`), left invariant
(`haarVol_smul`), finitely additive (`haarVol_union`), with $\mu(H) = \mu(K)/[K : H]$ (`idxVol_of_le`). The topology
is not formalized: "compact open" is represented by this combinatorial class.

## The normalization (gauge form)
$K_0 = O(L_\mathfrak p)$ gets $c = \beta_\mathfrak p(L, L)$, the self-density (`volO`). This is the volume for the gauge form
$\omega_Q = dX/dQ$ on $O(V)$: by Weil's fibration $X \mapsto Q \circ X$ of $M_n$ over the space of quadratic forms
(coefficients $c_{ij}$, $i \le j$), with $dX$, $dQ$ the Haar measures giving $M_n(\mathfrak o_\mathfrak p)$ and
$\mathrm{Sym}(\mathfrak o_\mathfrak p)$ volume $1$,
$$\mathrm{vol}_{|\omega_Q|}(O(L_\mathfrak p)) = \lim_k \frac{\mathrm{vol}\{X \in M_n(\mathfrak o) : Q\circ X \equiv Q \bmod \mathfrak p^k\}}
  {\mathrm{vol}(Q + \mathfrak p^k\,\mathrm{Sym})} = \lim_k \frac{A_{\mathfrak p^k}(Q,Q)\,N\mathfrak p^{-kn^2}}{N\mathfrak p^{-kn(n+1)/2}}
  = \beta_\mathfrak p(Q, Q)$$
(Weil 1982, §2.2 and §3.5 [unverified locator]; Gan–Yu 2000, §3 [unverified]; AWS notes Lemma 2.7.2 for the analogue with
numbers, `AWS.vol_preimage_div_vol`). The middle equality is `fiberVolume_eq` (the residue classes mod $\mathfrak p^k$ have
volume $N\mathfrak p^{-kn^2}$ and $N\mathfrak p^{-kn(n+1)/2}$; this Haar-measure fact is not formalized here).

*Convention (quadratic, not Gram).* The coordinates on the space of forms are the coefficients $c_{ii} = Q(e_i)$,
$c_{ij} = B(e_i, e_j)$, as in `repCountForm`; at a dyadic prime this differs from the Gram-matrix coordinates
$a_{ij} = c_{ij}/2$ ($i < j$) by $|2|_\mathfrak p^{-n(n-1)/2}$, and the product formula makes the global measure independent
of this choice.

**Proves**
* `volO_eq`: $\mathrm{vol}(O(L_\mathfrak p)) = \beta_\mathfrak p(L, L)$ (definition) and `fiberVolume_eq` (the fibration limit);
* `relIndex_soStab`: $[O(L_\mathfrak p) : SO(L_\mathfrak p)] = 2$ at **every** $\mathfrak p$ (reflection, `Reflection.lean`), hence
  `volSO_eq`: $\mathrm{vol}(SO(L_\mathfrak p)) = \beta_\mathfrak p(L,L)/2 = \alpha_\mathfrak p(L, L)$ (Siegel's density, `NF.siegelDensity`);
* `volSO_good_odd`, `volSO_good_even`: for $\mathfrak p \nmid 2\det H_{Q_0}$,
  $\mathrm{vol}(SO(L_\mathfrak p)) = \prod_{i=1}^m(1 - N\mathfrak p^{-2i})$ ($n = 2m+1$) and
  $(1 - \chi(\mathfrak p)N\mathfrak p^{-m})\prod_{i=1}^{m-1}(1 - N\mathfrak p^{-2i})$ ($n = 2m$), from `OrthFq.lean`.
-/
import QuadFormsKB.Tamagawa.OrbitMass
import QuadFormsKB.Tamagawa.Reflection
import QuadFormsKB.Tamagawa.OrthFq

open Subgroup

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

/-! ### The index volume on a commensurability class -/

section Abstract

variable {G : Type*} [Group G] (K₀ : Subgroup G) (c : ℝ)

/-- **The Haar volume of a subgroup** commensurable with $K_0$, normalized by $\mu(K_0) = c$:
$\mu(H) = c\,[H : H \cap K_0]/[K_0 : H \cap K_0]$. -/
@[kb "weil1982" "§2.1 (Haar measures on p-adic groups) [unverified]"]
def idxVol (H : Subgroup G) : ℝ := c * (K₀.relIndex H : ℝ) / (H.relIndex K₀ : ℝ)

theorem idxVol_self : idxVol K₀ c K₀ = c := by simp [idxVol, relIndex_self]

/-- **$\mu(H) = [H : H']\,\mu(H')$** for $H' \le H$, both commensurable with $K_0$. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem idxVol_of_le {H H' : Subgroup G} (hle : H' ≤ H) (hH : H.Commensurable K₀)
    (hH' : H'.Commensurable K₀) : idxVol K₀ c H = H'.relIndex H * idxVol K₀ c H' := by
  have e1 := relIndex_mul_relIndex _ _ _ (inf_le_inf_right K₀ hle) (inf_le_right : H ⊓ K₀ ≤ K₀)
  rw [inf_relIndex_right, inf_relIndex_right] at e1
  have e2 := relIndex_mul_relIndex _ _ _ (inf_le_inf_right K₀ hle) (inf_le_left : H ⊓ K₀ ≤ H)
  rw [inf_relIndex_left] at e2
  have e3 := relIndex_mul_relIndex _ _ _ (inf_le_left : H' ⊓ K₀ ≤ H') hle
  rw [inf_relIndex_left] at e3
  have hH1 : H.relIndex K₀ ≠ 0 := hH.1.relIndex_ne_zero
  have hH'1 : H'.relIndex K₀ ≠ 0 := hH'.1.relIndex_ne_zero
  have ha : (H' ⊓ K₀).relIndex (H ⊓ K₀) ≠ 0 := by
    intro h; rw [h, zero_mul] at e1; exact hH'1 e1.symm
  unfold idxVol
  have hHK : (H.relIndex K₀ : ℝ) ≠ 0 := by exact_mod_cast hH1
  have hH'K : (H'.relIndex K₀ : ℝ) ≠ 0 := by exact_mod_cast hH'1
  have e1' : ((H' ⊓ K₀).relIndex (H ⊓ K₀) : ℝ) * H.relIndex K₀ = H'.relIndex K₀ := by exact_mod_cast e1
  have e23 : ((H' ⊓ K₀).relIndex (H ⊓ K₀) : ℝ) * K₀.relIndex H = K₀.relIndex H' * H'.relIndex H := by
    exact_mod_cast e2.trans e3.symm
  have ha' : ((H' ⊓ K₀).relIndex (H ⊓ K₀) : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← e1']
  field_simp
  linear_combination c * e23

/-- **"Compact open" sets:** finite unions of left cosets $gH$ of a subgroup $H$ (i.e. $UH = U$ with finitely many
cosets). For $G = O(V)(F_\mathfrak p)$ and $H$ compact open these are exactly the compact open subsets. -/
def IsCosetUnion (H : Subgroup G) (U : Set G) : Prop :=
  (∀ u ∈ U, ∀ h ∈ H, u * h ∈ U) ∧ (QuotientGroup.mk '' U : Set (G ⧸ H)).Finite

/-- **The volume of a finite union of left $H$-cosets:** (number of cosets) $\times\,\mu(H)$. -/
def cosetVol (H : Subgroup G) (U : Set G) : ℝ :=
  Nat.card (QuotientGroup.mk '' U : Set (G ⧸ H)) * idxVol K₀ c H

theorem IsCosetUnion.mono {H H' : Subgroup G} (hle : H' ≤ H) (hfin : H'.relIndex H ≠ 0) {U : Set G}
    (hU : IsCosetUnion H U) : IsCosetUnion H' U := by
  refine ⟨fun u hu h hh => hU.1 u hu h (hle hh), ?_⟩
  -- the images in G/H' lie over the finitely many cosets of G/H, with finite fibres
  have hfib : ∀ x : G ⧸ H, ({y : G ⧸ H' | (Subgroup.quotientEquivProdOfLE hle y).1 = x}).Finite := by
    intro x
    have h' : Nat.card {y : G ⧸ H' // (Subgroup.quotientEquivProdOfLE hle y).1 = x} ≠ 0 := by
      rw [card_fiber_quotient hle x]; exact hfin
    have : Finite {y : G ⧸ H' // (Subgroup.quotientEquivProdOfLE hle y).1 = x} :=
      Nat.finite_of_card_ne_zero h'
    exact Set.finite_coe_iff.mp this
  refine ((hU.2.biUnion fun x _ => hfib x)).subset ?_
  rintro _ ⟨u, hu, rfl⟩
  exact Set.mem_biUnion (x := QuotientGroup.mk u) ⟨u, hu, rfl⟩ rfl

/-- **Independence of the subgroup** for $H' \le H$: a union of $N$ left $H$-cosets is a union of $N[H:H']$ left
$H'$-cosets. -/
theorem cosetVol_of_le {H H' : Subgroup G} (hle : H' ≤ H) (hH : H.Commensurable K₀)
    (hH' : H'.Commensurable K₀) {U : Set G} (hU : IsCosetUnion H U) :
    cosetVol K₀ c H' U = cosetVol K₀ c H U := by
  classical
  have hfin : H'.relIndex H ≠ 0 :=
    relIndex_ne_zero_trans hH'.1.relIndex_ne_zero hH.2.relIndex_ne_zero
  have hU' := hU.mono hle hfin
  unfold cosetVol
  rw [idxVol_of_le K₀ c hle hH hH']
  -- count the H'-cosets fibrewise over the H-cosets
  have hcount : Nat.card (QuotientGroup.mk '' U : Set (G ⧸ H')) =
      H'.relIndex H * Nat.card (QuotientGroup.mk '' U : Set (G ⧸ H)) := by
    have := hU.2.to_subtype
    have := hU'.2.to_subtype
    let p : G ⧸ H' → G ⧸ H := fun y => (Subgroup.quotientEquivProdOfLE hle y).1
    have hp : ∀ g : G, p (QuotientGroup.mk g) = QuotientGroup.mk g := fun g => rfl
    -- (mk '' U : G/H') is the preimage of (mk '' U : G/H)
    have hpre : (QuotientGroup.mk '' U : Set (G ⧸ H')) = p ⁻¹' (QuotientGroup.mk '' U) := by
      ext y
      induction y using QuotientGroup.induction_on with | H g => ?_
      constructor
      · rintro ⟨u, hu, he⟩
        exact ⟨u, hu, by rw [← he]; rfl⟩
      · rintro ⟨u, hu, he⟩
        rw [hp] at he
        have := QuotientGroup.eq.mp he
        refine ⟨g, ?_, rfl⟩
        have hg : g = u * (u⁻¹ * g) := by group
        rw [hg]; exact hU.1 u hu _ this
    rw [hpre]
    have hfibcard : ∀ x : (QuotientGroup.mk '' U : Set (G ⧸ H)),
        Nat.card {y : p ⁻¹' (QuotientGroup.mk '' U) // p y = x} = H'.relIndex H := by
      intro x
      rw [← card_fiber_quotient hle x.1]
      exact Nat.card_congr
        { toFun := fun y => ⟨y.1.1, y.2⟩
          invFun := fun y => ⟨⟨y.1, Set.mem_preimage.mpr (by
              have hy : p y.1 = x.1 := y.2
              rw [hy]; exact x.2)⟩, y.2⟩
          left_inv := fun y => rfl
          right_inv := fun y => rfl }
    have : Fintype (QuotientGroup.mk '' U : Set (G ⧸ H)) := Fintype.ofFinite _
    have hfinpre : Finite (p ⁻¹' (QuotientGroup.mk '' U)) := by rw [← hpre]; exact hU'.2.to_subtype
    have : ∀ x : (QuotientGroup.mk '' U : Set (G ⧸ H)),
        Fintype {y : p ⁻¹' (QuotientGroup.mk '' U) // p y = x} := fun x => Fintype.ofFinite _
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv (fun y : p ⁻¹' (QuotientGroup.mk '' U) =>
      (⟨p y.1, y.2⟩ : (QuotientGroup.mk '' U : Set (G ⧸ H))))).symm, Nat.card_sigma]
    rw [Finset.sum_congr rfl (fun x _ => (Nat.card_congr
      { toFun := fun y => ⟨y.1, congrArg Subtype.val y.2⟩
        invFun := fun y => ⟨y.1, Subtype.ext y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }).trans (hfibcard x))]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card]
  rw [hcount]
  push_cast
  ring

/-- **Independence of the subgroup** in general: two commensurable subgroups saturating $U$ give the same volume
(pass through $H_1 \cap H_2$). -/
theorem cosetVol_eq_of_commensurable {H₁ H₂ : Subgroup G} (h₁ : H₁.Commensurable K₀) (h₂ : H₂.Commensurable K₀)
    {U : Set G} (hU₁ : IsCosetUnion H₁ U) (hU₂ : IsCosetUnion H₂ U) :
    cosetVol K₀ c H₁ U = cosetVol K₀ c H₂ U := by
  have h12 : (H₁ ⊓ H₂).Commensurable K₀ := Commensurable.inf_left h₁ h₂
  rw [← cosetVol_of_le K₀ c inf_le_left h₁ h12 hU₁, ← cosetVol_of_le K₀ c inf_le_right h₂ h12 hU₂]

/-- **Compact open sets** (combinatorial): finite unions of left cosets of a subgroup commensurable with $K_0$. -/
def IsCompactOpen (U : Set G) : Prop := ∃ H : Subgroup G, H.Commensurable K₀ ∧ IsCosetUnion H U

open Classical in
/-- **The left Haar measure** on compact open sets, normalized by $\mu(K_0) = c$: $\mu(U) = N\,\mu(H)$ for
$U = \bigsqcup_{i=1}^N g_iH$, any admissible $H$ (well defined by `cosetVol_eq_of_commensurable`); $0$ on other sets. -/
@[kb "weil1982" "§2.1 [unverified]"]
def haarVol (U : Set G) : ℝ := if h : IsCompactOpen K₀ U then cosetVol K₀ c h.choose U else 0

theorem haarVol_eq {H : Subgroup G} (hH : H.Commensurable K₀) {U : Set G} (hU : IsCosetUnion H U) :
    haarVol K₀ c U = cosetVol K₀ c H U := by
  have h : IsCompactOpen K₀ U := ⟨H, hH, hU⟩
  rw [haarVol]; simp only [h, ↓reduceDIte]
  exact cosetVol_eq_of_commensurable K₀ c h.choose_spec.1 hH h.choose_spec.2 hU

/-- **$\mu(H) = $ `idxVol`** for a subgroup $H$ commensurable with $K_0$ (one coset). -/
theorem haarVol_subgroup {H : Subgroup G} (hH : H.Commensurable K₀) :
    haarVol K₀ c (H : Set G) = idxVol K₀ c H := by
  have hmk : ∀ u : G, (QuotientGroup.mk u : G ⧸ H) = QuotientGroup.mk 1 ↔ u ∈ H := by
    intro u; rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have hU : IsCosetUnion H (H : Set G) := by
    refine ⟨fun u hu h hh => H.mul_mem hu hh, ?_⟩
    refine (Set.finite_singleton (QuotientGroup.mk 1 : G ⧸ H)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (hmk u).mpr hu
  rw [haarVol_eq K₀ c hH hU, cosetVol]
  have : (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ H)) = {QuotientGroup.mk 1} := by
    ext x
    induction x using QuotientGroup.induction_on with | H g => ?_
    constructor
    · rintro ⟨u, hu, he⟩
      rw [Set.mem_singleton_iff, ← he]
      exact (hmk u).mpr hu
    · intro hx
      exact ⟨g, (hmk g).mp hx, rfl⟩
  rw [this, Nat.card_unique, Nat.cast_one, one_mul]

/-- **Normalization:** $\mu(K_0) = c$. -/
theorem haarVol_ref : haarVol K₀ c (K₀ : Set G) = c := by
  rw [haarVol_subgroup K₀ c (Commensurable.refl K₀), idxVol_self]

open Pointwise in
/-- **Left invariance:** $\mu(gU) = \mu(U)$. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem haarVol_smul (g : G) (U : Set G) : haarVol K₀ c (g • U) = haarVol K₀ c U := by
  have himg : ∀ (g : G) (U : Set G) (H : Subgroup G), (QuotientGroup.mk '' (g • U) : Set (G ⧸ H)) =
      (fun x : G ⧸ H => g • x) '' (QuotientGroup.mk '' U) := by
    intro g U H
    ext x
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨g * u, ⟨u, hu, rfl⟩, rfl⟩
  have hsat : ∀ (g : G) (U : Set G) (H : Subgroup G), IsCosetUnion H U → IsCosetUnion H (g • U) := by
    intro g U H hU
    refine ⟨?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩ h hh
      exact ⟨u * h, hU.1 u hu h hh, by simp [smul_eq_mul, mul_assoc]⟩
    · rw [himg]; exact hU.2.image _
  by_cases hc : IsCompactOpen K₀ U
  · obtain ⟨H, hH, hU⟩ := hc
    rw [haarVol_eq K₀ c hH (hsat g U H hU), haarVol_eq K₀ c hH hU, cosetVol, cosetVol, himg,
      Nat.card_image_of_injective (MulAction.injective g)]
  · have hc' : ¬ IsCompactOpen K₀ (g • U) := by
      rintro ⟨H, hH, hU⟩
      apply hc
      refine ⟨H, hH, ?_⟩
      have := hsat g⁻¹ _ H hU
      rwa [inv_smul_smul] at this
    rw [haarVol, haarVol]; simp only [hc, hc', ↓reduceDIte]

/-- **Finite additivity** on disjoint compact open sets. -/
@[kb "weil1982" "§2.1 [unverified]"]
theorem haarVol_union {U V : Set G} (hU : IsCompactOpen K₀ U) (hV : IsCompactOpen K₀ V)
    (hUV : Disjoint U V) : haarVol K₀ c (U ∪ V) = haarVol K₀ c U + haarVol K₀ c V := by
  classical
  obtain ⟨H₁, h₁, hU₁⟩ := hU
  obtain ⟨H₂, h₂, hV₂⟩ := hV
  set H := H₁ ⊓ H₂
  have hH : H.Commensurable K₀ := Commensurable.inf_left h₁ h₂
  have hU' := hU₁.mono inf_le_left (relIndex_ne_zero_trans hH.1.relIndex_ne_zero h₁.2.relIndex_ne_zero)
  have hV' := hV₂.mono inf_le_right (relIndex_ne_zero_trans hH.1.relIndex_ne_zero h₂.2.relIndex_ne_zero)
  have hUV' : IsCosetUnion H (U ∪ V) := by
    refine ⟨?_, ?_⟩
    · rintro u (hu | hu) h hh
      · exact Or.inl (hU'.1 u hu h hh)
      · exact Or.inr (hV'.1 u hu h hh)
    · rw [Set.image_union]; exact hU'.2.union hV'.2
  rw [haarVol_eq K₀ c hH hUV', haarVol_eq K₀ c hH hU', haarVol_eq K₀ c hH hV', cosetVol, cosetVol, cosetVol,
    ← add_mul, Set.image_union]
  congr 1
  have hdisj : Disjoint (QuotientGroup.mk '' U : Set (G ⧸ H)) (QuotientGroup.mk '' V) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have := QuotientGroup.eq.mp he
    have hvu : u = v * (v⁻¹ * u) := by group
    exact Set.disjoint_left.mp hUV hu (by rw [hvu]; exact hV'.1 v hv _ this)
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hdisj hU'.2 hV'.2]
  push_cast; ring

end Abstract

/-! ### $SO$ inside $O$ -/

section SO

open NumberField IsDedekindDomain Lattices Matrix

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **$SO(V)(R) = \{g \in O(V)(R) : \det g = 1\}$** for an $F$-algebra $R$. -/
@[kb "omeara1963" "§43 (O⁺(V)) [unverified]"]
def soSub (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] : Subgroup (orthGroup Q R) where
  carrier := {g | (g : GL (Fin n) R).val.det = 1}
  mul_mem' {a b} ha hb := by
    change ((a : GL (Fin n) R) * (b : GL (Fin n) R)).val.det = 1
    rw [Units.val_mul, det_mul, show (a : GL (Fin n) R).val.det = 1 from ha,
      show (b : GL (Fin n) R).val.det = 1 from hb, one_mul]
  one_mem' := by change (1 : GL (Fin n) R).val.det = 1; simp
  inv_mem' {a} ha := by
    change ((a : GL (Fin n) R)⁻¹).val.det = 1
    have h := congrArg Matrix.det (Units.inv_mul (a : GL (Fin n) R))
    rw [det_mul, show (a : GL (Fin n) R).val.det = 1 from ha, mul_one, det_one] at h
    exact h

theorem mem_soSub {Q : QuadForm F n} {R : Type*} [CommRing R] [Algebra F R] {g : orthGroup Q R} :
    g ∈ soSub Q R ↔ (g : GL (Fin n) R).val.det = 1 := Iff.rfl

/-- **Isometries have determinant $\pm 1$** over a field extension of $F$, for nondegenerate $Q$. -/
theorem det_eq_one_or_neg_one (Q : QuadForm F n) (hQ : Q.Nondegenerate) {R : Type*} [Field R] [Algebra F R]
    (g : orthGroup Q R) : (g : GL (Fin n) R).val.det = 1 ∨ (g : GL (Fin n) R).val.det = -1 := by
  have h := congrArg Matrix.det ((mem_orthGroup Q).mp g.2)
  rw [det_mul, det_mul, det_transpose] at h
  have hH : (Q.hessian.map (algebraMap F R)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr hQ
  have : (g : GL (Fin n) R).val.det * (g : GL (Fin n) R).val.det = 1 := by
    apply mul_right_cancel₀ hH
    linear_combination h
  exact mul_self_eq_one_iff.mp this

/-- **$[K : K \cap SO] = 2$** for a subgroup $K \le O(V)(R)$ containing an improper element ($R$ a field of
characteristic $\ne 2$ over $F$): multiplication by an improper $\rho \in K$ swaps the two cosets. -/
theorem relIndex_soSub_eq_two (Q : QuadForm F n) (hQ : Q.Nondegenerate) {R : Type*} [Field R] [Algebra F R]
    [CharZero R] (K : Subgroup (orthGroup Q R)) (ρ : orthGroup Q R) (hρK : ρ ∈ K)
    (hρ : (ρ : GL (Fin n) R).val.det = -1) : (soSub Q R ⊓ K).relIndex K = 2 := by
  rw [inf_relIndex_right, Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨ρ, hρK⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, hρ]
  have h1 : (1 : R) ≠ -1 := by
    intro h; have : (2 : R) = 0 := by linear_combination h
    exact two_ne_zero this
  rcases det_eq_one_or_neg_one Q hQ (b : orthGroup Q R) with h | h <;>
    simp [h, h1.symm, xor_true, xor_false]

end SO

/-! ### The local measures at a finite prime -/

section Local

open NumberField IsDedekindDomain Lattices LocalDensity

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
  (Q₀ : QuadForm (𝓞 F) n)

local notation "Fv" => v.adicCompletion F
local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The local Haar measure on $O(V)(F_\mathfrak p)$** for the gauge form $\omega_Q = dX/dQ$, $V = (F^n, Q_0)$: the
combinatorial Haar measure (`haarVol`) normalized by $\mathrm{vol}(O(L_\mathfrak p)) = \beta_\mathfrak p(L, L)$,
$L = \mathcal O_F^n$, $O(L_\mathfrak p)$ = `stdStab` (see the module docstring for the gauge-form justification). -/
@[kb "weil1982" "§2.2, §3.5 (gauge-form measures) [unverified locator]"]
def volLoc : Set (orthGroup QF Fv) → ℝ := haarVol (stdStab QF v) (NF.localDensityForm v Q₀ Q₀)

/-- **$SO(L_\mathfrak p) = O(L_\mathfrak p) \cap SO(V)(F_\mathfrak p)$.** -/
def soStab : Subgroup (orthGroup QF Fv) := soSub QF Fv ⊓ stdStab QF v

/-- **The fibration limit** (the "middle equality" of the module docstring): for nondegenerate $Q_0$,
$$\lim_k \frac{A_{\mathfrak p^k}(Q,Q)\,N\mathfrak p^{-kn^2}}{N\mathfrak p^{-kn(n+1)/2}} = \beta_\mathfrak p(Q, Q),$$
i.e. $\mathrm{vol}\{X : Q\circ X \equiv Q \bmod \mathfrak p^k\}/\mathrm{vol}(Q + \mathfrak p^k\mathrm{Sym})$ for the normalized Haar
measures on $M_n(\mathfrak o_\mathfrak p)$ and on quadratic forms over $\mathfrak o_\mathfrak p$ (each residue class mod $\mathfrak p^k$ of
matrices, resp. forms, has volume $N\mathfrak p^{-kn^2}$, resp. $N\mathfrak p^{-kn(n+1)/2}$; this Haar-measure fact is not
formalized). The sequence is eventually constant. -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem fiberVolume_eq (hQ : Q₀.Nondegenerate) :
    ∀ᶠ k in Filter.atTop, (NF.repCountForm v Q₀ Q₀ k : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ (k * n ^ 2))⁻¹ /
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (k * (n * (n + 1) / 2)))⁻¹ = NF.localDensityForm v Q₀ Q₀ := by
  filter_upwards [NF.localDensityForm_self_eventually_eq v Q₀ hQ] with k hk
  rw [← hk]
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : 0 < Ideal.absNorm v.asIdeal := by rw [← NF.q_completion]; exact DVR.q_pos
    exact_mod_cast this
  have hexp : k * n ^ 2 = k * (n * (n - 1) / 2) + k * (n * (n + 1) / 2) := by
    rw [← mul_add]
    congr 1
    have h1 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
    have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel] at h1 ⊢
      have : (n + 1) * n + (n + 1) * (n + 1 + 1) = 2 * (n + 1) ^ 2 := by ring
      omega
  rw [hexp, pow_add]
  field_simp

/-- **$\mathrm{vol}(O(L_\mathfrak p)) = \beta_\mathfrak p(L, L)$** (the normalization; Siegel's density is half of it). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem volO_eq : volLoc v Q₀ (stdStab QF v : Set (orthGroup QF Fv)) = NF.localDensityForm v Q₀ Q₀ :=
  haarVol_ref _ _

/-- **$[O(L_\mathfrak p) : SO(L_\mathfrak p)] = 2$** at every finite prime (a reflection of $L_\mathfrak p$,
`exists_stdStab_det_neg_one`). -/
@[kb "omeara1963" "§92 [unverified]"]
theorem relIndex_soStab (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    (soStab v Q₀).relIndex (stdStab QF v) = 2 := by
  have hQF : (QF).Nondegenerate := by
    rw [QuadForm.Nondegenerate]
    have : (QF).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (RingOfIntegers.coe_injective)).mpr hQ
  obtain ⟨ρ, hρ, hdet⟩ := exists_stdStab_det_neg_one v Q₀ hQ hn
  exact relIndex_soSub_eq_two QF hQF (stdStab QF v) ρ hρ hdet

/-- **$\mathrm{vol}(SO(L_\mathfrak p)) = \beta_\mathfrak p(L,L)/2 = \alpha_\mathfrak p(L, L)$**, Siegel's density
(`NF.siegelDensity`), at every finite prime. This is the correct form of "$\mathrm{vol}(O(L_\mathfrak p)) = \beta/2$": the
factor $\tfrac12$ belongs to $SO$, not to $O$ (`volO_eq`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem volSO_eq (hQ : Q₀.Nondegenerate) (hn : 0 < n) :
    volLoc v Q₀ (soStab v Q₀ : Set (orthGroup QF Fv)) = NF.siegelDensity v Q₀ Q₀ := by
  have h2 := relIndex_soStab v Q₀ hQ hn
  have hcomm : (soStab v Q₀).Commensurable (stdStab QF v) :=
    ⟨⟨by rw [h2]; norm_num⟩, ⟨by
      rw [Subgroup.relIndex_eq_one.mpr (show soStab v Q₀ ≤ stdStab QF v from inf_le_right)]; norm_num⟩⟩
  rw [volLoc, haarVol_subgroup _ _ hcomm, idxVol, h2,
    Subgroup.relIndex_eq_one.mpr (show soStab v Q₀ ≤ stdStab QF v from inf_le_right),
    NF.siegelDensity]
  simp only [↓reduceIte]
  push_cast; ring

/-- **The quadratic character at $\mathfrak p$** attached to $Q_0$: $\chi(\mathfrak p) = \chi_{\mathfrak p}((-1)^{\lfloor n/2\rfloor}\det(H/2))$
(`DVR.chiDisc` of $Q_0 \otimes \mathfrak o_\mathfrak p$; the Legendre symbol of the discriminant at $\mathfrak p$) for
$\mathfrak p \nmid 2\det H_{Q_0}$, and $0$ otherwise. For even $n = 2m$ this is the character of $F(\sqrt{(-1)^m\det})/F$
at $\mathfrak p$ (not formalized as a Hecke character; only its values are used). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def chiP : ℝ := by
  classical
  exact if (2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal then 0 else (DVR.chiDisc (NF.Qp v Q₀) : ℝ)

theorem not_dvd_two_of_good (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ¬ NF.π v ∣ 2 := by
  have := (NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
  rwa [pow_one, map_ofNat] at this

theorem not_dvd_det_of_good (hd : Q₀.hessian.det ∉ v.asIdeal) : ¬ NF.π v ∣ (NF.Qp v Q₀).hessian.det := by
  rw [NF.det_hessian_Qp, ← pow_one (NF.π v), NF.π_pow_dvd_ι_iff, pow_one]; exact hd

/-- **Good primes, odd rank** ($n = 2m+1$, $\mathfrak p \nmid 2\det H_{Q_0}$):
$\mathrm{vol}(SO(L_\mathfrak p)) = \prod_{i=1}^{m}(1 - N\mathfrak p^{-2i})$, the reciprocal of the local factor
$\lambda_\mathfrak p = \prod_{i=1}^m \zeta_{F,\mathfrak p}(2i)$ of $\zeta_F(2)\zeta_F(4)\cdots\zeta_F(2m)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem volSO_good_odd (m : ℕ) (Q₀ : QuadForm (𝓞 F) (2 * m + 1)) (hQ : Q₀.Nondegenerate)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hd : Q₀.hessian.det ∉ v.asIdeal) :
    volLoc v Q₀ (soStab v Q₀ : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) =
      ∏ i ∈ Finset.range m, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [volSO_eq v Q₀ hQ (by omega), NF.siegelDensity, NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_odd (NF.π v) m _ (NF.irreducible_π v) (not_dvd_two_of_good v h2)
      (not_dvd_det_of_good v Q₀ hd), NF.q_completion]
  simp only [↓reduceIte]
  ring

/-- **Good primes, even rank** ($n = 2m$, $m \ge 1$, $\mathfrak p \nmid 2\det H_{Q_0}$):
$\mathrm{vol}(SO(L_\mathfrak p)) = (1 - \chi(\mathfrak p)N\mathfrak p^{-m})\prod_{i=1}^{m-1}(1 - N\mathfrak p^{-2i})$, the reciprocal of
the local factor of $L_F(m, \chi)\,\zeta_F(2)\cdots\zeta_F(2m-2)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem volSO_good_even (m : ℕ) (hm : 1 ≤ m) (Q₀ : QuadForm (𝓞 F) (2 * m)) (hQ : Q₀.Nondegenerate)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hd : Q₀.hessian.det ∉ v.asIdeal) :
    volLoc v Q₀ (soStab v Q₀ : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) =
      (1 - chiP v Q₀ * ((Ideal.absNorm v.asIdeal : ℝ) ^ m)⁻¹) *
        ∏ i ∈ Finset.range (m - 1), (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [volSO_eq v Q₀ hQ (by omega), NF.siegelDensity, NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_even (NF.π v) m hm _ (NF.irreducible_π v) (not_dvd_two_of_good v h2)
      (not_dvd_det_of_good v Q₀ hd), NF.q_completion]
  have hχ : chiP v Q₀ = (DVR.chiDisc (NF.Qp v Q₀) : ℝ) := by
    rw [chiP]; simp [h2, hd]
  rw [hχ]
  simp only [↓reduceIte]
  ring

end Local

end QuadFormsKB.Tamagawa
