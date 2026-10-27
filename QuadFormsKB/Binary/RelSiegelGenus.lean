import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenusGroup

/-!
# Siegel's formula genus by genus for binary lattices over a totally real field

$E/F$ CM, $(C, \eta)$ the proper classes of normalized lattices $L_{C,\eta} = (\mathfrak A_C, c_{C,\eta}N)$, $c_{C,\eta} = \eta/a_C$ (`scaleOf`).
The **genus** of $L_{C,\eta}$ is the vector $(\psi_v(c_{C,\eta}))_v$.

* **`sum_genus_repNumLat`** (every $\nu \ne 0$, unconditional): all representations of $\nu$ come from the genus of $\nu$:
  $\sum_{(C,\eta) \in \mathcal G} r_{L_{C,\eta}}(\nu) = [\psi(\nu) = \mathcal G]\cdot\sum_{\text{all }(C,\eta)} r_{L_{C,\eta}}(\nu)$.
* **`card_genus_eq`** (unconditional): each genus $\mathcal G$ of totally positive classes has as many classes as the
  principal genus (Gauss, `card_fiber_eq`, transported by `classOf_bijective`).
* **`siegel_binaryF_genus`** (conditional on the named input `PosClassNumberRelation`): for $K$ CM, $F = K^+$, an
  $\mathcal O_F$-basis $b$ of $\mathcal O_K$, a genus $\mathcal G = \varphi$ of totally positive classes, and $\nu \gg 0$ divisible only by good
  primes of the norm form $Q_b$,
  $$r_{\mathcal G}(\nu) = \tfrac12\,|d_F|^{-1/2}\,\beta_\infty(\nu)\,L(1,\chi_{K/F})^{-1}\prod_{\mathfrak p \in T}\bigl(1 + \psi_\mathfrak p(\nu)\varphi_\mathfrak p\bigr)
     \prod_{\mathfrak p \mid \nu}\frac{\beta_\mathfrak p(Q_b, \nu)}{1 - \chi(\mathfrak p)N\mathfrak p^{-1}},$$
  $r_\mathcal G(\nu)$ = the average of $r_L(\nu)$ over the proper classes $L$ in $\mathcal G$ (since every $|SO(L)| = w_K$, `properAutEquiv`, this is the mass-weighted average; that identification is a remark, not formalized), $T$ = the
  ramified primes. This is Siegel's formula for $n = 2$, $\varepsilon = \frac12$, regularized product
, with the **ramified local densities entering as** $\beta_\mathfrak p^{\mathcal G}(\nu) = 1 + \psi_\mathfrak p(\nu)\varphi_\mathfrak p \in \{0, 2\}$ for $\nu$ a
  $\mathfrak p$-unit — the classical value, *not* computed here as a local density.

**The input** `PosClassNumberRelation K`: $\#\{\text{totally positive proper classes}\}\cdot Q_K\,h_{K^+}\,2^t = 2\cdot 2^{t-1}\,h_K$
($= h_K/(Q_Kh_{K^+})$ classes for $t \ge 1$, $2h_K/(Q_Kh_{K^+})$ for $t = 0$). Classically this is a consequence of class field theory
(the norm map $\mathrm{Cl}_K \to \mathrm{Cl}^+_{K^+}$ and Hasse's unit index; cf. Chevalley's ambiguous class number formula);
over $\mathbb Q$ it is $h^+(D) = h(D)$. **Given the rest of this file it is equivalent to the formula** (by the summed
formula `sum_repNumLat_eq_prod_localDensity` and the equal size of genera). **Proved** (`RelClassNumber.lean`,
`posClassNumberRelation`, without class field theory: ambiguous ideals and Hilbert 90); `siegel_binaryF_genus'` there is the
unconditional formula.

Sources: Siegel, *Ann. Math.* 36 (1935), Hauptsatz [unverified]; Hanke (2004) (5.3); Shimura (2010) §4 [unverified].
-/

open NumberField Module IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### The genus of the classes -/

theorem genusSym_inv {v : NFPlace F} {x : F} (hx : x ≠ 0) : genusSym E v x⁻¹ = genusSym E v x := by
  have h : x⁻¹ = x * (x⁻¹) ^ 2 := by field_simp
  rw [h, genusSym_mul v hx (pow_ne_zero 2 (inv_ne_zero hx)),
    NFPlace.hilbert_eq_one_of_norm v x⁻¹ 0 (by ring) |> fun h => (show genusSym E v ((x⁻¹) ^ 2) = 1 from h), mul_one]

/-- **The genus vector of $L_{C,\eta}$ is the genus homomorphism of its class:** $\psi_v(\eta/a_C) = \psi_v(\eta^{-1}a_C)$. -/
theorem genusSym_scaleOf (x : PNClass F E × unitQuot F E) (v : NFPlace F) :
    genusSym E v (scaleOf x.1 x.2) = genusHom E (classOf F E x) v := by
  rw [classOf, genusHom_mk]
  show genusSym E v (scaleOf x.1 x.2) =
    genusSym E v ((((x.2.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen x.1 : 𝓞 F) : F)
  have hu := algebraMap_unit_ne_zero (x.2.out : (𝓞 F)ˣ)
  have ha := algebraMap_normGen_ne_zero x.1
  have e : scaleOf x.1 x.2 = ((((x.2.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen x.1 : 𝓞 F) : F)⁻¹ := by
    rw [scaleOf, show ((((x.2.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * normGen x.1 : 𝓞 F) : F) =
      algebraMap (𝓞 F) F ((x.2.out⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * algebraMap (𝓞 F) F (normGen x.1) from map_mul _ _ _,
      algebraMap_inv_unit]
    field_simp
  rw [e, genusSym_inv]
  intro h0
  have := scaleOf_ne_zero x.1 x.2
  rw [e, h0, inv_zero] at this
  exact this rfl

/-- A nonzero representation number forces the genus: if $r_{(L, cN)}(\nu) \ne 0$ ($c, \nu \ne 0$), then $\psi_v(\nu) = \psi_v(c)$. -/
theorem genusSym_eq_of_repNumLat_ne_zero {c ν : F} (hc : c ≠ 0) (hν : ν ≠ 0) {L : Submodule (𝓞 F) E}
    (h : repNumLat (c • normForm F E) L ν ≠ 0) (v : NFPlace F) :
    genusSym E v ν = genusSym E v c := by
  obtain ⟨⟨x, hx⟩⟩ : Nonempty {x : L // (c • normForm F E) x = ν} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h (Nat.card_of_isEmpty)
  have hval : c * Algebra.norm F (x : E) = ν := by
    rw [← hx]; rfl
  have hx0 : (x : E) ≠ 0 := by
    intro h0; rw [h0, Algebra.norm_zero, mul_zero] at hval; exact hν hval.symm
  rw [← hval, genusSym_mul_norm v hc hx0]

open Classical in
/-- **All representations of $\nu$ come from the genus of $\nu$** (every $\nu \ne 0$): summing $r_{L_{C,\eta}}(\nu)$ over the classes $(C,\eta)$ of the
genus $\varphi$ gives the full class sum if $\psi(\nu) = \varphi$ and $0$ otherwise. -/
@[kb "siegel1935" "Hauptsatz (genus by genus) [unverified]; cf. sum_genus_repNum"]
theorem sum_genus_repNumLat {ν : F} (hν : ν ≠ 0) (φ : NFPlace F → ℤ) :
    ∑ x ∈ Finset.univ.filter (fun x : PNClass F E × unitQuot F E => ∀ v, genusSym E v (scaleOf x.1 x.2) = φ v),
      repNumLat (scaleOf x.1 x.2 • normForm F E) (idealLat F (classRep E x.1.1 : Ideal (𝓞 E))) ν =
    if ∀ v, genusSym E v ν = φ v then
      ∑ x : PNClass F E × unitQuot F E,
        repNumLat (scaleOf x.1 x.2 • normForm F E) (idealLat F (classRep E x.1.1 : Ideal (𝓞 E))) ν
    else 0 := by
  rw [Finset.sum_filter]
  split_ifs with hφ
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with hx
    · rfl
    · by_contra hr
      exact hx (fun v => by
        rw [← genusSym_eq_of_repNumLat_ne_zero (scaleOf_ne_zero x.1 x.2) hν (Ne.symm hr) v, hφ])
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs with hx
    · by_contra hr
      exact hφ (fun v => by rw [genusSym_eq_of_repNumLat_ne_zero (scaleOf_ne_zero x.1 x.2) hν hr v, hx])
    · rfl

/-! ### The number of classes in a genus -/

section CM

variable [IsTotallyReal F] [IsTotallyComplex E]

theorem isPos_of_genusHom {g : PairClass F E} (h : ∀ w : InfinitePlace F, genusHom E g (NFPlace.infinite w) = 1) :
    IsPos E g := by
  induction g using Con.induction_on with
  | H p =>
  intro w
  exact (genusSym_infinite_iff w (pair_snd_ne_zero' p)).mp (by rw [← genusHom_mk]; exact h w.1)

open Classical in
/-- **Each genus has as many classes as the principal genus**, in the parametrization: for a genus vector $\varphi$ of totally
positive classes, $\#\{(C,\eta) : \psi(c_{C,\eta}) = \varphi\} = \#\{g \gg 0 : g \text{ in the principal genus}\}$. -/
@[kb "gauss1801" "Art. 252 [unverified]"]
theorem card_genus_eq {φ : NFPlace F → ℤ} {g₀ : PairClass F E} (hg₀ : IsPos E g₀) (hφ : genusHom E g₀ = φ) :
    (Finset.univ.filter (fun x : PNClass F E × unitQuot F E => ∀ v, genusSym E v (scaleOf x.1 x.2) = φ v)).card =
      Nat.card {t : PairClass F E // IsPos E t ∧ genusHom E t = 1} := by
  rw [← card_fiber_eq hg₀, hφ, ← Nat.card_eq_finsetCard]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine Nat.card_congr ((Equiv.ofBijective _ (classOf_bijective (F := F) (E := E))).subtypeEquiv ?_)
  intro x
  simp only [Equiv.ofBijective_apply, genusSym_scaleOf]
  constructor
  · intro h
    have hg : genusHom E (classOf F E x) = φ := funext h
    refine ⟨isPos_of_genusHom (fun w => ?_), hg⟩
    rw [hg, ← hφ]
    induction g₀ using Con.induction_on with
    | H p =>
      rw [genusHom_mk]
      have hw : w.IsReal := IsTotallyReal.isReal w
      exact (genusSym_infinite_iff ⟨w, hw⟩ (pair_snd_ne_zero' p)).mpr (hg₀ ⟨w, hw⟩)
  · rintro ⟨-, h⟩ v; rw [h]

end CM

/-! ### Siegel's formula genus by genus -/

section Siegel

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Input: the number of totally positive proper classes of normalized binary lattices** ($K$ CM, $t$ = number of ramified
primes of $K^+$ in $K$): $\#G^+\cdot Q_K\,h_{K^+}\,2^t = 2\cdot2^{t-1}\,h_K$ (natural-number $t - 1$). A class-field-theory statement
(norm map $\mathrm{Cl}_K \to \mathrm{Cl}^+_{K^+}$, Hasse's unit index); over $\mathbb Q$, $h^+(D) = h(D)$. *Not* definitionally the conclusion
of `siegel_binaryF_genus`, but mathematically equivalent to it given the proved summed formula (see the module docstring).
**Proved** in `RelClassNumber.lean`: `posClassNumberRelation` (`RelClassNumber.lean`). -/
structure PosClassNumberRelation : Prop where
  card_eq : ∀ T : Finset (HeightOneSpectrum (𝓞 K⁺)), (∀ 𝔭, 𝔭 ∈ T ↔ relChar K 𝔭 = 0) →
    (Nat.card {g : PairClass K⁺ K // IsPos K g} : ℝ) * IsCMField.indexRealUnits K * classNumber K⁺ * 2 ^ T.card =
      2 * 2 ^ (T.card - 1) * classNumber K

variable {K}

/-- Positive classes have trivial genus characters off the ramified primes. -/
theorem genusHom_eq_one_off {T : Finset (HeightOneSpectrum (𝓞 K⁺))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar K 𝔭 = 0)
    {g : PairClass K⁺ K} (hg : IsPos K g) (v : NFPlace K⁺) (hv : ∀ 𝔭 ∈ T, v ≠ NFPlace.finite 𝔭) :
    genusHom K g v = 1 := by
  have hmem : genusHom K g ∈ (fun (x : K⁺) v => genusSym K v x) '' posNormValues K := by
    rw [← image_genusHom_eq]; exact ⟨g, hg, rfl⟩
  exact ((mem_genusVectors_iff hT _).mp hmem).1 v hv

theorem genusHom_eq_one_or (g : PairClass K⁺ K) (v : NFPlace K⁺) : genusHom K g v = 1 ∨ genusHom K g v = -1 := by
  induction g using Con.induction_on with
  | H p => rw [genusHom_mk]; exact genusSym_eq_one_or _ _

theorem isPos_one : IsPos K (1 : PairClass K⁺ K) := by
  intro w
  show 0 < Siegel.realEmb w (((1 : 𝓞 K⁺)) : K⁺)
  simp

open Classical in
/-- **Siegel's formula for $n = 2$ over $F = K^+$, genus by genus** ($K$ CM; conditional on `PosClassNumberRelation K`). For an
$\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$, the genus $\mathcal G$ of a totally positive class $g_0$ (vector $\varphi$), the ramified primes $T$,
$\lambda = L(1,\chi_{K/K^+})$, and $\nu \gg 0$ divisible only by good primes of $Q_b$:
$$\frac{1}{\#\mathcal G}\sum_{(C,\eta) \in \mathcal G} r_{L_{C,\eta}}(\nu) = \tfrac12\,|d_{K^+}|^{-1/2}\beta_\infty(\nu)\lambda^{-1}
\prod_{\mathfrak p \in T}\bigl(1 + \psi_\mathfrak p(\nu)\varphi_\mathfrak p\bigr)\prod_{\mathfrak p \mid \nu}\frac{\beta_\mathfrak p(Q_b,\nu)}{1 - \chi(\mathfrak p)N\mathfrak p^{-1}}.$$
The factors $1 + \psi_\mathfrak p(\nu)\varphi_\mathfrak p \in \{0, 2\}$ stand for the local densities $\beta^{\mathcal G}_\mathfrak p(\nu)$ at the ramified primes ($\nu$ a
$\mathfrak p$-unit), their classical values; they are not computed as local densities here. -/
@[kb "siegel1935" "Hauptsatz (n = 2) [unverified]; hanke2004 (5.3); shimura2010 §4 [unverified]"]
theorem siegel_binaryF_genus (hrel : PosClassNumberRelation K) (b : Basis (Fin 2) (𝓞 K⁺) (𝓞 K)) {lam : ℝ}
    (hlam : Tendsto (relLR K⁺ K) (𝓝[>] 1) (𝓝 lam))
    {T : Finset (HeightOneSpectrum (𝓞 K⁺))} (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar K 𝔭 = 0)
    {g₀ : PairClass K⁺ K} (hg₀ : IsPos K g₀)
    {ν : 𝓞 K⁺} (hν : ν ≠ 0) (hpos : ∀ w : Siegel.RealPlace K⁺, 0 < Siegel.realEmb w (ν : K⁺))
    (hgood : ∀ 𝔭 : HeightOneSpectrum (𝓞 K⁺), ν ∈ 𝔭.asIdeal → Siegel.IsGoodPrimeNF (normFormBasis b) 𝔭) :
    ((∑ x ∈ Finset.univ.filter
        (fun x : PNClass K⁺ K × unitQuot K⁺ K => ∀ v, genusSym K v (scaleOf x.1 x.2) = genusHom K g₀ v),
        repNumLat (scaleOf x.1 x.2 • normForm K⁺ K) (idealLat K⁺ (classRep K x.1.1 : Ideal (𝓞 K)))
          (algebraMap (𝓞 K⁺) K⁺ ν) : ℕ) : ℝ) /
      (Finset.univ.filter
        (fun x : PNClass K⁺ K × unitQuot K⁺ K => ∀ v, genusSym K v (scaleOf x.1 x.2) = genusHom K g₀ v)).card =
    (1 / 2 : ℝ) * |(discr K⁺ : ℝ)| ^ (-(1 / 2 : ℝ)) * Siegel.betaInfNF (normFormBasis b) (ν : K⁺) / lam *
      (∏ 𝔭 ∈ T, (1 + (genusSym K (NFPlace.finite 𝔭) (ν : K⁺) : ℝ) * (genusHom K g₀ (NFPlace.finite 𝔭) : ℝ))) *
      ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K⁺),
        (if ν ∈ 𝔭.asIdeal then
          NF.localDensity 𝔭 (normFormBasis b) ν / (1 - (relChar K 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ))
        else 1) := by
  have : Finite (NormOneUnits K⁺ K) := finite_normOneUnits
  set φ := genusHom K g₀
  set S := Finset.univ.filter
    (fun x : PNClass K⁺ K × unitQuot K⁺ K => ∀ v, genusSym K v (scaleOf x.1 x.2) = φ v)
  set R : PNClass K⁺ K × unitQuot K⁺ K → ℕ := fun x =>
    repNumLat (scaleOf x.1 x.2 • normForm K⁺ K) (idealLat K⁺ (classRep K x.1.1 : Ideal (𝓞 K)))
      (algebraMap (𝓞 K⁺) K⁺ ν)
  set P := ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K⁺),
    (if ν ∈ 𝔭.asIdeal then
      NF.localDensity 𝔭 (normFormBasis b) ν / (1 - (relChar K 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ))
    else 1)
  have hνF : (ν : K⁺) ≠ 0 := by exact_mod_cast hν
  -- the summed formula
  have hTot : ((∑ x, R x : ℕ) : ℝ) = (Units.torsionOrder K : ℝ) * P := by
    have h := sum_repNumLat_eq_prod_localDensity (F := K⁺) (E := K) b hν hgood
    rw [← Fintype.sum_prod_type'] at h
    rw [h, card_normOneUnits]
  rw [siegelConstant_binaryF_basis b (ν : K⁺) hlam]
  have hsum := sum_genus_repNumLat (E := K) (F := K⁺) hνF φ
  have hS : (S.card : ℝ) = Nat.card {t : PairClass K⁺ K // IsPos K t ∧ genusHom K t = 1} := by
    exact_mod_cast card_genus_eq hg₀ rfl
  have hG := card_posClasses_eq (F := K⁺) (E := K) hT
  have hr := hrel.card_eq T hT
  have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast Units.torsionOrder_ne_zero K
  have hh : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos (K := K)).ne'
  by_cases hφ : ∀ v, genusSym K v (ν : K⁺) = φ v
  · rw [if_pos hφ] at hsum
    change ((∑ x ∈ S, R x : ℕ) : ℝ) / S.card = _
    rw [hsum, hTot, hS]
    have hprod : ∏ 𝔭 ∈ T, (1 + (genusSym K (NFPlace.finite 𝔭) (ν : K⁺) : ℝ) * (φ (NFPlace.finite 𝔭) : ℝ)) =
        2 ^ T.card := by
      rw [Finset.prod_congr rfl (fun 𝔭 _ => by
        rw [hφ]
        rcases genusHom_eq_one_or g₀ (NFPlace.finite 𝔭) with h | h <;> (rw [show φ = genusHom K g₀ from rfl, h]; norm_num)
        : ∀ 𝔭 ∈ T, (1 + (genusSym K (NFPlace.finite 𝔭) (ν : K⁺) : ℝ) * (φ (NFPlace.finite 𝔭) : ℝ)) = 2),
        Finset.prod_const]
    rw [hprod]
    set k := Nat.card {t : PairClass K⁺ K // IsPos K t ∧ genusHom K t = 1}
    have hk : (k : ℝ) * IsCMField.indexRealUnits K * classNumber K⁺ * 2 ^ T.card = 2 * classNumber K := by
      rw [hG] at hr
      push_cast at hr
      have h2 : (2 : ℝ) ^ (T.card - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hr
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0
      rw [h0] at hk
      simp at hk
      exact hh (by exact_mod_cast hk)
    field_simp
    linear_combination (-P) * hk
  · rw [if_neg hφ] at hsum
    change ((∑ x ∈ S, R x : ℕ) : ℝ) / S.card = _
    rw [hsum, Nat.cast_zero, zero_div]
    by_cases hP : P = 0
    · rw [hP, mul_zero]
    · -- some class represents ν; its genus is that of ν
      have hTot0 : (∑ x, R x) ≠ 0 := by
        intro h0
        have := hTot
        rw [h0, Nat.cast_zero] at this
        exact hP ((mul_eq_zero.mp this.symm).resolve_left hw)
      obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hTot0
      have hgx : ∀ v, genusSym K v (ν : K⁺) = genusHom K (classOf K⁺ K x) v := fun v => by
        rw [← genusSym_scaleOf]; exact genusSym_eq_of_repNumLat_ne_zero (scaleOf_ne_zero _ _) hνF hx v
      have hposx : IsPos K (classOf K⁺ K x) := isPos_of_genusHom (fun w => by
        rw [← hgx]
        have hw : w.IsReal := IsTotallyReal.isReal w
        exact (genusSym_infinite_iff ⟨w, hw⟩ hνF).mpr (hpos ⟨w, hw⟩))
      push Not at hφ
      obtain ⟨v, hv⟩ := hφ
      have hvT : ∃ 𝔭 ∈ T, v = NFPlace.finite 𝔭 := by
        by_contra hno
        push Not at hno
        apply hv
        rw [hgx, genusHom_eq_one_off hT hposx v hno]
        exact (genusHom_eq_one_off hT hg₀ v hno).symm
      obtain ⟨𝔭, h𝔭, rfl⟩ := hvT
      rw [Finset.prod_eq_zero h𝔭, mul_zero, zero_mul]
      rcases genusSym_eq_one_or (E := K) (NFPlace.finite 𝔭) (ν : K⁺) with h1 | h1 <;>
      rcases genusHom_eq_one_or g₀ (NFPlace.finite 𝔭) with h2 | h2 <;>
      · simp only [φ] at hv ⊢
        simp only [h1, h2] at hv ⊢
        all_goals first | exact absurd rfl hv | norm_num

end Siegel

end QuadFormsKB.Binary.Rel
