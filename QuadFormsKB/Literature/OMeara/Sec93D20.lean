/-
# O'Meara §93D, Example 93:20: $\theta(O^+(L)) \supseteq \mathfrak u$ for modular lattices of dimension $\ge 3$

**Setting** as in `Sec93D18Q.lean`: $R$ a Henselian discrete valuation ring with finite residue field, fraction field
$F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField`, $F$ dyadic.
Spinor norms are in the factorization sense of `HasSpinorNorm` (§55).

**Page image read** (O'Meara 1973 printing, p. 262): "93:20. Example. Let $L$ be a modular lattice on the quadratic
space $V$ over the dyadic local field $F$, and suppose that $\dim V \ge 3$. We claim that $\theta(O^+(L)) \supseteq
\mathfrak u$. By scaling $V$ we can assume that $L$ is unimodular. Let $b$ denote any weight generator of $L$. By
examining the different cases in Example 93:18 we see that there is always a maximal vector $y$ in $L$ with
$Q(y) = b$. This vector satisfies $2B(y, L)/Q(y) = 2\mathfrak o/b \subseteq \mathfrak o$, hence the symmetry $\tau_y$
is a unit of $L$ by §91B. So there is always a symmetry in $O(L)$ with spinor norm $bF^{\times 2}$. But $\varepsilon b$
is also a weight generator of $L$, for any $\varepsilon$ in $\mathfrak u$. Hence $\varepsilon \in \theta(O^+(L))$.
Hence $\theta(O^+(L)) \supseteq \mathfrak u$."

**Proves**
* `exists_mem_eq_weight_gen` (the claim "there is always a vector $y$ in $L$ with $Q(y) = b$"): for a unimodular
  lattice of rank $\ge 3$ and any weight generator $b$, $b \in Q(L)$; by 93:18 (ii) and (v) (then $\mathfrak gL =
  Q(L)$) and by 93:18 (iii), (iv) in ranks $4$, $3$;
* `omeara93_20` (**93:20**): for a modular lattice $L$ of rank $\ge 3$, every unit $\varepsilon$ is the spinor norm
  of some $\sigma \in O^+(L)$.

*Remark.* Maximality of $y$ is not needed: $\tau_y \in O(L)$ follows from $2B(L, y) \subseteq Q(y)\mathfrak o$
(`Uni93.symmetry_mem_orthLat_of_dvd`). The scaling step ("we can assume $L$ unimodular") is done by applying the
unimodular case to the form $\alpha^{-1}Q$ ($\mathfrak sL = \alpha\mathfrak o$) and observing that the symmetries of
$Q$ and $\alpha^{-1}Q$ coincide.
-/
import QuadFormsKB.Literature.OMeara.Sec93D18Five

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **"There is always a vector $y$ in $L$ with $Q(y) = b$"** (O'Meara 1963, 93:20, p. 262, "by examining the
different cases in Example 93:18"): let $L$ be a unimodular lattice of rank $\ge 3$ over a dyadic local field and $b$
any weight generator of $L$. Then $Q(y) = b$ for some $y \in L$. -/
@[kb "omeara1963" "§93D, 93:20, p. 262 (Q(y) = b for a weight generator b)"]
theorem exists_mem_eq_weight_gen (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L) {b : F} (hb : IsWeightGenerator Q L b) :
    ∃ y ∈ L, Q y = b := by
  have h2R : (2 : R) ≠ 0 := fun h => two_ne_zero (α := F) (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, -, hρ⟩ := G93.exists_delta (F := F) h2R h2p hπ
  -- with a hyperbolic pair, `𝔤L = Q(L)` contains `b`
  have hyp : (∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1) → ∃ y ∈ L, Q y = b := by
    rintro ⟨x, hx, y, hy, h1, h2, h3⟩
    have hbg : b ∈ (normGroup Q L : Set F) :=
      normGroupIdeal_subset Q L ((weight_bounds Q L).2.1 (hb ▸ mem_span_singleton_self b))
    rw [normGroup_eq_image Q L hU.2.1 hx hy h1 h2 h3] at hbg
    obtain ⟨y', hy', hQ⟩ := hbg
    exact ⟨y', hy', hQ⟩
  obtain ⟨z, hzL, hzn⟩ := exists_isNormGenerator_Q Q hfg
  by_cases hev : Even (dord hπ (Q z) + dord hπ b)
  · exact hyp (Uni93.exists_hyperbolic_pair_of_even Q h2p hπ hfg hU hrk hzn hb hev)
  have hodd : Odd (dord hπ (Q z) + dord hπ b) := Int.not_even_iff_odd.mp hev
  by_cases h5 : 5 ≤ finrank R L
  · exact hyp (omeara93_18_v Q hK h2p hfg hU h5)
  rcases (by omega : finrank R L = 3 ∨ finrank R L = 4) with h3 | h4
  · -- ternary: 93:18 (iv)
    obtain ⟨e₀⟩ := exists_basis (R := R) (F := F) hfg
    let e1 : Basis (Fin 3) R L := e₀.reindex (finCongr h3)
    obtain ⟨u, -, hdet⟩ := Eng93.isUnit_det_of_isUnimodular Q hU e1
    have key := omeara93_18_iv_sub Q hK h2p hπ hfg hU h3 hzn hb hodd ⟨e1, hdet⟩ hρ
    have ext : ∀ {γ c : F}, HasBlk1 Q L b γ c → ∃ y ∈ L, Q y = b := by
      rintro γ c ⟨e, he⟩
      refine ⟨e 0, (e 0).2, ?_⟩
      have := congrFun (congrFun he 0) 0
      simpa [gram, blk1] using this
    rcases key with ⟨hJ, -⟩ | ⟨hK', -⟩
    · exact ext hJ
    · exact ext hK'
  · -- quaternary: 93:18 (iii)
    obtain ⟨α, hd, hdef⟩ := exists_basis_det_one_add Q h2p hfg hU h4
    have key := (omeara93_18_iii_sub Q hK h2p hπ hfg hU h4 hzn hb hodd hd hdef hρ).2
    have ext : ∀ {q s : F}, HasBlk Q L (Q z) q b s → ∃ y ∈ L, Q y = b := by
      rintro q s ⟨e, he⟩
      refine ⟨e 2, (e 2).2, ?_⟩
      have := congrFun (congrFun he 2) 2
      simpa [gram, blk2] using this
    rcases key with ⟨hJ, -⟩ | ⟨hK', -⟩
    · exact ext hJ
    · exact ext hK'

/-- **Example 93:20** (O'Meara 1963, §93D, p. 262): let $L$ be an $\mathfrak a$-modular lattice of rank $\ge 3$ in a
quadratic space $V$ over a dyadic local field. Then $\theta(O^+(L)) \supseteq \mathfrak u$: every unit $\varepsilon$
of $\mathfrak o$ is the spinor norm of some $\sigma \in O^+(L)$ (`HasSpinorNorm`, spinor norms modulo
$F^{\times 2}$).

*Form of the statement.* O'Meara's $L$ is a lattice on $V$ with $\dim V \ge 3$; here $L$ is any modular lattice in
$V$ of rank $\ge 3$ (the proof does not use $FL = V$). The local field is abstract, as in `omeara93_18_iii`. The
non-dyadic analogue is 92:5 (`exists_hasSpinorNorm_of_isModular`); the even-parity case alone is
`Uni93.exists_hasSpinorNorm_unit_of_even`.

*Proof* (O'Meara's): $\mathfrak sL = \alpha\mathfrak o$ and $L$ is unimodular for $\alpha^{-1}Q$ ("by scaling $V$").
For a weight generator $b$ of $L$ for $\alpha^{-1}Q$, both $b$ and $\varepsilon b$ are weight generators, so
$\alpha^{-1}Q(y_1) = b$, $\alpha^{-1}Q(y_2) = \varepsilon b$ with $y_i \in L$ (`exists_mem_eq_weight_gen`). Since
$2 \in b\mathfrak o$ and $B(L, y_i) \subseteq \alpha\mathfrak o$, $2B(L, y_i) \subseteq Q(y_i)\mathfrak o$, so
$\tau_{y_i} \in O(L)$, and $\tau_{y_1}\tau_{y_2} \in O^+(L)$ has spinor norm $Q(y_1)Q(y_2) = \varepsilon(\alpha b)^2$. -/
@[kb "omeara1963" "§93D, 93:20, p. 262"]
theorem omeara93_20 (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {a : Submodule R F} {L : Submodule R V}
    (hfg : L.FG) (hL : IsModular Q a L) (hrk : 3 ≤ finrank R L) {ε : R} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  have hinj := IsFractionRing.injective R F
  obtain ⟨α, hα, rfl⟩ := exists_eq_span_singleton (R := R) (hL.2.1 ▸ scale_fg Q hfg) hL.1
  set Q' : QuadraticForm F V := α⁻¹ • Q with hQ'
  have hU : IsUnimodular Q' L := isUnimodular_smul_of_isModular Q hα hfg hL
  have hα' : α⁻¹ ≠ 0 := inv_ne_zero hα
  obtain ⟨b, hb⟩ := exists_isWeightGenerator Q' h2p hfg hU
  have hne := Uni93.ne_bot_of_isUnimodular Q' hU
  have hreg : IsRegular Q' L := IsModular.isRegular Q' hU hfg
  obtain ⟨z, -, hzn⟩ := exists_isNormGenerator_Q Q' hfg
  have hb0 := weight_gen_ne_zero Q' hzn (hzn.ne_zero Q' hreg hne) hb
  -- `εb` is also a weight generator
  have hεF : algebraMap R F ε ≠ 0 := fun h => hε.ne_zero (hinj (h.trans (map_zero _).symm))
  have hεb : IsWeightGenerator Q' L (algebraMap R F ε * b) := by
    refine Eq.trans ?_ hb
    obtain ⟨ε', hε'⟩ := hε.exists_left_inv
    apply le_antisymm
    · rw [span_singleton_le_iff_mem]
      exact mem_span_singleton.mpr ⟨ε, by rw [Algebra.smul_def]⟩
    · rw [span_singleton_le_iff_mem]
      refine mem_span_singleton.mpr ⟨ε', ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, hε', map_one, one_mul]
  obtain ⟨y₁, hy₁, hQ₁⟩ := exists_mem_eq_weight_gen Q' hK h2p hfg hU hrk hb
  obtain ⟨y₂, hy₂, hQ₂⟩ := exists_mem_eq_weight_gen Q' hK h2p hfg hU hrk hεb
  have hQy : ∀ y : V, Q y = α * Q' y := fun y => by
    rw [hQ', QuadraticMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hα, one_mul]
  -- `2 = t b`
  have h1L : (1 : F) ∈ scale Q' L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q' hb
    (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  rw [Algebra.smul_def] at ht
  -- the two symmetries are units of `L`
  have sym : ∀ {y : V} (c : R), IsUnit c → y ∈ L → Q' y = algebraMap R F c * b →
      ∃ hy : Q y ≠ 0, symmetry Q y hy ∈ orthLat Q L := by
    intro y c hc hyL hQ
    have hcF : algebraMap R F c ≠ 0 := fun h => hc.ne_zero (hinj (h.trans (map_zero _).symm))
    have hy0 : Q y ≠ 0 := by rw [hQy, hQ]; exact mul_ne_zero hα (mul_ne_zero hcF hb0)
    refine ⟨hy0, Uni93.symmetry_mem_orthLat_of_dvd Q hy0 hyL fun l hl => ?_⟩
    have hs : bil Q l y ∈ R ∙ α := by rw [← hL.2.1]; exact bil_mem_scale Q hl hyL
    obtain ⟨r, hr⟩ := mem_span_singleton.mp hs
    rw [Algebra.smul_def] at hr
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    have hc'F : algebraMap R F c' * algebraMap R F c = 1 := by rw [← map_mul, hc', map_one]
    refine mem_span_singleton.mpr ⟨t * r * c', ?_⟩
    rw [Algebra.smul_def, hQy, hQ, ← hr]
    simp only [map_mul]
    linear_combination (algebraMap R F r * α) * ht +
      (algebraMap R F t * algebraMap R F r * α * b) * hc'F
  obtain ⟨h1, hs₁⟩ := sym 1 isUnit_one hy₁ (by rw [hQ₁, map_one, one_mul])
  obtain ⟨h2, hs₂⟩ := sym ε hε hy₂ hQ₂
  refine ⟨symmetry Q y₁ h1 * symmetry Q y₂ h2, ⟨(orthLat Q L).mul_mem hs₁ hs₂,
    symmetry_mul_mem_orthPlus Q h1 h2⟩, ?_⟩
  obtain ⟨l, hl, hσ, s, hs0, hprod⟩ := hasSpinorNorm_symmetry_mul Q h1 h2
  refine ⟨l, hl, hσ, s * (α * b), mul_ne_zero hs0 (mul_ne_zero hα hb0), ?_⟩
  rw [hprod, hQy, hQy, hQ₁, hQ₂]
  ring

end QuadFormsKB.OMeara.D18
