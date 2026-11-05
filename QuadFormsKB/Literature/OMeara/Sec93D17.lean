/-
# O'Meara §93D, Example 93:17: binary unimodular lattices from the discriminant

**Setting** (as in `Sec93DUni.lean`): $R$ a Henselian discrete valuation ring with finite residue field, $F$ its
fraction field, $2 \in F^\times$, $F$ dyadic ($2$ not a unit of $R$); $(V, Q)$ a quadratic space over $F$, O'Meara's
$B$ = `bil Q`, lattices = `Submodule R V`; $A(\alpha, \beta)$ is the matrix `matA α β`.

**Proves** (O'Meara 1963, §93D, p. 259; page image read: "let $a$ be a norm generator of $L$ that is in $Q(L)$, let
$b$ be a weight generator of $L$, let the discriminant $dL$ be written in the form $dL = -(1+\alpha)$ with
$\mathfrak d(1 + \alpha) = \alpha\mathfrak o$. We claim that $\alpha a^{-1} \in b\mathfrak o$ and
$L \cong A(a, -\alpha a^{-1})$"):
* `omeara93_17`: **Example 93:17**;
* `omeara93_17_hasMatrixA`: the same in the form `HasMatrixA` ($-\alpha a^{-1}$ is integral).

**Proof** (O'Meara's, with the isometry made explicit): by 93:10, $L \cong A(a, \beta)$ with $\beta \in \mathfrak wL$;
comparing discriminants, $1 - a\beta = \varepsilon^2(1 + \alpha)$ with $\varepsilon$ a unit, so
$\alpha\mathfrak o = \mathfrak d(1 + \alpha) \subseteq a\beta\mathfrak o$ and $\alpha a^{-1} \in \beta\mathfrak o
\subseteq b\mathfrak o$. In the base $x, y$ of $A(a, \beta)$ the vector $y' = \frac{1 - \varepsilon^{-1}}{a}x +
\varepsilon^{-1}y$ has $B(x, y') = 1$ and $Q(y') = -\alpha a^{-1}$, so $M = \mathfrak ox + \mathfrak oy' \cong
A(a, -\alpha a^{-1})$ is a lattice on $FL$. It has the norm generator $a$ and the same weight as $L$: if
$\mathfrak wL = 2\mathfrak o$ both weights are $2\mathfrak o$; otherwise $\operatorname{ord} a + \operatorname{ord}\beta$
is odd, $|a| \ge |\beta| > |2|$, and 63:5 gives $\mathfrak d(1 - a\beta) = a\beta\mathfrak o$, so $\alpha\mathfrak o =
a\beta\mathfrak o$. Hence $\mathfrak gM = \mathfrak gL$ and $L \cong M$ by 93:16 (`Eng93.exists_basis_gram_of_normGroup_eq`).

**Conventions.** O'Meara's "$a$ a norm generator in $Q(L)$" is $a = Q(x)$ with $x \in L$; "$dL = -(1+\alpha)$" is the
existence of a base of $L$ with discriminant $-(1+\alpha)$ (discriminants of bases differ by squares of units);
"$L$ on $V$" is `finrank F V = 2`. The conclusion gives a base of $L$ with matrix $A(a, -\alpha a^{-1})$; it does not
say that its first vector is $x$.
-/
import QuadFormsKB.Literature.OMeara.Sec93DEng
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Literature.OMeara.Sec94

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace D17

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- $2(\mathfrak o) = 2\mathfrak o$ as $R$-submodules of $F$. -/
theorem two_smul_one : (2 : F) • (1 : Submodule R F) = R ∙ (2 : F) := by
  rw [Submodule.one_eq_span, Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]

/-- **Example 93:17** (O'Meara 1963, §93D, p. 259): let $L$ be a binary unimodular lattice on the quadratic space $V$
($\dim V = 2$) over a dyadic local field, let $a = Q(x)$, $x \in L$, be a norm generator of $L$, let $b$ be a weight
generator of $L$, and let $dL = -(1 + \alpha)$ (a base of $L$ has discriminant $-(1+\alpha)$, $\alpha \in \mathfrak o$)
with quadratic defect $\mathfrak d(1 + \alpha) = \alpha\mathfrak o$. Then $\alpha a^{-1} \in b\mathfrak o$ and
$L \cong A(a, -\alpha a^{-1})$: $L$ has a base with matrix
$\begin{pmatrix} a & 1 \\ 1 & -\alpha a^{-1}\end{pmatrix}$. -/
@[kb "omeara1963" "§93D, 93:17, p. 259"]
theorem omeara93_17 [FiniteDimensional F V] (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : finrank R L = 2) (hV : finrank F V = 2) {x : V} (hx : x ∈ L)
    (ha : IsNormGenerator Q L (Q x)) {b : F} (hb : IsWeightGenerator Q L b) {α : R}
    (hd : ∃ e : Basis (Fin 2) R L, (gram Q fun i => (e i : V)).det = -(1 + algebraMap R F α))
    (hdef : quadDefect R (1 + algebraMap R F α) = R ∙ algebraMap R F α) :
    algebraMap R F α * (Q x)⁻¹ ∈ R ∙ b ∧
      ∃ e : Basis (Fin 2) R L,
        gram Q (fun i => (e i : V)) = matA (Q x) (-(algebraMap R F α) * (Q x)⁻¹) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj := IsFractionRing.injective R F
  have hne : L ≠ ⊥ := by rintro rfl; simp at hrk
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 : Q x ≠ 0 := ha.ne_zero Q hreg hne
  obtain ⟨a₀, ha₀⟩ := a10_mem_one Q hU hx hx
  rw [bil_self] at ha₀
  have haR : IsNormGenerator Q L (algebraMap R F a₀) := by rw [ha₀]; exact ha
  have ha₀0 : algebraMap R F a₀ ≠ 0 := by rw [ha₀]; exact ha0
  obtain ⟨β, hβw, -, bs, hbs0, hbs⟩ := exists_hasMatrixA Q h2p hfg hU hrk hx ha₀.symm ha
  -- the discriminant: `a β - 1 = -ε² (1 + α)`
  obtain ⟨e₀, he₀⟩ := hd
  obtain ⟨ε, hε, hdet⟩ := exists_unit_det_gram Q e₀ bs
  have hdetA : (gram Q fun i => (bs i : V)).det = algebraMap R F a₀ * algebraMap R F β - 1 := by
    rw [hbs, matA, Matrix.det_fin_two_of]; ring
  obtain ⟨ε', hεε'⟩ := hε.exists_right_inv
  have hεF : algebraMap R F ε * algebraMap R F ε' = 1 := by rw [← map_mul, hεε', map_one]
  have hrel : algebraMap R F a₀ * algebraMap R F β - 1 =
      -(algebraMap R F ε ^ 2 * (1 + algebraMap R F α)) := by
    rw [← hdetA, hdet, he₀]; ring
  -- `α 𝔬 ⊆ a β 𝔬`: `α = c a₀ β`
  have hkey : (1 + algebraMap R F α) - algebraMap R F ε' ^ 2 =
      -(algebraMap R F ε' ^ 2 * algebraMap R F a₀ * algebraMap R F β) := by
    linear_combination (algebraMap R F ε' ^ 2) * hrel -
      (1 + algebraMap R F α) * (algebraMap R F ε * algebraMap R F ε' + 1) * hεF
  have hα_mem : algebraMap R F α ∈ span R {(1 + algebraMap R F α) - algebraMap R F ε' ^ 2} := by
    have h1 : algebraMap R F α ∈ quadDefect R (1 + algebraMap R F α) := by
      rw [hdef]; exact mem_span_singleton_self _
    rw [quadDefect, Submodule.mem_iInf] at h1
    exact h1 _
  rw [hkey] at hα_mem
  obtain ⟨r, hr⟩ := mem_span_singleton.mp hα_mem
  set c : R := -(r * ε' ^ 2) with hc
  have hαc : α = c * a₀ * β := hinj (by
    rw [← hr, Algebra.smul_def]; simp only [hc, map_mul, map_neg, map_pow]; ring)
  -- `β` is not a unit: `𝔴L ⊆ 𝔭`
  have hbw : R ∙ b < scale Q L := weight_gen_lt_scale Q h2p hπ hreg hne ha hb
  have hβb : algebraMap R F β ∈ R ∙ b := hb ▸ hβw
  have hβnu : ¬ IsUnit β := by
    intro hu
    apply hbw.not_ge
    rw [hU.2.1]
    intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_one.mp hz
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : algebraMap R F t = (t * v) • algebraMap R F β := by
      rw [Algebra.smul_def, ← map_mul, mul_assoc, hv, mul_one]
    rw [this]; exact smul_mem _ _ hβb
  have hβm : β ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hβnu
  have hαm : α ∈ maximalIdeal R := by rw [hαc]; exact Ideal.mul_mem_left _ _ hβm
  have hbn : R ∙ b ≤ R ∙ Q x := weight_gen_le_norm_gen Q ha hb
  -- first claim
  have hγF : algebraMap R F α * (Q x)⁻¹ = algebraMap R F (c * β) := by
    rw [hαc, ← ha₀]; simp only [map_mul]; field_simp
  refine ⟨by rw [hγF, map_mul, ← Algebra.smul_def]; exact smul_mem _ _ hβb, ?_⟩
  set γ₀ : R := -(c * β) with hγ₀
  have hγ₀F : algebraMap R F γ₀ = -(algebraMap R F α) * (Q x)⁻¹ := by
    rw [neg_mul, hγF, hγ₀, map_neg]
  -- the explicit vector `y'`
  set y : V := (bs 1 : V) with hy
  have hxy : bil Q x y = 1 := by
    have := congrFun (congrFun hbs 0) 1
    simpa [gram, matA, hbs0] using this
  have hQy : Q y = algebraMap R F β := by
    have := congrFun (congrFun hbs 1) 1
    simpa [gram, matA] using this
  set u : F := algebraMap R F ε' with hu
  set s : F := (1 - u) / Q x with hs
  set y' : V := s • x + u • y with hy'
  have hxy' : bil Q x y' = 1 := by
    rw [hy', bil_add_right, bil_smul_right, bil_smul_right, bil_self, hxy, hs]
    field_simp; ring
  rw [ha₀] at hrel
  have hQy' : Q y' = algebraMap R F γ₀ := by
    have key : 1 + u ^ 2 * (Q x * algebraMap R F β - 1) = -algebraMap R F α := by
      linear_combination u ^ 2 * hrel - (1 + algebraMap R F α) * (u * algebraMap R F ε + 1) * hεF
    have e1 : Q y' = (1 + u ^ 2 * (Q x * algebraMap R F β - 1)) / Q x := by
      rw [hy', Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxy, hQy, hs]
      field_simp; ring
    rw [e1, key, hγ₀F]; ring
  -- the lattice `M = 𝔬x + 𝔬y'`
  let v : Fin 2 → V := ![x, y']
  let G : Matrix (Fin 2) (Fin 2) R := !![a₀, 1; 1, γ₀]
  have hGA : G.map (algebraMap R F) = matA (algebraMap R F a₀) (algebraMap R F γ₀) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [G, matA]
  have hgram : gram Q v = G.map (algebraMap R F) := by
    rw [hGA]
    ext i j; fin_cases i <;> fin_cases j <;> simp [v, gram, matA, hQy', ha₀, hxy', bil_comm Q y' x]
  have hGdet : G.det = -(1 + α) := by
    rw [Matrix.det_fin_two_of]
    have : a₀ * γ₀ = -α := by rw [hγ₀, hαc]; ring
    rw [this]; ring
  have hGu : IsUnit G.det := by rw [hGdet]; exact (isUnit_one_add_aux hαm).neg
  have hdetv : (gram Q v).det ≠ 0 := by
    rw [hgram, show (G.map (algebraMap R F)).det = algebraMap R F G.det from (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ hinj).2 hGu.ne_zero
  have hli : LinearIndependent F v := linearIndependent_of_det_gram_ne_zero (R := F) Q hdetv
  let e : Basis (Fin 2) F V := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have he : ∀ i, e i = v i := fun i => by simp [e]
  have hgram' : gram Q (fun i => e i) = G.map (algebraMap R F) := by
    rw [← hgram]; congr 1; funext i; exact he i
  -- `L` is a lattice on `V`
  have hdetbs : (gram Q fun i => (bs i : V)).det ≠ 0 := by
    rw [hdetA, ha₀, hrel]
    refine neg_ne_zero.2 (mul_ne_zero (pow_ne_zero 2 (alg_ne_zero_of_unit hε)) ?_)
    rw [← map_one (algebraMap R F), ← map_add]
    exact (map_ne_zero_iff _ hinj).2 (isUnit_one_add_aux hαm).ne_zero
  obtain ⟨e₁, he₁⟩ := Eng93.basisF_of_lattice Q bs hdetbs hV
  have hspan := Eng93.span_eq_top_of_basis bs e₁ he₁
  refine (Eng93.exists_basis_gram_of_normGroup_eq Q hfg hU hspan e hGu hgram' ?_).imp fun b' hb' => ?_
  swap
  · rw [hb', hGA, ha₀, hγ₀F]
  -- the norm groups agree
  set M := span R (Set.range e) with hM
  obtain ⟨hMU, hMfg, -, bM, hbM⟩ := Eng93.span_basis_props Q e hGu hgram'
  have hxM : x ∈ M := subset_span ⟨0, by rw [he]; rfl⟩
  have hy'M : y' ∈ M := subset_span ⟨1, by rw [he]; rfl⟩
  have hMne : M ≠ ⊥ := fun h => by
    have : x = 0 := by rw [h] at hxM; exact (Submodule.mem_bot R).mp hxM
    exact ha0 (by rw [this, map_zero])
  have hMreg : IsRegular Q M := IsModular.isRegular Q hMU hMfg
  have hsc : scale Q M = scale Q L := by rw [hMU.2.1, hU.2.1]
  have h2a : (2 : F) • scale Q L ≤ R ∙ Q x := (weight_bounds Q L).2.2.1.trans (hb ▸ hbn)
  have hγa : algebraMap R F γ₀ ∈ R ∙ Q x := by
    rw [hγ₀, map_neg, map_mul, ← Algebra.smul_def]
    exact neg_mem (smul_mem _ _ (hbn hβb))
  have haM : IsNormGenerator Q M (Q x) := by
    refine ⟨Q_mem_normGroup Q hxM, le_antisymm ((span_singleton_le_iff_mem _ _).2 (Q_mem_normIdeal Q hxM)) ?_⟩
    rw [hM, normIdeal_span, ← hM, hsc]
    refine sup_le ?_ h2a
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp only [he, v]; exact mem_span_singleton_self _
    · simp only [he, v]; simpa [hQy'] using hγa
  have haMR : IsNormGenerator Q M (algebraMap R F a₀) := by rw [ha₀]; exact haM
  have hbMg : gram Q (fun i => (bM i : V)) = matA (algebraMap R F a₀) (algebraMap R F γ₀) := by
    rw [← hGA, ← hgram']; congr 1; funext i; exact hbM i
  have hwL := weight_eq_of_matA Q h2p hreg hne haR hβw bs hbs
  have hwEq : weight Q M = weight Q L := by
    by_cases hcase : (2 : F) • scale Q L < weight Q L
    · have hβgen : IsWeightGenerator Q L (algebraMap R F β) :=
        isWeightGenerator_of_matA Q h2p hfg hU haR hβw bs hbs hcase
      have hβ0 : algebraMap R F β ≠ 0 := weight_gen_ne_zero Q haR ha₀0 hβgen
      have hβ0R : β ≠ 0 := fun h => hβ0 (by rw [h, map_zero])
      have ha₀0R : a₀ ≠ 0 := fun h => ha₀0 (by rw [h, map_zero])
      have hodd : ¬ Even (dord hπ (algebraMap R F a₀) + dord hπ (algebraMap R F β)) := fun hev => by
        have h := weight_gen_eq_of_even Q h2p hπ hreg hne haR hβgen hev
        rw [← hβgen, h] at hcase
        exact lt_irrefl _ hcase
      -- orders: `ord a ≤ ord β < ord 2`
      have h2F : (2 : F) ≠ 0 := two_ne_zero
      have hle1 : dord hπ (algebraMap R F a₀) ≤ dord hπ (algebraMap R F β) :=
        (mem_span_iff hπ hβ0 ha₀0).1 (by rw [ha₀]; exact hbn hβb)
      have hlt2 : dord hπ (algebraMap R F β) < dord hπ (2 : F) := by
        by_contra hge
        push Not at hge
        have hmem : algebraMap R F β ∈ R ∙ (2 : F) := (mem_span_iff hπ hβ0 h2F).2 hge
        rw [← hβgen, hU.2.1, two_smul_one] at hcase
        exact hcase.not_ge ((span_singleton_le_iff_mem _ _).2 hmem)
      -- `-(a₀ β) = π^n w`
      have hz : -(a₀ * β) ≠ 0 := neg_ne_zero.2 (mul_ne_zero ha₀0R hβ0R)
      obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hπ
      set z : F := algebraMap R F (π ^ n * ↑w) with hzdef
      have hzF : z = -(algebraMap R F a₀ * algebraMap R F β) := by
        rw [hzdef, mul_comm, ← hw]; simp
      have hz0 : z ≠ 0 := by rw [hzF]; exact neg_ne_zero.2 (mul_ne_zero ha₀0 hβ0)
      have hdz : dord hπ z = n := dord_eq hπ w.isUnit (by rw [hzdef]; simp [zpow_natCast]; ring)
      have hdz' : dord hπ z = dord hπ (algebraMap R F a₀) + dord hπ (algebraMap R F β) := by
        rw [hzF, dord_neg hπ (mul_ne_zero ha₀0 hβ0), dord_mul hπ ha₀0 hβ0]
      have hnodd : Odd n := by
        rw [Int.not_even_iff_odd] at hodd
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k.toNat, by omega⟩
      have h4F : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2F h2F
      have hd4 : dord hπ (4 : F) = 2 * dord hπ (2 : F) := by
        rw [show (4 : F) = 2 ^ 2 by norm_num, dord_sq hπ h2F]
      have h4 : span R {(4 : F)} < span R {z} := by
        refine lt_of_le_of_ne ((span_singleton_le_iff_mem _ _).2 ((mem_span_iff hπ h4F hz0).2 (by omega))) ?_
        intro heq
        have : z ∈ span R {(4 : F)} := heq ▸ mem_span_singleton_self z
        have := (mem_span_iff hπ hz0 h4F).1 this
        omega
      have hd1 := quadDefect_one_add (F := F) (two_ne_zero_R (R := R) (F := F)) hπ w.isUnit hnodd h4
      rw [← hzdef] at hd1
      -- `1 + α = ε'² (1 + z)`
      have hrel2 : 1 + algebraMap R F α = algebraMap R F ε' ^ 2 * (1 + z) := by
        rw [hzF, ha₀]
        linear_combination (algebraMap R F ε' ^ 2) * hrel -
          (1 + algebraMap R F α) * (algebraMap R F ε * algebraMap R F ε' + 1) * hεF
      have hdef2 := hdef
      rw [hrel2, quadDefect_sq_mul, hd1, Submodule.span_mul_span, Set.singleton_mul_singleton] at hdef2
      have hmem : algebraMap R F ε' ^ 2 * z ∈ R ∙ algebraMap R F α := hdef2 ▸ mem_span_singleton_self _
      obtain ⟨t, ht⟩ := mem_span_singleton.mp hmem
      have htR : t * α = ε' ^ 2 * (π ^ n * ↑w) := hinj (by
        rw [map_mul, ← Algebra.smul_def, ht, hzdef]; simp)
      have htR' : t * (c * a₀ * β) = ε' ^ 2 * (-(a₀ * β)) := by rw [← hαc, htR, hw]; ring
      have htc : t * c = -(ε' ^ 2) := by
        have h0 : (t * c + ε' ^ 2) * (a₀ * β) = 0 := by linear_combination htR'
        have := (mul_eq_zero.mp h0).resolve_right (mul_ne_zero ha₀0R hβ0R)
        linear_combination this
      have hcu : IsUnit c := by
        refine IsUnit.of_mul_eq_one_right (a := -(t * ε ^ 2)) ?_
        linear_combination (-(ε ^ 2)) * htc + (ε * ε' + 1) * hεε'
      -- `γ₀ 𝔬 = β 𝔬`
      have hγβ : R ∙ algebraMap R F γ₀ = R ∙ algebraMap R F β := by
        obtain ⟨ci, hci⟩ := hcu.exists_left_inv
        apply le_antisymm
        · rw [span_singleton_le_iff_mem, hγ₀, map_neg, map_mul, ← Algebra.smul_def]
          exact neg_mem (smul_mem _ _ (mem_span_singleton_self _))
        · rw [span_singleton_le_iff_mem]
          refine mem_span_singleton.mpr ⟨-ci, ?_⟩
          rw [Algebra.smul_def, hγ₀, map_neg, map_neg, map_mul]
          have : algebraMap R F ci * algebraMap R F c = 1 := by rw [← map_mul, hci, map_one]
          linear_combination (algebraMap R F β) * this
      have hγ0 : algebraMap R F γ₀ ≠ 0 := fun h => by
        rw [h, span_singleton_eq_bot.mpr rfl] at hγβ
        exact hβ0 ((span_singleton_eq_bot (R := R)).mp hγβ.symm)
      have hdγ : dord hπ (algebraMap R F γ₀) = dord hπ (algebraMap R F β) := by
        have h1 := (mem_span_iff hπ hγ0 hβ0).1 (hγβ ▸ mem_span_singleton_self _)
        have h2 := (mem_span_iff hπ hβ0 hγ0).1 (hγβ.symm ▸ mem_span_singleton_self _)
        omega
      have hγw : algebraMap R F γ₀ ∈ weight Q M := by
        refine mem_weight_of_odd Q h2p hπ haMR ha₀0 (by rw [← hQy']; exact Q_mem_normGroup Q hy'M) hγ0 ?_
        rw [hdγ]
        rw [Int.not_even_iff_odd] at hodd
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k - dord hπ (algebraMap R F a₀), by omega⟩
      rw [weight_eq_of_matA Q h2p hMreg hMne haMR hγw bM hbMg, hwL, hγβ, hsc]
    · have hwL2 : (2 : F) • scale Q L = weight Q L := (weight_bounds Q L).2.2.1.eq_of_not_lt hcase
      have hγ2 : algebraMap R F γ₀ ∈ (2 : F) • scale Q M := by
        rw [hsc, hwL2, hγ₀, map_neg, map_mul, ← Algebra.smul_def]
        exact neg_mem (smul_mem _ _ hβw)
      have hγw : algebraMap R F γ₀ ∈ weight Q M := (weight_bounds Q M).2.2.1 hγ2
      rw [weight_eq_of_matA Q h2p hMreg hMne haMR hγw bM hbMg,
        sup_eq_right.2 ((span_singleton_le_iff_mem _ _).2 hγ2), hsc, hwL2]
  have hbM' : IsWeightGenerator Q M b := hb.trans hwEq.symm
  have h1 := normGroup_eq_sq_add Q h2p hreg hne ha hb
  have h2 := normGroup_eq_sq_add Q h2p hMreg hMne haM hbM'
  exact SetLike.coe_injective (h1.trans h2.symm)

/-- **Example 93:17, `HasMatrixA` form**: under the hypotheses of `omeara93_17`, with $a = Q(x) = a_0 \in \mathfrak o$,
the element $-\alpha a^{-1}$ is integral, $-\alpha a^{-1} = \gamma \in \mathfrak o$, and $L \cong A(a_0, \gamma)$. -/
@[kb "omeara1963" "§93D, 93:17, p. 259 (L ≅ A(a, -αa⁻¹))"]
theorem omeara93_17_hasMatrixA [FiniteDimensional F V] (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : finrank R L = 2) (hV : finrank F V = 2) {x : V} (hx : x ∈ L)
    (ha : IsNormGenerator Q L (Q x)) {b : F} (hb : IsWeightGenerator Q L b) {α : R}
    (hd : ∃ e : Basis (Fin 2) R L, (gram Q fun i => (e i : V)).det = -(1 + algebraMap R F α))
    (hdef : quadDefect R (1 + algebraMap R F α) = R ∙ algebraMap R F α) {a₀ : R}
    (hQx : Q x = algebraMap R F a₀) :
    ∃ γ : R, algebraMap R F γ = -(algebraMap R F α) * (Q x)⁻¹ ∧ HasMatrixA Q L a₀ γ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hne : L ≠ ⊥ := by rintro rfl; simp at hrk
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 : Q x ≠ 0 := ha.ne_zero Q hreg hne
  obtain ⟨h1, e, he⟩ := omeara93_17 Q h2p hfg hU hrk hV hx ha hb hd hdef
  have hb1 : R ∙ b ≤ 1 := hU.2.1 ▸ (weight_gen_lt_scale Q h2p hπ hreg hne ha hb).le
  obtain ⟨t, ht⟩ := Submodule.mem_one.mp (hb1 h1)
  refine ⟨-t, by rw [map_neg, ht, neg_mul], ?_, e, by rw [he, map_neg, ht, neg_mul, hQx]⟩
  obtain ⟨e₀, he₀⟩ := hd
  obtain ⟨u, hu, hdu⟩ := Eng93.isUnit_det_of_isUnimodular Q hU e₀
  have hat : a₀ * t = α := IsFractionRing.injective R F (by
    rw [map_mul, ht, ← hQx]; field_simp)
  have : -1 + a₀ * -t = u := IsFractionRing.injective R F (by
    rw [← hdu, he₀, map_add, map_neg, map_one, mul_neg, map_neg, hat]; ring)
  rw [this]; exact hu

end D17

end QuadFormsKB.OMeara

