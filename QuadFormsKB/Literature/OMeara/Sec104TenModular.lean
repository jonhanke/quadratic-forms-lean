/-
# O'Meara 104:10, the modular case: modular lattices with the same scale and norm are locally isometric

**Setting.** $F$ is a number field with ring of integers $\mathcal O_F$, $V = F^n$ with the form `Q : QuadForm F n`
(O'Meara's $B$ = `OMeara.bil Q.toQuadraticForm`, $B(x, x) = Q(x)$), and $L, K$ are lattices on $V$ (`Lat F n`). For a
finite spot $\mathfrak p$ (= `v : HeightOneSpectrum (𝓞 F)`), $F_\mathfrak p$ = `v.adicCompletion F`,
$\mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F`, the local space is $V_\mathfrak p = F_\mathfrak p^n$ with the
form $Q_\mathfrak p$ = `qk Q F_𝔭` (equal to `QuadForm.toQuadraticForm (Q.map (algebraMap F F_𝔭))` by
`qk_eq_toQuadraticForm_map`), and $L_\mathfrak p = \mathfrak o_\mathfrak p L$ is `loc v L.1`.

**Proves** (O'Meara 1973, proof of Theorem 104:10, p. 320: "In the modular case we have $\operatorname{gen} L =
\operatorname{gen} K$ by Theorems 92:2 and 93:29"): if $L$ and $K$ are modular lattices on $V$ with
$\mathfrak sL = \mathfrak sK$ and $\mathfrak nL = \mathfrak nK$, then $K_\mathfrak p \in \operatorname{cls} L_\mathfrak p$
* at every non-dyadic spot (`mem_cls_loc_of_isModular_nondyadic`, by 92:2 with one Jordan component), and
* at every 2-adic spot, i.e. $2$ prime in $\mathfrak o_\mathfrak p$ (`mem_cls_loc_of_isModular_twoAdic`, by 93:29 with
  one Jordan component).

Over $\mathbb Q$ every finite spot is one of the two kinds (`isTwoAdic_rat`). Auxiliary results:
`OMeara.isJordanSplitting_single` (a modular lattice is its own Jordan splitting), `isModular_scale_loc`,
`sameDisc_loc` ($dL_\mathfrak p = dK_\mathfrak p$ in $F_\mathfrak p/\mathfrak u^2$ for modular lattices with the same scale).
-/
import QuadFormsKB.Literature.OMeara.Sec104Bridge
import QuadFormsKB.Literature.OMeara.Sec104LocalMod
import QuadFormsKB.Literature.OMeara.Sec102Max
import QuadFormsKB.Literature.OMeara.Sec92Jordan
import QuadFormsKB.Literature.OMeara.Sec93G29Main
import QuadFormsKB.Literature.OMeara.Sec41Extra
import QuadFormsKB.LocalDensity.NFBridge

open NumberField IsDedekindDomain Submodule Module WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **A modular lattice is its own Jordan splitting** (O'Meara 1963, §91C, p. 243, the case $t = 1$): if the lattice
$M$ in the quadratic space $(V, Q)$ over the field of fractions $F$ of the discrete valuation ring $R$ is
$\mathfrak a$-modular for some fractional ideal $\mathfrak a$ (hypothesis `hM : IsModular Q a M`), then $M = M_1$ (the
one-component family `![M]`, $M_1$ = `![M] 0`) is a Jordan splitting of $M$. -/
@[kb "omeara1963" "§91C, p. 243 (a modular lattice is a Jordan splitting with t = 1)"]
theorem isJordanSplitting_single (Q : QuadraticForm F V) {a : Submodule R F} {M : Submodule R V}
    (hM : IsModular Q a M) : IsJordanSplitting Q M ![M] where
  split := ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, iSupIndep_subsingleton _, by simp⟩
  modular i := by
    fin_cases i
    simpa [hM.2.1] using hM
  scale_strictAnti := Subsingleton.strictAnti _

end QuadFormsKB.OMeara

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- **The completion of a modular lattice is $\mathfrak sL_\mathfrak p$-modular** (O'Meara 1963, §82K, p. 239): if the
lattice $L$ on $F^n$ is modular (hypothesis `hL : IsModularLat Q L`), then $L_\mathfrak p$ is
$\mathfrak sL_\mathfrak p$-modular for the local form $Q_\mathfrak p$. -/
theorem isModular_scale_loc {L : Lat F n} (hL : IsModularLat Q L) :
    OMeara.IsModular Qv (OMeara.scale Qv (loc v L.1)) (loc v L.1) := by
  obtain ⟨a, -, hmod⟩ := isModular_loc_of_isModularLat v Q hL
  rw [hmod.2.1]
  exact hmod

/-- **Modular lattices with the same scale have the same local discriminant** (O'Meara 1963, §82B, p. 222, and §92,
proof of 104:10, p. 320): let $L$, $K$ be modular lattices on $F^n$ (hypotheses `hL`, `hK`) with $\mathfrak sL =
\mathfrak sK$ (hypothesis `hs`). Then $dL_\mathfrak p = dK_\mathfrak p$ in $F_\mathfrak p/\mathfrak u^2$
(`OMeara.SameDisc`). Proof: bases $b$, $b'$ of $L_\mathfrak p$, $K_\mathfrak p$ are bases of $V_\mathfrak p$, so
$d(b) = (\det P)^2 d(b')$ for the change of base $P$; both lattices have volume $(\mathfrak sL_\mathfrak p)^n$, so
$d(b) = \eta\, d(b')$ for a unit $\eta$ of $\mathfrak o_\mathfrak p$ and $d(b) \ne 0$; thus $(\det P)^2 = \eta$ is a
unit, and $\det P$ is integral over $\mathfrak o_\mathfrak p$, hence a unit of $\mathfrak o_\mathfrak p$. No
nondegeneracy hypothesis on $Q$ is needed (it follows from modularity). -/
theorem sameDisc_loc {L K : Lat F n} (hL : IsModularLat Q L) (hK : IsModularLat Q K)
    (hs : OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1) :
    OMeara.SameDisc Qv Qv (loc v L.1) (loc v K.1) := by
  have := OMeara.isTorsionFree_of_fractionRing (R := 𝔬) (F := Fv) (V := Fv)
  have := loc_isLattice v L.2
  have := loc_isLattice v K.2
  have hmL := isModular_scale_loc Q v hL
  have hmK := isModular_scale_loc Q v hK
  have hsv : OMeara.scale Qv (loc v L.1) = OMeara.scale Qv (loc v K.1) := by
    rw [scale_loc, scale_loc, hs]
  obtain ⟨b⟩ := OMeara.exists_basis (R := 𝔬) (F := Fv) (loc_fg v L)
  obtain ⟨b'⟩ := OMeara.exists_basis (R := 𝔬) (F := Fv) (loc_fg v K)
  have hr : finrank 𝔬 (loc v K.1) = finrank 𝔬 (loc v L.1) := by rw [finrank_loc, finrank_loc]
  -- equal volumes `(𝔰L_𝔭)^n = (𝔰K_𝔭)^n`, and the volume is non-zero
  have hvol : OMeara.volume Qv (loc v L.1) = OMeara.volume Qv (loc v K.1) := by
    rw [hmL.2.2, hmK.2.2, hsv, hr]
  have hne : OMeara.volume Qv (loc v L.1) ≠ ⊥ := by
    rw [hmL.2.2]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmL.1
    intro h
    have := Submodule.pow_mem_pow _ hx (finrank 𝔬 (loc v L.1))
    rw [h, mem_bot] at this
    exact hx0 (pow_eq_zero_iff'.mp this).1
  rw [OMeara.volume_eq_span_det Qv b, OMeara.volume_eq_span_det Qv b'] at hvol
  rw [OMeara.volume_eq_span_det Qv b] at hne
  have hd0 : (OMeara.gram Qv fun i => (b i : Fin n → Fv)).det ≠ 0 := by
    intro h; rw [h, span_singleton_eq_bot.mpr rfl] at hne; exact hne rfl
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp hvol
  -- the bases as `F_𝔭`-bases of `V_𝔭`, and the change of base
  let e := b.extendOfIsLattice Fv
  let e' := (b'.extendOfIsLattice Fv).reindex (finCongr hr)
  obtain ⟨α, -, hα⟩ := OMeara.det_gram_basis_change Qv e' e
  have he : (OMeara.gram Qv e) = OMeara.gram Qv fun i => (b i : Fin n → Fv) := by
    ext i j; simp [OMeara.gram, e]
  have he' : (OMeara.gram Qv e') = (OMeara.gram Qv fun i => (b' i : Fin n → Fv)).submatrix
      (finCongr hr).symm (finCongr hr).symm := by
    ext i j; simp [OMeara.gram, e']
  rw [he, he', Matrix.det_submatrix_equiv_self, ← hu, Units.smul_def, Algebra.smul_def] at hα
  have hαu : α ^ 2 * algebraMap 𝔬 Fv (u : 𝔬) = 1 := by
    have : (α ^ 2 * algebraMap 𝔬 Fv (u : 𝔬) - 1) * (OMeara.gram Qv fun i => (b i : Fin n → Fv)).det = 0 := by
      linear_combination -hα
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hd0
  -- `α = det P` is integral, hence in `𝔬_𝔭`, and a unit
  have hint : _root_.IsIntegral 𝔬 α := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : α ^ 2 = algebraMap 𝔬 Fv (↑u⁻¹ : 𝔬) := by
      calc α ^ 2 = α ^ 2 * algebraMap 𝔬 Fv ((u : 𝔬) * ↑u⁻¹) := by simp
        _ = algebraMap 𝔬 Fv (↑u⁻¹ : 𝔬) := by rw [map_mul, ← mul_assoc, hαu, one_mul]
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hyu : y ^ 2 * (u : 𝔬) = 1 :=
    IsFractionRing.injective 𝔬 Fv (by rw [map_mul, map_pow, map_one, hαu])
  refine ⟨b, b', y, IsUnit.of_mul_eq_one (y * u) (by linear_combination hyu), ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_pow, ← map_mul, hyu, map_one, one_mul]

/-- **Modular lattices with the same scale and norm are isometric at a non-dyadic spot** (O'Meara 1973, proof of
104:10, p. 320, via Theorem 92:2, p. 247, with $t = 1$). Let $L$, $K$ be modular lattices on $F^n$ (hypotheses `hL`,
`hK`: $L$ is $\mathfrak a$-modular and $K$ is $\mathfrak b$-modular for some fractional ideals) with the same scale
$\mathfrak sL = \mathfrak sK$ (`hs`) and the same norm $\mathfrak nL = \mathfrak nK$ (`hnorm`), and let $\mathfrak p$
(`v`) be a non-dyadic spot ($2$ is a unit of $\mathfrak o_\mathfrak p$, hypothesis `h2`). Then $K_\mathfrak p \in
\operatorname{cls} L_\mathfrak p$ for the local form $Q_\mathfrak p$ = `qk Q F_𝔭`. (The Jordan splittings
$L_\mathfrak p = L_\mathfrak p$, $K_\mathfrak p = K_\mathfrak p$ have the same type and $dL_\mathfrak p = dK_\mathfrak p$
by `sameDisc_loc`; `hnorm` gives the norm condition of the type. No nondegeneracy hypothesis on $Q$ is needed.) -/
@[kb "omeara1963" "§92, 92:2, p. 247 (modular lattices with the same scale on one space)"]
theorem mem_cls_loc_of_isModular_nondyadic (h2 : IsUnit (2 : 𝔬)) {L K : Lat F n} (hL : IsModularLat Q L)
    (hK : IsModularLat Q K)
    (hs : OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1)
    (hnorm : OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1) :
    loc v K.1 ∈ OMeara.cls (qk Q Fv) (loc v L.1) := by
  rw [qk_eq_toQuadraticForm_map]
  have := loc_isLattice v L.2
  have := loc_isLattice v K.2
  have hJL := OMeara.isJordanSplitting_single Qv (isModular_scale_loc Q v hL)
  have hJK := OMeara.isJordanSplitting_single Qv (isModular_scale_loc Q v hK)
  have htype : OMeara.SameJordanType Qv Qv ![loc v L.1] ![loc v K.1] := by
    have e1 : OMeara.scale Qv (loc v L.1) = OMeara.scale Qv (loc v K.1) := by rw [scale_loc, scale_loc, hs]
    have e2 : finrank 𝔬 (loc v L.1) = finrank 𝔬 (loc v K.1) := by rw [finrank_loc, finrank_loc]
    have e3 : OMeara.normIdeal Qv (loc v L.1) = OMeara.normIdeal Qv (loc v K.1) := by
      rw [normIdeal_loc, normIdeal_loc, hnorm]
    refine ⟨rfl, fun i => ?_⟩
    fin_cases i
    exact ⟨e1, e2, e1 ▸ e3 ▸ Iff.rfl⟩
  have hcls := (OMeara.cls_eq_iff_sameDisc Qv h2 hJL hJK htype).mpr fun i j _ => by
    fin_cases i; fin_cases j
    exact sameDisc_loc Q v hL hK hs
  rw [hcls]
  exact OMeara.mem_cls_self _ _

/-- **Modular lattices with the same scale and norm are isometric at a 2-adic spot** (O'Meara 1973, proof of 104:10,
p. 320, via Theorem 93:29, p. 277, with $t = 1$). Let $Q$ be nondegenerate (hypothesis `hQ`), let $L$, $K$ be modular
lattices on $F^n$ (hypotheses `hL`, `hK`) with the same scale $\mathfrak sL = \mathfrak sK$ (`hs`) and the same norm
$\mathfrak nL = \mathfrak nK$ (`hnorm`), and let $\mathfrak p$ (`v`) be a 2-adic spot ($2$ is a prime element of
$\mathfrak o_\mathfrak p$, hypothesis `h2 : IsTwoAdic 𝔬`). Then $K_\mathfrak p \in \operatorname{cls} L_\mathfrak p$ for
the local form $Q_\mathfrak p$ = `qk Q F_𝔭`. (The one-component Jordan splittings have the same Jordan invariants
$t = 1$, $\dim$, $\mathfrak s$, $\mathfrak n$; conditions (i), (ii) of 93:29 concern $1 \le i \le t - 1$ and are
vacuous.) -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (modular lattices with the same scale and norm)"]
theorem mem_cls_loc_of_isModular_twoAdic (hQ : Q.Nondegenerate) (h2 : OMeara.IsTwoAdic 𝔬) {L K : Lat F n}
    (hL : IsModularLat Q L) (hK : IsModularLat Q K)
    (hs : OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1)
    (hnorm : OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1) :
    loc v K.1 ∈ OMeara.cls (qk Q Fv) (loc v L.1) := by
  have hnd : (QuadraticMap.associated (qk Q Fv)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn Fv hQ))
  rw [qk_eq_toQuadraticForm_map] at hnd ⊢
  have := loc_isLattice v L.2
  have := loc_isLattice v K.2
  have hJL := OMeara.isJordanSplitting_single Qv (isModular_scale_loc Q v hL)
  have hJK := OMeara.isJordanSplitting_single Qv (isModular_scale_loc Q v hK)
  have hinv : OMeara.SameJordanInvariants Qv Qv ![loc v L.1] ![loc v K.1] := by
    have e1 : OMeara.scale Qv (loc v L.1) = OMeara.scale Qv (loc v K.1) := by rw [scale_loc, scale_loc, hs]
    have e2 : finrank 𝔬 (loc v L.1) = finrank 𝔬 (loc v K.1) := by rw [finrank_loc, finrank_loc]
    have e3 : OMeara.normIdeal Qv (loc v L.1) = OMeara.normIdeal Qv (loc v K.1) := by
      rw [normIdeal_loc, normIdeal_loc, hnorm]
    refine ⟨rfl, fun i => ?_⟩
    fin_cases i
    exact ⟨e2, e1, e3⟩
  have hcls := ((OMeara.G29.twoAdicClassification_twoAdic_nf v Qv).cls_eq_iff h2 hnd (loc v L.1) (loc v K.1)
    _ _ hJL hJK hinv).mpr fun i j hij => by
      fin_cases i; fin_cases j; simp at hij
  rw [hcls]
  exact OMeara.mem_cls_self _ _

/-- Over $\mathbb Q$, $2 \notin \mathfrak p^2$ for every finite spot $\mathfrak p$ (`v`): otherwise
$(N\mathfrak p)^2 \mid N(2\mathbb Z) = 2$, impossible for $N\mathfrak p \ge 2$. -/
theorem two_notMem_sq_rat (v : HeightOneSpectrum (𝓞 ℚ)) : (2 : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
  intro h
  have hle : Ideal.span {(2 : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).mpr h
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [map_pow, Ideal.absNorm_span_singleton] at hd
  have hn : Algebra.norm ℤ (2 : 𝓞 ℚ) = 2 := by
    rw [show (2 : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) 2 by simp, Algebra.norm_algebraMap, RingOfIntegers.rank,
      Module.finrank_self, pow_one]
  rw [hn] at hd
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h4 := Nat.le_of_dvd (by norm_num) hd
  norm_num at h4
  have : Ideal.absNorm v.asIdeal ≤ 1 := by nlinarith
  omega

/-- **Over $\mathbb Q$ every dyadic spot is 2-adic** (O'Meara 1963, §93G, p. 276: $\mathbb Q_2$ is 2-adic): if
$\mathfrak p$ (`v`) is a finite spot of $\mathbb Q$ at which $2$ is not a unit of $\mathfrak o_\mathfrak p$ (hypothesis
`h2`), then $2$ is a prime element of $\mathfrak o_\mathfrak p$ (`IsTwoAdic`). Proof: $2 \in \mathfrak p$ and
$2 \notin \mathfrak p^2$, so $\operatorname{ord}_\mathfrak p 2 = 1$. Hence `mem_cls_loc_of_isModular_nondyadic` and
`mem_cls_loc_of_isModular_twoAdic` together cover every finite spot of $\mathbb Q$. -/
@[kb "omeara1963" "§93G, p. 276 (over Q the dyadic spot is 2-adic)"]
theorem isTwoAdic_rat (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : ¬ IsUnit (2 : v.adicCompletionIntegers ℚ)) :
    OMeara.IsTwoAdic (v.adicCompletionIntegers ℚ) := by
  have hval := LocalDensity.NF.valued_ι v 2
  rw [map_ofNat] at hval
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hval] at h2
  have hlt : v.intValuation 2 < 1 := lt_of_le_of_ne (v.intValuation_le_one _) h2
  have hmem : (2 : 𝓞 ℚ) ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem _).mp hlt
  have hle1 : v.intValuation 2 ≤ exp (-((1 : ℕ) : ℤ)) := (v.intValuation_le_pow_iff_mem _ 1).mpr (by simpa)
  have hnle2 : ¬ v.intValuation 2 ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    two_notMem_sq_rat v ((v.intValuation_le_pow_iff_mem _ 2).mp h)
  refine LocalDensity.NF.irreducible_of_valued v ?_
  rw [hval]
  have hne : v.intValuation 2 ≠ 0 := v.intValuation_ne_zero _ two_ne_zero
  rw [← exp_log hne] at hle1 hnle2 ⊢
  rw [exp_le_exp] at hle1 hnle2
  rw [exp_inj]
  push_cast at hle1 hnle2
  omega

end QuadFormsKB.Lattices
