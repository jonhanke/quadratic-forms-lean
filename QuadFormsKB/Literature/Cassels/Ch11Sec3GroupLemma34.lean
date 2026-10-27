/-
# Cassels, Chapter 11, §3: Lemma 3.4 and its Corollary

**Layer:** as in `Ch11Sec3Group.lean` ($V = F^n$, $\Lambda$ = `L`, the finite set $P$ of primes with Cassels' condition
(3.7), $\theta(\Lambda_p)$ = `localSpinorNormGroup`, the adelic orthogonal group `OAf Q`).

**Proves** Cassels' Lemma 3.4 (p. 209; `exists_isProperIsometric_casselsForm`) and its Corollary (p. 210;
`exists_sameProperSpinorGenus_casselsForm`), over a number field with $\mathcal O_F$ a principal ideal domain under
Cassels' Lemma 3.2 in the form `hval`, and over $\mathbb Q$ (`…_rat`, $n \ge 3$).
*Proof of Lemma 3.4* (Cassels): write $\Delta = h\Lambda$ with rotations $h_p$ (gen = proper gen); choose $c \in
\theta(V)$ with $c\,\theta(h_p)$ a unit class at every $p$ (principal ideals); take $\gamma \in O^+(V)$ with
$\theta(\gamma) = c$ and $\Upsilon = \gamma\Delta$; at $p \notin P$ replace $\gamma h_p$ by $\gamma h_p\alpha_p^{-1}$
with $\alpha_p \in O^+(\Lambda_p)$, $\theta(\alpha_p) = \theta(\gamma h_p)$ (by (3.7)). *Corollary*: replace
$\beta_p$ by $1$ for $p \notin P$; the two lattices differ by an element of the adelic spinor kernel.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Group

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Helpers -/

section Helpers

variable {Q}

/-- A product of unit square classes is a unit square class. -/
theorem isUnitSqClass_mul' {v : HeightOneSpectrum (𝓞 F)} {c d : SqClass (v.adicCompletion F)}
    (hc : IsUnitSqClass v c) (hd : IsUnitSqClass v d) : IsUnitSqClass v (c * d) := by
  obtain ⟨u, hu, rfl⟩ := hc
  obtain ⟨w, hw, rfl⟩ := hd
  have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
  have hw0 : w ≠ 0 := by rintro rfl; rw [map_zero] at hw; exact zero_ne_one hw
  exact ⟨u * w, by rw [map_mul, hu, hw, one_mul], (sqClassOf_mul hu0 hw0).symm⟩

/-- The spinor norm is multiplicative. -/
theorem spinorNorm_mul_of (hQ : Q.Nondegenerate) (K : Type*) [Field K] [Algebra F K] [CharZero K]
    (a b : orthGroup Q K) : spinorNorm Q K (a * b) = spinorNorm Q K a * spinorNorm Q K b := by
  simpa only [spinorNormHom_apply] using map_mul (spinorNormHom Q K hQ) a b

/-- The spinor norm is compatible with inverses. -/
theorem spinorNorm_inv_of (hQ : Q.Nondegenerate) (K : Type*) [Field K] [Algebra F K] [CharZero K]
    (a : orthGroup Q K) : spinorNorm Q K a⁻¹ = (spinorNorm Q K a)⁻¹ := by
  simpa only [spinorNormHom_apply] using map_inv (spinorNormHom Q K hQ) a

/-- **Core of Lemma 3.4:** $\beta\Lambda = \gamma M$ for a rational rotation $\gamma$ and $\beta$ with the stated
local spinor norms. -/
theorem exists_casselsForm_core [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (hval : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ u : (𝓞 F)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : F) = algebraMap (𝓞 F) F ((u : 𝓞 F) * a₀))
    (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → ∀ u : (v.adicCompletion F)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ γ ∈ Tamagawa.soSub Q F, ∃ β : OAf Q, latSMul Q β L = latSMul Q (diagF Q γ) M ∧
      (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion F)) ∧
      (∀ v ∈ P, IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (β v))) ∧
      (∀ v, v ∉ P → spinorNorm Q (v.adicCompletion F) (β v) = 1) := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨h, hrot, hhM⟩ := exists_oaf_soSub hQ L hM
  subst hhM
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (h v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (Valued.v (xv v))
  let ε : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v % 2).toNat
  have hm : ∀ v, Valued.v (xv v) = WithZero.exp (m v) := fun v =>
    (WithZero.exp_log ((map_ne_zero _).mpr (hxv0 v))).symm
  have hε : ∀ v, ((ε v : ℕ) : ℤ) = m v % 2 := fun v => Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
  have hfin0 : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  -- at `v ∉ P` with `h_v ∈ O(L_v)`, `θ(h_v)` is a unit class
  have hunit : ∀ v, v ∉ P → h v ∈ locStabV Q v L →
      IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (h v)) := by
    intro v hvP hv
    have hz := hxv0 v
    have := (hP v hvP (Units.mk0 (xv v) hz)).mp ((mem_localSpinorNormGroup Q hQ v L).mpr
      ⟨h v, Subgroup.mem_inf.mpr ⟨hv, hrot v⟩, by rw [hxvθ, sqClassOf_of_ne_zero hz]⟩)
    rw [hxvθ, sqClassOf_of_ne_zero hz]
    exact this
  have hfin : {v | ¬ IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (h v))}.Finite := by
    refine (P.finite_toSet.union hfin0).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv (hunit v hc.1 hc.2)
  set S := hfin.toFinset
  have hSmem : ∀ v, v ∉ S → IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (h v)) := by
    intro v hv
    by_contra hc; exact hv (hfin.mem_toFinset.mpr hc)
  -- the global element `a` and `γ` with `θ(γ) = a`
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w with ha₀def
  have ha₀ : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  obtain ⟨u, a, haD, hau⟩ := hval a₀ ha₀
  have hvalue : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a₀) := by
    intro v
    rw [hau, ← IsScalarTower.algebraMap_apply, map_mul, map_mul, valued_unit v u, one_mul]
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-(ε v : ℤ)) := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp haD
  have hγθ' : spinorNorm Q F γ = sqClassOf (a : F) := by
    rw [hγθ, sqClassOf_of_ne_zero ha0]; exact congrArg (SqClass.mk (K := F)) (Units.ext rfl)
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) (a : F)) := fun v => spinorNorm_orthMap_of hQ v γ ha0 hγθ'
  -- `θ(γ_v h_v)` is a unit class everywhere
  have hθ' : ∀ v : HeightOneSpectrum (𝓞 F),
      IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ * h v)) := by
    intro v
    set K := v.adicCompletion F
    have hav : algebraMap F K (a : F) ≠ 0 := (map_ne_zero _).mpr ha0
    rw [spinorNorm_mul_of hQ, hθγ]
    by_cases hvS : v ∈ S
    · rw [hxvθ, ← sqClassOf_mul hav (hxv0 v)]
      refine isUnitSqClass_of_valued_eq v _ (m v / 2) ?_
      rw [map_mul, hva v hvS, hm, ← WithZero.exp_add, hε]
      congr 1
      omega
    · exact isUnitSqClass_mul' ⟨_, hva' v hvS, rfl⟩ (hSmem v hvS)
  -- the correction `α ∈ O(L̂)`
  have hα : ∀ v : HeightOneSpectrum (𝓞 F), ∃ σ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion F),
      (v ∈ P → σ = 1) ∧ (v ∉ P → spinorNorm Q (v.adicCompletion F) σ =
        spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ * h v)) := by
    intro v
    by_cases hvP : v ∈ P
    · exact ⟨1, (locStabV Q v L ⊓ Tamagawa.soSub Q _).one_mem, fun _ => rfl, fun h' => absurd hvP h'⟩
    · obtain ⟨z, hz1, hzc⟩ := hθ' v
      have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz1; exact zero_ne_one hz1
      have hcl : spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ * h v) = SqClass.mk (Units.mk0 z hz0) := by
        rw [hzc, sqClassOf_of_ne_zero hz0]
      obtain ⟨σ, hσ, hσθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp
        ((hP v hvP (Units.mk0 z hz0)).mpr ⟨z, hz1, (sqClassOf_of_ne_zero hz0).symm⟩)
      exact ⟨σ, hσ, fun h' => absurd h' hvP, fun _ => by rw [hσθ, hcl]⟩
  choose σ hσ hσP hσθ using hα
  let α : OAf Q := ⟨σ, by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact (locStabV_eq_stdStab Q v L hv).mp (Subgroup.mem_inf.mp (hσ v)).1⟩
  have hαL : α ∈ locStab Q L := fun v => (Subgroup.mem_inf.mp (hσ v)).1
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), (diagF Q γ * h * α⁻¹) v = orthMap Q _ γ * h v * (σ v)⁻¹ := fun v => rfl
  have hγv : ∀ v : HeightOneSpectrum (𝓞 F), orthMap Q (v.adicCompletion F) γ ∈ Tamagawa.soSub Q (v.adicCompletion F) :=
    fun v => orthMap_mem_soSub Q _ hγ
  refine ⟨γ, hγ, diagF Q γ * h * α⁻¹, ?_, ?_, ?_, ?_⟩
  · have huL : latSMul Q α⁻¹ L = L :=
      MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ (locStab Q L).inv_mem hαL)
    change (diagF Q γ * h * α⁻¹) • L = diagF Q γ • (h • L)
    rw [mul_smul, mul_smul]
    change diagF Q γ • (h • latSMul Q α⁻¹ L) = _
    rw [huL]
  · intro v
    rw [hβv]
    exact (Tamagawa.soSub Q _).mul_mem ((Tamagawa.soSub Q _).mul_mem (hγv v) (hrot v))
      ((Tamagawa.soSub Q _).inv_mem (Subgroup.mem_inf.mp (hσ v)).2)
  · intro v hv
    rw [hβv, spinorNorm_mul_of hQ, spinorNorm_inv_of hQ, hσP v hv,
      show spinorNorm Q _ (1 : orthGroup Q (v.adicCompletion F)) = 1 from
        (spinorNormHom_apply Q _ hQ 1).symm.trans (map_one _), inv_one, mul_one]
    exact hθ' v
  · intro v hv
    rw [hβv, spinorNorm_mul_of hQ, spinorNorm_inv_of hQ, hσθ v hv, spinorNorm_mul_of hQ]
    exact mul_inv_cancel _

end Helpers

/-! ### Lemma 3.4 and its Corollary -/

/-- **Cassels, Lemma 3.4** (Ch. 11, p. 209): *suppose that $n \ge 3$. Every lattice $\Delta$ in the genus of
$\Lambda$ is properly equivalent to a lattice $\Upsilon$ for which $\Upsilon_p = \beta_p\Lambda_p$, $\beta_p \in
O^+(V_p)$, with $\theta(\beta_p) \in U_p(\mathbb Q_p^\times)^2$ ($p \in P$) and $\theta(\beta_p) = (\mathbb
Q_p^\times)^2$ ($p \notin P$).* Over a number field with $\mathcal O_F$ a principal ideal domain, under `hval`
(Lemma 3.2; this is where $n \ge 3$ enters) and Cassels' condition (3.7) on $P$ (`hP`); $\Upsilon = \beta\Lambda$ with
$\beta \in O(V)(\mathbb A_f)$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.4, p. 209 (over a number field, h_F = 1)"]
theorem exists_isProperIsometric_casselsForm [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (hval : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ u : (𝓞 F)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : F) = algebraMap (𝓞 F) F ((u : 𝓞 F) * a₀))
    (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → ∀ u : (v.adicCompletion F)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ Y : Lat F n, IsProperIsometric Q M.1 Y.1 ∧ ∃ β : OAf Q, latSMul Q β L = Y ∧
      (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion F)) ∧
      (∀ v ∈ P, IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (β v))) ∧
      (∀ v, v ∉ P → spinorNorm Q (v.adicCompletion F) (β v) = 1) := by
  obtain ⟨γ, hγ, β, hβ, h1, h2, h3⟩ := exists_casselsForm_core hQ hval L P hP hM
  exact ⟨latSMul Q β L, ⟨γ, hγ, by rw [hβ, diagF_smul]; rfl⟩, β, rfl, h1, h2, h3⟩

/-- **Cassels, Lemma 3.4, Corollary** (Ch. 11, p. 210): *every spinor genus in the genus of $\Lambda$ contains a
lattice $\Gamma$ of the form (3.17), (3.18) for which $\Gamma_p = \Lambda_p$ ($p \notin P$)*: $\Gamma = \beta\Lambda$
with $\beta_p \in O^+(V_p)$ and $\theta(\beta_p) \in U_p(\mathbb Q_p^\times)^2$ for $p \in P$, $\beta_p = 1$ for
$p \notin P$. Hypotheses as in Lemma 3.4. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.4, Cor., p. 210 (over a number field, h_F = 1)"]
theorem exists_sameProperSpinorGenus_casselsForm [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (hval : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ u : (𝓞 F)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : F) = algebraMap (𝓞 F) F ((u : 𝓞 F) * a₀))
    (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → ∀ u : (v.adicCompletion F)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ Γ : Lat F n, SameProperSpinorGenus Q M Γ ∧ ∃ β : OAf Q, latSMul Q β L = Γ ∧
      (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion F)) ∧
      (∀ v ∈ P, IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) (β v))) ∧
      (∀ v, v ∉ P → β v = 1) ∧ (∀ v, v ∉ P → loc v Γ.1 = loc v L.1) := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨γ, hγ, β, hβ, h1, h2, h3⟩ := exists_casselsForm_core hQ hval L P hP hM
  have hMY : SameProperSpinorGenus Q M (latSMul Q β L) :=
    IsProperIsometric.sameProperSpinorGenus Q ⟨γ, hγ, by rw [hβ, diagF_smul]; rfl⟩
  -- `β''` agrees with `β` on `P` and is trivial elsewhere
  let β'' : OAf Q := ⟨fun v => if v ∈ P then β v else 1, by
    filter_upwards [P.eventually_cofinite_notMem] with v hv
    simp only [hv, ↓reduceIte]
    exact (stdStab Q v).one_mem⟩
  have hβ''v : ∀ v, β'' v = if v ∈ P then β v else 1 := fun v => rfl
  have hβ''P : ∀ v, v ∈ P → β'' v = β v := fun v hv => by rw [hβ''v]; simp [hv]
  have hβ''N : ∀ v, v ∉ P → β'' v = 1 := fun v hv => by rw [hβ''v]; simp [hv]
  let k : OAf Q := β''⁻¹ * β
  have hkv : ∀ v, k v = (β'' v)⁻¹ * β v := fun v => rfl
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    by_cases hv : v ∈ P
    · rw [hkv, hβ''P v hv, inv_mul_cancel]; exact (spinorKernel Q _).one_mem
    · rw [hkv, hβ''N v hv, inv_one, one_mul, spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker,
        MonoidHom.mem_ker, spinorNormHom_apply, h3 v hv, ← soSub_iff_detHom]
      exact ⟨rfl, h1 v⟩
  have hβk : β = k * β'' := by
    ext v : 1
    change β v = (β'' v)⁻¹ * β v * β'' v
    by_cases hv : v ∈ P
    · rw [hβ''P v hv]; group
    · rw [hβ''N v hv]; group
  have hYΓ : SameProperSpinorGenus Q (latSMul Q β'' L) (latSMul Q β L) := by
    refine (sameProperSpinorGenus_iff Q).mpr ⟨1, (Tamagawa.soSub Q F).one_mem, k, hk, ?_⟩
    rw [map_one]
    change (β : OAf Q) • L = (1 : OAf Q) • (k • (β'' • L))
    rw [one_smul, ← mul_smul, ← hβk]
  refine ⟨latSMul Q β'' L, SameProperSpinorGenus.trans Q hMY (SameProperSpinorGenus.symm Q hYΓ), β'', rfl,
    fun v => ?_, fun v hv => ?_, hβ''N, fun v hv => ?_⟩
  · by_cases hv : v ∈ P
    · rw [hβ''P v hv]; exact h1 v
    · rw [hβ''N v hv]; exact (Tamagawa.soSub Q _).one_mem
  · rw [hβ''P v hv]; exact h2 v hv
  · rw [loc_latSMul, hβ''N v hv]
    exact locAct_one _

section Rat

/- Over $\mathbb Q$ the completions carry two `Algebra ℚ` structures (the one of `adicCompletion` and the one of a
characteristic-zero division ring); they are equal (`algebra_rat_subsingleton`) but not reducibly, so the statements
below use the former, as the general theorems do. -/
attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Cassels, Lemma 3.4** (Ch. 11, p. 209) over $\mathbb Q$, $n \ge 3$, with condition (3.7) on $P$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.4, p. 209"]
theorem exists_isProperIsometric_casselsForm_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) :
    ∃ Y : Lat ℚ n, IsProperIsometric Q M.1 Y.1 ∧ ∃ β : OAf Q, latSMul Q β L = Y ∧
      (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) ∧
      (∀ v ∈ P, IsUnitSqClass v (spinorNorm Q (v.adicCompletion ℚ) (β v))) ∧
      (∀ v, v ∉ P → spinorNorm Q (v.adicCompletion ℚ) (β v) = 1) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  exact exists_isProperIsometric_casselsForm Q hQ (exists_unit_mul_mem_spinorNormGroup_rat Q hQ hn) L P hP hM

/-- **Cassels, Lemma 3.4, Corollary** (Ch. 11, p. 210) over $\mathbb Q$, $n \ge 3$, with condition (3.7) on $P$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.4, Cor., p. 210"]
theorem exists_sameProperSpinorGenus_casselsForm_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) :
    ∃ Γ : Lat ℚ n, SameProperSpinorGenus Q M Γ ∧ ∃ β : OAf Q, latSMul Q β L = Γ ∧
      (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) ∧
      (∀ v ∈ P, IsUnitSqClass v (spinorNorm Q (v.adicCompletion ℚ) (β v))) ∧
      (∀ v, v ∉ P → β v = 1) ∧ (∀ v, v ∉ P → loc v Γ.1 = loc v L.1) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  exact exists_sameProperSpinorGenus_casselsForm Q hQ (exists_unit_mul_mem_spinorNormGroup_rat Q hQ hn) L P hP hM

end Rat

end QuadFormsKB.Lattices
