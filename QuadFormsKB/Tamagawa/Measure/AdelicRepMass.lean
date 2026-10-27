/-
# Orbit masses as adelic integrals

**Layer:** abstract measure theory on $G_\infty\times G_f$ (as in `AdelicSO.lean`), then the library's
representation masses.

**Proves** (all unconditional, standard axioms only)
* `setLIntegral_neatDomain`: the integral of a right-$K'$-invariant function of $g_f$ over the neat fundamental domain
  $G_\infty\times\bigcup_i\beta_iK'$ is $\mu_\infty(G_\infty)\,\mu_f(K')\sum_i\theta(\beta_i)$;
* `sum_card_fiber_eq_relIndex_mul_orbitMass` (combinatorics): for a $\Gamma$-set $P$ over $G_f/K$ with finite fibres and
  a neat $K' \le K$ of finite index, $\sum_{\Gamma\beta K'}\#\pi^{-1}(\beta K) = [K:K']\cdot\mathrm{mass}_\Gamma(P)$;
* **`setLIntegral_card_fiber`** (**orbit masses are adelic integrals**): for $\Gamma \le G_\infty\times G_f$ as in
  `covolume_eq_measure_mul_dcMass_of_sep`, a $\Gamma_f$-set $P$ with an equivariant $\pi : P \to G_f/K$ with finite fibres,
  and **any** fundamental domain $D$ of $\Gamma$,
  $$\int_D\#\pi^{-1}(g_fK)\,d(\mu_\infty\times\mu_f)(g) = \mu_\infty(G_\infty)\cdot\mu_f(K)\cdot\mathrm{mass}_{\Gamma_f}(P).$$
  With $P = G_f/K$ this is the covolume formula; with $P$ = pairs (lattice, vector of value $m$) it is the adelic
  integral of the theta-type sum $\#\{\xi \in V(F) : Q(\xi) = m,\ \xi\in g_f\hat L\}$ (below).
-/
import QuadFormsKB.Tamagawa.Measure.Unfolding
import QuadFormsKB.Tamagawa.Measure.AdelicSO
import QuadFormsKB.Tamagawa.RepMass

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

section Abstract

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- **Integral over the neat fundamental domain** of a function of $g_f$ that is constant on each $\beta_iK'$:
$\int_{G_\infty\times\bigcup_i\beta_iK'}\theta(g_f) = \mu_\infty(G_\infty)\,\mu_f(K')\sum_i\theta(\beta_i)$. -/
theorem setLIntegral_neatDomain (K' : Subgroup B) (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Fintype ι]
    (β : ι → B) (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', β i * k = β j * k' → i = j)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μB.IsMulLeftInvariant]
    (θ : B → ℝ≥0∞) (hθ : ∀ i, ∀ k ∈ K', θ (β i * k) = θ (β i)) :
    ∫⁻ x in neatDomain K' β, θ x.2 ∂(μA.prod μB) = μA univ * μB K' * ∑ i, θ (β i) := by
  have hdom : neatDomain (A := A) K' β = ⋃ i, univ ×ˢ (β i • (K' : Set B)) := by
    rw [neatDomain, prod_iUnion]
  have hpd : Pairwise (Function.onFun Disjoint fun i => (univ : Set A) ×ˢ (β i • (K' : Set B))) := by
    intro i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨-, k, hk, hz⟩ ⟨-, k', hk', hz'⟩
    have e1 : β i * k = z.2 := hz
    have e2 : β j * k' = z.2 := hz'
    exact hne (hdisj i j k hk k' hk' (e1.trans e2.symm))
  rw [hdom, lintegral_iUnion (fun i => MeasurableSet.univ.prod (hK'.const_smul _)) hpd,
    tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setLIntegral_congr_fun (MeasurableSet.univ.prod (hK'.const_smul _)) (g := fun _ => θ (β i)),
    setLIntegral_const, Measure.prod_prod, measure_smul]
  · ring
  · rintro x ⟨-, k, hk, hx⟩
    have e : β i * k = x.2 := hx
    show θ x.2 = θ (β i)
    rw [← e]; exact hθ i k hk

variable {Γf : Type*} [Group Γf]

/-- **Pairs over a coset space** (pullback of $\pi : P \to G_f/K$ along $G_f/K' \to G_f/K$). -/
abbrev pullPairs (K' K : Subgroup B) (hle : K' ≤ K) {P : Type*} (π : P → B ⧸ K) : Type _ :=
  {q : (B ⧸ K') × P // π q.2 = (Subgroup.quotientEquivProdOfLE hle q.1).1}

theorem proj_smul (K' K : Subgroup B) (hle : K' ≤ K) (Γ : Subgroup B) (g : Γ) (y : B ⧸ K') :
    (Subgroup.quotientEquivProdOfLE hle (g • y)).1 = g • (Subgroup.quotientEquivProdOfLE hle y).1 := by
  induction y using QuotientGroup.induction_on with | H b => rfl

/-- The action of $\Gamma$ on the pairs. -/
@[instance_reducible]
def pullPairsAction (K' K : Subgroup B) (hle : K' ≤ K) (Γ : Subgroup B) {P : Type*} [MulAction Γ P]
    (π : P → B ⧸ K) (hπ : ∀ (g : Γ) p, π (g • p) = g • π p) : MulAction Γ (pullPairs K' K hle π) where
  smul g q := ⟨(g • q.1.1, g • q.1.2), by rw [hπ, q.2, proj_smul]⟩
  one_smul q := Subtype.ext (Prod.ext (one_smul _ _) (one_smul _ _))
  mul_smul a b q := Subtype.ext (Prod.ext (mul_smul _ _ _) (mul_smul _ _ _))

/-- **Counting fibres over a neat level** (the combinatorial core): for a $\Gamma$-set $P$ with equivariant
$\pi : P \to G_f/K$ with finite fibres, finitely many double cosets $\Gamma\backslash G_f/K$ with finite stabilizers, and
$K' \le K$ of finite index $m$ neat for $\Gamma$,
$$\sum_{\omega\in\Gamma\backslash G_f/K'}\#\pi^{-1}(\beta_\omega K) = m\cdot\mathrm{mass}_\Gamma(P).$$ -/
theorem sum_card_fiber_eq_relIndex_mul_orbitMass (Γ : Subgroup B) {K' K : Subgroup B} (hle : K' ≤ K)
    (hfin : K'.relIndex K ≠ 0) (hneat : IsNeat Γ K') [Finite (orbitRel.Quotient Γ (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer Γ x)) {P : Type*} [MulAction Γ P] (π : P → B ⧸ K)
    (hπ : ∀ (g : Γ) p, π (g • p) = g • π p) (hfib : ∀ x, Finite {p // π p = x})
    [Fintype (orbitRel.Quotient Γ (B ⧸ K'))] :
    (∑ ω : orbitRel.Quotient Γ (B ⧸ K'),
        (Nat.card {p // π p = (QuotientGroup.mk (dcRep Γ K' ω) : B ⧸ K)} : ℝ)) =
      K'.relIndex K * orbitMass Γ P := by
  classical
  let _ := pullPairsAction K' K hle Γ π hπ
  have := finite_orbits_of_relIndex Γ (K := K) (K' := K') hfin
  set proj : B ⧸ K' → B ⧸ K := fun y => (Subgroup.quotientEquivProdOfLE hle y).1
  -- the pairs over `B ⧸ K'`
  let f₁ : pullPairs K' K hle π → B ⧸ K' := fun q => q.1.1
  have hf₁ : ∀ (g : Γ) q, f₁ (g • q) = g • f₁ q := fun _ _ => rfl
  have hfib₁ : ∀ y, {q : pullPairs K' K hle π // f₁ q = y} ≃ {p // π p = proj y} := fun y =>
    { toFun := fun q => ⟨q.1.1.2, by have h := q.1.2; rw [show q.1.1.1 = y from q.2] at h; exact h⟩
      invFun := fun p => ⟨⟨(y, p.1), p.2⟩, rfl⟩
      left_inv := fun q => by
        rcases q with ⟨⟨⟨y', p⟩, h⟩, rfl⟩; rfl
      right_inv := fun p => rfl }
  have hstab₁ : ∀ y : B ⧸ K', Finite (stabilizer Γ y) := fun y => by
    rw [stabilizer_eq_bot_of_isNeat hneat y]; infer_instance
  have hfin₁ : ∀ y, Finite {q : pullPairs K' K hle π // f₁ q = y} := fun y =>
    have := hfib (proj y); Finite.of_equiv _ (hfib₁ y).symm
  have e1 := orbitMass_eq_finsum_fiber f₁ hf₁ hstab₁ hfin₁
  -- the pairs over `P`
  let f₂ : pullPairs K' K hle π → P := fun q => q.1.2
  have hf₂ : ∀ (g : Γ) q, f₂ (g • q) = g • f₂ q := fun _ _ => rfl
  have hfib₂ : ∀ p, {q : pullPairs K' K hle π // f₂ q = p} ≃ {y : B ⧸ K' // proj y = π p} := fun p =>
    { toFun := fun q => ⟨q.1.1.1, by have h := q.1.2; rw [show q.1.1.2 = p from q.2] at h; exact h.symm⟩
      invFun := fun y => ⟨⟨(y.1, p), y.2.symm⟩, rfl⟩
      left_inv := fun q => by
        rcases q with ⟨⟨⟨y, p'⟩, h⟩, rfl⟩; rfl
      right_inv := fun y => rfl }
  have hcard₂ : ∀ p, Nat.card {q : pullPairs K' K hle π // f₂ q = p} = K'.relIndex K := fun p => by
    rw [Nat.card_congr (hfib₂ p)]; exact card_fiber_quotient hle (π p)
  have hfin₂ : ∀ p, Finite {q : pullPairs K' K hle π // f₂ q = p} := fun p => by
    apply Nat.finite_of_card_ne_zero; rw [hcard₂]; exact hfin
  have := finite_orbits_of_fiber π hπ hfib
  have hstabP : ∀ p : P, Finite (stabilizer Γ p) := fun p => by
    have := hstab (π p)
    refine Finite.of_injective (fun s : stabilizer Γ p => (⟨s, by
      rw [mem_stabilizer_iff, ← hπ, mem_stabilizer_iff.mp s.2]⟩ : stabilizer Γ (π p))) ?_
    intro a b h; exact Subtype.ext (congrArg (fun z : stabilizer Γ (π p) => (z : Γ)) h)
  have e2 := orbitMass_fiber f₂ hf₂ hstabP _ hcard₂ hfin₂
  rw [← e2, e1, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [stabilizer_eq_bot_of_isNeat hneat, Nat.card_congr (hfib₁ _)]
  simp only [Subgroup.mem_bot, Nat.card_unique, Nat.cast_one, div_one]
  have hproj : proj ω.out = (QuotientGroup.mk (dcRep Γ K' ω) : B ⧸ K) := by
    rw [← mk_dcRep Γ K' ω]; rfl
  rw [hproj]

/-- Fibres over a translate have the same size. -/
theorem card_fiber_smul {Γ' Y P : Type*} [Group Γ'] [MulAction Γ' Y] [MulAction Γ' P] (π : P → Y)
    (hπ : ∀ (g : Γ') p, π (g • p) = g • π p) (g : Γ') (y : Y) :
    Nat.card {p // π p = g • y} = Nat.card {p // π p = y} :=
  Nat.card_congr
    { toFun := fun p => ⟨g⁻¹ • p.1, by rw [hπ, p.2, inv_smul_smul]⟩
      invFun := fun p => ⟨g • p.1, by rw [hπ, p.2]⟩
      left_inv := fun p => Subtype.ext (smul_inv_smul g p.1)
      right_inv := fun p => Subtype.ext (inv_smul_smul g p.1) }

/-- **Orbit masses are adelic integrals** (the unfolding of Weil 1982, §2.4, Lemma 2.4.2, p. 26, for a function of $g_f$
alone). Let $\Gamma \le G_\infty\times G_f$ be countable with injective projection to $G_f$ (`hinj`), $K \le G_f$ measurable with
a separating family of measurable normal finite-index subgroups (`hsep`), finitely many double cosets
$\Gamma_f\backslash G_f/K$ and finite stabilizers (`hstab`), and $\mu_\infty$, $\mu_f$ left-invariant and s-finite. Let $P$ be a
$\Gamma_f$-set with an equivariant map $\pi : P \to G_f/K$ with finite fibres. Then for **every** fundamental domain $D$ of
$\Gamma$:
$$\int_D\#\pi^{-1}(g_fK)\,d(\mu_\infty\times\mu_f)(g) = \mu_\infty(G_\infty)\cdot\mu_f(K)\cdot\mathrm{mass}_{\Gamma_f}(P)
  \qquad\Big(\mathrm{mass}_{\Gamma_f}(P) = \sum_{\Gamma_f p}\frac1{|\mathrm{Stab}(p)|}\Big).$$ -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26 (unfolding over Γ\\G_𝔸)"]
theorem setLIntegral_card_fiber (Γ : Subgroup (A × B)) [Countable Γ] (K : Subgroup B)
    (hK : MeasurableSet (K : Set B))
    (hsep : ∀ s ∈ K, s ≠ 1 → ∃ N : Subgroup B, N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
      N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B) ∧ s ∉ N)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1)
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer (Γ.map (MonoidHom.snd A B)) x))
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant]
    {P : Type*} [MulAction (Γ.map (MonoidHom.snd A B)) P] (π : P → B ⧸ K)
    (hπ : ∀ (g : Γ.map (MonoidHom.snd A B)) p, π (g • p) = g • π p) (hfib : ∀ x, Finite {p // π p = x})
    {D : Set (A × B)} (hD : IsFundamentalDomain Γ D (μA.prod μB)) :
    ∫⁻ x in D, (Nat.card {p // π p = (QuotientGroup.mk x.2 : B ⧸ K)} : ℝ≥0∞) ∂(μA.prod μB) =
      μA univ * μB K * ENNReal.ofReal (orbitMass (Γ.map (MonoidHom.snd A B)) P) := by
  let Pr : Subgroup B → Prop := fun N => N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
    N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B)
  have hPK : Pr K := ⟨le_rfl, fun x hx y hy => K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx),
    by rw [Subgroup.relIndex_self]; exact one_ne_zero, hK⟩
  have hinf : ∀ N₁ N₂, Pr N₁ → Pr N₂ → Pr (N₁ ⊓ N₂) := by
    rintro N₁ N₂ ⟨h1, n1, i1, m1⟩ ⟨h2, n2, i2, m2⟩
    exact ⟨inf_le_left.trans h1, fun x hx y hy => Subgroup.mem_inf.mpr
      ⟨n1 x hx y (Subgroup.mem_inf.mp hy).1, n2 x hx y (Subgroup.mem_inf.mp hy).2⟩,
      Subgroup.relIndex_inf_ne_zero i1 i2, m1.inter m2⟩
  have hsep' : ∀ s ∈ K, s ≠ 1 → ∃ N, Pr N ∧ s ∉ N := by
    intro s hs hs1
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hsep s hs hs1
    exact ⟨N, ⟨h1, h2, h3, h4⟩, h5⟩
  obtain ⟨K', ⟨hle, -, hfin, hmeas⟩, hneat⟩ :=
    exists_isNeat_of_reps_sep (Γ.map (MonoidHom.snd A B)) K Pr (fun N h => h.1) (fun N h => h.2.1) hPK hinf hsep' (dcRep (Γ.map (MonoidHom.snd A B)) K)
      (fun g => by
        obtain ⟨γ, hγ, k, hk, h⟩ := exists_eq_mul_dcRep (Γ.map (MonoidHom.snd A B)) K g
        exact ⟨_, γ, hγ, k, hk, h⟩)
      (fun ω => by
        have := hstab (QuotientGroup.mk (dcRep (Γ.map (MonoidHom.snd A B)) K ω))
        refine (Set.finite_range (fun s : stabilizer (Γ.map (MonoidHom.snd A B)) (QuotientGroup.mk (dcRep (Γ.map (MonoidHom.snd A B)) K ω) : B ⧸ K) =>
          ((s : (Γ.map (MonoidHom.snd A B))) : B))).subset ?_
        rintro γ ⟨hγ, hK⟩
        exact ⟨⟨⟨γ, hγ⟩, (mem_stabilizer_coset (Γ.map (MonoidHom.snd A B)) K _ ⟨γ, hγ⟩).mpr hK⟩, rfl⟩)
  have := finite_orbits_of_relIndex (Γ.map (MonoidHom.snd A B)) (K := K) (K' := K') hfin
  have := Fintype.ofFinite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K'))
  set θ : B → ℝ≥0∞ := fun b => (Nat.card {p // π p = (QuotientGroup.mk b : B ⧸ K)} : ℝ≥0∞) with hθdef
  have hθinv : ∀ (γ : Γ) (x : A × B), θ ((γ • x).2) = θ x.2 := by
    intro γ x
    have hmem : (γ : A × B).2 ∈ (Γ.map (MonoidHom.snd A B)) := ⟨γ, γ.2, rfl⟩
    simp only [θ]
    congr 1
    exact card_fiber_smul π hπ ⟨_, hmem⟩ (QuotientGroup.mk x.2 : B ⧸ K)
  have hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * dcRep (Γ.map (MonoidHom.snd A B)) K' i * k := fun g => by
    obtain ⟨γf, ⟨γ, hγ, rfl⟩, k, hk, h⟩ := exists_eq_mul_dcRep (Γ.map (MonoidHom.snd A B)) K' g
    exact ⟨_, γ, hγ, k, hk, h⟩
  have hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K',
      γ.2 * dcRep (Γ.map (MonoidHom.snd A B)) K' i * k = dcRep (Γ.map (MonoidHom.snd A B)) K' j * k' → i = j := fun i j γ hγ k hk k' hk' h =>
    dcRep_eq_of_mul (Γ.map (MonoidHom.snd A B)) K' i j ⟨γ, hγ, rfl⟩ hk hk' h
  have hN := isFundamentalDomain_neatDomain Γ K' hinj hneat hmeas (dcRep (Γ.map (MonoidHom.snd A B)) K') hcov hdisj (μA.prod μB)
  have hθ : ∀ i, ∀ k ∈ K', θ (dcRep (Γ.map (MonoidHom.snd A B)) K' i * k) = θ (dcRep (Γ.map (MonoidHom.snd A B)) K' i) := by
    intro i k hk
    simp only [θ, QuotientGroup.mk_mul_of_mem _ (hle hk)]
  change ∫⁻ x in D, θ x.2 ∂(μA.prod μB) = _
  rw [hD.setLIntegral_eq hN (fun x => θ x.2) hθinv,
    setLIntegral_neatDomain K' hmeas (dcRep (Γ.map (MonoidHom.snd A B)) K')
      (fun i j k hk k' hk' h => hdisj i j 1 Γ.one_mem k hk k' hk' (by simpa using h)) μA μB θ hθ]
  have hsum : ∑ ω, θ (dcRep (Γ.map (MonoidHom.snd A B)) K' ω) = ENNReal.ofReal (K'.relIndex K * orbitMass (Γ.map (MonoidHom.snd A B)) P) := by
    rw [← sum_card_fiber_eq_relIndex_mul_orbitMass (Γ.map (MonoidHom.snd A B)) hle hfin hneat hstab π hπ hfib,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
    simp only [θ, ENNReal.ofReal_natCast]
  rw [hsum, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ← relIndex_mul_measure hle hfin hmeas μB]
  ring

end Abstract

/-! ### Group isomorphisms and masses -/

/-- **Masses are invariant under a group isomorphism** acting through it (`MulAction.compHom`). -/
theorem orbitMass_compHom {H₁ H₂ X : Type*} [Group H₁] [Group H₂] [MulAction H₂ X] (e : H₁ ≃* H₂) :
    @orbitMass H₁ X _ (MulAction.compHom X e.toMonoidHom) = orbitMass H₂ X := by
  let _ : MulAction H₁ X := MulAction.compHom X e.toMonoidHom
  have hsmul : ∀ (h : H₁) (x : X), h • x = e h • x := fun _ _ => rfl
  refine orbitMass_eq_of_map id (fun a b => ⟨fun ⟨h, hh⟩ => ⟨e h, by
      show e h • b = a; rw [← hsmul]; exact hh⟩,
    fun ⟨h, hh⟩ => ⟨e.symm h, by
      show e.symm h • b = a; rw [hsmul, MulEquiv.apply_symm_apply]; exact hh⟩⟩)
    (fun y => ⟨y, mem_orbit_self y⟩) (fun x => ?_)
  refine Nat.card_congr
    { toFun := fun h => ⟨e.symm h, by rw [mem_stabilizer_iff, hsmul, MulEquiv.apply_symm_apply]; exact h.2⟩
      invFun := fun h => ⟨e h, by rw [mem_stabilizer_iff, ← hsmul]; exact h.2⟩
      left_inv := fun h => Subtype.ext (MulEquiv.apply_symm_apply e h)
      right_inv := fun h => Subtype.ext (MulEquiv.symm_apply_apply e h) }

/-! ### The representation masses as adelic integrals -/

section RepMass

open NumberField IsDedekindDomain QuadFormsKB.Lattices Matrix QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel

attribute [local instance] ratAct vecAct

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- $\Gamma_f$, the finite-adelic projection of the diagonal $SO(V)(F)$. -/
abbrev GammaSOfin : Subgroup (SOAf Q₀) := (GammaSO Q₀).map (MonoidHom.snd _ _)

/-- **$SO(V)(F) \cong \Gamma_f$** ($\gamma \mapsto (\gamma)_v$). -/
def ratSOEquiv : soSub QF F ≃* GammaSOfin Q₀ :=
  MulEquiv.ofBijective ((finHom Q₀).codRestrict (GammaSOfin Q₀) fun γ =>
      Subgroup.mem_map.mpr ⟨diagSO Q₀ γ, ⟨γ, rfl⟩, rfl⟩)
    ⟨fun a b h => Subtype.ext (diagF_injective QF (congrArg (fun z : GammaSOfin Q₀ => ((z : SOAf Q₀) : OAf QF)) h)),
     fun x => by
      obtain ⟨z, ⟨γ, rfl⟩, hz⟩ := Subgroup.mem_map.mp x.2
      exact ⟨γ, Subtype.ext hz⟩⟩

theorem coe_ratSOEquiv (γ : soSub QF F) :
    (((ratSOEquiv Q₀ γ : GammaSOfin Q₀) : SOAf Q₀) : OAf QF) = diagF QF (γ : orthGroup QF F) := rfl

/-- The lattice $gL$ of a coset $g\,SO(\hat L)$, $L = \mathcal O_F^n$. -/
def cosetLatSO : SOAf Q₀ ⧸ KSO Q₀ → Lat F n :=
  fun y => cosetLat QF (stdLat F n) (Quotient.map' (fun a : SOAf Q₀ => (a : OAf QF)) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢; exact hab) y)

theorem cosetLatSO_mk (a : SOAf Q₀) :
    cosetLatSO Q₀ (QuotientGroup.mk a) = latSMul QF (a : OAf QF) (stdLat F n) := rfl

theorem cosetLatSO_injective : Function.Injective (cosetLatSO Q₀) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  have h' := cosetLat_injective QF (stdLat F n) h
  change (QuotientGroup.mk (a : OAf QF) : OAf QF ⧸ locStab QF (stdLat F n)) = QuotientGroup.mk (b : OAf QF) at h'
  rw [QuotientGroup.eq] at h' ⊢
  rw [Subgroup.mem_subgroupOf]
  simpa using h'

theorem cosetLatSO_mem_latGenus (y : SOAf Q₀ ⧸ KSO Q₀) : cosetLatSO Q₀ y ∈ latGenus QF (stdLat F n) := by
  induction y using QuotientGroup.induction_on with | H a => ?_
  have hmem : latSMul QF (a : OAf QF) (stdLat F n) ∈
      @MulAction.orbit (OAf QF) (Lat F n) (latAction QF).toSMul (stdLat F n) := ⟨(a : OAf QF), rfl⟩
  rw [orbit_eq_genus QF (stdLat F n)] at hmem
  exact hmem

theorem exists_cosetLatSO_eq (hQ : Q₀.Nondegenerate) (hn : 0 < n) {M : Lat F n}
    (hM : M ∈ latGenus QF (stdLat F n)) : ∃ y, cosetLatSO Q₀ y = M := by
  rw [← orbit_eq_genus QF (stdLat F n)] at hM
  obtain ⟨g, hg⟩ := hM
  obtain ⟨s, hs, k, hk, rfl⟩ := exists_so_mul_locStab Q₀ hQ hn g
  refine ⟨QuotientGroup.mk ⟨s, hs⟩, ?_⟩
  rw [cosetLatSO_mk, ← hg]
  show latSMul QF s (stdLat F n) = latSMul QF (s * k) (stdLat F n)
  rw [latSMul_mul]
  congr 1
  rw [← stabilizer_eq_locStab QF (stdLat F n)] at hk
  exact ((@MulAction.mem_stabilizer_iff (OAf QF) (Lat F n) _ (latAction QF) _ _).mp hk).symm

/-- $\Gamma_f$ acts on lattices through $SO(V)(F)$: $\gamma\cdot gL = \gamma gL$. -/
theorem cosetLatSO_smul (γ : GammaSOfin Q₀) (y : SOAf Q₀ ⧸ KSO Q₀) :
    cosetLatSO Q₀ (γ • y) =
      Lat.image ((((ratSOEquiv Q₀).symm γ : soSub QF F) : orthGroup QF F) : GL (Fin n) F) (cosetLatSO Q₀ y) := by
  induction y using QuotientGroup.induction_on with | H a => ?_
  have hγ : ((γ : SOAf Q₀) : OAf QF) = diagF QF (((ratSOEquiv Q₀).symm γ : soSub QF F) : orthGroup QF F) := by
    rw [← coe_ratSOEquiv, MulEquiv.apply_symm_apply]
  show latSMul QF (((γ : SOAf Q₀) : OAf QF) * (a : OAf QF)) (stdLat F n) = _
  rw [latSMul_mul, hγ, diagF_smul]
  rfl

variable (hQ : Q₀.Nondegenerate) (hn : 0 < n)

/-- **The coset of a pair**: for $(M, v)$ in the genus, the unique $g\,SO(\hat L)$ with $gL = M$. -/
def pairCoset (m : F) (p : pairSMA QF (stdLat F n) m) : SOAf Q₀ ⧸ KSO Q₀ :=
  (exists_cosetLatSO_eq Q₀ hQ hn p.2.1).choose

theorem cosetLatSO_pairCoset (m : F) (p : pairSMA QF (stdLat F n) m) :
    cosetLatSO Q₀ (pairCoset Q₀ hQ hn m p) = (p : Lat F n × (Fin n → F)).1 :=
  (exists_cosetLatSO_eq Q₀ hQ hn p.2.1).choose_spec

/-- $\Gamma_f$ acts on the pairs through $SO(V)(F) \le O(V)(F)$. -/
@[instance_reducible]
def pairActSO (m : F) : MulAction (GammaSOfin Q₀) (pairSMA QF (stdLat F n) m) :=
  MulAction.compHom _ ((soSub QF F).subtype.comp (ratSOEquiv Q₀).symm.toMonoidHom)

theorem pairCoset_smul (m : F) (γ : GammaSOfin Q₀) (p : pairSMA QF (stdLat F n) m) :
    pairCoset Q₀ hQ hn m (@HSMul.hSMul _ _ _ (@instHSMul _ _ (pairActSO Q₀ m).toSMul) γ p) =
      γ • pairCoset Q₀ hQ hn m p := by
  apply cosetLatSO_injective Q₀
  rw [cosetLatSO_pairCoset, cosetLatSO_smul, cosetLatSO_pairCoset]
  rfl

/-- The fibre of a coset $gSO(\hat L)$ is the set of representations of $m$ by $gL$. -/
def pairCosetFiber (m : F) (y : SOAf Q₀ ⧸ KSO Q₀) :
    {p : pairSMA QF (stdLat F n) m // pairCoset Q₀ hQ hn m p = y} ≃
      {v : Fin n → F // v ∈ (cosetLatSO Q₀ y).1 ∧ (QF).eval v = m} where
  toFun p := ⟨(p.1 : Lat F n × (Fin n → F)).2, by
    have h := cosetLatSO_pairCoset Q₀ hQ hn m p.1
    rw [p.2] at h
    exact ⟨h ▸ p.1.2.2.1, p.1.2.2.2⟩⟩
  invFun v := ⟨⟨(cosetLatSO Q₀ y, v.1), cosetLatSO_mem_latGenus Q₀ y, v.2.1, v.2.2⟩, by
    apply cosetLatSO_injective Q₀
    rw [cosetLatSO_pairCoset]⟩
  left_inv p := by
    apply Subtype.ext; apply Subtype.ext
    have h := cosetLatSO_pairCoset Q₀ hQ hn m p.1
    rw [p.2] at h
    exact Prod.ext h rfl
  right_inv v := rfl

theorem card_pairCosetFiber (m : F) (a : SOAf Q₀) :
    Nat.card {p : pairSMA QF (stdLat F n) m // pairCoset Q₀ hQ hn m p = QuotientGroup.mk a} =
      repCount QF (latSMul QF (a : OAf QF) (stdLat F n)) m :=
  Nat.card_congr (pairCosetFiber Q₀ hQ hn m _)

include hQ hn in
/-- **$[O(V)(F) : SO(V)(F)] = 2$.** -/
theorem index_soSub_eq_two : (soSub QF F).index = 2 := by
  have hQF := nondegenerate_map Q₀ hQ
  obtain ⟨ρ, hρ⟩ := exists_orthGroup_det_neg_one QF hQF hn
  rw [Subgroup.index_eq_two_iff]
  refine ⟨ρ, fun b => ?_⟩
  rw [mem_soSub, mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, hρ]
  have h1 : (1 : F) ≠ -1 := by
    intro h; have : (2 : F) = 0 := by linear_combination h
    exact two_ne_zero this
  rcases det_eq_one_or_neg_one QF hQF b with h | h <;> simp [h, h1.symm]

include hQ hn in
/-- **The $SO$-mass of the pairs is twice the representation mass:**
$\mathrm{mass}_{\Gamma_f}\{(M, v)\} = 2\sum_{\mathrm{cls}M}r_M(m)/|O(M)|$. -/
theorem orbitMass_pairActSO (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1) (m : F) :
    @orbitMass (GammaSOfin Q₀) (pairSMA QF (stdLat F n) m) _ (pairActSO Q₀ m) =
      2 * repMass QF (stdLat F n) m := by
  have h1 := orbitMass_compHom (X := pairSMA QF (stdLat F n) m) (ratSOEquiv Q₀).symm
  -- `pairActSO` is the action of `soSub` composed with the isomorphism
  have h2 : @orbitMass (GammaSOfin Q₀) (pairSMA QF (stdLat F n) m) _ (pairActSO Q₀ m) =
      @orbitMass (GammaSOfin Q₀) (pairSMA QF (stdLat F n) m) _
        (MulAction.compHom _ (ratSOEquiv Q₀).symm.toMonoidHom) := rfl
  rw [h2, h1]
  have := finite_orbits_gen hpd (stdLat F n) hLi
  have hfin : ∀ M : genSMA QF (stdLat F n),
      Finite {p : pairSMA QF (stdLat F n) m // pairToGen QF (stdLat F n) m p = M} := by
    intro M
    have := finite_repSet hpd (M : Lat F n).2 (SameGenus.isIntegral QF hLi M.2) m
    exact Finite.of_equiv _ (fiberEquiv QF (stdLat F n) m M).symm
  have := finite_orbits_of_fiber (pairToGen QF (stdLat F n) m) (pairToGen_smul QF (stdLat F n) m) hfin
  have hstab : ∀ p : pairSMA QF (stdLat F n) m, Finite (stabilizer (orthGroup QF F) p) := by
    intro p
    have hM : Finite (stabilizer (orthGroup QF F) (pairToGen QF (stdLat F n) m p)) := by
      have := finite_autLat hpd (pairToGen QF (stdLat F n) m p : Lat F n).2
        (SameGenus.isIntegral QF hLi (pairToGen QF (stdLat F n) m p).2)
      apply Nat.finite_of_card_ne_zero
      rw [card_stabilizer_gen]; exact Nat.card_pos.ne'
    refine Finite.of_injective (fun s : stabilizer (orthGroup QF F) p =>
      (⟨s, by rw [mem_stabilizer_iff, ← pairToGen_smul, mem_stabilizer_iff.mp s.2]⟩ :
        stabilizer (orthGroup QF F) (pairToGen QF (stdLat F n) m p))) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun z : stabilizer (orthGroup QF F) (pairToGen QF (stdLat F n) m p) =>
      (z : orthGroup QF F)) h)
  have : (soSub QF F).FiniteIndex := ⟨by rw [index_soSub_eq_two Q₀ hQ hn]; norm_num⟩
  rw [orbitMass_subgroup (soSub QF F) hstab, index_soSub_eq_two Q₀ hQ hn,
    repMass_eq_orbitMass_pairs hpd (stdLat F n) hLi m]
  norm_num

/-- **A fundamental domain for $SO(V)(F)$ in $SO(V)(\mathbb A)$ exists** (the neat domain of `AdelicSO.lean`). -/
theorem exists_isFundamentalDomain_of_sep {A B : Type*} [Group A] [Group B] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableMul A] [MeasurableMul B] (Γ : Subgroup (A × B)) (K : Subgroup B)
    (hK : MeasurableSet (K : Set B))
    (hsep : ∀ s ∈ K, s ≠ 1 → ∃ N : Subgroup B, N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
      N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B) ∧ s ∉ N)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1)
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer (Γ.map (MonoidHom.snd A B)) x)) (μ : Measure (A × B)) :
    ∃ D, IsFundamentalDomain Γ D μ := by
  let Pr : Subgroup B → Prop := fun N => N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
    N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B)
  have hPK : Pr K := ⟨le_rfl, fun x hx y hy => K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx),
    by rw [Subgroup.relIndex_self]; exact one_ne_zero, hK⟩
  have hinf : ∀ N₁ N₂, Pr N₁ → Pr N₂ → Pr (N₁ ⊓ N₂) := by
    rintro N₁ N₂ ⟨h1, n1, i1, m1⟩ ⟨h2, n2, i2, m2⟩
    exact ⟨inf_le_left.trans h1, fun x hx y hy => Subgroup.mem_inf.mpr
      ⟨n1 x hx y (Subgroup.mem_inf.mp hy).1, n2 x hx y (Subgroup.mem_inf.mp hy).2⟩,
      Subgroup.relIndex_inf_ne_zero i1 i2, m1.inter m2⟩
  have hsep' : ∀ s ∈ K, s ≠ 1 → ∃ N, Pr N ∧ s ∉ N := by
    intro s hs hs1
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hsep s hs hs1
    exact ⟨N, ⟨h1, h2, h3, h4⟩, h5⟩
  obtain ⟨K', ⟨hle, -, hfin, hmeas⟩, hneat⟩ :=
    exists_isNeat_of_reps_sep (Γ.map (MonoidHom.snd A B)) K Pr (fun N h => h.1) (fun N h => h.2.1) hPK hinf
      hsep' (dcRep (Γ.map (MonoidHom.snd A B)) K)
      (fun g => by
        obtain ⟨γ, hγ, k, hk, h⟩ := exists_eq_mul_dcRep (Γ.map (MonoidHom.snd A B)) K g
        exact ⟨_, γ, hγ, k, hk, h⟩)
      (fun ω => by
        have := hstab (QuotientGroup.mk (dcRep (Γ.map (MonoidHom.snd A B)) K ω))
        refine (Set.finite_range (fun s : stabilizer (Γ.map (MonoidHom.snd A B))
          (QuotientGroup.mk (dcRep (Γ.map (MonoidHom.snd A B)) K ω) : B ⧸ K) =>
            ((s : Γ.map (MonoidHom.snd A B)) : B))).subset ?_
        rintro γ ⟨hγ, hK⟩
        exact ⟨⟨⟨γ, hγ⟩, (mem_stabilizer_coset (Γ.map (MonoidHom.snd A B)) K _ ⟨γ, hγ⟩).mpr hK⟩, rfl⟩)
  have := finite_orbits_of_relIndex (Γ.map (MonoidHom.snd A B)) (K := K) (K' := K') hfin
  exact ⟨_, isFundamentalDomain_neatDomain Γ K' hinj hneat hmeas (dcRep (Γ.map (MonoidHom.snd A B)) K')
    (fun g => by
      obtain ⟨γf, ⟨γ, hγ, rfl⟩, k, hk, h⟩ := exists_eq_mul_dcRep (Γ.map (MonoidHom.snd A B)) K' g
      exact ⟨_, γ, hγ, k, hk, h⟩)
    (fun i j γ hγ k hk k' hk' h => dcRep_eq_of_mul (Γ.map (MonoidHom.snd A B)) K' i j ⟨γ, hγ, rfl⟩ hk hk' h) μ⟩

include hQ hn in
theorem exists_isFundamentalDomain_GammaSO (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1)
    (μ : Measure (ArchSOProd (realQ Q₀) × SOAf Q₀)) : ∃ D, IsFundamentalDomain (GammaSO Q₀) D μ := by
  have hmap := map_snd_GammaSO Q₀
  have : Finite (orbitRel.Quotient ((GammaSO Q₀).map (MonoidHom.snd _ _)) (SOAf Q₀ ⧸ KSO Q₀)) := by
    rw [hmap]; exact finite_orbits_SO Q₀ hQ hn hpd hLi
  exact exists_isFundamentalDomain_of_sep (GammaSO Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (sep_KSO Q₀)
    (GammaSO_inj Q₀) (fun x => by rw [hmap]; exact finite_stabilizer_SO Q₀ hpd hLi x) μ

include hQ hn in
/-- **The representation mass is an adelic integral** (Weil 1982, §2.4, Lemma 2.4.2, p. 26, applied to the function
$g \mapsto r_{g_fL}(m) = \#\{\xi \in V(F) : Q(\xi) = m,\ \xi \in g_f\hat L\}$ on $SO(V)(F)\backslash SO(V)(\mathbb A)$): for any
fundamental domain $D$ of $\Gamma = SO(V)(F)$ in $SO(V)(\mathbb A)$ and any convergence factors,
$$\int_D r_{g_fL}(m)\,d\mu_{\mathbb A}(g) = c_F\prod_\sigma\mathrm{vol}(SO(V_\sigma))\cdot\prod'_v\mu_v(SO(L_v))\cdot
  2\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(m)}{|O(M)|}.$$ -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26 (unfolding); Siegel's mass side"]
theorem setLIntegral_repCount (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (m : F) {D : Set (ArchSOProd (realQ Q₀) × SOAf Q₀)}
    (hD : IsFundamentalDomain (GammaSO Q₀) D (muAdele Q₀ hQ hpd lam)) :
    ∫⁻ x in D, (repCount QF (latSMul QF (x.2 : OAf QF) (stdLat F n)) m : ℝ≥0∞) ∂(muAdele Q₀ hQ hpd lam) =
      ENNReal.ofReal (cF F n) * (∏ σ : F →ₐ[ℚ] ℂ, ENNReal.ofReal (archVolSO n (detGram Q₀ σ))) *
        ENNReal.ofReal (finFactor Q₀ lam) * ENNReal.ofReal (2 * repMass QF (stdLat F n) m) := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  have := countable_GammaSO Q₀
  have := sigmaFinite_muFin Q₀ hQ hn hpd hLi lam
  have : SFinite (muInfTam Q₀ hQ hpd) := by unfold muInfTam; infer_instance
  have : (muInfTam Q₀ hQ hpd).IsMulLeftInvariant := by unfold muInfTam; infer_instance
  have hmap := map_snd_GammaSO Q₀
  have hfinO : Finite (orbitRel.Quotient ((GammaSO Q₀).map (MonoidHom.snd _ _)) (SOAf Q₀ ⧸ KSO Q₀)) := by
    rw [hmap]; exact finite_orbits_SO Q₀ hQ hn hpd hLi
  have hstab : ∀ x : SOAf Q₀ ⧸ KSO Q₀, Finite (stabilizer ((GammaSO Q₀).map (MonoidHom.snd _ _)) x) := by
    intro x; rw [hmap]; exact finite_stabilizer_SO Q₀ hpd hLi x
  letI := pairActSO Q₀ m
  have hfib : ∀ y, Finite {p : pairSMA QF (stdLat F n) m // pairCoset Q₀ hQ hn m p = y} := by
    intro y
    have := finite_repSet hpd (cosetLatSO Q₀ y).2
      (SameGenus.isIntegral QF hLi (cosetLatSO_mem_latGenus Q₀ y)) m
    exact Finite.of_equiv _ (pairCosetFiber Q₀ hQ hn m y).symm
  have key := setLIntegral_card_fiber (GammaSO Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (sep_KSO Q₀)
    (GammaSO_inj Q₀) hstab (muInfTam Q₀ hQ hpd) (muFin Q₀ lam) (pairCoset Q₀ hQ hn m)
    (pairCoset_smul Q₀ hQ hn m) hfib hD
  have hint : (fun x : ArchSOProd (realQ Q₀) × SOAf Q₀ =>
      (Nat.card {p : pairSMA QF (stdLat F n) m // pairCoset Q₀ hQ hn m p = QuotientGroup.mk x.2} : ℝ≥0∞)) =
      fun x => (repCount QF (latSMul QF (x.2 : OAf QF) (stdLat F n)) m : ℝ≥0∞) := by
    funext x; rw [card_pairCosetFiber]
  unfold muAdele
  rw [← hint, key, muInfTam_univ, muFin_KSO, orbitMass_pairActSO Q₀ hQ hn hpd hLi m]

include hQ hn in
/-- **$2\,\mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{repMass}$ is the Tamagawa integral of $g \mapsto r_{g_fL}(m)$**
over $SO(V)(F)\backslash SO(V)(\mathbb A)$ ($\lambda_v = 1$): the left side of `two_mul_tamagawaK_mul_repMass_frame`
is Weil's unfolded integral. -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26 (unfolding); Siegel's mass side"]
theorem setLIntegral_repCount_one (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1) (m : F)
    {D : Set (ArchSOProd (realQ Q₀) × SOAf Q₀)}
    (hD : IsFundamentalDomain (GammaSO Q₀) D (muAdele Q₀ hQ hpd fun _ => 1)) :
    ∫⁻ x in D, (repCount QF (latSMul QF (x.2 : OAf QF) (stdLat F n)) m : ℝ≥0∞)
        ∂(muAdele Q₀ hQ hpd fun _ => 1) =
      ENNReal.ofReal (2 * tamagawaK Q₀ * repMass QF (stdLat F n) m) := by
  have hprod : 0 ≤ ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ) :=
    Finset.prod_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le
  have htp : 0 ≤ ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
    tprod_nonneg fun v => (siegelDensity_self_pos' Q₀ hQ v).le
  have hrep : 0 ≤ repMass QF (stdLat F n) m := by
    unfold repMass
    exact finsum_nonneg fun c => finsum_nonneg fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hK : tamagawaK Q₀ = cF F n * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
      ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ := rfl
  rw [setLIntegral_repCount Q₀ hQ hn hpd hLi _ m hD, finFactor_one Q₀ hQ,
    show 2 * tamagawaK Q₀ * repMass QF (stdLat F n) m = tamagawaK Q₀ * (2 * repMass QF (stdLat F n) m) by ring,
    hK, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg cF_nonneg hprod) htp),
    ENNReal.ofReal_mul (mul_nonneg cF_nonneg hprod), ENNReal.ofReal_mul cF_nonneg,
    ENNReal.ofReal_prod_of_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le]

end RepMass

end QuadFormsKB.Tamagawa.Measure
