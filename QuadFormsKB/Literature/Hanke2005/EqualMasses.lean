/-
# Shimura's equality of masses (Shimura 1999, Thm. 5.10(1)), proved; Corollary 5.2 unconditional

**Layer:** abstract groups and measures, then number fields (the adelic groups of `MuTamSO.lean`, the double cosets of
`ClassicalSetup.lean`, strong approximation for the spin group from `Lattices/SAVectorsAnisotropic.lean`).

Let $F$ be a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n\ge3$ variables, indefinite
(isotropic at some infinite place of $F$; automatic when $F$ has a complex place), $L = \mathcal O_F^n$,
$G = SO(V)$, $K = SO(\hat L)$, and $\beta_i$ representatives of the double cosets
$G(F)\backslash G(\mathbb A_f)/K$ (the proper classes in the genus of $L$). Shimura's Theorem 5.10(1), quoted in the proof
of Hanke's Corollary 5.2 (thesis, p. 19), says that all the classes have the same volume
$\tau_a(\Gamma_a\backslash G_a)$, $\Gamma_a = G(F)\cap\beta_aK\beta_a^{-1}$, for the archimedean measure $\tau_a$.

**Proves**
* `covolume_levelGroup_eq` (abstract): in $A\times B$ with a countable $\Gamma\le A\times B$, a measurable $K'\le B$ with
  $0<\mu_B(K')<\infty$, exact double coset representatives $\beta_i$ and $\sum_i\mathrm{covol}(\Gamma_{\beta_i})<\infty$: if
  $$bkx\in\Gamma_f\,(bx)\,K'\qquad(b,x\in B,\ k\in K')$$
  (`hSA`), then all $\mathrm{covol}(\Gamma_{\beta_i}, A, \mu_A)$ are equal. Only **left** invariance of $\mu_A$, $\mu_B$ is
  used (no unimodularity of $B$): right translation by $(1,x)$ maps a fundamental domain $\bigsqcup_iD_i\times\beta_iK'$
  of $\Gamma$ to another one; comparing their measures gives $\mu_B(K'x) = \mu_B(K')$, and comparing their intersections
  with the $\Gamma$-invariant set $\Gamma(A\times\beta_jK')$ (`IsFundamentalDomain.measure_set_eq`) gives
  $\mathrm{covol}(\Gamma_{\beta_i})\,\mu_B(K'x)\le\mathrm{covol}(\Gamma_{\beta_j})\,\mu_B(K')$ for $x = \beta_i^{-1}\beta_j$.
* `smul_mem_GammaKSO` (strong approximation): `hSA` holds for $\Gamma = SO(V)(F)$, $K' = SO(\hat L)$, when $Q$ is
  indefinite and $n\ge3$: $x^{-1}kx = ck$ with $c = x^{-1}kxk^{-1}$ a commutator, hence in the adelic spinor kernel
  $O'(V_{\mathbb A_f})$; strong approximation for the spin group (`strongApproximationSpin`, O'Meara 104:4) applied to
  $y c y^{-1}$, $y = bx$, and the lattice $yL$ writes $yc = \gamma\,y\,\kappa$ with $\gamma\in O'(V)\subseteq SO(V)(F)$ and
  $\kappa\in SO(\hat L)$.
* **`shimuraEqualMasses`**: the named statement `ShimuraEqualMasses Q₀ hQ` (formerly a cited input) holds for every
  indefinite $Q_0$ in $n\ge3$ variables. Shimura states it for maximal lattices; the proof here needs no maximality.
* **`corollary52_indefinite`**, `corollary52_indefinite_classNumberOne`: Hanke's Corollary 5.2 (corrected form,
  see `corollary52`), with no named input: $\mathrm{vol}_Z(D_a) = s_a\,\mathrm{Mass}/h$, $h$ the number of classes.

*Comparison with Shimura's proof.* Shimura (Lemma 2.4(5), p. 8) compares $\Gamma = G\cap D$ and $\Gamma^q = G\cap D^q$
through $[D:D\cap D^q] = [D^q:D\cap D^q]$ (his Lemma 2.3(1), cited from [S5, Prop. 8.13(3)]: unimodularity of
$G_{\mathbb A}$) and $GD = GD^q$ (strong approximation). The argument here uses the same strong approximation step but
replaces unimodularity by the finiteness $0<\tau(SO(V))<\infty$: right translation of a fundamental domain of $\Gamma$
in $G_{\mathbb A}$ gives $\mu_f(Kx) = \mu_f(K)$ directly.

All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.ArchComplexConsequences
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SpinorGenusCount
import QuadFormsKB.Tamagawa.Indefinite.OneClass
import QuadFormsKB.Citation

open MeasureTheory Measure MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.EqualMasses

open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### The abstract argument -/

section Abstract

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- **Equal covolumes of the level groups** (abstract form of Shimura 1999, Thm. 5.10(1)). Let $\Gamma\le A\times B$ be
countable, $K'\le B$ measurable with $0<\mu_B(K')<\infty$ (`hK0`, `hKT`), $\beta_i$ exact representatives of
$\Gamma_f\backslash B/K'$ (`hcov`, `hdisj`), $\Gamma_i\to A$ injective (`hinjA`), $D_i$ exact measurable fundamental domains of
the level groups $\Gamma_{\beta_i}$ = `levelGroup Γ K' (β i)` in $A$ (`hDm`, `hD`), with $\sum_i\mathrm{covol}(\Gamma_{\beta_i})<\infty$
(`hfin`). If $bkx\in\Gamma_f\,bx\,K'$ for all $b, x\in B$, $k\in K'$ (`hSA`), then all the covolumes
$\mathrm{covol}(\Gamma_{\beta_i}, A, \mu_A)$ are equal. Only left invariance of $\mu_A$ and $\mu_B$ is used. -/
@[kb "shimura1999" "Thm. 5.10(1) (equal masses of the classes), abstract form"]
theorem covolume_levelGroup_eq (Γ : Subgroup (A × B)) [Countable Γ] (K' : Subgroup B)
    (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] [∀ i, Countable (levelGroup Γ K' (β i))]
    [∀ i, SMulInvariantMeasure (levelGroup Γ K' (β i)) A μA]
    [∀ i, MeasurableConstSMul (levelGroup Γ K' (β i)) A]
    (hK0 : μB K' ≠ 0) (hKT : μB K' ≠ ⊤)
    (hfin : ∑' i, covolume (levelGroup Γ K' (β i)) A μA ≠ ⊤)
    (hSA : ∀ b x : B, ∀ k ∈ K', ∃ γ ∈ Γ, ∃ κ ∈ K', b * k * x = γ.2 * (b * x) * κ) (i j : ι) :
    covolume (levelGroup Γ K' (β i)) A μA = covolume (levelGroup Γ K' (β j)) A μA := by
  set μ := μA.prod μB
  set c : ι → ℝ≥0∞ := fun i => covolume (levelGroup Γ K' (β i)) A μA with hcdef
  have hcD : ∀ i, c i = μA (D i) := fun i =>
    (IsFundamentalDomain.mk' (hDm i).nullMeasurableSet (hD i)).covolume_eq_volume μA
  -- the standard fundamental domain
  set F1 : Set (A × B) := ⋃ i, D i ×ˢ (β i • (K' : Set B)) with hF1
  have hF1m : MeasurableSet F1 := MeasurableSet.iUnion fun i => (hDm i).prod (hK'.const_smul (β i))
  have hdom1 : IsFundamentalDomain Γ F1 μ :=
    IsFundamentalDomain.mk' hF1m.nullMeasurableSet (exists_unique_smul_mem_beta Γ K' β hcov hdisj hinjA D hD)
  have hdisjSet : ∀ (x : B), Pairwise (Function.onFun Disjoint
      fun i => D i ×ˢ ((fun y : B => y * x⁻¹) ⁻¹' (β i • (K' : Set B)))) := by
    intro x i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨-, k, hk, hb⟩ ⟨-, k', hk', hb'⟩
    exact hne (hdisj i j 1 Γ.one_mem k hk k' hk' (by simpa using hb.trans hb'.symm))
  -- the right translate by `(1, x)`
  have hmulR : ∀ x : B, Measurable fun p : A × B => p * ((1 : A), x⁻¹) := fun x => measurable_mul_const _
  set F2 : B → Set (A × B) := fun x => (fun p : A × B => p * ((1 : A), x⁻¹)) ⁻¹' F1 with hF2
  have hF2m : ∀ x, MeasurableSet (F2 x) := fun x => hF1m.preimage (hmulR x)
  have hdom2 : ∀ x, IsFundamentalDomain Γ (F2 x) μ := by
    intro x
    refine IsFundamentalDomain.mk' (hF2m x).nullMeasurableSet fun p => ?_
    obtain ⟨γ, hγ, huniq⟩ := exists_unique_smul_mem_beta Γ K' β hcov hdisj hinjA D hD (p * ((1 : A), x⁻¹))
    refine ⟨γ, ?_, fun γ' h' => huniq γ' ?_⟩
    · show (γ • p) * ((1 : A), x⁻¹) ∈ F1
      have : (γ • p) * ((1 : A), x⁻¹) = γ • (p * ((1 : A), x⁻¹)) := by
        show (γ : A × B) * p * _ = (γ : A × B) * (p * _); rw [mul_assoc]
      rw [this]; exact hγ
    · have : γ' • (p * ((1 : A), x⁻¹)) = (γ' • p) * ((1 : A), x⁻¹) := by
        show (γ' : A × B) * (p * _) = (γ' : A × B) * p * _; rw [mul_assoc]
      show γ' • (p * ((1 : A), x⁻¹)) ∈ F1
      rw [this]; exact h'
  have hF2eq : ∀ x, F2 x = ⋃ i, D i ×ˢ ((fun y : B => y * x⁻¹) ⁻¹' (β i • (K' : Set B))) := by
    intro x; ext ⟨a, b⟩
    simp only [F2, F1, mem_preimage, mem_iUnion, mem_prod, Prod.mk_mul_mk, mul_one]
  set m : B → ℝ≥0∞ := fun x => μB ((fun y : B => y * x⁻¹) ⁻¹' (K' : Set B)) with hmdef
  have hmeasK : ∀ x i, μB ((fun y : B => y * x⁻¹) ⁻¹' (β i • (K' : Set B))) = m x := by
    intro x i
    have : (fun y : B => y * x⁻¹) ⁻¹' (β i • (K' : Set B)) = β i • ((fun y : B => y * x⁻¹) ⁻¹' (K' : Set B)) := by
      ext y
      simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [mul_assoc]
    rw [this, measure_smul]
  have hKm : ∀ x, MeasurableSet ((fun y : B => y * x⁻¹) ⁻¹' (K' : Set B)) := fun x =>
    hK'.preimage (measurable_mul_const _)
  have hμF2 : ∀ x, μ (F2 x) = (∑' i, c i) * m x := by
    intro x
    rw [hF2eq, measure_iUnion (hdisjSet x) (fun i => (hDm i).prod
      ((hK'.const_smul (β i)).preimage (measurable_mul_const _))), ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [Measure.prod_prod, hmeasK, hcD]
  have hm1 : m 1 = μB K' := by simp [m]
  -- if all covolumes vanish there is nothing to prove
  rcases eq_or_ne (∑' i, c i) 0 with h0 | h0
  · have := ENNReal.tsum_eq_zero.1 h0
    show c i = c j
    rw [this i, this j]
  -- `μ_B(K' x) = μ_B(K')`
  have hmx : ∀ x, m x = μB K' := by
    intro x
    have h := (hdom2 1).measure_eq (hdom2 x)
    rw [hμF2, hμF2, hm1] at h
    exact ((ENNReal.mul_right_inj h0 hfin).1 h).symm
  -- the piece comparison
  have key : ∀ i j, c i ≤ c j := by
    intro i j
    set x := (β i)⁻¹ * β j with hx
    set T : Set (A × B) := univ ×ˢ (β j • (K' : Set B)) with hT
    set S : Set (A × B) := ⋃ γ : Γ, (fun p => γ • p) ⁻¹' T with hS
    have hTm : MeasurableSet T := MeasurableSet.univ.prod (hK'.const_smul (β j))
    have hSm : MeasurableSet S := MeasurableSet.iUnion fun γ => hTm.preimage (measurable_const_mul _)
    have hSinv : ∀ g : Γ, (fun p => g • p) ⁻¹' S = S := by
      intro g; ext p
      simp only [S, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨γ, hγ⟩; exact ⟨γ * g, by rwa [mul_smul]⟩
      · rintro ⟨γ, hγ⟩; exact ⟨γ * g⁻¹, by rwa [mul_smul, inv_smul_smul]⟩
    have heq := hdom1.measure_set_eq (hdom2 x) hSm hSinv
    -- upper bound: `S ∩ F1 ⊆ D_j × β_j K'`
    have hsub1 : S ∩ F1 ⊆ D j ×ˢ (β j • (K' : Set B)) := by
      rintro ⟨a, b⟩ ⟨hpS, hpF⟩
      obtain ⟨γ, hγ⟩ := mem_iUnion.1 hpS
      obtain ⟨l, hla, k, hk, hkb⟩ := mem_iUnion.1 hpF
      obtain ⟨-, k', hk', hk'b⟩ := hγ
      have hb : (γ : A × B).2 * b = β j * k' := by
        exact hk'b.symm
      have hlj : l = j := hdisj l j γ γ.2 k hk k' hk' (by
        rw [mul_assoc, ← hb]; simp only [smul_eq_mul] at hkb; rw [hkb])
      subst hlj
      exact ⟨hla, k, hk, hkb⟩
    have hle1 : μ (S ∩ F1) ≤ c j * μB K' := by
      refine (measure_mono hsub1).trans ?_
      rw [Measure.prod_prod, measure_smul, hcD]
    -- lower bound: `D_i × β_i K' x ⊆ S ∩ F2 x`
    have hsub2 : D i ×ˢ ((fun y : B => y * x⁻¹) ⁻¹' (β i • (K' : Set B))) ⊆ S ∩ F2 x := by
      rintro ⟨a, b⟩ hp
      refine ⟨?_, by rw [hF2eq]; exact mem_iUnion.2 ⟨i, hp⟩⟩
      obtain ⟨-, k, hk, hkb⟩ := hp
      simp only [smul_eq_mul] at hkb
      obtain ⟨γ, hγ, κ, hκ, hγκ⟩ := hSA (β i) x k hk
      have hbx : b = β i * k * x := by rw [hkb]; group
      have hix : β i * x = β j := by rw [hx]; group
      refine mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, mem_univ _, κ, hκ, ?_⟩
      show β j * κ = ((γ⁻¹ : A × B) * (a, b)).2
      simp only [Prod.snd_mul, Prod.snd_inv]
      rw [hbx, hγκ, hix]; group
    have hle2 : c i * μB K' ≤ μ (S ∩ F2 x) := by
      refine le_trans ?_ (measure_mono hsub2)
      rw [Measure.prod_prod, hmeasK, hcD, hmx]
    have := hle2.trans (heq ▸ hle1)
    exact (ENNReal.mul_le_mul_iff_left hK0 hKT).1 this
  exact le_antisymm (key i j) (key j i)

end Abstract

/-! ### Strong approximation: the hypothesis `hSA` for $SO(V)(F)$ and $SO(\hat L)$ -/

section NumberField

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Indefinite

/-- $O(\widehat{yL}) = y\,O(\hat L)\,y^{-1}$: if $g$ stabilizes $yL$ then $y^{-1}gy$ stabilizes $L$. -/
theorem conj_mem_locStab {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (L : Lat F n)
    (y g : OAf Q) (hg : g ∈ locStab Q (latSMul Q y L)) : y⁻¹ * g * y ∈ locStab Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  rw [← stabilizer_eq_locStab] at hg ⊢
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have hg' : g • (y • L) = y • L := hg
  rw [mul_smul, mul_smul, hg', inv_smul_smul]

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Strong approximation in the form used for equal masses**: for $Q$ indefinite, $n\ge3$, and all
$b, x\in SO(V)(\mathbb A_f)$, $k\in SO(\hat L)$: $bkx\in SO(V)(F)\,(bx)\,SO(\hat L)$. With $y = bx$ and the commutator
$c = x^{-1}kxk^{-1}\in O'(V_{\mathbb A_f})$, strong approximation for the spin group (O'Meara 104:4,
`strongApproximationSpin`) applied to $ycy^{-1}$ and the lattice $yL$ gives $\gamma\in O'(V)\subseteq SO(V)(F)$ with
$\gamma^{-1}ycy^{-1}\in O(\widehat{yL})$, and $bkx = yck = \gamma\,y\,(y^{-1}\gamma^{-1}yc)\,k$. -/
@[kb "omeara1963" "§104, 104:4, p. 315 (strong approximation for O'); §101D, p. 296 (J'_V contains the commutators)"]
theorem mem_Gamma_mul_KSO (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF)
    (b x k : SOAf Q₀) (hk : k ∈ KSO Q₀) :
    ∃ γ ∈ GammaSOAdele Q₀, ∃ κ ∈ KSO Q₀, b * k * x = γ.2 * (b * x) * κ := by
  have hQF : (QF).Nondegenerate := nondegenerate_map Q₀ hQ
  set y : SOAf Q₀ := b * x with hy
  set c : SOAf Q₀ := x⁻¹ * k * x * k⁻¹ with hc
  have hcK : ((c : SOAf Q₀) : OAf QF) ∈ spinorKernelAf QF := by
    have := commutator_mem_spinorKernelAf QF hQF ((x : OAf QF)⁻¹) (k : OAf QF)
    simpa [c, inv_inv] using this
  have hh : (y : OAf QF) * (c : OAf QF) * (y : OAf QF)⁻¹ ∈ spinorKernelAf QF :=
    (spinorKernelAf_normal QF).conj_mem _ hcK _
  obtain ⟨γ0, hγ0, hstab⟩ :=
    strongApproximationSpin.approx QF hn hQF hind (latSMul QF (y : OAf QF) (stdLat F n)) _ hh
  have hdet : ((γ0 : GL (Fin n) F)).val.det = 1 := det_of_mem_spinorKernel QF hγ0
  let γs : soSub QF F := ⟨γ0, hdet⟩
  have hfin : (((diagSOAdele Q₀ γs).2 : SOAf Q₀) : OAf QF) = diagF QF γ0 := rfl
  set κ : SOAf Q₀ := y⁻¹ * ((diagSOAdele Q₀ γs).2)⁻¹ * y * c with hκdef
  have hκ : κ ∈ KSO Q₀ := by
    rw [Subgroup.mem_subgroupOf]
    have := conj_mem_locStab QF (stdLat F n) (y : OAf QF) _ hstab
    convert this using 1
    simp only [κ, Subgroup.coe_mul, Subgroup.coe_inv, hfin]
    group
  refine ⟨diagSOAdele Q₀ γs, ⟨γs, rfl⟩, κ * k, (KSO Q₀).mul_mem hκ hk, ?_⟩
  simp only [κ, c, y]
  group

/-! ### Shimura's Theorem 5.10(1) and Corollary 5.2 -/

/-- **Equal unit volumes** $v(M_i) = \mathrm{covol}(\Gamma_i\backslash G_\infty)$ (`unitVolume`, measure `muArchTamSO`) for
all proper classes $i, j$ in the genus of $\mathcal O_F^n$, $Q_0$ indefinite, $n\ge3$. -/
@[kb "shimura1999" "Thm. 5.10(1)"]
theorem unitVolume_eq (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) (i j : DC Q₀) :
    unitVolume Q₀ hQ i = unitVolume Q₀ hQ j := by
  show covolume (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)) (GInfSO Q₀) (muArchTamSO Q₀ hQ) =
    covolume (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ j)) (GInfSO Q₀) (muArchTamSO Q₀ hQ)
  have hτ : TamagawaNumberTwoAdelic Q₀ hQ := Weil.tauTwoAll_release_uncond n hn Q₀ hQ
  have hcov := covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ
  have h2 : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  rw [h2] at hcov
  have hK0 : muFin Q₀ (fun _ => 1) (KSO Q₀) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcov; exact two_ne_zero hcov
  have hKT : muFin Q₀ (fun _ => 1) (KSO Q₀) ≠ ⊤ := by rw [muFin_KSO]; exact ENNReal.ofReal_ne_top
  have hfin := tsum_unitVolume_ne_top Q₀ hQ hτ
  have := countable_GammaSOAdele Q₀
  have := fun i => countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  have := fun i => smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
    (muArchTamSO Q₀ hQ)
  have := fun i => measurableConstSMul_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
  exact covolume_levelGroup_eq (GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (dcRep Q₀)
    (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1) hK0 hKT hfin
    (fun b x k hk => mem_Gamma_mul_KSO Q₀ hn hQ hind b x k hk) i j

/-- **Shimura's equality of masses, proved** (Shimura 1999, Thm. 5.10(1), as quoted in the proof of Hanke's
Corollary 5.2, thesis p. 19): for $Q_0$ nondegenerate and indefinite (`hind`: isotropic at some infinite place of $F$)
in $n\ge3$ variables, all the proper classes $a$ in the genus of $\mathcal O_F^n$ have the same volume
$\tau_a(\Gamma_a\backslash G_a)$. The named statement `ShimuraEqualMasses` is no longer an input. Shimura assumes the
lattice maximal; this proof does not need it. Proof: `covolume_levelGroup_eq` with the strong approximation step
`mem_Gamma_mul_KSO`; finiteness from $\tau(SO(V)) = 2$ (`tauTwoAll_release_uncond`). -/
@[kb "shimura1999" "Thm. 5.10(1)"]
theorem shimuraEqualMasses (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) :
    Eq57.ShimuraEqualMasses Q₀ hQ := by
  refine ⟨fun i j => ?_⟩
  rw [covolume_muArchHanke Q₀ hQ i, covolume_muArchHanke Q₀ hQ j, unitVolume_eq Q₀ hn hQ hind i j]

open Eq57 in
/-- **Corollary 5.2 (corrected), with no named input** (Hanke thesis, p. 19): for $Q_0$ nondegenerate and indefinite in
$n\ge3$ variables, $D_a\subseteq Z$ meeting almost every $\Gamma_a$-orbit $s_a$ times,
$$\mathrm{vol}_Z(D_a) = \frac{s_a\cdot\mathrm{Mass}}{h},\qquad h = \#\mathrm{Cl}\ (\texttt{Nat.card (DC Q₀)}),$$
i.e. $\mathrm{vol}(\Gamma_a\backslash Z) = \varepsilon\,\mathrm{Mass}/h$ (see `corollary52` for the erratum: the thesis prints
the class number in the numerator). Hanke assumes $\Lambda$ maximal; not needed here. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected)"]
theorem corollary52_indefinite (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ / (Nat.card (DC Q₀) : ℝ≥0∞) :=
  corollary52_uncond Q₀ hQ (by omega) (shimuraEqualMasses Q₀ hn hQ hind) D hD s hs0 hsT hDs i

open Eq57 in
/-- **Corollary 5.2 for class number one (corrected), with no named input**: $\mathrm{vol}_Z(D_a) = s_a\,\mathrm{Mass}$
when the genus has one proper class. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (corrected), class number one"]
theorem corollary52_indefinite_classNumberOne (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF)
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i)
    (hcard : Nat.card (DC Q₀) = 1) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ :=
  corollary52_classNumberOne_uncond Q₀ hQ (by omega) (shimuraEqualMasses Q₀ hn hQ hind) D hD s hs0 hsT hDs
    hcard i

end NumberField

end QuadFormsKB.Hanke2005.EqualMasses
