/-
# Kitaoka 1993, Theorem 1.2.2 (Kneser): Assertion 1

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.2, proof of Theorem 1.2.2, Assertion 1, pp. 7–9
(printed pages).

**Proves** `assertion1`: let $J \subseteq L$ with (1) $q(J) \subseteq R$, $b(L, J) \subseteq R$; $M, N \subseteq L$ with $M$
free of finite rank, (2a) every $R$-linear $M \to R$ is $x \mapsto b(x, y)$ with $y \in J$, (2b) the same for $N$;
$\sigma : M \cong N$ an isometry with (3) $\sigma(x) \equiv x \bmod J$; (5), (6): some $e \in J$ has $q(e) \in R^\times$
and, if $\#\bar R = 2$, $b(e, J) \subseteq P$. Then $\sigma$ is the restriction of an element of $S(J)$.

**Proof** (Kitaoka's induction on $\operatorname{rank} M$, with one addition). Split $M = M_0 \oplus Rm$ such that
$b(M_0, e) \subseteq P$: if $b(m_0, e)$ is a unit for some $m_0 \in M$ take $M_0 = \{x \in M : b(x, e) = 0\}$ (free, as a
direct summand of a free module over a local ring); otherwise any basis splitting. Kitaoka says "changing a basis if
necessary, we may suppose $h \in Rh_r + K$"; when all $b(m_i, e)$ lie in $P$ no change of basis achieves this in
general, and one uses instead $e_0 = e - \sum_i b(c_i, e)h_i \in J_0 = J \cap M_0^\perp$ ($c_i$ a basis of $M_0$, $h_i$
dual vectors), which has $q(e_0) \equiv q(e)$ and $b(e_0, J_0) \equiv b(e, J_0) \bmod P$. The induction hypothesis
gives $\tau_0 \in S(J)$ with $\tau_0 = \sigma$ on $M_0$; then `rankOne` for $J_0$, $m$ and $\tau_0^{-1}\sigma(m)$ gives
$\tau_1 \in S(J_0)$, which fixes $M_0$, and $\tau_0\tau_1 = \sigma$ on $M$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1KneserRankOne
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free

open QuadraticMap IsLocalRing Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Kneser

variable {R Rt U : Type} [CommRing R] [IsLocalRing R] [CommRing Rt] [Algebra R Rt]
  [AddCommGroup U] [Module Rt U] [Module R U] [IsScalarTower R Rt U]
variable {q : QuadraticForm Rt U}

/-- The hypotheses (1) of Kitaoka's Theorem 1.2.2 for $H = J$. -/
structure Cond1 (q : QuadraticForm Rt U) (L J : Submodule R U) : Prop where
  le : J ≤ L
  qJ : ∀ z ∈ J, q z ∈ (algebraMap R Rt).range
  LJ : ∀ x ∈ L, ∀ z ∈ J, polar q x z ∈ (algebraMap R Rt).range

/-- Condition (2) for a submodule $M$: every linear functional on $M$ is $x \mapsto b(x, y)$ with $y \in J$. -/
def Cond2 (q : QuadraticForm Rt U) (J M : Submodule R U) : Prop :=
  ∀ f : M →ₗ[R] R, ∃ y ∈ J, ∀ x : M, algebraMap R Rt (f x) = polar q x y

/-- Conditions (5), (6): a vector $e \in J$ with $q(e) \in R^\times$ and, if $\#\bar R = 2$, $b(e, J) \subseteq P$. -/
def Cond56 (q : QuadraticForm Rt U) (J : Submodule R U) : Prop :=
  ∃ e ∈ J, IsUnitVal R (q e) ∧ (Nat.card (ResidueField R) = 2 → ∀ z ∈ J, rs R (polar q e z) = 0)

/-- $J_0 = J \cap M_0^\perp$. -/
def perpIn (q : QuadraticForm Rt U) (J M0 : Submodule R U) : Submodule R U where
  carrier := {z | z ∈ J ∧ ∀ x ∈ M0, polar q x z = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨J.add_mem ha hb, fun x hx => by rw [polar_add_right, ha' x hx, hb' x hx, add_zero]⟩
  zero_mem' := ⟨J.zero_mem, fun x _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨J.smul_mem c ha, fun x hx => ?_⟩
    rw [← algebraMap_smul Rt c a, polar_smul_right, ha' x hx, smul_zero]

theorem perpIn_le (J M0 : Submodule R U) : perpIn q J M0 ≤ J := fun _ h => h.1

theorem Cond1.mono {L J J' : Submodule R U} (h : Cond1 q L J) (hJ : J' ≤ J) : Cond1 q L J' :=
  ⟨hJ.trans h.le, fun z hz => h.qJ z (hJ hz), fun x hx z hz => h.LJ x hx z (hJ hz)⟩

/-- A splitting $M = M_0 \oplus Rm$ with the coefficient functional $a$. -/
structure Split (M M0 : Submodule R U) (m : U) where
  le : M0 ≤ M
  mem : m ∈ M
  a : M →ₗ[R] R
  a_m : a ⟨m, mem⟩ = 1
  a_zero : ∀ x : M, (x : U) ∈ M0 → a x = 0
  dec : ∀ x : M, (x : U) - a x • m ∈ M0

/-- Elements of $S(J)$ are $R$-linear. -/
theorem map_smul_R (g : U ≃ₗ[Rt] U) (a : R) (x : U) : g (a • x) = a • g x := by
  rw [← algebraMap_smul Rt a x, map_smul, algebraMap_smul]

/-- An isometry of $U$ preserves $b$. -/
theorem polar_equiv (g : U ≃ₗ[Rt] U) (hg : ∀ x, q (g x) = q x) (x y : U) : polar q (g x) (g y) = polar q x y := by
  simp only [polar, ← map_add, hg]

/-- An isometry $M \cong N$ of submodules preserves $b$. -/
theorem polar_sub_equiv {M N : Submodule R U} (σ : M ≃ₗ[R] N) (hσq : ∀ x, q (σ x) = q x) (x y : M) :
    polar q (σ x : U) (σ y : U) = polar q (x : U) (y : U) := by
  have h1 : (σ x : U) + (σ y : U) = (σ (x + y) : U) := by rw [map_add, Submodule.coe_add]
  have h2 : (x : U) + (y : U) = ((x + y : M) : U) := rfl
  simp only [polar, h1, h2, hσq]

/-- **The induction step**, given the splitting and the facts about $e_0$. -/
theorem assertion_step {L J M N M0 : Submodule R U} {m : U} (hinj : Function.Injective (algebraMap R Rt))
    (h1 : Cond1 q L J) (hML : M ≤ L) (hNL : N ≤ L) (h2a : Cond2 q J M) (h2b : Cond2 q J N)
    (σ : M ≃ₗ[R] N) (hσq : ∀ x, q (σ x) = q x) (hσJ : ∀ x : M, (σ x : U) - x ∈ J)
    (S : Split M M0 m) (he0 : Cond56 q (perpIn q J M0))
    (ih : ∀ (N0 : Submodule R U) (σ0 : M0 ≃ₗ[R] N0), N0 ≤ L → Cond2 q J M0 → Cond2 q J N0 →
      (∀ x, q (σ0 x) = q x) → (∀ x : M0, (σ0 x : U) - x ∈ J) →
      ∃ g : U ≃ₗ[Rt] U, InS q J g ∧ ∀ x : M0, g x = σ0 x) :
    ∃ g : U ≃ₗ[Rt] U, InS q J g ∧ ∀ x : M, g x = σ x := by
  classical
  -- the projection $M \to M_0$
  let proj : M →ₗ[R] M0 := LinearMap.codRestrict M0 (M.subtype - S.a.smulRight m) (fun x => by
    simpa using S.dec x)
  have hproj : ∀ x : M, (proj x : U) = x - S.a x • m := fun x => by simp [proj]
  have hproj0 : ∀ x0 : M0, proj (Submodule.inclusion S.le x0) = x0 := fun x0 => by
    apply Subtype.ext
    rw [hproj, S.a_zero _ x0.2, zero_smul, sub_zero]; rfl
  -- $\sigma_0 = \sigma|_{M_0}$
  let f : M0 →ₗ[R] U := N.subtype ∘ₗ σ.toLinearMap ∘ₗ Submodule.inclusion S.le
  have hf : Function.Injective f := by
    intro x y h
    have := σ.injective (Subtype.ext h)
    exact Submodule.inclusion_injective S.le this
  let N0 := LinearMap.range f
  let σ0 : M0 ≃ₗ[R] N0 := LinearEquiv.ofInjective f hf
  have hσ0 : ∀ x : M0, (σ0 x : U) = σ (Submodule.inclusion S.le x) := fun x => rfl
  have hN0L : N0 ≤ L := by rintro _ ⟨x, rfl⟩; exact hNL (σ _).2
  -- (2) for $M_0$ and $N_0$
  have h2a0 : Cond2 q J M0 := by
    intro f0
    obtain ⟨y, hy, hy'⟩ := h2a (f0 ∘ₗ proj)
    refine ⟨y, hy, fun x0 => ?_⟩
    have := hy' (Submodule.inclusion S.le x0)
    rwa [LinearMap.comp_apply, hproj0] at this
  have h2b0 : Cond2 q J N0 := by
    intro g0
    obtain ⟨y, hy, hy'⟩ := h2b (g0 ∘ₗ σ0.toLinearMap ∘ₗ proj ∘ₗ σ.symm.toLinearMap)
    refine ⟨y, hy, fun z => ?_⟩
    obtain ⟨x0, hx0⟩ : ∃ x0 : M0, σ0 x0 = z := σ0.surjective z
    have hz : (z : U) = σ (Submodule.inclusion S.le x0) := by rw [← hx0, hσ0]
    have := hy' (σ (Submodule.inclusion S.le x0))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hproj0, hx0] at this
    rw [hz, ← this]
  obtain ⟨τ0, hτ0, hτ0σ⟩ := ih N0 σ0 hN0L h2a0 h2b0 (fun x => by rw [hσ0, hσq]; rfl)
    (fun x => by rw [hσ0]; exact hσJ _)
  -- the data for the rank-one step
  have hJJ : ∀ x ∈ J, ∀ z ∈ J, polar q x z ∈ (algebraMap R Rt).range := fun x hx z hz => h1.LJ x (h1.le hx) z hz
  have hτ0s := hτ0.symm
  have hσm : (σ ⟨m, S.mem⟩ : U) ∈ L := hNL (σ _).2
  set n' := τ0.symm (σ ⟨m, S.mem⟩ : U) with hn'
  have hn'L : n' ∈ L := (hτ0s.sub_mem h1.le h1.LJ _ hσm).1
  have hτ0n' : τ0 n' = σ ⟨m, S.mem⟩ := by rw [hn', LinearEquiv.apply_symm_apply]
  have hτ0x : ∀ x0 (hx0 : x0 ∈ M0), τ0 x0 = σ (Submodule.inclusion S.le ⟨x0, hx0⟩) := fun x0 hx0 => by
    have := hτ0σ ⟨x0, hx0⟩
    rw [hσ0] at this
    exact this
  -- $b(x_0, n') = b(x_0, m)$ for $x_0 \in M_0$
  have hpol : ∀ x0 ∈ M0, polar q x0 n' = polar q x0 m := by
    intro x0 hx0
    rw [← polar_equiv τ0 hτ0.isom, hτ0x x0 hx0, hτ0n', polar_sub_equiv σ hσq]
    rfl
  have hmem : n' - m ∈ perpIn q J M0 := by
    refine ⟨?_, fun x0 hx0 => by rw [polar_sub_right, hpol x0 hx0, sub_self]⟩
    have e1 : n' - m = (τ0.symm (σ ⟨m, S.mem⟩ : U) - (σ ⟨m, S.mem⟩ : U)) + ((σ ⟨m, S.mem⟩ : U) - m) := by
      rw [hn']; abel
    rw [e1]
    exact J.add_mem (hτ0s.sub_mem h1.le h1.LJ _ hσm).2 (hσJ _)
  have hqn' : q n' = q m := by rw [hn', hτ0s.isom, hσq]
  have hym : ∃ y ∈ perpIn q J M0, polar q m y = 1 := by
    obtain ⟨y, hy, hy'⟩ := h2a S.a
    refine ⟨y, ⟨hy, fun x0 hx0 => ?_⟩, ?_⟩
    · have := hy' ⟨x0, S.le hx0⟩
      rw [S.a_zero _ hx0, map_zero] at this
      exact this.symm
    · have := hy' ⟨m, S.mem⟩
      rw [S.a_m, map_one] at this
      exact this.symm
  have hyn : ∃ y ∈ perpIn q J M0, polar q n' y = 1 := by
    obtain ⟨y, hy, hy'⟩ := h2b (S.a ∘ₗ σ.symm.toLinearMap)
    have hyJ : τ0.symm y ∈ J := (hτ0s.sub_mem le_rfl hJJ y hy).1
    refine ⟨τ0.symm y, ⟨hyJ, fun x0 hx0 => ?_⟩, ?_⟩
    · rw [← polar_equiv τ0 hτ0.isom, LinearEquiv.apply_symm_apply, hτ0x x0 hx0]
      have := hy' (σ (Submodule.inclusion S.le ⟨x0, hx0⟩))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
      rw [← this]
      have : S.a (Submodule.inclusion S.le ⟨x0, hx0⟩) = 0 := S.a_zero _ hx0
      rw [this, map_zero]
    · rw [← polar_equiv τ0 hτ0.isom]
      simp only [LinearEquiv.apply_symm_apply, hn']
      have := hy' (σ ⟨m, S.mem⟩)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, S.a_m, map_one] at this
      exact this.symm
  have h10 := h1.mono (perpIn_le (q := q) J M0)
  obtain ⟨τ1, hτ1, hτ1m⟩ := rankOne hinj h10.le h10.qJ h10.LJ (hML S.mem) hn'L hmem hqn' hym hyn he0
  refine ⟨τ1.trans τ0, (hτ1.mono (perpIn_le J M0)).trans hτ0, fun x => ?_⟩
  -- $x = x_0 + a(x)m$
  have hx0 : (x : U) - S.a x • m ∈ M0 := S.dec x
  have hdec : (x : U) = ((x : U) - S.a x • m) + S.a x • m := by abel
  have hfix : τ1 ((x : U) - S.a x • m) = (x : U) - S.a x • m :=
    hτ1.fix _ fun z hz => hz.2 _ hx0
  have hσx : (σ x : U) = (σ (Submodule.inclusion S.le ⟨_, hx0⟩) : U) + S.a x • (σ ⟨m, S.mem⟩ : U) := by
    have : x = Submodule.inclusion S.le ⟨_, hx0⟩ + S.a x • ⟨m, S.mem⟩ := by
      apply Subtype.ext; simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
  rw [LinearEquiv.trans_apply, hdec, map_add, map_smul_R, hfix, hτ1m, map_add, map_smul_R, hτ0n',
    hτ0x _ hx0, hσx]


/-! ### Sums with coefficients in $P$ -/

theorem rs_sum_P {L J : Submodule R U} (hinj : Function.Injective (algebraMap R Rt)) (h1 : Cond1 q L J)
    {ι : Type} (s : Finset ι) (a : ι → R) (ha : ∀ i, a i ∈ maximalIdeal R) (h : ι → U) (hh : ∀ i, h i ∈ J) :
    (∑ i ∈ s, a i • h i) ∈ J ∧ rs R (q (∑ i ∈ s, a i • h i)) = 0 ∧
      ∀ w ∈ L, rs R (polar q (∑ i ∈ s, a i • h i) w) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨J.zero_mem, ?_, fun w _ => ?_⟩
    · simp only [Finset.sum_empty, QuadraticMap.map_zero]
      rw [← map_zero (algebraMap R Rt), rs_algebraMap hinj, map_zero]
    · simp only [Finset.sum_empty, QuadraticMap.polar_zero_left]
      rw [← map_zero (algebraMap R Rt), rs_algebraMap hinj, map_zero]
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [Finset.sum_insert hi]
    have hres : residue R (a i) = 0 := (residue_eq_zero_iff _).mpr (ha i)
    refine ⟨J.add_mem (J.smul_mem _ (hh i)) ih1, ?_, fun w hw => ?_⟩
    · rw [rs_q_smul_add hinj h1.le h1.qJ h1.LJ (hh i) ih1, hres, ih2]; ring
    · rw [rs_polar_smul_add hinj h1.le h1.qJ h1.LJ hw (hh i) ih1, hres, ih3 w hw]; ring

/-! ### The functional $x \mapsto b(x, e)$ on $M$ -/

/-- $x \mapsto b(x, e) \in R$ on $M \subseteq L$, for $e \in J$. -/
def phiE {L J M : Submodule R U} (hinj : Function.Injective (algebraMap R Rt)) (h1 : Cond1 q L J) (hML : M ≤ L)
    {e : U} (he : e ∈ J) : M →ₗ[R] R where
  toFun x := toR R (polar q (x : U) e)
  map_add' x y := by
    apply hinj
    have hx := h1.LJ _ (hML x.2) e he
    have hy := h1.LJ _ (hML y.2) e he
    have hxy := h1.LJ _ (hML (x + y).2) e he
    rw [toR_spec hxy, map_add, toR_spec hx, toR_spec hy, Submodule.coe_add, polar_add_left]
  map_smul' c x := by
    apply hinj
    have hx := h1.LJ _ (hML x.2) e he
    have hcx := h1.LJ _ (hML (c • x).2) e he
    rw [toR_spec hcx, RingHom.id_apply, smul_eq_mul, map_mul, toR_spec hx, Submodule.coe_smul,
      ← algebraMap_smul Rt c (x : U), polar_smul_left, smul_eq_mul]

theorem phiE_spec {L J M : Submodule R U} (hinj : Function.Injective (algebraMap R Rt)) (h1 : Cond1 q L J)
    (hML : M ≤ L) {e : U} (he : e ∈ J) (x : M) :
    algebraMap R Rt (phiE hinj h1 hML he x) = polar q (x : U) e :=
  toR_spec (h1.LJ _ (hML x.2) e he)

/-! ### The induction -/

/-- **Kitaoka 1993, proof of Theorem 1.2.2, Assertion 1** (pp. 7–9), for $M$ free of finite rank. -/
theorem assertion1 (hinj : Function.Injective (algebraMap R Rt)) (r : ℕ) :
    ∀ {L J M N : Submodule R U}, Cond1 q L J → M ≤ L → N ≤ L → Module.Free R M → Module.Finite R M →
      finrank R M = r → Cond2 q J M → Cond2 q J N → ∀ σ : M ≃ₗ[R] N, (∀ x, q (σ x) = q x) →
      (∀ x : M, (σ x : U) - x ∈ J) → Cond56 q J → ∃ g : U ≃ₗ[Rt] U, InS q J g ∧ ∀ x : M, g x = σ x := by
  induction r with
  | zero =>
    intro L J M N h1 hML hNL hfree hfin hr h2a h2b σ hσq hσJ he
    have b := Module.finBasisOfFinrankEq R M hr
    refine ⟨LinearEquiv.refl Rt U, InS.refl, fun x => ?_⟩
    have hx : x = 0 := by
      rw [← b.sum_repr x]; simp
    subst hx
    simp
  | succ r ih =>
    intro L J M N h1 hML hNL hfree hfin hr h2a h2b σ hσq hσJ he
    classical
    obtain ⟨e, heJ, heu, he2⟩ := he
    have he' : Cond56 q J := ⟨e, heJ, heu, he2⟩
    set φ := phiE hinj h1 hML heJ with hφ
    have ihM0 : ∀ {M0 : Submodule R U}, Module.Free R M0 → Module.Finite R M0 → finrank R M0 = r → M0 ≤ L →
        ∀ (N0 : Submodule R U) (σ0 : M0 ≃ₗ[R] N0), N0 ≤ L → Cond2 q J M0 → Cond2 q J N0 →
        (∀ x, q (σ0 x) = q x) → (∀ x : M0, (σ0 x : U) - x ∈ J) →
        ∃ g : U ≃ₗ[Rt] U, InS q J g ∧ ∀ x : M0, g x = σ0 x :=
      fun hf hfi hr0 hM0L N0 σ0 hN0L h2a0 h2b0 hq0 hJ0 => ih h1 hM0L hN0L hf hfi hr0 h2a0 h2b0 σ0 hq0 hJ0 he'
    by_cases hA : ∃ x0 : M, IsUnit (φ x0)
    · -- Case A: $M_0 = \{x : b(x, e) = 0\}$, $e_0 = e$
      obtain ⟨x0, u, hu⟩ := hA
      let K := LinearMap.ker φ
      let a : M →ₗ[R] R := (↑u⁻¹ : R) • φ
      have ha : ∀ x, a x = (↑u⁻¹ : R) * φ x := fun x => rfl
      have hax0 : a x0 = 1 := by rw [ha, ← hu, Units.inv_mul]
      let π : M →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - a.smulRight x0) (fun x => by
        rw [LinearMap.mem_ker]
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
          smul_eq_mul]
        rw [ha, ← hu, mul_assoc, mul_comm (φ x) (u : R), ← mul_assoc, Units.inv_mul, one_mul, sub_self])
      have hπ : ∀ x, (π x : M) = x - a x • x0 := fun x => rfl
      have hπK : π ∘ₗ K.subtype = LinearMap.id := by
        apply LinearMap.ext
        intro k
        apply Subtype.ext
        show (π (k : M) : M) = k
        rw [hπ]
        have : φ k = 0 := k.2
        simp [ha, this]
      have hproj : Module.Projective R K := Module.Projective.of_split K.subtype π hπK
      have hKfin : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, by
        have := LinearMap.congr_fun hπK k
        simpa using this⟩)
      have hKfree : Module.Free R K := Module.free_of_flat_of_isLocalRing
      -- $M \cong K \times R$
      let eMK : M ≃ₗ[R] K × R :=
        { toFun := fun x => (π x, a x)
          invFun := fun p => (p.1 : M) + p.2 • x0
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp
          left_inv := fun x => by simp [hπ]
          right_inv := fun p => by
            have hk : φ (p.1 : M) = 0 := p.1.2
            have hak : a (p.1 : M) = 0 := by rw [ha, hk, mul_zero]
            have hat : a (p.2 • x0) = p.2 := by rw [map_smul, hax0, smul_eq_mul, mul_one]
            ext
            · show ((π ((p.1 : M) + p.2 • x0) : M) : U) = ((p.1 : M) : U)
              rw [hπ, map_add, hak, hat, zero_add]
              simp
            · show a ((p.1 : M) + p.2 • x0) = p.2
              rw [map_add, hak, hat, zero_add] }
      have hKr : finrank R K = r := by
        have := eMK.finrank_eq
        rw [Module.finrank_prod, Module.finrank_self, hr] at this
        omega
      let M0 : Submodule R U := K.map M.subtype
      let eK : K ≃ₗ[R] M0 := Submodule.equivMapOfInjective M.subtype M.injective_subtype K
      have hM0free : Module.Free R M0 := Module.Free.of_equiv eK
      have hM0fin : Module.Finite R M0 := Module.Finite.equiv eK
      have hM0r : finrank R M0 = r := by rw [← eK.finrank_eq, hKr]
      have hM0L : M0 ≤ L := (Submodule.map_subtype_le M K).trans hML
      have hmemM0 : ∀ x : M, (x : U) ∈ M0 ↔ φ x = 0 := by
        intro x
        constructor
        · rintro ⟨y, hy, hyx⟩
          have : y = x := Subtype.ext hyx
          rw [← this]; exact hy
        · intro hx; exact ⟨x, hx, rfl⟩
      let S : Split M M0 (x0 : U) :=
        { le := Submodule.map_subtype_le M K
          mem := x0.2
          a := a
          a_m := by simpa using hax0
          a_zero := fun x hx => by rw [ha, (hmemM0 x).mp hx, mul_zero]
          dec := fun x => by
            have := (hmemM0 (π x : M)).mpr (π x).2
            rw [hπ] at this
            simpa using this }
      have he0 : Cond56 q (perpIn q J M0) := by
        refine ⟨e, ⟨heJ, fun x hx => ?_⟩, heu, fun hk z hz => he2 hk z hz.1⟩
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Submodule.subtype_apply, ← phiE_spec hinj h1 hML heJ y]
        have : φ y = 0 := hy
        rw [← hφ, this, map_zero]
      exact assertion_step hinj h1 hML hNL h2a h2b σ hσq hσJ S he0 (ihM0 hM0free hM0fin hM0r hM0L)
    · -- Case B: $b(M, e) \subseteq P$
      push_neg at hA
      have hP : ∀ x : M, φ x ∈ maximalIdeal R := fun x => (mem_maximalIdeal _).mpr (hA x)
      let b := Module.finBasisOfFinrankEq R M hr
      let v : Fin r → U := fun i => (b i.succ : U)
      have hli : LinearIndependent R v :=
        (b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)).comp Fin.succ (Fin.succ_injective _)
      let M0 : Submodule R U := Submodule.span R (Set.range v)
      let bM0 : Basis (Fin r) R M0 := Basis.span hli
      have hM0free : Module.Free R M0 := Module.Free.of_basis bM0
      have hM0fin : Module.Finite R M0 := Module.Finite.of_basis bM0
      have hM0r : finrank R M0 = r := by rw [Module.finrank_eq_card_basis bM0, Fintype.card_fin]
      have hM0M : M0 ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (b i.succ).2)
      have hM0L : M0 ≤ L := hM0M.trans hML
      -- coordinates
      have hcoord0 : ∀ x : M, (x : U) ∈ M0 → b.coord 0 x = 0 := by
        intro x hx
        have hx' : x ∈ Submodule.span R (Set.range (b ∘ Fin.succ)) := by
          have : M0 = (Submodule.span R (Set.range (b ∘ Fin.succ))).map M.subtype := by
            rw [Submodule.map_span, ← Set.range_comp]; rfl
          rw [this] at hx
          obtain ⟨y, hy, hyx⟩ := hx
          rw [← Subtype.ext hyx]; exact hy
        clear hx
        induction hx' using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          simp [Basis.coord_apply, Finsupp.single_apply, Fin.succ_ne_zero]
        | zero => simp
        | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
        | smul c y _ hy => rw [map_smul, hy, smul_zero]
      have hdec : ∀ x : M, (x : U) - b.coord 0 x • (b 0 : U) ∈ M0 := by
        intro x
        have hsum := b.sum_repr x
        rw [Fin.sum_univ_succ] at hsum
        have : (x : U) - b.coord 0 x • (b 0 : U) = ∑ i : Fin r, b.repr x i.succ • v i := by
          conv_lhs => rw [← hsum]
          simp [v, Basis.coord_apply]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      let S : Split M M0 (b 0 : U) :=
        { le := hM0M
          mem := (b 0).2
          a := b.coord 0
          a_m := by simp [Basis.coord_apply]
          a_zero := hcoord0
          dec := hdec }
      -- dual vectors and $e_0$
      have hdual : ∀ i : Fin r, ∃ h ∈ J, ∀ x : M, algebraMap R Rt (b.coord i.succ x) = polar q (x : U) h :=
        fun i => h2a (b.coord i.succ)
      choose hv hvJ hvx using hdual
      obtain ⟨hyJ, hyq, hyp⟩ := rs_sum_P hinj h1 Finset.univ (fun i => φ (b i.succ)) (fun i => hP _) hv hvJ
      set y := ∑ i, φ (b i.succ) • hv i with hy
      have he0J : (-1 : R) • y + e ∈ J := J.add_mem (J.smul_mem _ hyJ) heJ
      have he0 : Cond56 q (perpIn q J M0) := by
        refine ⟨(-1 : R) • y + e, ⟨he0J, fun x hx => ?_⟩, ?_, fun hk z hz => ?_⟩
        · induction hx using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨j, rfl⟩ := hw
            have h1' : polar q (v j) e = algebraMap R Rt (φ (b j.succ)) := (phiE_spec hinj h1 hML heJ _).symm
            have h2' : polar q (v j) y = algebraMap R Rt (φ (b j.succ)) := by
              rw [hy, ← polarBilin_apply_apply, map_sum]
              have : ∀ i, polar q (v j) (φ (b i.succ) • hv i) =
                  algebraMap R Rt (φ (b i.succ)) * algebraMap R Rt (b.coord i.succ (b j.succ)) := by
                intro i
                rw [← algebraMap_smul Rt (φ (b i.succ)) (hv i), polar_smul_right, smul_eq_mul, hvx i (b j.succ)]
              simp only [polarBilin_apply_apply] at *
              rw [Finset.sum_congr rfl fun i _ => this i]
              simp [Basis.coord_apply, Finsupp.single_apply]
            rw [polar_add_right, ← algebraMap_smul Rt (-1 : R) y, polar_smul_right, h1', h2', smul_eq_mul, map_neg,
              map_one]
            ring
          | zero => simp
          | add w w' _ _ hw hw' => rw [polar_add_left, hw, hw', add_zero]
          | smul c w _ hw => rw [← algebraMap_smul Rt c w, polar_smul_left, hw, smul_zero]
        · have hr : rs R (q ((-1 : R) • y + e)) = rs R (q e) := by
            rw [rs_q_smul_add hinj h1.le h1.qJ h1.LJ hyJ heJ, hyq, hyp e (h1.le heJ)]; ring
          have hqe0 := h1.qJ _ he0J
          apply (rs_ne_zero_iff hinj hqe0).mp
          rw [hr]
          exact (rs_ne_zero_iff hinj (h1.qJ e heJ)).mpr heu
        · rw [rs_polar_smul_add hinj h1.le h1.qJ h1.LJ (h1.le hz.1) hyJ heJ, hyp z (h1.le hz.1),
            he2 hk z hz.1]; ring
      exact assertion_step hinj h1 hML hNL h2a h2b σ hσq hσJ S he0 (ihM0 hM0free hM0fin hM0r hM0L)

end QuadFormsKB.Kitaoka.Kneser
