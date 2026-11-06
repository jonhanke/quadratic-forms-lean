/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelFormsIdeals
import QuadFormsKB.Literature.Hanke2011Structure.CMKneser

open NumberField NumberField.Units NumberField.IsCMField Module
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.CMUnits

set_option linter.unusedSectionVars false

noncomputable section

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-! ### Complex conjugation and the relative norm -/

theorem complexConj_eq_conj :
    complexConj K = QuadFormsKB.Binary.Rel.conj (maximalRealSubfield K) K := by
  rcases QuadFormsKB.Binary.Rel.eq_one_or_eq_conj (maximalRealSubfield K) K (complexConj K) with h | h
  · exact absurd h (complexConj_ne_one K)
  · exact h

/-- $N_{K/K^+}(\alpha) = \alpha\bar\alpha$ for Mathlib's integral norm `Algebra.intNorm`. -/
theorem algebraMap_intNorm_cm (α : 𝓞 K) :
    algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)
      (Algebra.intNorm (𝓞 (maximalRealSubfield K)) (𝓞 K) α) = α * ringOfIntegersComplexConj K α := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield K)) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield K)) (maximalRealSubfield K) K,
    Algebra.algebraMap_intNorm (L := K), QuadFormsKB.Binary.Rel.algebraMap_norm, ← complexConj_eq_conj]
  rfl

/-! ### $I\bar I = N_{K/F}(I)\mathcal O_K$ -/

/-- The ring of integers of $F = K^+$. -/
abbrev OF : Type _ := 𝓞 (maximalRealSubfield K)

/-- The conjugate ideal $\bar I$. -/
def conjI (I : Ideal (𝓞 K)) : Ideal (𝓞 K) := I.map (ringOfIntegersComplexConj K)

theorem mul_conjI_span (α : 𝓞 K) :
    Ideal.span {α} * conjI K (Ideal.span {α}) =
      (Ideal.relNorm (OF K) (Ideal.span {α})).map (algebraMap (OF K) (𝓞 K)) := by
  rw [conjI, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton,
    Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton, algebraMap_intNorm_cm]

/-- $I\bar I = N_{K/F}(I)\mathcal O_K$ for every ideal $I$ of $\mathcal O_K$. -/
theorem mul_conjI (I : Ideal (𝓞 K)) :
    I * conjI K I = (Ideal.relNorm (OF K) I).map (algebraMap (OF K) (𝓞 K)) := by
  by_cases h0 : I = ⊥
  · subst h0
    simp [conjI]
  set n := Fintype.card (ClassGroup (𝓞 K))
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hmem : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero h0
  have hp : (I ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hmem n)]
    have : ClassGroup.mk0 (⟨I, hmem⟩ ^ n) = 1 := by rw [map_pow, pow_card_eq_one]
    simpa using this
  obtain ⟨α, hα⟩ := hp
  refine QuadFormsKB.Binary.Rel.ideal_pow_left_injective hn ?_
  rw [mul_pow, conjI, ← Ideal.map_pow, ← conjI, ← Ideal.map_pow, ← map_pow, hα]
  exact mul_conjI_span K α

theorem relNorm_conjI (I : Ideal (𝓞 K)) : Ideal.relNorm (OF K) (conjI K I) = Ideal.relNorm (OF K) I :=
  Ideal.relNorm_map_algEquiv _ I

/-! ### The monoid of pairs and the group -/

/-- The relative norm $N_{K/F} : \mathcal O_K \to \mathcal O_F$ (Mathlib's `Algebra.intNorm`). -/
abbrev nrm (x : 𝓞 K) : OF K := Algebra.intNorm (OF K) (𝓞 K) x

theorem nrm_mul (x y : 𝓞 K) : nrm K (x * y) = nrm K x * nrm K y := map_mul _ _ _

theorem nrm_ne_zero {x : 𝓞 K} (hx : x ≠ 0) : nrm K x ≠ 0 := by
  intro h
  have this : Ideal.relNorm (OF K) (Ideal.span {x}) = Ideal.span {nrm K x} :=
    Ideal.relNorm_singleton (OF K) x
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at this
  have := Ideal.relNorm_eq_bot_iff.mp this
  exact hx (Ideal.span_singleton_eq_bot.mp this)

theorem nrm_algebraMap (r : OF K) : nrm K (algebraMap (OF K) (𝓞 K) r) = r * r := by
  apply FaithfulSMul.algebraMap_injective (OF K) (𝓞 K)
  rw [algebraMap_intNorm_cm, map_mul]
  simp

/-- The monoid of pairs $(I, a)$: $I \neq 0$ an ideal of $\mathcal O_K$, $a \in \mathcal O_F$ with
$N_{K/F}(I) = a\mathcal O_F$. -/
def kneserMonoid : Submonoid (Ideal (𝓞 K) × OF K) where
  carrier := {p | p.1 ≠ ⊥ ∧ Ideal.relNorm (OF K) p.1 = Ideal.span {p.2}}
  mul_mem' := by
    rintro ⟨I, a⟩ ⟨J, b⟩ ⟨hI, hIa⟩ ⟨hJ, hJb⟩
    refine ⟨mul_ne_zero hI hJ, ?_⟩
    simp only [Prod.mk_mul_mk] at hIa hJb ⊢
    rw [map_mul, hIa, hJb, Ideal.span_singleton_mul_span_singleton]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · exact one_ne_zero
    · simp

/-- The pair $(x\mathcal O_K, N_{K/F}x)$, $x \neq 0$. -/
def prin (x : 𝓞 K) (hx : x ≠ 0) : kneserMonoid K :=
  ⟨(Ideal.span {x}, nrm K x), by
    refine ⟨?_, ?_⟩
    · simpa using hx
    · simp⟩

/-- The submonoid of principal pairs $(x\mathcal O_K, N_{K/F}x)$. -/
def kneserPrincipal : Submonoid (kneserMonoid K) where
  carrier := {p | ∃ (x : 𝓞 K) (hx : x ≠ 0), p = prin K x hx}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, mul_ne_zero hx hy, ?_⟩
    apply Subtype.ext
    simp [prin, nrm_mul, Ideal.span_singleton_mul_span_singleton]
  one_mem' := by
    refine ⟨1, one_ne_zero, ?_⟩
    apply Subtype.ext
    simp [prin, Prod.ext_iff]

/-- The congruence $s \sim t$ iff $s p = t q$ for principal pairs $p, q$. -/
def kneserCon : Con (kneserMonoid K) where
  r s t := ∃ p ∈ kneserPrincipal K, ∃ q ∈ kneserPrincipal K, s * p = t * q
  iseqv := by
    refine ⟨fun s => ⟨1, one_mem _, 1, one_mem _, rfl⟩, ?_, ?_⟩
    · rintro s t ⟨p, hp, q, hq, h⟩
      exact ⟨q, hq, p, hp, h.symm⟩
    · rintro s t u ⟨p, hp, q, hq, h⟩ ⟨p', hp', q', hq', h'⟩
      refine ⟨p * p', mul_mem hp hp', q * q', mul_mem hq hq', ?_⟩
      calc s * (p * p') = (s * p) * p' := by rw [mul_assoc]
        _ = (t * q) * p' := by rw [h]
        _ = (t * p') * q := by rw [mul_assoc, mul_comm q p', ← mul_assoc]
        _ = (u * q') * q := by rw [h']
        _ = u * (q * q') := by rw [mul_assoc, mul_comm q' q]
  mul' := by
    rintro s s' t t' ⟨p, hp, q, hq, h⟩ ⟨p', hp', q', hq', h'⟩
    refine ⟨p * p', mul_mem hp hp', q * q', mul_mem hq hq', ?_⟩
    calc s * t * (p * p') = (s * p) * (t * p') := mul_mul_mul_comm _ _ _ _
      _ = (s' * q) * (t' * q') := by rw [h, h']
      _ = s' * t' * (q * q') := mul_mul_mul_comm _ _ _ _

/-- **Kneser's group $G(\mathcal O_K)$, ideal-theoretic form** (Hanke 2011, Lemma 8.3, p. 34; Kneser 1982, §6), for a CM
field $K$ with $F = K^+$.

Elements are classes $[(I, a)]$ of pairs with $I \subseteq \mathcal O_K$ a nonzero ideal and $a \in \mathcal O_F$ such that
$N_{K/F}(I) = a\,\mathcal O_F$ (Mathlib's `Ideal.relNorm`), multiplied componentwise, modulo the principal pairs
$(x\mathcal O_K, N_{K/F}(x))$, $x \in \mathcal O_K \setminus\{0\}$: $(I,a) \sim (J,b)$ iff $(I,a)(x\mathcal O_K, N x) =
(J,b)(y\mathcal O_K, N y)$ for some such $x, y$. The inverse of $[(I,a)]$ is $[(\bar I, a)]$ (since $I\bar I = N_{K/F}(I)\mathcal O_K$,
`mul_conjI`). This is the group of pairs (invertible fractional ideal $I$, $a \in F^\times$) with $N_{K/F}(I) = a\mathcal O_F$
modulo $\{(xO_K, N x) : x \in K^\times\}$, written with integral representatives (every class has one: clear denominators by
multiplying by $(c\mathcal O_K, N c)$).

A lattice-theoretic element $(L, Q)$ of Lemma 8.3 (a primitive binary $\mathcal O_F$-lattice $L$ that is a rank-one
$\mathcal O_K$-module, $Q(x) = N(x)/a$) corresponds to the pair $(I, a)$. *Not formalized:* the comparison between this
group and the lattice-theoretic group $G(\mathcal O_K)$ of Lemma 8.3 (the equivalence of the two descriptions is Kneser's). -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (G(O_K), ideal-theoretic form; Kneser 1982 §6)"]
def KneserGroup : Type _ := (kneserCon K).Quotient

instance : CommMonoid (KneserGroup K) := inferInstanceAs (CommMonoid (kneserCon K).Quotient)

/-- The class of a pair. -/
def kmk : kneserMonoid K →* KneserGroup K := (kneserCon K).mk'

theorem kmk_eq_iff (s t : kneserMonoid K) :
    kmk K s = kmk K t ↔ ∃ p ∈ kneserPrincipal K, ∃ q ∈ kneserPrincipal K, s * p = t * q :=
  (kneserCon K).eq

theorem kmk_surjective : Function.Surjective (kmk K) := Con.mk'_surjective (c := kneserCon K)

/-- The inverse of $(I, a)$ is $(\bar I, a)$. -/
def kinv (s : kneserMonoid K) : kneserMonoid K :=
  ⟨(conjI K s.1.1, s.1.2), by
    refine ⟨?_, ?_⟩
    · intro h
      apply s.2.1
      apply (Ideal.relNorm_eq_bot_iff (R := OF K)).mp
      have h' : conjI K s.1.1 = ⊥ := h
      rw [← relNorm_conjI K, h', Ideal.relNorm_bot]
    · exact (relNorm_conjI K _).trans s.2.2⟩

theorem kmk_mul_kinv (s : kneserMonoid K) : kmk K s * kmk K (kinv K s) = 1 := by
  rw [← map_mul, ← map_one (kmk K), kmk_eq_iff]
  have ha : s.1.2 ≠ 0 := by
    intro h
    apply s.2.1
    apply (Ideal.relNorm_eq_bot_iff (R := OF K)).mp
    rw [s.2.2, h, Ideal.span_singleton_eq_bot.mpr rfl]
  have hx : algebraMap (OF K) (𝓞 K) s.1.2 ≠ 0 := by
    intro h
    exact ha (FaithfulSMul.algebraMap_injective (OF K) (𝓞 K) (by rw [h, map_zero]))
  refine ⟨1, one_mem _, prin K _ hx, ⟨_, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show s.1.1 * conjI K s.1.1 * 1 = 1 * Ideal.span {algebraMap (OF K) (𝓞 K) s.1.2}
    rw [mul_one, one_mul, mul_conjI, s.2.2, Ideal.map_span, Set.image_singleton]
  · show s.1.2 * s.1.2 * 1 = 1 * nrm K (algebraMap (OF K) (𝓞 K) s.1.2)
    rw [nrm_algebraMap, mul_one, one_mul]

theorem exists_mul_eq_one (g : KneserGroup K) : ∃ g', g * g' = 1 := by
  obtain ⟨s, rfl⟩ := kmk_surjective K g
  exact ⟨_, kmk_mul_kinv K s⟩

instance : CommGroup (KneserGroup K) :=
  { (inferInstance : CommMonoid (KneserGroup K)) with
    inv := fun g => Classical.choose (exists_mul_eq_one K g)
    inv_mul_cancel := fun g => by
      rw [mul_comm]
      exact Classical.choose_spec (exists_mul_eq_one K g) }

/-! ### The maps $\delta$, $\rho$, $\nu$ -/

/-- The ideal of a pair, as a nonzero ideal. -/
def idlHom : kneserMonoid K →* (Ideal (𝓞 K))⁰ where
  toFun s := ⟨s.1.1, mem_nonZeroDivisors_of_ne_zero s.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- $(I, a) \mapsto [I] \in \mathrm{Cl}(\mathcal O_K)$ on pairs. -/
def rho0 : kneserMonoid K →* ClassGroup (𝓞 K) := ClassGroup.mk0.comp (idlHom K)

theorem span_mem_nonZeroDivisors {x : 𝓞 K} (hx : x ≠ 0) : Ideal.span {x} ∈ (Ideal (𝓞 K))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (by simpa using hx)

theorem rho0_prin (x : 𝓞 K) (hx : x ≠ 0) : rho0 K (prin K x hx) = 1 :=
  (ClassGroup.mk0_eq_one_iff (span_mem_nonZeroDivisors K hx)).mpr ⟨x, rfl⟩

theorem rho0_congr {s t : kneserMonoid K} (h : kneserCon K s t) : rho0 K s = rho0 K t := by
  obtain ⟨p, ⟨x, hx, rfl⟩, q, ⟨y, hy, rfl⟩, h⟩ := h
  have := congrArg (rho0 K) h
  rwa [map_mul, map_mul, rho0_prin, rho0_prin, mul_one, mul_one] at this

/-- $\rho : G \to \mathrm{Cl}(\mathcal O_K)$, $[(I, a)] \mapsto [I]$. -/
def rho : KneserGroup K →* ClassGroup (𝓞 K) :=
  Con.lift (kneserCon K) (rho0 K) (fun _ _ h => rho0_congr K h)

theorem rho_kmk (s : kneserMonoid K) : rho K (kmk K s) = rho0 K s := rfl

/-- The relative norm on nonzero ideals. -/
def nrmIdl : (Ideal (𝓞 K))⁰ →* (Ideal (OF K))⁰ where
  toFun I := ⟨Ideal.relNorm (OF K) (I : Ideal (𝓞 K)), mem_nonZeroDivisors_of_ne_zero
    (fun h => nonZeroDivisors.coe_ne_zero I (Ideal.relNorm_eq_bot_iff.mp h))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' I J := Subtype.ext (by simp)

/-- The norm on nonzero ideals followed by the class map of $\mathcal O_F$. -/
def nu0 : (Ideal (𝓞 K))⁰ →* ClassGroup (OF K) := ClassGroup.mk0.comp (nrmIdl K)

theorem nu0_congr {I J : (Ideal (𝓞 K))⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) : nu0 K I = nu0 K J := by
  obtain ⟨x, y, hx, hy, h⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  have h' := congrArg (Ideal.relNorm (OF K)) h
  rw [map_mul, map_mul, Ideal.relNorm_singleton, Ideal.relNorm_singleton] at h'
  exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨nrm K x, nrm K y, nrm_ne_zero K hx, nrm_ne_zero K hy, h'⟩

/-- **$\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$**, the norm map, $\nu[I] = [N_{K/F}I]$. -/
def nuHom : ClassGroup (𝓞 K) →* ClassGroup (OF K) where
  toFun c := nu0 K (Function.surjInv ClassGroup.mk0_surjective c)
  map_one' := by
    apply (nu0_congr K (by rw [Function.surjInv_eq ClassGroup.mk0_surjective, map_one])).trans
      (map_one _)
  map_mul' c d := by
    rw [← map_mul]
    apply nu0_congr
    rw [Function.surjInv_eq ClassGroup.mk0_surjective, map_mul, Function.surjInv_eq ClassGroup.mk0_surjective,
      Function.surjInv_eq ClassGroup.mk0_surjective]

theorem nuHom_mk0 (I : (Ideal (𝓞 K))⁰) : nuHom K (ClassGroup.mk0 I) = nu0 K I :=
  nu0_congr K (Function.surjInv_eq ClassGroup.mk0_surjective _)

/-- $u \mapsto (\mathcal O_K, u)$ on pairs. -/
def delta0 : (OF K)ˣ →* kneserMonoid K where
  toFun u := ⟨(1, (u : OF K)), by
    refine ⟨one_ne_zero, ?_⟩
    show Ideal.relNorm (OF K) (1 : Ideal (𝓞 K)) = Ideal.span {(u : OF K)}
    rw [map_one, Ideal.one_eq_top, eq_comm, Ideal.span_singleton_eq_top]
    exact u.isUnit⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

/-- The isomorphism $\mathcal O_F^\times \cong$ `realUnits K` (the units of $K^+$ inside $\mathcal O_K^\times$). -/
def realEquiv : (OF K)ˣ ≃* realUnits K := MonoidHom.ofInjective (injective_unitsMap K)

/-- **$\delta : \mathcal O_F^\times \to G$**, $u \mapsto [(\mathcal O_K, u)]$. -/
def delta1 : (OF K)ˣ →* KneserGroup K := (kmk K).comp (delta0 K)

/-- **$\delta : \mathcal O_F^\times \to G$** on `realUnits K`. -/
def delta : realUnits K →* KneserGroup K := (delta1 K).comp (realEquiv K).symm.toMonoidHom

theorem unitsNorm_val (w : (𝓞 K)ˣ) :
    ((unitsNorm K w : (𝓞 K)ˣ) : 𝓞 K) = (w : 𝓞 K) * ringOfIntegersComplexConj K w := rfl

theorem delta1_eq_one_iff (u : (OF K)ˣ) :
    delta1 K u = 1 ↔ ∃ w : (𝓞 K)ˣ, ((unitsNorm K w : (𝓞 K)ˣ) : 𝓞 K) = algebraMap (OF K) (𝓞 K) u := by
  rw [delta1, MonoidHom.comp_apply, ← map_one (kmk K), kmk_eq_iff]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, h⟩
    have h1 : (1 : Ideal (𝓞 K)) * Ideal.span {x} = 1 * Ideal.span {y} :=
      congrArg (fun z : kneserMonoid K => z.1.1) h
    have h2 : (u : OF K) * nrm K x = 1 * nrm K y := congrArg (fun z : kneserMonoid K => z.1.2) h
    rw [one_mul, one_mul] at h1
    rw [one_mul] at h2
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp h1
    rw [← hw, nrm_mul, mul_comm] at h2
    have hu : (u : OF K) = nrm K (w : 𝓞 K) := mul_left_cancel₀ (nrm_ne_zero K hx) h2
    refine ⟨w, ?_⟩
    rw [unitsNorm_val, ← algebraMap_intNorm_cm, hu]
  · rintro ⟨w, hw⟩
    refine ⟨1, one_mem _, prin K (w : 𝓞 K) w.ne_zero, ⟨_, w.ne_zero, rfl⟩, ?_⟩
    have hn : nrm K (w : 𝓞 K) = u :=
      FaithfulSMul.algebraMap_injective (OF K) (𝓞 K) ((algebraMap_intNorm_cm K w).trans hw)
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show (1 : Ideal (𝓞 K)) * 1 = 1 * Ideal.span {(w : 𝓞 K)}
      rw [Ideal.span_singleton_eq_top.mpr w.isUnit, Ideal.one_eq_top]
    · show (u : OF K) * 1 = 1 * nrm K (w : 𝓞 K)
      rw [hn]; simp

/-- $\ker\delta = N_{K/F}(\mathcal O_K^\times)$. -/
theorem ker_delta : (delta K).ker = (unitsNorm K).range.subgroupOf (realUnits K) := by
  ext r
  obtain ⟨u, rfl⟩ := (realEquiv K).surjective r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have : delta K (realEquiv K u) = delta1 K u := by simp [delta]
  rw [this, delta1_eq_one_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, Units.ext hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, congrArg Units.val hw⟩

theorem rho_delta (u : (OF K)ˣ) : rho K (delta1 K u) = 1 := by
  show ClassGroup.mk0 (idlHom K (delta0 K u)) = 1
  have : idlHom K (delta0 K u) = 1 := Subtype.ext rfl
  rw [this, map_one]

/-- $\operatorname{im}\delta = \ker\rho$. -/
theorem range_delta : (delta K).range = (rho K).ker := by
  ext g
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨u, rfl⟩ := (realEquiv K).surjective r
    have : delta K (realEquiv K u) = delta1 K u := by simp [delta]
    rw [MonoidHom.mem_ker, this]
    exact rho_delta K u
  · intro hg
    obtain ⟨s, rfl⟩ := kmk_surjective K g
    rw [MonoidHom.mem_ker, rho_kmk] at hg
    have hp : (s.1.1).IsPrincipal := (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero s.2.1)).mp hg
    set x := Submodule.IsPrincipal.generator s.1.1 with hxdef
    have hI : Ideal.span {x} = s.1.1 := Ideal.span_singleton_generator _
    have hx : x ≠ 0 := fun h => s.2.1 (by rw [← hI, h]; simp)
    have hN : Ideal.span {nrm K x} = Ideal.span {s.1.2} := by
      rw [← s.2.2, ← hI]
      exact (Ideal.relNorm_singleton (OF K) x).symm
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hN
    refine ⟨realEquiv K v, ?_⟩
    have : delta K (realEquiv K v) = delta1 K v := by simp [delta]
    rw [this, delta1, MonoidHom.comp_apply, kmk_eq_iff]
    refine ⟨prin K x hx, ⟨x, hx, rfl⟩, 1, one_mem _, ?_⟩
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show (1 : Ideal (𝓞 K)) * Ideal.span {x} = s.1.1 * 1
      rw [one_mul, mul_one, hI]
    · show (v : OF K) * nrm K x = s.1.2 * 1
      rw [mul_one, mul_comm]; exact hv

/-- $\operatorname{im}\rho = \ker\nu$. -/
theorem range_rho : (rho K).range = (nuHom K).ker := by
  ext c
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨s, rfl⟩ := kmk_surjective K g
    rw [MonoidHom.mem_ker, rho_kmk]
    show nuHom K (ClassGroup.mk0 (idlHom K s)) = 1
    rw [nuHom_mk0]
    refine (ClassGroup.mk0_eq_one_iff (nrmIdl K (idlHom K s)).2).mpr ?_
    show (Ideal.relNorm (OF K) s.1.1).IsPrincipal
    rw [s.2.2]
    exact ⟨s.1.2, rfl⟩
  · intro hc
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    rw [MonoidHom.mem_ker, nuHom_mk0] at hc
    have hp : (Ideal.relNorm (OF K) (I : Ideal (𝓞 K))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (nrmIdl K I).2).mp hc
    set a := Submodule.IsPrincipal.generator (Ideal.relNorm (OF K) (I : Ideal (𝓞 K)))
    have hI : Ideal.span {a} = Ideal.relNorm (OF K) (I : Ideal (𝓞 K)) := Ideal.span_singleton_generator _
    exact ⟨kmk K ⟨((I : Ideal (𝓞 K)), a), nonZeroDivisors.coe_ne_zero I, hI.symm⟩, rfl⟩

/-- **Surjectivity of the norm on class groups of a CM extension** (input). For a CM field $K$ with $F = K^+$, the norm
$\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$, $[I] \mapsto [N_{K/F} I]$ (`nuHom`), is surjective.
Washington, *Introduction to cyclotomic fields*, Thm. 10.1, p. 184: the norm on class groups of $K/F$ is surjective iff
$K \cap H_F = F$, $H_F$ the Hilbert class field of $F$; this holds for CM extensions because $K/F$ is ramified at the
infinite places while $H_F/F$ is unramified there. The proof uses class field theory, which is not in the library, so this
is a named input. It is a statement about class groups only, not about Kneser's group, and is not equivalent to the
conclusion of Lemma 8.4. -/
@[kb "washington1997" "Thm. 10.1, p. 184 (norm on class groups surjective iff K ∩ H_F = F; CM extensions)"]
structure CMNormSurjective : Prop where
  surjective : Function.Surjective (nuHom K)

/-- **Kneser's exact sequence** for the concrete group `KneserGroup K`, conditional on `CMNormSurjective K`:
$\mathcal O_K^\times \xrightarrow{N} \mathcal O_F^\times \xrightarrow{\delta} G \xrightarrow{\rho} \mathrm{Cl}(\mathcal O_K)
\xrightarrow{\nu} \mathrm{Cl}(\mathcal O_F) \to 1$ is exact (`ker_delta`, `range_delta`, `range_rho`). -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (Kneser's exact sequence for G(O_K))"]
theorem kneserSequence_of_normSurjective (H : CMNormSurjective K) : KneserSequence K (KneserGroup K) :=
  ⟨⟨delta K, rho K, nuHom K, ker_delta K, range_delta K, range_rho K, H.surjective⟩⟩

/-- **Lemma 8.4** (Hanke 2011, p. 35) for the concrete group $G = $ `KneserGroup K`, conditional only on the class-field-theory
input `CMNormSurjective K`:
$$|G|\cdot h(\mathcal O_F)\cdot Q_{K/F} = h(\mathcal O_K)\cdot 2^{[F:\mathbb Q]}.$$ -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4_kneser (H : CMNormSurjective K) :
    Nat.card (KneserGroup K) * classNumber (maximalRealSubfield K) * indexRealUnits K =
      classNumber K * 2 ^ finrank ℚ (maximalRealSubfield K) :=
  lemma_8_4 K (kneserSequence_of_normSurjective K H)

/-- **Lemma 8.4** in the paper's form, for `KneserGroup K`, conditional on `CMNormSurjective K`:
$|G| = \dfrac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\dfrac{2^{[F:\mathbb Q]}}{Q_{K/F}}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4_kneser_div (H : CMNormSurjective K) :
    (Nat.card (KneserGroup K) : ℚ) = (classNumber K : ℚ) / classNumber (maximalRealSubfield K) *
      (2 ^ finrank ℚ (maximalRealSubfield K) / indexRealUnits K) :=
  lemma_8_4_div K (kneserSequence_of_normSurjective K H)

end

end QuadFormsKB.Hanke2011Structure.CMUnits

#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.kneserSequence_of_normSurjective
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_kneser
#print axioms QuadFormsKB.Hanke2011Structure.CMUnits.lemma_8_4_kneser_div
