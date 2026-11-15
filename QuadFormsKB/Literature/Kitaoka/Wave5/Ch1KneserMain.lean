/-
# Kitaoka 1993, Theorem 1.2.2 (Kneser's theorem of Witt type): the proof

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.2, Theorem 1.2.2 and the end of its proof
("Proof of Theorem 1.2.2"), pp. 6–10 (printed pages). The statement `Kitaoka.Theorem122` is in `Ch1Spaces.lean`.

**Proves** `theorem122 : Theorem122` (unconditional).

**Proof** (Kitaoka's). Adjoin a hyperbolic plane: $U' = U \perp V$ with $V = \tilde R^2$, $q(a, b) = ab$,
$v_1 = (1, 0)$, $v_2 = (0, 1)$; $L' = L \perp (Rv_1 + Rv_2)$, $M' = M \perp Rv_1$, $N' = N \perp Rv_1$,
$H' = H \perp R(v_1 + v_2)$, $\sigma' = \sigma \perp \mathrm{id}$. Then (1), (2), (3) hold for the primed data, and
$e = v_1 + v_2 \in H'$ has $q(e) = 1$ and $b(e, H') = 2R \subseteq P$ when $\#\bar R = 2$, which is (5), (6). Assertion 1
(`assertion1`) gives $\tau \in S(H')$ with $\tau = \sigma'$ on $M'$; $\tau$ fixes $v_1$ and $v_1 - v_2 \in H'^\perp$,
hence $v_2$, hence maps $U = \{v_1, v_2\}^\perp$ to itself, and its restriction to $L$ is the required isometry.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1KneserAssertion
import QuadFormsKB.Literature.Kitaoka.Ch1Spaces

open QuadraticMap IsLocalRing Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Kneser

variable {R Rt U : Type} [CommRing R] [IsLocalRing R] [CommRing Rt] [Algebra R Rt]
  [AddCommGroup U] [Module Rt U] [Module R U] [IsScalarTower R Rt U]

/-- The hyperbolic plane $(a, b) \mapsto ab$ over $\tilde R$. -/
def hypRt : QuadraticForm Rt (Rt × Rt) := QuadraticMap.linMulLin (LinearMap.fst Rt Rt Rt) (LinearMap.snd Rt Rt Rt)

@[simp] theorem hypRt_apply (w : Rt × Rt) : hypRt w = w.1 * w.2 := rfl

theorem polar_hypRt (w w' : Rt × Rt) : polar hypRt w w' = w.1 * w'.2 + w'.1 * w.2 := by
  simp only [polar, hypRt_apply, Prod.fst_add, Prod.snd_add]; ring

theorem polar_prod' (q : QuadraticForm Rt U) (p p' : U × (Rt × Rt)) :
    polar (q.prod hypRt) p p' = polar q p.1 p'.1 + polar hypRt p.2 p'.2 := by
  simp only [polar, QuadraticMap.prod_apply, Prod.fst_add, Prod.snd_add]; ring

/-- In a residue field with two elements, $2 = 0$. -/
theorem two_eq_zero_of_card_two {k : Type} [Field k] (h : Nat.card k = 2) : (2 : k) = 0 := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp h
  have h01 : ∀ t : k, t = 0 ∨ t = 1 := by
    intro t
    have hx : (0 : k) ∈ ({x, y} : Set k) := hset ▸ Set.mem_univ _
    have hy : (1 : k) ∈ ({x, y} : Set k) := hset ▸ Set.mem_univ _
    have ht : t ∈ ({x, y} : Set k) := hset ▸ Set.mem_univ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ht
    rcases hx with rfl | rfl <;> rcases hy with h1 | h1 <;> rcases ht with rfl | rfl <;> simp_all
  rcases h01 2 with h | h
  · exact h
  · exfalso
    have : (1 : k) = 0 := by linear_combination h
    exact one_ne_zero this

section Main

variable (q : QuadraticForm Rt U) (hinj : Function.Injective (algebraMap R Rt))

/-- $Rv_1 \subseteq \tilde R^2$. -/
abbrev lineA : Submodule R (Rt × Rt) := R ∙ ((1 : Rt), (0 : Rt))
/-- $R(v_1 + v_2) \subseteq \tilde R^2$. -/
abbrev lineE : Submodule R (Rt × Rt) := R ∙ ((1 : Rt), (1 : Rt))
/-- $Rv_1 + Rv_2 \subseteq \tilde R^2$. -/
abbrev planeW : Submodule R (Rt × Rt) :=
  LinearMap.range ((Algebra.linearMap R Rt).prodMap (Algebra.linearMap R Rt))

theorem smul_v1 (s : R) : s • ((1 : Rt), (0 : Rt)) = (algebraMap R Rt s, 0) := by
  ext <;> simp [Algebra.smul_def]

theorem smul_e (s : R) : s • ((1 : Rt), (1 : Rt)) = (algebraMap R Rt s, algebraMap R Rt s) := by
  ext <;> simp [Algebra.smul_def]

theorem mem_planeW {w : Rt × Rt} : w ∈ (planeW : Submodule R (Rt × Rt)) ↔
    ∃ a b : R, w = (algebraMap R Rt a, algebraMap R Rt b) := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), rfl⟩

theorem lineE_le_planeW : (lineE : Submodule R (Rt × Rt)) ≤ planeW := by
  intro w hw
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [smul_e]; exact mem_planeW.mpr ⟨s, s, rfl⟩

theorem lineA_le_planeW : (lineA : Submodule R (Rt × Rt)) ≤ planeW := by
  intro w hw
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [smul_v1]; exact mem_planeW.mpr ⟨s, 0, by simp⟩

/-- Condition (1) for the primed data. -/
theorem cond1_prime {L H : Submodule R U} (hHL : H ≤ L) (h1q : ∀ h ∈ H, q h ∈ (algebraMap R Rt).range)
    (h1b : ∀ x ∈ L, ∀ h ∈ H, polar q x h ∈ (algebraMap R Rt).range) :
    Cond1 (q.prod hypRt) (L.prod planeW) (H.prod lineE) := by
  refine ⟨Submodule.prod_mono hHL lineE_le_planeW, ?_, ?_⟩
  · rintro ⟨h, w⟩ ⟨hh, hw⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [smul_e, QuadraticMap.prod_apply, hypRt_apply]
    exact (algebraMap R Rt).range.add_mem (h1q h hh) ⟨s * s, by simp⟩
  · rintro ⟨x, w⟩ ⟨hx, hw⟩ ⟨h, w'⟩ ⟨hh, hw'⟩
    obtain ⟨a, b, rfl⟩ := mem_planeW.mp hw
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    rw [smul_e, polar_prod', polar_hypRt]
    exact (algebraMap R Rt).range.add_mem (h1b x hx h hh) ⟨a * s + s * b, by simp⟩

/-- Condition (2) for $X \perp Rv_1$. -/
theorem cond2_prime {H X : Submodule R U}
    (h2 : ∀ f : X →ₗ[R] R, ∃ y ∈ H, ∀ x : X, algebraMap R Rt (f x) = polar q x y) :
    Cond2 (q.prod hypRt) (H.prod lineE) (X.prod lineA) := by
  intro f
  let i0 : X →ₗ[R] X.prod lineA :=
    { toFun := fun x => ⟨((x : U), (0 : Rt × Rt)), ⟨x.2, Submodule.zero_mem _⟩⟩
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun c x => by ext <;> simp }
  obtain ⟨y, hy, hy'⟩ := h2 (f ∘ₗ i0)
  have hv1 : ((0 : U), ((1 : Rt), (0 : Rt))) ∈ X.prod lineA :=
    ⟨X.zero_mem, Submodule.mem_span_singleton_self _⟩
  set c := f ⟨_, hv1⟩
  refine ⟨(y, c • ((1 : Rt), (1 : Rt))), ⟨hy, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩,
    fun p => ?_⟩
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_prod.mp p.2).2
  have hp : p = i0 ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩ + s • ⟨_, hv1⟩ := by
    apply Subtype.ext
    ext
    · simp [i0]
    · simp [i0, ← hs]
    · simp [i0, ← hs]
  have h0 := hy' ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩
  rw [LinearMap.comp_apply] at h0
  have key : f p = f (i0 ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩) + s * c := by
    conv_lhs => rw [hp]
    rw [map_add, map_smul, smul_eq_mul]
  have hp2 : (p : U × (Rt × Rt)).2 = (algebraMap R Rt s, 0) := by rw [← hs, smul_v1]
  have e1 : (p : U × (Rt × Rt)).2.1 = algebraMap R Rt s := congrArg Prod.fst hp2
  have e2 : (p : U × (Rt × Rt)).2.2 = 0 := congrArg Prod.snd hp2
  rw [key, map_add, map_mul, polar_prod', smul_e, polar_hypRt, e1, e2, h0]
  simp only [mul_zero, add_zero]

end Main

/-- **Kneser's theorem on $U$** (the form of Theorem 1.2.2 proved here): under the hypotheses of `Theorem122` (only $M$
is used free and finitely generated) there is an $\tilde R$-linear isometry $\tau$ of $U$ with $\tau(L) = L$,
$\tau = \sigma$ on $M$, $\tau = \mathrm{id}$ on $\{x \in L : b(x, H) = 0\}$ and $\tau(x) - x \in H$ for $x \in L$. -/
theorem kneser_U (q : QuadraticForm Rt U) (L M N H : Submodule R U) (hinj : Function.Injective (algebraMap R Rt))
    (hMfg : M.FG) (hMfree : Module.Free R M) (hM : M ≤ L) (hN : N ≤ L) (hH : H ≤ L)
    (h1q : ∀ h ∈ H, q h ∈ (algebraMap R Rt).range)
    (h1b : ∀ x ∈ L, ∀ h ∈ H, polar q x h ∈ (algebraMap R Rt).range)
    (h2a : ∀ f : M →ₗ[R] R, ∃ y ∈ H, ∀ x : M, algebraMap R Rt (f x) = polar q x y)
    (h2b : ∀ f : N →ₗ[R] R, ∃ y ∈ H, ∀ x : N, algebraMap R Rt (f x) = polar q x y)
    (σ : M ≃ₗ[R] N) (hσq : ∀ x, q (σ x) = q x) (hσH : ∀ x, (σ x : U) - x ∈ H) :
    ∃ τ : U ≃ₗ[Rt] U, (∀ x, q (τ x) = q x) ∧ (∀ x ∈ L, τ x ∈ L) ∧ (∀ x ∈ L, τ.symm x ∈ L) ∧
      (∀ x : M, τ x = σ x) ∧ (∀ x ∈ L, (∀ h ∈ H, polar q x h = 0) → τ x = x) ∧ ∀ x ∈ L, τ x - x ∈ H := by
  classical
  set q' : QuadraticForm Rt (U × (Rt × Rt)) := q.prod hypRt with hq'
  have h1' := cond1_prime q hH h1q h1b
  have hM'L : M.prod (lineA (R := R) (Rt := Rt)) ≤ L.prod (planeW (R := R) (Rt := Rt)) := Submodule.prod_mono hM lineA_le_planeW
  have hN'L : N.prod (lineA (R := R) (Rt := Rt)) ≤ L.prod (planeW (R := R) (Rt := Rt)) := Submodule.prod_mono hN lineA_le_planeW
  -- $M' = M \perp Rv_1$ is free and finite
  have hMfin : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  let eM : (M × R) →ₗ[R] M.prod (lineA (R := R) (Rt := Rt)) :=
    { toFun := fun p => ⟨((p.1 : U), p.2 • ((1 : Rt), (0 : Rt))),
        ⟨p.1.2, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩⟩
      map_add' := fun p p' => by ext <;> simp [add_smul]
      map_smul' := fun c p => by ext <;> simp [mul_smul] }
  have heM : Function.Bijective eM := by
    constructor
    · intro p p' h
      have h1 := congrArg (fun z : M.prod (lineA (R := R) (Rt := Rt)) => (z : U × (Rt × Rt)).1) h
      have h2 := congrArg (fun z : M.prod (lineA (R := R) (Rt := Rt)) => (z : U × (Rt × Rt)).2.1) h
      simp only [eM, LinearMap.coe_mk, AddHom.coe_mk, smul_v1] at h1 h2
      exact Prod.ext (Subtype.ext h1) (hinj h2)
    · intro z
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_prod.mp z.2).2
      refine ⟨(⟨(z : U × (Rt × Rt)).1, (Submodule.mem_prod.mp z.2).1⟩, s), Subtype.ext ?_⟩
      ext
      · rfl
      · simp [eM, ← hs]
      · simp [eM, ← hs]
  let eM' : (M × R) ≃ₗ[R] M.prod (lineA (R := R) (Rt := Rt)) := LinearEquiv.ofBijective eM heM
  have hM'free : Module.Free R (M.prod (lineA (R := R) (Rt := Rt))) := Module.Free.of_equiv eM'
  have hM'fin : Module.Finite R (M.prod (lineA (R := R) (Rt := Rt))) := Module.Finite.equiv eM'
  -- $\sigma' = \sigma \perp \mathrm{id}$
  let σ' : M.prod (lineA (R := R) (Rt := Rt)) ≃ₗ[R] N.prod (lineA (R := R) (Rt := Rt)) :=
    { toFun := fun p => ⟨(((σ ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩ : N) : U),
          (p : U × (Rt × Rt)).2), ⟨(σ _).2, (Submodule.mem_prod.mp p.2).2⟩⟩
      invFun := fun p => ⟨(((σ.symm ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩ : M) : U),
          (p : U × (Rt × Rt)).2), ⟨(σ.symm _).2, (Submodule.mem_prod.mp p.2).2⟩⟩
      map_add' := fun p p' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
        congr 1
        rw [← Submodule.coe_add, ← map_add]; rfl
      map_smul' := fun c p => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk]
        congr 1
        rw [← Submodule.coe_smul, ← map_smul]; rfl
      left_inv := fun p => by
        apply Subtype.ext
        simp only
        ext <;> simp
      right_inv := fun p => by
        apply Subtype.ext
        simp only
        ext <;> simp }
  have hσ' : ∀ p : M.prod (lineA (R := R) (Rt := Rt)), (σ' p : U × (Rt × Rt)) =
      (((σ ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩ : N) : U), (p : U × (Rt × Rt)).2) :=
    fun p => rfl
  have hσ'q : ∀ p, q' (σ' p) = q' p := by
    intro p
    rw [hσ', hq', QuadraticMap.prod_apply, QuadraticMap.prod_apply, hσq]
  have hσ'H : ∀ p : M.prod (lineA (R := R) (Rt := Rt)), (σ' p : U × (Rt × Rt)) - p ∈ H.prod (lineE (R := R) (Rt := Rt)) := by
    intro p
    rw [hσ']
    refine ⟨?_, ?_⟩
    · simpa using hσH ⟨(p : U × (Rt × Rt)).1, (Submodule.mem_prod.mp p.2).1⟩
    · simp
  -- (5), (6) for $H'$: $e = v_1 + v_2$
  have he : Cond56 q' (H.prod (lineE (R := R) (Rt := Rt))) := by
    refine ⟨((0 : U), ((1 : Rt), (1 : Rt))), ⟨H.zero_mem, Submodule.mem_span_singleton_self _⟩,
      ⟨1, isUnit_one, by simp [hq']⟩, fun hk z hz => ?_⟩
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_prod.mp hz).2
    have hz2 : z.2 = (algebraMap R Rt s, algebraMap R Rt s) := by rw [← hs, smul_e]
    rw [hq', polar_prod', QuadraticMap.polar_zero_left, zero_add, polar_hypRt, hz2]
    simp only [one_mul, mul_one]
    rw [← map_add, rs_algebraMap hinj, map_add, ← two_mul, two_eq_zero_of_card_two hk, zero_mul]
  obtain ⟨g, hg, hgσ⟩ := assertion1 hinj (finrank R (M.prod (lineA (R := R) (Rt := Rt)))) h1' hM'L hN'L hM'free hM'fin rfl
    (cond2_prime q h2a) (cond2_prime q h2b) σ' hσ'q hσ'H he
  -- $g$ fixes $v_1$ and $v_2$
  have hv1M : ((0 : U), ((1 : Rt), (0 : Rt))) ∈ M.prod (lineA (R := R) (Rt := Rt)) := ⟨M.zero_mem, Submodule.mem_span_singleton_self _⟩
  have hgv1 : g ((0 : U), ((1 : Rt), (0 : Rt))) = ((0 : U), ((1 : Rt), (0 : Rt))) := by
    rw [show ((0 : U), ((1 : Rt), (0 : Rt))) = ((⟨_, hv1M⟩ : M.prod (lineA (R := R) (Rt := Rt))) : U × (Rt × Rt)) from rfl, hgσ, hσ']
    simp
  have hgv12 : g ((0 : U), ((1 : Rt), (-1 : Rt))) = ((0 : U), ((1 : Rt), (-1 : Rt))) := by
    apply hg.fix
    intro z hz
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_prod.mp hz).2
    have hz2 : z.2 = (algebraMap R Rt s, algebraMap R Rt s) := by rw [← hs, smul_e]
    rw [polar_prod', QuadraticMap.polar_zero_left, zero_add, polar_hypRt, hz2]
    ring
  have hgv2 : g ((0 : U), ((0 : Rt), (1 : Rt))) = ((0 : U), ((0 : Rt), (1 : Rt))) := by
    have e : ((0 : U), ((0 : Rt), (1 : Rt))) = ((0 : U), ((1 : Rt), (0 : Rt))) - ((0 : U), ((1 : Rt), (-1 : Rt))) := by
      ext <;> simp
    rw [e, map_sub, hgv1, hgv12]
  -- $g$ and $g^{-1}$ preserve $U \times 0$
  have hpres : ∀ (g' : (U × (Rt × Rt)) ≃ₗ[Rt] (U × (Rt × Rt))), (∀ x, q' (g' x) = q' x) →
      g' ((0 : U), ((1 : Rt), (0 : Rt))) = ((0 : U), ((1 : Rt), (0 : Rt))) →
      g' ((0 : U), ((0 : Rt), (1 : Rt))) = ((0 : U), ((0 : Rt), (1 : Rt))) →
      ∀ x : U, (g' (x, 0)).2 = 0 := by
    intro g' hg'q hg'1 hg'2 x
    have k1 := polar_equiv g' hg'q (x, 0) ((0 : U), ((1 : Rt), (0 : Rt)))
    have k2 := polar_equiv g' hg'q (x, 0) ((0 : U), ((0 : Rt), (1 : Rt)))
    rw [hg'1, hq', polar_prod', polar_prod', polar_hypRt, polar_hypRt] at k1
    rw [hg'2, hq', polar_prod', polar_prod', polar_hypRt, polar_hypRt] at k2
    simp only [QuadraticMap.polar_zero_right, Prod.snd_zero, Prod.fst_zero, mul_zero, mul_one, zero_add,
      add_zero, one_mul, zero_mul] at k1 k2
    exact Prod.ext k2 k1
  have hgs := hg.symm
  have hgsv1 : g.symm ((0 : U), ((1 : Rt), (0 : Rt))) = ((0 : U), ((1 : Rt), (0 : Rt))) := by
    conv_lhs => rw [← hgv1]
    simp
  have hgsv2 : g.symm ((0 : U), ((0 : Rt), (1 : Rt))) = ((0 : U), ((0 : Rt), (1 : Rt))) := by
    conv_lhs => rw [← hgv2]
    simp
  have hp1 := hpres g hg.isom hgv1 hgv2
  have hp2 := hpres g.symm hgs.isom hgsv1 hgsv2
  let τU : U →ₗ[Rt] U := (LinearMap.fst Rt U (Rt × Rt)) ∘ₗ g.toLinearMap ∘ₗ (LinearMap.inl Rt U (Rt × Rt))
  let τU' : U →ₗ[Rt] U := (LinearMap.fst Rt U (Rt × Rt)) ∘ₗ g.symm.toLinearMap ∘ₗ (LinearMap.inl Rt U (Rt × Rt))
  have hτU : ∀ x, g (x, 0) = (τU x, 0) := fun x => Prod.ext rfl (hp1 x)
  have hτU' : ∀ x, g.symm (x, 0) = (τU' x, 0) := fun x => Prod.ext rfl (hp2 x)
  have hgL := hg.sub_mem h1'.le h1'.LJ
  have hgsL := hgs.sub_mem h1'.le h1'.LJ
  have hinv1 : ∀ x, τU (τU' x) = x := by
    intro x
    have := congrArg Prod.fst (hτU (τU' x))
    rw [← hτU', LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hinv2 : ∀ x, τU' (τU x) = x := by
    intro x
    have := congrArg Prod.fst (hτU' (τU x))
    rw [← hτU, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  let τ : U ≃ₗ[Rt] U := LinearEquiv.ofLinear τU τU' (by ext x; simp [hinv1]) (by ext x; simp [hinv2])
  have hτ : ∀ x, τ x = τU x := fun x => rfl
  have hτs : ∀ x, τ.symm x = τU' x := fun x => rfl
  refine ⟨τ, fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun x => ?_, fun x hxL hx => ?_, fun x hx => ?_⟩
  · rw [hτ]
    have := hg.isom (x, 0)
    rw [hτU, QuadraticMap.prod_apply, QuadraticMap.prod_apply] at this
    simpa using this
  · have := (hgL (x, 0) ⟨hx, Submodule.zero_mem _⟩).1
    rw [hτU] at this
    exact this.1
  · have := (hgsL (x, 0) ⟨hx, Submodule.zero_mem _⟩).1
    rw [hτU'] at this
    rw [hτs]; exact this.1
  · rw [hτ]
    have hxM : ((x : U), (0 : Rt × Rt)) ∈ M.prod (lineA (R := R) (Rt := Rt)) := ⟨x.2, Submodule.zero_mem _⟩
    have := hgσ ⟨_, hxM⟩
    rw [hσ'] at this
    have := congrArg Prod.fst this
    simp only at this
    rw [← this, hτU]
  · rw [hτ]
    have : g (x, 0) = (x, 0) := by
      apply hg.fix
      intro z hz
      rw [polar_prod', polar_hypRt]
      simp [hx z.1 (Submodule.mem_prod.mp hz).1]
    rw [hτU] at this
    exact congrArg Prod.fst this
  · have := (hgL (x, 0) ⟨hx, Submodule.zero_mem _⟩).2
    rw [hτU] at this
    rw [hτ]
    simpa using (Submodule.mem_prod.mp this).1

/-- **Kitaoka 1993, Theorem 1.2.2** (Kneser, p. 6): the statement `Kitaoka.Theorem122`. Unconditional. -/
@[kb "kitaoka1993" "§1.2, Thm. 1.2.2, p. 6 (proof)"]
theorem theorem122 : Theorem122 := by
  intro R Rt U _ _ _ _ _ _ _ _ q L M N H hinj _ hMfg _ _ hMfree _ hM hN hH h1q h1b h2a h2b σ hσq hσH
  obtain ⟨τ, hq, hL, hL', hσ, hfix, hH'⟩ :=
    kneser_U q L M N H hinj hMfg hMfree hM hN hH h1q h1b h2a h2b σ hσq hσH
  let τR := τ.restrictScalars R
  let τL : L ≃ₗ[R] L := LinearEquiv.ofLinear (τR.toLinearMap.restrict hL) (τR.symm.toLinearMap.restrict hL')
    (by ext x; exact τ.apply_symm_apply (x : U)) (by ext x; exact τ.symm_apply_apply (x : U))
  refine ⟨τL, fun x => hq x, fun x => hσ x, fun x hx => Subtype.ext (hfix x x.2 hx), fun x => hH' x x.2⟩

end QuadFormsKB.Kitaoka.Kneser
