/-
# Kitaoka 1993, Theorem 1.3.2 in characteristic $2$: $r(V, W)$ for a regular plane $V$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, proof of Theorem 1.3.2, second claim,
pp. 17–18 (printed pages).

**Proves** (finite field $F$ of characteristic $2$, $q = \# F$, $W$ regular of dimension $w$):
* `yCount_eq`: for $Q(x) = a$ and an isotropic $y_0$ with $b(x, y_0) = 1$,
  $\#\{y : Q(y) = c,\ b(x, y) = 1\} = \sum_s a(c - as^2 - s, W_1)$ with $W_1 = \langle x, y_0\rangle^\perp$;
* `isomCount_hyp`: $r(H, W) = (a(0, W) - 1)\,q^{w-2}$;
* `isomCount_aniso_of_isotropic`: for an anisotropic plane $K = \mathrm{binForm}\ a\ c$ and an isotropic $W$,
  $r(K, W) = a(a, W)\,q\,a(1, W_1)$, with $a(1, W_1) = q^{w-3}(1 - \chi(W)q^{-(w-2)/2})$;
* `isomCount_aniso_self`: $r(K, W) = 2\,a(a, W)$ for $W$ an anisotropic plane.

**Proof.** Kitaoka moves $x$ into a hyperbolic plane by Witt's theorem; here the plane $\langle x, y_0\rangle$ is
used directly, and Witt's theorem (`QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`) only provides the
partner $y_0$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2Plane

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

variable {F : Type} [Field F] [Finite F] (hF : ringChar F = 2)
variable {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (QW : QuadraticForm F W)

/-- The pairs $(x, y)$ with $Q(x) = a$, $Q(y) = c$, $b(x, y) = 1$, fibred over $x$. -/
def pairSigmaEquiv (a c : F) :
    {p : W × W // QW p.1 = a ∧ QW p.2 = c ∧ polar QW p.1 p.2 = 1} ≃
      Σ x : {x : W // QW x = a}, {y : W // QW y = c ∧ polar QW x.1 y = 1} where
  toFun p := ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
  invFun z := ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
  left_inv p := rfl
  right_inv z := rfl

theorem pairCount_const (a c : F) (R : ℝ)
    (hR : ∀ x, QW x = a → (Nat.card {y : W // QW y = c ∧ polar QW x y = 1} : ℝ) = R) :
    (Nat.card {p : W × W // QW p.1 = a ∧ QW p.2 = c ∧ polar QW p.1 p.2 = 1} : ℝ) = valCount QW a * R := by
  classical
  have : Finite W := Module.finite_of_finite F
  have : Fintype {x : W // QW x = a} := Fintype.ofFinite _
  rw [Nat.card_congr (pairSigmaEquiv QW a c), Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => hR x.1 x.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, valCount,
    Nat.card_eq_fintype_card]

theorem pairCount_zero (c : F) (R : ℝ)
    (hR : ∀ x, x ≠ 0 → QW x = 0 → (Nat.card {y : W // QW y = c ∧ polar QW x y = 1} : ℝ) = R) :
    (Nat.card {p : W × W // QW p.1 = 0 ∧ QW p.2 = c ∧ polar QW p.1 p.2 = 1} : ℝ) =
      ((valCount QW 0 : ℝ) - 1) * R := by
  classical
  have : Finite W := Module.finite_of_finite F
  have : Fintype {x : W // QW x = 0} := Fintype.ofFinite _
  rw [Nat.card_congr (pairSigmaEquiv QW 0 c), Nat.card_sigma]
  push_cast
  have h0 : (Nat.card {y : W // QW y = c ∧ polar QW (0 : W) y = 1} : ℝ) = 0 := by
    have : IsEmpty {y : W // QW y = c ∧ polar QW (0 : W) y = 1} := ⟨fun y => by
      have := y.2.2; simp at this⟩
    simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, map_zero QW⟩ : {x : W // QW x = 0})), h0, zero_add,
    Finset.sum_congr rfl fun x hx => hR x.1 (fun h => (Finset.mem_erase.mp hx).1 (Subtype.ext h)) x.2,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul, valCount,
    Nat.card_eq_fintype_card]
  have h1 : 1 ≤ Fintype.card {x : W // QW x = 0} := Fintype.card_pos_iff.mpr ⟨⟨0, map_zero QW⟩⟩
  push_cast [h1]
  ring

include hF

/-- The plane $\langle x, y_0\rangle$ as an isometry from `binForm a 0`. -/
def planeIso {x y0 : W} {a : F} (hx : QW x = a) (hy0 : QW y0 = 0) (hxy : polar QW x y0 = 1) :
    IsoT (binForm a 0) QW :=
  (isoBinEquiv hF QW a 0).symm ⟨(x, y0), hx, hy0, hxy⟩

theorem planeIso_coe {x y0 : W} {a : F} (hx : QW x = a) (hy0 : QW y0 = 0) (hxy : polar QW x y0 = 1) :
    (planeIso hF QW hx hy0 hxy).1 = pairMap x y0 := rfl

theorem mem_perp_pair {x y0 w : W} :
    w ∈ perpRange QW (pairMap (F := F) x y0) ↔ polar QW x w = 0 ∧ polar QW y0 w = 0 := by
  rw [mem_perpRange]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h (1, 0); simpa using this
    · have := h (0, 1); simpa using this
  · rintro ⟨h1, h2⟩ p
    simp [polar_add_left, polar_smul_left, h1, h2]


/-- The fibre over $x$, parametrized by $s = b(y_0, y)$ and $w = y - sx - y_0 \in \langle x, y_0\rangle^\perp$. -/
def yFiberEquiv {x y0 : W} {a : F} (hx : QW x = a) (hy0 : QW y0 = 0) (hxy : polar QW x y0 = 1) (c : F) :
    {y : W // QW y = c ∧ polar QW x y = 1} ≃
      {p : F × perpRange QW (pairMap (F := F) x y0) //
        (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) p.2 = c - a * p.1 * p.1 - p.1} where
  toFun y := ⟨(polar QW y0 y.1, ⟨y.1 - polar QW y0 y.1 • x - y0, (mem_perp_pair hF QW).mpr ⟨by
      rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_self_char2 hF, y.2.2, hxy]; simp, by
      rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_self_char2 hF, polar_comm QW y0 x, hxy]
      simp⟩⟩), by
      simp only [QuadraticMap.comp_apply, Submodule.subtype_apply]
      set s := polar QW y0 y.1
      have e : y.1 = s • x + y0 + (y.1 - s • x - y0) := by abel
      have p1 : polar QW x (y.1 - s • x - y0) = 0 := by
        rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_self_char2 hF, y.2.2, hxy]; simp
      have p2 : polar QW y0 (y.1 - s • x - y0) = 0 := by
        rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_self_char2 hF, polar_comm QW y0 x, hxy]
        simp [s]
      have hc := y.2.1
      rw [e, QuadraticMap.map_add QW, QuadraticMap.map_add QW, QuadraticMap.map_smul, hx, hy0,
        polar_smul_left, hxy, polar_add_left, polar_smul_left, p1, p2] at hc
      simp only [smul_eq_mul] at hc
      linear_combination hc⟩
  invFun z := ⟨z.1.1 • x + y0 + (z.1.2 : W), by
      have hw := (mem_perp_pair hF QW).mp z.1.2.2
      have hq := z.2
      simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at hq
      rw [QuadraticMap.map_add QW, QuadraticMap.map_add QW, QuadraticMap.map_smul, hx, hy0, polar_smul_left, hxy,
        polar_add_left, polar_smul_left, hw.1, hw.2, hq]
      simp only [smul_eq_mul]
      ring, by
      have hw := (mem_perp_pair hF QW).mp z.1.2.2
      rw [polar_add_right, polar_add_right, polar_smul_right, polar_self_char2 hF, hxy, hw.1]
      simp⟩
  left_inv y := by
    apply Subtype.ext
    simp only
    abel
  right_inv z := by
    rcases z with ⟨⟨s, w⟩, hw⟩
    have hw' := (mem_perp_pair hF QW).mp w.2
    have hs : polar QW y0 (s • x + y0 + (w : W)) = s := by
      rw [polar_add_right, polar_add_right, polar_smul_right, polar_comm QW y0 x, hxy, hw'.2,
        polar_self_char2 hF]
      simp
    apply Subtype.ext
    simp only [hs]
    ext
    · rfl
    · simp only [Submodule.coe_mk]
      abel

/-- **The fibre count over $x$**: $\#\{y : Q(y) = c, b(x, y) = 1\} = \sum_s a(c - as^2 - s, W_1)$. -/
theorem yCount_eq [Fintype F] {x y0 : W} {a : F} (hx : QW x = a) (hy0 : QW y0 = 0) (hxy : polar QW x y0 = 1) (c : F) :
    (Nat.card {y : W // QW y = c ∧ polar QW x y = 1} : ℝ) =
      ∑ s : F, (valCount (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) (c - a * s * s - s) : ℝ) := by
  classical
  have : Finite W := Module.finite_of_finite F
  rw [Nat.card_congr (yFiberEquiv hF QW hx hy0 hxy c),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (s : F) (w : perpRange QW (pairMap (F := F) x y0)) =>
      (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) w = c - a * s * s - s)), Nat.card_sigma]
  push_cast
  rfl


/-! ### Partners -/

/-- A nonzero isotropic $x$ in a regular space has an isotropic partner $y_0$ with $b(x, y_0) = 1$. -/
theorem exists_partner_isotropic (hQW : (polarBilin QW).Nondegenerate) {x : W} (hx0 : x ≠ 0) (hx : QW x = 0) :
    ∃ y0, QW y0 = 0 ∧ polar QW x y0 = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, polar QW x u ≠ 0 := by
    by_contra! h
    exact hx0 ((QuadraticForm.nondegenerate_polarBilin_iff QW).mp hQW x h)
  obtain ⟨u', hxu⟩ : ∃ u', polar QW x u' = 1 :=
    ⟨(polar QW x u)⁻¹ • u, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  refine ⟨u' - QW u' • x, ?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add QW, QuadraticMap.map_smul, hx, polar_smul_right,
      polar_comm, hxu]
    simp only [smul_eq_mul]; ring
  · rw [polar_sub_right, polar_smul_right, polar_self_char2 hF, hxu]; simp

/-- In a regular space with a nonzero isotropic vector, every $x$ with $Q(x) = a \ne 0$ has an isotropic partner
(Witt's theorem). -/
theorem exists_partner_of_isotropic (hQW : (polarBilin QW).Nondegenerate) (hiso : ∃ z : W, z ≠ 0 ∧ QW z = 0)
    {x : W} {a : F} (ha : a ≠ 0) (hx : QW x = a) : ∃ y0, QW y0 = 0 ∧ polar QW x y0 = 1 := by
  obtain ⟨z, hz0, hz⟩ := hiso
  obtain ⟨z', hz', hzz'⟩ := exists_partner_isotropic hF QW hQW hz0 hz
  have hx' : QW (a • z + z') = a := by
    rw [QuadraticMap.map_add QW, QuadraticMap.map_smul, hz, hz', polar_smul_left, hzz']; simp
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate QW hQW ha hx' hx
  refine ⟨ρ z, by rw [ρ.map_app, hz], ?_⟩
  have h := polar_of_iso ρ.toLinearEquiv.toLinearMap (fun v => ρ.map_app v) (a • z + z') z
  simp only [LinearEquiv.coe_coe] at h
  erw [← hρ, h]
  rw [polar_add_left, polar_smul_left, polar_self_char2 hF, polar_comm, hzz']
  simp

/-! ### The complement $\langle x, y_0\rangle^\perp$ -/

theorem perp_pair_facts (hQW : (polarBilin QW).Nondegenerate) {x y0 : W} {a : F} (hx : QW x = a)
    (hy0 : QW y0 = 0) (hxy : polar QW x y0 = 1) :
    (polarBilin (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype)).Nondegenerate ∧
      finrank F (perpRange QW (pairMap (F := F) x y0)) + 2 = finrank F W ∧
      chiGen (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) = chiGen QW := by
  obtain ⟨he, hd, hreg⟩ := perpRange_split (binForm_nondegenerate hF a 0) (planeIso hF QW hx hy0 hxy)
  rw [planeIso_coe] at he hd hreg
  have hreg1 := hreg hQW
  have h2 : finrank F (F × F) = 2 := by simp
  refine ⟨hreg1, by omega, ?_⟩
  have hH : (binForm a 0).Equivalent (QuadraticForm.hyperbolicPlane F) :=
    Radical.proposition122_plane _ h2 (binForm_nondegenerate hF a 0) ⟨(0, 1), by simp, by simp⟩
  have hregP := QuadraticForm.nondegenerate_polarBilin_prod (binForm_nondegenerate hF a 0) hreg1
  rw [← chiGen_congr hregP he, chiGen_congr hregP (hH.prod (QuadraticMap.Equivalent.refl
    (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype))), chiGen_hyp_prod hreg1]

/-! ### The three cases -/

/-- $r(H, W) = (a(0, W) - 1)\,q^{w-2}$ for a regular $W$ (with $H$ = `binForm 0 0`). -/
theorem isomCount_hyp (hQW : (polarBilin QW).Nondegenerate) :
    (isomCount (binForm 0 0) QW : ℝ) =
      ((valCount QW 0 : ℝ) - 1) * (Nat.card F : ℝ) ^ (finrank F W - 2) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [isomCount_binForm hF]
  refine pairCount_zero QW 0 _ fun x hx0 hx => ?_
  obtain ⟨y0, hy0, hxy⟩ := exists_partner_isotropic hF QW hQW hx0 hx
  obtain ⟨-, hd, -⟩ := perp_pair_facts hF QW hQW hx hy0 hxy
  rw [yCount_eq hF QW hx hy0 hxy]
  have : Finite (perpRange QW (pairMap (F := F) x y0)) := Module.finite_of_finite F
  have e : ∑ s : F, (valCount (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) (0 - 0 * s * s - s) : ℝ) =
      ∑ t : F, (valCount (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) t : ℝ) :=
    Fintype.sum_equiv (Equiv.neg F) _ _ fun s => by simp
  rw [e, sum_valCount, Module.natCard_eq_pow_finrank (K := F)]
  push_cast
  congr 1
  omega

/-- For an anisotropic plane `binForm a c` and a regular $W$ with a nonzero isotropic vector,
$r(K, W) = a(a, W)\,q\,a(1, W_1)$ with $a(1, W_1) = q^{w-3}(1 - \chi(W)q^{-(w-2)/2})$. -/
theorem isomCount_aniso_of_isotropic (hQW : (polarBilin QW).Nondegenerate)
    (hiso : ∃ z : W, z ≠ 0 ∧ QW z = 0) {a c : F} (hK : (binForm a c).Anisotropic) :
    (isomCount (binForm a c) QW : ℝ) =
      valCount QW a * ((Nat.card F : ℝ) * ((Nat.card F : ℝ) ^ (((finrank F W - 2 : ℕ) : ℤ) - 1) *
        (1 - chiGen QW * (Nat.card F : ℝ) ^ (-(((finrank F W - 2) / 2 : ℕ) : ℤ))))) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have ha : a ≠ 0 := by
    intro h
    have := hK (1, 0) (by simp [h])
    simp at this
  rw [isomCount_binForm hF]
  refine pairCount_const QW a c _ fun x hx => ?_
  obtain ⟨y0, hy0, hxy⟩ := exists_partner_of_isotropic hF QW hQW hiso ha hx
  obtain ⟨hreg1, hd, hchi⟩ := perp_pair_facts hF QW hQW hx hy0 hxy
  rw [yCount_eq hF QW hx hy0 hxy]
  have heven : Even (finrank F (perpRange QW (pairMap (F := F) x y0))) := even_finrank_char2 hF _ hreg1
  have hterm : ∀ s : F, (valCount (QW.comp (perpRange QW (pairMap (F := F) x y0)).subtype) (c - a * s * s - s) : ℝ)
      = (Nat.card F : ℝ) ^ (((finrank F W - 2 : ℕ) : ℤ) - 1) *
        (1 - chiGen QW * (Nat.card F : ℝ) ^ (-(((finrank F W - 2) / 2 : ℕ) : ℤ))) := by
    intro s
    have hne : c - a * s * s - s ≠ 0 := by
      have hb : c - a * s * s - s = binForm a c (s, 1) := by
        rw [binForm_apply, sub_eq_add_neg, sub_eq_add_neg, neg_eq_self_of_ringChar hF,
          neg_eq_self_of_ringChar hF]
        ring
      rw [hb]
      intro h0
      have := hK _ h0
      simp at this
    rw [valCount_even hreg1 heven hne, hchi, show finrank F (perpRange QW (pairMap (F := F) x y0)) =
      finrank F W - 2 by omega]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]

/-- For an anisotropic plane `binForm a c` and an anisotropic plane $W$, $r(K, W) = 2\,a(a, W)$. -/
theorem isomCount_aniso_aniso (hQW : (polarBilin QW).Nondegenerate) (hW2 : finrank F W = 2)
    (hWa : QW.Anisotropic) {a c : F} (hK : (binForm a c).Anisotropic) :
    (isomCount (binForm a c) QW : ℝ) = valCount QW a * 2 := by
  classical
  have ha : a ≠ 0 := by
    intro h
    have := hK (1, 0) (by simp [h])
    simp at this
  have h2 : finrank F (F × F) = 2 := by simp
  obtain ⟨φ⟩ := aniso_planes_equiv h2 hW2 hK hWa
  rw [isomCount_binForm hF]
  refine pairCount_const QW a c _ fun x hx => ?_
  have hφ1 : QW (φ (1, 0)) = a := by rw [φ.map_app]; simp
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate QW hQW ha hφ1 hx
  set ys := ρ (φ (0, 1))
  have hys : QW ys = c := by simp [ys, ρ.map_app, φ.map_app]
  have hxys : polar QW x ys = 1 := by
    have h1 := polar_of_iso ρ.toLinearEquiv.toLinearMap (fun v => ρ.map_app v) (φ (1, 0)) (φ (0, 1))
    have h2' := polar_of_iso φ.toLinearEquiv.toLinearMap (fun v => φ.map_app v) (1, 0) (0, 1)
    simp only [LinearEquiv.coe_coe] at h1 h2'
    rw [← hρ]
    erw [h1, h2', polar_binForm hF]
    simp
  -- the fibre is $\{y_s, y_s + a^{-1}x\}$
  have hbasis : Function.Bijective (pairMap (F := F) x ys) := by
    have hinj : Function.Injective (pairMap (F := F) x ys) := (isoBinEquiv hF QW a c).symm ⟨(x, ys), hx, hys, hxys⟩ |>.2.1
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hW2])).mp hinj⟩
  have hset : ∀ y : W, (QW y = c ∧ polar QW x y = 1) ↔ y ∈ ({ys, ys + a⁻¹ • x} : Set W) := by
    intro y
    constructor
    · rintro ⟨hy, hxy⟩
      obtain ⟨⟨α, β⟩, hp⟩ := hbasis.2 (y - ys)
      simp only [pairMap_apply] at hp
      have hβ : β = 0 := by
        have := congrArg (polar QW x) hp
        rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_char2 hF, hxys, polar_sub_right,
          hxy, hxys] at this
        simpa using this
      subst hβ
      have hy' : y = ys + α • x := by rw [← sub_eq_iff_eq_add', ← hp]; simp
      have hq : α * (1 + α * a) = 0 := by
        have := hy
        rw [hy', QuadraticMap.map_add QW, QuadraticMap.map_smul, hys, hx, polar_smul_right, polar_comm, hxys] at this
        simp only [smul_eq_mul] at this
        linear_combination this
      rcases mul_eq_zero.mp hq with h | h
      · left; rw [hy', h, zero_smul, add_zero]
      · right
        have hα : α = a⁻¹ := by
          have : α * a = 1 := by
            have := congrArg (· + 1) h
            simp only [zero_add] at this
            rw [add_comm] at this
            have h2 := two_eq_zero_of_ringChar hF
            linear_combination h - h2
          exact eq_inv_of_mul_eq_one_left this
        rw [Set.mem_singleton_iff, hy', hα]
    · rintro (h | h)
      · rw [h]; exact ⟨hys, hxys⟩
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        refine ⟨?_, ?_⟩
        · rw [QuadraticMap.map_add QW, QuadraticMap.map_smul, hys, hx, polar_smul_right, polar_comm, hxys]
          simp only [smul_eq_mul]
          have h2 := two_eq_zero_of_ringChar hF
          have e : a⁻¹ * a⁻¹ * a = a⁻¹ := by field_simp
          linear_combination e + a⁻¹ * h2
        · rw [polar_add_right, polar_smul_right, polar_self_char2 hF, hxys]; simp
  have hne : ys ≠ ys + a⁻¹ • x := by
    intro h
    have : a⁻¹ • x = 0 := by
      have := congrArg (· - ys) h
      simpa using this.symm
    rcases smul_eq_zero.mp this with h1 | h1
    · exact inv_ne_zero ha h1
    · rw [h1, map_zero] at hx; exact ha hx.symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_coe_set_eq, Set.ncard_pair hne]
  norm_num

end QuadFormsKB.Kitaoka.FqCount
