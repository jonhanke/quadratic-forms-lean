/-
# Kitaoka 1993, Proposition 1.3.3, second case: isometries into $W$ with $W^\perp \ne \operatorname{Rad} W$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, Proposition 1.3.3 and its proof, pp. 18–19
(printed pages).

**Book statement (second case).** Let $V, W$ be quadratic spaces over $F = \mathbb F_q$ with $V$ regular and represented
by $W$; $W = W_1 \perp \operatorname{Rad} W$, $v = \dim V$, $r = \dim \operatorname{Rad} W$. If
$W^\perp \ne \operatorname{Rad} W$ (possible only in characteristic $2$), then
$r(V, W) = q^{v\dim W - v(v+1)/2}\prod_{w-v+2 \le e \le w,\ e \text{ even}}(1 - q^{-e})$.

**Encoding.** In the proof Kitaoka writes $W^\perp = Fw_0 + \operatorname{Rad} W$ with $Q(w_0) = 1$ and
$W_1 = W_0 \perp Fw_0$ with $W_0$ regular; $w = \dim W_0$ (so $\dim W = w + 1 + r$). Here $W$ is given in this normal
form: $W = (W_0 \times F) \times R$ with the form $(Q_0 \perp \langle 1\rangle) \perp 0$ (`(Q₀.prod (lineForm 1)).prod 0`),
$Q_0$ regular, $R$ of dimension $r$ carrying the zero form, over a finite field of characteristic $2$ (there
$\langle 1\rangle : x \mapsto x^2$ has polar form $2xy = 0$, so $Fw_0 \subseteq W^\perp$ and $Q(w_0) = 1$). "$V$ is represented
by $W$" is the existence of an isometry `IsoT QV QW`.

**Proves** (unconditional): `proposition133_char2`. Together with `proposition133_rad` (the case
$W^\perp = \operatorname{Rad} W$, `Ch1Prop133.lean`) this is all of Proposition 1.3.3.

**Proof** (Kitaoka's). $r(V, W) = r(V, W_1)\,q^{vr}$ (first case). For $W_1 = W_0 \perp \langle 1\rangle$: induction on
$v$, splitting off a regular plane $A$ of $V$; $r(A, W_1) = (q^w - 1)q^{w-1}$, because the vectors $x = (u, f)$ with
$Q(x) = a$ correspond to $u \in W_0$ ($f$ is the unique square root of $a - Q_0(u)$), those with $b(x, W_1) \ne 0$ to
$u \ne 0$, and for such $x$ the $y$ with $Q(y) = c$, $b(x, y) = 1$ correspond to the $u'$ with $b_0(u, u') = 1$. For an
isometry $\tau : A \to W_1$, $\tau(A)^\perp$ again has polar radical $Fw_0$ and is $\cong W_0' \perp \langle 1\rangle$ with
$W_0'$ regular of dimension $w - 2$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Char2Main
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Prop133

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

/-! ### The formula -/

/-- Kitaoka's value $q^{(w+1)v - v(v+1)/2}\prod_{w-v+2 \le e \le w,\ e \text{ even}}(1 - q^{-e})$ for
$r(V, W_0 \perp \langle 1\rangle)$, $\dim V = v$, $\dim W_0 = w$ (the lower bound is $w + 2 - v$ in $\mathbb N$). -/
def radForm (q : ℝ) (v w : ℕ) : ℝ :=
  q ^ (((w + 1) * v : ℕ) - (v * (v + 1) / 2 : ℕ) : ℤ) * ∏ e ∈ (Finset.Icc (w + 2 - v) w).filter Even, (1 - q ^ (-(e : ℤ)))

theorem radForm_zero (q : ℝ) (w : ℕ) : radForm q 0 w = 1 := by
  have h : (Finset.Icc (w + 2 - 0) w).filter Even = ∅ := by
    ext e; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
  simp [radForm, h]

/-- The step $r(V, W_1) = r(A, W_1)\,r(V_1, W_1')$: $\mathrm{radForm}(2n + 2, w + 2) =
(q^{w+2} - 1)q^{w+1}\,\mathrm{radForm}(2n, w)$ for $w$ even. -/
theorem radForm_step {q : ℝ} (hq : 0 < q) (n w : ℕ) (hw : Even w) :
    ((q ^ (w + 2) - 1) * q ^ (w + 1)) * radForm q (2 * n) w = radForm q (2 * n + 2) (w + 2) := by
  have hnot : w + 2 ∉ (Finset.Icc (w + 2 - 2 * n) w).filter Even := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hP : (Finset.Icc (w + 2 + 2 - (2 * n + 2)) (w + 2)).filter Even =
      insert (w + 2) ((Finset.Icc (w + 2 - 2 * n) w).filter Even) := by
    obtain ⟨k, hk⟩ := hw
    ext e
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, Nat.even_iff]
    omega
  have hE : (((w + 2 + 1) * (2 * n + 2) : ℕ) - ((2 * n + 2) * (2 * n + 2 + 1) / 2 : ℕ) : ℤ) =
      (((w + 1) * (2 * n) : ℕ) - ((2 * n) * (2 * n + 1) / 2 : ℕ) : ℤ) + ((2 * w + 3 : ℕ) : ℤ) := by
    rw [show (2 * n + 2) * (2 * n + 2 + 1) / 2 = (n + 1) * (2 * n + 3) by
        rw [show (2 * n + 2) * (2 * n + 2 + 1) = 2 * ((n + 1) * (2 * n + 3)) by ring]; omega,
      show (2 * n) * (2 * n + 1) / 2 = n * (2 * n + 1) by
        rw [show (2 * n) * (2 * n + 1) = 2 * (n * (2 * n + 1)) by ring]; omega]
    push_cast; ring
  unfold radForm
  rw [hP, Finset.prod_insert hnot, hE, zpow_add₀ hq.ne', zpow_natCast, zpow_neg, zpow_natCast]
  have h1 : q ^ (w + 2) ≠ 0 := pow_ne_zero _ hq.ne'
  have e1 : q ^ (2 * w + 3) = q ^ (w + 2) * q ^ (w + 1) := by rw [← pow_add]; ring_nf
  rw [e1]
  field_simp
  first
  | done
  | ring

variable {F : Type} [Field F] [Finite F] (hF : ringChar F = 2)
include hF

/-! ### Square roots in characteristic $2$ -/

theorem sq_injective_char2 : Function.Injective (fun x : F => x * x) := by
  intro x y h
  have h2 := two_eq_zero_of_ringChar hF
  have : (x - y) * (x - y) = 0 := by
    simp only at h
    linear_combination h + (y * y - x * y) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

theorem sq_bijective_char2 : Function.Bijective (fun x : F => x * x) :=
  Finite.injective_iff_bijective.mp (sq_injective_char2 hF)

/-! ### The space $W_0 \perp \langle 1\rangle$ -/

section Space

variable {U : Type} [AddCommGroup U] [Module F U] [FiniteDimensional F U] (Q₀ : QuadraticForm F U)

theorem polar_prod_line (p p' : U × F) :
    polar (Q₀.prod (lineForm 1)) p p' = polar Q₀ p.1 p'.1 := by
  have h2 := two_eq_zero_of_ringChar hF
  simp only [polar, QuadraticMap.prod_apply, lineForm_apply, Prod.fst_add, Prod.snd_add]
  linear_combination (p.2 * p'.2) * h2

/-- The vectors with $Q(x) = a$ and $b(x, W_1) \ne 0$ correspond to $u \ne 0$ in $W_0$. -/
def valNeEquiv (a : F) :
    {p : U × F // (Q₀.prod (lineForm 1)) p = a ∧ p.1 ≠ 0} ≃ {u : U // u ≠ 0} where
  toFun p := ⟨p.1.1, p.2.2⟩
  invFun u := ⟨(u.1, Function.surjInv (sq_bijective_char2 hF).2 (a - Q₀ u.1)), by
      refine ⟨?_, u.2⟩
      simp only [QuadraticMap.prod_apply, lineForm_apply, one_mul]
      rw [Function.surjInv_eq (sq_bijective_char2 hF).2]
      ring⟩
  left_inv p := by
    apply Subtype.ext
    ext
    · rfl
    · apply sq_injective_char2 hF
      simp only
      rw [Function.surjInv_eq (sq_bijective_char2 hF).2]
      have := p.2.1
      simp only [QuadraticMap.prod_apply, lineForm_apply, one_mul] at this
      linear_combination -this
  right_inv u := rfl

/-- The $y$ with $Q(y) = c$, $b(x, y) = 1$ for $x = (u, f)$ correspond to the $u'$ with $b_0(u, u') = 1$. -/
def fiberLineEquiv (u : U) (c : F) :
    {p : U × F // (Q₀.prod (lineForm 1)) p = c ∧ polar Q₀ u p.1 = 1} ≃ {u' : U // polar Q₀ u u' = 1} where
  toFun p := ⟨p.1.1, p.2.2⟩
  invFun u' := ⟨(u'.1, Function.surjInv (sq_bijective_char2 hF).2 (c - Q₀ u'.1)), by
      refine ⟨?_, u'.2⟩
      simp only [QuadraticMap.prod_apply, lineForm_apply, one_mul]
      rw [Function.surjInv_eq (sq_bijective_char2 hF).2]
      ring⟩
  left_inv p := by
    apply Subtype.ext
    ext
    · rfl
    · apply sq_injective_char2 hF
      simp only
      rw [Function.surjInv_eq (sq_bijective_char2 hF).2]
      have := p.2.1
      simp only [QuadraticMap.prod_apply, lineForm_apply, one_mul] at this
      linear_combination -this
  right_inv u' := rfl

/-- An affine hyperplane $\{u' : b_0(u, u') = 1\}$ ($u \ne 0$, $Q_0$ regular) has $q^{w-1}$ elements. -/
theorem card_polar_eq_one (hQ₀ : (polarBilin Q₀).Nondegenerate) {u : U} (hu : u ≠ 0) :
    Nat.card {u' : U // polar Q₀ u u' = 1} = Nat.card F ^ (finrank F U - 1) := by
  classical
  set f := polarBilin Q₀ u
  have hf : f ≠ 0 := by
    intro h
    apply hu
    apply (QuadraticForm.nondegenerate_polarBilin_iff Q₀).mp hQ₀ u
    intro w
    have := LinearMap.congr_fun h w
    simpa [f] using this
  obtain ⟨w0, hw0⟩ : ∃ w0, f w0 ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  set w1 := (f w0)⁻¹ • w0
  have hw1 : f w1 = 1 := by simp [w1, hw0]
  have hsurj : Function.Surjective f := fun t => ⟨t • w1, by simp [hw1]⟩
  have e : {u' : U // polar Q₀ u u' = 1} ≃ LinearMap.ker f :=
    { toFun := fun u' => ⟨u'.1 - w1, by simp [f, LinearMap.mem_ker, polarBilin_apply_apply] at hw1 ⊢; rw [u'.2]; simp [hw1]⟩
      invFun := fun z => ⟨z.1 + w1, by
        have := z.2
        rw [LinearMap.mem_ker] at this
        have h1 : f (z.1 + w1) = 1 := by rw [map_add, this, hw1, zero_add]
        simpa [f, polarBilin_apply_apply] using h1⟩
      left_inv := fun u' => by apply Subtype.ext; simp
      right_inv := fun z => by apply Subtype.ext; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
  omega

/-- **$r(A, W_0 \perp \langle 1\rangle) = (q^w - 1)\,q^{w-1}$** for every regular plane $A = $ `binForm a c`. -/
theorem isomCount_binForm_line (hQ₀ : (polarBilin Q₀).Nondegenerate) (a c : F) :
    (isomCount (binForm a c) (Q₀.prod (lineForm 1)) : ℝ) =
      ((Nat.card F : ℝ) ^ finrank F U - 1) * (Nat.card F : ℝ) ^ (finrank F U - 1) := by
  classical
  have : Finite U := Module.finite_of_finite F
  rw [isomCount_binForm hF]
  -- the pairs, fibred over the first vector (which has $u \ne 0$)
  let E : {p : (U × F) × (U × F) // (Q₀.prod (lineForm 1)) p.1 = a ∧ (Q₀.prod (lineForm 1)) p.2 = c ∧
      polar (Q₀.prod (lineForm 1)) p.1 p.2 = 1} ≃
      Σ x : {p : U × F // (Q₀.prod (lineForm 1)) p = a ∧ p.1 ≠ 0},
        {p : U × F // (Q₀.prod (lineForm 1)) p = c ∧ polar Q₀ x.1.1 p.1 = 1} :=
    { toFun := fun z => ⟨⟨z.1.1, z.2.1, fun h0 => by
          have := z.2.2.2
          rw [polar_prod_line hF, h0] at this
          simp at this⟩, ⟨z.1.2, z.2.2.1, by have := z.2.2.2; rwa [polar_prod_line hF] at this⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2.1, s.2.2.1, by rw [polar_prod_line hF]; exact s.2.2.2⟩
      left_inv := fun z => rfl
      right_inv := fun s => rfl }
  have : Fintype {p : U × F // (Q₀.prod (lineForm 1)) p = a ∧ p.1 ≠ 0} := Fintype.ofFinite _
  rw [Nat.card_congr E, Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => by
      rw [Nat.card_congr (fiberLineEquiv hF Q₀ x.1.1 c), card_polar_eq_one hF Q₀ hQ₀ x.2.2],
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr (valNeEquiv hF Q₀ a)]
  have hcard : Nat.card {u : U // u ≠ 0} + 1 = Nat.card U := by
    have : Fintype U := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card U := Fintype.card_pos
    omega
  rw [Module.natCard_eq_pow_finrank (K := F) (V := U)] at hcard
  have hc : (Nat.card {u : U // u ≠ 0} : ℝ) = (Nat.card F : ℝ) ^ finrank F U - 1 := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast hcard
  rw [nsmul_eq_mul, hc]
  push_cast
  ring

end Space

/-! ### Spaces whose polar radical is a line $Fw_0$ with $Q(w_0) = 1$ -/

/-- A space whose polar radical is $Fw_0$ with $Q(w_0) = 1$ is $\cong W_0 \perp \langle 1\rangle$ with $W_0$ regular. -/
theorem exists_line_decomp {X : Type} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (QX : QuadraticForm F X) {w0 : X} (hw0 : QX w0 = 1)
    (hrad : ∀ x, (∀ y, polar QX x y = 0) ↔ x ∈ Submodule.span F {w0}) :
    ∃ (U : Submodule F X), (polarBilin (QX.comp U.subtype)).Nondegenerate ∧ finrank F U + 1 = finrank F X ∧
      ((QX.comp U.subtype).prod (lineForm 1)).Equivalent QX := by
  classical
  have hw0ne : w0 ≠ 0 := by rintro rfl; simp at hw0
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (Submodule.span F {w0})
  have hw0rad : ∀ y, polar QX w0 y = 0 := (hrad w0).mpr (Submodule.mem_span_singleton_self w0)
  have hdim : finrank F U + 1 = finrank F X := by
    have := Submodule.finrank_add_eq_of_isCompl hU
    rw [finrank_span_singleton hw0ne] at this
    omega
  let φ : (U × F) →ₗ[F] X := U.subtype.coprod ((LinearMap.id : F →ₗ[F] F).smulRight w0)
  have hφ : ∀ p : U × F, φ p = (p.1 : X) + p.2 • w0 := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, f⟩ h
    rw [hφ] at h
    have hu : (u : X) ∈ Submodule.span F {w0} := by
      rw [eq_neg_of_add_eq_zero_left h]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w0))
    have hu0 : (u : X) = 0 := by
      have := hU.disjoint.eq_bot
      exact (Submodule.disjoint_def.mp hU.disjoint) _ hu u.2
    have hu' : u = 0 := Subtype.ext hu0
    subst hu'
    simp only [Submodule.coe_zero, zero_add, smul_eq_zero] at h
    rcases h with h | h
    · simp [h]
    · exact absurd h hw0ne
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, Module.finrank_self, hdim])).mp hinj⟩
  refine ⟨U, ?_, hdim, ⟨{ toLinearEquiv := LinearEquiv.ofBijective φ hbij, map_app' := fun p => ?_ }⟩⟩
  · rw [QuadraticForm.nondegenerate_polarBilin_iff]
    intro z hz
    apply Subtype.ext
    have hzX : ∀ y, polar QX z y = 0 := by
      intro y
      obtain ⟨⟨u, f⟩, rfl⟩ := hbij.2 y
      rw [hφ, polar_add_right, polar_smul_right, polar_comm QX (z : X) w0, hw0rad, smul_zero, add_zero]
      have := hz u
      simpa [polar] using this
    exact (Submodule.disjoint_def.mp hU.disjoint) _ ((hrad z).mp hzX) z.2
  · show QX (φ p) = _
    rw [hφ, QuadraticMap.map_add QX, QuadraticMap.map_smul, hw0, polar_smul_right, polar_comm, hw0rad]
    simp [QuadraticMap.prod_apply, smul_eq_mul]

/-! ### The induction -/

theorem prop133_line_gen (n : ℕ) : ∀ {V U : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U] (QV : QuadraticForm F V) (Q₀ : QuadraticForm F U),
    (polarBilin QV).Nondegenerate → (polarBilin Q₀).Nondegenerate → finrank F V = 2 * n →
    (isomCount QV (Q₀.prod (lineForm 1)) : ℝ) = radForm (Nat.card F) (2 * n) (finrank F U) := by
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  have hb2 : finrank F (F × F) = 2 := by simp
  induction n with
  | zero =>
    intro V U _ _ _ _ _ _ QV Q₀ hQV hQ₀ hV
    have : Subsingleton V := by rw [← Module.finrank_zero_iff (R := F)]; omega
    rw [isomCount_of_subsingleton, mul_zero, radForm_zero]
    simp
  | succ n ih =>
    intro V U _ _ _ _ _ _ QV Q₀ hQV hQ₀ hV
    obtain ⟨a, c, ⟨τ⟩⟩ := exists_planeIso hF hQV (by omega)
    have hbreg := binForm_nondegenerate hF a c
    obtain ⟨he, hd, hreg⟩ := perpRange_split hbreg τ
    set QV1 := QV.comp (perpRange QV τ.1).subtype
    have hV1reg : (polarBilin QV1).Nondegenerate := hreg hQV
    have hV1dim : finrank F (perpRange QV τ.1) = 2 * n := by rw [hb2] at hd; omega
    obtain ⟨m, hm⟩ := even_finrank_char2 hF Q₀ hQ₀
    set W1 := Q₀.prod (lineForm 1)
    by_cases hw : finrank F U = 0
    · -- $W_0 = 0$: no regular plane is represented, and the formula has the factor $1 - q^0 = 0$
      have : Finite ((F × F) →ₗ[F] (U × F)) := Module.finite_of_finite F
      have h0 : (isomCount (binForm a c) W1 : ℝ) = 0 := by
        rw [isomCount_binForm_line hF Q₀ hQ₀, hw]; simp
      have hempty : IsEmpty (IsoT (binForm a c) W1) := by
        have h0' : isomCount (binForm a c) W1 = 0 := by exact_mod_cast h0
        rw [isomCount, Nat.card_eq_zero] at h0'
        rcases h0' with h | h
        · exact h
        · exact absurd (inferInstance : Finite _) (not_finite_iff_infinite.mpr h)
      rw [isomCount_congr_left W1 he.symm, isomCount_prod_eq hbreg QV1 W1 0 (fun σ => (hempty.false σ).elim), h0,
        zero_mul, hw]
      symm
      unfold radForm
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := 0)
      · simp
      · simp
    obtain ⟨k, hk⟩ : ∃ k, finrank F U = k + 2 := ⟨finrank F U - 2, by omega⟩
    have hR : ∀ σ : IsoT (binForm a c) W1,
        (isomCount QV1 (W1.comp (perpRange W1 σ.1).subtype) : ℝ) = radForm (Nat.card F) (2 * n) k := by
      intro σ
      obtain ⟨heW, hdW, -⟩ := perpRange_split hbreg σ
      set X := perpRange W1 σ.1
      have hw0X : ((0 : U), (1 : F)) ∈ X := by
        rw [mem_perpRange]
        intro p
        rw [polar_prod_line hF]
        simp
      set w0 : X := ⟨((0 : U), (1 : F)), hw0X⟩
      have hQw0 : (W1.comp X.subtype) w0 = 1 := by simp [w0, W1, QuadraticMap.prod_apply]
      have hrad : ∀ x : X, (∀ y : X, polar (W1.comp X.subtype) x y = 0) ↔ x ∈ Submodule.span F {w0} := by
        intro x
        constructor
        · intro hx
          have hall : ∀ z : U × F, polar W1 (x : U × F) z = 0 := by
            intro z
            obtain ⟨⟨p, y⟩, rfl⟩ := (splitMap_bijective hbreg σ).2 z
            rw [splitMap_apply, polar_add_right, polar_comm, x.2 p, zero_add]
            have := hx y
            simpa [polar] using this
          have hu : (x : U × F).1 = 0 := by
            apply (QuadraticForm.nondegenerate_polarBilin_iff Q₀).mp hQ₀
            intro u'
            have := hall (u', 0)
            rwa [polar_prod_line hF] at this
          rw [Submodule.mem_span_singleton]
          refine ⟨(x : U × F).2, Subtype.ext ?_⟩
          show (x : U × F).2 • ((0 : U), (1 : F)) = (x : U × F)
          ext
          · simp [hu]
          · simp
        · intro hx y
          obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
          show polar W1 (t • ((0 : U), (1 : F))) (y : U × F) = 0
          rw [polar_prod_line hF]
          simp
      obtain ⟨U', hU'reg, hU'dim, hU'e⟩ := exists_line_decomp hF (W1.comp X.subtype) hQw0 hrad
      rw [isomCount_congr_right (W' := ↥U' × F) QV1 hU'e.symm, ih QV1 _ hV1reg hU'reg hV1dim]
      congr 1
      rw [hb2] at hdW
      have : finrank F (U × F) = finrank F U + 1 := by simp
      omega
    rw [isomCount_congr_left W1 he.symm, isomCount_prod_eq hbreg QV1 W1 _ hR, isomCount_binForm_line hF Q₀ hQ₀,
      hk, show 2 * (n + 1) = 2 * n + 2 by ring, ← radForm_step hq n k (by
        obtain ⟨m, hm⟩ := even_finrank_char2 hF Q₀ hQ₀; exact ⟨m - 1, by omega⟩)]
    rw [show k + 2 - 1 = k + 1 by omega]

/-- A regular space represented by $W_0 \perp \langle 1\rangle \perp R$ has dimension at most $\dim W_0$. -/
theorem finrank_le_of_rep {V W₀ R : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W₀] [Module F W₀] [FiniteDimensional F W₀] [AddCommGroup R] [Module F R]
    {QV : QuadraticForm F V} (hV : (polarBilin QV).Nondegenerate) (Q₀ : QuadraticForm F W₀)
    (σ : IsoT QV ((Q₀.prod (lineForm 1)).prod (0 : QuadraticForm F R))) : finrank F V ≤ finrank F W₀ := by
  let π : V →ₗ[F] W₀ := (LinearMap.fst F W₀ F).comp ((LinearMap.fst F (W₀ × F) R).comp σ.1)
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply (QuadraticForm.nondegenerate_polarBilin_iff QV).mp hV x
    intro y
    rw [← polar_of_iso σ.1 σ.2.2]
    have h1 : polar ((Q₀.prod (lineForm 1)).prod (0 : QuadraticForm F R)) (σ.1 x) (σ.1 y) =
        polar Q₀ (σ.1 x).1.1 (σ.1 y).1.1 := by
      rw [← polar_prod_line hF Q₀]
      simp [polar, QuadraticMap.prod_apply]
    rw [h1]
    have : (σ.1 x).1.1 = 0 := hx
    rw [this]; simp
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **Kitaoka 1993, Proposition 1.3.3, second case** (p. 18). Let $F$ be a finite field of characteristic $2$ with $q$
elements, $V$ a regular quadratic space of dimension $v$, and $W = W_0 \perp Fw_0 \perp \operatorname{Rad} W$ with
$W_0$ regular of dimension $w$, $Q(w_0) = 1$, $w_0 \in W^\perp$ (so $W^\perp = Fw_0 + \operatorname{Rad} W \ne
\operatorname{Rad} W$), and $\operatorname{Rad} W = R$ carrying the zero form. If $V$ is represented by $W$, then
$r(V, W) = q^{v\dim W - v(v+1)/2}\prod_{w-v+2 \le e \le w,\ e \text{ even}}(1 - q^{-e})$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Prop. 1.3.3, p. 18 (case W^⊥ ≠ Rad W)"]
theorem proposition133_char2 {V W₀ R : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W₀] [Module F W₀] [FiniteDimensional F W₀] [AddCommGroup R] [Module F R] [FiniteDimensional F R]
    (QV : QuadraticForm F V) (hV : (polarBilin QV).Nondegenerate) (Q₀ : QuadraticForm F W₀)
    (hW₀ : (polarBilin Q₀).Nondegenerate)
    (hrep : Nonempty (IsoT QV ((Q₀.prod (lineForm 1)).prod (0 : QuadraticForm F R)))) :
    let q : ℝ := Nat.card F
    let v := finrank F V
    let w := finrank F W₀
    (isomCount QV ((Q₀.prod (lineForm 1)).prod (0 : QuadraticForm F R)) : ℝ) =
      q ^ ((v * finrank F ((W₀ × F) × R) : ℕ) - (v * (v + 1) / 2 : ℕ) : ℤ) *
        ∏ e ∈ (Finset.Icc (w - v + 2) w).filter Even, (1 - q ^ (-(e : ℤ))) := by
  intro q v w
  have hq : (0 : ℝ) < Nat.card F := by exact_mod_cast Nat.card_pos
  obtain ⟨σ⟩ := hrep
  have hvw : v ≤ w := finrank_le_of_rep hF hV Q₀ σ
  obtain ⟨m, hm⟩ := even_finrank_char2 hF QV hV
  have h1 := proposition133_rad QV hV (Q₀.prod (lineForm 1)) (R := R)
  have h2 := prop133_line_gen hF m QV Q₀ hV hW₀ (by omega)
  rw [h1]
  push_cast
  rw [show 2 * m = v by omega] at h2
  rw [h2, radForm, show w + 2 - v = w - v + 2 by omega]
  have hdim : finrank F ((W₀ × F) × R) = w + 1 + finrank F R := by simp [Module.finrank_prod]; ring
  rw [hdim, mul_comm _ (∏ e ∈ _, _), mul_comm _ (∏ e ∈ _, _), mul_assoc]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ hq.ne']
  congr 1
  push_cast
  ring

end QuadFormsKB.Kitaoka.FqCount
