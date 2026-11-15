/-
# Kitaoka 1993, Lemma 5.6.9: isometries of a totally isotropic space into a regular space over $\mathbb F_q$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.9, p. 120 (printed page); the
statement `Kitaoka.Lemma569` is in `Wave3/Ch5Lemma569.lean`.

**Proves** `lemma569 : Lemma569` (unconditional). For a finite field $F = \mathbb F_q$, a regular quadratic space $V$ of
dimension $v$ and the totally isotropic space $U = F^u$, the number $r(U, V)$ of isometries $U \to V$ (injective linear
maps with $Q(\sigma(x)) = 0$) satisfies
$$q^{u(u+1)/2 - uv}\,r(U, V) = \prod_{i=0}^{u-1}\bigl(1 - q^{-(v-2u+2i+1)}\bigr) \ (v \text{ odd}),\quad
\prod_{i=0}^{u-1}\bigl(1 - \chi(V)q^{-(v-2u+2i+2)/2}\bigr)\bigl(1 + \chi(V)q^{-(v-2u+2i)/2}\bigr) \ (v \text{ even}).$$

**Proof** (Kitaoka's induction on $u$). An isometry $\sigma : F^{u+1} \to V$ is determined by the isotropic vector
$y = \sigma(e_0) \ne 0$ and by $\tau = \sigma|_{F^u}$ (the last $u$ coordinates). Take $y'$ with $Q(y') = 0$,
$B(y, y') = 1$ (`QuadraticForm.Witt.hyperbolic_partner`) and $V_0 = \{y, y'\}^\perp$, so $V = (Fy + Fy') \perp V_0$,
$y^\perp = Fy \oplus V_0$, $\dim V_0 = v - 2$ and $\chi(V_0) = \chi(V)$. Writing $\tau(w) = f(w)y + \eta(w)$, the
pairs $(f, \eta)$ with $f$ a linear form on $F^u$ and $\eta : F^u \to V_0$ an isometry correspond bijectively to the
$\sigma$ with $\sigma(e_0) = y$ (`fiberEquiv`). Hence $r(u+1, V) = (a(0, V) - 1)\,q^u\,r(u, V_0)$ (Kitaoka's
$r(U, V) = q^{u-1}r(Fx, V)r(U_1, V_0)$), with $a(0, V)$ from Lemma 1.3.1 (`lemma131Gen`); the product formula follows
by induction. The hypothesis $r(U, V) > 0$ gives $2u \le v$.

Unlike Kitaoka, the proof does not use that $O(V)$ acts transitively on isotropic vectors: the count of the fibre over
each $y$ is computed directly, and depends on $y$ only through $\dim V_0$ and $\chi(V_0)$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Counting

open QuadraticMap Module QuadraticForm.Witt

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

namespace FqCount

variable {K : Type} [Field K] [Finite K]

/-- $r(F^u, V)$ for a general space $V$: the number of injective linear maps $\sigma : F^u \to V$ with
$Q(\sigma(x)) = 0$ for all $x$ (`Kitaoka.isoCountFq` is the case $V = F^v$). -/
def isoCount (u : ℕ) {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) : ℕ :=
  Nat.card {σ : (Fin u → K) →ₗ[K] V // Function.Injective σ ∧ ∀ x, Q (σ x) = 0}

/-- $\chi(V)$ for a general space (`Kitaoka.chiV` is the case $V = F^v$). -/
def chiGen {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : ℝ :=
  if Odd (finrank K V) then 0 else if QuadraticForm.wittIndex Q = finrank K V / 2 then 1 else -1

theorem chiV_eq_chiGen {v : ℕ} (QV : QuadraticForm K (Fin v → K)) : chiV QV = chiGen QV := by
  simp [chiV, chiGen, Module.finrank_fin_fun]

/-- $Z(v, \chi) = q^{v-1} - \chi q^{v/2-1} + \chi q^{v/2}$, the value of $a(0, V)$ in Lemma 1.3.1. -/
def zeroVal (q : ℝ) (v : ℕ) (c : ℝ) : ℝ := q ^ ((v : ℤ) - 1) - c * q ^ (((v / 2 : ℕ) : ℤ) - 1) + c * q ^ (v / 2)

/-- **Lemma 1.3.1 for a general space**: $a(0, V) = Z(\dim V, \chi(V))$. -/
theorem lemma131Gen {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) :
    (valCount Q 0 : ℝ) = zeroVal (Nat.card K) (finrank K V) (chiGen Q) := by
  obtain ⟨U, _, _, _, Qa, ha, hw, hdim, hform⟩ := exists_valCount_formula Q hQ
  have hq : (0 : ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos
  rw [hform, valCount_zero_of_anisotropic Qa ha, zeroVal]
  set m := QuadraticForm.wittIndex Q with hm
  set u := finrank K V with hu
  have hcases : finrank K U = 0 ∨ finrank K U = 1 ∨ finrank K U = 2 := by omega
  rcases hcases with hw0 | hw1 | hw2
  · have hu2 : u / 2 = m := by omega
    have hchi : chiGen Q = 1 := by
      simp only [chiGen, ← hu]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨m, by omega⟩), if_pos (by rw [← hm]; omega)]
    rw [hchi, hw0, hu2]
    simp only [Nat.cast_zero, zero_sub, zpow_neg_one, zpow_sub_one₀ hq.ne', zpow_natCast, Nat.cast_one]
    ring
  · have hchi : chiGen Q = 0 := by
      simp only [chiGen, ← hu]; rw [if_pos ⟨m, by omega⟩]
    rw [hchi, hw1]
    simp
  · have hu2 : u / 2 = m + 1 := by omega
    have hchi : chiGen Q = -1 := by
      simp only [chiGen, ← hu]
      rw [if_neg (by rw [Nat.not_odd_iff_even]; exact ⟨m + 1, by omega⟩), if_neg (by rw [← hm]; omega)]
    rw [hchi, hw2, hu2]
    simp only [Nat.cast_ofNat, zpow_sub_one₀ hq.ne', zpow_natCast, Nat.cast_add, Nat.cast_one]
    simp only [zpow_add_one₀ hq.ne', zpow_natCast]
    field_simp
    ring

/-! ### The complement of a hyperbolic pair -/

section Complement

variable {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- $V_0 = \{y, y'\}^\perp$. -/
def perpPair (y y' : V) : Submodule K V :=
  LinearMap.ker (polarBilin Q y) ⊓ LinearMap.ker (polarBilin Q y')

theorem mem_perpPair {y y' x : V} : x ∈ perpPair Q y y' ↔ polar Q y x = 0 ∧ polar Q y' x = 0 := by
  simp [perpPair]

variable {Q} {y y' : V} (hy : Q y = 0) (hy' : Q y' = 0) (hyy' : polar Q y y' = 1)
include hy hy' hyy'

theorem polar_y'_y : polar Q y' y = 1 := by rw [polar_comm]; exact hyy'

theorem polar_y_y : polar Q y y = 0 := by rw [polar_self_eq, hy, mul_zero]

theorem polar_y'_y' : polar Q y' y' = 0 := by rw [polar_self_eq, hy', mul_zero]

/-- The decomposition $x = B(x, y')y + B(x, y)y' + x_0$ with $x_0 \in V_0$. -/
theorem sub_mem_perpPair (x : V) : x - polar Q x y' • y - polar Q x y • y' ∈ perpPair Q y y' := by
  have h1 := polar_y'_y hy hy' hyy'
  have h2 := polar_y_y hy hy' hyy'
  have h3 := polar_y'_y' hy hy' hyy'
  rw [mem_perpPair]
  simp only [polar_sub_right, polar_smul_right, smul_eq_mul, h1, h2, h3, hyy', polar_comm Q y x,
    polar_comm Q y' x]
  constructor <;> ring

/-- The isometry $H \perp V_0 \cong V$, $((a, b), x_0) \mapsto ay + by' + x_0$ (the construction of
`QuadraticForm.Witt.exists_split_hyperbolicPlane`, with the partner $y'$ fixed). -/
def hypSplit :
    ((QuadraticForm.hyperbolicPlane K).prod (Q.comp (perpPair Q y y').subtype)).IsometryEquiv Q := by
  have h1 := polar_y'_y hy hy' hyy'
  have h2 := polar_y_y hy hy' hyy'
  have h3 := polar_y'_y' hy hy' hyy'
  let F : (K × K) × perpPair Q y y' →ₗ[K] V :=
    LinearMap.coprod ((LinearMap.fst K K K).smulRight y + (LinearMap.snd K K K).smulRight y')
      (perpPair Q y y').subtype
  have hF : ∀ x : (K × K) × perpPair Q y y', F x = x.1.1 • y + x.1.2 • y' + x.2 := fun x => rfl
  have hFQ : ∀ x, Q (F x) =
      ((QuadraticForm.hyperbolicPlane K).prod (Q.comp (perpPair Q y y').subtype)) x := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    obtain ⟨hu1, hu2⟩ := (mem_perpPair Q).mp hu
    rw [hF, map_add_eq, map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, hy, hy',
      polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left, polar_smul_right, hu1,
      hu2, hyy']
    simp [smul_eq_mul]
  have hFy : ∀ x : (K × K) × perpPair Q y y', polar Q (F x) y = x.1.2 := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    rw [hF, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, h2, h1,
      polar_comm, ((mem_perpPair Q).mp hu).1]
    simp
  have hFy' : ∀ x : (K × K) × perpPair Q y y', polar Q (F x) y' = x.1.1 := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    rw [hF, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hyy', h3,
      polar_comm, ((mem_perpPair Q).mp hu).2]
    simp
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨⟨a, b⟩, u⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hb : b = 0 := by
      have := hFy ⟨⟨a, b⟩, u⟩; rw [hx, polar_zero_left] at this; exact this.symm
    have ha : a = 0 := by
      have := hFy' ⟨⟨a, b⟩, u⟩; rw [hx, polar_zero_left] at this; exact this.symm
    have hu : (u : V) = 0 := by simpa [hF, ha, hb] using hx
    rw [Submodule.mem_bot]
    ext <;> simp [ha, hb, hu]
  have hsurj : Function.Surjective F := fun x =>
    ⟨⟨(polar Q x y', polar Q x y), ⟨_, sub_mem_perpPair hy hy' hyy' x⟩⟩, by rw [hF]; simp⟩
  exact { LinearEquiv.ofBijective F ⟨hinj, hsurj⟩ with map_app' := fun x => hFQ x }

end Complement

/-- Splitting off a hyperbolic plane keeps $\chi$ and lowers the dimension by $2$. -/
theorem chiGen_finrank_of_hyp {V W : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K V} {P : QuadraticForm K W}
    (hQ : Q.radical = ⊥) (e : ((QuadraticForm.hyperbolicPlane K).prod P).IsometryEquiv Q) :
    P.radical = ⊥ ∧ finrank K V = finrank K W + 2 ∧ chiGen P = chiGen Q := by
  have hP : P.radical = ⊥ :=
    QuadraticForm.radical_eq_bot_of_prod_right (radical_eq_bot_of_isometryEquiv e hQ)
  have hdim : finrank K V = finrank K W + 2 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, Module.finrank_self]; ring
  obtain ⟨U, _, _, _, Qa, ha, ⟨g⟩⟩ := QuadraticForm.wittIndex_spec P hP
  have hW : QuadraticForm.wittIndex Q = QuadraticForm.wittIndex P + 1 := by
    refine (QuadraticForm.eq_wittIndex Q hQ ha ⟨?_⟩).symm
    exact e.symm.trans (((QuadraticMap.IsometryEquiv.refl _).prod g).trans
      ((prodAssoc _ _ _).symm.trans ((hyperbolicSpaceSucc _).prod (QuadraticMap.IsometryEquiv.refl _))))
  refine ⟨hP, hdim, ?_⟩
  simp only [chiGen, hdim, hW]
  have hodd : Odd (finrank K W + 2) ↔ Odd (finrank K W) := by
    constructor <;> intro h
    · obtain ⟨k, hk⟩ := h; exact ⟨k - 1, by omega⟩
    · obtain ⟨k, hk⟩ := h; exact ⟨k + 1, by omega⟩
  have hidx : QuadraticForm.wittIndex P + 1 = (finrank K W + 2) / 2 ↔
      QuadraticForm.wittIndex P = finrank K W / 2 := by omega
  simp only [hodd, hidx]

/-- A nonzero isotropic vector of a space with zero radical has a hyperbolic partner. -/
theorem exists_partner {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (hQ : Q.radical = ⊥)
    {y : V} (hy : Q y = 0) (hy0 : y ≠ 0) : ∃ y', Q y' = 0 ∧ polar Q y y' = 1 := by
  have hyR : y ∉ LinearMap.ker (polarBilin Q) := fun h =>
    hy0 (by rw [← Submodule.mem_bot K, ← hQ]; exact ⟨hy, h⟩)
  rw [mem_ker_polarBilin] at hyR
  push Not at hyR
  obtain ⟨w, hw⟩ := hyR
  have hu : polar Q ((polar Q y w)⁻¹ • w) y = 1 := by
    rw [polar_smul_left, smul_eq_mul, polar_comm Q w y, inv_mul_cancel₀ hw]
  obtain ⟨hv', hvv'⟩ := hyperbolic_partner Q hy hu
  exact ⟨_, hv', hvv'⟩

/-! ### The fibre over an isotropic vector -/

/-- $w \mapsto (0, w_0, \dots, w_{u-1})$. -/
def consZero (u : ℕ) : (Fin u → K) →ₗ[K] (Fin (u + 1) → K) :=
  LinearMap.pi fun j => Fin.cases (0 : (Fin u → K) →ₗ[K] K) (fun i => LinearMap.proj i) j

@[simp] theorem consZero_zero (u : ℕ) (w : Fin u → K) : consZero u w 0 = 0 := by
  simp [consZero]

@[simp] theorem consZero_succ (u : ℕ) (w : Fin u → K) (i : Fin u) : consZero u w i.succ = w i := by
  simp [consZero]

/-- $x \mapsto x_0\, y + \tau(x_1, \dots, x_u)$. -/
def combine (u : ℕ) {V : Type} [AddCommGroup V] [Module K V] (y : V) (τ : (Fin u → K) →ₗ[K] V) :
    (Fin (u + 1) → K) →ₗ[K] V :=
  (LinearMap.proj 0).smulRight y + τ ∘ₗ LinearMap.funLeft K K Fin.succ

section Fiber

variable {u : ℕ} {V : Type} [AddCommGroup V] [Module K V]

theorem combine_apply (y : V) (τ : (Fin u → K) →ₗ[K] V) (x : Fin (u + 1) → K) :
    combine u y τ x = x 0 • y + τ (fun i => x i.succ) := rfl

theorem combine_consZero (y : V) (τ : (Fin u → K) →ₗ[K] V) (w : Fin u → K) :
    combine u y τ (consZero u w) = τ w := by
  rw [combine_apply]; simp

theorem combine_single (y : V) (τ : (Fin u → K) →ₗ[K] V) : combine u y τ (Pi.single 0 1) = y := by
  rw [combine_apply]
  have : (fun i : Fin u => (Pi.single 0 1 : Fin (u + 1) → K) i.succ) = 0 := by
    funext i; simp [Fin.succ_ne_zero]
  simp only [this, Pi.single_eq_same, one_smul, map_zero, add_zero]

theorem decomp_vec (x : Fin (u + 1) → K) :
    x = x 0 • Pi.single 0 1 + consZero u (fun i => x i.succ) := by
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ i => simp [Pi.single_apply, Fin.succ_ne_zero]

theorem eq_combine (σ : (Fin (u + 1) → K) →ₗ[K] V) :
    σ = combine u (σ (Pi.single 0 1)) (σ ∘ₗ consZero u) := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [decomp_vec x]
  rw [combine_apply, map_add, map_smul]
  rfl

/-- An isometry $F^u \to V$ of the totally isotropic space: injective with $Q \circ \sigma = 0$. -/
def IsIso (Q : QuadraticForm K V) (σ : (Fin u → K) →ₗ[K] V) : Prop :=
  Function.Injective σ ∧ ∀ x, Q (σ x) = 0

variable {Q : QuadraticForm K V} {y y' : V} (hy : Q y = 0) (hy' : Q y' = 0) (hyy' : polar Q y y' = 1)
include hy hy' hyy'

/-- For an isometry $\sigma$ with $\sigma(e_0) = y$, $B(y, \tau(w)) = 0$. -/
theorem polar_y_of_iso {σ : (Fin (u + 1) → K) →ₗ[K] V} (hσ : IsIso Q σ) (h0 : σ (Pi.single 0 1) = y)
    (w : Fin u → K) : polar Q y (σ (consZero u w)) = 0 := by
  have h1 := hσ.2 (Pi.single 0 1 + consZero u w)
  rw [map_add, h0] at h1
  simp only [polar, h1, hy, hσ.2 (consZero u w)]
  ring

theorem tau_sub_mem {σ : (Fin (u + 1) → K) →ₗ[K] V} (hσ : IsIso Q σ) (h0 : σ (Pi.single 0 1) = y)
    (w : Fin u → K) :
    σ (consZero u w) - polar Q y' (σ (consZero u w)) • y ∈ perpPair Q y y' := by
  rw [mem_perpPair]
  have h1 := polar_y'_y hy hy' hyy'
  have h2 := polar_y_y hy hy' hyy'
  simp only [polar_sub_right, polar_smul_right, smul_eq_mul, h1, h2, polar_y_of_iso hy hy' hyy' hσ h0 w]
  constructor <;> ring

/-- The $V_0$-part $\eta$ of $\tau = \sigma|_{F^u}$. -/
def etaOf {σ : (Fin (u + 1) → K) →ₗ[K] V} (hσ : IsIso Q σ) (h0 : σ (Pi.single 0 1) = y) :
    (Fin u → K) →ₗ[K] perpPair Q y y' :=
  LinearMap.codRestrict _ (σ ∘ₗ consZero u - ((polarBilin Q y') ∘ₗ σ ∘ₗ consZero u).smulRight y)
    (fun w => tau_sub_mem hy hy' hyy' hσ h0 w)

theorem etaOf_apply {σ : (Fin (u + 1) → K) →ₗ[K] V} (hσ : IsIso Q σ) (h0 : σ (Pi.single 0 1) = y)
    (w : Fin u → K) :
    (etaOf hy hy' hyy' hσ h0 w : V) = σ (consZero u w) - polar Q y' (σ (consZero u w)) • y := rfl

theorem etaOf_iso {σ : (Fin (u + 1) → K) →ₗ[K] V} (hσ : IsIso Q σ) (h0 : σ (Pi.single 0 1) = y) :
    IsIso (Q.comp (perpPair Q y y').subtype) (etaOf hy hy' hyy' hσ h0) := by
  refine ⟨fun w w' h => ?_, fun w => ?_⟩
  · have h' : ((etaOf hy hy' hyy' hσ h0 (w - w')) : V) = 0 := by rw [map_sub, h, sub_self]; rfl
    rw [etaOf_apply] at h'
    set c := polar Q y' (σ (consZero u (w - w')))
    have h3 : σ (consZero u (w - w') - c • Pi.single 0 1) = 0 := by
      rw [map_sub, map_smul, h0]; exact h'
    have h4 := hσ.1 (h3.trans (map_zero σ).symm)
    have h5 : ∀ i, (w - w') i = 0 := fun i => by
      have := congrFun h4 i.succ
      simpa [Pi.single_apply, Fin.succ_ne_zero] using this
    funext i; have := h5 i; simp only [Pi.sub_apply] at this; exact sub_eq_zero.1 this
  · simp only [QuadraticMap.comp_apply, Submodule.coe_subtype, etaOf_apply]
    rw [sub_eq_add_neg, ← neg_smul, map_add_smul, hy, hσ.2, polar_comm Q _ y,
      polar_y_of_iso hy hy' hyy' hσ h0 w]
    ring

/-- The isometry $F^{u+1} \to V$ built from a linear form $f$ and an isometry $\eta : F^u \to V_0$. -/
def ofPair (p : ((Fin u → K) →ₗ[K] K) × ((Fin u → K) →ₗ[K] perpPair Q y y')) :
    (Fin (u + 1) → K) →ₗ[K] V :=
  combine u y (p.1.smulRight y + (perpPair Q y y').subtype ∘ₗ p.2)

theorem ofPair_single (p : ((Fin u → K) →ₗ[K] K) × ((Fin u → K) →ₗ[K] perpPair Q y y')) :
    ofPair p (Pi.single 0 1) = y := combine_single _ _

theorem ofPair_iso (p : ((Fin u → K) →ₗ[K] K) × ((Fin u → K) →ₗ[K] perpPair Q y y'))
    (hp : IsIso (Q.comp (perpPair Q y y').subtype) p.2) : IsIso Q (ofPair p) := by
  have h3 := polar_y'_y hy hy' hyy'
  have key : ∀ x : Fin (u + 1) → K, ofPair p x =
      (x 0 + p.1 (fun i => x i.succ)) • y + (p.2 (fun i => x i.succ) : V) := by
    intro x
    simp only [ofPair, combine_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, Submodule.coe_subtype, add_smul]
    abel
  refine ⟨?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, key] at hx
    have hm := (p.2 (fun i => x i.succ)).2
    rw [mem_perpPair] at hm
    have hc : x 0 + p.1 (fun i => x i.succ) = 0 := by
      have := congrArg (polar Q y') hx
      rw [polar_add_right, polar_smul_right, h3, hm.2, polar_zero_right] at this
      simpa using this
    rw [hc, zero_smul, zero_add] at hx
    have ht : (fun i : Fin u => x i.succ) = 0 :=
      hp.1 (Subtype.ext (by rw [hx, map_zero]; rfl))
    have hx0 : x 0 = 0 := by rw [ht, map_zero, add_zero] at hc; exact hc
    rw [Submodule.mem_bot]
    funext j
    cases j using Fin.cases with
    | zero => exact hx0
    | succ i => exact congrFun ht i
  · rw [key, add_comm, map_add_smul, hy]
    have hm := (p.2 (fun i => x i.succ)).2
    rw [mem_perpPair] at hm
    have := hp.2 (fun i => x i.succ)
    simp only [QuadraticMap.comp_apply, Submodule.coe_subtype] at this
    rw [this, polar_comm, hm.1]
    ring

/-- **The fibre over $y$**: isometries $\sigma : F^{u+1} \to V$ with $\sigma(e_0) = y$ correspond to pairs $(f, \eta)$
of a linear form on $F^u$ and an isometry $\eta : F^u \to V_0$. -/
def fiberEquiv :
    {σ : (Fin (u + 1) → K) →ₗ[K] V // IsIso Q σ ∧ σ (Pi.single 0 1) = y} ≃
      ((Fin u → K) →ₗ[K] K) ×
        {η : (Fin u → K) →ₗ[K] perpPair Q y y' // IsIso (Q.comp (perpPair Q y y').subtype) η} where
  toFun σ := ((polarBilin Q y') ∘ₗ σ.1 ∘ₗ consZero u,
    ⟨etaOf hy hy' hyy' σ.2.1 σ.2.2, etaOf_iso hy hy' hyy' σ.2.1 σ.2.2⟩)
  invFun p := ⟨ofPair (p.1, p.2.1), ofPair_iso hy hy' hyy' (p.1, p.2.1) p.2.2,
    ofPair_single hy hy' hyy' _⟩
  left_inv σ := by
    apply Subtype.ext
    simp only
    conv_rhs => rw [eq_combine σ.1, σ.2.2]
    simp only [ofPair]
    congr 1
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      Submodule.coe_subtype, etaOf_apply, polarBilin_apply_apply]
    abel
  right_inv p := by
    have h3 := polar_y'_y hy hy' hyy'
    obtain ⟨f, η, hη⟩ := p
    have hτ : ∀ w, ofPair (f, η) (consZero u w) = f w • y + (η w : V) := by
      intro w
      simp only [ofPair, combine_consZero, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.comp_apply, Submodule.coe_subtype]
    have hf : ∀ w, polar Q y' (f w • y + (η w : V)) = f w := by
      intro w
      have hm := (η w).2
      rw [mem_perpPair] at hm
      rw [polar_add_right, polar_smul_right, h3, hm.2]; simp
    refine Prod.ext ?_ (Subtype.ext ?_)
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, polarBilin_apply_apply]
      rw [hτ, hf]
    · refine LinearMap.ext fun w => Subtype.ext ?_
      simp only
      rw [etaOf_apply, hτ, hf]
      simp

end Fiber

/-! ### The recursion -/

/-- $g(0, v, \chi) = 1$, $g(u + 1, v, \chi) = (Z(v, \chi) - 1)\,q^u\,g(u, v - 2, \chi)$. -/
def gRec (q : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | u + 1, v, c => (zeroVal q v c - 1) * q ^ u * gRec q u (v - 2) c

theorem isoCount_zero {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    isoCount 0 Q = 1 := by
  rw [isoCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, fun a b _ => Subsingleton.elim a b, fun x => by simp⟩, fun σ => Subtype.ext ?_⟩
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **The count** $r(u, V) = g(u, \dim V, \chi(V))$ for every $V$ with zero radical. -/
theorem isoCount_eq (u : ℕ) : ∀ {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), Q.radical = ⊥ →
    (isoCount u Q : ℝ) = gRec (Nat.card K) u (finrank K V) (chiGen Q) := by
  induction u with
  | zero => intro V _ _ _ Q _; simp [isoCount_zero, gRec]
  | succ u ih =>
    intro V _ _ _ Q hQ
    classical
    have : Finite V := Module.finite_of_finite K
    let Y := {y : V // y ≠ 0 ∧ Q y = 0}
    have : Fintype Y := Fintype.ofFinite Y
    let A := {σ : (Fin (u + 1) → K) →ₗ[K] V // IsIso Q σ}
    have hYof : ∀ σ : A, σ.1 (Pi.single 0 1) ≠ 0 ∧ Q (σ.1 (Pi.single 0 1)) = 0 := fun σ =>
      ⟨fun h => by
        have := σ.2.1 (h.trans (map_zero σ.1).symm)
        have := congrFun this 0
        simp at this, σ.2.2 _⟩
    let fY : A → Y := fun σ => ⟨σ.1 (Pi.single 0 1), hYof σ⟩
    have e1 : A ≃ Σ y : Y, {σ : A // fY σ = y} := (Equiv.sigmaFiberEquiv fY).symm
    -- each fibre
    have hfib : ∀ y : Y, (Nat.card {σ : A // fY σ = y} : ℝ) =
        (Nat.card K : ℝ) ^ u * gRec (Nat.card K) u (finrank K V - 2) (chiGen Q) := by
      intro y
      obtain ⟨y', hy', hyy'⟩ := exists_partner hQ y.2.2 y.2.1
      have e2 : {σ : A // fY σ = y} ≃
          {σ : (Fin (u + 1) → K) →ₗ[K] V // IsIso Q σ ∧ σ (Pi.single 0 1) = y.1} :=
        { toFun := fun σ => ⟨σ.1.1, σ.1.2, congrArg Subtype.val σ.2⟩
          invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, Subtype.ext σ.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr (e2.trans (fiberEquiv y.2.2 hy' hyy')), Nat.card_prod]
      have hdual : Nat.card ((Fin u → K) →ₗ[K] K) = Nat.card K ^ u := by
        rw [← Nat.card_congr ((Pi.basisFun K (Fin u)).constr K).toEquiv, Nat.card_fun,
          Nat.card_eq_fintype_card (α := Fin u), Fintype.card_fin]
      obtain ⟨hP, hdim, hchi⟩ := chiGen_finrank_of_hyp hQ (hypSplit y.2.2 hy' hyy')
      have hIH := ih (Q.comp (perpPair Q y.1 y').subtype) hP
      rw [hdual]
      push_cast
      rw [← hchi, show finrank K V - 2 = finrank K (perpPair Q y.1 y') by omega]
      congr 1
    have hfin : ∀ y : Y, Finite {σ : A // fY σ = y} := fun y => by
      have : Finite ((Fin (u + 1) → K) →ₗ[K] V) :=
        Finite.of_injective (fun f : (Fin (u + 1) → K) →ₗ[K] V => (f : (Fin (u + 1) → K) → V))
          DFunLike.coe_injective
      infer_instance
    show (Nat.card A : ℝ) = _
    rw [Nat.card_congr e1, Nat.card_sigma]
    push_cast
    simp only [hfib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- the number of nonzero isotropic vectors
    have hY : (Fintype.card Y : ℝ) = valCount Q 0 - 1 := by
      have e3 : Option Y ≃ {x : V // Q x = 0} :=
        { toFun := fun o => o.elim ⟨0, map_zero Q⟩ fun y => ⟨y.1, y.2.2⟩
          invFun := fun x => if h : x.1 = 0 then none else some ⟨x.1, h, x.2⟩
          left_inv := fun o => by
            cases o with
            | none => simp
            | some y => simp [y.2.1]
          right_inv := fun x => by
            by_cases h : x.1 = 0
            · simp only [h, dite_true, Option.elim]; exact Subtype.ext h.symm
            · simp [h] }
      rw [valCount, ← Nat.card_congr e3, Finite.card_option, Nat.card_eq_fintype_card]
      push_cast; ring
    rw [hY, lemma131Gen Q hQ, gRec]
    ring

/-- If $V$ (zero radical) has an isometry of $F^u$, then $2u \le \dim V$. -/
theorem two_mul_le_of_isoCount_pos (u : ℕ) : ∀ {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), Q.radical = ⊥ → 0 < isoCount u Q →
    2 * u ≤ finrank K V := by
  induction u with
  | zero => intros; omega
  | succ u ih =>
    intro V _ _ _ Q hQ hpos
    have : Finite V := Module.finite_of_finite K
    obtain ⟨⟨σ, hσ⟩⟩ := (Nat.card_pos_iff.1 hpos).1
    set y := σ (Pi.single 0 1)
    have hy0 : y ≠ 0 := fun h => by
      have := hσ.1 (h.trans (map_zero σ).symm)
      have := congrFun this 0
      simp at this
    obtain ⟨y', hy', hyy'⟩ := exists_partner hQ (hσ.2 _) hy0
    obtain ⟨hP, hdim, -⟩ := chiGen_finrank_of_hyp hQ (hypSplit (hσ.2 _) hy' hyy')
    have p := fiberEquiv (u := u) (hσ.2 _) hy' hyy' ⟨σ, hσ, rfl⟩
    have hpos' : 0 < isoCount u (Q.comp (perpPair Q y y').subtype) := by
      have : Finite ((Fin u → K) →ₗ[K] perpPair Q y y') :=
        Finite.of_injective (fun f : (Fin u → K) →ₗ[K] perpPair Q y y' => (f : (Fin u → K) → perpPair Q y y'))
          DFunLike.coe_injective
      rw [isoCount]
      exact Nat.card_pos_iff.2 ⟨⟨p.2⟩, inferInstance⟩
    have := ih _ hP hpos'
    omega

/-! ### The closed form -/

/-- One step of the induction for the closed form. -/
theorem closed_step {q : ℝ} (hq : q ≠ 0) (u : ℕ) (E E' n : ℤ) (hE : E + n + u = E') (Z P F g : ℝ)
    (hg : q ^ E' * g = P) (hZ : Z - 1 = q ^ n * F) : q ^ E * ((Z - 1) * q ^ u * g) = P * F := by
  rw [hZ, ← hg, ← hE, zpow_add₀ hq, zpow_add₀ hq, zpow_natCast]
  ring

/-- The exponent $E(u, v) = u(u+1)/2 - uv$. -/
def expE (u v : ℕ) : ℤ := ((u * (u + 1) / 2 : ℕ) : ℤ) - (u : ℤ) * v

theorem expE_step (u v : ℕ) (hv : 2 ≤ v) (n : ℤ) (hn : n = (v : ℤ) - 1) :
    expE (u + 1) v + n + u = expE u (v - 2) := by
  have hdiv : (u + 1) * (u + 1 + 1) / 2 = u * (u + 1) / 2 + (u + 1) := by
    rw [show (u + 1) * (u + 1 + 1) = u * (u + 1) + 2 * (u + 1) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  simp only [expE, hdiv, hn]
  push_cast [Nat.cast_sub hv]
  ring

/-- The closed form for odd $v$. -/
theorem gRec_odd {q : ℝ} (hq : q ≠ 0) (u : ℕ) : ∀ v : ℕ, Odd v → 2 * u ≤ v →
    q ^ expE u v * gRec q u v 0 =
      ∏ i ∈ Finset.range u, (1 - q ^ (-((v : ℤ) - 2 * u + 2 * i + 1))) := by
  induction u with
  | zero => intro v _ _; simp [expE, gRec]
  | succ u ih =>
    intro v hv hle
    have hv2 : 2 ≤ v := by omega
    have hodd : Odd (v - 2) := by obtain ⟨k, hk⟩ := hv; exact ⟨k - 1, by omega⟩
    have hIH := ih (v - 2) hodd (by omega)
    rw [gRec, Finset.prod_range_succ]
    have hfac : ∀ i ∈ Finset.range u, (1 - q ^ (-((v : ℤ) - 2 * ((u + 1 : ℕ) : ℤ) + 2 * i + 1))) =
        (1 - q ^ (-(((v - 2 : ℕ) : ℤ) - 2 * u + 2 * i + 1))) := by
      intro i _; congr 3; push_cast [Nat.cast_sub hv2]; ring
    rw [Finset.prod_congr rfl hfac]
    refine closed_step hq u _ _ ((v : ℤ) - 1) (expE_step u v hv2 _ rfl) _ _ _ _ hIH ?_
    have hz : zeroVal q v 0 = q ^ ((v : ℤ) - 1) := by simp [zeroVal]
    rw [hz, show -((v : ℤ) - 2 * ((u + 1 : ℕ) : ℤ) + 2 * (u : ℕ) + 1) = -((v : ℤ) - 1) by push_cast; ring,
      zpow_neg, mul_sub, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hq)]

/-- The closed form for even $v = 2k$ ($\chi = \pm 1$). -/
theorem gRec_even {q : ℝ} (hq : q ≠ 0) {c : ℝ} (hc : c ^ 2 = 1) (u : ℕ) : ∀ k : ℕ, u ≤ k →
    q ^ expE u (2 * k) * gRec q u (2 * k) c =
      ∏ i ∈ Finset.range u, (1 - c * q ^ (-((k : ℤ) - u + i + 1))) * (1 + c * q ^ (-((k : ℤ) - u + i))) := by
  induction u with
  | zero => intro k _; simp [expE, gRec]
  | succ u ih =>
    intro k hle
    have hk1 : 1 ≤ k := by omega
    have hIH := ih (k - 1) (by omega)
    rw [show 2 * (k - 1) = 2 * k - 2 by omega] at hIH
    rw [gRec, Finset.prod_range_succ]
    have hfac : ∀ i ∈ Finset.range u,
        (1 - c * q ^ (-((k : ℤ) - ((u + 1 : ℕ) : ℤ) + i + 1))) * (1 + c * q ^ (-((k : ℤ) - ((u + 1 : ℕ) : ℤ) + i))) =
        (1 - c * q ^ (-(((k - 1 : ℕ) : ℤ) - u + i + 1))) * (1 + c * q ^ (-(((k - 1 : ℕ) : ℤ) - u + i))) := by
      intro i _; push_cast [Nat.cast_sub hk1]; ring_nf
    rw [Finset.prod_congr rfl hfac]
    refine closed_step hq u _ _ ((2 * k : ℕ) - 1 : ℤ) (expE_step u (2 * k) (by omega) _ rfl) _ _ _ _ hIH ?_
    -- `Z(2k, c) - 1 = q^{2k-1}(1 - c q^{-k})(1 + c q^{-(k-1)})`
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e1 : (((2 * (m + 1) : ℕ) : ℤ) - 1) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (((2 * (m + 1) / 2 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by
      rw [show 2 * (m + 1) / 2 = m + 1 by omega]; push_cast; ring
    have e3 : 2 * (m + 1) / 2 = m + 1 := by omega
    have e4 : -(((m + 1 : ℕ) : ℤ) - ((u + 1 : ℕ) : ℤ) + (u : ℕ) + 1) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e5 : -(((m + 1 : ℕ) : ℤ) - ((u + 1 : ℕ) : ℤ) + (u : ℕ)) = -((m : ℕ) : ℤ) := by push_cast; ring
    have e6 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
    simp only [zeroVal, e1, e2, e3, e4, e5, e6, zpow_neg, zpow_natCast]
    field_simp
    linear_combination (q * q ^ (m * 2)) * hc

end FqCount

open FqCount in
/-- **Kitaoka 1993, Lemma 5.6.9** (p. 120), proved: for a finite field with $q$ elements, a regular quadratic space $V$
of dimension $v$ and the totally isotropic space $U = F^u$ represented by $V$,
$q^{u(u+1)/2 - uv}r(U, V) = \prod_{i<u}(1 - q^{-(v-2u+2i+1)})$ for odd $v$ and
$\prod_{i<u}(1 - \chi(V)q^{-(v-2u+2i+2)/2})(1 + \chi(V)q^{-(v-2u+2i)/2})$ for even $v$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.9, p. 120"]
theorem lemma569 : Lemma569 := by
  intro K _ _ u v QV hQ hpos
  have hrad := QuadraticForm.radical_eq_bot_of_nondegenerate QV hQ
  have hqK : (Fintype.card K : ℝ) = Nat.card K := by rw [Nat.card_eq_fintype_card]
  have hq0 : (Nat.card K : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcount : (isoCountFq u QV : ℝ) = gRec (Nat.card K) u v (chiV QV) := by
    have := isoCount_eq u QV hrad
    rw [Module.finrank_fin_fun, ← chiV_eq_chiGen] at this
    exact this
  have h2u : 2 * u ≤ v := by
    have := two_mul_le_of_isoCount_pos u QV hrad hpos
    rwa [Module.finrank_fin_fun] at this
  simp only [hqK]
  rw [hcount]
  change (Nat.card K : ℝ) ^ expE u v * _ = _
  split_ifs with hv
  · have hchi : chiV QV = 0 := by simp [chiV, hv]
    rw [hchi, gRec_odd hq0 u v hv h2u]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_intCast]
    congr 2
    push_cast; ring
  · obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hv
    have hc : chiV QV ^ 2 = 1 := by
      simp only [chiV, if_neg hv]
      split_ifs <;> norm_num
    subst hk
    have hE := gRec_even hq0 hc u k (by omega)
    rw [show 2 * k = k + k by ring] at hE
    rw [hE]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    congr 4 <;> push_cast <;> ring

end QuadFormsKB.Kitaoka
