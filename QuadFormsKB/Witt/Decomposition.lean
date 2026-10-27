/-
# Witt decomposition and the Witt index

Let $K$ be any field (characteristic $2$ allowed).

**Definitions.**
* `QuadraticForm.hyperbolicPlane K`: the **hyperbolic plane** $\mathbb{H}$, the form
  $\mathbb{H}(x, y) = xy$ on $K^2$ (as `K × K`). Its polar form is
  $b((x, y), (x', y')) = xy' + x'y$, which is nondegenerate in every characteristic. (Mathlib's
  `QuadraticForm.dualProd K K` is the same form written on `Module.Dual K K × K`.)
* `QuadraticForm.hyperbolicSpace K m`: $\mathbb{H}^m = \mathbb{H} \perp \cdots \perp \mathbb{H}$
  ($m$ copies) on $(K^2)^m$ (`Fin m → K × K`), $\mathbb{H}^m(x) = \sum_{i < m} x_{i,1} x_{i,2}$.
* `QuadraticForm.wittIndex Q`: the **Witt index** $m$ of the decomposition below (defined as $0$
  when the quadratic radical of $Q$ is nonzero).

**Main results.** Let $V$ be finite-dimensional and assume the quadratic radical
`QuadraticMap.radical Q` $= \{v \in \operatorname{rad} b : Q(v) = 0\}$ is $0$ (in characteristic
$\neq 2$: $Q$ nondegenerate).
* `QuadraticForm.exists_wittDecomposition` (**Witt decomposition**; EKM Thm 8.5, Lam Ch. I
  §4, Scharlau Ch. 1 §5, O'Meara 42:10, p. 95, and the index $\mathrm{ind}\,V$, §42F, p. 99; Lam and Scharlau locators unverified):
  $Q \cong \mathbb{H}^m \perp Q_{\mathrm{an}}$ with $Q_{\mathrm{an}}$ anisotropic.
* `QuadraticForm.wittDecomposition_unique`: $m$ and the isometry class of $Q_{\mathrm{an}}$ are
  unique: $\mathbb{H}^m \perp Q_{\mathrm{an}} \cong \mathbb{H}^{m'} \perp Q'_{\mathrm{an}}$ with both
  anisotropic forces $m = m'$ and $Q_{\mathrm{an}} \cong Q'_{\mathrm{an}}$.
* `QuadraticForm.wittIndex_spec`, `QuadraticForm.eq_wittIndex`.

Note that in characteristic $2$ the anisotropic part contains the (anisotropic) quasilinear part
$Q|_{\operatorname{rad} b}$.

**Proof.** Existence: a nonzero isotropic $v$ is not in $\operatorname{rad} b$ (the quadratic
radical is $0$), so it has a hyperbolic partner $v'$, and $V = \langle v, v' \rangle \perp
\{v, v'\}^\perp$ explicitly (`QuadraticForm.Witt.exists_split_hyperbolicPlane`); induct on
$\dim V$. Uniqueness: cancel one $\mathbb{H}$ at a time (`QuadraticForm.equivalent_of_prod_equivalent_prod`);
$\mathbb{H}^{k+1} \perp Q'$ is never anisotropic.

Shimura's *core subspace* is the anisotropic part $Q_{\mathrm{an}}$.
-/
import QuadFormsKB.Witt.Cancellation

open Module QuadraticMap

universe u

namespace QuadraticForm

variable (K : Type*) [Field K]

/-! ### The hyperbolic plane and hyperbolic spaces -/

/-- **The hyperbolic plane** $\mathbb{H}(x, y) = xy$ on $K^2$ (`K × K`). -/
def hyperbolicPlane : QuadraticForm K (K × K) :=
  QuadraticMap.linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K)

@[simp] theorem hyperbolicPlane_apply (x : K × K) : hyperbolicPlane K x = x.1 * x.2 := rfl

theorem polar_hyperbolicPlane (x y : K × K) :
    polar (hyperbolicPlane K) x y = x.1 * y.2 + y.1 * x.2 := by
  simp only [polar, hyperbolicPlane_apply, Prod.fst_add, Prod.snd_add]; ring

/-- The hyperbolic plane is nonsingular (in every characteristic). -/
theorem nondegenerate_hyperbolicPlane : (polarBilin (hyperbolicPlane K)).Nondegenerate := by
  rw [nondegenerate_polarBilin_iff]
  intro x hx
  have h1 := hx (1, 0)
  have h2 := hx (0, 1)
  simp only [polar_hyperbolicPlane, mul_zero, one_mul, zero_add, mul_one, zero_mul,
    add_zero] at h1 h2
  exact Prod.ext h2 h1

/-- **The hyperbolic space** $\mathbb{H}^m$ on $(K^2)^m$:
$\mathbb{H}^m(x) = \sum_{i < m} x_{i,1}\, x_{i,2}$, the orthogonal sum of $m$ hyperbolic planes. -/
def hyperbolicSpace (m : ℕ) : QuadraticForm K (Fin m → K × K) :=
  QuadraticMap.pi fun _ => hyperbolicPlane K

theorem hyperbolicSpace_apply (m : ℕ) (x : Fin m → K × K) :
    hyperbolicSpace K m x = ∑ i, (x i).1 * (x i).2 := by
  simp [hyperbolicSpace, pi_apply]

/-- $\mathbb{H}^m$ is nonsingular. -/
theorem nondegenerate_hyperbolicSpace (m : ℕ) :
    (polarBilin (hyperbolicSpace K m)).Nondegenerate := by
  classical
  rw [nondegenerate_polarBilin_iff]
  intro x hx
  funext i
  refine (nondegenerate_polarBilin_iff _).mp (nondegenerate_hyperbolicPlane K) _ fun w => ?_
  have := hx (Pi.single i w)
  rw [hyperbolicSpace, QuadraticMap.Ring.polar_pi, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj; simp [hj]
  · simp

namespace Witt

variable {K}

/-- $\mathbb{H} \perp \mathbb{H}^m \cong \mathbb{H}^{m+1}$. -/
def hyperbolicSpaceSucc (m : ℕ) :
    ((hyperbolicPlane K).prod (hyperbolicSpace K m)).IsometryEquiv (hyperbolicSpace K (m + 1)) where
  toLinearEquiv := Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K × K)
  map_app' x := by
    simp [hyperbolicSpace_apply, Fin.sum_univ_succ]

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- Associativity of the orthogonal sum. -/
def prodAssoc (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) (Q₃ : QuadraticForm K V₃) :
    ((Q₁.prod Q₂).prod Q₃).IsometryEquiv (Q₁.prod (Q₂.prod Q₃)) where
  toLinearEquiv := LinearEquiv.prodAssoc K V₁ V₂ V₃
  map_app' x := by simp [add_assoc]

/-- $\mathbb{H}^0 \perp Q \cong Q$. -/
noncomputable def hyperbolicSpaceZeroProd (Q : QuadraticForm K V₁) :
    ((hyperbolicSpace K 0).prod Q).IsometryEquiv Q where
  toLinearEquiv := LinearEquiv.uniqueProd
  map_app' x := by simp [hyperbolicSpace_apply]

/-- Anisotropy pulls back along isometry equivalences. -/
theorem anisotropic_of_isometryEquiv {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (e : Q₁.IsometryEquiv Q₂) (h : Q₂.Anisotropic) : Q₁.Anisotropic := fun x hx => by
  have : e x = 0 := h _ (by rw [e.map_app, hx])
  exact e.injective (this.trans (map_zero e).symm)

/-- A zero quadratic radical pulls back along isometry equivalences. -/
theorem radical_eq_bot_of_isometryEquiv {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (e : Q₁.IsometryEquiv Q₂) (h : Q₂.radical = ⊥) : Q₁.radical = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot K).mpr ?_
  have hx' : e x ∈ Q₂.radical := by
    rw [← e.map_radical]; exact Submodule.mem_map_of_mem hx
  rw [h, Submodule.mem_bot] at hx'
  exact e.injective (hx'.trans (map_zero e).symm)

/-- $\mathbb{H}^{m+1} \perp Q$ is isotropic. -/
theorem not_anisotropic_hyperbolicSpace_succ_prod (m : ℕ) (Q : QuadraticForm K V₁) :
    ¬ ((hyperbolicSpace K (m + 1)).prod Q).Anisotropic := by
  classical
  intro h
  have := h (Pi.single 0 (1, 0), 0) (by
    simp only [prod_apply, hyperbolicSpace_apply, map_zero, add_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases eq_or_ne i 0 with rfl | hi <;> simp [*])
  have := congr($(congr($this.1)) 0)
  simp at this

variable {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- **Splitting off a hyperbolic plane.** If the quadratic radical of $Q$ is $0$ and $v \ne 0$
is isotropic, then $Q \cong \mathbb{H} \perp Q|_U$ for the proper subspace
$U = \{v, v'\}^\perp \subsetneq V$, where $v'$ is a hyperbolic partner of $v$. -/
theorem exists_split_hyperbolicPlane (hQ : Q.radical = ⊥) {v : V} (hv : Q v = 0) (hv0 : v ≠ 0) :
    ∃ U : Submodule K V, U ≠ ⊤ ∧
      Nonempty (((hyperbolicPlane K).prod (Q.comp U.subtype)).IsometryEquiv Q) := by
  have hvR : v ∉ LinearMap.ker (polarBilin Q) := fun h =>
    hv0 (by rw [← Submodule.mem_bot K, ← hQ]; exact ⟨hv, h⟩)
  rw [mem_ker_polarBilin] at hvR
  push Not at hvR
  obtain ⟨w, hw⟩ := hvR
  have hu : polar Q ((polar Q v w)⁻¹ • w) v = 1 := by
    rw [polar_smul_left, smul_eq_mul, polar_comm Q w v, inv_mul_cancel₀ hw]
  obtain ⟨hv', hvv'⟩ := hyperbolic_partner Q hv hu
  set v' := (polar Q v w)⁻¹ • w - Q ((polar Q v w)⁻¹ • w) • v
  have hvv : polar Q v v = 0 := by rw [polar_self_eq, hv, mul_zero]
  have hv'v' : polar Q v' v' = 0 := by rw [polar_self_eq, hv', mul_zero]
  have hv'v : polar Q v' v = 1 := by rw [polar_comm, hvv']
  set U := LinearMap.ker (polarBilin Q v) ⊓ LinearMap.ker (polarBilin Q v')
  have hmemU : ∀ u, u ∈ U ↔ polar Q v u = 0 ∧ polar Q v' u = 0 := fun u => by
    simp [U]
  refine ⟨U, fun h => ?_, ?_⟩
  · have := (hmemU v').mp (h ▸ Submodule.mem_top)
    rw [hvv'] at this
    exact one_ne_zero this.1
  let F : (K × K) × U →ₗ[K] V :=
    LinearMap.coprod ((LinearMap.fst K K K).smulRight v + (LinearMap.snd K K K).smulRight v')
      U.subtype
  have hF : ∀ x : (K × K) × U, F x = x.1.1 • v + x.1.2 • v' + x.2 := fun x => rfl
  have hFQ : ∀ x, Q (F x) = ((hyperbolicPlane K).prod (Q.comp U.subtype)) x := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    obtain ⟨hu1, hu2⟩ := (hmemU u).mp hu
    rw [hF, map_add_eq, map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, hv, hv',
      polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left, polar_smul_right, hu1,
      hu2, hvv']
    simp [smul_eq_mul]
  have hFv : ∀ x : (K × K) × U, polar Q (F x) v = x.1.2 := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    rw [hF, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hvv, hv'v,
      polar_comm, ((hmemU u).mp hu).1]
    simp
  have hFv' : ∀ x : (K × K) × U, polar Q (F x) v' = x.1.1 := by
    rintro ⟨⟨a, b⟩, u, hu⟩
    rw [hF, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hvv', hv'v',
      polar_comm, ((hmemU u).mp hu).2]
    simp
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨⟨a, b⟩, u⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hb : b = 0 := by
      have := hFv ⟨⟨a, b⟩, u⟩; rw [hx, polar_zero_left] at this; exact this.symm
    have ha : a = 0 := by
      have := hFv' ⟨⟨a, b⟩, u⟩; rw [hx, polar_zero_left] at this; exact this.symm
    have hu : (u : V) = 0 := by simpa [hF, ha, hb] using hx
    rw [Submodule.mem_bot]
    ext <;> simp [ha, hb, hu]
  have hsurj : Function.Surjective F := fun x => by
    set a := polar Q x v'
    set b := polar Q x v
    have hu : x - a • v - b • v' ∈ U := by
      rw [hmemU]
      constructor
      · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hvv, hvv',
          polar_comm Q v x]
        simp [b]
      · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hv'v, hv'v',
          polar_comm Q v' x]
        simp [a]
    exact ⟨⟨(a, b), ⟨_, hu⟩⟩, by rw [hF]; simp⟩
  exact ⟨{ LinearEquiv.ofBijective F ⟨hinj, hsurj⟩ with map_app' := fun x => hFQ x }⟩

end Witt

open _root_.QuadraticForm.Witt

variable {K}

/-- **Witt decomposition: existence** (every field, including characteristic $2$).

Let $V$ be a finite-dimensional vector space over a field $K$ and $Q$ a quadratic form on $V$
whose quadratic radical $\{v \in \operatorname{rad} b : Q(v) = 0\}$ is $0$ (in characteristic
$\neq 2$: $Q$ nondegenerate). Then for some $m \in \mathbb{N}$ and some anisotropic quadratic form
$Q_{\mathrm{an}}$ on a finite-dimensional space $U$,
$$Q \cong \mathbb{H}^m \perp Q_{\mathrm{an}}$$
(`Q.Equivalent ((hyperbolicSpace K m).prod Qa)`). Uniqueness: `wittDecomposition_unique`. -/
@[kb "ekm2008" "Thm 8.5; cassels1978 Ch. 2, Example 6, p. 29"]
theorem exists_wittDecomposition {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) :
    ∃ (m : ℕ) (U : Type u) (_ : AddCommGroup U) (_ : Module K U) (_ : FiniteDimensional K U)
      (Qa : QuadraticForm K U), Qa.Anisotropic ∧ Q.Equivalent ((hyperbolicSpace K m).prod Qa) := by
  obtain ⟨n, hn⟩ : ∃ n, finrank K V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    by_cases ha : Q.Anisotropic
    · exact ⟨0, V, inferInstance, inferInstance, inferInstance, Q, ha,
        ⟨(hyperbolicSpaceZeroProd Q).symm⟩⟩
    obtain ⟨v, hv, hv0⟩ : ∃ v, Q v = 0 ∧ v ≠ 0 := by
      simp only [Anisotropic, not_forall] at ha
      obtain ⟨v, hv, hv0⟩ := ha
      exact ⟨v, hv, hv0⟩
    obtain ⟨U, hU, ⟨e⟩⟩ := exists_split_hyperbolicPlane Q hQ hv hv0
    have hUrad : (Q.comp U.subtype).radical = ⊥ :=
      radical_eq_bot_of_prod_right (radical_eq_bot_of_isometryEquiv e hQ)
    obtain ⟨m, U', _, _, _, Qa, hQa, ⟨g⟩⟩ :=
      ih (finrank K U) (hn ▸ Submodule.finrank_lt hU) (Q.comp U.subtype) hUrad rfl
    exact ⟨m + 1, U', inferInstance, inferInstance, inferInstance, Qa, hQa,
      ⟨e.symm.trans (((QuadraticMap.IsometryEquiv.refl _).prod g).trans
        ((prodAssoc _ _ _).symm.trans ((hyperbolicSpaceSucc m).prod (QuadraticMap.IsometryEquiv.refl _))))⟩⟩

/-- **Witt decomposition: uniqueness** (every field, including characteristic $2$).

If $Q_{\mathrm{an}}$ on $U$ and $Q'_{\mathrm{an}}$ on $U'$ are anisotropic quadratic forms on
finite-dimensional spaces and $\mathbb{H}^m \perp Q_{\mathrm{an}} \cong \mathbb{H}^{m'} \perp
Q'_{\mathrm{an}}$, then $m = m'$ (the **Witt index**) and $Q_{\mathrm{an}} \cong Q'_{\mathrm{an}}$
(the **anisotropic part** is unique up to isometry). -/
@[kb "ekm2008" "Thm 8.5"]
theorem wittDecomposition_unique {U U' : Type*} [AddCommGroup U] [Module K U] [AddCommGroup U']
    [Module K U'] [FiniteDimensional K U] [FiniteDimensional K U'] {Qa : QuadraticForm K U}
    {Qa' : QuadraticForm K U'} (ha : Qa.Anisotropic) (ha' : Qa'.Anisotropic) :
    ∀ {m m' : ℕ}, ((hyperbolicSpace K m).prod Qa).Equivalent ((hyperbolicSpace K m').prod Qa') →
      m = m' ∧ Qa.Equivalent Qa'
  | 0, 0, ⟨e⟩ => ⟨rfl, ⟨(hyperbolicSpaceZeroProd Qa).symm.trans
      (e.trans (hyperbolicSpaceZeroProd Qa'))⟩⟩
  | 0, m' + 1, ⟨e⟩ => absurd (anisotropic_of_isometryEquiv e.symm
      (anisotropic_of_isometryEquiv (hyperbolicSpaceZeroProd Qa) ha))
      (not_anisotropic_hyperbolicSpace_succ_prod m' Qa')
  | m + 1, 0, ⟨e⟩ => absurd (anisotropic_of_isometryEquiv e
      (anisotropic_of_isometryEquiv (hyperbolicSpaceZeroProd Qa') ha'))
      (not_anisotropic_hyperbolicSpace_succ_prod m Qa)
  | m + 1, m' + 1, ⟨e⟩ => by
    have e' := (prodAssoc _ _ _).symm.trans (((hyperbolicSpaceSucc m).prod
      (QuadraticMap.IsometryEquiv.refl Qa)).trans (e.trans (((hyperbolicSpaceSucc m').symm.prod
      (QuadraticMap.IsometryEquiv.refl Qa')).trans (prodAssoc _ _ _))))
    have h := equivalent_of_prod_equivalent_prod (nondegenerate_hyperbolicPlane K)
      (radical_prod_eq_bot (nondegenerate_hyperbolicSpace K m)
        (radical_eq_bot_of_anisotropic ha)) ⟨e'⟩
    obtain ⟨hm, hQ⟩ := wittDecomposition_unique ha ha' h
    exact ⟨congrArg (· + 1) hm, hQ⟩

variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

open Classical in
/-- **The Witt index** of $Q$: the number $m$ of hyperbolic planes in a Witt decomposition
$Q \cong \mathbb{H}^m \perp Q_{\mathrm{an}}$ (`exists_wittDecomposition`); well defined by
`wittDecomposition_unique`. Defined as $0$ if the quadratic radical of $Q$ is nonzero (junk value;
the decomposition is not unique then). -/
noncomputable def wittIndex (Q : QuadraticForm K V) : ℕ :=
  if hQ : Q.radical = ⊥ then (exists_wittDecomposition Q hQ).choose else 0

/-- The Witt index is the number of hyperbolic planes in a Witt decomposition. -/
theorem wittIndex_spec (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) :
    ∃ (U : Type u) (_ : AddCommGroup U) (_ : Module K U) (_ : FiniteDimensional K U)
      (Qa : QuadraticForm K U), Qa.Anisotropic ∧
        Q.Equivalent ((hyperbolicSpace K (wittIndex Q)).prod Qa) := by
  have h : wittIndex Q = (exists_wittDecomposition Q hQ).choose := by simp [wittIndex, hQ]
  rw [h]
  exact (exists_wittDecomposition Q hQ).choose_spec

/-- **Characterization of the Witt index**: any decomposition $Q \cong \mathbb{H}^m \perp
Q_{\mathrm{an}}$ with $Q_{\mathrm{an}}$ anisotropic has $m$ equal to the Witt index. -/
@[kb "ekm2008" "Thm 8.5"]
theorem eq_wittIndex (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) {U : Type*} [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] {Qa : QuadraticForm K U} (ha : Qa.Anisotropic) {m : ℕ}
    (h : Q.Equivalent ((hyperbolicSpace K m).prod Qa)) : m = wittIndex Q := by
  obtain ⟨U', _, _, _, Qa', ha', h'⟩ := wittIndex_spec Q hQ
  exact (wittDecomposition_unique ha ha' (h.symm.trans h')).1

end QuadraticForm
