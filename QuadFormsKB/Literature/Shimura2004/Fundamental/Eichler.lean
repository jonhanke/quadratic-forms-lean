/-
# Shimura 2004, Theorem 10.5, local tools: Eichler transformations and the dual of a maximal lattice

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 10.5 (printed p. 96).
The tools are classical: Eichler's transformations (M. Eichler, *Quadratische Formen und orthogonale Gruppen*,
Springer 1952, §3) and the hyperbolic splitting of a maximal lattice (O'Meara 1963, 82:20, `Sec91MaxA.lean`).

**Setting.** $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, $(V, Q)$ a quadratic space over
$F$ with $B(x, y)$ = `bil Q x y` (so $B(x, x) = Q(x)$), lattices = `Submodule R V`, $\mathfrak o$ = the image of $R$
in $F$. For a lattice $K$, $x \in K^\sharp$ (`IsDual Q K x`) means $2B(x, K) \subseteq \mathfrak o$. An isometry
$\sigma$ of $V$ is **on** a subspace $W$ (`IsOn Q W σ`) if it fixes $W^\perp$ pointwise and maps $W$ into itself.

**Defines**
* `eichler Q he hu`: for $Q(e) = 0$ and $B(e, u) = 0$, the Eichler transformation
  $E_{e,u}(x) = x + 2B(x,e)\,u - \bigl(2B(x,u) + 2B(x,e)\,Q(u)\bigr)e$, an isometry of determinant $1$
  ($E_{e,u}E_{e,v} = E_{e,u+v}$).
* `HypSplit Q W L e f K`: $L = (\mathfrak oe + \mathfrak of) \perp K$ with $Q(e) = Q(f) = 0$, $2B(e, f) = 1$ and $K$
  $\mathfrak o$-maximal on $W \cap \{e, f\}^\perp$.

**Proves** (unconditional; standard axioms only)
* `exists_hypSplit`: a $\mathfrak o$-maximal lattice on an isotropic regular subspace has a `HypSplit`.
* `exists_isOn_sub_mem` (**the orbit lemma on $K^\sharp$**): for $K$ $\mathfrak o$-maximal on a regular subspace $W$ and
  $z, z' \in W \cap K^\sharp$ with $Q(z) - Q(z') \in \mathfrak o$, there is an isometry $\sigma$ on $W$ with
  $\sigma K = K$ and $\sigma z - z' \in K$. (Induction on the hyperbolic planes of $K$; on the anisotropic part,
  where $K = \{x : Q(x) \in \mathfrak o\}$ (91:1), $\sigma = 1$ if $Q(z - z') \in \mathfrak o$ and otherwise the
  symmetry $\tau_{z - z'}$, which sends $z$ to $z' - \tfrac{\varepsilon}{Q(z-z')}(z - z')$, $\varepsilon = Q(z) - Q(z')$.)
* `exists_isOn_det_neg`: for $K$ as above with $\dim W \ge 1$ and $z \in W \cap K^\sharp$ (with $2z \in K$ when
  $\dim W = 1$) there is an isometry $\rho$ on $W$ of determinant $-1$ with $\rho K = K$ and $\rho z - z \in K$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Max
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Citation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004.Local105

open QuadFormsKB.OMeara

section General

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$x \in K^\sharp$**: $2B(x, y) \in \mathfrak o$ for every $y \in K$. -/
def IsDual (K : Submodule R V) (x : V) : Prop := ∀ y ∈ K, 2 * bil Q x y ∈ (algebraMap R F).range

/-- **An isometry on $W$**: an isometry of $V$ fixing $W^\perp$ pointwise and mapping $W$ into itself. -/
def IsOn (W : Submodule F V) (σ : V ≃ₗ[F] V) : Prop :=
  σ ∈ orth Q ∧ (∀ v, (∀ w ∈ W, bil Q v w = 0) → σ v = v) ∧ ∀ w ∈ W, σ w ∈ W

variable {Q}

theorem half_add_half_aux : (1 / 2 : F) + 1 / 2 = 1 := by
  rw [← two_mul, mul_one_div, div_self (Invertible.ne_zero (2 : F))]

theorem bil_neg_right' (x y : V) : bil Q x (-y) = -bil Q x y := by simp [bil]

theorem smul_mem_of_int {L : Submodule R V} {c : F} (hc : c ∈ (algebraMap R F).range) {x : V} (hx : x ∈ L) :
    c • x ∈ L := by
  obtain ⟨r, rfl⟩ := hc
  rw [algebraMap_smul]
  exact L.smul_mem r hx

theorem Q_int {L : Submodule R V} (hn : normIdeal Q L ≤ 1) {x : V} (hx : x ∈ L) :
    Q x ∈ (algebraMap R F).range := by
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hn (Q_mem_normIdeal Q hx))
  exact ⟨r, hr⟩

theorem two_bil_int {L : Submodule R V} (hn : normIdeal Q L ≤ 1) {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    2 * bil Q x y ∈ (algebraMap R F).range := by
  have h : 2 * bil Q x y = Q (x + y) - Q x - Q y := by rw [Q_add]; ring
  rw [h]
  exact sub_mem (sub_mem (Q_int hn (L.add_mem hx hy)) (Q_int hn hx)) (Q_int hn hy)

theorem isDual_of_mem {L : Submodule R V} (hn : normIdeal Q L ≤ 1) {x : V} (hx : x ∈ L) : IsDual Q L x :=
  fun _ hy => two_bil_int hn hx hy

theorem bil_map_eq {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) (σ y) = bil Q x y := by
  have h1 := hσ (x + y)
  rw [map_add, Q_add, Q_add, hσ x, hσ y] at h1
  have h2 : (2 : F) * bil Q (σ x) (σ y) = 2 * bil Q x y := by linear_combination h1
  exact mul_left_cancel₀ (two_ne_zero (α := F)) h2

theorem bil_map_left_eq {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) y = bil Q x (σ.symm y) := by
  conv_lhs => rw [← σ.apply_symm_apply y]
  exact bil_map_eq hσ x _

theorem IsDual.map {L : Submodule R V} {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) {x : V} (hx : IsDual Q L x) :
    IsDual Q L (σ x) := by
  intro y hy
  rw [bil_map_left_eq hσ.1]
  refine hx _ ?_
  have hinv := (orthLat Q L).inv_mem hσ
  have : σ⁻¹ y ∈ OMeara.latMap σ⁻¹ L := ⟨y, hy, rfl⟩
  rw [hinv.2] at this
  exact this

theorem isOn_one (W : Submodule F V) : IsOn Q W 1 := ⟨(orth Q).one_mem, fun _ _ => rfl, fun _ hw => hw⟩

theorem IsOn.mul {W : Submodule F V} {σ τ : V ≃ₗ[F] V} (hσ : IsOn Q W σ) (hτ : IsOn Q W τ) :
    IsOn Q W (σ * τ) :=
  ⟨(orth Q).mul_mem hσ.1 hτ.1, fun v hv => by rw [LinearEquiv.mul_apply, hτ.2.1 v hv, hσ.2.1 v hv],
    fun w hw => by rw [LinearEquiv.mul_apply]; exact hσ.2.2 _ (hτ.2.2 w hw)⟩

theorem IsOn.map_eq [FiniteDimensional F V] {W : Submodule F V} {σ : V ≃ₗ[F] V} (hσ : IsOn Q W σ) :
    W.map (σ : V →ₗ[F] V) = W :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact hσ.2.2 v hv) (LinearEquiv.finrank_map_eq σ W)

theorem IsOn.symm_mem [FiniteDimensional F V] {W : Submodule F V} {σ : V ≃ₗ[F] V} (hσ : IsOn Q W σ) {w : V}
    (hw : w ∈ W) : σ.symm w ∈ W := by
  rw [← hσ.map_eq] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  simpa using hv

theorem symmetry_apply_of_bil {u : V} (hu : Q u ≠ 0) {x : V} (hx : bil Q x u = 0) : symmetry Q u hu x = x := by
  rw [symmetry_apply, hx, mul_zero, zero_div, zero_smul, sub_zero]

theorem isOn_symmetry {W : Submodule F V} {u : V} (huW : u ∈ W) (hu : Q u ≠ 0) : IsOn Q W (symmetry Q u hu) :=
  ⟨symmetry_mem_orth Q hu, fun _ hv => symmetry_apply_of_bil hu (hv u huW),
    fun w hw => by rw [symmetry_apply]; exact W.sub_mem hw (W.smul_mem _ huW)⟩

/-- A symmetry $\tau_u$ with $u \in L$ and $Q(u)^{-1} \in \mathfrak o$ is a unit of a lattice with
$\mathfrak nL \subseteq \mathfrak o$. -/
theorem symmetry_mem_orthLat_of_inv {L : Submodule R V} (hn : normIdeal Q L ≤ 1) {u : V} (huL : u ∈ L)
    (hu : Q u ≠ 0) (hinv : (Q u)⁻¹ ∈ (algebraMap R F).range) : symmetry Q u hu ∈ orthLat Q L :=
  symmetry_mem_orthLat_of_le Q hu fun x hx => by
    rw [symmetry_apply]
    refine L.sub_mem hx (smul_mem_of_int ?_ huL)
    rw [div_eq_mul_inv]
    exact mul_mem (two_bil_int hn hx huL) hinv

/-- A map that sends $L$ into $L$, together with its inverse, preserves $L$. -/
theorem latMap_eq_of_le {L : Submodule R V} {σ : V ≃ₗ[F] V} (h1 : ∀ x ∈ L, σ x ∈ L)
    (h2 : ∀ x ∈ L, σ.symm x ∈ L) : OMeara.latMap σ L = L := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact h1 x hx
  · intro x hx
    exact ⟨σ.symm x, h2 x hx, σ.apply_symm_apply x⟩

/-! ### Eichler transformations -/

variable (Q) in
/-- The linear map underlying the Eichler transformation $E_{e,u}$. -/
def eichlerLin (e u : V) : V →ₗ[F] V :=
  LinearMap.id + ((2 : F) • (QuadraticMap.associated Q).flip e).smulRight u -
    ((2 : F) • (QuadraticMap.associated Q).flip u + (2 * Q u) • (QuadraticMap.associated Q).flip e).smulRight e

variable (Q) in
theorem eichlerLin_apply (e u x : V) :
    eichlerLin Q e u x = x + (2 * bil Q x e) • u - (2 * bil Q x u + 2 * bil Q x e * Q u) • e := by
  simp only [eichlerLin, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, bil]
  congr 2
  ring

theorem eichlerLin_comp {e u u' : V} (he : Q e = 0) (hu : bil Q e u = 0) (hu' : bil Q e u' = 0) (x : V) :
    eichlerLin Q e u (eichlerLin Q e u' x) = eichlerLin Q e (u + u') x := by
  have hue : bil Q u e = 0 := by rw [bil_comm]; exact hu
  have hue' : bil Q u' e = 0 := by rw [bil_comm]; exact hu'
  have hee : bil Q e e = 0 := by rw [bil_self]; exact he
  rw [eichlerLin_apply, eichlerLin_apply, eichlerLin_apply]
  simp only [bil_add_left, bil_sub_left, bil_smul_left, bil_add_right, bil_sub_right, bil_smul_right, hu, hu',
    hue, hue', hee, Q_add]
  rw [bil_comm Q u' u]
  module

theorem eichlerLin_zero (e x : V) : eichlerLin Q e 0 x = x := by
  rw [eichlerLin_apply]; simp [bil]

theorem Q_eichlerLin {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) (x : V) : Q (eichlerLin Q e u x) = Q x := by
  have hue : bil Q u e = 0 := by rw [bil_comm]; exact hu
  rw [eichlerLin_apply, sub_eq_add_neg, add_assoc, Q_add, Q_add]
  simp only [← neg_smul, bil_add_right, bil_smul_right, QuadraticMap.map_smul, he, hue, bil_smul_left, smul_eq_mul]
  ring

/-- **The Eichler transformation** $E_{e,u}$ (for $Q(e) = 0$, $B(e, u) = 0$) as a linear automorphism; its
inverse is $E_{e,-u}$. -/
def eichler {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinear (eichlerLin Q e u) (eichlerLin Q e (-u))
    (by
      ext x
      have hnu : bil Q e (-u) = 0 := by rw [bil_neg_right', hu, neg_zero]
      rw [LinearMap.comp_apply, eichlerLin_comp he hu hnu, add_neg_cancel, eichlerLin_zero]
      rfl)
    (by
      ext x
      have hnu : bil Q e (-u) = 0 := by rw [bil_neg_right', hu, neg_zero]
      rw [LinearMap.comp_apply, eichlerLin_comp he hnu hu, neg_add_cancel, eichlerLin_zero]
      rfl)

theorem eichler_apply {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) (x : V) :
    eichler he hu x = x + (2 * bil Q x e) • u - (2 * bil Q x u + 2 * bil Q x e * Q u) • e :=
  eichlerLin_apply Q e u x

theorem eichler_mem_orth {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) : eichler he hu ∈ orth Q :=
  fun x => Q_eichlerLin he hu x

theorem eichler_symm_apply {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) (x : V) :
    (eichler he hu).symm x = eichlerLin Q e (-u) x := rfl

/-- **$E_{e,u}$ has determinant $1$**: $E_{e,u} = E_{e,u/2}^2$ and the determinant of an isometry is $\pm 1$. -/
theorem det_eichler [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate) {e u : V}
    (he : Q e = 0) (hu : bil Q e u = 0) : LinearEquiv.det (eichler he hu) = 1 := by
  have hu2 : bil Q e ((1 / 2 : F) • u) = 0 := by rw [bil_smul_right, hu, mul_zero]
  have hsq : eichler he hu = eichler he hu2 * eichler he hu2 := by
    ext x
    rw [LinearEquiv.mul_apply, eichler_apply, eichler_apply, eichler_apply]
    rw [← eichler_apply he hu2, ← eichler_apply he hu2]
    change _ = eichlerLin Q e _ (eichlerLin Q e _ x)
    rw [eichlerLin_comp he hu2 hu2, ← add_smul, half_add_half_aux, one_smul,
      eichlerLin_apply]
  rw [hsq, map_mul]
  rcases det_orth_eq Q hV (eichler_mem_orth he hu2) with h | h <;> rw [h] <;> norm_num

theorem eichler_mem_orthLat {L : Submodule R V} (hn : normIdeal Q L ≤ 1) {e u : V} (he : Q e = 0)
    (hu : bil Q e u = 0) (heL : e ∈ L) (huL : u ∈ L) : eichler he hu ∈ orthLat Q L := by
  have key : ∀ w : V, w ∈ L → ∀ x ∈ L, eichlerLin Q e w x ∈ L := by
    intro w hw x hx
    rw [eichlerLin_apply]
    refine L.sub_mem (L.add_mem hx (smul_mem_of_int (two_bil_int hn hx heL) hw)) (smul_mem_of_int ?_ heL)
    exact add_mem (two_bil_int hn hx hw) (mul_mem (two_bil_int hn hx heL) (Q_int hn hw))
  exact ⟨eichler_mem_orth he hu, latMap_eq_of_le (key u huL) (key (-u) (L.neg_mem huL))⟩

theorem isOn_eichler {W : Submodule F V} {e u : V} (he : Q e = 0) (hu : bil Q e u = 0) (heW : e ∈ W)
    (huW : u ∈ W) : IsOn Q W (eichler he hu) := by
  refine ⟨eichler_mem_orth he hu, fun v hv => ?_, fun w hw => ?_⟩
  · rw [eichler_apply, hv e heW, hv u huW]; simp
  · rw [eichler_apply]
    exact W.sub_mem (W.add_mem hw (W.smul_mem _ huW)) (W.smul_mem _ heW)

end General

/-! ### Hyperbolic splittings -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {Q : QuadraticForm F V}

/-- **A normalized hyperbolic splitting** $L = (\mathfrak oe + \mathfrak of) \perp K$ of a lattice $L$ on $W$:
$Q(e) = Q(f) = 0$, $2B(e, f) = 1$, and $K$ is $\mathfrak o$-maximal on $W \cap \{e, f\}^\perp$. -/
structure HypSplit (W : Submodule F V) (L : Submodule R V) (e f : V) (K : Submodule R V) : Prop where
  he : e ∈ L
  hf : f ∈ L
  Qe : Q e = 0
  Qf : Q f = 0
  bef : 2 * bil Q e f = 1
  split : IsOrthSum Q L (span R {e, f}) K
  hK : IsMaxIn Q 1 (perpIn Q W (span R {e, f})) K

theorem mem_perpIn_pair {W : Submodule F V} {e f v : V} :
    v ∈ perpIn Q W (span R {e, f}) ↔ v ∈ W ∧ bil Q v e = 0 ∧ bil Q v f = 0 := by
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, h e (subset_span (by simp)), h f (subset_span (by simp))⟩
  · rintro ⟨hv, he, hf⟩
    refine ⟨hv, fun j hj => ?_⟩
    obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hj
    rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, he, hf]; ring

namespace HypSplit

variable {W : Submodule F V} {L : Submodule R V} {e f : V} {K : Submodule R V}

theorem bfe (h : HypSplit (Q := Q) W L e f K) : 2 * bil Q f e = 1 := by rw [bil_comm]; exact h.bef

theorem K_le (h : HypSplit (Q := Q) W L e f K) : K ≤ L := h.split.sup_eq ▸ le_sup_right

theorem bil_e_of_mem (h : HypSplit (Q := Q) W L e f K) {y : V} (hy : y ∈ K) : bil Q y e = 0 := by
  rw [bil_comm]; exact h.split.orth e (subset_span (by simp)) y hy

theorem bil_f_of_mem (h : HypSplit (Q := Q) W L e f K) {y : V} (hy : y ∈ K) : bil Q y f = 0 := by
  rw [bil_comm]; exact h.split.orth f (subset_span (by simp)) y hy

theorem mem_perp_of_mem (h : HypSplit (Q := Q) W L e f K) {y : V} (hy : y ∈ K) :
    y ∈ perpIn Q W (span R {e, f}) := by
  have := h.hK.2.1
  rw [← this]; exact subset_span hy

/-- The decomposition $x = 2B(x,f)\,e + 2B(x,e)\,f + z$ with $z \perp e, f$. -/
theorem sub_mem_perp (h : HypSplit (Q := Q) W L e f K) (heW : e ∈ W) (hfW : f ∈ W) {x : V} (hx : x ∈ W) :
    x - (2 * bil Q x f) • e - (2 * bil Q x e) • f ∈ perpIn Q W (span R {e, f}) := by
  have hee : bil Q e e = 0 := by rw [bil_self]; exact h.Qe
  have hff : bil Q f f = 0 := by rw [bil_self]; exact h.Qf
  have h1 := h.bef
  have h2 := h.bfe
  rw [mem_perp_iff_aux]
  refine ⟨W.sub_mem (W.sub_mem hx (W.smul_mem _ heW)) (W.smul_mem _ hfW), ?_, ?_⟩
  · simp only [bil_sub_left, bil_smul_left, hee]
    linear_combination (-(bil Q x e)) * h2
  · simp only [bil_sub_left, bil_smul_left, hff]
    linear_combination (-(bil Q x f)) * h1
where
  mem_perp_iff_aux {v : V} : v ∈ perpIn Q W (span R {e, f}) ↔ v ∈ W ∧ bil Q v e = 0 ∧ bil Q v f = 0 :=
    mem_perpIn_pair

/-- $Q(\alpha e + \beta f + z) = \alpha\beta + Q(z)$ for $z \perp e, f$. -/
theorem Q_comb' (h : HypSplit (Q := Q) W L e f K) {z : V} (hze : bil Q z e = 0) (hzf : bil Q z f = 0) (α β : F) :
    Q (α • e + β • f + z) = α * β + Q z := by
  have hze' : bil Q e z = 0 := by rw [bil_comm]; exact hze
  have hzf' : bil Q f z = 0 := by rw [bil_comm]; exact hzf
  rw [Q_add, Q_add, Q_smul, Q_smul, h.Qe, h.Qf, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left,
    bil_smul_right, hze', hzf']
  linear_combination α * β * h.bef

theorem Q_comb'' (h : HypSplit (Q := Q) W L e f K) {z : V} (hze : bil Q z e = 0) (hzf : bil Q z f = 0) (α : F) :
    Q (α • e + f + z) = α + Q z := by
  have := h.Q_comb' hze hzf α 1
  rwa [one_smul, mul_one] at this

theorem Q_ef (h : HypSplit (Q := Q) W L e f K) (α : F) : Q (α • e + f) = α := by
  have := h.Q_comb'' (z := 0) (by simp [bil]) (by simp [bil]) α
  rwa [add_zero, QuadraticMap.map_zero, add_zero] at this

end HypSplit

/-- **A normalized hyperbolic splitting exists** (O'Meara 1963, 82:20) for a lattice that is $\mathfrak o$-maximal on
a regular isotropic subspace $W$. -/
theorem exists_hypSplit {W : Submodule F V} (hWreg : ∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0)
    {L : Submodule R V} (hL : IsMaxIn Q 1 W L) {w : V} (hwW : w ∈ W) (hw0 : w ≠ 0) (hQw : Q w = 0) :
    ∃ e f : V, ∃ K : Submodule R V, HypSplit (Q := Q) W L e f K := by
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span (R := R) (hL.2.1.symm ▸ hwW : w ∈ span F (L : Set V))
  obtain ⟨x₀, hx₀, y, hy, γ, hγ, haγ, hQx₀, hQy, hxy, hsL⟩ :=
    exists_hyperbolic_split_of_isMaxIn Q hWreg hL hdw (smul_ne_zero hd hw0) (by rw [Q_rsmul, hQw, mul_zero])
  -- `2γ` is a unit of `𝔬`
  have h1 : (1 : F) ∈ R ∙ (2 * γ) := haγ ▸ Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨r, hr⟩ := mem_span_singleton.mp h1
  have h2 : 2 * γ ∈ (1 : Submodule R F) := haγ ▸ mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_one.mp h2
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R F
    rw [map_mul, hs, map_one, ← hr, Algebra.smul_def]
  have hJ : span R {x₀, r • y} = span R {x₀, y} := by
    apply le_antisymm <;> rw [span_le] <;> intro v hv <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv <;> rcases hv with h | h <;> rw [h]
    · exact subset_span (by simp)
    · exact smul_mem _ _ (subset_span (by simp))
    · exact subset_span (by simp)
    · have : y = s • r • y := by rw [smul_smul, mul_comm, hrs, one_smul]
      have hmem : s • r • y ∈ span R {x₀, r • y} := smul_mem _ _ (subset_span (by simp))
      rwa [← this] at hmem
  have hbef : 2 * bil Q x₀ (r • y) = 1 := by
    rw [bil_rsmul_right, hxy, ← hr, Algebra.smul_def]; ring
  have hγ' : bil Q x₀ (r • y) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hbef; exact zero_ne_one hbef
  refine ⟨x₀, r • y, splitComp Q L (span R {x₀, y}), ⟨hx₀, L.smul_mem r hy, hQx₀,
    by rw [Q_rsmul, hQy, mul_zero], hbef, hJ ▸ hsL, ?_⟩⟩
  rw [hJ]
  have hreg : IsRegular Q (span R {x₀, y}) := isRegular_hyp Q hγ hQx₀ hQy hxy
  exact hL.complement Q hsL hreg

/-! ### The orbit lemma on $K^\sharp$ and the determinant lemma -/

theorem int_or_inv_int (c : F) : c ∈ (algebraMap R F).range ∨ c⁻¹ ∈ (algebraMap R F).range := by
  rcases ValuationRing.isInteger_or_isInteger R c with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨r, hr⟩
  · exact Or.inr ⟨r, hr⟩

variable [HenselianLocalRing R]

theorem mem_iff_int {W : Submodule F V} (hW : ∀ w ∈ W, Q w = 0 → w = 0) {K : Submodule R V}
    (hK : IsMaxIn Q 1 W K) {x : V} (hx : x ∈ W) : x ∈ K ↔ Q x ∈ (algebraMap R F).range := by
  rw [mem_iff_of_isMaxIn Q hW hK hx, Submodule.mem_one]; rfl

/-- On an anisotropic subspace an isometry on $W$ preserves the maximal lattice (91:1). -/
theorem latMap_eq_of_aniso [FiniteDimensional F V] {W : Submodule F V} (hW : ∀ w ∈ W, Q w = 0 → w = 0) {K : Submodule R V}
    (hK : IsMaxIn Q 1 W K) {σ : V ≃ₗ[F] V} (hσ : IsOn Q W σ) : OMeara.latMap σ K = K := by
  have hKW : ∀ x ∈ K, x ∈ W := fun x hx => hK.2.1 ▸ subset_span hx
  have hσinv : ∀ w ∈ W, σ.symm w ∈ W := fun w hw => hσ.symm_mem hw
  apply latMap_eq_of_le
  · intro x hx
    have hxW := hKW x hx
    rw [mem_iff_int hW hK (hσ.2.2 x hxW), hσ.1 x]
    exact (mem_iff_int hW hK hxW).mp hx
  · intro x hx
    have hxW := hKW x hx
    rw [mem_iff_int hW hK (hσinv x hxW)]
    have : Q (σ.symm x) = Q x := by
      conv_rhs => rw [← σ.apply_symm_apply x]
      exact (hσ.1 _).symm
    rw [this]
    exact (mem_iff_int hW hK hxW).mp hx

namespace HypSplit

variable {W : Submodule F V} {L : Submodule R V} {e f : V} {K : Submodule R V}

theorem e_mem_W (h : HypSplit (Q := Q) W L e f K) (hL : IsMaxIn Q 1 W L) : e ∈ W := hL.2.1 ▸ subset_span h.he

theorem f_mem_W (h : HypSplit (Q := Q) W L e f K) (hL : IsMaxIn Q 1 W L) : f ∈ W := hL.2.1 ▸ subset_span h.hf

/-- $W \cap \{e, f\}^\perp$ is regular when $W$ is. -/
theorem perp_reg (h : HypSplit (Q := Q) W L e f K) (heW : e ∈ W) (hfW : f ∈ W)
    (hWreg : ∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) :
    ∀ v ∈ perpIn Q W (span R {e, f}), (∀ v' ∈ perpIn Q W (span R {e, f}), bil Q v v' = 0) → v = 0 := by
  intro v hv hv0
  obtain ⟨hvW, hve, hvf⟩ := mem_perpIn_pair.mp hv
  refine hWreg v hvW fun x hx => ?_
  have hx' := h.sub_mem_perp heW hfW hx
  have : x = (2 * bil Q x f) • e + (2 * bil Q x e) • f +
      (x - (2 * bil Q x f) • e - (2 * bil Q x e) • f) := by abel
  rw [this, bil_add_right, bil_add_right, bil_smul_right, bil_smul_right, hve, hvf, hv0 _ hx']
  ring

theorem finrank_perp_lt [FiniteDimensional F V] (h : HypSplit (Q := Q) W L e f K) (heW : e ∈ W) :
    finrank F (perpIn Q W (span R {e, f})) < finrank F W := by
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (fun v hv => hv.1) fun hc => ?_)
  have he' : e ∈ perpIn Q W (span R {e, f}) := by rw [hc]; exact heW
  have := (mem_perpIn_pair.mp he').2.2
  have h1 := h.bef
  rw [this, mul_zero] at h1
  exact zero_ne_one h1

/-- An isometry on $W \cap \{e, f\}^\perp$ fixes $e$ and $f$. -/
theorem fix_e (_h : HypSplit (Q := Q) W L e f K) {σ : V ≃ₗ[F] V}
    (hσ : IsOn Q (perpIn Q W (span R {e, f})) σ) : σ e = e :=
  hσ.2.1 e fun w hw => by rw [bil_comm]; exact (mem_perpIn_pair.mp hw).2.1

theorem fix_f (_h : HypSplit (Q := Q) W L e f K) {σ : V ≃ₗ[F] V}
    (hσ : IsOn Q (perpIn Q W (span R {e, f})) σ) : σ f = f :=
  hσ.2.1 f fun w hw => by rw [bil_comm]; exact (mem_perpIn_pair.mp hw).2.2

/-- An isometry on $W \cap \{e, f\}^\perp$ is an isometry on $W$. -/
theorem isOn_lift (h : HypSplit (Q := Q) W L e f K) (heW : e ∈ W) (hfW : f ∈ W) {σ : V ≃ₗ[F] V}
    (hσ : IsOn Q (perpIn Q W (span R {e, f})) σ) : IsOn Q W σ := by
  refine ⟨hσ.1, fun v hv => hσ.2.1 v fun w hw => hv w hw.1, fun x hx => ?_⟩
  have hx' := h.sub_mem_perp heW hfW hx
  have : x = (2 * bil Q x f) • e + (2 * bil Q x e) • f +
      (x - (2 * bil Q x f) • e - (2 * bil Q x e) • f) := by abel
  rw [this, map_add, map_add, map_smul, map_smul, h.fix_e hσ, h.fix_f hσ]
  exact W.add_mem (W.add_mem (W.smul_mem _ heW) (W.smul_mem _ hfW)) (hσ.2.2 _ hx').1

/-- An isometry on $W \cap \{e, f\}^\perp$ preserving $K$ preserves $L = (\mathfrak oe + \mathfrak of) \perp K$. -/
theorem latMap_eq (h : HypSplit (Q := Q) W L e f K) {σ : V ≃ₗ[F] V}
    (hσ : IsOn Q (perpIn Q W (span R {e, f})) σ) (hσK : OMeara.latMap σ K = K) : OMeara.latMap σ L = L := by
  conv_lhs => rw [← h.split.sup_eq]
  rw [OMeara.latMap, Submodule.map_sup]
  change OMeara.latMap σ _ ⊔ OMeara.latMap σ K = L
  rw [latMap_span_pair, h.fix_e hσ, h.fix_f hσ, hσK, h.split.sup_eq]

theorem orthLat_of_isOn (h : HypSplit (Q := Q) W L e f K) {σ : V ≃ₗ[F] V}
    (hσ : IsOn Q (perpIn Q W (span R {e, f})) σ) (hσK : OMeara.latMap σ K = K) : σ ∈ orthLat Q L :=
  ⟨hσ.1, h.latMap_eq hσ hσK⟩

/-- The component $z \perp e, f$ of a vector of $L^\sharp$ is in $K^\sharp$. -/
theorem isDual_comp (h : HypSplit (Q := Q) W L e f K) {x : V} (hx : IsDual Q L x) :
    IsDual Q K (x - (2 * bil Q x f) • e - (2 * bil Q x e) • f) := by
  intro y hy
  rw [bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, bil_comm Q e y, bil_comm Q f y,
    h.bil_e_of_mem hy, h.bil_f_of_mem hy, mul_zero, mul_zero, sub_zero, sub_zero]
  exact hx y (h.K_le hy)

end HypSplit

/-- **The orbit lemma on $K^\sharp$**: for $K$ $\mathfrak o$-maximal on a regular subspace $W$ and $z, z' \in W$
with $2B(z, K), 2B(z', K) \subseteq \mathfrak o$ and $Q(z) - Q(z') \in \mathfrak o$, some isometry $\sigma$ on $W$
with $\sigma K = K$ has $\sigma z - z' \in K$. -/
theorem exists_isOn_sub_mem [FiniteDimensional F V] (n : ℕ) :
    ∀ W : Submodule F V, finrank F W = n → (∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) →
    ∀ K : Submodule R V, IsMaxIn Q 1 W K → ∀ z z' : V, z ∈ W → z' ∈ W → IsDual Q K z → IsDual Q K z' →
      Q z - Q z' ∈ (algebraMap R F).range →
      ∃ σ : V ≃ₗ[F] V, IsOn Q W σ ∧ OMeara.latMap σ K = K ∧ σ z - z' ∈ K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWreg K hK z z' hz hz' hzd hzd' hQ
  by_cases hiso : ∀ w ∈ W, Q w = 0 → w = 0
  · by_cases hd : Q (z - z') ∈ (algebraMap R F).range
    · refine ⟨1, isOn_one W, latMap_one K, ?_⟩
      exact (mem_iff_int hiso hK (W.sub_mem hz hz')).mpr hd
    · have hd0 : Q (z - z') ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
      have hinv : (Q (z - z'))⁻¹ ∈ (algebraMap R F).range := (int_or_inv_int _).resolve_left hd
      have hσ : IsOn Q W (symmetry Q (z - z') hd0) := isOn_symmetry (W.sub_mem hz hz') hd0
      refine ⟨symmetry Q (z - z') hd0, hσ, latMap_eq_of_aniso hiso hK hσ, ?_⟩
      have hQd : Q (z - z') = Q z - 2 * bil Q z z' + Q z' := by
        rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg]; ring
      have hb : bil Q z (z - z') = Q z - bil Q z z' := by rw [bil_sub_right, bil_self]
      have hkey : symmetry Q (z - z') hd0 z - z' =
          (-((Q z - Q z') * (Q (z - z'))⁻¹)) • (z - z') := by
        rw [symmetry_apply]
        have hc : 2 * bil Q z (z - z') / Q (z - z') = 1 + (Q z - Q z') * (Q (z - z'))⁻¹ := by
          rw [hb]; field_simp; rw [hQd]; ring
        rw [hc]
        module
      rw [hkey, mem_iff_int hiso hK (W.smul_mem _ (W.sub_mem hz hz')), Q_smul]
      have : (-((Q z - Q z') * (Q (z - z'))⁻¹)) ^ 2 * Q (z - z') =
          (Q z - Q z') * (Q z - Q z') * (Q (z - z'))⁻¹ := by field_simp
      rw [this]
      exact mul_mem (mul_mem hQ hQ) hinv
  · push Not at hiso
    obtain ⟨w, hwW, hQw, hw0⟩ := hiso
    obtain ⟨e, f, K', hs⟩ := exists_hypSplit hWreg hK hwW hw0 hQw
    have heW := hs.e_mem_W hK
    have hfW := hs.f_mem_W hK
    have hW'reg := hs.perp_reg heW hfW hWreg
    have hlt : finrank F (perpIn Q W (span R {e, f})) < n := hn ▸ hs.finrank_perp_lt heW
    have hz₂ := hs.sub_mem_perp heW hfW hz
    have hz₂' := hs.sub_mem_perp heW hfW hz'
    have hzd₂ := hs.isDual_comp hzd
    have hzd₂' := hs.isDual_comp hzd'
    have hα := hzd f hs.hf
    have hβ := hzd e hs.he
    have hα' := hzd' f hs.hf
    have hβ' := hzd' e hs.he
    set z₂ := z - (2 * bil Q z f) • e - (2 * bil Q z e) • f with hz₂def
    set z₂' := z' - (2 * bil Q z' f) • e - (2 * bil Q z' e) • f with hz₂def'
    have hzeq : z = (2 * bil Q z f) • e + (2 * bil Q z e) • f + z₂ := by rw [hz₂def]; abel
    have hzeq' : z' = (2 * bil Q z' f) • e + (2 * bil Q z' e) • f + z₂' := by rw [hz₂def']; abel
    have hQz : Q z = (2 * bil Q z f) * (2 * bil Q z e) + Q z₂ := by
      conv_lhs => rw [hzeq]
      exact hs.Q_comb' (mem_perpIn_pair.mp hz₂).2.1 (mem_perpIn_pair.mp hz₂).2.2 _ _
    have hQz' : Q z' = (2 * bil Q z' f) * (2 * bil Q z' e) + Q z₂' := by
      conv_lhs => rw [hzeq']
      exact hs.Q_comb' (mem_perpIn_pair.mp hz₂').2.1 (mem_perpIn_pair.mp hz₂').2.2 _ _
    have hQ₂ : Q z₂ - Q z₂' ∈ (algebraMap R F).range := by
      have : Q z₂ - Q z₂' = (Q z - Q z') - ((2 * bil Q z f) * (2 * bil Q z e) -
          (2 * bil Q z' f) * (2 * bil Q z' e)) := by rw [hQz, hQz']; ring
      rw [this]
      exact sub_mem hQ (sub_mem (mul_mem hα hβ) (mul_mem hα' hβ'))
    obtain ⟨σ, hσ, hσK, hσz⟩ := ih _ hlt _ rfl hW'reg K' hs.hK z₂ z₂' hz₂ hz₂' hzd₂ hzd₂' hQ₂
    refine ⟨σ, hs.isOn_lift heW hfW hσ, hs.latMap_eq hσ hσK, ?_⟩
    have : σ z - z' = (2 * bil Q z f - 2 * bil Q z' f) • e + (2 * bil Q z e - 2 * bil Q z' e) • f +
        (σ z₂ - z₂') := by
      conv_lhs => rw [hzeq, hzeq']
      rw [map_add, map_add, map_smul, map_smul, hs.fix_e hσ, hs.fix_f hσ]
      module
    rw [this]
    exact K.add_mem (K.add_mem (smul_mem_of_int (sub_mem hα hα') hs.he)
      (smul_mem_of_int (sub_mem hβ hβ') hs.hf)) (hs.K_le hσz)

/-- A non-zero vector orthogonal to a given vector, in a subspace of dimension $\ge 2$. -/
theorem exists_ne_zero_bil_eq_zero [FiniteDimensional F V] {W : Submodule F V} (hW : 2 ≤ finrank F W) (z : V) :
    ∃ w ∈ W, w ≠ 0 ∧ bil Q z w = 0 := by
  let g : W →ₗ[F] F := (QuadraticMap.associated Q z).comp W.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : finrank F (LinearMap.range g) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range g)
    rwa [Module.finrank_self] at this
  have h3 : 0 < finrank F (LinearMap.ker g) := by omega
  obtain ⟨⟨⟨w, hwW⟩, hwk⟩, hw0⟩ := finrank_pos_iff_exists_ne_zero.mp h3
  refine ⟨w, hwW, fun h => hw0 (by ext; simp [h]), ?_⟩
  exact hwk

/-- **The determinant lemma**: for $K$ $\mathfrak o$-maximal on a regular subspace $W$ of dimension $\ge 1$ and
$z \in W \cap K^\sharp$ (with $2z \in K$ if $\dim W = 1$), some isometry $\rho$ on $W$ of determinant $-1$ with
$\rho K = K$ has $\rho z - z \in K$. -/
theorem exists_isOn_det_neg [FiniteDimensional F V] {W : Submodule F V}
    (hWreg : ∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) (hW1 : 1 ≤ finrank F W) {K : Submodule R V}
    (hK : IsMaxIn Q 1 W K) {z : V} (hz : z ∈ W) (hzd : IsDual Q K z) (h1 : finrank F W = 1 → (2 : F) • z ∈ K) :
    ∃ ρ : V ≃ₗ[F] V, IsOn Q W ρ ∧ OMeara.latMap ρ K = K ∧ LinearEquiv.det ρ = -1 ∧ ρ z - z ∈ K := by
  by_cases hiso : ∀ w ∈ W, Q w = 0 → w = 0
  · rcases Nat.lt_or_ge (finrank F W) 2 with hlt | hge
    · -- a line: `ρ = -1` on `W`
      have hW1' : finrank F W = 1 := by omega
      obtain ⟨⟨w, hwW⟩, hw0⟩ := finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank F W)
      have hw0' : w ≠ 0 := fun h => hw0 (by ext; simp [h])
      have hQw : Q w ≠ 0 := fun h => hw0' (hiso w hwW h)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W) hw0).mp hW1' ⟨z, hz⟩
      have hzc : z = c • w := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      refine ⟨symmetry Q w hQw, isOn_symmetry hwW hQw, latMap_eq_of_aniso hiso hK (isOn_symmetry hwW hQw),
        det_symmetry Q hQw, ?_⟩
      have : symmetry Q w hQw z - z = -((2 : F) • z) := by
        rw [symmetry_apply, hzc, bil_smul_left, bil_self]
        field_simp
        module
      rw [this]
      exact K.neg_mem (h1 hW1')
    · obtain ⟨w, hwW, hw0, hzw⟩ := exists_ne_zero_bil_eq_zero (Q := Q) hge z
      have hQw : Q w ≠ 0 := fun h => hw0 (hiso w hwW h)
      refine ⟨symmetry Q w hQw, isOn_symmetry hwW hQw, latMap_eq_of_aniso hiso hK (isOn_symmetry hwW hQw),
        det_symmetry Q hQw, ?_⟩
      rw [symmetry_apply_of_bil hQw hzw, sub_self]
      exact K.zero_mem
  · push Not at hiso
    obtain ⟨w, hwW, hQw, hw0⟩ := hiso
    obtain ⟨e, f, K', hs⟩ := exists_hypSplit hWreg hK hwW hw0 hQw
    have heW := hs.e_mem_W hK
    have hfW := hs.f_mem_W hK
    have hQef : Q (e - f) = -1 := by
      rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg, hs.Qe, hs.Qf]
      linear_combination -hs.bef
    have hQef0 : Q (e - f) ≠ 0 := by rw [hQef]; exact neg_ne_zero.mpr one_ne_zero
    have hsym : symmetry Q (e - f) hQef0 ∈ orthLat Q K :=
      symmetry_mem_orthLat_of_inv hK.2.2.1 (K.sub_mem hs.he hs.hf) hQef0
        (by rw [hQef]; exact ⟨-1, by simp⟩)
    refine ⟨symmetry Q (e - f) hQef0, isOn_symmetry (W.sub_mem heW hfW) hQef0, hsym.2, det_symmetry Q hQef0, ?_⟩
    rw [symmetry_apply, sub_sub_cancel_left, hQef]
    refine K.neg_mem (smul_mem_of_int ?_ (K.sub_mem hs.he hs.hf))
    rw [div_neg, div_one, bil_sub_right, mul_sub]
    exact neg_mem (sub_mem (hzd e hs.he) (hzd f hs.hf))

end DVR

end QuadFormsKB.Shimura2004.Local105
