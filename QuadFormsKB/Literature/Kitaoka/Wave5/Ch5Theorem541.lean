/-
# Kitaoka 1993, Theorem 5.4.1 (Eichler): extending isometries congruent to the identity

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.4, Theorem 5.4.1 and its proof, pp. 86–87
(printed pages). The statement `Kitaoka.Padic.Theorem541` is in `Ch5Extension.lean`.

**Proves** `theorem541 : Theorem541` (unconditional), hence Corollary 5.4.1 unconditionally
(`corollary541_uncond`).

**Proof** (Kitaoka's, slightly simplified). Let $A = \max_i a_i$; then $p^A\tilde M \subseteq M$. Since
$a\,\mathfrak n(L^\sharp) \subseteq (2)$ we have $aB(L^\sharp, L^\sharp) \subseteq R$, hence $aL^\sharp \subseteq L^{\sharp\sharp} = L$
(`smul_dual_le`), and $L^a = L_a = aL^\sharp$. Extend $\sigma$ to $\tilde\sigma(x) = p^{-A}\sigma(p^Ax)$ on $\tilde M$; then
$\tilde\sigma(x) - x \in aL^\sharp \subseteq L$, so $\tilde\sigma(\tilde M) \subseteq FN \cap L = \tilde N$, and the same for
$\sigma^{-1}$ gives $\tilde\sigma(\tilde M) = \tilde N$ (instead of Kitaoka's index count). Condition (3) of Theorem 5.3.4
for $\tilde M$: $\tilde M$ is a direct summand of $L$ ($L/\tilde M$ is finitely generated and torsion-free, hence free), so
every linear form on $\tilde M$ extends to $L$, and every linear form on $L$ is $B(\cdot, u)$ with $u \in L^\sharp$
($B$ nondegenerate). Theorem 5.3.4 (`theorem534`) with $a$ gives the extension.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch5Theorem534
import QuadFormsKB.Literature.Kitaoka.Wave4.Ch5Lifting
import QuadFormsKB.Literature.OMeara.Sec82Dual

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

local notation "V" => Fin n → ℚ_[p]

theorem pbil_comm (Q : QuadraticForm ℚ_[p] V) (x y : V) : pbil Q x y = pbil Q y x := by
  simp [pbil, polar_comm]

theorem pbil_add_left (Q : QuadraticForm ℚ_[p] V) (x x' y : V) :
    pbil Q (x + x') y = pbil Q x y + pbil Q x' y := by
  simp [pbil, polar_add_left, add_div]

theorem pbil_smul_left (Q : QuadraticForm ℚ_[p] V) (c : ℚ_[p]) (x y : V) :
    pbil Q (c • x) y = c * pbil Q x y := by
  simp [pbil, polar_smul_left, mul_div_assoc]

theorem pbil_smul_right (Q : QuadraticForm ℚ_[p] V) (c : ℚ_[p]) (x y : V) :
    pbil Q x (c • y) = c * pbil Q x y := by
  rw [pbil_comm, pbil_smul_left, pbil_comm]

theorem pbil_self (Q : QuadraticForm ℚ_[p] V) (x : V) : pbil Q x x = Q x := by
  simp only [pbil, QuadraticMap.polar_self, two_nsmul]
  ring

theorem two_pbil (Q : QuadraticForm ℚ_[p] V) (x y : V) : 2 * pbil Q x y = Q (x + y) - Q x - Q y := by
  simp only [pbil, polar]; ring

theorem inIdeal_one_iff {x : ℚ_[p]} : InIdeal 1 x ↔ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨r, rfl⟩; simpa using r.norm_le_one
  · intro h; exact ⟨⟨x, h⟩, by simp⟩

/-- $a\,B(L^\sharp, L^\sharp) \subseteq R$ when $a\,\mathfrak n(L^\sharp) \subseteq (2)$. -/
theorem a_pbil_dual (Q : QuadraticForm ℚ_[p] V) (L : Submodule ℤ_[p] V) {a : ℚ_[p]}
    (hdual : ∀ x ∈ dualL Q L, InIdeal 2 (a * Q x)) {z w : V} (hz : z ∈ dualL Q L) (hw : w ∈ dualL Q L) :
    InIdeal 1 (a * pbil Q z w) := by
  have hzw : z + w ∈ dualL Q L := fun y hy => by
    obtain ⟨r, hr⟩ := hz y hy
    obtain ⟨s, hs⟩ := hw y hy
    exact ⟨r + s, by rw [pbil_add_left, hr, hs]; push_cast; ring⟩
  obtain ⟨r1, h1⟩ := hdual _ hzw
  obtain ⟨r2, h2⟩ := hdual _ hz
  obtain ⟨r3, h3⟩ := hdual _ hw
  refine ⟨r1 - r2 - r3, ?_⟩
  have e := two_pbil Q z w
  have : 2 * (a * pbil Q z w) = 2 * (r1 - r2 - r3 : ℤ_[p]) := by
    rw [mul_left_comm, e]; push_cast
    linear_combination h1 - h2 - h3
  have h2' : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  rw [one_mul]
  exact mul_left_cancel₀ h2' this

section Dual

/-- O'Meara's $B$ is Kitaoka's $B$ (`pbil`). -/
theorem bil_eq_pbil (Q : QuadraticForm ℚ_[p] V) (x y : V) :
    letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
    OMeara.bil Q x y = pbil Q x y := by
  letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  have h := QuadraticMap.associated_eq_self_apply ℚ_[p] Q x
  have e : OMeara.bil Q x y * 2 = polar Q x y := by
    have := QuadraticMap.two_nsmul_associated ℚ_[p] Q
    have h2 := LinearMap.congr_fun₂ this x y
    simp only [LinearMap.smul_apply, two_nsmul, LinearMap.add_apply, polarBilin_apply_apply] at h2
    simp only [OMeara.bil]
    linear_combination h2
  simp only [pbil]
  field_simp
  exact e

/-- A lattice on a regular space is a regular lattice. -/
theorem isRegular_of_lattice (Q : QuadraticForm ℚ_[p] V) (hnd : (polarBilin Q).Nondegenerate) {L : Submodule ℤ_[p] V} (hL : L.IsLattice ℚ_[p]) :
    letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
    OMeara.IsRegular Q L := by
  letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  intro x _ hx
  apply (QuadraticForm.nondegenerate_polarBilin_iff Q).mp hnd x
  intro y
  have hy : y ∈ Submodule.span ℚ_[p] (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hy using Submodule.span_induction with
  | mem w hw =>
    have := hx w hw
    rw [bil_eq_pbil] at this
    simp only [pbil] at this
    linear_combination 2 * this
  | zero => simp
  | add u w _ _ hu hw => rw [polar_add_right, hu, hw, add_zero]
  | smul c w _ hw => rw [polar_smul_right, hw, smul_zero]

/-- $aL^\sharp \subseteq L$ when $a\,\mathfrak n(L^\sharp) \subseteq (2)$ (Kitaoka's (2), p. 87). -/
theorem smul_dual_le (Q : QuadraticForm ℚ_[p] V) (hnd : (polarBilin Q).Nondegenerate) {L : Submodule ℤ_[p] V} (hL : L.IsLattice ℚ_[p])
    {a : ℚ_[p]} (hdual : ∀ x ∈ dualL Q L, InIdeal 2 (a * Q x)) {z : V} (hz : z ∈ dualL Q L) : a • z ∈ L := by
  letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  have hreg := isRegular_of_lattice Q hnd hL
  rw [← OMeara.dual_dual Q hL.fg hreg, OMeara.mem_dual]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [OMeara.span_dual Q hL.fg hreg, hL.span_eq_top]; trivial
  · have hwd : w ∈ dualL Q L := fun y hy => by
      have := (OMeara.mem_dual Q).mp hw |>.2 y hy
      rw [bil_eq_pbil] at this
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp this
      exact ⟨r, by rw [← hr, one_mul]; rfl⟩
    rw [bil_eq_pbil, pbil_smul_left]
    obtain ⟨r, hr⟩ := a_pbil_dual Q L hdual hz hwd
    rw [hr, one_mul]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩

end Dual

section Duality

/-- A finitely generated $\mathbb Z_p$-submodule of $V$ is free. -/
theorem free_of_fg {L : Submodule ℤ_[p] V} (hL : L.FG) : Module.Free ℤ_[p] L := by
  have hfin : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hL
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have htf : Module.IsTorsionFree ℤ_[p] L := by
    refine ⟨fun r hr x y hxy => ?_⟩
    apply Subtype.ext
    have h1 := congrArg (fun z : L => (z : V)) hxy
    simp only [Submodule.coe_smul] at h1
    rw [← algebraMap_smul ℚ_[p] r (x : V), ← algebraMap_smul ℚ_[p] r (y : V)] at h1
    have hr' : algebraMap ℤ_[p] ℚ_[p] r ≠ 0 := fun h => hr.ne_zero (hinj (h.trans (map_zero _).symm))
    exact smul_right_injective _ hr' h1
  exact Module.free_of_finite_type_torsion_free'

/-- Every linear form on a lattice $L$ of a regular space is $B(\cdot, u)$ with $u \in L^\sharp$. -/
theorem exists_dual_rep_L (Q : QuadraticForm ℚ_[p] V) (hnd : (polarBilin Q).Nondegenerate) {L : Submodule ℤ_[p] V} (hL : L.IsLattice ℚ_[p])
    (f : L →ₗ[ℤ_[p]] ℤ_[p]) : ∃ u ∈ dualL Q L, ∀ y : L, (f y : ℚ_[p]) = pbil Q y u := by
  classical
  have hfree := free_of_fg hL.fg
  have hfin : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hL.fg
  let b := Module.Free.chooseBasis ℤ_[p] L
  let bV : Module.Free.ChooseBasisIndex ℤ_[p] L → V := fun i => (b i : V)
  have hliZ : LinearIndependent ℤ_[p] bV := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hli : LinearIndependent ℚ_[p] bV := (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hliZ
  have hspan : ⊤ ≤ Submodule.span ℚ_[p] (Set.range bV) := by
    rw [← hL.span_eq_top]
    apply Submodule.span_le.mpr
    intro y hy
    have hy' : (⟨y, hy⟩ : L) ∈ Submodule.span ℤ_[p] (Set.range b) := by rw [b.span_eq]; trivial
    have := Submodule.mem_map_of_mem (f := L.subtype) hy'
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact Submodule.span_subset_span ℤ_[p] ℚ_[p] _ this
  let bF : Module.Basis _ ℚ_[p] V := Module.Basis.mk hli hspan
  let φ : V →ₗ[ℚ_[p]] ℚ_[p] := bF.constr ℚ_[p] (fun i => (f (b i) : ℚ_[p]))
  have hφ : ∀ y : L, φ y = (f y : ℚ_[p]) := by
    have := b.ext (f₁ := (φ.restrictScalars ℤ_[p]) ∘ₗ L.subtype)
      (f₂ := (Algebra.linearMap ℤ_[p] ℚ_[p]) ∘ₗ f) (fun i => by
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
          Algebra.linearMap_apply]
        have : (b i : V) = bF i := by simp [bF, bV]
        rw [this, Module.Basis.constr_basis]
        rfl)
    intro y
    exact LinearMap.congr_fun this y
  let u : V := (LinearMap.BilinForm.toDual (polarBilin Q) hnd).symm ((2 : ℚ_[p]) • φ)
  have hu : ∀ v, polar Q u v = 2 * φ v := by
    intro v
    have := LinearMap.BilinForm.toDual_def (B := polarBilin Q) hnd (m := u) (n := v)
    simp only [u, LinearEquiv.apply_symm_apply, LinearMap.smul_apply, smul_eq_mul,
      polarBilin_apply_apply] at this
    exact this.symm
  have hpb : ∀ v, pbil Q v u = φ v := by
    intro v
    rw [pbil, polar_comm, hu]; ring
  refine ⟨u, fun y hy => ?_, fun y => by rw [hpb, hφ]⟩
  rw [pbil_comm, hpb, hφ ⟨y, hy⟩]
  exact ⟨f ⟨y, hy⟩, by rw [one_mul]⟩

/-- **Every linear form on a primitive submodule** $\tilde M = FM \cap L$ of $L$ is $B(\cdot, u)$ with
$u \in L^\sharp$ (Kitaoka's dual basis argument, p. 87). -/
theorem exists_dual_rep (Q : QuadraticForm ℚ_[p] V) (hnd : (polarBilin Q).Nondegenerate) {L Mt : Submodule ℤ_[p] V} (hL : L.IsLattice ℚ_[p])
    (hMtL : Mt ≤ L) (hsat : ∀ (r : ℤ_[p]) (x : V), r ≠ 0 → x ∈ L → r • x ∈ Mt → x ∈ Mt)
    (f : Mt →ₗ[ℤ_[p]] ℤ_[p]) : ∃ u ∈ dualL Q L, ∀ x : Mt, (f x : ℚ_[p]) = pbil Q x u := by
  classical
  have hfin : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hL.fg
  let MtL := Mt.comap L.subtype
  -- $L / \tilde M$ is free
  have htf : Module.IsTorsionFree ℤ_[p] (L ⧸ MtL) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective MtL x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective MtL y
    simp only [← Submodule.Quotient.mk_smul] at hxy
    rw [Submodule.Quotient.eq] at hxy ⊢
    have hxy' : r • (x - y) ∈ MtL := by rw [smul_sub]; exact hxy
    exact hsat r _ hr.ne_zero (L.sub_mem x.2 y.2) hxy'
  have hqfree : Module.Free ℤ_[p] (L ⧸ MtL) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property MtL.mkQ LinearMap.id (Submodule.mkQ_surjective _)
  let π : L →ₗ[ℤ_[p]] MtL := LinearMap.codRestrict MtL (LinearMap.id - s ∘ₗ MtL.mkQ) (fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    have := LinearMap.congr_fun hs (MtL.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self])
  let eMt : MtL ≃ₗ[ℤ_[p]] Mt := Submodule.comapSubtypeEquivOfLe hMtL
  obtain ⟨u, hu, hu'⟩ := exists_dual_rep_L Q hnd hL (f ∘ₗ eMt.toLinearMap ∘ₗ π)
  refine ⟨u, hu, fun x => ?_⟩
  have hx := hu' ⟨x, hMtL x.2⟩
  have hπ : π ⟨x, hMtL x.2⟩ = ⟨⟨x, hMtL x.2⟩, x.2⟩ := by
    apply Subtype.ext
    simp only [π, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    have : MtL.mkQ ⟨x, hMtL x.2⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr x.2
    rw [this, map_zero, sub_zero]
  have he : eMt ⟨⟨x, hMtL x.2⟩, x.2⟩ = x := rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hπ, he] at hx
  exact hx

end Duality

/-! ### The proof -/

theorem dualL_neg (Q : QuadraticForm ℚ_[p] V) (L : Submodule ℤ_[p] V) {z : V} (hz : z ∈ dualL Q L) :
    -z ∈ dualL Q L := fun y hy => by
  obtain ⟨r, hr⟩ := hz y hy
  exact ⟨-r, by rw [show -z = (-1 : ℚ_[p]) • z by simp, pbil_smul_left, hr]; push_cast; ring⟩

theorem pow_smul_eq (A : ℕ) (x : V) : ((p : ℤ_[p]) ^ A) • x = ((p : ℚ_[p]) ^ A) • x := by
  rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ A) x, map_pow, map_natCast]

/-- $p^A$ kills $\bigoplus_i R/(p^{a_i})$, $A = \max a_i$, so $p^A\tilde M \subseteq M$. -/
theorem pow_mem_of_quot {r : ℕ} (e : Fin r → ℕ) {X Y : Submodule ℤ_[p] V}
    (h : Nonempty ((X ⧸ Y.comap X.subtype) ≃ₗ[ℤ_[p]] ((i : Fin r) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ e i})))
    {x : V} (hx : x ∈ X) : ((p : ℤ_[p]) ^ Finset.univ.sup e) • x ∈ Y := by
  obtain ⟨φ⟩ := h
  have h0 : φ (((p : ℤ_[p]) ^ Finset.univ.sup e) • Submodule.Quotient.mk (⟨x, hx⟩ : X)) = 0 := by
    rw [map_smul]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply]
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (φ (Submodule.Quotient.mk ⟨x, hx⟩) i)
    rw [← hc, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mul_mem_right
    rw [Ideal.mem_span_singleton]
    exact pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i))
  have h1 := φ.injective (h0.trans (map_zero φ).symm)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

/-- The extension $x \mapsto p^{-A}g(p^Ax)$ of $g : X \to Y$ to $\tilde X$ (where $p^A\tilde X \subseteq X$). -/
def extMap (A : ℕ) {X Y Xt : Submodule ℤ_[p] V} (hk : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X)
    (g : X →ₗ[ℤ_[p]] Y) : Xt →ₗ[ℤ_[p]] V :=
  ((((p : ℚ_[p]) ^ A)⁻¹ • LinearMap.id : V →ₗ[ℚ_[p]] V).restrictScalars ℤ_[p]) ∘ₗ Y.subtype ∘ₗ g ∘ₗ
    LinearMap.codRestrict X (((p : ℤ_[p]) ^ A) • Xt.subtype) (fun x => hk x x.2)

theorem extMap_apply (A : ℕ) {X Y Xt : Submodule ℤ_[p] V} (hk : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X)
    (g : X →ₗ[ℤ_[p]] Y) (x : Xt) :
    extMap A hk g x = ((p : ℚ_[p]) ^ A)⁻¹ • (g ⟨_, hk x x.2⟩ : V) := rfl

theorem pp_ne_zero (A : ℕ) : ((p : ℚ_[p]) ^ A) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- $\tilde g(x) - x = az$ with $z \in L^\sharp$ when $g(x) - x \in ap^AL^\sharp$. -/
theorem extMap_cong (Q : QuadraticForm ℚ_[p] V) (L : Submodule ℤ_[p] V) (a : ℚ_[p]) (A : ℕ)
    {X Y Xt : Submodule ℤ_[p] V} (hk : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X) (g : X →ₗ[ℤ_[p]] Y)
    (hg : ∀ x : X, ∃ z ∈ dualL Q L, (g x : V) - x = (a * (p : ℚ_[p]) ^ A) • z) (x : Xt) :
    ∃ z ∈ dualL Q L, extMap A hk g x - x = a • z := by
  have hpA := pp_ne_zero (p := p) A
  obtain ⟨z, hz, hz'⟩ := hg ⟨_, hk x x.2⟩
  refine ⟨z, hz, ?_⟩
  rw [extMap_apply]
  have e1 : ((⟨_, hk x x.2⟩ : X) : V) = ((p : ℚ_[p]) ^ A) • (x : V) := pow_smul_eq A _
  rw [e1] at hz'
  have e2 : (g ⟨_, hk x x.2⟩ : V) = ((p : ℚ_[p]) ^ A) • (x : V) + (a * (p : ℚ_[p]) ^ A) • z := by
    rw [← hz']; abel
  rw [e2, smul_add, smul_smul, inv_mul_cancel₀ hpA, one_smul, smul_smul,
    show ((p : ℚ_[p]) ^ A)⁻¹ * (a * (p : ℚ_[p]) ^ A) = a by field_simp]
  abel

/-- $\tilde g(\tilde X) \subseteq \tilde Y$. -/
theorem extMap_mem (Q : QuadraticForm ℚ_[p] V) (L : Submodule ℤ_[p] V) (a : ℚ_[p]) (A : ℕ)
    (haL : ∀ z ∈ dualL Q L, a • z ∈ L)
    {X Y Xt : Submodule ℤ_[p] V} (hk : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X) (g : X →ₗ[ℤ_[p]] Y)
    (hg : ∀ x : X, ∃ z ∈ dualL Q L, (g x : V) - x = (a * (p : ℚ_[p]) ^ A) • z) (hXtL : Xt ≤ L) (x : Xt) :
    extMap A hk g x ∈ (Submodule.span ℚ_[p] (Y : Set V)).restrictScalars ℤ_[p] ⊓ L := by
  obtain ⟨z, hz, hz'⟩ := extMap_cong Q L a A hk g hg x
  refine ⟨?_, ?_⟩
  · rw [extMap_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (g _).2)
  · have : extMap A hk g x = (x : V) + a • z := by rw [← hz']; abel
    rw [this]
    exact L.add_mem (hXtL x.2) (haL z hz)

/-- The extensions of $g$ and $g^{-1}$ are inverse to each other. -/
theorem extMap_inv (A : ℕ) {X Y Xt Yt : Submodule ℤ_[p] V} (hkX : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X)
    (hkY : ∀ y ∈ Yt, ((p : ℤ_[p]) ^ A) • y ∈ Y) (g : X ≃ₗ[ℤ_[p]] Y) (y : Yt)
    (hy : extMap A hkY g.symm.toLinearMap y ∈ Xt) :
    extMap A hkX g.toLinearMap ⟨_, hy⟩ = y := by
  have hpA := pp_ne_zero (p := p) A
  rw [extMap_apply]
  have e1 : (⟨_, hkX _ hy⟩ : X) = g.symm ⟨_, hkY y y.2⟩ := by
    apply Subtype.ext
    show ((p : ℤ_[p]) ^ A) • extMap A hkY g.symm.toLinearMap y = _
    rw [extMap_apply, pow_smul_eq, smul_smul, mul_inv_cancel₀ hpA, one_smul]
    rfl
  simp only [LinearEquiv.coe_coe]
  rw [e1, LinearEquiv.apply_symm_apply]
  show ((p : ℚ_[p]) ^ A)⁻¹ • (((p : ℤ_[p]) ^ A) • (y : V)) = y
  rw [pow_smul_eq, smul_smul, inv_mul_cancel₀ hpA, one_smul]

/-- The other composition. -/
theorem extMap_inv' (A : ℕ) {X Y Xt Yt : Submodule ℤ_[p] V} (hkX : ∀ x ∈ Xt, ((p : ℤ_[p]) ^ A) • x ∈ X)
    (hkY : ∀ y ∈ Yt, ((p : ℤ_[p]) ^ A) • y ∈ Y) (g : X ≃ₗ[ℤ_[p]] Y) (x : Xt)
    (hx : extMap A hkX g.toLinearMap x ∈ Yt) :
    extMap A hkY g.symm.toLinearMap ⟨_, hx⟩ = x := by
  have hpA := pp_ne_zero (p := p) A
  rw [extMap_apply]
  have e1 : (⟨_, hkY _ hx⟩ : Y) = g ⟨_, hkX x x.2⟩ := by
    apply Subtype.ext
    show ((p : ℤ_[p]) ^ A) • extMap A hkX g.toLinearMap x = _
    rw [extMap_apply, pow_smul_eq, smul_smul, mul_inv_cancel₀ hpA, one_smul]
    rfl
  simp only [LinearEquiv.coe_coe]
  rw [e1, LinearEquiv.symm_apply_apply]
  show ((p : ℚ_[p]) ^ A)⁻¹ • (((p : ℤ_[p]) ^ A) • (x : V)) = x
  rw [pow_smul_eq, smul_smul, inv_mul_cancel₀ hpA, one_smul]

/-- **Kitaoka 1993, Theorem 5.4.1** (Eichler, p. 86): `Theorem541`. Unconditional. -/
@[kb "kitaoka1993" "§5.4, Thm. 5.4.1, p. 86 (proof)"]
theorem theorem541 : Theorem541 := by
  intro p _ n Q L M N a r e hnd hL hM hN ha _ Mt Nt hMq hNq hdual σ hσq hσ
  classical
  set A := Finset.univ.sup e with hA
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℚ_[p]) ^ A) ≠ 0 := pow_ne_zero _ hp0
  have hMMt : M ≤ Mt := fun x hx => ⟨Submodule.subset_span hx, hM hx⟩
  have hNNt : N ≤ Nt := fun x hx => ⟨Submodule.subset_span hx, hN hx⟩
  have hkM : ∀ x ∈ Mt, ((p : ℤ_[p]) ^ A) • x ∈ M := fun x hx => pow_mem_of_quot e hMq hx
  have hkN : ∀ x ∈ Nt, ((p : ℤ_[p]) ^ A) • x ∈ N := fun x hx => pow_mem_of_quot e hNq hx
  have haL : ∀ z ∈ dualL Q L, a • z ∈ L := fun z hz => smul_dual_le Q hnd hL hdual hz
  -- the congruence for $\sigma$ and $\sigma^{-1}$
  have hσ' : ∀ y : N, ∃ z ∈ dualL Q L, (σ.symm y : (Fin n → ℚ_[p])) - y = (a * (p : ℚ_[p]) ^ A) • z := by
    intro y
    obtain ⟨z, hz, hz'⟩ := hσ (σ.symm y)
    refine ⟨-z, dualL_neg Q L hz, ?_⟩
    rw [LinearEquiv.apply_symm_apply] at hz'
    rw [smul_neg, ← hz']; abel
  have hMtL : Mt ≤ L := inf_le_right
  have hNtL : Nt ≤ L := inf_le_right
  let f1 : Mt →ₗ[ℤ_[p]] Nt := LinearMap.codRestrict Nt (extMap A hkM σ.toLinearMap)
    (extMap_mem Q L a A haL hkM σ.toLinearMap hσ hMtL)
  let f2 : Nt →ₗ[ℤ_[p]] Mt := LinearMap.codRestrict Mt (extMap A hkN σ.symm.toLinearMap)
    (extMap_mem Q L a A haL hkN σ.symm.toLinearMap hσ' hNtL)
  let σt : Mt ≃ₗ[ℤ_[p]] Nt := LinearEquiv.ofLinear f1 f2
    (LinearMap.ext fun y => Subtype.ext (extMap_inv A hkM hkN σ y (f2 y).2))
    (LinearMap.ext fun x => Subtype.ext (extMap_inv' A hkM hkN σ x (f1 x).2))
  have hσt : ∀ x : Mt, (σt x : (Fin n → ℚ_[p])) = extMap A hkM σ.toLinearMap x := fun x => rfl
  -- $\tilde\sigma = \sigma$ on $M$
  have hσtM : ∀ x : M, (σt ⟨x, hMMt x.2⟩ : (Fin n → ℚ_[p])) = σ x := by
    intro x
    rw [hσt, extMap_apply]
    have e1 : (⟨_, hkM _ (hMMt x.2)⟩ : M) = ((p : ℤ_[p]) ^ A) • x := Subtype.ext rfl
    simp only [LinearEquiv.coe_coe]
    rw [e1, map_smul, Submodule.coe_smul, pow_smul_eq, smul_smul, inv_mul_cancel₀ hpA, one_smul]
  -- isometry
  have hσtq : ∀ x : Mt, Q (σt x) = Q x := by
    intro x
    rw [hσt, extMap_apply, QuadraticMap.map_smul]
    simp only [LinearEquiv.coe_coe]
    rw [hσq, show ((⟨_, hkM x x.2⟩ : M) : (Fin n → ℚ_[p])) = ((p : ℚ_[p]) ^ A) • (x : (Fin n → ℚ_[p])) from pow_smul_eq A _,
      QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      show ((p : ℚ_[p]) ^ A)⁻¹ * ((p : ℚ_[p]) ^ A)⁻¹ * ((p : ℚ_[p]) ^ A * (p : ℚ_[p]) ^ A) = 1 by field_simp,
      one_mul]
  -- saturation of $\tilde M$, $\tilde N$
  have hsat : ∀ {X : Submodule ℤ_[p] (Fin n → ℚ_[p])} (r' : ℤ_[p]) (x : (Fin n → ℚ_[p])), r' ≠ 0 → x ∈ L →
      r' • x ∈ (Submodule.span ℚ_[p] (X : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L →
      x ∈ (Submodule.span ℚ_[p] (X : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L := by
    intro X r' x hr hx hrx
    refine ⟨?_, hx⟩
    have hr' : algebraMap ℤ_[p] ℚ_[p] r' ≠ 0 :=
      fun h => hr (IsFractionRing.injective ℤ_[p] ℚ_[p] (h.trans (map_zero _).symm))
    have h1 := hrx.1
    rw [← algebraMap_smul ℚ_[p] r' x] at h1
    have : x = (algebraMap ℤ_[p] ℚ_[p] r')⁻¹ • (algebraMap ℤ_[p] ℚ_[p] r' • x) := by
      rw [smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    show _ ∈ Submodule.span ℚ_[p] (X : Set (Fin n → ℚ_[p]))
    exact Submodule.smul_mem _ _ h1
  -- condition (3) of Theorem 5.3.4
  have h3 : ∀ {Xt : Submodule ℤ_[p] (Fin n → ℚ_[p])}, Xt ≤ L →
      (∀ (r' : ℤ_[p]) (x : (Fin n → ℚ_[p])), r' ≠ 0 → x ∈ L → r' • x ∈ Xt → x ∈ Xt) →
      ∀ f : Xt →ₗ[ℤ_[p]] ℤ_[p], ∃ y ∈ lowerL Q L a, ∀ x : Xt, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y := by
    intro Xt hXtL hXsat f
    obtain ⟨u, hu, hu'⟩ := exists_dual_rep Q hnd hL hXtL hXsat f
    refine ⟨a • u, ⟨⟨haL u hu, fun w hw => ?_⟩, ?_⟩, fun x => ?_⟩
    · obtain ⟨s, hs⟩ := hu w hw
      exact ⟨s, by rw [pbil_smul_left, hs, one_mul]⟩
    · obtain ⟨s, hs⟩ := hdual u hu
      exact ⟨s, by rw [QuadraticMap.map_smul, smul_eq_mul, mul_assoc, hs]; ring⟩
    · rw [hu' x, pbil_smul_right]; field_simp
  have h3' : ∀ {Xt : Submodule ℤ_[p] (Fin n → ℚ_[p])}, Xt ≤ L → ∀ y ∈ lowerL Q L a,
      ∃ f : Xt →ₗ[ℤ_[p]] ℤ_[p], ∀ x : Xt, (f x : ℚ_[p]) = a⁻¹ * pbil Q x y := by
    intro Xt hXtL y hy
    have hval : ∀ x : Xt, ‖a⁻¹ * pbil Q x y‖ ≤ 1 := by
      intro x
      obtain ⟨s, hs⟩ := hy.1.2 x (hXtL x.2)
      rw [pbil_comm, hs, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      exact s.norm_le_one
    refine ⟨{ toFun := fun x => ⟨a⁻¹ * pbil Q x y, hval x⟩
              map_add' := fun x x' => by
                apply Subtype.ext
                change a⁻¹ * pbil Q ((x : Fin n → ℚ_[p]) + x') y = a⁻¹ * pbil Q x y + a⁻¹ * pbil Q x' y
                rw [pbil_add_left]; ring
              map_smul' := fun c x => by
                apply Subtype.ext
                change a⁻¹ * pbil Q (c • (x : Fin n → ℚ_[p])) y = (c : ℚ_[p]) * (a⁻¹ * pbil Q x y)
                rw [← algebraMap_smul ℚ_[p] c (x : (Fin n → ℚ_[p])), pbil_smul_left]
                rw [show algebraMap ℤ_[p] ℚ_[p] c = (c : ℚ_[p]) from rfl]
                ring }, fun x => rfl⟩
  have hσtH : ∀ x : Mt, (σt x : (Fin n → ℚ_[p])) - x ∈ upperL Q L a := by
    intro x
    obtain ⟨z, hz, hz'⟩ := extMap_cong Q L a A hkM σ.toLinearMap hσ x
    rw [hσt, hz']
    refine ⟨haL z hz, fun w hw => ?_⟩
    obtain ⟨s, hs⟩ := hz w hw
    exact ⟨s, by rw [pbil_smul_left, hs, one_mul]⟩
  obtain ⟨τ, hτQ, hτL, hτL', hτσ, hτS⟩ := theorem534 p n Q L Mt Nt a hnd hL hMtL hNtL ha
    (h3 hMtL (fun r' x hr hx hrx => hsat r' x hr hx hrx)) (h3' hMtL)
    (h3 hNtL (fun r' x hr hx hrx => hsat r' x hr hx hrx)) (h3' hNtL) σt hσtq hσtH
  refine ⟨τ, hτQ, hτL, hτL', fun x => ?_, fun x hx => ?_⟩
  · rw [← hσtM x]
    exact hτσ ⟨x, hMMt x.2⟩
  · obtain ⟨⟨_, hB⟩, _⟩ := hτS x hx
    refine ⟨a⁻¹ • (τ x - x), fun w hw => ?_, by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]⟩
    obtain ⟨s, hs⟩ := hB w hw
    exact ⟨s, by rw [pbil_smul_left, hs, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩

/-- **Kitaoka 1993, Corollary 5.4.1** (p. 87), unconditional: `corollary541` (Wave4/Ch5Lifting.lean) with its input
`Theorem541` discharged by `theorem541`. In a unimodular lattice $L$ over $\mathbb Z_p$ with $\mathfrak n(L) = (2)$, two
isometric submodules that are direct summands are carried onto each other by an isometry of $L$. -/
@[kb "kitaoka1993" "§5.4, Cor. 5.4.1, p. 87 (unconditional)"]
theorem corollary541_uncond {n : ℕ} (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    {L M N : Submodule ℤ_[p] (Fin n → ℚ_[p])} (hQ : (polarBilin Q).Nondegenerate)
    (hL : L.IsLattice ℚ_[p]) (hU : OMeara.IsUnimodular Q L) (hnorm : OMeara.normIdeal Q L = ℤ_[p] ∙ (2 : ℚ_[p]))
    (hML : M ≤ L) (hNL : N ≤ L) (hMN : OMeara.IsometricLat Q Q M N)
    (hMs : ∃ M' : Submodule ℤ_[p] (Fin n → ℚ_[p]), M ⊓ M' = ⊥ ∧ M ⊔ M' = L)
    (hNs : ∃ N' : Submodule ℤ_[p] (Fin n → ℚ_[p]), N ⊓ N' = ⊥ ∧ N ⊔ N' = L) :
    ∃ τ ∈ OMeara.orthLat Q L, OMeara.latMap τ M = N :=
  corollary541 theorem541 Q hQ hL hU hnorm hML hNL hMN hMs hNs

end QuadFormsKB.Kitaoka.Padic
