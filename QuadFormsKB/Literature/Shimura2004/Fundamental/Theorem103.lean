/-
# Shimura 2004, Theorem 10.3 (local finiteness of the orbits on $\{x \in \Lambda \mid \varphi[x] = \varphi[h]\}$)

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 10.3 (printed p. 94).

**Statement** (`Theorem10_3`, `Diophantine.lean`). $F$ the completion of a number field at a finite prime,
$(V, \varphi)$ nondegenerate of dimension $n > 1$, $\Lambda$ a lattice, $h \in \Lambda$ with $\varphi[h] \ne 0$,
$D = O^+(\Lambda)$. Then $\{x \in \Lambda \mid \varphi[x] = \varphi[h]\} = \bigcup_{\alpha \in A} D\,\alpha h$ for a
finite set $A \subseteq O^+(V)$.

**Proof.** Scale $\varphi$ so that $\varphi[\Lambda] \subseteq \mathfrak g$ and take a $\mathfrak g$-maximal
$L \supseteq \Lambda$ (82:18). By Theorem 10.5 (the transitivity part, `Local105.exists_orthLat_of_phi`) the
$O(L)$-orbits on $\{x \in L \mid \varphi[x] = \varphi[h]\}$ are classified by the ideal $\varphi(x, L)$, which lies
between $\varphi[h]\mathfrak g$ and $\tfrac12\mathfrak g$: finitely many orbits. With $d\,L \subseteq \Lambda$, the
lattices $\sigma^{-1}\Lambda$, $\sigma \in O(L)$, lie between $dL$ and $L$, a finite set (finite residue field), so
$O(L)$ is a finite union of cosets $(O(L) \cap O(\Lambda))\sigma_M$; a symmetry of $\Lambda$ (91:4) passes from
$O(\Lambda)$ to $O^+(\Lambda)$, and Witt's theorem gives the $\alpha \in O^+(V)$.

**Proves** (unconditional; standard axioms only): `Local105.theorem10_3_abstract` (over a Henselian discrete
valuation ring all of whose quotients $R/d$, $d \ne 0$, are finite) and `theorem10_3_holds : Theorem10_3`.
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Theorem105
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Literature.OMeara.Sec92Jordan
import QuadFormsKB.LocalDensity.DVRGeneral
import QuadFormsKB.Citation

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004.Local105

open QuadFormsKB.OMeara QuadFormsKB.Shimura2004

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {Q : QuadraticForm F V}

/-- **The transitivity part of Theorem 10.5** for primitive vectors (no (8.1) needed). -/
theorem exists_orthLat_of_primitive [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {L : Submodule R V} (hL : IsMaximal Q 1 L) {h k : V} (hdh : IsDual Q L h) (hdk : IsDual Q L k)
    (hph : ∃ y ∈ L, 2 * bil Q h y = 1) (hpk : ∃ y ∈ L, 2 * bil Q k y = 1) (hQ : Q h = Q k) :
    ∃ σ ∈ orthLat Q L, σ h = k := by
  by_cases hiso : ∀ x : V, Q x = 0 → x = 0
  · have horth : orthLat Q L = orth Q := orthLat_eq_orth_of_isMaximal Q hiso hL
    by_cases hhk : h = k
    · exact ⟨1, (orthLat Q L).one_mem, by rw [hhk]; rfl⟩
    · have h0 : Q (h - k) ≠ 0 := fun h0 => hhk (sub_eq_zero.mp (hiso _ h0))
      exact ⟨_, by rw [horth]; exact symmetry_mem_orth Q h0, symmetry_sub_apply hQ h0⟩
  · push Not at hiso
    obtain ⟨x, hQx, hx0⟩ := hiso
    obtain ⟨e, f, K, hs⟩ := exists_hypSplit (fun w _ hw => hV.1 w fun w' => hw w' mem_top)
      ((isMaxIn_top_iff Q).mpr hL) mem_top hx0 hQx
    exact exists_orthLat_of_split hV hL.2.1 hs hdh hdk hph hpk hQ

/-- **Theorem 10.5, transitivity part, for arbitrary vectors**: $\varphi[h] = \varphi[k] \ne 0$ and
$\varphi(h, L) = \varphi(k, L)$ give $k = \sigma h$ with $\sigma \in O(L)$. -/
theorem exists_orthLat_of_phi [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {L : Submodule R V} (hL : IsMaximal Q 1 L) {h k : V} (hQ : Q h = Q k) (hQ0 : Q h ≠ 0)
    (hφ : phiIdeal Q h L = phiIdeal Q k L) : ∃ σ ∈ orthLat Q L, σ h = k := by
  have hh0 : h ≠ 0 := by rintro rfl; exact hQ0 (QuadraticMap.map_zero Q)
  have hne : phiIdeal Q h L ≠ ⊥ := by
    intro h0
    apply hh0
    refine hV.1 h fun y => ?_
    refine bil_zero_of_mem_span_F Q (fun z hz => ?_) (hL.1.span_eq_top ▸ Submodule.mem_top : y ∈ _)
    have := bil_mem_phiIdeal (Q := Q) (h := h) hz
    rwa [h0, Submodule.mem_bot] at this
  have hfg : (phiIdeal Q h L).FG := by rw [phiIdeal_eq_map]; exact hL.1.fg.map _
  obtain ⟨c, hc0, hc⟩ := exists_eq_span_singleton hfg hne
  have hck : phiIdeal Q k L = Submodule.span R {c} := hφ ▸ hc
  have gen : ∀ x : V, phiIdeal Q x L = Submodule.span R {c} →
      (∃ y ∈ L, bil Q x y = c) ∧ ∀ y ∈ L, ∃ r : R, algebraMap R F r * c = bil Q x y := by
    intro x hx
    constructor
    · have : c ∈ phiIdeal Q x L := hx ▸ Submodule.mem_span_singleton_self c
      rw [phiIdeal_eq_map] at this
      obtain ⟨y, hy, hyc⟩ := Submodule.mem_map.mp this
      exact ⟨y, hy, hyc⟩
    · intro y hy
      have := bil_mem_phiIdeal (Q := Q) (h := x) hy
      rw [hx, Submodule.mem_span_singleton] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  obtain ⟨⟨y₀, hy₀L, hy₀⟩, hhd⟩ := gen h hc
  obtain ⟨⟨y₁, hy₁L, hy₁⟩, hkd⟩ := gen k hck
  set s : F := (2 * c)⁻¹ with hs
  have h2c : (2 * c) ≠ 0 := mul_ne_zero (Invertible.ne_zero 2) hc0
  have hdual : ∀ x : V, (∀ y ∈ L, ∃ r : R, algebraMap R F r * c = bil Q x y) → IsDual Q L (s • x) := by
    intro x hx y hy
    obtain ⟨r, hr⟩ := hx y hy
    refine ⟨r, ?_⟩
    rw [bil_smul_left, ← hr, hs]
    field_simp
  have hprim : ∀ x y, bil Q x y = c → 2 * bil Q (s • x) y = 1 := by
    intro x y hxy
    rw [bil_smul_left, hxy, hs]
    field_simp
  have hQs : Q (s • h) = Q (s • k) := by rw [Q_smul, Q_smul, hQ]
  obtain ⟨σ, hσL, hσh⟩ := exists_orthLat_of_primitive hV hL (hdual h hhd) (hdual k hkd)
    ⟨y₀, hy₀L, hprim h y₀ hy₀⟩ ⟨y₁, hy₁L, hprim k y₁ hy₁⟩ hQs
  refine ⟨σ, hσL, ?_⟩
  have : h = (2 * c) • (s • h) := by rw [smul_smul, hs, mul_inv_cancel₀ h2c, one_smul]
  rw [this, map_smul, hσh, smul_smul, hs, mul_inv_cancel₀ h2c, one_smul]

/-- An anisotropic vector orthogonal to a given anisotropic vector (regular space of dimension $\ge 2$). -/
theorem exists_Q_ne_zero_perp [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 2 ≤ finrank F V) {y : V} (hy : Q y ≠ 0) : ∃ w, Q w ≠ 0 ∧ bil Q y w = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, -, hw0, hyw⟩ := exists_ne_zero_bil_eq_zero (Q := Q) (W := ⊤) (by rw [finrank_top]; omega) y
  apply hw0
  refine hV.1 w fun z => ?_
  -- `z = c y + z'` with `z' ⊥ y`
  set c := bil Q z y / Q y with hc
  have hz' : bil Q y (z - c • y) = 0 := by
    rw [bil_sub_right, bil_smul_right, bil_self, hc, bil_comm]; field_simp; ring
  have hc' : ∀ a, bil Q y a = 0 → Q a = 0 := fun a ha => by
    by_contra h
    exact hcon a h ha
  have hww : ∀ a b : V, bil Q y a = 0 → bil Q y b = 0 → bil Q a b = 0 := by
    intro a b ha hb
    have hab : bil Q y (a + b) = 0 := by rw [bil_add_right, ha, hb, add_zero]
    have h1 := hc' _ hab
    rw [Q_add, hc' a ha, hc' b hb] at h1
    have : (2 : F) * bil Q a b = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (Invertible.ne_zero 2)
  have hzw : z = c • y + (z - c • y) := by abel
  change bil Q w z = 0
  rw [hzw, bil_add_right, bil_smul_right, bil_comm Q w y, hyw, mul_zero, zero_add]
  exact hww w _ hyw hz'

/-- **Witt's theorem in $O^+(V)$**: for $n \ge 2$, vectors with the same non-zero value are carried onto each
other by a rotation. -/
theorem exists_orthPlus_apply [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 2 ≤ finrank F V) {x y : V} (hQ : Q x = Q y) (hQ0 : Q x ≠ 0) : ∃ σ ∈ orthPlus Q, σ x = y := by
  have hy0 : Q y ≠ 0 := hQ ▸ hQ0
  have hσ : ∃ σ ∈ orth Q, σ x = y := by
    by_cases h1 : Q (x - y) = 0
    · have h2 : Q (x + y) ≠ 0 := by
        intro h2
        have h4 : Q (x - y) + Q (x + y) = 4 * Q x := by
          rw [sub_eq_add_neg, Q_add, Q_add, bil_neg_right', QuadraticMap.map_neg, ← hQ]; ring
        rw [h1, h2, zero_add] at h4
        have h4' : (4 : F) ≠ 0 := by
          rw [show (4 : F) = 2 * 2 by norm_num]
          exact mul_ne_zero (Invertible.ne_zero 2) (Invertible.ne_zero 2)
        exact hQ0 ((mul_eq_zero.mp h4.symm).resolve_left h4')
      have hx : symmetry Q (x + y) h2 x = -y := by
        rw [symmetry_apply]
        have : 2 * bil Q x (x + y) / Q (x + y) = 1 := by
          rw [div_eq_one_iff_eq h2, bil_add_right, bil_self, Q_add, ← hQ]; ring
        rw [this, one_smul]; abel
      have hyy : symmetry Q y hy0 y = -y := by
        rw [symmetry_apply, bil_self, show 2 * Q y / Q y = 2 by field_simp]
        module
      refine ⟨symmetry Q y hy0 * symmetry Q (x + y) h2,
        (orth Q).mul_mem (symmetry_mem_orth Q _) (symmetry_mem_orth Q _), ?_⟩
      rw [LinearEquiv.mul_apply, hx, map_neg, hyy, neg_neg]
    · exact ⟨_, symmetry_mem_orth Q h1, symmetry_sub_apply hQ h1⟩
  obtain ⟨σ, hσ, hσx⟩ := hσ
  rcases det_orth_eq Q hV hσ with hd | hd
  · exact ⟨σ, ⟨hσ, MonoidHom.mem_ker.mpr hd⟩, hσx⟩
  · obtain ⟨w, hw, hyw⟩ := exists_Q_ne_zero_perp hV hn hy0
    refine ⟨symmetry Q w hw * σ, ⟨(orth Q).mul_mem (symmetry_mem_orth Q hw) hσ, MonoidHom.mem_ker.mpr ?_⟩, ?_⟩
    · rw [map_mul, det_symmetry, hd]; simp
    · rw [LinearEquiv.mul_apply, hσx]
      exact symmetry_apply_of_bil hw hyw

/-- A lattice $\Lambda$ contains $dL$ for some $d \ne 0$, for every finitely generated $L$. -/
theorem exists_smul_mem {Λ L : Submodule R V} (hΛ : Λ.IsLattice F) (hL : L.FG) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ Λ := by
  classical
  obtain ⟨s, rfl⟩ := hL
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun x hx => by
      rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
      rw [hx, smul_zero]; exact Λ.zero_mem⟩
  | insert a s _ ih =>
    obtain ⟨d₁, hd₁, h₁⟩ := ih
    obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_mem_span (R := R) (S := Λ) (x := a)
      (hΛ.span_eq_top ▸ Submodule.mem_top)
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, fun x hx => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
    obtain ⟨c, z, hz, rfl⟩ := hx
    have e1 : (d₁ * d₂) • (c • a + z) = c • (d₁ • (d₂ • a)) + d₂ • (d₁ • z) := by module
    rw [e1]
    exact Λ.add_mem (Λ.smul_mem _ (Λ.smul_mem _ h₂)) (Λ.smul_mem _ (h₁ z hz))

/-- **Finitely many lattices between $dL$ and $L$** when $R/d$ is finite. -/
theorem finite_between {L : Submodule R V} (hL : L.IsLattice F) {d : R} (hfin : Finite (R ⧸ Ideal.span {d})) :
    {M : Submodule R V | (∀ x ∈ L, d • x ∈ M) ∧ M ≤ L}.Finite := by
  classical
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hL.fg
  set ι := Fin (finrank R L)
  let φ : Submodule R V → Set (ι → R ⧸ Ideal.span {d}) :=
    fun M => {c | ∃ x : L, (x : V) ∈ M ∧ c = fun i => Ideal.Quotient.mk _ (b.repr x i)}
  have key : ∀ M M' : Submodule R V, ((∀ x ∈ L, d • x ∈ M) ∧ M ≤ L) →
      ((∀ x ∈ L, d • x ∈ M') ∧ M' ≤ L) → φ M = φ M' → M ≤ M' := by
    intro M M' hM hM' heq x hx
    have hxL := hM.2 hx
    have hc : (fun i => Ideal.Quotient.mk (Ideal.span {d}) (b.repr ⟨x, hxL⟩ i)) ∈ φ M' :=
      heq ▸ ⟨⟨x, hxL⟩, hx, rfl⟩
    obtain ⟨x', hx'M, hx'⟩ := hc
    have hr : ∀ i, ∃ r : R, r * d = b.repr ⟨x, hxL⟩ i - b.repr x' i := fun i => by
      have := congrFun hx' i
      rw [Ideal.Quotient.eq] at this
      exact (Ideal.mem_span_singleton').mp this
    choose r hr using hr
    let y : L := ∑ i, r i • b i
    have hxy : (⟨x, hxL⟩ : L) = x' + d • y := by
      apply b.repr.injective
      ext i
      simp only [map_add, map_smul, map_sum, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.coe_finset_sum,
        Finset.sum_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul, y]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp only [if_true]
      linear_combination -(hr i)
    have : x = (x' : V) + d • (y : V) := by
      have := congrArg Subtype.val hxy
      simpa using this
    rw [this]
    exact M'.add_mem hx'M (hM'.1 _ y.2)
  haveI : Finite (ι → R ⧸ Ideal.span {d}) := Pi.finite
  refine Set.Finite.of_finite_image (f := φ) (Set.toFinite _) ?_
  intro M hM M' hM' heq
  exact le_antisymm (key M M' hM hM' heq) (key M' M hM' hM heq.symm)

/-- **Theorem 10.3 for an integral lattice** ($\varphi[\Lambda] \subseteq \mathfrak g$). -/
theorem theorem10_3_core [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 1 < finrank F V) (hfin : ∀ d : R, d ≠ 0 → Finite (R ⧸ Ideal.span {d})) {Λ : Submodule R V}
    (hΛ : Λ.IsLattice F) (hnΛ : normIdeal Q Λ ≤ 1) {h : V} (hh : h ∈ Λ) (hQ0 : Q h ≠ 0) :
    ∃ A : Finset (V ≃ₗ[F] V), (∀ α ∈ A, α ∈ orthPlus Q) ∧
      {x | x ∈ Λ ∧ Q x = Q h} = {x | ∃ α ∈ A, ∃ γ ∈ orthLatPlus Q Λ, x = γ (α h)} := by
  classical
  have h1fg : (1 : Submodule R F).FG := ⟨{1}, by simp [Submodule.one_eq_span]⟩
  obtain ⟨L, hΛL, hL⟩ := Dedekind.exists_isMaximal_ge Q hV h1fg hΛ hnΛ
  obtain ⟨d, hd0, hdL⟩ := exists_smul_mem hΛ hL.1.fg
  have hS := finite_between (R := R) (F := F) hL.1 (hfin d hd0)
  set S := {M : Submodule R V | (∀ x ∈ L, d • x ∈ M) ∧ M ≤ L} with hSdef
  set XL := {x : V | x ∈ L ∧ Q x = Q h} with hXL
  -- the ideals `φ(x, L)` lie between `b/2 𝔤` and `𝔤/2`
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) ((2 * Q h)⁻¹)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have h2 : (2 : F) ≠ 0 := Invertible.ne_zero 2
  have hbF : algebraMap R F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hb0
  have hab' : algebraMap R F b * (1 / 2) = algebraMap R F a * Q h := by
    have := hab
    rw [div_eq_iff hbF] at this
    rw [this]; field_simp
  set J0 : Submodule R F := Submodule.span R {(1 / 2 : F)} with hJ0def
  have hJ0 : J0.IsLattice F := by
    refine ⟨fg_span_singleton _, eq_top_iff.mpr fun x _ => ?_⟩
    have hmem : (1 / 2 : F) ∈ Submodule.span F (J0 : Set F) :=
      Submodule.subset_span (Submodule.mem_span_singleton_self _)
    have : x = (2 * x) • (1 / 2 : F) := by rw [smul_eq_mul]; field_simp
    rw [this]; exact Submodule.smul_mem _ _ hmem
  have hbound : ∀ x ∈ XL, (∀ c ∈ J0, b • c ∈ phiIdeal Q x L) ∧ phiIdeal Q x L ≤ J0 := by
    rintro x ⟨hxL, hQx⟩
    constructor
    · intro c hc
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hc
      rw [smul_comm]
      refine Submodule.smul_mem _ _ ?_
      rw [Algebra.smul_def, hab', ← hQx, ← bil_self, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (bil_mem_phiIdeal (Q := Q) hxL)
    · rw [phiIdeal, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨r, hr⟩ := two_bil_int hL.2.1 hxL hy
      refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
      rw [Algebra.smul_def, hr]; field_simp
  have hIfin : ((fun x => phiIdeal Q x L) '' XL).Finite :=
    (finite_between (R := R) (F := F) (V := F) hJ0 (hfin b hb0)).subset (by
      rintro _ ⟨x, hx, rfl⟩; exact hbound x hx)
  let rep : Submodule R F → V := fun J => if H : ∃ x ∈ XL, phiIdeal Q x L = J then H.choose else 0
  have hrep : ∀ J ∈ (fun x => phiIdeal Q x L) '' XL, rep J ∈ XL ∧ phiIdeal Q (rep J) L = J := by
    rintro J ⟨x, hx, rfl⟩
    have H : ∃ y ∈ XL, phiIdeal Q y L = phiIdeal Q x L := ⟨x, hx, rfl⟩
    simp only [rep, dif_pos H]
    exact H.choose_spec
  let T : Finset V := hIfin.toFinset.image rep
  have hT : ∀ t ∈ T, t ∈ XL := by
    intro t ht
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp ht
    exact (hrep J (hIfin.mem_toFinset.mp hJ)).1
  have horbit : ∀ x ∈ XL, ∃ t ∈ T, ∃ σ ∈ orthLat Q L, σ t = x := by
    intro x hx
    have hJ : phiIdeal Q x L ∈ (fun x => phiIdeal Q x L) '' XL := ⟨x, hx, rfl⟩
    obtain ⟨⟨htL, hQt⟩, hφ⟩ := hrep _ hJ
    obtain ⟨σ, hσ, hσt⟩ := exists_orthLat_of_phi hV hL (hQt.trans hx.2.symm) (by rw [hQt]; exact hQ0) hφ
    exact ⟨_, Finset.mem_image.mpr ⟨_, hIfin.mem_toFinset.mpr hJ, rfl⟩, σ, hσ, hσt⟩
  -- coset representatives
  let g : Submodule R V → V ≃ₗ[F] V := fun M =>
    if H : ∃ σ ∈ orthLat Q L, OMeara.latMap σ⁻¹ Λ = M then H.choose else 1
  have hg : ∀ M, g M ∈ orthLat Q L := by
    intro M
    by_cases H : ∃ σ ∈ orthLat Q L, OMeara.latMap σ⁻¹ Λ = M
    · simp only [g, dif_pos H]; exact H.choose_spec.1
    · simp only [g, dif_neg H]; exact (orthLat Q L).one_mem
  let Sg : Finset (V ≃ₗ[F] V) := hS.toFinset.image g
  have hmemL : ∀ σ ∈ orthLat Q L, ∀ x ∈ L, σ x ∈ L := fun σ hσ x hx => by
    rw [← hσ.2]; exact ⟨x, hx, rfl⟩
  have hMS : ∀ σ ∈ orthLat Q L, OMeara.latMap σ⁻¹ Λ ∈ S := by
    intro σ hσ
    have hσi := (orthLat Q L).inv_mem hσ
    refine ⟨fun x hx => ⟨d • σ x, hdL _ (hmemL σ hσ x hx), ?_⟩, fun x hx => ?_⟩
    · change σ⁻¹ (d • σ x) = d • x
      rw [← algebraMap_smul F d (σ x), map_smul, ← algebraMap_smul F d x]
      exact congrArg _ (σ.symm_apply_apply x)
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hmemL _ hσi y (hΛL hy)
  -- a symmetry of `Λ`
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨u, -, hu, hτ⟩ := exists_symmetry_mem_orthLat Q hV hΛ
  set τ := symmetry Q u hu with hτdef
  let P : Finset V := (T ×ˢ Sg).image fun p => p.2 p.1
  let P2 : Finset V := (P ∪ P.image τ).filter (· ∈ Λ)
  have hPQ : ∀ p ∈ P, Q p = Q h := by
    intro p hp
    obtain ⟨⟨t, σ⟩, hts, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ht, hσ⟩ := Finset.mem_product.mp hts
    obtain ⟨M, -, rfl⟩ := Finset.mem_image.mp hσ
    rw [(hg M).1 t]; exact (hT t ht).2
  have hP2 : ∀ p ∈ P2, p ∈ Λ ∧ Q p = Q h := by
    intro p hp
    obtain ⟨hp, hpΛ⟩ := Finset.mem_filter.mp hp
    refine ⟨hpΛ, ?_⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hPQ p hp
    · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
      rw [symmetry_mem_orth Q hu p']; exact hPQ p' hp'
  let αf : V → V ≃ₗ[F] V := fun p => if H : ∃ σ ∈ orthPlus Q, σ h = p then H.choose else 1
  have hαf : ∀ p ∈ P2, αf p ∈ orthPlus Q ∧ αf p h = p := by
    intro p hp
    have H := exists_orthPlus_apply hV (by omega) (hP2 p hp).2.symm hQ0
    simp only [αf, dif_pos H]
    exact H.choose_spec
  refine ⟨P2.image αf, fun α hα => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hα
    exact (hαf p hp).1
  ext x
  constructor
  · rintro ⟨hxΛ, hQx⟩
    obtain ⟨t, htT, σ, hσ, hσt⟩ := horbit x ⟨hΛL hxΛ, hQx⟩
    have hM := hMS σ hσ
    have H : ∃ σ' ∈ orthLat Q L, OMeara.latMap σ'⁻¹ Λ = OMeara.latMap σ⁻¹ Λ := ⟨σ, hσ, rfl⟩
    have hσM : g (OMeara.latMap σ⁻¹ Λ) ∈ orthLat Q L ∧
        OMeara.latMap (g (OMeara.latMap σ⁻¹ Λ))⁻¹ Λ = OMeara.latMap σ⁻¹ Λ := by
      simp only [g, dif_pos H]; exact H.choose_spec
    set σM := g (OMeara.latMap σ⁻¹ Λ) with hσMdef
    set ρ := σ * σM⁻¹ with hρdef
    have hρΛ : OMeara.latMap ρ Λ = Λ := by
      rw [hρdef, latMap_mul, hσM.2, ← latMap_mul, mul_inv_cancel, latMap_one]
    have hρ : ρ ∈ orthLat Q Λ := ⟨(orth Q).mul_mem hσ.1 ((orth Q).inv_mem hσM.1.1), hρΛ⟩
    have hxp : x = ρ (σM t) := by
      rw [hρdef, LinearEquiv.mul_apply, ← hσt]
      congr 1
      exact (σM.symm_apply_apply t).symm
    have hpΛ : σM t ∈ Λ := by
      have hρi := (orthLat Q Λ).inv_mem hρ
      have : ρ⁻¹ x ∈ OMeara.latMap ρ⁻¹ Λ := ⟨x, hxΛ, rfl⟩
      rw [hρi.2, hxp] at this
      simpa using this
    have hpP : σM t ∈ P := Finset.mem_image.mpr ⟨(t, σM), Finset.mem_product.mpr ⟨htT,
      Finset.mem_image.mpr ⟨_, hS.mem_toFinset.mpr hM, rfl⟩⟩, rfl⟩
    rcases det_orth_eq Q hV hρ.1 with hd | hd
    · have hp2 : σM t ∈ P2 := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hpP, hpΛ⟩
      refine ⟨αf (σM t), Finset.mem_image_of_mem _ hp2, ρ, (mem_orthLatPlus_iff Q hρ).mpr hd, ?_⟩
      rw [(hαf _ hp2).2]; exact hxp
    · have hτp : τ (σM t) ∈ Λ := by rw [← hτ.2]; exact ⟨_, hpΛ, rfl⟩
      have hp2 : τ (σM t) ∈ P2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpP), hτp⟩
      refine ⟨αf (τ (σM t)), Finset.mem_image_of_mem _ hp2, ρ * τ,
        (mem_orthLatPlus_iff Q ((orthLat Q Λ).mul_mem hρ hτ)).mpr ?_, ?_⟩
      · rw [map_mul, hd, hτdef, det_symmetry]; simp
      · rw [(hαf _ hp2).2, LinearEquiv.mul_apply, hτdef, symmetry_symmetry]; exact hxp
  · rintro ⟨α, hα, γ, hγ, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hα
    rw [(hαf p hp).2]
    refine ⟨?_, by rw [hγ.1.1 p]; exact (hP2 p hp).2⟩
    rw [← hγ.1.2]; exact ⟨p, (hP2 p hp).1, rfl⟩

/-- **Theorem 10.3 over a Henselian discrete valuation ring** whose quotients $R/d$ ($d \ne 0$) are finite: for a
lattice $\Lambda$ on a regular space of dimension $n > 1$ and $h \in \Lambda$ with $Q(h) \ne 0$,
$\{x \in \Lambda \mid Q(x) = Q(h)\}$ is a finite union of orbits $O^+(\Lambda)\,\alpha h$, $\alpha \in O^+(V)$. -/
theorem theorem10_3_abstract [FiniteDimensional F V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 1 < finrank F V) (hfin : ∀ d : R, d ≠ 0 → Finite (R ⧸ Ideal.span {d})) {Λ : Submodule R V}
    (hΛ : Λ.IsLattice F) {h : V} (hh : h ∈ Λ) (hQ0 : Q h ≠ 0) :
    ∃ A : Finset (V ≃ₗ[F] V), (∀ α ∈ A, α ∈ orthPlus Q) ∧
      {x | x ∈ Λ ∧ Q x = Q h} = {x | ∃ α ∈ A, ∃ γ ∈ orthLatPlus Q Λ, x = γ (α h)} := by
  -- scale `Q` so that `Λ` becomes integral
  have hnfg : (normIdeal Q Λ).FG := FG.of_le (scale_fg Q hΛ.fg) (normIdeal_le_scale Q Λ)
  have hnne : normIdeal Q Λ ≠ ⊥ := by
    intro h0
    have := Q_mem_normIdeal Q hh
    rw [h0, Submodule.mem_bot] at this
    exact hQ0 this
  obtain ⟨c, hc0, hc⟩ := exists_eq_span_singleton hnfg hnne
  set Q' : QuadraticForm F V := c⁻¹ • Q with hQ'def
  have hQ' : ∀ x, Q' x = c⁻¹ * Q x := fun x => rfl
  have hbil : ∀ x y, bil Q' x y = c⁻¹ * bil Q x y := by
    intro x y
    rw [bil_eq_half, bil_eq_half Q, hQ', hQ', hQ']; ring
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hV' : (QuadraticMap.associated Q').Nondegenerate := by
    refine ⟨fun x hx => hV.1 x fun y => ?_, fun y hy => hV.2 y fun x => ?_⟩
    · have := hx y
      change bil Q' x y = 0 at this
      rw [hbil] at this
      exact (mul_eq_zero.mp this).resolve_left hci
    · have := hy x
      change bil Q' x y = 0 at this
      rw [hbil] at this
      exact (mul_eq_zero.mp this).resolve_left hci
  have horth : orth Q' = orth Q := by
    ext σ
    change (∀ x, Q' (σ x) = Q' x) ↔ ∀ x, Q (σ x) = Q x
    simp only [hQ']
    exact ⟨fun H x => mul_left_cancel₀ hci (H x), fun H x => by rw [H x]⟩
  have horthLat : orthLat Q' Λ = orthLat Q Λ := by
    ext σ
    change σ ∈ orth Q' ∧ _ ↔ σ ∈ orth Q ∧ _
    rw [horth]
  have horthPlus : orthPlus Q' = orthPlus Q := by rw [orthPlus, orthPlus, horth]
  have horthLatPlus : orthLatPlus Q' Λ = orthLatPlus Q Λ := by
    rw [orthLatPlus, orthLatPlus, horthLat, horthPlus]
  have hn' : normIdeal Q' Λ ≤ 1 := by
    rw [normIdeal, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : Q x ∈ Submodule.span R {c} := hc ▸ Q_mem_normIdeal Q hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx'
    refine Submodule.mem_one.mpr ⟨r, ?_⟩
    change algebraMap R F r = Q' x
    rw [hQ', ← hr, Algebra.smul_def]; field_simp
  have hQ0' : Q' h ≠ 0 := by rw [hQ']; exact mul_ne_zero hci hQ0
  obtain ⟨A, hA, hset⟩ := theorem10_3_core (Q := Q') hV' hn hfin hΛ hn' hh hQ0'
  refine ⟨A, fun α hα => horthPlus ▸ hA α hα, ?_⟩
  rw [← horthLatPlus, ← hset]
  ext x
  simp only [Set.mem_setOf_eq, hQ']
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩, fun ⟨h1, h2⟩ => ⟨h1, mul_left_cancel₀ hci h2⟩⟩

end DVR

end QuadFormsKB.Shimura2004.Local105

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara Local105 IsDedekindDomain

/-- **Theorem 10.3** (Shimura 2004, p. 94), proved: `Theorem10_3` (for $n > 1$). -/
@[kb "shimura2004" "Thm. 10.3, p. 94 (proved, n > 1)"]
theorem theorem10_3_holds : Theorem10_3 := by
  intro K _ _ v V _ _ _ _ _ inst Q hnd hn1 Λ hΛ h hh hQ0
  have hfin : ∀ d : v.adicCompletionIntegers K, d ≠ 0 →
      Finite (v.adicCompletionIntegers K ⧸ Ideal.span {d}) := by
    intro d hd
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
    rw [Ideal.span_singleton_mul_left_unit u.isUnit]
    exact LocalDensity.DVR.finite_quot_pow ϖ hϖ n
  exact theorem10_3_abstract hnd hn1 hfin hΛ hh hQ0

end QuadFormsKB.Shimura2004
