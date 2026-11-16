/-
# Shimura 2004, Theorem 10.5 (local transitivity for maximal lattices), proved

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 10.5 (printed p. 96).

**Statement** (`Theorem10_5`, `Diophantine.lean`). $F$ the completion of a number field at a finite prime,
$\mathfrak g$ its maximal order, $(V, \varphi)$ nondegenerate of dimension $n > 1$ with (8.1), $L$ a
$\mathfrak g$-maximal lattice. If $\varphi[h] = \varphi[k] \ne 0$ and $\varphi(h, L) = \varphi(k, L)$, then
$k = \gamma h$ with $\gamma \in SO^\varphi(V)$, $\gamma L = L$, except when $n = 2$, $V$ is isotropic and
$\varphi[h] \in 4\varphi(h,L)^2\mathfrak p$; then $k = \alpha h$ with $\alpha \in O^\varphi(V)$, $\alpha L = L$.

**Proof** (uniform in the residue characteristic; the book's proof goes by the dimension of the core subspace).
Write $\varphi(h, L) = c\,\mathfrak g$ and replace $h, k$ by $h/2c$, $k/2c$: then $2B(h, L) = \mathfrak g$
($h$ is *primitive* in $L^\sharp = \{x : 2B(x, L) \subseteq \mathfrak g\}$).
* If $V$ is anisotropic, $O(L) = O(V)$ (91:1), and the symmetry $\tau_{h - k}$ sends $h$ to $k$.
* Otherwise $L = (\mathfrak ge + \mathfrak gf) \perp K$ with $Q(e) = Q(f) = 0$, $2B(e, f) = 1$ (82:20). With the
  symmetries $\tau_{e - f}$ (exchanging $e, f$), $\tau_{e-f}\tau_{e - \varepsilon f}$ ($e \mapsto \varepsilon e$,
  $f \mapsto \varepsilon^{-1}f$) and the Eichler transformations $E_{f,u}$, every primitive $h$ is moved to the
  normal form $h_1 = (Q(h) - Q(z))e + f + z$ with $z \perp e, f$ in $K^\sharp$ (`exists_normalForm`). For two normal
  forms, the orbit lemma (`Local105.exists_isOn_sub_mem`) gives $\sigma \in O(K)$ with $\sigma z - z' \in K$, and
  $E_{e,\, z' - \sigma z}$ finishes.
* Determinant: an element of $O(L)$ of determinant $-1$ fixing $h_1$ is $E_{e,\,z - \rho z}\,\rho$ with $\rho$ from
  `Local105.exists_isOn_det_neg`; for $n = 3$ this needs $2z \in K$, which is where (8.1) enters (the core line is
  $\mathfrak g u$ with $Q(u)$ a unit); for $n = 2$ it is $\tau_{ae - f}$, $a = Q(h_1)$, which needs $a$ to be a
  unit: the exceptional case.

**Proves** (unconditional; standard axioms only)
* `Local105.theorem10_5_abstract`: the theorem over any Henselian discrete valuation ring with $2 \in F^\times$, for
  primitive vectors.
* `theorem10_5_holds : Theorem10_5` (then `localTheorem10_5_holds` in `Local.lean` and
  `localTheorem10_5Core_holds t` in `CoreSplit.lean`).
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Eichler
import QuadFormsKB.Literature.Shimura2004.Diophantine
import QuadFormsKB.Literature.OMeara.Sec82Radical
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import QuadFormsKB.Citation

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004.Local105

open QuadFormsKB.OMeara

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {Q : QuadraticForm F V}

/-- A symmetry is self-adjoint: $B(\tau_u x, y) = B(x, \tau_u y)$. -/
theorem bil_symmetry_left {u : V} (hu : Q u ≠ 0) (x y : V) :
    bil Q (symmetry Q u hu x) y = bil Q x (symmetry Q u hu y) := by
  conv_lhs => rw [← symmetry_symmetry Q hu y]
  exact bil_map_eq (symmetry_mem_orth Q hu) x _

theorem isUnit_neg_one_add {x : R} (hx : x ∈ maximalIdeal R) : IsUnit (-1 + x) := by
  by_contra h
  have h1 : -1 + x ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h
  have h2 : (1 : R) ∈ maximalIdeal R := by
    have := (maximalIdeal R).sub_mem hx h1
    rwa [show x - (-1 + x) = 1 by ring] at this
  exact (maximalIdeal R).ne_top_iff_one.mp (maximalIdeal.isMaximal R).ne_top h2

theorem unit_inv_int (u : Rˣ) : (algebraMap R F u)⁻¹ ∈ (algebraMap R F).range :=
  ⟨(u⁻¹ : Rˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩

variable [FiniteDimensional F V]

section Split

variable {L : Submodule R V} {e f : V} {K : Submodule R V}

/-- **Step 1 of the normal form**: some unit of $L$ makes the coefficient $2B(\cdot, e)$ a unit. -/
theorem exists_unit_coeff (hn : normIdeal Q L ≤ 1) (hs : HypSplit (Q := Q) ⊤ L e f K) {h : V}
    (hd : IsDual Q L h) (hp : ∃ y ∈ L, 2 * bil Q h y = 1) :
    ∃ σ ∈ orthLat Q L, ∃ u : Rˣ, 2 * bil Q (σ h) e = algebraMap R F u := by
  obtain ⟨b, hb⟩ := hd e hs.he
  obtain ⟨a, ha⟩ := hd f hs.hf
  have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
  have hff : bil Q f f = 0 := by rw [bil_self]; exact hs.Qf
  by_cases hbu : IsUnit b
  · exact ⟨1, (orthLat Q L).one_mem, hbu.unit, by rw [IsUnit.unit_spec, hb]; rfl⟩
  by_cases hau : IsUnit a
  · have hQef : Q (e - f) = -1 := by
      rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg, hs.Qe, hs.Qf]
      linear_combination -hs.bef
    have hQef0 : Q (e - f) ≠ 0 := by rw [hQef]; exact neg_ne_zero.mpr one_ne_zero
    refine ⟨symmetry Q (e - f) hQef0, symmetry_mem_orthLat_of_inv hn (L.sub_mem hs.he hs.hf) hQef0
      (by rw [hQef]; exact ⟨-1, by simp⟩), hau.unit, ?_⟩
    rw [symmetry_apply, hQef, bil_sub_left, bil_smul_left, bil_sub_right, bil_sub_left, hee,
      bil_comm Q f e]
    change _ = algebraMap R F a
    rw [ha]
    field_simp
    linear_combination (-(bil Q h e - bil Q h f)) * hs.bef
  -- both coefficients are non-units: an Eichler transformation `E_{f,k}`
  obtain ⟨y, hyL, hy⟩ := hp
  rw [← hs.split.sup_eq] at hyL
  obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hyL
  obtain ⟨a', b', rfl⟩ := mem_span_pair.mp hj
  obtain ⟨q, hq⟩ := Q_int (hs.hK.2.2.1) hk
  have hkL := hs.K_le hk
  obtain ⟨t, ht⟩ := hd k hkL
  have hke := hs.bil_e_of_mem hk
  have hkf := hs.bil_f_of_mem hk
  have hfk : bil Q f k = 0 := by rw [bil_comm]; exact hkf
  refine ⟨eichler hs.Qf hfk, eichler_mem_orthLat hn hs.Qf hfk hs.hf hkL, ?_⟩
  have hb' : b ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hbu
  have ha' : a ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hau
  have htt : t = 1 - a' * b - b' * a := by
    apply IsFractionRing.injective R F
    rw [map_sub, map_sub, map_one, map_mul, map_mul, hb, ha, ht]
    rw [bil_add_right, bil_add_right, bil_rsmul_right, bil_rsmul_right] at hy
    linear_combination hy
  have hx : b + a' * b + b' * a - a * q ∈ maximalIdeal R :=
    (maximalIdeal R).sub_mem (add_mem (add_mem hb' (Ideal.mul_mem_left _ _ hb')) (Ideal.mul_mem_left _ _ ha'))
      (Ideal.mul_mem_right _ _ ha')
  have hunit : IsUnit (b - t - a * q) := by
    have : b - t - a * q = -1 + (b + a' * b + b' * a - a * q) := by rw [htt]; ring
    rw [this]; exact isUnit_neg_one_add hx
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, eichler_apply, map_sub, map_sub, map_mul, hb, ha, ht, hq]
  simp only [bil_sub_left, bil_add_left, bil_smul_left, hke]
  linear_combination (-(2 * bil Q h k + 2 * bil Q h f * Q k)) * hs.bfe

/-- **Step 2 of the normal form**: $\tau_{e-f}\tau_{e-\varepsilon f}$ ($e \mapsto \varepsilon e$,
$f \mapsto \varepsilon^{-1}f$) normalizes the coefficient to $1$. -/
theorem exists_coeff_one (hn : normIdeal Q L ≤ 1) (hs : HypSplit (Q := Q) ⊤ L e f K) {h : V}
    (hd : IsDual Q L h) (hp : ∃ y ∈ L, 2 * bil Q h y = 1) :
    ∃ σ ∈ orthLat Q L, 2 * bil Q (σ h) e = 1 := by
  obtain ⟨σ₁, hσ₁, u, hu⟩ := exists_unit_coeff hn hs hd hp
  set c : F := algebraMap R F u with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr u.ne_zero
  have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
  have hff : bil Q f f = 0 := by rw [bil_self]; exact hs.Qf
  have hQ1 : Q (e - f) = -1 := by
    rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg, hs.Qe, hs.Qf]
    linear_combination -hs.bef
  have hQc : Q (e - c • f) = -c := by
    rw [sub_eq_add_neg, Q_add, bil_neg_right', ← neg_smul, QuadraticMap.map_smul, bil_smul_right, hs.Qe, hs.Qf]
    simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
    linear_combination (-c) * hs.bef
  have h10 : Q (e - f) ≠ 0 := by rw [hQ1]; exact neg_ne_zero.mpr one_ne_zero
  have hc0' : Q (e - c • f) ≠ 0 := by rw [hQc]; exact neg_ne_zero.mpr hc0
  have hcint : c ∈ (algebraMap R F).range := ⟨u, rfl⟩
  have hm1 : symmetry Q (e - f) h10 ∈ orthLat Q L :=
    symmetry_mem_orthLat_of_inv hn (L.sub_mem hs.he hs.hf) h10 (by rw [hQ1]; exact ⟨-1, by simp⟩)
  have hm2 : symmetry Q (e - c • f) hc0' ∈ orthLat Q L := by
    refine symmetry_mem_orthLat_of_inv hn (L.sub_mem hs.he (smul_mem_of_int hcint hs.hf)) hc0' ?_
    rw [hQc, inv_neg]
    exact neg_mem (unit_inv_int u)
  refine ⟨symmetry Q (e - f) h10 * symmetry Q (e - c • f) hc0' * σ₁,
    (orthLat Q L).mul_mem ((orthLat Q L).mul_mem hm1 hm2) hσ₁, ?_⟩
  -- `τ_{e-f} e = f` and `τ_{e - c f} f = c⁻¹ e`
  have h1e : symmetry Q (e - f) h10 e = f := by
    rw [symmetry_apply, hQ1, bil_sub_right, hee]
    have : 2 * (0 - bil Q e f) / -1 = 1 := by rw [div_neg, div_one]; linear_combination hs.bef
    rw [this, one_smul]; abel
  have h2f : symmetry Q (e - c • f) hc0' f = c⁻¹ • e := by
    rw [symmetry_apply, hQc, bil_sub_right, bil_smul_right, hff, bil_comm Q f e]
    have : 2 * (bil Q e f - c * 0) / -c = -c⁻¹ := by
      field_simp; linear_combination -hs.bef
    rw [this, neg_smul, sub_neg_eq_add, smul_sub, smul_smul, inv_mul_cancel₀ hc0, one_smul]; abel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, bil_symmetry_left, h1e, bil_symmetry_left, h2f,
    bil_smul_right]
  rw [mul_left_comm, hu, inv_mul_cancel₀ hc0]

/-- **The normal form**: a primitive $h \in L^\sharp$ is moved by a unit of $L$ to $\alpha e + f + z$ with
$z \perp e, f$, $z \in K^\sharp$ and $\alpha = 2B(\sigma h, f) \in \mathfrak o$. -/
theorem exists_normalForm (hn : normIdeal Q L ≤ 1) (hs : HypSplit (Q := Q) ⊤ L e f K) {h : V}
    (hd : IsDual Q L h) (hp : ∃ y ∈ L, 2 * bil Q h y = 1) :
    ∃ σ ∈ orthLat Q L, ∃ z ∈ perpIn Q ⊤ (span R {e, f}), IsDual Q K z ∧
      σ h = (2 * bil Q (σ h) f) • e + f + z := by
  obtain ⟨σ, hσ, h1⟩ := exists_coeff_one hn hs hd hp
  have hd' := hd.map hσ
  refine ⟨σ, hσ, σ h - (2 * bil Q (σ h) f) • e - (2 * bil Q (σ h) e) • f, ?_, ?_, ?_⟩
  · exact hs.sub_mem_perp mem_top mem_top mem_top
  · exact hs.isDual_comp hd'
  · rw [h1, one_smul]; abel

end Split

/-- The orthogonal complement of a hyperbolic pair has codimension $2$. -/
theorem finrank_perp_add_two {L : Submodule R V} {e f : V} {K : Submodule R V}
    (hs : HypSplit (Q := Q) ⊤ L e f K) : finrank F (perpIn Q ⊤ (span R {e, f})) + 2 = finrank F V := by
  let φ : V →ₗ[F] F × F := LinearMap.prod ((QuadraticMap.associated Q).flip e) ((QuadraticMap.associated Q).flip f)
  have hker : LinearMap.ker φ = perpIn Q ⊤ (span R {e, f}) := by
    ext x
    rw [LinearMap.mem_ker, mem_perpIn_pair]
    simp [φ, bil, Prod.ext_iff]
  have hrange : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, q⟩ -
    have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
    have hff : bil Q f f = 0 := by rw [bil_self]; exact hs.Qf
    refine ⟨(2 * p) • f + (2 * q) • e, ?_⟩
    simp only [φ, LinearMap.prod_apply, LinearMap.flip_apply, Prod.ext_iff, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change 2 * p * bil Q f e + 2 * q * bil Q e e = p ∧ 2 * p * bil Q f f + 2 * q * bil Q e f = q
    rw [hee, hff]
    constructor
    · linear_combination p * hs.bfe
    · linear_combination q * hs.bef
  have := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self, hker] at this
  omega

/-- **(8.1) at $n = 3$**: if $\dim V = 3$ and $L = (\mathfrak ge + \mathfrak gf) \perp K$, then $2z \in K$ for
every $z \perp e, f$ with $2B(z, K) \subseteq \mathfrak g$. -/
theorem two_smul_mem_of_cond81 (hV : (QuadraticMap.associated Q).Nondegenerate) (h81 : Cond81 R Q)
    (h3 : finrank F V = 3) {L : Submodule R V} {e f : V} {K : Submodule R V}
    (hs : HypSplit (Q := Q) ⊤ L e f K) {z : V} (hz : z ∈ perpIn Q ⊤ (span R {e, f})) (hzd : IsDual Q K z) :
    (2 : F) • z ∈ K := by
  classical
  set W₁ := perpIn Q ⊤ (span R {e, f}) with hW₁
  have hW1 : finrank F W₁ = 1 := by
    have h := finrank_perp_add_two hs
    rw [← hW₁] at h
    omega
  have hWreg : ∀ v ∈ W₁, (∀ v' ∈ W₁, bil Q v v' = 0) → v = 0 :=
    hs.perp_reg mem_top mem_top fun w _ hw => hV.1 w fun w' => hw w' mem_top
  -- `W₁` is anisotropic
  have haniso : ∀ w ∈ W₁, Q w = 0 → w = 0 := by
    intro w hw hQw
    by_contra hw0
    refine hw0 (hWreg w hw fun w' hw' => ?_)
    have hne : (⟨w, hw⟩ : W₁) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : W₁) hne).mp hW1 ⟨w', hw'⟩
    have : w' = c • w := by have := congrArg Subtype.val hc; simpa using this.symm
    rw [this, bil_smul_right, bil_self, hQw, mul_zero]
  -- a maximal vector `u₀` of `K`
  obtain ⟨⟨x, hxW⟩, hx0⟩ := finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank F W₁)
  have hx0' : x ≠ 0 := fun h => hx0 (by ext; simp [h])
  obtain ⟨u₀, hu₀, t, ht, hxt⟩ := exists_isMaxVec_smul (F := F) hs.hK.1 hx0' (by rw [hs.hK.2.1]; exact hxW)
  have hu₀K := hu₀.1
  have hu₀W := hs.mem_perp_of_mem hu₀K
  have hu₀0 : u₀ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hxt
    exact hx0' hxt
  have hQu₀ : Q u₀ ≠ 0 := fun h => hu₀0 (haniso u₀ hu₀W h)
  have hu₀e : bil Q u₀ e = 0 := hs.bil_e_of_mem hu₀K
  have hu₀f : bil Q u₀ f = 0 := hs.bil_f_of_mem hu₀K
  have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
  have hff : bil Q f f = 0 := by rw [bil_self]; exact hs.Qf
  -- the basis `e, f, u₀`
  let v : Fin 3 → V := ![e, f, u₀]
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h1 : bil Q (g 0 • e + g 1 • f + g 2 • u₀) e = 0 := by rw [hg]; simp [bil]
    have h2 : bil Q (g 0 • e + g 1 • f + g 2 • u₀) f = 0 := by rw [hg]; simp [bil]
    rw [bil_add_left, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left, hee, hu₀e,
      bil_comm Q f e] at h1
    rw [bil_add_left, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left, hff, hu₀f] at h2
    have hg1 : g 1 = 0 := by linear_combination 2 * h1 - g 1 * hs.bef
    have hg0 : g 0 = 0 := by linear_combination 2 * h2 - g 0 * hs.bef
    rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
    have hg2 : g 2 = 0 := by
      by_contra h
      exact hu₀0 ((smul_eq_zero.mp hg).resolve_left h)
    intro i; fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  let b : Basis (Fin 3) F V := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h3])
  let b' : Basis (Fin (finrank F V)) F V := b.reindex (finCongr h3.symm)
  obtain ⟨ε, c, hc0, hdet⟩ := h81 (by rw [h3]; exact ⟨1, rfl⟩) b'
  have hdetb : (gram Q b').det = (gram Q v).det := by
    have : gram Q b' = (gram Q b).reindex (finCongr h3.symm) (finCongr h3.symm) := by
      ext i j; simp [gram, b']
    rw [this, Matrix.det_reindex_self]
    congr 2
    ext i j
    simp [gram, b, v]
  have hv : (gram Q v).det = -(bil Q e f) ^ 2 * Q u₀ := by
    rw [Matrix.det_fin_three]
    simp only [gram, Matrix.of_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, bil_self, hs.Qe, hs.Qf, bil_comm Q f e]
    rw [bil_comm Q e u₀, bil_comm Q f u₀, hu₀e, hu₀f]
    ring
  -- `Q u₀ = (-ε) (2c)²`
  set d : F := 2 * c with hd
  have hd0 : d ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hQd : Q u₀ = algebraMap R F (-ε : Rˣ) * d ^ 2 := by
    rw [hdetb, hv] at hdet
    rw [hd, Units.val_neg, map_neg]
    linear_combination (-4 : F) * hdet - Q u₀ * (2 * bil Q e f + 1) * hs.bef
  have hdinv : d⁻¹ ∈ (algebraMap R F).range := by
    refine hu₀.2 _ ((mem_iff_int haniso hs.hK (W₁.smul_mem _ hu₀W)).mpr ?_)
    rw [Q_smul, hQd]
    have : d⁻¹ ^ 2 * (algebraMap R F (-ε : Rˣ) * d ^ 2) = algebraMap R F (-ε : Rˣ) := by field_simp
    rw [this]; exact ⟨_, rfl⟩
  have hQint := Q_int hs.hK.2.2.1 hu₀K
  have hQinv : (Q u₀)⁻¹ ∈ (algebraMap R F).range := by
    rw [hQd, mul_inv, ← inv_pow]
    exact mul_mem (unit_inv_int _) (pow_mem hdinv 2)
  -- `z = s u₀`
  have hne : (⟨u₀, hu₀W⟩ : W₁) ≠ 0 := fun h => hu₀0 (congrArg Subtype.val h)
  obtain ⟨s, hsz⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u₀, hu₀W⟩ : W₁) hne).mp hW1 ⟨z, hz⟩
  have hzs : z = s • u₀ := by have := congrArg Subtype.val hsz; simpa using this.symm
  have h2s : 2 * s ∈ (algebraMap R F).range := by
    have := hzd u₀ hu₀K
    rw [hzs, bil_smul_left, bil_self] at this
    have h' : 2 * s = 2 * (s * Q u₀) * (Q u₀)⁻¹ := by field_simp
    rw [h']
    exact mul_mem this hQinv
  rw [hzs, smul_smul]
  exact smul_mem_of_int h2s hu₀K

section Main

variable {L : Submodule R V} {e f : V} {K : Submodule R V}

theorem inv_mul_apply_eq {σ τ : V ≃ₗ[F] V} {x y : V} (h : τ x = σ y) : (σ⁻¹ * τ) x = y := by
  rw [LinearEquiv.mul_apply, h]
  exact σ.symm_apply_apply y

/-- **Transitivity on primitive vectors, isotropic case**: two primitive vectors of $L^\sharp$ with the same value
are carried onto each other by a unit of $L$. -/
theorem exists_orthLat_of_split (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : normIdeal Q L ≤ 1)
    (hs : HypSplit (Q := Q) ⊤ L e f K) {h k : V} (hdh : IsDual Q L h) (hdk : IsDual Q L k)
    (hph : ∃ y ∈ L, 2 * bil Q h y = 1) (hpk : ∃ y ∈ L, 2 * bil Q k y = 1) (hQ : Q h = Q k) :
    ∃ σ ∈ orthLat Q L, σ h = k := by
  obtain ⟨σh, hσh, zh, hzh, hzdh, hh1⟩ := exists_normalForm hn hs hdh hph
  obtain ⟨σk, hσk, zk, hzk, hzdk, hk1⟩ := exists_normalForm hn hs hdk hpk
  set αh := 2 * bil Q (σh h) f with hαhdef
  set αk := 2 * bil Q (σk k) f with hαkdef
  have hαh : αh ∈ (algebraMap R F).range := hdh.map hσh f hs.hf
  have hαk : αk ∈ (algebraMap R F).range := hdk.map hσk f hs.hf
  obtain ⟨-, hzhe, hzhf⟩ := mem_perpIn_pair.mp hzh
  obtain ⟨-, hzke, hzkf⟩ := mem_perpIn_pair.mp hzk
  have hQh : Q h = αh + Q zh := by
    rw [← hσh.1 h, hh1, hs.Q_comb'' hzhe hzhf]
  have hQk : Q k = αk + Q zk := by
    rw [← hσk.1 k, hk1, hs.Q_comb'' hzke hzkf]
  have hdiff : Q zh - Q zk ∈ (algebraMap R F).range := by
    have : Q zh - Q zk = αk - αh := by linear_combination -hQh + hQk + hQ
    rw [this]; exact sub_mem hαk hαh
  have hW₁reg := hs.perp_reg mem_top mem_top fun w _ hw => hV.1 w fun w' => hw w' mem_top
  obtain ⟨σ₃, hσ₃, hσ₃K, hσ₃z⟩ :=
    exists_isOn_sub_mem _ _ rfl hW₁reg K hs.hK zh zk hzh hzk hzdh hzdk hdiff
  set u := zk - σ₃ zh with hudef
  have hu : u ∈ K := by have := K.neg_mem hσ₃z; rwa [neg_sub] at this
  have hue : bil Q e u = 0 := by rw [bil_comm]; exact hs.bil_e_of_mem hu
  have hfu : bil Q f u = 0 := by rw [bil_comm]; exact hs.bil_f_of_mem hu
  have hEL := eichler_mem_orthLat hn hs.Qe hue hs.he (hs.K_le hu)
  refine ⟨σk⁻¹ * (eichler hs.Qe hue * (σ₃ * σh)), (orthLat Q L).mul_mem ((orthLat Q L).inv_mem hσk)
    ((orthLat Q L).mul_mem hEL ((orthLat Q L).mul_mem (hs.orthLat_of_isOn hσ₃ hσ₃K) hσh)), ?_⟩
  apply inv_mul_apply_eq
  have hσ₃zW := hσ₃.2.2 zh hzh
  obtain ⟨-, hze', -⟩ := mem_perpIn_pair.mp hσ₃zW
  have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
  have hσ₃h₁ : σ₃ (σh h) = αh • e + f + σ₃ zh := by
    rw [hh1, map_add, map_add, map_smul, hs.fix_e hσ₃, hs.fix_f hσ₃]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσ₃h₁, eichler_apply, hk1]
  have h2e : 2 * bil Q (αh • e + f + σ₃ zh) e = 1 := by
    rw [bil_add_left, bil_add_left, bil_smul_left, hee, hze']
    linear_combination hs.bfe
  have h2u : bil Q (αh • e + f + σ₃ zh) u = bil Q (σ₃ zh) u := by
    rw [bil_add_left, bil_add_left, bil_smul_left, hue, hfu]; ring
  have hQzk : Q zk = Q zh + 2 * bil Q (σ₃ zh) u + Q u := by
    rw [show zk = σ₃ zh + u by rw [hudef]; abel, Q_add, hσ₃.1]
  have hcoef : αh - (2 * bil Q (σ₃ zh) u + 1 * Q u) = αk := by
    linear_combination -hQh + hQk + hQ + hQzk
  rw [h2e, h2u, one_smul]
  calc αh • e + f + σ₃ zh + u - (2 * bil Q (σ₃ zh) u + 1 * Q u) • e
      = (αh - (2 * bil Q (σ₃ zh) u + 1 * Q u)) • e + f + (σ₃ zh + u) := by module
    _ = αk • e + f + zk := by rw [hcoef, hudef]; congr 1; abel

/-- **A unit of determinant $-1$ fixing a primitive vector**, isotropic case. -/
theorem exists_det_neg_fix (hV : (QuadraticMap.associated Q).Nondegenerate) (h81 : Cond81 R Q)
    (hn : normIdeal Q L ≤ 1) (hs : HypSplit (Q := Q) ⊤ L e f K) {k : V} (hdk : IsDual Q L k)
    (hpk : ∃ y ∈ L, 2 * bil Q k y = 1)
    (hn2 : finrank F V = 2 → ∀ r ∈ maximalIdeal R, algebraMap R F r ≠ Q k) :
    ∃ ρ ∈ orthLat Q L, LinearEquiv.det ρ = -1 ∧ ρ k = k := by
  obtain ⟨σk, hσk, zk, hzk, hzdk, hk1⟩ := exists_normalForm hn hs hdk hpk
  set αk := 2 * bil Q (σk k) f with hαkdef
  have hαk : αk ∈ (algebraMap R F).range := hdk.map hσk f hs.hf
  obtain ⟨-, hzke, hzkf⟩ := mem_perpIn_pair.mp hzk
  have hee : bil Q e e = 0 := by rw [bil_self]; exact hs.Qe
  have hff : bil Q f f = 0 := by rw [bil_self]; exact hs.Qf
  -- it suffices to fix the normal form
  suffices H : ∃ ρ ∈ orthLat Q L, LinearEquiv.det ρ = -1 ∧ ρ (σk k) = σk k by
    obtain ⟨ρ, hρ, hdet, hfix⟩ := H
    refine ⟨σk⁻¹ * (ρ * σk), (orthLat Q L).mul_mem ((orthLat Q L).inv_mem hσk)
      ((orthLat Q L).mul_mem hρ hσk), ?_, inv_mul_apply_eq (by rw [LinearEquiv.mul_apply, hfix])⟩
    rw [map_mul, map_mul, map_inv, hdet]
    simp [mul_comm]
  have hfr := finrank_perp_add_two hs
  have hW₁reg := hs.perp_reg mem_top mem_top fun w _ hw => hV.1 w fun w' => hw w' mem_top
  rcases Nat.eq_zero_or_pos (finrank F (perpIn Q ⊤ (span R {e, f}))) with h0 | hpos
  · -- `n = 2`: the symmetry in `αk e - f`
    have hz0 : zk = 0 := by
      have := Submodule.finrank_eq_zero.mp h0
      have hz : zk ∈ (⊥ : Submodule F V) := this ▸ hzk
      exact (Submodule.mem_bot F).mp hz
    obtain ⟨a, ha⟩ := hαk
    have hQk : Q k = αk := by
      rw [← hσk.1 k, hk1, hz0, add_zero, hs.Q_ef]
    have hau : IsUnit a := by
      by_contra hna
      exact hn2 (by omega) a ((mem_maximalIdeal _).mpr hna) (by rw [ha, hQk])
    have hQw : Q (αk • e - f) = -αk := by
      rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg, QuadraticMap.map_smul, hs.Qe, hs.Qf,
        bil_smul_left]
      simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
      linear_combination (-αk) * hs.bef
    have hαk0 : αk ≠ 0 := by
      rw [← ha]; exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hau.ne_zero
    have hw0 : Q (αk • e - f) ≠ 0 := by rw [hQw]; exact neg_ne_zero.mpr hαk0
    refine ⟨symmetry Q (αk • e - f) hw0, ?_, det_symmetry Q hw0, ?_⟩
    · refine symmetry_mem_orthLat_of_inv hn (L.sub_mem (smul_mem_of_int ⟨a, ha⟩ hs.he) hs.hf) hw0 ?_
      rw [hQw, inv_neg, ← ha]
      exact neg_mem (unit_inv_int hau.unit)
    · refine symmetry_apply_of_bil hw0 ?_
      rw [hk1, hz0, add_zero, bil_sub_right, bil_add_left, bil_add_left, bil_smul_right, bil_smul_right,
        bil_smul_left, bil_smul_left, hee, hff, bil_comm Q f e]
      ring
  · -- `n ≥ 3`: the determinant lemma on `W₁`, then an Eichler transformation
    have h1 : finrank F (perpIn Q ⊤ (span R {e, f})) = 1 → (2 : F) • zk ∈ K := fun h1 =>
      two_smul_mem_of_cond81 hV h81 (by omega) hs hzk hzdk
    obtain ⟨ρ₂, hρ₂, hρ₂K, hdet₂, hρ₂z⟩ := exists_isOn_det_neg hW₁reg hpos hs.hK hzk hzdk h1
    set u := zk - ρ₂ zk with hudef
    have hu : u ∈ K := by have := K.neg_mem hρ₂z; rwa [neg_sub] at this
    have hue : bil Q e u = 0 := by rw [bil_comm]; exact hs.bil_e_of_mem hu
    have hfu : bil Q f u = 0 := by rw [bil_comm]; exact hs.bil_f_of_mem hu
    refine ⟨eichler hs.Qe hue * ρ₂, (orthLat Q L).mul_mem (eichler_mem_orthLat hn hs.Qe hue hs.he (hs.K_le hu))
      (hs.orthLat_of_isOn hρ₂ hρ₂K), ?_, ?_⟩
    · rw [map_mul, det_eichler hV, hdet₂, one_mul]
    · have hρzW := hρ₂.2.2 zk hzk
      obtain ⟨-, hze', -⟩ := mem_perpIn_pair.mp hρzW
      have hρk₁ : ρ₂ (σk k) = αk • e + f + ρ₂ zk := by
        rw [hk1, map_add, map_add, map_smul, hs.fix_e hρ₂, hs.fix_f hρ₂]
      rw [LinearEquiv.mul_apply, hρk₁, eichler_apply]
      conv_rhs => rw [hk1]
      have h2e : 2 * bil Q (αk • e + f + ρ₂ zk) e = 1 := by
        rw [bil_add_left, bil_add_left, bil_smul_left, hee, hze']
        linear_combination hs.bfe
      have h2u : bil Q (αk • e + f + ρ₂ zk) u = bil Q (ρ₂ zk) u := by
        rw [bil_add_left, bil_add_left, bil_smul_left, hue, hfu]; ring
      have hQz : Q zk = Q zk + 2 * bil Q (ρ₂ zk) u + Q u := by
        conv_lhs => rw [show zk = ρ₂ zk + u by rw [hudef]; abel]
        rw [Q_add, hρ₂.1]
      rw [h2e, h2u, one_smul]
      calc αk • e + f + ρ₂ zk + u - (2 * bil Q (ρ₂ zk) u + 1 * Q u) • e
          = (αk - (2 * bil Q (ρ₂ zk) u + 1 * Q u)) • e + f + (ρ₂ zk + u) := by module
        _ = αk • e + f + zk := by
          rw [show 2 * bil Q (ρ₂ zk) u + 1 * Q u = 0 by linear_combination -hQz, sub_zero, hudef]
          congr 1; abel

/-- The symmetry $\tau_{h-k}$ sends $h$ to $k$ when $Q(h) = Q(k)$, $Q(h - k) \ne 0$. -/
theorem symmetry_sub_apply {h k : V} (hQ : Q h = Q k) (h0 : Q (h - k) ≠ 0) : symmetry Q (h - k) h0 h = k := by
  rw [symmetry_apply]
  have hQd : Q (h - k) = 2 * Q h - 2 * bil Q h k := by
    rw [sub_eq_add_neg, Q_add, bil_neg_right', QuadraticMap.map_neg, ← hQ]; ring
  have : 2 * bil Q h (h - k) / Q (h - k) = 1 := by
    rw [div_eq_one_iff_eq h0, bil_sub_right, bil_self, hQd]; ring
  rw [this, one_smul, sub_sub_cancel]

/-- **Theorem 10.5 for primitive vectors** over a Henselian discrete valuation ring (`R`, `F` as in O'Meara §91):
for $L$ $\mathfrak o$-maximal on a regular space $V$ of dimension $n > 1$ with (8.1), and $h, k \in L^\sharp$ with
$2B(h, L) = 2B(k, L) = \mathfrak o$ and $Q(h) = Q(k)$: $k = \alpha h$ with $\alpha \in O(L)$, and $k = \gamma h$
with $\gamma \in O^+(L)$ unless $n = 2$, $V$ is isotropic and $Q(h) \in \mathfrak p$. -/
theorem theorem10_5_abstract (hV : (QuadraticMap.associated Q).Nondegenerate) (hL : IsMaximal Q 1 L)
    (hn1 : 1 < finrank F V) (h81 : Cond81 R Q) {h k : V} (hdh : IsDual Q L h) (hdk : IsDual Q L k)
    (hph : ∃ y ∈ L, 2 * bil Q h y = 1) (hpk : ∃ y ∈ L, 2 * bil Q k y = 1) (hQ : Q h = Q k) :
    (∃ σ ∈ orthLat Q L, σ h = k) ∧
      ((finrank F V = 2 → (∃ x : V, x ≠ 0 ∧ Q x = 0) → ∀ r ∈ maximalIdeal R, algebraMap R F r ≠ Q h) →
        ∃ σ ∈ orthLatPlus Q L, σ h = k) := by
  have hn : normIdeal Q L ≤ 1 := hL.2.1
  by_cases hiso : ∀ x : V, Q x = 0 → x = 0
  · have horth : orthLat Q L = orth Q := orthLat_eq_orth_of_isMaximal Q hiso hL
    have hσ : ∃ σ ∈ orth Q, σ h = k := by
      by_cases hhk : h = k
      · exact ⟨1, (orth Q).one_mem, by rw [hhk]; rfl⟩
      · have h0 : Q (h - k) ≠ 0 := fun h0 => hhk (sub_eq_zero.mp (hiso _ h0))
        exact ⟨_, symmetry_mem_orth Q h0, symmetry_sub_apply hQ h0⟩
    obtain ⟨σ, hσo, hσh⟩ := hσ
    have hσL : σ ∈ orthLat Q L := horth ▸ hσo
    refine ⟨⟨σ, hσL, hσh⟩, fun _ => ?_⟩
    rcases det_orth_eq Q hV hσo with hd | hd
    · exact ⟨σ, (mem_orthLatPlus_iff Q hσL).mpr hd, hσh⟩
    · obtain ⟨w, -, hw0, hkw⟩ := exists_ne_zero_bil_eq_zero (Q := Q) (W := ⊤) (by rw [finrank_top]; omega) k
      have hQw : Q w ≠ 0 := fun h0 => hw0 (hiso w h0)
      have hτL : symmetry Q w hQw ∈ orthLat Q L := horth ▸ symmetry_mem_orth Q hQw
      refine ⟨symmetry Q w hQw * σ, (mem_orthLatPlus_iff Q ((orthLat Q L).mul_mem hτL hσL)).mpr ?_, ?_⟩
      · rw [map_mul, det_symmetry, hd]; norm_num
      · rw [LinearEquiv.mul_apply, hσh, symmetry_apply_of_bil hQw hkw]
  · push Not at hiso
    obtain ⟨x, hQx, hx0⟩ := hiso
    have hL' : IsMaxIn Q 1 ⊤ L := (isMaxIn_top_iff Q).mpr hL
    obtain ⟨e, f, K, hs⟩ := exists_hypSplit (fun w _ hw => hV.1 w fun w' => hw w' mem_top) hL' mem_top hx0 hQx
    obtain ⟨σ, hσL, hσh⟩ := exists_orthLat_of_split hV hn hs hdh hdk hph hpk hQ
    refine ⟨⟨σ, hσL, hσh⟩, fun hex => ?_⟩
    rcases det_orth_eq Q hV hσL.1 with hd | hd
    · exact ⟨σ, (mem_orthLatPlus_iff Q hσL).mpr hd, hσh⟩
    · obtain ⟨ρ, hρL, hρd, hρk⟩ := exists_det_neg_fix hV h81 hn hs hdk hpk
        (fun h2 r hr => hQ ▸ hex h2 ⟨x, hx0, hQx⟩ r hr)
      refine ⟨ρ * σ, (mem_orthLatPlus_iff Q ((orthLat Q L).mul_mem hρL hσL)).mpr ?_, ?_⟩
      · rw [map_mul, hρd, hd]; norm_num
      · rw [LinearEquiv.mul_apply, hσh, hρk]

end Main

end DVR

end QuadFormsKB.Shimura2004.Local105

/-! ### Theorem 10.5 at the completions of a number field -/

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara Local105 IsDedekindDomain

theorem phiIdeal_eq_map {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] (Q : QuadraticForm F V)
    (h : V) (L : Submodule R V) :
    phiIdeal Q h L = L.map ((QuadraticMap.associated Q h : V →ₗ[F] F).restrictScalars R) := by
  rw [phiIdeal, ← Submodule.span_eq L, ← Submodule.span_image, Submodule.span_eq]
  rfl

/-- An element of the maximal ideal of $\mathfrak o_v$ has valuation $< 1$. -/
theorem valued_lt_one_of_mem_maximalIdeal {K : Type} [Field K] [NumberField K]
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)} {r : v.adicCompletionIntegers K}
    (hr : r ∈ maximalIdeal (v.adicCompletionIntegers K)) : Valued.v (r : v.adicCompletion K) < 1 := by
  have h1 : Valued.v (r : v.adicCompletion K) ≤ 1 := r.2
  refine lt_of_le_of_ne h1 fun heq => ?_
  have hr0 : (r : v.adicCompletion K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact zero_ne_one heq
  have hinv : (r : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, heq, inv_one]
  apply (mem_maximalIdeal _).mp hr
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  simp [hr0]

/-- **Theorem 10.5** (Shimura 2004, p. 96), proved: `Theorem10_5` (with the corrected exceptional clause).
*Proof:* normalize $h$, $k$ by $2c$, $\varphi(h, L) = c\,\mathfrak g$, and apply `Local105.theorem10_5_abstract`. -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (proved)"]
theorem theorem10_5_holds : Theorem10_5 := by
  intro K _ _ v V _ _ _ _ _ inst Q hnd hn1 h81 L hL h k hQ hQ0 hφ
  -- `φ(h, L) = c 𝔤`
  have hhyp : ∀ x : V, x ≠ 0 → phiIdeal Q x L ≠ ⊥ := by
    intro x hx0 h0
    apply hx0
    refine hnd.1 x fun y => ?_
    refine bil_zero_of_mem_span_F Q (fun z hz => ?_) (hL.1.span_eq_top ▸ Submodule.mem_top : y ∈ _)
    have := bil_mem_phiIdeal (Q := Q) (h := x) hz
    rwa [h0, Submodule.mem_bot] at this
  have hh0 : h ≠ 0 := by rintro rfl; exact hQ0 (QuadraticMap.map_zero Q)
  have hfg : (phiIdeal Q h L).FG := by rw [phiIdeal_eq_map]; exact hL.1.fg.map _
  obtain ⟨c, hc0, hc⟩ := exists_eq_span_singleton hfg (hhyp h hh0)
  have hck : phiIdeal Q k L = Submodule.span (v.adicCompletionIntegers K) {c} := hφ ▸ hc
  have gen : ∀ x : V, phiIdeal Q x L = Submodule.span (v.adicCompletionIntegers K) {c} →
      (∃ y ∈ L, bil Q x y = c) ∧ ∀ y ∈ L, ∃ r : v.adicCompletionIntegers K, (r : v.adicCompletion K) * c = bil Q x y := by
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
      exact ⟨r, by rw [← hr, Algebra.smul_def]; rfl⟩
  obtain ⟨⟨y₀, hy₀L, hy₀⟩, hhd⟩ := gen h hc
  obtain ⟨⟨y₁, hy₁L, hy₁⟩, hkd⟩ := gen k hck
  set s : v.adicCompletion K := (2 * c)⁻¹ with hs
  have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hdual : ∀ x : V, (∀ y ∈ L, ∃ r : v.adicCompletionIntegers K, (r : v.adicCompletion K) * c = bil Q x y) →
      IsDual Q L (s • x) := by
    intro x hx y hy
    obtain ⟨r, hr⟩ := hx y hy
    refine ⟨r, ?_⟩
    change (r : v.adicCompletion K) = _
    rw [bil_smul_left, ← hr, hs]
    field_simp
  have hprim : ∀ x y, bil Q x y = c → 2 * bil Q (s • x) y = 1 := by
    intro x y hxy
    rw [bil_smul_left, hxy, hs]
    field_simp
  have hQs : Q (s • h) = Q (s • k) := by rw [Q_smul, Q_smul, hQ]
  obtain ⟨⟨σ, hσL, hσh⟩, hplus⟩ := theorem10_5_abstract hnd hL hn1 h81 (hdual h hhd) (hdual k hkd)
    ⟨y₀, hy₀L, hprim h y₀ hy₀⟩ ⟨y₁, hy₁L, hprim k y₁ hy₁⟩ hQs
  have back : ∀ γ : V ≃ₗ[v.adicCompletion K] V, γ (s • h) = s • k → γ h = k := by
    intro γ hγ
    have : h = (2 * c) • (s • h) := by rw [smul_smul, hs, mul_inv_cancel₀ h2c, one_smul]
    rw [this, map_smul, hγ, smul_smul, hs, mul_inv_cancel₀ h2c, one_smul]
  refine ⟨fun hne => ?_, fun _ => ⟨σ, hσL, back σ hσh⟩⟩
  have hexc : finrank (v.adicCompletion K) V = 2 → (∃ x : V, x ≠ 0 ∧ Q x = 0) →
      ∀ r ∈ maximalIdeal (v.adicCompletionIntegers K), algebraMap _ (v.adicCompletion K) r ≠ Q (s • h) := by
    intro h2 hiso r hr hrQ
    refine hne ⟨h2, hiso, y₀, hy₀L, ?_⟩
    -- `|Q h| = |2c|² |r| < |2c|²`
    have hQh : Q h = (2 * c) ^ 2 * algebraMap _ _ r := by
      rw [hrQ, Q_smul, hs, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 h2c), one_mul]
    rw [hQh, hy₀, map_mul, map_pow]
    have hv0 : Valued.v (2 * c) ≠ 0 := (map_ne_zero _).mpr h2c
    have hlt := valued_lt_one_of_mem_maximalIdeal hr
    calc Valued.v (2 * c) ^ 2 * Valued.v (algebraMap _ (v.adicCompletion K) r)
        < Valued.v (2 * c) ^ 2 * 1 := by
          apply mul_lt_mul_of_pos_left hlt
          exact pow_pos (zero_lt_iff.mpr hv0) 2
      _ = Valued.v (2 * c) ^ 2 := mul_one _
  obtain ⟨γ, hγ, hγh⟩ := hplus hexc
  exact ⟨γ, hγ, back γ hγh⟩

end QuadFormsKB.Shimura2004
