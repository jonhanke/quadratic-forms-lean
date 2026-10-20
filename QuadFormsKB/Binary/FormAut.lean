import QuadFormsKB.Binary.ClassBijection

/-!
# Automorphism groups of binary forms

For a primitive positive definite form $f$ of fundamental discriminant $D < 0$:

* **Proper automorphisms are units:** $\mathrm{Aut}^+(f) = \mathrm{Aut}(f) \cap \mathrm{SL}_2(\mathbb{Z}) \cong \mathbb{Z}[\omega]^\times$
  (`autSLEquivUnits`), so $|\mathrm{Aut}^+(f)| = w$, the number of roots of unity of $K_D$ (`card_autSL`).
* **All automorphisms** (the convention of this repository, $\mathrm{Aut} \subseteq \mathrm{GL}_2(\mathbb{Z})$, the repo's `Siegel.Aut`):
  $|\mathrm{Aut}(f)| = 2w$ if $f$ has an improper automorphism, i.e. $f \sim_{\mathrm{SL}} \bar f$, i.e. $[\mathfrak a_f]^2 = 1$
  (`card_aut`, `sLEquiv_conj_iff`), and $|\mathrm{Aut}(f)| = w$ otherwise.

Sources: Cox, *Primes of the form $x^2 + ny^2$*, §7 (the units of $\mathcal O_K$ and proper
automorphs) [unverified locator]; Buell, *Binary Quadratic Forms*, Ch. 6 [unverified locator]; Zagier,
*Zetafunktionen und quadratische Körper*, §8.
-/

open QuadraticAlgebra NumberField Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF

variable {D : ℤ}

/-- **The proper automorphism group** $\mathrm{Aut}^+(f) = \{\gamma \in \mathrm{Aut}(f) : \det\gamma = 1\}$, the elements of
the repo's $\mathrm{Aut}(f) \subseteq \mathrm{GL}_2(\mathbb{Z})$ (`Siegel.Aut`) of determinant $1$. -/
def AutSL (f : BinQF) : Subgroup (GL (Fin 2) ℤ) := Siegel.Aut f ⊓ (Matrix.GeneralLinearGroup.det).ker

theorem mem_autSL {f : BinQF} {γ : GL (Fin 2) ℤ} :
    γ ∈ AutSL f ↔ γ ∈ Siegel.Aut f ∧ γ.val.det = 1 := by
  rw [AutSL, Subgroup.mem_inf, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- $\gamma \in \mathrm{Aut}(f)$ iff $f \circ \gamma = f$ (`subst`). -/
theorem mem_aut_iff {f : BinQF} {γ : GL (Fin 2) ℤ} :
    γ ∈ Siegel.Aut f ↔ BinQF.subst (γ.val 0 0) (γ.val 0 1) (γ.val 1 0) (γ.val 1 1) f = f :=
  forall_eval_mulVec_iff f f γ.val

/-- The basis $(p\alpha + r\beta, q\alpha + s\beta)$ obtained from $(\alpha, \beta) = (a, k_f - \omega)$ by a matrix. -/
def bα (D : ℤ) (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) : QOrder D := M 0 0 • fα D f + M 1 0 • fβ D f

/-- The second vector of the transformed basis. -/
def bβ (D : ℤ) (f : BinQF) (M : Matrix (Fin 2) (Fin 2) ℤ) : QOrder D := M 0 1 • fα D f + M 1 1 • fβ D f

/-- $a$ and $k_f - \omega$ are $\mathbb{Z}$-linearly independent ($a \neq 0$). -/
theorem coeffs_eq_of {f : BinQF} (ha : f.a ≠ 0) {x y x' y' : ℤ}
    (h : x • fα D f + y • fβ D f = x' • fα D f + y' • fβ D f) : x = x' ∧ y = y' := by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [fα, fβ] at h1 h2
  subst h2
  exact ⟨mul_right_cancel₀ ha (by linarith), rfl⟩

/-- A matrix is determined by the transformed basis. -/
theorem matrix_eq_of_b {f : BinQF} (ha : f.a ≠ 0) {M N : Matrix (Fin 2) (Fin 2) ℤ}
    (h1 : bα D f M = bα D f N) (h2 : bβ D f M = bβ D f N) : M = N := by
  obtain ⟨e00, e10⟩ := coeffs_eq_of ha h1
  obtain ⟨e01, e11⟩ := coeffs_eq_of ha h2
  ext i j; fin_cases i <;> fin_cases j <;> assumption

variable [IsQuadDisc D]

omit [IsQuadDisc D] in
/-- For $D < 0$ every unit of $\mathbb{Z}[\omega]$ has norm $1$. -/
theorem norm_unit_eq_one (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) (u : (QOrder D)ˣ) :
    norm (u : QOrder D) = 1 := by
  have h : norm (u : QOrder D) * norm ((u⁻¹ : (QOrder D)ˣ) : QOrder D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpos := norm_pos_of_neg hD hD4 u.ne_zero
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h' | h'
  · exact h'
  · omega

/-- **Proper automorphisms give units:** if $\gamma \in \mathrm{Aut}^+(f)$ then the transformed basis is
$(u a, u(k_f - \omega))$ for a unit $u$. *Proof:* both bases have form $f$ and span $\mathfrak a_f$, so
$(\alpha')\mathfrak a_f = (a)\mathfrak a_f = (\alpha)\mathfrak a_f$ (`span_mul_formIdeal`); cancel $\mathfrak a_f$ to get
$(\alpha') = (\alpha)$, and $\alpha'(k_f - \omega) = a\beta'$ (`mul_fβ_eq`) gives $\beta' = u\beta$. -/
theorem exists_unit_of_mem_autSL (f : PrimPosForm D) {γ : GL (Fin 2) ℤ} (hγ : γ ∈ AutSL f.1) :
    ∃ u : (QOrder D)ˣ, bα D f.1 γ.val = u * fα D f.1 ∧ bβ D f.1 γ.val = u * fβ D f.1 := by
  obtain ⟨hA, hd⟩ := mem_autSL.mp hγ
  have hsubst := mem_aut_iff.mp hA
  rw [Matrix.det_fin_two] at hd
  have hf := isFormOf_formIdeal f.2.1
  have hf' := hf.subst hd
  rw [hsubst] at hf'
  have ha : f.1.a ≠ 0 := f.a_pos.ne'
  have hn : odet (fα D f.1) (fβ D f.1) ≠ 0 := by rw [odet_fα_fβ f.2.1]; exact ha
  have hn' : odet (bα D f.1 γ.val) (bβ D f.1 γ.val) ≠ 0 := by
    rw [bα, bβ, odet_comb, hd, one_mul]; exact hn
  have hlat : ∀ z, z ∈ formIdeal D f.1 ↔ ∃ x y : ℤ, z = x • bα D f.1 γ.val + y • bβ D f.1 γ.val :=
    fun z => by rw [mem_formIdeal_iff_exists f.2.1, lattice_eq_of_det hd]; rfl
  have k1 := span_mul_formIdeal f.2.1 ha hf' hn' _ hlat
  have k2 := span_mul_formIdeal f.2.1 ha hf hn _ (mem_formIdeal_iff_exists f.2.1)
  have hspan : Ideal.span {bα D f.1 γ.val} = Ideal.span {fα D f.1} := by
    rw [← k2] at k1
    exact mul_right_cancel₀ (formIdeal_ne_bot ha) k1
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  -- `fα * v = bα`
  refine ⟨v, by rw [← hv, mul_comm], ?_⟩
  have e1 : bα D f.1 γ.val * fβ D f.1 = (f.1.a : QOrder D) * bβ D f.1 γ.val := mul_fβ_eq f.2.1 ha hf' hn'
  have e2 := mul_fβ_eq f.2.1 ha hf hn
  refine mul_left_cancel₀ (show ((f.1.a : ℤ) : QOrder D) ≠ 0 by exact_mod_cast ha) ?_
  calc (f.1.a : QOrder D) * bβ D f.1 γ.val = bα D f.1 γ.val * fβ D f.1 := e1.symm
    _ = fα D f.1 * fβ D f.1 * v := by rw [← hv]; ring
    _ = (f.1.a : QOrder D) * (v * fβ D f.1) := by rw [e2]; ring

/-- **Units give proper automorphisms** ($D < 0$): for a unit $u$, $(ua, u(k_f - \omega))$ is a positively oriented basis
of $\mathfrak a_f = u\,\mathfrak a_f$ with form $f$ ($N(u) = 1$), so it is obtained from $(a, k_f - \omega)$ by some
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $f \circ \gamma = f$. -/
theorem exists_autSL_of_unit (hD : D < 0) (f : PrimPosForm D) (u : (QOrder D)ˣ) :
    ∃ γ ∈ AutSL f.1, bα D f.1 γ.val = u * fα D f.1 ∧ bβ D f.1 γ.val = u * fβ D f.1 := by
  have hD4 := (IsQuadDisc.fund (D := D)).1
  have ha : f.1.a ≠ 0 := f.a_pos.ne'
  have hf := isFormOf_formIdeal f.2.1
  have hn : odet (fα D f.1) (fβ D f.1) ≠ 0 := by rw [odet_fα_fβ f.2.1]; exact ha
  have hlat : ∀ z, (∃ x y : ℤ, z = x • fα D f.1 + y • fβ D f.1) ↔
      (∃ x y : ℤ, z = x • ((u : QOrder D) * fα D f.1) + y • ((u : QOrder D) * fβ D f.1)) := by
    intro z
    rw [← mem_formIdeal_iff_exists f.2.1, ← mem_span_mul_formIdeal_iff f.2.1,
      Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul]
  obtain ⟨p, q, r, s, hα, hβ, e, hd⟩ := exists_basis_change hlat hn
  rw [odet_mul, norm_unit_eq_one hD hD4, one_mul] at e
  have hd1 : p * s - q * r = 1 := by
    have : (p * s - q * r) * odet (fα D f.1) (fβ D f.1) = 1 * odet (fα D f.1) (fβ D f.1) := by
      rw [← e, one_mul]
    exact mul_right_cancel₀ hn this
  have h1 := hf.subst hd1
  rw [← hα, ← hβ] at h1
  have h2 := hf.mul (u : QOrder D)
  have heq : BinQF.subst p q r s f.1 = f.1 := h1.unique h2 (by
    rw [odet_mul, norm_unit_eq_one hD hD4, one_mul]; exact hn)
  refine ⟨glOf p q r s (by rw [hd1]; norm_num), mem_autSL.mpr ⟨mem_aut_iff.mpr ?_, ?_⟩, ?_, ?_⟩
  · simpa using heq
  · simp [Matrix.det_fin_two_of, hd1]
  · simp [bα, hα]
  · simp [bβ, hβ]

/-- **$\mathrm{Aut}^+(f) \cong \mathbb{Z}[\omega]^\times$** ($D < 0$ fundamental, $f$ primitive positive definite of
discriminant $D$): $\gamma \mapsto u$ with $\gamma$ acting on the basis $(a, k_f - \omega)$ of $\mathfrak a_f$ as multiplication by
$u$. Source: Cox, §7 (proper automorphs and units) [unverified locator]; Buell, Ch. 6 [unverified locator]. -/
@[kb "buell1989" "Ch. 6 [unverified locator]"]
noncomputable def autSLEquivUnits (hD : D < 0) (f : PrimPosForm D) : AutSL f.1 ≃ (QOrder D)ˣ where
  toFun γ := Classical.choose (exists_unit_of_mem_autSL f γ.2)
  invFun u := ⟨Classical.choose (exists_autSL_of_unit hD f u),
    (Classical.choose_spec (exists_autSL_of_unit hD f u)).1⟩
  left_inv γ := by
    have hu := Classical.choose_spec (exists_unit_of_mem_autSL f γ.2)
    set u := Classical.choose (exists_unit_of_mem_autSL f γ.2)
    have hγ := (Classical.choose_spec (exists_autSL_of_unit hD f u)).2
    apply Subtype.ext; apply Units.ext
    exact matrix_eq_of_b f.a_pos.ne' (hγ.1.trans hu.1.symm) (hγ.2.trans hu.2.symm)
  right_inv u := by
    have hγ := (Classical.choose_spec (exists_autSL_of_unit hD f u)).2
    have hu := Classical.choose_spec (exists_unit_of_mem_autSL f
      (Classical.choose_spec (exists_autSL_of_unit hD f u)).1)
    apply Units.ext
    have h := hu.1.symm.trans hγ.1
    have hne : fα D f.1 ≠ 0 := fun h0 => f.a_pos.ne' (by simpa [fα] using congrArg QuadraticAlgebra.re h0)
    exact mul_right_cancel₀ hne h

/-- **The units of $\mathbb{Z}[\omega]$ are the roots of unity of $K_D$** for $D < 0$ (unit rank $0$):
$\#\mathbb{Z}[\omega]^\times = w$ (`NumberField.Units.torsionOrder`). -/
@[kb "marcus1977" "Ch. 5"]
theorem card_units_eq_torsionOrder (hD : D < 0) :
    Nat.card (QOrder D)ˣ = NumberField.Units.torsionOrder (QField D) := by
  classical
  rw [Nat.card_congr (Units.mapEquiv (orderEquiv D).toRingEquiv.toMulEquiv).toEquiv,
    NumberField.Units.torsionOrder]
  have hrank : NumberField.Units.rank (QField D) = 0 := by
    rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      nrRealPlaces_of_neg hD, nrComplexPlaces_of_neg hD]
  have htop : NumberField.Units.torsion (QField D) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨⟨ζ, e⟩, hx, -⟩ := NumberField.Units.exist_unique_eq_mul_prod (QField D) x
    have : IsEmpty (Fin (NumberField.Units.rank (QField D))) := by rw [hrank]; infer_instance
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hx
    rw [hx]; exact ζ.2
  rw [htop, Subgroup.card_top]

/-- **$|\mathrm{Aut}^+(f)| = w$** ($D < 0$ fundamental): the number of proper automorphisms of a primitive positive
definite form of discriminant $D$ is the number of roots of unity in $K_D$. -/
@[kb "zagier1981" "§8 [unverified locator]"]
theorem card_autSL (hD : D < 0) (f : PrimPosForm D) :
    Nat.card (AutSL f.1) = NumberField.Units.torsionOrder (QField D) := by
  rw [Nat.card_congr (autSLEquivUnits hD f), card_units_eq_torsionOrder hD]

/-! ### Improper automorphisms and $|\mathrm{Aut}(f)|$ in $\mathrm{GL}_2(\mathbb{Z})$ -/

omit [IsQuadDisc D] in
/-- **$f$ has an improper automorphism iff $\bar f \sim_{\mathrm{SL}} f$:** $f \circ \gamma = f$ with $\det\gamma = -1$ iff
$\bar f \circ \sigma = f$ with $\sigma = \operatorname{diag}(1, -1)\gamma$, $\det\sigma = 1$. Source: Cox, §2.A [unverified locator]. -/
@[kb "cox2013" "§2.A [unverified locator]"]
theorem exists_improper_iff (f : BinQF) :
    (∃ γ ∈ Siegel.Aut f, γ.val.det = -1) ↔ SLEquiv (conjForm f) f := by
  rw [sLEquiv_iff]
  constructor
  · rintro ⟨γ, hγ, hd⟩
    rw [mem_aut_iff] at hγ
    rw [Matrix.det_fin_two] at hd
    refine ⟨γ.val 0 0, γ.val 0 1, -γ.val 1 0, -γ.val 1 1, by linarith, ?_⟩
    conv_rhs => rw [← hγ]
    refine ext_abc ?_ ?_ ?_ <;> simp [conjForm]
    ring
  · rintro ⟨p, q, r, s, hd, h⟩
    refine ⟨glOf p q (-r) (-s) (by linear_combination (p * s - q * r + 1) * hd), mem_aut_iff.mpr ?_, ?_⟩
    · conv_rhs => rw [← h]
      refine ext_abc ?_ ?_ ?_ <;> simp [conjForm]
      ring
    · simp [Matrix.det_fin_two_of]; linarith

/-- **An improper automorphism exists iff $[\mathfrak a_f]$ has order $\le 2$** ($D < 0$ fundamental): $\bar f \sim_{\mathrm{SL}} f$
iff $[\mathfrak a_f]^{-1} = [\mathfrak a_f]$ (`idealClass_conj`). These are the forms in the ambiguous classes. -/
@[kb "cox2013" "§2.A; §7.C [unverified locator]"]
theorem sLEquiv_conj_iff (hD : D < 0) (f : PrimPosForm D) :
    SLEquiv (conjForm f.1) f.1 ↔ idealClass f ^ 2 = 1 := by
  rw [sq, ← inv_eq_iff_mul_eq_one, ← idealClass_conj]
  exact ⟨fun h => idealClass_eq_of_sLEquiv (f := f.conj) h, fun h => sLEquiv_of_idealClass_eq hD (f := f.conj) h⟩

open Classical in
/-- **$|\mathrm{Aut}(f)|$ in $\mathrm{GL}_2(\mathbb{Z})$** ($D < 0$ fundamental, the convention of this repository $\mathrm{Aut} \subseteq
\mathrm{GL}_2(\mathbb{Z})$, the repo's `Siegel.Aut`): $|\mathrm{Aut}(f)| = 2w$ if $f$ has an improper automorphism
($\bar f \sim_{\mathrm{SL}} f$, equivalently $[\mathfrak a_f]^2 = 1$ by `sLEquiv_conj_iff`), and $|\mathrm{Aut}(f)| = w$
otherwise; $w$ = `torsionOrder` $(K_D)$. *Proof:* $\det : \mathrm{Aut}(f) \to \{\pm 1\}$ has kernel $\mathrm{Aut}^+(f)$
(`card_autSL`) and image $\{\pm 1\}$ or $\{1\}$. -/
@[kb "cox2013" "§2.A [unverified locator]"]
theorem card_aut (hD : D < 0) (f : PrimPosForm D) :
    Nat.card (Siegel.Aut f.1) = (if SLEquiv (conjForm f.1) f.1 then 2 else 1) *
      NumberField.Units.torsionOrder (QField D) := by
  classical
  set φ : Siegel.Aut f.1 →* ℤˣ := Matrix.GeneralLinearGroup.det.comp (Siegel.Aut f.1).subtype
  have hφ : ∀ x : Siegel.Aut f.1, ((φ x : ℤˣ) : ℤ) = x.1.val.det := fun x => rfl
  have hker : Nat.card φ.ker = Nat.card (AutSL f.1) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, mem_autSL.mpr ⟨x.1.2, ?_⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_autSL.mp y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have := x.2; rw [MonoidHom.mem_ker, Units.ext_iff, hφ] at this; exact this
    · rw [MonoidHom.mem_ker, Units.ext_iff, hφ]; exact (mem_autSL.mp y.2).2
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, card_autSL hD f] at hcard
  rw [← hcard, mul_comm]
  congr 1
  split_ifs with h
  · obtain ⟨γ, hγ, hd⟩ := (exists_improper_iff f.1).mpr h
    have htop : φ.range = ⊤ := by
      refine eq_top_iff.mpr fun u _ => ?_
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact φ.range.one_mem
      · exact ⟨⟨γ, hγ⟩, Units.ext (by rw [hφ]; exact hd)⟩
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  · have hbot : φ.range = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rintro u ⟨x, rfl⟩
      rw [Subgroup.mem_bot, Units.ext_iff, hφ, Units.val_one]
      rcases det_GL_eq x.1 with hd | hd
      · exact hd
      · exact absurd ((exists_improper_iff f.1).mp ⟨x.1, x.2, hd⟩) h
    rw [hbot, Subgroup.card_bot]

/-! ### The number of units: $w = 2, 4, 6$ -/

omit [IsQuadDisc D] in
/-- $4N(u + v\omega) = (2u + b_D v)^2 - D v^2$. -/
theorem four_mul_norm (hD4 : D % 4 = 0 ∨ D % 4 = 1) (z : QOrder D) :
    4 * norm z = (2 * z.re + qb D * z.im) ^ 2 - D * z.im ^ 2 := by
  have hq := discr_qa_qb hD4
  rw [discr_def] at hq
  rw [QuadraticAlgebra.norm_def]; linear_combination -(z.im ^ 2) * hq

/-- For $D < 0$ the units of $\mathbb{Z}[\omega]$ are the elements of norm $1$. -/
def unitsEquivNormOne (hD : D < 0) : (QOrder D)ˣ ≃ {z : QOrder D // norm z = 1} where
  toFun u := ⟨u, norm_unit_eq_one hD (IsQuadDisc.fund (D := D)).1 u⟩
  invFun z := ⟨z.1, star z.1, by rw [← algebraMap_norm_eq_mul_star, z.2, map_one],
    by rw [mul_comm, ← algebraMap_norm_eq_mul_star, z.2, map_one]⟩
  left_inv u := Units.ext rfl
  right_inv z := rfl

/-- **$w = 2$ for $D < -4$:** the only units are $\pm 1$ ($4 = (2u + b_D v)^2 + |D| v^2$ forces $v = 0$). -/
@[kb "marcus1977" "Ch. 2, Exercise 13 [unverified locator]"]
theorem card_units_of_lt (hD : D < -4) : Nat.card (QOrder D)ˣ = 2 := by
  classical
  have hD4 := (IsQuadDisc.fund (D := D)).1
  rw [Nat.card_congr ((unitsEquivNormOne (by omega)).trans (Equiv.subtypeEquivRight (q := fun z =>
    z ∈ ({1, -1} : Finset (QOrder D))) fun z => ?_)), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_pair]
  · intro h
    have := congrArg QuadraticAlgebra.re h
    simp at this
  · have h4 := four_mul_norm hD4 z
    constructor
    · intro hN
      rw [hN] at h4
      have him : z.im = 0 := by
        by_contra him
        have : 1 ≤ z.im ^ 2 := by
          have := sq_pos_of_ne_zero him
          omega
        nlinarith [sq_nonneg (2 * z.re + qb D * z.im)]
      rw [him] at h4
      have hre : z.re = 1 ∨ z.re = -1 := by
        have : z.re ^ 2 = 1 := by nlinarith
        exact eq_one_or_neg_one_of_sq this
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hre with h | h
      · left; ext <;> simp [h, him]
      · right; ext <;> simp [h, him]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> simp [QuadraticAlgebra.norm_def]

omit [IsQuadDisc D] in
theorem norm_one_iff_neg_four (z : QOrder (-4)) :
    norm z = 1 ↔ z ∈ ({⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} : Finset (QOrder (-4))) := by
  obtain ⟨x, y⟩ := z
  simp only [QuadraticAlgebra.norm_def, Finset.mem_insert, Finset.mem_singleton, QuadraticAlgebra.mk.injEq]
  have ha : qa (-4) = -1 := by decide
  have hb : qb (-4) = 0 := by decide
  rw [ha, hb]
  constructor
  · intro h
    have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
    have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith [sq_nonneg y]
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hx1, hx2⟩ := hx
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

omit [IsQuadDisc D] in
theorem norm_one_iff_neg_three (z : QOrder (-3)) :
    norm z = 1 ↔ z ∈ ({⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, 1⟩} : Finset (QOrder (-3))) := by
  obtain ⟨x, y⟩ := z
  simp only [QuadraticAlgebra.norm_def, Finset.mem_insert, Finset.mem_singleton, QuadraticAlgebra.mk.injEq]
  have ha : qa (-3) = -1 := by decide
  have hb : qb (-3) = 1 := by decide
  rw [ha, hb]
  constructor
  · intro h
    have h1 : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * x + y)]
    have h2 : (2 * x + y) ^ 2 ≤ 4 := by nlinarith [sq_nonneg y]
    have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith
    have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hx1, hx2⟩ := hx
    interval_cases x <;> interval_cases y <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- **$w = 4$ for $D = -4$** ($\mathbb{Z}[i]^\times = \{\pm 1, \pm i\}$). -/
@[kb "marcus1977" "Ch. 2, Exercise 13 [unverified locator]"]
theorem card_units_of_eq_neg_four (h : D = -4) : Nat.card (QOrder D)ˣ = 4 := by
  subst h
  rw [Nat.card_congr ((unitsEquivNormOne (by norm_num)).trans
    (Equiv.subtypeEquivRight norm_one_iff_neg_four)), Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

/-- **$w = 6$ for $D = -3$** ($\mathbb{Z}[\rho]^\times = \{\pm 1, \pm\rho, \pm\rho^2\}$). -/
@[kb "marcus1977" "Ch. 2, Exercise 13 [unverified locator]"]
theorem card_units_of_eq_neg_three (h : D = -3) : Nat.card (QOrder D)ˣ = 6 := by
  subst h
  rw [Nat.card_congr ((unitsEquivNormOne (by norm_num)).trans
    (Equiv.subtypeEquivRight norm_one_iff_neg_three)), Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

omit [IsQuadDisc D] in
/-- A fundamental discriminant $-4 \le D < 0$ is $-3$ or $-4$. -/
theorem eq_neg_three_or_neg_four (hD : D < 0) (h4 : -4 ≤ D) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    D = -3 ∨ D = -4 := by omega

/-- **The number of roots of unity of an imaginary quadratic field** ($D < 0$ fundamental):
$w = 6$ for $D = -3$, $w = 4$ for $D = -4$, $w = 2$ for $D < -4$. (`torsionOrder` was left
uncomputed in the class number formula file). -/
@[kb "marcus1977" "Ch. 2, Exercise 13 [unverified locator]"]
theorem torsionOrder_of_neg (hD : D < 0) :
    NumberField.Units.torsionOrder (QField D) = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  rw [← card_units_eq_torsionOrder hD]
  split_ifs with h3 h4
  · exact card_units_of_eq_neg_three h3
  · exact card_units_of_eq_neg_four h4
  · refine card_units_of_lt ?_
    by_contra h
    rcases eq_neg_three_or_neg_four hD (by omega) (IsQuadDisc.fund (D := D)).1 with h' | h' <;> contradiction

end QuadFormsKB.Binary
