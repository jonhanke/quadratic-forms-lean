/-
# Cassels, Chapter 14, Lemma 3.3: the local classes at $p = 2$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 340. The sets of classes `LocalClasses` and the
reconstruction of the garbled cases are explained in `QuadFormsKB.Literature.Cassels.Ch14.LocalClasses`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.LocalClasses

namespace QuadFormsKB.Composition

open QuadForm Siegel

section TwoAdicHelpers

theorem norm_two_padic : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  have := PadicInt.norm_p (p := 2)
  simpa using this

/-- A unit of $\mathbb Z_2$ is odd. -/
theorem two_dvd_sub_one_of_isUnit {x : ℤ_[2]} (hx : IsUnit x) : (2 : ℤ_[2]) ∣ x - 1 := by
  have h0 := Siegel.Kneser.toZMod_ne_zero_of_isUnit hx
  have h1 : PadicInt.toZMod x = 1 := by
    generalize PadicInt.toZMod x = y at h0 ⊢
    revert y; decide
  have : x - 1 ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
    rw [RingHom.mem_ker, map_sub, h1, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  simpa using this

/-- $1 + 8k$ is a unit of $\mathbb Z_2$. -/
theorem isUnit_one_add_eight (k : ℤ_[2]) : IsUnit (1 + 8 * k : ℤ_[2]) := by
  apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
  have : (8 : ZMod 2) = 0 := by decide
  rw [map_add, map_mul, map_one, map_ofNat, this, zero_mul, add_zero]
  exact one_ne_zero

/-- **Hensel, $p = 2$:** $1 + 8k$ is the square of a unit. -/
theorem exists_sq_one_add_eight (k : ℤ_[2]) : ∃ z : ℤ_[2], z ^ 2 = 1 + 8 * k ∧ IsUnit z := by
  have h2 := norm_two_padic
  have hn : ‖(8 * k : ℤ_[2])‖ ≤ 1 / 8 := by
    rw [norm_mul]
    have : ‖(8 : ℤ_[2])‖ = 1 / 8 := by
      rw [show (8 : ℤ_[2]) = 2 ^ 3 by norm_num, norm_pow, h2]; norm_num
    rw [this]
    exact mul_le_of_le_one_right (by norm_num) k.norm_le_one
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
    (F := Polynomial.X ^ 2 - Polynomial.C (1 + 8 * k : ℤ_[2])) (a := 1) (by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Polynomial.derivative_X_pow, Polynomial.derivative_C]
      simp
      rw [h2]
      rw [← norm_mul]
      refine lt_of_le_of_lt hn ?_
      norm_num)
  simp at hz
  have hz' : z ^ 2 = 1 + 8 * k := sub_eq_zero.mp hz
  refine ⟨z, hz', ?_⟩
  have : IsUnit (z ^ 2) := by rw [hz']; exact isUnit_one_add_eight k
  exact (isUnit_pow_iff two_ne_zero).mp this

/-- Solving $r X^2 + X + s = 0$ in $\mathbb Z_2$ when $2 \mid s$ (Hensel at $0$). -/
theorem exists_root_of_two_dvd (r s : ℤ_[2]) (hs : (2 : ℤ_[2]) ∣ s) : ∃ X : ℤ_[2], r * X ^ 2 + X + s = 0 := by
  have h2 := norm_two_padic
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
    (F := Polynomial.C r * Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (2 * t)) (a := 0) (by
      simp
      rw [h2]
      calc 1 / 2 * ‖t‖ ≤ 1 / 2 * 1 := by gcongr; exact t.norm_le_one
        _ < 1 := by norm_num)
  simp at hz
  exact ⟨z, hz⟩

/-- Changing $x \mapsto x + ky$ to make an odd middle coefficient equal to $1$ (leading coefficient a unit). -/
theorem shear_to_one {w b c : ℤ_[2]} (hw : IsUnit w) (hb : ∃ m, b = 1 + 2 * m) :
    ∃ c', IsometricGL (bq w b c) (bq w 1 c') ∧ 1 - 4 * w * c' = b ^ 2 - 4 * w * c := by
  obtain ⟨m, rfl⟩ := hb
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  have hk : (1 + 2 * m) + 2 * w * (-m * wi) = 1 := by linear_combination (-2 * m) * hwi
  refine ⟨w * (-m * wi) ^ 2 + (1 + 2 * m) * (-m * wi) + c, ?_, ?_⟩
  · have := isometricGL_shear w (1 + 2 * m) c (-m * wi)
    rwa [hk] at this
  · linear_combination (-((1 + 2 * m) + 2 * w * (-m * wi) + 1)) * hk

/-- If $b^2 = 4t + 1$ in $\mathbb Z_2$ then $b$ is odd. -/
theorem exists_half_of_sq {b t : ℤ_[2]} (h : b ^ 2 = 4 * t + 1) : ∃ m, b = 1 + 2 * m := by
  have hp : Prime (2 : ℤ_[2]) := by simpa using PadicInt.prime_p (p := 2)
  have : (2 : ℤ_[2]) ∣ (b - 1) * (b + 1) := ⟨2 * t, by linear_combination h⟩
  rcases hp.dvd_or_dvd this with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m, by linear_combination hm⟩
  · exact ⟨m - 1, by linear_combination hm⟩

/-- **Odd discriminant:** a binary form over $\mathbb Z_2$ of discriminant $4q+1$ taking a unit value is
equivalent to $x^2 + xy - q y^2$. -/
theorem odd_normal {q : ℤ} {F : QuadForm ℤ_[2] 2} (hF : ∃ v, IsUnit (F.eval v))
    (hD : disc2 F = 4 * (q : ℤ_[2]) + 1) : IsometricGL F (bq 1 1 (-(q : ℤ_[2]))) := by
  obtain ⟨v, hv⟩ := hF
  obtain ⟨b, c, hbc, hiso⟩ := exists_first hv
  set w := F.eval v
  rw [hD] at hbc
  obtain ⟨m, hm⟩ := exists_half_of_sq (b := b) (t := q + w * c) (by linear_combination hbc)
  obtain ⟨c', h1, hc'⟩ := shear_to_one hv ⟨m, hm⟩
  obtain ⟨j, hj⟩ := two_dvd_sub_one_of_isUnit hv
  obtain ⟨X, hX⟩ := exists_root_of_two_dvd c' (w - 1) ⟨j, hj⟩
  have hev : (bq w 1 c').eval ![1, X] = 1 := by rw [bq_eval]; linear_combination hX
  have hv' : IsUnit ((bq w 1 c').eval ![1, X]) := by rw [hev]; exact isUnit_one
  obtain ⟨b2, c2, hbc2, hiso2⟩ := exists_first hv'
  rw [hev] at hbc2 hiso2
  have hd : disc2 (bq w 1 c') = 1 - 4 * w * c' := by
    rw [disc2, bq_coeff00, bq_coeff01, bq_coeff11]; ring
  have hdisc' : 1 - 4 * w * c' = 4 * (q : ℤ_[2]) + 1 := hc'.trans hbc
  obtain ⟨m2, hm2⟩ := exists_half_of_sq (b := b2) (t := q + c2) (by linear_combination hbc2 + hd + hdisc')
  obtain ⟨c3, h3, hc3⟩ := shear_to_one (isUnit_one (M := ℤ_[2])) ⟨m2, hm2⟩ (c := c2)
  have hc3' : c3 = -(q : ℤ_[2]) := by
    refine mul_left_cancel₀ (four_ne_zero_padic (p := 2)) ?_
    linear_combination (-1 : ℤ_[2]) * hc3 + (-1 : ℤ_[2]) * hbc2 + (-1 : ℤ_[2]) * hd + (-1 : ℤ_[2]) * hdisc'
  rw [hc3'] at h3
  exact hiso.trans (h1.trans (hiso2.trans h3))

theorem card_two_odd {D : ℤ} (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hD2 : D % 2 = 1) : Nat.card (LocalClasses 2 D) = 1 := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, D = 4 * q + 1 := ⟨D / 4, by omega⟩
  have key : ∀ F : LocalPrimForm 2 D, IsometricGL F.1 (bq 1 1 (-(q : ℤ_[2]))) := by
    intro F
    refine odd_normal (exists_unit_value F.2.1) ?_
    rw [← neg_det_eq_disc2, F.2.2, hq]; push_cast; ring
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ?_⟩
  · induction a using localClasses_ind with | _ F => ?_
    induction b using localClasses_ind with | _ G => ?_
    exact localClasses_sound ((key F).trans (key G).symm)
  · exact ⟨Quotient.mk _ ⟨bq 1 1 (-(q : ℤ_[2])), Or.inl (by rw [bq_coeff00]; exact isUnit_one),
      by rw [neg_det_bq, hq]; push_cast; ring⟩⟩

/-- Residues modulo $8$. -/
abbrev R8 : Type := ZMod (2 ^ 3)

/-- Reduction $\mathbb Z_2 \to \mathbb Z/8$. -/
noncomputable abbrev pi8 : ℤ_[2] →+* R8 := PadicInt.toZModPow 3

/-- A residue mod $8$ is odd (a unit). -/
def OddRes (w : R8) : Prop := ∃ w', w * w' = 1

instance : DecidablePred OddRes := fun w => by unfold OddRes; infer_instance

theorem pi8_eq (x y : ℤ_[2]) (h : pi8 x = pi8 y) : ∃ k : ℤ_[2], x = y + 8 * k := by
  have : x - y ∈ RingHom.ker pi8 := by rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at this
  obtain ⟨k, hk⟩ := this
  exact ⟨k, by push_cast at hk; linear_combination hk⟩

theorem pi8_surj (w : R8) : ∃ x : ℤ_[2], pi8 x = w := ZMod.ringHom_surjective pi8 w

theorem isUnit_iff_oddRes (x : ℤ_[2]) : IsUnit x ↔ OddRes (pi8 x) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    exact ⟨pi8 y, by rw [← map_mul, hy, map_one]⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨y, rfl⟩ := pi8_surj w'
    obtain ⟨k, hk⟩ := pi8_eq (x * y) 1 (by rw [map_mul, hw', map_one])
    have : IsUnit (x * y) := by rw [hk]; exact isUnit_one_add_eight k
    exact isUnit_of_mul_isUnit_left this

theorem oddRes_mul_self : ∀ a : R8, OddRes a → a * a = 1 := by decide

/-- Residue table of the unit values `a s² + b t²`. -/
def Wf (a b : R8) : Finset R8 :=
  Finset.univ.filter (fun w => OddRes w ∧ ∃ s t : R8, a * s ^ 2 + b * t ^ 2 = w)

/-- The set of distinct residue-sets, over the four odd $a$. -/
def Tset (m : R8) : Finset (Finset R8) :=
  (Finset.univ.filter OddRes).image (fun a => Wf a (-m * a))

theorem Tset_card : ∀ m : R8,
    (Tset m).card = if m.val % 4 = 1 then 1 else if m = 0 then 4 else 2 := by decide

/-- The residues mod $8$ of the unit values of a form (an invariant of $\mathrm{GL}_2(\mathbb Z_2)$-equivalence). -/
def Uset (F : QuadForm ℤ_[2] 2) : Set R8 := {w | ∃ v, IsUnit (F.eval v) ∧ pi8 (F.eval v) = w}

theorem Uset_mono {F G : QuadForm ℤ_[2] 2} (h : IsometricGL F G) : Uset G ⊆ Uset F := by
  rintro w ⟨v, hv, hw⟩
  obtain ⟨g, hg⟩ := h
  exact ⟨g.val.mulVec v, by rw [hg]; exact hv, by rw [hg]; exact hw⟩

/-- `Uset` as a `Finset`. -/
noncomputable def Phi (F : QuadForm ℤ_[2] 2) : Finset R8 := by
  classical exact Finset.univ.filter (fun w => w ∈ Uset F)

theorem mem_Phi {F : QuadForm ℤ_[2] 2} {w : R8} : w ∈ Phi F ↔ w ∈ Uset F := by
  classical simp [Phi]

theorem Phi_iso {F G : QuadForm ℤ_[2] 2} (h : IsometricGL F G) : Phi F = Phi G :=
  Finset.ext fun w => by
    rw [mem_Phi, mem_Phi]
    exact ⟨fun x => Uset_mono h.symm x, fun x => Uset_mono h x⟩

theorem pi8_bq_eval (u e s t : ℤ_[2]) :
    pi8 ((bq u 0 e).eval ![s, t]) = pi8 u * pi8 s ^ 2 + pi8 e * pi8 t ^ 2 := by
  rw [bq_eval]; simp

theorem mem_Uset_bq {u e : ℤ_[2]} {w : R8} :
    w ∈ Uset (bq u 0 e) ↔ OddRes w ∧ ∃ s t : R8, pi8 u * s ^ 2 + pi8 e * t ^ 2 = w := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, t, rfl⟩ : ∃ s t, v = ![s, t] := ⟨v 0, v 1, vec_eta v⟩
    exact ⟨(isUnit_iff_oddRes _).mp hv, pi8 s, pi8 t, (pi8_bq_eval u e s t).symm⟩
  · rintro ⟨hodd, s, t, h⟩
    obtain ⟨s', rfl⟩ := pi8_surj s
    obtain ⟨t', rfl⟩ := pi8_surj t
    have h2 := (pi8_bq_eval u e s' t').trans h
    exact ⟨![s', t'], (isUnit_iff_oddRes _).mpr (by rw [h2]; exact hodd), h2⟩

theorem Phi_bq (u e : ℤ_[2]) : Phi (bq u 0 e) = Wf (pi8 u) (pi8 e) :=
  Finset.ext fun w => by
    rw [mem_Phi, mem_Uset_bq]
    simp only [Wf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Equivalence of diagonal forms from a represented unit congruent mod $8$.** -/
theorem diag_equiv_of_mod8 {D : ℤ_[2]}
    (hhalf : ∀ b' c' w : ℤ_[2], IsUnit w → b' ^ 2 - 4 * w * c' = D → ∃ β, b' = 2 * β)
    {u e u' e' s t w : ℤ_[2]} (hu' : IsUnit u') (hD : -4 * u * e = D) (hD' : -4 * u' * e' = D)
    (_hw : IsUnit w) (hst : u * s ^ 2 + e * t ^ 2 = w) (hmod : pi8 w = pi8 u') :
    IsometricGL (bq u 0 e) (bq u' 0 e') := by
  obtain ⟨k, hk⟩ := pi8_eq w u' hmod
  obtain ⟨ui, hui⟩ := hu'.exists_right_inv
  obtain ⟨z, hz, hzu⟩ := exists_sq_one_add_eight (ui * k)
  have hwz : w = u' * z ^ 2 := by rw [hz, hk]; linear_combination (-8 * k) * hui
  obtain ⟨zi, hzi⟩ := hzu.exists_right_inv
  refine diag_equiv_of_rep hhalf (s := s * zi) (t := t * zi) hu' hD hD' ?_
  have : u * (s * zi) ^ 2 + e * (t * zi) ^ 2 = zi ^ 2 * w := by linear_combination zi ^ 2 * hst
  rw [this, hwz]; linear_combination (u' * (z * zi + 1)) * hzi

theorem card_two_even (d : ℤ) :
    Nat.card (LocalClasses 2 (4 * d)) = if d % 4 = 1 then 1 else if 8 ∣ d then 4 else 2 := by
  have hD : ((4 * d : ℤ) : ℤ_[2]) = 4 * (d : ℤ_[2]) := by push_cast; ring
  have hp : Prime (2 : ℤ_[2]) := by simpa using PadicInt.prime_p (p := 2)
  have hhalf := half_of_two_dvd hp (D := ((4 * d : ℤ) : ℤ_[2])) ⟨2 * (d : ℤ_[2]), by rw [hD]; ring⟩
  let PhiC : LocalClasses 2 (4 * d) → Finset R8 :=
    Quotient.lift (s := localSetoid 2 (4 * d)) (fun F => Phi F.1) (fun F G h => Phi_iso h)
  have PhiC_mk : ∀ F : LocalPrimForm 2 (4 * d), PhiC (Quotient.mk _ F) = Phi F.1 := fun F => rfl
  have inj : Function.Injective PhiC := by
    intro a b hab
    induction a using localClasses_ind with | _ F => ?_
    induction b using localClasses_ind with | _ G => ?_
    rw [PhiC_mk, PhiC_mk] at hab
    obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
    obtain ⟨u', e', hu', h', hG⟩ := exists_diagForm hhalf G
    have hF' : IsometricGL F.1 (bq u 0 e) := hF
    have hG' : IsometricGL G.1 (bq u' 0 e') := hG
    have h1 : Phi (bq u 0 e) = Phi (bq u' 0 e') := by
      rw [← Phi_iso hF', ← Phi_iso hG']; exact hab
    have hmem : pi8 u ∈ Phi (bq u 0 e) := by
      rw [mem_Phi, mem_Uset_bq]
      exact ⟨(isUnit_iff_oddRes _).mp hu, 1, 0, by simp⟩
    rw [h1, mem_Phi, mem_Uset_bq] at hmem
    obtain ⟨_, s, t, hst⟩ := hmem
    obtain ⟨s', rfl⟩ := pi8_surj s
    obtain ⟨t', rfl⟩ := pi8_surj t
    have hw : pi8 (u' * s' ^ 2 + e' * t' ^ 2) = pi8 u := by simpa using hst
    have hwU : IsUnit (u' * s' ^ 2 + e' * t' ^ 2) :=
      (isUnit_iff_oddRes _).mpr (by rw [hw]; exact (isUnit_iff_oddRes _).mp hu)
    have key : IsometricGL (bq u' 0 e') (bq u 0 e) :=
      diag_equiv_of_mod8 hhalf hu h' h hwU rfl hw
    exact localClasses_sound (hF'.trans (key.symm.trans hG'.symm))
  set m : R8 := pi8 (d : ℤ_[2]) with hm
  have hrange : Set.range PhiC = ↑(Tset m) := by
    ext S
    simp only [Set.mem_range, Finset.mem_coe, Tset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using localClasses_ind with | _ F => ?_
      obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
      have hF' : IsometricGL F.1 (bq u 0 e) := hF
      have hodd : OddRes (pi8 u) := (isUnit_iff_oddRes _).mp hu
      have hue : u * e = -(d : ℤ_[2]) := by
        rw [hD] at h
        exact mul_left_cancel₀ (four_ne_zero_padic (p := 2)) (by linear_combination (-1 : ℤ_[2]) * h)
      have hm' : pi8 u * pi8 e = -m := by
        rw [← map_mul, hue, map_neg]
      have haa := oddRes_mul_self _ hodd
      have hπ : pi8 e = -m * pi8 u := by
        linear_combination (-pi8 e) * haa + pi8 u * hm'
      refine ⟨pi8 u, hodd, ?_⟩
      rw [PhiC_mk, Phi_iso hF', Phi_bq, hπ]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨u, rfl⟩ := pi8_surj a
      have hu : IsUnit u := (isUnit_iff_oddRes _).mpr ha
      obtain ⟨ui, hui⟩ := hu.exists_right_inv
      have h : -4 * u * (-(d : ℤ_[2]) * ui) = ((4 * d : ℤ) : ℤ_[2]) := by
        rw [hD]; linear_combination (4 * (d : ℤ_[2])) * hui
      refine ⟨Quotient.mk _ (diagForm u (-(d : ℤ_[2]) * ui) hu h), ?_⟩
      rw [PhiC_mk]
      show Phi (bq u 0 (-(d : ℤ_[2]) * ui)) = _
      rw [Phi_bq]
      have haa := oddRes_mul_self _ ha
      have hui' : pi8 u * pi8 ui = 1 := by rw [← map_mul, hui, map_one]
      have : pi8 (-(d : ℤ_[2]) * ui) = -m * pi8 u := by
        have hpu : pi8 ui = pi8 u := by linear_combination (-pi8 ui) * haa + pi8 u * hui'
        rw [map_mul, map_neg, hpu, hm]
      rw [this]
  have hcard : Nat.card (LocalClasses 2 (4 * d)) = (Tset m).card := by
    rw [Nat.card_congr (Equiv.ofInjective PhiC inj), hrange]; simp
  rw [hcard, Tset_card]
  have hmd : m = (d : R8) := by simp [hm]
  have hval := ZMod.val_intCast (n := 2 ^ 3) d
  have h8 : ((2 ^ 3 : ℕ) : ℤ) = 8 := by norm_num
  rw [h8] at hval
  have e1 : (m.val % 4 = 1) ↔ d % 4 = 1 := by rw [hmd]; omega
  have e2 : m = 0 ↔ 8 ∣ d := by
    rw [hmd]
    have := ZMod.intCast_zmod_eq_zero_iff_dvd d (2 ^ 3)
    simpa using this
  by_cases h1 : d % 4 = 1 <;> by_cases h2 : 8 ∣ d <;> simp [e1, e2, h1, h2]

end TwoAdicHelpers

/-- **Cassels, Ch. 14, Lemma 3.3** (p. 340): *($p = 2$) (i) if $2 \nmid D$ then $\mathcal G_2$ is trivial; (ii) if
$D = 4d$: if $d \equiv 1 \pmod 4$, $\mathcal G_2$ is trivial; if $d \equiv -1 \pmod 4$ it has order $2$; if
$2 \mid d$ but $2^3 \nmid d$ it has order $2$; if $2^3 \mid d$ it (is non-cyclic and) has order $4$.* For every
$D \ne 0$, $D \equiv 0, 1 \pmod 4$; the cases (ii γ), (ii δ) are reconstructed from the scan (module docstring). -/
@[kb "cassels1978" "Ch. 14, Lemma 3.3, p. 340 (cases (ii γ), (ii δ) reconstructed)"]
theorem card_localClasses_two {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    Nat.card (LocalClasses 2 D) =
      if D % 2 = 1 ∨ (D / 4) % 4 = 1 then 1 else if 8 ∣ D / 4 then 4 else 2 := by
  by_cases h2 : D % 2 = 1
  · simp only [h2, true_or, ite_true]; exact card_two_odd hD4 h2
  · obtain ⟨d, rfl⟩ : ∃ d, D = 4 * d := ⟨D / 4, by omega⟩
    rw [card_two_even d, show (4 * d) / 4 = d by omega]
    simp [show ¬ ((4 * d) % 2 = 1) by omega]

end QuadFormsKB.Composition
