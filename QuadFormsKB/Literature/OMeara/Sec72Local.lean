/-
# O'Meara §72: local lemmas for Theorem 72:1

Auxiliary statements for `Sec72.lean`: diagonal forms over a field $K$ of characteristic $0$ (binary representation
through the Hilbert symbol, splitting off a represented value, the Hasse symbol of $\langle x\rangle \perp U$), and
facts at the completions of a number field $F$ (multiplicativity of the Hilbert symbol, invariance of O'Meara's Hasse
symbol under isometry, universality of the spaces with good invariants at almost all spots).
-/
import QuadFormsKB.Literature.OMeara.Sec71BNorm
import QuadFormsKB.Literature.OMeara.Sec63C
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Witt.Represents

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open QuadForm

/-! ### Diagonal forms over a field -/

section Generic

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem map_diag' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : Fin n → R) :
    (diag c).map f = diag (fun i => f (c i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem nondegenerate_diag (c : Fin n → K) (hc : ∀ i, c i ≠ 0) : (diag c).Nondegenerate := by
  exact QuadForm.nondegenerate_diag hc

/-- A binary diagonal form $\langle u_0, u_1\rangle$ represents $x \ne 0$ if and only if
$(x u_0, -u_0u_1)_K = 1$. -/
theorem diag_pair_representsIn_iff {u₀ u₁ x : K} (h₀ : u₀ ≠ 0) (h₁ : u₁ ≠ 0) (hx : x ≠ 0) :
    (diag ![u₀, u₁]).RepresentsIn K x ↔ hilbertSymbol K (x * u₀) (-(u₀ * u₁)) = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hα : -(u₀ * u₁) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h₀ h₁)
  rw [hilbertSymbol_comm, HN.hilbertSymbol_eq_one_iff_norm K h2 hα, PadicClass.representsIn_diag_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨u₀ * y 0, y 1, ?_⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hy
    rw [← hy]; ring
  · rintro ⟨x₀, x₁, h⟩
    refine ⟨![x₀ / u₀, x₁], ?_⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply mul_left_cancel₀ h₀
    field_simp
    linear_combination -h

/-- **Splitting off a represented value:** if the regular diagonal form $\langle a_0, \dots, a_n\rangle$ represents
$x \ne 0$, then it is isometric to $\langle x, b_0, \dots, b_{n-1}\rangle$ for some $b_i \ne 0$. -/
theorem exists_isometricIn_cons_of_representsIn {a : Fin (n + 1) → K} (ha : ∀ i, a i ≠ 0) {x : K} (hx : x ≠ 0)
    (h : (diag a).RepresentsIn K x) :
    ∃ b : Fin n → K, (∀ i, b i ≠ 0) ∧ (diag a).IsometricIn K (diag (Fin.cons x b)) := by
  have h' : (diag a).RepresentsIn K x := h
  obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons (QuadForm.nondegenerate_diag ha) hx h'
  exact ⟨α, hα, hiso⟩

theorem isometricIn_diag_cons (x : K) {b b' : Fin n → K} (h : (diag b).IsometricIn K (diag b')) :
    (diag (Fin.cons x b : Fin (n + 1) → K)).IsometricIn K (diag (Fin.cons x b')) := by
  exact QuadForm.isometricIn_diag_cons_of K x h

theorem isometricIn_diag_single {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : IsSquare (x / y)) :
    (diag ![x]).IsometricIn K (diag ![y]) := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact div_ne_zero hx hy (by simpa using hs)
  refine ⟨Matrix.of fun _ _ => s⁻¹, ?_, fun v => ?_⟩
  · simp [Matrix.det_unique, hs0]
  · simp only [QuadForm.evalIn_diag, Fin.sum_univ_one, Algebra.algebraMap_self, RingHom.id_apply]
    simp [Matrix.mulVec, dotProduct]
    have hxs : x = y * (s * s) := by rw [← hs]; field_simp
    rw [hxs]; field_simp

theorem isSquare_prod_div_of_isometricIn {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (diag a).IsometricIn K (diag b)) : IsSquare ((∏ i, a i) / ∏ i, b i) := by
  obtain ⟨t, ht, hd⟩ := PadicClass.disc_of_isometric h
  have hb' : ∏ i, b i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  refine ⟨t⁻¹, ?_⟩
  rw [hd] at hb' ⊢
  have ha' : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  field_simp

/-- O'Meara's Hasse symbol of $\langle x\rangle \perp \langle b_0, \dots, b_{n-1}\rangle$ (from the definition
$\prod_{i \le j}$): $(x, x)\prod_j (x, b_j) \cdot S\langle b\rangle$. -/
theorem hasseS_cons (x : K) (b : Fin n → K) :
    hasseS K (Fin.cons x b : Fin (n + 1) → K) =
      hilbertSymbol K x x * (∏ j, hilbertSymbol K x (b j)) * hasseS K b := by
  unfold hasseS
  rw [Fin.prod_univ_succ]
  simp [Fin.prod_univ_succ (n := n), Fin.succ_le_succ_iff, Fin.succ_pos, mul_assoc]

theorem hasseS_pm (a : Fin n → K) : hasseS K a = 1 ∨ hasseS K a = -1 := by
  unfold hasseS
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun i _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun j _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  split_ifs
  · exact PadicClass.hs_pm _ _
  · exact Or.inl rfl

theorem hasseS_eq_vec_mul_of_mul
    (hmul : ∀ a b b' : K, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
      hilbertSymbol K a (b * b') = hilbertSymbol K a b * hilbertSymbol K a b')
    (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    hasseS K a = PadicClass.hasseVec a * hilbertSymbol K (-1) (∏ i, a i) := by
  rw [hasseS_eq_vec]
  congr 1
  have hself : ∀ x : K, x ≠ 0 → hilbertSymbol K x x = hilbertSymbol K (-1) x := fun x hx => by
    have h := hilbertSymbol_self_neg K x
    rw [show -x = -1 * x by ring, hmul _ _ _ hx (by norm_num) hx] at h
    rcases PadicClass.hs_pm x (-1 : K) with h1 | h1 <;> rw [h1] at h <;>
      rw [hilbertSymbol_comm K (-1) x] <;> rcases PadicClass.hs_pm x x with h3 | h3 <;>
      first | omega | (rw [h3, h1] at *; omega)
  simp_rw [fun i => hself (a i) (ha i)]
  clear hself
  induction n with
  | zero => simp [hilbertSymbol_one_right]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, ih (fun i => a i.succ) (fun i => ha i.succ),
      hmul _ _ _ (by norm_num) (ha 0) (Finset.prod_ne_zero_iff.mpr fun i _ => ha i.succ)]

end Generic

/-! ### At the completions of a number field -/

section Places

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem hilbertSymbol_mul_right_finite (v : HeightOneSpectrum (𝓞 F)) {a b c : v.adicCompletion F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol _ a (b * c) = hilbertSymbol _ a b * hilbertSymbol _ a c := by
  rw [hilbertSymbol_comm _ a (b * c), hilbertSymbol_comm _ a b, hilbertSymbol_comm _ a c]
  exact HN.hilbertSymbol_mul_left_finite_nf v b c a hb hc ha

theorem hilbertSymbol_mul_right_infinite (w : InfinitePlace F) {a b c : w.Completion}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol _ a (b * c) = hilbertSymbol _ a b * hilbertSymbol _ a c := by
  rw [hilbertSymbol_comm _ a (b * c), hilbertSymbol_comm _ a b, hilbertSymbol_comm _ a c]
  exact NFLocal.hilbertSymbol_mul_left_infinite_nf w b c a hb hc ha

theorem hasseS_algebraMap_infinite (w : InfinitePlace F) (c : Fin n → F) :
    hasseS w.Completion (fun i => algebraMap F w.Completion (c i)) = (NFPlace.infinite w).hasseOMeara c := by
  rfl

/-- O'Meara's Hasse symbol at an infinite spot is an isometry invariant (real spots: through $F_w \cong \mathbb R$;
complex spots: every symbol is $1$). -/
theorem hasseS_eq_of_isometricIn_infinite (w : InfinitePlace F) {a b : Fin n → w.Completion}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (h : (diag a).IsometricIn w.Completion (diag b)) :
    hasseS w.Completion a = hasseS w.Completion b := by
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hmul : ∀ a b b' : w.Completion, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
      hilbertSymbol _ a (b * b') = hilbertSymbol _ a b * hilbertSymbol _ a b' :=
    fun a b b' ha hb hb' => hilbertSymbol_mul_right_infinite w ha hb hb'
  rw [hasseS_eq_vec_mul_of_mul hmul a ha, hasseS_eq_vec_mul_of_mul hmul b hb]
  obtain ⟨t, ht, hd⟩ := PadicClass.disc_of_isometric h
  have hv : PadicClass.hasseVec a = PadicClass.hasseVec b := by
    rcases w.isReal_or_isComplex with hw | hw
    · let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      rw [← HasseIsoNF.hasseVec_ringEquiv φ a, ← HasseIsoNF.hasseVec_ringEquiv φ b]
      exact HasseIsoNF.hasseVec_real_isometric _ _ (fun i => (map_ne_zero _).mpr (ha i))
        (fun i => (map_ne_zero _).mpr (hb i)) (HasseIsoNF.isometricIn_ringEquiv φ h)
    · simp [PadicClass.hasseVec, HasseIsoNF.hilbertSymbol_complex_place hw]
  rw [hv, hd, PadicClass.hs_sq_right _ _ _ ht]

/-- **Universality at a good spot:** at a non-dyadic finite spot $v$, a regular diagonal form $U$ over $F_v$ of
dimension $n \ge 3$ whose discriminant is a unit $d \in F$ (modulo squares) and whose Hasse symbol is $1$ represents
every $x \ne 0$ (it is isometric to $\langle 1, \dots, 1, d\rangle$, which is isotropic). -/
theorem representsIn_of_good (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hn : 3 ≤ n)
    {u : Fin n → v.adicCompletion F} (hu : ∀ i, u i ≠ 0) {d : F} (hd : v.valuation F d = 1)
    (hdisc : IsSquare ((∏ i, u i) / algebraMap F _ d)) (hS : hasseS _ u = 1)
    {x : v.adicCompletion F} (hx : x ≠ 0) : (diag u).RepresentsIn (v.adicCompletion F) x := by
  classical
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have hv : ∀ y : F, Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
  have h2' : Valued.v (2 : v.adicCompletion F) = 1 := by
    have : (2 : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F 2) := by
      rw [map_ofNat, map_ofNat]
    rw [this, hv, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr h2
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hdK : algebraMap F (v.adicCompletion F) d ≠ 0 := (map_ne_zero_iff _ (algebraMap F _).injective).mpr hd0
  have hdv : Valued.v (algebraMap F (v.adicCompletion F) d) = 1 := by rw [hv]; exact hd
  obtain ⟨s, hs⟩ := hdisc
  have hP : ∏ i, u i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hu i
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hs
    exact hs.elim hP hdK
  have hprod : ∏ i, u i = algebraMap F _ d * s ^ 2 := by
    rw [sq, ← hs]; field_simp
  -- the comparison form
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set u' : Fin (m + 1) → v.adicCompletion F :=
    fun i => if i = Fin.last m then algebraMap F _ d else 1 with hu'
  have hu'0 : ∀ i, u' i ≠ 0 := fun i => by
    simp only [hu']; split_ifs <;> simp [hdK]
  have hprod' : ∏ i, u' i = algebraMap F _ d := by
    simp [hu', Finset.prod_ite_eq']
  have hvec : PadicClass.hasseVec u' = 1 := by
    unfold PadicClass.hasseVec
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := hij.ne
      by_cases hi : i = Fin.last m
      · exact absurd (hi ▸ hij) (by simp [Fin.le_last])
      · simp only [hu', hi, if_false]
        rw [hilbertSymbol_comm, hilbertSymbol_one_right]
    · rfl
  have hunit : hilbertSymbol (v.adicCompletion F) (-1) (algebraMap F _ d) = 1 := by
    refine OMeara.hs_units v h2' ?_ hdv
    simp
  have hvecu : PadicClass.hasseVec u = 1 := by
    have := hasseS_eq_hasseVec_mul v u hu
    rw [hS, hprod, mul_comm (algebraMap F (v.adicCompletion F) d), PadicClass.hs_sq_right _ _ _ hs0, hunit, mul_one] at this
    exact this.symm
  have hiso : (diag u).IsometricIn (v.adicCompletion F) (diag u') := by
    refine (PadicClass.isometric_iff_invariants hK hu hu'0).mpr ⟨⟨s⁻¹, inv_ne_zero hs0, ?_⟩, ?_⟩
    · rw [hprod', hprod]; field_simp
    · rw [hvec, hvecu]
  have hisoF : ((QuadForm.diag (fun i : Fin (m + 1) => if i = Fin.last m then d else 1)) :
      QuadForm F (m + 1)).IsotropicIn (v.adicCompletion F) :=
    NFLocal.isotropic_diag_units_nf v h2 (m + 1) hn _ (fun i => by
      split_ifs
      · exact hd
      · simp)
  have hiso' : (diag u').IsotropicIn (v.adicCompletion F) := by
    obtain ⟨y, hy0, hy⟩ := hisoF
    refine ⟨y, hy0, ?_⟩
    rw [QuadForm.evalIn_diag] at hy
    rw [QuadForm.evalIn_diag]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hu']
    split_ifs <;> simp
  exact QuadForm.representsIn_of_isometricIn _ hiso (PadicClass.representsIn_of_isotropic hu'0 hiso' x)

/-- A finite product over the spots of $F$ splits into the finite spots and the infinite spots. -/
theorem finprod_nfPlace (f : NFPlace F → ℤ) (hf : Function.HasFiniteMulSupport f) :
    ∏ᶠ v, f v = (∏ᶠ v : HeightOneSpectrum (𝓞 F), f (.finite v)) * ∏ w : InfinitePlace F, f (.infinite w) := by
  classical
  have hg : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) => f (.finite v)) := by
    have : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => f (.finite v)) ⊆
        NFPlace.finite ⁻¹' Function.mulSupport f := fun v hv => hv
    exact (hf.preimage (fun _ _ _ _ h => NFPlace.finite.inj h)).subset this
  let T : Finset (NFPlace F) :=
    hg.toFinset.map ⟨NFPlace.finite, fun _ _ h => NFPlace.finite.inj h⟩ ∪
      (Finset.univ : Finset (InfinitePlace F)).map ⟨NFPlace.infinite, fun _ _ h => NFPlace.infinite.inj h⟩
  have hT : Function.mulSupport f ⊆ T := by
    intro x hx
    cases x with
    | infinite w => exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩)
    | finite v => exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v, hg.mem_toFinset.mpr hx, rfl⟩)
  rw [finprod_eq_prod_of_mulSupport_subset f hT,
    finprod_eq_prod_of_mulSupport_toFinset_subset _ hg (Finset.Subset.refl _)]
  rw [Finset.prod_union, Finset.prod_map, Finset.prod_map]
  · rfl
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx'
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hx'
    cases hb

end Places

end QuadFormsKB.OMeara
