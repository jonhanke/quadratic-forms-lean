/-
# O'Meara Theorem 102:8: every power of $2$ occurs as the number of proper spinor genera

**Layer:** as in `Sec102Seven.lean`: $V = F^n$ over a number field $F$ with a regular form `Q : QuadForm F n`,
lattices `Lat F n`, $S$ = all finite spots, the idèle group $J_F$ = `IdeleGroup (𝓞 F) F`, $D = \theta(O^+(V))$,
$P_D$ = `principalSpinorIdeles`, $J_F^L$ = `spinorIdeles`, $\theta(O^+(L_\mathfrak p))$ = `localSpinorNormSq`, and
$g^+(L)$ = `properSpinorGenusNumber`. Local lattices are built in O'Meara's abstract setting (`OMeara.*`, for the
form `qk Q F_𝔭`) and glued with `LocFamily.glue` (81:14).

**Proves**
* **`omeara102_8`** (Theorem 102:8, p. 302): if $n \ge 3$, then for every $r \ge 0$ there is a lattice $L$ on $V$ with
  $g^+(L) = 2^r$ (the first assertion, $g^+(L)$ is a power of $2$, is `omeara102_8a` in `Sec102Seven.lean`).

*Proof* (O'Meara's, steps 1, 4, 5, 6, with 102:7 in the form $g^+(L) = (J_F : P_DJ_F^L)$, `omeara102_7`). Fix a
cofinite set $W$ of non-dyadic spots with $J_F = P_DJ_F^W$ (101:13, `exists_finite_spots_idele_eq_mul`) at which the
discriminant $c$ of the standard base and the non-zero entries of its matrix are units (`exists_sConventions_strong`),
so that $\mathfrak o_\mathfrak p^n$ is unimodular on $W$. For a finite $E \subseteq W$ of spots at which $c$ is a square,
let $K_E$ be the lattice with $K_\mathfrak p$ = a lattice with $\theta(O^+(K_\mathfrak p)) = F_\mathfrak p^\times$ off $W$
(91:7), a lattice with $\theta(O(K_\mathfrak p)) = F_\mathfrak p^{\times2}$ on $E$ (92:7, with 92:2 for the orthonormal
base), and $\mathfrak o_\mathfrak p^n$ on $W - E$. Then $g^+(K_\emptyset) = 1$ ($J_F^W \subseteq J_F^{K_\emptyset}$, step 4);
adding one spot $\mathfrak q$ to $E$ at most doubles $g^+$ ($(J_F^{K_E} : J_F^{K_{E \cup \mathfrak q}}) \mid 2$, step 5);
and for spots $\mathfrak q \ne \mathfrak q'$ chosen by 65:20 (the same $(W - E)$-units are squares at both, $c$ a
square at both), $g^+(K_{E \cup \{\mathfrak q, \mathfrak q'\}}) \ne g^+(K_E)$ (step 6, by the argument with
$\alpha/\beta^2$ of 101:10). So one of $K_{E \cup \mathfrak q'}$, $K_{E \cup \{\mathfrak q, \mathfrak q'\}}$ has
$g^+ = 2g^+(K_E)$, and induction on $r$ gives every $2^r$.

*Update* (as in 101:10): O'Meara also asks for $S_\mathfrak pV = 1$ on $W$; it is not needed, since at the chosen
spots the unimodular $\mathfrak o_\mathfrak p^n$ and the square discriminant already give
$V_\mathfrak p \cong \langle 1, \dots, 1\rangle$ (92:2), which is what 92:7 uses.
-/
import QuadFormsKB.Literature.OMeara.Sec102Seven
import QuadFormsKB.Literature.OMeara.Sec101Ten
import QuadFormsKB.Literature.OMeara.Sec92Gap
import QuadFormsKB.Literature.OMeara.Sec91Local
import QuadFormsKB.Literature.OMeara.Sec65D
import QuadFormsKB.Literature.OMeara.Sec65Rest

open NumberField IsDedekindDomain Matrix
open QuadFormsKB.OMeara (ideleAt ideleAt_mul ideleAt_one ideleAt_inv ideleAt_ofAdic_self ideleAt_ofAdic_ne)
open QuadFormsKB.Hanke2005.SpinorIdele (ideleAt_ne_zero sqClassOf_inv ideleAtHom ideleAt_unitEmbedding spinorNorm_one')

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open OMeara.QIn (glEquiv)

/-! ### Indices in a commutative group -/

section Abstract

variable {G : Type*} [CommGroup G]

/-- If every element of $C$ is in $B$ or in $xB$, then $(C : B) \mid 2$. -/
theorem relIndex_dvd_two_of {B C : Subgroup G} (hBC : B ≤ C) (x : G)
    (hx : ∀ c ∈ C, c ∈ B ∨ x⁻¹ * c ∈ B) : B.relIndex C ∣ 2 := by
  by_cases hxC : x ∈ C
  · rw [Subgroup.relIndex, Subgroup.index]
    let f : Bool → C ⧸ B.subgroupOf C := fun t => if t then QuotientGroup.mk ⟨x, hxC⟩ else 1
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H c =>
        rcases hx c c.2 with h | h
        · refine ⟨false, ?_⟩
          simp only [f, Bool.false_eq_true, ↓reduceIte]
          rw [← QuotientGroup.mk_one, QuotientGroup.eq, inv_one, one_mul, Subgroup.mem_subgroupOf]
          exact h
        · refine ⟨true, ?_⟩
          simp only [f, ↓reduceIte]
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact h
    have : Finite (C ⧸ B.subgroupOf C) := Finite.of_surjective f hf
    have hle : Nat.card (C ⧸ B.subgroupOf C) ≤ 2 := by
      have := Nat.card_le_card_of_surjective f hf
      simpa using this
    have hpos : 0 < Nat.card (C ⧸ B.subgroupOf C) := Nat.card_pos
    interval_cases h : Nat.card (C ⧸ B.subgroupOf C)
    · exact one_dvd 2
    · exact dvd_refl 2
  · have : C ≤ B := fun c hc => by
      rcases hx c hc with h | h
      · exact h
      · exfalso
        apply hxC
        have : x = c * (x⁻¹ * c)⁻¹ := by group
        rw [this]
        exact C.mul_mem hc (C.inv_mem (hBC h))
    rw [Subgroup.relIndex_eq_one.mpr this]
    exact one_dvd 2

/-- Enlarging both $B \le C$ by $A$: $(A \sqcup C : A \sqcup B)$ divides $(C : B)$, and
$(G : A \sqcup B) = (A \sqcup C : A \sqcup B)\,(G : A \sqcup C)$. -/
theorem index_sup_eq_mul (A : Subgroup G) {B C : Subgroup G} (hBC : B ≤ C) :
    (A ⊔ B).relIndex (A ⊔ C) ∣ B.relIndex C ∧
      (A ⊔ B).index = (A ⊔ B).relIndex (A ⊔ C) * (A ⊔ C).index := by
  refine ⟨?_, (Subgroup.relIndex_mul_index (sup_le_sup_left hBC A)).symm⟩
  have e : A ⊔ C = C ⊔ (A ⊔ B) := by
    apply le_antisymm
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
    · exact sup_le le_sup_right (sup_le le_sup_left (hBC.trans le_sup_right))
  rw [e, Subgroup.relIndex_sup_right]
  exact Subgroup.relIndex_dvd_of_le_left C le_sup_right

end Abstract

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

local notation "J" => IdeleGroup (𝓞 F) F

/-! ### Local bridges: O'Meara's local lattices and $\theta(O^+(L_\mathfrak p))$ -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\theta(O^+(L_\mathfrak p))$ depends only on $L_\mathfrak p$. -/
theorem localSpinorNormSq_congr (hQ : Q.Nondegenerate) {L M : Lat F n} (h : loc v L.1 = loc v M.1) :
    localSpinorNormSq Q hQ v L = localSpinorNormSq Q hQ v M := by
  have : locStabV Q v L = locStabV Q v M := by
    ext g
    change locAct v _ (loc v L.1) = loc v L.1 ↔ locAct v _ (loc v M.1) = loc v M.1
    rw [h]
  rw [localSpinorNormSq, localSpinorNormSq, this]

/-- An element of $O(L_\mathfrak p)$ is in O'Meara's $O(L_\mathfrak p)$ for the form `qk Q F_𝔭`. -/
theorem glEquiv_mem_orthLat {L : Lat F n} {g : orthGroup Q Fv} (hg : g ∈ locStabV Q v L) :
    glEquiv Fv (g : GL (Fin n) Fv) ∈ OMeara.orthLat (qk Q Fv) (loc v L.1) := by
  refine ⟨?_, ?_⟩
  · rw [← OMeara.QIn.map_orthGroup Q Fv]
    exact Subgroup.mem_map.mpr ⟨_, g.2, rfl⟩
  · rw [← locAct_eq_latMap]
    exact hg

/-- Every element of $O(V_\mathfrak p)$ has an O'Meara spinor norm representing its spinor norm. -/
theorem exists_hasSpinorNorm_glEquiv (hQ : Q.Nondegenerate) (g : orthGroup Q Fv) :
    ∃ c : Fv, c ≠ 0 ∧ OMeara.HasSpinorNorm (qk Q Fv) (glEquiv Fv (g : GL (Fin n) Fv)) c ∧
      spinorNorm Q Fv g = sqClassOf c := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q Fv hQ g
  exact ⟨valProd Q Fv xs, valProd_ne_zero Q Fv hxs, hasSpinorNorm_symmProd Q Fv xs hxs,
    spinorNorm_symmProd Q Fv hQ xs hxs⟩

/-- **$\theta(O^+(L_\mathfrak p)) = F_\mathfrak p^\times$ from O'Meara's form** (as in 91:7). -/
theorem mem_localSpinorNormSq_of_omeara_top (hQ : Q.Nondegenerate) (L : Lat F n)
    (h : ∀ c : Fv, c ≠ 0 → ∃ σ ∈ OMeara.orthLatPlus (qk Q Fv) (loc v L.1), OMeara.HasSpinorNorm (qk Q Fv) σ c)
    {c : Fv} (hc : c ≠ 0) : sqClassOf c ∈ localSpinorNormSq Q hQ v L := by
  obtain ⟨σ, hσ, hsn⟩ := h c hc
  have hσL := (Subgroup.mem_inf.mp hσ).1
  have hσP := (Subgroup.mem_inf.mp hσ).2
  obtain ⟨g, hg⟩ := exists_orthGroup_glEquiv_eq Q Fv hσL.1
  refine (mem_localSpinorNormSq Q hQ).mpr ⟨g, ⟨?_, ?_⟩, ?_⟩
  · change locAct v (g : GL (Fin n) Fv) (loc v L.1) = loc v L.1
    rw [locAct_eq_latMap, hg]; exact hσL.2
  · have hdet := congrArg Units.val (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hσP).2)
    rw [LinearEquiv.coe_det, Units.val_one] at hdet
    change ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det = 1
    rw [det_eq_glEquiv, hg]; exact hdet
  · exact spinorNorm_eq_of_hasSpinorNorm Q Fv hQ hc (by rw [hg]; exact hsn)

/-- **$\theta(O^+(L_\mathfrak p)) = F_\mathfrak p^{\times 2}$ from O'Meara's form** (as in 92:7). -/
theorem eq_one_of_mem_localSpinorNormSq_of_omeara_sq (hQ : Q.Nondegenerate) (L : Lat F n)
    (h : ∀ σ ∈ OMeara.orthLat (qk Q Fv) (loc v L.1), ∀ c : Fv, OMeara.HasSpinorNorm (qk Q Fv) σ c → IsSquare c)
    {x : SqClass Fv} (hx : x ∈ localSpinorNormSq Q hQ v L) : x = 1 := by
  obtain ⟨g, hg, rfl⟩ := (mem_localSpinorNormSq Q hQ).mp hx
  obtain ⟨c, hc0, hc, hθ⟩ := exists_hasSpinorNorm_glEquiv Q v hQ g
  rw [hθ, sqClassOf_eq_one_iff hc0]
  exact h _ (glEquiv_mem_orthLat Q v (Subgroup.mem_inf.mp hg).1) c hc

/-- **On a unimodular $L_\mathfrak p$ at a non-dyadic spot, $\theta(O^+(L_\mathfrak p)) \subseteq \mathfrak u_\mathfrak p
F_\mathfrak p^{\times 2}$** (92:5, the easy inclusion). -/
theorem isUnitSqClass_of_mem_localSpinorNormSq (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (L : Lat F n)
    (h2 : IsUnit (2 : 𝔬)) (hU : OMeara.IsUnimodular (qk Q Fv) (loc v L.1))
    {x : SqClass Fv} (hx : x ∈ localSpinorNormSq Q hQ v L) : IsUnitSqClass v x := by
  obtain ⟨g, hg, rfl⟩ := (mem_localSpinorNormSq Q hQ).mp hx
  obtain ⟨c, hc0, hc, hθ⟩ := exists_hasSpinorNorm_glEquiv Q v hQ g
  have hnd := nondegenerate_qk Q v hQ
  have hfr : 1 ≤ Module.finrank Fv (Fin n → Fv) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨ε, hε, hεn⟩ := OMeara.exists_hasSpinorNorm_unit_of_isUnimodular (R := 𝔬) (qk Q Fv) h2 hnd hfr
    (loc_isLattice v L.2) hU (glEquiv_mem_orthLat Q v (Subgroup.mem_inf.mp hg).1)
  have hε0 : algebraMap 𝔬 Fv ε ≠ 0 := by
    intro h0
    have := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hε
    change Valued.v (algebraMap 𝔬 Fv ε) = 1 at this
    rw [h0, map_zero] at this; exact zero_ne_one this
  refine ⟨algebraMap 𝔬 Fv ε, (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hε, ?_⟩
  exact spinorNorm_eq_of_hasSpinorNorm Q Fv hQ hε0 hεn

/-- **Example 92:7 at a non-dyadic spot with $\mathfrak o_\mathfrak p^n$ unimodular and square discriminant**: some
lattice $M$ on $V_\mathfrak p$ has $\theta(O(M)) = F_\mathfrak p^{\times 2}$ (by 92:2, $V_\mathfrak p \cong \langle 1, \dots,
1\rangle$, `exists_orthonormal_of_isUnimodular`). -/
theorem exists_local_square (hQ : Q.Nondegenerate) (h2 : IsUnit (2 : 𝔬))
    (hU : OMeara.IsUnimodular (qk Q Fv) (std v : Submodule 𝔬 (Fin n → Fv)))
    (hsq : IsSquare (OMeara.gram (qk Q Fv) (fun i => (Pi.single i 1 : Fin n → Fv))).det) :
    ∃ M : Submodule 𝔬 (Fin n → Fv), M.IsLattice Fv ∧
      ∀ σ ∈ OMeara.orthLat (qk Q Fv) M, ∀ c : Fv, OMeara.HasSpinorNorm (qk Q Fv) σ c → IsSquare c := by
  have hstd : (std v : Submodule 𝔬 (Fin n → Fv)).IsLattice Fv := isLattice_of_bounds v le_rfl le_rfl
  have hf : IsSquare (OMeara.gram (qk Q Fv) (Pi.basisFun Fv (Fin n))).det := by
    rw [OMeara.basisFun_coe]; exact hsq
  obtain ⟨k, e, he, hQe⟩ := OMeara.exists_orthonormal_of_isUnimodular (qk Q Fv) h2 hstd hU
    (Pi.basisFun Fv (Fin n)) hf
  exact OMeara.exists_lattice_spinorNorm_square (qk Q Fv) h2 (nondegenerate_qk Q v hQ) e he hQe

/-- **92:5 in the coordinate layer**: on a unimodular $L_\mathfrak p$ at a non-dyadic spot with $n \ge 2$,
$\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$. -/
theorem spinorNormsContainUnits_of_isUnimodular (hQ : Q.Nondegenerate) (hn : 2 ≤ n) (L : Lat F n)
    (h2 : IsUnit (2 : 𝔬)) (hU : OMeara.IsUnimodular (qk Q Fv) (loc v L.1)) : SpinorNormsContainUnits Q v L := by
  apply spinorNormsContainUnits_of_omeara Q v hQ L
  intro ε hε
  have hmod : OMeara.IsModular (qk Q Fv) (𝔬 ∙ (1 : Fv)) (loc v L.1) := by
    have : (𝔬 ∙ (1 : Fv)) = 1 := (Submodule.one_eq_span).symm
    rw [this]; exact hU
  have hrk : Module.finrank 𝔬 (loc v L.1) = n := finrank_loc v L
  exact OMeara.exists_hasSpinorNorm_of_isModular (qk Q Fv) h2 (loc_fg v L) hmod (by omega) hε

theorem unit_mem_localSpinorNormSq (hQ : Q.Nondegenerate) {L : Lat F n} (hL : SpinorNormsContainUnits Q v L)
    {u : Fv} (hu : Valued.v u = 1) : sqClassOf u ∈ localSpinorNormSq Q hQ v L := by
  obtain ⟨g, hg, hd, hθ⟩ := hL u hu
  refine (mem_localSpinorNormSq Q hQ).mpr ⟨g, ⟨hg, ?_⟩, hθ⟩
  change g ∈ Tamagawa.soSub Q Fv
  rw [Tamagawa.mem_soSub, ← detHom_val, hd, Units.val_one]

/-- If $a = us^2$ in $F_\mathfrak p$ with $u$ a unit, then $\operatorname{ord}_\mathfrak p a$ is even. -/
theorem exists_valuation_eq_exp_two_mul' {a : F} {u s : Fv} (hu : Valued.v u = 1) (hs : s ≠ 0)
    (h : algebraMap F Fv a = u * s ^ 2) : ∃ k : ℤ, v.valuation F a = WithZero.exp (2 * k) := by
  have hs0 : Valued.v s ≠ 0 := (map_ne_zero _).mpr hs
  refine ⟨WithZero.log (Valued.v s), ?_⟩
  rw [← valued_algebraMap, h, map_mul, hu, one_mul, map_pow, ← WithZero.exp_log hs0, ← WithZero.exp_nsmul]
  congr 1

/-- Equal square classes differ by a square. -/
theorem exists_eq_mul_sq_of_sqClassOf_eq {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sqClassOf a = sqClassOf b) : ∃ t : K, t ≠ 0 ∧ a = b * t ^ 2 := by
  have h1 : sqClassOf (a / b) = 1 := by
    rw [div_eq_mul_inv, sqClassOf_mul ha (inv_ne_zero hb), sqClassOf_inv, h, SqClass.mul_self]
  obtain ⟨t, ht⟩ := (sqClassOf_eq_one_iff (div_ne_zero ha hb)).mp h1
  have ht0 : t ≠ 0 := by rintro rfl; simp [ha, hb] at ht
  refine ⟨t, ht0, ?_⟩
  rw [sq, ← ht]; field_simp

end Local

/-! ### The lattices $K_E$ -/

section Construction

open Classical

variable {Q}

/-- **The data of O'Meara's proof of 102:8**, internal to this file: a cofinite set $W$ of non-dyadic spots
with $J_F = P_DJ_F^W$ at which $\mathfrak o_\mathfrak p^n$ is unimodular and $d$ is a unit, local lattices `top` with
$\theta(O^+) = F_\mathfrak p^\times$ (91:7) and `sq` with $\theta(O) = F_\mathfrak p^{\times 2}$ at the spots of $W$ where
$d$ is a square (92:7). -/
structure Data102_8 (hQ : Q.Nondegenerate) where
  /-- The set of spots $W$. -/
  W : Set (HeightOneSpectrum (𝓞 F))
  /-- The discriminant $d$ of the standard base. -/
  d : F
  /-- The local lattices with $\theta(O^+) = F_\mathfrak p^\times$. -/
  top : ∀ w : HeightOneSpectrum (𝓞 F), Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)
  /-- The local lattices with $\theta(O) = F_\mathfrak p^{\times 2}$. -/
  sq : ∀ w : HeightOneSpectrum (𝓞 F), Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)
  d_ne_zero : d ≠ 0
  d_unit : ∀ w ∈ W, w.valuation F d = 1
  sconv : OMeara.SConventions W
  ideles : ∀ i : J, ∃ p ∈ principalSpinorIdeles Q hQ, ∃ j ∈ OMeara.sIdeles W, i = p * j
  two : ∀ w ∈ W, IsUnit (2 : w.adicCompletionIntegers F)
  unimod : ∀ w ∈ W, OMeara.IsUnimodular (qk Q (w.adicCompletion F))
    (std w : Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F))
  top_lat : ∀ w, (top w).IsLattice (w.adicCompletion F)
  sq_lat : ∀ w, (sq w).IsLattice (w.adicCompletion F)
  top_spin : ∀ w, ∀ c : w.adicCompletion F, c ≠ 0 →
    ∃ σ ∈ OMeara.orthLatPlus (qk Q (w.adicCompletion F)) (top w), OMeara.HasSpinorNorm (qk Q (w.adicCompletion F)) σ c
  sq_spin : ∀ w ∈ W, OMeara.SqAt w d → ∀ σ ∈ OMeara.orthLat (qk Q (w.adicCompletion F)) (sq w),
    ∀ c, OMeara.HasSpinorNorm (qk Q (w.adicCompletion F)) σ c → IsSquare c

namespace Data102_8

variable {hQ : Q.Nondegenerate} (D : Data102_8 hQ)

/-- The local family of $K_E$: `top` off $W$, `sq` on $E$, $\mathfrak o_\mathfrak p^n$ on $W - E$. -/
def fam (E : Finset (HeightOneSpectrum (𝓞 F))) : LocFamily F n where
  M w := if w ∉ D.W then D.top w else if w ∈ E then D.sq w else std w
  isLattice w := by
    split_ifs <;> first | exact D.top_lat w | exact D.sq_lat w | exact isLattice_of_bounds w le_rfl le_rfl
  eventually_std := by
    refine Filter.eventually_cofinite.mpr ((D.sconv.cofinite.union E.finite_toSet).subset ?_)
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_compl_iff, Finset.mem_coe, not_or, not_not] at hc
    simp only [Set.mem_ofPred_eq] at hw
    simp only [hc.1, not_true_eq_false, hc.2, ↓reduceIte] at hw

/-- **The lattice $K_E$.** -/
def lat (E : Finset (HeightOneSpectrum (𝓞 F))) : Lat F n := ⟨(D.fam E).glue, (D.fam E).glue_isLattice⟩

theorem loc_lat_of_not_mem_W (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∉ D.W) : loc w (D.lat E).1 = D.top w := by
  classical
  change loc w (D.fam E).glue = _
  rw [LocFamily.loc_glue]
  change (if w ∉ D.W then D.top w else if w ∈ E then D.sq w else std w) = _
  simp only [hw, not_false_eq_true, ↓reduceIte]

theorem loc_lat_of_mem_E (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ D.W) (hwE : w ∈ E) : loc w (D.lat E).1 = D.sq w := by
  classical
  change loc w (D.fam E).glue = _
  rw [LocFamily.loc_glue]
  change (if w ∉ D.W then D.top w else if w ∈ E then D.sq w else std w) = _
  simp only [hw, not_true_eq_false, hwE, ↓reduceIte]

theorem loc_lat_of_not_mem_E (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ D.W) (hwE : w ∉ E) : loc w (D.lat E).1 = std w := by
  classical
  change loc w (D.fam E).glue = _
  rw [LocFamily.loc_glue]
  change (if w ∉ D.W then D.top w else if w ∈ E then D.sq w else std w) = _
  simp only [hw, not_true_eq_false, hwE, ↓reduceIte]

/-- Off $W$: $\theta(O^+(K_\mathfrak p)) = F_\mathfrak p^\times$. -/
theorem mem_T_of_not_mem_W (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ D.W)
    {c : w.adicCompletion F} (hc : c ≠ 0) : sqClassOf c ∈ localSpinorNormSq Q hQ w (D.lat E) :=
  mem_localSpinorNormSq_of_omeara_top Q w hQ _ (by rw [D.loc_lat_of_not_mem_W E hw]; exact D.top_spin w) hc

/-- On $W - E$: $\theta(O^+(K_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$. -/
theorem unit_mem_T (hn : 2 ≤ n) (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ D.W) (hwE : w ∉ E) {u : w.adicCompletion F} (hu : Valued.v u = 1) :
    sqClassOf u ∈ localSpinorNormSq Q hQ w (D.lat E) :=
  unit_mem_localSpinorNormSq Q w hQ (spinorNormsContainUnits_of_isUnimodular Q w hQ hn _ (D.two w hw)
    (by rw [D.loc_lat_of_not_mem_E E hw hwE]; exact D.unimod w hw)) hu

/-- On $W - E$: $\theta(O^+(K_\mathfrak p)) \subseteq \mathfrak u_\mathfrak p F_\mathfrak p^{\times 2}$. -/
theorem isUnitSqClass_of_mem_T (hn : 1 ≤ n) (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ D.W) (hwE : w ∉ E) {x : SqClass (w.adicCompletion F)}
    (hx : x ∈ localSpinorNormSq Q hQ w (D.lat E)) : IsUnitSqClass w x :=
  isUnitSqClass_of_mem_localSpinorNormSq Q w hQ hn _ (D.two w hw)
    (by rw [D.loc_lat_of_not_mem_E E hw hwE]; exact D.unimod w hw) hx

/-- On $E$: $\theta(O^+(K_\mathfrak p)) = F_\mathfrak p^{\times 2}$. -/
theorem eq_one_of_mem_T (E : Finset (HeightOneSpectrum (𝓞 F))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ D.W) (hwE : w ∈ E) (hd : OMeara.SqAt w D.d) {x : SqClass (w.adicCompletion F)}
    (hx : x ∈ localSpinorNormSq Q hQ w (D.lat E)) : x = 1 :=
  eq_one_of_mem_localSpinorNormSq_of_omeara_sq Q w hQ _
    (by rw [D.loc_lat_of_mem_E E hw hwE]; exact D.sq_spin w hw hd) hx

/-- Adding $\mathfrak q$ to $E$ does not change $K_\mathfrak p$ at $\mathfrak p \ne \mathfrak q$. -/
theorem T_insert_of_ne (E : Finset (HeightOneSpectrum (𝓞 F))) {q w : HeightOneSpectrum (𝓞 F)} (hwq : w ≠ q) :
    localSpinorNormSq Q hQ w (D.lat (insert q E)) = localSpinorNormSq Q hQ w (D.lat E) := by
  apply localSpinorNormSq_congr Q w hQ
  by_cases hw : w ∈ D.W
  · by_cases hwE : w ∈ E
    · rw [D.loc_lat_of_mem_E _ hw (Finset.mem_insert_of_mem hwE), D.loc_lat_of_mem_E _ hw hwE]
    · rw [D.loc_lat_of_not_mem_E _ hw (by simp [hwq, hwE]), D.loc_lat_of_not_mem_E _ hw hwE]
  · rw [D.loc_lat_of_not_mem_W _ hw, D.loc_lat_of_not_mem_W _ hw]

/-- $J_F^{K_E}$. -/
abbrev JE (E : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup J := spinorIdeles Q hQ (D.lat E)

/-- **Step 4: $g^+(K_\emptyset) = 1$**: $J_F^W \subseteq J_F^{K_\emptyset}$ and $J_F = P_DJ_F^W$. -/
theorem index_empty (hn : 2 ≤ n) : (principalSpinorIdeles Q hQ ⊔ D.JE ∅).index = 1 := by
  rw [Subgroup.index_eq_one, eq_top_iff]
  intro i _
  obtain ⟨p, hp, j, hj, rfl⟩ := D.ideles i
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ?_)
  rw [mem_spinorIdeles]
  intro w
  by_cases hw : w ∈ D.W
  · exact D.unit_mem_T hn ∅ hw (Finset.notMem_empty w) (hj w hw)
  · exact D.mem_T_of_not_mem_W ∅ hw (ideleAt_ne_zero j w)

/-- The idèle with component $x$ at $\mathfrak q$ and $1$ elsewhere. -/
def single (q : HeightOneSpectrum (𝓞 F)) {x : q.adicCompletion F} (hx : x ≠ 0) : J :=
  IdeleGroup.ofAdicCompletion (𝓞 F) F q (Units.mk0 x hx)

theorem ideleAt_single_self (q : HeightOneSpectrum (𝓞 F)) {x : q.adicCompletion F} (hx : x ≠ 0) :
    ideleAt (single q hx) q = x := ideleAt_ofAdic_self q _

theorem ideleAt_single_ne (q : HeightOneSpectrum (𝓞 F)) {x : q.adicCompletion F} (hx : x ≠ 0)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ q) : ideleAt (single q hx) w = 1 := ideleAt_ofAdic_ne q w hw _

variable {D}

/-- Adding a spot $\mathfrak q$ of $W$ to $E$ makes $J_F^{K_E}$ smaller. -/
theorem JE_insert_le {E : Finset (HeightOneSpectrum (𝓞 F))} {q : HeightOneSpectrum (𝓞 F)} (hq : q ∈ D.W)
    (hd : OMeara.SqAt q D.d) : D.JE (insert q E) ≤ D.JE E := by
  intro c hc
  rw [mem_spinorIdeles] at hc ⊢
  intro w
  by_cases hwq : w = q
  · subst hwq
    rw [D.eq_one_of_mem_T _ hq (Finset.mem_insert_self _ _) hd (hc w)]
    exact Subgroup.one_mem _
  · rw [← D.T_insert_of_ne E hwq]; exact hc w

/-- **Step 5: adding one spot at most doubles $g^+$**: $(J_F^{K_E} : J_F^{K_{E \cup \mathfrak q}}) \mid 2$. -/
theorem relIndex_JE_insert_dvd_two (hn : 1 ≤ n) {E : Finset (HeightOneSpectrum (𝓞 F))}
    {q : HeightOneSpectrum (𝓞 F)} (hq : q ∈ D.W) (hqE : q ∉ E) (hd : OMeara.SqAt q D.d) :
    (D.JE (insert q E)).relIndex (D.JE E) ∣ 2 := by
  obtain ⟨Δ, hΔu, -, hΔ⟩ := OMeara.exists_nonsquare_unit (D.two q hq)
  set Δv : q.adicCompletion F := algebraMap (q.adicCompletionIntegers F) (q.adicCompletion F) Δ
  have hΔ1 : Valued.v Δv = 1 := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hΔu
  have hΔ0 : Δv ≠ 0 := by intro h; rw [h, map_zero] at hΔ1; exact zero_ne_one hΔ1
  refine relIndex_dvd_two_of (JE_insert_le hq hd) (single q hΔ0) fun c hc => ?_
  have hc' := (mem_spinorIdeles Q hQ).mp hc
  obtain ⟨u, hu, hcu⟩ := D.isUnitSqClass_of_mem_T hn E hq hqE (hc' q)
  let ε : q.adicCompletionIntegers F := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hε : IsUnit ε := by rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hu
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hmem : ∀ c' : J, ideleAt c' q = 1 ∨ sqClassOf (ideleAt c' q) = 1 → (∀ w, w ≠ q → ideleAt c' w = ideleAt c w) →
      c' ∈ D.JE (insert q E) := by
    intro c' hq1 hw
    rw [mem_spinorIdeles]
    intro w
    by_cases hwq : w = q
    · subst hwq
      have : sqClassOf (ideleAt c' w) = 1 := by
        rcases hq1 with h | h
        · rw [h, sqClassOf_one]
        · exact h
      rw [this]; exact Subgroup.one_mem _
    · rw [hw w hwq, D.T_insert_of_ne E hwq]; exact hc' w
  rcases hΔ ε hε with hsq | hsq
  · left
    refine hmem c (Or.inr ?_) fun _ _ => rfl
    rw [hcu, sqClassOf_eq_one_iff hu0]
    obtain ⟨r, hr⟩ := hsq
    exact ⟨r, by rw [show u = ((ε : q.adicCompletionIntegers F) : q.adicCompletion F) from rfl, hr]; simp⟩
  · right
    refine hmem _ (Or.inr ?_) fun w hwq => ?_
    · rw [ideleAt_mul, ideleAt_inv, ideleAt_single_self, sqClassOf_mul (inv_ne_zero hΔ0) (ideleAt_ne_zero c q),
        sqClassOf_inv, hcu, ← sqClassOf_mul hΔ0 hu0, sqClassOf_eq_one_iff (mul_ne_zero hΔ0 hu0)]
      obtain ⟨r, hr⟩ := hsq
      refine ⟨(r : q.adicCompletion F), ?_⟩
      have := congrArg (fun z : q.adicCompletionIntegers F => (z : q.adicCompletion F)) hr
      simp only [MulMemClass.coe_mul] at this
      rw [mul_comm Δv u]
      exact this
    · rw [ideleAt_mul, ideleAt_inv, ideleAt_single_ne q hΔ0 hwq, inv_one, one_mul]

/-- **Step 6: two twin spots change $g^+$**: if $\mathfrak q \ne \mathfrak q'$ are spots of $W - E$ at which $d$ is a
square and at which the same $(W - E)$-units are squares (65:20), then $J_F^{K_E} \not\subseteq
P_DJ_F^{K_{E \cup \{\mathfrak q, \mathfrak q'\}}}$. -/
theorem not_JE_le_sup {E : Finset (HeightOneSpectrum (𝓞 F))} {q q' : HeightOneSpectrum (𝓞 F)} (hn : 2 ≤ n)
    (hqq' : q ≠ q') (hq : q ∈ D.W) (hq' : q' ∈ D.W) (hqE : q ∉ E) (hq'E : q' ∉ E)
    (hE : ∀ w ∈ E, w ∈ D.W ∧ OMeara.SqAt w D.d) (hdq : OMeara.SqAt q D.d) (hdq' : OMeara.SqAt q' D.d)
    (htwin : ∀ δ : F, (∀ w ∈ D.W, w ∉ E → w.valuation F δ = 1) → (OMeara.SqAt q δ ↔ OMeara.SqAt q' δ)) :
    ¬ D.JE E ≤ principalSpinorIdeles Q hQ ⊔ D.JE (insert q (insert q' E)) := by
  obtain ⟨Δ, hΔu, hΔn, -⟩ := OMeara.exists_nonsquare_unit (D.two q hq)
  set Δv : q.adicCompletion F := algebraMap (q.adicCompletionIntegers F) (q.adicCompletion F) Δ
  have hΔ1 : Valued.v Δv = 1 := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hΔu
  have hΔ0 : Δv ≠ 0 := by intro h; rw [h, map_zero] at hΔ1; exact zero_ne_one hΔ1
  set x := single q hΔ0
  have hxJ : x ∈ D.JE E := by
    rw [mem_spinorIdeles]
    intro w
    by_cases hwq : w = q
    · subst hwq
      rw [ideleAt_single_self]
      exact D.unit_mem_T hn E hq hqE hΔ1
    · rw [ideleAt_single_ne q hΔ0 hwq, sqClassOf_one]; exact Subgroup.one_mem _
  intro hle
  obtain ⟨p, hp, j, hj, hpj⟩ := Subgroup.mem_sup.mp (hle hxJ)
  obtain ⟨α, -, rfl⟩ := hp
  set E'' := insert q (insert q' E)
  have hE'' : ∀ w ∈ E'', w ∈ D.W ∧ OMeara.SqAt w D.d := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨hq, hdq⟩
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨hq', hdq'⟩
    · exact hE w hw
  have hj' := (mem_spinorIdeles Q hQ).mp hj
  have hcomp : ∀ w, ideleAt x w = algebraMap F (w.adicCompletion F) (α : F) * ideleAt j w := fun w => by
    rw [← hpj, ideleAt_mul, ideleAt_unitEmbedding]
  have hα0 : (α : F) ≠ 0 := α.ne_zero
  -- `j` is a square on `E''`
  have hjsq : ∀ w ∈ E'', ∃ s : w.adicCompletion F, s ≠ 0 ∧ ideleAt j w = s ^ 2 := by
    intro w hw
    have h1 := D.eq_one_of_mem_T E'' (hE'' w hw).1 hw (hE'' w hw).2 (hj' w)
    obtain ⟨s, hs⟩ := (sqClassOf_eq_one_iff (ideleAt_ne_zero j w)).mp h1
    refine ⟨s, ?_, by rw [hs, pow_two]⟩
    rintro rfl; exact ideleAt_ne_zero j w (by rw [hs, mul_zero])
  -- `α` at a spot `w ≠ q` where `x_w = 1`
  have hαw : ∀ w, w ≠ q → algebraMap F (w.adicCompletion F) (α : F) = (ideleAt j w)⁻¹ := fun w hwq => by
    have := hcomp w
    rw [ideleAt_single_ne q hΔ0 hwq] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  -- even orders on `W`
  have heven : ∀ w ∈ D.W, ∃ k : ℤ, w.valuation F (α : F) = WithZero.exp (2 * k) := by
    intro w hw
    by_cases hwE : w ∈ E''
    · obtain ⟨s, hs0, hs⟩ := hjsq w hwE
      by_cases hwq : w = q
      · subst hwq
        have h := hcomp w
        rw [ideleAt_single_self, hs] at h
        refine exists_valuation_eq_exp_two_mul' w hΔ1 (inv_ne_zero hs0) ?_
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero 2 hs0), h]
      · refine exists_valuation_eq_exp_two_mul' w (u := 1) (by simp) (inv_ne_zero hs0) ?_
        rw [hαw w hwq, hs, one_mul, inv_pow]
    · have hwq : w ≠ q := fun h => hwE (h ▸ Finset.mem_insert_self _ _)
      obtain ⟨u, hu, hju⟩ := D.isUnitSqClass_of_mem_T (by omega) E'' hw hwE (hj' w)
      have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
      obtain ⟨t, ht0, ht⟩ := exists_eq_mul_sq_of_sqClassOf_eq (ideleAt_ne_zero j w) hu0 hju
      refine exists_valuation_eq_exp_two_mul' w (u := u⁻¹) (by rw [map_inv₀, hu, inv_one]) (inv_ne_zero ht0) ?_
      rw [hαw w hwq, ht, mul_inv, inv_pow]
  obtain ⟨β, hβ0, hβ⟩ := OMeara.exists_div_sq_valuation_eq_one D.sconv subset_rfl hα0 heven
  have hδ := htwin ((α : F) / β ^ 2) fun w hw _ => hβ w hw
  have hb : ∀ w : HeightOneSpectrum (𝓞 F), algebraMap F (w.adicCompletion F) β ≠ 0 := fun w =>
    (map_ne_zero _).mpr hβ0
  -- square at `q'`
  have hsq' : OMeara.SqAt q' ((α : F) / β ^ 2) := by
    obtain ⟨s, hs0, hs⟩ := hjsq q' (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine ⟨s⁻¹ / algebraMap F _ β, ?_⟩
    rw [map_div₀, map_pow, hαw q' (Ne.symm hqq'), hs]
    field_simp
  obtain ⟨r, hr⟩ := hδ.mpr hsq'
  obtain ⟨s, hs0, hs⟩ := hjsq q (Finset.mem_insert_self _ _)
  apply hΔn
  apply isSquare_of_isSquare_algebraMap q hΔu
  have h := hcomp q
  rw [ideleAt_single_self, hs] at h
  rw [map_div₀, map_pow, div_eq_iff (pow_ne_zero 2 (hb q))] at hr
  refine ⟨r * algebraMap F _ β * s, ?_⟩
  change Δv = _
  rw [h, hr]
  ring

/-- **Every power of $2$ occurs among the $K_E$** (O'Meara 1973, §102B, proof of 102:8, steps 4–6). -/
theorem exists_index_eq_two_pow (hn : 2 ≤ n) (r : ℕ) :
    ∃ E : Finset (HeightOneSpectrum (𝓞 F)), (∀ w ∈ E, w ∈ D.W ∧ OMeara.SqAt w D.d) ∧
      (principalSpinorIdeles Q hQ ⊔ D.JE E).index = 2 ^ r := by
  classical
  induction r with
  | zero => exact ⟨∅, by simp, by rw [pow_zero]; exact D.index_empty hn⟩
  | succ r ih =>
    obtain ⟨E, hE, hidx⟩ := ih
    set A := principalSpinorIdeles Q hQ
    -- 65:20 for the `(W - E)`-units
    set T : Finset (HeightOneSpectrum (𝓞 F)) := D.sconv.cofinite.toFinset ∪ E with hT
    have hTW : ∀ w, w ∉ T ↔ w ∈ D.W ∧ w ∉ E := fun w => by simp [hT]
    let cU : HN.SUnit (F := F) T := ⟨Units.mk0 D.d D.d_ne_zero, fun w hw =>
      D.d_unit w ((hTW w).mp hw).1⟩
    obtain ⟨q, q', hqq', hqT, hq'T, hdq, hdq', htwin⟩ := OMeara.exists_twin_spots T cU
    obtain ⟨hq, hqE⟩ := (hTW q).mp hqT
    obtain ⟨hq', hq'E⟩ := (hTW q').mp hq'T
    have htwin' : ∀ δ : F, (∀ w ∈ D.W, w ∉ E → w.valuation F δ = 1) →
        (OMeara.SqAt q δ ↔ OMeara.SqAt q' δ) := by
      intro δ hδ
      by_cases hδ0 : δ = 0
      · subst hδ0; simp [OMeara.SqAt]
      · exact htwin ⟨Units.mk0 δ hδ0, fun w hw => hδ w ((hTW w).mp hw).1 ((hTW w).mp hw).2⟩
    set E' := insert q' E
    set E'' := insert q E'
    have hE' : ∀ w ∈ E', w ∈ D.W ∧ OMeara.SqAt w D.d := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hq', hdq'⟩
      · exact hE w hw
    have hE'' : ∀ w ∈ E'', w ∈ D.W ∧ OMeara.SqAt w D.d := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hq, hdq⟩
      · exact hE' w hw
    have hqE' : q ∉ E' := by simp [E', hqq', hqE]
    -- the two steps
    have hle1 : D.JE E' ≤ D.JE E := JE_insert_le hq' hdq'
    have hle2 : D.JE E'' ≤ D.JE E' := JE_insert_le hq hdq
    obtain ⟨hd1, he1⟩ := index_sup_eq_mul A hle1
    obtain ⟨hd2, he2⟩ := index_sup_eq_mul A hle2
    have h1 := hd1.trans (relIndex_JE_insert_dvd_two (by omega) hq' hq'E hdq')
    have h2 := hd2.trans (relIndex_JE_insert_dvd_two (by omega) hq hqE' hdq)
    -- strictness
    have hne : (A ⊔ D.JE E'').relIndex (A ⊔ D.JE E) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro h
      exact not_JE_le_sup hn hqq' hq hq' hqE hq'E hE hdq hdq' htwin' (le_sup_right.trans h)
    have hmul := Subgroup.relIndex_mul_relIndex (A ⊔ D.JE E'') (A ⊔ D.JE E') (A ⊔ D.JE E)
      (sup_le_sup_left hle2 A) (sup_le_sup_left hle1 A)
    have hm1 : (A ⊔ D.JE E').relIndex (A ⊔ D.JE E) = 1 ∨ (A ⊔ D.JE E').relIndex (A ⊔ D.JE E) = 2 := by
      have := Nat.le_of_dvd two_pos h1
      have h0 : (A ⊔ D.JE E').relIndex (A ⊔ D.JE E) ≠ 0 := by
        intro h0; rw [h0] at h1; simp at h1
      omega
    have hm2 : (A ⊔ D.JE E'').relIndex (A ⊔ D.JE E') = 1 ∨ (A ⊔ D.JE E'').relIndex (A ⊔ D.JE E') = 2 := by
      have := Nat.le_of_dvd two_pos h2
      have h0 : (A ⊔ D.JE E'').relIndex (A ⊔ D.JE E') ≠ 0 := by
        intro h0; rw [h0] at h2; simp at h2
      omega
    rcases hm1 with hm1 | hm1
    · refine ⟨E'', hE'', ?_⟩
      have hm2' : (A ⊔ D.JE E'').relIndex (A ⊔ D.JE E') = 2 := by
        rcases hm2 with h | h
        · exfalso; apply hne; rw [← hmul, h, hm1]
        · exact h
      rw [he2, hm2', he1, hm1, one_mul, hidx, pow_succ, mul_comm]
    · refine ⟨E', hE', ?_⟩
      rw [he1, hm1, hidx, pow_succ, mul_comm]

end Data102_8

/-- **Step 1 of O'Meara's proof of 102:8: the data exist** for a regular $V$ with $n \ge 3$. -/
theorem exists_data102_8 (hQ : Q.Nondegenerate) (hn : 3 ≤ n) : Nonempty (Data102_8 hQ) := by
  set G := OMeara.gram (QuadForm.toQuadraticForm Q) (fun i => (Pi.single i 1 : Fin n → F)) with hGdef
  have hG0 : G.det ≠ 0 := det_gram_single_ne_zero Q hQ
  set Θ : Finset F :=
    insert G.det ((Finset.univ.image fun p : Fin n × Fin n => G p.1 p.2).filter (· ≠ 0)) with hΘ
  have hΘ0 : ∀ θ ∈ Θ, θ ≠ 0 := by
    intro θ hθ
    rcases Finset.mem_insert.mp hθ with rfl | h
    · exact hG0
    · exact (Finset.mem_filter.mp h).2
  obtain ⟨S, hS, hΘS, -⟩ := OMeara.exists_sConventions_strong (F := F) F Θ hΘ0
  obtain ⟨T0, hT0⟩ := exists_finite_spots_idele_eq_mul Q hQ hn
  set W : Set (HeightOneSpectrum (𝓞 F)) := S \ (T0 : Set _) with hWdef
  have hWS : W ⊆ S := Set.sdiff_subset
  have hdetW : ∀ w ∈ W, w.valuation F G.det = 1 := fun w hw =>
    hΘS _ (Finset.mem_insert_self _ _) w (hWS hw)
  have hentW : ∀ w ∈ W, ∀ i j, G i j ≠ 0 → w.valuation F (G i j) = 1 := fun w hw i j h =>
    hΘS _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩, h⟩)) w (hWS hw)
  have hideles : ∀ i : J, ∃ p ∈ principalSpinorIdeles Q hQ, ∃ j ∈ OMeara.sIdeles W, i = p * j :=
    hT0 W Set.disjoint_sdiff_left
  have hsconv : OMeara.SConventions W := by
    refine ⟨fun w hw => hS.nondyadic w (hWS hw), ?_, fun i => ?_⟩
    · have : Wᶜ = Sᶜ ∪ (T0 : Set _) := by
        ext w; simp only [hWdef, Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not, Set.mem_union]; tauto
      rw [this]; exact hS.cofinite.union T0.finite_toSet
    · obtain ⟨p, hp, j, hj, h⟩ := hideles i
      exact ⟨p, principalSpinorIdeles_le Q hQ hp, j, hj, h⟩
  have h2W : ∀ w ∈ W, IsUnit (2 : w.adicCompletionIntegers F) := fun w hw =>
    Hanke2011Structure.isUnit_two_of_not_mem w (hS.nondyadic w (hWS hw))
  have hUW : ∀ w ∈ W, OMeara.IsUnimodular (qk Q (w.adicCompletion F))
      (std w : Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)) :=
    fun w hw => isUnimodular_std Q w (by omega) (hentW w hw) (hdetW w hw)
  have hsqw : ∀ w, OMeara.SqAt w G.det → IsSquare (OMeara.gram (qk Q (w.adicCompletion F))
      (fun i => (Pi.single i 1 : Fin n → w.adicCompletion F))).det := by
    intro w hw
    rw [gram_qk_single, show (G.map (algebraMap F (w.adicCompletion F))).det =
      algebraMap F (w.adicCompletion F) G.det from (RingHom.map_det _ G).symm]
    exact hw
  have htop : ∀ w : HeightOneSpectrum (𝓞 F), ∃ M : Submodule (w.adicCompletionIntegers F)
      (Fin n → w.adicCompletion F), M.IsLattice (w.adicCompletion F) ∧ ∀ c : w.adicCompletion F, c ≠ 0 →
        ∃ σ ∈ OMeara.orthLatPlus (qk Q (w.adicCompletion F)) M,
          OMeara.HasSpinorNorm (qk Q (w.adicCompletion F)) σ c := fun w =>
    OMeara.exists_lattice_spinorNorm_eq_top w (qk Q (w.adicCompletion F)) (nondegenerate_qk Q w hQ)
      (by rw [Module.finrank_fin_fun]; exact hn)
  choose top htopL htopS using htop
  have hsq : ∀ w : HeightOneSpectrum (𝓞 F), ∃ M : Submodule (w.adicCompletionIntegers F)
      (Fin n → w.adicCompletion F), M.IsLattice (w.adicCompletion F) ∧
        (w ∈ W → OMeara.SqAt w G.det → ∀ σ ∈ OMeara.orthLat (qk Q (w.adicCompletion F)) M,
          ∀ c, OMeara.HasSpinorNorm (qk Q (w.adicCompletion F)) σ c → IsSquare c) := by
    intro w
    by_cases h : w ∈ W ∧ OMeara.SqAt w G.det
    · obtain ⟨M, hM, hMs⟩ := exists_local_square Q w hQ (h2W w h.1) (hUW w h.1) (hsqw w h.2)
      exact ⟨M, hM, fun _ _ => hMs⟩
    · exact ⟨std w, isLattice_of_bounds w le_rfl le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose sqL hsqL hsqS using hsq
  exact ⟨⟨W, G.det, top, sqL, hG0, hdetW, hsconv, hideles, h2W, hUW, htopL, hsqL, htopS, hsqS⟩⟩

end Construction

/-! ### Theorem 102:8 -/

/-- **O'Meara, Theorem 102:8** (O'Meara 1973, §102B, p. 302): let $V = (F^n, Q)$ be a regular quadratic space over a
number field $F$ (`hQ`) with $n = \dim V \ge 3$. Then

* for every lattice $L$ on $V$, the number $g^+(L)$ of proper spinor genera in $\operatorname{gen}L$
  (`properSpinorGenusNumber`) is of the form $2^r$ with $r \ge 0$, and
* every value of $r$ is obtained by taking a suitable lattice $L$ on $V$: for every $r \in \mathbb N$ there is a
  lattice $L$ on $V$ with $g^+(L) = 2^r$.

$S$ is the set of all finite spots (lattices over $\mathcal O_F$). Unconditional. The first part holds for every $n$
(Corollary 102:8a, `omeara102_8a`). -/
@[kb "omeara1963" "§102B, 102:8, p. 302"]
theorem omeara102_8 (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    (∀ L : Lat F n, ∃ r : ℕ, properSpinorGenusNumber Q L = 2 ^ r) ∧
      ∀ r : ℕ, ∃ L : Lat F n, properSpinorGenusNumber Q L = 2 ^ r := by
  refine ⟨fun L => omeara102_8a hQ L, fun r => ?_⟩
  obtain ⟨D⟩ := exists_data102_8 hQ hn
  obtain ⟨E, -, hE⟩ := D.exists_index_eq_two_pow (by omega) r
  exact ⟨D.lat E, by rw [omeara102_7 hQ hn]; exact hE⟩

end QuadFormsKB.Lattices
