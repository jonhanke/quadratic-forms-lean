/-
# Classification of quadratic forms over every completion of a number field

Let $F$ be a number field and $v$ a place of $F$ (`NFPlace F`). For nondegenerate diagonal forms
$\langle a_0,\dots,a_{n-1}\rangle$ and $\langle b_0,\dots,b_{n-1}\rangle$ with $a_i, b_i \in F^\times$ (same $n$):

* **Finite places** $\mathfrak p$, dyadic included (`LocalClassNF.isometric_finite_iff`): the forms are isometric over
  $F_{\mathfrak p}$ iff $\prod_i a_i / \prod_i b_i$ is a square in $F_{\mathfrak p}$ and Serre's Hasse invariants
  $\varepsilon_{\mathfrak p} = \prod_{i<j}(a_i,a_j)_{\mathfrak p}$ agree (O'Meara 63:20; Serre IV §2.3, Thm. 7, there over
  $\mathbb{Q}_p$; Lam VI.2). The same with O'Meara's $S_{\mathfrak p}$, Cassels' $c_{\mathfrak p}$, Lam's $s_{\mathfrak p}$ or
  Hasse's $\alpha_{\mathfrak p}$ (Shimura) in place of $\varepsilon_{\mathfrak p}$.
* **Real places** $w$ (`LocalClassNF.isometric_real_iff`): isometric over $F_w \cong \mathbb{R}$ iff the two forms have
  the same number of negative entries under the real embedding $F \to \mathbb{R}$ of $w$ (Sylvester's law of inertia
  and its converse).
* **Complex places** $w$ (`LocalClassNF.isometric_complex`): always isometric over $F_w \cong \mathbb{C}$.
* **Uniform statement** (`NFPlace.isometric_iff`, and `NFPlace.isometric_iff_hasseOMeara` etc. for the other
  conventions): at every place $v$, isometric over $F_v$ iff same discriminant square class in $F_v$, same Hasse
  invariant at $v$, and same negative index at $v$ (`NFPlace.negIndex`: the number of negative entries under the real
  embedding at a real place, $0$ at the other places).

**Route.**

* *Finite places.* `HasseIsoNF.localHilbertField_adicCompletion` gives the three Hilbert-symbol axioms
  `PadicClass.LocalHilbertField` at every $F_{\mathfrak p}$ (bimultiplicativity, nondegeneracy, isotropy in rank $5$,
  dyadic included). The classification `PadicClass.isometric_iff_invariants` is proved over any field satisfying these
  axioms (Serre's induction on $n$: split off $a_0$, which the second form represents by the rank $2$/$3$/$\ge 4$
  representation criteria, then Witt cancellation), so it applies verbatim; the $\mathbb{Q}_p$ statement
  `isometric_padic_iff_invariants` is the instance $K = \mathbb{Q}_p$ of the same abstract theorem.
* *Real places.* Transport along $F_w \cong \mathbb{R}$ (`InfinitePlace.Completion.ringEquivRealOfIsReal`). Over
  $\mathbb{R}$: "only if" is Sylvester's law (`HasseIsoNF.negCountR_eq_of_isometric`); "if": scale each entry to
  its sign by $1/\sqrt{|a_i|}$, then permute the signs (`Equiv.ofFiberEquiv`).
* *Complex places.* Every element of $F_w \cong \mathbb{C}$ is a square, so scaling each $a_i$ by a square root of
  $b_i/a_i$ is an isometry.

*Related work.* Tau Ceti (`NumberTheory/LocalField/QuadraticForm/Classification.lean`) classifies quadratic forms over
every nonarchimedean local field with `Invertible (2 : K)`, which in characteristic $0$ includes the dyadic fields, so
the finite-place result itself is there. What is added here: the formulation over the completions of a number field
for forms with entries in $F$ and the repository's Hasse conventions, the archimedean places, and the uniform statement
over `NFPlace F`, all from the repository's own local inputs.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open NumberField IsDedekindDomain

namespace QuadFormsKB

open Finset PadicClass Matrix HasseIsoNF QuadForm

variable {n : ℕ}

namespace LocalClassNF

/-! ### Generic lemmas -/

/-- Scaling every entry of a diagonal form by a nonzero square gives an isometric form: if $b_i = s_i^2 a_i$ with
$s_i \ne 0$, then $\langle a\rangle \cong \langle b\rangle$. -/
theorem isometricIn_diag_of_sq {K : Type*} [Field K] [CharZero K] {a b : Fin n → K} (s : Fin n → K)
    (hs : ∀ i, s i ≠ 0) (h : ∀ i, b i = s i ^ 2 * a i) :
    (QuadForm.diag a).IsometricIn K (QuadForm.diag b) := by
  refine ⟨Matrix.diagonal s, ?_, fun x => ?_⟩
  · rw [det_diagonal]
    exact (prod_ne_zero_iff.mpr fun i _ => hs i).isUnit
  · rw [evalIn_diag_self, evalIn_diag_self]
    refine sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal, h]; ring

/-- The discriminant condition of `PadicClass.isometric_iff_invariants` is "$\prod a / \prod b$ is a square". -/
theorem exists_sq_iff_isSquare_div {K : Type*} [Field K] {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) :
    (∃ t : K, t ≠ 0 ∧ B = t ^ 2 * A) ↔ IsSquare (A / B) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t⁻¹, by field_simp⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
      rcases hs with h | h
      · exact hA h
      · exact hB h
    refine ⟨s⁻¹, inv_ne_zero hs0, ?_⟩
    have : A = s * s * B := by rw [← hs]; field_simp
    rw [this]; field_simp

/-- Isometric diagonal forms have discriminants in the same square class: $\prod a / \prod b$ is a square in $K$. -/
theorem isSquare_div_of_isometric {F K : Type} [Field F] [Field K] [CharZero K] [Algebra F K] (a b : Fin n → F)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i)) := by
  rw [NFPlace.isometricIn_cast] at h
  obtain ⟨t, ht, e⟩ := disc_of_isometric h
  rw [map_div₀, map_prod, map_prod]
  exact (exists_sq_iff_isSquare_div (prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr (ha i))
    (prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr (hb i))).mp ⟨t, ht, e⟩

/-! ### Real diagonal forms -/

/-- The sign vector of a real vector: $-1$ at negative entries, $1$ elsewhere. Internal. -/
noncomputable def signVec (a : Fin n → ℝ) : Fin n → ℝ := fun i => if a i < 0 then -1 else 1

theorem isometric_signVec (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag (signVec a)) := by
  refine isometricIn_diag_of_sq (fun i => (Real.sqrt |a i|)⁻¹) (fun i => ?_) (fun i => ?_)
  · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (abs_pos.mpr (ha i)))
  · have hp : 0 < |a i| := abs_pos.mpr (ha i)
    rw [inv_pow, Real.sq_sqrt hp.le, signVec]
    split_ifs with h
    · rw [abs_of_neg h, inv_neg, neg_mul, inv_mul_cancel₀ (ha i)]
    · rw [abs_of_nonneg (not_lt.mp h), inv_mul_cancel₀ (ha i)]

theorem card_subtype_neg (a : Fin n → ℝ) : Fintype.card {i // decide (a i < 0) = true} = negCountR a := by
  rw [Fintype.card_subtype, HasseIsoNF.negCountR, Finset.card_filter]
  simp

theorem card_subtype_nonneg (a : Fin n → ℝ) :
    Fintype.card {i // decide (a i < 0) = false} = n - negCountR a := by
  rw [← card_subtype_neg a]
  have := Fintype.card_subtype_compl (fun i : Fin n => decide (a i < 0) = true)
  simp only [Bool.not_eq_true, Fintype.card_fin] at this
  rw [← this]

/-- **Classification of real diagonal forms** (Sylvester's law of inertia and its converse): for nonzero real
$a_i, b_i$, $\langle a\rangle \cong \langle b\rangle$ over $\mathbb{R}$ iff they have the same number of negative
entries. -/
theorem isometric_real_vec_iff (a b : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b) ↔ negCountR a = negCountR b := by
  refine ⟨negCountR_eq_of_isometric a b, fun h => ?_⟩
  have e : ∀ c : Bool, {i // decide (b i < 0) = c} ≃ {i // decide (a i < 0) = c} := fun c => by
    apply Fintype.equivOfCardEq
    cases c
    · rw [card_subtype_nonneg, card_subtype_nonneg, h]
    · rw [card_subtype_neg, card_subtype_neg, h]
  set σ := Equiv.ofFiberEquiv e
  have hσ : signVec a ∘ σ = signVec b := by
    funext i
    have hd : decide (a (σ i) < 0) = decide (b i < 0) := Equiv.ofFiberEquiv_map e i
    rw [decide_eq_decide] at hd
    simp only [Function.comp, signVec]
    by_cases hb' : b i < 0
    · simp [hd.mpr hb', hb']
    · simp [mt hd.mp hb', hb']
  have h1 := isometric_signVec a ha
  have h2 := isometric_diag_comp_perm (signVec a) σ
  rw [hσ] at h2
  exact isometricIn_trans ℝ (isometricIn_trans ℝ h1 h2) (isometricIn_symm ℝ (isometric_signVec b hb))

/-! ### The completions of a number field -/

variable {F : Type} [Field F] [NumberField F]

/-- **Classification of quadratic forms over $F_{\mathfrak p}$, at every finite place of a number field, dyadic
included** (O'Meara 63:20; Serre IV §2.3, Thm. 7, there over $\mathbb{Q}_p$; Lam VI.2): for $a_i, b_i \in F^\times$,
$$\langle a_0,\dots,a_{n-1}\rangle \cong \langle b_0,\dots,b_{n-1}\rangle \text{ over } F_{\mathfrak p}
\iff \frac{\prod_i a_i}{\prod_i b_i} \in (F_{\mathfrak p}^\times)^2 \text{ and }
\prod_{i<j}(a_i,a_j)_{\mathfrak p} = \prod_{i<j}(b_i,b_j)_{\mathfrak p}.$$
*Proof.* `localHilbertField_adicCompletion` and the abstract `PadicClass.isometric_iff_invariants`. -/
@[kb "omeara1963" "§63C, 63:20, p. 170"]
theorem isometric_finite_iff (v : HeightOneSpectrum (𝓞 F)) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn (v.adicCompletion F) (QuadForm.diag b) ↔
      IsSquare (algebraMap F (v.adicCompletion F) ((∏ i, a i) / ∏ i, b i)) ∧
        (NFPlace.finite v).hasseSerre a = (NFPlace.finite v).hasseSerre b := by
  have ha' : ∀ i, algebraMap F (v.adicCompletion F) (a i) ≠ 0 := fun i => (map_ne_zero _).mpr (ha i)
  have hb' : ∀ i, algebraMap F (v.adicCompletion F) (b i) ≠ 0 := fun i => (map_ne_zero _).mpr (hb i)
  rw [NFPlace.isometricIn_cast, isometric_iff_invariants (HasseIsoNF.localHilbertField_adicCompletion v) ha' hb',
    exists_sq_iff_isSquare_div (prod_ne_zero_iff.mpr fun i _ => ha' i) (prod_ne_zero_iff.mpr fun i _ => hb' i),
    map_div₀, map_prod, map_prod]
  rfl

/-- The number of negative entries of $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in F$, under the real embedding
$\sigma_w : F \to \mathbb{R}$ of a real place $w$: $\#\{i : \sigma_w(a_i) < 0\}$ (the negative index of inertia of
the form over $F_w \cong \mathbb{R}$). -/
noncomputable def realNegCount (w : InfinitePlace F) (hw : w.IsReal) (a : Fin n → F) : ℕ :=
  (univ.filter fun i => w.embedding_of_isReal hw (a i) < 0).card

/-- **Classification of quadratic forms over $F_w$ at a real place $w$ of a number field** (Sylvester's law of inertia
and its converse; Serre IV §2.4 over $\mathbb{R}$ [unverified locator]): for $a_i, b_i \in F^\times$, $\langle a\rangle \cong \langle b\rangle$
over $F_w \cong \mathbb{R}$ iff $\#\{i : \sigma_w(a_i) < 0\} = \#\{i : \sigma_w(b_i) < 0\}$. -/
@[kb "serre1973" "Ch. IV, §2.4 [unverified]; omeara1963 §61A, 61:1, p. 156 (isometry part)"]
theorem isometric_real_iff (w : InfinitePlace F) (hw : w.IsReal) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn w.Completion (QuadForm.diag b) ↔
      realNegCount w hw a = realNegCount w hw b := by
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hφ : ∀ x : F, φ (algebraMap F w.Completion x) = w.embedding_of_isReal hw x := fun x => by simp [φ]
  have cnt : ∀ c : Fin n → F, realNegCount w hw c = negCountR fun i => φ (algebraMap F w.Completion (c i)) :=
    fun c => by
      rw [realNegCount, negCountR, Finset.card_filter]
      simp only [hφ]
  have hne : ∀ c : Fin n → F, (∀ i, c i ≠ 0) → ∀ i, φ (algebraMap F w.Completion (c i)) ≠ 0 :=
    fun c hc i => (map_ne_zero _).mpr ((map_ne_zero _).mpr (hc i))
  rw [cnt, cnt, ← isometric_real_vec_iff _ _ (hne a ha) (hne b hb), NFPlace.isometricIn_cast]
  constructor
  · exact HasseIsoNF.isometricIn_ringEquiv φ
  · intro h
    have := HasseIsoNF.isometricIn_ringEquiv φ.symm h
    simpa using this

omit [NumberField F] in
/-- Every element of the completion at a complex place is a square. -/
theorem exists_sq_complex {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) : ∃ s, s ^ 2 = x := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (n := 2) (by norm_num)
  exact ⟨e.symm r, by rw [← map_pow, hr, RingEquiv.symm_apply_apply]⟩

/-- **Over $F_w$ at a complex place $w$ of a number field, nondegenerate diagonal forms of the same dimension are
isometric** (every element of $F_w \cong \mathbb{C}$ is a square; Lam II.3 [unverified locator]). -/
@[kb "lam2005" "Ch. II, §3 [unverified]; omeara1963 §61B, p. 156 (complex case)"]
theorem isometric_complex (w : InfinitePlace F) (hw : w.IsComplex) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) : (QuadForm.diag a).IsometricIn w.Completion (QuadForm.diag b) := by
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
  rw [NFPlace.isometricIn_cast]
  choose s hs using fun i => exists_sq_complex hw (algebraMap F w.Completion (b i) / algebraMap F w.Completion (a i))
  have ha' : ∀ i, algebraMap F w.Completion (a i) ≠ 0 := fun i => (map_ne_zero _).mpr (ha i)
  have hb' : ∀ i, algebraMap F w.Completion (b i) ≠ 0 := fun i => (map_ne_zero _).mpr (hb i)
  refine isometricIn_diag_of_sq s (fun i h0 => ?_) (fun i => ?_)
  · have := hs i
    rw [h0] at this
    exact div_ne_zero (hb' i) (ha' i) (by simpa using this.symm)
  · rw [hs i, div_mul_cancel₀ _ (ha' i)]

theorem hs_self_eq_of_isSquare_div {K : Type*} [Field K] [CharZero K] {A B : K} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : IsSquare (A / B)) : hilbertSymbol K A A = hilbertSymbol K B B := by
  obtain ⟨t, ht, e⟩ := (exists_sq_iff_isSquare_div hA hB).mpr h
  rw [e, hs_sq_left _ _ _ ht, hs_sq_right _ _ _ ht]

end LocalClassNF

open LocalClassNF

namespace NFPlace

variable {F : Type} [Field F] [NumberField F]

open Classical in
/-- **The negative index of $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in F$, at a place $v$ of a number field:** at a
real place $w$, the number of negative entries under the real embedding of $w$ (`LocalClassNF.realNegCount`); $0$ at
complex and finite places (where it carries no information). -/
noncomputable def negIndex : NFPlace F → (Fin n → F) → ℕ
  | infinite w, a => if hw : w.IsReal then realNegCount w hw a else 0
  | finite _, _ => 0

/-- **Classification of quadratic forms over every completion of a number field** (O'Meara 63:20 at the finite
places, Sylvester's law at the real places): for a place $v$ of $F$ (real, complex, or finite including dyadic) and
$a_i, b_i \in F^\times$,
$$\langle a_0,\dots,a_{n-1}\rangle \cong \langle b_0,\dots,b_{n-1}\rangle \text{ over } F_v \iff
\frac{\prod_i a_i}{\prod_i b_i} \in (F_v^\times)^2,\quad \varepsilon_v(\langle a\rangle) = \varepsilon_v(\langle b\rangle),
\quad \text{and the negative indices at } v \text{ agree},$$
with Serre's $\varepsilon_v = \prod_{i<j}(a_i,a_j)_v$ (`hasseSerre`) and the negative index `negIndex` (the number of
negative entries under the real embedding at a real place, $0$ elsewhere). At a finite place the third condition is
empty, at a real place it implies the other two, at a complex place all three always hold. -/
@[kb "omeara1963" "§63C, 63:20, p. 170; §61A, 61:1, p. 156 (real places)"]
theorem isometric_iff (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) ∧
        v.hasseSerre a = v.hasseSerre b ∧ v.negIndex a = v.negIndex b := by
  constructor
  · intro h
    refine ⟨?_, hasseSerre_isometric v a b ha hb h, ?_⟩
    · cases v with
      | finite v =>
        have : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
        exact isSquare_div_of_isometric a b ha hb h
      | infinite w =>
        have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
        exact isSquare_div_of_isometric a b ha hb h
    · cases v with
      | finite v => rfl
      | infinite w =>
        by_cases hw : w.IsReal
        · simp only [negIndex, hw, ↓reduceDIte]
          exact (isometric_real_iff w hw a b ha hb).mp h
        · simp only [negIndex, hw, ↓reduceDIte]
  · rintro ⟨hd, hε, hneg⟩
    cases v with
    | finite v => exact (isometric_finite_iff v a b ha hb).mpr ⟨hd, hε⟩
    | infinite w =>
      rcases w.isReal_or_isComplex with hw | hw
      · simp only [negIndex, hw, ↓reduceDIte] at hneg
        exact (isometric_real_iff w hw a b ha hb).mpr hneg
      · exact isometric_complex w hw a b ha hb

theorem hilbert_ne_zero (v : NFPlace F) (x y : F) : v.hilbert x y ≠ 0 := by
  cases v <;> (simp only [NFPlace.hilbert, hilbertSymbol]; split_ifs <;> norm_num)

/-- If the discriminants lie in the same square class of $F_v$, then $(d_a,d_a)_v = (d_b,d_b)_v$. -/
theorem hilbert_diagDet_self_of_isSquare (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) (hd : v.atPlace fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) :
    v.hilbert (diagDet a) (diagDet a) = v.hilbert (diagDet b) (diagDet b) := by
  have hA : (∏ i, a i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hb i
  cases v with
  | infinite w =>
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    have hd' : IsSquare (algebraMap F w.Completion ((∏ i, a i) / ∏ i, b i)) := hd
    rw [map_div₀] at hd'
    exact hs_self_eq_of_isSquare_div ((map_ne_zero _).mpr hA) ((map_ne_zero _).mpr hB) hd'
  | finite v =>
    have : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
    have hd' : IsSquare (algebraMap F (v.adicCompletion F) ((∏ i, a i) / ∏ i, b i)) := hd
    rw [map_div₀] at hd'
    exact hs_self_eq_of_isSquare_div ((map_ne_zero _).mpr hA) ((map_ne_zero _).mpr hB) hd'

/-- Given equal discriminant square classes, O'Meara's $S_v$ agree iff Serre's $\varepsilon_v$ agree. -/
theorem hasseOMeara_eq_iff (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hd : v.atPlace fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) :
    v.hasseOMeara a = v.hasseOMeara b ↔ v.hasseSerre a = v.hasseSerre b := by
  rw [hasseOMeara_eq v a ha, hasseOMeara_eq v b hb, hilbert_diagDet_self_of_isSquare v a b ha hb hd]
  exact ⟨fun h => mul_right_cancel₀ (hilbert_ne_zero v _ _) h, fun h => by rw [h]⟩

/-- **Classification over every completion $F_v$ with O'Meara's Hasse symbol** $S_v = \prod_{i \le j}(a_i,a_j)_v$
(O'Meara 63:20, stated there with $S_{\mathfrak p}$): as `isometric_iff`, with $S_v$ in place of $\varepsilon_v$. -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (with S_p of §63B, p. 167)"]
theorem isometric_iff_hasseOMeara (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) ∧
        v.hasseOMeara a = v.hasseOMeara b ∧ v.negIndex a = v.negIndex b := by
  rw [isometric_iff v a b ha hb]
  exact ⟨fun ⟨hd, hε, hn⟩ => ⟨hd, (hasseOMeara_eq_iff v a b ha hb hd).mpr hε, hn⟩,
    fun ⟨hd, hS, hn⟩ => ⟨hd, (hasseOMeara_eq_iff v a b ha hb hd).mp hS, hn⟩⟩

/-- **Classification over every completion $F_v$ with Hasse's $\alpha_v$ (Shimura §28.13)** (= O'Meara's $S_v$). -/
@[kb "shimura2010" "§28.13, p. 160 (classification: derived)"]
theorem isometric_iff_hasseShimura (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) ∧
        v.hasseShimura a = v.hasseShimura b ∧ v.negIndex a = v.negIndex b :=
  isometric_iff_hasseOMeara v a b ha hb

/-- **Classification over every completion $F_v$ with Cassels' $c_v$** (= Serre's $\varepsilon_v$). -/
@[kb "cassels1978" "Ch. 4, Thm. 1.1, p. 55, and Thm. 1.2, p. 56 (over ℚ_p and ℝ; over F_v derived)"]
theorem isometric_iff_hasseCassels (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) ∧
        v.hasseCassels a = v.hasseCassels b ∧ v.negIndex a = v.negIndex b :=
  isometric_iff v a b ha hb

/-- **Classification over every completion $F_v$ with Lam's $s_v$** (= Serre's $\varepsilon_v$; Lam VI.2). -/
@[kb "lam2005" "Ch. VI, §2 [unverified]"]
theorem isometric_iff_hasseLam (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) ∧
        v.hasseLam a = v.hasseLam b ∧ v.negIndex a = v.negIndex b :=
  isometric_iff v a b ha hb

end NFPlace


/-! ### Bridge to $\mathbb{Q}_p$ -/

/-- Isometry of diagonal forms with rational entries transports along any ring isomorphism of fields of
characteristic $0$ (the two $\mathbb{Q}$-algebra structures agree). Internal. -/
theorem LocalClassNF.isometricIn_ringEquiv_rat {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (f : K ≃+* L) {a b : Fin n → ℚ} (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    (QuadForm.diag a).IsometricIn L (QuadForm.diag b) := by
  rw [NFPlace.isometricIn_cast] at h ⊢
  have hf : ∀ x, f (algebraMap ℚ K x) = algebraMap ℚ L x := fun x => by
    have : algebraMap ℚ L = (f : K →+* L).comp (algebraMap ℚ K) := Subsingleton.elim _ _
    rw [this]; rfl
  simpa only [hf] using isometricIn_ringEquiv f h

/-- **Bridge to $\mathbb{Q}_p$:** for $F = \mathbb{Q}$ and a finite place $v$ with prime $p$, isometry over the
completion $\mathbb{Q}_v$ is isometry over $\mathbb{Q}_p$ (`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`). So
`LocalClassNF.isometric_finite_iff` at $F = \mathbb{Q}$ and `isometric_padic_iff_invariants` classify the same relation
(both are instances of `PadicClass.isometric_iff_invariants`). -/
theorem LocalClassNF.isometricIn_adicCompletion_rat_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a b : Fin n → ℚ) :
    (QuadForm.diag a).IsometricIn (v.adicCompletion ℚ) (QuadForm.diag b) ↔
      (QuadForm.diag a).IsometricIn ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] (QuadForm.diag b) := by
  let e : v.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v
  exact ⟨fun h => LocalClassNF.isometricIn_ringEquiv_rat e h,
    fun h => LocalClassNF.isometricIn_ringEquiv_rat e.symm h⟩

end QuadFormsKB
