/-
# O'Meara §72: existence of forms with prescribed local behaviour, Theorem 72:1

**Setting.** $F$ is a number field. A regular $n$-ary space $U_\mathfrak p$ over the completion $F_\mathfrak p$ is
given by an orthogonal splitting $U_\mathfrak p \cong \langle u_{\mathfrak p,0}, \dots, u_{\mathfrak p,n-1}\rangle$
with $u_{\mathfrak p,i} \in \dot F_\mathfrak p$ (every regular space over a field of characteristic $\ne 2$ has one), as
in `Sec63C.lean`: `u v` at a finite spot $v$ and `uInf w` at an infinite spot $w$ (real or complex). Its discriminant is
$dU_\mathfrak p = \prod_i u_{\mathfrak p,i}$ modulo squares, and its Hasse symbol is $S_\mathfrak pU_\mathfrak p =$
`hasseS` ($\prod_{i \le j} (u_{\mathfrak p,i}, u_{\mathfrak p,j})_\mathfrak p$, §63B, p. 167; at an infinite spot the
same product of real or complex Hilbert symbols). A global space $V$ is a nondegenerate `QuadForm F n`, and
"$V_\mathfrak p \cong U_\mathfrak p$" is isometry over $F_\mathfrak p$ of $V$ (coefficients mapped into $F_\mathfrak p$)
with $\langle u_{\mathfrak p,0}, \dots\rangle$.

**Proves** Theorem 72:1 (pp. 203–205), `exists_global_iff`.
-/
import QuadFormsKB.Literature.OMeara.Sec72Local
import QuadFormsKB.Literature.OMeara.Sec72Approx

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open QuadForm

/-! ### Hilbert-symbol algebra over a field with a multiplicative symbol -/

section Algebra

variable {K : Type*} [Field K] [CharZero K]
  (hmul : ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 → hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c)
include hmul

theorem hs_mul_left' {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol K (a * b) c = hilbertSymbol K a c * hilbertSymbol K b c := by
  rw [hilbertSymbol_comm, hmul _ _ _ hc ha hb, hilbertSymbol_comm K c, hilbertSymbol_comm K c]

theorem hs_self' {a : K} (ha : a ≠ 0) : hilbertSymbol K a a = hilbertSymbol K a (-1) := by
  have h := hilbertSymbol_self_neg K a
  rw [show -a = -1 * a by ring, hmul _ _ _ ha (by norm_num) ha] at h
  rcases PadicClass.hs_pm a (-1 : K) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

omit hmul in
theorem hs_sq_div_right {a b b' : K} (hb' : b' ≠ 0) (h : IsSquare (b / b')) (hb : b ≠ 0) :
    hilbertSymbol K a b = hilbertSymbol K a b' := by
  obtain ⟨t, ht⟩ := h
  have ht0 : t ≠ 0 := by rintro rfl; simp [hb, hb'] at ht
  have : b = t ^ 2 * b' := by rw [sq, ← ht]; field_simp
  rw [this, PadicClass.hs_sq_right _ _ _ ht0]

theorem hs_prod_right' {ι : Type*} (s : Finset ι) {a : K} (ha : a ≠ 0) (b : ι → K) (hb : ∀ i, b i ≠ 0) :
    hilbertSymbol K a (∏ i ∈ s, b i) = ∏ i ∈ s, hilbertSymbol K a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hilbertSymbol_one_right]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, hmul _ _ _ ha (hb j)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hb i), ih]

theorem hs_sq_eq_one' (a b : K) : hilbertSymbol K a b * hilbertSymbol K a b = 1 := by
  rcases PadicClass.hs_pm a b with h | h <;> rw [h] <;> norm_num

/-- O'Meara's Hasse symbol of a binary diagonal form: $S\langle u_0, u_1\rangle = (-u_0u_1, u_0)(u_0u_1, -1)$. -/
theorem hasseS_pair {u₀ u₁ : K} (h₀ : u₀ ≠ 0) (h₁ : u₁ ≠ 0) :
    hasseS K ![u₀, u₁] = hilbertSymbol K (-(u₀ * u₁)) u₀ * hilbertSymbol K (u₀ * u₁) (-1) := by
  have hS : hasseS K ![u₀, u₁] =
      hilbertSymbol K u₀ u₀ * hilbertSymbol K u₀ u₁ * hilbertSymbol K u₁ u₁ := by
    simp [hasseS, Fin.prod_univ_two]
  have hm1 : (-1 : K) ≠ 0 := by norm_num
  have h01 : u₀ * u₁ ≠ 0 := mul_ne_zero h₀ h₁
  rw [hS, hs_self' hmul h₀, hs_self' hmul h₁, hilbertSymbol_comm K (-(u₀ * u₁)),
    show -(u₀ * u₁) = -1 * u₀ * u₁ by ring, hmul _ _ _ h₀ (mul_ne_zero hm1 h₀) h₁,
    hmul _ _ _ h₀ hm1 h₀, hs_mul_left' hmul h₀ h₁ hm1, hs_self' hmul h₀]
  rcases PadicClass.hs_pm u₀ (-1 : K) with b | b <;>
    rcases PadicClass.hs_pm u₀ u₁ with c | c <;> rcases PadicClass.hs_pm u₁ (-1 : K) with e | e <;>
    simp only [b, c, e] <;> norm_num

/-- Binary forms: with $u_0u_1 = d$ modulo squares, $S\langle u_0, u_1\rangle = (-d, u_0)(d, -1)$. -/
theorem hasseS_pair_disc {u₀ u₁ dK : K} (h₀ : u₀ ≠ 0) (h₁ : u₁ ≠ 0) (hd : dK ≠ 0)
    (hsq : IsSquare (u₀ * u₁ / dK)) :
    hasseS K ![u₀, u₁] = hilbertSymbol K (-dK) u₀ * hilbertSymbol K dK (-1) := by
  have h01 : u₀ * u₁ ≠ 0 := mul_ne_zero h₀ h₁
  rw [hasseS_pair hmul h₀ h₁, hilbertSymbol_comm K (-(u₀ * u₁)), hilbertSymbol_comm K (-dK),
    hilbertSymbol_comm K (u₀ * u₁), hilbertSymbol_comm K dK,
    hs_sq_div_right (neg_ne_zero.mpr hd) (by rwa [neg_div_neg_eq]) (neg_ne_zero.mpr h01),
    hs_sq_div_right hd hsq h01]

/-- Binary forms: if $u_0u_1 = d$ modulo squares and $(-d, a) = (-d, u_0)$, then $\langle u_0, u_1\rangle$
represents $a$. -/
theorem representsIn_pair_of_hilbert {u₀ u₁ dK aK : K} (h₀ : u₀ ≠ 0) (h₁ : u₁ ≠ 0) (hd : dK ≠ 0) (ha : aK ≠ 0)
    (hsq : IsSquare (u₀ * u₁ / dK)) (h : hilbertSymbol K (-dK) aK = hilbertSymbol K (-dK) u₀) :
    (diag ![u₀, u₁]).RepresentsIn K aK := by
  have h01 : u₀ * u₁ ≠ 0 := mul_ne_zero h₀ h₁
  rw [diag_pair_representsIn_iff h₀ h₁ ha,
    hs_sq_div_right (neg_ne_zero.mpr hd) (by rwa [neg_div_neg_eq]) (neg_ne_zero.mpr h01),
    hs_mul_left' hmul ha h₀ (neg_ne_zero.mpr hd), hilbertSymbol_comm K aK, hilbertSymbol_comm K u₀, h]
  exact hs_sq_eq_one' hmul _ _

/-- **The induction step at one spot:** if $U \cong \langle a\rangle \perp \langle b\rangle$ with $dU = d$ and
$SU = S(\langle a\rangle \perp \langle b\rangle)$, then $d\langle b\rangle = da$ and
$S\langle b\rangle = SU \cdot (a, d)$. -/
theorem step_local {m : ℕ} {uK : Fin (m + 1) → K} {aK dK : K} {b : Fin m → K} (hu : ∀ i, uK i ≠ 0)
    (ha : aK ≠ 0) (hd : dK ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hiso : (diag uK).IsometricIn K (diag (Fin.cons aK b))) (hdisc : IsSquare ((∏ i, uK i) / dK))
    (hS : hasseS K uK = hasseS K (Fin.cons aK b : Fin (m + 1) → K)) :
    IsSquare ((∏ i, b i) / (dK * aK)) ∧ hasseS K b = hasseS K uK * hilbertSymbol K aK dK := by
  have hcons : ∀ i, (Fin.cons aK b : Fin (m + 1) → K) i ≠ 0 := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [ha, hb]
  have hpu : (∏ i, uK i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hu i
  have hpb : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  have h1 := isSquare_prod_div_of_isometricIn hu hcons hiso
  rw [Fin.prod_cons] at h1
  have hdisc' : IsSquare ((∏ i, b i) / (dK * aK)) := by
    have e : (∏ i, b i) / (dK * aK) =
        ((∏ i, uK i) / dK) * ((∏ i, uK i) / (aK * ∏ i, b i))⁻¹ * (aK⁻¹) ^ 2 := by
      field_simp
    rw [e]
    exact (hdisc.mul h1.inv).mul (IsSquare.sq _)
  refine ⟨hdisc', ?_⟩
  rw [hS, hasseS_cons, ← hs_prod_right' hmul _ ha _ hb,
    hs_sq_div_right (mul_ne_zero hd ha) hdisc' hpb, hmul _ _ _ ha hd ha, hs_self' hmul ha]
  have e1 := hs_sq_eq_one' hmul aK (-1)
  rcases PadicClass.hs_pm aK (-1 : K) with x | x <;> rcases PadicClass.hs_pm aK dK with y | y <;>
    rcases hasseS_pm b with z | z <;> simp only [x, y, z] <;> norm_num

end Algebra

theorem representsIn_of_isSquare_div {K : Type*} [Field K] [CharZero K] {m : ℕ} {u : Fin (m + 1) → K} (hu0 : u 0 ≠ 0) {x : K}
    (h : IsSquare (x / u 0)) : (diag u).RepresentsIn K x := by
  obtain ⟨t, ht⟩ := h
  rw [PadicClass.representsIn_diag_iff]
  refine ⟨Pi.single 0 t, ?_⟩
  rw [Fintype.sum_eq_single 0 (fun i hi => by simp [hi])]
  simp only [Pi.single_eq_same]
  rw [sq, ← ht]; field_simp

/-- A $\pm 1$-valued function with finitely many $-1$'s and finite product $1$ has an even number of $-1$'s. -/
theorem even_of_finprod_eq_one {P : Type*} (s : P → ℤ) (hpm : ∀ v, s v = 1 ∨ s v = -1)
    (hF : {v | s v = -1}.Finite) (h : ∏ᶠ v, s v = 1) : Even {v | s v = -1}.ncard := by
  have hms : Function.mulSupport s = {v | s v = -1} := by
    ext v
    rcases hpm v with h | h <;> simp [Function.mem_mulSupport, h]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)] at h
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : s v = -1))] at h
  rw [Finset.prod_const, neg_one_pow_eq_one_iff_even (by decide)] at h
  rwa [← Set.ncard_eq_toFinset_card _ hF] at h

variable {F : Type} [Field F] [NumberField F]

instance charZero_completion (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F w.Completion).injective

theorem hmul_finite (v : HeightOneSpectrum (𝓞 F)) : ∀ a b c : v.adicCompletion F, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    hilbertSymbol _ a (b * c) = hilbertSymbol _ a b * hilbertSymbol _ a c :=
  fun _ _ _ ha hb hc => hilbertSymbol_mul_right_finite v ha hb hc

theorem hmul_infinite (w : InfinitePlace F) : ∀ a b c : w.Completion, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    hilbertSymbol _ a (b * c) = hilbertSymbol _ a b * hilbertSymbol _ a c :=
  fun _ _ _ ha hb hc => hilbertSymbol_mul_right_infinite w ha hb hc

theorem hasFiniteMulSupport_hilbert_finite {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) => (NFPlace.finite v).hilbert x y) := by
  have h := (NFPlace.finprod_hilbert x y hx hy).1
  exact Set.Finite.preimage (fun a _ b _ hab => by cases hab; rfl) h

/-- **Twisting local Hasse symbols by a global Hilbert symbol** keeps conditions (2) and (3) of 72:1: if
$S_\mathfrak p = 1$ for almost all finite $\mathfrak p$, then so is $S_\mathfrak p (x, y)_\mathfrak p$, and the
products over all spots agree (Hilbert's reciprocity law). -/
theorem prod_mul_hilbert (s : HeightOneSpectrum (𝓞 F) → ℤ) (sInf : InfinitePlace F → ℤ)
    (hs : {v | s v ≠ 1}.Finite) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    {v | s v * (NFPlace.finite v).hilbert x y ≠ 1}.Finite ∧
      (∏ᶠ v, s v * (NFPlace.finite v).hilbert x y) * ∏ w, sInf w * (NFPlace.infinite w).hilbert x y =
        (∏ᶠ v, s v) * ∏ w, sInf w := by
  have hh := hasFiniteMulSupport_hilbert_finite (F := F) hx hy
  have hs' : Function.HasFiniteMulSupport s := hs
  refine ⟨(hs.union hh).subset fun v hv => ?_, ?_⟩
  · by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Function.mem_mulSupport] at hc hv
    exact hv (by rw [hc.1, hc.2, mul_one])
  · rw [finprod_mul_distrib hs' hh, Finset.prod_mul_distrib]
    have hall := NFPlace.finprod_hilbert x y hx hy
    rw [finprod_nfPlace _ hall.1] at hall
    calc (∏ᶠ v, s v) * (∏ᶠ v, (NFPlace.finite v).hilbert x y) *
          ((∏ w, sInf w) * ∏ w, (NFPlace.infinite w).hilbert x y)
        = (∏ᶠ v, s v) * (∏ w, sInf w) * ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert x y) *
          ∏ w, (NFPlace.infinite w).hilbert x y) := by ring
      _ = _ := by rw [hall.2, mul_one]

/-! ### Sufficiency -/

/-- **The conditions (1)–(3) of Theorem 72:1** for the local data `u`, `uInf`, with $d \in \dot F$ the global
discriminant of condition (1). Internal to the proof of `exists_global_iff`. -/
structure LocalConds (n : ℕ) (u : (v : HeightOneSpectrum (𝓞 F)) → Fin n → v.adicCompletion F)
    (uInf : (w : InfinitePlace F) → Fin n → w.Completion) (d : F) : Prop where
  ne : d ≠ 0
  disc : ∀ v, IsSquare ((∏ i, u v i) / algebraMap F (v.adicCompletion F) d)
  discInf : ∀ w, IsSquare ((∏ i, uInf w i) / algebraMap F w.Completion d)
  fin : {v : HeightOneSpectrum (𝓞 F) | hasseS (v.adicCompletion F) (u v) ≠ 1}.Finite
  prod : (∏ᶠ v, hasseS (v.adicCompletion F) (u v)) * ∏ w, hasseS w.Completion (uInf w) = 1

theorem isSquare_inv_div {K : Type*} [Field K] {x y : K} (h : IsSquare (x / y)) : IsSquare (y / x) := by
  rw [← inv_div]; exact h.inv

theorem commonValue_one (u : (v : HeightOneSpectrum (𝓞 F)) → Fin 1 → v.adicCompletion F) (hu : ∀ v i, u v i ≠ 0)
    (uInf : (w : InfinitePlace F) → Fin 1 → w.Completion) (huInf : ∀ w i, uInf w i ≠ 0) {d : F}
    (hc : LocalConds 1 u uInf d) :
    ∃ a : F, a ≠ 0 ∧ (∀ v, (diag (u v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ a)) ∧
      ∀ w, (diag (uInf w)).RepresentsIn w.Completion (algebraMap F _ a) := by
  refine ⟨d, hc.ne, fun v => ?_, fun w => ?_⟩
  · have h := hc.disc v
    rw [Fin.prod_univ_one] at h
    exact representsIn_of_isSquare_div (hu v 0) (isSquare_inv_div h)
  · have h := hc.discInf w
    rw [Fin.prod_univ_one] at h
    exact representsIn_of_isSquare_div (huInf w 0) (isSquare_inv_div h)

theorem commonValue_two (u : (v : HeightOneSpectrum (𝓞 F)) → Fin 2 → v.adicCompletion F) (hu : ∀ v i, u v i ≠ 0)
    (uInf : (w : InfinitePlace F) → Fin 2 → w.Completion) (huInf : ∀ w i, uInf w i ≠ 0) {d : F}
    (hc : LocalConds 2 u uInf d) :
    ∃ a : F, a ≠ 0 ∧ (∀ v, (diag (u v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ a)) ∧
      ∀ w, (diag (uInf w)).RepresentsIn w.Completion (algebraMap F _ a) := by
  classical
  have hd := hc.ne
  have hD : -d ≠ 0 := neg_ne_zero.mpr hd
  -- the prescribed symbols `ε_𝔭 = (-d, u_{𝔭,0})_𝔭`
  let ε : NFPlace F → ℤ
    | .finite v => hilbertSymbol (v.adicCompletion F) (algebraMap F _ (-d)) (u v 0)
    | .infinite w => hilbertSymbol w.Completion (algebraMap F _ (-d)) (uInf w 0)
  have hdv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) d ≠ 0 := fun v =>
    (map_ne_zero _).mpr hd
  have hdw : ∀ w : InfinitePlace F, algebraMap F w.Completion d ≠ 0 := fun w => (map_ne_zero _).mpr hd
  have hsqv : ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (u v 0 * u v 1 / algebraMap F (v.adicCompletion F) d) := fun v => by
    simpa [Fin.prod_univ_two] using hc.disc v
  have hsqw : ∀ w : InfinitePlace F, IsSquare (uInf w 0 * uInf w 1 / algebraMap F w.Completion d) := fun w => by
    simpa [Fin.prod_univ_two] using hc.discInf w
  have hm1 : ∀ (K : Type) [Field K] [Algebra F K], algebraMap F K (-1) = -1 := fun K _ _ => by simp
  -- `ε_𝔭 = S_𝔭 U_𝔭 · (d, -1)_𝔭`
  have hεv : ∀ v, ε (.finite v) = hasseS _ (u v) * (NFPlace.finite v).hilbert d (-1) := by
    intro v
    have e : u v = ![u v 0, u v 1] := PadicClass.eq_vec_two _
    rw [e, hasseS_pair_disc (hmul_finite v) (hu v 0) (hu v 1) (hdv v) (hsqv v)]
    simp only [ε, NFPlace.hilbert, map_neg, hm1]
    rw [mul_assoc, hs_sq_eq_one' (hmul_finite v), mul_one]
  have hεw : ∀ w, ε (.infinite w) = hasseS _ (uInf w) * (NFPlace.infinite w).hilbert d (-1) := by
    intro w
    have e : uInf w = ![uInf w 0, uInf w 1] := PadicClass.eq_vec_two _
    rw [e, hasseS_pair_disc (hmul_infinite w) (huInf w 0) (huInf w 1) (hdw w) (hsqw w)]
    simp only [ε, NFPlace.hilbert, map_neg, hm1]
    rw [mul_assoc, hs_sq_eq_one' (hmul_infinite w), mul_one]
  have hεpm : ∀ v, ε v = 1 ∨ ε v = -1 := fun v => by
    cases v <;> exact PadicClass.hs_pm _ _
  obtain ⟨hfin, hprod⟩ := prod_mul_hilbert (fun v => hasseS _ (u v)) (fun w => hasseS _ (uInf w)) hc.fin hd
    (by norm_num : (-1 : F) ≠ 0)
  have hεfin : {v : NFPlace F | ε v = -1}.Finite := by
    refine ((hfin.image NFPlace.finite).union (Set.finite_range NFPlace.infinite)).subset ?_
    intro v hv
    cases v with
    | finite v =>
      left
      refine ⟨v, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [← hεv, hv]; norm_num
    | infinite w => exact Or.inr ⟨w, rfl⟩
  have hεsupp : Function.HasFiniteMulSupport ε := by
    refine hεfin.subset fun v hv => ?_
    rcases hεpm v with h | h
    · exact absurd h hv
    · exact h
  have hεprod : ∏ᶠ v, ε v = 1 := by
    rw [finprod_nfPlace _ hεsupp]
    simp only [hεv, hεw]
    rw [hprod, hc.prod]
  obtain ⟨a, ha, hav⟩ := PresNF.exists_prescribed_hilbert (ι := Unit) (fun _ => -d) (fun _ => hD)
    (fun _ v => ε v) (fun _ v => hεpm v) (by simpa using hεfin)
    (fun _ => even_of_finprod_eq_one ε hεpm hεfin hεprod)
    (by
      intro v
      cases v with
      | finite v => exact ⟨u v 0, hu v 0, fun _ => rfl⟩
      | infinite w => exact ⟨uInf w 0, huInf w 0, fun _ => rfl⟩)
  refine ⟨a, ha, fun v => ?_, fun w => ?_⟩
  · rw [PadicClass.eq_vec_two (u v)]
    refine representsIn_pair_of_hilbert (hmul_finite v) (hu v 0) (hu v 1) (hdv v) ((map_ne_zero _).mpr ha)
      (hsqv v) ?_
    have h1 := hav () (.finite v)
    have e1 : (NFPlace.finite v).hilbert (-d) a =
        hilbertSymbol _ (-algebraMap F (v.adicCompletion F) d) (algebraMap F _ a) := by
      show hilbertSymbol _ (algebraMap F _ (-d)) _ = _; rw [map_neg]
    have e2 : ε (.finite v) = hilbertSymbol _ (-algebraMap F (v.adicCompletion F) d) (u v 0) := by
      show hilbertSymbol _ (algebraMap F _ (-d)) _ = _; rw [map_neg]
    rw [← e1, h1, e2]
  · rw [PadicClass.eq_vec_two (uInf w)]
    refine representsIn_pair_of_hilbert (hmul_infinite w) (huInf w 0) (huInf w 1) (hdw w)
      ((map_ne_zero _).mpr ha) (hsqw w) ?_
    have h1 := hav () (.infinite w)
    have e1 : (NFPlace.infinite w).hilbert (-d) a =
        hilbertSymbol _ (-algebraMap F w.Completion d) (algebraMap F _ a) := by
      show hilbertSymbol _ (algebraMap F _ (-d)) _ = _; rw [map_neg]
    have e2 : ε (.infinite w) = hilbertSymbol _ (-algebraMap F w.Completion d) (uInf w 0) := by
      show hilbertSymbol _ (algebraMap F _ (-d)) _ = _; rw [map_neg]
    rw [← e1, h1, e2]

theorem commonValue_ge_three {m : ℕ} (u : (v : HeightOneSpectrum (𝓞 F)) → Fin (m + 3) → v.adicCompletion F)
    (hu : ∀ v i, u v i ≠ 0) (uInf : (w : InfinitePlace F) → Fin (m + 3) → w.Completion)
    (huInf : ∀ w i, uInf w i ≠ 0) {d : F} (hc : LocalConds (m + 3) u uInf d) :
    ∃ a : F, a ≠ 0 ∧ (∀ v, (diag (u v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ a)) ∧
      ∀ w, (diag (uInf w)).RepresentsIn w.Completion (algebraMap F _ a) := by
  classical
  set T : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | (2 : 𝓞 F) ∈ v.asIdeal ∨ v.valuation F d ≠ 1 ∨ hasseS (v.adicCompletion F) (u v) ≠ 1}
  have hT : T.Finite := by
    refine ((NFLocal.finite_bad_places_nf 1 ![d] (fun i => by fin_cases i; exact hc.ne)).union hc.fin).subset ?_
    intro v hv
    simp only [T, Set.mem_ofPred_eq] at hv
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases hv with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨0, by simpa using h⟩)
    · exact Or.inr h
  obtain ⟨a, ha, hav, haw⟩ := exists_approx_sq hT.toFinset (fun v => u v 0) (fun v => hu v 0)
    (fun w => uInf w 0) (fun w => huInf w 0)
  refine ⟨a, ha, fun v => ?_, fun w => representsIn_of_isSquare_div (huInf w 0) (haw w)⟩
  by_cases hv : v ∈ T
  · exact representsIn_of_isSquare_div (hu v 0) (hav v (by simpa using hv))
  · simp only [T, Set.mem_ofPred_eq, not_or, not_not] at hv
    exact representsIn_of_good v hv.1 (by omega) (hu v) hv.2.1 (hc.disc v) hv.2.2 ((map_ne_zero _).mpr ha)

theorem cons_ne_zero' {K : Type*} [Field K] {m : ℕ} {x : K} (hx : x ≠ 0) {b : Fin m → K} (hb : ∀ i, b i ≠ 0) :
    ∀ i, (Fin.cons x b : Fin (m + 1) → K) i ≠ 0 := fun i => by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hx, hb]

theorem map_cons_eq {K : Type*} [Field K] [Algebra F K] {m : ℕ} (a : F) (c : Fin m → F) :
    (fun i => algebraMap F K ((Fin.cons a c : Fin (m + 1) → F) i)) =
      Fin.cons (algebraMap F K a) (fun i => algebraMap F K (c i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Sufficiency in Theorem 72:1**, with a diagonal global form: under conditions (1)–(3) there are
$c_0, \dots, c_{n-1} \in \dot F$ with $\langle c_0, \dots, c_{n-1}\rangle \cong U_\mathfrak p$ at every spot. -/
theorem exists_diag_of_localConds : ∀ (n : ℕ) (u : (v : HeightOneSpectrum (𝓞 F)) → Fin n → v.adicCompletion F)
    (_hu : ∀ v i, u v i ≠ 0) (uInf : (w : InfinitePlace F) → Fin n → w.Completion) (_huInf : ∀ w i, uInf w i ≠ 0)
    (d : F) (_hc : LocalConds n u uInf d),
    ∃ c : Fin n → F, (∀ i, c i ≠ 0) ∧
      (∀ v, (diag fun i => algebraMap F (v.adicCompletion F) (c i)).IsometricIn (v.adicCompletion F) (diag (u v))) ∧
      ∀ w, (diag fun i => algebraMap F w.Completion (c i)).IsometricIn w.Completion (diag (uInf w)) := by
  intro n
  induction n with
  | zero =>
    intro u _ uInf _ d _
    refine ⟨Fin.elim0, fun i => i.elim0, fun v => ?_, fun w => ?_⟩
    · rw [show (fun i : Fin 0 => algebraMap F (v.adicCompletion F) (Fin.elim0 i)) = u v from
        funext fun i => i.elim0]
      exact QuadForm.isometricIn_refl _ _
    · rw [show (fun i : Fin 0 => algebraMap F w.Completion (Fin.elim0 i)) = uInf w from funext fun i => i.elim0]
      exact QuadForm.isometricIn_refl _ _
  | succ m ih =>
    intro u hu uInf huInf d hc
    -- a common value `a` of all the `U_𝔭`
    obtain ⟨a, ha, hrep, hrepInf⟩ : ∃ a : F, a ≠ 0 ∧
        (∀ v, (diag (u v)).RepresentsIn (v.adicCompletion F) (algebraMap F _ a)) ∧
        ∀ w, (diag (uInf w)).RepresentsIn w.Completion (algebraMap F _ a) := by
      rcases m with _ | _ | m
      · exact commonValue_one u hu uInf huInf hc
      · exact commonValue_two u hu uInf huInf hc
      · exact commonValue_ge_three u hu uInf huInf hc
    have hav : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) a ≠ 0 :=
      fun v => (map_ne_zero _).mpr ha
    have haw : ∀ w : InfinitePlace F, algebraMap F w.Completion a ≠ 0 := fun w => (map_ne_zero _).mpr ha
    have hdv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) d ≠ 0 :=
      fun v => (map_ne_zero _).mpr hc.ne
    have hdw : ∀ w : InfinitePlace F, algebraMap F w.Completion d ≠ 0 := fun w => (map_ne_zero _).mpr hc.ne
    -- split off `⟨a⟩` at every spot
    choose b hb hbiso using fun v => exists_isometricIn_cons_of_representsIn (hu v) (hav v) (hrep v)
    choose bInf hbInf hbisoInf using fun w =>
      exists_isometricIn_cons_of_representsIn (huInf w) (haw w) (hrepInf w)
    have hstep : ∀ v : HeightOneSpectrum (𝓞 F), IsSquare ((∏ i, b v i) /
        (algebraMap F (v.adicCompletion F) d * algebraMap F _ a)) ∧
        hasseS _ (b v) = hasseS _ (u v) * (NFPlace.finite v).hilbert a d := fun v =>
      step_local (hmul_finite v) (hu v) (hav v) (hdv v) (hb v) (hbiso v) (hc.disc v)
        (hasseS_eq_of_isometric v (hu v) (cons_ne_zero' (hav v) (hb v)) (hbiso v))
    have hstepInf : ∀ w : InfinitePlace F, IsSquare ((∏ i, bInf w i) /
        (algebraMap F w.Completion d * algebraMap F _ a)) ∧
        hasseS _ (bInf w) = hasseS _ (uInf w) * (NFPlace.infinite w).hilbert a d := fun w =>
      step_local (hmul_infinite w) (huInf w) (haw w) (hdw w) (hbInf w) (hbisoInf w) (hc.discInf w)
        (hasseS_eq_of_isometricIn_infinite w (huInf w) (cons_ne_zero' (haw w) (hbInf w)) (hbisoInf w))
    obtain ⟨hfin, hprod⟩ := prod_mul_hilbert (fun v => hasseS _ (u v)) (fun w => hasseS _ (uInf w)) hc.fin ha
      hc.ne
    have hc' : LocalConds m b bInf (d * a) := by
      refine ⟨mul_ne_zero hc.ne ha, fun v => ?_, fun w => ?_, ?_, ?_⟩
      · rw [map_mul]; exact (hstep v).1
      · rw [map_mul]; exact (hstepInf w).1
      · simpa only [(hstep _).2] using hfin
      · simp only [(hstep _).2, (hstepInf _).2]
        rw [hprod, hc.prod]
    obtain ⟨c, hc0, hcv, hcw⟩ := ih b hb bInf hbInf (d * a) hc'
    refine ⟨Fin.cons a c, cons_ne_zero' ha hc0, fun v => ?_, fun w => ?_⟩
    · rw [map_cons_eq]
      exact QuadForm.isometricIn_trans _ (isometricIn_diag_cons _ (hcv v))
        (QuadForm.isometricIn_symm _ (hbiso v))
    · rw [map_cons_eq]
      exact QuadForm.isometricIn_trans _ (isometricIn_diag_cons _ (hcw w))
        (QuadForm.isometricIn_symm _ (hbisoInf w))

theorem evalIn_map_algebraMap {n : ℕ} (K : Type*) [Field K] [Algebra F K] (Q : QuadForm F n) (x : Fin n → K) :
    (Q.map (algebraMap F K)).evalIn K x = Q.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem isometricIn_map_of_isometricIn {n : ℕ} (K : Type*) [Field K] [Algebra F K] {Q Q' : QuadForm F n}
    (h : Q.IsometricIn K Q') : (Q.map (algebraMap F K)).IsometricIn K (Q'.map (algebraMap F K)) := by
  obtain ⟨P, hP, hx⟩ := h
  exact ⟨P, hP, fun x => by rw [evalIn_map_algebraMap, evalIn_map_algebraMap, hx]⟩

/-- **Theorem 72:1** (O'Meara 1963, pp. 203–205): a regular $n$-ary space $U_\mathfrak p$ is given over each
completion $F_\mathfrak p$ of the number field $F$ (diagonal coefficients `u v` at the finite spots and `uInf w` at the
infinite spots). There is an $n$-ary space $V$ over $F$ with $V_\mathfrak p \cong U_\mathfrak p$ for all $\mathfrak p$
if and only if
1. there is a $d \in \dot F$ with $dU_\mathfrak p = d$ (modulo squares) for all $\mathfrak p$,
2. $S_\mathfrak pU_\mathfrak p = 1$ for almost all $\mathfrak p$,
3. $\prod_{\mathfrak p \in \Omega} S_\mathfrak pU_\mathfrak p = 1$ (the finite product over the finite spots times the
   product over the infinite spots).

O'Meara's proof of sufficiency approximates the $U_\mathfrak p$ at finitely many spots, then corrects the Hasse symbols
at an even set of spots with two planes from 71:19 and the representation theorems 63:21 and 66:3. The proof here
splits off a common value instead: for $n \ge 3$ a value $a \in F$ represented by every $U_\mathfrak p$ (weak
approximation at the finitely many spots where $U_\mathfrak p$ need not be isotropic), and for $n = 2$ a value given by
the existence of elements with prescribed Hilbert symbols (71:19, `PresNF.exists_prescribed_hilbert`), and inducts on
$n$. -/
@[kb "omeara1963" "§72, 72:1, pp. 203–205"]
theorem exists_global_iff (n : ℕ) (u : (v : HeightOneSpectrum (𝓞 F)) → Fin n → v.adicCompletion F)
    (hu : ∀ v i, u v i ≠ 0) (uInf : (w : InfinitePlace F) → Fin n → w.Completion) (huInf : ∀ w i, uInf w i ≠ 0) :
    (∃ V : QuadForm F n, V.Nondegenerate ∧
      (∀ v, (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F) (diag (u v))) ∧
      ∀ w, (V.map (algebraMap F w.Completion)).IsometricIn w.Completion (diag (uInf w))) ↔
    ((∃ d : F, d ≠ 0 ∧ (∀ v, IsSquare ((∏ i, u v i) / algebraMap F (v.adicCompletion F) d)) ∧
        ∀ w, IsSquare ((∏ i, uInf w i) / algebraMap F w.Completion d)) ∧
      {v : HeightOneSpectrum (𝓞 F) | hasseS (v.adicCompletion F) (u v) ≠ 1}.Finite ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), hasseS (v.adicCompletion F) (u v)) *
        ∏ w : InfinitePlace F, hasseS w.Completion (uInf w) = 1) := by
  constructor
  · rintro ⟨V, hV, hiso, hisoInf⟩
    obtain ⟨c, hc, hVc⟩ := FieldGen.exists_isometric_diag V hV
    have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
        (diag fun i => algebraMap F (v.adicCompletion F) (c i)).IsometricIn (v.adicCompletion F) (diag (u v)) := by
      intro v
      rw [← map_diag']
      exact QuadForm.isometricIn_trans _ (isometricIn_map_of_isometricIn _
        (QuadForm.isometricIn_symm _ (FieldGen.isometricIn_of_base _ hVc))) (hiso v)
    have hlocInf : ∀ w : InfinitePlace F,
        (diag fun i => algebraMap F w.Completion (c i)).IsometricIn w.Completion (diag (uInf w)) := by
      intro w
      rw [← map_diag']
      exact QuadForm.isometricIn_trans _ (isometricIn_map_of_isometricIn _
        (QuadForm.isometricIn_symm _ (FieldGen.isometricIn_of_base _ hVc))) (hisoInf w)
    have hcv : ∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (v.adicCompletion F) (c i) ≠ 0 :=
      fun v i => (map_ne_zero _).mpr (hc i)
    have hcw : ∀ w : InfinitePlace F, ∀ i, algebraMap F w.Completion (c i) ≠ 0 :=
      fun w i => (map_ne_zero _).mpr (hc i)
    have hS : ∀ v : HeightOneSpectrum (𝓞 F), hasseS _ (u v) = (NFPlace.finite v).hasseOMeara c := fun v => by
      rw [hasseOMeara_finite_eq_hasseS, hasseS_eq_of_isometric v (hcv v) (hu v) (hloc v)]
    have hSInf : ∀ w : InfinitePlace F, hasseS _ (uInf w) = (NFPlace.infinite w).hasseOMeara c := fun w => by
      rw [← hasseS_algebraMap_infinite, hasseS_eq_of_isometricIn_infinite w (hcw w) (huInf w) (hlocInf w)]
    obtain ⟨hsupp, hprod⟩ := NFPlace.hasseOMeara_product_formula c hc
    refine ⟨⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc i, fun v => ?_, fun w => ?_⟩, ?_, ?_⟩
    · have h := isSquare_prod_div_of_isometricIn (hcv v) (hu v) (hloc v)
      rw [map_prod]
      exact isSquare_inv_div h
    · have h := isSquare_prod_div_of_isometricIn (hcw w) (huInf w) (hlocInf w)
      rw [map_prod]
      exact isSquare_inv_div h
    · simp only [hS]
      exact Set.Finite.preimage (fun a _ b _ hab => by cases hab; rfl) hsupp
    · simp only [hS, hSInf]
      rw [← finprod_nfPlace _ hsupp, hprod]
  · rintro ⟨⟨d, hd, h1, h1'⟩, h2, h3⟩
    obtain ⟨c, hc, hcv, hcw⟩ := exists_diag_of_localConds n u hu uInf huInf d ⟨hd, h1, h1', h2, h3⟩
    refine ⟨diag c, nondegenerate_diag c hc, fun v => ?_, fun w => ?_⟩
    · rw [map_diag']; exact hcv v
    · rw [map_diag']; exact hcw w

end QuadFormsKB.OMeara
