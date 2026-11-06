/-
# O'Meara 93:28, sufficiency, step 3: conditions (i)-(iii) survive a change of the Jordan splitting of $K$

**Setting** (as in `Sec93FMain.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$ of characteristic $0$, $2$ not a unit of $R$, $V$ a regular quadratic space over $F$, lattices
`Submodule R V`; indices are $0$-based.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 3, p. 273)
* `cond93_resplit`: if $L$, $K$ have the same fundamental invariants and `Cond93` holds for Jordan splittings $L_\bullet$
  and $K_\bullet$, then it holds for $L_\bullet$ and any other Jordan splitting $K'_\bullet$ of $K$;
* `rep_complement_disc`: the discriminant statement behind "the discriminant shows that we can take
  $a' \cong a \bmod a\mathfrak f$";
* `spanRepresents_trans_disc`, `resplit_rep`: the Witt-cancellation steps for (ii) and (iii);
* `isNormGenerator_of_sqEquivMod`, `smul_le_weight`: $a' \cong a \bmod a\mathfrak f$ is again a fundamental norm
  generator.
-/
import QuadFormsKB.Literature.OMeara.Sec93FMain

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Resplit

open QuadFormsKB.OMeara RepTransfer NecBlocks

section Abstract

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {U₁ U₂ : Type*} [AddCommGroup U₁] [Module F U₁] [AddCommGroup U₂] [Module F U₂]

/-- The bilinear form of an orthogonal sum is the sum of the bilinear forms: $B((x_1,x_2),(y_1,y_2)) = B_1(x_1,y_1) + B_2(x_2,y_2)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem bil_prod (Q₁ : QuadraticForm F U₁) (Q₂ : QuadraticForm F U₂) (x y : U₁ × U₂) :
    bil (Q₁.prod Q₂) x y = bil Q₁ x.1 y.1 + bil Q₂ x.2 y.2 := by
  rw [bil_eq_half, bil_eq_half, bil_eq_half]
  simp only [QuadraticMap.prod_apply, Prod.fst_add, Prod.snd_add]; ring

/-- The bilinear form of the line $\langle a\rangle$ ($t \mapsto a t^2$) is $B(x,y) = a\,x y$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem bil_smul_sq (a x y : F) : bil (a • (QuadraticMap.sq : QuadraticForm F F)) x y = a * (x * y) := by
  rw [bil_eq_half]
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  simp only [QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul]; field_simp; ring

/-- An isometry preserves the bilinear form: $B_2(ex, ey) = B_1(x,y)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem bil_isometry {Q₁ : QuadraticForm F U₁} {Q₂ : QuadraticForm F U₂} (e : Q₁.IsometryEquiv Q₂) (x y : U₁) :
    bil Q₂ (e x) (e y) = bil Q₁ x y := by
  rw [bil_eq_half, bil_eq_half, ← map_add, e.map_app, e.map_app, e.map_app]

/-- The Gram determinant of the basis $(e_0,\dots,e_{n-1}, 1)$ of $U \perp \langle a\rangle$ is $a$ times the Gram determinant of $e$ (0-based indices $0,\dots,n-1$ for $e$, the extra vector last). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem det_gram_prod_single {n : ℕ} (Q₁ : QuadraticForm F U₁) (e : Basis (Fin n) F U₁) (a : F) :
    (gram (Q₁.prod (a • (QuadraticMap.sq : QuadraticForm F F)))
      fun i => (e.prod (Basis.singleton Unit F)) i).det = a * (gram Q₁ fun i => e i).det := by
  have : (gram (Q₁.prod (a • (QuadraticMap.sq : QuadraticForm F F)))
      fun i => (e.prod (Basis.singleton Unit F)) i) =
      Matrix.fromBlocks (gram Q₁ fun i => e i) 0 0 (Matrix.of fun _ _ => a) := by
    have z1 : ∀ (Q : QuadraticForm F U₁) y, bil Q 0 y = 0 := fun Q y => by
      simpa using bil_smul_left Q 0 0 y
    have z2 : ∀ (Q : QuadraticForm F U₁) y, bil Q y 0 = 0 := fun Q y => by
      rw [bil_comm]; exact z1 Q y
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [gram, bil_prod, bil_smul_sq, z1, z2]
  have hu : (Matrix.of fun (_ : Unit) (_ : Unit) => a).det = a := by
    rw [Matrix.det_unique]; rfl
  rw [this, Matrix.det_fromBlocks_zero₂₁, hu, mul_comm]

/-- Let $A$, $B$ be nonsingular quadratic spaces over a field of characteristic $\ne 2$ with bases $e$, $e'$ of the same length $n$ and let $A$ embed in $B \perp \langle c\rangle$ (`Rep`). Then there are $a_1 \ne 0$ and $s \ne 0$ with $a_1\,d(e) = s^2 c\,d(e')$ and $A \perp \langle a_1\rangle \cong B \perp \langle c\rangle$ (the orthogonal complement of the image of $A$ is a line $\langle a_1\rangle$; the discriminants of the two bases of $B\perp\langle c\rangle$ differ by a square). This is the discriminant statement of O'Meara p. 273: "now the discriminant shows that we can take $a'_{i+1} \cong a_{i+1}$". -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem rep_complement_disc [FiniteDimensional F U₁] [FiniteDimensional F U₂]
    {Q₁ : QuadraticForm F U₁} {Q₂ : QuadraticForm F U₂} (h₁ : (polarBilin Q₁).Nondegenerate)
    {c : F} (hc : c ≠ 0) {n : ℕ} (e : Basis (Fin n) F U₁) (e' : Basis (Fin n) F U₂)
    (hd' : (gram Q₂ fun i => e' i).det ≠ 0)
    (h : Rep Q₁ (Q₂.prod (c • (QuadraticMap.sq : QuadraticForm F F)))) :
    ∃ a₁ s : F, s ≠ 0 ∧ a₁ ≠ 0 ∧
      a₁ * (gram Q₁ fun i => e i).det = s ^ 2 * c * (gram Q₂ fun i => e' i).det ∧
      Nonempty ((Q₁.prod (a₁ • (QuadraticMap.sq : QuadraticForm F F))).IsometryEquiv
        (Q₂.prod (c • (QuadraticMap.sq : QuadraticForm F F)))) := by
  classical
  obtain ⟨f, hf, hQ⟩ := h
  obtain ⟨Z, ⟨eZ⟩, hZdim⟩ := exists_complement h₁ hf hQ
  have hU₁ : finrank F U₁ = n := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hU₂ : finrank F U₂ = n := by rw [Module.finrank_eq_card_basis e', Fintype.card_fin]
  have hZ1 : finrank F Z = 1 := by
    rw [Module.finrank_prod, Module.finrank_self] at hZdim
    omega
  set QT : QuadraticForm F (U₂ × F) := Q₂.prod (c • (QuadraticMap.sq : QuadraticForm F F)) with hQT
  let b : Basis (Fin 1) F Z := Module.finBasisOfFinrankEq F Z hZ1
  set z : U₂ × F := (b 0 : U₂ × F) with hz
  set a₁ : F := QT z with ha₁
  let ψ' : Z ≃ₗ[F] F := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) F F)
  have hψ : ∀ t : F, (ψ'.symm t : U₂ × F) = t • z := by
    intro t
    have : ψ'.symm t = t • b 0 := by
      apply ψ'.injective
      simp [ψ', Basis.equivFun_apply]
    rw [this]; rfl
  let ψ : (a₁ • (QuadraticMap.sq : QuadraticForm F F)).IsometryEquiv (QT.comp Z.subtype) :=
    { ψ'.symm with
      map_app' := fun t => by
        show QT (ψ'.symm t : U₂ × F) = _
        rw [hψ, QuadraticMap.map_smul]
        simp [ha₁, mul_comm, pow_two] }
  let θ : (Q₁.prod (a₁ • (QuadraticMap.sq : QuadraticForm F F))).IsometryEquiv QT :=
    (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl Q₁) ψ).trans eZ
  -- discriminants
  let β₁ := e.prod (Basis.singleton Unit F)
  let β₂ := e'.prod (Basis.singleton Unit F)
  let γ : Basis (Fin n ⊕ Unit) F (U₂ × F) := β₁.map θ.toLinearEquiv
  have hγ : (gram QT fun i => γ i) = gram (Q₁.prod (a₁ • (QuadraticMap.sq : QuadraticForm F F))) fun i => β₁ i := by
    ext i j
    simp only [gram, Matrix.of_apply, γ, Basis.map_apply]
    exact bil_isometry θ _ _
  obtain ⟨P, hP, hPγ⟩ := D18.gram_change QT β₂ γ
  have hdA : (gram QT fun i => γ i).det = a₁ * (gram Q₁ fun i => e i).det := by
    rw [hγ]; exact det_gram_prod_single Q₁ e a₁
  have hdB : (gram QT fun i => β₂ i).det = c * (gram Q₂ fun i => e' i).det :=
    det_gram_prod_single Q₂ e' c
  have key : a₁ * (gram Q₁ fun i => e i).det = P.det ^ 2 * c * (gram Q₂ fun i => e' i).det := by
    rw [← hdA, hPγ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdB]; ring
  have hs : P.det ≠ 0 := hP.ne_zero
  refine ⟨a₁, P.det, hs, ?_, key, ⟨θ⟩⟩
  intro h0
  rw [h0, zero_mul] at key
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hs) hc) hd' key.symm

end Abstract

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The bilinear form of the restriction of $Q$ to $FA$ is the restriction of the bilinear form. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem bil_subQ (A : Submodule R V) (x y : D18.spanF F A) : bil (D18.subQ Q A) x y = bil Q (x : V) (y : V) := by
  rw [bil_eq_half, bil_eq_half]; rfl

/-- An $R$-basis of a lattice $A$ with nonzero discriminant is an $F$-basis of $FA$ with the same Gram matrix. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem exists_spanBasis {A : Submodule R V} {n : ℕ} (b : Basis (Fin n) R A)
    (hdet : (gram Q fun i => (b i : V)).det ≠ 0) :
    ∃ e : Basis (Fin n) F (D18.spanF F A), (gram (D18.subQ Q A) fun i => (e i)) = gram Q fun i => (b i : V) := by
  have hliV : LinearIndependent F (fun i => (b i : V)) := linearIndependent_of_det_gram_ne_zero (R := F) Q hdet
  have hli : LinearIndependent F (fun i => (⟨(b i : V), subset_span (b i).2⟩ : D18.spanF F A)) :=
    LinearIndependent.of_comp (D18.spanF F A).subtype hliV
  have hcard : Fintype.card (Fin n) = finrank F (D18.spanF F A) := by
    rw [D18.finrank_spanF Q A b hdet, Fintype.card_fin]
  refine ⟨Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge, ?_⟩
  ext i j
  simp only [gram, Matrix.of_apply, Basis.coe_mk]
  rw [bil_subQ]

/-- If $y \cong 1 \bmod \mathfrak a$ then $a y \cong a \bmod a\mathfrak a$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem sqEquivMod_smul_one {X : Submodule R F} {y : F} (hy : SqEquivMod X y 1) (a : F) :
    SqEquivMod (a • X) (a * y) a := by
  obtain ⟨⟨u, hu, huy⟩, ε, hε, hyε⟩ := hy
  rw [mul_one] at huy
  refine ⟨⟨u, hu, by rw [huy, mul_comm]⟩, ε, hε, ?_⟩
  have : a * y - a * algebraMap R F ε ^ 2 = a • (y - 1 * algebraMap R F ε ^ 2) := by
    rw [smul_eq_mul]; ring
  rw [this]
  exact Submodule.smul_mem_pointwise_smul _ _ _ hyε

/-- **Composition of representations through a nearby scalar** (O'Meara p. 273): let $A$, $B$, $B'$ be regular lattices, $\operatorname{rank} A = \operatorname{rank} B$, $a \ne 0$, $FA \to FB \perp \langle a\rangle$ and $dA/dB \cong 1 \bmod \mathfrak f$. If $FB \to FB' \perp \langle a'\rangle$ for every $a' \cong a \bmod a\mathfrak f$, then $FA \to FB' \perp \langle a\rangle$. With $a' = a\,dB/dA$ one has $FA \perp \langle a'\rangle \cong FB \perp \langle a\rangle$ (`rep_complement_disc`), $FB \perp \langle a\rangle \to (FB' \perp \langle a'\rangle) \perp \langle a\rangle$, and $\langle a'\rangle$ cancels (Witt). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem spanRepresents_trans_disc {A B B' : Submodule R V} (hAfg : A.FG) (hBfg : B.FG)
    (hAreg : IsRegular Q A) (hBreg : IsRegular Q B) (hB'reg : IsRegular Q B')
    (hrk : finrank R A = finrank R B) {a : F} (ha : a ≠ 0) {f : Submodule R F}
    (hAB : SpanRepresents Q A B a) (hdisc : DiscQuotSqEquivMod Q A B f)
    (hBB' : ∀ a' : F, SqEquivMod (a • f) a' a → SpanRepresents Q B B' a') :
    SpanRepresents Q A B' a := by
  classical
  obtain ⟨bA⟩ := exists_basis (R := R) (F := F) hAfg
  obtain ⟨bB0⟩ := exists_basis (R := R) (F := F) hBfg
  let bB : Basis (Fin (finrank R A)) R B := bB0.reindex (finCongr hrk.symm)
  have hdA := Transfer28.det_gram_ne_zero_of_isRegular Q hAreg bA
  have hdB := Transfer28.det_gram_ne_zero_of_isRegular Q hBreg bB
  have hsq := Transfer28.discQuot_bases Q hdisc bA bB hdB
  have hy := Arith28.sqEquivMod_inv_one hsq
  set dA := (gram Q fun i => (bA i : V)).det with hdAdef
  set dB := (gram Q fun i => (bB i : V)).det with hdBdef
  set a' : F := a * (dA / dB)⁻¹ with ha'
  have ha'0 : a' ≠ 0 := mul_ne_zero ha (inv_ne_zero (div_ne_zero hdA hdB))
  have hBB'a' := hBB' a' (sqEquivMod_smul_one hy a)
  obtain ⟨eA, heA⟩ := exists_spanBasis Q bA hdA
  obtain ⟨eB, heB⟩ := exists_spanBasis Q bB hdB
  have hrep := (spanRepresents_iff_rep Q A B a).1 hAB
  obtain ⟨a₁, s, hs, ha₁, hkey, ⟨θ⟩⟩ :=
    rep_complement_disc (nondegenerate_subQ Q hAreg) ha eA eB (by rw [heB]; exact hdB) hrep
  rw [heA, heB] at hkey
  have hrel : a₁ = s ^ 2 * a' := by
    rw [ha']; field_simp; linear_combination hkey
  let φ : ((a' • (QuadraticMap.sq : QuadraticForm F F))).IsometryEquiv
      (a₁ • (QuadraticMap.sq : QuadraticForm F F)) :=
    { LinearEquiv.smulOfNeZero F F s⁻¹ (inv_ne_zero hs) with
      map_app' := fun t => by
        simp only [QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul]
        show a₁ * (s⁻¹ • t * (s⁻¹ • t)) = a' * (t * t)
        rw [hrel, smul_eq_mul]; field_simp }
  let ISO : ((D18.subQ Q A).prod (a' • (QuadraticMap.sq : QuadraticForm F F))).IsometryEquiv
      ((D18.subQ Q B).prod (a • (QuadraticMap.sq : QuadraticForm F F))) :=
    (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl _) φ).trans θ
  have hr2 := (spanRepresents_iff_rep Q B B' a').1 hBB'a'
  have h3 := Rep.prod_right (a • (QuadraticMap.sq : QuadraticForm F F)) hr2
  have h4 := Rep.congr ISO (swap23 (D18.subQ Q B') (a' • (QuadraticMap.sq : QuadraticForm F F))
    (a • (QuadraticMap.sq : QuadraticForm F F))) h3
  have h5 := Rep.cancel_right (QuadraticForm.nondegenerate_polarBilin_prod (nondegenerate_subQ Q hB'reg)
    (nondegenerate_smul_sq ha)) (nondegenerate_smul_sq ha'0) h4
  exact (spanRepresents_iff_rep Q A B' a).2 h5

section Generators

/-- **A scalar $a' \cong a \bmod \mathfrak x$ with $\mathfrak x \subseteq \mathfrak wM$ is again a norm generator** (O'Meara p. 273: "$a_{i+1}\mathfrak f_i \subset \cdots \subset \mathfrak w_{i+1}$; so $a'_{i+1}$ is a fundamental norm generator"): $a' = u a$ with $u$ a unit and $a' - a\varepsilon^2 \in \mathfrak wM \subseteq \mathfrak gM$, and $a\varepsilon^2 \in \mathfrak gM$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem isNormGenerator_of_sqEquivMod {M : Submodule R V} {a a' : F} (ha : IsNormGenerator Q M a)
    {X : Submodule R F} (hX : X ≤ weight Q M) (h : SqEquivMod X a' a) : IsNormGenerator Q M a' := by
  obtain ⟨⟨u, hu, hua⟩, ε, hε, hdiff⟩ := h
  have hw : a' - a * algebraMap R F ε ^ 2 ∈ normGroup Q M :=
    normGroupIdeal_subset Q M ((weight_bounds Q M).2.1 (hX hdiff))
  have hsq : a * algebraMap R F ε ^ 2 ∈ normGroup Q M := by
    obtain ⟨x, hx, c, hc, hac⟩ := ha.1
    refine ⟨ε • x, M.smul_mem ε hx, ε ^ 2 • c, (scale Q M).smul_mem (ε ^ 2) hc, ?_⟩
    rw [← algebraMap_smul F ε x, QuadraticMap.map_smul, Algebra.smul_def (ε ^ 2), map_pow, hac]
    simp only [smul_eq_mul]; ring
  refine ⟨?_, ?_⟩
  · have : a' = (a' - a * algebraMap R F ε ^ 2) + a * algebraMap R F ε ^ 2 := by ring
    rw [this]; exact add_mem hw hsq
  · have : a' = u • a := by rw [hua, Algebra.smul_def]
    rw [this, Submodule.span_singleton_smul_eq hu a]; exact ha.2

/-- If $\mathfrak f \subseteq 4a\,\mathfrak w^{-1}$ and $a$ is a norm generator of $M$ then $a\mathfrak f \subseteq \mathfrak wM$ (since $2a \in 2\,\mathfrak sM \subseteq \mathfrak wM$, and $x \in \mathfrak w^{-1}$ gives $2a x \in \mathfrak o$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem smul_le_weight {M : Submodule R V} {a : F} (ha : IsNormGenerator Q M a) {f : Submodule R F}
    (hf : f ≤ (4 * a) • (1 / weight Q M)) : a • f ≤ weight Q M := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hf hz)
  have ha2 : (2 : F) * a ∈ weight Q M := by
    have : a ∈ scale Q M := normIdeal_le_scale Q M (normGroup_subset_normIdeal Q M ha.1)
    exact (weight_bounds Q M).2.2.1 (Submodule.smul_mem_pointwise_smul a (2 : F) _ this)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((Submodule.mem_div_iff_forall_mul_mem.1 hx) _ ha2)
  have : a • (4 * a) • x = r • ((2 : F) * a) := by
    simp only [smul_eq_mul]; rw [Algebra.smul_def, hr]; ring
  rw [this]; exact Submodule.smul_mem _ r ha2

/-- Multiplying an $R$-submodule of $F$ by a unit of $R$ does not change it. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem unit_smul_eq (Y : Submodule R F) {u : R} (hu : IsUnit u) : algebraMap R F u • Y = Y := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    have : algebraMap R F u • y = u • y := by rw [smul_eq_mul, Algebra.smul_def]
    rw [this]; exact Y.smul_mem u hy
  · intro z hz
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨v • z, Y.smul_mem v hz, ?_⟩
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_mul, hv, map_one, one_mul]

/-- If $a' = u a$ with $u$ a unit of $R$ then $(4a')X = (4a)X$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem smul_unit_mul_eq (X : Submodule R F) (a : F) {a' : F} {u : R} (hu : IsUnit u)
    (h : a' = algebraMap R F u * a) : (4 * a') • X = (4 * a) • X := by
  have : 4 * a' = algebraMap R F u * (4 * a) := by rw [h]; ring
  rw [this, mul_smul, unit_smul_eq _ hu]

/-- Transitivity of $dA/dB \cong 1 \bmod \mathfrak f$ for regular lattices: $dA/dC = (dA/dB)(dB/dC)$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem discQuot_trans {A B C : Submodule R V} (hAfg : A.FG) (hBfg : B.FG) (hCfg : C.FG)
    (hBreg : IsRegular Q B) (hCreg : IsRegular Q C) {f : Submodule R F}
    (h1 : DiscQuotSqEquivMod Q A B f) (h2 : DiscQuotSqEquivMod Q B C f) : DiscQuotSqEquivMod Q A C f := by
  obtain ⟨bA⟩ := exists_basis (R := R) (F := F) hAfg
  obtain ⟨bB⟩ := exists_basis (R := R) (F := F) hBfg
  obtain ⟨bC⟩ := exists_basis (R := R) (F := F) hCfg
  have hdB := Transfer28.det_gram_ne_zero_of_isRegular Q hBreg bB
  have hdC := Transfer28.det_gram_ne_zero_of_isRegular Q hCreg bC
  have hx := Transfer28.discQuot_bases Q h1 bA bB hdB
  have hy := Transfer28.discQuot_bases Q h2 bB bC hdC
  refine ⟨bA, bC, ?_⟩
  have := Arith28.sqEquivMod_mul_one hx hy
  rwa [div_mul_div_cancel₀ hdB] at this

/-- Replacing one fundamental norm generator $a_p$ by another norm generator of the same lattice $L^{\mathfrak s_p}$ keeps the family fundamental norm generators. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem isNormGenerator_update {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (p : Fin t) {a' : F} (h : IsNormGenerator Q (fundSub Q L Ls p) a') :
    IsFundNormGenerators Q L Ls (Function.update a p a') := by
  intro k
  by_cases hk : k = p
  · subst hk; simpa using h
  · simpa [Function.update_of_ne hk] using ha k

/-- Jordan chains of splittings with equal component ranks have equal ranks. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem finrank_chain_eq {L K : Submodule R V} {t : ℕ} {Ls Ks : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hrk : ∀ k, finrank R (Ls k) = finrank R (Ks k)) (i : Fin t) :
    finrank R (jordanChain Ls i) = finrank R (jordanChain Ks i) := by
  rw [(isJordanSplitting_jordanChain Q hL i).split.finrank_eq_sum (F := F),
    (isJordanSplitting_jordanChain Q hK i).split.finrank_eq_sum (F := F)]
  exact Finset.sum_congr rfl fun k _ => hrk _

end Generators

end Lattice

section Main

universe u v

open Suff28 SuffMain

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- If $L$, $K$ have the same fundamental invariants (for $Ls$, $Ks$) and $Ks$, $Ks'$ are two Jordan splittings of $K$, then $K$ and $K$ have the same fundamental invariants for $Ks$, $Ks'$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem sameFund_KK {K : Submodule R V} (hKfg : K.FG) {t : ℕ} {Ks Ks' : Fin t → Submodule R V} {L : Submodule R V}
    {Ls : Fin t → Submodule R V} {a : Fin t → F} (hK : IsJordanSplitting Q K Ks)
    (hK' : IsJordanSplitting Q K Ks') (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    SameFundamentalInvariants Q Q K K Ks Ks' a := by
  have hS' := sameFund_resplit Q hKfg hK hK' hS
  obtain ⟨⟨h0, hT⟩, -, haK⟩ := hS
  obtain ⟨⟨h0', hT'⟩, -, haK'⟩ := hS'
  refine ⟨⟨rfl, fun k => ?_⟩, haK, haK'⟩
  have e1 := hT k
  have e2 := hT' k
  rw [show Fin.cast h0 k = k from Fin.ext rfl] at e1
  rw [show Fin.cast h0' k = k from Fin.ext rfl] at e2
  rw [show Fin.cast rfl k = k from Fin.ext rfl]
  exact ⟨e1.1.symm.trans e2.1, e1.2.1.symm.trans e2.2.1, e1.2.2.symm.trans e2.2.2⟩

/-- The fundamental weights $\mathfrak w_k$ depend only on the fundamental invariants. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem fundWeight_eq_of_sameFund {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (k : Fin t) :
    fundWeight Q L Ls k = fundWeight Q K Ks k := by
  obtain ⟨⟨h0, hT⟩, -, -⟩ := hS
  have e := hT k
  rw [show Fin.cast h0 k = k from Fin.ext rfl] at e
  refine weight_congr Q Q e.2.2 ?_
  rw [scale_fundSub Q hLfg hL, scale_fundSub Q hKfg hK, e.2.1]

/-- The ideals $\mathfrak f_{ij}$ depend only on the fundamental invariants. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem fIdeal_eq_of_sameFund {L K : Submodule R V} {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (i j : Fin t) : fIdeal Q L Ls i j = fIdeal Q K Ks i j := by
  have := fIdeal_eq_of_sameFundamentalType Q Q rfl hS.1 i j
  simpa using this

/-- **Steps (ii) and (iii) of O'Meara p. 273.** Let $L$, $K$ have the same fundamental invariants, $K = K_0 \perp \cdots = K'_0 \perp \cdots$ two Jordan splittings, and suppose $FL_{(i)} \to FK_{(i)} \perp \langle a_p\rangle$ when $\mathfrak f_{ij} \subsetneq 4a_p\mathfrak w_p^{-1}$ and $dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak f_{ij}$. If the conditions (ii)/(iii) hold for $K$ against $K'$ for every fundamental norm generator family (`proj`), then $FL_{(i)} \to FK'_{(i)} \perp \langle a_p\rangle$. Proof: choose $a' \cong a_p \bmod a_p\mathfrak f$ with $FL_{(i)} \perp \langle a'\rangle \cong FK_{(i)} \perp \langle a_p\rangle$ (`rep_complement_disc`); $a'$ is a fundamental norm generator, so $FK_{(i)} \to FK'_{(i)} \perp \langle a'\rangle$ (necessity of 93:28 for $K$ against $K'$); adding $\langle a_p\rangle$ and cancelling $\langle a'\rangle$ (Witt) gives the claim (`spanRepresents_trans_disc`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem resplit_rep (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [hLl : L.IsLattice F]
    [hKl : K.IsLattice F] {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V} {a : Fin t → F}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hK' : IsJordanSplitting Q K Ks')
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (i j p : Fin t)
    (proj : ∀ {a'' : Fin t → F}, Cond93 Q K Ks Ks' a'' →
      fIdeal Q K Ks i j < (4 * a'' p) • (1 / fundWeight Q K Ks p) →
        SpanRepresents Q (jordanChain Ks i) (jordanChain Ks' i) (a'' p))
    (hlt : fIdeal Q L Ls i j < (4 * a p) • (1 / fundWeight Q L Ls p))
    (hrep : SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a p))
    (hdisc : DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j)) :
    SpanRepresents Q (jordanChain Ls i) (jordanChain Ks' i) (a p) := by
  have hLfg : L.FG := hLl.fg
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKK := sameFund_KK Q hKfg hK hK' hS
  have hAfg : (jordanChain Ls i).FG := FG.of_le hLfg (NecI.jordanChain_le hL.split i)
  have hBfg : (jordanChain Ks i).FG := FG.of_le hKfg (NecI.jordanChain_le hK.split i)
  have hAreg := isRegular_of_isJordanSplitting Q hAfg (isJordanSplitting_jordanChain Q hL i)
  have hBreg := isRegular_of_isJordanSplitting Q hBfg (isJordanSplitting_jordanChain Q hK i)
  have hB'fg : (jordanChain Ks' i).FG := FG.of_le hKfg (NecI.jordanChain_le hK'.split i)
  have hB'reg := isRegular_of_isJordanSplitting Q hB'fg (isJordanSplitting_jordanChain Q hK' i)
  have hrk : finrank R (jordanChain Ls i) = finrank R (jordanChain Ks i) := by
    refine finrank_chain_eq Q hL hK (fun k => ?_) i
    have := hS.1.2 k
    rw [show Fin.cast hS.1.1 k = k from Fin.ext rfl] at this
    exact this.1
  have hfK := fIdeal_eq_of_sameFund Q hS i j
  have hwK := fundWeight_eq_of_sameFund Q hLfg hKfg hL hK hS p
  have hlt' : fIdeal Q K Ks i j < (4 * a p) • (1 / fundWeight Q K Ks p) := by rwa [hfK, hwK] at hlt
  have ha0 : a p ≠ 0 := by
    intro h0
    rw [h0] at hlt'
    simp at hlt'
  refine spanRepresents_trans_disc Q hAfg hBfg hAreg hBreg hB'reg hrk ha0 hrep hdisc ?_
  intro a' ha'
  have hgen : IsNormGenerator Q (fundSub Q K Ks p) (a p) := hS.2.2 p
  have hX : a p • fIdeal Q L Ls i j ≤ weight Q (fundSub Q K Ks p) := by
    rw [hfK]
    exact smul_le_weight Q hgen hlt'.le
  have hg' : IsNormGenerator Q (fundSub Q K Ks p) a' := isNormGenerator_of_sqEquivMod Q hgen hX ha'
  have h3 : fundNormGroup Q K Ks' p = fundNormGroup Q K Ks p := by
    have := hKK.1.2 p
    rw [show Fin.cast hKK.1.1 p = p from Fin.ext rfl] at this
    exact this.2.2.symm
  have hg'' : IsNormGenerator Q (fundSub Q K Ks' p) a' := isNormGenerator_fundSub_of_eq Q Q h3 hg'
  have hKKu : SameFundamentalInvariants Q Q K K Ks Ks' (Function.update a p a') :=
    ⟨hKK.1, isNormGenerator_update Q hKK.2.1 p hg', isNormGenerator_update Q hKK.2.2 p hg''⟩
  have hCu := Main28.necessity Q hHil h2p hQ hK hK' hKKu rfl
  obtain ⟨⟨u, hu, hua⟩, -⟩ := ha'
  have hlt'' : fIdeal Q K Ks i j < (4 * Function.update a p a' p) • (1 / fundWeight Q K Ks p) := by
    rw [Function.update_self, smul_unit_mul_eq _ (a p) hu hua]; exact hlt'
  have := proj hCu hlt''
  rwa [Function.update_self] at this

/-- **The conditions (i)–(iii) of 93:28 survive a change of the Jordan splitting of $K$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 3, p. 273: "conditions (i)–(iii) will continue to hold if the given splitting $K_1 \perp \cdots \perp K_t$ is replaced by any other Jordan splitting $K_1' \perp \cdots \perp K_t'$"). Let $L$, $K$ be lattices on a regular quadratic space over a dyadic local field (with `LocalHilbertField`), $L = L_0 \perp \cdots \perp L_{t-1}$, $K = K_0 \perp \cdots \perp K_{t-1} = K'_0 \perp \cdots \perp K'_{t-1}$ Jordan splittings (0-based), with the same fundamental invariants $a$ for $(L, K)$. If `Cond93` holds for $(L, K_\bullet)$ then it holds for $(L, K'_\bullet)$. Proof: (i) $dK_{(i)}/dK'_{(i)} \cong 1 \bmod \mathfrak f_i$ by the necessity of 93:28 for $K$ against itself (`Main28.necessity`), and the two discriminant quotients multiply (`discQuot_trans`); (ii), (iii) by `resplit_rep` (the discriminant shows that $a_{i+1}' \cong a_{i+1} \bmod a_{i+1}\mathfrak f_i$ is a fundamental norm generator; Witt cancellation). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 3, p. 273 (re-splitting K keeps (i)–(iii))"]
theorem cond93_resplit (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [hLl : L.IsLattice F]
    [hKl : K.IsLattice F] {t : ℕ} {Ls Ks Ks' : Fin t → Submodule R V} {a : Fin t → F}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hK' : IsJordanSplitting Q K Ks')
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    Cond93 Q L Ls Ks' a := by
  have hLfg : L.FG := hLl.fg
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKK := sameFund_KK Q hKfg hK hK' hS
  have hCKK := Main28.necessity Q hHil h2p hQ hK hK' hKK rfl
  intro i j hij
  obtain ⟨hC1, hC2, hC3⟩ := hC i j hij
  obtain ⟨hK1, -, -⟩ := hCKK i j hij
  have hBfg : (jordanChain Ks i).FG := FG.of_le hKfg (NecI.jordanChain_le hK.split i)
  have hB'fg : (jordanChain Ks' i).FG := FG.of_le hKfg (NecI.jordanChain_le hK'.split i)
  have hAfg : (jordanChain Ls i).FG := FG.of_le hLfg (NecI.jordanChain_le hL.split i)
  have hBreg := isRegular_of_isJordanSplitting Q hBfg (isJordanSplitting_jordanChain Q hK i)
  have hB'reg := isRegular_of_isJordanSplitting Q hB'fg (isJordanSplitting_jordanChain Q hK' i)
  have hfK := fIdeal_eq_of_sameFund Q hS i j
  have hdisc : DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) := hC1
  refine ⟨?_, fun hlt => ?_, fun hlt => ?_⟩
  · rw [hfK] at hC1 ⊢
    exact discQuot_trans Q hAfg hBfg hB'fg hBreg hB'reg hC1 hK1
  · refine resplit_rep Q hHil h2p hQ hL hK hK' hS i j j (fun h hl => (h i j hij).2.1 hl) hlt (hC2 hlt) hdisc
  · refine resplit_rep Q hHil h2p hQ hL hK hK' hS i j i (fun h hl => (h i j hij).2.2 hl) hlt (hC3 hlt) hdisc

end Main

end QuadFormsKB.OMeara.Resplit
