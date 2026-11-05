/-
# O'Meara §93D, Example 93:18 (iii): quaternary unimodular lattices with $\operatorname{ord} a + \operatorname{ord} b$ odd

**Setting** (as in `Sec91Local.lean`): $R$ a Henselian discrete valuation ring with finite residue field, fraction
field $F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField` (they hold for the
completion of a number field at a finite place, `HasseIsoNF.localHilbertField_adicCompletion`), $F$ dyadic ($2$ not a
unit of $R$). $(V, Q)$ is a quadratic space over $F$, O'Meara's $B$ = `bil Q`, lattices are `Submodule R V`.
$L \cong A(\alpha, \beta) \perp A(\gamma, \delta)$ is `HasBlk Q L α β γ δ`: $L$ has a base with matrix `blk2 α β γ δ`.

**Page image read** (O'Meara 1973 printing, p. 260): "(iii) Next we consider $\dim L = 4$ with
$\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ odd. Here we suppose that $d$ has been
expressed in the form $d = 1 + \alpha$ with $\mathfrak d(d) = \alpha\mathfrak o$. It follows from Example 93:10 that we
must have $\alpha \in ab\mathfrak o$. Take lattices $J, K$ on quadratic spaces over $F$ with
$J \cong \langle A(a, -\alpha a^{-1})\rangle \perp \langle A(b, 0)\rangle$,
$K \cong \langle A(a, -(\alpha - 4\rho)a^{-1})\rangle \perp \langle A(b, 4\rho b^{-1})\rangle$. Let us prove that $L$ is
isometric to $J$ or to $K$, but not to both." The proof: $\mathfrak gJ = \mathfrak gL = \mathfrak gK$,
$dJ = dL = dK$, $S_{\mathfrak p}(FJ) = -S_{\mathfrak p}(FK)$ (§63B), then 63:20 and 93:16 (p. 261).

**Proves**
* `exists_blk2_basis`: a quaternary unimodular lattice has a base with matrix
  $A(a_1, \beta_1) \perp A(a_2, \beta_2)$, $a_i \in \mathfrak nL$, $\beta_i \in \mathfrak wL$ (93:15 and 93:10);
* `alpha_mem_span_mul` (the first claim of 93:18 (iii)): $\alpha \in ab\mathfrak o$;
* `omeara93_18_iii` (**93:18 (iii)**): $L \cong J$ or $L \cong K$, not both;
* `omeara93_18_iii_nf`: the same for completions of number fields at dyadic places.
-/
import QuadFormsKB.Literature.OMeara.Sec93DEng
import QuadFormsKB.Literature.OMeara.Sec82Isom

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

/-- **$L \cong A(\alpha, \beta) \perp A(\gamma, \delta)$** (O'Meara 1963, §93B, p. 255, notation of 93:18): the lattice
$L$ has a base $x_1, y_1, x_2, y_2$ with matrix `blk2 α β γ δ`, i.e. $Q(x_1) = \alpha$, $B(x_1, y_1) = 1$,
$Q(y_1) = \beta$, $Q(x_2) = \gamma$, $B(x_2, y_2) = 1$, $Q(y_2) = \delta$, and the two planes orthogonal. -/
def HasBlk {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)] {V : Type*}
    [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] (Q : QuadraticForm F V) (L : Submodule R V)
    (α β γ δ : F) : Prop :=
  ∃ e : Basis (Fin 4) R L, gram Q (fun i => (e i : V)) = blk2 α β γ δ

theorem hasseS_pm' {F : Type*} [Field F] [CharZero F] {n : ℕ} (w : Fin n → F) :
    hasseS F w = 1 ∨ hasseS F w = -1 := by
  unfold hasseS
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun i _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun j _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  split_ifs
  · exact hs_pm _ _
  · exact Or.inl rfl

section Frame

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **A unimodular frame is a base**: $n$ vectors of a unimodular lattice $L$ of rank $n$ whose matrix has entries in
$\mathfrak o$ and unit determinant form a base of $L$. -/
theorem exists_basis_of_gram_unit {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) {n : ℕ} [NeZero n]
    (hrk : finrank R L = n) {v : Fin n → V} (hv : ∀ i, v i ∈ L) {G : Matrix (Fin n) (Fin n) R}
    (hG : IsUnit G.det) (hgram : gram Q v = G.map (algebraMap R F)) :
    ∃ e : Basis (Fin n) R L, ∀ i, (e i : V) = v i := by
  have hG' : gram Q v = (1 : F) • G.map (algebraMap R F) := by rw [one_smul]; exact hgram
  obtain ⟨hmod, hrkJ⟩ := isModular_span_of_gram Q one_ne_zero hG hG'
  have hJL : span R (Set.range v) ≤ L := by rw [span_le]; rintro _ ⟨i, rfl⟩; exact hv i
  have hsc : scale Q L = R ∙ (1 : F) := by rw [hU.2.1, ← Submodule.one_eq_span]
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hmod (fg_span (Set.finite_range v)) hsc
  have hr := isOrthSum_finrank Q hK hfg
  rw [hrk, hrkJ, Fintype.card_fin] at hr
  have hK0 : K = ⊥ := by
    have hKfg : K.FG := FG.of_le hfg (hK.sup_eq ▸ le_sup_right)
    obtain ⟨b⟩ := exists_basis (R := R) (F := F) hKfg
    rw [← span_basis_eq b]
    have : IsEmpty (Fin (finrank R K)) := by rw [show finrank R K = 0 by omega]; infer_instance
    rw [Set.range_eq_empty, span_empty]
  have hspan : span R (Set.range v) = L := by rw [← hK.sup_eq, hK0, sup_bot_eq]
  have hdet : (gram Q v).det ≠ 0 := by
    rw [hgram, show (G.map (algebraMap R F)).det = algebraMap R F G.det from (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hG.ne_zero
  have hli : LinearIndependent R v := linearIndependent_of_det_gram_ne_zero Q hdet
  exact ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), fun i => by simp⟩

end Frame

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **93:10 with a chosen norm generator**: a binary unimodular lattice $J$ has a base with matrix $A(a_1, \beta_1)$,
$a_1 \neq 0$ a norm generator, $\beta_1 \in \mathfrak wJ$. -/
theorem exists_matA_basis (h2p : ¬ IsUnit (2 : R)) {J : Submodule R V} (hfg : J.FG) (hU : IsUnimodular Q J)
    (hrk : finrank R J = 2) :
    ∃ a₁ β₁ : R, algebraMap R F a₁ ≠ 0 ∧ algebraMap R F a₁ ∈ normIdeal Q J ∧
      algebraMap R F β₁ ∈ weight Q J ∧ IsUnit (-1 + a₁ * β₁) ∧
      ∃ b : Basis (Fin 2) R J, gram Q (fun i => (b i : V)) = matA (algebraMap R F a₁) (algebraMap R F β₁) := by
  obtain ⟨z, hzJ, hzn⟩ := exists_normIdeal_eq Q hfg
  have hn : IsNormGenerator Q J (Q z) := ⟨Q_mem_normGroup Q hzJ, hzn.symm⟩
  obtain ⟨a₁, ha₁⟩ := a10_mem_one Q hU hzJ hzJ
  rw [bil_self] at ha₁
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q J := IsModular.isRegular Q hU hfg
  obtain ⟨β, hβw, hβu, bs, -, hbs⟩ := exists_hasMatrixA Q h2p hfg hU hrk hzJ ha₁.symm hn
  refine ⟨a₁, β, ?_, ?_, hβw, hβu, bs, hbs⟩
  · rw [ha₁]; exact hn.ne_zero Q hreg hne
  · rw [ha₁]; exact Q_mem_normIdeal Q hzJ

/-- **A quaternary unimodular lattice is $A(a_1, \beta_1) \perp A(a_2, \beta_2)$** (93:15 and 93:10): it has a base
with matrix `blk2 a₁ β₁ a₂ β₂`, $a_i \neq 0$ in $\mathfrak nL$, $\beta_i \in \mathfrak wL$. -/
theorem exists_blk2_basis (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) :
    ∃ a₁ β₁ a₂ β₂ : R, algebraMap R F a₁ ≠ 0 ∧ algebraMap R F a₂ ≠ 0 ∧
      algebraMap R F a₁ ∈ normIdeal Q L ∧ algebraMap R F β₁ ∈ weight Q L ∧
      algebraMap R F a₂ ∈ normIdeal Q L ∧ algebraMap R F β₂ ∈ weight Q L ∧
      IsUnit (-1 + a₁ * β₁) ∧ IsUnit (-1 + a₂ * β₂) ∧
      ∃ e : Basis (Fin 4) R L, gram Q (fun i => (e i : V)) =
        blk2 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F a₂) (algebraMap R F β₂) := by
  obtain ⟨J, hJL, hJfg, hJU, hJrk, -⟩ := Uni93.exists_split_data Q hfg hU (by omega)
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJU hJfg hU.2.1
  have hrkL := isOrthSum_finrank Q hK hfg
  have hK0 : K ≠ ⊥ := by
    rintro rfl
    simp at hrkL; omega
  have hKle : K ≤ L := hK.sup_eq ▸ le_sup_right
  have hKfg : K.FG := FG.of_le hfg hKle
  have hKU := u93_isUnimodular_of_orth Q hfg hU hJU hK hK0
  have hKrk : finrank R K = 2 := by omega
  obtain ⟨a₁, β₁, h1, h2, h3, h4, bJ, hbJ⟩ := exists_matA_basis Q h2p hJfg hJU hJrk
  obtain ⟨a₂, β₂, k1, k2, k3, k4, bK, hbK⟩ := exists_matA_basis Q h2p hKfg hKU hKrk
  have eJ : ∀ i j, bil Q (bJ i : V) (bJ j : V) = matA (algebraMap R F a₁) (algebraMap R F β₁) i j :=
    fun i j => by simpa [gram] using congrFun (congrFun hbJ i) j
  have eK : ∀ i j, bil Q (bK i : V) (bK j : V) = matA (algebraMap R F a₂) (algebraMap R F β₂) i j :=
    fun i j => by simpa [gram] using congrFun (congrFun hbK i) j
  have cJK : ∀ i j, bil Q (bJ i : V) (bK j : V) = 0 := fun i j => hK.orth _ (bJ i).2 _ (bK j).2
  have cKJ : ∀ i j, bil Q (bK i : V) (bJ j : V) = 0 := fun i j => by rw [bil_comm]; exact cJK j i
  let v : Fin 4 → V := ![bJ 0, bJ 1, bK 0, bK 1]
  have hv : ∀ i, v i ∈ L := by
    intro i
    fin_cases i
    · exact hJL (bJ 0).2
    · exact hJL (bJ 1).2
    · exact hKle (bK 0).2
    · exact hKle (bK 1).2
  have hgram : gram Q v = (blk2 a₁ β₁ a₂ β₂).map (algebraMap R F) := by
    rw [map_blk2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v, gram, blk2, eJ, eK, cJK, cKJ, matA]
  have hdet : IsUnit (blk2 a₁ β₁ a₂ β₂).det := by
    rw [det_blk2]
    exact (by simpa [add_comm, sub_eq_add_neg] using h4 : IsUnit (a₁ * β₁ - 1)).mul
      (by simpa [add_comm, sub_eq_add_neg] using k4 : IsUnit (a₂ * β₂ - 1))
  obtain ⟨e, he⟩ := exists_basis_of_gram_unit Q hfg hU hrk hv hdet hgram
  refine ⟨a₁, β₁, a₂, β₂, h1, k1, Uni93.normIdeal_mono' Q hJL h2, weight_mono Q hJL h3,
    Uni93.normIdeal_mono' Q hKle k2, weight_mono Q hKle k3, h4, k4, e, ?_⟩
  rw [← map_blk2, ← hgram]
  congr 1
  funext i
  exact he i

omit [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [Finite (ResidueField R)]
  [IsFractionRing R F] [Invertible (2 : F)] in
/-- $\mathfrak d(1 + w) \subseteq w\mathfrak o$ (take $\eta = 1$ in the definition of the quadratic defect). -/
theorem quadDefect_one_add_le (w : F) : quadDefect R (1 + w) ≤ span R {w} := by
  unfold quadDefect
  refine (iInf_le _ (1 : F)).trans ?_
  simp

/-- **93:18 (iii), first claim** (O'Meara 1963, p. 260: "It follows from Example 93:10 that we must have
$\alpha \in ab\mathfrak o$"): let $L$ be a quaternary unimodular lattice with norm generator $a$ and weight generator
$b$, and let $dL = 1 + \alpha$ (a base of $L$ has discriminant $1 + \alpha$) with $\mathfrak d(1 + \alpha) =
\alpha\mathfrak o$. Then $\alpha \in ab\mathfrak o$. (No parity hypothesis is needed for this claim.) -/
@[kb "omeara1963" "§93D, 93:18 (iii), p. 260 (α ∈ ab𝔬)"]
theorem alpha_mem_span_mul (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b) {α : R}
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1 + algebraMap R F α)
    (hdef : quadDefect R (1 + algebraMap R F α) = span R {algebraMap R F α}) :
    algebraMap R F α ∈ R ∙ (a * b) := by
  obtain ⟨a₁, β₁, a₂, β₂, -, -, h1, h2, h3, h4, -, -, e, he⟩ := exists_blk2_basis Q h2p hfg hU hrk
  obtain ⟨e', he'⟩ := hd
  obtain ⟨ε, -, hdet⟩ := exists_unit_det_gram Q e e'
  rw [he', he, det_blk2] at hdet
  rw [← ha.2] at h1 h3
  rw [← hb] at h2 h4
  obtain ⟨r₁, hr₁⟩ := mem_span_singleton.mp h1
  obtain ⟨s₁, hs₁⟩ := mem_span_singleton.mp h2
  obtain ⟨r₂, hr₂⟩ := mem_span_singleton.mp h3
  obtain ⟨s₂, hs₂⟩ := mem_span_singleton.mp h4
  rw [Algebra.smul_def] at hr₁ hs₁ hr₂ hs₂
  set w : F := (algebraMap R F a₁ * algebraMap R F β₁ - 1) * (algebraMap R F a₂ * algebraMap R F β₂ - 1) - 1
    with hw
  have hscale : ∀ z ∈ normIdeal Q L, ∃ z₀ : R, algebraMap R F z₀ = z := fun z hz => by
    have := normIdeal_le_scale Q L hz
    rw [hU.2.1] at this
    exact Submodule.mem_one.mp this
  obtain ⟨a₀, ha₀⟩ := hscale a (ha.2 ▸ mem_span_singleton_self a)
  obtain ⟨b₀, hb₀⟩ := hscale b ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  have hwm : w ∈ R ∙ (a * b) := by
    refine mem_span_singleton.mpr ⟨r₁ * s₁ * r₂ * s₂ * a₀ * b₀ - r₁ * s₁ - r₂ * s₂, ?_⟩
    rw [hw, ← hr₁, ← hs₁, ← hr₂, ← hs₂, Algebra.smul_def, ← ha₀, ← hb₀]
    simp only [map_sub, map_mul]
    ring
  have hmem : algebraMap R F α ∈ quadDefect R (1 + algebraMap R F α) := by
    rw [hdef]; exact mem_span_singleton_self _
  have h1w : 1 + algebraMap R F α = algebraMap R F ε ^ 2 * (1 + w) := by
    rw [hdet, hw]; ring
  rw [h1w, quadDefect_sq_mul] at hmem
  have hle := mul_le_mul' (le_refl (span R {algebraMap R F ε ^ 2})) (quadDefect_one_add_le (R := R) w)
  have hm2 := hle hmem
  rw [span_mul_span, Set.singleton_mul_singleton] at hm2
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hm2
  obtain ⟨d, hd⟩ := mem_span_singleton.mp hwm
  refine mem_span_singleton.mpr ⟨c * ε ^ 2 * d, ?_⟩
  rw [← hc, ← hd]
  simp only [Algebra.smul_def, map_mul, map_pow]
  ring

end Split

section NormGroup

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The value of $Q$ on $\sum_i c_i e_i$ for a base $e$ with matrix `blk2 p q r s`. -/
theorem Q_blk2_comb {e : Fin 4 → V} {p q r s : F} (hg : gram Q e = blk2 p q r s) (c : Fin 4 → F) :
    Q (∑ i, c i • e i) = p * c 0 ^ 2 + 2 * c 0 * c 1 + q * c 1 ^ 2 + r * c 2 ^ 2 + 2 * c 2 * c 3 +
      s * c 3 ^ 2 := by
  rw [Q_sum_gram, hg]
  simp [blk2, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- Elements of the $\mathfrak o$-span of a base $e$ of $V$ are $\sum_i c_i e_i$ with $c_i \in \mathfrak o$. -/
theorem exists_coeffs {n : ℕ} (e : Fin n → V) {z : V} (hz : z ∈ span R (Set.range e)) :
    ∃ c : Fin n → R, z = ∑ i, algebraMap R F (c i) • e i := by
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hz
  exact ⟨c, by rw [← hc]; simp [algebraMap_smul]⟩

/-- **The norm group of $J \cong A(a, q) \perp A(b, s)$** (O'Meara 1963, p. 260: "every number represented by $J$ is
in $a\mathfrak o^2 + b\mathfrak o = \mathfrak gL$, hence $\mathfrak gJ \subseteq \mathfrak gL$; but $a$ is a norm
generator of $J$ and $J$ represents the number $b$ with $\operatorname{ord}_{\mathfrak p} a +
\operatorname{ord}_{\mathfrak p} b$ odd, so $b \in \mathfrak wJ$, hence $\mathfrak gJ = a\mathfrak o^2 + \mathfrak wJ
\supseteq \mathfrak gL$"): let $L$ be a unimodular lattice with norm generator $a$ and weight generator $b$,
$\operatorname{ord} a + \operatorname{ord} b$ odd, and let $M = \mathfrak oe_1 + \dots + \mathfrak oe_4$ be a unimodular
lattice whose base $e$ has matrix `blk2 a q b s` with $q, s \in b\mathfrak o$. Then $\mathfrak gM = \mathfrak gL$. -/
theorem normGroup_eq_of_blk2 (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {e : Fin 4 → V} {q s : F} (hq : q ∈ R ∙ b) (hs : s ∈ R ∙ b)
    (hgram : gram Q e = blk2 a q b s) (hMU : IsUnimodular Q (span R (Set.range e))) :
    normGroup Q L = normGroup Q (span R (Set.range e)) := by
  set M := span R (Set.range e) with hM
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have hset := normGroup_eq_sq_add Q h2p hreg hne ha hb
  -- `2 = t b`, `b = u a`, `q = q' b`, `s = s' b`
  have h1L : (1 : F) ∈ scale Q L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q hb (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  obtain ⟨u, hu⟩ := mem_span_singleton.mp (weight_gen_le_norm_gen Q ha hb (mem_span_singleton_self b))
  obtain ⟨q', hq'⟩ := mem_span_singleton.mp hq
  obtain ⟨s', hs'⟩ := mem_span_singleton.mp hs
  rw [Algebra.smul_def] at ht hu hq' hs'
  have he : ∀ i, e i ∈ M := fun i => subset_span ⟨i, rfl⟩
  have hQe : ∀ i j, bil Q (e i) (e j) = blk2 a q b s i j := fun i j => by
    simpa [gram] using congrFun (congrFun hgram i) j
  have hQa : Q (e 0) = a := by rw [← bil_self, hQe]; simp [blk2]
  have hQb : Q (e 2) = b := by rw [← bil_self, hQe]; simp [blk2]
  -- the value of `Q` on `M`
  have hval : ∀ c : Fin 4 → R, Q (∑ i, algebraMap R F (c i) • e i) = a * algebraMap R F (c 0) ^ 2 +
      b * algebraMap R F (t * c 0 * c 1 + q' * c 1 ^ 2 + c 2 ^ 2 + t * c 2 * c 3 + s' * c 3 ^ 2) := by
    intro c
    rw [Q_blk2_comb Q hgram, ← ht, ← hq', ← hs']
    simp only [map_add, map_mul, map_pow]
    ring
  -- `a` is a norm generator of `M`
  have haM : IsNormGenerator Q M a := by
    refine ⟨hQa ▸ Q_mem_normGroup Q (he 0), le_antisymm ?_ ?_⟩
    · rw [span_singleton_le_iff_mem, ← hQa]; exact Q_mem_normIdeal Q (he 0)
    · rw [normIdeal, span_le]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := exists_coeffs (R := R) (F := F) e hz
      rw [hval]
      refine mem_span_singleton.mpr ⟨c 0 ^ 2 + u * (t * c 0 * c 1 + q' * c 1 ^ 2 + c 2 ^ 2 + t * c 2 * c 3 +
        s' * c 3 ^ 2), ?_⟩
      rw [Algebra.smul_def, ← hu]
      simp only [map_add, map_mul, map_pow]
      ring
  have hbM : b ∈ weight Q M := by
    refine mem_weight_of_odd Q h2p hπ haM ha0 (hQb ▸ Q_mem_normGroup Q (he 2)) hb0 ?_
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - dord hπ a, by omega⟩
  apply le_antisymm
  · intro z hz
    have hz' : z ∈ (normGroup Q L : Set F) := hz
    rw [hset] at hz'
    obtain ⟨ε, η, rfl⟩ := hz'
    refine add_mem ?_ ?_
    · have := Q_mem_normGroup Q (M.smul_mem ε (he 0))
      rwa [← algebraMap_smul F ε (e 0), Q_smul, hQa, mul_comm] at this
    · have hw : algebraMap R F η * b ∈ weight Q M := by
        rw [← Algebra.smul_def]; exact (weight Q M).smul_mem η hbM
      have := normGroupIdeal_subset Q M ((weight_bounds Q M).2.1 hw)
      rwa [mul_comm] at this
  · rintro z ⟨y, hy, c, hc, rfl⟩
    rw [hMU.2.1] at hc
    obtain ⟨c₀, rfl⟩ := Submodule.mem_one.mp hc
    obtain ⟨x, rfl⟩ := exists_coeffs (R := R) (F := F) e hy
    have hz : Q (∑ i, algebraMap R F (x i) • e i) + 2 * algebraMap R F c₀ ∈ (normGroup Q L : Set F) := by
      rw [hset, hval]
      refine ⟨x 0, t * x 0 * x 1 + q' * x 1 ^ 2 + x 2 ^ 2 + t * x 2 * x 3 + s' * x 3 ^ 2 + t * c₀, ?_⟩
      rw [← ht]
      simp only [map_add, map_mul, map_pow]
      ring
    exact hz

end NormGroup

section Hasse

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- **$S_{\mathfrak p}(FJ) = -S_{\mathfrak p}(FK)$** (O'Meara 1963, p. 260, "if we compute Hasse symbols using the
rules of §63B we obtain $S_{\mathfrak p}(FJ) = -S_{\mathfrak p}(FK)$"), on the orthogonal bases `dw2` of
$FJ \cong A(a, -\alpha a^{-1}) \perp A(b, 0)$ and $FK \cong A(a, -(\alpha - 4\rho)a^{-1}) \perp A(b, 4\rho b^{-1})$.
Here $\alpha \in \mathfrak p$, $\Delta = 1 + 4\rho$ has quadratic defect $4\mathfrak o$, and
$\operatorname{ord} a + \operatorname{ord} b$ is odd. -/
theorem hasse_J_mul_hasse_K (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hodd : Odd (dord hπ a + dord hπ b)) {α ρ : R}
    (hαp : α ∈ maximalIdeal R) (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    hasseS F (dw2 a (-(algebraMap R F α) / a) b 0) *
      hasseS F (dw2 a (-(algebraMap R F α - 4 * algebraMap R F ρ) / a) b (4 * algebraMap R F ρ / b)) = -1 := by
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h2R : (2 : R) ≠ 0 := fun h => two_ne_zero (α := F) (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  have hinj := IsFractionRing.injective R F
  have algne : ∀ {u : R}, IsUnit u → algebraMap R F u ≠ 0 := fun hu h =>
    hu.ne_zero (hinj (by rw [h, map_zero]))
  -- the units `d = 1 + α`, `d' = 1 + α - 4ρ`, `e = 1 - 4ρ`
  have hdu : IsUnit (1 + α) := isUnit_one_add_aux hαp
  have hd'u : IsUnit (1 + (α - 4 * ρ)) := isUnit_one_add_aux (sub_mem hαp h4m)
  have heu : IsUnit (1 + -(4 * ρ)) := isUnit_one_add_aux (neg_mem h4m)
  have hΔu : IsUnit (1 + 4 * ρ) := isUnit_one_add_aux h4m
  set d : F := 1 + algebraMap R F α with hd
  set d' : F := 1 + algebraMap R F α - 4 * algebraMap R F ρ with hd'
  set e : F := 1 - 4 * algebraMap R F ρ with he
  have hd0 : d ≠ 0 := by have := algne hdu; simpa [hd] using this
  have hd'0 : d' ≠ 0 := by
    have := algne hd'u; simp only [map_add, map_one, map_sub, map_mul, map_ofNat] at this
    rw [hd']; convert this using 1; ring
  have he0 : e ≠ 0 := by
    have := algne heu; simp only [map_add, map_one, map_neg, map_mul, map_ofNat] at this
    rw [he]; convert this using 1; ring
  -- `d' e = σ² d` (Local Square Theorem)
  obtain ⟨u, hu⟩ := hdu.exists_left_inv
  set θ : R := -(ρ * (2 + α - 4 * ρ) * u) with hθ
  have hθm : θ ∈ maximalIdeal R := by
    refine neg_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_))
    exact sub_mem (add_mem h2m hαp) h4m
  obtain ⟨σ, hσ⟩ := isSquare_one_add_four_mul hθm
  have hσu : IsUnit (σ * σ) := hσ ▸ isUnit_one_add_aux (Ideal.mul_mem_left _ _ hθm)
  have hσ0 : algebraMap R F σ ≠ 0 := fun h => algne hσu (by rw [map_mul, h, zero_mul])
  have hR1 : (1 + α - 4 * ρ) * (1 - 4 * ρ) = σ * σ * (1 + α) := by
    rw [← hσ, hθ]; linear_combination (4 * ρ * (2 + α - 4 * ρ)) * hu
  have hte : d' * e = algebraMap R F σ ^ 2 * d := by
    have := congrArg (algebraMap R F) hR1
    simp only [map_mul, map_add, map_sub, map_one, map_ofNat] at this
    rw [hd', he, hd]; linear_combination this
  -- `e Δ = τ²`
  have hρρ : -(4 * ρ * ρ) ∈ maximalIdeal R := neg_mem (Ideal.mul_mem_right ρ _ h4m)
  obtain ⟨τ, hτ⟩ := isSquare_one_add_four_mul hρρ
  have hτu : IsUnit (τ * τ) := hτ ▸ isUnit_one_add_aux (Ideal.mul_mem_left _ _ hρρ)
  have hτ0 : algebraMap R F τ ≠ 0 := fun h => algne hτu (by rw [map_mul, h, zero_mul])
  have hΔ0 : algebraMap R F (1 + 4 * ρ) ≠ 0 := algne hΔu
  have heΔ : e = (algebraMap R F τ / algebraMap R F (1 + 4 * ρ)) ^ 2 * algebraMap R F (1 + 4 * ρ) := by
    have := congrArg (algebraMap R F) hτ
    simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at this
    rw [he]; field_simp
    simp only [map_add, map_mul, map_one, map_ofNat] at hΔ0 ⊢
    linear_combination this
  -- the two orthogonal bases
  have hJ : dw2 a (-(algebraMap R F α) / a) b 0 = ![a, -(a * d), b, -b] := by
    funext i; fin_cases i <;> simp [dw2, hd] <;> field_simp <;> ring
  have hK' : dw2 a (-(algebraMap R F α - 4 * algebraMap R F ρ) / a) b (4 * algebraMap R F ρ / b) =
      ![a, -(a * d'), b, -(b * e)] := by
    funext i; fin_cases i <;> simp [dw2, hd', he] <;> field_simp <;> ring
  rw [hJ, hK', hasseS_four_diff hK ha0 hb0 hd0 hd'0 he0 (hdd_of hK hd0 hd'0 he0 hte hσ0) ⟨_, hσ0, hte⟩]
  have hx0 : -(a * b * d) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha0 hb0) hd0)
  rw [heΔ, hs_sq_right _ _ _ (div_ne_zero hτ0 hΔ0), hilbert_delta_parity hK h2R hΔu hρ hπ hx0]
  have hdd : dord hπ d = 0 := by rw [hd, ← map_one (algebraMap R F), ← map_add]; exact dord_unit hπ hdu
  rw [dord_neg hπ (mul_ne_zero (mul_ne_zero ha0 hb0) hd0), dord_mul hπ (mul_ne_zero ha0 hb0) hd0,
    dord_mul hπ ha0 hb0, hdd, add_zero, if_neg (Int.not_even_iff_odd.mpr hodd)]

end Hasse

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$dK = dJ$** (O'Meara 1963, p. 260, "it is easily checked that $dJ = dL = dK$"): for $\alpha \in \mathfrak p$,
$(1 + \alpha - 4\rho)(1 - 4\rho) = \sigma^2(1 + \alpha)$ with $\sigma \neq 0$ (Local Square Theorem). -/
theorem exists_sq_discK (h2p : ¬ IsUnit (2 : R)) {α ρ : R} (hαp : α ∈ maximalIdeal R) :
    ∃ σ : F, σ ≠ 0 ∧ (1 + algebraMap R F α - 4 * algebraMap R F ρ) * (1 - 4 * algebraMap R F ρ) =
      σ ^ 2 * (1 + algebraMap R F α) := by
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  have hinj := IsFractionRing.injective R F
  obtain ⟨u, hu⟩ := (isUnit_one_add_aux hαp).exists_left_inv
  set θ : R := -(ρ * (2 + α - 4 * ρ) * u) with hθ
  have hθm : θ ∈ maximalIdeal R := by
    refine neg_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_))
    exact sub_mem (add_mem h2m hαp) h4m
  obtain ⟨σ, hσ⟩ := isSquare_one_add_four_mul hθm
  have hσu : IsUnit (σ * σ) := hσ ▸ isUnit_one_add_aux (Ideal.mul_mem_left _ _ hθm)
  have hσ0 : algebraMap R F σ ≠ 0 := fun h => hσu.ne_zero (hinj (by rw [map_mul, h, zero_mul, map_zero]))
  have hR1 : (1 + α - 4 * ρ) * (1 - 4 * ρ) = σ * σ * (1 + α) := by
    rw [← hσ, hθ]; linear_combination (4 * ρ * (2 + α - 4 * ρ)) * hu
  refine ⟨algebraMap R F σ, hσ0, ?_⟩
  have := congrArg (algebraMap R F) hR1
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat] at this
  linear_combination this

/-- A lattice $L \cong A(p, q) \perp A(r, s)$ of rank $\dim V = 4$ gives an $F$-base of $V$ with matrix
`blk2 p q r s`. -/
theorem rep_of_hasBlk (hV : finrank F V = 4) {L : Submodule R V} {p q r s : F} (h : HasBlk Q L p q r s)
    (hdet : (p * q - 1) * (r * s - 1) ≠ 0) : Rep Q (blk2 p q r s) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨eF, heF⟩ := Eng93.basisF_of_lattice Q e (by rw [he, det_blk2]; exact hdet) hV
  exact ⟨eF, by rw [← he]; congr 1; funext i; exact heF i⟩

/-- **Example 93:18 (iii)** (O'Meara 1963, §93D, pp. 260–261). Let $L$ be a unimodular lattice on a $4$-dimensional
quadratic space $V$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator of $L$ with
$\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ odd, and write the discriminant as
$dL = 1 + \alpha$ with $\mathfrak d(1 + \alpha) = \alpha\mathfrak o$. Let $\Delta = 1 + 4\rho$ be the unit of quadratic
defect $4\mathfrak o$ (§93, p. 251). Then $\alpha \in ab\mathfrak o$, and $L$ is isometric to exactly one of
$J \cong A(a, -\alpha a^{-1}) \perp A(b, 0)$ and
$K \cong A(a, -(\alpha - 4\rho)a^{-1}) \perp A(b, 4\rho b^{-1})$.

*Form of the statement.* "$L \cong J$" is `HasBlk Q L a (-α/a) b 0`: $L$ has a base with the matrix of $J$ (so the
lattices $J$, $K$ of the book need not be constructed separately). "$dL = 1 + \alpha$" is the existence of a base of
$L$ with discriminant $1 + \alpha$ (equivalently, $dL \cong 1 + \alpha$ modulo $\mathfrak u^2$). "On $V$" is
`finrank F V = 4 = finrank R L`. The local field is abstract: a Henselian discrete valuation ring with finite residue
field whose fraction field satisfies the Hilbert-symbol axioms `LocalHilbertField` (they hold for completions of
number fields, see `omeara93_18_iii_nf`).

*Proof* (O'Meara's): $\alpha \in ab\mathfrak o$ is `alpha_mem_span_mul`. $\mathfrak gJ = \mathfrak gL = \mathfrak gK$
(`normGroup_eq_of_blk2`), $dJ = dL = dK$ (`exists_sq_discK`), and $S_{\mathfrak p}(FJ) = -S_{\mathfrak p}(FK)$
(`hasse_J_mul_hasse_K`); by 63:20 (`rep_diag_iff_S`) $FL$ is isometric to $FJ$ or $FK$, and by 93:16
(`Eng93.exists_basis_gram_of_normGroup_eq`) $L$ is isometric to $J$ or $K$; it is not isometric to both since their
Hasse symbols differ. -/
@[kb "omeara1963" "§93D, 93:18 (iii), pp. 260–261"]
theorem omeara93_18_iii (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    (hV : finrank F V = 4) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : finrank R L = 4) {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {α : R}
    (hd : ∃ e : Basis (Fin 4) R L, (gram Q fun i => (e i : V)).det = 1 + algebraMap R F α)
    (hdef : quadDefect R (1 + algebraMap R F α) = span R {algebraMap R F α})
    {ρ : R} (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) :
    algebraMap R F α ∈ R ∙ (a * b) ∧
      Xor' (HasBlk Q L a (-(algebraMap R F α) / a) b 0)
        (HasBlk Q L a (-(algebraMap R F α - 4 * algebraMap R F ρ) / a) b (4 * algebraMap R F ρ / b)) := by
  have hαab := alpha_mem_span_mul Q h2p hfg hU hrk ha hb hd hdef
  refine ⟨hαab, ?_⟩
  have hinj := IsFractionRing.injective R F
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  -- `a`, `b` in `𝔬`; `α = c a b`; `2 = t b = m a`
  have hscale : ∀ z ∈ normIdeal Q L, ∃ z₀ : R, algebraMap R F z₀ = z := fun z hz => by
    have := normIdeal_le_scale Q L hz
    rw [hU.2.1] at this
    exact Submodule.mem_one.mp this
  obtain ⟨a₀, ha₀⟩ := hscale a (ha.2 ▸ mem_span_singleton_self a)
  obtain ⟨b₀, hb₀⟩ := hscale b ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hαab
  have h1L : (1 : F) ∈ scale Q L := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b := two_smul_scale_le_weight_gen Q hb
    (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  obtain ⟨m, hm⟩ := mem_span_singleton.mp (weight_gen_le_norm_gen Q ha hb h2b)
  rw [Algebra.smul_def] at hc ht hm
  have hα₀ : α = c * a₀ * b₀ := hinj (by rw [← hc, ← ha₀, ← hb₀]; simp only [map_mul]; ring)
  have hab : a₀ * b₀ ∈ maximalIdeal R := by
    by_contra hn
    have hu : IsUnit (a₀ * b₀) := by
      by_contra hu; exact hn ((mem_maximalIdeal _).mpr hu)
    have hda : dord hπ a = 0 := by rw [← ha₀]; exact dord_unit hπ (isUnit_of_mul_isUnit_left hu)
    have hdb : dord hπ b = 0 := by rw [← hb₀]; exact dord_unit hπ (isUnit_of_mul_isUnit_right hu)
    rw [hda, hdb] at hodd
    exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) hodd
  have hαp : α ∈ maximalIdeal R := by rw [hα₀, mul_assoc]; exact Ideal.mul_mem_left _ _ hab
  -- the parameters of `J` and `K` in `𝔬`
  have hqJ : -(algebraMap R F α) / a = algebraMap R F (-(c * b₀)) := by
    rw [← hc, ← hb₀]; field_simp; simp only [map_neg, map_mul]
  have hqK : -(algebraMap R F α - 4 * algebraMap R F ρ) / a = algebraMap R F (-(c * b₀) + 2 * m * ρ) := by
    rw [← hc, ← hb₀]; field_simp
    simp only [map_neg, map_mul, map_add, map_ofNat]
    linear_combination (-(2 * algebraMap R F ρ)) * hm
  have hsK : 4 * algebraMap R F ρ / b = algebraMap R F (2 * t * ρ) := by
    field_simp
    simp only [map_mul, map_ofNat]
    linear_combination (-(2 * algebraMap R F ρ)) * ht
  have hqJb : -(algebraMap R F α) / a ∈ R ∙ b := by
    rw [hqJ, ← hb₀]; exact mem_span_singleton.mpr ⟨-c, by rw [Algebra.smul_def]; simp⟩
  have hqKb : -(algebraMap R F α - 4 * algebraMap R F ρ) / a ∈ R ∙ b := by
    rw [hqK]
    refine mem_span_singleton.mpr ⟨-c + m * t * ρ, ?_⟩
    rw [Algebra.smul_def, ← hb₀]
    simp only [map_neg, map_mul, map_add, map_ofNat]
    rw [hb₀]
    linear_combination (algebraMap R F m * algebraMap R F ρ) * ht
  have hsKb : 4 * algebraMap R F ρ / b ∈ R ∙ b := by
    rw [hsK]
    refine mem_span_singleton.mpr ⟨t * t * ρ, ?_⟩
    rw [Algebra.smul_def]
    simp only [map_mul, map_ofNat]
    linear_combination (algebraMap R F t * algebraMap R F ρ) * ht
  have hzb : (0 : F) ∈ R ∙ b := zero_mem _
  -- unit determinants
  have huJ : IsUnit ((a₀ * -(c * b₀) - 1) * (b₀ * 0 - 1)) := by
    have : (a₀ * -(c * b₀) - 1) * (b₀ * 0 - 1) = 1 + α := by rw [hα₀]; ring
    rw [this]; exact isUnit_one_add_aux hαp
  have huK : IsUnit ((a₀ * (-(c * b₀) + 2 * m * ρ) - 1) * (b₀ * (2 * t * ρ) - 1)) := by
    have hm₀ : m * a₀ = 2 := hinj (by rw [map_mul, ha₀, hm, map_ofNat])
    have ht₀ : t * b₀ = 2 := hinj (by rw [map_mul, hb₀, ht, map_ofNat])
    have : (a₀ * (-(c * b₀) + 2 * m * ρ) - 1) * (b₀ * (2 * t * ρ) - 1) =
        (1 + (α - 4 * ρ)) * (1 + -(4 * ρ)) := by
      rw [hα₀]; linear_combination (2 * ρ * (b₀ * (2 * t * ρ) - 1)) * hm₀ +
        (2 * ρ) * (-(c * a₀ * b₀) - 1 + 4 * ρ) * ht₀
    rw [this]
    exact (isUnit_one_add_aux (sub_mem hαp h4m)).mul (isUnit_one_add_aux (neg_mem h4m))
  -- the space side: an orthogonal base of `V` from `exists_blk2_basis`
  obtain ⟨a₁, β₁, a₂, β₂, ha₁, ha₂, -, -, -, -, hu₁, hu₂, e, he⟩ := exists_blk2_basis Q h2p hfg hU hrk
  obtain ⟨e', he'⟩ := hd
  obtain ⟨ε, hε, hdet⟩ := exists_unit_det_gram Q e e'
  rw [he', he, det_blk2] at hdet
  have hu₁F : algebraMap R F a₁ * algebraMap R F β₁ - 1 ≠ 0 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub]
    exact fun h => (by simpa [add_comm, sub_eq_add_neg] using hu₁ : IsUnit (a₁ * β₁ - 1)).ne_zero
      (hinj (by rw [h, map_zero]))
  have hu₂F : algebraMap R F a₂ * algebraMap R F β₂ - 1 ≠ 0 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub]
    exact fun h => (by simpa [add_comm, sub_eq_add_neg] using hu₂ : IsUnit (a₂ * β₂ - 1)).ne_zero
      (hinj (by rw [h, map_zero]))
  have hε0 : algebraMap R F ε ≠ 0 := fun h => hε.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨eF, heF⟩ := Eng93.basisF_of_lattice Q e (by rw [he, det_blk2]; exact mul_ne_zero hu₁F hu₂F) hV
  have hspan : span F (L : Set V) = ⊤ := Eng93.span_eq_top_of_basis e eF heF
  have hRepL : Rep Q (blk2 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F a₂) (algebraMap R F β₂)) :=
    rep_of_hasBlk Q hV ⟨e, he⟩ (mul_ne_zero hu₁F hu₂F)
  set w := dw2 (algebraMap R F a₁) (algebraMap R F β₁) (algebraMap R F a₂) (algebraMap R F β₂) with hw
  have hRepw : Rep Q (Matrix.diagonal w) := (rep_blk2_iff Q ha₁ ha₂ _ _).mp hRepL
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i; fin_cases i <;> simp [hw, dw2, ha₁, ha₂, hu₁F, hu₂F]
  set qJ : F := -(algebraMap R F α) / a with hqJdef
  set qK : F := -(algebraMap R F α - 4 * algebraMap R F ρ) / a with hqKdef
  set sK : F := 4 * algebraMap R F ρ / b with hsKdef
  have hdJ : (a * qJ - 1) * (b * 0 - 1) = 1 + algebraMap R F α := by
    rw [hqJdef]; field_simp; ring
  have hdK : (a * qK - 1) * (b * sK - 1) =
      (1 + algebraMap R F α - 4 * algebraMap R F ρ) * (1 - 4 * algebraMap R F ρ) := by
    rw [hqKdef, hsKdef]; field_simp; ring
  have h1α : (1 : F) + algebraMap R F α ≠ 0 := by
    rw [← map_one (algebraMap R F), ← map_add]
    exact fun h => (isUnit_one_add_aux hαp).ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨σ, hσ0, hσ⟩ := exists_sq_discK (F := F) h2p (ρ := ρ) hαp
  have hdK0 : (1 + algebraMap R F α - 4 * algebraMap R F ρ) * (1 - 4 * algebraMap R F ρ) ≠ 0 := by
    rw [hσ]; exact mul_ne_zero (pow_ne_zero 2 hσ0) h1α
  set wJ := dw2 a qJ b 0 with hwJ
  set wK := dw2 a qK b sK with hwK
  have hwJ0 : ∀ i, wJ i ≠ 0 := by
    have h1 : a * qJ - 1 ≠ 0 := fun h => h1α (by rw [← hdJ, h, zero_mul])
    intro i; fin_cases i <;> simp [hwJ, dw2, ha0, hb0, h1]
  have hwK0 : ∀ i, wK i ≠ 0 := by
    have h1 : a * qK - 1 ≠ 0 := fun h => hdK0 (by rw [← hdK, h, zero_mul])
    have h2 : b * sK - 1 ≠ 0 := fun h => hdK0 (by rw [← hdK, h, mul_zero])
    intro i; fin_cases i <;> simp [hwK, dw2, ha0, hb0, h1, h2]
  -- discriminants
  have hprodw : ∏ i, w i = (algebraMap R F a₁ * algebraMap R F a₂ / algebraMap R F ε) ^ 2 *
      (1 + algebraMap R F α) := by
    rw [hdet, hw]; simp [dw2, Fin.prod_univ_four]; field_simp
  have hdiscJ : ∃ t : F, t ≠ 0 ∧ ∏ i, wJ i = t ^ 2 * ∏ i, w i := by
    refine ⟨a * b * algebraMap R F ε / (algebraMap R F a₁ * algebraMap R F a₂), by
      simp [ha0, hb0, hε0, ha₁, ha₂], ?_⟩
    rw [hprodw]
    have : ∏ i, wJ i = a ^ 2 * b ^ 2 * ((a * qJ - 1) * (b * 0 - 1)) := by
      simp [hwJ, dw2, Fin.prod_univ_four]; ring
    rw [this, hdJ]; field_simp
  have hdiscK : ∃ t : F, t ≠ 0 ∧ ∏ i, wK i = t ^ 2 * ∏ i, w i := by
    refine ⟨a * b * σ * algebraMap R F ε / (algebraMap R F a₁ * algebraMap R F a₂), by
      simp [ha0, hb0, hε0, ha₁, ha₂, hσ0], ?_⟩
    rw [hprodw]
    have : ∏ i, wK i = a ^ 2 * b ^ 2 * ((a * qK - 1) * (b * sK - 1)) := by
      simp [hwK, dw2, Fin.prod_univ_four]; ring
    rw [this, hdK, hσ]; field_simp
  -- Hasse symbols
  have hP := hasse_J_mul_hasse_K (R := R) hK h2p hπ ha0 hb0 hodd hαp hρ
  have iffJ := rep_diag_iff_S Q hK hw0 hwJ0 hRepw
  have iffK := rep_diag_iff_S Q hK hw0 hwK0 hRepw
  -- from a representation of the space to an isometry of lattices (93:16)
  have toBlk : ∀ {q s : F} (q₀ s₀ : R), algebraMap R F q₀ = q → algebraMap R F s₀ = s → q ∈ R ∙ b →
      s ∈ R ∙ b → IsUnit ((a₀ * q₀ - 1) * (b₀ * s₀ - 1)) → Rep Q (Matrix.diagonal (dw2 a q b s)) →
      HasBlk Q L a q b s := by
    intro q s q₀ s₀ hq hs hqb hsb hunit hR
    obtain ⟨eX, heX⟩ := (rep_blk2_iff Q ha0 hb0 q s).mpr hR
    have hG : gram Q (fun i => eX i) = (blk2 a₀ q₀ b₀ s₀).map (algebraMap R F) := by
      rw [map_blk2, ha₀, hq, hb₀, hs]; exact heX
    have hGu : IsUnit (blk2 a₀ q₀ b₀ s₀).det := by rw [det_blk2]; exact hunit
    obtain ⟨hMU, -, -, -⟩ := Eng93.span_basis_props Q eX hGu hG
    have hg := normGroup_eq_of_blk2 Q h2p hπ hfg hU ha hb hodd hqb hsb heX hMU
    obtain ⟨bL, hbL⟩ := Eng93.exists_basis_gram_of_normGroup_eq Q hfg hU hspan eX hGu hG hg
    exact ⟨bL, by rw [hbL, map_blk2, ha₀, hq, hb₀, hs]⟩
  -- not both
  have notBoth : ¬ (HasBlk Q L a qJ b 0 ∧ HasBlk Q L a qK b sK) := by
    rintro ⟨hJ, hKb⟩
    have hRJ := (rep_blk2_iff Q ha0 hb0 _ _).mp (rep_of_hasBlk Q hV hJ (by rw [hdJ]; exact h1α))
    have hRK := (rep_blk2_iff Q ha0 hb0 _ _).mp (rep_of_hasBlk Q hV hKb (by rw [hdK]; exact hdK0))
    have hJK := ((rep_diag_iff_S Q hK hwJ0 hwK0 hRJ).mp hRK).2
    rw [← hJK] at hP
    rcases hasseS_pm' wJ with h | h <;> rw [h] at hP <;> norm_num at hP
  have caseJ : hasseS F w = hasseS F wJ → Xor' (HasBlk Q L a qJ b 0) (HasBlk Q L a qK b sK) := fun h => by
    have hJ := toBlk _ _ hqJ.symm (map_zero _) hqJb hzb huJ (iffJ.mpr ⟨hdiscJ, h⟩)
    exact Or.inl ⟨hJ, fun hKb => notBoth ⟨hJ, hKb⟩⟩
  have caseK : hasseS F w = hasseS F wK → Xor' (HasBlk Q L a qJ b 0) (HasBlk Q L a qK b sK) := fun h => by
    have hKb := toBlk _ _ hqK.symm hsK.symm hqKb hsKb huK (iffK.mpr ⟨hdiscK, h⟩)
    exact Or.inr ⟨hKb, fun hJ => notBoth ⟨hJ, hKb⟩⟩
  rcases hasseS_pm' w with h | h <;> rcases hasseS_pm' wJ with h' | h' <;>
    rcases hasseS_pm' wK with h'' | h'' <;> rw [h', h''] at hP <;> norm_num at hP
  · exact caseJ (by rw [h, h'])
  · exact caseK (by rw [h, h''])
  · exact caseK (by rw [h, h''])
  · exact caseJ (by rw [h, h'])

end Main

end QuadFormsKB.OMeara.D18
