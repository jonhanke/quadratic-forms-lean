/-
# Hanke 2013, §5: $\mathfrak p$-neighbours via the residual quadric (Theorem 5.6, indices)

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §5, pp. 17–19.

**Setting** as in `Even.lean`, with $R$ a Dedekind domain with fraction field $F$ (for a number field,
$R = \mathcal O_F$), $\mathfrak a$ a non-zero fractional ideal (a non-zero finitely generated $R$-submodule of $F$),
$\mathfrak p$ a non-zero prime (hence maximal) ideal of $R$, $N(\mathfrak p) = \#(R/\mathfrak p)$, and indices
$[M : K]$ = `latIndex K M` (`AddSubgroup.relIndex`).

**Proves** all four steps of **Theorem 5.6** (step 1, the lift: `theorem_5_6_lift`, `theorem_5_6_eta`; step 3,
injectivity: `theorem_5_6_injective`; step 4, surjectivity: `theorem_5_6_surjective`, for the corrected Definition 5.1
with $\mathfrak pL\subseteq L'$, $\mathfrak pL'\subseteq L$, see the erratum) and **Remark 5.5** (`remark_5_5`, `remark_5_5_singular`,
`remark_5_5_modular`). Step 2): for an $\mathfrak a$-valued quadratic lattice $L$ and a lift
$\vec v_P\in L\setminus\mathfrak pL$ of a non-singular point of the residual quadric with $Q(\vec v_P)\in\mathfrak p^2\mathfrak a$,
$L' = L'' + \mathfrak p^{-1}\vec v_P$ is a $\mathfrak p$-neighbour of $L$ (`theorem_5_6_isPNeighbor`), with
$L/L''\cong\mathfrak a/\mathfrak p\mathfrak a$ (`theorem_5_6_index`) and $L'/L''\cong\mathfrak p^{-1}/\mathcal O_F$
(`theorem_5_6_index'`), both of order $N(\mathfrak p)$. The key input is that $\mathfrak a/\mathfrak p\mathfrak a$ is a simple
$R$-module (`covBy_smul`), which is the paper's "$L/L''\cong\mathbb F_{\mathfrak p}$ as abelian groups".
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Even
import QuadFormsKB.Literature.Hanke2013Algorithms.Discriminant

open QuadraticMap Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- An ideal $\mathfrak p$ of $R$ as an $R$-submodule of $F$ (its image under $R\to F$). -/
abbrev idealF (p : Ideal R) : Submodule R F := Submodule.map (Algebra.linearMap R F) p

theorem smul_eq_idealF_mul (p : Ideal R) (a : Submodule R F) : p • a = idealF p * a := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ⟨r, hr, rfl⟩ hx
  · rw [Submodule.mul_le]
    rintro _ ⟨r, hr, rfl⟩ x hx
    rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hx

theorem idealF_eq_one_iff {p : Ideal R} : idealF (F := F) p = 1 ↔ p = ⊤ := by
  constructor
  · intro h
    have h1 : (1 : F) ∈ idealF (F := F) p := by rw [h]; exact Submodule.one_le.1 le_rfl
    obtain ⟨r, hr, hr1⟩ := h1
    have : r = 1 := IsFractionRing.injective R F (by rw [map_one]; exact hr1)
    rw [Ideal.eq_top_iff_one]; rwa [← this]
  · rintro rfl
    rw [Submodule.one_eq_range]
    ext x; simp

/-- A submodule of $F$ contained in $\mathcal O_F$ is the image of an ideal. -/
theorem eq_idealF_comap {J : Submodule R F} (h : J ≤ 1) :
    J = idealF (J.comap (Algebra.linearMap R F)) := by
  rw [idealF, Submodule.map_comap_eq, ← Submodule.one_eq_range, inf_eq_right.2 h]

/-- **$\mathfrak a/\mathfrak p\mathfrak a$ is simple:** for a non-zero fractional ideal $\mathfrak a$ and a maximal ideal
$\mathfrak p$ of the Dedekind domain $R$, the only $R$-modules between $\mathfrak p\mathfrak a$ and $\mathfrak a$ are these
two, and they differ. -/
theorem covBy_smul {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal) :
    p • a ⋖ a := by
  have hinv := mul_one_div_cancel_of_fg ha ha0
  have cancel : ∀ J : Submodule R F, J * a * (1 / a) = J := fun J => by rw [mul_assoc, hinv, mul_one]
  refine ⟨lt_of_le_of_ne Submodule.smul_le_right fun h => hp.ne_top ?_, fun N h1 h2 => ?_⟩
  · rw [smul_eq_idealF_mul] at h
    have := congrArg (· * (1 / a)) h
    simp only [cancel, hinv] at this
    exact idealF_eq_one_iff.1 this
  · rw [smul_eq_idealF_mul] at h1
    set J := N * (1 / a) with hJ
    have hJ1 : J ≤ 1 := hinv ▸ mul_le_mul_left h2.le _
    have hPJ : idealF p ≤ J := cancel (idealF p) ▸ mul_le_mul_left h1.le _
    have hJI := eq_idealF_comap hJ1
    have hpI : p ≤ J.comap (Algebra.linearMap R F) := fun r hr => hPJ ⟨r, hr, rfl⟩
    have hNJ : N = J * a := by
      rw [hJ, mul_assoc, mul_comm (1 / a) a, hinv, mul_one]
    generalize J.comap (Algebra.linearMap R F) = I at hJI hpI
    rcases eq_or_ne I ⊤ with hI | hI
    · rw [hNJ, hJI, hI, idealF_eq_one_iff.2 rfl, one_mul] at h2
      exact lt_irrefl _ h2
    · have hI' : p = I := hp.eq_of_le hI hpI
      rw [hNJ, hJI, ← hI'] at h1
      exact lt_irrefl _ h1

/-- A simple $R$-module killed by the maximal ideal $\mathfrak p$ has $N(\mathfrak p) = \#(R/\mathfrak p)$ elements. -/
theorem card_eq_of_isSimpleModule {M : Type*} [AddCommGroup M] [Module R M] [IsSimpleModule R M] {p : Ideal R}
    (hp : p.IsMaximal) (hpM : ∀ r ∈ p, ∀ x : M, r • x = 0) : Nat.card M = Nat.card (R ⧸ p) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 (inferInstance : IsSimpleModule R M)
  have hann : Module.annihilator R M = I := by rw [e.annihilator_eq, Ideal.annihilator_quotient]
  have hpI : p ≤ I := fun r hr => hann ▸ Module.mem_annihilator.2 (hpM r hr)
  have := hp.eq_of_le hI.ne_top hpI
  subst this
  exact Nat.card_congr e.toEquiv

/-- **$\#(\mathfrak a/\mathfrak p\mathfrak a) = N(\mathfrak p)$** for a non-zero fractional ideal $\mathfrak a$. -/
theorem card_subQuot_smul {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal) :
    Nat.card (SubQuot (p • a) a) = Nat.card (R ⧸ p) := by
  have := (covBy_iff_quot_is_simple Submodule.smul_le_right).1 (covBy_smul ha ha0 hp)
  refine card_eq_of_isSimpleModule hp fun r hr x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr x.2

/-- $\mathfrak p^{-1}$ (`pInv`) is O'Meara's $\mathcal O_F/\mathfrak p$ (`1 / idealF p`). -/
theorem pInv_eq_one_div (p : Ideal R) : pInv (F := F) p = 1 / idealF p := by
  ext c
  rw [Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · rintro hc _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs⟩ := hc r hr
    rw [Algebra.linearMap_apply, hs, Submodule.mem_one]
    exact ⟨s, rfl⟩
  · intro hc r hr
    obtain ⟨s, hs⟩ := Submodule.mem_one.1 (hc _ ⟨r, hr, rfl⟩)
    exact ⟨s, hs.symm⟩

theorem idealF_fg (p : Ideal R) : (idealF (F := F) p).FG :=
  (IsNoetherian.noetherian p).map _

theorem idealF_ne_bot {p : Ideal R} (hp0 : p ≠ ⊥) : idealF (F := F) p ≠ ⊥ := by
  intro h
  apply hp0
  rw [eq_bot_iff]
  intro r hr
  have : algebraMap R F r ∈ idealF (F := F) p := ⟨r, hr, rfl⟩
  rw [h, Submodule.mem_bot] at this
  rw [Submodule.mem_bot]
  exact IsFractionRing.injective R F (by rw [this, map_zero])

/-- $\mathfrak p\mathfrak p^{-1} = \mathcal O_F$. -/
theorem smul_pInv {p : Ideal R} (hp0 : p ≠ ⊥) : p • pInv (F := F) p = 1 := by
  rw [smul_eq_idealF_mul, pInv_eq_one_div, mul_one_div_cancel_of_fg (idealF_fg p) (idealF_ne_bot hp0)]

theorem pInv_fg {p : Ideal R} (hp0 : p ≠ ⊥) : (pInv (F := F) p).FG ∧ pInv (F := F) p ≠ ⊥ := by
  rw [pInv_eq_one_div]; exact one_div_fg (idealF_fg p) (idealF_ne_bot hp0)

/-- $1\in\mathfrak p\mathfrak p^{-1}$ (used for induction along a decomposition $1 = \sum r_ic_i$). -/
theorem one_mem_smul_pInv {p : Ideal R} (hp0 : p ≠ ⊥) : (1 : F) ∈ p • pInv (F := F) p := by
  rw [smul_pInv hp0]; exact Submodule.one_le.1 le_rfl

end Ideals

section Neighbors

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $H(\vec v, \cdot)$ as an $R$-linear map $V\to F$. -/
def polarR (v : V) : V →ₗ[R] F where
  toFun x := polar Q v x
  map_add' x y := QuadraticMap.polar_add_right Q v x y
  map_smul' r x := by
    rw [← algebraMap_smul F r x, polar_smul_right, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]

theorem polar_mem_of_valued {a : Submodule R F} {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a) {x y : V}
    (hx : x ∈ L) (hy : y ∈ L) : polar Q x y ∈ a :=
  a.sub_mem (a.sub_mem (hL _ (L.add_mem hx hy)) (hL x hx)) (hL y hy)

/-- The map $L\to\mathfrak a/\mathfrak p\mathfrak a$, $\vec x\mapsto H(\vec v_P,\vec x)$ (needs only $H(\vec v_P, L)\subseteq\mathfrak a$). -/
def resForm {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V} (hvL : ∀ x ∈ L, polar Q v x ∈ a) :
    L →ₗ[R] SubQuot (p • a) a :=
  (Submodule.mkQ _).comp
    (((polarR Q v).comp L.subtype).codRestrict a fun x => hvL x.1 x.2)

theorem ker_resForm {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V}
    (hvL : ∀ x ∈ L, polar Q v x ∈ a) :
    LinearMap.ker (resForm Q (p := p) hvL) = (nbCore Q a p L v).comap L.subtype := by
  ext x
  simp only [LinearMap.mem_ker, resForm, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

/-- **Theorem 5.6, step 2), $[L : L''] = N(\mathfrak p)$, general form**: the proof uses only $H(\vec v_P, L)\subseteq\mathfrak a$,
so it applies to lattices that are $\mathfrak a$-valued for $H$ (as in step 2 of Algorithm 4.6). -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), p. 19 ([L : L''] = N(p), lattices a-valued for H)"]
theorem theorem_5_6_index_gen {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    {L : Submodule R V} {v : V} (hvL : ∀ x ∈ L, polar Q v x ∈ a) (hns : ¬ IsSingularPoint Q a p L v) :
    latIndex (nbCore Q a p L v) L = Nat.card (R ⧸ p) := by
  have hsimple := (covBy_iff_quot_is_simple Submodule.smul_le_right).1 (covBy_smul ha ha0 hp)
  set φ := resForm Q (p := p) hvL
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    rcases hsimple.eq_bot_or_eq_top (LinearMap.range φ) with h | h
    · exfalso; apply hns
      intro y hy
      have : φ ⟨y, hy⟩ = 0 := by
        have := LinearMap.mem_range_self φ ⟨y, hy⟩; rw [h, Submodule.mem_bot] at this; exact this
      have hk : (⟨y, hy⟩ : L) ∈ LinearMap.ker φ := this
      rw [ker_resForm] at hk
      exact hk.2
    · exact h
  rw [← card_subQuot_smul ha ha0 hp]
  show Nat.card (L ⧸ (nbCore Q a p L v).comap L.subtype) = _
  rw [← ker_resForm Q (p := p) hvL]
  exact Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv

/-- **Theorem 5.6, step 2), $[L : L''] = N(\mathfrak p)$** (Hanke 2013, pp. 18–19): for an $\mathfrak a$-valued quadratic
lattice $L$ ($Q(L)\subseteq\mathfrak a$, $\mathfrak a$ a non-zero fractional ideal), a maximal ideal $\mathfrak p$ and
$\vec v_P\in L$ whose point is non-singular ($H(\vec v_P, L)\not\subseteq\mathfrak a\mathfrak p$), $\vec x\mapsto H(\vec v_P,\vec x)$
induces $L/L''\cong\mathfrak a/\mathfrak a\mathfrak p$, so $[L : L''] = N(\mathfrak p)$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), p. 19 ([L : L''] = N(p))"]
theorem theorem_5_6_index {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a) {v : V} (hv : v ∈ L) (hns : ¬ IsSingularPoint Q a p L v) :
    latIndex (nbCore Q a p L v) L = Nat.card (R ⧸ p) :=
  theorem_5_6_index_gen Q ha ha0 hp (fun _ hx => polar_mem_of_valued Q hL hv hx) hns

/-- $\vec v\in L''$ when $Q(\vec v)\in\mathfrak p\mathfrak a$ (as $H(\vec v,\vec v) = 2Q(\vec v)$). -/
theorem mem_nbCore_self {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V} (hv : v ∈ L)
    (hvQ : Q v ∈ p • a) : v ∈ nbCore Q a p L v := by
  refine ⟨hv, ?_⟩
  rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]
  have := (p • a).smul_mem (2 : R) hvQ
  rwa [ofNat_smul_eq_nsmul (R := R) (n := 2), nsmul_eq_mul, Nat.cast_ofNat] at this

/-- If $\mathfrak p^{-1}\vec v\subseteq L$ then $\vec v\in\mathfrak pL$ (from $1\in\mathfrak p\mathfrak p^{-1}$). -/
theorem mem_smul_of_pInv {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} {v : V}
    (h : ∀ c ∈ pInv (F := F) p, c • v ∈ L) : v ∈ p • L := by
  have key : ∀ x ∈ p • pInv (F := F) p, x • v ∈ p • L := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun x => x • v ∈ p • L) hx (fun r hr c hc => ?_)
      (fun x y hx hy => by rw [add_smul]; exact add_mem hx hy)
    rw [smul_assoc]
    exact Submodule.smul_mem_smul hr (h c hc)
  simpa using key 1 (one_mem_smul_pInv hp0)

/-- If $c\,y\in\mathfrak a$ for all $c\in\mathfrak p^{-1}$ then $y\in\mathfrak p\mathfrak a$. -/
theorem mem_smul_of_pInv_mul {a : Submodule R F} {p : Ideal R} (hp0 : p ≠ ⊥) {y : F}
    (h : ∀ c ∈ pInv (F := F) p, c * y ∈ a) : y ∈ p • a := by
  have key : ∀ x ∈ p • pInv (F := F) p, x * y ∈ p • a := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun x => x * y ∈ p • a) hx (fun r hr c hc => ?_)
      (fun x z hx hz => by rw [add_mul]; exact add_mem hx hz)
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr (h c hc)
  simpa using key 1 (one_mem_smul_pInv hp0)

/-- The map $\mathfrak p^{-1}\to L'/L''$, $c\mapsto c\vec v_P$. -/
def lineMap (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (v : V) :
    pInv (F := F) p →ₗ[R] SubQuot (nbCore Q a p L v) (nbLatP Q a p L v) :=
  (Submodule.mkQ _).comp
    ((((LinearMap.toSpanSingleton F V v).restrictScalars R).comp (pInv (F := F) p).subtype).codRestrict _
      fun c => Submodule.mem_sup_right (mem_pInv_line.2 ⟨c, c.2, rfl⟩))

theorem lineMap_surjective (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (v : V) :
    Function.Surjective (lineMap Q a p L v) := by
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨y, hy, z, hz, hw⟩ := Submodule.mem_sup.1 w.2
    obtain ⟨c, hc, rfl⟩ := mem_pInv_line.1 hz
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [lineMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((c • v : V) - w.1) ∈ nbCore Q a p L v
    rw [← hw, sub_add_cancel_right]
    exact neg_mem hy

theorem mem_ker_lineMap {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V} {c : pInv (F := F) p} :
    c ∈ LinearMap.ker (lineMap Q a p L v) ↔ (c : F) • v ∈ nbCore Q a p L v := by
  rw [LinearMap.mem_ker, lineMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- **Theorem 5.6, step 2), $[L' : L''] = N(\mathfrak p)$, general form**: the proof uses only $\vec v_P\in L''$ (that is,
$\vec v_P\in L$ and $H(\vec v_P,\vec v_P)\in\mathfrak a\mathfrak p$) and $\vec v_P\notin\mathfrak pL$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), p. 19 ([L' : L''] = N(p), general form)"]
theorem theorem_5_6_index'_gen {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    {L : Submodule R V} {v : V} (hvv : v ∈ nbCore Q a p L v) (hvp : v ∉ p • L) :
    latIndex (nbCore Q a p L v) (nbLatP Q a p L v) = Nat.card (R ⧸ p) := by
  obtain ⟨hfg, hne⟩ := pInv_fg (F := F) hp0
  -- the kernel, as a submodule of `F`, is `𝒪_F = 𝔭 𝔭⁻¹`
  have hKF : (LinearMap.ker (lineMap Q a p L v)).map (pInv (F := F) p).subtype = p • pInv (F := F) p := by
    have hcov := covBy_smul hfg hne hp
    have h1 : p • pInv (F := F) p ≤ (LinearMap.ker (lineMap Q a p L v)).map (pInv (F := F) p).subtype := by
      rw [smul_pInv hp0]
      intro x hx
      obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
      have hr : algebraMap R F r ∈ pInv (F := F) p := fun s _ => ⟨r * s, by rw [map_mul]⟩
      refine ⟨⟨_, hr⟩, mem_ker_lineMap Q |>.2 ?_, rfl⟩
      show algebraMap R F r • v ∈ _
      rw [algebraMap_smul]
      exact (nbCore Q a p L v).smul_mem r hvv
    have h2 : (LinearMap.ker (lineMap Q a p L v)).map (pInv (F := F) p).subtype ≤ pInv (F := F) p := Submodule.map_subtype_le _ _
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd h2 (hcov.2 h1)
      · exfalso; apply hvp
        refine mem_smul_of_pInv (F := F) hp0 fun c hc => ?_
        rw [← h2] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        exact ((mem_ker_lineMap Q).1 hc').1
    · exact h1.symm
  have hsurj := lineMap_surjective Q a p L v
  show Nat.card (SubQuot _ _) = _
  rw [← Nat.card_congr ((lineMap Q a p L v).quotKerEquivOfSurjective hsurj).toEquiv,
    ← card_subQuot_smul hfg hne hp]
  have hK : LinearMap.ker (lineMap Q a p L v) = (p • pInv (F := F) p).comap (pInv (F := F) p).subtype := by
    rw [← hKF, Submodule.comap_map_eq_of_injective (pInv (F := F) p).injective_subtype]
  rw [hK]

/-- **Theorem 5.6, step 2), $[L' : L''] = N(\mathfrak p)$** (Hanke 2013, p. 19: "since $\vec v_P\notin\mathfrak pL$ ... similarly
$[L' : L''] = N_{F/\mathbb Q}(\mathfrak p)$"): for $\vec v_P\in L\setminus\mathfrak pL$ with $Q(\vec v_P)\in\mathfrak p^2\mathfrak a$,
$c\mapsto c\vec v_P$ induces $\mathfrak p^{-1}/\mathcal O_F\cong L'/L''$, so $[L' : L''] = N(\mathfrak p)$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), p. 19 ([L' : L''] = N(p))"]
theorem theorem_5_6_index' {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    {L : Submodule R V} {v : V} (hv : v ∈ L) (hvp : v ∉ p • L) (hvQ : Q v ∈ p • p • a) :
    latIndex (nbCore Q a p L v) (nbLatP Q a p L v) = Nat.card (R ⧸ p) :=
  theorem_5_6_index'_gen Q hp hp0 (mem_nbCore_self Q hv (Submodule.smul_le_right hvQ)) hvp

/-- **Theorem 5.6, step 2): $\eta(P)$ is a $\mathfrak p$-neighbour of $L$** (Hanke 2013, pp. 18–19). For an
$\mathfrak a$-valued quadratic lattice $L$ ($Q(L)\subseteq\mathfrak a$, $\mathfrak a$ a non-zero fractional ideal), a
non-zero prime $\mathfrak p$ and $\vec v_P\in L\setminus\mathfrak pL$ with $Q(\vec v_P)\in\mathfrak p^2\mathfrak a$ lifting a
non-singular point of the residual quadric, $L' = L'' + \mathfrak p^{-1}\vec v_P$ is a $\mathfrak p$-neighbouring
$\mathfrak a$-lattice of $L$ (Definition 5.1): it is $\mathfrak a$-valued, $[L : L\cap L'] = [L' : L\cap L'] = N(\mathfrak p)$
and $H(L, L')\not\subseteq\mathfrak a$. The paper's proof, with $L\cap L' = L''$ (`theorem_5_6_inter`). -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 2), pp. 18–19 (η(P) is a p-neighbour)"]
theorem theorem_5_6_isPNeighbor {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a) {v : V} (hv : v ∈ L) (hvp : v ∉ p • L)
    (hvQ : Q v ∈ p • p • a) (hns : ¬ IsSingularPoint Q a p L v) :
    IsPNeighbor Q a p L (nbLatP Q a p L v) where
  valued := hL
  valued' := (theorem_5_6_valued Q hL hvQ).2
  index := by
    rw [theorem_5_6_inter Q hvQ]; exact theorem_5_6_index Q ha ha0 hp hL hv hns
  index' := by
    rw [theorem_5_6_inter Q hvQ]; exact theorem_5_6_index' Q hp hp0 hv hvp hvQ
  not_valued := by
    by_contra hcon
    push Not at hcon
    apply hns
    intro y hy
    refine mem_smul_of_pInv_mul hp0 fun c hc => ?_
    have := hcon y hy (c • v) (Submodule.mem_sup_right (mem_pInv_line.2 ⟨c, hc, rfl⟩))
    rwa [polar_smul_right, polar_comm, smul_eq_mul] at this

/-- $\mathfrak pL'\subseteq L''$ for $L' = \eta(P)$, general form: only $\vec v_P\in L''$ is used. -/
theorem theorem_5_6_smul_le_gen {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V}
    (hvv : v ∈ nbCore Q a p L v) : p • nbLatP Q a p L v ≤ nbCore Q a p L v := by
  rw [Submodule.smul_le]
  intro r hr w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨c, hc, rfl⟩ := mem_pInv_line.1 hz
  rw [smul_add]
  refine add_mem ((nbCore Q a p L v).smul_mem r hy) ?_
  obtain ⟨s, hs⟩ := hc r hr
  have : r • c • v = s • v := by
    rw [← algebraMap_smul F r, smul_smul, mul_comm, hs, algebraMap_smul]
  rw [this]
  exact (nbCore Q a p L v).smul_mem s hvv

/-- $\eta(P)$ satisfies $\mathfrak pL'\subseteq L''\subseteq L$, so $L'/(L\cap L')$ is killed by $\mathfrak p$. (A $\mathfrak q$-neighbour
for a prime $\mathfrak q\ne\mathfrak p$ of the same norm satisfies Definition 5.1 for $\mathfrak p$ but not this; hence the
*Erratum* on Definition 5.1.) -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 4), p. 19 (pL' ⊆ L)"]
theorem theorem_5_6_smul_le {a : Submodule R F} {p : Ideal R} {L : Submodule R V} {v : V}
    (hv : v ∈ L) (hvQ : Q v ∈ p • p • a) : p • nbLatP Q a p L v ≤ nbCore Q a p L v :=
  theorem_5_6_smul_le_gen Q (mem_nbCore_self Q hv (Submodule.smul_le_right hvQ))

/-- $\mathfrak p\cdot\mathfrak p^{-1}\vec v = \mathcal O_F\vec v$. -/
theorem smul_pInv_line {p : Ideal R} (hp0 : p ≠ ⊥) (v : V) :
    p • (pInv (F := F) p).map ((LinearMap.toSpanSingleton F V v).restrictScalars R) = span R {v} := by
  rw [← Submodule.map_smul'', smul_pInv hp0, Submodule.one_eq_range, ← LinearMap.range_comp,
    LinearMap.span_singleton_eq_range]
  congr 1
  ext
  simp

/-- $L + L' = L + \mathfrak p^{-1}\vec v_P$ for $L' = \eta(P)$. -/
theorem sup_nbLatP (a : Submodule R F) (p : Ideal R) (L : Submodule R V) (v : V) :
    L ⊔ nbLatP Q a p L v = L ⊔ (pInv (F := F) p).map ((LinearMap.toSpanSingleton F V v).restrictScalars R) := by
  rw [nbLatP, ← sup_assoc, sup_eq_left.2 (show nbCore Q a p L v ≤ L from fun x hx => hx.1)]

/-- $\mathfrak p(L + L') = \mathcal O_F\vec v_P + \mathfrak pL$ for $L' = \eta(P)$: the residual line of $P$ is recovered from
$L'$. -/
theorem smul_sup_nbLatP {a : Submodule R F} {p : Ideal R} (hp0 : p ≠ ⊥) (L : Submodule R V) (v : V) :
    p • (L ⊔ nbLatP Q a p L v) = span R {v} ⊔ p • L := by
  rw [sup_nbLatP, Submodule.smul_sup, smul_pInv_line hp0, sup_comm]

/-- **Theorem 5.6, step 3), injectivity** (Hanke 2013, p. 19): if $\eta(P) = \eta(P')$ for lifts $\vec v_P$, $\vec v_{P'}$,
then $\vec v_P$ and $\vec v_{P'}$ span the same line in $L/\mathfrak pL$ ($\mathcal O_F\vec v_P + \mathfrak pL = \mathcal O_F\vec v_{P'} + \mathfrak pL$), i.e.
$P = P'$. Proof as in the paper: $\mathfrak p(L + L')$ is this line (`smul_sup_nbLatP`). No hypothesis on
$\vec v_P$, $\vec v_{P'}$ is needed beyond $\mathfrak p\ne0$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 3), p. 19 (η is injective)"]
theorem theorem_5_6_injective {a : Submodule R F} {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} {v v' : V}
    (h : nbLatP Q a p L v = nbLatP Q a p L v') : span R {v} ⊔ p • L = span R {v'} ⊔ p • L := by
  rw [← smul_sup_nbLatP Q hp0, ← smul_sup_nbLatP Q hp0, h]

/-- **Theorem 5.6, step 1), non-singular shearing** (Hanke 2013, p. 18: "by choosing any lift $\vec w$ ... we can find some
$\lambda\in\mathfrak p$ so that $Q(\vec v_P + \lambda\vec w)\in\mathfrak a\mathfrak p^2$"): for an $\mathfrak a$-valued quadratic lattice
$L$, a maximal ideal $\mathfrak p$ and $\vec x\in L\setminus\mathfrak pL$ with $Q(\vec x)\in\mathfrak a\mathfrak p$ giving a non-singular
point, there is $\vec v\in L$ with $\vec v\equiv\vec x\pmod{\mathfrak pL}$ (the same point) and $Q(\vec v)\in\mathfrak p^2\mathfrak a$;
$\vec v$ is again outside $\mathfrak pL$ and non-singular. Proof: $\mathfrak a = \mathcal O_FH(\vec x,\vec w) + \mathfrak p\mathfrak a$
(`covBy_smul`), so $Q(\vec x) = \lambda H(\vec x,\vec w) + z$ with $\lambda\in\mathfrak p$, $z\in\mathfrak p^2\mathfrak a$; take
$\vec v = \vec x - \lambda\vec w$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 1), p. 18 (existence of the lift v_P)"]
theorem theorem_5_6_lift {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a) {x : V} (hx : x ∈ L) (hxp : x ∉ p • L) (hxQ : Q x ∈ p • a)
    (hns : ¬ IsSingularPoint Q a p L x) :
    ∃ v ∈ L, x - v ∈ p • L ∧ Q v ∈ p • p • a ∧ v ∉ p • L ∧ ¬ IsSingularPoint Q a p L v := by
  simp only [IsSingularPoint, not_forall] at hns
  obtain ⟨w, hw, hxw⟩ := hns
  set h := polar Q x w
  have hha : h ∈ a := polar_mem_of_valued Q hL hx hw
  -- `a = R h + p a`
  have hcov := covBy_smul ha ha0 hp
  have hsup : span R {h} ⊔ p • a = a := by
    have h1 : p • a < span R {h} ⊔ p • a :=
      lt_of_le_of_ne le_sup_right fun he => hxw (he ▸ Submodule.mem_sup_left (Submodule.mem_span_singleton_self h))
    have h2 : span R {h} ⊔ p • a ≤ a := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hha) Submodule.smul_le_right
    rcases h2.lt_or_eq with h2 | h2
    · exact absurd h2 (hcov.2 h1)
    · exact h2
  have hxQ' := hxQ
  rw [← hsup, Submodule.smul_sup] at hxQ'
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxQ'
  obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_span_singleton).1 hy
  have hlw : l • w ∈ p • L := Submodule.smul_mem_smul hl hw
  refine ⟨x - l • w, L.sub_mem hx (L.smul_mem l hw), by rw [sub_sub_cancel]; exact hlw, ?_, ?_, ?_⟩
  · have e : Q (x - l • w) = z + l • l • Q w := by
      rw [← algebraMap_smul F l w, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
        polar_smul_right, ← hyz]
      simp only [smul_eq_mul, h, Algebra.smul_def]
      ring
    rw [e]
    exact add_mem hz (Submodule.smul_mem_smul hl (Submodule.smul_mem_smul hl (hL w hw)))
  · intro hv
    apply hxp
    have := add_mem hv hlw
    rwa [sub_add_cancel] at this
  · intro hsing
    apply hxw
    have e : polar Q x w = polar Q (x - l • w) w + l • polar Q w w := by
      rw [← algebraMap_smul F l w, polar_sub_left, polar_smul_left, smul_eq_mul, Algebra.smul_def]
      ring
    rw [show h = _ from e]
    exact add_mem (hsing w hw) (Submodule.smul_mem_smul hl (polar_mem_of_valued Q hL hw hw))

/-- **Theorem 5.6, $\eta$ on points** (Hanke 2013, pp. 18–19): every non-singular point of the residual $\mathfrak a$-quadric
at a non-zero prime $\mathfrak p$, given by $\vec x\in L\setminus\mathfrak pL$ with $Q(\vec x)\in\mathfrak a\mathfrak p$, has a lift
$\vec v_P\equiv\vec x\pmod{\mathfrak pL}$ with $Q(\vec v_P)\in\mathfrak p^2\mathfrak a$, and $\eta(P) = L'' + \mathfrak p^{-1}\vec v_P$ is a
$\mathfrak p$-neighbour of $L$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, pp. 18–19 (η(P) is a p-neighbour for every non-singular point P)"]
theorem theorem_5_6_eta {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp : p.IsMaximal)
    (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : ∀ x ∈ L, Q x ∈ a) {x : V} (hx : IsResidualPoint Q a p L x)
    (hns : ¬ IsSingularPoint Q a p L x) :
    ∃ v ∈ L, x - v ∈ p • L ∧ Q v ∈ p • p • a ∧ IsPNeighbor Q a p L (nbLatP Q a p L v) := by
  obtain ⟨v, hv, hxv, hvQ, hvp, hvns⟩ := theorem_5_6_lift Q ha ha0 hp hL hx.1 hx.2.1 hx.2.2 hns
  exact ⟨v, hv, hxv, hvQ, theorem_5_6_isPNeighbor Q ha ha0 hp hp0 hL hv hvp hvQ hvns⟩

end Neighbors

section Surjectivity

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A module killed by the maximal ideal $\mathfrak p$ with exactly $N(\mathfrak p) < \infty$ elements is a line over
$R/\mathfrak p$: each non-zero element generates it. -/
theorem span_singleton_eq_top_of_card {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R} (hp : p.IsMaximal)
    [Finite (R ⧸ p)] (hpM : ∀ r ∈ p, ∀ m : M, r • m = 0) (hcard : Nat.card M = Nat.card (R ⧸ p)) {m : M}
    (hm : m ≠ 0) : span R {m} = ⊤ := by
  have hpos : Nat.card (R ⧸ p) ≠ 0 := Nat.card_pos.ne'
  have : Finite M := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  set f := LinearMap.toSpanSingleton R M m
  have hker : LinearMap.ker f = p := by
    have hle : p ≤ LinearMap.ker f := fun r hr => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hpM r hr m
    have hne : LinearMap.ker f ≠ ⊤ := fun h => hm (by
      have : (1 : R) ∈ LinearMap.ker f := h ▸ Submodule.mem_top
      rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at this)
    exact (hp.eq_of_le hne hle).symm
  have hc : Nat.card (LinearMap.range f) = Nat.card M := by
    rw [← Nat.card_congr f.quotKerEquivRange.toEquiv, hker, hcard]
  rw [LinearMap.span_singleton_eq_range]
  apply Submodule.toAddSubgroup_injective
  exact (AddSubgroup.card_eq_iff_eq_top _).1 hc

/-- The subquotient $L'/(L\cap L')$ of a $\mathfrak p$-neighbour is generated by any $\vec v'\in L'\setminus L$, when
$\mathfrak pL'\subseteq L$ and $R/\mathfrak p$ is finite. -/
theorem exists_sub_mem_of_neighbor {p : Ideal R} (hp : p.IsMaximal) [Finite (R ⧸ p)] {L L' : Submodule R V}
    (hidx : (L ⊓ L').toAddSubgroup.relIndex L'.toAddSubgroup = Nat.card (R ⧸ p)) (hpL' : p • L' ≤ L)
    {v' : V} (hv' : v' ∈ L') (hv'L : v' ∉ L) {y : V} (hy : y ∈ L') : ∃ r : R, y - r • v' ∈ L ⊓ L' := by
  have hpM : ∀ r ∈ p, ∀ m : SubQuot (L ⊓ L') L', r • m = 0 := by
    intro r hr m
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨hpL' (Submodule.smul_mem_smul hr m.2), L'.smul_mem r m.2⟩
  have hm : (Submodule.Quotient.mk ⟨v', hv'⟩ : SubQuot (L ⊓ L') L') ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]; exact fun h => hv'L h.1
  have htop := span_singleton_eq_top_of_card hp hpM hidx hm
  have hmem : (Submodule.Quotient.mk ⟨y, hy⟩ : SubQuot (L ⊓ L') L') ∈ span R {Submodule.Quotient.mk ⟨v', hv'⟩} :=
    htop ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨r, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hr
  have := neg_mem hr
  simp only [neg_sub] at this
  exact this

/-- For $c\in\mathfrak p\setminus\mathfrak p^2$ there are $d\in\mathfrak p^{-1}$ and $j\in R\setminus\mathfrak p$ with $cd = j$ (i.e.
$c\mathfrak p^{-1}\not\subseteq\mathfrak p$). -/
theorem exists_mul_pInv_not_mem {p : Ideal R} (hp0 : p ≠ ⊥) {c : R} (hc : c ∈ p) (hc2 : c ∉ p ^ 2) :
    ∃ d ∈ pInv (F := F) p, ∃ j : R, j ∉ p ∧ algebraMap R F c * d = algebraMap R F j := by
  by_contra hcon
  push Not at hcon
  apply hc2
  -- `c = c · 1` with `1 ∈ p p⁻¹`
  have key : ∀ x ∈ p • pInv (F := F) p, ∃ s ∈ p ^ 2, algebraMap R F c * x = algebraMap R F s := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun x => ∃ s ∈ p ^ 2, algebraMap R F c * x = algebraMap R F s) hx
      (fun r hr d hd => ?_) (fun x y ⟨s, hs, hxs⟩ ⟨t, ht, hyt⟩ => ⟨s + t, add_mem hs ht, by rw [mul_add, hxs, hyt,
        map_add]⟩)
    obtain ⟨j, hj⟩ := hd c hc
    have hj' : algebraMap R F c * d = algebraMap R F j := by rw [mul_comm]; exact hj
    have hjp : j ∈ p := by
      by_contra hjp; exact hcon d hd j hjp hj'
    refine ⟨r * j, ?_, ?_⟩
    · rw [pow_two]; exact Ideal.mul_mem_mul hr hjp
    · rw [Algebra.smul_def, mul_left_comm, hj', map_mul]
  obtain ⟨s, hs, hcs⟩ := key 1 (one_mem_smul_pInv hp0)
  rw [mul_one] at hcs
  rwa [IsFractionRing.injective R F hcs]

/-- The cancellation used in step 4): if $\mathfrak pt\subseteq\mathfrak a$ and $ct\in\mathfrak p\mathfrak a$ (with $cd = j\notin\mathfrak p$,
$d\in\mathfrak p^{-1}$) then $t\in\mathfrak a$. -/
theorem mem_of_mul_mem {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) {c j : R} {d : F}
    (hd : d ∈ pInv (F := F) p) (hj : j ∉ p) (hcd : algebraMap R F c * d = algebraMap R F j) {t : F}
    (hpt : ∀ q ∈ p, q • t ∈ a) (hct : algebraMap R F c * t ∈ p • a) : t ∈ a := by
  obtain ⟨s, q, hq, hsq⟩ := hp.exists_inv hj
  have hjt : j • t ∈ a := by
    have := mul_mem_of_mem_pInv hd hct
    rwa [← mul_assoc, mul_comm d, hcd, ← Algebra.smul_def] at this
  have : t = s • j • t + q • t := by
    rw [smul_smul, ← add_smul, hsq, one_smul]
  rw [this]
  exact add_mem (a.smul_mem s hjt) (hpt q hq)

/-- **Theorem 5.6, step 4), for lattices $\mathfrak a$-valued for the Hessian form** (Hanke 2013, p. 19; the form needed in
Algorithm 4.6, step 2, where $L$ is not an $\mathfrak a$-valued quadratic lattice). Let $L$, $L'$ be $\mathfrak a$-valued for $H$
with $[L : L\cap L'] = [L' : L\cap L'] = N(\mathfrak p)$, $\mathfrak pL\subseteq L'$, $\mathfrak pL'\subseteq L$ and
$H(L, L')\not\subseteq\mathfrak a$ ($\mathfrak p$ a non-zero prime with finite residue field). Then for some $c\in\mathfrak p\setminus\mathfrak p^2$
and $\vec v'\in L'$, the vector $\vec v_P = c\vec v'$ lies in $L\setminus\mathfrak pL$, is non-singular, and
$L'' + \mathfrak p^{-1}\vec v_P = L'$. (The proof of `theorem_5_6_surjective`, which adds $Q(\vec v_P) = c^2Q(\vec v')\in\mathfrak p^2\mathfrak a$
when $L'$ is an $\mathfrak a$-valued quadratic lattice.) -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 4), p. 19 (η is surjective; Hessian-valued lattices)"]
theorem theorem_5_6_surjective_gen {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    [Finite (R ⧸ p)] {L L' : Submodule R V} (hHL : ∀ x ∈ L, ∀ y ∈ L, polar Q x y ∈ a)
    (hHL' : ∀ x ∈ L', ∀ y ∈ L', polar Q x y ∈ a)
    (hindex : (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (R ⧸ p))
    (hindex' : (L ⊓ L').toAddSubgroup.relIndex L'.toAddSubgroup = Nat.card (R ⧸ p)) (hpL : p • L ≤ L')
    (hpL' : p • L' ≤ L) (hnv : ∃ x ∈ L, ∃ y ∈ L', polar Q x y ∉ a) :
    ∃ c ∈ p, c ∉ p ^ 2 ∧ ∃ v' ∈ L', c • v' ∈ L ∧ c • v' ∉ p • L ∧ ¬ IsSingularPoint Q a p L (c • v') ∧
      nbLatP Q a p L (c • v') = L' := by
  obtain ⟨x₀, hx₀, v', hv', hx₀v'⟩ := hnv
  have hv'L : v' ∉ L := fun h => hx₀v' (hHL _ hx₀ _ h)
  have hx₀L' : x₀ ∉ L' := fun h => hx₀v' (hHL' _ h _ hv')
  have hpv' : ∀ q ∈ p, q • v' ∈ L := fun q hq => hpL' (Submodule.smul_mem_smul hq hv')
  -- `c ∈ p \ p²`, `c d = j ∉ p`
  obtain ⟨c, hc, hc2⟩ := IsConcreteLE.exists_of_lt (by simpa using Ideal.pow_succ_lt_pow hp0 1 : p ^ 2 < p)
  obtain ⟨d, hd, j, hj, hcd⟩ := exists_mul_pInv_not_mem (F := F) hp0 hc hc2
  obtain ⟨s, q, hq, hsq⟩ := hp.exists_inv hj
  set v := c • v' with hvdef
  have hvL : v ∈ L := hpv' c hc
  have polar_rsmul_left : ∀ (r : R) (x y : V), polar Q (r • x) y = r • polar Q x y := fun r x y => by
    rw [← algebraMap_smul F r x, polar_smul_left, smul_eq_mul, Algebra.smul_def]
  -- the cancellation with `t = H(v', x)`, `x ∈ L`
  have cancel : ∀ x ∈ L, polar Q v x ∈ p • a → polar Q v' x ∈ a := by
    intro x hx hvx
    refine mem_of_mul_mem hp hd hj hcd (fun r hr => ?_) ?_
    · rw [← polar_rsmul_left]; exact hHL _ (hpv' r hr) _ hx
    · rw [← Algebra.smul_def]; rwa [hvdef, polar_rsmul_left] at hvx
  -- `x ∈ L` with `H(v', x) ∈ a` lies in `L'`
  have toL' : ∀ x ∈ L, polar Q v' x ∈ a → x ∈ L' := by
    intro x hx hvx
    have hidx : (L' ⊓ L).toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (R ⧸ p) := by
      rw [inf_comm]; exact hindex
    obtain ⟨r, hr⟩ := exists_sub_mem_of_neighbor hp hidx hpL hx₀ hx₀L' hx
    have hx' : x = (x - r • x₀) + r • x₀ := by abel
    by_cases hrp : r ∈ p
    · rw [hx']; exact add_mem hr.1 (hpL (Submodule.smul_mem_smul hrp hx₀))
    · exfalso
      obtain ⟨s', q', hq', hsq'⟩ := hp.exists_inv hrp
      have h1 : r • polar Q v' x₀ ∈ a := by
        have e : polar Q v' x = polar Q v' (x - r • x₀) + r • polar Q v' x₀ := by
          conv_lhs => rw [hx']
          rw [polar_add_right, polar_comm Q v' (r • x₀), polar_rsmul_left, polar_comm Q x₀ v']
        have := a.sub_mem hvx (hHL' _ hv' _ hr.1)
        rwa [e, add_sub_cancel_left] at this
      have h2 : q' • polar Q v' x₀ ∈ a := by
        rw [← polar_rsmul_left]; exact hHL _ (hpv' q' hq') _ hx₀
      apply hx₀v'
      rw [polar_comm]
      have : polar Q v' x₀ = s' • r • polar Q v' x₀ + q' • polar Q v' x₀ := by
        rw [smul_smul, ← add_smul, hsq', one_smul]
      rw [this]
      exact add_mem (a.smul_mem s' h1) h2
  -- elements of `L ∩ L'` lie in `L''`
  have inCore : ∀ z ∈ L ⊓ L', z ∈ nbCore Q a p L v := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [hvdef, polar_rsmul_left]
    exact Submodule.smul_mem_smul hc (hHL' _ hv' _ hz.2)
  refine ⟨c, hc, hc2, v', hv', hvL, ?_, ?_, ?_⟩
  · -- `v ∉ p L`
    intro hv
    have hdv : d • v ∈ L := by
      refine Submodule.smul_induction_on (p := fun y => d • y ∈ L) hv (fun r hr l hl => ?_)
        (fun y z hy hz => by rw [smul_add]; exact add_mem hy hz)
      obtain ⟨t, ht⟩ := hd r hr
      rw [← algebraMap_smul F r l, smul_smul, ht, algebraMap_smul]
      exact L.smul_mem t hl
    have hjv : j • v' ∈ L := by
      rw [hvdef, ← algebraMap_smul F c v', smul_smul, mul_comm, hcd, algebraMap_smul] at hdv
      exact hdv
    apply hv'L
    have : v' = s • j • v' + q • v' := by rw [smul_smul, ← add_smul, hsq, one_smul]
    rw [this]
    exact add_mem (L.smul_mem s hjv) (hpv' q hq)
  · -- non-singular
    intro hsing
    apply hx₀v'
    rw [polar_comm]
    exact cancel x₀ hx₀ (hsing x₀ hx₀)
  · apply le_antisymm
    · refine sup_le (fun x hx => toL' x hx.1 (cancel x hx.1 hx.2)) ?_
      intro w hw
      obtain ⟨e, he, rfl⟩ := mem_pInv_line.1 hw
      obtain ⟨t, ht⟩ := he c hc
      show e • v ∈ L'
      rw [hvdef, ← algebraMap_smul F c v', smul_smul, ht, algebraMap_smul]
      exact L'.smul_mem t hv'
    · intro y hy
      obtain ⟨r, hr⟩ := exists_sub_mem_of_neighbor hp hindex' hpL' hv' hv'L hy
      have hrd : algebraMap R F (r * s) * d ∈ pInv (F := F) p := by
        rw [← Algebra.smul_def]; exact (pInv (F := F) p).smul_mem _ hd
      have e : y = (y - r • v') + (r * q) • v' + (algebraMap R F (r * s) * d) • v := by
        have h1 : (algebraMap R F (r * s) * d) • v = (r * s * j) • v' := by
          rw [hvdef, ← algebraMap_smul F c v', smul_smul, mul_assoc, mul_comm d, hcd, ← map_mul, algebraMap_smul]
        have h2 : r * q + r * s * j = r := by linear_combination r * hsq
        rw [h1, add_assoc, ← add_smul, h2, sub_add_cancel]
      rw [e]
      refine add_mem (Submodule.mem_sup_left (add_mem (inCore _ hr) (inCore _ ⟨?_, ?_⟩)))
        (Submodule.mem_sup_right (mem_pInv_line.2 ⟨_, hrd, rfl⟩))
      · rw [mul_smul]; exact L.smul_mem _ (hpv' q hq)
      · exact L'.smul_mem _ hv'

/-- **Theorem 5.6, step 4), surjectivity, for the corrected Definition 5.1** (Hanke 2013, p. 19). Let $L$, $L'$ be
$\mathfrak p$-neighbouring $\mathfrak a$-lattices (`IsPNeighbor`) with, in addition, $\mathfrak pL\subseteq L'$ and
$\mathfrak pL'\subseteq L$ (see the *Erratum* on Definition 5.1: without these, a $\mathfrak q$-neighbour for a prime
$\mathfrak q\ne\mathfrak p$ of the same norm is a counterexample), for a non-zero prime $\mathfrak p$ with finite residue field.
Then $L' = \eta(P)$ for a non-singular point $P$: there is $\vec v_P\in L\setminus\mathfrak pL$ with
$Q(\vec v_P)\in\mathfrak p^2\mathfrak a$, $H(\vec v_P, L)\not\subseteq\mathfrak a\mathfrak p$ and $L'' + \mathfrak p^{-1}\vec v_P = L'$.
*Proof* (global instead of the paper's uniformizer $\pi_{\mathfrak p}$): take $\vec x_0\in L$, $\vec v'\in L'$ with
$H(\vec x_0,\vec v')\notin\mathfrak a$, $c\in\mathfrak p\setminus\mathfrak p^2$, and $\vec v_P = c\vec v'$; then
$c\mathfrak p^{-1} + \mathfrak p = \mathcal O_F$ replaces "$\pi_{\mathfrak p}\mathfrak p^{-1} = \mathcal O_{\mathfrak p}$", and the paper's
$K = \{\vec x : H(\vec v',\vec x)\in\mathfrak a\} = L'$ is checked on $L$ using that $L/(L\cap L')$ is a line over $R/\mathfrak p$. -/
@[kb "hanke2013algorithms" "Theorem 5.6, proof step 4), p. 19 (η is surjective)"]
theorem theorem_5_6_surjective {a : Submodule R F} {p : Ideal R} (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    [Finite (R ⧸ p)] {L L' : Submodule R V} (hN : IsPNeighbor Q a p L L') (hpL : p • L ≤ L')
    (hpL' : p • L' ≤ L) :
    ∃ v ∈ L, v ∉ p • L ∧ Q v ∈ p • p • a ∧ ¬ IsSingularPoint Q a p L v ∧ nbLatP Q a p L v = L' := by
  obtain ⟨c, hc, hc2, v', hv', hvL, hvp, hns, heq⟩ := theorem_5_6_surjective_gen Q hp hp0
    (fun x hx y hy => polar_mem_of_valued Q hN.valued hx hy) (fun x hx y hy => polar_mem_of_valued Q hN.valued' hx hy)
    hN.index hN.index' hpL hpL' hN.not_valued
  refine ⟨c • v', hvL, hvp, ?_, hns, heq⟩
  rw [← algebraMap_smul F c v', QuadraticMap.map_smul, smul_eq_mul, mul_assoc, ← Algebra.smul_def,
    ← Algebra.smul_def]
  exact Submodule.smul_mem_smul hc (Submodule.smul_mem_smul hc (hN.valued' v' hv'))

end Surjectivity

section Remark55

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

theorem ideal_smul_eq_idealF_smul (p : Ideal R) (N : Submodule R V) : p • N = idealF (F := F) p • N := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n hn
    rw [← algebraMap_smul F r n]
    exact Submodule.smul_mem_smul ⟨r, hr, rfl⟩ hn
  · rw [Submodule.smul_le]
    rintro _ ⟨r, hr, rfl⟩ n hn
    rw [Algebra.linearMap_apply, algebraMap_smul]
    exact Submodule.smul_mem_smul hr hn

/-- $L^{\#\mathfrak a\mathfrak p} = \mathfrak pL^{\#\mathfrak a}$ for a lattice $L$ (Lemma 2.3). -/
theorem aDual_smul_ideal {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥)
    {L : Submodule R V} (hL : L.IsLattice F) : aDual Q (p • a) L = p • aDual Q a L := by
  have hpa : (p • a).FG := by rw [smul_eq_idealF_mul]; exact (idealF_fg p).mul ha
  have hpa0 : p • a ≠ ⊥ := by rw [smul_eq_idealF_mul]; exact mul_ne_bot' (idealF_ne_bot hp0) ha0
  rw [aDual_eq_smul_dual Q hpa hpa0 hL, aDual_eq_smul_dual Q ha ha0 hL, smul_eq_idealF_mul,
    mul_smul_submodule, ideal_smul_eq_idealF_smul (F := F)]

/-- **Remark 5.5** (Hanke 2013, p. 18), for a bilinear space $(V, B)$ ($B$ = `bil Q`): for a lattice $L$ in $V$
(non-degeneracy is not needed), a non-zero fractional ideal $\mathfrak a$, a non-zero ideal $\mathfrak p$ and $\vec x\in L$,
$B(\vec x,\vec y)\in\mathfrak a\mathfrak p$ for all $\vec y\in L$ if and only if $\vec x\in\mathfrak pL^{\#\mathfrak a}\cap L$. The
paper applies it to the Hessian space $(V, H)$: see `remark_5_5_singular`. -/
@[kb "hanke2013algorithms" "Remark 5.5, p. 18"]
theorem remark_5_5 {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥)
    {L : Submodule R V} (hL : L.IsLattice F) {x : V} (hx : x ∈ L) :
    (∀ y ∈ L, bil Q x y ∈ p • a) ↔ x ∈ p • aDual Q a L ⊓ L := by
  rw [← aDual_smul_ideal Q ha ha0 hp0 hL]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

/-- The bilinear form of $2Q$ is the Hessian form $H$ of $Q$: $B_{2Q}(\vec x,\vec y) = H(\vec x,\vec y)$. -/
theorem bil_two_smul (x y : V) : bil ((2 : F) • Q) x y = polar Q x y := by
  rw [bil, QuadraticMap.associated_apply]
  simp only [smul_apply, smul_eq_mul, polar]
  rw [← mul_sub, ← mul_sub, invOf_smul_eq_iff, two_smul, two_mul]

/-- **Remark 5.5, singular points** (Hanke 2013, p. 18): in the Hessian space $(V, H)$ (the
bilinear space of the quadratic form $2Q$, `bil_two_smul`), a vector $\vec x$ of the lattice $L$ gives a singular
point of the residual quadric ($H(\vec x, L)\subseteq\mathfrak a\mathfrak p$, `IsSingularPoint`) if and only if
$\vec x\in\mathfrak pL^{\#\mathfrak a}\cap L$, the duals taken for $H$. (The paper's non-degeneracy hypothesis is not
needed.) -/
@[kb "hanke2013algorithms" "Remark 5.5, p. 18 (singular points lie in P((pL^{#a} ∩ L)/pL))"]
theorem remark_5_5_singular {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {x : V}
    (hx : x ∈ L) : IsSingularPoint Q a p L x ↔ x ∈ p • aDual ((2 : F) • Q) a L ⊓ L := by
  rw [← remark_5_5 ((2 : F) • Q) ha ha0 hp0 hL hx, IsSingularPoint]
  simp only [bil_two_smul]

/-- **Remark 5.5, modular lattices** (Hanke 2013, p. 18: "for $\mathfrak a$-modular lattices (where $L^{\#\mathfrak a} = L$)
there are no singular points on $Q_{\mathfrak p;\mathfrak a}$"): if $L$ is $\mathfrak a$-modular for $H$, no $\vec x\in L\setminus\mathfrak pL$
is singular. -/
@[kb "hanke2013algorithms" "Remark 5.5, p. 18 (no singular points for a-modular L)"]
theorem remark_5_5_modular {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {p : Ideal R} (hp0 : p ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F)
    (hmod : IsAModular ((2 : F) • Q) a L) {x : V} (hx : x ∈ L) (hxp : x ∉ p • L) :
    ¬ IsSingularPoint Q a p L x := by
  rw [remark_5_5_singular Q ha ha0 hp0 hL hx, hmod]
  exact fun h => hxp h.1

end Remark55

end QuadFormsKB.Hanke2013Algorithms
