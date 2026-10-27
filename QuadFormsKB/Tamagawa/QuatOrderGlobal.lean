/-
# Global to local quaternion orders: completions of a maximal order are maximal

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $a, b \in \mathcal O_F$, $D = (a,b)_F$, $v$ a finite place with completion
$F_v \supseteq \mathfrak o_v$, and $D_v = (a,b)_{F_v}$.

**Contents.**
* `complHom`: the coordinatewise embedding $D \to D_v$ (an $F$-algebra map).
* `localOrder v O`: the completion $\mathcal O_v = \mathfrak o_v\,\iota(\mathcal O)$ of an $\mathcal O_F$-order $\mathcal O$ of $D$ (the $\mathfrak o_v$-span
  of its image), an $\mathfrak o_v$-order of $D_v$ (`isOrder_localOrder`); an $\mathcal O_F$-basis of $\mathcal O$ is an $\mathfrak o_v$-basis
  of $\mathcal O_v$ and an $F_v$-basis of $D_v$ (`linearIndependent_complHom_basis`, `mem_localOrder_iff`).
* **`isMaximalOrder_localOrder`**: if $\mathcal O$ is maximal then so is every completion $\mathcal O_v$ (Voight Lemma 10.4.3).
* **`localOrder_eq_valOrder`** (ramified $v$): $\mathcal O_v = \{x \in D_v : \operatorname{nrd}x \in \mathfrak o_v\}$ (`valOrder`).
* **`exists_algEquiv_localOrder_eq_matOrder`** (split $v$): there is an $F_v$-algebra isomorphism $\varphi : D_v \cong M_2(F_v)$ with
  $\varphi(\mathcal O_v) = M_2(\mathfrak o_v)$.
* `henselianLocalRing_adicCompletionIntegers`: $\mathfrak o_v$ is Henselian (it is complete).

**Proof of local maximality** (Voight's proof of Lemma 10.4.3, made explicit with a basis; a purely local argument plus
weak approximation in the form "$\mathcal O_F \to \mathfrak o_v/\varpi^N$ is onto"). Let $\varpi$ generate $\mathfrak p_v$ and
$\mathcal O'_v \supseteq \mathcal O_v$ be an order. It is finitely generated, so $\varpi^N\mathcal O'_v \subseteq \mathcal O_v$ for some $N$. Put
$$\mathcal O' = \{x \in D : \iota(x) \in \mathcal O'_v,\ \varpi^m x \in \mathcal O \text{ for some } m\},$$
a subring containing $\mathcal O$. Comparing coordinates in the basis $e$ (which is $F_v$-linearly independent in $D_v$) and using
$\varpi^k \mid s$ in $\mathcal O_F$ iff $\iota(\varpi)^k \mid \iota(s)$ in $\mathfrak o_v$, one gets $\varpi^N\mathcal O' \subseteq \mathcal O$, so $\mathcal O'$ is an order
and $\mathcal O' = \mathcal O$ by maximality. Given $y \in \mathcal O'_v$, write $\varpi^Ny = \sum_i d_ie_i$ ($d_i \in \mathfrak o_v$), choose $r_i \in \mathcal O_F$
with $r_i \equiv d_i \bmod \varpi^N$ and put $x = \varpi^{-N}\sum_ir_ie_i$: then $\iota(x) - y \in \mathcal O_v$, so $x \in \mathcal O' = \mathcal O$ and
$y \in \mathcal O_v$.

Sources: Voight, *Quaternion Algebras* (2021), Lemma 10.4.3 (maximality is local; for localizations), Lemma 9.5.3 (lattices and
their completions), Thm. 9.4.9 (local-global dictionary for lattices), Prop. 13.3.4, Cor. 10.5.5 (locators checked in the author's PDF); Weil 1982, §3.1 (the local orders $\mathcal O_v$ of his zeta function).
-/
import QuadFormsKB.Tamagawa.QuatOrderLocal
import QuadFormsKB.Tamagawa.MatOrder
import QuadFormsKB.Tamagawa.OrderNormForm
import QuadFormsKB.LocalDensity.NFBridge

open NumberField IsDedekindDomain Quaternion Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF IsLocalization IsLocalRing

/-! ### $\mathfrak o_v$ is Henselian -/

section Henselian

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- **$\mathfrak o_v$ is a Henselian local ring** (it is $\mathfrak m$-adically complete, `NF.isAdicComplete`; Mathlib's
`IsAdicComplete.henselianRing`). -/
instance henselianLocalRing_adicCompletionIntegers : HenselianLocalRing (v.adicCompletionIntegers F) where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers F)) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))

end Henselian

/-! ### The completion map $D \to D_v$ -/

section Completion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The completion map** $D = (a,b)_F \to D_v = (a,b)_{F_v}$, $x_0 + x_1i + x_2j + x_3k \mapsto$ the same quaternion with
coordinates in $F_v$ (an $F$-algebra homomorphism). -/
def complHom (a b : 𝓞 F) :
    ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b] →ₐ[F]
      ℍ[Fv, algebraMap 𝔬 Fv (ι v a), algebraMap 𝔬 Fv (ι v b)] where
  toFun x := ⟨algebraMap F Fv x.re, algebraMap F Fv x.imI, algebraMap F Fv x.imJ, algebraMap F Fv x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    have ha : algebraMap 𝔬 Fv (ι v a) = algebraMap F Fv (algebraMap (𝓞 F) F a) := rfl
    have hb : algebraMap 𝔬 Fv (ι v b) = algebraMap F Fv (algebraMap (𝓞 F) F b) := rfl
    obtain ⟨x0, x1, x2, x3⟩ := x
    obtain ⟨y0, y1, y2, y3⟩ := y
    simp only [QuaternionAlgebra.mk_mul_mk, ha, hb, map_add, map_sub, map_mul, zero_mul, add_zero]
  map_zero' := by ext <;> simp
  map_add' x y := by
    obtain ⟨x0, x1, x2, x3⟩ := x
    obtain ⟨y0, y1, y2, y3⟩ := y
    simp only [QuaternionAlgebra.mk_add_mk, map_add]
  commutes' r := by
    rw [QuaternionAlgebra.algebraMap_eq]
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · rfl
    all_goals exact (map_zero _).trans (QuaternionAlgebra.algebraMap_eq (R := Fv) _ ▸ rfl)

variable {v}

@[simp] theorem complHom_re (a b : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    (complHom v a b x).re = algebraMap F Fv x.re := rfl
@[simp] theorem complHom_imI (a b : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    (complHom v a b x).imI = algebraMap F Fv x.imI := rfl
@[simp] theorem complHom_imJ (a b : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    (complHom v a b x).imJ = algebraMap F Fv x.imJ := rfl
@[simp] theorem complHom_imK (a b : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    (complHom v a b x).imK = algebraMap F Fv x.imK := rfl

theorem complHom_injective (a b : 𝓞 F) : Function.Injective (complHom v a b) := by
  intro x y h
  have hi : Function.Injective (algebraMap F Fv) := (algebraMap F Fv).injective
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK] at h0 h1 h2 h3
  ext
  exacts [hi h0, hi h1, hi h2, hi h3]

theorem complHom_qi (a b : 𝓞 F) : complHom v a b qi = qi := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK, qi, map_zero, map_one]
theorem complHom_qj (a b : 𝓞 F) : complHom v a b qj = qj := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK, qj, map_zero, map_one]
theorem complHom_qk (a b : 𝓞 F) : complHom v a b qk = qk := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK, qk, map_zero, map_one]

/-- The scalar action of $\iota(r) \in \mathfrak o_v$ ($r \in \mathcal O_F$) on $D_v$ is that of $r \in F$. -/
theorem ι_smul_eq (a b : 𝓞 F) (r : 𝓞 F) (y : ℍ[Fv, algebraMap 𝔬 Fv (ι v a), algebraMap 𝔬 Fv (ι v b)]) :
    (ι v r) • y = (algebraMap (𝓞 F) F r) • y := by
  rw [← algebraMap_smul Fv (ι v r) y, ← algebraMap_smul Fv (algebraMap (𝓞 F) F r) y]
  rfl

theorem complHom_int_smul (a b : 𝓞 F) (r : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    complHom v a b (r • x) = (ι v r) • complHom v a b x := by
  rw [← algebraMap_smul F r x, map_smul, ι_smul_eq]

theorem complHom_smul_int (a b : 𝓞 F) (r : 𝓞 F) (x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    complHom v a b (algebraMap (𝓞 F) F r • x) = (ι v r) • complHom v a b x := by
  rw [map_smul, ι_smul_eq]

/-- **The completion $\mathcal O_v = \mathfrak o_v\,\iota(\mathcal O)$** of an $\mathcal O_F$-order $\mathcal O \subseteq D$ at $v$: the
$\mathfrak o_v$-span of the image of $\mathcal O$ in $D_v$, a subring (it is spanned by the products of a subring).

Source: Voight 2021, Lemma 9.5.3 (completion of lattices). -/
@[kb "voight2021" "Lemma 9.5.3"]
def localOrder (a b : 𝓞 F) (O : Subalgebra (𝓞 F) ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]) :
    Subalgebra 𝔬 ℍ[Fv, algebraMap 𝔬 Fv (ι v a), algebraMap 𝔬 Fv (ι v b)] :=
  Submodule.toSubalgebra (Submodule.span 𝔬 (complHom v a b '' (O : Set _)))
    (Submodule.subset_span ⟨1, O.one_mem, map_one _⟩)
    (fun x y hx hy => by
      have h : Submodule.span 𝔬 (complHom v a b '' (O : Set _)) * Submodule.span 𝔬 (complHom v a b '' (O : Set _)) ≤
          Submodule.span 𝔬 (complHom v a b '' (O : Set _)) := by
        rw [Submodule.span_mul_span, Submodule.span_le]
        rintro _ ⟨_, ⟨x', hx', rfl⟩, _, ⟨y', hy', rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨x' * y', O.mul_mem hx' hy', map_mul _ _ _⟩
      exact h (Submodule.mul_mem_mul hx hy))

theorem mem_localOrder_of_mem (a b : 𝓞 F) {O : Subalgebra (𝓞 F) ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]}
    {x : ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]} (hx : x ∈ O) :
    complHom v a b x ∈ localOrder (v := v) a b O :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- $D = (a,b)_F$ for $a, b \in \mathcal O_F$. -/
abbrev QuatF (F : Type) [Field F] [NumberField F] (a b : 𝓞 F) := ℍ[F, algebraMap (𝓞 F) F a, algebraMap (𝓞 F) F b]

/-- $D_v = (a,b)_{F_v}$ for $a, b \in \mathcal O_F$, with $a, b$ viewed in $\mathfrak o_v$. -/
abbrev QuatV (w : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) :=
  ℍ[w.adicCompletion F, algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F) (ι w a),
    algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F) (ι w b)]

end Completion

/-! ### A basis of the global order is a basis of the completion -/

section Basis

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {O : Subalgebra (𝓞 F) (QuatF F a b)} (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O))

include e in
/-- The images $E_i = \iota(e_i) \in D_v$ of an $\mathcal O_F$-basis $e$ of $\mathcal O$. -/
def complBasisVec (i : Fin 4) : QuatV v a b := complHom v a b (e i : (QuatF F a b))

theorem mem_O_eq_sum {x : QuatF F a b} (hx : x ∈ O) :
    x = ∑ i, algebraMap (𝓞 F) F (e.repr (⟨x, hx⟩ : Subalgebra.toSubmodule O) i) • (e i : (QuatF F a b)) := by
  have h := congrArg Subtype.val (e.sum_repr (⟨x, hx⟩ : Subalgebra.toSubmodule O))
  rw [Submodule.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [algebraMap_smul]; rfl

theorem complHom_mem_eq_sum {x : QuatF F a b} (hx : x ∈ O) :
    complHom v a b x = ∑ i, (ι v (e.repr (⟨x, hx⟩ : Subalgebra.toSubmodule O) i)) • complBasisVec (v := v) e i := by
  conv_lhs => rw [mem_O_eq_sum e hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ι_smul_eq]; rfl

/-- $\mathcal O_v$ is the $\mathfrak o_v$-span of the $E_i$. -/
theorem localOrder_eq_span :
    Subalgebra.toSubmodule (localOrder (v := v) a b O) = Submodule.span 𝔬 (Set.range (complBasisVec (v := v) e)) := by
  apply le_antisymm
  · change Submodule.span 𝔬 _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [complHom_mem_eq_sum e hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_localOrder_of_mem a b (e i).2

/-- **The $E_i$ span $D_v$ over $F_v$** (since $e$ spans $D$ over $F$). -/
theorem top_le_span_complBasisVec (hO : IsOrder (𝓞 F) F O) :
    ⊤ ≤ Submodule.span Fv (Set.range (complBasisVec (v := v) e)) := by
  set S := Submodule.span Fv (Set.range (complBasisVec (v := v) e))
  have hO' : ∀ x ∈ O, complHom v a b x ∈ S := by
    intro x hx
    rw [complHom_mem_eq_sum e hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul Fv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hall : ∀ x : QuatF F a b, complHom v a b x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span F (O : Set (QuatF F a b)) := hO.span ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hO' y hy
    | zero => rw [map_zero]; exact S.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, ← algebraMap_smul Fv c]
      exact S.smul_mem _ hy
  intro y _
  rw [eq_sum_basis y]
  have h1 : (1 : QuatV v a b) ∈ S := by rw [← map_one (complHom v a b)]; exact hall 1
  have hi : (qi : QuatV v a b) ∈ S := by rw [← complHom_qi (v := v) a b]; exact hall _
  have hj : (qj : QuatV v a b) ∈ S := by rw [← complHom_qj (v := v) a b]; exact hall _
  have hk : (qk : QuatV v a b) ∈ S := by rw [← complHom_qk (v := v) a b]; exact hall _
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ h1) (S.smul_mem _ hi)) (S.smul_mem _ hj)) (S.smul_mem _ hk)

/-- **The $E_i$ form an $F_v$-basis of $D_v$.** -/
def complBasis (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) (hO : IsOrder (𝓞 F) F O) : Module.Basis (Fin 4) Fv (QuatV v a b) :=
  basisOfTopLeSpanOfCardEqFinrank (complBasisVec (v := v) e) (top_le_span_complBasisVec e hO)
    (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])

@[simp] theorem complBasis_apply (hO : IsOrder (𝓞 F) F O) (i : Fin 4) :
    complBasis (v := v) e hO i = complBasisVec (v := v) e i := by
  rw [complBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

/-- **Membership in $\mathcal O_v$ by coordinates:** $y \in \mathcal O_v$ iff all its coordinates in the basis $E$ lie in $\mathfrak o_v$. -/
theorem mem_localOrder_iff (hO : IsOrder (𝓞 F) F O) (y : QuatV v a b) :
    y ∈ localOrder (v := v) a b O ↔ ∀ i, IsInteger 𝔬 ((complBasis e hO).repr y i) := by
  constructor
  · intro hy
    have hy' : y ∈ Submodule.span 𝔬 (Set.range (complBasisVec (v := v) e)) := by
      rw [← localOrder_eq_span e]; exact hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      rw [← complBasis_apply e hO, Module.Basis.repr_self]
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨p, hp⟩ := hy i; obtain ⟨q, hq⟩ := hz i
      exact ⟨p + q, by rw [map_add, hp, hq, map_add, Finsupp.add_apply]⟩
    | smul c y _ hy =>
      intro i
      obtain ⟨p, hp⟩ := hy i
      refine ⟨c * p, ?_⟩
      rw [← algebraMap_smul Fv c y, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hp]
  · intro h
    choose c hc using h
    rw [← (complBasis e hO).sum_repr y]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [← hc i, algebraMap_smul, complBasis_apply]
    exact Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (e i).2) _

omit e in
/-- An order of $(a,b)_F$ over the PID $\mathcal O_F$ has an $\mathcal O_F$-basis of 4 elements (`IsLattice.free`, `finrank_order`). -/
theorem exists_basis_order [IsPrincipalIdealRing (𝓞 F)] (hO : IsOrder (𝓞 F) F O) :
    Nonempty (Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) := by
  have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  exact ⟨Module.finBasisOfFinrankEq (𝓞 F) _ (finrank_order a b hO)⟩

omit e in
/-- **The completion of an order is an order** ($\mathcal O_F$ a PID). -/
@[kb "voight2021" "Lemma 9.5.3"]
theorem isOrder_localOrder [IsPrincipalIdealRing (𝓞 F)] (hO : IsOrder (𝓞 F) F O) :
    IsOrder 𝔬 Fv (localOrder (v := v) a b O) := by
  obtain ⟨e⟩ := exists_basis_order hO
  refine ⟨?_, ?_⟩
  · rw [localOrder_eq_span e]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.2 ((top_le_span_complBasisVec e hO).trans (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact mem_localOrder_of_mem a b (e i).2

end Basis

/-! ### Maximality is local -/

section Maximal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} [IsPrincipalIdealRing (𝓞 F)]

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable (v) in
/-- A generator $\varpi \in \mathcal O_F$ of the prime $\mathfrak p_v$ ($\mathcal O_F$ a PID). -/
def genP : 𝓞 F := Submodule.IsPrincipal.generator v.asIdeal

theorem span_genP : v.asIdeal = Ideal.span {genP v} := (Ideal.span_singleton_generator v.asIdeal).symm

theorem genP_ne_zero : genP v ≠ 0 := by
  intro h
  apply v.ne_bot
  rw [span_genP, h, Ideal.span_singleton_eq_bot.2 rfl]

theorem intValuation_genP : v.intValuation (genP v) = WithZero.exp (-1 : ℤ) :=
  v.intValuation_singleton genP_ne_zero span_genP

/-- $\iota(\varpi)$ is a uniformizer of $\mathfrak o_v$. -/
theorem irreducible_ι_genP : Irreducible (ι v (genP v)) :=
  irreducible_of_valued v (by rw [valued_ι, intValuation_genP])

theorem span_ι_genP_pow (k : ℕ) : Ideal.span {ι v (genP v) ^ k} = Ideal.span {π v ^ k} :=
  Ideal.span_singleton_eq_span_singleton.2
    ((IsDiscreteValuationRing.associated_of_irreducible _ irreducible_ι_genP (irreducible_π v)).pow_pow)

/-- $\iota(\varpi)^k \mid \iota(s)$ in $\mathfrak o_v$ implies $\varpi^k \mid s$ in $\mathcal O_F$. -/
theorem genP_pow_dvd_of_ι {k : ℕ} {s : 𝓞 F} (h : ι v (genP v) ^ k ∣ ι v s) : genP v ^ k ∣ s := by
  have h1 : ι v s ∈ Ideal.span {π v ^ k} := by
    rw [← span_ι_genP_pow]; exact Ideal.mem_span_singleton.2 h
  rwa [ι_mem_span_π_pow, span_genP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1

/-- **Weak approximation:** every $d \in \mathfrak o_v$ is $\iota(r) + \iota(\varpi)^kg$ with $r \in \mathcal O_F$, $g \in \mathfrak o_v$. -/
theorem exists_ι_sub_eq (k : ℕ) (d : 𝔬) : ∃ (r : 𝓞 F) (g : 𝔬), d - ι v r = ι v (genP v) ^ k * g := by
  obtain ⟨r, hr⟩ := redHom_surjective v k (Ideal.Quotient.mk _ d)
  have : d - ι v r ∈ Ideal.span {ι v (genP v) ^ k} := by
    rw [span_ι_genP_pow, ← Ideal.Quotient.eq]; exact hr.symm
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.1 this
  exact ⟨r, g, hg⟩

/-- Every $c \in F_v$ becomes integral after multiplying by a power of $\iota(\varpi)$. -/
theorem exists_pow_mul_isInteger (c : Fv) : ∃ N : ℕ, IsInteger 𝔬 (algebraMap 𝔬 Fv (ι v (genP v)) ^ N * c) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝔬) c
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 irreducible_ι_genP
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hu0 : algebraMap 𝔬 Fv (u : 𝔬) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 u.ne_zero
  have hp0 : algebraMap 𝔬 Fv (ι v (genP v)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 irreducible_ι_genP.ne_zero
  have huinv : algebraMap 𝔬 Fv (↑u⁻¹ : 𝔬) = (algebraMap 𝔬 Fv (u : 𝔬))⁻¹ := by
    have h1 := congrArg (algebraMap 𝔬 Fv) u.inv_mul
    rw [map_mul, map_one] at h1
    exact (inv_eq_of_mul_eq_one_left h1).symm
  rw [hu, map_mul, map_mul, map_pow, huinv]
  field_simp

variable {a b : 𝓞 F}

theorem int_smul_injective {r : 𝓞 F} (hr : r ≠ 0) :
    Function.Injective (fun z : QuatF F a b => r • z) := by
  intro z w h
  simp only at h
  rw [← algebraMap_smul F r z, ← algebraMap_smul F r w] at h
  exact smul_right_injective _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr) h

theorem o_smul_injective {c : 𝔬} (hc : c ≠ 0) : Function.Injective (fun z : QuatV v a b => c • z) := by
  intro z w h
  simp only at h
  rw [← algebraMap_smul Fv c z, ← algebraMap_smul Fv c w] at h
  exact smul_right_injective _ ((map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 hc) h

/-- The global order $\{x \in D : \iota(x) \in \mathcal O'_v,\ \varpi^mx \in \mathcal O \text{ for some } m\}$ attached to an order
$\mathcal O$ of $D$ and an $\mathfrak o_v$-subalgebra $\mathcal O'_v$ of $D_v$ (used in `isMaximalOrder_localOrder`). -/
def liftOrder (O : Subalgebra (𝓞 F) (QuatF F a b)) (O' : Subalgebra 𝔬 (QuatV v a b)) :
    Subalgebra (𝓞 F) (QuatF F a b) where
  carrier := {x | complHom v a b x ∈ O' ∧ ∃ m : ℕ, genP v ^ m • x ∈ O}
  mul_mem' := by
    rintro x y ⟨hx, m, hm⟩ ⟨hy, n, hn⟩
    refine ⟨by rw [map_mul]; exact O'.mul_mem hx hy, m + n, ?_⟩
    have : genP v ^ (m + n) • (x * y) = (genP v ^ m • x) * (genP v ^ n • y) := by
      rw [← algebraMap_smul F (genP v ^ (m + n)), ← algebraMap_smul F (genP v ^ m),
        ← algebraMap_smul F (genP v ^ n), smul_mul_smul_comm, ← map_mul, ← pow_add]
    rw [this]; exact O.mul_mem hm hn
  one_mem' := ⟨by rw [map_one]; exact O'.one_mem, 0, by rw [pow_zero, one_smul]; exact O.one_mem⟩
  add_mem' := by
    rintro x y ⟨hx, m, hm⟩ ⟨hy, n, hn⟩
    refine ⟨by rw [map_add]; exact O'.add_mem hx hy, m + n, ?_⟩
    have : genP v ^ (m + n) • (x + y) = genP v ^ n • (genP v ^ m • x) + genP v ^ m • (genP v ^ n • y) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [this]; exact O.add_mem (O.smul_mem hm _) (O.smul_mem hn _)
  zero_mem' := ⟨by rw [map_zero]; exact O'.zero_mem, 0, by rw [smul_zero]; exact O.zero_mem⟩
  algebraMap_mem' := fun r => by
    refine ⟨?_, 0, by rw [pow_zero, one_smul]; exact O.algebraMap_mem r⟩
    have h1 : complHom v a b (algebraMap (𝓞 F) (QuatF F a b) r) = algebraMap 𝔬 (QuatV v a b) (ι v r) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b), AlgHom.commutes,
        IsScalarTower.algebraMap_apply 𝔬 Fv (QuatV v a b), IsScalarTower.algebraMap_apply F Fv (QuatV v a b)]
      rfl
    change complHom v a b (algebraMap (𝓞 F) (QuatF F a b) r) ∈ O'
    rw [h1]
    exact O'.algebraMap_mem _

theorem mem_liftOrder {O : Subalgebra (𝓞 F) (QuatF F a b)} {O' : Subalgebra 𝔬 (QuatV v a b)}
    {x : QuatF F a b} : x ∈ liftOrder O O' ↔ complHom v a b x ∈ O' ∧ ∃ m : ℕ, genP v ^ m • x ∈ O := Iff.rfl

set_option maxHeartbeats 400000 in
/-- **Maximality is a local property (one direction): the completion of a maximal order is maximal.** For $\mathcal O$ a
maximal $\mathcal O_F$-order of $D = (a,b)_F$ ($\mathcal O_F$ a PID) and $v$ a finite place, $\mathcal O_v$ is a maximal
$\mathfrak o_v$-order of $D_v$.

*Proof.* See the module docstring: an order $\mathcal O'_v \supsetneq \mathcal O_v$ would give the order
$\{x \in D : \iota(x) \in \mathcal O'_v,\ \varpi^mx \in \mathcal O\} \supsetneq \mathcal O$.

Source: Voight 2021, Lemma 10.4.3 (stated there for the localizations $\mathcal O_{(\mathfrak p)}$; the completions are handled by
Lemma 9.5.3) and Thm. 9.4.9 (local-global dictionary for lattices). -/
@[kb "voight2021" "Lemma 10.4.3"]
theorem isMaximalOrder_localOrder {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) :
    IsMaximalOrder 𝔬 Fv (localOrder (v := v) a b O) := by
  classical
  refine ⟨isOrder_localOrder hO.1, fun O' hO' hle => ?_⟩
  obtain ⟨e⟩ := exists_basis_order hO.1
  set Eb := complBasis (v := v) e hO.1 with hEb
  set ϖ := genP v with hϖdef
  set ϖ' : 𝔬 := ι v ϖ with hϖ'def
  have hϖ0 : ϖ ≠ 0 := genP_ne_zero
  have hϖ'0 : ϖ' ≠ 0 := irreducible_ι_genP.ne_zero
  have hϖF : algebraMap (𝓞 F) F ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hϖ0
  -- Step A: a power of ϖ' moves O' into O_v
  have hA1 : ∀ z : QuatV v a b, ∃ N : ℕ, ∀ M, N ≤ M → ϖ' ^ M • z ∈ localOrder (v := v) a b O := by
    intro z
    have : ∀ i, ∃ N : ℕ, IsInteger 𝔬 (algebraMap 𝔬 Fv ϖ' ^ N * Eb.repr z i) := fun i =>
      exists_pow_mul_isInteger _
    choose Ni hNi using this
    refine ⟨Finset.univ.sup Ni, fun M hM => ?_⟩
    rw [mem_localOrder_iff e hO.1]
    intro i
    have hle' : Ni i ≤ M := (Finset.le_sup (Finset.mem_univ i)).trans hM
    obtain ⟨t, ht⟩ := hNi i
    refine ⟨ϖ' ^ (M - Ni i) * t, ?_⟩
    rw [← algebraMap_smul Fv (ϖ' ^ M) z, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ht, map_pow,
      map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle']
  choose Nz hNz using hA1
  obtain ⟨S, hS⟩ := hO'.fg
  set N := S.sup Nz
  have hN : ∀ z ∈ O', ϖ' ^ N • z ∈ localOrder (v := v) a b O := by
    intro z hz
    have hz' : z ∈ Submodule.span 𝔬 (S : Set (QuatV v a b)) := by rw [hS]; exact hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem y hy => exact hNz y N (Finset.le_sup hy)
    | zero => rw [smul_zero]; exact Subalgebra.zero_mem _
    | add y w _ _ hy hw => rw [smul_add]; exact Subalgebra.add_mem _ hy hw
    | smul c y _ hy => rw [smul_comm]; exact Subalgebra.smul_mem _ hy _
  -- Step C: the global order O'' and the bound ϖ^N O'' ⊆ O
  have hC : ∀ x : QuatF F a b, complHom v a b x ∈ O' → ∀ m : ℕ, ϖ ^ m • x ∈ O → ϖ ^ N • x ∈ O := by
    intro x hx m hm
    rcases le_or_gt m N with hmN | hmN
    · have : ϖ ^ N • x = ϖ ^ (N - m) • (ϖ ^ m • x) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hmN]
      rw [this]; exact O.smul_mem hm _
    · set k := m - N
      have hmk : m = k + N := by omega
      have ht := (mem_localOrder_iff e hO.1 _).1 (hN _ hx)
      choose t ht using ht
      set sc := e.repr (⟨ϖ ^ m • x, hm⟩ : Subalgebra.toSubmodule O)
      have hrel : ϖ' ^ k • (ϖ' ^ N • complHom v a b x) =
          ∑ i, (algebraMap 𝔬 Fv (ι v (sc i))) • Eb i := by
        rw [smul_smul, ← pow_add, ← hmk, hϖ'def, ← map_pow, ← complHom_int_smul, complHom_mem_eq_sum e hm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [algebraMap_smul Fv (ι v (sc i)), complBasis_apply]
      have hcoord : ∀ i, ϖ' ^ k * t i = ι v (sc i) := by
        intro i
        have := congrArg (fun z => Eb.repr z i) hrel
        simp only [Module.Basis.repr_sum_self] at this
        rw [← algebraMap_smul Fv (ϖ' ^ k), map_smul, Finsupp.smul_apply, smul_eq_mul, ← ht i, ← map_mul] at this
        exact IsFractionRing.injective 𝔬 Fv this
      have hdvd : ∀ i, ϖ ^ k ∣ sc i := fun i =>
        genP_pow_dvd_of_ι ⟨t i, (hcoord i).symm⟩
      choose u hu using hdvd
      set y0 : QuatF F a b := ∑ i, u i • (e i : QuatF F a b)
      have hy0 : y0 ∈ O := Subalgebra.sum_mem _ fun i _ => O.smul_mem (e i).2 _
      have hkey : ϖ ^ k • (ϖ ^ N • x) = ϖ ^ k • y0 := by
        rw [smul_smul, ← pow_add, ← hmk, mem_O_eq_sum e hm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [algebraMap_smul, smul_smul, ← hu i]
      have := int_smul_injective (pow_ne_zero k hϖ0) hkey
      rw [this]; exact hy0
  set O'' := liftOrder (v := v) O O' with hO''def
  have hOO'' : O ≤ O'' := fun x hx =>
    ⟨hle (mem_localOrder_of_mem a b hx), 0, by rw [pow_zero, one_smul]; exact hx⟩
  have hO''ord : IsOrder (𝓞 F) F O'' := by
    refine ⟨?_, eq_top_iff.2 (hO.1.span.symm.le.trans (Submodule.span_mono fun x hx => hOO'' hx))⟩
    set Lm : QuatF F a b →ₗ[𝓞 F] QuatF F a b := ((((algebraMap (𝓞 F) F ϖ ^ N)⁻¹ : F) • LinearMap.id :
          QuatF F a b →ₗ[F] QuatF F a b).restrictScalars (𝓞 F)) with hLm
    have hsub : Subalgebra.toSubmodule O'' ≤ (Subalgebra.toSubmodule O).map Lm := by
      rintro x ⟨hx, m, hm⟩
      refine ⟨ϖ ^ N • x, hC x hx m hm, ?_⟩
      change ((algebraMap (𝓞 F) F ϖ ^ N)⁻¹ : F) • (ϖ ^ N • x) = x
      rw [← algebraMap_smul F (ϖ ^ N) x, smul_smul, map_pow, inv_mul_cancel₀ (pow_ne_zero _ hϖF), one_smul]
    have hN' : IsNoetherian (𝓞 F) ((Subalgebra.toSubmodule O).map Lm) :=
      isNoetherian_of_fg_of_noetherian _ (hO.1.fg.map Lm)
    exact @Submodule.FG.of_le_of_isNoetherian _ _ _ _ _ _ _ hN' hsub
  have heq : O'' = O := hO.2 O'' hO''ord hOO''
  -- Step B: approximate y ∈ O' by a global element
  refine le_antisymm (fun y hy => ?_) hle
  have hy1 := (mem_localOrder_iff e hO.1 _).1 (hN y hy)
  choose d hd using hy1
  have hr := fun i => exists_ι_sub_eq (v := v) N (d i)
  choose r g hrg using hr
  set x : QuatF F a b := ((algebraMap (𝓞 F) F ϖ ^ N)⁻¹ : F) • ∑ i, r i • (e i : QuatF F a b)
  have hxN : ϖ ^ N • x = ∑ i, r i • (e i : QuatF F a b) := by
    rw [← algebraMap_smul F (ϖ ^ N) x, smul_smul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ hϖF), one_smul]
  have hsumO : ∑ i, r i • (e i : QuatF F a b) ∈ O := Subalgebra.sum_mem _ fun i _ => O.smul_mem (e i).2 _
  set w : QuatV v a b := ∑ i, g i • complBasisVec (v := v) e i
  have hw : w ∈ localOrder (v := v) a b O :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (e i).2) _
  have hdiff : y - complHom v a b x = w := by
    apply o_smul_injective (pow_ne_zero N hϖ'0)
    simp only
    have h1 : ϖ' ^ N • y = ∑ i, d i • complBasisVec (v := v) e i := by
      rw [← (Eb).sum_repr (ϖ' ^ N • y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hd i, algebraMap_smul Fv (d i), complBasis_apply]
    have h2 : ϖ' ^ N • complHom v a b x = ∑ i, ι v (r i) • complBasisVec (v := v) e i := by
      rw [hϖ'def, ← map_pow, ← complHom_int_smul, hxN, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [complHom_int_smul]; rfl
    rw [smul_sub, h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, hrg i, smul_smul]
  have hxO' : complHom v a b x ∈ O' := by
    have : complHom v a b x = y - w := by rw [← hdiff]; abel
    rw [this]; exact O'.sub_mem hy (hle hw)
  have hxO : x ∈ O := heq ▸ (show x ∈ O'' from ⟨hxO', N, hxN ▸ hsumO⟩)
  have : y = complHom v a b x + w := by rw [← hdiff]; abel
  rw [this]
  exact (localOrder (v := v) a b O).add_mem (mem_localOrder_of_mem a b hxO) hw

end Maximal

/-! ### The local structure: ramified and split places -/

section LocalStructure

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem algebraMap_two_mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    algebraMap 𝔬 Fv (2 * ι v a * ι v b) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero (mul_ne_zero (by simp) ?_) ?_
  · exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
  · exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)

/-- **At a ramified place the completion of a maximal order is the valuation ring:** if $D_v$ is a division algebra
($\operatorname{nrd}x = 0 \Rightarrow x = 0$) and $\mathcal O$ is a maximal order of $D$ ($ab \ne 0$), then
$\mathcal O_v = \{x \in D_v : \operatorname{nrd}x \in \mathfrak o_v\}$ (`valOrder`).

Source: Voight 2021, Lemma 10.4.3 and Prop. 13.3.4. -/
@[kb "voight2021" "Prop. 13.3.4; Lemma 10.4.3"]
theorem localOrder_eq_valOrder (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0) :
    localOrder (v := v) a b O = valOrder (R := 𝔬) hdiv :=
  eq_valOrder_of_isMaximalOrder (R := 𝔬) (a := ι v a) (b := ι v b) hdiv (algebraMap_two_mul_ne_zero ha hb)
    (isMaximalOrder_localOrder hO)

/-- **At a split place the completion of a maximal order is $M_2(\mathfrak o_v)$:** if $D_v \cong M_2(F_v)$ and $\mathcal O$ is a
maximal order of $D$, there is an $F_v$-algebra isomorphism $\varphi : D_v \cong M_2(F_v)$ with $\varphi(\mathcal O_v) = M_2(\mathfrak o_v)$.

Source: Voight 2021, Lemma 10.4.3 and Cor. 10.5.5. -/
@[kb "voight2021" "Cor. 10.5.5; Lemma 10.4.3"]
theorem exists_algEquiv_localOrder_eq_matOrder {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hsplit : Nonempty (QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv)) :
    ∃ φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv,
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) = matOrder 𝔬 Fv := by
  obtain ⟨φ₀⟩ := hsplit
  have hM := (isMaximalOrder_localOrder (v := v) hO).map φ₀
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_eq_conj_matOrder hM
  refine ⟨φ₀.trans (conjAlgEquiv P Q hPQ hQP).symm, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : φ₀ x ∈ (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) :=
      ⟨x, hx, rfl⟩
    rw [hconj] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) = z := by
      rw [← hzx]; exact (conjAlgEquiv P Q hPQ hQP).symm_apply_apply z
    change (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) ∈ matOrder 𝔬 Fv
    rw [this]; exact hz
  · intro hy
    have h1 : conjAlgEquiv P Q hPQ hQP y ∈
        (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) := by
      rw [hconj]; exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h1
    refine ⟨x, hx, ?_⟩
    change (conjAlgEquiv P Q hPQ hQP).symm (φ₀ x) = y
    rw [show φ₀ x = conjAlgEquiv P Q hPQ hQP y from hxy]
    exact (conjAlgEquiv P Q hPQ hQP).symm_apply_apply y

/-- **Local structure of a maximal order** ($\mathcal O_F$ a PID, $ab \ne 0$): at every finite place either $D_v$ is a division
algebra and $\mathcal O_v$ is its valuation ring, or $D_v \cong M_2(F_v)$ by an isomorphism carrying $\mathcal O_v$ onto
$M_2(\mathfrak o_v)$.

Source: Voight 2021, Lemma 10.4.3, Prop. 13.3.4, Cor. 10.5.5; Weil 1982, §3.7(a) (split or ramified). -/
@[kb "voight2021" "Lemma 10.4.3; Prop. 13.3.4; Cor. 10.5.5"]
theorem localOrder_ramified_or_split (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) :
    (∃ hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0, localOrder (v := v) a b O = valOrder (R := 𝔬) hdiv) ∨
      ∃ φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv,
        (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) = matOrder 𝔬 Fv := by
  by_cases h : ∃ x : QuatV v a b, x ≠ 0 ∧ nrd x = 0
  · right
    have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
    have hb' : algebraMap 𝔬 Fv (ι v b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)
    have h2 := two_ne_zero_of_algebra (F := F) Fv
    exact exists_algEquiv_localOrder_eq_matOrder hO ((nonempty_algEquiv_matrix_iff h2 ha' hb').2
      ((hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha' hb').2 h))
  · left
    push Not at h
    have hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0 := fun x hx => by
      by_contra h0; exact h x h0 hx
    exact ⟨hdiv, localOrder_eq_valOrder ha hb hO hdiv⟩

end LocalStructure

end QuadFormsKB.QuatOrder
