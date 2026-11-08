/-
# O'Meara §82K: modular and maximal global lattices complete to modular / maximal local lattices

**Setting.** $F$ is a number field with ring of integers $\mathfrak o = \mathcal O_F$, $V = F^n$ with the form
`Q : QuadForm F n` (O'Meara's $B$ = `OMeara.bil Q.toQuadraticForm`, $B(x,x) = Q(x)$), and $L$ a lattice on $V$
(`Lat F n`). For a finite spot $\mathfrak p$ (= `v : HeightOneSpectrum (𝓞 F)`), $F_\mathfrak p$ = `v.adicCompletion F`,
$\mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F`, the local space is $V_\mathfrak p = F_\mathfrak p^n$ with the form
$Q_\mathfrak p$ = `QuadForm.toQuadraticForm (Q.map (algebraMap F F_𝔭))` ($Q$ with its coefficients viewed in
$F_\mathfrak p$), and $L_\mathfrak p = \mathfrak o_\mathfrak pL$ is `loc v L.1` (`Lattices/Local.lean`).

**Defines** the completion $\mathfrak a_\mathfrak p = \mathfrak o_\mathfrak p\mathfrak a \subseteq F_\mathfrak p$ of an
$\mathfrak o$-submodule $\mathfrak a \subseteq F$ (`locFrac`).

**Proves** (O'Meara 1963, §82K, pp. 238–239, with the completion $\mathfrak o_\mathfrak p$ in place of the localization
used in `Sec82Local.lean`):
* `scale_loc`, `volume_loc`: $\mathfrak sL_\mathfrak p = (\mathfrak sL)_\mathfrak p$ and $\mathfrak vL_\mathfrak p =
  (\mathfrak vL)_\mathfrak p$; `loc_fg`, `finrank_loc`: $L_\mathfrak p$ is finitely generated of rank $n$;
* `isModular_loc_of_isModularLat`: if $L$ is $\mathfrak a$-modular then $L_\mathfrak p$ is
  $\mathfrak a_\mathfrak p$-modular;
* `isMaximal_loc_of_isMaximalLat`: if $L$ is $\mathfrak a$-maximal then $L_\mathfrak p$ is maximal (for the ideal
  $\mathfrak a_\mathfrak p$ up to the scaling used in the proof), by reduction to `Hanke2005.isMaximal_loc` (forms with
  integral coefficients and integral ideals) via `OMeara.IsMaximal.smul_form`.
-/
import QuadFormsKB.Literature.OMeara.Sec102To104
import QuadFormsKB.Literature.Hanke2005.MaximalLocal
import QuadFormsKB.Literature.OMeara.Sec82Scaling
import QuadFormsKB.Literature.OMeara.Sec82Isom

open NumberField IsDedekindDomain Submodule
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The completion of a fractional ideal** (O'Meara 1963, §81E, p. 217): for an $\mathcal O_F$-submodule
$\mathfrak a \subseteq F$, $\mathfrak a_\mathfrak p = \mathfrak o_\mathfrak p\mathfrak a$ is the
$\mathfrak o_\mathfrak p$-submodule of $F_\mathfrak p$ spanned by the image of $\mathfrak a$ under $F \to F_\mathfrak p$. -/
@[kb "omeara1963" "§81E, p. 217 (the completion a_p of a fractional ideal)"]
def locFrac (a : Submodule (𝓞 F) F) : Submodule 𝔬 Fv :=
  span 𝔬 (algebraMap F Fv '' (a : Set F))

/-- $F \to F_\mathfrak p$ is semilinear along $\mathcal O_F \to \mathfrak o_\mathfrak p$: for $r \in \mathcal O_F$ and
$x \in F$, $\iota(r x) = \iota(r)\,\iota(x)$ (with $\iota(r) \in \mathfrak o_\mathfrak p$ acting on $F_\mathfrak p$). -/
theorem algebraMap_smul_int (r : 𝓞 F) (x : F) :
    algebraMap F Fv (r • x) = (algebraMap (𝓞 F) 𝔬 r) • algebraMap F Fv x := by
  change _ = ((algebraMap (𝓞 F) 𝔬 r : 𝔬) : Fv) * _
  rw [algebraMap_int_coe, IsScalarTower.algebraMap_apply (𝓞 F) F Fv, Algebra.smul_def, map_mul]

/-- **Completion of a span:** for a set $S \subseteq F$, $(\mathcal O_F S)_\mathfrak p = \mathfrak o_\mathfrak p
\iota(S)$. -/
theorem locFrac_span (S : Set F) : locFrac v (span (𝓞 F) S) = span 𝔬 (algebraMap F Fv '' S) := by
  apply le_antisymm
  · rw [locFrac, span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [algebraMap_smul_int]; exact Submodule.smul_mem _ _ hx
  · exact span_mono (Set.image_mono subset_span)

/-- $(\alpha\mathfrak o)_\mathfrak p = \alpha\mathfrak o_\mathfrak p$ for $\alpha \in F$. -/
theorem locFrac_span_singleton (d : F) :
    locFrac v (span (𝓞 F) {d}) = span 𝔬 {algebraMap F Fv d} := by
  rw [locFrac_span, Set.image_singleton]

/-- $(\mathfrak a\mathfrak b)_\mathfrak p = \mathfrak a_\mathfrak p\mathfrak b_\mathfrak p$ for $\mathcal O_F$-submodules
$\mathfrak a, \mathfrak b$ of $F$. -/
theorem locFrac_mul (a b : Submodule (𝓞 F) F) : locFrac v (a * b) = locFrac v a * locFrac v b := by
  rw [Submodule.mul_eq_span_mul_set a b, locFrac_span, Set.image_mul, ← Submodule.span_mul_span]
  rfl

/-- $\mathfrak o_\mathfrak p = 1$: the completion of $\mathcal O_F$ is $\mathfrak o_\mathfrak p$. -/
theorem locFrac_one : locFrac v (1 : Submodule (𝓞 F) F) = 1 := by
  rw [Submodule.one_eq_span (R := 𝓞 F) (A := F), locFrac_span, Set.image_singleton, map_one,
    ← Submodule.one_eq_span]

/-- Completion of fractional ideals, $\mathfrak a \mapsto \mathfrak a_\mathfrak p$, as a monoid homomorphism. -/
def locFracHom : Submodule (𝓞 F) F →* Submodule 𝔬 Fv where
  toFun := locFrac v
  map_one' := locFrac_one v
  map_mul' := locFrac_mul v

/-- $(\mathfrak a^k)_\mathfrak p = (\mathfrak a_\mathfrak p)^k$. -/
theorem locFrac_pow (a : Submodule (𝓞 F) F) (k : ℕ) : locFrac v (a ^ k) = locFrac v a ^ k :=
  map_pow (locFracHom v) a k

/-- $(\prod_i \mathfrak a_i)_\mathfrak p = \prod_i (\mathfrak a_i)_\mathfrak p$ over a finite set $s$ of indices. -/
theorem locFrac_prod {ι : Type*} (s : Finset ι) (a : ι → Submodule (𝓞 F) F) :
    locFrac v (∏ i ∈ s, a i) = ∏ i ∈ s, locFrac v (a i) :=
  map_prod (locFracHom v) a s

/-- The completion of a finitely generated $\mathfrak a$ (hypothesis `ha`) is finitely generated. -/
theorem locFrac_fg {a : Submodule (𝓞 F) F} (ha : a.FG) : (locFrac v a).FG := by
  obtain ⟨s, rfl⟩ := ha
  rw [locFrac_span]
  exact Submodule.fg_span (s.finite_toSet.image _)

/-- The completion of a non-zero $\mathfrak a$ (hypothesis `ha`: $\mathfrak a \ne 0$) is non-zero. -/
theorem locFrac_ne_bot {a : Submodule (𝓞 F) F} (ha : a ≠ ⊥) : locFrac v a ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  intro h
  have : algebraMap F Fv x ∈ locFrac v a := subset_span ⟨x, hx, rfl⟩
  rw [h, mem_bot] at this
  exact hx0 ((map_eq_zero _).mp this)

variable (Q : QuadForm F n)

local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- $Q_\mathfrak p(\iota x) = \iota(Q(x))$ for $x \in F^n$, where $\iota : F \to F_\mathfrak p$ (coordinatewise on
vectors, `locVec`). -/
theorem locForm_locVec (x : Fin n → F) :
    Qv (locVec v x) = algebraMap F Fv (Q.toQuadraticForm x) := by
  rw [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply]
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, map_sum, locVec_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- $B_\mathfrak p(\iota x, \iota y) = \iota(B(x, y))$ for $x, y \in F^n$ (O'Meara's bilinear forms of $Q_\mathfrak p$
and $Q$). -/
theorem bil_locVec (x y : Fin n → F) :
    OMeara.bil Qv (locVec v x) (locVec v y) = algebraMap F Fv (OMeara.bil Q.toQuadraticForm x y) := by
  rw [OMeara.bil_eq_half, OMeara.bil_eq_half, ← (locVec v).map_add, locForm_locVec, locForm_locVec,
    locForm_locVec, map_div₀, map_sub, map_sub, map_ofNat]

/-- The matrix of $\iota y_0, \dots, \iota y_{r-1}$ for $Q_\mathfrak p$ is the image under $\iota$ of the matrix of
$y_0, \dots, y_{r-1}$ for $Q$. -/
theorem gram_locVec {r : ℕ} (y : Fin r → Fin n → F) :
    OMeara.gram Qv (fun i => locVec v (y i)) = (OMeara.gram Q.toQuadraticForm y).map (algebraMap F Fv) := by
  ext i j
  simp [OMeara.gram, bil_locVec]

/-- **$\mathfrak sL_\mathfrak p = (\mathfrak sL)_\mathfrak p$** (O'Meara 1963, §82K, p. 238, at the completion): the
scale of the completion of an $\mathcal O_F$-submodule $L \subseteq F^n$ is the completion of its scale. -/
@[kb "omeara1963" "§82K, p. 238 (sL_p = (sL)_p, at the completion)"]
theorem scale_loc (L : Submodule (𝓞 F) (Fin n → F)) :
    OMeara.scale Qv (loc v L) = locFrac v (OMeara.scale Q.toQuadraticForm L) := by
  apply le_antisymm
  · have key : ∀ x ∈ loc v L, ∀ y ∈ loc v L,
        OMeara.bil Qv x y ∈ locFrac v (OMeara.scale Q.toQuadraticForm L) := by
      intro x hx y hy
      change x ∈ span 𝔬 _ at hx
      change y ∈ span 𝔬 _ at hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, hx, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨y, hy, rfl⟩ := hy
          rw [bil_locVec]
          exact subset_span ⟨_, OMeara.bil_mem_scale _ hx hy, rfl⟩
        | zero => simp [OMeara.bil]
        | add y y' _ _ h h' => rw [OMeara.bil_add_right]; exact add_mem h h'
        | smul c y _ h =>
          rw [OMeara.bil_rsmul_right, ← Algebra.smul_def]; exact Submodule.smul_mem _ c h
      | zero => simp [OMeara.bil]
      | add x x' _ _ h h' => rw [OMeara.bil_add_left]; exact add_mem h h'
      | smul c x _ h => rw [OMeara.bil_rsmul_left, ← Algebra.smul_def]; exact Submodule.smul_mem _ c h
    rw [OMeara.scale, span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact key x hx y hy
  · rw [OMeara.scale, locFrac_span, span_le]
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    rw [← bil_locVec]
    exact OMeara.bil_mem_scale _ (locVec_mem_loc v hx) (locVec_mem_loc v hy)

/-- **Completion of an adapted lattice:** $(\sum_i \mathfrak a_i y_i)_\mathfrak p = \sum_i (\mathfrak a_i)_\mathfrak p
\iota y_i$ for $\mathcal O_F$-submodules $\mathfrak a_i \subseteq F$ and vectors $y_i \in F^n$. -/
theorem loc_iSup_smul {r : ℕ} (a : Fin r → Submodule (𝓞 F) F) (y : Fin r → Fin n → F) :
    loc v (⨆ i, a i • span (𝓞 F) {y i}) = ⨆ i, locFrac v (a i) • span 𝔬 {locVec v (y i)} := by
  apply le_antisymm
  · refine span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (OMeara.mem_iSup_smul_span_iff_exists a y x).1 hx
    refine (OMeara.mem_iSup_smul_span_iff_exists (fun i => locFrac v (a i))
      (fun i => locVec v (y i)) _).2 ⟨fun i => algebraMap F Fv (c i), fun i => subset_span ⟨c i, hc i, rfl⟩, ?_⟩
    simp only [map_sum, map_smul, algebraMap_smul]
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := (OMeara.mem_iSup_smul_span_iff_exists _ _ z).1 hz
    refine sum_mem fun i _ => ?_
    suffices h : ∀ t ∈ span 𝔬 (algebraMap F Fv '' (a i : Set F)),
        t • locVec v (y i) ∈ loc v (⨆ i, a i • span (𝓞 F) {y i}) from h _ (hc i)
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, rfl⟩ := ht
      rw [algebraMap_smul, ← (locVec v).map_smul]
      exact locVec_mem_loc v (mem_iSup_of_mem i (smul_mem_smul hγ (mem_span_singleton_self _)))
    | zero => simp
    | add s t _ _ hs ht => rw [add_smul]; exact add_mem hs ht
    | smul s t _ ht => rw [smul_assoc]; exact Submodule.smul_mem _ s ht

/-- **$\mathfrak vL_\mathfrak p = (\mathfrak vL)_\mathfrak p$** (O'Meara 1963, §82K, p. 238, at the completion): the
volume of the completion of a lattice $L$ on $F^n$ (hypothesis `hL`) is the completion of its volume. -/
@[kb "omeara1963" "§82K, p. 238 (vL_p = (vL)_p, at the completion)"]
theorem volume_loc {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    OMeara.volume Qv (loc v L) = locFrac v (OMeara.volume Q.toQuadraticForm L) := by
  classical
  obtain ⟨r, y, hy, hspan, a, ha, rfl⟩ := OMeara.exists_adapted (F := F) hL.fg
  have hspan' : span F (Set.range y) = ⊤ := hspan.trans hL.span_eq_top
  have hr : r = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hy hspan'.ge)
    simpa using this.symm
  subst hr
  have hli : LinearIndependent Fv (fun i => locVec v (y i)) := by
    have h1 : IsUnit (Matrix.of y).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hy)
    have h2 : IsUnit ((Matrix.of y).map (algebraMap F Fv)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact h1.map _
    have e : (fun i => locVec v (y i)) = ((Matrix.of y).map (algebraMap F Fv)).row := by
      funext i j; rfl
    rw [e]
    exact Matrix.linearIndependent_row_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h2)
  rw [loc_iSup_smul, OMeara.volume_eq_of_adapted _ _ hli _
      (fun i => ⟨locFrac_fg v (ha i).1, locFrac_ne_bot v (ha i).2⟩),
    OMeara.volume_eq_of_adapted _ y hy a ha, locFrac_mul, locFrac_pow, locFrac_prod, locFrac_span_singleton,
    gram_locVec, RingHom.map_det]
  rfl

/-- **The completion of a lattice is finitely generated** (O'Meara 1963, §81E, p. 218): $L_\mathfrak p$ is a finitely
generated $\mathfrak o_\mathfrak p$-module for every lattice $L$ on $F^n$. -/
@[kb "omeara1963" "§81E, p. 218 (L_p is a lattice)"]
theorem loc_fg (L : Lat F n) : (loc v L.1).FG := (loc_isLattice v L.2).fg

/-- **The rank of a lattice on $F^n$ is $n$** (O'Meara 1963, §81B, p. 212): for every lattice $L$ on $F^n$,
$\operatorname{rank}_{\mathcal O_F} L = n$. -/
@[kb "omeara1963" "§81B, p. 212 (rank L = dim V for a lattice on V)"]
theorem finrank_lat (L : Lat F n) : Module.finrank (𝓞 F) L.1 = n := by
  rw [OMeara.finrank_eq_finrank_span (F := F), L.2.span_eq_top, finrank_top, Module.finrank_fin_fun]

/-- **The rank of a completed lattice is $n$** (O'Meara 1963, §81B, p. 212 and §81E, p. 218): for every lattice $L$ on
$F^n$, $\operatorname{rank}_{\mathfrak o_\mathfrak p} L_\mathfrak p = n$. -/
@[kb "omeara1963" "§81E, p. 218 (rank L_p = rank L)"]
theorem finrank_loc (L : Lat F n) : Module.finrank 𝔬 (loc v L.1) = n := by
  rw [OMeara.finrank_eq_finrank_span (F := Fv), (loc_isLattice v L.2).span_eq_top, finrank_top,
    Module.finrank_fin_fun]

/-- **The completions of a modular lattice are modular** (O'Meara 1963, §82K, p. 239): if the lattice $L$ on $F^n$ is
$\mathfrak a$-modular for a non-zero fractional ideal $\mathfrak a$ (hypothesis `hL : IsModularLat Q L`), then at every
finite spot $\mathfrak p$ (`v`) the completion $L_\mathfrak p$ is $\mathfrak a_\mathfrak p$-modular for the local form
$Q_\mathfrak p$, with $\mathfrak a_\mathfrak p \ne 0$. (No nondegeneracy hypothesis on $Q$ is needed.) -/
@[kb "omeara1963" "§82K, p. 239 (L a-modular ⟹ L_p a_p-modular, at the completion)"]
theorem isModular_loc_of_isModularLat {L : Lat F n} (hL : IsModularLat Q L) :
    ∃ a : Submodule 𝔬 Fv, a ≠ ⊥ ∧ OMeara.IsModular Qv a (loc v L.1) := by
  obtain ⟨a, -, ha0, hs, hvol⟩ := hL
  have hne : locFrac v a ≠ ⊥ := locFrac_ne_bot v ha0
  refine ⟨locFrac v a, hne, hne, ?_, ?_⟩
  · rw [scale_loc, hs]
  · rw [volume_loc v Q L.2, hvol, locFrac_pow, finrank_lat, finrank_loc]

end Local

section Maximal

/-- $(c\,Q)$ with coefficients mapped along $f$ is $f(c)$ times $Q$ with coefficients mapped along $f$. -/
theorem quadForm_map_smul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : QuadForm R n) :
    (c • Q).map f = f c • Q.map f := by
  ext i j
  simp [QuadForm.map]

/-- The quadratic map of $c\,Q$ is $c$ times the quadratic map of $Q$. -/
theorem toQuadraticForm_smul {R : Type*} [CommRing R] (c : R) (Q : QuadForm R n) :
    (c • Q).toQuadraticForm = c • Q.toQuadraticForm := by
  ext x
  show _ = c • Q.toQuadraticForm x
  rw [smul_eq_mul, QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply]
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_assoc]

/-- $a\,(b\,Q) = (ab)\,Q$ for scalars $a, b$ and a form $Q$. -/
theorem quadForm_smul_smul {R : Type*} [CommRing R] (a b : R) (Q : QuadForm R n) :
    a • b • Q = (a * b) • Q := by
  ext i j
  simp [mul_assoc]


/-- **Clearing denominators of a form:** for every form $Q$ over $F$ there are $c \in \mathcal O_F$, $c \ne 0$, and a
form $Q_1$ over $\mathcal O_F$ whose image in $F$ is $c\,Q$. -/
theorem exists_integral_smul (Q : QuadForm F n) :
    ∃ (c : 𝓞 F) (Q₁ : QuadForm (𝓞 F) n), c ≠ 0 ∧ Q₁.map (algebraMap (𝓞 F) F) = algebraMap (𝓞 F) F c • Q := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun p : Fin n × Fin n => Q.coeff p.1 p.2)
  have hb' : ∀ p : Fin n × Fin n, ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = b • Q.coeff p.1 p.2 := fun p => hb p
  choose r hr using hb'
  refine ⟨b, QuadForm.ofUpper (fun i j => r (i, j)), nonZeroDivisors.ne_zero b.2, ?_⟩
  ext i j
  simp only [QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, QuadForm.smul_coeff,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [hr, Submonoid.smul_def, Algebra.smul_def]
  · rw [map_zero, Q.upper (show id j < id i from not_le.mp h), mul_zero]

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- **The completions of a maximal lattice are maximal** (O'Meara 1963, §82K, p. 239; used in §91A): if the lattice
$L$ on $F^n$ is $\mathfrak a$-maximal for a non-zero fractional ideal $\mathfrak a$ (hypothesis `hL : IsMaximalLat Q L`)
and $Q$ is nondegenerate (hypothesis `hQ`), then at every finite spot $\mathfrak p$ (`v`) the completion $L_\mathfrak p$
is maximal on $V_\mathfrak p$ for the local form $Q_\mathfrak p$: it is $\mathfrak b$-maximal for some
$\mathfrak o_\mathfrak p$-submodule $\mathfrak b$ of $F_\mathfrak p$.

*Proof.* Scale $Q$ and $\mathfrak a$ by a non-zero $\alpha \in \mathcal O_F$ so that $\alpha Q$ has coefficients in
$\mathcal O_F$ and $\alpha\mathfrak a$ is an integral ideal $I$ (`OMeara.IsMaximal.smul_form`); then
`Hanke2005.isMaximal_loc` gives that $L_\mathfrak p$ is $\mathfrak p^{\operatorname{ord}_\mathfrak p I}$-maximal for
$\alpha Q_\mathfrak p$, and scaling back by $\alpha^{-1}$ gives maximality for $Q_\mathfrak p$. -/
@[kb "omeara1963" "§82K, p. 239 (L a-maximal ⟹ L_p maximal, at the completion); §91A"]
theorem isMaximal_loc_of_isMaximalLat (hQ : Q.Nondegenerate) {L : Lat F n} (hL : IsMaximalLat Q L) :
    ∃ a : Submodule 𝔬 Fv, OMeara.IsMaximal Qv a (loc v L.1) := by
  classical
  obtain ⟨a, ha0, hLa⟩ := hL
  obtain ⟨c, Q₁, hc0, hQ₁⟩ := exists_integral_smul Q
  obtain ⟨d, hdS, hd⟩ := a.isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdS
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective (𝓞 F) F
  set φ := algebraMap (𝓞 F) F with hφ
  set Q₀ : QuadForm (𝓞 F) n := d • Q₁ with hQ₀def
  set α : F := φ (c * d) with hαdef
  have hα0 : α ≠ 0 := by
    rw [hαdef, ne_eq, map_eq_zero_iff φ hinj]; exact mul_ne_zero hc0 hd0
  have hQ₀ : Q₀.map φ = α • Q := by
    rw [hQ₀def, quadForm_map_smul, hQ₁, quadForm_smul_smul, hαdef, map_mul, mul_comm]
  have h1 : OMeara.IsMaximal (α • Q.toQuadraticForm) (span (𝓞 F) {α} * (a : Submodule (𝓞 F) F)) L.1 :=
    hLa.smul_form _ hα0
  have hmemI : ∀ z, z ∈ span (𝓞 F) {α} * (a : Submodule (𝓞 F) F) → ∃ r, φ r = z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_span_singleton_mul.1 hz
    obtain ⟨s, hs⟩ : ∃ s, φ s = d • t := hd t ht
    refine ⟨c * s, ?_⟩
    rw [map_mul, hs, Algebra.smul_def, ← mul_assoc, ← map_mul]
  let I : Ideal (𝓞 F) := (span (𝓞 F) {α} * (a : Submodule (𝓞 F) F)).comap (Algebra.linearMap (𝓞 F) F)
  have hIspan : span (𝓞 F) (φ '' (I : Set (𝓞 F))) = span (𝓞 F) {α} * (a : Submodule (𝓞 F) F) := by
    ext z
    rw [Hanke2005.mem_idealSpan_iff]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr
    · intro hz
      obtain ⟨r, rfl⟩ := hmemI z hz
      exact ⟨r, hz, rfl⟩
  have hI0 : I ≠ ⊥ := by
    have ha' : (a : Submodule (𝓞 F) F) ≠ ⊥ := by
      rwa [ne_eq, FractionalIdeal.coeToSubmodule_eq_bot]
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha'
    have hz : α * t ∈ span (𝓞 F) {α} * (a : Submodule (𝓞 F) F) :=
      Submodule.mem_span_singleton_mul.2 ⟨t, ht, rfl⟩
    obtain ⟨r, hr⟩ := hmemI _ hz
    intro hbot
    have hrI : r ∈ I := by
      simp only [I, Submodule.mem_comap, Algebra.linearMap_apply]
      rw [hr]; exact hz
    rw [hbot, Submodule.mem_bot] at hrI
    rw [hrI, map_zero] at hr
    exact mul_ne_zero hα0 ht0 hr.symm
  have hQ₀nd : Q₀.Nondegenerate := by
    intro h0
    have h : (Q₀.map φ).hessian.det = 0 := by
      rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hQ₀, ClassFin.hessian_smul, Matrix.det_smul] at h
    exact mul_ne_zero (pow_ne_zero _ hα0) hQ h
  have hL' := Hanke2005.isMaximal_loc v Q₀ hQ₀nd I hI0 L (by
    rw [← hφ, hQ₀, toQuadraticForm_smul, hIspan]
    exact h1)
  have hψα : algebraMap F Fv α ≠ 0 := (map_ne_zero _).2 hα0
  have hqv : Hanke2005.qv v Q₀ = algebraMap F Fv α • Qv := by
    rw [Hanke2005.qv, hQ₀, quadForm_map_smul, toQuadraticForm_smul]
  have h2 : OMeara.IsMaximal (algebraMap F Fv α • Qv) (Hanke2005.pPow v (Hanke2005.ordIdeal v I))
      (loc v L.1) := by
    have h := hL'
    rw [hqv] at h
    exact h
  have h3 := h2.smul_form _ (inv_ne_zero hψα)
  rw [smul_smul, inv_mul_cancel₀ hψα, one_smul] at h3
  exact ⟨_, h3⟩

end Maximal

end QuadFormsKB.Lattices
