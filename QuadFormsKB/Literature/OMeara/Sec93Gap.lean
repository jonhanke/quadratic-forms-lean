/-
# O'Meara §93A: the squares $\mathfrak o^2$, norm generators, and the norm group under scaling (93:1, 93:5–93:8)

**Setting** (as in `Sec93.lean`): $R$ a commutative ring (a discrete valuation ring where needed) with an algebra map
to a field $F$ in which $2$ is invertible, a quadratic space $(V, Q)$ over $F$, O'Meara's bilinear form
$B$ = `bil Q` ($B(x, x) = Q(x)$), lattices = `Submodule R V`. The norm group $\mathfrak gL$ (`normGroup`), the largest
fractional ideal $\mathfrak mL$ in it (`normGroupIdeal`), the weight $\mathfrak wL$ (`weight`) and norm generators
(`IsNormGenerator`) are those of `Sec93.lean`. O'Meara's dyadic hypothesis is never needed below.

*Scaling.* O'Meara's lattice $\alpha L$ ($\alpha \in F^\times$) is `(R ∙ α) • L` (the product of the fractional ideal
$\alpha\mathfrak o$ with $L$, as in `Sec81.lean`); the scaled space $V^\alpha$ is the same $V$ with the form
$\alpha Q$ (`α • Q`), and $L^\alpha$ is $L$ regarded as a lattice in $V^\alpha$.

**Proves** (O'Meara 1963, §93A, pp. 250–254)
* `sqSet` (**93:1**): the set $\mathfrak o^2 = \{\varepsilon^2 : \varepsilon \in \mathfrak o\}$, as a subset of $F$, and
  `mul_sq_mem_normGroup`: $\mathfrak gL$ is stable under multiplication by $\mathfrak o^2$ (p. 254);
* `exists_isNormGenerator_Q` (**93:5**, first part): an element $Q(x)$, $x \in L$, of largest value in $Q(L)$ is a norm
  generator;
* `isNormGenerator_of_sqEquivMod` (**93:6**, the "if" direction): if $a$ is a norm generator and
  $a \cong a' \bmod \mathfrak wL$, then $a'$ is a norm generator;
* `normGroup_smul_lattice`, `normGroupIdeal_smul_lattice`, `weight_smul_lattice`, `IsNormGenerator.smul_lattice`
  (**93:7**): $\mathfrak g(\alpha L) = \alpha^2\,\mathfrak gL$, $\mathfrak m(\alpha L) = \alpha^2\,\mathfrak mL$,
  $\mathfrak w(\alpha L) = \alpha^2\,\mathfrak wL$, and $\alpha^2 a$ is a norm generator of $\alpha L$;
* `normGroup_smul_form`, `normGroupIdeal_smul_form`, `weight_smul_form`, `IsNormGenerator.smul_form`,
  `normGroup_neg_form` (**93:8**): $\mathfrak g(L^\alpha) = \alpha\,\mathfrak gL$, $\mathfrak m(L^\alpha) =
  \alpha\,\mathfrak mL$, $\mathfrak w(L^\alpha) = \alpha\,\mathfrak wL$, $\alpha a$ is a norm generator of $L^\alpha$, and
  $\mathfrak g(L^{-1}) = \mathfrak gL$.

*Erratum (OCR or print).* In 93:7 the scanned text reads $\mathfrak m(\alpha L) = \alpha(\mathfrak mL)$ and "$\varepsilon a$
is a norm generator of $\alpha L$"; the correct statements (proved here) are $\mathfrak m(\alpha L) =
\alpha^2(\mathfrak mL)$ and "$\alpha^2a$ is a norm generator of $\alpha L$", consistent with $\mathfrak g(\alpha L) =
\alpha^2\,\mathfrak gL$ on the same line.
-/
import QuadFormsKB.Literature.OMeara.Sec93
import QuadFormsKB.Literature.OMeara.Sec82Scale

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Squares

variable (R : Type*) [CommRing R] (F : Type*) [Field F] [Algebra R F]

/-- **Notation 93:1** (O'Meara 1963, p. 251): $\mathfrak o^2 = \{\varepsilon^2 : \varepsilon \in \mathfrak o\}$, the set of
squares of elements of the ring of integers $\mathfrak o = R$, as a subset of $F$ (not the ideal product
$\mathfrak o\,\mathfrak o = \mathfrak o$). -/
@[kb "omeara1963" "§93, 93:1, p. 251"]
def sqSet : Set F := {z | ∃ ε : R, z = algebraMap R F ε ^ 2}

end Squares

section Basic

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [Invertible (2 : F)] in
theorem span_singleton_mul_span_singleton' (a b : F) : (R ∙ a) * (R ∙ b) = R ∙ (a * b) := by
  rw [span_mul_span, Set.singleton_mul_singleton]

omit [Invertible (2 : F)] in
theorem span_singleton_sq' (a : F) : (R ∙ a) ^ 2 = R ∙ (a ^ 2) := by
  rw [pow_two, span_singleton_mul_span_singleton', pow_two]

/-- **$\mathfrak gL$ is stable under $\mathfrak o^2$** (O'Meara 1963, §93A, p. 254: "$\mathfrak gL$ stands multiplication
by elements of $\mathfrak o^2$"): if $z \in \mathfrak gL$ and $s \in \mathfrak o^2$ (`sqSet`) then $sz \in \mathfrak gL$. -/
@[kb "omeara1963" "§93A, p. 254 (gL is stable under multiplication by o²)"]
theorem mul_sq_mem_normGroup {L : Submodule R V} {z s : F} (hz : z ∈ normGroup Q L) (hs : s ∈ sqSet R F) :
    s * z ∈ normGroup Q L := by
  obtain ⟨x, hx, c, hc, rfl⟩ := hz
  obtain ⟨ε, rfl⟩ := hs
  refine ⟨ε • x, L.smul_mem ε hx, algebraMap R F ε ^ 2 * c, ?_, ?_⟩
  · have : algebraMap R F ε ^ 2 * c = (ε ^ 2) • c := by
      rw [Algebra.smul_def, map_pow]
    rw [this]; exact (scale Q L).smul_mem _ hc
  · rw [Q_rsmul]; ring

/-- **Example 93:6, "if" direction** (O'Meara 1963, p. 254): if $a$ is a norm generator of $L$ and
$a \cong a' \bmod \mathfrak wL$ (i.e. $a/a'$ is a unit and $a \equiv a'\varepsilon^2 \bmod \mathfrak wL$ for a unit
$\varepsilon$, `SqEquivMod`), then $a'$ is a norm generator of $L$. -/
@[kb "omeara1963" "§93A, 93:6, p. 254 (if a ≅ a' mod wL then a' is a norm generator)"]
theorem isNormGenerator_of_sqEquivMod [IsLocalRing R] {L : Submodule R V} {a a' : F}
    (ha : IsNormGenerator Q L a) (h : SqEquivMod (weight Q L) a a') : IsNormGenerator Q L a' := by
  obtain ⟨⟨u, hu, hau⟩, ε, hε, hw⟩ := h
  obtain ⟨hag, han⟩ := ha
  have hwg : a - a' * algebraMap R F ε ^ 2 ∈ normGroup Q L :=
    normGroupIdeal_subset Q L ((weight_bounds Q L).2.1 hw)
  have h1 : a' * algebraMap R F ε ^ 2 ∈ normGroup Q L := by
    have := sub_mem hag hwg
    rwa [sub_sub_cancel] at this
  obtain ⟨εi, hεi⟩ := hε.exists_left_inv
  have h2 := mul_sq_mem_normGroup Q h1 ⟨εi, rfl⟩
  have hε1 : algebraMap R F εi * algebraMap R F ε = 1 := by rw [← map_mul, hεi, map_one]
  have : algebraMap R F εi ^ 2 * (a' * algebraMap R F ε ^ 2) = a' := by
    calc _ = a' * (algebraMap R F εi * algebraMap R F ε) ^ 2 := by ring
      _ = a' := by rw [hε1]; ring
  refine ⟨this ▸ h2, ?_⟩
  rw [← han, hau, ← Algebra.smul_def]
  exact (Submodule.span_singleton_smul_eq hu a').symm

end Basic

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Example 93:5, norm generators** (O'Meara 1963, p. 254): "to find a norm generator simply take any element $a$
of largest value in $Q(L)$": for a lattice $L$ (finitely generated) there is $x \in L$ with $Q(x)\mathfrak o =
\mathfrak nL$, and every such $Q(x)$ is a norm generator of $L$. -/
@[kb "omeara1963" "§93A, 93:5, p. 254 (a norm generator from Q(L))"]
theorem exists_isNormGenerator_Q {L : Submodule R V} (hL : L.FG) :
    ∃ x ∈ L, IsNormGenerator Q L (Q x) := by
  obtain ⟨x, hx, h⟩ := exists_normIdeal_eq Q hL
  exact ⟨x, hx, Q_mem_normGroup Q hx, h.symm⟩

end DVR

section ScaleLattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
/-- The vectors of $\alpha L$ = `(R ∙ α) • L` are the $\alpha x$, $x \in L$. -/
theorem mem_span_singleton_smul_iff {α : F} {L : Submodule R V} {v : V} :
    v ∈ (R ∙ α) • L ↔ ∃ x ∈ L, α • x = v := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on (p := fun v => ∃ x ∈ L, α • x = v) hv ?_ ?_
    · intro β hβ l hl
      obtain ⟨c, rfl⟩ := mem_span_singleton.mp hβ
      refine ⟨c • l, L.smul_mem c hl, ?_⟩
      rw [smul_comm, smul_assoc]
    · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, L.add_mem hx hy, smul_add _ _ _⟩
  · rintro ⟨x, hx, rfl⟩
    exact smul_mem_smul (mem_span_singleton_self α) hx

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem mem_span_singleton_mul_iff' {α z : F} {S : Submodule R F} :
    z ∈ (R ∙ α) * S ↔ ∃ c ∈ S, z = α * c := by
  rw [Submodule.mem_span_singleton_mul]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

theorem scale_span_singleton_smul (α : F) (L : Submodule R V) :
    scale Q ((R ∙ α) • L) = (R ∙ (α ^ 2)) * scale Q L := by
  rw [scale_smul, span_singleton_sq']

/-- **Example 93:7, the norm group** (O'Meara 1963, p. 254): $\mathfrak g(\alpha L) = \alpha^2(\mathfrak gL)$ for a
scalar $\alpha$, where $\alpha L$ = `(R ∙ α) • L`. -/
@[kb "omeara1963" "§93A, 93:7, p. 254 (g(αL) = α²(gL))"]
theorem normGroup_smul_lattice (α : F) (L : Submodule R V) :
    normGroup Q ((R ∙ α) • L) = (normGroup Q L).map (AddMonoidHom.mulLeft (α ^ 2)) := by
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨y, hy, c', hc', rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_span_singleton_smul_iff.mp hy
    rw [scale_span_singleton_smul, mem_span_singleton_mul_iff'] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    exact ⟨Q x + 2 * c, ⟨x, hx, c, hc, rfl⟩, by rw [Q_smul]; ring⟩
  · rintro ⟨_, ⟨x, hx, c, hc, rfl⟩, rfl⟩
    refine ⟨α • x, mem_span_singleton_smul_iff.mpr ⟨x, hx, rfl⟩, α ^ 2 * c, ?_, ?_⟩
    · rw [scale_span_singleton_smul, mem_span_singleton_mul_iff']; exact ⟨c, hc, rfl⟩
    · rw [Q_smul]; ring

theorem mem_normGroup_smul_lattice {α : F} (hα : α ≠ 0) {L : Submodule R V} {z : F} :
    z ∈ normGroup Q ((R ∙ α) • L) ↔ z / α ^ 2 ∈ normGroup Q L := by
  rw [normGroup_smul_lattice]
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [mul_div_cancel_left₀ _ (pow_ne_zero 2 hα)]
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ (pow_ne_zero 2 hα)⟩

/-- **Example 93:7, $\mathfrak m$** (O'Meara 1963, p. 254): $\mathfrak m(\alpha L) = \alpha^2(\mathfrak mL)$ for
$\alpha \ne 0$. -/
@[kb "omeara1963" "§93A, 93:7, p. 254 (m(αL) = α²(mL))"]
theorem normGroupIdeal_smul_lattice {α : F} (hα : α ≠ 0) (L : Submodule R V) :
    normGroupIdeal Q ((R ∙ α) • L) = (R ∙ (α ^ 2)) * normGroupIdeal Q L := by
  ext z
  rw [mem_span_singleton_mul_iff']
  constructor
  · intro hz
    refine ⟨z / α ^ 2, fun r => ?_, by field_simp⟩
    have := (mem_normGroup_smul_lattice Q hα).mp (hz r)
    rwa [smul_div_assoc] at this
  · rintro ⟨c, hc, rfl⟩ r
    rw [mem_normGroup_smul_lattice Q hα]
    have h2 : r • (α ^ 2 * c) / α ^ 2 = r • c := by
      rw [Algebra.smul_def, Algebra.smul_def]; field_simp
    rw [h2]
    exact hc r

/-- **Example 93:7, the weight** (O'Meara 1963, p. 254): $\mathfrak w(\alpha L) = \alpha^2(\mathfrak wL)$ for
$\alpha \ne 0$. -/
@[kb "omeara1963" "§93A, 93:7, p. 254 (w(αL) = α²(wL))"]
theorem weight_smul_lattice {α : F} (hα : α ≠ 0) (L : Submodule R V) :
    weight Q ((R ∙ α) • L) = (R ∙ (α ^ 2)) * weight Q L := by
  rw [weight, weight, normGroupIdeal_smul_lattice Q hα, scale_span_singleton_smul, mul_add,
    mul_left_comm, mul_smul_comm]

/-- **Example 93:7, norm generators** (O'Meara 1963, p. 254): if $a$ is a norm generator of the lattice $L$ then
$\alpha^2a$ is a norm generator of $\alpha L$. -/
@[kb "omeara1963" "§93A, 93:7, p. 254 (α²a is a norm generator of αL)"]
theorem IsNormGenerator.smul_lattice {L : Submodule R V} (hL : L.FG) {a : F} (ha : IsNormGenerator Q L a)
    (α : F) : IsNormGenerator Q ((R ∙ α) • L) (α ^ 2 * a) := by
  refine ⟨?_, ?_⟩
  · rw [normGroup_smul_lattice]; exact ⟨a, ha.1, rfl⟩
  · rw [normIdeal_smul Q _ hL, ← ha.2, span_singleton_sq',
      span_singleton_mul_span_singleton']

end ScaleLattice

section ScaleForm

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

theorem bil_smul_form (c : F) (x y : V) : bil (c • Q) x y = c * bil Q x y := by
  simp [bil, QuadraticMap.associated_apply, smul_eq_mul]

/-- The scale of $L^\alpha$: $\mathfrak s(L^\alpha) = \alpha\,\mathfrak sL$ (O'Meara 1963, §82J, p. 238). -/
theorem scale_smul_form (α : F) (L : Submodule R V) : scale (α • Q) L = (R ∙ α) * scale Q L := by
  rw [scale, scale, Submodule.span_mul_span]
  congr 1
  ext z
  simp only [Set.mem_image2, Set.mem_mul, Set.mem_singleton_iff, bil_smul_form]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨α, rfl, _, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, rfl, _, ⟨x, hx, y, hy, rfl⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩

/-- The norm of $L^\alpha$: $\mathfrak n(L^\alpha) = \alpha\,\mathfrak nL$ (O'Meara 1963, §82J, p. 238). -/
theorem normIdeal_smul_form (α : F) (L : Submodule R V) : normIdeal (α • Q) L = (R ∙ α) * normIdeal Q L := by
  rw [normIdeal, normIdeal, Submodule.span_mul_span]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_mul, Set.mem_singleton_iff, QuadraticMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨α, rfl, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, rfl, _, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

/-- **Example 93:8, the norm group** (O'Meara 1963, p. 254): scaling the quadratic space by $\alpha$ gives
$\mathfrak g(L^\alpha) = \alpha(\mathfrak gL)$, where $L^\alpha$ is $L$ in the space $(V, \alpha Q)$. -/
@[kb "omeara1963" "§93A, 93:8, p. 254 (g(L^α) = α(gL))"]
theorem normGroup_smul_form (α : F) (L : Submodule R V) :
    normGroup (α • Q) L = (normGroup Q L).map (AddMonoidHom.mulLeft α) := by
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨x, hx, c', hc', rfl⟩
    rw [scale_smul_form] at hc'
    obtain ⟨c, hc, h⟩ := Submodule.mem_span_singleton_mul.mp hc'
    subst h
    exact ⟨Q x + 2 * c, ⟨x, hx, c, hc, rfl⟩, by simp [smul_eq_mul]; ring⟩
  · rintro ⟨_, ⟨x, hx, c, hc, rfl⟩, rfl⟩
    refine ⟨x, hx, α * c, ?_, by simp [smul_eq_mul]; ring⟩
    rw [scale_smul_form]; exact Submodule.mem_span_singleton_mul.mpr ⟨c, hc, rfl⟩

theorem mem_normGroup_smul_form {α : F} (hα : α ≠ 0) {L : Submodule R V} {z : F} :
    z ∈ normGroup (α • Q) L ↔ z / α ∈ normGroup Q L := by
  rw [normGroup_smul_form]
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [mul_div_cancel_left₀ _ hα]
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ hα⟩

/-- **Example 93:8, $\mathfrak m$** (O'Meara 1963, p. 254): $\mathfrak m(L^\alpha) = \alpha(\mathfrak mL)$ for
$\alpha \ne 0$. -/
@[kb "omeara1963" "§93A, 93:8, p. 254 (m(L^α) = α(mL))"]
theorem normGroupIdeal_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) :
    normGroupIdeal (α • Q) L = (R ∙ α) * normGroupIdeal Q L := by
  ext z
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · intro hz
    refine ⟨z / α, fun r => ?_, by field_simp⟩
    have := (mem_normGroup_smul_form Q hα).mp (hz r)
    rwa [smul_div_assoc] at this
  · rintro ⟨c, hc, rfl⟩ r
    rw [mem_normGroup_smul_form Q hα]
    have h2 : r • (α * c) / α = r • c := by
      rw [Algebra.smul_def, Algebra.smul_def]; field_simp
    rw [h2]
    exact hc r

/-- **Example 93:8, the weight** (O'Meara 1963, p. 254): $\mathfrak w(L^\alpha) = \alpha(\mathfrak wL)$ for
$\alpha \ne 0$. -/
@[kb "omeara1963" "§93A, 93:8, p. 254 (w(L^α) = α(wL))"]
theorem weight_smul_form [IsLocalRing R] {α : F} (hα : α ≠ 0) (L : Submodule R V) :
    weight (α • Q) L = (R ∙ α) * weight Q L := by
  rw [weight, weight, normGroupIdeal_smul_form Q hα, scale_smul_form, mul_add, mul_left_comm,
    mul_smul_comm]

/-- **Example 93:8, norm generators** (O'Meara 1963, p. 254): if $a$ is a norm generator of $L$ then $\alpha a$ is a
norm generator of $L^\alpha$. -/
@[kb "omeara1963" "§93A, 93:8, p. 254 (αa is a norm generator of L^α)"]
theorem IsNormGenerator.smul_form {L : Submodule R V} {a : F} (ha : IsNormGenerator Q L a) (α : F) :
    IsNormGenerator (α • Q) L (α * a) := by
  refine ⟨?_, ?_⟩
  · rw [normGroup_smul_form]; exact ⟨a, ha.1, rfl⟩
  · rw [normIdeal_smul_form, ← ha.2, span_singleton_mul_span_singleton']

/-- **Example 93:8, $\alpha = -1$** (O'Meara 1963, p. 254): $\mathfrak g(L^{-1}) = \mathfrak gL$. -/
@[kb "omeara1963" "§93A, 93:8, p. 254 (gL^{-1} = gL)"]
theorem normGroup_neg_form (L : Submodule R V) : normGroup ((-1 : F) • Q) L = normGroup Q L := by
  rw [normGroup_smul_form]
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using neg_mem hw
  · intro h; exact ⟨-z, neg_mem h, by ring⟩

end ScaleForm

end QuadFormsKB.OMeara
