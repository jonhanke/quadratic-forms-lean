/-
# O'Meara §43B: the Cartan–Dieudonné theorem for abstract quadratic spaces (43:3)

**Setting** (Chapter V conventions): $F$ a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`), $(V, Q)$ a
finite-dimensional quadratic space over $F$, O'Meara's bilinear form $B$ = `bil Q` ($B(x,x) = Q(x)$); *regular* means
`(QuadraticMap.associated Q).Nondegenerate`. $\tau_u$ = `symmetry Q u hu` for $Q(u) \ne 0$.

**Proves**
* `exists_symmetry_prod_eq_length_le` (**43:3**, the sharp form): every isometry of a regular $n$-ary space is a
  product of at most $n$ symmetries;
* `exists_symmetry_prod_eq` (the weaker bound $2n$, a corollary of the sharp bound; the "two or three line proof"
  of O'Meara's footnote gives $2n-1$);
* `exists_symmetry_prod_eq_length_le_two` (the fact used in §55, 55:5, p. 140): for $\dim V \le 3$ every
  rotation is a product of at most two symmetries.

Names `cd_*` are internal helpers. The identity is the empty product.

*Proof of 43:3* (O'Meara, pp. 102–103). Step 1 (`cd_star_even_det`): if $\sigma$ satisfies $(*)$ "$x$ anisotropic
implies $\sigma x - x$ isotropic (non-zero, $Q = 0$)", then $\dim V$ is even and $\det\sigma = 1$. (Here, as in O'Meara,
"isotropic" means non-zero with $Q = 0$; the case $\sigma = 1$ shows this is needed.) We argue with $P = \sigma - 1$:
$Q(Py) = 0$ for all $y$ (using a vector $z \perp y$ with $Q(z) \ne 0$, which exists as $\dim V \ge 3$), hence
$B(Px, Py) = 0$ and $P$ is skew for $B$, so $P^2 = 0$ by regularity; the fixed space $K = \ker P$ is totally isotropic by
$(*)$, so $K \subseteq K^\perp$, which with $\operatorname{im} P \subseteq K$ forces $\dim V = 2\dim K$; finally
$\det\sigma = 1$ from the flag $K \subseteq V$ (replacing O'Meara's appeal to 43:1 on a hyperbolic space and a
maximal totally isotropic subspace). Step 2: induction on $n$ (types of smaller dimension: $x^\perp$), as in the
book.

*Relation to `Lattices.exists_symmProd_eq`* (coordinates, number-field base, bound $2n$): the present file is
the abstract (coordinate-free, any field with $2 \ne 0$) version with the sharp bound; the two proofs are different.
-/
import QuadFormsKB.Literature.OMeara.Sec92Spinor

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

universe u v

section CDBasic

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

theorem cd_two_ne : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero

theorem cd_bil_neg_right (x y : V) : bil Q x (-y) = -bil Q x y := by simp [bil]

/-- Regularity in elementary form: the radical is zero. -/
def cd_Reg : Prop := ∀ x : V, (∀ y, bil Q x y = 0) → x = 0

theorem cd_reg_of_nondeg (h : (QuadraticMap.associated Q).Nondegenerate) : cd_Reg Q := h.1

theorem cd_nondeg_of_reg (h : cd_Reg Q) : (QuadraticMap.associated Q).Nondegenerate :=
  ⟨h, fun y hy => h y fun x => by rw [bil_comm]; exact hy x⟩

theorem cd_bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (a b : V) : bil Q (σ a) (σ b) = bil Q a b := by
  have h1 := Q_add Q (σ a) (σ b)
  have h2 := Q_add Q a b
  have h3 : Q (σ a + σ b) = Q (a + b) := by rw [← map_add]; exact hσ _
  have ha := hσ a
  have hb := hσ b
  apply mul_left_cancel₀ (cd_two_ne (F := F))
  linear_combination (-1 : F) * h1 + h2 + h3 - ha - hb

/-- If $Q$ vanishes on a submodule, so does $B$. -/
theorem cd_bil_eq_zero_of_Q {a b : V} (ha : Q a = 0) (hb : Q b = 0) (hab : Q (a + b) = 0) :
    bil Q a b = 0 := by
  have h := Q_add Q a b
  rw [ha, hb, hab] at h
  have : (2 : F) * bil Q a b = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left cd_two_ne

theorem cd_exists_aniso (hV : cd_Reg Q) [Nontrivial V] : ∃ x : V, Q x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hV x fun y => cd_bil_eq_zero_of_Q Q (h x) (h y) (h _))

end CDBasic

section CDStar

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- For a nonzero $y$ in a regular space of dimension $\ge 3$ there is an anisotropic $z \perp y$. -/
theorem cd_exists_perp_aniso (hV : cd_Reg Q) (h3 : 3 ≤ finrank F V) {y : V} (hy : y ≠ 0) :
    ∃ z, Q z ≠ 0 ∧ bil Q y z = 0 := by
  by_contra hno
  push Not at hno
  have hnd := cd_nondeg_of_reg Q hV
  have hrefl : (QuadraticMap.associated Q).IsRefl := fun a b h => (bil_comm Q b a).trans h
  set B : LinearMap.BilinForm F V := QuadraticMap.associated Q
  set T := LinearMap.BilinForm.orthogonal B (F ∙ y) with hT
  have hmemT : ∀ z, z ∈ T ↔ bil Q y z = 0 := fun z => by
    rw [hT, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h; exact h y (mem_span_singleton_self y)
    · intro h w hw
      obtain ⟨c, rfl⟩ := mem_span_singleton.mp hw
      show bil Q (c • y) z = 0
      rw [bil_smul_left, h, mul_zero]
  have hiso : ∀ z ∈ T, Q z = 0 := fun z hz => by
    by_contra h
    exact (hno z h) ((hmemT z).mp hz)
  have hTT : T ≤ LinearMap.BilinForm.orthogonal B T := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    exact cd_bil_eq_zero_of_Q Q (hiso b hb) (hiso a ha) (hiso _ (T.add_mem hb ha))
  have h2 : LinearMap.BilinForm.orthogonal B T = F ∙ y := LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl _
  have h4 : finrank F T ≤ 1 := by
    have := Submodule.finrank_mono (hTT.trans h2.le)
    rwa [finrank_span_singleton hy] at this
  have h5 : finrank F T = finrank F V - finrank F (F ∙ y) :=
    LinearMap.BilinForm.finrank_orthogonal hnd (F ∙ y)
  rw [finrank_span_singleton hy] at h5
  omega

/-- **Step 1 of 43:3** (O'Meara p. 102): if $\sigma \in O(V)$ satisfies $(*)$ — every anisotropic $x$ has
$\sigma x \ne x$ and $Q(\sigma x - x) = 0$ — then $\dim V$ is even and $\sigma$ is a rotation. -/
theorem cd_star_even_det (hV : cd_Reg Q) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q)
    (hs : ∀ x, Q x ≠ 0 → σ x ≠ x ∧ Q (σ x - x) = 0) :
    Even (finrank F V) ∧ LinearEquiv.det σ = 1 := by
  obtain ⟨P, hP⟩ : ∃ P : V →ₗ[F] V, ∀ x, P x = σ x - x := ⟨(σ : V →ₗ[F] V) - LinearMap.id, fun x => rfl⟩
  have hσP : ∀ x, σ x = x + P x := fun x => by rw [hP]; abel
  by_cases hsub : Subsingleton V
  · refine ⟨by simp [finrank_zero_of_subsingleton], ?_⟩
    apply Units.ext
    rw [LinearEquiv.coe_det]
    simp [LinearMap.det_eq_one_of_subsingleton]
  have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
  -- dimension at least 3
  obtain ⟨x0, hx0⟩ := cd_exists_aniso Q hV
  obtain ⟨hne0, hQ0⟩ := hs x0 hx0
  have hPx0 : P x0 ≠ 0 := fun h => hne0 (by rw [hσP, h, add_zero])
  have hQP0 : Q (P x0) = 0 := by rw [hP]; exact hQ0
  have hB0 : bil Q x0 (P x0) = 0 := by
    have h1 := Q_add Q x0 (P x0)
    rw [← hσP x0, hσ x0, hQP0] at h1
    have h2 : (2 : F) * bil Q x0 (P x0) = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left cd_two_ne
  have h3 : 3 ≤ finrank F V := by
    by_contra hlt
    push Not at hlt
    have hli : LinearIndependent F ![x0, P x0] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e : bil Q (s • x0 + t • P x0) x0 = 0 := by rw [hst]; simp [bil]
      rw [bil_add_left, bil_smul_left, bil_smul_left, bil_self, bil_comm Q (P x0) x0, hB0] at e
      have hs0 : s = 0 := by
        have : s * Q x0 = 0 := by simpa using e
        exact (mul_eq_zero.mp this).resolve_right hx0
      subst hs0
      refine ⟨rfl, ?_⟩
      rw [zero_smul, zero_add] at hst
      exact (smul_eq_zero.mp hst).resolve_right hPx0
    have hW := finrank_span_eq_card hli
    simp only [Fintype.card_fin] at hW
    have hWtop : span F (Set.range ![x0, P x0]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le (span F (Set.range ![x0, P x0]))
      omega
    apply hPx0
    apply hV
    intro v
    have hv : v ∈ span F (Set.range ![x0, P x0]) := by rw [hWtop]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hv
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [bil_add_right, bil_smul_right, bil_smul_right, bil_comm Q (P x0) x0, hB0, bil_self, hQP0]
    ring
  have hQP : ∀ y, Q (P y) = 0 := by
    intro y
    by_cases hy : Q y ≠ 0
    · rw [hP]; exact (hs y hy).2
    push Not at hy
    by_cases hy0 : y = 0
    · subst hy0; simp
    obtain ⟨z, hz, hyz⟩ := cd_exists_perp_aniso Q hV h3 hy0
    have key : ∀ z', Q z' ≠ 0 → bil Q y z' = 0 → Q (P y) + 2 * bil Q (P y) (P z') = 0 := by
      intro z' hz' hyz'
      have hQy' : Q (y + z') ≠ 0 := by rw [Q_add, hy, hyz']; simpa using hz'
      have h1 := (hs _ hQy').2
      rw [← hP, map_add, Q_add] at h1
      have hz2 : Q (P z') = 0 := by rw [hP]; exact (hs z' hz').2
      rw [hz2] at h1
      linear_combination h1
    have e1 := key z hz hyz
    have e2 := key (-z) (by rw [QuadraticMap.map_neg]; exact hz) (by rw [cd_bil_neg_right, hyz, neg_zero])
    rw [map_neg, cd_bil_neg_right] at e2
    have : (2 : F) * Q (P y) = 0 := by linear_combination e1 + e2
    exact (mul_eq_zero.mp this).resolve_left cd_two_ne
  have hBP : ∀ a b, bil Q (P a) (P b) = 0 := fun a b =>
    cd_bil_eq_zero_of_Q Q (hQP a) (hQP b) (by rw [← map_add]; exact hQP _)
  have hskew : ∀ a b, bil Q (P a) b + bil Q a (P b) = 0 := by
    intro a b
    have h := cd_bil_orth Q hσ a b
    rw [hσP a, hσP b] at h
    simp only [bil_add_left, bil_add_right, hBP] at h
    linear_combination h
  have hPP : ∀ y, P (P y) = 0 := fun y => by
    apply hV
    intro x
    rw [bil_comm]
    have := hskew x (P y)
    rw [hBP] at this
    simpa using this
  have hnd := cd_nondeg_of_reg Q hV
  have hrefl : (QuadraticMap.associated Q).IsRefl := fun a b h => (bil_comm Q b a).trans h
  set K := LinearMap.ker P with hKdef
  have hK : ∀ y ∈ K, Q y = 0 := by
    intro y hy
    by_contra h
    apply (hs y h).1
    have : P y = 0 := hy
    rw [hP] at this
    exact sub_eq_zero.mp this
  have hKK : K ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) K := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    exact cd_bil_eq_zero_of_Q Q (hK b hb) (hK a ha) (hK _ (K.add_mem hb ha))
  have hrk : finrank F (LinearMap.range P) + finrank F K = finrank F V :=
    LinearMap.finrank_range_add_finrank_ker P
  have hrange : LinearMap.range P ≤ K := by
    rintro _ ⟨y, rfl⟩
    exact hPP y
  have hfr := Submodule.finrank_mono hrange
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd K
  have hle := Submodule.finrank_mono hKK
  refine ⟨⟨finrank F K, by omega⟩, ?_⟩
  -- the determinant
  have he : K ≤ K.comap (σ : V →ₗ[F] V) := fun y hy => by
    have : P y = 0 := hy
    rw [hP] at this
    show σ y ∈ K
    rw [sub_eq_zero.mp this]; exact hy
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearMap.det_eq_det_mul_det K (σ : V →ₗ[F] V) he]
  have h1 : (σ : V →ₗ[F] V).restrict he = LinearMap.id := by
    ext ⟨y, hy⟩
    have : P y = 0 := hy
    rw [hP] at this
    simp [sub_eq_zero.mp this]
  have h2 : K.mapQ K (σ : V →ₗ[F] V) he = LinearMap.id := by
    ext y
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
    rw [Submodule.Quotient.eq]
    show σ y - y ∈ K
    rw [← hP y]
    exact hPP y
  rw [h1, h2]
  simp

end CDStar

section CDProd

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- The product $\tau_{u_1}\cdots\tau_{u_r}$ of the symmetries of a list of anisotropic vectors. -/
def cd_prod (l : List {u : V // Q u ≠ 0}) : V ≃ₗ[F] V := (l.map fun u => symmetry Q u.1 u.2).prod

@[simp] theorem cd_prod_nil : cd_prod Q [] = 1 := rfl

theorem cd_prod_cons (a : {u : V // Q u ≠ 0}) (l : List {u : V // Q u ≠ 0}) :
    cd_prod Q (a :: l) = symmetry Q a.1 a.2 * cd_prod Q l := by simp [cd_prod]

theorem cd_det_prod [FiniteDimensional F V] (l : List {u : V // Q u ≠ 0}) :
    LinearEquiv.det (cd_prod Q l) = (-1 : Fˣ) ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => rw [cd_prod_cons, map_mul, ih, det_symmetry, List.length_cons, pow_succ']

theorem cd_neg_one_ne : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h' : (-1 : F) = 1 := congrArg Units.val h
  have h2F : (2 : F) = 0 := by linear_combination -h'
  exact cd_two_ne h2F

/-- The list form of the statement: `cd_prod` is the product in the statement of 43:3. -/
theorem cd_prod_eq_attach (l : List {u : V // Q u ≠ 0})
    (hl : ∀ u ∈ l.map Subtype.val, Q u ≠ 0) :
    (((l.map Subtype.val).attach).map fun u => symmetry Q u.1 (hl u.1 u.2)).prod = cd_prod Q l := by
  have h1 := List.pmap_eq_map_attach (p := fun u => Q u ≠ 0) (f := fun u h => symmetry Q u h)
    (l := l.map Subtype.val) hl
  rw [← h1, List.pmap_map]
  unfold cd_prod
  congr 1
  exact List.pmap_eq_map (p := fun a : {u : V // Q u ≠ 0} => Q a.1 ≠ 0)
    (f := fun a => symmetry Q a.1 a.2) (l := l) _

end CDProd

section CDFixed

variable (F : Type u) [Field F] [Invertible (2 : F)]

/-- **The induction claim of 43:3 for dimension $m$** (all spaces of dimension $m$ in universe `v`). -/
def cd_Claim (m : ℕ) : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    finrank F V = m → cd_Reg Q → ∀ σ ∈ orth Q,
      ∃ l : List {u : V // Q u ≠ 0}, l.length ≤ m ∧ σ = cd_prod Q l

variable {F}
variable {V : Type v} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- The hyperplane $x^\perp$ for $B$. -/
def cd_perp (x : V) : Submodule F V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (F ∙ x)

theorem cd_mem_perp (x v : V) : v ∈ cd_perp Q x ↔ bil Q x v = 0 := by
  rw [cd_perp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h; exact h x (mem_span_singleton_self x)
  · intro h w hw
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hw
    show bil Q (c • x) v = 0
    rw [bil_smul_left, h, mul_zero]

theorem cd_decomp_mem {x : V} (hx : Q x ≠ 0) (v : V) :
    v - (bil Q v x / Q x) • x ∈ cd_perp Q x := by
  rw [cd_mem_perp, bil_sub_right, bil_smul_right, bil_self, bil_comm Q x v, mul_comm,
    mul_div_cancel₀ _ hx, sub_self]

theorem cd_bil_comp (S : Submodule F V) (a b : S) :
    bil (Q.comp S.subtype) a b = bil Q a.1 b.1 := by
  apply mul_left_cancel₀ (cd_two_ne (F := F))
  have h1 := Q_add (Q.comp S.subtype) a b
  have h2 := Q_add Q a.1 b.1
  have e : (Q.comp S.subtype) (a + b) = Q (a.1 + b.1) := rfl
  have ea : (Q.comp S.subtype) a = Q a.1 := rfl
  have eb : (Q.comp S.subtype) b = Q b.1 := rfl
  rw [e, ea, eb] at h1
  linear_combination h2 - h1

theorem cd_reg_perp (hV : cd_Reg Q) {x : V} (hx : Q x ≠ 0) :
    cd_Reg (Q.comp (cd_perp Q x).subtype) := by
  intro u hu
  have hu0 : u.1 = 0 := by
    apply hV
    intro v
    have hw := cd_decomp_mem Q hx v
    have h1 : bil Q u.1 (v - (bil Q v x / Q x) • x) = 0 := by
      have := hu ⟨v - (bil Q v x / Q x) • x, hw⟩
      rwa [cd_bil_comp] at this
    have h2 : bil Q u.1 x = 0 := (bil_comm Q u.1 x).trans ((cd_mem_perp Q x u.1).mp u.2)
    have h3 : bil Q u.1 v = bil Q u.1 (v - (bil Q v x / Q x) • x) + (bil Q v x / Q x) * bil Q u.1 x := by
      rw [bil_sub_right, bil_smul_right]; ring
    rw [h3, h1, h2]; ring
  exact Subtype.ext hu0

theorem cd_exists_restrict {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {x : V} (hσx : σ x = x) :
    ∃ σU : cd_perp Q x ≃ₗ[F] cd_perp Q x, ∀ v, (σU v).1 = σ v.1 := by
  have h1 : ∀ v ∈ cd_perp Q x, σ v ∈ cd_perp Q x := fun v hv => by
    rw [cd_mem_perp] at hv ⊢
    calc bil Q x (σ v) = bil Q (σ x) (σ v) := by rw [hσx]
      _ = bil Q x v := cd_bil_orth Q hσ x v
      _ = 0 := hv
  have h2 : ∀ v ∈ cd_perp Q x, σ.symm v ∈ cd_perp Q x := fun v hv => by
    rw [cd_mem_perp] at hv ⊢
    have := cd_bil_orth Q hσ x (σ.symm v)
    rw [hσx, LinearEquiv.apply_symm_apply] at this
    rw [← this]; exact hv
  refine ⟨LinearEquiv.ofLinearMap ((σ : V →ₗ[F] V).restrict h1) ((σ.symm : V →ₗ[F] V).restrict h2) ?_ ?_,
    fun v => rfl⟩
  · ext ⟨v, hv⟩
    simp
  · ext ⟨v, hv⟩
    simp

theorem cd_lift {x : V}
    (l : List {u : cd_perp Q x // (Q.comp (cd_perp Q x).subtype) u ≠ 0}) :
    cd_prod Q (l.map fun u => (⟨u.1.1, u.2⟩ : {v : V // Q v ≠ 0})) x = x ∧
      ∀ w : cd_perp Q x, cd_prod Q (l.map fun u => (⟨u.1.1, u.2⟩ : {v : V // Q v ≠ 0})) w.1 =
        (cd_prod (Q.comp (cd_perp Q x).subtype) l w).1 := by
  induction l with
  | nil => exact ⟨by simp, fun w => by simp only [List.map_nil, cd_prod_nil]; rfl⟩
  | cons a t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · rw [List.map_cons, cd_prod_cons, LinearEquiv.mul_apply, ih1, symmetry_apply]
      have : bil Q x a.1.1 = 0 := (cd_mem_perp Q x _).mp a.1.2
      rw [this]; simp
    · intro w
      rw [List.map_cons, cd_prod_cons, LinearEquiv.mul_apply, ih2 w, cd_prod_cons,
        LinearEquiv.mul_apply, symmetry_apply, symmetry_apply]
      simp [cd_bil_comp]

theorem cd_fixed [FiniteDimensional F V] (n : ℕ) (IH : ∀ m < n, cd_Claim.{u, v} F m)
    (hn : finrank F V = n) (hV : cd_Reg Q) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) {x : V} (hx : Q x ≠ 0)
    (hσx : σ x = x) : ∃ l : List {u : V // Q u ≠ 0}, l.length + 1 ≤ n ∧ σ = cd_prod Q l := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; simp)
  have hdim : finrank F (cd_perp Q x) + 1 = n := by
    have h1 : finrank F (cd_perp Q x) = finrank F V - finrank F (F ∙ x) :=
      LinearMap.BilinForm.finrank_orthogonal (cd_nondeg_of_reg Q hV) (F ∙ x)
    have h2 := Submodule.finrank_le (F ∙ x)
    rw [finrank_span_singleton hx0] at h1 h2
    omega
  obtain ⟨σU, hσU⟩ := cd_exists_restrict Q hσ hσx
  have hσU' : σU ∈ orth (Q.comp (cd_perp Q x).subtype) := fun u => by
    show Q (σU u).1 = Q u.1
    rw [hσU]; exact hσ u.1
  obtain ⟨l, hl, hσl⟩ := IH (finrank F (cd_perp Q x)) (by omega) (cd_perp Q x)
    (Q.comp (cd_perp Q x).subtype) rfl (cd_reg_perp Q hV hx) σU hσU'
  obtain ⟨hl1, hl2⟩ := cd_lift Q l
  refine ⟨l.map fun u => (⟨u.1.1, u.2⟩ : {v : V // Q v ≠ 0}), by rw [List.length_map]; omega, ?_⟩
  ext v
  set c := bil Q v x / Q x with hc
  have hw := cd_decomp_mem Q hx v
  have hσw : σ (v - c • x) = cd_prod Q (l.map fun u => (⟨u.1.1, u.2⟩ : {v : V // Q v ≠ 0}))
      (v - c • x) := by
    rw [hl2 ⟨v - c • x, hw⟩, ← hσl]
    exact (hσU ⟨_, hw⟩).symm
  calc σ v = σ ((v - c • x) + c • x) := by rw [sub_add_cancel]
    _ = σ (v - c • x) + c • x := by rw [map_add, map_smul, hσx]
    _ = _ := by
      rw [hσw]
      conv_rhs => rw [← sub_add_cancel v (c • x), map_add, map_smul, hl1]

end CDFixed

section CDMain

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- **Step 2 of 43:3, the non-$(*)$ case**: an isometry violating $(*)$ is a product of at most $n$ symmetries
(given the theorem in smaller dimensions). -/
theorem cd_step (n : ℕ) (IH : ∀ m < n, cd_Claim.{u, v} F m) (hn : finrank F V = n) (hV : cd_Reg Q)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (hnot : ¬ ∀ x, Q x ≠ 0 → σ x ≠ x ∧ Q (σ x - x) = 0) :
    ∃ l : List {u : V // Q u ≠ 0}, l.length ≤ n ∧ σ = cd_prod Q l := by
  push Not at hnot
  obtain ⟨x, hx, hxs⟩ := hnot
  by_cases hfix : σ x = x
  · obtain ⟨l, hl, h⟩ := cd_fixed Q n IH hn hV hσ hx hfix
    exact ⟨l, by omega, h⟩
  · have hd : Q (σ x - x) ≠ 0 := hxs hfix
    set d := σ x - x with hdd
    have hsx : σ x = x + d := by rw [hdd]; abel
    have e : 2 * bil Q (σ x) d = Q d := by
      have h1 := Q_add Q x d
      rw [← hsx, hσ x] at h1
      rw [hsx, bil_add_left, bil_self]
      linear_combination (-1 : F) * h1
    have hρ : symmetry Q d hd * σ ∈ orth Q := (orth Q).mul_mem (symmetry_mem_orth Q hd) hσ
    have hρx : (symmetry Q d hd * σ) x = x := by
      rw [LinearEquiv.mul_apply, symmetry_apply, e, div_self hd, one_smul, hsx]
      abel
    obtain ⟨l, hl, h⟩ := cd_fixed Q n IH hn hV hρ hx hρx
    refine ⟨⟨d, hd⟩ :: l, by simp; omega, ?_⟩
    rw [cd_prod_cons, ← h]
    ext v
    simp [symmetry_symmetry]

/-- **43:3 for all dimensions** (induction on the dimension). -/
theorem cd_claim (n : ℕ) : cd_Claim.{u, v} F n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro V _ _ _ Q hn hV σ hσ
  by_cases hstar : ∀ x, Q x ≠ 0 → σ x ≠ x ∧ Q (σ x - x) = 0
  · by_cases hsub : Subsingleton V
    · refine ⟨[], by simp, ?_⟩
      ext v
      exact Subsingleton.elim _ _
    have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨hev, hdet⟩ := cd_star_even_det Q hV hσ hstar
    obtain ⟨x0, hx0⟩ := cd_exists_aniso Q hV
    have hρ : symmetry Q x0 hx0 * σ ∈ orth Q := (orth Q).mul_mem (symmetry_mem_orth Q hx0) hσ
    have hnot : ¬ ∀ x, Q x ≠ 0 → (symmetry Q x0 hx0 * σ) x ≠ x ∧
        Q ((symmetry Q x0 hx0 * σ) x - x) = 0 := by
      intro h
      have := (cd_star_even_det Q hV hρ h).2
      rw [map_mul, det_symmetry, hdet] at this
      exact cd_neg_one_ne (by simpa using this)
    obtain ⟨l, hl, h⟩ := cd_step Q n IH hn hV hρ hnot
    have hσe : σ = cd_prod Q (⟨x0, hx0⟩ :: l) := by
      rw [cd_prod_cons, ← h]
      ext v
      simp [symmetry_symmetry]
    refine ⟨⟨x0, hx0⟩ :: l, ?_, hσe⟩
    have hdl := cd_det_prod Q (⟨x0, hx0⟩ :: l)
    rw [← hσe, hdet] at hdl
    have hev' := (neg_one_pow_eq_one_iff_even cd_neg_one_ne).mp hdl.symm
    obtain ⟨a, ha⟩ := hev
    obtain ⟨b, hb⟩ := hev'
    simp only [List.length_cons] at hb hl ⊢
    omega
  · exact cd_step Q n IH hn hV hσ hstar

end CDMain

section CDFinal

variable {F : Type u} [Field F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- Conversion from a list of anisotropic vectors (as subtypes) to the list form of the statements. -/
theorem cd_repr {σ : V ≃ₗ[F] V} {l' : List {u : V // Q u ≠ 0}} (h : σ = cd_prod Q l') :
    ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length = l'.length := by
  have hl : ∀ u ∈ l'.map Subtype.val, Q u ≠ 0 := fun u hu => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.2
  exact ⟨l'.map Subtype.val, hl, by rw [cd_prod_eq_attach Q l' hl]; exact h, by simp⟩

theorem cd_list (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    ∃ l' : List {u : V // Q u ≠ 0}, l'.length ≤ finrank F V ∧ σ = cd_prod Q l' :=
  cd_claim.{u, v} (F := F) (finrank F V) V Q rfl (cd_reg_of_nondeg Q hQ) σ hσ

/-- **Theorem 43:3, the Cartan–Dieudonné theorem** (O'Meara 1963, p. 102): every isometry $\sigma$ of a regular
$n$-ary quadratic space onto itself is a product of at most $n$ symmetries $\tau_{x_1}\cdots\tau_{x_r}$,
$r \le n$, $Q(x_i) \ne 0$. (O'Meara's proof is by induction on $n$ using a lemma on isometries with the property
$(*)$; here the lemma is proved by a direct argument with $\sigma - 1$ instead of 43:1. The identity is the empty
product, $r = 0$.) -/
@[kb "omeara1963" "§43B, 43:3, p. 102"]
theorem exists_symmetry_prod_eq_length_le (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length ≤ finrank F V := by
  obtain ⟨l', hlen, h⟩ := cd_list Q hQ hσ
  obtain ⟨l, hl, hσ', hll⟩ := cd_repr Q h
  exact ⟨l, hl, hσ', by omega⟩

/-- **Cartan–Dieudonné, the weaker bound** (O'Meara 1963, 43:3, p. 102, with $2n$ in place of $n$): every
isometry of a regular quadratic space is a product of at most $2\dim V$ symmetries. This is a corollary of the sharp
bound `exists_symmetry_prod_eq_length_le`; the coordinate version over number fields is
`Lattices.exists_symmProd_eq`. -/
@[kb "omeara1963" "§43B, 43:3, p. 102 (weaker bound 2n; the sharp bound n is exists_symmetry_prod_eq_length_le)"]
theorem exists_symmetry_prod_eq (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length ≤ 2 * finrank F V := by
  obtain ⟨l, hl, h, hlen⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ
  exact ⟨l, hl, h, by omega⟩

/-- **Rotations of a space of dimension at most $3$ are products of two symmetries** (used in O'Meara 1963,
§55, 55:5, p. 140): by 43:3 a rotation of a regular space of dimension $\le 3$ is a product of at most $3$
symmetries; the determinant $1$ forces an even number, so at most $2$. -/
@[kb "omeara1963" "§55, 55:5, p. 140 (rotations of a space of dimension ≤ 3 are products of two symmetries)"]
theorem exists_symmetry_prod_eq_length_le_two (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hdim : finrank F V ≤ 3) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPlus Q) :
    ∃ l : List V, ∃ hl : ∀ u ∈ l, Q u ≠ 0,
      σ = (l.attach.map fun u => symmetry Q u.1 (hl u.1 u.2)).prod ∧ l.length ≤ 2 := by
  obtain ⟨l', hlen, h⟩ := cd_list Q hQ hσ.1
  obtain ⟨l, hl, hσ', hll⟩ := cd_repr Q h
  have hdet : LinearEquiv.det σ = 1 := MonoidHom.mem_ker.mp hσ.2
  rw [h, cd_det_prod] at hdet
  obtain ⟨a, ha⟩ := (neg_one_pow_eq_one_iff_even cd_neg_one_ne).mp hdet
  exact ⟨l, hl, hσ', by omega⟩

end CDFinal

end QuadFormsKB.OMeara
