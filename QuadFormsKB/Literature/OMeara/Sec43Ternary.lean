import QuadFormsKB.Literature.OMeara.Sec43A
import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Literature.OMeara.Sec91Units

/-!
# O'Meara §43: rotations of a ternary space fixing an isotropic vector (43:5)

**Setting** (as in `Sec43A.lean`): $F$ a field with $2 \ne 0$, $(V, Q)$ a finite-dimensional quadratic space over $F$,
$B$ = `bil Q` (so $B(x,x) = Q(x)$), *regular* = `(QuadraticMap.associated Q).Nondegenerate`, $O^+(V)$ = `orthPlus Q`.
Indices are 0-based; $n$ is the dimension.

**Proves** (O'Meara 1973 printing, §43, p. 105; checked against the printed page on 2026-10-27: 43:5 is the same statement, see below):
* `eichler` (definition): for an isotropic vector $x$ and $z \perp x$ the Eichler transformation
  $E_t v = v + t B(v,x)\,z - \bigl(t B(v,z) + \tfrac{t^2 Q(z)}{2} B(v,x)\bigr)x$, an isometry fixing $x$;
  `eichler_mul`: $E_t E_s = E_{t+s}$;
* `eichlerHom` / `eichlerEquiv` (**43:5**): for a regular ternary space with a frame $x, y, z$ ($Q(x) = Q(y) = 0$,
  $B(x,y) = 1$, $z \perp x, y$, $Q(z) \ne 0$) the map $t \mapsto E_t$ is an isomorphism of the additive group of $F$
  onto the group of rotations fixing $x$;
* `exists_mulEquiv_stabilizer` (**43:5**, frame-free form): for a regular ternary space and an isotropic vector
  $x \ne 0$, the group of rotations fixing $x$ is isomorphic to the additive group $(F,+)$.

**Not formalized:** 43:5a (the book's following remark is not available here; skipped).

**Proof notes.** A frame $x, y, z$ is a basis (independence is tested by pairing with $x, y, z$). In that basis a
rotation fixing $x$ has the shape $x \mapsto x$, $z \mapsto \alpha x + \gamma z$, $y \mapsto a x + c z + y$; isometry
forces $\gamma^2 = 1$, $\alpha = -c\,Q(z)$, $a = -c^2 Q(z)/2$, and the determinant is $\gamma$, so $\gamma = 1$ and the
map is $E_c$.
-/

open QuadraticMap Submodule Module LinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec43Ternary

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- **Eichler transformation as a linear map**: for $x, z \in V$ and $t \in F$,
$v \mapsto v + t B(v,x)\,z - \bigl(t B(v,z) + \tfrac{t^2 Q(z)}{2} B(v,x)\bigr)x$. It is an isometry fixing $x$ when
$Q(x) = 0$ and $B(x,z) = 0$ (`eichlerMap_isometry`). -/
def eichlerMap (x z : V) (t : F) : V →ₗ[F] V where
  toFun v := v + (t * bil Q v x) • z - (t * bil Q v z + t ^ 2 * Q z / 2 * bil Q v x) • x
  map_add' v w := by
    simp only [bil_add_left]
    match_scalars <;> ring
  map_smul' c v := by
    simp only [bil_smul_left, RingHom.id_apply]
    match_scalars <;> ring

theorem eichlerMap_apply (x z : V) (t : F) (v : V) :
    eichlerMap Q x z t v = v + (t * bil Q v x) • z - (t * bil Q v z + t ^ 2 * Q z / 2 * bil Q v x) • x := rfl

section Hyp

variable {x z : V} (hx : Q x = 0) (hxz : bil Q x z = 0)
include hx hxz

theorem bil_eichlerMap_x (t : F) (v : V) : bil Q (eichlerMap Q x z t v) x = bil Q v x := by
  rw [eichlerMap_apply]
  simp only [bil_sub_left, bil_add_left, bil_smul_left, bil_self, hx, bil_comm Q z x, hxz]
  ring

theorem bil_eichlerMap_z (t : F) (v : V) :
    bil Q (eichlerMap Q x z t v) z = bil Q v z + t * bil Q v x * Q z := by
  rw [eichlerMap_apply]
  simp only [bil_sub_left, bil_add_left, bil_smul_left, bil_self, hxz]
  ring

theorem eichlerMap_comp (t s : F) (v : V) :
    eichlerMap Q x z t (eichlerMap Q x z s v) = eichlerMap Q x z (t + s) v := by
  have h1 := eichlerMap_apply Q x z t (eichlerMap Q x z s v)
  rw [bil_eichlerMap_x Q hx hxz, bil_eichlerMap_z Q hx hxz] at h1
  rw [h1, eichlerMap_apply Q x z s v, eichlerMap_apply Q x z (t + s) v]
  match_scalars <;> field_simp <;> ring

theorem eichlerMap_zero (v : V) : eichlerMap Q x z 0 v = v := by
  rw [eichlerMap_apply]; simp

theorem eichlerMap_isometry (t : F) (v : V) : Q (eichlerMap Q x z t v) = Q v := by
  rw [← bil_self Q (eichlerMap Q x z t v), ← bil_self Q v, eichlerMap_apply]
  simp only [bil_add_left, bil_add_right, bil_sub_left, bil_sub_right, bil_smul_left, bil_smul_right]
  simp only [bil_self, hx, hxz, bil_comm Q z x, bil_comm Q x v, bil_comm Q z v]
  field_simp
  ring

end Hyp

section Equiv

/-- A linear automorphism has determinant $1$ as a unit iff its underlying linear map has determinant $1$. -/
theorem det_eq_one_iff {σ : V ≃ₗ[F] V} :
    LinearEquiv.det σ = 1 ↔ LinearMap.det (σ : V →ₗ[F] V) = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one]

/-- **Eichler transformation** $E_t$ (as a linear automorphism): for $x$ isotropic and $z \perp x$,
$E_t v = v + t B(v,x)\,z - \bigl(t B(v,z) + \tfrac{t^2 Q(z)}{2} B(v,x)\bigr)x$. Its inverse is $E_{-t}$
(`eichlerMap_comp`). -/
@[kb "omeara1963" "§43, 43:5, p. 105 (Eichler transformation, definition)"]
def eichler {x z : V} (hx : Q x = 0) (hxz : bil Q x z = 0) (t : F) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinearMap (eichlerMap Q x z t) (eichlerMap Q x z (-t))
    (LinearMap.ext fun v => by
      show eichlerMap Q x z t (eichlerMap Q x z (-t) v) = v
      rw [eichlerMap_comp Q hx hxz, add_neg_cancel, eichlerMap_zero Q hx hxz])
    (LinearMap.ext fun v => by
      show eichlerMap Q x z (-t) (eichlerMap Q x z t v) = v
      rw [eichlerMap_comp Q hx hxz, neg_add_cancel, eichlerMap_zero Q hx hxz])

theorem eichler_apply {x z : V} (hx : Q x = 0) (hxz : bil Q x z = 0) (t : F) (v : V) :
    eichler Q hx hxz t v = eichlerMap Q x z t v := rfl

/-- **The Eichler homomorphism** $t \mapsto E_t$ from the additive group of $F$ (written multiplicatively) to the group
of linear automorphisms of $V$: $E_t E_s = E_{t+s}$ and $E_0 = 1$. -/
@[kb "omeara1963" "§43, 43:5, p. 105 (Eichler homomorphism)"]
def eichlerHom {x z : V} (hx : Q x = 0) (hxz : bil Q x z = 0) : Multiplicative F →* (V ≃ₗ[F] V) where
  toFun t := eichler Q hx hxz (Multiplicative.toAdd t)
  map_one' := LinearEquiv.ext fun v => eichlerMap_zero Q hx hxz v
  map_mul' _ _ := LinearEquiv.ext fun v => (eichlerMap_comp Q hx hxz _ _ v).symm

/-- **The group of rotations fixing a vector $x$**: $\{\sigma \in O^+(V) : \sigma x = x\}$, the intersection of
`orthPlus Q` with the stabilizer of $x$. -/
@[kb "omeara1963" "§43, 43:5, p. 105 (rotations fixing x)"]
def rotationsFixing (x : V) : Subgroup (V ≃ₗ[F] V) :=
  orthPlus Q ⊓ MulAction.stabilizer (V ≃ₗ[F] V) x

theorem mem_rotationsFixing_iff {x : V} {σ : V ≃ₗ[F] V} :
    σ ∈ rotationsFixing Q x ↔ (∀ v, Q (σ v) = Q v) ∧ LinearEquiv.det σ = 1 ∧ σ x = x :=
  and_assoc

end Equiv

section Indep

variable {x y z : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
  (hxz : bil Q x z = 0) (hyz : bil Q y z = 0) (hz0 : z ≠ 0)
include hx hy hxy hxz hyz hz0

/-- The three vectors $x, z, y$ of a frame ($Q(x) = Q(y) = 0$, $B(x,y) = 1$, $z \ne 0$ orthogonal to $x$ and $y$) are
linearly independent. -/
theorem frame_linearIndependent : LinearIndependent F ![x, z, y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hg
  have bxx : bil Q x x = 0 := by rw [bil_self, hx]
  have byy : bil Q y y = 0 := by rw [bil_self, hy]
  have bzz : bil Q z z = Q z := bil_self Q z
  have byx : bil Q y x = 1 := by rw [bil_comm, hxy]
  have bzx : bil Q z x = 0 := by rw [bil_comm, hxz]
  have bzy : bil Q z y = 0 := by rw [bil_comm, hyz]
  have p0 : ∀ w, bil Q 0 w = 0 := fun w => by simp [bil]
  have e1 := congrArg (fun w => bil Q w x) hg
  have e2 := congrArg (fun w => bil Q w y) hg
  have e3 := congrArg (fun w => bil Q w z) hg
  simp only [bil_add_left, bil_smul_left, p0, bxx, bzx, byx, hxy, bzy, byy, hxz, hyz, bzz] at e1 e2 e3
  have g2 : g 2 = 0 := by simpa using e1
  have g0 : g 0 = 0 := by simpa using e2
  have g1 : g 1 = 0 := by
    rw [g0, g2, zero_smul, zero_smul, zero_add, add_zero] at hg
    exact (smul_eq_zero.1 hg).resolve_right hz0
  intro i
  fin_cases i <;> assumption

end Indep

section Frame

variable [FiniteDimensional F V] {x y z : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : bil Q x y = 1)
  (hxz : bil Q x z = 0) (hyz : bil Q y z = 0) (hz : Q z ≠ 0)
include hx hy hxy hxz hyz hz

omit hx hy hxy hxz hyz in
theorem frame_ne_zero : z ≠ 0 := fun h => hz (by rw [h]; exact map_zero Q)

theorem ext_frame (h3 : finrank F V = 3) {f g : V →ₗ[F] V} (h1 : f x = g x) (h2 : f z = g z)
    (h4 : f y = g y) : f = g := by
  let b := basisOfLinearIndependentOfCardEqFinrank (frame_linearIndependent Q hx hy hxy hxz hyz (frame_ne_zero Q hz))
    (by simp [h3])
  have hb : ∀ i, b i = ![x, z, y] i := fun i => by simp [b]
  refine b.ext fun i => ?_
  rw [hb]
  fin_cases i
  · simpa using h1
  · simpa using h2
  · simpa using h4

theorem det_frame (h3 : finrank F V = 3) (f : V →ₗ[F] V) (α γ a c : F) (h1 : f x = x)
    (h2 : f z = α • x + γ • z) (h4 : f y = a • x + c • z + y) : LinearMap.det f = γ := by
  let b := basisOfLinearIndependentOfCardEqFinrank (frame_linearIndependent Q hx hy hxy hxz hyz (frame_ne_zero Q hz))
    (by simp [h3])
  have hb0 : b 0 = x := by simp [b]
  have hb1 : b 1 = z := by simp [b]
  have hb2 : b 2 = y := by simp [b]
  have h1' : f (b 0) = b 0 := by rw [hb0]; exact h1
  have h2' : f (b 1) = α • b 0 + γ • b 1 := by rw [hb0, hb1]; exact h2
  have h4' : f (b 2) = a • b 0 + c • b 1 + b 2 := by rw [hb0, hb1, hb2]; exact h4
  have hM : LinearMap.toMatrix b b f = !![1, α, a; 0, γ, c; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, h1', h2', h4']
  rw [← LinearMap.det_toMatrix b f, hM, Matrix.det_fin_three]
  simp

theorem eichlerMap_x_eq (t : F) : eichlerMap Q x z t x = x := by
  rw [eichlerMap_apply]
  simp only [bil_self, hx, hxz]
  simp

theorem eichlerMap_z_eq (t : F) : eichlerMap Q x z t z = (-(t * Q z)) • x + (1 : F) • z := by
  rw [eichlerMap_apply]
  simp only [bil_self, bil_comm Q z x, hxz]
  module

theorem eichlerMap_y_eq (t : F) :
    eichlerMap Q x z t y = (-(t ^ 2 * Q z / 2)) • x + t • z + y := by
  rw [eichlerMap_apply]
  have byx : bil Q y x = 1 := by rw [bil_comm, hxy]
  simp only [byx, hyz]
  module

/-- Every rotation-type map $E_t$ is a rotation fixing $x$ (the determinant is $1$ by the triangular shape in the
basis $x, z, y$). -/
theorem eichler_mem_rotationsFixing (h3 : finrank F V = 3) (t : F) :
    eichler Q hx hxz t ∈ rotationsFixing Q x := by
  rw [mem_rotationsFixing_iff]
  refine ⟨eichlerMap_isometry Q hx hxz t, ?_, eichlerMap_x_eq Q hx hy hxy hxz hyz hz t⟩
  rw [det_eq_one_iff]
  exact det_frame Q hx hy hxy hxz hyz hz h3 (eichlerMap Q x z t) (-(t * Q z)) 1 (-(t ^ 2 * Q z / 2)) t
    (eichlerMap_x_eq Q hx hy hxy hxz hyz hz t) (eichlerMap_z_eq Q hx hy hxy hxz hyz hz t)
    (eichlerMap_y_eq Q hx hy hxy hxz hyz hz t)

/-- **Coordinates in a frame**: $w = B(w,y)\,x + B(w,x)\,y + \tfrac{B(w,z)}{Q(z)}\,z$ for every $w$. -/
theorem frame_expand (h3 : finrank F V = 3) (w : V) :
    w = bil Q w y • x + bil Q w x • y + ((Q z)⁻¹ * bil Q w z) • z := by
  let P : V →ₗ[F] V := ((associated Q).flip y).smulRight x + ((associated Q).flip x).smulRight y +
    ((Q z)⁻¹ • (associated Q).flip z).smulRight z
  have hP : ∀ w, P w = bil Q w y • x + bil Q w x • y + ((Q z)⁻¹ * bil Q w z) • z := fun w => rfl
  have byx : bil Q y x = 1 := by rw [bil_comm, hxy]
  have bzx : bil Q z x = 0 := by rw [bil_comm, hxz]
  have bzy : bil Q z y = 0 := by rw [bil_comm, hyz]
  have key : (LinearMap.id : V →ₗ[F] V) = P := by
    refine ext_frame Q hx hy hxy hxz hyz hz h3 ?_ ?_ ?_
    · rw [hP]; simp [hxy, hx, hxz]
    · rw [hP]; simp [bzx, bzy, hz]
    · rw [hP]; simp [byx, hy, hyz]
  exact (LinearMap.congr_fun key w).trans (hP w)

/-- A rotation fixing $x$ is an Eichler transformation $E_t$. -/
theorem exists_eq_eichler (h3 : finrank F V = 3) {σ : V ≃ₗ[F] V} (hσ : σ ∈ rotationsFixing Q x) :
    ∃ t : F, σ = eichler Q hx hxz t := by
  obtain ⟨hQσ, hdet, hfix⟩ := (mem_rotationsFixing_iff Q).1 hσ
  have hB : ∀ u w, bil Q (σ u) (σ w) = bil Q u w := by
    intro u w
    have h := hQσ (u + w)
    rw [map_add, Q_add, Q_add, hQσ u, hQσ w] at h
    have h4 : (2 : F) * bil Q (σ u) (σ w) = 2 * bil Q u w := by linear_combination h
    exact mul_left_cancel₀ two_ne_zero h4
  have bxx : bil Q x x = 0 := by rw [bil_self, hx]
  have byy : bil Q y y = 0 := by rw [bil_self, hy]
  have bzz : bil Q z z = Q z := bil_self Q z
  have byx : bil Q y x = 1 := by rw [bil_comm, hxy]
  have bzx : bil Q z x = 0 := by rw [bil_comm, hxz]
  have bzy : bil Q z y = 0 := by rw [bil_comm, hyz]
  -- σ z
  have hz1 : bil Q (σ z) x = 0 := by
    have := hB z x
    rw [hfix, bzx] at this
    exact this
  obtain ⟨α, γ, hσz⟩ : ∃ α γ : F, σ z = α • x + γ • z := by
    refine ⟨bil Q (σ z) y, (Q z)⁻¹ * bil Q (σ z) z, ?_⟩
    have h := frame_expand Q hx hy hxy hxz hyz hz h3 (σ z)
    rw [hz1, zero_smul, add_zero] at h
    exact h
  -- σ y
  have hy1 : bil Q (σ y) x = 1 := by
    have := hB y x
    rw [hfix, byx] at this
    exact this
  obtain ⟨a, c, hσy⟩ : ∃ a c : F, σ y = a • x + c • z + y := by
    refine ⟨bil Q (σ y) y, (Q z)⁻¹ * bil Q (σ y) z, ?_⟩
    have h := frame_expand Q hx hy hxy hxz hyz hz h3 (σ y)
    rw [hy1] at h
    calc σ y = _ := h
      _ = _ := by module
  have hγ : γ = 1 := by
    have := det_frame Q hx hy hxy hxz hyz hz h3 (σ : V →ₗ[F] V) α γ a c hfix hσz hσy
    rw [det_eq_one_iff] at hdet
    rw [← this]; exact hdet
  -- the constraints
  have hc2 := hQσ y
  rw [hσy, ← bil_self Q (a • x + c • z + y)] at hc2
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right] at hc2
  simp only [bil_self, hx, hy, hxy, hxz, bzx, bzy, hyz, byx, bzz] at hc2
  have hc3 := hB y z
  rw [hσy, hσz, hγ, hyz] at hc3
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right] at hc3
  simp only [bil_self, hx, hy, hxy, hxz, bzx, bzy, hyz, byx, bzz] at hc3
  have hα : α = -(c * Q z) := by linear_combination hc3
  have ha : a = -(c ^ 2 * Q z / 2) := by
    field_simp
    linear_combination hc2
  refine ⟨c, LinearEquiv.ext fun v => ?_⟩
  have hmap : (σ : V →ₗ[F] V) = eichlerMap Q x z c := by
    refine ext_frame Q hx hy hxy hxz hyz hz h3 ?_ ?_ ?_
    · rw [LinearEquiv.coe_coe, hfix, eichlerMap_x_eq Q hx hy hxy hxz hyz hz]
    · rw [LinearEquiv.coe_coe, hσz, eichlerMap_z_eq Q hx hy hxy hxz hyz hz, hα, hγ]
    · rw [LinearEquiv.coe_coe, hσy, eichlerMap_y_eq Q hx hy hxy hxz hyz hz, ha]
  exact LinearMap.congr_fun hmap v

/-- The Eichler homomorphism as a homomorphism onto the group of rotations fixing $x$. -/
def eichlerRot (h3 : finrank F V = 3) : Multiplicative F →* rotationsFixing Q x :=
  (eichlerHom Q hx hxz).codRestrict _
    (fun t => eichler_mem_rotationsFixing Q hx hy hxy hxz hyz hz h3 (Multiplicative.toAdd t))

theorem eichlerRot_bijective (h3 : finrank F V = 3) :
    Function.Bijective (eichlerRot Q hx hy hxy hxz hyz hz h3) := by
  constructor
  · intro a b hab
    have h := congrArg (fun s : rotationsFixing Q x => bil Q ((s : V ≃ₗ[F] V) y) z) hab
    change bil Q (eichlerMap Q x z (Multiplicative.toAdd a) y) z =
      bil Q (eichlerMap Q x z (Multiplicative.toAdd b) y) z at h
    have byx : bil Q y x = 1 := by rw [bil_comm, hxy]
    rw [bil_eichlerMap_z Q hx hxz, bil_eichlerMap_z Q hx hxz, byx, hyz] at h
    have h' : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      refine mul_right_cancel₀ hz ?_
      linear_combination h
    exact Multiplicative.toAdd.injective h'
  · rintro ⟨σ, hσ⟩
    obtain ⟨t, ht⟩ := exists_eq_eichler Q hx hy hxy hxz hyz hz h3 hσ
    exact ⟨Multiplicative.ofAdd t, Subtype.ext ht.symm⟩

/-- **O'Meara 43:5, with an explicit frame** (p. 105; checked against the printed page on 2026-10-27: a special case of the printed 43:5, which
does not name a frame but whose proof uses one, $V = (Fx + Fy) \perp Fz$). Let $V$ be a ternary quadratic space over a field $F$ of characteristic $\ne 2$ with a frame
$x, y, z$ ($Q(x) = Q(y) = 0$, $B(x,y) = 1$, $z \perp x, y$, $Q(z) \ne 0$; so $V = (Fx + Fy) \perp Fz$ is regular).
Then $t \mapsto E_t$ is an isomorphism from the additive group $(F,+)$ onto the group of rotations $\sigma \in O^+(V)$
with $\sigma x = x$. -/
@[kb "omeara1963" "§43, 43:5, p. 105 (rotations fixing an isotropic vector, explicit frame)"]
def eichlerEquiv (h3 : finrank F V = 3) : Multiplicative F ≃* rotationsFixing Q x :=
  MulEquiv.ofBijective (eichlerRot Q hx hy hxy hxz hyz hz h3) (eichlerRot_bijective Q hx hy hxy hxz hyz hz h3)

end Frame

section Main

variable [FiniteDimensional F V]

/-- A regular ternary space with an isotropic vector $x \ne 0$ has a frame: $y$ with $Q(y) = 0$, $B(x,y) = 1$ (42:13)
and $z \ne 0$ orthogonal to $x$ and $y$ (it exists since $\dim V = 3$), with $Q(z) \ne 0$ (otherwise $z$ would be in
the radical of the basis $x, z, y$). -/
theorem exists_frame (hQ : (QuadraticMap.associated Q).Nondegenerate) (h3 : finrank F V = 3) {x : V}
    (hx0 : x ≠ 0) (hx : Q x = 0) :
    ∃ y z : V, Q y = 0 ∧ bil Q x y = 1 ∧ bil Q x z = 0 ∧ bil Q y z = 0 ∧ Q z ≠ 0 := by
  obtain ⟨y, hy, hxy⟩ := exists_hyp_partner Q hQ hx0 hx
  let φ : V →ₗ[F] F × F := ((associated Q).flip x).prod ((associated Q).flip y)
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hr : finrank F (LinearMap.range φ) ≤ 2 := by
    calc finrank F (LinearMap.range φ) ≤ finrank F (F × F) := Submodule.finrank_le _
      _ = 2 := by simp
  have hk : 0 < finrank F (LinearMap.ker φ) := by omega
  obtain ⟨⟨z, hzk⟩, hz0'⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hk
  have hz0 : z ≠ 0 := fun h => hz0' (Subtype.ext h)
  have hφ := LinearMap.mem_ker.1 hzk
  have hzx : bil Q z x = 0 := congrArg Prod.fst hφ
  have hzy : bil Q z y = 0 := congrArg Prod.snd hφ
  have hxz : bil Q x z = 0 := by rw [bil_comm, hzx]
  have hyz : bil Q y z = 0 := by rw [bil_comm, hzy]
  refine ⟨y, z, hy, hxy, hxz, hyz, fun hQz => ?_⟩
  have hli := frame_linearIndependent Q hx hy hxy hxz hyz hz0
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h3])
  have hb : ∀ i, b i = ![x, z, y] i := fun i => by simp [b]
  have hzz : bil Q z z = 0 := by rw [bil_self, hQz]
  have hzero : (QuadraticMap.associated Q z : V →ₗ[F] F) = 0 := by
    refine b.ext fun i => ?_
    rw [hb]
    fin_cases i
    · simpa using hzx
    · simpa using hzz
    · simpa using hzy
  exact hz0 (hQ.1 z fun w => by simpa using LinearMap.congr_fun hzero w)

/-- **O'Meara 43:5** (§43, p. 105; checked against the printed page on 2026-10-27: the same statement, with "rotations having the
line as axis" read as the identity together with the rotations whose fixed space is the line). Let $V$ be a regular quadratic space of dimension $3$ over a field $F$ of characteristic $\ne 2$ and let
$x \ne 0$ be an isotropic vector ($Q(x) = 0$). Then the group of rotations $\{\sigma \in O^+(V) : \sigma x = x\}$ is
isomorphic to the additive group $(F,+)$ (written multiplicatively as `Multiplicative F`). Explicitly, for any
hyperbolic partner $y$ of $x$ and any $z$ orthogonal to $x$ and $y$ the isomorphism is $t \mapsto E_t$
(`eichlerEquiv`). Unconditional: no hypotheses beyond those stated. -/
@[kb "omeara1963" "§43, 43:5, p. 105 (rotations fixing an isotropic vector of a ternary space)"]
theorem exists_mulEquiv_rotationsFixing (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank F V = 3) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0) :
    Nonempty (Multiplicative F ≃* rotationsFixing Q x) := by
  obtain ⟨y, z, hy, hxy, hxz, hyz, hz⟩ := exists_frame Q hQ h3 hx0 hx
  exact ⟨eichlerEquiv Q hx hy hxy hxz hyz hz h3⟩

end Main

end Sec43Ternary

end QuadFormsKB.OMeara
