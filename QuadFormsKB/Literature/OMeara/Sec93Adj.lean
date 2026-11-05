/-
# O'Meara §93C–§93D: adjunction, cancellation of modular components (93:14a) and the classification of unimodular
lattices by the norm group (93:16)

**Setting** (as in `Sec93C.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a quadratic
space $(V, Q)$ over $F$, lattices = `Submodule R V`. O'Meara works over a dyadic local field; the arguments below use
only the discrete valuation ring (as 93:12, 93:13, 93:14 in `Sec93C.lean`).

**Proves**
* **Adjunction** (O'Meara's $L \perp J^{-1}$): orthogonal sums of spaces via Mathlib's `QuadraticMap.prod`
  (`adj_bil_prod`, `adj_isOrthSum_prod_left`, `adj_isOrthSum_prod_right`, `adj_isOrthSum_prod_split`,
  `adj_isometricLat_prod`, ...), the negative form $-Q$ (`adj_bil_neg`), and the transport of a splitting along an
  isometry of lattices (`adj_transport`);
* **Hyperbolic decomposition** (82:17 / 82:15, p. 257): `adj_exists_planeSum`: a finitely generated
  $\xi\mathfrak o$-modular lattice $M$ with a Lagrangian subspace $U$ (e.g. the diagonal of $A \perp B^{-1}$,
  `adj_planeSum_prod`) is an orthogonal sum of $\dim U$ planes $\xi A(\alpha_i, 0)$ (`AdjPlaneSum`);
* **Iterated 93:13** (`adj_planeSum_iter`) turning all planes into $\xi A(0, 0)$, and the **multi-plane scaled 93:14**
  (`adj_planeSum_cancel`, from `isometricLat_of_cancel_hyperbolic` for the form $\xi^{-1}Q$);
* `isometricLat_of_cancel_modular` (**93:14a**, pp. 257–258);
* `isometricLat_of_normGroup_eq`, `cls_eq_iff_normGroup_eq` (**93:16**, p. 259) and its footnote
  `cls_eq_iff_image_eq`, `cls_eq_iff_image_eq_of_hyperbolic`.

**Notes.** Planes are encoded by `AdjIsPlane Q ξ S J` ($J = \mathfrak ox + \mathfrak oy$, $B(x,y) = \xi$, $Q(y) = 0$,
$Q(x) \in \xi\mathfrak o \cap S$, i.e. $J \cong \xi A(\alpha, 0)$ with $\xi\alpha \in S$), and sums of $r$ planes by the
recursive predicate `AdjPlaneSum`; with $S = \{0\}$ these are the hyperbolic lattices $\xi A(0,0) \perp \cdots \perp
\xi A(0,0)$ of `IsModularHyperbolic`. No dyadic or Henselian hypothesis is needed anywhere.
-/
import QuadFormsKB.Literature.OMeara.Sec93E
import QuadFormsKB.Literature.OMeara.Sec92Jordan

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Basics

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable {V'' : Type*} [AddCommGroup V''] [Module F V''] [Module R V''] [IsScalarTower R F V'']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (Q'' : QuadraticForm F V'')

/-- If $Q(x + y) = Q(x) + 2c + Q(y)$ then $B(x, y) = c$. -/
theorem adj_eq_bil_of {x y : V} {c : F} (h : Q (x + y) = Q x + 2 * c + Q y) : bil Q x y = c := by
  have h1 := Q_add Q x y
  have h2 : (2 : F) * bil Q x y = 2 * c := by linear_combination h - h1
  exact mul_left_cancel₀ (two_ne_zero' F) h2

/-- **The bilinear form of an orthogonal sum of spaces**: $B((v, w), (v', w')) = B(v, v') + B'(w, w')$. -/
theorem adj_bil_prod (v v' : V) (w w' : V') :
    bil (Q.prod Q') (v, w) (v', w') = bil Q v v' + bil Q' w w' := by
  apply adj_eq_bil_of
  simp only [QuadraticMap.prod_apply, Prod.mk_add_mk]
  rw [Q_add Q, Q_add Q']; ring

/-- The bilinear form of the form $-Q$ is $-B$. -/
theorem adj_bil_neg (x y : V) : bil (-Q) x y = - bil Q x y := by
  apply adj_eq_bil_of
  simp only [neg_apply]
  rw [Q_add Q]; ring

/-- `IsometricLat` is reflexive. -/
theorem adj_isometricLat_refl (L : Submodule R V) : IsometricLat Q Q L L :=
  ⟨LinearEquiv.refl R L, fun _ => rfl⟩

/-- `IsometricLat` is symmetric. -/
theorem adj_isometricLat_symm {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    IsometricLat Q' Q K L := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, fun y => by simpa using (hf (f.symm y)).symm⟩

/-- `IsometricLat` is transitive (across three spaces). -/
theorem adj_isometricLat_trans {L : Submodule R V} {K : Submodule R V'} {M : Submodule R V''}
    (h1 : IsometricLat Q Q' L K) (h2 : IsometricLat Q' Q'' K M) : IsometricLat Q Q'' L M := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨f.trans g, fun x => by rw [LinearEquiv.trans_apply, hg, hf]⟩

/-- Swapping the two components of an orthogonal sum. -/
theorem adj_isOrthSum_symm {L J K : Submodule R V} (h : IsOrthSum Q L J K) : IsOrthSum Q L K J :=
  ⟨fun x hx y hy => by rw [bil_comm]; exact h.orth y hy x hx, h.disjoint.symm, by
    rw [sup_comm]; exact h.sup_eq⟩

/-- $L = 0 \perp L$. -/
theorem adj_isOrthSum_bot (L : Submodule R V) : IsOrthSum Q L ⊥ L :=
  ⟨fun x hx y _ => by rw [mem_bot] at hx; simp [hx, bil], disjoint_bot_left, by simp⟩

/-- If $L = 0 \perp K$ then $L = K$. -/
theorem adj_eq_of_isOrthSum_bot {L K : Submodule R V} (h : IsOrthSum Q L ⊥ K) : L = K := by
  rw [← h.sup_eq]; simp

/-- Associativity of orthogonal sums, first form: $P = A \perp N$, $N = B \perp C$ give $P = (A + B) \perp C$ and
$A + B = A \perp B$. -/
theorem adj_isOrthSum_assoc_left {P A N B C : Submodule R V} (h1 : IsOrthSum Q P A N)
    (h2 : IsOrthSum Q N B C) : IsOrthSum Q P (A ⊔ B) C ∧ IsOrthSum Q (A ⊔ B) A B := by
  have hBN : B ≤ N := h2.sup_eq ▸ le_sup_left
  have hCN : C ≤ N := h2.sup_eq ▸ le_sup_right
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun a ha b hb => h1.orth a ha b (hBN hb), h1.disjoint.mono_right hBN, rfl⟩⟩
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
    rw [bil_add_left, h1.orth a ha y (hCN hy), h2.orth b hb y hy, add_zero]
  · rw [Submodule.disjoint_def]
    intro x hx hxC
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
    have haN : a ∈ N := by
      have : a = (a + b) - b := by abel
      rw [this]; exact N.sub_mem (hCN hxC) (hBN hb)
    have ha0 : a = 0 := Submodule.disjoint_def.mp h1.disjoint a ha haN
    subst ha0
    rw [zero_add] at hxC ⊢
    exact Submodule.disjoint_def.mp h2.disjoint b hb hxC
  · rw [sup_assoc, h2.sup_eq, h1.sup_eq]

/-- Associativity of orthogonal sums, second form: $P = H \perp K$, $H = H_0 \perp H_1$ give $P = H_0 \perp
(H_1 + K)$ and $H_1 + K = H_1 \perp K$. -/
theorem adj_isOrthSum_assoc_right {P H K H₀ H₁ : Submodule R V} (h1 : IsOrthSum Q P H K)
    (h2 : IsOrthSum Q H H₀ H₁) : IsOrthSum Q P H₀ (H₁ ⊔ K) ∧ IsOrthSum Q (H₁ ⊔ K) H₁ K := by
  have h0H : H₀ ≤ H := h2.sup_eq ▸ le_sup_left
  have h1H : H₁ ≤ H := h2.sup_eq ▸ le_sup_right
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun a ha b hb => h1.orth a (h1H ha) b hb, h1.disjoint.mono_left h1H, rfl⟩⟩
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hy
    rw [bil_add_right, h2.orth x hx a ha, h1.orth x (h0H hx) b hb, add_zero]
  · rw [Submodule.disjoint_def]
    intro x hx hxs
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hxs
    have hbH : b ∈ H := by
      have : b = x - a := by rw [← hab]; abel
      rw [this]; exact H.sub_mem (h0H hx) (h1H ha)
    have hb0 : b = 0 := Submodule.disjoint_def.mp h1.disjoint b hbH hb
    subst hb0
    rw [add_zero] at hab
    subst hab
    exact Submodule.disjoint_def.mp h2.disjoint a hx ha
  · rw [← sup_assoc, h2.sup_eq, h1.sup_eq]

/-- Orthogonal sum with a lattice in the second space: $L \times T = (J \times T) \perp (K \times 0)$. -/
theorem adj_isOrthSum_prod_left {L J K : Submodule R V} (h : IsOrthSum Q L J K) (T : Submodule R V') :
    IsOrthSum (Q.prod Q') (L.prod T) (J.prod T) (K.prod ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    obtain rfl : d = 0 := (mem_bot R).mp hd
    rw [adj_bil_prod]
    simp [h.orth a ha c hc, bil]
  · rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    obtain rfl : b = 0 := (mem_bot R).mp hb'
    have : a = 0 := Submodule.disjoint_def.mp h.disjoint a ha ha'
    simp [this]
  · apply le_antisymm
    · exact sup_le (Submodule.prod_mono (h.sup_eq ▸ le_sup_left) le_rfl)
        (Submodule.prod_mono (h.sup_eq ▸ le_sup_right) bot_le)
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rw [← h.sup_eq] at ha
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp ha
      exact mem_sup.mpr ⟨(j, b), ⟨hj, hb⟩, (k, 0), ⟨hk, zero_mem _⟩, by simp⟩

/-- Orthogonal sum with a lattice in the first space: $S \times T = (S \times A) \perp (0 \times B)$. -/
theorem adj_isOrthSum_prod_right (S : Submodule R V) {T A B : Submodule R V'} (h : IsOrthSum Q' T A B) :
    IsOrthSum (Q.prod Q') (S.prod T) (S.prod A) ((⊥ : Submodule R V).prod B) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    obtain rfl : c = 0 := (mem_bot R).mp hc
    rw [adj_bil_prod]
    simp [h.orth b hb d hd, bil]
  · rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    obtain rfl : a = 0 := (mem_bot R).mp ha'
    have : b = 0 := Submodule.disjoint_def.mp h.disjoint b hb hb'
    simp [this]
  · apply le_antisymm
    · exact sup_le (Submodule.prod_mono le_rfl (h.sup_eq ▸ le_sup_left))
        (Submodule.prod_mono bot_le (h.sup_eq ▸ le_sup_right))
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rw [← h.sup_eq] at hb
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hb
      exact mem_sup.mpr ⟨(a, j), ⟨ha, hj⟩, (0, k), ⟨zero_mem _, hk⟩, by simp⟩

/-- The pure product splitting $L \times T = (L \times 0) \perp (0 \times T)$. -/
theorem adj_isOrthSum_prod_split (L : Submodule R V) (T : Submodule R V') :
    IsOrthSum (Q.prod Q') (L.prod T) (L.prod ⊥) ((⊥ : Submodule R V).prod T) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    obtain rfl : b = 0 := (mem_bot R).mp hb
    obtain rfl : c = 0 := (mem_bot R).mp hc
    rw [adj_bil_prod]
    simp [bil]
  · rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    obtain rfl : b = 0 := (mem_bot R).mp hb
    obtain rfl : a = 0 := (mem_bot R).mp ha'
    simp
  · apply le_antisymm
    · exact sup_le (Submodule.prod_mono le_rfl bot_le) (Submodule.prod_mono bot_le le_rfl)
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact mem_sup.mpr ⟨(a, 0), ⟨ha, zero_mem _⟩, (0, b), ⟨zero_mem _, hb⟩, by simp⟩

/-- $L \cong L \times 0$. -/
theorem adj_isometricLat_prod_bot (L : Submodule R V) : IsometricLat Q (Q.prod Q') L (L.prod ⊥) := by
  refine ⟨{ toFun := fun x => ⟨((x : V), (0 : V')), x.2, zero_mem _⟩
            map_add' := fun x y => by ext <;> simp
            map_smul' := fun c x => by ext <;> simp
            invFun := fun y => ⟨y.1.1, y.2.1⟩
            left_inv := fun x => rfl
            right_inv := fun y => Subtype.ext (Prod.ext rfl ((mem_bot R).mp y.2.2).symm) },
    fun x => ?_⟩
  simp [QuadraticMap.prod_apply]

/-- $T \cong 0 \times T$. -/
theorem adj_isometricLat_bot_prod (T : Submodule R V') :
    IsometricLat Q' (Q.prod Q') T ((⊥ : Submodule R V).prod T) := by
  refine ⟨{ toFun := fun x => ⟨((0 : V), (x : V')), zero_mem _, x.2⟩
            map_add' := fun x y => by ext <;> simp
            map_smul' := fun c x => by ext <;> simp
            invFun := fun y => ⟨y.1.2, y.2.2⟩
            left_inv := fun x => rfl
            right_inv := fun y => Subtype.ext (Prod.ext ((mem_bot R).mp y.2.1).symm rfl) },
    fun x => ?_⟩
  simp [QuadraticMap.prod_apply]

end Basics

section Basics2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable {V'' : Type*} [AddCommGroup V''] [Module F V''] [Module R V''] [IsScalarTower R F V'']
variable {V3 : Type*} [AddCommGroup V3] [Module F V3] [Module R V3] [IsScalarTower R F V3]
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (Q'' : QuadraticForm F V'')
  (Q3 : QuadraticForm F V3)

/-- **Products of isometries are isometries.** -/
theorem adj_isometricLat_prod {A : Submodule R V} {B : Submodule R V'} {A2 : Submodule R V''}
    {B2 : Submodule R V3} (h1 : IsometricLat Q Q'' A A2) (h2 : IsometricLat Q' Q3 B B2) :
    IsometricLat (Q.prod Q') (Q''.prod Q3) (A.prod B) (A2.prod B2) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  refine ⟨((Submodule.prodEquiv A B).trans (LinearEquiv.prodCongr f g)).trans
    (Submodule.prodEquiv A2 B2).symm, fun x => ?_⟩
  simp [QuadraticMap.prod_apply, hf, hg]

/-- The scale is monotone under isometries of lattices. -/
theorem adj_scale_le {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    scale Q L ≤ scale Q' K := by
  obtain ⟨f, hf⟩ := h
  rw [scale, span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have := bil_eq_of_isometricLat Q Q' f hf ⟨x, hx⟩ ⟨y, hy⟩
  show bil Q x y ∈ scale Q' K
  rw [← this]
  exact bil_mem_scale Q' (f _).2 (f _).2

/-- Isometric lattices have the same norm group (O'Meara 1963, §93A, p. 251). -/
theorem adj_normGroup_le {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    normGroup Q L ≤ normGroup Q' K := by
  obtain ⟨f, hf⟩ := h
  rintro _ ⟨x, hx, c, hc, rfl⟩
  exact ⟨f ⟨x, hx⟩, (f _).2, c, adj_scale_le Q Q' ⟨f, hf⟩ hc, by rw [hf]⟩

/-- Isometric lattices have the same norm group (O'Meara 1963, §93A, p. 251). -/
theorem adj_normGroup_eq {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K) :
    normGroup Q L = normGroup Q' K :=
  le_antisymm (adj_normGroup_le Q Q' h) (adj_normGroup_le Q' Q (adj_isometricLat_symm Q Q' h))

/-- $(K^{\mathfrak a}) \times 0 \subseteq (K \times 0)^{\mathfrak a}$. -/
theorem adj_subA_prod_bot_le (a : Submodule R F) (K : Submodule R V) :
    (subA Q a K).prod (⊥ : Submodule R V') ≤ subA (Q.prod Q') a (K.prod ⊥) := by
  rintro ⟨k, w⟩ ⟨hk, hw⟩
  obtain rfl : w = 0 := (mem_bot R).mp hw
  refine ⟨⟨hk.1, zero_mem _⟩, ?_⟩
  rintro ⟨k', w'⟩ ⟨hk', hw'⟩
  obtain rfl : w' = 0 := (mem_bot R).mp hw'
  show bil (Q.prod Q') (k, 0) (k', 0) ∈ a
  rw [adj_bil_prod]
  simpa [bil] using hk.2 k' hk'

/-- $0 \times (K^{\mathfrak a}) \subseteq (0 \times K)^{\mathfrak a}$. -/
theorem adj_subA_bot_prod_le (a : Submodule R F) (K : Submodule R V') :
    (⊥ : Submodule R V).prod (subA Q' a K) ≤ subA (Q.prod Q') a ((⊥ : Submodule R V).prod K) := by
  rintro ⟨w, k⟩ ⟨hw, hk⟩
  obtain rfl : w = 0 := (mem_bot R).mp hw
  refine ⟨⟨zero_mem _, hk.1⟩, ?_⟩
  rintro ⟨w', k'⟩ ⟨hw', hk'⟩
  obtain rfl : w' = 0 := (mem_bot R).mp hw'
  show bil (Q.prod Q') (0, k) (0, k') ∈ a
  rw [adj_bil_prod]
  simpa [bil] using hk.2 k' hk'

/-- $\mathfrak g(K^{\mathfrak a}) \subseteq \mathfrak g((K \times 0)^{\mathfrak a})$. -/
theorem adj_normGroup_subA_prod_bot_le (a : Submodule R F) (K : Submodule R V) :
    normGroup Q (subA Q a K) ≤ normGroup (Q.prod Q') (subA (Q.prod Q') a (K.prod (⊥ : Submodule R V'))) :=
  (adj_normGroup_le Q (Q.prod Q') (adj_isometricLat_prod_bot Q Q' (subA Q a K))).trans
    (normGroup_mono _ (adj_subA_prod_bot_le Q Q' a K))

/-- $\mathfrak g(K^{\mathfrak a}) \subseteq \mathfrak g((0 \times K)^{\mathfrak a})$. -/
theorem adj_normGroup_subA_bot_prod_le (a : Submodule R F) (K : Submodule R V') :
    normGroup Q' (subA Q' a K) ≤ normGroup (Q.prod Q') (subA (Q.prod Q') a ((⊥ : Submodule R V).prod K)) :=
  (adj_normGroup_le Q' (Q.prod Q') (adj_isometricLat_bot_prod Q Q' (subA Q' a K))).trans
    (normGroup_mono _ (adj_subA_bot_prod_le Q Q' a K))

/-- The image of a sublattice $A$ of $P$ under an isometry $f : P \to M$ of lattices. -/
def adjImg {P : Submodule R V} {M : Submodule R V'} (f : P ≃ₗ[R] M) (A : Submodule R V) :
    Submodule R V' :=
  (A.comap P.subtype).map (M.subtype ∘ₗ (f : P →ₗ[R] M))

/-- Membership in the image of a sublattice. -/
theorem adj_mem_adjImg {P : Submodule R V} {M : Submodule R V'} (f : P ≃ₗ[R] M) {A : Submodule R V}
    {y : V'} : y ∈ adjImg f A ↔ ∃ p : P, (p : V) ∈ A ∧ (f p : V') = y := by
  unfold adjImg
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- An isometry carries a sublattice isometrically onto its image. -/
theorem adj_isometricLat_adjImg {P : Submodule R V} {M : Submodule R V'} (f : P ≃ₗ[R] M)
    (hf : ∀ x : P, Q' (f x : V') = Q (x : V)) {A : Submodule R V} (hA : A ≤ P) :
    IsometricLat Q Q' A (adjImg f A) := by
  let φ : A →ₗ[R] adjImg f A := LinearMap.codRestrict _
    ((M.subtype ∘ₗ (f : P →ₗ[R] M)) ∘ₗ Submodule.inclusion hA)
    (fun a => (adj_mem_adjImg f).mpr ⟨Submodule.inclusion hA a, a.2, rfl⟩)
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : (f (Submodule.inclusion hA a) : V') = f (Submodule.inclusion hA b) :=
      congrArg (fun z : adjImg f A => (z : V')) hab
    have h2 := f.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun z : P => (z : V)) h2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨p, hp, rfl⟩ := (adj_mem_adjImg f).mp hy
    exact ⟨⟨p, hp⟩, Subtype.ext rfl⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => hf _⟩

/-- **Transport of a splitting along an isometry** (the transport lemma of the adjunction argument): if $P \cong M$
and $P = A \perp B$ then $M = A' \perp B'$ with $A \cong A'$ and $B \cong B'$. -/
theorem adj_transport {P : Submodule R V} {M : Submodule R V'} (e : IsometricLat Q Q' P M)
    {A B : Submodule R V} (h : IsOrthSum Q P A B) :
    ∃ A' B' : Submodule R V', IsOrthSum Q' M A' B' ∧ IsometricLat Q Q' A A' ∧
      IsometricLat Q Q' B B' := by
  obtain ⟨f, hf⟩ := e
  have hAP : A ≤ P := h.sup_eq ▸ le_sup_left
  have hBP : B ≤ P := h.sup_eq ▸ le_sup_right
  have hle : ∀ C : Submodule R V, adjImg f C ≤ M := by
    intro C y hy
    obtain ⟨p, -, rfl⟩ := (adj_mem_adjImg f).mp hy
    exact (f p).2
  refine ⟨adjImg f A, adjImg f B, ⟨?_, ?_, ?_⟩, adj_isometricLat_adjImg Q Q' f hf hAP,
    adj_isometricLat_adjImg Q Q' f hf hBP⟩
  · intro y hy z hz
    obtain ⟨p, hp, rfl⟩ := (adj_mem_adjImg f).mp hy
    obtain ⟨q, hq, rfl⟩ := (adj_mem_adjImg f).mp hz
    rw [bil_eq_of_isometricLat Q Q' f hf p q]
    exact h.orth _ hp _ hq
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨p, hp, rfl⟩ := (adj_mem_adjImg f).mp hy
    obtain ⟨q, hq, hqp⟩ := (adj_mem_adjImg f).mp hy'
    have hqp' : q = p := f.injective (Subtype.ext hqp)
    subst hqp'
    have : (q : V) = 0 := Submodule.disjoint_def.mp h.disjoint _ hp hq
    have : q = 0 := Subtype.ext this
    simp [this]
  · apply le_antisymm
    · exact sup_le (hle A) (hle B)
    · intro m hm
      obtain ⟨p, hp⟩ := f.surjective ⟨m, hm⟩
      have hpv : (p : V) ∈ A ⊔ B := h.sup_eq ▸ p.2
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hpv
      have hp' : p = ⟨a, hAP ha⟩ + ⟨b, hBP hb⟩ := Subtype.ext hab.symm
      have hm' : m = (f ⟨a, hAP ha⟩ : V') + (f ⟨b, hBP hb⟩ : V') := by
        have := congrArg Subtype.val hp
        rw [hp', map_add] at this
        simpa using this.symm
      rw [hm']
      exact add_mem (mem_sup_left ((adj_mem_adjImg f).mpr ⟨_, ha, rfl⟩))
        (mem_sup_right ((adj_mem_adjImg f).mpr ⟨_, hb, rfl⟩))

end Basics2

section Planes

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **A plane** $\mathfrak ox + \mathfrak oy \cong \xi A(\alpha, 0)$ with $\xi\alpha = Q(x)$ in a prescribed set $S$:
$J = \mathfrak ox + \mathfrak oy$ with $B(x, y) = \xi$, $Q(y) = 0$, $Q(x) \in \xi\mathfrak o \cap S$. With
$S = \{0\}$ this is a hyperbolic plane $\xi A(0, 0)$. -/
def AdjIsPlane (ξ : F) (S : Set F) (J : Submodule R V) : Prop :=
  ∃ x y : V, J = span R {x, y} ∧ bil Q x y = ξ ∧ Q y = 0 ∧ Q x ∈ S ∧ Q x ∈ R ∙ ξ

/-- **Orthogonal sum of $r$ planes** (`AdjIsPlane`): $H = J_1 \perp \cdots \perp J_r$, defined recursively. With
$S = \{0\}$ these are the lattices $\xi A(0,0) \perp \cdots \perp \xi A(0,0)$ of O'Meara's hyperbolic adjunction
(§93C, p. 257). -/
def AdjPlaneSum (ξ : F) (S : Set F) : ℕ → Submodule R V → Prop
  | 0, H => H = ⊥
  | r + 1, H => ∃ H₀ H₁ : Submodule R V, IsOrthSum Q H H₀ H₁ ∧ AdjIsPlane Q ξ S H₀ ∧ AdjPlaneSum ξ S r H₁

/-- Planes are carried to planes by isometries of lattices. -/
theorem adj_isPlane_of_isometric {ξ : F} {S : Set F} {J : Submodule R V} {J' : Submodule R V'}
    (h : IsometricLat Q Q' J J') (hp : AdjIsPlane Q ξ S J) : AdjIsPlane Q' ξ S J' := by
  obtain ⟨x, y, hJ, hxy, hQy, hQx, hQxξ⟩ := hp
  obtain ⟨f, hf⟩ := h
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  refine ⟨f ⟨x, hxJ⟩, f ⟨y, hyJ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro w hw
      obtain ⟨p, hp⟩ := f.surjective ⟨w, hw⟩
      have hpv : (f p : V') = w := congrArg Subtype.val hp
      rw [← hpv]
      have hpJ : (p : V) ∈ span R {x, y} := hJ ▸ p.2
      obtain ⟨a, b, hab⟩ := mem_span_pair.mp hpJ
      have : p = a • (⟨x, hxJ⟩ : J) + b • (⟨y, hyJ⟩ : J) := Subtype.ext (by simpa using hab.symm)
      rw [this, map_add, map_smul, map_smul]
      exact add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
    · rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact (f _).2
      · exact (f _).2
  · rw [bil_eq_of_isometricLat Q Q' f hf]; exact hxy
  · rw [hf]; exact hQy
  · rw [hf]; exact hQx
  · rw [hf]; exact hQxξ

/-- Orthogonal sums of planes are carried to orthogonal sums of planes by isometries of lattices. -/
theorem adj_planeSum_of_isometric {ξ : F} {S : Set F} (r : ℕ) :
    ∀ {H : Submodule R V} {H' : Submodule R V'}, IsometricLat Q Q' H H' →
      AdjPlaneSum Q ξ S r H → AdjPlaneSum Q' ξ S r H' := by
  induction r with
  | zero =>
    intro H H' e hH
    simp only [AdjPlaneSum] at hH ⊢
    obtain ⟨f, hf⟩ := e
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨p, hp⟩ := f.surjective ⟨w, hw⟩
    have key : ∀ v : V, v ∈ H → v = 0 := fun v hv => (mem_bot R).mp (hH ▸ hv)
    have hp' : p = 0 := Subtype.ext (key _ p.2)
    have h3 : (f p : V') = w := congrArg (fun z : H' => (z : V')) hp
    rw [hp', map_zero] at h3
    have hw0 : w = 0 := by rw [← h3]; simp
    rw [hw0]; exact zero_mem _
  | succ r ih =>
    intro H H' e hH
    simp only [AdjPlaneSum] at hH ⊢
    obtain ⟨H₀, H₁, h, hp, hr⟩ := hH
    obtain ⟨A', B', hAB, hA, hB⟩ := adj_transport Q Q' e h
    exact ⟨A', B', hAB, adj_isPlane_of_isometric Q Q' hA hp, ih hB hr⟩

/-- $K^{\mathfrak a} \subseteq N^{\mathfrak a}$ when $K$ is an orthogonal summand of $N$. -/
theorem adj_subA_le {N H₁ K : Submodule R V} (h : IsOrthSum Q N H₁ K) (a : Submodule R F) :
    subA Q a K ≤ subA Q a N := by
  intro z hz
  have hKN : K ≤ N := h.sup_eq ▸ le_sup_right
  refine ⟨hKN hz.1, fun n hn => ?_⟩
  rw [← h.sup_eq] at hn
  obtain ⟨a', ha', b, hb, rfl⟩ := mem_sup.mp hn
  rw [bil_add_right, bil_comm Q z a', h.orth a' ha' z hz.1, zero_add]
  exact hz.2 b hb

/-- **Iterated 93:13** (O'Meara 1963, §93C, p. 257, "successive application of 93:13"): let $P = H \perp K$ where
$H = J_1 \perp \cdots \perp J_r$ with $J_i \cong \xi A(\alpha_i, 0)$ and $\xi\alpha_i \in S \subseteq
\mathfrak g(K^{\xi\mathfrak o})$, and let $P \cong M$. Then $M = H' \perp K'$ with $H'$ an orthogonal sum of $r$
planes $\xi A(0, 0)$ and $K' \cong K$. -/
theorem adj_planeSum_iter {ξ : F} (hξ : ξ ≠ 0) (S : Set F) (r : ℕ) :
    ∀ {P M H K : Submodule R V}, AdjPlaneSum Q ξ S r H → IsOrthSum Q P H K → IsometricLat Q Q P M →
      (∀ s ∈ S, s ∈ normGroup Q (subA Q (R ∙ ξ) K)) →
      ∃ H' K' : Submodule R V, IsOrthSum Q M H' K' ∧ AdjPlaneSum Q ξ {0} r H' ∧ IsometricLat Q Q K K' := by
  induction r with
  | zero =>
    intro P M H K hH hPHK e _
    simp only [AdjPlaneSum] at hH
    subst hH
    have hPK : P = K := adj_eq_of_isOrthSum_bot Q hPHK
    subst hPK
    exact ⟨⊥, M, adj_isOrthSum_bot Q M, by simp only [AdjPlaneSum], e⟩
  | succ r ih =>
    intro P M H K hH hPHK e hS
    simp only [AdjPlaneSum] at hH
    obtain ⟨H₀, H₁, h01, ⟨x, y, hH₀, hxy, hQy, hQxS, hQxξ⟩, hr⟩ := hH
    obtain ⟨hP0, hN1⟩ := adj_isOrthSum_assoc_right Q hPHK h01
    obtain ⟨α, hα⟩ := mem_span_singleton.mp hQxξ
    have hQx : Q x = ξ * algebraMap R F α := by rw [← hα, Algebra.smul_def]; ring
    obtain ⟨z, hz, c, hc, hzc⟩ := neg_mem (hS _ hQxS)
    have hsub := adj_subA_le Q hN1 (R ∙ ξ)
    obtain ⟨x', y', α', hα', hQx', hxy', hQy', hs, hiso⟩ :=
      exists_isOrthSum_matA Q hP0 hξ hH₀ hQx hxy hQy (hsub hz) (scale_mono Q hsub hc)
    have hξ' : ξ⁻¹ * ξ = 1 := inv_mul_cancel₀ hξ
    have h0 : algebraMap R F α' = 0 := by
      rw [hα', ← hzc, hQx]
      linear_combination (-(algebraMap R F α)) * hξ'
    have hQx0 : Q x' = 0 := by rw [hQx', h0, mul_zero]
    obtain ⟨A', B', hAB, hA, hB⟩ := adj_transport Q Q e hs
    have hpl : AdjIsPlane Q ξ {0} A' :=
      adj_isPlane_of_isometric Q Q hA ⟨x', y', rfl, hxy', hQy', Set.mem_singleton_iff.mpr hQx0,
        by rw [hQx0]; exact zero_mem _⟩
    obtain ⟨H'', K'', hM, hpl'', hKK⟩ := ih hr hN1 (adj_isometricLat_trans Q Q Q hiso hB) hS
    obtain ⟨h1, h2⟩ := adj_isOrthSum_assoc_left Q hAB hM
    exact ⟨A' ⊔ H'', K'', h1, ⟨A', H'', h2, hpl, hpl''⟩, hKK⟩

/-- **Scaled 93:14 for one hyperbolic plane**: if $L = J \perp K = J' \perp K'$ with $J, J'$ spanned by pairs
$x, y$ and $x', y'$ with $Q(x) = Q(y) = Q(x') = Q(y') = 0$ and $B(x, y) = B(x', y') = \xi \ne 0$, then
$K \cong K'$ (93:14 for the form $\xi^{-1}Q$). -/
theorem adj_cancel_plane {ξ : F} (hξ : ξ ≠ 0) {L J K J' K' : Submodule R V} (h : IsOrthSum Q L J K)
    (h' : IsOrthSum Q L J' K') {x y x' y' : V} (hJ : J = span R {x, y}) (hJ' : J' = span R {x', y'})
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = ξ) (hQx' : Q x' = 0) (hQy' : Q y' = 0)
    (hxy' : bil Q x' y' = ξ) : IsometricLat Q Q K K' := by
  have hb1 : ∀ u v, bil (ξ⁻¹ • Q) u v = ξ⁻¹ * bil Q u v := fun u v =>
    adj_eq_bil_of _ (by
      simp only [smul_apply, smul_eq_mul]
      rw [Q_add Q]; ring)
  have hQ1 : ∀ u, (ξ⁻¹ • Q) u = ξ⁻¹ * Q u := fun u => by simp
  have hs : ∀ {L J K : Submodule R V}, IsOrthSum Q L J K → IsOrthSum (ξ⁻¹ • Q) L J K :=
    fun h => ⟨fun a ha b hb => by rw [hb1, h.orth a ha b hb, mul_zero], h.disjoint, h.sup_eq⟩
  have hξ' : ξ⁻¹ * ξ = 1 := inv_mul_cancel₀ hξ
  obtain ⟨f, hf⟩ := isometricLat_of_cancel_hyperbolic (ξ⁻¹ • Q) (hs h) (hs h') hJ hJ'
    (by rw [hQ1, hQx, mul_zero]) (by rw [hQ1, hQy, mul_zero]) (by rw [hb1, hxy, hξ'])
    (by rw [hQ1, hQx', mul_zero]) (by rw [hQ1, hQy', mul_zero]) (by rw [hb1, hxy', hξ'])
  refine ⟨f, fun a => ?_⟩
  have := hf a
  rw [hQ1, hQ1] at this
  exact mul_left_cancel₀ (inv_ne_zero hξ) this

/-- **Multi-plane scaled 93:14**: if $N \cong N'$, $N = H \perp K$, $N' = H' \perp K'$ with $H, H'$ orthogonal sums
of the same number $r$ of hyperbolic planes $\xi A(0, 0)$, then $K \cong K'$. -/
theorem adj_planeSum_cancel {ξ : F} (hξ : ξ ≠ 0) (r : ℕ) :
    ∀ {N N' H K H' K' : Submodule R V}, IsometricLat Q Q N N' → IsOrthSum Q N H K → IsOrthSum Q N' H' K' →
      AdjPlaneSum Q ξ {0} r H → AdjPlaneSum Q ξ {0} r H' → IsometricLat Q Q K K' := by
  induction r with
  | zero =>
    intro N N' H K H' K' e h h' hH hH'
    simp only [AdjPlaneSum] at hH hH'
    subst hH; subst hH'
    rw [← adj_eq_of_isOrthSum_bot Q h, ← adj_eq_of_isOrthSum_bot Q h']
    exact e
  | succ r ih =>
    intro N N' H K H' K' e h h' hH hH'
    simp only [AdjPlaneSum] at hH hH'
    obtain ⟨H₀, H₁, h01, ⟨x, y, hH₀, hxy, hQy, hQx, -⟩, hr⟩ := hH
    obtain ⟨H₀', H₁', h01', ⟨x', y', hH₀', hxy', hQy', hQx', -⟩, hr'⟩ := hH'
    obtain ⟨hN0, hN1⟩ := adj_isOrthSum_assoc_right Q h h01
    obtain ⟨hN0', hN1'⟩ := adj_isOrthSum_assoc_right Q h' h01'
    obtain ⟨A', B', hAB, hA, hB⟩ := adj_transport Q Q e hN0
    obtain ⟨x1, y1, hA1, hxy1, hQy1, hQx1, -⟩ :=
      adj_isPlane_of_isometric Q Q hA ⟨x, y, hH₀, hxy, hQy, hQx, by rw [Set.mem_singleton_iff.mp hQx]; exact zero_mem _⟩
    exact ih (adj_isometricLat_trans Q Q Q hB
      (adj_cancel_plane Q hξ hAB hN0' hA1 hH₀' (Set.mem_singleton_iff.mp hQx1) hQy1 hxy1
        (Set.mem_singleton_iff.mp hQx') hQy' hxy')) hN1 hN1' hr hr'

end Planes

section Lagrangian

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Self-dual-type lattice**: $M$ is a lattice with $\mathfrak sM \subseteq \xi\mathfrak o$, regular, and equal to
its dual $\{w \in FM : B(w, M) \subseteq \xi\mathfrak o\}$. (A finitely generated $\xi\mathfrak o$-modular lattice
has these properties; they are inherited by orthogonal summands.) -/
structure AdjSelfDual (ξ : F) (M : Submodule R V) : Prop where
  scale_le : scale Q M ≤ R ∙ ξ
  regular : ∀ m ∈ M, (∀ m' ∈ M, bil Q m m' = 0) → m = 0
  dual : ∀ w ∈ span F (M : Set V), (∀ m ∈ M, bil Q w m ∈ R ∙ ξ) → w ∈ M

/-- **A Lagrangian subspace**: $U \subseteq FM$ is totally isotropic and equal to its orthogonal complement in
$FM$ (so $2 \dim U = \dim FM$), for a self-dual-type lattice $M$. -/
structure AdjLagr (ξ : F) (M : Submodule R V) (U : Submodule F V) : Prop where
  sd : AdjSelfDual Q ξ M
  iso : ∀ u ∈ U, ∀ u' ∈ U, bil Q u u' = 0
  le_span : U ≤ span F (M : Set V)
  max : ∀ w ∈ span F (M : Set V), (∀ u ∈ U, bil Q w u = 0) → w ∈ U

/-- If $B(t, v) = 0$ for all $t \in T$ then $B(w, v) = 0$ for all $w \in FT$. -/
theorem adj_bil_span_left {T : Set V} {v : V} (h : ∀ t ∈ T, bil Q t v = 0) {w : V}
    (hw : w ∈ span F T) : bil Q w v = 0 :=
  span_induction (p := fun w _ => bil Q w v = 0) h (by simp [bil])
    (fun a b _ _ ha hb => by rw [bil_add_left, ha, hb, add_zero])
    (fun c a _ ha => by rw [bil_smul_left, ha, mul_zero]) hw

/-- The $F$-span of a finitely generated lattice is finite dimensional. -/
theorem adj_finiteDimensional_span {M : Submodule R V} (hM : M.FG) :
    FiniteDimensional F (span F (M : Set V)) := by
  obtain ⟨s, hs⟩ := hM
  have : span F (M : Set V) = span F (s : Set V) := by rw [← hs, Submodule.span_span_of_tower]
  rw [this]
  exact FiniteDimensional.span_finset F s

/-- **A primitive isotropic vector** (the use of 82:17 in O'Meara's proof of 93:14a): if $U \ne 0$ is a Lagrangian
subspace for $M$, there are $x \in M$ and $y \in M \cap U$ with $B(x, y) = \xi$. -/
theorem adj_exists_pair {ξ : F} {M : Submodule R V} {U : Submodule F V} (hM : M.FG)
    (hL : AdjLagr Q ξ M U) (hU : U ≠ ⊥) :
    ∃ x y : V, x ∈ M ∧ y ∈ M ∧ y ∈ U ∧ bil Q x y = ξ := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨d, hd0, hdM⟩ := exists_smul_mem_of_mem_span (hL.le_span huU)
  have hdU : d • u ∈ U := by rw [← algebraMap_smul F d u]; exact U.smul_mem _ huU
  have hd0F : algebraMap R F d ≠ 0 := fun h => hd0 (IsFractionRing.injective R F (by rw [h, map_zero]))
  have hy0 : d • u ≠ 0 := by
    rw [← algebraMap_smul F d u]; exact smul_ne_zero hd0F hu0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = d • u := ⟨_, rfl⟩
  rw [← hy₁] at hdM hdU hy0
  let φ : V →ₗ[R] F := (QuadraticMap.associated Q y₁).restrictScalars R
  have hφ : ∀ v, φ v = bil Q y₁ v := fun v => rfl
  have hfg : (M.map φ).FG := hM.map φ
  have hne : M.map φ ≠ ⊥ := by
    intro h
    apply hy0
    refine hL.sd.regular y₁ hdM fun m' hm' => ?_
    have : φ m' ∈ M.map φ := Submodule.mem_map_of_mem hm'
    rw [h, mem_bot] at this
    exact this
  obtain ⟨β, hβ0, hβ⟩ := exists_eq_span_singleton hfg hne
  have hβmem : β ∈ M.map φ := hβ ▸ mem_span_singleton_self β
  obtain ⟨x, hxM, hxβ⟩ := Submodule.mem_map.mp hβmem
  have hbil : ∀ m ∈ M, ∃ r : R, bil Q y₁ m = algebraMap R F r * β := by
    intro m hm
    have : φ m ∈ M.map φ := Submodule.mem_map_of_mem hm
    rw [hβ] at this
    obtain ⟨r, hr⟩ := mem_span_singleton.mp this
    exact ⟨r, by rw [← hφ, ← hr, Algebra.smul_def]⟩
  have hyU : (ξ / β) • y₁ ∈ U := U.smul_mem _ hdU
  have hyM : (ξ / β) • y₁ ∈ M := by
    refine hL.sd.dual _ (smul_mem _ _ (subset_span hdM)) fun m hm => ?_
    obtain ⟨r, hr⟩ := hbil m hm
    rw [bil_smul_left, hr]
    exact mem_span_singleton.mpr ⟨r, by rw [Algebra.smul_def]; field_simp⟩
  refine ⟨x, (ξ / β) • y₁, hxM, hyM, hyU, ?_⟩
  rw [bil_comm, bil_smul_left, ← hφ, hxβ]
  field_simp

/-- A pair $x, y \in M$ with $B(x, y) = \xi$, $Q(y) = 0$ spans a $\xi\mathfrak o$-modular plane
$\cong \xi A(\alpha, 0)$ which splits $M$ (82:15, the use of 82:17 in O'Meara's proof of 93:14a). -/
theorem adj_split_plane {ξ : F} (hξ : ξ ≠ 0) {M : Submodule R V} (hsd : AdjSelfDual Q ξ M) {x y : V}
    (hxM : x ∈ M) (hyM : y ∈ M) (hxy : bil Q x y = ξ) (hQy : Q y = 0) :
    ∃ α : R, Q x = ξ * algebraMap R F α ∧ IsModular Q (R ∙ ξ) (span R {x, y}) ∧
      ∃ M' : Submodule R V, IsOrthSum Q M (span R {x, y}) M' := by
  obtain ⟨α, hα⟩ := mem_span_singleton.mp
    (by rw [← bil_self]; exact hsd.scale_le (bil_mem_scale Q hxM hxM) : Q x ∈ R ∙ ξ)
  have hQx : Q x = ξ * algebraMap R F α := by rw [← hα, Algebra.smul_def]; ring
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![α, 1; 1, 0]
  have hG : gram Q v = ξ • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hxy, hQy, bil_comm Q y x]
  have hU : IsUnit U.det := by simp [U, Matrix.det_fin_two_of]
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hξ hU hG
  have hv : Set.range v = {x, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv] at hmod
  have hJM : span R {x, y} ≤ M := by
    rw [span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hxM
    · exact hyM
  refine ⟨α, hQx, hmod, ?_⟩
  exact (splits_iff_of_isModular Q hJM hmod (fg_span (Set.toFinite _))).mpr
    (fun a ha b hb => hsd.scale_le (bil_mem_scale Q (hJM ha) hb))

/-- The self-dual-type properties pass to an orthogonal summand $M'$ of $M = J \perp M'$ with $J$ regular. -/
theorem adj_selfDual_complement {ξ : F} {M J M' : Submodule R V} (hsd : AdjSelfDual Q ξ M)
    (hs : IsOrthSum Q M J M') (hJ : IsRegular Q J) : AdjSelfDual Q ξ M' := by
  have hMM : M' ≤ M := hs.sup_eq ▸ le_sup_right
  refine ⟨(scale_mono Q hMM).trans hsd.scale_le, ?_, ?_⟩
  · intro m hm h0
    refine hsd.regular m (hMM hm) fun n hn => ?_
    rw [← hs.sup_eq] at hn
    obtain ⟨j, hj, m', hm', rfl⟩ := mem_sup.mp hn
    rw [bil_add_right, bil_comm Q m j, hs.orth j hj m hm, h0 m' hm', add_zero]
  · intro w hw hwd
    have hwJ : ∀ j ∈ J, bil Q w j = 0 := fun j hj =>
      adj_bil_span_left Q (fun t ht => by rw [bil_comm]; exact hs.orth j hj t ht) hw
    have hwM : w ∈ M := by
      refine hsd.dual w (span_mono (fun t ht => hMM ht) hw) fun n hn => ?_
      rw [← hs.sup_eq] at hn
      obtain ⟨j, hj, m', hm', rfl⟩ := mem_sup.mp hn
      rw [bil_add_right, hwJ j hj, zero_add]
      exact hwd m' hm'
    rw [← hs.sup_eq] at hwM
    obtain ⟨j, hj, m', hm', rfl⟩ := mem_sup.mp hwM
    have hj0 : j = 0 := hJ j hj fun j' hj' => by
      have := hwJ j' hj'
      rw [bil_add_left, bil_comm Q m' j', hs.orth j' hj' m' hm', add_zero] at this
      exact this
    rw [hj0, zero_add]; exact hm'

/-- **The inductive step of the hyperbolic decomposition**: splitting off the plane $J = \mathfrak ox + \mathfrak oy$
with $y \in U$ leaves the Lagrangian subspace $U' = U \cap x^\perp$ of $M'$, of dimension one less. -/
theorem adj_lagr_step {ξ : F} (hξ : ξ ≠ 0) {M J M' : Submodule R V} {U : Submodule F V} {x y : V}
    (hL : AdjLagr Q ξ M U) (hs : IsOrthSum Q M J M') (hJ : J = span R {x, y}) (hJreg : IsRegular Q J)
    (hyU : y ∈ U) (hxy : bil Q x y = ξ) (hQy : Q y = 0) [FiniteDimensional F U] :
    ∃ U' : Submodule F V, AdjLagr Q ξ M' U' ∧ finrank F U = finrank F U' + 1 := by
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  have hMM : M' ≤ M := hs.sup_eq ▸ le_sup_right
  have hperp : ∀ b ∈ span F (M' : Set V), bil Q b x = 0 ∧ bil Q b y = 0 := fun b hb =>
    ⟨adj_bil_span_left Q (fun t ht => by rw [bil_comm]; exact hs.orth x hxJ t ht) hb,
     adj_bil_span_left Q (fun t ht => by rw [bil_comm]; exact hs.orth y hyJ t ht) hb⟩
  let ψ : V →ₗ[F] F := QuadraticMap.associated Q x
  let U' : Submodule F V := U ⊓ LinearMap.ker ψ
  have hmemU' : ∀ u, u ∈ U' ↔ u ∈ U ∧ bil Q x u = 0 := fun u => by
    simp only [U', Submodule.mem_inf, LinearMap.mem_ker]; rfl
  have hproj : ∀ u ∈ U, u - (bil Q x u / ξ) • y ∈ U' := by
    intro u hu
    rw [hmemU']
    refine ⟨U.sub_mem hu (U.smul_mem _ hyU), ?_⟩
    rw [bil_sub_right, bil_smul_right, hxy, div_mul_cancel₀ _ hξ, sub_self]
  have hU'le : U' ≤ U := inf_le_left
  refine ⟨U', ⟨adj_selfDual_complement Q hL.sd hs hJreg,
    fun u hu u' hu' => hL.iso u ((hmemU' u).mp hu).1 u' ((hmemU' u').mp hu').1, ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨huU, hxu⟩ := (hmemU' u).mp hu
    have huW := hL.le_span huU
    have hsub : span F (M : Set V) ≤ span F {x, y} ⊔ span F (M' : Set V) := by
      rw [span_le]
      intro m hm
      have hm' : m ∈ J ⊔ M' := hs.sup_eq ▸ hm
      obtain ⟨j, hj, m', hm'', rfl⟩ := mem_sup.mp hm'
      refine add_mem (mem_sup_left ?_) (mem_sup_right (subset_span hm''))
      rw [hJ] at hj
      exact Submodule.span_subset_span R F _ hj
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp (hsub huW)
    obtain ⟨c₁, c₂, rfl⟩ := mem_span_pair.mp ha
    have hby : bil Q y b = 0 := by rw [bil_comm]; exact (hperp b hb).2
    have hbx : bil Q x b = 0 := by rw [bil_comm]; exact (hperp b hb).1
    have hyu := hL.iso y hyU _ huU
    rw [bil_add_right, bil_add_right, bil_smul_right, bil_smul_right, bil_comm Q y x, hxy, bil_self,
      hQy, hby] at hyu
    have hc₁ : c₁ = 0 := by
      have : c₁ * ξ = 0 := by linear_combination hyu
      exact (mul_eq_zero.mp this).resolve_right hξ
    subst hc₁
    rw [zero_smul, zero_add, bil_add_right, bil_smul_right, hxy, hbx] at hxu
    have hc₂ : c₂ = 0 := by
      have : c₂ * ξ = 0 := by linear_combination hxu
      exact (mul_eq_zero.mp this).resolve_right hξ
    subst hc₂
    simpa using hb
  · intro w hw hwd
    obtain ⟨hwx, hwy⟩ := hperp w hw
    have hwW : w ∈ span F (M : Set V) := span_mono (fun t ht => hMM ht) hw
    have hwU : ∀ u ∈ U, bil Q w u = 0 := by
      intro u hu
      have h1 := hwd _ (hproj u hu)
      rw [bil_sub_right, bil_smul_right, hwy, mul_zero, sub_zero] at h1
      exact h1
    rw [hmemU']
    exact ⟨hL.max w hwW hwU, by rw [bil_comm]; exact hwx⟩
  · have hy0 : y ≠ 0 := by
      rintro rfl
      apply hξ
      rw [← hxy]
      simp [bil]
    have : FiniteDimensional F U' := Submodule.finiteDimensional_of_le hU'le
    have hsup : U' ⊔ F ∙ y = U := by
      apply le_antisymm
      · exact sup_le hU'le ((Submodule.span_singleton_le_iff_mem y U).mpr hyU)
      · intro u hu
        have : u = (u - (bil Q x u / ξ) • y) + (bil Q x u / ξ) • y := by abel
        rw [this]
        exact add_mem (mem_sup_left (hproj u hu))
          (mem_sup_right (smul_mem _ _ (mem_span_singleton_self y)))
    have hinf : U' ⊓ F ∙ y = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv1, hv2⟩
      obtain ⟨a, rfl⟩ := mem_span_singleton.mp hv2
      have h1 := ((hmemU' _).mp hv1).2
      rw [bil_smul_right, hxy] at h1
      have : a = 0 := (mul_eq_zero.mp h1).resolve_right hξ
      simp [this]
    have h := Submodule.finrank_sup_add_finrank_inf_eq U' (F ∙ y)
    rw [hsup, hinf, finrank_bot, finrank_span_singleton hy0] at h
    omega

/-- **Hyperbolic decomposition of a modular lattice with a Lagrangian subspace** (O'Meara 1963, §93C, p. 257, the
decomposition $\langle\xi A(\alpha_1, 0)\rangle \perp \cdots \perp \langle\xi A(\alpha_r, 0)\rangle$ from 82:17):
a finitely generated lattice $M$ of self-dual type ($\xi\mathfrak o$-modular) with a Lagrangian subspace $U$ of
dimension $n$ is an orthogonal sum of $n$ planes $\xi A(\alpha_i, 0)$ with $Q(x_i) = \xi\alpha_i \in S$ whenever
$Q(M) \subseteq S$. -/
theorem adj_exists_planeSum {ξ : F} (hξ : ξ ≠ 0) (S : Set F) (n : ℕ) :
    ∀ {M : Submodule R V} {U : Submodule F V}, M.FG → AdjLagr Q ξ M U → finrank F U = n →
      (∀ m ∈ M, Q m ∈ S) → AdjPlaneSum Q ξ S n M := by
  induction n with
  | zero =>
    intro M U hM hL hn hS
    have := adj_finiteDimensional_span (F := F) hM
    have : FiniteDimensional F U := Submodule.finiteDimensional_of_le hL.le_span
    have hU : U = ⊥ := Submodule.finrank_eq_zero.mp hn
    simp only [AdjPlaneSum]
    rw [eq_bot_iff]
    intro m hm
    have : m ∈ U := hL.max m (subset_span hm) (fun u hu => by
      rw [hU, mem_bot] at hu; simp [hu, bil])
    rw [hU] at this
    exact this
  | succ n ih =>
    intro M U hM hL hn hS
    have := adj_finiteDimensional_span (F := F) hM
    have : FiniteDimensional F U := Submodule.finiteDimensional_of_le hL.le_span
    have hU : U ≠ ⊥ := by
      rintro rfl
      simp at hn
    obtain ⟨x, y, hxM, hyM, hyU, hxy⟩ := adj_exists_pair Q hM hL hU
    have hQy : Q y = 0 := by rw [← bil_self]; exact hL.iso y hyU y hyU
    obtain ⟨α, hQx, hmod, M', hs⟩ := adj_split_plane Q hξ hL.sd hxM hyM hxy hQy
    have hreg := hmod.isRegular Q (fg_span (Set.toFinite _))
    obtain ⟨U', hL', hdim⟩ := adj_lagr_step Q hξ hL hs rfl hreg hyU hxy hQy
    have hMM : M' ≤ M := hs.sup_eq ▸ le_sup_right
    exact ⟨span R {x, y}, M', hs, ⟨x, y, rfl, hxy, hQy, hS x hxM,
      mem_span_singleton.mpr ⟨α, by rw [hQx, Algebra.smul_def]; ring⟩⟩,
      ih (Submodule.FG.of_le hM hMM) hL' (by omega) (fun m hm => hS m (hMM hm))⟩

/-- A vector of $FJ$ orthogonal to $J$ is $0$ when $J$ is regular. -/
theorem adj_span_regular {J : Submodule R V} (hreg : IsRegular Q J) {v : V} (hv : v ∈ span F (J : Set V))
    (h : ∀ m ∈ J, bil Q v m = 0) : v = 0 := by
  obtain ⟨d, hd0, hdJ⟩ := exists_smul_mem_of_mem_span hv
  have hd0F : algebraMap R F d ≠ 0 := fun h => hd0 (IsFractionRing.injective R F (by rw [h, map_zero]))
  have : d • v = 0 := hreg _ hdJ fun m hm => by
    rw [← algebraMap_smul F d v, bil_smul_left, h m hm, mul_zero]
  rw [← algebraMap_smul F d v] at this
  exact (smul_eq_zero.mp this).resolve_left hd0F

/-- **A finitely generated $\xi\mathfrak o$-modular lattice is of self-dual type** (`AdjSelfDual`; 82:13, 82:14a). -/
theorem adj_selfDual_of_isModular {ξ : F} {J : Submodule R V} (hJ : J.FG) (hmod : IsModular Q (R ∙ ξ) J) :
    AdjSelfDual Q ξ J := by
  have hreg := hmod.isRegular Q hJ
  refine ⟨hmod.2.1.le, hreg, ?_⟩
  intro w hw hwd
  obtain ⟨α, hα, hαξ, b, U, hU, hG⟩ := exists_gram_of_isModular Q hmod hJ
  obtain ⟨y, hyJ, hy⟩ := exists_mem_bil_eq_of_gram Q b hU hG (x := w) fun j => by
    rw [← hαξ]; exact hwd _ (b j).2
  have hsub : w - y ∈ span F (J : Set V) := sub_mem hw (subset_span hyJ)
  have : w - y = 0 := adj_span_regular Q hreg hsub fun m hm => by
    rw [bil_sub_left, ← hy m hm, sub_self]
  rw [sub_eq_zero.mp this]
  exact hyJ

/-- Self-dual type for the negative form. -/
theorem adj_selfDual_neg {ξ : F} {J : Submodule R V} (h : AdjSelfDual Q ξ J) : AdjSelfDual (-Q) ξ J := by
  refine ⟨?_, fun m hm h0 => h.regular m hm fun m' hm' => ?_, fun w hw hwd => h.dual w hw fun m hm => ?_⟩
  · rw [scale, span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    show bil (-Q) a b ∈ R ∙ ξ
    rw [adj_bil_neg]
    exact neg_mem (h.scale_le (bil_mem_scale Q ha hb))
  · have := h0 m' hm'
    rw [adj_bil_neg] at this
    exact neg_eq_zero.mp this
  · have := hwd m hm
    rw [adj_bil_neg] at this
    exact neg_mem_iff.mp this

variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q' : QuadraticForm F V')

/-- The two coordinates of a vector of $F(A \times B)$ lie in $FA$ and $FB$. -/
theorem adj_mem_span_prod {A : Submodule R V} {B : Submodule R V'} {w : V × V'}
    (hw : w ∈ span F ((A.prod B : Submodule R (V × V')) : Set (V × V'))) :
    w.1 ∈ span F (A : Set V) ∧ w.2 ∈ span F (B : Set V') := by
  refine span_induction (p := fun w _ => w.1 ∈ span F (A : Set V) ∧ w.2 ∈ span F (B : Set V'))
    (fun w hw => ⟨subset_span hw.1, subset_span hw.2⟩) ⟨zero_mem _, zero_mem _⟩
    (fun a b _ _ ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩)
    (fun c a _ ha => ⟨smul_mem _ _ ha.1, smul_mem _ _ ha.2⟩) hw

/-- $(v, 0) \in F(A \times B)$ for $v \in FA$. -/
theorem adj_mk_zero_mem_span {A : Submodule R V} {B : Submodule R V'} {v : V}
    (hv : v ∈ span F (A : Set V)) : (v, (0 : V')) ∈ span F ((A.prod B : Submodule R (V × V')) : Set (V × V')) :=
  span_induction (p := fun v _ => (v, (0 : V')) ∈ span F ((A.prod B : Submodule R (V × V')) : Set (V × V')))
    (fun a ha => subset_span ⟨ha, zero_mem _⟩) (zero_mem _)
    (fun a b _ _ ha hb => by simpa using add_mem ha hb)
    (fun c a _ ha => by simpa using smul_mem _ c ha) hv

/-- $(0, v) \in F(A \times B)$ for $v \in FB$. -/
theorem adj_zero_mk_mem_span {A : Submodule R V} {B : Submodule R V'} {v : V'}
    (hv : v ∈ span F (B : Set V')) : ((0 : V), v) ∈ span F ((A.prod B : Submodule R (V × V')) : Set (V × V')) :=
  span_induction (p := fun v _ => ((0 : V), v) ∈ span F ((A.prod B : Submodule R (V × V')) : Set (V × V')))
    (fun a ha => subset_span ⟨zero_mem _, ha⟩) (zero_mem _)
    (fun a b _ _ ha hb => by simpa using add_mem ha hb)
    (fun c a _ ha => by simpa using smul_mem _ c ha) hv

/-- Self-dual type is preserved by orthogonal sums of spaces. -/
theorem adj_selfDual_prod {ξ : F} {A : Submodule R V} {B : Submodule R V'} (hA : AdjSelfDual Q ξ A)
    (hB : AdjSelfDual Q' ξ B) : AdjSelfDual (Q.prod Q') ξ (A.prod B) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scale, span_le]
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, ⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩
    show bil (Q.prod Q') (a, b) (a', b') ∈ R ∙ ξ
    rw [adj_bil_prod]
    exact add_mem (hA.scale_le (bil_mem_scale Q ha ha')) (hB.scale_le (bil_mem_scale Q' hb hb'))
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ h0
    have h1 : a = 0 := hA.regular a ha fun a' ha' => by
      have := h0 (a', 0) ⟨ha', zero_mem _⟩
      rw [adj_bil_prod] at this
      simpa [bil] using this
    have h2 : b = 0 := hB.regular b hb fun b' hb' => by
      have := h0 (0, b') ⟨zero_mem _, hb'⟩
      rw [adj_bil_prod] at this
      simpa [bil] using this
    simp [h1, h2]
  · intro w hw hwd
    obtain ⟨hw1, hw2⟩ := adj_mem_span_prod hw
    refine ⟨hA.dual _ hw1 fun a' ha' => ?_, hB.dual _ hw2 fun b' hb' => ?_⟩
    · have := hwd (a', 0) ⟨ha', zero_mem _⟩
      rw [adj_bil_prod] at this
      simpa [bil] using this
    · have := hwd (0, b') ⟨zero_mem _, hb'⟩
      rw [adj_bil_prod] at this
      simpa [bil] using this

end Lagrangian

section Diagonal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The diagonal Lagrangian of $A \perp B^{-}$** (O'Meara 1963, §93C, p. 257, the hyperbolic space $V \perp V^{-}$):
if $A, B$ are lattices of self-dual type ($\xi\mathfrak o$-modular) with $FA = FB$, then the diagonal
$\{(v, v) : v \in FA\}$ is a Lagrangian subspace of $A \times B$ for the form $Q \perp -Q$. -/
theorem adj_lagr_diag {ξ : F} {A B : Submodule R V} (hA : AdjSelfDual Q ξ A) (hB : AdjSelfDual Q ξ B)
    (hspan : span F (A : Set V) = span F (B : Set V)) :
    AdjLagr (Q.prod (-Q)) ξ (A.prod B)
      (Submodule.map (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[F] V × V) (span F (A : Set V))) := by
  refine ⟨adj_selfDual_prod Q (-Q) hA (adj_selfDual_neg Q hB), ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    show bil (Q.prod (-Q)) (v, v) (v', v') = 0
    rw [adj_bil_prod, adj_bil_neg]; ring
  · rintro _ ⟨v, hv, rfl⟩
    have h1 := adj_mk_zero_mem_span (F := F) (B := B) hv
    have h2 := adj_zero_mk_mem_span (F := F) (A := A) (hspan ▸ hv)
    have := add_mem h1 h2
    simpa using this
  · intro w hw hwd
    obtain ⟨hw1, hw2⟩ := adj_mem_span_prod hw
    have hw2' : w.2 ∈ span F (A : Set V) := hspan ▸ hw2
    have hz : w.1 - w.2 = 0 := by
      refine adj_span_regular Q hA.regular (sub_mem hw1 hw2') fun m hm => ?_
      have := hwd (m, m) ⟨m, subset_span hm, rfl⟩
      rw [adj_bil_prod, adj_bil_neg] at this
      rw [bil_sub_left]
      linear_combination this
    refine ⟨w.1, hw1, ?_⟩
    ext
    · rfl
    · simp [sub_eq_zero.mp hz]

/-- **Hyperbolic decomposition of $A \perp B^{-}$** (O'Meara 1963, §93C, p. 257): for finitely generated lattices
$A, B$ of self-dual type with $FA = FB$, the lattice $A \times B$ with the form $Q \perp -Q$ is an orthogonal sum
of $\dim FA$ planes $\xi A(\alpha_i, 0)$, with $\xi\alpha_i \in S$ whenever $Q(a) - Q(b) \in S$ for all
$a \in A$, $b \in B$. -/
theorem adj_planeSum_prod {ξ : F} (hξ : ξ ≠ 0) {A B : Submodule R V} (hAfg : A.FG) (hBfg : B.FG)
    (hA : AdjSelfDual Q ξ A) (hB : AdjSelfDual Q ξ B) (hspan : span F (A : Set V) = span F (B : Set V))
    (S : Set F) (hS : ∀ a ∈ A, ∀ b ∈ B, Q a - Q b ∈ S) :
    AdjPlaneSum (Q.prod (-Q)) ξ S (finrank F (span F (A : Set V))) (A.prod B) := by
  have hinj : Function.Injective (LinearMap.prod LinearMap.id LinearMap.id : V →ₗ[F] V × V) :=
    fun a b h => congrArg Prod.fst h
  refine adj_exists_planeSum (Q.prod (-Q)) hξ S _ (hAfg.prod hBfg) (adj_lagr_diag Q hA hB hspan) ?_ ?_
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (span F (A : Set V)))).symm
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := hS a ha b hb
    simpa [QuadraticMap.prod_apply, sub_eq_add_neg] using this

end Diagonal

section Cancel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Corollary 93:14a** (O'Meara 1963, §93C, pp. 257–258): a lattice $L$ on a quadratic space has splittings
$L = J \perp K$ and $L = J_1 \perp K_1$ with $J \cong J_1$. Suppose that $J$ is $\mathfrak a$-modular with
$\mathfrak gJ \subseteq \mathfrak g K^{\mathfrak a}$ and $\mathfrak gJ_1 \subseteq \mathfrak g K_1^{\mathfrak a}$. Then
$K \cong K_1$.

Here $\mathfrak a$ is a non-zero finitely generated $R$-submodule of $F$ (a fractional ideal; `a.FG`, `IsModular`
already contains `a ≠ ⊥`), and $\mathfrak gK^{\mathfrak a}$ is `normGroup Q (subA Q a K)`. As in O'Meara's proof, the
adjunction of $J^{-1}$ (the lattice $J$ with the form $-Q$) is realized in $V \times V$ with the form
$Q \perp -Q$ and the lattice $L \times J$; no dyadic hypothesis is needed (O'Meara's statement is for a dyadic local
field; the argument uses only the discrete valuation ring). -/
@[kb "omeara1963" "§93C, 93:14a, pp. 257–258"]
theorem isometricLat_of_cancel_modular {L J K J₁ K₁ : Submodule R V} (hL : L.FG)
    (h : IsOrthSum Q L J K) (h₁ : IsOrthSum Q L J₁ K₁) (hJJ : IsometricLat Q Q J J₁)
    {a : Submodule R F} (ha : a.FG) (hmod : IsModular Q a J)
    (hg : normGroup Q J ≤ normGroup Q (subA Q a K))
    (hg₁ : normGroup Q J₁ ≤ normGroup Q (subA Q a K₁)) : IsometricLat Q Q K K₁ := by
  obtain ⟨ξ, hξ, rfl⟩ := exists_eq_span_singleton ha hmod.1
  have hJfg : J.FG := Submodule.FG.of_le hL (h.sup_eq ▸ le_sup_left)
  have hsd : AdjSelfDual Q ξ J := adj_selfDual_of_isModular Q hJfg hmod
  set Q2 : QuadraticForm F (V × V) := Q.prod (-Q) with hQ2
  set S : Set F := (normGroup Q J : Set F) with hS
  have hSv : ∀ a ∈ J, ∀ b ∈ J, Q a - Q b ∈ S := fun a ha b hb =>
    sub_mem (Q_mem_normGroup Q ha) (Q_mem_normGroup Q hb)
  have hP : AdjPlaneSum Q2 ξ S (finrank F (span F (J : Set V))) (J.prod J) :=
    adj_planeSum_prod Q hξ hJfg hJfg hsd hsd rfl S hSv
  have hP₁ : AdjPlaneSum Q2 ξ S (finrank F (span F (J : Set V))) (J₁.prod J) :=
    adj_planeSum_of_isometric Q2 Q2 _
      (adj_isometricLat_prod Q (-Q) Q (-Q) hJJ (adj_isometricLat_refl (-Q) J)) hP
  have hM1 : IsOrthSum Q2 (L.prod J) (J.prod J) (K.prod ⊥) := adj_isOrthSum_prod_left Q (-Q) h J
  have hM2 : IsOrthSum Q2 (L.prod J) (J₁.prod J) (K₁.prod ⊥) := adj_isOrthSum_prod_left Q (-Q) h₁ J
  have hSK : ∀ s ∈ S, s ∈ normGroup Q2 (subA Q2 (R ∙ ξ) (K.prod ⊥)) := fun s hs =>
    adj_normGroup_subA_prod_bot_le Q (-Q) (R ∙ ξ) K (hg hs)
  have hSK₁ : ∀ s ∈ S, s ∈ normGroup Q2 (subA Q2 (R ∙ ξ) (K₁.prod ⊥)) := fun s hs =>
    adj_normGroup_subA_prod_bot_le Q (-Q) (R ∙ ξ) K₁
      (hg₁ ((adj_normGroup_eq Q Q hJJ).le hs))
  obtain ⟨H, K', hHK, hHpl, hKK'⟩ :=
    adj_planeSum_iter Q2 hξ S _ hP hM1 (adj_isometricLat_refl Q2 (L.prod J)) hSK
  obtain ⟨H₁, K₁', hHK₁, hHpl₁, hKK₁'⟩ :=
    adj_planeSum_iter Q2 hξ S _ hP₁ hM2 (adj_isometricLat_refl Q2 (L.prod J)) hSK₁
  have hmid := adj_planeSum_cancel Q2 hξ _ (adj_isometricLat_refl Q2 (L.prod J)) hHK hHK₁ hHpl hHpl₁
  exact adj_isometricLat_trans Q Q2 Q (adj_isometricLat_prod_bot Q (-Q) K)
    (adj_isometricLat_trans Q2 Q2 Q (adj_isometricLat_trans Q2 Q2 Q2 hKK' hmid |> fun e =>
      adj_isometricLat_trans Q2 Q2 Q2 e (adj_isometricLat_symm Q2 Q2 hKK₁'))
      (adj_isometricLat_symm Q Q2 (adj_isometricLat_prod_bot Q (-Q) K₁)))

/-- A lattice lies in $L^{\mathfrak a}$ when its scale is contained in $\mathfrak a$. -/
theorem adj_le_subA {a : Submodule R F} {L : Submodule R V} (hsc : scale Q L ≤ a) : L ≤ subA Q a L :=
  fun _ hl => ⟨hl, fun _ hl' => hsc (bil_mem_scale Q hl hl')⟩

/-- **Isometry of unimodular lattices with the same norm group** (the substance of O'Meara's 93:16): unimodular
lattices $L, K$ on the same quadratic space with $\mathfrak gL = \mathfrak gK$ are isometric. -/
theorem isometricLat_of_normGroup_eq {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    (hL : IsUnimodular Q L) (hK : IsUnimodular Q K) (hg : normGroup Q L = normGroup Q K) :
    IsometricLat Q Q L K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F) (M := L)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F) (M := K)
  have hL' : IsModular Q (R ∙ (1 : F)) L := by rw [← Submodule.one_eq_span]; exact hL
  have hK' : IsModular Q (R ∙ (1 : F)) K := by rw [← Submodule.one_eq_span]; exact hK
  have sdL : AdjSelfDual Q (1 : F) L := adj_selfDual_of_isModular Q hLfg hL'
  have sdK : AdjSelfDual Q (1 : F) K := adj_selfDual_of_isModular Q hKfg hK'
  have hspan : span F (K : Set V) = span F (L : Set V) := by
    rw [Submodule.IsLattice.span_eq_top (A := F) (M := L), Submodule.IsLattice.span_eq_top (A := F) (M := K)]
  set Q2 : QuadraticForm F (V × V) := Q.prod (-Q) with hQ2
  set Q3 : QuadraticForm F (V × (V × V)) := Q.prod Q2 with hQ3
  set S : Set F := (normGroup Q L : Set F) with hS
  set r : ℕ := finrank F (span F (L : Set V)) with hr
  -- the hyperbolic lattices `K ⊥ L⁻` and `L ⊥ L⁻`
  have hY : AdjPlaneSum Q2 (1 : F) S r (K.prod L) := by
    have := adj_planeSum_prod Q one_ne_zero hKfg hLfg sdK sdL hspan S (fun k hk l hl =>
      sub_mem (hg ▸ Q_mem_normGroup Q hk) (Q_mem_normGroup Q hl))
    rwa [hspan] at this
  have hY' : AdjPlaneSum Q2 (1 : F) S r (L.prod L) :=
    adj_planeSum_prod Q one_ne_zero hLfg hLfg sdL sdL rfl S (fun k hk l hl =>
      sub_mem (Q_mem_normGroup Q hk) (Q_mem_normGroup Q hl))
  have hone : (R ∙ (1 : F)) = 1 := (Submodule.one_eq_span).symm
  -- the splitting `L ⊥ (K ⊥ L⁻) = (K⊥L⁻) ⊥ L`
  have hD1 : IsOrthSum Q3 (L.prod (K.prod L)) ((⊥ : Submodule R V).prod (K.prod L)) (L.prod ⊥) :=
    adj_isOrthSum_symm Q3 (adj_isOrthSum_prod_split Q Q2 L (K.prod L))
  have hH1 : AdjPlaneSum Q3 (1 : F) S r ((⊥ : Submodule R V).prod (K.prod L)) :=
    adj_planeSum_of_isometric Q2 Q3 r (adj_isometricLat_bot_prod Q Q2 (K.prod L)) hY
  have hS1 : ∀ s ∈ S, s ∈ normGroup Q3 (subA Q3 (R ∙ (1 : F)) (L.prod ⊥)) := fun s hs =>
    adj_normGroup_subA_prod_bot_le Q Q2 (R ∙ (1 : F)) L
      (normGroup_mono Q (adj_le_subA Q (by rw [hL'.2.1])) hs)
  obtain ⟨H1, K1, hH1K1, hpl1, hLK1⟩ :=
    adj_planeSum_iter Q3 one_ne_zero S r hH1 hD1 (adj_isometricLat_refl Q3 _) hS1
  -- the splitting `L ⊥ (K ⊥ L⁻) = (L ⊥ L⁻) ⊥ K`
  have hD2 : IsOrthSum Q3 (L.prod (K.prod L)) (L.prod ((⊥ : Submodule R V).prod L))
      ((⊥ : Submodule R V).prod (K.prod ⊥)) :=
    adj_isOrthSum_prod_right Q Q2 L (adj_isOrthSum_symm Q2 (adj_isOrthSum_prod_split Q (-Q) K L))
  have hH2 : AdjPlaneSum Q3 (1 : F) S r (L.prod ((⊥ : Submodule R V).prod L)) :=
    adj_planeSum_of_isometric (Q.prod (-Q)) Q3 r
      (adj_isometricLat_prod Q (-Q) Q Q2 (adj_isometricLat_refl Q L)
        (adj_isometricLat_bot_prod Q (-Q) L)) hY'
  have hS2 : ∀ s ∈ S, s ∈ normGroup Q3 (subA Q3 (R ∙ (1 : F)) ((⊥ : Submodule R V).prod (K.prod ⊥))) :=
    fun s hs => adj_normGroup_subA_bot_prod_le Q Q2 (R ∙ (1 : F)) (K.prod ⊥)
      (adj_normGroup_subA_prod_bot_le Q (-Q) (R ∙ (1 : F)) K
        (normGroup_mono Q (adj_le_subA Q (by rw [hK'.2.1])) (hg ▸ hs)))
  obtain ⟨H2, K2, hH2K2, hpl2, hKK2⟩ :=
    adj_planeSum_iter Q3 one_ne_zero S r hH2 hD2 (adj_isometricLat_refl Q3 _) hS2
  have hmid := adj_planeSum_cancel Q3 one_ne_zero r (adj_isometricLat_refl Q3 _) hH1K1 hH2K2 hpl1 hpl2
  have hKe : IsometricLat Q Q3 K ((⊥ : Submodule R V).prod (K.prod ⊥)) :=
    adj_isometricLat_trans Q Q2 Q3 (adj_isometricLat_prod_bot Q (-Q) K)
      (adj_isometricLat_bot_prod Q Q2 (K.prod ⊥))
  exact adj_isometricLat_trans Q Q3 Q (adj_isometricLat_prod_bot Q Q2 L)
    (adj_isometricLat_trans Q3 Q3 Q
      (adj_isometricLat_trans Q3 Q3 Q3 hLK1
        (adj_isometricLat_trans Q3 Q3 Q3 hmid (adj_isometricLat_symm Q3 Q3 hKK2)))
      (adj_isometricLat_symm Q Q3 hKe))

/-- **Theorem 93:16** (O'Meara 1963, §93D, p. 259): let $L$ and $K$ be unimodular lattices on the same quadratic
space over a dyadic local field. Then $\operatorname{cls} L = \operatorname{cls} K$ if and only if
$\mathfrak gL = \mathfrak gK$.

No dyadic hypothesis is used (the argument is O'Meara's: adjoin $L^{-1} \perp L$, use the hyperbolic decomposition,
93:13 and 93:14a; the unimodular lattices are lattices on the same space $V$ by `[L.IsLattice F]`,
`[K.IsLattice F]`). -/
@[kb "omeara1963" "§93D, 93:16, p. 259"]
theorem cls_eq_iff_normGroup_eq {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    (hL : IsUnimodular Q L) (hK : IsUnimodular Q K) :
    cls Q L = cls Q K ↔ normGroup Q L = normGroup Q K := by
  constructor
  · intro h
    have hKK : K ∈ cls Q K := mem_cls_self Q K
    rw [← h] at hKK
    obtain ⟨σ, hσ, hKσ⟩ := hKK
    have := isometricLat_latMap Q hσ L
    rw [← hKσ] at this
    exact adj_normGroup_eq Q Q this
  · intro hg
    have hiso := isometricLat_of_normGroup_eq Q hL hK hg
    exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q hiso)).symm

/-- **Footnote to 93:16** (O'Meara 1963, §93D, p. 259): for unimodular lattices $L, K$ on the same space with
$Q(L) = \mathfrak gL$ and $Q(K) = \mathfrak gK$ (e.g. each contains a sublattice $\cong A(0,0)$, see
`normGroup_eq_image`), $\operatorname{cls} L = \operatorname{cls} K$ if and only if $Q(L) = Q(K)$. -/
@[kb "omeara1963" "§93D, 93:16, p. 259, footnote (cls L = cls K iff Q(L) = Q(K))"]
theorem cls_eq_iff_image_eq {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    (hL : IsUnimodular Q L) (hK : IsUnimodular Q K)
    (hLq : Q '' (L : Set V) = (normGroup Q L : Set F)) (hKq : Q '' (K : Set V) = (normGroup Q K : Set F)) :
    cls Q L = cls Q K ↔ Q '' (L : Set V) = Q '' (K : Set V) := by
  rw [cls_eq_iff_normGroup_eq Q hL hK, hLq, hKq]
  exact SetLike.coe_set_eq.symm

/-- **Footnote to 93:16, hyperbolic form** (O'Meara 1963, §93D, p. 259): for unimodular lattices $L, K$ on the same
space each containing a sublattice $\cong A(0,0)$ (vectors $x, y$ with $Q(x) = Q(y) = 0$, $B(x, y) = 1$),
$\operatorname{cls} L = \operatorname{cls} K$ if and only if $Q(L) = Q(K)$ (using `normGroup_eq_image`). -/
@[kb "omeara1963" "§93D, 93:16, p. 259, footnote (cls L = cls K iff Q(L) = Q(K), A(0,0) ⊆ L, K)"]
theorem cls_eq_iff_image_eq_of_hyperbolic {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    (hL : IsUnimodular Q L) (hK : IsUnimodular Q K)
    (hLh : ∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1)
    (hKh : ∃ x ∈ K, ∃ y ∈ K, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1) :
    cls Q L = cls Q K ↔ Q '' (L : Set V) = Q '' (K : Set V) := by
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := hLh
  obtain ⟨x', hx', y', hy', h1', h2', h3'⟩ := hKh
  exact cls_eq_iff_image_eq Q hL hK (normGroup_eq_image Q L hL.2.1 hx hy h1 h2 h3).symm
    (normGroup_eq_image Q K hK.2.1 hx' hy' h1' h2' h3').symm

end Cancel

end QuadFormsKB.OMeara
