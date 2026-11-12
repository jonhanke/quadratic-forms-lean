/-
# Quaternion algebras over a number field are determined by their ramification (Voight, Main Theorem 14.6.1)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Main Theorem 14.6.1 (p. 231) and
Theorem 5.1.1 (key `voight2021`).

**Statement.** Let $F$ be a number field and $a, b, a', b' \in F^\times$. Then
$$(a, b \mid F) \cong (a', b' \mid F) \iff (a, b)_v = (a', b')_v \text{ for every place } v \text{ of } F
\iff \operatorname{Ram}(a, b \mid F) = \operatorname{Ram}(a', b' \mid F)$$
(`nonempty_algEquiv_iff_hilbert_eq`, `nonempty_algEquiv_iff_ram_eq`), with $(\cdot,\cdot)_v$ the local Hilbert
symbol (`NFPlace.hilbert`) and $\operatorname{Ram}$ the set of places (finite and infinite) at which the algebra is
a division algebra (`Quat.IsRamifiedAt`). This is the injectivity half of Main Theorem 14.6.1 (the map
$B \mapsto \operatorname{Ram} B$ is injective on isomorphism classes); the other halves are that $\operatorname{Ram} B$
is finite of even cardinality (Hilbert reciprocity, already proved in this repository as
`Quat.ramified_finite_even`) and that every finite set of noncomplex places of even cardinality occurs (stated
below as `RamificationSurjective`, not proved here). In particular (the local–global principle)
$(a, b \mid F) \cong \mathrm{M}_2(F)$ iff it is split at every place (`nonempty_algEquiv_one_iff`).

**Proof.** Everything comes from the quadratic-form theory of this repository:
* (Theorem 5.1.1, `PureForm.nonempty_algEquiv_iff_isometricIn`) $(a,b \mid F) \cong (a',b' \mid F)$ iff the pure
  norm forms $\langle -a, -b, ab\rangle$ and $\langle -a', -b', a'b'\rangle$ are isometric over $F$;
* (Hasse–Minkowski for isometry, `FormClassNF.isometricIn_of_everywhere_nf`) iff they are isometric over every
  completion $F_v$;
* (the classification over $F_v$, `NFPlace.isometric_iff`: discriminant, Hasse invariant, negative index) iff,
  at every $v$, the Hasse invariants agree and, at real $v$, the negative indices agree. The discriminant of
  $\langle -a,-b,ab\rangle$ is a square; its Hasse invariant is $\varepsilon_v = (-1,-1)_v\,(a,b)_v$
  (`hasseSerre_pure`); at a real place its negative index is $0$ if $\sigma(a), \sigma(b) < 0$ and $2$ otherwise,
  while $(a,b)_v = -1$ exactly when $\sigma(a), \sigma(b) < 0$.
-/
import QuadFormsKB.Literature.Voight.PureForm
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationGeneralNF
import QuadFormsKB.Binary.RelGenusHilbert

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField Quaternion

namespace QuadFormsKB.Voight

open QuadFormsKB.Quat

namespace LocalGlobal

variable {F : Type} [Field F] [NumberField F]

theorem hilbert_comm (v : NFPlace F) (x y : F) : v.hilbert x y = v.hilbert y x := by
  cases v <;> exact hilbertSymbol_comm _ _ _

theorem hilbert_self_neg (v : NFPlace F) (x : F) : v.hilbert x (-x) = 1 := by
  cases v <;> simp only [NFPlace.hilbert, map_neg] <;> exact hilbertSymbol_self_neg _ _

/-- **The Hasse invariant of the pure norm form**: $\varepsilon_v\langle -a, -b, ab\rangle = (-1,-1)_v\,(a,b)_v$. -/
theorem hasseSerre_pure (v : NFPlace F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    v.hasseSerre ![-a, -b, a * b] = v.hilbert (-1) (-1) * v.hilbert a b := by
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  have hnb : -b ≠ 0 := neg_ne_zero.2 hb
  have h1 : (-1 : F) ≠ 0 := by norm_num
  have m1 : v.hilbert (-a) (a * b) = v.hilbert (-a) a * v.hilbert (-a) b :=
    NFPlace.hilbert_mul_right v hna ha hb
  have m2 : v.hilbert (-b) (a * b) = v.hilbert (-b) a * v.hilbert (-b) b :=
    NFPlace.hilbert_mul_right v hnb ha hb
  have s1 : v.hilbert (-a) a = 1 := by rw [hilbert_comm]; exact hilbert_self_neg v a
  have s2 : v.hilbert (-b) b = 1 := by rw [hilbert_comm]; exact hilbert_self_neg v b
  have m3 : v.hilbert (-a) (-b) = v.hilbert (-a) (-1) * v.hilbert (-a) b := by
    rw [show -b = -1 * b by ring]; exact NFPlace.hilbert_mul_right v hna h1 hb
  have m4 : v.hilbert (-b) a = v.hilbert a (-1) * v.hilbert a b := by
    rw [hilbert_comm, show -b = -1 * b by ring]; exact NFPlace.hilbert_mul_right v ha h1 hb
  have m5 : v.hilbert (-a) (-1) = v.hilbert (-1) (-1) * v.hilbert a (-1) := by
    rw [hilbert_comm, show -a = -1 * a by ring, NFPlace.hilbert_mul_right v h1 h1 ha,
      hilbert_comm v (-1) a]
  simp only [NFPlace.hasseSerre, Fin.prod_univ_three, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [show ¬ ((0 : Fin 3) < 0) from by decide, show ((0 : Fin 3) < 1) from by decide,
    show ((0 : Fin 3) < 2) from by decide, show ¬ ((1 : Fin 3) < 0) from by decide,
    show ¬ ((1 : Fin 3) < 1) from by decide, show ((1 : Fin 3) < 2) from by decide,
    show ¬ ((2 : Fin 3) < 0) from by decide, show ¬ ((2 : Fin 3) < 1) from by decide,
    show ¬ ((2 : Fin 3) < 2) from by decide, if_true, if_false, one_mul, mul_one]
  rw [m1, m2, s1, s2, m3, m4, m5]
  rcases NFPlace.hilbert_eq_one_or v (-a) b with e1 | e1 <;>
    rcases NFPlace.hilbert_eq_one_or v a (-1) with e2 | e2 <;> rw [e1, e2] <;> ring

/-- At a real place, $(a, b)_v = -1$ iff $\sigma(a) < 0$ and $\sigma(b) < 0$. -/
theorem hilbert_real_eq_neg_one_iff (w : InfinitePlace F) (hw : w.IsReal) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (NFPlace.infinite w).hilbert a b = -1 ↔
      w.embedding_of_isReal hw a < 0 ∧ w.embedding_of_isReal hw b < 0 := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hφ : ∀ x : F, φ (algebraMap F w.Completion x) = w.embedding_of_isReal hw x := fun x => by
    simp [φ]
  have : (NFPlace.infinite w).hilbert a b =
      hilbertSymbol ℝ (w.embedding_of_isReal hw a) (w.embedding_of_isReal hw b) := by
    rw [← hφ, ← hφ, HasseIsoNF.hilbertSymbol_ringEquiv]; rfl
  rw [this]
  exact hilbertSymbol_real _ _ ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)

/-- The negative index of $\langle -a, -b, ab\rangle$ at a real place: $0$ if $\sigma(a), \sigma(b) < 0$, else $2$. -/
theorem realNegCount_pure (w : InfinitePlace F) (hw : w.IsReal) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    LocalClassNF.realNegCount w hw ![-a, -b, a * b] =
      if w.embedding_of_isReal hw a < 0 ∧ w.embedding_of_isReal hw b < 0 then 0 else 2 := by
  have ha' : w.embedding_of_isReal hw a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : w.embedding_of_isReal hw b ≠ 0 := (map_ne_zero _).2 hb
  rw [LocalClassNF.realNegCount, Finset.card_filter, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_neg, map_mul, Left.neg_neg_iff]
  rcases ha'.lt_or_gt with ha1 | ha1 <;> rcases hb'.lt_or_gt with hb1 | hb1
  · simp [ha1, hb1, not_lt.2 ha1.le, not_lt.2 hb1.le, not_lt.2 (mul_pos_of_neg_of_neg ha1 hb1).le]
  · simp [ha1, hb1, ha1.le, not_lt.2 hb1.le, mul_neg_of_neg_of_pos ha1 hb1, (lt_asymm hb1)]
  · simp [ha1, hb1, hb1.le, not_lt.2 ha1.le, mul_neg_of_pos_of_neg ha1 hb1, (lt_asymm ha1)]
  · simp [ha1, hb1, not_lt.2 (mul_pos ha1 hb1).le, lt_asymm ha1, lt_asymm hb1]

/-- **Local form of the classification**: at a place $v$, the pure norm forms of $(a,b)$ and $(a',b')$ are
isometric over $F_v$ iff $(a,b)_v = (a',b')_v$. -/
theorem atPlace_isometric_pure_iff (v : NFPlace F) {a b a' b' : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    v.atPlace (fun K _ _ => (pureForm a b).IsometricIn K (pureForm a' b')) ↔
      v.hilbert a b = v.hilbert a' b' := by
  have hne : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → ∀ i, (![-x, -y, x * y] : Fin 3 → F) i ≠ 0 := by
    intro x y hx hy i
    fin_cases i <;> simp [hx, hy]
  unfold pureForm
  rw [NFPlace.isometric_iff v _ _ (hne ha hb) (hne ha' hb'), hasseSerre_pure v ha hb,
    hasseSerre_pure v ha' hb']
  have hm1 : v.hilbert (-1) (-1) ≠ 0 := NFPlace.hilbert_ne_zero v _ _
  constructor
  · rintro ⟨-, hε, -⟩
    exact mul_left_cancel₀ hm1 hε
  · intro h
    refine ⟨?_, by rw [h], ?_⟩
    · have hsq : (∏ i, (![-a, -b, a * b] : Fin 3 → F) i) / ∏ i, (![-a', -b', a' * b'] : Fin 3 → F) i =
          ((a * b) / (a' * b')) ^ 2 := by
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        field_simp
      rw [hsq]
      cases v <;> exact ⟨_, by rw [map_pow, sq]⟩
    · cases v with
      | finite v => rfl
      | infinite w =>
        by_cases hw : w.IsReal
        · simp only [NFPlace.negIndex, hw, ↓reduceDIte]
          rw [realNegCount_pure w hw ha hb, realNegCount_pure w hw ha' hb']
          have e := (hilbert_real_eq_neg_one_iff w hw ha hb).symm.trans
            (h ▸ hilbert_real_eq_neg_one_iff w hw ha' hb')
          by_cases hc : w.embedding_of_isReal hw a < 0 ∧ w.embedding_of_isReal hw b < 0
          · rw [if_pos hc, if_pos (e.1 hc)]
          · rw [if_neg hc, if_neg (fun h' => hc (e.2 h'))]
        · simp only [NFPlace.negIndex, hw, ↓reduceDIte]

/-- **Quaternion algebras over a number field are determined by their local Hilbert symbols** (Voight 2021,
Main Theorem 14.6.1, injectivity; Theorem 5.1.1 and Hasse–Minkowski): for $a, b, a', b' \in F^\times$,
$$(a, b \mid F) \cong (a', b' \mid F) \iff (a, b)_v = (a', b')_v \text{ for all places } v \text{ of } F.$$
Proved unconditionally. -/
@[kb "voight2021" "Main Theorem 14.6.1, p. 231; Theorem 5.1.1, p. 65"]
theorem nonempty_algEquiv_iff_hilbert_eq {a b a' b' : F} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0)
    (hb' : b' ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,a',b']) ↔ ∀ v : NFPlace F, v.hilbert a b = v.hilbert a' b' := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hnd : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → (pureForm x y).Nondegenerate := by
    intro x y hx hy
    unfold pureForm
    refine QuadForm.nondegenerate_diag fun i => ?_
    fin_cases i <;> simp [hx, hy]
  rw [PureForm.nonempty_algEquiv_iff_isometricIn h2 ha hb]
  constructor
  · intro h v
    exact (atPlace_isometric_pure_iff v ha hb ha' hb').1 (LocalClassNF.atPlace_isometricIn_of_base v h)
  · intro h
    exact Tamagawa.FormClassNF.isometricIn_of_everywhere_nf _ _ (hnd ha hb) (hnd ha' hb')
      fun v => (atPlace_isometric_pure_iff v ha hb ha' hb').2 (h v)

/-- **Quaternion algebras over a number field are determined by their ramification** (Voight 2021,
Main Theorem 14.6.1: the map $B \mapsto \operatorname{Ram} B$ is injective on isomorphism classes): for
$a, b, a', b' \in F^\times$, $(a, b \mid F) \cong (a', b' \mid F)$ iff the two algebras are ramified (division
algebras over $F_v$) at exactly the same places $v$, finite and infinite. Proved unconditionally. -/
@[kb "voight2021" "Main Theorem 14.6.1, p. 231"]
theorem nonempty_algEquiv_iff_ram_eq {a b a' b' : F} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0)
    (hb' : b' ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,a',b']) ↔ ∀ v : NFPlace F, IsRamifiedAt a b v ↔ IsRamifiedAt a' b' v := by
  rw [nonempty_algEquiv_iff_hilbert_eq ha hb ha' hb']
  refine forall_congr' fun v => ?_
  rw [isRamifiedAt_iff ha hb, isRamifiedAt_iff ha' hb']
  rcases NFPlace.hilbert_eq_one_or v a b with e | e <;>
    rcases NFPlace.hilbert_eq_one_or v a' b' with e' | e' <;> rw [e, e'] <;> norm_num

/-- **The local–global principle for splitting** (Voight 2021, Main Theorem 14.6.1 with
$\operatorname{Ram} B = \emptyset$; Hasse–Brauer–Noether): $(a, b \mid F) \cong (1, 1 \mid F) \cong \mathrm{M}_2(F)$ iff
$(a, b \mid F)$ is split (not a division algebra) over every completion $F_v$. Proved unconditionally. -/
@[kb "voight2021" "Main Theorem 14.6.1, p. 231"]
theorem nonempty_algEquiv_one_iff {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,1,1]) ↔ ∀ v : NFPlace F, ¬ IsRamifiedAt a b v := by
  rw [nonempty_algEquiv_iff_ram_eq ha hb one_ne_zero one_ne_zero]
  refine forall_congr' fun v => ?_
  have h1 : ¬ IsRamifiedAt (1 : F) 1 v := by
    rw [isRamifiedAt_iff one_ne_zero one_ne_zero]
    have : v.hilbert 1 1 = 1 := by
      rw [NFPlace.hilbert_eq_one_iff v one_ne_zero]
      cases v <;> exact ⟨1, 0, by rw [map_one]; ring⟩
    rw [this]; norm_num
  simp [h1]

/-- **Main Theorem 14.6.1, surjectivity** (Voight 2021), as a named proposition about the number field $F$:
for every finite set $\Sigma$ of noncomplex places of $F$ (real places and finite places) of even cardinality,
there are $a, b \in F^\times$ such that $(a, b \mid F)$ is ramified exactly at the places in $\Sigma$. Stated,
not proved here (it needs elements with prescribed Hilbert symbols, `PresNF.exists_prescribed_hilbert`, plus
the choice of a suitable first entry $a$). -/
@[kb "voight2021" "Main Theorem 14.6.1, p. 231"]
def RamificationSurjective (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ S : Finset (NFPlace F), Even S.card →
    (∀ w : InfinitePlace F, NFPlace.infinite w ∈ S → w.IsReal) →
      ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ ∀ v : NFPlace F, IsRamifiedAt a b v ↔ v ∈ S

end LocalGlobal

end QuadFormsKB.Voight
