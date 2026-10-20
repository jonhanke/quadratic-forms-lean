import QuadFormsKB.Binary.SiegelBinary

/-!
# Siegel's formula for non-primitive binary forms

For $g$ primitive positive definite of fundamental discriminant $D$ and $c \ge 1$, the form $c\,g$ has discriminant
$c^2 D$ (never fundamental for $c > 1$), so `siegelFormula_binary` does not apply.  Here it is deduced from the
primitive case by scaling:

* **Classes** (`Scaling`): $\vec{x} \mapsto$ the map $[h] \mapsto [c\,h]$ is an injection of $\mathrm{GL}_2(\mathbb{Z})$-classes
  preserving $|\mathrm{Aut}|$, with $r_{ch}(cm) = r_h(m)$ and $r_{ch}(m) = 0$ for $c \nmid m$.
* **Genera** (`genusClasses_smul`): every form in the genus of $c\,g$ is $c\,h$ with $h$ in the genus of $g$ (all values
  are divisible by $c$ at every $p$), so $\mathrm{Gen}(cg) = c\cdot\mathrm{Gen}(g)$ and the genus average scales.
* **Local densities** (`localDensity_smul`): $\beta_p(c\,Q, c\,m') = p^{v_p(c)}\,\beta_p(Q, m')$ by the count
  $\#\{x \bmod p^{k+v} : cQ(x) \equiv cm'\} = p^{vn}\#\{x \bmod p^k : Q(x) \equiv m'\}$.
* **Result** (`siegelFormula_binary_nonprim`): the Siegel formula for $c\,g$ with the regularized product
  $L(1,\chi_{D})^{-1}\prod_{p \mid cmD}\beta_p(cg, m)/(1 - \chi_D(p)/p)$ (the primitive part's $D$).
-/

set_option linter.unusedSectionVars false

open Matrix Filter Topology QuadFormsKB.LocalDensity QuadFormsKB.Siegel

namespace QuadFormsKB.Binary

/-! ### Scaling of evaluation, classes, automorphisms -/

section Scaling

variable {n : ℕ}

theorem eval_smul {R : Type*} [CommRing R] (c : R) (Q : QuadForm R n) (x : Fin n → R) :
    (c • Q).eval x = c * Q.eval x := by
  simp only [QuadForm.evalIn, Finset.mul_sum, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem evalIn_smul {K : Type*} [CommRing K] (c : ℤ) (Q : QuadForm ℤ n) (x : Fin n → K) :
    (c • Q).evalIn K x = (c : K) * Q.evalIn K x := by
  simp only [QuadForm.evalIn, Finset.mul_sum, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, map_mul, eq_intCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem map_smul_form {K : Type*} [CommRing K] (c : ℤ) (Q : QuadForm ℤ n) (f : ℤ →+* K) :
    (c • Q).map f = (f c) • Q.map f := by
  ext i j
  simp only [QuadForm.map, QuadForm.smul_coeff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem isometricGL_smul_iff {K : Type*} [CommRing K] [IsDomain K] (a : K) (ha : a ≠ 0) (Q Q' : QuadForm K n) :
    IsometricGL (a • Q) (a • Q') ↔ IsometricGL Q Q' := by
  unfold IsometricGL
  simp only [eval_smul, mul_eq_mul_left_iff, ha, or_false]

/-- Scaling a class: $[h] \mapsto [c\,h]$ is well defined for $c \in \mathbb{Z}$. -/
theorem intEquiv_smul_iff {c : ℤ} (hc : c ≠ 0) (Q Q' : QuadForm ℤ n) :
    IntEquiv (c • Q) (c • Q') ↔ IntEquiv Q Q' :=
  isometricGL_smul_iff c hc Q Q'

/-- The classes of scaled forms: $[Q] \mapsto [cQ]$. -/
def scaleClass (c : ℤ) (hc : c ≠ 0) : QClass n → QClass n :=
  Quotient.map (sa := intSetoid n) (sb := intSetoid n) (fun Q => c • Q) (fun _ _ h => (intEquiv_smul_iff hc _ _).2 h)

@[simp] theorem scaleClass_classOf {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) :
    scaleClass c hc (classOf Q) = classOf (c • Q) := rfl

theorem scaleClass_injective {c : ℤ} (hc : c ≠ 0) : Function.Injective (scaleClass (n := n) c hc) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | h Q =>
  induction b using Quotient.inductionOn with
  | h Q' =>
    have h' : classOf (c • Q) = classOf (c • Q') := h
    exact classOf_eq_classOf_iff.2 ((intEquiv_smul_iff hc _ _).1 (classOf_eq_classOf_iff.1 h'))

/-- $\mathrm{Aut}(cQ) = \mathrm{Aut}(Q)$. -/
theorem aut_smul {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) : Aut (c • Q) = Aut Q := by
  ext g
  change (∀ x, (c • Q).eval (g.val *ᵥ x) = (c • Q).eval x) ↔ ∀ x, Q.eval (g.val *ᵥ x) = Q.eval x
  simp only [eval_smul, mul_eq_mul_left_iff, hc, or_false]

theorem repNum_smul_mul {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ n) (m : ℤ) : repNum (c • Q) (c * m) = repNum Q m := by
  unfold repNum
  have : repSet (c • Q) (c * m) = repSet Q m := by
    ext x
    simp only [repSet, eval_smul, Set.mem_ofPred_eq]
    exact mul_right_inj' hc
  rw [this]

theorem repNum_smul_of_not_dvd {c : ℤ} (Q : QuadForm ℤ n) {m : ℤ} (h : ¬ c ∣ m) : repNum (c • Q) m = 0 := by
  unfold repNum
  have : repSet (c • Q) m = ∅ := by
    ext x
    simp only [repSet, eval_smul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact h ⟨_, hx.symm⟩
  rw [this]; simp

theorem scaleClass_autCard {c : ℤ} (hc : c ≠ 0) (q : QClass n) : (scaleClass c hc q).autCard = q.autCard := by
  induction q using Quotient.inductionOn with
  | h Q =>
    change Nat.card (Aut (c • Q)) = Nat.card (Aut Q)
    rw [aut_smul hc]

theorem scaleClass_repNum {c : ℤ} (hc : c ≠ 0) (q : QClass n) (m : ℤ) :
    (scaleClass c hc q).repNum (c * m) = q.repNum m := by
  induction q using Quotient.inductionOn with
  | h Q => exact repNum_smul_mul hc Q m

theorem scaleClass_repNum_of_not_dvd {c : ℤ} (hc : c ≠ 0) (q : QClass n) {m : ℤ} (h : ¬ c ∣ m) :
    (scaleClass c hc q).repNum m = 0 := by
  induction q using Quotient.inductionOn with
  | h Q => exact repNum_smul_of_not_dvd Q h

end Scaling

/-! ### Genera under scaling -/

section Genus

variable {n : ℕ}

theorem sameGenus_smul_iff {c : ℤ} (hc : c ≠ 0) (Q Q' : QuadForm ℤ n) :
    SameGenus (c • Q) (c • Q') ↔ SameGenus Q Q' := by
  unfold SameGenus
  simp only [map_smul_form]
  refine and_congr (forall_congr' fun p => forall_congr' fun hp => ?_) ?_
  · exact isometricGL_smul_iff _ (by simpa using hc) _ _
  · exact isometricGL_smul_iff _ (by simpa using hc) _ _

/-- A $p$-adic divisibility of integers: `(c : ℤ_p) ∣ (z : ℤ_p)` gives `p ^ v_p(c) ∣ z`. -/
theorem padic_pow_dvd_of_dvd (p : ℕ) [Fact p.Prime] {c z : ℤ} (h : (c : ℤ_[p]) ∣ (z : ℤ_[p])) :
    (p : ℤ) ^ padicValInt p c ∣ z := by
  by_cases hc : c = 0
  · subst hc
    obtain ⟨w, hw⟩ := h
    have : (z : ℤ_[p]) = 0 := by simpa using hw
    have hz : z = 0 := by exact_mod_cast this
    simp [hz]
  obtain ⟨w, hw⟩ := h
  have h1 : ‖(c : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(padicValInt p c : ℕ) : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.2 (by exact_mod_cast padicValInt_dvd c)
  have h2 : ‖(z : ℤ_[p])‖ ≤ ‖(c : ℤ_[p])‖ := by
    rw [hw, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) w.norm_le_one
  have := PadicInt.norm_int_le_pow_iff_dvd.1 (h2.trans h1)
  exact_mod_cast this

/-- **Divisibility is detected prime by prime:** if $p^{v_p(c)} \mid z$ for every prime $p$ then $c \mid z$. -/
theorem int_dvd_of_forall_padic {c z : ℤ} (hc : c ≠ 0) (hz : z ≠ 0)
    (h : ∀ (p : ℕ) [Fact p.Prime], (p : ℤ) ^ padicValInt p c ∣ z) : c ∣ z := by
  have hc' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_prime_le_iff_dvd hc' hz']
  intro p hp
  have := Fact.mk hp
  have h3 : p ^ padicValInt p c ∣ z.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 (h p)
    simpa [Int.natAbs_pow] using this
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact (padicValNat_dvd_iff_le hz').1 h3

/-- **Every value of a form in the genus of $c\,Q$ is divisible by $c$.** -/
theorem dvd_eval_of_sameGenus {c : ℤ} (hc : c ≠ 0) {Q Q' : QuadForm ℤ n} (h : SameGenus (c • Q) Q')
    (x : Fin n → ℤ) : c ∣ Q'.eval x := by
  by_cases hz : Q'.eval x = 0
  · rw [hz]; exact dvd_zero _
  have hloc : ∀ (p : ℕ) [Fact p.Prime], (p : ℤ) ^ padicValInt p c ∣ Q'.eval x := by
    intro p _
    obtain ⟨g, hg⟩ := h.1 p
    have h1 := hg (fun i => (x i : ℤ_[p]))
    have e1 : ∀ (R : QuadForm ℤ n) (v : Fin n → ℤ),
        (R.map (Int.castRingHom ℤ_[p])).eval (fun i => (v i : ℤ_[p])) = ((R.eval v : ℤ) : ℤ_[p]) := by
      intro R v
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e1, map_smul_form, eval_smul] at h1
    apply padic_pow_dvd_of_dvd p
    exact ⟨_, by simpa using h1.symm⟩
  have hc' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
  have hz' : (Q'.eval x).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_prime_le_iff_dvd hc' hz']
  intro p hp
  have := Fact.mk hp
  have h3 : p ^ padicValInt p c ∣ (Q'.eval x).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 (hloc p)
    simpa [Int.natAbs_pow] using this
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact (padicValNat_dvd_iff_le hz').1 h3

/-! #### Binary forms: the coefficients -/

theorem binQF_eq_mk (f : BinQF) : f = BinQF.mk f.a f.b f.c := by
  apply QuadForm.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinQF.mk, QuadForm.ofUpper, BinQF.a, BinQF.b, BinQF.c, f.upper (show (0 : Fin 2) < 1 from by decide)]

theorem smul_mk (c a b d : ℤ) : c • BinQF.mk a b d = BinQF.mk (c * a) (c * b) (c * d) := by
  apply QuadForm.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinQF.mk, QuadForm.ofUpper]

theorem a_smul (c : ℤ) (f : BinQF) : (c • f).a = c * f.a := by simp [BinQF.a]
theorem b_smul (c : ℤ) (f : BinQF) : (c • f).b = c * f.b := by simp [BinQF.b]
theorem c_smul (c : ℤ) (f : BinQF) : (c • f).c = c * f.c := by simp [BinQF.c]

theorem disc_smul (c : ℤ) (f : BinQF) : (c • f).disc = c ^ 2 * f.disc := by
  simp only [BinQF.disc, a_smul, b_smul, c_smul]; ring

/-- **A binary form all of whose values are divisible by $c$ is $c\,h$.** -/
theorem exists_smul_of_dvd_eval {c : ℤ} {f : BinQF} (h : ∀ x : Fin 2 → ℤ, c ∣ QuadForm.eval f x) :
    ∃ g : BinQF, f = c • g := by
  have h1 := h ![1, 0]
  have h2 := h ![0, 1]
  have h3 := h ![1, 1]
  have e : ∀ x y : ℤ, QuadForm.eval f ![x, y] = f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2 := fun x y => BinQF.eval_eq f x y
  simp only [e] at h1 h2 h3
  have ha : c ∣ f.a := by simpa using h1
  have hd : c ∣ f.c := by simpa using h2
  have hb : c ∣ f.b := by
    have : c ∣ f.a * 1 ^ 2 + f.b * 1 * 1 + f.c * 1 ^ 2 - f.a - f.c := dvd_sub (dvd_sub h3 ha) hd
    have e2 : f.a * 1 ^ 2 + f.b * 1 * 1 + f.c * 1 ^ 2 - f.a - f.c = f.b := by ring
    rwa [e2] at this
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨d', hd'⟩ := hd
  refine ⟨BinQF.mk a' b' d', ?_⟩
  rw [smul_mk, ← ha', ← hb', ← hd', ← binQF_eq_mk]

/-- **Under scaling, the genus of $c\,g$ is the scaled genus of $g$:**
$\mathrm{Gen}(c\,g) = \{[c\,h] : h \in \mathrm{Gen}(g)\}$. -/
theorem genusClasses_smul {c : ℤ} (hc : c ≠ 0) (g : BinQF) :
    genusClasses (c • g) = scaleClass c hc '' genusClasses g := by
  ext q
  induction q using Quotient.inductionOn with
  | h Q' =>
    change classOf Q' ∈ _ ↔ classOf Q' ∈ _
    rw [classOf_mem_genusClasses_iff]
    constructor
    · intro hg
      obtain ⟨h, rfl⟩ := exists_smul_of_dvd_eval (dvd_eval_of_sameGenus hc hg)
      exact ⟨classOf h, classOf_mem_genusClasses_iff.2 ((sameGenus_smul_iff hc _ _).1 hg), rfl⟩
    · rintro ⟨q, hq, hqe⟩
      induction q using Quotient.inductionOn with
      | h h =>
        have hq' := classOf_mem_genusClasses_iff.1 hq
        have hqe' : classOf (c • h) = classOf Q' := hqe
        exact ((sameGenus_smul_iff hc _ _).2 hq').trans (classOf_eq_classOf_iff.1 hqe').sameGenus

theorem mass_smul {c : ℤ} (hc : c ≠ 0) (g : BinQF) : mass (c • g) = mass g := by
  unfold mass
  rw [genusClasses_smul hc, finsum_mem_image (scaleClass_injective hc).injOn]
  exact finsum_mem_congr rfl fun q _ => by rw [scaleClass_autCard]

theorem genusRepSum_smul_mul {c : ℤ} (hc : c ≠ 0) (g : BinQF) (m : ℤ) :
    genusRepSum (c • g) (c * m) = genusRepSum g m := by
  unfold genusRepSum
  rw [genusClasses_smul hc, finsum_mem_image (scaleClass_injective hc).injOn]
  exact finsum_mem_congr rfl fun q _ => by rw [scaleClass_autCard, scaleClass_repNum]

theorem genusRepSum_smul_of_not_dvd {c : ℤ} (hc : c ≠ 0) (g : BinQF) {m : ℤ} (h : ¬ c ∣ m) :
    genusRepSum (c • g) m = 0 := by
  unfold genusRepSum
  rw [genusClasses_smul hc, finsum_mem_image (scaleClass_injective hc).injOn]
  exact finsum_mem_eq_zero_of_forall_eq_zero fun q _ => by rw [scaleClass_repNum_of_not_dvd hc q h]; simp

/-- **The genus average scales:** $\mathrm{avg}_{\mathrm{Gen}(cg)}(cm) = \mathrm{avg}_{\mathrm{Gen}(g)}(m)$. -/
theorem genusRepAvg_smul_mul {c : ℤ} (hc : c ≠ 0) (g : BinQF) (m : ℤ) :
    genusRepAvg (c • g) (c * m) = genusRepAvg g m := by
  unfold genusRepAvg
  rw [genusRepSum_smul_mul hc, mass_smul hc]

theorem genusRepAvg_smul_of_not_dvd {c : ℤ} (hc : c ≠ 0) (g : BinQF) {m : ℤ} (h : ¬ c ∣ m) :
    genusRepAvg (c • g) m = 0 := by
  unfold genusRepAvg
  rw [genusRepSum_smul_of_not_dvd hc g h, zero_div]

end Genus

/-! ### Local densities under scaling -/

section LocalScaling

variable {n : ℕ}

/-- The fibre-counting identity for a surjective additive map of finite groups. -/
theorem card_preimage_mul {G H : Type} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H] (f : G →+ H)
    (hf : Function.Surjective f) (P : H → Prop) :
    Nat.card {g // P (f g)} * Nat.card H = Nat.card G * Nat.card {h // P h} := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite H
  have hfib : ∀ h : H, (Finset.univ.filter (fun g => f g = h)).card = (Finset.univ.filter (fun g => f g = 0)).card :=
    fun h => AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) ⟨0, map_zero f⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  have h1 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun g => P (f g)))
    (t := Finset.univ.filter P) (f := f) (by intro x hx; simpa using hx)
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G)) (t := Finset.univ) (f := f)
    (by intro x hx; simp)
  rw [h1, ← Finset.card_univ (α := G), h2]
  have h3 : ∀ b ∈ Finset.univ.filter P,
      ((Finset.univ.filter (fun g => P (f g))).filter (fun a => f a = b)).card =
        (Finset.univ.filter (fun g => f g = 0)).card := by
    intro b hb
    rw [← hfib b, Finset.filter_filter]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hb, h⟩
  rw [Finset.sum_congr rfl h3]
  have h4 : ∀ b ∈ (Finset.univ : Finset H), ((Finset.univ : Finset G).filter (fun a => f a = b)).card =
      (Finset.univ.filter (fun g => f g = 0)).card := fun b _ => hfib b
  rw [Finset.sum_congr rfl h4]
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  ring

/-- $p^v t = 0$ in $\mathbb{Z}/p^{k+v}$ iff $t \equiv 0 \pmod{p^k}$. -/
theorem pow_mul_eq_zero_iff (p : ℕ) [Fact p.Prime] (k v : ℕ) (t : ZMod (p ^ (k + v))) :
    (p ^ v : ZMod (p ^ (k + v))) * t = 0 ↔ ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k v)) (ZMod (p ^ k)) t = 0 := by
  have : NeZero (p ^ (k + v)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p ^ v := pow_pos (Fact.out : p.Prime).pos _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_lhs => rw [← ZMod.natCast_zmod_val t]
  rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  generalize t.val = w
  have : p ^ (k + v) = p ^ v * p ^ k := by rw [← pow_add, add_comm]
  rw [this, Nat.mul_dvd_mul_iff_left hp0]

/-- **Counting under scaling.** For $c = p^v u$ with $p \nmid u$,
$$\#\{x \bmod p^{k+v} : cQ(x) \equiv c m'\} = p^{vn}\,\#\{x \bmod p^k : Q(x) \equiv m'\}.$$ -/
theorem repCount_smul (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (v u : ℕ) (hu : ¬ p ∣ u) (k : ℕ) (m' : ℤ) :
    repCount (((p ^ v * u : ℕ) : ℤ) • Q) p (k + v) (((p ^ v * u : ℕ) : ℤ) * m') = p ^ (v * n) * repCount Q p k m' := by
  have hp := (Fact.out : p.Prime)
  have : NeZero (p ^ (k + v)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set π := ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k v)) (ZMod (p ^ k)) with hπ
  have hunit : IsUnit ((u : ℕ) : ZMod (p ^ (k + v))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((hp.coprime_iff_not_dvd.2 hu).symm).pow_right _
  have hmapQ : ∀ x : Fin n → ZMod (p ^ (k + v)), π (Q.evalIn (ZMod (p ^ (k + v))) x) = Q.evalIn (ZMod (p ^ k)) (fun i => π (x i)) := by
    intro x
    simp only [QuadForm.evalIn, map_sum, apply_ite π, map_mul, map_zero, algebraMap_int_eq, eq_intCast, map_intCast]
  let f : (Fin n → ZMod (p ^ (k + v))) →+ (Fin n → ZMod (p ^ k)) :=
    AddMonoidHom.compLeft π.toAddMonoidHom (Fin n)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := (Function.Surjective.comp_left (ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_add_right k v))) (α := Fin n)) z
    exact ⟨y, hy⟩
  have e : ∀ a : ZMod (p ^ (k + v)), ((p ^ v * u : ℕ) : ZMod (p ^ (k + v))) * a = ((p ^ v * u : ℕ) : ZMod (p ^ (k + v))) * (((m' : ℤ)) : ZMod (p ^ (k + v))) ↔ π (a - (m' : ZMod (p ^ (k + v)))) = 0 := by
    intro a
    rw [← sub_eq_zero, ← mul_sub]
    have : ((p ^ v * u : ℕ) : ZMod (p ^ (k + v))) * (a - (m' : ZMod (p ^ (k + v)))) =
        (u : ZMod (p ^ (k + v))) * ((p ^ v : ZMod (p ^ (k + v))) * (a - (m' : ZMod (p ^ (k + v))))) := by
      push_cast; ring
    rw [this, hunit.mul_right_eq_zero, pow_mul_eq_zero_iff]
  have hcond : ∀ x : Fin n → ZMod (p ^ (k + v)),
      ((((p ^ v * u : ℕ) : ℤ) • Q).evalIn (ZMod (p ^ (k + v))) x = ((((p ^ v * u : ℕ) : ℤ) * m' : ℤ) : ZMod (p ^ (k + v)))) ↔
        Q.evalIn (ZMod (p ^ k)) (f x) = (m' : ZMod (p ^ k)) := by
    intro x
    rw [evalIn_smul]
    have h1 := e (Q.evalIn (ZMod (p ^ (k + v))) x)
    push_cast at h1 ⊢
    rw [h1, map_sub, hmapQ, map_intCast, sub_eq_zero]
    rfl
  unfold repCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcond)]
  have hc := card_preimage_mul f hsurj (fun z => Q.evalIn (ZMod (p ^ k)) z = (m' : ZMod (p ^ k)))
  have hcard : ∀ N : ℕ, Nat.card (Fin n → ZMod (p ^ N)) = (p ^ N) ^ n := by
    intro N; rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [hcard, hcard] at hc
  have hpos : 0 < (p ^ k) ^ n := pow_pos (pow_pos hp.pos _) _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hc, ← pow_mul, ← pow_mul]
  ring

theorem padicValNat_pow_mul_of_not_dvd (p : ℕ) [Fact p.Prime] (v u : ℕ) (hu : ¬ p ∣ u) (hu0 : u ≠ 0) :
    padicValNat p (p ^ v * u) = v := by
  rw [padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hu0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hu, add_zero]

/-- **Local density under scaling.** For $Q$ nondegenerate, $c \ge 1$, $m' \ne 0$ and $p$ prime,
$$\beta_p(c\,Q, c\,m') = p^{v_p(c)}\,\beta_p(Q, m').$$ -/
theorem localDensity_smul (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 0 < n) {c : ℕ} (hc : c ≠ 0) (p : ℕ)
    [Fact p.Prime] {m' : ℤ} (hm' : m' ≠ 0) :
    localDensity (((c : ℕ) : ℤ) • Q) p ((c : ℤ) * m') = (p : ℝ) ^ padicValNat p c * localDensity Q p m' := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨v, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc p hp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  have hv : padicValNat p c = v := by rw [hcu]; exact padicValNat_pow_mul_of_not_dvd p v u hu hu0
  rw [hv]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h1 := localDensity_eventually_eq Q hQ p m' hm'
  have key : ∀ᶠ N in Filter.atTop, (repCount (((c : ℕ) : ℤ) • Q) p N ((c : ℤ) * m') : ℝ) / (p : ℝ) ^ (N * (n' + 1 - 1)) =
      (p : ℝ) ^ v * localDensity Q p m' := by
    rw [Filter.eventually_atTop] at h1 ⊢
    obtain ⟨K, hK⟩ := h1
    refine ⟨K + v, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + v := ⟨N - v, by omega⟩
    have hk := hK k (by omega)
    rw [hcu, repCount_smul Q p v u hu k m']
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [← hk]
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have : Filter.Tendsto (fun N : ℕ => (repCount (((c : ℕ) : ℤ) • Q) p N ((c : ℤ) * m') : ℝ) / (p : ℝ) ^ (N * (n' + 1 - 1)))
      Filter.atTop (nhds ((p : ℝ) ^ v * localDensity Q p m')) :=
    tendsto_const_nhds.congr' (key.mono fun _ h => h.symm)
  exact this.limUnder_eq

/-- **Local density vanishes when $p^{v_p(c)} \nmid m$.** -/
theorem localDensity_smul_of_not_dvd (Q : QuadForm ℤ n) {c : ℕ} (p : ℕ) [Fact p.Prime] {m : ℤ}
    (hm : ¬ (p : ℤ) ^ padicValNat p c ∣ m) :
    localDensity (((c : ℕ) : ℤ) • Q) p m = 0 := by
  have hp := (Fact.out : p.Prime)
  set v := padicValNat p c with hv
  have hcv : (p : ℤ) ^ v ∣ (c : ℤ) := by exact_mod_cast pow_padicValNat_dvd (n := c) (p := p)
  have key : ∀ᶠ N in Filter.atTop, (repCount (((c : ℕ) : ℤ) • Q) p N m : ℝ) / (p : ℝ) ^ (N * (n - 1)) = 0 := by
    rw [Filter.eventually_atTop]
    refine ⟨v, fun N hN => ?_⟩
    have : repCount (((c : ℕ) : ℤ) • Q) p N m = 0 := by
      unfold repCount
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨x, hx⟩
      have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hdv : p ^ v ∣ p ^ N := pow_dvd_pow p hN
      have h2 := congrArg (ZMod.castHom hdv (ZMod (p ^ v))) hx
      rw [evalIn_smul, map_mul, map_intCast, map_intCast] at h2
      have h3 : ((c : ℤ) : ZMod (p ^ v)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hcv
      rw [h3, zero_mul] at h2
      apply hm
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd m (p ^ v)).1 h2.symm
      exact_mod_cast this
    rw [this]; simp
  have : Filter.Tendsto (fun N : ℕ => (repCount (((c : ℕ) : ℤ) • Q) p N m : ℝ) / (p : ℝ) ^ (N * (n - 1)))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.congr' (key.mono fun _ h => h.symm)
  exact this.limUnder_eq

end LocalScaling

/-! ### The main theorem -/

section Main

variable {D : ℤ} [IsQuadDisc D]

/-- **The finite correction for a scaled form** $c\,g$ at $m$:
$$C^{(c)}_f(m) = \prod_{p \mid c\,m\,D}\frac{\beta_p(f, m)}{1 - \chi_D(p)/p},$$
the product taken over the primes dividing $c\,m\,D$ (here $D$ is the discriminant of the *primitive part*).  For
$c = 1$ it is `binaryEulerCorr`.  All primes outside $c\,m\,D$ contribute the factor $1$ (they do not divide $c$, so
$\beta_p(cg, m)$ is that of $g$ at the unit multiple $m/c \in \mathbb{Z}_p$). -/
noncomputable def binaryEulerCorrNP (f : BinQF) (D c m : ℤ) : ℝ :=
  ∏ p ∈ (c * m * D).natAbs.primeFactors, localDensity f p m / (1 - kronR D p / p)

/-- **Regularized $\prod_p\beta_p(m)$ for a scaled form:** $L(1,\chi_D)^{-1}\,C^{(c)}_f(m)$. -/
noncomputable def binaryEulerValueNP (f : BinQF) (D : ℤ) [IsQuadDisc D] (c m : ℤ) : ℝ :=
  (LOne D)⁻¹ * binaryEulerCorrNP f D c m

theorem factor_eq_one {g : BinQF} (hD : g.disc = D) {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : m ≠ 0)
    (hpm : p ∉ (m * D).natAbs.primeFactors) : localDensity g p m / (1 - kronR D p / p) = 1 := by
  have hD0 : D ≠ 0 := by
    have := three_le_natAbs (D := D); omega
  have hnd : ¬ (p : ℤ) ∣ m * D := by
    intro h
    apply hpm
    rw [Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.2 (mul_ne_zero hm hD0)⟩
  rw [localDensity_of_not_dvd hD hp hm hnd]
  exact div_self (one_sub_kronR_div_ne_zero hp)

theorem prod_pow_padicValNat_eq (S : Finset ℕ) {c : ℕ} (hc : c ≠ 0) (hS : c.primeFactors ⊆ S)
    (hSp : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (p : ℝ) ^ padicValNat p c = c := by
  have h1 : ∏ p ∈ S, (p : ℝ) ^ padicValNat p c = ∏ p ∈ c.primeFactors, (p : ℝ) ^ padicValNat p c := by
    symm
    refine Finset.prod_subset hS fun p hpS hp => ?_
    have hpp := hSp p hpS
    have : padicValNat p c = 0 := by
      have := Fact.mk hpp
      apply padicValNat.eq_zero_of_not_dvd
      intro hd; exact hp (Nat.mem_primeFactors.2 ⟨hpp, hd, hc⟩)
    simp [this]
  rw [h1]
  have h2 : ∏ p ∈ c.primeFactors, p ^ padicValNat p c = c := by
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hc]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
  exact_mod_cast h2

/-- **Scaling of the finite correction when $c \mid m$:** $C^{(c)}_{cg}(cm') = c\,C_g(m')$ (the factor
$p^{v_p(c)}$ at each $p \mid c$ multiplies up to $c$). -/
theorem binaryEulerCorrNP_smul {g : BinQF} (hg : Primitive g) (hD : g.disc = D) (hpos : g.PosDef') {c : ℕ} (hc : c ≠ 0)
    {m' : ℤ} (hm' : m' ≠ 0) :
    binaryEulerCorrNP ((c : ℤ) • g) D c ((c : ℤ) * m') = c * binaryEulerCorr g D m' := by
  have hD0 : D ≠ 0 := by
    have := three_le_natAbs (D := D); omega
  have hQ : g.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hessian_det_eq_neg_disc, hD]; exact neg_ne_zero.2 hD0
  set S := (((c : ℕ) : ℤ) * ((c : ℤ) * m') * D).natAbs.primeFactors with hS
  set T := (m' * D).natAbs.primeFactors with hT
  have hTS : T ⊆ S := by
    intro p hp
    rw [hT, Nat.mem_primeFactors] at hp
    rw [hS, Nat.mem_primeFactors]
    refine ⟨hp.1, ?_, Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hc) (mul_ne_zero (by exact_mod_cast hc) hm')) hD0)⟩
    refine dvd_trans hp.2.1 (Int.natAbs_dvd_natAbs.2 ?_)
    exact ⟨(c : ℤ) * c, by ring⟩
  have hcS : c.primeFactors ⊆ S := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [hS, Nat.mem_primeFactors]
    refine ⟨hp.1, ?_, Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hc) (mul_ne_zero (by exact_mod_cast hc) hm')) hD0)⟩
    refine dvd_trans hp.2.1 ?_
    have h1 : (c : ℤ) ∣ (c : ℤ) * ((c : ℤ) * m') * D := ⟨(c : ℤ) * m' * D, by ring⟩
    simpa using Int.natAbs_dvd_natAbs.2 h1
  have hfac : ∀ p ∈ S, localDensity ((c : ℤ) • g) p ((c : ℤ) * m') / (1 - kronR D p / p) =
      (p : ℝ) ^ padicValNat p c * (localDensity g p m' / (1 - kronR D p / p)) := by
    intro p hp
    have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    rw [localDensity_smul g hQ (by norm_num) hc p hm', mul_div_assoc]
  unfold binaryEulerCorrNP binaryEulerCorr
  rw [← hS, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_pow_padicValNat_eq S hc hcS (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  congr 1
  symm
  refine Finset.prod_subset hTS fun p hpS hpT => ?_
  exact factor_eq_one hD (Nat.prime_of_mem_primeFactors hpS) hm' hpT

/-- If $c \nmid m$ the corrected product vanishes (a prime $p \mid c$ with $v_p(m) < v_p(c)$ has $\beta_p = 0$). -/
theorem binaryEulerCorrNP_smul_of_not_dvd (g : BinQF) {c : ℕ} (hc : c ≠ 0) {m : ℤ} (hm : m ≠ 0)
    (h : ¬ (c : ℤ) ∣ m) : binaryEulerCorrNP ((c : ℤ) • g) D c m = 0 := by
  have hD0 : D ≠ 0 := by
    have := three_le_natAbs (D := D); omega
  by_contra hne
  apply h
  apply int_dvd_of_forall_padic (by exact_mod_cast hc : (c : ℤ) ≠ 0) hm
  intro p _
  by_contra hnd
  apply hne
  unfold binaryEulerCorrNP
  refine Finset.prod_eq_zero (i := p) ?_ ?_
  · have hpc : p ∣ c := by
      by_contra hpc
      apply hnd
      rw [padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd hpc]; simp
    rw [Nat.mem_primeFactors]
    refine ⟨Fact.out, ?_, Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hc) hm) hD0)⟩
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by simpa using hpc) _) _
  · rw [localDensity_smul_of_not_dvd g p (by rwa [padicValInt.of_nat] at hnd), zero_div]

theorem betaInf_smul (g : BinQF) (hD : g.disc < 0) {c : ℕ} (hc : c ≠ 0) (m m' : ℝ) :
    betaInf ((c : ℤ) • g) m = betaInf g m' / c := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hD' : (0 : ℝ) < -(g.disc : ℝ) := by
    have : (g.disc : ℝ) < 0 := by exact_mod_cast hD
    linarith
  have hD2 : (((c : ℕ) : ℤ) • g).disc < 0 := by
    rw [disc_smul]
    exact mul_neg_of_pos_of_neg (by positivity) hD
  rw [betaInf_binary _ hD2, betaInf_binary _ hD, disc_smul]
  have : -((((c : ℤ) ^ 2 * g.disc : ℤ) : ℝ)) = (c : ℝ) ^ 2 * (-(g.disc : ℝ)) := by push_cast; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hcpos.le]
  have hs : Real.sqrt (-(g.disc : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hD').ne'
  field_simp

/-- **Siegel's formula for the non-primitive binary form $c\,g$** ($g$ primitive positive definite of fundamental
discriminant $D < 0$, $c \ge 1$, $m \ge 1$):
$$r_{\mathcal G(cg)}(m) = \tfrac12\,\beta_\infty(cg, m)\cdot L(1,\chi_D)^{-1}\prod_{p \mid cmD}\frac{\beta_p(cg, m)}{1 - \chi_D(p)/p},$$
with $\chi_D$ of the **primitive part**.  For $c \nmid m$ both sides are $0$.  Proof: the class bijection, the
genus-average scaling `genusRepAvg_smul_mul`, `betaInf_smul`, `binaryEulerCorrNP_smul`
($\beta_p(cg, cm') = p^{v_p(c)}\beta_p(g, m')$) and `siegelFormula_binary`. -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2), non-primitive forms by scaling [unverified locator]"]
theorem siegelFormula_binary_nonprim [Fact (D < 0)] (g : PosForms D) {c : ℕ} (hc : c ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg ((c : ℤ) • g.1) m =
      (1 / 2 : ℝ) * aEWith ((c : ℤ) • g.1) m (binaryEulerValueNP ((c : ℤ) • g.1) D c m) := by
  have hD : D < 0 := Fact.out
  obtain ⟨hprim, hgD, hpos⟩ := g.2
  have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast hc
  by_cases hdiv : c ∣ m
  · obtain ⟨m', rfl⟩ := hdiv
    have hm' : m' ≠ 0 := fun h => hm (by simp [h])
    have hm'z : (m' : ℤ) ≠ 0 := by exact_mod_cast hm'
    have hcast : ((c * m' : ℕ) : ℤ) = (c : ℤ) * m' := by push_cast; ring
    rw [hcast, genusRepAvg_smul_mul hc0 g.1 m', siegelFormula_binary g hm']
    unfold aEWith binaryEulerValue binaryEulerValueNP
    rw [betaInf_smul g.1 (by rw [hgD]; exact hD) hc _ (m' : ℝ), binaryEulerCorrNP_smul hprim hgD hpos hc hm'z]
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [Int.cast_natCast]
    field_simp
  · have hndz : ¬ (c : ℤ) ∣ (m : ℤ) := by exact_mod_cast hdiv
    rw [genusRepAvg_smul_of_not_dvd hc0 g.1 hndz]
    unfold aEWith binaryEulerValueNP
    rw [binaryEulerCorrNP_smul_of_not_dvd g.1 hc (by exact_mod_cast hm) hndz]
    simp

/-! #### Every positive definite binary form is `c • g` with `g` primitive -/

/-- **Content decomposition:** a positive definite binary form is $c\,g$ with $c \ge 1$ its content and
$g$ primitive positive definite (`PosForms`) of discriminant $\operatorname{disc}(f)/c^2$. -/
theorem exists_content_decomp {f : BinQF} (hf : f.PosDef') :
    ∃ (c : ℕ) (_ : c ≠ 0) (D' : ℤ) (g : PosForms D'), f = (c : ℤ) • g.1 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = Int.gcd f.a (Int.gcd f.b f.c) := ⟨_, rfl⟩
  have ha : f.a ≠ 0 := hf.1.ne'
  have hd0 : d ≠ 0 := by
    intro h
    have := Int.gcd_eq_zero_iff.1 (hd ▸ h)
    exact ha this.1
  have hda : (d : ℤ) ∣ f.a := by rw [hd]; exact Int.gcd_dvd_left _ _
  have hdb : (d : ℤ) ∣ f.b := by rw [hd]; exact (Int.gcd_dvd_right f.a (Int.gcd f.b f.c : ℤ)).trans (Int.gcd_dvd_left f.b f.c)
  have hdc : (d : ℤ) ∣ f.c := by rw [hd]; exact (Int.gcd_dvd_right f.a (Int.gcd f.b f.c : ℤ)).trans (Int.gcd_dvd_right f.b f.c)
  obtain ⟨a', ha'⟩ := hda
  obtain ⟨b', hb'⟩ := hdb
  obtain ⟨c', hc'⟩ := hdc
  have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hfeq : f = (d : ℤ) • BinQF.mk a' b' c' := by
    rw [smul_mk, ← ha', ← hb', ← hc', ← binQF_eq_mk]
  have hprim : Primitive (BinQF.mk a' b' c') := by
    unfold Primitive
    simp only [BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
    have h1 : d = Int.gcd ((d : ℤ) * a') (Int.gcd ((d : ℤ) * b') ((d : ℤ) * c')) := by
      rw [← ha', ← hb', ← hc']; exact hd
    have hin : Int.gcd ((d : ℤ) * b') ((d : ℤ) * c') = d * Int.gcd b' c' := by
      rw [Int.gcd_mul_left]; simp
    rw [hin, Nat.cast_mul, Int.gcd_mul_left] at h1
    simp only [Int.natAbs_natCast] at h1
    have : d * 1 = d * Int.gcd a' (Int.gcd b' c' : ℤ) := by rw [mul_one]; exact h1
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) this).symm
  have hdisc : (BinQF.mk a' b' c').disc < 0 := by
    have h := hf.2
    rw [hfeq, disc_smul] at h
    by_contra hh
    replace hh : 0 ≤ (BinQF.mk a' b' c').disc := not_lt.1 hh
    nlinarith [sq_nonneg (d : ℤ), mul_nonneg (sq_nonneg (d : ℤ)) hh]
  have hapos : 0 < (BinQF.mk a' b' c').a := by
    simp only [BinQF.a_mk]
    have h := hf.1
    rw [ha'] at h
    exact pos_of_mul_pos_right h hdpos.le |> fun h => by simpa using h
  exact ⟨d, hd0, _, ⟨BinQF.mk a' b' c', hprim, rfl, hapos, hdisc⟩, hfeq⟩

theorem binaryEulerValueNP_one (f : BinQF) (m : ℤ) : binaryEulerValueNP f D 1 m = binaryEulerValue f D m := by
  simp [binaryEulerValueNP, binaryEulerValue, binaryEulerCorrNP, binaryEulerCorr]

/-- **Siegel's formula for every positive definite binary form whose primitive part has fundamental discriminant.**
Every positive definite binary form $f$ is $c\,g$ with $c \ge 1$ its content and $g$ primitive positive definite of
some discriminant $D < 0$ (`exists_content_decomp`); whenever $D$ is a (negative) fundamental discriminant, for every
$m \ge 1$
$$r_{\mathcal G(f)}(m) = \tfrac12\,\beta_\infty(f, m)\cdot L(1,\chi_D)^{-1}\prod_{p \mid c\,m\,D}\frac{\beta_p(f, m)}{1 - \chi_D(p)/p}.$$
Primitive forms ($c = 1$) recover `siegelFormula_binary`. -/
theorem siegelFormula_binary_posDef (f : BinQF) (hf : f.PosDef') :
    ∃ (c : ℕ) (_ : c ≠ 0) (D : ℤ) (g : PosForms D), f = (c : ℤ) • g.1 ∧
      ∀ [IsQuadDisc D] {m : ℕ}, m ≠ 0 →
        Siegel.genusRepAvg f m = (1 / 2 : ℝ) * aEWith f m (binaryEulerValueNP f D c m) := by
  obtain ⟨c, hc, D, g, rfl⟩ := exists_content_decomp hf
  refine ⟨c, hc, D, g, rfl, fun {_} {m} hm => ?_⟩
  have : Fact (D < 0) := ⟨by rw [← g.2.2.1]; exact g.2.2.2.2⟩
  exact siegelFormula_binary_nonprim g hc hm

end Main

end QuadFormsKB.Binary
