/-
# Cassels, Chapter 2, §6: the ring structure on $G(k)$ and $W(k)$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, §6, Note, p. 28.

**Setting.** As in `Ch2/WittGroup.lean` and `Ch2/WittPresentation.lean`: $k$ = `K` is a field with $2 \ne 0$
(`[Invertible (2 : K)]`); $G(k)$ = `G K` is the Grothendieck group of regular spaces, $W(k)$ = `W K` its quotient by
the hyperbolic plane, and $\langle a\rangle$ = `gG a` $=$ `toG K (unary K a)` (resp. `gW a` in $W(k)$) for
$a \in k^{\times}$.

**Proves.** The Note, p. 28: $G(k)$ and $W(k)$ are commutative rings, with product determined by
$\langle a\rangle\langle b\rangle = \langle ab\rangle$ and unit $\langle 1\rangle$ (`mulG_gen`, `mulW_gen`; the
instances `CommRing (G K)`, `CommRing (W K)`, whose additive structure is the existing one), and the quotient map
$G(k) \to W(k)$ is a ring homomorphism (`toWRingHom`).

**Proof notes.** Cassels defines the product by the tensor product of quadratic spaces. Here it is defined on the
generators through the universal properties `G_lift` and `W_lift`: for fixed $c$ the map $a \mapsto \langle ca\rangle$
satisfies relations (i), (ii) (and (iii) in $W(k)$ because $\langle c\rangle + \langle -c\rangle = 0$), giving an
endomorphism $m_c$; then $c \mapsto m_c$ satisfies the relations again, giving a biadditive product. The ring axioms
are checked on generators.
-/
import QuadFormsKB.Literature.Cassels.Ch2.WittPresentation

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The class $\langle a\rangle \in G(k)$ of the unary space $a x^{2}$, for $a \in k^{\times}$. -/
def gG (a : Kˣ) : G K := toG K (unary K a)

/-- The class $\langle a\rangle \in W(k)$ of the unary space $a x^{2}$, for $a \in k^{\times}$. -/
def gW (a : Kˣ) : W K := toW K (gG a)

/-- Relation (i) in $G(k)$: $\langle ab^{2}\rangle = \langle a\rangle$. -/
theorem gG_sq (a b : Kˣ) : gG (a * b ^ 2) = (gG a : G K) := by
  unfold gG; rw [unary_mul_sq]

/-- Relation (ii) in $G(k)$: $\langle a\rangle + \langle b\rangle = \langle a+b\rangle + \langle ab(a+b)\rangle$. -/
theorem gG_add (a b : Kˣ) (hab : (a : K) + b ≠ 0) :
    (gG a : G K) + gG b = gG (Units.mk0 _ hab) + gG (a * b * Units.mk0 _ hab) := by
  unfold gG; rw [← map_add, ← map_add, unary_add_unary a b hab]

/-- Relation (i) in $W(k)$. -/
theorem gW_sq (a b : Kˣ) : gW (a * b ^ 2) = (gW a : W K) := by
  unfold gW; rw [gG_sq]

/-- Relation (ii) in $W(k)$. -/
theorem gW_add (a b : Kˣ) (hab : (a : K) + b ≠ 0) :
    (gW a : W K) + gW b = gW (Units.mk0 _ hab) + gW (a * b * Units.mk0 _ hab) := by
  unfold gW; rw [← map_add, ← map_add, gG_add a b hab]

/-- The hyperbolic plane is zero in $W(k)$. -/
theorem toW_hyp : toW K (toG K (hyp K)) = 0 := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_zmultiples _

/-- $\langle c\rangle + \langle -c\rangle = 0$ in $W(k)$. -/
theorem gW_add_neg (c : Kˣ) : (gW c : W K) + gW (-c) = 0 := by
  unfold gW gG
  rw [← map_add, ← map_add, ← star_unary, unary_add_star]
  exact toW_hyp

section Twist

variable {A : Type*} [AddCommGroup A] (g : Kˣ → A)

/-- Relation (i) for $a \mapsto g(ca)$. -/
theorem twist_rel1 (h₁ : ∀ a b : Kˣ, g (a * b ^ 2) = g a) (c : Kˣ) :
    ∀ a b : Kˣ, (fun a => g (c * a)) (a * b ^ 2) = (fun a => g (c * a)) a := by
  intro a b
  show g (c * (a * b ^ 2)) = g (c * a)
  rw [← mul_assoc, h₁]

/-- Relation (ii) for $a \mapsto g(ca)$. -/
theorem twist_rel2
    (h₁ : ∀ a b : Kˣ, g (a * b ^ 2) = g a)
    (h₂ : ∀ (a b : Kˣ) (hab : (a : K) + b ≠ 0),
      g a + g b = g (Units.mk0 _ hab) + g (a * b * Units.mk0 _ hab)) (c : Kˣ) :
    ∀ (a b : Kˣ) (hab : (a : K) + b ≠ 0),
      (fun a => g (c * a)) a + (fun a => g (c * a)) b =
        (fun a => g (c * a)) (Units.mk0 _ hab) + (fun a => g (c * a)) (a * b * Units.mk0 _ hab) := by
  intro a b hab
  have hcab : ((c * a : Kˣ) : K) + (c * b : Kˣ) ≠ 0 := by
    rw [Units.val_mul, Units.val_mul, ← mul_add]; exact mul_ne_zero c.ne_zero hab
  show g (c * a) + g (c * b) = g (c * Units.mk0 _ hab) + g (c * (a * b * Units.mk0 _ hab))
  rw [h₂ (c * a) (c * b) hcab]
  have e1 : (Units.mk0 _ hcab : Kˣ) = c * Units.mk0 _ hab := Units.ext (by simp [mul_add])
  have e2 : c * a * (c * b) * Units.mk0 _ hcab = c * (a * b * Units.mk0 _ hab) * c ^ 2 :=
    Units.ext (by simp [mul_add]; ring)
  rw [e2, e1, h₁]

end Twist

/-! ### Extensionality and induction -/

/-- Two homomorphisms out of $G(k)$ agreeing on all $\langle a\rangle$ are equal. -/
theorem G_hom_ext {H : Type*} [AddCommGroup H] (φ ψ : G K →+ H)
    (h : ∀ a : Kˣ, φ (gG a) = ψ (gG a)) : φ = ψ := by
  obtain ⟨_, _, hu⟩ := G_lift (K := K) (fun a => ψ (gG a))
    (fun a b => congrArg ψ (gG_sq a b))
    (fun a b hab => by
      show ψ (gG a) + ψ (gG b) = ψ (gG _) + ψ (gG _)
      rw [← map_add, ← map_add]; exact congrArg ψ (gG_add a b hab))
  exact (hu φ h).trans (hu ψ fun _ => rfl).symm

/-- Two homomorphisms out of $W(k)$ agreeing on all $\langle a\rangle$ are equal. -/
theorem W_hom_ext {H : Type*} [AddCommGroup H] (φ ψ : W K →+ H)
    (h : ∀ a : Kˣ, φ (gW a) = ψ (gW a)) : φ = ψ :=
  QuotientAddGroup.addMonoidHom_ext _ (G_hom_ext _ _ h)

/-- Every element of $G(k)$ is in the subgroup generated by the $\langle a\rangle$. -/
theorem mem_closure_gG (x : G K) : x ∈ AddSubgroup.closure (Set.range (gG (K := K))) := by
  let T := AddSubgroup.closure (Set.range (gG (K := K)))
  have h : (QuotientAddGroup.mk' T) = (0 : G K →+ G K ⧸ T) :=
    G_hom_ext _ _ fun a =>
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨a, rfl⟩)
  exact (QuotientAddGroup.eq_zero_iff x).mp (DFunLike.congr_fun h x)

/-- Every element of $W(k)$ is in the subgroup generated by the $\langle a\rangle$. -/
theorem mem_closure_gW (x : W K) : x ∈ AddSubgroup.closure (Set.range (gW (K := K))) := by
  let T := AddSubgroup.closure (Set.range (gW (K := K)))
  have h : (QuotientAddGroup.mk' T) = (0 : W K →+ W K ⧸ T) :=
    W_hom_ext _ _ fun a =>
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨a, rfl⟩)
  exact (QuotientAddGroup.eq_zero_iff x).mp (DFunLike.congr_fun h x)

/-- Induction on $G(k)$ over the generators $\langle a\rangle$. -/
theorem G_induction {P : G K → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hneg : ∀ x, P x → P (-x)) (hgen : ∀ a, P (gG a)) (x : G K) : P x := by
  refine AddSubgroup.closure_induction (p := fun x _ => P x) (fun y hy => ?_) h0
    (fun x y _ _ => hadd x y) (fun x _ => hneg x) (mem_closure_gG x)
  obtain ⟨a, rfl⟩ := hy
  exact hgen a

/-- Induction on $W(k)$ over the generators $\langle a\rangle$. -/
theorem W_induction {P : W K → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hneg : ∀ x, P x → P (-x)) (hgen : ∀ a, P (gW a)) (x : W K) : P x := by
  refine AddSubgroup.closure_induction (p := fun x _ => P x) (fun y hy => ?_) h0
    (fun x y _ _ => hadd x y) (fun x _ => hneg x) (mem_closure_gW x)
  obtain ⟨a, rfl⟩ := hy
  exact hgen a

/-! ### The product on $G(k)$ -/

/-- Multiplication by $\langle c\rangle$ on $G(k)$: the homomorphism with $\langle a\rangle \mapsto \langle ca\rangle$. -/
def mulByG (c : Kˣ) : G K →+ G K :=
  (G_lift (K := K) (fun a => gG (c * a)) (twist_rel1 gG gG_sq c)
    (twist_rel2 gG gG_sq gG_add c)).exists.choose

theorem mulByG_gen (c a : Kˣ) : mulByG c (gG a) = (gG (c * a) : G K) :=
  (G_lift (K := K) (fun a => gG (c * a)) (twist_rel1 gG gG_sq c)
    (twist_rel2 gG gG_sq gG_add c)).exists.choose_spec a

/-- The product on $G(k)$ as a biadditive map, with $\langle a\rangle\langle b\rangle = \langle ab\rangle$. -/
def mulG : G K →+ G K →+ G K :=
  (G_lift (K := K) (fun c => mulByG c)
    (fun a b => G_hom_ext _ _ fun x => by
      rw [mulByG_gen, mulByG_gen, mul_right_comm, gG_sq])
    (fun a b hab => G_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByG_gen]
      have := twist_rel2 gG gG_sq gG_add x a b hab
      simpa only [mul_comm x] using this)).exists.choose

theorem mulG_gen_aux (c : Kˣ) : mulG (gG c) = (mulByG c : G K →+ G K) :=
  (G_lift (K := K) (fun c => mulByG c)
    (fun a b => G_hom_ext _ _ fun x => by
      rw [mulByG_gen, mulByG_gen, mul_right_comm, gG_sq])
    (fun a b hab => G_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByG_gen]
      have := twist_rel2 gG gG_sq gG_add x a b hab
      simpa only [mul_comm x] using this)).exists.choose_spec c

/-- $\langle a\rangle\langle b\rangle = \langle ab\rangle$ in $G(k)$. -/
theorem mulG_gen (a b : Kˣ) : mulG (gG a) (gG b) = (gG (a * b) : G K) := by
  rw [mulG_gen_aux, mulByG_gen]

instance : Mul (G K) := ⟨fun x y => mulG x y⟩

instance : One (G K) := ⟨gG 1⟩

theorem G_mul_def (x y : G K) : x * y = mulG x y := rfl

theorem G_mul_gen (a b : Kˣ) : (gG a : G K) * gG b = gG (a * b) := mulG_gen a b

theorem G_one_def : (1 : G K) = gG 1 := rfl

theorem G_mul_add (x y z : G K) : x * (y + z) = x * y + x * z := map_add (mulG x) y z

theorem G_add_mul (x y z : G K) : (x + y) * z = x * z + y * z := by
  simp only [G_mul_def, map_add, AddMonoidHom.add_apply]

theorem G_zero_mul (x : G K) : 0 * x = 0 := by simp [G_mul_def]

theorem G_mul_zero (x : G K) : x * 0 = 0 := by simp [G_mul_def]

theorem G_neg_mul (x y : G K) : -x * y = -(x * y) := by simp [G_mul_def]

theorem G_mul_neg (x y : G K) : x * -y = -(x * y) := by simp [G_mul_def]

theorem G_mul_comm (x y : G K) : x * y = y * x := by
  induction x using G_induction generalizing y with
  | h0 => simp [G_zero_mul, G_mul_zero]
  | hadd x z hx hz => rw [G_add_mul, G_mul_add, hx, hz]
  | hneg x hx => rw [G_neg_mul, G_mul_neg, hx]
  | hgen a =>
    induction y using G_induction with
    | h0 => simp [G_zero_mul, G_mul_zero]
    | hadd x z hx hz => rw [G_add_mul, G_mul_add, hx, hz]
    | hneg x hx => rw [G_neg_mul, G_mul_neg, hx]
    | hgen b => rw [G_mul_gen, G_mul_gen, mul_comm]

theorem G_mul_assoc (x y z : G K) : x * y * z = x * (y * z) := by
  induction x using G_induction generalizing y z with
  | h0 => simp [G_zero_mul]
  | hadd x w hx hw => rw [G_add_mul, G_add_mul, G_add_mul, hx, hw]
  | hneg x hx => rw [G_neg_mul, G_neg_mul, G_neg_mul, hx]
  | hgen a =>
    induction y using G_induction generalizing z with
    | h0 => simp [G_zero_mul, G_mul_zero]
    | hadd x w hx hw => rw [G_add_mul, G_mul_add, G_add_mul, G_mul_add, hx, hw]
    | hneg x hx => rw [G_neg_mul, G_mul_neg, G_neg_mul, G_mul_neg, hx]
    | hgen b =>
      induction z using G_induction with
      | h0 => simp [G_mul_zero]
      | hadd x w hx hw => rw [G_mul_add, G_mul_add, G_mul_add, hx, hw]
      | hneg x hx => simp only [G_mul_neg, hx]
      | hgen c => rw [G_mul_gen, G_mul_gen, G_mul_gen, G_mul_gen, mul_assoc]

theorem G_one_mul (x : G K) : 1 * x = x := by
  induction x using G_induction with
  | h0 => simp [G_mul_zero]
  | hadd x w hx hw => rw [G_mul_add, hx, hw]
  | hneg x hx => rw [G_mul_neg, hx]
  | hgen a => rw [G_one_def, G_mul_gen, one_mul]

/-- **Cassels, Ch. 2, §6, Note, p. 28.** ($\operatorname{char} k \ne 2$.) $G(k)$ is a commutative ring with unit
$\langle 1\rangle$ and product determined by $\langle a\rangle\langle b\rangle = \langle ab\rangle$ (`mulG_gen`); its
additive group is the Grothendieck group already constructed.

Deviation: Cassels defines the product by the tensor product of spaces; here it is defined on the generators,
$\langle a\rangle\cdot\langle b\rangle = \langle ab\rangle$, which is the class of $\langle a\rangle \otimes
\langle b\rangle$; the two agree since both are biadditive. -/
@[kb "cassels1978" "Ch. 2, §6, Note, p. 28 (ring structure on G(k), W(k))"]
instance instCommRingG : CommRing (G K) :=
  { (inferInstance : AddCommGroup (G K)) with
    mul := (· * ·)
    one := 1
    left_distrib := G_mul_add
    right_distrib := G_add_mul
    zero_mul := G_zero_mul
    mul_zero := G_mul_zero
    mul_assoc := G_mul_assoc
    one_mul := G_one_mul
    mul_one := fun x => by rw [G_mul_comm, G_one_mul]
    mul_comm := G_mul_comm }

/-! ### The product on $W(k)$ -/

/-- Multiplication by $\langle c\rangle$ on $W(k)$: the homomorphism with $\langle a\rangle \mapsto \langle ca\rangle$. -/
def mulByW (c : Kˣ) : W K →+ W K :=
  (W_lift (K := K) (fun a => gW (c * a)) (twist_rel1 gW gW_sq c)
    (twist_rel2 gW gW_sq gW_add c)
    (by
      show gW (c * 1) + gW (c * -1) = (0 : W K)
      rw [mul_one, mul_neg_one]; exact gW_add_neg c)).exists.choose

theorem mulByW_gen (c a : Kˣ) : mulByW c (gW a) = (gW (c * a) : W K) :=
  (W_lift (K := K) (fun a => gW (c * a)) (twist_rel1 gW gW_sq c)
    (twist_rel2 gW gW_sq gW_add c)
    (by
      show gW (c * 1) + gW (c * -1) = (0 : W K)
      rw [mul_one, mul_neg_one]; exact gW_add_neg c)).exists.choose_spec a

/-- The product on $W(k)$ as a biadditive map, with $\langle a\rangle\langle b\rangle = \langle ab\rangle$. -/
def mulW : W K →+ W K →+ W K :=
  (W_lift (K := K) (fun c => mulByW c)
    (fun a b => W_hom_ext _ _ fun x => by
      rw [mulByW_gen, mulByW_gen, mul_right_comm, gW_sq])
    (fun a b hab => W_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByW_gen]
      have := twist_rel2 gW gW_sq gW_add x a b hab
      simpa only [mul_comm x] using this)
    (W_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByW_gen, AddMonoidHom.zero_apply]
      rw [one_mul, neg_one_mul]; exact gW_add_neg x)).exists.choose

theorem mulW_gen_aux (c : Kˣ) : mulW (gW c) = (mulByW c : W K →+ W K) :=
  (W_lift (K := K) (fun c => mulByW c)
    (fun a b => W_hom_ext _ _ fun x => by
      rw [mulByW_gen, mulByW_gen, mul_right_comm, gW_sq])
    (fun a b hab => W_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByW_gen]
      have := twist_rel2 gW gW_sq gW_add x a b hab
      simpa only [mul_comm x] using this)
    (W_hom_ext _ _ fun x => by
      simp only [AddMonoidHom.add_apply, mulByW_gen, AddMonoidHom.zero_apply]
      rw [one_mul, neg_one_mul]; exact gW_add_neg x)).exists.choose_spec c

/-- $\langle a\rangle\langle b\rangle = \langle ab\rangle$ in $W(k)$. -/
theorem mulW_gen (a b : Kˣ) : mulW (gW a) (gW b) = (gW (a * b) : W K) := by
  rw [mulW_gen_aux, mulByW_gen]

instance : Mul (W K) := ⟨fun x y => mulW x y⟩

instance : One (W K) := ⟨gW 1⟩

theorem W_mul_def (x y : W K) : x * y = mulW x y := rfl

theorem W_mul_gen (a b : Kˣ) : (gW a : W K) * gW b = gW (a * b) := mulW_gen a b

theorem W_one_def : (1 : W K) = gW 1 := rfl

theorem W_mul_add (x y z : W K) : x * (y + z) = x * y + x * z := map_add (mulW x) y z

theorem W_add_mul (x y z : W K) : (x + y) * z = x * z + y * z := by
  simp only [W_mul_def, map_add, AddMonoidHom.add_apply]

theorem W_zero_mul (x : W K) : 0 * x = 0 := by simp [W_mul_def]

theorem W_mul_zero (x : W K) : x * 0 = 0 := by simp [W_mul_def]

theorem W_neg_mul (x y : W K) : -x * y = -(x * y) := by simp [W_mul_def]

theorem W_mul_neg (x y : W K) : x * -y = -(x * y) := by simp [W_mul_def]

theorem W_mul_comm (x y : W K) : x * y = y * x := by
  induction x using W_induction generalizing y with
  | h0 => simp [W_zero_mul, W_mul_zero]
  | hadd x z hx hz => rw [W_add_mul, W_mul_add, hx, hz]
  | hneg x hx => rw [W_neg_mul, W_mul_neg, hx]
  | hgen a =>
    induction y using W_induction with
    | h0 => simp [W_zero_mul, W_mul_zero]
    | hadd x z hx hz => rw [W_add_mul, W_mul_add, hx, hz]
    | hneg x hx => rw [W_neg_mul, W_mul_neg, hx]
    | hgen b => rw [W_mul_gen, W_mul_gen, mul_comm]

theorem W_mul_assoc (x y z : W K) : x * y * z = x * (y * z) := by
  induction x using W_induction generalizing y z with
  | h0 => simp [W_zero_mul]
  | hadd x w hx hw => rw [W_add_mul, W_add_mul, W_add_mul, hx, hw]
  | hneg x hx => rw [W_neg_mul, W_neg_mul, W_neg_mul, hx]
  | hgen a =>
    induction y using W_induction generalizing z with
    | h0 => simp [W_zero_mul, W_mul_zero]
    | hadd x w hx hw => rw [W_add_mul, W_mul_add, W_add_mul, W_mul_add, hx, hw]
    | hneg x hx => rw [W_neg_mul, W_mul_neg, W_neg_mul, W_mul_neg, hx]
    | hgen b =>
      induction z using W_induction with
      | h0 => simp [W_mul_zero]
      | hadd x w hx hw => rw [W_mul_add, W_mul_add, W_mul_add, hx, hw]
      | hneg x hx => simp only [W_mul_neg, hx]
      | hgen c => rw [W_mul_gen, W_mul_gen, W_mul_gen, W_mul_gen, mul_assoc]

theorem W_one_mul (x : W K) : 1 * x = x := by
  induction x using W_induction with
  | h0 => simp [W_mul_zero]
  | hadd x w hx hw => rw [W_mul_add, hx, hw]
  | hneg x hx => rw [W_mul_neg, hx]
  | hgen a => rw [W_one_def, W_mul_gen, one_mul]

/-- **Cassels, Ch. 2, §6, Note, p. 28.** ($\operatorname{char} k \ne 2$.) $W(k)$ is a commutative ring with unit
$\langle 1\rangle$ and product determined by $\langle a\rangle\langle b\rangle = \langle ab\rangle$ (`mulW_gen`); its
additive group is the Witt group already constructed.

Deviation: Cassels defines the product by the tensor product of spaces; here it is defined on the generators,
$\langle a\rangle\cdot\langle b\rangle = \langle ab\rangle$, which is the class of $\langle a\rangle \otimes
\langle b\rangle$; the two agree since both are biadditive. -/
@[kb "cassels1978" "Ch. 2, §6, Note, p. 28 (ring structure on G(k), W(k))"]
instance instCommRingW : CommRing (W K) :=
  { (inferInstance : AddCommGroup (W K)) with
    mul := (· * ·)
    one := 1
    left_distrib := W_mul_add
    right_distrib := W_add_mul
    zero_mul := W_zero_mul
    mul_zero := W_mul_zero
    mul_assoc := W_mul_assoc
    one_mul := W_one_mul
    mul_one := fun x => by rw [W_mul_comm, W_one_mul]
    mul_comm := W_mul_comm }

/-- The quotient map $G(k) \to W(k)$ is multiplicative: $\bar{xy} = \bar x\,\bar y$. -/
theorem toW_mul (x y : G K) : toW K (x * y) = toW K x * toW K y := by
  induction x using G_induction generalizing y with
  | h0 => simp
  | hadd x z hx hz => rw [G_add_mul, map_add, map_add, W_add_mul, hx, hz]
  | hneg x hx => rw [G_neg_mul, map_neg, map_neg, W_neg_mul, hx]
  | hgen a =>
    induction y using G_induction with
    | h0 => simp
    | hadd x z hx hz => rw [G_mul_add, map_add, map_add, W_mul_add, hx, hz]
    | hneg x hx => rw [G_mul_neg, map_neg, map_neg, W_mul_neg, hx]
    | hgen b =>
      rw [G_mul_gen]
      exact (W_mul_gen a b).symm

/-- **Cassels, Ch. 2, §6, Note, p. 28.** The quotient map $G(k) \to W(k)$ as a ring homomorphism. -/
@[kb "cassels1978" "Ch. 2, §6, Note, p. 28 (ring structure on G(k), W(k))"]
def toWRingHom : G K →+* W K where
  toFun := toW K
  map_one' := rfl
  map_mul' := toW_mul
  map_zero' := map_zero _
  map_add' := map_add _

end QuadFormsKB.Cassels
