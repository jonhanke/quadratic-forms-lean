/-
# Chenevier–Lannes, §1.3 and §3.2: the Kneser–Hecke operators $T_p$ commute on every $X_n$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.3, p. 6 ("The $T_p$ commute and are self-adjoint for a suitable
inner product on $\mathbb{R}[X_n]$"), and §3.2, p. 55 (the Remarks: $T_A$ and $T_B$ commute; the book proves this in
Chapter 4 through the commutativity of the Hecke ring). Printed page numbers.

**What is proved.** `heckeCommute n : HeckeCommute n` for every $n$ and for **all** primes $p, q$ (including $2$),
unconditionally: for every function $f : X_n \to \mathbb{C}$ and every class $x \in X_n$,
$T_p(T_qf)(x) = T_q(T_pf)(x)$. The proof is the elementary lattice argument (not the Hecke ring of Chapter 4):

1. For $p \ne q$ the matrix product of neighbour numbers is a count of chains,
   $\sum_y N_p(x,y)\,N_q(y,z) = \#\{(L', M) : L' \text{ a } p\text{-neighbour of } L,\ M \text{ a } q\text{-neighbour of } L',\
   [M] = z\}$ for $L$ a representative of $x$ (`sum_nbNum_mul`; the number of $q$-neighbours of $L'$ in the class $z$
   depends only on the class of $L'$, transported along a basis of $L'$, `card_nbMid`).
2. In a chain $L \overset{p}{-} L' \overset{q}{-} M$ one has $L' = pL + qM$ (`chain_eq`: from $pL' \subseteq L$,
   $qL' \subseteq M$, $pL \subseteq L'$, $qM \subseteq L'$ and $\gcd(p^2, q^2) = 1$), so $M$ determines $L'$, and
   $M' = qL + pM$ is a $q$-neighbour of $L$ of which $M$ is a $p$-neighbour (`square_adj`, `step_swap`; integrality of $M'$
   because $pq\,M \subseteq L$ and $L$ is integral).
3. Hence $(L', M) \mapsto (M', M)$ is a bijection between $p$-then-$q$ chains and $q$-then-$p$ chains with the same
   endpoint class (`natCard_swap`), so $\sum_y N_p(x,y)N_q(y,z) = \sum_y N_q(x,y)N_p(y,z)$ (`sum_nbNum_comm`).

No unimodularity beyond the inputs of `NeighborsTwo.lean` is used; the case $p = q$ is trivial.
-/
import QuadFormsKB.Literature.ChenevierLannes.NeighborsTwo
import QuadFormsKB.Literature.ChenevierLannes.Wave3.HeckeSixteen

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

namespace HeckeCommute060

/-! ### Adjacency of lattices (pure module theory) -/

section Lattice

variable {V : Type*} [AddCommGroup V]

/-- **$r$-adjacency:** $[A : A \cap B] = r = [B : A \cap B]$ (the first two conditions of `IsNeighbor`, for arbitrary
lattices $A$, $B$ in place of $\mathbb{Z}^n$ and $L'$). -/
def Adj (r : ℕ) (A B : Submodule ℤ V) : Prop :=
  B.toAddSubgroup.relIndex A.toAddSubgroup = r ∧ A.toAddSubgroup.relIndex B.toAddSubgroup = r

theorem Adj.symm {r : ℕ} {A B : Submodule ℤ V} (h : Adj r A B) : Adj r B A := ⟨h.2, h.1⟩

/-- If $[A : A \cap B] = r$ then $r A \subseteq B$ (Lagrange in $A/(A \cap B)$). -/
theorem smul_mem_of_relIndex {A B : Submodule ℤ V} {r : ℕ}
    (h : B.toAddSubgroup.relIndex A.toAddSubgroup = r) {x : V} (hx : x ∈ A) : (r : ℤ) • x ∈ B := by
  have h1 := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup)
    (show x ∈ A.toAddSubgroup from hx)
  rw [h] at h1
  rw [natCast_zsmul]
  exact h1

theorem bezout1 {p q : ℕ} (h : Nat.Coprime p q) : ∃ a b : ℤ, a * p + b * q = 1 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  exact ⟨a, b, hab⟩

theorem bezout2 {p q : ℕ} (h : Nat.Coprime p q) : ∃ a b : ℤ, a * (p : ℤ) ^ 2 + b * (q : ℤ) ^ 2 = 1 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow 2 2 h)
  refine ⟨a, b, ?_⟩
  push_cast at hab
  exact hab

/-- **Transfer of an index along multiplication by $u$:** if $u\cdot$ induces a bijection
$A/(A \cap B) \to C/(C \cap D)$ then $[A : A \cap B] = [C : C \cap D]$. -/
theorem relIndex_eq_of_smul {A B C D : Submodule ℤ V} (u : ℤ)
    (h1 : ∀ x ∈ A, u • x ∈ C)
    (h2 : ∀ x ∈ A, x ∈ B → u • x ∈ D)
    (h3 : ∀ x ∈ A, u • x ∈ D → x ∈ B)
    (h4 : ∀ y ∈ C, ∃ x ∈ A, y - u • x ∈ D) :
    B.toAddSubgroup.relIndex A.toAddSubgroup = D.toAddSubgroup.relIndex C.toAddSubgroup := by
  let φ : A.toAddSubgroup →+ C.toAddSubgroup :=
    { toFun := fun x => ⟨u • (x : V), h1 (x : V) x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  let f : A.toAddSubgroup →+ C.toAddSubgroup ⧸ (D.toAddSubgroup.addSubgroupOf C.toAddSubgroup) :=
    (QuotientAddGroup.mk' _).comp φ
  have hker : f.ker = B.toAddSubgroup.addSubgroupOf A.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    show (QuotientAddGroup.mk (φ x) : C.toAddSubgroup ⧸ _) = 0 ↔ (x : V) ∈ B.toAddSubgroup
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨fun h => h3 (x : V) x.2 h, fun h => h2 (x : V) x.2 h⟩
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hx, hxc⟩ := h4 (c : V) c.2
    refine ⟨⟨x, hx⟩, ?_⟩
    show (QuotientAddGroup.mk (φ ⟨x, hx⟩) : C.toAddSubgroup ⧸ _) = QuotientAddGroup.mk c
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(u • x) + (c : V) ∈ D
    rw [neg_add_eq_sub]
    exact hxc
  have hcard := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  rw [hker] at hcard
  exact hcard

/-- **The lattice $r A + s B$.** -/
def comb (r s : ℤ) (A B : Submodule ℤ V) : Submodule ℤ V where
  carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = r • a + s • b}
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨a + a', A.add_mem ha ha', b + b', B.add_mem hb hb', by simp only [smul_add]; abel⟩
  zero_mem' := ⟨0, A.zero_mem, 0, B.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨c • a, A.smul_mem c ha, c • b, B.smul_mem c hb, by rw [smul_add, smul_comm c r a, smul_comm c s b]⟩

theorem mem_comb {r s : ℤ} {A B : Submodule ℤ V} {x : V} :
    x ∈ comb r s A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = r • a + s • b := Iff.rfl

theorem comb_comm (r s : ℤ) (A B : Submodule ℤ V) : comb r s A B = comb s r B A := by
  ext x
  simp only [mem_comb]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, add_comm _ _⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, add_comm _ _⟩

/-- **A chain determines its middle lattice:** if $L \overset{p}{-} L' \overset{q}{-} M$ with $\gcd(p, q) = 1$ then
$L' = pL + qM$. -/
theorem chain_eq {p q : ℕ} (hpq : Nat.Coprime p q) {L L' M : Submodule ℤ V}
    (h1 : Adj p L L') (h2 : Adj q L' M) : L' = comb (p : ℤ) (q : ℤ) L M := by
  obtain ⟨a, b, hab⟩ := bezout2 hpq
  ext x
  constructor
  · intro hx
    have hpx : (p : ℤ) • x ∈ L := smul_mem_of_relIndex h1.2 hx
    have hqx : (q : ℤ) • x ∈ M := smul_mem_of_relIndex h2.1 hx
    refine mem_comb.mpr ⟨a • ((p : ℤ) • x), L.smul_mem a hpx, b • ((q : ℤ) • x), M.smul_mem b hqx, ?_⟩
    have e : (p : ℤ) • (a • ((p : ℤ) • x)) + (q : ℤ) • (b • ((q : ℤ) • x)) =
        (a * (p : ℤ) ^ 2 + b * (q : ℤ) ^ 2) • x := by module
    rw [e, hab, one_smul]
  · intro hx
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_comb.mp hx
    exact L'.add_mem (smul_mem_of_relIndex h1.1 ha₁) (smul_mem_of_relIndex h2.2 hb₁)

/-- **The square:** if $X \overset{p}{-} Y \overset{q}{-} Z$ with $\gcd(p, q) = 1$, then $W = qX + pZ$ is
$q$-adjacent to $X$. (The indices $[X : X \cap W]$ and $[W : X \cap W]$ are transported to $[Y : Y \cap Z]$ and
$[Z : Y \cap Z]$ by multiplication by $u = ap$, where $ap + bq = 1$.) -/
theorem square_adj {p q : ℕ} (hpq : Nat.Coprime p q) {X Y Z : Submodule ℤ V}
    (h1 : Adj p X Y) (h2 : Adj q Y Z) : Adj q X (comb (q : ℤ) (p : ℤ) X Z) := by
  obtain ⟨a, b, hab⟩ := bezout1 hpq
  have F1 : ∀ x ∈ X, (p : ℤ) • x ∈ Y := fun x hx => smul_mem_of_relIndex h1.1 hx
  have F2 : ∀ x ∈ Y, (p : ℤ) • x ∈ X := fun x hx => smul_mem_of_relIndex h1.2 hx
  have F3 : ∀ x ∈ Y, (q : ℤ) • x ∈ Z := fun x hx => smul_mem_of_relIndex h2.1 hx
  have F4 : ∀ x ∈ Z, (q : ℤ) • x ∈ Y := fun x hx => smul_mem_of_relIndex h2.2 hx
  have hmem : ∀ w, w ∈ comb (q : ℤ) (p : ℤ) X Z ↔ ∃ a ∈ X, ∃ b ∈ Z, w = (q : ℤ) • a + (p : ℤ) • b :=
    fun w => Iff.rfl
  generalize comb (q : ℤ) (p : ℤ) X Z = W at hmem ⊢
  have hu : ∀ w ∈ W, (a * (p : ℤ)) • w ∈ Z := by
    intro w hw
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (hmem w).mp hw
    have t1 : (q : ℤ) • ((p : ℤ) • a₁) ∈ Z := F3 _ (F1 _ ha₁)
    have e : (a * (p : ℤ)) • ((q : ℤ) • a₁ + (p : ℤ) • b₁) =
        a • ((q : ℤ) • ((p : ℤ) • a₁)) + (a * p * p) • b₁ := by module
    rw [e]
    exact Z.add_mem (Z.smul_mem a t1) (Z.smul_mem _ hb₁)
  have hq : ∀ w ∈ W, (q : ℤ) • w ∈ X := by
    intro w hw
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (hmem w).mp hw
    have t1 : (p : ℤ) • ((q : ℤ) • b₁) ∈ X := F2 _ (F4 _ hb₁)
    have e : (q : ℤ) • ((q : ℤ) • a₁ + (p : ℤ) • b₁) =
        ((q : ℤ) * q) • a₁ + (p : ℤ) • ((q : ℤ) • b₁) := by module
    rw [e]
    exact X.add_mem (X.smul_mem _ ha₁) t1
  refine ⟨?_, ?_⟩
  · -- `[X : X ∩ W] = [Y : Y ∩ Z] = q`
    have h1' : ∀ x ∈ X, (a * (p : ℤ)) • x ∈ Y := fun x hx => by
      rw [mul_smul]; exact Y.smul_mem a (F1 x hx)
    have h2' : ∀ x ∈ X, x ∈ W → (a * (p : ℤ)) • x ∈ Z := fun x _ hxW => hu x hxW
    have h3' : ∀ x ∈ X, (a * (p : ℤ)) • x ∈ Z → x ∈ W := by
      intro x hx hxZ
      have hyX : (a * (p : ℤ)) • x ∈ X := X.smul_mem _ hx
      refine (hmem x).mpr ⟨b • ((a * (p : ℤ)) • x) + b • x, X.add_mem (X.smul_mem b hyX) (X.smul_mem b hx),
        a • ((a * (p : ℤ)) • x), Z.smul_mem a hxZ, ?_⟩
      have e : (q : ℤ) • (b • ((a * (p : ℤ)) • x) + b • x) + (p : ℤ) • (a • ((a * (p : ℤ)) • x)) =
          ((q : ℤ) * (b * (a * p)) + q * b + p * (a * (a * p))) • x := by module
      have hS : (q : ℤ) * (b * (a * p)) + q * b + p * (a * (a * p)) = 1 := by
        linear_combination (a * (p : ℤ) + 1) * hab
      rw [e, hS, one_smul]
    have h4' : ∀ y ∈ Y, ∃ x ∈ X, y - (a * (p : ℤ)) • x ∈ Z := by
      intro y hy
      refine ⟨a • ((p : ℤ) • y), X.smul_mem a (F2 y hy), ?_⟩
      have e' : y - (a * (p : ℤ)) • (a • ((p : ℤ) • y)) = (1 - (a * p) * (a * p)) • y := by module
      have hS : (1 - (a * (p : ℤ)) * (a * p)) = q * (b * (1 + a * p)) := by
        linear_combination (-(1 + a * (p : ℤ))) * hab
      rw [e', hS, mul_smul]
      exact F3 _ (Y.smul_mem _ hy)
    have := relIndex_eq_of_smul (A := X) (B := W) (C := Y) (D := Z) (a * (p : ℤ)) h1' h2' h3' h4'
    exact this.trans h2.1
  · -- `[W : W ∩ X] = [Z : Z ∩ Y] = q`
    have g2 : ∀ w ∈ W, w ∈ X → (a * (p : ℤ)) • w ∈ Y := fun w _ hw => by
      rw [mul_smul]; exact Y.smul_mem a (F1 w hw)
    have g3 : ∀ w ∈ W, (a * (p : ℤ)) • w ∈ Y → w ∈ X := by
      intro w hw hy
      have hqw := hq w hw
      have h5 : (a * (p : ℤ)) • w ∈ X := by
        have e' : a • ((p : ℤ) • ((a * (p : ℤ)) • w)) + ((a * p) * b) • ((q : ℤ) • w) =
            (a * (p * (a * p)) + (a * p) * b * q) • w := by module
        have hS : a * ((p : ℤ) * (a * p)) + (a * p) * b * q = a * p := by
          linear_combination (a * (p : ℤ)) * hab
        have e : (a * (p : ℤ)) • w = a • ((p : ℤ) • ((a * (p : ℤ)) • w)) + ((a * p) * b) • ((q : ℤ) • w) := by
          rw [e', hS]
        rw [e]
        exact X.add_mem (X.smul_mem a (F2 _ hy)) (X.smul_mem _ hqw)
      have e2 : w = (a * (p : ℤ)) • w + b • ((q : ℤ) • w) := by
        have e' : (a * (p : ℤ)) • w + b • ((q : ℤ) • w) = (a * p + b * q) • w := by module
        rw [e', hab, one_smul]
      rw [e2]
      exact X.add_mem h5 (X.smul_mem b hqw)
    have g4 : ∀ z ∈ Z, ∃ w ∈ W, z - (a * (p : ℤ)) • w ∈ Y := by
      intro z hz
      refine ⟨(p : ℤ) • (a • z), (hmem _).mpr ⟨0, X.zero_mem, a • z, Z.smul_mem a hz, by simp⟩, ?_⟩
      have e' : z - (a * (p : ℤ)) • ((p : ℤ) • (a • z)) = (1 - (a * p) * (p * a)) • z := by module
      have hS : (1 - (a * (p : ℤ)) * (p * a)) = q * (b * (1 + a * p)) := by
        linear_combination (-(1 + a * (p : ℤ))) * hab
      rw [e', hS, mul_smul]
      exact F4 _ (Z.smul_mem _ hz)
    have := relIndex_eq_of_smul (A := W) (B := X) (C := Z) (D := Y) (a * (p : ℤ)) hu g2 g3 g4
    exact this.trans h2.2

end Lattice

/-! ### Neighbours of a lattice in $\mathbb{Q}^n$ and chains of neighbours -/

variable {n : ℕ}

/-- **$r$-neighbours of an arbitrary lattice $A$** for the form $Q$: $B$ is $r$-adjacent to $A$ and $Q$ is
$\mathbb{Z}$-valued on $B$. For $A = \mathbb{Z}^n$ this is `IsNeighbor`. -/
def IsNb (Q : QuadForm ℤ n) (r : ℕ) (A B : Submodule ℤ (Fin n → ℚ)) : Prop :=
  Adj r A B ∧ ∀ x ∈ B, ∃ z : ℤ, Q.evalIn ℚ x = z

theorem isNeighbor_iff_isNb {Q : QuadForm ℤ n} {r : ℕ} {L : Submodule ℤ (Fin n → ℚ)} :
    IsNeighbor Q r L ↔ IsNb Q r (stdLat n) L :=
  ⟨fun h => ⟨⟨h.relIndex_std, h.relIndex_self⟩, h.integral⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **Integrality of $qL + pM$:** if $Q$ is $\mathbb{Z}$-valued on $\mathbb{Z}^n$ (automatic for an integral form) and
on $M$, and $pq\,M \subseteq \mathbb{Z}^n$, then $Q$ is $\mathbb{Z}$-valued on $q\mathbb{Z}^n + pM$, because
$Q(qa + pb) = q^2Q(a) + pq\,B(a, b) + p^2Q(b)$. -/
theorem integral_comb (Q : QuadForm ℤ n) {p q : ℕ} {M : Submodule ℤ (Fin n → ℚ)}
    (hM : ∀ x ∈ M, ∃ z : ℤ, Q.evalIn ℚ x = z)
    (hpq : ∀ x ∈ M, ((p : ℤ) * q) • x ∈ stdLat n) :
    ∀ x ∈ comb (q : ℤ) (p : ℤ) (stdLat n) M, ∃ z : ℤ, Q.evalIn ℚ x = z := by
  intro x hx
  obtain ⟨a, ⟨y, rfl⟩, b, hb, rfl⟩ := mem_comb.mp hx
  obtain ⟨zb, hzb⟩ := hM b hb
  obtain ⟨w, hw⟩ := hpq b hb
  rw [← Int.cast_smul_eq_zsmul ℚ] at hw
  push_cast at hw
  have e1 : (q : ℤ) • cv y + (p : ℤ) • b = (q : ℚ) • cv y + (p : ℚ) • b := by
    simp only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  have hb2 : ((p : ℚ) * q) * bQ Q (cv y) b = (bZ Q y w : ℚ) := by
    rw [← bQ_smul_right, hw, bQ_cv]
  refine ⟨(q : ℤ) ^ 2 * Q.eval y + bZ Q y w + (p : ℤ) ^ 2 * zb, ?_⟩
  rw [e1, evalIn_add_smulQ, evalIn_smulQ, bQ_smul_left, evalIn_cv, hzb]
  push_cast
  linear_combination hb2

/-- **Swapping the order of a chain:** if $\mathbb{Z}^n \overset{p}{-} L' \overset{q}{-} M$ is a chain of neighbours
($p \ne q$ primes, so coprime) then $M' = q\mathbb{Z}^n + pM$ is a $q$-neighbour of $\mathbb{Z}^n$ and $M$ is a
$p$-neighbour of $M'$. -/
theorem step_swap (Q : QuadForm ℤ n) {p q : ℕ} (hpq : Nat.Coprime p q) {L' M : Submodule ℤ (Fin n → ℚ)}
    (h1 : IsNeighbor Q p L') (h2 : IsNb Q q L' M) :
    IsNeighbor Q q (comb (q : ℤ) (p : ℤ) (stdLat n) M) ∧ IsNb Q p (comb (q : ℤ) (p : ℤ) (stdLat n) M) M := by
  have h1' : Adj p (stdLat n) L' := (isNeighbor_iff_isNb.mp h1).1
  have hA : Adj q (stdLat n) (comb (q : ℤ) (p : ℤ) (stdLat n) M) := square_adj hpq h1' h2.1
  have hB : Adj p M (comb (p : ℤ) (q : ℤ) M (stdLat n)) := square_adj hpq.symm h2.1.symm h1'.symm
  rw [comb_comm] at hB
  have hint : ∀ x ∈ M, ((p : ℤ) * q) • x ∈ stdLat n := by
    intro x hx
    rw [mul_smul]
    exact smul_mem_of_relIndex h1'.2 (smul_mem_of_relIndex h2.1.2 hx)
  exact ⟨isNeighbor_iff_isNb.mpr ⟨hA, integral_comb Q h2.2 hint⟩, hB.symm, h2.2⟩

/-! ### Transport of lattices along $g \in \mathrm{GL}_n(\mathbb{Q})$ -/

/-- The image $gL$ of a lattice $L \subseteq \mathbb{Q}^n$. -/
noncomputable def tr (g : GL (Fin n) ℚ) (L : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℚ) :=
  L.map ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) ℚ)).restrictScalars ℤ)

theorem mem_tr {g : GL (Fin n) ℚ} {L : Submodule ℤ (Fin n → ℚ)} {x : Fin n → ℚ} :
    x ∈ tr g L ↔ ∃ y ∈ L, (g : Matrix (Fin n) (Fin n) ℚ) *ᵥ y = x := by
  simp [tr, Submodule.mem_map]

theorem mulVec_inv_mulVec (g : GL (Fin n) ℚ) (x : Fin n → ℚ) :
    ((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mulVec_mulVec_inv (g : GL (Fin n) ℚ) (x : Fin n → ℚ) :
    (g : Matrix (Fin n) (Fin n) ℚ) *ᵥ (((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem tr_inv_tr (g : GL (Fin n) ℚ) (L : Submodule ℤ (Fin n → ℚ)) : tr g⁻¹ (tr g L) = L := by
  ext x
  constructor
  · intro hx
    obtain ⟨_, hy, rfl⟩ := mem_tr.mp hx
    obtain ⟨y, hyL, rfl⟩ := mem_tr.mp hy
    rw [mulVec_inv_mulVec]
    exact hyL
  · intro hx
    exact mem_tr.mpr ⟨_, mem_tr.mpr ⟨x, hx, rfl⟩, mulVec_inv_mulVec g x⟩

theorem tr_tr_inv (g : GL (Fin n) ℚ) (L : Submodule ℤ (Fin n → ℚ)) : tr g (tr g⁻¹ L) = L := by
  have := tr_inv_tr g⁻¹ L
  rwa [inv_inv] at this

theorem tr_injective (g : GL (Fin n) ℚ) :
    Function.Injective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) ℚ)).toAddMonoidHom := by
  intro x y hxy
  have := congrArg (fun w => ((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ w) hxy
  simpa [mulVec_mulVec, ← Units.val_mul] using this

theorem toAddSubgroup_tr (g : GL (Fin n) ℚ) (L : Submodule ℤ (Fin n → ℚ)) :
    (tr g L).toAddSubgroup =
      L.toAddSubgroup.map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) ℚ)).toAddMonoidHom := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_tr, AddSubgroup.mem_map]
  simp

theorem tr_adj (g : GL (Fin n) ℚ) {r : ℕ} {A B : Submodule ℤ (Fin n → ℚ)} :
    Adj r (tr g A) (tr g B) ↔ Adj r A B := by
  unfold Adj
  rw [toAddSubgroup_tr g A, toAddSubgroup_tr g B,
    AddSubgroup.relIndex_map_map_of_injective _ _ (tr_injective g),
    AddSubgroup.relIndex_map_map_of_injective _ _ (tr_injective g)]

theorem tr_std (g : GL (Fin n) ℚ) : tr g (stdLat n) = imgLat (g : Matrix (Fin n) (Fin n) ℚ) := by
  ext x
  rw [mem_tr, mem_imgLat]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨cv c, ⟨c, rfl⟩, rfl⟩

theorem imgLat_mul_eq_tr (g : GL (Fin n) ℚ) (H : Matrix (Fin n) (Fin n) ℚ) :
    imgLat ((g : Matrix (Fin n) (Fin n) ℚ) * H) = tr g (imgLat H) := by
  ext x
  rw [mem_tr, mem_imgLat]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨H *ᵥ cv c, ⟨c, rfl⟩, by rw [mulVec_mulVec]⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [mulVec_mulVec]⟩

theorem isNb_tr {Q Q₁ : QuadForm ℤ n} {g : GL (Fin n) ℚ}
    (hG : ∀ x, Q₁.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x))
    {r : ℕ} {A B : Submodule ℤ (Fin n → ℚ)} : IsNb Q r (tr g A) (tr g B) ↔ IsNb Q₁ r A B := by
  unfold IsNb
  rw [tr_adj]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · obtain ⟨z, hz⟩ := h _ (mem_tr.mpr ⟨y, hy, rfl⟩)
    exact ⟨z, by rw [hG]; exact hz⟩
  · obtain ⟨y, hy, rfl⟩ := mem_tr.mp hx
    obtain ⟨z, hz⟩ := h y hy
    exact ⟨z, by rw [← hG]; exact hz⟩

theorem hG_inv {Q Q₁ : QuadForm ℤ n} {g : GL (Fin n) ℚ}
    (hG : ∀ x, Q₁.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)) :
    ∀ x, Q.evalIn ℚ x = Q₁.evalIn ℚ (((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) := by
  intro x
  rw [hG, mulVec_mulVec_inv]

theorem hasClass_tr {Q Q₁ : QuadForm ℤ n} (g : GL (Fin n) ℚ)
    (hG : ∀ x, Q₁.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x))
    {L : Submodule ℤ (Fin n → ℚ)} {z : QClass n} (h : hasClass Q₁ L z) : hasClass Q (tr g L) z := by
  obtain ⟨h₀, hL, Q'', hz, hQ''⟩ := h
  refine ⟨g * h₀, ?_, Q'', hz, fun x => ?_⟩
  · rw [Units.val_mul, imgLat_mul_eq_tr, hL]
  · rw [hQ'' x, hG, Units.val_mul, mulVec_mulVec]

/-- **A basis of a neighbour with a prescribed Gram form:** if $L$ has class $[Q']$ for the form $Q$, then
$L = g\mathbb{Z}^n$ with $Q'(\vec{x}) = Q(g\vec{x})$ exactly (not only up to an isometry). -/
theorem exists_base {Q Q' : QuadForm ℤ n} {L : Submodule ℤ (Fin n → ℚ)} (hL : hasClass Q L (classOf Q')) :
    ∃ g : GL (Fin n) ℚ, imgLat (g : Matrix (Fin n) (Fin n) ℚ) = L ∧
      ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) := by
  obtain ⟨g₁, hg₁, Q'', hcl, hQ''⟩ := hL
  obtain ⟨v, hv⟩ := classOf_eq_classOf_iff.mp hcl
  refine ⟨g₁ * toGLQ v, ?_, fun x => ?_⟩
  · rw [Units.val_mul, imgLat_mul_toGLQ, hg₁]
  · rw [Units.val_mul, ← mulVec_mulVec, ← hQ'', toGLQ_val, evalIn_rat_of_int hv]

/-! ### The number of $q$-neighbours of a neighbour depends only on its class -/

open Classical in
/-- **The $q$-neighbours of a lattice $L'$ of class $[Q_y]$** (with $L'$ a $p$-neighbour of $\mathbb{Z}^n$, $Q$ even
unimodular, $Q_y$ even unimodular): the $q$-neighbours $M$ of $L'$ inside $(\mathbb{Q}^n, Q)$ with class $z$ are in
bijection, via $M \mapsto g^{-1}M$ for a basis $g$ of $L'$ with Gram form $Q_y$, with the $q$-neighbours of $\mathbb{Z}^n$
for $Q_y$ of class $z$; there are `nbCount Qy q z` of them. -/
theorem card_nbMid {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {p : ℕ} [Fact p.Prime]
    {L' : Submodule ℤ (Fin n → ℚ)} (hL' : L' ∈ neighbors Q p) {Qy : QuadForm ℤ n}
    (hQy : IsEvenUnimodular Qy) (hcl : classOf Qy = nbClass Q L') (q : ℕ) [Fact q.Prime] (z : QClass n) :
    Finite {M // IsNb Q q L' M ∧ hasClass Q M z} ∧
      Nat.card {M // IsNb Q q L' M ∧ hasClass Q M z} = nbCount Qy q z := by
  have hcls : hasClass Q L' (classOf Qy) := by
    rw [hcl]
    exact ((nbClass_spec_unimod hQ hL').2 _).mpr rfl
  obtain ⟨g, hgL, hgQ⟩ := exists_base hcls
  have hgQ' := hG_inv hgQ
  have key : ∀ L : Submodule ℤ (Fin n → ℚ),
      (L ∈ (neighbors Qy q).filter (fun L => nbClass Qy L = z)) ↔
        (IsNb Q q L' (tr g L) ∧ hasClass Q (tr g L) z) := by
    intro L
    rw [Finset.mem_filter]
    have hnb : L ∈ neighbors Qy q ↔ IsNb Q q L' (tr g L) := by
      rw [mem_neighbors_iff (not_dvd_det hQy q), isNeighbor_iff_isNb, ← isNb_tr hgQ, tr_std, hgL]
    have hcls_iff : L ∈ neighbors Qy q → (hasClass Qy L z ↔ hasClass Q (tr g L) z) := by
      intro _
      refine ⟨hasClass_tr g hgQ, fun h => ?_⟩
      have := hasClass_tr g⁻¹ hgQ' h
      rwa [tr_inv_tr] at this
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hnb.mp h1, (hcls_iff h1).mp (((nbClass_spec_unimod hQy h1).2 z).mpr h2)⟩
    · rintro ⟨h1, h2⟩
      have h1' := hnb.mpr h1
      exact ⟨h1', ((nbClass_spec_unimod hQy h1').2 z).mp ((hcls_iff h1').mpr h2)⟩
  let E : {L // L ∈ (neighbors Qy q).filter (fun L => nbClass Qy L = z)} ≃
      {M // IsNb Q q L' M ∧ hasClass Q M z} :=
    Equiv.subtypeEquiv
      { toFun := tr g, invFun := tr g⁻¹, left_inv := tr_inv_tr g, right_inv := tr_tr_inv g } key
  refine ⟨Finite.of_equiv _ E, ?_⟩
  rw [← Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-! ### Counting chains -/

/-- The set of chains $\mathbb{Z}^n \overset{p}{-} L' \overset{q}{-} M$ with $[M] = z$. -/
abbrev Chain (Q : QuadForm ℤ n) (p q : ℕ) [Fact p.Prime] (z : QClass n) : Type :=
  Σ L' : ↥(neighbors Q p), {M // IsNb Q q L'.1 M ∧ hasClass Q M z}

open Classical in
/-- **The matrix product of neighbour numbers counts chains**: for $x \in X_n$ with chosen representative $Q$,
$\sum_y N_p(x, y)\,N_q(y, z) = \#\{\text{chains } \mathbb{Z}^n \overset{p}{-} L' \overset{q}{-} M,\ [M] = z\}$. -/
theorem sum_nbNum_mul {x : QClass n} (hx : x ∈ classSet n) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (z : QClass n) :
    ∑ y ∈ (classSet_finite n).toFinset, nbNum p x y * nbNum q y z =
      Nat.card (Chain (Quotient.out (s := intSetoid n) x) p q z) := by
  have hQ := out_isEvenUnimodular hx
  set Q := Quotient.out (s := intSetoid n) x with hQdef
  have hmid : ∀ L' ∈ neighbors Q p, Finite {M // IsNb Q q L' M ∧ hasClass Q M z} ∧
      Nat.card {M // IsNb Q q L' M ∧ hasClass Q M z} = nbNum q (nbClass Q L') z := by
    intro L' hL'
    have hyc : nbClass Q L' ∈ classSet n := by
      rw [classSet_eq_genusClasses hQ]
      exact (nbClass_spec_unimod hQ hL').1
    exact card_nbMid hQ hL' (out_isEvenUnimodular hyc) (Quotient.out_eq _) q z
  have : ∀ L' : ↥(neighbors Q p), Finite {M // IsNb Q q L'.1 M ∧ hasClass Q M z} :=
    fun L' => (hmid L'.1 L'.2).1
  have e1 : Nat.card (Chain Q p q z) =
      ∑ L' ∈ neighbors Q p, Nat.card {M // IsNb Q q L' M ∧ hasClass Q M z} := by
    rw [Nat.card_sigma]
    exact Finset.sum_coe_sort (neighbors Q p) (fun L' => Nat.card {M // IsNb Q q L' M ∧ hasClass Q M z})
  rw [e1, Finset.sum_congr rfl fun L' hL' => (hmid L' hL').2]
  rw [← Finset.sum_fiberwise_of_maps_to (g := nbClass Q) (s := neighbors Q p)
    (t := (classSet_finite n).toFinset) (f := fun L' => nbNum q (nbClass Q L') z) (fun L hL => by
      rw [Set.Finite.mem_toFinset, classSet_eq_genusClasses hQ]
      exact (nbClass_spec_unimod hQ hL).1)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => nbNum q y z) (fun L hL => by rw [(Finset.mem_filter.mp hL).2]),
    Finset.sum_const, smul_eq_mul]
  rfl

/-- The map $(L', M) \mapsto (qL + pM, M)$ from $p$-then-$q$ chains to $q$-then-$p$ chains. -/
noncomputable def swapMap {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (z : QClass n) : Chain Q p q z → Chain Q q p z := fun x =>
  have hs := step_swap Q hcop ((mem_neighbors_iff (not_dvd_det hQ p)).mp x.1.2) x.2.2.1
  ⟨⟨comb (q : ℤ) (p : ℤ) (stdLat n) x.2.1, (mem_neighbors_iff (not_dvd_det hQ q)).mpr hs.1⟩,
    ⟨x.2.1, hs.2, x.2.2.2⟩⟩

theorem swapMap_swapMap {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (z : QClass n) (x : Chain Q p q z) :
    swapMap hQ hcop.symm z (swapMap hQ hcop z x) = x := by
  refine Sigma.subtype_ext (Subtype.ext ?_) rfl
  have h1 : IsNeighbor Q p x.1.1 := (mem_neighbors_iff (not_dvd_det hQ p)).mp x.1.2
  exact (chain_eq hcop (isNeighbor_iff_isNb.mp h1).1 x.2.2.1.1).symm

/-- **$p$-then-$q$ chains and $q$-then-$p$ chains with the same endpoint class are equinumerous.** -/
theorem natCard_swap {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (z : QClass n) : Nat.card (Chain Q p q z) = Nat.card (Chain Q q p z) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes (Fact.out) (Fact.out)).mpr hpq
  exact Nat.card_congr
    { toFun := swapMap hQ hcop z
      invFun := swapMap hQ hcop.symm z
      left_inv := swapMap_swapMap hQ hcop z
      right_inv := swapMap_swapMap hQ hcop.symm z }

/-- **The neighbour matrices of distinct primes commute:**
$\sum_y N_p(x, y)\,N_q(y, z) = \sum_y N_q(x, y)\,N_p(y, z)$. -/
theorem sum_nbNum_comm {x : QClass n} (hx : x ∈ classSet n) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (z : QClass n) :
    ∑ y ∈ (classSet_finite n).toFinset, nbNum p x y * nbNum q y z =
      ∑ y ∈ (classSet_finite n).toFinset, nbNum q x y * nbNum p y z := by
  rw [sum_nbNum_mul hx p q z, sum_nbNum_mul hx q p z]
  exact natCard_swap (out_isEvenUnimodular hx) hpq z

end HeckeCommute060

/-- **The Kneser–Hecke operators commute on every $X_n$** (Chenevier–Lannes, §1.3, p. 6, and the Remarks of §3.2,
p. 55; all primes $p, q$, including $2$; unconditional): for every $f : X_n \to \mathbb{C}$ and every $x \in X_n$,
$T_p(T_qf)(x) = T_q(T_pf)(x)$. *Proof:* $T_p(T_qf)(x) = \sum_z \bigl(\sum_y N_p(x,y)N_q(y,z)\bigr) f(z)$, and for $p \ne q$
the inner sum counts the chains $L \overset{p}{-} L' \overset{q}{-} M$ with $M$ of class $z$ (`HeckeCommute060.sum_nbNum_mul`);
$(L', M) \mapsto (qL + pM, M)$ is a bijection onto the chains $L \overset{q}{-} M' \overset{p}{-} M$
(`HeckeCommute060.natCard_swap`), since $L' = pL + qM$ (`HeckeCommute060.chain_eq`) and $qL + pM$ is a
$q$-neighbour of $L$ of which $M$ is a $p$-neighbour (`HeckeCommute060.step_swap`). The case $p = q$ is trivial. -/
@[kb "chenevierlannes2019" "§1.3, p. 6; §3.2, p. 55 (the T_p commute)"]
theorem heckeCommute (n : ℕ) : HeckeCommute n := by
  intro p q _ _ f x hx
  by_cases hpq : p = q
  · subst hpq
    rfl
  · have expand : ∀ (p q : ℕ) [Fact p.Prime] [Fact q.Prime], heckeT p (heckeT q f) x =
        ∑ z ∈ (classSet_finite n).toFinset,
          (∑ y ∈ (classSet_finite n).toFinset, nbNum p x y * nbNum q y z) • f z := by
      intro p q _ _
      simp only [heckeT, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    rw [expand p q, expand q p]
    exact Finset.sum_congr rfl fun z _ => by rw [HeckeCommute060.sum_nbNum_comm hx hpq z]

end QuadFormsKB.ChenevierLannes
