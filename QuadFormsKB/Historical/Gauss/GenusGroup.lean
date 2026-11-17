import QuadFormsKB.Historical.Gauss.GeneraCount
import QuadFormsKB.Historical.Gauss.Duplication

/-!
# Genera as cosets of the principal genus (Disquisitiones Arithmeticae, Arts. 287, 303, 307)

(Art. 303, Euler's idoneal numbers: one class in each genus iff every class is
ambiguous) (Art. 307 III-IV: the genera containing ambiguous classes; the order of a class outside
the principal genus) (Art. 287, end: all assignable characters occur, in the negative and the
improperly primitive orders too, in local form) and (Art. 307 VII, the presentation of the class
group of a regular determinant; stated).

**Conventions.** The proper classes of primitive forms of a nonzero discriminant $D$ (positive and negative forms
together when $D < 0$) form the group `Composition.FormClass D` (Cassels, Ch. 14). Gauss's properly primitive forms
$(a, b, c)$ of determinant $D$ are the primitive forms of discriminant $4D$ (`Forms.lean`); his improperly primitive
forms $(a, b, c)$ ($a$, $c$ even, $\gcd(a, b, c) = 1$, determinant $D \equiv 1 \pmod 4$) are twice the primitive forms
$\frac a2 x^2 + bxy + \frac c2 y^2$ of discriminant $D$. Two forms are in the same **genus** when they are equivalent
over $\mathbb R$ and over every $\mathbb Z_p$ (`Siegel.SameGenus`; for primitive forms this is Gauss's "same complete
character", Arts. 229-231, by the local classification of binary forms, which is not re-proved here).

**The bridge** (`globalToLocal_mk_eq_iff`): two primitive forms of discriminant $D$ are in the same genus iff their
classes have the same image under Cassels's homomorphism $\mathcal G \to \prod_{p \mid 2D} \mathcal G_p \times
\mathcal G_\infty$ (`Composition.globalToLocal`). Hence the principal genus is the kernel, which is the subgroup of
squares by Gauss's duplication theorem (`ker_globalToLocal_eq_sq`, from `Composition.thm_3_1`), and the genera are
the cosets of the subgroup of squares (`sameGenus_iff_mul_inv_sq`). This is the identification asked for in loose end
a recorded loose end for the genera themselves (not for Gauss's individual characters).

An **ambiguous class** (Gauss, Art. 163/165) is a class equal to its opposite, i.e. $C = C^{-1}$, i.e. $C^2 = 1$
(the inverse class is the class of $[a, -b, c]$, `Composition.FormClass.mk_inv`).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition FormClass

variable {D : ℤ} [NonzeroDisc D]

/-! ### The bridge: genera are fibres of `globalToLocal` -/

theorem localHom_mk_eq_iff (p : ℕ) [Fact p.Prime] (f g : PrimForm D) :
    localHom p D (mk f) = localHom p D (mk g) ↔
      Siegel.IsometricGL (f.1.map (Int.castRingHom ℤ_[p])) (g.1.map (Int.castRingHom ℤ_[p])) := by
  rw [localHom_mk, localHom_mk]
  exact ⟨fun h => localClasses_exact (F := toLocalPrim p D f) (G := toLocalPrim p D g)
      ((localEquiv p D).injective h),
    fun h => congrArg (localEquiv p D) (localClasses_sound (F := toLocalPrim p D f) (G := toLocalPrim p D g) h)⟩

theorem realHom_mk_eq_iff (f g : PrimForm D) :
    realHom D (mk f) = realHom D (mk g) ↔
      Siegel.IsometricGL (f.1.map (Int.castRingHom ℝ)) (g.1.map (Int.castRingHom ℝ)) := by
  rw [realHom_mk, realHom_mk]
  exact ⟨fun h => Quotient.exact (s := realSetoid D) (a := toRealForm D f) (b := toRealForm D g)
      ((realEquiv D).injective h),
    fun h => congrArg (realEquiv D) (Quotient.sound (s := realSetoid D) (a := toRealForm D f)
      (b := toRealForm D g) h)⟩

theorem local_iso_of_not_mem (p : ℕ) [Fact p.Prime] (hp : p ∉ PrimesDvd D) (f g : PrimForm D) :
    Siegel.IsometricGL (f.1.map (Int.castRingHom ℤ_[p])) (g.1.map (Int.castRingHom ℤ_[p])) := by
  obtain ⟨hp2, hpD⟩ := odd_not_dvd_of_not_mem D p hp
  have hcard := card_localClasses_odd_of_not_dvd hp2 (NonzeroDisc.mod_four (D := D)) hpD
  have hsub : Subsingleton (LocalClasses p D) := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact localClasses_exact (p := p) (F := toLocalPrim p D f) (G := toLocalPrim p D g)
    (@Subsingleton.elim (LocalClasses p D) hsub _ _)

/-- **Same genus = same local data** (bridge between `Siegel.SameGenus` and Cassels's homomorphism (5.2)): for
primitive forms $f, g$ of discriminant $D \ne 0$, $f$ and $g$ are in the same genus (equivalent over $\mathbb R$ and
over every $\mathbb Z_p$) iff their classes have the same image in
$\prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$. -/
theorem globalToLocal_mk_eq_iff (f g : PrimForm D) :
    globalToLocal D (mk f) = globalToLocal D (mk g) ↔ Siegel.SameGenus f.1 g.1 := by
  constructor
  · intro h
    refine ⟨fun p _ => ?_, ?_⟩
    · by_cases hp : p ∈ PrimesDvd D
      · have h1 : localHom p D (mk f) = localHom p D (mk g) :=
          congrFun (congrArg Prod.fst h) ⟨p, hp⟩
        exact (localHom_mk_eq_iff p f g).1 h1
      · exact local_iso_of_not_mem p hp f g
    · exact (realHom_mk_eq_iff f g).1 (congrArg Prod.snd h)
  · intro hg
    refine Prod.ext (funext fun p => ?_) ?_
    · exact (localHom_mk_eq_iff p.1 f g).2 (hg.1 p.1)
    · exact (realHom_mk_eq_iff f g).2 hg.2

/-- **The principal genus is the kernel of `globalToLocal`:** a primitive form of discriminant $D$ lies in the
principal genus iff its class has trivial local data. -/
theorem globalToLocal_mk_eq_one_iff (f : PrimForm D) :
    globalToLocal D (mk f) = 1 ↔ InPrincipalGenus f.1 := by
  rw [← map_one (globalToLocal D), one_def, globalToLocal_mk_eq_iff, InPrincipalGenus, f.2.2]
  rfl

/-- **The principal genus is the subgroup of squares** (Gauss, *Disq. Arith.* Arts. 286-287, through Cassels,
Ch. 14, Thm. 3.1, `Composition.thm_3_1`): a class has trivial local data iff it is a square. -/
theorem globalToLocal_eq_one_iff_sq (C : FormClass D) :
    globalToLocal D C = 1 ↔ ∃ C₁ : FormClass D, C₁ ^ 2 = C := by
  obtain ⟨f, rfl⟩ := mk_surjective C
  rw [globalToLocal_mk_eq_one_iff, thm_3_1]

/-- The subgroup of squares $\mathcal G^2$ (the image of $C \mapsto C^2$). -/
noncomputable abbrev sqSubgroup (D : ℤ) [NonzeroDisc D] : Subgroup (FormClass D) := (powMonoidHom 2 : FormClass D →* _).range

/-- The subgroup of ambiguous classes $\{C : C^2 = 1\}$ (Gauss's ambiguous classes, $C = C^{-1}$). -/
noncomputable abbrev ambSubgroup (D : ℤ) [NonzeroDisc D] : Subgroup (FormClass D) := (powMonoidHom 2 : FormClass D →* _).ker

theorem ker_globalToLocal_eq_sq : MonoidHom.ker (G := FormClass D) (globalToLocal D) = sqSubgroup D := by
  ext C
  rw [MonoidHom.mem_ker, globalToLocal_eq_one_iff_sq, MonoidHom.mem_range]
  rfl

/-- **Genera are the cosets of the principal genus:** two primitive forms of discriminant $D$ are in the same genus
iff the quotient of their classes is a square. -/
theorem sameGenus_iff_mul_inv_sq (f g : PrimForm D) :
    Siegel.SameGenus f.1 g.1 ↔ ∃ C₁ : FormClass D, C₁ ^ 2 = mk f * (mk g)⁻¹ := by
  rw [← globalToLocal_mk_eq_iff, ← globalToLocal_eq_one_iff_sq, map_mul, map_inv]
  exact (_root_.mul_inv_eq_one (G := LocalProd D)).symm

/-! ### Art. 303: idoneal numbers -/

/-- **Gauss, *Disq. Arith.* Art. 303 (Euler's idoneal numbers):** for a nonzero
discriminant $D$ the following are equivalent:

0. every genus of primitive forms of discriminant $D$ consists of a single (proper) class;
1. every class is ambiguous ($C^2 = 1$ for every class $C$: the class group is an elementary abelian $2$-group);
2. any two forms of one genus are both properly equivalent and improperly equivalent (properly equivalent to the
   opposite form $[a, -b, c]$, `Binary.conjForm`).

Gauss's idoneal numbers $n$ are the case $D = -4n$ of Gauss's determinant $-n$. *Deviations:* Gauss counts positive
forms only; here positive and negative forms are counted together (for $D < 0$ a genus consists of forms of one sign,
and $f \mapsto -f$ preserves genera and classes, so this is the same condition; that last step is not formalized). The
list of the $65$ known idoneal numbers (Gauss: "it is easily seen"; a computation, and the completeness of the list is
open) is not formalized. -/
@[kb "gauss1801" "Art. 303"]
theorem art303_idoneal :
    List.TFAE [∀ f g : PrimForm D, Siegel.SameGenus f.1 g.1 → SLEquiv f.1 g.1,
      ∀ C : FormClass D, C ^ 2 = 1,
      ∀ f g : PrimForm D, Siegel.SameGenus f.1 g.1 → SLEquiv f.1 g.1 ∧ SLEquiv f.1 (conjForm g.1)] := by
  tfae_have 1 → 2 := by
    intro h C
    obtain ⟨f, hf⟩ := mk_surjective (C ^ 2)
    · rw [← hf]
      have hsq : Siegel.SameGenus f.1 (principal D).1 := by
        rw [sameGenus_iff_mul_inv_sq, ← one_def, inv_one, mul_one]
        exact ⟨C, hf.symm⟩
      rw [one_def]
      exact mk_eq_mk.2 (h _ _ hsq)
  tfae_have 2 → 1 := by
    intro h f g hfg
    obtain ⟨C₁, hC₁⟩ := (sameGenus_iff_mul_inv_sq f g).1 hfg
    rw [h C₁, eq_comm, mul_inv_eq_one] at hC₁
    exact mk_eq_mk.1 hC₁
  tfae_have 2 → 3 := by
    intro h f g hfg
    have h1 : SLEquiv f.1 g.1 := by
      obtain ⟨C₁, hC₁⟩ := (sameGenus_iff_mul_inv_sq f g).1 hfg
      rw [h C₁, eq_comm, mul_inv_eq_one] at hC₁
      exact mk_eq_mk.1 hC₁
    refine ⟨h1, ?_⟩
    have hg : (mk g)⁻¹ = mk g := by
      rw [inv_eq_iff_mul_eq_one, ← sq]; exact h _
    rw [mk_inv] at hg
    have := (mk_eq_mk.1 hg).symm
    exact h1.trans this
  tfae_have 3 → 1 := fun h f g hfg => (h f g hfg).1
  tfae_finish

/-! ### Art. 307 III-IV -/

/-- In a finite group, an element that is not a square has even order. -/
theorem even_orderOf_of_not_sq {G : Type*} [Group G] [Finite G] {x : G} (hx : ¬ ∃ y, y ^ 2 = x) :
    Even (orderOf x) := by
  by_contra h
  rw [Nat.not_even_iff_odd] at h
  obtain ⟨k, hk⟩ := h
  apply hx
  refine ⟨x ^ (k + 1), ?_⟩
  rw [← pow_mul, show (k + 1) * 2 = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]

/-- **Gauss, *Disq. Arith.* Art. 307 IV:** the order (period) of a class $C$ outside the
principal genus is twice the order of $C^2$, and it divides $2n$, where $n$ is the number of classes of the
principal genus. -/
@[kb "gauss1801" "Art. 307 IV"]
theorem art307_order_not_principal (f : PrimForm D) (hf : ¬ InPrincipalGenus f.1) :
    orderOf (mk f) = 2 * orderOf (mk f ^ 2) ∧ orderOf (mk f) ∣ 2 * Nat.card (sqSubgroup D) := by
  have hns : ¬ ∃ C₁ : FormClass D, C₁ ^ 2 = mk f := by rwa [thm_3_1]
  obtain ⟨k, hk⟩ := even_orderOf_of_not_sq hns
  have h1 : orderOf (mk f) = 2 * orderOf (mk f ^ 2) := by
    rw [orderOf_pow' _ two_ne_zero, hk, show k + k = 2 * k by ring,
      show (2 * k).gcd 2 = 2 from Nat.gcd_eq_right (dvd_mul_right 2 k), Nat.mul_div_cancel_left k two_pos]
  refine ⟨h1, ?_⟩
  rw [h1]
  refine Nat.mul_dvd_mul_left 2 ?_
  have hmem : mk f ^ 2 ∈ sqSubgroup D := ⟨mk f, rfl⟩
  rw [← Subgroup.orderOf_mk (mk f ^ 2) hmem]
  exact orderOf_dvd_natCard _

/-- In a finite commutative group $G$, with $A = \{x : x^2 = 1\}$ and $S = G^2$: the image of $A$ in $G / S$ has index
$\#(A \cap S)$. -/
theorem index_map_amb {G : Type*} [CommGroup G] [Finite G] :
    (((powMonoidHom 2 : G →* G).ker).map (QuotientGroup.mk' (powMonoidHom 2 : G →* G).range)).index =
      Nat.card ↥((powMonoidHom 2 : G →* G).ker ⊓ (powMonoidHom 2 : G →* G).range) := by
  set φ := (powMonoidHom 2 : G →* G)
  set A := φ.ker
  set S := φ.range
  -- |G| = |A| |S|
  have hGAS : Nat.card G = Nat.card A * Nat.card S := by
    rw [← Subgroup.card_mul_index A, Subgroup.index_ker]
  -- the image of A in G/S has cardinality |A| / |A ⊓ S|
  have hker : ((QuotientGroup.mk' S).comp A.subtype).ker = S.subgroupOf A := by
    ext x; simp [Subgroup.mem_subgroupOf]
  have himg : Nat.card (A.map (QuotientGroup.mk' S)) * Nat.card ↥(A ⊓ S) = Nat.card A := by
    have e1 : A.map (QuotientGroup.mk' S) = ((QuotientGroup.mk' S).comp A.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have e2 : Nat.card ↥(A ⊓ S) = Nat.card (S.subgroupOf A) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective A.subtype_injective]
    rw [e1, e2, ← hker, mul_comm, ← Subgroup.card_mul_index ((QuotientGroup.mk' S).comp A.subtype).ker,
      Subgroup.index_ker]
  have hpos : 0 < Nat.card ↥(A ⊓ S) := Nat.card_pos
  have hpos' : 0 < Nat.card (A.map (QuotientGroup.mk' S)) := Nat.card_pos
  have hq : Nat.card (G ⧸ S) * Nat.card S = Nat.card G := by
    rw [mul_comm]; exact (Subgroup.card_mul_index S)
  have hidx := Subgroup.card_mul_index (A.map (QuotientGroup.mk' S))
  have hSpos : 0 < Nat.card S := Nat.card_pos
  -- |G/S| = |A|
  have hGS : Nat.card (G ⧸ S) = Nat.card A := by
    have : Nat.card (G ⧸ S) * Nat.card S = Nat.card A * Nat.card S := by rw [hq, hGAS]
    exact Nat.eq_of_mul_eq_mul_right hSpos this
  rw [hGS, ← himg] at hidx
  exact Nat.eq_of_mul_eq_mul_left hpos' (by rw [hidx])

/-- **Gauss, *Disq. Arith.* Art. 307 III:** in the group of genera $\mathcal G / \mathcal
G^2$ (the classes modulo the principal genus, `ker_globalToLocal_eq_sq`), the genera containing ambiguous classes form
a subgroup of index equal to the number of ambiguous classes in the principal genus. In particular, when the principal
genus contains exactly two ambiguous classes (Gauss's hypothesis), that subgroup has index $2$. -/
@[kb "gauss1801" "Art. 307 III"]
theorem art307_ambiguous_genera_index :
    ((ambSubgroup D).map (QuotientGroup.mk' (sqSubgroup D))).index = Nat.card ↥(ambSubgroup D ⊓ sqSubgroup D) :=
  index_map_amb

/-- Art. 307 III with Gauss's hypothesis: two ambiguous classes in the principal genus give index $2$. -/
@[kb "gauss1801" "Art. 307 III"]
theorem art307_ambiguous_genera_index_two (h : Nat.card ↥(ambSubgroup D ⊓ sqSubgroup D) = 2) :
    ((ambSubgroup D).map (QuotientGroup.mk' (sqSubgroup D))).index = 2 :=
  art307_ambiguous_genera_index.trans h

/-! ### Art. 287, end: existence of the genera, in local form -/

/-- **Gauss, *Disq. Arith.* Art. 287, end, in local form (wrapper of
`Composition.range_eq_ker`, Cassels, Ch. 14, Thm. 5.1):** for every nonzero discriminant $D$, every family of local
classes $x \in \prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$ satisfying the one condition allowed by Arts.
263-264 and 274 (the product of the Hasse invariants is $1$, `Composition.hasseProd`) is the local data of a class.
The component at $\infty$ is the sign of the forms when $D < 0$, so this covers Gauss's negative properly primitive
order; with $D \equiv 1 \pmod 4$ it covers his improperly primitive order ($(a, b, c)$ with $a, c$ even is twice the
primitive form $\frac a2 x^2 + bxy + \frac c2 y^2$ of discriminant $D$). Gauss's species $P$ / $Q$ of characters are
not formalized; `Composition.hasseProd` plays their role. -/
@[kb "gauss1801" "Art. 287, end"]
theorem art287_all_genera_occur (x : LocalProd D) (hx : hasseProd D x = 1) :
    ∃ C : FormClass D, globalToLocal D C = x := by
  have : x ∈ MonoidHom.range (G := FormClass D) (N := LocalProd D) (globalToLocal D) := by
    rw [range_eq_ker]; exact hx
  exact this

/-- **Art. 287, end, counting:** for a nonsquare discriminant $D$ (in particular for Gauss's
improperly primitive order, $D \equiv 1 \pmod 4$ his determinant), the genera are exactly half of the a priori
possible local data (wrapper of `Composition.thm_5_1_nonsquare`). -/
@[kb "gauss1801" "Art. 287, end"]
theorem art287_half_genera (hD : ¬ IsSquare D) :
    Nat.card (MonoidHom.range (G := FormClass D) (N := LocalProd D) (globalToLocal D)) * 2 =
      Nat.card (LocalProd D) := by
  rw [← thm_5_1_nonsquare (D := D) hD]
  exact Subgroup.card_mul_index _

/-! ### Art. 307 VII (stated) -/

/-- **Gauss, *Disq. Arith.* Art. 307 VII, stated:** for a *regular* discriminant $D$ (the
principal genus, i.e. the subgroup of squares, is cyclic), with $2^{\mu}$ genera, there are a class $E$ whose powers
contain the principal genus and ambiguous classes $A_0, \dots, A_{\mu - 2}$ such that every class is
$E^k \prod_{i \in I} A_i$ for some $k$ and some set $I$ of indices. (Gauss's worked tables for $-161$ and $-546$ are
not formalized.) Stated, not proved: the proof needs the structure of finite abelian groups with cyclic subgroup of
squares (loose end). -/
@[kb "gauss1801" "Art. 307 VII"]
def Art307RegularPresentation (D : ℤ) [NonzeroDisc D] : Prop :=
  IsCyclic (sqSubgroup D) →
    ∀ μ : ℕ, Nat.card (FormClass D ⧸ sqSubgroup D) = 2 ^ μ →
      ∃ (E : FormClass D) (A : Fin (μ - 1) → FormClass D),
        (∀ C ∈ sqSubgroup D, C ∈ Subgroup.zpowers E) ∧ (∀ i, A i ^ 2 = 1) ∧
        ∀ C : FormClass D, ∃ (k : ℕ) (I : Finset (Fin (μ - 1))), C = E ^ k * ∏ i ∈ I, A i

end QuadFormsKB.Historical.Gauss
