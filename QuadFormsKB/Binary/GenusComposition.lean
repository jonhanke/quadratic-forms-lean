import QuadFormsKB.Binary.GenusClassGroup
import QuadFormsKB.Binary.RepresentationCount

/-!
# Gauss composition from forms ↔ ideals: discharging `IsFormClassGroup`

`GenusClassGroup.lean` proves the genus-theory consequences of composition (every genus has $h/2^{t-1}$ classes) from
a named
**interface** `IsFormClassGroup D G cls`. The proper classes are identified with the ideal class group. This file
supplies the interface from that identification, for a fundamental discriminant $D < 0$, with
$G = \mathrm{Cl}(\mathcal O_{K_D})$ and $\mathrm{cls}(f) = [\mathfrak a_f]$ (`isFormClassGroup`), so the class count
becomes **unconditional** (`card_classes_in_genus'`, `card_slClasses_in_genus`).

* **Reconciliation.** the `PosForms D` ($\gcd(a,b,c) = 1$, $a > 0$, $D < 0$) and the `PrimPosForm D` (every common
  divisor of $a, b, c$ is a unit, `BinQF.PosDef`) are the same forms: `primitive_iff_isPrimitive`, `posFormsEquiv`.
* **Genus characters of ideals, computed on norms** (`genusChar_norm_eq_formChar`): if $\mathfrak b \ne 0$ has
  $N\mathfrak b = m$ and $[\mathfrak b] = [\mathfrak a_f]^{-1}$, then $f$ represents $m$ (`exists_gen`,
  `repSetEquiv`), so $\psi_p(m) = \chi_p(f)$ for $p \mid D$, $p \nmid m$ (`genusChar_eval_eq_formChar`).
  Conversely a value of $f$ is the norm of an ideal in $[\mathfrak a_f]^{-1}$ (`exists_ideal_of_eval`).
* **Multiplicativity** (`genusVec_formClass_mul`): if $[\mathfrak a_h] = [\mathfrak a_f][\mathfrak a_g]$, choose ideals
  $\mathfrak b_1 \in [\mathfrak a_f]^{-1}$, $\mathfrak b_2 \in [\mathfrak a_g]^{-1}$ of norms $m_1, m_2$ prime to $D$; then
  $\mathfrak b_1\mathfrak b_2 \in [\mathfrak a_h]^{-1}$ has norm $m_1m_2$ and
  $\chi_p(h) = \psi_p(m_1m_2) = \psi_p(m_1)\psi_p(m_2) = \chi_p(f)\chi_p(g)$. This is the ideal-theoretic form of
  Cox's Lemma 3.17 argument (the composite represents the product of values), with no composition of forms.

Sources: Cox, *Primes of the form $x^2 + ny^2$*, §3.B (Thm. 3.15, Lemma 3.17), §7.B (Thm. 7.7) [unverified locator];
Gauss, *Disq. Arith.* §§234–260, 252; Zagier, *Zetafunktionen und quadratische Körper*, §8 [unverified locator].
-/

open QuadraticAlgebra NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-! ### The two definitions of primitive positive definite forms agree -/

/-- **The two notions of primitivity agree:** the `Primitive f` ($\gcd(a, \gcd(b, c)) = 1$) iff the
`BinQF.IsPrimitive f` (every common divisor of $a, b, c$ is a unit of $\mathbb{Z}$). -/
theorem primitive_iff_isPrimitive (f : BinQF) : Primitive f ↔ f.IsPrimitive := by
  unfold Primitive BinQF.IsPrimitive
  constructor
  · intro h d ha hb hc
    have hd : d ∣ ((Int.gcd f.a (Int.gcd f.b f.c) : ℕ) : ℤ) := Int.dvd_coe_gcd ha (Int.dvd_coe_gcd hb hc)
    rw [h, Nat.cast_one] at hd
    exact isUnit_of_dvd_one hd
  · intro h
    set g := Int.gcd f.a (Int.gcd f.b f.c)
    have hga : (g : ℤ) ∣ f.a := Int.gcd_dvd_left ..
    have hg' : (g : ℤ) ∣ (Int.gcd f.b f.c : ℤ) := Int.gcd_dvd_right ..
    have hgb : (g : ℤ) ∣ f.b := hg'.trans (Int.gcd_dvd_left ..)
    have hgc : (g : ℤ) ∣ f.c := hg'.trans (Int.gcd_dvd_right ..)
    have := Int.isUnit_iff_natAbs_eq.mp (h g hga hgb hgc)
    simpa using this

/-- A form of `PosForms D` as a form of `PrimPosForm D`. -/
def PosForms.toPrim (f : PosForms D) : PrimPosForm D :=
  ⟨f.1, f.2.2.1, (posDef_iff_posDef' _).mpr f.2.2.2, (primitive_iff_isPrimitive _).mp f.2.1⟩

/-- A form of `PrimPosForm D` as a form of `PosForms D`. -/
def PrimPosForm.toPos (f : PrimPosForm D) : PosForms D :=
  ⟨f.1, (primitive_iff_isPrimitive _).mpr f.2.2.2, f.2.1, (posDef_iff_posDef' _).mp f.2.2.1⟩

/-- **`PosForms D` and `PrimPosForm D` are the same set of forms** (primitive positive definite forms of
discriminant $D$); the bijection is the identity on the underlying `BinQF`. -/
def posFormsEquiv : PosForms D ≃ PrimPosForm D where
  toFun := PosForms.toPrim
  invFun := PrimPosForm.toPos
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem PosForms.toPrim_val (f : PosForms D) : f.toPrim.1 = f.1 := rfl
@[simp] theorem PrimPosForm.toPos_val (f : PrimPosForm D) : f.toPos.1 = f.1 := rfl

variable [IsQuadDisc D]

/-! ### The class map -/

/-- **The ideal class of a form** of `PosForms D`, in $\mathrm{Cl}(\mathbb{Z}[\omega])$: $f \mapsto [\mathfrak a_f]$
(the `idealClass`). -/
noncomputable def formClassOrder (f : PosForms D) : ClassGroup (QOrder D) := idealClass f.toPrim

/-- **The ideal class of a form** of `PosForms D`, in $\mathrm{Cl}(\mathcal O_{K_D})$: $f \mapsto [\mathfrak a_f]$,
transported by $\mathbb{Z}[\omega] \cong \mathcal O_{K_D}$ (`classGroupEquiv`). -/
noncomputable def formClass (f : PosForms D) : ClassGroup (𝓞 (QField D)) := classGroupEquiv D (formClassOrder f)

/-! ### Genus characters of ideals, computed on norms -/

/-- **A form represents the norms of the ideals in the inverse of its class** ($D < 0$): if $\mathfrak b \ne 0$,
$N\mathfrak b = m$ and $[\mathfrak b] = [\mathfrak a_f]^{-1}$, then $f(x, y) = m$ for some $x, y \in \mathbb{Z}$ (the
`exists_gen`: $\mathfrak b\,\mathfrak a_f = (z)$ with $N z = a m$, and `repSetEquiv`). -/
theorem exists_eval_of_ideal (hD : D < 0) (f : PrimPosForm D) {m : ℕ} {𝔟 : Ideal (QOrder D)}
    (hN : Ideal.absNorm 𝔟 = m) (h0 : 𝔟 ∈ (Ideal (QOrder D))⁰)
    (hc : ClassGroup.mk0 ⟨𝔟, h0⟩ = (idealClass f)⁻¹) : ∃ x y : ℤ, f.1.eval x y = m := by
  obtain ⟨z, -, -, hz, hNz⟩ := exists_gen hD f (m := m) ⟨𝔟, hN, h0, hc⟩
  set v := (repSetEquiv f m).symm ⟨z, hz, hNz⟩
  have hv := v.2
  simp only [Siegel.repSet, Set.mem_ofPred_eq] at hv
  exact ⟨v.1 0, v.1 1, by rw [BinQF.eval, ← vec_two_eq]; exact hv⟩

/-- **Every value is the norm of an ideal in the inverse class** ($D < 0$): if $f(x, y) = m \ne 0$ then there is
$\mathfrak b \ne 0$ with $N\mathfrak b = m$ and $[\mathfrak b] = [\mathfrak a_f]^{-1}$: $z = xa + y(k_f - \omega) \in \mathfrak a_f$
has $N z = a m$, and $(z) = \mathfrak a_f\mathfrak b$. -/
theorem exists_ideal_of_eval (hD : D < 0) (f : PrimPosForm D) {x y : ℤ} {m : ℕ} (hm : m ≠ 0)
    (hxy : f.1.eval x y = m) :
    ∃ 𝔟 : Ideal (QOrder D), Ideal.absNorm 𝔟 = m ∧
      ∃ h0 : 𝔟 ∈ (Ideal (QOrder D))⁰, ClassGroup.mk0 ⟨𝔟, h0⟩ = (idealClass f)⁻¹ := by
  have ha : f.1.a ≠ 0 := f.a_pos.ne'
  have hmem : ![x, y] ∈ Siegel.repSet f.1 m := by
    simp only [Siegel.repSet, Set.mem_ofPred_eq]; exact hxy
  obtain ⟨z, hz, hN⟩ := repSetEquiv f m ⟨![x, y], hmem⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [QuadraticAlgebra.norm_zero] at hN
    exact mul_ne_zero ha (by exact_mod_cast hm) hN.symm
  obtain ⟨𝔟, h𝔟⟩ : formIdeal D f.1 ∣ Ideal.span {z} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h𝔟
    exact hz0 h𝔟
  have hmem0 : 𝔟 ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔟0
  have hN𝔟 : Ideal.absNorm 𝔟 = m := by
    have e := absNorm_span_singleton_eq hD hz0
    rw [h𝔟, mul_comm, absNorm_mul_formIdeal, hN] at e
    push_cast at e
    rw [abs_of_pos f.a_pos, mul_comm] at e
    exact_mod_cast mul_left_cancel₀ ha e
  refine ⟨𝔟, hN𝔟, hmem0, ?_⟩
  rw [idealClass, ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨z, hz0, by rw [mul_comm]; exact h𝔟.symm⟩

/-- **The genus characters of an ideal class are characters of norms** ($D < 0$ fundamental): if $\mathfrak b \ne 0$ has
norm $m$ and $[\mathfrak b] = [\mathfrak a_f]^{-1}$, then for every prime $p \mid D$ with $p \nmid m$,
$$\psi_p(m) = \chi_p(f).$$
($f$ represents $m$, `exists_eval_of_ideal`, and `genusChar_eval_eq_formChar`.) Source: Cox, §3.B, Lemma 3.17
[unverified locator]; Zagier, §8 [unverified locator]. -/
@[kb "cox2013" "§3.B, Lemma 3.17 and Thm. 3.15 [unverified locator]"]
theorem genusChar_norm_eq_formChar (hD : D < 0) (f : PrimPosForm D) {m : ℕ} {𝔟 : Ideal (QOrder D)}
    (hN : Ideal.absNorm 𝔟 = m) (h0 : 𝔟 ∈ (Ideal (QOrder D))⁰)
    (hc : ClassGroup.mk0 ⟨𝔟, h0⟩ = (idealClass f)⁻¹) {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D)
    (hpm : ¬ (p : ℤ) ∣ m) : genusChar D p m = formChar f.1 p := by
  obtain ⟨x, y, hxy⟩ := exists_eval_of_ideal hD f hN h0 hc
  rw [← hxy]
  exact genusChar_eval_eq_formChar ((primitive_iff_isPrimitive _).mpr f.2.2.2) f.2.1 hp hpD x y (hxy ▸ hpm)

/-- **Every inverse class contains an ideal of norm prime to $D$** ($D < 0$): $f$ represents a value $m \ge 1$ prime
to $D$ (`exists_coprime_value`), which is the norm of an ideal in $[\mathfrak a_f]^{-1}$. -/
theorem exists_coprime_ideal (hD : D < 0) (f : PrimPosForm D) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ D.natAbs → ¬ (p : ℤ) ∣ m) ∧
      ∃ 𝔟 : Ideal (QOrder D), Ideal.absNorm 𝔟 = m ∧
        ∃ h0 : 𝔟 ∈ (Ideal (QOrder D))⁰, ClassGroup.mk0 ⟨𝔟, h0⟩ = (idealClass f)⁻¹ := by
  have hN0 : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
  obtain ⟨x, y, hx, -, -, hcop⟩ :=
    exists_coprime_value ((primitive_iff_isPrimitive _).mpr f.2.2.2) (N := D.natAbs) hN0
  have hpos : 0 < f.1.eval x y := f.2.2.1 x y (by intro h; simp only [Prod.mk.injEq] at h; omega)
  set m := (f.1.eval x y).toNat
  have hm : (m : ℤ) = f.1.eval x y := Int.toNat_of_nonneg hpos.le
  have hm0 : m ≠ 0 := by omega
  refine ⟨m, hm0, fun p hp hpN => hm ▸ hcop p hp hpN, exists_ideal_of_eval hD f hm0 hm.symm⟩

/-- **The genus characters are multiplicative on ideal classes** ($D < 0$ fundamental): if
$[\mathfrak a_h] = [\mathfrak a_f][\mathfrak a_g]$ in $\mathrm{Cl}(\mathbb{Z}[\omega])$ then $\chi_p(h) = \chi_p(f)\chi_p(g)$ for all
$p \mid D$, i.e. the genus vectors multiply. Proof: ideals $\mathfrak b_1 \in [\mathfrak a_f]^{-1}$, $\mathfrak b_2 \in
[\mathfrak a_g]^{-1}$ of norms $m_1, m_2$ prime to $D$ (`exists_coprime_ideal`); $\mathfrak b_1\mathfrak b_2 \in
[\mathfrak a_h]^{-1}$ has norm $m_1m_2$, so $\chi_p(h) = \psi_p(m_1m_2) = \psi_p(m_1)\psi_p(m_2) = \chi_p(f)\chi_p(g)$
(`genusChar_norm_eq_formChar`, `genusChar_mul`). Source: Cox, §3.B, Lemma 3.17 and proof of Thm. 3.15
[unverified locator]. -/
@[kb "cox2013" "§3.B, Lemma 3.17 and proof of Thm. 3.15 [unverified locator]"]
theorem genusVec_formClass_mul (hD : D < 0) (f g h : PosForms D)
    (hcls : formClassOrder h = formClassOrder f * formClassOrder g) :
    genusVec D h.1 = genusVec D f.1 * genusVec D g.1 := by
  obtain ⟨m₁, -, hc₁, 𝔟₁, hN₁, h₁, hk₁⟩ := exists_coprime_ideal hD f.toPrim
  obtain ⟨m₂, -, hc₂, 𝔟₂, hN₂, h₂, hk₂⟩ := exists_coprime_ideal hD g.toPrim
  have hN : Ideal.absNorm (𝔟₁ * 𝔟₂) = m₁ * m₂ := by rw [map_mul, hN₁, hN₂]
  have h0 : 𝔟₁ * 𝔟₂ ∈ (Ideal (QOrder D))⁰ := mul_mem h₁ h₂
  have hk : ClassGroup.mk0 ⟨𝔟₁ * 𝔟₂, h0⟩ = (idealClass h.toPrim)⁻¹ := by
    rw [show (⟨𝔟₁ * 𝔟₂, h0⟩ : (Ideal (QOrder D))⁰) = ⟨𝔟₁, h₁⟩ * ⟨𝔟₂, h₂⟩ from rfl, map_mul, hk₁, hk₂]
    change _ = (formClassOrder h)⁻¹
    rw [hcls, mul_inv]; rfl
  funext p
  apply Units.ext
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpN : p.1 ∣ D.natAbs := Nat.dvd_of_mem_primeFactors p.2
  have hpD : (p.1 : ℤ) ∣ D := Int.natCast_dvd.mpr hpN
  rw [Pi.mul_apply, Units.val_mul, coe_genusVec h.2.1 h.2.2.1, coe_genusVec f.2.1 f.2.2.1,
    coe_genusVec g.2.1 g.2.2.1]
  have e1 := genusChar_norm_eq_formChar hD f.toPrim hN₁ h₁ hk₁ hp hpD (hc₁ p hp hpN)
  have e2 := genusChar_norm_eq_formChar hD g.toPrim hN₂ h₂ hk₂ hp hpD (hc₂ p hp hpN)
  have e := genusChar_norm_eq_formChar hD h.toPrim hN h0 hk hp hpD (by
    push_cast
    intro hd
    rcases int_prime_dvd_mul hp hd with hd | hd
    exacts [hc₁ p hp hpN hd, hc₂ p hp hpN hd])
  push_cast at e
  rw [genusChar_mul, e1, e2] at e
  exact e.symm

/-! ### The interface is discharged -/

omit [IsQuadDisc D] in
/-- **`IsFormClassGroup` is transported along a group isomorphism** $e : G \cong G'$, with class map $e \circ \mathrm{cls}$. -/
theorem IsFormClassGroup.map {G G' : Type*} [CommGroup G] [CommGroup G'] {cls : PosForms D → G}
    (C : IsFormClassGroup D G cls) (e : G ≃* G') : IsFormClassGroup D G' (fun f => e (cls f)) where
  cls_surjective := e.surjective.comp C.cls_surjective
  sameGenus_of_cls_eq f g h := C.sameGenus_of_cls_eq f g (e.injective h)
  genusVec_mul f g h hcls := C.genusVec_mul f g h (e.injective (by rw [hcls, map_mul]))

/-- **Gauss composition for $D < 0$, from forms ↔ ideals, in $\mathrm{Cl}(\mathbb{Z}[\omega])$**: The interface
`IsFormClassGroup` holds for $G = \mathrm{Cl}(\mathbb{Z}[\omega])$ and $\mathrm{cls}(f) = [\mathfrak a_f]$. -/
theorem isFormClassGroupOrder (hD : D < 0) :
    IsFormClassGroup D (ClassGroup (QOrder D)) formClassOrder where
  cls_surjective x := by
    obtain ⟨f, hf⟩ := idealClass_surjective hD x
    exact ⟨f.toPos, hf⟩
  sameGenus_of_cls_eq f g h :=
    IntEquiv.sameGenus (SLEquiv.intEquiv (sLEquiv_of_idealClass_eq hD (f := f.toPrim) (g := g.toPrim) h))
  genusVec_mul f g h hcls := genusVec_formClass_mul hD f g h hcls

/-- **The composition interface is discharged** ($D < 0$ fundamental): `IsFormClassGroup D G cls` holds for
$G = \mathrm{Cl}(\mathcal O_{K_D})$ and $\mathrm{cls}(f) = [\mathfrak a_f]$ (`formClass`):
- `cls_surjective`: every ideal class is $[\mathfrak a_f]$ for a primitive positive definite form $f$ of discriminant $D$
  (`idealClass_surjective`);
- `sameGenus_of_cls_eq`: forms with the same class are properly equivalent (`sLEquiv_of_idealClass_eq`), hence in
  the same genus;
- `genusVec_mul`: the genus characters are multiplicative (`genusVec_formClass_mul`).
Source: Cox, §3.B, Thm. 3.15 and §7.B, Thm. 7.7 [unverified locator]. -/
@[kb "cox2013" "§3.B, Thm. 3.15; §7.B, Thm. 7.7 [unverified locator]; cassels1978 Ch. 14, Thm. 2.1, p. 337"]
theorem isFormClassGroup (hD : D < 0) :
    IsFormClassGroup D (ClassGroup (𝓞 (QField D))) formClass :=
  (isFormClassGroupOrder hD).map (classGroupEquiv D)

/-! ### Every genus has $h/2^{t-1}$ classes, unconditionally -/

namespace IsFormClassGroup

variable {G : Type*} [CommGroup G] {cls : PosForms D → G} (C : IsFormClassGroup D G cls)
include C

/-- The genus of the class of $f$ is the genus of $f$. -/
theorem genusOf_cls (f : PosForms D) : C.genusOf (cls f) = Quotient.mk (genusSetoid D) f :=
  Quotient.sound (C.sameGenus_of_cls_eq _ _ (C.cls_rep (cls f)))

/-- $\gamma(x^{-1}) = \gamma(x)$: the genus homomorphism takes values in $\{\pm 1\}^t$. -/
theorem genusHom_inv (x : G) : C.genusHom x⁻¹ = C.genusHom x := by
  rw [map_inv]
  funext p
  rcases Int.units_eq_one_or (C.genusHom x p) with h | h <;> simp [h]

/-- **A class and its inverse lie in the same genus** ($[\bar f] = [f]^{-1}$, and $\bar f = (a, -b, c)$ has the same
genus characters). -/
theorem genusOf_inv (hD : D < 0) (x : G) : C.genusOf x⁻¹ = C.genusOf x := by
  rw [C.genusOf_eq_iff hD, C.genusHom_inv, ← C.genusOf_eq_iff hD]

end IsFormClassGroup

/-- **The genus of a proper class** of primitive positive definite forms (proper equivalence implies
$\mathrm{GL}_2(\mathbb{Z})$-equivalence, hence the same genus). -/
def slGenus : Quotient (slSetoid D) → Genera D :=
  Quotient.lift (fun f => Quotient.mk (genusSetoid D) f.toPos) fun _ _ h =>
    Quotient.sound (IntEquiv.sameGenus (SLEquiv.intEquiv h))

@[simp] theorem slGenus_mk (f : PrimPosForm D) :
    slGenus (Quotient.mk (slSetoid D) f) = Quotient.mk (genusSetoid D) f.toPos := rfl

/-- **Every genus has $h/2^{t-1}$ ideal classes, unconditionally** ($D < 0$ fundamental, $t$ = number of prime
factors of $D$): for every genus $\mathcal G$ of primitive positive definite forms of discriminant $D$,
$$\#\{x \in \mathrm{Cl}(\mathcal O_{K_D}) : x \in \mathcal G\} \cdot 2^{t-1} = h(D).$$
`card_classes_in_genus` with its interface discharged by `isFormClassGroup`. Source: Gauss, *Disq. Arith.*
§252 [unverified]; Cox, Thm. 3.15 [unverified locator]. -/
@[kb "gauss1801" "§252 [unverified]"]
theorem card_classes_in_genus' (hD : D < 0) (𝒢 : Genera D) :
    Nat.card {x : ClassGroup (𝓞 (QField D)) // (isFormClassGroup hD).genusOf x = 𝒢} *
      2 ^ (D.natAbs.primeFactors.card - 1) = classNumber (QField D) := by
  rw [(isFormClassGroup hD).card_classes_in_genus hD 𝒢, classNumber, Nat.card_eq_fintype_card]

/-- **Every genus contains $h/2^{t-1}$ proper classes of forms, unconditionally** ($D < 0$ fundamental): for every
genus $\mathcal G$,
$$\#\{\mathrm{SL}_2(\mathbb{Z})\text{-classes of primitive positive definite forms of discriminant } D \text{ in }
\mathcal G\} \cdot 2^{t-1} = h(D).$$
Source: Gauss, *Disq. Arith.* §252 [unverified]; Cox, Thm. 3.15 [unverified locator]. -/
@[kb "gauss1801" "§252 [unverified]"]
theorem card_slClasses_in_genus (hD : D < 0) (𝒢 : Genera D) :
    Nat.card {c : Quotient (slSetoid D) // slGenus c = 𝒢} * 2 ^ (D.natAbs.primeFactors.card - 1) =
      classNumber (QField D) := by
  rw [← card_classes_in_genus' hD 𝒢]
  congr 1
  refine Nat.card_congr ((slClassEquiv hD).subtypeEquiv fun c => ?_)
  induction c using Quotient.inductionOn with
  | h f =>
    change _ ↔ (isFormClassGroup hD).genusOf (formClass f.toPos) = 𝒢
    rw [(isFormClassGroup hD).genusOf_cls]
    rfl

/-- **The number of proper classes in a genus is $h/2^{t-1}$** (division form of `card_slClasses_in_genus`). -/
theorem card_slClasses_in_genus_eq_div (hD : D < 0) (𝒢 : Genera D) :
    Nat.card {c : Quotient (slSetoid D) // slGenus c = 𝒢} =
      classNumber (QField D) / 2 ^ (D.natAbs.primeFactors.card - 1) := by
  rw [← card_slClasses_in_genus hD 𝒢, Nat.mul_div_cancel _ (by positivity)]

end QuadFormsKB.Binary
