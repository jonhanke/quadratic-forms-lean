/-
# The class set of a maximal order (Voight, Chapter 16 and Definition 26.1.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`), Main Theorem 16.6.1 (p. 267) and
Definition 26.1.4 (p. 432).

For a maximal order $\mathcal O$ of a totally definite quaternion algebra $B = (a,b)_F$ over a totally real number field,
every nonzero left ideal is locally principal (`isLocPrincipal_of_maximal`). Hence the class set $\operatorname{Cls}\mathcal O$
(`ClsO`, classes of nonzero locally principal left ideals) coincides with the set of classes of all nonzero left ideals
used in `classMass`, so `clsMass O = classMass O` and `clsNum O` is the number of classes of nonzero left ideals.
-/
import QuadFormsKB.Literature.Voight.MassFormula

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave4

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight

variable {F : Type} [Field F] [NumberField F]

/-- For a totally definite algebra a nonzero left ideal $J$ of an order has nonzero reduced norm ideal: a nonzero element
$x \in J$ has $\operatorname{nrd}(x) \neq 0$ (anisotropy of $\operatorname{nrd}$) and $\operatorname{nrd}(x) \in \mathbb Z_F$. -/
theorem leftNrdIdeal_ne_bot [IsTotallyReal F] {a b : 𝓞 F} (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : J ≠ ⊥) :
    leftNrdIdeal J ≠ ⊥ := by
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hx0' : (x : QuatF F a b) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hn : nrd (x : QuatF F a b) ≠ 0 := fun h => hx0' (eq_zero_of_nrd_eq_zero hdef h)
  obtain ⟨r, hr⟩ := (isInteger_trd_nrd hO.1 x.2).2
  intro hbot
  have hmem : r ∈ leftNrdIdeal J := Ideal.subset_span ⟨x, hxJ, hr⟩
  rw [hbot, Ideal.mem_bot] at hmem
  apply hn
  rw [← hr, hmem, map_zero]

/-- For a maximal order of a totally definite algebra, every nonzero left ideal is locally principal: at each finite place
$v$, `QuatOrder.exists_local_generator` gives $J_v = \mathcal O_v\alpha$ with $\operatorname{nrd}\alpha = t \neq 0$, so $\alpha$ is a
unit of $B_v$. -/
@[kb "voight2021" "Main Theorem 16.6.1, p. 267"]
theorem isLocPrincipal_of_maximal [IsTotallyReal F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : J ≠ ⊥) :
    IsLocPrincipal J := by
  intro v
  obtain ⟨α, t, -, hIα, ht, hspan⟩ := Gen.exists_local_generator ha hb hO (leftNrdIdeal_ne_bot hdef hO hJ) v
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at hspan
    exact (QuadFormsKB.LocalDensity.NF.irreducible_π v).ne_zero (pow_eq_zero_iff'.1 hspan).1
  have hn : nrd α ≠ 0 := by
    rw [← ht]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ht0
  obtain ⟨u, hu⟩ := (isUnit_iff_nrd_ne_zero α).2 hn
  exact ⟨u, by rw [hu]; exact hIα⟩

/-- Every class of nonzero left ideals of a maximal order of a totally definite algebra is a class of locally principal
ideals: the index types of `classMass` and `clsMass` are equivalent. -/
def clsOEquiv [IsTotallyReal F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) :
    {c : Quotient (idealSetoid O) // c.out ≠ ⊥} ≃ ClsO O :=
  Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => ⟨h, isLocPrincipal_of_maximal ha hb hdef hO h⟩, fun h => h.1⟩

/-- **The mass of the class set of a maximal order**: `clsMass O = classMass O`
(Voight 2021, Definition 26.1.4; all nonzero left ideals are locally principal). -/
@[kb "voight2021" "Definition 26.1.4, p. 432"]
theorem clsMass_eq_classMass [IsTotallyReal F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) : clsMass O = classMass O :=
  ((clsOEquiv ha hb hdef hO).tsum_eq fun c : ClsO O =>
    (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹).symm

/-- **The class number of a maximal order** is the number of classes of nonzero left ideals. -/
theorem clsNum_eq [IsTotallyReal F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) :
    clsNum O = Nat.card {c : Quotient (idealSetoid O) // c.out ≠ ⊥} :=
  (Nat.card_congr (clsOEquiv ha hb hdef hO)).symm

end QuadFormsKB.Voight.Wave4