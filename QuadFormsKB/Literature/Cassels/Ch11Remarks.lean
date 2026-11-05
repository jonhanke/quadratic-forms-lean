/-
# Cassels, Chapter 11: remarks on proper equivalence, the genus and $SL(\Lambda)$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, pp. 196-199 and p. 206.

**Layer.** $V = F^n$ over a number field $F$ with a quadratic form $Q$ (`Q : QuadForm F n`); lattices are
$\mathcal O_F$-submodules of $F^n$ (`Submodule (𝓞 F) (Fin n → F)`), `glImage γ L` is $\gamma L$ and `locAct` is the
corresponding action on local lattices.

**Formalized.**
* 11.r4 (p. 197): for odd $n$ the map $x \mapsto -x$ is an isometry of determinant $-1$ carrying every lattice onto
  itself (`negOrth`, `negOrth_det_of_odd`, `glImage_negOrth`), hence proper and improper equivalence of lattices
  coincide (`isProperIsometric_iff_isIsometric_of_odd`).
* 11.r5 (p. 197): for a local lattice, proper equivalence and equivalence coincide
  (`exists_proper_locAct_eq_iff`), by Chapter 8, Lemma 3.2, Corollary (here `exists_det_neg_one_locAct_eq`).
* 11.r8 (p. 199): the genus defined with rotations $O^{+}(V_p)$ is the genus defined with $O(V_p)$
  (`sameGenus_iff_forall_proper`; the library's `SameProperGenus` is the $O^{+}$ version).
* 11.r17 (p. 206): the group $SL(\Lambda)$ of automorphs of determinant $1$ (`slLat`).

*Conventions.* In Theorem 2.1 no form is involved: the "automorphs" of a lattice $\Lambda$ are the linear maps
carrying $\Lambda$ onto itself, so `slLat` consists of elements of $\mathrm{GL}_n(F)$, not of the orthogonal group.
Nondegeneracy of $Q$ is assumed where an isometry must have determinant $\pm 1$ (the book works in a nondegenerate
space).
-/
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace QuadFormsKB

namespace Cassels.Ch11Remarks

open Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### 11.r4: negation for odd dimension -/

/-- Helper: the isometry $x \mapsto -x$ of $(R^n, Q)$ for a commutative $F$-algebra `R` (the coefficient ring) and
the quadratic form `Q`. -/
def negOrth (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q R :=
  ⟨-1, by
    rw [mem_orthGroup]
    simp⟩

/-- Helper: the underlying matrix of `negOrth Q R` is $-1$. -/
theorem negOrth_val (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] :
    ((negOrth Q R : orthGroup Q R) : GL (Fin n) R).val = -1 := by
  simp [negOrth]

/-- Helper: the determinant of $x \mapsto -x$ on $R^n$ is $(-1)^n$. -/
theorem negOrth_det (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] :
    ((negOrth Q R : orthGroup Q R) : GL (Fin n) R).val.det = (-1) ^ n := by
  rw [negOrth_val]
  simp [Matrix.det_neg]

/-- **For odd $n$, $x \mapsto -x$ has determinant $-1$** (Cassels, Ch. 11, p. 197): the isometry `negOrth Q R`
of $R^n$ ($R$ a commutative $F$-algebra, `Q` the form) has determinant $-1$ when `n` is odd. -/
@[kb "cassels1978" "Ch. 11, §1, p. 197 (x ↦ -x is improper for n odd)"]
theorem negOrth_det_of_odd (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] (hn : Odd n) :
    ((negOrth Q R : orthGroup Q R) : GL (Fin n) R).val.det = -1 := by
  rw [negOrth_det, hn.neg_one_pow]

/-- Helper: $x \mapsto -x$ carries every lattice `L` onto itself. -/
theorem glImage_negOrth (Q : QuadForm F n) (L : Submodule (𝓞 F) (Fin n → F)) :
    glImage ((negOrth Q F : orthGroup Q F) : GL (Fin n) F) L = L := by
  ext x
  rw [mem_glImage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [negOrth_val]
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    exact L.neg_mem hy
  · intro hx
    refine ⟨-x, L.neg_mem hx, ?_⟩
    rw [negOrth_val, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]

/-- **Cassels, Ch. 11, p. 197: for odd $n$ proper and improper equivalence of lattices coincide.** Let `Q` be a
nondegenerate quadratic form on $F^n$ with $n$ odd, and `L`, `M` lattices. Then `L` and `M` are properly isometric
($M = \sigma L$, $\sigma \in O^{+}(V)$) if and only if they are isometric ($M = \sigma L$, $\sigma \in O(V)$),
because $x \mapsto -x$ is an improper automorph of every lattice. So Corollary 1 (proper classes versus classes)
has content only for $n$ even. -/
@[kb "cassels1978" "Ch. 11, §1, p. 197 (n odd: proper = improper equivalence)"]
theorem isProperIsometric_iff_isIsometric_of_odd (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : Odd n)
    (L M : Submodule (𝓞 F) (Fin n → F)) : IsProperIsometric Q L M ↔ IsIsometric Q L M := by
  refine ⟨IsProperIsometric.isIsometric Q, ?_⟩
  rintro ⟨γ, hγ, he⟩
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨γ, hγ⟩ with h1 | h1
  · exact ⟨⟨γ, hγ⟩, h1, he⟩
  · refine ⟨⟨γ, hγ⟩ * negOrth Q F, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, negOrth_det_of_odd Q F hn]
      change γ.val.det * _ = 1
      rw [show γ.val.det = -1 from h1]; ring
    · rw [Subgroup.coe_mul, glImage_mul, glImage_negOrth]; exact he

/-! ### 11.r5 and 11.r8: local lattices and the genus -/

section Local

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

/-- **Cassels, Ch. 11, p. 197: for local lattices proper equivalence is equivalence.** Let `Q` be nondegenerate on
$F^n$ with $n \ge 1$, `v` a finite prime, $F_v$ the completion, `M` a lattice on $F_v^n$ and `N` a submodule. Then there
is a rotation $g \in O^{+}(V_v)$ with $gM = N$ if and only if there is an isometry $g \in O(V_v)$ with $gM = N$; the
point is that $M$ has an improper automorph (Chapter 8, Lemma 3.2, Corollary). -/
@[kb "cassels1978" "Ch. 11, §1, p. 197 (local: proper = improper equivalence; Ch. 8, Lemma 3.2, Cor.)"]
theorem exists_proper_locAct_eq_iff (hQ : Q.Nondegenerate) (hn : 0 < n)
    {M : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)}
    (hM : M.IsLattice (v.adicCompletion F))
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) :
    (∃ g : orthGroup Q (v.adicCompletion F), g ∈ Tamagawa.soSub Q (v.adicCompletion F) ∧
        locAct v (g : GL (Fin n) _) M = N) ↔
      ∃ g ∈ orthGroup Q (v.adicCompletion F), locAct v g M = N := by
  refine ⟨fun ⟨g, _, he⟩ => ⟨g, g.2, he⟩, ?_⟩
  rintro ⟨g, hg, he⟩
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ ⟨g, hg⟩ with h1 | h1
  · exact ⟨⟨g, hg⟩, h1, he⟩
  · obtain ⟨τ, hτ, hτM⟩ := exists_det_neg_one_locAct_eq Q v hQ hn hM
    refine ⟨⟨g, hg⟩ * τ, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
      change g.val.det * _ = 1
      rw [show g.val.det = -1 from h1, hτ]; ring
    · rw [Subgroup.coe_mul, locAct_mul, hτM]; exact he

/-- **Cassels, Ch. 11, p. 199: the genus with $O^{+}(V_p)$ is the genus with $O(V_p)$.** For nondegenerate `Q`
on $F^n$ and a lattice `L`, a submodule `M` is in the genus of `L` in the sense of the library (`SameGenus`, with the
full local orthogonal groups) if and only if for every finite prime `v` there is a local rotation
$g_v \in O^{+}(V_v)$ with $g_v L_v = M_v$ (Cassels' definition; this is `SameProperGenus`, unfolded). -/
@[kb "cassels1978" "Ch. 11, §1, p. 199 (genus with O⁺(V_p) = genus with O(V_p))"]
theorem sameGenus_iff_forall_proper (hQ : Q.Nondegenerate) {L : Submodule (𝓞 F) (Fin n → F)}
    (hL : L.IsLattice F) (M : Submodule (𝓞 F) (Fin n → F)) :
    SameGenus Q L M ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : orthGroup Q (v.adicCompletion F),
      g ∈ Tamagawa.soSub Q (v.adicCompletion F) ∧ locAct v (g : GL (Fin n) _) (loc v L) = loc v M :=
  (sameProperGenus_iff_sameGenus Q hQ hL).symm

end Local

/-! ### 11.r17: $SL(\Lambda)$ -/

/-- **The group $SL(\Lambda)$** (Cassels, Ch. 11, p. 206): the automorphs of the lattice `L` (elements
$\gamma \in \mathrm{GL}_n(F)$ with $\gamma L = L$) of determinant $+1$. Here `L` is a lattice (an $\mathcal O_F$-submodule
of $F^n$); no quadratic form is involved. -/
@[kb "cassels1978" "Ch. 11, §2, p. 206 (SL(Λ))"]
def slLat (L : Submodule (𝓞 F) (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {γ | glImage γ L = L ∧ γ.val.det = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [glImage_mul, hb.1, ha.1]
    · rw [Units.val_mul, det_mul, ha.2, hb.2, one_mul]
  one_mem' := ⟨glImage_one L, by simp⟩
  inv_mem' {a} ha := by
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← ha.1]
      rw [← glImage_mul, inv_mul_cancel, glImage_one]
    · have h := congrArg Matrix.det (Units.mul_inv a)
      rw [det_mul, ha.2, one_mul, det_one] at h
      simpa using h

/-- **Membership in $SL(\Lambda)$** is the inline condition "$\gamma L = L$ and $\det\gamma = 1$" used in
`exists_slLat_approx` (Theorem 2.1): for a lattice `L` and $\gamma \in \mathrm{GL}_n(F)$. -/
@[kb "cassels1978" "Ch. 11, §2, p. 206 (SL(Λ): membership)"]
theorem mem_slLat_iff (L : Submodule (𝓞 F) (Fin n → F)) (γ : GL (Fin n) F) :
    γ ∈ slLat L ↔ glImage γ L = L ∧ γ.val.det = 1 := Iff.rfl

end Cassels.Ch11Remarks

end QuadFormsKB
