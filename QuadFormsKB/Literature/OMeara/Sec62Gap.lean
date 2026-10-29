/-
# O'Meara §62: the orthogonal groups of a quadratic space over a finite field (62:4, partial)

**Setting.** $F$ a finite field with $2$ invertible (O'Meara's standing assumption of Part Three), $(V, Q)$ a regular
quadratic space over $F$ of dimension $n$ (regular: `(QuadraticMap.associated Q).Nondegenerate`). The groups are those
of `Sec55.lean`: $O_n$ = `orth Q`, $O_n^+$ = `orthPlus Q`, the commutator subgroup $\Omega_n$ = `omega Q`, and the
spinor kernel $O_n'$ = `orthPrime Q`; spinor norms are expressed through `HasSpinorNorm` (`Sec92Spinor.lean`).

**Proves** (Remark 62:4, p. 158, in part)
* `omega_eq_orthPrime_finite` : $\Omega_n = O_n'$ for every $n$;
* `exists_hasSpinorNorm_finite` : for $n \ge 2$ the spinor norm $\theta : O_n^+ \to \dot F/\dot F^2$ is surjective, i.e.
  every $c \in \dot F$ is the spinor norm of a rotation; since $\dot F/\dot F^2$ has order $2$ for a finite field
  (`isSquare_or_isSquare_mul`, `Sec62.lean`), $O_n^+/O_n' \cong \dot F/\dot F^2$ has order $2$.

* `relIndex_orthPlus` : $(O_n : O_n^+) = 2$ for $n \ge 1$ (any field with $2$ invertible).

**Not proved here.** The machine-read text of 62:4 loses most of the displayed formulas; the description of the
remaining factor group by "$\{\pm 1_V\}$ if $dV = 1$ with $n$ even, $1$ otherwise" (that is, of $-1_V$ modulo $O_n'$,
compare 55:7, `neg_mem_orthPrime_iff`) is not restated.

**Proof notes.** $\Omega_n = O_n'$: for $n \le 3$ by 55:5 (`omega_eq_orthPrime_of_finrank_le_three`), for $n \ge 3$
because $V$ is isotropic (62:1b) and 55:6a (`omega_eq_orthPrime_of_isotropic`). Surjectivity: $V$ is universal (62:1),
so $c = Q(x)Q(y)$ with $Q(x) = c$, $Q(y) = 1$, and 55:2 (`exists_hasSpinorNorm_iff`) applies.
-/
import QuadFormsKB.Literature.OMeara.Sec62
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec82Free

open QuadraticMap Module

namespace QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Fintype F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

private theorem ringChar_ne_two_of_invertible : ringChar F ≠ 2 := by
  intro h
  have h2 : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
  rw [h] at h2
  exact (isUnit_of_invertible (2 : F)).ne_zero (by exact_mod_cast h2)

/-- **Remark 62:4, $\Omega_n = O_n'$** (O'Meara 1963, p. 158): for a regular quadratic space over a finite field (of odd
characteristic) the commutator subgroup $\Omega_n$ of $O_n$ equals the spinor kernel $O_n'$. -/
@[kb "omeara1963" "§62, 62:4, p. 158 (Ω_n = O_n')"]
theorem omega_eq_orthPrime_finite (hQ : (QuadraticMap.associated Q).Nondegenerate) : omega Q = orthPrime Q := by
  by_cases h3 : finrank F V ≤ 3
  · exact omega_eq_orthPrime_of_finrank_le_three Q hQ h3
  · have hiso := not_anisotropic_of_three_le (ringChar_ne_two_of_invertible (F := F)) Q (by omega)
    simp only [QuadraticMap.Anisotropic, not_forall] at hiso
    obtain ⟨x, hx, hx0⟩ := hiso
    exact omega_eq_orthPrime_of_isotropic Q hQ ⟨x, hx0, hx⟩

/-- **Remark 62:4, $O_n^+/O_n' \cong \dot F/\dot F^2$** (O'Meara 1963, p. 158): for a regular quadratic space of
dimension $n \ge 2$ over a finite field (of odd characteristic), every $c \in \dot F$ is the spinor norm of a rotation
$\sigma \in O_n^+$; so $\theta(O_n^+) = \dot F/\dot F^2$, a group of order $2$. -/
@[kb "omeara1963" "§62, 62:4, p. 158 (θ(O_n⁺) = Ḟ/Ḟ², so (O_n⁺ : O_n') = 2)"]
theorem exists_hasSpinorNorm_finite (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 2 ≤ finrank F V)
    {c : F} (hc : c ≠ 0) : ∃ σ ∈ orthPlus Q, HasSpinorNorm Q σ c := by
  have hrad : Q.radical = ⊥ :=
    QuadraticMap.nondegenerate_iff_radical_eq_bot.mp (QuadraticMap.nondegenerate_associated_iff.mp hQ)
  obtain ⟨x, hx⟩ := isUniversal_of_two_le (ringChar_ne_two_of_invertible (F := F)) Q hrad hn c
  obtain ⟨y, hy⟩ := isUniversal_of_two_le (ringChar_ne_two_of_invertible (F := F)) Q hrad hn 1
  refine (exists_hasSpinorNorm_iff Q hQ hn).mpr ⟨[x, y], ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [hx]; exact hc
    · rw [hy]; exact one_ne_zero
  · simp
  · simpa using hn
  · simp [hx, hy]

/-- **Remark 62:4, $(O_n : O_n^+) = 2$** (O'Meara 1963, p. 158): for a regular non-zero quadratic space the rotations
form a subgroup of index $2$ in the orthogonal group (a symmetry has determinant $-1$). Valid over any field with $2$
invertible; stated in §62 for finite fields. -/
@[kb "omeara1963" "§62, 62:4, p. 158 ((O_n : O_n⁺) = 2)"]
theorem relIndex_orthPlus (hQ : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V] :
    (orthPlus Q).relIndex (orth Q) = 2 := by
  obtain ⟨u, hu⟩ := exists_Q_ne_zero Q hQ
  have hτ : symmetry Q u hu ∈ orth Q := symmetry_mem_orth Q hu
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    have h2 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h2
    have : (2 : F) = 0 := by linear_combination -h2
    exact (isUnit_of_invertible (2 : F)).ne_zero this
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨_, hτ⟩, fun b => ?_⟩
  have hb := det_orth_eq Q hQ b.2
  have hmem : ∀ c : orth Q, c ∈ (orthPlus Q).subgroupOf (orth Q) ↔
      LinearEquiv.det (c : V ≃ₗ[F] V) = 1 := fun c =>
    ⟨fun H => H.2, fun H => ⟨c.2, H⟩⟩
  rw [hmem, hmem]
  have hd : LinearEquiv.det ((b * ⟨_, hτ⟩ : orth Q) : V ≃ₗ[F] V) =
      LinearEquiv.det (b : V ≃ₗ[F] V) * -1 := by
    rw [← det_symmetry Q hu, ← map_mul]; rfl
  rw [hd]
  rcases hb with h | h
  · rw [h]; simp [hne]
  · rw [h]; simp [hne]

end QuadFormsKB.OMeara
