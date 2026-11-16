import QuadFormsKB.Historical.Gauss.Duplication
import QuadFormsKB.Historical.Gauss.Reduction

/-!
# Gauss's worked example of the principal genus and duplication for determinant $-161$ (*Disq. Arith.* Art. 260)

(Gauss, *Disquisitiones Arithmeticae* (1801), Art. 260, the example $D = -161$).

Gauss's forms $(a, b, c) = a x^2 + 2 b x y + c y^2$ (`gaussForm`) of determinant $b^2 - a c = -161$, i.e. library
discriminant $4 \cdot (-161) = -644$, are treated as classes of properly primitive positive forms in the class
group `Composition.FormClass (-644)` (Dirichlet composition, `Ch14/Group.lean`). There are $16$ positive classes
(reduced forms $(1,0,161)$, $(2,1,81)$, $(3,\pm1,54)$, $(5,\pm2,33)$, $(6,\pm1,27)$, $(7,0,23)$, $(9,\pm1,18)$,
$(10,\pm3,17)$, $(11,\pm2,15)$, $(14,7,15)$), $4$ of them ambiguous ($(1,0,161)$, $(2,1,81)$, $(7,0,23)$, $(14,7,15)$).

**Proved** (`art260_example_161`), unconditionally:

* the four classes of $(1,0,161)$, $(2,1,81)$, $(9,1,18)$, $(9,-1,18)$ are squares in the class group, hence lie in
  the principal genus (`principal_genus_iff_square`), and they are pairwise distinct (uniqueness of reduced forms,
  `art172_aux`);
* $(1,0,161)$ is the double of each of the four ambiguous classes $(1,0,161)$, $(7,0,23)$, $(2,1,81)$, $(14,7,15)$;
* $(2,1,81)$ is the double of $(9,\pm1,18)$ and $(11,\pm2,15)$;
* $(9,1,18)$ is the double of $(3,1,54)$, $(6,1,27)$, $(5,-2,33)$, $(10,3,17)$;
* $(9,-1,18)$ is the double of $(3,-1,54)$, $(6,-1,27)$, $(5,2,33)$, $(10,-3,17)$.

Each "double" statement is `mk Y ^ 2 = mk X`, proved by composing two concordant representatives of $Y$ (explicit
forms) and an explicit properly equivalent substitution to $X$ (found by computation, checked by `norm_num`).

**Not proved:** that the principal genus consists of *exactly* these four classes (this needs the class number
$16$ and the genus count, not available cheaply in the library).

*Erratum:* Gauss's 1801 text prints $(2, 1, 18)$ where $(2, 1, 81)$ is meant (the determinant of $(2,1,18)$ is $-35$);
recorded as an erratum.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition _root_.QuadFormsKB.Composition.FormClass

local instance : NonzeroDisc (-644) := ⟨by norm_num, by norm_num⟩

/-- A form $(a, b, c)$ with $\gcd(a, 2b, c) = 1$ is primitive (helper). -/
theorem isPrimitive_of_gcd {a b c : ℤ} (h : Int.gcd a (Int.gcd b c) = 1) : (BinQF.mk a b c).IsPrimitive := by
  intro d h1 h2 h3
  simp only [a_mk, b_mk, c_mk] at h1 h2 h3
  have := Int.dvd_coe_gcd h1 (Int.dvd_coe_gcd h2 h3)
  rw [h] at this
  exact isUnit_of_dvd_one (by simpa using this)

/-- **The primitive form $(a, b, c)$ of determinant $-161$** as an element of `PrimForm (-644)`. -/
def gpf (a b c : ℤ) (h : Int.gcd a (Int.gcd (2 * b) c) = 1 ∧ b ^ 2 - a * c = -161) : PrimForm (-644) :=
  ⟨gaussForm a b c, isPrimitive_of_gcd h.1, by
    rw [disc_gaussForm]; unfold gaussDet; linarith [h.2]⟩

/-- **The class of Gauss's form $(a, b, c)$** of determinant $-161$ in `FormClass (-644)`. -/
def gcls (a b c : ℤ) (h : Int.gcd a (Int.gcd (2 * b) c) = 1 ∧ b ^ 2 - a * c = -161) : FormClass (-644) :=
  FormClass.mk (gpf a b c h)

/-- A proper equivalence from an explicit matrix (helper): `subst p q r s f = g` coefficientwise. -/
theorem sl_of (f g : BinQF) (p q r s : ℤ) (hd : p * s - q * r = 1)
    (ha : f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2 = g.a)
    (hb : 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s = g.b)
    (hc : f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2 = g.c) : SLEquiv f g :=
  (sLEquiv_iff f g).2 ⟨p, q, r, s, hd, ext_abc (by rw [BinQF.a_subst]; exact ha)
    (by rw [BinQF.b_subst]; exact hb) (by rw [BinQF.c_subst]; exact hc)⟩

/-- **Doubling through two concordant representatives** (helper): if $(a,b,c)$ is properly equivalent to two
concordant forms $g_1, g_2$ whose composition is properly equivalent to $(a',b',c')$, then
$[(a,b,c)]^2 = [(a',b',c')]$. -/
theorem gcls_sq {a b c a' b' c' : ℤ} {h : _} {h' : _} (g1 g2 : BinQF) (hc : Concordant g1 g2)
    (h1 : SLEquiv (gaussForm a b c) g1) (h2 : SLEquiv (gaussForm a b c) g2)
    (h3 : SLEquiv (Composition.comp g1 g2) (gaussForm a' b' c')) : gcls a b c h ^ 2 = gcls a' b' c' h' := by
  have e1 := mk_ofEquiv (gpf a b c h) h1
  have e2 := mk_ofEquiv (gpf a b c h) h2
  calc gcls a b c h ^ 2
      = FormClass.mk (ofEquiv (gpf a b c h) h1) * FormClass.mk (ofEquiv (gpf a b c h) h2) := by
        rw [pow_two, e1, e2]; rfl
    _ = FormClass.mk (PrimForm.comp (ofEquiv (gpf a b c h) h1) (ofEquiv (gpf a b c h) h2) hc) :=
        mk_mul_mk _ _ hc
    _ = gcls a' b' c' h' := mk_eq_mk.2 h3

local macro "nsimp161" : tactic => `(tactic| norm_num [gaussForm, Composition.comp, BinQF.disc])

theorem sq1 : gcls 1 0 161 (by decide) ^ 2 = gcls 1 0 161 (by decide) :=
  gcls_sq (BinQF.mk 1 0 161) (BinQF.mk 1 0 161)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 0 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 0 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 1 0 0 1 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq2 : gcls 7 0 23 (by decide) ^ 2 = gcls 1 0 161 (by decide) :=
  gcls_sq (BinQF.mk 7 0 23) (BinQF.mk 23 0 7)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 0 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 0 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 0 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq3 : gcls 2 1 81 (by decide) ^ 2 = gcls 1 0 161 (by decide) :=
  gcls_sq (BinQF.mk 81 2 2) (BinQF.mk 2 2 81)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-1) 1 0 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 0 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 1 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq4 : gcls 14 7 15 (by decide) ^ 2 = gcls 1 0 161 (by decide) :=
  gcls_sq (BinQF.mk 15 14 14) (BinQF.mk 14 14 15)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-1) 1 0 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 0 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 7 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq5 : gcls 9 1 18 (by decide) ^ 2 = gcls 2 1 81 (by decide) :=
  gcls_sq (BinQF.mk 25 (-34) 18) (BinQF.mk 9 (-34) 50)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 0 1 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 2 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-8) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq6 : gcls 9 (-1) 18 (by decide) ^ 2 = gcls 2 1 81 (by decide) :=
  gcls_sq (BinQF.mk 9 34 50) (BinQF.mk 25 34 18)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-2) 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 0 (-1) (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 9 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq7 : gcls 11 2 15 (by decide) ^ 2 = gcls 2 1 81 (by decide) :=
  gcls_sq (BinQF.mk 11 26 30) (BinQF.mk 15 26 22)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-1) 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 1 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 7 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq8 : gcls 11 (-2) 15 (by decide) ^ 2 = gcls 2 1 81 (by decide) :=
  gcls_sq (BinQF.mk 11 (-26) 30) (BinQF.mk 15 (-26) 22)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 1 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-6) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq9 : gcls 3 1 54 (by decide) ^ 2 = gcls 9 1 18 (by decide) :=
  gcls_sq (BinQF.mk 55 (-326) 486) (BinQF.mk 54 (-326) 495)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 2 1 (-3) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-3) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-18) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq10 : gcls 6 1 27 (by decide) ^ 2 = gcls 9 1 18 (by decide) :=
  gcls_sq (BinQF.mk 35 (-434) 1350) (BinQF.mk 27 (-434) 1750)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 7 (-1) 6 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-8) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) (-2) (-4) (-9) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq11 : gcls 5 (-2) 33 (by decide) ^ 2 = gcls 9 1 18 (by decide) :=
  gcls_sq (BinQF.mk 34 (-74) 45) (BinQF.mk 5 (-74) 306)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 2 (-1) 1 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 7 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-4) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq12 : gcls 10 3 17 (by decide) ^ 2 = gcls 9 1 18 (by decide) :=
  gcls_sq (BinQF.mk 10 (-74) 153) (BinQF.mk 17 (-74) 90)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) 4 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-2) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 (-4) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq13 : gcls 3 (-1) 54 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) :=
  gcls_sq (BinQF.mk 55 326 486) (BinQF.mk 54 326 495)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-2) (-1) (-3) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 3 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 18 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq14 : gcls 6 (-1) 27 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) :=
  gcls_sq (BinQF.mk 35 434 1350) (BinQF.mk 27 434 1750)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-7) 1 6 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 8 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) 2 4 (-9) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq15 : gcls 5 2 33 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) :=
  gcls_sq (BinQF.mk 5 74 306) (BinQF.mk 34 74 45)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-7) 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ (-1) (-2) 1 1 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 4 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))

theorem sq16 : gcls 10 (-3) 17 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) :=
  gcls_sq (BinQF.mk 10 74 153) (BinQF.mk 17 74 90)
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> nsimp161)
    (sl_of _ _ (-1) (-4) 0 (-1) (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 2 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))
    (sl_of _ _ 0 (-1) 1 4 (by norm_num) (by nsimp161) (by nsimp161) (by nsimp161))


/-- The class of $(1, 0, 161)$ is the unit class (it is the principal form, and represents $1$). -/
theorem gcls_one : gcls 1 0 161 (by decide) = 1 := by
  unfold gcls
  rw [mk_eq_one_iff]
  exact ⟨1, 0, by simp [gpf, eval_gaussForm]⟩

/-- Distinct reduced forms give distinct classes (helper, from `art172_aux`). -/
theorem gcls_ne_of {a b c a' b' c' : ℤ} {h : _} {h' : _} (hpos : 0 < a)
    (hr : IsReduced (gaussForm a b c)) (hr' : IsReduced (gaussForm a' b' c')) (hac : a < c)
    (hne : gaussForm a' b' c' ≠ gaussForm a b c)
    (hx : gaussForm a' b' c' ≠ gaussForm a (-b) c ∨ |2 * b| ≠ a) :
    gcls a b c h ≠ gcls a' b' c' h' := by
  intro he
  unfold gcls at he
  have hs : SLEquiv (gpf a b c h).1 (gpf a' b' c' h').1 := mk_eq_mk.1 he
  change SLEquiv (gaussForm a b c) (gaussForm a' b' c') at hs
  have hd : (gaussForm a b c).disc < 0 := by
    have := (gpf a b c h).2.2
    have h2 : (gaussForm a b c).disc = -644 := this
    omega
  have hf : (gaussForm a b c).PosDef := (posDef_iff_posDef' _).2 ⟨by simpa using hpos, hd⟩
  rcases art172_aux hf hr hr' (by simpa using hac) hs with h1 | ⟨h1, h2⟩
  · exact hne h1
  · rw [conjForm_gaussForm] at h1
    rcases hx with hx | hx
    · exact hx h1
    · exact hx (by simpa using h2)

theorem ne_1_2 : gcls 1 0 161 (by decide) ≠ gcls 2 1 81 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.a h; norm_num at this) (Or.inr (by norm_num))

theorem ne_1_3 : gcls 1 0 161 (by decide) ≠ gcls 9 1 18 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.a h; norm_num at this) (Or.inr (by norm_num))

theorem ne_1_4 : gcls 1 0 161 (by decide) ≠ gcls 9 (-1) 18 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.a h; norm_num at this) (Or.inr (by norm_num))

theorem ne_2_3 : gcls 2 1 81 (by decide) ≠ gcls 9 1 18 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.a h; norm_num at this)
    (Or.inl (fun h => by have := congrArg BinQF.a h; norm_num at this))

theorem ne_2_4 : gcls 2 1 81 (by decide) ≠ gcls 9 (-1) 18 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.a h; norm_num at this)
    (Or.inl (fun h => by have := congrArg BinQF.a h; norm_num at this))

theorem ne_3_4 : gcls 9 1 18 (by decide) ≠ gcls 9 (-1) 18 (by decide) :=
  gcls_ne_of (by norm_num) ⟨by nsimp161, by nsimp161⟩ ⟨by nsimp161, by nsimp161⟩ (by norm_num)
    (fun h => by have := congrArg BinQF.b h; norm_num at this) (Or.inr (by norm_num))

/-- **The four principal-genus classes of determinant $-161$ are squares, hence in the principal genus**
(*Disq. Arith.* Art. 260): $(1,0,161)$, $(2,1,81)$, $(9,1,18)$, $(9,-1,18)$ lie in the principal genus. -/
theorem principal_genus_four :
    InPrincipalGenus (gaussForm 1 0 161) ∧ InPrincipalGenus (gaussForm 2 1 81) ∧
    InPrincipalGenus (gaussForm 9 1 18) ∧ InPrincipalGenus (gaussForm 9 (-1) 18) :=
  ⟨(principal_genus_iff_square (gpf 1 0 161 (by decide))).1 ⟨gcls 1 0 161 (by decide), sq1⟩,
   (principal_genus_iff_square (gpf 2 1 81 (by decide))).1 ⟨gcls 9 1 18 (by decide), sq5⟩,
   (principal_genus_iff_square (gpf 9 1 18 (by decide))).1 ⟨gcls 3 1 54 (by decide), sq9⟩,
   (principal_genus_iff_square (gpf 9 (-1) 18 (by decide))).1 ⟨gcls 3 (-1) 54 (by decide), sq13⟩⟩

/-- **Gauss's example, $D = -161$** (*Disq. Arith.* Art. 260), unconditional, in
`Composition.FormClass (-644)` (Gauss's $(a, b, c)$ = library $[a, 2b, c]$):

1. the classes of $(1,0,161)$, $(2,1,81)$, $(9,1,18)$, $(9,-1,18)$ lie in the principal genus and are pairwise
   distinct;
2. $(1,0,161)$ (the unit class) is the double (square) of each of the four ambiguous classes $(1,0,161)$,
   $(7,0,23)$, $(2,1,81)$, $(14,7,15)$;
3. $(2,1,81)$ is the double of $(9,1,18)$, $(9,-1,18)$, $(11,2,15)$, $(11,-2,15)$;
4. $(9,1,18)$ is the double of $(3,1,54)$, $(6,1,27)$, $(5,-2,33)$, $(10,3,17)$;
5. $(9,-1,18)$ is the double of $(3,-1,54)$, $(6,-1,27)$, $(5,2,33)$, $(10,-3,17)$.

Differences from the source: none in the statements, except that Gauss's 1801 text prints $(2,1,18)$ for
$(2,1,81)$ (*Erratum:* a misprint, determinant $-35 \ne -161$). Not proved: that
the principal genus consists of *exactly* these four classes (out of $16$ classes in total). -/
@[kb "gauss1801" "Art. 260"]
theorem art260_example_161 :
    (InPrincipalGenus (gaussForm 1 0 161) ∧ InPrincipalGenus (gaussForm 2 1 81) ∧
      InPrincipalGenus (gaussForm 9 1 18) ∧ InPrincipalGenus (gaussForm 9 (-1) 18)) ∧
    (gcls 1 0 161 (by decide) ≠ gcls 2 1 81 (by decide) ∧ gcls 1 0 161 (by decide) ≠ gcls 9 1 18 (by decide) ∧
      gcls 1 0 161 (by decide) ≠ gcls 9 (-1) 18 (by decide) ∧ gcls 2 1 81 (by decide) ≠ gcls 9 1 18 (by decide) ∧
      gcls 2 1 81 (by decide) ≠ gcls 9 (-1) 18 (by decide) ∧
      gcls 9 1 18 (by decide) ≠ gcls 9 (-1) 18 (by decide)) ∧
    (gcls 1 0 161 (by decide) = 1) ∧
    (gcls 1 0 161 (by decide) ^ 2 = gcls 1 0 161 (by decide) ∧ gcls 7 0 23 (by decide) ^ 2 = gcls 1 0 161 (by decide) ∧
      gcls 2 1 81 (by decide) ^ 2 = gcls 1 0 161 (by decide) ∧ gcls 14 7 15 (by decide) ^ 2 = gcls 1 0 161 (by decide)) ∧
    (gcls 9 1 18 (by decide) ^ 2 = gcls 2 1 81 (by decide) ∧ gcls 9 (-1) 18 (by decide) ^ 2 = gcls 2 1 81 (by decide) ∧
      gcls 11 2 15 (by decide) ^ 2 = gcls 2 1 81 (by decide) ∧ gcls 11 (-2) 15 (by decide) ^ 2 = gcls 2 1 81 (by decide)) ∧
    (gcls 3 1 54 (by decide) ^ 2 = gcls 9 1 18 (by decide) ∧ gcls 6 1 27 (by decide) ^ 2 = gcls 9 1 18 (by decide) ∧
      gcls 5 (-2) 33 (by decide) ^ 2 = gcls 9 1 18 (by decide) ∧ gcls 10 3 17 (by decide) ^ 2 = gcls 9 1 18 (by decide)) ∧
    (gcls 3 (-1) 54 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) ∧ gcls 6 (-1) 27 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) ∧
      gcls 5 2 33 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide) ∧ gcls 10 (-3) 17 (by decide) ^ 2 = gcls 9 (-1) 18 (by decide)) :=
  ⟨principal_genus_four, ⟨ne_1_2, ne_1_3, ne_1_4, ne_2_3, ne_2_4, ne_3_4⟩, gcls_one,
   ⟨sq1, sq2, sq3, sq4⟩, ⟨sq5, sq6, sq7, sq8⟩, ⟨sq9, sq10, sq11, sq12⟩, ⟨sq13, sq14, sq15, sq16⟩⟩

end QuadFormsKB.Historical.Gauss
